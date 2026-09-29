-- Prove2me | solution 1 for GrothendieckTeichmuller.mzv_stuffle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T02:51:54.786508+00:00
-- url     : https://prove2.me/submissions/e86660fb-7493-4f52-8f74-f1ae720c7824

import Definitions.Def_GT_multizeta

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open GrothendieckTeichmuller

/-!
# The stuffle (quasi-shuffle) relation for multiple zeta values

Mathlib has no multiple zeta values.  The heart of the matter is a purely finite identity for
the truncated sums `mzvTail`, proved by strong induction on the truncation bound; the passage
to the full multiple zeta values is then a rearrangement of an absolutely convergent double
series into the three regions `j > j'`, `j < j'`, `j = j'`.
-/

namespace Stuf

/-! ### The truncated sums are finite sums -/

theorem tail_nil (m : ℕ) : mzvTail [] m = 1 := rfl

theorem tail_cons (k : ℕ) (ns : List ℕ) (m : ℕ) :
    mzvTail (k :: ns) m = ∑ j ∈ Finset.Ico 1 m, ((j : ℝ) ^ k)⁻¹ * mzvTail ns j := by
  rw [mzvTail]
  rw [tsum_eq_sum (s := Finset.Ico 1 m) (f := fun j : ℕ =>
    if 1 ≤ j ∧ j < m then ((j : ℝ) ^ k)⁻¹ * mzvTail ns j else 0)]
  · refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [if_pos ⟨hj.1, hj.2⟩]
  · intro j hj
    rw [Finset.mem_Ico] at hj
    rw [if_neg]
    intro hc
    exact hj ⟨hc.1, hc.2⟩

theorem tail_zero (u : List ℕ) (hu : u ≠ []) (m : ℕ) (hm : m ≤ 1) : mzvTail u m = 0 := by
  cases u with
  | nil => exact absurd rfl hu
  | cons k ns =>
    rw [tail_cons]
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]

/-! ### Defining equations of the stuffle product -/

theorem stuffle_nil_left (w : List ℕ) : stuffle [] w = {w} := by rw [stuffle]

theorem stuffle_nil_right (w : List ℕ) : stuffle w [] = {w} := by
  cases w with
  | nil => rw [stuffle]
  | cons a v =>
    rw [stuffle]
    simp

theorem stuffle_cons (a : ℕ) (v : List ℕ) (b : ℕ) (w : List ℕ) :
    stuffle (a :: v) (b :: w)
      = (stuffle v (b :: w)).map (fun z => a :: z)
        + (stuffle (a :: v) w).map (fun z => b :: z)
        + (stuffle v w).map (fun z => (a + b) :: z) := by
  rw [stuffle]

/-- Every word occurring in a stuffle of two non-empty words is non-empty. -/
theorem stuffle_ne_nil {u v : List ℕ} (hu : u ≠ []) (hv : v ≠ []) {w : List ℕ}
    (hw : w ∈ stuffle u v) : w ≠ [] := by
  cases u with
  | nil => exact absurd rfl hu
  | cons a u =>
    cases v with
    | nil => exact absurd rfl hv
    | cons b v =>
      rw [stuffle_cons] at hw
      rcases Multiset.mem_add.1 hw with h | h
      · rcases Multiset.mem_add.1 h with h | h <;>
          · obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 h
            exact List.cons_ne_nil _ _
      · obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 h
        exact List.cons_ne_nil _ _

/-! ### The finite stuffle identity for the truncated sums -/

theorem msum_fsum {α : Type*} (S : Multiset α) (s : Finset ℕ) (f : α → ℕ → ℝ) :
    (S.map (fun z => ∑ j ∈ s, f z j)).sum = ∑ j ∈ s, (S.map (fun z => f z j)).sum := by
  induction S using Multiset.induction with
  | empty => simp
  | cons a S ih => simp [ih, Finset.sum_add_distrib]

theorem tail_stuffle (m : ℕ) : ∀ u v : List ℕ,
    mzvTail u m * mzvTail v m = ((stuffle u v).map (fun w => mzvTail w m)).sum := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro u v
    match u, v with
    | [], v => rw [stuffle_nil_left, tail_nil, one_mul]; simp
    | a :: u, [] => rw [stuffle_nil_right, tail_nil, mul_one]; simp
    | a :: u, b :: v =>
      have hexp : ∀ (c : ℕ) (S : Multiset (List ℕ)),
          (S.map (fun z => mzvTail (c :: z) m)).sum
            = ∑ j ∈ Finset.Ico 1 m, ((j : ℝ) ^ c)⁻¹ * (S.map (fun z => mzvTail z j)).sum := by
        intro c S
        have h1 : (S.map (fun z => mzvTail (c :: z) m))
            = S.map (fun z => ∑ j ∈ Finset.Ico 1 m, ((j : ℝ) ^ c)⁻¹ * mzvTail z j) := by
          refine Multiset.map_congr rfl ?_
          intro z _
          exact tail_cons c z m
        rw [h1, msum_fsum]
        refine Finset.sum_congr rfl ?_
        intro j _
        exact Multiset.sum_map_mul_left
      rw [stuffle_cons]
      simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_map, Function.comp_def]
      rw [hexp a (stuffle u (b :: v)), hexp b (stuffle (a :: u) v), hexp (a + b) (stuffle u v)]
      have e1 : ∀ j ∈ Finset.Ico 1 m,
          ((j : ℝ) ^ a)⁻¹ * ((stuffle u (b :: v)).map (fun z => mzvTail z j)).sum
            = ∑ j' ∈ Finset.Ico 1 j,
                ((j : ℝ) ^ a)⁻¹ * ((j' : ℝ) ^ b)⁻¹ * mzvTail u j * mzvTail v j' := by
        intro j hj
        rw [Finset.mem_Ico] at hj
        rw [← ih j hj.2, tail_cons, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j' _
        ring
      have e2 : ∀ j' ∈ Finset.Ico 1 m,
          ((j' : ℝ) ^ b)⁻¹ * ((stuffle (a :: u) v).map (fun z => mzvTail z j')).sum
            = ∑ j ∈ Finset.Ico 1 j',
                ((j : ℝ) ^ a)⁻¹ * ((j' : ℝ) ^ b)⁻¹ * mzvTail u j * mzvTail v j' := by
        intro j' hj'
        rw [Finset.mem_Ico] at hj'
        rw [← ih j' hj'.2, tail_cons, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        ring
      have e3 : ∀ j ∈ Finset.Ico 1 m,
          ((j : ℝ) ^ (a + b))⁻¹ * ((stuffle u v).map (fun z => mzvTail z j)).sum
            = ((j : ℝ) ^ a)⁻¹ * ((j : ℝ) ^ b)⁻¹ * mzvTail u j * mzvTail v j := by
        intro j hj
        rw [Finset.mem_Ico] at hj
        rw [← ih j hj.2, pow_add, mul_inv]
        ring
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3]
      rw [tail_cons, tail_cons, Finset.sum_mul_sum]
      have hswap : (∑ j ∈ Finset.Ico 1 m, ∑ j' ∈ Finset.Ico (j + 1) m,
            ((j : ℝ) ^ a)⁻¹ * ((j' : ℝ) ^ b)⁻¹ * mzvTail u j * mzvTail v j')
          = ∑ j' ∈ Finset.Ico 1 m, ∑ j ∈ Finset.Ico 1 j',
            ((j : ℝ) ^ a)⁻¹ * ((j' : ℝ) ^ b)⁻¹ * mzvTail u j * mzvTail v j' := by
        refine Finset.sum_comm' ?_
        intro j j'
        simp only [Finset.mem_Ico]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩; omega
        · rintro ⟨⟨h1, h2⟩, h3, h4⟩; omega
      rw [← hswap]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hsplit : ∑ j' ∈ Finset.Ico 1 m,
            ((j : ℝ) ^ a)⁻¹ * mzvTail u j * (((j' : ℝ) ^ b)⁻¹ * mzvTail v j')
          = (∑ j' ∈ Finset.Ico 1 j,
              ((j : ℝ) ^ a)⁻¹ * ((j' : ℝ) ^ b)⁻¹ * mzvTail u j * mzvTail v j')
            + (((j : ℝ) ^ a)⁻¹ * ((j : ℝ) ^ b)⁻¹ * mzvTail u j * mzvTail v j
              + ∑ j' ∈ Finset.Ico (j + 1) m,
                ((j : ℝ) ^ a)⁻¹ * ((j' : ℝ) ^ b)⁻¹ * mzvTail u j * mzvTail v j') := by
        rw [← Finset.sum_Ico_consecutive _ hj.1 (le_of_lt hj.2),
          Finset.sum_eq_sum_Ico_succ_bot hj.2]
        congr 1
        · exact Finset.sum_congr rfl fun j' _ => by ring
        · congr 1
          · ring
          · exact Finset.sum_congr rfl fun j' _ => by ring
      rw [hsplit]
      ring

/-! ### Positivity and the tail estimate -/

theorem tail_nonneg (ns : List ℕ) (m : ℕ) : 0 ≤ mzvTail ns m := by
  induction ns generalizing m with
  | nil => rw [tail_nil]; norm_num
  | cons k ns ih =>
    rw [tail_cons]
    refine Finset.sum_nonneg ?_
    intro j hj
    exact mul_nonneg (by positivity) (ih j)

/-- The tail of a `p`-series with `p ≥ 2`, bounded by `1 / i`. -/
theorem tail_sum_le_aux (i : ℕ) (hi : 1 ≤ i) (s : ℕ) (hs : 2 ≤ s) :
    ∀ N : ℕ, i ≤ N → ∑ j ∈ Finset.Ico (i + 1) (N + 1), ((j : ℝ) ^ s)⁻¹ ≤ 1 / i - 1 / N := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ N ihN =>
    intro h
    rcases Nat.lt_or_ge i (N + 1) with hlt | hge
    · have hiN : i ≤ N := by omega
      have hN1 : 1 ≤ N := by omega
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
      rw [Finset.sum_Ico_succ_top (by omega)]
      have h2 : ((N : ℝ) + 1) ^ 2 ≤ ((N : ℝ) + 1) ^ s :=
        pow_le_pow_right₀ (by linarith) hs
      have key : (1 : ℝ) / (((N : ℝ) + 1) ^ s) ≤ 1 / ((N : ℝ) * ((N : ℝ) + 1)) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        calc (N : ℝ) * ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) * ((N : ℝ) + 1) := by nlinarith
          _ = ((N : ℝ) + 1) ^ 2 := by ring
          _ ≤ ((N : ℝ) + 1) ^ s := h2
      have hdiff : (1 : ℝ) / (N : ℝ) - 1 / ((N : ℝ) + 1) = 1 / ((N : ℝ) * ((N : ℝ) + 1)) := by
        field_simp; ring
      have hstep : (((N + 1 : ℕ) : ℝ) ^ s)⁻¹ ≤ 1 / (N : ℝ) - 1 / ((N : ℝ) + 1) := by
        rw [hdiff]
        push_cast
        rw [← one_div]
        exact key
      have hih := ihN hiN
      push_cast at hstep ⊢
      linarith [hih, hstep]
    · have hie : i = N + 1 := by omega
      subst hie
      rw [Finset.Ico_self, Finset.sum_empty]
      simp

theorem tail_sum_le (i : ℕ) (hi : 1 ≤ i) (s : ℕ) (hs : 2 ≤ s) (N : ℕ) :
    ∑ j ∈ Finset.Ico (i + 1) N, ((j : ℝ) ^ s)⁻¹ ≤ 1 / i := by
  rcases Nat.lt_or_ge N (i + 1) with h | h
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    positivity
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hiM : i ≤ M := by omega
    have hM : (0 : ℝ) < M := by
      have h1 : 1 ≤ M := by omega
      exact_mod_cast h1
    have := tail_sum_le_aux i hi s hs M hiM
    have hpos : (0 : ℝ) < 1 / M := by positivity
    linarith

/-! ### Bounded partial sums, hence summability -/

theorem partial_bound (ns : List ℕ) (hns : ∀ k ∈ ns, 1 ≤ k) :
    ∀ s : ℕ, 2 ≤ s → ∃ C : ℝ, ∀ N : ℕ,
      ∑ j ∈ Finset.Ico 1 N, ((j : ℝ) ^ s)⁻¹ * mzvTail ns j ≤ C := by
  induction ns with
  | nil =>
    intro s hs
    refine ⟨2, fun N => ?_⟩
    simp only [tail_nil, mul_one]
    rcases Nat.lt_or_ge N 2 with h | h
    · rcases Nat.lt_or_ge N 1 with h1 | h1
      · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]; norm_num
      · have hN : N = 1 := by omega
        subst hN
        rw [Finset.Ico_self, Finset.sum_empty]; norm_num
    · rw [← Finset.sum_Ico_consecutive (fun j : ℕ => ((j : ℝ) ^ s)⁻¹) (by omega : (1:ℕ) ≤ 2) h]
      have h1 : ∑ j ∈ Finset.Ico (1:ℕ) 2, ((j : ℝ) ^ s)⁻¹ = 1 := by
        rw [show Finset.Ico (1:ℕ) 2 = {1} from rfl]
        simp
      have h2 : ∑ j ∈ Finset.Ico (2:ℕ) N, ((j : ℝ) ^ s)⁻¹ ≤ 1 := by
        have h3 := tail_sum_le 1 le_rfl s hs N
        simpa using h3
      linarith
  | cons k ns ih =>
    intro s hs
    have hk : 1 ≤ k := hns k (List.mem_cons_self ..)
    have hns' : ∀ j ∈ ns, 1 ≤ j := fun j hj => hns j (List.mem_cons_of_mem k hj)
    obtain ⟨C, hC⟩ := ih hns' (k + 1) (by omega)
    refine ⟨C, fun N => ?_⟩
    have hrw : ∑ j ∈ Finset.Ico 1 N, ((j : ℝ) ^ s)⁻¹ * mzvTail (k :: ns) j
        = ∑ i ∈ Finset.Ico 1 N, ∑ j ∈ Finset.Ico (i + 1) N,
            ((j : ℝ) ^ s)⁻¹ * (((i : ℝ) ^ k)⁻¹ * mzvTail ns i) := by
      have h1 : ∀ j ∈ Finset.Ico 1 N, ((j : ℝ) ^ s)⁻¹ * mzvTail (k :: ns) j
          = ∑ i ∈ Finset.Ico 1 j, ((j : ℝ) ^ s)⁻¹ * (((i : ℝ) ^ k)⁻¹ * mzvTail ns i) := by
        intro j _
        rw [tail_cons, Finset.mul_sum]
      rw [Finset.sum_congr rfl h1]
      refine Finset.sum_comm' ?_
      intro j i
      simp only [Finset.mem_Ico]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩; omega
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩; omega
    rw [hrw]
    refine le_trans (Finset.sum_le_sum ?_) (hC N)
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [← Finset.sum_mul]
    have hnn : 0 ≤ ((i : ℝ) ^ k)⁻¹ * mzvTail ns i :=
      mul_nonneg (by positivity) (tail_nonneg ns i)
    have hi0 : (0 : ℝ) < i := by exact_mod_cast hi.1
    have heq : (1 : ℝ) / (i : ℝ) * (((i : ℝ) ^ k)⁻¹ * mzvTail ns i)
        = ((i : ℝ) ^ (k + 1))⁻¹ * mzvTail ns i := by
      rw [pow_succ, mul_inv]
      field_simp
    exact le_trans (mul_le_mul_of_nonneg_right (tail_sum_le i hi.1 s hs N) hnn) (le_of_eq heq)

/-! ### The truncations are the partial sums of the defining series -/

/-- The summand of the outer series defining `mzv (a :: ns)`. -/
noncomputable def term (a : ℕ) (ns : List ℕ) (j : ℕ) : ℝ :=
  if 1 ≤ j then ((j : ℝ) ^ a)⁻¹ * mzvTail ns j else 0

theorem term_nonneg (a : ℕ) (ns : List ℕ) (j : ℕ) : 0 ≤ term a ns j := by
  rw [term]
  split
  · exact mul_nonneg (by positivity) (tail_nonneg ns j)
  · exact le_refl 0

theorem mzv_cons (a : ℕ) (ns : List ℕ) : mzv (a :: ns) = ∑' j : ℕ, term a ns j := rfl

theorem tail_eq_range (a : ℕ) (ns : List ℕ) (N : ℕ) :
    mzvTail (a :: ns) N = ∑ j ∈ Finset.range N, term a ns j := by
  rw [tail_cons, Finset.range_eq_Ico]
  cases N with
  | zero => simp
  | succ N =>
    rw [Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N)]
    have h0 : term a ns 0 = 0 := by rw [term]; simp
    rw [h0, zero_add]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [term, if_pos hj.1]

theorem summable_term (a : ℕ) (ha : 2 ≤ a) (ns : List ℕ) (hns : ∀ k ∈ ns, 1 ≤ k) :
    Summable (term a ns) := by
  obtain ⟨C, hC⟩ := partial_bound ns hns a ha
  refine summable_of_sum_range_le (c := C) (term_nonneg a ns) ?_
  intro n
  rw [← tail_eq_range, tail_cons]
  exact hC n

/-! ### Admissibility is inherited by the stuffle -/

theorem stuffle_ge_one (u : List ℕ) : ∀ v : List ℕ, (∀ k ∈ u, 1 ≤ k) → (∀ k ∈ v, 1 ≤ k) →
    ∀ w ∈ stuffle u v, ∀ k ∈ w, 1 ≤ k := by
  induction u with
  | nil =>
    intro v _ hv w hw
    rw [stuffle_nil_left, Multiset.mem_singleton] at hw
    subst hw; exact hv
  | cons a u ihu =>
    intro v
    induction v with
    | nil =>
      intro hu _ w hw
      rw [stuffle_nil_right, Multiset.mem_singleton] at hw
      subst hw; exact hu
    | cons b v ihv =>
      intro hu hv w hw
      rw [stuffle_cons] at hw
      rcases Multiset.mem_add.1 hw with h | h
      · rcases Multiset.mem_add.1 h with h | h
        · obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 h
          intro k hk
          rcases List.mem_cons.1 hk with rfl | hk
          · exact hu k (List.mem_cons_self ..)
          · exact ihu (b :: v) (fun x hx => hu x (List.mem_cons_of_mem a hx)) hv z hz k hk
        · obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 h
          intro k hk
          rcases List.mem_cons.1 hk with rfl | hk
          · exact hv k (List.mem_cons_self ..)
          · exact ihv hu (fun x hx => hv x (List.mem_cons_of_mem b hx)) z hz k hk
      · obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 h
        intro k hk
        rcases List.mem_cons.1 hk with rfl | hk
        · have h1 := hu a (List.mem_cons_self ..)
          omega
        · exact ihu v (fun x hx => hu x (List.mem_cons_of_mem a hx))
            (fun x hx => hv x (List.mem_cons_of_mem b hx)) z hz k hk

theorem stuffle_admissible {u v : List ℕ} (hu : IsAdmissible u) (hv : IsAdmissible v) :
    ∀ w ∈ stuffle u v, IsAdmissible w := by
  intro w hw
  refine ⟨stuffle_ge_one u v hu.1 hv.1 w hw, ?_⟩
  match u, v with
  | [], v =>
    rw [stuffle_nil_left, Multiset.mem_singleton] at hw
    subst hw; exact hv.2
  | a :: u, [] =>
    rw [stuffle_nil_right, Multiset.mem_singleton] at hw
    subst hw; exact hu.2
  | a :: u, b :: v =>
    have ha : 2 ≤ a := hu.2 a rfl
    have hb : 2 ≤ b := hv.2 b rfl
    rw [stuffle_cons] at hw
    rcases Multiset.mem_add.1 hw with h | h
    · rcases Multiset.mem_add.1 h with h | h
      · obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 h
        intro k hk
        rw [List.head?_cons, Option.mem_def, Option.some_inj] at hk
        omega
      · obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 h
        intro k hk
        rw [List.head?_cons, Option.mem_def, Option.some_inj] at hk
        omega
    · obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 h
      intro k hk
      rw [List.head?_cons, Option.mem_def, Option.some_inj] at hk
      omega

/-! ### The truncations converge to the multiple zeta values -/

theorem tendsto_tail (u : List ℕ) (hu : IsAdmissible u) :
    Filter.Tendsto (fun N => mzvTail u N) Filter.atTop (nhds (mzv u)) := by
  match u with
  | [] =>
    have h : (fun N : ℕ => mzvTail ([] : List ℕ) N) = fun _ => (1 : ℝ) := by
      funext N; exact tail_nil N
    rw [h]
    have h2 : mzv ([] : List ℕ) = 1 := rfl
    rw [h2]
    exact tendsto_const_nhds
  | a :: ns =>
    have ha : 2 ≤ a := hu.2 a rfl
    have hns : ∀ k ∈ ns, 1 ≤ k := fun k hk => hu.1 k (List.mem_cons_of_mem a hk)
    have hsum := summable_term a ha ns hns
    have h : (fun N : ℕ => mzvTail (a :: ns) N)
        = fun N => ∑ j ∈ Finset.range N, term a ns j := by
      funext N; exact tail_eq_range a ns N
    rw [h, mzv_cons]
    exact hsum.hasSum.tendsto_sum_nat

theorem msum_tendsto (S : Multiset (List ℕ)) :
    (∀ w ∈ S, IsAdmissible w) →
      Filter.Tendsto (fun N => (S.map (fun w => mzvTail w N)).sum) Filter.atTop
        (nhds ((S.map mzv).sum)) := by
  induction S using Multiset.induction with
  | empty => intro _; simpa using tendsto_const_nhds
  | cons a S ih =>
    intro h
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact (tendsto_tail a (h a (Multiset.mem_cons_self a S))).add
      (ih fun w hw => h w (Multiset.mem_cons_of_mem hw))

/-! ### The stuffle relation -/

theorem mzv_stuffle (u v : List ℕ) (hu : IsAdmissible u) (hv : IsAdmissible v) :
    mzv u * mzv v = ((stuffle u v).map mzv).sum := by
  have h1 : Filter.Tendsto (fun N => mzvTail u N * mzvTail v N) Filter.atTop
      (nhds (mzv u * mzv v)) := (tendsto_tail u hu).mul (tendsto_tail v hv)
  have h3 : (fun N => mzvTail u N * mzvTail v N)
      = fun N => ((stuffle u v).map (fun w => mzvTail w N)).sum := by
    funext N; exact tail_stuffle N u v
  rw [h3] at h1
  exact tendsto_nhds_unique h1 (msum_tendsto _ (stuffle_admissible hu hv))

end Stuf

theorem solution (u v : List ℕ) (hu : GrothendieckTeichmuller.IsAdmissible u)
    (hv : GrothendieckTeichmuller.IsAdmissible v) :
    GrothendieckTeichmuller.mzv u * GrothendieckTeichmuller.mzv v
      = ((GrothendieckTeichmuller.stuffle u v).map GrothendieckTeichmuller.mzv).sum :=
  Stuf.mzv_stuffle u v hu hv
