-- Prove2me | solution 1 for LowDiameterNashWilliams.Main.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T18:53:33.314053+00:00
-- url     : https://prove2.me/submissions/b8991f0e-89c7-4f50-a9f3-34f96925ae5f

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Geometry
import Definitions.Def_LowDiameterNashWilliams_Main_Reserves
import Definitions.Def_LowDiameterNashWilliams_Main_Sampling
import Definitions.Def_LowDiameterNashWilliams_Main_Computation

section
/-!
# Frank's weight-splitting theorem for two matroids on `Fin m`

Plan (all weights integral; `Opt M c B` := `B` is a base of `M` of maximum `c`-weight).

1. Generic matroid facts: symmetric exchange, local-to-global optimality (a base with no
   improving single exchange is optimal), the bases of maximum weight form the bases of a matroid
   `optM M c`, and the triangular exchange lemma: if `B - x_i + y_i` are bases and
   `B - x_i + y_j` are not for `j < i`, then `B - X + Y` is a base (via fundamental circuits).
2. Induction on the weight: the claim holds for constant weights; and from a splitting for `w`
   one gets a splitting for `w + χ_e` (`step`).  In `step`, with `B` optimal for `(M₁,w₁)`
   and `(M₂,w₂)`, `e ∉ B`, build the tight exchange digraph (arcs `y → x` when `B - x + y` is
   `w₁`-optimal in `M₁`, arcs `x → y` when `B - x + y` is `w₂`-optimal in `M₂`).
   * If some `x ∈ B` reachable from `e` has `B - x + e` `w₂`-optimal in `M₂`: a shortest such
     cycle through `e` is triangular in both `optM M₁ w₁` and `optM M₂ w₂`, so the cycle's
     exchange `B*` is optimal in both and contains `e`; raise `w₁` by `χ_e`.
   * Otherwise, with `R` the set reachable from `e`, `w₁ + χ_R` and `w₂ + χ_e - χ_R` keep `B`
     locally (hence globally) optimal, using integrality (slack ≥ 1 on non-tight exchanges).
-/

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Dev.Frank

open Matroid Set

variable {α : Type*}

/-- Exchange within a base is the same as membership in the fundamental circuit. -/
theorem exch_iff_mem_fundCircuit {M : Matroid α} {B : Set α} {x y : α} (hB : M.IsBase B)
    (hx : x ∈ B) (hy : y ∉ B) (hyE : y ∈ M.E) :
    M.IsBase (insert y B \ {x}) ↔ x ∈ M.fundCircuit y B := by
  rw [hB.indep.mem_fundCircuit_iff (by rw [hB.closure_eq]; exact hyE) hy]
  exact ⟨fun h => h.indep, fun h => hB.exchange_isBase_of_indep' hx hy h⟩

/-- Symmetric exchange. -/
theorem sym_exchange {M : Matroid α} {A B : Set α} {a : α} (hA : M.IsBase A) (hB : M.IsBase B)
    (ha : a ∈ A) (haB : a ∉ B) :
    ∃ b ∈ B, b ∉ A ∧ M.IsBase (insert b A \ {a}) ∧ M.IsBase (insert a B \ {b}) := by
  have haE : a ∈ M.E := hA.subset_ground ha
  have hC := hB.fundCircuit_isCircuit haE haB
  have hex : ∃ b ∈ M.fundCircuit a B \ {a}, b ∉ M.closure (A \ {a}) := by
    by_contra hcon
    push Not at hcon
    have h1 : a ∈ M.closure (M.fundCircuit a B \ {a}) :=
      hC.mem_closure_sdiff_singleton_of_mem (M.mem_fundCircuit a B)
    have h2 : M.closure (M.fundCircuit a B \ {a}) ⊆ M.closure (A \ {a}) := by
      rw [← M.closure_closure (A \ {a})]
      exact M.closure_subset_closure hcon
    exact (hA.indep.notMem_closure_sdiff_of_mem ha) (h2 h1)
  obtain ⟨b, ⟨hbC, hba⟩, hbcl⟩ := hex
  have hba' : b ≠ a := hba
  have hbB : b ∈ B := by
    have := M.fundCircuit_subset_insert a B hbC
    rcases this with h | h
    · exact absurd h hba'
    · exact h
  have hbA : b ∉ A := by
    intro hbA
    exact hbcl (M.subset_closure _ (by
      intro z hz; exact (hA.subset_ground hz.1)) ⟨hbA, hba'⟩)
  refine ⟨b, hbB, hbA, ?_, ?_⟩
  · have hind : M.Indep (insert b (A \ {a})) := by
      rw [(hA.indep.subset sdiff_subset).insert_indep_iff_of_notMem (fun h => hbA h.1)]
      exact ⟨hB.subset_ground hbB, hbcl⟩
    have := hA.exchange_isBase_of_indep (e := a) hbA hind
    rwa [insert_sdiff_singleton_comm hba'] at this
  · exact (exch_iff_mem_fundCircuit hB hbB haB haE).2 hbC

/-! ### Finset-level API on `Fin m` -/

variable {m : ℕ}

/-- A finset is a base. -/
abbrev IB (M : Matroid (Fin m)) (F : Finset (Fin m)) : Prop := M.IsBase (F : Set (Fin m))

/-- `B - x + y`. -/
def exch (B : Finset (Fin m)) (x y : Fin m) : Finset (Fin m) := (insert y B).erase x

theorem coe_exch (B : Finset (Fin m)) (x y : Fin m) :
    ((exch B x y : Finset (Fin m)) : Set (Fin m)) = insert y (B : Set (Fin m)) \ {x} := by
  simp [exch, Finset.coe_erase, Finset.coe_insert]

/-- `B` is a base of maximum `c`-weight. -/
def Opt (M : Matroid (Fin m)) (c : Fin m → ℤ) (B : Finset (Fin m)) : Prop :=
  IB M B ∧ ∀ A : Finset (Fin m), IB M A → weight c A ≤ weight c B

theorem weight_exch (c : Fin m → ℤ) {B : Finset (Fin m)} {x y : Fin m} (hx : x ∈ B)
    (hy : y ∉ B) : weight c (exch B x y) = weight c B - c x + c y := by
  unfold weight exch
  rw [Finset.sum_erase_eq_sub (Finset.mem_insert_of_mem hx), Finset.sum_insert hy]
  ring

theorem card_eq {M : Matroid (Fin m)} {A B : Finset (Fin m)} (hA : IB M A) (hB : IB M B) :
    A.card = B.card := by
  have := hA.ncard_eq_ncard_of_isBase hB
  simpa [Set.ncard_coe_finset] using this

theorem sym_exchange_fin {M : Matroid (Fin m)} {A B : Finset (Fin m)} {a : Fin m}
    (hA : IB M A) (hB : IB M B) (ha : a ∈ A) (haB : a ∉ B) :
    ∃ b ∈ B, b ∉ A ∧ IB M (exch A a b) ∧ IB M (exch B b a) := by
  obtain ⟨b, hb, hbA, h1, h2⟩ :=
    sym_exchange hA hB (by exact_mod_cast ha) (by exact_mod_cast haB)
  refine ⟨b, by exact_mod_cast hb, by exact_mod_cast hbA, ?_, ?_⟩
  · unfold IB; rw [coe_exch]; exact h1
  · unfold IB; rw [coe_exch]; exact h2

/-- Local optimality implies global optimality. -/
theorem local_global (M : Matroid (Fin m)) (c : Fin m → ℤ) {B : Finset (Fin m)} (hB : IB M B)
    (hloc : ∀ x ∈ B, ∀ y, y ∉ B → IB M (exch B x y) → c y ≤ c x) :
    Opt M c B := by
  refine ⟨hB, ?_⟩
  suffices h : ∀ n : ℕ, ∀ A : Finset (Fin m), IB M A → (A \ B).card = n →
      weight c A ≤ weight c B from fun A hA => h _ A hA rfl
  intro n
  induction n with
  | zero =>
    intro A hA h0
    rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at h0
    have : A = B := Finset.eq_of_subset_of_card_le h0 (card_eq hB hA).le
    rw [this]
  | succ n ih =>
    intro A hA hn
    obtain ⟨a, haAB⟩ : (A \ B).Nonempty := by
      rw [← Finset.card_pos, hn]; exact Nat.succ_pos n
    rw [Finset.mem_sdiff] at haAB
    obtain ⟨b, hbB, hbA, h1, h2⟩ := sym_exchange_fin hA hB haAB.1 haAB.2
    have hcab : c a ≤ c b := hloc b hbB a haAB.2 h2
    have hcard : (exch A a b \ B).card = n := by
      have : exch A a b \ B = (A \ B).erase a := by
        ext v
        simp only [exch, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        constructor
        · rintro ⟨⟨hva, hv | hv⟩, hvB⟩
          · exact absurd (hv ▸ hbB) hvB
          · exact ⟨hva, hv, hvB⟩
        · rintro ⟨hva, hv, hvB⟩
          exact ⟨⟨hva, Or.inr hv⟩, hvB⟩
      rw [this, Finset.card_erase_of_mem (Finset.mem_sdiff.2 haAB), hn]
      rfl
    have := ih _ h1 hcard
    rw [weight_exch c haAB.1 hbA] at this
    linarith

theorem exists_opt (M : Matroid (Fin m)) (c : Fin m → ℤ) (h : ∃ B, IB M B) :
    ∃ B, Opt M c B := by
  obtain ⟨B0, hB0⟩ := h
  let S := (Finset.univ : Finset (Finset (Fin m))).filter (IB M)
  have hS : S.Nonempty := ⟨B0, by simp [S, hB0]⟩
  obtain ⟨B, hBS, hmax⟩ := S.exists_max_image (weight c) hS
  exact ⟨B, (by simpa [S] using hBS), fun A hA => hmax A (by simp [S, hA])⟩

theorem opt_exch_iff {M : Matroid (Fin m)} {c : Fin m → ℤ} {B : Finset (Fin m)} {x y : Fin m}
    (hB : Opt M c B) (hx : x ∈ B) (hy : y ∉ B) :
    Opt M c (exch B x y) ↔ IB M (exch B x y) ∧ c x = c y := by
  constructor
  · intro h
    have h1 := h.2 B hB.1
    have h2 := hB.2 _ h.1
    rw [weight_exch c hx hy] at h1 h2
    exact ⟨h.1, by linarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun A hA => ?_⟩
    rw [weight_exch c hx hy, h2]
    have := hB.2 A hA
    linarith

theorem opt_exchangeProperty (M : Matroid (Fin m)) (c : Fin m → ℤ) :
    Matroid.ExchangeProperty
      (fun S : Set (Fin m) => ∃ F : Finset (Fin m), (F : Set (Fin m)) = S ∧ Opt M c F) := by
  rintro _ _ ⟨F1, rfl, h1⟩ ⟨F2, rfl, h2⟩ e ⟨he1, he2⟩
  have he1' : e ∈ F1 := by exact_mod_cast he1
  have he2' : e ∉ F2 := by exact_mod_cast he2
  obtain ⟨b, hbF2, hbF1, hx1, hx2⟩ := sym_exchange_fin h1.1 h2.1 he1' he2'
  have w1 := weight_exch c he1' hbF1
  have w2 := weight_exch c hbF2 he2'
  have i1 := h2.2 _ hx1
  have i2 := h1.2 _ hx2
  refine ⟨b, ⟨by exact_mod_cast hbF2, by exact_mod_cast hbF1⟩, exch F1 e b, ?_, hx1, ?_⟩
  · have hbe : b ≠ e := fun h => hbF1 (h ▸ he1')
    rw [coe_exch, insert_sdiff_singleton_comm hbe]
  · intro A hA
    have := h2.2 A hA
    linarith

/-- The matroid whose bases are the maximum-weight bases of `M`. -/
noncomputable def optM (M : Matroid (Fin m)) (c : Fin m → ℤ) (h : ∃ B, IB M B) :
    Matroid (Fin m) :=
  Matroid.ofIsBaseOfFinite (E := Set.univ) Set.finite_univ
    (fun S => ∃ F : Finset (Fin m), (F : Set (Fin m)) = S ∧ Opt M c F)
    (by obtain ⟨B, hB⟩ := exists_opt M c h; exact ⟨B, B, rfl, hB⟩)
    (opt_exchangeProperty M c)
    (fun _ _ => Set.subset_univ _)

theorem optM_E (M : Matroid (Fin m)) (c : Fin m → ℤ) (h : ∃ B, IB M B) :
    (optM M c h).E = Set.univ := rfl

theorem optM_isBase {M : Matroid (Fin m)} {c : Fin m → ℤ} {h : ∃ B, IB M B}
    {F : Finset (Fin m)} : IB (optM M c h) F ↔ Opt M c F := by
  unfold IB optM
  rw [Matroid.ofIsBaseOfFinite_isBase]
  constructor
  · rintro ⟨F', hF', hO⟩
    rwa [Finset.coe_inj.1 hF'] at hO
  · exact fun hO => ⟨F, rfl, hO⟩

/-- The triangular exchange lemma. -/
theorem tri (N : Matroid (Fin m)) (hE : N.E = Set.univ) (x y : ℕ → Fin m) :
    ∀ (k : ℕ) (B : Finset (Fin m)), IB N B → (∀ i < k, x i ∈ B) → (∀ i < k, y i ∉ B) →
      (∀ i < k, IB N (exch B (x i) (y i))) →
      (∀ i < k, ∀ j < i, ¬ IB N (exch B (x i) (y j))) →
      IB N ((B \ (Finset.range k).image x) ∪ (Finset.range k).image y) := by
  intro k
  induction k with
  | zero => intro B hB _ _ _ _; simpa using hB
  | succ k ih =>
    intro B hB hx hy harc hno
    obtain ⟨B1, hB1def⟩ : ∃ B1, B1 = exch B (x k) (y k) := ⟨_, rfl⟩
    have hB1 : IB N B1 := hB1def ▸ harc k (Nat.lt_succ_self k)
    have hxk : x k ∈ B := hx k (Nat.lt_succ_self k)
    have hyk : y k ∉ B := hy k (Nat.lt_succ_self k)
    have hxne : ∀ i < k, x i ≠ x k := fun i hi heq =>
      hno k (Nat.lt_succ_self k) i hi (by rw [← heq]; exact harc i (by omega))
    have hyne : ∀ i < k, y i ≠ y k := fun i hi heq =>
      hno k (Nat.lt_succ_self k) i hi (by rw [heq]; exact harc k (Nat.lt_succ_self k))
    have hx1 : ∀ i < k, x i ∈ B1 := fun i hi => by
      simp only [hB1def, exch, Finset.mem_erase, Finset.mem_insert]
      exact ⟨hxne i hi, Or.inr (hx i (by omega))⟩
    have hy1 : ∀ i < k, y i ∉ B1 := fun i hi => by
      simp only [hB1def, exch, Finset.mem_erase, Finset.mem_insert, not_and, not_or]
      exact fun _ => ⟨hyne i hi, hy i (by omega)⟩
    have key : ∀ i < k, ∀ j < k, IB N (exch B1 (x i) (y j)) ↔ IB N (exch B (x i) (y j)) := by
      intro i hi j hj
      have hyjB : y j ∉ (B : Set (Fin m)) := by exact_mod_cast hy j (by omega)
      have hyjB1 : y j ∉ (B1 : Set (Fin m)) := by exact_mod_cast hy1 j hj
      have hyE : y j ∈ N.E := by rw [hE]; exact Set.mem_univ _
      unfold IB
      rw [coe_exch B1, coe_exch B, exch_iff_mem_fundCircuit hB1 (by exact_mod_cast hx1 i hi) hyjB1 hyE,
        exch_iff_mem_fundCircuit hB (by exact_mod_cast hx i (by omega)) hyjB hyE]
      have hC := hB.fundCircuit_isCircuit hyE hyjB
      have hsub : N.fundCircuit (y j) (B : Set (Fin m)) ⊆ insert (y j) (B1 : Set (Fin m)) := by
        intro z hz
        rcases N.fundCircuit_subset_insert (y j) (B : Set (Fin m)) hz with h | h
        · exact Or.inl h
        · right
          have hzk : z ≠ x k := by
            rintro rfl
            apply hno k (Nat.lt_succ_self k) j (by omega)
            unfold IB; rw [coe_exch]
            exact (exch_iff_mem_fundCircuit hB h hyjB hyE).2 hz
          have : z ∈ B1 := by
            simp only [hB1def, exch, Finset.mem_erase, Finset.mem_insert]
            exact ⟨hzk, Or.inr (by exact_mod_cast h)⟩
          exact_mod_cast this
      rw [← hC.eq_fundCircuit_of_subset hB1.indep hsub]
    have := ih B1 hB1 hx1 hy1 (fun i hi => (key i hi i hi).2 (harc i (by omega)))
      (fun i hi j hj h => hno i (by omega) j hj ((key i hi j (by omega)).1 h))
    convert this using 1
    ext v
    simp only [hB1def, exch, Finset.range_add_one, Finset.image_insert, Finset.mem_union,
      Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, Finset.mem_image, Finset.mem_range]
    have hXB : ∀ a < k, x a ∈ B := fun a ha => hx a (by omega)
    constructor
    · rintro (⟨hvB, hn⟩ | rfl | hv)
      · exact Or.inl ⟨⟨fun h => hn (Or.inl h), Or.inr hvB⟩, fun h => hn (Or.inr h)⟩
      · refine Or.inl ⟨⟨fun h => hyk (h ▸ hxk), Or.inl rfl⟩, ?_⟩
        rintro ⟨a, ha, hxa⟩
        exact hyk (hxa ▸ hXB a ha)
      · exact Or.inr hv
    · rintro (⟨⟨hvx, rfl | hvB⟩, hn⟩ | hv)
      · exact Or.inr (Or.inl rfl)
      · refine Or.inl ⟨hvB, ?_⟩
        rintro (h | h)
        · exact hvx h
        · exact hn h
      · exact Or.inr (Or.inr hv)

/-! ### Reachability in a digraph on `Fin m` -/

/-- `v` is reachable from `e` by a walk of exactly `n` arcs. -/
def reachIn (r : Fin m → Fin m → Prop) (e : Fin m) : ℕ → Fin m → Prop
  | 0, v => v = e
  | n + 1, v => ∃ u, reachIn r e n u ∧ r u v

theorem reachIn_path (r : Fin m → Fin m → Prop) (e : Fin m) :
    ∀ n x, reachIn r e n x →
      ∃ P : ℕ → Fin m, P 0 = e ∧ P n = x ∧ ∀ t < n, r (P t) (P (t + 1)) := by
  intro n
  induction n with
  | zero => intro x hx; exact ⟨fun _ => x, hx, rfl, fun t ht => absurd ht (Nat.not_lt_zero _)⟩
  | succ n ih =>
    rintro x ⟨u, hu, hux⟩
    obtain ⟨P, hP0, hPn, hP⟩ := ih u hu
    refine ⟨fun t => if t ≤ n then P t else x, by simpa using hP0, by simp, ?_⟩
    intro t ht
    by_cases htn : t + 1 ≤ n
    · simp only [htn, if_true, show t ≤ n by omega]
      exact hP t (by omega)
    · have : t = n := by omega
      subst this
      simp [hPn, hux]

theorem reachIn_extend (r : Fin m → Fin m → Prop) (e : Fin m) (P : ℕ → Fin m) (n : ℕ)
    (hP : ∀ t < n, r (P t) (P (t + 1))) (s t : ℕ) (h : reachIn r e s (P t)) :
    ∀ d, t + d ≤ n → reachIn r e (s + d) (P (t + d)) := by
  intro d
  induction d with
  | zero => intro _; simpa using h
  | succ d ih =>
    intro hd
    exact ⟨P (t + d), ih (by omega), hP (t + d) (by omega)⟩

theorem reachIn_of_path (r : Fin m → Fin m → Prop) (e : Fin m) (P : ℕ → Fin m) (n : ℕ)
    (hP0 : P 0 = e) (hP : ∀ t < n, r (P t) (P (t + 1))) : ∀ t ≤ n, reachIn r e t (P t) := by
  intro t ht
  have := reachIn_extend r e P n hP 0 0 (by simp [reachIn, hP0]) t (by omega)
  simpa using this

theorem reachIn_parity (r : Fin m → Fin m → Prop) (e : Fin m) (B : Finset (Fin m)) (he : e ∉ B)
    (hr : ∀ u v, r u v → (v ∈ B ↔ u ∉ B)) : ∀ n v, reachIn r e n v → (v ∈ B ↔ n % 2 = 1) := by
  intro n
  induction n with
  | zero => intro v hv; simp only [reachIn] at hv; subst hv; simp [he]
  | succ n ih =>
    rintro v ⟨u, hu, huv⟩
    rw [hr u v huv, ih u hu]
    omega

theorem rev_image (f : ℕ → Fin m) (K : ℕ) :
    (Finset.range (K + 1)).image (fun i => f (K - i)) = (Finset.range (K + 1)).image f := by
  ext v
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨K - i, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨K - i, by omega, by rw [show K - (K - i) = i by omega]⟩

/-! ### Weight shifts -/

/-- Indicator of a single element. -/
def ind (e : Fin m) : Fin m → ℤ := fun v => if v = e then 1 else 0

theorem weight_add_ind (c : Fin m → ℤ) (e : Fin m) (A : Finset (Fin m)) :
    weight (c + ind e) A = weight c A + if e ∈ A then 1 else 0 := by
  unfold weight ind
  simp [Finset.sum_add_distrib]

theorem opt_add_ind {M : Matroid (Fin m)} {c : Fin m → ℤ} {B : Finset (Fin m)} (e : Fin m)
    (hB : Opt M c B) (he : e ∈ B) : Opt M (c + ind e) B := by
  refine ⟨hB.1, fun A hA => ?_⟩
  rw [weight_add_ind, weight_add_ind, if_pos he]
  have := hB.2 A hA
  split_ifs <;> linarith

/-! ### The step `w ↦ w + χ_e` -/

/-- Tight exchange arcs at `B`: `y → x` if `B - x + y` is `w₁`-optimal in `M₁`,
`x → y` if `B - x + y` is `w₂`-optimal in `M₂` (`x ∈ B`, `y ∉ B`). -/
def arc (M₁ M₂ : Matroid (Fin m)) (w₁ w₂ : Fin m → ℤ) (B : Finset (Fin m)) (u v : Fin m) : Prop :=
  (u ∉ B ∧ v ∈ B ∧ Opt M₁ w₁ (exch B v u)) ∨ (u ∈ B ∧ v ∉ B ∧ Opt M₂ w₂ (exch B u v))

theorem arc_parity (M₁ M₂ : Matroid (Fin m)) (w₁ w₂ : Fin m → ℤ) (B : Finset (Fin m)) :
    ∀ u v, arc M₁ M₂ w₁ w₂ B u v → (v ∈ B ↔ u ∉ B) := by
  rintro u v (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩) <;> tauto

/-- A shortest tight cycle through `e` yields a common optimal base containing `e`. -/
theorem step_cycle (M₁ M₂ : Matroid (Fin m)) (h₁ : ∃ B, IB M₁ B) (h₂ : ∃ B, IB M₂ B)
    (w₁ w₂ : Fin m → ℤ) (B : Finset (Fin m)) (hB1 : Opt M₁ w₁ B) (hB2 : Opt M₂ w₂ B)
    (e : Fin m) (he : e ∉ B) (n : ℕ) (x : Fin m)
    (hx : reachIn (arc M₁ M₂ w₁ w₂ B) e n x) (hxB : x ∈ B) (hxe : Opt M₂ w₂ (exch B x e))
    (hmin : ∀ s < n, ∀ y, reachIn (arc M₁ M₂ w₁ w₂ B) e s y → y ∈ B →
      ¬ Opt M₂ w₂ (exch B y e)) :
    ∃ B', e ∈ B' ∧ Opt M₁ w₁ B' ∧ Opt M₂ w₂ B' := by
  obtain ⟨r, hr⟩ : ∃ r, r = arc M₁ M₂ w₁ w₂ B := ⟨_, rfl⟩
  rw [← hr] at hx hmin
  obtain ⟨P, hP0, hPn, hP⟩ := reachIn_path r e n x hx
  have hreach := reachIn_of_path r e P n hP0 hP
  have hdist : ∀ t ≤ n, ∀ s, reachIn r e s (P t) → t ≤ s := by
    intro t ht s hs
    by_contra hlt
    have := reachIn_extend r e P n hP s t hs (n - t) (by omega)
    rw [show t + (n - t) = n by omega, hPn] at this
    exact hmin (s + (n - t)) (by omega) x this hxB hxe
  have hpar := reachIn_parity r e B he (hr ▸ arc_parity M₁ M₂ w₁ w₂ B)
  have hPB : ∀ t ≤ n, (P t ∈ B ↔ t % 2 = 1) := fun t ht => hpar t (P t) (hreach t ht)
  have hstep : ∀ t ≤ n, ∀ s ≤ n, r (P s) (P t) → t ≤ s + 1 :=
    fun t ht s hs h => hdist t ht (s + 1) ⟨P s, hreach s hs, h⟩
  have hnodd : n % 2 = 1 := (hpar n x hx).1 hxB
  obtain ⟨K, rfl⟩ : ∃ K, n = 2 * K + 1 := ⟨n / 2, by omega⟩
  obtain ⟨X, hX⟩ : ∃ X : ℕ → Fin m, ∀ i, X i = P (2 * i + 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → Fin m, ∀ i, Y i = P (2 * i) := ⟨_, fun _ => rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℕ → Fin m, ∀ i, Z i = if i < K then P (2 * i + 2) else e :=
    ⟨_, fun _ => rfl⟩
  have hXB : ∀ i < K + 1, X i ∈ B := fun i hi => by
    rw [hX]; exact (hPB (2 * i + 1) (by omega)).2 (by omega)
  have hYB : ∀ i < K + 1, Y i ∉ B := fun i hi h => by
    rw [hY] at h; have := (hPB (2 * i) (by omega)).1 h; omega
  have hZB : ∀ i < K + 1, Z i ∉ B := fun i hi h => by
    rw [hZ] at h
    split_ifs at h with hiK
    · have := (hPB (2 * i + 2) (by omega)).1 h; omega
    · exact he h
  -- matroid 1
  have T1 := tri (optM M₁ w₁ h₁) (optM_E _ _ _) X Y (K + 1) B (optM_isBase.2 hB1) hXB hYB
    (fun i hi => by
      rw [optM_isBase]
      have h0 : r (P (2 * i)) (P (2 * i + 1)) := hP (2 * i) (by omega)
      rw [hr] at h0
      rcases h0 with ⟨_, _, h⟩ | ⟨h, _, _⟩
      · rw [hX, hY]; exact h
      · rw [← hY] at h; exact absurd h (hYB i hi))
    (fun i hi j hj h => by
      rw [optM_isBase] at h
      have harc : r (P (2 * j)) (P (2 * i + 1)) := by
        rw [hr]; left; rw [← hX, ← hY]; exact ⟨hYB j (by omega), hXB i hi, h⟩
      have := hstep (2 * i + 1) (by omega) (2 * j) (by omega) harc
      omega)
  -- matroid 2
  have T2 := tri (optM M₂ w₂ h₂) (optM_E _ _ _) (fun i => X (K - i)) (fun i => Z (K - i)) (K + 1)
    B (optM_isBase.2 hB2) (fun i hi => hXB _ (by omega)) (fun i hi => hZB _ (by omega))
    (fun i hi => by
      rw [optM_isBase]
      show Opt M₂ w₂ (exch B (X (K - i)) (Z (K - i)))
      rw [hZ]
      split_ifs with ha
      · have h0 : r (P (2 * (K - i) + 1)) (P (2 * (K - i) + 1 + 1)) :=
          hP (2 * (K - i) + 1) (by omega)
        rw [hr] at h0
        rcases h0 with ⟨h, _, _⟩ | ⟨_, _, h⟩
        · exact absurd (hX (K - i) ▸ hXB (K - i) (by omega)) h
        · rw [hX]; exact h
      · rw [hX, show 2 * (K - i) + 1 = 2 * K + 1 by omega, hPn]; exact hxe)
    (fun i hi j hj h => by
      rw [optM_isBase] at h
      change Opt M₂ w₂ (exch B (X (K - i)) (Z (K - j))) at h
      rw [hZ] at h
      split_ifs at h with hb
      · have harc : r (P (2 * (K - i) + 1)) (P (2 * (K - j) + 2)) := by
          rw [hr]; right
          refine ⟨?_, ?_, ?_⟩
          · rw [← hX]; exact hXB _ (by omega)
          · intro hc; have := (hPB (2 * (K - j) + 2) (by omega)).1 hc; omega
          · rw [← hX]; exact h
        have := hstep _ (by omega) _ (by omega) harc
        omega
      · exact hmin (2 * (K - i) + 1) (by omega) (X (K - i))
          (by rw [hX]; exact hreach _ (by omega)) (hXB _ (by omega)) h)
  rw [rev_image X K, rev_image Z K] at T2
  have hZY : (Finset.range (K + 1)).image Z = (Finset.range (K + 1)).image Y := by
    ext v
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [hZ]
      split_ifs with haK
      · exact ⟨a + 1, by omega, by rw [hY]; ring_nf⟩
      · exact ⟨0, by omega, by rw [hY, hP0]⟩
    · rintro ⟨a, ha, rfl⟩
      rcases a with _ | a
      · exact ⟨K, by omega, by rw [hZ, hY, if_neg (lt_irrefl K), hP0]⟩
      · exact ⟨a, by omega, by rw [hZ, hY, if_pos (by omega)]; ring_nf⟩
  rw [hZY] at T2
  refine ⟨B \ (Finset.range (K + 1)).image X ∪ (Finset.range (K + 1)).image Y, ?_,
    optM_isBase.1 T1, optM_isBase.1 T2⟩
  exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨0, by simp, by rw [hY, hP0]⟩)

/-- From a splitting for `w₁ + w₂` to a splitting for `w₁ + w₂ + χ_e`. -/
theorem step (M₁ M₂ : Matroid (Fin m)) (h₁ : ∃ B, IB M₁ B) (h₂ : ∃ B, IB M₂ B)
    (w₁ w₂ : Fin m → ℤ) (B : Finset (Fin m)) (hB1 : Opt M₁ w₁ B) (hB2 : Opt M₂ w₂ B)
    (e : Fin m) :
    ∃ (B' : Finset (Fin m)) (v₁ v₂ : Fin m → ℤ),
      v₁ + v₂ = w₁ + w₂ + ind e ∧ Opt M₁ v₁ B' ∧ Opt M₂ v₂ B' := by
  by_cases heB : e ∈ B
  · exact ⟨B, w₁ + ind e, w₂, by abel, opt_add_ind e hB1 heB, hB2⟩
  by_cases hA : ∃ n x, reachIn (arc M₁ M₂ w₁ w₂ B) e n x ∧ x ∈ B ∧ Opt M₂ w₂ (exch B x e)
  · obtain ⟨x, hx, hxB, hxe⟩ := Nat.find_spec hA
    obtain ⟨B', heB', o1, o2⟩ := step_cycle M₁ M₂ h₁ h₂ w₁ w₂ B hB1 hB2 e heB _ x hx hxB hxe
      (fun s hs y h1 h2 h3 => Nat.find_min hA hs ⟨y, h1, h2, h3⟩)
    exact ⟨B', w₁ + ind e, w₂, by abel, opt_add_ind e o1 heB', o2⟩
  push Not at hA
  obtain ⟨iR, hiR⟩ : ∃ iR : Fin m → ℤ, ∀ v,
      iR v = if ∃ n, reachIn (arc M₁ M₂ w₁ w₂ B) e n v then 1 else 0 := ⟨_, fun _ => rfl⟩
  have hRe : iR e = 1 := by rw [hiR, if_pos ⟨0, rfl⟩]
  have hR01 : ∀ v, iR v = 0 ∨ iR v = 1 := fun v => by rw [hiR]; split_ifs <;> simp
  refine ⟨B, w₁ + iR, w₂ + ind e - iR, by abel, ?_, ?_⟩
  · refine local_global M₁ _ hB1.1 (fun x hx y hy hxy => ?_)
    simp only [Pi.add_apply]
    have hle : w₁ y ≤ w₁ x := by
      have := hB1.2 _ hxy; rw [weight_exch _ hx hy] at this; linarith
    rcases hle.lt_or_eq with hlt | heq
    · rcases hR01 x with h | h <;> rcases hR01 y with h' | h' <;> linarith
    · have ho : Opt M₁ w₁ (exch B x y) := (opt_exch_iff hB1 hx hy).2 ⟨hxy, heq.symm⟩
      have hRyx : iR y = 1 → iR x = 1 := by
        rw [hiR, hiR]
        split_ifs with h1 h2
        · simp
        · obtain ⟨n, hn⟩ := h1
          exact absurd ⟨n + 1, y, hn, Or.inl ⟨hy, hx, ho⟩⟩ h2
        · simp
        · simp
      rcases hR01 x with h | h <;> rcases hR01 y with h' | h'
      · linarith
      · have := hRyx h'; omega
      · linarith
      · linarith
  · refine local_global M₂ _ hB2.1 (fun x hx y hy hxy => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, ind]
    have hxe : x ≠ e := fun h => heB (h ▸ hx)
    rw [if_neg hxe]
    have hle : w₂ y ≤ w₂ x := by
      have := hB2.2 _ hxy; rw [weight_exch _ hx hy] at this; linarith
    have hye : y = e → iR y = 1 := fun h => h ▸ hRe
    rcases hle.lt_or_eq with hlt | heq
    · by_cases h : y = e
      · rw [if_pos h, hye h]
        rcases hR01 x with h1 | h1 <;> linarith
      · rw [if_neg h]
        rcases hR01 x with h1 | h1 <;> rcases hR01 y with h' | h' <;> linarith
    · have ho : Opt M₂ w₂ (exch B x y) := (opt_exch_iff hB2 hx hy).2 ⟨hxy, heq.symm⟩
      have hRxy : iR x = 1 → iR y = 1 ∧ y ≠ e := by
        rw [hiR x, hiR y]
        split_ifs with h1 h2
        · intro _
          refine ⟨rfl, ?_⟩
          rintro rfl
          obtain ⟨n, hn⟩ := h1
          exact hA n x hn hx ho
        · obtain ⟨n, hn⟩ := h1
          exact absurd ⟨n + 1, x, hn, Or.inr ⟨hx, hy, ho⟩⟩ h2
        · simp
        · simp
      by_cases h : y = e
      · rw [if_pos h, hye h]
        rcases hR01 x with h1 | h1
        · linarith
        · exact absurd h (hRxy h1).2
      · rw [if_neg h]
        rcases hR01 x with h1 | h1
        · rcases hR01 y with h' | h' <;> linarith
        · rw [h1, (hRxy h1).1]; linarith

/-- Weight splitting, in terms of `Opt`. -/
theorem split (M₁ M₂ : Matroid (Fin m)) (B0 : Finset (Fin m)) (hB01 : IB M₁ B0)
    (hB02 : IB M₂ B0) (w : Fin m → ℤ) :
    ∃ (B : Finset (Fin m)) (w₁ w₂ : Fin m → ℤ), w = w₁ + w₂ ∧ Opt M₁ w₁ B ∧ Opt M₂ w₂ B := by
  set c : ℤ := -(∑ e, |w e|) with hc
  have hcw : ∀ e, c ≤ w e := fun e => by
    have h1 : |w e| ≤ ∑ e, |w e| :=
      Finset.single_le_sum (f := fun e => |w e|) (fun i _ => abs_nonneg (w i)) (Finset.mem_univ e)
    have h2 := neg_abs_le (w e)
    linarith
  have key : ∀ n : ℕ, ∀ u : Fin m → ℤ, (∀ e, 0 ≤ u e) → ∑ e, u e = n →
      ∃ (B : Finset (Fin m)) (w₁ w₂ : Fin m → ℤ),
        (fun _ => c) + u = w₁ + w₂ ∧ Opt M₁ w₁ B ∧ Opt M₂ w₂ B := by
    intro n
    induction n with
    | zero =>
      intro u hu hs
      have hu0 : u = 0 := by
        funext v
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hu i)).1 (by simpa using hs) v
          (Finset.mem_univ v)
        simpa using this
      refine ⟨B0, fun _ => c, 0, by rw [hu0], ⟨hB01, fun A hA => ?_⟩, ⟨hB02, fun A hA => ?_⟩⟩
      · simp only [weight, Finset.sum_const, card_eq hA hB01]; exact le_refl _
      · simp [weight]
    | succ n ih =>
      intro u hu hs
      obtain ⟨e, he⟩ : ∃ e, 0 < u e := by
        by_contra hcon
        push Not at hcon
        have : ∑ e, u e = 0 := Finset.sum_eq_zero (fun i _ => le_antisymm (hcon i) (hu i))
        omega
      have hu' : ∀ v, 0 ≤ (u - ind e) v := fun v => by
        simp only [Pi.sub_apply, ind]; split_ifs with h
        · subst h; omega
        · simpa using hu v
      have hs' : ∑ v, (u - ind e) v = n := by
        simp only [Pi.sub_apply, Finset.sum_sub_distrib, ind, Finset.sum_ite_eq', Finset.mem_univ,
          if_true]
        rw [hs]; push_cast; ring
      obtain ⟨B, w₁, w₂, hsum, o1, o2⟩ := ih _ hu' hs'
      obtain ⟨B', v₁, v₂, hv, p1, p2⟩ := step M₁ M₂ ⟨B0, hB01⟩ ⟨B0, hB02⟩ w₁ w₂ B o1 o2 e
      refine ⟨B', v₁, v₂, ?_, p1, p2⟩
      rw [hv, ← hsum]
      abel
  obtain ⟨u, hu⟩ : ∃ u : Fin m → ℤ, u = w - fun _ => c := ⟨_, rfl⟩
  have hnn : ∀ e, 0 ≤ u e := fun e => by rw [hu]; simp only [Pi.sub_apply]; linarith [hcw e]
  obtain ⟨B, w₁, w₂, hsum, o1, o2⟩ := key (∑ e, u e).toNat u hnn
    (Int.toNat_of_nonneg (Finset.sum_nonneg (fun i _ => hnn i))).symm
  refine ⟨B, w₁, w₂, ?_, o1, o2⟩
  rw [← hsum, hu]
  abel

end LowDiameterNashWilliams.Main.Dev.Frank

namespace LowDiameterNashWilliams.Main

open LowDiameterNashWilliams.Main.Dev.Frank in
theorem chk_theorem_3 :
  ∀ m : ℕ, ∀ M₁ M₂ : Matroid (Fin m), M₁.E = Set.univ → M₂.E = Set.univ →
  (∃ B : Finset (Fin m), M₁.IsBase (B : Set (Fin m)) ∧ M₂.IsBase (B : Set (Fin m))) →
  ∀ w : Fin m → ℤ, ∃ (B : Finset (Fin m)) (w₁ w₂ : Fin m → ℤ),
    M₁.IsBase (B : Set (Fin m)) ∧ M₂.IsBase (B : Set (Fin m)) ∧
    w = w₁ + w₂ ∧
    (∀ A : Finset (Fin m), M₁.IsBase (A : Set (Fin m)) → weight w₁ A ≤ weight w₁ B) ∧
    (∀ A : Finset (Fin m), M₂.IsBase (A : Set (Fin m)) → weight w₂ A ≤ weight w₂ B) := by
  intro m M₁ M₂ _ _ hcommon w
  obtain ⟨B0, h1, h2⟩ := hcommon
  obtain ⟨B, w₁, w₂, hw, o1, o2⟩ := split M₁ M₂ B0 h1 h2 w
  exact ⟨B, w₁, w₂, o1.1, o2.1, hw, o1.2, o2.2⟩

end LowDiameterNashWilliams.Main
end

theorem solution : type_of% @LowDiameterNashWilliams.Main.chk_theorem_3 := @LowDiameterNashWilliams.Main.chk_theorem_3
