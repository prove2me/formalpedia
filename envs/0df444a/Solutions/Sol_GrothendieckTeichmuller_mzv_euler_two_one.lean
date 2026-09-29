-- Prove2me | solution 1 for GrothendieckTeichmuller.mzv_euler_two_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T05:34:15.01184+00:00
-- url     : https://prove2.me/submissions/0d145ffd-b8ba-4ca3-ab88-395786590f85

import Definitions.Def_GT_multizeta

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators
open GrothendieckTeichmuller

/-!
# Euler's identity `zeta(2,1) = zeta(3)`

Mathlib has no multiple zeta values.  The symmetric double sum `sum 1/(m n (m+n))` is evaluated
in two ways — by the symmetry `m <-> n` and by partial fractions — and the identity follows.
Everything lives in a private namespace.
-/

namespace MZVEuler


/-- The harmonic number `H n = ∑_{i<n} 1/(i+1)`. -/
noncomputable def Har (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, (1 : ℝ) / (i + 1)

theorem Har_succ (n : ℕ) : Har (n + 1) = Har n + 1 / (n + 1) := by
  rw [Har, Har, Finset.sum_range_succ]

theorem Har_nonneg (n : ℕ) : 0 ≤ Har n :=
  Finset.sum_nonneg fun i _ => by positivity

theorem Har_mono {m n : ℕ} (h : m ≤ n) : Har m ≤ Har n := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) h)) ?_
  intro i _ _
  positivity

/-- The tail bound `H (N + k) - H N ≤ k / (N + 1)`. -/
theorem Har_diff_le (N k : ℕ) : Har (N + k) - Har N ≤ (k : ℝ) / (N + 1) := by
  have h : Har (N + k) - Har N = ∑ i ∈ Finset.Ico N (N + k), (1 : ℝ) / (i + 1) := by
    rw [Har, Har, ← Finset.sum_range_add_sum_Ico _ (Nat.le_add_right N k)]
    ring
  rw [h]
  calc ∑ i ∈ Finset.Ico N (N + k), (1 : ℝ) / (i + 1)
      ≤ ∑ i ∈ Finset.Ico N (N + k), (1 : ℝ) / (N + 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hiN : N ≤ i := (Finset.mem_Ico.1 hi).1
        have : (N : ℝ) + 1 ≤ (i : ℝ) + 1 := by
          have : (N : ℝ) ≤ (i : ℝ) := by exact_mod_cast hiN
          linarith
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) this
    _ = (k : ℝ) / (N + 1) := by
        rw [Finset.sum_const, Nat.card_Ico]
        simp [nsmul_eq_mul]
        ring

theorem sum_shift (N j : ℕ) :
    ∑ i ∈ Finset.range N, (1 : ℝ) / (i + j + 2) = Har (N + j + 1) - Har (j + 1) := by
  have h : Har (N + j + 1) - Har (j + 1)
      = ∑ i ∈ Finset.Ico (j + 1) (N + j + 1), (1 : ℝ) / (i + 1) := by
    rw [Har, Har, ← Finset.sum_range_add_sum_Ico _ (by omega : j + 1 ≤ N + j + 1)]
    ring
  rw [h, Finset.sum_Ico_eq_sum_range]
  have hc : N + j + 1 - (j + 1) = N := by omega
  rw [hc]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring_nf

theorem summable_inv_pow (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 1) ^ k) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ k) :=
    Real.summable_one_div_nat_pow.2 (by omega)
  have h2 := (summable_nat_add_iff 1).2 h
  refine h2.congr fun i => ?_
  push_cast
  ring

theorem summable_pf (j : ℕ) :
    Summable (fun i : ℕ => (1 : ℝ) / ((i + 1) * (i + j + 2))) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (summable_inv_pow 2 le_rfl)
  have h2 : ((i : ℝ) + 1) ≤ ((i : ℝ) + j + 2) := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity), sq]
  nlinarith [(by positivity : (0:ℝ) < (i : ℝ) + 1)]

theorem tsum_pf (j : ℕ) :
    ∑' i : ℕ, (1 : ℝ) / ((i + 1) * (i + j + 2)) = Har (j + 1) / (j + 1) := by
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hpart : ∀ N : ℕ, ∑ i ∈ Finset.range N, (1 : ℝ) / ((i + 1) * (i + j + 2))
      = (Har N - (Har (N + j + 1) - Har (j + 1))) / (j + 1) := by
    intro N
    have hterm : ∀ i : ℕ, (1 : ℝ) / ((i + 1) * (i + j + 2))
        = ((1 : ℝ) / (i + 1) - 1 / (i + j + 2)) / (j + 1) := by
      intro i
      have h1 : ((i : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((i : ℝ) + j + 2) ≠ 0 := by positivity
      field_simp
      ring
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range N) => hterm i)]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, sum_shift N j]
    congr 2
  have h1 : Filter.Tendsto
      (fun N => ∑ i ∈ Finset.range N, (1 : ℝ) / ((i + 1) * (i + j + 2))) Filter.atTop
      (nhds (∑' i : ℕ, (1 : ℝ) / ((i + 1) * (i + j + 2)))) :=
    (summable_pf j).hasSum.tendsto_sum_nat
  have htail : Filter.Tendsto (fun N : ℕ => Har (N + j + 1) - Har N) Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun N => ?_) (fun N => ?_)
      (show Filter.Tendsto (fun N : ℕ => ((j : ℝ) + 1) / (N + 1)) Filter.atTop (nhds 0) from ?_)
    · have := Har_mono (show N ≤ N + j + 1 by omega)
      linarith
    · have := Har_diff_le N (j + 1)
      rw [show N + (j + 1) = N + j + 1 by omega] at this
      push_cast at this
      linarith
    · have hto : Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1)) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      exact Filter.Tendsto.div_atTop tendsto_const_nhds hto
  have h2 : Filter.Tendsto
      (fun N => ∑ i ∈ Finset.range N, (1 : ℝ) / ((i + 1) * (i + j + 2))) Filter.atTop
      (nhds (Har (j + 1) / (j + 1))) := by
    have hrw : ∀ N : ℕ, ∑ i ∈ Finset.range N, (1 : ℝ) / ((i + 1) * (i + j + 2))
        = (Har (j + 1) - (Har (N + j + 1) - Har N)) / (j + 1) := by
      intro N
      rw [hpart N]
      ring_nf
    simp only [hrw]
    have := (htail.const_sub (Har (j + 1))).div_const ((j : ℝ) + 1)
    simpa using this
  exact tendsto_nhds_unique h1 h2

/-! ## The symmetric double sum -/

noncomputable def Fg (p : ℕ × ℕ) : ℝ :=
  1 / (((p.1 : ℝ) + 1) * ((p.1 : ℝ) + (p.2 : ℝ) + 2) ^ 2)

noncomputable def Hg (p : ℕ × ℕ) : ℝ :=
  1 / (((p.2 : ℝ) + 1) * ((p.1 : ℝ) + (p.2 : ℝ) + 2) ^ 2)

noncomputable def Gg (p : ℕ × ℕ) : ℝ :=
  1 / (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) * ((p.1 : ℝ) + (p.2 : ℝ) + 2))

theorem Fg_nonneg (p : ℕ × ℕ) : 0 ≤ Fg p := by unfold Fg; positivity

theorem Gg_eq (p : ℕ × ℕ) : Gg p = Fg p + Hg p := by
  unfold Fg Hg Gg
  have h1 : ((p.1 : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((p.2 : ℝ) + 1) ≠ 0 := by positivity
  have h3 : ((p.1 : ℝ) + (p.2 : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

theorem Hg_swap (p : ℕ × ℕ) : Hg (Prod.swap p) = Fg p := by
  unfold Fg Hg
  simp only [Prod.fst_swap, Prod.snd_swap]
  ring_nf

/-- The tail of `ζ(2)` beyond `i + 1` is at most `1 / (i + 1)`. -/
theorem tail_sq_le (i : ℕ) :
    ∑' j : ℕ, (1 : ℝ) / (((i : ℝ) + (j : ℝ) + 2) ^ 2) ≤ 1 / ((i : ℝ) + 1) := by
  refine Real.tsum_le_of_sum_range_le (fun j => by positivity) fun N => ?_
  have hstep : ∀ j ∈ Finset.range N, (1 : ℝ) / (((i : ℝ) + (j : ℝ) + 2) ^ 2)
      ≤ (fun t : ℕ => (1 : ℝ) / ((i : ℝ) + (t : ℝ) + 1)) j
        - (fun t : ℕ => (1 : ℝ) / ((i : ℝ) + (t : ℝ) + 1)) (j + 1) := by
    intro j _
    have h1 : (0 : ℝ) < (i : ℝ) + (j : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (i : ℝ) + (j : ℝ) + 2 := by positivity
    simp only []
    push_cast
    rw [show (1 : ℝ) / ((i : ℝ) + (j : ℝ) + 1) - 1 / ((i : ℝ) + ((j : ℝ) + 1) + 1)
        = 1 / (((i : ℝ) + (j : ℝ) + 1) * ((i : ℝ) + (j : ℝ) + 2)) by
      field_simp
      ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity), sq]
    nlinarith
  calc ∑ j ∈ Finset.range N, (1 : ℝ) / (((i : ℝ) + (j : ℝ) + 2) ^ 2)
      ≤ ∑ j ∈ Finset.range N, ((fun t : ℕ => (1 : ℝ) / ((i : ℝ) + (t : ℝ) + 1)) j
          - (fun t : ℕ => (1 : ℝ) / ((i : ℝ) + (t : ℝ) + 1)) (j + 1)) :=
        Finset.sum_le_sum hstep
    _ = (1 : ℝ) / ((i : ℝ) + 1) - 1 / ((i : ℝ) + (N : ℝ) + 1) := by
        rw [Finset.sum_range_sub' (fun t : ℕ => (1 : ℝ) / ((i : ℝ) + (t : ℝ) + 1))]
        norm_num
    _ ≤ (1 : ℝ) / ((i : ℝ) + 1) := by
        have : (0 : ℝ) ≤ 1 / ((i : ℝ) + (N : ℝ) + 1) := by positivity
        linarith

theorem summable_Fg_slice (i : ℕ) : Summable (fun j : ℕ => Fg (i, j)) := by
  refine Summable.of_nonneg_of_le (fun j => Fg_nonneg _) (fun j => ?_) (summable_inv_pow 2 le_rfl)
  show (1 : ℝ) / (((i : ℝ) + 1) * (((i : ℝ) + (j : ℝ) + 2) ^ 2)) ≤ 1 / ((j : ℝ) + 1) ^ 2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : ((j : ℝ) + 1) ≤ ((i : ℝ) + (j : ℝ) + 2) := by
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  have h2 : (1 : ℝ) ≤ (i : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  nlinarith [sq_nonneg ((j : ℝ) + 1), (by positivity : (0:ℝ) < ((j : ℝ) + 1) ^ 2)]

theorem tsum_Fg_slice (i : ℕ) :
    ∑' j : ℕ, Fg (i, j) = (1 / ((i : ℝ) + 1)) * ∑' j : ℕ, (1 : ℝ) / (((i:ℝ) + (j:ℝ) + 2) ^ 2) := by
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  unfold Fg
  simp only []
  rw [div_mul_div_comm]
  norm_num

theorem summable_Fg : Summable Fg := by
  refine (summable_prod_of_nonneg (fun p => Fg_nonneg p)).2 ⟨summable_Fg_slice, ?_⟩
  refine Summable.of_nonneg_of_le (fun i => tsum_nonneg fun j => Fg_nonneg _) (fun i => ?_)
    (summable_inv_pow 2 le_rfl)
  rw [tsum_Fg_slice i]
  have h := tail_sq_le i
  have hpos : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
  calc (1 / ((i : ℝ) + 1)) * ∑' j : ℕ, (1 : ℝ) / (((i:ℝ) + (j:ℝ) + 2) ^ 2)
      ≤ (1 / ((i : ℝ) + 1)) * (1 / ((i : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_left h (le_of_lt hpos)
    _ = 1 / ((i : ℝ) + 1) ^ 2 := by rw [div_mul_div_comm, sq]; norm_num

theorem summable_Hg : Summable Hg := by
  have := (Equiv.prodComm ℕ ℕ).summable_iff (f := Hg)
  rw [← this]
  refine summable_Fg.congr fun p => ?_
  exact (Hg_swap p).symm

theorem summable_Gg : Summable Gg := by
  refine (summable_Fg.add summable_Hg).congr fun p => ?_
  exact (Gg_eq p).symm

theorem tsum_Hg_eq : ∑' p : ℕ × ℕ, Hg p = ∑' p : ℕ × ℕ, Fg p := by
  rw [← (Equiv.prodComm ℕ ℕ).tsum_eq Hg]
  exact tsum_congr fun p => Hg_swap p

theorem tsum_Gg_two : ∑' p : ℕ × ℕ, Gg p = 2 * ∑' p : ℕ × ℕ, Fg p := by
  have h : ∑' p : ℕ × ℕ, Gg p = (∑' p : ℕ × ℕ, Fg p) + ∑' p : ℕ × ℕ, Hg p := by
    rw [← summable_Fg.tsum_add summable_Hg]
    exact tsum_congr Gg_eq
  rw [h, tsum_Hg_eq]
  ring

/-! ## Identifying the two evaluations -/

theorem tsum_Gg_har : ∑' p : ℕ × ℕ, Gg p = ∑' j : ℕ, Har (j + 1) / ((j : ℝ) + 1) ^ 2 := by
  have hswap : Summable (fun p : ℕ × ℕ => Gg (Prod.swap p)) :=
    ((Equiv.prodComm ℕ ℕ).summable_iff (f := Gg)).2 summable_Gg
  have h1 : ∑' p : ℕ × ℕ, Gg p = ∑' p : ℕ × ℕ, Gg (Prod.swap p) :=
    ((Equiv.prodComm ℕ ℕ).tsum_eq Gg).symm
  rw [h1, hswap.tsum_prod' (fun b => hswap.prod_factor b)]
  refine tsum_congr fun j => ?_
  have hterm : ∀ i : ℕ, Gg (Prod.swap (j, i))
      = (1 / ((j : ℝ) + 1)) * ((1 : ℝ) / ((i + 1) * (i + j + 2))) := by
    intro i
    unfold Gg
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [div_mul_div_comm]
    norm_num
    ring
  rw [tsum_congr hterm, tsum_mul_left, tsum_pf j]
  rw [div_mul_div_comm]
  norm_num
  ring

theorem mzvTail_one_succ (j : ℕ) : mzvTail [1] (j + 1) = Har j := by
  rw [mzvTail]
  rw [tsum_eq_sum (s := Finset.range (j + 1)) (f := fun t : ℕ =>
    if 1 ≤ t ∧ t < j + 1 then (((t : ℝ)) ^ (1 : ℕ))⁻¹ * mzvTail [] t else 0) ?_]
  · rw [Finset.sum_range_succ']
    simp only [mzvTail, mul_one, pow_one]
    rw [Har]
    have hz : (if 1 ≤ 0 ∧ 0 < j + 1 then ((0 : ℕ) : ℝ)⁻¹ else 0) = 0 := by norm_num
    rw [hz, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i < j := Finset.mem_range.1 hi
    rw [if_pos (by omega)]
    push_cast
    rw [one_div]
  · intro t ht
    rw [if_neg]
    intro hc
    exact ht (Finset.mem_range.2 hc.2)

/-! ## The `m`-outer form -/

noncomputable def Wf (p : ℕ × ℕ) : ℝ :=
  if p.2 < p.1 then 1 / (((p.1 : ℝ) + 1) ^ 2 * ((p.2 : ℝ) + 1)) else 0

def phi (p : ℕ × ℕ) : ℕ × ℕ := (p.1 + p.2 + 1, p.1)

theorem phi_inj : Function.Injective phi := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [phi, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  subst h2
  exact Prod.ext rfl (by omega)

theorem Wf_phi (p : ℕ × ℕ) : Wf (phi p) = Fg p := by
  unfold Wf phi Fg
  simp only []
  rw [if_pos (by omega)]
  push_cast
  rw [show ((p.1 : ℝ) + (p.2 : ℝ) + 1 + 1) = (p.1 : ℝ) + (p.2 : ℝ) + 2 by ring]
  ring

theorem Wf_off {q : ℕ × ℕ} (h : q ∉ Set.range phi) : Wf q = 0 := by
  unfold Wf
  rw [if_neg]
  intro hlt
  refine h ⟨(q.2, q.1 - q.2 - 1), ?_⟩
  have h1 : q.2 + (q.1 - q.2 - 1) + 1 = q.1 := by omega
  show ((q.2 + (q.1 - q.2 - 1) + 1 : ℕ), q.2) = q
  rw [h1]

theorem hasSum_Wf : HasSum Wf (∑' p : ℕ × ℕ, Fg p) := by
  refine (phi_inj.hasSum_iff (fun x hx => Wf_off hx)).1 ?_
  have hfun : (Wf ∘ phi) = Fg := funext Wf_phi
  rw [hfun]
  exact summable_Fg.hasSum

theorem summable_Wf : Summable Wf := hasSum_Wf.summable

theorem tsum_Wf_eq : ∑' q : ℕ × ℕ, Wf q = ∑' p : ℕ × ℕ, Fg p := hasSum_Wf.tsum_eq

theorem tsum_Wf_slice (j : ℕ) : ∑' t : ℕ, Wf (j, t) = Har j / ((j : ℝ) + 1) ^ 2 := by
  rw [tsum_eq_sum (s := Finset.range j) (f := fun t : ℕ => Wf (j, t)) ?_]
  · rw [Har, Finset.sum_div]
    refine Finset.sum_congr rfl fun t ht => ?_
    have hlt : t < j := Finset.mem_range.1 ht
    unfold Wf
    simp only []
    rw [if_pos hlt]
    rw [div_div]
    ring_nf
  · intro t ht
    unfold Wf
    simp only []
    rw [if_neg]
    intro hc
    exact ht (Finset.mem_range.2 hc)

theorem summable_har_sq : Summable (fun j : ℕ => Har j / ((j : ℝ) + 1) ^ 2) := by
  have hW0 : ∀ p : ℕ × ℕ, 0 ≤ Wf p := by
    intro p
    unfold Wf
    split
    · positivity
    · exact le_rfl
  exact ((summable_prod_of_nonneg hW0).1 summable_Wf).2.congr fun j => tsum_Wf_slice j

/-! ## Unfolding the multiple zeta values -/

theorem mzv3_eq : mzv [3] = ∑' j : ℕ, (1 : ℝ) / ((j : ℝ) + 1) ^ 3 := by
  have hshift : ∀ j : ℕ,
      (if 1 ≤ j + 1 then (((j + 1 : ℕ) : ℝ) ^ (3 : ℕ))⁻¹ * mzvTail [] (j + 1) else 0)
        = (1 : ℝ) / ((j : ℝ) + 1) ^ 3 := by
    intro j
    rw [if_pos (by omega)]
    simp only [mzvTail, mul_one]
    push_cast
    rw [one_div]
  have hsum : Summable (fun j : ℕ =>
      if 1 ≤ j then (((j : ℕ) : ℝ) ^ (3 : ℕ))⁻¹ * mzvTail [] j else 0) := by
    rw [← summable_nat_add_iff 1]
    exact (summable_inv_pow 3 (by norm_num)).congr fun j => (hshift j).symm
  rw [mzv, hsum.tsum_eq_zero_add]
  simp only [hshift]
  norm_num

theorem mzv21_eq : mzv [2, 1] = ∑' j : ℕ, Har j / ((j : ℝ) + 1) ^ 2 := by
  have hshift : ∀ j : ℕ,
      (if 1 ≤ j + 1 then (((j + 1 : ℕ) : ℝ) ^ (2 : ℕ))⁻¹ * mzvTail [1] (j + 1) else 0)
        = Har j / ((j : ℝ) + 1) ^ 2 := by
    intro j
    rw [if_pos (by omega), mzvTail_one_succ]
    push_cast
    rw [inv_mul_eq_div]
  have hsum : Summable (fun j : ℕ =>
      if 1 ≤ j then (((j : ℕ) : ℝ) ^ (2 : ℕ))⁻¹ * mzvTail [1] j else 0) := by
    rw [← summable_nat_add_iff 1]
    exact summable_har_sq.congr fun j => (hshift j).symm
  rw [mzv, hsum.tsum_eq_zero_add]
  simp only [hshift]
  norm_num

theorem euler : mzv [2, 1] = mzv [3] := by
  have h1 : ∑' p : ℕ × ℕ, Gg p = 2 * ∑' p : ℕ × ℕ, Fg p := tsum_Gg_two
  have h2 : ∑' p : ℕ × ℕ, Gg p = ∑' j : ℕ, Har (j + 1) / ((j : ℝ) + 1) ^ 2 := tsum_Gg_har
  have h3 : ∑' j : ℕ, Har (j + 1) / ((j : ℝ) + 1) ^ 2
      = (∑' j : ℕ, Har j / ((j : ℝ) + 1) ^ 2) + ∑' j : ℕ, (1 : ℝ) / ((j : ℝ) + 1) ^ 3 := by
    rw [← summable_har_sq.tsum_add (summable_inv_pow 3 (by norm_num))]
    refine tsum_congr fun j => ?_
    rw [Har_succ]
    have hne : ((j : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  have h4 : ∑' p : ℕ × ℕ, Fg p = ∑' j : ℕ, Har j / ((j : ℝ) + 1) ^ 2 := by
    rw [← tsum_Wf_eq, summable_Wf.tsum_prod' (fun b => summable_Wf.prod_factor b)]
    exact tsum_congr tsum_Wf_slice
  rw [mzv21_eq, mzv3_eq]
  rw [h4] at h1
  linarith [h1, h2, h3]


end MZVEuler

theorem solution : GrothendieckTeichmuller.mzv [2, 1] = GrothendieckTeichmuller.mzv [3] :=
  MZVEuler.euler
