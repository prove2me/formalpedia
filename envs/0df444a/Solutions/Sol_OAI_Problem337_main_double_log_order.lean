-- Prove2me | solution 1 for OAI.Problem337.main_double_log_order
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:09:20.687559+00:00
-- url     : https://prove2.me/submissions/dff97c23-d564-49ad-b356-6c3f36203243

import Mathlib
import Definitions.Def_EgyptianFractions
import Definitions.Def_OAIQ8EF000
import Theorems.Thm_OAI_Problem337_RandomProducts_eventually_common_geometric_random_fractional_residues
import Theorems.Thm_OAI_Problem337_deterministic_mean_two_errors
import Theorems.Thm_OAI_Problem337_eventually_residue_level_moment
import Theorems.Thm_OAI_Problem337_main_upper_of_raw_density_supply

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CeilResidue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- The natural remainder specified by a ceiling step is the canonical
representative of the negative residue, including remainder zero. -/
theorem residue_eq_neg_zmod_val {u N z h : ℕ} (hh : h < u)
    (heq : u * z = N + h) : h = (-(N : ZMod u)).val := by
  have hzmod := congrArg (fun a : ℕ => (a : ZMod u)) heq
  simp only [Nat.cast_mul, Nat.cast_add, ZMod.natCast_self, zero_mul] at hzmod
  have hcast : (h : ZMod u) = -(N : ZMod u) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using hzmod.symm
  rw [← hcast, ZMod.val_natCast_of_lt hh]

theorem natural_ceil_residue_eq_neg_zmod_val (u N : ℕ) (hu : 0 < u) :
    u * ⌈(N : ℝ) / u⌉₊ - N = (-(N : ZMod u)).val := by
  obtain ⟨_, heq, hlt⟩ := natural_ceil_residue_spec u N hu
  exact residue_eq_neg_zmod_val hlt heq


/-- Exact conversion of a real residue cutoff to the fractional-part interval. -/
theorem residue_lt_iff_fract_lt {u N z h : ℕ} (hh : h < u)
    (heq : u * z = N + h) (δ : ℝ) :
    (h : ℝ) < δ * u ↔ Int.fract (-(N : ℝ) / u) < δ := by
  have hu : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (show 0 < u by omega)
  rw [← residue_div_eq_fract_neg hh heq]
  exact (div_lt_iff₀ hu).symm

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CyclicInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- A point to the right of an inner interval is separated from that interval
in both directions around the cyclic group. -/
theorem cyclic_sub_val_margin {q : ℕ} [NeZero q]
    (x y : ZMod q) (d : ℕ) (hy : d ≤ y.val)
    (hgap : y.val + d ≤ x.val) :
    d ≤ (x - y).val ∧ (x - y).val + d ≤ q := by
  have hxq := ZMod.val_lt x
  rw [ZMod.val_sub (by omega : y.val ≤ x.val)]
  omega

/-- Normalized version of the cyclic separation estimate. -/
theorem cyclic_sub_phase_margin {q : ℕ} [NeZero q]
    (x y : ZMod q) (d : ℕ) (hy : d ≤ y.val)
    (hgap : y.val + d ≤ x.val) :
    (d : ℝ) / q ≤ ((x - y).val : ℝ) / q ∧
    ((x - y).val : ℝ) / q ≤ 1 - (d : ℝ) / q := by
  obtain ⟨hlo, hhi⟩ := cyclic_sub_val_margin x y d hy hgap
  have hq : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  constructor
  · apply div_le_div_of_nonneg_right _ hq.le
    exact_mod_cast hlo
  · apply (div_le_iff₀ hq).mpr
    have hh : ((x - y).val : ℝ) + d ≤ q := by exact_mod_cast hhi
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hq)]
    linarith

/-- An inner initial interval with margin `d` lies away from every point
outside the initial target interval ending at `B+d`. -/
theorem cyclic_initial_interval_phase_margin {q : ℕ} [NeZero q]
    (x y : ZMod q) (d B : ℕ)
    (hx : B + d ≤ x.val) (hy : d ≤ y.val ∧ y.val ≤ B) :
    (d : ℝ) / q ≤ ((x - y).val : ℝ) / q ∧
    ((x - y).val : ℝ) / q ≤ 1 - (d : ℝ) / q :=
  cyclic_sub_phase_margin x y d hy.1 (by omega)

/-- A cyclic interval is the image of its ordinary representatives. -/
theorem cyclic_interval_eq_image {q : ℕ} [NeZero q] (a b : ℕ) (hb : b < q) :
    (Finset.univ.filter (fun x : ZMod q => a ≤ x.val ∧ x.val ≤ b)) =
      (Finset.Icc a b).image (fun n : ℕ => (n : ZMod q)) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hx
    exact ⟨x.val, Finset.mem_Icc.mpr hx, ZMod.natCast_zmod_val x⟩
  · rintro ⟨n, hn, rfl⟩
    have hn' := Finset.mem_Icc.mp hn
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : n < q)] using hn'

/-- Exact cardinality of a cyclic interval which does not cross zero. -/
theorem cyclic_interval_card {q : ℕ} [NeZero q] (a b : ℕ) (hb : b < q) :
    (Finset.univ.filter (fun x : ZMod q => a ≤ x.val ∧ x.val ≤ b)).card =
      b + 1 - a := by
  classical
  rw [cyclic_interval_eq_image a b hb]
  have hinj : Set.InjOn (fun n : ℕ => (n : ZMod q)) (Finset.Icc a b) := by
    intro n hn m hm hnm
    have hn' := Finset.mem_Icc.mp hn
    have hm' := Finset.mem_Icc.mp hm
    have h := congrArg ZMod.val hnm
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : n < q),
      Nat.mod_eq_of_lt (by omega : m < q)] using h
  rw [Finset.card_image_iff.mpr hinj, Nat.card_Icc]

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CyclicSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.CyclicSmoothing

lemma window_le_one {G : Type*} [AddCommGroup G] [Fintype G]
    (K : G → ℝ) (J : Finset G) (hK : ∀ x, 0 ≤ K x) (hmass : ∑ x, K x = 1)
    (x : G) : window K J x ≤ 1 := by
  calc
    window K J x ≤ ∑ y, K (x - y) := Finset.sum_le_univ_sum_of_nonneg (fun _ => hK _)
    _ = ∑ y, K y := (Equiv.subLeft x).sum_comp K
    _ = 1 := hmass

lemma window_le_of_kernel_bound {G : Type*} [AddGroup G]
    (K : G → ℝ) (J : Finset G) (x : G) (η : ℝ)
    (h : ∀ y ∈ J, K (x - y) ≤ η) : window K J x ≤ (J.card : ℝ) * η := by
  calc
    window K J x ≤ ∑ _y ∈ J, η := Finset.sum_le_sum h
    _ = (J.card : ℝ) * η := by simp

/-- The counting conclusion of the smoothing argument. The spectral input is
only the sampled mean lower bound; the geometric input is the kernel tail
bound outside the outer window. Repeated sample values are allowed. -/
theorem count_window_lower {G Ω : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (K : G → ℝ) (inner outer : Finset G) (samples : Finset Ω) (x : Ω → G)
    (E η : ℝ) (hK : ∀ y, 0 ≤ K y) (hmass : ∑ y, K y = 1) (hη : 0 ≤ η)
    (htail : ∀ z, z ∉ outer → ∀ y ∈ inner, K (z - y) ≤ η)
    (hmean : (samples.card : ℝ) * ((inner.card : ℝ) / Fintype.card G - E) ≤
      ∑ ω ∈ samples, window K inner (x ω)) :
    (samples.card : ℝ) * ((inner.card : ℝ) / Fintype.card G - E -
      (inner.card : ℝ) * η) ≤ ((samples.filter (fun ω => x ω ∈ outer)).card : ℝ) := by
  classical
  have hbound (ω : Ω) : window K inner (x ω) ≤
      (if x ω ∈ outer then (1 : ℝ) else 0) + (inner.card : ℝ) * η := by
    split_ifs with h
    · have hu := window_le_one K inner hK hmass (x ω)
      have hp : 0 ≤ (inner.card : ℝ) * η := by positivity
      linarith
    · simpa using window_le_of_kernel_bound K inner (x ω) η (htail _ h)
  have hsum := Finset.sum_le_sum (fun ω (_ : ω ∈ samples) => hbound ω)
  have hind : (∑ ω ∈ samples, if x ω ∈ outer then (1 : ℝ) else 0) =
      ((samples.filter (fun ω => x ω ∈ outer)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  rw [Finset.sum_add_distrib, hind] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith

end Problem337.CyclicSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FejerBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337.GeometricKernel

theorem kernel_nonneg (h : ℕ) (z : ℂ) : 0 ≤ kernel h z := by
  unfold kernel
  positivity

theorem cyclic_geometric_sum_eq {q : ℕ} [NeZero q] (h : ℕ) (x : ZMod q) :
    (∑ j ∈ Finset.range h, ZMod.stdAddChar ((j : ZMod q) * x)) =
      ∑ j ∈ Finset.range h, (ZMod.stdAddChar x) ^ j := by
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [nsmul_eq_mul] using ZMod.stdAddChar.map_nsmul_eq_pow j x

end Problem337.GeometricKernel

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FourierSecondMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators
open Complex ComplexConjugate

namespace Problem337

lemma re_finset_sum {α : Type*} (s : Finset α) (f : α → ℂ) :
    (∑ a ∈ s, f a).re = ∑ a ∈ s, (f a).re :=
  map_sum Complex.reAddGroupHom f s

/-- Expand a finite complex second moment into pairwise correlations. -/
theorem finite_complex_second_moment_identity {α β : Type*}
    (U : Finset α) (T : Finset β) (z : α → β → ℂ) :
    (∑ u ∈ U, ‖∑ t ∈ T, z u t‖ ^ 2) =
      ∑ t ∈ T, ∑ s ∈ T, (∑ u ∈ U, z u t * conj (z u s)).re := by
  have hpoint (u : α) : ‖∑ t ∈ T, z u t‖ ^ 2 =
      ∑ t ∈ T, ∑ s ∈ T, (z u t * conj (z u s)).re := by
    calc
      ‖∑ t ∈ T, z u t‖ ^ 2 =
          ((∑ t ∈ T, z u t) * conj (∑ t ∈ T, z u t)).re := by
            rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      _ = _ := by
        simp only [map_sum, Finset.sum_mul, Finset.mul_sum, re_finset_sum]
        rw [Finset.sum_comm]
  simp_rw [hpoint, re_finset_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_comm]

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CyclicKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open ComplexConjugate

namespace Problem337.CyclicSmoothing

lemma conj_stdAddChar {q : ℕ} [NeZero q] (x : ZMod q) :
    conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq,
    AddChar.norm_apply]
  simp

lemma stdAddChar_pow {q : ℕ} [NeZero q] (r : ℕ) (x : ZMod q) :
    (ZMod.stdAddChar x) ^ r = ZMod.stdAddChar ((r : ZMod q) * x) := by
  simpa only [nsmul_eq_mul] using (ZMod.stdAddChar.map_nsmul_eq_pow r x).symm

lemma cyclic_power_correlation {q h : ℕ} [NeZero q]
    (hhq : h ≤ q) {r s : ℕ} (hr : r < h) (hs : s < h) :
    (∑ x : ZMod q, (ZMod.stdAddChar x)^r * conj ((ZMod.stdAddChar x)^s)) =
      if r = s then (q : ℂ) else 0 := by
  have hcast : (r : ZMod q) - (s : ZMod q) = 0 ↔ r = s := by
    rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff']
    rw [Nat.mod_eq_of_lt (hr.trans_le hhq), Nat.mod_eq_of_lt (hs.trans_le hhq)]
  have hpoint (x : ZMod q) :
      (ZMod.stdAddChar x)^r * conj ((ZMod.stdAddChar x)^s) =
        ZMod.stdAddChar (x * ((r : ZMod q) - (s : ZMod q))) := by
    rw [stdAddChar_pow, stdAddChar_pow, conj_stdAddChar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hpoint]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
  simp [hcast, ZMod.card]

/-- Exact mass of the cyclic Fejer kernel below the modulus. -/
theorem sum_cyclic_kernel {q h : ℕ} [NeZero q] (hh : 0 < h) (hhq : h ≤ q) :
    (∑ x : ZMod q, GeometricKernel.kernel h (ZMod.stdAddChar x)) = (q : ℝ) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  simp only [GeometricKernel.kernel]
  rw [← Finset.sum_div]
  have hraw : (∑ x : ZMod q, ‖∑ r ∈ Finset.range h, (ZMod.stdAddChar x)^r‖ ^ 2) =
      (h : ℝ) * q := by
    rw [finite_complex_second_moment_identity]
    calc
      (∑ r ∈ Finset.range h, ∑ s ∈ Finset.range h,
          (∑ x : ZMod q, (ZMod.stdAddChar x)^r * conj ((ZMod.stdAddChar x)^s)).re) =
          ∑ r ∈ Finset.range h, ∑ s ∈ Finset.range h,
            (if r = s then (q : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro s hs
        rw [cyclic_power_correlation hhq (Finset.mem_range.mp hr) (Finset.mem_range.mp hs)]
        split_ifs <;> simp
      _ = ∑ _r ∈ Finset.range h, (q : ℝ) := by
        apply Finset.sum_congr rfl
        intro r hr
        simp [Finset.mem_range.mp hr]
      _ = (h : ℝ) * q := by simp
  rw [hraw]
  field_simp

lemma normalizedKernel_nonneg {q : ℕ} [NeZero q] (h : ℕ) (x : ZMod q) :
    0 ≤ normalizedKernel h x := by
  exact div_nonneg (GeometricKernel.kernel_nonneg _ _) (Nat.cast_nonneg q)

lemma sum_normalizedKernel {q h : ℕ} [NeZero q] (hh : 0 < h) (hhq : h ≤ q) :
    (∑ x : ZMod q, normalizedKernel h x) = 1 := by
  simp only [normalizedKernel]
  rw [← Finset.sum_div, sum_cyclic_kernel hh hhq]
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  exact div_self hq

end Problem337.CyclicSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FejerBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace Problem337

/-- Rounding the inner cyclic interval leaves fixed proportional margins. -/
theorem cyclic_interval_floor_budget (δ : ℝ) (q : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hscale : 128 ≤ δ * q) :
    let d := ⌊δ * q / 8⌋₊
    1 ≤ d ∧ 7 * d < q ∧ (8 * d : ℕ) ≤ δ * q ∧
    δ / 16 ≤ (d : ℝ) / q ∧
    11 * δ / 16 ≤ ((6 * d + 1 : ℕ) : ℝ) / q ∧
    ((6 * d + 1 : ℕ) : ℝ) / q ≤ δ := by
  let d := ⌊δ * q / 8⌋₊
  change 1 ≤ d ∧ 7 * d < q ∧ (8 * d : ℕ) ≤ δ * q ∧
    δ / 16 ≤ (d : ℝ) / q ∧
    11 * δ / 16 ≤ ((6 * d + 1 : ℕ) : ℝ) / q ∧
    ((6 * d + 1 : ℕ) : ℝ) / q ≤ δ
  have hq : (0 : ℝ) < q := by
    by_contra h
    have hq0 : (q : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg q)
    rw [hq0] at hscale
    norm_num at hscale
  have hdhi : (d : ℝ) ≤ δ * q / 8 := Nat.floor_le (by positivity)
  have hdlo : δ * q / 8 < (d : ℝ) + 1 := Nat.lt_floor_add_one _
  have hδq : δ * q ≤ (q : ℝ) := by nlinarith [mul_le_mul_of_nonneg_right hδ1 hq.le]
  have hd1 : 1 ≤ d := by exact_mod_cast (show (1 : ℝ) ≤ d by linarith)
  have hdb : 7 * d < q := by exact_mod_cast (show 7 * (d : ℝ) < q by linarith)
  refine ⟨hd1, hdb, ?_, ?_, ?_, ?_⟩
  · push_cast
    linarith
  · apply (le_div_iff₀ hq).mpr
    linarith
  · apply (le_div_iff₀ hq).mpr
    push_cast
    linarith
  · apply (div_le_iff₀ hq).mpr
    push_cast
    linarith

/-- A low-degree kernel simultaneously has small leakage and Fourier error. -/
theorem fejer_degree_floor_budget (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536) :
    let h := ⌊1 / (64 * δ ^ 3)⌋₊
    1 ≤ h ∧ 1 / (128 * δ ^ 3) ≤ (h : ℝ) ∧
    (h : ℝ) ≤ 1 / (64 * δ ^ 3) ∧
    64 / ((h : ℝ) * δ) ≤ δ / 8 ∧
    2 * (h : ℝ) * δ * δ ^ 3 ≤ δ / 32 := by
  let h := ⌊1 / (64 * δ ^ 3)⌋₊
  change 1 ≤ h ∧ 1 / (128 * δ ^ 3) ≤ (h : ℝ) ∧
    (h : ℝ) ≤ 1 / (64 * δ ^ 3) ∧
    64 / ((h : ℝ) * δ) ≤ δ / 8 ∧
    2 * (h : ℝ) * δ * δ ^ 3 ≤ δ / 32
  have hcube : 0 < δ ^ 3 := by positivity
  have hcubehi : δ ^ 3 ≤ (1 / 8 : ℝ) ^ 3 := by
    gcongr
    norm_num at *
    linarith
  have harg2 : (2 : ℝ) ≤ 1 / (64 * δ ^ 3) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 64 * δ ^ 3)).mpr
    norm_num at hcubehi
    linarith
  have hhhi : (h : ℝ) ≤ 1 / (64 * δ ^ 3) := Nat.floor_le (by positivity)
  have hhlo : 1 / (64 * δ ^ 3) < (h : ℝ) + 1 := Nat.lt_floor_add_one _
  have hh1 : 1 ≤ h := by exact_mod_cast (show (1 : ℝ) ≤ h by linarith)
  have hhpos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have half : 1 / (128 * δ ^ 3) = (1 / (64 * δ ^ 3)) / 2 := by ring
  have hhalf : 1 / (128 * δ ^ 3) ≤ (h : ℝ) := by rw [half]; linarith
  refine ⟨hh1, hhalf, hhhi, ?_, ?_⟩
  · calc
      64 / ((h : ℝ) * δ) ≤ 64 / ((1 / (128 * δ ^ 3)) * δ) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact mul_le_mul_of_nonneg_right hhalf hδ.le
      _ = 8192 * δ ^ 2 := by
        field_simp
        ring
      _ ≤ δ / 8 := by
        have hh := mul_le_mul_of_nonneg_right hsmall hδ.le
        nlinarith
  · calc
      2 * (h : ℝ) * δ * δ ^ 3 ≤ 2 * (1 / (64 * δ ^ 3)) * δ * δ ^ 3 := by
        gcongr
      _ = δ / 32 := by
        field_simp
        ring

/-- The chosen degree uses only the prescribed low frequencies. -/
theorem fejer_degree_frequency_bound (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536) :
    ⌊1 / (64 * δ ^ 3)⌋₊ ≤ ⌊1 / δ ^ 4⌋₊ := by
  apply Nat.floor_mono
  apply one_div_le_one_div_of_le (by positivity)
  have hh := mul_le_mul_of_nonneg_right (show δ ≤ 64 by linarith)
    (show 0 ≤ δ ^ 3 by positivity)
  nlinarith

/-- The three error budgets leave at least half the target interval mass. -/
theorem fejer_localization_budget (δ mass inner error leakage : ℝ)
    (hδ : 0 ≤ δ) (hinner : 11 * δ / 16 ≤ inner)
    (herror : error ≤ δ / 32) (hleakage : leakage ≤ δ / 8)
    (hmass : inner - error - leakage ≤ mass) : δ / 2 ≤ mass := by
  linarith

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FejerSampleMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.FejerSampleMean

/-- Translating the samples rotates every Fourier coefficient without changing
its norm. -/
theorem norm_sum_character_translate {q : ℕ} [NeZero q] {I : Type*}
    [Fintype I] (x : I → ZMod q) (a y : ZMod q) :
    ‖∑ t : I, ZMod.stdAddChar (a * (x t - y))‖ =
      ‖∑ t : I, ZMod.stdAddChar (a * x t)‖ := by
  simp_rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  rw [← Finset.sum_mul, norm_mul]
  simp

/-- Negating a frequency conjugates its coefficient. -/
theorem norm_sum_character_neg {q : ℕ} [NeZero q] {I : Type*}
    [Fintype I] (x : I → ZMod q) (a : ZMod q) :
    ‖∑ t : I, ZMod.stdAddChar ((-a) * x t)‖ =
      ‖∑ t : I, ZMod.stdAddChar (a * x t)‖ := by
  simp_rw [neg_mul, AddChar.map_neg_eq_conj]
  rw [← map_sum (starRingEnd ℂ) (fun t : I => ZMod.stdAddChar (a * x t)) Finset.univ]
  exact Complex.norm_conj _

/-- Off-diagonal correlations of the geometric packet are controlled by the
positive low frequencies, with no unmentioned negative-frequency assumption. -/
theorem packet_correlation_bound {q h : ℕ} [NeZero q] {I : Type*}
    [Fintype I] (x : I → ZMod q) (y : ZMod q) (E : ℝ)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l < h →
      ‖∑ t : I, ZMod.stdAddChar ((l : ZMod q) * x t)‖ ≤ E)
    (j k : Fin h) (hjk : j ≠ k) :
    ‖∑ t : I, ZMod.stdAddChar ((j.val : ZMod q) * (x t - y)) *
      (starRingEnd ℂ) (ZMod.stdAddChar ((k.val : ZMod q) * (x t - y)))‖ ≤ E := by
  have heq (t : I) :
      ZMod.stdAddChar ((j.val : ZMod q) * (x t - y)) *
          (starRingEnd ℂ) (ZMod.stdAddChar ((k.val : ZMod q) * (x t - y))) =
        ZMod.stdAddChar (((j.val : ZMod q) - (k.val : ZMod q)) * (x t - y)) := by
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [heq]
  rw [norm_sum_character_translate]
  have hne : j.val ≠ k.val := by intro he; exact hjk (Fin.ext he)
  by_cases hkj : k.val ≤ j.val
  · have hc : ((j.val : ZMod q) - (k.val : ZMod q)) = ((j.val - k.val : ℕ) : ZMod q) :=
      (Nat.cast_sub hkj).symm
    rw [hc]
    exact hfourier (j.val - k.val) (by omega) (by omega)
  · have hc : ((j.val : ZMod q) - (k.val : ZMod q)) = -((k.val - j.val : ℕ) : ZMod q) := by
      rw [Nat.cast_sub (by omega : j.val ≤ k.val)]
      ring
    rw [hc, norm_sum_character_neg]
    exact hfourier (k.val - j.val) (by omega) (by omega)

/-- Lower counterpart of the finite second-moment bound, using the same
honest off-diagonal correlation hypotheses. -/
theorem second_moment_lower {α β : Type*}
    (U : Finset α) (T : Finset β) (z : α → β → ℂ) (E : ℝ)
    (hunit : ∀ u ∈ U, ∀ t ∈ T, ‖z u t‖ = 1)
    (hcorr : ∀ t ∈ T, ∀ s ∈ T, t ≠ s →
      ‖∑ u ∈ U, z u t * (starRingEnd ℂ) (z u s)‖ ≤ E) :
    (U.card : ℝ) * T.card - (T.card : ℝ) * (T.card - 1 : ℝ) * E ≤
      ∑ u ∈ U, ‖∑ t ∈ T, z u t‖ ^ 2 := by
  classical
  rw [finite_complex_second_moment_identity]
  have hentry (t : β) (ht : t ∈ T) (s : β) (hs : s ∈ T) :
      -E + (if t = s then (U.card : ℝ) + E else 0) ≤
        (∑ u ∈ U, z u t * (starRingEnd ℂ) (z u s)).re := by
    by_cases hts : t = s
    · subst s
      have hd : (∑ u ∈ U, z u t * (starRingEnd ℂ) (z u t)).re = U.card := by
        simp only [re_finset_sum, Complex.mul_conj, Complex.ofReal_re]
        calc
          (∑ u ∈ U, Complex.normSq (z u t)) = ∑ _u ∈ U, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [Complex.normSq_eq_norm_sq, hunit u hu t ht]
            norm_num
          _ = _ := by simp
      simp [hd]
    · have hc := hcorr t ht s hs hts
      have hn := Complex.re_le_norm (-(∑ u ∈ U, z u t * (starRingEnd ℂ) (z u s)))
      simp only [Complex.neg_re, norm_neg] at hn
      simp only [ite_eq_right hts, add_zero]
      linarith
  calc
    _ = ∑ t ∈ T, ∑ s ∈ T, (-E + if t = s then (U.card : ℝ) + E else 0) := by
      have hrow (t : β) (ht : t ∈ T) :
          (∑ s ∈ T, (-E + if t = s then (U.card : ℝ) + E else 0)) =
            -(T.card : ℝ) * E + (U.card : ℝ) + E := by
        simp [Finset.sum_add_distrib, ht]
        ring
      simp_rw [Finset.sum_congr rfl hrow]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := Finset.sum_le_sum (fun t ht => Finset.sum_le_sum (fun s hs => hentry t ht s hs))

/-- The lower sampled mean of the geometric packet, before identifying the
packet with the named kernel. -/
theorem raw_packet_mean_lower {q h : ℕ} [NeZero q] {I : Type*}
    [Fintype I] [Nonempty I] (hh : 0 < h)
    (x : I → ZMod q) (y : ZMod q) (ε : ℝ)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l < h →
      ‖∑ t : I, ZMod.stdAddChar ((l : ZMod q) * x t)‖ ≤
        (Fintype.card I : ℝ) * ε) :
    1 - ((h : ℝ) - 1) * ε ≤
      (∑ t : I, ‖∑ j : Fin h,
        ZMod.stdAddChar ((j.val : ZMod q) * (x t - y))‖ ^ 2 / (h : ℝ)) /
        (Fintype.card I : ℝ) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hI : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hraw := second_moment_lower Finset.univ Finset.univ
    (fun t : I => fun j : Fin h => ZMod.stdAddChar ((j.val : ZMod q) * (x t - y)))
    ((Fintype.card I : ℝ) * ε)
    (fun _ _ _ _ => by simp)
    (fun j _ k _ hjk => packet_correlation_bound x y _ hfourier j k hjk)
  simp only [Finset.card_univ, Fintype.card_fin] at hraw
  rw [← Finset.sum_div]
  apply (le_div_iff₀ hI).2
  apply (le_div_iff₀ hhR).2
  calc
    _ = (Fintype.card I : ℝ) * h -
        (h : ℝ) * ((h : ℝ) - 1) * ((Fintype.card I : ℝ) * ε) := by ring
    _ ≤ _ := hraw

theorem packet_eq_kernel {q h : ℕ} [NeZero q] (x : ZMod q) :
    ‖∑ j : Fin h, ZMod.stdAddChar ((j.val : ZMod q) * x)‖ ^ 2 / (h : ℝ) =
      GeometricKernel.kernel h (ZMod.stdAddChar x) := by
  unfold GeometricKernel.kernel
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ZMod.stdAddChar ((j : ZMod q) * x)) h,
    GeometricKernel.cyclic_geometric_sum_eq]

/-- Low-frequency cancellation implies the expected lower mass at every
center of the named Fejér kernel. -/
theorem fejer_sample_mean_lower {q h : ℕ} [NeZero q] {I : Type*}
    [Fintype I] [Nonempty I] (hh : 0 < h)
    (x : I → ZMod q) (y : ZMod q) (ε : ℝ)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l < h →
      ‖∑ t : I, ZMod.stdAddChar ((l : ZMod q) * x t)‖ ≤
        (Fintype.card I : ℝ) * ε) :
    1 - ((h : ℝ) - 1) * ε ≤
      (∑ t : I, GeometricKernel.kernel h (ZMod.stdAddChar (x t - y))) /
        (Fintype.card I : ℝ) := by
  simpa only [packet_eq_kernel] using raw_packet_mean_lower hh x y ε hfourier

end Problem337.FejerSampleMean

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_GeometricCharacterBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- Geometric cancellation on the complex unit circle. -/
theorem norm_geometric_sum_le_two_div {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1)
    (N : ℕ) : ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hne, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

/-- The chord distance for a phase of period one. -/
theorem norm_exp_phase_sub_one (x : ℝ) :
    ‖Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) - 1‖ =
      2 * |Real.sin (Real.pi * x)| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : 2 * Real.pi * x / 2 = Real.pi * x := by ring
  rw [heq, Real.norm_eq_abs, abs_mul]
  norm_num

/-- Geometric cancellation expressed directly in terms of the phase sine. -/
theorem norm_geometric_phase_sum_le {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0)
    (N : ℕ) :
    ‖∑ j ∈ Finset.range N, (Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))) ^ j‖ ≤
      1 / |Real.sin (Real.pi * x)| := by
  have habs : 0 < |Real.sin (Real.pi * x)| := abs_pos.2 hx
  have hne : Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) ≠ 1 := by
    intro h
    have hn := norm_exp_phase_sub_one x
    rw [h, sub_self, norm_zero] at hn
    linarith
  have hbound := norm_geometric_sum_le_two_div
    (Complex.norm_exp_I_mul_ofReal (2 * Real.pi * x)) hne N
  rw [norm_exp_phase_sub_one] at hbound
  convert hbound using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

/-- Uniform lower bound for the sine away from both ends of a period. -/
theorem sin_pi_mul_lower_on_middle {δ x : ℝ} (hδ : 0 < δ)
    (hleft : δ ≤ x) (hright : x ≤ 1 - δ) :
    2 * δ ≤ Real.sin (Real.pi * x) := by
  have hx0 : 0 ≤ x := le_trans hδ.le hleft
  have hx1 : 0 ≤ 1 - x := by linarith
  by_cases hx : x ≤ 1 / 2
  · have hs := Real.mul_le_sin (x := Real.pi * x)
      (mul_nonneg Real.pi_pos.le hx0) (by nlinarith [Real.pi_pos])
    have heq : 2 / Real.pi * (Real.pi * x) = 2 * x := by field_simp
    rw [heq] at hs
    linarith
  · have hs := Real.mul_le_sin (x := Real.pi * (1 - x))
      (mul_nonneg Real.pi_pos.le hx1)
      (by nlinarith [Real.pi_pos])
    have heq : 2 / Real.pi * (Real.pi * (1 - x)) = 2 * (1 - x) := by field_simp
    rw [heq, show Real.pi * (1 - x) = Real.pi - Real.pi * x by ring,
      Real.sin_pi_sub] at hs
    linarith

/-- A phase at distance at least `δ` from the ends gives a uniform kernel bound. -/
theorem norm_geometric_phase_sum_le_middle {δ x : ℝ} (hδ : 0 < δ)
    (hleft : δ ≤ x) (hright : x ≤ 1 - δ) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, (Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))) ^ j‖ ≤
      1 / (2 * δ) := by
  have hs := sin_pi_mul_lower_on_middle hδ hleft hright
  have hspos : 0 < Real.sin (Real.pi * x) := by linarith
  calc
    _ ≤ 1 / |Real.sin (Real.pi * x)| := norm_geometric_phase_sum_le hspos.ne' N
    _ = 1 / Real.sin (Real.pi * x) := by rw [abs_of_pos hspos]
    _ ≤ 1 / (2 * δ) := one_div_le_one_div_of_le (by positivity) hs

/-- Fejer leakage at phase distance at least `δ` from zero modulo one. -/
theorem geometric_phase_fejer_le_middle {δ x : ℝ} (hδ : 0 < δ)
    (hleft : δ ≤ x) (hright : x ≤ 1 - δ) {N : ℕ} (hN : 0 < N) :
    ‖∑ j ∈ Finset.range N, (Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))) ^ j‖ ^ 2 /
      (N : ℝ) ≤ 1 / (4 * (N : ℝ) * δ ^ 2) := by
  have hs := norm_geometric_phase_sum_le_middle hδ hleft hright N
  have hs2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ (1 / (2 * δ)) ^ 2 / (N : ℝ) := div_le_div_of_nonneg_right hs2 hNR.le
    _ = 1 / (4 * (N : ℝ) * δ ^ 2) := by field_simp; ring

/-- The standard cyclic character is the period-one phase at its normalized value. -/
theorem stdAddChar_eq_normalized_phase {p : ℕ} [NeZero p] (a : ZMod p) :
    ZMod.stdAddChar a =
      Complex.exp (Complex.I * (2 * Real.pi * ((a.val : ℝ) / (p : ℝ)) : ℝ)) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  congr 1
  push_cast
  ring

/-- Squared cyclic kernel leakage, normalized to have total mass one. -/
theorem stdAddChar_fejer_le_middle {p : ℕ} [NeZero p] (a : ZMod p)
    {δ : ℝ} (hδ : 0 < δ) (hleft : δ ≤ (a.val : ℝ) / p)
    (hright : (a.val : ℝ) / p ≤ 1 - δ) {N : ℕ} (hN : 0 < N) :
    ‖∑ j ∈ Finset.range N, ZMod.stdAddChar ((j : ZMod p) * a)‖ ^ 2 / (N : ℝ) ≤
      1 / (4 * (N : ℝ) * δ ^ 2) := by
  have hpow : ∀ j : ℕ, ZMod.stdAddChar ((j : ZMod p) * a) = (ZMod.stdAddChar a) ^ j := by
    intro j
    simpa only [nsmul_eq_mul] using ZMod.stdAddChar.map_nsmul_eq_pow j a
  simp_rw [hpow, stdAddChar_eq_normalized_phase]
  exact geometric_phase_fejer_le_middle hδ hleft hright hN

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CyclicDiscrepancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.CyclicSmoothing

/-- The geometric and counting part of cyclic discrepancy. The sampled
spectral-mean input is separated from the exact kernel normalization. -/
theorem initial_interval_count_of_kernel_mean {q h d : ℕ} [NeZero q]
    {Ω : Type*} (samples : Finset Ω) (x : Ω → ZMod q) (ε : ℝ)
    (hh : 0 < h) (hhq : h ≤ q) (hd : 0 < d) (hdq : 7 * d < q)
    (hmean : ∀ y : ZMod q,
      (samples.card : ℝ) * (1 - ((h : ℝ) - 1) * ε) ≤
        ∑ ω ∈ samples, GeometricKernel.kernel h (ZMod.stdAddChar (x ω - y))) :
    (samples.card : ℝ) *
      (((6 * d + 1 : ℕ) : ℝ) / q -
        (((6 * d + 1 : ℕ) : ℝ) / q) * ((h : ℝ) - 1) * ε -
        (((6 * d + 1 : ℕ) : ℝ) / q) / (4 * (h : ℝ) * ((d : ℝ) / q)^2)) ≤
      ((samples.filter (fun ω => (x ω).val < 8 * d)).card : ℝ) := by
  classical
  let inner : Finset (ZMod q) := Finset.univ.filter (fun y => d ≤ y.val ∧ y.val ≤ 7 * d)
  let outer : Finset (ZMod q) := Finset.univ.filter (fun z => z.val < 8 * d)
  let A : ℝ := (inner.card : ℝ) / q
  let η : ℝ := (1 / (4 * (h : ℝ) * ((d : ℝ) / q)^2)) / q
  have hqR : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hβ : 0 < (d : ℝ) / q := div_pos hdR hqR
  have hcard : inner.card = 6 * d + 1 := by
    change (Finset.univ.filter (fun y : ZMod q => d ≤ y.val ∧ y.val ≤ 7 * d)).card = _
    rw [cyclic_interval_card d (7 * d) hdq]
    omega
  have htail : ∀ z : ZMod q, z ∉ outer → ∀ y ∈ inner,
      normalizedKernel h (z - y) ≤ η := by
    intro z hz y hy
    have hz' : 8 * d ≤ z.val := by simpa [outer] using hz
    have hy' : d ≤ y.val ∧ y.val ≤ 7 * d := by simpa [inner] using hy
    obtain ⟨hleft, hright⟩ := cyclic_initial_interval_phase_margin z y d (7 * d)
      (by omega) hy'
    have hb := stdAddChar_fejer_le_middle (z - y) hβ hleft hright hh
    rw [GeometricKernel.cyclic_geometric_sum_eq] at hb
    exact div_le_div_of_nonneg_right hb hqR.le
  have hsampled : (samples.card : ℝ) *
      ((inner.card : ℝ) / Fintype.card (ZMod q) - A * ((h : ℝ) - 1) * ε) ≤
      ∑ ω ∈ samples, window (normalizedKernel h) inner (x ω) := by
    have hsum := Finset.sum_le_sum (fun y (_ : y ∈ inner) => hmean y)
    have hdiv := div_le_div_of_nonneg_right hsum hqR.le
    simp only [Finset.sum_const, nsmul_eq_mul] at hdiv
    have hright : (∑ y ∈ inner, ∑ ω ∈ samples,
        GeometricKernel.kernel h (ZMod.stdAddChar (x ω - y))) / (q : ℝ) =
        ∑ ω ∈ samples, window (normalizedKernel h) inner (x ω) := by
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ω hω
      simp only [window, normalizedKernel, Finset.sum_div]
    rw [hright] at hdiv
    convert hdiv using 1
    all_goals try with_reducible_and_instances rfl
    simp only [ZMod.card, A]
    ring
  have hcount := count_window_lower (normalizedKernel h) inner outer samples x
    (A * ((h : ℝ) - 1) * ε) η (normalizedKernel_nonneg h)
    (sum_normalizedKernel hh hhq) (by dsimp [η]; positivity) htail hsampled
  have hfilter : samples.filter (fun ω => x ω ∈ outer) =
      samples.filter (fun ω => (x ω).val < 8 * d) := by simp [outer]
  rw [hfilter] at hcount
  convert hcount using 1
  all_goals try with_reducible_and_instances rfl
  simp only [ZMod.card, A, η, hcard]
  ring

/-- With the explicit low-degree choice, the smoothing errors leave half of
the desired interval mass. This lemma isolates the sampled kernel mean. -/
theorem cyclic_small_interval_of_kernel_mean {q : ℕ} [NeZero q]
    {Ω : Type*} (samples : Finset Ω) (x : Ω → ZMod q) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536) (hscale : 128 ≤ δ * q)
    (hdegree : ⌊1 / (64 * δ ^ 3)⌋₊ ≤ q)
    (hmean : ∀ y : ZMod q,
      (samples.card : ℝ) * (1 - ((⌊1 / (64 * δ ^ 3)⌋₊ : ℝ) - 1) * δ ^ 3) ≤
        ∑ ω ∈ samples, GeometricKernel.kernel ⌊1 / (64 * δ ^ 3)⌋₊
          (ZMod.stdAddChar (x ω - y))) :
    (δ / 2) * (samples.card : ℝ) ≤
      ((samples.filter (fun ω => ((x ω).val : ℝ) < δ * q)).card : ℝ) := by
  classical
  let h : ℕ := ⌊1 / (64 * δ ^ 3)⌋₊
  let d : ℕ := ⌊δ * q / 8⌋₊
  obtain ⟨hd1, hdq, hdouter, hdmargin, hinnerLo, hinnerHi⟩ :=
    cyclic_interval_floor_budget δ q hδ (by linarith) hscale
  obtain ⟨hh1, hhLo, hhHi, hleak, herror⟩ := fejer_degree_floor_budget δ hδ hsmall
  change 1 ≤ h at hh1
  change 1 ≤ d at hd1
  have hh : 0 < h := by omega
  have hd : 0 < d := by omega
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hhR1 : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hqR : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  let A : ℝ := ((6 * d + 1 : ℕ) : ℝ) / q
  let β : ℝ := (d : ℝ) / q
  have hβ : 0 < β := by dsimp [β]; positivity
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hAhi : A ≤ δ := hinnerHi
  have hAlo : 11 * δ / 16 ≤ A := hinnerLo
  have hβlo : δ / 16 ≤ β := hdmargin
  have hE : A * ((h : ℝ) - 1) * δ ^ 3 ≤ δ / 32 := by
    calc
      A * ((h : ℝ) - 1) * δ ^ 3 ≤ δ * (h : ℝ) * δ ^ 3 := by gcongr; linarith
      _ ≤ 2 * (h : ℝ) * δ * δ ^ 3 := by
        nlinarith [mul_nonneg (mul_nonneg hδ.le hhR.le) (show 0 ≤ δ ^ 3 by positivity)]
      _ ≤ δ / 32 := herror
  have hL : A / (4 * (h : ℝ) * β ^ 2) ≤ δ / 8 := by
    calc
      A / (4 * (h : ℝ) * β ^ 2) ≤ δ / (4 * (h : ℝ) * β ^ 2) := by
        exact div_le_div_of_nonneg_right hAhi (by positivity)
      _ ≤ δ / (4 * (h : ℝ) * (δ / 16) ^ 2) := by
        apply div_le_div_of_nonneg_left hδ.le (by positivity)
        gcongr
      _ = 64 / ((h : ℝ) * δ) := by field_simp; ring
      _ ≤ δ / 8 := hleak
  have hbudget : δ / 2 ≤ A - A * ((h : ℝ) - 1) * δ ^ 3 -
      A / (4 * (h : ℝ) * β ^ 2) :=
    fejer_localization_budget δ _ A _ _ hδ.le hAlo hE hL le_rfl
  have hcount := initial_interval_count_of_kernel_mean samples x (δ ^ 3)
    hh hdegree hd hdq hmean
  have hsubset : samples.filter (fun ω => (x ω).val < 8 * d) ⊆
      samples.filter (fun ω => ((x ω).val : ℝ) < δ * q) := by
    intro ω hω
    obtain ⟨hω, hval⟩ := Finset.mem_filter.mp hω
    refine Finset.mem_filter.mpr ⟨hω, ?_⟩
    have hv : ((x ω).val : ℝ) < (8 * d : ℕ) := by exact_mod_cast hval
    exact hv.trans_le hdouter
  calc
    (δ / 2) * (samples.card : ℝ) ≤ (samples.card : ℝ) *
        (A - A * ((h : ℝ) - 1) * δ ^ 3 - A / (4 * (h : ℝ) * β ^ 2)) := by
      simpa only [mul_comm (δ / 2)] using
        mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg samples.card)
    _ ≤ ((samples.filter (fun ω => (x ω).val < 8 * d)).card : ℝ) := hcount
    _ ≤ ((samples.filter (fun ω => ((x ω).val : ℝ) < δ * q)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset

/-- Genuine finite cyclic low-frequency discrepancy, with no sampled-kernel
hypothesis remaining. Repeated samples are allowed. -/
theorem cyclic_small_interval_of_fourier {q : ℕ} [NeZero q]
    {Ω : Type*} [Fintype Ω] (x : Ω → ZMod q) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536) (hscale : 128 ≤ δ * q)
    (hdegree : ⌊1 / (64 * δ ^ 3)⌋₊ ≤ q)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖∑ ω : Ω, ZMod.stdAddChar ((l : ZMod q) * x ω)‖ ≤
        (Fintype.card Ω : ℝ) * δ ^ 3) :
    (δ / 2) * (Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter (fun ω => ((x ω).val : ℝ) < δ * q)).card : ℝ) := by
  classical
  cases isEmpty_or_nonempty Ω with
  | inl h =>
    let := h
    simp
  | inr h =>
    let := h
    have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
    have hh : 0 < ⌊1 / (64 * δ ^ 3)⌋₊ := by
      have hb := (fejer_degree_floor_budget δ hδ hsmall).1
      omega
    have hfreq := fejer_degree_frequency_bound δ hδ hsmall
    apply cyclic_small_interval_of_kernel_mean Finset.univ x δ hδ hsmall hscale hdegree
    intro y
    have hm := FejerSampleMean.fejer_sample_mean_lower hh x y (δ ^ 3)
      (fun l hl hlh => hfourier l hl (by omega))
    have hm' := (le_div_iff₀ hN).mp hm
    simpa only [Finset.card_univ, mul_comm] using hm'

end Problem337.CyclicSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FourierFrequencyGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Nontrivial cancellation at all prescribed low frequencies forces the
modulus itself to lie beyond that range. -/
theorem modulus_gt_low_frequency_range {q : ℕ} [NeZero q]
    {ι : Type*} (I : Finset ι) (hI : I.Nonempty) (x : ι → ZMod q)
    (H : ℕ) (ε : ℝ) (hε : ε < 1)
    (hfourier : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ H →
      ‖(∑ i ∈ I, ZMod.stdAddChar ((ℓ : ZMod q) * x i)) / (I.card : ℂ)‖ ≤ ε) :
    H < q := by
  by_contra h
  have hqH : q ≤ H := by omega
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have h := hfourier q hq1 hqH
  have hcard : I.card ≠ 0 := ne_of_gt (Finset.card_pos.mpr hI)
  have hcardC : (I.card : ℂ) ≠ 0 := by exact_mod_cast hcard
  simp only [ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one,
    Finset.sum_const, nsmul_eq_mul, mul_one, div_self hcardC, norm_one] at h
  linarith

/-- The frequency range needed for localization also guarantees that the
cyclic interval contains many integer representatives. -/
theorem low_frequency_gap_scale (δ : ℝ) (q : ℕ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536)
    (hgap : ⌊1 / δ ^ 4⌋₊ < q) : 128 ≤ δ * q := by
  have hq : 1 / δ ^ 4 < (q : ℝ) := (Nat.floor_lt (by positivity)).mp hgap
  have hδ8 : δ ≤ (1 / 8 : ℝ) := by linarith
  have hcube : δ ^ 3 ≤ (1 / 8 : ℝ) ^ 3 := by gcongr
  have hbound : (128 : ℝ) ≤ δ * (1 / δ ^ 4) := by
    have heq : δ * (1 / δ ^ 4) = 1 / δ ^ 3 := by
      field_simp
    rw [heq]
    apply (le_div_iff₀ (by positivity : 0 < δ ^ 3)).mpr
    norm_num at hcube
    linarith
  exact hbound.trans (mul_le_mul_of_nonneg_left hq.le hδ.le)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CyclicDiscrepancyAutomatic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.CyclicSmoothing

/-- Low-frequency cancellation itself supplies both numerical modulus
conditions needed for the cyclic localization argument. -/
theorem cyclic_small_interval_of_fourier_automatic {q : ℕ} [NeZero q]
    {Ω : Type*} [Fintype Ω] (x : Ω → ZMod q) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖∑ ω : Ω, ZMod.stdAddChar ((l : ZMod q) * x ω)‖ ≤
        (Fintype.card Ω : ℝ) * δ ^ 3) :
    (δ / 2) * (Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter (fun ω => ((x ω).val : ℝ) < δ * q)).card : ℝ) := by
  classical
  cases isEmpty_or_nonempty Ω with
  | inl h =>
    let := h
    simp
  | inr h =>
    let := h
    have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
    have hε : δ ^ 3 < 1 := by
      have hδ1 : δ < 1 := by linarith
      exact pow_lt_one₀ hδ.le hδ1 (by decide)
    have hgap : ⌊1 / δ ^ 4⌋₊ < q :=
      modulus_gt_low_frequency_range Finset.univ Finset.univ_nonempty x _ _ hε
        (fun l hl hH => by
          simp only [Finset.card_univ, norm_div, Complex.norm_natCast]
          exact (div_le_iff₀ hN).mpr (by simpa [mul_comm] using hfourier l hl hH))
    have hscale := low_frequency_gap_scale δ q hδ hsmall hgap
    have hdegree : ⌊1 / (64 * δ ^ 3)⌋₊ ≤ q :=
      (fejer_degree_frequency_bound δ hδ hsmall).trans (Nat.le_of_lt hgap)
    exact cyclic_small_interval_of_fourier x δ hδ hsmall hscale hdegree hfourier

end Problem337.CyclicSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_LeastResidueBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- The integer remainder in the ceiling descent is exactly the canonical
representative of the negative residue, including remainder zero. -/
theorem least_remainder_eq_neg_cast_val {u A z : ℕ} [NeZero u]
    (hlo : A ≤ u * z) (hhi : u * z < A + u) :
    u * z - A = (-(A : ZMod u)).val := by
  have hr : u * z - A < u := by omega
  have hc : ((u * z - A : ℕ) : ZMod u) = -(A : ZMod u) := by
    rw [Nat.cast_sub hlo, Nat.cast_mul]
    simp
  have hv := congrArg ZMod.val hc
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hr] using hv

/-- Natural rational ceiling supplies the exact least-residue integer. -/
theorem ceiling_remainder_eq_neg_cast_val {u A : ℕ} [NeZero u] :
    u * ⌈(A : ℚ) / (u : ℚ)⌉₊ - A = (-(A : ZMod u)).val := by
  have hu : (0 : ℚ) < u := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne u)
  let z : ℕ := ⌈(A : ℚ) / (u : ℚ)⌉₊
  have hloQ : (A : ℚ) ≤ (u : ℚ) * z := by
    have h := (div_le_iff₀ hu).mp (Nat.le_ceil ((A : ℚ) / (u : ℚ)))
    simpa only [mul_comm] using h
  have hhiQ : (u : ℚ) * z < (A : ℚ) + u := by
    have h := mul_lt_mul_of_pos_right
      (Nat.ceil_lt_add_one (by positivity : (0 : ℚ) ≤ (A : ℚ) / (u : ℚ))) hu
    dsimp [z]
    rw [add_mul, div_mul_cancel₀ _ hu.ne', one_mul] at h
    simpa only [mul_comm] using h
  exact least_remainder_eq_neg_cast_val (by exact_mod_cast hloQ) (by exact_mod_cast hhiQ)

/-- Standard additive characters at natural residues are the usual
exponential phases without choosing a representative. -/
theorem stdAddChar_nat_phase {u : ℕ} [NeZero u] (A : ℕ) :
    ZMod.stdAddChar (A : ZMod u) =
      Complex.exp (2 * Real.pi * Complex.I * (A : ℂ) / (u : ℂ)) := by
  simpa only [Int.cast_natCast] using (ZMod.stdAddChar_coe (N := u) (A : ℤ))

/-- In particular, the positive Fourier coefficient for natural products is
exactly the exponential sum in the residue estimates. -/
theorem stdAddChar_nat_product_phase {u : ℕ} [NeZero u] (l A : ℕ) :
    ZMod.stdAddChar ((l : ZMod u) * (A : ZMod u)) =
      Complex.exp (2 * Real.pi * Complex.I * (l * A : ℕ) / (u : ℂ)) := by
  rw [← Nat.cast_mul, stdAddChar_nat_phase]

/-- Passing from positive exponential phases to the negative least-residue
phases preserves every Fourier coefficient norm. -/
theorem norm_neg_residue_fourier_eq {u : ℕ} [NeZero u]
    {I : Type*} [Fintype I] (A : I → ℕ) (l : ℕ) :
    ‖∑ t : I, ZMod.stdAddChar ((l : ZMod u) * (-(A t : ZMod u)))‖ =
      ‖∑ t : I, Complex.exp
        (2 * Real.pi * Complex.I * (l * A t : ℕ) / (u : ℂ))‖ := by
  simp_rw [mul_neg, AddChar.map_neg_eq_conj]
  rw [← map_sum (starRingEnd ℂ)
    (fun t : I => ZMod.stdAddChar ((l : ZMod u) * (A t : ZMod u))) Finset.univ]
  rw [Complex.norm_conj]
  simp_rw [stdAddChar_nat_product_phase]

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CyclicCeilingCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Cancellation forces its own modulus-size conditions, so the direct
ceiling-remainder count has no separate scale or degree hypothesis. -/
theorem ceiling_remainder_count_of_character_expect_automatic {u : ℕ} [NeZero u]
    {Ω : Type*} [Fintype Ω] (A : Ω → ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖𝔼 ω : Ω, ZMod.stdAddChar ((l : ZMod u) * (A ω : ZMod u))‖ ≤ δ ^ 3) :
    (δ / 2) * (Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter (fun ω =>
        ((u * ⌈(A ω : ℚ) / (u : ℚ)⌉₊ - A ω : ℕ) : ℝ) < δ * u)).card : ℝ) := by
  classical
  cases isEmpty_or_nonempty Ω with
  | inl h =>
    let := h
    simp
  | inr h =>
    let := h
    have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
    have hc := CyclicSmoothing.cyclic_small_interval_of_fourier_automatic
      (fun ω => -(A ω : ZMod u)) δ hδ hsmall
      (fun l hl hld => by
        rw [norm_neg_residue_fourier_eq]
        have hf := hfourier l hl hld
        simp only [Fintype.expect_eq_sum_div_card, stdAddChar_nat_product_phase,
          norm_div, Complex.norm_natCast] at hf
        simpa only [mul_comm] using (div_le_iff₀ hN).mp hf)
    simpa only [ceiling_remainder_eq_neg_cast_val] using hc

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrefixGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- The reduced denominator of a finite rational sum divides the product of
its summands' reduced denominators. -/
theorem sum_den_dvd_prod {α : Type*} [DecidableEq α]
    (s : Finset α) (q : α → ℚ) :
    (∑ j ∈ s, q j).den ∣ ∏ j ∈ s, (q j).den := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (Rat.add_den_dvd _ _).trans (Nat.mul_dvd_mul_left _ ih)

/-- A positive rational with denominator dividing `P` is at least `1/P`. -/
theorem one_div_le_of_den_dvd {q : ℚ} {P : ℕ}
    (hq : 0 < q) (hP : 0 < P) (hd : q.den ∣ P) :
    (1 : ℚ) / P ≤ q := by
  have hden : q.den ≤ P := Nat.le_of_dvd hP hd
  have hnum : (1 : ℚ) ≤ q.num := by
    exact_mod_cast (Rat.num_pos.mpr hq)
  calc
    (1 : ℚ) / P ≤ 1 / q.den := by
      exact one_div_le_one_div_of_le (by exact_mod_cast q.den_pos) (by exact_mod_cast hden)
    _ ≤ (q.num : ℚ) / q.den :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = q := Rat.num_div_den q

/-- The remainder after subtracting finitely many positive unit fractions
from one has a gap of at least the reciprocal of the denominator product. -/
theorem prefix_remainder_gap {α : Type*} [DecidableEq α]
    (s : Finset α) (n : α → ℕ)
    (hn : ∀ j ∈ s, 0 < n j)
    (hrem : 0 < 1 - ∑ j ∈ s, (1 : ℚ) / (n j : ℚ)) :
    (1 : ℚ) / (∏ j ∈ s, n j : ℕ) ≤
      1 - ∑ j ∈ s, (1 : ℚ) / (n j : ℚ) := by
  apply one_div_le_of_den_dvd hrem
  · exact Finset.prod_pos hn
  · have hd := sum_den_dvd_prod s (fun j => (1 : ℚ) / (n j : ℚ))
    have heq : (∏ j ∈ s, ((1 : ℚ) / (n j : ℚ)).den) = ∏ j ∈ s, n j := by
      apply Finset.prod_congr rfl
      intro j hj
      simpa only [one_div] using Rat.inv_natCast_den_of_pos (hn j hj)
    simpa only [Rat.ofNat_sub_den, heq] using hd

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrefixGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace Problem337

/-- The elementary growth estimate for successive products of denominators. -/
theorem prefix_growth_bound (k t : ℕ) (P : ℕ → ℕ)
    (hzero : P 0 = 1)
    (hstep : ∀ i < t, P (i + 1) ≤ k * (P i) ^ 2) :
    ∀ i ≤ t, P i ≤ k ^ (2 ^ i - 1) := by
  intro i hi
  induction i with
  | zero => simp [hzero]
  | succ i ih =>
    have hit : i < t := by omega
    have hip := ih (by omega)
    have hpow : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by omega)
    have hexp : 1 + (2 ^ i - 1) * 2 = 2 ^ (i + 1) - 1 := by
      rw [pow_succ]
      omega
    calc
      P (i + 1) ≤ k * (P i) ^ 2 := hstep i hit
      _ ≤ k * (k ^ (2 ^ i - 1)) ^ 2 := Nat.mul_le_mul_left k (Nat.pow_le_pow_left hip 2)
      _ = k ^ (2 ^ (i + 1) - 1) := by
        rw [← pow_mul, ← pow_succ']
        congr 1
        omega

/-- The bound for the next denominator follows from the prefix-product bound. -/
theorem denominator_growth_bound (k i P n : ℕ)
    (hP : P ≤ k ^ (2 ^ i - 1)) (hn : n ≤ k * P) :
    n ≤ k ^ (2 ^ i) := by
  have hpow : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by omega)
  calc
    n ≤ k * P := hn
    _ ≤ k * k ^ (2 ^ i - 1) := Nat.mul_le_mul_left k hP
    _ = k ^ (2 ^ i) := by
      rw [← pow_succ']
      congr 1
      omega

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DenominatorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

 theorem ordered_unit_tail_bound {k : ℕ} (n : Fin k → ℕ)
    (hn : ∀ i, 0 < n i) (hmono : Monotone n)
    (hsum : (∑ j : Fin k, (1 : ℚ) / n j) = 1) (i : Fin k) :
    0 < 1 - ∑ j ∈ Finset.univ.filter (· < i), (1 : ℚ) / n j ∧
    1 - ∑ j ∈ Finset.univ.filter (· < i), (1 : ℚ) / n j ≤
      (k : ℚ) / n i := by
  let s : Finset (Fin k) := Finset.univ.filter (· < i)
  let t : Finset (Fin k) := Finset.univ.filter (i ≤ ·)
  have hsplit : (∑ j ∈ s, (1 : ℚ) / n j) + (∑ j ∈ t, (1 : ℚ) / n j) = 1 := by
    calc
      _ = ∑ j : Fin k, (1 : ℚ) / n j := by
        simpa [s, t, not_lt] using
          (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin k)))
            (p := fun j => j < i) (f := fun j => (1 : ℚ) / n j))
      _ = 1 := hsum
  have hrem : 1 - ∑ j ∈ s, (1 : ℚ) / n j = ∑ j ∈ t, (1 : ℚ) / n j := by
    linarith
  change 0 < 1 - ∑ j ∈ s, (1 : ℚ) / n j ∧ _
  rw [hrem]
  constructor
  · apply lt_of_lt_of_le (show 0 < (1 : ℚ) / n i from div_pos zero_lt_one (by exact_mod_cast hn i))
    apply Finset.single_le_sum (f := fun j => (1 : ℚ) / n j) (a := i)
    · intro j hj
      positivity
    · simp [t]
  · calc
      ∑ j ∈ t, (1 : ℚ) / n j ≤ ∑ _j ∈ t, (1 : ℚ) / n i := by
        apply Finset.sum_le_sum
        intro j hj
        apply one_div_le_one_div_of_le
        · exact_mod_cast hn i
        · exact_mod_cast hmono (by simpa [t] using hj)
      _ = (t.card : ℚ) / n i := by simp [div_eq_mul_inv]
      _ ≤ (k : ℚ) / n i := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast (show t.card ≤ k from (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ.trans (Fintype.card_fin k)))
        · positivity

 theorem denominator_le_prefix_product {k : ℕ} (n : Fin k → ℕ)
    (hn : ∀ i, 0 < n i) (hmono : Monotone n)
    (hsum : (∑ j : Fin k, (1 : ℚ) / n j) = 1) (i : Fin k)
    (hgap : (1 : ℚ) / (∏ j ∈ Finset.univ.filter (· < i), n j : ℕ) ≤
      1 - ∑ j ∈ Finset.univ.filter (· < i), (1 : ℚ) / n j) :
    n i ≤ k * ∏ j ∈ Finset.univ.filter (· < i), n j := by
  have hle := hgap.trans (ordered_unit_tail_bound n hn hmono hsum i).2
  have hp : (0 : ℚ) < (∏ j ∈ Finset.univ.filter (· < i), n j : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun j _ => hn j)
  have hi : (0 : ℚ) < n i := by exact_mod_cast hn i
  have hcross := (div_le_div_iff₀ hp hi).mp hle
  norm_num only [one_mul] at hcross
  exact_mod_cast hcross

/-- The coordinate estimate only needs weak ordering, so it also applies to
expansions with repeated denominators. -/
theorem ordered_unit_denominator_bound {k : ℕ} (n : Fin k → ℕ)
    (hn : ∀ i, 0 < n i) (hmono : Monotone n)
    (hsum : (∑ j : Fin k, (1 : ℚ) / n j) = 1) :
    ∀ i : Fin k, n i ≤ k ^ (2 ^ i.val) := by
  let P : ℕ → ℕ := fun t => ∏ j ∈ Finset.univ.filter (fun j : Fin k => j.val < t), n j
  have hrec : ∀ i : Fin k, n i ≤ k * P i.val := by
    intro i
    apply denominator_le_prefix_product n hn hmono hsum i
    exact prefix_remainder_gap _ n (fun j _ => hn j)
      (ordered_unit_tail_bound n hn hmono hsum i).1
  have hzero : P 0 = 1 := by simp [P]
  have hstep : ∀ t < k, P (t + 1) ≤ k * (P t) ^ 2 := by
    intro t ht
    let i : Fin k := ⟨t, ht⟩
    have hs : Finset.univ.filter (fun j : Fin k => j.val < t + 1) =
        insert i (Finset.univ.filter (fun j : Fin k => j.val < t)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hj
        by_cases hji : j = i
        · exact Or.inl hji
        · right
          have hne : j.val ≠ t := by
            intro he
            apply hji
            apply Fin.ext
            exact he
          omega
      · rintro (rfl | hj)
        · exact Nat.lt_succ_self t
        · omega
    have hnot : i ∉ Finset.univ.filter (fun j : Fin k => j.val < t) := by
      simp [i]
    have heq : P (t + 1) = n i * P t := by
      simp only [P, hs, Finset.prod_insert hnot]
    calc
      P (t + 1) = n i * P t := heq
      _ ≤ (k * P t) * P t := Nat.mul_le_mul_right (P t) (hrec i)
      _ = k * (P t) ^ 2 := by ring
  intro i
  exact denominator_growth_bound k i.val (P i.val) (n i)
    (prefix_growth_bound k k P hzero hstep i.val i.isLt.le) (hrec i)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DescentHolder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- A convenient exponential envelope for the coefficient in the normalized
recurrence, once the moment parameter is at least two. -/
theorem descent_coefficient_bound
    (E r : ℝ) (hE : 2 ≤ E) (hr : 1 ≤ r) :
    1 + 2 * Real.exp (E / r) ≤ Real.exp (2 * E) := by
  have hE0 : 0 ≤ E := by linarith
  have hsmall : Real.exp (E / r) ≤ Real.exp E :=
    Real.exp_le_exp.mpr (div_le_self hE0 hr)
  have hlarge : 3 ≤ Real.exp E := by
    have h := Real.add_one_le_exp E
    linarith
  have hproduct : 0 ≤ (Real.exp E - 3) * (Real.exp E + 1) :=
    mul_nonneg (by linarith) (by positivity)
  rw [show 2 * E = E + E by ring, Real.exp_add]
  nlinarith

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ResidueLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open Filter

namespace Problem337.ResidueLevels

theorem depth_upper {A m η : ℝ} (hm : 0 < m) (hη : 0 < η)
    (hA : m ≤ A) :
    (depth A m η : ℝ) < A / (η * m) + 1 := by
  have hp : 0 < η * m := mul_pos hη hm
  have hx : 0 ≤ (A - m) / (η * m) := div_nonneg (sub_nonneg.mpr hA) hp.le
  have hu := Nat.ceil_lt_add_one hx
  change (depth A m η : ℝ) < (A - m) / (η * m) + 1 at hu
  have hle : (A - m) / (η * m) ≤ A / (η * m) :=
    div_le_div_of_nonneg_right (by linarith) hp.le
  linarith

theorem depth_log_bound {S D m η : ℝ} (_hS : 0 < S) (hlog : 1 ≤ Real.log S)
    (hD : 1 ≤ D) (hm : 0 < m) (hη : 0 < η) (hηone : η ≤ 1)
    (hmlo : S / (2 * Real.log S) ≤ m) (hmhi : m ≤ D * S) :
    (depth (D * S) m η : ℝ) ≤ (3 * D / η) * Real.log S := by
  have hp : 0 < η * m := mul_pos hη hm
  have hlogpos : 0 < Real.log S := by linarith
  have hmlo' : S ≤ m * (2 * Real.log S) :=
    (div_le_iff₀ (by positivity : 0 < 2 * Real.log S)).1 hmlo
  have hratio : D * S / (η * m) ≤ (2 * D / η) * Real.log S := by
    apply (div_le_iff₀ hp).2
    have hmul := mul_le_mul_of_nonneg_left hmlo' (show 0 ≤ D by linarith)
    have heq : (2 * D / η) * Real.log S * (η * m) = D * (m * (2 * Real.log S)) := by
      field_simp
    rw [heq]
    exact hmul
  have hDone : 1 ≤ D / η := (le_div_iff₀ hη).2 (by linarith)
  have hbudget : 1 ≤ (D / η) * Real.log S := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hDone) (sub_nonneg.mpr hlog)]
  have hu := depth_upper hm hη hmhi
  have heq : (3 * D / η) * Real.log S =
      (2 * D / η) * Real.log S + (D / η) * Real.log S := by ring
  rw [heq]
  linarith

theorem tendsto_div_log : Tendsto (fun S : ℝ => S / Real.log S) atTop atTop := by
  have ht : Tendsto (fun S : ℝ => Real.log S / S) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  apply tendsto_atTop.2
  intro b
  let c : ℝ := max b 1
  have hc : 0 < c := by dsimp [c]; positivity
  filter_upwards [ht.eventually (gt_mem_nhds (one_div_pos.mpr hc)),
    eventually_gt_atTop (1 : ℝ)] with S hratio hS
  have hSp : 0 < S := by linarith
  have hlogp : 0 < Real.log S := Real.log_pos hS
  have hprod := (div_lt_div_iff₀ hSp hc).1 hratio
  have hlt : c < S / Real.log S := (lt_div_iff₀ hlogp).2 (by nlinarith)
  exact (le_max_left b 1).trans hlt.le

theorem scale_bounds {S : ℝ} (hS : 0 < S) (hlog : 0 < Real.log S)
    (hratio : 2 ≤ S / Real.log S) :
    S / (2 * Real.log S) ≤ (scale S : ℝ) ∧
      (scale S : ℝ) ≤ S / Real.log S := by
  have hx : 0 ≤ S / Real.log S := div_nonneg hS.le hlog.le
  have hfloor := Nat.lt_floor_add_one (S / Real.log S)
  have hle := Nat.floor_le hx
  change S / Real.log S < (scale S : ℝ) + 1 at hfloor
  change (scale S : ℝ) ≤ S / Real.log S at hle
  have heq : S / (2 * Real.log S) = (S / Real.log S) / 2 := by ring
  refine ⟨?_, hle⟩
  rw [heq]
  linarith

theorem eventually_scale_bounds : ∀ᶠ S : ℝ in atTop,
    1 ≤ Real.log S ∧ 2 ≤ scale S ∧
    S / (2 * Real.log S) ≤ (scale S : ℝ) ∧
    (scale S : ℝ) ≤ S / Real.log S := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_div_log.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with S hlog hratio hS
  refine ⟨hlog, Nat.le_floor hratio, ?_⟩
  exact scale_bounds (by linarith) (by linarith) hratio

theorem factor_zero {D S m η : ℝ} (hD : 1 < D) (hS : 0 < S) (C : ℕ) :
    factor (D * S) m η S C 0 = C := by
  have hlog : S < D * S := by nlinarith
  simp only [factor, level_zero, Real.exp_lt_exp.mpr hlog, ↓reduceIte]

end Problem337.ResidueLevels

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DeterministicMeanDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter

namespace Problem337.ResidueLevels

/-- The exponential absorption used in the deterministic second moment is
uniform in every real prime-product scale in the standard interval. -/
theorem eventually_exp_absorb_real_scale {a b c C : ℝ}
    (hab : a < b) (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ S : ℝ in atTop, ∀ m : ℝ,
      S / (2 * Real.log S) ≤ m → m ≤ S / Real.log S →
      Real.exp (-b * m) + C * Real.exp (-c * S) ≤ Real.exp (-a * m) := by
  have ht : Tendsto (fun S : ℝ => S / (2 * Real.log S)) atTop atTop := by
    convert tendsto_div_log.atTop_div_const (by norm_num : (0 : ℝ) < 2) using 1
    all_goals try with_reducible_and_instances rfl
    funext S
    ring
  have ht₁ : Tendsto
      (fun S : ℝ => Real.exp (-((b - a) * (S / (2 * Real.log S)))))
      atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (ht.const_mul_atTop (sub_pos.mpr hab))
  have ht₂ : Tendsto
      (fun S : ℝ => C * Real.exp (-(S / (2 * Real.log S))))
      atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul C
  have hsmall : ∀ᶠ S : ℝ in atTop,
      Real.exp (-((b - a) * (S / (2 * Real.log S)))) +
        C * Real.exp (-(S / (2 * Real.log S))) ≤ 1 := by
    apply Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1)
    simpa using ht₁.add ht₂
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop ((a + 1) / c))] with S hs hS hlog
  intro m hmlo hmhi
  have hSp : 0 < S := by linarith
  have hlogp : 0 < Real.log S := Real.log_pos hS
  have hmp : 0 < m := (div_pos hSp (by positivity)).trans_le hmlo
  have hlogm : Real.log S * m ≤ S := by
    have hh := (le_div_iff₀ hlogp).1 hmhi
    nlinarith
  have hcm : (a + 1) * m ≤ c * S := by
    have hh := (div_le_iff₀ hc).1 hlog
    nlinarith [mul_le_mul_of_nonneg_right hh hmp.le,
      mul_le_mul_of_nonneg_left hlogm hc.le]
  have hsmallm : Real.exp (-((b - a) * m)) + C * Real.exp (-m) ≤ 1 := by
    apply le_trans _ hs
    apply add_le_add
    · apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hmlo (sub_pos.mpr hab).le]
    · apply mul_le_mul_of_nonneg_left _ hC
      exact Real.exp_le_exp.mpr (neg_le_neg hmlo)
  have hexp : Real.exp (-c * S) ≤ Real.exp (-(a + 1) * m) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc
    Real.exp (-b * m) + C * Real.exp (-c * S) ≤
        Real.exp (-b * m) + C * Real.exp (-(a + 1) * m) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hexp hC)
    _ = Real.exp (-a * m) *
        (Real.exp (-((b - a) * m)) + C * Real.exp (-m)) := by
      rw [mul_add, ← Real.exp_add]
      have heq : -a * m + -((b - a) * m) = -b * m := by ring
      rw [heq]
      congr 1
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-a * m) := by
      simpa using mul_le_mul_of_nonneg_left hsmallm (Real.exp_pos _).le

end Problem337.ResidueLevels

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SimultaneousSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- A finite Markov inequality with a union over frequencies. No independence
between the frequencies, or between the points, is required. -/
theorem card_exists_large_score_mul_le {α β : Type*}
    (U : Finset α) (L : Finset β) (g : α → β → ℝ) (a : ℝ)
    (hg : ∀ u ∈ U, ∀ l ∈ L, 0 ≤ g u l) :
    ((U.filter (fun u => ∃ l ∈ L, a < g u l)).card : ℝ) * a ≤
      ∑ l ∈ L, ∑ u ∈ U, g u l := by
  classical
  let bad := U.filter (fun u => ∃ l ∈ L, a < g u l)
  calc
    (bad.card : ℝ) * a = ∑ _u ∈ bad, a := by simp
    _ ≤ ∑ u ∈ bad, ∑ l ∈ L, g u l := by
      apply Finset.sum_le_sum
      intro u hu
      obtain ⟨huU, l, hl, hlarge⟩ := Finset.mem_filter.mp hu
      exact hlarge.le.trans (Finset.single_le_sum (hg u huU) hl)
    _ ≤ ∑ u ∈ U, ∑ l ∈ L, g u l := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro u hu _
      exact Finset.sum_nonneg (hg u hu)
    _ = ∑ l ∈ L, ∑ u ∈ U, g u l := Finset.sum_comm

/-- Squared complex Fourier scores are a common instance of the preceding
finite Markov/union estimate. -/
theorem card_exists_large_norm_sq_mul_le {α β : Type*}
    (U : Finset α) (L : Finset β) (f : α → β → ℂ) (a : ℝ) (ha : 0 ≤ a) :
    ((U.filter (fun u => ∃ l ∈ L, a < ‖f u l‖)).card : ℝ) * a ^ 2 ≤
      ∑ l ∈ L, ∑ u ∈ U, ‖f u l‖ ^ 2 := by
  classical
  have hfilter : U.filter (fun u => ∃ l ∈ L, a < ‖f u l‖) =
      U.filter (fun u => ∃ l ∈ L, a ^ 2 < ‖f u l‖ ^ 2) := by
    apply Finset.filter_congr
    intro u _
    apply exists_congr
    intro l
    exact and_congr_right (fun _ => by
      constructor
      · intro h
        nlinarith [norm_nonneg (f u l)]
      · intro h
        nlinarith [norm_nonneg (f u l)])
  rw [hfilter]
  apply card_exists_large_score_mul_le
  intros
  positivity

/-- The uniform second-moment version of the frequency-union bound. -/
theorem card_exists_large_norm_le_of_moments {α β : Type*}
    (U : Finset α) (L : Finset β) (f : α → β → ℂ) (a E : ℝ)
    (ha : 0 < a) (hE : ∀ l ∈ L, (∑ u ∈ U, ‖f u l‖ ^ 2) ≤ E) :
    ((U.filter (fun u => ∃ l ∈ L, a < ‖f u l‖)).card : ℝ) ≤
      (L.card : ℝ) * E / a ^ 2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos ha)).2
  calc
    ((U.filter (fun u => ∃ l ∈ L, a < ‖f u l‖)).card : ℝ) * a ^ 2 ≤
        ∑ l ∈ L, ∑ u ∈ U, ‖f u l‖ ^ 2 :=
      card_exists_large_norm_sq_mul_le U L f a ha.le
    _ ≤ ∑ _l ∈ L, E := Finset.sum_le_sum hE
    _ = (L.card : ℝ) * E := by simp

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_HighResidueDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- An automatic-scale version of the positive exponential-average ceiling
count. The index type, rather than the image, counts repeated entries. -/
theorem ceiling_remainder_count_of_exp_average {u : ℕ} [NeZero u]
    {Ω : Type*} [Fintype Ω] (A : Ω → ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖residueFourierAverage A u l‖ ≤ δ ^ 3) :
    (δ / 2) * (Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter (fun ω =>
        ((u * ⌈(A ω : ℚ) / (u : ℚ)⌉₊ - A ω : ℕ) : ℝ) < δ * u)).card : ℝ) := by
  apply ceiling_remainder_count_of_character_expect_automatic A δ hδ hsmall
  intro l hl hld
  simpa only [Fintype.expect_eq_sum_div_card, stdAddChar_nat_product_phase,
    residueFourierAverage] using hfourier l hl hld

/-- The exact frequency-union exponent is `-9m/1000`. This is stronger
than the `-m/1000` exception budget required by density descent. -/
theorem highResidueExceptions_card_bound {Ω : Type*} [Fintype Ω]
    (U : Finset ℕ) (A : Ω → ℕ) (m X : ℝ) (hX : 0 ≤ X)
    (hmoment : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊Real.exp (m / 2500)⌋₊ →
      (∑ u ∈ U, ‖residueFourierAverage A u l‖ ^ 2) ≤ X * Real.exp (-m / 100)) :
    ((highResidueExceptions U A m).card : ℝ) ≤ X * Real.exp (-9 * m / 1000) := by
  classical
  have hmarkov := card_exists_large_norm_le_of_moments U
    (Finset.Icc 1 ⌊Real.exp (m / 2500)⌋₊) (residueFourierAverage A)
    (Real.exp (-3 * m / 10000)) (X * Real.exp (-m / 100))
    (Real.exp_pos _) (fun l hl => hmoment l (Finset.mem_Icc.mp hl).1
      (Finset.mem_Icc.mp hl).2)
  have hcard : ((Finset.Icc 1 ⌊Real.exp (m / 2500)⌋₊).card : ℝ) ≤
      Real.exp (m / 2500) := by
    simpa using Nat.floor_le (Real.exp_pos (m / 2500)).le
  calc
    ((highResidueExceptions U A m).card : ℝ) ≤
        ((Finset.Icc 1 ⌊Real.exp (m / 2500)⌋₊).card : ℝ) *
          (X * Real.exp (-m / 100)) / Real.exp (-3 * m / 10000) ^ 2 := by
      apply le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) hmarkov
      intro u hu
      simpa only [highResidueExceptions, Finset.mem_filter] using hu
    _ ≤ Real.exp (m / 2500) * (X * Real.exp (-m / 100)) /
        Real.exp (-3 * m / 10000) ^ 2 := by gcongr
    _ = X * Real.exp (-9 * m / 1000) := by
      have he : Real.exp (m / 2500) * Real.exp (-m / 100) /
          Real.exp (-3 * m / 10000) ^ 2 = Real.exp (-9 * m / 1000) := by
        rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_sub]
        congr 1
        ring
      calc
        _ = X * (Real.exp (m / 2500) * Real.exp (-m / 100) /
            Real.exp (-3 * m / 10000) ^ 2) := by ring
        _ = _ := by rw [he]

/-- Outside the explicit exception set, every frequency needed by the cyclic
localization theorem satisfies the correct cubed-density bound. -/
theorem highResidueExceptions_fourier {Ω : Type*} [Fintype Ω]
    (U : Finset ℕ) (A : Ω → ℕ) (m : ℝ) {u : ℕ}
    (hu : u ∈ U) (hgood : u ∉ highResidueExceptions U A m) :
    ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / Real.exp (-m / 10000) ^ 4⌋₊ →
      ‖residueFourierAverage A u l‖ ≤ Real.exp (-m / 10000) ^ 3 := by
  classical
  have hfreq : 1 / Real.exp (-m / 10000) ^ 4 = Real.exp (m / 2500) := by
    rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg]
    congr 1
    ring
  have hthreshold : Real.exp (-m / 10000) ^ 3 = Real.exp (-3 * m / 10000) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  intro l hl hld
  rw [hthreshold]
  apply le_of_not_gt
  intro hlarge
  apply hgood
  simp only [highResidueExceptions, Finset.mem_filter]
  exact ⟨hu, l, Finset.mem_Icc.mpr ⟨hl, by simpa [hfreq] using hld⟩, hlarge⟩

/-- The rational-ceiling convention in cyclic counts and the real-ceiling
convention in geometric descent specify exactly the same least residue. -/
theorem rational_ceiling_residue_lt_iff_fract_lt (u A : ℕ) (hu : 0 < u) (δ : ℝ) :
    ((u * ⌈(A : ℚ) / (u : ℚ)⌉₊ - A : ℕ) : ℝ) < δ * u ↔
      Int.fract (-(A : ℝ) / u) < δ := by
  let : NeZero u := ⟨Nat.ne_of_gt hu⟩
  rw [ceiling_remainder_eq_neg_cast_val,
    ← natural_ceil_residue_eq_neg_zmod_val u A hu]
  obtain ⟨_, heq, hlt⟩ := natural_ceil_residue_spec u A hu
  exact residue_lt_iff_fract_lt hlt heq δ

/-- The direct fractional-part count needed by geometric residue families. -/
theorem fractional_residue_count_of_exp_average {Ω : Type*} [Fintype Ω]
    (A : Ω → ℕ) (u : ℕ) (hu : 0 < u) (δ : ℝ)
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / 65536)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊1 / δ ^ 4⌋₊ →
      ‖residueFourierAverage A u l‖ ≤ δ ^ 3) :
    (δ / 2) * (Fintype.card Ω : ℝ) ≤
      ((Finset.univ.filter (fun ω => Int.fract (-(A ω : ℝ) / u) < δ)).card : ℝ) := by
  let : NeZero u := ⟨Nat.ne_of_gt hu⟩
  have hc := ceiling_remainder_count_of_exp_average A δ hδ hsmall hfourier
  simpa only [rational_ceiling_residue_lt_iff_fract_lt u _ hu δ] using hc

/-- High-level distribution in exactly the fractional-part convention used
by geometric raw-density packaging. The exceptional set is independent of
the chosen residue index, and multiplicities are retained. -/
theorem high_level_fractional_residues_of_second_moments
    {Ω : Type*} [Fintype Ω] (U : Finset ℕ) (A : Ω → ℕ) (m X : ℝ)
    (hm : 0 ≤ m) (hX : 0 ≤ X)
    (hsmall : Real.exp (-m / 10000) ≤ 1 / 65536)
    (hupos : ∀ u ∈ U, 0 < u)
    (hmoment : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊Real.exp (m / 2500)⌋₊ →
      (∑ u ∈ U, ‖residueFourierAverage A u l‖ ^ 2) ≤ X * Real.exp (-m / 100)) :
    ∃ E : Finset ℕ, E ⊆ U ∧ (E.card : ℝ) ≤ X * Real.exp (-m / 1000) ∧
      ∀ u ∈ U, u ∉ E →
        (Real.exp (-m / 10000) / 2) * (Fintype.card Ω : ℝ) ≤
          ((Finset.univ.filter (fun ω =>
            Int.fract (-(A ω : ℝ) / u) < Real.exp (-m / 10000))).card : ℝ) := by
  classical
  refine ⟨highResidueExceptions U A m, ?_, ?_, ?_⟩
  · intro u hu
    simp only [highResidueExceptions, Finset.mem_filter] at hu
    exact hu.1
  · exact (highResidueExceptions_card_bound U A m X hX hmoment).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hX)
  · intro u hu hgood
    exact fractional_residue_count_of_exp_average A u (hupos u hu)
      (Real.exp (-m / 10000)) (Real.exp_pos _) hsmall
      (highResidueExceptions_fourier U A m hu hgood)

/-- Finset-indexed form, matching the deterministic second-moment interface.
Repeated values of `A` remain distinct indices of `T`. -/
theorem high_level_fractional_residues_finset
    {ι : Type*} (T : Finset ι) (A : ι → ℕ) (U : Finset ℕ) (m X : ℝ)
    (hm : 0 ≤ m) (hX : 0 ≤ X)
    (hsmall : Real.exp (-m / 10000) ≤ 1 / 65536)
    (hupos : ∀ u ∈ U, 0 < u)
    (hmoment : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊Real.exp (m / 2500)⌋₊ →
      (∑ u ∈ U, ‖(∑ i ∈ T, Complex.exp
        (2 * Real.pi * Complex.I * (l * A i : ℕ) / (u : ℂ))) /
          (T.card : ℂ)‖ ^ 2) ≤ X * Real.exp (-m / 100)) :
    ∃ E : Finset ℕ, E ⊆ U ∧ (E.card : ℝ) ≤ X * Real.exp (-m / 1000) ∧
      ∀ u ∈ U, u ∉ E →
        (Real.exp (-m / 10000) / 2) * (T.card : ℝ) ≤
          ((T.filter (fun i =>
            Int.fract (-(A i : ℝ) / u) < Real.exp (-m / 10000))).card : ℝ) := by
  classical
  have he (u l : ℕ) : residueFourierAverage (fun i : T => A i) u l =
      (∑ i ∈ T, Complex.exp
        (2 * Real.pi * Complex.I * (l * A i : ℕ) / (u : ℂ))) /
          (T.card : ℂ) := by
    unfold residueFourierAverage
    rw [Finset.sum_coe_sort T (fun i => Complex.exp
      (2 * Real.pi * Complex.I * (l * A i : ℕ) / (u : ℂ))), Fintype.card_coe]
  obtain ⟨E, hEU, hEc, hE⟩ := high_level_fractional_residues_of_second_moments
    U (fun i : T => A i) m X hm hX hsmall hupos (by
      intro l hl hlH
      simpa only [he] using hmoment l hl hlH)
  refine ⟨E, hEU, hEc, ?_⟩
  intro u hu hgood
  have hcard : (Finset.univ.filter (fun i : T =>
      Int.fract (-(A i : ℝ) / u) < Real.exp (-m / 10000))).card =
      (T.filter (fun i => Int.fract (-(A i : ℝ) / u) < Real.exp (-m / 10000))).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Finset.sum_coe_sort T (fun i =>
      if Int.fract (-(A i : ℝ) / u) < Real.exp (-m / 10000) then 1 else 0)
  simpa only [Fintype.card_coe, hcard] using hE u hu hgood

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DeterministicResidueSupply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- Uniform positivity and localization cutoff for every admissible real
prime-product scale, not only the floor choice. -/
theorem eventually_high_residue_scale_window :
    ∀ᶠ S : ℝ in atTop, ∀ m : ℝ, S / (2 * Real.log S) ≤ m →
      0 ≤ m ∧ Real.exp (-m / 10000) ≤ 1 / 65536 := by
  have ht : Tendsto (fun S : ℝ => S / (2 * Real.log S)) atTop atTop := by
    convert ResidueLevels.tendsto_div_log.atTop_div_const
      (by norm_num : (0 : ℝ) < 2) using 1
    all_goals try with_reducible_and_instances rfl
    funext S
    ring
  have he : Tendsto
      (fun S : ℝ => Real.exp (-((S / (2 * Real.log S)) / 10000)))
      atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (ht.atTop_div_const (by norm_num))
  filter_upwards [ht.eventually (eventually_ge_atTop (0 : ℝ)),
    he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 65536))] with S hS hsmall
  intro m hm
  refine ⟨hS.trans hm, ?_⟩
  apply le_trans _ hsmall.le
  apply Real.exp_le_exp.mpr
  linarith

/-- The two phase conventions agree exactly, including zero modulus where
both divisions use their usual totalized field convention. -/
theorem natural_product_phase_eq_differencing (l C t u : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (l * (C * t) : ℕ) / (u : ℂ)) =
      differencingPhase ((l : ℝ) * C * t / (u : ℝ)) := by
  unfold differencingPhase
  congr 1
  push_cast
  ring

/-- Unconditional deterministic high-level small-residue distribution.
The only hypotheses concern the explicit scale, factor, size and distinctness
of the list. Reciprocal cancellation, frequency moments, Markov selection and
sharp localization are all discharged by the imported checked theorems. -/
theorem deterministic_high_residue_distribution (D : ℝ) (hD : 255 ≤ D) :
    ∀ᶠ S : ℝ in atTop, ∀ (m X : ℝ) (C : ℕ),
      S / (2 * Real.log S) ≤ m → m ≤ S / Real.log S →
      Real.exp S ≤ X → X ≤ Real.exp (D * S / 4) →
      Real.exp (D * S) ≤ (C : ℝ) → (C : ℝ) ≤ Real.exp (2 * D * S) →
      ∀ {ι : Type*} (T : Finset ι) (t : ι → ℕ),
        Set.InjOn t (T : Set ι) →
        Real.exp (Real.log 2 * m) ≤ (T.card : ℝ) →
        (∀ i ∈ T, (t i : ℝ) ≤ Real.exp (101 * S)) →
        ∃ E : Finset ℕ,
          E ⊆ Finset.Icc (⌊Real.exp (-m / 10000) * X⌋₊ + 1) ⌊X⌋₊ ∧
          (E.card : ℝ) ≤ X * Real.exp (-m / 1000) ∧
          ∀ u ∈ Finset.Icc (⌊Real.exp (-m / 10000) * X⌋₊ + 1) ⌊X⌋₊,
            u ∉ E →
            Real.exp (-m / 10000) * (T.card : ℝ) / 2 ≤
              ((T.filter (fun i => Int.fract (-((C * t i : ℕ) : ℝ) / u) <
                Real.exp (-m / 10000))).card : ℝ) := by
  obtain ⟨A, c, hA, hc, hmean⟩ := deterministic_mean_two_errors D hD
  have hlogtwo : (1 / 100 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  filter_upwards [hmean, ResidueLevels.eventually_exp_absorb_real_scale
      (a := 1 / 100) (b := Real.log 2) (c := c) (C := A) hlogtwo hc hA.le,
    eventually_high_residue_scale_window, eventually_ge_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
    with S hmean habs hscale hS hlog
  intro m X C hmlo hmhi hXlo hXhi hClo hChi ι T t ht hcard hsize
  have hX : 0 ≤ X := (Real.exp_pos S).le.trans hXlo
  have hmS : m ≤ S := by
    apply hmhi.trans
    apply (div_le_iff₀ (by linarith : 0 < Real.log S)).mpr
    nlinarith
  obtain ⟨hm, hsmall⟩ := hscale m hmlo
  have hbound := high_level_fractional_residues_finset T (fun i => C * t i)
    (Finset.Icc (⌊Real.exp (-m / 10000) * X⌋₊ + 1) ⌊X⌋₊) m X hm hX hsmall
    (by intro u hu; have := (Finset.mem_Icc.mp hu).1; omega) (by
      intro l hl hlH
      have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
      have hlup : (l : ℝ) ≤ Real.exp (m / 2500) :=
        (Nat.cast_le.mpr hlH).trans (Nat.floor_le (Real.exp_pos _).le)
      have hmoment := hmean m X C l hmS hXlo hXhi hClo hChi hlR hlup
        T t ht hcard hsize
      simp only [natural_product_phase_eq_differencing]
      apply hmoment.trans
      have ha := mul_le_mul_of_nonneg_left (habs m hmlo hmhi) hX
      simpa only [show -(1 / 100 : ℝ) * m = -m / 100 by ring] using ha)
  obtain ⟨E, hEU, hEc, hE⟩ := hbound
  refine ⟨E, hEU, hEc, ?_⟩
  intro u hu hgood
  simpa only [div_mul_eq_mul_div] using hE u hu hgood

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_EgyptianExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- Elementary greedy existence, stated independently of the shared definitions. -/
theorem exists_strict_unit_fraction_sum (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    ∃ k : ℕ, ∃ n : Fin k → ℕ,
      (∀ i, 2 ≤ n i) ∧ StrictMono n ∧
      (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = (a : ℚ) / (b : ℚ) := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    have ha0 : 0 < a := ha
    have hb0 : 0 < b := lt_trans ha0 hab
    have hdiv := Nat.div_add_mod b a
    have hmod := Nat.mod_lt b ha0
    by_cases hr : b % a = 0
    · have hq : 2 ≤ b / a := by
        by_contra h
        have hq' : b / a ≤ 1 := by omega
        have hmul : a * (b / a) ≤ a := by nlinarith
        omega
      refine ⟨1, fun _ => b / a, (fun _ => hq), ?_, ?_⟩
      · intro i j hij
        have hi := i.isLt
        have hj := j.isLt
        omega
      · simp only [Fin.sum_univ_one]
        have heq : a * (b / a) = b := by omega
        have hq0 : ((b / a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : b / a ≠ 0)
        have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
        have heq' : (a : ℚ) * (b / a : ℕ) = b := by exact_mod_cast heq
        apply (div_eq_div_iff hq0 hbq).2
        simpa [mul_comm] using heq'.symm
    · let d := b / a + 1
      let c := a - b % a
      have hd : 2 ≤ d := by
        have := Nat.div_pos (Nat.le_of_lt hab) ha0
        dsimp [d]
        omega
      have hd0 : 0 < d := by omega
      have hcpos : 1 ≤ c := by dsimp [c]; omega
      have hca : c < a := by dsimp [c]; omega
      have hcb : c < b * d := by nlinarith
      obtain ⟨k, n, hn, hmono, hsum⟩ := ih c hca (b * d) hcpos hcb
      have hbq : (0 : ℚ) < b := by exact_mod_cast hb0
      have hdq : (0 : ℚ) < d := by exact_mod_cast hd0
      have hdecomp : (1 : ℚ) / d + (c : ℚ) / (b * d : ℕ) = (a : ℚ) / b := by
        have hc : (c : ℚ) = a - (b % a : ℕ) := by
          dsimp [c]
          exact Nat.cast_sub (Nat.le_of_lt hmod)
        have hdivq : (a : ℚ) * (b / a : ℕ) + (b % a : ℕ) = b := by
          exact_mod_cast hdiv
        have hddef : (d : ℚ) = (b / a : ℕ) + 1 := by simp [d]
        push_cast
        field_simp
        nlinarith
      have hsmall : (c : ℚ) / (b * d : ℕ) < (1 : ℚ) / d := by
        have hcb' : (c : ℚ) < b := by exact_mod_cast (lt_trans hca hab)
        push_cast
        apply (div_lt_div_iff₀ (mul_pos hbq hdq) hdq).2
        nlinarith
      have hdn : ∀ i, d < n i := by
        intro i
        have hle : (1 : ℚ) / n i ≤ (c : ℚ) / (b * d : ℕ) := by
          rw [← hsum]
          exact Finset.single_le_sum (f := fun j : Fin k => (1 : ℚ) / n j) (fun j _ => by positivity) (Finset.mem_univ i)
        have hni : (0 : ℚ) < n i := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hn i))
        have := (one_div_lt_one_div hni hdq).1 (lt_of_le_of_lt hle hsmall)
        exact_mod_cast this
      refine ⟨k + 1, Fin.cons d n, ?_, ?_, ?_⟩
      · intro i
        exact Fin.cases hd (fun j => hn j) i
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => exact False.elim ((lt_irrefl _) hij)
          | succ j => simpa using hdn j
        | succ i =>
          cases j using Fin.cases with
          | zero => simp at hij
          | succ j => simpa using hmono (Fin.succ_lt_succ_iff.mp hij)
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hsum]
        exact hdecomp

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FiniteResidueIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- A pointwise assertion can be transported to the numeric indices. -/
theorem forall_residueEntry_iff {α β : Type*} [Fintype α] [Zero β]
    (f : α → β) (P : β → Prop) :
    (∀ i ∈ residueIndices α, P (residueEntry f i)) ↔ ∀ a, P (f a) := by
  constructor
  · intro h a
    simpa using h (Fintype.equivFin α a).val (by simp)
  · intro h i hi
    have hi' : i < Fintype.card α := mem_residueIndices.mp hi
    simpa [residueEntry, hi'] using h ((Fintype.equivFin α).symm ⟨i, hi'⟩)

/-- Full finite sums preserve sample multiplicity under the natural reindexing. -/
theorem sum_residueEntry {α β γ : Type*} [Fintype α] [Zero β]
    [AddCommMonoid γ] (f : α → β) (g : β → γ) :
    (∑ i ∈ residueIndices α, g (residueEntry f i)) = ∑ a, g (f a) := by
  rw [residueIndices, ← Fin.sum_univ_eq_sum_range]
  calc
    (∑ i : Fin (Fintype.card α), g (residueEntry f i.val)) =
        ∑ a : α, g (residueEntry f (Fintype.equivFin α a).val) :=
      (Equiv.sum_comp (Fintype.equivFin α) _).symm
    _ = ∑ a : α, g (f a) := by simp

/-- Filtering keeps repeated equal data as distinct samples. -/
theorem card_filter_residueEntry {α β : Type*} [Fintype α] [Zero β]
    (f : α → β) (P : β → Prop) [DecidablePred P] :
    ((residueIndices α).filter (fun i => P (residueEntry f i))).card =
      (Finset.univ.filter (fun a : α => P (f a))).card := by
  classical
  rw [Finset.card_filter, Finset.card_filter]
  exact sum_residueEntry f (fun x => if P x then 1 else 0)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_TerminalFiniteBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337.TerminalAssembly

theorem terminalCoefficient_pos {D α : ℝ}
    (hD : 1 ≤ D) (hα : 0 < α) (hα1 : α < 1) :
    0 < terminalCoefficient D α := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogα : 0 < -Real.log α := neg_pos.2 (Real.log_neg hα hα1)
  have hD0 : 0 < D := by linarith
  unfold terminalCoefficient
  positivity

/-- Rounding the terminal budget costs at most one extra logarithmic unit. -/
theorem ceiling_length_add_depth {B K S : ℝ} {d : ℕ}
    (hB : 0 ≤ B) (hlog : 1 ≤ Real.log S)
    (hd : (d : ℝ) ≤ K * Real.log S) :
    ((⌈B * Real.log S⌉₊ + d : ℕ) : ℝ) ≤ (B + K + 1) * Real.log S := by
  have hceil : (⌈B * Real.log S⌉₊ : ℝ) < B * Real.log S + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hB (by linarith))
  push_cast
  nlinarith

/-- The terminal tuple budget together with all backward levels remains
logarithmic, with one explicit coefficient independent of the cutoff. -/
theorem terminal_finite_total_budget {D α K S : ℝ} {d : ℕ}
    (hD : 1 ≤ D) (hα : 0 < α) (hα1 : α < 1)
    (hlogS : 1 ≤ Real.log S) (hd : (d : ℝ) ≤ K * Real.log S) :
    ((⌈terminalCoefficient D α * Real.log S⌉₊ + d : ℕ) : ℝ) ≤
      (terminalCoefficient D α + K + 1) * Real.log S :=
  ceiling_length_add_depth (terminalCoefficient_pos hD hα hα1).le hlogS hd

end Problem337.TerminalAssembly

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_GeometricRawDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open Filter
open scoped BigOperators

namespace Problem337

namespace GeometricDensity

/-- The concrete geometric construction meets the raw upper-bound interface.
Only the arithmetic input data, denominator size, and the displayed loss
estimate are assumed; the depth and rounded terminal length are proved. -/
theorem raw_density_supply_of_geometric_residues
    {DM D₀ η c r S loss : ℝ} {C M : ℕ}
    (H : ResidueData DM D₀ η c r S loss C M)
    (hDM : 1 < DM) (hD₀ : 1 ≤ D₀) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hS : 1 ≤ S) (hlog : 1 ≤ Real.log S) (hscale : 2 ≤ ResidueLevels.scale S)
    (hscale_lower : S / (2 * Real.log S) ≤ (ResidueLevels.scale S : ℝ))
    (hC : 0 < C) (hM : Real.exp S < (M : ℝ))
    (hMupper : (M : ℝ) ≤ Real.exp (DM * S))
    (hbinary : 2 ^ TerminalDepth.binaryExponent D₀ S ∣ M)
    (hloss : 0 < loss)
    (hloss_bound : 1 + loss * Real.exp (S ^ (1 / 4 : ℝ) / r) ≤
      Real.exp (2 * S ^ (1 / 4 : ℝ))) :
    RawDensitySupply DM
      (TerminalAssembly.terminalCoefficient D₀ (1 - η) + 3 * (DM + 2) / η + 1)
      c (3 * (DM + 2) / η) r S C := by
  have hSpos : 0 < S := by linarith
  have hm : (0 : ℝ) < ResidueLevels.scale S := by exact_mod_cast (by omega :
    0 < ResidueLevels.scale S)
  have hmS := ResidueLevels.scale_le_self hSpos.le hlog
  have hmA : (ResidueLevels.scale S : ℝ) ≤ (DM + 2) * S := by nlinarith
  have hηone : η ≤ 1 := by linarith
  have hd : (depth DM η S : ℝ) ≤ (3 * (DM + 2) / η) * Real.log S :=
    ResidueLevels.depth_log_bound hSpos hlog (by linarith) hm hη hηone
      hscale_lower hmA
  let F := H.toFamily hDM hD₀ hη hηhalf hS hlog hscale hC hM hbinary
    hloss hloss_bound
  refine ⟨ResidueLevels.scale S, contraction η S, depth DM η S, F,
    hscale_lower, hd, Real.exp_pos _, ?_, ?_, ?_, ?_, hM, hMupper⟩
  · apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hη.le) hm.le
  · exact TerminalAssembly.terminal_finite_total_budget hD₀
      (by linarith) (by linarith) hlog hd
  · exact ResidueLevels.level_zero _ _ _
  · exact ResidueLevels.factor_zero (by linarith) hSpos C

end GeometricDensity

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_LengthBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Existence is the only input needed to obtain a least expansion. -/
theorem egyptianLength_attained_of_exists {a b : ℕ}
    (h : ∃ k : ℕ, ∃ n : Fin k → ℕ,
      IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n) :
    ∃ n : Fin (egyptianLength a b) → ℕ,
      IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n := by
  exact Nat.sInf_mem h

/-- A pointwise length is bounded by the maximum over proper numerators. -/
theorem egyptianLength_le_max {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    egyptianLength a b ≤ maxEgyptianLength b := by
  unfold maxEgyptianLength
  simpa only [ite_eq_left ha] using
    (Finset.le_sup (f := fun a => if 1 ≤ a then egyptianLength a b else 0)
      (Finset.mem_range.mpr hab))

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MainLowerAppend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337
namespace MainLower

/-- Appending the remainder denominator and sorting reduces the lower-bound
argument to a coordinate bound for possibly repeated unit fractions. -/
theorem denominator_le_of_sum
    (hbound : ∀ s : ℕ, ∀ d : Fin s → ℕ,
      (∀ i, 1 ≤ d i) → Monotone d →
      (∑ i : Fin s, (1 : ℚ) / (d i : ℚ)) = 1 →
      ∀ i : Fin s, d i ≤ s ^ (2 ^ i.val))
    {b k : ℕ} (hb : 2 ≤ b) (n : Fin k → ℕ)
    (hn : ∀ i, 1 ≤ n i)
    (hsum : (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) =
      ((b - 1 : ℕ) : ℚ) / (b : ℚ)) :
    b ≤ (k + 1) ^ (2 ^ k) := by
  let d : Fin (k + 1) → ℕ := Fin.snoc n b
  let e := Tuple.sort d
  have hd : ∀ i, 1 ≤ d i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [d] using (show 1 ≤ b by omega)
    · simpa [d] using hn j
  have hdsum : (∑ i : Fin (k + 1), (1 : ℚ) / (d i : ℚ)) = 1 := by
    rw [Fin.sum_univ_castSucc]
    simp only [d, Fin.snoc_castSucc, Fin.snoc_last]
    rw [hsum]
    have hb0 : (b : ℚ) ≠ 0 := by positivity
    rw [Nat.cast_sub (show 1 ≤ b by omega)]
    push_cast
    field_simp
    ring
  have hsorted : (∑ i : Fin (k + 1), (1 : ℚ) / ((d ∘ e) i : ℚ)) = 1 := by
    calc
      _ = ∑ i : Fin (k + 1), (1 : ℚ) / (d i : ℚ) :=
        Equiv.sum_comp e (fun i => (1 : ℚ) / (d i : ℚ))
      _ = 1 := hdsum
  have hcoord := hbound (k + 1) (d ∘ e) (fun i => hd (e i))
    (Tuple.monotone_sort d) hsorted (e.symm (Fin.last k))
  have hpow : (k + 1) ^ (2 ^ (e.symm (Fin.last k)).val) ≤
      (k + 1) ^ (2 ^ k) := by
    apply Nat.pow_le_pow_right (by omega)
    apply Nat.pow_le_pow_right (by omega)
    exact Nat.le_of_lt_succ (e.symm (Fin.last k)).isLt
  have hbcoord : b ≤ (k + 1) ^ (2 ^ (e.symm (Fin.last k)).val) := by
    simpa [Function.comp_def, d] using hcoord
  exact hbcoord.trans hpow

/-- A convenient absolute constant for the elementary lower bound. -/
theorem log_log_le_twice {b k : ℕ} (hb : 2 ≤ b)
    (hbk : b ≤ (k + 1) ^ (2 ^ k)) :
    Real.log (Real.log (b : ℝ)) ≤ 2 * (k : ℝ) := by
  have hk : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    subst k
    norm_num at hbk
    omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) < (k : ℝ) + 1 := by linarith
  have hlog : 0 < Real.log ((k : ℝ) + 1) := Real.log_pos hk1
  have hbpos : (0 : ℝ) < b := by positivity
  have hp : (b : ℝ) ≤ ((k : ℝ) + 1) ^ (2 ^ k) := by exact_mod_cast hbk
  have hfirst := Real.log_le_log hbpos hp
  rw [Real.log_pow] at hfirst
  have hbLog : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
  have hsecond := Real.log_le_log hbLog hfirst
  rw [Real.log_mul (by positivity) (ne_of_gt hlog)] at hsecond
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by norm_cast
  rw [hcast, Real.log_pow] at hsecond
  have htwo : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have hsmall : Real.log ((k : ℝ) + 1) ≤ (k : ℝ) := by
    simpa using Real.log_le_sub_one_of_pos (show (0 : ℝ) < (k : ℝ) + 1 by positivity)
  have hsmall' : Real.log (Real.log ((k : ℝ) + 1)) ≤ (k : ℝ) := by
    calc
      Real.log (Real.log ((k : ℝ) + 1)) ≤ Real.log ((k : ℝ) + 1) :=
        Real.log_le_log hlog (by linarith)
      _ ≤ (k : ℝ) := hsmall
  nlinarith

end MainLower
end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MainLowerVerified
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace Problem337

/-- The elementary lower half of the main order theorem, with an explicit
absolute constant, independent of the short-expansion upper construction. -/
theorem main_double_log_lower_bound (b : ℕ) (hb : 2 ≤ b) :
    (1 / 2 : ℝ) * Real.log (Real.log (b : ℝ)) ≤ (maxEgyptianLength b : ℝ) := by
  have ha : 1 ≤ b - 1 := by omega
  have hab : b - 1 < b := by omega
  obtain ⟨n, hn⟩ := egyptianLength_attained_of_exists
    (exists_strict_unit_fraction_sum (b - 1) b ha hab)
  have hden := MainLower.denominator_le_of_sum
    (fun s d hd hm hs => ordered_unit_denominator_bound d hd hm hs)
    hb n (fun i => le_trans (by decide : 1 ≤ 2) (hn.1 i)) hn.2.2
  have hlog := MainLower.log_log_le_twice hb hden
  have hmax : (egyptianLength (b - 1) b : ℝ) ≤ (maxEgyptianLength b : ℝ) := by
    exact_mod_cast egyptianLength_le_max ha hab
  nlinarith

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RandomResidueRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RandomProducts

/-- Rational and real ceiling remainder formulas agree exactly. -/
theorem sampledRemainder_eq_real_ceil {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (u : ℕ) (hu : 0 < u) (I : Fin m → Bool) :
    sampledRemainder p u I =
      u * ⌈(sampledProduct p I : ℝ) / u⌉₊ - sampledProduct p I := by
  let : NeZero u := ⟨Nat.ne_of_gt hu⟩
  unfold sampledRemainder
  rw [ceiling_remainder_eq_neg_cast_val,
    natural_ceil_residue_eq_neg_zmod_val u (sampledProduct p I) hu]

/-- A sampled rational-ceiling remainder has exactly the same normalized
fractional-part interpretation as the real-ceiling construction. -/
theorem sampledRemainder_lt_iff_fract {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (u : ℕ) (hu : 0 < u)
    (I : Fin m → Bool) (δ : ℝ) :
    (sampledRemainder p u I : ℝ) < δ * u ↔
      Int.fract (-(sampledProduct p I : ℝ) / u) < δ := by
  have hrem := sampledRemainder_eq_real_ceil p u hu I
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  rw [← natural_ceil_residue_div_eq_fract_neg u (sampledProduct p I) hu, ← hrem]
  exact (div_lt_iff₀ huR).symm

end Problem337.RandomProducts

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RawDensityParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open Filter

namespace Problem337.RawDensityParameters

theorem DM_gt_one : 1 < DM := by norm_num [DM]
theorem D₀_ge_one : 1 ≤ D₀ := by norm_num [D₀]
theorem eta_pos : 0 < η := by norm_num [η]
theorem eta_le_half : η ≤ 1 / 2 := by norm_num [η]
theorem c_pos : 0 < c := by norm_num [c]
theorem K_nonneg : 0 ≤ K := by norm_num [K, DM, η]
theorem r_ge_two : 2 ≤ r := by norm_num [r, K, DM, η]
theorem eight_K_le_r : 8 * K ≤ r := le_rfl
theorem L_pos : 0 < L := by
  have h := TerminalAssembly.terminalCoefficient_pos D₀_ge_one
    (show 0 < 1 - η by norm_num [η]) (show 1 - η < 1 by norm_num [η])
  dsimp [L]
  linarith [K_nonneg]

/-- All scalar conditions required by the fixed-loss geometric constructor hold
at one common onset, independently of the natural values `C` and `M`. -/
theorem eventually_constructor_conditions : ∀ᶠ S : ℝ in atTop,
    1 ≤ S ∧ 1 ≤ Real.log S ∧ 2 ≤ ResidueLevels.scale S ∧
    S / (2 * Real.log S) ≤ (ResidueLevels.scale S : ℝ) ∧
    1 + 2 * Real.exp (S ^ (1 / 4 : ℝ) / r) ≤
      Real.exp (2 * S ^ (1 / 4 : ℝ)) := by
  have hpower : ∀ᶠ S : ℝ in atTop, (2 : ℝ) ≤ S ^ (1 / 4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop 2
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    ResidueLevels.eventually_scale_bounds, hpower] with S hS hscale hpower
  exact ⟨hS, hscale.1, hscale.2.1, hscale.2.2.1,
    descent_coefficient_bound _ _ hpower (by linarith [r_ge_two])⟩

/-- Canonical numerical specialization of the geometric constructor. This
lemma supplies only scalar conditions: genuine residue data, the denominator
window, and binary divisibility are still required explicitly. -/
theorem eventually_raw_density_supply_of_residue_data :
    ∀ᶠ S : ℝ in atTop, ∀ C M : ℕ,
      Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
      Real.exp S < (M : ℝ) →
      (M : ℝ) ≤ Real.exp (DM * S) →
      2 ^ TerminalDepth.binaryExponent D₀ S ∣ M →
      GeometricDensity.ResidueData DM D₀ η c r S 2 C M →
      RawDensitySupply DM L c K r S C := by
  filter_upwards [eventually_constructor_conditions] with S hS
  intro C M hC hM hMupper hbinary H
  have hCpos : 0 < C := by
    exact_mod_cast (Real.exp_pos _).trans_le hC
  exact GeometricDensity.raw_density_supply_of_geometric_residues H
    DM_gt_one D₀_ge_one eta_pos eta_le_half hS.1 hS.2.1 hS.2.2.1
    hS.2.2.2.1 hCpos hM hMupper hbinary (by norm_num) hS.2.2.2.2

end Problem337.RawDensityParameters

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrimePool
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace Problem337

/-- A coarse elementary lower estimate for the prime counting function. -/
theorem eventually_prime_count_lower :
    ∀ᶠ x : ℝ in atTop, x / (4 * Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hsmall := ((isLittleO_const_id_atTop (2 * Real.log 2)).add
    Real.isLittleO_log_id_atTop).bound (c := 1 / 4) (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with x hs hx
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have herror : 2 * Real.log 2 + Real.log x ≤ x / 4 := by
    have hh := (le_abs_self (2 * Real.log 2 + Real.log x)).trans (by simpa only [Real.norm_eq_abs] using hs)
    simpa [Real.norm_eq_abs, abs_of_nonneg hxpos.le, div_eq_mul_inv, mul_comm] using hh
  have hshift : Real.log (x + 2) ≤ Real.log 2 + Real.log x := by
    calc
      Real.log (x + 2) ≤ Real.log (2 * x) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hxpos.ne'
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  calc
    x / (4 * Real.log x) = (x / 4) / Real.log x := by ring
    _ ≤ ((x - 1) * Real.log 2 - Real.log (x + 2)) / Real.log x := by
      apply div_le_div_of_nonneg_right _ hlogpos.le
      nlinarith
    _ ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := Chebyshev.pi_ge' (by linarith)

/-- A coarse elementary upper estimate for the prime counting function. -/
theorem eventually_prime_count_upper :
    ∀ᶠ x : ℝ in atTop, (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 5 * x / Real.log x := by
  have hsmall := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound
    (c := 1) (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with x hs hx
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogsmall : Real.log x ≤ Real.sqrt x := by
    have hh := (le_abs_self (Real.log x)).trans (by simpa only [Real.norm_eq_abs] using hs)
    simpa [Real.norm_eq_abs, Real.sqrt_eq_rpow, abs_of_nonneg (Real.rpow_nonneg hxpos.le _)] using hh
  have hsqrt : Real.sqrt x ≤ x / Real.log x := by
    apply (le_div_iff₀ hlogpos).mpr
    calc
      Real.sqrt x * Real.log x ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_left hlogsmall (Real.sqrt_nonneg x)
      _ = x := Real.mul_self_sqrt hxpos.le
  have hlogfour : Real.log 4 ≤ 2 := by
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have heq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  calc
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ Real.log 4 * x / Real.log (Real.sqrt x) + Real.sqrt x :=
      Chebyshev.pi_le_log4_mul_div (by linarith)
    _ = 2 * Real.log 4 * x / Real.log x + Real.sqrt x := by
      rw [Real.log_sqrt hxpos.le]; ring
    _ ≤ 4 * x / Real.log x + x / Real.log x := by
      apply add_le_add _ hsqrt
      apply div_le_div_of_nonneg_right _ hlogpos.le
      nlinarith
    _ = 5 * x / Real.log x := by ring

theorem eventually_wide_prime_pool_large :
    ∀ᶠ x : ℝ in atTop,
      x / Real.log x ≤ ((widePrimePool x).card : ℝ) := by
  have hscale : Tendsto (fun x : ℝ => 64 * x) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_id
  filter_upwards [hscale.eventually eventually_prime_count_lower,
    eventually_prime_count_upper, eventually_ge_atTop (64 : ℝ)] with x hl hu hx
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hloglargepos : 0 < Real.log (64 * x) := Real.log_pos (by nlinarith)
  have hloglarge : Real.log (64 * x) ≤ 2 * Real.log x := by
    rw [Real.log_mul (by norm_num) hxpos.ne']
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 64) hx
    linarith
  have hlow : 8 * x / Real.log x ≤ (Nat.primeCounting ⌊64 * x⌋₊ : ℝ) := by
    apply le_trans _ hl
    apply (div_le_div_iff₀ hlogpos (by positivity : 0 < 4 * Real.log (64 * x))).mpr
    nlinarith [mul_le_mul_of_nonneg_left hloglarge (show 0 ≤ 32 * x by positivity)]
  have hsub : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesLE ⌊64 * x⌋₊ :=
    Nat.primesLE_mono (Nat.floor_mono (by nlinarith))
  have hcards := Finset.card_le_card hsub
  rw [widePrimePool, Finset.card_sdiff_of_subset hsub, Nat.cast_sub hcards,
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  have hratio : 0 ≤ x / Real.log x := by positivity
  simp only [mul_div_assoc] at hu hlow
  linarith

/-- The residue construction needs polynomially many primes at scale `S^100`.
Chebyshev's elementary estimates suffice if the fixed interval width is 64. -/
theorem eventually_residue_prime_pool_large :
    ∀ᶠ S : ℝ in atTop,
      S ^ 99 ≤ ((widePrimePool (S ^ 100)).card : ℝ) := by
  have hp : Tendsto (fun S : ℝ => S ^ 100) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hsmall := Real.isLittleO_log_id_atTop.bound (c := 1 / 100) (by norm_num)
  filter_upwards [hp.eventually eventually_wide_prime_pool_large,
    hsmall, eventually_ge_atTop (2 : ℝ)] with S hpool hs hS
  have hSpos : 0 < S := by linarith
  have hlogpos : 0 < Real.log S := Real.log_pos (by linarith)
  have hlogsmall : 100 * Real.log S ≤ S := by
    have hh := (le_abs_self (Real.log S)).trans (by simpa only [Real.norm_eq_abs] using hs)
    simp only [id_eq, abs_of_nonneg hSpos.le] at hh
    linarith
  apply le_trans _ hpool
  rw [Real.log_pow]
  norm_num
  apply (le_div_iff₀ (by positivity : 0 < 100 * Real.log S)).mpr
  calc
    S ^ 99 * (100 * Real.log S) ≤ S ^ 99 * S :=
      mul_le_mul_of_nonneg_left hlogsmall (by positivity)
    _ = S ^ 100 := by ring

/-- Membership records the exact real endpoints, without rounding ambiguity. -/
theorem mem_widePrimePool_iff {x : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    p ∈ widePrimePool x ↔ Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 64 * x := by
  simp only [widePrimePool, Finset.mem_sdiff, Nat.mem_primesLE,
    Nat.le_floor_iff (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64) hx), Nat.le_floor_iff hx]
  constructor
  · rintro ⟨⟨hupper, hprime⟩, hnot⟩
    refine ⟨hprime, ?_, hupper⟩
    exact lt_of_not_ge (fun h => hnot ⟨h, hprime⟩)
  · rintro ⟨hprime, hlower, hupper⟩
    exact ⟨⟨hupper, hprime⟩, fun h => (not_le_of_gt hlower) h.1⟩

/-- Full elementary prime-pool interface for the residue construction. -/
theorem eventually_residue_prime_pool_spec :
    ∀ᶠ S : ℝ in atTop,
      S ^ 99 ≤ ((widePrimePool (S ^ 100)).card : ℝ) ∧
      ∀ p ∈ widePrimePool (S ^ 100),
        Nat.Prime p ∧ S ^ 100 < (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101 := by
  filter_upwards [eventually_residue_prime_pool_large,
    eventually_ge_atTop (64 : ℝ)] with S hcard hS
  refine ⟨hcard, ?_⟩
  intro p hp
  obtain ⟨hprime, hlower, hupper⟩ := (mem_widePrimePool_iff (by positivity)).mp hp
  refine ⟨hprime, hlower, hupper.trans ?_⟩
  calc
    64 * S ^ 100 ≤ S * S ^ 100 := mul_le_mul_of_nonneg_right hS (by positivity)
    _ = S ^ 101 := by ring

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ResidueDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.ResidueConstruction

/-- A binary factor can cover any positive cutoff at a logarithmic cost of at most `log 2`. -/
theorem exists_binary_factor {x : ℝ} (hx : 1 ≤ x) :
    ∃ a : ℕ, x ≤ (2 : ℝ) ^ a ∧ (2 : ℝ) ^ a ≤ 2 * x ∧
      (a : ℝ) * Real.log 2 ≤ Real.log x + Real.log 2 := by
  obtain ⟨n, hn, hnx⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  have hxpos : 0 < x := by linarith
  have hpow : (2 : ℝ) ^ (n + 1) ≤ 2 * x := by
    rw [pow_succ]
    nlinarith
  refine ⟨n + 1, hnx.le, hpow, ?_⟩
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ (n + 1)) hpow
  rw [Real.log_pow, Real.log_mul (by norm_num) (ne_of_gt hxpos)] at hlog
  linarith

theorem exists_binary_cutoff {S : ℝ} (hS : 1 ≤ S) (D : ℕ) :
    ∃ a : ℕ, S ^ D ≤ (2 : ℝ) ^ a ∧
      (a : ℝ) * Real.log 2 ≤ (D : ℝ) * Real.log S + Real.log 2 := by
  obtain ⟨a, ha, _, hlog⟩ := exists_binary_factor (one_le_pow₀ hS)
  refine ⟨a, ha, ?_⟩
  simpa only [Real.log_pow] using hlog

theorem subsetEntry_dvd_product {m : ℕ} (p : Fin m → ℕ) (I : Fin m → Fin 2) :
    subsetEntry p I ∣ ∏ j, p j := by
  apply Finset.prod_dvd_prod_of_dvd
  intro j hj
  have hI : (I j).val = 0 ∨ (I j).val = 1 := by omega
  rcases hI with hI | hI <;> simp [hI]

/-- A selected prime divides a fixed-block entry precisely when its bit is one. -/
theorem prime_dvd_subsetEntry_iff {m : ℕ} (p : Fin m → ℕ)
    (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (I : Fin m → Fin 2) (j : Fin m) :
    p j ∣ subsetEntry p I ↔ (I j).val = 1 := by
  constructor
  · intro h
    obtain ⟨k, hk, hdiv⟩ :=
      ((Nat.prime_iff.mp (hp j)).dvd_finsetProd_iff (fun k => p k ^ (I k).val)).mp h
    have hjk : j = k := hinj (Nat.prime_eq_prime_of_dvd_pow (hp j) (hp k) hdiv)
    subst k
    have hI : (I j).val = 0 ∨ (I j).val = 1 := by omega
    rcases hI with hI | hI
    · simp only [hI, pow_zero] at hdiv
      exact False.elim ((hp j).not_dvd_one hdiv)
    · exact hI
  · intro hI
    apply dvd_trans (show p j ∣ p j ^ (I j).val by simp [hI])
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)

/-- Distinct primes give all `2^m` fixed-block entries distinct. -/
theorem subsetEntry_injective {m : ℕ} (p : Fin m → ℕ)
    (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p) :
    Function.Injective (subsetEntry p) := by
  intro I J hIJ
  funext j
  apply Fin.ext
  have hiff : (I j).val = 1 ↔ (J j).val = 1 := by
    rw [← prime_dvd_subsetEntry_iff p hp hinj I j,
      ← prime_dvd_subsetEntry_iff p hp hinj J j, hIJ]
  have hi := (I j).isLt
  have hj := (J j).isLt
  omega

theorem subsetEntry_image_card {m : ℕ} (p : Fin m → ℕ)
    (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p) :
    (Finset.univ.image (subsetEntry p)).card = 2 ^ m := by
  rw [Finset.card_image_of_injective _ (subsetEntry_injective p hp hinj)]
  simp

theorem pairedEntry_dvd_product {m : ℕ} (q : Fin m → Fin 2 → ℕ)
    (I : Fin m → Fin 2) : pairedEntry q I ∣ ∏ j, ∏ e, q j e := by
  apply Finset.prod_dvd_prod_of_dvd
  intro j hj
  exact Finset.dvd_prod_of_mem (q j) (Finset.mem_univ (I j))

theorem binary_factor_dvd_auxiliary {m R : ℕ} (a : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) :
    2 ^ a ∣ auxiliaryDenominator a p q := by
  exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

/-- Any covering binary factor also contains the precise ceiling cutoff used by terminal descent. -/
theorem ceiling_binary_factor_dvd_auxiliary {m R : ℕ} (a D : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) {S : ℝ} (hS : 0 < S)
    (hcut : S ^ D ≤ (2 : ℝ) ^ a) :
    2 ^ ⌈(D : ℝ) * Real.log S / Real.log 2⌉₊ ∣ auxiliaryDenominator a p q := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (pow_pos hS D) hcut
  rw [Real.log_pow, Real.log_pow] at hlog
  have hceil : ⌈(D : ℝ) * Real.log S / Real.log 2⌉₊ ≤ a := by
    apply Nat.ceil_le.mpr
    exact (div_le_iff₀ hlog2).mpr hlog
  exact (pow_dvd_pow 2 hceil).trans (binary_factor_dvd_auxiliary a p q)

theorem subsetEntry_dvd_auxiliary {m R : ℕ} (a : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) (I : Fin m → Fin 2) :
    subsetEntry p I ∣ auxiliaryDenominator a p q := by
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (subsetEntry_dvd_product p I) _) _

theorem pairedEntry_dvd_auxiliary {m R : ℕ} (a : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) (i : Fin R) (I : Fin m → Fin 2) :
    pairedEntry (q i) I ∣ auxiliaryDenominator a p q := by
  apply dvd_mul_of_dvd_right
  exact (pairedEntry_dvd_product (q i) I).trans
    (Finset.dvd_prod_of_mem (fun i => ∏ j, ∏ e, q i j e) (Finset.mem_univ i))

theorem auxiliaryDenominator_pos {m R : ℕ} (a : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) (hp : ∀ j, 0 < p j)
    (hq : ∀ i j e, 0 < q i j e) : 0 < auxiliaryDenominator a p q := by
  unfold auxiliaryDenominator
  apply Nat.mul_pos
  · exact Nat.mul_pos (by positivity) (Finset.prod_pos (fun j _ => hp j))
  · exact Finset.prod_pos (fun i _ => Finset.prod_pos (fun j _ =>
      Finset.prod_pos (fun e _ => hq i j e)))

theorem subsetEntry_pos {m : ℕ} (p : Fin m → ℕ) (hp : ∀ j, 0 < p j)
    (I : Fin m → Fin 2) : 0 < subsetEntry p I := by
  exact Finset.prod_pos (fun j _ => pow_pos (hp j) _)

theorem pairedEntry_pos {m : ℕ} (q : Fin m → Fin 2 → ℕ)
    (hq : ∀ j e, 0 < q j e) (I : Fin m → Fin 2) : 0 < pairedEntry q I := by
  exact Finset.prod_pos (fun j _ => hq j (I j))

private theorem log_nat_product {ι : Type*} [Fintype ι] (f : ι → ℕ)
    (hf : ∀ i, 0 < f i) :
    Real.log ((∏ i, f i : ℕ) : ℝ) = ∑ i, Real.log (f i : ℝ) := by
  rw [Nat.cast_prod, Real.log_prod]
  intro i hi
  exact_mod_cast (Nat.ne_of_gt (hf i))

theorem log_auxiliaryDenominator {m R : ℕ} (a : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) (hp : ∀ j, 0 < p j)
    (hq : ∀ i j e, 0 < q i j e) :
    Real.log (auxiliaryDenominator a p q : ℝ) =
      (a : ℝ) * Real.log 2 + (∑ j, Real.log (p j : ℝ)) +
        ∑ i, ∑ j, ∑ e, Real.log (q i j e : ℝ) := by
  have hP : (0 : ℝ) < (∏ j, p j : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun j _ => hp j)
  have hQ : (0 : ℝ) < (∏ i, ∏ j, ∏ e, q i j e : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => Finset.prod_pos (fun j _ =>
      Finset.prod_pos (fun e _ => hq i j e)))
  have hqi : ∀ i, 0 < ∏ j, ∏ e, q i j e := fun i =>
    Finset.prod_pos (fun j _ => Finset.prod_pos (fun e _ => hq i j e))
  have hqj : ∀ i j, 0 < ∏ e, q i j e := fun i j =>
    Finset.prod_pos (fun e _ => hq i j e)
  have hlogQ : Real.log ((∏ i, ∏ j, ∏ e, q i j e : ℕ) : ℝ) =
      ∑ i, ∑ j, ∑ e, Real.log (q i j e : ℝ) := by
    rw [log_nat_product _ hqi]
    apply Finset.sum_congr rfl
    intro i hi
    rw [log_nat_product _ (hqj i)]
    apply Finset.sum_congr rfl
    intro j hj
    exact log_nat_product _ (hq i j)
  unfold auxiliaryDenominator
  rw [Nat.cast_mul, Nat.cast_mul,
    Real.log_mul (mul_ne_zero (by positivity) (ne_of_gt hP)) (ne_of_gt hQ),
    Real.log_mul (by positivity) (ne_of_gt hP), Nat.cast_pow, Real.log_pow,
    log_nat_product p hp, hlogQ]
  norm_num

/-- The precise logarithmic size budget counts one fixed block and two factors per pair. -/
theorem log_auxiliaryDenominator_le {m R : ℕ} (a : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) (hp : ∀ j, 0 < p j)
    (hq : ∀ i j e, 0 < q i j e) (U : ℝ)
    (hpU : ∀ j, Real.log (p j : ℝ) ≤ U)
    (hqU : ∀ i j e, Real.log (q i j e : ℝ) ≤ U) :
    Real.log (auxiliaryDenominator a p q : ℝ) ≤
      (a : ℝ) * Real.log 2 + (2 * (R : ℝ) + 1) * (m : ℝ) * U := by
  have hP : (∑ j, Real.log (p j : ℝ)) ≤ (m : ℝ) * U := by
    calc
      _ ≤ ∑ _j : Fin m, U := Finset.sum_le_sum (fun j _ => hpU j)
      _ = (m : ℝ) * U := by simp
  have hQ : (∑ i, ∑ j, ∑ e, Real.log (q i j e : ℝ)) ≤
      2 * (R : ℝ) * (m : ℝ) * U := by
    calc
      _ ≤ ∑ _i : Fin R, ∑ _j : Fin m, ∑ _e : Fin 2, U := by
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
          Finset.sum_le_sum (fun e _ => hqU i j e)))
      _ = 2 * (R : ℝ) * (m : ℝ) * U := by simp; ring
  rw [log_auxiliaryDenominator a p q hp hq]
  nlinarith

theorem log_auxiliaryDenominator_ge {m R : ℕ} (a : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) (hp : ∀ j, 0 < p j)
    (hq : ∀ i j e, 0 < q i j e) (L : ℝ)
    (hpL : ∀ j, L ≤ Real.log (p j : ℝ)) :
    (m : ℝ) * L ≤ Real.log (auxiliaryDenominator a p q : ℝ) := by
  have hP : (m : ℝ) * L ≤ ∑ j, Real.log (p j : ℝ) := by
    calc
      _ = ∑ _j : Fin m, L := by simp
      _ ≤ ∑ j, Real.log (p j : ℝ) := Finset.sum_le_sum (fun j _ => hpL j)
  have hQ : 0 ≤ ∑ i, ∑ j, ∑ e, Real.log (q i j e : ℝ) := by
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun e _ => Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ q i j e from hq i j e)))))
  have ha : 0 ≤ (a : ℝ) * Real.log 2 := by positivity
  rw [log_auxiliaryDenominator a p q hp hq]
  linarith

theorem log_pairedEntry_le {m : ℕ} (q : Fin m → Fin 2 → ℕ)
    (hq : ∀ j e, 0 < q j e) (I : Fin m → Fin 2) (U : ℝ)
    (hqU : ∀ j e, Real.log (q j e : ℝ) ≤ U) :
    Real.log (pairedEntry q I : ℝ) ≤ (m : ℝ) * U := by
  rw [pairedEntry, log_nat_product _ (fun j => hq j (I j))]
  calc
    _ ≤ ∑ _j : Fin m, U := Finset.sum_le_sum (fun j _ => hqU j (I j))
    _ = (m : ℝ) * U := by simp

theorem log_subsetEntry_le {m : ℕ} (p : Fin m → ℕ) (hp : ∀ j, 0 < p j)
    (I : Fin m → Fin 2) (U : ℝ) (hU : 0 ≤ U)
    (hpU : ∀ j, Real.log (p j : ℝ) ≤ U) :
    Real.log (subsetEntry p I : ℝ) ≤ (m : ℝ) * U := by
  rw [subsetEntry, log_nat_product _ (fun j => pow_pos (hp j) _)]
  calc
    _ ≤ ∑ _j : Fin m, U := by
      apply Finset.sum_le_sum
      intro j hj
      have hI : (I j).val = 0 ∨ (I j).val = 1 := by omega
      rcases hI with hI | hI
      · simpa [hI] using hU
      · simpa [hI] using hpU j
    _ = (m : ℝ) * U := by simp

/-- Explicit analytic inequalities imply the required exponential denominator window. -/
theorem auxiliaryDenominator_exp_bounds {m R : ℕ} (a : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) (hp : ∀ j, 0 < p j)
    (hq : ∀ i j e, 0 < q i j e) (S L U D : ℝ)
    (hpL : ∀ j, L ≤ Real.log (p j : ℝ))
    (hpU : ∀ j, Real.log (p j : ℝ) ≤ U)
    (hqU : ∀ i j e, Real.log (q i j e : ℝ) ≤ U)
    (hLower : S < (m : ℝ) * L)
    (hUpper : (a : ℝ) * Real.log 2 + (2 * (R : ℝ) + 1) * (m : ℝ) * U ≤ D * S) :
    Real.exp S < (auxiliaryDenominator a p q : ℝ) ∧
      (auxiliaryDenominator a p q : ℝ) ≤ Real.exp (D * S) := by
  have hpos : (0 : ℝ) < auxiliaryDenominator a p q := by
    exact_mod_cast auxiliaryDenominator_pos a p q hp hq
  constructor
  · calc
      Real.exp S < Real.exp (Real.log (auxiliaryDenominator a p q : ℝ)) :=
        Real.exp_lt_exp.mpr (hLower.trans_le (log_auxiliaryDenominator_ge a p q hp hq L hpL))
      _ = (auxiliaryDenominator a p q : ℝ) := Real.exp_log hpos
  · calc
      (auxiliaryDenominator a p q : ℝ) = Real.exp (Real.log (auxiliaryDenominator a p q : ℝ)) :=
        (Real.exp_log hpos).symm
      _ ≤ Real.exp (D * S) := Real.exp_le_exp.mpr
        ((log_auxiliaryDenominator_le a p q hp hq U hpU hqU).trans hUpper)

end Problem337.ResidueConstruction

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrimePoolSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- Select the deterministic prime vector of length `floor(S/log S)` from the
proved elementary prime pool. -/
theorem eventually_residue_prime_vector :
    ∀ᶠ S : ℝ in atTop,
      ∃ p : Fin ⌊S / Real.log S⌋₊ → ℕ,
        Function.Injective p ∧
        (∀ i, Nat.Prime (p i) ∧ S ^ 100 < (p i : ℝ) ∧ (p i : ℝ) ≤ S ^ 101) ∧
        Function.Injective (ResidueConstruction.subsetEntry p) ∧
        (Finset.univ.image (ResidueConstruction.subsetEntry p)).card = 2 ^ ⌊S / Real.log S⌋₊ := by
  filter_upwards [eventually_residue_prime_pool_spec,
    eventually_ge_atTop (2 : ℝ), eventually_ge_atTop (Real.exp 1)] with S hpool hS hSexp
  have hSpos : 0 < S := by linarith
  have hlogS : 1 ≤ Real.log S := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log S := Real.log_le_log (Real.exp_pos 1) hSexp
  have hmreal : (⌊S / Real.log S⌋₊ : ℝ) ≤ S := by
    calc
      (⌊S / Real.log S⌋₊ : ℝ) ≤ S / Real.log S := Nat.floor_le (by positivity)
      _ ≤ S := div_le_self hSpos.le hlogS
  have hSpow : S ≤ S ^ 99 := by
    have hh : 1 ≤ S ^ 98 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ S)
    calc
      S = S * 1 := by ring
      _ ≤ S * S ^ 98 := mul_le_mul_of_nonneg_left hh hSpos.le
      _ = S ^ 99 := by ring
  have hmcard : ⌊S / Real.log S⌋₊ ≤ (widePrimePool (S ^ 100)).card := by
    exact_mod_cast hmreal.trans (hSpow.trans hpool.1)
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin ⌊S / Real.log S⌋₊) (β := ↥(widePrimePool (S ^ 100))) (by simpa using hmcard)
  let p : Fin ⌊S / Real.log S⌋₊ → ℕ := fun i => (e i).val
  have hinj : Function.Injective p := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  have hp : ∀ i, Nat.Prime (p i) ∧ S ^ 100 < (p i : ℝ) ∧ (p i : ℝ) ≤ S ^ 101 := by
    intro i
    exact hpool.2 (p i) (e i).property
  exact ⟨p, hinj, hp, ResidueConstruction.subsetEntry_injective p (fun i => (hp i).1) hinj,
    ResidueConstruction.subsetEntry_image_card p (fun i => (hp i).1) hinj⟩

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ResidueWideDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.ResidueConstruction

/-- The wide prime pool fits the same auxiliary-denominator size budget. -/
theorem residue_size_budget_wide {S : ℝ} {m a : ℕ}
    (hlog : 1 ≤ Real.log S) (hlarge : 100 * Real.log S ≤ S)
    (hmLower : S - Real.log S ≤ (m : ℝ) * Real.log S)
    (hmUpper : (m : ℝ) * Real.log S ≤ S)
    (ha : (a : ℝ) * Real.log 2 ≤ 100000 * Real.log S + Real.log 2) :
    S < (m : ℝ) * (100 * Real.log S) ∧
      (a : ℝ) * Real.log 2 + (2 * (1000 : ℝ) + 1) * (m : ℝ) *
        (101 * Real.log S) ≤ 204204 * S ∧
      (m : ℝ) * (101 * Real.log S) ≤ 101 * S := by
  have htwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- PNT-free factor-window variant of the residue denominator construction. -/
theorem construct_residue_denominator_wide {m : ℕ} (p : Fin m → ℕ)
    (q : Fin 1000 → Fin m → Fin 2 → ℕ) (hp : ∀ j, 0 < p j)
    (hq : ∀ i j e, 0 < q i j e) {S : ℝ}
    (hS : 1 ≤ S) (hlog : 1 ≤ Real.log S) (hlarge : 100 * Real.log S ≤ S)
    (hmLower : S - Real.log S ≤ (m : ℝ) * Real.log S)
    (hmUpper : (m : ℝ) * Real.log S ≤ S)
    (hpL : ∀ j, 100 * Real.log S ≤ Real.log (p j : ℝ))
    (hpU : ∀ j, Real.log (p j : ℝ) ≤ 101 * Real.log S)
    (hqU : ∀ i j e, Real.log (q i j e : ℝ) ≤ 101 * Real.log S) :
    ∃ M : ℕ, Real.exp S < (M : ℝ) ∧ (M : ℝ) ≤ Real.exp (204204 * S) ∧
      2 ^ ⌈100000 * Real.log S / Real.log 2⌉₊ ∣ M ∧
      (∀ I : Fin m → Fin 2, subsetEntry p I ∣ M ∧ 1 ≤ subsetEntry p I ∧
        (subsetEntry p I : ℝ) ≤ Real.exp (101 * S)) ∧
      (∀ i (I : Fin m → Fin 2), pairedEntry (q i) I ∣ M ∧ 1 ≤ pairedEntry (q i) I ∧
        (pairedEntry (q i) I : ℝ) ≤ Real.exp (101 * S)) := by
  obtain ⟨a, hcut, ha⟩ := exists_binary_cutoff hS 100000
  norm_num only [Nat.cast_ofNat] at ha
  obtain ⟨hLower, hUpper, hEntry⟩ := residue_size_budget_wide hlog hlarge hmLower hmUpper ha
  obtain ⟨hMl, hMu⟩ := auxiliaryDenominator_exp_bounds a p q hp hq S
    (100 * Real.log S) (101 * Real.log S) 204204
    hpL hpU hqU hLower (by simpa using hUpper)
  refine ⟨auxiliaryDenominator a p q, hMl, hMu, ?_, ?_, ?_⟩
  · simpa using ceiling_binary_factor_dvd_auxiliary a 100000 p q (by linarith : 0 < S) hcut
  · intro I
    have hpos := subsetEntry_pos p hp I
    refine ⟨subsetEntry_dvd_auxiliary a p q I, hpos, ?_⟩
    calc
      (subsetEntry p I : ℝ) = Real.exp (Real.log (subsetEntry p I : ℝ)) :=
        (Real.exp_log (by exact_mod_cast hpos)).symm
      _ ≤ Real.exp (101 * S) := Real.exp_le_exp.mpr
        ((log_subsetEntry_le p hp I _ (by positivity) hpU).trans hEntry)
  · intro i I
    have hpos := pairedEntry_pos (q i) (hq i) I
    refine ⟨pairedEntry_dvd_auxiliary a p q i I, hpos, ?_⟩
    calc
      (pairedEntry (q i) I : ℝ) = Real.exp (Real.log (pairedEntry (q i) I : ℝ)) :=
        (Real.exp_log (by exact_mod_cast hpos)).symm
      _ ≤ Real.exp (101 * S) := Real.exp_le_exp.mpr
        ((log_pairedEntry_le (q i) (hq i) I _ (hqU i)).trans hEntry)

end Problem337.ResidueConstruction

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ResidueDenominatorCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337.ResidueConstruction

/-- Uniform arithmetic certificate for the common residue denominator.
The deterministic prime vector is chosen before the random blocks. Every
realization with the stated factor bounds has a suitable common denominator;
there is no prime-density, floor-scale, or logarithmic-size premise left. -/
theorem eventually_residue_denominator_certificate :
    ∀ᶠ S : ℝ in atTop,
      ∃ p : Fin (ResidueLevels.scale S) → ℕ,
        Function.Injective p ∧
        (∀ j, Nat.Prime (p j) ∧ S ^ 100 < (p j : ℝ) ∧ (p j : ℝ) ≤ S ^ 101) ∧
        Function.Injective (subsetEntry p) ∧
        ∀ q : Fin 1000 → Fin (ResidueLevels.scale S) → Fin 2 → ℕ,
          (∀ i j e, 0 < q i j e) →
          (∀ i j e, (q i j e : ℝ) ≤ S ^ 101) →
          ∃ M : ℕ, Real.exp S < (M : ℝ) ∧
            (M : ℝ) ≤ Real.exp (204204 * S) ∧
            2 ^ ⌈100000 * Real.log S / Real.log 2⌉₊ ∣ M ∧
            (∀ I : Fin (ResidueLevels.scale S) → Fin 2,
              subsetEntry p I ∣ M ∧ 1 ≤ subsetEntry p I ∧
                (subsetEntry p I : ℝ) ≤ Real.exp (101 * S)) ∧
            (∀ i (I : Fin (ResidueLevels.scale S) → Fin 2),
              pairedEntry (q i) I ∣ M ∧ 1 ≤ pairedEntry (q i) I ∧
                (pairedEntry (q i) I : ℝ) ≤ Real.exp (101 * S)) := by
  filter_upwards [eventually_residue_prime_vector,
    ResidueLevels.eventually_scale_bounds,
    ResidueLevels.tendsto_div_log.eventually (eventually_ge_atTop (100 : ℝ)),
    eventually_ge_atTop (3 : ℝ)] with S hp hscale hratio hS
  obtain ⟨p, hinj, hp, hsub, _⟩ := hp
  have hp' : ∀ j, Nat.Prime (p j) ∧ S ^ 100 < (p j : ℝ) ∧
      (p j : ℝ) ≤ S ^ 101 := hp
  refine ⟨p, hinj, hp', hsub, ?_⟩
  intro q hq hqU
  have hSp : 0 < S := by linarith
  have hlog : 0 < Real.log S := by linarith [hscale.1]
  have hlarge : 100 * Real.log S ≤ S := (le_div_iff₀ hlog).mp hratio
  have hmUpper : (ResidueLevels.scale S : ℝ) * Real.log S ≤ S :=
    (le_div_iff₀ hlog).mp hscale.2.2.2
  have hf := Nat.lt_floor_add_one (S / Real.log S)
  change S / Real.log S < (ResidueLevels.scale S : ℝ) + 1 at hf
  have hmLower : S - Real.log S ≤ (ResidueLevels.scale S : ℝ) * Real.log S := by
    have hf' := (div_lt_iff₀ hlog).mp hf
    nlinarith
  have hpPos : ∀ j, 0 < p j := fun j => (hp j).1.pos
  have hpLogLower : ∀ j, 100 * Real.log S ≤ Real.log (p j : ℝ) := by
    intro j
    have h := Real.log_le_log (pow_pos hSp 100) (hp j).2.1.le
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hpLogUpper : ∀ j, Real.log (p j : ℝ) ≤ 101 * Real.log S := by
    intro j
    have h := Real.log_le_log (by exact_mod_cast hpPos j) (hp j).2.2
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hqLogUpper : ∀ i j e, Real.log (q i j e : ℝ) ≤ 101 * Real.log S := by
    intro i j e
    have h := Real.log_le_log (by exact_mod_cast hq i j e) (hqU i j e)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  exact construct_residue_denominator_wide p q hpPos hq (by linarith) hscale.1
    hlarge hmLower hmUpper hpLogLower hpLogUpper hqLogUpper

end Problem337.ResidueConstruction

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SampledDenominatorCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337.RandomProducts

/-- An unconditional arithmetic certificate in the actual sample coordinates.
The prime pool and deterministic injective vector are chosen first. Every
subsequent collection of the thousand Boolean sample blocks has one common
auxiliary denominator with the required window and binary factor. Thus a
Fourier-good realization can be used without resampling or identifying any
repeated product values. -/
theorem eventually_sampled_denominator_certificate :
    ∀ᶠ S : ℝ in atTop,
      S ^ 99 ≤ ((widePrimePool (S ^ 100)).card : ℝ) ∧
      (∀ q ∈ widePrimePool (S ^ 100),
        Nat.Prime q ∧ S ^ 100 < (q : ℝ) ∧ (q : ℝ) ≤ S ^ 101) ∧
      ∃ p : Fin (blockLength S) → ℕ,
        Function.Injective p ∧
        (∀ j, Nat.Prime (p j) ∧ S ^ 100 < (p j : ℝ) ∧ (p j : ℝ) ≤ S ^ 101) ∧
        Function.Injective (ResidueConstruction.subsetEntry p) ∧
        ∀ f : Fin 1000 → ((Fin (blockLength S) × Bool) → widePrimePool (S ^ 100)),
          ∃ M : ℕ, Real.exp S < (M : ℝ) ∧
            (M : ℝ) ≤ Real.exp (204204 * S) ∧
            2 ^ ⌈100000 * Real.log S / Real.log 2⌉₊ ∣ M ∧
            (∀ I : Fin (blockLength S) → Fin 2,
              ResidueConstruction.subsetEntry p I ∣ M ∧
                1 ≤ ResidueConstruction.subsetEntry p I ∧
                (ResidueConstruction.subsetEntry p I : ℝ) ≤ Real.exp (101 * S)) ∧
            (∀ i (I : Fin (blockLength S) → Bool),
              sampledProduct (f i) I ∣ M ∧ 1 ≤ sampledProduct (f i) I ∧
                (sampledProduct (f i) I : ℝ) ≤ Real.exp (101 * S)) := by
  filter_upwards [ResidueConstruction.eventually_residue_denominator_certificate,
    eventually_residue_prime_pool_spec] with S hcert hpool
  obtain ⟨p, hpInj, hp, hsubset, hM⟩ := hcert
  refine ⟨hpool.1, hpool.2, p, hpInj, hp, hsubset, ?_⟩
  intro f
  have hpos : ∀ i j e, 0 < residueSamplePairs (f i) j e := by
    intro i j e
    exact (hpool.2 _ (f i (j, finTwoEquiv e)).property).1.pos
  have hupper : ∀ i j e, (residueSamplePairs (f i) j e : ℝ) ≤ S ^ 101 := by
    intro i j e
    exact (hpool.2 _ (f i (j, finTwoEquiv e)).property).2.2
  obtain ⟨M, hMl, hMu, hbin, hfixed, hpaired⟩ :=
    hM (fun i => residueSamplePairs (f i)) hpos hupper
  refine ⟨M, hMl, hMu, hbin, hfixed, ?_⟩
  intro i I
  have ht := hpaired i ((residueWordEquiv (blockLength S)).symm I)
  change ResidueConstruction.pairedEntry (residueSamplePairs (f i))
      ((residueWordEquiv (blockLength S)).symm I) ∣ M ∧
    1 ≤ ResidueConstruction.pairedEntry (residueSamplePairs (f i))
      ((residueWordEquiv (blockLength S)).symm I) ∧
    (ResidueConstruction.pairedEntry (residueSamplePairs (f i))
      ((residueWordEquiv (blockLength S)).symm I) : ℝ) ≤ Real.exp (101 * S) at ht
  have heq := sampledProduct_residueWordEquiv_symm (f i) I
  rw [heq] at ht
  exact ht

end Problem337.RandomProducts

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RawDensityExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open Filter
open scoped BigOperators

namespace Problem337

open RandomProducts

/-- The deterministic and sampled lists can use exactly the same Boolean
sample space. The deterministic list is chosen before the random realization,
and every realization is accommodated by a common bounded denominator.
This is an unconditional arithmetic statement, including the prime pool. -/
theorem eventually_common_residue_lists :
    ∀ᶠ S : ℝ in atTop,
      S ^ 99 ≤ ((widePrimePool (S ^ 100)).card : ℝ) ∧
      (∀ q ∈ widePrimePool (S ^ 100),
        Nat.Prime q ∧ S ^ 100 < (q : ℝ) ∧ (q : ℝ) ≤ S ^ 101) ∧
      ∃ t₀ : (Fin (ResidueLevels.scale S) → Bool) → ℕ,
        Function.Injective t₀ ∧
        ∀ f : Fin 1000 →
            ((Fin (ResidueLevels.scale S) × Bool) → widePrimePool (S ^ 100)),
          ∃ M : ℕ, Real.exp S < (M : ℝ) ∧
            (M : ℝ) ≤ Real.exp (RawDensityParameters.DM * S) ∧
            2 ^ TerminalDepth.binaryExponent RawDensityParameters.D₀ S ∣ M ∧
            (∀ I : Fin (ResidueLevels.scale S) → Bool,
              t₀ I ∣ M ∧ 0 < t₀ I ∧ (t₀ I : ℝ) ≤ Real.exp (101 * S)) ∧
            (∀ i (I : Fin (ResidueLevels.scale S) → Bool),
              sampledProduct (f i) I ∣ M ∧ 0 < sampledProduct (f i) I ∧
                (sampledProduct (f i) I : ℝ) ≤ Real.exp (101 * S)) := by
  filter_upwards [eventually_sampled_denominator_certificate] with S hS
  obtain ⟨hsize, hpool, p, hp, hprime, hsubset, hdenominator⟩ := hS
  let t₀ : (Fin (ResidueLevels.scale S) → Bool) → ℕ := fun I =>
    ResidueConstruction.subsetEntry p ((residueWordEquiv (ResidueLevels.scale S)).symm I)
  refine ⟨hsize, hpool, t₀, hsubset.comp (residueWordEquiv _).symm.injective, ?_⟩
  intro f
  obtain ⟨M, hMlo, hMhi, hbinary, hfixed, hsampled⟩ := hdenominator f
  refine ⟨M, hMlo, hMhi, hbinary, ?_, hsampled⟩
  intro I
  exact hfixed ((residueWordEquiv (ResidueLevels.scale S)).symm I)

open RawDensityParameters GeometricDensity in
/-- Actual deterministic residue supply simultaneously on the canonical high
levels, with the same Boolean sample type as the random construction. -/
theorem eventually_geometric_high_residue_lists :
    ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
      Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
      (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * S) →
      ∀ t : (Fin (ResidueLevels.scale S) → Bool) → ℕ,
        Function.Injective t →
        (∀ I, (t I : ℝ) ≤ Real.exp (101 * S)) →
        ∃ E : ℕ → Finset ℕ, ∀ j < depth DM η S,
          Real.exp S < cutoff DM η S j →
          ((E j).card : ℝ) ≤ cutoff DM η S j *
              Real.exp (-c * ResidueLevels.scale S) ∧
          ∀ u ∈ Finset.Icc 1 ⌊cutoff DM η S j⌋₊, u ∉ E j →
            cutoff DM η S (j + 1) < (u : ℝ) →
            contraction η S * (2 : ℝ) ^ ResidueLevels.scale S / 2 ≤
              ((Finset.univ.filter (fun I : Fin (ResidueLevels.scale S) → Bool =>
                Int.fract (-((C * t I : ℕ) : ℝ) / u) < contraction η S)).card : ℝ) := by
  classical
  filter_upwards [deterministic_high_residue_distribution (4 * (DM + 2))
      (by norm_num [DM]), ResidueLevels.eventually_scale_bounds,
    eventually_ge_atTop (1 : ℝ)] with S hhigh hscale hS
  intro C hClo hChi t ht hsize
  have hm : (0 : ℝ) < ResidueLevels.scale S := by
    exact_mod_cast (show 0 < ResidueLevels.scale S by omega)
  have hη : 0 < η := eta_pos
  have hrho : Real.exp (-(ResidueLevels.scale S : ℝ) / 10000) = contraction η S := by
    unfold contraction η
    congr 1
    ring
  have herr : Real.exp (-(ResidueLevels.scale S : ℝ) / 1000) =
      Real.exp (-c * ResidueLevels.scale S) := by
    unfold c
    congr 1
    ring
  have hcard : Real.exp (Real.log 2 * (ResidueLevels.scale S : ℝ)) ≤
      ((Finset.univ : Finset (Fin (ResidueLevels.scale S) → Bool)).card : ℝ) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp
  have hlocal : ∀ j : ℕ, ∃ E : Finset ℕ,
      j < depth DM η S → Real.exp S < cutoff DM η S j →
        (E.card : ℝ) ≤ cutoff DM η S j * Real.exp (-c * ResidueLevels.scale S) ∧
        ∀ u ∈ Finset.Icc 1 ⌊cutoff DM η S j⌋₊, u ∉ E →
          cutoff DM η S (j + 1) < (u : ℝ) →
          contraction η S * (2 : ℝ) ^ ResidueLevels.scale S / 2 ≤
            ((Finset.univ.filter (fun I : Fin (ResidueLevels.scale S) → Bool =>
              Int.fract (-((C * t I : ℕ) : ℝ) / u) < contraction η S)).card : ℝ) := by
    intro j
    by_cases hj : j < depth DM η S
    · by_cases hlarge : Real.exp S < cutoff DM η S j
      · have hX : cutoff DM η S j ≤ Real.exp ((4 * (DM + 2)) * S / 4) := by
          have hmono := (ResidueLevels.level_strictAnti
            (A := (DM + 2) * S) hm hη).antitone (Nat.zero_le j)
          simpa only [ResidueLevels.level_zero,
            show 4 * (DM + 2) * S / 4 = (DM + 2) * S by ring] using hmono
        obtain ⟨E, hsub, hEc, hcount⟩ := hhigh (ResidueLevels.scale S)
          (cutoff DM η S j) C hscale.2.2.1 hscale.2.2.2 hlarge.le hX hClo hChi
          Finset.univ t (fun _ _ _ _ heq => ht heq) hcard (fun I _ => hsize I)
        refine ⟨E, fun _ _ => ⟨by simpa only [herr] using hEc, ?_⟩⟩
        intro u hu hnot hunext
        have hstep : cutoff DM η S (j + 1) =
            Real.exp (-(ResidueLevels.scale S : ℝ) / 10000) * cutoff DM η S j := by
          rw [hrho]
          exact ResidueLevels.level_succ _ _ _ j
        have hfloor : ⌊Real.exp (-(ResidueLevels.scale S : ℝ) / 10000) *
            cutoff DM η S j⌋₊ < u := by
          apply (Nat.floor_lt' (by have := (Finset.mem_Icc.mp hu).1; omega : u ≠ 0)).2
          simpa only [hstep] using hunext
        have hu' := Finset.mem_Icc.mpr
          ⟨show ⌊Real.exp (-(ResidueLevels.scale S : ℝ) / 10000) *
              cutoff DM η S j⌋₊ + 1 ≤ u by omega, (Finset.mem_Icc.mp hu).2⟩
        simpa only [hrho, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using hcount u hu' hnot
      · exact ⟨∅, fun _ hh => (hlarge hh).elim⟩
    · exact ⟨∅, fun h _ => (hj h).elim⟩
  choose E hE using hlocal
  exact ⟨E, hE⟩

/-- Reindex the sampled count without losing repeated data. -/
theorem reindexed_boolean_residue_count {m : ℕ}
    (t : (Fin m → Bool) → ℕ) (ρ : ℝ) (u : ℕ)
    (h : ρ / 2 * (2 : ℝ) ^ m ≤
      ((Finset.univ.filter (fun a : Fin m → Bool =>
        Int.fract (-(t a : ℝ) / u) < ρ)).card : ℝ)) :
    ρ * ((residueIndices (Fin m → Bool)).card : ℝ) / 2 ≤
      (((residueIndices (Fin m → Bool)).filter (fun i =>
        Int.fract (-((residueEntry t i : ℕ) : ℝ) / u) < ρ)).card : ℝ) := by
  classical
  rw [card_filter_residueEntry t (fun n : ℕ => Int.fract (-(n : ℝ) / u) < ρ)]
  simp only [residueIndices_card, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  convert h using 1 <;> first | rfl | ring

open RawDensityParameters GeometricDensity in
/-- Unconditional arithmetic construction of the raw density supply. The
prime-product and sampled lists share one bounded denominator, and the actual
high and middle residue estimates are joined before the density descent. -/
theorem eventually_raw_density_supply :
    ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
      Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
      (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * S) →
      RawDensitySupply DM L c K r S C := by
  classical
  filter_upwards [eventually_common_residue_lists,
    eventually_geometric_high_residue_lists,
    eventually_common_geometric_random_fractional_residues (DM + 2)
      (by norm_num [DM]),
    eventually_residue_level_moment DM η r DM_gt_one eta_pos eta_le_half
      (by linarith [r_ge_two]),
    eventually_raw_density_supply_of_residue_data,
    eventually_ge_atTop (1 : ℝ)] with S hlists hhigh hrandom hmoment hconstruct hS
  intro C hClo hChi
  have hSpos : 0 < S := by linarith
  obtain ⟨hpoolsize, hpool, t₀, ht₀, hdenom⟩ := hlists
  obtain ⟨f, E₁, hmiddle, hterminal⟩ := hrandom (widePrimePool (S ^ 100))
    (fun q hq => (hpool q hq).1)
    (fun q hq => ⟨(hpool q hq).2.1.le, (hpool q hq).2.2⟩) hpoolsize
  obtain ⟨M, hMlo, hMhi, hbinary, hfixed, hsampled⟩ := hdenom f
  obtain ⟨E₀, hhighE⟩ := hhigh C hClo hChi t₀ ht₀ (fun I => (hfixed I).2.2)
  let t₁ : (Fin (ResidueLevels.scale S) → Bool) → ℕ :=
    fun a => sampledProduct (f 0) a
  let I : Finset ℕ := residueIndices (Fin (ResidueLevels.scale S) → Bool)
  have hI : I.Nonempty := residueIndices_nonempty_iff _ |>.mpr inferInstance
  have hIcard : (I.card : ℝ) = (2 : ℝ) ^ ResidueLevels.scale S := by
    simp [I]
  have hpos₀ : ∀ i ∈ I, 0 < residueEntry t₀ i :=
    (forall_residueEntry_iff t₀ (fun t : ℕ => 0 < t)).mpr (fun a => (hfixed a).2.1)
  have hpos₁ : ∀ i ∈ I, 0 < residueEntry t₁ i :=
    (forall_residueEntry_iff _ (fun t : ℕ => 0 < t)).mpr
      (fun a => (hsampled 0 a).2.1)
  have hdvd₀ : ∀ i ∈ I, residueEntry t₀ i ∣ M :=
    (forall_residueEntry_iff t₀ (fun t : ℕ => t ∣ M)).mpr (fun a => (hfixed a).1)
  have hdvd₁ : ∀ i ∈ I, residueEntry t₁ i ∣ M :=
    (forall_residueEntry_iff _ (fun t : ℕ => t ∣ M)).mpr
      (fun a => (hsampled 0 a).1)
  have hrho : Real.exp (-(ResidueLevels.scale S : ℝ) / 10000) = contraction η S := by
    unfold contraction η
    congr 1
    ring
  have herr : Real.exp (-(ResidueLevels.scale S : ℝ) / 1000) =
      Real.exp (-c * ResidueLevels.scale S) := by
    unfold c
    congr 1
    ring
  have hjmiddle (j : ℕ) (hj : j < depth DM η S)
      (hsmall : cutoff DM η S j ≤ Real.exp S) :
      j ∈ GeometricRandomRanges.middleTests (DM + 2) S := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hsmall⟩
  have hdata : NormalizedResidueData DM D₀ η c r S 2 C M := by
    apply residueData_of_two_lists I hI (residueEntry t₀)
      (residueEntry t₁) hpos₀ hpos₁ hdvd₀ hdvd₁ E₀ E₁
    · intro j hj hlarge u hu hnot hunext
      have hx := (hhighE j hj hlarge).2 u hu hnot hunext
      rw [hIcard]
      dsimp only [I]
      rw [card_filter_residueEntry t₀ (fun t : ℕ =>
        Int.fract (-((C * t : ℕ) : ℝ) / u) < contraction η S)]
      exact hx
    · intro j hj hsmall u hu hnot hunext
      have hu' : u ∈ GeometricRandomRanges.middleLevel (DM + 2) S j :=
        Finset.mem_filter.mpr ⟨hu, hunext⟩
      have hx := (hmiddle j (hjmiddle j hj hsmall)).2.2 u hu' hnot
      have hrho' : Real.exp (-(blockLength S : ℝ) / 10000) = contraction η S := hrho
      rw [hrho'] at hx
      have hx' : contraction η S / 2 * (2 : ℝ) ^ ResidueLevels.scale S ≤
          ((Finset.univ.filter (fun a : Fin (ResidueLevels.scale S) → Bool =>
            Int.fract (-(t₁ a : ℝ) / u) < contraction η S)).card : ℝ) := by
        dsimp only [t₁, blockLength, ResidueLevels.scale] at hx ⊢
        exact hx
      exact reindexed_boolean_residue_count t₁ (contraction η S) u hx'
    · intro j hj hlarge
      exact (hhighE j hj hlarge).1
    · intro j hj hsmall
      have hx := (hmiddle j (hjmiddle j hj hsmall)).2.1
      change ((E₁ j).card : ℝ) ≤ cutoff DM η S j *
        Real.exp (-(ResidueLevels.scale S : ℝ) / 1000) at hx
      simpa only [herr] using hx
    · intro j hj t ht htdvd
      apply hmoment C M
      · exact_mod_cast (Real.exp_pos _).trans_le hClo
      · exact_mod_cast (Real.exp_pos _).trans hMlo
      · simpa only [show 2 * (4 * (DM + 2)) * S = 8 * (DM + 2) * S by ring]
          using hChi
      · exact hMhi
      · exact hj
      · exact htdvd
    · intro u huhi hulo
      have huR : (0 : ℝ) < u := (Real.rpow_pos_of_pos hSpos D₀).trans hulo
      have hu : 0 < u := by exact_mod_cast huR
      have hu' : u ∈ GeometricRandomRanges.terminalRange S := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨hu, Nat.le_floor huhi⟩, ?_⟩
        simpa only [D₀, show (100000 : ℝ) = (100000 : ℕ) by norm_num,
          Real.rpow_natCast] using hulo
      obtain ⟨i, a, ha⟩ := hterminal u hu'
      refine ⟨sampledProduct (f i) a, (hsampled i a).2.1, (hsampled i a).1, ?_⟩
      apply (sampledRemainder_lt_iff_fract (f i) u hu a ((u : ℝ) ^ (-η))).mp
      have hpower : (u : ℝ) ^ (-η) * u = (u : ℝ) ^ (9999 / 10000 : ℝ) := by
        calc
          (u : ℝ) ^ (-η) * u = (u : ℝ) ^ (-η) * (u : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = (u : ℝ) ^ (-η + 1) := (Real.rpow_add huR _ _).symm
          _ = (u : ℝ) ^ (9999 / 10000 : ℝ) := by congr 1; norm_num [η]
      simpa only [hpower] using ha
  exact hconstruct C M hClo hMlo hMhi hbinary (hdata.toResidueData hSpos)

/-- The complete quantitative raw-supply family, with no arithmetic or
analytic hypotheses left over. -/
theorem exists_raw_density_supply :
    ∃ DM L c K r : ℝ, 1 < DM ∧ 0 < L ∧ 0 < c ∧ 0 ≤ K ∧
      2 ≤ r ∧ 8 * K ≤ r ∧
      ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
        Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
        (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * S) →
        RawDensitySupply DM L c K r S C := by
  exact ⟨RawDensityParameters.DM, RawDensityParameters.L, RawDensityParameters.c,
    RawDensityParameters.K, RawDensityParameters.r, RawDensityParameters.DM_gt_one,
    RawDensityParameters.L_pos, RawDensityParameters.c_pos,
    RawDensityParameters.K_nonneg, RawDensityParameters.r_ge_two,
    RawDensityParameters.eight_K_le_r, eventually_raw_density_supply⟩

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

theorem main_double_log_order_oai :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∃ b0 : ℕ,
  ∀ b : ℕ, b0 ≤ b →
    c1 * Real.log (Real.log (b : ℝ)) ≤ (maxEgyptianLength b : ℝ) ∧
    (maxEgyptianLength b : ℝ) ≤ c2 * Real.log (Real.log (b : ℝ)) := by
  -- The unconditional arithmetic construction supplies the actual residue
  -- lists, common denominator, and divisor moments for the density descent.
  obtain ⟨DM, L, c, K, r, hDM, hL, hc, hK, hr, hKr, hsupply⟩ :
      ∃ DM L c K r : ℝ, 1 < DM ∧ 0 < L ∧ 0 < c ∧ 0 ≤ K ∧
        2 ≤ r ∧ 8 * K ≤ r ∧
        ∀ᶠ S : ℝ in Filter.atTop, ∀ C : ℕ,
          Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
          (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * S) →
          RawDensitySupply DM L c K r S C := exists_raw_density_supply
  obtain ⟨c2, hc2, b0, hupper⟩ :=
    main_upper_of_raw_density_supply DM L c K r hDM hL hc hK hr hKr hsupply
  refine ⟨1 / 2, c2, by norm_num, hc2, max 2 b0, ?_⟩
  intro b hb
  exact ⟨main_double_log_lower_bound b ((le_max_left 2 b0).trans hb),
    hupper b ((le_max_right 2 b0).trans hb)⟩

end Problem337

end

end OAI
end

theorem solution : type_of% @OAI.Problem337.main_double_log_order_oai := @OAI.Problem337.main_double_log_order_oai
