-- Prove2me | solution 1 for OAI.JointDickman.coarse_residue_smoothing_energy_proved_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:06:40.589621+00:00
-- url     : https://prove2.me/submissions/32ac6cd7-fe07-48d2-8309-550308eb605c

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_centered_bin_spectral_jd
import Theorems.Thm_OAI_JointDickman_primeCoarseFeature_laplace_approximation_jd
import Theorems.Thm_OAI_JointDickman_twisted_bin_spectral_jd

section
-- module Solutions.OAIQ083_JD.Compat
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ParameterEstimates
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compatible parameters and elementary asymptotics

The strict inequalities here are the weight margins of `arithmetic.tex`.
The subsequent limits account for the sampling entropy and the logarithmic
factors in the prime cutoff and amplification parameters.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

/-- Fixed logarithmic powers are smaller than every positive real power. -/
theorem log_power_div_power_tendsto_zero (r : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun B : ℝ => (Real.log B) ^ r / B ^ s) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop r hs).tendsto_div_nhds_zero

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_TwoSplitLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Two fair splits of the same prime site

The local law is constructed by first selecting a Bernoulli site and then,
conditional on that hit, taking two independent fair splits. Its common and
exclusive categories have mass `q/4` each. Finite product comparison gives
the independent common/exclusive model without assuming a coupling.
-/

namespace JointDickman

open scoped BigOperators

theorem finitePushMass_test {A B : Type*} [Fintype A] [Fintype B]
    (a : A → ℝ) (f : A → B) (F : B → ℂ) :
    (∑ y, (finitePushMass a f y : ℂ) * F y) = ∑ x, (a x : ℂ) * F (f x) := by
  classical
  calc
    _ = ∑ y, ∑ x, if f x = y then (a x : ℂ) * F y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [finitePushMass, Complex.ofReal_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ = ∑ x, ∑ y, if f x = y then (a x : ℂ) * F y else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      simp

/-- Pushforward commutes with finite independent products. -/
theorem finiteProductMass_pushforward {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (a : ∀ i, A i → ℝ) (f : ∀ i, A i → B i) (y : ∀ i, B i) :
    finiteProductMass (fun i => finitePushMass (a i) (f i)) y =
      finitePushMass (finiteProductMass a) (fun x i => f i (x i)) y := by
  classical
  unfold finiteProductMass finitePushMass
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (fun i => f i (x i)) = y
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro i _
    rw [ite_eq_left (congrFun h i)]
  · rw [ite_eq_right h]
    have hne : ∃ i, f i (x i) ≠ y i := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    obtain ⟨i, hi⟩ := hne
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem finiteProductMass_pushforward_test {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (a : ∀ i, A i → ℝ) (f : ∀ i, A i → B i) (F : (∀ i, B i) → ℂ) :
    (∑ y, (finiteProductMass (fun i => finitePushMass (a i) (f i)) y : ℂ) * F y) =
      ∑ x, (finiteProductMass a x : ℂ) * F (fun i => f i (x i)) := by
  simp_rw [finiteProductMass_pushforward]
  exact finitePushMass_test _ _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The manuscript's auxiliary prime scale

The lower cutoff is `B^1000`, the upper cutoff is `exp (4 B)`, and
`R = B / log (B^1000)`. The normalizing constant below is derived from
the published reciprocal-prime Mertens estimate.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

theorem auxiliaryCutoff_tendsto : Tendsto auxiliaryCutoff atTop atTop :=
  tendsto_pow_atTop (by norm_num : (1000 : ℕ) ≠ 0)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinLabels
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Multiplicative bin labels and real interpolation

The count in a finite prime bin includes multiplicity. Its additivity gives
complete multiplicativity of the uncentered labels. Centering is performed
only after evaluating a label; no multiplicativity is claimed for it.

A tensor product of finite Vandermonde inverses expresses every function of
bounded count vectors as a fixed finite linear combination of real,
nonnegative, 1-bounded multiplicative interpolants.
-/

namespace JointDickman

open Finset

theorem binCount_mul (E : Finset ℕ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    binCount E (m * n) = binCount E m + binCount E n := by
  simp [binCount, Nat.factorization_mul hm hn, Finset.sum_add_distrib]

theorem binCount_eq_zero_of_no_factor (E : Finset ℕ) (n : ℕ)
    (h : ∀ p ∈ E, ¬p ∣ n) : binCount E n = 0 := by
  exact Finset.sum_eq_zero fun p hp => Nat.factorization_eq_zero_of_not_dvd (h p hp)

section Labels

variable {ι R : Type*} [Fintype ι] [CommMonoidWithZero R]

theorem binLabel_apply {n : ℕ} (hn : n ≠ 0) (E : ι → Finset ℕ) (z : ι → R) :
    binLabel E z n = ∏ i, z i ^ binCount (E i) n := by simp [binLabel, hn]

/-- Complete multiplicativity, without a coprimality requirement. -/
theorem binLabel_mul (E : ι → Finset ℕ) (z : ι → R) (m n : ℕ) :
    binLabel E z (m * n) = binLabel E z m * binLabel E z n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp only [binLabel_apply (mul_ne_zero hm hn), binLabel_apply hm,
    binLabel_apply hn, binCount_mul _ hm hn, pow_add, Finset.prod_mul_distrib]

theorem binLabel_eq_one_of_no_factor (E : ι → Finset ℕ) (z : ι → R)
    {u : ℕ} (hu : u ≠ 0) (h : ∀ i p, p ∈ E i → ¬p ∣ u) :
    binLabel E z u = 1 := by
  simp only [binLabel_apply hu]
  apply Finset.prod_eq_one
  intro i _
  rw [binCount_eq_zero_of_no_factor _ _ (h i), pow_zero]

theorem binLabel_mul_invariant (E : ι → Finset ℕ) (z : ι → R)
    {u : ℕ} (hu : u ≠ 0) (h : ∀ i p, p ∈ E i → ¬p ∣ u) (n : ℕ) :
    binLabel E z (u * n) = binLabel E z n := by
  rw [binLabel_mul, binLabel_eq_one_of_no_factor E z hu h, one_mul]

end Labels

section Bounds

variable {ι : Type*} [Fintype ι] (E : ι → Finset ℕ)

theorem binLabel_nonneg (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) (n : ℕ) :
    0 ≤ binLabel E z n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [binLabel_apply hn]
  exact Finset.prod_nonneg fun i _ => pow_nonneg (hz i) _

theorem binLabel_le_one (z : ι → ℝ) (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    binLabel E z n ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  rw [binLabel_apply hn]
  exact Finset.prod_le_one (fun i _ => pow_nonneg (hz i).1 _)
    (fun i _ => pow_le_one₀ (hz i).1 (hz i).2)

theorem abs_binLabel_le_one (z : ι → ℝ) (hz : ∀ i, z i ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) : |binLabel E z n| ≤ 1 := by
  rw [abs_of_nonneg (binLabel_nonneg E z (fun i => (hz i).1) n)]
  exact binLabel_le_one E z hz n

theorem norm_binLabel_eq_one (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    {n : ℕ} (hn : n ≠ 0) : ‖binLabel E z n‖ = 1 := by
  simp [binLabel_apply hn, norm_prod, norm_pow, hz]

theorem norm_binLabel_le_one (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) (n : ℕ) :
    ‖binLabel E z n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  exact (norm_binLabel_eq_one E z hz hn).le

theorem norm_centered_binLabel_le_two (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1) (n : ℕ) : ‖binLabel E z n - μ‖ ≤ 2 := by
  calc
    _ ≤ ‖binLabel E z n‖ + ‖μ‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (norm_binLabel_le_one E z hz n) hμ
    _ = 2 := by norm_num

end Bounds

/-- A fixed nonzero integer eventually has no factor in any of the large-prime
bins. The first bin index is at least one, as in the manuscript. -/
theorem primeBin_eventually_no_factor {ι : Type*} (J : ℕ) (hJ : 0 < J)
    (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i) {u : ℕ} (hu : u ≠ 0) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ i p, p ∈ primeBin x J (k i) → ¬p ∣ u := by
  have hJreal : (0 : ℝ) < J := by exact_mod_cast hJ
  have hlarge := (tendsto_rpow_atTop (div_pos zero_lt_one hJreal)).eventually
    (Filter.eventually_ge_atTop (u : ℝ))
  filter_upwards [hlarge, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hxone
  intro i p hp hpdiv
  have hplower : x ^ ((k i : ℝ) / J) < (p : ℝ) :=
    Nat.lt_of_floor_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
  have hexp : (1 : ℝ) / J ≤ (k i : ℝ) / J :=
    div_le_div_of_nonneg_right (by exact_mod_cast hk i) hJreal.le
  have hpower := Real.rpow_le_rpow_of_exponent_le hxone hexp
  have hpupper : (p : ℝ) ≤ u := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hu) hpdiv
  linarith

/-- The exact eventual multiplier invariance used for uncentered labels. -/
theorem binLabel_eventually_mul_invariant {ι R : Type*} [Fintype ι] [CommMonoidWithZero R]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → R) {u : ℕ} (hu : u ≠ 0) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ n : ℕ,
      binLabel (fun i => primeBin x J (k i)) z (u * n) =
        binLabel (fun i => primeBin x J (k i)) z n := by
  filter_upwards [primeBin_eventually_no_factor J hJ k hk hu] with x hx n
  exact binLabel_mul_invariant _ z hu hx n


section Interpolation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem interpolationNode_mem {m : ℕ} (j : Fin m) :
    interpolationNode j ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold interpolationNode
    positivity
  · unfold interpolationNode
    apply (div_le_one (by positivity : 0 < (m : ℝ) + 1)).mpr
    exact_mod_cast Nat.succ_le_succ j.isLt.le

theorem interpolationNode_injective (m : ℕ) :
    Function.Injective (@interpolationNode m) := by
  intro a b h
  apply Fin.ext
  have hden : (m : ℝ) + 1 ≠ 0 := by positivity
  have heq : (a : ℝ) + 1 = (b : ℝ) + 1 := (div_left_inj' hden).mp h
  exact_mod_cast add_right_cancel heq

private theorem tensor_inverse_identity {m : ℕ} (v : Fin m → ℂ)
    (hv : Function.Injective v) (b t : ι → Fin m) :
    (∑ a : ι → Fin m,
      (∏ i, (Matrix.vandermonde v)⁻¹ (b i) (a i)) *
        ∏ i, v (a i) ^ ((t i : Fin m) : ℕ)) = if b = t then 1 else 0 := by
  classical
  have hinv := Matrix.nonsing_inv_mul (Matrix.vandermonde v)
    (isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hv))
  calc
    _ = ∑ a : ι → Fin m,
        ∏ i, (Matrix.vandermonde v)⁻¹ (b i) (a i) * v (a i) ^ ((t i : Fin m) : ℕ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.prod_mul_distrib]
    _ = ∏ i, ∑ a : Fin m,
        (Matrix.vandermonde v)⁻¹ (b i) a * v a ^ ((t i : Fin m) : ℕ) :=
      (Fintype.prod_sum (fun (i : ι) (a : Fin m) =>
        (Matrix.vandermonde v)⁻¹ (b i) a * v a ^ ((t i : Fin m) : ℕ))).symm
    _ = ∏ i, if b i = t i then (1 : ℂ) else 0 := by
      apply Finset.prod_congr rfl
      intro i _
      simpa only [Matrix.mul_apply, Matrix.vandermonde_apply, Matrix.one_apply] using
        congrArg (fun A : Matrix (Fin m) (Fin m) ℂ => A (b i) (t i)) hinv
    _ = _ := by
      by_cases h : b = t
      · simp [h]
      · rw [ite_eq_right h]
        obtain ⟨i, hi⟩ := Function.ne_iff.mp h
        exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Finite tensor interpolation for arbitrary tables on bounded count vectors. -/
theorem exists_bounded_count_interpolation {m : ℕ} (v : Fin m → ℝ)
    (hv : Function.Injective v) (F : (ι → Fin m) → ℂ) :
    ∃ c : (ι → Fin m) → ℂ, ∀ t : ι → Fin m,
      F t = ∑ a : ι → Fin m, c a * ∏ i, (v (a i) : ℂ) ^ ((t i : Fin m) : ℕ) := by
  classical
  let V := Matrix.vandermonde (fun j => (v j : ℂ))
  let c : (ι → Fin m) → ℂ := fun a => ∑ b : ι → Fin m,
    F b * ∏ i, V⁻¹ (b i) (a i)
  refine ⟨c, fun t => ?_⟩
  symm
  calc
    _ = ∑ b : ι → Fin m, F b *
        ∑ a : ι → Fin m, (∏ i, V⁻¹ (b i) (a i)) *
          ∏ i, (v (a i) : ℂ) ^ ((t i : Fin m) : ℕ) := by
      simp only [c, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ b : ι → Fin m, F b * (if b = t then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [show (∑ a : ι → Fin m, (∏ i, V⁻¹ (b i) (a i)) *
          ∏ i, (v (a i) : ℂ) ^ ((t i : Fin m) : ℕ)) = if b = t then 1 else 0 from
        tensor_inverse_identity (fun j => (v j : ℂ)) (Complex.ofReal_injective.comp hv) b t]
    _ = F t := by simp

/-- A centered phase label on bounded count vectors is a fixed finite linear
combination of real multiplicative interpolants with nodes in `[0,1]`. -/
theorem centered_binLabel_interpolation (ζ : ι → ℂ) (μ : ℂ) (J : ℕ) :
    ∃ c : (ι → Fin (J + 1)) → ℂ, ∀ E : ι → Finset ℕ, ∀ n : ℕ, n ≠ 0 →
      (∀ i, binCount (E i) n ≤ J) →
      binLabel E ζ n - μ = ∑ a : ι → Fin (J + 1),
        c a * (binLabel E (fun i => interpolationNode (a i)) n : ℂ) := by
  classical
  obtain ⟨c, hc⟩ := exists_bounded_count_interpolation (@interpolationNode (J + 1))
    (interpolationNode_injective _) (fun b : ι → Fin (J + 1) =>
      (∏ i, ζ i ^ ((b i : Fin (J + 1)) : ℕ)) - μ)
  refine ⟨c, fun E n hn hb => ?_⟩
  let t : ι → Fin (J + 1) := fun i => ⟨binCount (E i) n, Nat.lt_succ_of_le (hb i)⟩
  simpa only [t, binLabel_apply hn, Complex.ofReal_prod, Complex.ofReal_pow] using hc t

end Interpolation

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinCounts
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded multiplicity counts and smoothness at bin endpoints

A product of the prime powers counted in a bin divides the integer. This
bounds every bin count uniformly on fixed windows `n ≤ C*x`. The endpoint
criterion identifies smoothness with vanishing counts in all higher bins.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem mem_primeBin_iff {x : ℝ} (hx : 0 ≤ x) (J k p : ℕ) :
    p ∈ primeBin x J k ↔ p.Prime ∧
      x ^ ((k : ℝ) / J) < (p : ℝ) ∧ (p : ℝ) ≤ x ^ (((k : ℝ) + 1) / J) := by
  classical
  simp only [primeBin, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hl, hu⟩, hp⟩
    exact ⟨hp, Nat.lt_of_floor_lt hl,
      (Nat.le_floor_iff (Real.rpow_nonneg hx _)).mp hu⟩
  · rintro ⟨hp, hl, hu⟩
    exact ⟨⟨(Nat.floor_lt (Real.rpow_nonneg hx _)).mpr hl,
      (Nat.le_floor_iff (Real.rpow_nonneg hx _)).mpr hu⟩, hp⟩

/-- The product of the complete prime powers selected by a finite bin divides `n`. -/
theorem bin_primePower_prod_dvd (E : Finset ℕ) (n : ℕ) :
    (∏ p ∈ E, p ^ n.factorization p) ∣ n := by
  classical
  let f : ℕ →₀ ℕ := n.factorization.filter (fun p => p ∈ E)
  have hf : f ≤ n.factorization := by
    intro p
    simp only [f, Finsupp.filter_apply]
    split_ifs <;> simp
  have hsupp : f.support ⊆ E := by
    intro p hp
    exact (Finset.mem_filter.mp (show p ∈ n.factorization.support.filter (fun p => p ∈ E) from hp)).2
  have heq : f.prod (fun p a => p ^ a) = ∏ p ∈ E, p ^ n.factorization p := by
    rw [Finsupp.prod_of_support_subset f hsupp _ (by simp)]
    apply Finset.prod_congr rfl
    intro p hp
    simp only [f, Finsupp.filter_apply, ite_eq_left hp]
  rw [← heq]
  exact Nat.prod_pow_dvd_of_le_factorization hf

/-- A lower bound for every counted prime gives a power lower bound for `n`. -/
theorem binCount_pow_le (E : Finset ℕ) {n : ℕ} (hn : n ≠ 0)
    {q : ℝ} (hq : 0 ≤ q) (hE : ∀ p ∈ E, q ≤ (p : ℝ)) :
    q ^ binCount E n ≤ (n : ℝ) := by
  calc
    q ^ binCount E n = ∏ p ∈ E, q ^ n.factorization p :=
      (Finset.prod_pow_eq_pow_sum E n.factorization q).symm
    _ ≤ ∏ p ∈ E, (p : ℝ) ^ n.factorization p :=
      Finset.prod_le_prod (fun p _ => pow_nonneg hq _)
        (fun p hp => pow_le_pow_left₀ hq (hE p hp) _)
    _ = ((∏ p ∈ E, p ^ n.factorization p : ℕ) : ℝ) := by norm_cast
    _ ≤ n := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (bin_primePower_prod_dvd E n)

/-- Uniform boundedness of every relevant count, sufficient for interpolation.
The bound holds simultaneously for all bin indices `k ≥ 1`. -/
theorem primeBin_count_eventually_le (J : ℕ) (hJ : 0 < J) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ≤ C * x → binCount (primeBin x J k) n ≤ J := by
  have hJreal : (0 : ℝ) < J := by exact_mod_cast hJ
  have hroot := (tendsto_rpow_atTop (div_pos zero_lt_one hJreal)).eventually
    (eventually_gt_atTop C)
  filter_upwards [hroot, eventually_ge_atTop (1 : ℝ)] with x hxC hxone
  intro k hk n hn hnupper
  let q : ℝ := x ^ ((1 : ℝ) / J)
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hxone
  have hq : 1 ≤ q := Real.one_le_rpow hxone (div_nonneg zero_le_one hJreal.le)
  have hprimes : ∀ p ∈ primeBin x J k, q ≤ (p : ℝ) := by
    intro p hp
    have hl := ((mem_primeBin_iff hxpos.le J k p).mp hp).2.1
    have hexp : (1 : ℝ) / J ≤ (k : ℝ) / J :=
      div_le_div_of_nonneg_right (by exact_mod_cast hk) hJreal.le
    exact (Real.rpow_le_rpow_of_exponent_le hxone hexp).trans hl.le
  have hpow := binCount_pow_le (primeBin x J k) (by omega : n ≠ 0) (le_trans zero_le_one hq) hprimes
  have hrootpow : q ^ J = x := by
    simpa only [q, one_div] using Real.rpow_inv_natCast_pow hxpos.le (by omega : J ≠ 0)
  by_contra hcount
  have hjcount : J + 1 ≤ binCount (primeBin x J k) n := by omega
  have hmon := pow_le_pow_right₀ hq hjcount
  have hbig : C * x < q ^ (J + 1) := by
    rw [pow_succ, hrootpow]
    dsimp [q] at hxC ⊢
    nlinarith
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BinShortAverages
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The real/principal short-average estimate for the actual bin labels

Finite interpolation on fixed windows combines with the
published real short-interval input. Real multiplicative weights are allowed,
so the result includes the principal-character summands in `labels-short`.

The weighted long-mean limit remains an explicit arithmetic marginal
hypothesis. No short-average estimate, correlation statement, or independence
claim is assumed in place of it.
-/

namespace JointDickman

open Filter MeasureTheory
open scoped Topology
open PublishedInputs

theorem abs_weightedBinInterpolant_le_one {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (w : ArithmeticFunction ℝ) (hw : ∀ n, |w n| ≤ 1)
    {m : ℕ} (a : ι → Fin m) (n : ℕ) : |weightedBinInterpolant E w a n| ≤ 1 := by
  simp only [weightedBinInterpolant, ArithmeticFunction.pmul_apply, abs_mul]
  calc
    _ ≤ 1 * 1 := mul_le_mul (abs_binLabel_le_one E _ (fun i => interpolationNode_mem (a i)) n)
      (hw n) (abs_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_FinitePrimeWeight
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact divisor expansion for weights supported on finitely many primes -/
namespace JointDickman
open Finset Classical

theorem finitePrimeWeight_bounds {P : Finset ℕ} {t : ℕ → ℝ}
    (ht : ∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1) (n : ℕ) :
    0 ≤ finitePrimeWeight P t n ∧ finitePrimeWeight P t n ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  simp only [finitePrimeWeight,ArithmeticFunction.coe_mk,hn,ite_false, if_false]
  exact ⟨prod_nonneg (fun p hp => by split_ifs; exact (ht p hp).1; norm_num),
    Finset.prod_le_one (fun p hp => by split_ifs; exact (ht p hp).1; norm_num)
      (fun p hp => by split_ifs; exact (ht p hp).2; exact le_rfl)⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ComplexFiniteShortAverages
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite complex combinations of nonprincipal short averages -/
namespace JointDickman.PublishedInputs
open Finset Filter MeasureTheory
open scoped Topology

theorem measurable_complexShortAverage (f : ArithmeticFunction ℂ) (H : ℝ) :
    Measurable (complexShortAverage f H) := by
  have hm : Measurable (fun p : ℕ × ℕ => ∑ n ∈ Ioc p.1 p.2, f n) := measurable_of_countable _
  exact (hm.comp (Nat.measurable_floor.prodMk
    (measurable_id.add_const H).nat_floor)).div_const (H : ℂ)

theorem norm_complexShortAverage_le (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {H z b : ℝ} (hH : 0 < H) (hz : z ≤ b) :
    ‖complexShortAverage f H z‖ ≤ (⌊b+H⌋₊ : ℝ)/H := by
  rw [complexShortAverage,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hH]
  apply div_le_div_of_nonneg_right _ hH.le
  calc
    _ ≤ ∑ n ∈ Ioc ⌊z⌋₊ ⌊z+H⌋₊, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc ⌊z⌋₊ ⌊z+H⌋₊, (1 : ℝ) := sum_le_sum (fun n _ => hf n)
    _ = ((Ioc ⌊z⌋₊ ⌊z+H⌋₊).card : ℝ) := by simp
    _ ≤ (⌊b+H⌋₊ : ℝ) := by
      exact_mod_cast (show (Ioc ⌊z⌋₊ ⌊z+H⌋₊).card ≤ ⌊b+H⌋₊ from by
        simpa only [Nat.card_Ioc] using (Nat.sub_le ⌊z+H⌋₊ ⌊z⌋₊).trans
          (Nat.floor_mono (by linarith : z+H ≤ b+H)))

theorem complexShortAverage_sq_integrable (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {H : ℝ} (hH : 0 < H) (a b : ℝ) :
    IntervalIntegrable (fun z => ‖complexShortAverage f H z‖^2) volume a b := by
  let K : ℝ := (⌊max a b+H⌋₊ : ℝ)/H
  refine (intervalIntegrable_const (c := K^2)).mono_fun'
    (((measurable_complexShortAverage f H).norm.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with z hz
  have hh := norm_complexShortAverage_le f hf hH hz.2
  simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using
    pow_le_pow_left₀ (norm_nonneg _) hh 2

theorem complexFiniteShort_norm_sq_le {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (f : ι → ArithmeticFunction ℂ) (H z : ℝ) :
    ‖complexFiniteShort S c f H z‖^2 ≤
      (∑ i ∈ S, ‖c i‖^2)*(∑ i ∈ S, ‖complexShortAverage (f i) H z‖^2) := by
  have hn : ‖complexFiniteShort S c f H z‖ ≤ ∑ i ∈ S, ‖c i‖*‖complexShortAverage (f i) H z‖ := by
    simpa only [complexFiniteShort,norm_mul] using norm_sum_le S (fun i => c i*complexShortAverage (f i) H z)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (sum_mul_sq_le_sq_mul_sq S (fun i => ‖c i‖) (fun i => ‖complexShortAverage (f i) H z‖))

theorem complexFiniteShort_energy_le {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (f : ι → ArithmeticFunction ℂ) (hf : ∀ i ∈ S, ∀ n, ‖f i n‖ ≤ 1)
    {H X : ℝ} (hH : 0 < H) (hX : 0 < X) :
    (1/X)*(∫ z in X..2*X, ‖complexFiniteShort S c f H z‖^2) ≤
      (∑ i ∈ S, ‖c i‖^2)*∑ i ∈ S, (1/X)*(∫ z in X..2*X, ‖complexShortAverage (f i) H z‖^2) := by
  have hK : 0 ≤ ∑ i ∈ S, ‖c i‖^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hfi i hi := complexShortAverage_sq_integrable (f i) (hf i hi) hH X (2*X)
  have hsum : IntervalIntegrable (fun z => (∑ i ∈ S, ‖c i‖^2)*
      ∑ i ∈ S, ‖complexShortAverage (f i) H z‖^2) volume X (2*X) := by
    simpa only [Finset.sum_apply] using (IntervalIntegrable.sum S hfi).const_mul (∑ i ∈ S, ‖c i‖^2)
  have hc : IntervalIntegrable (fun z => ‖complexFiniteShort S c f H z‖^2) volume X (2*X) := by
    apply hsum.mono_fun'
    · exact ((Finset.measurable_sum S (fun i _ =>
        (measurable_complexShortAverage (f i) H).const_mul (c i))).norm.pow_const 2).aestronglyMeasurable
    · exact Eventually.of_forall (fun z => by
        simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using complexFiniteShort_norm_sq_le S c f H z)
  have hi := intervalIntegral.integral_mono (by linarith : X ≤ 2*X) hc hsum
    (complexFiniteShort_norm_sq_le S c f H)
  have hh := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1/X)
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum hfi] at hh
  simpa only [mul_sum,mul_assoc,mul_left_comm (1/X)] using hh

end JointDickman.PublishedInputs

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinShortComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocal weights in a short interval

Replacing the counting weight by `x/n` costs at most `(H+1)/x` in a
one-bounded short average. This is the elementary bridge to logarithmic
windows; the bound is uniform in the coefficients.
-/
namespace JointDickman
open Finset PublishedInputs

theorem mellin_short_interval_card_le {x H : ℝ} (hx : 0 ≤ x) (hH : 0 ≤ H) :
    ((Ioc ⌊x⌋₊ ⌊x + H⌋₊).card : ℝ) ≤ H + 1 := by
  have hfloor : ⌊x⌋₊ ≤ ⌊x + H⌋₊ := Nat.floor_mono (by linarith)
  rw [Nat.card_Ioc, Nat.cast_sub hfloor]
  have hl := Nat.lt_floor_add_one x
  have hu := Nat.floor_le (show 0 ≤ x + H by linarith)
  have hl' : x < (⌊x⌋₊ : ℝ) + 1 := hl
  linarith

/-- The reciprocal-weight normalization has a vanishing error whenever
`H/x` and `1/x` tend to zero. -/
theorem short_average_reciprocal_error (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {x H : ℝ} (hx : 0 < x) (hH : 0 < H) :
    ‖complexShortAverage f H x - reciprocalShortAverage f H x‖ ≤ (H + 1) / x := by
  let S := Ioc ⌊x⌋₊ ⌊x + H⌋₊
  have hn (n : ℕ) (hn : n ∈ S) : x < (n : ℝ) ∧ (n : ℝ) ≤ x + H := by
    obtain ⟨hl, hu⟩ := mem_Ioc.mp hn
    exact ⟨Nat.lt_of_floor_lt hl, (Nat.le_floor_iff (by linarith : 0 ≤ x + H)).mp hu⟩
  have hweight (n : ℕ) (hnS : n ∈ S) : |1 - x / (n : ℝ)| ≤ H / x := by
    have hn' := hn n hnS
    have hn0 : (0 : ℝ) < n := hx.trans hn'.1
    have hratio : x / (n : ℝ) ≤ 1 := (div_le_one hn0).mpr hn'.1.le
    rw [abs_of_nonneg (by linarith)]
    apply (le_div_iff₀ hx).mpr
    have hdiv := (div_mul_cancel₀ x hn0.ne')
    have hh : (1 - x / (n : ℝ)) * x ≤ H := by
      have hsmall : (1 - x / (n : ℝ)) * x ≤
          (1 - x / (n : ℝ)) * n :=
        mul_le_mul_of_nonneg_left hn'.1.le (by linarith)
      nlinarith
    exact hh
  have heq : complexShortAverage f H x - reciprocalShortAverage f H x =
      (∑ n ∈ S, ((1 - x / (n : ℝ) : ℝ) : ℂ) * f n) / (H : ℂ) := by
    unfold complexShortAverage reciprocalShortAverage
    rw [← sub_div, mul_sum, ← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro n _
    push_cast
    ring
  rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  have hs : ‖∑ n ∈ S, ((1 - x / (n : ℝ) : ℝ) : ℂ) * f n‖ ≤
      (S.card : ℝ) * (H / x) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _n ∈ S, H / x := by
        apply sum_le_sum
        intro n hnS
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_mul (hweight n hnS) (hf n) (norm_nonneg _) (by positivity)).trans_eq
          (mul_one _)
      _ = _ := by simp
  calc
    _ ≤ ((S.card : ℝ) * (H / x)) / H :=
      div_le_div_of_nonneg_right hs hH.le
    _ = (S.card : ℝ) / x := by field_simp [hH.ne', hx.ne']
    _ ≤ (H + 1) / x := div_le_div_of_nonneg_right (mellin_short_interval_card_le hx.le hH.le) hx.le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LogarithmicBoundaryWidths
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two transition strips of a smooth logarithmic window -/
namespace JointDickman
open Finset

theorem logarithmic_boundary_widths {x η δ : ℝ} (hx : 0 ≤ x)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    x * (Real.exp (η * δ) - 1) ≤ 2 * η * δ * x ∧
      x * Real.exp δ - x * Real.exp ((1 - η) * δ) ≤ 6 * η * δ * x := by
  have ht : 0 ≤ η * δ := mul_nonneg hη hδ
  have ht1 : η * δ ≤ 1 := (mul_le_mul hη1 hδ1 hδ (by norm_num)).trans_eq (one_mul 1)
  have hp := Real.abs_exp_sub_one_le (show |η * δ| ≤ 1 by rwa [abs_of_nonneg ht])
  have hm := Real.abs_exp_sub_one_le (show |-(η * δ)| ≤ 1 by simpa only [abs_neg, abs_of_nonneg ht] using ht1)
  have hlo : Real.exp (η * δ) - 1 ≤ 2 * η * δ := by
    rw [abs_of_nonneg ht] at hp
    exact (le_abs_self _).trans (by simpa only [mul_assoc] using hp)
  have hhi : 1 - Real.exp (-(η * δ)) ≤ 2 * η * δ := by
    rw [abs_neg, abs_of_nonneg ht] at hm
    have hh := (neg_le_abs (Real.exp (-(η * δ)) - 1)).trans hm
    linarith
  have hexp : Real.exp δ ≤ 3 :=
    (Real.exp_le_exp.mpr hδ1).trans Real.exp_one_lt_three.le
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hlo hx]
  · have he : Real.exp ((1 - η) * δ) = Real.exp δ * Real.exp (-(η * δ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    have hmul := mul_le_mul_of_nonneg_left hhi (mul_nonneg hx (Real.exp_pos δ).le)
    have hcap := mul_le_mul_of_nonneg_right hexp (mul_nonneg hx ht)
    nlinarith

lemma nat_interval_card_le_length {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ((Ioc ⌊a⌋₊ ⌊b⌋₊).card : ℝ) ≤ b - a + 1 := by
  have he : a + (b - a) = b := by ring
  simpa only [he] using mellin_short_interval_card_le ha (sub_nonneg.mpr hab)

theorem logarithmic_boundary_card {x η δ : ℝ} (hx : 0 ≤ x)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ((Ioc ⌊x⌋₊ ⌊x * Real.exp (η * δ)⌋₊).card : ℝ) +
      ((Ioc ⌊x * Real.exp ((1 - η) * δ)⌋₊ ⌊x * Real.exp δ⌋₊).card : ℝ) ≤
        8 * η * δ * x + 2 := by
  have hlo : x ≤ x * Real.exp (η * δ) := by
    have hh : 1 ≤ Real.exp (η * δ) := Real.one_le_exp_iff.mpr (mul_nonneg hη hδ)
    nlinarith
  have hhi : x * Real.exp ((1 - η) * δ) ≤ x * Real.exp δ := by
    apply mul_le_mul_of_nonneg_left _ hx
    apply Real.exp_le_exp.mpr
    nlinarith
  have hcount1 := nat_interval_card_le_length hx hlo
  have hcount2 := nat_interval_card_le_length
    (mul_nonneg hx (Real.exp_pos _).le) hhi
  obtain ⟨hw1, hw2⟩ := logarithmic_boundary_widths hx hη hη1 hδ hδ1
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_OscillatoryTests
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth oscillatory tests used in the coefficient estimate -/

namespace JointDickman

theorem norm_additivePhase (x : ℝ) : ‖additivePhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem hasDerivAt_additivePhase (x : ℝ) :
    HasDerivAt additivePhase (additivePhase x * ((2 * Real.pi : ℝ) * Complex.I)) x := by
  have h := (((hasDerivAt_id x).const_mul (2 * Real.pi)).ofReal_comp.mul_const Complex.I).cexp
  simpa only [mul_one, id_eq] using! h

theorem continuous_additivePhase : Continuous additivePhase :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_additivePhase x).continuousAt)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinPackets
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

/-! # Smoothed logarithmic windows and their Dirichlet energy

A finite sum of translates of a Schwartz window is itself Schwartz. Its
Fourier transform factors into the window transform and the actual finite
Dirichlet polynomial. Plancherel therefore identifies the two energies
without a truncation or an arithmetic hypothesis.
-/
namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap FourierTransform

theorem mellinPacket_apply (S : Finset ℕ) (a : ℕ → ℂ) (w : 𝓢(ℝ, ℂ)) (v : ℝ) :
    mellinPacket S a w v =
      ∑ n ∈ S, (a n / (n : ℂ)) * w (v - Real.log (n : ℝ)) := by
  simp [mellinPacket, smul_eq_mul]

theorem fourier_schwartz_translate (w : 𝓢(ℝ, ℂ)) (u ξ : ℝ) :
    (𝓕 (w.compSubConstCLM ℂ u) : 𝓢(ℝ, ℂ)) ξ =
      additivePhase (-ξ * u) * (𝓕 w : 𝓢(ℝ, ℂ)) ξ := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  change (∫ v : ℝ, Real.fourierChar (-(v * ξ)) • w (v - u)) = _
  rw [← integral_add_right_eq_self (fun v : ℝ =>
    Real.fourierChar (-(v * ξ)) • w (v - u)) u]
  simp only [add_sub_cancel_right]
  have hphase (v : ℝ) : Real.fourierChar (-((v + u) * ξ)) =
      Real.fourierChar (-(u * ξ)) * Real.fourierChar (-(v * ξ)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hphase, Circle.smul_def, Circle.coe_mul, smul_eq_mul, mul_assoc]
  rw [integral_const_mul]
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  have he : (Real.fourierChar (-(u * ξ)) : ℂ) = additivePhase (-ξ * u) := by
    simp only [Real.fourierChar_apply, additivePhase]
    congr 1
    push_cast
    ring
  simp only [Circle.smul_def, he, smul_eq_mul]

theorem mellinPacket_fourier (S : Finset ℕ) (a : ℕ → ℂ) (w : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    (𝓕 (mellinPacket S a w) : 𝓢(ℝ, ℂ)) ξ =
      (𝓕 w : 𝓢(ℝ, ℂ)) ξ * mellinPolynomial S a ξ := by
  change (SchwartzMap.fourierTransformCLM ℂ (mellinPacket S a w)) ξ = _
  simp only [mellinPacket, map_sum, map_smul, SchwartzMap.fourierTransformCLM_apply,
    _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
    fourier_schwartz_translate, mellinPolynomial, mul_sum]
  apply sum_congr rfl
  intro n _
  ring

/-- Exact Plancherel transfer for the smoothed logarithmic window. -/
theorem mellinPacket_energy (S : Finset ℕ) (a : ℕ → ℂ) (w : 𝓢(ℝ, ℂ)) :
    (∫ v : ℝ, ‖mellinPacket S a w v‖ ^ 2) =
      ∫ ξ : ℝ, ‖(𝓕 w : 𝓢(ℝ, ℂ)) ξ‖ ^ 2 * ‖mellinPolynomial S a ξ‖ ^ 2 := by
  rw [← SchwartzMap.integral_norm_sq_fourier (mellinPacket S a w)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ξ => by
    dsimp only
    rw [mellinPacket_fourier, norm_mul, mul_pow])

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinPacketScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized logarithmic windows at a prescribed scale -/
namespace JointDickman
open MeasureTheory
open scoped SchwartzMap FourierTransform

theorem normalizedSchwartzScale_apply (w : 𝓢(ℝ, ℂ)) {δ : ℝ} (hδ : 0 < δ) (v : ℝ) :
    normalizedSchwartzScale w δ hδ v = w (v / δ) / (δ : ℂ) := by
  simp only [normalizedSchwartzScale, smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.unitsEquivAut_apply_symm, Units.val_inv_eq_inv_val,
    Units.val_mk0, smul_eq_mul, div_eq_mul_inv]
  ring

/-- The normalization removes the scale factor in the Fourier transform. -/
theorem normalizedSchwartzScale_fourier (w : 𝓢(ℝ, ℂ)) {δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    (𝓕 (normalizedSchwartzScale w δ hδ) : 𝓢(ℝ, ℂ)) ξ =
      (𝓕 w : 𝓢(ℝ, ℂ)) (δ * ξ) := by
  let F : ℝ → ℂ := fun v =>
    Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I) * w (v / δ)
  have hchange := Measure.integral_comp_mul_left F δ
  have hpoint (v : ℝ) : F (δ * v) =
      Complex.exp (((-2 * Real.pi * v * (δ * ξ) : ℝ) : ℂ) * Complex.I) * w v := by
    dsimp [F]
    rw [mul_div_cancel_left₀ v hδ.ne']
    congr 2
    push_cast
    ring
  have hfactor : (|δ⁻¹| : ℝ) = δ⁻¹ := abs_of_pos (inv_pos.mpr hδ)
  simp_rw [hpoint] at hchange
  rw [hfactor] at hchange
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul,
    SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = (δ : ℂ)⁻¹ * ∫ v : ℝ, F v := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun v => by
        dsimp only
        rw [normalizedSchwartzScale_apply]
        dsimp [F]
        ring)
    _ = _ := by
      simpa only [smul_eq_mul, Complex.real_smul, Complex.ofReal_inv] using hchange.symm

/-- The exact energy identity at the short logarithmic scale `δ`. -/
theorem scaled_mellinPacket_energy (S : Finset ℕ) (a : ℕ → ℂ)
    (w : 𝓢(ℝ, ℂ)) {δ : ℝ} (hδ : 0 < δ) :
    (∫ v : ℝ, ‖mellinPacket S a (normalizedSchwartzScale w δ hδ) v‖ ^ 2) =
      ∫ ξ : ℝ, ‖(𝓕 w : 𝓢(ℝ, ℂ)) (δ * ξ)‖ ^ 2 *
        ‖mellinPolynomial S a ξ‖ ^ 2 := by
  rw [mellinPacket_energy]
  simp only [normalizedSchwartzScale_fourier]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinSpectralWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summable unit-interval bounds for a Schwartz spectral weight -/
namespace JointDickman
open scoped SchwartzMap

/-- A fixed Schwartz window has a summable quadratic Fourier majorant on
unit intervals. This will weight the local Dirichlet mean-square estimates. -/
theorem schwartz_cell_norm_sq_bound (w : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ) (u : ℝ), (n : ℝ) ≤ u → u ≤ n + 1 →
      ‖w u‖ ^ 2 ≤ C / (1 + |(n : ℝ)|) ^ 4 := by
  let C := 2 * (SchwartzMap.seminorm ℝ 0 0 w + SchwartzMap.seminorm ℝ 2 0 w) + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨16 * C ^ 2, by positivity, ?_⟩
  intro n u hnu hun
  have h0 := SchwartzMap.norm_le_seminorm ℝ w u
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ w 2 u
  rw [Real.norm_eq_abs] at h2
  have hw : (1 + |u|) ^ 2 * ‖w u‖ ≤ C := by
    have hh := mul_nonneg (sq_nonneg (|u| - 1)) (norm_nonneg (w u))
    dsimp [C]
    nlinarith
  have hnu' : |(n : ℝ)| ≤ |u| + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self u, neg_abs_le u]
  have hq : 0 < 1 + |(n : ℝ)| := by positivity
  have hrel : (1 + |(n : ℝ)|) ^ 2 ≤ (2 * (1 + |u|)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg u]) 2
  have hprod : (1 + |(n : ℝ)|) ^ 2 * ‖w u‖ ≤ 4 * C := by
    have hh := mul_le_mul_of_nonneg_right hrel (norm_nonneg (w u))
    nlinarith
  have hs := pow_le_pow_left₀
    (mul_nonneg (sq_nonneg (1 + |(n : ℝ)|)) (norm_nonneg (w u))) hprod 2
  apply (le_div_iff₀ (pow_pos hq 4)).mpr
  first | (convert hs using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hs.trans (le_of_eq (by ring)))

lemma summable_integer_window_weights :
    Summable (fun n : ℤ => 1 / (1 + |(n : ℝ)|) ^ 3) := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have ht := (summable_nat_add_iff 1).mpr hs
  apply Summable.of_nat_of_neg
  · apply ht.congr
    intro n
    simp only [Int.cast_natCast, Nat.cast_add, Nat.cast_one,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), add_comm]
  · apply ht.congr
    intro n
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.cast_add, Nat.cast_one,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), add_comm]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinWeightedEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From interval Dirichlet energies to a Schwartz weighted energy -/
namespace JointDickman
open MeasureTheory
open scoped SchwartzMap

/-- The constant depends only on the fixed Schwartz window. A bound linear
in the frequency cutoff gives a finite weighted energy, without a logarithmic
loss from the number of frequency intervals. -/
theorem schwartz_weighted_energy_bound (w : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ → ℂ), Continuous F → ∀ A B : ℝ,
      0 ≤ A → 0 ≤ B →
      Integrable (fun t : ℝ => ‖w t‖ ^ 2 * ‖F t‖ ^ 2) →
      (∀ T : ℝ, 1 ≤ T → (∫ t in -T..T, ‖F t‖ ^ 2) ≤ A + B * T) →
      (∫ t : ℝ, ‖w t‖ ^ 2 * ‖F t‖ ^ 2) ≤ C * (A + B) := by
  obtain ⟨K, hK, hweight⟩ := schwartz_cell_norm_sq_bound w
  let W : ℝ := ∑' n : ℤ, 1 / (1 + |(n : ℝ)|) ^ 3
  have hW : 0 ≤ W := tsum_nonneg (fun _ => by positivity)
  refine ⟨2 * K * W + 1, by positivity, ?_⟩
  intro F hF A B hA hB hI henergy
  let G : ℝ → ℝ := fun t => ‖w t‖ ^ 2 * ‖F t‖ ^ 2
  have hG : Continuous G := (w.continuous.norm.pow 2).mul (hF.norm.pow 2)
  have hcell (n : ℤ) :
      (∫ t in (n : ℝ)..n + 1, G t) ≤
        (2 * K * (A + B)) * (1 / (1 + |(n : ℝ)|) ^ 3) := by
    let q : ℝ := 1 + |(n : ℝ)|
    let T : ℝ := |(n : ℝ)| + 2
    have hq : 0 < q := by dsimp [q] <;> linarith [abs_nonneg (n : ℝ)]
    have hT : 1 ≤ T := by dsimp [T] <;> linarith [abs_nonneg (n : ℝ)]
    have hnT : -T ≤ (n : ℝ) := by dsimp [T] <;> linarith [neg_abs_le (n : ℝ)]
    have hnT' : (n : ℝ) + 1 ≤ T := by dsimp [T] <;> linarith [le_abs_self (n : ℝ)]
    have hmean : (∫ t in (n : ℝ)..n + 1, ‖F t‖ ^ 2) ≤ A + B * T :=
      (intervalIntegral.integral_mono_interval hnT (by linarith) hnT'
        (Filter.Eventually.of_forall (fun t => sq_nonneg ‖F t‖))
        ((hF.norm.pow 2).intervalIntegrable (-T) T)).trans (henergy T hT)
    have hlinear : A + B * T ≤ 2 * (A + B) * q := by
      have hq1 : 1 ≤ q := by dsimp [q] <;> linarith [abs_nonneg (n : ℝ)]
      have hAq := mul_le_mul_of_nonneg_left hq1 hA
      have hBq := mul_le_mul_of_nonneg_left hq1 hB
      dsimp [q, T] at *
      nlinarith
    calc
      _ ≤ ∫ t in (n : ℝ)..n + 1, (K / q ^ 4) * ‖F t‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on (by linarith)
          (hG.intervalIntegrable _ _) ((continuous_const.mul (hF.norm.pow 2)).intervalIntegrable _ _)
        intro t ht
        exact mul_le_mul_of_nonneg_right (hweight n t ht.1 ht.2) (sq_nonneg _)
      _ = (K / q ^ 4) * (∫ t in (n : ℝ)..n + 1, ‖F t‖ ^ 2) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ (K / q ^ 4) * (A + B * T) :=
        mul_le_mul_of_nonneg_left hmean (by positivity)
      _ ≤ (K / q ^ 4) * (2 * (A + B) * q) :=
        mul_le_mul_of_nonneg_left hlinear (by positivity)
      _ = _ := by dsimp [q]; field_simp
  have hsum := hI.hasSum_intervalIntegral 0
  have hsum' : HasSum (fun n : ℤ => ∫ t in (n : ℝ)..n + 1, G t) (∫ t, G t) := by
    simpa only [zero_add] using hsum
  have hmajor := summable_integer_window_weights.mul_left (2 * K * (A + B))
  calc
    _ = ∑' n : ℤ, ∫ t in (n : ℝ)..n + 1, G t := hsum'.tsum_eq.symm
    _ ≤ ∑' n : ℤ, (2 * K * (A + B)) * (1 / (1 + |(n : ℝ)|) ^ 3) :=
      hsum'.summable.tsum_le_tsum hcell hmajor
    _ = (2 * K * (A + B)) * W := tsum_mul_left
    _ ≤ (2 * K * W + 1) * (A + B) := by nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinEnergyTransfer
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scaled transfer of Dirichlet mean-square estimates to short windows -/
namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap FourierTransform

theorem continuous_mellinPolynomial (S : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (mellinPolynomial S a) := by
  apply continuous_finsetSum
  intro n _
  exact continuous_const.mul
    (continuous_additivePhase.comp (continuous_id.neg.mul_const _))

/-- A Dirichlet energy bound `A+B*T` gives the expected short-window cost
`A+B/δ`, with a constant depending only on the smoothing profile. -/
theorem mellinPacket_energy_of_spectral_bound (w : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (a : ℕ → ℂ)
      (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      (∀ T : ℝ, 1 ≤ T →
        (∫ t in -T..T, ‖mellinPolynomial S a t‖ ^ 2) ≤ A + B * T) →
      (∫ v : ℝ, ‖mellinPacket S a (normalizedSchwartzScale w δ hδ) v‖ ^ 2) ≤
        C * (A + B / δ) := by
  obtain ⟨C, hC, hCbound⟩ := schwartz_weighted_energy_bound (𝓕 w : 𝓢(ℝ, ℂ))
  refine ⟨C, hC, ?_⟩
  intro S a δ hδ hδ1 A B hA hB henergy
  let D := mellinPolynomial S a
  let F : ℝ → ℂ := fun u => D (u / δ)
  let G : ℝ → ℝ := fun t => ‖(𝓕 w : 𝓢(ℝ, ℂ)) (δ * t)‖ ^ 2 * ‖D t‖ ^ 2
  let p := mellinPacket S a (normalizedSchwartzScale w δ hδ)
  have hF : Continuous F := (continuous_mellinPolynomial S a).comp (continuous_id.div_const δ)
  have hi : Integrable G := by
    have hp := ((𝓕 p : 𝓢(ℝ, ℂ)).memLp 2).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    apply hp.congr
    filter_upwards [] with t
    dsimp only [G, p, D]
    rw [mellinPacket_fourier, normalizedSchwartzScale_fourier, norm_mul, mul_pow]
  have hscaledI : Integrable (fun u : ℝ =>
      ‖(𝓕 w : 𝓢(ℝ, ℂ)) u‖ ^ 2 * ‖F u‖ ^ 2) := by
    apply (hi.comp_div hδ.ne').congr
    filter_upwards [] with u
    dsimp only [G, F]
    rw [mul_div_cancel₀ u hδ.ne']
  have hscaled : ∀ T : ℝ, 1 ≤ T →
      (∫ u in -T..T, ‖F u‖ ^ 2) ≤ δ * A + B * T := by
    intro T hT
    have hTδ : 1 ≤ T / δ := (le_div_iff₀ hδ).mpr (by linarith)
    change (∫ u in -T..T, ‖D (u / δ)‖ ^ 2) ≤ _
    rw [intervalIntegral.integral_comp_div (fun u => ‖D u‖ ^ 2) hδ.ne']
    simp only [smul_eq_mul, neg_div]
    calc
      _ ≤ δ * (A + B * (T / δ)) := mul_le_mul_of_nonneg_left (henergy _ hTδ) hδ.le
      _ = _ := by field_simp
  have hb := hCbound F hF (δ * A) B (mul_nonneg hδ.le hA) hB hscaledI hscaled
  have hchange : (∫ u : ℝ, ‖(𝓕 w : 𝓢(ℝ, ℂ)) u‖ ^ 2 * ‖F u‖ ^ 2) =
      δ * ∫ t : ℝ, G t := by
    have hh := Measure.integral_comp_div G δ
    simpa only [G, F, mul_div_cancel₀ _ hδ.ne', abs_of_pos hδ, smul_eq_mul] using hh
  rw [scaled_mellinPacket_energy]
  change (∫ t : ℝ, G t) ≤ _
  calc
    _ = (∫ u : ℝ, ‖(𝓕 w : 𝓢(ℝ, ℂ)) u‖ ^ 2 * ‖F u‖ ^ 2) / δ := by
      rw [hchange, mul_div_cancel_left₀ _ hδ.ne']
    _ ≤ (C * (δ * A + B)) / δ := div_le_div_of_nonneg_right hb hδ.le
    _ = _ := by field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinAngularEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Angular-frequency normalization for the published Dirichlet estimates -/
namespace JointDickman
open Finset MeasureTheory

theorem mellinPolynomial_eq_angular (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    mellinPolynomial S a t = angularMellinPolynomial S a (2 * Real.pi * t) := by
  unfold mellinPolynomial angularMellinPolynomial
  apply sum_congr rfl
  intro n _
  congr 1
  unfold additivePhase
  congr 1
  push_cast
  ring

/-- Changing from angular to Fourier frequency preserves a linear spectral
bound, since the constant term is reduced by the factor `2*pi`. -/
theorem mellinPolynomial_energy_of_angular (S : Finset ℕ) (a : ℕ → ℂ)
    {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hbound : ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖angularMellinPolynomial S a t‖ ^ 2) ≤ A + B * T) :
    ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖mellinPolynomial S a t‖ ^ 2) ≤ A + B * T := by
  intro T hT
  have hp : 0 < 2 * Real.pi := by positivity
  have hp1 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hTp : 1 ≤ 2 * Real.pi * T := by nlinarith
  simp_rw [mellinPolynomial_eq_angular]
  rw [intervalIntegral.integral_comp_mul_left (f := fun t => ‖angularMellinPolynomial S a t‖ ^ 2) hp.ne']
  simp only [smul_eq_mul, mul_neg]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (A + B * (2 * Real.pi * T)) :=
      mul_le_mul_of_nonneg_left (hbound _ hTp) (inv_nonneg.mpr hp.le)
    _ = A / (2 * Real.pi) + B * T := by field_simp
    _ ≤ A + B * T := add_le_add (div_le_self hA hp1) le_rfl

theorem angularMellinPolynomial_consecutive (a : ℕ → ℂ) {K L N : ℕ}
    (hKL : K ≤ L) (hLN : L ≤ N) (t : ℝ) :
    angularMellinPolynomial (Ioc K N) a t =
      angularMellinPolynomial (Ioc K L) a t + angularMellinPolynomial (Ioc L N) a t := by
  unfold angularMellinPolynomial
  rw [← Ioc_union_Ioc_eq_Ioc hKL hLN, sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]

/-- Only two dyadic spectral bounds are needed for the entire coefficient
range used by the short-window transfer. -/
theorem mellinPolynomial_two_dyadic_energy (a : ℕ → ℂ) (N : ℕ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfirst : ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2 * N)) a t‖ ^ 2) ≤ A + B * T)
    (hsecond : ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc (2 * N) (4 * N)) a t‖ ^ 2) ≤ A + B * T) :
    ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖mellinPolynomial (Ioc N (4 * N)) a t‖ ^ 2) ≤ 4 * A + (4 * B) * T := by
  apply mellinPolynomial_energy_of_angular _ _ (by positivity) (by positivity)
  intro T hT
  have hc (S : Finset ℕ) : Continuous (angularMellinPolynomial S a) := by
    apply continuous_finsetSum
    intro n _
    exact continuous_const.mul (Complex.continuous_exp.comp
      (((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))).mul_const Complex.I))
  have hp (t : ℝ) : ‖angularMellinPolynomial (Ioc N (4 * N)) a t‖ ^ 2 ≤
      2 * ‖angularMellinPolynomial (Ioc N (2 * N)) a t‖ ^ 2 +
        2 * ‖angularMellinPolynomial (Ioc (2 * N) (4 * N)) a t‖ ^ 2 := by
    rw [angularMellinPolynomial_consecutive a (by omega : N ≤ 2 * N) (by omega : 2 * N ≤ 4 * N)]
    have hh := norm_add_le (angularMellinPolynomial (Ioc N (2 * N)) a t)
      (angularMellinPolynomial (Ioc (2 * N) (4 * N)) a t)
    nlinarith [norm_nonneg (angularMellinPolynomial (Ioc N (2 * N)) a t),
      norm_nonneg (angularMellinPolynomial (Ioc (2 * N) (4 * N)) a t),
      norm_nonneg (angularMellinPolynomial (Ioc N (2 * N)) a t + angularMellinPolynomial (Ioc (2 * N) (4 * N)) a t),
      sq_nonneg (‖angularMellinPolynomial (Ioc N (2 * N)) a t‖ -
        ‖angularMellinPolynomial (Ioc (2 * N) (4 * N)) a t‖)]
  have hI (S : Finset ℕ) : IntervalIntegrable
      (fun t => ‖angularMellinPolynomial S a t‖ ^ 2) volume (-T) T :=
    ((hc S).norm.pow 2).intervalIntegrable _ _
  have hi := intervalIntegral.integral_mono (by linarith : -T ≤ T)
    (hI _) (((hI _).const_mul 2).add ((hI _).const_mul 2)) hp
  rw [intervalIntegral.integral_add ((hI _).const_mul 2) ((hI _).const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  nlinarith [hfirst T hT, hsecond T hT]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinLowFrequency
attribute [-instance] _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unconditional low-frequency control of the actual weighted bin labels -/
namespace JointDickman
open Finset Filter
open scoped Topology

lemma norm_binLabel_le_one_of_norm_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (n : ℕ) :
    ‖binLabel E z n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [binLabel_apply hn, norm_prod]
    apply Finset.prod_le_one
    · intro i _
      exact norm_nonneg _
    · intro i _
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hz i)

lemma centeredWeightedBinCoefficient_norm {J : ℕ} (ζ : Fin (J-1) → ℂ)
    (hζ : ∀ i, ‖ζ i‖ ≤ 1) {μ : ℂ} (hμ : ‖μ‖ ≤ 1)
    {P : Finset ℕ} (t : ℕ → ℝ) (ht : ∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1)
    (x : ℝ) (n : ℕ) : ‖centeredWeightedBinCoefficient J ζ μ P t x n‖ ≤ 2 := by
  change ‖(binLabel _ ζ n - μ) * (finitePrimeWeight P t n : ℂ)‖ ≤ 2
  have hl : ‖binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ n - μ‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [norm_binLabel_le_one_of_norm_le (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ hζ n])
  have hw : ‖(finitePrimeWeight P t n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (finitePrimeWeight_bounds ht n).1]
    exact (finitePrimeWeight_bounds ht n).2
  rw [norm_mul]
  exact (mul_le_mul hl hw (norm_nonneg _) (by norm_num)).trans_eq (mul_one 2)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PeriodicAverages
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite periodic averages and coprime residue factorization

Integer averages of a function on `ZMod q` converge to its uniform residue
mean. The proof is the exact complete-block/remainder identity. The Chinese
remainder equivalence then gives factorization for fixed coprime moduli.
-/

namespace JointDickman

open Filter
open scoped Topology BigOperators

theorem residue_sum_eq_range {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ a : ZMod q, f a) = ∑ n ∈ Finset.range q, f (n : ZMod q) := by
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  exact Fintype.sum_equiv (residueEquiv q) _ _ (fun _ => rfl)

/-- Complete blocks have exactly the same sum, with an unaltered final
prefix. This equality also holds when the modulus is zero. -/
theorem periodic_sum_blocks {q : ℕ} (f : ZMod q → ℂ) (k r : ℕ) :
    (∑ n ∈ Finset.range (k * q + r), f (n : ZMod q)) =
      (k : ℂ) * (∑ n ∈ Finset.range q, f (n : ZMod q)) +
        ∑ n ∈ Finset.range r, f (n : ZMod q) := by
  have hshift (k n : ℕ) : f ((k * q + n : ℕ) : ZMod q) = f (n : ZMod q) := by
    simp
  have hblocks : ∀ k : ℕ, (∑ n ∈ Finset.range (k * q), f (n : ZMod q)) =
      (k : ℂ) * (∑ n ∈ Finset.range q, f (n : ZMod q)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add,
        Nat.cast_one]
      ring
  rw [Finset.sum_range_add, hblocks]
  simp only [hshift]

theorem periodic_sum_div_mod {q : ℕ} (f : ZMod q → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, f (n : ZMod q)) =
      (N / q : ℕ) * (∑ n ∈ Finset.range q, f (n : ZMod q)) +
        ∑ n ∈ Finset.range (N % q), f (n : ZMod q) := by
  have hsplit : N / q * q + N % q = N := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod N q
  simpa only [hsplit] using periodic_sum_blocks f (N / q) (N % q)

private theorem prefix_centered_bound {q r : ℕ} (hq : 0 < q) (hr : r ≤ q)
    (F : ℕ → ℂ) {M : ℝ} (hF : ∀ i < q, ‖F i‖ ≤ M) :
    ‖(∑ i ∈ Finset.range r, F i) -
      ((r : ℂ) / q) * ∑ i ∈ Finset.range q, F i‖ ≤ q * M := by
  classical
  have hprefix : (∑ i ∈ Finset.range r, F i) =
      ∑ i ∈ Finset.range q, if i < r then F i else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_range, Finset.mem_filter]
    omega
  have hid : (∑ i ∈ Finset.range r, F i) -
      ((r : ℂ) / q) * ∑ i ∈ Finset.range q, F i =
      ∑ i ∈ Finset.range q, ((if i < r then (1 : ℂ) else 0) - (r : ℂ) / q) * F i := by
    rw [hprefix, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  rw [hid]
  refine (norm_sum_le _ _).trans ?_
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hquot0 : 0 ≤ (r : ℝ) / q := div_nonneg (Nat.cast_nonneg _) hqR.le
  have hquot1 : (r : ℝ) / q ≤ 1 := (div_le_one hqR).mpr (by exact_mod_cast hr)
  calc
    _ ≤ ∑ i ∈ Finset.range q, M := by
      apply Finset.sum_le_sum
      intro i hi
      have hcoef : ‖(if i < r then (1 : ℂ) else 0) - (r : ℂ) / q‖ ≤ 1 := by
        have hcast : (r : ℂ) / q = (((r : ℝ) / q : ℝ) : ℂ) := by push_cast; rfl
        rw [hcast]
        split_ifs
        · rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          linarith
        · simp only [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hquot0]
          exact hquot1
      rw [norm_mul]
      exact (mul_le_mul hcoef (hF i (Finset.mem_range.mp hi)) (norm_nonneg _) (by norm_num)).trans
        (by simp)
    _ = q * M := by simp

/-- The remainder error is at most one period times the uniform norm,
divided by the averaging length. -/
theorem periodicAverage_error {q : ℕ} [NeZero q] (f : ZMod q → ℂ)
    {N : ℕ} (hN : 0 < N) :
    ‖periodicAverage f N - residueMean f‖ ≤ (q : ℝ) * ‖f‖ / N := by
  have hq : 0 < q := NeZero.pos q
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hid : periodicAverage f N - residueMean f =
      ((∑ i ∈ Finset.range (N % q), f (i : ZMod q)) -
        ((N % q : ℕ) : ℂ) / q * ∑ i ∈ Finset.range q, f (i : ZMod q)) / N := by
    unfold periodicAverage residueMean
    rw [residue_sum_eq_range, periodic_sum_div_mod]
    have hdecomp : (N : ℂ) = ((N / q : ℕ) : ℂ) * q + (N % q : ℕ) := by
      exact_mod_cast (by simpa only [Nat.mul_comm] using (Nat.div_add_mod N q).symm :
        N = N / q * q + N % q)
    field_simp
    linear_combination -(∑ i ∈ Finset.range q, f (i : ZMod q)) * hdecomp
  rw [hid, norm_div]
  have hprefix := prefix_centered_bound hq (Nat.mod_lt N hq).le
    (fun i => f (i : ZMod q)) (fun i _ => norm_le_pi_norm f _)
  have hnormN : ‖(N : ℂ)‖ = (N : ℝ) := by simp
  rw [hnormN]
  exact div_le_div_of_nonneg_right hprefix (Nat.cast_nonneg _)

theorem periodicAverage_tendsto {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    Tendsto (periodicAverage f) atTop (𝓝 (residueMean f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun N : ℕ => (q : ℝ) * ‖f‖ / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    ((eventually_gt_atTop 0).mono (fun N hN => periodicAverage_error f hN)) hlim

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CRTMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete residue mean is the independent uniform product law -/

namespace JointDickman
open Finset

theorem crt_uniform_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)]
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (F : (∀ i, ZMod (m i)) → ℝ) :
    (∑ n ∈ range (∏ i, m i), F (fun i => (n : ZMod (m i)))) / (∏ i, (m i : ℝ)) =
      ∑ x, finiteProductMass (fun i (_ : ZMod (m i)) => 1 / (m i : ℝ)) x * F x := by
  classical
  let : NeZero (∏ i, m i) := ⟨prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (m i))⟩
  let e := ZMod.prodEquivPi m hcop
  have heval (n : ℕ) : e (n : ZMod (∏ i, m i)) = (n : ∀ i, ZMod (m i)) := map_natCast e n
  have hr := residue_sum_eq_range (fun a : ZMod (∏ i, m i) => (F (e a) : ℂ))
  simp only [heval] at hr
  have hr' : (∑ a : ZMod (∏ i, m i), F (e a)) =
      ∑ n ∈ range (∏ i, m i), F (fun i => (n : ZMod (m i))) := by exact_mod_cast hr
  have hs : (∑ a : ZMod (∏ i, m i), F (e a)) = ∑ x, F x :=
    e.toEquiv.sum_comp F
  rw [← hr', hs, sum_div]
  apply sum_congr rfl
  intro x _
  simp only [finiteProductMass, prod_div_distrib, prod_const_one]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMultiplicativeReduction
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The general-multiplicative reduction in corrected MRT §3.  The completely
multiplicative part keeps the original values at primes; the convolution
correction vanishes at primes and is bounded by two at higher prime powers. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

@[simp] lemma mrtArithmetic_apply_pos (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mrtArithmetic f n = f n := ite_eq_right hn.ne'

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinApplicationScales
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Qualitative application scales for the multiscale energy bound

The large fixed logarithmic exponent pays the explicit factorial budget.
The application needs only a vanishing error as the short length grows.
-/
namespace JointDickman
open Filter TwoPointCorrelations
open scoped Topology

lemma mellinFirstPrime_tendsto : Tendsto mellinFirstPrime atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 300000)).comp Real.tendsto_log_atTop

lemma mellinLastPrime_tendsto : Tendsto mellinLastPrime atTop atTop :=
  tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)

lemma mellinFirstPrime_div_last_tendsto :
    Tendsto (fun H => mellinFirstPrime H / mellinLastPrime H) atTop (𝓝 0) :=
  log_power_div_power_tendsto_zero 300000 (by norm_num)

lemma mellinLastPrime_div_length_tendsto :
    Tendsto (fun H => mellinLastPrime H / H) atTop (𝓝 0) := by
  have hh := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  dsimp [mellinLastPrime]
  have he : H^(1/2 : ℝ)/H = H^(-1/2 : ℝ) := by
    calc
      _ = H^(1/2 : ℝ)/H^(1 : ℝ) := by rw [Real.rpow_one]
      _ = H^((1/2 : ℝ)-1) := (Real.rpow_sub hH _ _).symm
      _ = _ := by norm_num
  simpa only [neg_div] using he.symm

lemma mellinResolution_eventually :
    ∀ᶠ H : ℝ in atTop, mellinResolution H =
      Real.exp ((74999/3 : ℝ)*Real.log (Real.log H) - (1/3 : ℝ)*Real.log (1/2 : ℝ)) := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℝ)] with H hH hH0
  unfold mellinResolution mrtBaseResolution mellinFirstPrime mellinLastPrime
  rw [Real.log_rpow hH, Real.log_rpow hH0,
    Real.log_mul (by norm_num : (1/2 : ℝ) ≠ 0) hH.ne']
  congr 1
  ring

lemma mellinResolution_tendsto : Tendsto mellinResolution atTop atTop := by
  have hm := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).const_mul_atTop
    (by norm_num : (0 : ℝ) < 74999/3)
  have hl : Tendsto (fun H : ℝ => (74999/3 : ℝ)*Real.log (Real.log H) -
      (1/3 : ℝ)*Real.log (1/2 : ℝ)) atTop atTop := by
    simpa only [sub_eq_add_neg, Function.comp_apply] using
      tendsto_atTop_add_const_right atTop (-((1/3 : ℝ)*Real.log (1/2 : ℝ))) hm
  have hh := Real.tendsto_exp_atTop.comp hl
  exact hh.congr' (mellinResolution_eventually.mono fun _ h => h.symm)

/-- All fixed-scale numerical hypotheses of the canonical partition hold
for every sufficiently large short length. -/
theorem eventually_mellin_application_scales :
    ∀ᶠ H : ℝ in atTop,
      2*Real.exp 1 ≤ mellinFirstPrime H ∧
      mellinFirstPrime H ≤ mellinLastPrime H ∧
      2 ≤ Real.log (mellinFirstPrime H) ∧ 1 ≤ Real.log (mellinLastPrime H) ∧
      8192*(Real.log (Real.log (mellinLastPrime H))+1) ≤
        (1/12 : ℝ)*Real.log (mellinFirstPrime H) ∧
      2 ≤ mellinResolution H := by
  have hPlog := Real.tendsto_log_atTop.comp mellinFirstPrime_tendsto
  have hQlog := Real.tendsto_log_atTop.comp mellinLastPrime_tendsto
  filter_upwards [mellinFirstPrime_tendsto.eventually (eventually_ge_atTop (2*Real.exp 1)),
    mellinFirstPrime_div_last_tendsto.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    hPlog.eventually (eventually_ge_atTop 2), hQlog.eventually (eventually_ge_atTop 1),
    mellinResolution_tendsto.eventually (eventually_ge_atTop 2),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop 1),
    eventually_gt_atTop (1 : ℝ)] with H hP hPQ hLP hLQ hR hLL hH
  have hH0 : 0 < H := by linarith
  have hlogH : 0 < Real.log H := Real.log_pos hH
  refine ⟨hP, (div_le_one (Real.rpow_pos_of_pos hH0 _)).mp hPQ, hLP, hLQ, ?_, hR⟩
  rw [mellinFirstPrime, mellinLastPrime, Real.log_rpow hlogH, Real.log_rpow hH0,
    Real.log_mul (by norm_num : (1/2 : ℝ) ≠ 0) hlogH.ne']
  simp only [Function.comp_apply] at hLL
  have hhalf : Real.log (1/2 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  nlinarith

theorem mellin_typical_cost_tendsto_zero :
    Tendsto (fun H => Real.log (mellinFirstPrime H) / Real.log (mellinLastPrime H))
      atTop (𝓝 0) := by
  have hh := (log_power_div_power_tendsto_zero 1 (by norm_num : (0 : ℝ) < 1)).comp
    Real.tendsto_log_atTop
  simp only [Real.rpow_one] at hh
  have hs := hh.const_mul 600000
  simp only [mul_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with H hH
  have hH0 : 0 < H := by linarith
  have hlog : 0 < Real.log H := Real.log_pos hH
  rw [mellinFirstPrime, mellinLastPrime, Real.log_rpow hlog, Real.log_rpow hH0]
  dsimp only [Function.comp_apply]
  ring

theorem mellinWindowCost_tendsto_zero : Tendsto mellinWindowCost atTop (𝓝 0) := by
  have hH : Tendsto (fun H : ℝ => H⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hP := tendsto_inv_atTop_zero.comp mellinFirstPrime_tendsto
  have hR := tendsto_inv_atTop_zero.comp mellinResolution_tendsto
  have hQ := mellinLastPrime_div_length_tendsto
  have h1 := ((hH.add_const 1).const_mul (2816*Real.exp 1)).mul
    ((hP.const_mul 8).add (hR.const_mul 4))
  have h2 := ((hQ.add_const 1).const_mul (1024*Real.exp 2)).mul hR
  have h3 := ((hH.add_const 1).const_mul 2).mul hP
  unfold mellinWindowCost
  simpa only [Function.comp_apply, mul_zero, add_zero, div_eq_mul_inv, mul_assoc]
    using (h1.add h2).add h3

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CanonicalAffineCost
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constant and linear frequency costs in the canonical estimate -/
namespace JointDickman
open Filter TwoPointCorrelations
open scoped Topology

theorem canonical_affine_budget (C : ℝ) :
    Tendsto (fun H => canonicalAffineBase C H+canonicalAffineSlope C H/H) atTop (𝓝 0) := by
  have h1 := mellinWindowCost_tendsto_zero.const_mul 2
  have h2 := ((tendsto_inv_atTop_zero.add_const 2).mul mellin_typical_cost_tendsto_zero).const_mul
    (48*Real.exp 1*C)
  have hh := h1.add h2
  simp only [mul_zero,add_zero] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext H
  dsimp only [canonicalAffineBase,canonicalAffineSlope,mellinWindowCost]
  ring

theorem canonical_affine_nonneg {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ H : ℝ in atTop, 0 ≤ canonicalAffineBase C H ∧ 0 ≤ canonicalAffineSlope C H := by
  filter_upwards [eventually_mellin_application_scales] with H hH
  have hP : 0 ≤ mellinFirstPrime H := by linarith [hH.1,Real.exp_pos 1]
  have hQ : 0 ≤ mellinLastPrime H := hP.trans hH.2.1
  have hR : 0 ≤ mellinResolution H := by linarith [hH.2.2.2.2.2]
  have hlogP : 0 ≤ Real.log (mellinFirstPrime H) := by linarith [hH.2.2.1]
  have hlogQ : 0 ≤ Real.log (mellinLastPrime H) := by linarith [hH.2.2.2.1]
  constructor <;> dsimp [canonicalAffineBase,canonicalAffineSlope] <;> positivity

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinLogWindows
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact logarithmic reparametrization of a short interval -/
namespace JointDickman
open Finset PublishedInputs

/-- The logarithmic interval has exactly the original arithmetic endpoints. -/
theorem logarithmicWindowAverage_endpoints (f : ArithmeticFunction ℂ)
    {x H : ℝ} (hx : 0 < x) (hH : 0 < H) :
    logarithmicWindowAverage f (Real.log ((x + H) / x)) (Real.log x) =
      (∑ n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, f n / (n : ℂ)) /
        (Real.log ((x + H) / x) : ℂ) := by
  have hsum : 0 < x + H := by positivity
  have he : Real.log x + Real.log ((x + H) / x) = Real.log (x + H) := by
    rw [Real.log_div hsum.ne' hx.ne']
    ring
  simp only [logarithmicWindowAverage, he, Real.exp_log hx, Real.exp_log hsum]

/-- Before normalization, the reciprocal short average is the exact
logarithmic-window sum, with no endpoint error. -/
theorem reciprocalShortAverage_eq_logarithmic (f : ArithmeticFunction ℂ)
    {x H : ℝ} (hx : 0 < x) (hH : 0 < H) :
    reciprocalShortAverage f H x =
      ((x * Real.log ((x + H) / x) / H : ℝ) : ℂ) *
        logarithmicWindowAverage f (Real.log ((x + H) / x)) (Real.log x) := by
  rw [logarithmicWindowAverage_endpoints f hx hH]
  have hδ := (logarithmic_window_width hx hH).1
  unfold reciprocalShortAverage
  push_cast
  field_simp [show (Real.log ((x + H) / x) : ℂ) ≠ 0 by exact_mod_cast hδ.ne',
    show (H : ℂ) ≠ 0 by exact_mod_cast hH.ne']

/-- A hard short average is bounded by its normalized logarithmic window
plus the uniform endpoint-scale error. -/
theorem norm_shortAverage_le_logarithmic (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {x H : ℝ} (hx : 0 < x) (hH : 0 < H) :
    ‖complexShortAverage f H x‖ ≤
      ‖logarithmicWindowAverage f (Real.log ((x + H) / x)) (Real.log x)‖ +
        (H + 1) / x := by
  have hδ := logarithmic_window_width hx hH
  have hfactor0 : 0 ≤ x * Real.log ((x + H) / x) / H :=
    div_nonneg (mul_nonneg hx.le hδ.1.le) hH.le
  have hfactor1 : x * Real.log ((x + H) / x) / H ≤ 1 := by
    apply (div_le_one hH).mpr
    have ht := mul_le_mul_of_nonneg_left hδ.2.2 hx.le
    simpa only [mul_div_cancel₀ _ hx.ne'] using ht
  have hrecip : ‖reciprocalShortAverage f H x‖ ≤
      ‖logarithmicWindowAverage f (Real.log ((x + H) / x)) (Real.log x)‖ := by
    rw [reciprocalShortAverage_eq_logarithmic f hx hH, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfactor0]
    exact mul_le_of_le_one_left (norm_nonneg _) hfactor1
  calc
    _ = ‖(complexShortAverage f H x - reciprocalShortAverage f H x) +
        reciprocalShortAverage f H x‖ := by rw [sub_add_cancel]
    _ ≤ ‖complexShortAverage f H x - reciprocalShortAverage f H x‖ +
        ‖reciprocalShortAverage f H x‖ := norm_add_le _ _
    _ ≤ (H + 1) / x +
        ‖logarithmicWindowAverage f (Real.log ((x + H) / x)) (Real.log x)‖ :=
      add_le_add (short_average_reciprocal_error f hf hx hH) hrecip
    _ = _ := add_comm _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinWindowProfile
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth inner approximations to a logarithmic interval -/
namespace JointDickman
open scoped SchwartzMap

theorem logarithmicWindowProfile_apply (η : ℝ) (hη : 0 < η) (hηhalf : η < 1/2)
    (v : ℝ) : logarithmicWindowProfile η hη hηhalf v =
      ((logarithmicWindowBump η hη hηhalf v : ℝ) : ℂ) := rfl

theorem logarithmicWindowProfile_norm_le (η : ℝ) (hη : 0 < η)
    (hηhalf : η < 1/2) (v : ℝ) : ‖logarithmicWindowProfile η hη hηhalf v‖ ≤ 1 := by
  rw [logarithmicWindowProfile_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (logarithmicWindowBump η hη hηhalf).nonneg]
  exact (logarithmicWindowBump η hη hηhalf).le_one

theorem logarithmicWindowProfile_one (η : ℝ) (hη : 0 < η)
    (hηhalf : η < 1/2) {v : ℝ} (hv : v ∈ Set.Icc η (1 - η)) :
    logarithmicWindowProfile η hη hηhalf v = 1 := by
  rw [logarithmicWindowProfile_apply]
  have hh : logarithmicWindowBump η hη hηhalf v = 1 := by
    apply (logarithmicWindowBump η hη hηhalf).one_of_mem_closedBall
    change dist v (1/2 : ℝ) ≤ 1/2 - η
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hv.1, hv.2]
  rw [hh, Complex.ofReal_one]

theorem logarithmicWindowProfile_zero (η : ℝ) (hη : 0 < η)
    (hηhalf : η < 1/2) {v : ℝ} (hv : v ≤ 0 ∨ 1 ≤ v) :
    logarithmicWindowProfile η hη hηhalf v = 0 := by
  rw [logarithmicWindowProfile_apply]
  have hh : logarithmicWindowBump η hη hηhalf v = 0 := by
    apply (logarithmicWindowBump η hη hηhalf).zero_of_le_dist
    change (1/2 : ℝ) ≤ dist v (1/2 : ℝ)
    rw [Real.dist_eq]
    rcases hv with hv | hv
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  rw [hh, Complex.ofReal_zero]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinWindowSupport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The support and central plateau of the logarithmic smoothing kernel -/
namespace JointDickman
open Finset
open scoped SchwartzMap

lemma logarithmicWindowProfile_zero_of_outside {η δ x y : ℝ}
    (hη : 0 < η) (hηhalf : η < 1/2) (hδ : 0 < δ) (hx : 0 < x) (hy : 0 < y)
    (hout : y ≤ x ∨ x * Real.exp δ ≤ y) :
    logarithmicWindowProfile η hη hηhalf ((Real.log x + δ - Real.log y) / δ) = 0 := by
  apply logarithmicWindowProfile_zero
  rcases hout with hlo | hhi
  · right
    apply (le_div_iff₀ hδ).mpr
    have hh := Real.log_le_log hy hlo
    linarith
  · left
    apply div_nonpos_of_nonpos_of_nonneg _ hδ.le
    have hh := Real.log_le_log (mul_pos hx (Real.exp_pos δ)) hhi
    rw [Real.log_mul hx.ne' (Real.exp_ne_zero δ), Real.log_exp] at hh
    linarith

lemma logarithmicWindowProfile_one_of_inside {η δ x y : ℝ}
    (hη : 0 < η) (hηhalf : η < 1/2) (hδ : 0 < δ) (hx : 0 < x) (hy : 0 < y)
    (hlo : x * Real.exp (η * δ) ≤ y)
    (hhi : y ≤ x * Real.exp ((1 - η) * δ)) :
    logarithmicWindowProfile η hη hηhalf ((Real.log x + δ - Real.log y) / δ) = 1 := by
  apply logarithmicWindowProfile_one
  constructor
  · apply (le_div_iff₀ hδ).mpr
    have hh := Real.log_le_log hy hhi
    rw [Real.log_mul hx.ne' (Real.exp_ne_zero _), Real.log_exp] at hh
    nlinarith
  · apply (div_le_iff₀ hδ).mpr
    have hh := Real.log_le_log (mul_pos hx (Real.exp_pos _)) hlo
    rw [Real.log_mul hx.ne' (Real.exp_ne_zero _), Real.log_exp] at hh
    nlinarith

/-- Enlarging the finite Dirichlet polynomial adds only zero kernel terms. -/
theorem mellinPacket_logarithmicWindow_support (f : ℕ → ℂ) {K N : ℕ} {η δ x : ℝ}
    (hη : 0 < η) (hηhalf : η < 1/2) (hδ : 0 < δ) (hx : 0 < x)
    (hK : K ≤ ⌊x⌋₊) (hN : ⌊x * Real.exp δ⌋₊ ≤ N) :
    mellinPacket (Ioc K N) f
      (normalizedSchwartzScale (logarithmicWindowProfile η hη hηhalf) δ hδ)
      (Real.log x + δ) =
    (∑ n ∈ Ioc ⌊x⌋₊ ⌊x * Real.exp δ⌋₊,
      (f n / (n : ℂ)) * logarithmicWindowProfile η hη hηhalf
        ((Real.log x + δ - Real.log (n : ℝ)) / δ)) / (δ : ℂ) := by
  rw [mellinPacket_apply]
  simp_rw [normalizedSchwartzScale_apply, ← mul_div_assoc]
  rw [← sum_div]
  congr 1
  symm
  apply sum_subset
  · intro n hn
    rcases mem_Ioc.mp hn with ⟨hlo, hhi⟩
    exact mem_Ioc.mpr ⟨hK.trans_lt hlo, hhi.trans hN⟩
  · intro n hn hnout
    have hn0 : 0 < (n : ℝ) := by
      have hh := (Nat.zero_le K).trans_lt (mem_Ioc.mp hn).1
      exact_mod_cast hh
    have hout : (n : ℝ) ≤ x ∨ x * Real.exp δ ≤ (n : ℝ) := by
      by_cases hnx : n ≤ ⌊x⌋₊
      · left
        exact (show (n : ℝ) ≤ (⌊x⌋₊ : ℝ) by exact_mod_cast hnx).trans (Nat.floor_le hx.le)
      · right
        have hnupper : ⌊x * Real.exp δ⌋₊ < n := by
          have : ¬ n ≤ ⌊x * Real.exp δ⌋₊ := by
            intro hh
            exact hnout (mem_Ioc.mpr ⟨Nat.lt_of_not_ge hnx, hh⟩)
          omega
        exact (Nat.lt_of_floor_lt hnupper).le
    rw [logarithmicWindowProfile_zero_of_outside hη hηhalf hδ hx hn0 hout, mul_zero]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinWindowError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform error of smoothing a hard logarithmic window -/
namespace JointDickman
open Finset

/-- Only integers in the two transition strips can see a nonconstant profile. -/
lemma logarithmicWindowProfile_bad_card {η δ x : ℝ}
    (hη : 0 < η) (hηhalf : η < 1/2) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hx : 0 < x) :
    (((Ioc ⌊x⌋₊ ⌊x * Real.exp δ⌋₊).filter fun n : ℕ =>
      logarithmicWindowProfile η hη hηhalf
        ((Real.log x + δ - Real.log (n : ℝ)) / δ) ≠ 1).card : ℝ) ≤
          8 * η * δ * x + 2 := by
  let W := Ioc ⌊x⌋₊ ⌊x * Real.exp δ⌋₊
  let B := W.filter fun n : ℕ => logarithmicWindowProfile η hη hηhalf
    ((Real.log x + δ - Real.log (n : ℝ)) / δ) ≠ 1
  let L := Ioc ⌊x⌋₊ ⌊x * Real.exp (η * δ)⌋₊
  let U := Ioc ⌊x * Real.exp ((1 - η) * δ)⌋₊ ⌊x * Real.exp δ⌋₊
  have hsub : B ⊆ L ∪ U := by
    intro n hn
    obtain ⟨hnW, hnB⟩ := mem_filter.mp hn
    obtain ⟨hnlo, hnhi⟩ := mem_Ioc.mp hnW
    have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hnlo
    have hn0 : 0 < (n : ℝ) := hx.trans hxn
    by_cases hlo : (n : ℝ) ≤ x * Real.exp (η * δ)
    · exact mem_union_left U (mem_Ioc.mpr ⟨hnlo, Nat.le_floor hlo⟩)
    · by_cases hhi : x * Real.exp ((1 - η) * δ) < (n : ℝ)
      · exact mem_union_right L (mem_Ioc.mpr
          ⟨(Nat.floor_lt (mul_nonneg hx.le (Real.exp_pos _).le)).mpr hhi, hnhi⟩)
      · exact False.elim (hnB (logarithmicWindowProfile_one_of_inside
          hη hηhalf hδ hx hn0 (le_of_not_ge hlo) (le_of_not_gt hhi)))
  have hcard : (B.card : ℝ) ≤ (L.card : ℝ) + (U.card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le L U)
  exact hcard.trans (logarithmic_boundary_card hx.le hη.le (by linarith) hδ.le hδ1)

/-- The hard window differs from the smooth Mellin packet by an arbitrarily
small fixed profile error and the explicit integer endpoint error. -/
theorem logarithmicWindowAverage_mellinPacket_error (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {K N : ℕ} {η δ x : ℝ}
    (hη : 0 < η) (hηhalf : η < 1/2) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hx : 0 < x)
    (hK : K ≤ ⌊x⌋₊) (hN : ⌊x * Real.exp δ⌋₊ ≤ N) :
    ‖logarithmicWindowAverage f δ (Real.log x) -
      mellinPacket (Ioc K N) f
        (normalizedSchwartzScale (logarithmicWindowProfile η hη hηhalf) δ hδ)
        (Real.log x + δ)‖ ≤ 16 * η + 4 / (δ * x) := by
  let W := Ioc ⌊x⌋₊ ⌊x * Real.exp δ⌋₊
  let w := fun n : ℕ => logarithmicWindowProfile η hη hηhalf
    ((Real.log x + δ - Real.log (n : ℝ)) / δ)
  let B := W.filter fun n : ℕ => w n ≠ 1
  have hsum : (∑ n ∈ W, (f n / (n : ℂ) - (f n / (n : ℂ)) * w n)) =
      ∑ n ∈ B, (f n / (n : ℂ) - (f n / (n : ℂ)) * w n) := by
    symm
    apply sum_subset (filter_subset _ _)
    intro n hn hnB
    have hw : w n = 1 := by
      by_contra h
      exact hnB (mem_filter.mpr ⟨hn, h⟩)
    rw [hw, mul_one, sub_self]
  have hterm (n : ℕ) (hn : n ∈ B) :
      ‖f n / (n : ℂ) - (f n / (n : ℂ)) * w n‖ ≤ 2 / x := by
    have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt (mem_Ioc.mp (mem_filter.mp hn).1).1
    have hn0 : 0 < (n : ℝ) := hx.trans hxn
    have hrecip : ‖f n / (n : ℂ)‖ ≤ 1 / x := by
      rw [norm_div, Complex.norm_natCast]
      exact (div_le_div_of_nonneg_right (hf n) hn0.le).trans
        (one_div_le_one_div_of_le hx hxn.le)
    have hw : ‖w n‖ ≤ 1 := logarithmicWindowProfile_norm_le _ _ _ _
    calc
      _ ≤ ‖f n / (n : ℂ)‖ + ‖(f n / (n : ℂ)) * w n‖ := norm_sub_le _ _
      _ ≤ 1 / x + (1 / x) * 1 := by
        rw [norm_mul]
        exact add_le_add hrecip (mul_le_mul hrecip hw (norm_nonneg _) (by positivity))
      _ = 2 / x := by ring
  have hnorm : ‖∑ n ∈ W, (f n / (n : ℂ) - (f n / (n : ℂ)) * w n)‖ ≤
      (B.card : ℝ) * (2 / x) := by
    rw [hsum]
    exact (norm_sum_le _ _).trans ((sum_le_sum hterm).trans_eq (by simp))
  have hcard : (B.card : ℝ) ≤ 8 * η * δ * x + 2 :=
    logarithmicWindowProfile_bad_card hη hηhalf hδ hδ1 hx
  rw [mellinPacket_logarithmicWindow_support f hη hηhalf hδ hx hK hN]
  unfold logarithmicWindowAverage
  rw [Real.exp_add, Real.exp_log hx, ← sub_div, ← sum_sub_distrib,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  calc
    _ ≤ ((B.card : ℝ) * (2 / x)) / δ := div_le_div_of_nonneg_right hnorm hδ.le
    _ ≤ ((8 * η * δ * x + 2) * (2 / x)) / δ := by gcongr
    _ = 16 * η + 4 / (δ * x) := by field_simp <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ShortLengthComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Varying the short length on a fixed interval of origins -/
namespace JointDickman
open Finset PublishedInputs

lemma norm_short_sum_le (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {x H : ℝ} (hx : 0 ≤ x) (hH : 0 ≤ H) :
    ‖∑ n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, f n‖ ≤ H + 1 := by
  calc
    _ ≤ ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, (1 : ℝ) := sum_le_sum (fun n _ => hf n)
    _ = ((Ioc ⌊x⌋₊ ⌊x + H⌋₊).card : ℝ) := by simp
    _ ≤ _ := mellin_short_interval_card_le hx hH

lemma norm_short_sum_length_difference (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {x H K : ℝ} (hx : 0 ≤ x) (hH : 0 ≤ H) (hHK : H ≤ K) :
    ‖(∑ n ∈ Ioc ⌊x⌋₊ ⌊x + K⌋₊, f n) -
      ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, f n‖ ≤ K - H + 1 := by
  have hab : ⌊x⌋₊ ≤ ⌊x + H⌋₊ := Nat.floor_mono (by linarith)
  have hbc : ⌊x + H⌋₊ ≤ ⌊x + K⌋₊ := Nat.floor_mono (by linarith)
  have hsub : Ioc ⌊x⌋₊ ⌊x + H⌋₊ ⊆ Ioc ⌊x⌋₊ ⌊x + K⌋₊ :=
    fun _ hn => mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2.trans hbc⟩
  have hset : Ioc ⌊x⌋₊ ⌊x + K⌋₊ \ Ioc ⌊x⌋₊ ⌊x + H⌋₊ =
      Ioc ⌊x + H⌋₊ ⌊x + K⌋₊ := by
    ext n
    simp only [mem_sdiff, mem_Ioc]
    omega
  rw [← sum_sdiff hsub, add_sub_cancel_right, hset]
  have he : x + H + (K - H) = x + K := by ring
  simpa only [he] using norm_short_sum_le f hf (by linarith : 0 ≤ x + H)
    (sub_nonneg.mpr hHK)

lemma norm_shortAverage_le_two (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {x H : ℝ} (hx : 0 ≤ x) (hH : 1 ≤ H) : ‖complexShortAverage f H x‖ ≤ 2 := by
  have hH0 : 0 < H := by linarith
  rw [complexShortAverage, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH0]
  apply (div_le_iff₀ hH0).mpr
  exact (norm_short_sum_le f hf hx hH0.le).trans (by linarith)

/-- Nearby lengths have uniformly close normalized averages. -/
theorem shortAverage_length_difference (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {x H K : ℝ} (hx : 0 ≤ x) (hH : 1 ≤ H) (hHK : H ≤ K) :
    ‖complexShortAverage f H x - complexShortAverage f K x‖ ≤
      3 * (K - H + 1) / H := by
  have hH0 : 0 < H := by linarith
  have hK0 : 0 < K := hH0.trans_le hHK
  let S := ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + H⌋₊, f n
  let T := ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + K⌋₊, f n
  have he : complexShortAverage f H x - complexShortAverage f K x =
      (S - T) / (H : ℂ) + (((K - H) / H : ℝ) : ℂ) * complexShortAverage f K x := by
    dsimp [S, T, complexShortAverage]
    push_cast
    field_simp [show (H : ℂ) ≠ 0 by exact_mod_cast hH0.ne',
      show (K : ℂ) ≠ 0 by exact_mod_cast hK0.ne']
    ring
  have htail : ‖S - T‖ ≤ K - H + 1 := by
    rw [norm_sub_rev]
    exact norm_short_sum_length_difference f hf hx hH0.le hHK
  have hcoef : 0 ≤ (K - H) / H := div_nonneg (sub_nonneg.mpr hHK) hH0.le
  rw [he]
  calc
    _ ≤ ‖(S - T) / (H : ℂ)‖ +
        ‖(((K - H) / H : ℝ) : ℂ) * complexShortAverage f K x‖ := norm_add_le _ _
    _ = ‖S - T‖ / H + ((K - H) / H) * ‖complexShortAverage f K x‖ := by
      rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hH0, Real.norm_eq_abs, abs_of_nonneg hcoef]
    _ ≤ (K - H + 1) / H + ((K - H) / H) * 2 :=
      add_le_add (div_le_div_of_nonneg_right htail hH0.le)
        (mul_le_mul_of_nonneg_left (norm_shortAverage_le_two f hf hx (hH.trans hHK)) hcoef)
    _ = (3 * (K - H) + 1) / H := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hH0.le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LogarithmicWindowFreeze
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Freezing the relative short-window length on a small block -/
namespace JointDickman
open PublishedInputs

theorem shortAverage_le_fixed_logarithmic_window (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {X H ε x : ℝ} (hX : 0 < X) (hH : 1 ≤ H)
    (hx : x ∈ Set.Icc X ((1 + ε) * X)) :
    ‖complexShortAverage f H x‖ ≤
      ‖logarithmicWindowAverage f (Real.log ((X + H) / X)) (Real.log x)‖ +
        (3 * ε + 3 / H + H / X + 1 / X) := by
  have hx0 : 0 < x := hX.trans_le hx.1
  have hH0 : 0 < H := by linarith
  let K : ℝ := H * x / X
  have hK0 : 0 < K := div_pos (mul_pos hH0 hx0) hX
  have hHK : H ≤ K := by
    apply (le_div_iff₀ hX).mpr
    nlinarith [mul_le_mul_of_nonneg_left hx.1 hH0.le]
  have hKupper : K ≤ (1 + ε) * H := by
    apply (div_le_iff₀ hX).mpr
    nlinarith [mul_le_mul_of_nonneg_left hx.2 hH0.le]
  have hratio : (x + K) / x = (X + H) / X := by
    dsimp [K]
    field_simp
  have hlog := norm_shortAverage_le_logarithmic f hf hx0 hK0
  rw [hratio] at hlog
  have hdiff := shortAverage_length_difference f hf hx0.le hH hHK
  have herror : 3 * (K - H + 1) / H ≤ 3 * ε + 3 / H := by
    calc
      _ ≤ 3 * (ε * H + 1) / H := by gcongr; linarith
      _ = _ := by field_simp
  have hweight : (K + 1) / x = H / X + 1 / x := by
    dsimp [K]
    field_simp
  have hinv : 1 / x ≤ 1 / X := one_div_le_one_div_of_le hX hx.1
  calc
    _ = ‖(complexShortAverage f H x - complexShortAverage f K x) +
        complexShortAverage f K x‖ := by rw [sub_add_cancel]
    _ ≤ ‖complexShortAverage f H x - complexShortAverage f K x‖ +
        ‖complexShortAverage f K x‖ := norm_add_le _ _
    _ ≤ 3 * (K - H + 1) / H +
        (‖logarithmicWindowAverage f (Real.log ((X + H) / X)) (Real.log x)‖ +
          (K + 1) / x) := add_le_add hdiff hlog
    _ ≤ _ := by rw [hweight]; linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ShortMellinComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform approximation of the original short average on a small block -/
namespace JointDickman
open Finset PublishedInputs

/-- The coefficients are restricted to the same fixed block for every
location of the short interval; all errors are uniform on that block. -/
theorem shortAverage_le_mellinPacket_of_support (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {K N : ℕ} {X H ε η x : ℝ}
    (hX : 0 < X) (hH : 1 ≤ H) (hHX : H ≤ X)
    (hη : 0 < η) (hηhalf : η < 1/2)
    (hx : x ∈ Set.Icc X ((1 + ε) * X))
    (hK : K ≤ ⌊X⌋₊) (hN : ⌊(1 + ε) * (X + H)⌋₊ ≤ N) :
    let δ := Real.log ((X + H) / X)
    let hδ := (logarithmic_window_width hX (by linarith : 0 < H)).1
    ‖complexShortAverage f H x‖ ≤
      ‖mellinPacket (Ioc K N) f
        (normalizedSchwartzScale (logarithmicWindowProfile η hη hηhalf) δ hδ)
        (Real.log x + δ)‖ +
      (3 * ε + 11 / H + H / X + 1 / X + 16 * η) := by
  dsimp only
  let δ := Real.log ((X + H) / X)
  have hH0 : 0 < H := by linarith
  obtain ⟨hδ, hδlo, hδhi⟩ := logarithmic_window_width hX hH0
  have hδ1 : δ ≤ 1 := hδhi.trans ((div_le_one hX).mpr hHX)
  have hx0 : 0 < x := hX.trans_le hx.1
  have htop : x * Real.exp δ ≤ (1 + ε) * (X + H) := by
    dsimp [δ]
    rw [Real.exp_log (div_pos (by linarith) hX)]
    calc
      _ ≤ ((1 + ε) * X) * ((X + H) / X) :=
        mul_le_mul_of_nonneg_right hx.2 (by positivity)
      _ = _ := by field_simp
  have happrox := logarithmicWindowAverage_mellinPacket_error f hf hη hηhalf hδ hδ1 hx0
    (hK.trans (Nat.floor_mono hx.1)) ((Nat.floor_mono htop).trans hN)
  have hwindow := shortAverage_le_fixed_logarithmic_window f hf hX hH hx
  have hlower : H ≤ 2 * δ * x := by
    have hbase := (div_le_iff₀ (show 0 < X + H by linarith)).mp hδlo
    have hdouble : δ * (X + H) ≤ 2 * δ * X := by nlinarith
    have hxmul := mul_le_mul_of_nonneg_left hx.1 hδ.le
    nlinarith
  have hendpoint : 4 / (δ * x) ≤ 8 / H := by
    apply (div_le_div_iff₀ (mul_pos hδ hx0) hH0).mpr
    nlinarith
  have htriangle := norm_add_le
    (logarithmicWindowAverage f δ (Real.log x) -
      mellinPacket (Ioc K N) f
        (normalizedSchwartzScale (logarithmicWindowProfile η hη hηhalf) δ hδ)
        (Real.log x + δ))
    (mellinPacket (Ioc K N) f
      (normalizedSchwartzScale (logarithmicWindowProfile η hη hηhalf) δ hδ)
      (Real.log x + δ))
  rw [sub_add_cancel] at htriangle
  change ‖complexShortAverage f H x‖ ≤ _
  change ‖complexShortAverage f H x‖ ≤
    ‖logarithmicWindowAverage f δ (Real.log x)‖ + _ at hwindow
  dsimp only [δ] at hendpoint htriangle hwindow
  simp only [div_eq_mul_inv] at hwindow hendpoint happrox htriangle ⊢
  linarith only [hwindow, hendpoint, happrox, htriangle]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LogarithmicEnergyTransfer
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Returning from logarithmic measure to the original short-average variable -/
namespace JointDickman
open MeasureTheory
open scoped SchwartzMap

/-- On a positive block the Jacobian costs at most the upper endpoint. -/
theorem schwartz_logarithmic_energy_le (P : 𝓢(ℝ, ℂ)) {X Y : ℝ}
    (hX : 0 < X) (hXY : X ≤ Y) (δ : ℝ) :
    (∫ x in X..Y, ‖P (Real.log x + δ)‖ ^ 2) ≤
      Y * ∫ v : ℝ, ‖P v‖ ^ 2 := by
  let Q : ℝ → ℝ := fun v => ‖P (v + δ)‖ ^ 2
  have hQ : Continuous Q := (P.continuous.comp (continuous_id.add_const δ)).norm.pow 2
  have hlog : ContinuousOn Real.log (Set.uIcc X Y) := by
    rw [Set.uIcc_of_le hXY]
    intro x hx
    exact (Real.continuousAt_log (hX.trans_le hx.1).ne').continuousWithinAt
  have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc X Y) := by
    apply continuousOn_id.inv₀
    intro x hx
    rw [Set.uIcc_of_le hXY] at hx
    exact (hX.trans_le hx.1).ne'
  have hG : ContinuousOn (fun x => Q (Real.log x)) (Set.uIcc X Y) :=
    hQ.comp_continuousOn hlog
  have hchange : (∫ x in X..Y, Q (Real.log x) * x⁻¹) =
      ∫ v in Real.log X..Real.log Y, Q v := by
    apply intervalIntegral.integral_comp_mul_deriv (f := Real.log) (f' := fun x => x⁻¹) (g := Q)
    · intro x hx
      rw [Set.uIcc_of_le hXY] at hx
      exact Real.hasDerivAt_log (hX.trans_le hx.1).ne'
    · exact hinv
    · exact hQ
  have hbound : (∫ x in X..Y, Q (Real.log x)) ≤
      Y * ∫ v in Real.log X..Real.log Y, Q v := by
    rw [← hchange, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hXY hG.intervalIntegrable
      ((continuousOn_const.mul (hG.mul hinv)).intervalIntegrable)
    intro x hx
    have hx0 : 0 < x := hX.trans_le hx.1
    have hratio : 1 ≤ Y * x⁻¹ := by
      rw [← div_eq_mul_inv]
      exact (one_le_div hx0).mpr hx.2
    have hq : 0 ≤ Q (Real.log x) := sq_nonneg _
    change Q (Real.log x) ≤ Y * (Q (Real.log x) * x⁻¹)
    nlinarith [mul_le_mul_of_nonneg_left hratio hq]
  have hI : Integrable Q := by
    have hp := (P.memLp 2).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    exact hp.comp_add_right δ
  have hwhole : (∫ v in Real.log X..Real.log Y, Q v) ≤ ∫ v : ℝ, Q v := by
    rw [intervalIntegral.integral_of_le (Real.log_le_log hX hXY)]
    exact setIntegral_le_integral hI (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  have heq : (∫ v : ℝ, Q v) = ∫ v : ℝ, ‖P v‖ ^ 2 :=
    integral_add_right_eq_self (fun v : ℝ => ‖P v‖ ^ 2) δ
  exact hbound.trans ((mul_le_mul_of_nonneg_left hwhole (hX.trans_le hXY).le).trans_eq
    (congrArg (Y * ·) heq))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ShortMellinEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Short-average energy from the actual Dirichlet polynomial on a block -/
namespace JointDickman
open Finset MeasureTheory PublishedInputs

/-- A linear spectral bound yields a uniform bound for the original short
averages. The coefficient range is explicit and the smoothing error tends to
zero with the block width, profile transition width, and endpoint scales. -/
theorem shortAverage_block_energy_of_support (η : ℝ) (hη : 0 < η) (hηhalf : η < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ArithmeticFunction ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ (K N : ℕ) (X H ε : ℝ), 0 < X → 1 ≤ H → H ≤ X → 0 ≤ ε → ε ≤ 1 →
      K ≤ ⌊X⌋₊ → ⌊(1 + ε) * (X + H)⌋₊ ≤ N →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      (∀ T : ℝ, 1 ≤ T →
        (∫ t in -T..T, ‖mellinPolynomial
          (Ioc K N) f t‖ ^ 2) ≤ A + B * T) →
      (1 / X) * (∫ x in X..(1 + ε) * X, ‖complexShortAverage f H x‖ ^ 2) ≤
        C * (A + B * X / H) +
          2 * ε * (3 * ε + 11 / H + H / X + 1 / X + 16 * η) ^ 2 := by
  obtain ⟨C, hC, hCbound⟩ :=
    mellinPacket_energy_of_spectral_bound (logarithmicWindowProfile η hη hηhalf)
  refine ⟨8 * C, by positivity, ?_⟩
  intro f hf K N X H ε hX hH hHX hε hε1 hK hN A B hA hB hspectral
  have hH0 : 0 < H := by linarith
  let δ := Real.log ((X + H) / X)
  have hwidth := logarithmic_window_width hX hH0
  have hδ : 0 < δ := hwidth.1
  have hδ1 : δ ≤ 1 := hwidth.2.2.trans ((div_le_one hX).mpr hHX)
  let Y := (1 + ε) * X
  have hXY : X ≤ Y := by dsimp [Y] <;> nlinarith
  have hY2 : Y ≤ 2 * X := by dsimp [Y] <;> nlinarith
  let P := mellinPacket (Ioc K N) f
    (normalizedSchwartzScale (logarithmicWindowProfile η hη hηhalf) δ hδ)
  let E := 3 * ε + 11 / H + H / X + 1 / X + 16 * η
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have hP : (∫ v : ℝ, ‖P v‖ ^ 2) ≤ C * (A + B / δ) :=
    hCbound _ _ δ hδ hδ1 A B hA hB hspectral
  have hPnonneg : 0 ≤ ∫ v : ℝ, ‖P v‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hlog : ContinuousOn (fun x => ‖P (Real.log x + δ)‖ ^ 2) (Set.uIcc X Y) := by
    rw [Set.uIcc_of_le hXY]
    intro x hx
    exact ((P.continuous.continuousAt.comp ((Real.continuousAt_log
      (hX.trans_le hx.1).ne').add_const δ)).norm.pow 2).continuousWithinAt
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc X Y) :
      ‖complexShortAverage f H x‖ ^ 2 ≤ 2 * ‖P (Real.log x + δ)‖ ^ 2 + 2 * E ^ 2 := by
    have hh := shortAverage_le_mellinPacket_of_support f hf hX hH hHX hη hηhalf hx hK hN
    change ‖complexShortAverage f H x‖ ≤ ‖P (Real.log x + δ)‖ + E at hh
    have hn := norm_nonneg (complexShortAverage f H x)
    have hp := norm_nonneg (P (Real.log x + δ))
    nlinarith [sq_nonneg (‖P (Real.log x + δ)‖ - E)]
  have hshort : (∫ x in X..Y, ‖complexShortAverage f H x‖ ^ 2) ≤
      2 * Y * (C * (A + B / δ)) + 2 * (Y - X) * E ^ 2 := by
    calc
      _ ≤ ∫ x in X..Y, 2 * ‖P (Real.log x + δ)‖ ^ 2 + 2 * E ^ 2 :=
        intervalIntegral.integral_mono_on hXY (complexShortAverage_sq_integrable f hf hH0 X Y)
          ((hlog.const_mul 2).add continuousOn_const).intervalIntegrable hpoint
      _ = 2 * (∫ x in X..Y, ‖P (Real.log x + δ)‖ ^ 2) + 2 * (Y - X) * E ^ 2 := by
        rw [intervalIntegral.integral_add (hlog.const_mul 2).intervalIntegrable intervalIntegrable_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
      _ ≤ 2 * (Y * ∫ v : ℝ, ‖P v‖ ^ 2) + 2 * (Y - X) * E ^ 2 := by
        gcongr
        exact schwartz_logarithmic_energy_le P hX hXY δ
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hP (show 0 ≤ 2 * Y by positivity)
        nlinarith only [hh]
  have hlow : H ≤ 2 * δ * X := by
    have hh := (div_le_iff₀ (show 0 < X + H by linarith)).mp hwidth.2.1
    have hmul := mul_le_mul_of_nonneg_left hHX hδ.le
    nlinarith
  have hBδ : B / δ ≤ 2 * (B * X / H) := by
    calc
      B / δ ≤ (2 * B * X) / H := by
        apply (div_le_div_iff₀ hδ hH0).mpr
        nlinarith [mul_le_mul_of_nonneg_left hlow hB]
      _ = _ := by ring
  have hbudget : 2 * Y * (C * (A + B / δ)) ≤ 8 * C * X * (A + B * X / H) := by
    have hsmall : 0 ≤ B * X / H := by positivity
    have hfirst : 2 * Y * (C * (A + B / δ)) ≤
        2 * (2 * X) * (C * (A + 2 * (B * X / H))) := by gcongr
    nlinarith [mul_nonneg (by positivity : 0 ≤ C * X) hA]
  have hscaled := mul_le_mul_of_nonneg_left (hshort.trans (add_le_add hbudget (le_refl (2 * (Y - X) * E ^ 2))))
    (show 0 ≤ 1 / X by positivity)
  have hright : (1 / X) * (8 * C * X * (A + B * X / H) + 2 * (Y - X) * E ^ 2) =
      8 * C * (A + B * X / H) + 2 * ε * E ^ 2 := by
    dsimp [Y]
    field_simp
    ring
  rw [hright] at hscaled
  exact hscaled

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_ShortMellinDyadicEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite block cover for the full dyadic short-average integral -/
namespace JointDickman
open Finset MeasureTheory PublishedInputs

/-- The spectral bound is needed only on subintervals of the coefficient
range [X,4X]. The number of blocks is fixed before the short length grows. -/
theorem shortAverage_dyadic_energy (η : ℝ) (hη : 0 < η) (hηhalf : η < 1/2)
    (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ArithmeticFunction ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ X H : ℝ, 0 < X → 1 ≤ H → H ≤ X → ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      (∀ T : ℝ, 1 ≤ T →
        (∫ t in -T..T, ‖mellinPolynomial (Ioc ⌊X⌋₊ ⌊4 * X⌋₊) f t‖ ^ 2) ≤ A + B * T) →
      (1 / X) * (∫ x in X..2 * X, ‖complexShortAverage f H x‖ ^ 2) ≤
        C * (A + B * X / H) +
          2 * (3 / (m : ℝ) + 11 / H + H / X + 1 / X + 16 * η) ^ 2 := by
  obtain ⟨C, hC, hblock⟩ := shortAverage_block_energy_of_support η hη hηhalf
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  refine ⟨4 * (m : ℝ) * C, by positivity, ?_⟩
  intro f hf X H hX hH hHX A B hA hB hspectral
  have hH0 : 0 < H := by linarith
  let a : ℕ → ℝ := fun j => X + (j : ℝ) * (X / m)
  let e : ℕ → ℝ := fun j => (X / m) / a j
  let E : ℝ := 3 / (m : ℝ) + 11 / H + H / X + 1 / X + 16 * η
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have ha0 : a 0 = X := by simp [a]
  have ham : a m = 2 * X := by dsimp [a]; field_simp <;> ring
  have ha (j : ℕ) (hj : j ≤ m) : a j ∈ Set.Icc X (2 * X) := by
    have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
    dsimp [a]
    constructor
    · exact le_add_of_nonneg_right (by positivity)
    · have hh := mul_le_mul_of_nonneg_right hj' (show 0 ≤ X / m by positivity)
      rw [mul_div_cancel₀ X hm0.ne'] at hh
      linarith
  have hap (j : ℕ) (hj : j ≤ m) : 0 < a j := hX.trans_le (ha j hj).1
  have he (j : ℕ) (hj : j ≤ m) : e j ∈ Set.Icc (0 : ℝ) (1 / (m : ℝ)) := by
    constructor
    · dsimp [e] <;> positivity
    · dsimp [e]
      apply (div_le_iff₀ (hap j hj)).mpr
      have hh := div_le_div_of_nonneg_right (ha j hj).1 hm0.le
      simpa only [one_div_mul_eq_div] using hh
  have hstep (j : ℕ) (hj : j ≤ m) : (1 + e j) * a j = a (j + 1) := by
    dsimp [e]
    rw [add_mul, one_mul, div_mul_cancel₀ _ (hap j hj).ne']
    simp only [a, Nat.cast_add, Nat.cast_one]
    ring
  have hcell (j : ℕ) (hj : j < m) :
      (∫ x in a j..a (j + 1), ‖complexShortAverage f H x‖ ^ 2) ≤
        2 * X * C * (A + 2 * (B * X / H)) + 2 * (X / m) * E ^ 2 := by
    have hjle := hj.le
    have hU := ha j hjle
    have hU0 := hap j hjle
    have he' := he j hjle
    have he1 : e j ≤ 1 := he'.2.trans ((one_div_le_one_div_of_le (by norm_num) hm1).trans_eq (one_div_one))
    have hHU : H ≤ a j := hHX.trans hU.1
    let Ej := 3 * e j + 11 / H + H / a j + 1 / a j + 16 * η
    have hEj0 : 0 ≤ Ej := by dsimp [Ej] <;> positivity
    have hEj : Ej ≤ E := by
      have h3 := mul_le_mul_of_nonneg_left he'.2 (by norm_num : (0 : ℝ) ≤ 3)
      have hratio := div_le_div_of_nonneg_left hH0.le hX hU.1
      have hinv := one_div_le_one_div_of_le hX hU.1
      dsimp [Ej, E]
      simp only [div_eq_mul_inv] at h3 hratio hinv ⊢
      linarith only [h3, hratio, hinv]
    have hupper : (1 + e j) * (a j + H) ≤ 4 * X := by
      have hh := (ha (j + 1) (by omega)).2
      have heH := mul_le_mul_of_nonneg_right he1 hH0.le
      have hstep' := hstep j hjle
      nlinarith
    have hb := hblock f hf ⌊X⌋₊ ⌊4 * X⌋₊ (a j) H (e j) hU0 hH hHU he'.1 he1
      (Nat.floor_mono hU.1) (Nat.floor_mono hupper) A B hA hB hspectral
    rw [hstep j hjle] at hb
    have hraw : (∫ x in a j..a (j + 1), ‖complexShortAverage f H x‖ ^ 2) ≤
        a j * (C * (A + B * a j / H) + 2 * e j * Ej ^ 2) := by
      have hh : (∫ x in a j..a (j + 1), ‖complexShortAverage f H x‖ ^ 2) / a j ≤
          C * (A + B * a j / H) + 2 * e j * Ej ^ 2 := by
        simpa only [one_div_mul_eq_div, Ej] using hb
      simpa only [mul_comm] using (div_le_iff₀ hU0).mp hh
    have hmain : a j * (C * (A + B * a j / H)) ≤
        2 * X * C * (A + 2 * (B * X / H)) := by
      have hr : B * a j / H ≤ 2 * (B * X / H) := by
        calc
          _ ≤ B * (2 * X) / H := by gcongr; exact hU.2
          _ = _ := by ring
      calc
        _ ≤ (2 * X) * (C * (A + 2 * (B * X / H))) := by gcongr; exact hU.2
        _ = _ := by ring
    have herr : a j * (2 * e j * Ej ^ 2) ≤ 2 * (X / m) * E ^ 2 := by
      have heq : a j * (2 * e j * Ej ^ 2) = 2 * (X / m) * Ej ^ 2 := by
        dsimp [e]
        field_simp
      rw [heq]
      gcongr
    calc
      _ ≤ a j * (C * (A + B * a j / H)) + a j * (2 * e j * Ej ^ 2) := by
        simpa only [mul_add] using hraw
      _ ≤ _ := add_le_add hmain herr
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (a := a) (n := m) (fun j _ => complexShortAverage_sq_integrable f hf hH0 (a j) (a (j + 1)))
  rw [ha0, ham] at hsplit
  have hsum := sum_le_sum (fun j hj => hcell j (mem_range.mp hj))
  rw [hsplit, sum_const, nsmul_eq_mul, card_range] at hsum
  have hscale := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 1 / X by positivity)
  have hright : (1 / X) * ((m : ℝ) *
      (2 * X * C * (A + 2 * (B * X / H)) + 2 * (X / m) * E ^ 2)) =
      2 * (m : ℝ) * C * (A + 2 * (B * X / H)) + 2 * E ^ 2 := by field_simp
  rw [hright] at hscale
  have hlast : 2 * (m : ℝ) * C * (A + 2 * (B * X / H)) ≤
      4 * (m : ℝ) * C * (A + B * X / H) := by
    nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) * C by positivity) hA]
  exact hscale.trans (add_le_add hlast le_rfl)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ComplexShortIntegrability
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local integrability of arbitrary arithmetic short averages -/
namespace JointDickman.PublishedInputs
open Finset Filter MeasureTheory Classical

theorem complexShortAverage_sq_integrable_any (f : ArithmeticFunction ℂ)
    {H : ℝ} (hH : 0 < H) (a b : ℝ) :
    IntervalIntegrable (fun z => ‖complexShortAverage f H z‖^2) volume a b := by
  let S := range (⌊max a b+H⌋₊+1)
  let K := (∑ n ∈ S, ‖f n‖)/H
  have hK : 0 ≤ K := div_nonneg (sum_nonneg (fun _ _ => norm_nonneg _)) hH.le
  refine (intervalIntegrable_const (c := K^2)).mono_fun'
    (((measurable_complexShortAverage f H).norm.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with z hz
  have hbnd : ‖complexShortAverage f H z‖ ≤ K := by
    rw [complexShortAverage,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hH]
    apply div_le_div_of_nonneg_right _ hH.le
    refine (norm_sum_le _ _).trans (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _))
    intro n hn
    apply mem_range.mpr
    exact Nat.lt_succ_of_le ((mem_Ioc.mp hn).2.trans (Nat.floor_mono (by linarith [hz.2])))
  simpa only [Real.norm_eq_abs,abs_pow,abs_norm,abs_of_nonneg hK] using
    pow_le_pow_left₀ (norm_nonneg _) hbnd 2

end JointDickman.PublishedInputs

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ShortWindowEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mean-square control of short windows by a nonnegative long mean -/
namespace JointDickman
open Finset Filter MeasureTheory Classical

theorem shortWindowEnergy_integrable (E : ℕ → ℝ) (H : ℝ) (N : ℕ) (a b : ℝ) :
    IntervalIntegrable (shortWindowEnergy E H N) volume a b := by
  have hi (n : ℕ) : IntervalIntegrable
      ((Set.Ico ((n : ℝ)-H) n).indicator (fun _ => E n)) volume a b :=
    intervalIntegrable_iff.mpr ((intervalIntegrable_const (c := E n)).def'.indicator measurableSet_Ico)
  convert (IntervalIntegrable.sum (range N) (fun n _ => hi n)) using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [shortWindowEnergy,Finset.sum_apply]

theorem shortWindowEnergy_integral_le (E : ℕ → ℝ) (hE : ∀ n, 0 ≤ E n)
    {H a b : ℝ} (hH : 0 ≤ H) (hab : a ≤ b) (N : ℕ) :
    (∫ z in a..b, shortWindowEnergy E H N z) ≤ H*∑ n ∈ range N, E n := by
  unfold shortWindowEnergy
  rw [intervalIntegral.integral_finsetSum]
  · rw [mul_sum]
    apply sum_le_sum
    intro n _
    rw [intervalIntegral.integral_of_le hab,integral_indicator measurableSet_Ico,
      Measure.restrict_restrict measurableSet_Ico,setIntegral_const,smul_eq_mul]
    have hm := measureReal_mono (μ := volume)
      (show Set.Ico ((n : ℝ)-H) n ∩ Set.Ioc a b ⊆ Set.Ico ((n : ℝ)-H) n from Set.inter_subset_left)
      (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
    rw [Real.volume_real_Ico_of_le (by linarith)] at hm
    convert mul_le_mul_of_nonneg_right hm (hE n) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · intro n _
    apply intervalIntegrable_iff.mpr
    exact (intervalIntegrable_const (c := E n)).def'.indicator measurableSet_Ico

theorem shortWindowEnergy_eq (E : ℕ → ℝ) {H z : ℝ} (hH : 0 ≤ H) (hz : 0 ≤ z)
    {N : ℕ} (hN : ⌊z+H⌋₊ < N) :
    shortWindowEnergy E H N z = ∑ n ∈ Ioc ⌊z⌋₊ ⌊z+H⌋₊, E n := by
  have he (n : ℕ) : z ∈ Set.Ico ((n : ℝ)-H) n ↔ n ∈ Ioc ⌊z⌋₊ ⌊z+H⌋₊ := by
    rw [Set.mem_Ico,mem_Ioc,Nat.floor_lt hz,Nat.le_floor_iff (by linarith : 0 ≤ z+H)]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  unfold shortWindowEnergy
  simp only [Set.indicator_apply,he]
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter,mem_range,mem_Ioc]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨lt_of_le_of_lt h.2 hN,h⟩

theorem short_interval_card_le {H z : ℝ} (hH : 0 ≤ H) (hz : 0 ≤ z) :
    ((Ioc ⌊z⌋₊ ⌊z+H⌋₊).card : ℝ) ≤ H+1 := by
  rw [Nat.card_Ioc,Nat.cast_sub (Nat.floor_mono (by linarith : z ≤ z+H))]
  have hu := Nat.floor_le (by linarith : 0 ≤ z+H)
  have hl := Nat.lt_floor_add_one z
  linarith

theorem complexShortAverage_sq_le_window (f : ArithmeticFunction ℂ) (E : ℕ → ℝ)
    (hE : ∀ n, ‖f n‖^2 ≤ E n) {H z : ℝ} (hH : 1 ≤ H) (hz : 0 ≤ z)
    {N : ℕ} (hN : ⌊z+H⌋₊ < N) :
    ‖PublishedInputs.complexShortAverage f H z‖^2 ≤ (2/H)*shortWindowEnergy E H N z := by
  have hH0 : 0 < H := by linarith
  rw [shortWindowEnergy_eq E hH0.le hz hN]
  let S := Ioc ⌊z⌋₊ ⌊z+H⌋₊
  have hn := norm_sum_le S (fun n => f n)
  have hc := sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun n => ‖f n‖)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hc
  have hs := (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hc
  have he := sum_le_sum (s := S) (fun n _ => hE n)
  have hEn : 0 ≤ ∑ n ∈ S, E n := sum_nonneg (fun n _ => (sq_nonneg ‖f n‖).trans (hE n))
  have hcard : (S.card : ℝ) ≤ 2*H := (short_interval_card_le hH0.le hz).trans (by linarith)
  have hb : ‖∑ n ∈ S, f n‖^2 ≤ 2*H*∑ n ∈ S, E n :=
    hs.trans ((mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hcard hEn))
  rw [PublishedInputs.complexShortAverage,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hH0,div_pow]
  change ‖∑ n ∈ S, f n‖^2 / H^2 ≤ (2/H)*∑ n ∈ S, E n
  apply (div_le_iff₀ (sq_pos_of_pos hH0)).mpr
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  field_simp


theorem complexShortAverage_energy_le_prefix (f : ArithmeticFunction ℂ) (E : ℕ → ℝ)
    (hE : ∀ n, ‖f n‖^2 ≤ E n) {H X : ℝ} (hH : 1 ≤ H) (hX : 0 < X) (hHX : H ≤ X) :
    (1/X)*(∫ z in X..2*X, ‖PublishedInputs.complexShortAverage f H z‖^2) ≤
      2*(∑ n ∈ range (⌊3*X⌋₊+1), E n)/X := by
  have hH0 : 0 < H := by linarith
  have hE0 n : 0 ≤ E n := (sq_nonneg ‖f n‖).trans (hE n)
  have hi := intervalIntegral.integral_mono_on (by linarith : X ≤ 2*X)
    (PublishedInputs.complexShortAverage_sq_integrable_any f hH0 X (2*X))
    ((shortWindowEnergy_integrable E H (⌊3*X⌋₊+1) X (2*X)).const_mul (2/H))
    (fun z hz => complexShortAverage_sq_le_window f E hE hH (by linarith [hz.1])
      (show ⌊z+H⌋₊ < ⌊3*X⌋₊+1 from Nat.lt_succ_of_le (Nat.floor_mono (by linarith [hz.2]))))
  rw [intervalIntegral.integral_const_mul] at hi
  have he := shortWindowEnergy_integral_le E hE0 hH0.le (by linarith : X ≤ 2*X) (⌊3*X⌋₊+1)
  have h := hi.trans (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2/H))
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 1/X)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinEnergyAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centering and splitting the actual angular-frequency integrals -/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations

lemma angularMellinPolynomial_const_mul (K : Finset ℕ) (f : ℕ → ℂ) (c : ℂ) (t : ℝ) :
    angularMellinPolynomial K (fun n => c*f n) t = c*angularMellinPolynomial K f t := by
  simp only [angularMellinPolynomial,mul_div_assoc,mul_assoc,mul_sum]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_HalfArithmetic
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scaling a two-bounded arithmetic coefficient for the analytic transfer -/
namespace JointDickman
open Finset MeasureTheory PublishedInputs

lemma halfArithmetic_norm (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖≤2) (n : ℕ) :
    ‖halfArithmetic f n‖≤1 := by
  change ‖f n/2‖≤1
  rw [norm_div]
  norm_num
  linarith [hf n]

lemma halfArithmetic_polynomial (f : ArithmeticFunction ℂ) (K : Finset ℕ) (t : ℝ) :
    angularMellinPolynomial K (halfArithmetic f) t = angularMellinPolynomial K f t/2 := by
  rw [←mul_one_div (angularMellinPolynomial K f t) 2,mul_comm]
  rw [←angularMellinPolynomial_const_mul]
  congr 1
  funext n
  change f n/2=(1/2)*f n
  ring

lemma halfArithmetic_energy (f : ArithmeticFunction ℂ) (K : Finset ℕ) (T : ℝ) :
    (∫ t in -T..T, ‖angularMellinPolynomial K (halfArithmetic f) t‖^2) =
      (∫ t in -T..T, ‖angularMellinPolynomial K f t‖^2)/4 := by
  simp_rw [halfArithmetic_polynomial,norm_div,show ‖(2:ℂ)‖=(2:ℝ) by norm_num,div_pow]
  rw [show (2:ℝ)^2=4 by norm_num]
  rw [intervalIntegral.integral_div]

lemma halfArithmetic_short (f : ArithmeticFunction ℂ) (H z : ℝ) :
    complexShortAverage (halfArithmetic f) H z = complexShortAverage f H z/2 := by
  simp only [complexShortAverage,halfArithmetic,ArithmeticFunction.coe_mk]
  rw [←sum_div]
  ring

lemma halfArithmetic_short_energy (f : ArithmeticFunction ℂ) (H X : ℝ) :
    (1/X)*(∫ z in X..2*X, ‖complexShortAverage f H z‖^2) =
      4*((1/X)*(∫ z in X..2*X, ‖complexShortAverage (halfArithmetic f) H z‖^2)) := by
  simp_rw [halfArithmetic_short,norm_div,show ‖(2:ℂ)‖=(2:ℝ) by norm_num,div_pow]
  rw [show (2:ℝ)^2=4 by norm_num]
  rw [intervalIntegral.integral_div]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterDistanceInput
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published Dirichlet-character distance estimate

Only the fixed-modulus consequence of Klurman--Mangerel--Teräväinen,
*Multiplicative functions in short arithmetic progressions*, Proc. London
Math. Soc. 127 (2023), 366--446, Lemma 7.8, is assumed here. That lemma
bounds the infimum over `|t| ≤ 10X` by
`(1/4) log (log X / log (2 conductor χ)) + O(1)`.
For a fixed character the conductor term is absorbed in the constant.
The primes dividing the modulus only add nonnegative terms to our distance.
No modified character, bin label, or short average occurs in this input.
Source: https://doi.org/10.1112/plms.12546, arXiv:1909.12280, Lemma 7.8.
-/
namespace JointDickman
open Classical

theorem characterArithmetic_norm_le_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ‖characterArithmetic χ n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · simpa only [characterArithmetic,ArithmeticFunction.coe_mk,hn,ite_false, if_false] using χ.norm_le_one (n : ZMod q)

open Filter PublishedInputs
open scoped Topology


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_TwistedBinInterpolants
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual nonprincipal multiplicative interpolants -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem twistedWeightedBinInterpolant_norm_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (w : ArithmeticFunction ℝ) (hw : ∀ n, |w n| ≤ 1)
    {m : ℕ} (a : ι → Fin m) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖twistedWeightedBinInterpolant E w a χ n‖ ≤ 1 := by
  change ‖(weightedBinInterpolant E w a n : ℂ)*characterArithmetic χ n‖ ≤ 1
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul (abs_weightedBinInterpolant_le_one E w hw a n)
    (characterArithmetic_norm_le_one χ n) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_NonprincipalBinShort
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonprincipal short averages of the actual centered bin labels -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem twistedWeightedBinAverage_eq_combination {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (J : ℕ) (c : (ι → Fin (J+1)) → ℂ)
    (Y H z : ℝ)
    (hcoeff : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ Y →
      binLabel E ζ n-μ = ∑ a : ι → Fin (J+1), c a*(binLabel E (fun i => interpolationNode (a i)) n : ℂ))
    (hzH : z+H ≤ Y) :
    twistedWeightedBinAverage E ζ μ w χ H z =
      complexFiniteShort univ c (fun a => twistedWeightedBinInterpolant E w a χ) H z := by
  unfold twistedWeightedBinAverage complexFiniteShort complexShortAverage
  calc
    _ = (∑ n ∈ Ioc ⌊z⌋₊ ⌊z+H⌋₊, ∑ a : ι → Fin (J+1),
        c a*twistedWeightedBinInterpolant E w a χ n)/(H : ℂ) := by
      congr 1
      apply sum_congr rfl
      intro n hn
      have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
      have hnY : (n : ℝ) ≤ Y :=
        ((Nat.le_floor_iff' (by omega : n ≠ 0)).mp (mem_Ioc.mp hn).2).trans hzH
      rw [hcoeff n hn1 hnY,sum_mul,sum_mul]
      apply sum_congr rfl
      intro a _
      simp only [twistedWeightedBinInterpolant,ArithmeticFunction.coe_mk,
        weightedBinInterpolant,ArithmeticFunction.pmul_apply,Complex.ofReal_mul,
        characterArithmetic,show n ≠ 0 by omega,ite_false, if_false]
      ring
    _ = _ := by
      rw [sum_comm]
      simp only [sum_div,mul_sum]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro n _
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_PrincipalBinRestriction
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Principal characters are exact finite-prime restrictions -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem coprimePrimeWeight_eq (P : Finset ℕ) (t : ℕ → ℝ) {q : ℕ} (hq : q ≠ 0) (n : ℕ) :
    coprimePrimeWeight P t q n = if n.Coprime q then finitePrimeWeight P t n else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [coprimePrimeWeight]
  unfold coprimePrimeWeight
  simp only [finitePrimeWeight,ArithmeticFunction.coe_mk,hn,ite_false, if_false]
  by_cases hc : n.Coprime q
  · rw [ite_eq_left hc]
    have hd p (hp : p ∈ q.primeFactors) : ¬p ∣ n := by
      intro hpn
      have hpp := Nat.mem_primeFactors.mp hp
      exact hpp.1.ne_one (Nat.eq_one_of_dvd_coprimes hc hpn hpp.2.1)
    rw [prod_union_eq_left (fun p hp _ => by simp [hd p hp])]
    apply prod_congr rfl
    intro p _
    by_cases hp : p ∈ q.primeFactors
    · simp [hd p hp]
    · simp [hp]
  · rw [ite_eq_right hc]
    obtain ⟨p,hp,hpn,hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hpQ : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hpq,hq⟩
    exact prod_eq_zero (mem_union_right P hpQ) (by simp [hpn,hpQ])

theorem principal_twistedWeightedBinAverage {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (P : Finset ℕ) (t : ℕ → ℝ)
    {q : ℕ} [NeZero q] (H z : ℝ) :
    twistedWeightedBinAverage E ζ μ (finitePrimeWeight P t) (1 : DirichletCharacter ℂ q) H z =
      weightedBinAverage E ζ μ (coprimePrimeWeight P t q) H z := by
  unfold twistedWeightedBinAverage weightedBinAverage
  congr 1
  apply sum_congr rfl
  intro n _
  rw [coprimePrimeWeight_eq P t (NeZero.ne q)]
  by_cases hc : n.Coprime q
  · rw [ite_eq_left hc,MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hc),mul_one]
  · rw [ite_eq_right hc,MulChar.map_nonunit _ (fun h => hc ((ZMod.isUnit_iff_coprime n q).mp h))]
    simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_UnitProgressionBinAverage
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Character decomposition of unit-class bin averages -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem complex_progression_sum_characters {q : ℕ} [NeZero q]
    (S : Finset ℕ) (g : ℕ → ℂ) (r : (ZMod q)ˣ) :
    (q.totient : ℂ)*(∑ n ∈ S, if (n : ZMod q) = r then g n else 0) =
      ∑ χ : DirichletCharacter ℂ q, χ (r⁻¹ : (ZMod q)ˣ)*∑ n ∈ S, g n*χ (n : ZMod q) := by
  rw [mul_sum]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  calc
    _ = g n*(if (r : ZMod q) = (n : ZMod q) then (q.totient : ℂ) else 0) := by
      split_ifs <;> simp_all
      ring
    _ = g n*∑ χ : DirichletCharacter ℂ q, χ (r⁻¹ : (ZMod q)ˣ)*χ (n : ZMod q) := by
      rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ r.isUnit,ZMod.inv_coe_unit]
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro χ _; ring

theorem unitProgressionBinAverage_characters {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} [NeZero q] (r : (ZMod q)ˣ) (H z : ℝ) :
    unitProgressionBinAverage E ζ μ w r H z =
      (∑ χ : DirichletCharacter ℂ q, χ (r⁻¹ : (ZMod q)ˣ)*
        twistedWeightedBinAverage E ζ μ w χ H z)/(q.totient : ℂ) := by
  have hφ : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  apply (eq_div_iff hφ).mpr
  rw [mul_comm]
  have he := congrArg (fun x : ℂ => x/(H : ℂ))
    (complex_progression_sum_characters (Ioc ⌊z⌋₊ ⌊z+H⌋₊)
      (fun n => (binLabel E ζ n-μ)*(w n : ℂ)) r)
  simpa only [unitProgressionBinAverage,twistedWeightedBinAverage,mul_div_assoc,sum_div] using he

theorem unitProgressionBinAverage_square_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} [NeZero q] (r : (ZMod q)ˣ) (H z : ℝ) :
    ‖unitProgressionBinAverage E ζ μ w r H z‖^2 ≤
      (∑ χ : DirichletCharacter ℂ q, ‖twistedWeightedBinAverage E ζ μ w χ H z‖^2)/(q.totient : ℝ) := by
  let F := fun χ : DirichletCharacter ℂ q => twistedWeightedBinAverage E ζ μ w χ H z
  have hc : (Fintype.card (DirichletCharacter ℂ q) : ℝ) = q.totient := by
    rw [← Nat.card_eq_fintype_card,DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  have hn : ‖∑ χ : DirichletCharacter ℂ q, χ (r⁻¹ : (ZMod q)ˣ)*F χ‖ ≤ ∑ χ, ‖F χ‖ := by
    simpa only [norm_mul,DirichletCharacter.unit_norm_eq_one,one_mul] using
      norm_sum_le univ (fun χ : DirichletCharacter ℂ q => χ (r⁻¹ : (ZMod q)ˣ)*F χ)
  have hs := sum_mul_sq_le_sq_mul_sq univ (fun _ : DirichletCharacter ℂ q => (1 : ℝ)) (fun χ => ‖F χ‖)
  simp only [one_mul,one_pow,sum_const,card_univ,nsmul_eq_mul,mul_one,hc] at hs
  have he := (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hs
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [unitProgressionBinAverage_characters,norm_div,Complex.norm_natCast,div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hφ)).mpr
  change _ ≤ ((∑ χ, ‖F χ‖^2)/(q.totient : ℝ))*(q.totient : ℝ)^2
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_FairLaplaceFeature
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fair-split Laplace features are finite-prime multiplicative weights -/
namespace JointDickman
open Finset Classical

theorem primeLaplaceFeature_at_integer (Q : Finset ℕ) (B v : ℝ) {n : ℕ} (hn : n ≠ 0) :
    primeLaplaceFeature Q B v (fun p => decide (p.val ∣ n)) =
      finitePrimeWeight Q (fun p => (1+(p : ℝ)^(-v/B))/2) n := by
  simp only [finitePrimeWeight,ArithmeticFunction.coe_mk,hn,ite_false, if_false,primeLaplaceFeature,
    decide_eq_true_eq]
  exact prod_coe_sort Q (fun p => if p ∣ n then (1+(p : ℝ)^(-v/B))/2 else 1)

theorem primeLaplaceWeight_bounds {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime)
    {B v : ℝ} (hB : 0 ≤ B) (hv : 0 ≤ v) (p : ℕ) (hp : p ∈ Q) :
    0 ≤ (1+(p : ℝ)^(-v/B))/2 ∧ (1+(p : ℝ)^(-v/B))/2 ≤ 1 := by
  have hpow : (p : ℝ)^(-v/B) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (hQ p hp).one_lt.le)
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv) hB)
  exact ⟨by positivity,by linarith⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSiteMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual divisibility-site mean is the independent prime law -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem uniform_zero_bit_mass (p : ℕ) [NeZero p] (b : Bool) :
    finitePushMass (fun _ : ZMod p => (1 : ℝ)/p) (fun a => decide (a = 0)) b =
      bernoulliBitMass (1/(p : ℝ)) b := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  cases b
  · simp [finitePushMass,bernoulliBitMass]
    have he (x : ZMod p) : (if x = 0 then 0 else (p : ℝ)⁻¹) =
        (p : ℝ)⁻¹ - (if x = 0 then (p : ℝ)⁻¹ else 0) := by split_ifs <;> simp
    simp_rw [he]
    rw [sum_sub_distrib]
    simp [hp]
  · simp [finitePushMass,bernoulliBitMass]

theorem uniform_prime_site_mean (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (F : (Q → Bool) → ℝ) :
    (∑ n ∈ range (∏ p : Q, p.val), F (fun p => decide (p.val ∣ n))) /
      (∏ p : Q, (p.val : ℝ)) = ∑ x, fullPrimeMass Q x*F x := by
  let : ∀ p : Q, NeZero p.val := fun p => ⟨(hQ p p.property).ne_zero⟩
  have hcop : Pairwise (fun p q : Q => p.val.Coprime q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (hQ p p.property) (hQ q q.property)).mpr
      (fun h => hpq (Subtype.ext h))
  have hcrt := crt_uniform_mean (fun p : Q => p.val) hcop
    (fun x => F (fun p => decide (x p = 0)))
  have hpush := finiteProductMass_pushforward_test
    (fun p : Q => fun _ : ZMod p.val => (1 : ℝ)/p.val)
    (fun p : Q => fun a : ZMod p.val => decide (a = 0)) (fun x => (F x : ℂ))
  have hlocal : (fun p : Q => finitePushMass
      (fun _ : ZMod p.val => (1 : ℝ)/p.val) (fun a => decide (a = 0))) =
      (fun p : Q => bernoulliBitMass (1/(p.val : ℝ))) := by
    funext p b
    exact uniform_zero_bit_mass p.val b
  rw [hlocal] at hpush
  have hpushR : (∑ x, fullPrimeMass Q x*F x) =
      ∑ x, finiteProductMass (fun p : Q => fun _ : ZMod p.val => (1 : ℝ)/p.val) x *
        F (fun p => decide (x p = 0)) := by
    exact_mod_cast hpush
  rw [hpushR]
  simpa only [ZMod.natCast_eq_zero_iff] using hcrt

theorem prime_site_average_tendsto (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (F : (Q → Bool) → ℝ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, F (fun p => decide (p.val ∣ n)))/(N : ℝ))
      atTop (𝓝 (∑ x, fullPrimeMass Q x*F x)) := by
  let : ∀ p : Q, NeZero p.val := fun p => ⟨(hQ p p.property).ne_zero⟩
  let : NeZero (∏ p : Q, p.val) := ⟨prod_ne_zero_iff.mpr (fun p _ => NeZero.ne p.val)⟩
  have hcop : Pairwise (fun p q : Q => p.val.Coprime q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (hQ p p.property) (hQ q q.property)).mpr
      (fun h => hpq (Subtype.ext h))
  let e := ZMod.prodEquivPi (fun p : Q => p.val) hcop
  let f : ZMod (∏ p : Q, p.val) → ℂ := fun a => (F (fun p => decide (e a p = 0)) : ℂ)
  have he (n : ℕ) : e (n : ZMod (∏ p : Q, p.val)) = (n : ∀ p : Q, ZMod p.val) := map_natCast e n
  have hm : residueMean f = (∑ x, fullPrimeMass Q x*F x : ℝ) := by
    rw [residueMean,residue_sum_eq_range]
    dsimp only [f]
    simp only [he,Pi.natCast_apply,ZMod.natCast_eq_zero_iff]
    have hh := uniform_prime_site_mean Q hQ F
    have hc := congrArg (fun r : ℝ => (r : ℂ)) hh
    push_cast at hc
    simpa only [Nat.cast_prod,Complex.ofReal_sum,Complex.ofReal_mul] using hc
  have ht := (Complex.continuous_re.tendsto _).comp (periodicAverage_tendsto f)
  rw [hm] at ht
  change Tendsto (fun N => (periodicAverage f N).re) atTop _ at ht
  simpa only [periodicAverage,f,he,Pi.natCast_apply,ZMod.natCast_eq_zero_iff,
    ← Complex.ofReal_sum,← Complex.ofReal_natCast,← Complex.ofReal_div,Complex.ofReal_re,
    Function.comp_apply] using ht

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSitePrefix
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scaled prefix means of the finite prime law -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem prefix_scaled_sum_tendsto (f : ℕ → ℝ) {L A : ℝ} (hA : 0 < A)
    (hf : Tendsto (fun N : ℕ => (∑ n ∈ range N, f n)/(N : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun x : ℝ => (∑ n ∈ range (⌊A*x⌋₊+1), f n)/x) atTop (𝓝 (A*L)) := by
  have hAx : Tendsto (fun x : ℝ => A*x) atTop atTop := tendsto_id.const_mul_atTop hA
  have hN : Tendsto (fun x : ℝ => ⌊A*x⌋₊+1) atTop atTop :=
    tendsto_atTop_mono (fun x => Nat.le_add_right ⌊A*x⌋₊ 1) (tendsto_nat_floor_atTop.comp hAx)
  have hfloor := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hAx
  have hsmall : Tendsto (fun x : ℝ => 1/x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hratio : Tendsto (fun x : ℝ => ((⌊A*x⌋₊+1 : ℕ) : ℝ)/x) atTop (𝓝 A) := by
    have hh := (hfloor.mul_const A).add hsmall
    simp only [one_mul,add_zero,Function.comp_def] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hAx0 : A*x ≠ 0 := (mul_pos hA hx).ne'
    push_cast
    field_simp
  have hh := hratio.mul (hf.comp hN)
  apply hh.congr'
  filter_upwards [] with x
  have hN0 : ((⌊A*x⌋₊+1 : ℕ) : ℝ) ≠ 0 := by positivity
  dsimp only [Function.comp_def]
  field_simp

theorem prime_site_scaled_sum_tendsto (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (F : (Q → Bool) → ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ =>
      (∑ n ∈ range (⌊A*x⌋₊+1), F (fun p => decide (p.val ∣ n)))/x)
      atTop (𝓝 (A*∑ y, fullPrimeMass Q y*F y)) :=
  prefix_scaled_sum_tendsto _ hA (prime_site_average_tendsto Q hQ F)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeWindowError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime-law errors control all bounded short-window tests -/
namespace JointDickman
open Finset Filter MeasureTheory Classical
open scoped Topology

theorem prime_site_window_energy_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (E : (Q → Bool) → ℝ) {H : ℝ} (hH : 1 ≤ H) {A : ℝ} (hA : 0 < A)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ f : ArithmeticFunction ℂ,
      (∀ k, ‖f k‖^2 ≤ E (fun p => decide (p.val ∣ k))) →
      (1/(A*scale n))*(∫ z in (A*scale n)..2*(A*scale n),
        ‖PublishedInputs.complexShortAverage f H z‖^2) <
          6*(∑ x, fullPrimeMass Q x*E x)+ε := by
  have hX : Tendsto (fun n => A*scale n) atTop atTop := hscale.const_mul_atTop hA
  have ht := ((prime_site_scaled_sum_tendsto Q hQ E (by norm_num : (0 : ℝ) < 3)).const_mul 2).comp hX
  have ht' : Tendsto (fun n =>
      2*(∑ k ∈ range (⌊3*(A*scale n)⌋₊+1), E (fun p => decide (p.val ∣ k)))/(A*scale n))
      atTop (𝓝 (6*∑ x, fullPrimeMass Q x*E x)) := by
    convert ht using 1
    · ext n
      dsimp only [Function.comp_apply]
      ring
    · congr 1
      ring
  filter_upwards [hX.eventually_gt_atTop 0,hX.eventually_ge_atTop H,
    ht'.eventually (eventually_lt_nhds (lt_add_of_pos_right _ hε))] with n hn hHn he
  intro f hf
  exact (complexShortAverage_energy_le_prefix f _ hf hH hn hHn).trans_lt he

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_UnitProgressionBinShort
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted centered-bin short averages in every unit residue class -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem twistedWeightedBinAverage_sq_integrable {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) {H : ℝ} (hH : 0 < H) (a b : ℝ) :
    IntervalIntegrable (fun z => ‖twistedWeightedBinAverage E ζ μ w χ H z‖^2) volume a b := by
  let f : ArithmeticFunction ℂ := ⟨fun n => (binLabel E ζ n-μ)*(w n : ℂ)*χ (n : ZMod q),by simp⟩
  exact complexShortAverage_sq_integrable_any f hH a b

theorem unitProgressionBinAverage_sq_integrable {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (r : (ZMod q)ˣ) {H : ℝ} (hH : 0 < H) (a b : ℝ) :
    IntervalIntegrable (fun z => ‖unitProgressionBinAverage E ζ μ w r H z‖^2) volume a b := by
  let f : ArithmeticFunction ℂ := ⟨fun n => if (n : ZMod q) = r then
    (binLabel E ζ n-μ)*(w n : ℂ) else 0,by split_ifs <;> simp⟩
  exact complexShortAverage_sq_integrable_any f hH a b

theorem unitProgressionBinAverage_energy_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} [NeZero q] (r : (ZMod q)ˣ) {H X : ℝ} (hH : 0 < H) (hX : 0 < X) :
    (1/X)*(∫ z in X..2*X, ‖unitProgressionBinAverage E ζ μ w r H z‖^2) ≤
      (1/(q.totient : ℝ))*∑ χ : DirichletCharacter ℂ q,
        (1/X)*(∫ z in X..2*X, ‖twistedWeightedBinAverage E ζ μ w χ H z‖^2) := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hfi (χ : DirichletCharacter ℂ q) := twistedWeightedBinAverage_sq_integrable E ζ μ w χ hH X (2*X)
  have hsum : IntervalIntegrable (fun z =>
      (∑ χ : DirichletCharacter ℂ q, ‖twistedWeightedBinAverage E ζ μ w χ H z‖^2)/(q.totient : ℝ))
      volume X (2*X) := by
    simpa only [Finset.sum_apply] using (IntervalIntegrable.sum univ (fun χ _ => hfi χ)).div_const (q.totient : ℝ)
  have he := intervalIntegral.integral_mono (by linarith : X ≤ 2*X)
    (unitProgressionBinAverage_sq_integrable E ζ μ w r hH X (2*X)) hsum
    (unitProgressionBinAverage_square_le E ζ μ w r H)
  have hh := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 1/X)
  rw [intervalIntegral.integral_div,intervalIntegral.integral_finsetSum (fun χ _ => hfi χ)] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [← mul_sum]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeFeatureShortError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replacing prime features inside centered bin short averages -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem primeSiteWeight_laplace (Q : Finset ℕ) (B : ℝ) (V : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) :
    primeSiteWeight Q (fun x => ∑ v ∈ V, a v*primeLaplaceFeature Q B v x) n =
      ∑ v ∈ V, a v*finitePrimeWeight Q (fun p => (1+(p : ℝ)^(-(v : ℝ)/B))/2) n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [primeSiteWeight_apply Q _ hn]
    apply sum_congr rfl
    intro v _
    rw [primeLaplaceFeature_at_integer Q B v hn]

theorem unit_prime_feature_error
    {ι : Type*} [Fintype ι] (ζ : ι → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (F G : (Q → Bool) → ℝ) {H A : ℝ} (hH : 1 ≤ H) (hA : 0 < A)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    {q : ℕ} [NeZero q] {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (E : ι → Finset ℕ) (r : (ZMod q)ˣ),
      (1/(A*scale n))*(∫ z in (A*scale n)..2*(A*scale n),
        ‖unitProgressionBinAverage E ζ μ (primeSiteWeight Q F) r H z-
          unitProgressionBinAverage E ζ μ (primeSiteWeight Q G) r H z‖^2) <
      24*(∑ x, fullPrimeMass Q x*(F x-G x)^2)+ε := by
  have hh := prime_site_window_energy_bound Q hQ (fun x => 4*(F x-G x)^2)
    hH hA scale hscale hε
  filter_upwards [hh] with n hn
  intro E r
  let f : ArithmeticFunction ℂ := ⟨fun k => if (k : ZMod q) = r then
    (binLabel E ζ k-μ)*((primeSiteWeight Q F k : ℂ)-(primeSiteWeight Q G k : ℂ)) else 0,
    by split_ifs <;> simp⟩
  have hf k : ‖f k‖^2 ≤ 4*(F (fun p => decide (p.val ∣ k))-G (fun p => decide (p.val ∣ k)))^2 := by
    by_cases hk : k = 0
    · subst k
      rw [ArithmeticFunction.map_zero,norm_zero,zero_pow (by decide : 2 ≠ 0)]
      positivity
    by_cases hr : (k : ZMod q) = r
    · simp only [f,ArithmeticFunction.coe_mk,hr,ite_true, if_true,primeSiteWeight_apply Q _ hk,
        ← Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
      have hc := pow_le_pow_left₀ (norm_nonneg _) (norm_centered_binLabel_le_two E ζ hζ μ hμ k) 2
      exact mul_le_mul_of_nonneg_right (by norm_num at hc ⊢; exact hc) (sq_nonneg _)
    · have hz : f k = 0 := by simp [f,hr]
      rw [hz,norm_zero,zero_pow (by decide : 2 ≠ 0)]
      positivity
  have hshort z : complexShortAverage f H z =
      unitProgressionBinAverage E ζ μ (primeSiteWeight Q F) r H z-
        unitProgressionBinAverage E ζ μ (primeSiteWeight Q G) r H z := by
    unfold complexShortAverage unitProgressionBinAverage
    rw [← sub_div,← sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro k _
    simp only [f,ArithmeticFunction.coe_mk]
    split_ifs <;> ring
  have he := hn f hf
  simp only [hshort] at he
  have hid : (∑ x, fullPrimeMass Q x*(4*(F x-G x)^2)) =
      4*∑ x, fullPrimeMass Q x*(F x-G x)^2 := by rw [mul_sum]; congr 1; ext x; ring
  rw [hid] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LaplaceBinShort
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Laplace combinations have centered short averages -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem measurable_unitProgressionBinAverage {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (r : (ZMod q)ˣ) (H : ℝ) :
    Measurable (unitProgressionBinAverage E ζ μ w r H) := by
  let f : ArithmeticFunction ℂ := ⟨fun n => if (n : ZMod q) = r then
    (binLabel E ζ n-μ)*(w n : ℂ) else 0,by split_ifs <;> simp⟩
  exact measurable_complexShortAverage f H

theorem unit_laplace_combination {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (Q : Finset ℕ)
    (B : ℝ) (V : Finset ℕ) (a : ℕ → ℝ) {q : ℕ} (r : (ZMod q)ˣ) (H z : ℝ) :
    unitProgressionBinAverage E ζ μ
      (primeSiteWeight Q (fun x => ∑ v ∈ V, a v*primeLaplaceFeature Q B v x)) r H z =
    ∑ v ∈ V, (a v : ℂ)*unitProgressionBinAverage E ζ μ
      (finitePrimeWeight Q (fun p => (1+(p : ℝ)^(-(v : ℝ)/B))/2)) r H z := by
  unfold unitProgressionBinAverage
  simp only [primeSiteWeight_laplace,Complex.ofReal_sum,Complex.ofReal_mul,← mul_div_assoc]
  rw [← sum_div]
  congr 1
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  by_cases hk : (k : ZMod q) = r
  · simp only [hk,ite_true, if_true]
    apply sum_congr rfl
    intro v _
    ring
  · simp [hk]

theorem finite_complex_sum_energy {ι : Type*} (V : Finset ι) (a : ι → ℂ)
    (g : ι → ℝ → ℂ) {X : ℝ} (hX : 0 < X)
    (hg : ∀ v ∈ V, IntervalIntegrable (fun z => ‖g v z‖^2) volume X (2*X))
    (hgm : ∀ v ∈ V, AEStronglyMeasurable (g v) (volume.restrict (Set.uIoc X (2*X)))) :
    (1/X)*(∫ z in X..2*X, ‖∑ v ∈ V, a v*g v z‖^2) ≤
      (∑ v ∈ V, ‖a v‖^2)*∑ v ∈ V, (1/X)*(∫ z in X..2*X, ‖g v z‖^2) := by
  have hK : 0 ≤ ∑ v ∈ V, ‖a v‖^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hb z : ‖∑ v ∈ V, a v*g v z‖^2 ≤
      (∑ v ∈ V, ‖a v‖^2)*(∑ v ∈ V, ‖g v z‖^2) := by
    have hn : ‖∑ v ∈ V, a v*g v z‖ ≤ ∑ v ∈ V, ‖a v‖*‖g v z‖ := by
      simpa only [norm_mul] using norm_sum_le V (fun v => a v*g v z)
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
      (sum_mul_sq_le_sq_mul_sq V (fun v => ‖a v‖) (fun v => ‖g v z‖))
  have hi : IntervalIntegrable (fun z => (∑ v ∈ V, ‖a v‖^2)*∑ v ∈ V, ‖g v z‖^2)
      volume X (2*X) := by
    simpa only [Finset.sum_apply] using (IntervalIntegrable.sum V hg).const_mul (∑ v ∈ V, ‖a v‖^2)
  have hs : IntervalIntegrable (fun z => ‖∑ v ∈ V, a v*g v z‖^2) volume X (2*X) := by
    apply hi.mono_fun'
    · convert ((Finset.aestronglyMeasurable_sum V (fun v hv => (hgm v hv).const_mul (a v))).norm.pow 2) using 1
      all_goals try with_reducible_and_instances rfl
      ext z
      simp only [Pi.pow_apply,Finset.sum_apply]
    · exact Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using hb z)
  have he := intervalIntegral.integral_mono (by linarith : X ≤ 2*X) hs hi hb
  have hh := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 1/X)
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum hg] at hh
  simpa only [mul_sum,mul_assoc,mul_left_comm (1/X)] using hh


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_FiniteShortComponents
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing proved component short estimates to finite combinations -/
namespace JointDickman.PublishedInputs
open Finset Filter MeasureTheory
open scoped Topology

theorem complexFiniteShort_of_components {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (f : ℕ → ℕ → ι → ArithmeticFunction ℂ)
    (hf : ∀ B n i, i∈S → ∀ k, ‖f B n i k‖≤1)
    (H : ℕ → ℝ) (X : ℕ → ℕ → ℝ)
    (hH : Tendsto H atTop atTop) (hX : ∀ B, Tendsto (X B) atTop atTop)
    (hcomponent : ∀ i∈S, ∀ ε : ℝ, 0<ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/X B n)*(∫ z in X B n..2*X B n, ‖complexShortAverage (f B n i) (H B) z‖^2)<ε) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/X B n)*(∫ z in X B n..2*X B n, ‖complexFiniteShort S c (f B n) (H B) z‖^2)<ε := by
  intro ε hε
  let K := (∑ i ∈ S, ‖c i‖^2)*(S.card : ℝ)
  have hK : 0 ≤ K := mul_nonneg (sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)
  let δ := ε/(K+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall i (hi : i ∈ S) := hcomponent i hi δ hδ
  filter_upwards [(eventually_all_finset S).mpr hsmall,hH.eventually_gt_atTop 0] with B hsmall hHB
  filter_upwards [(eventually_all_finset S).mpr hsmall,(hX B).eventually_gt_atTop 0] with n hsmall hXB
  have he := complexFiniteShort_energy_le S c (f B n) (hf B n) hHB hXB
  have hs : (∑ i ∈ S, (1/X B n)*(∫ z in X B n..2*X B n,
      ‖complexShortAverage (f B n i) (H B) z‖^2)) ≤ (S.card : ℝ)*δ := by
    simpa only [sum_const,nsmul_eq_mul] using sum_le_sum (fun i hi => (hsmall i hi).le)
  have he' := he.trans (mul_le_mul_of_nonneg_left hs (sum_nonneg (fun _ _ => sq_nonneg _)))
  have hkδ : K*δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < K+1)).mpr
    nlinarith
  exact he'.trans_lt (by simpa only [K,mul_assoc] using hkδ)


end JointDickman.PublishedInputs

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ShortAffineBudget
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The vanishing budgets used by the actual short-average applications -/
namespace JointDickman
open Filter
open scoped Topology

theorem canonical_affine_application_budget (C d k e : ℝ) :
    Tendsto (fun H => d/H+k*canonicalAffineBase C H+
      (k*canonicalAffineSlope C H+e)/H) atTop (𝓝 0) := by
  have hh := ((canonical_affine_budget C).const_mul k).add
    (tendsto_inv_atTop_zero.const_mul (d+e))
  simp only [mul_zero,add_zero] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext H
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinShortLimit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The qualitative short-interval consequence of a vanishing spectral budget -/
namespace JointDickman
open Finset Filter MeasureTheory PublishedInputs
open scoped Topology

lemma exists_mellin_smoothing_parameters {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∃ m : ℕ, 0 < m ∧
      2 * (3 / (m : ℝ) + 16 * η) ^ 2 < ε := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 3) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hi := tendsto_inv_atTop_zero.comp hden
  have ht : Tendsto (fun n : ℕ => 2 * (19 / ((n : ℝ) + 3)) ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero, zero_pow (by norm_num : 2 ≠ 0)] using
      ((hi.const_mul 19).pow 2).const_mul 2
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨1 / ((n : ℝ) + 3), by positivity, ?_, n + 3, by omega, ?_⟩
  · apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 3) (by norm_num : (0 : ℝ) < 2)).mpr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  · convert hn using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MellinFloorEndpoints
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded floor discrepancy between real and integer dyadic cutoffs -/
namespace JointDickman
open Finset MeasureTheory

lemma mellinPolynomial_consecutive (a : ℕ → ℂ) {K L N : ℕ}
    (hKL : K ≤ L) (hLN : L ≤ N) (t : ℝ) :
    mellinPolynomial (Ioc K N) a t =
      mellinPolynomial (Ioc K L) a t + mellinPolynomial (Ioc L N) a t := by
  simp only [mellinPolynomial_eq_angular]
  exact angularMellinPolynomial_consecutive a hKL hLN _

lemma norm_mellinPolynomial_interval_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    {K L : ℕ} (hK : 0 < K) (_hKL : K ≤ L) (t : ℝ) :
    ‖mellinPolynomial (Ioc K L) a t‖ ≤ (L - K : ℕ) / (K : ℝ) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold mellinPolynomial
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _n ∈ Ioc K L, 1 / (K : ℝ) := by
      apply sum_le_sum
      intro n hn
      have hKn : K ≤ n := (mem_Ioc.mp hn).1.le
      have hnr : (0 : ℝ) < n := hKr.trans_le (by exact_mod_cast hKn)
      rw [norm_mul, norm_additivePhase, mul_one, norm_div, Complex.norm_natCast]
      exact (div_le_div_of_nonneg_right (ha n) hnr.le).trans
        (one_div_le_one_div_of_le hKr (by exact_mod_cast hKn))
    _ = _ := by simp [Nat.card_Ioc, div_eq_mul_inv]

lemma nat_floor_four_bounds {X : ℝ} (hX : 0 ≤ X) :
    4 * ⌊X⌋₊ ≤ ⌊4 * X⌋₊ ∧ ⌊4 * X⌋₊ ≤ 4 * ⌊X⌋₊ + 3 := by
  have hlo := Nat.floor_le hX
  have hhi := Nat.lt_floor_add_one X
  constructor
  · apply Nat.le_floor
    push_cast
    linarith
  · have hh : ⌊4 * X⌋₊ < 4 * ⌊X⌋₊ + 4 := by
      apply (Nat.floor_lt (by positivity : (0 : ℝ) ≤ 4 * X)).mpr
      push_cast
      linarith
    omega

/-- The three possible extra floor-endpoint terms contribute only `O(T/N²)`
to the spectral energy. -/
theorem mellinPolynomial_real_cutoff_energy (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    {X A B : ℝ} (hX : 1 ≤ X)
    (hbound : ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖mellinPolynomial (Ioc ⌊X⌋₊ (4 * ⌊X⌋₊)) a t‖ ^ 2) ≤ A + B * T) :
    ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖mellinPolynomial (Ioc ⌊X⌋₊ ⌊4 * X⌋₊) a t‖ ^ 2) ≤
        2 * A + (2 * B + 3 / (⌊X⌋₊ : ℝ) ^ 2) * T := by
  let N := ⌊X⌋₊
  have hN : 0 < N := by
    change 0 < ⌊X⌋₊
    exact Nat.floor_pos.mpr hX
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hlo, hhi⟩ := nat_floor_four_bounds (show 0 ≤ X by linarith)
  have htail (t : ℝ) : ‖mellinPolynomial (Ioc (4 * N) ⌊4 * X⌋₊) a t‖ ≤ 3 / (4 * (N : ℝ)) := by
    have hh := norm_mellinPolynomial_interval_le a ha
      (show 0 < 4 * N by omega) hlo t
    have hdiff : ⌊4 * X⌋₊ - 4 * N ≤ 3 := by omega
    have hdiff' : ((⌊4 * X⌋₊ - 4 * N : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hdiff
    apply hh.trans
    push_cast
    exact div_le_div_of_nonneg_right hdiff' (by positivity)
  intro T hT
  have hpoint (t : ℝ) : ‖mellinPolynomial (Ioc N ⌊4 * X⌋₊) a t‖ ^ 2 ≤
      2 * ‖mellinPolynomial (Ioc N (4 * N)) a t‖ ^ 2 + 2 * (3 / (4 * (N : ℝ))) ^ 2 := by
    rw [mellinPolynomial_consecutive a (by omega : N ≤ 4 * N) hlo]
    have hh := norm_add_le (mellinPolynomial (Ioc N (4 * N)) a t)
      (mellinPolynomial (Ioc (4 * N) ⌊4 * X⌋₊) a t)
    have hb := htail t
    have hn := norm_nonneg (mellinPolynomial (Ioc N (4 * N)) a t)
    have ht := norm_nonneg (mellinPolynomial (Ioc (4 * N) ⌊4 * X⌋₊) a t)
    have hs := norm_nonneg (mellinPolynomial (Ioc N (4 * N)) a t +
      mellinPolynomial (Ioc (4 * N) ⌊4 * X⌋₊) a t)
    have he : 0 ≤ 3 / (4 * (N : ℝ)) := by positivity
    nlinarith [sq_nonneg (‖mellinPolynomial (Ioc N (4 * N)) a t‖ - 3 / (4 * (N : ℝ)))]
  have hI (L U : ℕ) : IntervalIntegrable
      (fun t => ‖mellinPolynomial (Ioc L U) a t‖ ^ 2) volume (-T) T :=
    ((continuous_mellinPolynomial _ _).norm.pow 2).intervalIntegrable _ _
  have hi := intervalIntegral.integral_mono (by linarith : -T ≤ T) (hI _ _)
    (((hI _ _).const_mul 2).add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_add ((hI _ _).const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  have herr : (T - -T) * (2 * (3 / (4 * (N : ℝ))) ^ 2) ≤ 3 / (N : ℝ) ^ 2 * T := by
    field_simp
    nlinarith
  have hb := hbound T hT
  change (∫ t in -T..T, ‖mellinPolynomial (Ioc N (4 * N)) a t‖ ^ 2) ≤ A + B * T at hb
  change (∫ t in -T..T, ‖mellinPolynomial (Ioc N ⌊4 * X⌋₊) a t‖ ^ 2) ≤ _
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ShortAffineDyadic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A quantitative short-average consequence of two affine dyadic bounds -/
namespace JointDickman
open Finset MeasureTheory PublishedInputs

lemma short_affine_budget {X H a b : ℝ} {N : ℕ}
    (hN : 1≤(N:ℝ)) (hXN : X≤2*N) (hH : 0<H) (_ha : 0≤a) (hb : 0≤b) :
    8*a+(8*b/(N:ℝ)+3/(N:ℝ)^2)*X/H ≤ 8*a+16*b/H+6/H := by
  have hn : (0:ℝ)<N := by linarith
  have h1 : X/(N:ℝ)≤2 := (div_le_iff₀ hn).mpr (by nlinarith only [hXN])
  have h2 : X/(N:ℝ)^2≤2 := (div_le_iff₀ (sq_pos_of_pos hn)).mpr (by
    nlinarith only [hXN,hN])
  have hb' := mul_le_mul_of_nonneg_left h1 (show 0≤8*b/H by positivity)
  have hc' := mul_le_mul_of_nonneg_left h2 (show 0≤3/H by positivity)
  linear_combination hb'+hc'

theorem shortAverage_of_dyadic_affine (η : ℝ) (hη : 0<η) (hηhalf : η<1/2)
    (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 0<C ∧ ∀ f : ArithmeticFunction ℂ, (∀ n, ‖f n‖≤1) →
      ∀ X H a b : ℝ, 2≤X → 1≤H → H^2≤X → 0≤a → 0≤b →
      (∀ (N : ℕ), N=⌊X⌋₊ ∨ N=2*⌊X⌋₊ → ∀ T : ℝ, 1≤T →
        (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) f t‖^2) ≤ a+b*T/N) →
      (1/X)*(∫ x in X..2*X, ‖complexShortAverage f H x‖^2) ≤
        C*(8*a+16*b/H+6/H)+2*(3/(m:ℝ)+13/H+16*η)^2 := by
  obtain ⟨C,hC,hshort⟩ := shortAverage_dyadic_energy η hη hηhalf m hm
  refine ⟨C,hC,?_⟩
  intro f hf X H a b hX hH hHX ha hb hspec
  let N := ⌊X⌋₊
  have hXp : 0<X := by linarith
  have hHp : 0<H := by linarith
  have hNnat : 1≤N := (Nat.le_floor_iff hXp.le).mpr (by simp only [Nat.cast_one] <;> linarith)
  have hN : 1≤(N:ℝ) := by exact_mod_cast hNnat
  have hNp : (0:ℝ)<N := by linarith
  have hXN : X≤2*N := by
    have hh := Nat.lt_floor_add_one X
    change X<(N:ℝ)+1 at hh
    linarith
  have hNX : H≤X := by nlinarith only [hH,hHX]
  have htwo := mellinPolynomial_two_dyadic_energy f N ha (by positivity : 0≤b/(N:ℝ))
    (by intro T hT; convert hspec N (Or.inl rfl) T hT using 1; ring)
    (by
      intro T hT
      have hh := hspec (2*N) (Or.inr rfl) T hT
      rw [show 2*(2*N)=4*N by omega] at hh
      have hn2 : (N:ℝ)≤((2*N:ℕ):ℝ) := by push_cast <;> linarith
      have hbT : 0≤b*T := by positivity
      apply hh.trans
      have hd := div_le_div_of_nonneg_left hbT hNp hn2
      convert add_le_add_left hd a using 1 <;> first | (with_reducible_and_instances rfl) | ring)
  have hfull := mellinPolynomial_real_cutoff_energy f hf (by linarith : 1≤X) htwo
  have hi := hshort f hf X H hXp hH hNX
    (8*a) (8*b/(N:ℝ)+3/(N:ℝ)^2) (by positivity) (by positivity) (by
      intro T hT
      convert hfull T hT using 1; ring)
  have hbgt := short_affine_budget hN hXN hHp ha hb
  have hHratio : H/X≤1/H := by
    apply (div_le_div_iff₀ hXp hHp).mpr
    nlinarith only [hHX]
  have hXinv : 1/X≤1/H := one_div_le_one_div_of_le hHp hNX
  have hsmooth : 2*(3/(m:ℝ)+11/H+H/X+1/X+16*η)^2 ≤
      2*(3/(m:ℝ)+13/H+16*η)^2 := by
    have hsum : 3/(m:ℝ)+11/H+H/X+1/X+16*η ≤ 3/(m:ℝ)+13/H+16*η := by
      linear_combination hHratio+hXinv
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum 2) (by norm_num)
  exact hi.trans (add_le_add (mul_le_mul_of_nonneg_left hbgt hC.le) hsmooth)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ShortAffineLimit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Iterated short averages from a uniform affine spectral budget -/
namespace JointDickman
open Finset Filter MeasureTheory PublishedInputs
open scoped Topology

theorem shortAverage_iterated_affine
    (f : ℕ → ℝ → ArithmeticFunction ℂ) (hf : ∀ B x n, ‖f B x n‖≤1)
    (A H a b : ℕ → ℝ) (hA : ∀ B, 0<A B) (hH : Tendsto H atTop atTop)
    (hpos : ∀ᶠ B in atTop, 0≤a B ∧ 0≤b B)
    (hbudget : Tendsto (fun B => a B+b B/H B) atTop (𝓝 0))
    (hspec : ∀ᶠ B in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ, (A B/2)*x≤N → (N:ℝ)≤(2*A B)*x → ∀ T : ℝ, 1≤T →
        (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) (f B x) t‖^2) ≤
          a B+b B*T/N) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ B in atTop, ∀ᶠ x : ℝ in atTop,
      (1/(A B*x))*(∫ z in (A B*x)..2*(A B*x), ‖complexShortAverage (f B x) (H B) z‖^2)<ε := by
  intro ε hε
  obtain ⟨η,hη,hηhalf,m,hm,hsmall⟩ := exists_mellin_smoothing_parameters (half_pos hε)
  obtain ⟨C,hC,hshort⟩ := shortAverage_of_dyadic_affine η hη hηhalf m hm
  have hi := tendsto_inv_atTop_zero.comp hH
  have hcost : Tendsto (fun B => C*(16*(a B+b B/H B)+6/H B)+
      2*(3/(m:ℝ)+13/H B+16*η)^2) atTop
      (𝓝 (2*(3/(m:ℝ)+16*η)^2)) := by
    have hb := ((hbudget.const_mul 16).add (hi.const_mul 6)).const_mul C
    have he := ((((hi.const_mul 13).const_add (3/(m:ℝ))).add_const (16*η)).pow 2).const_mul 2
    convert hb.add he using 1 <;> first | (with_reducible_and_instances rfl) | (simp [Function.comp_apply,div_eq_mul_inv])
  have hnum := hcost.eventually (gt_mem_nhds (hsmall.trans (half_lt_self hε)))
  filter_upwards [hspec,hpos,hnum,hH.eventually_ge_atTop 1] with B hspec hpos hnum hHB
  have hX : Tendsto (fun x : ℝ => A B*x) atTop atTop := tendsto_id.const_mul_atTop (hA B)
  filter_upwards [hspec,hX.eventually_ge_atTop 2,hX.eventually_ge_atTop ((H B)^2)]
    with x hspec hX2 hXH
  have hfl : A B*x/2 ≤ (⌊A B*x⌋₊:ℝ) := by
    have hh := Nat.lt_floor_add_one (A B*x)
    linarith
  have hfu : (⌊A B*x⌋₊:ℝ)≤A B*x := Nat.floor_le (by linarith)
  have hs := hshort (f B x) (hf B x) (A B*x) (H B) (a B) (b B)
    hX2 hHB hXH hpos.1 hpos.2 (by
      intro N hN T hT
      apply hspec N _ _ T hT
      · rcases hN with rfl | rfl <;> push_cast <;> nlinarith only [hfl]
      · rcases hN with rfl | rfl <;> push_cast <;> nlinarith only [hfu,hX2])
  apply hs.trans_lt
  apply lt_of_le_of_lt _ hnum
  have hb : 8*a B+16*b B/H B+6/H B≤16*(a B+b B/H B)+6/H B := by
    have ha := hpos.1
    linear_combination 8*ha
  exact add_le_add (mul_le_mul_of_nonneg_left hb hC.le) le_rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_TwistedInterpolantShort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unconditional short averages for the nonprincipal interpolants -/
namespace JointDickman
open Finset Filter MeasureTheory PublishedInputs
open scoped Classical Topology

theorem twisted_interpolant_short {ι : Type*} [Fintype ι]
    {J : ℕ} (hJ : 0<J) (j : ι → ℕ) (hj : ∀ i, 1≤j i)
    (P : ℕ → Finset ℕ) (hP : ∀ B p, p∈P B → p.Prime)
    (w : ℕ → ℕ → ℝ) (hw : ∀ B p, p∈P B → 0≤w B p ∧ w B p≤1)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ≠1)
    (m : ℕ) (a : ι → Fin m) (A H scale : ℕ → ℝ) (hA : ∀ B, 0<A B)
    (hH : Tendsto H atTop atTop) (hscale : Tendsto scale atTop atTop) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖complexShortAverage (twistedWeightedBinInterpolant
          (fun i => primeBin (scale n) J (j i)) (finitePrimeWeight (P B) (w B)) a χ) (H B) z‖^2)<ε := by
  obtain ⟨C,hC,hs⟩ := twisted_bin_spectral_jd hJ j hj
  let f B x := twistedWeightedBinInterpolant (fun i => primeBin x J (j i))
    (finitePrimeWeight (P B) (w B)) a χ
  have hf : ∀ B x n, ‖f B x n‖≤1 := by
    intro B x n
    apply twistedWeightedBinInterpolant_norm_le
    intro v
    rw [abs_of_nonneg (finitePrimeWeight_bounds (hw B) v).1]
    exact (finitePrimeWeight_bounds (hw B) v).2
  have hpos : ∀ᶠ B in atTop, 0≤4/H B+canonicalAffineBase C (H B) ∧
      0 ≤ canonicalAffineSlope C (H B)+32*Real.exp 1 := by
    filter_upwards [hH.eventually (canonical_affine_nonneg hC.le),hH.eventually_gt_atTop 0] with B hpos hHB
    exact ⟨add_nonneg (by positivity) hpos.1,add_nonneg hpos.2 (by positivity)⟩
  have hbudget := (canonical_affine_application_budget C 4 1 (32*Real.exp 1)).comp hH
  simp only [one_mul] at hbudget
  have hspec : ∀ᶠ B in atTop, ∀ᶠ x : ℝ in atTop, ∀ N : ℕ,
      (A B/2)*x≤N → (N:ℝ)≤(2*A B)*x → ∀ T : ℝ, 1≤T →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) (f B x) t‖^2) ≤
        4/H B+canonicalAffineBase C (H B)+(canonicalAffineSlope C (H B)+32*Real.exp 1)*T/N := by
    filter_upwards [hH.eventually hs] with B hsB
    have hAB := hA B
    obtain ⟨M,hM⟩ := eventually_atTop.mp (hsB (P B) (hP B) q χ hχ (2*A B) (by positivity))
    filter_upwards [eventually_ge_atTop ((M:ℝ)/(A B/2))] with x hx
    intro N hlo hhi T hT
    have hMN : M≤N := by
      have hh := (div_le_iff₀ (show 0<A B/2 by positivity)).mp hx
      have hn : (M:ℝ)≤N := hh.trans (by nlinarith only [hlo])
      exact_mod_cast hn
    exact hM N hMN x ((div_le_iff₀ (by positivity)).mpr (by nlinarith only [hhi]))
      m a (w B) (hw B) T hT
  have he := shortAverage_iterated_affine f hf A H
    (fun B => 4/H B+canonicalAffineBase C (H B))
    (fun B => canonicalAffineSlope C (H B)+32*Real.exp 1) hA hH hpos hbudget hspec
  intro ε hε
  filter_upwards [he ε hε] with B hb
  exact hscale.eventually hb

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_NonprincipalShortDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonprincipal bin short averages -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem nonprincipal_weightedBinAverage_short_proved
    (_hKMT : CharacterDistanceDivergence) (_hM : PrimeReciprocalMertensInput)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (ζ : ι → ℂ) (μ : ℂ)
    (P : ℕ → Finset ℕ) (hP : ∀ B p, p ∈ P B → p.Prime)
    (t : ℕ → ℕ → ℝ) (ht : ∀ B p, p ∈ P B → 0 ≤ t B p ∧ t B p ≤ 1)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖twistedWeightedBinAverage (fun i => primeBin (scale n) J (k i)) ζ μ
          (finitePrimeWeight (P B) (t B)) χ (H B) z‖^2) < ε := by
  obtain ⟨c,hc⟩ := centered_binLabel_interpolation ζ μ J
  let E n i := primeBin (scale n) J (k i)
  let X B n := A B*scale n
  let f B n (a : ι → Fin (J+1)) := twistedWeightedBinInterpolant (E n) (finitePrimeWeight (P B) (t B)) a χ
  have hw B n : |finitePrimeWeight (P B) (t B) n| ≤ 1 := by
    rw [abs_of_nonneg (finitePrimeWeight_bounds (ht B) n).1]
    exact (finitePrimeWeight_bounds (ht B) n).2
  have hX B : Tendsto (X B) atTop atTop := hscale.const_mul_atTop (hA B)
  have hwindow B : ∀ᶠ n in atTop, ∀ v : ℕ, 1 ≤ v → (v : ℝ) ≤ 3*X B n →
      binLabel (E n) ζ v-μ = ∑ a : ι → Fin (J+1), c a*(binLabel (E n) (fun i => interpolationNode (a i)) v : ℂ) := by
    filter_upwards [hscale.eventually (primeBin_count_eventually_le J hJ (3*A B))] with n hn v hv hvX
    apply hc (E n) v (by omega)
    intro i
    apply hn (k i) (hk i) v hv
    simpa only [X,mul_assoc] using hvX
  have hbound := complexFiniteShort_of_components univ c f
    (fun B n a _ v => twistedWeightedBinInterpolant_norm_le _ _ (hw B) a χ v)
    H X hH hX (fun a _ => twisted_interpolant_short hJ k hk P hP t ht χ hχ
      (J+1) a A H scale hA hH hscale)
  have hi B : ∀ᶠ n in atTop,
      (∫ z in X B n..2*X B n, ‖twistedWeightedBinAverage (E n) ζ μ
        (finitePrimeWeight (P B) (t B)) χ (H B) z‖^2) =
      (∫ z in X B n..2*X B n, ‖complexFiniteShort univ c (f B n) (H B) z‖^2) := by
    filter_upwards [hwindow B,(hX B).eventually_gt_atTop 0,
      (hX B).eventually_ge_atTop (H B)] with n hn hpos hlen
    apply intervalIntegral.integral_congr
    intro z hz
    rw [Set.uIcc_of_le (by linarith : X B n ≤ 2*X B n)] at hz
    dsimp only
    rw [twistedWeightedBinAverage_eq_combination (E n) ζ μ (finitePrimeWeight (P B) (t B)) χ J c
      (3*X B n) (H B) z hn (by linarith [hz.2])]
  intro ε hε
  filter_upwards [hbound ε hε] with B hb
  filter_upwards [hb,hi B] with n hn he
  change (1/X B n)*(∫ z in X B n..2*X B n, ‖twistedWeightedBinAverage (E n) ζ μ
    (finitePrimeWeight (P B) (t B)) χ (H B) z‖^2) < ε
  rw [he]
  exact hn


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PrincipalBinShortDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unconditional principal short averages for the actual bin labels -/
namespace JointDickman
open Finset Filter MeasureTheory PublishedInputs
open scoped Classical Topology

theorem finitePrimeWeight_short_with_center_proved
    {J : ℕ} (hJ : 0<J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖≤1)
    (μ : ℂ) (hμ : ‖μ‖≤1)
    (hmean : ∀ D : ℝ, 0<D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (P : ℕ → Finset ℕ) (hP : ∀ B p, p∈P B → p.Prime)
    (w : ℕ → ℕ → ℝ) (hw : ∀ B p, p∈P B → 0≤w B p ∧ w B p≤1)
    (A H scale : ℕ → ℝ) (hA : ∀ B, 0<A B)
    (hH : Tendsto H atTop atTop) (hscale : Tendsto scale atTop atTop) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖weightedBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (finitePrimeWeight (P B) (w B)) (H B) z‖^2)<ε := by
  obtain ⟨C,hC,hs⟩ := centered_bin_spectral_jd hJ ζ hζ μ hμ hmean
  let g B x := centeredWeightedBinCoefficient J ζ μ (P B) (w B) x
  let f B x := halfArithmetic (g B x)
  have hf : ∀ B x n, ‖f B x n‖≤1 := fun B x => halfArithmetic_norm _
    (centeredWeightedBinCoefficient_norm ζ hζ hμ (w B) (hw B) x)
  have hpos : ∀ᶠ B in atTop, 0≤17/H B+4*canonicalAffineBase C (H B) ∧
      0≤4*canonicalAffineSlope C (H B)+128*Real.exp 1 := by
    filter_upwards [hH.eventually (canonical_affine_nonneg hC.le),hH.eventually_gt_atTop 0] with B hp hB
    exact ⟨add_nonneg (by positivity) (mul_nonneg (by norm_num) hp.1),
      add_nonneg (mul_nonneg (by norm_num) hp.2) (by positivity)⟩
  have hbudget := (canonical_affine_application_budget C 17 4 (128*Real.exp 1)).comp hH
  have hspec : ∀ᶠ B in atTop, ∀ᶠ x : ℝ in atTop, ∀ N : ℕ,
      (A B/2)*x≤N → (N:ℝ)≤(2*A B)*x → ∀ T : ℝ, 1≤T →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) (f B x) t‖^2) ≤
        17/H B+4*canonicalAffineBase C (H B)+(4*canonicalAffineSlope C (H B)+128*Real.exp 1)*T/N := by
    filter_upwards [hH.eventually hs] with B hsB
    filter_upwards [hsB (P B) (hP B) (w B) (hw B) (A B) (hA B)] with x hx
    intro N hlo hhi T hT
    have he := hx N hlo hhi T hT
    change (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) (halfArithmetic (g B x)) t‖^2) ≤ _
    rw [halfArithmetic_energy]
    have hn : 0≤∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) (g B x) t‖^2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
    exact (show (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) (g B x) t‖^2)/4 ≤
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) (g B x) t‖^2) by linarith).trans he
  have he := shortAverage_iterated_affine f hf A H
    (fun B => 17/H B+4*canonicalAffineBase C (H B))
    (fun B => 4*canonicalAffineSlope C (H B)+128*Real.exp 1) hA hH hpos hbudget hspec
  intro ε hε
  filter_upwards [he (ε/4) (by positivity)] with B hb
  filter_upwards [hscale.eventually hb] with n hn
  have hid (z : ℝ) : weightedBinAverage
      (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
      (finitePrimeWeight (P B) (w B)) (H B) z = complexShortAverage (g B (scale n)) (H B) z := rfl
  simp_rw [hid]
  rw [halfArithmetic_short_energy]
  change 4*((1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
    ‖complexShortAverage (f B (scale n)) (H B) z‖^2))<ε
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PrescribedShortDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem all_characters_short_with_center_proved
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖≤1) (μ : ℂ) (hμ : ‖μ‖≤1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (P : ℕ → Finset ℕ) (hP : ∀ B p, p ∈ P B → p.Prime)
    (t : ℕ → ℕ → ℝ) (ht : ∀ B p, p ∈ P B → 0 ≤ t B p ∧ t B p ≤ 1)
    {q : ℕ} [NeZero q] (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      ∀ χ : DirichletCharacter ℂ q,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖twistedWeightedBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (finitePrimeWeight (P B) (t B)) χ (H B) z‖^2) < ε := by
  have hp B p (h : p ∈ P B ∪ q.primeFactors) : p.Prime := by
    rcases mem_union.mp h with h | h
    · exact hP B p h
    · exact (Nat.mem_primeFactors.mp h).1
  have hb B p (h : p ∈ P B ∪ q.primeFactors) :
      0 ≤ (if p ∈ q.primeFactors then 0 else t B p) ∧ (if p ∈ q.primeFactors then 0 else t B p) ≤ (1 : ℝ) := by
    by_cases hh : p ∈ q.primeFactors
    · simp [hh]
    · simpa only [ite_eq_right hh] using ht B p ((mem_union.mp h).resolve_right hh)
  have hprincipal := finitePrimeWeight_short_with_center_proved hJ ζ hζ μ hμ hmean
    (fun B => P B ∪ q.primeFactors) hp (fun B p => if p ∈ q.primeFactors then 0 else t B p) hb
    A H scale hA hH hscale
  intro ε hε
  have hc (χ : DirichletCharacter ℂ q) : ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖twistedWeightedBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (finitePrimeWeight (P B) (t B)) χ (H B) z‖^2) < ε := by
    by_cases he : χ = 1
    · subst χ
      simpa only [principal_twistedWeightedBinAverage,coprimePrimeWeight] using hprincipal ε hε
    · exact nonprincipal_weightedBinAverage_short_proved hKMT hM J hJ
        (fun i : Fin (J-1) => i.val+1) (fun _ => by omega) ζ μ P hP t ht χ he
        A scale H hA hscale hH ε hε
  filter_upwards [eventually_all.mpr hc] with B hb
  exact eventually_all.mpr hb

theorem unit_progressions_short_with_center_proved
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖≤1) (μ : ℂ) (hμ : ‖μ‖≤1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (P : ℕ → Finset ℕ) (hP : ∀ B p, p ∈ P B → p.Prime)
    (t : ℕ → ℕ → ℝ) (ht : ∀ B p, p ∈ P B → 0 ≤ t B p ∧ t B p ≤ 1)
    {q : ℕ} [NeZero q] (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      ∀ r : (ZMod q)ˣ,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖unitProgressionBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (finitePrimeWeight (P B) (t B)) r (H B) z‖^2) < ε := by
  have hb := all_characters_short_with_center_proved hKMT hM hJ ζ hζ μ hμ hmean
    P hP t ht (q := q) A scale H hA hscale hH
  intro ε hε
  filter_upwards [hb (ε/2) (half_pos hε),hH.eventually_gt_atTop 0] with B hb hHB
  have hX : Tendsto (fun n => A B*scale n) atTop atTop := hscale.const_mul_atTop (hA B)
  filter_upwards [hb,hX.eventually_gt_atTop 0] with n hb hXn
  intro r
  have he := unitProgressionBinAverage_energy_le
    (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
    (finitePrimeWeight (P B) (t B)) r hHB hXn
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hc : (Fintype.card (DirichletCharacter ℂ q) : ℝ) = q.totient := by
    rw [← Nat.card_eq_fintype_card,DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  have hs := sum_le_sum (s := univ) (fun χ _ => (hb χ).le)
  have hh := he.trans (mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 1/(q.totient : ℝ)))
  simp only [sum_const,card_univ,nsmul_eq_mul,hc] at hh
  have hid : (1/(q.totient : ℝ))*((q.totient : ℝ)*(ε/2)) = ε/2 := by field_simp
  rw [hid] at hh
  exact hh.trans_lt (by linarith)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_LaplaceShortDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem unit_laplace_short_with_center_proved
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖≤1) (μ : ℂ) (hμ : ‖μ‖≤1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (Q : ℕ → Finset ℕ) (hQ : ∀ B p, p ∈ Q B → p.Prime)
    (V : Finset ℕ) (a : ℕ → ℝ)
    {q : ℕ} [NeZero q] (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop, ∀ r : (ZMod q)ˣ,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖unitProgressionBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (primeSiteWeight (Q B) (fun x => ∑ v ∈ V, a v*primeLaplaceFeature (Q B) B v x))
          r (H B) z‖^2) < ε := by
  intro ε hε
  let K := ∑ v ∈ V, |a v|^2
  have hK : 0 ≤ K := sum_nonneg (fun _ _ => sq_nonneg _)
  let δ := ε/(K*(V.card : ℝ)+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall v (_ : v ∈ V) := unit_progressions_short_with_center_proved hKMT hM hJ ζ hζ μ hμ hmean
    Q hQ (fun B p => (1+(p : ℝ)^(-(v : ℝ)/(B : ℝ)))/2)
    (fun B p hp => primeLaplaceWeight_bounds (hQ B) (Nat.cast_nonneg B) (Nat.cast_nonneg v) p hp)
    (q := q) A scale H hA hscale hH δ hδ
  filter_upwards [(eventually_all_finset V).mpr hsmall,hH.eventually_gt_atTop 0] with B hB hHB
  have hX := hscale.const_mul_atTop (hA B)
  filter_upwards [(eventually_all_finset V).mpr hB,hX.eventually_gt_atTop 0] with n hn hXn
  intro r
  let E := fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)
  let w := fun v => finitePrimeWeight (Q B) (fun p => (1+(p : ℝ)^(-(v : ℝ)/(B : ℝ)))/2)
  have he := finite_complex_sum_energy V (fun v => (a v : ℂ))
    (fun v z => unitProgressionBinAverage E ζ μ (w v) r (H B) z) hXn
    (fun v _ => unitProgressionBinAverage_sq_integrable E ζ μ (w v) r hHB _ _)
    (fun v _ => (measurable_unitProgressionBinAverage E ζ μ (w v) r (H B)).aestronglyMeasurable)
  simp only [Complex.norm_real,Real.norm_eq_abs] at he
  have hs := sum_le_sum (s := V) (fun v hv => (hn v hv r).le)
  have hb := he.trans (mul_le_mul_of_nonneg_left hs hK)
  simp only [sum_const,nsmul_eq_mul] at hb
  have hδid : (K*(V.card : ℝ)+1)*δ = ε := by dsimp [δ]; field_simp
  have hfinal : K*((V.card : ℝ)*δ) < ε := by nlinarith
  simp_rw [unit_laplace_combination]
  exact hb.trans_lt hfinal

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeFeatureInvariance
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed multipliers leave the auxiliary-prime features unchanged -/
namespace JointDickman
open Finset Filter Classical

theorem primeSiteWeight_mul_fixed (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (F : (Q → Bool) → ℝ) {d : ℕ} (hd : d ≠ 0)
    (hno : ∀ p ∈ Q, ¬p ∣ d) (k : ℕ) :
    primeSiteWeight Q F (d*k) = primeSiteWeight Q F k := by
  by_cases hk : k = 0
  · simp [hk]
  rw [primeSiteWeight_apply Q F (mul_ne_zero hd hk),primeSiteWeight_apply Q F hk]
  congr 1
  funext p
  simp only [(hQ p p.property).dvd_mul,hno p p.property,false_or]

theorem auxiliaryPrimes_eventually_no_factor {d : ℕ} (hd : d ≠ 0) :
    ∀ᶠ B in atTop, ∀ p ∈ auxiliaryPrimes B, ¬p ∣ d := by
  filter_upwards [auxiliaryCutoff_tendsto.eventually_ge_atTop d] with B hB
  intro p hp hpd
  have hlarge : (auxiliaryCutoff B : ℝ) < p := (mem_filter.mp hp).2
  have hle : p ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hpd
  have hh : (p : ℝ) ≤ auxiliaryCutoff B := by exact_mod_cast hle.trans hB
  exact (not_lt_of_ge hh) hlarge

theorem auxiliaryPrimeFeature_eventually_mul_fixed {d : ℕ} (hd : d ≠ 0)
    (F : ∀ B, (auxiliaryPrimes B → Bool) → ℝ) :
    ∀ᶠ B in atTop, ∀ k, primeSiteWeight (auxiliaryPrimes B) (F B) (d*k) =
      primeSiteWeight (auxiliaryPrimes B) (F B) k := by
  filter_upwards [auxiliaryPrimes_eventually_no_factor hd] with B hB
  exact primeSiteWeight_mul_fixed _ (auxiliaryPrimes_prime B) _ hd hB

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_FixedDivisorWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing a fixed divisor from finite-prime weights and intervals -/
namespace JointDickman
open Finset Classical

theorem sum_divisible_interval {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (a b d : ℕ) (hd : 0 < d) :
    (∑ n ∈ Ioc a b, if d ∣ n then f n else 0) =
      ∑ k ∈ Ioc (a/d) (b/d), f (d*k) := by
  rw [← sum_filter]
  have hsets : (Ioc (a/d) (b/d)).image (fun k => d*k) = (Ioc a b).filter (fun n => d ∣ n) := by
    ext n
    simp only [mem_image,mem_Ioc,mem_filter]
    constructor
    · rintro ⟨k,⟨hk,hkb⟩,rfl⟩
      constructor
      · constructor
        · have h := (Nat.div_lt_iff_lt_mul hd).mp hk
          simpa only [Nat.mul_comm] using h
        · exact (Nat.mul_le_mul_left d hkb).trans (Nat.mul_div_le b d)
      · exact dvd_mul_right d k
    · rintro ⟨⟨han,hnb⟩,hdn⟩
      refine ⟨n/d,⟨?_,Nat.div_le_div_right hnb⟩,Nat.mul_div_cancel' hdn⟩
      apply (Nat.div_lt_iff_lt_mul hd).mpr
      simpa only [Nat.mul_comm,Nat.mul_div_cancel' hdn] using han
  rw [← hsets,sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hd hab

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FixedResidueReduction
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dividing a residue class and its averaging interval by a fixed divisor -/
namespace JointDickman
open Finset Classical

theorem residueBinAverage_unit {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (r : (ZMod q)ˣ) (H z : ℝ) :
    residueBinAverage E ζ μ w (r : ZMod q) H z = unitProgressionBinAverage E ζ μ w r H z := rfl

theorem natCast_fixed_residue_iff {d e a n : ℕ} (hd : d ≠ 0) :
    (n : ZMod (d*e)) = ((d*a : ℕ) : ZMod (d*e)) ↔
      d ∣ n ∧ (n/d : ℕ) ≡ a [MOD e] := by
  rw [ZMod.natCast_eq_natCast_iff]
  constructor
  · intro h
    have hm := h.of_dvd (dvd_mul_right d e)
    have hdn : d ∣ n := (hm.dvd_iff (dvd_refl d)).mpr (dvd_mul_right d a)
    refine ⟨hdn,?_⟩
    have hh : d*(n/d) ≡ d*a [MOD d*e] := by simpa only [Nat.mul_div_cancel' hdn] using h
    exact hh.mul_left_cancel' hd
  · rintro ⟨hdn,h⟩
    have hh := h.mul_left' d
    simpa only [Nat.mul_div_cancel' hdn] using hh

theorem sum_fixed_residue {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (l u d e a : ℕ) (hd : 0 < d) :
    (∑ n ∈ Ioc l u, if (n : ZMod (d*e)) = ((d*a : ℕ) : ZMod (d*e)) then f n else 0) =
      ∑ k ∈ Ioc (l/d) (u/d), if (k : ZMod e) = (a : ZMod e) then f (d*k) else 0 := by
  have he (n : ℕ) : (if (n : ZMod (d*e)) = ((d*a : ℕ) : ZMod (d*e)) then f n else 0) =
      if d ∣ n then (if (n/d : ℕ) ≡ a [MOD e] then f n else 0) else 0 := by
    simp only [natCast_fixed_residue_iff hd.ne']
    split_ifs <;> simp_all
  simp_rw [he]
  rw [sum_divisible_interval (fun n => if (n/d : ℕ) ≡ a [MOD e] then f n else 0) l u d hd]
  apply sum_congr rfl
  intro k _
  simp only [Nat.mul_div_cancel_left k hd,ZMod.natCast_eq_natCast_iff]

theorem residueBinAverage_dilate {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ)
    (w v : ArithmeticFunction ℝ) (c : ℝ)
    {d : ℕ} (hd : 0 < d) (e a : ℕ)
    (hweight : ∀ k, w (d*k) = c*v k)
    (hbin : ∀ k, binLabel E ζ (d*k) = binLabel E ζ k)
    {H : ℝ} (hH : 0 < H) (z : ℝ) :
    residueBinAverage E ζ μ w ((d*a : ℕ) : ZMod (d*e)) H z =
      (c : ℂ)/(d : ℂ)*
        residueBinAverage E ζ μ v
          (a : ZMod e) (H/d) (z/d) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hHC : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  unfold residueBinAverage
  rw [sum_fixed_residue _ _ _ _ _ _ hd]
  simp_rw [hweight,hbin,Complex.ofReal_mul]
  rw [show z/(d : ℝ)+H/d = (z+H)/d by ring,Nat.floor_div_natCast,Nat.floor_div_natCast]
  simp only [Complex.ofReal_div,Complex.ofReal_natCast]
  have he (k : ℕ) : (if (k : ZMod e) = a then
      (binLabel E ζ k-μ)*((c : ℂ)*
        (v k : ℂ)) else 0) =
      (c : ℂ)*
        (if (k : ZMod e) = a then (binLabel E ζ k-μ)*
          (v k : ℂ) else 0) := by
    split_ifs <;> ring
  simp_rw [he]
  rw [← mul_sum]
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_ResidueDivisorRepresentation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every residue class is a fixed multiple of a unit class -/
namespace JointDickman

theorem residue_fixed_divisor_representation {q : ℕ} [NeZero q] (r : ZMod q) :
    ∃ d e a : ℕ, 0 < d ∧ 0 < e ∧ q = d*e ∧
      r = ((d*a : ℕ) : ZMod q) ∧ a.Coprime e := by
  let d := r.val.gcd q
  let e := q/d
  let a := r.val/d
  have hd : 0 < d := Nat.gcd_pos_of_pos_right r.val (NeZero.pos q)
  have he : 0 < e := Nat.div_gcd_pos_of_pos_right r.val (NeZero.pos q)
  have hq : d*e = q := Nat.mul_div_cancel' (Nat.gcd_dvd_right r.val q)
  have ha : d*a = r.val := Nat.mul_div_cancel' (Nat.gcd_dvd_left r.val q)
  refine ⟨d,e,a,hd,he,hq.symm,?_,?_⟩
  · rw [ha]
    exact (ZMod.natCast_zmod_val r).symm
  · exact Nat.gcd_div_gcd_div_gcd_of_pos_right (NeZero.pos q)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_UnitBinEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear and quadratic estimates for unit-progression bin averages -/
namespace JointDickman
open Finset Filter MeasureTheory Classical

theorem unitProgressionBinAverage_sub {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (u v : ArithmeticFunction ℝ)
    {q : ℕ} (r : (ZMod q)ˣ) (H z : ℝ) :
    unitProgressionBinAverage E ζ μ u r H z-unitProgressionBinAverage E ζ μ v r H z =
      unitProgressionBinAverage E ζ μ (u-v) r H z := by
  unfold unitProgressionBinAverage
  rw [← sub_div,← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro n _
  simp only [sub_eq_add_neg,ArithmeticFunction.add_apply,ArithmeticFunction.neg_apply,Complex.ofReal_add,Complex.ofReal_neg]
  split_ifs <;> ring

theorem unitProgressionBinAverage_energy_triangle {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (u v : ArithmeticFunction ℝ)
    {q : ℕ} (r : (ZMod q)ˣ) {H X : ℝ} (hH : 0 < H) (hX : 0 < X) :
    (1/X)*(∫ z in X..2*X, ‖unitProgressionBinAverage E ζ μ u r H z‖^2) ≤
      2*((1/X)*(∫ z in X..2*X,
        ‖unitProgressionBinAverage E ζ μ u r H z-unitProgressionBinAverage E ζ μ v r H z‖^2))+
      2*((1/X)*(∫ z in X..2*X, ‖unitProgressionBinAverage E ζ μ v r H z‖^2)) := by
  have hdiff : IntervalIntegrable (fun z =>
      ‖unitProgressionBinAverage E ζ μ u r H z-unitProgressionBinAverage E ζ μ v r H z‖^2)
      volume X (2*X) := by
    simp_rw [unitProgressionBinAverage_sub]
    exact unitProgressionBinAverage_sq_integrable E ζ μ (u-v) r hH _ _
  have hv := unitProgressionBinAverage_sq_integrable E ζ μ v r hH X (2*X)
  have hu := unitProgressionBinAverage_sq_integrable E ζ μ u r hH X (2*X)
  have hp z : ‖unitProgressionBinAverage E ζ μ u r H z‖^2 ≤
      2*‖unitProgressionBinAverage E ζ μ u r H z-unitProgressionBinAverage E ζ μ v r H z‖^2+
      2*‖unitProgressionBinAverage E ζ μ v r H z‖^2 := by
    let a := unitProgressionBinAverage E ζ μ u r H z
    let b := unitProgressionBinAverage E ζ μ v r H z
    have hh : ‖a‖ ≤ ‖a-b‖+‖b‖ := by simpa only [sub_add_cancel] using norm_add_le (a-b) b
    have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
    nlinarith [sq_nonneg (‖a-b‖-‖b‖)]
  have he := intervalIntegral.integral_mono (by linarith : X ≤ 2*X) hu
    ((hdiff.const_mul 2).add (hv.const_mul 2)) hp
  rw [intervalIntegral.integral_add (hdiff.const_mul 2) (hv.const_mul 2),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at he
  convert mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 1/X) using 1
  all_goals try with_reducible_and_instances rfl
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_DilatedWindowEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact normalization under a fixed dilation of short windows -/
namespace JointDickman
open MeasureTheory

theorem normalized_dilate_energy (f : ℝ → ℂ) (c : ℝ) {D X : ℝ} (hD : 0 < D) (hX : 0 < X) :
    (1/X)*(∫ z in X..2*X, ‖(c : ℂ)*f (z/D)‖^2) =
      c^2*((1/(X/D))*(∫ z in (X/D)..2*(X/D), ‖f z‖^2)) := by
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_div (fun y => ‖f y‖^2) hD.ne']
  simp only [smul_eq_mul]
  rw [show 2*X/D = 2*(X/D) by ring]
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_FixedResidueEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dividing a residue class does not increase its normalized energy -/
namespace JointDickman
open Finset MeasureTheory Classical

theorem residueBinAverage_dilate_energy_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ)
    (w v : ArithmeticFunction ℝ) (c : ℝ)
    {d : ℕ} (hd : 0 < d) (e a : ℕ) (hc : 0 ≤ c ∧ c ≤ d)
    (hweight : ∀ k, w (d*k) = c*v k)
    (hbin : ∀ k, binLabel E ζ (d*k) = binLabel E ζ k)
    {H X : ℝ} (hH : 0 < H) (hX : 0 < X) :
    (1/X)*(∫ z in X..2*X, ‖residueBinAverage E ζ μ w ((d*a : ℕ) : ZMod (d*e)) H z‖^2) ≤
    (1/(X/d))*(∫ z in (X/d)..2*(X/d), ‖residueBinAverage E ζ μ v (a : ZMod e) (H/d) z‖^2) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let C : ℝ := c/(d : ℝ)
  let f : ℝ → ℂ := residueBinAverage E ζ μ v (a : ZMod e) (H/d)
  have he z : residueBinAverage E ζ μ w ((d*a : ℕ) : ZMod (d*e)) H z = (C : ℂ)*f (z/d) := by
    simpa only [C,f,Complex.ofReal_div,Complex.ofReal_natCast] using
      residueBinAverage_dilate E ζ μ w v c hd e a hweight hbin hH z
  simp_rw [he]
  rw [normalized_dilate_energy f C hdR hX]
  have hC0 : 0 ≤ C := div_nonneg hc.1 hdR.le
  have hC1 : C ≤ 1 := (div_le_one hdR).mpr hc.2
  have hC2 : C^2 ≤ 1 := by nlinarith
  apply mul_le_of_le_one_left _ hC2
  apply mul_nonneg (by positivity)
  exact intervalIntegral.integral_nonneg
    (by have hh := div_pos hX hdR; linarith : X/(d : ℝ) ≤ 2*(X/d)) (fun _ _ => sq_nonneg _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_DiscreteShortEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact passage between discrete and continuous short-window energy -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem complexShortAverage_integer_cell (f : ArithmeticFunction ℂ) (H u : ℕ)
    {z : ℝ} (hz : (u : ℝ) < z ∧ z < (u : ℝ)+1) :
    complexShortAverage f H z = complexShortAverage f H u := by
  have hz0 : 0 ≤ z := (Nat.cast_nonneg u).trans hz.1.le
  have hf : ⌊z⌋₊ = u := (Nat.floor_eq_iff hz0).mpr ⟨hz.1.le,hz.2⟩
  have hfH : ⌊z+(H : ℝ)⌋₊ = u+H := by rw [Nat.floor_add_natCast hz0,hf]
  simp only [complexShortAverage,hf,hfH,Nat.floor_natCast,← Nat.cast_add]

theorem complexShortAverage_cell_integral (f : ArithmeticFunction ℂ) (H u : ℕ) :
    (∫ z in (u : ℝ)..(u+1 : ℕ), ‖complexShortAverage f H z‖^2) =
      ‖complexShortAverage f H u‖^2 := by
  calc
    _ = ∫ _z in (u : ℝ)..(u+1 : ℕ), ‖complexShortAverage f H u‖^2 := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_cast; omega)
      intro z hz
      exact congrArg (fun w : ℂ => ‖w‖^2)
        (complexShortAverage_integer_cell f H u (z := z) (by simpa using hz))
    _ = _ := by simp

theorem complexShortAverage_discrete_energy (f : ArithmeticFunction ℂ) {H : ℕ}
    (hH : 0 < H) (a b : ℕ) (hab : a ≤ b) :
    (∑ u ∈ Ico a b, ‖complexShortAverage f H u‖^2) =
      ∫ z in (a : ℝ)..(b : ℝ), ‖complexShortAverage f H z‖^2 := by
  have h := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (a := fun u : ℕ => (u : ℝ))
    (f := fun z => ‖complexShortAverage f (H : ℝ) z‖^2) (μ := volume) hab
    (fun u _ => by
      simpa only [Nat.cast_add,Nat.cast_one] using
        complexShortAverage_sq_integrable_any f (H := (H : ℝ)) (by exact_mod_cast hH) u (u+1))
  simpa only [complexShortAverage_cell_integral] using h

theorem residueBinAverage_discrete_energy {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (r : ZMod q) {H : ℕ} (hH : 0 < H) (a b : ℕ) (hab : a ≤ b) :
    (∑ u ∈ Ico a b, ‖residueBinAverage E ζ μ w r H u‖^2) =
      ∫ z in (a : ℝ)..(b : ℝ), ‖residueBinAverage E ζ μ w r H z‖^2 := by
  let f : ArithmeticFunction ℂ := ⟨fun n => if (n : ZMod q) = r then
    (binLabel E ζ n-μ)*(w n : ℂ) else 0,by split_ifs <;> simp⟩
  exact complexShortAverage_discrete_energy f hH a b hab

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_ResidueSmoothingIdentity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying progression smoothing with the arithmetic residue average -/
namespace JointDickman
open Finset Classical

theorem sum_residue_integer_window {q : ℕ} (hq : 0 < q) (R v : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Ioc v (v+q*R), if (n : ZMod q) = (v : ZMod q) then f n else 0) =
      ∑ h ∈ range R, f (v+q*(h+1)) := by
  have hs : (range R).image (fun h => v+q*(h+1)) =
      (Ioc v (v+q*R)).filter (fun n : ℕ => (n : ZMod q) = (v : ZMod q)) := by
    ext n
    simp only [mem_image,mem_filter,mem_Ioc,mem_range]
    constructor
    · rintro ⟨h,hh,rfl⟩
      refine ⟨⟨by nlinarith,by nlinarith⟩,?_⟩
      simp
    · rintro ⟨⟨hvn,hupper⟩,hr⟩
      have hm : n ≡ v [MOD q] := by rwa [ZMod.natCast_eq_natCast_iff] at hr
      have hd : q ∣ n-v := hm.symm.dvd'
      let k := (n-v)/q
      have hk : q*k = n-v := Nat.mul_div_cancel' hd
      have hnv : 0 < n-v := Nat.sub_pos_of_lt hvn
      have hk0 : 0 < k := by nlinarith
      have hnsub : n-v ≤ q*R := by omega
      have hkR : k ≤ R := by nlinarith
      refine ⟨k-1,by omega,?_⟩
      have hk1 : k-1+1=k := by omega
      rw [hk1,hk]
      omega
  rw [← sum_filter,← hs,sum_image]
  intro a _ b _ hab
  nlinarith

theorem residueSmoothed_eq_residueBinAverage {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q R : ℕ} (hq : 0 < q) (hR : 0 < R) (v : ℕ) :
    residueSmoothed (fun n => (binLabel E ζ n-μ)*(w n : ℂ)) q R v =
      (q : ℂ)*residueBinAverage E ζ μ w (v : ZMod q) (q*R : ℕ) v := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  unfold residueSmoothed residueBinAverage
  rw [← Nat.cast_add,Nat.floor_natCast,Nat.floor_natCast,sum_residue_integer_window hq]
  push_cast
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoarseDiscreteShort
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse-feature cancellation for discrete integer starting points -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem residueBinAverage_discrete_energy_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (r : ZMod q) {H : ℕ} (hH : 0 < H) (a b : ℕ) {X Y : ℝ}
    (hXY : X ≤ Y) (hXa : X ≤ a) (hbY : (b : ℝ) ≤ Y) :
    (∑ u ∈ Ico a b, ‖residueBinAverage E ζ μ w r H u‖^2) ≤
      ∫ z in X..Y, ‖residueBinAverage E ζ μ w r H z‖^2 := by
  let f : ArithmeticFunction ℂ := ⟨fun n => if (n : ZMod q) = r then
    (binLabel E ζ n-μ)*(w n : ℂ) else 0,by split_ifs <;> simp⟩
  by_cases hab : a ≤ b
  · rw [residueBinAverage_discrete_energy E ζ μ w r hH a b hab]
    exact intervalIntegral.integral_mono_interval hXa (by exact_mod_cast hab) hbY
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (complexShortAverage_sq_integrable_any f (by exact_mod_cast hH) X Y)
  · rw [Ico_eq_empty_of_le (by omega : b ≤ a),sum_empty]
    exact intervalIntegral.integral_nonneg hXY (fun _ _ => sq_nonneg _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoarseShiftedShort
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniformly shifted discrete coarse-feature short averages -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem residueBinAverage_sq_integrable {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (r : ZMod q) {H : ℝ} (hH : 0 < H) (a b : ℝ) :
    IntervalIntegrable (fun z => ‖residueBinAverage E ζ μ w r H z‖^2) volume a b := by
  let f : ArithmeticFunction ℂ := ⟨fun n => if (n : ZMod q) = r then
    (binLabel E ζ n-μ)*(w n : ℂ) else 0,by split_ifs <;> simp⟩
  exact complexShortAverage_sq_integrable_any f hH a b

theorem residueBinAverage_shifted_discrete_energy_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q : ℕ} (r : ZMod q) {H : ℕ} (hH : 0 < H) {X : ℝ} (hX : 0 < X)
    (j : ℕ) (hj : (j : ℝ) ≤ X) :
    (∑ u ∈ Ico ⌈X⌉₊ ⌊2*X⌋₊, ‖residueBinAverage E ζ μ w r H (u+j)‖^2) ≤
      ∫ z in X..4*X, ‖residueBinAverage E ζ μ w r H z‖^2 := by
  have hs := sum_Ico_add' (fun u : ℕ => ‖residueBinAverage E ζ μ w r H u‖^2)
    ⌈X⌉₊ ⌊2*X⌋₊ j
  simp only [Nat.cast_add] at hs
  rw [hs]
  apply residueBinAverage_discrete_energy_le E ζ μ w r hH
  · linarith
  · push_cast
    exact (Nat.le_ceil X).trans (le_add_of_nonneg_right (Nat.cast_nonneg j))
  · push_cast
    have hf := Nat.floor_le (show 0 ≤ 2*X by positivity)
    linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoarseBinShortDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem unit_coarse_short_with_center_proved
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) (d : Fin m)
    {q : ℕ} [NeZero q] (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop, ∀ r : (ZMod q)ˣ,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖unitProgressionBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B d)) r (H B) z‖^2) < ε := by
  intro ε hε
  obtain ⟨P,hP⟩ := primeCoarseFeature_laplace_approximation_jd hSD hSW hM hMP hm d
    (show 0 < ε/384 by positivity)
  have hpoly := unit_laplace_short_with_center_proved hKMT hM hJ ζ (fun i => (hζ i).le) μ hμ hmean
    auxiliaryPrimes auxiliaryPrimes_prime (range (P.natDegree+1)) P.coeff
    (q := q) A scale H hA hscale hH (ε/8) (by positivity)
  filter_upwards [hP,hpoly,hH.eventually_ge_atTop 1] with B hPB hpolyB hHB
  have herr := unit_prime_feature_error ζ hζ μ hμ (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    (primeCoarseFeature m B d)
    (fun x => ∑ v ∈ range (P.natDegree+1), P.coeff v*primeLaplaceFeature (auxiliaryPrimes B) B v x)
    hHB (hA B) scale hscale (q := q) (show 0 < ε/16 by positivity)
  have hX := hscale.const_mul_atTop (hA B)
  filter_upwards [hpolyB,herr,hX.eventually_gt_atTop 0] with n hpolyN herrN hXn
  intro r
  have he := unitProgressionBinAverage_energy_triangle
    (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
    (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B d))
    (primeSiteWeight (auxiliaryPrimes B)
      (fun x => ∑ v ∈ range (P.natDegree+1), P.coeff v*primeLaplaceFeature (auxiliaryPrimes B) B v x))
    r (by linarith : 0 < H B) hXn
  have hp := hpolyN r
  have hr := herrN (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) r
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ResidueCoarseShortDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem fixed_residue_coarse_short_with_center_proved
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) (b : Fin m)
    {d e : ℕ} (hd : 0 < d) [NeZero e] (a : ℕ) (ha : a.Coprime e)
    (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖residueBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b))
          ((d*a : ℕ) : ZMod (d*e)) (H B) z‖^2) < ε := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hH' : Tendsto (fun B => H B/(d : ℝ)) atTop atTop := by
    simpa only [div_eq_mul_inv,mul_comm] using hH.const_mul_atTop (inv_pos.mpr hdR)
  have hu := unit_coarse_short_with_center_proved hKMT hM hSD hSW hMP hJ ζ hζ μ hμ hmean hm b
    (q := e) (fun B => A B/d) scale (fun B => H B/d)
    (fun B => div_pos (hA B) hdR) hscale hH'
  have hbin := hscale.eventually (binLabel_eventually_mul_invariant J hJ
    (fun i : Fin (J-1) => i.val+1) (fun _ => by omega) ζ hd.ne')
  have hw := auxiliaryPrimeFeature_eventually_mul_fixed hd.ne' (fun B => primeCoarseFeature m B b)
  intro ε hε
  filter_upwards [hu ε hε,hH.eventually_gt_atTop 0,hw] with B hB hHB hwB
  have hX := hscale.const_mul_atTop (hA B)
  filter_upwards [hB,hbin,hX.eventually_gt_atTop 0] with n hn hbn hXn
  have he := residueBinAverage_dilate_energy_le
    (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
    (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b))
    (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b)) 1 hd e a
    ⟨by norm_num,by exact_mod_cast hd⟩ (fun k => by simpa only [one_mul] using hwB k) hbn hHB hXn
  have hh := hn (ZMod.unitOfCoprime a ha)
  have hxd : A B*scale n/(d : ℝ) = (A B/d)*scale n := by ring
  simp only [hxd] at he
  have hu' : (1/((A B/d)*scale n))*(∫ z in ((A B/d)*scale n)..2*((A B/d)*scale n),
      ‖residueBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
        (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b))
        (a : ZMod e) (H B/d) z‖^2) < ε := by
    simpa only [← residueBinAverage_unit,ZMod.coe_unitOfCoprime] using hh
  exact he.trans_lt hu'

theorem all_residues_coarse_short_with_center_proved
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) (b : Fin m)
    {q : ℕ} [NeZero q] (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop, ∀ r : ZMod q,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖residueBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b)) r (H B) z‖^2) < ε := by
  intro ε hε
  have hr (r : ZMod q) : ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖residueBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b)) r (H B) z‖^2) < ε := by
    obtain ⟨d,e,a,hd,he,hq,hr,ha⟩ := residue_fixed_divisor_representation r
    subst q
    let : NeZero e := ⟨he.ne'⟩
    rw [hr]
    exact fixed_residue_coarse_short_with_center_proved hKMT hM hSD hSW hMP hJ ζ hζ μ hμ hmean
      hm b hd a ha A scale H hA hscale hH ε hε
  filter_upwards [eventually_all.mpr hr] with B hB
  exact eventually_all.mpr hB

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoarseShiftedShortDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem all_residues_coarse_shifted_short_proved
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) (b : Fin m)
    {q : ℕ} [NeZero q] (A scale : ℕ → ℝ) (H M : ℕ → ℕ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop, ∀ (j : ℕ), j ≤ M B → ∀ r : ZMod q,
      (1/(A B*scale n))*(∑ u ∈ Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊,
        ‖residueBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b)) r (H B) (u+j)‖^2) < ε := by
  have hs₁ := all_residues_coarse_short_with_center_proved hKMT hM hSD hSW hMP
    hJ ζ hζ μ hμ hmean hm b (q := q) A scale (fun B => (H B : ℝ)) hA hscale
    (tendsto_natCast_atTop_atTop.comp hH)
  have hs₂ := all_residues_coarse_short_with_center_proved hKMT hM hSD hSW hMP
    hJ ζ hζ μ hμ hmean hm b (q := q) (fun B => 2*A B) scale (fun B => (H B : ℝ))
    (fun B => mul_pos (by norm_num) (hA B)) hscale (tendsto_natCast_atTop_atTop.comp hH)
  intro ε hε
  filter_upwards [hs₁ (ε/4) (by positivity),hs₂ (ε/4) (by positivity),hH.eventually_gt_atTop 0]
    with B h₁ h₂ hHB
  filter_upwards [h₁,h₂,(hscale.const_mul_atTop (hA B)).eventually_gt_atTop (M B)]
    with n h₁ h₂ hX
  intro j hj r
  have hX0 : 0 < A B*scale n := (Nat.cast_nonneg (M B)).trans_lt hX
  let E := fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)
  let w := primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b)
  let f := fun z => ‖residueBinAverage E ζ μ w r (H B) z‖^2
  have hi₁ := residueBinAverage_sq_integrable E ζ μ w r (by exact_mod_cast hHB : (0 : ℝ) < H B)
    (A B*scale n) (2*(A B*scale n))
  have hi₂ := residueBinAverage_sq_integrable E ζ μ w r (by exact_mod_cast hHB : (0 : ℝ) < H B)
    (2*(A B*scale n)) (4*(A B*scale n))
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
  have hh₂ : (1/(2*(A B*scale n)))*(∫ z in 2*(A B*scale n)..4*(A B*scale n), f z) < ε/4 := by
    have hb := h₂ r
    have heA : (2*A B)*scale n = 2*(A B*scale n) := by ring
    have heU : 2*((2*A B)*scale n) = 4*(A B*scale n) := by ring
    rw [heU,heA] at hb
    exact hb
  have hratio : (1/(A B*scale n))*(∫ z in (A B*scale n)..4*(A B*scale n), f z) =
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n), f z)+
        2*((1/(2*(A B*scale n)))*(∫ z in 2*(A B*scale n)..4*(A B*scale n), f z)) := by
    rw [← hadd]
    ring
  have hsmall : (1/(A B*scale n))*(∫ z in (A B*scale n)..4*(A B*scale n), f z) < ε := by
    rw [hratio]
    have hh₁ := h₁ r
    change (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n), f z) < ε/4 at hh₁
    linarith
  apply lt_of_le_of_lt _ hsmall
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact residueBinAverage_shifted_discrete_energy_le E ζ μ w r hHB hX0 j
    ((by exact_mod_cast hj : (j : ℝ) ≤ M B).trans hX.le)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_CoarseResidueSmoothingDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem coarse_residue_smoothing_energy_proved_jd_oai
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) (b : Fin m)
    {q : ℕ} [NeZero q] (A scale : ℕ → ℝ) (R M : ℕ → ℕ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hR : Tendsto R atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop, ∀ (j : ℕ), j ≤ M B →
      (1/(A B*scale n))*(∑ u ∈ Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊,
        ‖residueSmoothed (fun k =>
          (binLabel (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ k-μ)*
            (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b) k : ℂ))
            q (R B) (u+j)‖^2) < ε := by
  have hq : 0 < q := NeZero.pos q
  have hqR : Tendsto (fun B => q*R B) atTop atTop := tendsto_atTop_mono (fun B => by nlinarith : ∀ B, R B ≤ q*R B) hR
  have hs := all_residues_coarse_shifted_short_proved hKMT hM hSD hSW hMP
    hJ ζ hζ μ hμ hmean hm b (q := q) A scale (fun B => q*R B) M hA hscale hqR
  intro ε hε
  let δ := ε/((q : ℝ)^3+1)
  have hδ : 0 < δ := by dsimp [δ] <;> positivity
  filter_upwards [hs δ hδ,hR.eventually_gt_atTop 0] with B hB hRB
  filter_upwards [hB,(hscale.const_mul_atTop (hA B)).eventually_gt_atTop 0] with n hn hX
  intro j hj
  let E := fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)
  let w := primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b)
  let g := fun k => (binLabel E ζ k-μ)*(w k : ℂ)
  let I := Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊
  have hpoint (u : ℕ) : ‖residueSmoothed g q (R B) (u+j)‖^2 ≤
      (q : ℝ)^2*∑ r : ZMod q, ‖residueBinAverage E ζ μ w r (q*R B : ℕ) (u+j)‖^2 := by
    rw [residueSmoothed_eq_residueBinAverage E ζ μ w hq hRB,norm_mul,Complex.norm_natCast,mul_pow]
    simp only [Nat.cast_add]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact single_le_sum
      (f := fun r : ZMod q => ‖residueBinAverage E ζ μ w r (q*R B : ℕ) ((u : ℝ)+j)‖^2)
      (fun r _ => sq_nonneg _) (mem_univ ((u : ZMod q)+(j : ZMod q)))
  have hsum := sum_le_sum (fun r (_ : r ∈ (univ : Finset (ZMod q))) => (hn j hj r).le)
  change (∑ r : ZMod q, (1/(A B*scale n))*(∑ u ∈ I,
    ‖residueBinAverage E ζ μ w r (q*R B : ℕ) (u+j)‖^2)) ≤ _ at hsum
  simp only [sum_const,card_univ,ZMod.card,nsmul_eq_mul] at hsum
  calc
    _ ≤ (1/(A B*scale n))*(∑ u ∈ I, (q : ℝ)^2*
        ∑ r : ZMod q, ‖residueBinAverage E ζ μ w r (q*R B : ℕ) (u+j)‖^2) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun u _ => hpoint u)) (by positivity)
    _ = (q : ℝ)^2*∑ r : ZMod q, (1/(A B*scale n))*(∑ u ∈ I,
        ‖residueBinAverage E ζ μ w r (q*R B : ℕ) (u+j)‖^2) := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro u _
      ring
    _ ≤ (q : ℝ)^2*((q : ℝ)*δ) := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ < ε := by
      dsimp [δ]
      have hden : 0 < (q : ℝ)^3+1 := by positivity
      have he : (q : ℝ)^2*((q : ℝ)*(ε/((q : ℝ)^3+1))) =
          (q : ℝ)^3*ε/((q : ℝ)^3+1) := by ring
      rw [he]
      apply (div_lt_iff₀ hden).mpr
      nlinarith

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.coarse_residue_smoothing_energy_proved_jd_oai := @OAI.JointDickman.coarse_residue_smoothing_energy_proved_jd_oai
