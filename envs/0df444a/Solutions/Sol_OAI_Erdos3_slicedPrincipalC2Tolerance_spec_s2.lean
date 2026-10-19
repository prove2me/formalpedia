-- Prove2me | solution 1 for OAI.Erdos3.slicedPrincipalC2Tolerance_spec_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:45:48.636068+00:00
-- url     : https://prove2.me/submissions/15500aae-1837-4b18-ab05-491a1c011574

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B065
import Definitions.Def_OAIE3v2B066
import Definitions.Def_OAIE3v2B067
import Definitions.Def_OAIE3v2B096
import Theorems.Thm_OAI_Erdos3_selected_cutoff_comparison_of_close_derivatives_s2
import Theorems.Thm_OAI_Erdos3_unitBoxInteriorCutoff_mass_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnitBoxAmplitude
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem positiveUnitBox_measurable : MeasurableSet (positiveUnitBox ι) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ProductCutoffBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem product_cutoff_range {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1) : (∏ i, f i) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg (fun i _ => (hf i).1),
    Finset.prod_le_one (fun i _ => (hf i).1) (fun i _ => (hf i).2)⟩

theorem product_cutoff_tsupport_subset {ι E : Type*} [Fintype ι] [TopologicalSpace E]
    (f : ι → E → ℝ) (i : ι) : tsupport (fun x => ∏ j, f j x) ⊆ tsupport (f i) := by
  classical
  apply closure_mono
  intro x hx
  change f i x ≠ 0
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

theorem product_cutoff_fderiv_norm_le {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ι → E → ℝ) (x : E) (hf : ∀ i, DifferentiableAt ℝ (f i) x)
    (hrange : ∀ i, f i x ∈ Set.Icc (0 : ℝ) 1) :
    ‖fderiv ℝ (fun y => ∏ i, f i y) x‖ ≤ ∑ i, ‖fderiv ℝ (f i) x‖ := by
  classical
  rw [fderiv_finsetProd (fun i _ => hf i)]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hp0 : 0 ≤ ∏ j ∈ Finset.univ.erase i, f j x :=
    Finset.prod_nonneg (fun j _ => (hrange j).1)
  have hp1 : (∏ j ∈ Finset.univ.erase i, f j x) ≤ 1 :=
    Finset.prod_le_one (fun j _ => (hrange j).1) (fun j _ => (hrange j).2)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp0]
  exact mul_le_of_le_one_left (norm_nonneg _) hp1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.OperatorCoordinateBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem clm_norm_le_card_mul_of_entries {I O : Type*}
    [Fintype I] [DecidableEq I] [Fintype O]
    (A : (I → ℝ) →L[ℝ] (O → ℝ)) {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ i o, |A (Pi.single i 1) o| ≤ M) : ‖A‖ ≤ Fintype.card I * M := by
  apply clm_norm_le_card_mul_of_basis A hM
  intro i
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro o
  simpa only [Real.norm_eq_abs] using hA i o

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothHalfspaceCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem halfspaceCutoff_range {E : Type*} (r : ℝ) (d : E → ℝ) (x : E) :
    halfspaceCutoff r d x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem halfspaceCutoff_eq_zero {E : Type*} {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) {x : E} (hx : d x ≤ r) : halfspaceCutoff r d x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact sub_nonpos.mpr ((div_le_one hr).mpr hx)

theorem halfspaceCutoff_tsupport_subset {E : Type*} [TopologicalSpace E]
    {r : ℝ} (hr : 0 < r) (d : E → ℝ) (hd : Continuous d) :
    tsupport (halfspaceCutoff r d) ⊆ {x | r ≤ d x} := by
  apply closure_minimal _ (isClosed_le continuous_const hd)
  intro x hx
  change r ≤ d x
  by_contra! h
  exact hx (halfspaceCutoff_eq_zero hr d h.le)

theorem contDiff_halfspaceCutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (d : E → ℝ) (hd : ContDiff ℝ ∞ d) : ContDiff ℝ ∞ (halfspaceCutoff r d) :=
  Real.smoothTransition.contDiff.comp ((hd.div_const r).sub contDiff_const)

theorem halfspaceCutoff_fderiv_norm_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ≥0) (hLip : LipschitzWith A Real.smoothTransition)
    {r : ℝ} (hr : 0 < r) (d : E → ℝ) {x : E} (hd : DifferentiableAt ℝ d x) :
    ‖fderiv ℝ (halfspaceCutoff r d) x‖ ≤ (A : ℝ) / r * ‖fderiv ℝ d x‖ := by
  have ht : DifferentiableAt ℝ Real.smoothTransition (r⁻¹ • d x - 1) :=
    ((Real.smoothTransition.contDiff : ContDiff ℝ 1 _).differentiable one_ne_zero).differentiableAt
  have heq : halfspaceCutoff r d = Real.smoothTransition ∘ (fun y => r⁻¹ • d y - 1) := by
    funext y
    simp only [halfspaceCutoff, Function.comp_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq]
  change ‖fderiv ℝ (Real.smoothTransition ∘ (fun y => (r⁻¹ • d) y - 1)) x‖ ≤ _
  rw [fderiv_comp x ht ((hd.const_smul r⁻¹).sub_const 1),
    fderiv_sub_const, fderiv_const_smul hd]
  calc
    _ ≤ ‖fderiv ℝ Real.smoothTransition (r⁻¹ • d x - 1)‖ * ‖r⁻¹ • fderiv ℝ d x‖ :=
      (fderiv ℝ Real.smoothTransition _).opNorm_comp_le _
    _ ≤ (A : ℝ) * ‖r⁻¹ • fderiv ℝ d x‖ :=
      mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg _)
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeDomain
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff NNReal

theorem inequalityBoundaryCutoff_range {I E : Type*} [Fintype I]
    (r : I → ℝ) (d : I → E → ℝ) (x : E) :
    inequalityBoundaryCutoff r d x ∈ Set.Icc (0 : ℝ) 1 :=
  product_cutoff_range _ (fun i => halfspaceCutoff_range (r i) (d i) x)

theorem inequalityBoundaryCutoff_smooth {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (r : I → ℝ) (d : I → E → ℝ)
    (hd : ∀ i, ContDiff ℝ ∞ (d i)) : ContDiff ℝ ∞ (inequalityBoundaryCutoff r d) :=
  contDiff_prod (fun i _ => contDiff_halfspaceCutoff (r i) (d i) (hd i))

theorem inequalityBoundaryCutoff_tsupport_subset {I E : Type*} [Fintype I]
    [TopologicalSpace E] (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (d : I → E → ℝ) (hd : ∀ i, Continuous (d i)) :
    tsupport (inequalityBoundaryCutoff r d) ⊆ {x | ∀ i, r i ≤ d i x} := by
  intro x hx i
  exact halfspaceCutoff_tsupport_subset (hr i) (d i) (hd i)
    (product_cutoff_tsupport_subset (fun j => halfspaceCutoff (r j) (d j)) i hx)

theorem inequalityBoundaryCutoff_fderiv_norm_le {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ≥0) (hLip : LipschitzWith A Real.smoothTransition)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (d : I → E → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i)) (x : E) :
    ‖fderiv ℝ (inequalityBoundaryCutoff r d) x‖ ≤
      ∑ i, ((A : ℝ) / r i) * ‖fderiv ℝ (d i) x‖ := by
  apply (product_cutoff_fderiv_norm_le (fun i => halfspaceCutoff (r i) (d i)) x
    (fun i => ((contDiff_halfspaceCutoff (r i) (d i) (hd i)).differentiable (by norm_num)).differentiableAt)
    (fun i => halfspaceCutoff_range (r i) (d i) x)).trans
  exact Finset.sum_le_sum (fun i _ => halfspaceCutoff_fderiv_norm_le A hLip (hr i) (d i)
    (((hd i).differentiable (by norm_num)).differentiableAt))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateInjection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem coordinateInjection_apply {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) (x : ι → ℝ) :
    coordinateInjection f x = ∑ i, Pi.single (f i) (x i) := by
  simp only [coordinateInjection, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.single_apply, ContinuousLinearMap.proj_apply]

theorem coordinateInjection_at_image {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) (x : ι → ℝ) (i : ι) :
    coordinateInjection f x (f i) = x i := by
  classical
  simp only [coordinateInjection_apply, Finset.sum_apply, Pi.single_apply]
  simp [hf.eq_iff]

theorem coordinateInjection_off_image {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) (x : ι → ℝ) (j : κ) (hj : ∀ i, f i ≠ j) :
    coordinateInjection f x j = 0 := by
  have hji : ∀ i, j ≠ f i := fun i => (hj i).symm
  simp only [coordinateInjection_apply, Finset.sum_apply, Pi.single_apply, hji, ite_false,
    Finset.sum_const_zero]

theorem coordinateInjection_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) : ‖coordinateInjection f‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [coordinateInjection_at_image f hf]
    exact norm_le_pi_norm x i
  · rw [coordinateInjection_off_image f x j (not_exists.mp hj), norm_zero]
    exact norm_nonneg x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSliceC2Difference
namespace OAI

section

namespace Erdos3

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem operatorPrecompose_norm_le (J : E →L[ℝ] X) :
    ‖operatorPrecompose (Y := Y) J‖ ≤ ‖J‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg J)
  intro A
  exact (A.opNorm_comp_le J).trans_eq (mul_comm _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialParameterContinuity
namespace OAI

section

namespace Erdos3

theorem polynomialOperator_fderiv_entry {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (A : (I → ℝ) → (J → ℝ) →L[ℝ] (O → ℝ)) (p : Matrix O J (MvPolynomial I ℝ))
    (hentry : ∀ y row col, A y (Pi.single col 1) row = MvPolynomial.eval y (p row col))
    (x : I → ℝ) (hA : DifferentiableAt ℝ A x) (j : I) (row : O) (col : J) :
    (fderiv ℝ A x (Pi.single j 1)) (Pi.single col 1) row =
      MvPolynomial.eval x (MvPolynomial.pderiv j (p row col)) := by
  have hscalar : (fun y => A y (Pi.single col 1) row) =
      (fun y => MvPolynomial.eval y (p row col)) := funext (fun y => hentry y row col)
  have hB : DifferentiableAt ℝ (fun y => A y (Pi.single col 1)) x :=
    hA.clm_apply (differentiableAt_const _)
  have hp := mvPolynomial_fderiv_coordinate (p row col) x j
  rw [← hscalar, fderiv_apply hB row, fderiv_clm_apply hA (differentiableAt_const _)] at hp
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.flip_apply] at hp
  exact hp

theorem polynomialOperator_fderiv_norm_le {I J O : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (A : (I → ℝ) → (J → ℝ) →L[ℝ] (O → ℝ)) (p : Matrix O J (MvPolynomial I ℝ))
    (hentry : ∀ y row col, A y (Pi.single col 1) row = MvPolynomial.eval y (p row col))
    (x : I → ℝ) (hA : DifferentiableAt ℝ A x) {M : ℝ} (hM : 0 ≤ M)
    (hp : ∀ row col j, |MvPolynomial.eval x (MvPolynomial.pderiv j (p row col))| ≤ M) :
    ‖fderiv ℝ A x‖ ≤ Fintype.card I * (Fintype.card J * M) := by
  apply clm_norm_le_card_mul_of_basis _ (mul_nonneg (Nat.cast_nonneg _) hM)
  intro j
  apply clm_norm_le_card_mul_of_entries _ hM
  intro col row
  rw [polynomialOperator_fderiv_entry A p hentry x hA j row col]
  exact hp row col j

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]

omit [DecidableEq I] in
theorem polynomialVectorMap_contDiff (p : O → MvPolynomial I ℝ) :
    ContDiff ℝ ∞ (polynomialVectorMap p) := contDiff_pi.mpr (fun o => mvPolynomial_contDiff_eval (p o))

theorem polynomialVectorMap_fderiv_entry (p : O → MvPolynomial I ℝ) (x : I → ℝ) (i : I) (o : O) :
    fderiv ℝ (polynomialVectorMap p) x (Pi.single i 1) o =
      MvPolynomial.eval x (MvPolynomial.pderiv i (p o)) := by
  have hd := (polynomialVectorMap_contDiff p).differentiable (by norm_num) x
  have he := mvPolynomial_fderiv_coordinate (p o) x i
  change fderiv ℝ (fun y => polynomialVectorMap p y o) x (Pi.single i 1) = _ at he
  rw [fderiv_apply hd o] at he
  exact he

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators ContDiff

theorem polynomialVectorMap_mass_c2_bounds {I O : Type*}
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (p : O → MvPolynomial I ℝ) {d : ℕ} (hd : ∀ o i, (p o).degreeOf i ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hmass : ∀ o, realPolynomialMass (p o) ≤ C)
    (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ‖polynomialVectorMap p x‖ ≤ C ∧
      ‖fderiv ℝ (polynomialVectorMap p) x‖ ≤ Fintype.card I * ((d : ℝ) * C) ∧
      ‖fderiv ℝ (fderiv ℝ (polynomialVectorMap p)) x‖ ≤
        Fintype.card I * (Fintype.card I * ((d : ℝ) * ((d : ℝ) * C))) := by
  have hfirst (o : O) (i : I) : realPolynomialMass (pderiv i (p o)) ≤ (d : ℝ) * C :=
    (realPolynomialMass_pderiv_degreeOf (p o) i (hd o i)).trans
      (mul_le_mul_of_nonneg_left (hmass o) (Nat.cast_nonneg _))
  have hsecond (o : O) (i j : I) :
      realPolynomialMass (pderiv j (pderiv i (p o))) ≤ (d : ℝ) * ((d : ℝ) * C) :=
    (realPolynomialMass_pderiv_degreeOf (pderiv i (p o)) j
      (mvPolynomial_pderiv_degreeOf_le (p o) i j (hd o j))).trans
      (mul_le_mul_of_nonneg_left (hfirst o i) (Nat.cast_nonneg _))
  refine ⟨?_, ?_, ?_⟩
  · apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro o
    exact (mvPolynomial_eval_abs_le_sum_coeff (p o) x hx).trans (hmass o)
  · apply clm_norm_le_card_mul_of_entries _ (mul_nonneg (Nat.cast_nonneg _) hC)
    intro i o
    rw [polynomialVectorMap_fderiv_entry]
    exact (mvPolynomial_eval_abs_le_sum_coeff (pderiv i (p o)) x hx).trans (hfirst o i)
  · have hs : ContDiff ℝ 2 (polynomialVectorMap p) :=
      (polynomialVectorMap_contDiff p).of_le (by first | exact WithTop.coe_le_coe.2 le_top | exact ENat.LEInfty.out | (norm_cast; done) | exact_mod_cast le_top)
    have hs' : ContDiff ℝ 1 (fderiv ℝ (polynomialVectorMap p)) := hs.fderiv_right (by norm_num)
    exact polynomialOperator_fderiv_norm_le _ (fun o i => pderiv i (p o))
      (fun y o i => polynomialVectorMap_fderiv_entry p y i o) x (hs'.differentiable one_ne_zero x)
      (by positivity) (fun o i j =>
        (mvPolynomial_eval_abs_le_sum_coeff (pderiv j (pderiv i (p o))) x hx).trans (hsecond o i j))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SigmaAxisOperator
namespace OAI

section

namespace Erdos3

variable {D : Type*} [Fintype D] {I O P : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)] [∀ d, Fintype (P d)]

omit [Fintype D] [∀ d, Fintype (I d)] [∀ d, Fintype (O d)] [∀ d, Fintype (P d)] in
theorem sigmaAxisOperator_comp (A : ∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ))
    (B : ∀ d, (O d → ℝ) →L[ℝ] (P d → ℝ)) :
    (sigmaAxisOperator B).comp (sigmaAxisOperator A) =
      sigmaAxisOperator (fun d => (B d).comp (A d)) := by
  ext x s
  rfl

omit [Fintype D] [∀ d, Fintype (I d)] in
theorem sigmaAxisOperator_inverse_spec (A : ∀ d, (I d → ℝ) →L[ℝ] (I d → ℝ))
    (hA : ∀ d, (A d).IsInvertible) :
    (sigmaAxisOperator A).IsInvertible ∧
      (sigmaAxisOperator A).inverse = sigmaAxisOperator (fun d => (A d).inverse) := by
  have hr : (sigmaAxisOperator A).comp (sigmaAxisOperator (fun d => (A d).inverse)) =
      ContinuousLinearMap.id ℝ ((Σ d, I d) → ℝ) := by
    ext x s
    change A s.1 ((A s.1).inverse (sigmaAxisProjection I s.1 x)) s.2 = x s
    rw [(hA s.1).self_apply_inverse]
    rfl
  have hl : (sigmaAxisOperator (fun d => (A d).inverse)).comp (sigmaAxisOperator A) =
      ContinuousLinearMap.id ℝ ((Σ d, I d) → ℝ) := by
    ext x s
    change (A s.1).inverse (A s.1 (sigmaAxisProjection I s.1 x)) s.2 = x s
    rw [(hA s.1).inverse_apply_self]
    rfl
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse hr hl, ContinuousLinearMap.inverse_eq hr hl⟩

theorem sigmaAxisOperator_inverse_norm_le (A : ∀ d, (I d → ℝ) →L[ℝ] (I d → ℝ))
    (hA : ∀ d, (A d).IsInvertible) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ d, ‖(A d).inverse‖ ≤ K) :
    (sigmaAxisOperator A).IsInvertible ∧ ‖(sigmaAxisOperator A).inverse‖ ≤ K := by
  obtain ⟨hi, he⟩ := sigmaAxisOperator_inverse_spec A hA
  refine ⟨hi, ?_⟩
  rw [he]
  exact sigmaAxisOperator_norm_le _ hK hbound

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CanonicalSamplerTuple
namespace OAI

section

namespace Erdos3

open scoped ContDiff NNReal

variable {D : Type*} [Fintype D] {I O : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)]

theorem sigmaAxisSampler_contDiff (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (hU : ∀ d, ContDiff ℝ ∞ (U d)) : ContDiff ℝ ∞ (sigmaAxisSampler U) :=
  contDiff_pi.mpr (fun s => ((contDiff_apply ℝ ℝ s.2).comp (hU s.1)).comp
    (sigmaAxisProjection I s.1).contDiff)

theorem sigmaAxisSampler_hasFDerivAt (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (x : (Σ d, I d) → ℝ)
    (hU : ∀ d, DifferentiableAt ℝ (U d) (sigmaAxisProjection I d x)) :
    HasFDerivAt (sigmaAxisSampler U)
      (sigmaAxisOperator (fun d => fderiv ℝ (U d) (sigmaAxisProjection I d x))) x := by
  apply hasFDerivAt_pi.mpr
  intro s
  exact (hasFDerivAt_apply s.2 _).comp x
    ((hU s.1).hasFDerivAt.comp x (sigmaAxisProjection I s.1).hasFDerivAt)

theorem sigmaAxisSampler_fderiv (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (x : (Σ d, I d) → ℝ)
    (hU : ∀ d, DifferentiableAt ℝ (U d) (sigmaAxisProjection I d x)) :
    fderiv ℝ (sigmaAxisSampler U) x =
      sigmaAxisOperator (fun d => fderiv ℝ (U d) (sigmaAxisProjection I d x)) :=
  (sigmaAxisSampler_hasFDerivAt U x hU).fderiv

theorem sigmaAxisSampler_selectedDerivative (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (J : ∀ d, (O d → ℝ) →L[ℝ] (I d → ℝ)) (x : (Σ d, I d) → ℝ)
    (hU : ∀ d, DifferentiableAt ℝ (U d) (sigmaAxisProjection I d x)) :
    selectedDerivative (sigmaAxisSampler U) (sigmaAxisOperator J) x =
      sigmaAxisOperator (fun d => selectedDerivative (U d) (J d) (sigmaAxisProjection I d x)) := by
  unfold selectedDerivative
  rw [sigmaAxisSampler_fderiv U x hU, sigmaAxisOperator_comp]

theorem sigmaAxisSampler_inverse_bound (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (J : ∀ d, (O d → ℝ) →L[ℝ] (I d → ℝ)) (x : (Σ d, I d) → ℝ)
    (hU : ∀ d, DifferentiableAt ℝ (U d) (sigmaAxisProjection I d x))
    (hinv : ∀ d, (selectedDerivative (U d) (J d) (sigmaAxisProjection I d x)).IsInvertible)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ d, ‖(selectedDerivative (U d) (J d) (sigmaAxisProjection I d x)).inverse‖ ≤ K) :
    (selectedDerivative (sigmaAxisSampler U) (sigmaAxisOperator J) x).IsInvertible ∧
      ‖(selectedDerivative (sigmaAxisSampler U) (sigmaAxisOperator J) x).inverse‖ ≤ K := by
  rw [sigmaAxisSampler_selectedDerivative U J x hU]
  exact sigmaAxisOperator_inverse_norm_le _ hinv hK hbound

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem realDensityMeasure_indicator {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) {S : Set X} (hS : MeasurableSet S) :
    realDensityMeasure μ (S.indicator f) = (realDensityMeasure μ f).restrict S := by
  have he : (fun x => ENNReal.ofReal (S.indicator f x)) =
      S.indicator (fun x => ENNReal.ofReal (f x)) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
  unfold realDensityMeasure
  rw [he, withDensity_indicator hS, restrict_withDensity hS]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnitBoxInteriorCutoff
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {ι : Type*} [Fintype ι]

theorem unitBoxFace_contDiff (j : Bool × ι) : ContDiff ℝ ∞ (unitBoxFace j) := by
  rcases j with ⟨b, i⟩
  cases b
  · change ContDiff ℝ ∞ (fun x : ι → ℝ => x i)
    fun_prop
  · change ContDiff ℝ ∞ (fun x : ι → ℝ => 1 - x i)
    fun_prop

theorem unitBoxFace_lipschitz (j : Bool × ι) : LipschitzWith 1 (unitBoxFace j) := by
  rcases j with ⟨b, i⟩
  cases b
  · exact LipschitzWith.eval i
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [unitBoxFace, ↓reduceIte, NNReal.coe_one, one_mul, dist_sub_left] using
      dist_le_pi_dist x y i

theorem unitBoxInteriorCutoff_range (r : ℝ) (x : ι → ℝ) :
    unitBoxInteriorCutoff r x ∈ Set.Icc (0 : ℝ) 1 :=
  inequalityBoundaryCutoff_range _ _ _

theorem unitBoxInteriorCutoff_contDiff (r : ℝ) : ContDiff ℝ ∞ (unitBoxInteriorCutoff (ι := ι) r) :=
  inequalityBoundaryCutoff_smooth _ _ unitBoxFace_contDiff

theorem unitBoxInteriorCutoff_tsupport {r : ℝ} (hr : 0 < r)
    {x : ι → ℝ} (hx : x ∈ tsupport (unitBoxInteriorCutoff r)) :
    ∀ i, r ≤ x i ∧ x i ≤ 1 - r := by
  have h := inequalityBoundaryCutoff_tsupport_subset (fun _ : Bool × ι => r)
    (fun _ => hr) unitBoxFace (fun j => (unitBoxFace_contDiff j).continuous) hx
  intro i
  have h0 : r ≤ x i := h (false, i)
  have h1 : r ≤ 1 - x i := h (true, i)
  exact ⟨h0, by linarith⟩

theorem unitBoxInteriorCutoff_support_box {r : ℝ} (hr : 0 < r) :
    tsupport (unitBoxInteriorCutoff (ι := ι) r) ⊆ positiveUnitBox ι := by
  intro x hx i _
  have hi := unitBoxInteriorCutoff_tsupport hr hx i
  exact ⟨hr.trans_le hi.1, hi.2.trans (by linarith)⟩

theorem unitBoxInteriorCutoff_compact {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (unitBoxInteriorCutoff (ι := ι) r) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : ι => r) (fun _ : ι => 1 - r))).of_isClosed_subset
    (isClosed_tsupport _)
  intro x hx
  exact ⟨fun i => (unitBoxInteriorCutoff_tsupport hr hx i).1,
    fun i => (unitBoxInteriorCutoff_tsupport hr hx i).2⟩

theorem unitBoxInteriorCutoff_density {r : ℝ} (hr : 0 < r) :
    realDensityMeasure volume (unitBoxInteriorCutoff (ι := ι) r) =
      realDensityMeasure (unitBoxMeasure ι) (unitBoxInteriorCutoff r) := by
  have hi : (positiveUnitBox ι).indicator (unitBoxInteriorCutoff r) = unitBoxInteriorCutoff r := by
    apply Set.indicator_eq_self.2
    intro x hx
    exact unitBoxInteriorCutoff_support_box hr (subset_tsupport _ hx)
  have h := realDensityMeasure_indicator volume (unitBoxInteriorCutoff r)
    (positiveUnitBox_measurable (ι := ι))
  rw [hi] at h
  exact h.trans (restrict_withDensity (positiveUnitBox_measurable (ι := ι)) _)

theorem unitBoxInteriorCutoff_fderiv_bound (A : ℝ≥0)
    (hA : LipschitzWith A Real.smoothTransition) {r : ℝ} (hr : 0 < r) (x : ι → ℝ) :
    ‖fderiv ℝ (unitBoxInteriorCutoff r) x‖ ≤ 2 * Fintype.card ι * A / r := by
  have h := inequalityBoundaryCutoff_fderiv_norm_le A hA
    (fun _ : Bool × ι => r) (fun _ => hr) unitBoxFace unitBoxFace_contDiff x
  apply h.trans
  calc
    _ ≤ ∑ _j : Bool × ι, (A : ℝ) / r := Finset.sum_le_sum (fun j _ =>
      mul_le_of_le_one_right (div_nonneg A.coe_nonneg hr.le)
        (norm_fderiv_le_of_lipschitz ℝ (unitBoxFace_lipschitz j)))
    _ = _ := by simp [Fintype.card_prod]; ring

theorem unitBoxInteriorCutoff_directional_integral (A : ℝ≥0)
    (hA : LipschitzWith A Real.smoothTransition) {r : ℝ} (hr : 0 < r) (v : ι → ℝ) :
    (∫ x, |fderiv ℝ (unitBoxInteriorCutoff r) x v|) ≤
      (2 * Fintype.card ι * A / r) * ‖v‖ := by
  let L : ℝ := 2 * Fintype.card ι * A / r
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hb (x : ι → ℝ) : |fderiv ℝ (unitBoxInteriorCutoff r) x v| ≤ L * ‖v‖ := by
    exact ((fderiv ℝ (unitBoxInteriorCutoff r) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (unitBoxInteriorCutoff_fderiv_bound A hA hr x) (norm_nonneg v))
  have hm : Measurable (fun x : ι → ℝ => |fderiv ℝ (unitBoxInteriorCutoff r) x v|) :=
    (((unitBoxInteriorCutoff_contDiff r).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).abs.measurable
  have hi : Integrable (fun x : ι → ℝ => |fderiv ℝ (unitBoxInteriorCutoff r) x v|)
      (unitBoxMeasure ι) :=
    (integrable_const (L * ‖v‖)).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, abs_abs] using hb x))
  have he : (∫ x, |fderiv ℝ (unitBoxInteriorCutoff r) x v|) =
      ∫ x, |fderiv ℝ (unitBoxInteriorCutoff r) x v| ∂unitBoxMeasure ι := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (unitBoxInteriorCutoff_support_box hr h))]
    simp
  rw [he]
  have h := integral_mono hi (integrable_const (L * ‖v‖)) hb
  simpa only [integral_const, probReal_univ, one_smul] using h

theorem unitBoxInteriorCutoff_derivative_budget [DecidableEq ι] (A : ℝ≥0)
    (hA : LipschitzWith A Real.smoothTransition) {r : ℝ} (hr : 0 < r) :
    (∑ j : ι, ∫ x, |fderiv ℝ (unitBoxInteriorCutoff r) x (Pi.single j 1)|) ≤
      2 * (Fintype.card ι : ℝ) ^ 2 * A / r := by
  calc
    _ ≤ ∑ _j : ι, 2 * Fintype.card ι * A / r := Finset.sum_le_sum (fun j _ => by
      simpa only [Pi.norm_single, norm_one, mul_one] using
        unitBoxInteriorCutoff_directional_integral A hA hr (Pi.single j 1))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPerturbationScaleBudget
namespace OAI

section

namespace Erdos3

theorem polynomialPerturbationScale_spec {K M Q τ : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hτ : 0 < τ) (m : ℕ) :
    let t := polynomialPerturbationScale K M Q τ m
    0 < t ∧ t ≤ 1 ∧ K * (t * M) ≤ 1 / 2 ∧ t * M ≤ 1 ∧
      4 * (m : ℝ) * Real.sqrt (Q * (t * (1 + M))) ≤ τ := by
  let t := polynomialPerturbationScale K M Q τ m
  have ht : 0 < t := by dsimp [t, polynomialPerturbationScale]; positivity
  have ht1 : t ≤ 1 := min_le_left _ _
  have htK : t ≤ 1 / (2 * (1 + K) * (1 + M)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have htQ : t ≤ τ ^ 2 / (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hden : t * (2 * (1 + K) * (1 + M)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp htK
  have h2KM : 2 * K * M ≤ 2 * (1 + K) * (1 + M) := by nlinarith
  have hMden : M ≤ 2 * (1 + K) * (1 + M) := by nlinarith [mul_nonneg hK hM]
  have hsmall : K * (t * M) ≤ 1 / 2 := by
    have hh := (mul_le_mul_of_nonneg_left h2KM ht.le).trans hden
    nlinarith
  have hsecond : t * M ≤ 1 := (mul_le_mul_of_nonneg_left hMden ht.le).trans hden
  refine ⟨ht, ht1, hsmall, hsecond, ?_⟩
  have hdenQ : t * (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M)) ≤ τ ^ 2 :=
    (le_div_iff₀ (by positivity)).mp htQ
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hm2 : (m : ℝ) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
  have hpoly : 16 * (m : ℝ) ^ 2 * Q * (1 + M) ≤
      16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M) := by
    gcongr
    linarith
  have hb := (mul_le_mul_of_nonneg_left hpoly ht.le).trans hdenQ
  have hroot := Real.sq_sqrt (show 0 ≤ Q * (t * (1 + M)) by positivity)
  have hroot0 := Real.sqrt_nonneg (Q * (t * (1 + M)))
  have hsquare : (4 * (m : ℝ) * Real.sqrt (Q * (t * (1 + M)))) ^ 2 ≤ τ ^ 2 := by
    calc
      _ = t * (16 * (m : ℝ) ^ 2 * Q * (1 + M)) := by
        rw [mul_pow, mul_pow, hroot]
        ring
      _ ≤ _ := hb
  nlinarith [mul_nonneg (show 0 ≤ 4 * (m : ℝ) by positivity) hroot0]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedPrincipalInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff NNReal

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

omit [DecidableEq B] [DecidableEq F] in
theorem principalSliceValue_contDiff (c : B → ℝ) (lower width : B × F → ℝ) :
    ContDiff ℝ ∞ (principalSliceValue c lower width) := by
  unfold principalSliceValue
  fun_prop

theorem principalSliceValue_fderiv_single (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) (b : B) (i : F) :
    fderiv ℝ (principalSliceValue c lower width) x (Pi.single (b, i) 1) =
      principalSliceSlope c lower width x b i := by
  let g := fun b j (y : B × F → ℝ) => lower (b, j) + width (b, j) * y (b, j)
  have hd (b : B) (j : F) : HasFDerivAt (g b j)
      (width (b, j) • (ContinuousLinearMap.proj (b, j) : (B × F → ℝ) →L[ℝ] ℝ)) x := by
    have he : HasFDerivAt (fun y : B × F → ℝ => y (b, j))
        (ContinuousLinearMap.proj (b, j) : (B × F → ℝ) →L[ℝ] ℝ) x :=
      hasFDerivAt_apply (b, j) x
    simpa only [g] using (he.const_mul (width (b, j))).const_add (lower (b, j))
  have hp (b : B) := HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ => hd b j)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ => (hp b).const_mul (c b))
  change fderiv ℝ (fun y => ∑ b, c b * ∏ j, g b j y) x (Pi.single (b, i) 1) = _
  rw [hs.fderiv]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single b]
  · rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, mul_one, principalSliceSlope, g]
      ring
    · intro j _ hji
      simp [hji]
    · simp
  · intro b' _ hbb
    simp [hbb]
  · simp

omit [Fintype B] [DecidableEq B] in
theorem principalSliceSlope_lower (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) (b : B) (i : F) {a δ r : ℝ}
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hc : a ≤ |c b|)
    (hw : ∀ j, δ ≤ width (b, j))
    (hlower : ∀ j ≠ i, 0 ≤ lower (b, j)) (hx : ∀ j ≠ i, r ≤ x (b, j)) :
    a * δ * (δ * r) ^ (Fintype.card F - 1) ≤ |principalSliceSlope c lower width x b i| := by
  have hfactor (j) (hj : j ∈ Finset.univ.erase i) :
      δ * r ≤ lower (b, j) + width (b, j) * x (b, j) := by
    have hji := Finset.ne_of_mem_erase hj
    exact (mul_le_mul (hw j) (hx j hji) hr (hδ.trans (hw j))).trans
      (le_add_of_nonneg_left (hlower j hji))
  have hprod : (δ * r) ^ (Fintype.card F - 1) ≤
      ∏ j ∈ Finset.univ.erase i, (lower (b, j) + width (b, j) * x (b, j)) := by
    have h := Finset.prod_le_prod (s := Finset.univ.erase i)
      (fun _ _ => mul_nonneg hδ hr) hfactor
    simpa only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ] using h
  have hp0 := (pow_nonneg (mul_nonneg hδ hr) (Fintype.card F - 1)).trans hprod
  rw [principalSliceSlope, abs_mul, abs_mul, abs_of_nonneg (hδ.trans (hw i)),
    abs_of_nonneg hp0]
  exact mul_le_mul (mul_le_mul hc (hw i) hδ (ha.trans hc)) hprod
    (pow_nonneg (mul_nonneg hδ hr) _) (mul_nonneg (abs_nonneg _) (hδ.trans (hw i)))

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ContDiff BigOperators

theorem scalar_identity_inverse_abs_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℝ} (ha : a ≠ 0) :
    (a • ContinuousLinearMap.id ℝ E).IsInvertible ∧
      ‖(a • ContinuousLinearMap.id ℝ E).inverse‖ ≤ |a|⁻¹ := by
  let A := a • ContinuousLinearMap.id ℝ E
  let B := a⁻¹ • ContinuousLinearMap.id ℝ E
  have hAB : A.comp B = ContinuousLinearMap.id ℝ E := by
    ext x
    simp [A, B, smul_smul, ha]
  have hBA : B.comp A = ContinuousLinearMap.id ℝ E := by
    ext x
    simp [A, B, smul_smul, ha]
  refine ⟨ContinuousLinearMap.IsInvertible.of_inverse hAB hBA, ?_⟩
  change ‖A.inverse‖ ≤ _
  rw [ContinuousLinearMap.inverse_eq hAB hBA]
  calc
    ‖B‖ = |a|⁻¹ * ‖ContinuousLinearMap.id ℝ E‖ := by
      simp only [B, norm_smul, Real.norm_eq_abs, abs_inv]
    _ ≤ |a|⁻¹ := mul_le_of_le_one_right (inv_nonneg.mpr (abs_nonneg _))
      ContinuousLinearMap.norm_id_le

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

omit [DecidableEq B] [DecidableEq F] in
theorem principalSliceSingleton_contDiff (c : B → ℝ) (lower width : B × F → ℝ) :
    ContDiff ℝ ∞ (principalSliceSingleton c lower width) :=
  contDiff_pi.mpr (fun _ => principalSliceValue_contDiff c lower width)

theorem principalSliceSingleton_selectedDerivative (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) (b : B) (i : F) :
    selectedDerivative (principalSliceSingleton c lower width)
      (coordinateInjection (fun _ : Unit => (b, i))) x =
      principalSliceSlope c lower width x b i • ContinuousLinearMap.id ℝ (Unit → ℝ) := by
  have hd := (principalSliceSingleton_contDiff c lower width).differentiable (by norm_num)
  have hh := principalSliceValue_fderiv_single c lower width x b i
  change fderiv ℝ (fun y => principalSliceSingleton c lower width y ()) x
    (Pi.single (b, i) 1) = _ at hh
  rw [fderiv_apply (hd x) ()] at hh
  change (fderiv ℝ (principalSliceSingleton c lower width) x (Pi.single (b, i) 1)) () =
    principalSliceSlope c lower width x b i at hh
  ext y u
  cases u
  have hJ : coordinateInjection (fun _ : Unit => (b, i)) y =
      y () • (Pi.single (b, i) 1 : B × F → ℝ) := by
    simp only [coordinateInjection_apply, Fintype.sum_unique, ← Pi.single_smul, smul_eq_mul, mul_one]
  simp only [selectedDerivative, ContinuousLinearMap.comp_apply, hJ, map_smul,
    smul_apply, Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.id_apply, hh]
  ring

theorem principalSliceSingleton_inverse_bound (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) (b : B) (i : F) {κ : ℝ} (hκ : 0 < κ)
    (hbound : κ ≤ |principalSliceSlope c lower width x b i|) :
    (selectedDerivative (principalSliceSingleton c lower width)
      (coordinateInjection (fun _ : Unit => (b, i))) x).IsInvertible ∧
      ‖(selectedDerivative (principalSliceSingleton c lower width)
        (coordinateInjection (fun _ : Unit => (b, i))) x).inverse‖ ≤ κ⁻¹ := by
  rw [principalSliceSingleton_selectedDerivative]
  have h := scalar_identity_inverse_abs_bound
    (E := Unit → ℝ) (abs_pos.mp (hκ.trans_le hbound))
  exact ⟨h.1, h.2.trans (inv_anti₀ hκ hbound)⟩

section Joint

variable {D : Type*} [Fintype D]
variable {B F : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
variable [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]

theorem jointSlicedInjection_norm_le (b : ∀ d, B d) (i : ∀ d, F d) :
    ‖jointSlicedInjection b i‖ ≤ 1 :=
  sigmaAxisOperator_norm_le _ zero_le_one
    (fun _ => coordinateInjection_norm_le _ (Function.injective_of_subsingleton _))

omit [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)] in
theorem jointSlicedPrincipal_contDiff (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) :
    ContDiff ℝ ∞ (jointSlicedPrincipal c lower width) :=
  sigmaAxisSampler_contDiff _ (fun d => principalSliceSingleton_contDiff (c d) (lower d) (width d))

theorem jointSlicedPrincipal_inverse_bound (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) (b : ∀ d, B d) (i : ∀ d, F d)
    (x : (Σ d, B d × F d) → ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hbound : ∀ d, κ ≤ |principalSliceSlope (c d) (lower d) (width d)
      (sigmaAxisProjection (fun d => B d × F d) d x) (b d) (i d)|) :
    (selectedDerivative (jointSlicedPrincipal c lower width) (jointSlicedInjection b i) x).IsInvertible ∧
      ‖(selectedDerivative (jointSlicedPrincipal c lower width) (jointSlicedInjection b i) x).inverse‖ ≤ κ⁻¹ := by
  have hi (d) := principalSliceSingleton_inverse_bound (c d) (lower d) (width d)
    (sigmaAxisProjection (fun d => B d × F d) d x) (b d) (i d) hκ (hbound d)
  exact sigmaAxisSampler_inverse_bound _ _ x
    (fun d => (principalSliceSingleton_contDiff (c d) (lower d) (width d)).differentiable
      (by norm_num) _) (fun d => (hi d).1) (inv_nonneg.mpr hκ.le) (fun d => (hi d).2)

end Joint

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SlicedPrincipalPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

variable {B F : Type*} [Fintype B] [Fintype F]

theorem principalSlicePolynomial_eval [DecidableEq B] [DecidableEq F]
    (c : B → ℝ) (lower width : B × F → ℝ) (x : B × F → ℝ) :
    MvPolynomial.eval x (principalSlicePolynomial c lower width) = principalSliceValue c lower width x := by
  simp [principalSlicePolynomial, principalSliceValue]

theorem principalSlicePolynomial_degree (c : B → ℝ) (lower width : B × F → ℝ) :
    (principalSlicePolynomial c lower width).totalDegree ≤ Fintype.card F := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro b _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _i : F, 1 := Finset.sum_le_sum (fun i _ => by
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le (by simp)
      exact (MvPolynomial.totalDegree_mul _ _).trans (by simp))
    _ = _ := by simp

theorem principalSlicePolynomial_mass (c : B → ℝ) (lower width : B × F → ℝ)
    (hwidth : ∀ p, |lower p| + |width p| ≤ 1) :
    realPolynomialMass (principalSlicePolynomial c lower width) ≤ ∑ b, |c b| := by
  classical
  apply (realPolynomialMass_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  apply (realPolynomialMass_C_mul_le _ _).trans
  apply mul_le_of_le_one_right (abs_nonneg _)
  apply (realPolynomialMass_prod_le _ _).trans
  apply Finset.prod_le_one (fun _ _ => realPolynomialMass_nonneg _)
  intro i _
  apply (realPolynomialMass_add_le _ _).trans
  calc
    _ ≤ |lower (b, i)| + |width (b, i)| := by
      rw [realPolynomialMass_C]
      apply add_le_add le_rfl
      simpa only [realPolynomialMass_X, mul_one] using
        realPolynomialMass_C_mul_le (width (b, i)) (MvPolynomial.X (b, i))
    _ ≤ 1 := hwidth (b, i)

section Joint

variable {D : Type*} [Fintype D] {B F : D → Type*}
variable [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
variable [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]

omit [Fintype D] in
theorem jointSlicedPolynomial_map (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) :
    polynomialVectorMap (jointSlicedPolynomial c lower width) = jointSlicedPrincipal c lower width := by
  funext x o
  change MvPolynomial.eval x (MvPolynomial.rename _ _) = _
  rw [MvPolynomial.eval_rename, principalSlicePolynomial_eval]
  rfl

theorem jointSlicedPrincipal_c2_bounds (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) {m : ℕ}
    (hdegree : ∀ d, Fintype.card (F d) ≤ m)
    (hwidth : ∀ d p, |lower d p| + |width d p| ≤ 1)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ d, (∑ b, |c d b|) ≤ C)
    (x : (Σ d, B d × F d) → ℝ) (hx : ∀ p, |x p| ≤ 1) :
    let N := Fintype.card (Σ d, B d × F d)
    ‖jointSlicedPrincipal c lower width x‖ ≤ C ∧
      ‖fderiv ℝ (jointSlicedPrincipal c lower width) x‖ ≤ N * ((m : ℝ) * C) ∧
      ‖fderiv ℝ (fderiv ℝ (jointSlicedPrincipal c lower width)) x‖ ≤
        N * (N * ((m : ℝ) * ((m : ℝ) * C))) := by
  classical
  have hd (o : Σ _d : D, Unit) (p : Σ d, B d × F d) :
      (jointSlicedPolynomial c lower width o).degreeOf p ≤ m :=
    (MvPolynomial.degreeOf_le_totalDegree _ _).trans
      ((MvPolynomial.totalDegree_rename_le _ _).trans
        ((principalSlicePolynomial_degree _ _ _).trans (hdegree o.1)))
  have hm (o : Σ _d : D, Unit) : realPolynomialMass (jointSlicedPolynomial c lower width o) ≤ C :=
    (realPolynomialMass_rename_le _ _).trans
      ((principalSlicePolynomial_mass _ _ _ (hwidth o.1)).trans (hc o.1))
  have h := polynomialVectorMap_mass_c2_bounds (jointSlicedPolynomial c lower width) hd hC hm x hx
  rwa [jointSlicedPolynomial_map] at h

end Joint

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanStability
namespace OAI

section

namespace Erdos3

variable {I O : Type*} [Fintype I] [Fintype O]

theorem selectedDerivative_fderiv_eq (U : (I → ℝ) → (O → ℝ))
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) (x : I → ℝ)
    (hU : DifferentiableAt ℝ (fderiv ℝ U) x) :
    fderiv ℝ (selectedDerivative U J) x =
      (operatorPrecompose J).comp (fderiv ℝ (fderiv ℝ U) x) := by
  let L : ((I → ℝ) →L[ℝ] (O → ℝ)) →L[ℝ] ((O → ℝ) →L[ℝ] (O → ℝ)) := operatorPrecompose J
  change fderiv ℝ (L ∘ fderiv ℝ U) x = _
  rw [fderiv_comp x L.differentiableAt hU, L.fderiv]

theorem selectedDerivative_second_error (U V : (I → ℝ) → (O → ℝ))
    (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) (hJ : ‖J‖ ≤ 1) (x : I → ℝ) :
    ‖fderiv ℝ (selectedDerivative V J) x - fderiv ℝ (selectedDerivative U J) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ := by
  have hU' : ContDiff ℝ 1 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
  have hV' : ContDiff ℝ 1 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  rw [selectedDerivative_fderiv_eq V J x (hV'.differentiable one_ne_zero x),
    selectedDerivative_fderiv_eq U J x (hU'.differentiable one_ne_zero x),
    ← ContinuousLinearMap.comp_sub]
  have hL : ‖operatorPrecompose (Y := O → ℝ) J‖ ≤ 1 := (operatorPrecompose_norm_le J).trans hJ
  calc
    _ ≤ ‖operatorPrecompose J‖ * ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ :=
      mul_le_mul_of_nonneg_right hL
        (norm_nonneg (fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x))
    _ = _ := one_mul _

theorem selectedDerivative_bound_of_second_error (U V : (I → ℝ) → (O → ℝ))
    (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) (hJ : ‖J‖ ≤ 1) (x : I → ℝ)
    {H E : ℝ} (hH : ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H)
    (hE : ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ U) x‖ ≤ E) :
    ‖fderiv ℝ (selectedDerivative V J) x‖ ≤ H + E := by
  have ht := norm_add_le (fderiv ℝ (selectedDerivative V J) x - fderiv ℝ (selectedDerivative U J) x)
    (fderiv ℝ (selectedDerivative U J) x)
  have he : fderiv ℝ (selectedDerivative V J) x - fderiv ℝ (selectedDerivative U J) x +
      fderiv ℝ (selectedDerivative U J) x = fderiv ℝ (selectedDerivative V J) x := by
    ext y z i
    simp
  rw [he] at ht
  exact ht.trans ((add_le_add ((selectedDerivative_second_error U V hU hV J hJ x).trans hE) hH).trans_eq
    (add_comm E H))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

theorem slicedPrincipalComparisonBudget_nonneg (N m : ℕ) {C A r κ : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hr : 0 < r) (hκ : 0 < κ) :
    0 ≤ slicedPrincipalComparisonBudget N m C A r κ := by
  unfold slicedPrincipalComparisonBudget
  positivity

theorem jointSlicedPrincipal_unitBox_comparison
    {D : Type*} [Fintype D] {B F : D → Type*}
    [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]
    (c : ∀ d, B d → ℝ) (lower width : ∀ d, B d × F d → ℝ)
    (b : ∀ d, B d) (i : ∀ d, F d) {m : ℕ}
    (hdegree : ∀ d, Fintype.card (F d) ≤ m)
    (hwidth : ∀ d p, |lower d p| + |width d p| ≤ 1)
    {C a δ r κ ε : ℝ} (hC : 0 ≤ C) (hc : ∀ d, (∑ b, |c d b|) ≤ C)
    (ha : 0 < a) (hδ : 0 < δ) (hr : 0 < r) (hκ : 0 < κ)
    (hprincipal : ∀ d, a ≤ |c d (b d)|)
    (hselectedWidth : ∀ d j, δ ≤ width d (b d, j))
    (hselectedLower : ∀ d j, j ≠ i d → 0 ≤ lower d (b d, j))
    (hminor : ∀ d, κ ≤ a * δ * (δ * r) ^ (Fintype.card (F d) - 1))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (V : ((Σ d, B d × F d) → ℝ) → ((Σ _d : D, Unit) → ℝ))
    (hV : ContDiff ℝ 2 V) (hε : 0 < ε) (hεone : ε ≤ 1) (hsmall : κ⁻¹ * ε ≤ 1 / 2)
    (herr : ∀ x, (∀ p, |x p| ≤ 1) →
      ‖V x - jointSlicedPrincipal c lower width x‖ ≤ ε ∧
      ‖fderiv ℝ V x - fderiv ℝ (jointSlicedPrincipal c lower width) x‖ ≤ ε ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ (jointSlicedPrincipal c lower width)) x‖ ≤ ε)
    (φ : ((Σ _d : D, Unit) → ℝ) → ℝ) (hφ : Measurable φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let N := Fintype.card (Σ d, B d × F d)
    |mappedTest (unitBoxMeasure (Σ d, B d × F d)) (jointSlicedPrincipal c lower width) φ -
      mappedTest (unitBoxMeasure (Σ d, B d × F d)) V φ| ≤
      8 * N * r + 4 * (Fintype.card D : ℝ) *
        Real.sqrt (slicedPrincipalComparisonBudget N m C A r κ * ε) := by
  classical
  let N := Fintype.card (Σ d, B d × F d)
  let U := jointSlicedPrincipal c lower width
  let J := jointSlicedInjection b i
  let w := unitBoxInteriorCutoff (ι := Σ d, B d × F d) r
  let H₀ : ℝ := N * (N * ((m : ℝ) * ((m : ℝ) * C)))
  let K : ℝ≥0 := ⟨κ⁻¹, inv_nonneg.mpr hκ.le⟩
  let H : ℝ≥0 := ⟨H₀ + 1, by dsimp [H₀]; positivity⟩
  let S : ℝ≥0 := ⟨2 * (N : ℝ) ^ 2 * A / r, by positivity⟩
  have hU : ContDiff ℝ 2 U := (jointSlicedPrincipal_contDiff c lower width).of_le (WithTop.coe_le_coe.2 le_top)
  have hJ : ‖J‖ ≤ 1 := jointSlicedInjection_norm_le b i
  have hbox (x) (hx : x ∈ tsupport w) : ∀ p, |x p| ≤ 1 := by
    intro p
    have hp := unitBoxInteriorCutoff_tsupport hr hx p
    rw [abs_of_nonneg (hr.le.trans hp.1)]
    linarith
  have hinv (x) (hx : x ∈ tsupport w) :
      (selectedDerivative U J x).IsInvertible ∧ ‖(selectedDerivative U J x).inverse‖ ≤ K := by
    apply jointSlicedPrincipal_inverse_bound c lower width b i x hκ
    intro d
    apply (hminor d).trans
    apply principalSliceSlope_lower (c d) (lower d) (width d) _ (b d) (i d)
      ha.le hδ.le hr.le (hprincipal d) (hselectedWidth d) (hselectedLower d)
    intro j _
    exact (unitBoxInteriorCutoff_tsupport hr hx ⟨d, b d, j⟩).1
  have hHU₀ (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H₀ := by
    have hsecond := (jointSlicedPrincipal_c2_bounds c lower width hdegree hwidth hC hc x (hbox x hx)).2.2
    have hUd : DifferentiableAt ℝ (fderiv ℝ U) x :=
      (hU.fderiv_right (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiable one_ne_zero x
    rw [selectedDerivative_fderiv_eq U J x hUd]
    have hnonneg : 0 ≤ ‖fderiv ℝ (fderiv ℝ U) x‖ := ContinuousLinearMap.opNorm_nonneg _
    calc
      _ ≤ ‖operatorPrecompose J‖ * ‖fderiv ℝ (fderiv ℝ U) x‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖fderiv ℝ (fderiv ℝ U) x‖ :=
        mul_le_mul_of_nonneg_right ((operatorPrecompose_norm_le J).trans hJ) hnonneg
      _ ≤ H₀ := by simpa only [one_mul] using hsecond
  have hHU (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H :=
    (hHU₀ x hx).trans (by change H₀ ≤ H₀ + 1; linarith)
  have hHV (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative V J) x‖ ≤ H :=
    (selectedDerivative_bound_of_second_error U V hU hV J hJ x (hHU₀ x hx)
      (herr x (hbox x hx)).2.2).trans (add_le_add le_rfl hεone)
  have h := selected_cutoff_comparison_of_close_derivatives_s2
    (unitBoxMeasure (Σ d, B d × F d)) w w
    (unitBoxInteriorCutoff_contDiff r).continuous.measurable (unitBoxInteriorCutoff_range r)
    ((unitBoxInteriorCutoff_contDiff r).of_le (by norm_num))
    (unitBoxInteriorCutoff_compact hr) (fun x => (unitBoxInteriorCutoff_range r x).1)
    (unitBoxInteriorCutoff_density hr) U V hU hV J hJ K H S
    (fun x hx => (hinv x hx).1) (fun x hx => (hinv x hx).2)
    (fun x hx => (mul_le_mul_of_nonneg_left (herr x (hbox x hx)).2.1 K.coe_nonneg).trans hsmall)
    hHU hHV (unitBoxInteriorCutoff_derivative_budget A hA hr) hε
    (unitBoxInteriorCutoff_mass_s2 hr)
    (fun x hx => by
      rw [dist_comm, dist_eq_norm]
      exact (herr x (hbox x (subset_tsupport w hx))).1) φ hφ hφone
  change |mappedTest (unitBoxMeasure (Σ d, B d × F d)) U φ -
      mappedTest (unitBoxMeasure (Σ d, B d × F d)) V φ| ≤
    2 * (4 * (N : ℝ) * r) + 4 * (Fintype.card (Σ _d : D, Unit) : ℝ) *
      Real.sqrt (slicedPrincipalComparisonBudget N m C A r κ * ε) at h
  have hcard : Fintype.card (Σ _d : D, Unit) = Fintype.card D := by simp
  rw [hcard] at h
  exact h.trans_eq (by ring)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

theorem slicedPrincipalBoundaryRadius_spec (N : ℕ) {η : ℝ} (hη : 0 < η) :
    let r := slicedPrincipalBoundaryRadius N η
    0 < r ∧ r ≤ 1 / 4 ∧ 8 * N * r ≤ η / 2 := by
  let r := slicedPrincipalBoundaryRadius N η
  have hr : 0 < r := by dsimp [r, slicedPrincipalBoundaryRadius]; positivity
  have hr1 : r ≤ 1 / 4 := min_le_left _ _
  have he : r ≤ η / (16 * ((N : ℝ) + 1)) := min_le_right _ _
  have hh := (le_div_iff₀ (by positivity : 0 < 16 * ((N : ℝ) + 1))).mp he
  refine ⟨hr, hr1, ?_⟩
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

theorem slicedPrincipalC2Tolerance_spec_s2_oai
    {D : Type*} [Fintype D] {B F : D → Type*}
    [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]
    {m : ℕ} (hdegree : ∀ d, Fintype.card (F d) ≤ m)
    {C a δ η : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) :
    let t := slicedPrincipalC2Tolerance (Fintype.card (Σ d, B d × F d)) (Fintype.card D) m C a δ A η
    0 < t ∧ t ≤ 1 ∧
    ∀ (c : ∀ d, B d → ℝ) (lower width : ∀ d, B d × F d → ℝ)
      (b : ∀ d, B d) (i : ∀ d, F d),
      (∀ d p, |lower d p| + |width d p| ≤ 1) →
      (∀ d, (∑ b, |c d b|) ≤ C) → (∀ d, a ≤ |c d (b d)|) →
      (∀ d j, δ ≤ width d (b d, j)) →
      (∀ d j, j ≠ i d → 0 ≤ lower d (b d, j)) →
      ∀ V : ((Σ d, B d × F d) → ℝ) → ((Σ _d : D, Unit) → ℝ),
      ContDiff ℝ 2 V →
      (∀ x, (∀ p, |x p| ≤ 1) →
        ‖V x - jointSlicedPrincipal c lower width x‖ ≤ t ∧
        ‖fderiv ℝ V x - fderiv ℝ (jointSlicedPrincipal c lower width) x‖ ≤ t ∧
        ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ (jointSlicedPrincipal c lower width)) x‖ ≤ t) →
      ∀ φ : ((Σ _d : D, Unit) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        |mappedTest (unitBoxMeasure (Σ d, B d × F d)) (jointSlicedPrincipal c lower width) φ -
          mappedTest (unitBoxMeasure (Σ d, B d × F d)) V φ| ≤ η := by
  let N := Fintype.card (Σ d, B d × F d)
  let r := slicedPrincipalBoundaryRadius N η
  have hr := slicedPrincipalBoundaryRadius_spec N hη
  let κ := a * δ * (δ * r) ^ m
  have hκ : 0 < κ := mul_pos (mul_pos ha hδ) (pow_pos (mul_pos hδ hr.1) _)
  have hdr : δ * r ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hδone (hr.2.1.trans (by norm_num)) hr.1.le zero_le_one
      _ = 1 := one_mul _
  let Q := slicedPrincipalComparisonBudget N m C A r κ
  have hQ : 0 ≤ Q := slicedPrincipalComparisonBudget_nonneg N m hC A.coe_nonneg hr.1 hκ
  let t := slicedPrincipalC2Tolerance N (Fintype.card D) m C a δ A η
  have ht := polynomialPerturbationScale_spec (inv_nonneg.mpr hκ.le) zero_le_one hQ
    (half_pos hη) (Fintype.card D)
  change 0 < t ∧ t ≤ 1 ∧ κ⁻¹ * (t * 1) ≤ 1 / 2 ∧ t * 1 ≤ 1 ∧
    4 * (Fintype.card D : ℝ) * Real.sqrt (Q * (t * (1 + 1))) ≤ η / 2 at ht
  refine ⟨ht.1, ht.2.1, ?_⟩
  intro c lower width b i hwidth hc hprincipal hw hlower V hV herr φ hφ hφone
  have hminor (d) : κ ≤ a * δ * (δ * r) ^ (Fintype.card (F d) - 1) :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (mul_pos hδ hr.1).le hdr ((Nat.sub_le _ _).trans (hdegree d)))
      (mul_pos ha hδ).le
  have h := jointSlicedPrincipal_unitBox_comparison c lower width b i hdegree hwidth hC hc
    ha hδ hr.1 hκ hprincipal hw hlower hminor A hA V hV ht.1 ht.2.1
    (by simpa only [mul_one] using ht.2.2.1) herr φ hφ hφone
  have hsqrt : 4 * (Fintype.card D : ℝ) * Real.sqrt (Q * t) ≤ η / 2 := by
    apply le_trans _ ht.2.2.2.2
    apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
    exact mul_le_mul_of_nonneg_left (by nlinarith [ht.1] : t ≤ t * (1 + 1)) hQ
  exact h.trans (by change 8 * (N : ℝ) * r + 4 * (Fintype.card D : ℝ) * Real.sqrt (Q * t) ≤ η; linarith [hr.2.2])

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.slicedPrincipalC2Tolerance_spec_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.slicedPrincipalC2Tolerance_spec_s2_oai.{u_1, u_2, u_3}
