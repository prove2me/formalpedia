-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.normalized_two_ball_obstruction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T17:20:09.371265+00:00
-- url     : https://prove2.me/submissions/99177e42-0958-44d6-bc25-dd31dd20d4da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp007
import Definitions.Def_OAIQ10Bp008
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_affineHolderModuli_isCompact
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_densityFixedPoint_residual_zero
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_densityResidual_zero_affineLine
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_densityResponse_contDiffAt
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_densityResponse_locallyPrecompact
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_densityResponse_zero_time
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_homotopy_coefficient_extension
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_homotopy_density_common_support
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_packing_two_line_reduction
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_responseCoefficient_invertible
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_uniform_density_bounds
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_zero_mem_affineHolderModuli
import Theorems.Thm_OAI_TwoPointContinuation_local_degree_continuation

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_CompatibleStructures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HigherDimensionalBallPacking
open scoped ContDiff

noncomputable section
open scoped Topology
open Set Function Filter

namespace Rigidity

theorem standardForm_J_pos {n : ℕ} {v : Phase n} (hv : v ≠ 0) :
    0 < standardForm v (standardJ n v) := by
  rw [standardForm_J_self]
  have hi : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hi
  have hpos : 0 < Complex.normSq (v i) := Complex.normSq_pos.mpr hi
  exact hpos.trans_le (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j))
    (Finset.mem_univ i))

end Rigidity
end
end HigherDimensionalBallPacking

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity

theorem stdDot_pos {n : ℕ} {v : Phase n} (hv : v ≠ 0) : 0 < stdDot n v v := by
  rw [← standardForm_J_right]
  exact standardForm_J_pos hv

theorem relativeOperator_positive {n : ℕ} {J : End n} (hJ : Compatible J)
    {v : Phase n} (hv : v ≠ 0) : 0 < stdDot n v (relativeOperator J v) := by
  rw [stdDot_relativeOperator]
  exact hJ.2.2 v hv

theorem cayleyP_invertible {n : ℕ} {J : End n} (hJ : Compatible J)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : (cayleyP J b a).IsInvertible := by
  have hi : Injective (cayleyP J b a) := by
    apply (injective_iff_map_eq_zero (cayleyP J b a)).mpr
    intro v hv
    by_contra hne
    have hp := stdDot_pos hne
    have hA := relativeOperator_positive hJ hne
    have he : stdDot n v (cayleyP J b a v) =
        b * stdDot n v (relativeOperator J v) + a * stdDot n v v := by
      simp only [cayleyP_apply, map_add, map_smul, smul_eq_mul]
    rw [hv] at he
    simp only [map_zero] at he
    have hn := mul_nonneg hb hA.le
    have hh := mul_pos ha hp
    linarith
  have hs := (LinearMap.injective_iff_surjective (f := (cayleyP J b a).toLinearMap)).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective (cayleyP J b a)
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs), rfl⟩

theorem cayleyOperator_on_denominator {n : ℕ} {J : End n} {a b : ℝ}
    (hQ : (cayleyP J b a).IsInvertible) (v : Phase n) :
    cayleyOperator J a b (cayleyP J b a v) = cayleyP J a b v := by
  obtain ⟨e,he⟩ := hQ
  simp only [cayleyOperator, ←he, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

@[simp] theorem interpolateJ_zero {n : ℕ} {J : End n} (hJ : Compatible J) :
    interpolateJ J 0 = standardJ n := by
  have hQ := cayleyP_invertible hJ (a := 1) (b := 1) (by norm_num) (by norm_num)
  obtain ⟨e,he⟩ := hQ
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  change standardJ n (cayleyOperator J (1+0) (1-0) ((e : End n) x)) = standardJ n ((e : End n) x)
  simp only [add_zero, sub_zero, he, cayleyOperator_on_denominator ⟨e,he⟩]

@[simp] theorem interpolateJ_one {n : ℕ} {J : End n} (hJ : Compatible J) :
    interpolateJ J 1 = J := by
  have hQ := cayleyP_invertible hJ (a := 2) (b := 0) (by norm_num) (by norm_num)
  obtain ⟨e,he⟩ := hQ
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := e.surjective v
  change standardJ n (cayleyOperator J (1+1) (1-1) ((e : End n) x)) = J ((e : End n) x)
  norm_num only [he, show (1:ℝ)+1=2 by norm_num, sub_self,
    cayleyOperator_on_denominator ⟨e,he⟩]
  simp

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Rigidity_Adapted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter

@[simp] theorem lineHomotopy_zero {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) (x : Phase n) : lineHomotopy J 0 x = standardJ n :=
  interpolateJ_zero (hJ x)

@[simp] theorem lineHomotopy_one {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) (x : Phase n) : lineHomotopy J 1 x = J x :=
  interpolateJ_one (hJ x)


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_MarkedInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem c1Holder_contDiff (α : ℝ) (u : C1HolderSpace E α) :
    ContDiff ℝ 1 (holderValue α (c1HolderValue α u)) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨holderValue α (c1HolderDeriv α u),
    (holderValue α (c1HolderDeriv α u)).continuous,c1Holder_hasFDerivAt α u⟩

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]


lemma compactCRInverse_rightInverse (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    fderiv ℝ (compactCRInverseValue R u) x Complex.I -
      Complex.I • fderiv ℝ (compactCRInverseValue R u) x 1 = compactHolderValue R u x := by
  let v := compactHolderMap R (((Complex.I/2) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ) u
  have hh := cauchyTransform_holder_complexCurl (compactHolderValue R v).continuous
    (compactHolderValue_compactSupport R v) (compactHolderValue_bound R v) (norm_nonneg v)
    (compactHolderValue_holder R v) x
  have he : (compactCRInverseValue R u : ℂ → E) = cauchyTransform (compactHolderValue R v) := by
    funext z
    exact compactHolderCauchyCLM_value R v z
  rw [he]
  have hs : (2*Complex.I) • compactHolderValue R v x = -compactHolderValue R u x := by
    change (2*Complex.I) • ((Complex.I/2) • compactHolderValue R u x) = _
    rw [smul_smul,show (2*Complex.I)*(Complex.I/2)=(-1:ℂ) by ring_nf;simp,neg_one_smul]
  rw [hs] at hh
  change Complex.I • _ - _ = _ at hh
  apply neg_injective
  simpa only [neg_sub] using hh

lemma compactCRInverse_contDiff (R : ℝ) (u : CompactHolderSpace E R) :
    ContDiff ℝ 1 (compactCRInverseValue R u) := c1Holder_contDiff _ _

lemma compactCRInverse_tendsto_zero (R : ℝ) (u : CompactHolderSpace E R) :
    Tendsto (compactCRInverseValue R u) (cocompact ℂ) (𝓝 0) := by
  let v := compactHolderMap R (((Complex.I/2) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ) u
  have he : (compactCRInverseValue R u : ℂ → E) = cauchyTransform (compactHolderValue R v) := by
    funext z
    exact compactHolderCauchyCLM_value R v z
  rw [he]
  exact cauchyTransform_tendsto_zero (compactHolderValue R v).continuous
    (compactHolderValue_compactSupport R v)



lemma markedCRInverse_rightInverse (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    fderiv ℝ (markedCRInverse R u) x Complex.I -
      Complex.I • fderiv ℝ (markedCRInverse R u) x 1 = compactHolderValue R u x := by
  have hd := c1Holder_hasFDerivAt ((1:ℝ)/3) (compactCRInverse R u) x
  have ha := (hasFDerivAt_id (𝕜 := ℝ) x).smul_const
    (compactCRInverseValue R u 1-compactCRInverseValue R u 0)
  have ht := (hd.sub_const (compactCRInverseValue R u 0)).sub ha
  change HasFDerivAt (markedCRInverse R u) _ x at ht
  rw [ht.fderiv]
  simp only [sub_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply,one_smul,smul_sub]
  have hh := compactCRInverse_rightInverse R u x
  simp only [compactCRInverseValue,c1Holder_fderiv] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  abel

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_HolderCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal

open scoped ContDiff Topology
open Set Function Filter

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma markedCRInverse_differentiable (R : ℝ) (g : CompactHolderSpace E R) :
    Differentiable ℝ (markedCRInverse R g) := by
  exact (((compactCRInverse_contDiff R g).differentiable (by norm_num)).sub_const _).sub
    (differentiable_id.smul_const _)

end HigherDimensionalBallPacking.Rigidity

 

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
open FramedCR

 
theorem entire_weak_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {u : ℂ → E} (hd : Differentiable ℂ u) {a : E}
    (ha : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a)) :
    u=fun z : ℂ => u 0+z • a := by
  have hs : Differentiable ℂ (dslope u 0) := by
    rw [←differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (by simp : (univ : Set ℂ) ∈ 𝓝 (0:ℂ))).mpr hd.differentiableOn
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 (0:ℂ)) := by
    rw [←Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hl : Tendsto (dslope u 0) (cocompact ℂ) (𝓝 a) := by
    have he : Tendsto (fun z : ℂ => z⁻¹ • u z-z⁻¹ • u 0) (cocompact ℂ) (𝓝 a) := by
      simpa only [zero_smul,sub_zero] using ha.sub (hi.smul_const (u 0))
    apply he.congr'
    filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
    have hz0 : z ≠ 0 := by simpa using hz
    simp only [dslope_of_ne u hz0,slope_def_module,sub_zero,smul_sub]
  have hconst := hs.eq_const_of_tendsto_cocompact hl
  funext z
  have he := sub_smul_dslope u (0:ℂ) z
  rw [sub_zero,hconst] at he
  have he2 : u z-u 0=z • a := by simpa only [Function.const_apply] using he.symm
  exact (sub_eq_iff_eq_add.mp he2).trans (add_comm _ _)

theorem affineLine_density_representation {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (R : ℝ) (g : CompactHolderSpace (Phase n) R)
    (hg : ∀ z, compactHolderValue R g z=standardCurl u z) :
    u=densityCurve p q R g := by
  let f := compactCRInverseValue R g
  have hf : Differentiable ℝ f := (compactCRInverse_contDiff R g).differentiable (by simp)
  have hholo : Differentiable ℂ (fun z => u z-f z) := by
    intro z
    have hd := ((hu.1.differentiable (by simp) z).hasFDerivAt).sub ((hf z).hasFDerivAt)
    apply differentiableAt_complex_iff_differentiableAt_real.mpr
    refine ⟨hd.differentiableAt,?_⟩
    change fderiv ℝ (u-(f : ℂ → Phase n)) z Complex.I =
      Complex.I • fderiv ℝ (u-(f : ℂ → Phase n)) z 1
    rw [hd.fderiv]
    simp only [sub_apply,smul_sub]
    have he := compactCRInverse_rightInverse R g z
    rw [hg] at he
    change fderiv ℝ f z Complex.I-Complex.I • fderiv ℝ f z 1 =
      fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1 at he
    exact sub_eq_sub_iff_sub_eq_sub.mp he.symm
  obtain ⟨a,ha,hal⟩ := hu.2.2.2.2
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 (0:ℂ)) := by
    rw [←Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hfl : Tendsto (fun z => z⁻¹ • f z) (cocompact ℂ) (𝓝 (0 : Phase n)) := by
    simpa only [zero_smul] using hi.smul (compactCRInverse_tendsto_zero R g)
  have hw : Tendsto (fun z => z⁻¹ • (u z-f z)) (cocompact ℂ) (𝓝 a) := by
    simpa only [smul_sub,sub_zero] using hal.sub hfl
  have hrep := entire_weak_affine hholo hw
  have ha' : a=q-p-(f 1-f 0) := by
    have h := congrFun hrep (1:ℂ)
    simp only [one_smul,hu.2.2.1,hu.2.2.2.1] at h
    calc
      a=(p-f 0+a)-(p-f 0) := by abel
      _=(q-f 1)-(p-f 0) := by rw [←h]
      _=q-p-(f 1-f 0) := by abel
  funext z
  have h := congrFun hrep z
  simp only [hu.2.2.1,ha'] at h
  change u z=p+z • (q-p)+(f z-f 0-z • (f 1-f 0))
  rw [smul_sub] at h
  linear_combination h

theorem densityCurve_curl {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) (z : ℂ) :
    standardCurl (densityCurve p q R g) z=compactHolderValue R g z := by
  have hd := (hasFDerivAt_const (𝕜 := ℝ) p z).add
    ((hasFDerivAt_id (𝕜 := ℝ) z).smul_const (q-p))
  have hg := (markedCRInverse_differentiable R g z).hasFDerivAt
  have h := hd.add hg
  change HasFDerivAt (densityCurve p q R g) _ z at h
  unfold standardCurl
  rw [h.fderiv]
  simp only [add_apply,zero_add,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,one_smul,smul_add]
  have he := markedCRInverse_rightInverse R g z
  linear_combination he

theorem densitySlope_continuous {n : ℕ} (p q : Phase n) (R : ℝ) :
    Continuous (densitySlope p q R) := by
  have h (z : ℂ) : Continuous (fun g : CompactHolderSpace (Phase n) R =>
      compactCRInverseValue R g z) :=
    ((c1HolderEval ((1:ℝ)/3) z).comp (compactCRInverse R)).continuous
  exact continuous_const.sub ((h 1).sub (h 0))

theorem affineHolderModuli_iff {n : ℕ} (J : Phase n → End n)
    (p q : Phase n) (R : ℝ) (t : ℝ) (g : CompactHolderSpace (Phase n) R) :
    (t,g) ∈ affineHolderModuli J p q R ↔ t ∈ Icc (0:ℝ) 1 ∧
      AffineLineCurve (lineHomotopy J t) p q (densityCurve p q R g) := by
  constructor
  · rintro ⟨ht,u,hu,hg⟩
    exact ⟨ht,affineLine_density_representation hu R g hg ▸ hu⟩
  · rintro ⟨ht,hu⟩
    exact ⟨ht,densityCurve p q R g,hu,fun z => (densityCurve_curl p q R g z).symm⟩

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity FramedCR

 theorem densityAffineSize_continuous {n : ℕ} (p : Phase n) (R : ℝ) : Continuous (densityAffineSize p R) := by
  have hc : Continuous (compactCRInverseValue (E := Phase n) R) :=
    ((holderValue ((1:ℝ)/3)).comp ((c1HolderValue ((1:ℝ)/3)).comp (compactCRInverse R))).continuous
  exact (continuous_const.sub ((BoundedContinuousFunction.evalCLM ℝ (0:ℂ)).continuous.comp hc)).norm.add hc.norm

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity








open scoped ContDiff Topology
open Set Filter Function
open HigherDimensionalBallPacking.Rigidity

 theorem densityCurve_eq_profile {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) :
    densityCurve p q R g=c1HolderAffineCurve ((1:ℝ)/3)
      (p-compactCRInverseValue R g 0) (densityLinearSlope p q R g) (compactCRInverse R g) := by
  funext z
  change p+z • (q-p)+(compactCRInverseValue R g z-compactCRInverseValue R g 0-
    z • (compactCRInverseValue R g 1-compactCRInverseValue R g 0))=
    p-compactCRInverseValue R g 0+z • densitySlope p q R g+compactCRInverseValue R g z
  simp only [densitySlope,smul_sub]
  abel

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem densityCurve_lower_bound {n : ℕ} (p q : Phase n) (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) (z : ℂ) :
    ‖z‖*‖densitySlope p q R g‖ ≤ ‖densityCurve p q R g z‖+densityAffineSize p R g := by
  have he : z • densitySlope p q R g=densityCurve p q R g z-(p-compactCRInverseValue R g 0)-compactCRInverseValue R g z := by
    rw [densityCurve_eq_profile]
    change z • densitySlope p q R g=((p-compactCRInverseValue R g 0)+z • densitySlope p q R g+compactCRInverseValue R g z)-(p-compactCRInverseValue R g 0)-compactCRInverseValue R g z
    abel
  have hn : ‖z • densitySlope p q R g‖≤‖densityCurve p q R g z‖+‖p-compactCRInverseValue R g 0‖+‖compactCRInverseValue R g z‖ := by
    rw [he]
    have h1 := norm_sub_le (densityCurve p q R g z-(p-compactCRInverseValue R g 0)) (compactCRInverseValue R g z)
    have h2 := norm_sub_le (densityCurve p q R g z) (p-compactCRInverseValue R g 0)
    linarith
  rw [norm_smul] at hn
  have hb := (compactCRInverseValue R g).norm_coe_le_norm z
  unfold densityAffineSize
  linarith

 theorem goodDensities_isOpen {n : ℕ} (p q : Phase n) (R m M : ℝ) : IsOpen (goodDensities p q R m M) :=
  (isOpen_lt continuous_const (densitySlope_continuous p q R).norm).inter
    (isOpen_lt (densityAffineSize_continuous p R) continuous_const)

 theorem goodDensities_slope_ne {n : ℕ} (p q : Phase n) (R m M : ℝ) (hm : 0 < m)
    (g : CompactHolderSpace (Phase n) R) (hg : g∈goodDensities p q R m M) : densitySlope p q R g≠0 :=
  norm_pos_iff.mp (hm.trans hg.1)

 theorem goodDensities_exterior {n : ℕ} (p q : Phase n) (R m M C S : ℝ) (hm : 0 < m)
    (hS : 0 < S) (hSC : M+C≤S*m)
    (A : ℝ × Phase n → End n) (hAc : ∀ y∈tsupport A, ‖y‖≤C)
    (t : ℝ) (g : CompactHolderSpace (Phase n) R) (hg : g∈goodDensities p q R m M)
    (z : ℂ) (hz : S<‖z‖) : A (t,densityCurve p q R g z)=0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hy
  have hb : ‖densityCurve p q R g z‖≤C := (_root_.norm_snd_le _).trans (hAc _ hy)
  have hl := densityCurve_lower_bound p q R g z
  have hmul : S*m<‖z‖*‖densitySlope p q R g‖ :=
    mul_lt_mul hz hg.1.le hm (le_of_lt (hS.trans hz))
  linarith [hg.2]

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_DensityExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function







open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity TwoPointContinuation

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.actualDensityGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.actualDensitySpace
theorem actual_affine_line_exists (n : ℕ) (hn : 3≤n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p≠q) :
    ∃ u : ℂ → Phase n, AffineLineCurve J p q u := by
  obtain ⟨R₀,hR₀,hRc⟩ := homotopy_density_common_support n hn J hJs hJ hc hs p q hpq
  obtain ⟨m,M,hm,hM,hbounds⟩ := uniform_density_bounds n hn J hJs hJ hc hs p q hpq
  obtain ⟨A,hA,hAc,hAe⟩ := homotopy_coefficient_extension hJs hJ hc
  obtain ⟨C,hC⟩ := hAc.isBounded.exists_norm_le
  let S : ℝ := max R₀ ((M+C)/m)+1
  have hS₀ : R₀<S := lt_add_of_le_of_pos (le_max_left _ _) zero_lt_one
  have hS : 0<S := hR₀.trans hS₀
  have hSC : M+C≤S*m := by
    have hh : (M+C)/m≤S := (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
    exact (div_le_iff₀ hm).mp hh
  let b : ContDiffBump (0:ℂ) := ⟨S,S+1,hS,lt_add_one _⟩
  let B : ContDiffBump (0:ℂ) := ⟨S+2,S+3,by linarith,by linarith⟩
  have hbB : b.rOut≤B.rIn := by dsimp [b,B]; linarith
  let V := goodDensities p q b.rOut m M
  let K := Prod.snd '' affineHolderModuli J p q b.rOut
  let T := densityResponse b B p q A hA hAc
  have hV : IsOpen V := goodDensities_isOpen p q b.rOut m M
  have hK : IsCompact K := by
    apply IsCompact.image _ continuous_snd
    apply affineHolderModuli_isCompact n hn J hJs hJ hc hs p q hpq b.rOut
    intro t ht u hu z hz
    apply hRc t ht u hu z
    exact hS₀.trans (lt_trans (by dsimp [b]; exact lt_add_one _) hz)
  have hKV : K⊆V := by
    rintro g ⟨y,hy,rfl⟩
    exact hbounds b.rOut y hy
  have h0 : 0∈K := ⟨(0,0),zero_mem_affineHolderModuli J hJ p q hpq b.rOut,rfl⟩
  have houtside (t : ℝ) (g : CompactHolderSpace (Phase n) b.rOut) (hg : g∈V) :
      ∀ z : ℂ, b.rIn<‖z‖ → A (t,densityCurve p q b.rOut g z)=0 :=
    goodDensities_exterior p q b.rOut m M C S hm hS hSC A hC t g hg
  have hinv (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (g : CompactHolderSpace (Phase n) b.rOut) (hg : g∈V) :
      (cutoffFrozen b (responseCoefficient b B A hA hAc (responseCoords B p q b.rOut (t,g)))).IsInvertible :=
    responseCoefficient_invertible b B hbB p q A hA hAc J hJs hJ hc hAe (t,g) ht (houtside t g hg)
  have hline (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (g : CompactHolderSpace (Phase n) b.rOut)
      (hg : g∈V) (he : T (t,g)=g) : AffineLineCurve (lineHomotopy J t) p q (densityCurve p q b.rOut g) := by
    apply densityResidual_zero_affineLine p q b.rOut A hA hAc J hJs hJ hc hAe (t,g) ht
      (goodDensities_slope_ne p q b.rOut m M hm g hg)
    exact densityFixedPoint_residual_zero b B hbB p q A hA hAc (t,g) (houtside t g hg) (hinv t ht g hg) he
  obtain ⟨g,hg,hfix⟩ := local_degree_continuation T V hV
    (fun t ht g hg => (densityResponse_contDiffAt b B p q A hA hAc (t,g) (hinv t ht g hg)).continuousAt)
    (fun g _ => densityResponse_zero_time b B hbB p q A hA hAc (by
      intro x
      rw [hAe 0 (by norm_num) x,lineHomotopy_zero hJ,sub_self]) g)
    K hK hKV h0
    (by
      intro t ht g hg he
      refine ⟨(t,g),?_,rfl⟩
      rw [affineHolderModuli_iff]
      exact ⟨ht,hline t ht g hg he⟩)
    (fun t ht g hg => densityResponse_locallyPrecompact b B p q A hA hAc (t,g) (hinv t ht g (hKV hg)))
  refine ⟨densityCurve p q b.rOut g,?_⟩
  convert hline 1 (by norm_num) g hg hfix using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  exact (lineHomotopy_one hJ x).symm

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_PackingNecessity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking
section
open Rigidity

theorem normalized_two_ball_obstruction_oai (n : ℕ) (hn : 3 ≤ n)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hp : HasPacking n 2 1 ![a,b]) : a+b ≤ 1 := by
  obtain ⟨J,p,q,hJs,hJ,hJc,hJinside,hpq,harea⟩ := packing_two_line_reduction ha hb hp
  obtain ⟨u,hu⟩ := actual_affine_line_exists n hn J hJs hJ hJc hJinside p q hpq
  exact harea u hu

end

 

 

 

open scoped ENNReal NNReal Topology ContDiff Pointwise
open Set MeasureTheory








open scoped ContDiff Topology
open Set Function







open scoped ContDiff Topology
open Set Function
open Rigidity

end HigherDimensionalBallPacking

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.normalized_two_ball_obstruction_oai := @OAI.HigherDimensionalBallPacking.normalized_two_ball_obstruction_oai
