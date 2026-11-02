-- Prove2me | solution 1 for OAI.CircleDomainRigidity.principalRealBeltrami
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T06:14:42.072206+00:00
-- url     : https://prove2.me/submissions/c251f270-5eed-4ab8-97b6-cbee171d036f

import Mathlib
import Definitions.Def_Q146C011
import Theorems.Thm_OAI_CircleDomainRigidity_PrincipalSmoothApproximation_exists_principal_limit_data
import Theorems.Thm_OAI_CircleDomainRigidity_exists_principal_smooth_approximation
import Theorems.Thm_OAI_CircleDomainRigidity_exteriorCoefficientAreaTheorem
import Theorems.Thm_OAI_CircleDomainRigidity_unorientedFiniteCircleGreenFormula

section
-- module Solutions.Q146_CD.Cannon_Beltrami_MultiplyLp
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section
section
section
section
section
section
section
section
section
section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace CannonBeltrami

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma multiplier_ae (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ᵐ x ∂ν, ‖m x‖ ≤ k) (f : Lp ℂ 2 ν) :
    multiplier m hm hk hb f =ᵐ[ν] fun x => m x*f x := multiplyLp_ae m hm hb f

lemma norm_multiplier_eq (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    (hunit : ∀ᵐ x ∂ν, ‖m x‖=1) (f : Lp ℂ 2 ν) :
    ‖multiplier m hm zero_le_one (hunit.mono (fun _ h => h.le)) f‖=‖f‖ := by
  let g := multiplier m hm zero_le_one (hunit.mono (fun _ h => h.le)) f
  have he : ∀ᵐ x ∂ν, ‖g x‖=‖f x‖ := by
    filter_upwards [multiplier_ae m hm zero_le_one (hunit.mono (fun _ h => h.le)) f,hunit] with x hx hx'
    dsimp [g]
    rw [hx,norm_mul,hx',one_mul]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.le)))
    (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h => h.ge)))

lemma norm_symbolMultiplier (f : PlaneL2) : ‖symbolMultiplier f‖=‖f‖ :=
  norm_multiplier_eq beurlingSymbol measurable_beurlingSymbol.aestronglyMeasurable
    (.of_forall norm_beurlingSymbol) f

lemma norm_beurling (f : PlaneL2) : ‖beurling f‖=‖f‖ := by
  change ‖planeFourier.symm (symbolMultiplier (planeFourier f))‖=‖f‖
  rw [planeFourier.symm.norm_map,norm_symbolMultiplier,planeFourier.norm_map]

open FourierTransform

open scoped ENNReal

end CannonBeltrami

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConductivityContraction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real-linear conductivity equation is solved in the actual complex
L2 space by contraction. The operator parameter is only the contraction
property of the Beurling operator; the fixed point and its support are
constructed here. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

 theorem conductivityProduct_coe (q : EuclideanPlane → ℝ)
    (hq : AEStronglyMeasurable q volume) (k : ℝ≥0)
    (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) (f : ComplexPlaneL2) :
    conductivityProduct q hq k hb f =ᵐ[volume] fun x => q x • f x :=
  MemLp.coeFn_toLp _

 theorem conductivityConj_coe (f : ComplexPlaneL2) :
    conductivityConj f =ᵐ[volume] fun x => star (f x) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLp f

 theorem conductivitySource_coe (q : EuclideanPlane → ℝ) (hq : MemLp q 2 volume) :
    conductivitySource q hq =ᵐ[volume] fun x => (q x : ℂ) :=
  MemLp.coeFn_toLp _

 theorem conductivityIteration_coe (q : EuclideanPlane → ℝ) (hq : MemLp q 2 volume)
    (k : ℝ≥0) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k)
    (S : ComplexPlaneL2 →L[ℝ] ComplexPlaneL2) (f : ComplexPlaneL2) :
    conductivityIteration q hq k hb S f =ᵐ[volume]
      fun x => (q x : ℂ) * star (1 + S f x) := by
  filter_upwards [Lp.coeFn_add (conductivitySource q hq)
      (conductivityProduct q hq.aestronglyMeasurable k hb (conductivityConj (S f))),
    conductivitySource_coe q hq,
    conductivityProduct_coe q hq.aestronglyMeasurable k hb (conductivityConj (S f)),
    conductivityConj_coe (S f)] with x hx hq' hp hc
  rw [conductivityIteration, hx, Pi.add_apply, hq', hp, hc]
  simp only [Complex.real_smul, star_add, star_one]
  ring

 theorem conductivityIteration_contracting (q : EuclideanPlane → ℝ) (hq : MemLp q 2 volume)
    (k : ℝ≥0) (hk : k < 1) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k)
    (S : ComplexPlaneL2 →L[ℝ] ComplexPlaneL2) (hS : ∀ f, ‖S f‖ ≤ ‖f‖) :
    ContractingWith k (conductivityIteration q hq k hb S) := by
  refine ⟨hk, LipschitzWith.of_dist_le_mul fun f g => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  have he : ‖conductivityIteration q hq k hb S f - conductivityIteration q hq k hb S g‖ ≤
      (k : ℝ) * ‖S (f - g)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [conductivityIteration_coe q hq k hb S f,
      conductivityIteration_coe q hq k hb S g,
      Lp.coeFn_sub (conductivityIteration q hq k hb S f) (conductivityIteration q hq k hb S g),
      Lp.coeFn_sub (S f) (S g), hb] with x hf hg hd hs hqx
    rw [Pi.sub_apply, hf, hg] at hd
    rw [hd, map_sub S, hs]
    have ha : (q x : ℂ) * star (1 + S f x) - (q x : ℂ) * star (1 + S g x) =
        (q x : ℂ) * star (S f x - S g x) := by
      simp only [star_add, star_sub, star_one]
      ring
    rw [ha, norm_mul, norm_star, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right hqx (norm_nonneg _)
  exact he.trans (mul_le_mul_of_nonneg_left (hS (f - g)) k.2)

 theorem exists_conductivity_density (q : EuclideanPlane → ℝ) (hq : MemLp q 2 volume)
    (k : ℝ≥0) (hk : k < 1) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k)
    (S : ComplexPlaneL2 →L[ℝ] ComplexPlaneL2) (hS : ∀ f, ‖S f‖ ≤ ‖f‖) :
    ∃ g : ComplexPlaneL2,
      (∀ᵐ x ∂volume, g x = (q x : ℂ) * star (1 + S g x)) ∧
      ‖g‖ ≤ ‖conductivitySource q hq‖ / (1 - (k : ℝ)) := by
  let A := conductivityIteration q hq k hb S
  have hA : ContractingWith k A := conductivityIteration_contracting q hq k hk hb S hS
  let g := hA.fixedPoint A
  have hg : A g = g := hA.fixedPoint_isFixedPt
  refine ⟨g, ?_, ?_⟩
  · have hh := conductivityIteration_coe q hq k hb S g
    change conductivityIteration q hq k hb S g = g at hg
    rw [hg] at hh
    exact hh
  · have h := hA.dist_fixedPoint_le (0 : ComplexPlaneL2)
    have hz : A 0 = conductivitySource q hq := by
      apply Lp.ext
      filter_upwards [conductivityIteration_coe q hq k hb S 0,
        conductivitySource_coe q hq, Lp.coeFn_zero ℂ 2 (volume : Measure EuclideanPlane)] with x hx hq' h0
      rw [hx, map_zero, h0, Pi.zero_apply, add_zero, star_one, mul_one, hq']
    simpa only [g, dist_zero_left, hz] using h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_ConjugateBeltramiL2
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Beurling operator in the physical plane. Its exact L2
isometry supplies the operator previously parameterized in conductivity
contraction; no second fixed-point argument is needed. -/
open MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma physicalBeurling_norm (f : ComplexPlaneL2) : ‖physicalBeurling f‖ = ‖f‖ := by
  change ‖complexLpToPhysical (beurling (physicalLpToComplex f))‖ = ‖f‖
  rw [complexLpToPhysical.norm_map, norm_beurling, physicalLpToComplex.norm_map]

lemma complexLpToPhysical_coe (f : PlaneL2) :
    complexLpToPhysical f =ᵐ[volume] fun x => f (complexPlaneCoordinates x) :=
  Lp.coeFn_compMeasurePreserving f complexPlaneCoordinates_measurePreserving

lemma physicalLpToComplex_coe (f : ComplexPlaneL2) :
    physicalLpToComplex f =ᵐ[volume] fun z => f (complexPlaneCoordinates.symm z) :=
  Lp.coeFn_compMeasurePreserving f
    (complexPlaneCoordinates_measurePreserving.symm
      complexPlaneCoordinates.toHomeomorph.toMeasurableEquiv)

lemma physicalLpToComplex_complexLpToPhysical (f : PlaneL2) :
    physicalLpToComplex (complexLpToPhysical f) = f := by
  apply Lp.ext
  filter_upwards [physicalLpToComplex_coe (complexLpToPhysical f),
    (complexPlaneCoordinates_measurePreserving.symm
      complexPlaneCoordinates.toHomeomorph.toMeasurableEquiv).quasiMeasurePreserving.ae (complexLpToPhysical_coe f)]
    with z hz hw
  simpa only [hz, hw, ContinuousLinearEquiv.apply_symm_apply]

lemma physicalLpToComplex_beurling (f : ComplexPlaneL2) :
    physicalLpToComplex (physicalBeurling f) = beurling (physicalLpToComplex f) :=
  physicalLpToComplex_complexLpToPhysical _

lemma physicalBeurling_complex_coe (f : ComplexPlaneL2) :
    beurling (physicalLpToComplex f) =ᵐ[volume]
      fun z => physicalBeurling f (complexPlaneCoordinates.symm z) := by
  rw [← physicalLpToComplex_beurling]
  exact physicalLpToComplex_coe _

lemma exists_actual_conductivity_density (q : EuclideanPlane → ℝ)
    (hq : MemLp q 2 volume) (k : ℝ≥0) (hk : k < 1)
    (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) :
    ∃ g : ComplexPlaneL2,
      (∀ᵐ x ∂volume, g x = (q x : ℂ) * star (1 + physicalBeurling g x)) ∧
      ‖g‖ ≤ ‖conductivitySource q hq‖ / (1 - (k : ℝ)) :=
  exists_conductivity_density q hq k hk hb physicalBeurling
    (fun f => (physicalBeurling_norm f).le)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexLocalSobolevTransport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Package actual complex weak directional fields as the physical local
Sobolev witness required by the principal-map construction. -/
open MeasureTheory Set Filter Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma planarDz_of_complex_directions (a b : ℂ) :
    planarDz a.re b.re a.im b.im = (a - Complex.I * b) / 2 := by
  apply Complex.ext <;> simp [planarDz]

lemma planarDbar_of_complex_directions (a b : ℂ) :
    planarDbar a.re b.re a.im b.im = (a + Complex.I * b) / 2 := by
  apply Complex.ext <;> simp [planarDbar, add_comm, sub_eq_add_neg]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalWeakDirections
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The strong principal density limit supplies the actual directional weak
derivatives of the locally uniform homeomorphism limit. -/
open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma principalDirectionalCorrection_ae (g : PlaneL2) (v : ℂ) :
    principalDirectionalCorrection g v =ᵐ[volume]
      fun z => v*beurling g z + star v*g z := by
  filter_upwards [Lp.coeFn_add (v • beurling g) (star v • g),
    Lp.coeFn_smul v (beurling g), Lp.coeFn_smul (star v) g] with z h1 h2 h3
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3
  exact h1.trans (congrArg₂ (· + ·) h2 h3)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PrincipalPhysicalWitness
attribute [-instance] _root_.ContinuousMap.measurableSpace
attribute [-simp] _root_.OAI.CircleDomainRigidity.CompactScalarModel.postcompose_coefficient _root_.OAI.CircleDomainRigidity.horizontalLinear_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_apply _root_.OAI.CircleDomainRigidity.physicalHomeomorph_symm _root_.OAI.CircleDomainRigidity.sphereFromPlaneFunction_coe _root_.OAI.CircleDomainRigidity.verticalLinear_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the actual principal weak directional fields to the exact
physical Sobolev witness, retaining the real conjugate Beltrami equation. -/
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma principalPhysicalWitness_equation (H : ℂ ≃ₜ ℂ) (g : PlaneL2)
    (hw : ∀ (v : ℂ) (φ : SchwartzMap ℂ ℂ), HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, H z*fderiv ℝ (φ : ℂ → ℂ) z v) =
        -(∫ z, (v+principalDirectionalCorrection g v z)*φ z))
    (q : EuclideanPlane → ℝ)
    (hq : ∀ᵐ z ∂volume, g z=(q (complexPlaneCoordinates.symm z) : ℂ)*
      star (1+beurling g z)) :
    let D := principalPhysicalWitness H g hw
    ∀ᵐ x ∂volume,
      planarDbar (D.realGradient x 0) (D.realGradient x 1)
        (D.imagGradient x 0) (D.imagGradient x 1) =
      q x • star (planarDz (D.realGradient x 0) (D.realGradient x 1)
        (D.imagGradient x 0) (D.imagGradient x 1)) := by
  have hmp := complexPlaneCoordinates_measurePreserving.quasiMeasurePreserving
  filter_upwards [hmp.ae hq, hmp.ae (principalDirectionalCorrection_ae g 1),
    hmp.ae (principalDirectionalCorrection_ae g Complex.I)] with x hqx h0 h1
  change planarDbar (principalWeakDirections g 0 (complexPlaneCoordinates x)).re
    (principalWeakDirections g 1 (complexPlaneCoordinates x)).re
    (principalWeakDirections g 0 (complexPlaneCoordinates x)).im
    (principalWeakDirections g 1 (complexPlaneCoordinates x)).im =
      q x • star (planarDz (principalWeakDirections g 0 (complexPlaneCoordinates x)).re
        (principalWeakDirections g 1 (complexPlaneCoordinates x)).re
        (principalWeakDirections g 0 (complexPlaneCoordinates x)).im
        (principalWeakDirections g 1 (complexPlaneCoordinates x)).im)
  rw [planarDbar_of_complex_directions, planarDz_of_complex_directions]
  simp only [principalWeakDirections, complexPlaneCoordinates_zero,
    complexPlaneCoordinates_one, h0, h1, star_one, Complex.star_def, Complex.conj_I,
    one_mul, neg_mul] at hqx ⊢
  have hb : (1+(beurling g (complexPlaneCoordinates x)+g (complexPlaneCoordinates x))+
      Complex.I*(Complex.I+(Complex.I*beurling g (complexPlaneCoordinates x)-
        Complex.I*g (complexPlaneCoordinates x))))/2 = g (complexPlaneCoordinates x) := by
    ring_nf
    simp [Complex.I_sq]
    ring
  have hz : (1+(beurling g (complexPlaneCoordinates x)+g (complexPlaneCoordinates x))-
      Complex.I*(Complex.I+(Complex.I*beurling g (complexPlaneCoordinates x)-
        Complex.I*g (complexPlaneCoordinates x))))/2 = 1+beurling g (complexPlaneCoordinates x) := by
    ring_nf
    simp [Complex.I_sq]
    ring
  simp only [sub_eq_add_neg] at hb hz ⊢
  rw [hb, hz]
  simpa only [ContinuousLinearEquiv.symm_apply_apply, Complex.real_smul] using hqx

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_RealBeltramiCoefficientReduction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the actual conjugate Beltrami equation to a bounded standard
coefficient after constructing its L2 solution. No nonvanishing assumption
on the complex derivative is needed for this algebraic reduction. -/
open MeasureTheory Filter Set
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma realBeltramiStandardCoefficient_norm_le (q : ℝ) (a : ℂ) :
    ‖realBeltramiStandardCoefficient q a‖ ≤ ‖q‖ := by
  by_cases ha : a = 0
  · simp [realBeltramiStandardCoefficient, ha]
  · simp [realBeltramiStandardCoefficient, norm_ne_zero_iff.mpr ha]

lemma realBeltramiStandardCoefficient_mul (q : ℝ) (a : ℂ) :
    realBeltramiStandardCoefficient q a * a = (q : ℂ) * star a := by
  by_cases ha : a = 0
  · simp [realBeltramiStandardCoefficient, ha]
  · exact div_mul_cancel₀ _ ha

lemma realBeltramiStandardCoefficient_aeStronglyMeasurable
    (q : EuclideanPlane → ℝ) (a : EuclideanPlane → ℂ)
    (hq : AEStronglyMeasurable q volume) (ha : AEStronglyMeasurable a volume) :
    AEStronglyMeasurable (fun z => realBeltramiStandardCoefficient (q z) (a z)) volume := by
  exact ((Complex.continuous_ofReal.comp_aestronglyMeasurable hq).mul ha.star).div₀ ha

lemma realBeltramiStandardCoefficient_zero (a : ℂ) :
    realBeltramiStandardCoefficient 0 a = 0 := by
  simp [realBeltramiStandardCoefficient]

lemma exists_compact_coefficient_representative (μ : EuclideanPlane → ℂ)
    (hm : AEStronglyMeasurable μ volume) {K : Set EuclideanPlane}
    (hK : IsCompact K) (hzero : ∀ x ∉ K, μ x = 0)
    (k : ℝ≥0) (hb : ∀ᵐ x ∂volume, ‖μ x‖ ≤ k) :
    ∃ ν : EuclideanPlane → ℂ, Measurable ν ∧ (∀ x, ‖ν x‖ ≤ k) ∧
      (∀ x ∉ K, ν x = 0) ∧ μ =ᵐ[volume] ν := by
  classical
  let ν : EuclideanPlane → ℂ := fun x =>
    if x ∈ K ∧ ‖hm.mk μ x‖ ≤ k then hm.mk μ x else 0
  have hm' : Measurable (hm.mk μ) := hm.measurable_mk
  refine ⟨ν, Measurable.ite (hK.measurableSet.inter (measurableSet_le hm'.norm measurable_const))
    hm' measurable_const, ?_, ?_, ?_⟩
  · intro x
    dsimp only [ν]
    split_ifs with hx
    · exact hx.2
    · exact_mod_cast k.2
  · intro x hx
    exact ite_eq_right (fun h => hx h.1)
  · filter_upwards [hm.ae_eq_mk, hb] with x hx hb'
    by_cases hxK : x ∈ K
    · dsimp only [ν]
      rw [← hx, ite_eq_left ⟨hxK, hb'⟩]
    · dsimp only [ν]
      rw [ite_eq_right (fun h => hxK h.1)]
      exact hzero x hxK

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_RealBeltramiL2Reduction
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable standard coefficient built from the actual conductivity
L2 density. The zero-derivative set requires no division hypothesis. -/
open MeasureTheory Filter Set
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_real_beltrami_l2_reduction (q : EuclideanPlane → ℝ)
    (hq : MemLp q 2 volume) (k : ℝ≥0) (hk : k < 1)
    (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) :
    ∃ (h : ComplexPlaneL2) (μ : EuclideanPlane → ℂ),
      AEStronglyMeasurable μ volume ∧
      (∀ᵐ x ∂volume, ‖μ x‖ ≤ k) ∧
      (∀ x, q x = 0 → μ x = 0) ∧
      (∀ᵐ x ∂volume, h x = (q x : ℂ) * star (1 + physicalBeurling h x)) ∧
      (∀ᵐ x ∂volume, h x = μ x * (1 + physicalBeurling h x)) ∧
      ‖h‖ ≤ ‖conductivitySource q hq‖ / (1 - (k : ℝ)) := by
  obtain ⟨h, heq, hn⟩ := exists_actual_conductivity_density q hq k hk hb
  let μ : EuclideanPlane → ℂ := fun x =>
    realBeltramiStandardCoefficient (q x) (1 + physicalBeurling h x)
  refine ⟨h, μ, realBeltramiStandardCoefficient_aeStronglyMeasurable q _
    hq.aestronglyMeasurable
    (aestronglyMeasurable_const.add (Lp.aestronglyMeasurable _)), ?_, ?_, heq, ?_, hn⟩
  · filter_upwards [hb] with x hx
    exact (realBeltramiStandardCoefficient_norm_le _ _).trans hx
  · intro x hx
    simp only [μ, hx, realBeltramiStandardCoefficient_zero]
  · filter_upwards [heq] with x hx
    exact hx.trans (realBeltramiStandardCoefficient_mul _ _).symm

lemma real_beltrami_memLp_of_compact_support (q : EuclideanPlane → ℝ)
    (hq : AEStronglyMeasurable q volume) {K : Set EuclideanPlane}
    (hK : IsCompact K) (hzero : ∀ x ∉ K, q x = 0)
    (k : ℝ≥0) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) : MemLp q 2 volume := by
  have hm : MemLp (K.indicator (fun _ : EuclideanPlane => (k : ℝ))) 2 volume :=
    memLp_indicator_const 2 hK.measurableSet _ (Or.inr hK.measure_lt_top.ne)
  apply hm.of_le hq
  filter_upwards [hb] with x hx
  by_cases hxK : x ∈ K
  · simpa only [indicator_of_mem hxK, Real.norm_eq_abs] using
      hx.trans (le_abs_self (k : ℝ))
  · simp only [hzero x hxK, norm_zero, indicator_of_notMem hxK, le_refl]

lemma exists_compact_real_beltrami_l2_reduction (q : EuclideanPlane → ℝ)
    (hq : AEStronglyMeasurable q volume) {K : Set EuclideanPlane}
    (hK : IsCompact K) (hzero : ∀ x ∉ K, q x = 0)
    (k : ℝ≥0) (hk : k < 1) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) :
    ∃ (h : ComplexPlaneL2) (μ : EuclideanPlane → ℂ),
      AEStronglyMeasurable μ volume ∧ (∀ᵐ x ∂volume, ‖μ x‖ ≤ k) ∧
      (∀ x ∉ K, μ x = 0) ∧
      (∀ᵐ x ∂volume, h x = (q x : ℂ) * star (1 + physicalBeurling h x)) ∧
      (∀ᵐ x ∂volume, h x = μ x * (1 + physicalBeurling h x)) := by
  obtain ⟨h, μ, hm, hbμ, hzμ, hqeq, hμeq, _⟩ := exists_real_beltrami_l2_reduction q
    (real_beltrami_memLp_of_compact_support q hq hK hzero k hb) k hk hb
  exact ⟨h, μ, hm, hbμ, fun x hx => hzμ x (hzero x hx), hqeq, hμeq⟩

lemma exists_bounded_compact_real_beltrami_l2_reduction (q : EuclideanPlane → ℝ)
    (hq : AEStronglyMeasurable q volume) {K : Set EuclideanPlane}
    (hK : IsCompact K) (hzero : ∀ x ∉ K, q x = 0)
    (k : ℝ≥0) (hk : k < 1) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) :
    ∃ (h : ComplexPlaneL2) (μ : EuclideanPlane → ℂ), Measurable μ ∧
      (∀ x, ‖μ x‖ ≤ k) ∧ (∀ x ∉ K, μ x = 0) ∧
      (∀ᵐ x ∂volume, h x = (q x : ℂ) * star (1 + physicalBeurling h x)) ∧
      (∀ᵐ x ∂volume, h x = μ x * (1 + physicalBeurling h x)) := by
  obtain ⟨h, μ, hm, hbm, hzm, hqeq, hmeq⟩ :=
    exists_compact_real_beltrami_l2_reduction q hq hK hzero k hk hb
  obtain ⟨ν, hνm, hνb, hνz, heq⟩ :=
    exists_compact_coefficient_representative μ hm hK hzm k hbm
  refine ⟨h, ν, hνm, hνb, hνz, hqeq, ?_⟩
  filter_upwards [hmeq, heq] with x hx he
  rwa [he] at hx

lemma exists_complex_real_beltrami_l2_reduction (q : EuclideanPlane → ℝ)
    (hq : AEStronglyMeasurable q volume) {K : Set EuclideanPlane}
    (hK : IsCompact K) (hzero : ∀ x ∉ K, q x = 0)
    (k : ℝ≥0) (hk : k < 1) (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) :
    ∃ (g : CannonBeltrami.PlaneL2) (μ : ℂ → ℂ), Measurable μ ∧
      (∀ z, ‖μ z‖ ≤ k) ∧
      (∀ z ∉ complexPlaneCoordinates '' K, μ z = 0) ∧
      (∀ᵐ z ∂volume,
        g z = (q (complexPlaneCoordinates.symm z) : ℂ) *
          star (1+CannonBeltrami.beurling g z)) ∧
      (∀ᵐ z ∂volume, g z = μ z*(1+CannonBeltrami.beurling g z)) := by
  obtain ⟨h, ν, hνm, hνb, hνz, hqe, hνe⟩ :=
    exists_bounded_compact_real_beltrami_l2_reduction q hq hK hzero k hk hb
  let g := physicalLpToComplex h
  let μ : ℂ → ℂ := ν ∘ complexPlaneCoordinates.symm
  have hmp := complexPlaneCoordinates_measurePreserving.symm
    complexPlaneCoordinates.toHomeomorph.toMeasurableEquiv
  refine ⟨g, μ, hνm.comp complexPlaneCoordinates.symm.continuous.measurable,
    fun z => hνb _, ?_, ?_, ?_⟩
  · intro z hz
    exact hνz _ (fun h => hz ⟨_, h, complexPlaneCoordinates.apply_symm_apply z⟩)
  · filter_upwards [hmp.quasiMeasurePreserving.ae hqe, physicalLpToComplex_coe h,
      physicalBeurling_complex_coe h] with z hqz hgz hBz
    change physicalLpToComplex h z = _
    rw [hgz, hBz]
    exact hqz
  · filter_upwards [hmp.quasiMeasurePreserving.ae hνe, physicalLpToComplex_coe h,
      physicalBeurling_complex_coe h] with z hνz hgz hBz
    change physicalLpToComplex h z = _
    rw [hgz, hBz]
    exact hνz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PrincipalSmoothLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the principal plane homeomorphism with the specified strong
L2 density. Retain the actual smooth approximants and both convergences
for the subsequent scalar transport application. -/
open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami CannonPlane

namespace PrincipalSmoothApproximation
variable {g : PlaneL2} {k R : ℝ} (S : PrincipalSmoothApproximation g k R)

include S in
lemma exists_principal_homeomorph_limit (harea : ExteriorCoefficientAreaTheorem)
    (hk : 0 ≤ k) (hk1 : k < 1) {T : ℝ} (hT : 0 < T) (hRT : R+2 ≤ T) :
    ∃ H : ℂ ≃ₜ ℂ,
      Tendsto (fun z => H z-z) (Bornology.cobounded ℂ) (𝓝 0) ∧
      ∀ (v : ℂ) (φ : SchwartzMap ℂ ℂ), HasCompactSupport (φ : ℂ → ℂ) →
        (∫ z, H z*fderiv ℝ (φ : ℂ → ℂ) z v) =
          -(∫ z, (v+principalDirectionalCorrection g v z)*φ z) := by
  obtain ⟨L⟩ := S.exists_principal_limit_data harea hk hk1 hT hRT
  exact ⟨L.map, L.principal, L.weak⟩

end PrincipalSmoothApproximation
end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Rigidity_PrincipalRealBeltramiProof
attribute [-instance] _root_.ContinuousMap.measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact compactly supported real-coefficient principal Beltrami input,
constructed from the L2 conductivity contraction and smooth principal maps.
No generalized Beltrami existence theorem is assumed. -/
open MeasureTheory Set Filter
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma principalRealBeltrami_oai : PrincipalRealBeltrami := by
  intro q hq hcompact k hk hb
  obtain ⟨K, hK, hKzero⟩ := hcompact
  obtain ⟨g, μ, hm, hbound, hzero, hreal, he⟩ :=
    exists_complex_real_beltrami_l2_reduction q hq hK hKzero k hk hb
  obtain ⟨R, hR⟩ := (hK.image complexPlaneCoordinates.continuous).isBounded.subset_ball 0
  have hs : ∀ z, R ≤ ‖z‖ → μ z=0 := by
    intro z hz
    apply hzero
    intro hmem
    have hh := hR hmem
    simp only [Metric.mem_ball, dist_zero_right] at hh
    linarith
  have hk0 : 0 ≤ (k : ℝ) := k.2
  have hk1 : (k : ℝ) < 1 := by exact_mod_cast hk
  obtain ⟨S⟩ := exists_principal_smooth_approximation μ hm.aestronglyMeasurable
    hk0 hk1 hbound hs g he
  let T := max (R+2) 1
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨H, hprincipal, hw⟩ := S.exists_principal_homeomorph_limit
    (exteriorCoefficientAreaTheorem planarSchoenflies unorientedFiniteCircleGreenFormula)
    hk0 hk1 hT (le_max_left _ _)
  exact ⟨H, principalPhysicalWitness H g hw, hprincipal,
    principalPhysicalWitness_equation H g hw q hreal⟩

end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.principalRealBeltrami_oai := @OAI.CircleDomainRigidity.principalRealBeltrami_oai
