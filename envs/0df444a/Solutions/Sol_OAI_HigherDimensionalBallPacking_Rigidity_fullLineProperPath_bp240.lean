-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.fullLineProperPath_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T02:20:53.545993+00:00
-- url     : https://prove2.me/submissions/30638610-8cb5-4882-ace1-db2c9482af61

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp020
import Definitions.Def_OAIQ240Bp021
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_fullLineEquation_contDiff_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_fullLineEquation_initial_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_fullLineEquation_spatial_fredholm_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_HolderCompletion_isolatedFullLineZeros_compact_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_Adapted
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothAlongJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.capacity_eq_stdDot _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.stdDot_J_right _root_.OAI.HigherDimensionalBallPacking.Rigidity.stdOmega_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
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

theorem pseudoHolomorphicAt_standard_of_complex {n : ℕ} {u : ℂ → Phase n} {z : ℂ}
    (hu : DifferentiableAt ℂ u z) :
    PseudoHolomorphicAt (fun _ => standardJ n) u z := by
  refine ⟨hu.restrictScalars ℝ,?_⟩
  intro w
  rw [(hu.hasFDerivAt.restrictScalars ℝ).fderiv]
  change fderiv ℂ u z (Complex.I • w) = Complex.I • fderiv ℂ u z w
  exact map_smul (fderiv ℂ u z) Complex.I w

theorem standard_affine_line {n : ℕ} (p q : Phase n) (hpq : p ≠ q) :
    AffineLineCurve (fun _ => standardJ n) p q (fun z : ℂ => p + z • (q-p)) := by
  have hs : ContDiff ℂ ∞ (fun z : ℂ => p + z • (q-p)) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  refine ⟨hs.restrict_scalars ℝ,fun z =>
    pseudoHolomorphicAt_standard_of_complex (hs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z),by simp,by simp,?_,?_⟩
  · exact q-p
  · refine ⟨sub_ne_zero.mpr hpq.symm,?_⟩
    have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
      simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
    have ht : Tendsto (fun z : ℂ => z⁻¹ • p + (q-p)) (cocompact ℂ) (𝓝 (q-p)) := by
      simpa only [zero_smul, zero_add] using (hi.smul_const p).add_const (q-p)
    apply ht.congr'
    filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
    have hz0 : z ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hz
    simp only [smul_add, smul_smul, inv_mul_cancel₀ hz0, one_smul]


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Holder_MarkedJets
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {K : Set ℂ} (hK : IsCompact K)

local instance markedAffineInst1_r579cd7_1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance markedAffineInst2_r579cd7_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance markedAffineInst3_r579cd7_1 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance markedAffineInst4_r579cd7_1 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance markedAffineInst5_r579cd7_1 : NormedAddCommGroup (markedModel (E := E) K) := inferInstance
local instance markedAffineInst6_r579cd7_1 : NormedSpace ℝ (markedModel (E := E) K) := inferInstance
local instance markedAffineInst7_r579cd7_1 : NormedAddCommGroup (supportedHolder (E := E) K) := inferInstance
local instance markedAffineInst8_r579cd7_1 : NormedSpace ℝ (supportedHolder (E := E) K) := inferInstance
omit [CompleteSpace E] in
lemma markedSlope_continuous (p q : E) : Continuous (markedSlope p q : COne ℂ E → E) :=
  continuous_const.sub (jetEval (E := E) 1).continuous



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Continuation_CompatibleHomotopy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.cmn1
local instance cmn2_r579cd7_1 : NormedSpace ℝ (COne ℂ E) := inferInstance
omit [CompleteSpace E] in
lemma markedBoundedDomain_open [CompleteSpace E] (p q : E) (M δ : ℝ) : IsOpen (markedBoundedDomain p q M δ) :=
  (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const (markedSlope_continuous p q).norm)

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Continuation_ParameterizedImplicit
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology
open Filter
open scoped BoundedContinuousFunction
open Set Function

variable {n : ℕ}
variable (b : ContDiffBump (0:ℂ))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gid1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gid2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gid3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gid4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gid5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.gid6
lemma fullLineDomain_open (p q : Phase n) (M δ : ℝ) : IsOpen (fullLineDomain b p q M δ) :=
  (markedBoundedDomain_open p q M δ).preimage continuous_subtype_val

variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n))
  (b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)
  (hb₁ : Metric.closedBall (0:ℂ) b.rOut⊆Metric.closedBall (0:ℂ) b₁.rIn)
  {B M δ : ℝ} (hstd : ∀ x,B<‖x‖ →J x=standardJ n) (hδ : 0<δ)
  (he : ∀ w∈markedBoundedDomain p q M δ,MarkedEscapeNeighborhood b p q w B)
  (hbound : ∀ v∈exactMarkedZeroSet J p q,v.2∈markedBoundedDomain p q M δ)

include hb₁ hstd he in
lemma fullLineEquation_fredholm_on_domain {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (w : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
    (hw : w∈fullLineDomain b p q M δ) : IsIndexZeroFredholm
      (fderiv ℝ (fun v => fullLineEquation hJs hJ hJc b b₁ p q (t,v)) w) :=
  fullLineEquation_spatial_fredholm_bp240 hJs hJ hJc b b₁ p q hb₁ hstd ht w (he w.val hw)

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
section

variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcdEnd2
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcd1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcd2
lemma markedCurve_zero_correction (p q : Phase n) :
    markedCurve p q (0:COne ℂ (Phase n))=(fun z : ℂ => p+z • (q-p)) := by
  funext z
  have hz (z : ℂ) : cValue (0:COne ℂ (Phase n)) z=0 := rfl
  simp only [markedCurve,markedSlope,hz,sub_zero,add_zero]

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcdEnd1
lemma exact_marked_initial {J : Phase n → End n} (hJ : ∀ x,Compatible (J x))
    {p q : Phase n} (hpq : p≠q) : (0,0)∈exactMarkedZeroSet J p q := by
  refine ⟨by constructor <;> norm_num,?_,?_⟩
  · change cValue (0:COne ℂ (Phase n)) 0=0
    rfl
  · rw [markedCurve_zero_correction]
    have he : lineHomotopy J 0=(fun _ => standardJ n) := funext (lineHomotopy_zero hJ)
    rw [he]
    exact standard_affine_line p q hpq

variable (b : ContDiffBump (0:ℂ))

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcd3
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcd4
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcd5
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.lcd6
local instance lcd7_r579cd7_1 : AddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (lcd3 (n := n) b).toAddCommGroup
local instance lcd8_r579cd7_1 : Module ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (lcd4 (n := n) b).toModule
local instance lcd9_r579cd7_1 : AddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (lcd5 (n := n) b).toAddCommGroup
local instance lcd10_r579cd7_1 : Module ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (lcd6 (n := n) b).toModule
local instance lcd11_r579cd7_1 : NormedAddCommGroup (ℝ × markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance lcd12_r579cd7_1 : NormedSpace ℝ (ℝ × markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n)) (b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)
  (hb₁ : Metric.closedBall (0:ℂ) b.rOut⊆Metric.closedBall (0:ℂ) b₁.rIn)
  {B M δ : ℝ} (hstd : ∀ x,B<‖x‖ →J x=standardJ n) (hδ : 0<δ)
  (he : ∀ w∈markedBoundedDomain p q M δ,MarkedEscapeNeighborhood b p q w B)

include hb₁ hstd hδ he in
lemma fullLineProperPath_bp240_oai
    (hbound : ∀ v∈exactMarkedZeroSet J p q,v.2∈markedBoundedDomain p q M δ)
    (hc : IsCompact (fullMarkedZeroSet J p q)) (hpq : p≠q) :
    ProperIndexZeroPath (fullLineEquation hJs hJ hJc b b₁ p q) (fullLineDomain b p q M δ) := by
  have h0 : (0:markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))∈fullLineDomain b p q M δ :=
    hbound (0,0) (exact_marked_initial hJ hpq)
  refine ⟨fullLineDomain_open b p q M δ,h0,
    fullLineEquation_contDiff_bp240 hJs hJ hJc b b₁ p q,?_,?_,?_⟩
  · exact ⟨markedCREquiv (E := Phase n) (isCompact_closedBall (0:ℂ) b.rOut),
      fullLineEquation_initial_bp240 hJs hJ hJc b b₁ p q⟩
  · exact isolatedFullLineZeros_compact_bp240 b hJs hJ hJc b₁ p q hb₁ hstd hδ he hbound hc
  · intro t ht w hw
    exact fullLineEquation_fredholm_on_domain b hJs hJ hJc b₁ p q hb₁ hstd he ht w hw

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.fullLineProperPath_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.fullLineProperPath_bp240_oai
