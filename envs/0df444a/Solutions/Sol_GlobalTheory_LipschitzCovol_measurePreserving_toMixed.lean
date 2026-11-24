-- Prove2me | solution 1 for GlobalTheory.LipschitzCovol.measurePreserving_toMixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:45:06.534573+00:00
-- url     : https://prove2.me/submissions/d95e2c20-a300-41d5-9765-903459445202

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovolumeFractionalIdealRealLatticeImage
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply



set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzCovol
open NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory.LipschitzCovol
theorem _root_.solution :
    MeasurePreserving (toMixed (F := F)).toContinuousLinearEquiv volume volume := by
  have h1 := PiLp.volume_preserving_ofLp (F →+* ℝ)
  have h2 := volume_measurePreserving_piCongrLeft (fun _ : {w : InfinitePlace F // IsReal w} => ℝ)
    (embPlace (F := F))
  have h3 : MeasurePreserving (fun y : {w : InfinitePlace F // IsReal w} → ℝ =>
      (y, (0 : {w : InfinitePlace F // IsComplex w} → ℂ))) volume volume := by
    refine ⟨measurable_id.prodMk measurable_const, ?_⟩
    rw [Measure.volume_eq_prod, show (volume : Measure ({w : InfinitePlace F // IsComplex w} → ℂ)) =
      Measure.dirac 0 from Measure.volume_pi_eq_dirac 0, Measure.prod_dirac]
  have h := h3.comp (h2.comp h1)
  have he : ⇑(toMixed (F := F)).toContinuousLinearEquiv =
      (fun y : {w : InfinitePlace F // IsReal w} → ℝ =>
        (y, (0 : {w : InfinitePlace F // IsComplex w} → ℂ))) ∘
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : {w : InfinitePlace F // IsReal w} => ℝ)
        (embPlace (F := F))) ∘ WithLp.ofLp := by
    funext x
    refine Prod.ext (funext fun w => ?_) rfl
    simp [toMixed, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rw [he]
  exact h
end GlobalTheory.LipschitzCovol
