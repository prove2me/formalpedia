-- Prove2me | solution 1 for GlobalTheory.FlatFactor.UpStage.measurePreserving_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:07:18.219571+00:00
-- url     : https://prove2.me/submissions/99033c07-c486-4e54-af17-494761e7cc34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegrated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillingPartialEvalIntegralKernelTransla
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelIntegratesFreeEntries
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.FlatFactor GlobalTheory.FlatFactor.UpStage
namespace GlobalTheory.FlatFactor.UpStage
theorem _root_.solution {k ι : Type} [AddCommGroup k] [MeasurableSpace k] [MeasurableAdd₂ k] [Fintype ι]
    (ν : Measure k) [SigmaFinite ν] [ν.IsAddRightInvariant] (p : ι → Prop) [DecidablePred p]
    (v : (ι → k) → ι → k) (hv : Measurable v) (h0 : ∀ α i, p i → v α i = 0)
    (hd : ∀ α α', (∀ i, p i → α i = α' i) → v α = v α') :
    MeasurePreserving (fun α => α + v α) (Measure.pi fun _ : ι => ν) (Measure.pi fun _ : ι => ν) := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => k) p
  have he : MeasurePreserving e (Measure.pi fun _ : ι => ν)
      ((Measure.pi fun _ : {i // p i} => ν).prod (Measure.pi fun _ : {i // ¬p i} => ν)) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : ι => ν) p
  let w : ({i // p i} → k) → ({i // ¬p i} → k) := fun x j => v (e.symm (x, 0)) j.1
  have hw : Measurable w := by
    refine measurable_pi_lambda _ fun j => ?_
    exact (measurable_pi_apply j.1).comp (hv.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const)))
  have hF : MeasurePreserving (fun q : ({i // p i} → k) × ({i // ¬p i} → k) => (id q.1, q.2 + w q.1))
      ((Measure.pi fun _ : {i // p i} => ν).prod (Measure.pi fun _ : {i // ¬p i} => ν))
      ((Measure.pi fun _ : {i // p i} => ν).prod (Measure.pi fun _ : {i // ¬p i} => ν)) :=
    (MeasurePreserving.id _).skew_product (measurable_snd.add (hw.comp measurable_fst))
      (Filter.Eventually.of_forall fun x => map_add_right_eq_self _ _)
  have hc := (he.symm e).comp (hF.comp he)
  convert hc using 1
  funext α
  have hα : v (e.symm ((fun j : {i // p i} => α j.1), 0)) = v α := by
    apply hd
    intro i hi
    simp [e, MeasurableEquiv.piEquivPiSubtypeProd, hi]
  funext i
  by_cases hi : p i
  · simp [e, w, MeasurableEquiv.piEquivPiSubtypeProd, hi, h0 α i hi]
  · simp [e, w, MeasurableEquiv.piEquivPiSubtypeProd, hi]
    exact (congrFun hα i).symm
end GlobalTheory.FlatFactor.UpStage
