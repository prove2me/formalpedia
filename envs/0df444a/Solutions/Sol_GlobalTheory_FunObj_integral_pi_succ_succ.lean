-- Prove2me | solution 1 for GlobalTheory.FunObj.integral_pi_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:47:48.501015+00:00
-- url     : https://prove2.me/submissions/f7e6d330-6f3b-43b1-8fe6-725886a09bc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr
import Theorems.Thm_GlobalTheory_FunObj_consEquiv_apply
import Theorems.Thm_GlobalTheory_FunObj_measurePreserving_consEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.LocFlat
namespace GlobalTheory.FunObj
theorem _root_.solution {n : ℕ} {E : Fin (n + 2) → Type} [∀ j, MeasurableSpace (E j)] (μ : ∀ j, Measure (E j))
    [∀ j, SigmaFinite (μ j)] (F : (∀ j, E j) → ℂ) :
    ∫ w, F w ∂(Measure.pi μ) =
      ∫ p : (E 0 × E (Fin.succ 0)) × (∀ j : Fin n, E j.succ.succ), F (Fin.cons p.1.1 (Fin.cons p.1.2 p.2))
        ∂(((μ 0).prod (μ (Fin.succ 0))).prod (Measure.pi fun j => μ j.succ.succ)) := by
  have h : MeasurePreserving (MeasurableEquiv.prodAssoc.trans (((MeasurableEquiv.refl (E 0)).prodCongr
      (consEquiv fun j : Fin (n + 1) => E j.succ)).trans (consEquiv E)))
      (((μ 0).prod (μ (Fin.succ 0))).prod (Measure.pi fun j : Fin n => μ j.succ.succ)) (Measure.pi μ) :=
    (measurePreserving_consEquiv μ).comp (((MeasurePreserving.id (μ 0)).prod
      (measurePreserving_consEquiv fun j : Fin (n + 1) => μ j.succ)).comp (measurePreserving_prodAssoc _ _ _))
  rw [← h.integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show F (consEquiv E (p.1.1, consEquiv (fun j : Fin (n + 1) => E j.succ) (p.1.2, p.2))) = _
  simp only [consEquiv_apply]
end GlobalTheory.FunObj
