-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.isClopen_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:41:33.978783+00:00
-- url     : https://prove2.me/submissions/f1cc9635-6b95-4e97-a72a-72788563492e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TfLoc GlobalTheory.CompanionTheory.TfLoc.Iw
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {m : ℕ}
namespace GlobalTheory.CompanionTheory.TfLoc.Iw
theorem _root_.solution : IsClopen {x : F | valuation F x < 1} := by
  let H : AddSubgroup F :=
    { carrier := {x | valuation F x < 1}
      add_mem' := fun {a b} ha hb => (valuation F).map_add_lt ha hb
      zero_mem' := by simp
      neg_mem' := fun {x} hx => by simpa [Valuation.map_neg] using hx }
  have ho : IsOpen (H : Set F) := H.isOpen_of_mem_nhds (g := 0)
    ((IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.2 ⟨1, one_ne_zero, fun x hx => hx⟩)
  exact ⟨H.isClosed_of_isOpen ho, ho⟩
end GlobalTheory.CompanionTheory.TfLoc.Iw
