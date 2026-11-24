-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.isCompact_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:41:35.195605+00:00
-- url     : https://prove2.me/submissions/0e6b2478-455f-4976-8f73-41f7526371c8

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
theorem _root_.solution : IsCompact {M : Matrix (Fin m) (Fin m) F | ∀ i j, valuation F (M i j) ≤ 1} := by
  have h : IsCompact (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m =>
      {x : F | valuation F x ≤ 1}) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      IsNonarchimedeanLocalField.isCompact_closedBall F 1
  have e : {M : Matrix (Fin m) (Fin m) F | ∀ i j, valuation F (M i j) ≤ 1} =
      (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m =>
        {x : F | valuation F x ≤ 1}) := by
    ext M
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [e]
  exact h
end GlobalTheory.CompanionTheory.TfLoc.Iw
