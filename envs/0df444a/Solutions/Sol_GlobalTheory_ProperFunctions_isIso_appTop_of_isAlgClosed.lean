-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.isIso_appTop_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:38:48.255532+00:00
-- url     : https://prove2.me/submissions/1d1b3ea6-9ee2-4bbe-8b1a-5d1a34ffd957

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X S : Scheme.{u}}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution {k : Type u} [Field k] [IsAlgClosed k]
    (p : X ⟶ Spec (.of k)) [IsIntegral X] [UniversallyClosed p] : IsIso p.appTop := by
  let F := (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed p
  have : IsIso F := by
    algebraize [F.hom]
    exact (ConcreteCategory.isIso_iff_bijective F).mpr
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤)))
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv p.appTop
end GlobalTheory.ProperFunctions
