-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FormalClosed.isIso_of_isClosedImmersion_of_thickenings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:29:31.46285+00:00
-- url     : https://prove2.me/submissions/a00ac44d-a9f9-408d-954a-8249303c564d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_FormalAlgebraisation_GEClosedProj
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsIsoOfIsClosedImmersionOfThickenings
import Theorems.Thm_GlobalTheory_CompanionTheory_FormalClosed_mem_of_forall_mem_over_closedFibre
import Theorems.Thm_GlobalTheory_CompanionTheory_FormalClosed_eq_bot_of_forall_mem_zeroLocusOpen
import Theorems.Thm_GlobalTheory_ThickeningClosed_isOpen_zeroLocusOpen
import Theorems.Thm_GlobalTheory_ThickeningClosed_mem_of_thickenings


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FormalClosed
open GlobalTheory.ThickeningClosed
namespace GlobalTheory.CompanionTheory.FormalClosed
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom →
    ∀ (E : Scheme.{0}) (j : E ⟶ X.left), IsClosedImmersion j →
      (∀ e, ∃ h : (thickObj R I e X).left ⟶ E, h ≫ j = pullback.fst X.hom (thick R I e)) →
        IsIso j := by
  intro R _ _ I hI X hX E j hj hth
  haveI := hX
  haveI := hj
  haveI := hI
  haveI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  apply eq_bot_of_forall_mem_zeroLocusOpen
  intro x
  refine mem_of_forall_mem_over_closedFibre (IsAdicComplete.le_jacobson_bot I) X.hom
    (isOpen_zeroLocusOpen _) ?_ x
  intro y hy
  refine mem_of_thickenings I X.hom j ?_ y hy
  intro n
  obtain ⟨l, hl⟩ := hth n
  exact ⟨l, hl⟩
end GlobalTheory.CompanionTheory.FormalClosed
