-- Prove2me | solution 1 for GlobalTheory.FiniteLengthComplex.nonempty_iso_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:04:24.029299+00:00
-- url     : https://prove2.me/submissions/64fc6175-261c-4f30-95f2-4ff52984965b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing
open GlobalTheory
open GlobalTheory.FiniteLengthComplex
variable {R : Type} [CommRing R]
namespace GlobalTheory.FiniteLengthComplex
theorem _root_.solution [IsLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] :
    Nonempty (ModuleCat.of R M ≅ ModuleCat.of R (R ⧸ maximalIdeal R)) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R M›
  obtain rfl := eq_maximalIdeal hI
  exact ⟨e.toModuleIso⟩
end GlobalTheory.FiniteLengthComplex
