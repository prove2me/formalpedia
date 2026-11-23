-- Prove2me | solution 1 for GlobalTheory.SmGL.hasFiniteLength_comp_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:10.567288+00:00
-- url     : https://prove2.me/submissions/360500ff-b080-4ac9-a87b-f803297fc167

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open GlobalTheory
open GlobalTheory.SmGL
variable {F G H V : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
namespace GlobalTheory.SmGL
theorem _root_.solution (ρ : Representation F G V) (s : H →* G) (hs : Function.Surjective s) :
    HasFiniteLength (ρ.comp s : Representation F H V) ↔ HasFiniteLength ρ := by
  let φ : Subrepresentation (ρ.comp s : Representation F H V) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        obtain ⟨h, rfl⟩ := hs g
        exact S.apply_mem_toSubmodule h hv⟩
      invFun := fun S => ⟨S.toSubmodule, fun h v hv => S.apply_mem_toSubmodule (s h) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  rw [hasFiniteLength_iff_wellFounded, hasFiniteLength_iff_wellFounded]
  exact and_congr ⟨fun _ => φ.symm.toOrderEmbedding.wellFoundedGT,
    fun _ => φ.toOrderEmbedding.wellFoundedGT⟩ ⟨fun _ => φ.symm.toOrderEmbedding.wellFoundedLT,
    fun _ => φ.toOrderEmbedding.wellFoundedLT⟩
end GlobalTheory.SmGL
