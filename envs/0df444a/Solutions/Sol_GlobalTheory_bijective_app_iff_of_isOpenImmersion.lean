-- Prove2me | solution 1 for GlobalTheory.bijective_app_iff_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:55:23.067794+00:00
-- url     : https://prove2.me/submissions/02c05ba4-c92f-4846-9f9f-630d25d62f00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {X Y : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution (f : Y ⟶ X) [IsOpenImmersion f] (V : X.Opens) :
    Function.Bijective (f.app V).hom ↔
      Function.Bijective (X.presheaf.map
        (homOfLE (inf_le_left : V ⊓ f.opensRange ≤ V)).op).hom := by
  have := f.isIso_app (V ⊓ f.opensRange) inf_le_right
  have hb : Function.Bijective (f.app (V ⊓ f.opensRange)).hom :=
    ConcreteCategory.bijective_of_isIso _
  have he : f ⁻¹ᵁ (V ⊓ f.opensRange) = f ⁻¹ᵁ V :=
    le_antisymm (fun _ h ↦ h.1) fun y h ↦ ⟨h, y, rfl⟩
  have hb' : Function.Bijective (Y.presheaf.map (eqToHom he).op).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [← hb.of_comp_iff', ← hb'.of_comp_iff', ← RingHom.coe_comp, ← RingHom.coe_comp,
    ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, f.naturality]
  rfl
end GlobalTheory
