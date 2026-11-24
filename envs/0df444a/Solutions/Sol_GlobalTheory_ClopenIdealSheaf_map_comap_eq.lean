-- Prove2me | solution 1 for GlobalTheory.ClopenIdealSheaf.map_comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:08.97296+00:00
-- url     : https://prove2.me/submissions/cc81ed81-b943-42d0-8141-261554b995e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSheafDataOfIsClopenFamily
import Theorems.Thm_GlobalTheory_ClopenIdealSheaf_map_comap_localization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.ClopenIdealSheaf
namespace GlobalTheory.ClopenIdealSheaf
theorem _root_.solution {Z : Scheme.{0}} (F : ∀ U : Z.affineOpens, Ideal Γ(Z, U))
    {U V B : Z.affineOpens} (hVU : (V : Z.Opens) ≤ U) (f : Γ(Z, U))
    (hB : Z.affineBasicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f) = B)
    (hBD : (B : Z.Opens) ≤ Z.basicOpen f)
    (hI : (F V).map (Z.presheaf.map (homOfLE (Z.basicOpen_le
        ((Z.presheaf.map (homOfLE hVU).op).hom f))).op).hom =
      F (Z.affineBasicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f))) :
    ((F V).comap (Z.presheaf.map (homOfLE hVU).op).hom).map
        (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom =
      (F B).comap (Z.presheaf.map (homOfLE hBD).op).hom := by
  subst hB
  rw [← hI]
  haveI := U.2.isLocalization_basicOpen f
  haveI := V.2.isLocalization_basicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f)
  refine map_comap_localization (S := Γ(Z, Z.basicOpen f)) f _
    (T := Γ(Z, Z.basicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f))) _ ?_ _
  intro a
  change (Z.presheaf.map (homOfLE hBD).op).hom
      ((Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom a) =
    (Z.presheaf.map (homOfLE (Z.basicOpen_le _)).op).hom
      ((Z.presheaf.map (homOfLE hVU).op).hom a)
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  rfl
end GlobalTheory.ClopenIdealSheaf
