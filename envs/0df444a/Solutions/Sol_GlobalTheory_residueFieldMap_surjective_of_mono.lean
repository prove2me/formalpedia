-- Prove2me | solution 1 for GlobalTheory.residueFieldMap_surjective_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:44:28.548995+00:00
-- url     : https://prove2.me/submissions/ecd4c434-1df1-4eed-a407-69d0aff08d5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueFieldMapSurjectiveOfMono
import Theorems.Thm_GlobalTheory_surjective_of_epi_of_field_to_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y : Scheme.{0}} (f : X ⟶ Y) [Mono f] (x : X) :
    Function.Surjective (f.residueFieldMap x).hom := by
  have h1 : Mono (Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField (f x)) := by
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    infer_instance
  have h2 : Mono (Spec.map (f.residueFieldMap x)) := mono_of_mono _ (Y.fromSpecResidueField (f x))
  have h3 : Mono (f.residueFieldMap x).op :=
    Scheme.Spec.mono_of_mono_map (f := (f.residueFieldMap x).op) h2
  have h4 : Epi (f.residueFieldMap x) := (CategoryTheory.op_mono_iff _).1 h3
  exact surjective_of_epi_of_field_to_field (K := Y.residueField (f x)) (L := X.residueField x) (f.residueFieldMap x)
end GlobalTheory
