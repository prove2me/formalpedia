-- Prove2me | solution 1 for GlobalTheory.SheafLES.toAbSheaf_map_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:02.894729+00:00
-- url     : https://prove2.me/submissions/86e07976-fb49-4b26-ac12-edf373fb2a56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe w' v u
open CategoryTheory Limits Abelian Opposite
noncomputable section
open GlobalTheory
open GlobalTheory.SheafLES
open AlgebraicGeometry
variable (X : Scheme.{u})
variable {X}
namespace GlobalTheory.SheafLES
theorem _root_.solution {M N : X.Modules} (φ : M ⟶ N) :
    ((toAbSheaf X).map φ).hom = φ.mapPresheaf := rfl
end GlobalTheory.SheafLES
