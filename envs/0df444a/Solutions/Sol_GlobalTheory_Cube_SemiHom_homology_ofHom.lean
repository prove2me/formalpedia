-- Prove2me | solution 1 for GlobalTheory.Cube.SemiHom.homology_ofHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:40:31.548499+00:00
-- url     : https://prove2.me/submissions/87837e87-2f7b-49b5-a984-40491a1bc362

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Theorems.Thm_GlobalTheory_homologyMap_cechClass
import Theorems.Thm_GlobalTheory_Cube_SemiHom_homology_cechClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Cube.SemiHom.homology_cechClass

set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
noncomputable section
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
open GlobalTheory.Cube GlobalTheory.Cube.SemiHom
variable {f : R →+* S} {A A' : Cube.{v} ι R} {B B' : Cube.{v'} ι S} (ψ : Cube.SemiHom f A B)
namespace GlobalTheory.Cube.SemiHom
theorem _root_.solution (φ : A ⟶ A') (p : ℕ) :
    (ofHom φ).homology p = (HomologicalComplex.homologyMap (cechComplexMap φ) p).hom := by
  ext x
  obtain ⟨x, rfl⟩ := cechClass_surjective A p x
  rw [homology_cechClass]
  exact (homologyMap_cechClass φ p x _ rfl).symm
end GlobalTheory.Cube.SemiHom
