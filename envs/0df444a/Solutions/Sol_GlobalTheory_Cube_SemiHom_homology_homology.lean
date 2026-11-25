-- Prove2me | solution 1 for GlobalTheory.Cube.SemiHom.homology_homology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:37:49.06811+00:00
-- url     : https://prove2.me/submissions/dfa36db4-9038-4a70-a746-d360590df391

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
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
theorem _root_.solution {Q : Type*} [Ring Q] {g : S →+* Q} {k : R →+* Q} {C : Cube ι Q}
    (χ : Cube.SemiHom g B C) (ω : Cube.SemiHom k A C)
    (h : ∀ s, s.Nonempty → ∀ x, χ.app s (ψ.app s x) = ω.app s x) (p : ℕ)
    (x : (cechComplex A).homology p) : χ.homology p (ψ.homology p x) = ω.homology p x := by
  obtain ⟨x, rfl⟩ := cechClass_surjective A p x
  rw [homology_cechClass, homology_cechClass, homology_cechClass]
  exact congrArg _ (Subtype.ext (funext fun s =>
    h s.1 (Finset.card_pos.1 (by have := s.2; omega)) _))
end GlobalTheory.Cube.SemiHom
