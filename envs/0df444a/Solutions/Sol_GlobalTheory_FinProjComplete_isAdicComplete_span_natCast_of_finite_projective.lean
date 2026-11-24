-- Prove2me | solution 1 for GlobalTheory.FinProjComplete.isAdicComplete_span_natCast_of_finite_projective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:45:18.792529+00:00
-- url     : https://prove2.me/submissions/3d46dda7-270c-434a-9b3e-621299d1ebad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAdicCompleteSpanNatCastFiniteProjectiveAlgebra
import Theorems.Thm_GlobalTheory_FinProjComplete_isAdicComplete_pi
import Theorems.Thm_GlobalTheory_FinProjComplete_isAdicComplete_of_retract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinProjComplete
namespace GlobalTheory.FinProjComplete
theorem _root_.solution (p : ℕ) (O A : Type) [CommRing O] [CommRing A]
    [Algebra O A] [Module.Finite O A] [Module.Projective O A]
    [IsAdicComplete (Ideal.span {(p : O)}) O] : IsAdicComplete (Ideal.span {(p : A)}) A := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' O A
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have : IsAdicComplete (Ideal.span {(p : O)}) (Fin r → O) := isAdicComplete_pi _
  have hO : IsAdicComplete (Ideal.span {(p : O)}) A :=
    isAdicComplete_of_retract _ π s fun x => by simpa using LinearMap.congr_fun hs x
  have hmap : (Ideal.span {(p : O)}).map (algebraMap O A) = Ideal.span {(p : A)} := by
    simp [Ideal.map_span]
  rw [← hmap]
  exact (IsAdicComplete.map_algebraMap_iff _ _).2 hO
end GlobalTheory.FinProjComplete
