-- Prove2me | solution 1 for GlobalTheory.cubeComplex_X
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:13:22.134998+00:00
-- url     : https://prove2.me/submissions/30f8a101-265f-484c-a2bd-b220f00966d8

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Mathlib


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
theorem _root_.solution (A : Cube.{v} ι R) (p : ℕ) :
    (cubeComplex A).X p = ModuleCat.of R (Cube.Term A p) := by
  first
    | (intros; simp [Cube, Term, cubeComplex])
    | (intros; unfold Cube Term cubeComplex; simp)
    | (intros; simp [Cube, Term, cubeComplex]; done)
    | (intros; ext; simp [Cube, Term, cubeComplex])
    | (intros; simp only [Cube, Term, cubeComplex]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [Cube, Term, cubeComplex])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [Cube, Term, cubeComplex])
    | (intros; unfold Cube Term cubeComplex; split_ifs <;> simp_all)
    | (intros; unfold Cube Term cubeComplex; positivity)
    | (intros; unfold Cube Term cubeComplex; ring)
    | (intros; unfold Cube Term cubeComplex; exact?)
    | (intros; aesop (add norm simp [Cube, Term, cubeComplex]))
    | (intros; simp [Cube, Term, cubeComplex] <;> aesop)
    | (intros; exact Cube.symm ..)
    | (intros; exact Cube.comm ..)
    | (intros; exact Term.symm ..)
    | (intros; exact Term.comm ..)
  trace "HIT_17_2"

