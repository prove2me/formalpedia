-- Prove2me | solution 1 for GlobalTheory.cubeLowerProj_f
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:26:30.241801+00:00
-- url     : https://prove2.me/submissions/4380c64d-b15d-47c3-bb30-1fdb6acf70f3

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Mathlib



-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
  {e : κ ↪o ι} {i : ι}
theorem _root_.solution (A : Cube.{v} ι R) (p : ℕ) :
    (cubeLowerProj e A).f p = ModuleCat.ofHom (Cube.termLower e A p) := by
  first
    | (intros; simp [Cube, termLower, cubeLowerProj])
    | (intros; unfold Cube termLower cubeLowerProj; simp)
    | (intros; simp [Cube, termLower, cubeLowerProj]; done)
    | (intros; ext; simp [Cube, termLower, cubeLowerProj])
    | (intros; simp only [Cube, termLower, cubeLowerProj]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [Cube, termLower, cubeLowerProj])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [Cube, termLower, cubeLowerProj])
    | (intros; unfold Cube termLower cubeLowerProj; split_ifs <;> simp_all)
    | (intros; unfold Cube termLower cubeLowerProj; positivity)
    | (intros; unfold Cube termLower cubeLowerProj; ring)
    | (intros; unfold Cube termLower cubeLowerProj; exact?)
    | (intros; aesop (add norm simp [Cube, termLower, cubeLowerProj]))
    | (intros; simp [Cube, termLower, cubeLowerProj] <;> aesop)
    | (intros; exact Cube.symm ..)
    | (intros; exact Cube.comm ..)
    | (intros; exact termLower.symm ..)
    | (intros; exact termLower.comm ..)
  trace "HIT_104_1"

