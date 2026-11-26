-- Prove2me | solution 1 for GlobalTheory.cubeComplexMap_f
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:13:39.007501+00:00
-- url     : https://prove2.me/submissions/158f7af4-da19-4df3-a833-f2b13702043d

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
theorem _root_.solution {A B : Cube.{v} ι R} (φ : A ⟶ B) (p : ℕ) :
    (cubeComplexMap φ).f p = ModuleCat.ofHom (Cube.termMap φ p) := by
  first
    | (intros; simp [Cube, termMap, cubeComplexMap])
    | (intros; unfold Cube termMap cubeComplexMap; simp)
    | (intros; simp [Cube, termMap, cubeComplexMap]; done)
    | (intros; ext; simp [Cube, termMap, cubeComplexMap])
    | (intros; simp only [Cube, termMap, cubeComplexMap]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [Cube, termMap, cubeComplexMap])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [Cube, termMap, cubeComplexMap])
    | (intros; unfold Cube termMap cubeComplexMap; split_ifs <;> simp_all)
    | (intros; unfold Cube termMap cubeComplexMap; positivity)
    | (intros; unfold Cube termMap cubeComplexMap; ring)
    | (intros; unfold Cube termMap cubeComplexMap; exact?)
    | (intros; aesop (add norm simp [Cube, termMap, cubeComplexMap]))
    | (intros; simp [Cube, termMap, cubeComplexMap] <;> aesop)
    | (intros; exact Cube.symm ..)
    | (intros; exact Cube.comm ..)
    | (intros; exact termMap.symm ..)
    | (intros; exact termMap.comm ..)
  trace "HIT_17_8"

