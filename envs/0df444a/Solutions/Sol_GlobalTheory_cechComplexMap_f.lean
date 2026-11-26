-- Prove2me | solution 1 for GlobalTheory.cechComplexMap_f
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:13:51.043564+00:00
-- url     : https://prove2.me/submissions/d29fea80-34bf-4d76-b905-8726297270f6

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
    (cechComplexMap φ).f p = ModuleCat.ofHom (Cube.termMap φ (p + 1)) := by
  first
    | (intros; simp [Cube, termMap, cechComplexMap])
    | (intros; unfold Cube termMap cechComplexMap; simp)
    | (intros; simp [Cube, termMap, cechComplexMap]; done)
    | (intros; ext; simp [Cube, termMap, cechComplexMap])
    | (intros; simp only [Cube, termMap, cechComplexMap]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [Cube, termMap, cechComplexMap])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [Cube, termMap, cechComplexMap])
    | (intros; unfold Cube termMap cechComplexMap; split_ifs <;> simp_all)
    | (intros; unfold Cube termMap cechComplexMap; positivity)
    | (intros; unfold Cube termMap cechComplexMap; ring)
    | (intros; unfold Cube termMap cechComplexMap; exact?)
    | (intros; aesop (add norm simp [Cube, termMap, cechComplexMap]))
    | (intros; simp [Cube, termMap, cechComplexMap] <;> aesop)
    | (intros; exact Cube.symm ..)
    | (intros; exact Cube.comm ..)
    | (intros; exact termMap.symm ..)
    | (intros; exact termMap.comm ..)
  trace "HIT_17_9"

