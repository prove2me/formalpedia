-- Prove2me | solution 1 for GlobalTheory.cubeComparison_f
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:40:09.562314+00:00
-- url     : https://prove2.me/submissions/7999cc8e-f8cf-42dc-9b30-e64b5ee90fad

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
variable {ι : Type} {R : Type u} [Ring R] {S : Type u'} [Ring S]
  (F : ModuleCat.{v} R ⥤ ModuleCat.{v'} S)
variable [LinearOrder ι] [F.Additive]
theorem _root_.solution (A : Cube.{v} ι R) (p : ℕ) :
    (cubeComparison F A).f p = Cube.termComparison F A p := by
  first
    | (intros; rfl)
    | exact Iff.rfl
    | decide
    | (intros; omega)
    | (intros; simp)
    | (intros; simp_all)
    | (intros; norm_num)
    | (intros; positivity)
    | (intros; aesop)
    | (intros; nlinarith)
    | (intros; field_simp; ring)
    | (intros; ext; simp)
    | (intros; constructor <;> intro h <;> simpa using h)
    | (intros; exact?)
  trace "HIT_54_3"

