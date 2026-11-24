-- Prove2me | solution 1 for GlobalTheory.CubeFace.prod_alt_erase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:42:54.045963+00:00
-- url     : https://prove2.me/submissions/df28bc64-e142-4648-9964-6482a0472db8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling
import Theorems.Thm_GlobalTheory_CubeFace_prod_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.CubeFace
namespace GlobalTheory.CubeFace
theorem _root_.solution (a : Fin 3) (f : Finset (Fin 3) → ℂ) (hf : ∀ I, f I ≠ 0) :
    ∏ I : Finset (Fin 3), f (I.erase a) ^ ((-1 : ℤ) ^ (3 - I.card)) = 1 := by
  rw [prod_alt (fun I => f (I.erase a))]
  have := hf ∅
  have := hf {0}
  have := hf {1}
  have := hf {2}
  have := hf {0, 1}
  have := hf {0, 2}
  have := hf {1, 2}
  fin_cases a
  · have e1 : ({0, 1} : Finset (Fin 3)).erase 0 = {1} := by decide
    have e2 : ({0, 2} : Finset (Fin 3)).erase 0 = {2} := by decide
    have e3 : ({1, 2} : Finset (Fin 3)).erase 0 = {1, 2} := by decide
    have e4 : ({0, 1, 2} : Finset (Fin 3)).erase 0 = {1, 2} := by decide
    have e5 : ({0} : Finset (Fin 3)).erase 0 = ∅ := by decide
    have e6 : ({1} : Finset (Fin 3)).erase 0 = {1} := by decide
    have e7 : ({2} : Finset (Fin 3)).erase 0 = {2} := by decide
    simp only [Fin.zero_eta, e1, e2, e3, e4, e5, e6, e7, Finset.erase_empty]
    field_simp
  · have e1 : ({0, 1} : Finset (Fin 3)).erase 1 = {0} := by decide
    have e2 : ({0, 2} : Finset (Fin 3)).erase 1 = {0, 2} := by decide
    have e3 : ({1, 2} : Finset (Fin 3)).erase 1 = {2} := by decide
    have e4 : ({0, 1, 2} : Finset (Fin 3)).erase 1 = {0, 2} := by decide
    have e5 : ({0} : Finset (Fin 3)).erase 1 = {0} := by decide
    have e6 : ({1} : Finset (Fin 3)).erase 1 = ∅ := by decide
    have e7 : ({2} : Finset (Fin 3)).erase 1 = {2} := by decide
    simp only [Fin.mk_one, e1, e2, e3, e4, e5, e6, e7, Finset.erase_empty]
    field_simp
  · have e1 : ({0, 1} : Finset (Fin 3)).erase 2 = {0, 1} := by decide
    have e2 : ({0, 2} : Finset (Fin 3)).erase 2 = {0} := by decide
    have e3 : ({1, 2} : Finset (Fin 3)).erase 2 = {1} := by decide
    have e4 : ({0, 1, 2} : Finset (Fin 3)).erase 2 = {0, 1} := by decide
    have e5 : ({0} : Finset (Fin 3)).erase 2 = {0} := by decide
    have e6 : ({1} : Finset (Fin 3)).erase 2 = {1} := by decide
    have e7 : ({2} : Finset (Fin 3)).erase 2 = ∅ := by decide
    simp only [Fin.reduceFinMk, e1, e2, e3, e4, e5, e6, e7, Finset.erase_empty]
    field_simp
end GlobalTheory.CubeFace
