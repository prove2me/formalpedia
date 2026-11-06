-- Prove2me | solution 1 for OAI.ShortDraftCRT.crossDen_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:31:06.067206+00:00
-- url     : https://prove2.me/submissions/74c867bb-1285-4de8-9aaa-d1b02fae8e56

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.ShortDraftCRT
open AddChar
variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R]
namespace OAI.ShortDraftCRT
theorem _root_.solution (ι : R →+* K) (c₀ : R)
    (rows : List (R × R)) (hc₀ : ι c₀ ≠ 0)
    (hp : ∀ ph ∈ rows, ι ph.1 ≠ 0) :
    ι (crossDen c₀ rows) ≠ 0 := by
  revert hp
  induction rows with
  | nil =>
      intro _
      simpa [crossDen] using hc₀
  | cons ph rows ih =>
      rcases ph with ⟨p, h⟩
      intro hp
      simp only [crossDen, map_mul]
      exact mul_ne_zero (ih (by
        intro ph hmem
        exact hp ph (List.mem_cons_of_mem _ hmem)))
        (hp (p, h) (List.mem_cons_self ..))
end OAI.ShortDraftCRT
