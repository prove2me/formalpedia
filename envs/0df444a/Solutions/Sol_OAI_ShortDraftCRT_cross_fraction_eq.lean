-- Prove2me | solution 1 for OAI.ShortDraftCRT.cross_fraction_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:09.357534+00:00
-- url     : https://prove2.me/submissions/7efd58a2-bb70-4839-a3ce-ff43721ef0b3

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Theorems.Thm_OAI_ShortDraftCRT_crossDen_ne_zero

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
theorem _root_.solution (ι : R →+* K) (a c₀ : R)
    (rows : List (R × R)) (hc₀ : ι c₀ ≠ 0)
    (hp : ∀ ph ∈ rows, ι ph.1 ≠ 0) :
    ι (crossNum a c₀ rows) / ι (crossDen c₀ rows) =
      ι a / ι c₀ +
        (rows.map fun ph => ι ph.2 / ι ph.1).sum := by
  revert hp
  induction rows with
  | nil =>
      intro _
      simp [crossNum, crossDen]
  | cons ph rows ih =>
      rcases ph with ⟨p, h⟩
      intro hp
      have hden : ι (crossDen c₀ rows) ≠ 0 :=
        crossDen_ne_zero ι c₀ rows hc₀ (by
          intro ph hmem
          exact hp ph (List.mem_cons_of_mem _ hmem))
      have hp₀ : ι p ≠ 0 := hp (p, h) (List.mem_cons_self ..)
      simp only [crossNum, crossDen, map_add, map_mul,
        List.map_cons, List.sum_cons]
      calc
        (ι (crossNum a c₀ rows) * ι p + ι h * ι (crossDen c₀ rows)) /
            (ι (crossDen c₀ rows) * ι p) =
          ι (crossNum a c₀ rows) / ι (crossDen c₀ rows) + ι h / ι p := by
            field_simp
        _ = ι a / ι c₀ +
            (ι h / ι p + (rows.map fun ph => ι ph.2 / ι ph.1).sum) := by
          rw [ih (by
            intro ph hmem
            exact hp ph (List.mem_cons_of_mem _ hmem))]
          ring
end OAI.ShortDraftCRT
