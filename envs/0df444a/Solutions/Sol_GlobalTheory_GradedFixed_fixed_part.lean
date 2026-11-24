-- Prove2me | solution 1 for GlobalTheory.GradedFixed.fixed_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:55:10.930288+00:00
-- url     : https://prove2.me/submissions/923c96cc-88bf-4516-a49a-a208ef1eb8a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FixedMemOfOrbitHeight
import Theorems.Thm_GlobalTheory_GradedFixed_map_WA_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule MulAction
open GlobalTheory GlobalTheory.GradedFixed
variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.GradedFixed
theorem _root_.solution (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M) (hV : iSupIndep V)
    (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) {A B : Set ι}
    (hA : ∀ (g : G), ∀ j ∈ A, g • j ∈ A) (hB : ∀ (g : G), ∀ j ∈ B, g • j ∈ B)
    (hAB : Disjoint A B) {a b : M} (ha : a ∈ WA V A) (hb : b ∈ WA V B)
    (hfix : ∀ g, π g (a + b) = a + b) : ∀ g, π g a = a := by
  intro g
  have h1 : π g a - a ∈ WA V A := sub_mem (map_WA_le π V hπ hA g ha) ha
  have h2 : π g a - a ∈ WA V B := by
    have e : π g a - a = b - π g b := by
      rw [sub_eq_sub_iff_add_eq_add, ← map_add, hfix g, add_comm]
    rw [e]
    exact sub_mem hb (map_WA_le π V hπ hB g hb)
  have hd : Disjoint (WA V A) (WA V B) := hV.disjoint_biSup_biSup hAB
  exact sub_eq_zero.mp (Submodule.disjoint_def.mp hd _ h1 h2)
end GlobalTheory.GradedFixed
