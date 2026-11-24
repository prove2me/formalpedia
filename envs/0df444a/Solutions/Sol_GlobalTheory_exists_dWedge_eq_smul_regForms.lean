-- Prove2me | solution 1 for GlobalTheory.exists_dWedge_eq_smul_regForms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:42:16.293532+00:00
-- url     : https://prove2.me/submissions/a0cb4c21-15d7-4137-8fed-742bc2714aee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_GlobalTheory_dWedge_mem_of_two_mem
import Theorems.Thm_GlobalTheory_formMap_dWedge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (K V F : Type*) [CommRing K] [CommRing V] [CommRing F] [Algebra K V] [Algebra V F]
  [Algebra K F] [IsScalarTower K V F] (p : ℕ)
variable {V p}
namespace GlobalTheory
theorem _root_.solution (t : V) (x : Fin p → V) {i j : Fin p} (hij : i ≠ j)
    (hi : t ∣ x i) (hj : t ∣ x j) :
    ∃ η ∈ regForms K V F p, dWedge K (fun k => algebraMap V F (x k)) = t • η := by
  obtain ⟨η, hη⟩ := dWedge_mem_of_two_mem K t x hij hi hj
  exact ⟨_, ⟨η, rfl⟩, by rw [← formMap_dWedge, hη, map_smul]⟩
end GlobalTheory
