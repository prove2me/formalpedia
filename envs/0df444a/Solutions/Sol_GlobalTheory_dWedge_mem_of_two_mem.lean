-- Prove2me | solution 1 for GlobalTheory.dWedge_mem_of_two_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:35:27.509706+00:00
-- url     : https://prove2.me/submissions/61cc7514-483d-42cd-b52d-d5a129308c86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_GlobalTheory_alternating_smul_add_mem
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A] {p : ℕ}
namespace GlobalTheory
theorem _root_.solution (t : A) (x : Fin p → A) {i j : Fin p} (hij : i ≠ j)
    (hi : t ∣ x i) (hj : t ∣ x j) :
    ∃ η : ⋀[A]^p Ω[A⁄R], dWedge R x = t • η := by
  classical
  let P : Submodule A (⋀[A]^p Ω[A⁄R]) := LinearMap.range (t • LinearMap.id)
  have hP : ∀ (v : Fin p → Ω[A⁄R]) (k : Fin p) (u : Ω[A⁄R]), v k = t • u →
      exteriorPower.ιMulti A p v ∈ P := by
    intro v k u h
    refine ⟨exteriorPower.ιMulti A p (Function.update v k u), ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, ← AlternatingMap.map_update_smul, ← h,
      Function.update_eq_self]
  have hx : ∀ k, ∃ (a : A) (w : Ω[A⁄R]), D R A (x k) = a • D R A t + w ∧
      (t ∣ x k → ∃ u, w = t • u) := by
    intro k
    by_cases hk : t ∣ x k
    · obtain ⟨c, hc⟩ := hk
      exact ⟨c, t • D R A c, by rw [hc, Derivation.leibniz, add_comm], fun _ => ⟨_, rfl⟩⟩
    · exact ⟨0, D R A (x k), by simp, fun h => absurd h hk⟩
  choose a w hw hw' using hx
  obtain ⟨ui, hui⟩ := hw' i hi
  obtain ⟨uj, huj⟩ := hw' j hj
  have : dWedge R x ∈ P := by
    rw [dWedge, funext hw]
    refine alternating_smul_add_mem _ P _ a w (hP w i ui hui) fun k => ?_
    by_cases hk : i = k
    · exact hP _ j uj (by rw [Function.update_of_ne (hk ▸ hij.symm), huj])
    · exact hP _ i ui (by rw [Function.update_of_ne hk, hui])
  obtain ⟨η, hη⟩ := this
  exact ⟨η, hη.symm⟩
end GlobalTheory
