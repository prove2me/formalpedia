-- Prove2me | solution 1 for GlobalTheory.smul_dlogWedge_mem_regForms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:35:26.549393+00:00
-- url     : https://prove2.me/submissions/20f55d6b-adc9-4c68-8f35-bf7ed7233ed4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_GlobalTheory_alternating_smul_add_mem
import Theorems.Thm_P2M_GlobalTheory__Multi_mem_regForms_c782fe77fe92
import Theorems.Thm_GlobalTheory_dlog_mul
import Theorems.Thm_GlobalTheory_dlog_zpow
import Theorems.Thm_GlobalTheory_dlog_unit_mem_range

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
variable (K : Type*) {F : Type*} [CommRing K] [Field F] [Algebra K F] {p : ℕ}
variable {V : Type*} [CommRing V] [Algebra K V] [Algebra V F] [IsScalarTower K V F]
namespace GlobalTheory
theorem _root_.solution (t : V) (ht : algebraMap V F t ≠ 0) (S : Finset (Fin p))
    (x : Fin p → F) (hS : ∀ k ∈ S, ∃ (m : ℤ) (u : Vˣ), x k = algebraMap V F u * algebraMap V F t ^ m)
    (hS' : ∀ k ∉ S, x k ∈ Set.range (algebraMap V F)) :
    t • dlogWedge K S x ∈ regForms K V F p := by
  classical
  let θ : Ω[F⁄K] := (algebraMap V F t)⁻¹ • D K F (algebraMap V F t)
  have hθ : t • θ ∈ LinearMap.range (KaehlerDifferential.map K K V F) := by
    refine ⟨D K V t, ?_⟩
    rw [map_D, ← algebraMap_smul F t, smul_smul, mul_inv_cancel₀ ht, one_smul]
  have hx : ∀ k, ∃ (a : V) (w : Ω[F⁄K]),
      (if k ∈ S then (x k)⁻¹ • D K F (x k) else D K F (x k)) = a • θ + w ∧
        w ∈ LinearMap.range (KaehlerDifferential.map K K V F) := by
    intro k
    split_ifs with hk
    · obtain ⟨m, u, h⟩ := hS k hk
      refine ⟨m, _, ?_, dlog_unit_mem_range K u⟩
      rw [h, dlog_mul K ((u.isUnit.map (algebraMap V F)).ne_zero) (zpow_ne_zero m ht),
        dlog_zpow K ht, add_comm, Int.cast_smul_eq_zsmul]
    · obtain ⟨y, hy⟩ := hS' k hk
      exact ⟨0, _, by rw [zero_smul, zero_add], D K V y, by rw [map_D, hy]⟩
  choose a w hw hw' using hx
  let P : Submodule V (⋀[F]^p Ω[F⁄K]) := (regForms K V F p).comap (t • LinearMap.id)
  have : altRestrictScalars V (exteriorPower.ιMulti F p) (fun k => a k • θ + w k) ∈ P := by
    refine alternating_smul_add_mem _ P θ a w ?_ fun k => ?_
    · exact (regForms K V F p).smul_mem t (ιMulti_mem_regForms K F w hw')
    · change t • altRestrictScalars V (exteriorPower.ιMulti F p) (Function.update w k θ)
        ∈ regForms K V F p
      rw [← AlternatingMap.map_update_smul]
      refine ιMulti_mem_regForms K F _ fun l => ?_
      by_cases hl : l = k
      · subst hl
        rwa [Function.update_self]
      · rw [Function.update_of_ne hl]
        exact hw' l
  rw [dlogWedge, funext hw]
  exact this
end GlobalTheory
