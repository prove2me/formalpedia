-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PatGrp.patGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:44:18.00744+00:00
-- url     : https://prove2.me/submissions/2a40e775-a611-4e75-9cfd-0007081a914b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_coe_patSubgroup
import Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_card_patSet
import Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_patChar_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_patChar_one
import Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_exists_nat_wh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PatGrp
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Φ : ι → ι → Prop}
namespace GlobalTheory.CompanionTheory.PatGrp
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.PatGroup := by
  intro K _ _ _ ι _ _ Φ h
  refine ⟨⟨patSubgroup h, coe_patSubgroup h⟩, card_patSet h, fun E ψ₀ hE =>
    ⟨fun u hu v hv => patChar_mul h hE ψ₀ hu hv, patChar_one h hE ψ₀, fun u hu => ?_,
      fun V _ _ _ ρ => exists_nat_wh h hE ψ₀ ρ⟩⟩
  have hu' : u ∈ ((patSubgroup h : Subgroup (GL ι K)) : Set (GL ι K)) := by
    rw [coe_patSubgroup h]
    exact hu
  have hinv : u⁻¹ ∈ patSet K Φ := by
    rw [← coe_patSubgroup h]
    exact (patSubgroup (K := K) h).inv_mem hu'
  have hm := patChar_mul h hE ψ₀ hu hinv
  rw [mul_inv_cancel, patChar_one h hE ψ₀] at hm
  exact eq_inv_of_mul_eq_one_right hm.symm
end GlobalTheory.CompanionTheory.PatGrp
