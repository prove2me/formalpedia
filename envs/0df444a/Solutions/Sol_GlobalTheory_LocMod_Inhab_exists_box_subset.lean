-- Prove2me | solution 1 for GlobalTheory.LocMod.Inhab.exists_box_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:58.829699+00:00
-- url     : https://prove2.me/submissions/0ce27813-a7aa-4836-8e3c-ab280d8ed5ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Theorems.Thm_GlobalTheory_LocMod_Inhab_isCompact_box
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_subset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology
open GlobalTheory GlobalTheory.LocMod GlobalTheory.LocMod.Inhab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
namespace GlobalTheory.LocMod.Inhab
theorem _root_.solution {U : Set (Matrix Y Y' k)} (hU : U ∈ 𝓝 0) : ∃ a : kˣ, ∀ x ∈ box Y Y' a, x ∈ U := by
  have h := (isCompact_box (Y := Y) (Y' := Y') (1 : kˣ)).eventually_forall_of_forall_eventually (x₀ := (0 : k))
    (P := fun c x => c • x ∈ U) fun x _ =>
      (continuous_smul.tendsto' ((0 : k), x) 0 (zero_smul _ _)).eventually hU
  obtain ⟨s, hs⟩ := exists_cball_subset h
  refine ⟨s, fun x hx => ?_⟩
  have := hs (show (s : k) ∈ cball s from le_refl (valuation k (s : k))) ((s : k)⁻¹ • x) fun r q => by
    have h0 : valuation k (s : k) ≠ 0 := by simp
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, Units.val_one, map_one]
    exact inv_mul_le_one_of_le₀ (hx r q) zero_le'
  rwa [smul_inv_smul₀ s.ne_zero] at this
end GlobalTheory.LocMod.Inhab
