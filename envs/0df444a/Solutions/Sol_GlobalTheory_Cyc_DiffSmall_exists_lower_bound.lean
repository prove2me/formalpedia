-- Prove2me | solution 1 for GlobalTheory.Cyc.DiffSmall.exists_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:25.312321+00:00
-- url     : https://prove2.me/submissions/23875e96-6efc-4a56-983c-88bf66d4c5e9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCycCycChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTraceNormGe
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_gal
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_gal_aeval
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_C_mem_intPoly
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_map_mem_intPoly
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_eval_le_prod
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_finite_orbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open GlobalTheory.Cyc.DiffSmall
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.DiffSmall
theorem _root_.solution {y : Om l} (hy : ‖y‖ ≤ 1) : ∃ c : ℝ, 0 < c ∧
    ∀ (x : Om l) (p : ℤ_[l][X]), ‖x‖ ≤ 1 → aeval x p = y → ∀ (T : Finset ℕ) (g : ℕ → GQ l),
      Set.InjOn (fun k => g k x) T → (∀ k ∈ T, g k y ≠ y) → c ≤ ∏ k ∈ T, ‖x - g k x‖ := by
  classical
  set R := (finite_orbit y).toFinset with hR
  refine ⟨∏ r ∈ R.erase y, ‖y - r‖, Finset.prod_pos fun r hr => ?_, ?_⟩
  · exact norm_pos_iff.2 (sub_ne_zero.2 (Finset.ne_of_mem_erase hr).symm)
  intro x p hx hp T g hinj hne
  set Q : (Om l)[X] := ∏ r ∈ R.erase y, (p.map (algebraMap ℤ_[l] (Om l)) - C r) with hQ
  have hev : ∀ z, Q.eval z = ∏ r ∈ R.erase y, (aeval z p - r) := by
    intro z
    simp [hQ, eval_prod, eval_map_algebraMap]
  have := norm_eval_le_prod T (fun k => g k x) hinj (fun k _ => by rwa [norm_gal]) hx Q
    (prod_mem fun r hr => sub_mem (map_mem_intPoly p) (C_mem_intPoly ?_)) fun k hk => ?_
  · rwa [hev, hp, norm_prod] at this
  · have := Finset.mem_of_mem_erase hr
    rw [hR, Set.Finite.mem_toFinset] at this
    obtain ⟨g, rfl⟩ := this
    rwa [norm_gal]
  · rw [hev, ← gal_aeval, hp]
    refine Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hne k hk, ?_⟩) (sub_self _)
    rw [hR, Set.Finite.mem_toFinset]
    exact ⟨g k, rfl⟩
end GlobalTheory.Cyc.DiffSmall
