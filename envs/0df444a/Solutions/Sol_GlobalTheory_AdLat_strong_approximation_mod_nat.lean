-- Prove2me | solution 1 for GlobalTheory.AdLat.strong_approximation_mod_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:30:40.778829+00:00
-- url     : https://prove2.me/submissions/c8feddc0-5830-4b0b-b05d-5cc271635b02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Theorems.Thm_GlobalTheory_AdLat_exists_eq_algebraMap_add_nsmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
namespace GlobalTheory.AdLat
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), 0 < N → (∀ y : FiniteAdeleRing (𝓞 F) F, ∃ (x : F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = algebraMap F _ x + N • a) ∧ ∀ y : FiniteAdeleRing (𝓞 F) F, (∀ v, y v ∈ v.adicCompletionIntegers F) → ∃ (x : 𝓞 F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = algebraMap F _ (x : F) + N • a := by
  intro F _ _ N hN
  refine ⟨exists_eq_algebraMap_add_nsmul F N hN, fun y hy => ?_⟩
  obtain ⟨x, a, ha, rfl⟩ := exists_eq_algebraMap_add_nsmul F N hN y
  have hx : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F x ≤ 1 := by
    intro v
    have hNa : (N • a) v ∈ v.adicCompletionIntegers F := by
      rw [show (N • a) v = N • a v from rfl]
      exact nsmul_mem (ha v) N
    have e : (algebraMap F (FiniteAdeleRing (𝓞 F) F) x + N • a) v =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) x v + (N • a) v := rfl
    have h := sub_mem (hy v) hNa
    rw [e, add_sub_cancel_right, FiniteAdeleRing.algebraMap_apply,
      HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
    exact h
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) x hx
  subst hr
  exact ⟨r, a, ha, rfl⟩
end GlobalTheory.AdLat
