-- Prove2me | solution 1 for GlobalTheory.Nef.place_res_exists_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:25:29.468936+00:00
-- url     : https://prove2.me/submissions/cddf1a9e-2927-4a1e-b092-2c4ee97bcccc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceRestrictionExistsPow
import Theorems.Thm_GlobalTheory_Nef_PlaceResiduePowerBound_pow_inj
import Theorems.Thm_P2M_GlobalTheory_Nef_PlaceResiduePowerBound_pow_le_one_iff__b5da8e0cef6d
import Theorems.Thm_GlobalTheory_Nef_PlaceResiduePowerBound_pow_of_iff
import Theorems.Thm_GlobalTheory_Nef_PlaceResiduePowerBound_root
import Theorems.Thm_GlobalTheory_Nef_PlaceResiduePowerBound_exists_one_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef
open WithZero
namespace GlobalTheory.Nef
theorem _root_.solution : ∀ (k F E : Type) [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E]
    [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E],
    (∃ ρ : Place k E → Place k F, IsRes ρ) ∧ ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ p,
      ∃ e : ℕ, 0 < e ∧ (∀ x : F, p.1 (algebraMap F E x) = (ρ p).1 x ^ e) ∧
        ∀ x : F, ord p (algebraMap F E x) = e * ord (ρ p) x := by
  intro k F E _ _ _ _ _ _ _ _
  refine ⟨?_, fun ρ hρ p => ?_⟩
  · have hex : ∀ p : Place k E, ∃ q : Place k F,
        ∀ x, p.1 (algebraMap F E x) ≤ 1 ↔ q.1 x ≤ 1 := by
      intro p
      obtain ⟨a, ha⟩ := PlaceResiduePowerBound.exists_one_lt (F := F) p.1 p.2.1
      obtain ⟨q, hq, e, he, hpow⟩ := PlaceResiduePowerBound.root (p.1.comap (algebraMap F E)) ⟨a, ha⟩
      refine ⟨⟨q, hq, fun c hc => ?_⟩, fun x => ?_⟩
      · apply PlaceResiduePowerBound.pow_inj he.ne'
        rw [← hpow, Valuation.comap_apply, ← IsScalarTower.algebraMap_apply, p.2.2 c hc, one_pow]
      · have h := hpow x
        rw [Valuation.comap_apply] at h
        rw [h, PlaceResiduePowerBound.pow_le_one_iff' he.ne']
    choose ρ hρ using hex
    exact ⟨ρ, hρ⟩
  · obtain ⟨e, he, hpow⟩ :=
      PlaceResiduePowerBound.pow_of_iff (p.1.comap (algebraMap F E)) (ρ p).1 (ρ p).2.1 (fun x => hρ p x)
    refine ⟨e, he, fun x => hpow x, fun x => ?_⟩
    have h : p.1 (algebraMap F E x) = (ρ p).1 x ^ e := hpow x
    unfold ord
    rw [h, log_pow, nsmul_eq_mul]
    ring
end GlobalTheory.Nef
