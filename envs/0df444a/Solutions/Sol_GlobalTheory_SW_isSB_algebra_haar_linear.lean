-- Prove2me | solution 1 for GlobalTheory.SW.isSB_algebra_haar_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:41:43.770596+00:00
-- url     : https://prove2.me/submissions/ab5048f4-c65f-40a0-9d8c-77acc4ccfe67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Theorems.Thm_GlobalTheory_SW_HaarAlg_hasLevel_mul
import Theorems.Thm_GlobalTheory_SW_HaarAlg_exists_common_level
import Theorems.Thm_P2M_GlobalTheory_SW_HaarAlg_hasLevel_map__fb46485b3230
import Theorems.Thm_GlobalTheory_SW_HaarAlg_exists_natCast_smul_intM
import Theorems.Thm_GlobalTheory_SW_HaarAlg_hasLevel_translate
import Theorems.Thm_GlobalTheory_SW_HaarAlg_finsum_translate
import Theorems.Thm_GlobalTheory_SW_haar_eq_haarAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory.SW.HaarAlg
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (φ ψ : Matrix κ ι K → ℂ), IsSB φ → IsSB ψ → IsSB (φ + ψ) ∧ (∀ c : ℂ, IsSB (c • φ)) ∧ IsSB (φ * ψ) ∧ IsSB (fun x : Matrix κ ι K => conj (φ x)) ∧ haar (φ + ψ) = haar φ + haar ψ ∧ (∀ c : ℂ, haar (c • φ) = c * haar φ) ∧ haar (fun x : Matrix κ ι K => conj (φ x)) = conj (haar φ) ∧ ∀ b : Matrix κ ι K, IsSB (fun x : Matrix κ ι K => φ (x - b)) ∧ haar (fun x : Matrix κ ι K => φ (x - b)) = haar φ := by
  intro K κ ι _ _ _ _ φ ψ hφ hψ
  obtain ⟨R, hR, h1, h2⟩ := exists_common_level hφ hψ
  have hadd : HasLevel R (φ + ψ) := hasLevel_map₂ h1 h2 (fun a b => a + b) (by simp)
  have hsmul : ∀ c : ℂ, HasLevel R (c • φ) := fun c =>
    hasLevel_map₂ h1 h2 (fun a _ => c * a) (by simp)
  have hmul : HasLevel R (φ * ψ) := hasLevel_map₂ h1 h2 (fun a b => a * b) (by simp)
  have hconj : HasLevel R (fun x => conj (φ x)) :=
    hasLevel_map₂ h1 h2 (fun a _ => conj a) (by simp)
  obtain ⟨e1, f1⟩ := GlobalTheory.SW.haar_eq_haarAt K κ ι R φ hR h1
  obtain ⟨e2, f2⟩ := GlobalTheory.SW.haar_eq_haarAt K κ ι R ψ hR h2
  refine ⟨⟨R, hR, hadd⟩, fun c => ⟨R, hR, hsmul c⟩, ⟨R, hR, hmul⟩, ⟨R, hR, hconj⟩, ?_,
    fun c => ?_, ?_, fun b => ?_⟩
  · rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hadd).1, e1, e2]
    unfold haarAt
    rw [← mul_add, ← finsum_add_distrib f1 f2]
    rfl
  · rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR (hsmul c)).1, e1]
    unfold haarAt
    rw [mul_left_comm c]
    congr 1
    exact ((AddMonoidHom.mulLeft c).map_finsum f1).symm
  · rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hconj).1, e1]
    unfold haarAt
    rw [map_mul, map_inv₀, map_pow, map_natCast]
    congr 1
    exact ((starRingEnd ℂ).toAddMonoidHom.map_finsum f1).symm
  · obtain ⟨N, hN, hb⟩ := exists_natCast_smul_intM b
    have hRN := Nat.mul_pos hR hN
    have ht := hasLevel_translate h1 hb
    refine ⟨⟨_, hRN, ht⟩, ?_⟩
    rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι _ _ hRN ht).1, (GlobalTheory.SW.haar_eq_haarAt K κ ι _ _ hRN (hasLevel_mul h1 N)).1]
    unfold haarAt
    rw [finsum_translate (hasLevel_mul h1 N) b]
end GlobalTheory.SW
