-- Prove2me | solution 1 for GlobalTheory.valuation_pow_apply_div_sub_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:35:23.761841+00:00
-- url     : https://prove2.me/submissions/33ccd02b-2696-4e53-9e1f-be5c78f00bb3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ValuationPowApplyDivSubOneLt
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open GlobalTheory
open NumberField IsDedekindDomain
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (x : Ω) (hx : x ≠ 0) (i : ℕ) :
    A.valuation ((σ ^ i) x / x - 1) < 1 := by
  induction i with
  | zero => simp [hx]
  | succ i ih =>
    have hy0 : (σ ^ i) x ≠ 0 := (map_ne_zero (σ ^ i)).2 hx
    have hle : A.valuation ((σ ^ i) x / x) ≤ 1 := by
      have e : (σ ^ i) x / x = ((σ ^ i) x / x - 1) + 1 := by ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans (max_le ih.le (by simp))
    have key : (σ ^ (i + 1)) x / x - 1 =
        (σ ((σ ^ i) x) / (σ ^ i) x - 1) * ((σ ^ i) x / x) + ((σ ^ i) x / x - 1) := by
      rw [pow_succ', AlgEquiv.mul_apply]
      field_simp
      ring
    rw [key]
    apply Valuation.map_add_lt _ _ ih
    rw [map_mul]
    calc A.valuation (σ ((σ ^ i) x) / (σ ^ i) x - 1) * A.valuation ((σ ^ i) x / x)
        ≤ A.valuation (σ ((σ ^ i) x) / (σ ^ i) x - 1) * 1 := by gcongr
      _ < 1 := by simpa using hσ _ hy0
end _root_.GlobalTheory
end GlobalTheory
