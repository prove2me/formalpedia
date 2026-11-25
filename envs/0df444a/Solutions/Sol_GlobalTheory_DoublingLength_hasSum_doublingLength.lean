-- Prove2me | solution 1 for GlobalTheory.DoublingLength.hasSum_doublingLength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:25:37.943632+00:00
-- url     : https://prove2.me/submissions/6a60e6f1-7000-4e4c-bcbc-166e9b1ff951

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalEigenfunctionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumSphericalFunctionDoublingLength
import Theorems.Thm_GlobalTheory_DoublingLength_hasSum_pairTerm_fiber
import Theorems.Thm_GlobalTheory_DoublingLength_hasSum_pairTerm_total
import Theorems.Thm_GlobalTheory_DoublingLength_summable_pairTerm
import Theorems.Thm_GlobalTheory_DoublingLength_hasSum_pairTerm_pairEquiv
import Theorems.Thm_GlobalTheory_DoublingLength_exists_small
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_LGrp_HasGJValue_unique
import Theorems.Thm_GlobalTheory_LGrp_HasGJ_unique
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_Published_UnramifiedDoublingGL_hasSum
import Theorems.Thm_GlobalTheory_WeilM_IsTilde_unique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
open GlobalTheory GlobalTheory.DoublingLength
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
namespace GlobalTheory.DoublingLength
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k → ∀ len : GL (Fin n) k → ℕ, (∀ e : Fin n → ℤ, Antitone e → ∀ g ∈ cell k (Fin n) ϖ e, len g = (∑ i, |e i|).toNat) → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℂ, ‖X‖ < δ → HasSum (fun c : GL (Fin n) k ⧸ KO k (Fin n) => X ^ len c.out * φ c.out) ((∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) * (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)) := by
  intro k _ _ _ _ n γ φ hφ hγ ϖ hϖ len hlen
  obtain ⟨δ, hδ, hsm⟩ := exists_small (resCard k : ℝ) (Nat.cast_nonneg _) γ
  refine ⟨δ, hδ, fun X hX => ?_⟩
  have hX1 : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1 := fun i => by
    simpa using (hsm _ (norm_nonneg X) hX i).1
  have hX2 : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X‖ < 1 := fun i => by
    simpa using (hsm _ (norm_nonneg X) hX i).2.1
  have hX3 : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * X ^ 2‖ < 1 := fun i => by
    simpa using (hsm _ (norm_nonneg X) hX i).2.2
  have hsum := (summable_pairTerm hφ hγ hX1 hX2).hasSum
  rw [(hsum.prod_fiberwise (hasSum_pairTerm_fiber hφ hγ hX1)).unique (hasSum_pairTerm_total hφ hγ hX2 _)] at hsum
  have hmain := ((pairEquiv k n).hasSum_iff.2 hsum).prod_fiberwise (hasSum_pairTerm_pairEquiv hφ hϖ hlen hX3)
  have hR : ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ H => by
      have := hX3 i
      rw [← sub_eq_zero.1 H, norm_one] at this
      exact lt_irrefl _ this
  have hfun : (fun c : GL (Fin n) k ⧸ KO k (Fin n) => X ^ len c.out * φ c.out) = fun c =>
      X ^ len c.out * (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)⁻¹) * φ c.out *
        ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2) := funext fun c => by
    rw [Finset.prod_inv_distrib, mul_right_comm _ _ (φ c.out), inv_mul_cancel_right₀ hR]
  rw [hfun]
  exact hmain.mul_right _
end GlobalTheory.DoublingLength
