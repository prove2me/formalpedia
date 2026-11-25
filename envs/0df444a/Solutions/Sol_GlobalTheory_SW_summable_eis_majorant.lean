-- Prove2me | solution 1 for GlobalTheory.SW.summable_eis_majorant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:22:01.315126+00:00
-- url     : https://prove2.me/submissions/e148ed3b-1e24-45ed-aa16-20dd79755a43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorant
import Theorems.Thm_GlobalTheory_SW_EisConv_one_le_norm_embAll
import Theorems.Thm_GlobalTheory_SW_EisConv_summable_embAll
import Theorems.Thm_GlobalTheory_SW_EisConv_summable_prod_tuple
import Theorems.Thm_GlobalTheory_SW_EisConv_exists_short_generators
import Theorems.Thm_GlobalTheory_SW_IsType_finrank_eq
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory.SW.EisConv
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), 4 * N < n → ∀ (c : ℕ) (rep : Lag E N → M2 E N), 0 < c → (∀ U, rep U ∈ UU E N ∧ Den c (rep U) ∧ botSpan (rep U) = U.1) → Summable fun U : Lag E N => ∏ τ : Ψ, (‖(hDen Ψ (rep U) (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ)) τ).det‖ ^ n)⁻¹ := by
  intro E _ _ _ Ψ hΨ n N hn c rep hc hrep
  obtain ⟨K, hK, H⟩ := exists_short_generators hΨ N c hc
  choose w hspan hne hle using fun U => H (rep U) (hrep U).1 (hrep U).2.1
  have hinj : Function.Injective w := fun U V h => Subtype.ext (by
    rw [← (hrep U).2.2, ← (hrep V).2.2, ← hspan, ← hspan, h])
  have hf : 0 < Ψ.card := by
    have h1 := hΨ.finrank_eq
    have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  have hs := summable_embAll E (Fin N ⊕ Fin N) (Ψ.card * n) (by
    rw [hΨ.finrank_eq, Fintype.card_sum, Fintype.card_fin]
    nlinarith)
  have hs2 := ((summable_prod_tuple hs (fun _ => by positivity) N).comp_injective hinj).mul_left
    (K ^ n)
  refine Summable.of_nonneg_of_le (fun U => by positivity) (fun U => ?_) hs2
  have hp : 0 < ∏ i, ‖embAll E _ (w U i)‖ ^ Ψ.card := Finset.prod_pos fun i _ =>
    pow_pos (one_pos.trans_le (one_le_norm_embAll (hne U i))) _
  have hP := (pos_iff_pos_of_mul_pos (hp.trans_le (hle U))).1 hK
  simp only [Function.comp, pow_mul, inv_pow]
  rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib, Finset.prod_pow, Finset.prod_pow _ n,
    ← div_eq_mul_inv, ← div_pow, ← inv_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ n
  rw [inv_eq_one_div, div_le_div_iff₀ hP hp, one_mul]
  exact hle U
end GlobalTheory.SW
