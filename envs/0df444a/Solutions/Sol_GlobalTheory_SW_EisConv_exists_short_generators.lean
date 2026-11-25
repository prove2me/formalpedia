-- Prove2me | solution 1 for GlobalTheory.SW.EisConv.exists_short_generators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:11:31.70929+00:00
-- url     : https://prove2.me/submissions/5c8f28b4-9822-4ec0-a558-a56b2e030bf2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorant
import Theorems.Thm_GlobalTheory_SW_EisConv_linearIndependent_bot
import Theorems.Thm_GlobalTheory_SW_EisConv_det_gram_bot
import Theorems.Thm_GlobalTheory_SW_EisConv_norm_embAll_sq_le
import Theorems.Thm_GlobalTheory_SW_EisConv_span_rows_mul
import Theorems.Thm_GlobalTheory_SW_exists_short_independent_rows
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisConv
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
namespace GlobalTheory.SW.EisConv
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (N c : ℕ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ γ ∈ UU E N, Den c γ → ∃ w : Fin N → (Fin N ⊕ Fin N → 𝓞 E),
      Submodule.span E (Set.range fun i j => (w i j : E)) = botSpan γ ∧ (∀ i, w i ≠ 0) ∧
      ∏ i, ‖embAll E _ (w i)‖ ^ Ψ.card ≤
        K * ∏ τ : Ψ, ‖(hDen Ψ γ (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ)) τ).det‖ := by
  obtain ⟨C, hC, H⟩ := exists_short_independent_rows E Ψ hΨ N
  refine ⟨√C * (c : ℝ) ^ (N * Ψ.card), by positivity, fun γ hγ hd => ?_⟩
  obtain ⟨a, hai, ha, hle⟩ := H _ _ (linearIndependent_bot hγ)
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have hca : ((c : E) • a).det ≠ 0 := by
    rw [det_smul]; exact mul_ne_zero (pow_ne_zero _ hcE) ha
  have hint : ∀ i j, IsIntegral ℤ ((((c : E) • a) * γ.submatrix Sum.inr id) i j) := fun i j => by
    rw [Matrix.smul_mul, ← Matrix.mul_smul, mul_apply]
    exact IsIntegral.sum _ fun k _ => (hai i k).mul (hd (Sum.inr k) j)
  set w : Fin N → (Fin N ⊕ Fin N → 𝓞 E) := fun i j => ⟨_, hint i j⟩ with hw
  have hwe : ∀ i j, (w i j : E) = (((c : E) • a) * γ.submatrix Sum.inr id) i j := fun _ _ => rfl
  refine ⟨w, span_rows_mul _ hca _, fun i hi => ?_, ?_⟩
  · have h1 : ((c : E) • a) i ᵥ* γ.submatrix Sum.inr id = 0 := by
      ext j
      have := hwe i j
      rw [hi] at this
      exact this.symm
    have h2 : ((c : E) • a) i = 0 :=
      vecMul_injective_iff.2 (linearIndependent_bot hγ) (h1.trans (zero_vecMul _).symm)
    exact hca (det_eq_zero_of_row_eq_zero i fun j => congrFun h2 j)
  · refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    simp only [det_gram_bot hγ] at hle
    have h1 : ∀ i, (‖embAll E _ (w i)‖ ^ Ψ.card) ^ 2 ≤ ((c : ℝ) ^ 2) ^ Ψ.card *
        (∑ τ : Ψ, ∑ j, ‖τ.1 ((a * γ.submatrix Sum.inr id) i j)‖ ^ 2) ^ Ψ.card := fun i => by
      rw [← pow_mul, mul_comm, pow_mul, ← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ((norm_embAll_sq_le hΨ _).trans (le_of_eq ?_)) _
      simp only [hwe, Finset.mul_sum, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul,
        map_natCast, norm_mul, norm_natCast, mul_pow]
    rw [← Finset.prod_pow]
    refine (Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => h1 i).trans ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (mul_le_mul_of_nonneg_left hle (by positivity)).trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt hC.le, Finset.prod_pow]
    simp only [hDen]
    ring
end GlobalTheory.SW.EisConv
