-- Prove2me | solution 1 for GlobalTheory.SW.EisBdd.eis_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:13:16.295461+00:00
-- url     : https://prove2.me/submissions/1181c6ff-ffbc-4aeb-9134-84694d87bda0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LinearIndependentMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBounded
import Theorems.Thm_GlobalTheory_SW_EisBdd_approx_herm
import Theorems.Thm_GlobalTheory_SW_EisBdd_imH_sub
import Theorems.Thm_GlobalTheory_SW_EisBdd_mem_Hn
import Theorems.Thm_GlobalTheory_SW_EisBdd_transl_mem
import Theorems.Thm_GlobalTheory_SW_EisBdd_botSpan_mul
import Theorems.Thm_GlobalTheory_SW_EisBdd_pair
import Theorems.Thm_GlobalTheory_SW_Base_ccT_map
import Theorems.Thm_GlobalTheory_SW_Base_mem_stdL
import Theorems.Thm_GlobalTheory_SW_Base_stdL_mem_Vset
import Theorems.Thm_GlobalTheory_SW_HAct_mul_blocks
import Theorems.Thm_GlobalTheory_SW_HAct_mul_mem
import Theorems.Thm_GlobalTheory_SW_LagRep_exists_rep_den
import Theorems.Thm_GlobalTheory_SW_Model_mem_stdL
import Theorems.Thm_GlobalTheory_SW_Model_stdL_mem_Vset
import Theorems.Thm_GlobalTheory_SW_TransComp_key
import Theorems.Thm_GlobalTheory_SW_norm_det_denom_compare
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_T_hermitianWeilAction_siegelParabolic_explicit
import Theorems.Thm_GlobalTheory_T_summable_prod_inv_norm_det_hDen_pow
import Theorems.Thm_GlobalTheory_T_weil_action_level_supNorm_uniform_in_lattice
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisBdd
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.EisBdd
theorem _root_.solution (hΨ : IsType Ψ) (hn : Even n) (hN : 4 * N < n) {R : ℕ} {δ : ℝ} (hR : 0 < R)
    (hδ : 0 < δ) : ∃ C : ℝ, ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, HasLevel R φ → ∀ B : ℝ,
      (∀ x, ‖φ x‖ ≤ B) → ∀ Z ∈ HnGe Ψ N δ,
      (Summable fun U : Lag E N => ‖eisTerm Ψ U.2.choose φ Z 0 0‖) ∧ ‖eis Ψ φ Z 0 0‖ ≤ C * B := by
  obtain ⟨c, hc, hrep⟩ := LagRep.exists_rep_den E N
  choose rep hU hD hS using hrep
  have hm := GlobalTheory.T.summable_prod_inv_norm_det_hDen_pow E Ψ hΨ n N hN c rep hc fun U => ⟨hU U, hD U, hS U⟩
  set m : Lag E N → ℝ := fun U => ∏ τ : Ψ,
    (‖(hDen Ψ (rep U) (fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ)) τ).det‖ ^ n)⁻¹ with hmd
  have hm0 : ∀ U, 0 ≤ m U := fun U => Finset.prod_nonneg fun _ _ => by positivity
  obtain ⟨K, hK⟩ := approx_herm (N := N) hΨ
  obtain ⟨κ, hκ, hcomp⟩ := norm_det_denom_compare N δ K hδ
  obtain ⟨R', C, -, hC⟩ := GlobalTheory.T.weil_action_level_supNorm_uniform_in_lattice E Ψ hΨ n N hn c R hc hR
  set L : ℝ := |C| * ∏ _τ : Ψ, (κ ^ n)⁻¹ with hL
  have hL0 : 0 ≤ L := mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun _ _ => by positivity)
  refine ⟨L * ∑' U, m U, fun φ hφ B hB Z hZ => ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨β, hβ, hβi, hβK⟩ := hK Z
  have hβ' : ccT (-β) = -β := by
    conv_rhs => rw [← hβ]
    ext i j; simp [ccT, cc]
  have ht := transl_mem hβ
  have ht' := transl_mem hβ'
  have htt : (fromBlocks 1 β 0 1 : M2 E N) * fromBlocks 1 (-β) 0 1 = 1 := by
    rw [fromBlocks_multiply]; simp
  let σ : Lag E N → Lag E N := fun U =>
    ⟨botSpan (rep U * fromBlocks 1 β 0 1), _, HAct.mul_mem ht (hU U), rfl⟩
  have hσ : ∀ U, botSpan (rep (σ U) * fromBlocks 1 (-β) 0 1) = U.1 := fun U => by
    rw [botSpan_mul, hS]
    change (botSpan (rep U * fromBlocks 1 β 0 1)).map _ = _
    rw [← botSpan_mul, Matrix.mul_assoc, htt, Matrix.mul_one, hS]
  have hinj : Function.Injective σ := fun U V h => Subtype.ext (by rw [← hσ U, h, hσ])
  have hlev : LevelL (stdL E n) R φ :=
    ⟨fun x hx a => (Base.mem_stdL _).2 fun k => hφ.1 x hx k a,
      fun x y hy => hφ.2 x y fun k a => (Base.mem_stdL _).1 (hy a) k⟩
  have key : ∀ U : Lag E N, ‖eisTerm Ψ U.2.choose φ Z 0 0‖ ≤ L * B * m (σ U) := fun U => by
    have hγ := HAct.mul_mem ht' (hU (σ U))
    rw [(GlobalTheory.T.hermitianWeilAction_siegelParabolic_explicit E Ψ hΨ n N hn φ ⟨R, hR, hφ⟩).2 _ U.2.choose_spec.1 _ hγ
      (U.2.choose_spec.2.trans (hσ U).symm) Z (mem_Hn hδ hZ)]
    have hden : Den c (rep (σ U) * fromBlocks 1 (-β) 0 1) := by
      intro i j
      rw [← Matrix.smul_mul, Matrix.mul_apply]
      refine IsIntegral.sum _ fun k _ => (hD _ i k).mul ?_
      rcases k with k | k <;> rcases j with j | j
      · by_cases h : k = j <;> simp [h, isIntegral_one, isIntegral_zero]
      · exact (hβi k j).neg
      · exact isIntegral_zero
      · by_cases h : k = j <;> simp [h, isIntegral_one, isIntegral_zero]
    have h1 := (hC 1 _ (Base.stdL_mem_Vset n 1) _ hγ hden φ hlev).2.2 B hB 0
    have h2 : ‖(hFac Ψ (rep (σ U) * fromBlocks 1 (-β) 0 1) Z (0 : CM Ψ n N) 0)⁻¹‖ ≤
        (∏ _τ : Ψ, (κ ^ n)⁻¹) * m (σ U) := by
      have h0 : ∀ (τ : Ψ) (k : Fin n), (0 : CM Ψ n N) τ k = 0 := fun _ _ => rfl
      simp only [hFac, h0, zero_dotProduct, Finset.sum_const_zero, mul_zero, Complex.exp_zero,
        mul_one, hmd]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, norm_prod]
      refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => ?_
      obtain ⟨p1, p2, p3⟩ := pair (hU (σ U)) τ
      have hb : (β.map τ.1)ᴴ = β.map τ.1 := by rw [← Base.ccT_map, hβ]
      have h3 := (hcomp _ _ (Z τ - β.map τ.1) p1 p2
        (by rw [imH_sub, imH, imH, hb, sub_self, smul_zero, sub_zero]; exact hZ τ) (hβK τ)).1
      have h4 : hDen Ψ (rep (σ U) * fromBlocks 1 (-β) 0 1) Z τ =
          (rep (σ U)).toBlocks₂₁.map τ.1 * (Z τ - β.map τ.1) + (rep (σ U)).toBlocks₂₂.map τ.1 := by
        obtain ⟨-, -, m3, m4⟩ := HAct.mul_blocks τ.1 (fromBlocks 1 (-β) 0 1) (rep (σ U))
        rw [hDen, m3, m4]
        simp [Matrix.map_neg, Matrix.mul_sub]
        abel
      rw [h4, norm_inv, norm_pow, ← mul_inv, ← mul_pow]
      have p4 := norm_pos_iff.2 p3
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h3 n)
    rw [eisTerm, norm_mul]
    calc _ ≤ (|C| * B) * ((∏ _τ : Ψ, (κ ^ n)⁻¹) * m (σ U)) :=
          mul_le_mul (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hB0)) h2
            (norm_nonneg _) (by positivity)
      _ = _ := by rw [hL]; ring
  have hs : Summable fun U => L * B * m (σ U) := (hm.comp_injective hinj).mul_left _
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) key hs, ?_⟩
  refine (tsum_of_norm_bounded hs.hasSum key).trans ?_
  rw [tsum_mul_left, mul_right_comm L _ B]
  exact mul_le_mul_of_nonneg_left (_root_.tsum_comp_le_tsum_of_inj hm hm0 hinj) (by positivity)
end GlobalTheory.SW.EisBdd
