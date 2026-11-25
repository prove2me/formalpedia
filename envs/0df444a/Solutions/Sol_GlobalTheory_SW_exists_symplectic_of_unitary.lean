-- Prove2me | solution 1 for GlobalTheory.SW.exists_symplectic_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:11:59.622599+00:00
-- url     : https://prove2.me/submissions/12770d0a-f778-4ab8-8247-ef8d23735b79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmField
import Theorems.Thm_GlobalTheory_SW_UniSp_transport
import Theorems.Thm_GlobalTheory_SW_UniSp_transport_sp
import Theorems.Thm_GlobalTheory_SW_UniSp_vecMul_bd
import Theorems.Thm_GlobalTheory_SW_UniSp_quad_bd
import Theorems.Thm_GlobalTheory_SW_UniSp_local_sp
import Theorems.Thm_GlobalTheory_SW_UniSp_local_den
import Theorems.Thm_GlobalTheory_SW_UniSp_local_num
import Theorems.Thm_GlobalTheory_SW_UniSp_local_quad
import Theorems.Thm_GlobalTheory_SW_UniSp_zeta_eq
import Theorems.Thm_GlobalTheory_SW_UniSp_tau_eq
import Theorems.Thm_GlobalTheory_SW_UniSp_exists_inv
import Theorems.Thm_GlobalTheory_SW_UniSp_qm_mul
import Theorems.Thm_GlobalTheory_SW_UniSp_qm_inj
import Theorems.Thm_GlobalTheory_SW_UniSp_qm_J
import Theorems.Thm_GlobalTheory_SW_UniSp_exists_blocks
import Theorems.Thm_GlobalTheory_SW_HAct_blocks
import Theorems.Thm_GlobalTheory_SW_HAct_group_part
import Theorems.Thm_GlobalTheory_SW_HAct_map_blocks
import Theorems.Thm_GlobalTheory_SW_HAct_map_ccT
import Theorems.Thm_GlobalTheory_SW_HAct_map_mem
import Theorems.Thm_GlobalTheory_SW_HAct_norm_det
import Theorems.Thm_GlobalTheory_SW_unitary_act_halfSpace
import Theorems.Thm_P2M_GlobalTheory_SW_HAct_den__act_d7a6623b371e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory.SW.UniSp GlobalTheory.SW.HAct Classical
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (γ : M2 E N), γ ∈ UU E N → ∃ σ ∈ Matrix.symplecticGroup (QI E N) ℚ, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ Z ∈ Hn Ψ N, spAct σ (tauOf Ψ Z) = tauOf Ψ (hAct Ψ γ Z) ∧ (spDen σ (tauOf Ψ Z)).det = c * ∏ τ, (hDen Ψ γ Z τ).det ^ 2 ∧ ∀ z z' : CM Ψ n N, (zetaOf Ψ (fun τ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) (fun τ => Matrix.of fun k => z' τ k ᵥ* (hDen Ψ γ Z τ)⁻¹) = fun k => zetaOf Ψ z z' k ᵥ* (spDen σ (tauOf Ψ Z))⁻¹) ∧ ∀ k, zetaOf Ψ z z' k ⬝ᵥ ((spDen σ (tauOf Ψ Z))⁻¹ * qm σ.toBlocks₂₁) *ᵥ zetaOf Ψ z z' k = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ ((hDen Ψ γ Z τ)⁻¹ * γ.toBlocks₂₁.map τ.1) *ᵥ z τ k := by
  intro E _ _ _ Ψ hΨ n N γ hγ
  obtain ⟨S', h1, h2⟩ := exists_inv (N := N) hΨ
  obtain ⟨σ, s1, s2, s3, s4⟩ := exists_blocks hΨ h1 h2 γ.toBlocks₁₁ γ.toBlocks₁₂ γ.toBlocks₂₁
    γ.toBlocks₂₂
  have hb := fun τ : Ψ => blocks (map_blocks τ.1 γ ▸ map_mem τ.1 hγ)
  have hb' : ∀ τ : Ψ, _ := fun τ : Ψ => by
    have h := map_mem τ.1 (group_part hγ).2.2.1
    rw [map_ccT, map_blocks τ.1 γ, fromBlocks_conjTranspose] at h
    have h' := blocks h
    simp only [conjTranspose_conjTranspose] at h'
    exact h'
  have one : ∀ {m : Type} [DecidableEq m],
      blockDiagonal (fun _ : Ψ => (1 : Matrix m m ℂ)) = 1 := fun {m} _ => blockDiagonal_one
  have add : ∀ {m : Type} (X Y : Ψ → Matrix m m ℂ),
      blockDiagonal X + blockDiagonal Y = blockDiagonal fun τ => X τ + Y τ :=
    fun X Y => (blockDiagonal_add X Y).symm
  have hl := fun τ : Ψ => local_sp (hb' τ).1 (hb' τ).2.1 (hb' τ).2.2.1 (hb' τ).2.2.2
  refine ⟨σ, ?_, ∏ τ : Ψ, (τ.1 γ.det)⁻¹, ?_, fun Z hZ => ?_⟩
  · rw [SymplecticGroup.mem_iff]
    apply qm_inj
    have e : qm σ = fromBlocks (qm σ.toBlocks₁₁) (qm σ.toBlocks₁₂) (qm σ.toBlocks₂₁)
        (qm σ.toBlocks₂₂) := by
      simp only [qm]
      rw [← fromBlocks_map, fromBlocks_toBlocks]
    rw [qm_mul, qm_mul, qm_J, show qm σᵀ = (qm σ)ᵀ from rfl, e, s1, s2, s3, s4]
    refine transport_sp h1 h2 ?_ ?_ ?_ ?_
    all_goals
      simp only [blockDiagonal_transpose, ← blockDiagonal_mul, ← one, add]
      congr 1
      funext τ
    exacts [(hl τ).1, (hl τ).2.1, (hl τ).2.2.1, (hl τ).2.2.2]
  · simp [norm_prod, norm_det _ hγ]
  obtain ⟨hA, -⟩ := (unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
  have hQ : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0 := fun τ => (hA τ).1
  have hP : ∀ τ, (hDen' Ψ γ Z τ).det ≠ 0 := fun τ h => hQ τ (by rw [← (hA τ).2.1, h, zero_mul])
  have hden : blockDiagonal (fun τ : Ψ => sw _ * dl (γ.toBlocks₂₁.map τ.1)) *
      blockDiagonal (fun τ => fromBlocks 0 (Z τ) (Z τ)ᵀ 0) +
      blockDiagonal (fun τ : Ψ => sw _ * dl (γ.toBlocks₂₂.map τ.1) * sw _) =
      blockDiagonal fun τ => fromBlocks (hDen' Ψ γ Z τ)ᵀ 0 0 (hDen Ψ γ Z τ) := by
    simp only [← blockDiagonal_mul, add, local_den]
    rfl
  obtain ⟨t1, t2, t3⟩ := transport h1 h2
    (a := blockDiagonal fun τ : Ψ => dl (γ.toBlocks₁₁.map τ.1))
    (b := blockDiagonal fun τ : Ψ => dl (γ.toBlocks₁₂.map τ.1) * sw _)
    (c := blockDiagonal fun τ : Ψ => sw _ * dl (γ.toBlocks₂₁.map τ.1))
    (d := blockDiagonal fun τ : Ψ => sw _ * dl (γ.toBlocks₂₂.map τ.1) * sw _)
    (T := blockDiagonal fun τ => fromBlocks 0 (Z τ) (Z τ)ᵀ 0)
    (W := blockDiagonal fun τ => fromBlocks 0 (hAct Ψ γ Z τ) (hAct Ψ γ Z τ)ᵀ 0)
    (Qi := blockDiagonal fun τ => fromBlocks ((hDen' Ψ γ Z τ)⁻¹)ᵀ 0 0 (hDen Ψ γ Z τ)⁻¹)
    (den := spDen σ (tauOf Ψ Z))
    (by
      rw [hden, ← blockDiagonal_mul, ← one]
      congr 1
      funext τ
      simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
        ← transpose_mul, nonsing_inv_mul _ (Ne.isUnit (hP τ)), mul_nonsing_inv _ (Ne.isUnit (hQ τ)),
        transpose_one, fromBlocks_one])
    (by
      simp only [← blockDiagonal_mul, add, local_num]
      congr 1
      funext τ
      have hd : hDen' Ψ γ Z τ * hAct Ψ γ Z τ = _ :=
        den'_act (hb τ).1 (hb τ).2.1 (hb τ).2.2.1 (hb τ).2.2.2 (hQ τ)
      simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
        ← transpose_mul, ← hd, nonsing_inv_mul_cancel_left _ _ (Ne.isUnit (hP τ))]
      rfl)
    (by rw [spDen, s3, s4, tau_eq])
  refine ⟨?_, ?_, fun z z' => ⟨?_, fun k => ?_⟩⟩
  · rw [spAct, s1, s2, tau_eq (hAct Ψ γ Z), ← t2, ← tau_eq]
  · rw [t1, hden, det_blockDiagonal, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have h0 : τ.1 γ.det ≠ 0 := fun h => by
      have := norm_det τ.1 hγ
      rw [h, norm_zero] at this
      exact zero_ne_one this
    rw [det_fromBlocks_zero₂₁, det_transpose, ← (hA τ).2.1]
    field_simp
  · funext k
    rw [zeta_eq, zeta_eq, (t3 _).1]
    congr 1
    funext ⟨i, τ⟩
    rw [vecMul_bd]
    change _ = (Sum.elim (z τ k) (z' τ k) ᵥ* fromBlocks _ _ _ _) i
    rw [vecMul_fromBlocks]
    rcases i with a | a <;> simp [vecMul_transpose]
  · rw [zeta_eq, s3, (t3 _).2, ← blockDiagonal_mul, quad_bd, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => local_quad (hb' τ).2.2.2 (hP τ) (hQ τ) (z τ k) (z' τ k)
end GlobalTheory.SW
