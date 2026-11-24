-- Prove2me | solution 1 for GlobalTheory.RealWeil.GaussPairing.lam_mu_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:19.561609+00:00
-- url     : https://prove2.me/submissions/4b590f7a-7b07-47bd-be6d-b943baf698cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HalfAddSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralComplexGaussianPosDefHermitianPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingOfNormSqEqSumComplexCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThree
import Theorems.Thm_GlobalTheory_RealWeil_GaussPairing_norm_sq_eq_dot
import Theorems.Thm_GlobalTheory_RealWeil_GaussPairing_inner_eq_dot
import Theorems.Thm_GlobalTheory_RealWeil_GaussPairing_star_mulVec_dot
import Theorems.Thm_GlobalTheory_RealWeil_GaussPairing_posDef_one_add
import Theorems.Thm_GlobalTheory_RealWeil_GaussPairing_integral_sum_elim
import Theorems.Thm_GlobalTheory_RealWeil_PosDet_detPlus_identities
import Theorems.Thm_GlobalTheory_RealWeil_PosDet_half_add_self
import Theorems.Thm_GlobalTheory_T_integral_complexGaussian_posDef_hermitian_part
import Theorems.Thm_GlobalTheory_measurePreserving_of_norm_sq_eq_sum_complex_coords

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
namespace GlobalTheory.RealWeil.GaussPairing
section Coord
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type} [Fintype ι]
end Coord
private lemma half_smul_add_conjTranspose_eq_of_hermitian {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (hX : Xᴴ = X) :
    (1 / 2 : ℂ) • X + ((1 / 2 : ℂ) • X)ᴴ = X := by
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [Complex.star_def, map_div₀, map_one, map_ofNat]
  rw [conjTranspose_smul, hX, h2, ← smul_add, GlobalTheory.RealWeil.PosDet.half_add_self]
private lemma half_cross_add_conjTranspose_eq_mul {ι : Type} [Fintype ι] [DecidableEq ι] (s a b : Matrix ι ι ℂ) (hs : sᴴ = s) :
    (1 / 2 : ℂ) • (aᴴ * (1 + s) * b) + ((1 / 2 : ℂ) • (bᴴ * (1 - s) * a))ᴴ = 0 + aᴴ * b := by
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [Complex.star_def, map_div₀, map_one, map_ofNat]
  rw [conjTranspose_smul, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_sub, conjTranspose_one, hs, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, zero_add]
  module
private lemma half_cross_add_conjTranspose_eq_mul_swap {ι : Type} [Fintype ι] [DecidableEq ι] (s a b : Matrix ι ι ℂ) (hs : sᴴ = s) :
    (1 / 2 : ℂ) • (bᴴ * (1 - s) * a) + ((1 / 2 : ℂ) • (aᴴ * (1 + s) * b))ᴴ = 0 + bᴴ * a := by
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [Complex.star_def, map_div₀, map_one, map_ofNat]
  rw [conjTranspose_smul, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_add, conjTranspose_one, hs, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, zero_add]
  module
end GlobalTheory.RealWeil.GaussPairing
end

set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.GaussPairing
namespace GlobalTheory.RealWeil.GaussPairing
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (ι : Type) [Fintype ι] [DecidableEq ι] (e : V ≃L[ℝ] (ι → ℂ)), (∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) → ∀ (s : Matrix ι ι ℂ), sᴴ = s → s * s = 1 → ∀ J : V ≃ₗᵢ[ℝ] V, (∀ v, e (J v) = I • s *ᵥ e v) → (∀ (g : Matrix ι ι ℂ) (k : V → V), gᴴ * s * g = s → (∀ v, e (k v) = g *ᵥ e v) → dP s g ≠ 0 ∧ dP s g⁻¹ = star (dP s g) ∧ lam k = (dP s g * dP s g⁻¹)⁻¹) ∧ ∀ (g₁ g₂ : Matrix ι ι ℂ) (k₁ k₂ : V → V), g₁ᴴ * s * g₁ = s → g₂ᴴ * s * g₂ = s → (∀ v, e (k₁ v) = g₁ *ᵥ e v) → (∀ v, e (k₂ v) = g₂ *ᵥ e v) → mu J k₁ k₂ = (dP s g₁⁻¹ * dP s g₂ * dP s (g₂⁻¹ * g₁))⁻¹ := by
  intro V _ _ _ _ _ ι _ _ e he s hs hss J hJ
  have hmp := GlobalTheory.measurePreserving_of_norm_sq_eq_sum_complex_coords V ι e he
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  obtain ⟨hd1, hd2⟩ := GlobalTheory.RealWeil.PosDet.detPlus_identities ι s hs hss
  have hHerm : ∀ g : Matrix ι ι ℂ, (1 + gᴴ * g)ᴴ = 1 + gᴴ * g := fun g => by
    rw [conjTranspose_add, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose]
  refine ⟨fun g k hg hk => ?_, fun g₁ g₂ k₁ k₂ hg₁ hg₂ hk₁ hk₂ => ?_⟩
  · obtain ⟨A, hA⟩ : ∃ A : Matrix ι ι ℂ, A = (1 / 2 : ℂ) • (1 + gᴴ * g) := ⟨_, rfl⟩
    have hAA : A + Aᴴ = 1 + gᴴ * g := by rw [hA]; exact half_smul_add_conjTranspose_eq_of_hermitian _ (hHerm g)
    obtain ⟨hA0, -, hAint⟩ := GlobalTheory.T.integral_complexGaussian_posDef_hermitian_part ι A (by rw [hAA]; exact posDef_one_add g)
    obtain ⟨hstar, hdet⟩ := hd1 g hg
    rw [← hA] at hdet
    have hpt : ∀ u, gau u * gau (k u) = cexp (-(π : ℂ) * (star (e u) ⬝ᵥ A *ᵥ e u)) := by
      intro u
      simp only [gau, ← Complex.exp_add]
      congr 1
      rw [norm_sq_eq_dot e he u, norm_sq_eq_dot e he (k u), hk u, star_mulVec_dot, hA, smul_mulVec,
        dotProduct_smul, add_mulVec, one_mulVec, ← mulVec_mulVec, dotProduct_add, smul_eq_mul]
      ring
    have hlam : lam k = A.det⁻¹ :=
      calc lam k = ∫ u, cexp (-(π : ℂ) * (star (e u) ⬝ᵥ A *ᵥ e u)) := by
            unfold lam
            congr 1
            funext u
            exact hpt u
        _ = ∫ z, cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) :=
            hmp.integral_comp hme (fun z => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)))
        _ = A.det⁻¹ := hAint
    refine ⟨fun h0 => hA0 (by rw [hdet, h0, zero_mul]), hstar, ?_⟩
    rw [hlam, hdet]
  · obtain ⟨M, hM⟩ : ∃ M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ, M =
        fromBlocks ((1 / 2 : ℂ) • (1 + g₁ᴴ * g₁)) ((1 / 2 : ℂ) • (g₁ᴴ * (1 + s) * g₂))
          ((1 / 2 : ℂ) • (g₂ᴴ * (1 - s) * g₁)) ((1 / 2 : ℂ) • (1 + g₂ᴴ * g₂)) := ⟨_, rfl⟩
    have hdet2 := hd2 g₁ g₂ hg₁ hg₂
    rw [← hM] at hdet2
    have hMM : M + Mᴴ = 1 + (fromCols g₁ g₂)ᴴ * fromCols g₁ g₂ := by
      rw [hM, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols,
        fromBlocks_conjTranspose, fromBlocks_add, ← fromBlocks_one, fromBlocks_add,
        half_smul_add_conjTranspose_eq_of_hermitian _ (hHerm g₁), half_smul_add_conjTranspose_eq_of_hermitian _ (hHerm g₂), half_cross_add_conjTranspose_eq_mul s g₁ g₂ hs,
        half_cross_add_conjTranspose_eq_mul_swap s g₁ g₂ hs]
    obtain ⟨-, hMi, hMint⟩ := GlobalTheory.T.integral_complexGaussian_posDef_hermitian_part (ι ⊕ ι) M (by rw [hMM]; exact posDef_one_add _)
    have hpt : ∀ u v, gau u * gau v * (cexp (π * I * (omJ J (k₁ u) (k₂ v) : ℂ)) * gau (k₁ u + k₂ v)) =
        cexp (-(π : ℂ) * (star (Sum.elim (e u) (e v)) ⬝ᵥ M *ᵥ Sum.elim (e u) (e v))) := by
      intro u v
      simp only [gau, ← Complex.exp_add]
      congr 1
      have hsum : star (Sum.elim (e u) (e v)) = Sum.elim (star (e u)) (star (e v)) := by
        funext i
        cases i <;> rfl
      have hA1 : ∀ (g : Matrix ι ι ℂ) (z : ι → ℂ),
          star z ⬝ᵥ ((1 / 2 : ℂ) • (1 + gᴴ * g)) *ᵥ z = 1 / 2 * (star z ⬝ᵥ z + star (g *ᵥ z) ⬝ᵥ g *ᵥ z) := by
        intro g z
        rw [smul_mulVec, dotProduct_smul, add_mulVec, one_mulVec, ← mulVec_mulVec, dotProduct_add,
          ← star_mulVec_dot, smul_eq_mul]
      have hB1 : star (e u) ⬝ᵥ ((1 / 2 : ℂ) • (g₁ᴴ * (1 + s) * g₂)) *ᵥ e v =
          1 / 2 * (star (g₁ *ᵥ e u) ⬝ᵥ g₂ *ᵥ e v + star (g₁ *ᵥ e u) ⬝ᵥ s *ᵥ (g₂ *ᵥ e v)) := by
        rw [smul_mulVec, dotProduct_smul, ← mulVec_mulVec, ← mulVec_mulVec, ← star_mulVec_dot,
          add_mulVec, one_mulVec, dotProduct_add, smul_eq_mul]
      have hC1 : star (e v) ⬝ᵥ ((1 / 2 : ℂ) • (g₂ᴴ * (1 - s) * g₁)) *ᵥ e u =
          1 / 2 * (star (g₂ *ᵥ e v) ⬝ᵥ g₁ *ᵥ e u - star (g₂ *ᵥ e v) ⬝ᵥ s *ᵥ (g₁ *ᵥ e u)) := by
        rw [smul_mulVec, dotProduct_smul, ← mulVec_mulVec, ← mulVec_mulVec, ← star_mulVec_dot,
          sub_mulVec, one_mulVec, dotProduct_sub, smul_eq_mul]
      have hJ1 : star (g₁ *ᵥ e u) ⬝ᵥ I • s *ᵥ (g₂ *ᵥ e v) = I * (star (g₁ *ᵥ e u) ⬝ᵥ s *ᵥ (g₂ *ᵥ e v)) := by
        rw [dotProduct_smul, smul_eq_mul]
      have hJ2 : star (I • s *ᵥ (g₂ *ᵥ e v)) ⬝ᵥ g₁ *ᵥ e u =
          -I * (star (g₂ *ᵥ e v) ⬝ᵥ s *ᵥ (g₁ *ᵥ e u)) := by
        rw [star_smul, smul_dotProduct, star_mulVec_dot, hs, smul_eq_mul, Complex.star_def, Complex.conj_I]
      have hN : star (g₁ *ᵥ e u + g₂ *ᵥ e v) ⬝ᵥ (g₁ *ᵥ e u + g₂ *ᵥ e v) =
          star (g₁ *ᵥ e u) ⬝ᵥ g₁ *ᵥ e u + star (g₁ *ᵥ e u) ⬝ᵥ g₂ *ᵥ e v +
            (star (g₂ *ᵥ e v) ⬝ᵥ g₁ *ᵥ e u + star (g₂ *ᵥ e v) ⬝ᵥ g₂ *ᵥ e v) := by
        rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add]
      unfold omJ
      rw [inner_eq_dot e he, hJ, norm_sq_eq_dot e he u, norm_sq_eq_dot e he v,
        norm_sq_eq_dot e he (k₁ u + k₂ v), map_add, hk₁, hk₂, hJ1, hJ2, hN, hM, hsum, fromBlocks_mulVec,
        sumElim_dotProduct_sumElim]
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, dotProduct_add]
      rw [hA1, hA1, hB1, hC1]
      linear_combination ((π : ℂ) / 2 * (star (g₁ *ᵥ e u) ⬝ᵥ s *ᵥ (g₂ *ᵥ e v) -
        star (g₂ *ᵥ e v) ⬝ᵥ s *ᵥ (g₁ *ᵥ e u))) * Complex.I_sq
    calc mu J k₁ k₂ = ∫ u, ∫ v, cexp (-(π : ℂ) * (star (Sum.elim (e u) (e v)) ⬝ᵥ M *ᵥ Sum.elim (e u) (e v))) := by
          unfold mu
          congr 1
          funext u
          congr 1
          funext v
          exact hpt u v
      _ = ∫ u, ∫ w, cexp (-(π : ℂ) * (star (Sum.elim (e u) w) ⬝ᵥ M *ᵥ Sum.elim (e u) w)) := by
          congr 1
          funext u
          exact hmp.integral_comp hme (fun w => cexp (-(π : ℂ) * (star (Sum.elim (e u) w) ⬝ᵥ M *ᵥ Sum.elim (e u) w)))
      _ = ∫ z, ∫ w, cexp (-(π : ℂ) * (star (Sum.elim z w) ⬝ᵥ M *ᵥ Sum.elim z w)) :=
          hmp.integral_comp hme (fun z => ∫ w, cexp (-(π : ℂ) * (star (Sum.elim z w) ⬝ᵥ M *ᵥ Sum.elim z w)))
      _ = ∫ x, cexp (-(π : ℂ) * (star x ⬝ᵥ M *ᵥ x)) := integral_sum_elim _ hMi
      _ = M.det⁻¹ := hMint
      _ = (dP s g₁⁻¹ * dP s g₂ * dP s (g₂⁻¹ * g₁))⁻¹ := by rw [hdet2]
end GlobalTheory.RealWeil.GaussPairing
