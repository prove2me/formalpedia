-- Prove2me | solution 1 for GlobalTheory.FrameNet.exists_net_card_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:54:24.497603+00:00
-- url     : https://prove2.me/submissions/5c8e659d-3afc-4658-8e25-392915c94195

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetMeetingFibres
import Theorems.Thm_GlobalTheory_FrameNet_exists_net_of_matrices
import Theorems.Thm_GlobalTheory_FrameNet_det_basisMat_ne_zero
import Theorems.Thm_GlobalTheory_FrameNet_det_gramMat_ne_zero
import Theorems.Thm_GlobalTheory_FrameNet_det_ne_zero_of_ortho
import Theorems.Thm_GlobalTheory_FrameNet_norm_det_coord
import Theorems.Thm_GlobalTheory_FrameNet_maj_eq_sum_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticCoefficientForms_card_Psi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticCoefficientForms_one_le_prod_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FrameNet
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace GlobalTheory.FrameNet
theorem _root_.solution (v : Fin r → Fin r → E) (hv : LinearIndependent E v)
    (hint : ∀ i k, IsIntegral ℤ (herm X.Gm (v i) (v k))) {B η : ℝ} (hB : 1 ≤ B) (hη0 : 0 < η)
    (hη : η ≤ 1) :
    ∃ N : Finset (Frame X.Ψ r), (N : Set (Frame X.Ψ r)) ⊆ shortFrames X v B ∧
      (∀ x ∈ shortFrames X v B, ∃ A : Frame X.Ψ r, rmul x A ∈ N ∧
        ∀ τ a b, ‖A τ a b - (if a = b then 1 else 0)‖ ≤ η) ∧
      (N.card : ℝ) ≤ (6 * (r : ℝ) ^ 2 / η * ((r : ℝ) * B) ^ r) ^ (2 * fdeg E * r ^ 2) := by
  classical
  have hcard : Fintype.card X.Ψ = fdeg E := ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi X
  have hdetG : (gramMat X.Gm v).det ≠ 0 := det_gramMat_ne_zero X hv
  have hmem : (gramMat X.Gm v).det ∈ integralClosure ℤ E := by
    rw [Matrix.det_apply]
    refine sum_mem fun σ _ => ?_
    rw [Units.smul_def]
    exact zsmul_mem (prod_mem fun i _ => hint (σ i) i) _
  have hint_det : IsIntegral ℤ (gramMat X.Gm v).det := hmem
  obtain ⟨D, hDdef⟩ : ∃ D : X.Ψ → ℝ, ∀ τ, D τ = Real.sqrt ‖τ.1 (gramMat X.Gm v).det‖ :=
    ⟨_, fun _ => rfl⟩
  have hD0 : ∀ τ, 0 < D τ := fun τ => by
    rw [hDdef]; exact Real.sqrt_pos.mpr (norm_pos_iff.mpr ((map_ne_zero _).mpr hdetG))
  have hD : 1 ≤ ∏ τ : X.Ψ, D τ := by
    have h1 := ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.one_le_prod_norm X _ hint_det hdetG
    have h2 : (∏ τ : X.Ψ, D τ) ^ 4 = ∏ τ : X.Ψ, ‖τ.1 (gramMat X.Gm v).det‖ ^ 2 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hDdef τ, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (norm_nonneg _)]
    rcases lt_or_ge (∏ τ : X.Ψ, D τ) 1 with hlt | hge
    swap
    · exact hge
    have h3 : (∏ τ : X.Ψ, D τ) ^ 4 < 1 :=
      pow_lt_one₀ (Finset.prod_nonneg fun τ _ => (hD0 τ).le) hlt (by norm_num)
    linarith
  have hm : ∀ x ∈ shortFrames X v B, ∀ (τ : X.Ψ) (i k : Fin r),
      ‖((mat x τ)⁻¹ * basisMat τ.1 v) i k‖ ^ 2 ≤ B := by
    intro x hx τ i k
    have ho : X.IsOrtho x := hx.1
    have hnn : ∀ σ : X.Ψ, 0 ≤ X.maj x σ (Data.emb σ.1 (v k)) := fun σ => by
      rw [maj_eq_sum_coord X ho σ v k]; exact Finset.sum_nonneg fun _ _ => by positivity
    calc ‖((mat x τ)⁻¹ * basisMat τ.1 v) i k‖ ^ 2
        ≤ ∑ i', ‖((mat x τ)⁻¹ * basisMat τ.1 v) i' k‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' => ‖((mat x τ)⁻¹ * basisMat τ.1 v) i' k‖ ^ 2)
            (fun _ _ => by positivity) (Finset.mem_univ i)
      _ = X.maj x τ (Data.emb τ.1 (v k)) := (maj_eq_sum_coord X ho τ v k).symm
      _ ≤ ∑ σ : X.Ψ, X.maj x σ (Data.emb σ.1 (v k)) :=
          Finset.single_le_sum (f := fun σ : X.Ψ => X.maj x σ (Data.emb σ.1 (v k)))
            (fun σ _ => hnn σ) (Finset.mem_univ τ)
      _ ≤ B := hx.2 k
  have hdet : ∀ x ∈ shortFrames X v B, ∀ τ : X.Ψ,
      ‖((mat x τ)⁻¹ * basisMat τ.1 v).det‖ = D τ := by
    intro x hx τ
    rw [hDdef]
    exact norm_det_coord X hx.1 τ v
  obtain ⟨N, hNO, hNcard, hNcov⟩ := exists_net_of_matrices (shortFrames X v B)
    (fun x τ => (mat x τ)⁻¹ * basisMat τ.1 v) D hD0 hD hB hη0 hη hm hdet
  refine ⟨N, hNO, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hyN, hxy⟩ := hNcov x hx
    have hy := hNO hyN
    let A : Frame X.Ψ r := fun τ => ((mat x τ)⁻¹ * mat y τ : Matrix (Fin r) (Fin r) ℂ)
    refine ⟨A, ?_, fun τ a b => ?_⟩
    · have hxy' : rmul x A = y := by
        funext τ
        have hdx : IsUnit (mat x τ).det :=
          isUnit_iff_ne_zero.mpr (det_ne_zero_of_ortho X hx.1 τ)
        show mat x τ * ((mat x τ)⁻¹ * mat y τ) = mat y τ
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdx, Matrix.one_mul]
      rw [hxy']
      exact hyN
    · have hdy : IsUnit (mat y τ).det := isUnit_iff_ne_zero.mpr (det_ne_zero_of_ortho X hy.1 τ)
      have hdV : IsUnit (basisMat τ.1 v).det :=
        isUnit_iff_ne_zero.mpr (det_basisMat_ne_zero τ.1 hv)
      have heq : (mat x τ)⁻¹ * basisMat τ.1 v * ((mat y τ)⁻¹ * basisMat τ.1 v)⁻¹ =
          (mat x τ)⁻¹ * mat y τ := by
        rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hdy, Matrix.mul_assoc,
          ← Matrix.mul_assoc (basisMat τ.1 v), Matrix.mul_nonsing_inv _ hdV, Matrix.one_mul]
      have h := hxy τ a b
      beta_reduce at h
      rw [heq] at h
      exact h
  · rw [← hcard]
    exact hNcard
end GlobalTheory.FrameNet
