-- Prove2me | solution 1 for GlobalTheory.LatL.exists_glO_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:25.751044+00:00
-- url     : https://prove2.me/submissions/b40e68d9-c35d-451c-a6cf-00a7845dac34

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormSubLeMaxUltra
import Theorems.Thm_P2M_GlobalTheory_LatL_norm_sub_le_max_ultra__b241ffa55670

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.LatL
namespace GlobalTheory.LatL
theorem _root_.solution {F : Type} [NormedField F] [IsUltrametricDist F] (r : ℕ)
    (v w : Fin (r + 1) → F) (hv : ∀ i, ‖v i‖ ≤ 1) (hw : ∀ i, ‖w i‖ ≤ 1) (hwv : w ⬝ᵥ v = 1) :
    ∃ k ∈ glO (r + 1) F, (k : Matrix _ _ F) *ᵥ Pi.single (Fin.last r) 1 = v ∧
      w ᵥ* (k : Matrix _ _ F) = Pi.single (Fin.last r) 1 := by
  classical
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i => ‖w i‖)
  have hw0 : w i₀ ≠ 0 := by
    intro h
    have : w = 0 := funext fun i => norm_le_zero_iff.mp (by simpa [h] using hi₀ i)
    simp [this] at hwv
  have hratio : ∀ i, ‖w i / w i₀‖ ≤ 1 := fun i => by
    rw [norm_div]; exact div_le_one_of_le₀ (hi₀ i) (norm_nonneg _)
  let s : Fin r → Fin (r + 1) := i₀.succAbove
  have hs : ∀ c, s c ≠ i₀ := fun c => Fin.succAbove_ne i₀ c
  let u : Fin r → Fin (r + 1) → F := fun c =>
    Pi.single (s c) 1 - (w (s c) / w i₀) • Pi.single i₀ 1
  let ρ : Fin r → Fin (r + 1) → F := fun c => Pi.single (s c) 1 - v (s c) • w
  let col : Fin (r + 1) → Fin (r + 1) → F := Fin.lastCases v u
  let row : Fin (r + 1) → Fin (r + 1) → F := Fin.lastCases w ρ
  let K : Matrix (Fin (r + 1)) (Fin (r + 1)) F := Matrix.of fun a b => col b a
  let L : Matrix (Fin (r + 1)) (Fin (r + 1)) F := Matrix.of fun a b => row a b
  have hwu : ∀ c, w ⬝ᵥ u c = 0 := by
    intro c
    simp only [u, dotProduct_sub, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one]
    field_simp; ring
  have hdot : ∀ a b, row a ⬝ᵥ col b = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) F) a b := by
    intro a b
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => simp [row, col, hwv]
      | cast c => simp [row, col, hwu, Matrix.one_apply, (Fin.castSucc_lt_last c).ne']
    | cast c =>
      induction b using Fin.lastCases with
      | last =>
        simp [row, col, ρ, sub_dotProduct, smul_dotProduct, single_dotProduct, hwv,
          Matrix.one_apply, (Fin.castSucc_lt_last c).ne]
      | cast c' =>
        simp only [row, col, Fin.lastCases_castSucc, ρ, sub_dotProduct, smul_dotProduct,
          single_dotProduct, hwu, smul_eq_mul, mul_zero, sub_zero, one_mul, u, Pi.sub_apply,
          Pi.smul_apply, Pi.single_apply, hs c, if_false, mul_zero, sub_zero, Matrix.one_apply,
          Fin.castSucc_inj]
        by_cases h : c = c'
        · subst h; simp
        · have : s c ≠ s c' := fun e => h (Fin.succAbove_right_injective e)
          simp [this, h]
  have hLK : L * K = 1 := by
    ext a b
    rw [← hdot a b]
    simp [L, K, Matrix.mul_apply, dotProduct]
  have hKL : K * L = 1 := mul_eq_one_comm.mp hLK
  let k : GL (Fin (r + 1)) F := ⟨K, L, hKL, hLK⟩
  have hsingle : ∀ i j : Fin (r + 1), ‖(Pi.single i (1 : F) : Fin (r + 1) → F) j‖ ≤ 1 := by
    intro i j; by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hcol : ∀ b a, ‖col b a‖ ≤ 1 := by
    intro b a
    induction b using Fin.lastCases with
    | last => simpa [col] using hv a
    | cast c =>
      simp only [col, Fin.lastCases_castSucc, u, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_sub_le_max_ultra' _ _).trans (max_le (hsingle _ _) ?_)
      rw [norm_mul]
      exact mul_le_one₀ (hratio _) (norm_nonneg _) (hsingle _ _)
  have hrow : ∀ a b, ‖row a b‖ ≤ 1 := by
    intro a b
    induction a using Fin.lastCases with
    | last => simpa [row] using hw b
    | cast c =>
      simp only [row, Fin.lastCases_castSucc, ρ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_sub_le_max_ultra' _ _).trans (max_le (hsingle _ _) ?_)
      rw [norm_mul]
      exact mul_le_one₀ (hv _) (norm_nonneg _) (hw _)
  refine ⟨k, fun i j => ⟨by simpa [k, K] using hcol j i, by simpa [k, L] using hrow i j⟩, ?_, ?_⟩
  · ext a
    simp [k, K, col, Matrix.mulVec_single]
  · ext b
    rw [show (w ᵥ* (k : Matrix _ _ F)) b = row (Fin.last r) ⬝ᵥ col b by
      simp [k, K, row, Matrix.vecMul, dotProduct]]
    rw [hdot, Matrix.one_apply, Pi.single_apply]
    simp only [eq_comm]
end GlobalTheory.LatL
