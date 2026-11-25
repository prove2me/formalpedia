-- Prove2me | solution 1 for GlobalTheory.SW.shortIso_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:41:55.103096+00:00
-- url     : https://prove2.me/submissions/a8f7374d-c015-493b-95eb-c46afc139f85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
import Theorems.Thm_GlobalTheory_SW_ShortStep_quot_maj
import Theorems.Thm_GlobalTheory_SW_ShortStep_exists_close
import Theorems.Thm_GlobalTheory_SW_ShortStep_quot_iso
import Theorems.Thm_GlobalTheory_SW_ShortStep_exists_dual
import Theorems.Thm_GlobalTheory_SW_ShortStep_exists_compl
import Theorems.Thm_GlobalTheory_SW_ShortStep_map_conj
import Theorems.Thm_GlobalTheory_SW_ShortStep_det_map_ne
import Theorems.Thm_GlobalTheory_SW_ShortStep_map_proj
import Theorems.Thm_GlobalTheory_SW_ShortStep_iso_of_short
import Theorems.Thm_GlobalTheory_SW_ShortStep_lift_le
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_comb_le
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_fac
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_hval_eq
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_intM_mul
import Theorems.Thm_GlobalTheory_SW_RowExt_ccT_eq
import Theorems.Thm_GlobalTheory_SW_RowExt_exists_right_inv
import Theorems.Thm_GlobalTheory_SW_RowExt_intM_mul
import Theorems.Thm_GlobalTheory_SW_exists_nearly_primitive
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory.SW.MinkowskiProductBounds GlobalTheory.SW.ShortStep
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N : ℕ, (∀ D : ℕ, 0 < D → ∃ C : ℝ, ShortIso Ψ N D 0 C) → (∀ (D : ℕ) (ε : ℝ), 0 < D → 0 < ε → ∃ C : ℝ, ShortIso Ψ (N + 1) D ε C) → ∀ D : ℕ, 0 < D → ∃ C : ℝ, ShortIso Ψ (N + 1) D 0 C := by
  intro E _ _ _ Ψ h N ih hth D hD
  classical
  obtain ⟨C₀, hC₀⟩ := hth D (1 / D) hD (by positivity)
  obtain ⟨c, C₁, hc, hprim⟩ := exists_nearly_primitive E 1
  obtain ⟨D', hD', hcompl⟩ := exists_compl (E := E) (2 * N) D (D * c * D * (D * c) * 2) hD
    (by positivity)
  obtain ⟨C₂, hC₂⟩ := ih D' hD'
  obtain ⟨C₃, hC₃⟩ := exists_close h
  set C₄ := max (((1 : ℕ) * (C₁ * √(1 / D))) ^ 2) C₂ with hC₄
  refine ⟨max (max C₀ C₄) ((2 * (max 1 C₃ * √C₄)) ^ 2),
    fun G H hG h0 hD1 hD2 ⟨W, hW⟩ hH _ => ?_⟩
  by_cases hmin : ∀ v : Fin (2 * (N + 1)) → E, v ≠ 0 → (∀ a, IsIntegral ℤ (v a)) →
      1 / (D : ℝ) ≤ ∑ τ, hval Ψ H τ v
  · obtain ⟨W', h1, h2, h3⟩ := hC₀ G H hG h0 hD1 hD2 ⟨W, hW⟩ hH hmin
    exact ⟨W', h1, h2, fun i τ => (h3 i τ).trans ((le_max_left _ _).trans (le_max_left _ _))⟩
  push Not at hmin
  obtain ⟨v, hv0, hvi, hvs⟩ := hmin
  have hG' : Gᴴ = G := hG
  have hnn : ∀ {k : ℕ} {K : CM Ψ k k}, (∀ τ, (K τ).PosDef) → ∀ τ x, 0 ≤ hval Ψ K τ x := by
    intro k K hK τ x
    obtain ⟨B, -, -, h3⟩ := fac (hK τ)
    rw [hval_eq, h3]; positivity
  let V₀ : Matrix (Fin 1) (Fin (2 * (N + 1))) E := Matrix.of fun _ => v
  have hs : ∀ τ, hval Ψ H τ (V₀ 0) < 1 / D := fun τ =>
    (Finset.single_le_sum (f := fun τ => hval Ψ H τ v)
      (fun τ _ => hnn (fun τ => (hH τ).1) τ v) (Finset.mem_univ τ)).trans_lt hvs
  have hV₀ := iso_of_short h hD hG' h0 hD1 hH (V := V₀) (fun _ a => hvi a) hs
  obtain ⟨a, ha, haC, hVi, hpr⟩ := hprim _ V₀ (fun _ a => hvi a)
    (linearIndependent_unique_iff.2 hv0)
  have hV : a * V₀ * G * (a * V₀)ᴴ = 0 := by
    rw [conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc a, Matrix.mul_assoc a, hV₀]; simp
  have hVne : (a * V₀) 0 ≠ 0 := by
    rw [det_fin_one] at ha
    have : (a * V₀) 0 = a 0 0 • v := by ext j; simp [Matrix.mul_apply, V₀]
    rw [this]
    exact smul_ne_zero ha hv0
  have hVC : ∀ τ, hval Ψ H τ ((a * V₀) 0) ≤ C₄ := fun τ => by
    have h1 : (fun j => τ.1 ((a * V₀) 0 j)) = ∑ j, τ.1 (a 0 j) • fun b => τ.1 (V₀ j b) := by
      ext j
      simp [Matrix.mul_apply]
    rw [hval_eq, h1]
    exact (comb_le (hH τ).1 _ _ (fun j => (hs τ).le) fun j => haC _ _ _).trans (le_max_left _ _)
  generalize a * V₀ = V at hVi hpr hV hVne hVC
  obtain ⟨X, hX, hVX⟩ := RowExt.exists_right_inv (c : E) V hVi
    (linearIndependent_unique_iff.2 hVne) hpr
  obtain ⟨w, hw, w1, w2, w3⟩ := exists_dual hc hG' h0 hD1 hD2 hVi hX hVX hV
  obtain ⟨B, S, hBi, hVS, hBS, hBV, hSB, hd, d1, d2⟩ :=
    hcompl _ G V w (by ring) hG' h0 hD1 hD2 hVi hw hV w1 w2 w3
  have hq := fun τ : Ψ => quot_maj (G := G.map τ.1) (H := H τ) (V := V.map τ.1) (w := w.map τ.1)
    (B := B.map τ.1) (S := S.map τ.1) (by rw [← map_conj, hG']) (det_map_ne τ.1 h0) (hH τ).1
    (hH τ).2
    (by rw [← map_conj, ← Matrix.map_mul, ← Matrix.map_mul, w1,
      Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [← map_conj, ← Matrix.map_mul, ← Matrix.map_mul, hV, Matrix.map_zero _ (map_zero _)])
    (by rw [← map_conj, ← Matrix.map_mul, ← Matrix.map_mul, hBV, Matrix.map_zero _ (map_zero _)])
    (by rw [← Matrix.map_mul, hSB, map_proj])
    (by rw [← map_conj, ← Matrix.map_mul, ← Matrix.map_mul]; exact det_map_ne τ.1 hd)
  choose L hL1 hL2 using hq
  obtain ⟨T, hTi, ⟨hT1, hT2⟩, hTC⟩ := hC₂ (B * G * Bᴴ)
    (fun τ => (B.map τ.1 - L τ * V.map τ.1) * H τ * (B.map τ.1 - L τ * V.map τ.1)ᴴ)
    (by
      rw [RowExt.ccT_eq, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG',
        Matrix.mul_assoc])
    hd d1 d2 (quot_iso hG' hV hBV hSB hW)
    (fun τ => ⟨hL1 τ, by rw [Matrix.map_mul, Matrix.map_mul, map_conj]; exact hL2 τ⟩)
    (fun x _ _ => Finset.sum_nonneg fun τ _ => hnn hL1 τ x)
  choose α hα hαC using fun i => hC₃ fun τ => ((fun j => τ.1 (T i j)) ᵥ* L τ) 0
  let T' : Matrix (Fin (N + 1)) (Fin (2 * N)) E := Matrix.of (Fin.cons 0 fun i => T i)
  let A : Matrix (Fin (N + 1)) (Fin 1) E := Matrix.of (Fin.cons 1 fun i _ => α i)
  have r0 : (T' * B + A * V) 0 = V 0 := by
    ext j; simp [T', A, Matrix.mul_apply]
  have r1 : ∀ i : Fin N, (T' * B + A * V) i.succ = T i ᵥ* B + α i • V 0 := fun i => by
    ext j; simp [T', A, Matrix.mul_apply, vecMul, dotProduct]
  refine ⟨T' * B + A * V, fun i j => ?_, ⟨?_, ?_⟩, fun i τ => ?_⟩
  · refine (intM_mul (A := T') (fun i j => ?_) hBi i j).add
      (intM_mul (A := A) (fun i j => ?_) hVi i j)
    · cases i using Fin.cases
      · exact isIntegral_zero
      · exact hTi _ _
    · cases i using Fin.cases
      · exact isIntegral_one
      · exact hα _
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_succ, r0] at hg
    simp only [r1] at hg
    have hVS' : V 0 ᵥ* S = 0 := congrFun hVS 0
    have h1 := congrArg (fun x => x ᵥ* S) hg
    simp only [add_vecMul, sum_vecMul, smul_vecMul, vecMul_vecMul, hBS, hVS', vecMul_one,
      smul_zero, add_zero, zero_add, zero_vecMul] at h1
    have h2 := Fintype.linearIndependent_iff.1 hT1 _ h1
    simp only [h2, zero_smul, Finset.sum_const_zero, add_zero] at hg
    intro i
    cases i using Fin.cases
    · exact (smul_eq_zero.1 hg).resolve_right hVne
    · exact h2 _
  · have hVB : V * G * Bᴴ = 0 := by
      simpa [conjTranspose_mul, hG', Matrix.mul_assoc] using congrArg conjTranspose hBV
    have h1 : T' * (B * G * Bᴴ) * T'ᴴ = 0 := by
      generalize B * G * Bᴴ = G' at hT2
      ext i j
      cases i using Fin.cases
      · simp [T', Matrix.mul_apply]
      cases j using Fin.cases
      · simp [T', Matrix.mul_apply]
      · exact congrFun (congrFun hT2 _) _
    have h2 : (T' * B + A * V) * G * (T' * B + A * V)ᴴ = T' * (B * G * Bᴴ) * T'ᴴ +
        T' * (B * G * Vᴴ) * Aᴴ + A * (V * G * Bᴴ) * T'ᴴ + A * (V * G * Vᴴ) * Aᴴ := by
      simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add,
        Matrix.mul_assoc]
      abel
    refine h2.trans ?_
    rw [h1, hBV, hVB, hV]; simp
  · cases i using Fin.cases with
    | zero => rw [r0]; exact (hVC τ).trans ((le_max_right _ _).trans (le_max_left _ _))
    | succ i =>
      refine le_trans ?_ (le_max_right _ _)
      have e : (fun j => τ.1 ((T i ᵥ* B + α i • V 0) j)) =
          (fun j => τ.1 (T i j)) ᵥ* B.map τ.1 + τ.1 (α i) • V.map τ.1 0 := by
        ext j; simp [vecMul, dotProduct]
      rw [r1, hval_eq, e]
      exact lift_le (hH τ).1 _ _ (L τ) _ _ (le_max_left _ _) (hVC τ)
        ((hTC i τ).trans (le_max_right _ _)) ((hαC i τ).trans (le_max_right _ _))
end GlobalTheory.SW
