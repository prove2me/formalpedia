-- Prove2me | solution 1 for KanCombine.Optimal.eq_20
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T14:00:15.518402+00:00
-- url     : https://prove2.me/submissions/0a72eccb-b009-49c0-9b79-a24f230ad847
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Definitions.Def_KanCombine_Optimal_Model
import Theorems.Thm_KanCombine_Optimal_lemma_1

open MeasureTheory ProbabilityTheory Matrix RiskEU.OOSUVar KanCombine.Optimal

/-- ψ² ≥ 0 when Σ is positive definite and N ≥ 1 (Cauchy–Schwarz in the Σ⁻¹ inner product). -/
lemma kan20_psi2_nonneg {N : ℕ} (M : Market N) (hN : 1 ≤ N) (hS : M.Sigma.PosDef) :
    0 ≤ M.psi2 ∧ 0 < M.sigmaG2 := by
  have hI : (M.Sigma⁻¹).PosDef := hS.inv
  set S := M.Sigma⁻¹ with hSdef
  set e := ones N
  have he : e ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hN⟩
    simp [e, ones] at this
  have ha : 0 < e ⬝ᵥ (S *ᵥ e) := by
    have := hI.dotProduct_mulVec_pos he
    simpa using this
  have hsym : ∀ u v : Fin N → ℝ, u ⬝ᵥ (S *ᵥ v) = v ⬝ᵥ (S *ᵥ u) := by
    intro u v
    have hH : Sᵀ = S := by
      have := hI.isHermitian
      rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
      exact this
    rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hH]
  set a := e ⬝ᵥ (S *ᵥ e)
  set b := M.mu ⬝ᵥ (S *ᵥ e)
  set m := M.mu ⬝ᵥ (S *ᵥ M.mu)
  have hq : 0 ≤ (a • M.mu - b • e) ⬝ᵥ (S *ᵥ (a • M.mu - b • e)) := by
    have := hI.posSemidef.dotProduct_mulVec_nonneg (a • M.mu - b • e)
    simpa using this
  have hexp : (a • M.mu - b • e) ⬝ᵥ (S *ᵥ (a • M.mu - b • e)) = a * (a * m - b ^ 2) := by
    have h1 := hsym e M.mu
    simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    rw [h1]
    ring
  have hcs : 0 ≤ a * m - b ^ 2 := by
    rw [hexp] at hq
    exact (mul_nonneg_iff_of_pos_left ha).mp hq
  have hsg : M.sigmaG2 = a⁻¹ := rfl
  have hmg : M.muG = b * a⁻¹ := rfl
  have hp : M.psi2 = m - (b * a⁻¹) ^ 2 / a⁻¹ := by
    show m - M.muG ^ 2 / M.sigmaG2 = _
    rw [hmg, hsg]
  refine ⟨?_, by rw [hsg]; exact inv_pos.mpr ha⟩
  rw [hp]
  have : m - (b * a⁻¹) ^ 2 / a⁻¹ = (a * m - b ^ 2) / a := by
    field_simp
  rw [this]
  exact div_nonneg hcs ha.le

theorem solution {N h : ℕ} (M : Market N) (hM : KanStanding M h)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin h → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r) :
    (∀ c : ℝ, expUtility M P r c ≤ expUtility M P r (cStar M h)) ∧
    (∀ c : ℝ, expUtility M P r c = expUtility M P r (cStar M h) → c = cStar M h) ∧
    0 ≤ cStar M h ∧ cStar M h < 1 ∧ (0 < M.psi2 → 0 < cStar M h) := by
  obtain ⟨hN2, hNh, hS, hg⟩ := hM
  have L := lemma_1 M ⟨hN2, hNh, hS, hg⟩ P r hr
  obtain ⟨hψ, -⟩ := kan20_psi2_nonneg M (by omega) hS
  set ψ := M.psi2
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hhr : (N : ℝ) + 3 < h := by exact_mod_cast hNh
  set H : ℝ := (h : ℝ)
  set n : ℝ := (N : ℝ)
  set D : ℝ := H / (M.gamma * (H - n - 1))
  set E : ℝ := (H - 2) * (H * ψ + n - 1) / ((H - n) * (H - n - 3))
  have hD : 0 < D := div_pos (by linarith) (mul_pos hg (by linarith))
  have hE : 0 < E := div_pos (mul_pos (by linarith) (by nlinarith))
    (mul_pos (by linarith) (by linarith))
  set A : ℝ := M.muG - M.gamma * (H - 2) * M.sigmaG2 / (2 * (H - n - 1))
  have h3 : H - n ≠ 0 := by linarith
  have h4 : H - n - 3 ≠ 0 := by linarith
  have hf : ∀ c, expUtility M P r c = A + D * (c * ψ - c ^ 2 * E / 2) := by
    intro c
    rw [(L c).2]
    congr 2
    simp only [E]
    field_simp
  have hcs : cStar M h = ψ / E := by
    show ((H - n) * (H - n - 3) / (H * (H - 2))) * ψ / (ψ + (n - 1) / H) = _
    have h1 : H * ψ + n - 1 ≠ 0 := by nlinarith
    have h2 : ψ + (n - 1) / H ≠ 0 := by
      have : 0 < (n - 1) / H := div_pos (by linarith) (by linarith)
      linarith
    have h5 : H ≠ 0 := by linarith
    have h6 : H - 2 ≠ 0 := by linarith
    simp only [E]
    field_simp
    ring_nf
    have h1' : -1 + ψ * H + n ≠ 0 := by nlinarith
    field_simp
    ring
  set cs := cStar M h
  have hcE : cs * E = ψ := by rw [hcs]; field_simp
  have key : ∀ c, expUtility M P r cs - expUtility M P r c = D * E / 2 * (c - cs) ^ 2 := by
    intro c
    rw [hf, hf]
    linear_combination (-(D * (cs - c))) * hcE
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c
    have := key c
    have : 0 ≤ D * E / 2 * (c - cs) ^ 2 := by positivity
    linarith
  · intro c hc
    have := key c
    rw [hc, sub_self] at this
    have hDE : D * E / 2 ≠ 0 := by positivity
    have : (c - cs) ^ 2 = 0 := by
      rcases mul_eq_zero.mp this.symm with h | h
      · exact absurd h hDE
      · exact h
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  · rw [hcs]; exact div_nonneg hψ hE.le
  · rw [hcs, div_lt_one hE]
    simp only [E]
    rw [lt_div_iff₀ (mul_pos (by linarith) (by linarith))]
    nlinarith [mul_nonneg hψ (by linarith : (0:ℝ) ≤ H - n), mul_pos (by linarith : (0:ℝ) < n - 1) (by linarith : (0:ℝ) < H - 2)]
  · intro hp
    rw [hcs]; exact div_pos hp hE
