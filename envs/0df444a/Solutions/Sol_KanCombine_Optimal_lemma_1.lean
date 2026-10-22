-- Prove2me | solution 1 for KanCombine.Optimal.lemma_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T14:02:21.066758+00:00
-- url     : https://prove2.me/submissions/a33cd309-2992-4715-ba33-aac4a1e574ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Definitions.Def_KanCombine_Optimal_Model
import Theorems.Thm_KanCombine_Optimal_eq_A9
import Theorems.Thm_KanCombine_Optimal_eq_A10
import Theorems.Thm_KanCombine_Optimal_eq_A11
import Theorems.Thm_KanCombine_Optimal_eq_A12
import Theorems.Thm_KanCombine_Optimal_eq_A13

open MeasureTheory ProbabilityTheory Matrix RiskEU.OOSUVar KanCombine.Optimal

lemma kanL1_pointwise {N h : ℕ} (M : Market N) (hS : M.Sigma.IsHermitian) (c : ℝ)
    (x : Fin h → Fin N → ℝ) :
    M.U (wComb M c x) = muGt M x + (c / M.gamma) * muZt M x
      - M.gamma / 2 * (sigGt2 M x + 2 * (c / M.gamma) * sigGZt M x
        + (c / M.gamma) ^ 2 * sigZt2 M x) := by
  have hT : M.Sigmaᵀ = M.Sigma := by
    have := hS
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hsym : wHatZ x ⬝ᵥ (M.Sigma *ᵥ wHatG x) = wHatG x ⬝ᵥ (M.Sigma *ᵥ wHatZ x) := by
    rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hT]
  simp only [Market.U, wComb, muGt, muZt, sigGt2, sigZt2, sigGZt, mulVec_add, mulVec_smul,
    add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hsym]
  ring

theorem solution {N h : ℕ} (M : Market N) (hM : KanStanding M h)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin h → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r) :
    ∀ c : ℝ, Integrable (fun ω => M.U (wComb M c (sampleData r ω))) P ∧
      expUtility M P r c =
        M.muG - M.gamma * ((h : ℝ) - 2) * M.sigmaG2 / (2 * ((h : ℝ) - N - 1)) +
          (h : ℝ) / (M.gamma * ((h : ℝ) - N - 1)) *
            (c * M.psi2 - c ^ 2 * ((h : ℝ) - 2) * ((h : ℝ) * M.psi2 + N - 1) /
              (2 * ((h : ℝ) - N) * ((h : ℝ) - N - 3))) := by
  intro c
  obtain ⟨i9, e9⟩ := eq_A9 M hM P r hr
  obtain ⟨i10, e10⟩ := eq_A10 M hM P r hr
  obtain ⟨i11, e11⟩ := eq_A11 M hM P r hr
  obtain ⟨i12, e12⟩ := eq_A12 M hM P r hr
  obtain ⟨i13, e13⟩ := eq_A13 M hM P r hr
  obtain ⟨hN2, hNh, hS, hg⟩ := hM
  have hpw := fun ω => kanL1_pointwise M hS.isHermitian c (sampleData r ω)
  set a := c / M.gamma
  have hfun : (fun ω => M.U (wComb M c (sampleData r ω))) =
      fun ω => (muGt M (sampleData r ω) + a * muZt M (sampleData r ω))
        - M.gamma / 2 * ((sigGt2 M (sampleData r ω) + (2 * a) * sigGZt M (sampleData r ω))
          + a ^ 2 * sigZt2 M (sampleData r ω)) := by
    funext ω; rw [hpw ω]
  have iA : Integrable (fun ω => muGt M (sampleData r ω) + a * muZt M (sampleData r ω)) P :=
    i9.add (i10.const_mul a)
  have iB0 : Integrable (fun ω => sigGt2 M (sampleData r ω) + (2 * a) * sigGZt M (sampleData r ω)) P :=
    i11.add (i13.const_mul (2 * a))
  have iB1 : Integrable (fun ω => (sigGt2 M (sampleData r ω) + (2 * a) * sigGZt M (sampleData r ω))
      + a ^ 2 * sigZt2 M (sampleData r ω)) P := iB0.add (i12.const_mul (a ^ 2))
  have iB : Integrable (fun ω => M.gamma / 2 * ((sigGt2 M (sampleData r ω)
      + (2 * a) * sigGZt M (sampleData r ω)) + a ^ 2 * sigZt2 M (sampleData r ω))) P :=
    iB1.const_mul _
  refine ⟨hfun ▸ iA.sub iB, ?_⟩
  unfold expUtility
  rw [hfun, integral_sub iA iB, integral_add i9 (i10.const_mul a), integral_const_mul,
    integral_const_mul, integral_add iB0 (i12.const_mul (a ^ 2)),
    integral_add i11 (i13.const_mul (2 * a)), integral_const_mul, integral_const_mul,
    e9, e10, e11, e12, e13]
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hhr : (N : ℝ) + 3 < h := by exact_mod_cast hNh
  have h1 : (h : ℝ) - N - 1 ≠ 0 := by linarith
  have h2 : (h : ℝ) - N ≠ 0 := by linarith
  have h3 : (h : ℝ) - N - 3 ≠ 0 := by linarith
  have hg0 : M.gamma ≠ 0 := hg.ne'
  simp only [a]
  field_simp
  ring
