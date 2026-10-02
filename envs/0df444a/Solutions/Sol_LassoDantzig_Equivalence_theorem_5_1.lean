-- Prove2me | solution 1 for LassoDantzig.Equivalence.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-01T12:34:20.959168+00:00
-- url     : https://prove2.me/submissions/020797ea-5638-46f7-b835-784e09cc8eb3

import Theorems.Thm_LassoDantzig_Equivalence_eq_B4_noise_event
import Theorems.Thm_LassoDantzig_Equivalence_eq_B15_dantzig_side
import Theorems.Thm_LassoDantzig_Equivalence_eq_B17_lasso_side

open MeasureTheory ProbabilityTheory

open LassoDantzig.Equivalence

/-- Theorem 5.1 (Bickel–Ritov–Tsybakov): approximate equivalence of the Lasso and Dantzig
prediction losses. With probability at least `1 − M^{1 − A²/8}`, for every Lasso solution
`β̂_L` with `𝓜(β̂_L) ≤ s` and every Dantzig selector `β̂_D` (same `r = Aσ√(log M / n)`),
`|‖f̂_D − f‖_n² − ‖f̂_L − f‖_n²| ≤ 16 A² (𝓜(β̂_L) σ² / n) (f_max² / κ²) log M`. -/
theorem solution {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (f : Fin n → ℝ) (hX : ∀ j, colNorm X j ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M) (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 1 κ)
    (A : ℝ) (hA : 2 * Real.sqrt 2 < A) (r : ℝ) (hr : r = A * σ * Real.sqrt (Real.log M / n)) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - (M : ℝ) ^ (1 - A ^ 2 / 8) ≤ (P E).toReal ∧
      ∀ ω ∈ E, ∀ βL βD : Fin M → ℝ,
        IsLasso X (fun i => f i + W i ω) r βL → IsDantzig X (fun i => f i + W i ω) r βD →
        sparsity βL ≤ s →
        |predLoss X f βD - predLoss X f βL| ≤
          16 * A ^ 2 * ((sparsity βL : ℝ) * σ ^ 2 / n) * (fmax X ^ 2 / κ ^ 2) * Real.log M := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hMone : (1 : ℝ) < M := by exact_mod_cast (by omega : 1 < M)
  have hApos : 0 < A := lt_trans (by positivity) hA
  have hlog : 0 < Real.log M := Real.log_pos hMone
  have hrpos : 0 < r := by rw [hr]; positivity
  have hr2 : r ^ 2 = A ^ 2 * σ ^ 2 * (Real.log M / n) := by
    rw [hr, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  let E : Set Ω := {ω | NoiseEventHalf X r (fun i => W i ω)}
  have hE : MeasurableSet E := by
    simp only [E, NoiseEventHalf, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    apply measurableSet_le _ measurable_const
    exact measurable_const.mul ((measurable_const.mul
      (Finset.measurable_sum _ (fun i _ => measurable_const.mul (hWm i)))).abs)
  have hbad : P Eᶜ ≤ ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 8)) :=
    eq_B4_noise_event hn hM X hX P W σ hσ hWm hWind hWlaw A hApos r hr
  have hbadReal : (P Eᶜ).toReal ≤ (M : ℝ) ^ (1 - A ^ 2 / 8) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
    rwa [ENNReal.toReal_ofReal (Real.rpow_nonneg (Nat.cast_nonneg M) _)] at h
  have hsum : (P E).toReal + (P Eᶜ).toReal = 1 := by
    simpa [Measure.real] using measureReal_add_measureReal_compl (μ := P) hE
  refine ⟨E, hE, by linarith, ?_⟩
  intro ω hω βL βD hL hD hsp
  have hhalf : NoiseEventHalf X r (fun i => W i ω) := hω
  have hfull : NoiseEvent X r (fun i => W i ω) := by
    intro j
    have hj := hhalf j
    have hnonneg := abs_nonneg ((1 / (n : ℝ)) * ∑ i, X i j * W i ω)
    linarith
  have hDside := eq_B15_dantzig_side hn hM X f (fun i => W i ω) hX
    s hs1 hsM κ hκ hRE r hrpos hfull βL βD hL hD hsp
  have hLside := eq_B17_lasso_side hn hM X f (fun i => W i ω) hX
    s hs1 hsM κ hκ hRE r hrpos hhalf βL βD hL hD hsp
  let C : ℝ := fmax X ^ 2 * r ^ 2 * (sparsity βL : ℝ) / κ ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have h16 : 16 * C =
      16 * A ^ 2 * ((sparsity βL : ℝ) * σ ^ 2 / n) * (fmax X ^ 2 / κ ^ 2) * Real.log M := by
    dsimp [C]
    rw [hr2]
    ring
  have hDconst : 16 * fmax X ^ 2 * r ^ 2 * (sparsity βL : ℝ) / κ ^ 2 = 16 * C := by
    dsimp [C]; ring
  have hLconst : 9 * fmax X ^ 2 * r ^ 2 * (sparsity βL : ℝ) / κ ^ 2 = 9 * C := by
    dsimp [C]; ring
  rw [hDconst] at hDside
  rw [hLconst] at hLside
  rw [← h16]
  exact abs_le.mpr ⟨by linarith only [hLside, hC], by linarith only [hDside]⟩


