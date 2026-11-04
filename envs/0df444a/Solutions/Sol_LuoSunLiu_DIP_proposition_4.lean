-- Prove2me | solution 1 for LuoSunLiu.DIP.proposition_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T05:16:55.567387+00:00
-- url     : https://prove2.me/submissions/a6358002-f4d0-44e4-a323-cc9818d9a895
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LuoSunLiu_DIP_Model
import Definitions.Def_LuoSunLiu_DIP_InnerB
import Definitions.Def_LuoSunLiu_DIP_PLB
import Theorems.Thm_LuoSunLiu_DIP_lemma_1
import Theorems.Thm_LuoSunLiu_DIP_lemma_2
import Theorems.Thm_LuoSunLiu_DIP_lemma_3

open MeasureTheory ProbabilityTheory NNReal ENNReal

namespace LuoSunLiu.DIP.P4Aux
open LuoSunLiu.DIP

theorem l1_nonneg {d0 : ℕ} (θ : Fin d0 → ℝ) : 0 ≤ l1 θ :=
  Finset.sum_nonneg fun i _ => abs_nonneg _

theorem abs_dot_le {d0 : ℕ} (y θ : Fin d0 → ℝ) (hy : ∀ i, |y i| ≤ 1) : |y ⬝ᵥ θ| ≤ l1 θ := by
  unfold dotProduct l1
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  calc |y i| * |θ i| ≤ 1 * |θ i| := mul_le_mul_of_nonneg_right (hy i) (abs_nonneg _)
    _ = |θ i| := one_mul _

theorem grid_near (g0 h pmax p : ℝ) (d : ℕ) (hd : 1 ≤ d) (hh : 0 < h) (hhp : h < pmax)
    (hg0 : g0 ≤ h / 2) (hgl : pmax - h / 2 ≤ g0 + ((d : ℝ) - 1) * h) (hp0 : 0 < p)
    (hp1 : p < pmax) :
    ∃ j : ℕ, j < d ∧ 0 < g0 + j * h ∧ g0 + j * h < pmax ∧ |p - (g0 + j * h)| ≤ h := by
  set r := (p - g0) / h with hr
  have hrh : r * h = p - g0 := by rw [hr]; field_simp
  set j1 := ⌈r⌉₊ with hj1
  have hle : r ≤ j1 := Nat.le_ceil r
  by_cases hjd : d ≤ j1
  · refine ⟨d - 1, by omega, ?_⟩
    have hlt : ((d - 1 : ℕ) : ℝ) < r := Nat.lt_ceil.1 (by omega)
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd]; simp
    rw [hcast] at hlt ⊢
    have h1 : g0 + ((d : ℝ) - 1) * h < p := by nlinarith
    refine ⟨by linarith, by linarith, ?_⟩
    rw [abs_of_pos (by linarith)]; linarith
  push Not at hjd
  rcases le_or_gt 0 r with hr0 | hr0
  · have hlt : (j1 : ℝ) < r + 1 := Nat.ceil_lt_add_one hr0
    have hpg : p ≤ g0 + j1 * h := by nlinarith
    have hgp : g0 + j1 * h < p + h := by nlinarith
    by_cases hgm : g0 + j1 * h < pmax
    · exact ⟨j1, hjd, by linarith, hgm, by rw [abs_of_nonpos (by linarith)]; linarith⟩
    · push Not at hgm
      have hj1pos : 1 ≤ j1 := by
        by_contra hc
        have : j1 = 0 := by omega
        rw [this] at hgm; simp at hgm; linarith
      refine ⟨j1 - 1, by omega, ?_⟩
      have hcast : ((j1 - 1 : ℕ) : ℝ) = (j1 : ℝ) - 1 := by rw [Nat.cast_sub hj1pos]; simp
      rw [hcast]
      have hq : g0 + ((j1 : ℝ) - 1) * h < p := by nlinarith
      refine ⟨by nlinarith, by linarith, ?_⟩
      rw [abs_of_pos (by linarith)]; nlinarith
  · have hj0 : j1 = 0 := Nat.ceil_eq_zero.2 hr0.le
    refine ⟨0, by omega, ?_⟩
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have hpg : p < g0 := by
      have : r * h < 0 := mul_neg_of_neg_of_pos hr0 hh
      linarith
    refine ⟨by linarith, by linarith, ?_⟩
    rw [abs_of_neg (by linarith)]; linarith

/-- Some arm is available for every covariate in `𝒳` (the nearest grid point to `p_max/2`). -/
theorem exists_avail {d0 : ℕ} (M : PricingModel d0) (hM : M.Standing) (θh : Fin d0 → ℝ)
    (d : ℕ) (hd : 1 ≤ d) (hgrid : M.pmax + 2 * l1 θh < d * M.pmax) (y : Fin d0 → ℝ)
    (hy : y ∈ M.X) : ∃ j : Fin d, j ∈ avail M.pmax θh d y := by
  obtain ⟨-, hp, hX, -⟩ := hM
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hl0 := l1_nonneg θh
  set h := gridStep M.pmax θh d with hhdef
  have hdh : (d : ℝ) * h = M.pmax + 2 * l1 θh := by rw [hhdef, gridStep]; field_simp
  have hh : 0 < h := by rw [hhdef, gridStep]; positivity
  have hhp : h < M.pmax := by
    by_contra hc; push Not at hc
    have : (d : ℝ) * M.pmax ≤ d * h := mul_le_mul_of_nonneg_left hc hd'.le
    linarith
  have hdot := abs_dot_le y θh (hX y hy)
  rw [abs_le] at hdot
  obtain ⟨hdot1, hdot2⟩ := hdot
  -- the grid point closest to `p_max / 2`
  set g0 := -l1 θh + h / 2 + y ⬝ᵥ θh with hg0
  have hgrid_eq : ∀ j : Fin d, gridPrice M.pmax θh d j y = g0 + (j : ℕ) * h := by
    intro j; simp only [gridPrice, gridMid, hg0, ← hhdef]; ring
  have key := grid_near g0 h M.pmax (M.pmax / 2) d hd hh hhp (by rw [hg0]; linarith)
    (by rw [hg0]; nlinarith) (by linarith) (by linarith)
  obtain ⟨j, hjd, hj0, hj1, -⟩ := key
  refine ⟨⟨j, hjd⟩, ?_⟩
  simp only [avail, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hgrid_eq]; exact ⟨hj0, hj1⟩


theorem pullSet_congr {d : ℕ} (j j' : ℕ → Fin d) (τ T0 : ℕ) (hτ : τ ≤ T0)
    (hj : ∀ t ∈ Finset.Icc 1 T0, j t = j' t) (i : Fin d) :
    pullSet j 0 τ i = pullSet j' 0 τ i := by
  ext s
  simp only [pullSet, Finset.mem_filter, Finset.mem_Ico, zero_add]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← hj s (Finset.mem_Icc.2 ⟨h1.1, by omega⟩)]; exact h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [hj s (Finset.mem_Icc.2 ⟨h1.1, by omega⟩)]; exact h2⟩

theorem ucb_congr {d : ℕ} (lam β : ℝ) (j j' : ℕ → Fin d) (p p' y y' : ℕ → ℝ) (τ T0 : ℕ)
    (hτ : τ ≤ T0) (hj : ∀ t ∈ Finset.Icc 1 T0, j t = j' t)
    (hp : ∀ t ∈ Finset.Icc 1 T0, p t = p' t) (hy : ∀ t ∈ Finset.Icc 1 T0, y t = y' t)
    (i : Fin d) : ucb lam β j p y 0 τ i = ucb lam β j' p' y' 0 τ i := by
  have hmem : ∀ s ∈ pullSet j' 0 τ i, s ∈ Finset.Icc 1 T0 := by
    intro s hs
    simp only [pullSet, Finset.mem_filter, Finset.mem_Ico, zero_add] at hs
    exact Finset.mem_Icc.2 ⟨hs.1.1, by omega⟩
  have h1 : ∑ s ∈ pullSet j' 0 τ i, p s ^ 2 * y s = ∑ s ∈ pullSet j' 0 τ i, p' s ^ 2 * y' s :=
    Finset.sum_congr rfl fun s hs => by rw [hp s (hmem s hs), hy s (hmem s hs)]
  have h2 : ∑ s ∈ pullSet j' 0 τ i, p s ^ 2 = ∑ s ∈ pullSet j' 0 τ i, p' s ^ 2 :=
    Finset.sum_congr rfl fun s hs => by rw [hp s (hmem s hs)]
  simp only [ucb, pullSet_congr j j' τ T0 hτ hj i, h1, h2]

theorem innerB_congr {d0 d : ℕ} (pmax : ℝ) (θh : Fin d0 → ℝ) (lam : ℝ) (β : ℕ → ℝ) (T0 : ℕ)
    (x x' : ℕ → Fin d0 → ℝ) (j j' : ℕ → Fin d) (p p' y y' : ℕ → ℝ)
    (hx : ∀ t ∈ Finset.Icc 1 T0, x t = x' t) (hj : ∀ t ∈ Finset.Icc 1 T0, j t = j' t)
    (hp : ∀ t ∈ Finset.Icc 1 T0, p t = p' t) (hy : ∀ t ∈ Finset.Icc 1 T0, y t = y' t)
    (h : IsInnerBRun pmax θh lam β 0 T0 x j p y) :
    IsInnerBRun pmax θh lam β 0 T0 x' j' p' y' := by
  intro τ hτ
  obtain ⟨h1, h2, h3, h4⟩ := h τ hτ
  have hτ' : τ ≤ T0 := (Finset.mem_Icc.1 hτ).2
  simp only [zero_add] at h1 h2 h3 h4 ⊢
  rw [hx τ hτ, hj τ hτ] at h1
  rw [hx τ hτ, hj τ hτ, hp τ hτ] at h2
  rw [hx τ hτ] at h3 h4
  simp only [pullSet_congr j j' τ T0 hτ' hj, hj τ hτ] at h3
  refine ⟨h1, h2, h3, ?_⟩
  intro hall i hi
  have := h4 (fun i hi => by rw [pullSet_congr j j' τ T0 hτ' hj]; exact hall i hi) i hi
  rwa [ucb_congr lam (β τ) j j' p p' y y' τ T0 hτ' hj hp hy,
    ucb_congr lam (β τ) j j' p p' y y' τ T0 hτ' hj hp hy, hj τ hτ] at this

theorem rls_smul {d : ℕ} {Ω : Type*} (lam c : ℝ) (A : ℕ → Ω → Fin d → ℝ) (Z : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) :
    BanditAlgorithm.regularizedLeastSquares d lam A (fun t ω => c * Z t ω) t ω =
      c • BanditAlgorithm.regularizedLeastSquares d lam A Z t ω := by
  unfold BanditAlgorithm.regularizedLeastSquares
  rw [← Matrix.mulVec_smul, Finset.smul_sum]
  simp only [smul_smul]

theorem linUCB_scale {d : ℕ} {Ω : Type*} (lam pmax β : ℝ) (hp : 0 < pmax)
    (A : ℕ → Ω → Fin d → ℝ) (Z : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) (a : Fin d → ℝ) :
    linUCB lam β A (fun t ω => (1 / pmax) * Z t ω) t ω a =
      (1 / pmax) * linUCB lam (pmax ^ 2 * β) A Z t ω a := by
  unfold linUCB
  rw [rls_smul, smul_dotProduct, Real.sqrt_mul (by positivity), Real.sqrt_sq hp.le, smul_eq_mul]
  field_simp


theorem sup'_const_mul {ι : Type*} (s : Finset ι) (h : s.Nonempty) (f : ι → ℝ) (c : ℝ)
    (hc : 0 ≤ c) : s.sup' h (fun i => c * f i) = c * s.sup' h f := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun i hi =>
      mul_le_mul_of_nonneg_left (Finset.le_sup' f hi) hc
  · rcases hc.lt_or_eq with hc | hc
    · rw [← le_div_iff₀' hc]
      exact Finset.sup'_le _ _ fun i hi => by
        rw [le_div_iff₀' hc]; exact Finset.le_sup' (fun i => c * f i) hi
    · subst hc; simp only [zero_mul]
      obtain ⟨i, hi⟩ := h
      exact Finset.le_sup' (fun _ => (0 : ℝ)) hi

theorem dot_single_xi {d0 d : ℕ} (M : PricingModel d0) (θh : Fin d0 → ℝ) (y : Fin d0 → ℝ)
    (c : ℝ) (j : Fin d) :
    (c • xiPricing M θh d y) ⬝ᵥ Pi.single j (gridPrice M.pmax θh d j y) =
      c * revenue M.F (y ⬝ᵥ M.θ0) (gridPrice M.pmax θh d j y) := by
  rw [dotProduct_single]
  simp only [Pi.smul_apply, smul_eq_mul, xiPricing, revenue, gridPrice]
  ring_nf

theorem bestValue_pricing {d0 d : ℕ} (M : PricingModel d0) (θh : Fin d0 → ℝ) (y : Fin d0 → ℝ)
    (c : ℝ) (hc : 0 ≤ c) :
    bestValue (pricingActions M θh d y) (c • xiPricing M θh d y) =
      c * bestGridRevenue M θh d y := by
  unfold bestValue bestGridRevenue pricingActions
  by_cases h : (avail M.pmax θh d y).Nonempty
  · rw [dif_pos (h.image _), dif_pos h, Finset.sup'_image]
    simp only [Function.comp_def, dot_single_xi]
    exact sup'_const_mul _ h _ c hc
  · have h' : ¬ ((avail M.pmax θh d y).image
        (fun j => Pi.single j (gridPrice M.pmax θh d j y))).Nonempty := by
      rwa [Finset.image_nonempty]
    rw [dif_neg h', dif_neg h, mul_zero]

end LuoSunLiu.DIP.P4Aux

open LuoSunLiu.DIP LuoSunLiu.DIP.P4Aux in
theorem solution {d0 : ℕ} (M : PricingModel d0) (hM : M.Standing) (L : ℝ≥0)
    (hL : LipschitzWith L M.F) (θh : Fin d0 → ℝ) (d : ℕ) (hd : 1 ≤ d)
    (hgrid : M.pmax + 2 * l1 θh < d * M.pmax) (lam δ : ℝ) (hlam : 0 < lam)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Filtration ℕ mΩ)
    (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ) (hEnv : IsPricingEnv M P 𝒢 x z p)
    (T0 : ℕ) (hT0 : 1 ≤ T0)
    (hrun : ∀ ω, ∃ j : ℕ → Fin d, IsInnerBRun M.pmax θh lam (betaStar M.pmax lam d δ) 0 T0
      (fun t => x t ω) j (fun t => p t ω) (fun t => response M x z p t ω)) :
    ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ P E ∧
      ∀ ω ∈ E, discreteRegret M θh d x p T0 ω ≤
        2 * Real.sqrt (2 * d * T0 * betaStar M.pmax lam d δ T0 *
          Real.log ((d * lam + T0 * M.pmax ^ 2) / (d * lam))) +
        4 * M.pmax * L * l1 (θh - M.θ0) * T0 + 2 * d * M.pmax := by
  classical
  have hp : 0 < M.pmax := hM.2.1
  have hc0 : 0 ≤ 1 / M.pmax := by positivity
  obtain ⟨ω0⟩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := measure_univ (μ := P)
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
    exact zero_ne_one this
  have hFb : ∀ c, 0 ≤ M.F c ∧ M.F c ≤ 1 := by
    intro c
    obtain ⟨-, -, -, -, hF, -⟩ := hEnv 1 le_rfl
    rw [← hF c]
    exact ⟨measureReal_nonneg, measureReal_le_one⟩
  set xs := x 1 ω0 with hxsdef
  have hxs : xs ∈ M.X := (hEnv 1 le_rfl).2.2.2.1 ω0
  obtain ⟨js, hjs⟩ := exists_avail M hM θh d hd hgrid xs hxs
  set ps := gridPrice M.pmax θh d js xs with hpsdef
  let jc : Ω → ℕ → Fin d := fun ω => Classical.choose (hrun ω)
  have hjc : ∀ ω, IsInnerBRun M.pmax θh lam (betaStar M.pmax lam d δ) 0 T0
      (fun t => x t ω) (jc ω) (fun t => p t ω) (fun t => response M x z p t ω) :=
    fun ω => Classical.choose_spec (hrun ω)
  let x' : ℕ → Ω → Fin d0 → ℝ := fun t ω => if t ≤ T0 then x t ω else xs
  let p' : ℕ → Ω → ℝ := fun t ω => if t ≤ T0 then p t ω else ps
  let j' : ℕ → Ω → Fin d := fun t ω => if t ≤ T0 then jc ω t else js
  have henv' : IsPricingEnv M P 𝒢 x' z p' := by
    intro t ht
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hEnv t ht
    by_cases htT : t ≤ T0
    · refine ⟨?_, ?_, h3, ?_, h5, h6⟩
      · simpa only [x', if_pos htT] using h1
      · simpa only [p', if_pos htT] using h2
      · intro ω; simpa only [x', if_pos htT] using h4 ω
    · refine ⟨?_, ?_, h3, ?_, h5, h6⟩
      · simp only [x', if_neg htT]; exact measurable_const
      · simp only [p', if_neg htT]; exact measurable_const
      · intro ω; simp only [x', if_neg htT]; exact hxs
  have hj' : ∀ t : ℕ, 1 ≤ t → ∀ ω, j' t ω ∈ avail M.pmax θh d (x' t ω) ∧
      p' t ω = gridPrice M.pmax θh d (j' t ω) (x' t ω) := by
    intro t ht ω
    by_cases htT : t ≤ T0
    · obtain ⟨h1, h2, -, -⟩ := hjc ω t (Finset.mem_Icc.2 ⟨ht, htT⟩)
      simp only [zero_add] at h1 h2
      simp only [x', p', j', if_pos htT]
      exact ⟨h1, h2⟩
    · simp only [x', p', j', if_neg htT]
      exact ⟨hjs, rfl⟩
  have hrun' : ∀ ω, IsInnerBRun M.pmax θh lam (betaStar M.pmax lam d δ) 0 T0
      (fun t => x' t ω) (fun t => j' t ω) (fun t => p' t ω)
      (fun t => response M x' z p' t ω) := by
    intro ω
    refine innerB_congr _ _ _ _ T0 _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ (hjc ω)
    · intro t ht; simp only [x', if_pos (Finset.mem_Icc.1 ht).2]
    · intro t ht; simp only [j', if_pos (Finset.mem_Icc.1 ht).2]
    · intro t ht; simp only [p', if_pos (Finset.mem_Icc.1 ht).2]
    · intro t ht; simp only [response, x', p', if_pos (Finset.mem_Icc.1 ht).2]
  obtain ⟨-, hPLB, hPert⟩ := lemma_1 M hM L hL θh d hd P 𝒢 x' z p' henv' j' hj'
  have hML : ∀ ω, IsMLinUCBRunAt lam (betaStar M.pmax lam d δ)
      (fun t ω => pricingActions M θh d (x' t ω))
      (fun t ω => Pi.single (j' t ω) (p' t ω))
      (fun t ω => p' t ω * response M x' z p' t ω) T0 ω := fun ω =>
    ((lemma_2.{0, _}.2 M θh lam δ x' j' p' (fun t ω => response M x' z p' t ω) T0 ω hp hlam hd).2
      (hrun' ω))
  set c : ℝ := 1 / M.pmax with hcdef
  -- the rescaled perturbed linear bandit
  have hPLBs : IsPLBModel P 𝒢 (fun t ω => c • xiPricing M θh d (x' t ω))
      (fun t ω => pricingActions M θh d (x' t ω))
      (fun t ω => Pi.single (j' t ω) (p' t ω))
      (fun t ω => c * (p' t ω * response M x' z p' t ω))
      (fun t ω => c * (p' t ω * response M x' z p' t ω -
        xiPricing M θh d (x' t ω) ⬝ᵥ Pi.single (j' t ω) (p' t ω))) 1 := by
    intro t ht
    obtain ⟨h1, h2, h3, h4⟩ := hPLB t ht
    refine ⟨fun ω => ⟨(h1 ω).1, ?_⟩, h2, h3.const_mul c, ?_⟩
    · simp only [smul_dotProduct, smul_eq_mul]; ring
    · have hk := Kernel.HasSubgaussianMGF.const_mul h4 c
      have e : NNReal.mk (c ^ 2) (sq_nonneg c) * Real.toNNReal M.pmax ^ 2 = 1 := by
        rw [← NNReal.coe_inj]
        rw [NNReal.coe_mul, NNReal.coe_pow, Real.coe_toNNReal _ hp.le, NNReal.coe_one]
        show c ^ 2 * M.pmax ^ 2 = 1
        rw [hcdef]; field_simp
      rw [e] at hk
      exact hk
  have hPerts : HasPerturbation (fun t ω => c • xiPricing M θh d (x' t ω))
      (c * (2 * L * l1 (θh - M.θ0))) := by
    intro s t hs ht ω i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_sub, abs_mul, abs_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left (hPert s t hs ht ω i) hc0
  have hxi01 : ∀ y : Fin d0 → ℝ, ∀ i : Fin d, 0 ≤ xiPricing M θh d y i ∧
      xiPricing M θh d y i ≤ 1 := by
    intro y i
    simp only [xiPricing]
    have := hFb (gridMid M.pmax θh d i + y ⬝ᵥ θh - y ⬝ᵥ M.θ0)
    constructor <;> linarith
  have hCond1 : Condition1 (fun t ω => c • xiPricing M θh d (x' t ω))
      (fun t ω => pricingActions M θh d (x' t ω)) := by
    intro t ht ω a ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ha
    simp only [avail, Finset.mem_filter] at hj
    rw [dotProduct_single]
    simp only [Pi.smul_apply, smul_eq_mul]
    have h01 := hxi01 (x' t ω) j
    rw [abs_le]
    have hg := hj.2
    constructor
    · have : 0 ≤ c * xiPricing M θh d (x' t ω) j * gridPrice M.pmax θh d j (x' t ω) := by
        have := h01.1; have := hg.1.le; positivity
      linarith
    · calc c * xiPricing M θh d (x' t ω) j * gridPrice M.pmax θh d j (x' t ω)
          ≤ c * 1 * M.pmax := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left h01.2 hc0) hg.2.le hg.1.le
            positivity
        _ = 1 := by rw [hcdef]; field_simp
  have hCond2 : Condition2 (fun t ω => c • xiPricing M θh d (x' t ω)) c := by
    intro t ht ω i
    simp only [Pi.smul_apply, smul_eq_mul]
    have h01 := hxi01 (x' t ω) i
    rw [abs_mul, abs_of_nonneg hc0, abs_of_nonneg h01.1]
    calc c * xiPricing M θh d (x' t ω) i ≤ c * 1 := mul_le_mul_of_nonneg_left h01.2 hc0
      _ = c := mul_one c
  have hCond3 : Condition3 (fun t ω => pricingActions M θh d (x' t ω)) M.pmax := by
    intro t ht ω a ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ha
    simp only [avail, Finset.mem_filter] at hj
    refine ⟨⟨j, _, hj.2.1.ne', rfl⟩, ?_⟩
    have hsum : ∑ i, Pi.single (M := fun _ => ℝ) j (gridPrice M.pmax θh d j (x' t ω)) i ^ 2 =
        gridPrice M.pmax θh d j (x' t ω) ^ 2 := by
      rw [Finset.sum_eq_single j (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; ring)
        (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same]
    rw [hsum, Real.sqrt_sq hj.2.1.le]
    exact hj.2.2.le
  have hMLs : ∀ ω, IsMLinUCBRunAt lam (betaTilde c M.pmax lam d δ)
      (fun t ω => pricingActions M θh d (x' t ω))
      (fun t ω => Pi.single (j' t ω) (p' t ω))
      (fun t ω => c * (p' t ω * response M x' z p' t ω)) T0 ω := by
    intro ω t ht
    obtain ⟨h1, h2, h3⟩ := hML ω t ht
    refine ⟨h1, h2, fun hsub a ha => ?_⟩
    have := h3 hsub a ha
    rw [linUCB_scale lam M.pmax _ hp, linUCB_scale lam M.pmax _ hp]
    exact mul_le_mul_of_nonneg_left this hc0
  obtain ⟨E, hE, hPE, hbd⟩ := lemma_3 hd P 𝒢 _ _ _ _ _ (c * (2 * L * l1 (θh - M.θ0))) c M.pmax
    lam δ hPLBs hPerts hCond1 hCond2 hCond3 hc0 hp hlam hδ T0 hT0 hMLs
  refine ⟨E, hE, hPE, fun ω hω => ?_⟩
  have hb := hbd ω hω
  have hdisc : discreteRegret M θh d x p T0 ω = M.pmax *
      plbRegret (fun t ω => c • xiPricing M θh d (x' t ω))
        (fun t ω => pricingActions M θh d (x' t ω))
        (fun t ω => Pi.single (j' t ω) (p' t ω)) T0 ω := by
    unfold discreteRegret plbRegret
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    obtain ⟨ht1, htT⟩ := Finset.mem_Icc.1 ht
    obtain ⟨-, hjp⟩ := hj' t ht1 ω
    have ex : x' t ω = x t ω := by simp only [x', if_pos htT]
    have ep : p' t ω = p t ω := by simp only [p', if_pos htT]
    simp only
    rw [bestValue_pricing _ _ _ c hc0, hjp, dot_single_xi, ← hjp, ex, ep, hcdef]
    field_simp
  rw [hdisc]
  have hbeta : betaStar M.pmax lam d δ T0 = M.pmax ^ 2 * betaTilde c M.pmax lam d δ T0 := rfl
  have hsq : M.pmax * Real.sqrt (2 * d * T0 * betaTilde c M.pmax lam d δ T0 *
      Real.log ((d * lam + T0 * M.pmax ^ 2) / (d * lam))) =
      Real.sqrt (2 * d * T0 * betaStar M.pmax lam d δ T0 *
        Real.log ((d * lam + T0 * M.pmax ^ 2) / (d * lam))) := by
    rw [hbeta]
    have hr : 2 * (d : ℝ) * T0 * (M.pmax ^ 2 * betaTilde c M.pmax lam d δ T0) *
        Real.log ((d * lam + T0 * M.pmax ^ 2) / (d * lam)) = M.pmax ^ 2 *
        (2 * d * T0 * betaTilde c M.pmax lam d δ T0 *
          Real.log ((d * lam + T0 * M.pmax ^ 2) / (d * lam))) := by ring
    rw [hr, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hp.le]
  calc M.pmax * plbRegret _ _ _ T0 ω
      ≤ M.pmax * (2 * Real.sqrt (2 * d * T0 * betaTilde c M.pmax lam d δ T0 *
          Real.log ((d * lam + T0 * M.pmax ^ 2) / (d * lam))) +
          2 * M.pmax * (c * (2 * L * l1 (θh - M.θ0))) * T0 + 2 * d) :=
        mul_le_mul_of_nonneg_left hb hp.le
    _ = 2 * (M.pmax * Real.sqrt (2 * d * T0 * betaTilde c M.pmax lam d δ T0 *
          Real.log ((d * lam + T0 * M.pmax ^ 2) / (d * lam)))) +
          4 * M.pmax * L * l1 (θh - M.θ0) * T0 + 2 * d * M.pmax := by
        rw [hcdef]; field_simp; ring
    _ = _ := by rw [hsq]
