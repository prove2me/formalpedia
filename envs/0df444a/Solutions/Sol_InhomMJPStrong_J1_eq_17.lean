-- Prove2me | solution 1 for InhomMJPStrong.J1.eq_17
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T22:40:49.381212+00:00
-- url     : https://prove2.me/submissions/89149c79-7c2d-4f52-b9f9-214acbccaa0c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InhomMJPStrong_J1_Model
import Theorems.Thm_InhomMJPStrong_J1_eq_16
import Theorems.Thm_InhomMJPStrong_J1_superposition_poisson

open MeasureTheory ProbabilityTheory Filter Asymptotics
open InhomMJPStrong.J1

namespace J1Eq17

lemma arrivalOf_zero (N : ℝ → ℕ) : arrivalOf N 0 = 0 := by
  unfold arrivalOf
  have : {t : ℝ | 0 ≤ t ∧ 0 ≤ N t} = Set.Ici 0 := by ext t; simp
  rw [this, csInf_Ici]

lemma maxGap_congr (T T' U : ℕ → ℝ) (m : ℕ) (h : ∀ l, 1 ≤ l → l ≤ m → T l = T' l) :
    maxGap T U m = maxGap T' U m := by
  unfold maxGap
  by_cases hne : (Finset.Icc 1 m).Nonempty
  · rw [dif_pos hne, dif_pos hne]
    refine Finset.sup'_congr hne rfl fun l hl => ?_
    rw [Finset.mem_Icc] at hl
    rw [h l hl.1 hl.2]
  · rw [dif_neg hne, dif_neg hne]

/-- Extension of a finite vector by zero. -/
noncomputable def ext {m : ℕ} (v : Fin m → ℝ) (i : ℕ) : ℝ := if h : i < m then v ⟨i, h⟩ else 0

/-- The maximal-deviation statistic as a function of the first `m` gaps. -/
noncomputable def Φ (n m : ℕ) (v : Fin m → ℝ) : ℝ :=
  maxGap (fun l => ∑ i ∈ Finset.range l, ext v i) (fun l => (l : ℝ) / (n : ℝ)) m

lemma continuous_Φ (n m : ℕ) : Continuous (Φ n m) := by
  unfold Φ maxGap
  by_cases hne : (Finset.Icc 1 m).Nonempty
  · simp only [dif_pos hne]
    refine Continuous.finset_sup'_apply hne fun l _ => ?_
    refine (continuous_finset_sum _ fun i _ => ?_).sub continuous_const |>.abs
    unfold ext
    by_cases hi : i < m
    · simp only [dif_pos hi]; exact continuous_apply _
    · simp only [dif_neg hi]; exact continuous_const
  · simp only [dif_neg hne]; exact continuous_const

lemma Φ_eq (Y : ℕ → ℝ) (hY0 : Y 0 = 0) (n m : ℕ) :
    maxGap Y (fun l => (l : ℝ) / (n : ℝ)) m = Φ n m (fun i : Fin m => Y (i + 1) - Y i) := by
  unfold Φ
  refine maxGap_congr _ _ _ m fun l _ hlm => ?_
  have : ∑ i ∈ Finset.range l, ext (fun i : Fin m => Y (i + 1) - Y i) i
      = ∑ i ∈ Finset.range l, (Y (i + 1) - Y i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have : i < m := lt_of_lt_of_le (Finset.mem_range.1 hi) hlm
    simp [ext, this]
  rw [this, Finset.sum_range_sub, hY0, sub_zero]

lemma maxGap_arrival (Y : ℕ → ℝ) (hY0 : Y 0 = 0) (n m : ℕ) :
    maxGap Y (fun l => (l : ℝ) / (n : ℝ)) m =
      maxGap (fun l => arrival (fun i => Y (i + 1) - Y i) l) (fun l => (l : ℝ) / (n : ℝ)) m := by
  refine maxGap_congr _ _ _ m fun l _ _ => ?_
  unfold arrival
  rw [Finset.sum_range_sub, hY0, sub_zero]

lemma prob_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {μ : Measure ℝ} (m : ℕ) (g h : ℕ → Ω → ℝ) (hg : iIndepFun g P) (hh : iIndepFun h P)
    (hgl : ∀ i, HasLaw (g i) μ P) (hhl : ∀ i, HasLaw (h i) μ P)
    (A : Set (Fin m → ℝ)) (hA : MeasurableSet A) :
    P {ω | (fun i : Fin m => g i ω) ∈ A} = P {ω | (fun i : Fin m => h i ω) ∈ A} := by
  have hg' : iIndepFun (fun i : Fin m => g i) P := hg.precomp Fin.val_injective
  have hh' : iIndepFun (fun i : Fin m => h i) P := hh.precomp Fin.val_injective
  have e1 := iIndepFun.map_fun_eq_pi_map (f := fun (i : Fin m) => g i)
    (fun i : Fin m => (hgl i).aemeasurable) hg'
  have e2 := iIndepFun.map_fun_eq_pi_map (f := fun (i : Fin m) => h i)
    (fun i : Fin m => (hhl i).aemeasurable) hh'
  have f1 : (fun i : Fin m => P.map (g i)) = fun _ => μ := funext fun i => (hgl i).map_eq
  have f2 : (fun i : Fin m => P.map (h i)) = fun _ => μ := funext fun i => (hhl i).map_eq
  rw [f1] at e1; rw [f2] at e2
  have a1 : AEMeasurable (fun ω (i : Fin m) => g i ω) P :=
    aemeasurable_pi_lambda _ fun i => (hgl i).aemeasurable
  have a2 : AEMeasurable (fun ω (i : Fin m) => h i ω) P :=
    aemeasurable_pi_lambda _ fun i => (hhl i).aemeasurable
  have := Measure.map_apply_of_aemeasurable a1 hA
  have := Measure.map_apply_of_aemeasurable a2 hA
  change P ((fun ω (i : Fin m) => g i ω) ⁻¹' A) = P ((fun ω (i : Fin m) => h i ω) ⁻¹' A)
  rw [← Measure.map_apply_of_aemeasurable a1 hA, ← Measure.map_apply_of_aemeasurable a2 hA, e1, e2]

end J1Eq17

open J1Eq17 in
theorem solution {p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hp : 1 ≤ p) (Lam : ℝ → Matrix (Fin p) (Fin p) ℝ)
    (hLam : IsIntensityFn Lam) (hBound : Condition1 Lam)
    (hPos : 0 < sSup {x : ℝ | ∃ i t, 0 ≤ t ∧ x = |Lam t i i|})
    (alpha : Fin p → ℝ) (hAlpha : (∀ i, 0 ≤ alpha i) ∧ ∑ i, alpha i = 1)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Src → Ω → ℝ) (hX : IsUnifSetup (lam0 Lam) X P)
    (q eps : ℝ) (hq : 0 < q) (heps : 0 < eps) (heps1 : eps < 1) :
    let beta : ℕ → ℝ := fun n =>
      2 * Real.exp (1 / 2 + eps / 2 + 2 * q) * Real.log (n : ℝ) *
        (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2)
    (∀ n, lam0 Lam ≤ n →
      P {ω | beta n ≤
        maxGap (theta (lam0 Lam) n X ω)
          (fun l => (l : ℝ) / (n : ℝ)) (gridSize n eps)} =
      P {ω | beta n ≤
        maxGap (chi (lam0 Lam) n X ω)
          (fun l => (l : ℝ) / (n : ℝ)) (gridSize n eps)}) ∧
    (fun n : ℕ =>
      (P {ω | beta n ≤
        maxGap (theta (lam0 Lam) n X ω)
          (fun l => (l : ℝ) / (n : ℝ)) (gridSize n eps)}).toReal)
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-q)) := by
  intro beta
  have hr : 1 ≤ lam0 Lam := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hPos).ne'
  constructor
  · intro n hn
    obtain ⟨hχi, hχl, hθi, hθl⟩ := superposition_poisson P X (lam0 Lam) n hr hn hX
    have hA : MeasurableSet {v : Fin (gridSize n eps) → ℝ | beta n ≤ Φ n (gridSize n eps) v} :=
      measurableSet_le measurable_const (continuous_Φ n _).measurable
    have h1 : {ω | beta n ≤ maxGap (theta (lam0 Lam) n X ω) (fun l => (l : ℝ) / (n : ℝ))
        (gridSize n eps)} = {ω | (fun i : Fin (gridSize n eps) =>
          (fun l ω => theta (lam0 Lam) n X ω (l + 1) - theta (lam0 Lam) n X ω l) (i : ℕ) ω) ∈
          {v : Fin (gridSize n eps) → ℝ | beta n ≤ Φ n (gridSize n eps) v}} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [Φ_eq (theta (lam0 Lam) n X ω) (arrivalOf_zero _)]
    have h2 : {ω | beta n ≤ maxGap (chi (lam0 Lam) n X ω) (fun l => (l : ℝ) / (n : ℝ))
        (gridSize n eps)} = {ω | (fun i : Fin (gridSize n eps) =>
          (fun l ω => chi (lam0 Lam) n X ω (l + 1) - chi (lam0 Lam) n X ω l) (i : ℕ) ω) ∈
          {v : Fin (gridSize n eps) → ℝ | beta n ≤ Φ n (gridSize n eps) v}} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [Φ_eq (chi (lam0 Lam) n X ω) (arrivalOf_zero _)]
    rw [h1, h2]
    exact prob_eq _ _ _ hθi hχi hθl hχl _ hA
  · -- the tail bound from (16)
    set a := 1 / 2 + eps / 2 + 2 * q with ha
    have hbound : ∀ᶠ n : ℕ in atTop,
        (P {ω | beta n ≤ maxGap (theta (lam0 Lam) n X ω) (fun l => (l : ℝ) / (n : ℝ))
          (gridSize n eps)}).toReal ≤ 2 * (n : ℝ) ^ (-(2 * q)) := by
      filter_upwards [eventually_ge_atTop (lam0 Lam), eventually_ge_atTop 8] with n hn hn8
      have hn8' : (8:ℝ) ≤ n := by exact_mod_cast hn8
      have hnpos : (0:ℝ) < n := by linarith
      have he2 : Real.exp 2 ≤ (n:ℝ) := by
        have : Real.exp 2 < 8 := by
          have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          have h2 := Real.exp_one_lt_d9
          have h3 := Real.exp_pos 1
          nlinarith
        linarith
      obtain ⟨-, -, hθi, hθl⟩ := superposition_poisson P X (lam0 Lam) n hr hn hX
      have h16 := eq_16 P n he2 eps heps heps1 _ hθi hθl (Real.exp a)
        (Real.one_le_exp (by positivity))
      dsimp only at h16
      have hset : {ω | beta n ≤ maxGap (theta (lam0 Lam) n X ω) (fun l => (l : ℝ) / (n : ℝ))
          (gridSize n eps)} = {ω | 2 * Real.exp a * Real.log (n : ℝ) *
            (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2) ≤
            maxGap (fun l => arrival (fun i => theta (lam0 Lam) n X ω (i + 1) -
              theta (lam0 Lam) n X ω i) l) (fun l => (l : ℝ) / (n : ℝ)) (gridSize n eps)} := by
        ext ω
        simp only [Set.mem_setOf_eq]
        rw [maxGap_arrival (theta (lam0 Lam) n X ω) (arrivalOf_zero _)]
      rw [hset]
      have hval : 2 * Real.sqrt ((n : ℝ) ^ (1 + eps)) / Real.exp a ^ Real.log (n : ℝ)
          = 2 * (n : ℝ) ^ (-(2 * q)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hnpos.le, Real.rpow_def_of_pos (Real.exp_pos a),
          Real.log_exp, Real.rpow_def_of_pos hnpos, Real.rpow_def_of_pos hnpos, mul_div_assoc,
          ← Real.exp_sub]
        congr 2
        rw [ha]; ring
      rw [hval] at h16
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h16
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have hO : (fun n : ℕ => 2 * (n : ℝ) ^ (-(2 * q))) =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-q)) := by
      have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (-q)) atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop hq).comp tendsto_natCast_atTop_atTop
      have h1 : (fun n : ℕ => (n : ℝ) ^ (-q)) =o[atTop] (fun _ => (1:ℝ)) :=
        (isLittleO_one_iff ℝ).2 ht
      have h2 := (h1.mul_isBigO (isBigO_refl (fun n : ℕ => (n : ℝ) ^ (-q)) atTop)).const_mul_left 2
      refine h2.congr' ?_ ?_
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hnpos : (0:ℝ) < n := by exact_mod_cast hn
        rw [← Real.rpow_add hnpos]; ring_nf
      · exact Eventually.of_forall fun n => one_mul _
    refine Asymptotics.IsBigO.trans_isLittleO ?_ hO
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [hbound] with n hn
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg, one_mul]
    exact le_trans hn (le_abs_self _)
