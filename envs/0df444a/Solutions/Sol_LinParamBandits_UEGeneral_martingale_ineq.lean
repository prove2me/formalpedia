-- Prove2me | solution 1 for LinParamBandits.UEGeneral.martingale_ineq
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T21:19:39.462347+00:00
-- url     : https://prove2.me/submissions/3762344b-061c-4f3f-a45e-281ed79c7177

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy
import Theorems.Thm_LinParamBandits_UEGeneral_exp_ineq_ratios

open MeasureTheory ProbabilityTheory

namespace UE3Core

open LinParamBandits.UEGeneral

variable {r : ℕ}

lemma measurable_step (ψ : Policy r) (z : LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    Measurable (fun p : LinParamBandits.LowerBound.History r n × ℝ =>
      Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) p.1
        (ψ.act n p.1, inner ℝ (ψ.act n p.1) z + p.2)) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    have ha : Measurable (fun p : LinParamBandits.LowerBound.History r n × ℝ => ψ.act n p.1) :=
      (ψ.measurable_act n).comp measurable_fst
    refine ha.prodMk ?_
    exact (Measurable.inner ha measurable_const).add measurable_snd
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp measurable_fst

lemma isProb_histMeasure (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) [IsMarkovKernel ν]
    (z : LinParamBandits.LowerBound.Vec r) (ψ : Policy r) :
    ∀ n, IsProbabilityMeasure (histMeasure ν z ψ n)
  | 0 => by
      simp only [histMeasure]; infer_instance
  | n + 1 => by
      have := isProb_histMeasure ν z ψ n
      simp only [histMeasure]
      exact Measure.isProbabilityMeasure_map (measurable_step ψ z n).aemeasurable

/-- The exponent of the exponential supermartingale. -/
noncomputable def G (σ₀ γ : ℝ) (w z : LinParamBandits.LowerBound.Vec r) {n : ℕ}
    (h : LinParamBandits.LowerBound.History r n) : ℝ :=
  γ * ∑ s, inner ℝ w (h s).1 * ((h s).2 - inner ℝ (h s).1 z) -
    γ ^ 2 * σ₀ ^ 2 * (∑ s, inner ℝ w (h s).1 ^ 2) / 2

lemma measurable_G (σ₀ γ : ℝ) (w z : LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    Measurable (fun h : LinParamBandits.LowerBound.History r n => G σ₀ γ w z h) := by
  unfold G
  fun_prop

lemma G_snoc (σ₀ γ : ℝ) (w z : LinParamBandits.LowerBound.Vec r) {n : ℕ}
    (h : LinParamBandits.LowerBound.History r n) (a : LinParamBandits.LowerBound.Vec r) (y : ℝ) :
    G σ₀ γ w z (Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) h
      (a, inner ℝ a z + y)) =
      G σ₀ γ w z h + ((γ * inner ℝ w a) * y - γ ^ 2 * σ₀ ^ 2 * inner ℝ w a ^ 2 / 2) := by
  unfold G
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

theorem core_exp (𝒰 : Set (LinParamBandits.LowerBound.Vec r))
    (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) [IsMarkovKernel ν] (σ₀ : ℝ)
    (hmgf : ∀ u ∈ 𝒰, ∀ x : ℝ,
      ∫⁻ w, ENNReal.ofReal (Real.exp (x * w)) ∂(ν u) ≤ ENNReal.ofReal (Real.exp (x ^ 2 * σ₀ ^ 2 / 2)))
    (z : LinParamBandits.LowerBound.Vec r) (ψ : Policy r) (hact : ∀ t h, ψ.act t h ∈ 𝒰)
    (w : LinParamBandits.LowerBound.Vec r) (γ : ℝ) :
    ∀ n, ∫⁻ h, ENNReal.ofReal (Real.exp (G σ₀ γ w z h)) ∂(histMeasure ν z ψ n) ≤ 1
  | 0 => by
      simp only [histMeasure]
      rw [lintegral_dirac' _ (by
        exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_G σ₀ γ w z 0)))]
      simp [G]
  | n + 1 => by
      have ih := core_exp 𝒰 ν σ₀ hmgf z ψ hact w γ n
      haveI := isProb_histMeasure ν z ψ n
      have hF : Measurable (fun h : LinParamBandits.LowerBound.History r (n + 1) =>
          ENNReal.ofReal (Real.exp (G σ₀ γ w z h))) :=
        ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_G σ₀ γ w z (n + 1)))
      simp only [histMeasure]
      rw [lintegral_map hF (measurable_step ψ z n)]
      rw [Measure.lintegral_compProd (f := fun p : LinParamBandits.LowerBound.History r n × ℝ =>
        ENNReal.ofReal (Real.exp (G σ₀ γ w z (Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) p.1
          (ψ.act n p.1, inner ℝ (ψ.act n p.1) z + p.2))))) (hF.comp (measurable_step ψ z n))]
      refine le_trans (lintegral_mono fun h => ?_) ih
      rw [Kernel.comap_apply]
      simp only [Function.comp_apply, G_snoc]
      set a := ψ.act n h
      have hpt : ∀ y : ℝ, ENNReal.ofReal (Real.exp (G σ₀ γ w z h +
          ((γ * inner ℝ w a) * y - γ ^ 2 * σ₀ ^ 2 * inner ℝ w a ^ 2 / 2))) =
          ENNReal.ofReal (Real.exp (G σ₀ γ w z h) *
            Real.exp (-(γ ^ 2 * σ₀ ^ 2 * inner ℝ w a ^ 2 / 2))) *
          ENNReal.ofReal (Real.exp ((γ * inner ℝ w a) * y)) := by
        intro y
        rw [← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
      simp_rw [hpt]
      rw [lintegral_const_mul _ (f := fun y => ENNReal.ofReal (Real.exp (γ * inner ℝ w a * y)))
        (by fun_prop)]
      calc ENNReal.ofReal (Real.exp (G σ₀ γ w z h) *
            Real.exp (-(γ ^ 2 * σ₀ ^ 2 * inner ℝ w a ^ 2 / 2))) *
            ∫⁻ y, ENNReal.ofReal (Real.exp ((γ * inner ℝ w a) * y)) ∂(ν a)
          ≤ ENNReal.ofReal (Real.exp (G σ₀ γ w z h) *
            Real.exp (-(γ ^ 2 * σ₀ ^ 2 * inner ℝ w a ^ 2 / 2))) *
            ENNReal.ofReal (Real.exp ((γ * inner ℝ w a) ^ 2 * σ₀ ^ 2 / 2)) := by
            gcongr
            exact hmgf a (hact n h) _
        _ = ENNReal.ofReal (Real.exp (G σ₀ γ w z h)) := by
            rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add]
            congr 3
            ring_nf
            simp


/-- The admissible arm set of period `s + 1`. -/
def admissible (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (b : Fin r → LinParamBandits.LowerBound.Vec r)
    (s : ℕ) : Set (LinParamBandits.LowerBound.Vec r) :=
  {v | v ∈ 𝒰 ∧ ∀ hs : s < r, v = b ⟨s, hs⟩}

lemma measurableSet_admissible (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰 : MeasurableSet 𝒰)
    (b : Fin r → LinParamBandits.LowerBound.Vec r) (s : ℕ) : MeasurableSet (admissible 𝒰 b s) := by
  by_cases hs : s < r
  · have : admissible 𝒰 b s = 𝒰 ∩ {b ⟨s, hs⟩} := by
      ext v; simp only [admissible, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_singleton_iff]
      exact ⟨fun h => ⟨h.1, h.2 hs⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
    rw [this]; exact h𝒰.inter (measurableSet_singleton _)
  · have : admissible 𝒰 b s = 𝒰 := by
      ext v; simp only [admissible, Set.mem_setOf_eq]
      exact ⟨fun h => h.1, fun h => ⟨h, fun h' => absurd h' hs⟩⟩
    rw [this]; exact h𝒰

lemma measurableSet_good (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰 : MeasurableSet 𝒰)
    (b : Fin r → LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    MeasurableSet {h : LinParamBandits.LowerBound.History r n | ∀ s : Fin n, (h s).1 ∈ admissible 𝒰 b s} := by
  have : {h : LinParamBandits.LowerBound.History r n | ∀ s : Fin n, (h s).1 ∈ admissible 𝒰 b s} =
      ⋂ s : Fin n, (fun h : LinParamBandits.LowerBound.History r n => (h s).1) ⁻¹' admissible 𝒰 b s := by
    ext h; simp
  rw [this]
  exact MeasurableSet.iInter fun s =>
    (measurable_fst.comp (measurable_pi_apply s)) (measurableSet_admissible 𝒰 h𝒰 b s)

lemma ae_good (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰 : MeasurableSet 𝒰)
    (b : Fin r → LinParamBandits.LowerBound.Vec r)
    (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ)
    (z : LinParamBandits.LowerBound.Vec r) (ψ : Policy r)
    (hact : ∀ t h, ψ.act t h ∈ 𝒰)
    (hinit : ∀ (t : ℕ) (h : LinParamBandits.LowerBound.History r t) (ht : t < r), ψ.act t h = b ⟨t, ht⟩) :
    ∀ n, ∀ᵐ h ∂(histMeasure ν z ψ n), ∀ s : Fin n, (h s).1 ∈ admissible 𝒰 b s
  | 0 => Filter.Eventually.of_forall (fun h s => Fin.elim0 s)
  | n + 1 => by
      have ih := ae_good 𝒰 h𝒰 b ν z ψ hact hinit n
      simp only [histMeasure]
      rw [ae_map_iff (measurable_step ψ z n).aemeasurable (measurableSet_good 𝒰 h𝒰 b (n + 1))]
      have hms : MeasurableSet {p : LinParamBandits.LowerBound.History r n × ℝ |
          ∀ s : Fin n, (p.1 s).1 ∈ admissible 𝒰 b s} :=
        measurable_fst (measurableSet_good 𝒰 h𝒰 b n)
      have h2 : ∀ᵐ p ∂((histMeasure ν z ψ n) ⊗ₘ (ν.comap (ψ.act n) (ψ.measurable_act n))),
          ∀ s : Fin n, (p.1 s).1 ∈ admissible 𝒰 b s := by
        apply Measure.ae_compProd_of_ae_ae hms
        filter_upwards [ih] with h hh
        exact Filter.Eventually.of_forall (fun _ => hh)
      filter_upwards [h2] with p hp
      intro s
      refine Fin.lastCases ?_ (fun j => ?_) s
      · simp only [Fin.snoc_last, Fin.val_last]
        exact ⟨hact n p.1, fun hs => hinit n p.1 hs⟩
      · simp only [Fin.snoc_castSucc, Fin.coe_castSucc]
        exact hp j

lemma inner_vec (x y : LinParamBandits.LowerBound.Vec r) :
    inner ℝ x y = x.ofLp ⬝ᵥ y.ofLp := by
  simp [PiLp.inner_apply, dotProduct, mul_comm]

lemma inner_Mvec (x z : LinParamBandits.LowerBound.Vec r) {n : ℕ}
    (h : LinParamBandits.LowerBound.History r n) :
    inner ℝ x (Mvec z h) = ∑ s, inner ℝ x (h s).1 * ((h s).2 - inner ℝ (h s).1 z) := by
  unfold Mvec
  rw [inner_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [inner_smul_right]
  ring

lemma quadForm_design {n : ℕ} (U : Fin n → LinParamBandits.LowerBound.Vec r)
    (x : LinParamBandits.LowerBound.Vec r) :
    quadForm (design U) x = ∑ s, inner ℝ x (U s) ^ 2 := by
  unfold quadForm design
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.vecMulVec_mulVec, dotProduct_smul, inner_vec]
  simp [dotProduct_comm (U s).ofLp x.ofLp, sq]

lemma numeric (t : ℝ) (ht : 2 ≤ t) (c : ℝ) (hc : 0 ≤ c) (y Q : ℝ) (hy : 0 < y) (hyQ : y ≤ Q)
    (hQ : Q ≤ t * c * y) :
    (Q + y) * (1 + 1 / 2 * Real.log (1 + Q / y)) ≤
      (4 * (1 + Real.log (1 + 36 * c))) * Real.log t * Q := by
  have hQ0 : 0 < Q := lt_of_lt_of_le hy hyQ
  have h1 : Q / y ≤ t * c := by rw [div_le_iff₀ hy]; linarith
  have hQy : 0 ≤ Q / y := by positivity
  have h2 : Real.log (1 + Q / y) ≤ Real.log t + Real.log (1 + c) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    nlinarith
  have hL : 2 / 3 < Real.log t := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
    linarith
  have h3 : Real.log (1 + c) ≤ Real.log (1 + 36 * c) :=
    Real.log_le_log (by positivity) (by linarith)
  have h4 : 0 ≤ Real.log (1 + c) := Real.log_nonneg (by linarith)
  have h5 : 0 ≤ Real.log (1 + Q / y) := Real.log_nonneg (by linarith)
  have key : 2 + Real.log t + Real.log (1 + c) ≤ 4 * (1 + Real.log (1 + 36 * c)) * Real.log t := by
    have : Real.log (1 + 36 * c) ≤ 4 * Real.log t * Real.log (1 + 36 * c) := by
      have h6 : 0 ≤ Real.log (1 + 36 * c) := by linarith
      nlinarith
    nlinarith
  calc (Q + y) * (1 + 1 / 2 * Real.log (1 + Q / y))
      ≤ (2 * Q) * (1 + 1 / 2 * (Real.log t + Real.log (1 + c))) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    _ = Q * (2 + Real.log t + Real.log (1 + c)) := by ring
    _ ≤ Q * (4 * (1 + Real.log (1 + 36 * c)) * Real.log t) :=
        mul_le_mul_of_nonneg_left key hQ0.le
    _ = _ := by ring

end UE3Core

open UE3Core LinParamBandits.UEGeneral in
theorem solution {r : ℕ} (hr : 2 ≤ r) {𝒰 : Set (LinParamBandits.LowerBound.Vec r)} (h𝒰c : IsCompact 𝒰) (h𝒰n : 𝒰.Nonempty)
    {ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ} [IsMarkovKernel ν] {b : Fin r → LinParamBandits.LowerBound.Vec r} {σ₀ ubar lam0 : ℝ}
    (hA : Assumption1 𝒰 ν b σ₀ ubar lam0) {ψ : Policy r} (hψ : IsUE 𝒰 b σ₀ ubar lam0 ψ)
    (x z : LinParamBandits.LowerBound.Vec r) (t : ℕ) (ht : r ≤ t) (ζ : ℝ) (hζ : Real.sqrt 2 ≤ ζ) :
    histMeasure ν z ψ t
        {h | ζ * kappa0 ubar lam0 * σ₀ * Real.sqrt (Real.log t) *
            wnorm (design (armsOf h)) x < |inner ℝ x (Mvec z h)|} =
      histMeasure ν z ψ t
        {h | ζ ^ 2 * kappa0 ubar lam0 ^ 2 * σ₀ ^ 2 * Real.log t *
            quadForm (design (armsOf h)) x < inner ℝ x (Mvec z h) ^ 2} ∧
    histMeasure ν z ψ t
        {h | ζ ^ 2 * kappa0 ubar lam0 ^ 2 * σ₀ ^ 2 * Real.log t *
            quadForm (design (armsOf h)) x < inner ℝ x (Mvec z h) ^ 2} ≤
      ENNReal.ofReal (Real.exp (-ζ ^ 2 / 2)) := by
  have hσ := hA.σ₀_pos
  have hlam := hA.lam0_pos
  have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast hr.trans ht
  have hL0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hζ0 : 0 < ζ := lt_of_lt_of_le (by positivity) hζ
  have hκ0 : 0 ≤ kappa0 ubar lam0 := by unfold kappa0; positivity
  have hX : 0 ≤ 1 + Real.log (1 + 36 * ubar ^ 2 / lam0) := by
    have : 0 ≤ Real.log (1 + 36 * ubar ^ 2 / lam0) := Real.log_nonneg (by
      have : 0 ≤ 36 * ubar ^ 2 / lam0 := by positivity
      linarith)
    linarith
  have hκsq : kappa0 ubar lam0 ^ 2 = 4 * (1 + Real.log (1 + 36 * (ubar ^ 2 / lam0))) := by
    unfold kappa0
    rw [mul_pow, Real.sq_sqrt hX, mul_div_assoc]
    norm_num
  have hset : {h : LinParamBandits.LowerBound.History r t | ζ * kappa0 ubar lam0 * σ₀ *
      Real.sqrt (Real.log t) * wnorm (design (armsOf h)) x < |inner ℝ x (Mvec z h)|} =
      {h | ζ ^ 2 * kappa0 ubar lam0 ^ 2 * σ₀ ^ 2 * Real.log t *
            quadForm (design (armsOf h)) x < inner ℝ x (Mvec z h) ^ 2} := by
    ext h
    simp only [Set.mem_setOf_eq]
    have hq : 0 ≤ quadForm (design (armsOf h)) x := by rw [quadForm_design]; positivity
    have hsq : (ζ * kappa0 ubar lam0 * σ₀ * Real.sqrt (Real.log t) *
        wnorm (design (armsOf h)) x) ^ 2 =
        ζ ^ 2 * kappa0 ubar lam0 ^ 2 * σ₀ ^ 2 * Real.log t * quadForm (design (armsOf h)) x := by
      unfold wnorm
      rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hq, Real.sq_sqrt hL0]
    rw [← hsq, ← sq_abs (inner ℝ x (Mvec z h)),
      pow_lt_pow_iff_left₀ (by unfold wnorm; positivity) (abs_nonneg _) two_ne_zero]
  refine ⟨by rw [hset], ?_⟩
  rw [← hset]
  haveI := isProb_histMeasure ν z ψ t
  by_cases hx : x = 0
  · have : {h : LinParamBandits.LowerBound.History r t | ζ * kappa0 ubar lam0 * σ₀ *
        Real.sqrt (Real.log t) * wnorm (design (armsOf h)) x < |inner ℝ x (Mvec z h)|} = ∅ := by
      ext h
      simp [hx, wnorm, quadForm]
    rw [this, measure_empty]
    exact bot_le
  set y := lam0 * ‖x‖ ^ 2 with hy_def
  have hy : 0 < y := by
    have : 0 < ‖x‖ := norm_pos_iff.mpr hx
    positivity
  set c := ubar ^ 2 / lam0 with hc_def
  have hc : 0 ≤ c := by positivity
  let A : LinParamBandits.LowerBound.History r t → ℝ := fun h =>
    (∑ s, inner ℝ x (h s).1 * ((h s).2 - inner ℝ (h s).1 z)) / σ₀
  let B : LinParamBandits.LowerBound.History r t → ℝ := fun h =>
    Real.sqrt (∑ s, inner ℝ x (h s).1 ^ 2)
  have hAm : Measurable A := by fun_prop
  have hBm : Measurable B := by fun_prop
  have hexp : ∀ γ : ℝ, ∫⁻ h, ENNReal.ofReal (Real.exp (γ * A h - γ ^ 2 * B h ^ 2 / 2))
      ∂(histMeasure ν z ψ t) ≤ 1 := by
    intro γ
    refine le_trans (le_of_eq (lintegral_congr fun h => ?_))
      (core_exp 𝒰 ν σ₀ hA.mgf_le z ψ hψ.act_mem x (γ / σ₀) t)
    congr 2
    simp only [A, B, G]
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hB3 := exp_ineq_ratios (P := histMeasure ν z ψ t) hAm hBm
    (Filter.Eventually.of_forall fun h => Real.sqrt_nonneg _) hexp ζ hζ y hy
  refine le_trans (measure_mono_ae ?_) hB3
  filter_upwards [ae_good 𝒰 h𝒰c.isClosed.measurableSet b ν z ψ hψ.act_mem hψ.act_init t]
    with h hh
  intro hin
  change ζ * kappa0 ubar lam0 * σ₀ * Real.sqrt (Real.log t) * wnorm (design (armsOf h)) x <
    |inner ℝ x (Mvec z h)| at hin
  show ζ * Real.sqrt ((B h ^ 2 + y) * (1 + 1 / 2 * Real.log (1 + B h ^ 2 / y))) ≤ |A h|
  set Q := ∑ s, inner ℝ x (h s).1 ^ 2 with hQ_def
  have hQ0 : 0 ≤ Q := by positivity
  have hBQ : B h ^ 2 = Q := Real.sq_sqrt hQ0
  rw [hBQ]
  have hw : wnorm (design (armsOf h)) x = Real.sqrt Q := by
    unfold wnorm; rw [quadForm_design]; rfl
  rw [hw, inner_Mvec] at hin
  -- lower bound
  have hyQ : y ≤ Q := by
    refine (hA.b_minEig x).trans ?_
    calc ∑ k : Fin r, inner ℝ (b k) x ^ 2
        = ∑ k : Fin r, inner ℝ x (h (Fin.castLE ht k)).1 ^ 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have := (hh (Fin.castLE ht k)).2 (by simp)
          rw [this, real_inner_comm]
          simp
      _ = ∑ s ∈ Finset.univ.map (Fin.castLEEmb ht), inner ℝ x (h s).1 ^ 2 := by
          rw [Finset.sum_map]; rfl
      _ ≤ Q := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => sq_nonneg _)
  have hQle : Q ≤ t * c * y := by
    have hterm : ∀ s : Fin t, inner ℝ x (h s).1 ^ 2 ≤ (‖x‖ * ubar) ^ 2 := by
      intro s
      have h1 := abs_real_inner_le_norm x (h s).1
      have h2 : ‖(h s).1‖ ≤ ubar := hA.norm_le _ (hh s).1
      rw [← sq_abs]
      have : ‖x‖ * ‖(h s).1‖ ≤ ‖x‖ * ubar := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans this) 2
    calc Q ≤ ∑ _s : Fin t, (‖x‖ * ubar) ^ 2 := Finset.sum_le_sum fun s _ => hterm s
      _ = t * c * y := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc_def,
            hy_def]
          field_simp
  have hnum := numeric t ht2 c hc y Q hy hyQ hQle
  rw [← hκsq] at hnum
  have hsq : Real.sqrt ((Q + y) * (1 + 1 / 2 * Real.log (1 + Q / y))) ≤
      kappa0 ubar lam0 * Real.sqrt (Real.log t) * Real.sqrt Q := by
    calc _ ≤ Real.sqrt (kappa0 ubar lam0 ^ 2 * Real.log t * Q) := Real.sqrt_le_sqrt hnum
      _ = _ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hκ0]
  have hAabs : |A h| = |∑ s, inner ℝ x (h s).1 * ((h s).2 - inner ℝ (h s).1 z)| / σ₀ := by
    simp only [A]; rw [abs_div, abs_of_pos hσ]
  rw [hAabs, le_div_iff₀ hσ]
  calc ζ * Real.sqrt ((Q + y) * (1 + 1 / 2 * Real.log (1 + Q / y))) * σ₀
      ≤ ζ * (kappa0 ubar lam0 * Real.sqrt (Real.log t) * Real.sqrt Q) * σ₀ := by gcongr
    _ = ζ * kappa0 ubar lam0 * σ₀ * Real.sqrt (Real.log t) * Real.sqrt Q := by ring
    _ ≤ _ := hin.le
