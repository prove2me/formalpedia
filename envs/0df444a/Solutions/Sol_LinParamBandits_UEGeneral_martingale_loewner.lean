-- Prove2me | solution 1 for LinParamBandits.UEGeneral.martingale_loewner
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T21:33:33.045225+00:00
-- url     : https://prove2.me/submissions/e6d68053-e5e2-4a6c-9379-1de7173d8e17

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy
import Theorems.Thm_LinParamBandits_UEGeneral_martingale_ineq

open MeasureTheory ProbabilityTheory

namespace UE3Core

open Matrix

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


lemma lower_sum {𝒰 : Set (LinParamBandits.LowerBound.Vec r)} {b : Fin r → LinParamBandits.LowerBound.Vec r}
    {lam0 : ℝ} (hb : ∀ x : LinParamBandits.LowerBound.Vec r, lam0 * ‖x‖ ^ 2 ≤ ∑ k, (inner ℝ (b k) x) ^ 2)
    {t : ℕ} (ht : r ≤ t) (h : LinParamBandits.LowerBound.History r t)
    (hh : ∀ s : Fin t, (h s).1 ∈ admissible 𝒰 b s) (x : LinParamBandits.LowerBound.Vec r) :
    lam0 * ‖x‖ ^ 2 ≤ ∑ s, inner ℝ x (h s).1 ^ 2 := by
  refine (hb x).trans ?_
  calc ∑ k : Fin r, inner ℝ (b k) x ^ 2
      = ∑ k : Fin r, inner ℝ x (h (Fin.castLE ht k)).1 ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have := (hh (Fin.castLE ht k)).2 (by simp)
        rw [this, real_inner_comm]
        simp
    _ = ∑ s ∈ Finset.univ.map (Fin.castLEEmb ht), inner ℝ x (h s).1 ^ 2 := by
        rw [Finset.sum_map]; rfl
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)


/-- Grid points `k / N` with `k ∈ {-N, …, N}^r`. -/
noncomputable def grid (N : ℕ) (k : Fin r → ℤ) : LinParamBandits.LowerBound.Vec r :=
  WithLp.toLp 2 (fun i => (k i : ℝ) / N)

lemma net (N : ℕ) (hN : 0 < N) (x : LinParamBandits.LowerBound.Vec r) (hx : ‖x‖ ≤ 1) :
    ∃ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(N : ℤ)) N),
      ‖x - grid N k‖ ^ 2 ≤ r / (N : ℝ) ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨fun i => ⌊x i * N⌋, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]
    intro i
    have hxi : |x i| ≤ 1 := by
      have := PiLp.norm_apply_le x i
      rw [Real.norm_eq_abs] at this
      linarith
    have h1 : -(N : ℝ) ≤ x i * N := by
      have := neg_abs_le (x i); nlinarith
    have h2 : x i * N ≤ N := by
      have := le_abs_self (x i); nlinarith
    rw [Finset.mem_Icc]
    constructor
    · apply Int.le_floor.mpr; push_cast; exact h1
    · have := Int.floor_le (x i * N)
      have : (⌊x i * N⌋ : ℝ) ≤ N := by linarith
      exact_mod_cast this
  · rw [EuclideanSpace.real_norm_sq_eq]
    have hterm : ∀ i, ((x - grid N (fun i => ⌊x i * N⌋)) i) ^ 2 ≤ 1 / (N : ℝ) ^ 2 := by
      intro i
      have e : (x - grid N (fun i => ⌊x i * N⌋)) i = (x i * N - ⌊x i * N⌋) / N := by
        simp only [grid, PiLp.sub_apply]
        field_simp
      rw [e, div_pow]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h0 := Int.floor_le (x i * N)
      have h1 := Int.lt_floor_add_one (x i * N)
      rw [sq_le_one_iff_abs_le_one, abs_le]
      constructor <;> linarith
    calc ∑ i, ((x - grid N (fun i => ⌊x i * N⌋)) i) ^ 2 ≤ ∑ _i : Fin r, 1 / (N : ℝ) ^ 2 :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = r / (N : ℝ) ^ 2 := by simp [div_eq_mul_inv]

lemma card_grid (N : ℕ) :
    ((Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(N : ℤ)) N)).image (grid N)).card ≤
      (2 * N + 1) ^ r := by
  refine Finset.card_image_le.trans ?_
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
  apply le_of_eq
  congr 1
  omega

lemma three_four (r : ℕ) (hr : 1 ≤ r) : 3 ^ r + 1 ≤ 4 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ, pow_succ]; omega

lemma count_bound (r t : ℕ) (hr : 2 ≤ r) (ht : r ≤ t) (c : ℝ) (hc : 1 / (r : ℝ) ≤ c) (N : ℕ)
    (hN : (N : ℝ) ≤ 9 * c * t * Real.sqrt r + 1) :
    (r : ℝ) + ((2 * N + 1 : ℕ) : ℝ) ^ r ≤
      (t : ℝ) ^ ((r : ℝ) * (4 * (1 + Real.log (1 + 36 * c)))) := by
  have hr0 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have htr : (r : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (2 : ℝ) ≤ t := by linarith
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc
  have hsr : 1 ≤ Real.sqrt r := by rw [Real.one_le_sqrt]; linarith
  have hsr2 : Real.sqrt r ≤ r := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  set a := 9 * c * t * Real.sqrt r with ha
  have hct : 1 ≤ c * t := by
    have : 1 / (r : ℝ) * r ≤ c * t := mul_le_mul hc htr (by positivity) hc0.le
    rw [div_mul_cancel₀ _ (by positivity)] at this; exact this
  have ha3 : 3 ≤ a := by
    have : 1 ≤ c * t * Real.sqrt r := by nlinarith
    nlinarith
  have h1 : ((2 * N + 1 : ℕ) : ℝ) ≤ 3 * a := by push_cast; linarith
  have h2 : ((2 * N + 1 : ℕ) : ℝ) ^ r ≤ 3 ^ r * a ^ r := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 r
  have h3 : (r : ℝ) ≤ a ^ r := by
    have : (r : ℝ) ≤ 2 ^ r := by exact_mod_cast (Nat.lt_two_pow_self).le
    exact this.trans (pow_le_pow_left₀ (by norm_num) (by linarith) r)
  have h34 : (3 : ℝ) ^ r + 1 ≤ 4 ^ r := by exact_mod_cast three_four r (by omega)
  have h4 : (r : ℝ) + ((2 * N + 1 : ℕ) : ℝ) ^ r ≤ (4 * a) ^ r := by
    rw [mul_pow]
    have : 0 ≤ a ^ r := by positivity
    nlinarith
  have h5 : 4 * a ≤ 36 * c * (t : ℝ) ^ 2 := by
    have : Real.sqrt r ≤ t := hsr2.trans htr
    rw [ha]
    have : 0 ≤ c * t := by positivity
    nlinarith
  have hL : 2 / 3 < Real.log t := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht0
    linarith
  have hl36 : 0 ≤ Real.log (1 + 36 * c) := Real.log_nonneg (by linarith)
  have h6 : 36 * c * (t : ℝ) ^ 2 ≤ (t : ℝ) ^ (4 * (1 + Real.log (1 + 36 * c))) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    calc 36 * c * (t : ℝ) ^ 2 ≤ (1 + 36 * c) * (t : ℝ) ^ 2 := by nlinarith
      _ = Real.exp (Real.log (1 + 36 * c) + 2 * Real.log t) := by
          rw [Real.exp_add, Real.exp_log (by linarith), ← Real.log_rpow (by linarith),
            Real.exp_log (by positivity)]
          norm_num
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          nlinarith
  calc (r : ℝ) + ((2 * N + 1 : ℕ) : ℝ) ^ r ≤ (4 * a) ^ r := h4
    _ ≤ ((t : ℝ) ^ (4 * (1 + Real.log (1 + 36 * c)))) ^ r :=
        pow_le_pow_left₀ (by positivity) (h5.trans h6) r
    _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), mul_comm]

/-- The deterministic covering step for a unit vector. -/
lemma unit_step {t : ℕ} (U : Fin t → LinParamBandits.LowerBound.Vec r)
    (M x y : LinParamBandits.LowerBound.Vec r) (β δ ubar lam0 : ℝ) (hβ : 0 ≤ β) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hx : ‖x‖ = 1) (hxy : ‖x - y‖ ≤ δ) (hU : ∀ s, ‖U s‖ ≤ ubar)
    (hy : inner ℝ y M ^ 2 ≤ β / 2 * ∑ s, inner ℝ y (U s) ^ 2)
    (hMn : ‖M‖ ^ 2 ≤ β * (t * ubar ^ 2))
    (hlow : lam0 ≤ ∑ s, inner ℝ x (U s) ^ 2) (hδ : 9 * (δ * t * ubar ^ 2) ≤ lam0) :
    inner ℝ x M ^ 2 ≤ β * ∑ s, inner ℝ x (U s) ^ 2 := by
  have hyn : ‖y‖ ≤ 1 + δ := by
    have := norm_sub_norm_le x y
    have : ‖x‖ - ‖y‖ ≥ -‖x - y‖ := by
      have := abs_norm_sub_norm_le x y
      rw [abs_le] at this; linarith
    linarith
  have hxy3 : ‖x + y‖ ≤ 3 := by
    have := norm_add_le x y; linarith
  have hprod : ∀ v : LinParamBandits.LowerBound.Vec r, inner ℝ x v ^ 2 - inner ℝ y v ^ 2 ≤
      3 * δ * ‖v‖ ^ 2 := by
    intro v
    have e : inner ℝ x v ^ 2 - inner ℝ y v ^ 2 = inner ℝ (x - y) v * inner ℝ (x + y) v := by
      rw [inner_sub_left, inner_add_left]; ring
    rw [e]
    have h1 := abs_real_inner_le_norm (x - y) v
    have h2 := abs_real_inner_le_norm (x + y) v
    calc inner ℝ (x - y) v * inner ℝ (x + y) v ≤ |inner ℝ (x - y) v| * |inner ℝ (x + y) v| := by
          rw [← abs_mul]; exact le_abs_self _
      _ ≤ (δ * ‖v‖) * (3 * ‖v‖) := by
          apply mul_le_mul _ _ (abs_nonneg _) (by positivity)
          · exact h1.trans (mul_le_mul_of_nonneg_right hxy (norm_nonneg _))
          · exact h2.trans (mul_le_mul_of_nonneg_right hxy3 (norm_nonneg _))
      _ = 3 * δ * ‖v‖ ^ 2 := by ring
  have hqy : ∑ s, inner ℝ y (U s) ^ 2 ≤ ∑ s, inner ℝ x (U s) ^ 2 + 3 * (δ * t * ubar ^ 2) := by
    have : ∀ s, inner ℝ y (U s) ^ 2 ≤ inner ℝ x (U s) ^ 2 + 3 * δ * ubar ^ 2 := by
      intro s
      have hyx : ‖y - x‖ ≤ δ := by rw [norm_sub_rev]; exact hxy
      have e : inner ℝ y (U s) ^ 2 - inner ℝ x (U s) ^ 2 =
          inner ℝ (y - x) (U s) * inner ℝ (y + x) (U s) := by
        rw [inner_sub_left, inner_add_left]; ring
      have h1 := abs_real_inner_le_norm (y - x) (U s)
      have h2 := abs_real_inner_le_norm (y + x) (U s)
      have hyx3 : ‖y + x‖ ≤ 3 := by rw [add_comm]; exact hxy3
      have hUs := hU s
      have hU0 : 0 ≤ ‖U s‖ := norm_nonneg _
      have : inner ℝ (y - x) (U s) * inner ℝ (y + x) (U s) ≤ (δ * ubar) * (3 * ubar) := by
        calc _ ≤ |inner ℝ (y - x) (U s)| * |inner ℝ (y + x) (U s)| := by
              rw [← abs_mul]; exact le_abs_self _
          _ ≤ (δ * ubar) * (3 * ubar) := by
              apply mul_le_mul _ _ (abs_nonneg _) (by nlinarith)
              · exact h1.trans (mul_le_mul hyx hUs hU0 hδ0)
              · exact h2.trans (mul_le_mul hyx3 hUs hU0 (by norm_num))
      nlinarith
    calc ∑ s, inner ℝ y (U s) ^ 2 ≤ ∑ s, (inner ℝ x (U s) ^ 2 + 3 * δ * ubar ^ 2) :=
          Finset.sum_le_sum fun s _ => this s
      _ = _ := by
          rw [Finset.sum_add_distrib]; simp; ring
  have hM := hprod M
  have k1 : β / 2 * ∑ s, inner ℝ y (U s) ^ 2 ≤
      β / 2 * (∑ s, inner ℝ x (U s) ^ 2 + 3 * (δ * t * ubar ^ 2)) :=
    mul_le_mul_of_nonneg_left hqy (by positivity)
  have k2 : 3 * δ * ‖M‖ ^ 2 ≤ 3 * δ * (β * (t * ubar ^ 2)) :=
    mul_le_mul_of_nonneg_left hMn (by positivity)
  have k3 : β * (9 * (δ * t * ubar ^ 2)) ≤ β * ∑ s, inner ℝ x (U s) ^ 2 :=
    mul_le_mul_of_nonneg_left (hδ.trans hlow) hβ
  nlinarith

/-- Homogeneity: from unit vectors to all vectors. -/
lemma all_dirs {t : ℕ} (U : Fin t → LinParamBandits.LowerBound.Vec r)
    (M : LinParamBandits.LowerBound.Vec r) (β : ℝ)
    (hunit : ∀ x : LinParamBandits.LowerBound.Vec r, ‖x‖ = 1 →
      inner ℝ x M ^ 2 ≤ β * ∑ s, inner ℝ x (U s) ^ 2)
    (v : LinParamBandits.LowerBound.Vec r) :
    inner ℝ v M ^ 2 ≤ β * ∑ s, inner ℝ v (U s) ^ 2 := by
  by_cases hv : v = 0
  · subst hv; simp
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h := hunit (‖v‖⁻¹ • v) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
  simp only [inner_smul_left, conj_trivial, mul_pow] at h
  rw [← Finset.mul_sum] at h
  have hn2 : 0 < (‖v‖⁻¹) ^ 2 := by positivity
  nlinarith

lemma lam_le {b : Fin r → LinParamBandits.LowerBound.Vec r} {lam0 ubar : ℝ} (hr : 1 ≤ r)
    (hb : ∀ x : LinParamBandits.LowerBound.Vec r, lam0 * ‖x‖ ^ 2 ≤ ∑ k, (inner ℝ (b k) x) ^ 2)
    (hbn : ∀ k, ‖b k‖ ≤ ubar) : lam0 ≤ r * ubar ^ 2 := by
  have h := hb (EuclideanSpace.single ⟨0, hr⟩ 1)
  rw [EuclideanSpace.norm_single, norm_one, one_pow, mul_one] at h
  refine h.trans ?_
  calc ∑ k, inner ℝ (b k) (EuclideanSpace.single ⟨0, hr⟩ (1 : ℝ)) ^ 2 ≤ ∑ _k : Fin r, ubar ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        have h1 := abs_real_inner_le_norm (b k) (EuclideanSpace.single ⟨0, hr⟩ (1 : ℝ))
        rw [EuclideanSpace.norm_single, norm_one, mul_one] at h1
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans (hbn k)) 2
    _ = r * ubar ^ 2 := by simp

lemma design_transpose {n : ℕ} (U : Fin n → LinParamBandits.LowerBound.Vec r) :
    (design U)ᵀ = design U := by
  unfold design
  rw [Matrix.transpose_sum]
  simp [Matrix.transpose_vecMulVec]

end UE3Core

open UE3Core LinParamBandits.UEGeneral Matrix in
theorem solution {r : ℕ} (hr : 2 ≤ r) {𝒰 : Set (LinParamBandits.LowerBound.Vec r)} (h𝒰c : IsCompact 𝒰) (h𝒰n : 𝒰.Nonempty)
    {ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ} [IsMarkovKernel ν] {b : Fin r → LinParamBandits.LowerBound.Vec r} {σ₀ ubar lam0 : ℝ}
    (hA : Assumption1 𝒰 ν b σ₀ ubar lam0) {ψ : Policy r} (hψ : IsUE 𝒰 b σ₀ ubar lam0 ψ)
    (z : LinParamBandits.LowerBound.Vec r) (t : ℕ) (ht : r ≤ t) (ζ : ℝ) (hζ : 2 ≤ ζ) :
    ENNReal.ofReal (1 - (t : ℝ) ^ ((r : ℝ) * kappa0 ubar lam0 ^ 2) * Real.exp (-ζ ^ 2 / 4)) ≤
      histMeasure ν z ψ t
        {h | ((ζ ^ 2 * kappa0 ubar lam0 ^ 2 * σ₀ ^ 2 * Real.log t) • design (armsOf h) -
            Matrix.vecMulVec (Mvec z h).ofLp (Mvec z h).ofLp).PosSemidef} := by
  have hσ := hA.σ₀_pos
  have hlam := hA.lam0_pos
  have hub := hA.ubar_pos
  have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast hr.trans ht
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have htr : (r : ℝ) ≤ t := by exact_mod_cast ht
  have hL0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hX : 0 ≤ 1 + Real.log (1 + 36 * ubar ^ 2 / lam0) := by
    have : 0 ≤ Real.log (1 + 36 * ubar ^ 2 / lam0) := Real.log_nonneg (by
      have : 0 ≤ 36 * ubar ^ 2 / lam0 := by positivity
      linarith)
    linarith
  have hκsq : kappa0 ubar lam0 ^ 2 = 4 * (1 + Real.log (1 + 36 * (ubar ^ 2 / lam0))) := by
    unfold kappa0
    rw [mul_pow, Real.sq_sqrt hX, mul_div_assoc]
    norm_num
  set β := ζ ^ 2 * kappa0 ubar lam0 ^ 2 * σ₀ ^ 2 * Real.log t with hβ
  have hβ0 : 0 ≤ β := by positivity
  set c := ubar ^ 2 / lam0 with hc_def
  have hlamr : lam0 ≤ r * ubar ^ 2 :=
    lam_le (by omega) hA.b_minEig (fun k => hA.norm_le _ (hA.b_mem k))
  have hc : 1 / (r : ℝ) ≤ c := by
    rw [hc_def, div_le_div_iff₀ (by positivity) hlam]; linarith
  set δ := lam0 / (9 * ubar ^ 2 * t) with hδ_def
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ_def, div_le_one (by positivity)]
    nlinarith
  have hδeq : 9 * (δ * t * ubar ^ 2) = lam0 := by
    rw [hδ_def]; field_simp
  set N := ⌈Real.sqrt r / δ⌉₊ with hN_def
  have hN0 : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hNge : Real.sqrt r / δ ≤ N := Nat.le_ceil _
  have hNle : (N : ℝ) ≤ 9 * c * t * Real.sqrt r + 1 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ Real.sqrt r / δ by positivity)
    have e : Real.sqrt r / δ = 9 * c * t * Real.sqrt r := by
      rw [hδ_def, hc_def]; field_simp
    rw [← hN_def, e] at this
    linarith
  set X := (Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(N : ℤ)) N)).image (grid N) with hX_def
  have hcover : ∀ x : LinParamBandits.LowerBound.Vec r, ‖x‖ = 1 → ∃ y ∈ X, ‖x - y‖ ≤ δ := by
    intro x hx
    obtain ⟨k, hk, hk2⟩ := net N hN0 x hx.le
    refine ⟨grid N k, Finset.mem_image_of_mem _ hk, ?_⟩
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
    have h1 : (r : ℝ) / (N : ℝ) ^ 2 ≤ δ ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : Real.sqrt r ≤ N * δ := by rwa [div_le_iff₀ hδ0] at hNge
      have h2 : (Real.sqrt r) ^ 2 ≤ (N * δ) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
      rw [Real.sq_sqrt (by positivity)] at h2
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hδ0.le two_ne_zero).mp (hk2.trans h1)
  -- the bad events of Lemma B.4
  let bad : LinParamBandits.LowerBound.Vec r → ℝ → Set (LinParamBandits.LowerBound.History r t) :=
    fun v ζ' => {h | ζ' ^ 2 * kappa0 ubar lam0 ^ 2 * σ₀ ^ 2 * Real.log t *
      quadForm (design (armsOf h)) v < inner ℝ v (Mvec z h) ^ 2}
  have hbad : ∀ v ζ', Real.sqrt 2 ≤ ζ' →
      histMeasure ν z ψ t (bad v ζ') ≤ ENNReal.ofReal (Real.exp (-ζ' ^ 2 / 2)) :=
    fun v ζ' h => (martingale_ineq hr h𝒰c h𝒰n hA hψ v z t ht ζ' h).2
  let e : Fin r → LinParamBandits.LowerBound.Vec r := fun i => EuclideanSpace.single i 1
  set ζ2 := ζ / Real.sqrt 2 with hζ2
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hζ2sq : ζ2 ^ 2 = ζ ^ 2 / 2 := by
    rw [hζ2, div_pow, Real.sq_sqrt (by norm_num)]
  have hζ2ge : Real.sqrt 2 ≤ ζ2 := by
    rw [hζ2, le_div_iff₀ hs2, Real.mul_self_sqrt (by norm_num)]; linarith
  have hζge : Real.sqrt 2 ≤ ζ := by
    have : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  let G : Set (LinParamBandits.LowerBound.History r t) :=
    {h | (∀ i, h ∉ bad (e i) ζ) ∧ ∀ y ∈ X, h ∉ bad y ζ2}
  have hGc : Gᶜ ⊆ (⋃ i, bad (e i) ζ) ∪ ⋃ y ∈ X, bad y ζ2 := by
    intro h hh
    rw [Set.mem_compl_iff] at hh
    simp only [G, Set.mem_setOf_eq, not_and_or, not_forall, not_not] at hh
    rcases hh with ⟨i, hi⟩ | ⟨y, hy, hyb⟩
    · left; exact Set.mem_iUnion.mpr ⟨i, hi⟩
    · right; exact Set.mem_biUnion hy hyb
  set p := (t : ℝ) ^ ((r : ℝ) * kappa0 ubar lam0 ^ 2) * Real.exp (-ζ ^ 2 / 4) with hp_def
  have hp0 : 0 ≤ p := by positivity
  have hGcm : histMeasure ν z ψ t Gᶜ ≤ ENNReal.ofReal p := by
    calc histMeasure ν z ψ t Gᶜ
        ≤ histMeasure ν z ψ t ((⋃ i, bad (e i) ζ) ∪ ⋃ y ∈ X, bad y ζ2) := measure_mono hGc
      _ ≤ histMeasure ν z ψ t (⋃ i, bad (e i) ζ) + histMeasure ν z ψ t (⋃ y ∈ X, bad y ζ2) :=
          measure_union_le _ _
      _ ≤ (∑ i, histMeasure ν z ψ t (bad (e i) ζ)) + ∑ y ∈ X, histMeasure ν z ψ t (bad y ζ2) :=
          add_le_add (measure_iUnion_fintype_le _ _) (measure_biUnion_finset_le _ _)
      _ ≤ (∑ _i : Fin r, ENNReal.ofReal (Real.exp (-ζ ^ 2 / 2))) +
            ∑ _y ∈ X, ENNReal.ofReal (Real.exp (-ζ ^ 2 / 4)) := by
          gcongr with i _ y _
          · exact hbad _ _ hζge
          · have := hbad y ζ2 hζ2ge
            rw [hζ2sq] at this
            rwa [show -(ζ ^ 2 / 2) / 2 = -ζ ^ 2 / 4 by ring] at this
      _ = ENNReal.ofReal (r * Real.exp (-ζ ^ 2 / 2) + X.card * Real.exp (-ζ ^ 2 / 4)) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            nsmul_eq_mul, ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal p := by
          apply ENNReal.ofReal_le_ofReal
          have hcard : (X.card : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) ^ r := by
            have := card_grid (r := r) N
            exact_mod_cast this
          have hcb := count_bound r t hr ht c hc N hNle
          rw [← hκsq] at hcb
          have he : Real.exp (-ζ ^ 2 / 2) ≤ Real.exp (-ζ ^ 2 / 4) :=
            Real.exp_le_exp.mpr (by nlinarith)
          have he0 : 0 < Real.exp (-ζ ^ 2 / 4) := Real.exp_pos _
          rw [hp_def]
          calc (r : ℝ) * Real.exp (-ζ ^ 2 / 2) + X.card * Real.exp (-ζ ^ 2 / 4)
              ≤ r * Real.exp (-ζ ^ 2 / 4) + ((2 * N + 1 : ℕ) : ℝ) ^ r * Real.exp (-ζ ^ 2 / 4) := by
                gcongr
            _ = ((r : ℝ) + ((2 * N + 1 : ℕ) : ℝ) ^ r) * Real.exp (-ζ ^ 2 / 4) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hcb he0.le
  -- on `G` (and a.s.), the matrix inequality holds
  have hGsub : histMeasure ν z ψ t G ≤ histMeasure ν z ψ t
      {h | (β • design (armsOf h) - Matrix.vecMulVec (Mvec z h).ofLp (Mvec z h).ofLp).PosSemidef} := by
    apply measure_mono_ae
    filter_upwards [ae_good 𝒰 h𝒰c.isClosed.measurableSet b ν z ψ hψ.act_mem hψ.act_init t]
      with h hh
    intro hG
    obtain ⟨hGe, hGy⟩ := hG
    set M := Mvec z h
    have hUn : ∀ s, ‖(h s).1‖ ≤ ubar := fun s => hA.norm_le _ (hh s).1
    have hqd : ∀ v, quadForm (design (armsOf h)) v = ∑ s, inner ℝ v (h s).1 ^ 2 := fun v => by
      rw [quadForm_design]; rfl
    have hMn : ‖M‖ ^ 2 ≤ β * (t * ubar ^ 2) := by
      have hei : ∀ i, M i ^ 2 ≤ β * ∑ s, ((h s).1 i) ^ 2 := by
        intro i
        have h1 := hGe i
        simp only [bad, Set.mem_setOf_eq, not_lt, hqd] at h1
        have hin : ∀ v : LinParamBandits.LowerBound.Vec r, inner ℝ (e i) v = v i := by
          intro v
          simp [e, EuclideanSpace.inner_single_left]
        rw [hin] at h1
        simp only [hin] at h1
        exact h1
      rw [EuclideanSpace.real_norm_sq_eq]
      calc ∑ i, M i ^ 2 ≤ ∑ i, β * ∑ s, ((h s).1 i) ^ 2 := Finset.sum_le_sum fun i _ => hei i
        _ = β * ∑ s, ‖(h s).1‖ ^ 2 := by
            rw [← Finset.mul_sum, Finset.sum_comm]
            congr 1
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [EuclideanSpace.real_norm_sq_eq]
        _ ≤ β * (t * ubar ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hβ0
            calc ∑ s, ‖(h s).1‖ ^ 2 ≤ ∑ _s : Fin t, ubar ^ 2 :=
                  Finset.sum_le_sum fun s _ => pow_le_pow_left₀ (norm_nonneg _) (hUn s) 2
              _ = t * ubar ^ 2 := by simp
    have hunit : ∀ x : LinParamBandits.LowerBound.Vec r, ‖x‖ = 1 →
        inner ℝ x M ^ 2 ≤ β * ∑ s, inner ℝ x (h s).1 ^ 2 := by
      intro x hx
      obtain ⟨y, hyX, hxy⟩ := hcover x hx
      have hy := hGy y hyX
      simp only [bad, Set.mem_setOf_eq, not_lt, hqd, hζ2sq] at hy
      have hy' : inner ℝ y M ^ 2 ≤ β / 2 * ∑ s, inner ℝ y (h s).1 ^ 2 := by
        rw [hβ]; linarith
      have hlow : lam0 ≤ ∑ s, inner ℝ x (h s).1 ^ 2 := by
        have := lower_sum hA.b_minEig ht h hh x
        rw [hx] at this; simpa using this
      exact unit_step (fun s => (h s).1) M x y β δ ubar lam0 hβ0 hδ0.le hδ1 hx hxy hUn hy' hMn
        hlow hδeq.le
    show (β • design (armsOf h) - Matrix.vecMulVec M.ofLp M.ofLp).PosSemidef
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
        Matrix.transpose_smul, design_transpose, Matrix.transpose_vecMulVec]
    · intro v
      simp only [star_trivial]
      have hv := all_dirs (fun s => (h s).1) M β hunit (WithLp.toLp 2 v)
      have e1 : v ⬝ᵥ ((β • design (armsOf h) - Matrix.vecMulVec M.ofLp M.ofLp) *ᵥ v) =
          β * (v ⬝ᵥ (design (armsOf h) *ᵥ v)) - (M.ofLp ⬝ᵥ v) * (v ⬝ᵥ M.ofLp) := by
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, dotProduct_sub,
          dotProduct_smul, dotProduct_smul, smul_eq_mul]
        simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
        ring
      have e2 : v ⬝ᵥ (design (armsOf h) *ᵥ v) = ∑ s, inner ℝ (WithLp.toLp 2 v :
          LinParamBandits.LowerBound.Vec r) (h s).1 ^ 2 := by
        have := hqd (WithLp.toLp 2 v)
        unfold quadForm at this
        simpa using this
      have e3 : inner ℝ (WithLp.toLp 2 v : LinParamBandits.LowerBound.Vec r) M = v ⬝ᵥ M.ofLp := by
        rw [inner_vec]
      rw [e1, e2, dotProduct_comm M.ofLp v, ← e3, ← sq]
      linarith
  -- conclude
  haveI := isProb_histMeasure ν z ψ t
  have h1 : (1 : ENNReal) ≤ histMeasure ν z ψ t G + histMeasure ν z ψ t Gᶜ := by
    rw [← measure_univ (μ := histMeasure ν z ψ t), ← Set.union_compl_self G]
    exact measure_union_le _ _
  refine le_trans ?_ hGsub
  rw [ENNReal.ofReal_sub _ hp0, ENNReal.ofReal_one, tsub_le_iff_right]
  exact h1.trans (add_le_add le_rfl hGcm)
