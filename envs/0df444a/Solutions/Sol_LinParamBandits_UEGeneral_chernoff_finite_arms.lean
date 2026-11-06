-- Prove2me | solution 1 for LinParamBandits.UEGeneral.chernoff_finite_arms
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T21:23:42.939027+00:00
-- url     : https://prove2.me/submissions/10836fb3-98c4-4289-8ac2-f44780f2ce20

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy

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

lemma design_transpose {n : ℕ} (U : Fin n → LinParamBandits.LowerBound.Vec r) :
    (design U)ᵀ = design U := by
  unfold design
  rw [Matrix.transpose_sum]
  simp [Matrix.transpose_vecMulVec]

lemma design_det_ne {n : ℕ} (U : Fin n → LinParamBandits.LowerBound.Vec r)
    (hpos : ∀ x : LinParamBandits.LowerBound.Vec r, x ≠ 0 → 0 < ∑ s, inner ℝ x (U s) ^ 2) :
    (design U).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hDv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hx : (WithLp.toLp 2 v : LinParamBandits.LowerBound.Vec r) ≠ 0 := by
    intro h; apply hv
    have := congrArg WithLp.ofLp h
    simpa using this
  have h1 := hpos _ hx
  rw [← quadForm_design] at h1
  unfold quadForm at h1
  simp [hDv] at h1

lemma sum_eq (z : LinParamBandits.LowerBound.Vec r) {n : ℕ} (h : LinParamBandits.LowerBound.History r n) :
    (∑ s, (h s).2 • (h s).1).ofLp = design (armsOf h) *ᵥ z.ofLp + (Mvec z h).ofLp := by
  unfold Mvec design armsOf
  rw [Matrix.sum_mulVec]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Matrix.vecMulVec_mulVec, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [inner_vec, dotProduct_comm]
  ext i
  simp [MulOpposite.smul_eq_mul_unop]
  ring

/-- On a history with invertible design matrix, `d′(Ẑ_t − z) = w′ M_t` with `w = C_t d`,
and `‖d‖²_{C_t} = ∑_s (w′U_s)²`. -/
lemma key_identity (z d : LinParamBandits.LowerBound.Vec r) {n : ℕ}
    (h : LinParamBandits.LowerBound.History r n) (hdet : (design (armsOf h)).det ≠ 0) :
    inner ℝ d (Zhat h - z) =
      inner ℝ (WithLp.toLp 2 (Cmat (armsOf h) *ᵥ d.ofLp) : LinParamBandits.LowerBound.Vec r) (Mvec z h) ∧
    quadForm (Cmat (armsOf h)) d =
      ∑ s, inner ℝ (WithLp.toLp 2 (Cmat (armsOf h) *ᵥ d.ofLp) : LinParamBandits.LowerBound.Vec r) (h s).1 ^ 2 := by
  set D := design (armsOf h)
  have hu : IsUnit D.det := isUnit_iff_ne_zero.mpr hdet
  have hCD : Cmat (armsOf h) * D = 1 := Matrix.nonsing_inv_mul D hu
  have hDC : D * Cmat (armsOf h) = 1 := Matrix.mul_nonsing_inv D hu
  have hCT : (Cmat (armsOf h))ᵀ = Cmat (armsOf h) := by
    unfold Cmat; rw [Matrix.transpose_nonsing_inv, design_transpose]
  have hsym : ∀ v : Fin r → ℝ, v ᵥ* Cmat (armsOf h) = Cmat (armsOf h) *ᵥ v := by
    intro v; rw [← Matrix.mulVec_transpose, hCT]
  constructor
  · have hZ : Zhat h - z = WithLp.toLp 2 (Cmat (armsOf h) *ᵥ (Mvec z h).ofLp) := by
      unfold Zhat
      rw [sum_eq z h, Matrix.mulVec_add, Matrix.mulVec_mulVec, hCD, Matrix.one_mulVec]
      ext i
      simp
    rw [hZ, inner_vec, inner_vec]
    simp only [WithLp.ofLp_toLp]
    rw [Matrix.dotProduct_mulVec, hsym]
  · rw [← quadForm_design]
    unfold quadForm
    simp only [WithLp.ofLp_toLp]
    rw [Matrix.mulVec_mulVec, show (design fun s => (h s).1) = D from rfl, hDC, Matrix.one_mulVec,
      dotProduct_comm]

lemma tail_G (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) [IsMarkovKernel ν]
    (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (σ₀ : ℝ)
    (hmgf : ∀ u ∈ 𝒰, ∀ x : ℝ,
      ∫⁻ w, ENNReal.ofReal (Real.exp (x * w)) ∂(ν u) ≤ ENNReal.ofReal (Real.exp (x ^ 2 * σ₀ ^ 2 / 2)))
    (z : LinParamBandits.LowerBound.Vec r) (ψ : Policy r) (hact : ∀ t h, ψ.act t h ∈ 𝒰)
    (w : LinParamBandits.LowerBound.Vec r) (γ a : ℝ) (n : ℕ) :
    histMeasure ν z ψ n {h | a ≤ G σ₀ γ w z h} ≤ ENNReal.ofReal (Real.exp (-a)) := by
  have hF : Measurable (fun h : LinParamBandits.LowerBound.History r n =>
      ENNReal.ofReal (Real.exp (G σ₀ γ w z h))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_G σ₀ γ w z n))
  have h1 := mul_meas_ge_le_lintegral₀ (μ := histMeasure ν z ψ n) hF.aemeasurable (ENNReal.ofReal (Real.exp a))
  have h2 := core_exp 𝒰 ν σ₀ hmgf z ψ hact w γ n
  have hsub : {h : LinParamBandits.LowerBound.History r n | a ≤ G σ₀ γ w z h} ⊆
      {h | ENNReal.ofReal (Real.exp a) ≤ ENNReal.ofReal (Real.exp (G σ₀ γ w z h))} := by
    intro h hh
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hh)
  have h3 : ENNReal.ofReal (Real.exp a) *
      histMeasure ν z ψ n {h | a ≤ G σ₀ γ w z h} ≤ 1 :=
    le_trans (by gcongr) (h1.trans h2)
  rw [Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos a), ENNReal.le_inv_iff_mul_le, mul_comm]
  exact h3

/-- Chernoff bound with finitely many possible (direction, design) pairs. -/
lemma finite_chernoff {𝒰 : Set (LinParamBandits.LowerBound.Vec r)} (h𝒰c : IsCompact 𝒰)
    {ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ} [IsMarkovKernel ν]
    {b : Fin r → LinParamBandits.LowerBound.Vec r} {σ₀ ubar lam0 : ℝ}
    (hA : Assumption1 𝒰 ν b σ₀ ubar lam0) {ψ : Policy r} (hψ : IsUE 𝒰 b σ₀ ubar lam0 ψ)
    (t : ℕ) (ht : r ≤ t) (z : LinParamBandits.LowerBound.Vec r) (ζ : ℝ) (hζ : 0 < ζ)
    (dir : LinParamBandits.LowerBound.History r t → LinParamBandits.LowerBound.Vec r)
    (F : Finset (LinParamBandits.LowerBound.Vec r × Matrix (Fin r) (Fin r) ℝ))
    (hF : ∀ h : LinParamBandits.LowerBound.History r t, (∀ s : Fin t, (h s).1 ∈ admissible 𝒰 b s) →
      (dir h, design (armsOf h)) ∈ F) :
    histMeasure ν z ψ t
        {h | ζ * σ₀ * wnorm (Cmat (armsOf h)) (dir h) < inner ℝ (dir h) (Zhat h - z)} ≤
      F.card * ENNReal.ofReal (Real.exp (-ζ ^ 2 / 2)) := by
  have hσ := hA.σ₀_pos
  -- the test vector and exponent attached to a pair
  let wv : LinParamBandits.LowerBound.Vec r × Matrix (Fin r) (Fin r) ℝ → LinParamBandits.LowerBound.Vec r :=
    fun p => WithLp.toLp 2 (p.2⁻¹ *ᵥ p.1.ofLp)
  let cv : LinParamBandits.LowerBound.Vec r × Matrix (Fin r) (Fin r) ℝ → ℝ :=
    fun p => quadForm p.2⁻¹ p.1
  let γv : LinParamBandits.LowerBound.Vec r × Matrix (Fin r) (Fin r) ℝ → ℝ :=
    fun p => ζ / (σ₀ * Real.sqrt (cv p))
  let T : LinParamBandits.LowerBound.Vec r × Matrix (Fin r) (Fin r) ℝ →
      Set (LinParamBandits.LowerBound.History r t) :=
    fun p => {h | ζ ^ 2 / 2 ≤ G σ₀ (γv p) (wv p) z h}
  calc histMeasure ν z ψ t
        {h | ζ * σ₀ * wnorm (Cmat (armsOf h)) (dir h) < inner ℝ (dir h) (Zhat h - z)}
      ≤ histMeasure ν z ψ t (⋃ p ∈ F, T p) := by
        apply measure_mono_ae
        filter_upwards [ae_good 𝒰 h𝒰c.isClosed.measurableSet b ν z ψ hψ.act_mem hψ.act_init t]
          with h hh
        intro hin
        change ζ * σ₀ * wnorm (Cmat (armsOf h)) (dir h) < inner ℝ (dir h) (Zhat h - z) at hin
        have hpF := hF h hh
        show h ∈ ⋃ p ∈ F, T p
        rw [Set.mem_iUnion₂]
        refine ⟨_, hpF, ?_⟩
        have hpos : ∀ x : LinParamBandits.LowerBound.Vec r, x ≠ 0 →
            0 < ∑ s, inner ℝ x (armsOf h s) ^ 2 := by
          intro x hx
          have := lower_sum hA.b_minEig ht h hh x
          have : 0 < lam0 * ‖x‖ ^ 2 := by
            have := hA.lam0_pos
            have : 0 < ‖x‖ := norm_pos_iff.mpr hx
            positivity
          unfold armsOf; linarith
        obtain ⟨hk1, hk2⟩ := key_identity z (dir h) h (design_det_ne _ hpos)
        set w := (WithLp.toLp 2 (Cmat (armsOf h) *ᵥ (dir h).ofLp) : LinParamBandits.LowerBound.Vec r)
        set c := quadForm (Cmat (armsOf h)) (dir h)
        have hwv : wv (dir h, design (armsOf h)) = w := rfl
        have hcv : cv (dir h, design (armsOf h)) = c := rfl
        show ζ ^ 2 / 2 ≤ G σ₀ (γv (dir h, design (armsOf h))) (wv (dir h, design (armsOf h))) z h
        simp only [γv, hwv, hcv]
        rw [hk1, inner_Mvec] at hin
        unfold wnorm at hin
        have hc0 : 0 ≤ c := by rw [hk2]; positivity
        rcases hc0.lt_or_eq with hcpos | hczero
        · have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hcpos
          unfold G
          rw [← hk2]
          set S := ∑ s, inner ℝ w (h s).1 * ((h s).2 - inner ℝ (h s).1 z)
          have hγ : 0 < ζ / (σ₀ * Real.sqrt c) := by positivity
          have h1 : ζ / (σ₀ * Real.sqrt c) * (ζ * σ₀ * Real.sqrt c) ≤ ζ / (σ₀ * Real.sqrt c) * S :=
            mul_le_mul_of_nonneg_left hin.le hγ.le
          have h2 : ζ / (σ₀ * Real.sqrt c) * (ζ * σ₀ * Real.sqrt c) = ζ ^ 2 := by
            field_simp
          have h3 : (ζ / (σ₀ * Real.sqrt c)) ^ 2 * σ₀ ^ 2 * c / 2 = ζ ^ 2 / 2 := by
            rw [div_pow, mul_pow, Real.sq_sqrt hc0]
            field_simp
          linarith
        · exfalso
          have hall : ∀ s ∈ Finset.univ, inner ℝ w (h s).1 ^ 2 = 0 := by
            have h0 : ∑ s, inner ℝ w (h s).1 ^ 2 = 0 := by rw [← hk2]; exact hczero.symm
            exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp h0
          have hS : ∑ s, inner ℝ w (h s).1 * ((h s).2 - inner ℝ (h s).1 z) = 0 := by
            refine Finset.sum_eq_zero fun s hs => ?_
            have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (hall s hs)
            rw [this, zero_mul]
          have hq0 : quadForm (Cmat (armsOf h)) (dir h) = 0 := hczero.symm
          rw [hS] at hin
          rw [hq0, Real.sqrt_zero, mul_zero] at hin
          exact lt_irrefl _ hin
    _ ≤ ∑ p ∈ F, histMeasure ν z ψ t (T p) := measure_biUnion_finset_le F T
    _ ≤ ∑ _p ∈ F, ENNReal.ofReal (Real.exp (-ζ ^ 2 / 2)) := by
        refine Finset.sum_le_sum fun p _ => ?_
        have := tail_G ν 𝒰 σ₀ hA.mgf_le z ψ hψ.act_mem (wv p) (γv p) (ζ ^ 2 / 2) t
        rw [show -(ζ ^ 2 / 2) = -ζ ^ 2 / 2 by ring] at this
        exact this
    _ = F.card * ENNReal.ofReal (Real.exp (-ζ ^ 2 / 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- The design matrix determined by a vector of pull counts. -/
noncomputable def Dn (S : Finset (LinParamBandits.LowerBound.Vec r)) {t : ℕ} (n : S → Fin (t + 1)) :
    Matrix (Fin r) (Fin r) ℝ :=
  ∑ u : S, (((n u : ℕ) : ℝ)) • vecMulVec (u : LinParamBandits.LowerBound.Vec r).ofLp
    (u : LinParamBandits.LowerBound.Vec r).ofLp

/-- The finite set of possible (direction, design) pairs. -/
noncomputable def pairs (S : Finset (LinParamBandits.LowerBound.Vec r)) (t : ℕ)
    (f : LinParamBandits.LowerBound.Vec r → LinParamBandits.LowerBound.Vec r) :
    Finset (LinParamBandits.LowerBound.Vec r × Matrix (Fin r) (Fin r) ℝ) :=
  (Finset.univ : Finset (S × (S → Fin (t + 1)))).image (fun p => (f p.1, Dn S p.2))

lemma card_pairs_le (S : Finset (LinParamBandits.LowerBound.Vec r)) (t : ℕ)
    (f : LinParamBandits.LowerBound.Vec r → LinParamBandits.LowerBound.Vec r) :
    (pairs S t f).card ≤ S.card * (t + 1) ^ S.card := by
  unfold pairs
  refine Finset.card_image_le.trans ?_
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fun]

lemma design_eq_Dn (S : Finset (LinParamBandits.LowerBound.Vec r)) {t : ℕ}
    (h : LinParamBandits.LowerBound.History r t) (hS : ∀ s, (h s).1 ∈ S) :
    ∃ n : S → Fin (t + 1), design (armsOf h) = Dn S n := by
  refine ⟨fun u => ⟨(Finset.univ.filter (fun s : Fin t => (h s).1 = u)).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩, ?_⟩
  unfold design Dn armsOf
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := S) (g := fun s => (h s).1)
    (fun s _ => hS s)]
  rw [← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_congr rfl (fun s hs => by
    rw [(Finset.mem_filter.mp hs).2])]
  rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]

lemma nat_bound (k t : ℕ) (ht : 2 ≤ t) : k * (t + 1) ^ k ≤ t ^ (5 * k) := by
  have h1 : k ≤ t ^ k := (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left ht k)
  have h2 : (t + 1) ^ k ≤ t ^ (2 * k) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by nlinarith) k
  calc k * (t + 1) ^ k ≤ t ^ k * t ^ (2 * k) := Nat.mul_le_mul h1 h2
    _ = t ^ (3 * k) := by rw [← pow_add]; ring_nf
    _ ≤ t ^ (5 * k) := Nat.pow_le_pow_right (by omega) (by omega)

lemma final_bound (c t k : ℕ) (ht : 2 ≤ t) (hc : c ≤ k * (t + 1) ^ k) (e : ℝ) (he : 0 ≤ e) :
    (c : ENNReal) * ENNReal.ofReal e ≤ ENNReal.ofReal ((t : ℝ) ^ (5 * k) * e) := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ he
  have := hc.trans (nat_bound k t ht)
  exact_mod_cast this

end UE3Core

open UE3Core LinParamBandits.UEGeneral in
theorem solution {r : ℕ} (hr : 2 ≤ r) {𝒰 : Set (LinParamBandits.LowerBound.Vec r)} (h𝒰c : IsCompact 𝒰) (h𝒰n : 𝒰.Nonempty)
    {ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ} [IsMarkovKernel ν] {b : Fin r → LinParamBandits.LowerBound.Vec r} {σ₀ ubar lam0 : ℝ}
    (hA : Assumption1 𝒰 ν b σ₀ ubar lam0) {ψ : Policy r} (hψ : IsUE 𝒰 b σ₀ ubar lam0 ψ)
    (hfin : 𝒰.Finite) (t : ℕ) (ht : r ≤ t) (x z : LinParamBandits.LowerBound.Vec r) (ζ : ℝ) (hζ : 0 < ζ) :
    histMeasure ν z ψ t
        {h | ζ * σ₀ * wnorm (Cmat (armsOf h)) x < inner ℝ x (Zhat h - z)} ≤
      ENNReal.ofReal ((t : ℝ) ^ (5 * 𝒰.ncard) * Real.exp (-ζ ^ 2 / 2)) ∧
    histMeasure ν z ψ t
        {h | ζ * σ₀ * wnorm (Cmat (armsOf h)) (ψ.act t h - x) <
          inner ℝ (ψ.act t h - x) (Zhat h - z)} ≤
      ENNReal.ofReal ((t : ℝ) ^ (5 * 𝒰.ncard) * Real.exp (-ζ ^ 2 / 2)) := by
  set S := hfin.toFinset with hSdef
  have hncard : 𝒰.ncard = S.card := Set.ncard_eq_toFinset_card 𝒰 hfin
  have ht2 : 2 ≤ t := hr.trans ht
  have hmem : ∀ f : LinParamBandits.LowerBound.Vec r → LinParamBandits.LowerBound.Vec r,
      ∀ h : LinParamBandits.LowerBound.History r t, (∀ s : Fin t, (h s).1 ∈ admissible 𝒰 b s) →
      (f (ψ.act t h), design (armsOf h)) ∈ pairs S t f := by
    intro f h hh
    obtain ⟨n, hn⟩ := design_eq_Dn S h (fun s => by
      rw [hSdef, Set.Finite.mem_toFinset]; exact (hh s).1)
    unfold pairs
    rw [Finset.mem_image]
    refine ⟨(⟨ψ.act t h, by rw [hSdef, Set.Finite.mem_toFinset]; exact hψ.act_mem t h⟩, n),
      Finset.mem_univ _, ?_⟩
    simp [hn]
  rw [hncard]
  constructor
  · have h1 := finite_chernoff h𝒰c hA hψ t ht z ζ hζ (fun _ => x) (pairs S t (fun _ => x))
      (fun h hh => hmem (fun _ => x) h hh)
    exact h1.trans (final_bound _ t S.card ht2 (card_pairs_le S t _) _ (Real.exp_pos _).le)
  · have h1 := finite_chernoff h𝒰c hA hψ t ht z ζ hζ (fun h => ψ.act t h - x)
      (pairs S t (fun u => u - x)) (fun h hh => hmem (fun u => u - x) h hh)
    exact h1.trans (final_bound _ t S.card ht2 (card_pairs_le S t _) _ (Real.exp_pos _).le)
