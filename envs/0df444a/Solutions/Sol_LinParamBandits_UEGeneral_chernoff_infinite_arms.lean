-- Prove2me | solution 1 for LinParamBandits.UEGeneral.chernoff_infinite_arms
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T21:28:15.613202+00:00
-- url     : https://prove2.me/submissions/52979731-8144-4558-94c7-f0dd551db154

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy
import Theorems.Thm_LinParamBandits_UEGeneral_martingale_loewner

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


lemma isClosed_psd : IsClosed {A : Matrix (Fin r) (Fin r) ℝ | A.PosSemidef} := by
  have : {A : Matrix (Fin r) (Fin r) ℝ | A.PosSemidef} =
      {A | Aᴴ = A} ∩ ⋂ v : Fin r → ℝ, {A | 0 ≤ star v ⬝ᵥ (A *ᵥ v)} := by
    ext A; simp [posSemidef_iff_dotProduct_mulVec, IsHermitian]
  rw [this]
  exact (isClosed_eq (by fun_prop) continuous_id).inter
    (isClosed_iInter fun v => isClosed_le continuous_const (by fun_prop))

lemma measurableSet_psd (β : ℝ) (z : LinParamBandits.LowerBound.Vec r) (t : ℕ) :
    MeasurableSet {h : LinParamBandits.LowerBound.History r t |
      (β • design (armsOf h) - vecMulVec (Mvec z h).ofLp (Mvec z h).ofLp).PosSemidef} := by
  let Φ : LinParamBandits.LowerBound.History r t → (Fin r → Fin r → ℝ) := fun h i j =>
    β * (∑ s, (h s).1.ofLp i * (h s).1.ofLp j) -
      (∑ s, ((h s).2 - inner ℝ (h s).1 z) * (h s).1.ofLp i) *
      (∑ s, ((h s).2 - inner ℝ (h s).1 z) * (h s).1.ofLp j)
  have hΦ : Measurable Φ := by
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
    simp only [Φ]
    fun_prop
  have hKc : IsClosed {A : Fin r → Fin r → ℝ | Matrix.PosSemidef (Matrix.of A)} := isClosed_psd
  have hK : MeasurableSet {A : Fin r → Fin r → ℝ | Matrix.PosSemidef (Matrix.of A)} :=
    hKc.measurableSet
  have heq : {h : LinParamBandits.LowerBound.History r t |
      (β • design (armsOf h) - vecMulVec (Mvec z h).ofLp (Mvec z h).ofLp).PosSemidef} =
      Φ ⁻¹' {A : Fin r → Fin r → ℝ | Matrix.PosSemidef (Matrix.of A)} := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    congr! 1
    ext i j
    simp only [Φ, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.vecMulVec_apply, design, armsOf, Matrix.sum_apply, Mvec, WithLp.ofLp_sum,
      WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply]
  rw [heq]
  exact hΦ hK

lemma chernoff_dir {𝒰 : Set (LinParamBandits.LowerBound.Vec r)} (h𝒰c : IsCompact 𝒰)
    {ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ} [IsMarkovKernel ν]
    {b : Fin r → LinParamBandits.LowerBound.Vec r} {σ₀ ubar lam0 : ℝ}
    (hA : Assumption1 𝒰 ν b σ₀ ubar lam0) {ψ : Policy r} (hψ : IsUE 𝒰 b σ₀ ubar lam0 ψ)
    (hr : 2 ≤ r) (t : ℕ) (ht : r ≤ t) (z : LinParamBandits.LowerBound.Vec r) (ζ : ℝ) (hζ : 2 ≤ ζ)
    (dir : LinParamBandits.LowerBound.History r t → LinParamBandits.LowerBound.Vec r)
    (p : ℝ) (hp : 0 ≤ p)
    (hloew : ENNReal.ofReal (1 - p) ≤ histMeasure ν z ψ t
      {h | ((ζ ^ 2 * kappa0 ubar lam0 ^ 2 * σ₀ ^ 2 * Real.log t) • design (armsOf h) -
            Matrix.vecMulVec (Mvec z h).ofLp (Mvec z h).ofLp).PosSemidef}) :
    histMeasure ν z ψ t
        {h | ζ * kappa0 ubar lam0 * σ₀ * Real.sqrt (Real.log t) * wnorm (Cmat (armsOf h)) (dir h) <
          inner ℝ (dir h) (Zhat h - z)} ≤ ENNReal.ofReal p := by
  have hσ := hA.σ₀_pos
  have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast (le_trans hr ht)
  have hL0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hκ0 : 0 ≤ kappa0 ubar lam0 := by unfold kappa0; positivity
  have hζ0 : 0 ≤ ζ := by linarith
  set β := ζ ^ 2 * kappa0 ubar lam0 ^ 2 * σ₀ ^ 2 * Real.log t with hβ
  set Aset := {h : LinParamBandits.LowerBound.History r t |
      (β • design (armsOf h) - Matrix.vecMulVec (Mvec z h).ofLp (Mvec z h).ofLp).PosSemidef}
  haveI := isProb_histMeasure ν z ψ t
  have hAm : MeasurableSet Aset := measurableSet_psd β z t
  calc _ ≤ histMeasure ν z ψ t Asetᶜ := by
        apply measure_mono_ae
        filter_upwards [ae_good 𝒰 h𝒰c.isClosed.measurableSet b ν z ψ hψ.act_mem hψ.act_init t]
          with h hh
        intro hin hpsd
        change ζ * kappa0 ubar lam0 * σ₀ * Real.sqrt (Real.log t) *
          wnorm (Cmat (armsOf h)) (dir h) < inner ℝ (dir h) (Zhat h - z) at hin
        change (β • design (armsOf h) -
          Matrix.vecMulVec (Mvec z h).ofLp (Mvec z h).ofLp).PosSemidef at hpsd
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
        have hq := hpsd.dotProduct_mulVec_nonneg w.ofLp
        simp only [star_trivial] at hq
        have hq' : 0 ≤ β * (w.ofLp ⬝ᵥ (design (armsOf h) *ᵥ w.ofLp)) -
            ((Mvec z h).ofLp ⬝ᵥ w.ofLp) * (w.ofLp ⬝ᵥ (Mvec z h).ofLp) := by
          have e : w.ofLp ⬝ᵥ ((β • design (armsOf h) -
              Matrix.vecMulVec (Mvec z h).ofLp (Mvec z h).ofLp) *ᵥ w.ofLp) =
              β * (w.ofLp ⬝ᵥ (design (armsOf h) *ᵥ w.ofLp)) -
              ((Mvec z h).ofLp ⬝ᵥ w.ofLp) * (w.ofLp ⬝ᵥ (Mvec z h).ofLp) := by
            rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, dotProduct_sub,
              dotProduct_smul, dotProduct_smul, smul_eq_mul]
            simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
            ring
          rw [e] at hq
          exact hq
        clear hq
        have hq := hq'
        have hD : w.ofLp ⬝ᵥ (design (armsOf h) *ᵥ w.ofLp) = ∑ s, inner ℝ w (h s).1 ^ 2 := by
          have := quadForm_design (armsOf h) w
          unfold quadForm at this
          exact this
        have hM : (Mvec z h).ofLp ⬝ᵥ w.ofLp = inner ℝ w (Mvec z h) := by
          rw [inner_vec, dotProduct_comm]
        rw [hD, hM, dotProduct_comm w.ofLp, hM] at hq
        rw [hk1] at hin
        unfold wnorm at hin
        rw [hk2] at hin
        set c := ∑ s, inner ℝ w (h s).1 ^ 2
        have hc0 : 0 ≤ c := by positivity
        have hsq : inner ℝ w (Mvec z h) ^ 2 ≤ β * c := by nlinarith
        have hroot : ζ * kappa0 ubar lam0 * σ₀ * Real.sqrt (Real.log t) * Real.sqrt c =
            Real.sqrt (β * c) := by
          rw [hβ, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
            Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hζ0,
            Real.sqrt_sq hκ0, Real.sqrt_sq hσ.le]
        rw [hroot] at hin
        have : inner ℝ w (Mvec z h) ≤ Real.sqrt (β * c) :=
          (le_abs_self _).trans (Real.abs_le_sqrt hsq)
        linarith
    _ = 1 - histMeasure ν z ψ t Aset := prob_compl_eq_one_sub hAm
    _ ≤ 1 - ENNReal.ofReal (1 - p) := tsub_le_tsub_left hloew _
    _ ≤ ENNReal.ofReal p := by
        rw [tsub_le_iff_right]
        calc (1 : ENNReal) = ENNReal.ofReal (p + (1 - p)) := by norm_num
          _ ≤ _ := ENNReal.ofReal_add_le

end UE3Core

open UE3Core LinParamBandits.UEGeneral in
theorem solution {r : ℕ} (hr : 2 ≤ r) {𝒰 : Set (LinParamBandits.LowerBound.Vec r)} (h𝒰c : IsCompact 𝒰) (h𝒰n : 𝒰.Nonempty)
    {ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ} [IsMarkovKernel ν] {b : Fin r → LinParamBandits.LowerBound.Vec r} {σ₀ ubar lam0 : ℝ}
    (hA : Assumption1 𝒰 ν b σ₀ ubar lam0) {ψ : Policy r} (hψ : IsUE 𝒰 b σ₀ ubar lam0 ψ)
    (t : ℕ) (ht : r ≤ t) (x z : LinParamBandits.LowerBound.Vec r) (ζ : ℝ) (hζ : 2 ≤ ζ) :
    histMeasure ν z ψ t
        {h | ζ * kappa0 ubar lam0 * σ₀ * Real.sqrt (Real.log t) * wnorm (Cmat (armsOf h)) x <
          inner ℝ x (Zhat h - z)} ≤
      ENNReal.ofReal ((t : ℝ) ^ ((r : ℝ) * kappa0 ubar lam0 ^ 2) * Real.exp (-ζ ^ 2 / 4)) ∧
    histMeasure ν z ψ t
        {h | ζ * kappa0 ubar lam0 * σ₀ * Real.sqrt (Real.log t) *
            wnorm (Cmat (armsOf h)) (ψ.act t h - x) < inner ℝ (ψ.act t h - x) (Zhat h - z)} ≤
      ENNReal.ofReal ((t : ℝ) ^ ((r : ℝ) * kappa0 ubar lam0 ^ 2) * Real.exp (-ζ ^ 2 / 4)) := by
  have hloew := martingale_loewner hr h𝒰c h𝒰n hA hψ z t ht ζ hζ
  have hp : 0 ≤ (t : ℝ) ^ ((r : ℝ) * kappa0 ubar lam0 ^ 2) * Real.exp (-ζ ^ 2 / 4) := by positivity
  exact ⟨chernoff_dir h𝒰c hA hψ hr t ht z ζ hζ (fun _ => x) _ hp hloew,
    chernoff_dir h𝒰c hA hψ hr t ht z ζ hζ (fun h => ψ.act t h - x) _ hp hloew⟩
