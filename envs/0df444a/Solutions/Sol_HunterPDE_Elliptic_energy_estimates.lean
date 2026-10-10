-- Prove2me | solution 1 for HunterPDE.Elliptic.energy_estimates
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T04:22:25.421991+00:00
-- url     : https://prove2.me/submissions/13bd8d55-8aa2-4fdd-98bb-54301a4e5f75

import Mathlib
import Definitions.Def_HunterPDE_Elliptic_EllipticOperator

set_option autoImplicit false

open MeasureTheory

namespace HunterPDE.Elliptic.EE96

open HunterPDE.Elliptic

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

/-- Pointwise integrand of `form`. -/
noncomputable def Gf (P : Coeffs n) (x : EuclideanSpace ℝ (Fin n)) (p q : Jet n) : ℝ :=
  ((∑ i, ∑ j, P.a i j x * (WithLp.ofLp p).2 i * (WithLp.ofLp q).2 j)
    - (∑ i, P.b i x * (WithLp.ofLp p).1 * (WithLp.ofLp q).2 i))
    + P.c x * (WithLp.ofLp p).1 * (WithLp.ofLp q).1

lemma form_eq (P : Coeffs n) (u v : H10 n Ω) :
    form P u v = ∫ x in Ω, Gf P x ((u : JetL2 n Ω) x) ((v : JetL2 n Ω) x) := rfl

lemma memLp_fst (U : JetL2 n Ω) :
    MemLp (fun x => (WithLp.ofLp (U x)).1) 2 (volume.restrict Ω) :=
  ContinuousLinearMap.comp_memLp (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))) U

lemma memLp_snd (U : JetL2 n Ω) (i : Fin n) :
    MemLp (fun x => (WithLp.ofLp (U x)).2 i) 2 (volume.restrict Ω) :=
  ContinuousLinearMap.comp_memLp
    ((EuclideanSpace.proj i).comp (WithLp.sndL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n)))) U

lemma int3 {f g h : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f ⊤ (volume.restrict Ω))
    (hg : MemLp g 2 (volume.restrict Ω)) (hh : MemLp h 2 (volume.restrict Ω)) :
    Integrable (fun x => f x * g x * h x) (volume.restrict Ω) := by
  have h1 : Integrable (g * h) (volume.restrict Ω) := hg.integrable_mul hh
  have h2 := h1.mul_of_top_right hf
  refine h2.congr (ae_of_all _ fun x => ?_)
  simp [mul_assoc]

lemma Gf_integrable (P : Coeffs n) (hP : P.Admissible Ω) (U V : JetL2 n Ω) :
    Integrable (fun x => Gf P x (U x) (V x)) (volume.restrict Ω) := by
  unfold Gf
  refine Integrable.add (Integrable.sub ?_ ?_) ?_
  · refine integrable_finsetSum _ fun i _ => ?_
    refine integrable_finsetSum _ fun j _ => ?_
    exact int3 (hP.1 i j) (memLp_snd U i) (memLp_snd V j)
  · refine integrable_finsetSum _ fun i _ => ?_
    exact int3 (hP.2.1 i) (memLp_fst U) (memLp_snd V i)
  · exact int3 hP.2.2.1 (memLp_fst U) (memLp_fst V)

/-- Squared norm of a jet. -/
lemma jet_norm_sq (p : Jet n) :
    ‖p‖ ^ 2 = (WithLp.ofLp p).1 ^ 2 + ∑ i, (WithLp.ofLp p).2 i ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  rfl

lemma abs_fst_le (p : Jet n) : |(WithLp.ofLp p).1| ≤ ‖p‖ := by
  have h := jet_norm_sq p
  have h0 : 0 ≤ ∑ i, (WithLp.ofLp p).2 i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have : (WithLp.ofLp p).1 ^ 2 ≤ ‖p‖ ^ 2 := by linarith
  have := sq_le_sq.mp this
  rwa [abs_norm] at this

lemma abs_snd_le (p : Jet n) (i : Fin n) : |(WithLp.ofLp p).2 i| ≤ ‖p‖ := by
  have h := jet_norm_sq p
  have h1 : (WithLp.ofLp p).2 i ^ 2 ≤ ∑ j, (WithLp.ofLp p).2 j ^ 2 :=
    Finset.single_le_sum (f := fun j => (WithLp.ofLp p).2 j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have : (WithLp.ofLp p).2 i ^ 2 ≤ ‖p‖ ^ 2 := by nlinarith [sq_nonneg (WithLp.ofLp p).1]
  have := sq_le_sq.mp this
  rwa [abs_norm] at this

/-- `‖u‖² = ∫_Ω |U x|²`. -/
lemma normsq (u : H10 n Ω) : ‖u‖ ^ 2 = ∫ x in Ω, ‖(u : JetL2 n Ω) x‖ ^ 2 := by
  have h : ‖u‖ = ‖(u : JetL2 n Ω)‖ := rfl
  rw [h, ← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma int_normsq (U : JetL2 n Ω) :
    Integrable (fun x => ‖U x‖ ^ 2) (volume.restrict Ω) := by
  have := L2.integrable_inner (𝕜 := ℝ) U U
  simpa only [real_inner_self_eq_norm_sq] using this

lemma ae_abs_le {μ : Measure (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : MemLp f ⊤ μ) : ∀ᵐ x ∂μ, |f x| ≤ (eLpNorm f ⊤ μ).toReal := by
  have hlt : eLpNorm f ⊤ μ ≠ ⊤ := hf.2.ne
  rw [eLpNorm_exponent_top] at hlt ⊢
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
  have h1 : ‖f x‖ ≤ (eLpNormEssSup f μ).toReal := by
    rw [← toReal_enorm]
    exact ENNReal.toReal_mono hlt hx
  rwa [Real.norm_eq_abs] at h1

/-- Pointwise boundedness of the integrand. -/
lemma Gf_bound (P : Coeffs n) (x : EuclideanSpace ℝ (Fin n)) (A : Fin n → Fin n → ℝ)
    (B : Fin n → ℝ) (Cc : ℝ) (hA : ∀ i j, |P.a i j x| ≤ A i j) (hB : ∀ i, |P.b i x| ≤ B i)
    (hC : |P.c x| ≤ Cc) (p q : Jet n) :
    |Gf P x p q| ≤ (∑ i, ∑ j, A i j + ∑ i, B i + Cc) * (‖p‖ * ‖q‖) := by
  have hA0 : ∀ i j, 0 ≤ A i j := fun i j => (abs_nonneg _).trans (hA i j)
  have hB0 : ∀ i, 0 ≤ B i := fun i => (abs_nonneg _).trans (hB i)
  have h1 : |∑ i, ∑ j, P.a i j x * (WithLp.ofLp p).2 i * (WithLp.ofLp q).2 j| ≤
      (∑ i, ∑ j, A i j) * (‖p‖ * ‖q‖) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, abs_mul, ← mul_assoc]
    exact mul_le_mul (mul_le_mul (hA i j) (abs_snd_le p i) (abs_nonneg _) (hA0 i j))
      (abs_snd_le q j) (abs_nonneg _) (mul_nonneg (hA0 i j) (norm_nonneg _))
  have h2 : |∑ i, P.b i x * (WithLp.ofLp p).1 * (WithLp.ofLp q).2 i| ≤
      (∑ i, B i) * (‖p‖ * ‖q‖) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul, abs_mul, ← mul_assoc]
    exact mul_le_mul (mul_le_mul (hB i) (abs_fst_le p) (abs_nonneg _) (hB0 i))
      (abs_snd_le q i) (abs_nonneg _) (mul_nonneg (hB0 i) (norm_nonneg _))
  have h3 : |P.c x * (WithLp.ofLp p).1 * (WithLp.ofLp q).1| ≤ Cc * (‖p‖ * ‖q‖) := by
    rw [abs_mul, abs_mul, ← mul_assoc]
    exact mul_le_mul (mul_le_mul hC (abs_fst_le p) (abs_nonneg _) ((abs_nonneg _).trans hC))
      (abs_fst_le q) (abs_nonneg _) (mul_nonneg ((abs_nonneg _).trans hC) (norm_nonneg _))
  unfold Gf
  calc _ ≤ |(∑ i, ∑ j, P.a i j x * (WithLp.ofLp p).2 i * (WithLp.ofLp q).2 j)
          - (∑ i, P.b i x * (WithLp.ofLp p).1 * (WithLp.ofLp q).2 i)|
          + |P.c x * (WithLp.ofLp p).1 * (WithLp.ofLp q).1| := abs_add_le _ _
    _ ≤ (|∑ i, ∑ j, P.a i j x * (WithLp.ofLp p).2 i * (WithLp.ofLp q).2 j|
          + |∑ i, P.b i x * (WithLp.ofLp p).1 * (WithLp.ofLp q).2 i|)
          + |P.c x * (WithLp.ofLp p).1 * (WithLp.ofLp q).1| := by
        gcongr; exact abs_sub _ _
    _ ≤ _ := by nlinarith [h1, h2, h3]

/-- Hölder: `∫ |U||V| ≤ ‖u‖ ‖v‖`. -/
lemma int_norm_mul_le (u v : H10 n Ω) :
    ∫ x in Ω, ‖(u : JetL2 n Ω) x‖ * ‖(v : JetL2 n Ω) x‖ ≤ ‖u‖ * ‖v‖ := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hU : MemLp (fun x => ‖(u : JetL2 n Ω) x‖) (ENNReal.ofReal 2) (volume.restrict Ω) := by
    rw [ENNReal.ofReal_ofNat]; exact (Lp.memLp _).norm
  have hV : MemLp (fun x => ‖(v : JetL2 n Ω) x‖) (ENNReal.ofReal 2) (volume.restrict Ω) := by
    rw [ENNReal.ofReal_ofNat]; exact (Lp.memLp _).norm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (ae_of_all _ fun x => norm_nonneg _)
    (ae_of_all _ fun x => norm_nonneg _) hU hV
  simp only [Real.rpow_two] at h
  rw [← normsq, ← normsq] at h
  have e : ∀ t : ℝ, 0 ≤ t → (t ^ 2) ^ (1 / (2 : ℝ)) = t := fun t ht => by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq ht]
  rwa [e _ (norm_nonneg _), e _ (norm_nonneg _)] at h

/-- Boundedness of the form. -/
lemma form_bound (P : Coeffs n) (hP : P.Admissible Ω) (A : Fin n → Fin n → ℝ)
    (B : Fin n → ℝ) (Cc : ℝ)
    (hA : ∀ᵐ x ∂(volume.restrict Ω), ∀ i j, |P.a i j x| ≤ A i j)
    (hB : ∀ᵐ x ∂(volume.restrict Ω), ∀ i, |P.b i x| ≤ B i)
    (hC : ∀ᵐ x ∂(volume.restrict Ω), |P.c x| ≤ Cc) (hK : 0 ≤ ∑ i, ∑ j, A i j + ∑ i, B i + Cc)
    (u v : H10 n Ω) :
    |form P u v| ≤ (∑ i, ∑ j, A i j + ∑ i, B i + Cc) * ‖u‖ * ‖v‖ := by
  set K := ∑ i, ∑ j, A i j + ∑ i, B i + Cc
  rw [form_eq]
  refine (abs_integral_le_integral_abs).trans ?_
  have hi : Integrable (fun x => K * (‖(u : JetL2 n Ω) x‖ * ‖(v : JetL2 n Ω) x‖))
      (volume.restrict Ω) := by
    refine Integrable.const_mul ?_ K
    exact (Lp.memLp (u : JetL2 n Ω)).norm.integrable_mul (Lp.memLp (v : JetL2 n Ω)).norm
  calc _ ≤ ∫ x in Ω, K * (‖(u : JetL2 n Ω) x‖ * ‖(v : JetL2 n Ω) x‖) := by
        refine integral_mono_ae (Gf_integrable P hP _ _).abs hi ?_
        filter_upwards [hA, hB, hC] with x h1 h2 h3
        exact Gf_bound P x A B Cc h1 h2 h3 _ _
    _ = K * ∫ x in Ω, ‖(u : JetL2 n Ω) x‖ * ‖(v : JetL2 n Ω) x‖ := integral_const_mul _ _
    _ ≤ K * (‖u‖ * ‖v‖) := mul_le_mul_of_nonneg_left (int_norm_mul_le u v) hK
    _ = K * ‖u‖ * ‖v‖ := by ring

/-- Pointwise Gårding inequality. -/
lemma garding_pt (P : Coeffs n) (x : EuclideanSpace ℝ (Fin n)) (θ c₀ : ℝ) (B : Fin n → ℝ)
    (hθ0 : 0 < θ)
    (hell : ∀ ξ : Fin n → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, P.a i j x * ξ i * ξ j)
    (hc : c₀ ≤ P.c x) (hB : ∀ i, |P.b i x| ≤ B i) (p : Jet n) :
    θ / 2 * ‖p‖ ^ 2 ≤ Gf P x p p +
      (1 / (2 * θ) * ∑ i, B i ^ 2 + θ / 2 - c₀) * ((WithLp.ofLp p).1 * (WithLp.ofLp p).1) := by
  set s := (WithLp.ofLp p).1 with hs
  set ξ := (WithLp.ofLp p).2 with hξ
  have h1 := hell (fun i => ξ i)
  have hterm : ∀ i, P.b i x * s * ξ i ≤ 1 / (2 * θ) * (B i ^ 2 * s ^ 2) + θ / 2 * ξ i ^ 2 := by
    intro i
    have hb : P.b i x * s * ξ i ≤ B i * (|s| * |ξ i|) := by
      calc P.b i x * s * ξ i ≤ |P.b i x * s * ξ i| := le_abs_self _
        _ = |P.b i x| * (|s| * |ξ i|) := by rw [abs_mul, abs_mul, mul_assoc]
        _ ≤ B i * (|s| * |ξ i|) :=
            mul_le_mul_of_nonneg_right (hB i) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have key : 2 * θ * (B i * (|s| * |ξ i|)) ≤ B i ^ 2 * s ^ 2 + θ ^ 2 * ξ i ^ 2 := by
      nlinarith [sq_nonneg (B i * |s| - θ * |ξ i|), sq_abs s, sq_abs (ξ i)]
    have e : 1 / (2 * θ) * (B i ^ 2 * s ^ 2) + θ / 2 * ξ i ^ 2 =
        (B i ^ 2 * s ^ 2 + θ ^ 2 * ξ i ^ 2) / (2 * θ) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith [hb, key]
  have h2 : ∑ i, P.b i x * s * ξ i ≤
      1 / (2 * θ) * (∑ i, B i ^ 2) * s ^ 2 + θ / 2 * ∑ i, ξ i ^ 2 := by
    refine (Finset.sum_le_sum fun i _ => hterm i).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.sum_mul]
    refine congrArg₂ _ (Finset.sum_congr rfl fun i _ => by ring) rfl
  have h3 : c₀ * (s * s) ≤ P.c x * (s * s) := mul_le_mul_of_nonneg_right hc (mul_self_nonneg s)
  have hn := jet_norm_sq p
  rw [← hs, ← hξ] at hn
  have hG : Gf P x p p = (∑ i, ∑ j, P.a i j x * ξ i * ξ j) - (∑ i, P.b i x * s * ξ i)
      + P.c x * s * s := rfl
  rw [hG, hn]
  nlinarith [h1, h2, h3]

/-- Integrated Gårding inequality. -/
lemma garding_int (P : Coeffs n) (hP : P.Admissible Ω) (θ c₀ : ℝ) (B : Fin n → ℝ)
    (hθ0 : 0 < θ)
    (hell : ∀ᵐ x ∂(volume.restrict Ω), ∀ ξ : Fin n → ℝ,
      θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, P.a i j x * ξ i * ξ j)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), c₀ ≤ P.c x)
    (hB : ∀ᵐ x ∂(volume.restrict Ω), ∀ i, |P.b i x| ≤ B i) (u : H10 n Ω) :
    θ / 2 * ‖u‖ ^ 2 ≤ form P u u + (1 / (2 * θ) * ∑ i, B i ^ 2 + θ / 2 - c₀) * l2inner u u := by
  set γ := 1 / (2 * θ) * ∑ i, B i ^ 2 + θ / 2 - c₀
  set U := (u : JetL2 n Ω)
  have hl : l2inner u u = ∫ x in Ω, (WithLp.ofLp (U x)).1 * (WithLp.ofLp (U x)).1 := rfl
  have hi2 : Integrable (fun x => γ * ((WithLp.ofLp (U x)).1 * (WithLp.ofLp (U x)).1))
      (volume.restrict Ω) :=
    ((memLp_fst U).integrable_mul (memLp_fst U)).const_mul γ
  rw [form_eq, hl, ← integral_const_mul, ← integral_add (Gf_integrable P hP _ _) hi2,
    normsq, ← integral_const_mul]
  refine integral_mono_ae ((int_normsq U).const_mul _) ((Gf_integrable P hP _ _).add hi2) ?_
  filter_upwards [hell, hc, hB] with x h1 h2 h3
  exact garding_pt P x θ c₀ B hθ0 h1 h2 h3 (U x)

end HunterPDE.Elliptic.EE96

open HunterPDE.Elliptic MeasureTheory in
theorem solution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (P : Coeffs n) (hP : P.Admissible Ω) (θ : ℝ) (hθ : P.UniformlyEllipticWith Ω θ) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
      (∀ u v : H10 n Ω, |form P u v| ≤ C₂ * ‖u‖ * ‖v‖) ∧
      ∀ c₀ : ℝ, (∀ᵐ x ∂(volume.restrict Ω), c₀ ≤ P.c x) →
        ((∀ i, P.b i =ᵐ[volume.restrict Ω] 0) →
          ∀ u : H10 n Ω, C₁ * ‖u‖ ^ 2 ≤ form P u u + (θ - c₀) * l2inner u u) ∧
        (¬ (∀ i, P.b i =ᵐ[volume.restrict Ω] 0) →
          ∀ u : H10 n Ω, C₁ * ‖u‖ ^ 2 ≤ form P u u +
            (1 / (2 * θ) * ∑ i, (eLpNorm (P.b i) ⊤ (volume.restrict Ω)).toReal ^ 2
              + θ / 2 - c₀) * l2inner u u) := by
  obtain ⟨hθ0, hell⟩ := hθ
  set A : Fin n → Fin n → ℝ := fun i j => (eLpNorm (P.a i j) ⊤ (volume.restrict Ω)).toReal
  set B : Fin n → ℝ := fun i => (eLpNorm (P.b i) ⊤ (volume.restrict Ω)).toReal
  set Cc : ℝ := (eLpNorm P.c ⊤ (volume.restrict Ω)).toReal
  have hA : ∀ᵐ x ∂(volume.restrict Ω), ∀ i j, |P.a i j x| ≤ A i j := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
    exact EE96.ae_abs_le (hP.1 i j)
  have hB : ∀ᵐ x ∂(volume.restrict Ω), ∀ i, |P.b i x| ≤ B i := by
    rw [ae_all_iff]; intro i
    exact EE96.ae_abs_le (hP.2.1 i)
  have hC : ∀ᵐ x ∂(volume.restrict Ω), |P.c x| ≤ Cc := EE96.ae_abs_le hP.2.2.1
  have hK : 0 ≤ ∑ i, ∑ j, A i j + ∑ i, B i + Cc := by
    have hA0 : ∀ i j, 0 ≤ A i j := fun i j => ENNReal.toReal_nonneg
    have hB0 : ∀ i, 0 ≤ B i := fun i => ENNReal.toReal_nonneg
    have : 0 ≤ Cc := ENNReal.toReal_nonneg
    have : 0 ≤ ∑ i, ∑ j, A i j :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hA0 i j
    have : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _ => hB0 i
    linarith
  refine ⟨θ / 2, by positivity, ∑ i, ∑ j, A i j + ∑ i, B i + Cc + 1, by linarith, ?_, ?_⟩
  · intro u v
    have h := EE96.form_bound P hP A B Cc hA hB hC hK u v
    have : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith [h]
  · intro c₀ hc
    refine ⟨fun hb0 u => ?_, fun _ u => EE96.garding_int P hP θ c₀ B hθ0 hell hc hB u⟩
    have hB0 : ∀ᵐ x ∂(volume.restrict Ω), ∀ i, |P.b i x| ≤ (fun _ => (0 : ℝ)) i := by
      rw [ae_all_iff]; intro i
      filter_upwards [hb0 i] with x hx
      simp [hx]
    have h := EE96.garding_int P hP θ c₀ (fun _ => 0) hθ0 hell hc hB0 u
    have hl : 0 ≤ l2inner u u := by
      unfold l2inner
      exact integral_nonneg fun x => mul_self_nonneg _
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
      mul_zero, zero_add] at h
    nlinarith [h, hl]
