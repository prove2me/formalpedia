-- Prove2me | solution 1 for GittinsUCB.Patient.equation_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T08:17:03.520899+00:00
-- url     : https://prove2.me/submissions/fd63871f-181a-408f-9b96-8117670a50cb

import Mathlib
import Definitions.Def_GittinsUCB_Patient_Model
open MeasureTheory ProbabilityTheory Filter Asymptotics NNReal
open GittinsUCB.Patient

namespace GittinsEq2Aux

instance (μ : ℝ) (σ2 σW2 : ℝ≥0) : IsProbabilityMeasure (model μ σ2 σW2) := by
  unfold model; infer_instance

/-- Closed form of the posterior mean for a general prior. -/
lemma postMean_closed (m0 p s : ℝ) (hp : 0 < p) (hs : 0 < s) (t : ℕ) (ω : Ω) :
    postMean m0 p s t ω = postVar p s t * (m0 / p + (∑ i ∈ Finset.range t, R i ω) / s) := by
  induction t with
  | zero => simp [postMean, postVar]; field_simp
  | succ n ih =>
    have hv : 0 < 1 / p + (n : ℝ) / s := by positivity
    have hv' : 0 < 1 / p + ((n + 1 : ℕ) : ℝ) / s := by positivity
    simp only [postMean, ih, Finset.sum_range_succ]
    simp only [postVar] at hv hv' ⊢
    field_simp
    push_cast
    ring

/-- The first `t` noises form a Gaussian vector. -/
lemma hasGaussianLaw_noise (m0 : ℝ) (σ2 σW2 : ℝ≥0) (t : ℕ) :
    HasGaussianLaw (fun ω : Ω => fun i : Fin t => ω.2 i) (model m0 σ2 σW2) := by
  set Pi := Measure.infinitePi (fun _ : ℕ => gaussianReal 0 σW2) with hPi
  have hI : iIndepFun (fun (i : Fin t) (w : ℕ → ℝ) => w i) Pi :=
    (iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)).precomp
      (g := fun i : Fin t => (i : ℕ)) Fin.val_injective
  have hG : ∀ i : Fin t, HasGaussianLaw (fun w : ℕ → ℝ => w i) Pi := by
    intro i
    exact ⟨by rw [Measure.infinitePi_map_eval]; infer_instance⟩
  have hG' := iIndepFun.hasGaussianLaw hG hI
  refine ⟨?_⟩
  have e : (model m0 σ2 σW2).map (fun ω : Ω => fun i : Fin t => ω.2 i) =
      Pi.map (fun w : ℕ → ℝ => fun i : Fin t => w i) := by
    unfold model
    rw [show (fun ω : Ω => fun i : Fin t => ω.2 i) =
      (fun w : ℕ → ℝ => fun i : Fin t => w i) ∘ Prod.snd from rfl,
      ← Measure.map_map (measurable_pi_lambda _ fun i => measurable_pi_apply _) measurable_snd,
      Measure.map_snd_prod]
    simp [hPi]
  rw [e]
  exact hG'.isGaussian_map

lemma law_theta (m0 : ℝ) (σ2 σW2 : ℝ≥0) :
    (model m0 σ2 σW2).map (fun ω : Ω => ω.1) = gaussianReal m0 σ2 := by
  unfold model; rw [Measure.map_fst_prod]; simp

lemma law_noise (m0 : ℝ) (σ2 σW2 : ℝ≥0) (j : ℕ) :
    (model m0 σ2 σW2).map (fun ω : Ω => ω.2 j) = gaussianReal 0 σW2 := by
  unfold model
  rw [show (fun ω : Ω => ω.2 j) = (fun w : ℕ → ℝ => w j) ∘ Prod.snd from rfl,
    ← Measure.map_map (measurable_pi_apply j) measurable_snd, Measure.map_snd_prod]
  simp [Measure.infinitePi_map_eval]

lemma cov_self_of_law {X : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P] (hX : Measurable X)
    {m : ℝ} {v : ℝ≥0} (h : P.map X = gaussianReal m v) : cov[X, X; P] = v := by
  rw [covariance_self hX.aemeasurable]
  have := variance_map (μ := P) (X := id) (Y := X) (by fun_prop) hX.aemeasurable
  rw [h, variance_id_gaussianReal] at this
  simpa using this.symm

lemma cov_noise (m0 : ℝ) (σ2 σW2 : ℝ≥0) (i j : ℕ) :
    cov[fun ω : Ω => ω.2 i, fun ω : Ω => ω.2 j; model m0 σ2 σW2] =
      if i = j then (σW2 : ℝ) else 0 := by
  split_ifs with hij
  · subst hij
    exact cov_self_of_law ((measurable_pi_apply i).comp measurable_snd) (law_noise m0 σ2 σW2 i)
  · set Pi := Measure.infinitePi (fun _ : ℕ => gaussianReal 0 σW2) with hPi
    have hmap : (model m0 σ2 σW2).map Prod.snd = Pi := by
      unfold model; rw [Measure.map_snd_prod]; simp [hPi]
    have e := covariance_map (μ := model m0 σ2 σW2) (Z := Prod.snd)
      (X := fun w : ℕ → ℝ => w i) (Y := fun w : ℕ → ℝ => w j)
      (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable
      measurable_snd.aemeasurable
    rw [hmap] at e
    rw [show (fun ω : Ω => ω.2 i) = (fun w : ℕ → ℝ => w i) ∘ Prod.snd from rfl,
      show (fun ω : Ω => ω.2 j) = (fun w : ℕ → ℝ => w j) ∘ Prod.snd from rfl, ← e]
    have hI : iIndepFun (fun (k : ℕ) (w : ℕ → ℝ) => w k) Pi :=
      iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
    have hGi : HasGaussianLaw (fun w : ℕ → ℝ => w i) Pi :=
      ⟨by rw [Measure.infinitePi_map_eval]; infer_instance⟩
    have hGj : HasGaussianLaw (fun w : ℕ → ℝ => w j) Pi :=
      ⟨by rw [Measure.infinitePi_map_eval]; infer_instance⟩
    exact (hI.indepFun hij).covariance_eq_zero hGi.memLp_two hGj.memLp_two

/-- The key orthogonality: `θ - μ_t` has zero mean against every event of the history. -/
lemma key (m0 : ℝ) (σ2 σW2 : ℝ≥0) (hσ : 0 < σ2) (hW : 0 < σW2) (t : ℕ) (A : Set Ω)
    (hA : MeasurableSet[MeasurableSpace.comap (fun ω (s : Fin t) => R s ω) inferInstance] A) :
    ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω * (θ ω - postMean m0 σ2 σW2 t ω)
      ∂(model m0 σ2 σW2) = 0 := by
  obtain ⟨B, hB, rfl⟩ := hA
  set P := model m0 σ2 σW2 with hP
  set p : ℝ := (σ2 : ℝ) with hp
  set s : ℝ := (σW2 : ℝ) with hs
  have hp0 : 0 < p := by rw [hp]; exact_mod_cast hσ
  have hs0 : 0 < s := by rw [hs]; exact_mod_cast hW
  set v := postVar p s t with hv
  have hv' : v * (1 / p + (t : ℝ) / s) = 1 := by
    rw [hv]; unfold postVar; field_simp
  set c1 := 1 - v * t / s with hc1
  set c2 := v / s with hc2
  set X0 : Ω → ℝ := fun ω => c1 * ω.1 - c2 * ∑ i : Fin t, ω.2 i with hX0
  set H : Ω → (Fin t → ℝ) := fun ω j => R j ω with hH
  have hD : ∀ ω, θ ω - postMean m0 p s t ω = X0 ω - v * m0 / p := by
    intro ω
    rw [postMean_closed m0 p s hp0 hs0 t ω, ← hv]
    have e : ∑ i ∈ Finset.range t, R i ω = t * ω.1 + ∑ i : Fin t, ω.2 i := by
      rw [Finset.sum_range (fun i => R i ω)]
      simp [R, Finset.sum_add_distrib]
    rw [e]
    simp only [hX0, hc1, hc2, θ]
    field_simp
    ring
  -- Gaussian structure
  have hθG : HasGaussianLaw (fun ω : Ω => ω.1) P :=
    ⟨by rw [hP, law_theta]; infer_instance⟩
  have hWG := hasGaussianLaw_noise m0 σ2 σW2 t
  have hind : IndepFun (fun ω : Ω => ω.1) (fun ω : Ω => fun i : Fin t => ω.2 i) P := by
    rw [hP]; unfold model
    exact indepFun_prod (X := fun x : ℝ => x) (Y := fun (w : ℕ → ℝ) (i : Fin t) => w i)
      measurable_id (measurable_pi_lambda _ (fun i => measurable_pi_apply _))
  have hZ := IndepFun.hasGaussianLaw hθG hWG hind
  let Lm : (ℝ × (Fin t → ℝ)) →ₗ[ℝ] ((Unit → ℝ) × (Fin t → ℝ)) :=
    { toFun := fun z => (fun _ => c1 * z.1 - c2 * ∑ i, z.2 i, fun j => z.1 + z.2 j)
      map_add' := by
        intro x y
        ext
        · simp [Finset.sum_add_distrib]; ring
        · simp; ring
      map_smul' := by
        intro r x
        ext
        · simp
          rw [← Finset.mul_sum]
          ring
        · simp; ring }
  have hXY := hZ.map_fun (LinearMap.toContinuousLinearMap Lm)
  have hXY' : HasGaussianLaw (fun ω => (fun _ : Unit => X0 ω, fun j => H ω j)) P := by
    have e : (fun ω => (fun _ : Unit => X0 ω, fun j => H ω j)) =
        (fun ω : Ω => (LinearMap.toContinuousLinearMap Lm) (ω.1, fun i : Fin t => ω.2 i)) := by
      funext ω
      simp [Lm, hX0, hH, R]
    rw [e]; exact hXY
  -- covariances
  have hΘm : MemLp (fun ω : Ω => ω.1) 2 P := hθG.memLp_two
  have hWG1 : ∀ i : ℕ, HasGaussianLaw (fun ω : Ω => ω.2 i) P := fun i =>
    ⟨by rw [hP, law_noise]; infer_instance⟩
  have hWm : ∀ i : ℕ, MemLp (fun ω : Ω => ω.2 i) 2 P := fun i => (hWG1 i).memLp_two
  have hvarθ : cov[fun ω : Ω => ω.1, fun ω : Ω => ω.1; P] = p :=
    cov_self_of_law measurable_fst (law_theta m0 σ2 σW2)
  have hθW : ∀ j : ℕ, cov[fun ω : Ω => ω.1, fun ω : Ω => ω.2 j; P] = 0 := by
    intro j
    have : IndepFun (fun ω : Ω => ω.1) (fun ω : Ω => ω.2 j) P := by
      rw [hP]; unfold model
      exact indepFun_prod (X := fun x : ℝ => x) (Y := fun w : ℕ → ℝ => w j) measurable_id
        (measurable_pi_apply j)
    exact this.covariance_eq_zero hΘm (hWm j)
  have hWθ : ∀ j : ℕ, cov[fun ω : Ω => ω.2 j, fun ω : Ω => ω.1; P] = 0 := fun j => by
    rw [covariance_comm]; exact hθW j
  have hsumm : MemLp (fun ω : Ω => ∑ i : Fin t, ω.2 i) 2 P :=
    memLp_finset_sum (s := Finset.univ) (f := fun (i : Fin t) (ω : Ω) => ω.2 i)
      (fun i _ => hWm i)
  have h2 : v * (s + t * p) = p * s := by
    have e : v * (s + t * p) = (v * (1 / p + (t : ℝ) / s)) * (p * s) := by
      field_simp
    rw [e, hv', one_mul]
  have hcov : ∀ (u : Unit) (j : Fin t),
      cov[(fun (_ : Unit) (ω : Ω) => X0 ω) u, (fun (j : Fin t) (ω : Ω) => H ω j) j; P] = 0 := by
    intro u j
    have hHj : (fun ω => H ω j) = (fun ω : Ω => ω.1) + (fun ω : Ω => ω.2 j) := by
      funext ω; simp [hH, R]
    have hHm : MemLp (fun ω => H ω j) 2 P := by rw [hHj]; exact hΘm.add (hWm j)
    have hi : ∀ i : Fin t, cov[fun ω : Ω => ω.2 i, fun ω => H ω j; P] =
        if (i : ℕ) = (j : ℕ) then s else 0 := by
      intro i
      rw [hHj, covariance_add_right (hWm i) hΘm (hWm j), hWθ, cov_noise, zero_add]
    have h0 : cov[fun ω : Ω => ω.1, fun ω => H ω j; P] = p := by
      rw [hHj, covariance_add_right hΘm hΘm (hWm j), hvarθ, hθW, add_zero]
    show cov[fun ω => X0 ω, fun ω => H ω j; P] = 0
    rw [hX0]
    rw [covariance_fun_sub_left (hΘm.const_mul c1) (hsumm.const_mul c2) hHm,
      covariance_const_mul_left, covariance_const_mul_left,
      covariance_fun_sum_left (X := fun (i : Fin t) (ω : Ω) => ω.2 i) (fun i => hWm i) hHm, h0, Finset.sum_congr rfl (fun i _ => hi i)]
    have hsum : ∑ i : Fin t, (if (i : ℕ) = (j : ℕ) then s else 0) = s := by
      simp [Fin.val_inj]
    rw [hsum, hc1, hc2]
    field_simp
    linear_combination (-1 : ℝ) * h2
  have hindXH := hXY'.indepFun_of_covariance_eval (X := fun (_ : Unit) (ω : Ω) => X0 ω)
    (Y := fun (j : Fin t) (ω : Ω) => H ω j) hcov
  -- means
  have hmeanθ : ∫ ω, ω.1 ∂P = m0 := by
    have h := integral_map (μ := P) (φ := fun ω : Ω => ω.1) (f := fun x : ℝ => x)
      measurable_fst.aemeasurable aestronglyMeasurable_id
    rw [hP, law_theta, integral_id_gaussianReal] at h
    exact h.symm
  have hmeanW : ∀ i : ℕ, ∫ ω, ω.2 i ∂P = 0 := by
    intro i
    have h := integral_map (μ := P) (φ := fun ω : Ω => ω.2 i) (f := fun x : ℝ => x)
      ((measurable_pi_apply i).comp measurable_snd).aemeasurable aestronglyMeasurable_id
    rw [hP, law_noise, integral_id_gaussianReal] at h
    exact h.symm
  have hθint : Integrable (fun ω : Ω => ω.1) P := hθG.integrable
  have hWint : ∀ i : ℕ, Integrable (fun ω : Ω => ω.2 i) P := fun i => (hWG1 i).integrable
  have hmeanX : ∫ ω, (X0 ω - v * m0 / p) ∂P = 0 := by
    have hX0int : Integrable X0 P :=
      (hθint.const_mul c1).sub ((integrable_finsetSum (s := Finset.univ) (f := fun (i : Fin t) (ω : Ω) => ω.2 i) (fun i _ => hWint i)).const_mul c2)
    rw [integral_sub hX0int (integrable_const _), integral_const, hX0]
    simp only [probReal_univ, one_smul, smul_eq_mul, one_mul]
    rw [integral_sub (hθint.const_mul c1)
      ((integrable_finsetSum (s := Finset.univ) (f := fun (i : Fin t) (ω : Ω) => ω.2 i) (fun i _ => hWint i)).const_mul c2),
      integral_const_mul, integral_const_mul, integral_finsetSum (s := Finset.univ) (f := fun (i : Fin t) (ω : Ω) => ω.2 i) (fun i _ => hWint i),
      hmeanθ]
    simp only [hmeanW, Finset.sum_const_zero, mul_zero, sub_zero, hc1]
    field_simp
    linear_combination (-m0) * h2
  -- the integral factorizes
  have hind2 : IndepFun (fun ω => B.indicator (fun _ => (1 : ℝ)) (H ω))
      (fun ω => X0 ω - v * m0 / p) P :=
    (hindXH.comp (φ := fun f : Unit → ℝ => f () - v * m0 / p)
      (ψ := B.indicator (fun _ => (1 : ℝ)))
      ((measurable_pi_apply ()).sub_const _) (measurable_const.indicator hB)).symm
  have hHmeas : Measurable H := measurable_pi_lambda _ (fun j =>
    measurable_fst.add ((measurable_pi_apply _).comp measurable_snd))
  have hrw : ∀ ω, (H ⁻¹' B).indicator (fun _ => (1 : ℝ)) ω * (θ ω - postMean m0 p s t ω) =
      B.indicator (fun _ => (1 : ℝ)) (H ω) * (X0 ω - v * m0 / p) := by
    intro ω; rw [hD]; rfl
  simp_rw [hrw]
  rw [hind2.integral_fun_mul_eq_mul_integral
    ((measurable_const.indicator hB).comp hHmeas).aestronglyMeasurable
    (by
      have hX0m : Measurable X0 := by
        rw [hX0]
        exact (measurable_const.mul measurable_fst).sub (measurable_const.mul
          (Finset.measurable_sum _ (fun i _ => (measurable_pi_apply _).comp measurable_snd)))
      exact (hX0m.sub_const _).aestronglyMeasurable),
    hmeanX, mul_zero]

end GittinsEq2Aux

open GittinsEq2Aux in
theorem solution (σW2 : ℝ≥0) (hW : 0 < σW2)
    (γ lam μ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (σ2 : ℝ≥0) (hσ : 0 < σ2) (τ : Ω → ℕ∞)
    (hτ : IsRetirementTime τ) :
    (∫ ω, stoppedReward γ lam (fun _ => θ) τ ω ∂(model μ σ2 σW2)) =
      ∫ ω, stoppedReward γ lam (postMean μ (σ2 : ℝ) (σW2 : ℝ)) τ ω
        ∂(model μ σ2 σW2) := by
  set P := model μ σ2 σW2 with hP
  set p : ℝ := (σ2 : ℝ) with hp
  set s : ℝ := (σW2 : ℝ) with hs
  have hp0 : 0 < p := by rw [hp]; exact_mod_cast hσ
  have hs0 : 0 < s := by rw [hs]; exact_mod_cast hW
  set M : ℕ → Ω → ℝ := postMean μ p s with hM
  -- the events `{t ≤ τ}`
  set A : ℕ → Set Ω := fun t => {ω | (t : ℕ∞) ≤ τ ω} with hA
  have hAc : ∀ t, MeasurableSet[MeasurableSpace.comap (fun ω (j : Fin t) => R j ω) inferInstance]
      (A t) := by
    intro t
    cases t with
    | zero =>
      have : A 0 = Set.univ := by ext ω; simp [hA]
      rw [this]; exact @MeasurableSet.univ _ (MeasurableSpace.comap _ _)
    | succ n =>
      have h : A (n + 1) = {ω | τ ω ≤ (n : ℕ∞)}ᶜ := by
        ext ω
        simp only [hA, Set.mem_setOf_eq, Set.mem_compl_iff, not_le, Nat.cast_add, Nat.cast_one]
        exact ENat.add_one_le_iff (ENat.coe_ne_top n)
      rw [h]
      exact (hτ.1 n).compl
  have hcomap_le : ∀ t, MeasurableSpace.comap (fun ω (j : Fin t) => R j ω) inferInstance ≤
      (inferInstance : MeasurableSpace Ω) := by
    intro t
    apply Measurable.comap_le
    exact measurable_pi_lambda _ (fun j => measurable_fst.add
      ((measurable_pi_apply _).comp measurable_snd))
  have hAm : ∀ t, MeasurableSet (A t) := fun t => hcomap_le t _ (hAc t)
  -- basic integrability
  have hθG : HasGaussianLaw (fun ω : Ω => ω.1) P := ⟨by rw [hP, law_theta]; infer_instance⟩
  have hWG1 : ∀ i : ℕ, HasGaussianLaw (fun ω : Ω => ω.2 i) P := fun i =>
    ⟨by rw [hP, law_noise]; infer_instance⟩
  have hθint : Integrable (fun ω : Ω => ω.1) P := hθG.integrable
  have hWint : ∀ i : ℕ, Integrable (fun ω : Ω => ω.2 i) P := fun i => (hWG1 i).integrable
  set cθ := ∫ ω, |ω.1 - μ| ∂P with hcθ
  set cW := ∫ ω, |ω.2 0| ∂P with hcW
  have hcθ0 : 0 ≤ cθ := integral_nonneg (fun ω => abs_nonneg _)
  have hcW0 : 0 ≤ cW := integral_nonneg (fun ω => abs_nonneg _)
  have hWabs : ∀ i : ℕ, ∫ ω, |ω.2 i| ∂P = cW := by
    intro i
    have h1 := integral_map (μ := P) (φ := fun ω : Ω => ω.2 i) (f := fun x : ℝ => |x|)
      ((measurable_pi_apply i).comp measurable_snd).aemeasurable
      continuous_abs.aestronglyMeasurable
    have h2 := integral_map (μ := P) (φ := fun ω : Ω => ω.2 0) (f := fun x : ℝ => |x|)
      ((measurable_pi_apply 0).comp measurable_snd).aemeasurable
      continuous_abs.aestronglyMeasurable
    rw [hP, law_noise] at h1 h2
    rw [hcW, ← h1, ← h2]
  -- closed form and the posterior-mean deviation
  have hMclosed : ∀ t ω, M t ω - μ = postVar p s t * t / s * (ω.1 - μ) +
      postVar p s t / s * ∑ i ∈ Finset.range t, ω.2 i := by
    intro t ω
    have hv' : postVar p s t * (1 / p + (t : ℝ) / s) = 1 := by unfold postVar; field_simp
    rw [hM, postMean_closed μ p s hp0 hs0 t ω]
    have e : ∑ i ∈ Finset.range t, R i ω = t * ω.1 + ∑ i ∈ Finset.range t, ω.2 i := by
      simp [R, Finset.sum_add_distrib]
    rw [e]
    linear_combination μ * hv'
  have hratio : ∀ t : ℕ, postVar p s t * t / s ≤ 1 := by
    intro t
    unfold postVar
    rw [div_le_one hs0]
    have hpos : 0 < 1 / p + (t : ℝ) / s := by positivity
    rw [inv_mul_eq_div, div_le_iff₀ hpos]
    have : (t : ℝ) = (t : ℝ) / s * s := by field_simp
    nlinarith [div_pos one_pos hp0]
  have hMint : ∀ t, Integrable (M t) P := by
    intro t
    have e : M t = fun ω => μ + (postVar p s t * t / s * (ω.1 - μ) +
        postVar p s t / s * ∑ i ∈ Finset.range t, ω.2 i) := by
      funext ω; rw [← hMclosed]; ring
    rw [e]
    exact (integrable_const μ).add (((hθint.sub (integrable_const μ)).const_mul _).add
      ((integrable_finsetSum (s := Finset.range t) (f := fun i (ω : Ω) => ω.2 i)
        (fun i _ => hWint i)).const_mul _))
  set K := |μ - lam| + cθ + cW with hK
  have hMbound : ∀ t, ∫ ω, |M t ω - lam| ∂P ≤ K := by
    intro t
    set v := postVar p s t with hv
    have hv0 : 0 ≤ v := by rw [hv]; unfold postVar; positivity
    have hc1 : 0 ≤ v * t / s := by positivity
    have hc2 : 0 ≤ v / s := by positivity
    have hpt : ∀ ω, |M t ω - lam| ≤ |μ - lam| + (v * t / s * |ω.1 - μ| +
        v / s * ∑ i ∈ Finset.range t, |ω.2 i|) := by
      intro ω
      have e : M t ω - lam = (μ - lam) + (M t ω - μ) := by ring
      rw [e, hMclosed, ← hv]
      have h1 : |v * t / s * (ω.1 - μ) + v / s * ∑ i ∈ Finset.range t, ω.2 i| ≤
          v * t / s * |ω.1 - μ| + v / s * ∑ i ∈ Finset.range t, |ω.2 i| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hc1, abs_of_nonneg hc2]
        have := mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs
          (fun i => ω.2 i) (Finset.range t)) hc2
        linarith
      have h2 := abs_add_le (μ - lam)
        (v * t / s * (ω.1 - μ) + v / s * ∑ i ∈ Finset.range t, ω.2 i)
      linarith
    have hsumabs : Integrable (fun ω : Ω => ∑ i ∈ Finset.range t, |ω.2 i|) P :=
      integrable_finsetSum (s := Finset.range t) (f := fun i (ω : Ω) => |ω.2 i|)
        (fun i _ => (hWint i).abs)
    have hRint : Integrable (fun ω : Ω => |μ - lam| + (v * t / s * |ω.1 - μ| +
        v / s * ∑ i ∈ Finset.range t, |ω.2 i|)) P :=
      (integrable_const _).add ((((hθint.sub (integrable_const μ)).abs).const_mul _).add
        (hsumabs.const_mul _))
    refine (integral_mono ((hMint t).sub (integrable_const lam)).abs hRint hpt).trans ?_
    have hθabs : Integrable (fun ω : Ω => |ω.1 - μ|) P := (hθint.sub (integrable_const μ)).abs
    rw [integral_add (f := fun _ => |μ - lam|) (g := fun ω : Ω => v * t / s * |ω.1 - μ| +
        v / s * ∑ i ∈ Finset.range t, |ω.2 i|) (integrable_const _)
        ((hθabs.const_mul _).add (hsumabs.const_mul _)),
      integral_add (f := fun ω : Ω => v * t / s * |ω.1 - μ|)
        (g := fun ω : Ω => v / s * ∑ i ∈ Finset.range t, |ω.2 i|)
        (hθabs.const_mul _) (hsumabs.const_mul _),
      integral_const_mul, integral_const_mul,
      integral_finsetSum (s := Finset.range t) (f := fun i (ω : Ω) => |ω.2 i|)
        (fun i _ => (hWint i).abs)]
    simp only [hWabs, Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_const,
      probReal_univ, one_smul, smul_eq_mul, one_mul]
    rw [← hcθ]
    have h1 : v * t / s * cθ ≤ cθ := by
      have := mul_le_mul_of_nonneg_right (hratio t) hcθ0
      rw [← hv] at this; linarith
    have h2 : v / s * (t * cW) ≤ cW := by
      have := mul_le_mul_of_nonneg_right (hratio t) hcW0
      rw [← hv] at this
      have e : v / s * (t * cW) = v * t / s * cW := by ring
      linarith
    linarith
  -- termwise functions
  set a : ℕ → Ω → ℝ := fun t => (A t).indicator (fun ω => γ ^ t * (θ ω - lam)) with ha
  set b : ℕ → Ω → ℝ := fun t => (A t).indicator (fun ω => γ ^ t * (M t ω - lam)) with hb
  have hL : (fun ω => stoppedReward γ lam (fun _ => θ) τ ω) = fun ω => ∑' t, a t ω := by
    funext ω
    unfold stoppedReward
    congr 1
    funext t
    simp only [ha, hA, Set.indicator, Set.mem_setOf_eq]
  have hR : (fun ω => stoppedReward γ lam (postMean μ p s) τ ω) = fun ω => ∑' t, b t ω := by
    funext ω
    unfold stoppedReward
    congr 1
    funext t
    simp only [hb, hA, hM, Set.indicator, Set.mem_setOf_eq]
  have hsubθ : Integrable (fun ω : Ω => θ ω - lam) P := hθint.sub (integrable_const lam)
  have haint : ∀ t, Integrable (a t) P := fun t =>
    (hsubθ.const_mul (γ ^ t)).indicator (hAm t)
  have hbint : ∀ t, Integrable (b t) P := fun t =>
    (((hMint t).sub (integrable_const lam)).const_mul (γ ^ t)).indicator (hAm t)
  have haS : Summable fun t => ∫ ω, ‖a t ω‖ ∂P := by
    refine Summable.of_nonneg_of_le (fun t => integral_nonneg (fun ω => norm_nonneg _))
      (fun t => ?_) ((summable_geometric_of_lt_one hγ0.le hγ1).mul_right
        (∫ ω, |θ ω - lam| ∂P))
    rw [← integral_const_mul]
    refine integral_mono (haint t).norm (hsubθ.abs.const_mul _) (fun ω => ?_)
    refine (norm_indicator_le_norm_self _ _).trans ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hγ0 t)]
  have hbS : Summable fun t => ∫ ω, ‖b t ω‖ ∂P := by
    refine Summable.of_nonneg_of_le (fun t => integral_nonneg (fun ω => norm_nonneg _))
      (fun t => ?_) ((summable_geometric_of_lt_one hγ0.le hγ1).mul_right K)
    have h1 : ∫ ω, ‖b t ω‖ ∂P ≤ γ ^ t * ∫ ω, |M t ω - lam| ∂P := by
      rw [← integral_const_mul]
      refine integral_mono (hbint t).norm
        (((hMint t).sub (integrable_const lam)).abs.const_mul _) (fun ω => ?_)
      refine (norm_indicator_le_norm_self _ _).trans ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hγ0 t)]
    exact h1.trans (mul_le_mul_of_nonneg_left (hMbound t) (pow_pos hγ0 t).le)
  have hterm : ∀ t, ∫ ω, a t ω ∂P = ∫ ω, b t ω ∂P := by
    intro t
    have hk := key μ σ2 σW2 hσ hW t (A t) (hAc t)
    have e : ∀ ω, a t ω - b t ω =
        γ ^ t * ((A t).indicator (fun _ => (1 : ℝ)) ω * (θ ω - postMean μ σ2 σW2 t ω)) := by
      intro ω
      simp only [ha, hb, hM, Set.indicator]
      split_ifs <;> ring
    have hdiff : ∫ ω, (a t ω - b t ω) ∂P = 0 := by
      simp_rw [e]
      rw [integral_const_mul, hk, mul_zero]
    rw [integral_sub (haint t) (hbint t)] at hdiff
    linarith
  rw [hL, hR, ← integral_tsum_of_summable_integral_norm haint haS,
    ← integral_tsum_of_summable_integral_norm hbint hbS]
  exact tsum_congr hterm
