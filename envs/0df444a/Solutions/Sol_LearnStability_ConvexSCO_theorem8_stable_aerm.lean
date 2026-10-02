-- Prove2me | solution 1 for LearnStability.ConvexSCO.theorem8_stable_aerm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T13:21:14.61276+00:00
-- url     : https://prove2.me/submissions/16e0981a-a01b-4293-9a17-61c74646830e

import Mathlib
import Definitions.Def_LearnStability_ConvexSCO_Setting

set_option autoImplicit false

namespace Pd5d217db

open MeasureTheory LearnStability.ConvexSCO

/-! ### Exchangeability of product measures (coordinate swap) -/

lemma perm_mp {Z : Type*} [MeasurableSpace Z] {ι : Type*} [Fintype ι] (D : Measure Z)
    [SigmaFinite D] (π : Equiv.Perm ι) :
    MeasurePreserving (fun x : ι → Z => fun i => x (π i)) (Measure.pi fun _ => D)
      (Measure.pi fun _ => D) := by
  have hmeas : Measurable (fun x : ι → Z => fun i => x (π i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (π i)
  refine ⟨hmeas, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have : (fun x : ι → Z => fun i => x (π i)) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => s (π.symm i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h i
      have := h (π.symm i)
      simpa using this
    · intro h i
      have := h (π i)
      simpa using this
  rw [this, Measure.pi_pi]
  exact Equiv.prod_comp π.symm (fun i => D (s i))

lemma swap_mp {Z : Type*} [MeasurableSpace Z] {m : ℕ} (D : Measure Z) [IsProbabilityMeasure D]
    (i : Fin m) :
    MeasurePreserving (fun p : (Fin m → Z) × Z => (Function.update p.1 i p.2, p.1 i))
      ((Measure.pi fun _ : Fin m => D).prod D) ((Measure.pi fun _ : Fin m => D).prod D) := by
  set J := MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin m) => Z) with hJdef
  have hJs : MeasurePreserving J.symm ((Measure.pi fun _ : Fin m => D).prod D)
      (Measure.pi fun _ : Option (Fin m) => D) :=
    ⟨J.symm.measurable, Measure.pi_map_piOptionEquivProd (fun _ : Option (Fin m) => D)⟩
  have hJ : MeasurePreserving J (Measure.pi fun _ : Option (Fin m) => D)
      ((Measure.pi fun _ : Fin m => D).prod D) :=
    MeasurePreserving.symm J.symm hJs
  have hσ := perm_mp D (Equiv.swap (none : Option (Fin m)) (some i))
  have hc := hJ.comp (hσ.comp hJs)
  convert hc using 1
  funext p
  obtain ⟨x, rfl⟩ := J.surjective p
  simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  refine Prod.ext ?_ ?_
  · show Function.update (fun j => x (some j)) i (x none) =
      fun j => x (Equiv.swap none (some i) (some j))
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Equiv.swap_apply_def, hj]
  · show x (some i) = x (Equiv.swap none (some i) none)
    simp

lemma integrable_of_abs_le' {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : Measurable g) (c : ℝ) (h : ∀ x, |g x| ≤ c) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable c (Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using h x)

lemma sq_integral_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {g : α → ℝ} (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) :
    (∫ x, |g x| ∂μ) ^ 2 ≤ ∫ x, (g x) ^ 2 ∂μ := by
  have hi1 : Integrable (fun x => |g x|) μ :=
    integrable_of_abs_le' hg.abs C fun x => by rw [abs_abs]; exact hC x
  have hi2 : Integrable (fun x => (g x) ^ 2) μ :=
    integrable_of_abs_le' (hg.pow_const 2) (C ^ 2) fun x => by
      have h1 := hC x
      have h0 := abs_nonneg (g x)
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      nlinarith
  set a := ∫ x, |g x| ∂μ with ha
  have h0 : 0 ≤ ∫ x, (|g x| - a) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have e : (fun x => (|g x| - a) ^ 2) = fun x => (g x) ^ 2 - (2 * a) * |g x| + a ^ 2 := by
    funext x
    rw [sub_sq, sq_abs]
    ring
  have hi3 : Integrable (fun x => (g x) ^ 2 - (2 * a) * |g x|) μ := hi2.sub (hi1.const_mul _)
  rw [e, integral_add hi3 (integrable_const _),
    integral_sub hi2 (hi1.const_mul _), integral_const_mul, integral_const] at h0
  have hu : μ.real Set.univ = 1 := by simp
  rw [hu, one_smul, ← ha] at h0
  nlinarith

section Main

variable {H Z : Type*} [MeasurableSpace Z]

lemma abs_risk_le {f : H → Z → ℝ} {C : ℝ} (hC : ∀ h z, |f h z| ≤ C) (D : Measure Z)
    [IsProbabilityMeasure D] (h : H) : |risk f D h| ≤ C := by
  unfold risk
  have := norm_integral_le_of_norm_le_const (μ := D) (f := f h) (C := C)
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hC h z)
  rw [Real.norm_eq_abs] at this
  simpa using this

lemma abs_empRisk_le {f : H → Z → ℝ} {C : ℝ} (hC : ∀ h z, |f h z| ≤ C) {m : ℕ} (hm : 1 ≤ m)
    (S : Fin m → Z) (h : H) : |empRisk f S h| ≤ C := by
  unfold empRisk
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  rw [abs_div, abs_of_pos hm', div_le_iff₀ hm']
  calc |∑ i, f h (S i)| ≤ ∑ i, |f h (S i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, C := Finset.sum_le_sum fun i _ => hC h (S i)
    _ = C * m := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

lemma ermValue_le {f : H → Z → ℝ} {C : ℝ} (hC : ∀ h z, |f h z| ≤ C) {m : ℕ} (hm : 1 ≤ m)
    (S : Fin m → Z) (h : H) : ermValue f S ≤ empRisk f S h :=
  ciInf_le ⟨-C, by rintro _ ⟨h, rfl⟩; exact (abs_le.mp (abs_empRisk_le hC hm S h)).1⟩ h

lemma abs_ermValue_le [Nonempty H] {f : H → Z → ℝ} {C : ℝ} (hC : ∀ h z, |f h z| ≤ C) {m : ℕ}
    (hm : 1 ≤ m) (S : Fin m → Z) : |ermValue f S| ≤ C := by
  rw [abs_le]
  constructor
  · exact le_ciInf fun h => (abs_le.mp (abs_empRisk_le hC hm S h)).1
  · exact (ermValue_le hC hm S (Classical.arbitrary H)).trans
      (abs_le.mp (abs_empRisk_le hC hm S _)).2

lemma opt_le_risk {f : H → Z → ℝ} {C : ℝ} (hC : ∀ h z, |f h z| ≤ C) (D : Measure Z)
    [IsProbabilityMeasure D] (h : H) : optRisk f D ≤ risk f D h :=
  ciInf_le ⟨-C, by rintro _ ⟨h, rfl⟩; exact (abs_le.mp (abs_risk_le hC D h)).1⟩ h

lemma measurable_empRisk_const {f : H → Z → ℝ} (hf : ∀ h, Measurable (f h)) (m : ℕ) (h : H) :
    Measurable (fun S : Fin m → Z => empRisk f S h) := by
  unfold empRisk
  exact (Finset.measurable_sum _ fun i _ => (hf h).comp (measurable_pi_apply i)).div_const _

lemma integral_empRisk {f : H → Z → ℝ} {C : ℝ} (hC : ∀ h z, |f h z| ≤ C)
    (hf : ∀ h, Measurable (f h)) (D : Measure Z) [IsProbabilityMeasure D]
    {m : ℕ} (hm : 1 ≤ m) (h : H) :
    ∫ S, empRisk f S h ∂(Measure.pi fun _ : Fin m => D) = risk f D h := by
  have hm' : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    exact this.ne'
  have hi : ∀ i : Fin m, Integrable (fun S : Fin m → Z => f h (S i))
      (Measure.pi fun _ : Fin m => D) := fun i =>
    integrable_of_abs_le' ((hf h).comp (measurable_pi_apply i)) C fun S => hC h _
  have h1 : ∀ i : Fin m, ∫ S, f h (S i) ∂(Measure.pi fun _ : Fin m => D) = risk f D h :=
    fun i => integral_comp_eval (hf h).aestronglyMeasurable
  have hsum : ∫ S, ∑ i, f h (S i) ∂(Measure.pi fun _ : Fin m => D)
      = ∑ i, ∫ S, f h (S i) ∂(Measure.pi fun _ : Fin m => D) :=
    integral_finsetSum _ fun i _ => hi i
  unfold empRisk
  rw [integral_div, hsum, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_cancel_left₀ _ hm']

/-- The variance bound: `E (F_S(h) - F(h))^2 ≤ C^2 / m`. -/
lemma second_moment {f : H → Z → ℝ} {C : ℝ} (hC : ∀ h z, |f h z| ≤ C)
    (hf : ∀ h, Measurable (f h)) (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (hm : 1 ≤ m) (h : H) :
    ∫ S, (empRisk f S h - risk f D h) ^ 2 ∂(Measure.pi fun _ : Fin m => D) ≤ C ^ 2 / m := by
  classical
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  set r := risk f D h with hr
  have hYm : ∀ i : Fin m, Measurable (fun S : Fin m → Z => f h (S i) - r) := fun i =>
    ((hf h).comp (measurable_pi_apply i)).sub_const _
  have hYb : ∀ (i : Fin m) (S : Fin m → Z), |f h (S i) - r| ≤ 2 * C := by
    intro i S
    calc |f h (S i) - r| ≤ |f h (S i)| + |r| := abs_sub _ _
      _ ≤ C + C := add_le_add (hC _ _) (abs_risk_le hC D h)
      _ = 2 * C := by ring
  have hB0 : ∀ (i : Fin m) (S : Fin m → Z), 0 ≤ 2 * C := fun i S =>
    (abs_nonneg _).trans (hYb i S)
  have hind := ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin m => D)
    (X := fun _ : Fin m => fun z : Z => f h z - r)
    (fun _ => ((hf h).sub_const _).aemeasurable)
  have hfi : ∀ i : Fin m, Integrable (fun S : Fin m → Z => f h (S i))
      (Measure.pi fun _ : Fin m => D) := fun i =>
    integrable_of_abs_le' ((hf h).comp (measurable_pi_apply i)) C fun S => hC _ _
  have hmean : ∀ i : Fin m, ∫ S : Fin m → Z, f h (S i) ∂(Measure.pi fun _ : Fin m => D) = r :=
    fun i => integral_comp_eval (hf h).aestronglyMeasurable
  have h0 : ∀ i : Fin m, ∫ S : Fin m → Z, (f h (S i) - r)
      ∂(Measure.pi fun _ : Fin m => D) = 0 := by
    intro i
    rw [integral_sub (hfi i) (integrable_const _), hmean i]
    simp
  have hoff : ∀ i j : Fin m, i ≠ j → ∫ S : Fin m → Z,
      (f h (S i) - r) * (f h (S j) - r)
        ∂(Measure.pi fun _ : Fin m => D) = 0 := by
    intro i j hij
    have hI := hind.indepFun hij
    have := hI.integral_mul_eq_mul_integral (hYm i).aestronglyMeasurable
      (hYm j).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, h0 i, zero_mul]
  have hI2 : ∀ i j : Fin m, Integrable (fun S : Fin m → Z =>
      (f h (S i) - r) * (f h (S j) - r)) (Measure.pi fun _ : Fin m => D) :=
    fun i j => integrable_of_abs_le' ((hYm i).mul (hYm j)) ((2 * C) * (2 * C)) fun S => by
      rw [abs_mul]
      exact mul_le_mul (hYb i S) (hYb j S) (abs_nonneg _) (hB0 i S)
  have hdiag : ∀ i : Fin m, ∫ S : Fin m → Z, (f h (S i) - r) * (f h (S i) - r)
      ∂(Measure.pi fun _ : Fin m => D) ≤ C ^ 2 := by
    intro i
    have hsq : Integrable (fun S : Fin m → Z => f h (S i) ^ 2) (Measure.pi fun _ : Fin m => D) :=
      integrable_of_abs_le' (((hf h).comp (measurable_pi_apply i)).pow_const 2) (C ^ 2)
        fun S => by
          have h1 := hC h (S i)
          have h0 := abs_nonneg (f h (S i))
          rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
          nlinarith
    have e : ∀ S : Fin m → Z, (f h (S i) - r) * (f h (S i) - r)
        = (f h (S i) ^ 2 - (2 * r) * f h (S i)) + r ^ 2 := fun S => by ring
    have i1 : ∫ S : Fin m → Z, ((f h (S i) ^ 2 - (2 * r) * f h (S i)) + r ^ 2)
        ∂(Measure.pi fun _ : Fin m => D) =
        ∫ S : Fin m → Z, (f h (S i) ^ 2 - (2 * r) * f h (S i)) ∂(Measure.pi fun _ : Fin m => D)
          + ∫ _S : Fin m → Z, r ^ 2 ∂(Measure.pi fun _ : Fin m => D) :=
      integral_add (hsq.sub ((hfi i).const_mul _)) (integrable_const _)
    have i2 : ∫ S : Fin m → Z, (f h (S i) ^ 2 - (2 * r) * f h (S i))
        ∂(Measure.pi fun _ : Fin m => D) =
        ∫ S : Fin m → Z, f h (S i) ^ 2 ∂(Measure.pi fun _ : Fin m => D)
          - ∫ S : Fin m → Z, (2 * r) * f h (S i) ∂(Measure.pi fun _ : Fin m => D) :=
      integral_sub hsq ((hfi i).const_mul _)
    have i3 : ∫ S : Fin m → Z, (2 * r) * f h (S i) ∂(Measure.pi fun _ : Fin m => D)
        = (2 * r) * ∫ S : Fin m → Z, f h (S i) ∂(Measure.pi fun _ : Fin m => D) :=
      integral_const_mul _ _
    have hu : (Measure.pi fun _ : Fin m => D).real Set.univ = 1 := by simp
    rw [integral_congr_ae (ae_of_all _ e), i1, i2, i3, hmean i, integral_const, hu, one_smul]
    have hle := integral_mono hsq (integrable_const (C ^ 2))
      (μ := Measure.pi fun _ : Fin m => D) (fun S => by
        have h1 := hC h (S i)
        have h0 := abs_nonneg (f h (S i))
        show f h (S i) ^ 2 ≤ C ^ 2
        rw [← sq_abs]
        nlinarith)
    rw [integral_const, hu, one_smul] at hle
    nlinarith [sq_nonneg r]
  have hexp : ∀ S : Fin m → Z, (empRisk f S h - r) ^ 2 =
      (∑ i, ∑ j, (f h (S i) - r) * (f h (S j) - r)) / (m:ℝ) ^ 2 := by
    intro S
    have e1 : empRisk f S h - r = (∑ i, (f h (S i) - r)) / m := by
      unfold empRisk
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    rw [e1, div_pow, sq (∑ i, _), Finset.sum_mul_sum]
  calc ∫ S, (empRisk f S h - r) ^ 2 ∂(Measure.pi fun _ : Fin m => D)
      = ∫ S, (∑ i, ∑ j, (f h (S i) - r) * (f h (S j) - r)) / (m:ℝ) ^ 2
          ∂(Measure.pi fun _ : Fin m => D) := by
        congr 1
        funext S
        exact hexp S
    _ = (∑ i, ∑ j, ∫ S : Fin m → Z, (f h (S i) - r) * (f h (S j) - r)
          ∂(Measure.pi fun _ : Fin m => D)) / (m:ℝ) ^ 2 := by
        rw [integral_div, integral_finsetSum _ (fun i _ => integrable_finsetSum _
          fun j _ => hI2 i j)]
        congr 1
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hI2 i j
    _ ≤ (∑ i : Fin m, ∑ j : Fin m, if i = j then C ^ 2 else 0) / (m:ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl]
          exact hdiag i
        · rw [if_neg hij, hoff i j hij]
    _ = C ^ 2 / m := by
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

lemma abs_moment {f : H → Z → ℝ} {C : ℝ} (hC : ∀ h z, |f h z| ≤ C)
    (hf : ∀ h, Measurable (f h)) (D : Measure Z)
    [IsProbabilityMeasure D] {m : ℕ} (hm : 1 ≤ m) (h : H) :
    ∫ S, |empRisk f S h - risk f D h| ∂(Measure.pi fun _ : Fin m => D) ≤
      C / Real.sqrt m := by
  have hB : 0 ≤ C := (abs_nonneg _).trans (abs_risk_le hC D h)
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hsq : (0:ℝ) < Real.sqrt m := Real.sqrt_pos.mpr hm'
  have h1 := sq_integral_abs_le (μ := Measure.pi fun _ : Fin m => D)
    (g := fun S : Fin m → Z => empRisk f S h - risk f D h)
    ((measurable_empRisk_const hf m h).sub_const _) (2 * C) (fun S => by
      have a1 := abs_empRisk_le hC hm S h
      have a2 := abs_risk_le hC D h
      calc |empRisk f S h - risk f D h| ≤ |empRisk f S h| + |risk f D h| := abs_sub _ _
        _ ≤ C + C := add_le_add a1 a2
        _ = 2 * C := by ring)
  have h2 := second_moment hC hf D hm h
  have h3 : (C / Real.sqrt m) ^ 2 = C ^ 2 / m := by
    rw [div_pow, Real.sq_sqrt hm'.le]
  have h4 : 0 ≤ C / Real.sqrt m := by positivity
  have h5 : (∫ S, |empRisk f S h - risk f D h| ∂(Measure.pi fun _ : Fin m => D)) ^ 2
      ≤ (C / Real.sqrt m) ^ 2 := by
    rw [h3]
    exact h1.trans h2
  exact (sq_le_sq₀ (integral_nonneg fun S => abs_nonneg _) h4).mp h5

/-! ### The stability identity -/

lemma measurable_risk_rule {f : H → Z → ℝ} {A : (m : ℕ) → (Fin m → Z) → H}
    (hA : IsMeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) :
    Measurable (fun S : Fin m → Z => risk f D (A m S)) :=
  ((hA m).stronglyMeasurable.integral_prod_right' (ν := D)).measurable

lemma measurable_empRisk_rule {f : H → Z → ℝ} {A : (m : ℕ) → (Fin m → Z) → H}
    (hA : IsMeasurableRule f A) (m : ℕ) :
    Measurable (fun S : Fin m → Z => empRisk f S (A m S)) := by
  unfold empRisk
  refine Measurable.div_const ?_ _
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (hA m).comp (measurable_id.prodMk (measurable_pi_apply i))

/-- `E[F(A S) - F_S(A S)] = -(1/m) ∑_i E_{S,z}[f(A(S^{i←z}); z) - f(A S; z)]`. -/
lemma gen_eq {f : H → Z → ℝ} {C : ℝ} (hC : ∀ h z, |f h z| ≤ C)
    {A : (m : ℕ) → (Fin m → Z) → H} (hA : IsMeasurableRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] {m : ℕ} (hm : 1 ≤ m) :
    ∫ S, (risk f D (A m S) - empRisk f S (A m S)) ∂(Measure.pi fun _ : Fin m => D) =
      -(∑ i : Fin m, ∫ q, (f (A m (Function.update q.1 i q.2)) q.2 - f (A m q.1) q.2)
        ∂((Measure.pi fun _ : Fin m => D).prod D)) / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hW : Measurable (fun p : (Fin m → Z) × Z => f (A m p.1) p.2) := hA m
  have hRi : Integrable (fun S : Fin m → Z => risk f D (A m S)) (Measure.pi fun _ : Fin m => D) :=
    integrable_of_abs_le' (measurable_risk_rule hA D m) C fun S => abs_risk_le hC D _
  have hEi : Integrable (fun S : Fin m → Z => empRisk f S (A m S))
      (Measure.pi fun _ : Fin m => D) :=
    integrable_of_abs_le' (measurable_empRisk_rule hA m) C fun S => abs_empRisk_le hC hm S _
  have hWi : Integrable (fun p : (Fin m → Z) × Z => f (A m p.1) p.2)
      ((Measure.pi fun _ : Fin m => D).prod D) :=
    integrable_of_abs_le' hW C fun p => hC _ _
  have hG : ∀ i : Fin m,
      Measurable (fun p : (Fin m → Z) × Z => f (A m (Function.update p.1 i p.2)) p.2) :=
    fun i => hW.comp (measurable_update'.prodMk measurable_snd)
  have hGi : ∀ i : Fin m,
      Integrable (fun p : (Fin m → Z) × Z => f (A m (Function.update p.1 i p.2)) p.2)
        ((Measure.pi fun _ : Fin m => D).prod D) :=
    fun i => integrable_of_abs_le' (hG i) C fun p => hC _ _
  have hF : ∀ i : Fin m, Measurable (fun S : Fin m → Z => f (A m S) (S i)) :=
    fun i => hW.comp (measurable_id.prodMk (measurable_pi_apply i))
  have hFi : ∀ i : Fin m,
      Integrable (fun S : Fin m → Z => f (A m S) (S i)) (Measure.pi fun _ : Fin m => D) :=
    fun i => integrable_of_abs_le' (hF i) C fun S => hC _ _
  have hswap : ∀ i : Fin m,
      ∫ p, f (A m (Function.update p.1 i p.2)) p.2 ∂((Measure.pi fun _ : Fin m => D).prod D)
        = ∫ S, f (A m S) (S i) ∂(Measure.pi fun _ : Fin m => D) := by
    intro i
    have hmp := swap_mp D i
    have hF' : Measurable (fun p : (Fin m → Z) × Z => f (A m p.1) (p.1 i)) :=
      (hF i).comp measurable_fst
    have h := integral_map (μ := (Measure.pi fun _ : Fin m => D).prod D)
      hmp.measurable.aemeasurable (f := fun p : (Fin m → Z) × Z => f (A m p.1) (p.1 i))
      (by rw [hmp.map_eq]; exact hF'.aestronglyMeasurable)
    rw [hmp.map_eq] at h
    have h2 : ∫ p, f (A m p.1) (p.1 i) ∂((Measure.pi fun _ : Fin m => D).prod D)
        = ∫ S, f (A m S) (S i) ∂(Measure.pi fun _ : Fin m => D) := by
      have := integral_fun_fst (μ := Measure.pi fun _ : Fin m => D) (ν := D)
        (fun S : Fin m → Z => f (A m S) (S i))
      simpa using this
    rw [← h2, h]
    congr 1
    funext p
    simp
  have hRQ : ∫ p, f (A m p.1) p.2 ∂((Measure.pi fun _ : Fin m => D).prod D)
      = ∫ S, risk f D (A m S) ∂(Measure.pi fun _ : Fin m => D) := by
    rw [integral_prod _ hWi]
    rfl
  have hsumP : ∫ S, ∑ i, f (A m S) (S i) ∂(Measure.pi fun _ : Fin m => D)
      = ∑ i, ∫ S, f (A m S) (S i) ∂(Measure.pi fun _ : Fin m => D) :=
    integral_finsetSum _ fun i _ => hFi i
  have hEP : ∫ S, empRisk f S (A m S) ∂(Measure.pi fun _ : Fin m => D)
      = (∑ i, ∫ S, f (A m S) (S i) ∂(Measure.pi fun _ : Fin m => D)) / m := by
    unfold empRisk
    rw [integral_div, hsumP]
  rw [integral_sub hRi hEi, Finset.sum_congr rfl fun i _ => integral_sub (hGi i) hWi,
    Finset.sum_sub_distrib, Finset.sum_congr rfl fun i _ => hswap i, hRQ, hEP,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

lemma avg_term_eq {f : H → Z → ℝ} {A : (m : ℕ) → (Fin m → Z) → H} (hA : IsMeasurableRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] {m : ℕ} (i : Fin m) :
    ∫ p, (f (A m (Function.update p.1 i (p.2 i))) (p.2 i) - f (A m p.1) (p.2 i))
        ∂((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin m => D)) =
      ∫ q, (f (A m (Function.update q.1 i q.2)) q.2 - f (A m q.1) q.2)
        ∂((Measure.pi fun _ : Fin m => D).prod D) := by
  have hΦ : MeasurePreserving (Prod.map (id : (Fin m → Z) → (Fin m → Z)) (Function.eval i))
      ((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin m => D))
      ((Measure.pi fun _ : Fin m => D).prod D) :=
    (MeasurePreserving.id _).prod (measurePreserving_eval (fun _ : Fin m => D) i)
  have hg : Measurable (fun q : (Fin m → Z) × Z =>
      f (A m (Function.update q.1 i q.2)) q.2 - f (A m q.1) q.2) :=
    ((hA m).comp (measurable_update'.prodMk measurable_snd)).sub (hA m)
  rw [← hΦ.map_eq, integral_map hΦ.measurable.aemeasurable
    (by rw [hΦ.map_eq]; exact hg.aestronglyMeasurable)]
  rfl

lemma ex_le {f : H → Z → ℝ} {C : ℝ} (hC : ∀ h z, |f h z| ≤ C)
    {A : (m : ℕ) → (Fin m → Z) → H} (hA : IsMeasurableRule f A)
    (D : Measure Z) [IsProbabilityMeasure D] (εstable : ℕ → ℝ)
    (hstable : AverageROStableUnder f A D εstable ∨ UniformROStable f A εstable)
    {m : ℕ} (hm : 1 ≤ m) :
    ∫ S, (risk f D (A m S) - empRisk f S (A m S)) ∂(Measure.pi fun _ : Fin m => D)
      ≤ εstable m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [gen_eq hC hA D hm]
  rcases hstable with hs | hs
  · have h := hs m hm
    unfold sampleLaw at h
    rw [Finset.sum_congr rfl fun i _ => avg_term_eq hA D i] at h
    rw [neg_div]
    exact (neg_le_abs _).trans h
  · have hgi : ∀ i : Fin m, Integrable (fun q : (Fin m → Z) × Z =>
        f (A m (Function.update q.1 i q.2)) q.2 - f (A m q.1) q.2)
        ((Measure.pi fun _ : Fin m => D).prod D) := fun i =>
      integrable_of_abs_le' (((hA m).comp (measurable_update'.prodMk measurable_snd)).sub (hA m))
        (C + C) fun q => (abs_sub _ _).trans (add_le_add (hC _ _) (hC _ _))
    rw [← integral_finsetSum _ fun i _ => hgi i, ← integral_neg, ← integral_div]
    have hI : Integrable (fun q : (Fin m → Z) × Z =>
        -(∑ i : Fin m, (f (A m (Function.update q.1 i q.2)) q.2 - f (A m q.1) q.2)) / m)
        ((Measure.pi fun _ : Fin m => D).prod D) :=
      (integrable_finsetSum _ fun i _ => hgi i).neg.div_const _
    have hle := integral_mono hI (integrable_const (εstable m)) (fun q => by
      have hq := hs m hm q.1 (fun _ => q.2) q.2
      show -(∑ i : Fin m, (f (A m (Function.update q.1 i q.2)) q.2 - f (A m q.1) q.2)) / m
        ≤ εstable m
      refine le_trans ?_ hq
      apply div_le_div_of_nonneg_right _ hm'.le
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun i _ => neg_le_abs _)
    simpa using hle

end Main

end Pd5d217db

open MeasureTheory LearnStability.ConvexSCO in
theorem solution {Z H : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (C : ℝ) (hC : ∀ h z, |f h z| ≤ C) (hf : ∀ h, Measurable (f h))
    (herm : ErmValueMeasurable f) (A : (m : ℕ) → (Fin m → Z) → H)
    (hA : IsMeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D]
    (εerm εstable : ℕ → ℝ) (haerm : IsAERMUnder f A D εerm)
    (hstable : AverageROStableUnder f A D εstable ∨ UniformROStable f A εstable) :
    IsConsistentUnder f A D (fun m => εstable m + εerm m) ∧
      GeneralizesUnder f A D
        (fun m => εstable m + 2 * εerm m + 2 * C / Real.sqrt m) := by
  open Pd5d217db in
  have hRi : ∀ m, Integrable (fun S : Fin m → Z => risk f D (A m S))
      (Measure.pi fun _ : Fin m => D) := fun m =>
    integrable_of_abs_le' (measurable_risk_rule hA D m) C fun S => abs_risk_le hC D _
  open Pd5d217db in
  have hEi : ∀ m, 1 ≤ m → Integrable (fun S : Fin m → Z => empRisk f S (A m S))
      (Measure.pi fun _ : Fin m => D) := fun m hm =>
    integrable_of_abs_le' (measurable_empRisk_rule hA m) C fun S => abs_empRisk_le hC hm S _
  open Pd5d217db in
  have hVi : ∀ m, 1 ≤ m → Integrable (fun S : Fin m → Z => ermValue f S)
      (Measure.pi fun _ : Fin m => D) := fun m hm =>
    integrable_of_abs_le' (herm m) C fun S => abs_ermValue_le hC hm S
  have hu : ∀ m : ℕ, (Measure.pi fun _ : Fin m => D).real Set.univ = 1 := fun m => by simp
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · -- consistency
    unfold sampleLaw
    have hX := Pd5d217db.ex_le hC hA D εstable hstable hm
    have hG := haerm m hm
    unfold sampleLaw at hG
    rw [integral_sub (hEi m hm) (hVi m hm)] at hG
    rw [integral_sub (hRi m) (hEi m hm)] at hX
    have hV : ∫ S, ermValue f S ∂(Measure.pi fun _ : Fin m => D) ≤ optRisk f D := by
      refine le_ciInf fun h => ?_
      rw [← Pd5d217db.integral_empRisk hC hf D hm h]
      exact integral_mono (hVi m hm)
        (Pd5d217db.integrable_of_abs_le' (Pd5d217db.measurable_empRisk_const hf m h) C
          fun S => Pd5d217db.abs_empRisk_le hC hm S h)
        fun S => Pd5d217db.ermValue_le hC hm S h
    rw [integral_sub (hRi m) (integrable_const _), integral_const, hu, one_smul]
    linarith
  · -- generalization
    unfold sampleLaw
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    have hX := Pd5d217db.ex_le hC hA D εstable hstable hm
    have hG := haerm m hm
    unfold sampleLaw at hG
    have hXi : Integrable (fun S : Fin m → Z => risk f D (A m S) - empRisk f S (A m S))
        (Measure.pi fun _ : Fin m => D) := (hRi m).sub (hEi m hm)
    have hgapi : Integrable (fun S : Fin m → Z => empRisk f S (A m S) - ermValue f S)
        (Measure.pi fun _ : Fin m => D) := (hEi m hm).sub (hVi m hm)
    refine le_of_forall_pos_le_add fun η hη => ?_
    obtain ⟨h, hh⟩ : ∃ h, risk f D h < optRisk f D + η / 2 :=
      exists_lt_of_ciInf_lt (f := fun h => risk f D h) (a := optRisk f D + η / 2)
        (show optRisk f D < optRisk f D + η / 2 by linarith)
    have hpt : ∀ S : Fin m → Z, |risk f D (A m S) - empRisk f S (A m S)| ≤
        (risk f D (A m S) - empRisk f S (A m S)) +
          (2 * (empRisk f S (A m S) - ermValue f S) +
            2 * (|empRisk f S h - risk f D h| + η / 2)) := by
      intro S
      have l0 := Pd5d217db.ermValue_le hC hm S (A m S)
      have l1 := Pd5d217db.ermValue_le hC hm S h
      have l2 := Pd5d217db.opt_le_risk hC D (A m S)
      have l3 := le_abs_self (empRisk f S h - risk f D h)
      have l4 := abs_nonneg (empRisk f S h - risk f D h)
      rcases abs_cases (risk f D (A m S) - empRisk f S (A m S)) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        linarith
    have hWa : Integrable (fun S : Fin m → Z => |empRisk f S h - risk f D h|)
        (Measure.pi fun _ : Fin m => D) :=
      ((Pd5d217db.integrable_of_abs_le' (Pd5d217db.measurable_empRisk_const hf m h) C
        fun S => Pd5d217db.abs_empRisk_le hC hm S h).sub (integrable_const _)).abs
    have hW : Integrable (fun S : Fin m → Z => |empRisk f S h - risk f D h| + η / 2)
        (Measure.pi fun _ : Fin m => D) := hWa.add (integrable_const _)
    set μ := (Measure.pi fun _ : Fin m => D) with hμ
    have hint : ∫ S, |risk f D (A m S) - empRisk f S (A m S)| ∂μ ≤
        ∫ S, ((risk f D (A m S) - empRisk f S (A m S)) +
          (2 * (empRisk f S (A m S) - ermValue f S) +
            2 * (|empRisk f S h - risk f D h| + η / 2))) ∂μ :=
      integral_mono hXi.abs (hXi.add ((hgapi.const_mul 2).add (hW.const_mul 2))) hpt
    have s1 : ∫ S, ((risk f D (A m S) - empRisk f S (A m S)) +
          (2 * (empRisk f S (A m S) - ermValue f S) +
            2 * (|empRisk f S h - risk f D h| + η / 2))) ∂μ =
        ∫ S, (risk f D (A m S) - empRisk f S (A m S)) ∂μ +
          ∫ S, (2 * (empRisk f S (A m S) - ermValue f S) +
            2 * (|empRisk f S h - risk f D h| + η / 2)) ∂μ :=
      integral_add hXi ((hgapi.const_mul 2).add (hW.const_mul 2))
    have s2 : ∫ S, (2 * (empRisk f S (A m S) - ermValue f S) +
            2 * (|empRisk f S h - risk f D h| + η / 2)) ∂μ =
        ∫ S, 2 * (empRisk f S (A m S) - ermValue f S) ∂μ +
          ∫ S, 2 * (|empRisk f S h - risk f D h| + η / 2) ∂μ :=
      integral_add (hgapi.const_mul 2) (hW.const_mul 2)
    have s3 : ∫ S, 2 * (empRisk f S (A m S) - ermValue f S) ∂μ =
        2 * ∫ S, (empRisk f S (A m S) - ermValue f S) ∂μ := integral_const_mul _ _
    have s4 : ∫ S, 2 * (|empRisk f S h - risk f D h| + η / 2) ∂μ =
        2 * ∫ S, (|empRisk f S h - risk f D h| + η / 2) ∂μ := integral_const_mul _ _
    have s5 : ∫ S, (|empRisk f S h - risk f D h| + η / 2) ∂μ =
        ∫ S, |empRisk f S h - risk f D h| ∂μ + ∫ _S, η / 2 ∂μ :=
      integral_add hWa (integrable_const _)
    have s6 : ∫ _S, η / 2 ∂μ = η / 2 := by rw [integral_const, hu, one_smul]
    rw [s1, s2, s3, s4, s5, s6] at hint
    show _ ≤ εstable m + 2 * εerm m + 2 * C / Real.sqrt m + η
    have hm2 := Pd5d217db.abs_moment hC hf D hm h
    have e : 2 * C / Real.sqrt m = 2 * (C / Real.sqrt m) := by ring
    rw [e]
    linarith
