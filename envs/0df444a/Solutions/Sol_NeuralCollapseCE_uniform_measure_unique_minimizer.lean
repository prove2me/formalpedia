-- Prove2me | solution 1 for NeuralCollapseCE.uniform_measure_unique_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T04:32:28.597471+00:00
-- url     : https://prove2.me/submissions/fd44ffe6-0ea4-43be-a8fd-1ce461f07bb1

import Mathlib
import Definitions.Def_NeuralCollapseCE_Basic

open MeasureTheory

noncomputable section

namespace NeuralCollapseCE
section GaussBlock

/-- The standard Gaussian measure on `Vec d` (product of `N(0,1)` coordinates). -/
def p4rho (d : ℕ) : Measure (Vec d) :=
  (Measure.pi (fun _ : Fin d => ProbabilityTheory.gaussianReal 0 1)).map
    (MeasurableEquiv.toLp 2 (Fin d → ℝ))

lemma p4g_eq_stdGaussian (d : ℕ) : p4rho d = ProbabilityTheory.stdGaussian (Vec d) := by
  rw [p4rho, MeasurableEquiv.coe_toLp]
  exact ProbabilityTheory.map_pi_eq_stdGaussian

theorem p4rho_prob (d : ℕ) : IsProbabilityMeasure (p4rho d) := by
  rw [p4g_eq_stdGaussian]; infer_instance

lemma p4g_map_inner (d : ℕ) (a : Vec d) :
    (p4rho d).map (fun z : Vec d => inner ℝ a z) = ProbabilityTheory.gaussianReal 0 (‖a‖ ^ 2).toNNReal := by
  rw [p4g_eq_stdGaussian]
  have h := ProbabilityTheory.IsGaussian.map_eq_gaussianReal
    (μ := ProbabilityTheory.stdGaussian (Vec d)) (innerSL ℝ a)
  rw [ProbabilityTheory.integral_strongDual_stdGaussian,
    ProbabilityTheory.variance_dual_stdGaussian, innerSL_apply_norm] at h
  convert h using 2
  funext z; simp [innerSL_apply_apply]

theorem p4rho_integrable_exp (d : ℕ) (a : Vec d) :
    Integrable (fun z : Vec d => Real.exp (inner ℝ a z)) (p4rho d) := by
  have hm : AEMeasurable (fun z : Vec d => inner ℝ a z) (p4rho d) := by fun_prop
  have h1 : Integrable (fun x : ℝ => Real.exp (1 * x)) ((p4rho d).map (fun z : Vec d => inner ℝ a z)) := by
    rw [p4g_map_inner]; exact ProbabilityTheory.integrable_exp_mul_gaussianReal 1
  simpa [Function.comp_def] using h1.comp_aemeasurable hm

theorem p4rho_integral_exp (d : ℕ) (a : Vec d) :
    ∫ z, Real.exp (inner ℝ a z) ∂(p4rho d) = Real.exp (‖a‖ ^ 2 / 2) := by
  have hm : AEMeasurable (fun z : Vec d => inner ℝ a z) (p4rho d) := by fun_prop
  have h := ProbabilityTheory.mgf_gaussianReal (p := p4rho d) (X := fun z : Vec d => inner ℝ a z)
    (μ := 0) (v := (‖a‖ ^ 2).toNNReal) (p4g_map_inner d a) 1
  rw [ProbabilityTheory.mgf] at h
  simp only [one_mul, zero_add, one_pow, mul_one] at h
  rw [h, Real.coe_toNNReal _ (by positivity)]

theorem p4rho_integrable_exp_norm (d : ℕ) (c : ℝ) :
    Integrable (fun z : Vec d => Real.exp (c * ‖z‖)) (p4rho d) := by
  rw [p4g_eq_stdGaussian]
  obtain ⟨C, hC, hint⟩ := ProbabilityTheory.IsGaussian.exists_integrable_exp_sq
    (ProbabilityTheory.stdGaussian (Vec d))
  refine (hint.const_mul (Real.exp (c ^ 2 / (4 * C)))).mono' (by fun_prop) ?_
  refine Filter.Eventually.of_forall fun z => ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h2 : 0 ≤ (2 * C * ‖z‖ - c) ^ 2 / (4 * C) := by positivity
  have h3 : c ^ 2 / (4 * C) + C * ‖z‖ ^ 2 - c * ‖z‖ = (2 * C * ‖z‖ - c) ^ 2 / (4 * C) := by
    field_simp; ring
  linarith

end GaussBlock
end NeuralCollapseCE

namespace NeuralCollapseCE
section SphereBlock

open Set Metric Submodule
open scoped Pointwise

/-- The rotation `R` restricted to the unit sphere. -/
def p4s_rot {d : ℕ} (R : Vec d ≃ₗᵢ[ℝ] Vec d) (y : Sph d) : Sph d :=
  ⟨R y, by simp [norm_eq_of_mem_sphere y]⟩

lemma p4s_rot_coe {d : ℕ} (R : Vec d ≃ₗᵢ[ℝ] Vec d) (y : Sph d) :
    ((p4s_rot R y : Sph d) : Vec d) = R y := rfl

lemma p4s_rot_continuous {d : ℕ} (R : Vec d ≃ₗᵢ[ℝ] Vec d) : Continuous (p4s_rot R) :=
  (R.continuous.comp continuous_subtype_val).subtype_mk _

lemma p4s_rot_measurable {d : ℕ} (R : Vec d ≃ₗᵢ[ℝ] Vec d) : Measurable (p4s_rot R) :=
  (p4s_rot_continuous R).measurable

lemma p4s_set_eq {d : ℕ} (R : Vec d ≃ₗᵢ[ℝ] Vec d) (s : Set (Sph d)) :
    Ioo (0 : ℝ) 1 • (((↑) : Sph d → Vec d) '' (p4s_rot R ⁻¹' s)) =
      R ⁻¹' (Ioo (0 : ℝ) 1 • (((↑) : Sph d → Vec d) '' s)) := by
  ext z
  simp only [Set.mem_smul, Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨r, hr, w, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨r, hr, R y, ⟨p4s_rot R y, hy, rfl⟩, by simp⟩
  · rintro ⟨r, hr, w, ⟨y, hy, rfl⟩, hz⟩
    refine ⟨r, hr, R.symm y, ⟨⟨R.symm y, ?_⟩, ?_, rfl⟩, ?_⟩
    · simp [norm_eq_of_mem_sphere y]
    · have : p4s_rot R ⟨R.symm y, by
          simp [norm_eq_of_mem_sphere y]⟩ = y := by
        apply Subtype.ext; simp [p4s_rot_coe]
      rw [this]; exact hy
    · have := congrArg R.symm hz
      simpa [map_smul] using this

lemma p4s_map_toSphere {d : ℕ} (R : Vec d ≃ₗᵢ[ℝ] Vec d) :
    ((volume : Measure (Vec d)).toSphere).map (p4s_rot R) = (volume : Measure (Vec d)).toSphere := by
  ext s hs
  rw [Measure.map_apply (p4s_rot_measurable R) hs,
    Measure.toSphere_apply' _ ((p4s_rot_measurable R) hs), Measure.toSphere_apply' _ hs,
    p4s_set_eq]
  congr 1
  have h := R.measurePreserving
  have h2 : MeasurePreserving R.toMeasurableEquiv volume volume := h
  exact h2.measure_preimage_equiv _

lemma p4s_map_uniform {d : ℕ} (R : Vec d ≃ₗᵢ[ℝ] Vec d) :
    (uniformSphere d).map (p4s_rot R) = uniformSphere d := by
  rw [uniformSphere, Measure.map_smul, p4s_map_toSphere]

theorem p4_sphere_prob {d : ℕ} (hd : 1 ≤ d) : IsProbabilityMeasure (uniformSphere d) := by
  have : Nontrivial (Vec d) := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  constructor
  rw [uniformSphere, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel
  · rw [Ne, Measure.measure_univ_eq_zero]
    exact Measure.toSphere_ne_zero _
  · exact measure_ne_top _ _

theorem p4_sphere_invariant {d : ℕ} (hd : 1 ≤ d) (f : ℝ → ℝ) (hf : Continuous f)
    (x x' : Sph d) :
    ∫ y, f (inner ℝ (x : Vec d) (y : Vec d)) ∂(uniformSphere d) =
      ∫ y, f (inner ℝ (x' : Vec d) (y : Vec d)) ∂(uniformSphere d) := by
  set R : Vec d ≃ₗᵢ[ℝ] Vec d := reflection (ℝ ∙ ((x : Vec d) - x'))ᗮ
  have hRx : R x = x' := reflection_sub (by
    rw [norm_eq_of_mem_sphere x, norm_eq_of_mem_sphere x'])
  have hg : ∀ y : Sph d, f (inner ℝ (x' : Vec d) (y : Vec d)) =
      (fun z : Sph d => f (inner ℝ (x : Vec d) (z : Vec d))) (p4s_rot R y) := by
    intro y
    simp only [p4s_rot_coe]
    rw [← hRx]
    congr 1
    conv_lhs => rw [← reflection_reflection (ℝ ∙ ((x : Vec d) - x'))ᗮ (y : Vec d)]
    exact R.inner_map_map _ _
  have hmp : MeasurePreserving (p4s_rot R) (uniformSphere d) (uniformSphere d) :=
    ⟨p4s_rot_measurable R, p4s_map_uniform R⟩
  simp_rw [hg]
  have h := integral_map (μ := uniformSphere d) (p4s_rot_measurable R).aemeasurable
    (f := fun z : Sph d => f (inner ℝ (x : Vec d) (z : Vec d)))
    (hf.comp (continuous_const.inner continuous_subtype_val)).aestronglyMeasurable
  rw [hmp.map_eq] at h
  exact h

end SphereBlock
end NeuralCollapseCE

namespace NeuralCollapseCE
section ExtBlock

/-- The exponential `x ↦ exp ⟪x, w⟫` as a continuous function on the sphere. -/
def p4e_exp {d : ℕ} (w : Vec d) : C(Sph d, ℝ) :=
  ⟨fun x => Real.exp (inner ℝ (x : Vec d) w), by fun_prop⟩

lemma p4e_exp_apply {d : ℕ} (w : Vec d) (x : Sph d) :
    p4e_exp w x = Real.exp (inner ℝ (x : Vec d) w) := rfl

/-- The set of exponentials is a submonoid. -/
lemma p4e_closure_subset {d : ℕ} :
    (Submonoid.closure (Set.range (p4e_exp (d := d))) : Set C(Sph d, ℝ)) ⊆
      Set.range (p4e_exp (d := d)) := by
  intro f hf
  induction hf using Submonoid.closure_induction with
  | mem x hx => exact hx
  | one =>
    refine ⟨0, ?_⟩
    ext x
    simp [p4e_exp_apply]
  | mul x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    refine ⟨a + b, ?_⟩
    ext x
    simp [p4e_exp_apply, inner_add_right, Real.exp_add]

lemma p4e_integrable {d : ℕ} (μ : Measure (Sph d)) [IsFiniteMeasure μ] (f : C(Sph d, ℝ)) :
    Integrable (fun x => f x) μ := by
  exact (BoundedContinuousFunction.mkOfCompact f).integrable μ

lemma p4e_integral_eq_adjoin {d : ℕ} (μ ν : Measure (Sph d)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ w : Vec d, ∫ x, Real.exp (inner ℝ (x : Vec d) w) ∂μ =
      ∫ x, Real.exp (inner ℝ (x : Vec d) w) ∂ν)
    (g : C(Sph d, ℝ)) (hg : g ∈ Algebra.adjoin ℝ (Set.range (p4e_exp (d := d)))) :
    ∫ x, g x ∂μ = ∫ x, g x ∂ν := by
  have hg' : g ∈ Subalgebra.toSubmodule (Algebra.adjoin ℝ (Set.range (p4e_exp (d := d)))) := hg
  clear hg
  rw [Algebra.adjoin_eq_span] at hg'
  induction hg' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := p4e_closure_subset hx
    exact h w
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [ContinuousMap.add_apply]
    rw [integral_add (p4e_integrable μ x) (p4e_integrable μ y),
      integral_add (p4e_integrable ν x) (p4e_integrable ν y), hx, hy]
  | smul a x _ hx =>
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    rw [integral_const_mul, integral_const_mul, hx]

lemma p4e_separates {d : ℕ} :
    (Algebra.adjoin ℝ (Set.range (p4e_exp (d := d)))).SeparatesPoints := by
  intro x y hxy
  refine ⟨_, ⟨p4e_exp ((x : Vec d) - y), Algebra.subset_adjoin ⟨_, rfl⟩, rfl⟩, ?_⟩
  simp only [p4e_exp_apply]
  intro heq
  have h1 := Real.exp_injective heq
  have h2 : inner ℝ ((x : Vec d) - y) ((x : Vec d) - y) = 0 := by
    rw [inner_sub_left, h1, sub_self]
  rw [inner_self_eq_zero, sub_eq_zero] at h2
  exact hxy (Subtype.ext h2)

theorem p4_mgf_ext {d : ℕ} (μ ν : Measure (Sph d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ w : Vec d, ∫ x, Real.exp (inner ℝ (x : Vec d) w) ∂μ =
      ∫ x, Real.exp (inner ℝ (x : Vec d) w) ∂ν) : μ = ν := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  set A := Algebra.adjoin ℝ (Set.range (p4e_exp (d := d)))
  set C : ℝ := μ.real Set.univ + ν.real Set.univ + 1
  have hC : 0 < C := by positivity
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints A
    p4e_separates f f.continuous (ε / C) (div_pos hε hC)
  have hgA := p4e_integral_eq_adjoin μ ν h g g.2
  have hfi : ∀ m : Measure (Sph d), IsFiniteMeasure m → Integrable (fun x => f x) m :=
    fun m _ => f.integrable m
  have hbound : ∀ m : Measure (Sph d), IsFiniteMeasure m →
      ‖∫ x, f x ∂m - ∫ x, (g : C(Sph d, ℝ)) x ∂m‖ ≤ ε / C * m.real Set.univ := by
    intro m _
    rw [← integral_sub (hfi m inferInstance) (p4e_integrable m g)]
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_sub_rev]
    exact (hg x).le
  have h1 := hbound μ inferInstance
  have h2 := hbound ν inferInstance
  rw [hgA] at h1
  rw [Real.dist_eq]
  calc |∫ x, f x ∂μ - ∫ x, f x ∂ν|
      = ‖(∫ x, f x ∂μ - ∫ x, (g : C(Sph d, ℝ)) x ∂ν) -
          (∫ x, f x ∂ν - ∫ x, (g : C(Sph d, ℝ)) x ∂ν)‖ := by
        rw [Real.norm_eq_abs]; ring_nf
    _ ≤ ε / C * μ.real Set.univ + ε / C * ν.real Set.univ := (norm_sub_le _ _).trans
        (add_le_add h1 h2)
    _ = ε * ((μ.real Set.univ + ν.real Set.univ) / C) := by ring
    _ ≤ ε * 1 := by
        gcongr
        rw [div_le_one hC]; linarith
    _ = ε := mul_one ε

end ExtBlock
end NeuralCollapseCE

namespace NeuralCollapseCE
/-! ## Proof of Proposition 4 -/

section P4Main

variable {d : ℕ}

def p4m_phi (β : ℝ) (x : Sph d) (z : Vec d) : ℝ := Real.exp (β * inner ℝ (x : Vec d) z)

def p4m_G (β : ℝ) (μ : Measure (Sph d)) (z : Vec d) : ℝ := ∫ x, p4m_phi β x z ∂μ

def p4m_K (α : ℝ) (μ : Measure (Sph d)) (x : Sph d) : ℝ :=
  ∫ y, Real.exp (α * (inner ℝ (x : Vec d) (y : Vec d) - 1)) ∂μ

lemma p4m_norm (x : Sph d) : ‖(x : Vec d)‖ = 1 := norm_eq_of_mem_sphere x

lemma p4m_inner_le (x : Sph d) (z : Vec d) : |inner ℝ (x : Vec d) z| ≤ ‖z‖ := by
  have := abs_real_inner_le_norm (x : Vec d) z
  rwa [p4m_norm, one_mul] at this

lemma p4m_phi_cont (β : ℝ) : Continuous (Function.uncurry (p4m_phi (d := d) β)) := by
  unfold p4m_phi
  change Continuous (fun p : Sph d × Vec d => Real.exp (β * inner ℝ (p.1 : Vec d) p.2))
  fun_prop

lemma p4m_phi_le {β : ℝ} (hβ : 0 ≤ β) (x : Sph d) (z : Vec d) :
    p4m_phi β x z ≤ Real.exp (β * ‖z‖) := by
  unfold p4m_phi
  have h := (abs_le.mp (p4m_inner_le x z)).2
  gcongr

lemma p4m_phi_ge {β : ℝ} (hβ : 0 ≤ β) (x : Sph d) (z : Vec d) :
    Real.exp (-(β * ‖z‖)) ≤ p4m_phi β x z := by
  unfold p4m_phi
  have h := (abs_le.mp (p4m_inner_le x z)).1
  gcongr
  nlinarith

lemma p4m_int_x (μ : Measure (Sph d)) [IsFiniteMeasure μ] {f : Sph d → ℝ} (hf : Continuous f) :
    Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

lemma p4m_int_z {f : Vec d → ℝ} (hf : Continuous f) (C c : ℝ)
    (hb : ∀ z, |f z| ≤ C * Real.exp (c * ‖z‖)) : Integrable f (p4rho d) := by
  refine Integrable.mono' ((p4rho_integrable_exp_norm d c).const_mul C)
    hf.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  simpa [Real.norm_eq_abs] using hb z

lemma p4m_int_prod (μ : Measure (Sph d)) [IsFiniteMeasure μ] {F : Sph d → Vec d → ℝ}
    (hF : Continuous (Function.uncurry F)) (C c : ℝ)
    (hb : ∀ x z, |F x z| ≤ C * Real.exp (c * ‖z‖)) :
    Integrable (Function.uncurry F) (μ.prod (p4rho d)) := by
  have := p4rho_prob d
  refine Integrable.mono' (((p4rho_integrable_exp_norm d c).const_mul C).comp_snd μ)
    hF.aestronglyMeasurable (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs]; exact hb p.1 p.2

lemma p4m_swap (μ : Measure (Sph d)) [IsFiniteMeasure μ] {F : Sph d → Vec d → ℝ}
    (hF : Continuous (Function.uncurry F)) (C c : ℝ)
    (hb : ∀ x z, |F x z| ≤ C * Real.exp (c * ‖z‖)) :
    ∫ x, ∫ z, F x z ∂(p4rho d) ∂μ = ∫ z, ∫ x, F x z ∂μ ∂(p4rho d) := by
  have := p4rho_prob d
  exact integral_integral_swap (p4m_int_prod μ hF C c hb)

lemma p4m_int_inner (μ : Measure (Sph d)) [IsFiniteMeasure μ] {F : Sph d → Vec d → ℝ}
    (hF : Continuous (Function.uncurry F)) (C c : ℝ)
    (hb : ∀ x z, |F x z| ≤ C * Real.exp (c * ‖z‖)) :
    Integrable (fun x => ∫ z, F x z ∂(p4rho d)) μ := by
  have := p4rho_prob d
  exact (p4m_int_prod μ hF C c hb).integral_prod_left

lemma p4m_phi_pos (β : ℝ) (x : Sph d) (z : Vec d) : 0 < p4m_phi β x z := Real.exp_pos _

lemma p4m_phi_cont_x (β : ℝ) (z : Vec d) : Continuous (fun x : Sph d => p4m_phi β x z) := by
  unfold p4m_phi; fun_prop

lemma p4m_feat {α β : ℝ} (hβ : β ^ 2 = α) (x y : Sph d) :
    ∫ z, p4m_phi β x z * p4m_phi β y z ∂(p4rho d) =
      Real.exp (2 * α) * Real.exp (α * (inner ℝ (x : Vec d) (y : Vec d) - 1)) := by
  have h1 : ∀ z, p4m_phi β x z * p4m_phi β y z =
      Real.exp (inner ℝ (β • ((x : Vec d) + y)) z) := by
    intro z; unfold p4m_phi
    rw [← Real.exp_add, real_inner_smul_left, inner_add_left]; ring_nf
  simp_rw [h1, p4rho_integral_exp, ← Real.exp_add]
  congr 1
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_add_sq_real, p4m_norm, p4m_norm, hβ]
  ring

lemma p4m_G_cont (β : ℝ) (μ : Measure (Sph d)) [IsFiniteMeasure μ] :
    Continuous (p4m_G β μ) := by
  have h := continuous_parametric_integral_of_continuous (μ := μ)
    (f := fun (z : Vec d) (x : Sph d) => p4m_phi β x z) ?_ isCompact_univ
  · show Continuous (fun z => ∫ x, p4m_phi β x z ∂μ)
    simpa [Measure.restrict_univ] using h
  · exact (p4m_phi_cont β).comp continuous_swap

lemma p4m_K_cont (α : ℝ) (μ : Measure (Sph d)) [IsFiniteMeasure μ] :
    Continuous (p4m_K α μ) := by
  have h := continuous_parametric_integral_of_continuous (μ := μ)
    (f := fun (x y : Sph d) => Real.exp (α * (inner ℝ (x : Vec d) (y : Vec d) - 1)))
    ?_ isCompact_univ
  · show Continuous (fun x : Sph d => ∫ y, Real.exp (α * (inner ℝ (x : Vec d) (y : Vec d) - 1)) ∂μ)
    simpa [Measure.restrict_univ] using h
  · change Continuous (fun p : Sph d × Sph d =>
      Real.exp (α * (inner ℝ (p.1 : Vec d) (p.2 : Vec d) - 1)))
    fun_prop

lemma p4m_G_le {β : ℝ} (hβ : 0 ≤ β) (μ : Measure (Sph d)) [IsProbabilityMeasure μ]
    (z : Vec d) : p4m_G β μ z ≤ Real.exp (β * ‖z‖) := by
  have := integral_mono (p4m_int_x μ (p4m_phi_cont_x β z))
    (integrable_const (Real.exp (β * ‖z‖))) (fun x => p4m_phi_le hβ x z)
  simpa [p4m_G] using this

lemma p4m_G_ge {β : ℝ} (hβ : 0 ≤ β) (μ : Measure (Sph d)) [IsProbabilityMeasure μ]
    (z : Vec d) : Real.exp (-(β * ‖z‖)) ≤ p4m_G β μ z := by
  have := integral_mono (integrable_const (Real.exp (-(β * ‖z‖))))
    (p4m_int_x μ (p4m_phi_cont_x β z)) (fun x => p4m_phi_ge hβ x z)
  simpa [p4m_G] using this

lemma p4m_G_pos {β : ℝ} (hβ : 0 ≤ β) (μ : Measure (Sph d)) [IsProbabilityMeasure μ]
    (z : Vec d) : 0 < p4m_G β μ z := (Real.exp_pos _).trans_le (p4m_G_ge hβ μ z)

lemma p4m_logG_abs {β : ℝ} (hβ : 0 ≤ β) (μ : Measure (Sph d)) [IsProbabilityMeasure μ]
    (z : Vec d) : |Real.log (p4m_G β μ z)| ≤ β * ‖z‖ := by
  have hpos := p4m_G_pos hβ μ z
  rw [abs_le]; constructor
  · rw [Real.le_log_iff_exp_le hpos]; exact p4m_G_ge hβ μ z
  · rw [Real.log_le_iff_le_exp hpos]; exact p4m_G_le hβ μ z

lemma p4m_K_ge {α : ℝ} (hα : 0 ≤ α) (μ : Measure (Sph d)) [IsProbabilityMeasure μ]
    (x : Sph d) : Real.exp (-(2 * α)) ≤ p4m_K α μ x := by
  have hc : Continuous (fun y : Sph d => Real.exp (α * (inner ℝ (x : Vec d) (y : Vec d) - 1))) := by
    fun_prop
  have := integral_mono (integrable_const (Real.exp (-(2 * α)))) (p4m_int_x μ hc) (fun y => by
    have h := (abs_le.mp (p4m_inner_le x (y : Vec d))).1
    rw [p4m_norm] at h
    show Real.exp (-(2 * α)) ≤ Real.exp (α * (inner ℝ (x : Vec d) (y : Vec d) - 1))
    gcongr; nlinarith)
  simpa [p4m_K] using this

lemma p4m_K_pos {α : ℝ} (hα : 0 ≤ α) (μ : Measure (Sph d)) [IsProbabilityMeasure μ]
    (x : Sph d) : 0 < p4m_K α μ x := (Real.exp_pos _).trans_le (p4m_K_ge hα μ x)

lemma p4m_F1 {α β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ^ 2 = α) (μ : Measure (Sph d))
    [IsProbabilityMeasure μ] (x : Sph d) :
    ∫ z, p4m_phi β x z * p4m_G β μ z ∂(p4rho d) = Real.exp (2 * α) * p4m_K α μ x := by
  have h1 : ∀ z, p4m_phi β x z * p4m_G β μ z = ∫ y, p4m_phi β x z * p4m_phi β y z ∂μ :=
    fun z => (integral_const_mul _ _).symm
  simp_rw [h1]
  rw [show (∫ z, ∫ y, p4m_phi β x z * p4m_phi β y z ∂μ ∂(p4rho d)) =
      ∫ y, ∫ z, p4m_phi β x z * p4m_phi β y z ∂(p4rho d) ∂μ from
    (p4m_swap μ (F := fun y z => p4m_phi β x z * p4m_phi β y z) ?_ 1 (2 * β) ?_).symm]
  · simp_rw [p4m_feat hβ x]
    rw [integral_const_mul]; rfl
  · change Continuous (fun p : Sph d × Vec d => p4m_phi β x p.2 * p4m_phi β p.1 p.2)
    unfold p4m_phi; fun_prop
  · intro y z
    rw [abs_of_pos (mul_pos (p4m_phi_pos _ _ _) (p4m_phi_pos _ _ _)), one_mul,
      show 2 * β * ‖z‖ = β * ‖z‖ + β * ‖z‖ by ring, Real.exp_add]
    exact mul_le_mul (p4m_phi_le hβ0 x z) (p4m_phi_le hβ0 y z) (p4m_phi_pos _ _ _).le
      (Real.exp_pos _).le

lemma p4m_F2 {α β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ^ 2 = α) (μ ν : Measure (Sph d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (c : ℝ) (hc : ∀ x, p4m_K α ν x = c) :
    ∫ z, p4m_G β μ z * p4m_G β ν z ∂(p4rho d) = Real.exp (2 * α) * c := by
  have hQ := p4m_G_cont β ν
  have h1 : ∀ z, p4m_G β μ z * p4m_G β ν z = ∫ x, p4m_phi β x z * p4m_G β ν z ∂μ :=
    fun z => (integral_mul_const _ _).symm
  simp_rw [h1]
  rw [show (∫ z, ∫ x, p4m_phi β x z * p4m_G β ν z ∂μ ∂(p4rho d)) =
      ∫ x, ∫ z, p4m_phi β x z * p4m_G β ν z ∂(p4rho d) ∂μ from
    (p4m_swap μ (F := fun x z => p4m_phi β x z * p4m_G β ν z) ?_ 1 (2 * β) ?_).symm]
  · simp_rw [p4m_F1 hβ0 hβ ν, hc]
    simp
  · change Continuous (fun p : Sph d × Vec d => p4m_phi β p.1 p.2 * p4m_G β ν p.2)
    have := p4m_phi_cont (d := d) β
    exact this.mul (hQ.comp continuous_snd)
  · intro x z
    rw [abs_of_pos (mul_pos (p4m_phi_pos _ _ _) (p4m_G_pos hβ0 ν z)), one_mul,
      show 2 * β * ‖z‖ = β * ‖z‖ + β * ‖z‖ by ring, Real.exp_add]
    exact mul_le_mul (p4m_phi_le hβ0 x z) (p4m_G_le hβ0 ν z) (p4m_G_pos hβ0 ν z).le
      (Real.exp_pos _).le

lemma p4m_phi_abs {β : ℝ} (hβ : 0 ≤ β) (x : Sph d) (z : Vec d) :
    |p4m_phi β x z| ≤ Real.exp (β * ‖z‖) := by
  rw [abs_of_pos (p4m_phi_pos β x z)]; exact p4m_phi_le hβ x z

lemma p4m_G_abs {β : ℝ} (hβ : 0 ≤ β) (μ : Measure (Sph d)) [IsProbabilityMeasure μ]
    (z : Vec d) : |p4m_G β μ z| ≤ Real.exp (β * ‖z‖) := by
  rw [abs_of_pos (p4m_G_pos hβ μ z)]; exact p4m_G_le hβ μ z

lemma p4m_mul_bd {u v β C c t : ℝ} (hu : |u| ≤ Real.exp (β * t))
    (hv : |v| ≤ C * Real.exp (c * t)) : |u * v| ≤ C * Real.exp ((β + c) * t) := by
  rw [abs_mul, add_mul, Real.exp_add]
  calc |u| * |v| ≤ Real.exp (β * t) * (C * Real.exp (c * t)) :=
        mul_le_mul hu hv (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

lemma p4m_const {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 ≤ α) :
    ∃ c, 0 < c ∧ ∀ x, p4m_K α (uniformSphere d) x = c := by
  have hσ := p4_sphere_prob hd
  refine ⟨∫ x, p4m_K α (uniformSphere d) x ∂(uniformSphere d), ?_, fun x => ?_⟩
  · have := integral_mono (integrable_const (Real.exp (-(2 * α))))
      (p4m_int_x (uniformSphere d) (p4m_K_cont α (uniformSphere d))) (p4m_K_ge hα (uniformSphere d))
    simp only [integral_const, probReal_univ, one_smul] at this
    exact (Real.exp_pos _).trans_le this
  · symm
    calc ∫ x', p4m_K α (uniformSphere d) x' ∂(uniformSphere d)
        = ∫ _x', p4m_K α (uniformSphere d) x ∂(uniformSphere d) :=
          integral_congr_ae (ae_of_all _ fun x' =>
            p4_sphere_invariant hd (fun t => Real.exp (α * (t - 1))) (by fun_prop) x' x)
      _ = p4m_K α (uniformSphere d) x := by simp

lemma p4m_energy_const {d : ℕ} (hd : 1 ≤ d) (α c : ℝ)
    (hc : ∀ x, p4m_K α (uniformSphere d) x = c) :
    measureEnergy α (uniformSphere d) = Real.log c := by
  have hσ := p4_sphere_prob hd
  show ∫ x, Real.log (p4m_K α (uniformSphere d) x) ∂(uniformSphere d) = _
  simp [hc]

def p4m_R (β : ℝ) (μ ν : Measure (Sph d)) (z : Vec d) : ℝ :=
  p4m_G β ν z * Real.log (p4m_G β μ z / p4m_G β ν z)

lemma p4m_R_cont {β : ℝ} (hβ0 : 0 ≤ β) (μ ν : Measure (Sph d)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : Continuous (p4m_R β μ ν) := by
  have hP := p4m_G_cont β μ
  have hQ := p4m_G_cont β ν
  have h : Continuous (fun z => p4m_G β μ z / p4m_G β ν z) :=
    hP.div hQ (fun z => (p4m_G_pos hβ0 ν z).ne')
  exact hQ.mul (h.log (fun z => (div_pos (p4m_G_pos hβ0 μ z) (p4m_G_pos hβ0 ν z)).ne'))

lemma p4m_R_abs {β : ℝ} (hβ0 : 0 ≤ β) (μ ν : Measure (Sph d)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (z : Vec d) :
    |p4m_R β μ ν z| ≤ 2 * β * Real.exp ((β + 1) * ‖z‖) := by
  unfold p4m_R
  have hP := p4m_G_pos hβ0 μ z
  have hQ := p4m_G_pos hβ0 ν z
  rw [abs_mul, abs_of_pos hQ, Real.log_div hP.ne' hQ.ne']
  obtain ⟨a1, a2⟩ := abs_le.mp (p4m_logG_abs hβ0 μ z)
  obtain ⟨b1, b2⟩ := abs_le.mp (p4m_logG_abs hβ0 ν z)
  have h3 : |Real.log (p4m_G β μ z) - Real.log (p4m_G β ν z)| ≤ 2 * β * ‖z‖ := by
    rw [abs_le]; constructor <;> linarith
  have h4 : ‖z‖ ≤ Real.exp ‖z‖ := by linarith [Real.add_one_le_exp ‖z‖]
  have h5 : 2 * β * ‖z‖ ≤ 2 * β * Real.exp ‖z‖ := mul_le_mul_of_nonneg_left h4 (by positivity)
  calc p4m_G β ν z * |Real.log (p4m_G β μ z) - Real.log (p4m_G β ν z)|
      ≤ Real.exp (β * ‖z‖) * (2 * β * Real.exp ‖z‖) :=
        mul_le_mul (p4m_G_le hβ0 ν z) (h3.trans h5) (abs_nonneg _) (Real.exp_pos _).le
    _ = 2 * β * Real.exp ((β + 1) * ‖z‖) := by
        rw [show (β + 1) * ‖z‖ = β * ‖z‖ + ‖z‖ by ring, Real.exp_add]; ring

lemma p4m_step4 {α β : ℝ} (hα : 0 ≤ α) (hβ0 : 0 ≤ β) (hβ : β ^ 2 = α)
    (μ ν : Measure (Sph d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : ℝ) (hcpos : 0 < c) (hc : ∀ x, p4m_K α ν x = c) (x : Sph d) :
    ∫ z, p4m_phi β x z * p4m_R β μ ν z ∂(p4rho d) ≤
      Real.exp (2 * α) * c * (Real.log (p4m_K α μ x) - Real.log c) := by
  have hK := p4m_K_pos hα μ x
  have hA : 0 < p4m_K α μ x / c := div_pos hK hcpos
  have hpt : ∀ z, p4m_phi β x z * p4m_R β μ ν z ≤
      p4m_phi β x z * p4m_G β ν z * (Real.log (p4m_K α μ x / c) - 1) +
        p4m_phi β x z * p4m_G β μ z * (p4m_K α μ x / c)⁻¹ := by
    intro z
    have hP := p4m_G_pos hβ0 μ z
    have hQ := p4m_G_pos hβ0 ν z
    have hφ := p4m_phi_pos β x z
    have key : Real.log (p4m_G β μ z / p4m_G β ν z) ≤
        Real.log (p4m_K α μ x / c) - 1 + p4m_G β μ z / p4m_G β ν z * (p4m_K α μ x / c)⁻¹ := by
      have h := Real.log_le_sub_one_of_pos
        (show 0 < p4m_G β μ z / p4m_G β ν z * (p4m_K α μ x / c)⁻¹ by positivity)
      rw [Real.log_mul (by positivity) (by positivity), Real.log_inv] at h
      linarith
    have h2 : p4m_phi β x z * (p4m_G β ν z * Real.log (p4m_G β μ z / p4m_G β ν z)) ≤
        p4m_phi β x z * (p4m_G β ν z * (Real.log (p4m_K α μ x / c) - 1 +
          p4m_G β μ z / p4m_G β ν z * (p4m_K α μ x / c)⁻¹)) := by gcongr
    calc p4m_phi β x z * p4m_R β μ ν z
        = p4m_phi β x z * (p4m_G β ν z * Real.log (p4m_G β μ z / p4m_G β ν z)) := rfl
      _ ≤ _ := h2
      _ = _ := by field_simp
  have hRc := p4m_R_cont hβ0 μ ν
  have hI1 : Integrable (fun z => p4m_phi β x z * p4m_R β μ ν z) (p4rho d) :=
    p4m_int_z ((p4m_phi_cont β).comp (Continuous.prodMk continuous_const continuous_id) |>.mul hRc)
      (2 * β) (β + (β + 1)) (fun z => p4m_mul_bd (p4m_phi_abs hβ0 x z) (p4m_R_abs hβ0 μ ν z))
  have hIG : ∀ (ν' : Measure (Sph d)) [IsProbabilityMeasure ν'],
      Integrable (fun z => p4m_phi β x z * p4m_G β ν' z) (p4rho d) := fun ν' _ =>
    p4m_int_z ((p4m_phi_cont β).comp (Continuous.prodMk continuous_const continuous_id) |>.mul
      (p4m_G_cont β ν')) 1 (β + β)
      (fun z => p4m_mul_bd (p4m_phi_abs hβ0 x z) (by rw [one_mul]; exact p4m_G_abs hβ0 ν' z))
  have hint := integral_mono hI1 (((hIG ν).mul_const _).add ((hIG μ).mul_const _)) hpt
  simp only [Pi.add_apply] at hint
  rw [integral_add ((hIG ν).mul_const _) ((hIG μ).mul_const _), integral_mul_const,
    integral_mul_const, p4m_F1 hβ0 hβ ν x, p4m_F1 hβ0 hβ μ x, hc x,
    Real.log_div hK.ne' hcpos.ne'] at hint
  have e : Real.exp (2 * α) * p4m_K α μ x * (p4m_K α μ x / c)⁻¹ = Real.exp (2 * α) * c := by
    field_simp
  rw [e] at hint
  linarith

lemma p4m_key {α β : ℝ} (hα : 0 ≤ α) (hβ0 : 0 ≤ β) (hβ : β ^ 2 = α)
    (μ ν : Measure (Sph d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : ℝ) (hcpos : 0 < c) (hc : ∀ x, p4m_K α ν x = c) :
    Real.log c + (Real.exp (2 * α) * c)⁻¹ * ∫ z, p4m_G β μ z * p4m_R β μ ν z ∂(p4rho d) ≤
      measureEnergy α μ := by
  have := p4rho_prob d
  have hE : 0 < Real.exp (2 * α) * c := by positivity
  have hRc := p4m_R_cont hβ0 μ ν
  have hFc : Continuous (Function.uncurry fun x z => p4m_phi β x z * p4m_R β μ ν z) :=
    (p4m_phi_cont β).mul (hRc.comp continuous_snd)
  have hFb : ∀ x z, |p4m_phi β x z * p4m_R β μ ν z| ≤
      (2 * β) * Real.exp ((β + (β + 1)) * ‖z‖) :=
    fun x z => p4m_mul_bd (p4m_phi_abs hβ0 x z) (p4m_R_abs hβ0 μ ν z)
  have hswap := p4m_swap μ hFc _ _ hFb
  have hinner := p4m_int_inner μ hFc _ _ hFb
  have hlogK : Integrable (fun x => Real.log (p4m_K α μ x)) μ :=
    p4m_int_x μ ((p4m_K_cont α μ).log (fun x => (p4m_K_pos hα μ x).ne'))
  have h1 : ∫ x, (Real.log c + (Real.exp (2 * α) * c)⁻¹ *
      ∫ z, p4m_phi β x z * p4m_R β μ ν z ∂(p4rho d)) ∂μ ≤
      ∫ x, Real.log (p4m_K α μ x) ∂μ :=
    integral_mono ((integrable_const _).add (hinner.const_mul _)) hlogK (fun x => by
      have h4 := p4m_step4 hα hβ0 hβ μ ν c hcpos hc x
      have h5 : (Real.exp (2 * α) * c)⁻¹ * ∫ z, p4m_phi β x z * p4m_R β μ ν z ∂(p4rho d) ≤
          Real.log (p4m_K α μ x) - Real.log c := by
        rw [inv_mul_le_iff₀ hE]; exact h4
      show _ ≤ _
      linarith)
  have h2 : ∫ z, ∫ x, p4m_phi β x z * p4m_R β μ ν z ∂μ ∂(p4rho d) =
      ∫ z, p4m_G β μ z * p4m_R β μ ν z ∂(p4rho d) :=
    integral_congr_ae (ae_of_all _ fun z => integral_mul_const _ _)
  calc Real.log c + (Real.exp (2 * α) * c)⁻¹ * ∫ z, p4m_G β μ z * p4m_R β μ ν z ∂(p4rho d)
      = ∫ x, (Real.log c + (Real.exp (2 * α) * c)⁻¹ *
          ∫ z, p4m_phi β x z * p4m_R β μ ν z ∂(p4rho d)) ∂μ := by
        rw [integral_add (integrable_const _) (hinner.const_mul _), integral_const_mul, hswap, h2]
        simp
    _ ≤ ∫ x, Real.log (p4m_K α μ x) ∂μ := h1
    _ = measureEnergy α μ := rfl

lemma p4m_gap_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ a * (b * Real.log (a / b)) - (a * b - b * b) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  have e : Real.log (a / b) = - Real.log (b / a) := by rw [← Real.log_inv, inv_div]
  have e2 : a * (b * Real.log (a / b)) - (a * b - b * b) =
      a * b * ((b / a - 1) - Real.log (b / a)) := by
    rw [e]; field_simp; ring
  rw [e2]; exact mul_nonneg (by positivity) (by linarith)

lemma p4m_gap_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h0 : a * (b * Real.log (a / b)) - (a * b - b * b) = 0) : a = b := by
  by_contra hne
  have hs : b / a ≠ 1 := by
    intro h; rw [div_eq_one_iff_eq ha.ne'] at h; exact hne h.symm
  have hl : Real.log (b / a) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (div_pos hb ha) hs
  have h := Real.add_one_lt_exp hl
  rw [Real.exp_log (div_pos hb ha)] at h
  have e : Real.log (a / b) = - Real.log (b / a) := by rw [← Real.log_inv, inv_div]
  have e2 : a * (b * Real.log (a / b)) - (a * b - b * b) =
      a * b * ((b / a - 1) - Real.log (b / a)) := by
    rw [e]; field_simp; ring
  rw [e2] at h0
  have : 0 < a * b * ((b / a - 1) - Real.log (b / a)) := mul_pos (by positivity) (by linarith)
  linarith

def p4m_D (β : ℝ) (μ ν : Measure (Sph d)) (z : Vec d) : ℝ :=
  p4m_G β μ z * p4m_R β μ ν z - (p4m_G β μ z * p4m_G β ν z - p4m_G β ν z * p4m_G β ν z)

lemma p4m_D_facts {α β : ℝ} (hα : 0 ≤ α) (hβ0 : 0 ≤ β) (hβ : β ^ 2 = α)
    (μ ν : Measure (Sph d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : ℝ) (hcpos : 0 < c) (hc : ∀ x, p4m_K α ν x = c) :
    Integrable (p4m_D β μ ν) (p4rho d) ∧ (∀ z, 0 ≤ p4m_D β μ ν z) ∧
    (∀ z, p4m_D β μ ν z = 0 → p4m_G β μ z = p4m_G β ν z) ∧
    Real.log c + (Real.exp (2 * α) * c)⁻¹ * ∫ z, p4m_D β μ ν z ∂(p4rho d) ≤
      measureEnergy α μ := by
  have hP := p4m_G_cont β μ
  have hQ := p4m_G_cont β ν
  have hR := p4m_R_cont hβ0 μ ν
  have hPR : Integrable (fun z => p4m_G β μ z * p4m_R β μ ν z) (p4rho d) :=
    p4m_int_z (hP.mul hR) (2 * β) (β + (β + 1))
      (fun z => p4m_mul_bd (p4m_G_abs hβ0 μ z) (p4m_R_abs hβ0 μ ν z))
  have hPQ : Integrable (fun z => p4m_G β μ z * p4m_G β ν z) (p4rho d) :=
    p4m_int_z (hP.mul hQ) 1 (β + β)
      (fun z => p4m_mul_bd (p4m_G_abs hβ0 μ z) (by rw [one_mul]; exact p4m_G_abs hβ0 ν z))
  have hQQ : Integrable (fun z => p4m_G β ν z * p4m_G β ν z) (p4rho d) :=
    p4m_int_z (hQ.mul hQ) 1 (β + β)
      (fun z => p4m_mul_bd (p4m_G_abs hβ0 ν z) (by rw [one_mul]; exact p4m_G_abs hβ0 ν z))
  have hDint : Integrable (p4m_D β μ ν) (p4rho d) := hPR.sub (hPQ.sub hQQ)
  have hDeq : ∫ z, p4m_D β μ ν z ∂(p4rho d) =
      ∫ z, p4m_G β μ z * p4m_R β μ ν z ∂(p4rho d) := by
    have e1 := integral_sub hPR (hPQ.sub hQQ)
    have e2 := integral_sub hPQ hQQ
    simp only [Pi.sub_apply] at e1
    rw [show (∫ z, p4m_D β μ ν z ∂(p4rho d)) = _ from e1, e2, p4m_F2 hβ0 hβ μ ν c hc,
      p4m_F2 hβ0 hβ ν ν c hc]
    ring
  refine ⟨hDint, fun z => p4m_gap_nonneg (p4m_G_pos hβ0 μ z) (p4m_G_pos hβ0 ν z),
    fun z hz => p4m_gap_eq (p4m_G_pos hβ0 μ z) (p4m_G_pos hβ0 ν z) hz, ?_⟩
  rw [hDeq]; exact p4m_key hα hβ0 hβ μ ν c hcpos hc

lemma p4m_mgf {α β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ^ 2 = α) (μ : Measure (Sph d))
    [IsProbabilityMeasure μ] (w : Vec d) :
    ∫ z, p4m_G β μ z * Real.exp (inner ℝ w z) ∂(p4rho d) =
      Real.exp ((α + ‖w‖ ^ 2) / 2) * ∫ x, Real.exp (β * inner ℝ (x : Vec d) w) ∂μ := by
  have h1 : ∀ z, p4m_G β μ z * Real.exp (inner ℝ w z) =
      ∫ x, p4m_phi β x z * Real.exp (inner ℝ w z) ∂μ :=
    fun z => (integral_mul_const _ _).symm
  simp_rw [h1]
  rw [show (∫ z, ∫ x, p4m_phi β x z * Real.exp (inner ℝ w z) ∂μ ∂(p4rho d)) =
      ∫ x, ∫ z, p4m_phi β x z * Real.exp (inner ℝ w z) ∂(p4rho d) ∂μ from
    (p4m_swap μ (F := fun x z => p4m_phi β x z * Real.exp (inner ℝ w z)) ?_ 1 (β + ‖w‖) ?_).symm]
  · rw [← integral_const_mul]
    congr 1; funext x
    have h2 : ∀ z, p4m_phi β x z * Real.exp (inner ℝ w z) =
        Real.exp (inner ℝ (β • (x : Vec d) + w) z) := by
      intro z; unfold p4m_phi; rw [← Real.exp_add, inner_add_left, real_inner_smul_left]
    simp_rw [h2, p4rho_integral_exp]
    rw [← Real.exp_add]; congr 1
    rw [norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, p4m_norm,
      real_inner_smul_left, hβ]
    ring
  · change Continuous (fun p : Sph d × Vec d => p4m_phi β p.1 p.2 * Real.exp (inner ℝ w p.2))
    unfold p4m_phi; fun_prop
  · intro x z
    refine p4m_mul_bd (p4m_phi_abs hβ0 x z) ?_
    rw [abs_of_pos (Real.exp_pos _), one_mul]
    gcongr
    exact real_inner_le_norm w z

end P4Main

theorem p4_main {d : ℕ} (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    IsProbabilityMeasure (uniformSphere d) ∧
    (∀ μ : Measure (Sph d), IsProbabilityMeasure μ →
      measureEnergy α (uniformSphere d) ≤ measureEnergy α μ) ∧
    (∀ μ : Measure (Sph d), IsProbabilityMeasure μ →
      (∀ ν : Measure (Sph d), IsProbabilityMeasure ν → measureEnergy α μ ≤ measureEnergy α ν) →
      μ = uniformSphere d) := by
  have hσ : IsProbabilityMeasure (uniformSphere d) := p4_sphere_prob hd
  have hβ0 : 0 ≤ Real.sqrt α := Real.sqrt_nonneg _
  have hβpos : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hβ : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
  obtain ⟨c, hcpos, hc⟩ := p4m_const hd hα.le
  have hEσ : measureEnergy α (uniformSphere d) = Real.log c := p4m_energy_const hd α c hc
  have hE : 0 < Real.exp (2 * α) * c := by positivity
  refine ⟨hσ, fun μ hμ => ?_, fun μ hμ hmin => ?_⟩
  · obtain ⟨-, hD0, -, hkey⟩ := p4m_D_facts hα.le hβ0 hβ μ (uniformSphere d) c hcpos hc
    have h1 := integral_nonneg (μ := p4rho d) (f := p4m_D (Real.sqrt α) μ (uniformSphere d)) (fun z => hD0 z)
    have h2 := mul_nonneg (inv_pos.mpr hE).le h1
    rw [hEσ]; linarith
  · obtain ⟨hDi, hD0, hDeq, hkey⟩ :=
      p4m_D_facts hα.le hβ0 hβ μ (uniformSphere d) c hcpos hc
    have h1 := hmin _ hσ
    rw [hEσ] at h1
    have hI0 : ∫ z, p4m_D (Real.sqrt α) μ (uniformSphere d) z ∂(p4rho d) = 0 := by
      refine le_antisymm ?_ (integral_nonneg (fun z => hD0 z))
      by_contra hpos
      replace hpos := lt_of_not_ge hpos
      have := mul_pos (inv_pos.mpr hE) hpos
      linarith
    have hae := (integral_eq_zero_iff_of_nonneg (fun z => hD0 z) hDi).mp hI0
    have hPQ : ∀ᵐ z ∂(p4rho d), p4m_G (Real.sqrt α) μ z =
        p4m_G (Real.sqrt α) (uniformSphere d) z := by
      filter_upwards [hae] with z hz using hDeq z hz
    have hmgf : ∀ w : Vec d, ∫ x, Real.exp (Real.sqrt α * inner ℝ (x : Vec d) w) ∂μ =
        ∫ x, Real.exp (Real.sqrt α * inner ℝ (x : Vec d) w) ∂(uniformSphere d) := by
      intro w
      have h := integral_congr_ae (μ := p4rho d)
        (f := fun z => p4m_G (Real.sqrt α) μ z * Real.exp (inner ℝ w z))
        (g := fun z => p4m_G (Real.sqrt α) (uniformSphere d) z * Real.exp (inner ℝ w z))
        (by filter_upwards [hPQ] with z hz; simp only [hz])
      rw [p4m_mgf hβ0 hβ μ w, p4m_mgf hβ0 hβ (uniformSphere d) w] at h
      exact mul_left_cancel₀ (Real.exp_pos _).ne' h
    apply p4_mgf_ext
    intro v
    have e : ∀ x : Sph d, Real.sqrt α * inner ℝ (x : Vec d) ((Real.sqrt α)⁻¹ • v) =
        inner ℝ (x : Vec d) v := by
      intro x; rw [real_inner_smul_right]; field_simp
    have := hmgf ((Real.sqrt α)⁻¹ • v)
    simp_rw [e] at this
    exact this

end NeuralCollapseCE

open NeuralCollapseCE in
theorem solution {d : ℕ} (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    IsProbabilityMeasure (uniformSphere d) ∧
    (∀ μ : Measure (Sph d), IsProbabilityMeasure μ →
      measureEnergy α (uniformSphere d) ≤ measureEnergy α μ) ∧
    (∀ μ : Measure (Sph d), IsProbabilityMeasure μ →
      (∀ ν : Measure (Sph d), IsProbabilityMeasure ν → measureEnergy α μ ≤ measureEnergy α ν) →
      μ = uniformSphere d) := p4_main hd α hα
