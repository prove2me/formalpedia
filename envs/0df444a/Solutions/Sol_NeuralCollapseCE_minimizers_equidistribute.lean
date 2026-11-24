-- Prove2me | solution 1 for NeuralCollapseCE.minimizers_equidistribute
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T04:35:43.365366+00:00
-- url     : https://prove2.me/submissions/37a384db-c6c4-407b-a8a1-4095ec3e633c

import Mathlib
import Definitions.Def_NeuralCollapseCE_Basic
import Theorems.Thm_NeuralCollapseCE_uniform_measure_unique_minimizer

open MeasureTheory Filter Topology

noncomputable section

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

section Generic

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

lemma t3c_integrable (f : C(X, ℝ)) (μ : ProbabilityMeasure X) :
    Integrable (fun x => f x) (μ : Measure X) :=
  (BoundedContinuousFunction.mkOfCompact f).integrable _

/-- Joint continuity of `(f, μ) ↦ ∫ f dμ` on `C(X, ℝ) × ProbabilityMeasure X`, `X` compact. -/
lemma t3c_pairing_continuous :
    Continuous (fun p : C(X, ℝ) × ProbabilityMeasure X => ∫ x, p.1 x ∂(p.2 : Measure X)) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨f0, μ0⟩
  have h2 : Tendsto (fun p : C(X, ℝ) × ProbabilityMeasure X => ∫ x, f0 x ∂(p.2 : Measure X))
      (𝓝 (f0, μ0)) (𝓝 (∫ x, f0 x ∂(μ0 : Measure X))) := by
    have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (continuous_snd.tendsto (f0, μ0))) (BoundedContinuousFunction.mkOfCompact f0)
    simpa using this
  have h1 : Tendsto (fun p : C(X, ℝ) × ProbabilityMeasure X =>
      ∫ x, p.1 x ∂(p.2 : Measure X) - ∫ x, f0 x ∂(p.2 : Measure X)) (𝓝 (f0, μ0)) (𝓝 0) := by
    have hn : Tendsto (fun p : C(X, ℝ) × ProbabilityMeasure X => ‖p.1 - f0‖)
        (𝓝 (f0, μ0)) (𝓝 0) := by
      have : Tendsto (fun p : C(X, ℝ) × ProbabilityMeasure X => p.1) (𝓝 (f0, μ0)) (𝓝 f0) :=
        continuous_fst.tendsto _
      simpa using (tendsto_iff_norm_sub_tendsto_zero.mp this)
    refine squeeze_zero_norm (fun p => ?_) hn
    rw [← integral_sub (t3c_integrable _ _) (t3c_integrable _ _)]
    calc ‖∫ x, (p.1 x - f0 x) ∂(p.2 : Measure X)‖
        ≤ ‖p.1 - f0‖ * (p.2 : Measure X).real Set.univ :=
          norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => by
            simpa using (p.1 - f0).norm_coe_le_norm x)
      _ = ‖p.1 - f0‖ := by simp
  have := h1.add h2
  simp only [sub_add_cancel, zero_add] at this
  exact this

end Generic

/-- The kernel `k(x, y) = exp (α (⟪x, y⟫ - 1))` as a continuous function on `S × S`. -/
def t3c_k (d : ℕ) (α : ℝ) : C(Sph d × Sph d, ℝ) :=
  ⟨fun p => Real.exp (α * (inner ℝ (p.1 : Vec d) (p.2 : Vec d) - 1)), by fun_prop⟩

/-- The energy is continuous for the weak topology on probability measures. -/
theorem t3_continuous (d : ℕ) (α : ℝ) :
    Continuous (fun μ : ProbabilityMeasure (Sph d) => measureEnergy α (μ : Measure (Sph d))) := by
  set F : ProbabilityMeasure (Sph d) × Sph d → ℝ := fun z =>
    ∫ y, Real.exp (α * (inner ℝ (z.2 : Vec d) (y : Vec d) - 1)) ∂(z.1 : Measure (Sph d)) with hFdef
  have hF : Continuous F :=
    t3c_pairing_continuous.comp
      (((t3c_k d α).curry.continuous.comp continuous_snd).prodMk continuous_fst)
  have hpos : ∀ z, 0 < F z := fun z =>
    integral_exp_pos (t3c_integrable ((t3c_k d α).curry z.2) z.1)
  let G : C(ProbabilityMeasure (Sph d) × Sph d, ℝ) :=
    ⟨fun z => Real.log (F z), hF.log (fun z => (hpos z).ne')⟩
  exact t3c_pairing_continuous.comp (G.curry.continuous.prodMk continuous_id)

end NeuralCollapseCE

namespace NeuralCollapseCE



/-! ### Helpers for `t3_symLoss_eq` -/

lemma t3p_integral_emp {d n : ℕ} (v : Fin n → Sph d) (g : Sph d → ℝ) :
    ∫ x, g x ∂(empiricalMeasure v) = (n : ℝ)⁻¹ * ∑ i, g (v i) := by
  unfold empiricalMeasure
  rw [integral_smul_measure,
    integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp [integral_dirac, smul_eq_mul, ENNReal.toReal_inv]

lemma t3p_energy_emp {d n : ℕ} (α : ℝ) (v : Fin n → Sph d) :
    measureEnergy α (empiricalMeasure v) = (n : ℝ)⁻¹ * ∑ i, Real.log ((n : ℝ)⁻¹ *
      ∑ j, Real.exp (α * (inner ℝ (v i : Vec d) (v j : Vec d) - 1))) := by
  unfold measureEnergy
  rw [t3p_integral_emp]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [t3p_integral_emp]

lemma t3p_self_term {d : ℕ} (α : ℝ) (x : Sph d) :
    Real.exp (α * (inner ℝ (x : Vec d) (x : Vec d) - 1)) = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere x]; simp

/-- The diagonal terms make the discrete loss an exact rescaling of the measure energy. -/
theorem t3_symLoss_eq {d n : ℕ} (hn : 1 ≤ n) (α : ℝ) (v : Fin n → Sph d) :
    symLoss α (fun i => (v i : Vec d)) =
      (n : ℝ) * Real.log n + (n : ℝ) * measureEnergy α (empiricalMeasure v) := by
  rw [t3p_energy_emp]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold symLoss
  have key : ∀ i : Fin n, Real.log (1 + ∑ j ∈ Finset.univ.erase i,
      Real.exp (α * (inner ℝ (v j : Vec d) (v i : Vec d) - 1))) =
      Real.log n + Real.log ((n : ℝ)⁻¹ *
        ∑ j, Real.exp (α * (inner ℝ (v i : Vec d) (v j : Vec d) - 1))) := by
    intro i
    have hS : 1 + ∑ j ∈ Finset.univ.erase i,
        Real.exp (α * (inner ℝ (v j : Vec d) (v i : Vec d) - 1)) =
        ∑ j, Real.exp (α * (inner ℝ (v i : Vec d) (v j : Vec d) - 1)) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), t3p_self_term]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [real_inner_comm]
    have hpos : 0 < ∑ j, Real.exp (α * (inner ℝ (v i : Vec d) (v j : Vec d) - 1)) :=
      Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨i, Finset.mem_univ _⟩
    rw [hS, Real.log_mul (inv_ne_zero hn0.ne') hpos.ne', Real.log_inv]
    ring
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hn0.ne',
    one_mul]

/-! ### Helpers for `t3_greedy` -/

/-- The kernel `k(x, y) = exp (α (⟨x, y⟩ - 1))`. -/
def t3p_k {d : ℕ} (α : ℝ) (x y : Sph d) : ℝ :=
  Real.exp (α * (inner ℝ (x : Vec d) (y : Vec d) - 1))

lemma t3p_k_symm {d : ℕ} (α : ℝ) (x y : Sph d) : t3p_k α x y = t3p_k α y x := by
  unfold t3p_k; rw [real_inner_comm]

lemma t3p_k_self {d : ℕ} (α : ℝ) (x : Sph d) : t3p_k α x x = 1 := t3p_self_term α x

lemma t3p_k_cont {d : ℕ} {X : Type*} [TopologicalSpace X] (α : ℝ) {f g : X → Sph d}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun z => t3p_k α (f z) (g z)) := by
  unfold t3p_k
  exact Real.continuous_exp.comp (continuous_const.mul
    (((continuous_subtype_val.comp hf).inner (continuous_subtype_val.comp hg)).sub
      continuous_const))

lemma t3p_nonempty {d : ℕ} (hd : 1 ≤ d) : Nonempty (Sph d) :=
  ⟨⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ), by simp⟩⟩

lemma t3p_integrable {d : ℕ} (hd : 1 ≤ d) {f : Sph d → ℝ} (hf : Continuous f) :
    Integrable f (uniformSphere d) := by
  have := p4_sphere_prob hd
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

lemma t3p_const {d : ℕ} (hd : 1 ≤ d) (α : ℝ) (x x' : Sph d) :
    ∫ y, t3p_k α x y ∂(uniformSphere d) = ∫ y, t3p_k α x' y ∂(uniformSphere d) :=
  p4_sphere_invariant hd (fun t => Real.exp (α * (t - 1))) (by fun_prop) x x'

lemma t3p_pos {d : ℕ} (hd : 1 ≤ d) (α : ℝ) (x0 : Sph d) :
    0 < ∫ y, t3p_k α x0 y ∂(uniformSphere d) := by
  have := p4_sphere_prob hd
  exact integral_exp_pos (f := fun y : Sph d => α * (inner ℝ (x0 : Vec d) (y : Vec d) - 1))
    (t3p_integrable hd (t3p_k_cont α continuous_const continuous_id'))

lemma t3p_energy_unif {d : ℕ} (hd : 1 ≤ d) (α : ℝ) (x0 : Sph d) :
    Real.exp (measureEnergy α (uniformSphere d)) = ∫ y, t3p_k α x0 y ∂(uniformSphere d) := by
  have := p4_sphere_prob hd
  have hc : ∀ x : Sph d, ∫ y, Real.exp (α * (inner ℝ (x : Vec d) (y : Vec d) - 1))
      ∂(uniformSphere d) = ∫ y, t3p_k α x0 y ∂(uniformSphere d) := fun x => t3p_const hd α x x0
  unfold measureEnergy
  simp_rw [hc]
  simp [Real.exp_log (t3p_pos hd α x0)]

lemma t3p_step {d : ℕ} (hd : 1 ≤ d) (α c : ℝ)
    (hc : ∀ x, ∫ y, t3p_k α x y ∂(uniformSphere d) = c) {m : ℕ} (w : Fin m → Sph d) :
    ∃ x : Sph d, ∑ j, t3p_k α x (w j) ≤ m * c := by
  have := p4_sphere_prob hd
  have := t3p_nonempty hd
  let F : Sph d → ℝ := fun x => ∑ j, t3p_k α x (w j)
  have hFc : Continuous F :=
    continuous_finsetSum _ fun j _ => t3p_k_cont α continuous_id' continuous_const
  obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hFc.continuousOn
  refine ⟨x, ?_⟩
  have h1 : ∫ _y, F x ∂(uniformSphere d) ≤ ∫ y, F y ∂(uniformSphere d) :=
    integral_mono (integrable_const _) (t3p_integrable hd hFc)
      (fun y => isMinOn_iff.mp hx y (Set.mem_univ y))
  have hj : ∀ j, ∫ y, t3p_k α y (w j) ∂(uniformSphere d) = c := fun j => by
    rw [← hc (w j)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => t3p_k_symm α y (w j))
  have h2 : ∫ y, F y ∂(uniformSphere d) = m * c := by
    simp only [F]
    rw [integral_finsetSum _
      (fun j _ => t3p_integrable hd (t3p_k_cont α continuous_id' continuous_const))]
    simp [hj]
  rw [integral_const] at h1
  simp only [probReal_univ, one_smul] at h1
  simp only [F] at h1
  linarith

lemma t3p_build {d : ℕ} (hd : 1 ≤ d) (α c : ℝ)
    (hc : ∀ x, ∫ y, t3p_k α x y ∂(uniformSphere d) = c) (m : ℕ) :
    ∃ w : Fin m → Sph d, ∑ i, ∑ j, t3p_k α (w i) (w j) ≤ m + m * (m - 1) * c := by
  induction m with
  | zero => exact ⟨Fin.elim0, by simp⟩
  | succ m ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨x, hx⟩ := t3p_step hd α c hc w
    refine ⟨Fin.cons x w, ?_⟩
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, t3p_k_self,
      Finset.sum_add_distrib]
    have hsym : ∑ i, t3p_k α (w i) x = ∑ j, t3p_k α x (w j) :=
      Finset.sum_congr rfl fun i _ => t3p_k_symm α _ _
    rw [hsym]
    push_cast
    have e : ((m : ℝ) + 1) + ((m : ℝ) + 1) * ((m : ℝ) + 1 - 1) * c =
        ((m : ℝ) + m * (m - 1) * c) + 1 + 2 * (m * c) := by ring
    linarith

/-- Greedy upper bound: some `n`-point configuration has energy at most
`log ((1 + (n - 1) c) / n)`, where `c = exp (measureEnergy α σ)`. -/
theorem t3_greedy {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (α : ℝ) :
    ∃ v : Fin n → Sph d, measureEnergy α (empiricalMeasure v) ≤
      Real.log ((1 + ((n : ℝ) - 1) * Real.exp (measureEnergy α (uniformSphere d))) / n) := by
  have := p4_sphere_prob hd
  obtain ⟨x0⟩ := t3p_nonempty hd
  rw [t3p_energy_unif hd α x0]
  set c := ∫ y, t3p_k α x0 y ∂(uniformSphere d) with hcdef
  have hc : ∀ x, ∫ y, t3p_k α x y ∂(uniformSphere d) = c := fun x => t3p_const hd α x x0
  have hcpos : 0 < c := t3p_pos hd α x0
  obtain ⟨w, hw⟩ := t3p_build hd α c hc n
  refine ⟨w, ?_⟩
  let T : Fin n → ℝ := fun i => ∑ j, t3p_k α (w i) (w j)
  have hE : measureEnergy α (empiricalMeasure w) =
      (n : ℝ)⁻¹ * ∑ i, Real.log ((n : ℝ)⁻¹ * T i) := t3p_energy_emp α w
  have hw' : ∑ i, T i ≤ n + n * (n - 1) * c := hw
  rw [hE]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set a := 1 + ((n : ℝ) - 1) * c with ha
  have hapos : 0 < a := by nlinarith
  have hT : ∀ i, 0 < T i := fun i =>
    Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨i, Finset.mem_univ _⟩
  have hlog : ∀ i, Real.log ((n : ℝ)⁻¹ * T i) ≤ Real.log (a / n) + T i / a - 1 := by
    intro i
    have hp1 : 0 < (n : ℝ)⁻¹ * T i := mul_pos (inv_pos.2 hn0) (hT i)
    have hp2 : 0 < a / n := div_pos hapos hn0
    have h1 := Real.log_le_sub_one_of_pos (div_pos hp1 hp2)
    rw [Real.log_div hp1.ne' hp2.ne'] at h1
    have : (n : ℝ)⁻¹ * T i / (a / n) = T i / a := by field_simp
    rw [this] at h1
    linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hlog i
  have e1 : ∑ i, (Real.log (a / n) + T i / a - 1) = n * Real.log (a / n) + (∑ i, T i) / a - n := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div]
    simp
  rw [e1] at hsum
  have hQ : (∑ i, T i) / a ≤ n := by
    rw [div_le_iff₀ hapos]
    have : (n : ℝ) + n * (n - 1) * c = n * a := by rw [ha]; ring
    linarith
  rw [inv_mul_le_iff₀ hn0]
  linarith


end NeuralCollapseCE

namespace NeuralCollapseCE

theorem t3m_isProb {d n : ℕ} (hn : 1 ≤ n) (v : Fin n → Sph d) :
    IsProbabilityMeasure (empiricalMeasure v) := by
  constructor
  have hn' : (n : ENNReal) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp [empiricalMeasure, ENNReal.inv_mul_cancel hn' (ENNReal.natCast_ne_top n)]

theorem t3m_upper {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (α : ℝ) (w : Fin n → Sph d)
    (hw : IsSymMinimizer α (fun i => ((w i : Sph d) : Vec d))) :
    measureEnergy α (empiricalMeasure w) ≤
      Real.log ((1 + ((n : ℝ) - 1) * Real.exp (measureEnergy α (uniformSphere d))) / n) := by
  obtain ⟨v, hv⟩ := t3_greedy (α := α) hd hn
  have hunit : IsUnitConfig (fun i => ((v i : Sph d) : Vec d)) := fun i => by simp
  have h1 := hw.2 _ hunit
  rw [t3_symLoss_eq hn, t3_symLoss_eq hn] at h1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have : measureEnergy α (empiricalMeasure w) ≤ measureEnergy α (empiricalMeasure v) := by
    exact le_of_mul_le_mul_left (by linarith) hnpos
  exact this.trans hv

theorem t3m_bound_tendsto (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => Real.log ((1 + (((n + 1 : ℕ) : ℝ) - 1) * c) / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 (Real.log c)) := by
  have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h1 : Tendsto (fun n : ℕ => c + (1 - c) * (1 / ((n : ℝ) + 1))) atTop (𝓝 c) := by
    simpa using (tendsto_const_nhds (x := c)).add (h0.const_mul (1 - c))
  have h2 : Tendsto (fun n : ℕ => (1 + (((n + 1 : ℕ) : ℝ) - 1) * c) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 c) := by
    refine h1.congr fun n => ?_
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  exact h2.log hc.ne'

theorem t3_main {d : ℕ} (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (u : (n : ℕ) → Fin n → Sph d)
    (hu : ∀ n, IsSymMinimizer α (fun i => ((u n i : Sph d) : Vec d))) :
    ∀ f : C(Sph d, ℝ),
      Tendsto (fun n => ∫ x, f x ∂(empiricalMeasure (u n))) atTop
        (𝓝 (∫ x, f x ∂(uniformSphere d))) := by
  intro f
  obtain ⟨hσ, hmin, huniq⟩ := uniform_measure_unique_minimizer hd α hα
  set L : ProbabilityMeasure (Sph d) → ℝ := fun μ => measureEnergy α (μ : Measure (Sph d))
    with hL
  let σP : ProbabilityMeasure (Sph d) := ⟨uniformSphere d, hσ⟩
  let P : ℕ → ProbabilityMeasure (Sph d) := fun n =>
    ⟨empiricalMeasure (u (n + 1)), t3m_isProb (by omega) _⟩
  set c := Real.exp (measureEnergy α (uniformSphere d)) with hc
  have hcpos : 0 < c := Real.exp_pos _
  -- (a) upper bound
  have hub : ∀ n, L (P n) ≤
      Real.log ((1 + (((n + 1 : ℕ) : ℝ) - 1) * c) / ((n + 1 : ℕ) : ℝ)) := fun n =>
    t3m_upper hd (by omega) α (u (n + 1)) (hu (n + 1))
  have hlim := t3m_bound_tendsto c hcpos
  rw [hc, Real.log_exp] at hlim
  -- (b) unique cluster point
  have hT : Tendsto P atTop (𝓝 σP) := by
    apply tendsto_nhds_of_unique_mapClusterPt
    intro μ hμ
    have hcl : MapClusterPt (L μ) atTop (L ∘ P) :=
      hμ.continuousAt_comp (t3_continuous d α).continuousAt
    have hle : L μ ≤ measureEnergy α (uniformSphere d) := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hev : ∀ᶠ n in atTop, (L ∘ P) n ≤ measureEnergy α (uniformSphere d) + ε := by
        filter_upwards [(hlim.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε)))] with n hn
        exact (hub n).trans hn.le
      have := ClusterPt.mem_closure_of_mem hcl (s := Set.Iic _) hev
      rwa [closure_Iic] at this
    have : (μ : Measure (Sph d)) = uniformSphere d :=
      huniq μ inferInstance fun ν hν => hle.trans (hmin ν hν)
    exact Subtype.ext this
  -- (c) convert
  have hF := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hT)
    (BoundedContinuousFunction.mkOfCompact f)
  simp only [BoundedContinuousFunction.mkOfCompact_apply] at hF
  exact (Filter.tendsto_add_atTop_iff_nat 1).1 hF

end NeuralCollapseCE

open NeuralCollapseCE in
theorem solution {d : ℕ} (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (u : (n : ℕ) → Fin n → Sph d)
    (hu : ∀ n, IsSymMinimizer α (fun i => ((u n i : Sph d) : Vec d))) :
    ∀ f : C(Sph d, ℝ),
      Tendsto (fun n => ∫ x, f x ∂(empiricalMeasure (u n))) atTop
        (𝓝 (∫ x, f x ∂(uniformSphere d))) := t3_main hd α hα u hu
