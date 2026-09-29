-- Prove2me | solution 1 for HairerSPDE.joint_gaussian_of_memLp_closure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T23:26:37.297978+00:00
-- url     : https://prove2.me/submissions/077c501a-470e-48a9-92a8-02d225e19736

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology InnerProductSpace

private theorem l2_inner_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Lp ℝ 2 μ) :
    ⟪f, g⟫_ℝ = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  rw [Real.inner_apply]

private theorem gaussian_l2_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ℕ → Lp ℝ 2 μ) (g : Lp ℝ 2 μ)
    (hf : ∀ n, μ.map (f n) = gaussianReal 0 (‖f n‖ ^ 2).toNNReal)
    (hlim : Tendsto f atTop (𝓝 g)) :
    μ.map g = gaussianReal 0 (‖g‖ ^ 2).toNNReal := by
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  apply Measure.ext_of_charFun
  funext t
  let F : ℝ → ℂ := fun y => Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hbound (y : ℝ) : ‖F y‖ ≤ 1 := by
    simp [F, Complex.norm_exp]
  have hi : Tendsto (fun n => ∫ x, F (f (ns n) x) ∂μ) atTop
      (𝓝 (∫ x, F (g x) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro n
      exact hF.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)
    · exact integrable_const 1
    · intro n
      exact Eventually.of_forall fun x => hbound _
    · filter_upwards [hae] with x hx
      exact hF.continuousAt.tendsto.comp hx
  have hmap (u : Lp ℝ 2 μ) : charFun (μ.map u) t = ∫ x, F (u x) ∂μ := by
    rw [charFun_apply_real, integral_map (Lp.aestronglyMeasurable u).aemeasurable
      hF.aestronglyMeasurable]
  have hn : Tendsto (fun n => charFun (gaussianReal 0 (‖f (ns n)‖ ^ 2).toNNReal) t)
      atTop (𝓝 (charFun (gaussianReal 0 (‖g‖ ^ 2).toNNReal) t)) := by
    simp only [charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul,
      zero_sub, Real.coe_toNNReal _ (sq_nonneg _)]
    have hh := (hlim.comp hns.tendsto_atTop).norm.pow 2
    exact Complex.continuous_exp.continuousAt.tendsto.comp
      (((Complex.continuous_ofReal.continuousAt.tendsto.comp hh).mul_const
        ((t : ℂ) ^ 2)).div_const 2).neg
  have he : (fun n => ∫ x, F (f (ns n) x) ∂μ) =
      (fun n => charFun (gaussianReal 0 (‖f (ns n)‖ ^ 2).toNNReal) t) := by
    funext n
    rw [← hf, hmap]
  rw [he] at hi
  rw [hmap]
  exact tendsto_nhds_unique hi hn

theorem solution {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h' : B → ℝ)
    (h'meas : Measurable h') (h'mem : MemLp h' 2 μ)
    (h'orth : (∀ g : B → ℝ, MemLp g 2 μ →
        (∀ L : StrongDual ℝ B, ∫ x, g x * L x ∂μ = 0) → ∫ x, h' x * g x ∂μ = 0)) :
    ∀ (L : StrongDual ℝ B) (a b : ℝ),
      μ.map (fun x => a * L x + b * h' x) =
        gaussianReal 0 ((ProbabilityTheory.variance (fun x => a * L x + b * h' x) μ).toNNReal) := by
  classical
  have hLmem : ∀ L : StrongDual ℝ B, MemLp (fun x => L x) 2 μ :=
    fun L => IsGaussian.memLp_dual μ L 2 (by simp)
  let J : StrongDual ℝ B →ₗ[ℝ] Lp ℝ 2 μ :=
    { toFun := fun L => (hLmem L).toLp _
      map_add' := fun L₁ L₂ => by
        have hc := MemLp.toLp_congr (hLmem (L₁ + L₂)) ((hLmem L₁).add (hLmem L₂))
          (Eventually.of_forall fun x => by simp)
        rw [hc, MemLp.toLp_add]
      map_smul' := fun c L => by
        show (hLmem (c • L)).toLp _ = c • (hLmem L).toLp _
        have hc := MemLp.toLp_congr (hLmem (c • L)) ((hLmem L).const_smul c)
          (Eventually.of_forall fun x => by simp)
        rw [hc, MemLp.toLp_const_smul] }
  let S := LinearMap.range J
  let R := S.topologicalClosure
  let p : Lp ℝ 2 μ := h'mem.toLp h'
  have hp_ae : (⇑p : B → ℝ) =ᵐ[μ] h' := MemLp.coeFn_toLp h'mem
  have hJ_ae (L : StrongDual ℝ B) : (⇑(J L) : B → ℝ) =ᵐ[μ] (fun x => L x) :=
    MemLp.coeFn_toLp (hLmem L)
  have hpR : p ∈ R := by
    change p ∈ S.topologicalClosure
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal']
    intro g hg
    rw [l2_inner_integral]
    have hgL (L : StrongDual ℝ B) : ∫ x, g x * L x ∂μ = 0 := by
      have hi := (Submodule.mem_orthogonal' S g).mp hg (J L) ⟨L, rfl⟩
      rw [l2_inner_integral] at hi
      calc
        _ = ∫ x, g x * J L x ∂μ := by
          apply integral_congr_ae
          filter_upwards [hJ_ae L] with x hx
          rw [hx]
        _ = 0 := hi
    calc
      _ = ∫ x, h' x * g x ∂μ := integral_congr_ae (hp_ae.mul (Eventually.of_forall fun _ => rfl))
      _ = 0 := h'orth g (Lp.memLp g) hgL
  have hJlaw (L : StrongDual ℝ B) : μ.map (J L) = gaussianReal 0 (‖J L‖ ^ 2).toNNReal := by
    have hm : ∫ x, L x ∂μ = 0 := by
      rw [IsGaussian.integral_dual L]
      change L (∫ x, id x ∂μ) = 0
      rw [hμ, map_zero]
    have hv : variance (fun x => L x) μ = ‖J L‖ ^ 2 := by
      rw [variance_of_integral_eq_zero L.continuous.measurable.aemeasurable hm,
        ← real_inner_self_eq_norm_sq, l2_inner_integral]
      apply integral_congr_ae
      filter_upwards [hJ_ae L] with x hx
      rw [hx, pow_two]
    rw [Measure.map_congr (hJ_ae L), IsGaussian.map_eq_gaussianReal]
    rw [hm, hv]
  intro L a b
  let q : Lp ℝ 2 μ := a • J L + b • p
  have hqR : q ∈ R := R.add_mem (R.smul_mem a (S.le_topologicalClosure ⟨L, rfl⟩))
    (R.smul_mem b hpR)
  have hqcl : q ∈ closure (S : Set (Lp ℝ 2 μ)) := by
    exact hqR
  obtain ⟨f, hf, hlim⟩ := mem_closure_iff_seq_limit.mp hqcl
  have hflaw (n : ℕ) : μ.map (f n) = gaussianReal 0 (‖f n‖ ^ 2).toNNReal := by
    obtain ⟨K, hK⟩ := hf n
    rw [← hK]
    exact hJlaw K
  have hq := gaussian_l2_limit μ f q hflaw hlim
  have hqae : (⇑q : B → ℝ) =ᵐ[μ] (fun x => a * L x + b * h' x) := by
    filter_upwards [Lp.coeFn_add (a • J L) (b • p), Lp.coeFn_smul a (J L),
      Lp.coeFn_smul b p, hJ_ae L, hp_ae] with x hx ha hb hL hp
    simpa only [q, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha, hb, hL, hp] using hx
  have hv : variance (fun x => a * L x + b * h' x) μ = (‖q‖ ^ 2).toNNReal := by
    have hm : AEMeasurable (fun x => a * L x + b * h' x) μ :=
      ((L.continuous.measurable.const_mul a).add (h'meas.const_mul b)).aemeasurable
    rw [← variance_id_map hm,
      ← Measure.map_congr hqae, hq, variance_id_gaussianReal]
  rw [← Measure.map_congr hqae, hq, hv, Real.toNNReal_coe]
