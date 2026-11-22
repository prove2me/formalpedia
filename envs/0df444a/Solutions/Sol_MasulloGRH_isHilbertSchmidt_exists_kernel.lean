-- Prove2me | solution 1 for MasulloGRH.isHilbertSchmidt_exists_kernel
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:53:12.613067+00:00
-- url     : https://prove2.me/submissions/370f7cba-2d59-4baf-bf3c-fffc669d0786

import Mathlib
import Definitions.Def_MasulloGRH_HilbertNuclear

open Filter Topology MeasureTheory
set_option autoImplicit false

namespace Sol_MasulloGRH_isHilbertSchmidt_exists_kernel

open scoped ComplexConjugate ENNReal InnerProductSpace

theorem L2_norm_sq {Z : Type*} [MeasurableSpace Z] {ρ : Measure Z}
    (g : Lp ℂ 2 ρ) : ‖g‖ ^ 2 = ∫ z, ‖g z‖ ^ 2 ∂ρ := by
  rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ, L2.inner_def]
  simp_rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem L2_norm_sq_toLp {Z : Type*} [MeasurableSpace Z] {ρ : Measure Z}
    {g : Z → ℂ} (hg : MemLp g 2 ρ) :
    ‖hg.toLp g‖ ^ 2 = ∫ z, ‖g z‖ ^ 2 ∂ρ := by
  rw [L2_norm_sq]
  exact integral_congr_ae (hg.coeFn_toLp.fun_comp (fun c ↦ ‖c‖ ^ 2))

theorem integrable_mul_of_L2 {Z : Type*} [MeasurableSpace Z] {ρ : Measure Z}
    {g h : Z → ℂ} (hg : MemLp g 2 ρ) (hh : MemLp h 2 ρ) :
    Integrable (fun z ↦ g z * h z) ρ := by
  have : ENNReal.HolderTriple 2 2 1 := by infer_instance
  exact memLp_one_iff_integrable.mp (hh.mul' hg)

theorem exists_conj_L2 {Z : Type*} [MeasurableSpace Z] {ρ : Measure Z}
    {g : Z → ℂ} (hg : MemLp g 2 ρ) :
    ∃ u : Lp ℂ 2 ρ, (u =ᵐ[ρ] fun z ↦ conj (g z)) ∧ ‖u‖ = ‖hg.toLp g‖ := by
  let h : Z → ℂ := fun z ↦ conj (g z)
  have hh : MemLp h 2 ρ := by
    apply (memLp_two_iff_integrable_sq_norm _).mpr
    · simpa [h] using (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
    · exact Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable
  refine ⟨hh.toLp h, hh.coeFn_toLp, (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_⟩
  rw [L2_norm_sq_toLp, L2_norm_sq_toLp]
  simp [h]

theorem integral_eq_inner_of_conj {Z : Type*} [MeasurableSpace Z] {ρ : Measure Z}
    {g : Z → ℂ} {u : Lp ℂ 2 ρ} (hu : u =ᵐ[ρ] fun z ↦ conj (g z)) (f : Lp ℂ 2 ρ) :
    (∫ z, g z * f z ∂ρ) = ⟪u, f⟫_ℂ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu] with z hz
  simp [hz, RCLike.inner_apply, mul_comm]

theorem norm_integral_mul_le {Z : Type*} [MeasurableSpace Z] {ρ : Measure Z}
    {g : Z → ℂ} (hg : MemLp g 2 ρ) (f : Lp ℂ 2 ρ) :
    ‖∫ z, g z * f z ∂ρ‖ ≤ ‖hg.toLp g‖ * ‖f‖ := by
  obtain ⟨u, hu, hnorm⟩ := exists_conj_L2 hg
  rw [← hnorm]
  exact (le_of_eq (congrArg norm (integral_eq_inner_of_conj hu f))).trans (norm_inner_le_norm _ _)

section
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]

/-- For almost every `x`, the row `y ↦ K (x, y)` of an L² kernel is square integrable. -/
theorem rows_memLp (K : Lp ℂ 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, MemLp (fun y ↦ K (x, y)) 2 μ := by
  have h := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable K)).mp (Lp.memLp K)
  filter_upwards [h.prod_right_ae] with x hx
  exact (memLp_two_iff_integrable_sq_norm
    ((Lp.stronglyMeasurable K).comp_measurable measurable_prodMk_left).aestronglyMeasurable).mpr hx

theorem rows_memLp_fun {k : X × X → ℂ} (hk : MemLp k 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, MemLp (fun y ↦ k (x, y)) 2 μ := by
  filter_upwards [rows_memLp (hk.toLp k), Measure.ae_ae_of_ae_prod hk.coeFn_toLp] with x hx h'
  exact hx.ae_eq h'

theorem rows_norm_sq (K : Lp ℂ 2 (μ.prod μ)) :
    Integrable (fun x ↦ ∫ y, ‖K (x, y)‖ ^ 2 ∂μ) μ ∧
      (∫ x, ∫ y, ‖K (x, y)‖ ^ 2 ∂μ ∂μ) = ‖K‖ ^ 2 := by
  have h := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable K)).mp (Lp.memLp K)
  exact ⟨h.integral_prod_left, (integral_prod _ h).symm.trans (L2_norm_sq K).symm⟩

theorem kernel_memLp (K : Lp ℂ 2 (μ.prod μ)) (f : Lp ℂ 2 μ) :
    MemLp (fun x ↦ ∫ y, K (x, y) * f y ∂μ) 2 μ := by
  have hmeas : StronglyMeasurable (fun z : X × X ↦ K z * f z.2) :=
    (Lp.stronglyMeasurable K).mul ((Lp.stronglyMeasurable f).comp_measurable measurable_snd)
  apply (memLp_two_iff_integrable_sq_norm hmeas.integral_prod_right'.aestronglyMeasurable).mpr
  refine ((rows_norm_sq K).1.const_mul (‖f‖ ^ 2)).mono'
    (hmeas.integral_prod_right'.norm.pow 2).aestronglyMeasurable ?_
  filter_upwards [rows_memLp K] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _), mul_comm, ← L2_norm_sq_toLp hx, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_integral_mul_le hx f) 2

theorem kernelOp_bound (K : Lp ℂ 2 (μ.prod μ)) (f : Lp ℂ 2 μ) :
    ‖(kernel_memLp K f).toLp _‖ ≤ ‖K‖ * ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [L2_norm_sq_toLp, mul_pow, ← (rows_norm_sq K).2, ← integral_mul_const]
  apply integral_mono_ae
    ((memLp_two_iff_integrable_sq_norm (kernel_memLp K f).aestronglyMeasurable).mp
      (kernel_memLp K f)) ((rows_norm_sq K).1.mul_const _)
  filter_upwards [rows_memLp K] with x hx
  rw [← L2_norm_sq_toLp hx, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_integral_mul_le hx f) 2

/-- The integral operator `f ↦ (x ↦ ∫ y, K (x, y) f y)` of an L² kernel. -/
noncomputable def kernelOp (K : Lp ℂ 2 (μ.prod μ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ (kernel_memLp K f).toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(kernel_memLp K (f + g)).coeFn_toLp,
          (kernel_memLp K f).coeFn_toLp, (kernel_memLp K g).coeFn_toLp,
          Lp.coeFn_add ((kernel_memLp K f).toLp _) ((kernel_memLp K g).toLp _),
          rows_memLp K] with x hfg hf hg hadd hx
        rw [hfg, hadd, Pi.add_apply, hf, hg, ← integral_add
          (integrable_mul_of_L2 hx (Lp.memLp f)) (integrable_mul_of_L2 hx (Lp.memLp g))]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f g] with y hy
        rw [hy, Pi.add_apply, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(kernel_memLp K (c • f)).coeFn_toLp,
          (kernel_memLp K f).coeFn_toLp,
          Lp.coeFn_smul c ((kernel_memLp K f).toLp _)] with x hcf hf hsmul
        simp only [RingHom.id_apply]
        rw [hcf, hsmul, Pi.smul_apply, hf, ← integral_smul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with y hy
        rw [hy, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        ring } ‖K‖ (kernelOp_bound K)

theorem kernelOp_apply (K : Lp ℂ 2 (μ.prod μ)) (f : Lp ℂ 2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ K (x, y) * f y) μ ∧
      kernelOp K f x = ∫ y, K (x, y) * f y ∂μ := by
  filter_upwards [rows_memLp K, (kernel_memLp K f).coeFn_toLp] with x hx h
  exact ⟨integrable_mul_of_L2 hx (Lp.memLp f), h⟩

/-- Integration against an L² kernel is linear in the kernel. -/
noncomputable def kernelLin :
    Lp ℂ 2 (μ.prod μ) →ₗ[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) where
  toFun := kernelOp
  map_add' K L := by
    ext1 f
    apply Lp.ext
    have h := Measure.ae_ae_of_ae_prod (Lp.coeFn_add K L)
    filter_upwards [kernelOp_apply (K + L) f, kernelOp_apply K f,
      kernelOp_apply L f, h, Lp.coeFn_add (kernelOp K f) (kernelOp L f)]
      with x hkl hk hl hx hadd
    change kernelOp (K + L) f x = (kernelOp K f + kernelOp L f) x
    rw [hkl.2, hadd, Pi.add_apply, hk.2, hl.2, ← integral_add hk.1 hl.1]
    apply integral_congr_ae
    filter_upwards [hx] with y hy
    exact (congrArg (fun z : ℂ ↦ z * f y) hy).trans (add_mul _ _ _)
  map_smul' c K := by
    ext1 f
    apply Lp.ext
    have h := Measure.ae_ae_of_ae_prod (Lp.coeFn_smul c K)
    filter_upwards [kernelOp_apply (c • K) f, kernelOp_apply K f,
      h, Lp.coeFn_smul c (kernelOp K f)] with x hck hk hx hsmul
    change kernelOp (c • K) f x = (c • kernelOp K f) x
    rw [hck.2, hsmul, Pi.smul_apply, hk.2, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [hx] with y hy
    exact (congrArg (fun z : ℂ ↦ z * f y) hy).trans (mul_assoc _ _ _)

theorem kernelLin_apply (K : Lp ℂ 2 (μ.prod μ)) : kernelLin K = kernelOp K := rfl

theorem kernelOp_norm_le (K : Lp ℂ 2 (μ.prod μ)) : ‖kernelOp K‖ ≤ ‖K‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) (kernelOp_bound K)

/-- The kernel-to-operator map as a bounded linear map. -/
noncomputable def kernelCLM : Lp ℂ 2 (μ.prod μ) →L[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  (kernelLin (μ := μ)).mkContinuous 1 (fun K ↦
    (kernelOp_norm_le K).trans_eq (one_mul _).symm)

theorem kernelCLM_apply (K : Lp ℂ 2 (μ.prod μ)) : kernelCLM K = kernelOp K := rfl

end

section
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]

/-- Parseval on the rows gives the squared L² norm of the kernel. -/
theorem hasSum_norm_sq_kernelOp {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (K : Lp ℂ 2 (μ.prod μ)) :
    HasSum (fun i ↦ ‖kernelOp K (b i)‖ ^ 2) (‖K‖ ^ 2) := by
  let F (i : ι) (x : X) := ‖kernelOp K (b i) x‖ ^ 2
  have hF (i : ι) : Integrable (F i) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hpoint : ∀ᵐ x ∂μ, (∑' i, ENNReal.ofReal (F i x)) =
      ENNReal.ofReal (∫ y, ‖K (x, y)‖ ^ 2 ∂μ) := by
    filter_upwards [rows_memLp K, ae_all_iff.mpr (fun i ↦ kernelOp_apply K (b i))]
      with x hx heval
    obtain ⟨u, hu, hnorm⟩ := exists_conj_L2 hx
    have hsum : HasSum (fun i ↦ F i x) (‖u‖ ^ 2) := by
      have hnormsum := lp.hasSum_norm (p := 2) (by norm_num) (b.repr u)
      convert hnormsum using 1
      · funext i
        change ‖kernelOp K (b i) x‖ ^ 2 = ‖b.repr u i‖ ^ (2 : ℝ≥0∞).toReal
        rw [b.repr_apply_apply, show (2 : ℝ≥0∞).toReal = (2 : ℕ) by norm_num,
          Real.rpow_natCast, (heval i).2, integral_eq_inner_of_conj hu, norm_inner_symm]
      · rw [b.repr.norm_map, show (2 : ℝ≥0∞).toReal = (2 : ℕ) by norm_num, Real.rpow_natCast]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _) hsum.summable,
      hsum.tsum_eq, hnorm, L2_norm_sq_toLp]
  have ht : (∑' i, ENNReal.ofReal (‖kernelOp K (b i)‖ ^ 2)) =
      ENNReal.ofReal (‖K‖ ^ 2) := by
    have heq (i : ι) : ENNReal.ofReal (‖kernelOp K (b i)‖ ^ 2) =
        ∫⁻ x, ENNReal.ofReal (F i x) ∂μ := by
      rw [L2_norm_sq, ofReal_integral_eq_lintegral_ofReal (hF i)
        (ae_of_all _ fun _ ↦ sq_nonneg _)]
    simp_rw [heq]
    rw [← lintegral_tsum (fun i ↦ (hF i).aemeasurable.ennreal_ofReal),
      lintegral_congr_ae hpoint,
      ← ofReal_integral_eq_lintegral_ofReal (rows_norm_sq K).1
        (ae_of_all _ fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _),
      (rows_norm_sq K).2]
  have hsum : Summable (fun i ↦ ‖kernelOp K (b i)‖ ^ 2) := by
    have hfin := ht.trans_ne ENNReal.ofReal_ne_top
    have hn := ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hfin
    simpa only [Real.coe_toNNReal _ (sq_nonneg _)] using hn
  have heq : (∑' i, ‖kernelOp K (b i)‖ ^ 2) = ‖K‖ ^ 2 := by
    rw [← ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg fun _ ↦ sq_nonneg _) (sq_nonneg _),
      ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _) hsum]
    exact ht
  exact heq ▸ hsum.hasSum

omit [SigmaFinite μ] in
theorem rankOne_memLp (f e : Lp ℂ 2 μ) :
    MemLp (fun z : X × X ↦ f z.1 * conj (e z.2)) 2 (μ.prod μ) := by
  have he := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable e)).mp (Lp.memLp e)
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  apply (memLp_two_iff_integrable_sq_norm
    (((Lp.stronglyMeasurable f).comp_measurable measurable_fst).mul
      ((Complex.continuous_conj.comp_stronglyMeasurable (Lp.stronglyMeasurable e)).comp_measurable
        measurable_snd)).aestronglyMeasurable).mpr
  change Integrable (fun z : X × X ↦ ‖f z.1 * conj (e z.2)‖ ^ 2) (μ.prod μ)
  simpa only [norm_mul, Complex.norm_conj, mul_pow] using hf.mul_prod he

/-- The kernel `(x, y) ↦ f x * conj (e y)` of the rank-one operator `g ↦ ⟪e, g⟫ • f`. -/
noncomputable def rankOneKernel (f e : Lp ℂ 2 μ) : Lp ℂ 2 (μ.prod μ) :=
  (rankOne_memLp f e).toLp _

theorem rankOneKernel_inner (f e f' e' : Lp ℂ 2 μ) :
    ⟪rankOneKernel f e, rankOneKernel f' e'⟫_ℂ = ⟪f, f'⟫_ℂ * ⟪e', e⟫_ℂ := by
  simp only [L2.inner_def]
  rw [← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [(rankOne_memLp f e).coeFn_toLp,
    (rankOne_memLp f' e').coeFn_toLp] with z hz hz'
  change (rankOneKernel f e) z = _ at hz
  change (rankOneKernel f' e') z = _ at hz'
  rw [hz, hz']
  simp only [RCLike.inner_apply, map_mul, starRingEnd_apply, star_star]
  ring

theorem kernelOp_rankOne (f e : Lp ℂ 2 μ) (g : Lp ℂ 2 μ) :
    kernelOp (rankOneKernel f e) g = ⟪e, g⟫_ℂ • f := by
  apply Lp.ext
  have h := Measure.ae_ae_of_ae_prod (rankOne_memLp f e).coeFn_toLp
  filter_upwards [kernelOp_apply (rankOneKernel f e) g, h,
    Lp.coeFn_smul ⟪e, g⟫_ℂ f] with x hx hker hsmul
  rw [hx.2, hsmul, Pi.smul_apply, smul_eq_mul, L2.inner_def, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [hker] with y hy
  change (rankOneKernel f e) (x, y) = f x * conj (e y) at hy
  rw [hy]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  ring

end


section
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]

/-- A bounded operator with `∑ ‖T bᵢ‖² < ∞` is the integral operator of the kernel
`∑ᵢ (T bᵢ) ⊗ conj bᵢ`. -/
theorem exists_kernel_of_summable {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hT : Summable fun i => ‖T (b i)‖ ^ 2) :
    ∃ K : Lp ℂ 2 (μ.prod μ), kernelOp K = T := by
  let w : ι → Lp ℂ 2 (μ.prod μ) := fun i => rankOneKernel (T (b i)) (b i)
  have horth (i j : ι) (hij : i ≠ j) : ⟪w i, w j⟫_ℂ = 0 := by
    simp only [w, rankOneKernel_inner, b.orthonormal.inner_eq_zero (Ne.symm hij), mul_zero]
  have hnorm (i : ι) : ‖w i‖ ^ 2 = ‖T (b i)‖ ^ 2 := by
    have h1 : ⟪w i, w i⟫_ℂ = ⟪T (b i), T (b i)⟫_ℂ := by
      rw [show w i = rankOneKernel (T (b i)) (b i) from rfl, rankOneKernel_inner,
        inner_self_eq_norm_sq_to_K (b i), b.orthonormal.norm_eq_one i]
      simp
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) (w i), norm_sq_eq_re_inner (𝕜 := ℂ) (T (b i)), h1]
  let V : ι → Submodule ℂ (Lp ℂ 2 (μ.prod μ)) := fun i => ℂ ∙ w i
  have hV : OrthogonalFamily ℂ (fun i => V i) (fun i => (V i).subtypeₗᵢ) := by
    apply orthogonalFamily_iff_pairwise.mpr
    intro i j hij
    change Submodule.span ℂ {w i} ⟂ Submodule.span ℂ {w j}
    rw [Submodule.isOrtho_span]
    intro u hu v hv
    rw [Set.mem_singleton_iff] at hu hv
    subst hu hv
    exact horth i j hij
  have hs : Summable w := by
    have h := (hV.summable_iff_norm_sq_summable
      (fun i => (⟨w i, Submodule.mem_span_singleton_self _⟩ : V i))).mpr
    apply h
    change Summable (fun i => ‖w i‖ ^ 2)
    simpa only [hnorm] using hT
  refine ⟨∑' i, w i, ?_⟩
  ext1 ϕ
  have h1 : HasSum (fun i => kernelCLM (w i) ϕ) (kernelCLM (∑' i, w i) ϕ) :=
    (ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ) ϕ).hasSum ((kernelCLM (μ := μ)).hasSum hs.hasSum)
  have h2 : HasSum (fun i => T (b.repr ϕ i • b i)) (T ϕ) := T.hasSum (b.hasSum_repr ϕ)
  simp only [kernelCLM_apply, w, kernelOp_rankOne] at h1
  simp only [map_smul, b.repr_apply_apply] at h2
  exact h1.unique h2

end

theorem countable_of_hilbertBasis {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [TopologicalSpace.SeparableSpace H] {ι : Type*}
    (b : HilbertBasis ι ℂ H) : Countable ι := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i ↦ Metric.ball (b i) (1 / 2))
    ?_ (fun _ ↦ Metric.isOpen_ball) (fun _ ↦ Metric.nonempty_ball.mpr (by norm_num))
  intro i j hij
  apply Metric.ball_disjoint_ball
  have hsq : dist (b i) (b j) ^ 2 = 2 := by
    rw [dist_eq_norm, @norm_sub_sq ℂ, b.orthonormal.inner_eq_zero hij,
      b.orthonormal.norm_eq_one, b.orthonormal.norm_eq_one]
    norm_num
  rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
  apply (sq_le_sq₀ zero_le_one dist_nonneg).mp
  rw [hsq]
  norm_num

end Sol_MasulloGRH_isHilbertSchmidt_exists_kernel

open MasulloGRH Sol_MasulloGRH_isHilbertSchmidt_exists_kernel in
theorem solution
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.Regular] [SigmaFinite μ]
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hT : IsHilbertSchmidt T) :
    ∃ k : X × X → ℂ, MemLp k 2 (μ.prod μ) ∧
      (∀ ϕ : Lp ℂ 2 μ, ∀ᵐ x ∂μ,
        Integrable (fun y => k (x, y) * ϕ y) μ ∧ T ϕ x = ∫ y, k (x, y) * ϕ y ∂μ) ∧
      hilbertSchmidtNorm T = (eLpNorm k 2 (μ.prod μ)).toReal ∧
      ∀ k' : X × X → ℂ, MemLp k' 2 (μ.prod μ) →
        (∀ ϕ : Lp ℂ 2 μ, ∀ᵐ x ∂μ, T ϕ x = ∫ y, k' (x, y) * ϕ y ∂μ) →
        k' =ᵐ[μ.prod μ] k := by
  have : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℂ 2 μ) := Lp.SecondCountableTopology
  have : TopologicalSpace.SeparableSpace (Lp ℂ 2 μ) := inferInstance
  have hcount := countable_of_hilbertBasis (chosenHilbertBasis (Lp ℂ 2 μ))
  obtain ⟨K, hK⟩ := exists_kernel_of_summable (chosenHilbertBasis (Lp ℂ 2 μ)) T hT
  refine ⟨K, Lp.memLp K, ?_, ?_, ?_⟩
  · intro ϕ
    rw [← hK]
    exact kernelOp_apply K ϕ
  · unfold hilbertSchmidtNorm
    rw [← hK, (hasSum_norm_sq_kernelOp (chosenHilbertBasis (Lp ℂ 2 μ)) K).tsum_eq,
      Real.sqrt_sq (norm_nonneg _), Lp.norm_def]
  · intro k' hk' hrep
    have hK' : kernelOp (hk'.toLp k') = T := by
      ext1 ϕ
      apply Lp.ext
      filter_upwards [kernelOp_apply (hk'.toLp k') ϕ, hrep ϕ,
        Measure.ae_ae_of_ae_prod hk'.coeFn_toLp] with x h1 h2 h3
      rw [h1.2, h2]
      apply integral_congr_ae
      filter_upwards [h3] with y hy
      rw [hy]
    have h0 : kernelCLM (hk'.toLp k' - K) = 0 := by
      rw [map_sub, kernelCLM_apply, kernelCLM_apply, hK', hK, sub_self]
    have hs := hasSum_norm_sq_kernelOp (chosenHilbertBasis (Lp ℂ 2 μ)) (hk'.toLp k' - K)
    rw [← kernelCLM_apply, h0] at hs
    simp only [zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow] at hs
    have hz : ‖hk'.toLp k' - K‖ ^ 2 = 0 := (hasSum_zero.unique hs).symm
    have hEq : hk'.toLp k' = K := sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hz))
    have := hk'.coeFn_toLp
    rw [hEq] at this
    exact this.symm

