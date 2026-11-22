-- Prove2me | solution 1 for MasulloGRH.adelic_theta_estimates
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T09:44:22.446184+00:00
-- url     : https://prove2.me/submissions/45b63002-a2fd-47cc-8dd1-42c5be4e2fc3

import Definitions.Def_MasulloGRH_AdelicTheta

set_option autoImplicit false

open MasulloGRH NumberField IsDedekindDomain

namespace Aux_MasulloGRH_adelic_theta_estimates

section PoissonPart
open MeasureTheory Real Complex Set Filter Topology
open scoped FourierTransform SchwartzMap

namespace AuxP

variable {ι : Type*} [Fintype ι]

/-- integer point of EuclideanSpace -/
noncomputable def zpt (m : ι → ℤ) : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => (m i : ℝ))

omit [Fintype ι] in
lemma zpt_injective : Function.Injective (zpt (ι := ι)) := by
  intro a b h
  funext i
  have := congrArg (fun v : EuclideanSpace ℝ ι => v i) h
  simpa [zpt] using this

lemma summable_zpt_rpow (k : ℝ) (hk : (Fintype.card ι : ℝ) < k) :
    Summable (fun m : ι → ℤ => ((1 + ‖zpt m‖) ^ k)⁻¹) := by
  let b := (EuclideanSpace.basisFun ι ℝ).toBasis
  let L : Submodule ℤ (EuclideanSpace ℝ ι) := Submodule.span ℤ (Set.range b)
  have hmem : ∀ m : ι → ℤ, zpt m ∈ L := by
    intro m
    rw [Module.Basis.mem_span_iff_repr_mem]
    intro i
    exact ⟨m i, by simp [b, zpt]⟩
  have hrank : Module.finrank ℤ L = Fintype.card ι := by
    rw [Module.finrank_eq_card_basis (b.restrictScalars ℤ)]
  have hs := ZLattice.summable_norm_rpow L (-k) (by rw [hrank]; linarith)
  let j : (ι → ℤ) → L := fun m => ⟨zpt m, hmem m⟩
  have hj : Function.Injective j := by
    intro a c h
    exact zpt_injective (congrArg Subtype.val h)
  have hs' := hs.comp_injective hj
  refine Summable.of_norm_bounded_eventually hs' ?_
  have hfin : {m : ι → ℤ | zpt m = 0}.Finite := by
    refine Set.Finite.subset (Set.finite_singleton 0) ?_
    intro m hm
    simp only [Set.mem_ofPred_eq] at hm
    simp only [Set.mem_singleton_iff]
    exact zpt_injective (by rw [hm]; ext i; simp [zpt])
  filter_upwards [hfin.compl_mem_cofinite] with m hm
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hm
  have hpos : 0 < ‖zpt m‖ := norm_pos_iff.mpr hm
  have hn : ‖j m‖ = ‖zpt m‖ := rfl
  simp only [Function.comp_apply, hn]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg (norm_nonneg _)]
  exact inv_anti₀ (by positivity) (Real.rpow_le_rpow (norm_nonneg _) (by linarith) (by linarith))

lemma schwartz_decay {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : 𝓢(E, ℂ)) (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, (1 + ‖x‖) ^ k * ‖f x‖ ≤ C := by
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f,
    by positivity, fun x => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0)
    le_rfl le_rfl f x
  simpa [norm_iteratedFDeriv_zero] using this

lemma one_add_norm_le (u v : EuclideanSpace ℝ ι) :
    1 + ‖u‖ ≤ (1 + ‖u + v‖) * (1 + ‖v‖) := by
  have : ‖u‖ ≤ ‖u + v‖ + ‖v‖ := by
    calc ‖u‖ = ‖(u + v) - v‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖u + v‖ + ‖v‖ := norm_sub_le _ _
  nlinarith [norm_nonneg (u + v), norm_nonneg v]

/-- uniform bound on translates -/
lemma schwartz_translate_bound (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : EuclideanSpace ℝ ι) (v : EuclideanSpace ℝ ι),
      ‖f (m + v)‖ ≤ C * (1 + ‖v‖) ^ k * ((1 + ‖m‖) ^ k)⁻¹ := by
  obtain ⟨C, hC, h⟩ := schwartz_decay f k
  refine ⟨C, hC, fun m v => ?_⟩
  have h1 := h (m + v)
  have h2 : (1 + ‖m‖) ^ k ≤ (1 + ‖m + v‖) ^ k * (1 + ‖v‖) ^ k := by
    rw [← mul_pow]; gcongr; exact one_add_norm_le m v
  have hp : 0 < (1 + ‖m‖) ^ k := by positivity
  rw [le_mul_inv_iff₀ hp]
  calc ‖f (m + v)‖ * (1 + ‖m‖) ^ k ≤ ‖f (m + v)‖ * ((1 + ‖m + v‖) ^ k * (1 + ‖v‖) ^ k) := by
        gcongr
    _ = ((1 + ‖m + v‖) ^ k * ‖f (m + v)‖) * (1 + ‖v‖) ^ k := by ring
    _ ≤ C * (1 + ‖v‖) ^ k := by gcongr

lemma summable_schwartz_zpt (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (v : EuclideanSpace ℝ ι) :
    Summable (fun m : ι → ℤ => ‖f (zpt m + v)‖) := by
  obtain ⟨C, hC, h⟩ := schwartz_translate_bound f (Fintype.card ι + 1)
  have hs := summable_zpt_rpow (ι := ι) ((Fintype.card ι + 1 : ℕ) : ℝ) (by push_cast; linarith)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (hs.mul_left (C * (1 + ‖v‖) ^ (Fintype.card ι + 1)))
  rw [Real.rpow_natCast]
  exact h _ v


/-- complex exponential phase -/
noncomputable def ex (t : ℝ) : ℂ := Complex.exp (↑(2 * π * t) * Complex.I)

lemma fourierChar_smul (t : ℝ) (z : ℂ) : (𝐞 t) • z = ex t * z := by
  rw [Circle.smul_def, Real.fourierChar_apply]; rfl

lemma ex_add (a b : ℝ) : ex (a + b) = ex a * ex b := by
  simp only [ex, ← Complex.exp_add]; congr 1; push_cast; ring

lemma ex_int (z : ℤ) : ex z = 1 := by
  simp only [ex]
  have : (↑(2 * π * (z : ℝ)) * Complex.I : ℂ) = (z : ℂ) * (2 * π * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma norm_ex (t : ℝ) : ‖ex t‖ = 1 := by
  simp only [ex]; exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_ex : Continuous ex := by
  unfold ex; fun_prop

/-- real-valued integer coordinates -/
def mR (m : ι → ℤ) : ι → ℝ := fun i => (m i : ℝ)

lemma toLp_add_mR (m : ι → ℤ) (x : ι → ℝ) :
    WithLp.toLp 2 (mR m + x) = zpt m + WithLp.toLp 2 x := by
  rfl

lemma inner_zpt (x : ι → ℝ) (n : ι → ℤ) :
    inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ ι) (zpt n) = ∑ i, x i * (n i : ℝ) := by
  simp [zpt, PiLp.inner_apply, mul_comm]

lemma inner_zpt_zpt (m n : ι → ℤ) :
    inner ℝ (zpt m : EuclideanSpace ℝ ι) (zpt n) = ((∑ i, m i * n i : ℤ) : ℝ) := by
  have := inner_zpt (mR m) n
  rw [show (zpt m) = WithLp.toLp 2 (mR m) from rfl, this]
  push_cast; simp [mR]

/-- periodization -/
noncomputable def per (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) (x : ι → ℝ) : ℂ :=
  ∑' m : ι → ℤ, Φ (zpt m + WithLp.toLp 2 x)

lemma per_continuous (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) : Continuous (per Φ) := by
  obtain ⟨C, hC, h⟩ := schwartz_translate_bound Φ (Fintype.card ι + 1)
  have hs := summable_zpt_rpow (ι := ι) ((Fintype.card ι + 1 : ℕ) : ℝ) (by push_cast; linarith)
  rw [continuous_iff_continuousAt]
  intro x0
  set R := ‖(WithLp.toLp 2 x0 : EuclideanSpace ℝ ι)‖ + 1
  let s : Set (ι → ℝ) := {x | ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ < R}
  have hso : IsOpen s := isOpen_lt (by fun_prop) continuous_const
  have hx0 : x0 ∈ s := by simp [s, R]
  have hcont : ContinuousOn (per Φ) s := by
    refine continuousOn_tsum (u := fun m => C * (1 + R) ^ (Fintype.card ι + 1) *
      ((1 + ‖zpt m‖) ^ ((Fintype.card ι + 1 : ℕ) : ℝ))⁻¹) (fun m => ?_) (hs.mul_left _) ?_
    · exact (Φ.continuous.comp (continuous_const.add (by fun_prop))).continuousOn
    · intro m x hx
      have h1 := h (zpt m) (WithLp.toLp 2 x)
      rw [Real.rpow_natCast]
      refine h1.trans ?_
      have : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ≤ R := le_of_lt hx
      gcongr
  exact hcont.continuousAt (hso.mem_nhds hx0)

lemma per_periodic (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) (m0 : ι → ℤ) (x : ι → ℝ) :
    per Φ (mR m0 + x) = per Φ x := by
  unfold per
  conv_rhs => rw [← (Equiv.addRight m0).tsum_eq]
  congr 1; funext m
  congr 1
  rw [toLp_add_mR, ← add_assoc]
  congr 1
  ext i; simp [zpt]

/-- the quotient map to the torus -/
noncomputable def qT (x : ι → ℝ) : UnitAddTorus ι := fun i => (x i : UnitAddCircle)

lemma qT_isQuotientMap : Topology.IsQuotientMap (qT (ι := ι)) :=
  (IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk).isQuotientMap

lemma per_factors (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) : Function.FactorsThrough (per Φ) qT := by
  intro a b hab
  have hi : ∀ i, ∃ k : ℤ, b i = (k : ℝ) + a i := by
    intro i
    have h1 := congrFun hab i
    simp only [qT] at h1
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp h1)
    exact ⟨k, by simp at hk; linarith⟩
  choose k hk using hi
  have : b = mR k + a := by funext i; simp [mR, hk i]
  rw [this, per_periodic]

/-- the periodization as a function on the torus -/
noncomputable def perT (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) : C(UnitAddTorus ι, ℂ) :=
  Topology.IsQuotientMap.lift (f := ⟨qT, qT_isQuotientMap.continuous⟩) (qT_isQuotientMap (ι := ι)) ⟨per Φ, per_continuous Φ⟩ (per_factors Φ)

lemma perT_qT (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) (x : ι → ℝ) : perT Φ (qT x) = per Φ x :=
  DFunLike.congr_fun (Topology.IsQuotientMap.lift_comp (f := ⟨qT, qT_isQuotientMap.continuous⟩)
    (qT_isQuotientMap (ι := ι)) ⟨per Φ, per_continuous Φ⟩ (per_factors Φ)) x

lemma mFourier_qT (n : ι → ℤ) (x : ι → ℝ) :
    UnitAddTorus.mFourier (-n) (qT x) = ex (-(∑ i, x i * (n i : ℝ))) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, qT, Pi.neg_apply, fourier_coe_apply]
  rw [← Complex.exp_sum]
  simp only [ex]
  congr 1
  push_cast
  rw [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring


omit [Fintype ι] in
lemma mem_span_mR (m : ι → ℤ) [Finite ι] :
    mR m ∈ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) := by
  rw [Module.Basis.mem_span_iff_repr_mem]
  intro i
  exact ⟨m i, by simp [mR]⟩

/-- the integer lattice equivalence -/
noncomputable def eL : (ι → ℤ) ≃ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup :=
  Equiv.ofBijective (fun m => ⟨mR m, mem_span_mR m⟩) (by
    constructor
    · intro a b h
      funext i
      have := congrFun (congrArg Subtype.val h) i
      simpa [mR] using this
    · rintro ⟨γ, hγ⟩
      have h := (Module.Basis.mem_span_iff_repr_mem ℤ (Pi.basisFun ℝ ι) γ).mp hγ
      choose m hm using h
      refine ⟨m, ?_⟩
      apply Subtype.ext
      funext i
      simpa [mR] using hm i)

lemma eL_coe (m : ι → ℤ) : ((eL m : (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup) :
    ι → ℝ) = mR m := rfl

lemma integrable_comp_toLp (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    Integrable (fun y : ι → ℝ => Φ (WithLp.toLp 2 y)) :=
  ((PiLp.volume_preserving_toLp ι).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding).mpr Φ.integrable

lemma fourier_zpt (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) (n : ι → ℤ) :
    𝓕 (⇑Φ) (zpt n) = ∫ y : ι → ℝ, ex (-(∑ i, y i * (n i : ℝ))) * Φ (WithLp.toLp 2 y) := by
  rw [Real.fourier_eq]
  rw [← (PiLp.volume_preserving_toLp ι).integral_comp
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding]
  congr 1; funext y
  rw [fourierChar_smul, inner_zpt]

lemma ex_shift (m n : ι → ℤ) (x : ι → ℝ) :
    ex (-(∑ i, (mR m + x) i * (n i : ℝ))) = ex (-(∑ i, x i * (n i : ℝ))) := by
  have : -(∑ i, (mR m + x) i * (n i : ℝ)) = ((-(∑ i, m i * n i) : ℤ) : ℝ) +
      (-(∑ i, x i * (n i : ℝ))) := by
    simp only [Pi.add_apply, mR, add_mul, Finset.sum_add_distrib]; push_cast; ring
  rw [this, ex_add, ex_int, one_mul]

lemma fourier_zpt_tsum (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) (n : ι → ℤ) :
    𝓕 (⇑Φ) (zpt n) = ∑' m : ι → ℤ, ∫ x in Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1),
      ex (-(∑ i, x i * (n i : ℝ))) * Φ (zpt m + WithLp.toLp 2 x) := by
  have hFD := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ ι) (volume : Measure (ι → ℝ))
  rw [ZSpan.fundamentalDomain_pi_basisFun] at hFD
  have hg : Integrable (fun y : ι → ℝ => ex (-(∑ i, y i * (n i : ℝ))) * Φ (WithLp.toLp 2 y)) := by
    refine (integrable_comp_toLp Φ).bdd_mul (c := 1) ?_ ?_
    · exact (continuous_ex.comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y => (norm_ex _).le
  have : Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))).toAddSubgroup :=
    Function.Injective.countable (eL (ι := ι)).symm.injective
  rw [fourier_zpt, hFD.integral_eq_tsum'' _ hg, ← (eL (ι := ι)).tsum_eq]
  congr 1; funext m
  congr 1; funext x
  rw [AddSubgroup.vadd_def, vadd_eq_add, eL_coe, ex_shift, toLp_add_mR]


lemma cube_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1),
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ≤ B := by
  have hK : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (f := fun x : ι → ℝ => ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖) (by fun_prop)
  refine ⟨max B 0, le_max_right _ _, fun x hx => ?_⟩
  have := hB x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at this
  exact this.trans (le_max_left _ _)

lemma coeff_eq (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (perT Φ) n = 𝓕 (⇑Φ) (zpt n) := by
  rw [fourier_zpt_tsum, UnitAddTorus.mFourierCoeff_eq_integral _ n 0]
  have hS : {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} =
      Set.pi Set.univ (fun _ : ι => Set.Ioc (0 : ℝ) 1) := by
    ext x; simp
  rw [hS]
  have hae : (Set.pi Set.univ (fun _ : ι => Set.Ioc (0 : ℝ) 1)) =ᵐ[volume]
      (Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1)) :=
    (Measure.pi_Ioc_ae_eq_pi_Icc (μ := fun _ : ι => (volume : Measure ℝ))).trans
      (Measure.pi_Ico_ae_eq_pi_Icc (μ := fun _ : ι => (volume : Measure ℝ))).symm
  rw [setIntegral_congr_set hae]
  set S := Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1)
  have hSK : S ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) :=
    Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self
  have hK : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hvol : volume S = 1 := by
    simp [S, volume_pi_pi, Real.volume_Ico]
  have hvol' : volume S < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  let F : (ι → ℤ) → (ι → ℝ) → ℂ := fun m x =>
    ex (-(∑ i, x i * (n i : ℝ))) * Φ (zpt m + WithLp.toLp 2 x)
  have hFc : ∀ m, Continuous (F m) := fun m =>
    (continuous_ex.comp (by fun_prop)).mul (Φ.continuous.comp (continuous_const.add (by fun_prop)))
  have hint : ∀ m, Integrable (F m) (volume.restrict S) := fun m =>
    ((hFc m).continuousOn.integrableOn_compact hK).mono_set hSK
  obtain ⟨C, hC, h⟩ := schwartz_translate_bound Φ (Fintype.card ι + 1)
  obtain ⟨B, hB0, hB⟩ := cube_bound (ι := ι)
  have hs := summable_zpt_rpow (ι := ι) ((Fintype.card ι + 1 : ℕ) : ℝ) (by push_cast; linarith)
  have hbd : ∀ m, ∀ x ∈ S, ‖F m x‖ ≤ C * (1 + B) ^ (Fintype.card ι + 1) *
      ((1 + ‖zpt m‖) ^ ((Fintype.card ι + 1 : ℕ) : ℝ))⁻¹ := by
    intro m x hx
    simp only [F, norm_mul, norm_ex, one_mul]
    rw [Real.rpow_natCast]
    refine (h (zpt m) (WithLp.toLp 2 x)).trans ?_
    have := hB x (hSK hx)
    gcongr
  have hsum : Summable fun m => ∫ x, ‖F m x‖ ∂(volume.restrict S) := by
    refine Summable.of_norm_bounded (hs.mul_left (C * (1 + B) ^ (Fintype.card ι + 1))) ?_
    intro m
    have := norm_setIntegral_le_of_norm_le_const (f := fun x => ‖F m x‖) hvol'
      (fun x hx => by rw [norm_norm]; exact hbd m x hx)
    simp only [Measure.real, hvol, ENNReal.toReal_one, mul_one] at this
    simpa using this
  rw [integral_tsum_of_summable_integral_norm hint hsum]
  refine setIntegral_congr_fun (measurableSet_pi Set.countable_univ.to_subtype |>.mpr
    (Or.inl fun _ _ => measurableSet_Ico)) ?_
  intro x _
  simp only [F]
  rw [show (fun i => ((x i : ℝ) : UnitAddCircle)) = qT x from rfl, mFourier_qT, perT_qT, per,
    smul_eq_mul, ← tsum_mul_left]

theorem poisson (Φ : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    Summable (fun m : ι → ℤ => Φ (zpt m)) ∧ Summable (fun n : ι → ℤ => 𝓕 (⇑Φ) (zpt n)) ∧
    ∑' m : ι → ℤ, Φ (zpt m) = ∑' n : ι → ℤ, 𝓕 (⇑Φ) (zpt n) := by
  have h1 : Summable (fun m : ι → ℤ => Φ (zpt m)) :=
    Summable.of_norm (by simpa using summable_schwartz_zpt Φ 0)
  have h2 : Summable (fun n : ι → ℤ => 𝓕 (⇑Φ) (zpt n)) := by
    have := summable_schwartz_zpt (𝓕 Φ) 0
    simp only [add_zero, SchwartzMap.fourier_coe] at this
    exact Summable.of_norm this
  refine ⟨h1, h2, ?_⟩
  have hc : Summable (UnitAddTorus.mFourierCoeff (perT Φ)) := by
    have : UnitAddTorus.mFourierCoeff (perT Φ) = fun n => 𝓕 (⇑Φ) (zpt n) := funext (coeff_eq Φ)
    rw [this]; exact h2
  have := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hc 0
  have h0 : (0 : UnitAddTorus ι) = qT 0 := by funext i; simp [qT]
  rw [h0, perT_qT] at this
  simp only [per] at this
  have hz : (WithLp.toLp 2 (0 : ι → ℝ) : EuclideanSpace ℝ ι) = 0 := rfl
  simp only [hz, add_zero] at this
  rw [← this.tsum_eq]
  refine tsum_congr fun n => ?_
  rw [coeff_eq]
  simp [UnitAddTorus.mFourier, qT, fourier_eval_zero]

end AuxP

end PoissonPart

namespace AuxA

open Filter Topology
open scoped WithZero

variable {F : Type*} [Field F] [NumberField F]

lemma val_coe (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

lemma val_int_le_one (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)) ≤ 1 := by
  rw [val_coe]; exact v.valuation_le_one r

/-- local approximation by elements of `F` -/
lemma exists_approx1 (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ a : F, Valued.v (x - algebraMap F (v.adicCompletion F) a) < 1 := by
  have hn : {z : v.adicCompletion F | Valued.v (z - x) < 1} ∈ 𝓝 x := by
    refine Valued.mem_nhds.mpr ⟨1, ?_⟩
    intro z hz
    simpa only [Set.mem_ofPred_eq, Units.val_one, Valuation.restrict_lt_iff_lt_embedding,
      map_one] using hz
  obtain ⟨a, ha⟩ := (v.denseRange_algebraMap F).mem_nhds hn
  refine ⟨a, ?_⟩
  have : Valued.v (algebraMap F (v.adicCompletion F) a - x) < 1 := ha
  rw [← Valuation.map_neg, neg_sub]
  exact this

lemma exists_approx (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) (d : F) (hd : d ≠ 0) :
    ∃ a : F, Valued.v (x - algebraMap F (v.adicCompletion F) a) <
      Valued.v (algebraMap F (v.adicCompletion F) d) := by
  set D := algebraMap F (v.adicCompletion F) d
  have hD : D ≠ 0 := (map_ne_zero _).mpr hd
  obtain ⟨a, ha⟩ := exists_approx1 v (x * D⁻¹)
  refine ⟨a * d, ?_⟩
  have : x - algebraMap F (v.adicCompletion F) (a * d) =
      (x * D⁻¹ - algebraMap F (v.adicCompletion F) a) * D := by
    rw [map_mul, sub_mul, mul_assoc, inv_mul_cancel₀ hD, mul_one]
  rw [this, map_mul]
  have hD' : 0 < Valued.v D := by
    rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).mpr hD
  calc Valued.v (x * D⁻¹ - algebraMap F (v.adicCompletion F) a) * Valued.v D
      < 1 * Valued.v D := mul_lt_mul_of_pos_right ha hD'
    _ = Valued.v D := one_mul _

/-- local approximation of integral elements by global integers -/
lemma exists_int_approx (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (hx : Valued.v x ≤ 1) (d : 𝓞 F) (hd : d ≠ 0) :
    ∃ r : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)) <
      Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d)) := by
  have hd' : algebraMap (𝓞 F) F d ≠ 0 := by
    simpa using hd
  obtain ⟨a, ha⟩ := exists_approx v x _ hd'
  have hγ : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d)) ≤ 1 :=
    val_int_le_one v d
  have ha1 : v.valuation F a ≤ 1 := by
    rw [← val_coe]
    have : algebraMap F (v.adicCompletion F) a = x - (x - algebraMap F (v.adicCompletion F) a) := by
      ring
    rw [this]
    exact Valuation.map_sub_le _ hx (ha.le.trans hγ)
  have hne : v.valuation F (algebraMap (𝓞 F) F d) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact hd'
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer ha1 (Units.mk0 _ hne)
  refine ⟨r, ?_⟩
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) a -
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)) <
      Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d)) := by
    rw [← Valuation.map_neg, neg_sub, ← map_sub, val_coe, val_coe]
    exact hr
  have : x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r) =
      (x - algebraMap F (v.adicCompletion F) a) + (algebraMap F (v.adicCompletion F) a -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)) := by
    ring
  rw [this]
  exact Valuation.map_add_lt _ ha h2

/-- an element of `F` integral at every finite place is an integer -/
lemma int_of_val_le_one (ξ : F) (h : ∀ v : HeightOneSpectrum (𝓞 F),
    Valued.v (algebraMap F (v.adicCompletion F) ξ) ≤ 1) :
    ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = ξ := by
  have := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F ξ
    (fun v => by rw [← val_coe]; exact h v)
  obtain ⟨r, hr⟩ := this
  exact ⟨r, hr⟩


lemma fin_algebraMap_apply (k : F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) v = algebraMap F (v.adicCompletion F) k := rfl

lemma val_d_le (v : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d)) ≤ 1 :=
  val_int_le_one v d

/-- strong approximation away from the archimedean places: every finite adele is congruent to an
element of `F` modulo the integral adeles -/
lemma exists_sub_int (z : FiniteAdeleRing (𝓞 F) F) :
    ∃ ξ : F, ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (z v - algebraMap F (v.adicCompletion F) ξ) ≤ 1 := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ Valued.v (z v) ≤ 1}.Finite := by
    have := z.2
    rw [Filter.eventually_cofinite] at this
    refine this.subset ?_
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv ⊢
    intro h
    exact hv ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp h)
  set S := hfin.toFinset
  -- local approximations by fractions
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ p q : 𝓞 F, q ≠ 0 ∧
      Valued.v (z v - algebraMap F (v.adicCompletion F)
        (algebraMap (𝓞 F) F p / algebraMap (𝓞 F) F q)) < 1 := by
    intro v
    obtain ⟨a, ha⟩ := exists_approx1 v (z v)
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
    exact ⟨p, q, nonZeroDivisors.ne_zero hq, ha⟩
  choose p q hq hpq using hloc
  set d : 𝓞 F := ∏ v ∈ S, q v with hd_def
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => hq v
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := by simpa using hd
  -- `d z` is integral
  have hdz : ∀ v, Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d) * z v) ≤ 1 := by
    intro v
    by_cases hv : v ∈ S
    · have hS : d = q v * ∏ w ∈ S.erase v, q w := by
        rw [hd_def, ← Finset.mul_prod_erase S q hv]
      set e : 𝓞 F := ∏ w ∈ S.erase v, q w
      have hqv : algebraMap (𝓞 F) F (q v) ≠ 0 := by simpa using hq v
      have hsplit : algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d) * z v =
          algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d) *
            (z v - algebraMap F (v.adicCompletion F)
              (algebraMap (𝓞 F) F (p v) / algebraMap (𝓞 F) F (q v))) +
          algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (e * p v)) := by
        have hk : algebraMap (𝓞 F) F d * (algebraMap (𝓞 F) F (p v) / algebraMap (𝓞 F) F (q v)) =
            algebraMap (𝓞 F) F (e * p v) := by
          rw [hS, map_mul, map_mul]; field_simp
        rw [mul_sub, ← map_mul, hk]; ring
      rw [hsplit]
      refine Valuation.map_add_le _ ?_ (val_int_le_one v _)
      rw [map_mul]
      calc Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d)) *
            Valued.v (z v - algebraMap F (v.adicCompletion F)
              (algebraMap (𝓞 F) F (p v) / algebraMap (𝓞 F) F (q v)))
          ≤ 1 * 1 := mul_le_mul' (val_d_le v d) (hpq v).le
        _ = 1 := one_mul 1
    · have hzv : Valued.v (z v) ≤ 1 := by
        by_contra h
        exact hv (hfin.mem_toFinset.mpr h)
      rw [map_mul]
      calc _ ≤ (1 : ℤᵐ⁰) * 1 := mul_le_mul' (val_d_le v d) hzv
        _ = 1 := one_mul 1
  -- the finite set of primes dividing `d`
  have hTfin : {v : HeightOneSpectrum (𝓞 F) | d ∈ v.asIdeal}.Finite := by
    refine (HeightOneSpectrum.Support.finite (𝓞 F) (algebraMap (𝓞 F) F d)⁻¹).subset ?_
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv
    simp only [HeightOneSpectrum.Support, Set.mem_ofPred_eq, map_inv₀]
    have h1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v d).mpr hv
    have h0 : v.valuation F (algebraMap (𝓞 F) F d) ≠ 0 := (Valuation.ne_zero_iff _).mpr hdF
    exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr h0, h1⟩
  set T := hTfin.toFinset
  -- local integer approximations of `d z` at the primes dividing `d`
  have hr : ∀ v : HeightOneSpectrum (𝓞 F), ∃ r : 𝓞 F,
      Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d) * z v -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)) <
      Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d)) :=
    fun v => exists_int_approx v _ (hdz v) d hd
  choose r hr using hr
  obtain ⟨c, hc⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v => v.asIdeal) (fun v => multiplicity v.asIdeal (Ideal.span {d}))
    (fun v _ => Ideal.prime_of_isPrime v.ne_bot v.isPrime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => r v)
  refine ⟨algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F d, fun v => ?_⟩
  set D := algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d)
  have hD : D ≠ 0 := (map_ne_zero _).mpr hdF
  have hD0 : 0 < Valued.v D := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hD)
  have key : Valued.v (D * z v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F c)) ≤
      Valued.v D := by
    by_cases hv : v ∈ T
    · have hcv := hc v hv
      have h1 : v.intValuation (c - r v) ≤ v.intValuation d := by
        rw [v.intValuation_eq_exp_neg_multiplicity hd]
        exact (v.intValuation_le_pow_iff_mem _ _).mpr hcv
      have h2 : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (r v)) -
          algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F c)) ≤ Valued.v D := by
        rw [← map_sub, ← map_sub, ← Valuation.map_neg, ← map_neg, ← map_neg, neg_sub, val_coe,
          val_coe, HeightOneSpectrum.valuation_of_algebraMap,
          HeightOneSpectrum.valuation_of_algebraMap]
        exact h1
      have : D * z v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F c) =
          (D * z v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (r v))) +
          (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (r v)) -
            algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F c)) := by ring
      rw [this]
      exact Valuation.map_add_le _ (hr v).le h2
    · have hdv : d ∉ v.asIdeal := fun h => hv (hTfin.mem_toFinset.mpr h)
      have hD1 : Valued.v D = 1 := by
        simp only [D]
        rw [val_coe]
        exact (HeightOneSpectrum.valuation_eq_one_iff_notMem v).mpr hdv
      rw [hD1]
      exact Valuation.map_sub_le _ (hdz v) (val_int_le_one v c)
  have : z v - algebraMap F (v.adicCompletion F)
      (algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F d) =
      (D * z v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F c)) * D⁻¹ := by
    rw [map_div₀]
    simp only [D] at hD ⊢
    field_simp
  rw [this, map_mul, map_inv₀]
  calc _ ≤ Valued.v D * (Valued.v D)⁻¹ := mul_le_mul_left key _
    _ = 1 := mul_inv_cancel₀ hD0.ne'


/-! ### the archimedean trace and the standard character -/

/-- archimedean trace `∑_w Tr_{F_w/ℝ}` -/
noncomputable def trI (y : InfiniteAdeleRing F) : ℝ :=
  ∑ w : InfinitePlace F, (w.mult : ℝ) * (InfinitePlace.Completion.extensionEmbedding w (y w)).re

lemma trI_add (a b : InfiniteAdeleRing F) : trI (a + b) = trI a + trI b := by
  simp only [trI, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  change (w.mult : ℝ) * (InfinitePlace.Completion.extensionEmbedding w (a w + b w)).re = _
  rw [map_add, Complex.add_re]; ring

lemma trI_zero : trI (0 : InfiniteAdeleRing F) = 0 := by
  have := trI_add (0 : InfiniteAdeleRing F) 0
  simp only [add_zero] at this
  linarith

lemma trI_neg (a : InfiniteAdeleRing F) : trI (-a) = -trI a := by
  have := trI_add a (-a)
  rw [add_neg_cancel, trI_zero] at this
  linarith

lemma trI_sub (a b : InfiniteAdeleRing F) : trI (a - b) = trI a - trI b := by
  rw [sub_eq_add_neg, trI_add, trI_neg, sub_eq_add_neg]

lemma continuous_trI : Continuous (trI (F := F)) := by
  unfold trI
  refine continuous_finsetSum _ fun w _ => continuous_const.mul ?_
  exact Complex.continuous_re.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w))

lemma ext_coe (w : InfinitePlace F) (x : F) :
    InfinitePlace.Completion.extensionEmbedding w ((algebraMap F (InfiniteAdeleRing F) x) w) =
      w.embedding x := by
  rw [InfiniteAdeleRing.algebraMap_apply]
  exact InfinitePlace.Completion.extensionEmbedding_coe w _

lemma trI_algebraMap (x : F) : trI (algebraMap F (InfiniteAdeleRing F) x) =
    ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  classical
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ) (x := x)
  have h2 : (∑ σ : F →ₐ[ℚ] ℂ, σ x) = ∑ φ : F →+* ℂ, φ x :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ).symm _ _ (fun σ => by
      simp [RingHom.equivRatAlgHom])
  rw [h2, ← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun φ => φ x)] at h
  have h3 : ∀ w : InfinitePlace F, (∑ φ ∈ ({φ | InfinitePlace.mk φ = w} : Finset (F →+* ℂ)),
      φ x).re = (w.mult : ℝ) * (w.embedding x).re := by
    intro w
    rw [Complex.re_sum]
    have : ∀ φ ∈ ({φ | InfinitePlace.mk φ = w} : Finset (F →+* ℂ)),
        (φ x).re = (w.embedding x).re := by
      intro φ hφ
      have hφ' : InfinitePlace.mk φ = InfinitePlace.mk w.embedding := by
        rw [InfinitePlace.mk_embedding]; exact (Finset.mem_filter.mp hφ).2
      rcases InfinitePlace.mk_eq_iff.mp hφ' with h | h
      · rw [h]
      · rw [← h, NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
    rw [Finset.sum_congr rfl this, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]
  have h4 := congrArg Complex.re h
  rw [Complex.re_sum] at h4
  simp only [h3] at h4
  rw [trI]
  simp only [ext_coe]
  rw [← h4]
  simp

lemma trace_int (r : 𝓞 F) : ∃ n : ℤ, Algebra.trace ℚ F (algebraMap (𝓞 F) F r) = n := by
  have hint : IsIntegral ℤ (Algebra.trace ℚ F (algebraMap (𝓞 F) F r)) :=
    Algebra.isIntegral_trace (r.2)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨n, by rw [← hn]; simp⟩

/-- `exp(-2πi tr_∞ y)` -/
noncomputable def Ie (y : InfiniteAdeleRing F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * (trI y : ℂ))

lemma Ie_add (a b : InfiniteAdeleRing F) : Ie (a + b) = Ie a * Ie b := by
  simp only [Ie, trI_add, ← Complex.exp_add]; congr 1; push_cast; ring

lemma Ie_int (r : 𝓞 F) : Ie (algebraMap F (InfiniteAdeleRing F) (algebraMap (𝓞 F) F r)) = 1 := by
  obtain ⟨n, hn⟩ := trace_int r
  simp only [Ie, trI_algebraMap, hn]
  have : (-(2 * Real.pi * Complex.I) * (((n : ℚ) : ℝ) : ℂ)) = ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma continuous_Ie : Continuous (Ie (F := F)) := by
  unfold Ie
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_trI))

lemma norm_Ie (y : InfiniteAdeleRing F) : ‖Ie y‖ = 1 := by
  unfold Ie
  have : (-(2 * Real.pi * Complex.I) * (trI y : ℂ)) = ((-(2 * Real.pi * trI y) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this]; exact Complex.norm_exp_ofReal_mul_I _


/-! ### the standard character -/

lemma adele_fst_alg (ξ : F) : (algebraMap F (AdeleRing (𝓞 F) F) ξ).1 =
    algebraMap F (InfiniteAdeleRing F) ξ := rfl

lemma adele_snd_alg (ξ : F) : (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 =
    algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ := rfl

lemma isIntegral_iff (y : AdeleRing (𝓞 F) F) :
    IsIntegralAdele y ↔ ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (y.2 v) ≤ 1 := by
  unfold IsIntegralAdele
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers]

lemma decomp_exists (x : AdeleRing (𝓞 F) F) :
    ∃ (y : AdeleRing (𝓞 F) F) (ξ : F), IsIntegralAdele y ∧ x = y + algebraMap F _ ξ := by
  obtain ⟨ξ, hξ⟩ := exists_sub_int x.2
  refine ⟨x - algebraMap F _ ξ, ξ, ?_, by ring⟩
  rw [isIntegral_iff]
  intro v
  exact hξ v

lemma int_of_diff (y y' : AdeleRing (𝓞 F) F) (ξ ξ' : F) (hy : IsIntegralAdele y)
    (hy' : IsIntegralAdele y') (h : y + algebraMap F _ ξ = y' + algebraMap F _ ξ') :
    ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = ξ' - ξ ∧
      y.1 = y'.1 + algebraMap F (InfiniteAdeleRing F) (algebraMap (𝓞 F) F r) := by
  have hdiff : y - y' = algebraMap F _ (ξ' - ξ) := by
    rw [map_sub]; linear_combination h
  rw [isIntegral_iff] at hy hy'
  obtain ⟨r, hr⟩ := int_of_val_le_one (ξ' - ξ) (fun v => by
    have : (y - y').2 v = (algebraMap F (AdeleRing (𝓞 F) F) (ξ' - ξ)).2 v := by rw [hdiff]
    rw [← fin_algebraMap_apply, ← adele_snd_alg, ← this]
    change Valued.v (y.2 v - y'.2 v) ≤ 1
    exact Valuation.map_sub_le _ (hy v) (hy' v))
  refine ⟨r, hr, ?_⟩
  have : (y - y').1 = (algebraMap F (AdeleRing (𝓞 F) F) (ξ' - ξ)).1 := by rw [hdiff]
  rw [hr, ← adele_fst_alg, ← this]
  change y.1 = y'.1 + (y.1 - y'.1)
  ring

lemma std_eq_Ie (x : AdeleRing (𝓞 F) F) (h : ∃ y : AdeleRing (𝓞 F) F, IsIntegralAdele y ∧
      ∃ ξ : F, x = y + algebraMap F (AdeleRing (𝓞 F) F) ξ) :
    stdAdelicCharacter x = Ie h.choose.1 := by
  unfold stdAdelicCharacter
  rw [dif_pos h]
  unfold Ie trI
  congr 2
  push_cast
  rfl

lemma psi_eq (y : AdeleRing (𝓞 F) F) (ξ : F) (hy : IsIntegralAdele y) :
    stdAdelicCharacter (y + algebraMap F _ ξ) = Ie y.1 := by
  have h : ∃ y' : AdeleRing (𝓞 F) F, IsIntegralAdele y' ∧
      ∃ ξ' : F, y + algebraMap F _ ξ = y' + algebraMap F (AdeleRing (𝓞 F) F) ξ' := ⟨y, hy, ξ, rfl⟩
  rw [std_eq_Ie _ h]
  obtain ⟨hy0, ξ0, hξ0⟩ := h.choose_spec
  obtain ⟨r, -, hr⟩ := int_of_diff _ _ _ _ hy0 hy hξ0.symm
  rw [hr, Ie_add, Ie_int, mul_one]

lemma psi_add (a b : AdeleRing (𝓞 F) F) :
    stdAdelicCharacter (a + b) = stdAdelicCharacter a * stdAdelicCharacter b := by
  obtain ⟨y, ξ, hy, rfl⟩ := decomp_exists a
  obtain ⟨y', ξ', hy', rfl⟩ := decomp_exists b
  have : y + algebraMap F _ ξ + (y' + algebraMap F _ ξ') = (y + y') + algebraMap F _ (ξ + ξ') := by
    rw [map_add]; ring
  rw [this, psi_eq _ _ (by
    rw [isIntegral_iff] at hy hy' ⊢
    intro v
    exact Valuation.map_add_le _ (hy v) (hy' v)), psi_eq _ _ hy, psi_eq _ _ hy']
  exact Ie_add _ _

lemma psi_zero_int (y : AdeleRing (𝓞 F) F) (hy : IsIntegralAdele y) :
    stdAdelicCharacter y = Ie y.1 := by
  have := psi_eq y 0 hy
  rwa [map_zero, add_zero] at this

lemma psi_algebraMap (ξ : F) : stdAdelicCharacter (algebraMap F (AdeleRing (𝓞 F) F) ξ) = 1 := by
  have := psi_eq 0 ξ (by
    rw [isIntegral_iff]; intro v
    show Valued.v (0 : v.adicCompletion F) ≤ 1
    simp)
  rw [zero_add] at this
  rw [this, show (0 : AdeleRing (𝓞 F) F).1 = 0 from rfl]
  simp [Ie, trI_zero]

lemma norm_psi (x : AdeleRing (𝓞 F) F) : ‖stdAdelicCharacter x‖ = 1 := by
  obtain ⟨y, ξ, hy, rfl⟩ := decomp_exists x
  rw [psi_eq _ _ hy, norm_Ie]


/-! ### coordinates on the infinite adeles -/

open InfinitePlace InfinitePlace.Completion in
open scoped Classical in
/-- `F_∞ ≅ ℝ^{r₁} × ℂ^{r₂}` as a homeomorphism -/
noncomputable def eH : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
  (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace F => IsReal v)
      (fun v : InfinitePlace F => v.Completion)).trans
    (Homeomorph.prodCongr
      (Homeomorph.piCongrRight fun v => (isometryEquivRealOfIsReal v.2).toHomeomorph)
      ((Homeomorph.piCongrRight fun v => (isometryEquivComplexOfIsComplex
          ((not_isReal_iff_isComplex.1 v.2))).toHomeomorph).trans
        (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
          (Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex)))))

omit [NumberField F] in
lemma eH_apply (y : InfiniteAdeleRing F) :
    eH y = InfiniteAdeleRing.ringEquiv_mixedSpace F y := rfl

lemma eH_symm_apply (z : mixedEmbedding.mixedSpace F) :
    eH.symm z = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z := by
  apply eH.injective
  rw [Homeomorph.apply_symm_apply, eH_apply, RingEquiv.apply_symm_apply]

/-- the index type of an integral basis -/
abbrev Ix (F : Type*) [Field F] [NumberField F] := Module.Free.ChooseBasisIndex ℤ (𝓞 F)

/-- linear coordinates `ℝ^d ≅ F_∞` adapted to the integers -/
noncomputable def LH : EuclideanSpace ℝ (Ix F) ≃ₜ InfiniteAdeleRing F :=
  ((EuclideanSpace.equiv (Ix F) ℝ).toHomeomorph.trans
    (mixedEmbedding.latticeBasis F).equivFun.symm.toContinuousLinearEquiv.toHomeomorph).trans
    eH.symm

lemma LH_apply (t : EuclideanSpace ℝ (Ix F)) :
    LH t = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      ((mixedEmbedding.latticeBasis F).equivFun.symm (EuclideanSpace.equiv (Ix F) ℝ t)) := by
  simp only [LH, Homeomorph.trans_apply, eH_symm_apply]
  rfl

lemma LH_add (a b : EuclideanSpace ℝ (Ix F)) : LH (a + b) = LH a + LH b := by
  simp only [LH_apply, map_add]

lemma LH_zero : LH (0 : EuclideanSpace ℝ (Ix F)) = 0 := by
  simp only [LH_apply, map_zero]

/-- `LH` as an additive equivalence -/
noncomputable def LHa : EuclideanSpace ℝ (Ix F) ≃+ InfiniteAdeleRing F :=
  { LH.toEquiv with map_add' := LH_add }

lemma LH_neg (a : EuclideanSpace ℝ (Ix F)) : LH (-a) = -LH a := map_neg (LHa (F := F)) a

lemma LH_sub (a b : EuclideanSpace ℝ (Ix F)) : LH (a - b) = LH a - LH b := map_sub (LHa (F := F)) a b

lemma LH_nsmul (n : ℕ) (a : EuclideanSpace ℝ (Ix F)) : LH (n • a) = n • LH a :=
  map_nsmul (LHa (F := F)) n a

lemma LH_zsmul (n : ℤ) (a : EuclideanSpace ℝ (Ix F)) : LH (n • a) = n • LH a :=
  map_zsmul (LHa (F := F)) n a

lemma LH_symm_add (a b : InfiniteAdeleRing F) : LH.symm (a + b) = LH.symm a + LH.symm b :=
  map_add (LHa (F := F)).symm a b

lemma LH_symm_sub (a b : InfiniteAdeleRing F) : LH.symm (a - b) = LH.symm a - LH.symm b :=
  map_sub (LHa (F := F)).symm a b

/-- the element `∑ mᵢ bᵢ` of `F` -/
noncomputable def emb (m : Ix F → ℤ) : F := ∑ i, (m i) • integralBasis F i

lemma LH_zpt (m : Ix F → ℤ) :
    LH (AuxP.zpt m) = algebraMap F (InfiniteAdeleRing F) (emb m) := by
  rw [LH_apply]
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
  rw [RingEquiv.apply_symm_apply, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rw [Module.Basis.equivFun_symm_apply]
  simp only [emb, map_sum, map_zsmul, mixedEmbedding.latticeBasis_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [AuxP.zpt, EuclideanSpace.equiv, integralBasis_apply]
  exact Int.cast_smul_eq_zsmul ℝ (m i) _

lemma emb_int (m : Ix F → ℤ) :
    emb m = algebraMap (𝓞 F) F (∑ i, (m i) • RingOfIntegers.basis F i) := by
  simp [emb, map_sum, integralBasis_apply]

lemma exists_emb (r : 𝓞 F) : ∃ m : Ix F → ℤ, emb m = algebraMap (𝓞 F) F r := by
  refine ⟨fun i => (RingOfIntegers.basis F).repr r i, ?_⟩
  rw [emb_int]
  congr 1
  conv_rhs => rw [← (RingOfIntegers.basis F).sum_repr r]

lemma emb_injective : Function.Injective (emb (F := F)) := by
  intro a b h
  have h' : (∑ i, (a i : ℚ) • integralBasis F i) = ∑ i, (b i : ℚ) • integralBasis F i := by
    simpa [emb, Int.cast_smul_eq_zsmul] using h
  have := (integralBasis F).equivFun.symm.injective (a₁ := fun i => (a i : ℚ))
    (a₂ := fun i => (b i : ℚ)) (by simpa [Module.Basis.equivFun_symm_apply] using h')
  funext i
  have := congrFun this i
  exact_mod_cast this

lemma emb_add (a b : Ix F → ℤ) : emb (a + b) = emb a + emb b := by
  simp [emb, add_smul, Finset.sum_add_distrib]

lemma emb_smul (c : ℤ) (a : Ix F → ℤ) : emb (c • a) = (c : F) * emb a := by
  simp [emb, Finset.mul_sum, mul_smul, zsmul_eq_mul]


/-! ### the trace pairing in coordinates -/

lemma continuous_LH : Continuous (LH (F := F)) := LH.continuous

/-- `t ↦ tr_∞(LH t · η)` as an additive map -/
noncomputable def trLin (η : F) : EuclideanSpace ℝ (Ix F) →+ ℝ where
  toFun t := trI (LH t * algebraMap F (InfiniteAdeleRing F) η)
  map_zero' := by simp [LH_zero, trI_zero]
  map_add' a b := by simp [LH_add, add_mul, trI_add]

lemma continuous_trLin (η : F) : Continuous (trLin η) :=
  continuous_trI.comp ((continuous_LH).mul continuous_const)

lemma trI_mul_alg (a b : F) : trI (algebraMap F (InfiniteAdeleRing F) a *
    algebraMap F (InfiniteAdeleRing F) b) = ((Algebra.trace ℚ F (a * b) : ℚ) : ℝ) := by
  rw [← map_mul, trI_algebraMap]

lemma trLin_apply (η : F) (t : EuclideanSpace ℝ (Ix F)) :
    trI (LH t * algebraMap F (InfiniteAdeleRing F) η) =
      ∑ i, t i * ((Algebra.trace ℚ F (integralBasis F i * η) : ℚ) : ℝ) := by
  change trLin η t = _
  have ht : t = ∑ i, t i • AuxP.zpt (Pi.single i 1) := by
    ext j
    simp [AuxP.zpt, Pi.single_apply, Finset.sum_apply]
  conv_lhs => rw [ht]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_real_smul (trLin η) (continuous_trLin η), smul_eq_mul]
  congr 1
  change trI (LH (AuxP.zpt (Pi.single i 1)) * algebraMap F (InfiniteAdeleRing F) η) = _
  rw [LH_zpt, trI_mul_alg]
  congr 3
  simp [emb, Pi.single_apply]

/-- the trace-dual basis of the integral basis -/
noncomputable def bd (F : Type*) [Field F] [NumberField F] : Module.Basis (Ix F) ℚ F :=
  (Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) (integralBasis F)

lemma trace_bd (i j : Ix F) :
    Algebra.trace ℚ F (integralBasis F i * bd F j) = if i = j then 1 else 0 := by
  have := LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate ℚ F)
    (integralBasis F) j i
  rw [Algebra.traceForm_apply, mul_comm] at this
  exact this

/-- the element `∑ (nⱼ / M) bⱼ^∨` of the dual lattice of `M 𝒪` -/
noncomputable def etaN (M : ℕ) (n : Ix F → ℤ) : F := ∑ j, ((n j : ℚ) / M) • bd F j

lemma trace_etaN (M : ℕ) (n : Ix F → ℤ) (i : Ix F) :
    Algebra.trace ℚ F (integralBasis F i * etaN M n) = (n i : ℚ) / M := by
  simp only [etaN, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, trace_bd, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma trI_LH_etaN (M : ℕ) (n : Ix F → ℤ) (t : EuclideanSpace ℝ (Ix F)) :
    trI (LH t * algebraMap F (InfiniteAdeleRing F) (etaN M n)) =
      (∑ i, t i * (n i : ℝ)) / M := by
  rw [trLin_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [trace_etaN]; push_cast; ring

lemma etaN_injective (M : ℕ) (hM : M ≠ 0) : Function.Injective (etaN (F := F) M) := by
  intro a b h
  funext i
  have h1 := trace_etaN M a i
  rw [h, trace_etaN] at h1
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  have : (b i : ℚ) = a i := by
    field_simp at h1; exact h1
  exact_mod_cast this.symm

lemma exists_etaN (M : ℕ) (hM : M ≠ 0) (η : F)
    (h : ∀ i, ∃ k : ℤ, (M : ℚ) * Algebra.trace ℚ F (integralBasis F i * η) = k) :
    ∃ n, η = etaN M n := by
  choose k hk using h
  refine ⟨k, ?_⟩
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  rw [← (bd F).sum_repr η]
  simp only [etaN]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [bd, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm]
  field_simp
  rw [← hk j, mul_comm]

lemma trace_emb_etaN (M : ℕ) (m n : Ix F → ℤ) :
    Algebra.trace ℚ F (emb m * etaN M n) = (∑ i, m i * n i : ℤ) / M := by
  simp only [emb, Finset.sum_mul, smul_mul_assoc, map_sum, map_zsmul, trace_etaN]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [zsmul_eq_mul]; ring


/-! ### boxes `c Ô` in the finite adeles -/

/-- the set `c Ô` -/
def box (c : F) : Set (FiniteAdeleRing (𝓞 F) F) :=
  {z | ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (z v) ≤ Valued.v (algebraMap F (v.adicCompletion F) c)}

lemma zero_mem_box (c : F) : (0 : FiniteAdeleRing (𝓞 F) F) ∈ box c := by
  intro v; change Valued.v (0 : v.adicCompletion F) ≤ _; simp

lemma add_mem_box {c : F} {a b : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ box c) (hb : b ∈ box c) :
    a + b ∈ box c := fun v => Valuation.map_add_le _ (ha v) (hb v)

lemma neg_mem_box {c : F} {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ box c) : -a ∈ box c := by
  intro v; change Valued.v (-(a v)) ≤ _; rw [Valuation.map_neg]; exact ha v

lemma sub_mem_box {c : F} {a b : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ box c) (hb : b ∈ box c) :
    a - b ∈ box c := by
  rw [sub_eq_add_neg]; exact add_mem_box ha (neg_mem_box hb)

/-- the additive subgroup `c Ô` -/
def boxSub (c : F) : AddSubgroup (FiniteAdeleRing (𝓞 F) F) where
  carrier := box c
  add_mem' := add_mem_box
  zero_mem' := zero_mem_box c
  neg_mem' := neg_mem_box

lemma mem_box_one (z : FiniteAdeleRing (𝓞 F) F) :
    z ∈ box (1 : F) ↔ ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (z v) ≤ 1 := by
  simp [box]

lemma mul_mem_box {c c' : F} {a b : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ box c) (hb : b ∈ box c') :
    a * b ∈ box (c * c') := by
  intro v
  change Valued.v (a v * b v) ≤ _
  rw [map_mul, map_mul, map_mul]
  exact mul_le_mul' (ha v) (hb v)

lemma alg_mem_box (c : F) (r : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (c * algebraMap (𝓞 F) F r) ∈ box c := by
  intro v
  rw [fin_algebraMap_apply, map_mul, map_mul]
  calc _ ≤ Valued.v (algebraMap F (v.adicCompletion F) c) * 1 :=
        mul_le_mul' le_rfl (val_int_le_one v r)
    _ = _ := mul_one _

lemma mem_box_iff_mul (c : F) (hc : c ≠ 0) (z : FiniteAdeleRing (𝓞 F) F) :
    z ∈ box c ↔ algebraMap F (FiniteAdeleRing (𝓞 F) F) c⁻¹ * z ∈ box (1 : F) := by
  rw [mem_box_one]
  simp only [box, Set.mem_ofPred_eq]
  refine forall_congr' fun v => ?_
  change _ ↔ Valued.v (algebraMap F (v.adicCompletion F) c⁻¹ * z v) ≤ 1
  have hc' : Valued.v (algebraMap F (v.adicCompletion F) c) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr ((map_ne_zero _).mpr hc)
  rw [map_mul, map_inv₀, map_inv₀]
  constructor
  · intro h
    calc (Valued.v (algebraMap F (v.adicCompletion F) c))⁻¹ * Valued.v (z v)
        ≤ (Valued.v (algebraMap F (v.adicCompletion F) c))⁻¹ *
            Valued.v (algebraMap F (v.adicCompletion F) c) := mul_le_mul' le_rfl h
      _ = 1 := inv_mul_cancel₀ hc'
  · intro h
    have := mul_le_mul' (le_refl (Valued.v (algebraMap F (v.adicCompletion F) c))) h
    rwa [← mul_assoc, mul_inv_cancel₀ hc', one_mul, mul_one] at this

/-- elements of `F` in `c Ô` are the elements of `c 𝒪` -/
lemma alg_mem_box_iff (c : F) (hc : c ≠ 0) (ξ : F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ ∈ box c ↔ ∃ r : 𝓞 F, ξ = c * algebraMap (𝓞 F) F r := by
  constructor
  · intro h
    rw [mem_box_iff_mul c hc, ← map_mul, mem_box_one] at h
    obtain ⟨r, hr⟩ := int_of_val_le_one (c⁻¹ * ξ) (fun v => h v)
    exact ⟨r, by rw [hr]; field_simp⟩
  · rintro ⟨r, rfl⟩
    exact alg_mem_box c r

lemma alg_mem_boxM_iff (M : ℕ) (hM : M ≠ 0) (ξ : F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ ∈ box (M : F) ↔ ∃ m : Ix F → ℤ, ξ = M * emb m := by
  rw [alg_mem_box_iff _ (by exact_mod_cast hM)]
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨m, hm⟩ := exists_emb r
    exact ⟨m, by rw [hm]⟩
  · rintro ⟨m, rfl⟩
    exact ⟨_, by rw [emb_int]⟩

/-- every finite adele is congruent to an element of `F` modulo `c Ô` -/
lemma exists_sub_box (c : F) (hc : c ≠ 0) (z : FiniteAdeleRing (𝓞 F) F) :
    ∃ ξ : F, z - algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ ∈ box c := by
  obtain ⟨ξ, hξ⟩ := exists_sub_int (algebraMap F (FiniteAdeleRing (𝓞 F) F) c⁻¹ * z)
  refine ⟨c * ξ, ?_⟩
  rw [mem_box_iff_mul c hc, mem_box_one]
  intro v
  have := hξ v
  have hc' : algebraMap F (v.adicCompletion F) c ≠ 0 := (map_ne_zero _).mpr hc
  convert this using 2
  change algebraMap F (v.adicCompletion F) c⁻¹ * (z v - algebraMap F (v.adicCompletion F) (c * ξ)) =
    algebraMap F (v.adicCompletion F) c⁻¹ * z v - algebraMap F (v.adicCompletion F) ξ
  rw [map_mul, map_inv₀, mul_sub]
  field_simp

lemma box_mono_int (c : F) (r : 𝓞 F) : box (c * algebraMap (𝓞 F) F r) ⊆ box c := by
  intro z hz v
  refine (hz v).trans ?_
  rw [map_mul, map_mul]
  calc _ ≤ Valued.v (algebraMap F (v.adicCompletion F) c) * 1 :=
        mul_le_mul' le_rfl (val_int_le_one v r)
    _ = _ := mul_one _

/-- integral adeles decompose as integers plus `e Ô` -/
lemma int_decomp (e : 𝓞 F) (he : e ≠ 0) (z : FiniteAdeleRing (𝓞 F) F) (hz : z ∈ box (1 : F)) :
    ∃ r : 𝓞 F, z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F r) ∈
      box (algebraMap (𝓞 F) F e) := by
  have he' : algebraMap (𝓞 F) F e ≠ 0 := by simpa using he
  obtain ⟨ξ, hξ⟩ := exists_sub_box _ he' z
  have h1 : box (algebraMap (𝓞 F) F e) ⊆ box (1 : F) := by
    have := box_mono_int (1 : F) e
    rwa [one_mul] at this
  have hξ1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ ∈ box (1 : F) := by
    have : algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ =
        z - (z - algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ) := by ring
    rw [this]; exact sub_mem_box hz (h1 hξ)
  obtain ⟨r, hr⟩ := (alg_mem_box_iff 1 one_ne_zero ξ).mp hξ1
  refine ⟨r, ?_⟩
  rw [one_mul] at hr
  rw [← hr]; exact hξ

section PriorLocal
open IsLocalRing RestrictedProduct
theorem nonempty_residueFieldEquiv (v : HeightOneSpectrum (𝓞 F)) :
    Nonempty ((𝓞 F ⧸ v.asIdeal) ≃+* ResidueField (v.adicCompletionIntegers F)) := by
  let O := v.adicCompletionIntegers F
  let f := (residue O).comp (algebraMap (𝓞 F) O)
  let q : 𝓞 F ⧸ v.asIdeal →+* ResidueField O := Ideal.Quotient.lift v.asIdeal f (by
    intro r hr
    rw [RingHom.comp_apply, residue_eq_zero_iff]
    apply (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).2
    change Valued.v ((algebraMap (𝓞 F) F r : F) : v.adicCompletion F) < (1 : ℤᵐ⁰)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (v.valuation_lt_one_iff_mem r).2 hr)
  let := Ideal.Quotient.field v.asIdeal
  refine ⟨RingEquiv.ofBijective q ⟨q.injective, ?_⟩⟩
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  let ν : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v
  have hn : {z | ν (z - (x : v.adicCompletion F)) < 1} ∈ 𝓝 (x : v.adicCompletion F) := by
    refine Valued.mem_nhds.mpr ⟨1, ?_⟩
    intro z hz
    simpa only [Set.mem_ofPred_eq, Units.val_one, Valuation.restrict_lt_iff_lt_embedding,
      map_one] using hz
  obtain ⟨a, ha⟩ := (v.denseRange_algebraMap F).mem_nhds hn
  change ν (algebraMap F (v.adicCompletion F) a - x) < 1 at ha
  have ha' : v.valuation F a ≤ 1 := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    change ν (algebraMap F (v.adicCompletion F) a) ≤ 1
    simpa only [sub_add_cancel] using ν.map_add_le ha.le x.property
  obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer ha' 1
  have hr' : ν (algebraMap (𝓞 F) (v.adicCompletion F) r -
      algebraMap F (v.adicCompletion F) a) < 1 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← map_sub]
    change Valued.v (((algebraMap (𝓞 F) F) r - a : F) : v.adicCompletion F) < (1 : ℤᵐ⁰)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa only [Units.val_one] using hr
  refine ⟨Ideal.Quotient.mk _ r, sub_eq_zero.mp ?_⟩
  change residue O (algebraMap (𝓞 F) O r) - residue O x = 0
  rw [← map_sub, residue_eq_zero_iff]
  apply (Valuation.mem_maximalIdeal_iff _ ν).2
  change ν (algebraMap (𝓞 F) (v.adicCompletion F) r - x) < 1
  simpa only [sub_add_sub_cancel] using ν.map_add_lt hr' ha

theorem finite_residueField (v : HeightOneSpectrum (𝓞 F)) :
    Finite (ResidueField (v.adicCompletionIntegers F)) := by
  obtain ⟨e⟩ := nonempty_residueFieldEquiv v
  have : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  exact Finite.of_equiv _ e.toEquiv

theorem properSpace_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    ProperSpace (v.adicCompletion F) := by
  have : IsDiscreteValuationRing (v.adicCompletionIntegers F) := inferInstance
  exact (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (Γ₀ := ℤᵐ⁰)).2 ⟨inferInstance, ‹_›, finite_residueField v⟩

theorem compactSpace_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (v.adicCompletionIntegers F) := by
  have : IsClosed (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isClosed_valuationSubring _
  have hcomplete : CompleteSpace (v.adicCompletionIntegers F) := IsClosed.completeSpace_coe
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    ⟨hcomplete, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
      finite_residueField v⟩

theorem isCompact_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have := compactSpace_adicCompletionIntegers v
  exact isCompact_iff_compactSpace.mpr this

theorem isOpen_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  Valued.isOpen_valuationSubring _

instance locallyCompactSpace_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    LocallyCompactSpace (v.adicCompletion F) := by
  have := properSpace_adicCompletion v
  infer_instance

instance locallyCompactSpace_finiteAdeleRing : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := by
  have : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ isOpen_adicCompletionIntegers v⟩
  exact RestrictedProduct.locallyCompactSpace_of_addGroup _
    (Filter.Eventually.of_forall fun v ↦ isCompact_adicCompletionIntegers v)

instance locallyCompactSpace_adeleRing : LocallyCompactSpace (AdeleRing (𝓞 F) F) := by
  change LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  infer_instance

instance t2Space_adeleRing : T2Space (AdeleRing (𝓞 F) F) := by
  have : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    T2Space.of_injective_continuous
      (f := fun x : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]
        ↦ (x : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F))
      DFunLike.coe_injective RestrictedProduct.continuous_coe
  have : T2Space (InfiniteAdeleRing F) := by
    change T2Space ((v : InfinitePlace F) → v.Completion)
    infer_instance
  change T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  infer_instance
end PriorLocal

/-! ### topology of boxes -/

lemma box_one_eq : box (1 : F) = {f : FiniteAdeleRing (𝓞 F) F |
    ∀ v, f v ∈ v.adicCompletionIntegers F} := by
  ext z; rw [mem_box_one]; simp [HeightOneSpectrum.mem_adicCompletionIntegers]

open RestrictedProduct in
instance t2Space_finiteAdeleRing : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  T2Space.of_injective_continuous
    (f := fun x : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]
      ↦ (x : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F))
    DFunLike.coe_injective RestrictedProduct.continuous_coe

lemma isOpen_box_one : IsOpen (box (1 : F)) := by
  rw [box_one_eq]
  exact RestrictedProduct.isOpen_forall_mem (fun v => isOpen_adicCompletionIntegers v)

lemma isCompact_box_one : IsCompact (box (1 : F)) := by
  rw [box_one_eq]
  have : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F) :=
    fun v => compactSpace_adicCompletionIntegers v
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

lemma box_eq_preimage (c : F) (hc : c ≠ 0) :
    box c = (fun z => algebraMap F (FiniteAdeleRing (𝓞 F) F) c⁻¹ * z) ⁻¹' box (1 : F) := by
  ext z; exact mem_box_iff_mul c hc z

lemma box_eq_image (c : F) (hc : c ≠ 0) :
    box c = (fun z => algebraMap F (FiniteAdeleRing (𝓞 F) F) c * z) '' box (1 : F) := by
  ext z
  rw [mem_box_iff_mul c hc]
  constructor
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
  · rintro ⟨w, hw, rfl⟩
    simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] using hw

lemma isOpen_box (c : F) (hc : c ≠ 0) : IsOpen (box c) := by
  rw [box_eq_preimage c hc]
  exact isOpen_box_one.preimage (continuous_const.mul continuous_id)

lemma isCompact_box (c : F) (hc : c ≠ 0) : IsCompact (box c) := by
  rw [box_eq_image c hc]
  exact isCompact_box_one.image (continuous_const.mul continuous_id)

lemma isClosed_box (c : F) (hc : c ≠ 0) : IsClosed (box c) := (isCompact_box c hc).isClosed

/-! ### fundamental domains for `F` in `𝔸_F` -/

/-- the cube `[0, M)^d` -/
def cube (M : ℕ) : Set (EuclideanSpace ℝ (Ix F)) := {s | ∀ i, s i ∈ Set.Ico (0 : ℝ) M}

/-- the fundamental domain `LH([0,M)^d) × M Ô` -/
def FD (M : ℕ) : Set (AdeleRing (𝓞 F) F) := {x | x.2 ∈ box (M : F) ∧ LH.symm x.1 ∈ cube M}

lemma LH_symm_alg_emb (m : Ix F → ℤ) :
    LH.symm (algebraMap F (InfiniteAdeleRing F) (emb m)) = AuxP.zpt m := by
  rw [← LH_zpt, Homeomorph.symm_apply_apply]

lemma LH_symm_alg_Memb (M : ℕ) (m : Ix F → ℤ) :
    LH.symm (algebraMap F (InfiniteAdeleRing F) ((M : F) * emb m)) = M • AuxP.zpt m := by
  rw [show algebraMap F (InfiniteAdeleRing F) ((M : F) * emb m) = LH (M • AuxP.zpt m) by
    rw [LH_nsmul, LH_zpt, map_mul, map_natCast, nsmul_eq_mul], Homeomorph.symm_apply_apply]

lemma zpt_apply (m : Ix F → ℤ) (i : Ix F) : (AuxP.zpt m) i = (m i : ℝ) := rfl

lemma FD_unique (M : ℕ) (hM : M ≠ 0) (x : AdeleRing (𝓞 F) F) :
    ∃! ξ : F, x + algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ FD M := by
  have hM' : (M : F) ≠ 0 := by exact_mod_cast hM
  have hMR : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  obtain ⟨ξ0, hξ0⟩ := exists_sub_box (M : F) hM' x.2
  set s := LH.symm (x.1 - algebraMap F (InfiniteAdeleRing F) ξ0)
  let m : Ix F → ℤ := fun i => -⌊s i / M⌋
  refine ⟨-ξ0 + M * emb m, ⟨?_, ?_⟩, ?_⟩
  · change x.2 + algebraMap F (FiniteAdeleRing (𝓞 F) F) (-ξ0 + M * emb m) ∈ box (M : F)
    rw [RingHom.map_add, RingHom.map_neg, ← add_assoc, ← sub_eq_add_neg]
    exact add_mem_box hξ0 ((alg_mem_boxM_iff M hM _).mpr ⟨m, rfl⟩)
  · change LH.symm (x.1 + algebraMap F (InfiniteAdeleRing F) (-ξ0 + M * emb m)) ∈ cube M
    rw [RingHom.map_add, RingHom.map_neg, ← add_assoc, ← sub_eq_add_neg, LH_symm_add,
      LH_symm_alg_Memb]
    intro i
    change s i + (M • AuxP.zpt m) i ∈ Set.Ico (0 : ℝ) M
    rw [PiLp.smul_apply, zpt_apply, nsmul_eq_mul]
    simp only [m, Int.cast_neg]
    constructor
    · have := Int.floor_le (s i / M)
      have h2 : (M : ℝ) * ⌊s i / M⌋ ≤ s i := by
        rw [le_div_iff₀ hMR] at this; linarith
      linarith
    · have := Int.lt_floor_add_one (s i / M)
      have h2 : s i < M * ⌊s i / M⌋ + M := by
        rw [div_lt_iff₀ hMR] at this; linarith
      linarith
  · rintro η ⟨h1, h2⟩
    -- the difference lies in `M 𝒪`
    have hd : algebraMap F (FiniteAdeleRing (𝓞 F) F) (η - (-ξ0 + M * emb m)) ∈ box (M : F) := by
      have e1 : (x + algebraMap F (AdeleRing (𝓞 F) F) η).2 ∈ box (M : F) := h1
      have e2 : x.2 + algebraMap F (FiniteAdeleRing (𝓞 F) F) (-ξ0 + M * emb m) ∈ box (M : F) := by
        rw [RingHom.map_add, RingHom.map_neg, ← add_assoc, ← sub_eq_add_neg]
        exact add_mem_box hξ0 ((alg_mem_boxM_iff M hM _).mpr ⟨m, rfl⟩)
      have := sub_mem_box e1 e2
      convert this using 1
      change _ = x.2 + algebraMap F (FiniteAdeleRing (𝓞 F) F) η - _
      rw [map_sub]; ring
    obtain ⟨k, hk⟩ := (alg_mem_boxM_iff M hM _).mp hd
    have hη : η = (-ξ0 + M * emb m) + M * emb k := by rw [← hk]; ring
    -- compare the archimedean coordinates
    have h2' : LH.symm (x.1 + algebraMap F (InfiniteAdeleRing F) η) ∈ cube M := h2
    rw [hη, RingHom.map_add, RingHom.map_add, RingHom.map_neg, ← add_assoc, ← add_assoc,
      ← sub_eq_add_neg, LH_symm_add, LH_symm_add, LH_symm_alg_Memb, LH_symm_alg_Memb] at h2'
    have hk0 : k = 0 := by
      funext i
      have hi := h2' i
      change s i + (M • AuxP.zpt m) i + (M • AuxP.zpt k) i ∈ Set.Ico (0 : ℝ) M at hi
      rw [PiLp.smul_apply, PiLp.smul_apply, zpt_apply, zpt_apply, nsmul_eq_mul, nsmul_eq_mul] at hi
      simp only [m, Int.cast_neg] at hi
      have hf1 := Int.floor_le (s i / M)
      have hf2 := Int.lt_floor_add_one (s i / M)
      rw [le_div_iff₀ hMR] at hf1
      rw [div_lt_iff₀ hMR] at hf2
      have hlo : (k i : ℝ) * M > -M := by nlinarith [hi.1]
      have hhi : (k i : ℝ) * M < M := by nlinarith [hi.2]
      have : (-1 : ℝ) < k i := by
        by_contra hc; have hc' := not_lt.mp hc; nlinarith
      have : (k i : ℝ) < 1 := by
        by_contra hc; have hc' := not_lt.mp hc; nlinarith
      have h3 : (-1 : ℤ) < k i := by exact_mod_cast ‹(-1 : ℝ) < k i›
      have h4 : k i < 1 := by exact_mod_cast ‹(k i : ℝ) < 1›
      simp only [Pi.zero_apply]; omega
    rw [hη, hk0]
    simp [emb]


/-! ### the Tamagawa measure on the adeles -/

section Measure

open MeasureTheory

/-- adele from a pair -/
def mkA (a : InfiniteAdeleRing F) (b : FiniteAdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F := (a, b)

@[simp] lemma mkA_fst (a : InfiniteAdeleRing F) (b : FiniteAdeleRing (𝓞 F) F) : (mkA a b).1 = a := rfl
@[simp] lemma mkA_snd (a : InfiniteAdeleRing F) (b : FiniteAdeleRing (𝓞 F) F) : (mkA a b).2 = b := rfl

lemma continuous_mkA : Continuous (fun p : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F =>
    mkA p.1 p.2) := continuous_id

lemma continuous_fst_A : Continuous (fun x : AdeleRing (𝓞 F) F => x.1) := continuous_fst
lemma continuous_snd_A : Continuous (fun x : AdeleRing (𝓞 F) F => x.2) := continuous_snd

lemma measurableSet_boxA (c : F) (hc : c ≠ 0) :
    MeasurableSet {x : AdeleRing (𝓞 F) F | x.2 ∈ box c} :=
  ((isOpen_box c hc).preimage continuous_snd_A).measurableSet

lemma measurableSet_cube (M : ℕ) : MeasurableSet (cube (F := F) M) := by
  have : cube (F := F) M = ⋂ i, (fun s : EuclideanSpace ℝ (Ix F) => s i) ⁻¹' Set.Ico (0 : ℝ) M := by
    ext s; simp [cube]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_Ico).preimage ((PiLp.continuous_apply 2 _ i).measurable)

lemma continuous_LHs_fst : Continuous (fun x : AdeleRing (𝓞 F) F => LH.symm x.1) :=
  LH.symm.continuous.comp continuous_fst_A

lemma measurableSet_FD (M : ℕ) (hM : M ≠ 0) : MeasurableSet (FD (F := F) M) :=
  (measurableSet_boxA (M : F) (by exact_mod_cast hM)).inter
    ((measurableSet_cube M).preimage continuous_LHs_fst.measurable)

lemma isCompact_prodImage (K : Set (EuclideanSpace ℝ (Ix F))) (hK : IsCompact K) (c : F)
    (hc : c ≠ 0) : IsCompact ((fun p : EuclideanSpace ℝ (Ix F) × FiniteAdeleRing (𝓞 F) F =>
      mkA (LH p.1) p.2) '' (K ×ˢ box c)) :=
  (hK.prod (isCompact_box c hc)).image
    (continuous_mkA.comp ((LH.continuous.comp continuous_fst).prodMk continuous_snd))

lemma subset_prodImage (K : Set (EuclideanSpace ℝ (Ix F))) (c : F) :
    {x : AdeleRing (𝓞 F) F | x.2 ∈ box c ∧ LH.symm x.1 ∈ K} ⊆
      (fun p : EuclideanSpace ℝ (Ix F) × FiniteAdeleRing (𝓞 F) F => mkA (LH p.1) p.2) ''
        (K ×ˢ box c) := by
  rintro x ⟨h1, h2⟩
  exact ⟨(LH.symm x.1, x.2), ⟨h2, h1⟩, by simp only [mkA, Homeomorph.apply_symm_apply]; rfl⟩

lemma exists_tamagawa_hyp : ∃ ν : Measure (AdeleRing (𝓞 F) F), ν.IsAddHaarMeasure ∧
    ∃ D : Set (AdeleRing (𝓞 F) F), MeasurableSet D ∧
      (∀ x : AdeleRing (𝓞 F) F, ∃! ξ : F, x + algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ D) ∧
      ν D = 1 := by
  let ν0 : Measure (AdeleRing (𝓞 F) F) := Measure.addHaar
  -- positivity
  let U : Set (AdeleRing (𝓞 F) F) := {x | x.2 ∈ box (1 : F) ∧
    LH.symm x.1 ∈ {s : EuclideanSpace ℝ (Ix F) | ∀ i, s i ∈ Set.Ioo (0 : ℝ) 1}}
  have hUo : IsOpen U := by
    show IsOpen ({x : AdeleRing (𝓞 F) F | x.2 ∈ box (1 : F)} ∩ ((fun x : AdeleRing (𝓞 F) F =>
      LH.symm x.1) ⁻¹' {s : EuclideanSpace ℝ (Ix F) | ∀ i, s i ∈ Set.Ioo (0 : ℝ) 1}))
    refine (isOpen_box_one.preimage continuous_snd_A).inter (IsOpen.preimage continuous_LHs_fst ?_)
    have : {s : EuclideanSpace ℝ (Ix F) | ∀ i, s i ∈ Set.Ioo (0 : ℝ) 1} =
        ⋂ i, (fun s : EuclideanSpace ℝ (Ix F) => s i) ⁻¹' Set.Ioo (0 : ℝ) 1 := by ext; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (PiLp.continuous_apply 2 _ i)
  have hUne : U.Nonempty := by
    refine ⟨mkA (LH (WithLp.toLp 2 (fun _ => (1 / 2 : ℝ)))) 0, ?_, ?_⟩
    · exact zero_mem_box 1
    · intro i; simp only [mkA_fst, Homeomorph.symm_apply_apply]
      constructor <;> norm_num
  have hU : U ⊆ FD 1 := by
    rintro x ⟨h1, h2⟩
    refine ⟨by exact_mod_cast h1, fun i => ⟨(h2 i).1.le, by exact_mod_cast (h2 i).2⟩⟩
  have hpos : ν0 (FD 1) ≠ 0 :=
    (lt_of_lt_of_le (hUo.measure_pos ν0 hUne) (measure_mono hU)).ne'
  -- finiteness
  let Kc : Set (EuclideanSpace ℝ (Ix F)) := {s | ∀ i, s i ∈ Set.Icc (0 : ℝ) 1}
  have hKc : IsCompact Kc := by
    have : Kc = (fun s : EuclideanSpace ℝ (Ix F) => (WithLp.ofLp s)) ⁻¹'
        (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1) := by
      ext s
      simp only [Kc, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]
    rw [this]
    exact (PiLp.homeomorph 2 _ ).isCompact_preimage.mpr (isCompact_univ_pi fun _ => isCompact_Icc)
  have hfin : ν0 (FD 1) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ((isCompact_prodImage Kc hKc 1 one_ne_zero).measure_lt_top).ne
      (measure_mono ((?_ : FD 1 ⊆ _).trans (subset_prodImage Kc 1)))
    rintro x ⟨h1, h2⟩
    exact ⟨by exact_mod_cast h1, fun i => ⟨(h2 i).1, by exact_mod_cast (h2 i).2.le⟩⟩
  refine ⟨(ν0 (FD 1))⁻¹ • ν0, ?_, FD 1, measurableSet_FD 1 one_ne_zero,
    fun x => FD_unique 1 one_ne_zero x, ?_⟩
  · exact Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr hfin) (ENNReal.inv_ne_top.mpr hpos)
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]

lemma tam_spec : (tamagawaAdelic (F := F)).IsAddHaarMeasure ∧
    ∃ D : Set (AdeleRing (𝓞 F) F), MeasurableSet D ∧
      (∀ x : AdeleRing (𝓞 F) F, ∃! ξ : F, x + algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ D) ∧
      tamagawaAdelic D = 1 := by
  have h := exists_tamagawa_hyp (F := F)
  unfold tamagawaAdelic
  rw [dif_pos h]
  exact h.choose_spec

instance tam_isAddHaar : (tamagawaAdelic (F := F)).IsAddHaarMeasure := tam_spec.1

lemma countable_F : Countable F :=
  Function.Injective.countable (integralBasis F).equivFun.injective

lemma tam_FD (D : Set (AdeleRing (𝓞 F) F)) (hD : MeasurableSet D)
    (hfd : ∀ x : AdeleRing (𝓞 F) F, ∃! ξ : F, x + algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ D) :
    tamagawaAdelic D = 1 := by
  have := countable_F (F := F)
  let G : AddSubgroup (AdeleRing (𝓞 F) F) := AdeleRing.principalSubgroup (𝓞 F) F
  have hfdG : ∀ D' : Set (AdeleRing (𝓞 F) F), MeasurableSet D' →
      (∀ x : AdeleRing (𝓞 F) F, ∃! ξ : F, x + algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ D') →
      IsAddFundamentalDomain G D' tamagawaAdelic := by
    intro D' hD' hfd'
    refine IsAddFundamentalDomain.mk' hD'.nullMeasurableSet fun x => ?_
    obtain ⟨ξ, hξ, huniq⟩ := hfd' x
    refine ⟨⟨algebraMap F _ ξ, ξ, rfl⟩, ?_, ?_⟩
    · change algebraMap F _ ξ + x ∈ D'
      rwa [add_comm]
    · rintro ⟨g, η, rfl⟩ hg
      change algebraMap F _ η + x ∈ D' at hg
      rw [add_comm] at hg
      have := huniq η hg
      subst this
      rfl
  have hcount : Countable G := by
    have : Function.Surjective (fun ξ : F => (⟨algebraMap F _ ξ, ξ, rfl⟩ : G)) := by
      rintro ⟨g, η, rfl⟩; exact ⟨η, rfl⟩
    exact this.countable
  have hinv : VAddInvariantMeasure G (AdeleRing (𝓞 F) F) tamagawaAdelic :=
    ⟨fun c s _ => measure_preimage_add tamagawaAdelic (c : AdeleRing (𝓞 F) F) s⟩
  obtain ⟨D0, hD0, hfd0, h1⟩ := (tam_spec (F := F)).2
  rw [(hfdG D hD hfd).measure_eq (hfdG D0 hD0 hfd0), h1]

lemma tam_FDM (M : ℕ) (hM : M ≠ 0) : tamagawaAdelic (FD (F := F) M) = 1 :=
  tam_FD _ (measurableSet_FD M hM) (FD_unique M hM)

end Measure


section Measure2

open MeasureTheory

/-- the pushforward of the Tamagawa measure on `F_∞ × M Ô` to `ℝ^d` -/
noncomputable def muM (M : ℕ) : Measure (EuclideanSpace ℝ (Ix F)) :=
  Measure.map (fun x : AdeleRing (𝓞 F) F => LH.symm x.1)
    ((tamagawaAdelic (F := F)).restrict {x | x.2 ∈ box (M : F)})

lemma muM_apply (M : ℕ) (hM : M ≠ 0) (E : Set (EuclideanSpace ℝ (Ix F))) (hE : MeasurableSet E) :
    muM M E = tamagawaAdelic {x : AdeleRing (𝓞 F) F | x.2 ∈ box (M : F) ∧ LH.symm x.1 ∈ E} := by
  rw [muM, Measure.map_apply continuous_LHs_fst.measurable hE,
    Measure.restrict_apply (hE.preimage continuous_LHs_fst.measurable)]
  congr 1
  ext x; simp [and_comm]

lemma muM_leftInv (M : ℕ) (hM : M ≠ 0) : (muM (F := F) M).IsAddLeftInvariant := by
  refine ⟨fun t => ?_⟩
  ext E hE
  rw [Measure.map_apply (measurable_const_add t) hE, muM_apply M hM _ hE,
    muM_apply M hM _ (hE.preimage (measurable_const_add t))]
  have : {x : AdeleRing (𝓞 F) F | x.2 ∈ box (M : F) ∧ LH.symm x.1 ∈ (fun s => t + s) ⁻¹' E} =
      (fun x => mkA (LH t) 0 + x) ⁻¹'
        {x : AdeleRing (𝓞 F) F | x.2 ∈ box (M : F) ∧ LH.symm x.1 ∈ E} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    have h1 : (mkA (LH t) 0 + x).2 = x.2 := by
      change (0 : FiniteAdeleRing (𝓞 F) F) + x.2 = x.2; rw [zero_add]
    have h2 : (mkA (LH t) 0 + x).1 = LH t + x.1 := rfl
    rw [h1, h2, LH_symm_add, Homeomorph.symm_apply_apply]
  rw [this, measure_preimage_add]

lemma muM_finite (M : ℕ) (hM : M ≠ 0) : IsFiniteMeasureOnCompacts (muM (F := F) M) := by
  refine ⟨fun K hK => ?_⟩
  rw [muM_apply M hM K hK.measurableSet]
  have hM' : (M : F) ≠ 0 := by exact_mod_cast hM
  exact lt_of_le_of_lt (measure_mono (subset_prodImage K (M : F)))
    (isCompact_prodImage K hK (M : F) hM').measure_lt_top

lemma volume_cube (M : ℕ) : (MeasureTheory.volume (cube (F := F) M)) =
    (M : ENNReal) ^ Fintype.card (Ix F) := by
  have : cube (F := F) M = (fun s : EuclideanSpace ℝ (Ix F) => WithLp.ofLp s) ⁻¹'
      (Set.pi Set.univ fun _ => Set.Ico (0 : ℝ) M) := by
    ext s
    simp only [cube, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]
  rw [this, (PiLp.volume_preserving_ofLp (Ix F)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet]
  rw [Real.volume_pi_Ico]
  simp [Finset.prod_const, ENNReal.ofReal_natCast]

lemma muM_eq (M : ℕ) (hM : M ≠ 0) :
    muM (F := F) M = ((M : ENNReal) ^ Fintype.card (Ix F))⁻¹ • MeasureTheory.volume := by
  have := muM_leftInv (F := F) M hM
  have := muM_finite (F := F) M hM
  have h := Measure.isAddLeftInvariant_eq_smul (muM (F := F) M) MeasureTheory.volume
  set c := Measure.addHaarScalarFactor (muM (F := F) M) MeasureTheory.volume
  have h1 : muM (F := F) M (cube M) = 1 := by
    rw [muM_apply M hM _ (measurableSet_cube M)]
    exact tam_FDM M hM
  have h2 : (c : ENNReal) * (M : ENNReal) ^ Fintype.card (Ix F) = 1 := by
    rw [h, Measure.smul_apply, volume_cube] at h1
    simpa [ENNReal.smul_def] using h1
  have hc : (c : ENNReal) = ((M : ENNReal) ^ Fintype.card (Ix F))⁻¹ :=
    ENNReal.eq_inv_of_mul_eq_one_left h2
  rw [h]
  ext E hE
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [← hc]
  rfl

/-- the basic integration formula on `F_∞ × M Ô` -/
lemma integral_box (M : ℕ) (hM : M ≠ 0) (G : InfiniteAdeleRing F → ℂ) (hG : Continuous G) :
    ∫ x in {x : AdeleRing (𝓞 F) F | x.2 ∈ box (M : F)}, G x.1 ∂tamagawaAdelic =
      ((M : ℝ) ^ Fintype.card (Ix F))⁻¹ • ∫ s, G (LH s) := by
  have h1 : ∫ x in {x : AdeleRing (𝓞 F) F | x.2 ∈ box (M : F)}, G x.1 ∂tamagawaAdelic =
      ∫ s, G (LH s) ∂(muM M) := by
    have := integral_map (μ := (tamagawaAdelic (F := F)).restrict
      {x : AdeleRing (𝓞 F) F | x.2 ∈ box (M : F)}) continuous_LHs_fst.measurable.aemeasurable
      (f := fun s => G (LH s)) (hG.comp LH.continuous).aestronglyMeasurable
    simp only [Homeomorph.apply_symm_apply] at this
    exact this.symm
  rw [h1, muM_eq M hM, integral_smul_measure]
  congr 1
  simp [ENNReal.toReal_inv, ENNReal.toReal_pow]

lemma integrableOn_box (M : ℕ) (hM : M ≠ 0) (G : InfiniteAdeleRing F → ℂ) (hG : Continuous G)
    (hi : Integrable (fun s => G (LH s))) :
    IntegrableOn (fun x : AdeleRing (𝓞 F) F => G x.1) {x | x.2 ∈ box (M : F)} tamagawaAdelic := by
  have h1 : Integrable (fun s => G (LH s)) (muM (F := F) M) := by
    rw [muM_eq M hM]
    exact hi.smul_measure (ENNReal.inv_ne_top.mpr (by simp [hM]))
  have h2 := (integrable_map_measure (hG.comp LH.continuous).aestronglyMeasurable
    continuous_LHs_fst.measurable.aemeasurable).mp h1
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp

end Measure2


/-! ### more on the standard character -/

lemma mkA_isIntegral (t : InfiniteAdeleRing F) (z : FiniteAdeleRing (𝓞 F) F) (hz : z ∈ box (1 : F)) :
    IsIntegralAdele (mkA t z) := by
  rw [isIntegral_iff]; exact (mem_box_one z).mp hz

lemma psi_inf (t : InfiniteAdeleRing F) : stdAdelicCharacter (mkA t 0) = Ie t :=
  psi_zero_int _ (mkA_isIntegral t 0 (zero_mem_box 1))

lemma psi_fin_int (z : FiniteAdeleRing (𝓞 F) F) (hz : z ∈ box (1 : F)) :
    stdAdelicCharacter (mkA 0 z) = 1 := by
  rw [psi_zero_int _ (mkA_isIntegral 0 z hz), mkA_fst]
  simp [Ie, trI_zero]

lemma mkA_add (a b : InfiniteAdeleRing F) (c d : FiniteAdeleRing (𝓞 F) F) :
    mkA a c + mkA b d = mkA (a + b) (c + d) := rfl

lemma mkA_mul (a b : InfiniteAdeleRing F) (c d : FiniteAdeleRing (𝓞 F) F) :
    mkA a c * mkA b d = mkA (a * b) (c * d) := rfl

lemma mkA_eta (x : AdeleRing (𝓞 F) F) : mkA x.1 x.2 = x := rfl

lemma alg_eq_mkA (ξ : F) : algebraMap F (AdeleRing (𝓞 F) F) ξ =
    mkA (algebraMap F (InfiniteAdeleRing F) ξ) (algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ) := rfl

lemma psi_split (x : AdeleRing (𝓞 F) F) :
    stdAdelicCharacter x = Ie x.1 * stdAdelicCharacter (mkA 0 x.2) := by
  have : x = mkA x.1 0 + mkA 0 x.2 := by rw [mkA_add, add_zero, zero_add, mkA_eta]
  conv_lhs => rw [this]
  rw [psi_add, psi_inf]

lemma psi_fin_alg (ξ : F) :
    stdAdelicCharacter (mkA 0 (algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) =
      Ie (-(algebraMap F (InfiniteAdeleRing F) ξ)) := by
  have : mkA 0 (algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ) =
      mkA (-(algebraMap F (InfiniteAdeleRing F) ξ)) 0 + algebraMap F _ ξ := by
    rw [alg_eq_mkA, mkA_add, neg_add_cancel, zero_add]
  rw [this, psi_add, psi_algebraMap, mul_one, psi_inf]

lemma Ie_neg_alg (ξ : F) : Ie (-(algebraMap F (InfiniteAdeleRing F) ξ)) =
    Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F ξ : ℚ) : ℂ)) := by
  simp only [Ie, trI_neg, trI_algebraMap]
  congr 1; push_cast; ring

lemma Ie_neg_alg_eq_one (ξ : F) (k : ℤ) (hk : Algebra.trace ℚ F ξ = k) :
    Ie (-(algebraMap F (InfiniteAdeleRing F) ξ)) = 1 := by
  rw [Ie_neg_alg, hk]
  have : (2 * Real.pi * Complex.I * (((k : ℚ) : ℚ) : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma Ie_neg_alg_ne_one (ξ : F) (h : ¬ ∃ k : ℤ, Algebra.trace ℚ F ξ = k) :
    Ie (-(algebraMap F (InfiniteAdeleRing F) ξ)) ≠ 1 := by
  rw [Ie_neg_alg]
  intro h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  apply h
  refine ⟨n, ?_⟩
  have h2 : ((Algebra.trace ℚ F ξ : ℚ) : ℂ) = (n : ℂ) := by
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have := hn
    rw [mul_comm (n : ℂ)] at this
    exact mul_left_cancel₀ hpi this
  exact_mod_cast h2

lemma continuous_psi : Continuous (stdAdelicCharacter (F := F)) := by
  rw [continuous_iff_continuousAt]
  intro x0
  obtain ⟨y0, ξ0, hy0, rfl⟩ := decomp_exists x0
  set x1 := y0 + algebraMap F (AdeleRing (𝓞 F) F) ξ0
  have hV : {x : AdeleRing (𝓞 F) F | (x - x1).2 ∈ box (1 : F)} ∈ 𝓝 x1 := by
    refine IsOpen.mem_nhds ?_ ?_
    · exact isOpen_box_one.preimage (continuous_snd_A.comp (continuous_id.sub continuous_const))
    · simp only [Set.mem_ofPred_eq, sub_self]; exact zero_mem_box 1
  have heq : (fun x => Ie (y0.1 + (x - x1).1)) =ᶠ[𝓝 x1] stdAdelicCharacter := by
    filter_upwards [hV] with x hx
    have hint : IsIntegralAdele (y0 + (x - x1)) := by
      rw [isIntegral_iff] at hy0 ⊢
      intro v
      exact Valuation.map_add_le _ (hy0 v) ((mem_box_one _).mp hx v)
    have : x = (y0 + (x - x1)) + algebraMap F (AdeleRing (𝓞 F) F) ξ0 := by
      simp only [x1]; ring
    conv_rhs => rw [this]
    rw [psi_eq _ _ hint]
    rfl
  refine ContinuousAt.congr ?_ heq
  exact (continuous_Ie.comp (continuous_const.add
    (continuous_fst_A.comp (continuous_id.sub continuous_const)))).continuousAt

/-! ### the basic test functions `T₀(M, Ψ) = 1_{M Ô} ⊗ Ψ ∘ LH⁻¹` -/

section T0

open MeasureTheory
open scoped SchwartzMap FourierTransform

/-- the basic test function -/
noncomputable def T0 (M : ℕ) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) : AdeleRing (𝓞 F) F → ℂ :=
  fun x => (box (M : F)).indicator (fun _ => (1 : ℂ)) x.2 * Ψ (LH.symm x.1)

lemma T0_of_mem (M : ℕ) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) (x : AdeleRing (𝓞 F) F)
    (hx : x.2 ∈ box (M : F)) : T0 M Ψ x = Ψ (LH.symm x.1) := by
  simp [T0, Set.indicator_of_mem hx]

lemma T0_of_not_mem (M : ℕ) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) (x : AdeleRing (𝓞 F) F)
    (hx : x.2 ∉ box (M : F)) : T0 M Ψ x = 0 := by
  simp [T0, Set.indicator_of_notMem hx]

lemma T0_eq_indicator (M : ℕ) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) :
    T0 M Ψ = {x : AdeleRing (𝓞 F) F | x.2 ∈ box (M : F)}.indicator
      (fun x => Ψ (LH.symm x.1)) := by
  funext x
  by_cases hx : x.2 ∈ box (M : F)
  · rw [T0_of_mem M Ψ x hx, Set.indicator_of_mem (show x ∈ {x : AdeleRing (𝓞 F) F |
      x.2 ∈ box (M : F)} from hx)]
  · rw [T0_of_not_mem M Ψ x hx, Set.indicator_of_notMem (show x ∉ {x : AdeleRing (𝓞 F) F |
      x.2 ∈ box (M : F)} from hx)]

lemma integrable_T0 (M : ℕ) (hM : M ≠ 0) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) :
    Integrable (T0 M Ψ) tamagawaAdelic := by
  rw [T0_eq_indicator, integrable_indicator_iff (measurableSet_boxA _ (by exact_mod_cast hM))]
  have := integrableOn_box M hM (fun t => Ψ (LH.symm t)) (Ψ.continuous.comp LH.symm.continuous)
    (by simpa using Ψ.integrable)
  exact this

lemma integrable_T0_psi (M : ℕ) (hM : M ≠ 0) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ))
    (y : AdeleRing (𝓞 F) F) :
    Integrable (fun x => T0 M Ψ x * stdAdelicCharacter (x * y)) tamagawaAdelic := by
  refine (integrable_T0 M hM Ψ).mul_bdd (c := 1) ?_ ?_
  · exact (continuous_psi.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => (norm_psi _).le

end T0


section T0Fourier

open MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace

lemma alg_mem_box_self (c : F) : algebraMap F (FiniteAdeleRing (𝓞 F) F) c ∈ box c := by
  intro v; rfl

lemma psi_fin_dual (M : ℕ) (hM : M ≠ 0) (n : Ix F → ℤ) (z : FiniteAdeleRing (𝓞 F) F)
    (hz : z ∈ box (M : F)) :
    stdAdelicCharacter (mkA 0 (z * algebraMap F (FiniteAdeleRing (𝓞 F) F) (etaN M n))) = 1 := by
  have hM' : (M : F) ≠ 0 := by exact_mod_cast hM
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (etaN (F := F) M n)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set u := algebraMap F (FiniteAdeleRing (𝓞 F) F) (M : F)⁻¹ * z
  have hu : u ∈ box (1 : F) := (mem_box_iff_mul _ hM' z).mp hz
  obtain ⟨r, hr⟩ := int_decomp b hb0 u hu
  obtain ⟨m, hm⟩ := exists_emb r
  have hz' : z = algebraMap F (FiniteAdeleRing (𝓞 F) F) ((M : F) * algebraMap (𝓞 F) F r) +
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (M : F) *
        (u - algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F r)) := by
    simp only [u, map_mul, mul_sub, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hM', map_one, one_mul]
    ring
  rw [hz', add_mul, show ∀ A B : FiniteAdeleRing (𝓞 F) F, mkA (0 : InfiniteAdeleRing F) (A + B) =
    mkA 0 A + mkA 0 B from fun A B => by rw [mkA_add, add_zero], psi_add]
  have h1 : stdAdelicCharacter (mkA 0 (algebraMap F (FiniteAdeleRing (𝓞 F) F)
      ((M : F) * algebraMap (𝓞 F) F r) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (etaN M n))) = 1 := by
    rw [← map_mul, psi_fin_alg]
    refine Ie_neg_alg_eq_one _ (∑ i, m i * n i) ?_
    rw [← hm, mul_assoc, ← nsmul_eq_mul, map_nsmul, trace_emb_etaN, nsmul_eq_mul]
    push_cast
    field_simp
  have h2 : stdAdelicCharacter (mkA 0 (algebraMap F (FiniteAdeleRing (𝓞 F) F) (M : F) *
      (u - algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F r)) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (etaN M n))) = 1 := by
    apply psi_fin_int
    have hmem : algebraMap F (FiniteAdeleRing (𝓞 F) F) (M : F) *
        (u - algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F r)) *
          algebraMap F (FiniteAdeleRing (𝓞 F) F) (etaN M n) ∈
        box ((M : F) * algebraMap (𝓞 F) F b * etaN M n) :=
      mul_mem_box (mul_mem_box (alg_mem_box_self _) hr) (alg_mem_box_self _)
    have hc : (M : F) * algebraMap (𝓞 F) F b * etaN M n = 1 * algebraMap (𝓞 F) F (M * a) := by
      rw [← hab, map_mul, map_natCast]
      have hbF : algebraMap (𝓞 F) F b ≠ 0 := by simpa using hb0
      field_simp
    rw [hc] at hmem
    exact box_mono_int 1 _ hmem
  rw [h1, h2, mul_one]

/-- scaling by `M` as a continuous linear equivalence -/
noncomputable def smulE (M : ℕ) (hM : M ≠ 0) :
    EuclideanSpace ℝ (Ix F) ≃L[ℝ] EuclideanSpace ℝ (Ix F) :=
  (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Ix F)) (M : ℝ)
    (by exact_mod_cast hM)).toContinuousLinearEquiv

/-- `Ψ_M(t) = Ψ(M t)` -/
noncomputable def PsiM (M : ℕ) (hM : M ≠ 0) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) :
    𝓢(EuclideanSpace ℝ (Ix F), ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (smulE M hM) Ψ

lemma PsiM_apply (M : ℕ) (hM : M ≠ 0) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ))
    (t : EuclideanSpace ℝ (Ix F)) : PsiM M hM Ψ t = Ψ ((M : ℝ) • t) := rfl

lemma inner_eucl_zpt (s : EuclideanSpace ℝ (Ix F)) (n : Ix F → ℤ) :
    ⟪s, AuxP.zpt n⟫ = ∑ i, s i * (n i : ℝ) := by
  simp [AuxP.zpt, PiLp.inner_apply, mul_comm]

lemma fourier_PsiM (M : ℕ) (hM : M ≠ 0) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) (n : Ix F → ℤ) :
    𝓕 (⇑(PsiM M hM Ψ)) (AuxP.zpt n) = ((M : ℝ) ^ Fintype.card (Ix F))⁻¹ •
      ∫ s, Ψ s * Complex.exp (-(2 * Real.pi * Complex.I) *
        (((∑ i, s i * (n i : ℝ)) / M : ℝ) : ℂ)) := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  rw [Real.fourier_eq]
  let f : EuclideanSpace ℝ (Ix F) → ℂ := fun s => Ψ s * Complex.exp (-(2 * Real.pi * Complex.I) *
      (((∑ i, s i * (n i : ℝ)) / M : ℝ) : ℂ))
  have hf : ∀ v : EuclideanSpace ℝ (Ix F),
      𝐞 (-⟪v, AuxP.zpt n⟫) • (PsiM M hM Ψ) v = f ((M : ℝ) • v) := by
    intro v
    have hs : (∑ i, ((M : ℝ) • v) i * (n i : ℝ)) / M = ∑ i, v i * (n i : ℝ) := by
      simp only [PiLp.smul_apply, smul_eq_mul]
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_; field_simp
    simp only [f]
    rw [hs, AuxP.fourierChar_smul, PsiM_apply, inner_eucl_zpt, AuxP.ex, mul_comm]
    congr 2; push_cast; ring
  simp_rw [hf]
  rw [Measure.integral_comp_smul, finrank_euclideanSpace]
  congr 1
  rw [abs_of_nonneg (by positivity)]

end T0Fourier


section T0Poisson

open MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace

lemma mul_alg_fst (x : AdeleRing (𝓞 F) F) (η : F) :
    (x * algebraMap F (AdeleRing (𝓞 F) F) η).1 = x.1 * algebraMap F (InfiniteAdeleRing F) η := rfl

lemma mul_alg_snd (x : AdeleRing (𝓞 F) F) (η : F) :
    (x * algebraMap F (AdeleRing (𝓞 F) F) η).2 = x.2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) η :=
  rfl

lemma Ie_LH_etaN (M : ℕ) (n : Ix F → ℤ) (s : EuclideanSpace ℝ (Ix F)) :
    Ie (LH s * algebraMap F (InfiniteAdeleRing F) (etaN M n)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (((∑ i, s i * (n i : ℝ)) / M : ℝ) : ℂ)) := by
  rw [Ie, trI_LH_etaN]

/-- Fourier transform of `T₀` on the dual lattice -/
lemma T0_fourier_dual (M : ℕ) (hM : M ≠ 0) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) (n : Ix F → ℤ) :
    adelicFourierFun (T0 M Ψ) (algebraMap F (AdeleRing (𝓞 F) F) (etaN M n)) =
      𝓕 (⇑(PsiM M hM Ψ)) (AuxP.zpt n) := by
  have hM' : (M : F) ≠ 0 := by exact_mod_cast hM
  unfold adelicFourierFun
  have hind : (fun x => T0 M Ψ x * stdAdelicCharacter (x * algebraMap F (AdeleRing (𝓞 F) F)
      (etaN M n))) = {x : AdeleRing (𝓞 F) F | x.2 ∈ box (M : F)}.indicator (fun x =>
        Ψ (LH.symm x.1) * stdAdelicCharacter (x * algebraMap F (AdeleRing (𝓞 F) F) (etaN M n))) := by
    funext x
    by_cases hx : x.2 ∈ box (M : F)
    · rw [T0_of_mem M Ψ x hx, Set.indicator_of_mem (show x ∈ {x : AdeleRing (𝓞 F) F |
        x.2 ∈ box (M : F)} from hx)]
    · rw [T0_of_not_mem M Ψ x hx, Set.indicator_of_notMem (show x ∉ {x : AdeleRing (𝓞 F) F |
        x.2 ∈ box (M : F)} from hx), zero_mul]
  rw [hind, integral_indicator (measurableSet_boxA _ hM')]
  have h1 : ∫ x in {x : AdeleRing (𝓞 F) F | x.2 ∈ box (M : F)}, Ψ (LH.symm x.1) *
      stdAdelicCharacter (x * algebraMap F (AdeleRing (𝓞 F) F) (etaN M n)) ∂tamagawaAdelic =
      ∫ x in {x : AdeleRing (𝓞 F) F | x.2 ∈ box (M : F)},
        (fun t => Ψ (LH.symm t) * Ie (t * algebraMap F (InfiniteAdeleRing F) (etaN M n))) x.1
          ∂tamagawaAdelic := by
    refine setIntegral_congr_fun (measurableSet_boxA _ hM') fun x hx => ?_
    rw [psi_split, mul_alg_fst, mul_alg_snd, psi_fin_dual M hM n x.2 hx, mul_one]
  rw [h1, integral_box M hM (fun t => Ψ (LH.symm t) * Ie (t * algebraMap F (InfiniteAdeleRing F)
    (etaN M n))) ((Ψ.continuous.comp LH.symm.continuous).mul
    (continuous_Ie.comp (continuous_id.mul continuous_const))), fourier_PsiM]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [Homeomorph.symm_apply_apply, Ie_LH_etaN]

/-- Fourier transform of `T₀` off the dual lattice -/
lemma T0_fourier_off (M : ℕ) (hM : M ≠ 0) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) (η : F)
    (hη : ¬ ∃ n, η = etaN M n) :
    adelicFourierFun (T0 M Ψ) (algebraMap F (AdeleRing (𝓞 F) F) η) = 0 := by
  have hM' : (M : F) ≠ 0 := by exact_mod_cast hM
  have : ∃ i, ¬ ∃ k : ℤ, (M : ℚ) * Algebra.trace ℚ F (integralBasis F i * η) = k := by
    by_contra h
    push Not at h
    exact hη (exists_etaN M hM η h)
  obtain ⟨i, hi⟩ := this
  set lam : F := (M : F) * integralBasis F i
  set a : AdeleRing (𝓞 F) F := mkA 0 (algebraMap F (FiniteAdeleRing (𝓞 F) F) lam)
  have hlam : algebraMap F (FiniteAdeleRing (𝓞 F) F) lam ∈ box (M : F) := by
    simp only [lam]
    rw [integralBasis_apply]
    exact alg_mem_box _ _
  have hT : ∀ x, T0 M Ψ (a + x) = T0 M Ψ x := by
    intro x
    have h1 : (a + x).1 = x.1 := by
      change (0 : InfiniteAdeleRing F) + x.1 = x.1; rw [zero_add]
    have h2 : (a + x).2 = algebraMap F (FiniteAdeleRing (𝓞 F) F) lam + x.2 := rfl
    by_cases hx : x.2 ∈ box (M : F)
    · rw [T0_of_mem M Ψ x hx, T0_of_mem M Ψ _ (by rw [h2]; exact add_mem_box hlam hx), h1]
    · have : (a + x).2 ∉ box (M : F) := by
        rw [h2]; intro h; apply hx
        have := sub_mem_box h hlam
        rwa [add_sub_cancel_left] at this
      rw [T0_of_not_mem M Ψ x hx, T0_of_not_mem M Ψ _ this]
  set c := stdAdelicCharacter (a * algebraMap F (AdeleRing (𝓞 F) F) η)
  have hc : c ≠ 1 := by
    have : a * algebraMap F (AdeleRing (𝓞 F) F) η =
        mkA 0 (algebraMap F (FiniteAdeleRing (𝓞 F) F) (lam * η)) := by
      rw [alg_eq_mkA η, mkA_mul, zero_mul]
      simp only [lam, map_mul]
    simp only [c]
    rw [this, psi_fin_alg]
    apply Ie_neg_alg_ne_one
    rintro ⟨k, hk⟩
    apply hi
    refine ⟨k, ?_⟩
    rw [← hk]
    simp only [lam]
    conv_rhs => rw [mul_assoc, ← nsmul_eq_mul, map_nsmul]
    rw [nsmul_eq_mul]
  unfold adelicFourierFun
  have hI : (∫ x, T0 M Ψ x * stdAdelicCharacter (x * algebraMap F (AdeleRing (𝓞 F) F) η)
      ∂tamagawaAdelic) = c * ∫ x, T0 M Ψ x *
        stdAdelicCharacter (x * algebraMap F (AdeleRing (𝓞 F) F) η) ∂tamagawaAdelic := by
    have := integral_add_left_eq_self (μ := (tamagawaAdelic (F := F)))
      (fun x => T0 M Ψ x * stdAdelicCharacter (x * algebraMap F (AdeleRing (𝓞 F) F) η)) a
    conv_lhs => rw [← this]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [hT, add_mul, psi_add, show stdAdelicCharacter (a * algebraMap F _ η) = c from rfl]
    ring
  set I := ∫ x, T0 M Ψ x * stdAdelicCharacter (x * algebraMap F (AdeleRing (𝓞 F) F) η)
    ∂tamagawaAdelic
  have : (1 - c) * I = 0 := by rw [sub_mul, one_mul, ← hI, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h).symm hc
  · exact h

lemma T0_alg (M : ℕ) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) (m : Ix F → ℤ) :
    T0 M Ψ (algebraMap F (AdeleRing (𝓞 F) F) ((M : F) * emb m)) = Ψ ((M : ℝ) • AuxP.zpt m) := by
  have : (algebraMap F (AdeleRing (𝓞 F) F) ((M : F) * emb m)).2 ∈ box (M : F) := by
    rw [adele_snd_alg, emb_int]; exact alg_mem_box _ _
  rw [T0_of_mem M Ψ _ this, adele_fst_alg, LH_symm_alg_Memb, ← Nat.cast_smul_eq_nsmul ℝ]

/-- Poisson summation for `T₀` -/
lemma T0_poisson (M : ℕ) (hM : M ≠ 0) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) :
    Summable (fun ξ : F => T0 M Ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ)) ∧
    Summable (fun η : F => adelicFourierFun (T0 M Ψ) (algebraMap F (AdeleRing (𝓞 F) F) η)) ∧
    ∑' ξ : F, T0 M Ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ) =
      ∑' η : F, adelicFourierFun (T0 M Ψ) (algebraMap F (AdeleRing (𝓞 F) F) η) := by
  have hM' : (M : F) ≠ 0 := by exact_mod_cast hM
  obtain ⟨h1, h2, h3⟩ := AuxP.poisson (PsiM M hM Ψ)
  let j : (Ix F → ℤ) → F := fun m => (M : F) * emb m
  have hj : Function.Injective j := fun a b h => emb_injective (mul_left_cancel₀ hM' h)
  have hsuppL : ∀ ξ ∉ Set.range j, T0 M Ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ) = 0 := by
    intro ξ hξ
    apply T0_of_not_mem
    rw [adele_snd_alg]
    intro h
    obtain ⟨m, hm⟩ := (alg_mem_boxM_iff M hM ξ).mp h
    exact hξ ⟨m, hm.symm⟩
  have hL : (fun ξ : F => T0 M Ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ)) ∘ j =
      fun m => PsiM M hM Ψ (AuxP.zpt m) := by
    funext m; simp only [Function.comp_apply, j, T0_alg, PsiM_apply]
  have hj' : Function.Injective (etaN (F := F) M) := etaN_injective M hM
  have hsuppR : ∀ η ∉ Set.range (etaN (F := F) M),
      adelicFourierFun (T0 M Ψ) (algebraMap F (AdeleRing (𝓞 F) F) η) = 0 := by
    intro η hη
    exact T0_fourier_off M hM Ψ η (fun ⟨n, hn⟩ => hη ⟨n, hn.symm⟩)
  have hR : (fun η : F => adelicFourierFun (T0 M Ψ) (algebraMap F (AdeleRing (𝓞 F) F) η)) ∘
      etaN M = fun n => 𝓕 (⇑(PsiM M hM Ψ)) (AuxP.zpt n) := by
    funext n; simp only [Function.comp_apply, T0_fourier_dual M hM]
  refine ⟨(hj.summable_iff hsuppL).mp (hL ▸ h1), (hj'.summable_iff hsuppR).mp (hR ▸ h2), ?_⟩
  rw [← hj.tsum_eq (fun ξ hξ => by
      by_contra h; exact hξ (hsuppL ξ h)),
    ← hj'.tsum_eq (fun η hη => by by_contra h; exact hη (hsuppR η h))]
  have e1 := congrFun hL
  have e2 := congrFun hR
  simp only [Function.comp_apply] at e1 e2
  simp only [e1, e2]
  exact h3

end T0Poisson

section Norm


theorem fin_mul_inv (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    (g : AdeleRing (𝓞 F) F).2 v * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
  have h := g.mul_inv
  have := congrArg (fun a : AdeleRing (𝓞 F) F ↦ a.2 v) h
  exact this

theorem norm_eq_one_of_mem {v : HeightOneSpectrum (𝓞 F)} {x y : v.adicCompletion F}
    (hxy : x * y = 1) (hx : x ∈ v.adicCompletionIntegers F) (hy : y ∈ v.adicCompletionIntegers F) :
    ‖x‖ = 1 := by
  have h1 : ‖x‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr hx
  have h2 : ‖y‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr hy
  have h3 : ‖x‖ * ‖y‖ = 1 := by rw [← norm_mul, hxy, norm_one]
  have h4 : 0 ≤ ‖x‖ := norm_nonneg _
  have h5 : 0 ≤ ‖y‖ := norm_nonneg _
  nlinarith

theorem fin_norm_pos (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    0 < ‖(g : AdeleRing (𝓞 F) F).2 v‖ := by
  apply norm_pos_iff.mpr
  intro h
  have := fin_mul_inv g v
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem eventually_norm_eq_one (g : IdeleGroup F) :
    ∀ᶠ v in cofinite, ‖(g : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
  filter_upwards [(g : AdeleRing (𝓞 F) F).2.2, ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2.2]
    with v h1 h2
  exact norm_eq_one_of_mem (fin_mul_inv g v) h1 h2

theorem hasFiniteMulSupport_norm (g : IdeleGroup F) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) ↦ ‖(g : AdeleRing (𝓞 F) F).2 v‖).Finite := by
  have := eventually_norm_eq_one g
  rw [Filter.eventually_cofinite] at this
  exact this

theorem ideleNorm_mul (g h : IdeleGroup F) : ideleNorm (g * h) = ideleNorm g * ideleNorm h := by
  unfold ideleNorm
  have e1 : ∀ w : InfinitePlace F, ‖((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult =
      ‖(g : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult * ‖(h : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult := by
    intro w
    rw [← mul_pow, ← norm_mul]
    rfl
  have e2 : ∀ v : HeightOneSpectrum (𝓞 F), ‖((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ =
      ‖(g : AdeleRing (𝓞 F) F).2 v‖ * ‖(h : AdeleRing (𝓞 F) F).2 v‖ := by
    intro v
    rw [← norm_mul]
    rfl
  simp only [e1, e2, Finset.prod_mul_distrib]
  rw [finprod_mul_distrib (hasFiniteMulSupport_norm g) (hasFiniteMulSupport_norm h)]
  ring

theorem ideleNorm_pos (g : IdeleGroup F) : 0 < ideleNorm g := by
  unfold ideleNorm
  apply mul_pos
  · apply Finset.prod_pos
    intro w _
    apply pow_pos
    apply norm_pos_iff.mpr
    intro h0
    have h := g.mul_inv
    have := congrArg (fun a : AdeleRing (𝓞 F) F ↦ a.1 w) h
    change (g : AdeleRing (𝓞 F) F).1 w * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w = 1
      at this
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  · exact finprod_induction (0 < ·) zero_lt_one (fun _ _ ↦ mul_pos) fun v ↦ fin_norm_pos g v

theorem ideleNorm_eq_infNorm (g : IdeleGroup F) (hg : ∀ v : HeightOneSpectrum (𝓞 F),
    (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F ∧
    ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F) :
    ideleNorm g = ∏ w : InfinitePlace F, ‖(g : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult := by
  unfold ideleNorm
  have : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(g : AdeleRing (𝓞 F) F).2 v‖) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v ↦ norm_eq_one_of_mem (fin_mul_inv g v) (hg v).1 (hg v).2
  rw [this, mul_one]

end Norm

section Principal


theorem fin_prod_eq (x : F) (hx : x ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : v.adicCompletion F)‖ = |Algebra.norm ℚ x|⁻¹ := by
  have e : ∀ v : HeightOneSpectrum (𝓞 F), ‖(x : v.adicCompletion F)‖ =
      (FinitePlace.equivHeightOneSpectrum.symm v) x := fun v ↦ rfl
  simp only [e]
  rw [finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F)).symm
    (f := fun w : FinitePlace F ↦ w x)]
  exact FinitePlace.prod_eq_inv_abs_norm hx

theorem inf_prod_eq (x : F) :
    ∏ w : InfinitePlace F, ‖(x : w.Completion)‖ ^ w.mult = |Algebra.norm ℚ x| := by
  have := InfiniteAdeleRing.coe_norm_eq_abs_norm x
  rw [InfiniteAdeleRing.norm_def] at this
  exact this

theorem product_formula (x : F) (hx : x ≠ 0) :
    (∏ w : InfinitePlace F, ‖(x : w.Completion)‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : v.adicCompletion F)‖ = 1 := by
  rw [inf_prod_eq, fin_prod_eq x hx]
  have hN : Algebra.norm ℚ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  rw [← Rat.cast_mul, mul_inv_cancel₀ (abs_ne_zero.mpr hN), Rat.cast_one]

theorem ideleNorm_principal (ξ : Fˣ) : ideleNorm (principalIdele F ξ) = 1 :=
  product_formula (ξ : F) ξ.ne_zero



end Principal

section Ideals


open scoped nonZeroDivisors

theorem valued_eq_one_of_mem {v : HeightOneSpectrum (𝓞 F)} {x y : v.adicCompletion F}
    (hxy : x * y = 1) (hx : x ∈ v.adicCompletionIntegers F) (hy : y ∈ v.adicCompletionIntegers F) :
    Valued.v x = 1 := by
  have h1 : Valued.v x * Valued.v y = 1 := by rw [← map_mul, hxy, map_one]
  have hx' : Valued.v x ≤ 1 := hx
  have hy' : Valued.v y ≤ 1 := hy
  refine le_antisymm hx' ?_
  calc (1 : ℤᵐ⁰) = Valued.v x * Valued.v y := h1.symm
    _ ≤ Valued.v x * 1 := mul_le_mul' le_rfl hy'
    _ = Valued.v x := mul_one _

theorem fin_ne_zero (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    (g : AdeleRing (𝓞 F) F).2 v ≠ 0 := by
  intro h
  have := fin_mul_inv g v
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem eventually_valued_eq_one (g : IdeleGroup F) :
    ∀ᶠ v in cofinite, Valued.v ((g : AdeleRing (𝓞 F) F).2 v) = 1 := by
  filter_upwards [(g : AdeleRing (𝓞 F) F).2.2, ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2.2]
    with v h1 h2
  exact valued_eq_one_of_mem (fin_mul_inv g v) h1 h2

/-- The finite valuation of an idele. -/
noncomputable def ideleExponent (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) : ℤ :=
  -WithZero.log (Valued.v ((g : AdeleRing (𝓞 F) F).2 v))

theorem eventually_ideleExponent_eq_zero (g : IdeleGroup F) :
    ∀ᶠ v in cofinite, ideleExponent g v = 0 :=
  (eventually_valued_eq_one g).mono fun v hv ↦ by simp [ideleExponent, hv]

/-- The prime of a finite place as a unit fractional ideal. -/
noncomputable def primeUnit (v : HeightOneSpectrum (𝓞 F)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  Units.mk0 ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F))
    (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

/-- The fractional ideal of an idele. -/
noncomputable def ideleFractionalIdeal : IdeleGroup F →* (FractionalIdeal (𝓞 F)⁰ F)ˣ where
  toFun g := ∏ᶠ v : HeightOneSpectrum (𝓞 F), (primeUnit v) ^ ideleExponent g v
  map_one' := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    change _ ^ (-WithZero.log (Valued.v (1 : v.adicCompletion F))) = _
    simp
  map_mul' g h := by
    let P (v : HeightOneSpectrum (𝓞 F)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ := primeUnit v
    change (∏ᶠ v, P v ^ ideleExponent (g * h) v) =
      (∏ᶠ v, P v ^ ideleExponent g v) * (∏ᶠ v, P v ^ ideleExponent h v)
    have hs (a : IdeleGroup F) :
        (Function.mulSupport fun v ↦ P v ^ ideleExponent a v).Finite :=
      eventually_cofinite.mp ((eventually_ideleExponent_eq_zero a).mono
        fun v hv ↦ by simp [hv])
    rw [← finprod_mul_distrib (hs g) (hs h)]
    apply finprod_congr
    intro v
    rw [← zpow_add]
    congr 1
    change -WithZero.log (Valued.v ((g : AdeleRing (𝓞 F) F).2 v * (h : AdeleRing (𝓞 F) F).2 v)) =
      -WithZero.log (Valued.v ((g : AdeleRing (𝓞 F) F).2 v)) +
        -WithZero.log (Valued.v ((h : AdeleRing (𝓞 F) F).2 v))
    rw [map_mul, WithZero.log_mul, neg_add]
    · exact (Valuation.ne_zero_iff _).mpr (fin_ne_zero g v)
    · exact (Valuation.ne_zero_iff _).mpr (fin_ne_zero h v)

theorem coe_ideleFractionalIdeal (g : IdeleGroup F) :
    (ideleFractionalIdeal g : FractionalIdeal (𝓞 F)⁰ F) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ ideleExponent g v := by
  change Units.coeHom _ (∏ᶠ v : HeightOneSpectrum (𝓞 F), (primeUnit v) ^ ideleExponent g v) = _
  rw [map_finprod]
  · apply finprod_congr
    intro v
    exact Units.val_zpow_eq_zpow_val (primeUnit v) _
  · exact eventually_cofinite.mp ((eventually_ideleExponent_eq_zero g).mono
      fun v hv ↦ by simp [hv])

theorem ideleFractionalIdeal_principal (x : Fˣ) :
    ideleFractionalIdeal (principalIdele F x) = toPrincipalIdeal (𝓞 F) F x := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (𝓞 F)⁰ (x : F)
  have hn : n ≠ 0 := by
    rintro rfl
    exact x.ne_zero (by rw [← hnd, IsFractionRing.mk'_eq_div, map_zero, zero_div])
  apply Units.ext
  rw [coe_ideleFractionalIdeal, coe_toPrincipalIdeal, ← hnd,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization_principal_fraction (K := F) hn d]
  apply finprod_congr
  intro v
  congr 1
  change -WithZero.log (Valued.v ((x : F) : v.adicCompletion F)) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← hnd,
    HeightOneSpectrum.valuation_of_mk', v.intValuation_if_neg hn,
    v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero d), WithZero.log_div,
    WithZero.log_exp, WithZero.log_exp]
  · ring
  · exact WithZero.exp_ne_zero
  · exact WithZero.exp_ne_zero

theorem exists_integral_fin_idele (g : IdeleGroup F)
    (hg : ClassGroup.mk F (ideleFractionalIdeal g) = 1) :
    ∃ x : Fˣ, ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (((g / principalIdele F x : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v) = 1 := by
  obtain ⟨x, hx⟩ := (ClassGroup.mk_eq_one_iff.mp hg).principal
  have hx' : (ideleFractionalIdeal g : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton _ x := by
    rwa [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_spanSingleton]
  have hx0 : x ≠ 0 := fun h ↦ (ideleFractionalIdeal g).ne_zero
    (hx'.trans (FractionalIdeal.spanSingleton_eq_zero_iff.mpr h))
  let u := Units.mk0 x hx0
  have hI : ideleFractionalIdeal (g / principalIdele F u) = 1 := by
    rw [map_div, ideleFractionalIdeal_principal, div_eq_one]
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    exact hx'
  refine ⟨u, fun v ↦ ?_⟩
  let a := g / principalIdele F u
  have hc := FractionalIdeal.count_finprod F v (ideleExponent a)
    (eventually_ideleExponent_eq_zero a)
  rw [← coe_ideleFractionalIdeal, hI, Units.val_one, FractionalIdeal.count_one] at hc
  have hv : WithZero.log (Valued.v ((a : AdeleRing (𝓞 F) F).2 v)) = 0 := neg_eq_zero.mp hc.symm
  have hv0 : Valued.v ((a : AdeleRing (𝓞 F) F).2 v) ≠ (0 : ℤᵐ⁰) :=
    (Valuation.ne_zero_iff _).mpr (fin_ne_zero a v)
  change Valued.v ((a : AdeleRing (𝓞 F) F).2 v) = (1 : ℤᵐ⁰)
  rw [← WithZero.exp_log hv0, hv, WithZero.exp_zero]

end Ideals



/-! ### multiplication on `F_∞` in coordinates and its determinant -/

section Det

/-- `t ↦ LH⁻¹(LH t · y)` -/
noncomputable def mulA (y : InfiniteAdeleRing F) :
    EuclideanSpace ℝ (Ix F) →+ EuclideanSpace ℝ (Ix F) where
  toFun t := LH.symm (LH t * y)
  map_zero' := by rw [LH_zero, zero_mul]; exact map_zero (LHa (F := F)).symm
  map_add' a b := by rw [LH_add, add_mul, LH_symm_add]

lemma continuous_mulA (y : InfiniteAdeleRing F) : Continuous (mulA y) :=
  LH.symm.continuous.comp ((LH.continuous).mul continuous_const)

/-- `mulA` as a real linear map -/
noncomputable def mulL (y : InfiniteAdeleRing F) :
    EuclideanSpace ℝ (Ix F) →ₗ[ℝ] EuclideanSpace ℝ (Ix F) :=
  ((mulA y).toRealLinearMap (continuous_mulA y)).toLinearMap

lemma mulL_apply (y : InfiniteAdeleRing F) (t : EuclideanSpace ℝ (Ix F)) :
    mulL y t = LH.symm (LH t * y) := rfl

/-- `ξ ↦ LH⁻¹(ξ)` on `F` -/
noncomputable def PhiF : F →+ EuclideanSpace ℝ (Ix F) where
  toFun ξ := LH.symm (algebraMap F (InfiniteAdeleRing F) ξ)
  map_zero' := by rw [map_zero]; exact map_zero (LHa (F := F)).symm
  map_add' a b := by rw [map_add, LH_symm_add]

lemma zpt_single (i : Ix F) : AuxP.zpt (Pi.single i (1 : ℤ)) = EuclideanSpace.single i (1 : ℝ) := by
  ext j; simp [AuxP.zpt, Pi.single_apply, PiLp.single_apply]

lemma PhiF_basis (i : Ix F) : PhiF (integralBasis F i) = EuclideanSpace.single i (1 : ℝ) := by
  have : integralBasis F i = emb (Pi.single i 1) := by
    simp [emb, Pi.single_apply]
  change LH.symm _ = _
  rw [this, LH_symm_alg_emb, zpt_single]

lemma PhiF_apply (ξ : F) (j : Ix F) : (PhiF ξ) j = ((integralBasis F).repr ξ j : ℝ) := by
  conv_lhs => rw [← (integralBasis F).sum_repr ξ]
  rw [map_sum]
  simp only [map_rat_smul (PhiF (F := F)), PhiF_basis]
  simp [Rat.smul_def, Finset.sum_apply, Pi.single_apply]

lemma toMatrix_mulL_alg (ξ : F) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Ix F) ℝ).toBasis
      (EuclideanSpace.basisFun (Ix F) ℝ).toBasis (mulL (algebraMap F (InfiniteAdeleRing F) ξ)) =
    (Algebra.leftMulMatrix (integralBasis F) ξ).map (Rat.castHom ℝ) := by
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  rw [mulL_apply, ← zpt_single, LH_zpt, ← map_mul]
  have : emb (Pi.single j (1 : ℤ)) * ξ = ξ * integralBasis F j := by
    rw [mul_comm]; congr 1; simp [emb, Pi.single_apply]
  rw [this]
  exact PhiF_apply _ i

lemma det_mulL_alg (ξ : F) :
    LinearMap.det (mulL (algebraMap F (InfiniteAdeleRing F) ξ)) = ((Algebra.norm ℚ ξ : ℚ) : ℝ) := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Ix F) ℝ).toBasis, toMatrix_mulL_alg,
    Algebra.norm_eq_matrix_det (integralBasis F)]
  exact ((Rat.castHom ℝ).map_det _).symm

lemma continuous_det_mulL : Continuous (fun y : InfiniteAdeleRing F => LinearMap.det (mulL y)) := by
  have : (fun y : InfiniteAdeleRing F => LinearMap.det (mulL y)) = fun y =>
      (LinearMap.toMatrix (EuclideanSpace.basisFun (Ix F) ℝ).toBasis
        (EuclideanSpace.basisFun (Ix F) ℝ).toBasis (mulL y)).det := by
    funext y; rw [LinearMap.det_toMatrix]
  rw [this]
  refine Continuous.matrix_det ?_
  refine continuous_matrix fun i j => ?_
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr, mulL_apply]
  exact (PiLp.continuous_apply 2 _ i).comp (LH.symm.continuous.comp (continuous_const.mul
    continuous_id))

lemma continuous_infNormA : Continuous (fun y : InfiniteAdeleRing F => ‖y‖) := by
  simp only [InfiniteAdeleRing.norm_def]
  exact continuous_finsetProd _ fun w _ => ((continuous_apply w).norm).pow _

lemma abs_det_mulL (y : InfiniteAdeleRing F) : |LinearMap.det (mulL y)| = ‖y‖ := by
  have h := (InfiniteAdeleRing.denseRange_algebraMap F).equalizer
    (continuous_abs.comp continuous_det_mulL) continuous_infNormA (funext fun ξ => by
      simp only [Function.comp_apply, det_mulL_alg, InfiniteAdeleRing.coe_norm_eq_abs_norm]
      push_cast; rfl)
  exact congrFun h y

end Det


/-! ### the modulus of multiplication by an idele -/

section Modulus

open MeasureTheory

/-- multiplication by an idele -/
noncomputable def mulG (g : IdeleGroup F) (x : AdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F :=
  x * (g : AdeleRing (𝓞 F) F)

lemma continuous_mulG (g : IdeleGroup F) : Continuous (mulG g) :=
  continuous_id.mul continuous_const

lemma mulG_mulG_inv (g : IdeleGroup F) (x : AdeleRing (𝓞 F) F) : mulG g (mulG g⁻¹ x) = x := by
  simp only [mulG, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

lemma mulG_inv_mulG (g : IdeleGroup F) (x : AdeleRing (𝓞 F) F) : mulG g⁻¹ (mulG g x) = x := by
  simp only [mulG, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

lemma preimage_mulG (g : IdeleGroup F) (s : Set (AdeleRing (𝓞 F) F)) :
    mulG g ⁻¹' s = mulG g⁻¹ '' s := by
  ext x
  constructor
  · intro hx; exact ⟨mulG g x, hx, mulG_inv_mulG g x⟩
  · rintro ⟨y, hy, rfl⟩; change mulG g (mulG g⁻¹ y) ∈ s; rwa [mulG_mulG_inv]

/-- pushforward of the Tamagawa measure by multiplication by `g` -/
noncomputable def muG (g : IdeleGroup F) : Measure (AdeleRing (𝓞 F) F) :=
  Measure.map (mulG g) tamagawaAdelic

lemma muG_apply (g : IdeleGroup F) (s : Set (AdeleRing (𝓞 F) F)) (hs : MeasurableSet s) :
    muG g s = tamagawaAdelic (mulG g ⁻¹' s) :=
  Measure.map_apply (continuous_mulG g).measurable hs

instance muG_leftInv (g : IdeleGroup F) : (muG g).IsAddLeftInvariant := by
  refine ⟨fun a => ?_⟩
  rw [muG, Measure.map_map (measurable_const_add a) (continuous_mulG g).measurable]
  have : (fun x => a + x) ∘ mulG g = mulG g ∘ (fun x => mulG g⁻¹ a + x) := by
    funext x; simp only [Function.comp_apply, mulG, add_mul, mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, mul_one]
  rw [this, ← Measure.map_map (continuous_mulG g).measurable (measurable_const_add _),
    MeasureTheory.map_add_left_eq_self]

instance muG_finite (g : IdeleGroup F) : IsFiniteMeasureOnCompacts (muG g) := by
  refine ⟨fun K hK => ?_⟩
  rw [muG_apply g K hK.isClosed.measurableSet, preimage_mulG]
  exact (hK.image (continuous_mulG g⁻¹)).measure_lt_top

/-- the modulus of `g` -/
noncomputable def kappa (g : IdeleGroup F) : NNReal :=
  Measure.addHaarScalarFactor (muG g) tamagawaAdelic

/-- exhausting compact sets -/
def Cx (j : ℕ) : Set (AdeleRing (𝓞 F) F) :=
  {x | ‖LH.symm x.1‖ ≤ j ∧ x.2 ∈ box ((j.factorial : F)⁻¹)}

lemma fact_ne (j : ℕ) : ((j.factorial : F)⁻¹) ≠ 0 :=
  inv_ne_zero (by exact_mod_cast (Nat.factorial_pos j).ne')

lemma isCompact_closure_sub_Cx (j : ℕ) (s : Set (AdeleRing (𝓞 F) F)) (hs : s ⊆ Cx j) :
    IsCompact (closure s) := by
  have hK := isCompact_prodImage (Metric.closedBall (0 : EuclideanSpace ℝ (Ix F)) j)
    (isCompact_closedBall _ _) _ (fact_ne (F := F) j)
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  intro x hx
  obtain ⟨h1, h2⟩ := hs hx
  exact subset_prodImage _ _ ⟨h2, by simpa using h1⟩

lemma box_inv_mono (a b : ℕ) (hab : a ∣ b) (hb : b ≠ 0) :
    box ((a : F)⁻¹) ⊆ box ((b : F)⁻¹) := by
  obtain ⟨q, rfl⟩ := hab
  have hq : (q : F) ≠ 0 := by
    intro h; apply hb; simp only [Nat.cast_eq_zero] at h; simp [h]
  intro z hz v
  refine (hz v).trans ?_
  have : ((a * q : ℕ) : F)⁻¹ * (q : F) = (a : F)⁻¹ := by
    rw [Nat.cast_mul, mul_inv, mul_assoc, inv_mul_cancel₀ hq, mul_one]
  rw [← this, map_mul, map_mul]
  calc Valued.v (algebraMap F (v.adicCompletion F) ((a * q : ℕ) : F)⁻¹) *
        Valued.v (algebraMap F (v.adicCompletion F) (q : F))
      ≤ Valued.v (algebraMap F (v.adicCompletion F) ((a * q : ℕ) : F)⁻¹) * 1 := by
        refine mul_le_mul' le_rfl ?_
        have := val_int_le_one v (q : 𝓞 F)
        simpa using this
    _ = _ := mul_one _

/-- clearing denominators of a finite adele by an integer -/
lemma exists_den (z : FiniteAdeleRing (𝓞 F) F) :
    ∃ N : ℕ, N ≠ 0 ∧ z ∈ box ((N : F)⁻¹) := by
  obtain ⟨ξ, hξ⟩ := exists_sub_int z
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) ξ
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set N := Ideal.absNorm (Ideal.span {b})
  have hN : N ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨N, hN, ?_⟩
  have hN' : (N : F) ≠ 0 := by exact_mod_cast hN
  rw [mem_box_iff_mul _ (inv_ne_zero hN'), inv_inv, mem_box_one]
  intro v
  have hbF : algebraMap (𝓞 F) F b ≠ 0 := by simpa using hb0
  have hz : z v = (z v - algebraMap F (v.adicCompletion F)
      (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b)) +
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) := by ring
  change Valued.v (algebraMap F (v.adicCompletion F) (N : F) * z v) ≤ 1
  rw [hz, mul_add]
  refine Valuation.map_add_le _ ?_ ?_
  · rw [map_mul]
    calc _ ≤ (1 : ℤᵐ⁰) * 1 := mul_le_mul' (by simpa using val_int_le_one v (N : 𝓞 F)) (hξ v)
      _ = 1 := one_mul 1
  · rw [← map_mul]
    have : (N : F) * (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) = algebraMap (𝓞 F) F (c * a) := by
      have hc' : ((N : 𝓞 F) : F) = algebraMap (𝓞 F) F c * algebraMap (𝓞 F) F b := by
        rw [← map_mul, ← hc]
      rw [map_mul, show (N : F) = ((N : 𝓞 F) : F) by simp, hc']
      field_simp
    rw [this]
    exact val_int_le_one v _

lemma Cx_mono : Monotone (Cx (F := F)) := by
  intro a b hab x ⟨h1, h2⟩
  refine ⟨h1.trans (by exact_mod_cast hab), box_inv_mono _ _ (Nat.factorial_dvd_factorial hab)
    (Nat.factorial_pos b).ne' h2⟩

lemma iUnion_Cx : (⋃ j, Cx (F := F) j) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨N, hN, hx⟩ := exists_den x.2
  obtain ⟨j, hj⟩ := exists_nat_ge (max ‖LH.symm x.1‖ N)
  refine Set.mem_iUnion.mpr ⟨j, (le_max_left _ _).trans hj, ?_⟩
  have hNj : N ≤ j := by exact_mod_cast (le_max_right _ _).trans hj
  exact box_inv_mono _ _ (Nat.dvd_factorial (Nat.pos_of_ne_zero hN) hNj)
    (Nat.factorial_pos j).ne' hx

lemma muG_eq (g : IdeleGroup F) : muG g = (kappa g : ENNReal) • tamagawaAdelic := by
  ext s hs
  rw [Measure.smul_apply, smul_eq_mul]
  have hU : s = ⋃ j, s ∩ Cx j := by
    rw [← Set.inter_iUnion, iUnion_Cx, Set.inter_univ]
  have hmono : Monotone (fun j => s ∩ Cx (F := F) j) := fun a b hab =>
    Set.inter_subset_inter_right _ (Cx_mono hab)
  rw [hU, hmono.measure_iUnion, hmono.measure_iUnion, ENNReal.mul_iSup]
  refine iSup_congr fun j => ?_
  have := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure (muG g) tamagawaAdelic
    (isCompact_closure_sub_Cx j (s ∩ Cx j) Set.inter_subset_right)
  rw [this]; rfl

lemma FD1_compact_closure : IsCompact (closure (FD (F := F) 1)) := by
  let Kc : Set (EuclideanSpace ℝ (Ix F)) := {s | ∀ i, s i ∈ Set.Icc (0 : ℝ) 1}
  have hKc : IsCompact Kc := by
    have : Kc = (fun s : EuclideanSpace ℝ (Ix F) => (WithLp.ofLp s)) ⁻¹'
        (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1) := by
      ext s
      simp only [Kc, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]
    rw [this]
    exact (PiLp.homeomorph 2 _ ).isCompact_preimage.mpr (isCompact_univ_pi fun _ => isCompact_Icc)
  have hK := isCompact_prodImage Kc hKc (1 : F) one_ne_zero
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro x ⟨h1, h2⟩
  exact subset_prodImage _ _ ⟨by exact_mod_cast h1, fun i => ⟨(h2 i).1, by exact_mod_cast (h2 i).2.le⟩⟩

lemma kappa_eq (g : IdeleGroup F) :
    (kappa g : ENNReal) = tamagawaAdelic (mulG g ⁻¹' FD 1) := by
  have h1 := congrArg (fun μ : Measure (AdeleRing (𝓞 F) F) => μ (FD 1)) (muG_eq g)
  simp only [Measure.smul_apply, smul_eq_mul, tam_FDM 1 one_ne_zero, mul_one] at h1
  rw [← h1, muG_apply g _ (measurableSet_FD 1 one_ne_zero)]

lemma kappa_mul (g h : IdeleGroup F) : kappa (g * h) = kappa g * kappa h := by
  have e : muG (g * h) = Measure.map (mulG h) (muG g) := by
    rw [muG, muG, Measure.map_map (continuous_mulG h).measurable (continuous_mulG g).measurable]
    congr 1
    funext x; simp only [Function.comp_apply, mulG, Units.val_mul, mul_assoc]
  have e2 : muG (g * h) = ((kappa g : ENNReal) * kappa h) • tamagawaAdelic := by
    rw [e, muG_eq g, Measure.map_smul, ← muG, muG_eq h, smul_smul]
  have h1 := congrArg (fun μ : Measure (AdeleRing (𝓞 F) F) => μ (FD 1)) e2
  have h2 := congrArg (fun μ : Measure (AdeleRing (𝓞 F) F) => μ (FD 1)) (muG_eq (g * h))
  simp only [Measure.smul_apply, smul_eq_mul, tam_FDM 1 one_ne_zero, mul_one] at h1 h2
  rw [h2] at h1
  exact_mod_cast h1

lemma principal_coe (ξ : Fˣ) :
    ((principalIdele F ξ : IdeleGroup F) : AdeleRing (𝓞 F) F) =
      algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) := rfl

lemma kappa_principal (ξ : Fˣ) : kappa (principalIdele F ξ) = 1 := by
  have h := kappa_eq (principalIdele F ξ)
  rw [tam_FD _ ((measurableSet_FD 1 one_ne_zero).preimage (continuous_mulG _).measurable)] at h
  · exact_mod_cast h
  · intro x
    obtain ⟨ζ, hζ, huniq⟩ := FD_unique 1 one_ne_zero (x * algebraMap F _ (ξ : F))
    refine ⟨ζ / ξ, ?_, ?_⟩
    · beta_reduce
      rw [Set.mem_preimage, mulG, principal_coe, add_mul, ← map_mul,
        div_mul_cancel₀ _ ξ.ne_zero]
      exact hζ
    · intro η hη
      beta_reduce at hη
      rw [Set.mem_preimage, mulG, principal_coe, add_mul, ← map_mul] at hη
      rw [← huniq _ hη, mul_div_cancel_right₀ _ ξ.ne_zero]

end Modulus


section Modulus2

open MeasureTheory

lemma infA_ne_zero (u : IdeleGroup F) (w : InfinitePlace F) : (u : AdeleRing (𝓞 F) F).1 w ≠ 0 := by
  intro h
  have h1 := congrArg (fun a : AdeleRing (𝓞 F) F => a.1 w) u.mul_inv
  change (u : AdeleRing (𝓞 F) F).1 w * ((u⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w = 1 at h1
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

lemma infA_norm_pos (u : IdeleGroup F) : 0 < ‖(u : AdeleRing (𝓞 F) F).1‖ := by
  rw [InfiniteAdeleRing.norm_def]
  exact Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr (infA_ne_zero u w)) _

lemma kappa_unit (u : IdeleGroup F)
    (hu : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((u : AdeleRing (𝓞 F) F).2 v) = 1) :
    (kappa u : ℝ) = ‖(u : AdeleRing (𝓞 F) F).1‖⁻¹ := by
  have h := kappa_eq u
  set y := (u : AdeleRing (𝓞 F) F).1
  have hset : mulG u ⁻¹' FD 1 = {x : AdeleRing (𝓞 F) F | x.2 ∈ box ((1 : ℕ) : F) ∧
      LH.symm x.1 ∈ (mulL y) ⁻¹' cube 1} := by
    ext x
    simp only [Set.mem_preimage, FD, Set.mem_ofPred_eq, mulG]
    have e1 : (x * (u : AdeleRing (𝓞 F) F)).2 ∈ box ((1 : ℕ) : F) ↔ x.2 ∈ box ((1 : ℕ) : F) := by
      simp only [Nat.cast_one, mem_box_one]
      refine forall_congr' fun v => ?_
      change Valued.v (x.2 v * (u : AdeleRing (𝓞 F) F).2 v) ≤ 1 ↔ _
      rw [map_mul, hu v, mul_one]
    have e2 : LH.symm (x * (u : AdeleRing (𝓞 F) F)).1 = mulL y (LH.symm x.1) := by
      rw [mulL_apply, Homeomorph.apply_symm_apply]; rfl
    rw [e1, e2]
  have hdet : LinearMap.det (mulL y) ≠ 0 := by
    intro h0
    have := abs_det_mulL y
    rw [h0, abs_zero] at this
    exact (infA_norm_pos u).ne' this.symm
  rw [hset, ← muM_apply 1 one_ne_zero _ ((measurableSet_cube 1).preimage
    (LinearMap.continuous_of_finiteDimensional (mulL y)).measurable), muM_eq 1 one_ne_zero] at h
  simp only [Nat.cast_one, one_pow, inv_one, one_smul] at h
  rw [Measure.addHaar_preimage_linearMap _ hdet, volume_cube, Nat.cast_one, one_pow, mul_one,
    abs_inv, abs_det_mulL] at h
  have : (kappa u : ℝ) = (ENNReal.ofReal ‖y‖⁻¹).toReal := by
    rw [← h]; rfl
  rw [this]; exact ENNReal.toReal_ofReal (inv_nonneg.mpr (infA_norm_pos u).le)

lemma kappa_one : kappa (1 : IdeleGroup F) = 1 := by
  have := kappa_principal (F := F) 1
  rwa [map_one] at this

lemma kappa_pow (g : IdeleGroup F) (n : ℕ) : kappa (g ^ n) = kappa g ^ n := by
  induction n with
  | zero => simp [kappa_one]
  | succ n ih => rw [pow_succ, kappa_mul, ih, pow_succ]

lemma ideleNorm_pow (g : IdeleGroup F) (n : ℕ) : ideleNorm (g ^ n) = ideleNorm g ^ n := by
  induction n with
  | zero =>
    have := ideleNorm_principal (F := F) 1
    rw [map_one] at this
    simp [this]
  | succ n ih => rw [pow_succ, ideleNorm_mul, ih, pow_succ]

lemma kappa_eq_inv (g : IdeleGroup F) : (kappa g : ℝ) = (ideleNorm g)⁻¹ := by
  set h := Fintype.card (ClassGroup (𝓞 F))
  have hh : h ≠ 0 := Fintype.card_ne_zero
  have hcl : ClassGroup.mk F (ideleFractionalIdeal (g ^ h)) = 1 := by
    rw [map_pow, map_pow, pow_card_eq_one]
  obtain ⟨x, hx⟩ := exists_integral_fin_idele (g ^ h) hcl
  set u := g ^ h / principalIdele F x
  have hgu : g ^ h = u * principalIdele F x := by simp [u]
  have hu1 : ∀ v, Valued.v ((u : AdeleRing (𝓞 F) F).2 v) = 1 := hx
  have hk : (kappa g : ℝ) ^ h = ‖(u : AdeleRing (𝓞 F) F).1‖⁻¹ := by
    rw [← NNReal.coe_pow, ← kappa_pow, hgu, kappa_mul, kappa_principal, mul_one, kappa_unit u hu1]
  have hn : ideleNorm g ^ h = ‖(u : AdeleRing (𝓞 F) F).1‖ := by
    rw [← ideleNorm_pow, hgu, ideleNorm_mul, ideleNorm_principal, mul_one,
      ideleNorm_eq_infNorm u, InfiniteAdeleRing.norm_def]
    intro v
    have h1 : Valued.v ((u : AdeleRing (𝓞 F) F).2 v) ≤ 1 := (hu1 v).le
    have h2 : Valued.v (((u⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v) = 1 := by
      have := fin_mul_inv u v
      have h3 := congrArg Valued.v this
      rw [map_mul, hu1 v, one_mul, map_one] at h3
      exact h3
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h1,
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h2.le⟩
  have hpos := ideleNorm_pos g
  rw [← pow_left_inj₀ (NNReal.coe_nonneg _) (inv_nonneg.mpr hpos.le) hh, hk, inv_pow, hn]

/-- the change of variables `x ↦ x g` -/
lemma integral_mulG (g : IdeleGroup F) (h : AdeleRing (𝓞 F) F → ℂ)
    (hh : AEStronglyMeasurable h tamagawaAdelic) :
    ∫ x, h (x * (g : AdeleRing (𝓞 F) F)) ∂tamagawaAdelic =
      ((ideleNorm g)⁻¹ : ℝ) * ∫ x, h x ∂tamagawaAdelic := by
  have hm : AEStronglyMeasurable h (muG g) := by
    rw [muG_eq]; exact hh.smul_measure _
  have := integral_map (μ := (tamagawaAdelic (F := F))) (continuous_mulG g).measurable.aemeasurable
    (f := h) hm
  change ∫ x, h (mulG g x) ∂tamagawaAdelic = _
  rw [← this]
  change ∫ x, h x ∂(muG g) = _
  rw [muG_eq, integral_smul_measure, ENNReal.coe_toReal, kappa_eq_inv, Complex.real_smul]

lemma fourier_scale (φ : AdeleRing (𝓞 F) F → ℂ) (hφ : AEStronglyMeasurable φ tamagawaAdelic)
    (g : IdeleGroup F) (y : AdeleRing (𝓞 F) F) :
    adelicFourierFun (fun x => φ (x * (g : AdeleRing (𝓞 F) F))) y =
      ((ideleNorm g)⁻¹ : ℝ) * adelicFourierFun φ (y * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F)) := by
  unfold adelicFourierFun
  have hH : AEStronglyMeasurable (fun z => φ z * stdAdelicCharacter
      (z * (y * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F)))) tamagawaAdelic :=
    hφ.mul (continuous_psi.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
  rw [← integral_mulG g _ hH]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  congr 2
  have : ((g : IdeleGroup F) : AdeleRing (𝓞 F) F) * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc x * y = x * y * ((g : AdeleRing (𝓞 F) F) * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F)) := by
        rw [this, mul_one]
    _ = _ := by ring

end Modulus2


/-! ### neighbourhoods of `0` in the finite adeles -/

section NB

lemma box_natMul_sub (c : F) (n : ℕ) : box (c * n) ⊆ box c := by
  have := box_mono_int c (n : 𝓞 F)
  simpa using this

lemma box_nat_sub_one (n : ℕ) : box (n : F) ⊆ box (1 : F) := by
  have := box_natMul_sub (1 : F) n
  rwa [one_mul] at this

lemma eq_zero_of_mem_all_box (z : FiniteAdeleRing (𝓞 F) F)
    (hz : ∀ j : ℕ, z ∈ box ((j.factorial : ℕ) : F)) : z = 0 := by
  by_contra hne
  have : ∃ v, z v ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (DFunLike.ext z 0 h)
  obtain ⟨v, hv⟩ := this
  set p : ℕ := Ideal.absNorm v.asIdeal
  have hp0 : p ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hpv : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (p : 𝓞 F))) < 1 := by
    rw [val_coe, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact Ideal.absNorm_mem v.asIdeal
  have hz0 : Valued.v (z v) ≠ 0 := (Valuation.ne_zero_iff _).mpr hv
  obtain ⟨k, hk⟩ := exists_pow_lt₀ hpv (Units.mk0 _ hz0)
  have hj := hz (p ^ k) v
  have hdvd : p ^ k ∣ (p ^ k).factorial := Nat.dvd_factorial (pow_pos (Nat.pos_of_ne_zero hp0) k) le_rfl
  obtain ⟨q, hq⟩ := hdvd
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) (((p ^ k).factorial : ℕ) : F)) ≤
      Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (p : 𝓞 F))) ^ k := by
    rw [hq, Nat.cast_mul, map_mul, map_mul, Nat.cast_pow, map_pow, ← map_pow]
    calc _ ≤ Valued.v (algebraMap F (v.adicCompletion F) ((p : F) ^ k)) * 1 := by
          refine mul_le_mul' le_rfl ?_
          simpa using val_int_le_one v (q : 𝓞 F)
      _ = _ := by rw [mul_one]; simp
  have := (hj.trans h2).trans_lt hk
  exact lt_irrefl _ this

lemma isClosed_box_fact (j : ℕ) : IsClosed (box ((j.factorial : ℕ) : F)) :=
  isClosed_box _ (by exact_mod_cast (Nat.factorial_pos j).ne')

/-- every neighbourhood of `0` in the finite adeles contains some `M Ô` -/
lemma exists_box_sub (V : Set (FiniteAdeleRing (𝓞 F) F)) (hV : V ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ M : ℕ, M ≠ 0 ∧ box (M : F) ⊆ V := by
  obtain ⟨U, hUV, hUo, hU0⟩ := mem_nhds_iff.mp hV
  have hs : IsCompact (box (1 : F) ∩ Uᶜ) :=
    isCompact_box_one.inter_right hUo.isClosed_compl
  have hst : (box (1 : F) ∩ Uᶜ) ∩ ⋂ j : ℕ, box ((j.factorial : ℕ) : F) = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iInter, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro h1 hz
    exact h1.2 (by rw [eq_zero_of_mem_all_box z hz]; exact hU0)
  have hdir : Directed (· ⊇ ·) (fun j : ℕ => box ((j.factorial : ℕ) : F)) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · obtain ⟨q, hq⟩ := Nat.factorial_dvd_factorial (le_max_left i j)
      change box _ ⊆ box _
      rw [hq, Nat.cast_mul]; exact box_natMul_sub _ _
    · obtain ⟨q, hq⟩ := Nat.factorial_dvd_factorial (le_max_right i j)
      change box _ ⊆ box _
      rw [hq, Nat.cast_mul]; exact box_natMul_sub _ _
  obtain ⟨j, hj⟩ := hs.elim_directed_family_closed _ isClosed_box_fact hst hdir
  refine ⟨j.factorial, (Nat.factorial_pos j).ne', fun z hz => hUV ?_⟩
  by_contra hzU
  have : z ∈ (box (1 : F) ∩ Uᶜ) ∩ box ((j.factorial : ℕ) : F) :=
    ⟨⟨box_nat_sub_one _ hz, hzU⟩, hz⟩
  rw [hj] at this
  exact this

end NB

/-! ### a finite coset decomposition -/

section Coset

lemma mem_box_iff_mk (N : ℕ) (a b : FiniteAdeleRing (𝓞 F) F) :
    a - b ∈ box (N : F) ↔ (QuotientAddGroup.mk a : FiniteAdeleRing (𝓞 F) F ⧸ boxSub (N : F)) =
      QuotientAddGroup.mk b := by
  rw [QuotientAddGroup.eq]
  constructor
  · intro h
    have := neg_mem_box h
    rwa [neg_sub, sub_eq_neg_add] at this
  · intro h
    have := neg_mem_box h
    rw [neg_add, neg_neg, ← sub_eq_add_neg] at this; exact this

/-- a compact set stable under `N Ô` is a finite disjoint union of cosets -/
lemma coset_decomp (N : ℕ) (hN : N ≠ 0) (K : Set (FiniteAdeleRing (𝓞 F) F)) (hK : IsCompact K)
    (hKs : ∀ z ∈ K, ∀ w ∈ box (N : F), z + w ∈ K) :
    ∃ Q : Finset (FiniteAdeleRing (𝓞 F) F ⧸ boxSub (N : F)), (∀ q ∈ Q, q.out ∈ K) ∧
      ∀ z, K.indicator (fun _ => (1 : ℂ)) z =
        ∑ q ∈ Q, (box (N : F)).indicator (fun _ => (1 : ℂ)) (z - q.out) := by
  classical
  have hN' : (N : F) ≠ 0 := by exact_mod_cast hN
  have hopen : ∀ x ∈ K, (fun w => w - x) ⁻¹' box (N : F) ∈ 𝓝 x := by
    intro x _
    refine IsOpen.mem_nhds ((isOpen_box _ hN').preimage (continuous_id.sub continuous_const)) ?_
    simp only [Set.mem_preimage, sub_self]; exact zero_mem_box _
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover _ hopen
  let Q := t.image (fun x => (QuotientAddGroup.mk x : FiniteAdeleRing (𝓞 F) F ⧸ boxSub (N : F)))
  have hout : ∀ q ∈ Q, q.out ∈ K := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    have h1 : (QuotientAddGroup.mk (QuotientAddGroup.mk x :
        FiniteAdeleRing (𝓞 F) F ⧸ boxSub (N : F)).out : FiniteAdeleRing (𝓞 F) F ⧸ boxSub (N : F)) =
        QuotientAddGroup.mk x := Quotient.out_eq _
    have h2 := (mem_box_iff_mk N _ _).mpr h1
    have := hKs x (htK x hx) _ h2
    rwa [add_sub_cancel] at this
  refine ⟨Q, hout, fun z => ?_⟩
  have hterm : ∀ q : FiniteAdeleRing (𝓞 F) F ⧸ boxSub (N : F),
      (box (N : F)).indicator (fun _ => (1 : ℂ)) (z - q.out) =
        if (QuotientAddGroup.mk z : FiniteAdeleRing (𝓞 F) F ⧸ boxSub (N : F)) = q then 1 else 0 := by
    intro q
    by_cases h : (QuotientAddGroup.mk z : FiniteAdeleRing (𝓞 F) F ⧸ boxSub (N : F)) = q
    · rw [if_pos h, Set.indicator_of_mem]
      rw [mem_box_iff_mk, h]; exact (Quotient.out_eq q).symm
    · rw [if_neg h, Set.indicator_of_notMem]
      intro hm
      rw [mem_box_iff_mk] at hm
      exact h (hm.trans (Quotient.out_eq q))
  simp only [hterm, Finset.sum_ite_eq]
  by_cases hz : z ∈ K
  · rw [Set.indicator_of_mem hz]
    have : (QuotientAddGroup.mk z : FiniteAdeleRing (𝓞 F) F ⧸ boxSub (N : F)) ∈ Q := by
      obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (hcover hz)
      refine Finset.mem_image.mpr ⟨x, hx, ?_⟩
      exact ((mem_box_iff_mk N z x).mp hzx).symm
    rw [if_pos this]
  · rw [Set.indicator_of_notMem hz]
    rw [if_neg]
    intro hq
    obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hq
    apply hz
    have h1 := hout _ hq
    have h2 : z - (QuotientAddGroup.mk z : FiniteAdeleRing (𝓞 F) F ⧸ boxSub (N : F)).out ∈
        box (N : F) := by
      rw [mem_box_iff_mk]; exact (Quotient.out_eq _).symm
    have := hKs _ h1 _ h2
    rwa [add_sub_cancel] at this

end Coset


/-! ### the class of test functions and Poisson summation for it -/

section Tclass

open MeasureTheory
open scoped SchwartzMap

/-- translated basic test functions -/
noncomputable def Tt (M : ℕ) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) (a : FiniteAdeleRing (𝓞 F) F) :
    AdeleRing (𝓞 F) F → ℂ := fun x => T0 M Ψ (x - mkA 0 a)

/-- generators -/
def Tgen : Set (AdeleRing (𝓞 F) F → ℂ) :=
  {φ | ∃ (M : ℕ) (_ : M ≠ 0) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) (a : FiniteAdeleRing (𝓞 F) F),
    φ = Tt M Ψ a}

/-- the span of the generators -/
def Tsp : Submodule ℂ (AdeleRing (𝓞 F) F → ℂ) := Submodule.span ℂ (Tgen (F := F))

/-- the Poisson package -/
def Good (φ : AdeleRing (𝓞 F) F → ℂ) : Prop :=
  AEStronglyMeasurable φ tamagawaAdelic ∧
  (∀ y, Integrable (fun x => φ x * stdAdelicCharacter (x * y)) tamagawaAdelic) ∧
  Summable (fun ξ : F => φ (algebraMap F _ ξ)) ∧
  Summable (fun η : F => adelicFourierFun φ (algebraMap F _ η)) ∧
  ∑' ξ : F, φ (algebraMap F _ ξ) = ∑' η : F, adelicFourierFun φ (algebraMap F _ η)

lemma aesm_T0 (M : ℕ) (hM : M ≠ 0) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) :
    AEStronglyMeasurable (T0 M Ψ) tamagawaAdelic := by
  rw [T0_eq_indicator]
  exact ((Ψ.continuous.comp continuous_LHs_fst).aestronglyMeasurable).indicator
    (measurableSet_boxA _ (by exact_mod_cast hM))

lemma good_T0 (M : ℕ) (hM : M ≠ 0) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) : Good (T0 M Ψ) := by
  obtain ⟨h1, h2, h3⟩ := T0_poisson M hM Ψ
  exact ⟨aesm_T0 M hM Ψ, integrable_T0_psi M hM Ψ, h1, h2, h3⟩

lemma fourier_translate (φ : AdeleRing (𝓞 F) F → ℂ) (c : AdeleRing (𝓞 F) F) (y : AdeleRing (𝓞 F) F) :
    adelicFourierFun (fun x => φ (x - c)) y = stdAdelicCharacter (c * y) * adelicFourierFun φ y := by
  unfold adelicFourierFun
  rw [← integral_const_mul]
  have := integral_add_left_eq_self (μ := (tamagawaAdelic (F := F)))
    (fun x => φ (x - c) * stdAdelicCharacter (x * y)) c
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [add_sub_cancel_left, add_mul, psi_add]
  ring

lemma good_translate (φ : AdeleRing (𝓞 F) F → ℂ) (hφ : Good φ) (ξ0 : F) :
    Good (fun x => φ (x - algebraMap F _ ξ0)) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hφ
  have hF : ∀ η : F, adelicFourierFun (fun x => φ (x - algebraMap F _ ξ0)) (algebraMap F _ η) =
      adelicFourierFun φ (algebraMap F _ η) := by
    intro η
    rw [fourier_translate, ← map_mul, psi_algebraMap, one_mul]
  have hS : (fun ξ : F => φ (algebraMap F (AdeleRing (𝓞 F) F) ξ - algebraMap F _ ξ0)) =
      (fun ξ : F => φ (algebraMap F _ ξ)) ∘ (Equiv.subRight ξ0) := by
    funext ξ; simp [map_sub]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact h0.comp_quasiMeasurePreserving
      (measurePreserving_sub_right tamagawaAdelic _).quasiMeasurePreserving
  · intro y
    have := ((h1 y).const_mul (stdAdelicCharacter (algebraMap F _ ξ0 * y))).comp_sub_right
      (algebraMap F (AdeleRing (𝓞 F) F) ξ0)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [show x = (x - algebraMap F (AdeleRing (𝓞 F) F) ξ0) + algebraMap F _ ξ0 by ring]
    rw [add_sub_cancel_right, add_mul, psi_add]
    ring
  · rw [hS]; exact (Equiv.summable_iff _).mpr h2
  · simp only [hF]; exact h3
  · simp only [hF]
    rw [hS]
    exact ((Equiv.subRight ξ0).tsum_eq (fun ξ : F => φ (algebraMap F _ ξ))).trans h4

lemma good_add (φ ψ : AdeleRing (𝓞 F) F → ℂ) (hφ : Good φ) (hψ : Good ψ) : Good (φ + ψ) := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := hφ
  obtain ⟨b0, b1, b2, b3, b4⟩ := hψ
  have hF : ∀ y, adelicFourierFun (φ + ψ) y = adelicFourierFun φ y + adelicFourierFun ψ y := by
    intro y
    unfold adelicFourierFun
    rw [← integral_add (a1 y) (b1 y)]
    congr 1; funext x; simp only [Pi.add_apply]; ring
  refine ⟨a0.add b0, fun y => ?_, ?_, ?_, ?_⟩
  · refine ((a1 y).add (b1 y)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]; ring
  · exact a2.add b2
  · simp only [hF]; exact a3.add b3
  · simp only [hF, Pi.add_apply]
    rw [a2.tsum_add b2, a3.tsum_add b3, a4, b4]

lemma good_smul (c : ℂ) (φ : AdeleRing (𝓞 F) F → ℂ) (hφ : Good φ) : Good (c • φ) := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := hφ
  have hF : ∀ y, adelicFourierFun (c • φ) y = c * adelicFourierFun φ y := by
    intro y
    unfold adelicFourierFun
    rw [← integral_const_mul]
    congr 1; funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
  refine ⟨a0.const_smul c, fun y => ?_, ?_, ?_, ?_⟩
  · refine ((a1 y).const_mul c).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  · simpa only [Pi.smul_apply, smul_eq_mul] using a2.mul_left c
  · simp only [hF]; exact a3.mul_left c
  · simp only [hF, Pi.smul_apply, smul_eq_mul]
    rw [tsum_mul_left, tsum_mul_left, a4]

lemma good_zero : Good (0 : AdeleRing (𝓞 F) F → ℂ) := by
  have := good_smul 0 (T0 (F := F) 1 0) (good_T0 1 one_ne_zero 0)
  rwa [zero_smul] at this

/-- a generator is a translate of `T₀` by an element of `F` -/
lemma Tt_eq (M : ℕ) (hM : M ≠ 0) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ (ξ0 : F) (Ψ' : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)),
      Tt M Ψ a = fun x => T0 M Ψ' (x - algebraMap F _ ξ0) := by
  have hM' : (M : F) ≠ 0 := by exact_mod_cast hM
  obtain ⟨ξ0, hξ0⟩ := exists_sub_box (M : F) hM' a
  refine ⟨ξ0, SchwartzMap.compSubConstCLM ℂ (-LH.symm (algebraMap F (InfiniteAdeleRing F) ξ0)) Ψ,
    funext fun x => ?_⟩
  simp only [Tt]
  have h2 : (x - mkA 0 a).2 ∈ box (M : F) ↔ (x - algebraMap F (AdeleRing (𝓞 F) F) ξ0).2 ∈
      box (M : F) := by
    have e1 : (x - mkA 0 a).2 = x.2 - a := rfl
    have e2 : (x - algebraMap F (AdeleRing (𝓞 F) F) ξ0).2 =
        (x.2 - a) + (a - algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ0) := by
      change x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ0 = _; ring
    rw [e1, e2]
    constructor
    · intro h; exact add_mem_box h hξ0
    · intro h; have := sub_mem_box h hξ0; rwa [add_sub_cancel_right] at this
  by_cases hx : (x - mkA 0 a).2 ∈ box (M : F)
  · rw [T0_of_mem M Ψ _ hx, T0_of_mem _ _ _ (h2.mp hx), SchwartzMap.compSubConstCLM_apply,
      sub_neg_eq_add]
    congr 1
    have e3 : (x - mkA 0 a).1 = x.1 := by
      change x.1 - 0 = x.1; rw [sub_zero]
    have e4 : (x - algebraMap F (AdeleRing (𝓞 F) F) ξ0).1 =
        x.1 - algebraMap F (InfiniteAdeleRing F) ξ0 := rfl
    rw [e3, e4, LH_symm_sub, sub_add_cancel]
  · rw [T0_of_not_mem M Ψ _ hx, T0_of_not_mem _ _ _ (fun h => hx (h2.mpr h))]

lemma good_Tsp (φ : AdeleRing (𝓞 F) F → ℂ) (hφ : φ ∈ Tsp (F := F)) : Good φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨M, hM, Ψ, a, rfl⟩ := hx
    obtain ⟨ξ0, Ψ', h⟩ := Tt_eq M hM Ψ a
    rw [h]
    exact good_translate _ (good_T0 M hM Ψ') ξ0
  | zero => exact good_zero
  | add x y _ _ hx hy => exact good_add x y hx hy
  | smul c x _ hx => exact good_smul c x hx

end Tclass


section Tscale

open MeasureTheory
open scoped SchwartzMap

lemma mulL_mul (y z : InfiniteAdeleRing F) (t : EuclideanSpace ℝ (Ix F)) :
    mulL y (mulL z t) = mulL (z * y) t := by
  simp only [mulL_apply, Homeomorph.apply_symm_apply, mul_assoc]

lemma mulL_one (t : EuclideanSpace ℝ (Ix F)) : mulL 1 t = t := by
  simp [mulL_apply]

lemma inf_inv_mul (g : IdeleGroup F) :
    ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).1 * (g : AdeleRing (𝓞 F) F).1 = 1 := by
  have h : ((g⁻¹ * g : IdeleGroup F) : AdeleRing (𝓞 F) F) = 1 := by
    rw [inv_mul_cancel, Units.val_one]
  exact (congrArg (fun a : AdeleRing (𝓞 F) F => a.1) h : _)

lemma inf_mul_inv (g : IdeleGroup F) :
    (g : AdeleRing (𝓞 F) F).1 * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).1 = 1 := by
  have h : ((g * g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) = 1 := by
    rw [mul_inv_cancel, Units.val_one]
  exact (congrArg (fun a : AdeleRing (𝓞 F) F => a.1) h : _)

/-- multiplication by the archimedean part of an idele as a linear equivalence -/
noncomputable def mulLE (g : IdeleGroup F) : EuclideanSpace ℝ (Ix F) ≃L[ℝ] EuclideanSpace ℝ (Ix F) :=
  (LinearEquiv.ofLinear (mulL (g : AdeleRing (𝓞 F) F).1)
    (mulL ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).1)
    (by
      ext t : 1
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq, mulL_mul]
      rw [inf_inv_mul g, mulL_one])
    (by
      ext t : 1
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq, mulL_mul]
      rw [inf_mul_inv g, mulL_one])).toContinuousLinearEquiv

lemma mulLE_apply (g : IdeleGroup F) (t : EuclideanSpace ℝ (Ix F)) :
    mulLE g t = mulL (g : AdeleRing (𝓞 F) F).1 t := rfl

lemma Tt_scale (M : ℕ) (hM : M ≠ 0) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ))
    (a : FiniteAdeleRing (𝓞 F) F) (g : IdeleGroup F) :
    (fun x => Tt M Ψ a (x * (g : AdeleRing (𝓞 F) F))) ∈ Tsp (F := F) := by
  classical
  have hM' : (M : F) ≠ 0 := by exact_mod_cast hM
  set gf := (g : AdeleRing (𝓞 F) F).2
  set gi := ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2
  have hggi : gf * gi = 1 := by
    change ((g * g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 = 1
    rw [mul_inv_cancel]; rfl
  obtain ⟨N, hN, hNz⟩ := exists_den (algebraMap F (FiniteAdeleRing (𝓞 F) F) (M : F)⁻¹ * gf)
  have hN' : (N : F) ≠ 0 := by exact_mod_cast hN
  have hboxN : ∀ w ∈ box (N : F), w * gf ∈ box (M : F) := by
    intro w hw
    have h1 := mul_mem_box hw hNz
    rw [mul_inv_cancel₀ hN'] at h1
    have h2 := mul_mem_box (alg_mem_box_self (M : F)) h1
    rw [mul_one] at h2
    convert h2 using 1
    rw [← mul_assoc, mul_comm _ w, mul_assoc, ← mul_assoc _ _ gf, ← map_mul,
      mul_inv_cancel₀ hM', map_one, one_mul]
  let K : Set (FiniteAdeleRing (𝓞 F) F) := {z | z * gf - a ∈ box (M : F)}
  have hKc : IsCompact K := by
    have : K = (fun w => (w + a) * gi) '' box (M : F) := by
      ext z
      constructor
      · intro hz
        refine ⟨z * gf - a, hz, ?_⟩
        simp only [sub_add_cancel, mul_assoc, hggi, mul_one]
      · rintro ⟨w, hw, rfl⟩
        change (w + a) * gi * gf - a ∈ box (M : F)
        rw [mul_assoc, mul_comm gi, hggi, mul_one, add_sub_cancel_right]
        exact hw
    rw [this]
    exact (isCompact_box _ hM').image ((continuous_id.add continuous_const).mul continuous_const)
  have hKs : ∀ z ∈ K, ∀ w ∈ box (N : F), z + w ∈ K := by
    intro z hz w hw
    change (z + w) * gf - a ∈ box (M : F)
    rw [add_mul, add_sub_right_comm]
    exact add_mem_box hz (hboxN w hw)
  obtain ⟨Q, -, hQ⟩ := coset_decomp N hN K hKc hKs
  let Ψg : 𝓢(EuclideanSpace ℝ (Ix F), ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mulLE g) Ψ
  have heq : (fun x => Tt M Ψ a (x * (g : AdeleRing (𝓞 F) F))) =
      ∑ q ∈ Q, Tt N Ψg q.out := by
    funext x
    rw [Finset.sum_apply]
    simp only [Tt, T0]
    have e1 : (x * (g : AdeleRing (𝓞 F) F) - mkA 0 a).2 = x.2 * gf - a := rfl
    have e2 : (x * (g : AdeleRing (𝓞 F) F) - mkA 0 a).1 = x.1 * (g : AdeleRing (𝓞 F) F).1 := by
      change x.1 * (g : AdeleRing (𝓞 F) F).1 - 0 = _; rw [sub_zero]
    have e3 : ∀ r, (x - mkA 0 r).2 = x.2 - r := fun r => rfl
    have e4 : ∀ r, (x - mkA 0 r).1 = x.1 := fun r => by change x.1 - 0 = x.1; rw [sub_zero]
    have e5 : Ψ (LH.symm (x.1 * (g : AdeleRing (𝓞 F) F).1)) = Ψg (LH.symm x.1) := by
      change _ = Ψ (mulLE g (LH.symm x.1))
      rw [mulLE_apply, mulL_apply, Homeomorph.apply_symm_apply]
    simp only [e1, e2, e3, e4, e5]
    rw [← Finset.sum_mul, ← hQ]
    congr 1
  rw [heq]
  exact Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨N, hN, Ψg, q.out, rfl⟩

end Tscale


section RRfun

open MeasureTheory
open scoped SchwartzMap

lemma Tsp_scale (g : IdeleGroup F) (φ : AdeleRing (𝓞 F) F → ℂ) (hφ : φ ∈ Tsp (F := F)) :
    (fun x => φ (x * (g : AdeleRing (𝓞 F) F))) ∈ Tsp (F := F) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨M, hM, Ψ, a, rfl⟩ := hx
    exact Tt_scale M hM Ψ a g
  | zero => exact (Tsp (F := F)).zero_mem
  | add x y _ _ hx hy => exact (Tsp (F := F)).add_mem hx hy
  | smul c x _ hx => exact (Tsp (F := F)).smul_mem c hx

lemma tsum_F_split (f : F → ℂ) (hf : Summable f) :
    ∑' ξ : F, f ξ = f 0 + ∑' ξ : Fˣ, f (ξ : F) := by
  classical
  rw [hf.tsum_eq_add_tsum_ite 0]
  congr 1
  have hinj : Function.Injective (fun u : Fˣ => (u : F)) := Units.val_injective
  have := hinj.tsum_eq (f := fun n => if n = 0 then 0 else f n) (by
    intro x hx
    by_cases h0 : x = 0
    · simp [h0] at hx
    · exact ⟨Units.mk0 x h0, rfl⟩)
  rw [← this]
  refine tsum_congr fun u => ?_
  simp [u.ne_zero]

lemma summable_units (f : F → ℂ) (hf : Summable f) : Summable (fun ξ : Fˣ => f (ξ : F)) :=
  hf.comp_injective Units.val_injective

/-- Riemann–Roch for the functions of the class -/
lemma RR_fun (φ : AdeleRing (𝓞 F) F → ℂ) (hφ : φ ∈ Tsp (F := F)) (g : IdeleGroup F) :
    Summable (fun ξ : Fˣ => φ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (g : AdeleRing (𝓞 F) F))) ∧
    Summable (fun ξ : Fˣ => adelicFourierFun φ
      (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F))) ∧
    adelicThetaFun φ g =
      ((ideleNorm g)⁻¹ : ℝ) * adelicThetaFun (adelicFourierFun φ) g⁻¹ +
        ((ideleNorm g)⁻¹ : ℝ) * adelicFourierFun φ 0 - φ 0 := by
  have hg := good_Tsp _ (Tsp_scale g φ hφ)
  have hφg := good_Tsp φ hφ
  obtain ⟨_, _, h2, h3, h4⟩ := hg
  have hF : ∀ η : F, adelicFourierFun (fun x => φ (x * (g : AdeleRing (𝓞 F) F)))
      (algebraMap F (AdeleRing (𝓞 F) F) η) = ((ideleNorm g)⁻¹ : ℝ) * adelicFourierFun φ
        (algebraMap F (AdeleRing (𝓞 F) F) η * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F)) :=
    fun η => fourier_scale φ hφg.1 g _
  have hpos := ideleNorm_pos g
  have hc : ((ideleNorm g)⁻¹ : ℝ) ≠ 0 := inv_ne_zero hpos.ne'
  have h3' : Summable (fun η : F => adelicFourierFun φ
      (algebraMap F (AdeleRing (𝓞 F) F) η * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F))) := by
    simp only [hF] at h3
    have := h3.mul_left (((ideleNorm g : ℝ) : ℂ))
    refine this.congr fun η => ?_
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, one_mul]
  refine ⟨summable_units _ h2, summable_units _ h3', ?_⟩
  have e := h4
  simp only [hF] at e
  rw [tsum_F_split _ h2, tsum_mul_left, tsum_F_split _ h3'] at e
  simp only [map_zero, zero_mul] at e
  unfold adelicThetaFun
  linear_combination e

end RRfun


/-! ### structure of structural pairs on the adeles: preliminaries -/

section StructPrelim

open Multiplicative

lemma ell_zero {k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))} (hk : IsOpen (annihilator k))
    (ℓ : AdeleRing (𝓞 F) F →+ ℝ) (hℓ : Continuous ℓ) (x : Multiplicative (AdeleRing (𝓞 F) F))
    (hx : x ∈ k) : ℓ (Multiplicative.toAdd x) = 0 := by
  let χ : ℝ → PontryaginDual (Multiplicative (AdeleRing (𝓞 F) F)) := fun t =>
    ({ toFun := fun y => Circle.exp (t * ℓ (Multiplicative.toAdd y))
       map_one' := by
         simp only [toAdd_one, map_zero, mul_zero, Circle.exp_zero]
       map_mul' := by
         intro a b
         simp only [toAdd_mul, map_add, mul_add, Circle.exp_add]
       continuous_toFun := Circle.exp.continuous.comp
         (continuous_const.mul (hℓ.comp continuous_toAdd)) } :
      ContinuousMonoidHom (Multiplicative (AdeleRing (𝓞 F) F)) Circle)
  have hχ : Continuous χ := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    exact Circle.exp.continuous.comp
      (continuous_fst.mul (hℓ.comp (continuous_toAdd.comp continuous_snd)))
  have h0 : χ 0 ∈ annihilator k := by
    intro y _
    show Circle.exp (0 * ℓ (Multiplicative.toAdd y)) = 1
    rw [zero_mul, Circle.exp_zero]
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), χ t ∈ annihilator k :=
    hχ.continuousAt.preimage_mem_nhds (hk.mem_nhds h0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  by_contra hne
  generalize hc : ℓ (Multiplicative.toAdd x) = c at hne
  have hcpos : 0 < |c| := abs_pos.mpr hne
  let t : ℝ := min (δ / 2) (1 / (|c| + 1))
  have htpos : 0 < t := lt_min (by linarith) (by positivity)
  have htd : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have h1 : (χ t) x = 1 := hball htd x hx
  have h2 : Circle.exp (t * c) = 1 := by
    rw [← hc]
    exact h1
  obtain ⟨n, hn⟩ := Circle.exp_eq_one.1 h2
  have h3 : |t * c| < 1 := by
    rw [abs_mul, abs_of_pos htpos]
    have h4 : t ≤ 1 / (|c| + 1) := min_le_right _ _
    have h5 : t * |c| ≤ 1 / (|c| + 1) * |c| := mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
    have h6 : 1 / (|c| + 1) * |c| < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
      linarith
    linarith
  have hn0 : n = 0 := by
    by_contra hn0
    have h7 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
      exact_mod_cast this
    have h8 : |t * c| = |(n : ℝ)| * (2 * Real.pi) := by
      rw [hn, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have h9 : (1 : ℝ) * (2 * Real.pi) ≤ |(n : ℝ)| * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right h7 (by positivity)
    have h10 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    linarith
  rw [hn0, Int.cast_zero, zero_mul] at hn
  have : c = 0 := by
    rcases mul_eq_zero.1 hn with h | h
    · exact absurd h htpos.ne'
    · exact h
  exact hne this

/-- the `i`-th archimedean coordinate as an additive map -/
noncomputable def coordA (i : Ix F) : AdeleRing (𝓞 F) F →+ ℝ where
  toFun y := (LH.symm y.1) i
  map_zero' := by
    change (LH.symm (0 : InfiniteAdeleRing F)) i = 0
    rw [show LH.symm (0 : InfiniteAdeleRing F) = 0 from map_zero (LHa (F := F)).symm]; rfl
  map_add' a b := by
    change (LH.symm (a.1 + b.1)) i = _
    rw [LH_symm_add]; rfl

lemma k_inf_zero {k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))} (hk : IsOpen (annihilator k))
    (x : Multiplicative (AdeleRing (𝓞 F) F)) (hx : x ∈ k) : (Multiplicative.toAdd x).1 = 0 := by
  have h : LH.symm (Multiplicative.toAdd x).1 = 0 := by
    ext i
    exact ell_zero hk (coordA i) ((PiLp.continuous_apply 2 _ i).comp continuous_LHs_fst) x hx
  have := congrArg LH h
  rwa [Homeomorph.apply_symm_apply, LH_zero] at this

lemma Gamma_bdd {Γ : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))}
    (hg : IsCompactlyGeneratedSubgroup Γ) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ x ∈ Γ, (Multiplicative.toAdd x).2 ∈ box ((N : F)⁻¹) := by
  obtain ⟨U, hUc, hUΓ, -, hcl⟩ := hg
  let Kf := (fun x : Multiplicative (AdeleRing (𝓞 F) F) => (Multiplicative.toAdd x).2) '' U
  have hKf : IsCompact Kf := hUc.image (continuous_snd_A.comp continuous_toAdd)
  have hcov : Kf ⊆ ⋃ j : ℕ, box (((j.factorial : ℕ) : F)⁻¹) := by
    intro z _
    obtain ⟨N, hN, hz⟩ := exists_den z
    exact Set.mem_iUnion.mpr ⟨N, box_inv_mono _ _ (Nat.dvd_factorial (Nat.pos_of_ne_zero hN) le_rfl)
      (Nat.factorial_pos N).ne' hz⟩
  have hdir : Directed (· ⊆ ·) (fun j : ℕ => box (((j.factorial : ℕ) : F)⁻¹)) := by
    intro i j
    exact ⟨max i j, box_inv_mono _ _ (Nat.factorial_dvd_factorial (le_max_left i j))
      (Nat.factorial_pos _).ne', box_inv_mono _ _ (Nat.factorial_dvd_factorial (le_max_right i j))
      (Nat.factorial_pos _).ne'⟩
  obtain ⟨j, hj⟩ := hKf.elim_directed_cover _ (fun j => isOpen_box _ (fact_ne j)) hcov hdir
  refine ⟨j.factorial, (Nat.factorial_pos j).ne', ?_⟩
  let H : Subgroup (Multiplicative (AdeleRing (𝓞 F) F)) :=
    { carrier := {x | (Multiplicative.toAdd x).2 ∈ box (((j.factorial : ℕ) : F)⁻¹)}
      mul_mem' := fun ha hb => add_mem_box ha hb
      one_mem' := zero_mem_box _
      inv_mem' := fun ha => neg_mem_box ha }
  have hUH : U ⊆ H := fun x hx => hj ⟨x, hx, rfl⟩
  have : Γ ≤ H := by rw [← hcl]; exact (Subgroup.closure_le H).mpr hUH
  exact fun x hx => this hx

lemma Gamma_contains {Γ : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))}
    (hΓo : IsOpen (Γ : Set (Multiplicative (AdeleRing (𝓞 F) F)))) :
    ∃ M0 : ℕ, M0 ≠ 0 ∧ ∀ x : AdeleRing (𝓞 F) F, x.2 ∈ box (M0 : F) → Multiplicative.ofAdd x ∈ Γ := by
  let V : Set (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) :=
    {x | Multiplicative.ofAdd (show AdeleRing (𝓞 F) F from x) ∈ Γ}
  have hVo : IsOpen V := hΓo.preimage continuous_ofAdd
  have hV0 : V ∈ 𝓝 ((0 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F)) :=
    hVo.mem_nhds Γ.one_mem
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hV0
  obtain ⟨t1, ht1, t2, ht2, hsub⟩ := hV0
  obtain ⟨M0, hM0, hbox⟩ := exists_box_sub t2 ht2
  refine ⟨M0, hM0, fun x hx => ?_⟩
  set s := LH.symm x.1
  have htend : Filter.Tendsto (fun n : ℕ => LH ((1 / (n : ℝ)) • s)) Filter.atTop
      (𝓝 (LH (0 : EuclideanSpace ℝ (Ix F)))) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const s
    rw [zero_smul] at this
    exact (LH.continuous.tendsto _).comp this
  rw [LH_zero] at htend
  obtain ⟨n, hn⟩ := ((htend.eventually (Filter.mem_of_superset ht1 subset_rfl)).and
    (Filter.eventually_ge_atTop 1)).exists
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have ha : Multiplicative.ofAdd (mkA (LH ((1 / (n : ℝ)) • s)) 0) ∈ Γ :=
    hsub ⟨hn.1, mem_of_mem_nhds ht2⟩
  have hb : Multiplicative.ofAdd (mkA 0 x.2) ∈ Γ := hsub ⟨mem_of_mem_nhds ht1, hbox hx⟩
  have hx' : x = n • mkA (LH ((1 / (n : ℝ)) • s)) 0 + mkA 0 x.2 := by
    have e1 : (n • mkA (LH ((1 / (n : ℝ)) • s)) 0) = mkA (LH s) 0 := by
      change mkA (n • LH ((1 / (n : ℝ)) • s)) (n • 0) = _
      rw [← LH_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_one_div_cancel hn0, one_smul,
        smul_zero]
    rw [e1, mkA_add, add_zero, zero_add, Homeomorph.apply_symm_apply, mkA_eta]
  rw [hx', ofAdd_add, ofAdd_nsmul]
  exact Γ.mul_mem (Γ.pow_mem ha n) hb

/-- a point of the circle all of whose multiples are small is zero -/
lemma circle_eq_zero (θ : UnitAddCircle) (h : ∀ k : ℕ, ‖k • θ‖ < 1 / 4) : θ = 0 := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective θ
  set t := s - round s
  have hts : ((t : ℝ) : UnitAddCircle) = (s : UnitAddCircle) := by
    simp only [t]
    rw [AddCircle.coe_sub]
    have : ((round s : ℤ) : ℝ) = (round s : ℤ) • (1 : ℝ) := by simp
    rw [this, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, sub_zero]
  have hthalf : |t| ≤ 1 / 2 := abs_sub_round s
  have hnorm : ∀ u : ℝ, |u| ≤ 1 / 2 → ‖((u : ℝ) : UnitAddCircle)‖ = |u| := by
    intro u hu
    exact (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).mpr (by simpa using hu)
  change ((s : ℝ) : UnitAddCircle) = 0
  rw [← hts]
  by_contra hne
  have ht0 : t ≠ 0 := by intro h0; apply hne; rw [h0]; rfl
  have h1 := h 1
  rw [one_smul, ← hts, hnorm t hthalf] at h1
  have htpos : 0 < |t| := abs_pos.mpr ht0
  set k := ⌈1 / (4 * |t|)⌉₊
  have hk1 : 1 / (4 * |t|) ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) < 1 / (4 * |t|) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hlow : 1 / 4 ≤ k * |t| := by
    rw [div_le_iff₀ (by positivity)] at hk1; nlinarith
  have hup : k * |t| < 1 / 2 := by
    have : (k : ℝ) * |t| < (1 / (4 * |t|) + 1) * |t| := mul_lt_mul_of_pos_right hk2 htpos
    rw [add_mul, one_div, mul_inv, mul_assoc, inv_mul_cancel₀ htpos.ne', mul_one, one_mul] at this
    linarith
  have h2 := h k
  rw [← hts, ← AddCircle.coe_nsmul, nsmul_eq_mul] at h2
  rw [hnorm _ (by rw [abs_mul, Nat.abs_cast]; linarith), abs_mul, Nat.abs_cast] at h2
  linarith

/-- the small neighbourhood of `0` in an elementary abelian Lie group -/
def Wn (m n r s : ℕ) (d : Fin s → ℕ) : Set (ElemGroup m n r s d) :=
  {e | ‖e.1‖ < 1 ∧ (∀ j, ‖e.2.1 j‖ < 1 / 4) ∧ e.2.2 = 0}

lemma zero_mem_Wn (m n r s : ℕ) (d : Fin s → ℕ) : (0 : ElemGroup m n r s d) ∈ Wn m n r s d := by
  refine ⟨by simp, fun j => by simp, rfl⟩

lemma isOpen_Wn (m n r s : ℕ) (d : Fin s → ℕ) (hd : ∀ i, d i ≠ 0) : IsOpen (Wn m n r s d) := by
  have : ∀ i, NeZero (d i) := fun i => ⟨hd i⟩
  have e : Wn m n r s d = {e : ElemGroup m n r s d | ‖e.1‖ < 1} ∩
      ((⋂ j, {e : ElemGroup m n r s d | ‖e.2.1 j‖ < 1 / 4}) ∩
        (fun e : ElemGroup m n r s d => e.2.2) ⁻¹' {0}) := by
    ext e; simp [Wn]
  rw [e]
  refine (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
    ((isOpen_iInter_of_finite fun j => isOpen_lt (continuous_norm.comp ((continuous_apply j).comp
      (continuous_fst.comp continuous_snd))) continuous_const).inter ?_)
  exact (isOpen_discrete {(0 : (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)))}).preimage
    (continuous_snd.comp continuous_snd)

lemma Wn_nss (m n r s : ℕ) (d : Fin s → ℕ) (e : ElemGroup m n r s d)
    (h : ∀ k : ℕ, k • e ∈ Wn m n r s d) : e = 0 := by
  have h1 : e.1 = 0 := by
    by_contra hne
    have hpos : 0 < ‖e.1‖ := norm_pos_iff.mpr hne
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / ‖e.1‖)
    have := (h k).1
    change ‖k • e.1‖ < 1 at this
    rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast] at this
    rw [div_lt_iff₀ hpos] at hk
    linarith
  have h2 : e.2.1 = 0 := by
    funext j
    exact circle_eq_zero _ fun k => (h k).2.1 j
  have h3 : e.2.2 = 0 := by simpa using (h 1).2.2
  exact Prod.ext h1 (Prod.ext h2 h3)

end StructPrelim


section SchwartzOfRapid

open scoped SchwartzMap

/-- rapidly decreasing functions on `ℝ^m × ...` composed with an injective linear map are Schwartz -/
lemma schwartz_of_rapid {m n r s : ℕ} {d : Fin s → ℕ} (h : ElemGroup m n r s d → ℂ)
    (hr : IsRapidDecay h) (L : EuclideanSpace ℝ (Ix F) →L[ℝ] (Fin m → ℝ)) (K : ℝ)
    (hK : ∀ t, ‖t‖ ≤ K * ‖L t‖) (ρ : Fin r → ℤ) (σ : (i : Fin s) → ZMod (d i)) :
    ∃ Φ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ), ∀ t, Φ t = elemLift h ρ σ (L t, 0) := by
  let Lx : EuclideanSpace ℝ (Ix F) →L[ℝ] (Fin m → ℝ) × (Fin n → ℝ) := L.prod 0
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (elemLift h ρ σ) := hr.1 ρ σ
  set K' := max K 0
  have hK' : ∀ t, ‖t‖ ≤ K' * ‖L t‖ := fun t =>
    (hK t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  refine ⟨⟨elemLift h ρ σ ∘ Lx, hG.comp Lx.contDiff, ?_⟩, fun t => rfl⟩
  intro k' n'
  obtain ⟨C, hC⟩ := hr.2 k' 0 n'
  refine ⟨K' ^ k' * ‖Lx‖ ^ n' * C, fun t => ?_⟩
  rw [Lx.iteratedFDeriv_comp_right hG t (by exact_mod_cast le_top)]
  have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n' (elemLift h ρ σ) (Lx t)) (fun _ : Fin n' => Lx)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have h2 := hC ρ σ (Lx t)
  simp only [pow_zero, one_mul] at h2
  have hLx : (Lx t).1 = L t := rfl
  rw [hLx] at h2
  have h3 : ‖t‖ ^ k' ≤ (K' * ‖L t‖) ^ k' := pow_le_pow_left₀ (norm_nonneg _) (hK' t) k'
  have hK0 : 0 ≤ K' := le_max_right _ _
  calc ‖t‖ ^ k' * ‖(iteratedFDeriv ℝ n' (elemLift h ρ σ) (Lx t)).compContinuousLinearMap
        fun _ => Lx‖
      ≤ (K' * ‖L t‖) ^ k' * (‖iteratedFDeriv ℝ n' (elemLift h ρ σ) (Lx t)‖ * ‖Lx‖ ^ n') :=
        mul_le_mul h3 h1 (norm_nonneg _) (by positivity)
    _ = K' ^ k' * ‖Lx‖ ^ n' * (‖L t‖ ^ k' * ‖iteratedFDeriv ℝ n' (elemLift h ρ σ) (Lx t)‖) := by
        ring
    _ ≤ K' ^ k' * ‖Lx‖ ^ n' * C := mul_le_mul_of_nonneg_left h2 (by positivity)

end SchwartzOfRapid


section StructMain

open Multiplicative
open scoped SchwartzMap

variable {Γ k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))} {m n r s : ℕ} {d : Fin s → ℕ}

lemma ofAdd_mkA_add (a b : InfiniteAdeleRing F) (c e : FiniteAdeleRing (𝓞 F) F) :
    ofAdd (mkA (a + b) (c + e)) = ofAdd (mkA a c) * ofAdd (mkA b e) := by
  rw [← mkA_add, ofAdd_add]

lemma nss_step (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hπc : Continuous π)
    (hd : ∀ i, d i ≠ 0) (hΓo : IsOpen (Γ : Set (Multiplicative (AdeleRing (𝓞 F) F)))) :
    ∃ M1 : ℕ, M1 ≠ 0 ∧ ∀ z (hz : ofAdd (mkA 0 z) ∈ Γ), z ∈ box (M1 : F) →
      π ⟨ofAdd (mkA 0 z), hz⟩ = 1 := by
  let P0 : Γ → ElemGroup m n r s d := fun γ => toAdd (π γ)
  have hP0 : Continuous P0 := continuous_toAdd.comp hπc
  have hS : IsOpen (P0 ⁻¹' Wn m n r s d) := (isOpen_Wn m n r s d hd).preimage hP0
  obtain ⟨T, hTo, hT⟩ := isOpen_induced_iff.mp hS
  let j0 : FiniteAdeleRing (𝓞 F) F → Multiplicative (AdeleRing (𝓞 F) F) := fun z => ofAdd (mkA 0 z)
  have hj0 : Continuous j0 := continuous_ofAdd.comp (continuous_mkA.comp
    (continuous_const.prodMk continuous_id))
  let O := j0 ⁻¹' (T ∩ Γ)
  have hO : IsOpen O := (hTo.inter hΓo).preimage hj0
  have hj00 : j0 0 = 1 := rfl
  have h1T : (1 : Multiplicative (AdeleRing (𝓞 F) F)) ∈ T := by
    have : (⟨1, Γ.one_mem⟩ : Γ) ∈ P0 ⁻¹' Wn m n r s d := by
      simp only [Set.mem_preimage, P0]
      have : π ⟨1, Γ.one_mem⟩ = 1 := map_one π
      rw [this, toAdd_one]; exact zero_mem_Wn m n r s d
    rw [← hT] at this; exact this
  have h0O : (0 : FiniteAdeleRing (𝓞 F) F) ∈ O := by
    change j0 0 ∈ T ∩ Γ; rw [hj00]; exact ⟨h1T, Γ.one_mem⟩
  obtain ⟨M1, hM1, hbox⟩ := exists_box_sub O (hO.mem_nhds h0O)
  refine ⟨M1, hM1, fun z hz hzb => ?_⟩
  have hk : ∀ k : ℕ, k • z ∈ O := fun k => hbox ((boxSub (M1 : F)).nsmul_mem hzb k)
  have hpow : ∀ k : ℕ, (⟨j0 (k • z), (hk k).2⟩ : Γ) = (⟨j0 z, hz⟩ : Γ) ^ k := by
    intro k
    apply Subtype.ext
    change ofAdd (mkA 0 (k • z)) = (ofAdd (mkA 0 z)) ^ k
    rw [← ofAdd_nsmul]
    congr 1
    change mkA 0 (k • z) = mkA (k • 0) (k • z)
    rw [smul_zero]
  have hW : ∀ k : ℕ, k • P0 ⟨j0 z, hz⟩ ∈ Wn m n r s d := by
    intro k
    have h1 : (⟨j0 (k • z), (hk k).2⟩ : Γ) ∈ P0 ⁻¹' Wn m n r s d := by
      rw [← hT]; exact (hk k).1
    rw [hpow k] at h1
    simp only [Set.mem_preimage, P0, map_pow, toAdd_pow] at h1
    exact h1
  have := Wn_nss m n r s d _ hW
  simp only [P0] at this
  rw [← ofAdd_toAdd (π _), this, ofAdd_zero]

end StructMain


section StructArch

open Multiplicative
open scoped SchwartzMap

variable {Γ k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))} {m n r s : ℕ} {d : Fin s → ℕ}

lemma arch_step (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hπc : Continuous π)
    (hπo : IsOpenMap π) (hπk : ∀ x : Γ, π x = 1 ↔ (x : Multiplicative (AdeleRing (𝓞 F) F)) ∈ k)
    (hko : IsOpen (annihilator k)) (M0 : ℕ)
    (hmem : ∀ x : AdeleRing (𝓞 F) F, x.2 ∈ box (M0 : F) → ofAdd x ∈ Γ) (M1 : ℕ) (hM1 : M1 ≠ 0)
    (hnss : ∀ z (hz : ofAdd (mkA 0 z) ∈ Γ), z ∈ box (M1 : F) → π ⟨ofAdd (mkA 0 z), hz⟩ = 1) :
    ∃ (L : EuclideanSpace ℝ (Ix F) →L[ℝ] (Fin m → ℝ)) (K : ℝ), (∀ t, ‖t‖ ≤ K * ‖L t‖) ∧
      IsEmpty (Fin n) ∧ ∀ t (ht : ofAdd (mkA (LH t) 0) ∈ Γ),
        (toAdd (π ⟨_, ht⟩)).1 = L t ∧ (toAdd (π ⟨_, ht⟩)).2.2 = 0 := by
  have hM1' : (M1 : F) ≠ 0 := by exact_mod_cast hM1
  let jI : EuclideanSpace ℝ (Ix F) → Multiplicative (AdeleRing (𝓞 F) F) :=
    fun t => ofAdd (mkA (LH t) 0)
  have hjI : ∀ t, jI t ∈ Γ := fun t => hmem _ (zero_mem_box _)
  let Aa : EuclideanSpace ℝ (Ix F) →+ ElemGroup m n r s d :=
    { toFun := fun t => toAdd (π ⟨jI t, hjI t⟩)
      map_zero' := by
        have : (⟨jI 0, hjI 0⟩ : Γ) = 1 := by
          apply Subtype.ext
          change ofAdd (mkA (LH 0) 0) = 1
          rw [LH_zero]; rfl
        simp only [this, map_one, toAdd_one]
      map_add' := fun a b => by
        have : (⟨jI (a + b), hjI (a + b)⟩ : Γ) = ⟨jI a, hjI a⟩ * ⟨jI b, hjI b⟩ := by
          apply Subtype.ext
          change ofAdd (mkA (LH (a + b)) 0) = ofAdd (mkA (LH a) 0) * ofAdd (mkA (LH b) 0)
          rw [LH_add, ← ofAdd_mkA_add, add_zero]
        simp only [this, map_mul, toAdd_mul] }
  have hAa : ∀ t, Aa t = toAdd (π ⟨jI t, hjI t⟩) := fun t => rfl
  have hAc : Continuous Aa := continuous_toAdd.comp (hπc.comp (Continuous.subtype_mk
    (continuous_ofAdd.comp (continuous_mkA.comp (LH.continuous.prodMk continuous_const))) _))
  have hA22 : ∀ t, (Aa t).2.2 = 0 := by
    intro t
    have := PreconnectedSpace.constant (inferInstance : PreconnectedSpace (EuclideanSpace ℝ (Ix F)))
      (f := fun t => (Aa t).2.2) ((continuous_snd.comp continuous_snd).comp hAc) (x := t) (y := 0)
    simpa using this
  have hinj : ∀ t, Aa t = 0 → t = 0 := by
    intro t ht
    have h1 : π ⟨jI t, hjI t⟩ = 1 := by
      rw [← ofAdd_toAdd (π _), ← hAa, ht, ofAdd_zero]
    have h2 := k_inf_zero hko _ ((hπk _).mp h1)
    have h3 : LH t = LH 0 := by rw [LH_zero]; exact h2
    exact LH.injective h3
  -- the range of `Aa` is a neighbourhood of `0`
  have hrange : Set.range Aa ∈ 𝓝 (0 : ElemGroup m n r s d) := by
    let Oγ : Set Γ := {γ | (toAdd (γ : Multiplicative (AdeleRing (𝓞 F) F))).2 ∈ box (M1 : F)}
    have hOγ : IsOpen Oγ := (isOpen_box _ hM1').preimage
      (continuous_snd_A.comp (continuous_toAdd.comp continuous_subtype_val))
    have h1O : (1 : Γ) ∈ Oγ := zero_mem_box _
    have hZ : IsOpen (ofAdd ⁻¹' (π '' Oγ)) := (hπo Oγ hOγ).preimage continuous_ofAdd
    have h0Z : (0 : ElemGroup m n r s d) ∈ ofAdd ⁻¹' (π '' Oγ) := ⟨1, h1O, map_one π⟩
    refine Filter.mem_of_superset (hZ.mem_nhds h0Z) ?_
    rintro e ⟨γ, hγ, hγe⟩
    set x := toAdd (γ : Multiplicative (AdeleRing (𝓞 F) F))
    set t := LH.symm x.1
    have hx : x = mkA (LH t) 0 + mkA 0 x.2 := by
      rw [mkA_add, add_zero, zero_add, Homeomorph.apply_symm_apply, mkA_eta]
    have hz : ofAdd (mkA 0 x.2) ∈ Γ := by
      have : ofAdd (mkA 0 x.2) = (jI t)⁻¹ * (γ : Multiplicative (AdeleRing (𝓞 F) F)) := by
        rw [eq_inv_mul_iff_mul_eq]
        change ofAdd (mkA (LH t) 0) * ofAdd (mkA 0 x.2) = ofAdd x
        rw [← ofAdd_add, ← hx]
      rw [this]; exact Γ.mul_mem (Γ.inv_mem (hjI t)) γ.2
    have hsplit : γ = ⟨jI t, hjI t⟩ * ⟨ofAdd (mkA 0 x.2), hz⟩ := by
      apply Subtype.ext
      change (γ : Multiplicative (AdeleRing (𝓞 F) F)) = ofAdd (mkA (LH t) 0) * ofAdd (mkA 0 x.2)
      rw [← ofAdd_add, ← hx]; rfl
    refine ⟨t, ?_⟩
    rw [hAa, ← toAdd_ofAdd e, ← hγe, hsplit, map_mul, hnss _ hz hγ, mul_one]
  -- the torus part is trivial
  have hempty : IsEmpty (Fin n) := by
    by_contra hne
    rw [not_isEmpty_iff] at hne
    obtain ⟨j0⟩ := hne
    let θ : ℝ → ElemGroup m n r s d := fun u => (0, Pi.single j0 (u : UnitAddCircle), 0)
    have hθc : Continuous θ := continuous_const.prodMk
      (((continuous_single j0).comp (AddCircle.continuous_mk' (1 : ℝ))).prodMk continuous_const)
    have hθ0 : θ 0 = 0 := by
      simp only [θ, AddCircle.coe_zero, Pi.single_zero]; rfl
    have htend : Filter.Tendsto (fun q : ℕ => θ (1 / (q : ℝ))) Filter.atTop (𝓝 0) := by
      rw [← hθ0]
      exact (hθc.tendsto 0).comp (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    obtain ⟨q, ⟨t, ht⟩, hq2⟩ := ((htend.eventually hrange).and (Filter.eventually_ge_atTop 2)).exists
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hqθ : q • θ (1 / (q : ℝ)) = 0 := by
      simp only [θ]
      refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
      funext j
      change q • (Pi.single j0 (((1 / (q : ℝ)) : ℝ) : UnitAddCircle) : Fin n → UnitAddCircle) j = 0
      by_cases hj : j = j0
      · subst hj
        rw [Pi.single_eq_same, ← AddCircle.coe_nsmul, nsmul_eq_mul, mul_one_div_cancel hq0]
        exact AddCircle.coe_period (1 : ℝ)
      · rw [Pi.single_eq_of_ne hj, smul_zero]
    have h1 : Aa (q • t) = 0 := by rw [map_nsmul, ht, hqθ]
    have h2 := hinj _ h1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact hq0 h2
    · rw [h2, map_zero] at ht
      have h3 : ((1 / (q : ℝ) : ℝ) : UnitAddCircle) = 0 := by
        have := congrArg (fun e : ElemGroup m n r s d => e.2.1 j0) ht
        simpa [θ] using this.symm
      obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h3
      rw [zsmul_eq_mul, mul_one] at hz
      have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq2
      have hlt : 1 / (q : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
      have hgt : 0 < 1 / (q : ℝ) := by positivity
      rw [← hz] at hlt hgt
      have : (0 : ℤ) < z := by exact_mod_cast hgt
      have : z < 1 := by exact_mod_cast hlt
      omega
  -- the linear map
  let Lr0 : EuclideanSpace ℝ (Ix F) →+ (Fin m → ℝ) := (AddMonoidHom.fst _ _).comp Aa
  have hLr0 : Continuous Lr0 := continuous_fst.comp hAc
  let L := Lr0.toRealLinearMap hLr0
  have hL : ∀ t, L t = (Aa t).1 := fun t => rfl
  have hker : LinearMap.ker (L : EuclideanSpace ℝ (Ix F) →ₗ[ℝ] (Fin m → ℝ)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro t ht
    apply hinj
    refine Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (hA22 t))
    exact (hL t).symm.trans ht
  obtain ⟨K0, -, hanti⟩ := LinearMap.exists_antilipschitzWith _ hker
  refine ⟨L, K0, fun t => ?_, hempty, fun t ht => ⟨(hL t).symm, hA22 t⟩⟩
  have := hanti.le_mul_dist t 0
  simpa [dist_eq_norm] using this

end StructArch


section StructFinal

open Multiplicative
open scoped SchwartzMap

variable {Γ k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))} {m n r s : ℕ} {d : Fin s → ℕ}

set_option maxHeartbeats 1600000 in
lemma pullback_mem_Tsp (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (h : ElemGroup m n r s d → ℂ) (hr : IsRapidDecay h) :
    (fun x : AdeleRing (𝓞 F) F => extendPullback Γ π h (ofAdd x)) ∈ Tsp (F := F) := by
  classical
  obtain ⟨hΓo, hgen, hk, -⟩ := hs
  obtain ⟨hd, hπc, hπo, -, hπk⟩ := hπ
  obtain ⟨M0, hM0, hmem⟩ := Gamma_contains hΓo
  obtain ⟨Nb, hNb, hbdd⟩ := Gamma_bdd hgen
  obtain ⟨M1', hM1', hnss'⟩ := nss_step π hπc hd hΓo
  obtain ⟨M1, hM1def⟩ : ∃ M1 : ℕ, M1 = M0 * M1' := ⟨_, rfl⟩
  have hM1 : M1 ≠ 0 := by rw [hM1def]; exact Nat.mul_ne_zero hM0 hM1'
  have hb1 : box (M1 : F) ⊆ box (M1' : F) := by
    have := box_natMul_sub (M1' : F) M0
    rwa [hM1def, Nat.cast_mul, mul_comm (M0 : F)]
  have hb0 : box (M1 : F) ⊆ box (M0 : F) := by
    have := box_natMul_sub (M0 : F) M1'
    rwa [hM1def, Nat.cast_mul]
  have hnss : ∀ z (hz : ofAdd (mkA 0 z) ∈ Γ), z ∈ box (M1 : F) → π ⟨ofAdd (mkA 0 z), hz⟩ = 1 :=
    fun z hz hzb => hnss' z hz (hb1 hzb)
  have hko : IsOpen (annihilator k) := hk.2.1
  obtain ⟨L, K, hK, hempty, hLA⟩ := arch_step (Γ := Γ) (k := k) π hπc hπo hπk hko M0 hmem M1 hM1 hnss
  -- the finite part of `Γ`
  let Γf : Set (FiniteAdeleRing (𝓞 F) F) := {z | ofAdd (mkA 0 z) ∈ Γ}
  have hj0c : Continuous (fun z : FiniteAdeleRing (𝓞 F) F => ofAdd (mkA (0 : InfiniteAdeleRing F) z)) :=
    continuous_ofAdd.comp (continuous_mkA.comp (continuous_const.prodMk continuous_id))
  have hΓc : IsClosed (Γ : Set (Multiplicative (AdeleRing (𝓞 F) F))) :=
    Subgroup.isClosed_of_isOpen Γ hΓo
  have hΓfsub : Γf ⊆ box ((Nb : F)⁻¹) := fun z hz => hbdd (ofAdd (mkA 0 z)) hz
  have hNb' : (Nb : F) ≠ 0 := by exact_mod_cast hNb
  have hΓfK : IsCompact Γf :=
    (isCompact_box _ (inv_ne_zero hNb')).of_isClosed_subset (hΓc.preimage hj0c) hΓfsub
  have hΓfs : ∀ z ∈ Γf, ∀ w ∈ box (M1 : F), z + w ∈ Γf := by
    intro z hz w hw
    change ofAdd (mkA 0 (z + w)) ∈ Γ
    rw [show (mkA (0 : InfiniteAdeleRing F) (z + w)) = mkA (0 + 0) (z + w) by rw [add_zero],
      ofAdd_mkA_add]
    exact Γ.mul_mem hz (hmem _ (hb0 hw))
  obtain ⟨Q, hQK, hQ⟩ := coset_decomp M1 hM1 Γf hΓfK hΓfs
  -- the Schwartz function attached to each coset
  have hΦ : ∀ q ∈ Q, ∃ Φ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ), ∀ (x : AdeleRing (𝓞 F) F)
      (hx : ofAdd x ∈ Γ), x.2 - q.out ∈ box (M1 : F) →
        h (toAdd (π ⟨ofAdd x, hx⟩)) = Φ (LH.symm x.1) := by
    intro q hq
    have hqΓ : ofAdd (mkA 0 q.out) ∈ Γ := hQK q hq
    set e := toAdd (π ⟨ofAdd (mkA 0 q.out), hqΓ⟩)
    have he1 : e.1 = 0 := by
      set N' := Nb * M1
      have hN' : N' ≠ 0 := Nat.mul_ne_zero hNb hM1
      have hmemN : N' • q.out ∈ box (M1 : F) := by
        have := mul_mem_box (alg_mem_box_self (N' : F)) (hΓfsub hqΓ)
        have hc : (N' : F) * (Nb : F)⁻¹ = M1 := by
          simp only [N', Nat.cast_mul]; field_simp
        rw [hc] at this
        rwa [nsmul_eq_mul, show ((N' : FiniteAdeleRing (𝓞 F) F)) =
          algebraMap F (FiniteAdeleRing (𝓞 F) F) (N' : F) by simp]
      have hmemΓ : ofAdd (mkA 0 (N' • q.out)) ∈ Γ := hmem _ (hb0 hmemN)
      have h1 := hnss _ hmemΓ hmemN
      have h2 : (⟨ofAdd (mkA 0 (N' • q.out)), hmemΓ⟩ : Γ) = (⟨_, hqΓ⟩ : Γ) ^ N' := by
        apply Subtype.ext
        change ofAdd (mkA 0 (N' • q.out)) = (ofAdd (mkA 0 q.out)) ^ N'
        rw [← ofAdd_nsmul]
        congr 1
        change mkA 0 (N' • q.out) = mkA (N' • 0) (N' • q.out)
        rw [smul_zero]
      rw [h2, map_pow] at h1
      have h3 : N' • e = 0 := by
        simp only [e]; rw [← toAdd_pow, h1, toAdd_one]
      have h4 : N' • e.1 = 0 := by
        have := congrArg Prod.fst h3; simpa using this
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_eq_zero] at h4
      rcases h4 with h4 | h4
      · exact absurd (by exact_mod_cast h4) hN'
      · exact h4
    obtain ⟨Φ, hΦ⟩ := schwartz_of_rapid h hr L K hK e.2.2.1 e.2.2.2
    refine ⟨Φ, fun x hx hxq => ?_⟩
    set t := LH.symm x.1
    have hjI : ofAdd (mkA (LH t) 0) ∈ Γ := hmem _ (zero_mem_box _)
    have hdq : ofAdd (mkA 0 (x.2 - q.out)) ∈ Γ := hmem _ (hb0 hxq)
    have hsplit : (⟨ofAdd x, hx⟩ : Γ) = (⟨_, hjI⟩ * ⟨_, hqΓ⟩) * ⟨_, hdq⟩ := by
      apply Subtype.ext
      change ofAdd x = ofAdd (mkA (LH t) 0) * ofAdd (mkA 0 q.out) * ofAdd (mkA 0 (x.2 - q.out))
      rw [← ofAdd_add, ← ofAdd_add, mkA_add, mkA_add, add_zero, add_zero, zero_add,
        add_sub_cancel, Homeomorph.apply_symm_apply, mkA_eta]
    rw [hsplit, map_mul π, map_mul π, hnss _ hdq hxq, mul_one, toAdd_mul, hΦ t]
    obtain ⟨hA1, hA2⟩ := hLA t hjI
    haveI := hempty
    simp only [elemLift]
    congr 1
    refine Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) ?_)
    · change (toAdd (π ⟨_, hjI⟩)).1 + e.1 = L t
      rw [hA1, he1, add_zero]
    · change (toAdd (π ⟨_, hjI⟩)).2.2 + e.2.2 = (e.2.2.1, e.2.2.2)
      rw [hA2, zero_add]
  choose! Φ hΦ using hΦ
  have hdec : ∀ x : AdeleRing (𝓞 F) F, ofAdd x = ofAdd (mkA x.1 0) * ofAdd (mkA 0 x.2) := by
    intro x
    rw [← ofAdd_add, mkA_add, add_zero, zero_add, mkA_eta]
  have hfun : (fun x : AdeleRing (𝓞 F) F => extendPullback Γ π h (ofAdd x)) =
      ∑ q ∈ Q, Tt M1 (Φ q) q.out := by
    funext x
    rw [Finset.sum_apply]
    simp only [Tt, T0]
    have e3 : ∀ r, (x - mkA 0 r).2 = x.2 - r := fun r => rfl
    have e4 : ∀ r, (x - mkA 0 r).1 = x.1 := fun r => by change x.1 - 0 = x.1; rw [sub_zero]
    simp only [e3, e4]
    unfold extendPullback
    by_cases hx : ofAdd x ∈ Γ
    · rw [dif_pos hx]
      have hterm : ∀ q ∈ Q, (box (M1 : F)).indicator (fun _ => (1 : ℂ)) (x.2 - q.out) *
          Φ q (LH.symm x.1) = (box (M1 : F)).indicator (fun _ => (1 : ℂ)) (x.2 - q.out) *
            h (toAdd (π ⟨ofAdd x, hx⟩)) := by
        intro q hq
        by_cases hm : x.2 - q.out ∈ box (M1 : F)
        · rw [hΦ q hq x hx hm]
        · simp [Set.indicator_of_notMem hm]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← hQ]
      have hxf : x.2 ∈ Γf := by
        change ofAdd (mkA 0 x.2) ∈ Γ
        have : ofAdd (mkA 0 x.2) = (ofAdd (mkA x.1 0))⁻¹ * ofAdd x := by
          rw [hdec x, inv_mul_cancel_left]
        rw [this]
        exact Γ.mul_mem (Γ.inv_mem (hmem _ (zero_mem_box _))) hx
      rw [Set.indicator_of_mem hxf, one_mul]
    · rw [dif_neg hx]
      symm
      refine Finset.sum_eq_zero fun q hq => ?_
      have hm : x.2 - q.out ∉ box (M1 : F) := by
        intro hm
        apply hx
        have h1 : x.2 ∈ Γf := by
          have := hΓfs _ (hQK q hq) _ hm
          rwa [add_sub_cancel] at this
        rw [hdec x]
        exact Γ.mul_mem (hmem _ (zero_mem_box _)) h1
      simp [Set.indicator_of_notMem hm]
  rw [hfun]
  exact Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨M1, hM1, Φ q, q.out, rfl⟩

end StructFinal


/-! ### every Schwartz–Bruhat function on the adeles lies in the class -/

section Final

open Multiplicative

lemma extendPullback_add {Γ : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))} {m n r s : ℕ}
    {d : Fin s → ℕ} (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (g1 g2 : ElemGroup m n r s d → ℂ) :
    extendPullback Γ π (g1 + g2) = extendPullback Γ π g1 + extendPullback Γ π g2 := by
  funext x; by_cases hx : x ∈ Γ <;> simp [extendPullback, hx]

lemma extendPullback_smul {Γ : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))} {m n r s : ℕ}
    {d : Fin s → ℕ} (π : Γ →* Multiplicative (ElemGroup m n r s d)) (c : ℂ)
    (g1 : ElemGroup m n r s d → ℂ) :
    extendPullback Γ π (c • g1) = c • extendPullback Γ π g1 := by
  funext x; by_cases hx : x ∈ Γ <;> simp [extendPullback, hx]

lemma extendPullback_zero {Γ : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))} {m n r s : ℕ}
    {d : Fin s → ℕ} (π : Γ →* Multiplicative (ElemGroup m n r s d)) :
    extendPullback Γ π (0 : ElemGroup m n r s d → ℂ) = 0 := by
  funext x; by_cases hx : x ∈ Γ <;> simp [extendPullback, hx]

lemma elem_mem_Tsp {Γ k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))} {m n r s : ℕ}
    {d : Fin s → ℕ} (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (g : ElemGroup m n r s d → ℂ)
    (hg : g ∈ elemSchwartzSubmodule m n r s d) :
    (fun x : AdeleRing (𝓞 F) F => extendPullback Γ π g (ofAdd x)) ∈ Tsp (F := F) := by
  induction hg using Submodule.span_induction with
  | mem h hh => exact pullback_mem_Tsp π hs hπ h hh
  | zero =>
    rw [extendPullback_zero]; exact (Tsp (F := F)).zero_mem
  | add a b _ _ ha hb =>
    rw [extendPullback_add]; exact (Tsp (F := F)).add_mem ha hb
  | smul c a _ ha =>
    rw [extendPullback_smul]; exact (Tsp (F := F)).smul_mem c ha

lemma sb_mem_Tsp (φ : Multiplicative (AdeleRing (𝓞 F) F) → ℂ)
    (hφ : φ ∈ schwartzBruhatSubmodule (Multiplicative (AdeleRing (𝓞 F) F))) :
    (fun x : AdeleRing (𝓞 F) F => φ (ofAdd x)) ∈ Tsp (F := F) := by
  induction hφ using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩ := hf
    exact elem_mem_Tsp π hs hπ g.toFun g.2
  | zero => exact (Tsp (F := F)).zero_mem
  | add a b _ _ ha hb => exact (Tsp (F := F)).add_mem ha hb
  | smul c a _ ha => exact (Tsp (F := F)).smul_mem c ha

lemma eval_mem_Tsp (f : AdelicSchwartz F) : f.eval ∈ Tsp (F := F) :=
  sb_mem_Tsp f.1 f.2

end Final


/-! ### separated point sets in a Euclidean space -/

section Euclid

open MeasureTheory Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [μ.IsAddHaarMeasure] in
/-- tail of `(1+‖x‖)^{-k}` -/
lemma tail_le (k m ρ : ℝ) (hkm : m ≤ k) (hρ : 0 ≤ ρ) :
    ∫⁻ x in {x : E | ρ ≤ ‖x‖}, ENNReal.ofReal ((1 + ‖x‖) ^ (-k)) ∂μ ≤
      ENNReal.ofReal ((1 + ρ) ^ (-(k - m))) * ∫⁻ x, ENNReal.ofReal ((1 + ‖x‖) ^ (-m)) ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans ?_ (setLIntegral_le_lintegral {x : E | ρ ≤ ‖x‖} _)
  refine (setLIntegral_mono (by fun_prop) fun x hx => ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : 0 < 1 + ‖x‖ := by positivity
  have h2 : (1 + ‖x‖) ^ (-k) = (1 + ‖x‖) ^ (-(k - m)) * (1 + ‖x‖) ^ (-m) := by
    rw [← Real.rpow_add h1]; ring_nf
  rw [h2]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by simpa using hx) (by linarith)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] in
/-- separated point sets: the basic packing bound -/
lemma sep_sum {ι : Type*} [Countable ι] (S : Set ι) (l : ι → E) (r : ℝ)
    (h1 : ∀ i ∈ S, r ≤ ‖l i‖) (h2 : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → r ≤ ‖l i - l j‖) (k : ℝ)
    (hk : 0 ≤ k) :
    (∑' i, S.indicator (fun i => ENNReal.ofReal ((1 + ‖l i‖) ^ (-k))) i) * μ (ball 0 (r / 2)) ≤
      ENNReal.ofReal ((3 / 2) ^ k) *
        ∫⁻ x in {x : E | r / 2 ≤ ‖x‖}, ENNReal.ofReal ((1 + ‖x‖) ^ (-k)) ∂μ := by
  classical
  let s : ι → Set E := fun i => if i ∈ S then ball (l i) (r / 2) else ∅
  have hs : ∀ i, MeasurableSet (s i) := by
    intro i; by_cases hi : i ∈ S <;> simp [s, hi, measurableSet_ball]
  have hd : Pairwise (Function.onFun Disjoint s) := by
    intro i j hij
    by_cases hi : i ∈ S
    · by_cases hj : j ∈ S
      · simp only [Function.onFun, s, hi, hj, if_true]
        rw [Set.disjoint_left]
        intro x hxi hxj
        rw [mem_ball] at hxi hxj
        have := h2 i hi j hj hij
        have h3 : dist (l i) (l j) ≤ dist x (l i) + dist x (l j) := dist_triangle_left _ _ _
        rw [dist_eq_norm] at h3
        linarith
      · simp [Function.onFun, s, hj]
    · simp [Function.onFun, s, hi]
  let G : E → ENNReal := fun x => ENNReal.ofReal ((3 / 2) ^ k * (1 + ‖x‖) ^ (-k))
  have hG : Measurable G := by fun_prop
  have hterm : ∀ i, S.indicator (fun i => ENNReal.ofReal ((1 + ‖l i‖) ^ (-k))) i *
      μ (ball 0 (r / 2)) ≤ ∫⁻ x in s i, G x ∂μ := by
    intro i
    by_cases hi : i ∈ S
    · rw [Set.indicator_of_mem hi]
      simp only [s, hi, if_true]
      rw [← Measure.addHaar_ball_center μ (l i), ← setLIntegral_const]
      refine setLIntegral_mono hG fun x hx => ?_
      refine ENNReal.ofReal_le_ofReal ?_
      rw [mem_ball, dist_eq_norm] at hx
      have hli := h1 i hi
      have hx1 : 1 + ‖x‖ ≤ (3 / 2) * (1 + ‖l i‖) := by
        have : ‖x‖ ≤ ‖x - l i‖ + ‖l i‖ := by
          have := norm_add_le (x - l i) (l i); rwa [sub_add_cancel] at this
        nlinarith
      have hpos : 0 < 1 + ‖x‖ := by positivity
      have h4 := Real.rpow_le_rpow_of_nonpos hpos hx1 (by linarith : -k ≤ 0)
      rw [Real.mul_rpow (by norm_num) (by positivity)] at h4
      have h5 : (3 / 2 : ℝ) ^ (-k) * (3 / 2) ^ k = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      have h6 : (0 : ℝ) ≤ (3 / 2) ^ k := by positivity
      calc (1 + ‖l i‖) ^ (-k) = ((3 / 2 : ℝ) ^ (-k) * (3 / 2) ^ k) * (1 + ‖l i‖) ^ (-k) := by
            rw [h5, one_mul]
        _ = (3 / 2) ^ k * ((3 / 2 : ℝ) ^ (-k) * (1 + ‖l i‖) ^ (-k)) := by ring
        _ ≤ (3 / 2) ^ k * (1 + ‖x‖) ^ (-k) := mul_le_mul_of_nonneg_left h4 h6
    · rw [Set.indicator_of_notMem hi, zero_mul]; exact zero_le
  have hsub : (⋃ i, s i) ⊆ {x : E | r / 2 ≤ ‖x‖} := by
    intro x hx
    obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    by_cases hi : i ∈ S
    · simp only [s, hi, if_true, mem_ball, dist_eq_norm] at hx
      have hli := h1 i hi
      have : ‖l i‖ ≤ ‖x‖ + ‖x - l i‖ := by
        have := norm_sub_le x (x - l i); rwa [sub_sub_cancel] at this
      show r / 2 ≤ ‖x‖
      linarith
    · simp [s, hi] at hx
  calc (∑' i, S.indicator (fun i => ENNReal.ofReal ((1 + ‖l i‖) ^ (-k))) i) * μ (ball 0 (r / 2))
      = ∑' i, S.indicator (fun i => ENNReal.ofReal ((1 + ‖l i‖) ^ (-k))) i *
          μ (ball 0 (r / 2)) := ENNReal.tsum_mul_right.symm
    _ ≤ ∑' i, ∫⁻ x in s i, G x ∂μ := ENNReal.tsum_le_tsum hterm
    _ = ∫⁻ x in ⋃ i, s i, G x ∂μ := (lintegral_iUnion hs hd G).symm
    _ ≤ ∫⁻ x in {x : E | r / 2 ≤ ‖x‖}, G x ∂μ := lintegral_mono_set hsub
    _ = _ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun x => ?_
      simp only [G]
      rw [ENNReal.ofReal_mul (by positivity)]

/-- separated point sets: real form -/
lemma sep_real {ι : Type*} [Countable ι] (S : Set ι) (l : ι → E) (r : ℝ) (hr : 0 < r)
    (h1 : ∀ i ∈ S, r ≤ ‖l i‖) (h2 : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → r ≤ ‖l i - l j‖) (k : ℝ)
    (hk : (Module.finrank ℝ E : ℝ) + 1 ≤ k) :
    Summable (fun i => S.indicator (fun i => (1 + ‖l i‖) ^ (-k)) i) ∧
    ∑' i, S.indicator (fun i => (1 + ‖l i‖) ^ (-k)) i ≤
      (3 / 2) ^ k * (1 + r / 2) ^ (-(k - ((Module.finrank ℝ E : ℝ) + 1))) *
        (∫⁻ x, ENNReal.ofReal ((1 + ‖x‖) ^ (-((Module.finrank ℝ E : ℝ) + 1))) ∂μ).toReal /
        (r ^ Module.finrank ℝ E * (μ (ball 0 (1 / 2))).toReal) := by
  classical
  set m : ℝ := (Module.finrank ℝ E : ℝ) + 1
  have hk0 : 0 ≤ k := by
    have : (0 : ℝ) ≤ Module.finrank ℝ E := by positivity
    linarith
  set f : ι → ENNReal := fun i => S.indicator (fun i => ENNReal.ofReal ((1 + ‖l i‖) ^ (-k))) i
  have hf : ∀ i, f i ≠ ⊤ := by
    intro i; by_cases hi : i ∈ S <;> simp [f, hi]
  have hfr : ∀ i, (f i).toReal = S.indicator (fun i => (1 + ‖l i‖) ^ (-k)) i := by
    intro i
    by_cases hi : i ∈ S
    · simp only [f, Set.indicator_of_mem hi]
      exact ENNReal.toReal_ofReal (by positivity)
    · simp [f, hi]
  set Im := ∫⁻ x, ENNReal.ofReal ((1 + ‖x‖) ^ (-m)) ∂μ
  have hIm : Im ≠ ⊤ := (finite_integral_one_add_norm (μ := μ) (by simp [m])).ne
  have hmain := sep_sum μ S l r h1 h2 k hk0
  have htail := tail_le μ k m (r / 2) hk (by positivity)
  have hB : μ (ball 0 (r / 2)) = ENNReal.ofReal (r ^ Module.finrank ℝ E) * μ (ball 0 (1 / 2)) := by
    rw [← Measure.addHaar_ball_mul μ 0 hr.le]; ring_nf
  have hB0 : μ (ball (0 : E) (r / 2)) ≠ 0 := (measure_ball_pos μ 0 (by positivity)).ne'
  have hBt : μ (ball (0 : E) (r / 2)) ≠ ⊤ := measure_ball_lt_top.ne
  set R : ENNReal := ENNReal.ofReal ((3 / 2) ^ k) * (ENNReal.ofReal ((1 + r / 2) ^ (-(k - m))) * Im)
  have hRt : R ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIm)
  have hAB : (∑' i, f i) * μ (ball 0 (r / 2)) ≤ R :=
    hmain.trans (mul_le_mul' le_rfl htail)
  have hA : (∑' i, f i) ≤ R / μ (ball 0 (r / 2)) := (ENNReal.le_div_iff_mul_le (Or.inl hB0)
    (Or.inl hBt)).mpr hAB
  have hAt : (∑' i, f i) ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.div_ne_top hRt hB0) hA
  have hsum := ENNReal.summable_toReal hAt
  simp only [hfr] at hsum
  refine ⟨hsum, ?_⟩
  have e1 : ∑' i, S.indicator (fun i => (1 + ‖l i‖) ^ (-k)) i = (∑' i, f i).toReal := by
    rw [ENNReal.tsum_toReal_eq hf]; simp only [hfr]
  rw [e1]
  refine (ENNReal.toReal_mono (ENNReal.div_ne_top hRt hB0) hA).trans (le_of_eq ?_)
  have e2 : (ENNReal.ofReal (r ^ Module.finrank ℝ E)).toReal = r ^ Module.finrank ℝ E :=
    ENNReal.toReal_ofReal (by positivity)
  rw [ENNReal.toReal_div, hB]
  simp only [R, ENNReal.toReal_mul, e2, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (3 / 2) ^ k),
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (1 + r / 2) ^ (-(k - m)))]
  ring

end Euclid


/-! ### the product formula lower bound -/

section Arith

lemma ideleNorm_split (g : IdeleGroup F) : ideleNorm g =
    ‖(g : AdeleRing (𝓞 F) F).1‖ * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(g : AdeleRing (𝓞 F) F).2 v‖ := by
  unfold ideleNorm; rw [InfiniteAdeleRing.norm_def]

lemma fin_le_one (g : IdeleGroup F)
    (hg : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((g : AdeleRing (𝓞 F) F).2 v) ≤ 1) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(g : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 := by
  have := finprod_induction (fun x : ℝ => 0 ≤ x ∧ x ≤ 1) ⟨zero_le_one, le_rfl⟩
    (fun a b ha hb => ⟨mul_nonneg ha.1 hb.1, mul_le_one₀ ha.2 hb.1 hb.2⟩)
    (fun v => ⟨norm_nonneg _, Valued.toNormedField.norm_le_one_iff.mpr
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hg v))⟩)
    (f := fun v : HeightOneSpectrum (𝓞 F) => ‖(g : AdeleRing (𝓞 F) F).2 v‖)
  exact this.2

lemma ideleNorm_le_inf (g : IdeleGroup F)
    (hg : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((g : AdeleRing (𝓞 F) F).2 v) ≤ 1) :
    ideleNorm g ≤ ‖(g : AdeleRing (𝓞 F) F).1‖ := by
  rw [ideleNorm_split]
  have h0 : 0 ≤ ‖(g : AdeleRing (𝓞 F) F).1‖ := by
    rw [InfiniteAdeleRing.norm_def]; positivity
  calc _ ≤ ‖(g : AdeleRing (𝓞 F) F).1‖ * 1 := mul_le_mul_of_nonneg_left (fin_le_one g hg) h0
    _ = _ := mul_one _

lemma mulL_comm_apply (y z : InfiniteAdeleRing F) :
    LH.symm (y * z) = mulL y (LH.symm z) := by
  rw [mulL_apply, Homeomorph.apply_symm_apply, mul_comm]

/-- the normalized norm on `F_∞` is bounded by a power of the coordinate norm -/
lemma inf_norm_le : ∃ C : ℝ, 0 < C ∧ ∀ y : InfiniteAdeleRing F,
    ‖y‖ ≤ C * ‖LH.symm y‖ ^ Fintype.card (Ix F) := by
  classical
  let e : Ix F → EuclideanSpace ℝ (Ix F) := fun j => EuclideanSpace.single j (1 : ℝ)
  let T : Ix F → (EuclideanSpace ℝ (Ix F) →L[ℝ] EuclideanSpace ℝ (Ix F)) :=
    fun j => LinearMap.toContinuousLinearMap (mulL (LH (e j)))
  set C₁ : ℝ := ∑ j, ‖T j‖ + 1
  have hC₁ : 0 < C₁ := by positivity
  refine ⟨(Fintype.card (Ix F)).factorial * C₁ ^ Fintype.card (Ix F), by positivity, fun y => ?_⟩
  rw [← abs_det_mulL, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Ix F) ℝ).toBasis]
  have hent : ∀ i j, AbsoluteValue.abs (LinearMap.toMatrix (EuclideanSpace.basisFun (Ix F) ℝ).toBasis
      (EuclideanSpace.basisFun (Ix F) ℝ).toBasis (mulL y) i j) ≤ C₁ * ‖LH.symm y‖ := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr, AbsoluteValue.abs_apply]
    have e1 : mulL y (EuclideanSpace.single j 1) = T j (LH.symm y) := by
      change _ = mulL (LH (e j)) (LH.symm y)
      rw [← mulL_comm_apply, mulL_apply, mul_comm]
    rw [e1]
    have h1 : |(T j (LH.symm y)) i| ≤ ‖T j (LH.symm y)‖ := by
      have := PiLp.norm_apply_le (T j (LH.symm y)) i
      rwa [Real.norm_eq_abs] at this
    have h2 : ‖T j‖ ≤ C₁ := by
      have := Finset.single_le_sum (f := fun j => ‖T j‖) (fun j _ => norm_nonneg _)
        (Finset.mem_univ j)
      simp only [C₁]; linarith
    calc |(T j (LH.symm y)) i| ≤ ‖T j (LH.symm y)‖ := h1
      _ ≤ ‖T j‖ * ‖LH.symm y‖ := (T j).le_opNorm _
      _ ≤ C₁ * ‖LH.symm y‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have := Matrix.det_le hent
  rw [AbsoluteValue.abs_apply, nsmul_eq_mul, mul_pow] at this
  simpa [mul_assoc] using this

/-- the product formula forces archimedean coordinates of `ξ h` to be large -/
lemma lam_lower (c : F) (hc : c ≠ 0) : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (h : IdeleGroup F) (ξ : F), ξ ≠ 0 →
    (algebraMap F (AdeleRing (𝓞 F) F) ξ * (h : AdeleRing (𝓞 F) F)).2 ∈ box c →
    c₀ * ideleNorm h ≤ ‖LH.symm (algebraMap F (AdeleRing (𝓞 F) F) ξ * (h : AdeleRing (𝓞 F) F)).1‖ ^
      Fintype.card (Ix F) := by
  obtain ⟨C, hC, hCy⟩ := inf_norm_le (F := F)
  set K : ℝ := ‖LinearMap.toContinuousLinearMap (mulL (algebraMap F (InfiniteAdeleRing F) c⁻¹))‖ + 1
  have hK : 0 < K := by positivity
  refine ⟨1 / (C * K ^ Fintype.card (Ix F)), by positivity, fun h ξ hξ hbox => ?_⟩
  set x := algebraMap F (AdeleRing (𝓞 F) F) ξ * (h : AdeleRing (𝓞 F) F)
  have hcξ : c⁻¹ * ξ ≠ 0 := mul_ne_zero (inv_ne_zero hc) hξ
  set u : IdeleGroup F := principalIdele F (Units.mk0 (c⁻¹ * ξ) hcξ) * h
  have hu : (u : AdeleRing (𝓞 F) F) = algebraMap F (AdeleRing (𝓞 F) F) c⁻¹ * x := by
    simp only [u, x, Units.val_mul, principal_coe, Units.val_mk0, map_mul, mul_assoc]
  have hnu : ideleNorm u = ideleNorm h := by
    rw [ideleNorm_mul, ideleNorm_principal, one_mul]
  have hint : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((u : AdeleRing (𝓞 F) F).2 v) ≤ 1 := by
    have := (mem_box_iff_mul c hc x.2).mp hbox
    rw [mem_box_one] at this
    intro v
    rw [hu]
    exact this v
  have h1 := ideleNorm_le_inf u hint
  rw [hnu] at h1
  have h2 := hCy (u : AdeleRing (𝓞 F) F).1
  have e3 : LH.symm (u : AdeleRing (𝓞 F) F).1 =
      mulL (algebraMap F (InfiniteAdeleRing F) c⁻¹) (LH.symm x.1) := by
    rw [hu, ← mulL_comm_apply]; rfl
  have h3 : ‖LH.symm (u : AdeleRing (𝓞 F) F).1‖ ≤ K * ‖LH.symm x.1‖ := by
    rw [e3]
    have := (LinearMap.toContinuousLinearMap (mulL (algebraMap F (InfiniteAdeleRing F) c⁻¹))).le_opNorm
      (LH.symm x.1)
    refine this.trans (mul_le_mul_of_nonneg_right (by simp [K]) (norm_nonneg _))
  have h4 : ‖LH.symm (u : AdeleRing (𝓞 F) F).1‖ ^ Fintype.card (Ix F) ≤
      (K * ‖LH.symm x.1‖) ^ Fintype.card (Ix F) := pow_le_pow_left₀ (norm_nonneg _) h3 _
  rw [mul_pow] at h4
  have h5 : ideleNorm h ≤ C * K ^ Fintype.card (Ix F) * ‖LH.symm x.1‖ ^ Fintype.card (Ix F) := by
    calc ideleNorm h ≤ C * ‖LH.symm (u : AdeleRing (𝓞 F) F).1‖ ^ Fintype.card (Ix F) := h1.trans h2
      _ ≤ C * (K ^ Fintype.card (Ix F) * ‖LH.symm x.1‖ ^ Fintype.card (Ix F)) :=
          mul_le_mul_of_nonneg_left h4 hC.le
      _ = _ := by ring
  have hCK : 0 < C * K ^ Fintype.card (Ix F) := by positivity
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hCK]
  linarith

end Arith


/-! ### decay of lattice sums over `Fˣ` -/

section LatDecay

open MeasureTheory Metric

/-- the weight `1_{c Ô}(x_f) (1 + ‖x_∞‖)^{-k}` -/
noncomputable def Wt (c : F) (k : ℝ) (x : AdeleRing (𝓞 F) F) : ℝ :=
  (box c).indicator (fun _ => (1 : ℝ)) x.2 * (1 + ‖LH.symm x.1‖) ^ (-k)

lemma Wt_nonneg (c : F) (k : ℝ) (x : AdeleRing (𝓞 F) F) : 0 ≤ Wt c k x := by
  unfold Wt
  by_cases hx : x.2 ∈ box c
  · rw [Set.indicator_of_mem hx]; positivity
  · rw [Set.indicator_of_notMem hx, zero_mul]

instance nontrivial_E : Nontrivial (EuclideanSpace ℝ (Ix F)) := by
  refine nontrivial_of_ne (LH.symm 1) (LH.symm 0) fun h => ?_
  have := congrArg LH h
  simp only [Homeomorph.apply_symm_apply] at this
  exact one_ne_zero this

lemma card_Ix_pos : 0 < Fintype.card (Ix F) := by
  have := Module.finrank_pos (R := ℝ) (M := EuclideanSpace ℝ (Ix F))
  rwa [finrank_euclideanSpace] at this

lemma alg_mul_sub (ξ η : F) (h : AdeleRing (𝓞 F) F) :
    algebraMap F (AdeleRing (𝓞 F) F) (ξ - η) * h =
      algebraMap F (AdeleRing (𝓞 F) F) ξ * h - algebraMap F (AdeleRing (𝓞 F) F) η * h := by
  rw [map_sub, sub_mul]

/-- lattice sums of the weight decay faster than any power of `|h|` -/
theorem wt_decay (c : F) (hc : c ≠ 0) (N : ℕ) : ∃ k C : ℝ, 0 ≤ k ∧ 0 ≤ C ∧
    ∀ h : IdeleGroup F, 1 ≤ ideleNorm h →
      Summable (fun ξ : Fˣ => Wt c k (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) *
        (h : AdeleRing (𝓞 F) F))) ∧
      ∑' ξ : Fˣ, Wt c k (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (h : AdeleRing (𝓞 F) F)) ≤
        C * ideleNorm h ^ (-(N : ℝ)) := by
  classical
  obtain ⟨c₀, hc₀, hlow⟩ := lam_lower (F := F) c hc
  set d := Fintype.card (Ix F)
  have hd : 0 < d := card_Ix_pos
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Ix F)) = d := finrank_euclideanSpace
  set m : ℝ := (d : ℝ) + 1
  set k : ℝ := m + d * N
  set Im : ℝ := (∫⁻ x : EuclideanSpace ℝ (Ix F), ENNReal.ofReal ((1 + ‖x‖) ^ (-m))).toReal
  set V : ℝ := (volume (ball (0 : EuclideanSpace ℝ (Ix F)) (1 / 2))).toReal
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos volume _ (by norm_num)).ne'
    measure_ball_lt_top.ne
  have hIm : 0 ≤ Im := ENNReal.toReal_nonneg
  have hk : 0 ≤ k := by positivity
  set P : ℝ := (3 / 2) ^ k * (c₀ / 2 ^ d) ^ (-(N : ℝ)) * Im
  have hP : 0 ≤ P := by positivity
  refine ⟨k, P / (c₀ * V), hk, by positivity, fun h hh => ?_⟩
  have hn : 0 < ideleNorm h := ideleNorm_pos h
  set X := c₀ * ideleNorm h
  have hX : 0 < X := by positivity
  set r : ℝ := X ^ ((d : ℝ)⁻¹)
  have hr : 0 < r := Real.rpow_pos_of_pos hX _
  have hrd : r ^ d = X := Real.rpow_inv_natCast_pow hX.le hd.ne'
  set l : Fˣ → EuclideanSpace ℝ (Ix F) :=
    fun ξ => LH.symm (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (h : AdeleRing (𝓞 F) F)).1
  set S : Set Fˣ := {ξ | (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (h : AdeleRing (𝓞 F) F)).2 ∈ box c}
  have hlr : ∀ (ζ : F), ζ ≠ 0 →
      (algebraMap F (AdeleRing (𝓞 F) F) ζ * (h : AdeleRing (𝓞 F) F)).2 ∈ box c →
      r ≤ ‖LH.symm (algebraMap F (AdeleRing (𝓞 F) F) ζ * (h : AdeleRing (𝓞 F) F)).1‖ := by
    intro ζ hζ hb
    have h1 : r ^ d ≤ ‖LH.symm (algebraMap F (AdeleRing (𝓞 F) F) ζ * (h : AdeleRing (𝓞 F) F)).1‖ ^ d := by
      rw [hrd]; exact hlow h ζ hζ hb
    exact le_of_pow_le_pow_left₀ hd.ne' (norm_nonneg _) h1
  have h1 : ∀ ξ ∈ S, r ≤ ‖l ξ‖ := fun ξ hξ => hlr ξ ξ.ne_zero hξ
  have h2 : ∀ ξ ∈ S, ∀ η ∈ S, ξ ≠ η → r ≤ ‖l ξ - l η‖ := by
    intro ξ hξ η hη hne
    have hne' : (ξ : F) - η ≠ 0 := sub_ne_zero.mpr (fun h => hne (Units.val_injective h))
    have hb : (algebraMap F (AdeleRing (𝓞 F) F) ((ξ : F) - η) * (h : AdeleRing (𝓞 F) F)).2 ∈ box c := by
      rw [alg_mul_sub]; exact sub_mem_box hξ hη
    have := hlr _ hne' hb
    simp only [l]
    rw [alg_mul_sub] at this
    have e : (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (h : AdeleRing (𝓞 F) F) -
        algebraMap F (AdeleRing (𝓞 F) F) (η : F) * (h : AdeleRing (𝓞 F) F)).1 =
        (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (h : AdeleRing (𝓞 F) F)).1 -
        (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * (h : AdeleRing (𝓞 F) F)).1 := rfl
    rwa [e, LH_symm_sub] at this
  have hW : ∀ ξ : Fˣ, Wt c k (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (h : AdeleRing (𝓞 F) F)) =
      S.indicator (fun ξ => (1 + ‖l ξ‖) ^ (-k)) ξ := by
    intro ξ
    unfold Wt
    by_cases hξ : ξ ∈ S
    · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem (show _ ∈ box c from hξ), one_mul]
    · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem (show _ ∉ box c from hξ), zero_mul]
  haveI : Countable Fˣ := by
    haveI := countable_F (F := F)
    exact Function.Injective.countable Units.val_injective
  have hkm : (Module.finrank ℝ (EuclideanSpace ℝ (Ix F)) : ℝ) + 1 ≤ k := by
    rw [hfr]; simp only [k, m]; nlinarith [show (0 : ℝ) ≤ d * N by positivity]
  obtain ⟨hs, hb⟩ := sep_real volume S l r hr h1 h2 k hkm
  simp only [hW]
  refine ⟨hs, hb.trans ?_⟩
  rw [hfr]
  change (3 / 2) ^ k * (1 + r / 2) ^ (-(k - m)) * Im / (r ^ d * V) ≤ _
  have hb1 : (1 + r / 2) ^ (-(k - m)) ≤ (r / 2) ^ (-(k - m)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith)
      (by simp only [k]; nlinarith [show (0 : ℝ) ≤ d * N by positivity])
  have hb2 : (r / 2) ^ (-(k - m)) = (c₀ / 2 ^ d) ^ (-(N : ℝ)) * ideleNorm h ^ (-(N : ℝ)) := by
    rw [show -(k - m) = (d : ℝ) * (-(N : ℝ)) by simp only [k]; ring, Real.rpow_mul (by positivity),
      Real.rpow_natCast, div_pow, hrd, ← Real.mul_rpow (by positivity) hn.le]
    congr 1
    simp only [X]; ring
  rw [hrd]
  calc (3 / 2) ^ k * (1 + r / 2) ^ (-(k - m)) * Im / (X * V)
      ≤ (3 / 2) ^ k * (r / 2) ^ (-(k - m)) * Im / (X * V) := by
        gcongr
    _ = P * ideleNorm h ^ (-(N : ℝ)) / (X * V) := by rw [hb2]; simp only [P]; ring
    _ ≤ P * ideleNorm h ^ (-(N : ℝ)) / (c₀ * V) := by
        gcongr
        simp only [X]
        nlinarith
    _ = P / (c₀ * V) * ideleNorm h ^ (-(N : ℝ)) := by ring

end LatDecay


/-! ### the Fourier transform of `T₀` at a general point -/

section T0hat

open MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace

/-- `t ↦ tr_∞(LH t · y)` as an additive map -/
noncomputable def trLinY (y : InfiniteAdeleRing F) : EuclideanSpace ℝ (Ix F) →+ ℝ where
  toFun t := trI (LH t * y)
  map_zero' := by simp [LH_zero, trI_zero]
  map_add' a b := by simp [LH_add, add_mul, trI_add]

lemma continuous_trLinY (y : InfiniteAdeleRing F) : Continuous (trLinY y) :=
  continuous_trI.comp ((continuous_LH).mul continuous_const)

lemma trI_LH_mul (s : EuclideanSpace ℝ (Ix F)) (y : InfiniteAdeleRing F) :
    trI (LH s * y) = ∑ i, s i * trI (LH (AuxP.zpt (Pi.single i 1)) * y) := by
  change trLinY y s = _
  have ht : s = ∑ i, s i • AuxP.zpt (Pi.single i 1) := by
    ext j
    simp [AuxP.zpt, Pi.single_apply, Finset.sum_apply]
  conv_lhs => rw [ht]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_real_smul (trLinY y) (continuous_trLinY y), smul_eq_mul]
  rfl

/-- the vector representing the linear form `s ↦ tr_∞(LH s · y)` -/
noncomputable def Bv (y : InfiniteAdeleRing F) : EuclideanSpace ℝ (Ix F) :=
  WithLp.toLp 2 (fun i => trI (LH (AuxP.zpt (Pi.single i 1)) * y))

lemma inner_Bv (s : EuclideanSpace ℝ (Ix F)) (y : InfiniteAdeleRing F) :
    ⟪s, Bv y⟫ = trI (LH s * y) := by
  rw [trI_LH_mul]
  simp [Bv, PiLp.inner_apply, mul_comm]

lemma Bv_add (y z : InfiniteAdeleRing F) : Bv (y + z) = Bv y + Bv z := by
  ext i; simp [Bv, mul_add, trI_add]

lemma Bv_zero : Bv (0 : InfiniteAdeleRing F) = 0 := by
  ext i; simp [Bv, trI_zero]

lemma continuous_Bv : Continuous (Bv (F := F)) := by
  unfold Bv
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  exact continuous_trI.comp (continuous_const.mul continuous_id)

/-- non-degeneracy of the archimedean trace form -/
lemma trI_nondeg (y : InfiniteAdeleRing F) (h : ∀ z : InfiniteAdeleRing F, trI (z * y) = 0) :
    y = 0 := by
  classical
  funext w
  by_contra hw
  let z : InfiniteAdeleRing F := Pi.single w (y w)⁻¹
  have h1 := h z
  have h2 : z * y = Pi.single w 1 := by
    funext w'
    by_cases hw' : w' = w
    · subst hw'
      rw [show (z * y) w' = z w' * y w' from rfl]
      simp [z, inv_mul_cancel₀ hw]
    · change z w' * y w' = _; simp [z, Pi.single_apply, hw']
  rw [h2] at h1
  unfold trI at h1
  rw [Finset.sum_eq_single w (fun w' _ hw' => by simp [Pi.single_apply, hw'])
    (fun h => absurd (Finset.mem_univ w) h)] at h1
  simp only [Pi.single_eq_same, map_one, Complex.one_re, mul_one] at h1
  have : (0 : ℝ) < w.mult := by exact_mod_cast InfinitePlace.mult_pos
  linarith

/-- `‖LH⁻¹ y‖ ≤ K ‖Bv y‖` -/
lemma Bv_anti : ∃ K : ℝ, 0 < K ∧ ∀ y : InfiniteAdeleRing F, ‖LH.symm y‖ ≤ K * ‖Bv y‖ := by
  let BA : EuclideanSpace ℝ (Ix F) →+ EuclideanSpace ℝ (Ix F) :=
    { toFun := fun t => Bv (LH t)
      map_zero' := by rw [LH_zero, Bv_zero]
      map_add' := fun a b => by rw [LH_add, Bv_add] }
  have hBA : Continuous BA := continuous_Bv.comp continuous_LH
  let BL := BA.toRealLinearMap hBA
  have hker : LinearMap.ker (BL : EuclideanSpace ℝ (Ix F) →ₗ[ℝ] EuclideanSpace ℝ (Ix F)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro t ht
    have ht' : Bv (LH t) = 0 := ht
    have hall : ∀ z : InfiniteAdeleRing F, trI (z * LH t) = 0 := by
      intro z
      have := inner_Bv (LH.symm z) (LH t)
      rw [ht', inner_zero_right, Homeomorph.apply_symm_apply] at this
      exact this.symm
    have h0 := trI_nondeg _ hall
    have : LH t = LH 0 := by rw [h0, LH_zero]
    exact LH.injective this
  obtain ⟨K0, -, hanti⟩ := LinearMap.exists_antilipschitzWith _ hker
  refine ⟨K0 + 1, by positivity, fun y => ?_⟩
  have h1 := hanti.le_mul_dist (LH.symm y) 0
  simp only [dist_eq_norm, sub_zero, map_zero] at h1
  have h2 : ‖(BL : EuclideanSpace ℝ (Ix F) →ₗ[ℝ] EuclideanSpace ℝ (Ix F)) (LH.symm y)‖ = ‖Bv y‖ := by
    congr 1
    change Bv (LH (LH.symm y)) = Bv y
    rw [Homeomorph.apply_symm_apply]
  rw [h2] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right (by simp) (norm_nonneg _))

lemma T0_shift (M : ℕ) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) (z : FiniteAdeleRing (𝓞 F) F)
    (hz : z ∈ box (M : F)) (x : AdeleRing (𝓞 F) F) : T0 M Ψ (mkA 0 z + x) = T0 M Ψ x := by
  have h1 : (mkA 0 z + x).1 = x.1 := by
    change (0 : InfiniteAdeleRing F) + x.1 = x.1; rw [zero_add]
  have h2 : (mkA 0 z + x).2 = z + x.2 := rfl
  by_cases hx : x.2 ∈ box (M : F)
  · rw [T0_of_mem M Ψ x hx, T0_of_mem M Ψ _ (by rw [h2]; exact add_mem_box hz hx), h1]
  · have : (mkA 0 z + x).2 ∉ box (M : F) := by
      rw [h2]; intro h; apply hx
      have := sub_mem_box h hz
      rwa [add_sub_cancel_left] at this
    rw [T0_of_not_mem M Ψ x hx, T0_of_not_mem M Ψ _ this]

lemma T0hat_char (M : ℕ) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) (y : AdeleRing (𝓞 F) F)
    (hne : adelicFourierFun (T0 M Ψ) y ≠ 0) (z : FiniteAdeleRing (𝓞 F) F) (hz : z ∈ box (M : F)) :
    stdAdelicCharacter (mkA 0 (z * y.2)) = 1 := by
  set a : AdeleRing (𝓞 F) F := mkA 0 z
  have hay : a * y = mkA 0 (z * y.2) := by
    change mkA 0 z * mkA y.1 y.2 = _; rw [mkA_mul, zero_mul]
  set c := stdAdelicCharacter (a * y)
  unfold adelicFourierFun at hne
  set I := ∫ x, T0 M Ψ x * stdAdelicCharacter (x * y) ∂tamagawaAdelic
  have hI : I = c * I := by
    have := integral_add_left_eq_self (μ := (tamagawaAdelic (F := F)))
      (fun x => T0 M Ψ x * stdAdelicCharacter (x * y)) a
    simp only [I]
    conv_lhs => rw [← this]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [T0_shift M Ψ z hz, add_mul, psi_add]
    ring
  have : (1 - c) * I = 0 := by rw [sub_mul, one_mul, ← hI, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · rw [← hay]; exact (sub_eq_zero.mp h).symm
  · exact absurd h hne

/-- a common denominator for the dual lattices -/
lemma etaN_den : ∃ D : ℕ, D ≠ 0 ∧ ∀ (M : ℕ), M ≠ 0 → ∀ n : Ix F → ℤ,
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (etaN M n) ∈ box (((M * D : ℕ) : F)⁻¹) := by
  classical
  choose Nj hNj hbox using fun j : Ix F => exists_den (algebraMap F (FiniteAdeleRing (𝓞 F) F) (bd F j))
  refine ⟨∏ j, Nj j, Finset.prod_ne_zero_iff.mpr fun j _ => hNj j, fun M hM n => ?_⟩
  have hD : (∏ j, Nj j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hNj j
  unfold etaN
  rw [map_sum]
  refine (boxSub (((M * ∏ j, Nj j : ℕ) : F)⁻¹)).sum_mem fun j _ => ?_
  have e1 : ((n j : ℚ) / M) • bd F j = ((M : F)⁻¹ * algebraMap (𝓞 F) F (n j : 𝓞 F)) * bd F j := by
    rw [Rat.smul_def, map_intCast]; push_cast; ring
  rw [e1, map_mul]
  have h1 := mul_mem_box (alg_mem_box ((M : F)⁻¹) (n j : 𝓞 F)) (hbox j)
  have e2 : (M : F)⁻¹ * (Nj j : F)⁻¹ = ((M * Nj j : ℕ) : F)⁻¹ := by
    push_cast; rw [mul_inv]
  rw [e2] at h1
  refine box_inv_mono _ _ ?_ (Nat.mul_ne_zero hM hD) h1
  exact Nat.mul_dvd_mul_left M (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))

/-- elements of `𝔸_f` whose character is trivial on `M Ô` lie in a fixed box -/
lemma ann_box (M : ℕ) (hM : M ≠ 0) : ∃ c' : F, c' ≠ 0 ∧ ∀ w : FiniteAdeleRing (𝓞 F) F,
    (∀ z ∈ box (M : F), stdAdelicCharacter (mkA 0 (z * w)) = 1) → w ∈ box c' := by
  obtain ⟨D, hD, hDb⟩ := etaN_den (F := F)
  have hMD : ((M * D : ℕ) : F) ≠ 0 := by exact_mod_cast Nat.mul_ne_zero hM hD
  refine ⟨((M * D : ℕ) : F)⁻¹, inv_ne_zero hMD, fun w hw => ?_⟩
  obtain ⟨ξ, hξ⟩ := exists_sub_int w
  set u := w - algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ
  have hu : u ∈ box (1 : F) := (mem_box_one u).mpr hξ
  have htr : ∀ i, ∃ k : ℤ, (M : ℚ) * Algebra.trace ℚ F (integralBasis F i * ξ) = k := by
    intro i
    set z := algebraMap F (FiniteAdeleRing (𝓞 F) F) ((M : F) * integralBasis F i)
    have hz : z ∈ box (M : F) := by
      simp only [z]; rw [integralBasis_apply]; exact alg_mem_box _ _
    have h1 := hw z hz
    have hw' : w = algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ + u := by simp [u]
    rw [hw', mul_add, show ∀ A B : FiniteAdeleRing (𝓞 F) F, mkA (0 : InfiniteAdeleRing F) (A + B) =
      mkA 0 A + mkA 0 B from fun A B => by rw [mkA_add, add_zero], psi_add] at h1
    have h2 : stdAdelicCharacter (mkA 0 (z * u)) = 1 := by
      apply psi_fin_int
      have := mul_mem_box hz hu
      rw [mul_one] at this
      exact box_nat_sub_one M this
    rw [h2, mul_one, ← map_mul, psi_fin_alg] at h1
    by_contra hne
    apply Ie_neg_alg_ne_one _ ?_ h1
    rintro ⟨k, hk⟩
    apply hne
    refine ⟨k, ?_⟩
    rw [← hk, mul_assoc, show ((M : F) * (integralBasis F i * ξ)) = M • (integralBasis F i * ξ) from
      (nsmul_eq_mul _ _).symm, map_nsmul, nsmul_eq_mul]
  obtain ⟨n, hn⟩ := exists_etaN M hM ξ htr
  have hw' : w = algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ + u := by simp [u]
  rw [hw']
  refine add_mem_box (hn ▸ hDb M hM n) ?_
  have := box_inv_mono (F := F) 1 (M * D) (one_dvd _) (Nat.mul_ne_zero hM hD)
  simp only [Nat.cast_one, inv_one] at this
  exact this hu

/-- the Fourier transform of `T₀` where the character is trivial on `M Ô` -/
lemma T0hat_eq (M : ℕ) (hM : M ≠ 0) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) (y : AdeleRing (𝓞 F) F)
    (hy : ∀ z ∈ box (M : F), stdAdelicCharacter (mkA 0 (z * y.2)) = 1) :
    adelicFourierFun (T0 M Ψ) y = ((M : ℝ) ^ Fintype.card (Ix F))⁻¹ • 𝓕 (⇑Ψ) (Bv y.1) := by
  have hM' : (M : F) ≠ 0 := by exact_mod_cast hM
  unfold adelicFourierFun
  have hind : (fun x => T0 M Ψ x * stdAdelicCharacter (x * y)) =
      {x : AdeleRing (𝓞 F) F | x.2 ∈ box (M : F)}.indicator (fun x =>
        Ψ (LH.symm x.1) * stdAdelicCharacter (x * y)) := by
    funext x
    by_cases hx : x.2 ∈ box (M : F)
    · rw [T0_of_mem M Ψ x hx, Set.indicator_of_mem (show x ∈ {x : AdeleRing (𝓞 F) F |
        x.2 ∈ box (M : F)} from hx)]
    · rw [T0_of_not_mem M Ψ x hx, Set.indicator_of_notMem (show x ∉ {x : AdeleRing (𝓞 F) F |
        x.2 ∈ box (M : F)} from hx), zero_mul]
  rw [hind, integral_indicator (measurableSet_boxA _ hM')]
  have h1 : ∫ x in {x : AdeleRing (𝓞 F) F | x.2 ∈ box (M : F)}, Ψ (LH.symm x.1) *
      stdAdelicCharacter (x * y) ∂tamagawaAdelic =
      ∫ x in {x : AdeleRing (𝓞 F) F | x.2 ∈ box (M : F)},
        (fun t => Ψ (LH.symm t) * Ie (t * y.1)) x.1 ∂tamagawaAdelic := by
    refine setIntegral_congr_fun (measurableSet_boxA _ hM') fun x hx => ?_
    rw [psi_split]
    have e1 : (x * y).1 = x.1 * y.1 := rfl
    have e2 : (x * y).2 = x.2 * y.2 := rfl
    rw [e1, e2, hy x.2 hx, mul_one]
  rw [h1, integral_box M hM (fun t => Ψ (LH.symm t) * Ie (t * y.1))
    ((Ψ.continuous.comp LH.symm.continuous).mul
    (continuous_Ie.comp (continuous_id.mul continuous_const))), Real.fourier_eq]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [Homeomorph.symm_apply_apply]
  rw [AuxP.fourierChar_smul, inner_Bv, AuxP.ex, Ie, mul_comm]
  congr 2
  push_cast; ring

/-- pointwise bound for the Fourier transform of `T₀` -/
lemma T0hat_bound (M : ℕ) (hM : M ≠ 0) : ∃ c' : F, c' ≠ 0 ∧ ∀ (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ))
    (y : AdeleRing (𝓞 F) F), ‖adelicFourierFun (T0 M Ψ) y‖ ≤
      (box c').indicator (fun _ => (1 : ℝ)) y.2 * ‖𝓕 (⇑Ψ) (Bv y.1)‖ := by
  obtain ⟨c', hc', hann⟩ := ann_box (F := F) M hM
  refine ⟨c', hc', fun Ψ y => ?_⟩
  by_cases hne : adelicFourierFun (T0 M Ψ) y = 0
  · rw [hne, norm_zero]
    by_cases hy : y.2 ∈ box c'
    · rw [Set.indicator_of_mem hy]; positivity
    · rw [Set.indicator_of_notMem hy, zero_mul]
  · have hy := T0hat_char M Ψ y hne
    have hyb : y.2 ∈ box c' := hann _ (fun z hz => hy z hz)
    rw [Set.indicator_of_mem hyb, one_mul, T0hat_eq M hM Ψ y hy, norm_smul]
    have h1 : ‖((M : ℝ) ^ Fintype.card (Ix F))⁻¹‖ ≤ 1 := by
      rw [norm_inv, norm_pow, Real.norm_natCast]
      have : (1 : ℝ) ≤ (M : ℝ) ^ Fintype.card (Ix F) :=
        one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM)
      exact inv_le_one_of_one_le₀ this
    calc _ ≤ 1 * ‖𝓕 (⇑Ψ) (Bv y.1)‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = _ := one_mul _

end T0hat


/-! ### stages: rapid decay of the span, neighbourhoods, Schwartz slices -/

section StageTop

open scoped SchwartzMap

variable {m n r s : ℕ} {d : Fin s → ℕ}

lemma rapid_zero : IsRapidDecay (0 : ElemGroup m n r s d → ℂ) := by
  refine ⟨fun a b => ?_, fun i j k => ⟨0, fun a b xt => ?_⟩⟩
  · exact contDiff_const (c := (0 : ℂ))
  · have : elemLift (0 : ElemGroup m n r s d → ℂ) a b = fun _ => 0 := rfl
    rw [this, iteratedFDeriv_zero_fun]; simp

lemma rapid_add (g₁ g₂ : ElemGroup m n r s d → ℂ) (h₁ : IsRapidDecay g₁) (h₂ : IsRapidDecay g₂) :
    IsRapidDecay (g₁ + g₂) := by
  refine ⟨fun a b => (h₁.1 a b).add (h₂.1 a b), fun i j k => ?_⟩
  obtain ⟨C₁, hC₁⟩ := h₁.2 i j k
  obtain ⟨C₂, hC₂⟩ := h₂.2 i j k
  refine ⟨C₁ + C₂, fun a b xt => ?_⟩
  have e : elemLift (g₁ + g₂) a b = elemLift g₁ a b + elemLift g₂ a b := rfl
  rw [e, iteratedFDeriv_add_apply ((h₁.1 a b).contDiffAt.of_le (by exact_mod_cast le_top))
    ((h₂.1 a b).contDiffAt.of_le (by exact_mod_cast le_top))]
  have h3 := norm_add_le (iteratedFDeriv ℝ k (elemLift g₁ a b) xt)
    (iteratedFDeriv ℝ k (elemLift g₂ a b) xt)
  have h4 : 0 ≤ ‖a‖ ^ j * ‖xt.1‖ ^ i := by positivity
  calc _ ≤ ‖a‖ ^ j * ‖xt.1‖ ^ i * (‖iteratedFDeriv ℝ k (elemLift g₁ a b) xt‖ +
        ‖iteratedFDeriv ℝ k (elemLift g₂ a b) xt‖) := mul_le_mul_of_nonneg_left h3 h4
    _ = _ := by ring
    _ ≤ C₁ + C₂ := add_le_add (hC₁ a b xt) (hC₂ a b xt)

lemma rapid_smul (c : ℂ) (g : ElemGroup m n r s d → ℂ) (h : IsRapidDecay g) :
    IsRapidDecay (c • g) := by
  refine ⟨fun a b => (h.1 a b).const_smul c, fun i j k => ?_⟩
  obtain ⟨C, hC⟩ := h.2 i j k
  refine ⟨‖c‖ * C, fun a b xt => ?_⟩
  have e : elemLift (c • g) a b = c • elemLift g a b := rfl
  rw [e, iteratedFDeriv_const_smul_apply ((h.1 a b).contDiffAt.of_le (by exact_mod_cast le_top)),
    norm_smul]
  have := hC a b xt
  calc _ = ‖c‖ * (‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift g a b) xt‖) := by ring
    _ ≤ ‖c‖ * C := mul_le_mul_of_nonneg_left this (norm_nonneg _)

lemma rapid_of_mem (g : ElemGroup m n r s d → ℂ) (hg : g ∈ elemSchwartzSubmodule m n r s d) :
    IsRapidDecay g := by
  induction hg using Submodule.span_induction with
  | mem h hh => exact hh
  | zero => exact rapid_zero
  | add a b _ _ ha hb => exact rapid_add a b ha hb
  | smul c a _ ha => exact rapid_smul c a ha

lemma elem_rapid (g : ElemSchwartz m n r s d) : IsRapidDecay g.toFun := rapid_of_mem g.1 g.2

lemma elem_toFun_sub (g g₀ : ElemSchwartz m n r s d) : (g - g₀).toFun = g.toFun - g₀.toFun := rfl

lemma elem_nhds_D (g₀ : ElemSchwartz m n r s d) (i j k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ g in 𝓝 g₀, ∀ a b xt, ‖a‖ ^ j * ‖xt.1‖ ^ i *
      ‖iteratedFDeriv ℝ k (elemLift (g - g₀).toFun a b) xt‖ < δ := by
  have h1 : Continuous (fun (g : ElemSchwartz m n r s d) (p : ℕ × ℕ × ℕ) =>
      UniformFun.ofFun
        (fun q : (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
          (‖q.1‖ ^ p.2.1 * ‖q.2.2.1‖ ^ p.1) •
            iteratedFDeriv ℝ p.2.2 (elemLift g.toFun q.1 q.2.1) q.2.2)) :=
    continuous_induced_dom
  have h2 := ((continuous_apply ((i, j, k) : ℕ × ℕ × ℕ)).comp h1).tendsto g₀
  rw [UniformFun.tendsto_iff_tendstoUniformly] at h2
  have h4 := Metric.tendstoUniformly_iff.1 h2 δ hδ
  filter_upwards [h4] with g hg
  intro a b xt
  have h5 := hg (a, b, xt)
  simp only [Function.comp_apply, UniformFun.toFun_ofFun] at h5
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)] at h5
  have hc : ∀ g' : ElemSchwartz m n r s d, ContDiffAt ℝ k (elemLift g'.toFun a b) xt :=
    fun g' => ((elem_rapid g').1 a b).contDiffAt.of_le (by exact_mod_cast le_top)
  have e : elemLift (g - g₀).toFun a b = elemLift g.toFun a b - elemLift g₀.toFun a b := rfl
  rw [e, iteratedFDeriv_sub_apply (hc g) (hc g₀), norm_sub_rev]
  exact h5

/-- the Schwartz slice `t ↦ u(L t, 0, ρ, σ)` -/
noncomputable def schwE (L : EuclideanSpace ℝ (Ix F) →L[ℝ] (Fin m → ℝ)) (K : ℝ)
    (ρ : Fin r → ℤ) (σ : (i : Fin s) → ZMod (d i)) (hK : ∀ t, ‖t‖ ≤ K * ‖L t‖)
    (u : ElemSchwartz m n r s d) : 𝓢(EuclideanSpace ℝ (Ix F), ℂ) where
  toFun := elemLift u.toFun ρ σ ∘ (L.prod (0 : EuclideanSpace ℝ (Ix F) →L[ℝ] (Fin n → ℝ)))
  smooth' := ((elem_rapid u).1 ρ σ).comp
    (L.prod (0 : EuclideanSpace ℝ (Ix F) →L[ℝ] (Fin n → ℝ))).contDiff
  decay' := by
    intro k' n'
    let Lx : EuclideanSpace ℝ (Ix F) →L[ℝ] (Fin m → ℝ) × (Fin n → ℝ) := L.prod 0
    have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (elemLift u.toFun ρ σ) := (elem_rapid u).1 ρ σ
    set K' := max K 0
    have hK' : ∀ t, ‖t‖ ≤ K' * ‖L t‖ := fun t =>
      (hK t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    obtain ⟨C, hC⟩ := (elem_rapid u).2 k' 0 n'
    refine ⟨K' ^ k' * ‖Lx‖ ^ n' * C, fun t => ?_⟩
    rw [Lx.iteratedFDeriv_comp_right hG t (by exact_mod_cast le_top)]
    have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ n' (elemLift u.toFun ρ σ) (Lx t)) (fun _ : Fin n' => Lx)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := hC ρ σ (Lx t)
    simp only [pow_zero, one_mul] at h2
    have hLx : (Lx t).1 = L t := rfl
    rw [hLx] at h2
    have h3 : ‖t‖ ^ k' ≤ (K' * ‖L t‖) ^ k' := pow_le_pow_left₀ (norm_nonneg _) (hK' t) k'
    have hK0 : 0 ≤ K' := le_max_right _ _
    calc ‖t‖ ^ k' * ‖(iteratedFDeriv ℝ n' (elemLift u.toFun ρ σ) (Lx t)).compContinuousLinearMap
          fun _ => Lx‖
        ≤ (K' * ‖L t‖) ^ k' * (‖iteratedFDeriv ℝ n' (elemLift u.toFun ρ σ) (Lx t)‖ * ‖Lx‖ ^ n') :=
          mul_le_mul h3 h1 (norm_nonneg _) (by positivity)
      _ = K' ^ k' * ‖Lx‖ ^ n' * (‖L t‖ ^ k' * ‖iteratedFDeriv ℝ n' (elemLift u.toFun ρ σ) (Lx t)‖) := by
          ring
      _ ≤ K' ^ k' * ‖Lx‖ ^ n' * C := mul_le_mul_of_nonneg_left h2 (by positivity)

lemma schwE_apply (L : EuclideanSpace ℝ (Ix F) →L[ℝ] (Fin m → ℝ)) (K : ℝ)
    (ρ : Fin r → ℤ) (σ : (i : Fin s) → ZMod (d i)) (hK : ∀ t, ‖t‖ ≤ K * ‖L t‖)
    (u : ElemSchwartz m n r s d) (t : EuclideanSpace ℝ (Ix F)) :
    schwE L K ρ σ hK u t = elemLift u.toFun ρ σ (L t, 0) := rfl

lemma schwE_sub (L : EuclideanSpace ℝ (Ix F) →L[ℝ] (Fin m → ℝ)) (K : ℝ)
    (ρ : Fin r → ℤ) (σ : (i : Fin s) → ZMod (d i)) (hK : ∀ t, ‖t‖ ≤ K * ‖L t‖)
    (u u₀ : ElemSchwartz m n r s d) :
    schwE L K ρ σ hK (u - u₀) = schwE L K ρ σ hK u - schwE L K ρ σ hK u₀ := by
  ext t; rfl

lemma schwE_cont (L : EuclideanSpace ℝ (Ix F) →L[ℝ] (Fin m → ℝ)) (K : ℝ)
    (ρ : Fin r → ℤ) (σ : (i : Fin s) → ZMod (d i)) (hK : ∀ t, ‖t‖ ≤ K * ‖L t‖) :
    Continuous (schwE (n := n) L K ρ σ hK) := by
  rw [continuous_iff_continuousAt]
  intro u₀
  refine ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ (Ix F)) ℂ).tendsto_nhds _ _).2 ?_
  rintro ⟨k', n'⟩ ε hε
  let Lx : EuclideanSpace ℝ (Ix F) →L[ℝ] (Fin m → ℝ) × (Fin n → ℝ) := L.prod 0
  set K' := max K 0
  have hK' : ∀ t, ‖t‖ ≤ K' * ‖L t‖ := fun t =>
    (hK t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  set Q : ℝ := K' ^ k' * ‖Lx‖ ^ n' + 1
  have hQ : 0 < Q := by positivity
  set δ : ℝ := ε / (2 * Q)
  have hδ : 0 < δ := by positivity
  filter_upwards [elem_nhds_D u₀ k' 0 n' δ hδ] with u hu
  rw [← schwE_sub]
  set w := u - u₀
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (elemLift w.toFun ρ σ) := (elem_rapid w).1 ρ σ
  have hb : ∀ t, ‖t‖ ^ k' * ‖iteratedFDeriv ℝ n' (schwE L K ρ σ hK w) t‖ ≤ K' ^ k' * ‖Lx‖ ^ n' * δ := by
    intro t
    change ‖t‖ ^ k' * ‖iteratedFDeriv ℝ n' (elemLift w.toFun ρ σ ∘ Lx) t‖ ≤ _
    rw [Lx.iteratedFDeriv_comp_right hG t (by exact_mod_cast le_top)]
    have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ n' (elemLift w.toFun ρ σ) (Lx t)) (fun _ : Fin n' => Lx)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := (hu ρ σ (Lx t)).le
    simp only [pow_zero, one_mul] at h2
    have hLx : (Lx t).1 = L t := rfl
    rw [hLx] at h2
    have h3 : ‖t‖ ^ k' ≤ (K' * ‖L t‖) ^ k' := pow_le_pow_left₀ (norm_nonneg _) (hK' t) k'
    calc ‖t‖ ^ k' * ‖(iteratedFDeriv ℝ n' (elemLift w.toFun ρ σ) (Lx t)).compContinuousLinearMap
          fun _ => Lx‖
        ≤ (K' * ‖L t‖) ^ k' * (‖iteratedFDeriv ℝ n' (elemLift w.toFun ρ σ) (Lx t)‖ * ‖Lx‖ ^ n') :=
          mul_le_mul h3 h1 (norm_nonneg _) (by positivity)
      _ = K' ^ k' * ‖Lx‖ ^ n' * (‖L t‖ ^ k' * ‖iteratedFDeriv ℝ n' (elemLift w.toFun ρ σ) (Lx t)‖) := by
          ring
      _ ≤ K' ^ k' * ‖Lx‖ ^ n' * δ := mul_le_mul_of_nonneg_left h2 (by positivity)
  have h5 := SchwartzMap.seminorm_le_bound ℂ k' n' (schwE L K ρ σ hK w) (by positivity) hb
  change SchwartzMap.seminorm ℂ k' n' _ < ε
  have h6 : K' ^ k' * ‖Lx‖ ^ n' * δ ≤ Q * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
  have h7 : Q * δ = ε / 2 := by simp only [δ]; field_simp
  linarith

end StageTop


/-! ### the stage decomposition with explicit, continuous Schwartz slices -/

section StageDec

open Multiplicative
open scoped SchwartzMap

variable {Γ k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))} {m n r s : ℕ} {d : Fin s → ℕ}

set_option maxHeartbeats 1600000 in
lemma stage_dec (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) :
    ∃ (M1 : ℕ), M1 ≠ 0 ∧ ∃ (c : F), c ≠ 0 ∧
    ∃ (Q : Finset (FiniteAdeleRing (𝓞 F) F ⧸ boxSub (M1 : F)))
      (Ψa : FiniteAdeleRing (𝓞 F) F → ElemSchwartz m n r s d → 𝓢(EuclideanSpace ℝ (Ix F), ℂ)),
      (∀ q ∈ Q, ∀ z, z - q.out ∈ box (M1 : F) → z ∈ box c) ∧
      (∀ a, Continuous (Ψa a)) ∧
      (∀ a u u₀, Ψa a (u - u₀) = Ψa a u - Ψa a u₀) ∧
      (∀ u : ElemSchwartz m n r s d,
        (fun x : AdeleRing (𝓞 F) F => extendPullback Γ π u.toFun (ofAdd x)) =
          ∑ q ∈ Q, Tt M1 (Ψa q.out u) q.out) := by
  classical
  obtain ⟨hΓo, hgen, hk, -⟩ := hs
  obtain ⟨hd, hπc, hπo, -, hπk⟩ := hπ
  obtain ⟨M0, hM0, hmem⟩ := Gamma_contains hΓo
  obtain ⟨Nb, hNb, hbdd⟩ := Gamma_bdd hgen
  obtain ⟨M1', hM1', hnss'⟩ := nss_step π hπc hd hΓo
  obtain ⟨M1, hM1def⟩ : ∃ M1 : ℕ, M1 = M0 * M1' := ⟨_, rfl⟩
  have hM1 : M1 ≠ 0 := by rw [hM1def]; exact Nat.mul_ne_zero hM0 hM1'
  have hb1 : box (M1 : F) ⊆ box (M1' : F) := by
    have := box_natMul_sub (M1' : F) M0
    rwa [hM1def, Nat.cast_mul, mul_comm (M0 : F)]
  have hb0 : box (M1 : F) ⊆ box (M0 : F) := by
    have := box_natMul_sub (M0 : F) M1'
    rwa [hM1def, Nat.cast_mul]
  have hnss : ∀ z (hz : ofAdd (mkA 0 z) ∈ Γ), z ∈ box (M1 : F) → π ⟨ofAdd (mkA 0 z), hz⟩ = 1 :=
    fun z hz hzb => hnss' z hz (hb1 hzb)
  have hko : IsOpen (annihilator k) := hk.2.1
  obtain ⟨L, K, hK, hempty, hLA⟩ := arch_step (Γ := Γ) (k := k) π hπc hπo hπk hko M0 hmem M1 hM1 hnss
  let Γf : Set (FiniteAdeleRing (𝓞 F) F) := {z | ofAdd (mkA 0 z) ∈ Γ}
  have hj0c : Continuous (fun z : FiniteAdeleRing (𝓞 F) F => ofAdd (mkA (0 : InfiniteAdeleRing F) z)) :=
    continuous_ofAdd.comp (continuous_mkA.comp (continuous_const.prodMk continuous_id))
  have hΓc : IsClosed (Γ : Set (Multiplicative (AdeleRing (𝓞 F) F))) :=
    Subgroup.isClosed_of_isOpen Γ hΓo
  have hΓfsub : Γf ⊆ box ((Nb : F)⁻¹) := fun z hz => hbdd (ofAdd (mkA 0 z)) hz
  have hNb' : (Nb : F) ≠ 0 := by exact_mod_cast hNb
  have hΓfK : IsCompact Γf :=
    (isCompact_box _ (inv_ne_zero hNb')).of_isClosed_subset (hΓc.preimage hj0c) hΓfsub
  have hΓfs : ∀ z ∈ Γf, ∀ w ∈ box (M1 : F), z + w ∈ Γf := by
    intro z hz w hw
    change ofAdd (mkA 0 (z + w)) ∈ Γ
    rw [show (mkA (0 : InfiniteAdeleRing F) (z + w)) = mkA (0 + 0) (z + w) by rw [add_zero],
      ofAdd_mkA_add]
    exact Γ.mul_mem hz (hmem _ (hb0 hw))
  obtain ⟨Q, hQK, hQ⟩ := coset_decomp M1 hM1 Γf hΓfK hΓfs
  let e : FiniteAdeleRing (𝓞 F) F → ElemGroup m n r s d := fun a =>
    if h : ofAdd (mkA 0 a) ∈ Γ then toAdd (π ⟨ofAdd (mkA 0 a), h⟩) else 0
  let Ψa : FiniteAdeleRing (𝓞 F) F → ElemSchwartz m n r s d → 𝓢(EuclideanSpace ℝ (Ix F), ℂ) :=
    fun a => schwE L K (e a).2.2.1 (e a).2.2.2 hK
  have hΦ : ∀ q ∈ Q, ∀ (u : ElemSchwartz m n r s d) (x : AdeleRing (𝓞 F) F)
      (hx : ofAdd x ∈ Γ), x.2 - q.out ∈ box (M1 : F) →
        u.toFun (toAdd (π ⟨ofAdd x, hx⟩)) = Ψa q.out u (LH.symm x.1) := by
    intro q hq u x hx hxq
    have hqΓ : ofAdd (mkA 0 q.out) ∈ Γ := hQK q hq
    have heq : e q.out = toAdd (π ⟨ofAdd (mkA 0 q.out), hqΓ⟩) := dif_pos hqΓ
    set e0 := toAdd (π ⟨ofAdd (mkA 0 q.out), hqΓ⟩)
    have he1 : e0.1 = 0 := by
      set N' := Nb * M1
      have hN' : N' ≠ 0 := Nat.mul_ne_zero hNb hM1
      have hmemN : N' • q.out ∈ box (M1 : F) := by
        have := mul_mem_box (alg_mem_box_self (N' : F)) (hΓfsub hqΓ)
        have hc : (N' : F) * (Nb : F)⁻¹ = M1 := by
          simp only [N', Nat.cast_mul]; field_simp
        rw [hc] at this
        rwa [nsmul_eq_mul, show ((N' : FiniteAdeleRing (𝓞 F) F)) =
          algebraMap F (FiniteAdeleRing (𝓞 F) F) (N' : F) by simp]
      have hmemΓ : ofAdd (mkA 0 (N' • q.out)) ∈ Γ := hmem _ (hb0 hmemN)
      have h1 := hnss _ hmemΓ hmemN
      have h2 : (⟨ofAdd (mkA 0 (N' • q.out)), hmemΓ⟩ : Γ) = (⟨_, hqΓ⟩ : Γ) ^ N' := by
        apply Subtype.ext
        change ofAdd (mkA 0 (N' • q.out)) = (ofAdd (mkA 0 q.out)) ^ N'
        rw [← ofAdd_nsmul]
        congr 1
        change mkA 0 (N' • q.out) = mkA (N' • 0) (N' • q.out)
        rw [smul_zero]
      rw [h2, map_pow] at h1
      have h3 : N' • e0 = 0 := by
        simp only [e0]; rw [← toAdd_pow, h1, toAdd_one]
      have h4 : N' • e0.1 = 0 := by
        have := congrArg Prod.fst h3; simpa using this
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_eq_zero] at h4
      rcases h4 with h4 | h4
      · exact absurd (by exact_mod_cast h4) hN'
      · exact h4
    set t := LH.symm x.1
    have hjI : ofAdd (mkA (LH t) 0) ∈ Γ := hmem _ (zero_mem_box _)
    have hdq : ofAdd (mkA 0 (x.2 - q.out)) ∈ Γ := hmem _ (hb0 hxq)
    have hsplit : (⟨ofAdd x, hx⟩ : Γ) = (⟨_, hjI⟩ * ⟨_, hqΓ⟩) * ⟨_, hdq⟩ := by
      apply Subtype.ext
      change ofAdd x = ofAdd (mkA (LH t) 0) * ofAdd (mkA 0 q.out) * ofAdd (mkA 0 (x.2 - q.out))
      rw [← ofAdd_add, ← ofAdd_add, mkA_add, mkA_add, add_zero, add_zero, zero_add,
        add_sub_cancel, Homeomorph.apply_symm_apply, mkA_eta]
    have hΨ : Ψa q.out u t = elemLift u.toFun e0.2.2.1 e0.2.2.2 (L t, 0) := by
      simp only [Ψa, heq]; rfl
    rw [hsplit, map_mul π, map_mul π, hnss _ hdq hxq, mul_one, toAdd_mul, hΨ]
    obtain ⟨hA1, hA2⟩ := hLA t hjI
    haveI := hempty
    simp only [elemLift]
    congr 1
    refine Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) ?_)
    · change (toAdd (π ⟨_, hjI⟩)).1 + e0.1 = L t
      rw [hA1, he1, add_zero]
    · change (toAdd (π ⟨_, hjI⟩)).2.2 + e0.2.2 = (e0.2.2.1, e0.2.2.2)
      rw [hA2, zero_add]
  have hdec : ∀ x : AdeleRing (𝓞 F) F, ofAdd x = ofAdd (mkA x.1 0) * ofAdd (mkA 0 x.2) := by
    intro x
    rw [← ofAdd_add, mkA_add, add_zero, zero_add, mkA_eta]
  refine ⟨M1, hM1, (Nb : F)⁻¹, inv_ne_zero hNb', Q, Ψa, ?_, fun a => schwE_cont _ _ _ _ _,
    fun a u u₀ => schwE_sub _ _ _ _ _ _ _, fun u => ?_⟩
  · intro q hq z hz
    have := hΓfs _ (hQK q hq) _ hz
    rw [add_sub_cancel] at this
    exact hΓfsub this
  funext x
  rw [Finset.sum_apply]
  simp only [Tt, T0]
  have e3 : ∀ r, (x - mkA 0 r).2 = x.2 - r := fun r => rfl
  have e4 : ∀ r, (x - mkA 0 r).1 = x.1 := fun r => by change x.1 - 0 = x.1; rw [sub_zero]
  simp only [e3, e4]
  unfold extendPullback
  by_cases hx : ofAdd x ∈ Γ
  · rw [dif_pos hx]
    have hterm : ∀ q ∈ Q, (box (M1 : F)).indicator (fun _ => (1 : ℂ)) (x.2 - q.out) *
        Ψa q.out u (LH.symm x.1) = (box (M1 : F)).indicator (fun _ => (1 : ℂ)) (x.2 - q.out) *
          u.toFun (toAdd (π ⟨ofAdd x, hx⟩)) := by
      intro q hq
      by_cases hm : x.2 - q.out ∈ box (M1 : F)
      · rw [hΦ q hq u x hx hm]
      · simp [Set.indicator_of_notMem hm]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← hQ]
    have hxf : x.2 ∈ Γf := by
      change ofAdd (mkA 0 x.2) ∈ Γ
      have : ofAdd (mkA 0 x.2) = (ofAdd (mkA x.1 0))⁻¹ * ofAdd x := by
        rw [hdec x, inv_mul_cancel_left]
      rw [this]
      exact Γ.mul_mem (Γ.inv_mem (hmem _ (zero_mem_box _))) hx
    rw [Set.indicator_of_mem hxf, one_mul]
  · rw [dif_neg hx]
    symm
    refine Finset.sum_eq_zero fun q hq => ?_
    have hm : x.2 - q.out ∉ box (M1 : F) := by
      intro hm
      apply hx
      have h1 : x.2 ∈ Γf := by
        have := hΓfs _ (hQK q hq) _ hm
        rwa [add_sub_cancel] at this
      rw [hdec x]
      exact Γ.mul_mem (hmem _ (zero_mem_box _)) h1
    simp [Set.indicator_of_notMem hm]

end StageDec


/-! ### bounded sets and families of linear functionals -/

section BddFam

universe uE

lemma cont_of_seminorm {X : Type*} [TopologicalSpace X] {E : Type uE} [AddCommGroup E]
    [Module ℂ E] (p : Seminorm ℂ E) (φ : X → E)
    (hφ : ∀ (x₀ : X) (ε : ℝ), 0 < ε → ∀ᶠ x in 𝓝 x₀, p (φ x - φ x₀) < ε) :
    @Continuous X E _ (SeminormFamily.moduleFilterBasis (fun _ : PUnit.{uE + 1} => p)).topology
      φ := by
  letI : TopologicalSpace E :=
    (SeminormFamily.moduleFilterBasis (fun _ : PUnit.{uE + 1} => p)).topology
  have hws : WithSeminorms (fun _ : PUnit.{uE + 1} => p) := ⟨rfl⟩
  rw [continuous_iff_continuousAt]
  intro x₀
  exact (hws.tendsto_nhds φ (φ x₀)).2 fun _ ε hε => hφ x₀ ε hε

lemma bdd_of_seminorm {E : Type uE} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E) (B : Set E)
    (hB : @Bornology.IsVonNBounded ℂ E _ _ _
      (SeminormFamily.moduleFilterBasis (fun _ : PUnit.{uE + 1} => p)).topology B) :
    ∃ r : ℝ, ∀ f ∈ B, p f < r := by
  letI : TopologicalSpace E :=
    (SeminormFamily.moduleFilterBasis (fun _ : PUnit.{uE + 1} => p)).topology
  have hws : WithSeminorms (fun _ : PUnit.{uE + 1} => p) := ⟨rfl⟩
  obtain ⟨r, -, hr⟩ := (hws.isVonNBounded_iff_seminorm_bounded).1 hB PUnit.unit
  exact ⟨r, hr⟩

lemma lc_of_seminorm {E : Type uE} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E) :
    IsLocallyConvexTopology E
      (SeminormFamily.moduleFilterBasis (fun _ : PUnit.{uE + 1} => p)).topology := by
  letI : TopologicalSpace E :=
    (SeminormFamily.moduleFilterBasis (fun _ : PUnit.{uE + 1} => p)).topology
  exact ⟨PUnit.{uE + 1}, inferInstance, fun _ => p, ⟨rfl⟩⟩

lemma ofElem_sub' {Γ k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))} {m n r s : ℕ}
    {d : Fin s → ℕ} (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) (g g₀ : ElemSchwartz m n r s d) :
    SchwartzBruhat.ofElem Γ k π hs hπ g - SchwartzBruhat.ofElem Γ k π hs hπ g₀ =
      SchwartzBruhat.ofElem Γ k π hs hπ (g - g₀) := by
  apply Subtype.ext
  funext x
  show extendPullback Γ π g.toFun x - extendPullback Γ π g₀.toFun x =
    extendPullback Γ π (g - g₀).toFun x
  unfold extendPullback
  by_cases hx : x ∈ Γ
  · rw [dif_pos hx, dif_pos hx, dif_pos hx]; rfl
  · rw [dif_neg hx, dif_neg hx, dif_neg hx, sub_zero]

/-- a family of linear functionals, pointwise bounded and uniformly small on every stage, is
bounded on every bounded set -/
lemma bdd_family {H : Type*} (ℓ : H → AdelicSchwartz F → ℂ)
    (hadd : ∀ h f g, ℓ h (f + g) = ℓ h f + ℓ h g) (hsmul : ∀ h (c : ℂ) f, ℓ h (c • f) = c * ℓ h f)
    (hfin : ∀ f, ∃ C, ∀ h, ‖ℓ h f‖ ≤ C)
    (hst : ∀ (Γ k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))) (m n r s : ℕ) (d : Fin s → ℕ)
      (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
      (hπ : IsElemPresentation Γ k π) (g₀ : ElemSchwartz m n r s d) (ε : ℝ), 0 < ε →
      ∀ᶠ g in 𝓝 g₀, ∀ h, ‖ℓ h (SchwartzBruhat.ofElem Γ k π hs hπ (g - g₀))‖ ≤ ε)
    (B : Set (AdelicSchwartz F)) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ C, ∀ f ∈ B, ∀ h, ‖ℓ h f‖ ≤ C := by
  have hbdd : ∀ f, BddAbove (Set.range fun h => ‖ℓ h f‖) := by
    intro f
    obtain ⟨C, hC⟩ := hfin f
    exact ⟨C, by rintro _ ⟨h, rfl⟩; exact hC h⟩
  have hnn : ∀ f, 0 ≤ ⨆ h, ‖ℓ h f‖ := fun f => Real.iSup_nonneg fun h => norm_nonneg _
  let p : Seminorm ℂ (AdelicSchwartz F) := Seminorm.of (fun f => ⨆ h, ‖ℓ h f‖)
    (by
      intro f g
      refine Real.iSup_le (fun h => ?_) (add_nonneg (hnn f) (hnn g))
      rw [hadd]
      exact (norm_add_le _ _).trans (add_le_add (le_ciSup (hbdd f) h) (le_ciSup (hbdd g) h)))
    (by
      intro c f
      rw [Real.mul_iSup_of_nonneg (norm_nonneg c)]
      congr 1
      funext h
      rw [hsmul, norm_mul])
  have hle : ∀ f h, ‖ℓ h f‖ ≤ p f := fun f h => le_ciSup (hbdd f) h
  let t := (SeminormFamily.moduleFilterBasis (fun _ : PUnit => p)).topology
  have hmem : t ∈ {t | IsLocallyConvexTopology (AdelicSchwartz F) t ∧
      ∀ (Γ k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))) (m n r s : ℕ) (d : Fin s → ℕ)
        (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
        (hπ : IsElemPresentation Γ k π),
        @Continuous (ElemSchwartz m n r s d) (SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)))
          _ t (SchwartzBruhat.ofElem Γ k π hs hπ)} := by
    refine ⟨lc_of_seminorm _, fun Γ k m n r s d π hs hπ => ?_⟩
    apply cont_of_seminorm
    intro g₀ ε hε
    filter_upwards [hst Γ k m n r s d π hs hπ g₀ (ε / 2) (by positivity)] with g hg
    rw [ofElem_sub']
    have : p (SchwartzBruhat.ofElem Γ k π hs hπ (g - g₀)) ≤ ε / 2 :=
      Real.iSup_le hg (by positivity)
    linarith
  have hle' : instTopologicalSpaceSchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)) ≤ t :=
    sInf_le hmem
  have hB' := Bornology.IsVonNBounded.of_topologicalSpace_le (𝕜 := ℂ) hle' hB
  obtain ⟨M, hM⟩ := bdd_of_seminorm p B hB'
  exact ⟨M, fun f hf h => (hle f h).trans (hM f hf).le⟩

end BddFam


/-! ### pointwise majorants and theta bounds for the basic functions -/

section Majorants

open MeasureTheory
open scoped SchwartzMap FourierTransform

lemma one_add_pow_le' (u : ℝ) (hu : 0 ≤ u) (N : ℕ) : (1 + u) ^ N ≤ 2 ^ N * (1 + u ^ N) := by
  rcases le_total u 1 with h | h
  · calc (1 + u) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ ≤ 2 ^ N * (1 + u ^ N) :=
          le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg hu N])
  · calc (1 + u) ^ N ≤ (2 * u) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ = 2 ^ N * u ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + u ^ N) := by
          have : (0 : ℝ) < 2 ^ N := by positivity
          nlinarith

lemma rpow_neg_nat (x : ℝ) (hx : 0 ≤ x) (K : ℕ) : x ^ (-(K : ℝ)) = (x ^ K)⁻¹ := by
  rw [Real.rpow_neg hx, Real.rpow_natCast]

/-- a pair of Schwartz seminorms -/
noncomputable def SK (K : ℕ) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) : ℝ :=
  SchwartzMap.seminorm ℂ 0 0 Ψ + SchwartzMap.seminorm ℂ K 0 Ψ

lemma SK_nonneg (K : ℕ) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) : 0 ≤ SK K Ψ := by
  unfold SK; positivity

lemma SK_zero (K : ℕ) : SK (F := F) K 0 = 0 := by simp [SK]

lemma SK_cont (K : ℕ) : Continuous (SK (F := F) K) := by
  have h1 := (schwartz_withSeminorms ℂ (EuclideanSpace ℝ (Ix F)) ℂ).continuous_seminorm (0, 0)
  have h2 := (schwartz_withSeminorms ℂ (EuclideanSpace ℝ (Ix F)) ℂ).continuous_seminorm (K, 0)
  exact h1.add h2

lemma schwartz_decay_K (K : ℕ) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) (t : EuclideanSpace ℝ (Ix F)) :
    ‖Ψ t‖ ≤ 2 ^ K * SK K Ψ * (1 + ‖t‖) ^ (-(K : ℝ)) := by
  have h1 := SchwartzMap.norm_le_seminorm ℂ Ψ t
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℂ Ψ K t
  have h3 := one_add_pow_le' ‖t‖ (norm_nonneg _) K
  have hp : 0 < (1 + ‖t‖) ^ K := by positivity
  have h4 : (1 + ‖t‖) ^ K * ‖Ψ t‖ ≤ 2 ^ K * SK K Ψ := by
    calc (1 + ‖t‖) ^ K * ‖Ψ t‖ ≤ 2 ^ K * (1 + ‖t‖ ^ K) * ‖Ψ t‖ :=
          mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ = 2 ^ K * (‖Ψ t‖ + ‖t‖ ^ K * ‖Ψ t‖) := by ring
      _ ≤ 2 ^ K * SK K Ψ := by unfold SK; gcongr
  rw [rpow_neg_nat _ (by positivity)]
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  linarith

lemma Wt_anti (c : F) {k k' : ℝ} (hkk : k ≤ k') (x : AdeleRing (𝓞 F) F) :
    Wt c k' x ≤ Wt c k x := by
  unfold Wt
  refine mul_le_mul_of_nonneg_left ?_ (by
    by_cases hx : x.2 ∈ box c
    · rw [Set.indicator_of_mem hx]; norm_num
    · rw [Set.indicator_of_notMem hx])
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg (LH.symm x.1)]) (by linarith)

lemma Tt_le (M : ℕ) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) (a : FiniteAdeleRing (𝓞 F) F) (c : F)
    (hbox : ∀ z, z - a ∈ box (M : F) → z ∈ box c) (K : ℕ) (x : AdeleRing (𝓞 F) F) :
    ‖Tt M Ψ a x‖ ≤ 2 ^ K * SK K Ψ * Wt c K x := by
  have e1 : (x - mkA 0 a).2 = x.2 - a := rfl
  have e2 : (x - mkA 0 a).1 = x.1 := by change x.1 - 0 = x.1; rw [sub_zero]
  unfold Tt
  by_cases hx : x.2 - a ∈ box (M : F)
  · rw [T0_of_mem M Ψ _ (by rw [e1]; exact hx), e2]
    unfold Wt
    rw [Set.indicator_of_mem (hbox _ hx), one_mul]
    exact schwartz_decay_K K Ψ _
  · rw [T0_of_not_mem M Ψ _ (by rw [e1]; exact hx), norm_zero]
    have := Wt_nonneg c K x
    have := SK_nonneg K Ψ
    positivity

/-- theta series of a function dominated by the weight -/
lemma maj_theta (φ : AdeleRing (𝓞 F) F → ℂ) (A : ℝ) (c : F) (k : ℝ)
    (hφ : ∀ x, ‖φ x‖ ≤ A * Wt c k x) (h : IdeleGroup F)
    (hs : Summable (fun ξ : Fˣ => Wt c k (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) *
      (h : AdeleRing (𝓞 F) F)))) :
    ‖adelicThetaFun φ h‖ ≤ A * ∑' ξ : Fˣ, Wt c k (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) *
      (h : AdeleRing (𝓞 F) F)) := by
  have hsn : Summable (fun ξ : Fˣ => ‖φ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) *
      (h : AdeleRing (𝓞 F) F))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hφ _) (hs.mul_left A)
  unfold adelicThetaFun
  refine (norm_tsum_le_tsum_norm hsn).trans ?_
  rw [← tsum_mul_left]
  exact hsn.tsum_le_tsum (fun ξ => hφ _) (hs.mul_left A)

lemma Tt_mem (M : ℕ) (hM : M ≠ 0) (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ))
    (a : FiniteAdeleRing (𝓞 F) F) : Tt M Ψ a ∈ Tsp (F := F) :=
  Submodule.subset_span ⟨M, hM, Ψ, a, rfl⟩

lemma fourier_Tt_le (M : ℕ) (hM : M ≠ 0) : ∃ c' : F, c' ≠ 0 ∧ ∃ Kb : ℝ, 1 ≤ Kb ∧
    ∀ (Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) (a : FiniteAdeleRing (𝓞 F) F) (K : ℕ)
      (y : AdeleRing (𝓞 F) F),
      ‖adelicFourierFun (Tt M Ψ a) y‖ ≤ 2 ^ K * Kb ^ K * SK K (𝓕 Ψ) * Wt c' K y := by
  obtain ⟨c', hc', hT⟩ := T0hat_bound (F := F) M hM
  obtain ⟨Kb0, hKb0, hanti⟩ := Bv_anti (F := F)
  refine ⟨c', hc', Kb0 + 1, by linarith, fun Ψ a K y => ?_⟩
  have e0 : Tt M Ψ a = fun x => T0 M Ψ (x - mkA 0 a) := rfl
  rw [e0, fourier_translate, norm_mul, norm_psi, one_mul]
  refine (hT Ψ y).trans ?_
  have hF : 𝓕 (⇑Ψ) (Bv y.1) = (𝓕 Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) (Bv y.1) := rfl
  rw [hF]
  have h1 := schwartz_decay_K K (𝓕 Ψ) (Bv y.1)
  have h2 : (1 + ‖Bv y.1‖) ^ (-(K : ℝ)) ≤ (Kb0 + 1) ^ K * (1 + ‖LH.symm y.1‖) ^ (-(K : ℝ)) := by
    rw [rpow_neg_nat _ (by positivity), rpow_neg_nat _ (by positivity)]
    have h3 : 1 + ‖LH.symm y.1‖ ≤ (Kb0 + 1) * (1 + ‖Bv y.1‖) := by
      have := hanti y.1
      nlinarith [norm_nonneg (Bv y.1)]
    have h4 : (1 + ‖LH.symm y.1‖) ^ K ≤ (Kb0 + 1) ^ K * (1 + ‖Bv y.1‖) ^ K := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h3 K
    have hp1 : 0 < (1 + ‖LH.symm y.1‖) ^ K := by positivity
    have hp2 : 0 < (1 + ‖Bv y.1‖) ^ K := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hp1]
    calc ((1 + ‖Bv y.1‖) ^ K)⁻¹ * (1 + ‖LH.symm y.1‖) ^ K
        ≤ ((1 + ‖Bv y.1‖) ^ K)⁻¹ * ((Kb0 + 1) ^ K * (1 + ‖Bv y.1‖) ^ K) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = (Kb0 + 1) ^ K := by field_simp
  have hSK := SK_nonneg K (𝓕 Ψ)
  unfold Wt
  by_cases hy : y.2 ∈ box c'
  · rw [Set.indicator_of_mem hy, one_mul, one_mul]
    calc ‖(𝓕 Ψ : 𝓢(EuclideanSpace ℝ (Ix F), ℂ)) (Bv y.1)‖
        ≤ 2 ^ K * SK K (𝓕 Ψ) * (1 + ‖Bv y.1‖) ^ (-(K : ℝ)) := h1
      _ ≤ 2 ^ K * SK K (𝓕 Ψ) * ((Kb0 + 1) ^ K * (1 + ‖LH.symm y.1‖) ^ (-(K : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hy, zero_mul, zero_mul, mul_zero]

lemma fourier_sum {ι : Type*} (Q : Finset ι) (f : ι → AdeleRing (𝓞 F) F → ℂ)
    (hf : ∀ i, f i ∈ Tsp (F := F)) (y : AdeleRing (𝓞 F) F) :
    adelicFourierFun (∑ i ∈ Q, f i) y = ∑ i ∈ Q, adelicFourierFun (f i) y := by
  unfold adelicFourierFun
  simp only [Finset.sum_apply, Finset.sum_mul]
  rw [integral_finset_sum]
  intro i _
  exact (good_Tsp _ (hf i)).2.1 y

lemma theta_add (φ ψ : AdeleRing (𝓞 F) F → ℂ) (hφ : φ ∈ Tsp (F := F)) (hψ : ψ ∈ Tsp (F := F))
    (h : IdeleGroup F) : adelicThetaFun (φ + ψ) h = adelicThetaFun φ h + adelicThetaFun ψ h := by
  unfold adelicThetaFun
  simp only [Pi.add_apply]
  rw [(RR_fun φ hφ h).1.tsum_add (RR_fun ψ hψ h).1]

lemma theta_smul (c : ℂ) (φ : AdeleRing (𝓞 F) F → ℂ) (h : IdeleGroup F) :
    adelicThetaFun (c • φ) h = c * adelicThetaFun φ h := by
  unfold adelicThetaFun
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [tsum_mul_left]

lemma fourierFun_add (φ ψ : AdeleRing (𝓞 F) F → ℂ) (hφ : φ ∈ Tsp (F := F)) (hψ : ψ ∈ Tsp (F := F)) :
    adelicFourierFun (φ + ψ) = adelicFourierFun φ + adelicFourierFun ψ := by
  funext y
  unfold adelicFourierFun
  rw [Pi.add_apply, ← integral_add ((good_Tsp _ hφ).2.1 y) ((good_Tsp _ hψ).2.1 y)]
  congr 1; funext x; simp only [Pi.add_apply]; ring

lemma fourierFun_smul (c : ℂ) (φ : AdeleRing (𝓞 F) F → ℂ) :
    adelicFourierFun (c • φ) = c • adelicFourierFun φ := by
  funext y
  unfold adelicFourierFun
  rw [Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  congr 1; funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma summable_thetaF (φ : AdeleRing (𝓞 F) F → ℂ) (hφ : φ ∈ Tsp (F := F)) (h : IdeleGroup F) :
    Summable (fun ξ : Fˣ => adelicFourierFun φ
      (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (h : AdeleRing (𝓞 F) F))) := by
  have := (RR_fun φ hφ h⁻¹).2.1
  simpa only [inv_inv] using this

lemma thetaF_add (φ ψ : AdeleRing (𝓞 F) F → ℂ) (hφ : φ ∈ Tsp (F := F)) (hψ : ψ ∈ Tsp (F := F))
    (h : IdeleGroup F) : adelicThetaFun (adelicFourierFun (φ + ψ)) h =
      adelicThetaFun (adelicFourierFun φ) h + adelicThetaFun (adelicFourierFun ψ) h := by
  rw [fourierFun_add φ ψ hφ hψ]
  unfold adelicThetaFun
  simp only [Pi.add_apply]
  rw [(summable_thetaF φ hφ h).tsum_add (summable_thetaF ψ hψ h)]

lemma thetaF_smul (c : ℂ) (φ : AdeleRing (𝓞 F) F → ℂ) (h : IdeleGroup F) :
    adelicThetaFun (adelicFourierFun (c • φ)) h = c * adelicThetaFun (adelicFourierFun φ) h := by
  rw [fourierFun_smul]; exact theta_smul c _ h

end Majorants


/-! ### uniform bounds for theta series over bounded sets -/

section Uniform

open MeasureTheory Multiplicative
open scoped SchwartzMap FourierTransform

lemma box_cond_of_den (M : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (Na : ℕ) (hNa : Na ≠ 0)
    (ha : a ∈ box ((Na : F)⁻¹)) : ∀ z, z - a ∈ box (M : F) → z ∈ box ((Na : F)⁻¹) := by
  intro z hz
  have h1 : box (1 : F) ⊆ box ((Na : F)⁻¹) := by
    have := box_inv_mono (F := F) 1 Na (one_dvd _) hNa
    simpa using this
  have := add_mem_box (h1 (box_nat_sub_one M hz)) ha
  rwa [sub_add_cancel] at this

lemma rpow_mul_rpow_neg (x : ℝ) (hx : 0 < x) (N : ℕ) : x ^ (N : ℝ) * x ^ (-(N : ℝ)) = 1 := by
  rw [Real.rpow_neg hx.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hx _).ne']

lemma tsp_theta_bound (N : ℕ) (φ : AdeleRing (𝓞 F) F → ℂ) (hφ : φ ∈ Tsp (F := F)) :
    ∃ C, ∀ h : IdeleGroup F, 1 ≤ ideleNorm h → ‖adelicThetaFun φ h‖ ≤ C * ideleNorm h ^ (-(N : ℝ)) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨M, hM, Ψ, a, rfl⟩ := hx
    obtain ⟨Na, hNa, ha⟩ := exists_den a
    have hc : ((Na : F)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast hNa)
    obtain ⟨k, Cw, hk, hCw, hdec⟩ := wt_decay _ hc N
    set K := ⌈k⌉₊
    have hkK : k ≤ K := Nat.le_ceil k
    refine ⟨2 ^ K * SK K Ψ * Cw, fun h hh => ?_⟩
    obtain ⟨hs, hb⟩ := hdec h hh
    have hA : 0 ≤ 2 ^ K * SK K Ψ := by have := SK_nonneg K Ψ; positivity
    have hpt : ∀ x, ‖Tt M Ψ a x‖ ≤ (2 ^ K * SK K Ψ) * Wt ((Na : F)⁻¹) k x := fun x =>
      (Tt_le M Ψ a _ (box_cond_of_den M a Na hNa ha) K x).trans
        (mul_le_mul_of_nonneg_left (Wt_anti _ hkK x) hA)
    refine (maj_theta _ _ _ k hpt h hs).trans ?_
    calc _ ≤ (2 ^ K * SK K Ψ) * (Cw * ideleNorm h ^ (-(N : ℝ))) := mul_le_mul_of_nonneg_left hb hA
      _ = _ := by ring
  | zero => exact ⟨0, fun h _ => by simp [adelicThetaFun]⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨C₁, h₁⟩ := ihx
    obtain ⟨C₂, h₂⟩ := ihy
    refine ⟨C₁ + C₂, fun h hh => ?_⟩
    rw [theta_add x y hx hy h, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h₁ h hh) (h₂ h hh))
  | smul c x hx ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨‖c‖ * C, fun h hh => ?_⟩
    rw [theta_smul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC h hh) (norm_nonneg _)

lemma fourierFun_zero : adelicFourierFun (0 : AdeleRing (𝓞 F) F → ℂ) = 0 := by
  funext y; simp [adelicFourierFun]

lemma tsp_thetaF_bound (N : ℕ) (φ : AdeleRing (𝓞 F) F → ℂ) (hφ : φ ∈ Tsp (F := F)) :
    ∃ C, ∀ h : IdeleGroup F, 1 ≤ ideleNorm h →
      ‖adelicThetaFun (adelicFourierFun φ) h‖ ≤ C * ideleNorm h ^ (-(N : ℝ)) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨M, hM, Ψ, a, rfl⟩ := hx
    obtain ⟨c', hc', Kb, hKb, hT⟩ := fourier_Tt_le (F := F) M hM
    obtain ⟨k, Cw, hk, hCw, hdec⟩ := wt_decay _ hc' N
    set K := ⌈k⌉₊
    have hkK : k ≤ K := Nat.le_ceil k
    set A := 2 ^ K * Kb ^ K * SK K (𝓕 Ψ)
    refine ⟨A * Cw, fun h hh => ?_⟩
    obtain ⟨hs, hb⟩ := hdec h hh
    have hA : 0 ≤ A := by
      have := SK_nonneg K (𝓕 Ψ)
      have : (0:ℝ) ≤ Kb := by linarith
      positivity
    have hpt : ∀ y, ‖adelicFourierFun (Tt M Ψ a) y‖ ≤ A * Wt c' k y := fun y =>
      (hT Ψ a K y).trans (mul_le_mul_of_nonneg_left (Wt_anti _ hkK y) hA)
    refine (maj_theta _ _ _ k hpt h hs).trans ?_
    calc _ ≤ A * (Cw * ideleNorm h ^ (-(N : ℝ))) := mul_le_mul_of_nonneg_left hb hA
      _ = _ := by ring
  | zero => exact ⟨0, fun h _ => by simp [adelicThetaFun, fourierFun_zero]⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨C₁, h₁⟩ := ihx
    obtain ⟨C₂, h₂⟩ := ihy
    refine ⟨C₁ + C₂, fun h hh => ?_⟩
    rw [thetaF_add x y hx hy h, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h₁ h hh) (h₂ h hh))
  | smul c x hx ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨‖c‖ * C, fun h hh => ?_⟩
    rw [thetaF_smul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC h hh) (norm_nonneg _)

lemma ofElem_eval {Γ k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))} {m n r s : ℕ}
    {d : Fin s → ℕ} (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) (u : ElemSchwartz m n r s d) :
    AdelicSchwartz.eval (SchwartzBruhat.ofElem Γ k π hs hπ u) =
      fun x : AdeleRing (𝓞 F) F => extendPullback Γ π u.toFun (ofAdd x) := rfl

lemma ev_small {X : Type*} [TopologicalSpace X] (G : X → ℝ) (hG : Continuous G) (x₀ : X)
    (hG0 : G x₀ = 0) (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ x in 𝓝 x₀, G x < δ := by
  have h1 : Set.Iio δ ∈ 𝓝 (G x₀) := by rw [hG0]; exact Iio_mem_nhds hδ
  exact hG.continuousAt h1

lemma stage_theta (N : ℕ) {Γ k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))} {m n r s : ℕ}
    {d : Fin s → ℕ} (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) (g₀ : ElemSchwartz m n r s d)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ g in 𝓝 g₀, ∀ h : IdeleGroup F, 1 ≤ ideleNorm h →
      ideleNorm h ^ (N : ℝ) * ‖adelicTheta (SchwartzBruhat.ofElem Γ k π hs hπ (g - g₀)) h‖ ≤ ε := by
  obtain ⟨M1, hM1, c, hc, Q, Ψa, hbox, hcont, hsub, hdec⟩ := stage_dec π hs hπ
  obtain ⟨k', Cw, hk', hCw, hwd⟩ := wt_decay c hc N
  set K := ⌈k'⌉₊
  have hkK : k' ≤ K := Nat.le_ceil k'
  let G : ElemSchwartz m n r s d → ℝ := fun g =>
    ∑ q ∈ Q, 2 ^ K * SK K (Ψa q.out g - Ψa q.out g₀)
  have hG : Continuous G := continuous_finset_sum _ fun q _ =>
    continuous_const.mul ((SK_cont K).comp ((hcont q.out).sub continuous_const))
  have hG0 : G g₀ = 0 := by simp [G, SK_zero]
  filter_upwards [ev_small G hG g₀ hG0 (ε / (Cw + 1)) (by positivity)] with g hg h hh
  set u := g - g₀
  have hGn : 0 ≤ G g := Finset.sum_nonneg fun q _ => by
    have := SK_nonneg K (Ψa q.out g - Ψa q.out g₀); positivity
  have hpt : ∀ x, ‖AdelicSchwartz.eval (SchwartzBruhat.ofElem Γ k π hs hπ u) x‖ ≤ G g * Wt c k' x := by
    intro x
    rw [ofElem_eval, hdec u, Finset.sum_apply]
    refine (norm_sum_le _ _).trans ?_
    simp only [G, Finset.sum_mul]
    refine Finset.sum_le_sum fun q hq => ?_
    rw [← hsub]
    refine (Tt_le M1 _ _ c (hbox q hq) K x).trans ?_
    exact mul_le_mul_of_nonneg_left (Wt_anti c hkK x) (by have := SK_nonneg K (Ψa q.out u); positivity)
  obtain ⟨hs', hb'⟩ := hwd h hh
  have h1 := (maj_theta _ (G g) c k' hpt h hs').trans (mul_le_mul_of_nonneg_left hb' hGn)
  have hn := ideleNorm_pos h
  have h2 : ideleNorm h ^ (N : ℝ) * ‖adelicTheta (SchwartzBruhat.ofElem Γ k π hs hπ u) h‖ ≤
      G g * Cw := by
    calc _ ≤ ideleNorm h ^ (N : ℝ) * (G g * (Cw * ideleNorm h ^ (-(N : ℝ)))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = G g * Cw * (ideleNorm h ^ (N : ℝ) * ideleNorm h ^ (-(N : ℝ))) := by ring
      _ = G g * Cw := by rw [rpow_mul_rpow_neg _ hn, mul_one]
  have h3 : G g * Cw ≤ ε / (Cw + 1) * Cw := mul_le_mul_of_nonneg_right hg.le hCw
  have h4 : ε / (Cw + 1) * Cw ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  linarith

lemma stage_thetaF (N : ℕ) {Γ k : Subgroup (Multiplicative (AdeleRing (𝓞 F) F))} {m n r s : ℕ}
    {d : Fin s → ℕ} (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) (g₀ : ElemSchwartz m n r s d)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ g in 𝓝 g₀, ∀ h : IdeleGroup F, 1 ≤ ideleNorm h →
      ideleNorm h ^ (N : ℝ) * ‖adelicThetaFun
        (adelicFourier (SchwartzBruhat.ofElem Γ k π hs hπ (g - g₀))) h‖ ≤ ε := by
  obtain ⟨M1, hM1, c, hc, Q, Ψa, hbox, hcont, hsub, hdec⟩ := stage_dec π hs hπ
  obtain ⟨c', hc', Kb, hKb, hT⟩ := fourier_Tt_le (F := F) M1 hM1
  obtain ⟨k', Cw, hk', hCw, hwd⟩ := wt_decay c' hc' N
  set K := ⌈k'⌉₊
  have hkK : k' ≤ K := Nat.le_ceil k'
  have hFc : Continuous (fun x : 𝓢(EuclideanSpace ℝ (Ix F), ℂ) => 𝓕 x) :=
    (SchwartzMap.fourierTransformCLM ℂ).continuous
  have hFsub : ∀ x y : 𝓢(EuclideanSpace ℝ (Ix F), ℂ), 𝓕 (x - y) = 𝓕 x - 𝓕 y := fun x y =>
    map_sub (SchwartzMap.fourierTransformCLM ℂ) x y
  have hKb0 : (0 : ℝ) ≤ Kb := by linarith
  let G : ElemSchwartz m n r s d → ℝ := fun g =>
    ∑ q ∈ Q, 2 ^ K * Kb ^ K * SK K (𝓕 (Ψa q.out g) - 𝓕 (Ψa q.out g₀))
  have hG : Continuous G := continuous_finset_sum _ fun q _ =>
    continuous_const.mul ((SK_cont K).comp ((hFc.comp (hcont q.out)).sub continuous_const))
  have hG0 : G g₀ = 0 := by simp [G, SK_zero]
  filter_upwards [ev_small G hG g₀ hG0 (ε / (Cw + 1)) (by positivity)] with g hg h hh
  set u := g - g₀
  have hGn : 0 ≤ G g := Finset.sum_nonneg fun q _ => by
    have := SK_nonneg K (𝓕 (Ψa q.out g) - 𝓕 (Ψa q.out g₀)); positivity
  have hpt : ∀ y, ‖adelicFourier (SchwartzBruhat.ofElem Γ k π hs hπ u) y‖ ≤ G g * Wt c' k' y := by
    intro y
    have e1 : adelicFourier (SchwartzBruhat.ofElem Γ k π hs hπ u) =
        adelicFourierFun (AdelicSchwartz.eval (SchwartzBruhat.ofElem Γ k π hs hπ u)) := rfl
    rw [e1, ofElem_eval, hdec u, fourier_sum Q _ (fun q => Tt_mem M1 hM1 _ _)]
    refine (norm_sum_le _ _).trans ?_
    simp only [G, Finset.sum_mul]
    refine Finset.sum_le_sum fun q hq => ?_
    rw [← hFsub, ← hsub]
    refine (hT _ _ K y).trans ?_
    exact mul_le_mul_of_nonneg_left (Wt_anti c' hkK y)
      (by have := SK_nonneg K (𝓕 (Ψa q.out u)); positivity)
  obtain ⟨hs', hb'⟩ := hwd h hh
  have h1 := (maj_theta _ (G g) c' k' hpt h hs').trans (mul_le_mul_of_nonneg_left hb' hGn)
  have hn := ideleNorm_pos h
  have h2 : ideleNorm h ^ (N : ℝ) *
      ‖adelicThetaFun (adelicFourier (SchwartzBruhat.ofElem Γ k π hs hπ u)) h‖ ≤ G g * Cw := by
    calc _ ≤ ideleNorm h ^ (N : ℝ) * (G g * (Cw * ideleNorm h ^ (-(N : ℝ)))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = G g * Cw * (ideleNorm h ^ (N : ℝ) * ideleNorm h ^ (-(N : ℝ))) := by ring
      _ = G g * Cw := by rw [rpow_mul_rpow_neg _ hn, mul_one]
  have h3 : G g * Cw ≤ ε / (Cw + 1) * Cw := mul_le_mul_of_nonneg_right hg.le hCw
  have h4 : ε / (Cw + 1) * Cw ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  linarith

lemma eval_add' (f g : AdelicSchwartz F) : (f + g).eval = f.eval + g.eval := rfl

lemma eval_smul' (c : ℂ) (f : AdelicSchwartz F) : (c • f).eval = c • f.eval := rfl

lemma norm_real_mul (x : ℝ) (hx : 0 ≤ x) (z : ℂ) : ‖((x : ℝ) : ℂ) * z‖ = x * ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx]

/-- uniform decay of `θ(f)` over a bounded set -/
theorem unif_theta (B : Set (AdelicSchwartz F)) (hB : Bornology.IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C, ∀ f ∈ B, ∀ h : IdeleGroup F, 1 ≤ ideleNorm h →
      ‖adelicTheta f h‖ ≤ C * ideleNorm h ^ (-(N : ℝ)) := by
  let ℓ : {h : IdeleGroup F // 1 ≤ ideleNorm h} → AdelicSchwartz F → ℂ :=
    fun h f => ((ideleNorm h.1 ^ (N : ℝ) : ℝ) : ℂ) * adelicTheta f h.1
  have hpos : ∀ h : IdeleGroup F, 0 ≤ ideleNorm h ^ (N : ℝ) := fun h =>
    (Real.rpow_pos_of_pos (ideleNorm_pos h) _).le
  obtain ⟨C, hC⟩ := bdd_family ℓ
    (fun h f g => by
      simp only [ℓ]
      rw [show adelicTheta (f + g) h.1 = adelicThetaFun (f.eval + g.eval) h.1 from rfl,
        theta_add _ _ (eval_mem_Tsp f) (eval_mem_Tsp g)]
      unfold adelicTheta; ring)
    (fun h c f => by
      simp only [ℓ]
      rw [show adelicTheta (c • f) h.1 = adelicThetaFun (c • f.eval) h.1 from rfl, theta_smul]
      unfold adelicTheta; ring)
    (fun f => by
      obtain ⟨C, hC⟩ := tsp_theta_bound N f.eval (eval_mem_Tsp f)
      refine ⟨C, fun h => ?_⟩
      simp only [ℓ]
      rw [norm_real_mul _ (hpos h.1)]
      have hn := ideleNorm_pos h.1
      calc _ ≤ ideleNorm h.1 ^ (N : ℝ) * (C * ideleNorm h.1 ^ (-(N : ℝ))) :=
            mul_le_mul_of_nonneg_left (hC h.1 h.2) (hpos h.1)
        _ = C * (ideleNorm h.1 ^ (N : ℝ) * ideleNorm h.1 ^ (-(N : ℝ))) := by ring
        _ = C := by rw [rpow_mul_rpow_neg _ hn, mul_one])
    (fun Γ k m n r s d π hs hπ g₀ ε hε => by
      filter_upwards [stage_theta N π hs hπ g₀ ε hε] with g hg h
      simp only [ℓ]
      rw [norm_real_mul _ (hpos h.1)]
      exact hg h.1 h.2)
    B hB
  refine ⟨C, fun f hf h hh => ?_⟩
  have h1 := hC f hf ⟨h, hh⟩
  simp only [ℓ] at h1
  rw [norm_real_mul _ (hpos h)] at h1
  have hn := ideleNorm_pos h
  have hq : 0 < ideleNorm h ^ (-(N : ℝ)) := Real.rpow_pos_of_pos hn _
  calc ‖adelicTheta f h‖ = ideleNorm h ^ (-(N : ℝ)) * (ideleNorm h ^ (N : ℝ) * ‖adelicTheta f h‖) := by
        rw [← mul_assoc, mul_comm (ideleNorm h ^ (-(N : ℝ))), rpow_mul_rpow_neg _ hn, one_mul]
    _ ≤ ideleNorm h ^ (-(N : ℝ)) * C := mul_le_mul_of_nonneg_left h1 hq.le
    _ = _ := by ring

/-- uniform decay of `θ(f̂)` over a bounded set -/
theorem unif_thetaF (B : Set (AdelicSchwartz F)) (hB : Bornology.IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C, ∀ f ∈ B, ∀ h : IdeleGroup F, 1 ≤ ideleNorm h →
      ‖adelicThetaFun (adelicFourier f) h‖ ≤ C * ideleNorm h ^ (-(N : ℝ)) := by
  let ℓ : {h : IdeleGroup F // 1 ≤ ideleNorm h} → AdelicSchwartz F → ℂ :=
    fun h f => ((ideleNorm h.1 ^ (N : ℝ) : ℝ) : ℂ) * adelicThetaFun (adelicFourier f) h.1
  have hpos : ∀ h : IdeleGroup F, 0 ≤ ideleNorm h ^ (N : ℝ) := fun h =>
    (Real.rpow_pos_of_pos (ideleNorm_pos h) _).le
  obtain ⟨C, hC⟩ := bdd_family ℓ
    (fun h f g => by
      simp only [ℓ]
      rw [show adelicFourier (f + g) = adelicFourierFun (f.eval + g.eval) from rfl,
        thetaF_add _ _ (eval_mem_Tsp f) (eval_mem_Tsp g)]
      unfold adelicFourier; ring)
    (fun h c f => by
      simp only [ℓ]
      rw [show adelicFourier (c • f) = adelicFourierFun (c • f.eval) from rfl, thetaF_smul]
      unfold adelicFourier; ring)
    (fun f => by
      obtain ⟨C, hC⟩ := tsp_thetaF_bound N f.eval (eval_mem_Tsp f)
      refine ⟨C, fun h => ?_⟩
      simp only [ℓ]
      rw [norm_real_mul _ (hpos h.1)]
      have hn := ideleNorm_pos h.1
      calc _ ≤ ideleNorm h.1 ^ (N : ℝ) * (C * ideleNorm h.1 ^ (-(N : ℝ))) :=
            mul_le_mul_of_nonneg_left (hC h.1 h.2) (hpos h.1)
        _ = C * (ideleNorm h.1 ^ (N : ℝ) * ideleNorm h.1 ^ (-(N : ℝ))) := by ring
        _ = C := by rw [rpow_mul_rpow_neg _ hn, mul_one])
    (fun Γ k m n r s d π hs hπ g₀ ε hε => by
      filter_upwards [stage_thetaF N π hs hπ g₀ ε hε] with g hg h
      simp only [ℓ]
      rw [norm_real_mul _ (hpos h.1)]
      exact hg h.1 h.2)
    B hB
  refine ⟨C, fun f hf h hh => ?_⟩
  have h1 := hC f hf ⟨h, hh⟩
  simp only [ℓ] at h1
  rw [norm_real_mul _ (hpos h)] at h1
  have hn := ideleNorm_pos h
  have hq : 0 < ideleNorm h ^ (-(N : ℝ)) := Real.rpow_pos_of_pos hn _
  calc ‖adelicThetaFun (adelicFourier f) h‖ = ideleNorm h ^ (-(N : ℝ)) *
        (ideleNorm h ^ (N : ℝ) * ‖adelicThetaFun (adelicFourier f) h‖) := by
        rw [← mul_assoc, mul_comm (ideleNorm h ^ (-(N : ℝ))), rpow_mul_rpow_neg _ hn, one_mul]
    _ ≤ ideleNorm h ^ (-(N : ℝ)) * C := mul_le_mul_of_nonneg_left h1 hq.le
    _ = _ := by ring

end Uniform


/-! ### assembly -/

section FinalA

lemma ideleNorm_one' : ideleNorm (1 : IdeleGroup F) = 1 := by
  have := ideleNorm_principal (F := F) 1
  rwa [map_one] at this

lemma ideleNorm_inv' (g : IdeleGroup F) : ideleNorm g⁻¹ = (ideleNorm g)⁻¹ := by
  have h := ideleNorm_mul g g⁻¹
  rw [mul_inv_cancel, ideleNorm_one'] at h
  have hp := ideleNorm_pos g
  field_simp
  linarith

lemma zpow_neg_eq_rpow (x : ℝ) (N : ℕ) : x ^ (-(N : ℤ)) = x ^ (-(N : ℝ)) := by
  rw [← Real.rpow_intCast]; push_cast; rfl

theorem main_A (B : Set (AdelicSchwartz F)) (hB : Bornology.IsVonNBounded ℂ B) (N : ℕ) :
    (∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : IdeleGroup F, 1 < ideleNorm g →
      ‖adelicTheta f g‖ ≤ C * ideleNorm g ^ (-(N : ℤ))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : IdeleGroup F, ideleNorm g < 1 →
      ‖adelicTheta f g - ((ideleNorm g)⁻¹ : ℝ) * adelicFourier f 0 + f.eval 0‖ ≤
        C * ideleNorm g ^ N) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, f.IsPolarFree → ∀ g : IdeleGroup F, ideleNorm g ≠ 1 →
      ‖adelicTheta f g‖ ≤ C * Real.exp (-(N * |Real.log (ideleNorm g)|))) := by
  obtain ⟨C1, hC1⟩ := unif_theta B hB N
  obtain ⟨C2, hC2⟩ := unif_thetaF B hB (N + 1)
  -- the bound at infinity
  have hinf : ∀ f ∈ B, ∀ g : IdeleGroup F, 1 < ideleNorm g →
      ‖adelicTheta f g‖ ≤ max C1 1 * ideleNorm g ^ (-(N : ℝ)) := by
    intro f hf g hg
    refine (hC1 f hf g hg.le).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact (Real.rpow_pos_of_pos (ideleNorm_pos g) _).le
  -- the bound at zero
  have hzero : ∀ f ∈ B, ∀ g : IdeleGroup F, ideleNorm g < 1 →
      ‖adelicTheta f g - ((ideleNorm g)⁻¹ : ℝ) * adelicFourier f 0 + f.eval 0‖ ≤
        max C2 1 * ideleNorm g ^ N := by
    intro f hf g hg
    have hp := ideleNorm_pos g
    have hRR := (RR_fun f.eval (eval_mem_Tsp f) g).2.2
    have e1 : adelicTheta f g - ((ideleNorm g)⁻¹ : ℝ) * adelicFourier f 0 + f.eval 0 =
        ((ideleNorm g)⁻¹ : ℝ) * adelicThetaFun (adelicFourier f) g⁻¹ := by
      change adelicThetaFun f.eval g - _ * adelicFourierFun f.eval 0 + _ = _
      rw [hRR]; unfold adelicFourier; ring
    rw [e1, norm_real_mul _ (inv_nonneg.mpr hp.le)]
    have hgi : 1 ≤ ideleNorm g⁻¹ := by
      rw [ideleNorm_inv']; exact (one_le_inv₀ hp).mpr hg.le
    have h2 := hC2 f hf g⁻¹ hgi
    rw [ideleNorm_inv', Real.inv_rpow hp.le, Real.rpow_neg (by positivity), inv_inv,
      Real.rpow_natCast] at h2
    have h3 : (ideleNorm g)⁻¹ * (C2 * ideleNorm g ^ (N + 1)) = C2 * ideleNorm g ^ N := by
      field_simp; ring
    calc (ideleNorm g)⁻¹ * ‖adelicThetaFun (adelicFourier f) g⁻¹‖
        ≤ (ideleNorm g)⁻¹ * (C2 * ideleNorm g ^ (N + 1)) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hp.le)
      _ = C2 * ideleNorm g ^ N := h3
      _ ≤ max C2 1 * ideleNorm g ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  refine ⟨⟨max C1 1, by positivity, fun f hf g hg => ?_⟩,
    ⟨max C2 1, by positivity, hzero⟩, ⟨max (max C1 1) (max C2 1), by positivity, ?_⟩⟩
  · rw [zpow_neg_eq_rpow]; exact hinf f hf g hg
  · intro f hf hpf g hg
    have hp := ideleNorm_pos g
    rcases lt_or_gt_of_ne hg with hlt | hgt
    · have h1 := hzero f hf g hlt
      rw [hpf.1, hpf.2] at h1
      simp only [mul_zero, sub_zero, add_zero] at h1
      have hlog : Real.log (ideleNorm g) < 0 := Real.log_neg hp hlt
      rw [abs_of_neg hlog]
      have e : Real.exp (-(N * -Real.log (ideleNorm g))) = ideleNorm g ^ N := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hp]; congr 1; ring
      rw [e]
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    · have h1 := hinf f hf g hgt
      have hlog : 0 < Real.log (ideleNorm g) := Real.log_pos hgt
      rw [abs_of_pos hlog]
      have e : Real.exp (-(N * Real.log (ideleNorm g))) = ideleNorm g ^ (-(N : ℝ)) := by
        rw [Real.rpow_def_of_pos hp]; congr 1; ring
      rw [e]
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

end FinalA

end AuxA

end Aux_MasulloGRH_adelic_theta_estimates

theorem solution (F : Type*) [Field F] [NumberField F]
    (B : Set (AdelicSchwartz F)) (hB : Bornology.IsVonNBounded ℂ B) (N : ℕ) :
    (∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : IdeleGroup F, 1 < ideleNorm g →
      ‖adelicTheta f g‖ ≤ C * ideleNorm g ^ (-(N : ℤ))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : IdeleGroup F, ideleNorm g < 1 →
      ‖adelicTheta f g - ((ideleNorm g)⁻¹ : ℝ) * adelicFourier f 0 + f.eval 0‖ ≤
        C * ideleNorm g ^ N) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, f.IsPolarFree → ∀ g : IdeleGroup F, ideleNorm g ≠ 1 →
      ‖adelicTheta f g‖ ≤ C * Real.exp (-(N * |Real.log (ideleNorm g)|))) :=
  Aux_MasulloGRH_adelic_theta_estimates.AuxA.main_A B hB N
