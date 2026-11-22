-- Prove2me | solution 1 for MasulloGRH.adelicSchwartz_dilation_equiv_and_fourier
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:59:50.760464+00:00
-- url     : https://prove2.me/submissions/2140c0d1-da6e-4252-8961-9253ff51e311

import Mathlib
import Definitions.Def_MasulloGRH_AdelicTheta

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

/-!
The measure-theoretic part (Haar modulus of multiplication by an idele on the adeles, computed
against the Tamagawa measure) reuses the auxiliary development of the accepted platform proof of
`MasulloGRH.adelic_riemann_roch` (lines kept verbatim, inside its own namespace).
-/

open MasulloGRH

namespace Aux_MasulloGRH_adelic_riemann_roch

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


end Modulus2

end AuxA

end Aux_MasulloGRH_adelic_riemann_roch


namespace Sol_MasulloGRH_adelicSchwartz_dilation_equiv_and_fourier

set_option linter.unusedSectionVars false

open Topology

section gen

variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [CommGroup H] [TopologicalSpace H]

/-- The underlying monoid hom of a continuous multiplicative equivalence. -/
def cmh (e : G ≃ₜ* H) : G →* H := e.toMulEquiv.toMonoidHom

lemma cmh_apply (e : G ≃ₜ* H) (x : G) : cmh e x = e x := rfl

lemma cg_comap (e : G ≃ₜ* H) (A : Subgroup H) (hA : IsCompactlyGeneratedSubgroup A) :
    IsCompactlyGeneratedSubgroup (A.comap (cmh e)) := by
  obtain ⟨U, hU, hUA, ⟨V, hV, hVU⟩, hcl⟩ := hA
  refine ⟨e ⁻¹' U, ?_, ?_, ⟨e ⁻¹' V, ?_, ?_⟩, ?_⟩
  · exact e.toHomeomorph.isCompact_preimage.mpr hU
  · intro x hx
    exact hUA hx
  · apply e.continuous.continuousAt.preimage_mem_nhds
    have : e 1 = 1 := map_one e
    change V ∈ 𝓝 (e 1)
    rw [this]
    exact hV
  · rintro x ⟨hx1, hx2⟩
    exact hVU ⟨hx1, hx2⟩
  · apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rw [← hcl]
      exact Subgroup.subset_closure hx
    · intro x hx
      have h1 : Subgroup.closure U ≤ (Subgroup.closure (e ⁻¹' U)).comap (cmh e.symm) := by
        rw [Subgroup.closure_le]
        intro y hy
        apply Subgroup.subset_closure
        change e (e.symm y) ∈ U
        rw [ContinuousMulEquiv.apply_symm_apply]
        exact hy
      have h2 : cmh e x ∈ Subgroup.closure U := by
        rw [hcl]
        exact hx
      have h3 := h1 h2
      change e.symm (e x) ∈ Subgroup.closure (e ⁻¹' U) at h3
      rwa [ContinuousMulEquiv.symm_apply_apply] at h3

end gen

section dual

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- A continuous multiplicative equivalence as a continuous monoid hom. -/
def ccmh (e : G ≃ₜ* G) : G →ₜ* G :=
  { toMonoidHom := cmh e, continuous_toFun := e.continuous }

/-- The dual automorphism `χ ↦ χ ∘ e⁻¹` of the Pontryagin dual. -/
noncomputable def dualE (e : G ≃ₜ* G) : PontryaginDual G ≃ₜ* PontryaginDual G where
  toFun χ := PontryaginDual.map (ccmh e.symm) χ
  invFun χ := PontryaginDual.map (ccmh e) χ
  left_inv χ := by
    ext x
    simp only [PontryaginDual.map_apply]
    have : (ccmh e.symm) ((ccmh e) x) = x := e.symm_apply_apply x
    rw [this]
  right_inv χ := by
    ext x
    simp only [PontryaginDual.map_apply]
    have : (ccmh e) ((ccmh e.symm) x) = x := e.apply_symm_apply x
    rw [this]
  map_mul' χ ψ := map_mul _ χ ψ
  continuous_toFun := (PontryaginDual.map (ccmh e.symm)).continuous
  continuous_invFun := (PontryaginDual.map (ccmh e)).continuous

lemma dualE_apply (e : G ≃ₜ* G) (χ : PontryaginDual G) (x : G) :
    dualE e χ x = χ (e.symm x) := rfl

lemma annihilator_comap (e : G ≃ₜ* G) (k : Subgroup G) :
    annihilator (k.comap (cmh e)) = dualE e ⁻¹' annihilator k := by
  ext χ
  simp only [annihilator, Set.mem_ofPred_eq, Set.mem_preimage, dualE_apply]
  constructor
  · intro h y hy
    apply h
    change e (e.symm y) ∈ k
    rwa [ContinuousMulEquiv.apply_symm_apply]
  · intro h x hx
    have := h (e x) hx
    rwa [ContinuousMulEquiv.symm_apply_apply] at this

variable [IsTopologicalGroup G]

lemma good_comap (e : G ≃ₜ* G) (k : Subgroup G) (hk : IsGoodSubgroup k) :
    IsGoodSubgroup (k.comap (cmh e)) := by
  obtain ⟨hcl, hop, A, hA, hAcg⟩ := hk
  refine ⟨hcl.preimage e.continuous, ?_, A.comap (cmh (dualE e)), ?_, cg_comap _ _ hAcg⟩
  · rw [annihilator_comap]
    exact hop.preimage (dualE e).continuous
  · rw [annihilator_comap, Subgroup.coe_comap, hA]
    rfl

lemma structural_comap (e : G ≃ₜ* G) (Γ k : Subgroup G) (hs : IsStructuralPair Γ k) :
    IsStructuralPair (Γ.comap (cmh e)) (k.comap (cmh e)) := by
  obtain ⟨hΓo, hΓcg, hk, hkΓ⟩ := hs
  exact ⟨hΓo.preimage e.continuous, cg_comap e Γ hΓcg, good_comap e k hk,
    Subgroup.comap_mono hkΓ⟩

lemma symm_mem_comap (e : G ≃ₜ* G) (Γ : Subgroup G) (y : Γ) :
    e.symm (y : G) ∈ Γ.comap (cmh e) := by
  change e (e.symm (y : G)) ∈ Γ
  rw [ContinuousMulEquiv.apply_symm_apply]
  exact y.2

/-- The restriction `Γ.comap e ≃ₜ Γ` of `e`. -/
def resH (e : G ≃ₜ* G) (Γ : Subgroup G) : Γ.comap (cmh e) ≃ₜ Γ where
  toFun x := ⟨e x, x.2⟩
  invFun y := ⟨e.symm y, symm_mem_comap e Γ y⟩
  left_inv x := Subtype.ext (ContinuousMulEquiv.symm_apply_apply e x)
  right_inv y := Subtype.ext (ContinuousMulEquiv.apply_symm_apply e y)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

section pres

variable {m n r s : ℕ} {d : Fin s → ℕ}

/-- The transported presentation. -/
def presE (e : G ≃ₜ* G) (Γ : Subgroup G) (π : Γ →* Multiplicative (ElemGroup m n r s d)) :
    Γ.comap (cmh e) →* Multiplicative (ElemGroup m n r s d) :=
  π.comp ((cmh e).subgroupComap Γ)

lemma presE_apply (e : G ≃ₜ* G) (Γ : Subgroup G) (π : Γ →* Multiplicative (ElemGroup m n r s d))
    (x : Γ.comap (cmh e)) : presE e Γ π x = π (resH e Γ x) := rfl

lemma presentation_comap (e : G ≃ₜ* G) (Γ k : Subgroup G)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hπ : IsElemPresentation Γ k π) :
    IsElemPresentation (Γ.comap (cmh e)) (k.comap (cmh e)) (presE e Γ π) := by
  obtain ⟨hd, hc, ho, hsurj, hker⟩ := hπ
  have hfun : (presE e Γ π : Γ.comap (cmh e) → Multiplicative (ElemGroup m n r s d)) =
      (π : Γ → Multiplicative (ElemGroup m n r s d)) ∘ (resH e Γ) := rfl
  refine ⟨hd, ?_, ?_, ?_, ?_⟩
  · rw [hfun]
    exact hc.comp (resH e Γ).continuous
  · rw [hfun]
    exact ho.comp (resH e Γ).isOpenMap
  · rw [hfun]
    exact hsurj.comp (resH e Γ).surjective
  · intro x
    rw [presE_apply, hker]
    rfl

lemma extendPullback_comap (e : G ≃ₜ* G) (Γ : Subgroup G)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (u : ElemGroup m n r s d → ℂ) :
    extendPullback (Γ.comap (cmh e)) (presE e Γ π) u = fun x => extendPullback Γ π u (e x) := by
  funext x
  by_cases hx : e x ∈ Γ
  · have hx' : x ∈ Γ.comap (cmh e) := hx
    simp only [extendPullback, dif_pos hx, dif_pos hx']
    rfl
  · have hx' : x ∉ Γ.comap (cmh e) := hx
    simp only [extendPullback, dif_neg hx, dif_neg hx']

end pres

lemma pull_mem (e : G ≃ₜ* G) (f : G → ℂ) (hf : f ∈ schwartzBruhatSubmodule G) :
    (fun x => f (e x)) ∈ schwartzBruhatSubmodule G := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨Γ, k, m, n, r, s, d, π, u, hs, hπ, rfl⟩ := hf
    refine Submodule.subset_span ⟨Γ.comap (cmh e), k.comap (cmh e), m, n, r, s, d, presE e Γ π, u,
      structural_comap e Γ k hs, presentation_comap e Γ k π hπ, ?_⟩
    rw [extendPullback_comap]
  | zero => exact Submodule.zero_mem _
  | add f₁ f₂ _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul c f _ h => exact Submodule.smul_mem _ c h

/-- Pull-back of Schwartz–Bruhat functions along a topological automorphism. -/
noncomputable def pullL (e : G ≃ₜ* G) : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G where
  toFun f := ⟨fun x => f.1 (e x), pull_mem e f.1 f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma pullL_apply (e : G ≃ₜ* G) (f : SchwartzBruhat G) (x : G) :
    (pullL e f).toFun x = f.toFun (e x) := rfl

lemma pullL_ofElem (e : G ≃ₜ* G) {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (u : ElemSchwartz m n r s d) :
    pullL e (SchwartzBruhat.ofElem Γ k π hs hπ u) =
      SchwartzBruhat.ofElem (Γ.comap (cmh e)) (k.comap (cmh e)) (presE e Γ π)
        (structural_comap e Γ k hs) (presentation_comap e Γ k π hπ) u := by
  apply Subtype.ext
  change (fun x => extendPullback Γ π u.toFun (e x)) =
    extendPullback (Γ.comap (cmh e)) (presE e Γ π) u.toFun
  rw [extendPullback_comap]

variable (G) in
/-- The set of topologies whose infimum is the topology of `S(G)`. -/
def stageTops : Set (TopologicalSpace (SchwartzBruhat G)) :=
  {t | IsLocallyConvexTopology (SchwartzBruhat G) t ∧
    ∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
      (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
      (hπ : IsElemPresentation Γ k π),
      @Continuous (ElemSchwartz m n r s d) (SchwartzBruhat G) _ t
        (SchwartzBruhat.ofElem Γ k π hs hπ)}

variable (G) in
lemma topology_eq : instTopologicalSpaceSchwartzBruhat G = sInf (stageTops G) := rfl

lemma pullL_stage (e : G ≃ₜ* G) (t : TopologicalSpace (SchwartzBruhat G))
    (ht : t ∈ stageTops G) : TopologicalSpace.induced (pullL e) t ∈ stageTops G := by
  refine ⟨?_, ?_⟩
  · obtain ⟨ι, hι, p, hp⟩ := ht.1
    exact ⟨ι, hι, p.comp (pullL e), LinearMap.withSeminorms_induced hp _⟩
  · intro Γ k m n r s d π hs hπ
    rw [continuous_induced_rng]
    have h := ht.2 (Γ.comap (cmh e)) (k.comap (cmh e)) m n r s d (presE e Γ π)
      (structural_comap e Γ k hs) (presentation_comap e Γ k π hπ)
    have heq : (pullL e ∘ SchwartzBruhat.ofElem Γ k π hs hπ) =
        SchwartzBruhat.ofElem (Γ.comap (cmh e)) (k.comap (cmh e)) (presE e Γ π)
        (structural_comap e Γ k hs) (presentation_comap e Γ k π hπ) := by
      funext u
      exact pullL_ofElem e Γ k π hs hπ u
    rw [heq]
    exact h

lemma pullL_continuous (e : G ≃ₜ* G) : Continuous (pullL e) := by
  rw [continuous_iff_le_induced]
  have key : ∀ t ∈ stageTops G,
      instTopologicalSpaceSchwartzBruhat G ≤ TopologicalSpace.induced (pullL e) t := by
    intro t ht
    rw [topology_eq]
    exact sInf_le (pullL_stage e t ht)
  calc instTopologicalSpaceSchwartzBruhat G
        ≤ sInf (TopologicalSpace.induced (pullL e) '' stageTops G) := by
          refine le_sInf ?_
          rintro _ ⟨t, ht, rfl⟩
          exact key t ht
    _ = TopologicalSpace.induced (pullL e) (sInf (stageTops G)) := induced_sInf.symm
    _ = TopologicalSpace.induced (pullL e) (instTopologicalSpaceSchwartzBruhat G) := rfl

/-- Pull-back along a topological automorphism, as a topological linear automorphism. -/
noncomputable def pullCLE (e : G ≃ₜ* G) : SchwartzBruhat G ≃L[ℂ] SchwartzBruhat G :=
  { pullL e with
    invFun := pullL e.symm
    left_inv := fun f => by
      apply Subtype.ext
      funext x
      change f.1 (e (e.symm x)) = f.1 x
      rw [ContinuousMulEquiv.apply_symm_apply]
    right_inv := fun f => by
      apply Subtype.ext
      funext x
      change f.1 (e.symm (e x)) = f.1 x
      rw [ContinuousMulEquiv.symm_apply_apply]
    continuous_toFun := pullL_continuous e
    continuous_invFun := pullL_continuous e.symm }

lemma pullCLE_apply (e : G ≃ₜ* G) (f : SchwartzBruhat G) (x : G) :
    (pullCLE e f).toFun x = f.toFun (e x) := rfl

end dual


section adelic

open Aux_MasulloGRH_adelic_riemann_roch.AuxA

variable {F : Type*} [Field F] [NumberField F]

/-- Multiplication by an idele, as a homeomorphism of the adeles. -/
noncomputable def mulH (g : IdeleGroup F) : AdeleRing (𝓞 F) F ≃ₜ AdeleRing (𝓞 F) F where
  toFun := mulG g
  invFun := mulG g⁻¹
  left_inv := mulG_inv_mulG g
  right_inv := mulG_mulG_inv g
  continuous_toFun := continuous_mulG g
  continuous_invFun := continuous_mulG g⁻¹

lemma integral_mul_left (g : IdeleGroup F) (h : AdeleRing (𝓞 F) F → ℂ) :
    ∫ x, h ((g : AdeleRing (𝓞 F) F) * x) ∂tamagawaAdelic =
      ((ideleNorm g)⁻¹ : ℝ) * ∫ x, h x ∂tamagawaAdelic := by
  have hme : MeasurableEmbedding (mulG g) := (mulH g).measurableEmbedding
  have e1 : (fun x => h ((g : AdeleRing (𝓞 F) F) * x)) = fun x => h (mulG g x) := by
    funext x
    simp only [mulG, mul_comm]
  calc ∫ x, h ((g : AdeleRing (𝓞 F) F) * x) ∂tamagawaAdelic
        = ∫ x, h (mulG g x) ∂tamagawaAdelic := by rw [e1]
    _ = ∫ y, h y ∂(muG g) := (hme.integral_map h).symm
    _ = ((ideleNorm g)⁻¹ : ℝ) * ∫ x, h x ∂tamagawaAdelic := by
      rw [muG_eq, integral_smul_measure, ENNReal.coe_toReal, kappa_eq_inv, Complex.real_smul]

/-- Dilation `x ↦ g x` by an idele, as a topological automorphism of `(𝔸_F, +)`. -/
noncomputable def dilE (g : IdeleGroup F) :
    Multiplicative (AdeleRing (𝓞 F) F) ≃ₜ* Multiplicative (AdeleRing (𝓞 F) F) where
  toFun x := Multiplicative.ofAdd ((g : AdeleRing (𝓞 F) F) * Multiplicative.toAdd x)
  invFun x := Multiplicative.ofAdd (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) *
    Multiplicative.toAdd x)
  left_inv x := by
    simp only [toAdd_ofAdd, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul,
      ofAdd_toAdd]
  right_inv x := by
    simp only [toAdd_ofAdd, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul,
      ofAdd_toAdd]
  map_mul' x y := by
    simp only [toAdd_mul, mul_add, ofAdd_add]
  continuous_toFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)
  continuous_invFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)

end adelic

end Sol_MasulloGRH_adelicSchwartz_dilation_equiv_and_fourier

open Sol_MasulloGRH_adelicSchwartz_dilation_equiv_and_fourier in
theorem solution
    (F : Type*) [Field F] [NumberField F] (g : IdeleGroup F) :
    ∃ T : AdelicSchwartz F ≃L[ℂ] AdelicSchwartz F,
      (∀ (f : AdelicSchwartz F) (x : AdeleRing (𝓞 F) F),
        (T f).eval x = f.eval ((g : AdeleRing (𝓞 F) F) * x)) ∧
      ∀ (f : AdelicSchwartz F) (y : AdeleRing (𝓞 F) F),
        adelicFourier (T f) y =
          (((ideleNorm g)⁻¹ : ℝ) : ℂ) *
            adelicFourier f (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) * y) := by
  have hev : ∀ (f : AdelicSchwartz F) (x : AdeleRing (𝓞 F) F),
      AdelicSchwartz.eval (pullCLE (dilE g) f) x = f.eval ((g : AdeleRing (𝓞 F) F) * x) := fun _ _ => rfl
  refine ⟨pullCLE (dilE g), hev, fun f y => ?_⟩
  have key : ∀ x : AdeleRing (𝓞 F) F,
      AdelicSchwartz.eval (pullCLE (dilE g) f) x * stdAdelicCharacter (x * y) =
        (fun u => f.eval u * stdAdelicCharacter
          (u * (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) * y))) ((g : AdeleRing (𝓞 F) F) * x) := by
    intro x
    rw [hev]
    have hgg : (g : AdeleRing (𝓞 F) F) * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have : (g : AdeleRing (𝓞 F) F) * x * (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) * y) =
        x * y := by
      calc (g : AdeleRing (𝓞 F) F) * x * (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) * y)
          = x * y * ((g : AdeleRing (𝓞 F) F) * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F)) := by
            ring
        _ = x * y := by rw [hgg, mul_one]
    simp only [this]
  unfold adelicFourier adelicFourierFun
  simp_rw [key]
  exact integral_mul_left g (fun u => f.eval u * stdAdelicCharacter
    (u * (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) * y)))
