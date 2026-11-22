-- Prove2me | solution 1 for MasulloGRH.sZetaIntegral_mul_fourier_symm
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:44:53.890145+00:00
-- url     : https://prove2.me/submissions/ed9d5ece-17ec-4c8b-83a4-3a6d749173e7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloGRH_SLocalZetaIntegrals
import Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion
import Theorems.Thm_RiemannMasullo_finiteLocalAdditiveTamagawaMeasure_isAddHaar
import Theorems.Thm_MasulloGRH_sZetaIntegral_integrable_and_differentiableOn
import Theorems.Thm_MasulloGRH_sLocalFourier_schwartzBruhat_equiv
import Theorems.Thm_MasulloGRH_sMultiplicativeTamagawa_isHaarMeasure_and_rectangle
import Theorems.Thm_MasulloGRH_sAdditiveTamagawa_selfDual_sStdCharacter

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false

/-!
# Tate's symmetry lemma for the `S`-local zeta integrals

`Z_S(f, c) Z_S(\hat h, \hat c) = Z_S(h, c) Z_S(\hat f, \hat c)` for a quasi-character `c` of
exponent `σ ∈ (0, 1)`.

* `ae_isUnit`: `ν_S`-almost every `S`-adele is an `S`-idele (the local additive Haar measures have
  no atoms).
* `integral_units_mul_norm`: `∫ Φ(g) |g| dμ_S(g) = κ_S ∫ Φ dν_S`, from the density
  `dμ_S = κ_S |·|⁻¹ dν_S`.
* `integral_mul_fourier_comm`: `∫ f(x) \hat h(x z) dν_S(x) = ∫ h(x) \hat f(x z) dν_S(x)` (Fubini).
* `zeta_mul_eq_kernel`: `Z(φ, c) Z(φ', \hat c) = ∫ (∫ φ(a) φ'(a b) |a| dμ_S(a)) \hat c(b) dμ_S(b)`
  (Fubini and the Haar invariance `(a, b) ↦ (a, a b)` of `μ_S × μ_S`).
-/

namespace Sol_MasulloGRH_sZetaIntegral_mul_fourier_symm
open MasulloGRH Topology Filter

variable {F : Type*} [Field F] [NumberField F]

omit [NumberField F] in
theorem nhdsNE_inf (w : InfinitePlace F) : (𝓝[≠] (0 : w.Completion)).NeBot := by
  have h2 : ‖(2 : w.Completion)‖ = 2 := by
    have := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) (2 : w.Completion)
    rw [← this, map_ofNat]; norm_num
  let _ : NontriviallyNormedField w.Completion :=
    NontriviallyNormedField.ofNormNeOne ⟨2, fun h => by rw [h, norm_zero] at h2; norm_num at h2,
      by rw [h2]; norm_num⟩
  exact NormedField.nhdsNE_neBot (0 : w.Completion)

theorem nhdsNE_fin (v : HeightOneSpectrum (𝓞 F)) : (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
  obtain ⟨π, hπ⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hn : ‖π‖ ≠ 1 := by
    intro h
    have : Valued.v π = 1 := by
      rw [le_antisymm_iff, ← Valued.toNormedField.norm_le_one_iff,
        ← Valued.toNormedField.one_le_norm_iff, h]; exact ⟨le_rfl, le_rfl⟩
    rw [hπ] at this
    exact absurd this (by decide)
  let _ : NontriviallyNormedField (v.adicCompletion F) :=
    NontriviallyNormedField.ofNormNeOne ⟨π, hπ0, hn⟩
  exact NormedField.nhdsNE_neBot (0 : v.adicCompletion F)

omit [NumberField F] in
theorem infinite_haar (w : InfinitePlace F) :
    (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure := by
  open InfinitePlace.Completion in
  by_cases h : w.IsReal
  · rw [RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure, dif_pos h]
    exact (ringEquivRealOfIsReal h).symm.toAddEquiv.isAddHaarMeasure_map volume
      (isometryEquivRealOfIsReal h).symm.continuous (isometryEquivRealOfIsReal h).continuous
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp h
    rw [RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure, dif_neg h]
    have : (2 • (volume : Measure ℂ)).IsAddHaarMeasure := by
      rw [show 2 • (volume : Measure ℂ) = (2 : ℝ≥0∞) • volume by simp [two_smul]]
      exact Measure.IsAddHaarMeasure.smul (μ := (volume : Measure ℂ)) (by norm_num) (by simp)
    exact (ringEquivComplexOfIsComplex hc).symm.toAddEquiv.isAddHaarMeasure_map _
      (isometryEquivComplexOfIsComplex hc).symm.continuous
      (isometryEquivComplexOfIsComplex hc).continuous

omit [NumberField F] in
theorem nullSingleton_inf (w : InfinitePlace F) :
    NullSingletonClass (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w) := by
  have := infinite_haar w
  have := nhdsNE_inf w
  infer_instance

theorem nullSingleton_fin (v : HeightOneSpectrum (𝓞 F)) :
    NullSingletonClass (RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v) := by
  have := RiemannMasullo.finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have := nhdsNE_fin v
  have := RiemannMasullo.locallyCompactSpace_adicCompletion (K := F) v
  infer_instance

omit [NumberField F] in
theorem secondCountable_infinite (w : InfinitePlace F) :
    SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

theorem countable_numberField : Countable F := by
  have h : ({x : F | IsAlgebraic ℚ x}).Countable := Algebraic.countable ℚ F
  have huniv : {x : F | IsAlgebraic ℚ x} = Set.univ :=
    Set.eq_univ_of_forall fun x => Algebra.IsAlgebraic.isAlgebraic x
  rw [huniv] at h
  exact Set.countable_univ_iff.mp h

theorem secondCountable_finite (v : HeightOneSpectrum (𝓞 F)) :
    SecondCountableTopology (v.adicCompletion F) := by
  have : Countable F := countable_numberField
  have : TopologicalSpace.SeparableSpace (v.adicCompletion F) :=
    ⟨⟨Set.range (algebraMap F (v.adicCompletion F)), Set.countable_range _,
      v.denseRange_algebraMap F⟩⟩
  exact UniformSpace.secondCountable_of_separable _

omit [NumberField F] in
theorem sigmaFinite_inf (w : InfinitePlace F) :
    SigmaFinite (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w) := by
  have := infinite_haar w
  have := secondCountable_infinite w
  infer_instance

theorem sigmaFinite_fin (v : HeightOneSpectrum (𝓞 F)) :
    SigmaFinite (RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v) := by
  have := RiemannMasullo.finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have := RiemannMasullo.locallyCompactSpace_adicCompletion (K := F) v
  have := secondCountable_finite v
  infer_instance

variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

theorem ae_isUnit : ∀ᵐ x ∂(sAdditiveTamagawa F Sf), IsUnit x := by
  have hsf_inf : ∀ w : InfinitePlace F,
      SigmaFinite (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w) :=
    sigmaFinite_inf
  have hsf_fin : ∀ v : HeightOneSpectrum (𝓞 F),
      SigmaFinite (RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v) :=
    sigmaFinite_fin
  have h1 : ∀ w : InfinitePlace F, ∀ᵐ x ∂(sAdditiveTamagawa F Sf), x.1 w ≠ 0 := by
    intro w
    have := nullSingleton_inf w
    exact Measure.quasiMeasurePreserving_fst.ae (Measure.ae_eval_ne _ w 0)
  have h2 : ∀ v : Sf, ∀ᵐ x ∂(sAdditiveTamagawa F Sf), x.2 v ≠ 0 := by
    intro v
    have := nullSingleton_fin (F := F) (v : HeightOneSpectrum (𝓞 F))
    exact Measure.quasiMeasurePreserving_snd.ae (Measure.ae_eval_ne _ v 0)
  filter_upwards [ae_all_iff.mpr h1, ae_all_iff.mpr h2] with x hx1 hx2
  rw [Prod.isUnit_iff]
  exact ⟨Pi.isUnit_iff.mpr fun w => isUnit_iff_ne_zero.mpr (hx1 w),
    Pi.isUnit_iff.mpr fun v => isUnit_iff_ne_zero.mpr (hx2 v)⟩


theorem isOpenEmbedding_pi_units_val {ι : Type*} [Finite ι] {M : ι → Type*} [∀ i, Monoid (M i)]
    [∀ i, TopologicalSpace (M i)] [∀ i, IsOpenUnits (M i)] :
    Topology.IsOpenEmbedding (fun (u : ∀ i, (M i)ˣ) (i : ι) => (u i : M i)) := by
  have h : ∀ i, Topology.IsOpenEmbedding (Units.val : (M i)ˣ → M i) :=
    fun i => IsOpenUnits.isOpenEmbedding_unitsVal
  exact ⟨Topology.IsEmbedding.piMap fun i => (h i).isEmbedding,
    (IsOpenMap.piMap (fun i => (h i).isOpenMap)
      (Filter.eventually_cofinite.mpr (Set.toFinite _))).isOpen_range⟩

noncomputable def coordEquiv : SIdeleGroup F Sf ≃*
    ((w : InfinitePlace F) → w.Completionˣ) ×
      ((v : Sf) → ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ) :=
  (MulEquiv.prodUnits (M := (w : InfinitePlace F) → w.Completion)
      (N := (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).trans
    (MulEquiv.prodCongr MulEquiv.piUnits MulEquiv.piUnits)

theorem continuous_coordEquiv : Continuous (coordEquiv Sf) :=
  ((ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F => w.Completion)).continuous.prodMap
    (ContinuousMulEquiv.piUnits
      (M := fun v : Sf => (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).continuous).comp
    (Homeomorph.prodUnits (α := (w : InfinitePlace F) → w.Completion)
      (β := (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).continuous

theorem continuous_coordEquiv_symm : Continuous (coordEquiv Sf).symm :=
  (Homeomorph.prodUnits (α := (w : InfinitePlace F) → w.Completion)
      (β := (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).symm.continuous.comp
    ((ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F => w.Completion)).symm.continuous.prodMap
      (ContinuousMulEquiv.piUnits
        (M := fun v : Sf => (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).symm.continuous)

noncomputable def coordVal (p : ((w : InfinitePlace F) → w.Completionˣ) ×
      ((v : Sf) → ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ)) : SAdeleRing F Sf :=
  (fun w => (p.1 w : w.Completion), fun v => (p.2 v : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F))

theorem isOpenEmbedding_val :
    Topology.IsOpenEmbedding (Units.val : SIdeleGroup F Sf → SAdeleRing F Sf) := by
  have h1 : Topology.IsOpenEmbedding (coordVal Sf) :=
    (isOpenEmbedding_pi_units_val (M := fun w : InfinitePlace F => w.Completion)).prodMap
      (isOpenEmbedding_pi_units_val
        (M := fun v : Sf => (v : HeightOneSpectrum (𝓞 F)).adicCompletion F))
  have h2 : Topology.IsOpenEmbedding (coordEquiv Sf) :=
    (Homeomorph.mk (coordEquiv Sf).toEquiv (continuous_coordEquiv Sf)
      (continuous_coordEquiv_symm Sf)).isOpenEmbedding
  exact h1.comp h2

instance instSCInf : SecondCountableTopology (InfiniteAdeleRing F) := by
  have := secondCountable_infinite (F := F)
  exact inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))

instance instBorelInf : BorelSpace (InfiniteAdeleRing F) := by
  have := secondCountable_infinite (F := F)
  exact inferInstanceAs (BorelSpace ((w : InfinitePlace F) → w.Completion))

instance instSCA : SecondCountableTopology (SAdeleRing F Sf) := by
  have := secondCountable_finite (F := F)
  infer_instance

instance instBorelA : BorelSpace (SAdeleRing F Sf) := by
  have := secondCountable_finite (F := F)
  infer_instance

instance instLCA : LocallyCompactSpace (SAdeleRing F Sf) := by
  have : ∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (v.adicCompletion F) :=
    fun v => RiemannMasullo.locallyCompactSpace_adicCompletion v
  infer_instance

instance instSCG : SecondCountableTopology (SIdeleGroup F Sf) :=
  (isOpenEmbedding_val Sf).isEmbedding.secondCountableTopology

instance instLCG : LocallyCompactSpace (SIdeleGroup F Sf) :=
  (isOpenEmbedding_val Sf).locallyCompactSpace

instance instSFA : SigmaFinite (sAdditiveTamagawa F Sf) := by
  have := sigmaFinite_inf (F := F)
  have := sigmaFinite_fin (F := F)
  have : SigmaFinite (infiniteAdditiveTamagawa F) :=
    inferInstanceAs
      (SigmaFinite (Measure.pi (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F)))
  unfold sAdditiveTamagawa
  infer_instance

example : MeasurableMul₂ (SIdeleGroup F Sf) := inferInstance
example : MeasurableInv (SIdeleGroup F Sf) := inferInstance
example : SFinite (sMultiplicativeTamagawa F Sf) := by
  have := (sMultiplicativeTamagawa_isHaarMeasure_and_rectangle F Sf).1
  infer_instance
example : OpensMeasurableSpace (SAdeleRing F Sf × SAdeleRing F Sf) := inferInstance


theorem sIdeleNorm_pos (g : SIdeleGroup F Sf) : 0 < sIdeleNorm Sf g := by
  have hinf : ∀ w : InfinitePlace F, (g : SAdeleRing F Sf).1 w ≠ 0 := by
    intro w
    have h := congrArg (fun x : SAdeleRing F Sf => x.1 w) g.mul_inv
    simp only [Prod.fst_mul, Prod.fst_one] at h
    exact left_ne_zero_of_mul_eq_one h
  have hfin : ∀ v : Sf, (g : SAdeleRing F Sf).2 v ≠ 0 := by
    intro v
    have h := congrArg (fun x : SAdeleRing F Sf => x.2 v) g.mul_inv
    simp only [Prod.snd_mul, Prod.snd_one] at h
    exact left_ne_zero_of_mul_eq_one h
  unfold sIdeleNorm
  exact mul_pos (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr (hinf w)) _)
    (Finset.prod_pos fun v _ => norm_pos_iff.mpr (hfin v))

/-- The constant `κ_S = ∏_{v ∈ S_f} q_v / (q_v - 1)` relating `μ_S` and `|·|⁻¹ ν_S`. -/
noncomputable def kappa : ℝ :=
  (∏ v ∈ Sf, ((Ideal.absNorm v.asIdeal : ℝ≥0∞) / ((Ideal.absNorm v.asIdeal : ℝ≥0∞) - 1))).toReal

/-- `∫_{GL₁(𝔸_S)} Φ(g) |g| dμ_S(g) = κ_S ∫_{𝔸_S} Φ dν_S` for every function `Φ`. -/
theorem integral_units_mul_norm (Φ : SAdeleRing F Sf → ℂ) :
    ∫ g : SIdeleGroup F Sf, Φ (g : SAdeleRing F Sf) * ((sIdeleNorm Sf g : ℝ) : ℂ)
        ∂(sMultiplicativeTamagawa F Sf) =
      (kappa Sf : ℂ) * ∫ x, Φ x ∂(sAdditiveTamagawa F Sf) := by
  set D : SAdeleRing F Sf → ℝ≥0∞ := fun x =>
    ((∏ w : InfinitePlace F, (‖x.1 w‖₊ : ℝ≥0∞) ^ w.mult) * ∏ v : Sf, (‖x.2 v‖₊ : ℝ≥0∞))⁻¹
    with hD
  set N' : SAdeleRing F Sf → ℝ := fun x =>
    (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) * ∏ v : Sf, ‖x.2 v‖ with hN'
  have hemb : MeasurableEmbedding (Units.val : SIdeleGroup F Sf → SAdeleRing F Sf) :=
    (isOpenEmbedding_val Sf).measurableEmbedding
  have hR : MeasurableSet (Set.range (Units.val : SIdeleGroup F Sf → SAdeleRing F Sf)) :=
    hemb.measurableSet_range
  have hDm : Measurable D := by
    simp only [hD]
    refine Measurable.inv (Measurable.mul (Finset.measurable_prod _ fun w _ => ?_)
      (Finset.measurable_prod _ fun v _ => ?_))
    · exact (measurable_coe_nnreal_ennreal.comp
        (continuous_nnnorm.measurable.comp ((measurable_pi_apply w).comp measurable_fst))).pow_const _
    · exact measurable_coe_nnreal_ennreal.comp
        (continuous_nnnorm.measurable.comp ((measurable_pi_apply v).comp measurable_snd))
  have hDreal : ∀ x, (D x).toReal = (N' x)⁻¹ := by
    intro x
    simp only [hD, hN', ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_prod,
      ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm]
  have hN'val : ∀ g : SIdeleGroup F Sf, N' (g : SAdeleRing F Sf) = sIdeleNorm Sf g := fun g => rfl
  rw [sMultiplicativeTamagawa, integral_smul_measure]
  have h1 : ∫ g : SIdeleGroup F Sf, Φ (g : SAdeleRing F Sf) * ((sIdeleNorm Sf g : ℝ) : ℂ)
        ∂(((sAdditiveTamagawa F Sf).withDensity D).comap Units.val) =
      ∫ x, Φ x * ((N' x : ℝ) : ℂ)
        ∂(((sAdditiveTamagawa F Sf).withDensity D).restrict (Set.range Units.val)) := by
    rw [← hemb.map_comap, hemb.integral_map]
    rfl
  rw [h1, restrict_withDensity hR]
  have hlt : ∀ᵐ x ∂((sAdditiveTamagawa F Sf).restrict (Set.range Units.val)), D x < ⊤ := by
    filter_upwards [ae_restrict_mem hR] with x hx
    obtain ⟨g, rfl⟩ := hx
    have h0 : (D (g : SAdeleRing F Sf)).toReal ≠ 0 := by
      rw [hDreal, hN'val]; exact inv_ne_zero (sIdeleNorm_pos Sf g).ne'
    exact lt_top_iff_ne_top.mpr (ENNReal.toReal_ne_zero.mp h0).2
  rw [integral_withDensity_eq_integral_toReal_smul hDm hlt]
  have h2 : ∫ x, (D x).toReal • (Φ x * ((N' x : ℝ) : ℂ))
        ∂((sAdditiveTamagawa F Sf).restrict (Set.range Units.val)) =
      ∫ x, Φ x ∂((sAdditiveTamagawa F Sf).restrict (Set.range Units.val)) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hR] with x hx
    obtain ⟨g, rfl⟩ := hx
    rw [hDreal, hN'val, Complex.real_smul]
    have : ((sIdeleNorm Sf g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sIdeleNorm_pos Sf g).ne'
    push_cast
    field_simp
  have hae : ∀ᵐ x ∂(sAdditiveTamagawa F Sf),
      x ∈ Set.range (Units.val : SIdeleGroup F Sf → SAdeleRing F Sf) :=
    (ae_isUnit Sf).mono fun x hx => by obtain ⟨u, hu⟩ := hx; exact ⟨u, hu⟩
  rw [h2, Measure.restrict_eq_self_of_ae_mem hae, kappa, Complex.real_smul]


/-- Fubini on `𝔸_S × 𝔸_S`: `∫ f(x) \hat h(x z) dν_S(x) = ∫ h(x) \hat f(x z) dν_S(x)`. -/
theorem integral_mul_fourier_comm (f h : SAdeleRing F Sf → ℂ)
    (hf : Integrable f (sAdditiveTamagawa F Sf)) (hh : Integrable h (sAdditiveTamagawa F Sf))
    (z : SAdeleRing F Sf) :
    ∫ x, f x * sLocalFourier Sf h (x * z) ∂(sAdditiveTamagawa F Sf) =
      ∫ x, h x * sLocalFourier Sf f (x * z) ∂(sAdditiveTamagawa F Sf) := by
  obtain ⟨-, hψ1, hψc, -⟩ := sAdditiveTamagawa_selfDual_sStdCharacter F Sf
  have hint : Integrable (Function.uncurry fun (x y : SAdeleRing F Sf) =>
      f x * h y * sStdCharacter Sf (y * (x * z)))
      ((sAdditiveTamagawa F Sf).prod (sAdditiveTamagawa F Sf)) := by
    have h1 := hf.mul_prod hh
    have hm : AEStronglyMeasurable (fun p : SAdeleRing F Sf × SAdeleRing F Sf =>
        sStdCharacter Sf (p.2 * (p.1 * z)))
        ((sAdditiveTamagawa F Sf).prod (sAdditiveTamagawa F Sf)) :=
      (hψc.comp (continuous_snd.mul (continuous_fst.mul continuous_const))).aestronglyMeasurable
    exact h1.mul_bdd hm (ae_of_all _ fun p => (hψ1 _).le)
  unfold sLocalFourier
  calc ∫ x, f x * ∫ y, h y * sStdCharacter Sf (y * (x * z)) ∂(sAdditiveTamagawa F Sf)
        ∂(sAdditiveTamagawa F Sf)
      = ∫ x, ∫ y, f x * h y * sStdCharacter Sf (y * (x * z)) ∂(sAdditiveTamagawa F Sf)
          ∂(sAdditiveTamagawa F Sf) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only
        rw [← integral_const_mul]
        simp_rw [mul_assoc]
    _ = ∫ y, ∫ x, f x * h y * sStdCharacter Sf (y * (x * z)) ∂(sAdditiveTamagawa F Sf)
          ∂(sAdditiveTamagawa F Sf) := integral_integral_swap hint
    _ = ∫ y, h y * ∫ x, f x * sStdCharacter Sf (x * (y * z)) ∂(sAdditiveTamagawa F Sf)
          ∂(sAdditiveTamagawa F Sf) := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only
        rw [mul_left_comm y x z]
        ring

/-- The kernel `K_{f,h}(b) = ∫ f(a) \hat h(a b) |a| dμ_S(a)` is symmetric in `f, h`. -/
theorem kernel_symm (f h : SAdeleRing F Sf → ℂ)
    (hf : Integrable f (sAdditiveTamagawa F Sf)) (hh : Integrable h (sAdditiveTamagawa F Sf))
    (b : SIdeleGroup F Sf) :
    ∫ a : SIdeleGroup F Sf, f (a : SAdeleRing F Sf) *
        sLocalFourier Sf h ((a : SAdeleRing F Sf) * (b : SAdeleRing F Sf)) *
        ((sIdeleNorm Sf a : ℝ) : ℂ) ∂(sMultiplicativeTamagawa F Sf) =
      ∫ a : SIdeleGroup F Sf, h (a : SAdeleRing F Sf) *
        sLocalFourier Sf f ((a : SAdeleRing F Sf) * (b : SAdeleRing F Sf)) *
        ((sIdeleNorm Sf a : ℝ) : ℂ) ∂(sMultiplicativeTamagawa F Sf) := by
  rw [integral_units_mul_norm Sf (fun x => f x * sLocalFourier Sf h (x * (b : SAdeleRing F Sf))),
    integral_units_mul_norm Sf (fun x => h x * sLocalFourier Sf f (x * (b : SAdeleRing F Sf))),
    integral_mul_fourier_comm Sf f h hf hh]


theorem sIdeleNorm_mul (g h : SIdeleGroup F Sf) :
    sIdeleNorm Sf (g * h) = sIdeleNorm Sf g * sIdeleNorm Sf h := by
  have h1 : ∀ w : InfinitePlace F, ((g * h : SIdeleGroup F Sf) : SAdeleRing F Sf).1 w =
      (g : SAdeleRing F Sf).1 w * (h : SAdeleRing F Sf).1 w := fun w => rfl
  have h2 : ∀ v : Sf, ((g * h : SIdeleGroup F Sf) : SAdeleRing F Sf).2 v =
      (g : SAdeleRing F Sf).2 v * (h : SAdeleRing F Sf).2 v := fun v => rfl
  unfold sIdeleNorm
  simp only [h1, h2, norm_mul, mul_pow, Finset.prod_mul_distrib]
  ring

theorem continuous_sIdeleNorm : Continuous (sIdeleNorm (F := F) Sf) := by
  have h1 : Continuous fun g : SIdeleGroup F Sf => (g : SAdeleRing F Sf) := Units.continuous_val
  show Continuous fun g : SIdeleGroup F Sf =>
    (∏ w : InfinitePlace F, ‖(g : SAdeleRing F Sf).1 w‖ ^ w.mult) * ∏ v : Sf, ‖(g : SAdeleRing F Sf).2 v‖
  refine Continuous.mul (continuous_finsetProd _ fun w _ => ?_)
    (continuous_finsetProd _ fun v _ => ?_)
  · exact ((continuous_apply w).comp (continuous_fst.comp h1)).norm.pow _
  · exact ((continuous_apply v).comp (continuous_snd.comp h1)).norm

theorem dual_isQC {c : SIdeleGroup F Sf → ℂ} (hc : IsSIdeleQuasiCharacter Sf c) :
    IsSIdeleQuasiCharacter Sf (sQuasiDual Sf c) := by
  obtain ⟨hcont, hmul, hne⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · unfold sQuasiDual
    exact (Complex.continuous_ofReal.comp (continuous_sIdeleNorm Sf)).mul (hcont.inv₀ hne)
  · intro g h
    unfold sQuasiDual
    rw [hmul, sIdeleNorm_mul, Complex.ofReal_mul, mul_inv]
    ring
  · intro g
    unfold sQuasiDual
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (sIdeleNorm_pos Sf g).ne') (inv_ne_zero (hne g))

theorem dual_norm {c : SIdeleGroup F Sf → ℂ} {σ : ℝ}
    (hσ : ∀ g : SIdeleGroup F Sf, ‖c g‖ = sIdeleNorm Sf g ^ σ) (g : SIdeleGroup F Sf) :
    ‖sQuasiDual Sf c g‖ = sIdeleNorm Sf g ^ (1 - σ) := by
  unfold sQuasiDual
  rw [norm_mul, norm_inv, hσ, Complex.norm_of_nonneg (sIdeleNorm_pos Sf g).le,
    Real.rpow_sub (sIdeleNorm_pos Sf g), Real.rpow_one, div_eq_mul_inv]

/-- Tate's unfolding: `Z(φ, c) Z(φ', \hat c) = ∫ K(b) \hat c(b) dμ_S(b)` with
`K(b) = ∫ φ(a) φ'(a b) |a| dμ_S(a)` (Haar invariance of `μ_S` and Fubini). -/
theorem zeta_mul_eq_kernel (c : SIdeleGroup F Sf → ℂ) (hc : IsSIdeleQuasiCharacter Sf c)
    (φ φ' : SAdeleRing F Sf → ℂ)
    (h1 : Integrable (fun g : SIdeleGroup F Sf => φ (g : SAdeleRing F Sf) * c g)
      (sMultiplicativeTamagawa F Sf))
    (h2 : Integrable (fun g : SIdeleGroup F Sf => φ' (g : SAdeleRing F Sf) * sQuasiDual Sf c g)
      (sMultiplicativeTamagawa F Sf)) :
    sZetaIntegralFun Sf φ c * sZetaIntegralFun Sf φ' (sQuasiDual Sf c) =
      ∫ b : SIdeleGroup F Sf, (∫ a : SIdeleGroup F Sf, φ (a : SAdeleRing F Sf) *
          φ' ((a : SAdeleRing F Sf) * (b : SAdeleRing F Sf)) * ((sIdeleNorm Sf a : ℝ) : ℂ)
          ∂(sMultiplicativeTamagawa F Sf)) * sQuasiDual Sf c b ∂(sMultiplicativeTamagawa F Sf) := by
  have hH := (sMultiplicativeTamagawa_isHaarMeasure_and_rectangle F Sf).1
  obtain ⟨-, hmul, hne⟩ := hc
  unfold sZetaIntegralFun
  rw [← integral_prod_mul (μ := sMultiplicativeTamagawa F Sf) (ν := sMultiplicativeTamagawa F Sf)
    (fun a : SIdeleGroup F Sf => φ (a : SAdeleRing F Sf) * c a)
    (fun b : SIdeleGroup F Sf => φ' (b : SAdeleRing F Sf) * sQuasiDual Sf c b)]
  have hmp := measurePreserving_prod_mul (sMultiplicativeTamagawa F Sf) (sMultiplicativeTamagawa F Sf)
  have hemb : MeasurableEmbedding (fun z : SIdeleGroup F Sf × SIdeleGroup F Sf => (z.1, z.1 * z.2)) :=
    (MeasurableEquiv.shearMulRight (SIdeleGroup F Sf)).measurableEmbedding
  set P : SIdeleGroup F Sf × SIdeleGroup F Sf → ℂ := fun z =>
    (φ (z.1 : SAdeleRing F Sf) * c z.1) * (φ' (z.2 : SAdeleRing F Sf) * sQuasiDual Sf c z.2) with hP
  have hPi : Integrable P ((sMultiplicativeTamagawa F Sf).prod (sMultiplicativeTamagawa F Sf)) :=
    h1.mul_prod h2
  have hPT : Integrable (fun z : SIdeleGroup F Sf × SIdeleGroup F Sf => P (z.1, z.1 * z.2))
      ((sMultiplicativeTamagawa F Sf).prod (sMultiplicativeTamagawa F Sf)) :=
    (hmp.integrable_comp_emb hemb).mpr hPi
  rw [← hmp.integral_comp hemb, integral_prod_symm _ hPT]
  refine integral_congr_ae (ae_of_all _ fun b => ?_)
  simp only
  rw [← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  simp only [hP, Units.val_mul, sQuasiDual, hmul, sIdeleNorm_mul, Complex.ofReal_mul]
  have ha := hne a
  have hb := hne b
  field_simp

end Sol_MasulloGRH_sZetaIntegral_mul_fourier_symm

open MasulloGRH Sol_MasulloGRH_sZetaIntegral_mul_fourier_symm

theorem solution
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (c : SIdeleGroup F Sf → ℂ) (hc : IsSIdeleQuasiCharacter Sf c)
    (σ : ℝ) (hσ : ∀ g : SIdeleGroup F Sf, ‖c g‖ = sIdeleNorm Sf g ^ σ)
    (h0 : 0 < σ) (h1 : σ < 1) (f h : SAdelicSchwartz F Sf) :
    sZetaIntegral f c * sZetaIntegralFun Sf (sLocalFourier Sf h.eval) (sQuasiDual Sf c) =
      sZetaIntegral h c * sZetaIntegralFun Sf (sLocalFourier Sf f.eval) (sQuasiDual Sf c) := by
  obtain ⟨hint, T, hT, -⟩ := sLocalFourier_schwartzBruhat_equiv F Sf
  have hdc := dual_isQC Sf hc
  have hdn := dual_norm Sf hσ
  have hI1 : ∀ φ : SAdelicSchwartz F Sf, Integrable
      (fun g : SIdeleGroup F Sf => φ.eval (g : SAdeleRing F Sf) * c g)
      (sMultiplicativeTamagawa F Sf) := by
    intro φ
    have := (sZetaIntegral_integrable_and_differentiableOn F Sf φ c hc σ hσ).1 0 (by simpa using h0)
    simpa [sQuasiTwist] using this
  have hI2 : ∀ φ : SAdelicSchwartz F Sf, Integrable
      (fun g : SIdeleGroup F Sf => sLocalFourier Sf φ.eval (g : SAdeleRing F Sf) *
        sQuasiDual Sf c g) (sMultiplicativeTamagawa F Sf) := by
    intro φ
    have := (sZetaIntegral_integrable_and_differentiableOn F Sf (T φ) _ hdc (1 - σ) hdn).1 0
      (by simp only [Complex.zero_re, add_zero]; linarith)
    rw [hT] at this
    simpa [sQuasiTwist] using this
  unfold sZetaIntegral
  rw [zeta_mul_eq_kernel Sf c hc _ _ (hI1 f) (hI2 h), zeta_mul_eq_kernel Sf c hc _ _ (hI1 h) (hI2 f)]
  refine integral_congr_ae (ae_of_all _ fun b => ?_)
  simp only
  rw [kernel_symm Sf f.eval h.eval (hint f) (hint h) b]
