-- Prove2me | solution 1 for LanglandsTunnell.HeckeTate.isNicePinned_heckeDatum_mul_comp_idelicNorm_of_not_exists_eq_pow_inertiaDeg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/41c67c13-547c-5c53-b31e-c400ff3256a8

import Mathlib.NumberTheory.RamificationInertia.Basic
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
import Theorems.Thm_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
import Theorems.Thm_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
import Theorems.Thm_LanglandsTunnell_Converse_isArchCompAt_comp_idelicNorm_genuineBaseChange
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_NumberField_NormPowChar
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Theorems.Thm_LanglandsTunnell_HeckeTate_isNicePinned_heckeDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_HeckeTate_isNicePinned_heckeDatum_mul_comp_idelicNorm_of_not_exists_eq_pow_inertiaDeg
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed"

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal
open LanglandsTunnell.Converse LanglandsTunnell.HeckeTate

private theorem algebra_ringOfIntegers_rat_eq (K : Type) [Field K] [NumberField K]
    (inst : Algebra (𝓞 ℚ) (𝓞 K)) : inst = NumberField.inst_ringOfIntegersAlgebra ℚ K := by
  refine Algebra.algebra_ext _ _ fun r => ?_
  have huniq : ∀ f g : 𝓞 ℚ →+* 𝓞 K, f = g := fun f g => by
    have h1 : f.comp Rat.ringOfIntegersEquiv.symm.toRingHom = g.comp Rat.ringOfIntegersEquiv.symm.toRingHom :=
      Subsingleton.elim _ _
    have h2 := congrArg (fun φ : ℤ →+* 𝓞 K => φ.comp Rat.ringOfIntegersEquiv.toRingHom) h1
    simp only [RingHom.comp_assoc, RingEquiv.symm_toRingHom_comp_toRingHom, RingHom.comp_id] at h2
    exact h2
  exact RingHom.congr_fun
    (huniq (@algebraMap _ _ _ _ inst) (@algebraMap _ _ _ _ (NumberField.inst_ringOfIntegersAlgebra ℚ K))) r

private theorem char_localUnit_eq_one_of_isUnramifiedCharAt (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (hχ : IsUnramifiedCharAt χ p) (t : (p.adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : p.adicCompletion ℚ) = 1) :
    χ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ) (NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ p t)) = 1 := by
  have hinv : Valued.v ((t⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1 := by
    have h := congrArg Valued.v (Units.mul_inv t)
    rwa [map_mul, ht, one_mul, map_one] at h
  have h1 : (t : p.adicCompletion ℚ) ∈ p.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact ht.le
  have h2 : ((t⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) ∈ p.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hinv.le
  exact hχ t h1 h2

private theorem isAdmissibleTwist_mul (F : Type) [Field F] [NumberField F]
    {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsAdmissibleTwist F μ) (hν : IsAdmissibleTwist F ν) :
    IsAdmissibleTwist F (μ * ν) := by
  obtain ⟨hμ₁, hμc, hμu⟩ := hμ
  obtain ⟨hν₁, hνc, hνu⟩ := hν
  refine ⟨fun u => ?_, ?_, fun x => ?_⟩
  · rw [MonoidHom.mul_apply, hμ₁ u, hν₁ u, one_mul]
  · show Continuous fun x => μ x * ν x
    exact hμc.mul hνc
  · rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hμu x, hνu x, one_mul]

private theorem isAdmissibleTwist_inv (F : Type) [Field F] [NumberField F]
    {μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsAdmissibleTwist F μ) : IsAdmissibleTwist F μ⁻¹ := by
  obtain ⟨hμ₁, hμc, hμu⟩ := hμ
  refine ⟨fun u => ?_, ?_, fun x => ?_⟩
  · rw [MonoidHom.inv_apply, hμ₁ u, inv_one]
  · show Continuous fun x => (μ x)⁻¹
    exact hμc.inv
  · rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hμu x, inv_one]

private theorem continuous_idelicNorm (K : Type) [Field K] [NumberField K] :
    Continuous (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange ℚ K).comp Units.continuous_val
  · exact (M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange ℚ K).comp Units.continuous_coe_inv

private theorem idelicNorm_map_algebraMap (K : Type) [Field K] [NumberField K] (u : Kˣ) :
    (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u) =
      Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) (Units.map (Algebra.norm ℚ : K →* ℚ) u) := by
  ext
  exact M4aHerbrand.GenuineDescent.adelicNorm_genuineBaseChange_algebraMap ℚ K (u : K)

private theorem isAdmissibleTwist_comp_idelicNorm (K : Type) [Field K] [NumberField K]
    {τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ} (hτ : IsAdmissibleTwist ℚ τ) :
    IsAdmissibleTwist K (τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) := by
  obtain ⟨hτ₁, hτc, hτu⟩ := hτ
  refine ⟨fun u => ?_, ?_, fun x => ?_⟩
  · rw [MonoidHom.comp_apply, idelicNorm_map_algebraMap, hτ₁]
  · show Continuous fun x => τ ((M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm x)
    exact hτc.comp (continuous_idelicNorm K)
  · rw [MonoidHom.comp_apply]
    exact hτu _

private theorem ideleNorm_map_algebraMap_eq_one (F : Type) [Field F] [NumberField F] (u : Fˣ) :
    ideleNorm F (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) u) = 1 := by
  have h := ideleNorm_det_globalPoints (Matrix.GeneralLinearGroup.scalar (Fin 2) u)
  have hdet : Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) =
      Units.map (algebraMap F (AdeleRing (𝓞 F) F)) u * Units.map (algebraMap F (AdeleRing (𝓞 F) F)) u := by
    ext
    simp [globalPoints, Matrix.GeneralLinearGroup.scalar, pow_two]
  rw [hdet, ideleNorm_mul] at h
  have hpos : 0 < ideleNorm F (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) u) := ideleNorm_pos _
  exact (mul_self_eq_one_iff.1 h).resolve_right (by intro h1; linarith)

private theorem isAdmissibleTwist_normPowChar (F : Type) [Field F] [NumberField F] (t : ℝ) :
    IsAdmissibleTwist F (normPowChar F t) := by
  refine ⟨fun u => normPowChar_eq_one_of_ideleNorm_eq_one t (ideleNorm_map_algebraMap_eq_one F u), ?_,
    fun x => norm_coe_normPowChar_apply t x⟩
  have hc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ideleNorm F x : ℝ) : ℂ) ^ (Complex.I * t) :=
    (Complex.continuous_ofReal.comp (continuous_ideleNorm F)).cpow continuous_const
      fun x => Complex.ofReal_mem_slitPlane.2 (ideleNorm_pos x)
  refine Units.continuous_iff.2 ⟨hc, ?_⟩
  show Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => (((ideleNorm F x : ℝ) : ℂ) ^ (Complex.I * t))⁻¹
  exact hc.inv₀ fun x => ofReal_ideleNorm_cpow_ne_zero F x _

private theorem normPowChar_isUnramifiedCharAt_and_apply_uniformizerIdele (F : Type) [Field F] [NumberField F]
    (t : ℝ) (v : HeightOneSpectrum (𝓞 F)) :
    IsUnramifiedCharAt (normPowChar F t) v ∧
      ((normPowChar F t (uniformizerIdele F v) : ℂˣ) : ℂ) =
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * t)) := by
  have h := ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg F t v
  have hne : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * t)) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and]
    intro h0
    exfalso
    have h1 : Ideal.absNorm v.asIdeal = 0 := by exact_mod_cast h0
    exact v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h1)
  by_cases hu : IsUnramifiedCharAt (normPowChar F t) v
  · rw [if_pos hu] at h
    exact ⟨hu, h⟩
  · rw [if_neg hu] at h
    exact absurd h.symm hne

private theorem isArchCompAt_mul (F : Type) [Field F] [NumberField F] {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (w : InfinitePlace F) {u u' : ℂ} {a a' : ℤ} (hμ : IsArchCompAt F μ w u a) (hν : IsArchCompAt F ν w u' a') :
    IsArchCompAt F (μ * ν) w (u + u') (a + a') := by
  intro x
  have hx : ((‖(x : w.Completion)‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.2 x.ne_zero
  have he : InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) / ((‖(x : w.Completion)‖ : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero ((map_ne_zero _).2 x.ne_zero) hx
  have hmul : ((archLocalChar (μ * ν) w x : ℂˣ) : ℂ) = (archLocalChar μ w x : ℂ) * (archLocalChar ν w x : ℂ) := by
    simp only [archLocalChar, MonoidHom.mul_comp, MonoidHom.mul_apply, Units.val_mul]
  rw [hmul, hμ x, hν x, mul_add, Complex.cpow_add _ _ hx, zpow_add₀ he]
  ring

private theorem isArchCompAt_of_int_modEq (F : Type) [Field F] [NumberField F] (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    {w : InfinitePlace F} (hw : w.IsReal) {u : ℂ} {a a' : ℤ} (hmod : a ≡ a' [ZMOD 2])
    (h : IsArchCompAt F μ w u a) : IsArchCompAt F μ w u a' := by
  intro x
  rw [h x]
  have hr0 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (x : w.Completion) ≠ 0 :=
    (map_ne_zero _).2 x.ne_zero
  have hz : InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) / ((‖(x : w.Completion)‖ : ℝ) : ℂ) =
      ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (x : w.Completion) /
        |InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (x : w.Completion)| : ℝ) : ℂ) := by
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, Complex.ofReal_div, ← Real.norm_eq_abs,
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _)]
  have hsq : (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) /
      ((‖(x : w.Completion)‖ : ℝ) : ℂ)) ^ (2 : ℤ) = 1 := by
    rw [hz, zpow_two, ← Complex.ofReal_mul, div_mul_div_comm, ← sq, ← sq, sq_abs, div_self (pow_ne_zero 2 hr0),
      Complex.ofReal_one]
  obtain ⟨m, hm⟩ := hmod.dvd
  have hne : InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) /
      ((‖(x : w.Completion)‖ : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0, zero_zpow 2 two_ne_zero] at hsq
    exact zero_ne_one hsq
  rw [show a' = a + 2 * m by omega, zpow_add₀ hne, zpow_mul, hsq, one_zpow, mul_one]

private theorem isArchCompAt_mul_comp_idelicNorm_of_isReal (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) {t : ℂ} {e : ℤ}
    (hτinf : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ τ v t e) {w : InfinitePlace K} (hw : w.IsReal)
    {u : ℂ} {a : ZMod 2} (hμ : IsArchCompAt K μ w u (a.val : ℤ)) :
    IsArchCompAt K (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w (u + t)
      ((a + (e : ZMod 2)).val : ℤ) := by
  have hτw : IsArchCompAt K (τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w t e :=
    (isArchCompAt_comp_idelicNorm_genuineBaseChange ℚ K τ w t).1 hw e (hτinf _ (IsTotallyReal.isReal _))
  refine isArchCompAt_of_int_modEq K _ hw ?_ (isArchCompAt_mul K w hμ hτw)
  exact (ZMod.intCast_eq_intCast_iff _ _ 2).1 (by push_cast [ZMod.natCast_zmod_val]; rfl)

private theorem isArchCompAt_mul_comp_idelicNorm_of_isComplex (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) {t : ℂ} {e : ℤ}
    (hτinf : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ τ v t e) {w : InfinitePlace K} (hw : w.IsComplex)
    {u : ℂ} {k : ℤ} (hμ : IsArchCompAt K μ w u k) :
    IsArchCompAt K (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w (u + t) k := by
  have hτw : IsArchCompAt K (τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w t 0 :=
    (isArchCompAt_comp_idelicNorm_genuineBaseChange ℚ K τ w t).2.1 hw (IsTotallyReal.isReal _) e
      (hτinf _ (IsTotallyReal.isReal _))
  have h := isArchCompAt_mul K w hμ hτw
  rwa [add_zero] at h

private theorem exists_mem_normOneIdeles_mul_comp_idelicNorm_ne_one (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hτ : IsAdmissibleTwist ℚ τ) :
    ∃ x ∈ normOneIdeles K, (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hadm : IsAdmissibleTwist K (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) :=
    isAdmissibleTwist_mul K hμ (isAdmissibleTwist_comp_idelicNorm K hτ)
  obtain ⟨t₀, ht₀⟩ := exists_eq_normPowChar_of_forall_mem_normOneIdeles K _ hadm.2.1 hadm.2.2 hcon
  refine hns ⟨normPowChar ℚ t₀ * τ⁻¹, isAdmissibleTwist_mul ℚ (isAdmissibleTwist_normPowChar ℚ t₀)
    (isAdmissibleTwist_inv ℚ hτ), fun 𝔓 _ hη => ?_⟩
  obtain ⟨s, hs₁, hs⟩ := M4aHerbrand.exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit ℚ K 𝔓
  have hnK := normPowChar_isUnramifiedCharAt_and_apply_uniformizerIdele K t₀ 𝔓
  have hnQ := normPowChar_isUnramifiedCharAt_and_apply_uniformizerIdele ℚ t₀ (𝔓.under (𝓞 ℚ))
  have hτs : τ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ)
      (NumberField.AdelicLevel.localUnit (𝓞 ℚ) ℚ (𝔓.under (𝓞 ℚ)) s)) = 1 := by
    have h₁ := char_localUnit_eq_one_of_isUnramifiedCharAt _ _ hnQ.1 s hs₁
    have h₂ := char_localUnit_eq_one_of_isUnramifiedCharAt _ _ hη s hs₁
    rwa [MonoidHom.mul_apply, MonoidHom.inv_apply, h₁, one_mul, inv_eq_one] at h₂
  have hμ𝔓 : μ (uniformizerIdele K 𝔓) =
      normPowChar K t₀ (uniformizerIdele K 𝔓) *
        (τ (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal)⁻¹ := by
    have h := congrArg (fun ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ => ψ (uniformizerIdele K 𝔓)) ht₀
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply] at h
    rw [hs, map_mul, map_pow, hτs, mul_one] at h
    rw [← h, mul_inv_cancel_right]
  haveI : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
  have habs : Ideal.absNorm 𝔓.asIdeal =
      Ideal.absNorm (𝔓.under (𝓞 ℚ)).asIdeal ^ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal :=
    Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔓.asIdeal (𝔓.under (𝓞 ℚ)).asIdeal (𝔓.under (𝓞 ℚ)).isPrime
      (𝔓.under (𝓞 ℚ)).ne_bot
  have harg₁ : -Real.pi < ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal : ℝ) *
      ((Ideal.absNorm (𝔓.under (𝓞 ℚ)).asIdeal : ℕ) : ℂ).arg := by
    rw [Complex.natCast_arg, mul_zero]
    exact neg_neg_of_pos Real.pi_pos
  have harg₂ : ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal : ℝ) *
      ((Ideal.absNorm (𝔓.under (𝓞 ℚ)).asIdeal : ℕ) : ℂ).arg ≤ Real.pi := by
    rw [Complex.natCast_arg, mul_zero]
    exact Real.pi_pos.le
  rw [hμ𝔓, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hnK.2, hnQ.2, habs, Nat.cast_pow,
    ← Complex.cpow_nat_mul' harg₁ harg₂, Complex.cpow_nat_mul, mul_pow, inv_pow]

open LanglandsTunnell LanglandsTunnell.HeckeTate in
theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hτ : IsAdmissibleTwist ℚ τ) (t : ℂ) (e : ℤ)
    (hτinf : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ τ v t e) :
    IsNicePinned
      (heckeDatum K (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
        (fun w hw => uR w hw + t) (fun w hw => aR w hw + (e : ZMod 2)) (fun w hw => uC w hw + t) kC)
      (fun _ => 1) (fun _ => 1)
      (heckeRootNumber K (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
        (fun w hw => aR w hw + (e : ZMod 2)) kC)
      (heckeConductor K (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)) := by
  obtain rfl := algebra_ringOfIntegers_rat_eq K ‹Algebra (𝓞 ℚ) (𝓞 K)›
  exact isNicePinned_heckeDatum K _ (isAdmissibleTwist_mul K hμ (isAdmissibleTwist_comp_idelicNorm K hτ))
    (exists_mem_normOneIdeles_mul_comp_idelicNorm_ne_one K μ hμ hns τ hτ) _ _ _ _
    (fun w hw => isArchCompAt_mul_comp_idelicNorm_of_isReal K μ τ hτinf hw (huR w hw))
    (fun w hw => isArchCompAt_mul_comp_idelicNorm_of_isComplex K μ τ hτinf hw (huC w hw))

end S_LanglandsTunnell_HeckeTate_isNicePinned_heckeDatum_mul_comp_idelicNorm_of_not_exists_eq_pow_inertiaDeg
end P2MW
export P2MW.S_LanglandsTunnell_HeckeTate_isNicePinned_heckeDatum_mul_comp_idelicNorm_of_not_exists_eq_pow_inertiaDeg (solution)
