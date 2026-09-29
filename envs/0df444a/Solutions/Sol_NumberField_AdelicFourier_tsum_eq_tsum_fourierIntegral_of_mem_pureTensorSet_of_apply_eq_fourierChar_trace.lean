-- Prove2me | solution 1 for NumberField.AdelicFourier.tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0334c7e6-ce4f-52f8-b96d-4b15efe7ef21

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing
import Theorems.Thm_NumberField_AdelicFourier_addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace
import Theorems.Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual
import Theorems.Thm_NumberField_mixedEmbedding_coe_dualSubmodule_flip_traceForm_idealLattice
import Theorems.Thm_NumberField_mixedEmbedding_trace_mixedEmbedding
import Theorems.Thm_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate
import Theorems.Thm_NumberField_AdelicBox_algebraMap_mem_image_integralFiniteAdeles_iff
import Theorems.Thm_NumberField_AdelicBox_absNorm_mul_measure_image_integralFiniteAdeles
import Theorems.Thm_NumberField_AdelicBox_exists_eq_sum_indicator_image_integralFiniteAdeles
import Theorems.Thm_NumberField_AdelicBox_isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles
import Theorems.Thm_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule
import Theorems.Thm_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
import Theorems.Thm_NumberField_AdelicFourier_summable_comp_algebraMap_of_mem_pureTensorSet
import Theorems.Thm_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

set_option maxHeartbeats 6400000 in

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (hμB : μ (AdelicBox.adelicBox F) = 1)
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    ∑' ξ : F, f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = ∑' ξ : F, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  classical

  obtain ⟨g, h, hlc, hcs, rfl⟩ := hf
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  let ν : Measure (FiniteAdeleRing (𝓞 F) F) := Measure.addHaar
  have hψu : ∀ x, ‖ψ x‖ = 1 := norm_apply_eq_one_of_isGlobalAddChar F hψ

  obtain ⟨d, hd, s, c, hdec⟩ := exists_eq_sum_indicator_image_integralFiniteAdeles F hlc hcs
  subst hdec

  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let S : F → Set (FiniteAdeleRing (𝓞 F) F) := fun k =>
    (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
        + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F
  let fk : F → AdeleRing (𝓞 F) F → ℂ := fun k x =>
    g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * (S k).indicator 1 x.2
  have hS : ∀ k, IsLocallyConstant ((S k).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) ∧
      HasCompactSupport ((S k).indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ)) := fun k =>
    isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles F d hd k
  have hfk_mem : ∀ k, fk k ∈ pureTensorSet F := fun k =>
    tensor_mem_pureTensorSet g _ (hS k).1 (hS k).2
  have hf_pt : ∀ x : AdeleRing (𝓞 F) F,
      g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * (∑ k ∈ s, c k • ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1) x.2
        = ∑ k ∈ s, c k * fk k x := by
    intro x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, fk]
    exact Finset.sum_congr rfl fun k _ => by ring

  have hInt : ∀ k (w : AdeleRing (𝓞 F) F),
      Integrable (fun v => ψ (-(v * w)) * fk k v) μ := by
    intro k w
    have h1 : Integrable (fk k) μ :=
      integrable_of_mem_schwartzBruhat F μ (mem_schwartzBruhat_of_mem_pureTensorSet (hfk_mem k))
    refine h1.norm.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
    · exact ((hψ.continuous.comp ((continuous_id.mul continuous_const).neg)).aestronglyMeasurable).mul
        h1.aestronglyMeasurable
    · rw [norm_mul, hψu, one_mul]

  have hR : ∀ w, fourierIntegral ψ μ
        (fun x => g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * (∑ k ∈ s, c k • ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1) x.2) w
      = ∑ k ∈ s, c k * fourierIntegral ψ μ (fk k) w := by
    intro w
    simp only [fourierIntegral_def]
    have : (fun v : AdeleRing (𝓞 F) F => ψ (-(v * w)) *
        (g (InfiniteAdeleRing.ringEquiv_mixedSpace F v.1) * (∑ k ∈ s, c k • ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1) v.2))
        = fun v => ∑ k ∈ s, c k * (ψ (-(v * w)) * fk k v) := by
      funext v; rw [hf_pt v, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, integral_finsetSum _ (fun k _ => (hInt k w).const_mul (c k))]
    simp only [integral_const_mul]

  have hsumL : ∀ k, Summable fun ξ : F => fk k (algebraMap F (AdeleRing (𝓞 F) F) ξ) := fun k =>
    summable_comp_algebraMap_of_mem_pureTensorSet (hfk_mem k)

  suffices hcore : ∀ k : F,
      Summable (fun ξ : F => fourierIntegral ψ μ (fk k) (algebraMap F (AdeleRing (𝓞 F) F) ξ)) ∧
      ∑' ξ : F, fk k (algebraMap F (AdeleRing (𝓞 F) F) ξ)
        = ∑' ξ : F, fourierIntegral ψ μ (fk k) (algebraMap F (AdeleRing (𝓞 F) F) ξ) by
    calc ∑' ξ : F, (fun x => g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * (∑ k ∈ s, c k • ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1) x.2)
              (algebraMap F (AdeleRing (𝓞 F) F) ξ)
        = ∑' ξ : F, ∑ k ∈ s, c k * fk k (algebraMap F (AdeleRing (𝓞 F) F) ξ) :=
          tsum_congr fun ξ => hf_pt _
      _ = ∑ k ∈ s, ∑' ξ : F, c k * fk k (algebraMap F (AdeleRing (𝓞 F) F) ξ) :=
          Summable.tsum_finsetSum fun k _ => (hsumL k).mul_left (c k)
      _ = ∑ k ∈ s, c k * ∑' ξ : F, fourierIntegral ψ μ (fk k) (algebraMap F (AdeleRing (𝓞 F) F) ξ) :=
          Finset.sum_congr rfl fun k _ => by rw [tsum_mul_left, (hcore k).2]
      _ = ∑ k ∈ s, ∑' ξ : F, c k * fourierIntegral ψ μ (fk k) (algebraMap F (AdeleRing (𝓞 F) F) ξ) :=
          Finset.sum_congr rfl fun k _ => by rw [tsum_mul_left]
      _ = ∑' ξ : F, ∑ k ∈ s, c k * fourierIntegral ψ μ (fk k) (algebraMap F (AdeleRing (𝓞 F) F) ξ) :=
          (Summable.tsum_finsetSum fun k _ => (hcore k).1.mul_left (c k)).symm
      _ = _ := tsum_congr fun ξ => (hR _).symm

  intro k

  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  let V := mixedEmbedding.mixedSpace F
  let σ : F →+* V := mixedEmbedding F
  let Bt : LinearMap.BilinForm ℝ V := Algebra.traceForm ℝ V
  have hBt : Bt.Nondegenerate := mixedEmbedding.traceForm_mixedSpace_nondegenerate F
  let I : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
    Units.mk0 (FractionalIdeal.spanSingleton (𝓞 F)⁰ (d : F))
      (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])
  have hIval : (I : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ (d : F) := rfl
  let L : Submodule ℤ V := mixedEmbedding.idealLattice F I
  let Ld : Submodule ℤ V := LinearMap.BilinForm.dualSubmodule Bt.flip L
  let t : V := σ k
  let ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
    ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  have hψf_apply : ∀ y, ψf y = ψ (0, y) := fun y => rfl
  have hψf_cont : Continuous ψf := by
    show Continuous fun y => ψ ((0 : InfiniteAdeleRing F), y)
    exact hψ.continuous.comp (continuous_const.prodMk continuous_id)
  let ψV : AddChar V ℂ :=
    ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom)
  have hψV_apply : ∀ v : V, ψV v = ψ ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm v, 0) :=
    fun v => rfl
  let P : F → Prop := fun ξ => (d : F) * ξ ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)
  have hE : ∀ ξ : F, InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (InfiniteAdeleRing F) ξ) = σ ξ :=
    fun ξ => (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm
  have hι1 : ∀ ξ : F, (algebraMap F (AdeleRing (𝓞 F) F) ξ).1 = algebraMap F (InfiniteAdeleRing F) ξ :=
    fun ξ => rfl
  have hι2 : ∀ ξ : F, (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 = algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ :=
    fun ξ => rfl

  have hν0 : ν (integralFiniteAdeles (𝓞 F) F) ≠ 0 :=
    (isOpen_integralFiniteAdeles F).measure_ne_zero ν ⟨0, fun v => (v.adicCompletionIntegers F).zero_mem⟩
  have hνtop : ν (integralFiniteAdeles (𝓞 F) F) ≠ ⊤ := (isCompact_integralFiniteAdeles F).measure_lt_top.ne
  have hνreal : (ν (integralFiniteAdeles (𝓞 F) F)).toReal ≠ 0 := (ENNReal.toReal_pos hν0 hνtop).ne'
  have hIDX : (Ideal.absNorm (Ideal.span {d}) : ℝ) * (ν (S k)).toReal
      = (ν (integralFiniteAdeles (𝓞 F) F)).toReal := by
    have h := congrArg ENNReal.toReal (absNorm_mul_measure_image_integralFiniteAdeles F ν d hd k)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
  have hNpos : (0 : ℝ) < Ideal.absNorm (Ideal.span {d}) := by
    have : Ideal.absNorm (Ideal.span ({d} : Set (𝓞 F))) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd
    positivity
  have hcovΛ : 0 < ZLattice.covolume (mixedEmbedding.integerLattice F) volume := ZLattice.covolume_pos _ _
  have hNI : (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℝ) = Ideal.absNorm (Ideal.span {d}) := by
    have hq : FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F)
        = (Ideal.absNorm (Ideal.span {d}) : ℚ) := by
      rw [hIval, FractionalIdeal.absNorm_span_singleton, Ideal.absNorm_span_singleton,
        Nat.cast_natAbs, Int.cast_abs, Algebra.coe_norm_int]
    rw [hq]; push_cast; rfl
  have hcovI : ZLattice.covolume L volume
      = (Ideal.absNorm (Ideal.span {d}) : ℝ) * ZLattice.covolume (mixedEmbedding.integerLattice F) volume := by
    rw [mixedEmbedding.covolume_idealLattice, mixedEmbedding.covolume_integerLattice, ← mul_assoc, hNI]
  have hcovL : 0 < ZLattice.covolume L volume := ZLattice.covolume_pos _ _

  have hconst : (μ (adelicBox F)).toReal /
        (ZLattice.covolume (mixedEmbedding.integerLattice F) volume * (ν (integralFiniteAdeles (𝓞 F) F)).toReal)
        * (ν (S k)).toReal = (ZLattice.covolume L volume)⁻¹ := by
    have hνS : (ν (S k)).toReal ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hIDX; exact hνreal hIDX.symm
    rw [show μ (adelicBox F) = 1 from hμB, ENNReal.toReal_one, hcovI, ← hIDX]
    field_simp

  have hV : ∀ w' : V, fourierIntegral ψV volume (g : V → ℂ) w'
      = VectorFourier.fourierIntegral 𝐞 volume Bt g w' := by
    intro w'
    rw [fourierIntegral_def]
    show _ = ∫ v, 𝐞 (-(Bt v w')) • g v
    congr 1; funext v
    rw [Circle.smul_def, smul_eq_mul, hψV_apply, hψ_inf, RingEquiv.apply_symm_apply, map_neg]
    rfl

  have hphase : ∀ ξ : F, ψf (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) (k * ξ)))
      = (𝐞 ((Algebra.trace ℚ F (k * ξ) : ℚ) : ℝ) : ℂ) := by
    intro ξ
    rw [hψf_apply, ← map_neg,
      addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace F hψ hψ_inf (-(k * ξ))]
    simp only [map_neg, Rat.cast_neg, neg_neg]
  have hcond : ∀ ξ : F, (∀ z ∈ integralFiniteAdeles (𝓞 F) F,
      ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F) * ξ) * z) = 1) ↔ P ξ :=
    fun ξ => forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual F hψ hψ_inf ((d : F) * ξ)

  let G : F → ℂ := fun ξ =>
    VectorFourier.fourierIntegral 𝐞 volume Bt g (σ ξ) * (𝐞 ((Algebra.trace ℚ F (k * ξ) : ℚ) : ℝ) : ℂ)
  have hstar : ∀ ξ : F, fourierIntegral ψ μ (fk k) (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = (ZLattice.covolume L volume : ℂ)⁻¹ * {ξ | P ξ}.indicator G ξ := by
    intro ξ
    have hT := fourierIntegral_pureTensor_eq F μ ν hψ.continuous hψu g (hS k).1 (hS k).2
      (algebraMap F (AdeleRing (𝓞 F) F) ξ)
    have hF := fourierIntegral_indicator_principalCoset_finiteAdeleRing F ν hψf_cont d hd k ξ
    rw [show fk k = fun x => g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * (S k).indicator 1 x.2 from rfl,
      hT, hι1, hι2, hE, hV, hF]
    have hsc : ((μ (adelicBox F)).toReal /
        (ZLattice.covolume (mixedEmbedding.integerLattice F) volume *
          (ν (integralFiniteAdeles (𝓞 F) F)).toReal) : ℂ) * ((ν (S k)).toReal : ℂ)
        = ((ZLattice.covolume L volume : ℝ) : ℂ)⁻¹ := by
      have h := congrArg (fun r : ℝ => (r : ℂ)) hconst
      push_cast at h
      exact h
    by_cases hP : P ξ
    · rw [if_pos ((hcond ξ).mpr hP), Set.indicator_of_mem (show ξ ∈ {ξ | P ξ} from hP), hphase, ← hsc]
      simp only [G]
      ring
    · rw [if_neg (fun h' => hP ((hcond ξ).mp h')), Set.indicator_of_notMem (show ξ ∉ {ξ | P ξ} from hP)]
      simp

  haveI : DiscreteTopology L := inferInstanceAs (DiscreteTopology (mixedEmbedding.idealLattice F I))
  haveI : IsZLattice ℝ L := inferInstanceAs (IsZLattice ℝ (mixedEmbedding.idealLattice F I))
  have hmemL : ∀ x : V, x ∈ L ↔ ∃ a : 𝓞 F, σ ((d : F) * a) = x := by
    intro x
    show x ∈ mixedEmbedding.idealLattice F I ↔ _
    rw [mixedEmbedding.mem_idealLattice]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ (I : FractionalIdeal (𝓞 F)⁰ F) := hy
      rw [hIval, FractionalIdeal.mem_spanSingleton] at hy'
      obtain ⟨z, rfl⟩ := hy'
      exact ⟨z, by rw [Algebra.smul_def, mul_comm, RingOfIntegers.coe_eq_algebraMap]⟩
    · rintro ⟨a, rfl⟩
      refine ⟨(d : F) * a, ?_, rfl⟩
      show (d : F) * a ∈ (I : FractionalIdeal (𝓞 F)⁰ F)
      rw [hIval, FractionalIdeal.mem_spanSingleton]
      exact ⟨a, by rw [Algebra.smul_def, mul_comm, RingOfIntegers.coe_eq_algebraMap]⟩
  have hinjL : Function.Injective fun a : 𝓞 F => σ ((d : F) * a) := by
    intro a b hab
    have h1 : (d : F) * a = (d : F) * b := mixedEmbedding_injective F hab
    exact RingOfIntegers.eq_iff.mp (mul_left_cancel₀ hd' h1)
  let EL : 𝓞 F ≃ L := Equiv.ofBijective (fun a => ⟨σ ((d : F) * a), (hmemL _).2 ⟨a, rfl⟩⟩)
    ⟨fun a b hab => hinjL (congrArg Subtype.val hab), fun x => by
      obtain ⟨a, ha⟩ := (hmemL x).1 x.2
      exact ⟨a, Subtype.ext ha⟩⟩
  have hEL : ∀ a : 𝓞 F, ((EL a : L) : V) = σ ((d : F) * a) := fun a => rfl

  have hdualI : ∀ ξ : F, ξ ∈ FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 F)⁰ F) ↔ P ξ := by
    intro ξ
    have hI0 : (I : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := I.ne_zero
    have h10 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := one_ne_zero
    show _ ↔ (d : F) * ξ ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)
    rw [FractionalIdeal.mem_dual hI0, FractionalIdeal.mem_dual h10]
    constructor
    · intro H b hb
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hb
      have hmem : algebraMap (𝓞 F) F r * (d : F) ∈ (I : FractionalIdeal (𝓞 F)⁰ F) := by
        rw [hIval, FractionalIdeal.mem_spanSingleton]; exact ⟨r, by rw [Algebra.smul_def]⟩
      have := H _ hmem
      simp only [Algebra.traceForm_apply] at this ⊢
      convert this using 2; ring
    · intro H a ha
      rw [hIval, FractionalIdeal.mem_spanSingleton] at ha
      obtain ⟨r, rfl⟩ := ha
      have := H (algebraMap (𝓞 F) F r) ((FractionalIdeal.mem_one_iff _).2 ⟨r, rfl⟩)
      simp only [Algebra.traceForm_apply, Algebra.smul_def] at this ⊢
      convert this using 2; ring
  have hmemD : ∀ y : V, y ∈ Ld ↔ ∃ ξ : F, P ξ ∧ σ ξ = y := by
    intro y
    have hset := mixedEmbedding.coe_dualSubmodule_flip_traceForm_idealLattice F I
    show y ∈ LinearMap.BilinForm.dualSubmodule (Algebra.traceForm ℝ V).flip (mixedEmbedding.idealLattice F I) ↔ _
    rw [← SetLike.mem_coe, hset, Set.mem_image]
    simp only [SetLike.mem_coe, hdualI]
    exact Iff.rfl
  let D : Set F := {ξ | P ξ}
  let ED : D ≃ Ld := Equiv.ofBijective (fun ξ => ⟨σ ξ, (hmemD _).2 ⟨ξ, ξ.2, rfl⟩⟩)
    ⟨fun a b hab => Subtype.ext (mixedEmbedding_injective F (congrArg Subtype.val hab)), fun y => by
      obtain ⟨ξ, hξ, hy⟩ := (hmemD y).1 y.2
      exact ⟨⟨ξ, hξ⟩, Subtype.ext hy⟩⟩
  have hED : ∀ ξ : D, ((ED ξ : Ld) : V) = σ ξ := fun ξ => rfl

  have hfkι : ∀ ξ : F, fk k (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = g (σ ξ) * (S k).indicator 1 (algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ) := by
    intro ξ
    show g (InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ).1) *
        (S k).indicator 1 (algebraMap F (AdeleRing (𝓞 F) F) ξ).2 = _
    rw [hι1, hι2, hE]
  have hLS : ∀ ξ : F, algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ ∈ S k ↔ ∃ a : 𝓞 F, ξ = k + (d : F) * a :=
    fun ξ => algebraMap_mem_image_integralFiniteAdeles_iff F d hd k ξ
  let jk : 𝓞 F → F := fun a => k + (d : F) * a
  have hjk : Function.Injective jk := fun a b hab =>
    RingOfIntegers.eq_iff.mp (mul_left_cancel₀ hd' (add_left_cancel hab))
  have hsupp : Function.support (fun ξ : F => fk k (algebraMap F (AdeleRing (𝓞 F) F) ξ)) ⊆ Set.range jk := by
    intro ξ hξ
    rw [Function.mem_support, hfkι] at hξ
    have hmem : algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ ∈ S k := by
      by_contra hn
      exact hξ (by rw [Set.indicator_of_notMem hn, mul_zero])
    obtain ⟨a, rfl⟩ := (hLS ξ).1 hmem
    exact ⟨a, rfl⟩
  have hLHS : ∑' ξ : F, fk k (algebraMap F (AdeleRing (𝓞 F) F) ξ) = ∑' x : L, g (t + x) := by
    rw [← hjk.tsum_eq hsupp]
    have hja : ∀ a : 𝓞 F, fk k (algebraMap F (AdeleRing (𝓞 F) F) (jk a)) = g (t + (EL a : V)) := by
      intro a
      rw [hfkι, Set.indicator_of_mem ((hLS _).2 ⟨a, rfl⟩), Pi.one_apply, mul_one, hEL, map_add]
    exact (tsum_congr hja).trans (EL.tsum_eq (fun x : L => g (t + x)))

  have hP2 := ZLattice.tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
    (volume : Measure V) Bt hBt L g t

  have hphase2 : ∀ ξ : F, (𝐞 ((Algebra.trace ℚ F (k * ξ) : ℚ) : ℝ) : ℂ) = (𝐞 (Bt t (σ ξ)) : ℂ) := by
    intro ξ
    congr 2
    show _ = Algebra.trace ℝ V (σ k * σ ξ)
    rw [← map_mul, mixedEmbedding.trace_mixedEmbedding]
  have hGD : ∀ y : Ld, G (ED.symm y : D)
      = VectorFourier.fourierIntegral 𝐞 volume Bt g y * (𝐞 (Bt t y) : ℂ) := by
    intro y
    obtain ⟨ξ, rfl⟩ := ED.surjective y
    rw [Equiv.symm_apply_apply, hED]
    show VectorFourier.fourierIntegral 𝐞 volume Bt g (σ ξ) * _ = _
    rw [hphase2]
  have hSF : Summable fun y : Ld =>
      VectorFourier.fourierIntegral 𝐞 volume Bt g y * (𝐞 (Bt t y) : ℂ) :=
    ZLattice.summable_fourierIntegral_mul_fourierChar_dualSubmodule volume Bt hBt L g t
  have hsumG : Summable (D.indicator G) := by
    rw [← summable_subtype_iff_indicator]
    have h1 : (G ∘ Subtype.val) ∘ ED.symm
        = fun y : Ld => VectorFourier.fourierIntegral 𝐞 volume Bt g y * (𝐞 (Bt t y) : ℂ) :=
      funext fun y => hGD y
    exact (ED.symm.summable_iff).mp (h1 ▸ hSF)
  refine ⟨?_, ?_⟩
  · have : (fun ξ : F => fourierIntegral ψ μ (fk k) (algebraMap F (AdeleRing (𝓞 F) F) ξ))
        = fun ξ => (ZLattice.covolume L volume : ℂ)⁻¹ * D.indicator G ξ := funext hstar
    rw [this]
    exact hsumG.mul_left _
  · calc ∑' ξ : F, fk k (algebraMap F (AdeleRing (𝓞 F) F) ξ)
        = ∑' x : L, g (t + x) := hLHS
      _ = (ZLattice.covolume L volume : ℂ)⁻¹ *
            ∑' y : Ld, VectorFourier.fourierIntegral 𝐞 volume Bt g y * (𝐞 (Bt t y) : ℂ) := hP2
      _ = (ZLattice.covolume L volume : ℂ)⁻¹ * ∑' ξ : D, G ξ := by
          congr 1
          rw [← ED.tsum_eq]
          exact tsum_congr fun ξ => by rw [← hGD (ED ξ), Equiv.symm_apply_apply]
      _ = (ZLattice.covolume L volume : ℂ)⁻¹ * ∑' ξ : F, D.indicator G ξ := by rw [tsum_subtype]
      _ = ∑' ξ : F, (ZLattice.covolume L volume : ℂ)⁻¹ * D.indicator G ξ := tsum_mul_left.symm
      _ = ∑' ξ : F, fourierIntegral ψ μ (fk k) (algebraMap F (AdeleRing (𝓞 F) F) ξ) :=
          tsum_congr fun ξ => (hstar ξ).symm

end S_NumberField_AdelicFourier_tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace
end P2MW
export P2MW.S_NumberField_AdelicFourier_tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace (solution)
