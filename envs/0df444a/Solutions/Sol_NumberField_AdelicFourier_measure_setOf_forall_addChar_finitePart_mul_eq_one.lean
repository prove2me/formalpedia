-- Prove2me | solution 1 for NumberField.AdelicFourier.measure_setOf_forall_addChar_finitePart_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6adacfc5-dd58-5ea4-88f9-933760fd06b1

import Mathlib
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Theorems.Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual
import Theorems.Thm_NumberField_AdelicBox_algebraMap_mem_image_integralFiniteAdeles_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_measure_setOf_forall_addChar_finitePart_mul_eq_one

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

p2m_open "NumberField P2MW.S_NumberField_AdelicFourier_measure_setOf_forall_addChar_finitePart_mul_eq_one.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_measure_setOf_forall_addChar_finitePart_mul_eq_one.NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory"

open scoped Classical FourierTransform nonZeroDivisors

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace AdeleRing AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual AdelicBox.algebraMap_mem_image_integralFiniteAdeles_iff"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual"
namespace Ws25
namespace AnnVol
p2m_open "NumberField.AdelicFourier NumberField"

variable {F : Type} [Field F] [NumberField F]

theorem add_mem_integralFiniteAdeles {y z : FiniteAdeleRing (𝓞 F) F}
    (hy : y ∈ integralFiniteAdeles (𝓞 F) F) (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    y + z ∈ integralFiniteAdeles (𝓞 F) F := fun v => add_mem (hy v) (hz v)

theorem sub_mem_integralFiniteAdeles {y z : FiniteAdeleRing (𝓞 F) F}
    (hy : y ∈ integralFiniteAdeles (𝓞 F) F) (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    y - z ∈ integralFiniteAdeles (𝓞 F) F := fun v => sub_mem (hy v) (hz v)

theorem algebraMap_coe_mem_integralFiniteAdeles (q : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (q : F) ∈ integralFiniteAdeles (𝓞 F) F :=
  fun v => algebraMap_mem_adicCompletionIntegers (𝓞 F) F v q

theorem exists_eq_coe_of_algebraMap_mem {ξ : F}
    (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ ∈ integralFiniteAdeles (𝓞 F) F) :
    ∃ e : 𝓞 F, ξ = (e : F) := by
  have hset : (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) 0
      + algebraMap F (FiniteAdeleRing (𝓞 F) F) ((1 : 𝓞 F) : F) * z) '' integralFiniteAdeles (𝓞 F) F
      = integralFiniteAdeles (𝓞 F) F := by
    have : (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) 0
        + algebraMap F (FiniteAdeleRing (𝓞 F) F) ((1 : 𝓞 F) : F) * z) = id := by
      funext z
      rw [show ((1 : 𝓞 F) : F) = 1 from map_one (algebraMap (𝓞 F) F), map_zero, map_one,
        zero_add, one_mul, id]
    rw [this, Set.image_id]
  have hLS := NumberField.AdelicBox.algebraMap_mem_image_integralFiniteAdeles_iff F 1 one_ne_zero 0 ξ
  rw [hset] at hLS
  obtain ⟨e, he⟩ := hLS.mp h
  refine ⟨e, ?_⟩
  rw [he, show ((1 : 𝓞 F) : F) = 1 from map_one (algebraMap (𝓞 F) F), zero_add, one_mul]

theorem ncard_map_eq_absNorm {a : 𝓞 F} (ha : a ≠ 0) {𝔡 𝔟 : Ideal (𝓞 F)}
    (h : Ideal.span {a} = 𝔡 * 𝔟) :
    ((𝔟.map (Ideal.Quotient.mk (Ideal.span {a})) : Ideal (𝓞 F ⧸ Ideal.span {a})) :
        Set (𝓞 F ⧸ Ideal.span {a})).ncard = Ideal.absNorm 𝔡 := by
  set I : Ideal (𝓞 F) := Ideal.span {a} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]; exact ha
  have h𝔟0 : 𝔟 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at h
    exact hI0 h
  have hle : I ≤ 𝔟 := by rw [h]; exact Ideal.mul_le_right
  haveI : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI0
  set Q : Ideal (𝓞 F ⧸ I) := 𝔟.map (Ideal.Quotient.mk I) with hQ

  have h1 : Nat.card (𝓞 F ⧸ I) = Nat.card Q * Nat.card ((𝓞 F ⧸ I) ⧸ Q) :=
    Submodule.card_eq_card_quotient_mul_card Q
  have h2 : Nat.card ((𝓞 F ⧸ I) ⧸ Q) = Nat.card (𝓞 F ⧸ 𝔟) :=
    Nat.card_congr (DoubleQuot.quotQuotEquivQuotOfLE hle).toEquiv
  have h3 : Nat.card (𝓞 F ⧸ I) = Ideal.absNorm I :=
    ((Ideal.absNorm_apply I).trans (Submodule.cardQuot_apply _)).symm
  have h4 : Nat.card (𝓞 F ⧸ 𝔟) = Ideal.absNorm 𝔟 :=
    ((Ideal.absNorm_apply 𝔟).trans (Submodule.cardQuot_apply _)).symm
  have h5 : Ideal.absNorm I = Ideal.absNorm 𝔡 * Ideal.absNorm 𝔟 := by
    rw [h, map_mul]
  have h𝔟N : Ideal.absNorm 𝔟 ≠ 0 := fun h0 => h𝔟0 (Ideal.absNorm_eq_zero_iff.mp h0)
  have key : Nat.card Q * Ideal.absNorm 𝔟 = Ideal.absNorm 𝔡 * Ideal.absNorm 𝔟 := by
    rw [← h5, ← h3, h1, h2, h4]
  have := mul_right_cancel₀ h𝔟N key
  rw [← Nat.card_coe_set_eq]
  exact this

theorem measure_annih_eq
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ)) :
    ν {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1}
      = (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ENNReal) * ν (integralFiniteAdeles (𝓞 F) F) := by

  have hann :=
    NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual
      F hψ hψ_inf
  set A : Set (FiniteAdeleRing (𝓞 F) F) :=
    {w | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1} with hA
  set D : FractionalIdeal (𝓞 F)⁰ F :=
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) with hD
  have hD0 : D ≠ 0 := FractionalIdeal.dual_ne_zero (A := ℤ) (K := ℚ) one_ne_zero
  have hmemA : ∀ w, w ∈ A ↔ ∃ r : F, r ∈ D ∧
      w - algebraMap F (FiniteAdeleRing (𝓞 F) F) r ∈ integralFiniteAdeles (𝓞 F) F :=
    fun w => hann w

  have hOD : ∀ e : 𝓞 F, (e : F) ∈ D := fun e =>
    FractionalIdeal.one_le_dual_one (A := ℤ) (K := ℚ)
      ((FractionalIdeal.mem_one_iff (S := (𝓞 F)⁰)).mpr ⟨e, rfl⟩)

  set 𝔡 : Ideal (𝓞 F) := differentIdeal ℤ (𝓞 F) with h𝔡
  have h𝔡D : (𝔡 : FractionalIdeal (𝓞 F)⁰ F) = D⁻¹ := coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := F) (B := 𝓞 F)
  have h𝔡0 : 𝔡 ≠ ⊥ := by
    intro h0
    rw [h0, FractionalIdeal.coeIdeal_bot] at h𝔡D
    exact inv_ne_zero hD0 h𝔡D.symm
  have hN0 : Ideal.absNorm 𝔡 ≠ 0 := fun h0 => h𝔡0 (Ideal.absNorm_eq_zero_iff.mp h0)
  set a : 𝓞 F := (Ideal.absNorm 𝔡 : 𝓞 F) with ha_def
  have ha𝔡 : a ∈ 𝔡 := Ideal.absNorm_mem 𝔡
  have ha0 : a ≠ 0 := by rw [ha_def]; exact Nat.cast_ne_zero.mpr hN0
  have haF : (a : F) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha0)
  obtain ⟨𝔟, h𝔟⟩ : 𝔡 ∣ Ideal.span {a} := Ideal.dvd_span_singleton.mpr ha𝔡

  have h𝔟D : (𝔟 : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) * D := by
    have h1 : (↑(Ideal.span {a}) : FractionalIdeal (𝓞 F)⁰ F) = ↑(𝔡 * 𝔟) := by rw [h𝔟]
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_mul, h𝔡D] at h1

    calc (𝔟 : FractionalIdeal (𝓞 F)⁰ F) = D * (D⁻¹ * ↑𝔟) := by
          rw [← mul_assoc, mul_inv_cancel₀ hD0, one_mul]
      _ = D * FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) := by rw [← h1]
      _ = FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) * D := mul_comm _ _

  have h𝔟_div : ∀ b ∈ 𝔟, (b : F) * (a : F)⁻¹ ∈ D := by
    intro b hb
    have hbF : (b : F) ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) :=
      (FractionalIdeal.mem_coeIdeal (S := (𝓞 F)⁰)).mpr ⟨b, hb, rfl⟩
    rw [h𝔟D] at hbF
    obtain ⟨r, hr, hbr⟩ := FractionalIdeal.mem_singleton_mul.mp hbF
    rw [hbr, mul_comm (a : F) r, mul_assoc, mul_inv_cancel₀ haF, mul_one]
    exact hr
  have hD_mul : ∀ r ∈ D, ∃ b ∈ 𝔟, (b : F) = (a : F) * r := by
    intro r hr
    have : (a : F) * r ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [h𝔟D]
      exact FractionalIdeal.mem_singleton_mul.mpr ⟨r, hr, rfl⟩
    obtain ⟨b, hb, hbr⟩ := (FractionalIdeal.mem_coeIdeal (S := (𝓞 F)⁰)).mp this
    exact ⟨b, hb, hbr⟩

  set I : Ideal (𝓞 F) := Ideal.span {a} with hI
  have hmk : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  set σ : 𝓞 F ⧸ I → 𝓞 F := Function.surjInv hmk with hσ
  have hσ_mk : ∀ q, Ideal.Quotient.mk I (σ q) = q := Function.surjInv_eq hmk
  set Q : Set (𝓞 F ⧸ I) := ((𝔟.map (Ideal.Quotient.mk I) : Ideal (𝓞 F ⧸ I)) : Set (𝓞 F ⧸ I))
    with hQ
  have hI0 : I ≠ ⊥ := by rw [hI, Ne, Ideal.span_singleton_eq_bot]; exact ha0
  haveI : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI0
  have hQfin : Q.Finite := Set.toFinite Q

  have hσD : ∀ q ∈ Q, (σ q : F) * (a : F)⁻¹ ∈ D := by
    intro q hq
    obtain ⟨b, hb, hbq⟩ := (Ideal.mem_map_iff_of_surjective _ hmk).mp hq
    have hqb : Ideal.Quotient.mk I (σ q) = Ideal.Quotient.mk I b := by rw [hσ_mk, hbq]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hqb)

    have hσq : (σ q : F) = (b : F) + (c : F) * (a : F) := by
      rw [← map_mul, ← map_add]
      exact congrArg (algebraMap (𝓞 F) F) (by rw [hc]; abel)
    rw [hσq, add_mul, mul_assoc, mul_inv_cancel₀ haF, mul_one]
    exact Submodule.add_mem (D : Submodule (𝓞 F) F) (h𝔟_div b hb) (hOD c)

  set P : 𝓞 F ⧸ I → Set (FiniteAdeleRing (𝓞 F) F) := fun q =>
    (fun z => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((σ q : F) * (a : F)⁻¹) + z) ''
      integralFiniteAdeles (𝓞 F) F with hP

  have hcover : A = ⋃ q ∈ hQfin.toFinset, P q := by
    ext w
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset]
    constructor
    · intro hw
      obtain ⟨r, hr, hwr⟩ := (hmemA w).mp hw
      obtain ⟨b, hb, hbr⟩ := hD_mul r hr
      refine ⟨Ideal.Quotient.mk I b, Ideal.mem_map_of_mem _ hb, ?_⟩

      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
        (Ideal.Quotient.eq.mp (hσ_mk (Ideal.Quotient.mk I b)))
      have hσb : (σ (Ideal.Quotient.mk I b) : F) * (a : F)⁻¹ = r + (c : F) := by
        have : (σ (Ideal.Quotient.mk I b) : F) = (b : F) + (c : F) * (a : F) := by
          rw [← map_mul, ← map_add]
          exact congrArg (algebraMap (𝓞 F) F) (by rw [hc]; abel)
        rw [this, hbr, add_mul, mul_inv_cancel_right₀ haF, mul_comm (a : F) r,
          mul_inv_cancel_right₀ haF]
      refine ⟨w - algebraMap F (FiniteAdeleRing (𝓞 F) F) ((σ (Ideal.Quotient.mk I b) : F) * (a : F)⁻¹),
        ?_, by simp only; abel⟩
      rw [hσb, map_add, ← sub_sub]
      exact sub_mem_integralFiniteAdeles hwr (algebraMap_coe_mem_integralFiniteAdeles c)
    · rintro ⟨q, hq, z, hz, rfl⟩
      refine (hmemA _).mpr ⟨(σ q : F) * (a : F)⁻¹, hσD q hq, ?_⟩
      simpa only [add_sub_cancel_left] using hz

  have hdisj : Set.PairwiseDisjoint (↑hQfin.toFinset : Set (𝓞 F ⧸ I)) P := by
    intro q₁ hq₁ q₂ hq₂ hne
    refine Set.disjoint_left.mpr fun x hx₁ hx₂ => hne ?_
    obtain ⟨z₁, hz₁, rfl⟩ := hx₁
    obtain ⟨z₂, hz₂, hx⟩ := hx₂

    have hdiff : algebraMap F (FiniteAdeleRing (𝓞 F) F)
        (((σ q₂ : F) - (σ q₁ : F)) * (a : F)⁻¹) ∈ integralFiniteAdeles (𝓞 F) F := by
      have heq : algebraMap F (FiniteAdeleRing (𝓞 F) F) (((σ q₂ : F) - (σ q₁ : F)) * (a : F)⁻¹)
          = z₁ - z₂ := by
        simp only at hx
        rw [sub_mul, map_sub]
        linear_combination hx
      rw [heq]
      exact sub_mem_integralFiniteAdeles hz₁ hz₂
    obtain ⟨e, he⟩ := exists_eq_coe_of_algebraMap_mem hdiff

    have hOe : σ q₂ - σ q₁ = e * a := by
      apply IsFractionRing.injective (𝓞 F) F
      rw [map_sub, map_mul]
      show (σ q₂ : F) - (σ q₁ : F) = (e : F) * (a : F)
      rw [← he, mul_assoc, inv_mul_cancel₀ haF, mul_one]
    have : Ideal.Quotient.mk I (σ q₂) = Ideal.Quotient.mk I (σ q₁) :=
      Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton'.mpr ⟨e, hOe.symm⟩)
    rw [hσ_mk, hσ_mk] at this
    exact this.symm

  have hPre : ∀ q, P q = (fun z => -algebraMap F (FiniteAdeleRing (𝓞 F) F) ((σ q : F) * (a : F)⁻¹) + z) ⁻¹'
      integralFiniteAdeles (𝓞 F) F := fun q => Set.image_add_left
  have hmeas : ∀ q ∈ hQfin.toFinset, MeasurableSet (P q) := fun q _ => by
    rw [hPre]
    exact ((isClosed_integralFiniteAdeles F).preimage (continuous_const.add continuous_id)).measurableSet
  have hνP : ∀ q, ν (P q) = ν (integralFiniteAdeles (𝓞 F) F) := fun q => by
    rw [hPre]
    exact measure_preimage_add ν _ _

  rw [hcover, measure_biUnion_finset hdisj hmeas, Finset.sum_congr rfl fun q _ => hνP q,
    Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [← Set.ncard_eq_toFinset_card Q hQfin, hQ, ncard_map_eq_absNorm ha0 h𝔟]

end NumberField.AdelicFourier.Ws25.AnnVol

open NumberField.AdelicFourier.Ws25.AnnVol in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ)) :
    ν {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1}
      = (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ENNReal) * ν (integralFiniteAdeles (𝓞 F) F) :=
  measure_annih_eq ν hψ hψ_inf

end

end S_NumberField_AdelicFourier_measure_setOf_forall_addChar_finitePart_mul_eq_one
end P2MW
export P2MW.S_NumberField_AdelicFourier_measure_setOf_forall_addChar_finitePart_mul_eq_one (solution)
