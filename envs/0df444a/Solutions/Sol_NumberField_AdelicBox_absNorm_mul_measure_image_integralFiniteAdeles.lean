-- Prove2me | solution 1 for NumberField.AdelicBox.absNorm_mul_measure_image_integralFiniteAdeles
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7b1f28ce-61e8-5d4f-b25a-37c9409702bc

import Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicBox_absNorm_mul_measure_image_integralFiniteAdeles

set_option autoImplicit false

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped nonZeroDivisors

namespace LatIdx

open IsDedekindDomain MeasureTheory

variable (F : Type) [Field F] [NumberField F]

def dBox (d : 𝓞 F) : Set (FiniteAdeleRing (𝓞 F) F) :=
  (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
    integralFiniteAdeles (𝓞 F) F

theorem algebraMap_integer_apply (a : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v
      = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := rfl

theorem valued_algebraMap_integer (a : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v) = v.intValuation a := by
  rw [algebraMap_integer_apply, show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)
        = ((algebraMap (𝓞 F) F a : F) : v.adicCompletion F) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]

theorem mul_apply' (x y : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (x * y) v = x v * y v := rfl

theorem sub_apply' (x y : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (x - y) v = x v - y v := rfl

theorem algebraMap_integer_mem (a : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  algebraMap_mem_adicCompletionIntegers (𝓞 F) F v a

theorem mul_integer_mem (a : 𝓞 F) {z : FiniteAdeleRing (𝓞 F) F} (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) * z ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  mul_mem (algebraMap_mem_adicCompletionIntegers (𝓞 F) F v a) (hz v)

theorem add_mem' {z w : FiniteAdeleRing (𝓞 F) F} (hz : z ∈ integralFiniteAdeles (𝓞 F) F)
    (hw : w ∈ integralFiniteAdeles (𝓞 F) F) : z + w ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  add_mem (hz v) (hw v)

theorem sub_mem' {z w : FiniteAdeleRing (𝓞 F) F} (hz : z ∈ integralFiniteAdeles (𝓞 F) F)
    (hw : w ∈ integralFiniteAdeles (𝓞 F) F) : z - w ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  sub_mem (hz v) (hw v)

theorem dBox_sub_mem {d : 𝓞 F} {y y' : FiniteAdeleRing (𝓞 F) F} (hy : y ∈ dBox F d) (hy' : y' ∈ dBox F d) :
    y - y' ∈ dBox F d := by
  obtain ⟨w, hw, rfl⟩ := hy
  obtain ⟨w', hw', rfl⟩ := hy'
  exact ⟨w - w', sub_mem' F hw hw', by simp only [mul_sub]⟩

theorem isCompact_dBox (d : 𝓞 F) : IsCompact (dBox F d) :=
  (isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)

variable {F}

theorem exists_sub_mem_dBox {d : 𝓞 F} (hd : d ≠ 0) {z : FiniteAdeleRing (𝓞 F) F}
    (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    ∃ a : 𝓞 F, z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ dBox F d := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  obtain ⟨a, ha⟩ := exists_forall_valued_sub_le (𝓞 F) F hz hd
  refine ⟨a, algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹
      * (z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)), fun v => ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, mul_apply', map_mul, sub_apply']
    have hdv : Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v) ≠ 0 := by
      rw [valued_algebraMap_integer]; exact v.intValuation_ne_zero d hd
    have hinv : Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹) v)
        = (Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v))⁻¹ := by
      rw [show (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹) v
          = algebraMap F (v.adicCompletion F) (d : F)⁻¹ from rfl, map_inv₀, Valuation.map_inv]
      rfl
    have ha' : Valued.v (z v - (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v)
        ≤ Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v) := ha v
    rw [hinv]
    calc (Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v))⁻¹
          * Valued.v (z v - (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v)
        ≤ (Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v))⁻¹
          * Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v) := by gcongr
      _ = 1 := inv_mul_cancel₀ hdv
  · show algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹
      * (z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F))) = z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hd', map_one, one_mul]

theorem sub_mem_span_of_sub_mem_dBox {d a a' : 𝓞 F} (hd : d ≠ 0)
    (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a' : F)
      ∈ dBox F d) : a - a' ∈ Ideal.span {d} := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  obtain ⟨w, hw, hw'⟩ := h
  set y : F := (d : F)⁻¹ * ((a : F) - (a' : F)) with hy
  have hwy : w = algebraMap F (FiniteAdeleRing (𝓞 F) F) y := by
    have h1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * w
        = algebraMap F (FiniteAdeleRing (𝓞 F) F) ((a : F) - (a' : F)) := by rw [map_sub]; exact hw'
    calc w = algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹ * (d : F)) * w := by
            rw [inv_mul_cancel₀ hd', map_one, one_mul]
      _ = algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹ * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * w) := by
            rw [map_mul, mul_assoc]
      _ = algebraMap F (FiniteAdeleRing (𝓞 F) F) y := by rw [h1, ← map_mul]
  have hyint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F y ≤ 1 := fun v => by
    have hv : (algebraMap F (FiniteAdeleRing (𝓞 F) F) y) v ∈ v.adicCompletionIntegers F := by
      rw [← hwy]; exact hw v
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (algebraMap F (FiniteAdeleRing (𝓞 F) F) y) v = (y : v.adicCompletion F) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F y hyint
  rw [Ideal.mem_span_singleton']
  refine ⟨b, RingOfIntegers.coe_injective ?_⟩
  have hb' : (b : F) = y := hb
  show ((b * d : 𝓞 F) : F) = ((a - a' : 𝓞 F) : F)
  have e1 : ((b * d : 𝓞 F) : F) = (b : F) * (d : F) := by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul]
  have e2 : ((a - a' : 𝓞 F) : F) = (a : F) - (a' : F) := by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_sub]
  rw [e1, e2, hb', hy, mul_comm, ← mul_assoc, mul_inv_cancel₀ hd', one_mul]

end LatIdx

namespace LatIdx

open IsDedekindDomain MeasureTheory

variable {F : Type} [Field F] [NumberField F]

theorem image_coset_eq (d : 𝓞 F) (x : FiniteAdeleRing (𝓞 F) F) :
    (fun z : FiniteAdeleRing (𝓞 F) F ↦ x + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
        integralFiniteAdeles (𝓞 F) F
      = (fun y : FiniteAdeleRing (𝓞 F) F ↦ x + y) '' dBox F d := by
  rw [dBox, Set.image_image]

theorem measure_image_add_left [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)]
    [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (x : FiniteAdeleRing (𝓞 F) F) (s : Set (FiniteAdeleRing (𝓞 F) F)) :
    ν ((fun y ↦ x + y) '' s) = ν s := by
  rw [Set.image_add_left, measure_preimage_add]

theorem main [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) :
    (Ideal.absNorm (Ideal.span {d}) : ENNReal) *
        ν ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F)
      = ν (integralFiniteAdeles (𝓞 F) F) := by
  classical

  rw [image_coset_eq, measure_image_add_left]

  set I : Ideal (𝓞 F) := Ideal.span {d} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, ne_eq, Ideal.span_singleton_eq_bot]; exact hd
  haveI : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  set r : 𝓞 F ⧸ I → 𝓞 F := Function.surjInv Ideal.Quotient.mk_surjective with hrdef
  have hr : ∀ q, Ideal.Quotient.mk I (r q) = q := Function.surjInv_eq Ideal.Quotient.mk_surjective
  set T : 𝓞 F ⧸ I → Set (FiniteAdeleRing (𝓞 F) F) :=
    fun q ↦ (fun y ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) (r q : F) + y) '' dBox F d with hTdef
  have hcover : integralFiniteAdeles (𝓞 F) F = ⋃ q, T q := by
    ext z
    constructor
    · intro hz
      obtain ⟨a, ha⟩ := exists_sub_mem_dBox hd hz
      refine Set.mem_iUnion.mpr ⟨Ideal.Quotient.mk I a, ?_⟩
      have hra : r (Ideal.Quotient.mk I a) - a ∈ I := Ideal.Quotient.eq.mp (hr _)
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hra
      refine ⟨z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (r (Ideal.Quotient.mk I a) : F), ?_,
        add_sub_cancel _ _⟩
      have : z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (r (Ideal.Quotient.mk I a) : F)
          = (z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F))
            - algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F) := by
        have e : ((r (Ideal.Quotient.mk I a) : 𝓞 F) : F) = (a : F) + (d : F) * (b : F) := by
          have hb2 : (r (Ideal.Quotient.mk I a) : 𝓞 F) = a + d * b := by rw [mul_comm, hb]; abel
          rw [hb2]; simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul]
        rw [e, map_add, map_mul]
        abel
      rw [this]
      exact dBox_sub_mem F ha ⟨_, algebraMap_integer_mem F b, rfl⟩
    · intro hz
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hz
      obtain ⟨y, ⟨w, hw, rfl⟩, rfl⟩ := hq
      exact add_mem' F (algebraMap_integer_mem F _) (mul_integer_mem F d hw)
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨y, hy, rfl⟩ ⟨y', hy', hxy⟩
    dsimp only at hxy
    apply hqq'
    have hsub : algebraMap F (FiniteAdeleRing (𝓞 F) F) (r q' : F)
        - algebraMap F (FiniteAdeleRing (𝓞 F) F) (r q : F) ∈ dBox F d := by
      have : algebraMap F (FiniteAdeleRing (𝓞 F) F) (r q' : F)
          - algebraMap F (FiniteAdeleRing (𝓞 F) F) (r q : F) = y - y' := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm y, hxy]
      rw [this]
      exact dBox_sub_mem F hy hy'
    have hmem := sub_mem_span_of_sub_mem_dBox hd hsub
    rw [← hr q, ← hr q', Ideal.Quotient.eq]

    rw [← neg_sub]
    exact I.neg_mem hmem
  have hmeas : ∀ q, MeasurableSet (T q) := fun q =>
    ((isCompact_dBox F d).image (continuous_const.add continuous_id)).isClosed.measurableSet
  have hcard : (Ideal.absNorm I : ENNReal) = (Finset.univ : Finset (𝓞 F ⧸ I)).card := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, Finset.card_univ]
  calc (Ideal.absNorm I : ENNReal) * ν (dBox F d)
      = ∑ q : 𝓞 F ⧸ I, ν (dBox F d) := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ = ∑ q : 𝓞 F ⧸ I, ν (T q) := Finset.sum_congr rfl fun q _ => (measure_image_add_left ν _ _).symm
    _ = ∑' q : 𝓞 F ⧸ I, ν (T q) := (tsum_fintype _).symm
    _ = ν (⋃ q, T q) := (measure_iUnion hdisj hmeas).symm
    _ = ν (integralFiniteAdeles (𝓞 F) F) := by rw [← hcover]

end LatIdx

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) :
    (Ideal.absNorm (Ideal.span {d}) : ENNReal) *
        ν ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F)
      = ν (integralFiniteAdeles (𝓞 F) F) :=
  LatIdx.main ν d hd k

end S_NumberField_AdelicBox_absNorm_mul_measure_image_integralFiniteAdeles
end P2MW
export P2MW.S_NumberField_AdelicBox_absNorm_mul_measure_image_integralFiniteAdeles (solution)
