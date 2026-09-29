-- Prove2me | solution 1 for HopfAlgebra.isHopfGalois_of_isHopfGalois_baseChange_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e039b8b4-8309-54c4-bfd0-b8f1ffc9e7aa

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_isHopfGalois_iff_ker_le_span_of_surjective
import Theorems.Thm_HopfAlgebra_hopfKer_baseChange_toSubmodule_eq_range_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_isHopfGalois_of_isHopfGalois_baseChange_of_flat

set_option maxHeartbeats 1600000
set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk hopfKer IsHopfGalois isHopfGalois_iff_ker_le_span_of_surjective hopfKer_baseChange_toSubmodule_eq_range_baseChange"
p2m_open "HopfAlgebra"

section AugIdealBaseChange

variable {R : Type u} [CommRing R] (K : Type u) [CommRing K] [Algebra R K]
variable {H : Type v} [CommRing H] [HopfAlgebra R H] {H' : Type w} [CommRing H'] [HopfAlgebra R H']
variable (qc : H →ₐc[R] H')

noncomputable def augPart : ↥(hopfKer qc) →ₗ[R] H :=
  (hopfKer qc).val.toLinearMap -
    (Algebra.linearMap R H).comp ((Coalgebra.counit (R := R) (A := H)).comp (hopfKer qc).val.toLinearMap)

theorem augPart_apply (b : ↥(hopfKer qc)) :
    augPart qc b = (b : H) - algebraMap R H (Coalgebra.counit (R := R) (b : H)) := rfl

theorem augPart_mem (b : ↥(hopfKer qc)) :
    augPart qc b ∈ Ideal.span {a : H | a ∈ hopfKer qc ∧ Coalgebra.counit (R := R) a = 0} := by
  apply Ideal.subset_span
  refine ⟨?_, ?_⟩
  · rw [augPart_apply]
    exact (hopfKer qc).sub_mem b.2 ((hopfKer qc).algebraMap_mem _)
  · rw [augPart_apply, map_sub, Bialgebra.counit_algebraMap, sub_self]

theorem baseChange_val_eq_linearMap :
    ((hopfKer qc).val.toLinearMap.baseChange K) =
      ((augPart qc).baseChange K) +
        (Algebra.linearMap K (K ⊗[R] H)).comp
          ((Coalgebra.counit (R := K) (A := K ⊗[R] H)).comp ((hopfKer qc).val.toLinearMap.baseChange K)) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro k b
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, augPart_apply, TensorProduct.counit_tmul,
    CommSemiring.counit_apply, Algebra.TensorProduct.algebraMap_apply, TensorProduct.tmul_sub]
  show k ⊗ₜ[R] (b : H) = k ⊗ₜ[R] (b : H) - k ⊗ₜ[R] algebraMap R H (Coalgebra.counit (R := R) (b : H)) +
    algebraMap K K (Coalgebra.counit (R := R) (b : H) • k) ⊗ₜ[R] (1 : H)
  rw [Algebra.algebraMap_self, RingHom.id_apply, TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
    sub_add_cancel]

theorem baseChange_val_eq (t : K ⊗[R] ↥(hopfKer qc)) :
    ((hopfKer qc).val.toLinearMap.baseChange K) t =
      ((augPart qc).baseChange K) t +
        algebraMap K (K ⊗[R] H) (Coalgebra.counit (R := K) (((hopfKer qc).val.toLinearMap.baseChange K) t)) := by
  have := LinearMap.congr_fun (baseChange_val_eq_linearMap K qc) t
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, Algebra.linearMap_apply] using this

theorem span_augHopfKer_baseChange_le_map_includeRight [Module.Flat R K] :
    Ideal.span {a : K ⊗[R] H |
        a ∈ hopfKer (Bialgebra.TensorProduct.map (BialgHom.id K K) qc : K ⊗[R] H →ₐc[K] K ⊗[R] H') ∧
          Coalgebra.counit (R := K) a = 0}
      ≤ (Ideal.span {a : H | a ∈ hopfKer qc ∧ Coalgebra.counit (R := R) a = 0}).map
          (Algebra.TensorProduct.includeRight : H →ₐ[R] K ⊗[R] H) := by
  set J : Ideal H := Ideal.span {a : H | a ∈ hopfKer qc ∧ Coalgebra.counit (R := R) a = 0}
  set JK : Ideal (K ⊗[R] H) := J.map (Algebra.TensorProduct.includeRight : H →ₐ[R] K ⊗[R] H)
  rw [Ideal.span_le]
  rintro a ⟨haK, hεa⟩

  have hrange : a ∈ LinearMap.range ((hopfKer qc).val.toLinearMap.baseChange K) := by
    rw [← hopfKer_baseChange_toSubmodule_eq_range_baseChange K qc]
    exact haK
  obtain ⟨t, rfl⟩ := hrange

  have haug : ∀ t : K ⊗[R] ↥(hopfKer qc), ((augPart qc).baseChange K) t ∈ JK := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact JK.zero_mem
    | tmul k b =>
        rw [LinearMap.baseChange_tmul]
        have : k ⊗ₜ[R] augPart qc b = (k ⊗ₜ[R] (1 : H)) * Algebra.TensorProduct.includeRight (augPart qc b) := by
          rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [this]
        exact JK.mul_mem_left _ (Ideal.mem_map_of_mem _ (augPart_mem qc b))
    | add x y hx hy => rw [map_add]; exact JK.add_mem hx hy
  show ((hopfKer qc).val.toLinearMap.baseChange K) t ∈ JK
  rw [baseChange_val_eq K qc t, hεa, map_zero, add_zero]
  exact haug t

end AugIdealBaseChange
end HopfAlgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk hopfKer IsHopfGalois isHopfGalois_iff_ker_le_span_of_surjective hopfKer_baseChange_toSubmodule_eq_range_baseChange"
p2m_open "HopfAlgebra"

section AugQuotFlat

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
  {H' : Type w} [CommRing H'] [HopfAlgebra R H'] (qc : H →ₐc[R] H')

noncomputable def augHom : ↥(hopfKer qc) →ₐ[R] R := (Bialgebra.counitAlgHom R H).comp (hopfKer qc).val

theorem augHom_apply (b : ↥(hopfKer qc)) : augHom qc b = Coalgebra.counit (R := R) (b : H) := rfl

theorem augHom_surjective : Function.Surjective (augHom qc) := fun r =>
  ⟨algebraMap R _ r, by rw [augHom_apply]; exact Bialgebra.counit_algebraMap r⟩

theorem span_aug_eq_map_ker :
    Ideal.span {a : H | a ∈ hopfKer qc ∧ Coalgebra.counit (R := R) a = 0} =
      (RingHom.ker (augHom qc)).map (algebraMap ↥(hopfKer qc) H) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro a ⟨ha, hε⟩
    exact Ideal.mem_map_of_mem (algebraMap ↥(hopfKer qc) H)
      (show (⟨a, ha⟩ : ↥(hopfKer qc)) ∈ RingHom.ker (augHom qc) from hε)
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    exact Ideal.subset_span ⟨b.2, hb⟩

theorem flat_quot_span_aug [Module.Flat ↥(hopfKer qc) H] :
    Module.Flat R (H ⧸ Ideal.span {a : H | a ∈ hopfKer qc ∧ Coalgebra.counit (R := R) a = 0}) := by
  let I : Ideal ↥(hopfKer qc) := RingHom.ker (augHom qc)
  have hJ : Ideal.span {a : H | a ∈ hopfKer qc ∧ Coalgebra.counit (R := R) a = 0} =
      I.map (algebraMap ↥(hopfKer qc) H) := span_aug_eq_map_ker qc

  let e₂ : (↥(hopfKer qc) ⧸ I) ≃ₐ[R] R := Ideal.quotientKerAlgEquivOfSurjective (augHom_surjective qc)
  haveI : Module.Flat R (↥(hopfKer qc) ⧸ I) := Module.Flat.of_linearEquiv e₂.toLinearEquiv
  haveI : Module.Flat (↥(hopfKer qc) ⧸ I) ((↥(hopfKer qc) ⧸ I) ⊗[↥(hopfKer qc)] H) := inferInstance
  haveI : Module.Flat R ((↥(hopfKer qc) ⧸ I) ⊗[↥(hopfKer qc)] H) :=
    Module.Flat.trans R (↥(hopfKer qc) ⧸ I) _

  let e₁ := Algebra.TensorProduct.quotIdealMapEquivTensorQuot (B := H) I
  let e₃ : (H ⧸ I.map (algebraMap ↥(hopfKer qc) H)) ≃ₗ[R] ((↥(hopfKer qc) ⧸ I) ⊗[↥(hopfKer qc)] H) :=
    (e₁.restrictScalars R).toLinearEquiv.trans
      ((Algebra.TensorProduct.comm ↥(hopfKer qc) H (↥(hopfKer qc) ⧸ I)).restrictScalars R).toLinearEquiv
  rw [hJ]
  exact Module.Flat.of_linearEquiv e₃

theorem mem_span_aug_of_smul_mem [IsDomain R] [Module.Flat ↥(hopfKer qc) H] {d : R} (hd : d ≠ 0) {x : H}
    (h : d • x ∈ Ideal.span {a : H | a ∈ hopfKer qc ∧ Coalgebra.counit (R := R) a = 0}) :
    x ∈ Ideal.span {a : H | a ∈ hopfKer qc ∧ Coalgebra.counit (R := R) a = 0} := by
  haveI := flat_quot_span_aug qc
  have hreg : IsSMulRegular (H ⧸ Ideal.span {a : H | a ∈ hopfKer qc ∧ Coalgebra.counit (R := R) a = 0}) d :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd)
  rw [← Ideal.Quotient.eq_zero_iff_mem] at h ⊢
  apply hreg
  show d • Ideal.Quotient.mk _ x = d • 0
  rw [smul_zero, ← Ideal.Quotient.mkₐ_eq_mk R, ← map_smul, Ideal.Quotient.mkₐ_eq_mk, h]

end AugQuotFlat

end HopfAlgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk hopfKer IsHopfGalois isHopfGalois_iff_ker_le_span_of_surjective hopfKer_baseChange_toSubmodule_eq_range_baseChange"
p2m_open "HopfAlgebra"
namespace GalDescent

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]

theorem exists_smul_mem_of_one_tmul_mem_map_includeRight [IsDomain R] [Module.Flat R H]
    (K : Type u) [CommRing K] [Algebra R K] [IsFractionRing R K]
    (J : Ideal H) {x : H}
    (hx : (1 : K) ⊗ₜ[R] x ∈ J.map (Algebra.TensorProduct.includeRight : H →ₐ[R] K ⊗[R] H)) :
    ∃ d : R, d ≠ 0 ∧ d • x ∈ J := by
  have hx' : (1 : K) ⊗ₜ[R] x ∈ (J.map (Algebra.TensorProduct.includeRight : H →ₐ[R] K ⊗[R] H)).restrictScalars R := hx
  rw [Ideal.map_includeRight_eq] at hx'
  obtain ⟨z, hz⟩ := hx'
  obtain ⟨⟨j, s⟩, hjs⟩ := IsLocalizedModule.surj (nonZeroDivisors R) (TensorProduct.mk R K ↥(J.restrictScalars R) 1) z

  have h1 : (s : R) • ((1 : K) ⊗ₜ[R] x) = (1 : K) ⊗ₜ[R] (j : H) := by
    have := congrArg (LinearMap.lTensor K (J.restrictScalars R).subtype) hjs
    rw [Submonoid.smul_def, map_smul, hz] at this
    rw [this, TensorProduct.mk_apply, LinearMap.lTensor_tmul]
    rfl
  refine ⟨s, nonZeroDivisors.ne_zero s.2, ?_⟩
  have h2 : (1 : K) ⊗ₜ[R] ((s : R) • x - (j : H)) = 0 := by
    rw [TensorProduct.tmul_sub, TensorProduct.tmul_smul, h1, sub_self]
  have h3 : TensorProduct.mk R K H 1 ((s : R) • x - (j : H)) = 0 := h2
  obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors R) (TensorProduct.mk R K H 1)).1 h3
  have hreg : IsSMulRegular H ((s' : R)) :=
    Module.IsTorsionFree.isSMulRegular (IsRegular.of_ne_zero (nonZeroDivisors.ne_zero s'.2))
  have h4 : (s : R) • x - (j : H) = 0 := hreg (by
    change (s' : R) • _ = (s' : R) • (0 : H)
    rw [smul_zero, ← Submonoid.smul_def]; exact hs')
  rw [sub_eq_zero] at h4
  rw [h4]
  exact j.2

end GalDescent
end HopfAlgebra

namespace HopfAlgebra p2m_export "HopfAlgebra" "mk hopfKer IsHopfGalois isHopfGalois_iff_ker_le_span_of_surjective hopfKer_baseChange_toSubmodule_eq_range_baseChange" namespace GalDescent end HopfAlgebra.GalDescent
p2m_open_scoped "HopfAlgebra" in

theorem HopfAlgebra.GalDescent.isHopfGalois_of_baseChange
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Flat R H]
    {H' : Type w} [CommRing H'] [HopfAlgebra R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc)
    [Module.Flat ↥(HopfAlgebra.hopfKer qc) H]
    (hK : HopfAlgebra.IsHopfGalois
      (Bialgebra.TensorProduct.map (BialgHom.id K K) qc : K ⊗[R] H →ₐc[K] K ⊗[R] H')) :
    HopfAlgebra.IsHopfGalois qc := by
  haveI : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  set qcK := (Bialgebra.TensorProduct.map (BialgHom.id K K) qc : K ⊗[R] H →ₐc[K] K ⊗[R] H') with hqcK

  have hqcK_tmul : ∀ (k : K) (h : H), qcK (k ⊗ₜ[R] h) = k ⊗ₜ[R] qc h := fun _ _ => rfl
  have hsurjK : Function.Surjective qcK := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul k h' =>
        obtain ⟨h, rfl⟩ := hqc h'
        exact ⟨k ⊗ₜ[R] h, hqcK_tmul k h⟩
    | add x y hx hy =>
        obtain ⟨x', rfl⟩ := hx
        obtain ⟨y', rfl⟩ := hy
        exact ⟨x' + y', map_add _ _ _⟩

  have hkerK := (HopfAlgebra.isHopfGalois_iff_ker_le_span_of_surjective qcK hsurjK).1 hK

  refine (HopfAlgebra.isHopfGalois_iff_ker_le_span_of_surjective qc hqc).2 fun x hx => ?_
  have hx0 : qc x = 0 := hx
  have hxK : (1 : K) ⊗ₜ[R] x ∈ RingHom.ker (qcK : K ⊗[R] H →ₐ[K] K ⊗[R] H') := by
    rw [RingHom.mem_ker]
    change qcK ((1 : K) ⊗ₜ[R] x) = 0
    rw [hqcK_tmul, hx0, TensorProduct.tmul_zero]
  have h1 := hkerK hxK
  have h2 := HopfAlgebra.span_augHopfKer_baseChange_le_map_includeRight K qc h1
  obtain ⟨d, hd, hdx⟩ := HopfAlgebra.GalDescent.exists_smul_mem_of_one_tmul_mem_map_includeRight K _ h2
  exact HopfAlgebra.mem_span_aug_of_smul_mem qc hd hdx

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Flat R H]
    {H' : Type w} [CommRing H'] [HopfAlgebra R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc)
    [Module.Flat ↥(HopfAlgebra.hopfKer qc) H]
    (hK : HopfAlgebra.IsHopfGalois
      (Bialgebra.TensorProduct.map (BialgHom.id K K) qc : K ⊗[R] H →ₐc[K] K ⊗[R] H')) :
    HopfAlgebra.IsHopfGalois qc :=
  HopfAlgebra.GalDescent.isHopfGalois_of_baseChange K qc hqc hK

end S_HopfAlgebra_isHopfGalois_of_isHopfGalois_baseChange_of_flat
end P2MW
export P2MW.S_HopfAlgebra_isHopfGalois_of_isHopfGalois_baseChange_of_flat (solution)
