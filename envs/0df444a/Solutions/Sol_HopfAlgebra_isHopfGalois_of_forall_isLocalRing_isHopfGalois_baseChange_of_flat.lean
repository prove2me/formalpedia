-- Prove2me | solution 1 for HopfAlgebra.isHopfGalois_of_forall_isLocalRing_isHopfGalois_baseChange_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8c5e6d22-fd52-5960-aee1-4e6ab13ac29e

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_HopfAlgebra_isHopfGalois_iff_ker_le_span_of_surjective
import Theorems.Thm_HopfAlgebra_hopfKer_baseChange_toSubmodule_eq_range_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_isHopfGalois_of_forall_isLocalRing_isHopfGalois_baseChange_of_flat

set_option maxHeartbeats 1600000
set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk hopfKer IsHopfGalois isHopfGalois_iff_ker_le_span_of_surjective hopfKer_baseChange_toSubmodule_eq_range_baseChange"
p2m_open "HopfAlgebra"
namespace LocalDescent

variable {R : Type} [CommRing R]

theorem subsingleton_of_forall_flat_local (Q : Type) [AddCommGroup Q] [Module R Q]
    (h : ∀ (p : Ideal R), p.IsMaximal →
      ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (_ : Module.Flat R R₁) (_ : IsLocalRing R₁),
        (IsLocalRing.maximalIdeal R₁).LiesOver p ∧ Subsingleton (R₁ ⊗[R] Q)) :
    Subsingleton Q := by
  refine ⟨fun q q' => ?_⟩
  rw [← sub_eq_zero]
  set x := q - q'
  by_contra hx

  let I : Ideal R := (Submodule.span R {x}).annihilator
  have hI : I ≠ ⊤ := by
    intro hI
    have h1 : (1 : R) ∈ I := by rw [hI]; trivial
    have := Submodule.mem_annihilator.1 h1 x (Submodule.mem_span_singleton_self x)
    rw [one_smul] at this
    exact hx this
  obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨R₁, _, _, _, _, hlies, hsub⟩ := h p hp

  let φ : (R ⧸ I) →ₗ[R] Q :=
    Submodule.liftQ I ((LinearMap.toSpanSingleton R Q x)) (by
      intro r hr
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact Submodule.mem_annihilator.1 hr x (Submodule.mem_span_singleton_self x))
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro r hr
    induction r using Submodule.Quotient.induction_on with
    | H r =>
      rw [LinearMap.mem_ker, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply] at hr
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      rw [Submodule.mem_annihilator]
      intro y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [smul_comm, hr, smul_zero]
  have hφ1 : Function.Injective (LinearMap.lTensor R₁ φ) := Module.Flat.lTensor_preserves_injective_linearMap φ hφ
  haveI : Subsingleton (R₁ ⊗[R] (R ⧸ I)) := hφ1.subsingleton

  let ψ := Algebra.TensorProduct.quotIdealMapEquivTensorQuot R₁ I
  haveI : Subsingleton (R₁ ⧸ I.map (algebraMap R R₁)) := ψ.toEquiv.subsingleton
  have hmap : I.map (algebraMap R R₁) ≤ IsLocalRing.maximalIdeal R₁ := by
    rw [Ideal.map_le_iff_le_comap]
    have : (IsLocalRing.maximalIdeal R₁).comap (algebraMap R R₁) = p := (hlies.over).symm
    rw [this]
    exact hIp
  have htop : I.map (algebraMap R R₁) = ⊤ := by
    rw [← Ideal.Quotient.subsingleton_iff]
    infer_instance
  exact (IsLocalRing.maximalIdeal.isMaximal R₁).ne_top (top_le_iff.1 (htop ▸ hmap))

end LocalDescent
end HopfAlgebra

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk hopfKer IsHopfGalois isHopfGalois_iff_ker_le_span_of_surjective hopfKer_baseChange_toSubmodule_eq_range_baseChange"
p2m_open "HopfAlgebra"
namespace LocalDescent

variable {R : Type} [CommRing R]

theorem surjective_of_forall_flat_local {M M' : Type} [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M']
    (f : M →ₗ[R] M')
    (h : ∀ (p : Ideal R), p.IsMaximal →
      ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (_ : Module.Flat R R₁) (_ : IsLocalRing R₁),
        (IsLocalRing.maximalIdeal R₁).LiesOver p ∧ Function.Surjective (LinearMap.lTensor R₁ f)) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
  refine subsingleton_of_forall_flat_local (R := R) (M' ⧸ LinearMap.range f) fun p hp => ?_
  obtain ⟨R₁, _, _, _, _, hlies, hsurj⟩ := h p hp
  refine ⟨R₁, inferInstance, inferInstance, inferInstance, inferInstance, hlies, ⟨fun a b => ?_⟩⟩

  have hz : ∀ w : R₁ ⊗[R] (M' ⧸ LinearMap.range f), w = 0 := by
    intro w
    obtain ⟨v, rfl⟩ := LinearMap.lTensor_surjective R₁ (Submodule.mkQ_surjective (LinearMap.range f)) w
    obtain ⟨u, rfl⟩ := hsurj v
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have : (LinearMap.range f).mkQ ∘ₗ f = 0 := by
      ext m; simp
    rw [this, LinearMap.lTensor_zero, LinearMap.zero_apply]
  rw [hz a, hz b]

theorem mem_of_forall_flat_local_one_tmul_mem {H : Type} [CommRing H] [Algebra R H] (J : Ideal H) (x : H)
    (h : ∀ (p : Ideal R), p.IsMaximal →
      ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (_ : Module.Flat R R₁) (_ : IsLocalRing R₁),
        (IsLocalRing.maximalIdeal R₁).LiesOver p ∧
          (1 : R₁) ⊗ₜ[R] x ∈ J.map (Algebra.TensorProduct.includeRight : H →ₐ[R] R₁ ⊗[R] H)) :
    x ∈ J := by

  let J' : Submodule R H := J.restrictScalars R
  let xbar : H ⧸ J' := Submodule.Quotient.mk x
  suffices hx : xbar = 0 by
    have := (Submodule.Quotient.mk_eq_zero J').1 hx
    exact this
  let S : Submodule R (H ⧸ J') := Submodule.span R {xbar}
  suffices hS : Subsingleton S by
    have : (⟨xbar, Submodule.mem_span_singleton_self xbar⟩ : S) = 0 := Subsingleton.elim _ _
    exact congrArg Subtype.val this
  refine subsingleton_of_forall_flat_local (R := R) S fun p hp => ?_
  obtain ⟨R₁, _, _, _, _, hlies, hmem⟩ := h p hp
  refine ⟨R₁, inferInstance, inferInstance, inferInstance, inferInstance, hlies, ?_⟩

  have h0 : (1 : R₁) ⊗ₜ[R] xbar = 0 := by
    have hmem' : (1 : R₁) ⊗ₜ[R] x ∈ (J.map (Algebra.TensorProduct.includeRight : H →ₐ[R] R₁ ⊗[R] H)).restrictScalars R := hmem
    rw [Ideal.map_includeRight_eq] at hmem'
    obtain ⟨w, hw⟩ := hmem'
    have : (1 : R₁) ⊗ₜ[R] xbar = LinearMap.lTensor R₁ J'.mkQ ((1 : R₁) ⊗ₜ[R] x) := by
      rw [LinearMap.lTensor_tmul]; rfl
    rw [this, ← hw, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have hc : J'.mkQ ∘ₗ (Submodule.restrictScalars R J).subtype = 0 := by
      ext j; simp [J']
    rw [hc, LinearMap.lTensor_zero, LinearMap.zero_apply]

  have hinj : Function.Injective (LinearMap.lTensor R₁ S.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ S.injective_subtype
  refine ⟨fun a b => hinj ?_⟩
  have hz : ∀ t : R₁ ⊗[R] S, LinearMap.lTensor R₁ S.subtype t = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]
    | tmul r s =>
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 s.2
        rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, ← hc, TensorProduct.tmul_smul,
          show r ⊗ₜ[R] xbar = r • ((1 : R₁) ⊗ₜ[R] xbar) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
          h0, smul_zero, smul_zero]
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
  rw [hz a, hz b]

end LocalDescent
end HopfAlgebra

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

namespace HopfAlgebra p2m_export "HopfAlgebra" "mk hopfKer IsHopfGalois isHopfGalois_iff_ker_le_span_of_surjective hopfKer_baseChange_toSubmodule_eq_range_baseChange" namespace LocalDescent end HopfAlgebra.LocalDescent
p2m_open_scoped "HopfAlgebra" in

theorem HopfAlgebra.LocalDescent.isHopfGalois_of_forall_flat_local
    (R : Type) [CommRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Flat R H]
    (H' : Type) [CommRing H'] [HopfAlgebra R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc)
    (hloc : ∀ (p : Ideal R), p.IsMaximal →
      ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (_ : Module.Flat R R₁) (_ : IsLocalRing R₁),
        (IsLocalRing.maximalIdeal R₁).LiesOver p ∧
        HopfAlgebra.IsHopfGalois (Bialgebra.TensorProduct.map (BialgHom.id R₁ R₁) qc :
            TensorProduct R R₁ H →ₐc[R₁] TensorProduct R R₁ H')) :
    HopfAlgebra.IsHopfGalois qc := by
  refine (HopfAlgebra.isHopfGalois_iff_ker_le_span_of_surjective qc hqc).2 fun x hx => ?_
  apply HopfAlgebra.LocalDescent.mem_of_forall_flat_local_one_tmul_mem (R := R) _ x
  intro p hp
  obtain ⟨R₁, _, _, _, _, hlies, hgal⟩ := hloc p hp
  refine ⟨R₁, inferInstance, inferInstance, inferInstance, inferInstance, hlies, ?_⟩
  let qc₁ := (Bialgebra.TensorProduct.map (BialgHom.id R₁ R₁) qc : TensorProduct R R₁ H →ₐc[R₁] TensorProduct R R₁ H')
  have hqc₁_tmul : ∀ (r : R₁) (h : H), qc₁ (r ⊗ₜ[R] h) = r ⊗ₜ[R] qc h := fun _ _ => rfl
  have hsurj₁ : Function.Surjective qc₁ := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul r h' =>
        obtain ⟨h, rfl⟩ := hqc h'
        exact ⟨r ⊗ₜ[R] h, hqc₁_tmul r h⟩
    | add a b ha hb =>
        obtain ⟨a', rfl⟩ := ha
        obtain ⟨b', rfl⟩ := hb
        exact ⟨a' + b', map_add _ _ _⟩
  have hker₁ := (HopfAlgebra.isHopfGalois_iff_ker_le_span_of_surjective qc₁ hsurj₁).1 hgal
  have hx0 : qc x = 0 := hx
  have hx₁ : (1 : R₁) ⊗ₜ[R] x ∈ RingHom.ker (qc₁ : TensorProduct R R₁ H →ₐ[R₁] TensorProduct R R₁ H') := by
    rw [RingHom.mem_ker]
    change qc₁ ((1 : R₁) ⊗ₜ[R] x) = 0
    rw [hqc₁_tmul, hx0, TensorProduct.tmul_zero]
  exact HopfAlgebra.span_augHopfKer_baseChange_le_map_includeRight R₁ qc (hker₁ hx₁)

theorem solution
    (R : Type) [CommRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Flat R H]
    (H' : Type) [CommRing H'] [HopfAlgebra R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc)
    (hloc : ∀ (p : Ideal R), p.IsMaximal →
      ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (_ : Module.Flat R R₁) (_ : IsLocalRing R₁),
        (IsLocalRing.maximalIdeal R₁).LiesOver p ∧
        HopfAlgebra.IsHopfGalois (Bialgebra.TensorProduct.map (BialgHom.id R₁ R₁) qc :
            TensorProduct R R₁ H →ₐc[R₁] TensorProduct R R₁ H')) :
    HopfAlgebra.IsHopfGalois qc :=
  HopfAlgebra.LocalDescent.isHopfGalois_of_forall_flat_local R H H' qc hqc hloc

end S_HopfAlgebra_isHopfGalois_of_forall_isLocalRing_isHopfGalois_baseChange_of_flat
end P2MW
export P2MW.S_HopfAlgebra_isHopfGalois_of_forall_isLocalRing_isHopfGalois_baseChange_of_flat (solution)
