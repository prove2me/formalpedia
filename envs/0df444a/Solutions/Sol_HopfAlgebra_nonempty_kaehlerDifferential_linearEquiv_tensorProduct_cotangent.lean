-- Prove2me | solution 1 for HopfAlgebra.nonempty_kaehlerDifferential_linearEquiv_tensorProduct_cotangent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1d5d68f6-0970-5ff4-94ce-0cab1ff8fcb6

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_nonempty_kaehlerDifferential_linearEquiv_tensorProduct_cotangent

set_option autoImplicit false

open scoped TensorProduct

universe u v

set_option maxHeartbeats 800000

open TensorProduct

namespace Ws47
namespace INVDIFF
open HopfAlgebra

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]

noncomputable def antipodeAlgHom : H →ₐ[R] H :=
  AlgHom.ofLinearMap (antipode R (A := H)) antipode_one (fun a b => by rw [antipode_mul, mul_comm])

@[scoped simp] theorem antipodeAlgHom_apply (a : H) : antipodeAlgHom (R := R) a = antipode R a := rfl

noncomputable def shearRight : H →ₐ[R] H ⊗[R] H :=
  (Algebra.TensorProduct.map (antipodeAlgHom (R := R) (H := H)) (AlgHom.id R H)).comp
    (Bialgebra.comulAlgHom R H)

theorem shearRight_apply (b : H) {ιr : Type*} (r : Coalgebra.Repr R b ιr) :
    shearRight (R := R) b = ∑ i ∈ r.index, antipode R (r.left i) ⊗ₜ[R] r.right i := by
  change Algebra.TensorProduct.map (antipodeAlgHom (R := R) (H := H)) (AlgHom.id R H)
    (Coalgebra.comul (R := R) b) = _
  rw [← r.eq, map_sum]
  simp only [Algebra.TensorProduct.map_tmul, antipodeAlgHom_apply, AlgHom.id_apply]

noncomputable def shear : H ⊗[R] H →ₐ[R] H ⊗[R] H :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft (S := R)) (shearRight (R := R))
    (fun _ _ => .all _ _)

theorem shear_tmul (a b : H) {ιr : Type*} (r : Coalgebra.Repr R b ιr) :
    shear (R := R) (a ⊗ₜ[R] b) = ∑ i ∈ r.index, (a * antipode R (r.left i)) ⊗ₜ[R] r.right i := by
  rw [shear, Algebra.TensorProduct.lift_tmul, shearRight_apply b r, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem lmul'_shear_one_tmul (b : H) :
    Algebra.TensorProduct.lmul' (S := H) R (shear (R := R) ((1 : H) ⊗ₜ[R] b)) =
      algebraMap R H (Coalgebra.counit b) := by
  rw [shear_tmul 1 b (Coalgebra.Repr.arbitrary R b), map_sum]
  simp only [one_mul, Algebra.TensorProduct.lmul'_apply_tmul]
  exact sum_antipode_mul_eq_algebraMap_counit _

theorem shear_comul (b : H) {ιr : Type*} (r : Coalgebra.Repr R b ιr) :
    ∑ i ∈ r.index, shear (R := R) (r.left i ⊗ₜ[R] r.right i) = (1 : H) ⊗ₜ[R] b := by

  let T : H ⊗[R] (H ⊗[R] H) →ₗ[R] H ⊗[R] H :=
    LinearMap.rTensor H (LinearMap.mul' R H ∘ₗ LinearMap.lTensor H (antipode R)) ∘ₗ
      (TensorProduct.assoc R H H H).symm.toLinearMap
  have hT : ∀ x y z : H, T (x ⊗ₜ[R] (y ⊗ₜ[R] z)) = (x * antipode R y) ⊗ₜ[R] z := fun x y z => by
    simp only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul,
      LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.mul'_apply]
  let a₁ := fun i : r.ι => Coalgebra.Repr.arbitrary R (r.left i)
  let a₂ := fun i : r.ι => Coalgebra.Repr.arbitrary R (r.right i)
  have hco := congrArg T (Coalgebra.sum_tmul_tmul_eq r a₁ a₂)
  simp only [map_sum, hT] at hco

  have hleft : ∑ i ∈ r.index, ∑ j ∈ (a₁ i).index,
      ((a₁ i).left j * antipode R ((a₁ i).right j)) ⊗ₜ[R] r.right i = (1 : H) ⊗ₜ[R] b := by
    have h2 : ∑ i ∈ r.index, algebraMap R H (Coalgebra.counit (r.left i)) ⊗ₜ[R] r.right i
        = (1 : H) ⊗ₜ[R] b := by
      have h := congrArg (LinearMap.rTensor H (Algebra.linearMap R H)) (Coalgebra.sum_counit_tmul_eq r)
      simpa only [map_sum, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one] using h
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sum_tmul, sum_mul_antipode_eq_algebraMap_counit (a₁ i)]

  have hright : ∑ i ∈ r.index, ∑ j ∈ (a₂ i).index,
      (r.left i * antipode R ((a₂ i).left j)) ⊗ₜ[R] (a₂ i).right j =
        ∑ i ∈ r.index, shear (R := R) (r.left i ⊗ₜ[R] r.right i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [shear_tmul (r.left i) (r.right i) (a₂ i)]
  rw [← hright, ← hco, hleft]

theorem kaehlerDifferential_ideal_le_sq
    (hI : RingHom.ker (Bialgebra.counitAlgHom R H) = RingHom.ker (Bialgebra.counitAlgHom R H) ^ 2) :
    KaehlerDifferential.ideal R H ≤ KaehlerDifferential.ideal R H ^ 2 := by
  set I : Ideal H := RingHom.ker (Bialgebra.counitAlgHom R H) with hIdef

  set K : Ideal (H ⊗[R] H) := I.map (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H))
    with hK
  have hKsq : K = K ^ 2 := by
    rw [hK, ← Ideal.map_pow, ← hI]

  have hKJ : K.map (shear (R := R) (H := H)) ≤ KaehlerDifferential.ideal R H := by
    rw [Ideal.map_le_iff_le_comap, hK, Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, Ideal.mem_comap, KaehlerDifferential.ideal, RingHom.mem_ker]
    change Algebra.TensorProduct.lmul' (S := H) R (shear (R := R) ((1 : H) ⊗ₜ[R] i)) = 0
    rw [lmul'_shear_one_tmul]
    have : Coalgebra.counit (R := R) i = 0 := by
      rwa [hIdef, RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hi
    rw [this, map_zero]

  have hgen : ∀ b : H, (1 : H) ⊗ₜ[R] b - b ⊗ₜ[R] 1 ∈ K.map (shear (R := R) (H := H)) := by
    intro b
    have r := Coalgebra.Repr.arbitrary R b

    have hpre : ∑ i ∈ r.index, r.left i ⊗ₜ[R] r.right i - b ⊗ₜ[R] (1 : H) ∈ K := by
      have h3 : ∑ i ∈ r.index, r.left i ⊗ₜ[R] algebraMap R H (Coalgebra.counit (r.right i))
          = b ⊗ₜ[R] (1 : H) := by
        have h := congrArg (LinearMap.lTensor H (Algebra.linearMap R H)) (Coalgebra.sum_tmul_counit_eq r)
        simpa only [map_sum, LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one] using h
      rw [← h3, ← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [← tmul_sub, show r.left i ⊗ₜ[R] (r.right i - algebraMap R H (Coalgebra.counit (r.right i)))
          = (r.left i ⊗ₜ[R] (1 : H)) * ((1 : H) ⊗ₜ[R] (r.right i - algebraMap R H (Coalgebra.counit (r.right i)))) by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
      refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
      rw [hIdef, RingHom.mem_ker, Bialgebra.counitAlgHom_apply, map_sub, Bialgebra.counit_algebraMap,
        sub_self]
    have himg := Ideal.mem_map_of_mem (shear (R := R) (H := H)) hpre
    rw [map_sub, map_sum, shear_comul b r, shear_tmul b 1 (Coalgebra.Repr.arbitrary R (1 : H))] at himg

    have hone : ∑ i ∈ (Coalgebra.Repr.arbitrary R (1 : H)).index,
        (b * antipode R ((Coalgebra.Repr.arbitrary R (1 : H)).left i)) ⊗ₜ[R]
          (Coalgebra.Repr.arbitrary R (1 : H)).right i = b ⊗ₜ[R] (1 : H) := by
      have := shear_tmul (R := R) b 1 (Coalgebra.Repr.arbitrary R (1 : H))
      rw [← this, shear, Algebra.TensorProduct.lift_tmul, map_one, mul_one,
        Algebra.TensorProduct.includeLeft_apply]
    rwa [hone] at himg

  have hJle : KaehlerDifferential.ideal R H ≤ K.map (shear (R := R) (H := H)) := by
    rw [← KaehlerDifferential.span_range_eq_ideal, Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    exact hgen b
  calc KaehlerDifferential.ideal R H ≤ K.map (shear (R := R) (H := H)) := hJle
    _ = (K.map (shear (R := R) (H := H))) ^ 2 := by rw [← Ideal.map_pow, ← hKsq]
    _ ≤ KaehlerDifferential.ideal R H ^ 2 := Ideal.pow_right_mono hKJ 2

theorem subsingleton_kaehlerDifferential
    (hI : RingHom.ker (Bialgebra.counitAlgHom R H) = RingHom.ker (Bialgebra.counitAlgHom R H) ^ 2) :
    Subsingleton (Ω[H⁄R]) := by
  have hle := kaehlerDifferential_ideal_le_sq (R := R) (H := H) hI
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := (KaehlerDifferential.ideal R H).toCotangent_surjective x
  obtain ⟨y, rfl⟩ := (KaehlerDifferential.ideal R H).toCotangent_surjective y
  rw [(Ideal.toCotangent_eq_zero _ _).2 (hle x.2), (Ideal.toCotangent_eq_zero _ _).2 (hle y.2)]

noncomputable def unshear : H ⊗[R] H →ₐ[R] H ⊗[R] H :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft (S := R)) (Bialgebra.comulAlgHom R H)
    (fun _ _ => .all _ _)

theorem unshear_tmul (a b : H) {ιr : Type*} (r : Coalgebra.Repr R b ιr) :
    unshear (R := R) (a ⊗ₜ[R] b) = ∑ i ∈ r.index, (a * r.left i) ⊗ₜ[R] r.right i := by
  rw [unshear, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.includeLeft_apply]
  change (a ⊗ₜ[R] (1 : H)) * Coalgebra.comul (R := R) b = _
  rw [← r.eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem shear_tmul_one (a : H) : shear (R := R) (a ⊗ₜ[R] (1 : H)) = a ⊗ₜ[R] 1 := by
  rw [shear, Algebra.TensorProduct.lift_tmul, map_one, mul_one, Algebra.TensorProduct.includeLeft_apply]

theorem unshear_tmul_one (a : H) : unshear (R := R) (a ⊗ₜ[R] (1 : H)) = a ⊗ₜ[R] 1 := by
  rw [unshear, Algebra.TensorProduct.lift_tmul, map_one, mul_one, Algebra.TensorProduct.includeLeft_apply]

theorem unshear_one_tmul (b : H) : unshear (R := R) ((1 : H) ⊗ₜ[R] b) = Coalgebra.comul (R := R) b := by
  rw [unshear, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

theorem unshear_shear_one_tmul (b : H) : unshear (R := R) (shear (R := R) ((1 : H) ⊗ₜ[R] b)) = (1 : H) ⊗ₜ[R] b := by
  have r := Coalgebra.Repr.arbitrary R b
  rw [shear_tmul 1 b r, map_sum]
  simp only [one_mul]

  let T : H ⊗[R] (H ⊗[R] H) →ₗ[R] H ⊗[R] H :=
    LinearMap.rTensor H (LinearMap.mul' R H ∘ₗ LinearMap.rTensor H (antipode R)) ∘ₗ
      (TensorProduct.assoc R H H H).symm.toLinearMap
  have hT : ∀ x y z : H, T (x ⊗ₜ[R] (y ⊗ₜ[R] z)) = (antipode R x * y) ⊗ₜ[R] z := fun x y z => by
    simp only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul,
      LinearMap.rTensor_tmul, LinearMap.mul'_apply]
  let a₁ := fun i : r.ι => Coalgebra.Repr.arbitrary R (r.left i)
  let a₂ := fun i : r.ι => Coalgebra.Repr.arbitrary R (r.right i)
  have hco := congrArg T (Coalgebra.sum_tmul_tmul_eq r a₁ a₂)
  simp only [map_sum, hT] at hco
  have hleft : ∑ i ∈ r.index, ∑ j ∈ (a₁ i).index,
      (antipode R ((a₁ i).left j) * (a₁ i).right j) ⊗ₜ[R] r.right i = (1 : H) ⊗ₜ[R] b := by
    have h2 : ∑ i ∈ r.index, algebraMap R H (Coalgebra.counit (r.left i)) ⊗ₜ[R] r.right i
        = (1 : H) ⊗ₜ[R] b := by
      have h := congrArg (LinearMap.rTensor H (Algebra.linearMap R H)) (Coalgebra.sum_counit_tmul_eq r)
      simpa only [map_sum, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one] using h
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sum_tmul, sum_antipode_mul_eq_algebraMap_counit (a₁ i)]
  have hright : ∑ i ∈ r.index, ∑ j ∈ (a₂ i).index,
      (antipode R (r.left i) * (a₂ i).left j) ⊗ₜ[R] (a₂ i).right j =
        ∑ i ∈ r.index, unshear (R := R) (antipode R (r.left i) ⊗ₜ[R] r.right i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [unshear_tmul _ _ (a₂ i)]
  rw [← hright, ← hco, hleft]

theorem shear_unshear_one_tmul (b : H) : shear (R := R) (unshear (R := R) ((1 : H) ⊗ₜ[R] b)) = (1 : H) ⊗ₜ[R] b := by
  have r := Coalgebra.Repr.arbitrary R b
  rw [unshear_tmul 1 b r, map_sum]
  simp only [one_mul]
  exact shear_comul b r

noncomputable def shearEquiv : H ⊗[R] H ≃ₐ[R] H ⊗[R] H :=
  AlgEquiv.ofAlgHom (shear (R := R) (H := H)) (unshear (R := R) (H := H))
    (by
      apply Algebra.TensorProduct.ext
      · ext a
        simp [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply, unshear_tmul_one, shear_tmul_one]
      · ext b
        simp [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply, shear_unshear_one_tmul])
    (by
      apply Algebra.TensorProduct.ext
      · ext a
        simp [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply, unshear_tmul_one, shear_tmul_one]
      · ext b
        simp [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply, unshear_shear_one_tmul])

theorem shearEquiv_apply (x : H ⊗[R] H) : shearEquiv (R := R) (H := H) x = shear (R := R) x := rfl

noncomputable def extIdeal : Ideal (H ⊗[R] H) :=
  (RingHom.ker (Bialgebra.counitAlgHom R H)).map (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H))

theorem map_shear_extIdeal : (extIdeal (R := R) (H := H)).map (shear (R := R) (H := H)) = KaehlerDifferential.ideal R H := by
  set I : Ideal H := RingHom.ker (Bialgebra.counitAlgHom R H) with hIdef
  have hK : extIdeal (R := R) (H := H) = I.map (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H)) := rfl
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, hK, Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, Ideal.mem_comap, KaehlerDifferential.ideal, RingHom.mem_ker]
    change Algebra.TensorProduct.lmul' (S := H) R (shear (R := R) ((1 : H) ⊗ₜ[R] i)) = 0
    rw [lmul'_shear_one_tmul]
    have : Coalgebra.counit (R := R) i = 0 := by
      rwa [hIdef, RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hi
    rw [this, map_zero]
  · have hgen : ∀ b : H, (1 : H) ⊗ₜ[R] b - b ⊗ₜ[R] 1 ∈ (extIdeal (R := R) (H := H)).map (shear (R := R) (H := H)) := by
      intro b
      have r := Coalgebra.Repr.arbitrary R b
      have hpre : ∑ i ∈ r.index, r.left i ⊗ₜ[R] r.right i - b ⊗ₜ[R] (1 : H) ∈ extIdeal (R := R) (H := H) := by
        have h3 : ∑ i ∈ r.index, r.left i ⊗ₜ[R] algebraMap R H (Coalgebra.counit (r.right i))
            = b ⊗ₜ[R] (1 : H) := by
          have h := congrArg (LinearMap.lTensor H (Algebra.linearMap R H)) (Coalgebra.sum_tmul_counit_eq r)
          simpa only [map_sum, LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one] using h
        rw [← h3, ← Finset.sum_sub_distrib]
        refine Ideal.sum_mem _ fun i _ => ?_
        rw [← tmul_sub, show r.left i ⊗ₜ[R] (r.right i - algebraMap R H (Coalgebra.counit (r.right i)))
            = (r.left i ⊗ₜ[R] (1 : H)) * ((1 : H) ⊗ₜ[R] (r.right i - algebraMap R H (Coalgebra.counit (r.right i)))) by
              rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
        refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
        rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply, map_sub, Bialgebra.counit_algebraMap, sub_self]
      have himg := Ideal.mem_map_of_mem (shear (R := R) (H := H)) hpre
      rw [map_sub, map_sum, shear_comul b r, shear_tmul_one] at himg
      exact himg
    rw [← KaehlerDifferential.span_range_eq_ideal, Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    exact hgen b

theorem extIdeal_le_comap_shear :
    extIdeal (R := R) (H := H) ≤ (KaehlerDifferential.ideal R H).comap (shear (R := R) (H := H)) := by
  rw [← Ideal.map_le_iff_le_comap, map_shear_extIdeal]

theorem unshear_shear (x : H ⊗[R] H) : unshear (R := R) (shear (R := R) x) = x :=
  (shearEquiv (R := R) (H := H)).symm_apply_apply x

theorem shear_unshear (x : H ⊗[R] H) : shear (R := R) (unshear (R := R) x) = x :=
  (shearEquiv (R := R) (H := H)).apply_symm_apply x

theorem map_unshear_ideal : (KaehlerDifferential.ideal R H).map (unshear (R := R) (H := H)) = extIdeal (R := R) (H := H) := by
  rw [← map_shear_extIdeal]
  change Ideal.map (unshear (R := R) (H := H)).toRingHom (Ideal.map (shear (R := R) (H := H)).toRingHom _) = _
  rw [Ideal.map_map]
  have : (unshear (R := R) (H := H)).toRingHom.comp (shear (R := R) (H := H)).toRingHom = RingHom.id _ :=
    RingHom.ext fun x => unshear_shear x
  rw [this, Ideal.map_id]

theorem ideal_le_comap_unshear :
    KaehlerDifferential.ideal R H ≤ (extIdeal (R := R) (H := H)).comap (unshear (R := R) (H := H)) := by
  rw [← Ideal.map_le_iff_le_comap, map_unshear_ideal]

noncomputable def cotangentShear : (extIdeal (R := R) (H := H)).Cotangent ≃ₗ[R] (KaehlerDifferential.ideal R H).Cotangent :=
  LinearEquiv.ofLinear
    ((extIdeal (R := R) (H := H)).mapCotangent (KaehlerDifferential.ideal R H) (shear (R := R)) extIdeal_le_comap_shear)
    ((KaehlerDifferential.ideal R H).mapCotangent (extIdeal (R := R) (H := H)) (unshear (R := R)) ideal_le_comap_unshear)
    (by
      ext x
      obtain ⟨x, rfl⟩ := (KaehlerDifferential.ideal R H).toCotangent_surjective x
      rw [LinearMap.comp_apply, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent, LinearMap.id_apply]
      congr 1; ext; exact shear_unshear _)
    (by
      ext x
      obtain ⟨x, rfl⟩ := (extIdeal (R := R) (H := H)).toCotangent_surjective x
      rw [LinearMap.comp_apply, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent, LinearMap.id_apply]
      congr 1; ext; exact unshear_shear _)

theorem cotangentShear_toCotangent (x : ↥(extIdeal (R := R) (H := H))) :
    cotangentShear (R := R) (H := H) ((extIdeal (R := R) (H := H)).toCotangent x) =
      (KaehlerDifferential.ideal R H).toCotangent ⟨shear (R := R) x, extIdeal_le_comap_shear x.2⟩ :=
  Ideal.mapCotangent_toCotangent _ _ _ _ x

theorem cotangentShear_smul (a : H) (ξ : (extIdeal (R := R) (H := H)).Cotangent) :
    cotangentShear (R := R) (H := H) (a • ξ) = a • cotangentShear (R := R) (H := H) ξ := by
  obtain ⟨x, rfl⟩ := (extIdeal (R := R) (H := H)).toCotangent_surjective ξ

  have hK : a • (extIdeal (R := R) (H := H)).toCotangent x =
      (extIdeal (R := R) (H := H)).toCotangent ((algebraMap H (H ⊗[R] H) a) • x) := by
    rw [← IsScalarTower.algebraMap_smul (H ⊗[R] H) a, map_smul]
  have hJ : ∀ (y : ↥(KaehlerDifferential.ideal R H)), a • (KaehlerDifferential.ideal R H).toCotangent y =
      (KaehlerDifferential.ideal R H).toCotangent ((algebraMap H (H ⊗[R] H) a) • y) := by
    intro y
    rw [← IsScalarTower.algebraMap_smul (H ⊗[R] H) a, map_smul]
  rw [hK, cotangentShear_toCotangent, cotangentShear_toCotangent, hJ]
  congr 1
  ext
  change shear (R := R) ((algebraMap H (H ⊗[R] H) a) • (x : H ⊗[R] H)) = (algebraMap H (H ⊗[R] H) a) • shear (R := R) (x : H ⊗[R] H)
  have ha : algebraMap H (H ⊗[R] H) a = a ⊗ₜ[R] (1 : H) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [smul_eq_mul, smul_eq_mul, map_mul, ha, shear_tmul_one]

noncomputable abbrev augI : Ideal H := RingHom.ker (Bialgebra.counitAlgHom R H)

theorem mem_augI {x : H} : x ∈ augI (R := R) (H := H) ↔ Coalgebra.counit (R := R) x = 0 := by
  rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply]

theorem tmul_mem_extIdeal (u : H) {j : H} (hj : j ∈ augI (R := R) (H := H)) :
    u ⊗ₜ[R] j ∈ extIdeal (R := R) (H := H) := by
  have : u ⊗ₜ[R] j = (u ⊗ₜ[R] (1 : H)) * ((1 : H) ⊗ₜ[R] j) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hj)

theorem tmul_mem_extIdeal_sq (u : H) {i j : H} (hi : i ∈ augI (R := R) (H := H)) (hj : j ∈ augI (R := R) (H := H)) :
    u ⊗ₜ[R] (i * j) ∈ extIdeal (R := R) (H := H) ^ 2 := by
  have : u ⊗ₜ[R] (i * j) = (u ⊗ₜ[R] i) * ((1 : H) ⊗ₜ[R] j) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [this, pow_two]
  exact Ideal.mul_mem_mul (tmul_mem_extIdeal u hi) (tmul_mem_extIdeal 1 hj)

noncomputable def projI : H →ₗ[R] ↥(augI (R := R) (H := H)) where
  toFun x := ⟨x - algebraMap R H (Coalgebra.counit (R := R) x), by
    rw [mem_augI, map_sub, Bialgebra.counit_algebraMap, sub_self]⟩
  map_add' x y := by ext; simp only [map_add, Submodule.coe_add]; ring
  map_smul' r x := by
    apply Subtype.ext
    change r • x - algebraMap R H (Coalgebra.counit (R := R) (r • x)) =
      r • (x - algebraMap R H (Coalgebra.counit (R := R) x))
    rw [map_smul, smul_eq_mul, map_mul, ← Algebra.smul_def, smul_sub]

theorem projI_apply_coe (x : H) : ((projI (R := R) (H := H) x : ↥(augI (R := R) (H := H))) : H) =
    x - algebraMap R H (Coalgebra.counit (R := R) x) := rfl

theorem projI_of_mem {x : H} (hx : x ∈ augI (R := R) (H := H)) : projI (R := R) (H := H) x = ⟨x, hx⟩ := by
  ext; rw [projI_apply_coe, (mem_augI).1 hx, map_zero, sub_zero]

theorem toCotangent_smul_tower {A : Type v} [CommRing A] [Algebra R A] (J : Ideal A) (r : R) (y : ↥J) :
    J.toCotangent (r • y) = r • J.toCotangent y := by
  rw [← algebraMap_smul A r y, map_smul, algebraMap_smul]

noncomputable def fwd₀ : H ⊗[R] ↥(augI (R := R) (H := H)) →ₗ[R] (extIdeal (R := R) (H := H)).Cotangent :=
  TensorProduct.lift (LinearMap.mk₂ R
    (fun (u : H) (i : ↥(augI (R := R) (H := H))) =>
      (extIdeal (R := R) (H := H)).toCotangent ⟨u ⊗ₜ[R] (i : H), tmul_mem_extIdeal u i.2⟩)
    (fun u v i => by
      rw [← map_add]
      exact congrArg _ (Subtype.ext (TensorProduct.add_tmul u v (i : H))))
    (fun r u i => by
      rw [← toCotangent_smul_tower]
      exact congrArg _ (Subtype.ext (TensorProduct.smul_tmul' r u (i : H)).symm))
    (fun u i j => by
      rw [← map_add]
      exact congrArg _ (Subtype.ext (TensorProduct.tmul_add u (i : H) (j : H))))
    (fun r u i => by
      rw [← toCotangent_smul_tower]
      exact congrArg _ (Subtype.ext (by
        change u ⊗ₜ[R] ((r • i : ↥(augI (R := R) (H := H))) : H) = r • (u ⊗ₜ[R] (i : H))
        rw [← TensorProduct.tmul_smul]
        rfl))))

theorem fwd₀_tmul (u : H) (i : ↥(augI (R := R) (H := H))) :
    fwd₀ (R := R) (H := H) (u ⊗ₜ[R] i) = (extIdeal (R := R) (H := H)).toCotangent ⟨u ⊗ₜ[R] (i : H), tmul_mem_extIdeal u i.2⟩ :=
  by rw [fwd₀, TensorProduct.lift.tmul]; rfl

noncomputable def bwd₀ : H ⊗[R] H →ₗ[R] H ⊗[R] (augI (R := R) (H := H)).Cotangent :=
  LinearMap.lTensor H ((augI (R := R) (H := H)).toCotangent ∘ₗ projI (R := R) (H := H))

theorem bwd₀_tmul (u x : H) :
    bwd₀ (R := R) (H := H) (u ⊗ₜ[R] x) = u ⊗ₜ[R] (augI (R := R) (H := H)).toCotangent (projI (R := R) (H := H) x) :=
  LinearMap.lTensor_tmul _ _ _ _

theorem bwd₀_mul_one_tmul_mul {i j : H} (hi : i ∈ augI (R := R) (H := H)) (hj : j ∈ augI (R := R) (H := H))
    (z : H ⊗[R] H) : bwd₀ (R := R) (H := H) (z * ((1 : H) ⊗ₜ[R] (i * j))) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero]
  | tmul u w =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, bwd₀_tmul]
    have hwij : w * (i * j) ∈ augI (R := R) (H := H) := Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hj)
    rw [projI_of_mem hwij]
    have hsq : w * (i * j) ∈ augI (R := R) (H := H) ^ 2 := by
      rw [pow_two, show w * (i * j) = (w * i) * j by ring]
      exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hi) hj
    rw [(Ideal.toCotangent_eq_zero _ _).2 hsq, TensorProduct.tmul_zero]
  | add x y hx hy => rw [add_mul, map_add, hx, hy, add_zero]

theorem bwd₀_mul_gen_mul (i : H) (hi : i ∈ augI (R := R) (H := H)) {b : H ⊗[R] H}
    (hb : b ∈ extIdeal (R := R) (H := H)) :
    ∀ z : H ⊗[R] H, bwd₀ (R := R) (H := H) (z * (((1 : H) ⊗ₜ[R] i) * b)) = 0 := by
  have hb' : b ∈ Submodule.span (H ⊗[R] H) (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H) '' (augI (R := R) (H := H))) := by
    rwa [extIdeal, Ideal.map, ← Ideal.submodule_span_eq] at hb
  clear hb
  induction hb' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    intro z
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact bwd₀_mul_one_tmul_mul hi hj z
  | zero => intro z; rw [mul_zero, mul_zero, map_zero]
  | add x y _ _ hx hy => intro z; rw [mul_add, mul_add, map_add, hx, hy, add_zero]
  | smul w x _ hx =>
    intro z
    have : z * (((1 : H) ⊗ₜ[R] i) * (w • x)) = (z * w) * (((1 : H) ⊗ₜ[R] i) * x) := by
      rw [smul_eq_mul]; ring
    rw [this]; exact hx (z * w)

theorem bwd₀_mul_mem (a b : H ⊗[R] H) (ha : a ∈ extIdeal (R := R) (H := H)) (hb : b ∈ extIdeal (R := R) (H := H)) :
    bwd₀ (R := R) (H := H) (a * b) = 0 := by
  have ha' : a ∈ Submodule.span (H ⊗[R] H) (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H) '' (augI (R := R) (H := H))) := by
    rwa [extIdeal, Ideal.map, ← Ideal.submodule_span_eq] at ha
  clear ha
  suffices h : ∀ z : H ⊗[R] H, bwd₀ (R := R) (H := H) (z * (a * b)) = 0 by simpa using h 1
  induction ha' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    intro z
    rw [Algebra.TensorProduct.includeRight_apply]
    exact bwd₀_mul_gen_mul i hi hb z
  | zero => intro z; rw [zero_mul, mul_zero, map_zero]
  | add x y _ _ hx hy => intro z; rw [add_mul, mul_add, map_add, hx, hy, add_zero]
  | smul w x _ hx =>
    intro z
    have : z * ((w • x) * b) = (z * w) * (x * b) := by rw [smul_eq_mul]; ring
    rw [this]; exact hx (z * w)

theorem bwd₀_eq_zero_of_mem_sq {k : H ⊗[R] H} (hk : k ∈ extIdeal (R := R) (H := H) ^ 2) :
    bwd₀ (R := R) (H := H) k = 0 := by
  rw [pow_two] at hk
  refine Submodule.mul_induction_on hk (fun a ha b hb => bwd₀_mul_mem a b ha hb) (fun x y hx hy => ?_)
  rw [map_add, hx, hy, add_zero]

noncomputable def bwdK : ↥(extIdeal (R := R) (H := H)) →ₗ[R] H ⊗[R] (augI (R := R) (H := H)).Cotangent :=
  (bwd₀ (R := R) (H := H)).comp ((extIdeal (R := R) (H := H)).restrictScalars R).subtype

theorem bwdK_apply (x : ↥(extIdeal (R := R) (H := H))) : bwdK (R := R) (H := H) x = bwd₀ (R := R) (H := H) x := rfl

noncomputable def bwd : (extIdeal (R := R) (H := H)).Cotangent →ₗ[R] H ⊗[R] (augI (R := R) (H := H)).Cotangent :=
  ((((extIdeal (R := R) (H := H)) • ⊤ : Submodule (H ⊗[R] H) ↥(extIdeal (R := R) (H := H))).restrictScalars R).liftQ
      (bwdK (R := R) (H := H)) (by
        intro x hx
        rw [LinearMap.mem_ker, bwdK_apply]
        apply bwd₀_eq_zero_of_mem_sq
        have h0 : (extIdeal (R := R) (H := H)).toCotangent x = 0 :=
          (Submodule.Quotient.mk_eq_zero _).2 hx
        exact (Ideal.toCotangent_eq_zero _ _).1 h0)).comp
    (Submodule.Quotient.restrictScalarsEquiv R
      ((extIdeal (R := R) (H := H)) • ⊤ : Submodule (H ⊗[R] H) ↥(extIdeal (R := R) (H := H)))).symm.toLinearMap

theorem bwd_toCotangent (x : ↥(extIdeal (R := R) (H := H))) :
    bwd (R := R) (H := H) ((extIdeal (R := R) (H := H)).toCotangent x) = bwd₀ (R := R) (H := H) x := by
  rw [bwd, LinearMap.comp_apply]
  change ((((extIdeal (R := R) (H := H)) • ⊤ : Submodule (H ⊗[R] H) ↥(extIdeal (R := R) (H := H))).restrictScalars R).liftQ
      (bwdK (R := R) (H := H)) _)
    ((Submodule.Quotient.restrictScalarsEquiv R ((extIdeal (R := R) (H := H)) • ⊤ : Submodule (H ⊗[R] H) ↥(extIdeal (R := R) (H := H)))).symm
      (Submodule.Quotient.mk x)) = _
  rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply]
  rfl

theorem fwd₀_vanishes :
    LinearMap.ker (LinearMap.lTensor H ((augI (R := R) (H := H)).toCotangent.restrictScalars R)) ≤ LinearMap.ker (fwd₀ (R := R) (H := H)) := by
  have h0 : Function.Exact
      ((((augI (R := R) (H := H)) • ⊤ : Submodule H ↥(augI (R := R) (H := H))).subtype.restrictScalars R))
      ((augI (R := R) (H := H)).toCotangent.restrictScalars R) :=
    LinearMap.exact_subtype_mkQ ((augI (R := R) (H := H)) • ⊤ : Submodule H ↥(augI (R := R) (H := H)))
  have hex := lTensor_exact H h0 (augI (R := R) (H := H)).toCotangent_surjective
  have hker := hex.linearMap_ker_eq
  rw [hker, LinearMap.range_le_iff_comap, eq_top_iff]
  rintro t -
  rw [Submodule.mem_comap, LinearMap.mem_ker]
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul u y =>
    rw [LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, Submodule.subtype_apply, fwd₀_tmul, Ideal.toCotangent_eq_zero]
    have hy2 : ((y : ↥(augI (R := R) (H := H))) : H) ∈ augI (R := R) (H := H) ^ 2 :=
      (Ideal.toCotangent_eq_zero _ _).1 ((Submodule.Quotient.mk_eq_zero _).2 y.2)
    change u ⊗ₜ[R] ((y : ↥(augI (R := R) (H := H))) : H) ∈ extIdeal (R := R) (H := H) ^ 2
    rw [pow_two] at hy2
    refine Submodule.mul_induction_on hy2 (fun i hi j hj => tmul_mem_extIdeal_sq u hi hj) (fun a b ha hb => ?_)
    rw [TensorProduct.tmul_add]; exact Ideal.add_mem _ ha hb
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]

noncomputable def fwd : H ⊗[R] (augI (R := R) (H := H)).Cotangent →ₗ[R] (extIdeal (R := R) (H := H)).Cotangent :=
  ((LinearMap.ker (LinearMap.lTensor H ((augI (R := R) (H := H)).toCotangent.restrictScalars R))).liftQ (fwd₀ (R := R) (H := H)) fwd₀_vanishes).comp
    (LinearMap.quotKerEquivOfSurjective _ (LinearMap.lTensor_surjective H (g := ((augI (R := R) (H := H)).toCotangent.restrictScalars R)) (augI (R := R) (H := H)).toCotangent_surjective)).symm.toLinearMap

theorem fwd_tmul (u : H) (i : ↥(augI (R := R) (H := H))) :
    fwd (R := R) (H := H) (u ⊗ₜ[R] (augI (R := R) (H := H)).toCotangent i) =
      (extIdeal (R := R) (H := H)).toCotangent ⟨u ⊗ₜ[R] (i : H), tmul_mem_extIdeal u i.2⟩ := by
  have h1 : u ⊗ₜ[R] (augI (R := R) (H := H)).toCotangent i = LinearMap.lTensor H ((augI (R := R) (H := H)).toCotangent.restrictScalars R) (u ⊗ₜ[R] i) := by
    rw [LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply]
  rw [fwd, LinearMap.comp_apply, h1, LinearEquiv.coe_toLinearMap,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply, fwd₀_tmul]

theorem bwd_fwd (t : H ⊗[R] (augI (R := R) (H := H)).Cotangent) : bwd (R := R) (H := H) (fwd (R := R) (H := H) t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul u ξ =>
    obtain ⟨i, rfl⟩ := (augI (R := R) (H := H)).toCotangent_surjective ξ
    rw [fwd_tmul, bwd_toCotangent, bwd₀_tmul, projI_of_mem i.2]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem extIdeal_le_span :
    (extIdeal (R := R) (H := H)).restrictScalars R ≤
      Submodule.span R {t : H ⊗[R] H | ∃ (u j : H), j ∈ augI (R := R) (H := H) ∧ t = u ⊗ₜ[R] j} := by

  have hmul : ∀ z t : H ⊗[R] H, t ∈ Submodule.span R {t : H ⊗[R] H | ∃ (u j : H), j ∈ augI (R := R) (H := H) ∧ t = u ⊗ₜ[R] j} →
      z * t ∈ Submodule.span R {t : H ⊗[R] H | ∃ (u j : H), j ∈ augI (R := R) (H := H) ∧ t = u ⊗ₜ[R] j} := by
    intro z t ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, j, hj, rfl⟩ := hx
      induction z using TensorProduct.induction_on with
      | zero => rw [zero_mul]; exact Submodule.zero_mem _
      | tmul x y =>
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        exact Submodule.subset_span ⟨x * u, y * j, Ideal.mul_mem_left _ _ hj, rfl⟩
      | add a b ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx
  intro k hk
  have hk' : k ∈ Submodule.span (H ⊗[R] H) (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H) '' (augI (R := R) (H := H))) := by
    rwa [Submodule.restrictScalars_mem, extIdeal, Ideal.map, ← Ideal.submodule_span_eq] at hk
  clear hk
  induction hk' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact Submodule.subset_span ⟨1, j, hj, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul w x _ hx => rw [smul_eq_mul]; exact hmul w x hx

theorem span_le_extIdeal :
    Submodule.span R {t : H ⊗[R] H | ∃ (u j : H), j ∈ augI (R := R) (H := H) ∧ t = u ⊗ₜ[R] j} ≤
      (extIdeal (R := R) (H := H)).restrictScalars R := by
  rw [Submodule.span_le]
  rintro _ ⟨u, j, hj, rfl⟩
  exact tmul_mem_extIdeal u hj

theorem fwd_bwd (ξ : (extIdeal (R := R) (H := H)).Cotangent) : fwd (R := R) (H := H) (bwd (R := R) (H := H) ξ) = ξ := by
  obtain ⟨x, rfl⟩ := (extIdeal (R := R) (H := H)).toCotangent_surjective ξ
  rw [bwd_toCotangent]

  suffices h : ∀ (k : H ⊗[R] H), k ∈ Submodule.span R {t : H ⊗[R] H | ∃ (u j : H), j ∈ augI (R := R) (H := H) ∧ t = u ⊗ₜ[R] j} →
      ∀ (hk : k ∈ extIdeal (R := R) (H := H)),
        fwd (R := R) (H := H) (bwd₀ (R := R) (H := H) k) = (extIdeal (R := R) (H := H)).toCotangent ⟨k, hk⟩ by
    exact h x (extIdeal_le_span x.2) x.2
  intro k hk
  induction hk using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨u, j, hj, rfl⟩ := ht
    intro hk
    rw [bwd₀_tmul, projI_of_mem hj, fwd_tmul]
  | zero =>
    intro hk
    rw [map_zero, map_zero]
    have : (⟨0, hk⟩ : ↥(extIdeal (R := R) (H := H))) = 0 := rfl
    rw [this, map_zero]
  | add a b ha' hb' ha hb =>
    intro hk
    have hak : a ∈ extIdeal (R := R) (H := H) := span_le_extIdeal ha'
    have hbk : b ∈ extIdeal (R := R) (H := H) := span_le_extIdeal hb'
    rw [map_add, map_add, ha hak, hb hbk, ← map_add]
    rfl
  | smul r a ha' ha =>
    intro hk
    have hak : a ∈ extIdeal (R := R) (H := H) := span_le_extIdeal ha'
    rw [map_smul, map_smul, ha hak, ← toCotangent_smul_tower]
    rfl

theorem fwd_smul (a : H) (t : H ⊗[R] (augI (R := R) (H := H)).Cotangent) :
    fwd (R := R) (H := H) (a • t) = a • fwd (R := R) (H := H) t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul u ξ =>
    obtain ⟨i, rfl⟩ := (augI (R := R) (H := H)).toCotangent_surjective ξ
    rw [TensorProduct.smul_tmul', fwd_tmul, fwd_tmul]
    have hK : ∀ (y : ↥(extIdeal (R := R) (H := H))), a • (extIdeal (R := R) (H := H)).toCotangent y =
        (extIdeal (R := R) (H := H)).toCotangent ((algebraMap H (H ⊗[R] H) a) • y) := by
      intro y
      rw [← IsScalarTower.algebraMap_smul (H ⊗[R] H) a, map_smul]
    rw [hK]
    congr 1
    ext
    change (a • u) ⊗ₜ[R] (i : H) = (algebraMap H (H ⊗[R] H) a) • (u ⊗ₜ[R] (i : H))
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul,
      smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem fwd_comp_bwd : (fwd (R := R) (H := H)).comp (bwd (R := R) (H := H)) = LinearMap.id :=
  LinearMap.ext fun ξ => fwd_bwd ξ

theorem bwd_comp_fwd : (bwd (R := R) (H := H)).comp (fwd (R := R) (H := H)) = LinearMap.id :=
  LinearMap.ext fun t => bwd_fwd t

noncomputable def fwdEquiv : H ⊗[R] (augI (R := R) (H := H)).Cotangent ≃ₗ[R] (extIdeal (R := R) (H := H)).Cotangent :=
  LinearEquiv.ofLinear (fwd (R := R) (H := H)) (bwd (R := R) (H := H)) fwd_comp_bwd bwd_comp_fwd

noncomputable def invDiffR : H ⊗[R] (augI (R := R) (H := H)).Cotangent ≃ₗ[R] (KaehlerDifferential.ideal R H).Cotangent :=
  (fwdEquiv (R := R) (H := H)).trans (cotangentShear (R := R) (H := H))

theorem invDiffR_apply (t : H ⊗[R] (augI (R := R) (H := H)).Cotangent) :
    invDiffR (R := R) (H := H) t = cotangentShear (R := R) (H := H) (fwd (R := R) (H := H) t) := rfl

noncomputable def invDiff : H ⊗[R] (augI (R := R) (H := H)).Cotangent ≃ₗ[H] Ω[H⁄R] :=
  { toFun := invDiffR (R := R) (H := H)
    invFun := (invDiffR (R := R) (H := H)).symm
    map_add' := fun x y => (invDiffR (R := R) (H := H)).map_add x y
    map_smul' := fun a t => by
      rw [RingHom.id_apply, invDiffR_apply, invDiffR_apply, fwd_smul, cotangentShear_smul]
      rfl
    left_inv := (invDiffR (R := R) (H := H)).left_inv
    right_inv := (invDiffR (R := R) (H := H)).right_inv }

end Ws47.INVDIFF
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_kaehlerDifferential_linearEquiv_tensorProduct_cotangent.Ws47 P2MW.S_HopfAlgebra_nonempty_kaehlerDifferential_linearEquiv_tensorProduct_cotangent.Ws47.INVDIFF"
p2m_reactivate "P2MW.S_HopfAlgebra_nonempty_kaehlerDifferential_linearEquiv_tensorProduct_cotangent.Ws47"

theorem solution (R : Type) [CommRing R] (A : Type) [CommRing A] [HopfAlgebra R A] :
    Nonempty (Ω[A⁄R] ≃ₗ[A] A ⊗[R] (RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent) :=
  ⟨(Ws47.INVDIFF.invDiff (R := R) (H := A)).symm⟩

end S_HopfAlgebra_nonempty_kaehlerDifferential_linearEquiv_tensorProduct_cotangent
end P2MW
export P2MW.S_HopfAlgebra_nonempty_kaehlerDifferential_linearEquiv_tensorProduct_cotangent (solution)
