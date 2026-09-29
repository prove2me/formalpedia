-- Prove2me | solution 1 for HopfAlgebra.exists_bialgHom_surjective_comp_eq_id_comp_eq_of_comp_eq_self_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/3392c811-b294-551d-b77c-e043028e3429

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_bialgHom_surjective_comp_eq_id_comp_eq_of_comp_eq_self_of_isLocalRing

set_option autoImplicit false

open scoped TensorProduct

namespace HopfRetract

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [HopfAlgebra R A]
variable {C : Type*} [CommRing C] [Algebra R C]
variable (q : A →ₐ[R] C) (i : C →ₐ[R] A) (ε : A →ₐc[R] A)

structure Datum : Prop where
  hqi : ∀ c, q (i c) = c
  hiq : ∀ a, i (q a) = ε a
  hε : ∀ a, ε (ε a) = ε a

variable {q i ε} (H : Datum q i ε)
include H

theorem q_ε (a : A) : q (ε a) = q a := by rw [← H.hiq, H.hqi]

theorem ε_i (c : C) : ε (i c) = i c := by rw [← H.hiq, H.hqi]

noncomputable def reprE (x : A) (hx : ε x = x) : Coalgebra.Repr R x (A × A) where
  index := (Coalgebra.Repr.arbitrary R x).index
  left := fun j => ε ((Coalgebra.Repr.arbitrary R x).left j)
  right := fun j => ε ((Coalgebra.Repr.arbitrary R x).right j)
  eq := by
    have h1 := CoalgHomClass.map_comp_comul_apply ε x
    rw [hx] at h1
    refine Eq.trans ?_ h1
    rw [← (Coalgebra.Repr.arbitrary R x).eq, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.map_tmul]
    rfl

private noncomputable def _root_.HopfRetract.comulAlgHom (q : A →ₐ[R] C) (i : C →ₐ[R] A) : C →ₐ[R] C ⊗[R] C :=
  (Algebra.TensorProduct.map q q).comp ((Bialgebra.comulAlgHom R A).comp i)

p2m_export "HopfRetract" "comulAlgHom"

private noncomputable def _root_.HopfRetract.counitAlgHom (i : C →ₐ[R] A) : C →ₐ[R] R := (Bialgebra.counitAlgHom R A).comp i

p2m_export "HopfRetract" "counitAlgHom"
omit H in
theorem counitAlgHom_apply (c : C) : counitAlgHom (R := R) i c = Coalgebra.counit (R := R) (i c) := rfl

omit H in
theorem comulAlgHom_eq_sum' (c : C) {ιrepr : Type*} (repr : Coalgebra.Repr R (i c) ιrepr) :
    comulAlgHom q i c = ∑ j ∈ repr.index, q (repr.left j) ⊗ₜ[R] q (repr.right j) := by
  change Algebra.TensorProduct.map q q (Coalgebra.comul (R := R) (i c)) = _
  rw [← repr.eq, map_sum]
  simp only [Algebra.TensorProduct.map_tmul]

theorem comulAlgHom_q_eq_sum (x : A) {ιrepr : Type*} (repr : Coalgebra.Repr R x ιrepr) :
    comulAlgHom q i (q x) = ∑ j ∈ repr.index, q (repr.left j) ⊗ₜ[R] q (repr.right j) := by
  change Algebra.TensorProduct.map q q (Coalgebra.comul (R := R) (i (q x))) = _
  rw [H.hiq, ← CoalgHomClass.map_comp_comul_apply ε x, ← repr.eq, map_sum, map_sum]
  simp only [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  change q (ε (repr.left j)) ⊗ₜ[R] q (ε (repr.right j)) = _
  rw [q_ε H, q_ε H]

noncomputable def reprI (c : C) : Coalgebra.Repr R (i c) (A × A) := reprE (ε := ε) (i c) (ε_i H c)

theorem i_q_left (c : C) (j) : i (q ((reprI H c).left j)) = (reprI H c).left j := by
  rw [H.hiq]; exact H.hε _

theorem i_q_right (c : C) (j) : i (q ((reprI H c).right j)) = (reprI H c).right j := by
  rw [H.hiq]; exact H.hε _

theorem h_rTensor :
    (Algebra.TensorProduct.map (counitAlgHom (R := R) i) (.id R C)).comp (comulAlgHom q i) =
      (Algebra.TensorProduct.lid R C).symm := by
  apply AlgHom.ext
  intro c
  have key := congrArg (TensorProduct.map (LinearMap.id : R →ₗ[R] R) q.toLinearMap)
    (Coalgebra.sum_counit_tmul_eq (reprI H c))
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply, H.hqi] at key
  rw [AlgHom.comp_apply, comulAlgHom_eq_sum' c (reprI H c), map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, counitAlgHom_apply, i_q_left H]
  rw [key]
  rfl

theorem h_lTensor :
    (Algebra.TensorProduct.map (.id R C) (counitAlgHom (R := R) i)).comp (comulAlgHom q i) =
      (Algebra.TensorProduct.rid R R C).symm := by
  apply AlgHom.ext
  intro c
  have key := congrArg (TensorProduct.map q.toLinearMap (LinearMap.id : R →ₗ[R] R))
    (Coalgebra.sum_tmul_counit_eq (reprI H c))
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply, H.hqi] at key
  rw [AlgHom.comp_apply, comulAlgHom_eq_sum' c (reprI H c), map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, counitAlgHom_apply, i_q_right H]
  rw [key]
  rfl

theorem h_coassoc :
    (Algebra.TensorProduct.assoc R R R C C C).toAlgHom.comp
        ((Algebra.TensorProduct.map (comulAlgHom q i) (.id R C)).comp (comulAlgHom q i)) =
      (Algebra.TensorProduct.map (.id R C) (comulAlgHom q i)).comp (comulAlgHom q i) := by
  apply AlgHom.ext
  intro c
  let a₁ := fun j => Coalgebra.Repr.arbitrary R ((reprI H c).left j)
  let a₂ := fun j => Coalgebra.Repr.arbitrary R ((reprI H c).right j)
  have key := congrArg (TensorProduct.map q.toLinearMap (TensorProduct.map q.toLinearMap q.toLinearMap))
    (Coalgebra.sum_tmul_tmul_eq (reprI H c) a₁ a₂)
  simp only [map_sum, TensorProduct.map_tmul, AlgHom.toLinearMap_apply] at key
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, comulAlgHom_eq_sum' c (reprI H c), map_sum, map_sum,
    map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, comulAlgHom_q_eq_sum H _ (a₁ _),
    comulAlgHom_q_eq_sum H _ (a₂ _), TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum]
  exact key

@[reducible] noncomputable def bialgebra : Bialgebra R C :=
  Bialgebra.ofAlgHom (comulAlgHom q i) (counitAlgHom i) (h_coassoc H) (h_rTensor H) (h_lTensor H)

private noncomputable def _root_.HopfRetract.antipode (q : A →ₐ[R] C) (i : C →ₐ[R] A) : C →ₗ[R] C :=
  q.toLinearMap ∘ₗ HopfAlgebraStruct.antipode R ∘ₗ i.toLinearMap

p2m_export "HopfRetract" "antipode"
omit H in
theorem antipode_apply (c : C) : antipode (R := R) q i c = q (HopfAlgebraStruct.antipode R (i c)) := rfl

@[reducible] noncomputable def hopfAlgebra : HopfAlgebra R C :=
  letI := bialgebra H
  { antipode := antipode q i
    mul_antipode_rTensor_comul := by
      apply LinearMap.ext
      intro c
      change LinearMap.mul' R C ((antipode q i).rTensor C (comulAlgHom q i c)) =
        algebraMap R C (Coalgebra.counit (R := R) (i c))
      rw [comulAlgHom_eq_sum' c (reprI H c), map_sum, map_sum]
      simp only [LinearMap.rTensor_tmul, LinearMap.mul'_apply, antipode_apply, i_q_left H, ← map_mul,
        ← map_sum, HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit, AlgHom.commutes]
    mul_antipode_lTensor_comul := by
      apply LinearMap.ext
      intro c
      change LinearMap.mul' R C ((antipode q i).lTensor C (comulAlgHom q i c)) =
        algebraMap R C (Coalgebra.counit (R := R) (i c))
      rw [comulAlgHom_eq_sum' c (reprI H c), map_sum, map_sum]
      simp only [LinearMap.lTensor_tmul, LinearMap.mul'_apply, antipode_apply, i_q_right H, ← map_mul,
        ← map_sum, HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit, AlgHom.commutes] }

theorem isCocomm [Coalgebra.IsCocomm R A] : letI := bialgebra H; Coalgebra.IsCocomm R C := by
  letI := bialgebra H
  refine ⟨?_⟩
  apply LinearMap.ext
  intro c
  change (TensorProduct.comm R C C) (comulAlgHom q i c) = comulAlgHom q i c
  have key := congrArg (TensorProduct.map q.toLinearMap q.toLinearMap) (Coalgebra.comm_comul R (i c))
  rw [← (reprI H c).eq, map_sum, map_sum, map_sum] at key
  simp only [TensorProduct.comm_tmul, TensorProduct.map_tmul, AlgHom.toLinearMap_apply] at key
  rw [comulAlgHom_eq_sum' c (reprI H c), map_sum]
  simp only [TensorProduct.comm_tmul]
  exact key

noncomputable def qBialgHom : letI := bialgebra H; A →ₐc[R] C :=
  letI := bialgebra H
  BialgHom.ofAlgHom q
    (by
      apply AlgHom.ext
      intro a
      change Coalgebra.counit (R := R) (i (q a)) = Coalgebra.counit (R := R) a
      rw [H.hiq]
      exact CoalgHomClass.counit_comp_apply ε a)
    (by
      apply AlgHom.ext
      intro a
      let repr := Coalgebra.Repr.arbitrary R a
      change Algebra.TensorProduct.map q q (Coalgebra.comul (R := R) a) = comulAlgHom q i (q a)
      rw [comulAlgHom_q_eq_sum H a repr, ← repr.eq, map_sum]
      simp only [Algebra.TensorProduct.map_tmul])

theorem qBialgHom_apply (a : A) : (letI := bialgebra H; qBialgHom H a) = q a := rfl

noncomputable def iBialgHom : letI := bialgebra H; C →ₐc[R] A :=
  letI := bialgebra H
  BialgHom.ofAlgHom i rfl
    (by
      apply AlgHom.ext
      intro c
      change Algebra.TensorProduct.map i i (comulAlgHom q i c) = Coalgebra.comul (R := R) (i c)
      rw [comulAlgHom_eq_sum' c (reprI H c), map_sum, ← (reprI H c).eq]
      simp only [Algebra.TensorProduct.map_tmul, i_q_left H, i_q_right H])

theorem iBialgHom_apply (c : C) : (letI := bialgebra H; iBialgHom H c) = i c := rfl

end HopfRetract

theorem solution
    (R : Type) [CommRing R] [IsLocalRing R]
    (A : Type) [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
    [Module.Finite R A] [Module.Free R A]
    (ε : A →ₐc[R] A) (hε : ε.comp ε = ε) :
    ∃ (C : Type) (_ : CommRing C) (_ : HopfAlgebra R C) (_ : Coalgebra.IsCocomm R C)
      (_ : Module.Finite R C) (_ : Module.Free R C)
      (q : A →ₐc[R] C) (i : C →ₐc[R] A),
      Function.Surjective q ∧ q.comp i = BialgHom.id R C ∧ i.comp q = ε := by
  classical
  let I : Ideal A := RingHom.ker (ε : A →ₐ[R] A)
  let q : A →ₐ[R] A ⧸ I := Ideal.Quotient.mkₐ R I
  let i : A ⧸ I →ₐ[R] A := Ideal.Quotient.liftₐ I (ε : A →ₐ[R] A) (fun a ha => ha)
  have hεε : ∀ a, ε (ε a) = ε a := fun a => by
    have := DFunLike.congr_fun hε a
    rwa [BialgHom.comp_apply] at this
  have hiq : ∀ a, i (q a) = ε a := fun a => rfl
  have hqi : ∀ c, q (i c) = c := by
    intro c
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I c
    change Ideal.Quotient.mk I (ε a) = Ideal.Quotient.mk I a
    rw [Ideal.Quotient.eq]
    change ε (ε a - a) = 0
    rw [map_sub, hεε, sub_self]
  have Hd : HopfRetract.Datum q i ε := ⟨hqi, hiq, hεε⟩
  letI : HopfAlgebra R (A ⧸ I) := HopfRetract.hopfAlgebra Hd
  haveI : Coalgebra.IsCocomm R (A ⧸ I) := HopfRetract.isCocomm Hd
  haveI : Module.Finite R (A ⧸ I) := Module.Finite.of_surjective q.toLinearMap (Ideal.Quotient.mkₐ_surjective R I)
  haveI : Module.Projective R (A ⧸ I) :=
    Module.Projective.of_split i.toLinearMap q.toLinearMap (LinearMap.ext hqi)
  haveI : Module.Free R (A ⧸ I) := Module.free_of_flat_of_isLocalRing
  refine ⟨A ⧸ I, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    HopfRetract.qBialgHom Hd, HopfRetract.iBialgHom Hd, Ideal.Quotient.mkₐ_surjective R I, ?_, ?_⟩
  · apply BialgHom.ext
    intro c
    exact hqi c
  · apply BialgHom.ext
    intro a
    exact hiq a

end S_HopfAlgebra_exists_bialgHom_surjective_comp_eq_id_comp_eq_of_comp_eq_self_of_isLocalRing
end P2MW
export P2MW.S_HopfAlgebra_exists_bialgHom_surjective_comp_eq_id_comp_eq_of_comp_eq_self_of_isLocalRing (solution)
