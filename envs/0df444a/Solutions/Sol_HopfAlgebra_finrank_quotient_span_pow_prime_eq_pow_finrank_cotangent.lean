-- Prove2me | solution 1 for HopfAlgebra.finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/72ffcd51-2621-51b5-b6ca-df3426de6879

import Mathlib
import Theorems.Thm_HopfAlgebra_finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent

set_option autoImplicit false

open scoped TensorProduct
open Coalgebra Bialgebra

universe u v

section InlinedHopfIdealQuotient
noncomputable section HIQ

p2m_open_scoped "TensorProduct Coalgebra.TensorProduct Bialgebra.TensorProduct"
open Coalgebra Bialgebra WithConv

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one ofAlgHom mul_antipode_lTensor_comul_apply antipode_mul counit_antipode mul_antipode_rTensor_comul_apply finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero"
p2m_open "HopfAlgebra"

section AntipodeAlgHom

variable (R : Type*) [CommSemiring R] (H : Type*) [CommSemiring H] [HopfAlgebra R H]

def antipodeAlgHom : H →ₐ[R] H :=
  AlgHom.ofLinearMap (antipode R) antipode_one fun a b => by
    rw [antipode_mul, mul_comm]

@[scoped simp] theorem antipodeAlgHom_apply (x : H) : antipodeAlgHom R H x = antipode R x := rfl

theorem antipodeAlgHom_toLinearMap : (antipodeAlgHom R H).toLinearMap = antipode R := rfl

variable {R H}
variable {A : Type*} [CommSemiring A] [Algebra R A]

theorem lift_comp_antipodeAlgHom_apply (φ : H →ₐ[R] A) (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift φ (φ.comp (antipodeAlgHom R H)) (fun _ _ => .all _ _) z =
      φ (LinearMap.mul' R H ((antipode R).lTensor H z)) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.lTensor_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

theorem lift_antipodeAlgHom_comp_apply (φ : H →ₐ[R] A) (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift (φ.comp (antipodeAlgHom R H)) φ (fun _ _ => .all _ _) z =
      φ (LinearMap.mul' R H ((antipode R).rTensor H z)) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

theorem convMul_comp_antipodeAlgHom (φ : H →ₐ[R] A) :
    toConv φ * toConv (φ.comp (antipodeAlgHom R H)) = 1 := by
  refine WithConv.ext (AlgHom.ext fun x => ?_)
  change (toConv φ * toConv (φ.comp (antipodeAlgHom R H))) x = (1 : WithConv (H →ₐ[R] A)) x
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, ofConv_toConv, ofConv_toConv,
    lift_comp_antipodeAlgHom_apply, mul_antipode_lTensor_comul_apply, AlgHom.commutes]

theorem comp_antipodeAlgHom_convMul (φ : H →ₐ[R] A) :
    toConv (φ.comp (antipodeAlgHom R H)) * toConv φ = 1 := by
  refine WithConv.ext (AlgHom.ext fun x => ?_)
  change (toConv (φ.comp (antipodeAlgHom R H)) * toConv φ) x = (1 : WithConv (H →ₐ[R] A)) x
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, ofConv_toConv, ofConv_toConv,
    lift_antipodeAlgHom_comp_apply, mul_antipode_rTensor_comul_apply, AlgHom.commutes]

theorem isUnit_toConv_algHom (φ : H →ₐ[R] A) : IsUnit (toConv φ) :=
  isUnit_iff_exists.2 ⟨_, convMul_comp_antipodeAlgHom φ, comp_antipodeAlgHom_convMul φ⟩

end AntipodeAlgHom

section ConvComp

variable {R : Type*} [CommSemiring R] {H G : Type*} [CommSemiring H] [CommSemiring G]
  [Bialgebra R H] [Bialgebra R G]
variable (A : Type*) [CommSemiring A] [Algebra R A]

def convCompMonoidHom (π : H →ₐc[R] G) : WithConv (G →ₐ[R] A) →* WithConv (H →ₐ[R] A) where
  toFun f := toConv (f.ofConv.comp (π : H →ₐ[R] G))
  map_one' := by
    refine WithConv.ext ?_
    simp only [ofConv_toConv, AlgHom.convOne_def, AlgHom.comp_assoc, BialgHom.counitAlgHom_comp]
  map_mul' f g := by
    rw [AlgHom.convMul_comp_bialgHom_distrib]

@[scoped simp] theorem convCompMonoidHom_apply (π : H →ₐc[R] G) (f : WithConv (G →ₐ[R] A)) :
    convCompMonoidHom A π f = toConv (f.ofConv.comp (π : H →ₐ[R] G)) := rfl

end ConvComp

end HopfAlgebra
p2m_reactivate "P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.HopfAlgebra"

section IsHopfIdeal'

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

namespace Ideal p2m_export "Ideal" "map_le_iff_le_comap height Cotangent Quotient.eq_zero_iff_mem mul_mem_right Quotient.mkₐ Quotient.eq toCotangent_surjective Quotient.liftₐ Quotient.mkₐ_surjective toCotangent_eq_zero mem_bot span Quotient.algHom_ext Quotient.mk map ext Quotient.liftₐ_comp mem_map_of_mem span_le pow_le_self mem_comap mapCotangent_toCotangent pow_mem_pow comap mapCotangent Quotient.mkₐ_eq_mk subset_span le_comap_map mem_map_iff_of_surjective Quotient.mk_surjective toCotangent" end Ideal
namespace Ideal
p2m_open_scoped "Ideal" in

private class _root_.Ideal.IsHopfIdeal' (I : Ideal H) : Prop where
  map_mkₐ_comul_eq_zero : ∀ x ∈ I,
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
      (Coalgebra.comul (R := R) x) = 0
  counit_eq_zero : ∀ x ∈ I, Coalgebra.counit (R := R) x = 0
  antipode_mem : ∀ x ∈ I, HopfAlgebra.antipode R x ∈ I

end Ideal
p2m_export "" "Ideal.IsHopfIdeal'"
p2m_export_all "" "Ideal.IsHopfIdeal'"
p2m_open_scoped "Ideal" in
scoped instance Ideal.isHopfIdeal_bot : (⊥ : Ideal H).IsHopfIdeal' R where
  map_mkₐ_comul_eq_zero x hx := by rw [(Ideal.mem_bot).1 hx]; simp
  counit_eq_zero x hx := by rw [(Ideal.mem_bot).1 hx]; simp
  antipode_mem x hx := by rw [(Ideal.mem_bot).1 hx]; simp

p2m_reactivate "P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.HopfAlgebra P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.Ideal"
end IsHopfIdeal'
p2m_reactivate "P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.HopfAlgebra P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.Ideal"

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one ofAlgHom mul_antipode_lTensor_comul_apply antipode_mul counit_antipode mul_antipode_rTensor_comul_apply finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero"
p2m_open "HopfAlgebra"

namespace HopfIdealQuotient

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]
variable (I : Ideal H) [hI : I.IsHopfIdeal' R]

private def _root_.HopfAlgebra.HopfIdealQuotient.comul : H ⧸ I →ₐ[R] (H ⧸ I) ⊗[R] (H ⧸ I) :=
  Ideal.Quotient.liftₐ I
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
      (comulAlgHom R H))
    (fun x hx => hI.map_mkₐ_comul_eq_zero x hx)

p2m_export "HopfAlgebra.HopfIdealQuotient" "comul"
theorem comul_comp_mkₐ :
    (comul R I).comp (Ideal.Quotient.mkₐ R I) =
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
        (comulAlgHom R H) :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[scoped simp] theorem comul_mk (x : H) :
    comul R I (Ideal.Quotient.mk I x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) x) := rfl

private def _root_.HopfAlgebra.HopfIdealQuotient.counit : H ⧸ I →ₐ[R] R :=
  Ideal.Quotient.liftₐ I (counitAlgHom R H) (fun x hx => hI.counit_eq_zero x hx)

p2m_export "HopfAlgebra.HopfIdealQuotient" "counit"
theorem counit_comp_mkₐ : (counit R I).comp (Ideal.Quotient.mkₐ R I) = counitAlgHom R H :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[scoped simp] theorem counit_mk (x : H) :
    counit R I (Ideal.Quotient.mk I x) = Coalgebra.counit (R := R) x := rfl

private def _root_.HopfAlgebra.HopfIdealQuotient.antipode : H ⧸ I →ₐ[R] H ⧸ I :=
  Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ R I).comp (antipodeAlgHom R H)) (fun x hx => by
    simp only [AlgHom.comp_apply, antipodeAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hI.antipode_mem x hx)

p2m_export "HopfAlgebra.HopfIdealQuotient" "antipode"
theorem antipode_comp_mkₐ :
    (antipode R I).comp (Ideal.Quotient.mkₐ R I) =
      (Ideal.Quotient.mkₐ R I).comp (antipodeAlgHom R H) :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[scoped simp] theorem antipode_mk (x : H) :
    antipode R I (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (HopfAlgebra.antipode R x) := rfl

private theorem map_apply_eq_linearMap {A B C D : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A →ₐ[R] C) (g : B →ₐ[R] D) (z : A ⊗[R] B) :
    Algebra.TensorProduct.map f g z = TensorProduct.map f.toLinearMap g.toLinearMap z := rfl

private theorem _root_.HopfAlgebra.HopfIdealQuotient.rTensor_counit_comul :
    (Algebra.TensorProduct.map (counit R I) (.id R (H ⧸ I))).comp (comul R I) =
      (Algebra.TensorProduct.lid R (H ⧸ I)).symm := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    counit_comp_mkₐ, AlgHom.id_comp]
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, Algebra.TensorProduct.lid_symm_apply,
    map_apply_eq_linearMap, Bialgebra.comulAlgHom_apply]
  rw [show TensorProduct.map (counitAlgHom R H).toLinearMap (Ideal.Quotient.mkₐ R I).toLinearMap
      = ((Ideal.Quotient.mkₐ R I).toLinearMap.lTensor R) ∘ₗ
          ((counitAlgHom R H).toLinearMap.rTensor H) from
      (LinearMap.lTensor_comp_rTensor _ _ _).symm, LinearMap.comp_apply]
  rw [show ((counitAlgHom R H).toLinearMap.rTensor H) (Coalgebra.comul x) = 1 ⊗ₜ x from
    Coalgebra.rTensor_counit_comul x]
  simp

p2m_export "HopfAlgebra.HopfIdealQuotient" "rTensor_counit_comul"
private theorem _root_.HopfAlgebra.HopfIdealQuotient.lTensor_counit_comul :
    (Algebra.TensorProduct.map (.id R (H ⧸ I)) (counit R I)).comp (comul R I) =
      (Algebra.TensorProduct.rid R R (H ⧸ I)).symm := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    counit_comp_mkₐ, AlgHom.id_comp]
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, Algebra.TensorProduct.rid_symm_apply,
    map_apply_eq_linearMap, Bialgebra.comulAlgHom_apply]
  rw [show TensorProduct.map (Ideal.Quotient.mkₐ R I).toLinearMap (counitAlgHom R H).toLinearMap
      = ((Ideal.Quotient.mkₐ R I).toLinearMap.rTensor R) ∘ₗ
          ((counitAlgHom R H).toLinearMap.lTensor H) from
      (LinearMap.rTensor_comp_lTensor _ _ _).symm, LinearMap.comp_apply]
  rw [show ((counitAlgHom R H).toLinearMap.lTensor H) (Coalgebra.comul x) = x ⊗ₜ 1 from
    Coalgebra.lTensor_counit_comul x]
  simp

p2m_export "HopfAlgebra.HopfIdealQuotient" "lTensor_counit_comul"

private theorem assoc_map_map_apply {A B : Type*} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) (z : (A ⊗[R] A) ⊗[R] A) :
    (Algebra.TensorProduct.assoc R R R B B B)
        (Algebra.TensorProduct.map (Algebra.TensorProduct.map f f) f z) =
      Algebra.TensorProduct.map f (Algebra.TensorProduct.map f f)
        (Algebra.TensorProduct.assoc R R R A A A z) := by
  induction z with
  | zero => simp
  | tmul xy c =>
    induction xy with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem coassoc :
    (Algebra.TensorProduct.assoc R R R (H ⧸ I) (H ⧸ I) (H ⧸ I)).toAlgHom.comp
        ((Algebra.TensorProduct.map (comul R I) (.id R (H ⧸ I))).comp (comul R I)) =
      (Algebra.TensorProduct.map (.id R (H ⧸ I)) (comul R I)).comp (comul R I) := by
  refine Ideal.Quotient.algHom_ext R ?_
  refine AlgHom.ext fun x => ?_
  set π := Ideal.Quotient.mkₐ R I

  have hL : ∀ z : H ⊗[R] H,
      Algebra.TensorProduct.map (comul R I) (.id R (H ⧸ I)) (Algebra.TensorProduct.map π π z) =
        Algebra.TensorProduct.map (Algebra.TensorProduct.map π π) π
          (Algebra.TensorProduct.map (comulAlgHom R H) (.id R H) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => simp [π, Ideal.Quotient.mkₐ_eq_mk]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hR : ∀ z : H ⊗[R] H,
      Algebra.TensorProduct.map (.id R (H ⧸ I)) (comul R I) (Algebra.TensorProduct.map π π z) =
        Algebra.TensorProduct.map π (Algebra.TensorProduct.map π π)
          (Algebra.TensorProduct.map (.id R H) (comulAlgHom R H) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => simp [π, Ideal.Quotient.mkₐ_eq_mk]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hx : comul R I (π x) = Algebra.TensorProduct.map π π (comulAlgHom R H x) := by
    simp [π, Ideal.Quotient.mkₐ_eq_mk]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, hx, hL, hR, assoc_map_map_apply]
  congr 1
  have hassoc : ∀ z : (H ⊗[R] H) ⊗[R] H,
      Algebra.TensorProduct.assoc R R R H H H z = TensorProduct.assoc R H H H z := by
    intro z
    induction z with
    | zero => simp
    | tmul xy c =>
      induction xy with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [map_apply_eq_linearMap, map_apply_eq_linearMap, hassoc]
  exact Coalgebra.coassoc_apply x

scoped instance instBialgebra : Bialgebra R (H ⧸ I) :=
  Bialgebra.ofAlgHom (comul R I) (counit R I) (coassoc R I) (rTensor_counit_comul R I)
    (lTensor_counit_comul R I)

theorem comulAlgHom_eq : comulAlgHom R (H ⧸ I) = comul R I := rfl

theorem counitAlgHom_eq : counitAlgHom R (H ⧸ I) = counit R I := rfl

theorem coalgebra_comul_mk (x : H) :
    Coalgebra.comul (R := R) (Ideal.Quotient.mk I x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) x) := rfl

theorem coalgebra_counit_mk (x : H) :
    Coalgebra.counit (R := R) (Ideal.Quotient.mk I x) = Coalgebra.counit (R := R) x := rfl

end HopfIdealQuotient
p2m_reactivate "P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.HopfAlgebra P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.Ideal P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.HopfAlgebra.HopfIdealQuotient"

end HopfAlgebra
p2m_reactivate "P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.HopfAlgebra P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.Ideal P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.HopfAlgebra.HopfIdealQuotient"

end HIQ
p2m_reactivate "P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.HopfAlgebra P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.Ideal P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.HopfAlgebra.HopfIdealQuotient"

end InlinedHopfIdealQuotient
p2m_reactivate "P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.HopfAlgebra P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.Ideal P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.HopfAlgebra.HopfIdealQuotient"

namespace FrobKer

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
  (H : Type v) [CommRing H] [HopfAlgebra k H]

omit [CharP k p] in
theorem add_pow_char' {T : Type*} [CommRing T] (hT : (p : T) = 0) (x y : T) :
    (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow_prime_eq (Fact.out : p.Prime), hT, zero_mul, zero_mul, zero_mul, add_zero]

omit [CharP k p] in
theorem sum_pow_char' {T : Type*} [CommRing T] (hT : (p : T) = 0) {ι : Type*} (s : Finset ι)
    (f : ι → T) : (∑ i ∈ s, f i) ^ p = ∑ i ∈ s, f i ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, zero_pow (Fact.out : p.Prime).ne_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_pow_char' p hT, ih]

private theorem _root_.FrobKer.cast_eq_zero (T : Type*) [Ring T] [Algebra k T] : (p : T) = 0 := by
  rw [← map_natCast (algebraMap k T), CharP.cast_eq_zero, map_zero]

p2m_export "FrobKer" "cast_eq_zero"

abbrev I : Ideal H := RingHom.ker (counitAlgHom k H)

abbrev J : Ideal H := Ideal.span ((fun a : H => a ^ p) '' (I k H : Set H))

omit [Fact p.Prime] [CharP k p] in
theorem mem_I_iff (a : H) : a ∈ I k H ↔ counit (R := k) a = 0 := RingHom.mem_ker

omit [Fact p.Prime] [CharP k p] in
theorem pow_mem_J {a : H} (ha : a ∈ I k H) : a ^ p ∈ J k p H :=
  Ideal.subset_span ⟨a, ha, rfl⟩

omit [CharP k p] in

theorem J_le_sq : J k p H ≤ I k H ^ 2 := by
  rw [Ideal.span_le]
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Fact.out : p.Prime).two_le
  change a ^ p ∈ I k H ^ 2
  rw [hm, pow_add]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ha 2)

omit [CharP k p] in
theorem J_le_I : J k p H ≤ I k H :=
  (J_le_sq k p H).trans (Ideal.pow_le_self two_ne_zero)

noncomputable def π : H →ₗ[k] H := LinearMap.id - Algebra.linearMap k H ∘ₗ Coalgebra.counit

omit [Fact p.Prime] [CharP k p] in
theorem π_apply (a : H) : π k H a = a - algebraMap k H (counit (R := k) a) := rfl

omit [Fact p.Prime] [CharP k p] in
theorem π_mem (a : H) : π k H a ∈ I k H := by
  rw [mem_I_iff, π_apply, map_sub, counit_algebraMap, sub_self]

omit [Fact p.Prime] [CharP k p] in

theorem comul_eq (x : H) :
    comul (R := k) x = x ⊗ₜ[k] (1 : H) + LinearMap.lTensor H (π k H) (comul (R := k) x) := by
  have h1 : LinearMap.lTensor H (Algebra.linearMap k H ∘ₗ Coalgebra.counit) (comul (R := k) x) =
      x ⊗ₜ[k] (1 : H) := by
    rw [LinearMap.lTensor_comp, LinearMap.comp_apply, Coalgebra.lTensor_counit_comul,
      LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one]
  rw [π, LinearMap.lTensor_sub, LinearMap.sub_apply, LinearMap.lTensor_id, LinearMap.id_apply, h1,
    add_sub_cancel]

theorem map_mk_comul_pow_eq_zero {x : H} (_hx : x ∈ I k H) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (J k p H)) (Ideal.Quotient.mkₐ k (J k p H))
      (comul (R := k) (x ^ p)) = 0 := by
  have hp0 : (p : H ⊗[k] H) = 0 := cast_eq_zero k p (H ⊗[k] H)
  rw [comul_pow, comul_eq k H x, add_pow_char' p hp0, map_add]

  have h1 : Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (J k p H)) (Ideal.Quotient.mkₐ k (J k p H))
      ((x ⊗ₜ[k] (1 : H)) ^ p) = 0 := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.map_tmul,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_J k p H _hx),
      TensorProduct.zero_tmul]
  rw [h1, zero_add]

  obtain ⟨ι, s, f, g, hrep⟩ :=
    (⟨_, _, _, _, (Coalgebra.Repr.arbitrary k x).eq⟩ :
      ∃ (ι : Type v) (s : Finset ι) (f g : ι → H), ∑ i ∈ s, f i ⊗ₜ[k] g i = comul (R := k) x)
  rw [← hrep, map_sum, sum_pow_char' p hp0, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.map_tmul,
    Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_J k p H (π_mem k H (g i))), TensorProduct.tmul_zero]

theorem isHopfIdeal_J : (J k p H).IsHopfIdeal' k where
  map_mkₐ_comul_eq_zero := by

    intro y hy
    have hle : J k p H ≤ RingHom.ker
        ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (J k p H)) (Ideal.Quotient.mkₐ k (J k p H))).comp
          (comulAlgHom k H)) := by
      rw [Ideal.span_le]
      rintro _ ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      exact map_mk_comul_pow_eq_zero k p H ha
    exact hle hy
  counit_eq_zero y hy := (mem_I_iff k H y).1 (J_le_I k p H hy)
  antipode_mem := by
    intro y hy
    have hle : J k p H ≤ (J k p H).comap (HopfAlgebra.antipodeAlgHom k H) := by
      rw [Ideal.span_le]
      rintro _ ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, map_pow, HopfAlgebra.antipodeAlgHom_apply]
      refine pow_mem_J k p H ?_
      rw [mem_I_iff, HopfAlgebra.counit_antipode]
      exact (mem_I_iff k H a).1 ha
    exact hle hy

section Quot

attribute [local instance] isHopfIdeal_J

local notation "B" => H ⧸ J k p H

theorem quot_pow_eq_zero (b : B) (hb : counit (R := k) b = 0) : b ^ p = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [HopfAlgebra.HopfIdealQuotient.coalgebra_counit_mk] at hb
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact pow_mem_J k p H ((mem_I_iff k H a).2 hb)

theorem ker_counit_quot_eq :
    RingHom.ker (counitAlgHom k B) = (I k H).map (Ideal.Quotient.mkₐ k (J k p H)) := by
  refine le_antisymm ?_ ?_
  · intro b hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    have ha : a ∈ I k H := by
      rw [RingHom.mem_ker, counitAlgHom_apply, HopfAlgebra.HopfIdealQuotient.coalgebra_counit_mk] at hb
      exact (mem_I_iff k H a).2 hb
    exact Ideal.mem_map_of_mem (Ideal.Quotient.mkₐ k (J k p H)) ha
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, counitAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      HopfAlgebra.HopfIdealQuotient.coalgebra_counit_mk]
    exact (mem_I_iff k H a).1 ha

theorem I_le_comap : I k H ≤ (RingHom.ker (counitAlgHom k B)).comap (Ideal.Quotient.mkₐ k (J k p H)) := by
  rw [ker_counit_quot_eq]
  exact Ideal.le_comap_map

noncomputable def cotMap : (I k H).Cotangent →ₗ[k] (RingHom.ker (counitAlgHom k B)).Cotangent :=
  Ideal.mapCotangent (I k H) (RingHom.ker (counitAlgHom k B)) (Ideal.Quotient.mkₐ k (J k p H))
    (I_le_comap k p H)

theorem cotMap_surjective : Function.Surjective (cotMap k p H) := by
  intro z
  obtain ⟨⟨b, hb⟩, rfl⟩ := (RingHom.ker (counitAlgHom k B)).toCotangent_surjective z
  have hb' := hb
  rw [ker_counit_quot_eq, Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mkₐ k (J k p H))
    (Ideal.Quotient.mkₐ_surjective k (J k p H))] at hb'
  obtain ⟨a, ha, rfl⟩ := hb'
  exact ⟨(I k H).toCotangent ⟨a, ha⟩, rfl⟩

theorem cotMap_injective : Function.Injective (cotMap k p H) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨x, rfl⟩ := (I k H).toCotangent_surjective z
  rw [cotMap, Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq_zero] at hz
  change Ideal.Quotient.mkₐ k (J k p H) x ∈ RingHom.ker (counitAlgHom k B) ^ 2 at hz
  rw [ker_counit_quot_eq, ← Ideal.map_pow,
    Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mkₐ k (J k p H))
      (Ideal.Quotient.mkₐ_surjective k (J k p H))] at hz
  obtain ⟨x', hx', hxx'⟩ := hz
  rw [Ideal.toCotangent_eq_zero]
  have hdiff : (x : H) - x' ∈ J k p H := by
    rw [← Ideal.Quotient.eq, ← Ideal.Quotient.mkₐ_eq_mk k, ← hxx']
  have := Ideal.add_mem _ (J_le_sq k p H hdiff) hx'
  rwa [sub_add_cancel] at this

theorem finrank_cotangent_quot :
    Module.finrank k (RingHom.ker (counitAlgHom k B)).Cotangent =
      Module.finrank k (I k H).Cotangent :=
  (LinearEquiv.ofBijective (cotMap k p H) ⟨cotMap_injective k p H, cotMap_surjective k p H⟩).finrank_eq.symm

theorem finrank_quot [Module.Finite k H] :
    Module.finrank k B = p ^ Module.finrank k (I k H).Cotangent := by
  haveI : Module.Finite k B := inferInstance
  rw [HopfAlgebra.finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero k p B
    (quot_pow_eq_zero k p H), finrank_cotangent_quot]

end Quot
p2m_reactivate "P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.HopfAlgebra P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.Ideal P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.HopfAlgebra.HopfIdealQuotient"

end FrobKer
p2m_reactivate "P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.HopfAlgebra P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.Ideal P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.HopfAlgebra.HopfIdealQuotient"

theorem solution
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (H : Type v) [CommRing H] [HopfAlgebra k H] [Module.Finite k H] :
    Module.finrank k
        (H ⧸ Ideal.span ((fun a : H => a ^ p) '' (RingHom.ker (Bialgebra.counitAlgHom k H) : Set H))) =
      p ^ Module.finrank k (RingHom.ker (Bialgebra.counitAlgHom k H)).Cotangent :=
  FrobKer.finrank_quot k p H

end S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent
end P2MW
export P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent (solution)
