-- Prove2me | solution 1 for ModularCurve.frobenius_comp_verschiebung_eq_unit_counit_of_model_jZero_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/707d1850-9a3e-5461-9614-385a8c6a0b89

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_HopfAlgebra_CartierDualMap
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_HopfAlgebra_toConv_id_pow_eq_one_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_frobenius_comp_verschiebung_eq_unit_counit_of_model_jZero_torsion

open ModularCurve WithConv

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000

open Coalgebra Module
p2m_open_scoped "TensorProduct Coalgebra.TensorProduct"

universe u v w

namespace KTailFrobVer

section CoalgComp

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {B : Type v} [AddCommMonoid B] [Module R B] [Coalgebra R B]
variable {T : Type w} [CommRing T] [Algebra R T]

private theorem convOne_comp_coalgHom (π : B →ₗc[R] C) :
    WithConv.toConv ((1 : WithConv (C →ₗ[R] T)).ofConv ∘ₗ π.toLinearMap)
      = (1 : WithConv (B →ₗ[R] T)) := by
  rw [LinearMap.convOne_def, LinearMap.convOne_def, WithConv.ofConv_toConv]
  congr 1
  rw [LinearMap.comp_assoc, π.counit_comp]

private theorem convPow_comp_coalgHom (f : WithConv (C →ₗ[R] T)) (π : B →ₗc[R] C) (m : ℕ) :
    (WithConv.toConv (f.ofConv ∘ₗ π.toLinearMap)) ^ m
      = WithConv.toConv ((f ^ m).ofConv ∘ₗ π.toLinearMap) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, convOne_comp_coalgHom]
  | succ k ih =>
      rw [pow_succ, pow_succ, ih, LinearMap.convMul_comp_coalgHom_distrib,
        WithConv.toConv_ofConv]

end CoalgComp

section ConvScalar

variable {R : Type u} [CommSemiring R]
variable {A₀ : Type v} [Semiring A₀] [Algebra R A₀]
variable {C : Type w} [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]

private theorem convMul_smul_left (c : R) (f g : WithConv (C →ₗ[R] A₀)) :
    (c • f) * g = c • (f * g) := by
  apply WithConv.ofConv_injective
  apply LinearMap.ext
  intro x
  have 𝓡 := Coalgebra.Repr.arbitrary R x
  show ((c • f) * g) x = (c • (f * g)).ofConv x
  rw [𝓡.convMul_apply,
    show (c • (f * g)).ofConv x = c • ((f * g) x) from rfl,
    𝓡.convMul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ((c • f) : WithConv (C →ₗ[R] A₀)) (𝓡.left i) = c • (f (𝓡.left i)) from rfl,
    smul_mul_assoc]

private theorem convMul_smul_right (c : R) (f g : WithConv (C →ₗ[R] A₀)) :
    f * (c • g) = c • (f * g) := by
  apply WithConv.ofConv_injective
  apply LinearMap.ext
  intro x
  have 𝓡 := Coalgebra.Repr.arbitrary R x
  show (f * (c • g)) x = (c • (f * g)).ofConv x
  rw [𝓡.convMul_apply,
    show (c • (f * g)).ofConv x = c • ((f * g) x) from rfl,
    𝓡.convMul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ((c • g) : WithConv (C →ₗ[R] A₀)) (𝓡.right i) = c • (g (𝓡.right i)) from rfl,
    mul_smul_comm]

scoped instance : IsScalarTower R (WithConv (C →ₗ[R] A₀)) (WithConv (C →ₗ[R] A₀)) where
  smul_assoc c f g := convMul_smul_left c f g

scoped instance : SMulCommClass R (WithConv (C →ₗ[R] A₀)) (WithConv (C →ₗ[R] A₀)) where
  smul_comm c f g := (convMul_smul_right c f g).symm

end ConvScalar

section CharPTransfer

private theorem charP_of_unital_linearForm {k : Type u} [CommSemiring k] {p : ℕ} [CharP k p]
    {S : Type w} [NonAssocSemiring S] [Module k S] (E : S →ₗ[k] k) (hE : E 1 = 1) :
    CharP S p := by
  constructor
  intro n
  have key : ((n : ℕ) : S) = ((n : ℕ) : k) • (1 : S) := by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
  rw [key, ← CharP.cast_eq_zero_iff k p n]
  constructor
  · intro hn
    have h0 := congrArg E hn
    rwa [map_smul, hE, smul_eq_mul, mul_one, map_zero] at h0
  · intro hn
    rw [hn, zero_smul]

private theorem charP_carrier (k : Type u) [Field k] (p : ℕ) [CharP k p]
    (A : Type v) [CommRing A] [Bialgebra k A] : CharP A p :=
  charP_of_unital_linearForm (Coalgebra.counit (R := k) (A := A)) Bialgebra.counit_one

private theorem charP_tensorSquare (k : Type u) [Field k] (p : ℕ) [CharP k p]
    (A : Type v) [CommRing A] [Bialgebra k A] : CharP (A ⊗[k] A) p := by
  refine charP_of_unital_linearForm
    (LinearMap.mul' k k ∘ₗ TensorProduct.map (Coalgebra.counit (R := k) (A := A))
      (Coalgebra.counit (R := k) (A := A))) ?_
  rw [Algebra.TensorProduct.one_def, LinearMap.comp_apply, TensorProduct.map_tmul,
    Bialgebra.counit_one, LinearMap.mul'_apply, one_mul]

private theorem charP_convEnd (k : Type u) [Field k] (p : ℕ) [CharP k p]
    (A : Type v) [CommRing A] [Bialgebra k A] : CharP (WithConv (A →ₗ[k] A)) p := by
  refine charP_of_unital_linearForm
    (k := k) (S := WithConv (A →ₗ[k] A))
    { toFun := fun W => Coalgebra.counit (R := k) (W.ofConv 1)
      map_add' := fun W₁ W₂ => by
        simp only [WithConv.ofConv_add, LinearMap.add_apply, map_add]
      map_smul' := fun c W => by
        simp only [WithConv.ofConv_smul, LinearMap.smul_apply, map_smul, RingHom.id_apply,
          smul_eq_mul] } ?_
  show Coalgebra.counit (R := k) ((1 : WithConv (A →ₗ[k] A)).ofConv 1) = 1
  rw [LinearMap.convOne_def, WithConv.ofConv_toConv, LinearMap.comp_apply,
    Algebra.linearMap_apply, Bialgebra.counit_one, map_one, Bialgebra.counit_one]

private theorem charP_convDual (k : Type u) [Field k] (p : ℕ) [CharP k p]
    (A : Type v) [CommRing A] [Bialgebra k A] : CharP (WithConv (A →ₗ[k] k)) p := by
  refine charP_of_unital_linearForm
    (k := k) (S := WithConv (A →ₗ[k] k))
    { toFun := fun W => W.ofConv 1
      map_add' := fun W₁ W₂ => by
        simp only [WithConv.ofConv_add, LinearMap.add_apply]
      map_smul' := fun c W => by
        simp only [WithConv.ofConv_smul, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul] } ?_
  show (1 : WithConv (A →ₗ[k] k)).ofConv 1 = 1
  rw [LinearMap.convOne_def, WithConv.ofConv_toConv, LinearMap.comp_apply,
    Algebra.linearMap_apply, Bialgebra.counit_one, map_one]

end CharPTransfer

section RankOne

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Bialgebra k A]

private theorem toConv_smulRight_one :
    WithConv.toConv (((1 : WithConv (A →ₗ[k] k)).ofConv).smulRight (1 : A))
      = (1 : WithConv (A →ₗ[k] A)) := by
  apply WithConv.ofConv_injective
  apply LinearMap.ext
  intro x
  rw [WithConv.ofConv_toConv, LinearMap.smulRight_apply,
    show (1 : WithConv (A →ₗ[k] k)).ofConv x
      = algebraMap k k (Coalgebra.counit (R := k) x) from rfl,
    show (1 : WithConv (A →ₗ[k] A)).ofConv x
      = algebraMap k A (Coalgebra.counit (R := k) x) from rfl,
    Algebra.algebraMap_eq_smul_one (R := k) (A := A)]
  congr 1

private theorem toConv_smulRight_mul (φ ψ : A →ₗ[k] k) (m n : A) :
    (WithConv.toConv (φ.smulRight m) : WithConv (A →ₗ[k] A)) * WithConv.toConv (ψ.smulRight n)
      = WithConv.toConv ((((WithConv.toConv φ : WithConv (A →ₗ[k] k))
          * WithConv.toConv ψ).ofConv).smulRight (m * n)) := by
  apply WithConv.ofConv_injective
  apply LinearMap.ext
  intro x
  have 𝓡 := Coalgebra.Repr.arbitrary k x
  show (WithConv.toConv (φ.smulRight m) * WithConv.toConv (ψ.smulRight n)) x
      = (WithConv.toConv ((((WithConv.toConv φ : WithConv (A →ₗ[k] k))
          * WithConv.toConv ψ).ofConv).smulRight (m * n))).ofConv x
  rw [𝓡.convMul_apply, WithConv.ofConv_toConv, LinearMap.smulRight_apply,
    show ((WithConv.toConv φ : WithConv (A →ₗ[k] k)) * WithConv.toConv ψ).ofConv x
      = ((WithConv.toConv φ : WithConv (A →ₗ[k] k)) * WithConv.toConv ψ) x from rfl,
    𝓡.convMul_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (φ.smulRight m) (𝓡.left i) * (ψ.smulRight n) (𝓡.right i)
      = (φ (𝓡.left i) * ψ (𝓡.right i)) • (m * n)
  rw [LinearMap.smulRight_apply, LinearMap.smulRight_apply, smul_mul_smul_comm]

private theorem toConv_smulRight_pow (φ : A →ₗ[k] k) (m : A) (n : ℕ) :
    (WithConv.toConv (φ.smulRight m) : WithConv (A →ₗ[k] A)) ^ n
      = WithConv.toConv ((((WithConv.toConv φ : WithConv (A →ₗ[k] k)) ^ n).ofConv).smulRight
          (m ^ n)) := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, pow_zero]
      exact toConv_smulRight_one.symm
  | succ n ih =>
      rw [pow_succ, ih, toConv_smulRight_mul, WithConv.toConv_ofConv, ← pow_succ, ← pow_succ]

end RankOne

section KeyFormula

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
variable (A : Type v) [CommRing A] [Bialgebra k A] [Coalgebra.IsCocomm k A]

private theorem id_eq_sum_smulRight {ι : Type w} [Fintype ι] (b : Basis ι k A) :
    (LinearMap.id : A →ₗ[k] A) = ∑ i, (b.coord i).smulRight (b i) := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.id_apply, LinearMap.sum_apply]
  simp_rw [LinearMap.smulRight_apply, Basis.coord_apply]
  exact (b.sum_repr x).symm

private theorem ofConv_pow_toConv_id_eq_sum {ι : Type w} [Fintype ι] (b : Basis ι k A) (a : A) :
    ((WithConv.toConv (LinearMap.id : A →ₗ[k] A)) ^ p).ofConv a
      = ∑ i, ((WithConv.toConv (b.coord i) : WithConv (A →ₗ[k] k)) ^ p).ofConv a • (b i) ^ p := by
  haveI : CharP (WithConv (A →ₗ[k] A)) p := charP_convEnd k p A
  have h1 : (WithConv.toConv (LinearMap.id : A →ₗ[k] A) : WithConv (A →ₗ[k] A))
      = ∑ i, WithConv.toConv ((b.coord i).smulRight (b i)) := by
    rw [← WithConv.toConv_sum, ← id_eq_sum_smulRight k A b]
  rw [h1, sum_pow_char]
  simp_rw [toConv_smulRight_pow]
  rw [WithConv.ofConv_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i _ => rfl

end KeyFormula

section Frobenius

variable (p : ℕ) [Fact p.Prime]
variable (A : Type v) [CommRing A] [Bialgebra (ZMod p) A]

private theorem counit_pow (n : ℕ) (x : A) :
    Coalgebra.counit (R := ZMod p) (x ^ n)
      = (Coalgebra.counit (R := ZMod p) x : ZMod p) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact Bialgebra.counit_one
  | succ n ih => rw [pow_succ, pow_succ, Bialgebra.counit_mul, ih]

private theorem comul_pow (n : ℕ) (x : A) :
    Coalgebra.comul (R := ZMod p) (x ^ n) = (Coalgebra.comul (R := ZMod p) x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact Bialgebra.comul_one
  | succ n ih => rw [pow_succ, pow_succ, Bialgebra.comul_mul, ih]

private noncomputable def frobeniusLinear : A →ₗ[ZMod p] A where
  toFun x := x ^ p
  map_add' x y := by
    haveI : CharP A p := charP_carrier (ZMod p) p A
    exact map_add (frobenius A p) x y
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [smul_pow, ZMod.pow_card]

@[scoped simp] private theorem frobeniusLinear_apply (x : A) : frobeniusLinear p A x = x ^ p := rfl

private noncomputable def frobeniusCoalgHom : A →ₗc[ZMod p] A where
  toLinearMap := frobeniusLinear p A
  counit_comp := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, frobeniusLinear_apply]
    rw [counit_pow p A p x, ZMod.pow_card]
  map_comp_comul := by
    haveI : CharP (A ⊗[ZMod p] A) p := charP_tensorSquare (ZMod p) p A
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, frobeniusLinear_apply]
    have 𝓡 := Coalgebra.Repr.arbitrary (ZMod p) x
    rw [comul_pow p A p x, ← 𝓡.eq, map_sum, sum_pow_char]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.map_tmul, Algebra.TensorProduct.tmul_pow, frobeniusLinear_apply,
      frobeniusLinear_apply]

@[scoped simp] private theorem frobeniusCoalgHom_toLinearMap :
    (frobeniusCoalgHom p A).toLinearMap = frobeniusLinear p A := rfl

end Frobenius

section Verschiebung

variable (p : ℕ) [Fact p.Prime]
variable (A : Type v) [CommRing A] [Bialgebra (ZMod p) A] [Coalgebra.IsCocomm (ZMod p) A]
variable [Module.Finite (ZMod p) A] [Module.Free (ZMod p) A]

private noncomputable def verschiebungAux {ι : Type w} [Fintype ι] (b : Basis ι (ZMod p) A) :
    A →ₗ[ZMod p] A :=
  ∑ i, ((((WithConv.toConv (b.coord i) : WithConv (A →ₗ[ZMod p] ZMod p)) ^ p)).ofConv).smulRight
    (b i)

private theorem verschiebungAux_apply {ι : Type w} [Fintype ι] (b : Basis ι (ZMod p) A) (a : A) :
    verschiebungAux p A b a
      = ∑ i, ((WithConv.toConv (b.coord i) : WithConv (A →ₗ[ZMod p] ZMod p)) ^ p).ofConv a
          • b i := by
  rw [verschiebungAux, LinearMap.sum_apply]
  simp_rw [LinearMap.smulRight_apply]

private theorem toConv_pow_eq_sum {ι : Type w} [Fintype ι] (b : Basis ι (ZMod p) A)
    (φ : A →ₗ[ZMod p] ZMod p) :
    (WithConv.toConv φ : WithConv (A →ₗ[ZMod p] ZMod p)) ^ p
      = ∑ i, φ (b i) • (WithConv.toConv (b.coord i) : WithConv (A →ₗ[ZMod p] ZMod p)) ^ p := by
  haveI : CharP (WithConv (A →ₗ[ZMod p] ZMod p)) p := charP_convDual (ZMod p) p A
  have hφ : φ = ∑ i, φ (b i) • b.coord i := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.sum_apply]
    simp_rw [LinearMap.smul_apply, Basis.coord_apply, smul_eq_mul]
    conv_lhs => rw [← b.sum_repr x, map_sum]
    simp_rw [map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hsum : (WithConv.toConv φ : WithConv (A →ₗ[ZMod p] ZMod p))
      = ∑ i, φ (b i) • WithConv.toConv (b.coord i) := by
    conv_lhs => rw [hφ]
    rw [WithConv.toConv_sum]
    simp_rw [WithConv.toConv_smul]
  rw [hsum, sum_pow_char]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_pow, ZMod.pow_card]

private theorem dual_apply_verschiebungAux {ι : Type w} [Fintype ι] (b : Basis ι (ZMod p) A) (a : A)
    (φ : A →ₗ[ZMod p] ZMod p) :
    φ (verschiebungAux p A b a)
      = ((WithConv.toConv φ : WithConv (A →ₗ[ZMod p] ZMod p)) ^ p).ofConv a := by
  rw [verschiebungAux_apply, map_sum]
  simp_rw [map_smul, smul_eq_mul]
  rw [toConv_pow_eq_sum p A b φ, WithConv.ofConv_sum, LinearMap.sum_apply]
  simp_rw [WithConv.ofConv_smul, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private noncomputable def verschiebung : A →ₗ[ZMod p] A :=
  verschiebungAux p A (Module.Free.chooseBasis (ZMod p) A)

private theorem dual_apply_verschiebung (a : A) (φ : A →ₗ[ZMod p] ZMod p) :
    φ (verschiebung p A a)
      = ((WithConv.toConv φ : WithConv (A →ₗ[ZMod p] ZMod p)) ^ p).ofConv a :=
  dual_apply_verschiebungAux p A _ a φ

private theorem eq_verschiebung_of_dual_apply (W : A → A)
    (hW : ∀ (a : A) (φ : A →ₗ[ZMod p] ZMod p),
      φ (W a) = ((WithConv.toConv φ : WithConv (A →ₗ[ZMod p] ZMod p)) ^ p).ofConv a)
    (a : A) :
    W a = verschiebung p A a := by
  set b := Module.Free.chooseBasis (ZMod p) A
  apply b.ext_elem
  intro i
  rw [← Basis.coord_apply, ← Basis.coord_apply, hW a (b.coord i),
    dual_apply_verschiebung p A a (b.coord i)]

private theorem verschiebungAux_eq_verschiebung {ι : Type w} [Fintype ι] (b : Basis ι (ZMod p) A) :
    verschiebungAux p A b = verschiebung p A := by
  apply LinearMap.ext
  intro a
  exact eq_verschiebung_of_dual_apply p A (verschiebungAux p A b)
    (dual_apply_verschiebungAux p A b) a

end Verschiebung

section MainTheorems

variable (p : ℕ) [Fact p.Prime]
variable (A : Type v) [CommRing A] [Bialgebra (ZMod p) A] [Coalgebra.IsCocomm (ZMod p) A]
variable [Module.Finite (ZMod p) A] [Module.Free (ZMod p) A]

private theorem verschiebung_pow (a : A) :
    (verschiebung p A a) ^ p
      = ((WithConv.toConv (LinearMap.id : A →ₗ[ZMod p] A)) ^ p).ofConv a := by
  haveI : CharP A p := charP_carrier (ZMod p) p A
  set b := Module.Free.chooseBasis (ZMod p) A
  rw [show verschiebung p A a = verschiebungAux p A b a from rfl,
    verschiebungAux_apply p A b a, sum_pow_char,
    ofConv_pow_toConv_id_eq_sum (ZMod p) p A b a]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_pow, ZMod.pow_card]

private theorem pow_verschiebung (a : A) :
    verschiebung p A (a ^ p)
      = ((WithConv.toConv (LinearMap.id : A →ₗ[ZMod p] A)) ^ p).ofConv a := by
  haveI : CharP A p := charP_carrier (ZMod p) p A
  haveI : CharP (WithConv (A →ₗ[ZMod p] ZMod p)) p := charP_convDual (ZMod p) p A
  set b := Module.Free.chooseBasis (ZMod p) A

  have stepB : ∀ i : Module.Free.ChooseBasisIndex (ZMod p) A,
      (b.coord i) ∘ₗ (frobeniusCoalgHom p A).toLinearMap
      = ∑ j, b.coord i ((b j) ^ p) • b.coord j := by
    intro i
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, LinearMap.sum_apply]
    simp_rw [LinearMap.smul_apply, smul_eq_mul]
    have hxp : (frobeniusCoalgHom p A).toLinearMap x = ∑ j, b.coord j x • (b j) ^ p := by
      rw [frobeniusCoalgHom_toLinearMap, frobeniusLinear_apply]
      conv_lhs => rw [← b.sum_repr x]
      rw [sum_pow_char]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_pow, ZMod.pow_card, Basis.coord_apply]
    rw [hxp, map_sum]
    simp_rw [map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

  have stepAll : ∀ i : Module.Free.ChooseBasisIndex (ZMod p) A,
      ((WithConv.toConv (b.coord i) : WithConv (A →ₗ[ZMod p] ZMod p)) ^ p).ofConv (a ^ p)
      = ∑ j, b.coord i ((b j) ^ p)
          * ((WithConv.toConv (b.coord j) : WithConv (A →ₗ[ZMod p] ZMod p)) ^ p).ofConv a := by
    intro i

    have hA := convPow_comp_coalgHom
      (WithConv.toConv (b.coord i) : WithConv (A →ₗ[ZMod p] ZMod p)) (frobeniusCoalgHom p A) p
    rw [WithConv.ofConv_toConv] at hA
    have hAa : ((WithConv.toConv (b.coord i) : WithConv (A →ₗ[ZMod p] ZMod p)) ^ p).ofConv (a ^ p)
        = ((WithConv.toConv ((b.coord i) ∘ₗ (frobeniusCoalgHom p A).toLinearMap) :
            WithConv (A →ₗ[ZMod p] ZMod p)) ^ p).ofConv a := by
      rw [hA, WithConv.ofConv_toConv, LinearMap.comp_apply]
      rfl
    rw [hAa, stepB i]

    have stepC : (WithConv.toConv (∑ j, b.coord i ((b j) ^ p) • b.coord j) :
          WithConv (A →ₗ[ZMod p] ZMod p)) ^ p
        = ∑ j, b.coord i ((b j) ^ p)
            • (WithConv.toConv (b.coord j) : WithConv (A →ₗ[ZMod p] ZMod p)) ^ p := by
      rw [WithConv.toConv_sum]
      simp_rw [WithConv.toConv_smul]
      rw [sum_pow_char]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_pow, ZMod.pow_card]
    rw [stepC, WithConv.ofConv_sum, LinearMap.sum_apply]
    simp_rw [WithConv.ofConv_smul, LinearMap.smul_apply, smul_eq_mul]

  rw [show verschiebung p A (a ^ p) = verschiebungAux p A b (a ^ p) from rfl,
    verschiebungAux_apply p A b (a ^ p),
    Finset.sum_congr rfl (fun i _ => by rw [stepAll i] :
      ∀ i ∈ Finset.univ,
        ((WithConv.toConv (b.coord i) : WithConv (A →ₗ[ZMod p] ZMod p)) ^ p).ofConv (a ^ p) • b i
        = (∑ j, b.coord i ((b j) ^ p)
            * ((WithConv.toConv (b.coord j) : WithConv (A →ₗ[ZMod p] ZMod p)) ^ p).ofConv a)
              • b i),
    ofConv_pow_toConv_id_eq_sum (ZMod p) p A b a]

  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpull : ∀ i : Module.Free.ChooseBasisIndex (ZMod p) A,
      (b.coord i ((b j) ^ p)
          * ((WithConv.toConv (b.coord j) : WithConv (A →ₗ[ZMod p] ZMod p)) ^ p).ofConv a) • b i
      = ((WithConv.toConv (b.coord j) : WithConv (A →ₗ[ZMod p] ZMod p)) ^ p).ofConv a
          • (b.coord i ((b j) ^ p) • b i) := by
    intro i
    rw [mul_comm, mul_smul]
  simp_rw [hpull]
  rw [← Finset.smul_sum]
  congr 1
  simp_rw [Basis.coord_apply]
  exact b.sum_repr ((b j) ^ p)

private theorem toConv_pow_ofConv_frobenius (φ : A →ₗ[ZMod p] ZMod p) (a : A) :
    ((WithConv.toConv φ : WithConv (A →ₗ[ZMod p] ZMod p)) ^ p).ofConv (a ^ p)
      = φ (((WithConv.toConv (LinearMap.id : A →ₗ[ZMod p] A)) ^ p).ofConv a) := by
  rw [← dual_apply_verschiebung p A (a ^ p) φ, pow_verschiebung p A a]

private theorem pow_verschiebung_eq_counit_of_killed
    (hkilled : (WithConv.toConv (LinearMap.id : A →ₗ[ZMod p] A)) ^ p = 1) (a : A) :
    verschiebung p A (a ^ p) = algebraMap (ZMod p) A (Coalgebra.counit (R := ZMod p) a) := by
  rw [pow_verschiebung p A a, hkilled, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]

private theorem verschiebung_pow_eq_counit_of_killed
    (hkilled : (WithConv.toConv (LinearMap.id : A →ₗ[ZMod p] A)) ^ p = 1) (a : A) :
    (verschiebung p A a) ^ p = algebraMap (ZMod p) A (Coalgebra.counit (R := ZMod p) a) := by
  rw [verschiebung_pow p A a, hkilled, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]

end MainTheorems

section K3D

variable (p : ℕ) [Fact p.Prime]
variable (A : Type v) [CommRing A] [Bialgebra (ZMod p) A] [Coalgebra.IsCocomm (ZMod p) A]
variable [Module.Finite (ZMod p) A] [Module.Free (ZMod p) A]

private theorem toDual_pow (ψ : CartierDual (ZMod p) A) (n : ℕ) :
    CartierDual.toDual (ZMod p) A (ψ ^ n)
      = ((WithConv.toConv (CartierDual.toDual (ZMod p) A ψ) :
          WithConv (A →ₗ[ZMod p] ZMod p)) ^ n).ofConv := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, CartierDual.one_def, CartierDual.toDual_ofDual, LinearMap.convOne_def,
        WithConv.ofConv_toConv]
      apply LinearMap.ext
      intro a
      simp
  | succ n ih =>
      rw [pow_succ, pow_succ, CartierDual.toDual_mul, ih, WithConv.toConv_ofConv]

private theorem k3D_of_killed
    (hkilled : (WithConv.toConv (LinearMap.id : A →ₗ[ZMod p] A)) ^ p = 1)
    (Fk : A →ₐc[ZMod p] A) (hFk : ∀ x, Fk x = x ^ p)
    (FD : CartierDual (ZMod p) A →ₐ[ZMod p] CartierDual (ZMod p) A) (hFD : ∀ ψ, FD ψ = ψ ^ p) :
    (FD : CartierDual (ZMod p) A →ₗ[ZMod p] CartierDual (ZMod p) A) ∘ₗ
        (CartierDual.map Fk : CartierDual (ZMod p) A →ₗ[ZMod p] CartierDual (ZMod p) A)
      = Algebra.linearMap (ZMod p) (CartierDual (ZMod p) A) ∘ₗ Coalgebra.counit := by
  apply LinearMap.ext
  intro ψ
  apply CartierDual.ext
  intro a
  have hL : (((FD : CartierDual (ZMod p) A →ₗ[ZMod p] CartierDual (ZMod p) A) ∘ₗ
      (CartierDual.map Fk : CartierDual (ZMod p) A →ₗ[ZMod p] CartierDual (ZMod p) A)) ψ) a
        = (ψ ^ p) (a ^ p) := by
    rw [LinearMap.comp_apply]
    change FD (CartierDual.map Fk ψ) a = _
    rw [hFD, ← map_pow, CartierDual.map_apply, hFk]
  have hR : ((Algebra.linearMap (ZMod p) (CartierDual (ZMod p) A) ∘ₗ Coalgebra.counit) ψ) a
        = Coalgebra.counit (R := ZMod p) a * ψ 1 := by
    rw [LinearMap.comp_apply, Algebra.linearMap_apply, CartierDual.algebraMap_apply,
      CartierDual.counit_apply]
  rw [hL]
  refine Eq.trans ?_ hR.symm
  have h3 : (ψ ^ p) (a ^ p)
      = ((WithConv.toConv (CartierDual.toDual (ZMod p) A ψ) :
          WithConv (A →ₗ[ZMod p] ZMod p)) ^ p).ofConv (a ^ p) := by
    rw [← CartierDual.toDual_apply, toDual_pow]
  rw [h3, toConv_pow_ofConv_frobenius p A, hkilled, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, map_smul,
    CartierDual.toDual_apply, smul_eq_mul]

end K3D

end KTailFrobVer
p2m_reactivate "P2MW.S_ModularCurve_frobenius_comp_verschiebung_eq_unit_counit_of_model_jZero_torsion.KTailFrobVer"

namespace KTailKilled

variable {R : Type*} [CommRing R] {B : Type*} [CommRing B] [Algebra R B]
  [Module.Free R B] [Module.Finite R B] {K : Type*} [Field K] [Algebra R K]

private theorem apply_eq_sum (v : Module.Basis (Module.Free.ChooseBasisIndex R B) R B)
    (x : B →ₐ[R] K) (y : B) :
    x y = ∑ j, algebraMap R K (v.repr y j) * x (v j) := by
  conv_lhs => rw [← v.sum_repr y]
  simp [map_sum, Algebra.smul_def]

private theorem eq_zero_of_forall_algHom_eq_zero (hinj : Function.Injective (algebraMap R K))
    (hcard : Nat.card (B →ₐ[R] K) = Module.finrank R B) (b : B) (hb : ∀ x : B →ₐ[R] K, x b = 0) :
    b = 0 := by
  classical
  haveI : Nontrivial R := (algebraMap R K).domain_nontrivial
  let v := Module.Free.chooseBasis R B
  by_cases hι : IsEmpty (Module.Free.ChooseBasisIndex R B)
  · apply v.repr.injective
    ext i
    exact hι.elim i
  rw [not_isEmpty_iff] at hι
  have hn : Module.finrank R B ≠ 0 := by
    rw [Module.finrank_eq_card_chooseBasisIndex]
    exact Fintype.card_ne_zero
  haveI : Finite (B →ₐ[R] K) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hn)
  letI := Fintype.ofFinite (B →ₐ[R] K)
  have hc : Fintype.card (Module.Free.ChooseBasisIndex R B) = Fintype.card (B →ₐ[R] K) := by
    rw [← Nat.card_eq_fintype_card (α := B →ₐ[R] K), hcard, Module.finrank_eq_card_chooseBasisIndex]
  let σ := Fintype.equivOfCardEq hc
  let M : Matrix (Module.Free.ChooseBasisIndex R B) (Module.Free.ChooseBasisIndex R B) K :=
    fun i j => σ i (v j)

  have hDed : LinearIndependent K (fun i => ((σ i : B →ₐ[R] K) : B → K)) := by
    have h2 : Function.Injective (fun i => ((σ i : B →ₐ[R] K) : B →* K)) :=
      AlgHom.coe_monoidHom_injective.comp σ.injective
    have h3 := (linearIndependent_monoidHom B K).comp _ h2
    simpa [AlgHom.coe_toMonoidHom, Function.comp_def] using h3
  have hrows : LinearIndependent K M.row := by
    rw [Fintype.linearIndependent_iff] at hDed ⊢
    intro c hc0 i
    have hcol : ∀ j, ∑ i, c i * M i j = 0 := by
      intro j
      have := congr_fun hc0 j
      simpa [Finset.sum_apply, Matrix.row] using this
    refine hDed c ?_ i
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    calc ∑ i, c i * σ i y
        = ∑ i, c i * ∑ j, algebraMap R K (v.repr y j) * M i j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [apply_eq_sum v (σ i) y]
      _ = ∑ j, algebraMap R K (v.repr y j) * ∑ i, c i * M i j := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = 0 := by simp [hcol]
  have hmv : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)

  have hvec : M.mulVec (fun j => algebraMap R K (v.repr b j)) = M.mulVec 0 := by
    rw [Matrix.mulVec_zero]
    funext i
    have hbi := hb (σ i)
    rw [apply_eq_sum v] at hbi
    simpa [Matrix.mulVec, dotProduct, M, mul_comm] using hbi
  have hr := congr_fun (hmv hvec)
  apply v.repr.injective
  ext j
  have hj : algebraMap R K (v.repr b j) = algebraMap R K 0 := by
    rw [map_zero]
    exact hr j
  simpa using hinj hj

private theorem eq_of_forall_algHom_eq (hinj : Function.Injective (algebraMap R K))
    (hcard : Nat.card (B →ₐ[R] K) = Module.finrank R B) {b₁ b₂ : B}
    (h : ∀ x : B →ₐ[R] K, x b₁ = x b₂) : b₁ = b₂ := by
  rw [← sub_eq_zero]
  exact eq_zero_of_forall_algHom_eq_zero hinj hcard (b₁ - b₂) fun x => by rw [map_sub, h x, sub_self]

end KTailKilled
p2m_reactivate "P2MW.S_ModularCurve_frobenius_comp_verschiebung_eq_unit_counit_of_model_jZero_torsion.KTailFrobVer"

namespace KTailKilled

section Base
variable (p : ℕ)

private theorem algebraMap_injective :
    Function.Injective (algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) := by
  rw [IsScalarTower.algebraMap_eq (GaloisRep.ratLocalizedAt p) ℚ (AlgebraicClosure ℚ)]
  exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective.comp Subtype.val_injective

end Base
p2m_reactivate "P2MW.S_ModularCurve_frobenius_comp_verschiebung_eq_unit_counit_of_model_jZero_torsion.KTailFrobVer"

set_option maxHeartbeats 4000000 in

private theorem toConv_id_pow_eq_one
    (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          ↥(Submodule.torsionBy ℤ (JZero M) (p : ℤ) ⊓
            ⨆ m : ℕ, LinearMap.ker (heckeOperatorBar M ⟨p, hp.out⟩ ^ m)))
    (he_add : ∀ f g, e (f * g) = e f + e g) :
    WithConv.toConv (AlgHom.id (GaloisRep.ratLocalizedAt p) H) ^ p = 1 := by
  classical
  by_cases hι : IsEmpty (Module.Free.ChooseBasisIndex (GaloisRep.ratLocalizedAt p) H)
  · haveI : Subsingleton H :=
      (Module.Free.chooseBasis (GaloisRep.ratLocalizedAt p) H).repr.toEquiv.subsingleton
    exact (WithConv.equiv _).injective (AlgHom.ext fun _ => Subsingleton.elim _ _)
  rw [not_isEmpty_iff] at hι
  have hcard := HopfAlgebra.natCard_algHom_eq_finrank_of_charZero (GaloisRep.ratLocalizedAt p) H
    (AlgebraicClosure ℚ)
  have sepH : ∀ {a b : H},
      (∀ x : H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ, x a = x b) → a = b :=
    fun h => eq_of_forall_algHom_eq (algebraMap_injective p) hcard h
  have hE : ∀ {x y : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)},
      ((e x : JZero M)) = (e y : JZero M) → x = y :=
    fun h => e.injective (Subtype.ext h)
  have hadd : ∀ x y : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
      ((e (x * y) : JZero M)) = (e x : JZero M) + (e y : JZero M) := by
    intro x y
    rw [he_add]
    rfl
  have hone : ((e 1 : JZero M)) = 0 := by
    have h := hadd 1 1
    rw [one_mul] at h
    have h' : (e 1 : JZero M) + (e 1 : JZero M) = (e 1 : JZero M) + 0 := by
      rw [add_zero]
      exact h.symm
    exact add_left_cancel h'

  have hpow : ∀ (x : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) (n : ℕ),
      ((e (x ^ n) : JZero M)) = n • (e x : JZero M) := by
    intro x n
    induction n with
    | zero => rw [pow_zero, hone, zero_nsmul]
    | succ n ih => rw [pow_succ, hadd, ih, succ_nsmul]
  have hpt : ∀ x : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), x ^ p = 1 := by
    intro x
    apply hE
    rw [hpow, hone]
    have hmem : (e x : JZero M) ∈ Submodule.torsionBy ℤ (JZero M) (p : ℤ) :=
      (Submodule.mem_inf.mp (e x).2).1
    rw [Submodule.mem_torsionBy_iff] at hmem
    rw [← natCast_zsmul]
    exact hmem

  have hcomp : ∀ (x : H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) (n : ℕ),
      WithConv.toConv (x.comp ((WithConv.toConv (AlgHom.id (GaloisRep.ratLocalizedAt p) H) ^ n).ofConv)) =
        WithConv.toConv x ^ n := by
    intro x n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero]
      refine (WithConv.equiv _).injective (AlgHom.ext fun h => ?_)
      show x (algebraMap (GaloisRep.ratLocalizedAt p) H (Coalgebra.counit h)) =
        algebraMap (GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) (Coalgebra.counit h)
      exact x.commutes _
    | succ n ih =>
      rw [pow_succ (WithConv.toConv (AlgHom.id (GaloisRep.ratLocalizedAt p) H)) n,
        AlgHom.comp_convMul_distrib, WithConv.toConv_ofConv, ih, WithConv.ofConv_toConv,
        AlgHom.comp_id, pow_succ]
  refine (WithConv.equiv _).injective (AlgHom.ext fun h => ?_)
  apply sepH
  intro x
  have h1 : x ((WithConv.toConv (AlgHom.id (GaloisRep.ratLocalizedAt p) H) ^ p).ofConv h) =
      (WithConv.toConv x ^ p).ofConv h :=
    congrArg (fun g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) => g.ofConv h)
      (hcomp x p)
  have h2 : (WithConv.toConv x ^ p).ofConv h =
      x ((1 : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] H)).ofConv h) := by
    rw [hpt (WithConv.toConv x)]
    exact (x.commutes _).symm
  exact h1.trans h2

private theorem toConv_linearMap_id_pow_eq_one_baseChange
    (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          ↥(Submodule.torsionBy ℤ (JZero M) (p : ℤ) ⊓
            ⨆ m : ℕ, LinearMap.ker (heckeOperatorBar M ⟨p, hp.out⟩ ^ m)))
    (he_add : ∀ f g, e (f * g) = e f + e g) :
    (WithConv.toConv (LinearMap.id :
        TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H →ₗ[ZMod p]
          TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H)) ^ p = 1 := by
  have h1 := HopfAlgebra.toConv_id_pow_eq_one_baseChange (ZMod p) p (toConv_id_pow_eq_one M p H e he_add)
  have h2 := congrArg
    (fun g : WithConv (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H →ₐ[ZMod p]
        TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H) => WithConv.toConv g.ofConv.toLinearMap) h1
  simpa using h2

end KTailKilled
p2m_reactivate "P2MW.S_ModularCurve_frobenius_comp_verschiebung_eq_unit_counit_of_model_jZero_torsion.KTailFrobVer"

theorem solution
    (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          ↥(Submodule.torsionBy ℤ (JZero M) (p : ℤ) ⊓
            ⨆ m : ℕ, LinearMap.ker (heckeOperatorBar M ⟨p, hp.out⟩ ^ m)))
    (he_add : ∀ f g, e (f * g) = e f + e g) :
    ∀ (Fk : TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H →ₐc[ZMod p]
        TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H),
      (∀ x, Fk x = x ^ p) →
    ∀ (FD : CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H) →ₐ[ZMod p]
        CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H)),
      (∀ ψ, FD ψ = ψ ^ p) →
      (FD : CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H) →ₗ[ZMod p]
          CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H)) ∘ₗ
          (CartierDual.map Fk :
            CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H) →ₗ[ZMod p]
              CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H)) =
        Algebra.linearMap (ZMod p)
            (CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H)) ∘ₗ
          Coalgebra.counit := by
  intro Fk hFk FD hFD
  exact KTailFrobVer.k3D_of_killed p (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H)
    (KTailKilled.toConv_linearMap_id_pow_eq_one_baseChange M p H e he_add) Fk hFk FD hFD

end S_ModularCurve_frobenius_comp_verschiebung_eq_unit_counit_of_model_jZero_torsion
end P2MW
export P2MW.S_ModularCurve_frobenius_comp_verschiebung_eq_unit_counit_of_model_jZero_torsion (solution)
