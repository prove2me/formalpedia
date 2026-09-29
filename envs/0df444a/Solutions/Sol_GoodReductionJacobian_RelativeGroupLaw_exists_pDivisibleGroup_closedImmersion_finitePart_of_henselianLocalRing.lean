-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/48c8602f-337d-5ce2-ab57-9db6ba4208b0

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

open Coalgebra Bialgebra WithConv

scoped instance (priority := 50) YF.moduleFinite_quotient {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] (I : Ideal A) : Module.Finite R (A ⧸ I) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ_surjective R I)

namespace YF

namespace Hopf

open PDivisibleGroup.Hopf

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Bialgebra R A]
variable {L : Type*} [CommRing L] [Algebra R L]

theorem toConv_pow_eq_one_of_torsionIdeal_le_ker (f : A →ₐ[R] L) (n : ℕ)
    (h : torsionIdeal R A n ≤ RingHom.ker f) : (toConv f) ^ n = 1 := by
  apply WithConv.ofConv_injective
  refine AlgHom.ext fun a => ?_
  change ((toConv f) ^ n) a = (1 : WithConv (A →ₐ[R] L)) a
  rw [pow_apply_eq_apply_nsmulAlgHom, AlgHom.convOne_apply]
  have hdec : a = algebraMap R A (counit (R := R) a) + (a - algebraMap R A (counit (R := R) a)) := by
    abel
  conv_lhs => rw [hdec]
  change f (nsmulAlgHom R A n _) = _
  rw [map_add, map_add, nsmulAlgHom_algebraMap, AlgHom.commutes]
  have hmem : nsmulAlgHom R A n (a - algebraMap R A (counit (R := R) a)) ∈ torsionIdeal R A n :=
    nsmulAlgHom_mem_torsionIdeal R A (sub_algebraMap_counit_mem_augIdeal R A a) n
  have hker : f (nsmulAlgHom R A n (a - algebraMap R A (counit (R := R) a))) = 0 := h hmem
  rw [hker, add_zero]

theorem torsionIdeal_le_ker_of_toConv_pow_eq_one (f : A →ₐ[R] L) (n : ℕ)
    (h : (toConv f) ^ n = 1) : torsionIdeal R A n ≤ RingHom.ker f := fun _ ha =>
  apply_eq_zero_of_mem_torsionIdeal_of_pow_eq_one R A (toConv f) n h ha

theorem toConv_pow_eq_one_iff (f : A →ₐ[R] L) (n : ℕ) :
    (toConv f) ^ n = 1 ↔ torsionIdeal R A n ≤ RingHom.ker f :=
  ⟨torsionIdeal_le_ker_of_toConv_pow_eq_one f n, toConv_pow_eq_one_of_torsionIdeal_le_ker f n⟩

noncomputable def quotientPointEquiv (n : ℕ) :
    (A ⧸ torsionIdeal R A n →ₐ[R] L) ≃ {f : A →ₐ[R] L // (toConv f) ^ n = 1} where
  toFun g := ⟨g.comp (Ideal.Quotient.mkₐ R (torsionIdeal R A n)),
    toConv_pow_eq_one_of_torsionIdeal_le_ker _ n (fun a ha => by
      rw [RingHom.mem_ker]
      change g (Ideal.Quotient.mk (torsionIdeal R A n) a) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero])⟩
  invFun f := Ideal.Quotient.liftₐ (torsionIdeal R A n) f.1
    (fun a ha => torsionIdeal_le_ker_of_toConv_pow_eq_one f.1 n f.2 ha)
  left_inv g := by
    refine AlgHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  right_inv f := by
    apply Subtype.ext
    refine AlgHom.ext fun a => ?_
    rfl

@[scoped simp] theorem quotientPointEquiv_apply_coe (n : ℕ) (g : A ⧸ torsionIdeal R A n →ₐ[R] L) :
    ((quotientPointEquiv (L := L) n g : {f : A →ₐ[R] L // (toConv f) ^ n = 1}) : A →ₐ[R] L) =
      g.comp (Ideal.Quotient.mkₐ R (torsionIdeal R A n)) := rfl

theorem quotientPointEquiv_symm_apply_mk (n : ℕ) (f : {f : A →ₐ[R] L // (toConv f) ^ n = 1})
    (a : A) :
    (quotientPointEquiv (L := L) n).symm f (Ideal.Quotient.mk (torsionIdeal R A n) a) = f.1 a := rfl

end Hopf
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Hopf"

namespace Law

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmul_add (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (m n : ℕ) (x : SchemeHomOver t f) :
    G.nsmul t (m + n) x = G.mul t (G.nsmul t m x) (G.nsmul t n x) := by
  induction n with
  | zero => rw [Nat.add_zero, G.nsmul_zero, G.mul_one]
  | succ n ih => rw [Nat.add_succ, G.nsmul_succ, G.nsmul_succ, ih, G.mul_assoc]

theorem nsmul_mul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (m n : ℕ) (x : SchemeHomOver t f) :
    G.nsmul t (m * n) x = G.nsmul t n (G.nsmul t m x) := by
  induction n with
  | zero => rw [Nat.mul_zero, G.nsmul_zero, G.nsmul_zero]
  | succ n ih => rw [Nat.mul_succ, nsmul_add, ih, G.nsmul_succ]

theorem isTorsionPoint_mul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (m k : ℕ) {x : SchemeHomOver t f}
    (hx : G.IsTorsionPoint t m x) : G.IsTorsionPoint t (m * k) x := by
  rw [RelativeGroupLaw.isTorsionPoint_def] at hx ⊢
  rw [nsmul_mul, hx, G.nsmul_unit]

theorem torsionSubset_mono (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (m k : ℕ) :
    G.torsionSubset t m ⊆ G.torsionSubset t (m * k) := fun _ hx =>
  isTorsionPoint_mul G t m k hx

theorem torsionSubset_pow_succ (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (p v : ℕ) :
    G.torsionSubset t (p ^ v) ⊆ G.torsionSubset t (p ^ (v + 1)) := by
  rw [pow_succ]
  exact torsionSubset_mono G t (p ^ v) p

theorem isTorsionPoint_pow_iff (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    G.IsTorsionPoint t n x ↔ G.nsmul t n x = G.one t := Iff.rfl

end Law
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Hopf"

namespace Yoneda

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
p2m_open_scoped "TensorProduct Coalgebra.TensorProduct Bialgebra.TensorProduct"

variable {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f) (m n : ℕ)
  (hmn : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)), L.torsionSubset t m ⊆ L.torsionSubset t n)
  (HB : Type) [CommRing HB] [HopfAlgebra R HB] [Module.Finite R HB] (HJ : Type) [CommRing HJ] [HopfAlgebra R HJ] [Module.Finite R HJ]
  (eB : ∀ (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T],
    WithConv (HB →ₐ[R] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) m)
  (eB_mul : ∀ (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] (φ ψ : WithConv (HB →ₐ[R] T)),
    ((eB T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (eB T φ).val (eB T ψ).val)
  (eB_nat : ∀ (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T'] [Module.Finite R T] [Module.Finite R T']
    (a : T →ₐ[R] T') (φ : WithConv (HB →ₐ[R] T)),
    ((eB T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (eB T φ).val.1)
  (eJ : ∀ (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T],
    WithConv (HJ →ₐ[R] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n)
  (eJ_mul : ∀ (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] (φ ψ : WithConv (HJ →ₐ[R] T)),
    ((eJ T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (eJ T φ).val (eJ T ψ).val)
  (eJ_nat : ∀ (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T'] [Module.Finite R T] [Module.Finite R T']
    (a : T →ₐ[R] T') (φ : WithConv (HJ →ₐ[R] T)),
    ((eJ T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (eJ T φ).val.1)

noncomputable def univPoint :
    L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R HB))) n :=
  ⟨(eB HB (toConv (AlgHom.id R HB))).val, hmn _ (eB HB (toConv (AlgHom.id R HB))).2⟩

private noncomputable def _root_.YF.Yoneda.trans : HJ →ₐ[R] HB :=
  ((eJ HB).symm (univPoint L m n hmn HB eB)).ofConv

p2m_export "YF.Yoneda" "trans"
include eB_nat eJ_nat in

theorem eJ_comp_trans (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] (x : WithConv (HB →ₐ[R] T)) :
    ((eJ T (toConv (x.ofConv.comp (trans L m n hmn HB HJ eB eJ)))).val : SchemeHomOver _ f).1 =
      ((eB T x).val : SchemeHomOver _ f).1 := by
  have h1 := eJ_nat HB T x.ofConv ((eJ HB).symm (univPoint L m n hmn HB eB))
  rw [Equiv.apply_symm_apply] at h1
  have h2 := eB_nat HB T x.ofConv (toConv (AlgHom.id R HB))
  have hx : x.ofConv.comp (toConv (AlgHom.id R HB)).ofConv = x.ofConv := AlgHom.comp_id _
  rw [hx, toConv_ofConv] at h2
  exact h1.trans h2.symm

include eB_nat eJ_nat in
theorem eJ_comp_trans_val (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] (x : WithConv (HB →ₐ[R] T)) :
    ((eJ T (toConv (x.ofConv.comp (trans L m n hmn HB HJ eB eJ)))).val : SchemeHomOver _ f) =
      ⟨((eB T x).val : SchemeHomOver _ f).1, ((eB T x).val : SchemeHomOver _ f).2⟩ :=
  Subtype.ext (eJ_comp_trans L m n hmn HB HJ eB eB_nat eJ eJ_nat T x)

include eB_mul eB_nat eJ_mul eJ_nat in

theorem toConv_mul_comp_trans (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] (x y : WithConv (HB →ₐ[R] T)) :
    toConv ((x * y).ofConv.comp (trans L m n hmn HB HJ eB eJ)) =
      toConv (x.ofConv.comp (trans L m n hmn HB HJ eB eJ)) *
        toConv (y.ofConv.comp (trans L m n hmn HB HJ eB eJ)) := by
  apply (eJ T).injective
  apply Subtype.ext
  rw [eJ_mul, eJ_comp_trans_val L m n hmn HB HJ eB eB_nat eJ eJ_nat T x,
    eJ_comp_trans_val L m n hmn HB HJ eB eB_nat eJ eJ_nat T y,
    eJ_comp_trans_val L m n hmn HB HJ eB eB_nat eJ eJ_nat T (x * y), eB_mul]

include eB_mul eB_nat eJ_mul eJ_nat in
theorem toConv_one_comp_trans (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] :
    toConv ((1 : WithConv (HB →ₐ[R] T)).ofConv.comp (trans L m n hmn HB HJ eB eJ)) =
      (1 : WithConv (HJ →ₐ[R] T)) := by

  apply (eJ T).injective
  apply Subtype.ext
  letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R T)))

  have hJ : ((eJ T 1).val : SchemeHomOver _ f) = L.one _ := by
    have h := eJ_mul T 1 1
    rw [one_mul] at h

    have h' : (eJ T 1).val * (eJ T 1).val = (eJ T 1).val := h.symm
    exact mul_eq_left.1 h'
  have hB : ((eB T 1).val : SchemeHomOver _ f) = L.one _ := by
    have h := eB_mul T 1 1
    rw [one_mul] at h
    have h' : (eB T 1).val * (eB T 1).val = (eB T 1).val := h.symm
    exact mul_eq_left.1 h'
  rw [eJ_comp_trans_val L m n hmn HB HJ eB eB_nat eJ eJ_nat T 1, hJ]
  exact Subtype.ext (congrArg Subtype.val hB)

theorem lmul'_comp_map_includeLeft_includeRight (A : Type) [CommRing A] [Algebra R A] :
    (Algebra.TensorProduct.lmul' R : (A ⊗[R] A) ⊗[R] (A ⊗[R] A) →ₐ[R] A ⊗[R] A).comp
        (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A)
          (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A)) =
      AlgHom.id R (A ⊗[R] A) := by
  refine Algebra.TensorProduct.ext' fun a b => ?_
  change Algebra.TensorProduct.lmul' R
      (Algebra.TensorProduct.map Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeRight
        (a ⊗ₜ[R] b)) = a ⊗ₜ[R] b
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

include eB_mul eB_nat eJ_mul eJ_nat in

theorem counit_comp_trans :
    (Bialgebra.counitAlgHom R HB).comp (trans L m n hmn HB HJ eB eJ) = Bialgebra.counitAlgHom R HJ := by
  have h := congrArg WithConv.ofConv (toConv_one_comp_trans L m n hmn HB HJ eB eB_mul eB_nat eJ eJ_mul eJ_nat R)
  rw [ofConv_toConv, AlgHom.convOne_def, AlgHom.convOne_def, ofConv_toConv, ofConv_toConv,
    Algebra.ofId_self, AlgHom.id_comp, AlgHom.id_comp] at h
  exact h

include eB_mul eB_nat eJ_mul eJ_nat in

theorem map_comp_comul_trans :
    (Algebra.TensorProduct.map (trans L m n hmn HB HJ eB eJ) (trans L m n hmn HB HJ eB eJ)).comp
        (Bialgebra.comulAlgHom R HJ) =
      (Bialgebra.comulAlgHom R HB).comp (trans L m n hmn HB HJ eB eJ) := by
  have h := congrArg WithConv.ofConv
    (toConv_mul_comp_trans L m n hmn HB HJ eB eB_mul eB_nat eJ eJ_mul eJ_nat (HB ⊗[R] HB)
      (toConv (Algebra.TensorProduct.includeLeft : HB →ₐ[R] HB ⊗[R] HB))
      (toConv (Algebra.TensorProduct.includeRight : HB →ₐ[R] HB ⊗[R] HB)))
  rw [ofConv_toConv, AlgHom.convMul_def, AlgHom.convMul_def, ofConv_toConv, ofConv_toConv, ofConv_toConv,
    ofConv_toConv, ofConv_toConv, ofConv_toConv, Algebra.TensorProduct.map_comp,
    AlgHom.comp_assoc, AlgHom.comp_assoc, AlgHom.comp_assoc] at h

  rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc (Algebra.TensorProduct.lmul' R),
    lmul'_comp_map_includeLeft_includeRight, AlgHom.id_comp, AlgHom.id_comp] at h
  exact h.symm

noncomputable def transBialgHom : HJ →ₐc[R] HB :=
  BialgHom.ofAlgHom (trans L m n hmn HB HJ eB eJ)
    (counit_comp_trans L m n hmn HB HJ eB eB_mul eB_nat eJ eJ_mul eJ_nat)
    (map_comp_comul_trans L m n hmn HB HJ eB eB_mul eB_nat eJ eJ_mul eJ_nat)

theorem transBialgHom_coe :
    (transBialgHom L m n hmn HB HJ eB eB_mul eB_nat eJ eJ_mul eJ_nat : HJ →ₐ[R] HB) =
      trans L m n hmn HB HJ eB eJ := rfl

include eJ_mul in
theorem eJ_one (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] :
    ((eJ T 1).val : SchemeHomOver _ f) = L.one _ := by
  letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R T)))
  have h := eJ_mul T 1 1
  rw [one_mul] at h
  have h' : (eJ T 1).val * (eJ T 1).val = (eJ T 1).val := h.symm
  exact mul_eq_left.1 h'

include eJ_mul in
theorem eJ_pow (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] (g : WithConv (HJ →ₐ[R] T)) (k : ℕ) :
    ((eJ T (g ^ k)).val : SchemeHomOver _ f) = L.nsmul _ k (eJ T g).val := by
  induction k with
  | zero => rw [pow_zero, RelativeGroupLaw.nsmul_zero, eJ_one L n HJ eJ eJ_mul]
  | succ k ih => rw [pow_succ, eJ_mul, ih, RelativeGroupLaw.nsmul_succ]

include eJ_mul in

theorem pow_eq_one_iff_mem_torsionSubset (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T]
    (g : WithConv (HJ →ₐ[R] T)) :
    g ^ m = 1 ↔ ((eJ T g).val : SchemeHomOver _ f) ∈ L.torsionSubset _ m := by
  rw [RelativeGroupLaw.mem_torsionSubset, RelativeGroupLaw.isTorsionPoint_def,
    ← eJ_pow L n HJ eJ eJ_mul, ← eJ_one L n HJ eJ eJ_mul T]
  constructor
  · intro h
    rw [h]
  · intro h
    exact (eJ T).injective (Subtype.ext h)

include eB_nat eJ_mul eJ_nat in
theorem trans_pow_eq_one : (toConv (trans L m n hmn HB HJ eB eJ)) ^ m = 1 := by
  rw [pow_eq_one_iff_mem_torsionSubset L m n HJ eJ eJ_mul]
  have h : ((eJ HB (toConv (trans L m n hmn HB HJ eB eJ))).val : SchemeHomOver _ f) =
      (eB HB (toConv (AlgHom.id R HB))).val := by
    have h1 := eJ_comp_trans_val L m n hmn HB HJ eB eB_nat eJ eJ_nat HB (toConv (AlgHom.id R HB))
    have h2 : (toConv (AlgHom.id R HB)).ofConv.comp (trans L m n hmn HB HJ eB eJ) =
        trans L m n hmn HB HJ eB eJ := AlgHom.id_comp _
    rw [h2] at h1
    rw [h1]
  rw [h]
  exact (eB HB (toConv (AlgHom.id R HB))).2

include eB_nat eJ_mul eJ_nat in
theorem torsionIdeal_le_ker_trans :
    PDivisibleGroup.Hopf.torsionIdeal R HJ m ≤ RingHom.ker (trans L m n hmn HB HJ eB eJ) :=
  Hopf.torsionIdeal_le_ker_of_toConv_pow_eq_one _ m
    (trans_pow_eq_one L m n hmn HB HJ eB eB_nat eJ eJ_mul eJ_nat)

noncomputable def transBar : (HJ ⧸ PDivisibleGroup.Hopf.torsionIdeal R HJ m) →ₐ[R] HB :=
  Ideal.Quotient.liftₐ _ (trans L m n hmn HB HJ eB eJ)
    (fun _ ha => torsionIdeal_le_ker_trans L m n hmn HB HJ eB eB_nat eJ eJ_mul eJ_nat ha)

theorem transBar_comp_mk :
    (transBar L m n hmn HB HJ eB eB_nat eJ eJ_mul eJ_nat).comp
        (Ideal.Quotient.mkₐ R (PDivisibleGroup.Hopf.torsionIdeal R HJ m)) =
      trans L m n hmn HB HJ eB eJ :=
  AlgHom.ext fun _ => rfl

noncomputable def quotUnivPoint :
    L.torsionSubset (Spec.map (CommRingCat.ofHom
      (algebraMap R (HJ ⧸ PDivisibleGroup.Hopf.torsionIdeal R HJ m)))) m :=
  ⟨(eJ _ (toConv (Ideal.Quotient.mkₐ R (PDivisibleGroup.Hopf.torsionIdeal R HJ m)))).val,
    (pow_eq_one_iff_mem_torsionSubset L m n HJ eJ eJ_mul _ _).1
      ((Hopf.quotientPointEquiv (L := HJ ⧸ PDivisibleGroup.Hopf.torsionIdeal R HJ m) m
        (AlgHom.id R _)).2)⟩

private noncomputable def _root_.YF.Yoneda.inv : HB →ₐ[R] (HJ ⧸ PDivisibleGroup.Hopf.torsionIdeal R HJ m) :=
  ((eB _).symm (quotUnivPoint L m n HJ eJ eJ_mul)).ofConv

p2m_export "YF.Yoneda" "inv"
include eB_nat eJ_nat in
theorem inv_comp_trans :
    (inv L m n HB HJ eB eJ eJ_mul).comp (trans L m n hmn HB HJ eB eJ) =
      Ideal.Quotient.mkₐ R (PDivisibleGroup.Hopf.torsionIdeal R HJ m) := by
  have h := eJ_comp_trans_val L m n hmn HB HJ eB eB_nat eJ eJ_nat _ (toConv (inv L m n HB HJ eB eJ eJ_mul))
  have hinv : eB _ (toConv (inv L m n HB HJ eB eJ eJ_mul)) = quotUnivPoint L m n HJ eJ eJ_mul := by
    change eB _ ((eB _).symm (quotUnivPoint L m n HJ eJ eJ_mul)) = _
    rw [Equiv.apply_symm_apply]
  rw [hinv] at h

  have h' : eJ _ (toConv ((toConv (inv L m n HB HJ eB eJ eJ_mul)).ofConv.comp
      (trans L m n hmn HB HJ eB eJ))) =
      eJ _ (toConv (Ideal.Quotient.mkₐ R (PDivisibleGroup.Hopf.torsionIdeal R HJ m))) :=
    Subtype.ext (h.trans rfl)
  exact congrArg WithConv.ofConv ((eJ _).injective h')

include eB_nat eJ_nat in
theorem inv_comp_transBar :
    (inv L m n HB HJ eB eJ eJ_mul).comp (transBar L m n hmn HB HJ eB eB_nat eJ eJ_mul eJ_nat) =
      AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  rw [AlgHom.comp_assoc, transBar_comp_mk, inv_comp_trans L m n hmn HB HJ eB eB_nat eJ eJ_mul eJ_nat,
    AlgHom.id_comp]

omit hmn in
theorem eB_injective_val (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] {x y : WithConv (HB →ₐ[R] T)}
    (h : ((eB T x).val : SchemeHomOver _ f).1 = ((eB T y).val : SchemeHomOver _ f).1) : x = y :=
  (eB T).injective (Subtype.ext (Subtype.ext h))

include eB_nat eJ_nat in
theorem transBar_comp_inv :
    (transBar L m n hmn HB HJ eB eB_nat eJ eJ_mul eJ_nat).comp (inv L m n HB HJ eB eJ eJ_mul) =
      AlgHom.id R HB := by

  have key : ((eB HB (toConv ((transBar L m n hmn HB HJ eB eB_nat eJ eJ_mul eJ_nat).comp
      (inv L m n HB HJ eB eJ eJ_mul)))).val : SchemeHomOver _ f).1 =
      ((eB HB (toConv (AlgHom.id R HB))).val : SchemeHomOver _ f).1 := by

    have h1 := eB_nat _ HB (transBar L m n hmn HB HJ eB eB_nat eJ eJ_mul eJ_nat)
      (toConv (inv L m n HB HJ eB eJ eJ_mul))
    rw [ofConv_toConv] at h1
    rw [h1]
    have hinv : eB _ (toConv (inv L m n HB HJ eB eJ eJ_mul)) = quotUnivPoint L m n HJ eJ eJ_mul := by
      change eB _ ((eB _).symm (quotUnivPoint L m n HJ eJ eJ_mul)) = _
      rw [Equiv.apply_symm_apply]
    rw [hinv]
    change Spec.map _ ≫ ((eJ _ (toConv (Ideal.Quotient.mkₐ R
      (PDivisibleGroup.Hopf.torsionIdeal R HJ m)))).val : SchemeHomOver _ f).1 = _

    have h2 := eJ_nat HJ _ (Ideal.Quotient.mkₐ R (PDivisibleGroup.Hopf.torsionIdeal R HJ m))
      (toConv (AlgHom.id R HJ))
    have h2' : (Ideal.Quotient.mkₐ R (PDivisibleGroup.Hopf.torsionIdeal R HJ m)).comp
        (toConv (AlgHom.id R HJ)).ofConv = Ideal.Quotient.mkₐ R _ := AlgHom.comp_id _
    rw [h2'] at h2
    rw [h2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

    have hcomp : (Ideal.Quotient.mkₐ R (PDivisibleGroup.Hopf.torsionIdeal R HJ m)).toRingHom.comp
        (RingHom.id HJ) = (Ideal.Quotient.mkₐ R (PDivisibleGroup.Hopf.torsionIdeal R HJ m)).toRingHom := by
      rfl
    have hcomp' : ((transBar L m n hmn HB HJ eB eB_nat eJ eJ_mul eJ_nat).toRingHom).comp
        (Ideal.Quotient.mkₐ R (PDivisibleGroup.Hopf.torsionIdeal R HJ m)).toRingHom =
        (trans L m n hmn HB HJ eB eJ).toRingHom := by
      rfl
    rw [hcomp']

    have h3 := eJ_nat HJ HB (trans L m n hmn HB HJ eB eJ) (toConv (AlgHom.id R HJ))
    have h3' : (trans L m n hmn HB HJ eB eJ).comp (toConv (AlgHom.id R HJ)).ofConv =
        trans L m n hmn HB HJ eB eJ := AlgHom.comp_id _
    rw [h3'] at h3
    rw [← h3]
    change ((eJ HB ((eJ HB).symm (univPoint L m n hmn HB eB))).val : SchemeHomOver _ f).1 = _
    rw [Equiv.apply_symm_apply]
    rfl
  exact congrArg WithConv.ofConv (eB_injective_val L m HB eB HB key)

noncomputable def transBarEquiv : (HJ ⧸ PDivisibleGroup.Hopf.torsionIdeal R HJ m) ≃ₐ[R] HB :=
  AlgEquiv.ofAlgHom (transBar L m n hmn HB HJ eB eB_nat eJ eJ_mul eJ_nat) (inv L m n HB HJ eB eJ eJ_mul)
    (transBar_comp_inv L m n hmn HB HJ eB eB_nat eJ eJ_mul eJ_nat)
    (inv_comp_transBar L m n hmn HB HJ eB eB_nat eJ eJ_mul eJ_nat)

include eB_nat eJ_mul eJ_nat in

theorem trans_surjective : Function.Surjective (trans L m n hmn HB HJ eB eJ) := by
  intro b
  obtain ⟨q, hq⟩ := (transBarEquiv L m n hmn HB HJ eB eB_nat eJ eJ_mul eJ_nat).surjective b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨a, hq⟩

include eB_nat eJ_mul eJ_nat in

theorem ker_trans :
    RingHom.ker (trans L m n hmn HB HJ eB eJ) = PDivisibleGroup.Hopf.torsionIdeal R HJ m := by
  apply le_antisymm
  · intro a ha
    rw [RingHom.mem_ker] at ha
    have h : transBarEquiv L m n hmn HB HJ eB eB_nat eJ eJ_mul eJ_nat
        (Ideal.Quotient.mk (PDivisibleGroup.Hopf.torsionIdeal R HJ m) a) = 0 := ha
    rw [map_eq_zero_iff _ (transBarEquiv L m n hmn HB HJ eB eB_nat eJ eJ_mul eJ_nat).injective]
      at h
    exact Ideal.Quotient.eq_zero_iff_mem.1 h
  · exact torsionIdeal_le_ker_trans L m n hmn HB HJ eB eB_nat eJ eJ_mul eJ_nat

end Yoneda
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Hopf"

end YF
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Hopf P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF"

noncomputable section

namespace YF
namespace Assembly

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

variable {R : Type} [CommRing R] [HenselianLocalRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
  [IsSeparated f] [LocallyOfFiniteType f] (L : RelativeGroupLaw R f)

structure LevelDataF (n : ℕ) : Type 1 where
  H : Type
  [cr : CommRing H]
  [ha : HopfAlgebra R H]
  fin : Module.Finite R H
  flat : Module.Flat R H
  cocomm : Coalgebra.IsCocomm R H
  j : Spec (CommRingCat.of H) ⟶ L.schemeKer n
  e : ∀ (T : Type) [CommRing T] [Algebra R T],
    WithConv (H →ₐ[R] T) → L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n
  j_str : j ≫ L.schemeKerStr n = Spec.map (CommRingCat.ofHom (algebraMap R H))
  j_open : IsOpenImmersion j
  j_closed : IsClosedImmersion j
  j_cov : ∀ x : ↥(L.schemeKer n), (L.schemeKerStr n).base x = IsLocalRing.closedPoint R → x ∈ Set.range j.base
  e_j : ∀ (T : Type) [CommRing T] [Algebra R T] (φ : WithConv (H →ₐ[R] T)),
    ((e T φ).val : SchemeHomOver _ f).1 =
      Spec.map (CommRingCat.ofHom φ.ofConv.toRingHom) ≫ j ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1
  e_inj : ∀ (T : Type) [CommRing T] [Algebra R T], Function.Injective (e T)
  e_surj : ∀ (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T], Function.Surjective (e T)
  e_mul : ∀ (T : Type) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
    ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val
  e_nat : ∀ (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    (g : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
    ((e T' (.toConv (g.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.1

theorem nonempty_levelDataF (hc : L.IsCommutative) (n : ℕ)
    [LocallyQuasiFinite (L.schemeKerStr n)] [QuasiCompact (L.schemeKerStr n)] [Flat (L.schemeKerStr n)] :
    Nonempty (LevelDataF L n) := by
  obtain ⟨H, _, _, hfin, hflat, hco, j, e, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_finitePart_schemeKer_of_henselianLocalRing L
      (fun t x y => hc t x y) n
  exact ⟨⟨H, hfin, hflat, hco, j, e, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩

noncomputable def levelDataF (hc : L.IsCommutative) (n : ℕ)
    [LocallyQuasiFinite (L.schemeKerStr n)] [QuasiCompact (L.schemeKerStr n)] [Flat (L.schemeKerStr n)] :
    LevelDataF L n :=
  Classical.choice (nonempty_levelDataF L hc n)

section Build

variable (hc : L.IsCommutative) (p h : ℕ)
  (hlqf : ∀ v : ℕ, LocallyQuasiFinite (L.schemeKerStr (p ^ v)))
  (hqc : ∀ v : ℕ, QuasiCompact (L.schemeKerStr (p ^ v)))
  (hflat : ∀ v : ℕ, Flat (L.schemeKerStr (p ^ v)))

noncomputable def D (v : ℕ) : LevelDataF L (p ^ v) := by
  haveI := hlqf v; haveI := hqc v; haveI := hflat v
  exact levelDataF L hc (p ^ v)

noncomputable scoped instance instCommRingD (v : ℕ) : CommRing (D L hc p hlqf hqc hflat v).H := (D L hc p hlqf hqc hflat v).cr
noncomputable scoped instance instHopfD (v : ℕ) : HopfAlgebra R (D L hc p hlqf hqc hflat v).H := (D L hc p hlqf hqc hflat v).ha
scoped instance instFiniteD (v : ℕ) : Module.Finite R (D L hc p hlqf hqc hflat v).H := (D L hc p hlqf hqc hflat v).fin
scoped instance instFlatD (v : ℕ) : Module.Flat R (D L hc p hlqf hqc hflat v).H := (D L hc p hlqf hqc hflat v).flat
scoped instance instFreeD (v : ℕ) : Module.Free R (D L hc p hlqf hqc hflat v).H := Module.free_of_flat_of_isLocalRing

noncomputable def eFin (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] :
    WithConv ((D L hc p hlqf hqc hflat v).H →ₐ[R] T) ≃
      L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) (p ^ v) :=
  Equiv.ofBijective ((D L hc p hlqf hqc hflat v).e T)
    ⟨(D L hc p hlqf hqc hflat v).e_inj T, (D L hc p hlqf hqc hflat v).e_surj T⟩

theorem eFin_apply (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T]
    (φ : WithConv ((D L hc p hlqf hqc hflat v).H →ₐ[R] T)) :
    eFin L hc p hlqf hqc hflat v T φ = (D L hc p hlqf hqc hflat v).e T φ := rfl

theorem eFin_mul (v : ℕ) : ∀ (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T]
    (φ ψ : WithConv ((D L hc p hlqf hqc hflat v).H →ₐ[R] T)),
    ((eFin L hc p hlqf hqc hflat v T (φ * ψ)).val : SchemeHomOver _ f) =
      L.mul _ (eFin L hc p hlqf hqc hflat v T φ).val (eFin L hc p hlqf hqc hflat v T ψ).val :=
  fun T _ _ _ φ ψ => (D L hc p hlqf hqc hflat v).e_mul T φ ψ

theorem eFin_nat (v : ℕ) : ∀ (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    [Module.Finite R T] [Module.Finite R T']
    (a : T →ₐ[R] T') (φ : WithConv ((D L hc p hlqf hqc hflat v).H →ₐ[R] T)),
    ((eFin L hc p hlqf hqc hflat v T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (eFin L hc p hlqf hqc hflat v T φ).val.1 :=
  fun T T' _ _ _ _ _ _ a φ => (D L hc p hlqf hqc hflat v).e_nat T T' a φ

theorem hmn (v : ℕ) : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)),
    L.torsionSubset t (p ^ v) ⊆ L.torsionSubset t (p ^ (v + 1)) :=
  fun t => YF.Law.torsionSubset_pow_succ L t p v

variable (hrank : ∀ (v : ℕ) (H : Type) [CommRing H] [Algebra R H] [Module.Finite R H] [Module.Free R H]
      (j : Spec (CommRingCat.of H) ⟶ L.schemeKer (p ^ v)),
      j ≫ L.schemeKerStr (p ^ v) = Spec.map (CommRingCat.ofHom (algebraMap R H)) →
      IsOpenImmersion j → IsClosedImmersion j →
      (∀ x : ↥(L.schemeKer (p ^ v)), (L.schemeKerStr (p ^ v)).base x = IsLocalRing.closedPoint R →
        x ∈ Set.range j.base) →
      Module.finrank R H = p ^ (v * h))

noncomputable def G : PDivisibleGroup R p h where
  level v := (D L hc p hlqf hqc hflat v).H
  instCommRing v := inferInstance
  instHopfAlgebra v := inferInstance
  instIsCocomm v := (D L hc p hlqf hqc hflat v).cocomm
  instModuleFinite v := inferInstance
  instModuleFree v := inferInstance
  transition v :=
    YF.Yoneda.transBialgHom L (p ^ v) (p ^ (v + 1)) (hmn L p v)
      (D L hc p hlqf hqc hflat v).H (D L hc p hlqf hqc hflat (v + 1)).H
      (eFin L hc p hlqf hqc hflat v) (eFin_mul L hc p hlqf hqc hflat v) (eFin_nat L hc p hlqf hqc hflat v)
      (eFin L hc p hlqf hqc hflat (v + 1)) (eFin_mul L hc p hlqf hqc hflat (v + 1)) (eFin_nat L hc p hlqf hqc hflat (v + 1))
  transition_surjective v :=
    YF.Yoneda.trans_surjective L (p ^ v) (p ^ (v + 1)) (hmn L p v)
      (D L hc p hlqf hqc hflat v).H (D L hc p hlqf hqc hflat (v + 1)).H
      (eFin L hc p hlqf hqc hflat v) (eFin_nat L hc p hlqf hqc hflat v)
      (eFin L hc p hlqf hqc hflat (v + 1)) (eFin_mul L hc p hlqf hqc hflat (v + 1)) (eFin_nat L hc p hlqf hqc hflat (v + 1))
  finrank_level v :=
    hrank v (D L hc p hlqf hqc hflat v).H (D L hc p hlqf hqc hflat v).j (D L hc p hlqf hqc hflat v).j_str
      (D L hc p hlqf hqc hflat v).j_open (D L hc p hlqf hqc hflat v).j_closed (D L hc p hlqf hqc hflat v).j_cov
  ker_transition v :=
    YF.Yoneda.ker_trans L (p ^ v) (p ^ (v + 1)) (hmn L p v)
      (D L hc p hlqf hqc hflat v).H (D L hc p hlqf hqc hflat (v + 1)).H
      (eFin L hc p hlqf hqc hflat v) (eFin_nat L hc p hlqf hqc hflat v)
      (eFin L hc p hlqf hqc hflat (v + 1)) (eFin_mul L hc p hlqf hqc hflat (v + 1)) (eFin_nat L hc p hlqf hqc hflat (v + 1))

end Build
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Hopf P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF"

end YF.Assembly
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Hopf P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Assembly"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Hopf P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Hopf P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Assembly"

namespace FPS13

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

section Bridge

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f)

theorem schemeHomOverComp_idPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x := by
  apply Subtype.ext
  simp [GoodReductionJacobian.schemeHomOverComp_coe]

theorem nsmul_val {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) :
    (L.nsmul t n x).1 = x.1 ≫ L.schemeNsmul n := by
  have h := L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  rw [schemeHomOverComp_idPoint] at h
  rw [← h]
  rfl

theorem one_val {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h := L.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t)
  rw [← h]
  rfl

theorem isTorsionPoint_iff_comp {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) :
    L.IsTorsionPoint t n x ↔
      x.1 ≫ L.schemeNsmul n = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  rw [RelativeGroupLaw.isTorsionPoint_def, ← nsmul_val, ← one_val]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem mem_torsionSubset_iff_comp {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) :
    x ∈ L.torsionSubset t n ↔
      x.1 ≫ L.schemeNsmul n = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 :=
  isTorsionPoint_iff_comp L t n x

theorem isClosedImmersion_one [IsSeparated f] :
    IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h2 := (L.one (𝟙 (Spec (CommRingCat.of R)))).2
  have : IsClosedImmersion ((L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) := by
    rw [h2]; infer_instance
  exact IsClosedImmersion.of_comp _ f

end Bridge
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Hopf P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Assembly"

section Levels

variable {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f) {p h : ℕ} (G : PDivisibleGroup R p h)
  (e : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T],
    G.Point T v ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) (p ^ v))
  (he_nat : ∀ (v : ℕ) (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T'] [Module.Finite R T] [Module.Finite R T']
    (a : T →ₐ[R] T') (x : G.Point T v),
    ((e v T' (G.pointMap a v x)).val : SchemeHomOver _ f).1 =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e v T x).val.1)
  (ι : ∀ v : ℕ, Spec (CommRingCat.of (G.level v)) ⟶ J)
  (hι : ∀ v : ℕ, ι v =
    (e v (G.level v) (PDivisibleGroup.Point.ofAlgHom (AlgHom.id R (G.level v)))).val.1)

include hι in

theorem ι_comp (v : ℕ) :
    ι v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (G.level v))) := by
  rw [hι]
  exact (e v (G.level v) _).val.2

include he_nat hι in

theorem val_eq (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] (x : G.Point T v) :
    (e v T x).val.1 =
      Spec.map (CommRingCat.ofHom (PDivisibleGroup.Point.toAlgHom x).toRingHom) ≫ ι v := by
  have hx : G.pointMap (PDivisibleGroup.Point.toAlgHom x) v
      (PDivisibleGroup.Point.ofAlgHom (AlgHom.id R (G.level v))) = x :=
    PDivisibleGroup.Point.ext fun _ => rfl
  have := he_nat v (G.level v) T (PDivisibleGroup.Point.toAlgHom x)
    (PDivisibleGroup.Point.ofAlgHom (AlgHom.id R (G.level v)))
  rw [hx] at this
  rw [hι]
  exact this

include hι in

theorem ι_comp_schemeNsmul (v : ℕ) :
    ι v ≫ L.schemeNsmul (p ^ v) =
      (ι v ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have hmem := (e v (G.level v) (PDivisibleGroup.Point.ofAlgHom (AlgHom.id R (G.level v)))).2
  rw [mem_torsionSubset_iff_comp] at hmem
  rw [ι_comp L G e ι hι v, hι]
  exact hmem

theorem kernel_fst_comp (n : ℕ) :
    pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f =
      pullback.snd (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h1 : pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f =
      pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫
        (L.schemeNsmul n ≫ f) := by
    rw [L.schemeNsmul_over]
  have h2 := (L.one (𝟙 (Spec (CommRingCat.of R)))).2
  rw [h1, ← Category.assoc, pullback.condition, Category.assoc, h2, Category.comp_id]

end Levels
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Hopf P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Assembly"

section Hom

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f)

theorem eq_one_of_mul_self {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {a : SchemeHomOver t f} (h : L.mul t a a = a) : a = L.one t := by
  have h' := congrArg (L.mul t (L.inv t a)) h
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at h'
  exact h'

variable (E : SchemeHomOver f f)
  (hE : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
    NeronModelInfra.schemeHomOverComp (L.mul s x y) E =
      L.mul s (NeronModelInfra.schemeHomOverComp x E) (NeronModelInfra.schemeHomOverComp y E))

include hE in
theorem comp_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    NeronModelInfra.schemeHomOverComp (L.one t) E = L.one t := by
  apply eq_one_of_mul_self L
  have := hE t (L.one t) (L.one t)
  rw [L.one_mul] at this
  exact this.symm

include hE in
theorem comp_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (L.nsmul t n x) E =
      L.nsmul t n (NeronModelInfra.schemeHomOverComp x E) := by
  induction n with
  | zero => exact comp_one L E hE t
  | succ n ih => rw [L.nsmul_succ, hE, ih, L.nsmul_succ]

include hE in
theorem isTorsionPoint_comp {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    {x : SchemeHomOver t f} (hx : L.IsTorsionPoint t n x) :
    L.IsTorsionPoint t n (NeronModelInfra.schemeHomOverComp x E) := by
  rw [RelativeGroupLaw.isTorsionPoint_def] at hx ⊢
  rw [← comp_nsmul L E hE, hx, comp_one L E hE]

end Hom
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Hopf P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Assembly"

section Endo

open PDivisibleGroup Bialgebra
p2m_open_scoped "TensorProduct Coalgebra.TensorProduct Bialgebra.TensorProduct"

variable {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f) {p h : ℕ} (G : PDivisibleGroup R p h)
  (e : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T],
    G.Point T v ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) (p ^ v))
  (he_mul : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] (x y : G.Point T v),
    ((e v T (x * y)).val : SchemeHomOver _ f) = L.mul _ (e v T x).val (e v T y).val)
  (he_nat : ∀ (v : ℕ) (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T'] [Module.Finite R T] [Module.Finite R T']
    (a : T →ₐ[R] T') (x : G.Point T v),
    ((e v T' (G.pointMap a v x)).val : SchemeHomOver _ f).1 =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e v T x).val.1)
  (he_incl : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] (x : G.Point T v),
    ((e (v + 1) T (G.pointIncl T v x)).val : SchemeHomOver _ f) = (e v T x).val)
  (ι : ∀ v : ℕ, Spec (CommRingCat.of (G.level v)) ⟶ J)
  (hι : ∀ v : ℕ, ι v =
    (e v (G.level v) (PDivisibleGroup.Point.ofAlgHom (AlgHom.id R (G.level v)))).val.1)
  (E : SchemeHomOver f f)
  (hE : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
    NeronModelInfra.schemeHomOverComp (L.mul s x y) E =
      L.mul s (NeronModelInfra.schemeHomOverComp x E) (NeronModelInfra.schemeHomOverComp y E))

noncomputable def act (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] (x : G.Point T v) :
    G.Point T v :=
  (e v T).symm ⟨NeronModelInfra.schemeHomOverComp (e v T x).val E,
    isTorsionPoint_comp L E hE _ _ (e v T x).2⟩

theorem e_act_val (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] (x : G.Point T v) :
    ((e v T (act L G e E hE v T x)).val : SchemeHomOver _ f) =
      NeronModelInfra.schemeHomOverComp (e v T x).val E := by
  unfold act
  rw [Equiv.apply_symm_apply]

theorem e_act_val_coe (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] (x : G.Point T v) :
    (e v T (act L G e E hE v T x)).val.1 = (e v T x).val.1 ≫ E.1 := by
  rw [e_act_val]
  rfl

noncomputable def φ₀ (v : ℕ) : G.level v →ₐ[R] G.level v :=
  Point.toAlgHom (act L G e E hE v (G.level v) (Point.ofAlgHom (AlgHom.id R (G.level v))))

include he_nat hι in
theorem specMap_φ₀_comp_ι (v : ℕ) :
    Spec.map (CommRingCat.ofHom (φ₀ L G e E hE v).toRingHom) ≫ ι v = ι v ≫ E.1 := by
  have h1 := val_eq L G e he_nat ι hι v (G.level v)
    (act L G e E hE v (G.level v) (Point.ofAlgHom (AlgHom.id R (G.level v))))
  rw [e_act_val_coe, ← hι] at h1
  exact h1.symm

include he_nat hι in

theorem act_eq (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] (x : G.Point T v) :
    act L G e E hE v T x = Point.ofAlgHom ((Point.toAlgHom x).comp (φ₀ L G e E hE v)) := by
  apply (e v T).injective
  apply Subtype.ext
  apply Subtype.ext
  rw [e_act_val_coe, val_eq L G e he_nat ι hι v T x,
    val_eq L G e he_nat ι hι v T (Point.ofAlgHom _), Point.toAlgHom_ofAlgHom]
  change _ = Spec.map (CommRingCat.ofHom (φ₀ L G e E hE v).toRingHom ≫
    CommRingCat.ofHom (Point.toAlgHom x).toRingHom) ≫ ι v
  rw [Spec.map_comp]
  simp only [Category.assoc]
  rw [specMap_φ₀_comp_ι L G e he_nat ι hι E hE v]

include he_mul in
theorem act_mul (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] (x y : G.Point T v) :
    act L G e E hE v T (x * y) = act L G e E hE v T x * act L G e E hE v T y := by
  apply (e v T).injective
  apply Subtype.ext
  rw [e_act_val, he_mul, hE, he_mul, e_act_val, e_act_val]

include he_mul in
theorem act_one (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] :
    act L G e E hE v T (1 : G.Point T v) = 1 := by
  have h1 := act_mul L G e he_mul E hE v T (1 : G.Point T v) 1
  rw [_root_.mul_one] at h1
  have h2 : act L G e E hE v T 1 * act L G e E hE v T 1 = act L G e E hE v T 1 * 1 := by
    rw [_root_.mul_one]; exact h1.symm
  exact mul_left_cancel h2

include he_mul he_nat hι in

theorem counit_comp_φ₀ (v : ℕ) :
    (counitAlgHom R (G.level v)).comp (φ₀ L G e E hE v) = counitAlgHom R (G.level v) := by
  have h1 := act_one L G e he_mul E hE v R
  rw [act_eq L G e he_nat ι hι E hE] at h1
  have h2 := congrArg Point.toAlgHom h1
  rw [Point.toAlgHom_ofAlgHom] at h2
  have h3 : Point.toAlgHom (1 : G.Point R v) = counitAlgHom R (G.level v) := by
    apply AlgHom.ext
    intro a
    rw [Point.one_apply, counitAlgHom_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [h3] at h2
  exact h2

include he_mul he_nat hι in

theorem map_comp_comul_φ₀ (v : ℕ) :
    (Algebra.TensorProduct.map (φ₀ L G e E hE v) (φ₀ L G e E hE v)).comp
        (comulAlgHom R (G.level v)) =
      (comulAlgHom R (G.level v)).comp (φ₀ L G e E hE v) := by
  have h1 := act_mul L G e he_mul E hE v (G.level v ⊗[R] G.level v)
    (Point.ofAlgHom
      (Algebra.TensorProduct.includeLeft : G.level v →ₐ[R] G.level v ⊗[R] G.level v))
    (Point.ofAlgHom
      (Algebra.TensorProduct.includeRight : G.level v →ₐ[R] G.level v ⊗[R] G.level v))
  rw [act_eq L G e he_nat ι hι E hE, act_eq L G e he_nat ι hι E hE,
    act_eq L G e he_nat ι hι E hE] at h1
  have h2 := congrArg Point.toAlgHom h1
  rw [Point.toAlgHom_ofAlgHom] at h2
  apply AlgHom.ext
  intro a
  have h3 := congrArg (fun F : G.level v →ₐ[R] G.level v ⊗[R] G.level v => F a) h2
  simp only [AlgHom.comp_apply, Point.mul_apply, Point.toAlgHom_ofAlgHom] at h3

  have hl : ∀ hc, Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeLeft : G.level v →ₐ[R] G.level v ⊗[R] G.level v)
      (Algebra.TensorProduct.includeRight : G.level v →ₐ[R] G.level v ⊗[R] G.level v) hc =
        AlgHom.id R (G.level v ⊗[R] G.level v) :=
    fun hc => Algebra.TensorProduct.ext' fun a b => by simp
  have hr : ∀ hc, Algebra.TensorProduct.lift
      ((Algebra.TensorProduct.includeLeft : G.level v →ₐ[R] G.level v ⊗[R] G.level v).comp
        (φ₀ L G e E hE v))
      ((Algebra.TensorProduct.includeRight : G.level v →ₐ[R] G.level v ⊗[R] G.level v).comp
        (φ₀ L G e E hE v)) hc =
        Algebra.TensorProduct.map (φ₀ L G e E hE v) (φ₀ L G e E hE v) :=
    fun hc => Algebra.TensorProduct.ext' fun a b => by simp [Algebra.TensorProduct.map_tmul]
  rw [hl, hr] at h3
  rw [AlgHom.comp_apply, AlgHom.comp_apply, comulAlgHom_apply, comulAlgHom_apply]
  exact h3.symm

noncomputable def φ (v : ℕ) : G.level v →ₐc[R] G.level v :=
  BialgHom.ofAlgHom (φ₀ L G e E hE v) (counit_comp_φ₀ L G e he_mul he_nat ι hι E hE v)
    (map_comp_comul_φ₀ L G e he_mul he_nat ι hι E hE v)

theorem φ_toAlgHom (v : ℕ) :
    (φ L G e he_mul he_nat ι hι E hE v : G.level v →ₐ[R] G.level v) = φ₀ L G e E hE v := by
  apply AlgHom.ext
  intro a
  rfl

theorem φ_toRingHom (v : ℕ) :
    (φ L G e he_mul he_nat ι hι E hE v : G.level v →+* G.level v) = (φ₀ L G e E hE v).toRingHom := by
  apply RingHom.ext
  intro a
  rfl

include he_incl in

theorem act_pointIncl (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] (x : G.Point T v) :
    act L G e E hE (v + 1) T (G.pointIncl T v x) = G.pointIncl T v (act L G e E hE v T x) := by
  apply (e (v + 1) T).injective
  apply Subtype.ext
  rw [e_act_val, he_incl, he_incl, e_act_val]

include he_incl in

theorem transition_comp_φ (v : ℕ) :
    (G.transition v).comp (φ L G e he_mul he_nat ι hι E hE (v + 1)) =
      (φ L G e he_mul he_nat ι hι E hE v).comp (G.transition v) := by
  apply BialgHom.coe_algHom_injective
  rw [BialgHom.comp_toAlgHom, BialgHom.comp_toAlgHom, φ_toAlgHom, φ_toAlgHom]
  have h1 := act_pointIncl L G e he_incl E hE v (G.level v)
    (Point.ofAlgHom (AlgHom.id R (G.level v)))
  rw [act_eq L G e he_nat ι hι E hE, act_eq L G e he_nat ι hι E hE] at h1
  have h2 := congrArg Point.toAlgHom h1
  rw [Point.toAlgHom_ofAlgHom, toAlgHom_pointIncl, toAlgHom_pointIncl,
    Point.toAlgHom_ofAlgHom, Point.toAlgHom_ofAlgHom, AlgHom.id_comp] at h2
  exact h2

include L e he_mul he_nat he_incl hι hE in

theorem exists_bialgHom_restrict :
    ∃ φ : ∀ v : ℕ, G.level v →ₐc[R] G.level v,
      (∀ v : ℕ, (G.transition v).comp (φ (v + 1)) = (φ v).comp (G.transition v)) ∧
      ∀ v : ℕ, Spec.map (CommRingCat.ofHom (φ v : G.level v →+* G.level v)) ≫ ι v = ι v ≫ E.1 :=
  ⟨φ L G e he_mul he_nat ι hι E hE, transition_comp_φ L G e he_mul he_nat he_incl ι hι E hE,
    fun v => by
      rw [φ_toRingHom]
      exact specMap_φ₀_comp_ι L G e he_nat ι hι E hE v⟩

end Endo
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Hopf P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Assembly"

end FPS13
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Hopf P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Assembly"

noncomputable section

namespace YF
namespace Assembly

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

section Final

variable {R : Type} [CommRing R] [HenselianLocalRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
  [IsSeparated f] [LocallyOfFiniteType f] (L : RelativeGroupLaw R f)
  (hc : L.IsCommutative) (p h : ℕ)
  (hlqf : ∀ v : ℕ, LocallyQuasiFinite (L.schemeKerStr (p ^ v)))
  (hqc : ∀ v : ℕ, QuasiCompact (L.schemeKerStr (p ^ v)))
  (hflat : ∀ v : ℕ, Flat (L.schemeKerStr (p ^ v)))
  (hrank : ∀ (v : ℕ) (H : Type) [CommRing H] [Algebra R H] [Module.Finite R H] [Module.Free R H]
      (j : Spec (CommRingCat.of H) ⟶ L.schemeKer (p ^ v)),
      j ≫ L.schemeKerStr (p ^ v) = Spec.map (CommRingCat.ofHom (algebraMap R H)) →
      IsOpenImmersion j → IsClosedImmersion j →
      (∀ x : ↥(L.schemeKer (p ^ v)), (L.schemeKerStr (p ^ v)).base x = IsLocalRing.closedPoint R →
        x ∈ Set.range j.base) →
      Module.finrank R H = p ^ (v * h))

def ιv (v : ℕ) : Spec (CommRingCat.of ((G L hc p h hlqf hqc hflat hrank).level v)) ⟶ X :=
  (D L hc p hlqf hqc hflat v).j ≫ pullback.fst (L.schemeNsmul (p ^ v)) (L.one (𝟙 (Spec (CommRingCat.of R)))).1

def eP (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T] :
    (G L hc p h hlqf hqc hflat hrank).Point T v ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) (p ^ v) :=
  eFin L hc p hlqf hqc hflat v T

theorem eP_val_coe (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T]
    (x : (G L hc p h hlqf hqc hflat hrank).Point T v) :
    (eP L hc p h hlqf hqc hflat hrank v T x).val.1 =
      Spec.map (CommRingCat.ofHom (PDivisibleGroup.Point.toAlgHom x).toRingHom) ≫ ιv L hc p h hlqf hqc hflat hrank v :=
  (D L hc p hlqf hqc hflat v).e_j T x

theorem hι (v : ℕ) : ιv L hc p h hlqf hqc hflat hrank v =
    (eP L hc p h hlqf hqc hflat hrank v _ (PDivisibleGroup.Point.ofAlgHom (AlgHom.id R _))).val.1 := by
  rw [eP_val_coe, PDivisibleGroup.Point.toAlgHom_ofAlgHom]
  change _ = Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ _
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

theorem heP_mul (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T]
    (x y : (G L hc p h hlqf hqc hflat hrank).Point T v) :
    ((eP L hc p h hlqf hqc hflat hrank v T (x * y)).val : SchemeHomOver _ f) =
      L.mul _ (eP L hc p h hlqf hqc hflat hrank v T x).val (eP L hc p h hlqf hqc hflat hrank v T y).val :=
  (D L hc p hlqf hqc hflat v).e_mul T x y

theorem heP_nat (v : ℕ) (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    [Module.Finite R T] [Module.Finite R T']
    (a : T →ₐ[R] T') (x : (G L hc p h hlqf hqc hflat hrank).Point T v) :
    ((eP L hc p h hlqf hqc hflat hrank v T' ((G L hc p h hlqf hqc hflat hrank).pointMap a v x)).val : SchemeHomOver _ f).1 =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (eP L hc p h hlqf hqc hflat hrank v T x).val.1 :=
  (D L hc p hlqf hqc hflat v).e_nat T T' a x

theorem heP_incl (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T]
    (x : (G L hc p h hlqf hqc hflat hrank).Point T v) :
    ((eP L hc p h hlqf hqc hflat hrank (v + 1) T ((G L hc p h hlqf hqc hflat hrank).pointIncl T v x)).val : SchemeHomOver _ f) =
      (eP L hc p h hlqf hqc hflat hrank v T x).val := by
  apply Subtype.ext
  exact YF.Yoneda.eJ_comp_trans L (p ^ v) (p ^ (v + 1)) (hmn L p v)
      (D L hc p hlqf hqc hflat v).H (D L hc p hlqf hqc hflat (v + 1)).H
      (eFin L hc p hlqf hqc hflat v) (eFin_nat L hc p hlqf hqc hflat v)
      (eFin L hc p hlqf hqc hflat (v + 1)) (eFin_nat L hc p hlqf hqc hflat (v + 1)) T x

end Final
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Hopf P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Assembly"

end YF.Assembly
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Hopf P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Assembly"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Hopf P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Assembly"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Hopf P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing.YF.Assembly"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian YF.Assembly in
theorem solution
    {R : Type} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} [IsSeparated f] [LocallyOfFiniteType f]
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (p h : ℕ)
    (hlqf : ∀ v : ℕ, LocallyQuasiFinite (L.schemeKerStr (p ^ v)))
    (hqc : ∀ v : ℕ, QuasiCompact (L.schemeKerStr (p ^ v)))
    (hflat : ∀ v : ℕ, Flat (L.schemeKerStr (p ^ v)))

    (hrank : ∀ (v : ℕ) (H : Type) [CommRing H] [Algebra R H] [Module.Finite R H] [Module.Free R H]
      (j : Spec (CommRingCat.of H) ⟶ L.schemeKer (p ^ v)),
      j ≫ L.schemeKerStr (p ^ v) = Spec.map (CommRingCat.ofHom (algebraMap R H)) →
      IsOpenImmersion j → IsClosedImmersion j →
      (∀ x : ↥(L.schemeKer (p ^ v)), (L.schemeKerStr (p ^ v)).base x = IsLocalRing.closedPoint R →
        x ∈ Set.range j.base) →
      Module.finrank R H = p ^ (v * h)) :
    ∃ (G : PDivisibleGroup R p h) (ι : ∀ v : ℕ, Spec (CommRingCat.of (G.level v)) ⟶ X),

      (∀ v : ℕ, ι v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (G.level v)))) ∧

      (∀ v : ℕ, IsClosedImmersion (ι v)) ∧

      (∀ v : ℕ, ι v ≫ L.schemeNsmul (p ^ v) = (ι v ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ∧

      (∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R B] (x y : G.Point B v)
        (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v) ≫ f =
          Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v) ≫ f =
          Spec.map (CommRingCat.ofHom (algebraMap R B))),
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v =
          (L.mul (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟨_, hx⟩ ⟨_, hy⟩).1) ∧

      (∀ v : ℕ, Spec.map (CommRingCat.ofHom (G.transition v : G.level (v + 1) →+* G.level v)) ≫ ι (v + 1) = ι v) ∧

      (∀ (E : SchemeHomOver f f),
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
          NeronModelInfra.schemeHomOverComp (L.mul s x y) E =
            L.mul s (NeronModelInfra.schemeHomOverComp x E) (NeronModelInfra.schemeHomOverComp y E)) →
        ∃ φ : ∀ v : ℕ, G.level v →ₐc[R] G.level v,
          (∀ v : ℕ, (G.transition v).comp (φ (v + 1)) = (φ v).comp (G.transition v)) ∧
          ∀ v : ℕ, Spec.map (CommRingCat.ofHom (φ v : G.level v →+* G.level v)) ≫ ι v = ι v ≫ E.1) ∧

      (∀ (v : ℕ)
        (h3 : ι v ≫ L.schemeNsmul (p ^ v) = (ι v ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1),
        IsOpenImmersion (pullback.lift (f := L.schemeNsmul (p ^ v)) (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
            (ι v) (ι v ≫ f) h3) ∧
        IsClosedImmersion (pullback.lift (f := L.schemeNsmul (p ^ v)) (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
            (ι v) (ι v ≫ f) h3) ∧
        ∀ x : ↥(L.schemeKer (p ^ v)), (L.schemeKerStr (p ^ v)).base x = IsLocalRing.closedPoint R →
          x ∈ Set.range (pullback.lift (f := L.schemeNsmul (p ^ v)) (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1)
            (ι v) (ι v ≫ f) h3).base) ∧

      (∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T] [Module.Finite R T]
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) f),
        L.IsTorsionPoint _ (p ^ v) x →
        ∃ φ : G.level v →ₐ[R] T, Spec.map (CommRingCat.ofHom (φ : G.level v →+* T)) ≫ ι v = x.1) := by
  classical
  let G0 := YF.Assembly.G L hc p h hlqf hqc hflat hrank
  let ι0 : ∀ v : ℕ, Spec (CommRingCat.of (G0.level v)) ⟶ X := fun v => YF.Assembly.ιv L hc p h hlqf hqc hflat hrank v
  have hkf : ∀ n : ℕ, pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f =
      pullback.snd (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := FPS13.kernel_fst_comp L
  have hS1 : ∀ v : ℕ, ι0 v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (G0.level v))) := by
    intro v
    change ((D L hc p hlqf hqc hflat v).j ≫ _) ≫ f = _
    rw [Category.assoc, hkf]
    exact (D L hc p hlqf hqc hflat v).j_str
  have hjs : ∀ v : ℕ, (D L hc p hlqf hqc hflat v).j ≫ pullback.snd (L.schemeNsmul (p ^ v)) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 =
      ι0 v ≫ f := fun v => ((D L hc p hlqf hqc hflat v).j_str).trans (hS1 v).symm
  have hS3 : ∀ v : ℕ, ι0 v ≫ L.schemeNsmul (p ^ v) = (ι0 v ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
    intro v
    rw [← hjs v]
    change ((D L hc p hlqf hqc hflat v).j ≫ _) ≫ _ = _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    rfl
  have hlift : ∀ (v : ℕ) (h3 : ι0 v ≫ L.schemeNsmul (p ^ v) = (ι0 v ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1),
      pullback.lift (f := L.schemeNsmul (p ^ v)) (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1) (ι0 v) (ι0 v ≫ f) h3 =
        (D L hc p hlqf hqc hflat v).j := by
    intro v h3
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      rfl
    · rw [pullback.lift_snd]
      exact (hjs v).symm
  refine ⟨G0, ι0, hS1, ?_, hS3, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro v
    haveI := FPS13.isClosedImmersion_one L
    haveI := (D L hc p hlqf hqc hflat v).j_closed
    change IsClosedImmersion ((D L hc p hlqf hqc hflat v).j ≫ _)
    infer_instance
  ·
    intro v B _ _ x y hx hy
    have ex : ((D L hc p hlqf hqc hflat v).e B x).val =
        (⟨_, hx⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R B))) f) :=
      Subtype.ext ((D L hc p hlqf hqc hflat v).e_j B x)
    have ey : ((D L hc p hlqf hqc hflat v).e B y).val =
        (⟨_, hy⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R B))) f) :=
      Subtype.ext ((D L hc p hlqf hqc hflat v).e_j B y)
    have h1 := (D L hc p hlqf hqc hflat v).e_mul B x y
    rw [ex, ey] at h1
    have h2 := (D L hc p hlqf hqc hflat v).e_j B (x * y)
    exact h2.symm.trans (congrArg Subtype.val h1)
  ·
    intro v
    have h1 := congrArg (fun z : SchemeHomOver _ f => z.1)
      (YF.Assembly.heP_incl L hc p h hlqf hqc hflat hrank v (G0.level v) (PDivisibleGroup.Point.ofAlgHom (AlgHom.id R _)))
    rw [YF.Assembly.eP_val_coe, YF.Assembly.eP_val_coe, PDivisibleGroup.Point.toAlgHom_ofAlgHom,
      PDivisibleGroup.toAlgHom_pointIncl, PDivisibleGroup.Point.toAlgHom_ofAlgHom, AlgHom.id_comp] at h1

    have h2 : Spec.map (CommRingCat.ofHom (AlgHom.id R (G0.level v)).toRingHom) ≫ ι0 v = ι0 v := by
      change Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ _ = _
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    rw [h2] at h1
    exact h1
  ·
    intro E hE
    exact FPS13.exists_bialgHom_restrict L G0 (YF.Assembly.eP L hc p h hlqf hqc hflat hrank)
      (YF.Assembly.heP_mul L hc p h hlqf hqc hflat hrank) (YF.Assembly.heP_nat L hc p h hlqf hqc hflat hrank)
      (YF.Assembly.heP_incl L hc p h hlqf hqc hflat hrank) ι0 (YF.Assembly.hι L hc p h hlqf hqc hflat hrank) E hE
  ·
    intro v h3
    rw [hlift v h3]
    exact ⟨(D L hc p hlqf hqc hflat v).j_open, (D L hc p hlqf hqc hflat v).j_closed, (D L hc p hlqf hqc hflat v).j_cov⟩
  ·
    intro v T _ _ _ x hx
    obtain ⟨φ, hφ⟩ := (D L hc p hlqf hqc hflat v).e_surj T ⟨x, hx⟩
    refine ⟨φ.ofConv, ?_⟩
    have h1 := (D L hc p hlqf hqc hflat v).e_j T φ
    rw [hφ] at h1
    exact h1.symm

end S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_closedImmersion_finitePart_of_henselianLocalRing (solution)
