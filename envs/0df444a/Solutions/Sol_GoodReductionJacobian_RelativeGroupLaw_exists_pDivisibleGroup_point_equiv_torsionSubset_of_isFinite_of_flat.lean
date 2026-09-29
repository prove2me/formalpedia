-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ba9f0477-4c1d-565c-bd03-d2f54f0ecefc

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_torsion_of_isFinite_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

open Coalgebra Bialgebra WithConv

namespace YEng

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
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat.YEng.Hopf"

section Rank

theorem rank {R : Type} [CommRing R] [IsLocalRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra R Ω]
    {S : Type*} (e : WithConv (H →ₐ[R] Ω) ≃ S) (N : ℕ) (hS : Nat.card S = N) :
    Module.Free R H ∧ Module.finrank R H = N := by
  haveI : Module.Free R H := Module.free_of_flat_of_isLocalRing
  refine ⟨this, ?_⟩
  rw [← HopfAlgebra.natCard_algHom_eq_finrank_of_charZero R H Ω, ← hS]
  exact Nat.card_congr ((WithConv.equiv (H →ₐ[R] Ω)).symm.trans e)

end Rank
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat.YEng.Hopf"

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
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat.YEng.Hopf"

namespace Yoneda

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
p2m_open_scoped "TensorProduct Coalgebra.TensorProduct Bialgebra.TensorProduct"

variable {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f) (m n : ℕ)
  (hmn : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)), L.torsionSubset t m ⊆ L.torsionSubset t n)
  (HB : Type) [CommRing HB] [HopfAlgebra R HB] (HJ : Type) [CommRing HJ] [HopfAlgebra R HJ]
  (eB : ∀ (T : Type) [CommRing T] [Algebra R T],
    WithConv (HB →ₐ[R] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) m)
  (eB_mul : ∀ (T : Type) [CommRing T] [Algebra R T] (φ ψ : WithConv (HB →ₐ[R] T)),
    ((eB T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (eB T φ).val (eB T ψ).val)
  (eB_nat : ∀ (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    (a : T →ₐ[R] T') (φ : WithConv (HB →ₐ[R] T)),
    ((eB T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (eB T φ).val.1)
  (eJ : ∀ (T : Type) [CommRing T] [Algebra R T],
    WithConv (HJ →ₐ[R] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n)
  (eJ_mul : ∀ (T : Type) [CommRing T] [Algebra R T] (φ ψ : WithConv (HJ →ₐ[R] T)),
    ((eJ T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (eJ T φ).val (eJ T ψ).val)
  (eJ_nat : ∀ (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    (a : T →ₐ[R] T') (φ : WithConv (HJ →ₐ[R] T)),
    ((eJ T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (eJ T φ).val.1)

noncomputable def univPoint :
    L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R HB))) n :=
  ⟨(eB HB (toConv (AlgHom.id R HB))).val, hmn _ (eB HB (toConv (AlgHom.id R HB))).2⟩

private noncomputable def _root_.YEng.Yoneda.trans : HJ →ₐ[R] HB :=
  ((eJ HB).symm (univPoint L m n hmn HB eB)).ofConv

p2m_export "YEng.Yoneda" "trans"
include eB_nat eJ_nat in

theorem eJ_comp_trans (T : Type) [CommRing T] [Algebra R T] (x : WithConv (HB →ₐ[R] T)) :
    ((eJ T (toConv (x.ofConv.comp (trans L m n hmn HB HJ eB eJ)))).val : SchemeHomOver _ f).1 =
      ((eB T x).val : SchemeHomOver _ f).1 := by
  have h1 := eJ_nat HB T x.ofConv ((eJ HB).symm (univPoint L m n hmn HB eB))
  rw [Equiv.apply_symm_apply] at h1
  have h2 := eB_nat HB T x.ofConv (toConv (AlgHom.id R HB))
  have hx : x.ofConv.comp (toConv (AlgHom.id R HB)).ofConv = x.ofConv := AlgHom.comp_id _
  rw [hx, toConv_ofConv] at h2
  exact h1.trans h2.symm

include eB_nat eJ_nat in
theorem eJ_comp_trans_val (T : Type) [CommRing T] [Algebra R T] (x : WithConv (HB →ₐ[R] T)) :
    ((eJ T (toConv (x.ofConv.comp (trans L m n hmn HB HJ eB eJ)))).val : SchemeHomOver _ f) =
      ⟨((eB T x).val : SchemeHomOver _ f).1, ((eB T x).val : SchemeHomOver _ f).2⟩ :=
  Subtype.ext (eJ_comp_trans L m n hmn HB HJ eB eB_nat eJ eJ_nat T x)

include eB_mul eB_nat eJ_mul eJ_nat in

theorem toConv_mul_comp_trans (T : Type) [CommRing T] [Algebra R T] (x y : WithConv (HB →ₐ[R] T)) :
    toConv ((x * y).ofConv.comp (trans L m n hmn HB HJ eB eJ)) =
      toConv (x.ofConv.comp (trans L m n hmn HB HJ eB eJ)) *
        toConv (y.ofConv.comp (trans L m n hmn HB HJ eB eJ)) := by
  apply (eJ T).injective
  apply Subtype.ext
  rw [eJ_mul, eJ_comp_trans_val L m n hmn HB HJ eB eB_nat eJ eJ_nat T x,
    eJ_comp_trans_val L m n hmn HB HJ eB eB_nat eJ eJ_nat T y,
    eJ_comp_trans_val L m n hmn HB HJ eB eB_nat eJ eJ_nat T (x * y), eB_mul]

include eB_mul eB_nat eJ_mul eJ_nat in
theorem toConv_one_comp_trans (T : Type) [CommRing T] [Algebra R T] :
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
theorem eJ_one (T : Type) [CommRing T] [Algebra R T] :
    ((eJ T 1).val : SchemeHomOver _ f) = L.one _ := by
  letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R T)))
  have h := eJ_mul T 1 1
  rw [one_mul] at h
  have h' : (eJ T 1).val * (eJ T 1).val = (eJ T 1).val := h.symm
  exact mul_eq_left.1 h'

include eJ_mul in
theorem eJ_pow (T : Type) [CommRing T] [Algebra R T] (g : WithConv (HJ →ₐ[R] T)) (k : ℕ) :
    ((eJ T (g ^ k)).val : SchemeHomOver _ f) = L.nsmul _ k (eJ T g).val := by
  induction k with
  | zero => rw [pow_zero, RelativeGroupLaw.nsmul_zero, eJ_one L n HJ eJ eJ_mul]
  | succ k ih => rw [pow_succ, eJ_mul, ih, RelativeGroupLaw.nsmul_succ]

include eJ_mul in

theorem pow_eq_one_iff_mem_torsionSubset (T : Type) [CommRing T] [Algebra R T]
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

noncomputable def inv : HB →ₐ[R] (HJ ⧸ PDivisibleGroup.Hopf.torsionIdeal R HJ m) :=
  ((eB _).symm (quotUnivPoint L m n HJ eJ eJ_mul)).ofConv

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
theorem eB_injective_val (T : Type) [CommRing T] [Algebra R T] {x y : WithConv (HB →ₐ[R] T)}
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
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat.YEng.Hopf"

end YEng
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat.YEng.Hopf P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat.YEng"

namespace YEng
namespace Assembly

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian WithConv

variable {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f)

structure LevelData (n : ℕ) : Type 1 where

  H : Type
  [cr : CommRing H]
  [ha : HopfAlgebra R H]
  fin : Module.Finite R H
  flat : Module.Flat R H
  cocomm : Coalgebra.IsCocomm R H

  e : ∀ (T : Type) [CommRing T] [Algebra R T],
    WithConv (H →ₐ[R] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) n
  e_mul : ∀ (T : Type) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
    ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val
  e_nat : ∀ (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    (a : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
    ((e T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e T φ).val.1

attribute [scoped instance] LevelData.cr LevelData.ha

noncomputable def levelData
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (hfin : IsFinite (L.schemeNsmul n)) (hflat : Flat (L.schemeNsmul n)) : LevelData L n :=
  let ex := GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_torsion_of_isFinite_of_flat
    L hcomm n hfin hflat
  @LevelData.mk R _ J f L n ex.choose ex.choose_spec.choose ex.choose_spec.choose_spec.choose
    ex.choose_spec.choose_spec.choose_spec.1 ex.choose_spec.choose_spec.choose_spec.2.1
    ex.choose_spec.choose_spec.choose_spec.2.2.1
    ex.choose_spec.choose_spec.choose_spec.2.2.2.choose
    ex.choose_spec.choose_spec.choose_spec.2.2.2.choose_spec.1
    ex.choose_spec.choose_spec.choose_spec.2.2.2.choose_spec.2

section Build

variable
  (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
    L.mul t x y = L.mul t y x)
  (p h : ℕ)
  (hfin : ∀ v : ℕ, IsFinite (L.schemeNsmul (p ^ v)))
  (hflat : ∀ v : ℕ, Flat (L.schemeNsmul (p ^ v)))
  (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra R Ω]
  (hcard : ∀ v : ℕ,
    Nat.card (L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) (p ^ v)) = p ^ (v * h))

noncomputable def D (v : ℕ) : LevelData L (p ^ v) := levelData L hcomm (p ^ v) (hfin v) (hflat v)

include hcard in
theorem free_and_finrank [IsLocalRing R] (v : ℕ) :
    Module.Free R (D L hcomm p hfin hflat v).H ∧
      Module.finrank R (D L hcomm p hfin hflat v).H = p ^ (v * h) := by
  haveI := (D L hcomm p hfin hflat v).fin
  haveI := (D L hcomm p hfin hflat v).flat
  exact YEng.rank (D L hcomm p hfin hflat v).H Ω ((D L hcomm p hfin hflat v).e Ω) _ (hcard v)

theorem hmn (v : ℕ) : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)),
    L.torsionSubset t (p ^ v) ⊆ L.torsionSubset t (p ^ (v + 1)) :=
  fun t => YEng.Law.torsionSubset_pow_succ L t p v

noncomputable def G [IsLocalRing R] : PDivisibleGroup R p h where
  level v := (D L hcomm p hfin hflat v).H
  instCommRing v := (D L hcomm p hfin hflat v).cr
  instHopfAlgebra v := (D L hcomm p hfin hflat v).ha
  instIsCocomm v := (D L hcomm p hfin hflat v).cocomm
  instModuleFinite v := (D L hcomm p hfin hflat v).fin
  instModuleFree v := (free_and_finrank L hcomm p h hfin hflat Ω hcard v).1
  transition v :=
    YEng.Yoneda.transBialgHom L (p ^ v) (p ^ (v + 1)) (hmn L p v)
      (D L hcomm p hfin hflat v).H (D L hcomm p hfin hflat (v + 1)).H
      (D L hcomm p hfin hflat v).e (D L hcomm p hfin hflat v).e_mul (D L hcomm p hfin hflat v).e_nat
      (D L hcomm p hfin hflat (v + 1)).e (D L hcomm p hfin hflat (v + 1)).e_mul
      (D L hcomm p hfin hflat (v + 1)).e_nat
  transition_surjective v :=
    YEng.Yoneda.trans_surjective L (p ^ v) (p ^ (v + 1)) (hmn L p v)
      (D L hcomm p hfin hflat v).H (D L hcomm p hfin hflat (v + 1)).H
      (D L hcomm p hfin hflat v).e (D L hcomm p hfin hflat v).e_nat
      (D L hcomm p hfin hflat (v + 1)).e (D L hcomm p hfin hflat (v + 1)).e_mul
      (D L hcomm p hfin hflat (v + 1)).e_nat
  finrank_level v := (free_and_finrank L hcomm p h hfin hflat Ω hcard v).2
  ker_transition v :=
    YEng.Yoneda.ker_trans L (p ^ v) (p ^ (v + 1)) (hmn L p v)
      (D L hcomm p hfin hflat v).H (D L hcomm p hfin hflat (v + 1)).H
      (D L hcomm p hfin hflat v).e (D L hcomm p hfin hflat v).e_nat
      (D L hcomm p hfin hflat (v + 1)).e (D L hcomm p hfin hflat (v + 1)).e_mul
      (D L hcomm p hfin hflat (v + 1)).e_nat

end Build
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat.YEng.Hopf P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat.YEng"

end YEng.Assembly
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat.YEng.Hopf P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat.YEng P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat.YEng.Assembly"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat.YEng.Hopf P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat.YEng"

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian in
theorem solution
    {R : Type} [CommRing R] [IsLocalRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (p h : ℕ)
    (hfin : ∀ v : ℕ, IsFinite (L.schemeNsmul (p ^ v)))
    (hflat : ∀ v : ℕ, Flat (L.schemeNsmul (p ^ v)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra R Ω]
    (hcard : ∀ v : ℕ,
      Nat.card (L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) (p ^ v)) =
        p ^ (v * h)) :
    ∃ (G : PDivisibleGroup R p h)
      (e : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T],
        G.Point T v ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) (p ^ v)),
      (∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T] (x y : G.Point T v),
        ((e v T (x * y)).val : SchemeHomOver _ f) = L.mul _ (e v T x).val (e v T y).val) ∧
      (∀ (v : ℕ) (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
        (a : T →ₐ[R] T') (x : G.Point T v),
        ((e v T' (G.pointMap a v x)).val : SchemeHomOver _ f).1 =
          Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e v T x).val.1) ∧
      (∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T] (x : G.Point T v),
        ((e (v + 1) T (G.pointIncl T v x)).val : SchemeHomOver _ f) = (e v T x).val) := by
  refine ⟨YEng.Assembly.G L hcomm p h hfin hflat Ω hcard,
    fun v T _ _ => (YEng.Assembly.D L hcomm p hfin hflat v).e T,
    fun v T _ _ x y => (YEng.Assembly.D L hcomm p hfin hflat v).e_mul T x y,
    fun v T T' _ _ _ _ a x => (YEng.Assembly.D L hcomm p hfin hflat v).e_nat T T' a x,
    fun v T _ _ x => ?_⟩
  exact Subtype.ext (YEng.Yoneda.eJ_comp_trans L (p ^ v) (p ^ (v + 1)) (YEng.Assembly.hmn L p v)
    (YEng.Assembly.D L hcomm p hfin hflat v).H (YEng.Assembly.D L hcomm p hfin hflat (v + 1)).H
    (YEng.Assembly.D L hcomm p hfin hflat v).e (YEng.Assembly.D L hcomm p hfin hflat v).e_nat
    (YEng.Assembly.D L hcomm p hfin hflat (v + 1)).e (YEng.Assembly.D L hcomm p hfin hflat (v + 1)).e_nat
    T x)

end S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pDivisibleGroup_point_equiv_torsionSubset_of_isFinite_of_flat (solution)
