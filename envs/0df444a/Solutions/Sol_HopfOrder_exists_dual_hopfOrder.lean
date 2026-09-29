-- Prove2me | solution 1 for HopfOrder.exists_dual_hopfOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8ef31b4c-9645-558a-b7b3-19a09b2b212e

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_HopfOrderData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfOrder_exists_dual_hopfOrder

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

namespace S17Dual

section DualOrder

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
variable {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
variable [Module.Finite K A] [Coalgebra.IsCocomm K A]
variable [Algebra R (CartierDual K A)] [IsScalarTower R K (CartierDual K A)]

theorem add_apply' (φ ψ : CartierDual K A) (a : A) : (φ + ψ) a = φ a + ψ a := rfl
theorem zero_apply' (a : A) : (0 : CartierDual K A) a = 0 := rfl
theorem smulK_apply' (k : K) (φ : CartierDual K A) (a : A) : (k • φ) a = k * φ a := rfl

theorem smulR_eq (r : R) (φ : CartierDual K A) : r • φ = algebraMap R K r • φ :=
  (algebraMap_smul K r φ).symm

theorem dualDistrib_tensorSqHom_mem (S : Subalgebra R A) (φ ψ : CartierDual K A)
    (hφ : ∀ b ∈ S, φ b ∈ (algebraMap R K).range) (hψ : ∀ b ∈ S, ψ b ∈ (algebraMap R K).range)
    (z : ↥S ⊗[R] ↥S) :
    TensorProduct.dualDistrib K A A (CartierDual.toDual K A φ ⊗ₜ[K] CartierDual.toDual K A ψ)
      (HopfOrder.tensorSqHom (K := K) S z) ∈ (algebraMap R K).range := by
  induction z with
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | tmul s t =>
      rw [HopfOrder.tensorSqHom_tmul, TensorProduct.dualDistrib_apply, CartierDual.toDual_apply,
        CartierDual.toDual_apply]
      exact mul_mem (hφ s s.2) (hψ t t.2)
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

def dualOrder (S : Subalgebra R A)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    Subalgebra R (CartierDual K A) where
  carrier := {φ | ∀ b ∈ S, φ b ∈ (algebraMap R K).range}
  mul_mem' {φ ψ} hφ hψ := by
    intro b hb
    rw [CartierDual.mul_apply]
    obtain ⟨z, hz⟩ := (AlgHom.mem_range _).mp (hcomul b hb)
    rw [← hz]
    exact dualDistrib_tensorSqHom_mem S φ ψ hφ hψ z
  one_mem' := by
    intro b hb
    rw [CartierDual.one_apply]
    exact hcounit b hb
  add_mem' {φ ψ} hφ hψ := by
    intro b hb
    rw [add_apply']
    exact add_mem (hφ b hb) (hψ b hb)
  zero_mem' := by
    intro b _
    rw [zero_apply']
    exact zero_mem _
  algebraMap_mem' r := by
    intro b hb
    rw [IsScalarTower.algebraMap_apply R K (CartierDual K A), CartierDual.algebraMap_apply]
    exact mul_mem (hcounit b hb) ⟨r, rfl⟩

theorem mem_dualOrder_iff (S : Subalgebra R A)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) (φ : CartierDual K A) :
    φ ∈ dualOrder S hcomul hcounit ↔ ∀ b ∈ S, φ b ∈ (algebraMap R K).range := Iff.rfl

end DualOrder

section Bases

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]

noncomputable def basisA (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} (b : Module.Basis ι R ↥S) : Module.Basis ι K A :=
  haveI := HopfOrder.moduleFlat_of_finite (K := K) S
  (Algebra.TensorProduct.basis K b).map (HopfOrder.baseChangeEquiv S hspan).toLinearEquiv

theorem basisA_apply (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} (b : Module.Basis ι R ↥S) (i : ι) :
    basisA S hspan b i = (b i : A) := by
  haveI := HopfOrder.moduleFlat_of_finite (K := K) S
  rw [basisA, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
  show HopfOrder.baseChangeEquiv S hspan ((1 : K) ⊗ₜ[R] b i) = _
  rw [HopfOrder.baseChangeEquiv_tmul, one_smul]

theorem basisA_repr_coe (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} [Finite ι] (b : Module.Basis ι R ↥S) (s : ↥S) (i : ι) :
    (basisA S hspan b).repr (s : A) i = algebraMap R K (b.repr s i) := by
  classical

  let f : ↥S →ₗ[R] K := ((basisA S hspan b).coord i).restrictScalars R ∘ₗ (S.val.toLinearMap)
  let g : ↥S →ₗ[R] K := (Algebra.linearMap R K) ∘ₗ (b.coord i)
  have hfg : f = g := by
    apply b.ext
    intro j
    show (basisA S hspan b).repr (S.val (b j)) i = algebraMap R K (b.repr (b j) i)
    rw [Module.Basis.repr_self]
    have : S.val (b j) = basisA S hspan b j := by rw [basisA_apply]; rfl
    rw [this, Module.Basis.repr_self]
    by_cases h : j = i
    · subst h; simp
    · simp [Finsupp.single_apply, h]
  have := LinearMap.congr_fun hfg s
  simpa [f, g] using this

theorem mem_of_forall_repr_mem (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} [Fintype ι] (b : Module.Basis ι R ↥S) (a : A)
    (h : ∀ i, (basisA S hspan b).repr a i ∈ (algebraMap R K).range) : a ∈ S := by
  choose r hr using h
  have ha : a = ∑ i, (basisA S hspan b).repr a i • basisA S hspan b i :=
    ((basisA S hspan b).sum_repr a).symm
  rw [ha]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  rw [← hr i, algebraMap_smul, basisA_apply]
  exact Subalgebra.smul_mem _ (b i).2 _

variable [Module.Finite K A] [Coalgebra.IsCocomm K A]
variable [Algebra R (CartierDual K A)] [IsScalarTower R K (CartierDual K A)]

noncomputable def basisD (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} [Finite ι] [DecidableEq ι] (b : Module.Basis ι R ↥S) :
    Module.Basis ι K (CartierDual K A) :=
  ((basisA S hspan b).dualBasis).map (CartierDual.ofDual K A)

theorem basisD_apply_apply (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} [Finite ι] [DecidableEq ι] (b : Module.Basis ι R ↥S) (i : ι) (a : A) :
    basisD S hspan b i a = (basisA S hspan b).repr a i := by
  rw [basisD, Module.Basis.map_apply, CartierDual.ofDual_apply, Module.Basis.dualBasis_apply]

theorem toDual_basisD (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} [Finite ι] [DecidableEq ι] (b : Module.Basis ι R ↥S) (i : ι) :
    CartierDual.toDual K A (basisD S hspan b i) = (basisA S hspan b).coord i := by
  apply LinearMap.ext; intro a
  rw [CartierDual.toDual_apply, basisD_apply_apply, Module.Basis.coord_apply]

theorem basisD_repr (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} [Finite ι] [DecidableEq ι] (b : Module.Basis ι R ↥S)
    (φ : CartierDual K A) (i : ι) :
    (basisD S hspan b).repr φ i = φ (b i : A) := by
  rw [basisD, Module.Basis.map_repr, LinearEquiv.trans_apply, Module.Basis.dualBasis_repr, basisA_apply]
  rfl

theorem basisD_mem (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} [Finite ι] [DecidableEq ι] (b : Module.Basis ι R ↥S) (i : ι) :
    ∀ s ∈ S, basisD S hspan b i s ∈ (algebraMap R K).range := by
  intro s hs
  rw [basisD_apply_apply]
  have := basisA_repr_coe S hspan b ⟨s, hs⟩ i
  exact ⟨_, this.symm⟩

theorem mem_span_basisD (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤) {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R ↥S)
    (φ : CartierDual K A) (hφ : ∀ s ∈ S, φ s ∈ (algebraMap R K).range) :
    φ ∈ Submodule.span R (Set.range (basisD S hspan b)) := by
  have hφ' : φ = ∑ i, (basisD S hspan b).repr φ i • basisD S hspan b i := ((basisD S hspan b).sum_repr φ).symm
  rw [hφ']
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨r, hr⟩ := hφ (b i : A) (b i).2
  rw [basisD_repr, ← hr, algebraMap_smul]
  exact Submodule.smul_mem _ r (Submodule.subset_span ⟨i, rfl⟩)

end Bases

section DualIsOrder

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
variable [Module.Finite K A] [Coalgebra.IsCocomm K A]
variable [Algebra R (CartierDual K A)] [IsScalarTower R K (CartierDual K A)]

variable (S : Subalgebra R A) (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
      (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)

theorem toSubmodule_dualOrder_eq [Module.Finite R ↥S] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R ↥S) :
    Subalgebra.toSubmodule (dualOrder S hcomul hcounit) = Submodule.span R (Set.range (basisD S hspan b)) := by
  apply le_antisymm
  · intro φ hφ
    exact mem_span_basisD S hspan _ φ hφ
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact basisD_mem S hspan _ i

include hfin hspan in
theorem finite_dualOrder : Module.Finite R ↥(dualOrder S hcomul hcounit) := by
  classical
  haveI := hfin
  haveI := HopfOrder.moduleFree_of_finite (K := K) S
  have hfg : (Subalgebra.toSubmodule (dualOrder S hcomul hcounit)).FG := by
    rw [toSubmodule_dualOrder_eq S hspan hcomul hcounit (Module.Free.chooseBasis R ↥S)]
    exact Submodule.fg_span (Set.finite_range _)
  exact Module.Finite.iff_fg.mpr hfg

include hfin hspan in
theorem span_dualOrder : Submodule.span K ((dualOrder S hcomul hcounit : Subalgebra R (CartierDual K A)) :
    Set (CartierDual K A)) = ⊤ := by
  classical
  haveI := hfin
  haveI := HopfOrder.moduleFree_of_finite (K := K) S
  apply eq_top_iff.mpr
  exact (basisD S hspan (Module.Free.chooseBasis R ↥S)).span_eq.ge.trans
    (Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact basisD_mem S hspan _ i))

theorem counit_dualOrder : ∀ φ ∈ dualOrder S hcomul hcounit,
    Coalgebra.counit (R := K) (A := CartierDual K A) φ ∈ (algebraMap R K).range := by
  intro φ hφ
  rw [CartierDual.counit_apply]
  exact hφ 1 S.one_mem

include hanti in
theorem antipode_dualOrder : ∀ φ ∈ dualOrder S hcomul hcounit,
    HopfAlgebra.antipode K (A := CartierDual K A) φ ∈ dualOrder S hcomul hcounit := by
  intro φ hφ b hb
  rw [CartierDual.antipode_apply]
  exact hφ _ (hanti b hb)

theorem tensor_repr_eq_pairing {ι : Type*} [Fintype ι] [DecidableEq ι] [Module.Finite R ↥S] (b : Module.Basis ι R ↥S)
    (w : CartierDual K A ⊗[K] CartierDual K A) (i j : ι) :
    ((basisD S hspan b).tensorProduct (basisD S hspan b)).repr w (i, j) =
      TensorProduct.dualDistrib K A A
        (TensorProduct.map (CartierDual.toDual K A).toLinearMap (CartierDual.toDual K A).toLinearMap w)
        (basisA S hspan b i ⊗ₜ[K] basisA S hspan b j) := by
  induction w with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, LinearMap.add_apply]
  | tmul φ ψ =>
      rw [Module.Basis.tensorProduct_repr_tmul_apply, TensorProduct.map_tmul, TensorProduct.dualDistrib_apply]
      simp only [LinearEquiv.coe_coe, CartierDual.toDual_apply, basisD_repr, basisA_apply, smul_eq_mul]
      exact mul_comm _ _

include hfin hspan in
theorem comul_dualOrder : ∀ φ ∈ dualOrder S hcomul hcounit, Coalgebra.comul (R := K) φ ∈
    (Algebra.TensorProduct.productMap
      (((Algebra.TensorProduct.includeLeft : CartierDual K A →ₐ[K] CartierDual K A ⊗[K] CartierDual K A).restrictScalars R).comp
        (dualOrder S hcomul hcounit).val)
      (((Algebra.TensorProduct.includeRight : CartierDual K A →ₐ[K] CartierDual K A ⊗[K] CartierDual K A).restrictScalars R).comp
        (dualOrder S hcomul hcounit).val)).range := by
  intro φ hφ
  classical
  haveI := hfin
  haveI := HopfOrder.moduleFree_of_finite (K := K) S
  let b := Module.Free.chooseBasis R ↥S
  let β := (basisD S hspan b).tensorProduct (basisD S hspan b)
  set w := Coalgebra.comul (R := K) φ with hw

  have hcoord : ∀ ij : _ × _, β.repr w ij ∈ (algebraMap R K).range := by
    rintro ⟨i, j⟩
    have h1 : β.repr w (i, j) = φ ((b i : A) * (b j : A)) := by
      refine (tensor_repr_eq_pairing S hspan b w i j).trans ?_
      rw [hw]
      refine (CartierDual.comul_pairing φ _ _).trans ?_
      rw [basisA_apply, basisA_apply]
    rw [h1]
    exact hφ _ (S.mul_mem (b i).2 (b j).2)
  choose r hr using hcoord
  have hw' : w = ∑ ij, β.repr w ij • β ij := (β.sum_repr w).symm
  rw [hw']
  refine Subalgebra.sum_mem _ fun ij _ => ?_
  obtain ⟨i, j⟩ := ij
  rw [← hr, algebraMap_smul, Module.Basis.tensorProduct_apply]
  refine Subalgebra.smul_mem _ ?_ _
  exact (AlgHom.mem_range _).mpr
    ⟨(⟨basisD S hspan b i, basisD_mem S hspan b i⟩ : ↥(dualOrder S hcomul hcounit)) ⊗ₜ[R]
      (⟨basisD S hspan b j, basisD_mem S hspan b j⟩ : ↥(dualOrder S hcomul hcounit)),
     HopfOrder.tensorSqHom_tmul (K := K) (dualOrder S hcomul hcounit) _ _⟩

end DualIsOrder

end S17Dual

namespace S17Dual

section Packaging

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
variable [Module.Finite K A] [Coalgebra.IsCocomm K A]
variable [Algebra R (CartierDual K A)] [IsScalarTower R K (CartierDual K A)]

theorem childI (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range) :
    ∃ S' : Subalgebra R (CartierDual K A),
      (∀ φ : CartierDual K A, φ ∈ S' ↔ ∀ b ∈ S, φ b ∈ (algebraMap R K).range) ∧
      Module.Finite R ↥S' ∧ Submodule.span K (S' : Set (CartierDual K A)) = ⊤ ∧
      (∀ x ∈ S', Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : CartierDual K A →ₐ[K] CartierDual K A ⊗[K] CartierDual K A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : CartierDual K A →ₐ[K] CartierDual K A ⊗[K] CartierDual K A).restrictScalars R).comp S'.val)).range) ∧
      (∀ x ∈ S', HopfAlgebra.antipode K (A := CartierDual K A) x ∈ S') ∧
      (∀ x ∈ S', Coalgebra.counit (R := K) (A := CartierDual K A) x ∈ (algebraMap R K).range) :=
  ⟨dualOrder S hcomul hcounit, mem_dualOrder_iff S hcomul hcounit, finite_dualOrder S hfin hspan hcomul hcounit,
    span_dualOrder S hfin hspan hcomul hcounit, comul_dualOrder S hfin hspan hcomul hcounit,
    antipode_dualOrder S hcomul hanti hcounit, counit_dualOrder S hcomul hcounit⟩

theorem childIII (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (S' : Subalgebra R (CartierDual K A))
    (hS' : ∀ φ : CartierDual K A, φ ∈ S' ↔ ∀ b ∈ S, φ b ∈ (algebraMap R K).range)
    (a : A) (ha : ∀ φ ∈ S', φ a ∈ (algebraMap R K).range) : a ∈ S := by
  classical
  haveI := hfin
  haveI := HopfOrder.moduleFree_of_finite (K := K) S
  let b := Module.Free.chooseBasis R ↥S
  apply mem_of_forall_repr_mem S hspan b a
  intro i
  rw [← basisD_apply_apply S hspan b i a]
  exact ha _ ((hS' _).mpr (basisD_mem S hspan b i))

end Packaging

end S17Dual

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    [Module.Finite K A] [Coalgebra.IsCocomm K A]
    [Algebra R (CartierDual K A)] [IsScalarTower R K (CartierDual K A)]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range) :
    ∃ S' : Subalgebra R (CartierDual K A),
      (∀ φ : CartierDual K A, φ ∈ S' ↔ ∀ b ∈ S, φ b ∈ (algebraMap R K).range) ∧
      Module.Finite R ↥S' ∧ Submodule.span K (S' : Set (CartierDual K A)) = ⊤ ∧
      (∀ x ∈ S', Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : CartierDual K A →ₐ[K] CartierDual K A ⊗[K] CartierDual K A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : CartierDual K A →ₐ[K] CartierDual K A ⊗[K] CartierDual K A).restrictScalars R).comp S'.val)).range) ∧
      (∀ x ∈ S', HopfAlgebra.antipode K (A := CartierDual K A) x ∈ S') ∧
      (∀ x ∈ S', Coalgebra.counit (R := K) (A := CartierDual K A) x ∈ (algebraMap R K).range) :=
  S17Dual.childI S hfin hspan hcomul hanti hcounit

end S_HopfOrder_exists_dual_hopfOrder
end P2MW
export P2MW.S_HopfOrder_exists_dual_hopfOrder (solution)
