-- Prove2me | solution 1 for Module.free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/33bbee78-2a72-5f35-8014-18207b547404

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
universe u

open scoped TensorProduct Polynomial

namespace LevelPow

section BaseChange

variable (R : Type u) [CommRing R] (S₁ S₂ : Type u) [CommRing S₁] [CommRing S₂]
  [Algebra R S₁] [Algebra R S₂] [Algebra S₁ S₂] [IsScalarTower R S₁ S₂]
  (A : Type u) [CommRing A] [Algebra R A] (a : A) (s₁ : S₁)

abbrev I₁ : Ideal (S₁ ⊗[R] A) := Ideal.span {(1 : S₁) ⊗ₜ[R] a - s₁ ⊗ₜ[R] (1 : A)}

abbrev I₂ : Ideal (S₂ ⊗[R] A) := Ideal.span {(1 : S₂) ⊗ₜ[R] a - algebraMap S₁ S₂ s₁ ⊗ₜ[R] (1 : A)}

noncomputable abbrev canc : S₂ ⊗[S₁] (S₁ ⊗[R] A) ≃ₐ[S₂] S₂ ⊗[R] A :=
  Algebra.TensorProduct.cancelBaseChange R S₁ S₂ S₂ A

theorem canc_tmul (x : S₂) (y : S₁) (z : A) :
    canc R S₁ S₂ A (x ⊗ₜ[S₁] (y ⊗ₜ[R] z)) = (y • x) ⊗ₜ[R] z :=
  Algebra.TensorProduct.cancelBaseChange_tmul R S₁ S₂ S₂ A x y z

noncomputable def step1 :
    S₂ ⊗[S₁] (S₁ ⊗[R] A ⧸ I₁ R S₁ A a s₁) ≃ₗ[S₁]
      (S₂ ⊗[S₁] (S₁ ⊗[R] A)) ⧸ LinearMap.range (TensorProduct.map (LinearMap.id : S₂ →ₗ[S₁] S₂) ((I₁ R S₁ A a s₁).restrictScalars S₁).subtype) :=
  (TensorProduct.congr (LinearEquiv.refl S₁ S₂) (Submodule.Quotient.restrictScalarsEquiv S₁ (I₁ R S₁ A a s₁)).symm).trans
    (TensorProduct.tensorQuotientEquiv S₂ ((I₁ R S₁ A a s₁).restrictScalars S₁))

abbrev rel₁ : S₁ ⊗[R] A := (1 : S₁) ⊗ₜ[R] a - s₁ ⊗ₜ[R] (1 : A)

abbrev rel₂ : S₂ ⊗[R] A := (1 : S₂) ⊗ₜ[R] a - algebraMap S₁ S₂ s₁ ⊗ₜ[R] (1 : A)

theorem canc_one_tmul_rel₁ : canc R S₁ S₂ A ((1 : S₂) ⊗ₜ[S₁] rel₁ R S₁ A a s₁) = rel₂ R S₁ S₂ A a s₁ := by
  simp only [TensorProduct.tmul_sub, map_sub, canc_tmul, one_smul]
  show _ = (1 : S₂) ⊗ₜ[R] a - algebraMap S₁ S₂ s₁ ⊗ₜ[R] (1 : A)
  rw [Algebra.algebraMap_eq_smul_one]

abbrev Rg : Submodule S₁ (S₂ ⊗[S₁] (S₁ ⊗[R] A)) :=
  LinearMap.range (TensorProduct.map (LinearMap.id : S₂ →ₗ[S₁] S₂) ((I₁ R S₁ A a s₁).restrictScalars S₁).subtype)

theorem map_Rg_eq :
    (Rg R S₁ S₂ A a s₁).map ((canc R S₁ S₂ A).toLinearEquiv.restrictScalars S₁).toLinearMap
      = (I₂ R S₁ S₂ A a s₁).restrictScalars S₁ := by
  apply le_antisymm
  ·
    rw [Submodule.map_le_iff_le_comap, LinearMap.range_le_iff_comap, Submodule.eq_top_iff']
    intro t
    rw [Submodule.mem_comap, Submodule.mem_comap]
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
    | tmul x i =>
      obtain ⟨i, hi⟩ := i
      obtain ⟨p, rfl⟩ := Ideal.mem_span_singleton'.mp hi
      show canc R S₁ S₂ A (x ⊗ₜ[S₁] (p * rel₁ R S₁ A a s₁)) ∈ I₂ R S₁ S₂ A a s₁
      have : x ⊗ₜ[S₁] (p * rel₁ R S₁ A a s₁) = (x ⊗ₜ[S₁] p) * ((1 : S₂) ⊗ₜ[S₁] rel₁ R S₁ A a s₁) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      rw [this, map_mul, canc_one_tmul_rel₁]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  ·
    intro q hq
    obtain ⟨q', rfl⟩ := Ideal.mem_span_singleton'.mp hq
    obtain ⟨t, rfl⟩ := (canc R S₁ S₂ A).surjective q'
    rw [Submodule.mem_map]
    refine ⟨t * ((1 : S₂) ⊗ₜ[S₁] rel₁ R S₁ A a s₁), ?_, by
      show canc R S₁ S₂ A (t * 1 ⊗ₜ[S₁] rel₁ R S₁ A a s₁) = canc R S₁ S₂ A t * rel₂ R S₁ S₂ A a s₁
      rw [map_mul, canc_one_tmul_rel₁]⟩
    clear hq
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
    | tmul x p =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      exact ⟨x ⊗ₜ[S₁] ⟨p * rel₁ R S₁ A a s₁, Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)⟩, rfl⟩

noncomputable def equiv₁ :
    S₂ ⊗[S₁] (S₁ ⊗[R] A ⧸ I₁ R S₁ A a s₁) ≃ₗ[S₁] (S₂ ⊗[R] A ⧸ I₂ R S₁ S₂ A a s₁) :=
  (step1 R S₁ S₂ A a s₁).trans <|
    (Submodule.Quotient.equiv (Rg R S₁ S₂ A a s₁) ((I₂ R S₁ S₂ A a s₁).restrictScalars S₁)
      ((canc R S₁ S₂ A).toLinearEquiv.restrictScalars S₁) (map_Rg_eq R S₁ S₂ A a s₁)).trans
    (Submodule.Quotient.restrictScalarsEquiv S₁ (I₂ R S₁ S₂ A a s₁))

theorem equiv₁_tmul_mk (x : S₂) (p : S₁ ⊗[R] A) :
    equiv₁ R S₁ S₂ A a s₁ (x ⊗ₜ[S₁] Ideal.Quotient.mk (I₁ R S₁ A a s₁) p)
      = Ideal.Quotient.mk (I₂ R S₁ S₂ A a s₁) (canc R S₁ S₂ A (x ⊗ₜ[S₁] p)) := by
  simp [equiv₁, step1, TensorProduct.tensorQuotientEquiv, Submodule.Quotient.equiv,
    Submodule.Quotient.restrictScalarsEquiv]
  rfl

theorem canc_tmul_eq_smul (x : S₂) (p : S₁ ⊗[R] A) :
    canc R S₁ S₂ A (x ⊗ₜ[S₁] p) = x • canc R S₁ S₂ A ((1 : S₂) ⊗ₜ[S₁] p) := by
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem equiv₁_smul (x : S₂) (t : S₂ ⊗[S₁] (S₁ ⊗[R] A ⧸ I₁ R S₁ A a s₁)) :
    equiv₁ R S₁ S₂ A a s₁ (x • t) = x • equiv₁ R S₁ S₂ A a s₁ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [smul_add, map_add, map_add, smul_add, hu, hv]
  | tmul y m =>
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective m
    rw [TensorProduct.smul_tmul', equiv₁_tmul_mk, equiv₁_tmul_mk, canc_tmul_eq_smul R S₁ S₂ A (x • y),
      canc_tmul_eq_smul R S₁ S₂ A y, smul_eq_mul, mul_smul, ← Ideal.Quotient.mkₐ_eq_mk S₂]
    exact map_smul (Ideal.Quotient.mkₐ S₂ (I₂ R S₁ S₂ A a s₁)) x _

noncomputable def baseChangeEquiv :
    S₂ ⊗[S₁] (S₁ ⊗[R] A ⧸ Ideal.span {(1 : S₁) ⊗ₜ[R] a - s₁ ⊗ₜ[R] (1 : A)})
      ≃ₗ[S₂] (S₂ ⊗[R] A ⧸ Ideal.span {(1 : S₂) ⊗ₜ[R] a - algebraMap S₁ S₂ s₁ ⊗ₜ[R] (1 : A)}) :=
  { (equiv₁ R S₁ S₂ A a s₁).toAddEquiv with
    map_smul' := fun x t => equiv₁_smul R S₁ S₂ A a s₁ x t }

@[scoped simp] theorem baseChangeEquiv_tmul_mk (x : S₂) (p : S₁ ⊗[R] A) :
    baseChangeEquiv R S₁ S₂ A a s₁ (x ⊗ₜ[S₁] Ideal.Quotient.mk _ p)
      = Ideal.Quotient.mk _ (canc R S₁ S₂ A (x ⊗ₜ[S₁] p)) :=
  equiv₁_tmul_mk R S₁ S₂ A a s₁ x p

theorem baseChangeEquiv_tmul_mk_tmul (x : S₂) (y : S₁) (z : A) :
    baseChangeEquiv R S₁ S₂ A a s₁ (x ⊗ₜ[S₁] Ideal.Quotient.mk _ (y ⊗ₜ[R] z))
      = Ideal.Quotient.mk _ ((y • x) ⊗ₜ[R] z) := by
  rw [baseChangeEquiv_tmul_mk, canc_tmul]

end BaseChange

end LevelPow
p2m_reactivate "P2MW.S_Module_free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul.LevelPow"

noncomputable section
namespace LevelPow
namespace Pow

variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
  (a : A) (n : ℕ) (s : S)
  (S' : Type u) [CommRing S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
  (h : IsAdjoinRoot S' (Polynomial.X ^ n - Polynomial.C s : S[X]))

local notation "II" => (Ideal.span {(1 : S) ⊗ₜ[R] (a ^ n) - s ⊗ₜ[R] (1 : A)} : Ideal (S ⊗[R] A))
local notation "JJ" => (Ideal.span {(1 : S') ⊗ₜ[R] a - h.root ⊗ₜ[R] (1 : A)} : Ideal (S' ⊗[R] A))

theorem root_pow : h.root ^ n = algebraMap S S' s := by
  have h0 : Polynomial.aeval h.root (Polynomial.X ^ n - Polynomial.C s : S[X]) = 0 := IsAdjoinRoot.aeval_root_self h
  rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at h0
  exact h0

def gA : A →ₐ[R] (S' ⊗[R] A ⧸ JJ) :=
  ((Ideal.Quotient.mkₐ S' JJ).restrictScalars R).comp Algebra.TensorProduct.includeRight

theorem gA_apply (x : A) : gA R S A a n s S' h x = Ideal.Quotient.mk JJ ((1 : S') ⊗ₜ[R] x) := rfl

theorem mk_one_tmul_a :
    Ideal.Quotient.mk JJ ((1 : S') ⊗ₜ[R] a) = Algebra.ofId S' (S' ⊗[R] A ⧸ JJ) h.root := by
  change _ = Ideal.Quotient.mk JJ (algebraMap S' (S' ⊗[R] A) h.root)
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  exact Ideal.Quotient.eq.mpr (Ideal.subset_span (Set.mem_singleton _))

def ψ₀ : S ⊗[R] A →ₐ[S] (S' ⊗[R] A ⧸ JJ) :=
  Algebra.TensorProduct.lift (Algebra.ofId S (S' ⊗[R] A ⧸ JJ)) (gA R S A a n s S' h)
    (fun x z => Commute.all (Algebra.ofId S (S' ⊗[R] A ⧸ JJ) x) (gA R S A a n s S' h z))

theorem ψ₀_one_tmul (x : A) : ψ₀ R S A a n s S' h ((1 : S) ⊗ₜ[R] x) = gA R S A a n s S' h x :=
  AlgHom.congr_fun (Algebra.TensorProduct.lift_comp_includeRight (Algebra.ofId S (S' ⊗[R] A ⧸ JJ))
    (gA R S A a n s S' h) (fun x z => Commute.all (Algebra.ofId S (S' ⊗[R] A ⧸ JJ) x) (gA R S A a n s S' h z))) x

theorem ψ₀_tmul_one (c : S) : ψ₀ R S A a n s S' h (c ⊗ₜ[R] (1 : A)) = Algebra.ofId S (S' ⊗[R] A ⧸ JJ) c :=
  AlgHom.congr_fun (Algebra.TensorProduct.lift_comp_includeLeft (Algebra.ofId S (S' ⊗[R] A ⧸ JJ))
    (gA R S A a n s S' h) (fun x z => Commute.all (Algebra.ofId S (S' ⊗[R] A ⧸ JJ) x) (gA R S A a n s S' h z))) c

theorem gA_pow_eq : gA R S A a n s S' h (a ^ n) = Algebra.ofId S (S' ⊗[R] A ⧸ JJ) s := by
  rw [map_pow, gA_apply, mk_one_tmul_a, ← map_pow, root_pow, Algebra.ofId_apply, Algebra.ofId_apply]
  exact (IsScalarTower.algebraMap_apply S S' _ s).symm

theorem ψ₀_rel : ψ₀ R S A a n s S' h ((1 : S) ⊗ₜ[R] (a ^ n) - s ⊗ₜ[R] (1 : A)) = 0 := by
  rw [map_sub, ψ₀_one_tmul, ψ₀_tmul_one, gA_pow_eq, sub_self]

theorem ψ₀_ker : ∀ z ∈ II, ψ₀ R S A a n s S' h z = 0 := fun z hz =>
  (RingHom.mem_ker).mp ((Ideal.span_le (I := RingHom.ker (ψ₀ R S A a n s S' h).toRingHom)).mpr
    (Set.singleton_subset_iff.mpr ((RingHom.mem_ker).mpr (ψ₀_rel R S A a n s S' h))) hz)

def Φ : (S ⊗[R] A ⧸ II) →ₐ[S] (S' ⊗[R] A ⧸ JJ) :=
  Ideal.Quotient.liftₐ II (ψ₀ R S A a n s S' h) (ψ₀_ker R S A a n s S' h)

theorem Φ_mk (z : S ⊗[R] A) : Φ R S A a n s S' h (Ideal.Quotient.mk _ z) = ψ₀ R S A a n s S' h z := rfl

def gA' : A →ₐ[R] (S ⊗[R] A ⧸ II) :=
  ((Ideal.Quotient.mkₐ S II).restrictScalars R).comp Algebra.TensorProduct.includeRight

theorem gA'_apply (x : A) : gA' R S A a n s x = Ideal.Quotient.mk II ((1 : S) ⊗ₜ[R] x) := rfl

abbrev abar : S ⊗[R] A ⧸ II := Ideal.Quotient.mk II ((1 : S) ⊗ₜ[R] a)

theorem abar_root : Polynomial.aeval (abar R S A a n s) (Polynomial.X ^ n - Polynomial.C s : S[X]) = 0 := by
  rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, ← map_pow, Algebra.TensorProduct.tmul_pow, one_pow,
    sub_eq_zero]
  change _ = Ideal.Quotient.mk II (algebraMap S (S ⊗[R] A) s)
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  exact Ideal.Quotient.eq.mpr (Ideal.subset_span (Set.mem_singleton _))

def fS' : S' →ₐ[S] (S ⊗[R] A ⧸ II) := h.liftHom (abar R S A a n s) (abar_root R S A a n s)

theorem fS'_root : fS' R S A a n s S' h h.root = abar R S A a n s := h.liftHom_root _

def χ₀ : S' ⊗[R] A →ₐ[S] (S ⊗[R] A ⧸ II) :=
  Algebra.TensorProduct.lift (fS' R S A a n s S' h) (gA' R S A a n s)
    (fun x z => Commute.all (fS' R S A a n s S' h x) (gA' R S A a n s z))

theorem χ₀_one_tmul (x : A) : χ₀ R S A a n s S' h ((1 : S') ⊗ₜ[R] x) = gA' R S A a n s x :=
  AlgHom.congr_fun (Algebra.TensorProduct.lift_comp_includeRight (fS' R S A a n s S' h) (gA' R S A a n s)
    (fun x z => Commute.all (fS' R S A a n s S' h x) (gA' R S A a n s z))) x

theorem χ₀_tmul_one (c : S') : χ₀ R S A a n s S' h (c ⊗ₜ[R] (1 : A)) = fS' R S A a n s S' h c :=
  AlgHom.congr_fun (Algebra.TensorProduct.lift_comp_includeLeft (fS' R S A a n s S' h) (gA' R S A a n s)
    (fun x z => Commute.all (fS' R S A a n s S' h x) (gA' R S A a n s z))) c

theorem χ₀_rel : χ₀ R S A a n s S' h ((1 : S') ⊗ₜ[R] a - h.root ⊗ₜ[R] (1 : A)) = 0 := by
  rw [map_sub, χ₀_one_tmul, χ₀_tmul_one, gA'_apply, fS'_root, sub_self]

theorem χ₀_ker : ∀ z ∈ JJ, χ₀ R S A a n s S' h z = 0 := fun z hz =>
  (RingHom.mem_ker).mp ((Ideal.span_le (I := RingHom.ker (χ₀ R S A a n s S' h).toRingHom)).mpr
    (Set.singleton_subset_iff.mpr ((RingHom.mem_ker).mpr (χ₀_rel R S A a n s S' h))) hz)

def Ψ : (S' ⊗[R] A ⧸ JJ) →ₐ[S] (S ⊗[R] A ⧸ II) :=
  Ideal.Quotient.liftₐ JJ (χ₀ R S A a n s S' h) (χ₀_ker R S A a n s S' h)

theorem Ψ_mk (z : S' ⊗[R] A) : Ψ R S A a n s S' h (Ideal.Quotient.mk _ z) = χ₀ R S A a n s S' h z := rfl

def mapₐ : S[X] →ₐ[S] S' where
  toRingHom := h.map
  commutes' r := by
    show h.map (algebraMap S S[X] r) = algebraMap S S' r
    rw [Polynomial.algebraMap_eq]
    exact (h.algebraMap_apply r).symm

theorem mapₐ_apply (p : S[X]) : mapₐ S n s S' h p = h.map p := rfl

theorem algHom_ext_root {T : Type u} [Semiring T] [Algebra S T] (f₁ f₂ : S' →ₐ[S] T) (hf : f₁ h.root = f₂ h.root) :
    f₁ = f₂ := by
  have key : f₁.comp (mapₐ S n s S' h) = f₂.comp (mapₐ S n s S' h) :=
    Polynomial.algHom_ext (by simp only [AlgHom.comp_apply, mapₐ_apply, IsAdjoinRoot.map_X, hf])
  ext c
  obtain ⟨p, rfl⟩ := h.map_surjective c
  exact AlgHom.congr_fun key p

theorem Φ_Ψ : (Φ R S A a n s S' h).comp (Ψ R S A a n s S' h) = AlgHom.id S _ := by
  apply Ideal.Quotient.algHom_ext
  apply Algebra.TensorProduct.ext
  ·
    apply algHom_ext_root S n s S' h
    show Φ R S A a n s S' h (Ψ R S A a n s S' h (Ideal.Quotient.mk _ (h.root ⊗ₜ[R] (1 : A)))) = Ideal.Quotient.mk _ (h.root ⊗ₜ[R] (1 : A))
    rw [Ψ_mk, χ₀_tmul_one, fS'_root, Φ_mk, ψ₀_one_tmul, gA_apply, mk_one_tmul_a]
    change Ideal.Quotient.mk JJ (algebraMap S' (S' ⊗[R] A) h.root) = _
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  · apply AlgHom.ext; intro x
    show Φ R S A a n s S' h (Ψ R S A a n s S' h (Ideal.Quotient.mk _ ((1 : S') ⊗ₜ[R] x))) = Ideal.Quotient.mk _ ((1 : S') ⊗ₜ[R] x)
    rw [Ψ_mk, χ₀_one_tmul, gA'_apply, Φ_mk, ψ₀_one_tmul, gA_apply]

theorem Ψ_Φ : (Ψ R S A a n s S' h).comp (Φ R S A a n s S' h) = AlgHom.id S _ := by
  apply Ideal.Quotient.algHom_ext
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · apply AlgHom.ext; intro x
    show Ψ R S A a n s S' h (Φ R S A a n s S' h (Ideal.Quotient.mk _ ((1 : S) ⊗ₜ[R] x))) = Ideal.Quotient.mk _ ((1 : S) ⊗ₜ[R] x)
    rw [Φ_mk, ψ₀_one_tmul, gA_apply, Ψ_mk, χ₀_one_tmul, gA'_apply]

end Pow
p2m_reactivate "P2MW.S_Module_free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul.LevelPow"

def powEquiv (R S A : Type u) [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    (a : A) (n : ℕ) (s : S)
    (S' : Type u) [CommRing S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    (h : IsAdjoinRoot S' (Polynomial.X ^ n - Polynomial.C s : S[X])) :
    (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] (a ^ n) - s ⊗ₜ[R] (1 : A)}) ≃ₐ[S]
      (S' ⊗[R] A ⧸ Ideal.span {(1 : S') ⊗ₜ[R] a - h.root ⊗ₜ[R] (1 : A)}) :=
  AlgEquiv.ofAlgHom (Pow.Φ R S A a n s S' h) (Pow.Ψ R S A a n s S' h) (Pow.Φ_Ψ R S A a n s S' h) (Pow.Ψ_Φ R S A a n s S' h)

end LevelPow
p2m_reactivate "P2MW.S_Module_free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul.LevelPow"
end
p2m_reactivate "P2MW.S_Module_free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul.LevelPow"

namespace LevelPow

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A] (a : A)

theorem finite_levelSet (hfin : (Polynomial.aeval a : R[X] →ₐ[R] A).toRingHom.Finite)
    (T : Type u) [CommRing T] [Algebra R T] (t : T) :
    Module.Finite T (T ⊗[R] A ⧸ Ideal.span {(1 : T) ⊗ₜ[R] a - t ⊗ₜ[R] (1 : A)}) := by
  classical
  letI alg : Algebra R[X] A := (Polynomial.aeval a : R[X] →ₐ[R] A).toRingHom.toAlgebra
  haveI : Module.Finite R[X] A := hfin
  have hsmul : ∀ (p : R[X]) (x : A), p • x = Polynomial.aeval a p * x := fun _ _ => rfl
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := R[X]) (M := A)
  let π := Ideal.Quotient.mkₐ T (Ideal.span {(1 : T) ⊗ₜ[R] a - t ⊗ₜ[R] (1 : A)})

  have hπa : π ((1 : T) ⊗ₜ[R] a) = π (algebraMap T (T ⊗[R] A) t) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    exact Ideal.Quotient.eq.mpr (Ideal.subset_span (Set.mem_singleton _))

  have hpoly : ∀ p : R[X], π ((1 : T) ⊗ₜ[R] Polynomial.aeval a p) =
      π (algebraMap T (T ⊗[R] A) (Polynomial.aeval t p)) := by
    intro p
    let f := (π.restrictScalars R).comp (Algebra.TensorProduct.includeRight (R := R) (A := T) (B := A))
    let φ := (π.restrictScalars R).comp ((Algebra.ofId T (T ⊗[R] A)).restrictScalars R)
    have hf : ∀ x : A, f x = π ((1 : T) ⊗ₜ[R] x) := fun _ => rfl
    have hφ : ∀ x : T, φ x = π (algebraMap T (T ⊗[R] A) x) := fun _ => rfl
    rw [← hf, ← Polynomial.aeval_algHom_apply, hf, hπa, ← hφ, Polynomial.aeval_algHom_apply, hφ]
  refine ⟨⟨G.image fun g => π ((1 : T) ⊗ₜ[R] g), ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  rintro q -
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  change π x ∈ _
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | tmul t' x =>
      have hx : x ∈ Submodule.span R[X] (G : Set A) := by rw [hG]; trivial
      have key : ∀ y ∈ Submodule.span R[X] (G : Set A), ∀ t'' : T,
          π (t'' ⊗ₜ[R] y) ∈ Submodule.span T ((fun g => π ((1 : T) ⊗ₜ[R] g)) '' (G : Set A)) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem g hg =>
            intro t''
            have e1 : t'' ⊗ₜ[R] g = t'' • ((1 : T) ⊗ₜ[R] g) := by
              rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
            rw [e1, map_smul]
            exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, rfl⟩)
        | zero => intro t''; rw [TensorProduct.tmul_zero, map_zero]; exact zero_mem _
        | add y z _ _ hy hz => intro t''; rw [TensorProduct.tmul_add, map_add]; exact add_mem (hy t'') (hz t'')
        | smul p y _ hy =>
            intro t''
            have e2 : t'' ⊗ₜ[R] (p • y) = ((1 : T) ⊗ₜ[R] Polynomial.aeval a p) * (t'' ⊗ₜ[R] y) := by
              rw [hsmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
            rw [e2, map_mul, hpoly, AlgHom.commutes, ← Algebra.smul_def]
            exact Submodule.smul_mem _ _ (hy t'')
      exact key x hx t'

theorem flat_levelSet (m : ℕ)
    (h : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
      Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) ∧
      Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) ∧
      Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) = m)
    (S' : Type u) [CommRing S'] [Algebra R S'] (y : S') :
    Module.Flat S' (S' ⊗[R] A ⧸ Ideal.span {(1 : S') ⊗ₜ[R] a - y ⊗ₜ[R] (1 : A)}) := by
  set L := S' ⊗[R] A ⧸ Ideal.span {(1 : S') ⊗ₜ[R] a - y ⊗ₜ[R] (1 : A)}
  apply Module.flat_of_isLocalized_maximal (R := S') (S := S') (M := L)
    (Mₚ := fun P _ => Localization.AtPrime P ⊗[S'] L)
    (f := fun P _ => TensorProduct.mk S' (Localization.AtPrime P) L 1)
  intro P hP
  let T := Localization.AtPrime P
  obtain ⟨-, hfree, -⟩ := h T (algebraMap S' T y)
  haveI := hfree
  haveI : Module.Flat T (T ⊗[R] A ⧸ Ideal.span {(1 : T) ⊗ₜ[R] a - algebraMap S' T y ⊗ₜ[R] (1 : A)}) :=
    Module.Flat.of_projective
  haveI : Module.Flat S' (T ⊗[R] A ⧸ Ideal.span {(1 : T) ⊗ₜ[R] a - algebraMap S' T y ⊗ₜ[R] (1 : A)}) :=
    Module.Flat.trans S' T _
  exact Module.Flat.of_linearEquiv ((baseChangeEquiv R S' T A a y).restrictScalars S')

theorem finite_maximalSpectrum (S S' : Type u) [CommRing S] [CommRing S'] [IsLocalRing S] [Algebra S S']
    [Module.Finite S S'] : Finite (MaximalSpectrum S') := by
  classical
  let 𝔪 := IsLocalRing.maximalIdeal S
  let I : Ideal S' := 𝔪.map (algebraMap S S')

  letI : Field (S ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Module.Finite (S ⧸ 𝔪) (S' ⧸ I) := Module.Finite.of_restrictScalars_finite S _ _
  haveI : IsArtinianRing (S' ⧸ I) := IsArtinianRing.of_finite (S ⧸ 𝔪) (S' ⧸ I)

  have hle : ∀ P : MaximalSpectrum S', I ≤ P.asIdeal := by
    intro P
    haveI := P.isMaximal
    rw [Ideal.map_le_iff_le_comap]
    have hc : (P.asIdeal.comap (algebraMap S S')).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
    rw [IsLocalRing.eq_maximalIdeal hc]
  let F : MaximalSpectrum S' → MaximalSpectrum (S' ⧸ I) := fun P =>
    ⟨P.asIdeal.map (Ideal.Quotient.mk I), by
      haveI := P.isMaximal
      refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective P.isMaximal).resolve_left ?_
      intro htop
      apply P.isMaximal.ne_top
      have := congrArg (Ideal.comap (Ideal.Quotient.mk I)) htop
      rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.mpr (hle P), Ideal.comap_top] at this⟩
  refine Finite.of_injective F fun P Q hPQ => ?_
  have h1 : P.asIdeal = Q.asIdeal := by
    have := congrArg (fun M : MaximalSpectrum (S' ⧸ I) => M.asIdeal.comap (Ideal.Quotient.mk I)) hPQ
    simp only [F] at this
    rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr (hle P), sup_eq_left.mpr (hle Q)] at this
  exact MaximalSpectrum.ext h1

theorem finite_free_finrank_over_base (m : ℕ) (hfin : (Polynomial.aeval a : R[X] →ₐ[R] A).toRingHom.Finite)
    (h : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
      Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) ∧
      Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) ∧
      Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) = m)
    (S S' : Type u) [CommRing S] [CommRing S'] [IsLocalRing S] [Algebra R S] [Algebra R S'] [Algebra S S']
    [IsScalarTower R S S'] [Module.Free S S'] [Module.Finite S S'] (y : S') :
    Module.Finite S (S' ⊗[R] A ⧸ Ideal.span {(1 : S') ⊗ₜ[R] a - y ⊗ₜ[R] (1 : A)}) ∧
    Module.Free S (S' ⊗[R] A ⧸ Ideal.span {(1 : S') ⊗ₜ[R] a - y ⊗ₜ[R] (1 : A)}) ∧
    Module.finrank S (S' ⊗[R] A ⧸ Ideal.span {(1 : S') ⊗ₜ[R] a - y ⊗ₜ[R] (1 : A)}) = Module.finrank S S' * m := by
  classical
  set L := S' ⊗[R] A ⧸ Ideal.span {(1 : S') ⊗ₜ[R] a - y ⊗ₜ[R] (1 : A)}
  haveI : Module.Finite S' L := finite_levelSet a hfin S' y
  haveI : Module.Flat S' L := flat_levelSet a m h S' y
  haveI : Finite (MaximalSpectrum S') := finite_maximalSpectrum S S'

  have rk : ∀ P : MaximalSpectrum S', Module.finrank (S' ⧸ P.1) ((S' ⧸ P.1) ⊗[S'] L) = m := by
    intro P
    haveI := P.isMaximal
    letI : Field (S' ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
    obtain ⟨-, -, hrk⟩ := h (S' ⧸ P.asIdeal) (Ideal.Quotient.mk P.asIdeal y)
    rw [← hrk]
    exact (baseChangeEquiv R S' (S' ⧸ P.asIdeal) A a y).finrank_eq
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq S' L m rk

  let e : L ≃ₗ[S] (Fin m → S') := (b.repr.restrictScalars S).trans (Finsupp.linearEquivFunOnFinite S S' (Fin m))
  haveI : Module.Finite S L := Module.Finite.trans S' L
  refine ⟨inferInstance, Module.Free.of_equiv e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_comm]

end LevelPow
p2m_reactivate "P2MW.S_Module_free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul.LevelPow"

open LevelPow in
theorem solution
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (a : A) (m n : ℕ) (hn : 1 ≤ n)
    (hfin : (Polynomial.aeval a : R[X] →ₐ[R] A).toRingHom.Finite)
    (h : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
      Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) ∧
      Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) ∧
      Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) = m)
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S) :
    Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] (a ^ n) - s ⊗ₜ[R] (1 : A)}) ∧
      Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] (a ^ n) - s ⊗ₜ[R] (1 : A)}) ∧
      Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] (a ^ n) - s ⊗ₜ[R] (1 : A)}) = n * m := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hmon : (Polynomial.X ^ n - Polynomial.C s : S[X]).Monic := Polynomial.monic_X_pow_sub_C s hn0
  set S' := AdjoinRoot (Polynomial.X ^ n - Polynomial.C s : S[X]) with hS'
  let pb := AdjoinRoot.powerBasis' hmon
  haveI : Module.Free S S' := Module.Free.of_basis pb.basis
  haveI : Module.Finite S S' := Module.Finite.of_basis pb.basis
  have hdim : Module.finrank S S' = n := by
    rw [Module.finrank_eq_card_basis pb.basis, Fintype.card_fin]
    show (AdjoinRoot.powerBasis' hmon).dim = n
    rw [AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_X_pow_sub_C]
  obtain ⟨hF, hFr, hrk⟩ := finite_free_finrank_over_base a m hfin h S S'
    ((AdjoinRoot.isAdjoinRoot (Polynomial.X ^ n - Polynomial.C s : S[X])).root)
  rw [hdim] at hrk
  let e := (powEquiv R S A a n s S' (AdjoinRoot.isAdjoinRoot _)).toLinearEquiv
  haveI := hF; haveI := hFr
  exact ⟨Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm, by rw [e.finrank_eq, hrk]⟩

end S_Module_free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul
end P2MW
export P2MW.S_Module_free_and_finrank_tensorProduct_quot_span_tmul_pow_sub_eq_mul (solution)
