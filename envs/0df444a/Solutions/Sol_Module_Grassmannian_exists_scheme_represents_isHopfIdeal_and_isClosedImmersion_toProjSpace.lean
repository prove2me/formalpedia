-- Prove2me | solution 1 for Module.Grassmannian.exists_scheme_represents_isHopfIdeal_and_isClosedImmersion_toProjSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/582d1718-8fee-5e3a-b035-e2839e8aea09

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_HopfAlgebra_HopfIdealQuotient
import Theorems.Thm_Module_Grassmannian_exists_scheme_represents_and_isClosedImmersion_toProjSpace
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal
import Theorems.Thm_Module_Projective_exists_ideal_forall_tmul_eq_zero_iff_map_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Grassmannian_exists_scheme_represents_isHopfIdeal_and_isClosedImmersion_toProjSpace
p2m_attr_erase "simp" "CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst"

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GrassClosed
open TensorProduct Module
variable {R : Type} [CommRing R] {A : Type} [AddCommGroup A] [Module R A] {k : ℕ}

def Stable (B : Type) [CommRing B] [Algebra R B] (t : A →ₗ[R] A) (N : Grassmannian B (B ⊗[R] A) k) : Prop :=
  ∀ x : B ⊗[R] A, x ∈ N.toSubmodule → t.baseChange B x ∈ N.toSubmodule

variable {B B' : Type} [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (φ : B →ₐ[R] B')

theorem stable_map_iff (t : A →ₗ[R] A) (N : Grassmannian B (B ⊗[R] A) k) :
    Stable B' t (Grassmannian.map φ N) ↔
      ∀ n : B ⊗[R] A, n ∈ N.toSubmodule →
        (letI : Algebra B B' := φ.toAlgebra
         ((1 : B') ⊗ₜ[B] (N.toSubmodule.mkQ (t.baseChange B n)) :
            B' ⊗[B] ((B ⊗[R] A) ⧸ N.toSubmodule)) = 0) := by
  letI : Algebra B B' := φ.toAlgebra
  letI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have hmapN : (Grassmannian.map φ N).toSubmodule =
      LinearMap.ker (Grassmannian.baseChangeMkQ B' N.toSubmodule) := Grassmannian.map_toSubmodule φ N
  have hq' : ∀ x : B' ⊗[R] A, Grassmannian.baseChangeMkQ B' N.toSubmodule x =
      (N.toSubmodule.mkQ.baseChange B') ((AlgebraTensorModule.cancelBaseChange R B B' B' A).symm x) :=
    fun x => rfl

  have hT : ∀ x : B' ⊗[R] A,
      (AlgebraTensorModule.cancelBaseChange R B B' B' A).symm (t.baseChange B' x) =
        (t.baseChange B).baseChange B' ((AlgebraTensorModule.cancelBaseChange R B B' B' A).symm x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b' a₀ =>
        rw [LinearMap.baseChange_tmul, AlgebraTensorModule.cancelBaseChange_symm_tmul,
          AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hex : Function.Exact (N.toSubmodule.subtype.baseChange B') (N.toSubmodule.mkQ.baseChange B') := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact (M := ↥N.toSubmodule) (N := B ⊗[R] A) (P := (B ⊗[R] A) ⧸ N.toSubmodule) B'
      (LinearMap.exact_subtype_mkQ N.toSubmodule) (Submodule.mkQ_surjective _)
  constructor
  · intro hW n hn
    have hx : (AlgebraTensorModule.cancelBaseChange R B B' B' A) ((1 : B') ⊗ₜ[B] n) ∈
        (Grassmannian.map φ N).toSubmodule := by
      rw [hmapN, LinearMap.mem_ker, hq', LinearEquiv.symm_apply_apply]
      exact (hex _).mpr ⟨(1 : B') ⊗ₜ[B] ⟨n, hn⟩, by rw [LinearMap.baseChange_tmul]; rfl⟩
    have h2 := hW _ hx
    rw [hmapN, LinearMap.mem_ker, hq', hT, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul] at h2
    exact h2
  · intro h x hx
    rw [hmapN, LinearMap.mem_ker] at hx ⊢
    obtain ⟨z, hz⟩ := (hex _).mp (show (N.toSubmodule.mkQ.baseChange B')
      ((AlgebraTensorModule.cancelBaseChange R B B' B' A).symm x) = 0 by rw [← hq']; exact hx)
    rw [hq', hT, ← hz, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.comp_apply,
      ← LinearMap.baseChange_comp]
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]
    | tmul b' m =>
        rw [LinearMap.baseChange_tmul, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply]
        have hm := h m m.2
        rw [show (b' ⊗ₜ[B] N.toSubmodule.mkQ (t.baseChange B (m : B ⊗[R] A))) =
            b' • ((1 : B') ⊗ₜ[B] N.toSubmodule.mkQ (t.baseChange B (m : B ⊗[R] A))) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], hm, smul_zero]
    | add u v hu hv => rw [map_add, hu, hv, add_zero]

theorem stable_map (t : A →ₗ[R] A) (N : Grassmannian B (B ⊗[R] A) k) (hN : Stable B t N) :
    Stable B' t (Grassmannian.map φ N) := by
  rw [stable_map_iff φ t N]
  intro n hn
  have h0 : N.toSubmodule.mkQ (t.baseChange B n) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hN _ hn
  rw [h0, TensorProduct.tmul_zero]

omit φ in

theorem stable_closed (t : A →ₗ[R] A) (N : Grassmannian B (B ⊗[R] A) k) :
    ∃ 𝔞 : Ideal B, ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'),
      Stable B' t (Grassmannian.map φ N) ↔ ∀ b ∈ 𝔞, φ b = 0 := by
  classical
  have hJ := fun (n : ↥N.toSubmodule) =>
    Module.Projective.exists_ideal_forall_tmul_eq_zero_iff_map_eq_bot B ((B ⊗[R] A) ⧸ N.toSubmodule)
      (N.toSubmodule.mkQ (t.baseChange B (n : B ⊗[R] A)))
  choose J hJ using hJ
  refine ⟨⨆ n, J n, fun B' _ _ φ => ?_⟩
  rw [stable_map_iff φ t N]
  constructor
  · intro h b hb
    have hle : (⨆ n, J n) ≤ RingHom.ker φ.toRingHom := by
      refine iSup_le fun n => ?_
      rw [← Ideal.map_eq_bot_iff_le_ker]
      exact (hJ n B' φ.toRingHom).mp (h n n.2)
    exact hle hb
  · intro h n hn
    have hb : Ideal.map φ.toRingHom (J ⟨n, hn⟩) = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker]
      exact le_trans (le_iSup (fun n => J n) ⟨n, hn⟩) (fun b hb => h b hb)
    exact (hJ ⟨n, hn⟩ B' φ.toRingHom).mpr hb

omit φ in

theorem closed_forall {ι : Type}
    (P : ι → ∀ (B' : Type) [CommRing B'] [Algebra R B'], (B →ₐ[R] B') → Prop)
    (h : ∀ i, ∃ 𝔞 : Ideal B, ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'),
      P i B' φ ↔ ∀ b ∈ 𝔞, φ b = 0) :
    ∃ 𝔞 : Ideal B, ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'),
      (∀ i, P i B' φ) ↔ ∀ b ∈ 𝔞, φ b = 0 := by
  classical
  choose J hJ using h
  refine ⟨⨆ i, J i, fun B' _ _ φ => ?_⟩
  constructor
  · intro hP b hb
    have hle : (⨆ i, J i) ≤ RingHom.ker φ.toRingHom :=
      iSup_le fun i => fun b hb => (hJ i B' φ).mp (hP i) b hb
    exact hle hb
  · intro hb i
    exact (hJ i B' φ).mpr fun b hb' => hb b (le_iSup J i hb')

theorem stable_family_closed {ι : Type} (t : ι → (A →ₗ[R] A)) (N : Grassmannian B (B ⊗[R] A) k) :
    ∃ 𝔞 : Ideal B, ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'),
      (∀ i, Stable B' (t i) (Grassmannian.map φ N)) ↔ ∀ b ∈ 𝔞, φ b = 0 :=
  closed_forall (fun i B' _ _ φ => Stable B' (t i) (Grassmannian.map φ N)) fun i => stable_closed (t i) N

end GrassClosed

namespace HilbFinAlg
open TensorProduct Module
section Alg
variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A] {k : ℕ}

def W (B : Type) [CommRing B] [Algebra R B] (N : Grassmannian B (B ⊗[R] A) k) : Prop :=
  ∀ (a x : B ⊗[R] A), x ∈ N.toSubmodule → a * x ∈ N.toSubmodule

noncomputable def mulA (B : Type) [CommRing B] [Algebra R B] (a : A) : B ⊗[R] A →ₗ[B] B ⊗[R] A :=
  LinearMap.mulLeft B ((1 : B) ⊗ₜ[R] a)

theorem mulA_apply (B : Type) [CommRing B] [Algebra R B] (a : A) (x : B ⊗[R] A) :
    mulA B a x = ((1 : B) ⊗ₜ[R] a) * x := rfl

variable {B B' : Type} [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (φ : B →ₐ[R] B')

theorem W_map_iff (N : Grassmannian B (B ⊗[R] A) k) :
    W B' (Grassmannian.map φ N) ↔
      ∀ (a : A) (n : B ⊗[R] A), n ∈ N.toSubmodule →
        (letI : Algebra B B' := φ.toAlgebra
         ((1 : B') ⊗ₜ[B] (N.toSubmodule.mkQ (((1 : B) ⊗ₜ[R] a) * n)) :
            B' ⊗[B] ((B ⊗[R] A) ⧸ N.toSubmodule)) = 0) := by
  letI : Algebra B B' := φ.toAlgebra
  letI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have hmapN : (Grassmannian.map φ N).toSubmodule =
      LinearMap.ker (Grassmannian.baseChangeMkQ B' N.toSubmodule) := Grassmannian.map_toSubmodule φ N

  have hq' : ∀ x : B' ⊗[R] A, Grassmannian.baseChangeMkQ B' N.toSubmodule x =
      (N.toSubmodule.mkQ.baseChange B') ((AlgebraTensorModule.cancelBaseChange R B B' B' A).symm x) :=
    fun x => rfl

  have hT : ∀ (a : A) (x : B' ⊗[R] A),
      (AlgebraTensorModule.cancelBaseChange R B B' B' A).symm (((1 : B') ⊗ₜ[R] a) * x) =
        (mulA B a).baseChange B' ((AlgebraTensorModule.cancelBaseChange R B B' B' A).symm x) := by
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b' a₀ =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, AlgebraTensorModule.cancelBaseChange_symm_tmul,
          AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul, mulA_apply,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]

  have hex : Function.Exact (N.toSubmodule.subtype.baseChange B') (N.toSubmodule.mkQ.baseChange B') := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact (M := ↥N.toSubmodule) (N := B ⊗[R] A) (P := (B ⊗[R] A) ⧸ N.toSubmodule) B'
      (LinearMap.exact_subtype_mkQ N.toSubmodule) (Submodule.mkQ_surjective _)
  constructor
  · intro hW a n hn
    have hx : (AlgebraTensorModule.cancelBaseChange R B B' B' A) ((1 : B') ⊗ₜ[B] n) ∈
        (Grassmannian.map φ N).toSubmodule := by
      rw [hmapN, LinearMap.mem_ker, hq', LinearEquiv.symm_apply_apply]
      exact (hex _).mpr ⟨(1 : B') ⊗ₜ[B] ⟨n, hn⟩, by rw [LinearMap.baseChange_tmul]; rfl⟩
    have h2 := hW ((1 : B') ⊗ₜ[R] a) _ hx
    rw [hmapN, LinearMap.mem_ker, hq', hT, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul,
      LinearMap.baseChange_tmul, mulA_apply] at h2
    exact h2
  · intro h a' x hx
    rw [hmapN, LinearMap.mem_ker] at hx ⊢

    have hone : ∀ a : A, Grassmannian.baseChangeMkQ B' N.toSubmodule (((1 : B') ⊗ₜ[R] a) * x) = 0 := by
      intro a
      obtain ⟨z, hz⟩ := (hex _).mp (show (N.toSubmodule.mkQ.baseChange B')
        ((AlgebraTensorModule.cancelBaseChange R B B' B' A).symm x) = 0 by rw [← hq']; exact hx)
      rw [hq', hT, ← hz, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.comp_apply,
        ← LinearMap.baseChange_comp]
      clear hz

      induction z using TensorProduct.induction_on with
      | zero => rw [map_zero]
      | tmul b' m =>
          rw [LinearMap.baseChange_tmul, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply]
          have hm := h a m m.2
          rw [show (b' ⊗ₜ[B] N.toSubmodule.mkQ (mulA B a (m : B ⊗[R] A))) =
              b' • ((1 : B') ⊗ₜ[B] N.toSubmodule.mkQ (mulA B a (m : B ⊗[R] A))) by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], mulA_apply, hm, smul_zero]
      | add u v hu hv => rw [map_add, hu, hv, add_zero]

    induction a' using TensorProduct.induction_on with
    | zero => rw [zero_mul, map_zero]
    | tmul b' a =>
        have hs : (b' ⊗ₜ[R] a) * x = b' • ((((1 : B') ⊗ₜ[R] a) * x)) := by
          rw [← smul_mul_assoc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hs, map_smul, hone a, smul_zero]
    | add u v hu hv => rw [add_mul, map_add, hu, hv, add_zero]

theorem W_map (N : Grassmannian B (B ⊗[R] A) k) (hN : W B N) : W B' (Grassmannian.map φ N) := by
  rw [W_map_iff φ N]
  intro a n hn
  have h0 : N.toSubmodule.mkQ (((1 : B) ⊗ₜ[R] a) * n) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hN _ _ hn
  rw [h0, TensorProduct.tmul_zero]

theorem W_closed (N : Grassmannian B (B ⊗[R] A) k) :
    ∃ 𝔞 : Ideal B, ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'),
      W B' (Grassmannian.map φ N) ↔ ∀ b ∈ 𝔞, φ b = 0 := by
  classical
  have hJ := fun (a : A) (n : ↥N.toSubmodule) =>
    Module.Projective.exists_ideal_forall_tmul_eq_zero_iff_map_eq_bot B ((B ⊗[R] A) ⧸ N.toSubmodule)
      (N.toSubmodule.mkQ (((1 : B) ⊗ₜ[R] a) * (n : B ⊗[R] A)))
  choose J hJ using hJ
  refine ⟨⨆ a, ⨆ n, J a n, fun B' _ _ φ => ?_⟩
  rw [W_map_iff φ N]
  constructor
  · intro h b hb
    have hle : (⨆ a, ⨆ n, J a n) ≤ RingHom.ker φ.toRingHom := by
      refine iSup_le fun a => iSup_le fun n => ?_
      rw [← Ideal.map_eq_bot_iff_le_ker]
      exact (hJ a n B' φ.toRingHom).mp (h a n n.2)
    exact hle hb
  · intro h a n hn
    have hb : Ideal.map φ.toRingHom (J a ⟨n, hn⟩) = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker]
      refine le_trans ?_ (show (⨆ a, ⨆ n, J a n) ≤ RingHom.ker φ.toRingHom from fun b hb => h b hb)
      exact le_trans (le_iSup (fun n => J a n) ⟨n, hn⟩) (le_iSup (fun a => ⨆ n, J a n) a)
    exact (hJ a ⟨n, hn⟩ B' φ.toRingHom).mpr hb

end Alg
end HilbFinAlg

namespace HopfHilb

open TensorProduct Module

section Engine

variable {R : Type} [CommRing R] {A : Type} [AddCommGroup A] [Module R A] {k : ℕ}
variable {B B' : Type} [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (φ : B →ₐ[R] B')

theorem forall_baseChange_eq_zero_iff {M : Type} [AddCommGroup M] [Module B M]
    (T : B ⊗[R] A →ₗ[B] M) (N : Grassmannian B (B ⊗[R] A) k) :
    letI : Algebra B B' := φ.toAlgebra
    letI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
    (∀ x : B' ⊗[R] A, x ∈ (Grassmannian.map φ N).toSubmodule →
        T.baseChange B' ((AlgebraTensorModule.cancelBaseChange R B B' B' A).symm x) = 0) ↔
      ∀ n : B ⊗[R] A, n ∈ N.toSubmodule → ((1 : B') ⊗ₜ[B] T n : B' ⊗[B] M) = 0 := by
  letI : Algebra B B' := φ.toAlgebra
  letI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have hmapN : (Grassmannian.map φ N).toSubmodule =
      LinearMap.ker (Grassmannian.baseChangeMkQ B' N.toSubmodule) := Grassmannian.map_toSubmodule φ N
  have hq' : ∀ x : B' ⊗[R] A, Grassmannian.baseChangeMkQ B' N.toSubmodule x =
      (N.toSubmodule.mkQ.baseChange B') ((AlgebraTensorModule.cancelBaseChange R B B' B' A).symm x) :=
    fun x => rfl
  have hex : Function.Exact (N.toSubmodule.subtype.baseChange B') (N.toSubmodule.mkQ.baseChange B') := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact (M := ↥N.toSubmodule) (N := B ⊗[R] A) (P := (B ⊗[R] A) ⧸ N.toSubmodule) B'
      (LinearMap.exact_subtype_mkQ N.toSubmodule) (Submodule.mkQ_surjective _)
  constructor
  · intro hW n hn
    have hx : (AlgebraTensorModule.cancelBaseChange R B B' B' A) ((1 : B') ⊗ₜ[B] n) ∈
        (Grassmannian.map φ N).toSubmodule := by
      rw [hmapN, LinearMap.mem_ker, hq', LinearEquiv.symm_apply_apply]
      exact (hex _).mpr ⟨(1 : B') ⊗ₜ[B] ⟨n, hn⟩, by rw [LinearMap.baseChange_tmul]; rfl⟩
    have h2 := hW _ hx
    rw [LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul] at h2
    exact h2
  · intro h x hx
    rw [hmapN, LinearMap.mem_ker] at hx
    obtain ⟨z, hz⟩ := (hex _).mp (show (N.toSubmodule.mkQ.baseChange B')
      ((AlgebraTensorModule.cancelBaseChange R B B' B' A).symm x) = 0 by rw [← hq']; exact hx)
    rw [← hz, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]
    | tmul b' m =>
        rw [LinearMap.baseChange_tmul, LinearMap.comp_apply, Submodule.subtype_apply]
        have hm := h m m.2
        rw [show (b' ⊗ₜ[B] T (m : B ⊗[R] A)) = b' • ((1 : B') ⊗ₜ[B] T (m : B ⊗[R] A)) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], hm, smul_zero]
    | add u v hu hv => rw [map_add, hu, hv, add_zero]

omit φ in

theorem closed_of_engine {M : Type} [AddCommGroup M] [Module B M] [Module.Finite B M] [Module.Projective B M]
    (T : B ⊗[R] A →ₗ[B] M) (N : Grassmannian B (B ⊗[R] A) k)
    (P : ∀ (B' : Type) [CommRing B'] [Algebra R B'], (B →ₐ[R] B') → Prop)
    (hP : ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'),
      P B' φ ↔ ∀ n : B ⊗[R] A, n ∈ N.toSubmodule →
        (letI : Algebra B B' := φ.toAlgebra; ((1 : B') ⊗ₜ[B] T n : B' ⊗[B] M) = 0)) :
    ∃ 𝔞 : Ideal B, ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'),
      P B' φ ↔ ∀ b ∈ 𝔞, φ b = 0 := by
  classical
  have hJ := fun (n : ↥N.toSubmodule) =>
    Module.Projective.exists_ideal_forall_tmul_eq_zero_iff_map_eq_bot B M (T (n : B ⊗[R] A))
  choose J hJ using hJ
  refine ⟨⨆ n, J n, fun B' _ _ φ => ?_⟩
  rw [hP B' φ]
  constructor
  · intro h b hb
    have hle : (⨆ n, J n) ≤ RingHom.ker φ.toRingHom := by
      refine iSup_le fun n => ?_
      rw [← Ideal.map_eq_bot_iff_le_ker]
      exact (hJ n B' φ.toRingHom).mp (h n n.2)
    exact hle hb
  · intro h n hn
    have hb : Ideal.map φ.toRingHom (J ⟨n, hn⟩) = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker]
      exact le_trans (le_iSup (fun n => J n) ⟨n, hn⟩) (fun b hb => h b hb)
    exact (hJ ⟨n, hn⟩ B' φ.toRingHom).mpr hb

omit φ in

theorem closed_of_engine_base (T : B ⊗[R] A →ₗ[B] B) (N : Grassmannian B (B ⊗[R] A) k)
    (P : ∀ (B' : Type) [CommRing B'] [Algebra R B'], (B →ₐ[R] B') → Prop)
    (hP : ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'),
      P B' φ ↔ ∀ n : B ⊗[R] A, n ∈ N.toSubmodule →
        (letI : Algebra B B' := φ.toAlgebra; ((1 : B') ⊗ₜ[B] T n : B' ⊗[B] B) = 0)) :
    ∃ 𝔞 : Ideal B, ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'),
      P B' φ ↔ ∀ b ∈ 𝔞, φ b = 0 := by
  refine ⟨Ideal.span (Set.range fun n : ↥N.toSubmodule => T (n : B ⊗[R] A)), fun B' _ _ φ => ?_⟩
  letI : Algebra B B' := φ.toAlgebra
  rw [hP B' φ]

  have key : ∀ c : B, ((1 : B') ⊗ₜ[B] c : B' ⊗[B] B) = 0 ↔ φ c = 0 := by
    intro c
    constructor
    · intro h
      have := congrArg (AlgebraTensorModule.rid B B' B') h
      rw [map_zero, AlgebraTensorModule.rid_tmul] at this
      rw [Algebra.smul_def, mul_one] at this
      exact this
    · intro h
      have : ((1 : B') ⊗ₜ[B] c : B' ⊗[B] B) = (c • (1 : B')) ⊗ₜ[B] (1 : B) := by
        rw [TensorProduct.smul_tmul, smul_eq_mul, mul_one]
      rw [this, Algebra.smul_def, mul_one, show (algebraMap B B') c = φ c from rfl, h, TensorProduct.zero_tmul]
  simp_rw [key]
  constructor
  · intro h b hb
    refine Submodule.span_induction (p := fun b _ => φ b = 0) ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨n, rfl⟩; exact h n n.2
    · exact map_zero φ
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro a x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero]
  · intro h n hn
    exact h _ (Ideal.subset_span ⟨⟨n, hn⟩, rfl⟩)

end Engine

end HopfHilb

namespace HopfHilb

open TensorProduct Module

section Hopf

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [HopfAlgebra R A] {k : ℕ}

def Weps (B : Type) [CommRing B] [Algebra R B] (N : Grassmannian B (B ⊗[R] A) k) : Prop :=
  ∀ n : B ⊗[R] A, n ∈ N.toSubmodule → Coalgebra.counit (R := B) (A := B ⊗[R] A) n = 0

def Wdelta (B : Type) [CommRing B] [Algebra R B] (N : Grassmannian B (B ⊗[R] A) k) : Prop :=
  ∀ n : B ⊗[R] A, n ∈ N.toSubmodule →
    TensorProduct.map N.toSubmodule.mkQ N.toSubmodule.mkQ (Coalgebra.comul (R := B) (A := B ⊗[R] A) n) = 0

theorem antipode_eq_baseChange (B : Type) [CommRing B] [Algebra R B] :
    HopfAlgebra.antipode B (A := B ⊗[R] A) = (HopfAlgebra.antipode R (A := A)).baseChange B := rfl

variable {B B' : Type} [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (φ : B →ₐ[R] B')

theorem counit_tmul' (b : B) (a : A) :
    Coalgebra.counit (R := B) (A := B ⊗[R] A) (b ⊗ₜ[R] a) = Coalgebra.counit (R := R) a • b := by
  rw [TensorProduct.counit_tmul]
  rfl

theorem counit_cancelBaseChange
    [Algebra B B'] [IsScalarTower R B B'] (w : B' ⊗[B] (B ⊗[R] A)) :
    Coalgebra.counit (R := B') (A := B' ⊗[R] A) (AlgebraTensorModule.cancelBaseChange R B B' B' A w) =
      AlgebraTensorModule.rid B B' B' ((Coalgebra.counit (R := B) (A := B ⊗[R] A)).baseChange B' w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul b' y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b a =>
          rw [AlgebraTensorModule.cancelBaseChange_tmul, counit_tmul', LinearMap.baseChange_tmul, counit_tmul',
            AlgebraTensorModule.rid_tmul, smul_assoc]
      | add u v hu hv => simp only [tmul_add, map_add, hu, hv]
  | add u v hu hv => simp only [map_add, hu, hv]

theorem Weps_map_iff (N : Grassmannian B (B ⊗[R] A) k) :
    Weps B' (Grassmannian.map φ N) ↔ ∀ n : B ⊗[R] A, n ∈ N.toSubmodule →
      (letI : Algebra B B' := φ.toAlgebra;
       ((1 : B') ⊗ₜ[B] Coalgebra.counit (R := B) (A := B ⊗[R] A) n : B' ⊗[B] B) = 0) := by
  letI : Algebra B B' := φ.toAlgebra
  letI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  rw [← forall_baseChange_eq_zero_iff φ (Coalgebra.counit (R := B) (A := B ⊗[R] A)) N]
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  have h := counit_cancelBaseChange (R := R) (A := A) (B := B) (B' := B')
    ((AlgebraTensorModule.cancelBaseChange R B B' B' A).symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [show Coalgebra.counit (R := B') (A := B' ⊗[R] A) x = _ from h]
  exact (AlgebraTensorModule.rid B B' B').map_eq_zero_iff

theorem Weps_map (N : Grassmannian B (B ⊗[R] A) k) (h : Weps B N) : Weps B' (Grassmannian.map φ N) := by
  rw [Weps_map_iff φ N]
  intro n hn
  rw [h n hn, TensorProduct.tmul_zero]

omit φ in
theorem Weps_closed (N : Grassmannian B (B ⊗[R] A) k) :
    ∃ 𝔞 : Ideal B, ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'),
      Weps B' (Grassmannian.map φ N) ↔ ∀ b ∈ 𝔞, φ b = 0 :=
  closed_of_engine_base (Coalgebra.counit (R := B) (A := B ⊗[R] A)) N
    (fun B' _ _ φ => Weps B' (Grassmannian.map φ N)) (fun B' _ _ φ => Weps_map_iff φ N)

end Hopf

end HopfHilb

namespace HopfHilb

p2m_open "TensorProduct Module Coalgebra CategoryTheory.Coalgebra"

section Comul

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [HopfAlgebra R A] {k : ℕ}
variable {B B' : Type} [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']

theorem comul_one_tmul (B : Type) [CommRing B] [Algebra R B] (a : A) {ιρ : Type*} (ρ : Coalgebra.Repr R a ιρ) :
    Coalgebra.comul (R := B) (A := B ⊗[R] A) ((1 : B) ⊗ₜ[R] a) =
      ∑ i ∈ ρ.index, ((1 : B) ⊗ₜ[R] ρ.left i) ⊗ₜ[B] ((1 : B) ⊗ₜ[R] ρ.right i) := by
  rw [TensorProduct.comul_tmul, ← ρ.eq, tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show Coalgebra.comul (R := B) (A := B) (1 : B) = (1 : B) ⊗ₜ[B] (1 : B) from rfl,
    AlgebraTensorModule.tensorTensorTensorComm_tmul]

theorem comul_tmul_repr (b' : B') (a : A) {ιρ : Type*} (ρ : Coalgebra.Repr R a ιρ) :
    Coalgebra.comul (R := B') (A := B' ⊗[R] A) (b' ⊗ₜ[R] a) =
      ∑ i ∈ ρ.index, ((1 : B') ⊗ₜ[R] ρ.left i) ⊗ₜ[B'] (b' ⊗ₜ[R] ρ.right i) := by
  rw [TensorProduct.comul_tmul, ← ρ.eq, tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show Coalgebra.comul (R := B') (A := B') b' = (1 : B') ⊗ₜ[B'] b' from rfl,
    AlgebraTensorModule.tensorTensorTensorComm_tmul]

variable (N : Grassmannian B (B ⊗[R] A) k)

theorem baseChangeMkQEquiv_symm_mk (x : B' ⊗[R] A) :
    Grassmannian.baseChangeMkQEquiv (B := B') N.toSubmodule (Submodule.Quotient.mk x) =
      N.toSubmodule.mkQ.baseChange B' ((AlgebraTensorModule.cancelBaseChange R B B' B' A).symm x) :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

theorem baseChangeMkQEquiv_symm_tmul (b' : B') (y : B ⊗[R] A) :
    (Grassmannian.baseChangeMkQEquiv (B := B') N.toSubmodule).symm (b' ⊗ₜ[B] N.toSubmodule.mkQ y) =
      Submodule.Quotient.mk (AlgebraTensorModule.cancelBaseChange R B B' B' A (b' ⊗ₜ[B] y)) := by
  rw [LinearEquiv.symm_apply_eq, baseChangeMkQEquiv_symm_mk, LinearEquiv.symm_apply_apply,
    LinearMap.baseChange_tmul]

noncomputable def Theta :
    B' ⊗[B] (((B ⊗[R] A) ⧸ N.toSubmodule) ⊗[B] ((B ⊗[R] A) ⧸ N.toSubmodule)) ≃ₗ[B']
      ((B' ⊗[R] A) ⧸ LinearMap.ker (Grassmannian.baseChangeMkQ B' N.toSubmodule)) ⊗[B']
        ((B' ⊗[R] A) ⧸ LinearMap.ker (Grassmannian.baseChangeMkQ B' N.toSubmodule)) :=
  AlgebraTensorModule.distribBaseChange B B' _ _ ≪≫ₗ
    TensorProduct.congr (Grassmannian.baseChangeMkQEquiv (B := B') N.toSubmodule).symm
      (Grassmannian.baseChangeMkQEquiv (B := B') N.toSubmodule).symm

noncomputable def delta (B : Type) [CommRing B] [Algebra R B] (N : Grassmannian B (B ⊗[R] A) k) :
    B ⊗[R] A →ₗ[B] ((B ⊗[R] A) ⧸ N.toSubmodule) ⊗[B] ((B ⊗[R] A) ⧸ N.toSubmodule) :=
  TensorProduct.map N.toSubmodule.mkQ N.toSubmodule.mkQ ∘ₗ Coalgebra.comul (R := B) (A := B ⊗[R] A)

set_option maxHeartbeats 4000000 in

theorem map_mkQ_comul_eq_Theta (x : B' ⊗[R] A) :
    TensorProduct.map (LinearMap.ker (Grassmannian.baseChangeMkQ B' N.toSubmodule)).mkQ
        (LinearMap.ker (Grassmannian.baseChangeMkQ B' N.toSubmodule)).mkQ
        (Coalgebra.comul (R := B') (A := B' ⊗[R] A) x) =
      Theta N ((delta B N).baseChange B' ((AlgebraTensorModule.cancelBaseChange R B B' B' A).symm x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul b' a =>
      let ρ := Coalgebra.Repr.arbitrary R a
      rw [comul_tmul_repr b' a ρ, map_sum, AlgebraTensorModule.cancelBaseChange_symm_tmul,
        LinearMap.baseChange_tmul]
      rw [show delta B N ((1 : B) ⊗ₜ[R] a) = _ from by
        rw [delta, LinearMap.comp_apply, comul_one_tmul B a ρ, map_sum]]
      rw [tmul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul, Theta, LinearEquiv.trans_apply,
        AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.congr_tmul,
        baseChangeMkQEquiv_symm_tmul, baseChangeMkQEquiv_symm_tmul,
        AlgebraTensorModule.cancelBaseChange_tmul, AlgebraTensorModule.cancelBaseChange_tmul, one_smul, one_smul]

      rw [show (b' ⊗ₜ[R] ρ.right i : B' ⊗[R] A) = b' • ((1 : B') ⊗ₜ[R] ρ.right i) by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        show (b' ⊗ₜ[R] ρ.left i : B' ⊗[R] A) = b' • ((1 : B') ⊗ₜ[R] ρ.left i) by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']

end Comul

end HopfHilb

namespace HopfHilb

open TensorProduct Module

section Closed

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [HopfAlgebra R A] {k : ℕ}
variable {B B' : Type} [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (φ : B →ₐ[R] B')

theorem Wdelta_map_iff (N : Grassmannian B (B ⊗[R] A) k) :
    Wdelta B' (Grassmannian.map φ N) ↔ ∀ n : B ⊗[R] A, n ∈ N.toSubmodule →
      (letI : Algebra B B' := φ.toAlgebra; ((1 : B') ⊗ₜ[B] delta B N n :
        B' ⊗[B] (((B ⊗[R] A) ⧸ N.toSubmodule) ⊗[B] ((B ⊗[R] A) ⧸ N.toSubmodule))) = 0) := by
  letI : Algebra B B' := φ.toAlgebra
  letI : IsScalarTower R B B' := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  rw [← forall_baseChange_eq_zero_iff φ (delta B N) N]
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  rw [← (Theta (B' := B') N).map_eq_zero_iff, ← map_mkQ_comul_eq_Theta N x]
  exact Iff.rfl

theorem Wdelta_map (N : Grassmannian B (B ⊗[R] A) k) (h : Wdelta B N) : Wdelta B' (Grassmannian.map φ N) := by
  rw [Wdelta_map_iff φ N]
  intro n hn
  have : delta B N n = 0 := by rw [delta, LinearMap.comp_apply]; exact h n hn
  rw [this, TensorProduct.tmul_zero]

omit φ in
theorem Wdelta_closed (N : Grassmannian B (B ⊗[R] A) k) :
    ∃ 𝔞 : Ideal B, ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'),
      Wdelta B' (Grassmannian.map φ N) ↔ ∀ b ∈ 𝔞, φ b = 0 :=
  closed_of_engine (delta B N) N (fun B' _ _ φ => Wdelta B' (Grassmannian.map φ N)) (fun B' _ _ φ => Wdelta_map_iff φ N)

omit φ in

theorem closed_and (P Q : ∀ (B' : Type) [CommRing B'] [Algebra R B'], (B →ₐ[R] B') → Prop)
    (hP : ∃ 𝔞 : Ideal B, ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'), P B' φ ↔ ∀ b ∈ 𝔞, φ b = 0)
    (hQ : ∃ 𝔞 : Ideal B, ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'), Q B' φ ↔ ∀ b ∈ 𝔞, φ b = 0) :
    ∃ 𝔞 : Ideal B, ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'),
      (P B' φ ∧ Q B' φ) ↔ ∀ b ∈ 𝔞, φ b = 0 := by
  obtain ⟨𝔞, h𝔞⟩ := hP
  obtain ⟨𝔟, h𝔟⟩ := hQ
  refine ⟨𝔞 ⊔ 𝔟, fun B' _ _ φ => ?_⟩
  rw [h𝔞 B' φ, h𝔟 B' φ]
  constructor
  · rintro ⟨h1, h2⟩ b hb
    have hle : 𝔞 ⊔ 𝔟 ≤ RingHom.ker φ.toRingHom := sup_le (fun b hb => h1 b hb) (fun b hb => h2 b hb)
    exact hle hb
  · intro h
    exact ⟨fun b hb => h b (Ideal.mem_sup_left hb), fun b hb => h b (Ideal.mem_sup_right hb)⟩

omit φ in

theorem closed_congr (P Q : ∀ (B' : Type) [CommRing B'] [Algebra R B'], (B →ₐ[R] B') → Prop)
    (hPQ : ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'), P B' φ ↔ Q B' φ)
    (hQ : ∃ 𝔞 : Ideal B, ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'), Q B' φ ↔ ∀ b ∈ 𝔞, φ b = 0) :
    ∃ 𝔞 : Ideal B, ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'), P B' φ ↔ ∀ b ∈ 𝔞, φ b = 0 := by
  obtain ⟨𝔞, h⟩ := hQ
  exact ⟨𝔞, fun B' _ _ φ => (hPQ B' φ).trans (h B' φ)⟩

end Closed

section IsHopfIdealIff

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [HopfAlgebra R A] {k : ℕ}

def idealOf {B : Type} [CommRing B] [Algebra R B] (N : Grassmannian B (B ⊗[R] A) k)
    (hN : ∀ (a x : B ⊗[R] A), x ∈ N.toSubmodule → a * x ∈ N.toSubmodule) : Ideal (B ⊗[R] A) where
  carrier := N.toSubmodule
  add_mem' := fun hx hy => N.toSubmodule.add_mem hx hy
  zero_mem' := N.toSubmodule.zero_mem
  smul_mem' := fun a x hx => hN a x hx

theorem span_eq_idealOf {B : Type} [CommRing B] [Algebra R B] (N : Grassmannian B (B ⊗[R] A) k)
    (hN : ∀ (a x : B ⊗[R] A), x ∈ N.toSubmodule → a * x ∈ N.toSubmodule) :
    Ideal.span (N.toSubmodule : Set (B ⊗[R] A)) = idealOf N hN :=
  le_antisymm (Ideal.span_le.mpr fun x hx => hx) fun x hx => Ideal.subset_span hx

theorem mem_span_iff {B : Type} [CommRing B] [Algebra R B] (N : Grassmannian B (B ⊗[R] A) k)
    (hN : ∀ (a x : B ⊗[R] A), x ∈ N.toSubmodule → a * x ∈ N.toSubmodule) (x : B ⊗[R] A) :
    x ∈ Ideal.span (N.toSubmodule : Set (B ⊗[R] A)) ↔ x ∈ N.toSubmodule := by
  rw [span_eq_idealOf N hN]; exact Iff.rfl

theorem isHopfIdeal_span_iff (B : Type) [CommRing B] [Algebra R B] (N : Grassmannian B (B ⊗[R] A) k)
    (hN : ∀ (a x : B ⊗[R] A), x ∈ N.toSubmodule → a * x ∈ N.toSubmodule) :
    (Ideal.span (N.toSubmodule : Set (B ⊗[R] A))).IsHopfIdeal' B ↔
      Weps B N ∧ Wdelta B N ∧
        ∀ n : B ⊗[R] A, n ∈ N.toSubmodule →
          (HopfAlgebra.antipode R (A := A)).baseChange B n ∈ N.toSubmodule := by

  set I : Ideal (B ⊗[R] A) := Ideal.span (N.toSubmodule : Set (B ⊗[R] A)) with hI
  have hmem : ∀ x, x ∈ I ↔ x ∈ N.toSubmodule := fun x => by rw [hI]; exact mem_span_iff N hN x
  have hres : I.restrictScalars B = N.toSubmodule := by
    ext x; rw [Submodule.restrictScalars_mem]; exact hmem x
  let E : ((B ⊗[R] A) ⧸ I) ≃ₗ[B] ((B ⊗[R] A) ⧸ N.toSubmodule) :=
    (Submodule.Quotient.restrictScalarsEquiv B I).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hres
  have hE : ∀ x : B ⊗[R] A, E (Ideal.Quotient.mkₐ B I x) = N.toSubmodule.mkQ x := by
    intro x
    show ((Submodule.Quotient.restrictScalarsEquiv B I).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hres)
        (Submodule.Quotient.mk x) = Submodule.Quotient.mk x
    rw [LinearEquiv.trans_apply, Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.quotEquivOfEq_mk]
  have hcongr : ∀ z : (B ⊗[R] A) ⊗[B] (B ⊗[R] A),
      TensorProduct.congr E E (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ B I) (Ideal.Quotient.mkₐ B I) z) =
        TensorProduct.map N.toSubmodule.mkQ N.toSubmodule.mkQ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, LinearEquiv.map_zero, map_zero]
    | tmul x y => rw [Algebra.TensorProduct.map_tmul, TensorProduct.congr_tmul, hE, hE, TensorProduct.map_tmul]
    | add u v hu hv => rw [map_add, LinearEquiv.map_add, map_add, hu, hv]
  have hdelta : ∀ n : B ⊗[R] A,
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ B I) (Ideal.Quotient.mkₐ B I)
          (Coalgebra.comul (R := B) (A := B ⊗[R] A) n) = 0 ↔
        TensorProduct.map N.toSubmodule.mkQ N.toSubmodule.mkQ (Coalgebra.comul (R := B) (A := B ⊗[R] A) n) = 0 := by
    intro n
    rw [← hcongr, LinearEquiv.map_eq_zero_iff]
  constructor
  · intro h
    refine ⟨fun n hn => h.counit_eq_zero n ((hmem n).mpr hn),
      fun n hn => (hdelta n).mp (h.map_mkₐ_comul_eq_zero n ((hmem n).mpr hn)), fun n hn => ?_⟩
    rw [← antipode_eq_baseChange]
    exact (hmem _).mp (h.antipode_mem n ((hmem n).mpr hn))
  · rintro ⟨h1, h2, h3⟩
    exact
      { map_mkₐ_comul_eq_zero := fun x hx => (hdelta x).mpr (h2 x ((hmem x).mp hx))
        counit_eq_zero := fun x hx => h1 x ((hmem x).mp hx)
        antipode_mem := fun x hx => by
          rw [antipode_eq_baseChange]
          exact (hmem _).mpr (h3 x ((hmem x).mp hx)) }

end IsHopfIdealIff

section Wall

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [HopfAlgebra R A] {k : ℕ}
variable {ι : Type} (σ : ι → (A →ₐ[R] A))

def Wall (B : Type) [CommRing B] [Algebra R B] (N : Grassmannian B (B ⊗[R] A) k) : Prop :=
  (∀ (a x : B ⊗[R] A), x ∈ N.toSubmodule → a * x ∈ N.toSubmodule) ∧
  (Ideal.span (N.toSubmodule : Set (B ⊗[R] A))).IsHopfIdeal' B ∧
  ∀ (i : ι) (x : B ⊗[R] A), x ∈ N.toSubmodule → (σ i).toLinearMap.baseChange B x ∈ N.toSubmodule

def Wall' (B : Type) [CommRing B] [Algebra R B] (N : Grassmannian B (B ⊗[R] A) k) : Prop :=
  HilbFinAlg.W B N ∧
  (Weps B N ∧ Wdelta B N ∧ GrassClosed.Stable B (HopfAlgebra.antipode R (A := A)) N) ∧
  ∀ i : ι, GrassClosed.Stable B (σ i).toLinearMap N

theorem wall_iff (B : Type) [CommRing B] [Algebra R B] (N : Grassmannian B (B ⊗[R] A) k) :
    Wall σ B N ↔ Wall' σ B N := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, (isHopfIdeal_span_iff B N h1).mp h2, fun i x hx => h3 i x hx⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, (isHopfIdeal_span_iff B N h1).mpr h2, fun i x hx => h3 i x hx⟩

variable {B B' : Type} [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (φ : B →ₐ[R] B')

theorem wall'_map (N : Grassmannian B (B ⊗[R] A) k) (h : Wall' σ B N) : Wall' σ B' (Grassmannian.map φ N) := by
  obtain ⟨h1, ⟨h2, h3, h4⟩, h5⟩ := h
  exact ⟨HilbFinAlg.W_map φ N h1, ⟨Weps_map φ N h2, Wdelta_map φ N h3, GrassClosed.stable_map φ _ N h4⟩,
    fun i => GrassClosed.stable_map φ _ N (h5 i)⟩

theorem wall_map (N : Grassmannian B (B ⊗[R] A) k) (h : Wall σ B N) : Wall σ B' (Grassmannian.map φ N) :=
  (wall_iff σ B' _).mpr (wall'_map σ φ N ((wall_iff σ B N).mp h))

omit φ in
theorem wall_closed (N : Grassmannian B (B ⊗[R] A) k) :
    ∃ 𝔞 : Ideal B, ∀ (B' : Type) [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B'),
      Wall σ B' (Grassmannian.map φ N) ↔ ∀ b ∈ 𝔞, φ b = 0 := by
  refine closed_congr (fun B' _ _ φ => Wall σ B' (Grassmannian.map φ N))
    (fun B' _ _ φ => Wall' σ B' (Grassmannian.map φ N)) (fun B' _ _ φ => wall_iff σ B' _) ?_
  refine closed_and _ _ (HilbFinAlg.W_closed N) (closed_and _ _ (closed_and _ _ (Weps_closed N)
    (closed_and _ _ (Wdelta_closed N) (GrassClosed.stable_closed _ N))) ?_)
  exact GrassClosed.stable_family_closed (fun i => (σ i).toLinearMap) N

end Wall

end HopfHilb

open HopfHilb in
theorem solution
    (R : Type) [CommRing R] (A : Type) [CommRing A] [HopfAlgebra R A] [Module.Finite R A]
    (ι : Type) (σ : ι → (A →ₐ[R] A)) (k : ℕ) :
    ∃ (H : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of R))
      (pt : ∀ (B : Type) [CommRing B] [Algebra R B],
        {N : Module.Grassmannian B (B ⊗[R] A) k //
            (∀ (a x : B ⊗[R] A), x ∈ N.toSubmodule → a * x ∈ N.toSubmodule) ∧
            (Ideal.span (N.toSubmodule : Set (B ⊗[R] A))).IsHopfIdeal' B ∧
            ∀ (i : ι) (x : B ⊗[R] A), x ∈ N.toSubmodule →
              (σ i).toLinearMap.baseChange B x ∈ N.toSubmodule} ≃
          {g : Spec (CommRingCat.of B) ⟶ H // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R B))})
      (hmap : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (φ : B →ₐ[R] B')
          (N : {N : Module.Grassmannian B (B ⊗[R] A) k //
            (∀ (a x : B ⊗[R] A), x ∈ N.toSubmodule → a * x ∈ N.toSubmodule) ∧
            (Ideal.span (N.toSubmodule : Set (B ⊗[R] A))).IsHopfIdeal' B ∧
            ∀ (i : ι) (x : B ⊗[R] A), x ∈ N.toSubmodule →
              (σ i).toLinearMap.baseChange B x ∈ N.toSubmodule}),
          (∀ (a x : B' ⊗[R] A), x ∈ (Module.Grassmannian.map φ N.1).toSubmodule →
              a * x ∈ (Module.Grassmannian.map φ N.1).toSubmodule) ∧
          (Ideal.span ((Module.Grassmannian.map φ N.1).toSubmodule : Set (B' ⊗[R] A))).IsHopfIdeal' B' ∧
          ∀ (i : ι) (x : B' ⊗[R] A), x ∈ (Module.Grassmannian.map φ N.1).toSubmodule →
            (σ i).toLinearMap.baseChange B' x ∈ (Module.Grassmannian.map φ N.1).toSubmodule),
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (φ : B →ₐ[R] B')
          (N : {N : Module.Grassmannian B (B ⊗[R] A) k //
            (∀ (a x : B ⊗[R] A), x ∈ N.toSubmodule → a * x ∈ N.toSubmodule) ∧
            (Ideal.span (N.toSubmodule : Set (B ⊗[R] A))).IsHopfIdeal' B ∧
            ∀ (i : ι) (x : B ⊗[R] A), x ∈ N.toSubmodule →
              (σ i).toLinearMap.baseChange B x ∈ N.toSubmodule}),
        (pt B' ⟨Module.Grassmannian.map φ N.1, hmap B B' φ N⟩).1 =
          Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt B N).1) ∧
      ∃ (m : ℕ) (ιP : H ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) R)),
        IsClosedImmersion ιP ∧ ιP ≫ ProjSpace.π R m = p := by
  classical
  obtain ⟨Gr, pG, ptG, natG, m, ιG, hιG, hcompG⟩ :=
    Module.Grassmannian.exists_scheme_represents_and_isClosedImmersion_toProjSpace R A k
  obtain ⟨Z, ιZ, ptZ, hιZ, hcompat⟩ :=
    AlgebraicGeometry.Scheme.exists_isClosedImmersion_represents_of_forall_exists_ideal R
      (fun B _ _ => Module.Grassmannian B (B ⊗[R] A) k)
      (fun B B' _ _ _ _ φ N => Module.Grassmannian.map φ N)
      Gr pG ptG natG
      (fun B _ _ N => Wall σ B N)
      (fun B _ _ N => wall_closed σ N)
  refine ⟨Z, ιZ ≫ pG, ptZ, fun B B' _ _ _ _ φ N => wall_map σ φ N.1 N.2, ?_, m, ιZ ≫ ιG, ?_, ?_⟩
  · intro B B' _ _ _ _ φ N
    haveI : IsClosedImmersion ιZ := hιZ
    rw [← cancel_mono ιZ, Category.assoc]
    exact (hcompat B' ⟨_, wall_map σ φ N.1 N.2⟩).trans ((natG B B' φ N.1).trans
      (congrArg (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ·) (hcompat B N).symm))
  · haveI : IsClosedImmersion ιZ := hιZ
    haveI : IsClosedImmersion ιG := hιG
    infer_instance
  · rw [Category.assoc, hcompG]

end S_Module_Grassmannian_exists_scheme_represents_isHopfIdeal_and_isClosedImmersion_toProjSpace
end P2MW
export P2MW.S_Module_Grassmannian_exists_scheme_represents_isHopfIdeal_and_isClosedImmersion_toProjSpace (solution)
