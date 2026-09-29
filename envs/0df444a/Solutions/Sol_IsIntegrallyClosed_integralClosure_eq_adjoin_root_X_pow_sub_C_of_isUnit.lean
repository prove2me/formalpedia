-- Prove2me | solution 1 for IsIntegrallyClosed.integralClosure_eq_adjoin_root_X_pow_sub_C_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2f98273a-122a-5f71-85cf-719c47e72ced

import Mathlib
import Theorems.Thm_AdjoinRoot_etale_and_finite_X_pow_sub_C_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsIntegrallyClosed_integralClosure_eq_adjoin_root_X_pow_sub_C_of_isUnit

set_option autoImplicit false

open Polynomial TensorProduct

namespace KummerIntegralClosureKa

variable {A K : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field K] [Algebra A K] [IsFractionRing A K]

theorem mem_range_includeLeft_of_isIntegral {S : Type*} [CommRing S] [Algebra A S] [Algebra.Smooth A S]
    (y : S ⊗[A] K) (hy : IsIntegral S y) :
    y ∈ (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] K).range := by
  obtain ⟨z, hz⟩ :=
    (TensorProduct.toIntegralClosure_bijective_of_smooth (R := A) (S := S) (B := K)).2 ⟨y, hy⟩
  have hz' : ((TensorProduct.toIntegralClosure A S K z : integralClosure S (S ⊗[A] K)) : S ⊗[A] K) = y := by
    rw [hz]
  rw [← hz']
  clear hz hz' hy y
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s a =>
      obtain ⟨a, ha⟩ := a
      have ha' : a ∈ integralClosure A K := ha
      rw [IsIntegrallyClosed.integralClosure_eq_bot A K, Algebra.mem_bot] at ha'
      obtain ⟨a₀, rfl⟩ := ha'
      refine ⟨a₀ • s, ?_⟩
      simp only [TensorProduct.toIntegralClosure, AlgHom.coe_codRestrict, Algebra.TensorProduct.map_tmul,
        AlgHom.coe_id, id_eq, Subalgebra.coe_val]
      rw [Algebra.TensorProduct.includeLeftRingHom_apply, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
      rw [map_add, Subalgebra.coe_add]
      exact add_mem hx hy

variable (K)

noncomputable abbrev fA (n : ℕ) (u : A) : A[X] := X ^ n - C u

noncomputable abbrev fK (n : ℕ) (u : A) : K[X] := X ^ n - C (algebraMap A K u)

variable {K}

theorem root_fK_pow (n : ℕ) (u : A) :
    (AdjoinRoot.root (fK K n u)) ^ n = algebraMap A (AdjoinRoot (fK K n u)) u := by
  have h := AdjoinRoot.eval₂_root (fK K n u)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [sub_eq_zero] at h
  rw [h, IsScalarTower.algebraMap_apply A K (AdjoinRoot (fK K n u))]
  rfl

theorem root_fA_pow (n : ℕ) (u : A) :
    (AdjoinRoot.root (fA n u)) ^ n = algebraMap A (AdjoinRoot (fA n u)) u := by
  have h := AdjoinRoot.eval₂_root (fA n u)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [sub_eq_zero] at h
  rw [h]
  rfl

noncomputable def ψ₁ (n : ℕ) (u : A) : AdjoinRoot (fA n u) →ₐ[A] AdjoinRoot (fK K n u) :=
  AdjoinRoot.liftAlgHom (fA n u) (Algebra.ofId A (AdjoinRoot (fK K n u))) (AdjoinRoot.root (fK K n u)) (by
    change (fA n u).eval₂ (algebraMap A (AdjoinRoot (fK K n u))) (AdjoinRoot.root (fK K n u)) = 0
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, root_fK_pow, sub_self])

theorem ψ₁_root (n : ℕ) (u : A) : ψ₁ (K := K) n u (AdjoinRoot.root (fA n u)) = AdjoinRoot.root (fK K n u) := by
  simp [ψ₁]

noncomputable def ψ (n : ℕ) (u : A) : AdjoinRoot (fA n u) ⊗[A] K →ₐ[A] AdjoinRoot (fK K n u) :=
  Algebra.TensorProduct.lift (ψ₁ n u) (IsScalarTower.toAlgHom A K (AdjoinRoot (fK K n u)))
    (fun _ _ => Commute.all _ _)

theorem ψ_tmul (n : ℕ) (u : A) (s : AdjoinRoot (fA n u)) (k : K) :
    ψ n u (s ⊗ₜ[A] k) = ψ₁ n u s * algebraMap K (AdjoinRoot (fK K n u)) k := by
  simp [ψ]

noncomputable def θ (n : ℕ) (u : A) : AdjoinRoot (fK K n u) →+* AdjoinRoot (fA n u) ⊗[A] K :=
  AdjoinRoot.lift
    ((Algebra.TensorProduct.includeRight : K →ₐ[A] AdjoinRoot (fA n u) ⊗[A] K).toRingHom)
    (AdjoinRoot.root (fA n u) ⊗ₜ[A] (1 : K)) (by
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.includeRight_apply]
      rw [Algebra.TensorProduct.tmul_pow, one_pow, root_fA_pow, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, sub_self])

theorem θ_of (n : ℕ) (u : A) (k : K) :
    θ n u (AdjoinRoot.of (fK K n u) k) = (1 : AdjoinRoot (fA n u)) ⊗ₜ[A] k := by
  simp [θ]

theorem θ_root (n : ℕ) (u : A) :
    θ n u (AdjoinRoot.root (fK K n u)) = AdjoinRoot.root (fA n u) ⊗ₜ[A] (1 : K) := by
  simp [θ]

noncomputable def θₐ (n : ℕ) (u : A) : AdjoinRoot (fK K n u) →ₐ[A] AdjoinRoot (fA n u) ⊗[A] K :=
  { θ n u with
    commutes' := fun a => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe]
      rw [IsScalarTower.algebraMap_apply A K (AdjoinRoot (fK K n u)), AdjoinRoot.algebraMap_eq, θ_of,
        Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_eq_smul_one (A := AdjoinRoot (fA n u)), TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one] }

noncomputable def ψθ (n : ℕ) (u : A) : AdjoinRoot (fK K n u) →ₐ[K] AdjoinRoot (fK K n u) :=
  { (ψ n u).toRingHom.comp (θ n u) with
    commutes' := fun k => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, AdjoinRoot.algebraMap_eq]
      rw [θ_of]
      change ψ n u ((1 : AdjoinRoot (fA n u)) ⊗ₜ[A] k) = _
      rw [ψ_tmul, map_one, one_mul]
      rfl }

theorem ψθ_eq_id (n : ℕ) (u : A) : ψθ (K := K) n u = AlgHom.id K (AdjoinRoot (fK K n u)) := by
  apply AdjoinRoot.algHom_ext
  change ψ n u (θ n u (AdjoinRoot.root (fK K n u))) = AdjoinRoot.root (fK K n u)
  rw [θ_root, ψ_tmul, map_one, mul_one, ψ₁_root]

theorem ψ_θ (n : ℕ) (u : A) (x : AdjoinRoot (fK K n u)) : ψ n u (θ n u x) = x := by
  have h := congrArg (fun φ : AdjoinRoot (fK K n u) →ₐ[K] AdjoinRoot (fK K n u) => φ x) (ψθ_eq_id (K := K) n u)
  simpa [ψθ] using h

theorem integralClosure_eq_adjoin (n : ℕ) (u : A) (hn : IsUnit ((n : ℕ) : A)) (hu : IsUnit u) :
    integralClosure A (AdjoinRoot (fK K n u)) = Algebra.adjoin A {AdjoinRoot.root (fK K n u)} := by
  classical
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn

  have hE : Algebra.Etale A (AdjoinRoot (fA n u)) :=
    (AdjoinRoot.etale_and_finite_X_pow_sub_C_of_isUnit n u hn hu).1
  haveI : Algebra.Smooth A (AdjoinRoot (fA n u)) :=
    (Algebra.Etale.iff_formallyUnramified_and_smooth.mp hE).2
  apply le_antisymm
  ·
    intro x hx
    have hx' : IsIntegral A x := hx
    have h1 : IsIntegral A (θₐ n u x) := hx'.map (θₐ n u)
    have h2 : IsIntegral (AdjoinRoot (fA n u)) (θₐ n u x) := h1.tower_top
    obtain ⟨s, hs⟩ := mem_range_includeLeft_of_isIntegral (A := A) (K := K) (θₐ n u x) h2
    have hx_eq : x = ψ₁ n u s := by
      have := ψ_θ (K := K) n u x
      change ψ n u (θₐ n u x) = x at this
      rw [← hs, Algebra.TensorProduct.includeLeftRingHom_apply, ψ_tmul, map_one, mul_one] at this
      exact this.symm
    rw [hx_eq]
    have hrange : (ψ₁ (K := K) n u).range = Algebra.adjoin A {AdjoinRoot.root (fK K n u)} := by
      rw [← Algebra.map_top, ← AdjoinRoot.adjoinRoot_eq_top, AlgHom.map_adjoin, Set.image_singleton,
        ψ₁_root]
    change ψ₁ n u s ∈ (Algebra.adjoin A {AdjoinRoot.root (fK K n u)} : Subalgebra A _)
    rw [← hrange]
    exact ⟨s, rfl⟩
  ·
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    change IsIntegral A (AdjoinRoot.root (fK K n u))
    refine ⟨fA n u, Polynomial.monic_X_pow_sub_C u hn0, ?_⟩
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, root_fK_pow, sub_self]

end KummerIntegralClosureKa

open KummerIntegralClosureKa in
theorem solution
    {A K : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (n : ℕ) (u : A) (hn : IsUnit (n : A)) (hu : IsUnit u) :
    integralClosure A (AdjoinRoot (X ^ n - C (algebraMap A K u) : K[X])) =
      Algebra.adjoin A {AdjoinRoot.root (X ^ n - C (algebraMap A K u) : K[X])} :=
  integralClosure_eq_adjoin n u hn hu

end S_IsIntegrallyClosed_integralClosure_eq_adjoin_root_X_pow_sub_C_of_isUnit
end P2MW
export P2MW.S_IsIntegrallyClosed_integralClosure_eq_adjoin_root_X_pow_sub_C_of_isUnit (solution)
