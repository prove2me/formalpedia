-- Prove2me | solution 1 for HopfAlgebra.exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7f064308-394b-5477-86df-d9b8ede1922e

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual

set_option autoImplicit false

open TensorProduct

namespace UnipotentPrimitive

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Bialgebra k A] [Coalgebra.IsCocomm k A]

lemma mem_maximalIdeal_of_apply_one_eq_zero
    (hloc : IsLocalRing (CartierDual k A)) (φ : CartierDual k A) (hφ : φ 1 = 0) :
    φ ∈ IsLocalRing.maximalIdeal (CartierDual k A) := by
  haveI := hloc
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨ψ', hψ'⟩ := hu.exists_right_inv
  have h1 := congrArg (fun χ : CartierDual k A => χ 1) hψ'
  rw [CartierDual.mul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.dualDistrib_apply, CartierDual.one_apply, Bialgebra.counit_one,
    CartierDual.toDual_apply, hφ, zero_mul] at h1
  exact zero_ne_one h1

lemma apply_one_eq_zero_of_mem_maximalIdeal
    (hloc : IsLocalRing (CartierDual k A)) (φ : CartierDual k A)
    (hφ : φ ∈ IsLocalRing.maximalIdeal (CartierDual k A)) : φ 1 = 0 := by
  haveI := hloc
  by_contra hne
  set c : k := φ 1
  have hφ' : φ - algebraMap k (CartierDual k A) c ∈ IsLocalRing.maximalIdeal (CartierDual k A) := by
    apply mem_maximalIdeal_of_apply_one_eq_zero hloc
    show φ 1 - (algebraMap k (CartierDual k A) c) 1 = 0
    rw [CartierDual.algebraMap_apply, Bialgebra.counit_one, one_mul, sub_self]
  have hu : IsUnit (algebraMap k (CartierDual k A) c) := (Ne.isUnit hne).map _
  have hmem : algebraMap k (CartierDual k A) c ∈ IsLocalRing.maximalIdeal (CartierDual k A) := by
    have := Ideal.sub_mem _ hφ hφ'
    rwa [sub_sub_cancel] at this
  exact (IsLocalRing.mem_maximalIdeal _).1 hmem hu

variable [Module.Finite k A]

lemma isNilpotent_maximalIdeal (hloc : IsLocalRing (CartierDual k A)) :
    IsNilpotent (IsLocalRing.maximalIdeal (CartierDual k A)) := by
  haveI := hloc
  haveI : IsArtinianRing (CartierDual k A) := IsArtinianRing.of_finite k (CartierDual k A)
  have h := IsArtinianRing.isNilpotent_jacobson_bot (R := CartierDual k A)
  rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h

lemma exists_mem_maximalIdeal_ne_zero (hloc : IsLocalRing (CartierDual k A))
    (hrank : Module.finrank k A ≠ 1) :
    ∃ φ ∈ IsLocalRing.maximalIdeal (CartierDual k A), φ ≠ 0 := by
  haveI := hloc
  haveI : Nontrivial A := ⟨⟨0, 1, fun h => zero_ne_one (α := k)
    (by simpa using congrArg (Coalgebra.counit (R := k) (A := A)) h)⟩⟩

  have hlt : Submodule.span k {(1 : A)} ≠ ⊤ := by
    intro htop
    apply hrank
    have h1 : Module.finrank k (Submodule.span k {(1 : A)}) = 1 :=
      finrank_span_singleton one_ne_zero
    rw [htop, finrank_top] at h1
    exact h1
  obtain ⟨a, ha⟩ : ∃ a : A, a ∉ Submodule.span k {(1 : A)} := by
    by_contra h
    push Not at h
    exact hlt (eq_top_iff.2 fun a _ => h a)
  obtain ⟨f, hfa, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem ha inferInstance
  refine ⟨CartierDual.ofDual k A f, mem_maximalIdeal_of_apply_one_eq_zero hloc _ ?_, ?_⟩
  · have : f 1 ∈ (Submodule.span k {(1 : A)}).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span rfl)
    rw [hf, Submodule.mem_bot] at this
    exact this
  · intro h0
    apply hfa
    have := congrArg (fun χ : CartierDual k A => χ a) h0
    simp at this
    exact this

theorem exists_primitive (hloc : IsLocalRing (CartierDual k A)) (hrank : Module.finrank k A ≠ 1) :
    ∃ a : A, a ≠ 0 ∧ Coalgebra.comul (R := k) a = a ⊗ₜ[k] 1 + 1 ⊗ₜ[k] a := by
  classical
  haveI := hloc
  set C := CartierDual k A
  set 𝔪 := IsLocalRing.maximalIdeal (CartierDual k A) with h𝔪

  set W : Submodule k (CartierDual k A) :=
    Submodule.span k {(1 : CartierDual k A)} ⊔ (𝔪 ^ 2).restrictScalars k with hW
  obtain ⟨φ₀, hφ₀𝔪, hφ₀W⟩ : ∃ φ₀ ∈ 𝔪, φ₀ ∉ W := by
    by_contra hall
    push Not at hall

    have hle : 𝔪 ≤ 𝔪 ^ 2 := by
      intro φ hφ
      have hφW := hall φ hφ
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hφW
      rw [Submodule.mem_span_singleton] at hy
      obtain ⟨c, rfl⟩ := hy
      change z ∈ 𝔪 ^ 2 at hz
      have hz1 : z 1 = 0 :=
        apply_one_eq_zero_of_mem_maximalIdeal hloc z (Ideal.pow_le_self two_ne_zero hz)
      have h1 : (c • (1 : CartierDual k A) + z) 1 = 0 :=
        apply_one_eq_zero_of_mem_maximalIdeal hloc _ hφ
      have hc : c = 0 := by
        have e : (c • (1 : CartierDual k A) + z) 1 = c * (1 : CartierDual k A) 1 + z 1 := rfl
        rw [e, hz1, CartierDual.one_apply, Bialgebra.counit_one, mul_one, add_zero] at h1
        exact h1
      rw [hc, zero_smul, zero_add]
      exact hz
    have hidem : IsIdempotentElem 𝔪 := by
      change 𝔪 * 𝔪 = 𝔪
      apply le_antisymm Ideal.mul_le_left
      rw [← pow_two]; exact hle
    obtain ⟨N, hN⟩ := isNilpotent_maximalIdeal (k := k) (A := A) hloc
    obtain ⟨φ, hφ, hφ0⟩ := exists_mem_maximalIdeal_ne_zero hloc hrank
    have h𝔪bot : 𝔪 = ⊥ := by
      have e := hidem.pow_succ_eq N
      rw [pow_succ, hN, zero_mul] at e
      exact e.symm.trans Submodule.zero_eq_bot
    have hφ' : φ ∈ 𝔪 := hφ
    rw [h𝔪bot, Submodule.mem_bot] at hφ'
    exact hφ0 hφ'

  obtain ⟨lam, hlamφ₀, hlamW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hφ₀W inferInstance
  have hlam0 : ∀ w ∈ W, lam w = 0 := fun w hw => by
    have : lam w ∈ W.map lam := Submodule.mem_map_of_mem hw
    rwa [hlamW, Submodule.mem_bot] at this
  have hlam1 : lam 1 = 0 := hlam0 _ (Submodule.mem_sup_left (Submodule.subset_span rfl))
  have hlam2 : ∀ φ ∈ 𝔪, ∀ ψ ∈ 𝔪, lam (φ * ψ) = 0 := fun φ hφ ψ hψ =>
    hlam0 _ (Submodule.mem_sup_right (by
      change φ * ψ ∈ 𝔪 ^ 2
      rw [pow_two]; exact Ideal.mul_mem_mul hφ hψ))

  have hder : ∀ φ ψ : CartierDual k A, lam (φ * ψ) = φ 1 * lam ψ + ψ 1 * lam φ := by
    intro φ ψ
    have key : ∀ χ : CartierDual k A, ∃ χ' ∈ 𝔪,
        χ = algebraMap k (CartierDual k A) (χ 1) + χ' ∧ lam χ = lam χ' := by
      intro χ
      refine ⟨χ - algebraMap k _ (χ 1), mem_maximalIdeal_of_apply_one_eq_zero hloc _ ?_,
        (add_sub_cancel _ _).symm, ?_⟩
      · show χ 1 - (algebraMap k (CartierDual k A) (χ 1)) 1 = 0
        rw [CartierDual.algebraMap_apply, Bialgebra.counit_one, one_mul, sub_self]
      · rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, hlam1, smul_zero, sub_zero]
    obtain ⟨φ', hφ'm, eφ, lφ⟩ := key φ
    obtain ⟨ψ', hψ'm, eψ, lψ⟩ := key ψ
    have hprod : φ * ψ = algebraMap k (CartierDual k A) (φ 1 * ψ 1) + (φ 1) • ψ' + (ψ 1) • φ' +
        φ' * ψ' := by
      conv_lhs => rw [eφ, eψ]
      rw [map_mul, Algebra.smul_def, Algebra.smul_def]; ring
    rw [hprod, map_add, map_add, map_add, map_smul, map_smul, Algebra.algebraMap_eq_smul_one,
      map_smul, hlam1, hlam2 _ hφ'm _ hψ'm, lφ, lψ, smul_zero, zero_add, add_zero, smul_eq_mul,
      smul_eq_mul]

  let lam' : Module.Dual k (Module.Dual k A) := lam ∘ₗ (CartierDual.ofDual k A).toLinearMap
  let a : A := (Module.evalEquiv k A).symm lam'
  have ha : ∀ φ : CartierDual k A, φ a = lam φ := fun φ => by
    have := Module.apply_evalEquiv_symm_apply (R := k) (M := A) (CartierDual.toDual k A φ) lam'
    exact this
  refine ⟨a, ?_, ?_⟩
  · intro h0
    apply hlamφ₀
    rw [← ha, h0, map_zero]
  ·
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff k]
    intro F
    obtain ⟨w, rfl⟩ := (TensorProduct.dualDistribEquiv k A A).surjective F
    rw [map_sub, sub_eq_zero]
    change TensorProduct.dualDistrib k A A w _ = TensorProduct.dualDistrib k A A w _
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul φ ψ =>
      rw [map_add, TensorProduct.dualDistrib_apply, TensorProduct.dualDistrib_apply,
        ← CartierDual.ofDual_apply (R := k) φ a, ← CartierDual.ofDual_apply (R := k) ψ a,
        ← CartierDual.ofDual_apply (R := k) φ 1, ← CartierDual.ofDual_apply (R := k) ψ 1]
      have hmul := CartierDual.mul_apply (CartierDual.ofDual k A φ) (CartierDual.ofDual k A ψ) a
      rw [CartierDual.toDual_ofDual, CartierDual.toDual_ofDual] at hmul
      rw [← hmul, ha, hder, ha, ha]
      ring
    | add x y hx hy => rw [map_add, LinearMap.add_apply, LinearMap.add_apply, hx, hy]

end UnipotentPrimitive

universe u v

theorem solution
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Bialgebra k A] [Coalgebra.IsCocomm k A]
    [Module.Finite k A] (hA : IsLocalRing (CartierDual k A)) (hrank : Module.finrank k A ≠ 1) :
    ∃ a : A, a ≠ 0 ∧ Coalgebra.comul (R := k) a = a ⊗ₜ[k] 1 + 1 ⊗ₜ[k] a :=
  UnipotentPrimitive.exists_primitive hA hrank

end S_HopfAlgebra_exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_HopfAlgebra_exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual (solution)
