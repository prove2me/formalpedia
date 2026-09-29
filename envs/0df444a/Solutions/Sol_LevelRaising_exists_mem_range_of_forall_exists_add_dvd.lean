-- Prove2me | solution 1 for LevelRaising.exists_mem_range_of_forall_exists_add_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/0365255e-aea7-58b8-b279-8fa752bea2b4

import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LevelRaising_exists_mem_range_of_forall_exists_add_dvd

set_option Elab.async false
set_option autoImplicit false

open Polynomial

namespace LevelRaisingAux
namespace LocalNakayama

section LemmaA

variable {C : Type*} [AddCommGroup C] [Module.Finite ℤ C] (τ : C →ₗ[ℤ] C)
  {p : ℕ} [Fact p.Prime] (a : ℤ)

private theorem exists_annihilate_of_forall_exists_dvd
    (h : ∀ c : C, ∃ s : ℤ[X], ((s.eval a : ℤ) : ZMod p) ≠ 0 ∧
      ∃ c' : C, (aeval τ s) c = (p : ℤ) • c') :
    ∀ c : C, ∃ S : ℤ[X], ((S.eval a : ℤ) : ZMod p) ≠ 0 ∧ (aeval τ S) c = 0 := by
  classical

  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := ℤ) (M := C)
  choose s hs_unit c' hs_dvd using h

  let s₀ : ℤ[X] := ∏ g ∈ G, s g

  have hpC : LinearMap.range (aeval τ s₀ : C →ₗ[ℤ] C) ≤ (Ideal.span {(p : ℤ)}) • ⊤ := by
    rw [LinearMap.range_le_iff_comap, eq_top_iff, ← hG, Submodule.span_le]
    intro g hg
    rw [SetLike.mem_coe, Submodule.mem_comap, hG,
      show s₀ = (∏ j ∈ G.erase g, s j) * s g from (Finset.prod_erase_mul G s hg).symm,
      map_mul, Module.End.mul_apply, hs_dvd g, map_smul, Submodule.ideal_span_singleton_smul]
    exact ⟨_, Submodule.mem_top, rfl⟩

  obtain ⟨P, hPmonic, _hPdeg, hPcoeff, hPkill⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero ℤ
      (aeval τ s₀) (Ideal.span {(p : ℤ)}) hpC

  refine fun c => ⟨P.comp s₀, ?_, ?_⟩
  ·
    rw [eval_comp]
    have hs₀_unit : ((s₀.eval a : ℤ) : ZMod p) ≠ 0 := by
      simp only [s₀, eval_prod, Int.cast_prod]
      exact Finset.prod_ne_zero_iff.mpr fun g _ => hs_unit g

    have hP_modp : ((P.eval (s₀.eval a) : ℤ) : ZMod p)
        = ((s₀.eval a : ℤ) : ZMod p) ^ P.natDegree := by
      rw [eval_eq_sum_range (s₀.eval a), Int.cast_sum, Finset.sum_range_succ,
        hPmonic.coeff_natDegree, one_mul, Int.cast_pow]
      convert zero_add _
      refine Finset.sum_eq_zero fun k hk => ?_
      have hkP : P.coeff k ∈ Ideal.span {(p : ℤ)} :=
        Ideal.pow_le_self (Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hk)) (hPcoeff k)
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hkP
      rw [hd, Int.cast_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_mul]
    rw [hP_modp]
    exact pow_ne_zero _ hs₀_unit
  · have := congrArg (· c) (congrArg DFunLike.coe hPkill)
    simpa [aeval_comp] using this

end LemmaA

section LemmaB

variable {C₁ C₀ : Type*} [AddCommGroup C₁] [AddCommGroup C₀] [Module.Finite ℤ C₀]
  (τ₁ : C₁ →ₗ[ℤ] C₁) (τ₀ : C₀ →ₗ[ℤ] C₀) (β : C₁ →ₗ[ℤ] C₀)
  (hβτ : β ∘ₗ τ₁ = τ₀ ∘ₗ β)
  {p : ℕ} [Fact p.Prime] (a : ℤ)

private def τQuot : (C₀ ⧸ LinearMap.range β) →ₗ[ℤ] (C₀ ⧸ LinearMap.range β) :=
  Submodule.mapQ _ _ τ₀ (by
    rintro _ ⟨y, rfl⟩
    exact ⟨τ₁ y, LinearMap.congr_fun hβτ y⟩)

omit [Module.Finite ℤ C₀] in
private lemma τQuot_mk (x : C₀) :
    τQuot τ₁ τ₀ β hβτ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (τ₀ x) := rfl

omit [Module.Finite ℤ C₀] in
private lemma τQuot_pow_mk (n : ℕ) (x : C₀) :
    ((τQuot τ₁ τ₀ β hβτ) ^ n) (Submodule.Quotient.mk x) = Submodule.Quotient.mk ((τ₀ ^ n) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => simp only [pow_succ, Module.End.mul_apply]; exact ih (τ₀ x)

omit [Module.Finite ℤ C₀] in
private lemma aeval_τQuot_mk (s : ℤ[X]) (x : C₀) :
    (aeval (τQuot τ₁ τ₀ β hβτ) s) (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk ((aeval τ₀ s) x) := by
  induction s using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    rw [τQuot_pow_mk]
    exact (map_zsmul (LinearMap.range β).mkQ c ((τ₀ ^ n) x)).symm

include τ₁ hβτ in

private theorem exists_mem_range_of_forall_exists_add_dvd
    (hyp : ∀ h : C₀, ∃ s : ℤ[X], ((s.eval a : ℤ) : ZMod p) ≠ 0 ∧
      ∃ x : C₁, ∃ h' : C₀, (aeval τ₀ s) h = β x + (p : ℤ) • h') :
    ∀ h : C₀, ∃ s : ℤ[X], ((s.eval a : ℤ) : ZMod p) ≠ 0 ∧
      ∃ x : C₁, (aeval τ₀ s) h = β x := by

  have hfin : Module.Finite ℤ (C₀ ⧸ LinearMap.range β) :=
    Module.Finite.of_surjective (LinearMap.range β).mkQ (LinearMap.range β).mkQ_surjective
  have := exists_annihilate_of_forall_exists_dvd (τQuot τ₁ τ₀ β hβτ) a (fun cbar => by
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ cbar
    obtain ⟨s, hs_unit, x, h', hs_eq⟩ := hyp c
    refine ⟨s, hs_unit, Submodule.Quotient.mk h', ?_⟩
    rw [aeval_τQuot_mk, hs_eq, Submodule.Quotient.mk_add,
      (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self β x), zero_add]
    exact map_zsmul (LinearMap.range β).mkQ (p : ℤ) h')
  intro h
  obtain ⟨S, hS_unit, hS_kill⟩ := this (Submodule.Quotient.mk h)
  rw [aeval_τQuot_mk, Submodule.Quotient.mk_eq_zero] at hS_kill
  obtain ⟨x, hx⟩ := hS_kill
  exact ⟨S, hS_unit, x, hx.symm⟩

end LemmaB

end LevelRaisingAux.LocalNakayama

theorem solution
    {C₁ C₀ : Type*} [AddCommGroup C₁] [AddCommGroup C₀] [Module.Finite ℤ C₀]
    (τ₁ : C₁ →ₗ[ℤ] C₁) (τ₀ : C₀ →ₗ[ℤ] C₀) (β : C₁ →ₗ[ℤ] C₀)
    (hβτ : β ∘ₗ τ₁ = τ₀ ∘ₗ β)
    {p : ℕ} [Fact p.Prime] (a : ℤ)
    (hyp : ∀ h : C₀, ∃ s : Polynomial ℤ, ((s.eval a : ℤ) : ZMod p) ≠ 0 ∧
      ∃ x : C₁, ∃ h' : C₀, (Polynomial.aeval τ₀ s) h = β x + (p : ℤ) • h') :
    ∀ h : C₀, ∃ s : Polynomial ℤ, ((s.eval a : ℤ) : ZMod p) ≠ 0 ∧
      ∃ x : C₁, (Polynomial.aeval τ₀ s) h = β x :=
  LevelRaisingAux.LocalNakayama.exists_mem_range_of_forall_exists_add_dvd τ₁ τ₀ β hβτ a hyp

#print axioms solution

end S_LevelRaising_exists_mem_range_of_forall_exists_add_dvd
end P2MW
export P2MW.S_LevelRaising_exists_mem_range_of_forall_exists_add_dvd (solution)
