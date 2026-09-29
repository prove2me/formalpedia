-- Prove2me | solution 1 for IsLocalRing.exists_monic_aeval_eq_zero_map_residue_eq_pow_of_residue_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/990d9cb6-6b9e-5199-a99d-c8a9396a67ca

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_monic_aeval_eq_zero_map_residue_eq_pow_of_residue_eq

set_option autoImplicit false

open Polynomial IsLocalRing
open scoped TensorProduct

namespace Ws50RT

section engine

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
  {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] [Module.Free 𝒪 A]
  [IsLocalHom (algebraMap 𝒪 A)]

theorem exists_pow_mem_map_maximalIdeal (m : A) (hm : m ∈ maximalIdeal A) :
    ∃ n : ℕ, m ^ n ∈ (maximalIdeal 𝒪).map (algebraMap 𝒪 A) := by
  have hrad : m ∈ ((maximalIdeal 𝒪).map (algebraMap 𝒪 A)).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hIP, hP⟩
    have hcomap : maximalIdeal 𝒪 ≤ P.comap (algebraMap 𝒪 A) := Ideal.map_le_iff_le_comap.mp hIP
    have hne : P.comap (algebraMap 𝒪 A) ≠ ⊤ := Ideal.comap_ne_top _ hP.ne_top
    have heq : P.comap (algebraMap 𝒪 A) = maximalIdeal 𝒪 :=
      ((IsLocalRing.maximalIdeal.isMaximal 𝒪).eq_of_le hne hcomap).symm
    have hmax' : (P.comap (algebraMap 𝒪 A)).IsMaximal := heq ▸ IsLocalRing.maximalIdeal.isMaximal 𝒪
    haveI := hP
    have hPmax : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P hmax'
    rw [IsLocalRing.eq_maximalIdeal hPmax]
    exact hm
  exact hrad

variable (𝒪 A) in

theorem baseChange_lmul_eq_zero_of_mem {a : A} (ha : a ∈ (maximalIdeal 𝒪).map (algebraMap 𝒪 A)) :
    (Algebra.lmul 𝒪 A a).baseChange (ResidueField 𝒪) = 0 := by
  refine Submodule.span_induction (p := fun a _ => (Algebra.lmul 𝒪 A a).baseChange (ResidueField 𝒪) = 0)
    ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨r, hr, rfl⟩
    have h1 : Algebra.lmul 𝒪 A (algebraMap 𝒪 A r) = r • (1 : Module.End 𝒪 A) := by
      ext b
      simp [Algebra.smul_def]
    rw [h1, LinearMap.baseChange_smul, LinearMap.baseChange_one, ← algebraMap_smul (ResidueField 𝒪) r,
      ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff r).mpr hr, zero_smul]
  · show (Algebra.lmul 𝒪 A 0).baseChange (ResidueField 𝒪) = 0
    rw [map_zero, LinearMap.baseChange_zero]
  · intro a b _ _ ha hb
    rw [map_add, LinearMap.baseChange_add, ha, hb, add_zero]
  · intro a b _ hb
    rw [smul_eq_mul, map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp, hb, LinearMap.comp_zero]

theorem exists_monic_aeval_eq_zero_map_residue_eq_pow
    {F : Type} [CommRing F] [Algebra 𝒪 F]
    (φ : A →ₐ[𝒪] F) (x : A) (c : ResidueField 𝒪)
    (hx : residue A x = ResidueField.map (algebraMap 𝒪 A) c) :
    ∃ R : Polynomial 𝒪, R.Monic ∧ aeval (φ x) R = 0 ∧
        R.map (residue 𝒪) = (X - C c) ^ R.natDegree := by
  classical
  set f : Module.End 𝒪 A := Algebra.lmul 𝒪 A x with hf

  have hCH : aeval x f.charpoly = 0 := by
    have h1 : aeval f f.charpoly = 0 := f.aeval_self_charpoly
    have h2 := congrArg (fun g : Module.End 𝒪 A => g 1) h1
    simp only [LinearMap.zero_apply, hf, aeval_algHom_apply] at h2
    simpa [hf] using h2
  refine ⟨f.charpoly, f.charpoly_monic, by rw [aeval_algHom_apply, hCH, map_zero], ?_⟩

  obtain ⟨c₀, rfl⟩ := Ideal.Quotient.mk_surjective c
  change residue A x = ResidueField.map (algebraMap 𝒪 A) (residue 𝒪 c₀) at hx
  rw [ResidueField.map_residue] at hx
  set m : A := x - algebraMap 𝒪 A c₀ with hm
  have hmmem : m ∈ maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, hm, map_sub, hx, sub_self]
  obtain ⟨n, hn⟩ := exists_pow_mem_map_maximalIdeal (𝒪 := 𝒪) m hmmem
  have hnil : IsNilpotent ((Algebra.lmul 𝒪 A m).baseChange (ResidueField 𝒪)) := by
    refine ⟨n, ?_⟩
    rw [← LinearMap.baseChange_pow, ← map_pow]
    exact baseChange_lmul_eq_zero_of_mem 𝒪 A hn
  have hkey : (Algebra.lmul 𝒪 A m).baseChange (ResidueField 𝒪) = f.baseChange (ResidueField 𝒪) - (residue 𝒪 c₀) • 1 := by
    have h1 : Algebra.lmul 𝒪 A (algebraMap 𝒪 A c₀) = c₀ • (1 : Module.End 𝒪 A) := by
      ext b
      simp [Algebra.smul_def]
    rw [hm, map_sub, LinearMap.baseChange_sub, hf, h1, LinearMap.baseChange_smul, LinearMap.baseChange_one,
      ← algebraMap_smul (ResidueField 𝒪) c₀, ResidueField.algebraMap_eq]
  have hchar : (f.baseChange (ResidueField 𝒪) - (residue 𝒪 c₀) • 1).charpoly = X ^ Module.finrank (ResidueField 𝒪) (ResidueField 𝒪 ⊗[𝒪] A) := by
    rw [← hkey]
    exact hnil.charpoly_eq_X_pow_finrank
  rw [LinearMap.charpoly_sub_smul] at hchar
  have hbc : (f.baseChange (ResidueField 𝒪)).charpoly = (X - C (residue 𝒪 c₀)) ^ Module.finrank (ResidueField 𝒪) (ResidueField 𝒪 ⊗[𝒪] A) := by
    have h := congrArg (fun p : Polynomial (ResidueField 𝒪) => p.comp (X - C (residue 𝒪 c₀))) hchar
    simp only [Polynomial.comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, Polynomial.comp_X,
      X_pow_comp] at h
    exact h
  rw [LinearMap.charpoly_baseChange, ResidueField.algebraMap_eq] at hbc
  rw [hbc]
  congr 1
  have hdeg := congrArg natDegree hbc
  rwa [(f.charpoly_monic).natDegree_map, natDegree_pow, natDegree_X_sub_C, mul_one, eq_comm] at hdeg

end engine

end Ws50RT

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] [Module.Free 𝒪 A]
    [IsLocalHom (algebraMap 𝒪 A)]
    {F : Type} [CommRing F] [Algebra 𝒪 F]
    (φ : A →ₐ[𝒪] F) (x : A) (c : IsLocalRing.ResidueField 𝒪)
    (hx : IsLocalRing.residue A x = IsLocalRing.ResidueField.map (algebraMap 𝒪 A) c) :
    (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (φ x) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C c) ^ R.natDegree) :=
  Ws50RT.exists_monic_aeval_eq_zero_map_residue_eq_pow φ x c hx

end S_IsLocalRing_exists_monic_aeval_eq_zero_map_residue_eq_pow_of_residue_eq
end P2MW
export P2MW.S_IsLocalRing_exists_monic_aeval_eq_zero_map_residue_eq_pow_of_residue_eq (solution)
