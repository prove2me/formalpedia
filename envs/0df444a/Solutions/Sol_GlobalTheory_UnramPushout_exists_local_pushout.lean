-- Prove2me | solution 1 for GlobalTheory.UnramPushout.exists_local_pushout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:00:24.736145+00:00
-- url     : https://prove2.me/submissions/2078107d-b0bf-4966-bb18-53bf2ac60684

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalPushoutUnramifiedCharZero
import Theorems.Thm_GlobalTheory_UnramPushout_isReduced_nontrivial_tensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.UnramPushout
open TensorProduct
namespace GlobalTheory.UnramPushout
theorem _root_.solution (A V V' : Type) [CommRing A] [CommRing V] [IsLocalRing V]
    [CommRing V'] [IsLocalRing V'] (f : A →+* V) (f' : A →+* V') (hf' : f'.Flat)
    (hP : (maximalIdeal V).comap f = (maximalIdeal V').comap f')
    (hV : ((maximalIdeal V).comap f).map f = maximalIdeal V)
    (hV' : ((maximalIdeal V').comap f').map f' = maximalIdeal V')
    (h0 : CharZero (ResidueField V)) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B) (g : V →+* B) (g' : V' →+* B),
      g.comp f = g'.comp f' ∧ g.Flat ∧ (maximalIdeal V).map g = maximalIdeal B ∧
        (maximalIdeal V').map g' = maximalIdeal B := by
  letI : Algebra A V := f.toAlgebra
  letI : Algebra A V' := f'.toAlgebra
  haveI : Module.Flat A V' := hf'
  set P := (maximalIdeal V).comap f with hPdef
  let C := V ⊗[A] V'
  let φ : C →ₐ[A] ResidueField V ⊗[A] ResidueField V' :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A V (ResidueField V))
      (IsScalarTower.toAlgHom A V' (ResidueField V'))
  set Q := P.map (algebraMap A C) with hQ
  have hL : (maximalIdeal V).map (Algebra.TensorProduct.includeLeft : V →ₐ[A] C) = Q := by
    rw [← hV, hQ, AlgHom.coe_ideal_map, Ideal.map_map]
    congr 1
  have hR : (maximalIdeal V').map (Algebra.TensorProduct.includeRight : V' →ₐ[A] C) = Q := by
    rw [← hV', ← hP, hQ, AlgHom.coe_ideal_map, Ideal.map_map]
    congr 1
    ext a
    exact (Algebra.TensorProduct.includeRight (R := A) (A := V) (B := V')).commutes a
  have hker : RingHom.ker φ = Q := by
    have e1 : RingHom.ker (IsScalarTower.toAlgHom A V (ResidueField V)) = maximalIdeal V :=
      ker_residue
    have e2 : RingHom.ker (IsScalarTower.toAlgHom A V' (ResidueField V')) = maximalIdeal V' :=
      ker_residue
    rw [Algebra.TensorProduct.map_ker _ _ residue_surjective residue_surjective, e1, e2, hL, hR,
      sup_idem]
  have hk : RingHom.ker (algebraMap A (ResidueField V)) = P := by
    ext a
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply A V (ResidueField V),
      ResidueField.algebraMap_eq, residue_eq_zero_iff]
    rfl
  have hk' : RingHom.ker (algebraMap A (ResidueField V')) = P := by
    rw [hP]
    ext a
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply A V' (ResidueField V'),
      ResidueField.algebraMap_eq, residue_eq_zero_iff]
    rfl
  obtain ⟨hred, hnt⟩ :=
    isReduced_nontrivial_tensor (k := ResidueField V) (k' := ResidueField V') P hk hk'
  have hrad : Q.IsRadical := by
    rintro x ⟨n, hn⟩
    rw [← hker, RingHom.mem_ker] at hn ⊢
    rw [map_pow] at hn
    exact IsNilpotent.eq_zero ⟨n, hn⟩
  have hne : Q ≠ ⊤ := by
    intro h
    have h1 : (1 : C) ∈ RingHom.ker φ := by rw [hker, h]; exact Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  haveI := hm.isPrime
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le hle
  haveI : q.IsPrime := hq.1.1
  let B := Localization.AtPrime q
  have hmax : Q.map (algebraMap C B) = maximalIdeal B := by
    have h1 := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes B q Q hq
    rw [← IsLocalization.map_radical q.primeCompl B, hrad.radical,
      Localization.AtPrime.map_eq_maximalIdeal] at h1
    exact h1
  let g : V →+* B := (algebraMap C B).comp
    ((Algebra.TensorProduct.includeLeft : V →ₐ[A] C) : V →+* C)
  let g' : V' →+* B := (algebraMap C B).comp
    ((Algebra.TensorProduct.includeRight : V' →ₐ[A] C) : V' →+* C)
  have hgf : g.comp f = (algebraMap C B).comp (algebraMap A C) := by
    ext a
    exact congrArg (algebraMap C B)
      ((Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := V) (B := V')).commutes a)
  have hgf' : g'.comp f' = (algebraMap C B).comp (algebraMap A C) := by
    ext a
    exact congrArg (algebraMap C B)
      ((Algebra.TensorProduct.includeRight (R := A) (A := V) (B := V')).commutes a)
  rw [AlgHom.coe_ideal_map] at hL hR
  refine ⟨B, inferInstance, inferInstance, g, g', hgf.trans hgf'.symm, ?_, ?_, ?_⟩
  · have h1 : (algebraMap C B).Flat :=
      RingHom.flat_algebraMap_iff.2 (IsLocalization.flat B q.primeCompl)
    have h2 : (algebraMap V C).Flat := RingHom.flat_algebraMap_iff.2 (Module.Flat.baseChange A V V')
    exact RingHom.Flat.comp h2 h1
  · rw [← Ideal.map_map, hL, hmax]
  · rw [← Ideal.map_map, hR, hmax]
end GlobalTheory.UnramPushout
