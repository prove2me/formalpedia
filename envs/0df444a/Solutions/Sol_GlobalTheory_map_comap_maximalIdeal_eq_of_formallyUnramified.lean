-- Prove2me | solution 1 for GlobalTheory.map_comap_maximalIdeal_eq_of_formallyUnramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:19:52.426951+00:00
-- url     : https://prove2.me/submissions/c298ef3a-43da-4030-b849-366190ee3d8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapComapMaximalIdealEqOfFormallyUnramified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    (A B : Type) [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] :
    ((IsLocalRing.maximalIdeal B).comap (algebraMap A B)).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B := by
  set p := (maximalIdeal B).comap (algebraMap A B) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let A' := Localization.AtPrime p
  have hg : ∀ y : p.primeCompl, IsUnit (algebraMap A B y) := by
    intro y
    have : (y : A) ∉ p := y.2
    exact IsLocalRing.notMem_maximalIdeal.mp this
  let f : A' →+* B := IsLocalization.lift (M := p.primeCompl) hg
  letI : Algebra A' B := f.toAlgebra
  haveI : IsScalarTower A A' B := IsScalarTower.of_algebraMap_eq
    (fun x => (IsLocalization.lift_eq (M := p.primeCompl) hg x).symm)
  haveI : IsLocalHom (algebraMap A' B) := by
    constructor
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
    have e : IsLocalization.mk' A' a s * algebraMap A A' s = algebraMap A A' a :=
      IsLocalization.mk'_spec A' a s
    have hs : IsUnit (algebraMap A' B (algebraMap A A' s)) := by
      rw [← IsScalarTower.algebraMap_apply]; exact hg s
    have ha : IsUnit (algebraMap A B a) := by
      rw [IsScalarTower.algebraMap_apply A A' B, ← e, map_mul]; exact hx.mul hs
    have ha' : a ∈ p.primeCompl := by
      show a ∉ p
      rw [hp, Ideal.mem_comap]
      exact IsLocalRing.notMem_maximalIdeal.mpr ha
    have hu : IsUnit (algebraMap A A' a) := IsLocalization.map_units A' (⟨a, ha'⟩ : p.primeCompl)
    rw [← e] at hu
    exact isUnit_of_mul_isUnit_left hu
  haveI : Algebra.FormallyUnramified A' B := .of_restrictScalars A A' B
  haveI : Algebra.EssFiniteType A' B := .of_comp A A' B
  have h := Algebra.FormallyUnramified.map_maximalIdeal (R := A') (S := B)
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq] at h
  exact h
end GlobalTheory
