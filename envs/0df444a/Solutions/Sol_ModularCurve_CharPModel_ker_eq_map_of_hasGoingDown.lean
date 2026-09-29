-- Prove2me | solution 1 for ModularCurve.CharPModel.ker_eq_map_of_hasGoingDown
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/184e78f3-06c6-559f-9d80-647fed23c878

import Mathlib.FieldTheory.Relrank
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_ker_eq_map_of_hasGoingDown

set_option autoImplicit false

noncomputable section

open Polynomial

namespace CharpS10bB

namespace KerAbs

open Ideal Polynomial

section Unique

variable {P₀ B κ : Type*} [CommRing P₀] [CommRing B] [Field κ] [Algebra P₀ B]

theorem prime_over_eq_ker [Algebra.IsIntegral P₀ B] (π : B →+* κ) (𝔭₀ : Ideal P₀)
    (hK : (RingHom.ker π).comap (algebraMap P₀ B) = 𝔭₀)
    (R : Subring B) (halg : ∀ p : P₀, algebraMap P₀ B p ∈ R)
    (hpres : ∀ b : B, ∃ r ∈ R, ∃ s ∈ R, π s ≠ 0 ∧ b * s = r)
    (hfree : ∀ r ∈ R, π r = 0 → ∃ c ∈ 𝔭₀, ∃ r' ∈ R, r = algebraMap P₀ B c * r')
    (P : Ideal B) [P.IsPrime] (hP : P.comap (algebraMap P₀ B) = 𝔭₀) :
    P = RingHom.ker π := by
  letI : Algebra P₀ R := ((algebraMap P₀ B).codRestrict R halg).toAlgebra
  haveI : IsScalarTower P₀ R B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halgR : R.subtype.comp (algebraMap P₀ R) = algebraMap P₀ B := RingHom.ext fun _ => rfl
  have hintR : ∀ r : R, IsIntegral P₀ r := fun r =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom P₀ R B) Subtype.val_injective).1
      (Algebra.IsIntegral.isIntegral (r : B))
  set K := RingHom.ker π with hKdef
  haveI hKp : K.IsPrime := RingHom.ker_isPrime π
  haveI hKR : (K.comap R.subtype).IsPrime := Ideal.comap_isPrime _ _
  haveI hPR : (P.comap R.subtype).IsPrime := Ideal.comap_isPrime _ _
  have hKR_le : K.comap R.subtype ≤ P.comap R.subtype := by
    intro r hr
    have hr0 : π (r : B) = 0 := hr
    obtain ⟨c, hc, r', -, hrr⟩ := hfree r r.2 hr0
    show (r : B) ∈ P
    rw [hrr]
    refine P.mul_mem_right _ ?_
    have : c ∈ P.comap (algebraMap P₀ B) := by rw [hP]; exact hc
    exact this
  have hcomapKR : (K.comap R.subtype).comap (algebraMap P₀ R) = 𝔭₀ := by
    rw [Ideal.comap_comap, halgR]; exact hK
  have hcomapPR : (P.comap R.subtype).comap (algebraMap P₀ R) = 𝔭₀ := by
    rw [Ideal.comap_comap, halgR]; exact hP
  have hPR_le : P.comap R.subtype ≤ K.comap R.subtype := by
    intro r hr
    by_contra hrK
    have hlt := Ideal.comap_lt_comap_of_integral_mem_sdiff hKR_le
      ((Set.mem_diff _).2 ⟨hr, hrK⟩) (hintR r)
    rw [hcomapKR, hcomapPR] at hlt
    exact lt_irrefl _ hlt
  have hPK : P ≤ K := by
    intro b hb
    obtain ⟨r, hr, s, hs, hπs, hbs⟩ := hpres b
    have hrP : r ∈ P := by rw [← hbs]; exact P.mul_mem_right _ hb
    have hrK : (⟨r, hr⟩ : R) ∈ K.comap R.subtype :=
      hPR_le (show (⟨r, hr⟩ : R) ∈ P.comap R.subtype from hrP)
    have hπr : π r = 0 := hrK
    rw [RingHom.mem_ker]
    have : π b * π s = 0 := by rw [← map_mul, hbs, hπr]
    exact (mul_eq_zero.1 this).resolve_right hπs
  refine le_antisymm hPK fun b hb => ?_
  by_contra hbP
  have hlt := Ideal.comap_lt_comap_of_integral_mem_sdiff hPK ((Set.mem_diff _).2 ⟨hb, hbP⟩)
    (Algebra.IsIntegral.isIntegral (R := P₀) b)
  rw [hP, hK] at hlt
  exact lt_irrefl _ hlt

theorem ker_le_map [Algebra.HasGoingDown P₀ B] (π : B →+* κ) (𝔭₀ : Ideal P₀) [𝔭₀.IsPrime]
    (hunique : ∀ P : Ideal B, P.IsPrime → P.comap (algebraMap P₀ B) = 𝔭₀ → P = RingHom.ker π)
    (hrad : ∀ (b : B) (n : ℕ), 0 < n → b ^ n ∈ 𝔭₀.map (algebraMap P₀ B) →
      b ∈ 𝔭₀.map (algebraMap P₀ B)) :
    RingHom.ker π ≤ 𝔭₀.map (algebraMap P₀ B) := by
  set I := 𝔭₀.map (algebraMap P₀ B) with hI
  intro b hb
  suffices hrI : b ∈ I.radical by
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 hrI
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [pow_zero] at hn
      have hT : I = ⊤ := Ideal.eq_top_of_isUnit_mem I hn isUnit_one
      rw [hT]; exact Submodule.mem_top
    · exact hrad b n hpos hn
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro Q ⟨hIQ, hQ⟩
  haveI := hQ
  have hle : 𝔭₀ ≤ Q.comap (algebraMap P₀ B) := Ideal.map_le_iff_le_comap.1 hIQ
  haveI : Q.LiesOver (Q.under P₀) := ⟨rfl⟩
  obtain ⟨P, hPQ, hP, hPover⟩ :=
    Q.exists_ideal_le_liesOver_of_le (p := 𝔭₀) (q := Q.under P₀) hle
  have hPcomap : P.comap (algebraMap P₀ B) = 𝔭₀ := hPover.over.symm
  have hPK : P = RingHom.ker π := hunique P hP hPcomap
  exact hPQ (by rw [hPK]; exact hb)

end Unique

end KerAbs

end CharpS10bB

end

theorem solution
    {P₀ : Type*} [CommRing P₀] {B : Type*} [CommRing B] [Algebra P₀ B]
    [Algebra.IsIntegral P₀ B] [Algebra.HasGoingDown P₀ B]
    {κ : Type*} [Field κ] (π : B →+* κ) (𝔭₀ : Ideal P₀) [𝔭₀.IsPrime]
    (hK : (RingHom.ker π).comap (algebraMap P₀ B) = 𝔭₀)
    (R : Subring B) (halg : ∀ p : P₀, algebraMap P₀ B p ∈ R)
    (hpres : ∀ b : B, ∃ r ∈ R, ∃ s ∈ R, π s ≠ 0 ∧ b * s = r)
    (hfree : ∀ r ∈ R, π r = 0 → ∃ c ∈ 𝔭₀, ∃ r' ∈ R, r = algebraMap P₀ B c * r')
    (hrad : ∀ (b : B) (n : ℕ), 0 < n → b ^ n ∈ 𝔭₀.map (algebraMap P₀ B) →
      b ∈ 𝔭₀.map (algebraMap P₀ B)) :
    RingHom.ker π = 𝔭₀.map (algebraMap P₀ B) := by
  apply le_antisymm
  · exact CharpS10bB.KerAbs.ker_le_map π 𝔭₀
      (fun P hP hPc => by
        haveI := hP
        exact CharpS10bB.KerAbs.prime_over_eq_ker π 𝔭₀ hK R halg hpres hfree P hPc)
      hrad
  · rw [Ideal.map_le_iff_le_comap, hK]

end S_ModularCurve_CharPModel_ker_eq_map_of_hasGoingDown
end P2MW
export P2MW.S_ModularCurve_CharPModel_ker_eq_map_of_hasGoingDown (solution)
