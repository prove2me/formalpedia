-- Prove2me | solution 1 for GlobalTheory.UnitAdj.exists_unitary_mul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:19:12.056891+00:00
-- url     : https://prove2.me/submissions/4a628f2e-15de-4d97-86f0-84a2c0b303f2

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryMulIntegralOfNormMaximalOrderUnit
import Theorems.Thm_GlobalTheory_UnitAdj_isIntegral_or_isIntegral_inv
import Theorems.Thm_GlobalTheory_UnitAdj_isIntegral_of_mul_self_eq
import Theorems.Thm_GlobalTheory_UnitAdj_eq_zero_of_forall_mem
import Theorems.Thm_GlobalTheory_UnitAdj_isIntegral_of_residues
import Theorems.Thm_GlobalTheory_UnitAdj_exists_residues_indicator
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
noncomputable section
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.UnitAdj
namespace GlobalTheory.UnitAdj
theorem _root_.solution : ∀ {O K A : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Algebra K A] [Algebra O A] [IsScalarTower O K A] [Module.Finite K A] [IsReduced A]
    (σ : K →+* K), (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    ∀ τ : A →+* A, (∀ a, τ (τ a) = a) → (∀ k, τ (algebraMap K A k) = algebraMap K A (σ k)) →
    ∀ x : Aˣ, IsIntegral O (τ (x : A) * x) → IsIntegral O (τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A)) →
    ∃ t : Aˣ, τ (t : A) * t = 1 ∧ IsIntegral O ((t : A) * ((x⁻¹ : Aˣ) : A)) ∧
      IsIntegral O (((t⁻¹ : Aˣ) : A) * (x : A)) := by
  intro O K A _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ τ hτ hτσ x hc hci
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A

  have hinj := IsFractionRing.injective O K
  choose s hs using hσ
  let σO : O →+* O :=
    { toFun := s
      map_one' := hinj (by simp [← hs])
      map_mul' := fun a b => hinj (by simp [← hs])
      map_zero' := hinj (by simp [← hs])
      map_add' := fun a b => hinj (by simp [← hs]) }
  have hτO : ∀ a : O, τ (algebraMap O A a) = algebraMap O A (σO a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply O K A, hτσ]
    change _ = algebraMap O A (s a)
    rw [hs, ← IsScalarTower.algebraMap_apply]

  have hsurj : Function.Surjective τ := fun a => ⟨τ a, hτ a⟩
  obtain ⟨tI, hmem, htt⟩ : ∃ tI : MaximalSpectrum A → MaximalSpectrum A,
      (∀ I y, y ∈ (tI I).asIdeal ↔ τ y ∈ I.asIdeal) ∧ ∀ I, tI (tI I) = I := by
    have hmax : ∀ I : MaximalSpectrum A, (I.asIdeal.comap τ).IsMaximal := fun I => by
      haveI := I.isMaximal
      exact Ideal.comap_isMaximal_of_surjective τ hsurj
    refine ⟨fun I => ⟨I.asIdeal.comap τ, hmax I⟩, fun I y => Iff.rfl, fun I => ?_⟩
    ext y
    change τ (τ y) ∈ I.asIdeal ↔ y ∈ I.asIdeal
    rw [hτ]

  obtain ⟨e, he⟩ := exists_residues_indicator (fun I : MaximalSpectrum A => WellOrderingRel I (tI I))
  have he1 : ∀ I, WellOrderingRel I (tI I) → e - 1 ∈ I.asIdeal := fun I => (he I).1
  have he0 : ∀ I, ¬ WellOrderingRel I (tI I) → e ∈ I.asIdeal := fun I => (he I).2
  have hτe1 : ∀ I, WellOrderingRel (tI I) I → τ e - 1 ∈ I.asIdeal := by
    intro I h
    have := he1 (tI I) (by rw [htt]; exact h)
    rw [hmem, map_sub, map_one] at this
    exact this
  have hτe0 : ∀ I, ¬ WellOrderingRel (tI I) I → τ e ∈ I.asIdeal := by
    intro I h
    exact (hmem I e).1 (he0 (tI I) (by rw [htt]; exact h))
  have hee : e * e = e := by
    refine sub_eq_zero.1 (eq_zero_of_forall_mem fun I => ?_)
    by_cases hP : WellOrderingRel I (tI I)
    · have := I.asIdeal.mul_mem_left e (he1 I hP)
      rwa [mul_sub, mul_one] at this
    · exact I.asIdeal.sub_mem (I.asIdeal.mul_mem_left e (he0 I hP)) (he0 I hP)
  have hgg : τ e * τ e = τ e := by rw [← map_mul, hee]
  have heg : e * τ e = 0 := by
    refine eq_zero_of_forall_mem fun I => ?_
    by_cases hP : WellOrderingRel I (tI I)
    · exact I.asIdeal.mul_mem_left _ (hτe0 I (asymm_of WellOrderingRel hP))
    · exact I.asIdeal.mul_mem_right _ (he0 I hP)

  set f : A := 1 - e - τ e with hf
  have hfix : ∀ I, tI I = I → f - 1 ∈ I.asIdeal := by
    intro I hI
    have h0 : ¬ WellOrderingRel I (tI I) := by rw [hI]; exact irrefl_of WellOrderingRel I
    have h0' : ¬ WellOrderingRel (tI I) I := by rw [hI]; exact irrefl_of WellOrderingRel I
    have : f - 1 = -(e + τ e) := by rw [hf]; ring
    rw [this]
    exact I.asIdeal.neg_mem (I.asIdeal.add_mem (he0 I h0) (hτe0 I h0'))
  have hmov : ∀ I, tI I ≠ I → f ∈ I.asIdeal := by
    intro I hI
    rcases trichotomous_of WellOrderingRel I (tI I) with h | h | h
    · have : f = -(e - 1) - τ e := by rw [hf]; ring
      rw [this]
      exact I.asIdeal.sub_mem (I.asIdeal.neg_mem (he1 I h)) (hτe0 I (asymm_of WellOrderingRel h))
    · exact absurd h.symm hI
    · have : f = -(τ e - 1) - e := by rw [hf]; ring
      rw [this]
      exact I.asIdeal.sub_mem (I.asIdeal.neg_mem (hτe1 I h)) (he0 I (asymm_of WellOrderingRel h))

  set a : A := (x : A) with ha
  set b : A := ((x⁻¹ : Aˣ) : A) with hb
  have hab : a * b = 1 := x.mul_inv
  have hpq : τ a * τ b = 1 := by rw [← map_mul, hab, map_one]

  have hstable : ∀ I : MaximalSpectrum A, tI I = I →
      IsIntegral O (Ideal.Quotient.mk I.asIdeal a) ∧ IsIntegral O (Ideal.Quotient.mk I.asIdeal b) := by
    intro I hI
    have hle : I.asIdeal ≤ I.asIdeal.comap τ := fun y hy => by
      rw [Ideal.mem_comap, ← hmem, hI]; exact hy
    let ρ := Ideal.quotientMap I.asIdeal τ hle
    have hρ : ∀ y, ρ (Ideal.Quotient.mk I.asIdeal y) = Ideal.Quotient.mk I.asIdeal (τ y) :=
      fun y => Ideal.quotientMap_mk
    have hcomp : (algebraMap O (A ⧸ I.asIdeal)).comp σO = ρ.comp (algebraMap O (A ⧸ I.asIdeal)) := by
      ext r
      change Ideal.Quotient.mk _ (algebraMap O A (σO r)) = ρ (Ideal.Quotient.mk _ (algebraMap O A r))
      rw [hρ, hτO]
    have hρi : ∀ z, IsIntegral O z → IsIntegral O (ρ z) := fun z hz =>
      IsIntegral.map_of_comp_eq σO ρ hcomp hz
    have hmk : ∀ y : A, IsIntegral O y → IsIntegral O (Ideal.Quotient.mk I.asIdeal y) :=
      fun y hy => hy.map (Ideal.Quotient.mkₐ O I.asIdeal)
    have hxa : a = (τ a * a) * τ b := by linear_combination -a * hpq
    have hxb : b = (τ b * b) * τ a := by linear_combination -b * hpq
    haveI := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional K (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    have hX : Ideal.Quotient.mk I.asIdeal a * Ideal.Quotient.mk I.asIdeal b = 1 := by
      rw [← map_mul, hab, map_one]
    have hinv : (Ideal.Quotient.mk I.asIdeal a)⁻¹ = Ideal.Quotient.mk I.asIdeal b :=
      inv_eq_of_mul_eq_one_right hX
    rcases isIntegral_or_isIntegral_inv (O := O) (K := K) (Ideal.Quotient.mk I.asIdeal a) with h | h
    · refine ⟨h, ?_⟩
      rw [hxb, map_mul, ← hρ]
      exact (hmk _ hci).mul (hρi _ h)
    · rw [hinv] at h
      refine ⟨?_, h⟩
      rw [hxa, map_mul, ← hρ]
      exact (hmk _ hc).mul (hρi _ h)
  have haf : IsIntegral O (a * f) ∧ IsIntegral O (b * f) := by
    constructor <;>
    · refine isIntegral_of_residues fun I => ?_
      by_cases hI : tI I = I
      · have h1 : Ideal.Quotient.mk I.asIdeal f = 1 := by
          rw [← map_one (Ideal.Quotient.mk I.asIdeal)]
          exact Ideal.Quotient.eq.2 (hfix I hI)
        rw [map_mul, h1, mul_one]
        first | exact (hstable I hI).1 | exact (hstable I hI).2
      · rw [Ideal.Quotient.eq_zero_iff_mem.2 (I.asIdeal.mul_mem_left _ (hmov I hI))]
        exact isIntegral_zero

  set T : A := a * e + τ b * τ e + f with hT
  set S : A := b * e + τ a * τ e + f with hS
  have hTS : T * S = 1 := by
    rw [hT, hS, hf]
    linear_combination e ^ 2 * hab + τ e ^ 2 * hpq + (2 - a - b) * hee + (2 - τ a - τ b) * hgg +
      (a * τ a + b * τ b - a - b - τ a - τ b + 2) * heg
  have hτT : τ T = S := by
    rw [hT, hS, hf]
    simp only [map_add, map_sub, map_mul, map_one, hτ]
    ring
  have ie : IsIntegral O e := isIntegral_of_mul_self_eq hee
  have ig : IsIntegral O (τ e) := isIntegral_of_mul_self_eq hgg
  refine ⟨Units.mkOfMulEqOne T S hTS, ?_, ?_, ?_⟩
  · change τ T * T = 1
    rw [hτT, mul_comm, hTS]
  · change IsIntegral O (T * b)
    have : T * b = e + (τ b * b) * τ e + b * f := by
      rw [hT]; linear_combination e * hab
    rw [this]
    exact (ie.add (hci.mul ig)).add haf.2
  · change IsIntegral O (S * a)
    have : S * a = e + (τ a * a) * τ e + a * f := by
      rw [hS]; linear_combination e * hab
    rw [this]
    exact (ie.add (hc.mul ig)).add haf.1
end GlobalTheory.UnitAdj
