-- Prove2me | solution 1 for GlobalTheory.NormEq.exists_mul_invol_eq_of_fixed_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:54:11.34136+00:00
-- url     : https://prove2.me/submissions/b8206594-79ac-48b7-9b48-ee6cca3a457c

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulInvolEqOfFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsReducedAdjoinRootOfSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormApproximationFirstLevel
import Theorems.Thm_GlobalTheory_NormEq_eq_zero_of_forall_mem_maxSpec
import Theorems.Thm_GlobalTheory_exists_mul_invol_eq_of_fixed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
open GlobalTheory GlobalTheory.NormEq
namespace GlobalTheory.NormEq
theorem _root_.solution {R : Type} [CommRing R] [Finite R] [IsReduced R]
    (τ : R →+* R) (hτ : ∀ a, τ (τ a) = a) {b : R} (hb : IsUnit (τ b - b)) {x : R} (hx : IsUnit x)
    (hxτ : τ x = x) : ∃ z : R, IsUnit z ∧ z * τ z = x := by
  classical
  haveI : IsArtinianRing R := inferInstance
  have hsurj : Function.Surjective τ := fun a => ⟨τ a, hτ a⟩
  obtain ⟨tI, hmem, htt⟩ : ∃ tI : MaximalSpectrum R → MaximalSpectrum R,
      (∀ I y, y ∈ (tI I).asIdeal ↔ τ y ∈ I.asIdeal) ∧ ∀ I, tI (tI I) = I := by
    have hmax : ∀ I : MaximalSpectrum R, (I.asIdeal.comap τ).IsMaximal := fun I => by
      haveI := I.isMaximal
      exact Ideal.comap_isMaximal_of_surjective τ hsurj
    refine ⟨fun I => ⟨I.asIdeal.comap τ, hmax I⟩, fun I y => Iff.rfl, fun I => ?_⟩
    ext y
    change τ (τ y) ∈ I.asIdeal ↔ y ∈ I.asIdeal
    rw [hτ]
  have hnot : ∀ (I : MaximalSpectrum R) {u : R}, IsUnit u → u ∉ I.asIdeal := fun I u hu hI =>
    I.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hI hu)

  have hfixed : ∀ I : MaximalSpectrum R, ∃ a : R, tI I = I → a * τ a - x ∈ I.asIdeal := by
    intro I
    by_cases hI : tI I = I
    · have hle : I.asIdeal ≤ I.asIdeal.comap τ := fun y hy => by
        rw [Ideal.mem_comap, ← hmem, hI]; exact hy
      haveI := I.isMaximal
      letI : Field (R ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
      haveI : Finite (R ⧸ I.asIdeal) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
      let ρ := Ideal.quotientMap I.asIdeal τ hle
      have hρ : ∀ y, ρ (Ideal.Quotient.mk I.asIdeal y) = Ideal.Quotient.mk I.asIdeal (τ y) :=
        fun y => Ideal.quotientMap_mk
      have hinv : Function.Involutive ρ := fun c => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective c
        rw [hρ, hρ, hτ]
      have hne : ∃ c, ρ c ≠ c := ⟨Ideal.Quotient.mk I.asIdeal b, fun h => by
        rw [hρ, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at h
        exact hnot I hb h⟩
      obtain ⟨a', ha'⟩ := GlobalTheory.exists_mul_invol_eq_of_fixed (R ⧸ I.asIdeal) ρ hinv hne
        (Ideal.Quotient.mk I.asIdeal x) (by rw [hρ, hxτ])
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
      refine ⟨a, fun _ => ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hρ, ha', sub_self]
    · exact ⟨0, fun h => absurd h hI⟩
  choose a ha using hfixed
  let r : MaximalSpectrum R → R := fun I =>
    if WellOrderingRel I (tI I) then x else if WellOrderingRel (tI I) I then 1 else a I
  obtain ⟨z, hz⟩ : ∃ z : R, ∀ I, z - r I ∈ I.asIdeal := by
    refine ⟨(IsArtinianRing.equivPi R).symm (fun I => Ideal.Quotient.mk I.asIdeal (r I)), fun I => ?_⟩
    have h1 := congrFun ((IsArtinianRing.equivPi R).apply_symm_apply
      (fun I => Ideal.Quotient.mk I.asIdeal (r I))) I
    rw [IsArtinianRing.equivPi_apply] at h1
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, sub_self]
  have hτz : ∀ I, τ z - τ (r (tI I)) ∈ I.asIdeal := fun I => by
    rw [← map_sub, ← hmem]; exact hz (tI I)
  have hfix_of : ∀ I, ¬ WellOrderingRel I (tI I) → ¬ WellOrderingRel (tI I) I → tI I = I := fun I h1 h2 => by
    rcases trichotomous_of WellOrderingRel I (tI I) with h | h | h
    · exact absurd h h1
    · exact h.symm
    · exact absurd h h2
  have key : ∀ I : MaximalSpectrum R, z * τ z - x ∈ I.asIdeal ∧ z ∉ I.asIdeal := by
    intro I
    have hzI := hz I
    have hτzI := hτz I
    by_cases h1 : WellOrderingRel I (tI I)
    · have e1 : r I = x := if_pos h1
      have e2 : r (tI I) = 1 := by
        simp only [r, htt]
        rw [if_neg (asymm_of WellOrderingRel h1), if_pos h1]
      rw [e1] at hzI
      rw [e2, map_one] at hτzI
      refine ⟨?_, fun hzm => hnot I hx (by simpa using I.asIdeal.sub_mem hzm hzI)⟩
      have : z * τ z - x = (z - x) * τ z + x * (τ z - 1) := by ring
      rw [this]
      exact I.asIdeal.add_mem (I.asIdeal.mul_mem_right _ hzI) (I.asIdeal.mul_mem_left _ hτzI)
    · by_cases h2 : WellOrderingRel (tI I) I
      · have e1 : r I = 1 := by simp only [r]; rw [if_neg h1, if_pos h2]
        have e2 : r (tI I) = x := by
          simp only [r, htt]
          rw [if_pos h2]
        rw [e1] at hzI
        rw [e2, hxτ] at hτzI
        refine ⟨?_, fun hzm => hnot I isUnit_one (by simpa using I.asIdeal.sub_mem hzm hzI)⟩
        have : z * τ z - x = (z - 1) * τ z + (τ z - x) := by ring
        rw [this]
        exact I.asIdeal.add_mem (I.asIdeal.mul_mem_right _ hzI) hτzI
      · have hI := hfix_of I h1 h2
        have e1 : r I = a I := by simp only [r]; rw [if_neg h1, if_neg h2]
        rw [e1] at hzI
        rw [hI, e1] at hτzI
        have haI := ha I hI
        refine ⟨?_, fun hzm => ?_⟩
        · have : z * τ z - x = (z - a I) * τ z + a I * (τ z - τ (a I)) + (a I * τ (a I) - x) := by ring
          rw [this]
          exact I.asIdeal.add_mem (I.asIdeal.add_mem (I.asIdeal.mul_mem_right _ hzI)
            (I.asIdeal.mul_mem_left _ hτzI)) haI
        · have haM : a I ∈ I.asIdeal := by simpa using I.asIdeal.sub_mem hzm hzI
          exact hnot I hx (by simpa using I.asIdeal.sub_mem (I.asIdeal.mul_mem_right (τ (a I)) haM) haI)
  refine ⟨z, ?_, sub_eq_zero.1 (eq_zero_of_forall_mem_maxSpec fun I => (key I).1)⟩
  by_contra hu
  obtain ⟨M, hM, hzM⟩ := exists_max_ideal_of_mem_nonunits (show z ∈ nonunits R from hu)
  exact (key ⟨M, hM⟩).2 hzM
end GlobalTheory.NormEq
