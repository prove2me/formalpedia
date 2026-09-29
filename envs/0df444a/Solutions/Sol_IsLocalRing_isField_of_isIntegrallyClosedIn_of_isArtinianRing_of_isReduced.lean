-- Prove2me | solution 1 for IsLocalRing.isField_of_isIntegrallyClosedIn_of_isArtinianRing_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/8ef72be0-9ffe-5751-8ed5-48a6b8bfc8c7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_isField_of_isIntegrallyClosedIn_of_isArtinianRing_of_isReduced

set_option autoImplicit false

open Polynomial in
theorem solution
    {B F : Type*} [CommRing B] [IsLocalRing B] [CommRing F] [Nontrivial F] [Algebra B F]
    [IsArtinianRing F] [IsReduced F] (h : IsIntegrallyClosedIn B F) :
    IsField F := by
  classical
  haveI : IsIntegrallyClosedIn B F := h

  have hidem : ∀ e : F, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    have hint : IsIntegral B e := by
      refine ⟨X ^ 2 - X, ?_, ?_⟩
      · exact (monic_X_pow 2).sub_of_left (by
          rw [degree_X_pow, degree_X]; norm_num)
      · simp [eval₂_sub, eval₂_pow, eval₂_X, pow_two, he.eq]
    obtain ⟨b, hb⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := B) (A := F)).mp hint
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self b with hu | hu
    · right
      have heu : IsUnit e := hb ▸ hu.map (algebraMap B F)
      obtain ⟨u, rfl⟩ := heu
      have := he.eq

      have h1 : (u : F) = 1 := by
        have := congrArg (fun x => (↑u⁻¹ : F) * x) this
        simpa [← mul_assoc, Units.inv_mul] using this
      exact h1
    · left
      have heu : IsUnit (1 - e) := by
        have := hu.map (algebraMap B F)
        simpa [map_sub, hb] using this
      have he' : IsIdempotentElem (1 - e) := he.one_sub
      obtain ⟨u, hu'⟩ := heu
      have h1 : (1 - e) = 1 := by
        have hh := he'.eq
        rw [← hu'] at hh ⊢
        have := congrArg (fun x => (↑u⁻¹ : F) * x) hh
        simpa [← mul_assoc, Units.inv_mul] using this
      have : e = 0 := by
        have := congrArg (fun x => 1 - x) h1
        simpa using this
      exact this

  let φ := IsArtinianRing.equivPi F
  have hsub : Subsingleton (MaximalSpectrum F) := by
    refine ⟨fun I J => ?_⟩
    by_contra hIJ
    let e : F := φ.symm (Pi.single I 1)
    have he : IsIdempotentElem e := by
      show φ.symm (Pi.single I 1) * φ.symm (Pi.single I 1) = φ.symm (Pi.single I 1)
      rw [← map_mul]
      congr 1
      ext K
      by_cases hK : K = I
      · subst hK; simp
      · simp [Pi.single_apply, hK]
    rcases hidem e he with h0 | h1
    · have : (Pi.single I (1 : F ⧸ I.asIdeal) : ∀ K : MaximalSpectrum F, F ⧸ K.asIdeal) = 0 := by
        have := congrArg φ h0
        simpa [e] using this
      have := congrFun this I
      simp at this
    · have : (Pi.single I (1 : F ⧸ I.asIdeal) : ∀ K : MaximalSpectrum F, F ⧸ K.asIdeal) = 1 := by
        have := congrArg φ h1
        simpa [e] using this
      have := congrFun this J
      rw [Pi.single_eq_of_ne (fun h => hIJ h.symm)] at this
      simp at this

  obtain ⟨M, hM⟩ := Ideal.exists_maximal F
  let I0 : MaximalSpectrum F := ⟨M, hM⟩

  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  have hunit : IsUnit (φ a) := by
    rw [Pi.isUnit_iff]
    intro K
    have hK : K = I0 := Subsingleton.elim _ _

    have hne : φ a K ≠ 0 := by
      intro hz
      apply ha
      have : φ a = 0 := by
        funext K'
        have : K' = K := Subsingleton.elim _ _
        subst this; simpa using hz
      simpa using congrArg φ.symm this
    letI : Field (F ⧸ K.asIdeal) := Ideal.Quotient.field K.asIdeal
    exact isUnit_iff_ne_zero.mpr hne
  have : IsUnit a := by
    have := hunit.map φ.symm
    simpa using this
  obtain ⟨u, rfl⟩ := this
  exact ⟨↑u⁻¹, by simp⟩

end S_IsLocalRing_isField_of_isIntegrallyClosedIn_of_isArtinianRing_of_isReduced
end P2MW
export P2MW.S_IsLocalRing_isField_of_isIntegrallyClosedIn_of_isArtinianRing_of_isReduced (solution)
