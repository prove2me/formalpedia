-- Prove2me | solution 1 for GlobalTheory.FlatFibreRegular.mem_of_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:57:55.91737+00:00
-- url     : https://prove2.me/submissions/83fde72e-23a9-4bba-9d31-a081eae5b4c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinim
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
open GlobalTheory GlobalTheory.FlatFibreRegular
namespace GlobalTheory.FlatFibreRegular
theorem _root_.solution {B : Type} [CommRing B] (u : Ideal B) [u.IsPrime] (I₀ : Ideal B)
    (hrad : I₀.IsRadical) (g : B) (hg : ∀ Q ∈ I₀.minimalPrimes, Q ≤ u → g ∉ Q)
    (y : Localization.AtPrime u)
    (hy : algebraMap B _ g * y ∈ I₀.map (algebraMap B (Localization.AtPrime u))) :
    y ∈ I₀.map (algebraMap B (Localization.AtPrime u)) := by
  set L := Localization.AtPrime u
  set J := I₀.map (algebraMap B L) with hJdef
  have hJrad : J.IsRadical := by
    rintro x ⟨n, hn⟩
    obtain ⟨⟨b, s⟩, hx⟩ := IsLocalization.mk'_surjective u.primeCompl x
    dsimp only at hx
    subst hx
    have h1 : algebraMap B L (b ^ n) ∈ J := by
      have := Ideal.mul_mem_right (algebraMap B L ((s ^ n : u.primeCompl) : B)) J hn
      rwa [← IsLocalization.mk'_pow, IsLocalization.mk'_spec] at this
    obtain ⟨t, ht, htb⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff u.primeCompl L _ _).1 h1
    have h2 : t * b ∈ I₀ := hrad ⟨n + 1, by
      rw [show (t * b) ^ (n + 1) = (t ^ n * b) * (t * b ^ n) by ring]
      exact Ideal.mul_mem_left _ _ htb⟩
    have h3 : algebraMap B L b ∈ J := by
      have h4 := Ideal.mem_map_of_mem (algebraMap B L) h2
      rw [map_mul] at h4
      obtain ⟨t', ht'⟩ := (IsLocalization.map_units L (⟨t, ht⟩ : u.primeCompl)).exists_left_inv
      have := Ideal.mul_mem_left _ t' h4
      rwa [← mul_assoc, ht', one_mul] at this
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ h3
  by_contra hyJ
  rw [← hJrad.radical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf] at hyJ
  push_neg at hyJ
  obtain ⟨P, hP, hyP⟩ := hyJ
  haveI : P.IsPrime := hP.1.1
  have hgP : algebraMap B L g ∈ P := ((Ideal.IsPrime.mem_or_mem inferInstance (hP.1.2 hy)).resolve_right hyP)
  set Q := P.comap (algebraMap B L)
  have hQu : Q ≤ u := by
    intro x hx
    by_contra hxu
    exact (Ideal.IsPrime.ne_top inferInstance : P ≠ ⊤)
      (Ideal.eq_top_of_isUnit_mem _ hx (IsLocalization.map_units L (⟨x, hxu⟩ : u.primeCompl)))
  have hQmin : Q ∈ I₀.minimalPrimes := by
    refine ⟨⟨inferInstance, Ideal.map_le_iff_le_comap.1 hP.1.2⟩, fun Q' hQ' hle => ?_⟩
    haveI : Q'.IsPrime := hQ'.1
    have hd : Disjoint (u.primeCompl : Set B) (Q' : Set B) :=
      Set.disjoint_left.2 fun x hxM hxI => hxM (hQu (hle hxI))
    haveI := IsLocalization.isPrime_of_isPrime_disjoint u.primeCompl L Q' hQ'.1 hd
    have hc := IsLocalization.comap_map_of_isPrime_disjoint u.primeCompl L hQ'.1 hd
    have hPP : P ≤ Q'.map (algebraMap B L) :=
      hP.2 ⟨inferInstance, Ideal.map_mono hQ'.2⟩ (Ideal.map_le_iff_le_comap.2 hle)
    intro x hx
    rw [← hc]
    exact hPP hx
  exact hg Q hQmin hQu hgP
end GlobalTheory.FlatFibreRegular
