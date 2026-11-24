-- Prove2me | solution 1 for GlobalTheory.DVRBaseChange.exists_dvr_of_isRadical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:30:12.987815+00:00
-- url     : https://prove2.me/submissions/4d8e6307-dfba-4460-9fdd-83539b16ee41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsUnramifiedExtension
import Theorems.Thm_GlobalTheory_DVRBaseChange_exists_dvr_quotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.DVRBaseChange
namespace GlobalTheory.DVRBaseChange
theorem _root_.solution (S : Type) [CommRing S] (π : S)
    (hrad : (Ideal.span {π}).IsRadical) (hne : Ideal.span {π} ≠ ⊤)
    (hreg : ∀ s, π * s = 0 → s = 0) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (q : S →+* V), Irreducible (q π) := by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hne
  have hpp : p.IsPrime := hp.1.1
  let W := Localization.AtPrime p
  have hm : IsLocalRing.maximalIdeal W = Ideal.span {algebraMap S W π} := by
    have h1 := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes W p _ hp
    rw [← IsLocalization.map_radical p.primeCompl, hrad.radical,
      Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton] at h1
    exact h1.symm
  have hn : ¬ IsNilpotent (algebraMap S W π) := by
    rintro ⟨n, hn⟩
    rw [← map_pow, IsLocalization.map_eq_zero_iff p.primeCompl] at hn
    obtain ⟨⟨s, hs⟩, h⟩ := hn
    have key : ∀ (n : ℕ) (s : S), s * π ^ n = 0 → s = 0 := by
      intro n
      induction n with
      | zero => intro s h; simpa using h
      | succ n ih => intro s h; exact ih s (hreg _ (by linear_combination h))
    exact hs (by rw [key n s h]; exact p.zero_mem)
  obtain ⟨V, i1, i2, i3, q, hq⟩ := exists_dvr_quotient W _ hm hn
  exact ⟨V, i1, i2, i3, q.comp (algebraMap S W), hq⟩
end GlobalTheory.DVRBaseChange
