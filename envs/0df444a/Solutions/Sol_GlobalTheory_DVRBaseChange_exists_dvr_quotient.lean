-- Prove2me | solution 1 for GlobalTheory.DVRBaseChange.exists_dvr_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:35.313795+00:00
-- url     : https://prove2.me/submissions/d99ee9c1-2adb-406e-9ced-1b7f7e95d7c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsUnramifiedExtension

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
theorem _root_.solution (W : Type) [CommRing W] [IsLocalRing W] (π : W)
    (hm : IsLocalRing.maximalIdeal W = Ideal.span {π}) (hπ : ¬ IsNilpotent π) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (q : W →+* V), Irreducible (q π) := by
  classical
  have hnu : ∀ x : W, ¬ IsUnit x ↔ π ∣ x := fun x => by
    rw [← Ideal.mem_span_singleton, ← hm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  let J : Ideal W := ⨅ n : ℕ, Ideal.span {π ^ n}
  have hJ : ∀ x, x ∈ J ↔ ∀ n : ℕ, π ^ n ∣ x := fun x => by
    simp only [J, Ideal.mem_iInf, Ideal.mem_span_singleton]
  have hpow : ∀ n : ℕ, π ^ n ∉ J := by
    intro n hn
    obtain ⟨y, hy⟩ := (hJ _).1 hn (n + 1)
    have hu : IsUnit (1 - π * y) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ((hnu _).2 (dvd_mul_right _ _))
    refine hπ ⟨n, ?_⟩
    have : π ^ n * (1 - π * y) = 0 := by linear_combination hy
    exact (hu.mul_left_eq_zero).1 this
  have hfac : ∀ x, x ∉ J → ∃ (n : ℕ) (u : W), IsUnit u ∧ x = π ^ n * u := by
    intro x hx
    have hex : ∃ n : ℕ, ¬ π ^ (n + 1) ∣ x := by
      by_contra hc
      push Not at hc
      exact hx ((hJ x).2 fun n => (pow_dvd_pow π (Nat.le_succ n)).trans (hc n))
    have h1 : π ^ (Nat.find hex) ∣ x := by
      rcases h : Nat.find hex with _ | m
      · simp
      · by_contra hc
        exact Nat.find_min hex (m := m) (by omega) hc
    obtain ⟨u, hu⟩ := h1
    refine ⟨_, u, ?_, hu⟩
    by_contra hc
    obtain ⟨v, rfl⟩ := (hnu u).1 hc
    exact Nat.find_spec hex ⟨v, hu.trans (by ring)⟩
  have hprime : J.IsPrime := by
    refine ⟨fun h => hpow 0 (h ▸ Submodule.mem_top), fun {x y} hxy => ?_⟩
    by_contra hc
    push Not at hc
    obtain ⟨n, u, hu, rfl⟩ := hfac x hc.1
    obtain ⟨m, v, hv, rfl⟩ := hfac y hc.2
    refine hpow (n + m) ?_
    rw [← J.mul_unit_mem_iff_mem (hu.mul hv)]
    convert hxy using 1
    ring
  have hdom : IsDomain (W ⧸ J) := Ideal.Quotient.isDomain J
  have hloc : IsLocalRing (W ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hirr : Irreducible (Ideal.Quotient.mk J π) := by
    refine IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ ?_ ?_
    · rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
      simpa using hpow 1
    · rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
        Ideal.Quotient.mk_surjective, hm, Ideal.map_span, Set.image_singleton]
  refine ⟨W ⧸ J, inferInstance, hdom,
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hirr, ?_⟩,
    Ideal.Quotient.mk J, hirr⟩
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n, u, hu, rfl⟩ := hfac x (fun h => hx (Ideal.Quotient.eq_zero_iff_mem.2 h))
  refine ⟨n, ?_⟩
  rw [map_mul, map_pow]
  exact associated_mul_unit_right _ _ (hu.map _)
end GlobalTheory.DVRBaseChange
