-- Prove2me | solution 1 for IsRegularLocalRing.exists_isDiscreteValuationRing_ringHom_comp_eq_of_ringKrullDim_le_two_of_isAdicComplete_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/5220f7d6-8b11-5118-94e3-23f2725c34e9

import Mathlib
import Theorems.Thm_IsRegularLocalRing_exists_notMem_sq_charZero_quotient_span_singleton
import Theorems.Thm_IsRegularLocalRing_quotient_span_singleton_isAdicComplete_of_notMem_sq
import Theorems.Thm_IsRegularLocalRing_isDomain_and_isIntegrallyClosed_of_ringKrullDim_le_one
import Theorems.Thm_IsRegularLocalRing_isDomain_and_isIntegrallyClosed_adicCompletion_of_ringKrullDim_eq_two
import Theorems.Thm_IsRegularLocalRing_isRegularRing_of_ringKrullDim_le_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_exists_isDiscreteValuationRing_ringHom_comp_eq_of_ringKrullDim_le_two_of_isAdicComplete_of_natCast_ne_zero
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal"

set_option autoImplicit false

open IsLocalRing

namespace HullToDVRAux

theorem isDiscreteValuationRing_of_ringKrullDim_eq_one (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (h : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  have hnf : ¬ IsField R := by
    intro hf
    have h0 : ringKrullDim R = 0 := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, (isField_iff_maximalIdeal_eq).1 hf]
      simp
    rw [h0] at h; exact absurd h (by decide)
  have hcot : Module.finrank (ResidueField R) (CotangentSpace R) = 1 := by
    have := (IsRegularLocalRing.iff_finrank_cotangentSpace R).1 inferInstance
    rw [h] at this
    exact_mod_cast this
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 0 5).mpr hcot

end HullToDVRAux

open HullToDVRAux in
theorem solution
    (Ry : Type) [CommRing Ry] [IsRegularLocalRing Ry] (hd : ringKrullDim Ry ≤ 2) [IsAdicComplete (maximalIdeal Ry) Ry]
    (p : ℕ) [Fact p.Prime] (hp : ((p : ℕ) : Ry) ≠ 0)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (ι₀ : (Ry ⧸ maximalIdeal Ry ^ (0 + 1)) →+* k) (hι₀ : Function.Bijective ι₀) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (_ : CharZero R)
      (ψ : Ry →+* R) (φ : R →+* k),
      Function.Surjective φ ∧ IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
      φ.comp ψ = ι₀.comp (Ideal.Quotient.mk (maximalIdeal Ry ^ (0 + 1))) := by
  classical

  let r : Ry →+* k := ι₀.comp (Ideal.Quotient.mk (maximalIdeal Ry ^ (0 + 1)))
  have hpow : maximalIdeal Ry ^ (0 + 1) = maximalIdeal Ry := by rw [zero_add, pow_one]
  have hr_surj : Function.Surjective r := hι₀.2.comp Ideal.Quotient.mk_surjective
  have hr0 : ∀ a ∈ maximalIdeal Ry, r a = 0 := fun a ha => by
    show ι₀ (Ideal.Quotient.mk _ a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (hpow.symm ▸ ha), map_zero]
  have hrker : ∀ a, r a = 0 → a ∈ maximalIdeal Ry := fun a ha => by
    have : Ideal.Quotient.mk (maximalIdeal Ry ^ (0 + 1)) a = 0 := hι₀.1 (by rw [map_zero]; exact ha)
    rw [Ideal.Quotient.eq_zero_iff_mem, hpow] at this; exact this

  have hunit : ∀ m : ℕ, ¬ p ∣ m → IsUnit (m : Ry) := by
    intro m hm
    by_contra hu
    have hmem : (m : Ry) ∈ maximalIdeal Ry := (mem_maximalIdeal _).2 hu
    have := hr0 _ hmem
    rw [map_natCast, CharP.cast_eq_zero_iff k p] at this
    exact hm this
  have hpmem : (p : Ry) ∈ maximalIdeal Ry := hrker _ (by rw [map_natCast, CharP.cast_eq_zero])
  have hMne : maximalIdeal Ry ≠ ⊥ := fun h => hp (by rw [h] at hpmem; exact hpmem)
  have hcharZero : IsDomain Ry → CharZero Ry := by
    intro hdom
    apply charZero_of_inj_zero
    intro n hn
    by_contra hn0
    obtain ⟨a, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p (Fact.out : p.Prime).ne_one
    rw [Nat.cast_mul, Nat.cast_pow, (hunit m hpm).mul_left_eq_zero] at hn
    exact hp (pow_eq_zero_iff'.1 hn).1

  set d := (maximalIdeal Ry).spanFinrank with hd_def
  have hdim : ringKrullDim Ry = d := IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  have hd2 : d ≤ 2 := by rw [hdim] at hd; exact_mod_cast hd
  have hd0 : d ≠ 0 := by
    intro h0
    apply hMne
    rw [← Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _), ← hd_def, h0]
  interval_cases d
  · exact absurd rfl hd0
  ·
    have hdim1 : ringKrullDim Ry = 1 := by rw [hdim]; rfl
    haveI : IsDomain Ry := (IsRegularLocalRing.isDomain_and_isIntegrallyClosed_of_ringKrullDim_le_one Ry hdim1.le).1
    haveI : CharZero Ry := hcharZero inferInstance
    exact ⟨Ry, inferInstance, inferInstance, isDiscreteValuationRing_of_ringKrullDim_eq_one Ry hdim1, inferInstance,
      RingHom.id Ry, r, hr_surj, inferInstance, by rfl⟩
  ·
    have hdim2 : ringKrullDim Ry = 2 := by rw [hdim]; rfl
    haveI : IsRegularRing Ry := IsRegularLocalRing.isRegularRing_of_ringKrullDim_le_two Ry hdim2.le
    haveI : IsDomain Ry := by
      have hc := (IsRegularLocalRing.isDomain_and_isIntegrallyClosed_adicCompletion_of_ringKrullDim_eq_two Ry hdim2).1
      exact Function.Injective.isDomain (AdicCompletion.ofAlgEquiv (maximalIdeal Ry)).toRingHom
        (AdicCompletion.ofAlgEquiv (maximalIdeal Ry)).injective
    haveI : CharZero Ry := hcharZero inferInstance
    obtain ⟨x, hx, hx2, hx0, hxcz⟩ :=
      IsRegularLocalRing.exists_notMem_sq_charZero_quotient_span_singleton Ry hdim2.ge
    haveI : Nontrivial (Ry ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.2 (fun h => (mem_maximalIdeal _).1 hx (Ideal.span_singleton_eq_top.1 h))
    haveI : IsLocalRing (Ry ⧸ Ideal.span {x}) := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    obtain ⟨hreg, hdom, hdimq, hcomp, -⟩ :=
      IsRegularLocalRing.quotient_span_singleton_isAdicComplete_of_notMem_sq Ry x hx hx2 hx0
    haveI := hreg; haveI := hdom; haveI := hxcz
    have hdimq1 : ringKrullDim (Ry ⧸ Ideal.span {x}) = 1 := by
      rw [hdim2, ← IsRegularLocalRing.spanFinrank_maximalIdeal] at hdimq
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal]
      have : (maximalIdeal (Ry ⧸ Ideal.span {x})).spanFinrank + 1 = 2 := by exact_mod_cast hdimq
      have : (maximalIdeal (Ry ⧸ Ideal.span {x})).spanFinrank = 1 := by omega
      rw [this]; rfl
    refine ⟨Ry ⧸ Ideal.span {x}, inferInstance, hdom, isDiscreteValuationRing_of_ringKrullDim_eq_one _ hdimq1, hxcz,
      Ideal.Quotient.mk _, Ideal.Quotient.lift (Ideal.span {x}) r ?_, ?_, hcomp, ?_⟩
    · intro a ha
      exact hr0 a ((Ideal.span_singleton_le_iff_mem _).2 hx ha)
    · exact Ideal.Quotient.lift_surjective_of_surjective _ _ hr_surj
    · ext a; rfl

end S_IsRegularLocalRing_exists_isDiscreteValuationRing_ringHom_comp_eq_of_ringKrullDim_le_two_of_isAdicComplete_of_natCast_ne_zero
end P2MW
export P2MW.S_IsRegularLocalRing_exists_isDiscreteValuationRing_ringHom_comp_eq_of_ringKrullDim_le_two_of_isAdicComplete_of_natCast_ne_zero (solution)
