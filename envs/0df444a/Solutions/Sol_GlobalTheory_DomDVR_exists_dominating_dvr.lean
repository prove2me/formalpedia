-- Prove2me | solution 1 for GlobalTheory.DomDVR.exists_dominating_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:24:59.64973+00:00
-- url     : https://prove2.me/submissions/7547da45-d1ad-4ecd-a838-3dce47ccfc25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDominatingDvrContainingFinset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.DomDVR
set_option maxHeartbeats 1000000
namespace GlobalTheory.DomDVR
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] (T' : Subring F), IsDiscreteValuationRing T' → ∀ (s : Finset F), (1 : F) ∈ Submodule.span T' (s : Set F) → (∀ x ∈ s, ∀ y ∈ s, x * y ∈ Submodule.span T' (s : Set F)) → ∃ T'' : Subring F, IsDiscreteValuationRing T'' ∧ T' ≤ T'' ∧ (∀ x ∈ s, x ∈ T'') ∧ (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) ∧ (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) := by
  intro F _ _ T' hT s h1 hmul
  classical
  haveI := hT
  set A := Submodule.span T' (s : Set F) with hA
  have hAmul : ∀ x y, x ∈ A → y ∈ A → x * y ∈ A := by
    intro x y hx hy
    have : A * A ≤ A := by
      rw [hA, Submodule.span_mul_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact hmul a ha b hb
    exact this (Submodule.mul_mem_mul hx hy)
  have hsm : ∀ d ∈ T', ∀ a ∈ A, d * a ∈ A := fun d hd a ha => A.smul_mem ⟨d, hd⟩ ha
  let Asub : Subalgebra T' F := A.toSubalgebra h1 hAmul
  have hint : ∀ x ∈ s, IsIntegral T' x := fun x hx =>
    IsIntegral.of_mem_of_fg Asub (Submodule.fg_span s.finite_toSet) x (Submodule.subset_span hx)
  let K := FractionRing T'
  have hι : Function.Injective (T'.subtype) := Subtype.val_injective
  letI : Algebra K F := (IsFractionRing.lift (K := K) hι).toAlgebra
  haveI : IsScalarTower T' K F :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsFractionRing.lift_algebraMap (K := K) hι x).symm)
  have hintK : ∀ x ∈ (s : Set F), IsIntegral K x := fun x hx => (hint x hx).tower_top
  let L := IntermediateField.adjoin K (s : Set F)
  haveI : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin hintK
  haveI : CharZero K := (algebraMap K F).charZero
  haveI : Algebra.IsSeparable K L := inferInstance
  let C := integralClosure T' L
  haveI : IsDedekindDomain C := IsIntegralClosure.isDedekindDomain T' K L C

  have hLF : ∀ a : T', ((algebraMap T' L a : L) : F) = a := by
    intro a
    rw [IsScalarTower.algebraMap_apply T' K L]
    show algebraMap K F (algebraMap T' K a) = a
    exact IsFractionRing.lift_algebraMap (K := K) hι a
  have hcoe : ∀ a : T', (((algebraMap T' C a : C) : L) : F) = a := by
    intro a
    rw [← hLF a, IsScalarTower.algebraMap_apply T' C L]
    rfl
  have hinjC : Function.Injective (algebraMap T' C) := fun a b h => Subtype.val_injective (by
    have := congrArg (fun c : C => ((c : L) : F)) h
    simpa only [hcoe] using this)
  obtain ⟨P, hPmax, hPm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := C) (maximalIdeal T')
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinjC]; exact bot_le)
  haveI : P.IsPrime := hPmax.isPrime
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    apply IsDiscreteValuationRing.not_a_field T'
    rw [← hPm, Ideal.comap_bot_of_injective _ hinjC]
  let Loc := Localization.AtPrime P
  haveI : IsDiscreteValuationRing Loc :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hPbot Loc
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap C L y) := fun y =>
    isUnit_iff_ne_zero.2 fun h => y.2 (by
      rw [show (y : C) = 0 from Subtype.ext (by simpa using h)]; exact P.zero_mem)
  let ψ : Loc →+* L := IsLocalization.lift (M := P.primeCompl) hunit
  have hψ : Function.Injective ψ := (IsLocalization.lift_injective_iff hunit).2 fun x y =>
    ⟨fun h => by rw [IsLocalization.injective Loc P.primeCompl_le_nonZeroDivisors h], fun h => by rw [Subtype.val_injective h]⟩
  let φ : Loc →+* F := (algebraMap L F).comp ψ
  have hφ : Function.Injective φ := fun a b h => hψ ((algebraMap L F).injective h)
  have hφc : ∀ c : C, φ (algebraMap C Loc c) = ((c : L) : F) := by
    intro c
    show ((ψ (algebraMap C Loc c) : L) : F) = _
    rw [IsLocalization.lift_eq]
    rfl
  let T'' := φ.range
  let e : Loc ≃+* T'' := RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun a b h => hφ (by simpa only [RingHom.coe_rangeRestrict] using congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
  refine ⟨T'', IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact RingHom.mem_range.2 ⟨algebraMap C Loc (algebraMap T' C ⟨x, hx⟩), by rw [hφc, hcoe]⟩
  · intro x hx
    have hxL : x ∈ L := IntermediateField.subset_adjoin K _ hx
    have hxC : (⟨x, hxL⟩ : L) ∈ C := by
      rw [mem_integralClosure_iff]
      let f : L →ₐ[T'] F := { toRingHom := algebraMap L F, commutes' := fun a => hLF a }
      exact (isIntegral_algHom_iff f (algebraMap L F).injective).1 (hint x hx)
    exact RingHom.mem_range.2 ⟨algebraMap C Loc ⟨⟨x, hxL⟩, hxC⟩, by rw [hφc]⟩
  · rintro x hx ⟨y, hy, hxy⟩
    by_contra hne
    have hnu : (⟨x, hx⟩ : T') ∈ maximalIdeal T' := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      exact hne ⟨b, b.2, congrArg Subtype.val hb⟩
    have hP : algebraMap T' C ⟨x, hx⟩ ∈ P := by
      rw [← hPm] at hnu; exact hnu
    have hmax : algebraMap C Loc (algebraMap T' C ⟨x, hx⟩) ∈ maximalIdeal Loc :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff Loc P _).2 hP
    obtain ⟨z, rfl⟩ := RingHom.mem_range.1 hy
    apply (IsLocalRing.mem_maximalIdeal _).1 hmax
    refine isUnit_iff_exists_inv.2 ⟨z, hφ ?_⟩
    rw [map_mul, map_one, hφc, hcoe]; exact hxy
  · let M : Subalgebra K F :=
      { carrier := {y | ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ A}
        mul_mem' := by
          rintro a b ⟨d1, hd1, hd1', ha⟩ ⟨d2, hd2, hd2', hb⟩
          exact ⟨d1 * d2, T'.mul_mem hd1 hd2, mul_ne_zero hd1' hd2', by
            rw [show d1 * d2 * (a * b) = (d1 * a) * (d2 * b) by ring]; exact hAmul _ _ ha hb⟩
        add_mem' := by
          rintro a b ⟨d1, hd1, hd1', ha⟩ ⟨d2, hd2, hd2', hb⟩
          exact ⟨d1 * d2, T'.mul_mem hd1 hd2, mul_ne_zero hd1' hd2', by
            rw [show d1 * d2 * (a + b) = d2 * (d1 * a) + d1 * (d2 * b) by ring]
            exact A.add_mem (hsm _ hd2 _ ha) (hsm _ hd1 _ hb)⟩
        algebraMap_mem' := by
          intro k
          obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors T') k
          have hb : ((b : T') : F) ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero b (Subtype.ext h)
          refine ⟨(b : T'), (b : T').2, hb, ?_⟩
          have e1 : algebraMap K F (IsLocalization.mk' K a b) = (a : F) / ((b : T') : F) :=
            IsFractionRing.lift_mk' hι a b
          have e2 : ((b : T') : F) * ((a : F) / ((b : T') : F)) = a := by field_simp
          rw [e1, e2]
          simpa using hsm _ a.2 _ h1 }
    have hLM : ∀ y ∈ L, y ∈ M := by
      intro y hy
      have e := IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (F := K) (S := (s : Set F))
        (fun x hx => (hintK x hx).isAlgebraic)
      have hy' : y ∈ Algebra.adjoin K (s : Set F) := by rw [← e]; exact hy
      refine (Algebra.adjoin_le ?_ : Algebra.adjoin K (s : Set F) ≤ M) hy'
      intro x hx
      exact ⟨1, T'.one_mem, one_ne_zero, by rw [one_mul]; exact Submodule.subset_span hx⟩
    intro y hy
    obtain ⟨z, rfl⟩ := RingHom.mem_range.1 hy
    exact hLM _ (ψ z).2
end GlobalTheory.DomDVR
