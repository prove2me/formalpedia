-- Prove2me | solution 1 for ModularCurve.IgusaScheme.chartAlg_eq_and_mem_iff_and_exists_ringEquiv_quotient_span_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/cf6da94c-31c0-565e-b302-3fdc3475a245

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isLocalization_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_chartAlg_eq_and_mem_iff_and_exists_ringEquiv_quotient_span_natCast

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "ModularCurve P2MW.S_ModularCurve_IgusaScheme_chartAlg_eq_and_mem_iff_and_exists_ringEquiv_quotient_span_natCast.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_chartAlg_eq_and_mem_iff_and_exists_ringEquiv_quotient_span_natCast.ModularCurve.IgusaScheme AlgebraicCurve"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme.chartAlg IgusaScheme modularFunctionFieldFull"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "chartAlg"
namespace ChartTransport
p2m_open "ModularCurve.IgusaScheme ModularCurve"

variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

theorem isScalarTower_int : IsScalarTower ℤ ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) :=
  IsScalarTower.of_algebraMap_eq fun z => by
    have h1 : algebraMap ℤ ↥(modularFunctionFieldFull N) z = (z : ↥(modularFunctionFieldFull N)) := eq_intCast _ z
    have h2 : algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ) z = (z : ↥(GaloisRep.ratLocalizedAt ℓ)) := eq_intCast _ z
    rw [h1, h2, map_intCast]

theorem span_isPrime : (Ideal.span {(ℓ : ℤ)}).IsPrime := by
  have hq : Prime (ℓ : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using (Fact.out : ℓ.Prime)
  exact (Ideal.span_singleton_prime hq.ne_zero).mpr hq

theorem chartAlg_eq (S : Set ↥(modularFunctionFieldFull N)) :
    IgusaScheme.chartAlg N ℓ S = TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) S :=
  SetLike.ext fun _ => Iff.rfl

theorem isUnit_algebraMap_of_not_dvd {s : ℤ} (hs : ¬ ((ℓ : ℤ) ∣ s)) : IsUnit (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ) s) := by
  haveI := span_isPrime ℓ
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := ℓ) Fact.out
  refine IsLocalization.map_units (M := (Ideal.span {(ℓ : ℤ)}).primeCompl) ↥(GaloisRep.ratLocalizedAt ℓ) ⟨s, ?_⟩
  simpa [Ideal.mem_span_singleton] using hs

theorem coe_natCast_chartAlg_int (S : Set ↥(modularFunctionFieldFull N)) : (((ℓ : ℕ) : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S)) : ↥(modularFunctionFieldFull N)) = (ℓ : ↥(modularFunctionFieldFull N)) :=
  map_natCast (TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S).val ℓ

theorem coe_intCast_chartAlg_int (S : Set ↥(modularFunctionFieldFull N)) (z : ℤ) : (((z : ℤ) : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S)) : ↥(modularFunctionFieldFull N)) = (z : ↥(modularFunctionFieldFull N)) :=
  map_intCast (TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S).val z

theorem coe_natCast_chartAlg (S : Set ↥(modularFunctionFieldFull N)) : (((ℓ : ℕ) : ↥(IgusaScheme.chartAlg N ℓ S)) : ↥(modularFunctionFieldFull N)) = (ℓ : ↥(modularFunctionFieldFull N)) :=
  map_natCast (IgusaScheme.chartAlg N ℓ S).val ℓ

theorem coe_intCast_chartAlg (S : Set ↥(modularFunctionFieldFull N)) (z : ℤ) : (((z : ℤ) : ↥(IgusaScheme.chartAlg N ℓ S)) : ↥(modularFunctionFieldFull N)) = (z : ↥(modularFunctionFieldFull N)) :=
  map_intCast (IgusaScheme.chartAlg N ℓ S).val z

theorem mem_chartAlg_iff_exists (S : Set ↥(modularFunctionFieldFull N)) (x : ↥(modularFunctionFieldFull N)) :
    x ∈ IgusaScheme.chartAlg N ℓ S ↔
      ∃ (a : ↥(modularFunctionFieldFull N)) (s : ℤ), a ∈ TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S ∧ ¬ ((ℓ : ℤ) ∣ s) ∧ (s : ↥(modularFunctionFieldFull N)) * x = a := by
  haveI := isScalarTower_int N ℓ
  haveI := span_isPrime ℓ
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := ℓ) Fact.out
  letI : Algebra ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S) ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) S) :=
    (TwoChartIntegralModel.chartBaseChange ℤ ↥(modularFunctionFieldFull N) ↥(GaloisRep.ratLocalizedAt ℓ) S).toAlgebra
  have hloc := TwoChartIntegralModel.isLocalization_chartAlg ℤ ↥(modularFunctionFieldFull N) ↥(GaloisRep.ratLocalizedAt ℓ) (Ideal.span {(ℓ : ℤ)}).primeCompl S
  rw [chartAlg_eq]
  constructor
  · intro hx

    obtain ⟨⟨a, ⟨_, ⟨s, hs, rfl⟩⟩⟩, h⟩ := IsLocalization.surj ((Ideal.span {(ℓ : ℤ)}).primeCompl.map
      (algebraMap ℤ ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S))) (⟨x, hx⟩ : ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) S))
    refine ⟨(a : ↥(modularFunctionFieldFull N)), s, a.2, ?_, ?_⟩
    · simpa [Ideal.mem_span_singleton] using hs
    ·
      have := congrArg (fun y : ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) S) => (y : ↥(modularFunctionFieldFull N))) h
      simp only [Subalgebra.coe_mul, RingHom.algebraMap_toAlgebra, TwoChartIntegralModel.coe_chartBaseChange] at this

      have hs' : ((algebraMap ℤ ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S) s : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S)) : ↥(modularFunctionFieldFull N)) = (s : ↥(modularFunctionFieldFull N)) := by
        rw [eq_intCast]; exact map_intCast (TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S).val s
      rw [hs'] at this
      rw [mul_comm]; exact this
  · rintro ⟨a, s, ha, hs, h⟩

    obtain ⟨t, ht⟩ := isUnit_algebraMap_of_not_dvd ℓ hs
    have ha' : a ∈ TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) S :=
      TwoChartIntegralModel.chartAlg_le_chartAlg ℤ ↥(modularFunctionFieldFull N) ↥(GaloisRep.ratLocalizedAt ℓ) S ha
    have htF : algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) (t : ↥(GaloisRep.ratLocalizedAt ℓ)) = (s : ↥(modularFunctionFieldFull N)) := by
      rw [ht, ← IsScalarTower.algebraMap_apply ℤ ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) s, eq_intCast]
    have hinv : algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) ((t⁻¹ : (↥(GaloisRep.ratLocalizedAt ℓ))ˣ) : ↥(GaloisRep.ratLocalizedAt ℓ)) * algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) (t : ↥(GaloisRep.ratLocalizedAt ℓ)) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hx : x = ((t⁻¹ : (↥(GaloisRep.ratLocalizedAt ℓ))ˣ) : ↥(GaloisRep.ratLocalizedAt ℓ)) • a := by
      rw [Algebra.smul_def]
      calc x = (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) ((t⁻¹ : (↥(GaloisRep.ratLocalizedAt ℓ))ˣ) : ↥(GaloisRep.ratLocalizedAt ℓ)) * algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) (t : ↥(GaloisRep.ratLocalizedAt ℓ))) * x := by
              rw [hinv, one_mul]
        _ = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) ((t⁻¹ : (↥(GaloisRep.ratLocalizedAt ℓ))ˣ) : ↥(GaloisRep.ratLocalizedAt ℓ)) * ((s : ↥(modularFunctionFieldFull N)) * x) := by rw [htF]; ring
        _ = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) ((t⁻¹ : (↥(GaloisRep.ratLocalizedAt ℓ))ˣ) : ↥(GaloisRep.ratLocalizedAt ℓ)) * a := by rw [h]
    rw [hx]
    exact Subalgebra.smul_mem _ ha' _

theorem coe_mem_chartAlg (S : Set ↥(modularFunctionFieldFull N)) (a : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S)) :
    (a : ↥(modularFunctionFieldFull N)) ∈ IgusaScheme.chartAlg N ℓ S := by
  haveI := isScalarTower_int N ℓ
  rw [chartAlg_eq]
  exact TwoChartIntegralModel.chartAlg_le_chartAlg ℤ ↥(modularFunctionFieldFull N) ↥(GaloisRep.ratLocalizedAt ℓ) S a.2

theorem exists_mul_add_mul_eq_one {s : ℤ} (hs : ¬ ((ℓ : ℤ) ∣ s)) : ∃ u v : ℤ, u * s + v * (ℓ : ℤ) = 1 := by
  have hp : Nat.Prime ℓ := Fact.out
  have hcop : IsCoprime s (ℓ : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    have h1 : ¬ ℓ ∣ s.natAbs := fun h => hs (Int.natCast_dvd.mpr h)
    have h2 : Nat.Coprime ℓ s.natAbs := (Nat.Prime.coprime_iff_not_dvd hp).mpr h1
    simpa [Int.gcd, Int.natAbs_natCast] using h2
  obtain ⟨u, v, huv⟩ := hcop
  exact ⟨u, v, huv⟩

noncomputable def redMap (S : Set ↥(modularFunctionFieldFull N)) :
    ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S) →+* (↥(IgusaScheme.chartAlg N ℓ S) ⧸ Ideal.span {((ℓ : ℕ) : ↥(IgusaScheme.chartAlg N ℓ S))}) :=
  (Ideal.Quotient.mk _).comp
    { toFun := fun a => ⟨(a : ↥(modularFunctionFieldFull N)), coe_mem_chartAlg N ℓ S a⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

theorem redMap_apply (S : Set ↥(modularFunctionFieldFull N)) (a : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S)) :
    redMap N ℓ S a = Ideal.Quotient.mk _ ⟨(a : ↥(modularFunctionFieldFull N)), coe_mem_chartAlg N ℓ S a⟩ := rfl

theorem redMap_surjective (S : Set ↥(modularFunctionFieldFull N)) : Function.Surjective (redMap N ℓ S) := by
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, s, ha, hs, h⟩ := (mem_chartAlg_iff_exists N ℓ S (y : ↥(modularFunctionFieldFull N))).mp y.2
  obtain ⟨u, v, huv⟩ := exists_mul_add_mul_eq_one ℓ hs
  refine ⟨(u : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S)) * ⟨a, ha⟩, ?_⟩
  rw [redMap_apply, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨-((v : ↥(IgusaScheme.chartAlg N ℓ S)) * y), Subtype.ext ?_⟩
  have h1 : ((u * s + v * (ℓ : ℤ) : ℤ) : ↥(modularFunctionFieldFull N)) = 1 := by exact_mod_cast huv
  have hy : (y : ↥(modularFunctionFieldFull N)) = (u : ↥(modularFunctionFieldFull N)) * a + (v : ↥(modularFunctionFieldFull N)) * (ℓ : ↥(modularFunctionFieldFull N)) * (y : ↥(modularFunctionFieldFull N)) := by
    calc (y : ↥(modularFunctionFieldFull N)) = ((u * s + v * (ℓ : ℤ) : ℤ) : ↥(modularFunctionFieldFull N)) * (y : ↥(modularFunctionFieldFull N)) := by rw [h1, one_mul]
      _ = (u : ↥(modularFunctionFieldFull N)) * ((s : ↥(modularFunctionFieldFull N)) * (y : ↥(modularFunctionFieldFull N))) + (v : ↥(modularFunctionFieldFull N)) * (ℓ : ↥(modularFunctionFieldFull N)) * (y : ↥(modularFunctionFieldFull N)) := by push_cast; ring
      _ = (u : ↥(modularFunctionFieldFull N)) * a + (v : ↥(modularFunctionFieldFull N)) * (ℓ : ↥(modularFunctionFieldFull N)) * (y : ↥(modularFunctionFieldFull N)) := by rw [h]

  simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_neg, coe_natCast_chartAlg, coe_intCast_chartAlg]

  change (((u : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S)) * ⟨a, ha⟩ : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S)) : ↥(modularFunctionFieldFull N)) - (y : ↥(modularFunctionFieldFull N)) = (ℓ : ↥(modularFunctionFieldFull N)) * -((v : ↥(modularFunctionFieldFull N)) * (y : ↥(modularFunctionFieldFull N)))
  rw [Subalgebra.coe_mul, coe_intCast_chartAlg_int]
  linear_combination (-1 : ↥(modularFunctionFieldFull N)) * hy

theorem ker_redMap (S : Set ↥(modularFunctionFieldFull N)) :
    RingHom.ker (redMap N ℓ S) = Ideal.span {((ℓ : ℕ) : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S))} := by
  apply le_antisymm
  · intro a ha
    rw [RingHom.mem_ker, redMap_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at ha
    obtain ⟨y, hy⟩ := ha
    obtain ⟨b, s, hb, hs, h⟩ := (mem_chartAlg_iff_exists N ℓ S (y : ↥(modularFunctionFieldFull N))).mp y.2
    obtain ⟨u, v, huv⟩ := exists_mul_add_mul_eq_one ℓ hs
    have haF : (a : ↥(modularFunctionFieldFull N)) = (ℓ : ↥(modularFunctionFieldFull N)) * (y : ↥(modularFunctionFieldFull N)) := by
      have := congrArg (fun z : ↥(IgusaScheme.chartAlg N ℓ S) => (z : ↥(modularFunctionFieldFull N))) hy
      simp only [Subalgebra.coe_mul, coe_natCast_chartAlg] at this
      exact this
    have h1 : ((u * s + v * (ℓ : ℤ) : ℤ) : ↥(modularFunctionFieldFull N)) = 1 := by exact_mod_cast huv
    rw [Ideal.mem_span_singleton]
    refine ⟨(u : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S)) * ⟨b, hb⟩ + (v : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S)) * a, Subtype.ext ?_⟩
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, coe_natCast_chartAlg_int, coe_intCast_chartAlg_int]

    have key : (a : ↥(modularFunctionFieldFull N)) = ((u * s + v * (ℓ : ℤ) : ℤ) : ↥(modularFunctionFieldFull N)) * (a : ↥(modularFunctionFieldFull N)) := by rw [h1, one_mul]
    push_cast at key
    change (a : ↥(modularFunctionFieldFull N)) = (ℓ : ↥(modularFunctionFieldFull N)) * ((u : ↥(modularFunctionFieldFull N)) * b + (v : ↥(modularFunctionFieldFull N)) * (a : ↥(modularFunctionFieldFull N)))
    linear_combination key + (u : ↥(modularFunctionFieldFull N)) * (s : ↥(modularFunctionFieldFull N)) * haF + (u : ↥(modularFunctionFieldFull N)) * (ℓ : ↥(modularFunctionFieldFull N)) * h
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, redMap_apply,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    refine ⟨1, Subtype.ext ?_⟩
    rw [mul_one]
    change (((ℓ : ℕ) : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S)) : ↥(modularFunctionFieldFull N)) = (((ℓ : ℕ) : ↥(IgusaScheme.chartAlg N ℓ S)) : ↥(modularFunctionFieldFull N))
    rw [coe_natCast_chartAlg_int, coe_natCast_chartAlg]

theorem exists_ringEquiv_quotient (S : Set ↥(modularFunctionFieldFull N)) :
    ∃ (hle : ∀ a : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S), (a : ↥(modularFunctionFieldFull N)) ∈ IgusaScheme.chartAlg N ℓ S)
       (e : (↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S) ⧸ Ideal.span {((ℓ : ℕ) : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S))}) ≃+* (↥(IgusaScheme.chartAlg N ℓ S) ⧸ Ideal.span {((ℓ : ℕ) : ↥(IgusaScheme.chartAlg N ℓ S))})),
       ∀ a : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S), e (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ ⟨(a : ↥(modularFunctionFieldFull N)), hle a⟩ := by
  refine ⟨coe_mem_chartAlg N ℓ S,
    (Ideal.quotEquivOfEq (ker_redMap N ℓ S).symm).trans
      (RingHom.quotientKerEquivOfSurjective (redMap_surjective N ℓ S)), fun a => ?_⟩
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact RingHom.kerLift_mk (redMap N ℓ S) a

end ModularCurve.IgusaScheme.ChartTransport

open ModularCurve.IgusaScheme.ChartTransport in
theorem solution
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (S : Set ↥(modularFunctionFieldFull N)) :
    IgusaScheme.chartAlg N ℓ S =
        TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) S ∧
    (∀ x : ↥(modularFunctionFieldFull N), x ∈ IgusaScheme.chartAlg N ℓ S ↔
        ∃ (a : ↥(modularFunctionFieldFull N)) (s : ℤ), a ∈ TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S ∧
          ¬ ((ℓ : ℤ) ∣ s) ∧ (s : ↥(modularFunctionFieldFull N)) * x = a) ∧
    (∃ (hle : ∀ a : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S), (a : ↥(modularFunctionFieldFull N)) ∈ IgusaScheme.chartAlg N ℓ S)
       (e : (↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S) ⧸
              Ideal.span {((ℓ : ℕ) : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S))}) ≃+*
            (↥(IgusaScheme.chartAlg N ℓ S) ⧸ Ideal.span {((ℓ : ℕ) : ↥(IgusaScheme.chartAlg N ℓ S))})),
       ∀ a : ↥(TwoChartIntegralModel.chartAlg ℤ ↥(modularFunctionFieldFull N) S),
         e (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ ⟨(a : ↥(modularFunctionFieldFull N)), hle a⟩) :=
  ⟨chartAlg_eq N ℓ S, mem_chartAlg_iff_exists N ℓ S, exists_ringEquiv_quotient N ℓ S⟩

end S_ModularCurve_IgusaScheme_chartAlg_eq_and_mem_iff_and_exists_ringEquiv_quotient_span_natCast
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_chartAlg_eq_and_mem_iff_and_exists_ringEquiv_quotient_span_natCast (solution)
