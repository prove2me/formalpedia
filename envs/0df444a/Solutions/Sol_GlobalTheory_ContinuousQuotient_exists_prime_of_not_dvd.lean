-- Prove2me | solution 1 for GlobalTheory.ContinuousQuotient.exists_prime_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:04:54.912919+00:00
-- url     : https://prove2.me/submissions/fd7d88e0-517b-4330-a090-f61d78d1145c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfForallAlgHomComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEqMulOfContinuousOnQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Topology
open GlobalTheory GlobalTheory.ContinuousQuotient
namespace GlobalTheory.ContinuousQuotient
theorem _root_.solution {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {a b : A} (hb : b ≠ 0) (h : ¬ b ∣ a) :
    ∃ p : Ideal A, p.IsPrime ∧ ∃ s r : A, s ∉ p ∧ r ∈ p ∧ b * s = a * r := by
  classical
  set I : Ideal A := Ideal.span {b} with hI
  have hmk : ∀ r x : A, r • (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (r * x) := fun r x => by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
  have hz : ∀ x : A, Ideal.Quotient.mk I x = 0 ↔ b ∣ x := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]

  let J : A → Ideal A := fun x => Submodule.comap (LinearMap.mulRight A x) I
  have hJ : ∀ x r : A, r ∈ J x ↔ b ∣ r * x := fun x r => by
    simp only [J, Submodule.mem_comap, LinearMap.mulRight_apply, hI, Ideal.mem_span_singleton]

  obtain ⟨P, ⟨c, hc, hac, rfl⟩, hmaxP⟩ := (set_has_maximal_iff_noetherian (R := A) (M := A)).2 inferInstance
    {P | ∃ x, ¬ b ∣ x ∧ J a ≤ J x ∧ P = J x} ⟨J a, a, h, le_rfl, rfl⟩
  have hp : (J c).IsPrime := by
    refine ⟨fun ht => hc (by simpa using (hJ c 1).1 ((Ideal.eq_top_iff_one _).1 ht)), ?_⟩
    intro r s hrs
    by_contra hno
    push Not at hno
    obtain ⟨hr, hs⟩ := hno
    have hle' : J c ≤ J (r * c) := fun t ht => by
      obtain ⟨k, hk⟩ := (hJ c t).1 ht
      exact (hJ _ t).2 ⟨r * k, by rw [← _root_.mul_assoc, _root_.mul_comm t r, _root_.mul_assoc, hk]; ring⟩
    have hrc : ¬ b ∣ r * c := fun hd => hr ((hJ c r).2 hd)
    have heq : J c = J (r * c) := by
      by_contra hne
      exact hmaxP (J (r * c)) ⟨r * c, hrc, hac.trans hle', rfl⟩ (lt_of_le_of_ne hle' hne)
    apply hs
    rw [heq, hJ]
    obtain ⟨k, hk⟩ := (hJ c (r * s)).1 hrs
    exact ⟨k, by rw [← hk]; ring⟩
  set p := J c with hpdef
  have hpc : ∀ r : A, r ∈ p ↔ b ∣ r * c := hJ c
  have hla : ∀ r : A, b ∣ r * a → r ∈ p := fun r hr => hac ((hJ a r).2 hr)
  have hbp : b ∈ p := (hpc b).2 (dvd_mul_right b c)

  have key : ∃ q w : A, q ∈ p ∧ w ∉ p ∧ b * w = q * c := by
    by_contra hne
    push Not at hne
    let K := FractionRing A
    let y : K := algebraMap A K c / algebraMap A K b
    have hb' : algebraMap A K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hb
    let N : Submodule A K := Submodule.map (Algebra.linearMap A K) p
    have hN : N ≠ ⊥ := by
      intro h0
      have : algebraMap A K b ∈ N := Submodule.mem_map_of_mem (f := Algebra.linearMap A K) hbp
      rw [h0, Submodule.mem_bot] at this
      exact hb' this
    have hfg : N.FG := (IsNoetherian.noetherian p).map (Algebra.linearMap A K)
    have hint : IsIntegral A y := by
      refine isIntegral_of_smul_mem_submodule N hN hfg y ?_
      intro n hn
      obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨w, hw⟩ := (hpc q).1 hq
      have hwp : w ∈ p := by
        by_contra hwp
        exact hne q w hq hwp hw.symm
      refine ⟨w, hwp, ?_⟩
      simp only [Algebra.linearMap_apply, smul_eq_mul, y]
      rw [div_mul_eq_mul_div, eq_div_iff hb', ← map_mul, ← map_mul, _root_.mul_comm w b, ← hw, _root_.mul_comm]
    obtain ⟨z, hz'⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have hbc : b * z = c := by
      apply IsFractionRing.injective A K
      rw [map_mul, hz', mul_div_cancel₀ _ hb']
    exact hp.ne_top ((Ideal.eq_top_iff_one p).2 ((hpc 1).2 ⟨z, by rw [_root_.one_mul, hbc]⟩))
  obtain ⟨q, w, hq, hw, hbw⟩ := key
  let R := Localization.AtPrime p
  have : IsDomain R := IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors
  have : IsNoetherianRing R := IsLocalization.isNoetherianRing p.primeCompl R inferInstance
  have hinj : Function.Injective (algebraMap A R) :=
    IsLocalization.injective R p.primeCompl_le_nonZeroDivisors
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {algebraMap A R q} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      obtain ⟨v, hv⟩ := (hpc x).1 hx
      have hwx : w * x = v * q := by
        apply mul_left_cancel₀ hb
        calc b * (w * x) = (b * w) * x := by ring
          _ = b * v * q := by rw [hbw, _root_.mul_assoc, _root_.mul_comm c x, hv]; ring
          _ = b * (v * q) := by ring
      obtain ⟨u, hu⟩ := IsLocalization.map_units R (⟨w, hw⟩ : p.primeCompl)
      rw [Ideal.mem_comap, Ideal.mem_span_singleton']
      refine ⟨(↑u⁻¹ : R) * algebraMap A R v, ?_⟩
      have e : (u : R) * algebraMap A R x = algebraMap A R v * algebraMap A R q := by
        rw [hu, ← map_mul, ← map_mul, hwx]
      rw [_root_.mul_assoc, ← e, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
    · exact (Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_map_of_mem _ hq)
  have hnf : ¬ IsField R := by
    intro hF
    have h0 := IsLocalRing.isField_iff_maximalIdeal_eq.1 hF
    have : algebraMap A R b ∈ IsLocalRing.maximalIdeal R := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ hbp
    rw [h0, Ideal.mem_bot, ← map_zero (algebraMap A R)] at this
    exact hb (hinj this)
  have : ValuationRing R :=
    ((IsDiscreteValuationRing.TFAE R hnf).out 4 1).1
      (show Submodule.IsPrincipal (IsLocalRing.maximalIdeal R) from ⟨⟨_, hmax⟩⟩)
  obtain ⟨z, hz2⟩ := ValuationRing.cond (algebraMap A R a) (algebraMap A R b)
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
  have hs : (s : A) ∉ p := s.2
  rcases hz2 with e | e
  · rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul] at e
    have e' : a * r = b * s := hinj e
    have hr : r ∈ p := hla r ⟨s, by rw [_root_.mul_comm r a, e']⟩
    exact ⟨p, hp, s, r, hs, hr, e'.symm⟩
  · rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul] at e
    have e' : b * r = a * s := hinj e
    exact absurd (hla s ⟨r, by rw [_root_.mul_comm (s : A) a, e']⟩) hs
end GlobalTheory.ContinuousQuotient
