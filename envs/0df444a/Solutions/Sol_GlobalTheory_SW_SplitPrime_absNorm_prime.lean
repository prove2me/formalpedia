-- Prove2me | solution 1 for GlobalTheory.SW.SplitPrime.absNorm_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:43.41777+00:00
-- url     : https://prove2.me/submissions/3b547ad6-5054-4de8-bad9-8f7ba9ddbc02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsGoodSplitPrimeCmField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SplitPrime
open Polynomial
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical
open Polynomial
namespace GlobalTheory.SW.SplitPrime
namespace _root_.GlobalTheory.SW.SplitPrime
theorem _root_.solution {E : Type} [Field E] [NumberField E]
    (P : Ideal (𝓞 E)) (hP : P.IsMaximal)
    (hs : Function.Surjective (Int.castRingHom (𝓞 E ⧸ P))) : (Ideal.absNorm P).Prime := by
  letI := Ideal.Quotient.field P
  have hN : Ideal.absNorm P = Nat.card (𝓞 E ⧸ P) := Nat.add_zero _
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 E ⧸ P)
  haveI := hp
  have hp' : p.Prime := (CharP.char_is_prime_or_zero (𝓞 E ⧸ P) p).resolve_right (by
    rintro rfl
    haveI : CharZero (𝓞 E ⧸ P) := CharP.charP_to_charZero _
    haveI : Infinite (𝓞 E ⧸ P) := Infinite.of_injective _ Nat.cast_injective
    exact not_finite (𝓞 E ⧸ P))
  haveI := Fact.mk hp'
  have hbij : Function.Bijective (ZMod.castHom (dvd_refl p) (𝓞 E ⧸ P)) := by
    refine ⟨(ZMod.castHom (dvd_refl p) (𝓞 E ⧸ P)).injective, fun y => ?_⟩
    obtain ⟨n, rfl⟩ := hs y
    exact ⟨n, by simp⟩
  rw [hN, ← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_zmod]
  exact hp'
end _root_.GlobalTheory.SW.SplitPrime
end GlobalTheory.SW.SplitPrime
