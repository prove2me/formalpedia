-- Prove2me | solution 1 for GlobalTheory.EmbFrob.exists_frobenius_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:28:36.574731+00:00
-- url     : https://prove2.me/submissions/419aa8ef-f19e-484b-8c7a-210001e51ef3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueMaximalAbovePlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPowOfFiniteField
import Theorems.Thm_GlobalTheory_EmbFrob_exists_pow_of_finite_field
import Theorems.Thm_GlobalTheory_EmbFrob_comap_eq
import Theorems.Thm_GlobalTheory_OnePrime_exists_prime_under


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory GlobalTheory.EmbFrob
open Polynomial
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
namespace GlobalTheory.EmbFrob
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [IsDedekindDomain OE] [CharZero OE] [Module.Finite ℤ OE] (C : Type) [Field C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R],
    v.Integers R → ¬ IsUnit (p : R) → ∀ (w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p OE)
    (σ τ : OE →+* R), σ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e →
    τ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e →
    ∃ i : ℕ, ∀ a : OE, v (algebraMap R C (τ a - σ a ^ (p ^ i))) < 1 := by
  intro p _ OE _ _ _ _ C _ v R _ _ _ hv hp w σ τ hσ hτ
  haveI : IsDomain R := hv.hom_inj.isDomain (algebraMap R C)
  haveI : ValuationRing R := ValuationRing.of_integers v hv
  let w' : Place p OE := ⟨w.e, w.idem, w.ne_zero, w.prim⟩
  obtain ⟨P, hPm, hpP, -, hP⟩ := GlobalTheory.OnePrime.exists_prime_under p OE w'
  have h1 := comap_eq hp w' hP σ hσ
  have h2 := comap_eq hp w' hP τ hτ
  have hP0 : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpP
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hpP
  haveI : Finite (OE ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  letI : Field (OE ⧸ P) := Ideal.Quotient.field P
  haveI : CharP (IsLocalRing.ResidueField R) p := by
    refine (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 ?_
    rw [← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff]
    exact hp
  obtain ⟨i, hi⟩ := exists_pow_of_finite_field p (k := IsLocalRing.ResidueField R)
    (Ideal.quotientMap (IsLocalRing.maximalIdeal R) σ h1.ge)
    (Ideal.quotientMap (IsLocalRing.maximalIdeal R) τ h2.ge)
  refine ⟨i, fun a => ?_⟩
  have h3 : IsLocalRing.residue R (τ a) = IsLocalRing.residue R (σ a) ^ p ^ i :=
    hi (Ideal.Quotient.mk P a)
  have h4 : τ a - σ a ^ p ^ i ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, h3, sub_self]
  exact lt_of_le_of_ne (hv.map_le_one _) fun h => h4 (hv.isUnit_iff_valuation_eq_one.2 h)
end GlobalTheory.EmbFrob
