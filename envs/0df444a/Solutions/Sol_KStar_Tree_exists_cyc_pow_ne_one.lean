-- Prove2me | solution 1 for KStar.Tree.exists_cyc_pow_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:25:35.858115+00:00
-- url     : https://prove2.me/submissions/9bf9d34f-adbc-4e11-accf-a0809d8e37ed

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuInf
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_TotientLeOfCycPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace KStar.Tree
open Polynomial IntermediateField in
private theorem totient_le_of_cyc_pow_eq_one (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ) (hn : n ≠ 0) (h : ∀ g : Ω ≃ₐ[E] Ω, cyc l E Ω g ^ n = 1) (k : ℕ) :
    Nat.totient (l ^ k) ≤ Module.finrank ℚ E * n := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have hl := (Fact.out : l.Prime)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ k)
  have hint : IsIntegral E ζ := (hζ.isIntegral (pow_pos hl.pos k)).tower_top
  set S : Finset ℤ_[l] := (Polynomial.nthRoots n (1 : ℤ_[l])).toFinset with hSdef
  have hS : S.card ≤ n := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots n 1)
  have hsub : ∀ r ∈ (minpoly E ζ).rootSet Ω, r ∈ S.image fun x => ζ ^ (PadicInt.toZModPow k x).val := by
    intro r hr
    rw [Polynomial.mem_rootSet] at hr
    have hmin : minpoly E r = minpoly E ζ :=
      (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hr.2 (minpoly.monic hint)).symm
    obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit Ω).1 hmin
    have hspec := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut Gal(Ω/E) Ω g) ζ hζ.pow_eq_one
    rw [Finset.mem_image]
    refine ⟨((cyc l E Ω g : ℤ_[l]ˣ) : ℤ_[l]), ?_, ?_⟩
    · rw [hSdef, Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hn),
        ← Units.val_pow_eq_pow_val, h g, Units.val_one]
    · rw [← hg]
      exact hspec.symm
  have hdeg : (minpoly E ζ).natDegree ≤ n := by
    rw [← Polynomial.card_rootSet_eq_natDegree (K := Ω) (minpoly.irreducible hint).separable
      (IsAlgClosed.splits ((minpoly E ζ).map (algebraMap E Ω)))]
    calc Fintype.card ((minpoly E ζ).rootSet Ω) = ((minpoly E ζ).rootSet Ω).toFinset.card :=
          (Set.toFinset_card _).symm
      _ ≤ (S.image fun x => ζ ^ (PadicInt.toZModPow k x).val).card :=
          Finset.card_le_card fun x hx => hsub x (Set.mem_toFinset.1 hx)
      _ ≤ S.card := Finset.card_image_le
      _ ≤ n := hS
  haveI : FiniteDimensional E E⟮ζ⟯ := IntermediateField.adjoin.finiteDimensional hint
  haveI : FiniteDimensional ℚ E⟮ζ⟯ := Module.Finite.trans E E⟮ζ⟯
  have hζF : IsPrimitiveRoot (⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩ : E⟮ζ⟯) (l ^ k) :=
    IsPrimitiveRoot.of_map_of_injective (f := (E⟮ζ⟯).val) hζ Subtype.val_injective
  have hq : (l ^ k).totient ≤ Module.finrank ℚ E⟮ζ⟯ := by
    rw [← Polynomial.natDegree_cyclotomic (l ^ k) ℚ,
      Polynomial.cyclotomic_eq_minpoly_rat hζF (pow_pos hl.pos k)]
    exact minpoly.natDegree_le _
  calc (l ^ k).totient ≤ Module.finrank ℚ E⟮ζ⟯ := hq
    _ = Module.finrank ℚ E * Module.finrank E E⟮ζ⟯ := (Module.finrank_mul_finrank ℚ E E⟮ζ⟯).symm
    _ ≤ Module.finrank ℚ E * n := by
        apply Nat.mul_le_mul_left
        rw [IntermediateField.adjoin.finrank hint]
        exact hdeg
end KStar.Tree
end

set_option autoImplicit false
open KStar KStar.Tree
namespace KStar.Tree
theorem _root_.solution (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (n : ℕ) (hn : n ≠ 0) : ∃ g : Ω ≃ₐ[E] Ω, cyc l E Ω g ^ n ≠ 1 := by
  have hl := (Fact.out : l.Prime)
  by_contra hne
  push_neg at hne
  have key := totient_le_of_cyc_pow_eq_one l E Ω n hn hne (Module.finrank ℚ E * n + 1)
  rw [Nat.totient_prime_pow_succ hl] at key
  have h1 : Module.finrank ℚ E * n < l ^ (Module.finrank ℚ E * n) := Nat.lt_pow_self hl.one_lt
  have h2 : l ^ (Module.finrank ℚ E * n) ≤ l ^ (Module.finrank ℚ E * n) * (l - 1) :=
    Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt hl.one_lt)
  omega
end KStar.Tree
