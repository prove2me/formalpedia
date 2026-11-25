-- Prove2me | solution 1 for GlobalTheory.BadShare.dvd_of_samePart_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:46:51.88253+00:00
-- url     : https://prove2.me/submissions/d2ed76f5-c74c-47de-94cc-e5c47364d49d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassDivisorBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassUnionBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardIrreducibleSamePrimeToPartRootsLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassSamePartOneFactorLe
import Theorems.Thm_GlobalTheory_BadShare_eq_of_pow_eq
import Theorems.Thm_GlobalTheory_BadShare_root_ne_zero
import Theorems.Thm_GlobalTheory_BadShare_samePart_iff_of_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare
private theorem pow_card_pow_natDegree_eq_self_of_mem_aroots {g : ℕ} [Fact g.Prime] {P : (ZMod g)[X]} (hP : Irreducible P)
    {x : AlgebraicClosure (ZMod g)} (hx : x ∈ P.aroots (AlgebraicClosure (ZMod g))) :
    x ^ (g ^ P.natDegree) = x := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have : Fact (Irreducible P) := ⟨hP⟩
  have hxr : aeval x P = 0 := (Polynomial.mem_aroots.mp hx).2
  have : Module.Finite (ZMod g) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP0).finite
  have : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod g)
  let _ : Fintype (AdjoinRoot P) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot P) = g ^ P.natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, (AdjoinRoot.powerBasis hP0).finrank,
      AdjoinRoot.powerBasis_dim]
  have h := FiniteField.pow_card (AdjoinRoot.root P)
  rw [hcard] at h
  have hxr' : P.eval₂ (algebraMap (ZMod g) (AlgebraicClosure (ZMod g))) x = 0 := by
    rwa [aeval_def] at hxr
  have h' := congrArg (AdjoinRoot.lift (algebraMap (ZMod g) (AlgebraicClosure (ZMod g))) x hxr') h
  rwa [map_pow, AdjoinRoot.lift_root] at h'
end GlobalTheory.BadShare
end

set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution {g : ℕ} [Fact g.Prime] {P : (ZMod g)[X]} (hP : Irreducible P) (h0 : P.coeff 0 ≠ 0)
    {l : ℕ} (hl : l.Prime) {x y : AlgebraicClosure (ZMod g)} (hx : x ∈ P.aroots (AlgebraicClosure (ZMod g)))
    (hy : y ∈ P.aroots (AlgebraicClosure (ZMod g))) (hxy : x ≠ y) (hs : SamePart l x y) :
    2 ≤ P.natDegree ∧ l ∣ g ^ P.natDegree - 1 := by
  have hcard : (P.aroots (AlgebraicClosure (ZMod g))).card = P.natDegree :=
    IsAlgClosed.card_aroots_eq_natDegree
  have h2 : 2 ≤ P.natDegree := by
    rw [← hcard]
    have hsub : ({x, y} : Finset (AlgebraicClosure (ZMod g))) ⊆
        (P.aroots (AlgebraicClosure (ZMod g))).toFinset := by
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [Multiset.mem_toFinset]
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    calc 2 = ({x, y} : Finset (AlgebraicClosure (ZMod g))).card := (Finset.card_pair hxy).symm
      _ ≤ (P.aroots (AlgebraicClosure (ZMod g))).toFinset.card := Finset.card_le_card hsub
      _ ≤ (P.aroots (AlgebraicClosure (ZMod g))).card := Multiset.toFinset_card_le _
  refine ⟨h2, ?_⟩
  have hgp : g.Prime := Fact.out
  have hx0 := root_ne_zero h0 hx
  have hy0 := root_ne_zero h0 hy
  have hM0 : g ^ P.natDegree - 1 ≠ 0 := by
    have : 2 ≤ g ^ P.natDegree := le_trans hgp.two_le (Nat.le_self_pow (by omega) g)
    omega
  have hpow : ∀ z ∈ P.aroots (AlgebraicClosure (ZMod g)), z ≠ 0 → z ^ (g ^ P.natDegree - 1) = 1 := by
    intro z hz hz0
    have h := pow_card_pow_natDegree_eq_self_of_mem_aroots hP hz
    have hg1 : 1 ≤ g ^ P.natDegree := Nat.one_le_pow _ _ hgp.pos
    apply mul_left_cancel₀ hz0
    rw [← pow_succ', Nat.sub_add_cancel hg1, h, mul_one]
  by_contra hnd
  have hcop : (g ^ P.natDegree - 1).Coprime l :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).mpr hnd)
  obtain ⟨a, ha⟩ := (samePart_iff_of_ne_zero hl hx0 hy0).mp hs
  exact hxy (eq_of_pow_eq hcop (hpow x hx hx0) (hpow y hy hy0) hM0 ha)
end GlobalTheory.BadShare
