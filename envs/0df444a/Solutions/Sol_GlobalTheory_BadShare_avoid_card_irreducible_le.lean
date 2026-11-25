-- Prove2me | solution 1 for GlobalTheory.BadShare.avoid_card_irreducible_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:14:47.508356+00:00
-- url     : https://prove2.me/submissions/c02fd264-1130-4759-a86f-1619b8c096c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassDivisorBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumPrimePowerPartPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumLeProdOfTwoLeNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PowPadicValEqOneOfPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassUnionBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MassNotRootsAvoidLe
import Theorems.Thm_GlobalTheory_BadShare_avoid_pow_natDegree_minpoly
import Theorems.Thm_GlobalTheory_BadShare_eq_of_pow_eq
import Theorems.Thm_GlobalTheory_BadShare_mem_sqSet
import Theorems.Thm_GlobalTheory_BadShare_root_ne_zero
import Theorems.Thm_GlobalTheory_BadShare_rootsAvoid_iff
import Theorems.Thm_GlobalTheory_BadShare_samePart_iff_of_ne_zero
import Theorems.Thm_GlobalTheory_BadShare_samePart_roots_finite_ncard


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution {g : ℕ} [Fact g.Prime] (c : (ZMod g)ˣ) (d : ℕ) (hd : 1 ≤ d) (h2 : 2 ∣ g - 1) :
    d * ((sqSet g d).filter fun P => Irreducible P ∧ ¬ RootsAvoid g c P).card ≤
      ∑ l ∈ (g ^ d - 1).primeFactors, l ^ padicValNat l (g ^ d - 1) := by
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have hn : 0 < g ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) hg)
  have hdv : g - 1 ∣ g ^ d - 1 := by simpa using Nat.sub_dvd_pow_sub_pow g 1 d
  set n := g ^ d - 1 with hndef
  set c' : AlgebraicClosure (ZMod g) := algebraMap (ZMod g) (AlgebraicClosure (ZMod g)) (c : ZMod g) with hc'
  have hc0 : c' ≠ 0 := by simp [hc']
  have hcn : c' ^ n = 1 := by
    obtain ⟨k, hk⟩ := hdv
    rw [hk, pow_mul, hc', ← map_pow, ZMod.pow_card_sub_one_eq_one c.ne_zero, map_one, one_pow]
  have hS := fun l (hl : l ∈ n.primeFactors) =>
    (GlobalTheory.BadShare.samePart_roots_finite_ncard (AlgebraicClosure (ZMod g)) n l hn (Nat.prime_of_mem_primeFactors hl)).2 c'
  let T : Finset (AlgebraicClosure (ZMod g)) :=
    n.primeFactors.attach.biUnion fun l => (hS l.1 l.2).1.toFinset
  have hT : T.card ≤ ∑ l ∈ n.primeFactors, l ^ padicValNat l n := by
    refine Finset.card_biUnion_le.trans ?_
    rw [← Finset.sum_attach n.primeFactors]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [← Set.ncard_eq_toFinset_card _ (hS l.1 l.2).1]
    exact (hS l.1 l.2).2
  refine le_trans ?_ hT
  set B := (sqSet g d).filter fun P => Irreducible P ∧ ¬ RootsAvoid g c P with hB
  have h1 : ∑ P ∈ B, (T.filter fun x => minpoly (ZMod g) x = P).card ≤ T.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    exact Finset.card_filter_le _ _
  refine le_trans ?_ h1
  rw [mul_comm, ← smul_eq_mul]
  refine Finset.card_nsmul_le_sum _ _ _ fun P hP => ?_
  obtain ⟨hP1, hirr, hbad⟩ := Finset.mem_filter.1 hP
  obtain ⟨hm, hdeg, -, h0⟩ := mem_sqSet.1 hP1
  rw [rootsAvoid_iff h0] at hbad
  push Not at hbad
  obtain ⟨l, hl, -, x, hx, a, ha⟩ := hbad
  have hmin : ∀ y ∈ P.aroots (AlgebraicClosure (ZMod g)), minpoly (ZMod g) y = P := fun y hy =>
    (minpoly.eq_of_irreducible_of_monic hirr (mem_aroots.1 hy).2 hm).symm
  have hdvd : P ∣ X ^ (l ^ a) - C ((c : ZMod g) ^ (l ^ a)) := by
    rw [← hmin x hx, minpoly.dvd_iff]
    simp [ha, hc']
  have hcard : (P.aroots (AlgebraicClosure (ZMod g))).toFinset.card = d := by
    have hsep : P.Separable := PerfectField.separable_of_irreducible hirr
    have := Polynomial.card_rootSet_eq_natDegree (K := AlgebraicClosure (ZMod g)) hsep (IsAlgClosed.splits _)
    rw [← hdeg, ← this]
    simp only [rootSet, Finset.coe_sort_coe]
    convert (Fintype.card_coe _).symm
  rw [← hcard]
  refine Finset.card_le_card fun y hy => ?_
  rw [Multiset.mem_toFinset] at hy
  have hy0 := root_ne_zero h0 hy
  have hyn : y ^ n = 1 := by
    have := avoid_pow_natDegree_minpoly hy0
    rwa [hmin y hy, hdeg] at this
  have hya : y ^ (l ^ a) = c' ^ (l ^ a) := by
    have h3 : minpoly (ZMod g) y ∣ X ^ (l ^ a) - C ((c : ZMod g) ^ (l ^ a)) := by rwa [hmin y hy]
    rw [minpoly.dvd_iff] at h3
    simpa [sub_eq_zero, hc'] using h3
  refine Finset.mem_filter.2 ⟨?_, hmin y hy⟩
  simp only [T, Finset.mem_biUnion, Finset.mem_attach, true_and, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  by_cases hln : l ∣ n
  · exact ⟨⟨l, Nat.mem_primeFactors.2 ⟨hl, hln, hn.ne'⟩⟩, hyn, (samePart_iff_of_ne_zero hl hy0 hc0).2 ⟨a, hya⟩⟩
  · have : y = c' := eq_of_pow_eq ((hl.coprime_iff_not_dvd.2 hln).symm) hyn hcn hn.ne' hya
    refine ⟨⟨2, Nat.mem_primeFactors.2 ⟨Nat.prime_two, h2.trans hdv, hn.ne'⟩⟩, hyn, ?_⟩
    rw [this]; rfl
end GlobalTheory.BadShare
