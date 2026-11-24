-- Prove2me | solution 1 for GlobalTheory.SW.WeilLevel.sq_le_of_finsum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:01:33.992996+00:00
-- url     : https://prove2.me/submissions/d575089f-d6c3-4b33-92be-82733dbdb755

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Theorems.Thm_GlobalTheory_SW_HaarLevel_finsum_quotient_of_le
import Theorems.Thm_GlobalTheory_SW_TransComp_key


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
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.WeilLevel
noncomputable section
namespace GlobalTheory.SW.WeilLevel
theorem _root_.solution {A : Type} [AddCommGroup A] {s t u : AddSubgroup A} (h : s ≤ t)
    (hn : s.relIndex t ≠ 0) (hu : t.relIndex u ≠ 0) (f g : A → ℂ)
    (hf : ∀ x, ∀ y ∈ t, f (x + y) = f x) (hg : ∀ x, ∀ y ∈ t, g (x + y) = g x)
    (hf' : ∀ x, f x ≠ 0 → x ∈ u) (hg' : ∀ x, g x ≠ 0 → x ∈ u)
    (he : ∑ᶠ q : A ⧸ s, f q.out * conj (f q.out) = ∑ᶠ q : A ⧸ s, g q.out * conj (g q.out))
    (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) (x : A) : ‖g x‖ ^ 2 ≤ (t.relIndex u : ℝ) * B ^ 2 := by
  classical
  have hc : t.relIndex u = Nat.card (u.map (QuotientAddGroup.mk' t)) := by
    rw [← AddSubgroup.relIndex_ker, QuotientAddGroup.ker_mk']
  haveI : Finite (u.map (QuotientAddGroup.mk' t)) := Nat.finite_of_card_ne_zero (hc ▸ hu)
  have hS : ((u.map (QuotientAddGroup.mk' t) : AddSubgroup (A ⧸ t)) : Set (A ⧸ t)).Finite :=
    Set.toFinite _
  have hcard : hS.toFinset.card = t.relIndex u := by
    rw [hc, ← Set.ncard_eq_toFinset_card _ hS]; rfl
  have key : ∀ k : A → ℂ, (∀ x, k x ≠ 0 → x ∈ u) →
      (Function.support fun q : A ⧸ t => k q.out * conj (k q.out)) ⊆ hS.toFinset := by
    intro k hk q hq
    rw [Set.Finite.coe_toFinset]
    exact ⟨q.out, hk _ (left_ne_zero_of_mul hq), QuotientAddGroup.out_eq' q⟩
  rw [HaarLevel.finsum_quotient_of_le h hn (fun x => f x * conj (f x))
      (fun x y hy => by simp only [hf x y hy]) ((Finset.finite_toSet _).subset (key f hf')),
    HaarLevel.finsum_quotient_of_le h hn (fun x => g x * conj (g x))
      (fun x y hy => by simp only [hg x y hy]) ((Finset.finite_toSet _).subset (key g hg')),
    finsum_eq_sum_of_support_subset _ (key f hf'),
    finsum_eq_sum_of_support_subset _ (key g hg')] at he
  have he2 := mul_left_cancel₀ (by exact_mod_cast hn) he
  simp only [Complex.mul_conj'] at he2
  have he3 : ∑ q ∈ hS.toFinset, ‖f q.out‖ ^ 2 = ∑ q ∈ hS.toFinset, ‖g q.out‖ ^ 2 := by
    exact_mod_cast he2
  by_cases hx : g x = 0
  · rw [hx, norm_zero, zero_pow two_ne_zero]; positivity
  have h1 : g (x : A ⧸ t).out = g x := by
    have := hg x _ (QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (x : A ⧸ t)).symm)
    rw [← this]; congr 1; abel
  calc ‖g x‖ ^ 2 = ‖g (x : A ⧸ t).out‖ ^ 2 := by rw [h1]
    _ ≤ ∑ q ∈ hS.toFinset, ‖g q.out‖ ^ 2 :=
        Finset.single_le_sum (f := fun q : A ⧸ t => ‖g q.out‖ ^ 2) (fun _ _ => sq_nonneg _)
          (by rw [Set.Finite.mem_toFinset]; exact ⟨x, hg' x hx, rfl⟩)
    _ ≤ hS.toFinset.card • B ^ 2 := by
        rw [← he3]
        exact Finset.sum_le_card_nsmul _ _ _ fun q _ => by
          have := hB q.out
          gcongr
    _ = _ := by rw [hcard, nsmul_eq_mul]
end GlobalTheory.SW.WeilLevel
