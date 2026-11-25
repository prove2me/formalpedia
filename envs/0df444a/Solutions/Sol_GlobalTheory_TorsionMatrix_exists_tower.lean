-- Prove2me | solution 1 for GlobalTheory.TorsionMatrix.exists_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:52:33.699831+00:00
-- url     : https://prove2.me/submissions/e568a0e6-6ed6-4cf3-ad45-3a8b8fbf4e14

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NormCardQuotientSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MatrixPolynomialDetNormFixedPoints
import Theorems.Thm_GlobalTheory_TorsionMatrix_exists_zmod_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.TorsionMatrix
open Matrix
namespace GlobalTheory.TorsionMatrix
theorem _root_.solution (l : ℕ) [hl : Fact l.Prime] (m : ℕ) (Q : Type) [AddCommGroup Q]
    (h : ∀ j : ℕ, Nat.card {x : Q // l ^ j • x = 0} = l ^ (m * j)) :
    ∃ τ : Fin m → ℕ → Q, (∀ i n, (l ^ (n + 1)) • τ i n = 0) ∧ (∀ i n, τ i n = l • τ i (n + 1)) ∧
      (∀ x : Q, l • x = 0 → ∃! t : Fin m → ZMod l, x = ∑ j, (t j).val • τ j 0) := by
  let T : ℕ → AddSubgroup Q := fun k => (nsmulAddMonoidHom (α := Q) k).ker
  have hT : ∀ k x, x ∈ T k ↔ k • x = 0 := fun k x => Iff.rfl
  have hc : ∀ j, Nat.card (T (l ^ j)) = l ^ (m * j) := h
  have hc1 : Nat.card (T l) = l ^ m := by simpa using hc 1
  have hfin : ∀ j, Finite (T (l ^ j)) := fun j =>
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hl.out.ne_zero)
  have hsurj : ∀ j (x : Q), l ^ j • x = 0 → ∃ y : Q, l ^ (j + 1) • y = 0 ∧ x = l • y := by
    intro j x hx
    have := hfin j
    have := hfin (j + 1)
    let φ : T (l ^ (j + 1)) →+ T (l ^ j) :=
      ((nsmulAddMonoidHom (α := Q) l).comp (T (l ^ (j + 1))).subtype).codRestrict _ fun y => by
        have := (hT _ _).1 y.2
        change l ^ j • l • (y : Q) = 0
        rw [smul_smul, ← pow_succ]
        exact this
    have hφ : ∀ y, (φ y : Q) = l • (y : Q) := fun y => rfl
    have hk : Nat.card φ.ker = l ^ m := by
      rw [← hc1]
      refine Nat.card_congr ⟨fun y => ⟨y.1.1, ?_⟩, fun y => ⟨⟨y.1, ?_⟩, ?_⟩, fun _ => rfl, fun _ => rfl⟩
      · exact congrArg Subtype.val y.2
      · rw [hT, pow_succ, mul_smul, (hT _ _).1 y.2, smul_zero]
      · exact Subtype.ext y.2
    have h1 := AddSubgroup.card_mul_index φ.ker
    rw [AddSubgroup.index_ker, hk, hc, mul_add, mul_one, pow_add l (m * j), mul_comm] at h1
    have h2 : Nat.card φ.range = Nat.card (T (l ^ j)) := by
      rw [hc]
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hl.out.pos m) h1
    have h3 : φ.range = ⊤ := AddSubgroup.eq_top_of_card_eq _ h2
    obtain ⟨y, hy⟩ := AddMonoidHom.range_eq_top.1 h3 ⟨x, hx⟩
    exact ⟨y, y.2, (congrArg Subtype.val hy).symm⟩
  choose! g hg1 hg2 using hsurj
  obtain ⟨b, hb⟩ := @exists_zmod_basis l hl m (T l) _
    (AddCommGroup.zmodModule fun x => Subtype.ext x.2) hc1
  let τ : Fin m → ℕ → Q := fun i n => Nat.rec (b i : Q) (fun k x => g (k + 1) x) n
  have h1 : ∀ i n, (l ^ (n + 1)) • τ i n = 0 := by
    intro i n
    induction n with
    | zero => rw [zero_add, pow_one]; exact (b i).2
    | succ n ih => exact hg1 _ _ ih
  have hs : ∀ t : Fin m → ZMod l,
      ((∑ j, (t j).val • b j : T l) : Q) = ∑ j, (t j).val • τ j 0 := by
    intro t
    rw [AddSubgroup.val_finset_sum]
    rfl
  refine ⟨τ, h1, fun i n => hg2 _ _ (h1 i n), fun x hx => ?_⟩
  simpa only [Subtype.ext_iff, hs] using hb ⟨x, hx⟩
end GlobalTheory.TorsionMatrix
