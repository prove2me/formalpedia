-- Prove2me | solution 1 for GlobalTheory.ZM.sum_omegaStd_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:31:44.863023+00:00
-- url     : https://prove2.me/submissions/abb460c6-e830-48dc-bf22-2e3019cb5570

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_W8AddTransposeEqE8
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsE8IsSharpBasis
import Theorems.Thm_GlobalTheory_ZM_sharpIndex_inl
import Theorems.Thm_GlobalTheory_ZM_sharpIndex_inr

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM
namespace GlobalTheory.ZM
theorem _root_.solution (h : ℕ) (i j : Fin (2 * (8 * h))) :
    ∑ u, omegaStd (fun c => (Pi.single i 1 : Fin (2 * (8 * h)) → ℤ) (sharpIndex h (u, c)))
      (fun c => (Pi.single j 1 : Fin (2 * (8 * h)) → ℤ) (sharpIndex h (u, c))) = Out.stdSymp (8 * h) i j := by
  obtain ⟨⟨u, c⟩, rfl⟩ := (sharpIndex h).surjective i
  obtain ⟨⟨v, d⟩, rfl⟩ := (sharpIndex h).surjective j
  have hinj : ∀ (u v : Fin 8) (a b : Fin h),
      ((finProdFinEquiv (u, a) : ℕ) = (finProdFinEquiv (v, b) : ℕ)) ↔ (u = v ∧ a = b) := by
    intro u v a b
    rw [Fin.val_inj, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  rcases c with a | a <;> rcases d with b | b
  all_goals
    have h1 := (finProdFinEquiv (u, a)).isLt
    have h2 := (finProdFinEquiv (v, b)).isLt
    have h3 := hinj u v a b
    simp only [omegaStd, Out.stdSymp, Pi.single_apply, Equiv.apply_eq_iff_eq, Prod.mk.injEq,
      sharpIndex_inl, sharpIndex_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
      if_false, mul_zero, zero_mul, sub_zero, zero_sub, Finset.sum_const_zero, sub_self]
    generalize (finProdFinEquiv (u, a) : ℕ) = m at *
    generalize (finProdFinEquiv (v, b) : ℕ) = n at *
  · rw [if_neg (by omega), if_neg (by omega)]
  · by_cases huv : u = v ∧ a = b
    · obtain ⟨rfl, rfl⟩ := huv
      have : m = n := h3.2 ⟨rfl, rfl⟩
      rw [if_pos (by omega)]
      simp [ite_and]
    · have : m ≠ n := fun e => huv (h3.1 e)
      rw [if_neg (by omega), if_neg (by omega)]
      refine Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun c _ => ?_
      split_ifs with p q
      · exact absurd ⟨p.1.symm.trans q.1, p.2.symm.trans q.2⟩ huv
      all_goals simp
  · by_cases huv : u = v ∧ a = b
    · obtain ⟨rfl, rfl⟩ := huv
      have : m = n := h3.2 ⟨rfl, rfl⟩
      rw [if_neg (by omega), if_pos (by omega)]
      simp [ite_and]
    · have : m ≠ n := fun e => huv (h3.1 e)
      rw [if_neg (by omega), if_neg (by omega)]
      refine Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun c _ => ?_
      split_ifs with p q
      · exact absurd ⟨p.1.symm.trans q.1, p.2.symm.trans q.2⟩ huv
      all_goals simp
  · rw [if_neg (by omega), if_neg (by omega)]
end GlobalTheory.ZM
