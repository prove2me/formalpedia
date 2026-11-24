-- Prove2me | solution 1 for GlobalTheory.ZM.exists_equiv_stdSymp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:19:15.126511+00:00
-- url     : https://prove2.me/submissions/a3a34ec8-09bf-4c83-b4e4-b647991d4ed3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEquivStdSymp
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_right
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_reindex
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_right
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_left_right
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_right_left
import Theorems.Thm_GlobalTheory_exists_isSymplecticBasis_of_finrank
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM
namespace GlobalTheory.ZM
theorem _root_.solution {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    {B : LinearMap.BilinForm ℤ M} (hB : B.IsAlt) (hp : Function.Bijective B) {g : ℕ}
    (hg : Module.finrank ℤ M = 2 * g) :
    ∃ bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] M,
      ∀ i j, B (bas (Pi.single i 1)) (bas (Pi.single j 1)) = Out.stdSymp g i j := by
  obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank hB hp hg
  let e : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)
  have hl : ∀ i, ((e (Sum.inl i) : Fin (2 * g)) : ℕ) = i := fun i => by simp [e]
  have hr : ∀ i, ((e (Sum.inr i) : Fin (2 * g)) : ℕ) = g + i := fun i => by simp [e]; omega
  refine ⟨(b.reindex e).equivFun.symm, fun i j => ?_⟩
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  have hs : ∀ k, (b.reindex e).equivFun.symm (Pi.single (e k) 1) = b k := fun k => by
    rw [Module.Basis.equivFun_symm_apply]; simp [Pi.single_apply]
  rw [hs, hs, Out.stdSymp]
  rcases i with i | i <;> rcases j with j | j <;> have := i.2 <;> have := j.2
  · rw [hb.left_left, hl, hl, if_neg (by omega), if_neg (by omega)]
  · rw [hb.left_right, hl, hr]
    by_cases h : i = j
    · subst h; rw [if_pos rfl, if_pos (by omega)]
    · have : (i : ℕ) ≠ j := fun a => h (Fin.ext a)
      rw [if_neg h, if_neg (by omega), if_neg (by omega)]
  · rw [hb.right_left hB, hl, hr]
    by_cases h : i = j
    · subst h; rw [if_pos rfl, if_neg (by omega), if_pos (by omega)]
    · have : (i : ℕ) ≠ j := fun a => h (Fin.ext a)
      rw [if_neg h, if_neg (by omega), if_neg (by omega)]
  · rw [hb.right_right, hr, hr, if_neg (by omega), if_neg (by omega)]
end GlobalTheory.ZM
