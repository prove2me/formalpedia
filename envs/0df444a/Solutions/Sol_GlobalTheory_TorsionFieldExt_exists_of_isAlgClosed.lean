-- Prove2me | solution 1 for GlobalTheory.TorsionFieldExt.exists_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:46:03.514234+00:00
-- url     : https://prove2.me/submissions/18e7a046-3572-4361-ac91-ca18f1fecfc4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionPointsFieldExtension
import Theorems.Thm_GlobalTheory_TorsionFieldExt_comp_injective
import Theorems.Thm_GlobalTheory_TorsionFieldExt_card_torsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TorsionFieldExt
variable {S : Scheme.{0}}
namespace GlobalTheory.TorsionFieldExt
theorem _root_.solution (hL : Out.Laws) (P : Out.PolAV S) {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K]
    [IsAlgClosed Ω] {x : Sp K ⟶ S} {x' : Sp Ω ⟶ S} (u : Over.mk x' ⟶ Over.mk x) {n : ℕ} (hK : (n : K) ≠ 0)
    (hΩ : (n : Ω) ≠ 0) (z : Over.mk x' ⟶ P.A) (hz : z ^ n = 1) :
    ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ u ≫ y = z := by
  have hn' : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hK Nat.cast_zero)
  have c₁ := card_torsion hL P x hK
  have c₂ := card_torsion hL P x' hΩ
  have : Finite {y : Over.mk x' ⟶ P.A // y ^ n = 1} := Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
  let F : {y : Over.mk x ⟶ P.A // y ^ n = 1} → {y : Over.mk x' ⟶ P.A // y ^ n = 1} := fun a =>
    ⟨u ≫ a.1, by rw [← MonObj.comp_pow, a.2, MonObj.comp_one]⟩
  have hF : Function.Bijective F := (Nat.bijective_iff_injective_and_card F).2
    ⟨fun a b h => Subtype.ext (comp_injective u _ (congrArg Subtype.val h)), c₁.trans c₂.symm⟩
  obtain ⟨a, ha⟩ := hF.2 ⟨z, hz⟩
  exact ⟨a.1, a.2, congrArg Subtype.val ha⟩
end GlobalTheory.TorsionFieldExt
