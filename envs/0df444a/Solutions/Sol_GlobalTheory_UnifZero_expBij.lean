-- Prove2me | solution 1 for GlobalTheory.UnifZero.expBij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:48:59.729009+00:00
-- url     : https://prove2.me/submissions/0b19c626-504e-4148-8c14-e91fcd38d54d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_PsiWeightZeroLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Theorems.Thm_GlobalTheory_UnifZero_exists_secConst
import Theorems.Thm_GlobalTheory_UnifZero_sec_eq_of_secConst
import Theorems.Thm_GlobalTheory_UnifZero_scal_bijective
import Theorems.Thm_GlobalTheory_UnifZero_expands_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.UnifZero
open GlobalTheory.ToricData
variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R)
variable {R I}
namespace GlobalTheory.UnifZero
theorem _root_.solution [IsHausdorff I R] (k : ℕ) : (zeroPre R I).ExpBij k := by
  have hS : ∀ s : (zeroPre R I).SecK k, ∃ x, SecConst s (scal pGK x) := fun s => by
    obtain ⟨a, ha⟩ := exists_secConst s
    obtain ⟨x, rfl⟩ := (scal_bijective (pGK (R := R))).2 a
    exact ⟨x, ha⟩
  have hF : ∀ F : Fam (zeroData R I).toPre (FractionRing R) k,
      ∃ y, SecConst (F.s PUnit.unit) (scal pBK y) := fun F => by
    obtain ⟨a, ha⟩ := exists_secConst (F.s PUnit.unit)
    obtain ⟨y, rfl⟩ := (scal_bijective (pBK (R := R) (I := I))).2 a
    exact ⟨y, ha⟩
  constructor
  · intro s
    obtain ⟨x, hx⟩ := hS s
    refine ⟨constFam k (scal pBK x), (expands_iff k hx (cs_const _ _ _)).2 rfl, fun F h => ?_⟩
    obtain ⟨y, hy⟩ := hF F
    obtain rfl := (expands_iff k hx hy).1 h
    exact DVR.fam_ext fun _ j => hy j
  · intro F
    obtain ⟨y, hy⟩ := hF F
    refine ⟨cs _ _ (scal pGK y), (expands_iff k (cs_const _ _ _) hy).2 rfl, fun s h => ?_⟩
    obtain ⟨x, hx⟩ := hS s
    obtain rfl := (expands_iff k hx hy).1 h
    exact sec_eq_of_secConst hx (cs_const _ _ _)
end GlobalTheory.UnifZero
