-- Prove2me | solution 1 for GlobalTheory.ExtUnique.intAct_unique_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:42:05.860506+00:00
-- url     : https://prove2.me/submissions/29af216c-c883-437f-848b-8707c9f6500f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Theorems.Thm_GlobalTheory_ExtUnique_spec_fractionRing
import Theorems.Thm_GlobalTheory_ExtUnique_oAct_ext
import Theorems.Thm_GlobalTheory_ExtUnique_existsUnique_oAct_pullback
import Theorems.Thm_GlobalTheory_ExtUnique_intAct_pullback
import Theorems.Thm_GlobalTheory_ExtUnique_splitTorusAff_flat_and_isSeparated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ExtUnique
variable {U S : Scheme.{0}} {j : U ⟶ S} [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
namespace GlobalTheory.ExtUnique
theorem _root_.solution (a : OAct ℤ (splitTorusAff (CommRingCat.of ℤ) ℤ))
    (ha : OAct.pullback (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) _ a = intAct _) : a = intAct _ := by
  obtain ⟨_, _⟩ := spec_fractionRing ℤ ℚ
  obtain ⟨_, _⟩ := splitTorusAff_flat_and_isSeparated (CommRingCat.of ℤ) ℤ
  exact (existsUnique_oAct_pullback _ _ fun n => ⟨_, intAct_pullback _ _ n⟩).unique ha
    (oAct_ext fun n => intAct_pullback _ _ n)
end GlobalTheory.ExtUnique
