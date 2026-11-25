-- Prove2me | solution 1 for GlobalTheory.gm_div_pull_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:32:18.928062+00:00
-- url     : https://prove2.me/submissions/2ea5da4f-bfbc-4560-8a09-2aeab4ee0097

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {I : Type} [SmallCategory I] [IsCofiltered I]
variable (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
namespace GlobalTheory
theorem _root_.solution {Y Z : Scheme.{0}} (M N : LB Y) (F : Z ⟶ Y) (z : Z) (p q : N.ι × M.ι)
    (hz : F z ∈ (LB.div N M).U p ⊓ (LB.div N M).U q) :
    gm (𝟙 Z) z _ ((LB.div (N.pull F) (M.pull F)).g (fun _ => p.1, fun _ => p.2) (fun _ => q.1, fun _ => q.2)) =
      gm F z _ ((LB.div N M).g p q) := by
  refine (gm_div (M.pull F) (N.pull F) (𝟙 Z) z (fun _ => p.1, fun _ => p.2) (fun _ => q.1, fun _ => q.2)
    ⟨⟨mem_pull.2 hz.1.1, mem_pull.2 hz.1.2⟩, mem_pull.2 hz.2.1, mem_pull.2 hz.2.2⟩).trans
    (Eq.trans ?_ (gm_div M N F z p q hz).symm)
  exact congrArg₂ (· * ·) (gm_pull_g N F (𝟙 Z) z _ _ (mem_pull.2 hz.1.1) (mem_pull.2 hz.2.1))
    (congrArg (·⁻¹) (gm_pull_g M F (𝟙 Z) z _ _ (mem_pull.2 hz.1.2) (mem_pull.2 hz.2.2)))
end GlobalTheory
