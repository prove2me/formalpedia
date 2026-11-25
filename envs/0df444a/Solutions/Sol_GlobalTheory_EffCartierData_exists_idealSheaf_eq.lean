-- Prove2me | solution 1 for GlobalTheory.EffCartierData.exists_idealSheaf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:33:04.689903+00:00
-- url     : https://prove2.me/submissions/2c1170bc-bb84-4715-aee9-1a308dfbc3a5

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_EffCartierData_eq_idealSheaf
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_associated_of_germ
import Theorems.Thm_GlobalTheory_Cartier_isRegularFn_iff_of_isAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_resG_self
import Theorems.Thm_ReciprocityTheory_AnForm_R_ds_stalkId_eq_map


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
open GlobalTheory
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier
open GlobalTheory.EffCartierData
variable {X Y Z : Scheme.{0}}
variable (D D' : EffCartierData X)
namespace GlobalTheory.EffCartierData
theorem _root_.solution {I : X.IdealSheafData} (hI : FinalTheorems.EffCartier I) :
    ∃ D : EffCartierData X, D.idealSheaf = I := by
  choose W g hx hg hI using hI
  have reg : ∀ x, IsRegularFn (g x) := fun x => (isRegularFn_iff_of_isAffineOpen (W x).2).2 (hg x)
  have st : ∀ x y (hy : y ∈ (W x).1),
      FinalTheorems.stalkId I y = Ideal.span {(X.presheaf.germ _ y hy).hom (g x)} := fun x y hy => by
    rw [ds_stalkId_eq_map _ (W x) y hy, hI, Ideal.map_span, Set.image_singleton]
  let D : EffCartierData X :=
    { ι := X
      U := fun x => (W x).1
      f := g
      cover := eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩
      regular := reg
      assoc := fun x x' => ((reg x).resG _).associated_of_germ ((reg x').resG _) fun y hy => by
        rw [germ_resG, germ_resG, ← st, ← st] }
  exact ⟨D, (D.eq_idealSheaf fun x => ⟨W x, x, le_rfl, hx x,
    (hI x).trans (congrArg (fun a => Ideal.span {a}) (resG_self _ _).symm)⟩).symm⟩
end GlobalTheory.EffCartierData
