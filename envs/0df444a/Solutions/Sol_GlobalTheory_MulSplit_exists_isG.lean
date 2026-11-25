-- Prove2me | solution 1 for GlobalTheory.MulSplit.exists_isG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:49.578345+00:00
-- url     : https://prove2.me/submissions/67e5cf07-cce5-4449-aa60-8d3815174496

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights
import Theorems.Thm_GlobalTheory_MulSplit_mem_Sg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_genSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.MulSplit
variable {X Y B : Scheme.{0}} (L : LB X) (p : Y ⟶ B)
variable {L p}
variable {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.MulSplit
theorem _root_.solution (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ u : (Vals L p)ˣ, IsG (dv φ ε) u ∧ ∀ i : Idx L p, u.val i = (val t i.1.2.2 i.1.1 i.1.2.1).val := by
  refine ⟨⟨fun i => (val t i.1.2.2 i.1.1 i.1.2.1).val, fun i => ((val t i.1.2.2 i.1.1 i.1.2.1)⁻¹).val,
    funext fun i => Units.mul_inv _, funext fun i => Units.inv_mul _⟩, ⟨?_, ?_⟩, fun _ => rfl⟩
  · exact (mem_Sg hL rfl _).2 ⟨genSec t ht, funext fun i => sval_genSec t ht _ _ i.2.1⟩
  · refine (mem_Sg hL ?_ _).2 ⟨genSec (LB.invGen L φ ε t) (DVR.invGen_isGen _ _ _ _ ht), funext fun i =>
      (sval_genSec _ _ _ _ i.2.1).trans (congrArg Units.val (val_inv t _))⟩
    simp only [dv, Finsupp.single_neg, Finset.sum_neg_distrib]
end GlobalTheory.MulSplit
