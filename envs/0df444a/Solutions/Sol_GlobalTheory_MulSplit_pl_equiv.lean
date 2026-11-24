-- Prove2me | solution 1 for GlobalTheory.MulSplit.pl_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:11:36.337808+00:00
-- url     : https://prove2.me/submissions/36813317-e273-4229-a590-fe03e8cb7f9d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights
import Theorems.Thm_GlobalTheory_MulSplit_pl_pl
import Theorems.Thm_GlobalTheory_MulSplit_pl_id
import Theorems.Thm_GlobalTheory_MulSplit_pl_mem_Sg

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
theorem _root_.solution (hL : L.IsLB) {h h' : Y ⟶ Y} (hh : h ≫ p = p) (hh' : h' ≫ p = p) (e : h ≫ h' = 𝟙 Y)
    (e' : h' ≫ h = 𝟙 Y) {D E : (Y ⟶ X) →₀ ℤ} (hE : D.mapDomain (h ≫ ·) = E) :
    Nonempty (Sg L p D ≃ₗ[Γ(B, ⊤)] Sg L p E) :=
  ⟨{ toFun := fun v => ⟨pl L h hh v.1, pl_mem_Sg hL hh v.2 hE⟩
     invFun := fun v => ⟨pl L h' hh' v.1, pl_mem_Sg hL hh' v.2 (by
       rw [← hE, ← Finsupp.mapDomain_comp]
       refine (congrArg (Finsupp.mapDomain · D) (funext fun ψ => ?_)).trans Finsupp.mapDomain_id
       show h' ≫ h ≫ ψ = ψ
       rw [← Category.assoc, e', Category.id_comp])⟩
     map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
     map_smul' := fun _ _ => Subtype.ext (map_smul (pl L h hh) _ _)
     left_inv := fun _ => Subtype.ext ((pl_pl _ _ (Category.id_comp _) e' _).trans (pl_id _ rfl _))
     right_inv := fun _ => Subtype.ext ((pl_pl _ _ (Category.id_comp _) e _).trans (pl_id _ rfl _)) }⟩
end GlobalTheory.MulSplit
