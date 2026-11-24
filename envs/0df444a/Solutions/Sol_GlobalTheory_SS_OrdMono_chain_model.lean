-- Prove2me | solution 1 for GlobalTheory.SS.OrdMono.chain_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:53:36.368803+00:00
-- url     : https://prove2.me/submissions/a5710e2b-afec-4896-84a7-657f2f32f591

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ChainRuleAndJacobianCriterion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfExtendsIdOfEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobianOrderMonotoneSemistableModel
import Theorems.Thm_GlobalTheory_EtaleCoordJacobian_chain_rule_and_jacobian_criterion
import Theorems.Thm_GlobalTheory_SS_Ord_j_cst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.Ord
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdMono
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}
  {I : Type} [Fintype I] [DecidableEq I]
namespace GlobalTheory.SS.OrdMono
theorem _root_.solution (M : Model R A) (D : I → VF A) (U : M.Y.left.Opens) (t t' : I → Γ(M.Y.left, U))
    (h : IsCoord M U t) : ∃ a, jm M D U t' = (M.j.app U).hom a * jm M D U t ∧ (IsUnit a → IsCoord M U t') := by
  obtain ⟨a, h1, h2⟩ := GlobalTheory.EtaleCoordJacobian.chain_rule_and_jacobian_criterion R _ (cst M U) I t t' h
  refine ⟨a, h1 _ (M.j.app U).hom (fun i => ((D i).D _).comp (M.j.app U).hom.toAddMonoidHom)
    (fun i x y => ?_) (fun i r => ?_), h2⟩
  · show (D i).D _ ((M.j.app U).hom (x * y)) = _
    rw [map_mul, (D i).leibniz]; rfl
  · show (D i).D _ ((M.j.app U).hom (cst M U r)) = _
    rw [j_cst, (D i).const]
end GlobalTheory.SS.OrdMono
