-- Prove2me | solution 1 for GlobalTheory.SS.OrdMono.isUnit_jm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:09:37.424416+00:00
-- url     : https://prove2.me/submissions/a9a88d80-127e-4772-a640-a81d490e72b2

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
import Theorems.Thm_GlobalTheory_SS_OrdMono_etale_comp
import Theorems.Thm_GlobalTheory_SS_OrdMono_isUnit_of_local
import Theorems.Thm_GlobalTheory_EtaleCoordJacobian_chain_rule_and_jacobian_criterion
import Theorems.Thm_GlobalTheory_SS_Ord_isOpenImmersion_j
import Theorems.Thm_GlobalTheory_SS_Ord_j_cst
import Theorems.Thm_GlobalTheory_SS_Ord_rs_cstK
import Theorems.Thm_GlobalTheory_SS_Ord_rs_jac
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
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Over (Sp K)} {π : R} {I : Type} [Fintype I] [DecidableEq I]
namespace GlobalTheory.SS.OrdMono
theorem _root_.solution (M : Model R A) {D : I → VF A} (hD : IsFrame D) {U : M.Y.left.Opens} (hU : IsAffineOpen U)
    {t : I → Γ(M.Y.left, U)} (ht : IsCoord M U t) : IsUnit (jm M D U t) := by
  have := isOpenImmersion_j M
  refine isUnit_of_local _ _ _ fun z hz => ?_
  obtain ⟨U', t', hz', hu⟩ := hD.2 z
  obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := A.left) (U := U' ⊓ M.j ⁻¹ᵁ U) ⟨hz', hz⟩
  have h1 : V ≤ U' := fun _ h => (hle h).1
  have h2 : V ≤ M.j ⁻¹ᵁ U := fun _ h => (hle h).2
  refine ⟨V, h2, hzV, ?_⟩
  have he := etale_comp _ t _ ht (M.j.etale_appLE hU hV h2)
  obtain ⟨a, ha, -⟩ := GlobalTheory.EtaleCoordJacobian.chain_rule_and_jacobian_criterion R _ _ I _ (fun i => rs _ h1 (t' i)) he
  have hb := ha _ (RingHom.id _) (fun i => (D i).D V) (fun i => (D i).leibniz V) (fun i r => by
    have : ((M.j.appLE U V h2).hom.comp (cst M U)) r = cstK A V (algebraMap R K r) := by
      rw [← rs_cstK h2, ← j_cst]; rfl
    rw [this, (D i).const])
  have hc : IsUnit (jac D V fun i => rs _ h1 (t' i)) := by rw [← rs_jac]; exact hu.map _
  rw [jm, rs_jac]
  exact isUnit_of_mul_isUnit_right (show IsUnit (_ * _) from hb.subst hc)
end GlobalTheory.SS.OrdMono
