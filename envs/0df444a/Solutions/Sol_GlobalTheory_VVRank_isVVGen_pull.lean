-- Prove2me | solution 1 for GlobalTheory.VVRank.isVVGen_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:27.345474+00:00
-- url     : https://prove2.me/submissions/5656e142-97a5-452b-bb68-37ebf6e80e04

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Theorems.Thm_GlobalTheory_VVRank_exists_twist_pull
import Theorems.Thm_GlobalTheory_VVRank_exists_theta_pull
import Theorems.Thm_GlobalTheory_VVRank_mulT_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VVRank
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
namespace GlobalTheory.VVRank
theorem _root_.solution (P : PolAV S) (N n : ℕ) {T T' : Over S} (h : T' ⟶ T)
    {t : LB.Sec (LPow P.A P.L N T)} (ht : IsVVGen P N n t) : IsVVGen P N n (pullS P.A N h t) := by
  obtain ⟨th, s1, α, U, hα, h₁, h₂⟩ := ht
  obtain ⟨α', k₁, k₂⟩ := exists_twist_pull P.A (ψ := mulT P.A T n) (hm := lift_snd _ _) (b := 1)
    P.isLB hα h (ψ' := mulT P.A T' n) (lift_snd _ _) (mulT_comm P.A h n)
  obtain ⟨U', -, k₃⟩ := exists_theta_pull P.A P.isLB h U
  exact ⟨_, _, α', U', k₁, k₂ _ _ h₁, k₃ _ _ h₂⟩
end GlobalTheory.VVRank
