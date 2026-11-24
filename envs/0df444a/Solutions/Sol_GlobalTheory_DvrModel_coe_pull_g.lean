-- Prove2me | solution 1 for GlobalTheory.DvrModel.coe_pull_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:03:23.05485+00:00
-- url     : https://prove2.me/submissions/4165b622-1098-4e1e-973c-6e7b3cdd6fc1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.DvrModel
open PrimeSection
variable {V : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {K : Type u} [Field K] [Algebra V K] [IsFractionRing V K] {ϖ : V}
  {H : Scheme.{u}} {f : H ⟶ Spec (.of V)}
  {HK : Scheme.{u}} {j : HK ⟶ H} {fK : HK ⟶ Spec (.of K)}
  {Hs : Scheme.{u}} {i : Hs ⟶ H} {fs : Hs ⟶ Spec (.of (ResidueField V))}
local notation "cst[" f ", " R ", " c "]" =>
  ConcreteCategory.hom (Scheme.Hom.appTop f)
    (ConcreteCategory.hom (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of R))) c)
namespace GlobalTheory.DvrModel
theorem _root_.solution {X Y : Scheme.{u}} (L : LB X) (φ : Y ⟶ X) (a b : PUnit → L.ι) :
    ((L.pull φ).g a b : Γ(Y, (L.pull φ).U a ⊓ (L.pull φ).U b)) =
      φ.appLE (L.U (a ⟨⟩) ⊓ L.U (b ⟨⟩)) _ (inf_le_inf (pull_U L φ a).le (pull_U L φ b).le)
        (L.g (a ⟨⟩) (b ⟨⟩) : Γ(X, L.U (a ⟨⟩) ⊓ L.U (b ⟨⟩))) :=
  congrArg Units.val (LB.lcg_pull L φ a b)
end GlobalTheory.DvrModel
