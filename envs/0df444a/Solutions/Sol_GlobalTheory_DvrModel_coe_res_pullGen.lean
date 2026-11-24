-- Prove2me | solution 1 for GlobalTheory.DvrModel.coe_res_pullGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:06:01.783955+00:00
-- url     : https://prove2.me/submissions/97fb22ff-8fcd-4378-ac79-304fb7d80a23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Theorems.Thm_GlobalTheory_PrimeSection_res_appLE


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
theorem _root_.solution {X Y Z : Scheme.{u}} (L : LB X) {κ : Type u} [Fintype κ]
    (φ : κ → (Y ⟶ X)) (ε : κ → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (a : κ → L.ι)
    {A : Z.Opens} (hA : A ≤ LB.wchart L (fun k ↦ h ≫ φ k) a) :
    (res hA (LB.ts (LB.pullGen L φ ε c h) a) : Γ(Z, A)ˣ) =
      h.appLE (LB.wchart L φ a) A (hA.trans (LB.wchart_comp_le L h φ a))
        (LB.ts c a : Γ(Y, LB.wchart L φ a)ˣ) :=
  res_appLE h (LB.wchart_comp_le L h φ a) hA _
end GlobalTheory.DvrModel
