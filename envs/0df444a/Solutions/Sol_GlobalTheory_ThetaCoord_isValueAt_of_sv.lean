-- Prove2me | solution 1 for GlobalTheory.ThetaCoord.isValueAt_of_sv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:42:45.83144+00:00
-- url     : https://prove2.me/submissions/b6fc5996-20ec-49dc-8df7-dfe4e0bfa327

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Statements_TorsionEndomorphisms_ExistsGeneratorOfIsField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverOfSubsingleton
import Theorems.Thm_GlobalTheory_ThetaCoord_sv_of_isValueAt
import Theorems.Thm_GlobalTheory_ThetaPtExist_exists_isValueAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_exists_chart


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaCoord
open CommPairing GlobalLift VVRank
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T T' : Over S} {k : ℤ}
namespace GlobalTheory.ThetaCoord
theorem _root_.solution (hL : L.IsLB) {s : LB.Sec (LPow A L k T)} {w : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => w.left) (fun _ => k))} (hτ : τ.IsGen)
    {v : Γ(T.left, ⊤)} (H : ∀ (z : T.left) (J), Good L z J →
      sv A s (lift (𝟙 T) w).left z J = gs (𝟙 T.left) z ⊤ v * (val τ (𝟙 T.left) z J).val) :
    IsValueAt A L k s w τ v := by
  obtain ⟨v₀, h₀⟩ := ThetaPtExist.exists_isValueAt hL s w τ hτ
  obtain rfl : v₀ = v := fn_ext fun z _ => by
    choose J hJ using fun χ : T.left ⟶ A.left => exists_chart hL (χ z)
    have := sv_of_isValueAt h₀ (𝟙 T) hJ
    rw [Category.id_comp, H z J hJ] at this
    exact (Units.mul_left_inj _).1 this.symm
  exact h₀
end GlobalTheory.ThetaCoord
