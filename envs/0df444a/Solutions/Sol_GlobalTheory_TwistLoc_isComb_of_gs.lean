-- Prove2me | solution 1 for GlobalTheory.TwistLoc.isComb_of_gs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:12:21.255848+00:00
-- url     : https://prove2.me/submissions/5bdcbbae-b38c-4c9e-bd80-e0249e0c6f1a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TwistLoc
variable {X X' Y Y₁ Y₂ T Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K] {m : ℕ}
namespace GlobalTheory.TwistLoc
theorem _root_.solution {π : Y ⟶ T} {N : LB Y} {b : Fin m → LB.Sec N} {s : LB.Sec N} {c : Fin m → Γ(T, ⊤)}
    (h : ∀ y j, y ∈ N.U j →
      gs (𝟙 Y) y (N.U j) (s.f j) = ∑ i, gs (𝟙 Y ≫ π) y ⊤ (c i) * gs (𝟙 Y) y (N.U j) ((b i).f j)) :
    IsComb π b s c := fun j => fn_ext fun y hy => (h y j hy).trans (gs_comb π _ c _ (𝟙 Y) y hy).symm
end GlobalTheory.TwistLoc
