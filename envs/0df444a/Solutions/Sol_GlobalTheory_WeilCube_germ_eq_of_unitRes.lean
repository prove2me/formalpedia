-- Prove2me | solution 1 for GlobalTheory.WeilCube.germ_eq_of_unitRes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:55:50.6693+00:00
-- url     : https://prove2.me/submissions/a6f66961-8c7d-47fa-848d-1a7563a866a4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
open GlobalTheory.WeilCube
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (c : CubicalStr A Lr)
namespace GlobalTheory.WeilCube
theorem _root_.solution {T : Over S} {V : T.left.Opens} {p : T.left} (hp : p ∈ V) {e e' : Γ(T.left, ⊤)ˣ}
    (h : unitRes V e = unitRes V e') : gm (𝟙 _) p ⊤ e = gm (𝟙 _) p ⊤ e' := by
  have v : ∀ a : Γ(T.left, ⊤)ˣ, gm V.ι (⟨p, hp⟩ : V.toScheme) ⊤ a =
      gm (𝟙 V.toScheme) (⟨p, hp⟩ : V.toScheme) ⊤ (unitRes V a) := fun a =>
    (congrArg (fun q => gm q (⟨p, hp⟩ : V.toScheme) ⊤ a) (Category.id_comp V.ι).symm).trans
      (gm_pull (𝟙 _) V.ι ⟨p, hp⟩ ⊤ trivial a).symm
  exact gm_inj V.ι ⟨p, hp⟩ (U := ⊤) (U' := ⊤) trivial trivial ((v e).trans ((congrArg _ h).trans (v e').symm))
end GlobalTheory.WeilCube
