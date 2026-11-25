-- Prove2me | solution 1 for GlobalTheory.SS.frobG_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:09:04.179782+00:00
-- url     : https://prove2.me/submissions/fd503079-c5fd-44da-8e42-8da124d6f37e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.SS
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw
section ProjLine
open Polynomial IsDedekindDomain
variable (k : Type) [Field k]
variable {k}
variable (k)
private theorem appLE_apply_of_eq_id' {Y : Scheme.{0}} (φ : Y ⟶ Y) (hφ : φ = 𝟙 Y) {U : Y.Opens}
    (e : U ≤ φ ⁻¹ᵁ U) (f : Γ(Y, U)) : (φ.appLE U U e).hom f = f := by
  subst hφ
  show (Y.presheaf.map (𝟙 (Opposite.op U))).hom f = f
  rw [CategoryTheory.Functor.map_id]
  rfl
end ProjLine
end GlobalTheory.SS
end
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SS
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw
namespace GlobalTheory.SS
theorem _root_.solution {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] : FrobG G 1 1 := by
  unfold FrobG
  refine ⟨inferInstanceAs (IsMonHom (𝟙 G)), fun U _ f => ⟨1, le_rfl, ?_⟩⟩
  have hh : Over.Hom.left (show G ⟶ G from (1 : End G) ^ 1) = 𝟙 G.left := by
    exact congrArg (fun φ => Over.Hom.left φ) (pow_one (1 : End G))
  refine ⟨by rw [hh]; rfl, ?_⟩
  rw [appLE_apply_of_eq_id' _ hh]
  simp
end GlobalTheory.SS
