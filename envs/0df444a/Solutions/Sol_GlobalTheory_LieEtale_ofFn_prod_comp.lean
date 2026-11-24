-- Prove2me | solution 1 for GlobalTheory.LieEtale.ofFn_prod_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:41:33.359584+00:00
-- url     : https://prove2.me/submissions/174b41ce-a6b0-425b-8387-f9ff4f5f1821

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueTangentLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LieEtale
variable {S : Scheme.{0}} {O k : Type} {P E : Over S}
namespace GlobalTheory.LieEtale
theorem _root_.solution {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ] {n : ℕ}
    (u : Fin n → (E ⟶ A)) : (List.ofFn u).prod ≫ ψ = (List.ofFn fun i => u i ≫ ψ).prod :=
  (map_list_prod (IsMonHom.monoidHom ψ E) _).trans (by rw [List.map_ofFn]; rfl)
end GlobalTheory.LieEtale
