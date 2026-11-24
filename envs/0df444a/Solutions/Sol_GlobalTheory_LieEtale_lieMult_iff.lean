-- Prove2me | solution 1 for GlobalTheory.LieEtale.lieMult_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:59:25.488807+00:00
-- url     : https://prove2.me/submissions/795a82e0-01c7-4a65-907c-c68e07d13a9e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueTangentLift
import Theorems.Thm_GlobalTheory_LieEtale_isLieEigen_iff

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
variable {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S)
variable {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (τ : O →+* k)
namespace GlobalTheory.LieEtale
theorem _root_.solution (n : ℕ) : LieMult act x τ n ↔
    ∃ v : Fin n → (epsPt x ⟶ G), (∀ i, Eig (epsPtZero x) (epsPtScale x) act.act τ (v i)) ∧
      ∀ w, Eig (epsPtZero x) (epsPtScale x) act.act τ w →
        ∃! c : Fin n → k, w = (List.ofFn fun i => epsPtScale x (c i) ≫ v i).prod := by
  simp only [LieMult, isLieEigen_iff]
  refine exists_congr fun v => and_congr_right fun _ => forall_congr' fun w =>
    imp_congr_right fun _ => existsUnique_congr fun c => ⟨?_, fun h => ⟨_, fun _ => rfl, h⟩⟩
  rintro ⟨u, hu, rfl⟩
  obtain rfl : u = fun i => epsPtScale x (c i) ≫ v i :=
    funext fun i => Over.OverMorphism.ext (hu i)
  rfl
end GlobalTheory.LieEtale
