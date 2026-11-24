-- Prove2me | solution 1 for GlobalTheory.CubeValues.hol_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:02:45.738215+00:00
-- url     : https://prove2.me/submissions/fd7e1041-fe9b-452a-a8f2-1cb443055a2a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.CubeValues
variable {A : Over (Sp ℂ)} [GrpObj A] {L₀ : LB A.left} {g : ℕ} (u : HolUnif A L₀ g)
namespace GlobalTheory.CubeValues
theorem _root_.solution (a : Fin 3) (U : A.left.Opens) (f : Γ(A.left, U)) :
    IsOpen {w : Fin 3 → Fin g → ℂ | w ∈ (Set.univ : Set _) ∧ ⊤ ≤ (u.ex (w a)).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w : Fin 3 → Fin g → ℂ => valAt' (u.ex (w a)).left U f)
        {w | w ∈ (Set.univ : Set _) ∧ ⊤ ≤ (u.ex (w a)).left ⁻¹ᵁ U} := by
  obtain ⟨ho, hd⟩ := u.hol U f
  have hset : {w : Fin 3 → Fin g → ℂ | w ∈ (Set.univ : Set _) ∧ ⊤ ≤ (u.ex (w a)).left ⁻¹ᵁ U} =
      (fun w : Fin 3 → Fin g → ℂ => w a) ⁻¹' {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} := by
    ext w; simp
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact ho.preimage (continuous_apply a)
  · exact hd.comp (differentiable_apply a).differentiableOn (fun w hw => hw.2)
end GlobalTheory.CubeValues
