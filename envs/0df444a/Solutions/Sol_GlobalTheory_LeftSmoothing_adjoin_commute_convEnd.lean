-- Prove2me | solution 1 for GlobalTheory.LeftSmoothing.adjoin_commute_convEnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:49:01.403699+00:00
-- url     : https://prove2.me/submissions/36f6a27b-ebb1-4ed8-a716-d7e1833b27eb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftSmoothingProdExpSmoothCommute
import Theorems.Thm_GlobalTheory_LeftSmoothing_commute_convEnd
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.LeftSmoothing
open scoped Manifold Topology
open Set Filter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
variable (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin n → 𝔤) (κ : (Fin n → ℝ) → ℂ)
variable {h X κ}
namespace GlobalTheory.LeftSmoothing
theorem _root_.solution (hκ : Continuous κ) (hκs : HasCompactSupport κ)
    {T : Module.End ℂ (h.smoothFuns (F := ℂ))}
    (hT : T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ)))) :
    T * convEnd h X hκ hκs = convEnd h X hκ hκs * T := by
  have hle : Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) ≤
      Subalgebra.centralizer ℂ {convEnd h X hκ hκs} := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨Z, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro A hA
    rw [Set.mem_singleton_iff] at hA
    subst hA
    exact (commute_convEnd hκ hκs Z).symm
  have := (Subalgebra.mem_centralizer_iff ℂ).1 (hle hT) _ rfl
  exact this.symm
end GlobalTheory.LeftSmoothing
