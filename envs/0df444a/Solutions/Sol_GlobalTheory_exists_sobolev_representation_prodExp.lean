-- Prove2me | solution 1 for GlobalTheory.exists_sobolev_representation_prodExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:02:59.574402+00:00
-- url     : https://prove2.me/submissions/5bf99030-caac-41e6-a49f-3be3597fc487

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivExpGLineEqRightDerivPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValueAtZeroEqSumIntegralKernelIteratedDerivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSobolevRepresentationProdExp
import Theorems.Thm_GlobalTheory_SobolevRep_exists_rep

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
      (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (ε : ℝ), 0 < ε →
      ∀ (n : ℕ) (X : Fin n → 𝔤),
      ∃ (N : ℕ) (l : Fin N → List 𝔤) (κ : Fin N → (Fin n → ℝ) → ℂ),
        (∀ i, Continuous (κ i) ∧ tsupport (κ i) ⊆ Metric.closedBall 0 ε) ∧
        ∀ f : G → ℂ, h.IsSmoothFun f → ∀ g,
          f g = ∑ i, ∫ t, κ i t * (l i).foldr h.rightDeriv f (g * h.prodExp X t) :=
  fun _ _ _ _ _ _ _ h _ hε n X => SobolevRep.exists_rep h hε n X
end GlobalTheory
