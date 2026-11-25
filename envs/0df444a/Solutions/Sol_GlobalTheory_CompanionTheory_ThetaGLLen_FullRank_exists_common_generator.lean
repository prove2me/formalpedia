-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_common_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:23:22.628467+00:00
-- url     : https://prove2.me/submissions/404da3d2-489b-4233-8f54-6fdbde13cefb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_Reached_add
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_reached_all

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaGLLen GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
variable {H X : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [TopologicalSpace X] [MulAction H X]
variable [T2Space X] [ContinuousSMul H X]
namespace GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
theorem _root_.solution [T2Space H] [TotallyDisconnectedSpace H] [MulAction.IsPretransitive H X]
    (ρ : Representation ℂ H (SB X))
    (hρ : ∀ (g : H) (f : SB X) (x : X), (ρ g f).1 x = f.1 (g⁻¹ • x))
    (hopen : ∀ x : X, IsOpenMap fun g : H => g • x) {K : Subgroup H} (hK : IsCompact (K : Set H))
    (hKo : IsOpen (K : Set H)) (w w' : SB X) :
    ∃ t : SB X, w ∈ Submodule.span ℂ (Set.range fun g : H => ρ g t) ∧
      w' ∈ Submodule.span ℂ (Set.range fun g : H => ρ g t) := by
  by_cases hX : Nonempty X
  · obtain ⟨x₀⟩ := hX
    obtain ⟨_, _, t, _, h, h'⟩ := (reached_all ρ hρ hopen hK hKo x₀ w).add hρ hopen hK
      (reached_all ρ hρ hopen hK hKo x₀ w')
    exact ⟨t, h, h'⟩
  · haveI : IsEmpty X := not_nonempty_iff.1 hX
    have h0 : ∀ u : SB X, u = 0 := fun u => Subtype.ext (funext fun x => isEmptyElim x)
    exact ⟨0, by rw [h0 w]; exact Submodule.zero_mem _, by rw [h0 w']; exact Submodule.zero_mem _⟩
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
