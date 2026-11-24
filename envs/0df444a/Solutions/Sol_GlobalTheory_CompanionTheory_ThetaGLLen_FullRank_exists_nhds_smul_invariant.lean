-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.exists_nhds_smul_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:43:14.826273+00:00
-- url     : https://prove2.me/submissions/9cc7ed18-1cdf-44ba-af08-0f88637c9742

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient

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
namespace GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
theorem _root_.solution : ∀ (H X : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace X] [MulAction H X] [ContinuousSMul H X] (f : SB X), ∃ U ∈ 𝓝 (1 : H), ∀ g ∈ U, ∀ x : X, f.1 (g • x) = f.1 x := by
  intro H X _ _ _ _ _ _ f
  have hc : IsCompact (tsupport f.1) := f.2.2
  have hl : IsLocallyConstant fun p : H × X => f.1 (p.1 • p.2) - f.1 p.2 :=
    (f.2.1.comp_continuous (continuous_fst.smul continuous_snd)).comp₂
      (f.2.1.comp_continuous continuous_snd) (· - ·)
  have hS : IsOpen {p : H × X | f.1 (p.1 • p.2) = f.1 p.2} := by
    have := hl.isOpen_fiber 0
    simpa only [sub_eq_zero] using this
  have hsub : ({1} : Set H) ×ˢ tsupport f.1 ⊆ {p : H × X | f.1 (p.1 • p.2) = f.1 p.2} := by
    rintro ⟨g, x⟩ ⟨hg, -⟩
    have : g = 1 := hg
    simp [this]
  obtain ⟨U, W, hU, hW, h1, hCW, hUW⟩ := generalized_tube_lemma isCompact_singleton hc hS hsub
  have h1U : (1 : H) ∈ U := h1 rfl
  refine ⟨U ∩ (fun g : H => g⁻¹) ⁻¹' U, Filter.inter_mem (hU.mem_nhds h1U)
    (continuous_inv.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds h1U)), ?_⟩
  rintro g ⟨hg, hg'⟩ x
  by_cases hx : x ∈ W
  · exact hUW (show (g, x) ∈ U ×ˢ W from ⟨hg, hx⟩)
  by_cases hgx : g • x ∈ W
  · have h2 : f.1 (g⁻¹ • g • x) = f.1 (g • x) := hUW (show (g⁻¹, g • x) ∈ U ×ˢ W from ⟨hg', hgx⟩)
    rw [inv_smul_smul] at h2
    exact h2.symm
  · rw [image_eq_zero_of_notMem_tsupport fun h => hgx (hCW h),
      image_eq_zero_of_notMem_tsupport fun h => hx (hCW h)]
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
