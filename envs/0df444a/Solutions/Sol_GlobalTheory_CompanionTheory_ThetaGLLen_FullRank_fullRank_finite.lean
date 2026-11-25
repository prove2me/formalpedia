-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.FullRank.fullRank_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:32:28.489842+00:00
-- url     : https://prove2.me/submissions/2e242e02-f73f-4cad-b498-015b09703fb5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_finite_coinv_of_common_generator
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_exists_gl_eq_mul_of_rank
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_exists_common_generator
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_continuous_rAct_inv
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_subset
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball


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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a c : Type} [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
namespace GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
theorem _root_.solution (κ : ℕ) (hκ : κ = Fintype.card c) (θ : GL a k →* ℂˣ) :
    Module.Finite ℂ (SB (RankIn k a c {κ}) ⧸ twRel (rightRep (k := k) a c κ) θ) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨SplitWeil.cball s, SplitWeil.add_mem_cball⟩, by simp [SplitWeil.cball]⟩,
      SplitWeil.neg_mem_cball⟩, SplitWeil.isOpen_cball s⟩, hs⟩⟩
  have : TotallyDisconnectedSpace k := inferInstance
  have : TotallyDisconnectedSpace (Matrix a a k) := inferInstanceAs (TotallyDisconnectedSpace (a → a → k))
  have : LocallyCompactSpace (Matrix c a k) := inferInstanceAs (LocallyCompactSpace (c → a → k))
  haveI : TotallyDisconnectedSpace (GL a k) :=
    ⟨(isTotallyDisconnected_of_image (f := fun g : GL a k => g.val) SplitFlip.isEmbedding_val_GL.continuous.continuousOn
      SplitFlip.isEmbedding_val_GL.injective (isTotallyDisconnected_of_totallyDisconnectedSpace _))⟩
  letI := rMul (k := k) (a := a) (c := c) κ
  have hsm : ∀ (g : GL a k) (x : RankIn k a c {κ}), g • x = rAct {κ} x g⁻¹ := fun _ _ => rfl
  haveI : ContinuousSMul (GL a k) (RankIn k a c {κ}) := ⟨continuous_rAct_inv κ⟩
  haveI : MulAction.IsPretransitive (GL a k) (RankIn k a c {κ}) := ⟨fun x y => by
    obtain ⟨g, hg⟩ := exists_gl_eq_mul_of_rank k a c x.1 y.1 (x.2.trans hκ) (y.2.trans hκ)
    refine ⟨g⁻¹, Subtype.ext ?_⟩
    rw [hsm, inv_inv, rAct_val, hg]⟩
  have hXo : IsOpen {x : Matrix c a k | x.rank ∈ ({κ} : Set ℕ)} := by
    convert isOpen_le_rank (k := k) (a := a) (b := c) κ using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => h.ge, fun h => le_antisymm ((Matrix.rank_le_card_height x).trans hκ.ge) h⟩
  haveI : LocallyCompactSpace (RankIn k a c {κ}) := hXo.locallyCompactSpace
  have hop : ∀ x : RankIn k a c {κ}, IsOpenMap fun g : GL a k => g • x :=
    fun x => isOpenMap_smul_of_sigmaCompact x
  have hρ : ∀ (g : GL a k) (f : SB (RankIn k a c {κ})) (x : RankIn k a c {κ}),
      (rightRep (k := k) a c κ g f).1 x = f.1 (g⁻¹ • x) := by
    intro g f x
    show _ = f.1 (rAct {κ} x g⁻¹⁻¹)
    rw [inv_inv]
    rfl
  exact finite_coinv_of_common_generator _ _ _ _ (exists_common_generator (rightRep (k := k) a c κ) hρ hop SplitFlip.isCompact_KO SplitFlip.isOpen_KO)
end GlobalTheory.CompanionTheory.ThetaGLLen.FullRank
