-- Prove2me | solution 1 for GlobalTheory.T.chainStep_kernel_rank_le_mod_maxIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:12:08.619666+00:00
-- url     : https://prove2.me/submissions/5aadaab6-1856-470b-8c76-f8bb4bccde5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainStepKernelRankLeModMaxIdeal
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainStepKernelRankLeModMaxIdealStatement
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_GlobalTheory_ChainStep_rank_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s + 1 < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → ∀ (N : ℕ) (x : Fin N → Fin m → C), (∀ ν δ, V.Ge 0 (x ν δ)) → IndepMod V x → (∀ ν e, D.lev e = s + 1 → V.MM (∑ δ, x ν δ ^ (V.l ^ 2) * ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), (V.l : C) * D.al c 2 e * y δ c ^ (V.l ^ 2))) → N ≤ X.j' := by
  first | exact @GlobalTheory.ChainStep.rank_le | exact GlobalTheory.ChainStep.rank_le | (intros; apply GlobalTheory.ChainStep.rank_le <;> assumption)
end _root_.GlobalTheory.T
