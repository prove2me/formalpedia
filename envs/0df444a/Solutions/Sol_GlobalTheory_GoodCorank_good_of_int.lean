-- Prove2me | solution 1 for GlobalTheory.GoodCorank.good_of_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:35:09.040665+00:00
-- url     : https://prove2.me/submissions/50efbae6-38cb-4f1b-81a0-f97abd00d574

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSaturatedGoodVectorsSmallCorank
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.GoodCorank
variable {C : Type} [Field C] {V : VF C}
variable {d : ℕ} {I J : Type} [Fintype I] [DecidableEq I]
namespace GlobalTheory.GoodCorank
theorem _root_.solution (G : Cart V d I J) {a : ZMod d} {u : I → C} {y : ℕ → I ⊕ J → C} (hy : G.IsCurve a u y)
    (h1 : ∀ b, V.Ge 0 (y 1 (Sum.inl b))) : ∃ x, G.Good a u x := by
  obtain ⟨z, hz, hz0, hzp⟩ := G.t4 (a + 1) (fun b => y 1 (Sum.inl b)) h1
    (fun b hb => hy.2.2 1 _ (by simpa using hb))
  refine ⟨y - Vpow 1 z, ⟨G.Ty.sub_mem hy.1 (G.V_mem _ hz), ?_, fun i n hn => ?_⟩, fun c => ?_⟩
  · funext n
    simp [Vpow, hy.2.1]
  · cases i with
    | zero => simp [Vpow, hy.2.2 0 n hn]
    | succ i =>
      have : z i n = 0 := hzp i n (by
        intro hc; apply hn; rw [hc]; push_cast; ring)
      simp [Vpow, hy.2.2 _ n hn, this]
  · simp [Vpow, hz0]
end GlobalTheory.GoodCorank
