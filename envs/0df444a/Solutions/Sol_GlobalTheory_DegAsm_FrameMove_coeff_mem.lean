-- Prove2me | solution 1 for GlobalTheory.DegAsm.FrameMove.coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:38:27.426976+00:00
-- url     : https://prove2.me/submissions/f75d6e81-cdb4-43ad-96ac-568ce0c7ec1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SmulMemOfOne
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_sum_mem_xa
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.FrameMove
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegAsm.FrameMove
theorem _root_.solution (G : FlagD H r) {Λ : Submodule (𝓞 K) V} {aa : Fin r → Submodule (𝓞 K) K}
    (h1 : ∀ (a : Fin r) (t : K), ∀ x ∈ Λ, x - t • G.e a.castSucc ∈ G.Xa a.val → t ∈ aa a)
    (h2 : ∀ a, ∀ t ∈ aa a, t • G.e a.castSucc ∈ Λ) (n : ℕ) :
    ∀ c : Fin r → K, (∀ b : Fin r, n ≤ b.val → c b = 0) → ∑ b, c b • G.e b.castSucc ∈ Λ → ∀ b, c b ∈ aa b := by
  induction n with
  | zero => intro c hc _ b; rw [hc b (Nat.zero_le _)]; exact Submodule.zero_mem _
  | succ n ih =>
    intro c hc hx
    by_cases hn : n < r
    · let a : Fin r := ⟨n, hn⟩
      have hc' : ∀ b : Fin r, n ≤ b.val → Function.update c a 0 b = 0 := by
        intro b hb
        by_cases hba : b = a
        · simp [hba]
        · rw [Function.update_of_ne hba]
          refine hc b ?_
          have : b.val ≠ n := fun e => hba (Fin.ext e)
          omega
      have he : ∑ b, Function.update c a 0 b • G.e b.castSucc = ∑ b, c b • G.e b.castSucc - c a • G.e a.castSucc := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ (fun b => c b • G.e b.castSucc) (Finset.mem_univ a)]
        rw [Function.update_self, zero_smul, zero_add, add_sub_cancel_left]
        exact Finset.sum_congr rfl fun b hb => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hb)]
      have ha : c a ∈ aa a := h1 a _ _ hx (he ▸ sum_mem_xa G n _ hc')
      have hr := ih _ hc' (he ▸ Λ.sub_mem hx (h2 a _ ha))
      intro b
      by_cases hba : b = a
      · rw [hba]; exact ha
      · have := hr b
        rwa [Function.update_of_ne hba] at this
    · exact ih c (fun b hb => absurd (lt_of_le_of_lt hb b.2) hn) hx
end GlobalTheory.DegAsm.FrameMove
