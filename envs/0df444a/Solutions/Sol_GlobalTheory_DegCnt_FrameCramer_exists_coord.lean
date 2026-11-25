-- Prove2me | solution 1 for GlobalTheory.DegCnt.FrameCramer.exists_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:08:55.082185+00:00
-- url     : https://prove2.me/submissions/e5024f5b-1042-430d-9c1a-63fcf299825b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemOfForall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairingCramerOfLeadingCoeffs
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
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FrameCramer
open Matrix
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.FrameCramer
theorem _root_.solution (F : FlagD H r) {l : ℕ} (hl : l ≤ r) {m : ℕ} (hm : m ≤ l) {x : V} (hx : x ∈ F.Xa m) :
    ∃ c : Fin l → K, (∀ b : Fin l, m ≤ b.val → c b = 0) ∧
      x = ∑ b, c b • F.e (Fin.castLE (hl.trans (Nat.le_succ r)) b) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    have hb' : b.val < m := hb
    refine ⟨Pi.single ⟨b.val, by omega⟩ 1, fun c hc => Pi.single_eq_of_ne (fun h => ?_) _, ?_⟩
    · rw [h] at hc; simp at hc; omega
    · rw [Finset.sum_eq_single ⟨b.val, by omega⟩]
      · simp; rfl
      · intro c _ hc; simp [Pi.single_eq_of_ne hc]
      · simp
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨c + d, fun b hb => by simp [hc b hb, hd b hb], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul t x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨t • c, fun b hb => by simp [hc b hb], by simp [Finset.smul_sum, smul_smul]⟩
end GlobalTheory.DegCnt.FrameCramer
