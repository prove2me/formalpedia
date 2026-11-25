-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosIso.Xa_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:36:43.328149+00:00
-- url     : https://prove2.me/submissions/728bd164-f897-4be6-8e77-7978be9bbcce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormIdealDivisibility
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
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosIso
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.PosIso
theorem _root_.solution (F : FlagD H r) {j : ℕ} (hj : j ≤ r + 1) {n : ℕ} (hn : n ≤ j) {y : V} (hy : y ∈ F.Xa n) :
    ∃ p : Fin j → K, (∀ b : Fin j, n ≤ b.val → p b = 0) ∧ y = ∑ b, p b • F.e (Fin.castLE hj b) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := hy
    have hb' : b.val < n := hb
    refine ⟨Pi.single ⟨b.val, by omega⟩ 1, fun c hc => Pi.single_eq_of_ne ?_ _, ?_⟩
    · intro h; rw [h] at hc; simp at hc; omega
    · rw [Finset.sum_eq_single ⟨b.val, by omega⟩]
      · simp only [Pi.single_eq_same, one_smul]; rfl
      · intro c _ hc; rw [Pi.single_eq_of_ne hc, zero_smul]
      · simp
  | zero => exact ⟨0, by simp, by simp⟩
  | add y y' _ _ h h' =>
    obtain ⟨p, hp, rfl⟩ := h
    obtain ⟨p', hp', rfl⟩ := h'
    exact ⟨p + p', fun b hb => by simp [hp b hb, hp' b hb], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul a y _ h =>
    obtain ⟨p, hp, rfl⟩ := h
    exact ⟨a • p, fun b hb => by simp [hp b hb], by simp [Finset.smul_sum, smul_smul]⟩
end GlobalTheory.DegCnt.PosIso
