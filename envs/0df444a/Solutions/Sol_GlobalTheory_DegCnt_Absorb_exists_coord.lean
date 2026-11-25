-- Prove2me | solution 1 for GlobalTheory.DegCnt.Absorb.exists_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:36:49.490557+00:00
-- url     : https://prove2.me/submissions/4672f5ac-4f40-456d-bf45-67b04a573e92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsStarStableIdealAbsorbingMinors
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
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Absorb
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
open NumberField
open scoped Pointwise ENNReal Classical nonZeroDivisors
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.Absorb
namespace _root_.GlobalTheory.DegCnt.Absorb
theorem _root_.solution (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) {l : ℕ} (hl : l ≤ r + 1) (a : Fin l)
    {y : V} (hy : y ∈ F.Xa a.val) :
    ∃ m : Fin l → K, (∀ b, a ≤ b → m b = 0) ∧ y = ∑ b, m b • F.e (Fin.castLE hl b) := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.Xa at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    have hc' : (c : ℕ) < a := hc
    have hca : (c : ℕ) < l := lt_trans hc' a.isLt
    refine ⟨fun b => if (b : ℕ) = c then 1 else 0, fun b hb => ?_, ?_⟩
    · have : (a : ℕ) ≤ b := hb
      simp only [ite_eq_right_iff]
      intro h
      omega
    · rw [Finset.sum_eq_single ⟨c, hca⟩]
      · simp only [if_true, one_smul]
        congr 1
      · intro b _ hb
        dsimp only
        rw [if_neg (fun h => hb (Fin.ext h)), zero_smul]
      · intro h
        exact absurd (Finset.mem_univ _) h
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, rfl⟩ := hx
    obtain ⟨n, hn, rfl⟩ := hy
    exact ⟨m + n, fun b hb => by simp [hm b hb, hn b hb],
      by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul c x _ hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨c • m, fun b hb => by simp [hm b hb], by simp [Finset.smul_sum, smul_smul]⟩
end _root_.GlobalTheory.DegCnt.Absorb
end GlobalTheory.DegCnt.Absorb
