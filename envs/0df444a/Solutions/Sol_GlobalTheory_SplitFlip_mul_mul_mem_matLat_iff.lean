-- Prove2me | solution 1 for GlobalTheory.SplitFlip.mul_mul_mem_matLat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:54:55.798596+00:00
-- url     : https://prove2.me/submissions/f0103fa6-11e2-46dd-82b0-e59218d7d68b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_mem_matLat_stdLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitFlip
theorem _root_.solution {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {g : GL m k} {h : GL n k} (hg : g ∈ KO k m) (hh : h ∈ KO k n) (X : Matrix m n k) :
    g.val * X * h.val ∈ matLat m (stdLat k n) ↔ X ∈ matLat m (stdLat k n) := by
  have key : ∀ {g : GL m k} {h : GL n k}, g ∈ KO k m → h ∈ KO k n → ∀ X ∈ matLat m (stdLat k n),
      g.val * X * h.val ∈ matLat m (stdLat k n) := fun hg hh X hX =>
    mem_matLat_stdLat.2 fun i j => Subring.sum_mem _ fun l _ => mul_mem (Subring.sum_mem _ fun l' _ =>
      mul_mem (((mem_KO_iff _).1 hg).1 _ _) (mem_matLat_stdLat.1 hX _ _)) (((mem_KO_iff _).1 hh).1 _ _)
  refine ⟨fun H => ?_, key hg hh X⟩
  have := key (inv_mem hg) (inv_mem hh) _ H
  rwa [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
    Units.inv_mul, Matrix.one_mul] at this
end GlobalTheory.SplitFlip
