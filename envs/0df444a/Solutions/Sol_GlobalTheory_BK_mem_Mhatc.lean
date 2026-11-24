-- Prove2me | solution 1 for GlobalTheory.BK.mem_Mhatc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:24:49.553463+00:00
-- url     : https://prove2.me/submissions/06d523fd-c9a1-419c-aff6-3ab73a2ca711

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_hat_coe_A
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.hat_coe

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
variable {O K}
variable {ι}
namespace GlobalTheory.BK
theorem _root_.solution {w : ι → AhatE O K l e} :
    w ∈ Mhatc O K l e ι ↔ ∀ i, ∃ x : Ahat O K l e, algebraMap _ _ x = w i := by
  constructor
  · intro hw
    have : Mhatc O K l e ι ≤ Submodule.pi Set.univ fun _ => 1 := Submodule.span_le.2 <| by
      rintro _ ⟨v, ⟨hv, -⟩, rfl⟩ i -
      exact Submodule.mem_one.2 ⟨_, (hat_coe_A l e ⟨v i, hv i⟩).symm⟩
    exact fun i => Submodule.mem_one.1 (this hw i trivial)
  · intro hw
    choose x hx using hw
    have h1 : w = ∑ i, x i • hatV O l e (Pi.single i (1 : K⟦X⟧)) := by
      ext j
      have h0 : hat O l e (0 : K⟦X⟧) = 0 := (hat_coe l e 0).trans (map_zero _)
      have h1 : hat O l e (1 : K⟦X⟧) = 1 := (hat_coe l e 1).trans (map_one _)
      simp [hatV, Pi.single_apply, apply_ite (hat O l e), h0, h1, Algebra.smul_def, hx]
    rw [h1]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨_, ⟨fun j => ?_, fun j => ?_⟩, rfl⟩) <;> rw [Pi.single_apply] <;> split_ifs <;> simp
end GlobalTheory.BK
