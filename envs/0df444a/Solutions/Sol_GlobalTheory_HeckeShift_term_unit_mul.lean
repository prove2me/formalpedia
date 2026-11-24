-- Prove2me | solution 1 for GlobalTheory.HeckeShift.term_unit_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:49:40.026803+00:00
-- url     : https://prove2.me/submissions/ba125ec1-d0ac-483e-b769-9da54faf8422

import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeMellinGaussIntegrandUnitMul
import Theorems.Thm_GlobalTheory_HeckeShift_factor_shift
import Theorems.Thm_GlobalTheory_HeckeShift_sum_ulog
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
namespace GlobalTheory.HeckeShift
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I]
    (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ) (u : (𝓞 K)ˣ) (α : K) (y : I → ℝ),
    GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (((u : 𝓞 K) : K) * α)) y =
      GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) *
        GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ α) (y + GlobalTheory.HeckeTheta.ulog φ u) := by
  intro K _ _ _ I _ φ hφ n s u α y
  have hsum : (∑ i, (y + GlobalTheory.HeckeTheta.ulog φ u) i) = ∑ i, y i := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, GlobalTheory.HeckeShift.sum_ulog φ hφ u, add_zero]
  have hu0 : ((u : 𝓞 K) : K) ≠ 0 := by
    intro h
    exact (Units.ne_zero u) (by exact_mod_cast h)
  unfold GlobalTheory.HeckeMellin.term
  rw [hsum, ← mul_assoc]
  congr 1
  unfold GlobalTheory.HeckeTheta.gauss GlobalTheory.HeckeStrip.wt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [GlobalTheory.HeckeTheta.dil, GlobalTheory.HeckeTheta.emb, GlobalTheory.HeckeTheta.ulog, Pi.add_apply, map_mul]
  exact GlobalTheory.HeckeShift.factor_shift (n i) (y i) ((map_ne_zero _).2 hu0) (φ i α)
end GlobalTheory.HeckeShift
