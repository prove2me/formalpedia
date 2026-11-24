-- Prove2me | solution 1 for GlobalTheory.HoloWirt.iterD_holo_and_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:14:59.669059+00:00
-- url     : https://prove2.me/submissions/f869481f-238f-45f0-9c97-76e53bfa6f62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedComplexPartialDerivativeEqWirtingerWord
import Theorems.Thm_GlobalTheory_HoloWirt_wirt_false_eq_lineDeriv
import Theorems.Thm_GlobalTheory_SCV_analyticOnNhd_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.HoloWirt
namespace GlobalTheory.HoloWirt
theorem _root_.solution {I : Type} [Fintype I] [DecidableEq I] (U : Set (I → ℂ)) (g : (I → ℂ) → ℂ)
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) (l : List I) :
    DifferentiableOn ℂ (iterD l g) U ∧ Set.EqOn (iterD l g) (wirtWord (l.map fun i => (i, false)) g) U := by
  induction l with
  | nil => exact ⟨hg, fun _ _ => rfl⟩
  | cons i l ih =>
    obtain ⟨hd, heq⟩ := ih
    have hat : ∀ z ∈ U, DifferentiableAt ℂ (iterD l g) z := fun z hz => hd.differentiableAt (hU.mem_nhds hz)
    have hpart : Set.EqOn (iterD (i :: l) g) (fun z => fderiv ℂ (iterD l g) z (Pi.single i 1)) U := by
      intro z hz
      show lineDeriv ℂ (iterD l g) z (Pi.single i 1) = _
      exact (hat z hz).lineDeriv_eq_fderiv
    refine ⟨?_, ?_⟩
    · have hf : DifferentiableOn ℂ (fun z => fderiv ℂ (iterD l g) z (Pi.single i 1)) U :=
        ((GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hU hd).fderiv.differentiableOn).clm_apply
          (differentiableOn_const _)
      exact hf.congr hpart
    · intro z hz
      have hev : wirtWord (l.map fun i => (i, false)) g =ᶠ[nhds z] iterD l g :=
        Filter.eventually_of_mem (hU.mem_nhds hz) (fun y hy => (heq hy).symm)
      show partialD i (iterD l g) z = wirt i false (wirtWord (l.map fun i => (i, false)) g) z
      have hw : wirt i false (wirtWord (l.map fun i => (i, false)) g) z = wirt i false (iterD l g) z := by
        unfold wirt
        rw [hev.fderiv_eq]
      rw [hw, wirt_false_eq_lineDeriv i _ z (hat z hz)]
      rfl
end GlobalTheory.HoloWirt
