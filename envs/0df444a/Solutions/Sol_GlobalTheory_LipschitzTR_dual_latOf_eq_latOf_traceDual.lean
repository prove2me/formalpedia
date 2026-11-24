-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:53:04.934874+00:00
-- url     : https://prove2.me/submissions/daf866e8-bb3e-4423-80eb-2cfd4e11de73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualLatticeImageEqLatticeImageTraceDual
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_mem_dual_latOf_iff
import Theorems.Thm_GlobalTheory_LipschitzTR_exists_remb_eq_of_mem_dual
import Theorems.Thm_GlobalTheory_LipschitzTR_mem_latOf
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply



set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR
namespace GlobalTheory.LipschitzTR
theorem _root_.solution (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0) :
    Formalism.H.dual (latOf N) = latOf (FractionalIdeal.dual ℤ ℚ N) := by
  classical
  ext μ
  constructor
  · intro hμ
    rw [mem_latOf]
    let I : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 N hN
    have hbN : ∀ i, basisOfFractionalIdeal F I i ∈ N := fun i => by
      have := (mem_span_basisOfFractionalIdeal F (I := I) (x := basisOfFractionalIdeal F I i)).mp
        (Submodule.subset_span ⟨i, rfl⟩)
      simpa [I] using this
    obtain ⟨ν, hν⟩ := exists_remb_eq_of_mem_dual (basisOfFractionalIdeal F I) N hbN μ hμ
    subst hν
    exact ⟨ν, (remb_mem_dual_latOf_iff N hN ν).mp hμ, rfl⟩
  · intro hμ
    obtain ⟨ν, hν, rfl⟩ := (mem_latOf _ μ).mp hμ
    exact (remb_mem_dual_latOf_iff N hN ν).mpr hν
end GlobalTheory.LipschitzTR
