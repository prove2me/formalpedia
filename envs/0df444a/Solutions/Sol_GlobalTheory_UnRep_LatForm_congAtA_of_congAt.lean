-- Prove2me | solution 1 for GlobalTheory.UnRep.LatForm.congAtA_of_congAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:45:10.14282+00:00
-- url     : https://prove2.me/submissions/de34187d-4ada-4873-8408-d275039b1af7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryCorrectionCongruentOneAtLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominator
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.LatForm
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix nonZeroDivisors
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.UnRep.LatForm
theorem _root_.solution (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ) (δ : Matrix (Fin n) (Fin n) E)
    (h : CongAt L N D δ) : CongAtA F L N D (fm F δ) := by
  obtain ⟨t, ht, h⟩ := h
  refine ⟨t, ht, fun z hz => ?_⟩
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨w, hw, e⟩ := h x hx
    refine ⟨fun i => a ⊗ₜ[F] w i, AddSubgroup.subset_closure ⟨a, ha, w, hw, rfl⟩, ?_⟩
    rw [fm_mulVec_pure]
    funext i
    have := congrArg (fun y : Fin n → E =>
      (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E a) (y i)) e
    simpa only [Pi.smul_apply, Pi.sub_apply, map_nsmul, map_sub, TensorProduct.mk_apply] using this
  | zero => exact ⟨0, AddSubgroup.zero_mem _, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨w, hw, e⟩ := ihx
    obtain ⟨w', hw', e'⟩ := ihy
    refine ⟨w + w', AddSubgroup.add_mem _ hw hw', ?_⟩
    rw [smul_add, ← e, ← e', Matrix.mulVec_add, ← smul_add]; congr 1; abel
  | neg x _ ih =>
    obtain ⟨w, hw, e⟩ := ih
    refine ⟨-w, AddSubgroup.neg_mem _ hw, ?_⟩
    rw [smul_neg, ← e, Matrix.mulVec_neg, ← smul_neg]; congr 1; abel
end GlobalTheory.UnRep.LatForm
