-- Prove2me | solution 1 for GlobalTheory.BK.exists_eq_algebraMap_add_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:27.097784+00:00
-- url     : https://prove2.me/submissions/909d1de5-2645-4619-829f-95febf11f0b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InstTameDescentExponentDataPadicThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapMemNonZeroDivisorsAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (l e) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
namespace GlobalTheory.BK
theorem _root_.solution {B : Type} [CommRing B] (s : B) (n : ℕ)
    (x : AdicCompletion (Ideal.span {s}) B) :
    ∃ (g : B) (x' : AdicCompletion (Ideal.span {s}) B),
      x = algebraMap B _ g + algebraMap B _ s ^ n * x' := by
  obtain ⟨g, hg⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (Ideal.span {s}) B n x)
  have h : x - AdicCompletion.of (Ideal.span {s}) B g ∈
      Ideal.span {s} ^ n • (⊤ : Submodule B (AdicCompletion (Ideal.span {s}) B)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker,
      map_sub, ← hg, sub_eq_zero]
    rfl
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨x', -, hx'⟩ := h
  refine ⟨g, x', ?_⟩
  rw [Algebra.smul_def, map_pow, eq_sub_iff_add_eq'] at hx'
  exact hx'.symm
end GlobalTheory.BK
