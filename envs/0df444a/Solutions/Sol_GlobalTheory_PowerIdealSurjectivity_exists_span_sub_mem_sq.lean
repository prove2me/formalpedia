-- Prove2me | solution 1 for GlobalTheory.PowerIdealSurjectivity.exists_span_sub_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:29:26.12454+00:00
-- url     : https://prove2.me/submissions/fee5723b-325a-4360-9bf3-89df566575b7

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanSubMemSq
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply



set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerIdealSurjectivity
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
namespace GlobalTheory.PowerIdealSurjectivity
theorem _root_.solution (ε : A →ₐ[O] O) {d : ℕ} (x : Fin d → A) (hx : ∀ i, ε (x i) = 0)
    (hs : Submodule.span O (Set.range fun i ↦ GlobalTheory.AugCot.d ε (x i)) = ⊤) {c : A}
    (hc : c ∈ RingHom.ker ε) :
    ∃ m ∈ Submodule.span O (Set.range x), m ∈ RingHom.ker ε ∧ c - m ∈ RingHom.ker ε ^ 2 := by
  classical

  let J : Submodule O A := (RingHom.ker ε ^ 2).restrictScalars O
  let D : A →ₗ[O] A ⧸ J := J.mkQ ∘ₗ (LinearMap.id - (Algebra.linearMap O A) ∘ₗ ε.toLinearMap)
  have hDa : ∀ a, D a = Submodule.Quotient.mk (a - algebraMap O A (ε a)) := fun a => rfl
  have hmemI : ∀ a, a - algebraMap O A (ε a) ∈ RingHom.ker ε := fun a =>
    RingHom.mem_ker.mpr (show ε (a - algebraMap O A (ε a)) = 0 by simp)
  have hD : ∀ a b : A, D (a * b) = ε a • D b + ε b • D a := by
    intro a b
    rw [hDa, hDa, hDa, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, Submodule.restrictScalars_mem]
    have key : a * b - algebraMap O A (ε (a * b)) -
        (ε a • (b - algebraMap O A (ε b)) + ε b • (a - algebraMap O A (ε a))) =
        (a - algebraMap O A (ε a)) * (b - algebraMap O A (ε b)) := by
      rw [map_mul, Algebra.smul_def, Algebra.smul_def, map_mul]
      ring
    rw [key, pow_two]
    exact Ideal.mul_mem_mul (hmemI a) (hmemI b)
  have hdc : GlobalTheory.AugCot.d ε c ∈ Submodule.span O (Set.range fun i => GlobalTheory.AugCot.d ε (x i)) := by
    rw [hs]
    exact Submodule.mem_top
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp hdc
  have hε0 : ε (∑ i, r i • x i) = 0 := by simp [map_sum, hx]
  refine ⟨∑ i, r i • x i,
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩),
    RingHom.mem_ker.mpr hε0, ?_⟩
  have hdm : GlobalTheory.AugCot.d ε (∑ i, r i • x i) = GlobalTheory.AugCot.d ε c := by
    rw [← hr, map_sum]
    simp only [map_smul]
  have h := congrArg (GlobalTheory.AugCot.lift ε D hD) hdm
  rw [GlobalTheory.AugCot.lift_d, GlobalTheory.AugCot.lift_d, hDa, hDa, Submodule.Quotient.eq,
    Submodule.restrictScalars_mem] at h
  have hεc : ε c = 0 := RingHom.mem_ker.mp hc
  rw [hε0, hεc, map_zero, sub_zero, sub_zero] at h
  rw [← neg_sub]
  exact (RingHom.ker ε ^ 2).neg_mem h
end GlobalTheory.PowerIdealSurjectivity
