-- Prove2me | solution 1 for GlobalTheory.SmoothForms.SecondKind.prod_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:12:22.809365+00:00
-- url     : https://prove2.me/submissions/ddee0aba-b65f-4427-bb15-aa6473d8ad6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_SmoothInExponentialCoordsIffFirstSecondKind
import Theorems.Thm_GlobalTheory_SmoothForms_SecondKind_exp_unitary
import Theorems.Thm_GlobalTheory_SmoothForms_SecondKind_map_one_eq
import Theorems.Thm_GlobalTheory_SmoothForms_SecondKind_contDiff_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.SecondKind
open NormedSpace
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
namespace GlobalTheory.SmoothForms.SecondKind
theorem _root_.solution (H : IsLieData σ j s) (J : L →L[ℝ] 𝔸) (hJ : ∀ X, J X = j X) (l : List (P →L[ℝ] L)) :
    ∃ c : P → 𝔸, ContDiff ℝ ∞ c ∧ (∀ p, σ (c p) * c p = 1) ∧
      (∀ p, s (c p) = (l.map fun A => expMap j s (A p)).prod) ∧ c 0 = 1 ∧ HasFDerivAt c (J ∘L l.sum) 0 := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  induction l with
  | nil =>
    refine ⟨fun _ => 1, contDiff_const, fun _ => by simp [H.one], fun _ => by simp [map_one_eq H], rfl, ?_⟩
    simpa using hasFDerivAt_const (1 : 𝔸) (0 : P)
  | cons A l ih =>
    obtain ⟨c, h1, h2, h3, h4, h5⟩ := ih
    have hA : ContDiff ℝ ∞ fun p => exp (J (A p)) := contDiff_exp.comp (J ∘L A).contDiff
    have hu : ∀ p, σ (exp (J (A p))) * exp (J (A p)) = 1 := fun p => by rw [hJ]; exact exp_unitary H _
    refine ⟨fun p => exp (J (A p)) * c p, hA.mul h1, fun p => ?_, fun p => ?_, by simp [h4], ?_⟩
    · rw [H.anti, mul_assoc, ← mul_assoc (σ (exp _)), hu, one_mul, h2]
    · rw [H.mul _ _ (hu p) (h2 p), h3, hJ, List.map_cons, List.prod_cons, expMap]
    · have hd : HasFDerivAt (fun p => exp (J (A p))) (J ∘L A) 0 := by
        have := HasFDerivAt.comp (g := (exp : 𝔸 → 𝔸)) (g' := 1) (0 : P)
          (by simpa using hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)) (J ∘L A).hasFDerivAt
        exact this
      refine (hd.mul' h5).congr_fderiv ?_
      ext p
      simp [h4, add_comm]
end GlobalTheory.SmoothForms.SecondKind
