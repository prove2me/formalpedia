-- Prove2me | solution 1 for GlobalTheory.IdealChain.opE_rescale_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:24:45.820315+00:00
-- url     : https://prove2.me/submissions/4d51250f-7625-490c-b796-36ba8d520384

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMeasurePiChangeConstantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulFrameMulFrameInvApply
import Theorems.Thm_GlobalTheory_IdealChain_smul_frame_mul_frame_inv_apply
import Theorems.Thm_GlobalTheory_T_haar_measure_pi_change_constant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical
open GlobalTheory GlobalTheory.IdealChain
namespace GlobalTheory.IdealChain
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (α β₀ : kˣ) (b' : ℕ → kˣ) (ν νs : Measure k), (∀ i, 1 ≤ i → i ≤ c → b' i / b' (i + 1) = β₀) → ν.IsAddHaarMeasure → νs.IsAddHaarMeasure → ∃ C : ℝ, (0 < C ∧ (IsHalfPow k (ν (𝒪[k] : Set k)).toReal → IsHalfPow k (νs (𝒪[k] : Set k)).toReal → IsHalfPow k C)) ∧ ∀ (ψ : AddChar k Circle) (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix n n' k), opE ψ ν p Ψ x = C * opE (ψ.mulShift (β₀ : k)) νs p (fun y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k => Ψ ((α : k) • ((frame n c fun i => α⁻¹ * b' i).val * y * ((frame n' (c + 1) b')⁻¹).val))) (((α⁻¹ : kˣ) : k) • x) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p α β₀ b' ν νs hb hν hνs
  let d : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → kˣ := fun rs =>
    α * Sum.elim (fun _ : n => 1) (fun i : Fin c => α⁻¹ * b' (i.val + 1)) rs.1.1 *
      (Sum.elim (fun _ : n' => 1) (fun i : Fin (c + 1) => b' (i.val + 1)) rs.1.2)⁻¹
  obtain ⟨C, hC, hF⟩ := @GlobalTheory.T.haar_measure_pi_change_constant k _ _ _ _ _ _ _ (@Subtype.fintype _ _ (Classical.decPred _) _) ν νs d hν hνs
  refine ⟨C, hC, fun ψ Ψ x => ?_⟩
  unfold opE
  rw [hF]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  dsimp only
  congr 1
  · congr 1
    ext r q
    rw [smul_frame_mul_frame_inv_apply]
    by_cases h : Free p (r, q)
    · rcases r with r | r <;> rcases q with q | q
      · exact absurd h (by simp [Free])
      · simp [affPt, basePt, h, d]
      · simp [affPt, basePt, h, d]
      · have : r.val ≠ q.val := by simp only [Free] at h; omega
        simp [affPt, basePt, h, d, this]
    · rcases r with r | r <;> rcases q with q | q
      · simp [affPt, basePt, h]
      · simp [affPt, basePt, h]
      · simp [affPt, basePt, h]
      · by_cases h' : r.val = q.val <;> simp [affPt, basePt, h, h']
  · rw [AddChar.mulShift_apply, mul_neg]
    congr 3
    unfold ch
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : Free (n := n) (n' := n') p (Sum.inr i, Sum.inr i.succ) := by simp [Free]
    rw [← hb (i.val + 1) (by omega) (by omega)]
    simp [affPt, basePt, h, d, div_eq_mul_inv]
end GlobalTheory.IdealChain
