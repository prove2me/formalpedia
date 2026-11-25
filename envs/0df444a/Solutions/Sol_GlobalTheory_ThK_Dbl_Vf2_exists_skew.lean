-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Vf2.exists_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:25:30.281203+00:00
-- url     : https://prove2.me/submissions/c368f957-b3b4-4bbb-9321-764150af663e

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_SkewTwo
import Theorems.Thm_GlobalTheory_ThK_Dbl_Vf2_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Vf2
open Matrix GlobalTheory.WeilM PositivityTheory.ThKG.Loc.Cone.Vf
variable {A K β : Type} [CommRing A] [Field K] [Fintype β] [DecidableEq β]
variable {c : A →+* A} {r : A →+* K} {G G' M m P Q : Matrix β β A}
namespace GlobalTheory.ThK.Dbl.Vf2
theorem _root_.solution (hc : ∀ z, c (c z) = z) (hr : Function.Surjective r) (hG : ∀ i j, c (G j i) = G i j) (hG' : G * G' = 1)
    (hcase : ((∀ z, r z = 0 → r (c z) = 0) ∧ ∃ κ, r (κ - c κ) ≠ 0) ∨ ∃ η, r η = 1 ∧ r (c η) = 0)
    (hu : ∀ z, r z ≠ 0 → r (c z) ≠ 0 → IsUnit z)
    (lag : Mᵀ * G * m.map c + mᵀ * G * M.map c = 0) (inj : P * M + Q * m = 1) :
    ∃ S : Matrix β β A, Sᵀ * G + G * S.map c = 0 ∧ IsUnit (M + S * m).det := by
  have l2 : ∀ S : Matrix β β A, Sᵀ * G + G * S.map c = 0 →
      (M + S * m)ᵀ * G * m.map c + mᵀ * G * (M + S * m).map c = 0 := fun S hS => by
    rw [transpose_add, transpose_mul, Matrix.map_add _ (map_add c), Matrix.map_mul]
    linear_combination (norm := noncomm_ring) lag + mᵀ * hS * m.map c
  have i2 : ∀ S : Matrix β β A, P * (M + S * m) + (Q - P * S) * m = 1 := fun S => by
    linear_combination (norm := noncomm_ring) inj
  have ind : ∀ k : ℕ, ∃ S : Matrix β β A, Sᵀ * G + G * S.map c = 0 ∧
      (((M + S * m).map r).det ≠ 0 ∨ k ≤ ((M + S * m).map r).rank) := fun k => by
    induction k with
    | zero => exact ⟨0, by simp, .inr (Nat.zero_le _)⟩
    | succ k ih =>
      obtain ⟨S, h1, h2⟩ := ih
      by_cases h0 : ((M + S * m).map r).det = 0
      · obtain ⟨S', h3, h4⟩ := step hc hr hG hG' hcase (l2 S h1) (i2 S) h0
        refine ⟨S + S', ?_, .inr ?_⟩
        · rw [transpose_add, Matrix.map_add _ (map_add c)]
          linear_combination (norm := noncomm_ring) h1 + h3
        · rw [Matrix.add_mul, ← add_assoc]
          exact (h2.resolve_left (not_not.2 h0)).trans_lt h4
      · exact ⟨S, h1, .inl h0⟩
  obtain ⟨S, h1, h2⟩ := ind (Fintype.card β + 1)
  have h3 := h2.resolve_right (not_le.2 (Nat.lt_succ_of_le (rank_le_card_width _)))
  refine ⟨S, h1, hu _ (by rwa [r.map_det]) fun h4 => ?_⟩
  rw [c.map_det, r.map_det] at h4
  obtain ⟨y, hy0, hy⟩ := exists_mulVec_eq_zero_iff.2 h4
  have l := congrArg (fun N : Matrix β β A => N.map r *ᵥ y) (l2 S h1)
  have j := congrArg (fun N : Matrix β β A => (N.map c).map r *ᵥ y) (i2 S)
  generalize M + S * m = t at *
  change (t.map c).map r *ᵥ y = 0 at hy
  simp only [Matrix.map_add _ (map_add r), Matrix.map_add _ (map_add c), Matrix.map_mul, add_mulVec, ← mulVec_mulVec, hy,
    mulVec_zero, add_zero, zero_add, Matrix.map_zero _ (map_zero r), zero_mulVec, Matrix.map_one _ (map_zero r) (map_one r),
    Matrix.map_one _ (map_zero c) (map_one c), one_mulVec] at l j
  have g0 : (G.map r).det ≠ 0 := fun h => by
    have := congrArg (fun N : Matrix β β A => (N.map r).det) hG'
    simp only [Matrix.map_mul, det_mul, h, zero_mul, Matrix.map_one _ (map_zero r) (map_one r), det_one] at this
    exact zero_ne_one this
  rw [eq_zero_of_mulVec_eq_zero g0 (eq_zero_of_mulVec_eq_zero (by rwa [transpose_map, det_transpose]) l), mulVec_zero] at j
  exact hy0 j.symm
end GlobalTheory.ThK.Dbl.Vf2
