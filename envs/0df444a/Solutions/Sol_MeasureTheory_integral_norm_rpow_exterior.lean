-- Prove2me | solution 1 for MeasureTheory.integral_norm_rpow_exterior
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T17:02:24.636812+00:00
-- url     : https://prove2.me/submissions/d7802faa-e153-4b41-b330-b7817488ae2f

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set Metric
set_option autoImplicit false

theorem solution (n : ℕ) (hn : 1 ≤ n) (β : ℝ) (hβ : β < 0)
    (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ (β - n))
        (closedBall 0 R)ᶜ ∧
      (∫ z : EuclideanSpace ℝ (Fin n) in (closedBall 0 R)ᶜ, ‖z‖ ^ (β - n)) =
        (n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * R ^ β / (-β) := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hp : (n - 1 : ℕ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn, Nat.cast_one]
  have heq : ∀ r : ℝ, 0 < r → r ^ (n - 1) * r ^ (β - n) = r ^ (β - 1) := by
    intro r hr
    rw [← Real.rpow_natCast, ← Real.rpow_add hr, hp]
    congr 1
    ring
  have hi : IntegrableOn (fun r : ℝ => r ^ (β - 1)) (Ioi R) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hR
  have hiw : IntegrableOn (fun r : ℝ => r ^ (n - 1) * r ^ (β - n)) (Ioi R) :=
    hi.congr_fun (fun r hr => (heq r (hR.trans hr)).symm) measurableSet_Ioi
  have hleft : (fun z : EuclideanSpace ℝ (Fin n) =>
      (Ioi R).indicator (fun r : ℝ => r ^ (β - n)) ‖z‖) =
      ((closedBall 0 R)ᶜ).indicator (fun z => ‖z‖ ^ (β - n)) := by
    funext z
    simp [indicator, not_le]
  have hright : (fun r : ℝ => r ^ (n - 1) *
      (Ioi R).indicator (fun r : ℝ => r ^ (β - n)) r) =
      (Ioi R).indicator (fun r : ℝ => r ^ (n - 1) * r ^ (β - n)) := by
    funext r
    by_cases hr : R < r <;> simp [indicator, hr]
  have hset : Ioi (0 : ℝ) ∩ Ioi R = Ioi R := by
    ext r
    simp only [mem_inter_iff, mem_Ioi, and_iff_right_iff_imp]
    exact hR.trans
  have hs : MeasurableSet ((closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ) :=
    isClosed_closedBall.measurableSet.compl
  refine ⟨?_, ?_⟩
  · rw [← integrable_indicator_iff hs, ← hleft]
    apply (integrable_fun_norm_addHaar volume).2
    simpa only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, hright,
      integrableOn_indicator_iff measurableSet_Ioi, Set.inter_comm (Ioi R) (Ioi 0),
      hset] using hiw
  · have hrad := integral_fun_norm_addHaar
      (E := EuclideanSpace ℝ (Fin n)) volume ((Ioi R).indicator (fun r : ℝ => r ^ (β - n)))
    simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul] at hrad
    rw [hleft, integral_indicator hs, hright, setIntegral_indicator measurableSet_Ioi,
      hset, setIntegral_congr_fun measurableSet_Ioi (fun r hr => heq r (hR.trans hr)),
      integral_Ioi_rpow_of_lt (by linarith : β - 1 < -1) hR] at hrad
    simp only [show β - 1 + 1 = β by ring] at hrad
    rw [hrad]
    ring
