-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Ellipsoid.finalFace_feasible_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:28:49.277141+00:00
-- url     : https://prove2.me/submissions/33e2aeb6-a111-4ff9-a2d2-bbd6e95a3fb2

import Mathlib
import Definitions.Def_Q238L009
import Definitions.Def_Q238L010
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_selectFace_spec_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoordinateRow
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

lemma coordinateRow_value {n : ℕ} (i : Fin n) (c b : ℚ) (x : Fin n → ℝ) :
    (coordinateRow i c b).realValue x=(c:ℝ)*x i := by
  simp [coordinateRow,Row.realValue,apply_ite]

lemma boxRows_holds {n B : ℕ} (x : Fin n → ℝ) :
    (∀ q∈boxRows n B, q.RealHolds x) ↔ ∀ j, |x j|≤(B:ℝ) := by
  have he (i : Fin n) (c : ℚ) : (coordinateRow i c B).RealHolds x ↔ (c:ℝ)*x i≤(B:ℝ) := by
    change (coordinateRow i c B).realValue x≤((B:ℚ):ℝ) ↔ _
    rw [coordinateRow_value,Rat.cast_natCast]
  simp only [boxRows,List.forall_mem_append,List.forall_mem_ofFn_iff,he]
  constructor
  · rintro ⟨hp,hm⟩ j
    have hpj : x j≤(B:ℝ) := by simpa using hp j
    have hmj : -x j≤(B:ℝ) := by simpa using hm j
    exact abs_le.mpr ⟨by linarith,hpj⟩
  · intro h
    constructor
    · intro j
      simpa using (abs_le.mp (h j)).2
    · intro j
      have hh := (abs_le.mp (h j)).1
      simpa using (show -x j≤(B:ℝ) by linarith)

lemma finalFace_feasible_s238r_oai {n : ℕ} (rows : List (Row n)) (B : ℕ)
    (hfeas : ∃ x : Fin n → ℝ, (∀ q∈rows,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
    ∃ x, Face (withBox rows B) (finalFace rows B) B x := by
  apply (selectFace_spec_s238r (withBox rows B) B (withBox rows B) [] ?_).2.1
  obtain ⟨x,hx,hb⟩ := hfeas
  refine ⟨x,⟨?_,by simp,hb⟩⟩
  exact List.forall_mem_append.mpr ⟨hx,(boxRows_holds x).mpr hb⟩

end MetricKMedianRecovery.Ellipsoid

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.Ellipsoid.finalFace_feasible_s238r_oai := @OAI.MetricKMedianRecovery.Ellipsoid.finalFace_feasible_s238r_oai
