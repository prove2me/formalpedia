-- Prove2me | solution 1 for OAI.EuclideanRamsey.CircleConsequence.circle_five_rows_independent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:43:25.29181+00:00
-- url     : https://prove2.me/submissions/a28591d9-c846-4f08-8eb9-d2cfefb06474

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/CircleRows.lean:L52-L78
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.CircleConsequence.circle_five_rows_independent. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleRows
import Theorems.Thm_OAI_EuclideanRamsey_CircleConsequence_normalized_isolators

-- ---- from OAI.Combinatorics.EuclideanRamsey.CircleRows ----
namespace OAI
noncomputable section
namespace EuclideanRamsey.CircleConsequence

/-- The quadratic evaluation rows are independent because their dual rows isolate them. -/
theorem circle_five_rows_independent (a : Fin 5 → Space 2)
    (ha : Function.Injective a) (c : Space 2) (r : ℝ)
    (hc : ∀ i, dist (a i) c = r) :
    LinearIndependent (Coeff a) (fun i : Fin 5 => fun q : QIndex =>
      augmented a i q.1 * augmented a i q.2) := by
  classical
  obtain ⟨L, hL⟩ := normalized_isolators a ha c r hc
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hzero (q : QIndex) : ∑ j, g j * quadraticRow a j q = 0 := by
    simpa [quadraticRow] using congrFun hg q
  have hpair : ∑ q, L i q * (∑ j, g j * quadraticRow a j q) = 0 := by
    simp [hzero]
  have hcalc : (∑ q, L i q * (∑ j, g j * quadraticRow a j q)) = g i := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ j, g j * (∑ q, L i q * quadraticRow a j q) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ = g i := by simp [hL]
  exact hcalc.symm.trans hpair
end EuclideanRamsey.CircleConsequence

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.CircleConsequence


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.CircleConsequence.circle_five_rows_independent := @_root_.OAI.EuclideanRamsey.CircleConsequence.circle_five_rows_independent
