-- Prove2me | solution 2 for OAI.Cotype.projectionSubset_union
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:43:30.699669+00:00
-- url     : https://prove2.me/submissions/84c71dcc-0380-4941-b488-3d462f2f9976

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ProjectionProducts.lean:L50-L72
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.projectionSubset_union. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts

-- ---- from OAI.Analysis.Cotype.ProjectionProducts ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem projectionSubset_commute {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (ε : Cube n) (Q : X →L[ℝ] X) (h : ∀ i, Commute (P i) Q) :
    Commute (projectionSubset P ε) Q := by
  apply projectionProduct_commute
  intro i
  cases ε i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact Commute.one_left Q
  · exact h i

theorem projectionSubset_union {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (ε η : Cube n) :
    projectionSubset P ε * projectionSubset P η =
      projectionSubset P (fun i => ε i || η i) := by
  induction n with
  | zero => simp [projectionSubset, projectionProduct]
  | succ n ih =>
    have ht := ih (fun i => P i.succ) (fun i => hp i.succ)
      (fun i j => hc i.succ j.succ) (fun i => ε i.succ) (fun i => η i.succ)
    have hm := projectionSubset_commute (fun i => P i.succ) (fun i => ε i.succ)
      (P 0) (fun i => hc i.succ 0)
    change ((if ε 0 then P 0 else 1) * projectionSubset (fun i => P i.succ) (fun i => ε i.succ)) *
      ((if η 0 then P 0 else 1) * projectionSubset (fun i => P i.succ) (fun i => η i.succ)) =
      (if ε 0 || η 0 then P 0 else 1) *
        projectionSubset (fun i => P i.succ) (fun i => ε i.succ || η i.succ)
    cases he : ε 0 <;> cases hh : η 0 <;> simp only [Bool.false_or, Bool.true_or,
      Bool.false_eq_true, ite_false, ite_true, one_mul]
    · exact ht
    · rw [← mul_assoc, hm.eq, mul_assoc, ht]
    · rw [mul_assoc, ht]
    · rw [mul_assoc, ← mul_assoc (projectionSubset _ _) (P 0), hm.eq,
        mul_assoc, ← mul_assoc (P 0) (P 0), hp, ht]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.projectionSubset_union := @_root_.OAI.Cotype.projectionSubset_union
