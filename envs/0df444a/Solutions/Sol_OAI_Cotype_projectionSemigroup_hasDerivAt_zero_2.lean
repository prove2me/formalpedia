-- Prove2me | solution 2 for OAI.Cotype.projectionSemigroup_hasDerivAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:51:18.074542+00:00
-- url     : https://prove2.me/submissions/7ea50ea2-7647-43c0-b45d-83002bcb2437

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ProjectionCoefficientDerivative.lean:L34-L48
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.projectionSemigroup_hasDerivAt_zero. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum

-- ---- from OAI.Analysis.Cotype.ProjectionCoefficientDerivative ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem projectionLinearCoefficient_succ {m : ℕ} (P : Fin (m+1) → Y →L[ℝ] Y)
    (hc : ∀ i j, Commute (P i) (P j)) :
    projectionLinearCoefficient P =
      (1-P 0)*projectionProduct (fun i => P i.succ) +
      P 0*projectionLinearCoefficient (fun i => P i.succ) := by
  classical
  unfold projectionLinearCoefficient
  rw [Fin.sum_univ_succ]
  have hz : projectionSubset P (fun j => decide (j ≠ 0)) =
      projectionProduct (fun i => P i.succ) := by
    simp [projectionSubset, projectionProduct]
  rw [hz, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hi : projectionSubset P (fun j => decide (j ≠ i.succ)) =
      P 0*projectionSubset (fun j => P j.succ) (fun j => decide (j ≠ i)) := by
    simp [projectionSubset, projectionProduct, Ne.symm (Fin.succ_ne_zero i)]
  have hcomm : Commute (1-P i.succ) (P 0) :=
    (Commute.one_left _).sub_left (hc i.succ 0)
  rw [hi, ← mul_assoc, hcomm.eq, mul_assoc]

theorem projectionSemigroup_hasDerivAt_zero {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hc : ∀ i j, Commute (P i) (P j)) :
    HasDerivAt (projectionSemigroup P) (projectionLinearCoefficient P) 0 := by
  induction m with
  | zero =>
    convert! hasDerivAt_const (0 : ℝ) (1 : Y →L[ℝ] Y) using 1
  | succ m ih =>
    have ht := ih (fun i => P i.succ) (fun i j => hc i.succ j.succ)
    have h0 : HasDerivAt (fun r : ℝ => P 0+r • (1-P 0)) (1-P 0) 0 := by
      convert! HasDerivAt.add (hasDerivAt_const (0 : ℝ) (P 0))
        ((hasDerivAt_id (0 : ℝ)).smul_const (1-P 0)) using 1; simp
    have h := h0.mul ht
    convert! h using 1
    simp only [projectionSemigroup_zero, zero_smul, add_zero,
      ← projectionLinearCoefficient_succ P hc]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.projectionSemigroup_hasDerivAt_zero := @_root_.OAI.Cotype.projectionSemigroup_hasDerivAt_zero
