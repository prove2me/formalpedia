-- Prove2me | solution 2 for OAI.Cotype.projectionLinearCoefficient_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:07:59.603177+00:00
-- url     : https://prove2.me/submissions/3ca38c08-1875-401d-b021-5f3e27525b28

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ProjectionEigenvectors.lean:L32-L74
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.projectionLinearCoefficient_eigenvector. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank
import Definitions.Def_OAI_Analysis_Cotype_BiasedFourier
import Definitions.Def_OAI_Analysis_Cotype_Damping
import Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing
import Definitions.Def_OAI_Analysis_Cotype_WalshSymmetry
import Definitions.Def_OAI_Analysis_Cotype_CubeCoordinateProjections

-- ---- from OAI.Analysis.Cotype.ProjectionEigenvectors ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem projectionProduct_eigenvector {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (c : Fin n → ℝ) (x : X) (h : ∀ i, P i x = c i • x) :
    projectionProduct P x = (∏ i, c i) • x := by
  induction n with
  | zero => simp [projectionProduct]
  | succ n ih =>
    change P 0 (projectionProduct (fun i => P i.succ) x) = _
    rw [ih _ _ (fun i => h i.succ), map_smul, h 0, smul_smul, Fin.prod_univ_succ, mul_comm]

theorem projectionSubset_eigenvector {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (c : Fin n → ℝ) (x : X) (h : ∀ i, P i x = c i • x) (ε : Cube n) :
    projectionSubset P ε x = (∏ i, if ε i then c i else 1) • x := by
  apply projectionProduct_eigenvector
  intro i
  cases ε i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · simp
  · exact h i

theorem projectionLinearCoefficient_eigenvector {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (p : Cube n) (x : X) (h : ∀ i, P i x = (if p i then (0 : ℝ) else 1) • x) :
    projectionLinearCoefficient P x = ∑ i : Fin n, if p = unitIndex i then x else 0 := by
  classical
  have he i : (1-P i) (projectionSubset P (fun j => decide (j ≠ i)) x) =
      if p = unitIndex i then x else 0 := by
    rw [projectionSubset_eigenvector P _ x h]
    simp only [map_smul, sub_apply, one_apply_eq_self, h]
    by_cases hi : p i = true
    · simp only [hi, ite_true, zero_smul, sub_zero]
      by_cases hall : ∀ j, j ≠ i → p j = false
      · have hp : p = unitIndex i := by
          funext j
          by_cases hj : j=i
          · subst j; simp [unitIndex, hi]
          · simp [hall j hj, unitIndex, Ne.symm hj]
        rw [ite_eq_left hp]
        have hprod : (∏ j, if decide (j ≠ i) then (if p j then (0 : ℝ) else 1) else 1) = 1 := by
          apply Finset.prod_eq_one
          intro j _
          by_cases hj : j=i
          · simp [hj]
          · simp [hj, hall j hj]
        rw [hprod, one_smul]
      · push Not at hall
        obtain ⟨j,hji,hpj⟩ := hall
        have hpj' : p j = true := by cases hq : p j <;> simp_all
        have hprod : (∏ j, if decide (j ≠ i) then (if p j then (0 : ℝ) else 1) else 1) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ j)
          simp [hji,hpj']
        have hne : p ≠ unitIndex i := by
          intro hh
          have := congrFun hh j
          simp [unitIndex, Ne.symm hji, hpj'] at this
        rw [hprod, zero_smul, ite_eq_right hne]
    · have hip : p i = false := by cases hq : p i <;> simp_all
      have hne : p ≠ unitIndex i := by
        intro hh
        have := congrFun hh i
        simp [unitIndex,hip] at this
      simp [hip,hne]
  simp only [projectionLinearCoefficient, sum_apply]
  exact Finset.sum_congr rfl (fun i _ => he i)

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.projectionLinearCoefficient_eigenvector := @_root_.OAI.Cotype.projectionLinearCoefficient_eigenvector
