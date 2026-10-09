-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedSlicedForecastCommonFloor_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T12:04:57.448496+00:00
-- url     : https://prove2.me/submissions/6444b1c2-8b7e-4323-80b5-9f3e1b23cf10

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedSlicedForecastComparisonLogs
namespace OAI

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedSlicedForecastCommonFloor_bounds
    (periodLog childLog cost comparisonLog : ℝ) :
    let F := preparedSlicedForecastCommonFloorExponent periodLog childLog cost comparisonLog
    let Lmin := preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog
    0 ≤ F ∧ 0 < Lmin ∧ (Lmin : ℝ) ≤ Real.exp (F + 1) ∧
      preparedSlicedForecastChildSize childLog ≤ Lmin ∧
      2 * Real.exp cost ≤ (Lmin : ℝ) ∧
      (∀ T : ℕ, (T : ℝ) ≤ Real.exp periodLog → T ≤ Lmin) ∧
      (∀ Lcompare : ℕ, (Lcompare : ℝ) ≤ Real.exp comparisonLog → Lcompare ≤ Lmin) := by
  intro F Lmin
  have hF : 0 ≤ F := le_max_left _ _
  have hp : periodLog ≤ F := (le_max_left _ _).trans (le_max_right _ _)
  have hc : childLog ≤ F :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hs : cost + 1 ≤ F :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have ha : comparisonLog ≤ F :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hfloor : Real.exp F ≤ (Lmin : ℝ) := Nat.le_ceil _
  have hnat (a : ℝ) (haF : a ≤ F) (k : ℕ) (hk : (k : ℝ) ≤ Real.exp a) :
      k ≤ Lmin := by
    exact_mod_cast hk.trans ((Real.exp_le_exp.mpr haF).trans hfloor)
  refine ⟨hF, one_le_ceil_exp F, ceil_exp_le_exp_add_one hF, ?_, ?_, hnat _ hp, hnat _ ha⟩
  · exact Nat.ceil_mono (Real.exp_le_exp.mpr hc)
  · have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    calc
      2 * Real.exp cost ≤ Real.exp 1 * Real.exp cost :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg cost)
      _ = Real.exp (cost + 1) := by rw [← Real.exp_add, add_comm]
      _ ≤ Real.exp F := Real.exp_le_exp.mpr hs
      _ ≤ Lmin := hfloor

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedSlicedForecastCommonFloor_bounds := @OAI.Erdos3.VectorPolynomial.preparedSlicedForecastCommonFloor_bounds
