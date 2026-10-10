-- Prove2me | solution 1 for OAI.Erdos3.preparedRelativeInitializer_scalarInputs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T12:15:02.712588+00:00
-- url     : https://prove2.me/submissions/a4f08268-4224-4bf6-9ce2-eb8dec7622e3

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130
import Theorems.Thm_OAI_Erdos3_RelativePatchSliceConclusion_mono
import Theorems.Thm_OAI_Erdos3_preparationCoordinateCap_mono
import Theorems.Thm_OAI_Erdos3_preparedRelativeInitializer_padded_coordinate_card_le

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem RelativePatchAbsoluteRule.mono {s n₀ d₀ : ℕ} {p p' a Λ : ℝ}
    (h : RelativePatchAbsoluteRule s n₀ p a Λ d₀) (hpp : p ≤ p') :
    RelativePatchAbsoluteRule s n₀ p' a Λ d₀ := by
  intro N hprime hinj hratio hsize f hf hfree hmean
  exact (h N hprime hinj hratio
    (fun i => (Real.exp_le_exp.mpr hpp).trans (hsize i)) f hf hfree hmean).mono le_rfl hpp

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem relativePatchComplexity_kernel_bound {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) {U : ℝ} (hA : relativePatchComplexity A ≤ U) :
    (A.kernel.lip : ℝ) + 1 ≤ Real.exp U := by
  have hlog : Real.log (1 + (A.kernel.lip : ℝ)) ≤ U := by
    unfold relativePatchComplexity at hA
    have := Nat.cast_nonneg (α := ℝ) d
    linarith
  have hpos : 0 < 1 + (A.kernel.lip : ℝ) := by positivity
  have h := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hpos] at h
  linarith

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

namespace ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q : ℕ}

end ResidueBoxSlice

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.ResidueBoxSlice

variable {I : Type*} {N : I → ℕ} {q r : ℕ}

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {X : Type*} {N : X → ℕ} {q : ℕ}

end ResidueBoxSlice

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationProjectedAxisBudget
namespace OAI

section

namespace Erdos3

open VectorPolynomial

namespace RankPreparationFamily

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators

variable {I J : Type} [Fintype J] [DecidableEq J] {j : ℕ}

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3

open scoped BigOperators
open VectorPolynomial

namespace RankPreparationLayer

end RankPreparationLayer

namespace RankPreparationFamily

variable {I J : Type} {m q : ℕ}

theorem pad_coordinate_card_le (L : RankPreparationFamily I J m) {M : ℕ}
    (hL : ∀ j, Fintype.card (L j).Coord ≤ M) :
    ∀ j, Fintype.card (L.pad q j).Coord ≤ M := by
  intro j
  by_cases hj : j.val < m
  · simpa only [pad_apply_lt L j hj] using hL ⟨j.val, hj⟩
  · rw [pad_apply_ge L j (by omega)]
    change Fintype.card PEmpty ≤ M
    simp

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3

open Module Submodule VectorPolynomial
open scoped BigOperators

namespace RankPreparationLayer

variable {I J : Type} (L : RankPreparationLayer I J)

end RankPreparationLayer

namespace RankPreparationFamily

variable {I J : Type} {s : ℕ} (L : RankPreparationFamily I J s)

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3.RankPreparationLayer

open Module Submodule

variable {X J E : Type} [Fintype E] (L : RankPreparationLayer X J)
variable [IsZLattice ℝ
  (latticeSection (standardEuclideanLattice L.Coord) (euclideanSubspace L.space))]

end Erdos3.RankPreparationLayer

end

section

namespace Erdos3.RankPreparationLayer

open Module Submodule VectorPolynomial BohrLattice.MinkowskiSecondBox

variable {X J : Type} (L : RankPreparationLayer X J)

end Erdos3.RankPreparationLayer

end

section

namespace Erdos3

open Module Submodule

namespace RankPreparationLayer

end RankPreparationLayer

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeInitializerScalarInputs
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {m s D nX : ℕ}

theorem preparedRelativeInitializerVariableCount_le
    (prep : RankPreparationFamily (Fin nX) (Fin D) m) (hms : m ≤ s)
    {M : ℕ} (hcoord : ∀ j, Fintype.card (prep j).Coord ≤ M) :
    preparedRelativeInitializerVariableCount prep s M ≤
      enlargedPreparedCommonSamplerDimension s M
        (modularInitialBlockCount s (nX + s * M)) := by
  have hdim := (enlargedPreparedCommonSampler_dimensions
    (prep.pad (max m s))
    (modularInitialBlockCount (max m s) (nX + max m s * M))
    (prep.pad_coordinate_card_le hcoord)).1
  calc
    preparedRelativeInitializerVariableCount prep s M ≤
        enlargedPreparedCommonSamplerDimension (max m s) M
          (modularInitialBlockCount (max m s) (nX + max m s * M)) := hdim
    _ = _ := by rw [max_eq_right hms]

theorem preparedRelativeInitializerVariableCount_le_dimension
    (prep : RankPreparationFamily (Fin nX) (Fin D) m) (hms : m ≤ s)
    (hcoord : ∀ j, Fintype.card (prep j).Coord ≤
      preparationCoordinateCap m D (m * D)) :
    let M := preparationCoordinateCap s D (s * D)
    preparedRelativeInitializerVariableCount prep s M ≤
      enlargedPreparedCommonSamplerDimension s M
        (modularInitialBlockCount s (nX + s * M)) := by
  apply preparedRelativeInitializerVariableCount_le prep hms
  intro j
  exact (hcoord j).trans
    (preparationCoordinateCap_mono hms (Nat.mul_le_mul_right D hms))

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial

theorem preparedRelativeInitializer_scalarInputs_of_bounds
    {X : Type*} {s D E q M variableCount n₀ d₀ : ℕ}
    (oldPatch : PolynomialPatch X s (D + E)) (coordinates : Fin q → ℕ)
    {p pRelative precisionBudget chartLog a Λ : ℝ}
    (hp : 2 ≤ p) (hpp : p ≤ pRelative)
    (hq : (q : ℝ) ≤ pRelative) (hM : (M : ℝ) ≤ pRelative)
    (hcoordinates : ∀ j, coordinates j ≤ M)
    (hvariableCount : (variableCount : ℝ) ≤ pRelative)
    (hchart : chartLog + 1 ≤ pRelative)
    (hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (hcomplexity : relativePatchComplexity oldPatch ≤ p)
    (ha : Real.exp (-p) ≤ a)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀) :
    PreparedRelativeInitializerScalarInputs oldPatch coordinates variableCount
      p pRelative precisionBudget chartLog a Λ n₀ d₀ := by
  have hRexp : pRelative ≤ Real.exp pRelative :=
    (by linarith : pRelative ≤ pRelative + 1).trans (Real.add_one_le_exp pRelative)
  have hD : (D : ℝ) ≤ p := by
    have hrank := (relativePatchComplexity_rank_le oldPatch).trans hcomplexity
    simp only [Nat.cast_add] at hrank
    linarith only [hrank, Nat.cast_nonneg (α := ℝ) E]
  have hkernel := relativePatchComplexity_kernel_bound oldPatch hcomplexity
  have hgain : Real.exp (-pRelative) ≤ Real.exp (-p) :=
    Real.exp_le_exp.mpr (neg_le_neg hpp)
  refine ⟨hp.trans hpp, (hD.trans hpp).trans hRexp, hq.trans hRexp,
    ?_, ?_, ?_, hgain, Real.exp_le_exp.mpr (neg_le_neg hprecision), le_rfl,
    hgain.trans ha, habsolute.mono hpp, ?_, ?_, ?_, (Real.exp_pos _).le⟩
  · exact (by linarith only [hkernel] : (oldPatch.kernel.lip : ℝ) ≤ Real.exp p).trans
      (Real.exp_le_exp.mpr hpp)
  · intro j
    exact ((Nat.cast_le.mpr (hcoordinates j)).trans hM).trans hRexp
  · intro _
    exact Real.exp_le_exp.mpr (by linarith only [hchart])
  · linarith only [hvariableCount]
  · exact hcomplexity.trans (by linarith only [hpp])
  · exact Real.exp_le_one_iff.mpr (by linarith only [hp])

theorem preparedRelativeInitializer_scalarInputs
    {nX s D E m n₀ d₀ : ℕ}
    (oldPatch : PolynomialPatch (Fin nX) s (D + E))
    (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    {p pRelative precisionBudget a Λ : ℝ}
    (hp : 2 ≤ p) (hms : m ≤ s)
    (hcoord : ∀ j, Fintype.card (prep j).Coord ≤
      preparationCoordinateCap m D (m * D))
    (hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (hcomplexity : relativePatchComplexity oldPatch ≤ p)
    (ha : Real.exp (-p) ≤ a)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀) :
    let M := preparationCoordinateCap s D (s * D)
    PreparedRelativeInitializerScalarInputs oldPatch
      (fun j => Fintype.card (prep.pad (max m s) j).Coord)
      (preparedRelativeInitializerVariableCount prep s M)
      p pRelative precisionBudget (allocatedUniformChartLog (M : ℝ)) a Λ n₀ d₀ := by
  obtain ⟨hpp, hs, hM, _hJalloc, hdim, hchart⟩ := hstructure
  refine preparedRelativeInitializer_scalarInputs_of_bounds oldPatch _ hp hpp
    ?_ hM (preparedRelativeInitializer_padded_coordinate_card_le prep hms hcoord)
    ?_ hchart hprecision hcomplexity ha habsolute
  · rw [max_eq_right hms]
    linarith only [hs]
  · exact (Nat.cast_le.mpr
      (preparedRelativeInitializerVariableCount_le_dimension prep hms hcoord)).trans hdim

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.preparedRelativeInitializer_scalarInputs := @OAI.Erdos3.preparedRelativeInitializer_scalarInputs
