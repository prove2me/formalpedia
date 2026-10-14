-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedFiniteNestedSource_counts
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-13T03:44:19.737302+00:00
-- url     : https://prove2.me/submissions/48b2b965-e9e8-4a74-be19-304a2e6902f3

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B187

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

theorem enlargedPreparedCommonSamplerDimension_allocation (m M Jalloc : ℕ) :
    Jalloc ≤ enlargedPreparedCommonSamplerDimension m M Jalloc := by
  unfold enlargedPreparedCommonSamplerDimension
  omega

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedBadProductInputBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical

theorem boundedCoefficientExponent_card_le_common_dimension
    {K : Type*} [Fintype K] (m pnum : ℕ) (hK : Fintype.card K ≤ pnum)
    {h : ℕ} (hh : h ≤ m) :
    Fintype.card (BoundedCoefficientExponent K h) ≤ (m + 1) * (pnum + 1) ^ m := by
  apply (boundedCoefficientExponent_card_le h).trans
  apply Nat.mul_le_mul (Nat.add_le_add_right hh 1)
  exact (Nat.pow_le_pow_left (Nat.add_le_add_right hK 1) h).trans
    (Nat.pow_le_pow_right (Nat.succ_pos pnum) hh)

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem preparedBadProduct_input_counts
    (Jalloc nX : ℕ) {M : ℕ} (hM : ∀ j, Fintype.card (L j).Coord ≤ M) :
    let pnum := enlargedPreparedCommonSamplerDimension m M Jalloc
    let G := EnlargedPreparedCommonKernel m Jalloc
    let I := PreparedSamplerContinuous L
    let n := preparedSamplerTransverse L
    let B := EnlargedPreparedCommonSamplerBlock L Jalloc
    let vars := LayerSamplerVariables G I n B
    m ≤ pnum ∧ M ≤ pnum ∧ Jalloc ≤ pnum ∧ Fintype.card G ≤ pnum ∧
      Fintype.card vars ≤ pnum ∧
      (∀ j, Fintype.card (I j) ≤ pnum) ∧ (∀ j, n j ≤ pnum) ∧
      (∀ j, Fintype.card (L j).Coord ≤ pnum) ∧
      (∀ j : Fin m, Fintype.card (BoundedCoefficientExponent vars (j.val + 1)) ≤
        (m + 1) * (pnum + 1) ^ m) ∧
      Fintype.card (Option vars × Fin nX) ≤ (pnum + 1) * nX := by
  intro pnum G I n B vars
  obtain ⟨hvars, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions L Jalloc hM
  have hpM := enlargedPreparedCommonSamplerDimension_ge m M Jalloc
  have halloc := enlargedPreparedCommonSamplerDimension_allocation m M Jalloc
  have hm : m ≤ pnum := by unfold pnum enlargedPreparedCommonSamplerDimension; omega
  have hG : Fintype.card G ≤ pnum := by
    simp only [G, EnlargedPreparedCommonKernel, Fintype.card_fin]
    unfold pnum enlargedPreparedCommonSamplerDimension
    omega
  refine ⟨hm, hpM, halloc, hG, hvars, hI, hn, fun j => (hM j).trans hpM, ?_, ?_⟩
  · intro j
    exact boundedCoefficientExponent_card_le_common_dimension m pnum hvars (Nat.succ_le_of_lt j.isLt)
  · simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    exact Nat.mul_le_mul_right nX (Nat.add_le_add_right hvars 1)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedSourceRelativeInitializerBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uα
open scoped Classical BigOperators NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

theorem preparedBadProduct_dimension_le_initial_allocation (m d : ℕ) :
    d ≤ modularInitialBlockCount m d := by
  have hp : 0 < (2 : ℕ) ^ m := by positivity
  unfold modularInitialBlockCount
  nlinarith [Nat.zero_le (modularInitialRankStrength m d)]

section Source
variable {X₀ J₀ : Type} {m : ℕ} (prep : RankPreparationFamily X₀ J₀ m) (nX M : ℕ)
local notation "Jalloc" => modularInitialBlockCount m (nX + m * M)

end Source
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical

theorem preparedFiniteCanonicalSource_counts
    {m : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
    (nX M : ℕ) {Bstruct : ℝ}
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hnum : (enlargedPreparedCommonSamplerDimension m M
      (modularInitialBlockCount m (nX + m * M)) : ℝ) ≤ Bstruct) :
    (Fintype.card (EnlargedPreparedCommonKernel m
      (modularInitialBlockCount m (nX + m * M))) : ℝ) ≤ Bstruct ∧
    (Fintype.card (Fin nX ⊕ (Σ j, (prep j).Coord)) : ℝ) ≤ Bstruct ∧
    (Fintype.card (LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ)
        ≤ Bstruct ∧ (m : ℝ) ≤ Bstruct := by
  let Jalloc := modularInitialBlockCount m (nX + m * M)
  have hcounts := preparedBadProduct_input_counts prep Jalloc nX hCoord
  have htags : Fintype.card (Fin nX ⊕ (Σ j, (prep j).Coord)) ≤ nX + m * M := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
    apply Nat.add_le_add_left
    calc
      ∑ j : Fin m, Fintype.card (prep j).Coord ≤ ∑ _j : Fin m, M :=
        Finset.sum_le_sum (fun j _ => hCoord j)
      _ = m * M := by simp
  have htagsDimension := htags.trans
    ((preparedBadProduct_dimension_le_initial_allocation m (nX + m * M)).trans
      (enlargedPreparedCommonSamplerDimension_allocation m M Jalloc))
  exact ⟨(Nat.cast_le.mpr hcounts.2.2.2.1).trans hnum,
    (Nat.cast_le.mpr htagsDimension).trans hnum,
    (Nat.cast_le.mpr hcounts.2.2.2.2.1).trans hnum,
    (Nat.cast_le.mpr hcounts.1).trans hnum⟩

theorem preparedFiniteNestedSource_counts
    {m : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
    (nX M cutoff : ℕ) {Bstruct : ℝ}
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hnum : (enlargedPreparedCommonSamplerDimension (max m cutoff) M
      (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M)) : ℝ) ≤ Bstruct) :
    (Fintype.card (EnlargedPreparedCommonKernel (max m cutoff)
      (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M))) : ℝ) ≤ Bstruct ∧
    (Fintype.card (Fin nX ⊕ (Σ j, (prep.pad (max m cutoff) j).Coord)) : ℝ) ≤ Bstruct ∧
    (Fintype.card (LayerSamplerVariables
      (EnlargedPreparedCommonKernel (max m cutoff)
        (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M)))
      (PreparedSamplerContinuous (prep.pad (max m cutoff)))
      (preparedSamplerTransverse (prep.pad (max m cutoff)))
      (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff))
        (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M)))) : ℝ)
        ≤ Bstruct ∧ ((max m cutoff : ℕ) : ℝ) ≤ Bstruct :=
  preparedFiniteCanonicalSource_counts (prep.pad (max m cutoff)) nX M
    (prep.pad_coordinate_card_le hCoord) hnum

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedFiniteNestedSource_counts := @OAI.Erdos3.VectorPolynomial.preparedFiniteNestedSource_counts
