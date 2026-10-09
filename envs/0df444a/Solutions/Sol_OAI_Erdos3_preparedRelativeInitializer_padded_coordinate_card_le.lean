-- Prove2me | solution 1 for OAI.Erdos3.preparedRelativeInitializer_padded_coordinate_card_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T12:07:22.104401+00:00
-- url     : https://prove2.me/submissions/eb447e86-3211-4489-bdac-ec1af74e3d79

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130
import Theorems.Thm_OAI_Erdos3_preparationCoordinateCap_mono

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

theorem preparedRelativeInitializer_padded_coordinate_card_le
    (prep : RankPreparationFamily (Fin nX) (Fin D) m) (hms : m ≤ s)
    (hcoord : ∀ j, Fintype.card (prep j).Coord ≤
      preparationCoordinateCap m D (m * D)) :
    ∀ j, Fintype.card (prep.pad (max m s) j).Coord ≤
      preparationCoordinateCap s D (s * D) := by
  apply prep.pad_coordinate_card_le
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

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.preparedRelativeInitializer_padded_coordinate_card_le := @OAI.Erdos3.preparedRelativeInitializer_padded_coordinate_card_le
