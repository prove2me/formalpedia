-- Prove2me | solution 1 for GlobalTheory.mem_span_indicator_of_right_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:41:11.507509+00:00
-- url     : https://prove2.me/submissions/6916fba7-84e5-433d-a4f3-138b99aa747c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant
import Theorems.Thm_GlobalTheory_exists_eq_sum_indicator_of_right_invariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open LatticeIndicator
variable {O K m n R : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [CommRing R]
namespace GlobalTheory
theorem _root_.solution {a b : O} (ha : a ≠ 0) (hb : b ≠ 0)
    (φ : Matrix m n K → R)
    (hinv : ∀ (x : Matrix m n K) (k : GL n O),
      φ (x * (k : Matrix n n O).map (algebraMap O K)) = φ x)
    (hsupp : ∀ x : Matrix m n K, φ x ≠ 0 →
      ∀ i j, (algebraMap O K a • x) i j ∈ (algebraMap O K).range)
    (hper : ∀ x y : Matrix m n K, (∀ i j, y i j ∈ (algebraMap O K).range) →
      φ (x + algebraMap O K b • y) = φ x) :
    φ ∈ Submodule.span R (Set.range fun (h : GL m K) (x : Matrix m n K) =>
      Set.indicator {y : Matrix m n K | ∀ i j, y i j ∈ (algebraMap O K).range}
        (1 : Matrix m n K → R) (((h⁻¹ : GL m K) : Matrix m m K) * x)) := by
  obtain ⟨r, h, c, hφ⟩ := exists_eq_sum_indicator_of_right_invariant ha hb φ hinv hsupp hper
  have : φ = ∑ l, c l • fun x : Matrix m n K =>
      Set.indicator {y : Matrix m n K | ∀ i j, y i j ∈ (algebraMap O K).range}
        (1 : Matrix m n K → R) ((((h l)⁻¹ : GL m K) : Matrix m m K) * x) := by
    ext x
    rw [hφ x, Finset.sum_apply]
    rfl
  rw [this]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨h l, rfl⟩)
end GlobalTheory
