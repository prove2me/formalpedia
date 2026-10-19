-- Prove2me | solution 1 for OAI.MainGap.mem_Her_of_moduli
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:25:56.529035+00:00
-- url     : https://prove2.me/submissions/bb066226-0741-465b-95c3-19d27e0e2328

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Cutoffs.lean:L51-L81
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.mem_Her_of_moduli. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Theorems.Thm_OAI_MainGap_Her_exists_approx_unit

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Hereditary ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma Her_sandwich {h k : A} (hk : k ∈ Her h) (a : A) : k * a * star k ∈ Her h := by
  let k' : Her h := ⟨k, hk⟩
  change (k' : A) * a * star (k' : A) ∈ Her h
  refine (sandwichMap_dense h).induction_on k'
    ((isClosed_Her h).preimage (by fun_prop)) ?_
  intro b
  change (h * b * star h) * a * star (h * b * star h) ∈ Her h
  convert sandwich_mem_Her h (b * star h * a * h * star b) using 1
  simp only [star_mul, star_star, mul_assoc]

lemma Her_mono_of_mem {h k : A} (hk : k ∈ Her h) : Her k ≤ Her h := by
  apply closure_minimal _ (isClosed_Her h)
  rintro _ ⟨a, rfl⟩
  exact Her_sandwich hk a

namespace RegularTransport
variable {h v : A} (T : RegularTransport h v)

end RegularTransport

section Order
variable [PartialOrder A] [StarOrderedRing A]

lemma twoSidedRemainder_as_square {e a : A} (he : IsSelfAdjoint e) (ha : 0 ≤ a) :
    twoSidedRemainder e a =
      (CFC.sqrt a - e * CFC.sqrt a) * star (CFC.sqrt a - e * CFC.sqrt a) := by
  have hs : star (CFC.sqrt a) = CFC.sqrt a := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq
  simp only [star_sub, star_mul, he.star_eq, hs]
  calc
    twoSidedRemainder e a = a - e * a - a * e + e * a * e := rfl
    _ = (CFC.sqrt a * CFC.sqrt a) - e * (CFC.sqrt a * CFC.sqrt a) -
        (CFC.sqrt a * CFC.sqrt a) * e + e * (CFC.sqrt a * CFC.sqrt a) * e := by
      rw [CFC.sqrt_mul_sqrt_self a ha]
    _ = _ := by noncomm_ring

lemma twoSidedRemainder_nonneg {e a : A} (he : IsSelfAdjoint e) (ha : 0 ≤ a) :
    0 ≤ twoSidedRemainder e a := by
  rw [twoSidedRemainder_as_square he ha]
  exact mul_star_self_nonneg _

lemma twoSidedRemainder_mono {e a b : A} (he : IsSelfAdjoint e) (hab : a ≤ b) :
    twoSidedRemainder e a ≤ twoSidedRemainder e b := by
  apply sub_nonneg.mp
  convert twoSidedRemainder_nonneg he (sub_nonneg.mpr hab) using 1
  simp only [twoSidedRemainder]
  noncomm_ring

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_twoSidedRemainder_le {e : A} (he : ‖e‖ ≤ 1) (b : A) :
    ‖twoSidedRemainder e b‖ ≤ 2 * ‖b - e * b‖ := by
  have heq : twoSidedRemainder e b = (b - e * b) - (b - e * b) * e := by
    simp only [twoSidedRemainder]
    noncomm_ring
  rw [heq]
  calc
    ‖(b - e * b) - (b - e * b) * e‖ ≤ ‖b - e * b‖ + ‖(b - e * b) * e‖ := norm_sub_le _ _
    _ ≤ ‖b - e * b‖ + ‖b - e * b‖ * ‖e‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ 2 * ‖b - e * b‖ := by nlinarith [norm_nonneg (b - e * b)]

end Order

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Cutoffs ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
private theorem CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
section MoreHer
variable [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_left_remainder_sq {e z : A} (he : IsSelfAdjoint e) :
    ‖z - e * z‖ ^ 2 = ‖twoSidedRemainder e (z * star z)‖ := by
  rw [pow_two, ← CStarRing.norm_self_mul_star]
  congr 1
  simp only [twoSidedRemainder, star_sub, star_mul, he.star_eq]
  noncomm_ring

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_right_remainder_sq {e z : A} (he : IsSelfAdjoint e) :
    ‖z - z * e‖ ^ 2 = ‖twoSidedRemainder e (star z * z)‖ := by
  rw [← norm_star (z - z * e), star_sub, star_mul, he.star_eq,
    norm_left_remainder_sq he, star_star]

lemma norm_left_remainder_sq_le {e z b : A} (he : IsSelfAdjoint e)
    (hen : ‖e‖ ≤ 1) (hle : z * star z ≤ b) :
    ‖z - e * z‖ ^ 2 ≤ 2 * ‖b - e * b‖ := by
  rw [norm_left_remainder_sq he]
  exact (CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (twoSidedRemainder_mono he hle)
    (twoSidedRemainder_nonneg he (mul_star_self_nonneg z))).trans
      (norm_twoSidedRemainder_le hen b)

lemma norm_right_remainder_sq_le {e z b : A} (he : IsSelfAdjoint e)
    (hen : ‖e‖ ≤ 1) (hle : star z * z ≤ b) :
    ‖z - z * e‖ ^ 2 ≤ 2 * ‖b - e * b‖ := by
  rw [norm_right_remainder_sq he]
  exact (CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (twoSidedRemainder_mono he hle)
    (twoSidedRemainder_nonneg he (star_mul_self_nonneg z))).trans
      (norm_twoSidedRemainder_le hen b)

lemma mem_Her_of_moduli {h z : A} (hl : z * star z ∈ Her h)
    (hr : star z * z ∈ Her h) : z ∈ Her h := by
  let b := z * star z + star z * z
  have hb : 0 ≤ b := add_nonneg (mul_star_self_nonneg z) (star_mul_self_nonneg z)
  have hbh : b ∈ Her h := (Her h).add_mem hl hr
  have hbl : z * star z ≤ b := le_add_of_nonneg_right (star_mul_self_nonneg z)
  have hbr : star z * z ≤ b := le_add_of_nonneg_left (mul_star_self_nonneg z)
  have hzc : z ∈ closure (Her h : Set A) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨e, he, hesa, hen, hs⟩ := Her_exists_approx_unit hb
      (show 0 < ε^2 / 8 by positivity)
    have hδ : 2 * ‖b - e * b‖ < (ε / 2)^2 := by linarith
    have hle : ‖z - e * z‖ < ε / 2 := by
      exact (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp
        ((norm_left_remainder_sq_le hesa hen hbl).trans_lt hδ)
    have hre : ‖z - z * e‖ < ε / 2 := by
      exact (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp
        ((norm_right_remainder_sq_le hesa hen hbr).trans_lt hδ)
    refine ⟨e * z * e, ?_, ?_⟩
    · change e * z * e ∈ Her h
      simpa only [hesa.star_eq] using Her_sandwich (Her_mono_of_mem hbh he) z
    · rw [dist_eq_norm]
      have heq : z - e * z * e = (z - e * z) + e * (z - z * e) := by noncomm_ring
      rw [heq]
      calc
        ‖(z - e * z) + e * (z - z * e)‖ ≤ ‖z - e * z‖ + ‖e * (z - z * e)‖ := norm_add_le _ _
        _ ≤ ‖z - e * z‖ + ‖e‖ * ‖z - z * e‖ := by gcongr; exact norm_mul_le _ _
        _ ≤ ‖z - e * z‖ + ‖z - z * e‖ := by nlinarith [norm_nonneg (z - z * e)]
        _ < ε := by linarith
  rwa [(isClosed_Her h).closure_eq] at hzc

end MoreHer
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
section Ramps
variable [PartialOrder A] [StarOrderedRing A]

end Ramps
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]

section UnitalCutBounds
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

end UnitalCutBounds

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace


theorem solution : type_of% @_root_.OAI.MainGap.mem_Her_of_moduli := @_root_.OAI.MainGap.mem_Her_of_moduli
