-- Prove2me | solution 1 for OAI.MainGap.mem_Her_of_nonneg_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:11:18.198898+00:00
-- url     : https://prove2.me/submissions/91e4eca5-555e-4977-aeea-2d1391c27852

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Hereditary.lean:L457-L476
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.mem_Her_of_nonneg_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
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

lemma norm_sqrt_remainder_sq_le {e a b : A} (he : IsSelfAdjoint e) (hen : ‖e‖ ≤ 1)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖CFC.sqrt a - e * CFC.sqrt a‖ ^ 2 ≤ 2 * ‖b - e * b‖ := by
  calc
    ‖CFC.sqrt a - e * CFC.sqrt a‖ ^ 2 = ‖twoSidedRemainder e a‖ := by
      rw [twoSidedRemainder_as_square he ha, CStarRing.norm_self_mul_star, pow_two]
    _ ≤ ‖twoSidedRemainder e b‖ :=
      CStarAlgebra.norm_le_norm_of_nonneg_of_le (twoSidedRemainder_nonneg he ha)
        (twoSidedRemainder_mono he hab)
    _ ≤ 2 * ‖b - e * b‖ := norm_twoSidedRemainder_le hen b

lemma norm_compression_error_le {e a : A} (he : IsSelfAdjoint e) (hen : ‖e‖ ≤ 1)
    (ha : 0 ≤ a) :
    ‖a - e * a * e‖ ≤ 2 * ‖CFC.sqrt a - e * CFC.sqrt a‖ * ‖CFC.sqrt a‖ := by
  have ha' : IsSelfAdjoint a := .of_nonneg ha
  have hstar : ‖a - a * e‖ = ‖a - e * a‖ := by
    rw [← norm_star (a - a * e), star_sub, star_mul, he.star_eq, ha'.star_eq]
  have heq : a - e * a * e = (a - e * a) + e * (a - a * e) := by noncomm_ring
  have hbound : ‖a - e * a‖ ≤ ‖CFC.sqrt a - e * CFC.sqrt a‖ * ‖CFC.sqrt a‖ := by
    calc
      ‖a - e * a‖ = ‖(CFC.sqrt a - e * CFC.sqrt a) * CFC.sqrt a‖ := by
        rw [sub_mul, mul_assoc e, CFC.sqrt_mul_sqrt_self a ha]
      _ ≤ _ := norm_mul_le _ _
  calc
    ‖a - e * a * e‖ = ‖(a - e * a) + e * (a - a * e)‖ := congrArg norm heq
    _ ≤ ‖a - e * a‖ + ‖e * (a - a * e)‖ := norm_add_le _ _
    _ ≤ ‖a - e * a‖ + ‖e‖ * ‖a - a * e‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ 2 * ‖a - e * a‖ := by rw [hstar]; nlinarith [norm_nonneg (a - e * a)]
    _ ≤ _ := by nlinarith

lemma norm_compression_error_sq_le {e a b : A} (he : IsSelfAdjoint e) (hen : ‖e‖ ≤ 1)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖a - e * a * e‖ ^ 2 ≤ 8 * ‖a‖ * ‖b - e * b‖ := by
  have hsa : IsSelfAdjoint (CFC.sqrt a) := .of_nonneg (CFC.sqrt_nonneg _)
  have hsq : ‖CFC.sqrt a‖ ^ 2 = ‖a‖ := by
    rw [← hsa.norm_mul_self, CFC.sqrt_mul_sqrt_self a ha]
  calc
    ‖a - e * a * e‖ ^ 2 ≤
        (2 * ‖CFC.sqrt a - e * CFC.sqrt a‖ * ‖CFC.sqrt a‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (norm_compression_error_le he hen ha)
    _ = 4 * ‖a‖ * ‖CFC.sqrt a - e * CFC.sqrt a‖ ^ 2 := by rw [← hsq]; ring
    _ ≤ 4 * ‖a‖ * (2 * ‖b - e * b‖) := by
      gcongr
      exact norm_sqrt_remainder_sq_le he hen ha hab
    _ = _ := by ring

lemma mem_Her_of_nonneg_le {a b : A} (ha : 0 ≤ a) (hab : a ≤ b) : a ∈ Her b := by
  have hb : 0 ≤ b := ha.trans hab
  have hc : a ∈ closure (Her b : Set A) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hden : 0 < 8 * ‖a‖ + 1 := by positivity
    have hδ : 0 < ε ^ 2 / (8 * ‖a‖ + 1) := div_pos (sq_pos_of_pos hε) hden
    obtain ⟨e, he, hesa, hen, hesmall⟩ := Her_exists_approx_unit hb hδ
    refine ⟨e * a * e, ?_, ?_⟩
    · change e * a * e ∈ Her b
      simpa only [hesa.star_eq] using Her_sandwich he a
    · rw [dist_eq_norm]
      have hsq := norm_compression_error_sq_le hesa hen ha hab
      have hp : (8 * ‖a‖ + 1) * ‖b - e * b‖ < ε ^ 2 := by
        have ht := mul_lt_mul_of_pos_left hesmall hden
        rwa [mul_div_cancel₀ _ (ne_of_gt hden)] at ht
      have hfinal : ‖a - e * a * e‖ ^ 2 < ε ^ 2 := by
        nlinarith [norm_nonneg (b - e * b)]
      exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hfinal
  rwa [(isClosed_Her b).closure_eq] at hc

end Order

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace


theorem solution : type_of% @_root_.OAI.MainGap.mem_Her_of_nonneg_le := @_root_.OAI.MainGap.mem_Her_of_nonneg_le
