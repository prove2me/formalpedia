-- Prove2me | solution 1 for OAI.SegmentLenses.mem_atomicBody_of_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:33:18.701679+00:00
-- url     : https://prove2.me/submissions/26ef9a4f-cd40-4a9c-afb9-ed29c24b08ce

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/AtomicBalls.lean:L219-L250
-- (upload_full_project.md Phase 4): solution for node OAI.SegmentLenses.mem_atomicBody_of_norm_le_one. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
import Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls
import Theorems.Thm_OAI_SegmentLenses_SegmentFamily_clip_seminorm

-- ---- from OAI.Analysis.SegmentLenses.Pairing ----
namespace OAI

/-!
# Finite heads and the completion–dual pairing
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section Restrictions
variable {V : Type*} [decidableEqV : DecidableEq V] [PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

end Restrictions

section Pairing
variable {V : Type*} [SegmentSystem V]

end Pairing

section MorePairing
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

end MorePairing

section DualRestrictions
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

end DualRestrictions

section IndexedFamilies
variable {V ι : Type*} [DecidableEq V] [SegmentSystem V] [Fintype ι]

end IndexedFamilies

section ClipFamilies
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

theorem SegmentFamily.clip_subset {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (F : SegmentFamily V) : ∀ S ∈ (F.clip hH).sets, S ⊆ H := by
  intro S hS
  obtain ⟨T, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hS).2
  exact Finset.inter_subset_right

end ClipFamilies

end SegmentLenses

end

end OAI

-- ---- from OAI.Analysis.SegmentLenses.AtomicBalls ----
namespace OAI

/-!
# Atomic polar descriptions of finite unit balls
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section FiniteBodies
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

@[continuity, fun_prop] theorem continuous_coefficientBudget (K : Finset V) :
    Continuous (coefficientBudget K) := by
  unfold coefficientBudget
  fun_prop

theorem coefficientBudget_nonneg (K : Finset V) (c : LocalCoefficients K) :
    0 ≤ coefficientBudget K c := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem norm_le_coefficientBudget (K : Finset V) (c : LocalCoefficients K) :
    ‖c‖ ≤ coefficientBudget K c := by
  apply (pi_norm_le_iff_of_nonneg (coefficientBudget_nonneg K c)).mpr
  intro F
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ F)

theorem compact_coefficientBall (K : Finset V) {R : ℝ} (_hR : 0 ≤ R) :
    IsCompact {c : LocalCoefficients K | coefficientBudget K c ≤ R} := by
  apply (isCompact_closedBall (0 : LocalCoefficients K) R).of_isClosed_subset
    (isClosed_le (continuous_coefficientBudget K) continuous_const)
  intro c hc
  simpa only [Metric.mem_closedBall, dist_zero_right] using (norm_le_coefficientBudget K c).trans hc

theorem convex_coefficientBall (K : Finset V) (R : ℝ) :
    Convex ℝ {c : LocalCoefficients K | coefficientBudget K c ≤ R} := by
  intro c hc d hd a b ha hb hab
  change (∑ F, ‖a • c F + b • d F‖) ≤ R
  calc
    (∑ F, ‖a • c F + b • d F‖) ≤ ∑ F, (a * ‖c F‖ + b * ‖d F‖) := by
      apply Finset.sum_le_sum
      intro F hF
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] using
        norm_add_le (a • c F) (b • d F)
    _ = a * coefficientBudget K c + b * coefficientBudget K d := by
      simp only [coefficientBudget, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ a * R + b * R := add_le_add (mul_le_mul_of_nonneg_left hc ha)
      (mul_le_mul_of_nonneg_left hd hb)
    _ = R := by rw [← add_mul, hab, one_mul]

theorem compact_atomicBody (K : Finset V) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (atomicBody K R) :=
  (compact_coefficientBall K hR).image (localValue K).continuous_of_finiteDimensional

theorem convex_atomicBody (K : Finset V) (R : ℝ) : Convex ℝ (atomicBody K R) :=
  (convex_coefficientBall K R).linear_image (localValue K)

theorem familyValue_mem_atomicBody (K : Finset V) (F : LocalFamily K)
    (c : FamilyCoefficients F.val) {R : ℝ} (hc : ‖c‖ ≤ R) :
    familyValue F.val c ∈ atomicBody K R := by
  classical
  refine ⟨Pi.single (M := fun F : LocalFamily K => FamilyCoefficients F.val) F c, ?_, ?_⟩
  · change (∑ G, ‖Pi.single (M := fun F : LocalFamily K => FamilyCoefficients F.val) F c G‖) ≤ R
    have he : (fun G : LocalFamily K => ‖Pi.single (M := fun F : LocalFamily K => FamilyCoefficients F.val) F c G‖) = Pi.single F ‖c‖ := by
      funext G
      exact Pi.apply_single (fun G (c : FamilyCoefficients G.val) => ‖c‖) (fun _ => norm_zero) F c G
    rw [he]
    simpa [Pi.single_apply] using hc
  · change (∑ G, familyValue G.val (Pi.single (M := fun F : LocalFamily K => FamilyCoefficients F.val) F c G)) = _
    have he : (fun G : LocalFamily K => familyValue G.val (Pi.single (M := fun F : LocalFamily K => FamilyCoefficients F.val) F c G)) =
        Pi.single F (familyValue F.val c) := by
      funext G
      exact Pi.apply_single (fun G => familyValue G.val) (fun _ => map_zero _) F c G
    rw [he]
    simp [Pi.single_apply]

end FiniteBodies

section FinitePolar
variable {V : Type*} [decidableEqV : DecidableEq V] [segmentSystemV : SegmentSystem V]

theorem Test.support_ofFinite (K : Finset V) (a : V → ℝ) :
    (Test.ofFinite K a).coeff.support ⊆ K := by
  intro v hv
  by_contra hn
  exact Finsupp.mem_support_iff.mp hv (by simp [hn])

theorem polarTest_pairing (K : Finset V) (f : FullDual V →L[ℝ] ℝ) (z : FullDual V) :
    f (head K z) = z ((polarTest K f : Test V) : Primal V) := by
  simp [head, polarTest, mul_comm]

theorem polarTest_familyValue (K : Finset V) (f : FullDual V →L[ℝ] ℝ)
    (F : LocalFamily K) (c : FamilyCoefficients F.val) :
    f (familyValue F.val c) = ∑ S, c S * (F.val.test (polarTest K f).coeff) S := by
  change f (∑ S, c S • segmentFunctional S.val) = _
  simp only [map_sum, map_smul, smul_eq_mul, SegmentFamily.test_apply]
  apply Finset.sum_congr rfl
  intro S hS
  congr 1
  simp only [segmentFunctional, map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  simp [polarTest, F.property _ S.property hv]

end FinitePolar

section EuclideanNormalization
variable {ι : Type*} [Fintype ι]

theorem norm_normalized_le (q : EuclideanSpace ℝ ι) : ‖‖q‖⁻¹ • q‖ ≤ 1 := by
  by_cases hq : ‖q‖ = 0
  · simp [hq]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg q)),
      inv_mul_cancel₀ hq]

theorem normalized_pairing (q : EuclideanSpace ℝ ι) :
    (∑ i, (‖q‖⁻¹ • q) i * q i) = ‖q‖ := by
  have hs : (∑ i, q i ^ 2) = ‖q‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  simp only [PiLp.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  simp_rw [← sq]
  rw [hs]
  by_cases hq : ‖q‖ = 0
  · simp [hq]
  · field_simp

end EuclideanNormalization

section AtomicSeparation
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

theorem mem_atomicBody_of_norm_le_one {K : Finset V} (hK : Ancestral (· ≤ ·) K)
    (z : FullDual V) (hz : head K z = z) (hn : ‖z‖ ≤ 1) :
    z ∈ atomicBody K 1 := by
  by_contra hnot
  obtain ⟨f, a, hfa, haz⟩ := geometric_hahn_banach_closed_point
    (convex_atomicBody K 1) (compact_atomicBody K (by norm_num : (0 : ℝ) ≤ 1)).isClosed hnot
  let p := polarTest K f
  have hp : p.coeff.support ⊆ K := Test.support_ofFinite K _
  have hpn : ‖p‖ ≤ a := by
    change segmentSeminorm V p.coeff ≤ a
    rw [segmentSeminorm_apply]
    apply ciSup_le
    intro F
    let G : LocalFamily K := ⟨F.clip hK, F.clip_subset hK⟩
    let q := G.val.test p.coeff
    have hm := familyValue_mem_atomicBody K G (‖q‖⁻¹ • q) (norm_normalized_le q)
    have hf := hfa _ hm
    rw [polarTest_familyValue, normalized_pairing] at hf
    change G.val.seminorm p.coeff < a at hf
    rw [show G.val = F.clip hK from rfl, F.clip_seminorm hK p.coeff hp] at hf
    exact hf.le
  have hpair := polarTest_pairing K f z
  rw [hz] at hpair
  have hop := z.le_opNorm (p : Primal V)
  rw [Real.norm_eq_abs, UniformSpace.Completion.norm_coe] at hop
  have hle : f z ≤ a := calc
    f z = z (p : Primal V) := hpair
    _ ≤ |z (p : Primal V)| := le_abs_self _
    _ ≤ ‖z‖ * ‖p‖ := hop
    _ ≤ ‖p‖ := mul_le_of_le_one_left (norm_nonneg _) hn
    _ ≤ a := hpn
  exact not_lt_of_ge hle haz

end AtomicSeparation

end SegmentLenses

end

end OAI

-- ---- platform node ----
open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

theorem solution {K : Finset V} (hK : Ancestral (· ≤ ·) K)
    (z : FullDual V) (hz : head K z = z) (hn : ‖z‖ ≤ 1) :
    z ∈ atomicBody K 1 := by
  first
    | exact OAI.SegmentLenses.mem_atomicBody_of_norm_le_one hK z hz hn
    | exact OAI.SegmentLenses.mem_atomicBody_of_norm_le_one
    | (apply OAI.SegmentLenses.mem_atomicBody_of_norm_le_one <;> assumption)
    | (intros; apply OAI.SegmentLenses.mem_atomicBody_of_norm_le_one <;> assumption)
