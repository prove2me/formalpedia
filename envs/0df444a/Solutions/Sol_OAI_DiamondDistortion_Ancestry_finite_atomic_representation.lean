-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.finite_atomic_representation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:53:16.814636+00:00
-- url     : https://prove2.me/submissions/2af5931c-2437-4aae-8280-021322fcceee

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L782-L828
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.finite_atomic_representation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_localize_family_energy
import Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_coefficientBall_convex
import Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_coordinateTest_pairing
import Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_local_energy_le_of_functional_bound

-- ---- from OAI.Analysis.DiamondDistortion.SegmentNorm ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι : Type*} (T : SegmentSystem ι)

variable {T}

variable (T)

lemma coordinateTest_not_mem (K : Finset ι) (a : T.Coordinates K)
    {v : ι} (hv : v ∉ K) : T.coordinateTest K a v = 0 := by simp [coordinateTest, hv]

lemma functional_pi_formula (K : Finset ι) (f : T.Coordinates K →L[ℝ] ℝ)
    (z : T.Coordinates K) : f z = ∑ v : K, z v * f (Pi.single v 1) := by
  classical
  have hz : z = ∑ v : K, z v • (Pi.single v 1 : T.Coordinates K) := by
    ext w
    simp [Pi.single_apply, Finset.sum_apply, mul_ite, Finset.sum_ite_eq]
  conv_lhs => rw [hz]
  simp only [map_sum, map_smul, smul_eq_mul]

variable {T}

variable (T)

lemma finiteEmbedding_norm (p : ι →₀ ℝ) :
    ‖T.finiteEmbedding p‖ = T.primalSeminorm p := by
  rw [finiteEmbedding_apply, UniformSpace.Completion.norm_coe]
  rfl

lemma coefficientBall_compact (K : Finset ι) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (T.coefficientBall K R) := by
  apply (isCompact_closedBall (0 : T.Coefficients K) R).of_isClosed_subset
  · exact isClosed_le (by fun_prop) continuous_const
  · intro c hc
    simp only [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro F
    exact (Finset.single_le_sum (fun G _ => norm_nonneg (c G)) (Finset.mem_univ F)).trans hc

lemma totalMap_single (K : Finset ι) (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) :
    T.totalMap K (Pi.single F a) = T.localMap F a := by
  classical
  rw [totalMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_eq_single F]
  · rw [Pi.single_eq_same]
  · intro G _ hGF
    rw [Pi.single_eq_of_ne hGF, map_zero]
  · simp

lemma single_mem_coefficientBall (K : Finset ι) (F : T.LocalFamily K)
    (a : EuclideanSpace ℝ (T.LocalIndex F)) {R : ℝ} (ha : ‖a‖ ≤ R) :
    Pi.single F a ∈ T.coefficientBall K R := by
  classical
  change ∑ G, ‖(Pi.single F a : T.Coefficients K) G‖ ≤ R
  rw [Finset.sum_eq_single F]
  · simpa only [Pi.single_eq_same] using ha
  · intro G _ hGF
    rw [Pi.single_eq_of_ne hGF, norm_zero]
  · simp

end SegmentSystem

end DiamondDistortion

end

end OAI

-- ---- from OAI.Analysis.DiamondDistortion.Ancestry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Ancestry
open scoped Classical
variable {ι : Type*} [A : Ancestry ι]
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder
lemma primal_le_of_local_energies {K : Finset ι} (hK : A.Ancestral (K : Set ι))
    (p : ι →₀ ℝ) (hp : ∀ v, v ∉ K → p v = 0) {M : ℝ} (hM : 0 ≤ M)
    (hlocal : ∀ G : A.segments.LocalFamily K,
      (∑ S : A.segments.LocalIndex G, (∑ v ∈ S.val, p v) ^ 2) ≤ M ^ 2) :
    A.segments.primalSeminorm p ≤ M := by
  rw [SegmentSystem.primalSeminorm, Seminorm.iSup_apply A.segments.families_bddAbove]
  apply ciSup_le
  intro F
  obtain ⟨G, he⟩ := A.localize_family_energy hK F p hp
  have h := hlocal G
  rw [← he] at h
  have hnorm : ‖F.test p‖ ^ 2 = ∑ i, (∑ v ∈ F.seg i, p v) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [SegmentSystem.Family.test_apply, Real.norm_eq_abs, sq_abs]
  rw [← hnorm] at h
  exact (sq_le_sq₀ (norm_nonneg _) hM).mp h

/-- Finite atomic-ball formula: exact inherited dual restrictions, derived by
    finite-dimensional separation rather than assumed as model data. -/
lemma finite_atomic_representation {K : Finset ι} (hK : A.Ancestral (K : Set ι))
    (x : A.segments.Dual) (hx : ‖x‖ ≤ 1) :
    ∃ c ∈ A.segments.coefficientBall K 1,
      A.segments.totalMap K c = fun v : K => x (A.segments.unitVector v.val) := by
  classical
  let C := A.segments.totalMap K '' A.segments.coefficientBall K 1
  let z : A.segments.Coordinates K := fun v => x (A.segments.unitVector v.val)
  suffices z ∈ C by exact this
  by_contra hn
  have hCc : Convex ℝ C := (A.segments.coefficientBall_convex K 1).linear_image _
  have hCk : IsCompact C := (A.segments.coefficientBall_compact K (by norm_num : (0:ℝ) ≤ 1)).image
    (A.segments.totalMap K).continuous_of_finiteDimensional
  obtain ⟨f, u, hfu, huz⟩ := geometric_hahn_banach_closed_point hCc hCk.isClosed hn
  have hzC : (0 : A.segments.Coordinates K) ∈ C := by
    refine ⟨0, ?_, map_zero _⟩
    change (∑ F : A.segments.LocalFamily K, ‖(0 : A.segments.Coefficients K) F‖) ≤ 1
    simp
  have hu : 0 < u := by simpa only [map_zero] using hfu 0 hzC
  let p := A.segments.coordinateTest K (fun w => f (Pi.single w 1))
  have hp : ∀ v, v ∉ K → p v = 0 := by
    intro v hv
    exact A.segments.coordinateTest_not_mem K _ hv
  have hpbound : A.segments.primalSeminorm p ≤ u := by
    apply A.primal_le_of_local_energies hK p hp hu.le
    intro F
    apply A.segments.local_energy_le_of_functional_bound F f hu.le
    intro a ha
    apply (hfu _ ?_).le
    refine ⟨Pi.single F a, A.segments.single_mem_coefficientBall K F a ha, ?_⟩
    exact A.segments.totalMap_single K F a
  have he : f z = x (A.segments.finiteEmbedding p) := by
    rw [A.segments.functional_pi_formula, A.segments.coordinateTest_pairing]
    apply Finset.sum_congr rfl
    intro v _
    exact mul_comm _ _
  have hle : f z ≤ u := by
    rw [he]
    calc
      x (A.segments.finiteEmbedding p) ≤ ‖x (A.segments.finiteEmbedding p)‖ := Real.le_norm_self _
      _ ≤ ‖x‖ * ‖A.segments.finiteEmbedding p‖ := x.le_opNorm _
      _ ≤ 1 * A.segments.primalSeminorm p := by
        rw [A.segments.finiteEmbedding_norm]
        exact mul_le_mul_of_nonneg_right hx (apply_nonneg _ _)
      _ ≤ u := by simpa using hpbound
  exact (not_lt_of_ge hle) huz

end Ancestry

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Ancestry
open scoped BigOperators Classical Topology
open Set
open scoped Classical
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.finite_atomic_representation := @_root_.OAI.DiamondDistortion.Ancestry.finite_atomic_representation
