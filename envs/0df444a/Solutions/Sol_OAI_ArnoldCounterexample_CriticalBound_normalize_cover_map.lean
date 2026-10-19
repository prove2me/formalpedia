-- Prove2me | solution 1 for OAI.ArnoldCounterexample.CriticalBound.normalize_cover_map
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:14:22.232441+00:00
-- url     : https://prove2.me/submissions/a4f8b567-e752-4081-9b3e-9424c538c2ac

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Deformation.lean:L215-L260
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.CriticalBound.normalize_cover_map. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation

-- ---- from OAI.Geometry.Arnold.Symplectic ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Forms

lemma normSq_contDiff (n : ℕ) : ContDiff ℝ ∞ (normSq n) := by
  unfold normSq
  apply ContDiff.sum
  intro i _
  simpa only [Complex.normSq_apply, reCoord_apply, imCoord_apply] using
    (((reCoord n i).contDiff.mul (reCoord n i).contDiff).add
      ((imCoord n i).contDiff.mul (imCoord n i).contDiff))

lemma normSq_nonneg (n : ℕ) (z : CSpace n) : 0 ≤ normSq n z :=
  Finset.sum_nonneg (fun _ _ ↦ Complex.normSq_nonneg _)

lemma normSq_eq_zero_iff (n : ℕ) (z : CSpace n) : normSq n z = 0 ↔ z = 0 := by
  constructor
  · intro h
    ext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ Complex.normSq_nonneg (z j))).mp h i (Finset.mem_univ i)
    exact Complex.normSq_eq_zero.mp hi
  · rintro rfl
    simp [normSq]

lemma normSq_smul (n : ℕ) (a : ℂ) (z : CSpace n) :
    normSq n (a • z) = Complex.normSq a * normSq n z := by
  simp [normSq, Complex.normSq_mul, Finset.mul_sum]

end ArnoldCounterexample.Forms

end

end OAI

-- ---- from OAI.Geometry.Arnold.Deformation ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Quadric

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
-- [generator] trimmed: open ArnoldCounterexample.Quadric ArnoldCounterexample.Descent
open ArnoldCounterexample.Quadric

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
-- [generator] trimmed: open ArnoldCounterexample.Quadric ArnoldCounterexample.Forms ArnoldCounterexample.Descent
open ArnoldCounterexample.Quadric ArnoldCounterexample.Forms

/-- Normalization has a globally smooth ambient extension, even away from K.
The positive complement bump prevents spurious singularities off K. -/
theorem normalize_cover_map {F : CV → CSpace 3} (hF : ContDiff ℝ ∞ F)
    (hne : ∀ z : UnitQuadric, F z ≠ 0)
    (hphase : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → F (a • (z : CV)) = a • F z) :
    ∃ F' : CV → CSpace 3, ContDiff ℝ ∞ F' ∧
      (∀ z : UnitQuadric, normSq 3 (F' z) = 1) ∧
      (∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → F' (a • (z : CV)) = a • F' z) := by
  obtain ⟨δ, hδsupp, hδ, hδrange⟩ := isClosed_unitQuadric.isOpen_compl.exists_contDiff_support_eq (n := ⊤)
  have hδzero (z : UnitQuadric) : δ z = 0 := by
    by_contra hne
    have hz : ↑z ∈ Function.support δ := hne
    rw [hδsupp] at hz
    exact hz z.property
  let S : CV → ℝ := fun z ↦ normSq 3 (F z) + δ z
  have hS : ContDiff ℝ ∞ S := ((normSq_contDiff 3).comp hF).add hδ
  have hpos (z : CV) : 0 < S z := by
    by_cases hz : IsUnitQuadric z
    · have hn : normSq 3 (F z) ≠ 0 := fun hn ↦ hne ⟨z, hz⟩ ((normSq_eq_zero_iff _ _).mp hn)
      have hp := lt_of_le_of_ne (normSq_nonneg 3 (F z)) hn.symm
      change 0 < normSq 3 (F z) + δ z
      exact add_pos_of_pos_of_nonneg hp (hδrange ⟨z, rfl⟩).1
    · have hd : δ z ≠ 0 := by
        change z ∈ Function.support δ
        rw [hδsupp]
        exact hz
      exact add_pos_of_nonneg_of_pos (normSq_nonneg 3 (F z))
        (lt_of_le_of_ne (hδrange ⟨z, rfl⟩).1 hd.symm)
  let F' : CV → CSpace 3 := fun z ↦ (Real.sqrt (S z))⁻¹ • F z
  refine ⟨F', ((hS.sqrt (fun z ↦ (hpos z).ne')).inv (fun z ↦
    (Real.sqrt_pos.2 (hpos z)).ne')).smul hF, ?_, ?_⟩
  · intro z
    change normSq 3 ((Real.sqrt (S z))⁻¹ • F z) = 1
    have hss : S z = normSq 3 (F z) := by simp only [S, hδzero z, add_zero]
    change normSq 3 (((Real.sqrt (S z))⁻¹ : ℝ) • F z) = 1
    change normSq 3 ((((Real.sqrt (S z))⁻¹ : ℝ) : ℂ) • F z) = 1
    rw [normSq_smul, Complex.normSq_ofReal, ← pow_two,
      inv_pow, Real.sq_sqrt (hpos z).le, hss]
    exact inv_mul_cancel₀ (by simpa only [← hss] using (hpos z).ne')
  · intro z a ha
    have hs : S (a • (z : CV)) = S z := by
      simp only [S, hδzero ⟨_, unit_phase z a ha⟩, hδzero z, add_zero, hphase z a ha,
        normSq_smul, ha, one_mul]
    dsimp only [F']
    rw [hs, hphase z a ha]
    exact smul_comm _ _ _

end ArnoldCounterexample.CriticalBound

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.CriticalBound
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ArnoldCounterexample.Quadric ArnoldCounterexample.Forms


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.CriticalBound.normalize_cover_map := @_root_.OAI.ArnoldCounterexample.CriticalBound.normalize_cover_map
