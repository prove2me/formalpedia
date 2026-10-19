-- Prove2me | solution 1 for OAI.ArnoldCounterexample.CriticalBound.cover_map
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:12:40.910966+00:00
-- url     : https://prove2.me/submissions/735952dc-dd0e-4493-a9b2-79ece9a1b6cc

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Deformation.lean:L156-L213
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.CriticalBound.cover_map. The node keeps its source
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
import Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_exists_smooth_descent
import Theorems.Thm_OAI_ArnoldCounterexample_Descent_critical_level_cover

-- ---- from OAI.Geometry.Arnold.Model ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff

namespace ArnoldCounterexample

lemma unitQuadric_ne_zero (z : UnitQuadric) : (z : CV) ≠ 0 := by
  intro h
  have hz := z.property.1
  simp [normSquared, h] at hz

end ArnoldCounterexample

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

lemma project_eq_phase (z w : UnitQuadric) (heq : project w = project z) :
    ∃ a : ℂ, Complex.normSq a = 1 ∧ (w : CV) = a • (z : CV) := by
  have hp := congrArg Subtype.val heq
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hp
  have hn := w.property.1
  rw [← ha, normSquared_smul, z.property.1, mul_one] at hn
  exact ⟨a, hn, ha.symm⟩

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Quadric ArnoldCounterexample.Descent

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Quadric ArnoldCounterexample.Forms ArnoldCounterexample.Descent

lemma critical_chart (h : SmoothFunction) (hf : (criticalSet h).Finite) :
    ∃ ℓ : CV →L[ℂ] ℂ, ∀ z : UnitQuadric, IsCritical h.toFun (project z) → ℓ z ≠ 0 := by
  classical
  let : Fintype (criticalSet h) := hf.fintype
  choose r hr using fun q : criticalSet h ↦ project_surjective q.val
  obtain ⟨ℓ, hℓ⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℂ)
    (fun q : criticalSet h ↦ (r q : CV)) (fun q ↦ unitQuadric_ne_zero (r q))
  refine ⟨ℓ.toContinuousLinearMap, ?_⟩
  intro z hz
  let q : criticalSet h := ⟨project z, hz⟩
  obtain ⟨a, ha, hza⟩ := project_eq_phase (r q) z (hr q).symm
  have ha0 : a ≠ 0 := fun hn ↦ by simp [hn] at ha
  change ℓ (z : CV) ≠ 0
  rw [hza, map_smul, smul_eq_mul]
  exact mul_ne_zero ha0 (hℓ q)

lemma contDiff_iterate {D : CV → CV} (hD : ContDiff ℝ ∞ D) (n : ℕ) :
    ContDiff ℝ ∞ (D^[n]) := by
  induction n with
  | zero => simpa using (contDiff_id : ContDiff ℝ ∞ (id : CV → CV))
  | succ n hn => simpa only [Function.iterate_succ] using hn.comp hD

lemma iterate_preserves {D : CV → CV}
    (hD : ∀ z : UnitQuadric, IsUnitQuadric (D z)) (n : ℕ) (z : UnitQuadric) :
    IsUnitQuadric (D^[n] z) := by
  induction n with
  | zero => exact z.property
  | succ n hn => simpa only [Function.iterate_succ_apply'] using hD ⟨_, hn⟩

lemma iterate_phase {D : CV → CV}
    (hD : ∀ z : UnitQuadric, IsUnitQuadric (D z))
    (heq : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → D (a • (z : CV)) = a • D z)
    (n : ℕ) (z : UnitQuadric) (a : ℂ) (ha : Complex.normSq a = 1) :
    D^[n] (a • (z : CV)) = a • (D^[n] z) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    simpa only [Function.iterate_succ_apply', hn] using heq ⟨D^[n] z, iterate_preserves hD n z⟩ a ha

/-- Three or fewer critical points yield three nonvanishing-coordinate descent
charts, on the literal quadric, with no Morse or nondegeneracy hypotheses. -/
theorem cover_map (h : SmoothFunction) (hsmall : (criticalSet h).encard ≤ 3) :
    ∃ F : CV → CSpace 3, ContDiff ℝ ∞ F ∧
      (∀ z : UnitQuadric, F z ≠ 0) ∧
      (∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → F (a • (z : CV)) = a • F z) := by
  classical
  have hf : (criticalSet h).Finite := Set.finite_of_encard_le_coe hsmall
  obtain ⟨G, hG, hagree⟩ := Extension.global_extension isCompact_unitQuadric
    (fun z : UnitQuadric ↦ h.toFun (project z)) h.smooth
  obtain ⟨D, hD, hDK, hDphase, hdec, hstationary⟩ := exists_smooth_descent hG hagree
  obtain ⟨ℓ, hℓ⟩ := critical_chart h hf
  let DK : UnitQuadric → UnitQuadric := fun z ↦ ⟨D z, hDK z⟩
  have hDKcont : Continuous DK := (hD.continuous.comp continuous_subtype_val).subtype_mk _
  let fK : UnitQuadric → ℝ := fun z ↦ G z
  let ℓK : UnitQuadric → ℂ := fun z ↦ ℓ z
  let s : Finset ℝ := hf.toFinset.image h.toFun
  obtain ⟨zmax, _, hzmax⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty :
    (Set.univ : Set UnitQuadric).Nonempty) (hG.continuous.comp continuous_subtype_val).continuousOn
  obtain ⟨T, hTcard, hT⟩ := critical_level_cover hDKcont
    (hG.continuous.comp continuous_subtype_val) (ℓ.continuous.comp continuous_subtype_val)
    hdec (fun z hz ↦ lt_of_le_of_ne (hdec z) (fun heq ↦ hℓ z (hstationary z heq) hz))
    s (G zmax) (fun z _ heq ↦ by
      apply Finset.mem_image.mpr
      exact ⟨project z, hf.mem_toFinset.mpr (hstationary z heq), (hagree z).symm⟩)
  have hcard : T.card ≤ 3 := by
    have hfcard : hf.toFinset.card ≤ 3 := by
      have hh := hsmall
      rw [hf.encard_eq_coe_toFinset_card] at hh
      exact_mod_cast hh
    exact hTcard.trans (Finset.card_image_le.trans hfcard)
  let e : T ↪ Fin 3 := T.equivFin.toEmbedding.trans (Fin.castLEEmb hcard)
  let F : CV → CSpace 3 := fun z ↦ Function.extend e (fun n : T ↦ ℓ (D^[n.val] z)) 0
  have hiterate (n : ℕ) (z : UnitQuadric) : ((DK^[n] z : UnitQuadric) : CV) = D^[n] z := by
    induction n with
    | zero => rfl
    | succ n hn => simp only [Function.iterate_succ_apply']; exact congrArg D hn
  refine ⟨F, contDiff_pi.mpr (fun i ↦ ?_), ?_, ?_⟩
  · by_cases hi : ∃ n : T, e n = i
    · obtain ⟨n, rfl⟩ := hi
      simp only [F, e.injective.extend_apply]
      exact (ℓ.restrictScalars ℝ).contDiff.comp (contDiff_iterate hD n.val)
    · simp only [F, Function.extend_apply' _ _ _ hi, Pi.zero_apply]
      exact contDiff_const
  · intro z hz
    obtain ⟨n, hn, hnz⟩ := hT z (hzmax (Set.mem_univ z))
    have hcoord := congrFun hz (e ⟨n, hn⟩)
    simp only [F, e.injective.extend_apply, Pi.zero_apply] at hcoord
    change ℓ ((DK^[n] z : UnitQuadric) : CV) ≠ 0 at hnz
    rw [hiterate] at hnz
    exact hnz hcoord
  · intro z a ha
    ext i
    by_cases hi : ∃ n : T, e n = i
    · obtain ⟨n, rfl⟩ := hi
      simp only [F, e.injective.extend_apply, Pi.smul_apply,
        iterate_phase hDK hDphase n.val z a ha, map_smul]
    · simp only [F, Function.extend_apply' _ _ _ hi, Pi.zero_apply, Pi.smul_apply, smul_zero]

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
open ArnoldCounterexample.Quadric ArnoldCounterexample.Forms ArnoldCounterexample.Descent


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.CriticalBound.cover_map := @_root_.OAI.ArnoldCounterexample.CriticalBound.cover_map
