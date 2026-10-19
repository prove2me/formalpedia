-- Prove2me | solution 2 for OAI.BalancedTransport.Geometry.loadingVelocity_supported
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:03:32.566223+00:00
-- url     : https://prove2.me/submissions/5c9af295-0bd6-40b2-975f-b6913dfa50ee

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Loading.lean:L106-L120
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Geometry.loadingVelocity_supported. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Work ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem curl_congr {A B : Space → Space} {x : Space}
    (h : A =ᶠ[𝓝 x] B) : curl A x = curl B x := by
  have he (j : Fin 3) : (fun y => A y j) =ᶠ[𝓝 x] (fun y => B y j) :=
    h.mono (fun _ hh => congrFun hh j)
  simp only [curl, pd, (he 0).fderiv_eq, (he 1).fderiv_eq, (he 2).fderiv_eq]

theorem tsupport_curl_subset (A : Space → Space) :
    tsupport (curl A) ⊆ tsupport A := by
  apply closure_minimal _ (isClosed_tsupport A)
  intro x hx
  by_contra hxA
  have hh : A =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxA
  have hz := curl_congr hh
  exact hx (by simpa using hz)

theorem closedEnlargement_isCompact (a b : Space) (η : ℝ) :
    IsCompact (closedEnlargement a b η) := isCompact_Icc

theorem boxCutoff_eq_zero {a b : Space} {η : ℝ} (hη : 0 < η) {x : Space}
    (hx : x ∉ closedEnlargement a b (2 * η)) : boxCutoff a b η x = 0 := by
  rw [mem_closedEnlargement] at hx
  push Not at hx
  obtain ⟨i, hi⟩ := hx
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_cases hl : a i - 2 * η ≤ x i
  · have he : Real.smoothTransition ((b i + 2 * η - x i) / η) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (by linarith [hi hl]) hη.le)
    rw [he, mul_zero]
  · have he : Real.smoothTransition ((x i - a i + 2 * η) / η) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (by linarith) hη.le)
    rw [he, zero_mul]

theorem tsupport_localizedAffine_subset (a b c v l : Space) {η : ℝ} (hη : 0 < η) :
    tsupport (localizedAffine a b c v l η) ⊆ closedEnlargement a b (2 * η) := by
  refine (tsupport_curl_subset _).trans ?_
  apply closure_minimal _ (closedEnlargement_isCompact _ _ _).isClosed
  intro x hx
  by_contra hn
  exact hx (by simp [boxCutoff_eq_zero hη hn])

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.TimeRegularity ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma tsupport_movingBoxVelocity_subset (a b : Space) (c d : ℝ → Space) {η : ℝ}
    (hη : 0 < η) (t : ℝ) :
    tsupport (movingBoxVelocity a b c d η t) ⊆
      closedEnlargement (lowerEndpoint a c d t) (lowerEndpoint b c d t) (2 * η) :=
  tsupport_localizedAffine_subset _ _ _ _ _ hη

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Loading ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set

lemma loadingSwitch_nonneg (t : ℝ) : 0 ≤ loadingSwitch t :=
  Real.smoothTransition.nonneg _

lemma loadingSwitch_le_one (t : ℝ) : loadingSwitch t ≤ 1 :=
  Real.smoothTransition.le_one _

lemma loadingPath_eq (z : Space) (t : ℝ) (i : Fin 3) :
    loadingPath z t i = (1 - loadingSwitch t) * fixedLabel i + loadingSwitch t * z i := by
  dsimp [loadingPath, affinePath, loadingCenter]
  ring

lemma loadingPath_between (z : Space) (t : ℝ) (i : Fin 3) :
    min (fixedLabel i) (z i) ≤ loadingPath z t i ∧
      loadingPath z t i ≤ max (fixedLabel i) (z i) := by
  rw [loadingPath_eq]
  have h₀ := loadingSwitch_nonneg t
  have h₁ := loadingSwitch_le_one t
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr (min_le_left (fixedLabel i) (z i)))
        (sub_nonneg.mpr h₁),
      mul_nonneg (sub_nonneg.mpr (min_le_right (fixedLabel i) (z i))) h₀]
  · nlinarith [mul_nonneg (sub_nonneg.mpr (le_max_left (fixedLabel i) (z i)))
        (sub_nonneg.mpr h₁),
      mul_nonneg (sub_nonneg.mpr (le_max_right (fixedLabel i) (z i))) h₀]

lemma loadingVelocity_supported (z : Space) {η : ℝ} (hη : 0 < η) :
    SpatiallySupported (loadingSupport z η) (loadingVelocity z η) := by
  intro t x hx
  apply image_eq_zero_of_notMem_tsupport
  intro ht
  apply hx
  have hh := tsupport_movingBoxVelocity_subset fixedLabel fixedLabel
      (loadingCenter z) (fun _ => 1) hη t ht
  unfold loadingSupport
  rw [mem_closedEnlargement] at hh ⊢
  intro i
  have hbound := loadingPath_between z t i
  have hpoint : lowerEndpoint fixedLabel (loadingCenter z) (fun _ => 1) t = loadingPath z t := rfl
  rw [hpoint] at hh
  constructor <;> linarith [(hh i).1, (hh i).2]

end BalancedTransport.Geometry
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry
open scoped Topology
open Filter Set


theorem solution : type_of% @_root_.OAI.BalancedTransport.Geometry.loadingVelocity_supported := @_root_.OAI.BalancedTransport.Geometry.loadingVelocity_supported
