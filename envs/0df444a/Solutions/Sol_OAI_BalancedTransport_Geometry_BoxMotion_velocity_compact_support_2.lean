-- Prove2me | solution 2 for OAI.BalancedTransport.Geometry.BoxMotion.velocity_compact_support
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:51:41.199179+00:00
-- url     : https://prove2.me/submissions/85d7b84d-73a2-41f5-8051-1dc3b554c9be

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/MotionField.lean:L231-L251
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Geometry.BoxMotion.velocity_compact_support. The node keeps its source
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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Deformation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryMotion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryCalculus
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderSimulation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineHalting
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Bridge
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MotionField

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

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.CompactFamilies ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*} [Fintype ι]

lemma tsupport_familyVelocity_subset (a b : ι → Space) (c d : ι → ℝ → Space)
    {η : ℝ} (hη : 0 < η) (t : ℝ) :
    tsupport (familyVelocity a b c d η t) ⊆
      ⋃ i, closedEnlargement (lowerEndpoint (a i) (c i) (d i) t)
        (lowerEndpoint (b i) (c i) (d i) t) (2 * η) := by
  apply closure_minimal _ (isClosed_iUnion_of_finite (fun _ => isCompact_Icc.isClosed))
  intro x hx
  by_contra hn
  apply hx
  apply Finset.sum_eq_zero
  intro i _
  apply image_eq_zero_of_notMem_tsupport
  intro hi
  exact hn (mem_iUnion.mpr ⟨i,
    tsupport_movingBoxVelocity_subset (a i) (b i) (c i) (d i) hη t hi⟩)

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Motion ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Geometry.BoxLayout
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Geometry.BoxLayout
end

noncomputable section
namespace BalancedTransport.Geometry
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Geometry.BoxMotion
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]
variable {A B C : BoxLayout ι} {safe : Set ι} {η : ℝ}

lemma positive_start (m : BoxMotion A B safe η) : A.Positive := by
  have hh := m.positive 0
  rwa [m.start_width 0 le_rfl] at hh

end BalancedTransport.Geometry.BoxMotion
end

noncomputable section
namespace BalancedTransport.Geometry
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.MotionField ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry.BoxLayout
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

end BalancedTransport.Geometry.BoxLayout
end

noncomputable section
namespace BalancedTransport.Geometry.BoxMotion
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]
variable {A B : BoxLayout ι} {safe : Set ι} {η : ℝ}

lemma lowerEndpoint_eq (m : BoxMotion A B safe η) (i : ι) (t : ℝ) :
    lowerEndpoint (-A.width i) (m.fieldCenter i) (m.fieldScale i) t =
      m.center (2 * t - 1 / 2) i - m.width (2 * t - 1 / 2) i := by
  ext k
  dsimp [lowerEndpoint, fieldCenter, fieldScale]
  field_simp [(m.positive_start i k).ne']
  ring

lemma upperEndpoint_eq (m : BoxMotion A B safe η) (i : ι) (t : ℝ) :
    lowerEndpoint (A.width i) (m.fieldCenter i) (m.fieldScale i) t =
      m.center (2 * t - 1 / 2) i + m.width (2 * t - 1 / 2) i := by
  ext k
  dsimp [lowerEndpoint, fieldCenter, fieldScale]
  rw [div_mul_cancel₀ _ (m.positive_start i k).ne']

lemma bounded_geometry (m : BoxMotion A B safe η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t i k,
      |m.center t i k| ≤ C ∧ |m.width t i k| ≤ C := by
  obtain ⟨Cc, hc⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    m.smooth_center.continuous.continuousOn
  obtain ⟨Cw, hw⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    m.smooth_width.continuous.continuousOn
  have hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i k,
      |m.center t i k| ≤ max 0 (max Cc Cw) ∧
      |m.width t i k| ≤ max 0 (max Cc Cw) := by
    intro t ht i k
    constructor
    · exact (norm_le_pi_norm (m.center t i) k).trans
        ((norm_le_pi_norm (m.center t) i).trans ((hc t ht).trans
          ((le_max_left _ _).trans (le_max_right _ _))))
    · exact (norm_le_pi_norm (m.width t i) k).trans
        ((norm_le_pi_norm (m.width t) i).trans ((hw t ht).trans
          ((le_max_right _ _).trans (le_max_right _ _))))
  refine ⟨max 0 (max Cc Cw), le_max_left _ _, fun t i k => ?_⟩
  by_cases ht : t ≤ 0
  · simpa only [m.start_center t ht, m.start_width t ht,
      m.start_center 0 le_rfl, m.start_width 0 le_rfl] using hh 0 ⟨le_rfl, by norm_num⟩ i k
  · by_cases ht' : 1 ≤ t
    · simpa only [m.end_center t ht', m.end_width t ht',
        m.end_center 1 le_rfl, m.end_width 1 le_rfl] using hh 1 ⟨by norm_num, le_rfl⟩ i k
    · exact hh t ⟨le_of_not_ge ht, le_of_not_ge ht'⟩ i k

lemma velocity_compact_support (m : BoxMotion A B safe η) (hη : 0 < η) :
    ∃ K : Set Space, IsCompact K ∧ SpatiallySupported K m.velocity := by
  obtain ⟨C, hC, hb⟩ := m.bounded_geometry
  let K : Set Space := Icc (fun _ => -(2 * C + 2 * η)) (fun _ => 2 * C + 2 * η)
  refine ⟨K, isCompact_Icc, fun t x hx => image_eq_zero_of_notMem_tsupport ?_⟩
  intro ht
  obtain ⟨i, hi⟩ := mem_iUnion.mp (tsupport_familyVelocity_subset
    (fun i => -A.width i) A.width m.fieldCenter m.fieldScale hη t ht)
  rw [m.lowerEndpoint_eq, m.upperEndpoint_eq, mem_closedEnlargement] at hi
  apply hx
  constructor <;> intro k
  · have hh := hi k
    have hbc := (abs_le.mp (hb (2 * t - 1 / 2) i k).1).1
    have hbw := (abs_le.mp (hb (2 * t - 1 / 2) i k).2).2
    dsimp at hh ⊢
    linarith [hh.1]
  · have hh := hi k
    have hbc := (abs_le.mp (hb (2 * t - 1 / 2) i k).1).2
    have hbw := (abs_le.mp (hb (2 * t - 1 / 2) i k).2).2
    dsimp at hh ⊢
    linarith [hh.2]

end BalancedTransport.Geometry.BoxMotion
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry OAI.BalancedTransport.Geometry.BoxMotion
open Set Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BalancedTransport.Geometry.BoxMotion.velocity_compact_support := @_root_.OAI.BalancedTransport.Geometry.BoxMotion.velocity_compact_support
