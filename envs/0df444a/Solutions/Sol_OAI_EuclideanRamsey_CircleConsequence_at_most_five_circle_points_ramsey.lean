-- Prove2me | solution 1 for OAI.EuclideanRamsey.CircleConsequence.at_most_five_circle_points_ramsey
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:56:00.048256+00:00
-- url     : https://prove2.me/submissions/40363c6d-58f6-4d7d-9858-bb5717a84ba0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Circle.lean:L19-L34
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.EuclideanRamsey.CircleConsequence.at_most_five_circle_points_ramsey.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_EuclideanRamsey_CircleConsequence_at_most_five_circle_points_ramsey) verbatim and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleExtension
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Quadratic__EuclideanRamseyCircle
import Theorems.Thm_OAI_EuclideanRamsey_CircleConsequence_circle_five_affineSpan
import Theorems.Thm_OAI_EuclideanRamsey_CircleConsequence_circle_five_rows_independent
import Theorems.Thm_OAI_EuclideanRamsey_CircleConsequence_extend_to_five
import Theorems.Thm_OAI_EuclideanRamsey_spherical_quadraticIndependent_ramsey

-- ---- from OAI.Combinatorics.EuclideanRamsey.CircleGeometry ----
namespace OAI

noncomputable section
namespace EuclideanRamsey.CircleConsequence

/-- Restriction of a Ramsey configuration preserves its distances. -/
theorem ramsey_restrict {s t d : ℕ} (a : Fin t → Space d)
    (f : Fin s → Fin t) (ha : Ramsey a) : Ramsey (a ∘ f) := by
  intro r hr
  obtain ⟨D, hD, h⟩ := ha r hr
  refine ⟨D, hD, ?_⟩
  intro c
  obtain ⟨b, hb, k, hk⟩ := h c
  exact ⟨b ∘ f, fun i j => hb (f i) (f j), k, fun i => hk (f i)⟩

/-- A circle of zero radius is a singleton; repeated labels are allowed. -/
theorem zero_radius_ramsey {s : ℕ} (a : Fin s → Space 2)
    (c : Space 2) (h : ∀ i, dist (a i) c = 0) : Ramsey a := by
  intro r hr
  refine ⟨1, by omega, ?_⟩
  intro coloring
  refine ⟨fun _ => 0, ?_, coloring 0, fun _ => rfl⟩
  intro i j
  have hi : a i = c := dist_eq_zero.mp (h i)
  have hj : a j = c := dist_eq_zero.mp (h j)
  simp [hi, hj]

end EuclideanRamsey.CircleConsequence

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.Circle ----
namespace OAI

noncomputable section
namespace EuclideanRamsey.CircleConsequence

/-- Every five-point subset of a circle is Ramsey. -/
theorem five_circle_points_ramsey (a : Fin 5 → Space 2)
    (ha : Function.Injective a) (c : Space 2) (r : ℝ)
    (hc : ∀ i, dist (a i) c = r) : Ramsey a := by
  exact spherical_quadraticIndependent_ramsey a (by decide) ha
    (circle_five_affineSpan a ha c r hc) ⟨c, r, hc⟩
    (circle_five_rows_independent a ha c r hc)

/-- Every nonempty set of at most five distinct circle points is Ramsey,
including singletons and zero-radius circles. -/
theorem at_most_five_circle_points_ramsey {s : ℕ} (a : Fin s → Space 2)
    (hs : 0 < s) (hs5 : s ≤ 5) (ha : Function.Injective a)
    (hsphere : ∃ c : Space 2, ∃ r : ℝ, ∀ i, dist (a i) c = r) : Ramsey a := by
  obtain ⟨c, r, hc⟩ := hsphere
  have hr : 0 ≤ r := by
    rw [← hc ⟨0, hs⟩]
    exact dist_nonneg
  by_cases hr0 : r = 0
  · exact zero_radius_ramsey a c (by simpa [hr0] using hc)
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    obtain ⟨b, hb, hbc, f, hf⟩ := extend_to_five a hs5 ha c r hrpos hc
    have hramsey := ramsey_restrict b f (five_circle_points_ramsey b hb c r hbc)
    have he : b ∘ f = a := funext hf
    rwa [he] at hramsey

end EuclideanRamsey.CircleConsequence

end

end OAI

-- ---- mission target ----
open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.CircleConsequence

namespace OAI
namespace EuclideanRamsey
namespace CircleConsequence
theorem _root_.solution {s : ℕ} (a : Fin s → Space 2)
    (hs : 0 < s) (hs5 : s ≤ 5) (ha : Function.Injective a)
    (hsphere : ∃ c : Space 2, ∃ r : ℝ, ∀ i, dist (a i) c = r) : Ramsey a := by
  first
    | exact OAI.EuclideanRamsey.CircleConsequence.at_most_five_circle_points_ramsey a hs hs5 ha hsphere
    | exact OAI.EuclideanRamsey.CircleConsequence.at_most_five_circle_points_ramsey
    | (apply OAI.EuclideanRamsey.CircleConsequence.at_most_five_circle_points_ramsey <;> assumption)
    | (intros; apply OAI.EuclideanRamsey.CircleConsequence.at_most_five_circle_points_ramsey <;> assumption)
end CircleConsequence
end EuclideanRamsey
end OAI
