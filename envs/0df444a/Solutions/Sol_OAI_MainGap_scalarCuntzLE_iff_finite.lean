-- Prove2me | solution 1 for OAI.MainGap.scalarCuntzLE_iff_finite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:23:14.830401+00:00
-- url     : https://prove2.me/submissions/a7141360-f4cc-4efa-a4b2-505c035e8284

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/IdealDetection.lean:L124-L145
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.scalarCuntzLE_iff_finite. The node keeps its source
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
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Ultrafilter
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Avoidance
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Graph
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Nonvanishing
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Compression
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Shrinking
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Products
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Separation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealDetection

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Comparison ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

attribute [local instance] OAI.MainGap.positivityOrder
attribute [local instance] OAI.MainGap.positivityStarOrder
lemma finiteCuntzLE_iff_closure {m n : ℕ} (d : CStarMatrix (Fin n) (Fin n) A)
    (v : CStarMatrix (Fin m) (Fin m) A) :
    FiniteCuntzLE d v ↔ d ∈ closure (Set.range
      (fun r : CStarMatrix (Fin m) (Fin n) A => r.conjTranspose * v * r)) := by
  rw [mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨_, fun j => ⟨r j, rfl⟩, hr⟩
  · rintro ⟨x, hx, ht⟩
    choose r hr using hx
    exact ⟨r, by simpa only [hr] using ht⟩

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.IdealDetection ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.idealDetectionOrder
attribute [local instance] OAI.MainGap.idealDetectionStarOrder
lemma scalarCuntzLE_iff_finite (u v : A) :
    ScalarCuntzLE u v ↔ FiniteCuntzLE (scalarCorner u) (scalarCorner v) := by
  let E : A ≃⋆ₐ[ℂ] CStarMatrix (Fin 1) (Fin 1) A :=
    CStarMatrix.toOneByOne (Fin 1) ℂ A
  have hc : Continuous E := (StarAlgEquiv.isometry E).continuous
  have hci : Continuous E.symm := (StarAlgEquiv.isometry E.symm).continuous
  rw [finiteCuntzLE_iff_closure]
  change u ∈ closure (Set.range (fun w : A => star w * v * w)) ↔
    E u ∈ closure (Set.range (fun w : CStarMatrix (Fin 1) (Fin 1) A =>
      star w * E v * w))
  constructor
  · intro h
    apply closure_mono (s := E '' Set.range (fun w : A => star w * v * w)) _
      (image_closure_subset_closure_image hc ⟨u, h, rfl⟩)
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨E w, by simp [map_star]⟩
  · intro h
    have hh := image_closure_subset_closure_image hci ⟨E u, h, rfl⟩
    simp only [StarAlgEquiv.symm_apply_apply] at hh
    apply closure_mono (s := E.symm '' Set.range (fun w => star w * E v * w)) _ hh
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨E.symm w, by simp [map_star]⟩

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.idealDetectionOrder
attribute [local instance] OAI.MainGap.idealDetectionStarOrder


theorem solution : type_of% @_root_.OAI.MainGap.scalarCuntzLE_iff_finite := @_root_.OAI.MainGap.scalarCuntzLE_iff_finite
