-- Prove2me | solution 1 for OAI.MainGap.scalarCuntzLE_of_mem_Her
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:24:46.322361+00:00
-- url     : https://prove2.me/submissions/0c706ba3-60e4-4f8f-a44d-c2784c6f709a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/IdealDetection.lean:L157-L178
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.scalarCuntzLE_of_mem_Her. The node keeps its source
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
lemma scalarCuntzLE_of_mem_Her {u v : A} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : u ∈ Her v) : ScalarCuntzLE u v := by
  have hs := sqrt_mem_Her h hu
  have hc : Continuous (fun z : A => star z * z) := by fun_prop
  have hm := image_closure_subset_closure_image hc ⟨CFC.sqrt u, hs, rfl⟩
  simp only [(CFC.sqrt_nonneg u).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self u hu] at hm
  apply closure_mono (s := (fun z : A => star z * z) ''
      Set.range (fun w : A => v * w * star v)) _ hm
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  refine ⟨CFC.sqrt v * w * v, ?_⟩
  have hsv := (CFC.sqrt_nonneg v).isSelfAdjoint.star_eq
  have hsq := CFC.sqrt_mul_sqrt_self v hv
  simp only [star_mul, hv.isSelfAdjoint.star_eq, hsv, mul_assoc]
  have hh : CFC.sqrt v * v * CFC.sqrt v = v * v := by
    calc
      _ = CFC.sqrt v * (CFC.sqrt v * CFC.sqrt v) * CFC.sqrt v :=
        congrArg (fun t => CFC.sqrt v * t * CFC.sqrt v) hsq.symm
      _ = (CFC.sqrt v * CFC.sqrt v) * (CFC.sqrt v * CFC.sqrt v) := by noncomm_ring
      _ = v * v := by rw [hsq]
  calc
    _ = v * star w * (CFC.sqrt v * v * CFC.sqrt v) * w * v := by noncomm_ring
    _ = _ := by rw [hh]; noncomm_ring

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.idealDetectionOrder
attribute [local instance] OAI.MainGap.idealDetectionStarOrder


theorem solution : type_of% @_root_.OAI.MainGap.scalarCuntzLE_of_mem_Her := @_root_.OAI.MainGap.scalarCuntzLE_of_mem_Her
