-- Prove2me | solution 1 for OAI.MainGap.unitization_Her
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:12:16.947045+00:00
-- url     : https://prove2.me/submissions/d3e341b9-d357-4aa0-b7b1-800d40855188

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Shrinking.lean:L158-L173
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.unitization_Her. The node keeps its source
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

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Hereditary ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

namespace RegularTransport
variable {h v : A} (T : RegularTransport h v)

end RegularTransport

section Order
variable [PartialOrder A] [StarOrderedRing A]

lemma mul_star_mem_Her (h : A) : h * star h ∈ Her h := by
  apply (isClosed_Her h).mem_of_tendsto
    (((CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left h).mul_const (star h))
  exact Filter.Eventually.of_forall (sandwich_mem_Her h)

end Order

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Shrinking ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
universe u v
variable {A : Type u} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.shrinkingPartialOrder
attribute [local instance] OAI.MainGap.shrinkingStarOrderedRing
attribute [local instance] OAI.MainGap.shrinkingOperatorPartialOrder
attribute [local instance] OAI.MainGap.shrinkingOperatorStarOrderedRing
end MainGap

namespace MainGap
variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.shrinkingHerPartialOrder
attribute [local instance] OAI.MainGap.shrinkingHerStarOrderedRing
attribute [local instance] OAI.MainGap.shrinkingHerUnitizationPartialOrder
attribute [local instance] OAI.MainGap.shrinkingHerUnitizationStarOrderedRing
lemma unitization_Her {a : A} {z : Unitization ℂ A}
    (hz : z ∈ Her (a : Unitization ℂ A)) : z.fst=0 ∧ z.snd ∈ Her a := by
  have hc : IsClosed {z : Unitization ℂ A | z.fst=0 ∧ z.snd ∈ Her a} :=
    (isClosed_eq Unitization.continuous_fst continuous_const).inter
      ((isClosed_Her a).preimage Unitization.continuous_snd)
  apply closure_minimal (s := Set.range (fun b : Unitization ℂ A =>
    (a : Unitization ℂ A)*b*star (a : Unitization ℂ A))) _ hc hz
  rintro z ⟨b,rfl⟩
  constructor
  · simp
  · change ((a : Unitization ℂ A)*b*star (a : Unitization ℂ A)).snd ∈ Her a
    have he : ((a : Unitization ℂ A)*b*star (a : Unitization ℂ A)).snd =
        b.fst • (a*star a) + a*b.snd*star a := by
      simp [Unitization.snd_mul, Unitization.fst_mul, add_mul, smul_mul_assoc]
    rw [he]
    exact (Her a).add_mem ((Her a).smul_mem b.fst (mul_star_mem_Her a)) (sandwich_mem_Her a b.snd)

end MainGap

namespace MainGap
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.shrinkingNonunitalPartialOrder
attribute [local instance] OAI.MainGap.shrinkingNonunitalStarOrderedRing
attribute [local instance] OAI.MainGap.shrinkingNonunitalUnitizationPartialOrder
attribute [local instance] OAI.MainGap.shrinkingNonunitalUnitizationStarOrderedRing
end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.shrinkingHerPartialOrder
attribute [local instance] OAI.MainGap.shrinkingHerStarOrderedRing
attribute [local instance] OAI.MainGap.shrinkingHerUnitizationPartialOrder
attribute [local instance] OAI.MainGap.shrinkingHerUnitizationStarOrderedRing


theorem solution : type_of% @_root_.OAI.MainGap.unitization_Her := @_root_.OAI.MainGap.unitization_Her
