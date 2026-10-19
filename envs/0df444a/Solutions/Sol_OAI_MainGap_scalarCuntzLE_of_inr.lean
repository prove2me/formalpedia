-- Prove2me | solution 1 for OAI.MainGap.scalarCuntzLE_of_inr
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:28:20.756279+00:00
-- url     : https://prove2.me/submissions/da29ed69-42bc-41ec-8143-754cfc777ea6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/IdealComparison.lean:L117-L158
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.scalarCuntzLE_of_inr. The node keeps its source
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
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealComparison

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.IdealComparison ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.idealComparisonPartialOrder
attribute [local instance] OAI.MainGap.idealComparisonStarOrderedRing
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.idealComparisonNonUnitalPartialOrder
attribute [local instance] OAI.MainGap.idealComparisonNonUnitalStarOrderedRing
lemma scalarCuntzLE_of_inr {u v : A} (hv : 0 ≤ v)
    (h : ScalarCuntzLE (Unitization.inr u : Unitization ℂ A) (Unitization.inr v)) :
    ScalarCuntzLE u v := by
  let V : Unitization ℂ A := Unitization.inr v
  have hc : IsClosed {z : Unitization ℂ A | ScalarCuntzLE z.snd v} :=
    isClosed_closure.preimage Unitization.continuous_snd
  apply closure_minimal (s := Set.range (fun w : Unitization ℂ A => star w * V * w)) _ hc h
  rintro _ ⟨w, rfl⟩
  change ScalarCuntzLE (star w * V * w).snd v
  let hau := CStarAlgebra.increasingApproximateUnit A
  let x := CFC.sqrt v
  have hxx : star x * x = v := by
    rw [(CFC.sqrt_nonneg v).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self v]
  have ht : Tendsto (fun e : A => star (x * e) * (x * e))
      (CStarAlgebra.approximateUnit A) (𝓝 v) := by
    simpa only [hxx] using (hau.tendsto_mul_left x).star.mul (hau.tendsto_mul_left x)
  have hti := (Unitization.continuous_inr (𝕜 := ℂ)).tendsto v |>.comp ht
  have htfinal : Tendsto
      (fun e : A => (star w * (Unitization.inr (star (x*e)*(x*e)) : Unitization ℂ A) * w).snd)
      (CStarAlgebra.approximateUnit A) (𝓝 (star w * V * w).snd) :=
    Unitization.continuous_snd.tendsto _ |>.comp (tendsto_const_nhds.mul hti |>.mul tendsto_const_nhds)
  apply isClosed_closure.mem_of_tendsto htfinal
  apply Filter.Eventually.of_forall
  intro e
  let r : A := ((Unitization.inr e : Unitization ℂ A) * w).snd
  have hr : (Unitization.inr r : Unitization ℂ A) = Unitization.inr e * w := by
    have he := Unitization.inl_fst_add_inr_snd_eq ((Unitization.inr e : Unitization ℂ A) * w)
    simpa [r] using he
  have heq : (star w * (Unitization.inr (star (x*e)*(x*e)) : Unitization ℂ A) * w).snd =
      star r * v * r := by
    apply Unitization.inr_injective (R := ℂ)
    have hs : (Unitization.inr (star r * v * r) : Unitization ℂ A) =
        star w * Unitization.inr (star (x*e)*(x*e)) * w := by
      simp only [Unitization.inr_mul, Unitization.inr_star, hr, star_mul]
      have hx := congrArg (Unitization.inr : A → Unitization ℂ A) hxx
      simp only [Unitization.inr_mul, Unitization.inr_star] at hx
      simp only [mul_assoc] at hx ⊢
      rw [← hx]
      simp only [mul_assoc]
    rw [← hs]
    rfl
  exact heq ▸ subset_closure ⟨r, rfl⟩

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.idealComparisonNonUnitalPartialOrder
attribute [local instance] OAI.MainGap.idealComparisonNonUnitalStarOrderedRing


theorem solution : type_of% @_root_.OAI.MainGap.scalarCuntzLE_of_inr := @_root_.OAI.MainGap.scalarCuntzLE_of_inr
