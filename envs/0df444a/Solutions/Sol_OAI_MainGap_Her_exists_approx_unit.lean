-- Prove2me | solution 1 for OAI.MainGap.Her_exists_approx_unit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:09:49.574191+00:00
-- url     : https://prove2.me/submissions/74a77dc9-660b-4b11-b785-26a4824c7986

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Hereditary.lean:L439-L455
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.Her_exists_approx_unit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary

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

lemma self_mem_Her {h : A} (hh : 0 ≤ h) : h ∈ Her h := by
  have hm : h * h ∈ Her h := by
    simpa only [IsSelfAdjoint.of_nonneg hh |>.star_eq] using mul_star_mem_Her h
  simpa only [CFC.sqrt_mul_self h hh] using
    sqrt_mem_Her hm (by simpa only [IsSelfAdjoint.of_nonneg hh |>.star_eq] using
      star_mul_self_nonneg h)

lemma Her_exists_approx_unit {b : A} (hb : 0 ≤ b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ e : A, e ∈ Her b ∧ IsSelfAdjoint e ∧ ‖e‖ ≤ 1 ∧ ‖b - e * b‖ < δ := by
  let b' : Her b := ⟨b, self_mem_Her hb⟩
  let : PartialOrder (Her b) := CStarAlgebra.spectralOrder (Her b)
  let : StarOrderedRing (Her b) := CStarAlgebra.spectralOrderedRing (Her b)
  have hunit := CStarAlgebra.increasingApproximateUnit (Her b)
  have ht : Tendsto (fun e : Her b => ‖b' - e * b'‖)
      (CStarAlgebra.approximateUnit (Her b)) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds (x := b')).sub (hunit.tendsto_mul_right b')).norm
  have hsmall : ∀ᶠ e : Her b in CStarAlgebra.approximateUnit (Her b), ‖b' - e * b'‖ < δ :=
    ht.eventually (Iio_mem_nhds hδ)
  obtain ⟨e, hn, hp, hs⟩ := (hunit.eventually_norm.and (hunit.eventually_nonneg.and hsmall)).exists
  refine ⟨e, e.property, ?_, hn, hs⟩
  change star (e : A) = (e : A)
  have he := congrArg (fun x : Her b => (x : A)) (IsSelfAdjoint.of_nonneg hp |>.star_eq)
  exact he

end Order

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace


theorem solution : type_of% @_root_.OAI.MainGap.Her_exists_approx_unit := @_root_.OAI.MainGap.Her_exists_approx_unit
