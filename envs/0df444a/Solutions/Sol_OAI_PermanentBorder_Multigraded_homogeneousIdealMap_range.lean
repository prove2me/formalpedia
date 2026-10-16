-- Prove2me | solution 1 for OAI.PermanentBorder.Multigraded.homogeneousIdealMap_range
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:30:48.838245+00:00
-- url     : https://prove2.me/submissions/0779a25e-270b-40ad-aa50-f4df3637b355

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/LinearForms.lean:L344-L366
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Multigraded.homogeneousIdealMap_range. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Theorems.Thm_OAI_PermanentBorder_Multigraded_project_mul

-- ---- from OAI.Algebra.Determinantal.LinearForms ----
namespace OAI
namespace PermanentBorder.Multigraded
open MvPolynomial
section LinearCoefficients
variable {K σ τ : Type*} [Field K] [Fintype τ]

end LinearCoefficients

section Vandermonde
variable {K : Type*} [Field K]

end Vandermonde
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section VandermondeLeaves
variable {K ι L : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype L]

end VandermondeLeaves
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section BinaryChoices
variable {K σ G : Type*} [Field K] [AddCommGroup G]
variable (w : σ → G)

end BinaryChoices
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section MixedCoefficient
variable {ι E : Type*} [Fintype E] [DecidableEq ι]

end MixedCoefficient
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section ComparisonPieceBound
variable {K ι σ : Type*} [Field K] [DecidableEq ι]

variable [Fintype ι]

end ComparisonPieceBound
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section HomogeneousIdealMap
variable {K σ G E : Type*} [Field K] [AddCommGroup G] [Fintype E]
variable (w : σ → G) (e : E → G) (F : E → MvPolynomial σ K)
  (hF : ∀ i, (F i).IsWeightedHomogeneous w (e i))

lemma homogeneousIdealMap_val (d : G) (p : ∀ i : E, Piece (K := K) w (d-e i)) :
    (homogeneousIdealMap w e F hF d p).val = ∑ i, F i * (p i).val := by
  simp [homogeneousIdealMap]

lemma homogeneousIdealMap_range (d : G) :
    LinearMap.range (homogeneousIdealMap w e F hF d) =
      ((Ideal.span (Set.range F)).restrictScalars K).comap (Piece (K := K) w d).subtype := by
  classical
  ext p
  constructor
  · rintro ⟨g,rfl⟩
    change (homogeneousIdealMap w e F hF d g).val ∈ Ideal.span (Set.range F)
    rw [homogeneousIdealMap_val]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_span_range_self)
  · intro hp
    change p.val ∈ Ideal.span (Set.range F) at hp
    obtain ⟨g,hg⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
    let g' : ∀ i : E, Piece (K := K) w (d-e i) := fun i =>
      ⟨weightedHomogeneousComponent w (d-e i) (g i),
        weightedHomogeneousComponent_mem w (g i) (d-e i)⟩
    refine ⟨g', Subtype.ext ?_⟩
    rw [homogeneousIdealMap_val]
    change ∑ i, F i * weightedHomogeneousComponent w (d-e i) (g i) = p.val
    simp_rw [← project_mul w (hF _)]
    rw [← map_sum]
    simp_rw [mul_comm (F _) _]
    rw [hg, weightedHomogeneousComponent_eq_self p.property]

end HomogeneousIdealMap

end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
section AffineIndependent
variable {K E V : Type*} [Field K] [Fintype E]
  [AddCommGroup V] [Module K V]

end AffineIndependent
end PermanentBorder.Multigraded

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.Multigraded
open MvPolynomial


theorem solution : type_of% @_root_.OAI.PermanentBorder.Multigraded.homogeneousIdealMap_range := @_root_.OAI.PermanentBorder.Multigraded.homogeneousIdealMap_range
