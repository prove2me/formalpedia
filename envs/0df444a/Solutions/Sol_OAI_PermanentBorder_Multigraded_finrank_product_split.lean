-- Prove2me | solution 1 for OAI.PermanentBorder.Multigraded.finrank_product_split
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:21:56.701111+00:00
-- url     : https://prove2.me/submissions/82434d0a-45db-4fbf-847f-677bd4105397

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/Multigraded.lean:L100-L153
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Multigraded.finrank_product_split. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Theorems.Thm_OAI_PermanentBorder_Multigraded_project_mul

-- ---- from OAI.Algebra.Determinantal.Multigraded ----
namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial

variable {K σ G : Type*} [Field K] [AddCommGroup G]
variable (w : σ → G)

theorem finrank_product_split (I : Ideal (MvPolynomial σ K))
    (hI : ComponentClosed w I) {a b : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (d : G)
    [Module.Finite K (Piece (K := K) w d)]
    [Module.Finite K (Piece (K := K) w (d-e))] :
    Module.finrank K (componentQuotient w (I ⊔ Ideal.span {a*b}) d) ≤
      Module.finrank K (componentQuotient w (I ⊔ Ideal.span {a}) d) +
      Module.finrank K (componentQuotient w (I ⊔ Ideal.span {b}) (d-e)) := by
  let B := I ⊔ Ideal.span {a*b}
  let A := I ⊔ Ideal.span {a}
  let C := I ⊔ Ideal.span {b}
  have hBA : B ≤ A := by
    apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    rintro _ rfl
    exact Submodule.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  have hm : ∀ p ∈ C, a*p ∈ B := by
    intro p hp
    obtain ⟨i,hi,z,hz,rfl⟩ := Submodule.mem_sup.mp hp
    obtain ⟨g,rfl⟩ := Ideal.mem_span_singleton.mp hz
    rw [mul_add, ← mul_assoc]
    exact Ideal.add_mem _ (Submodule.mem_sup_left (I.mul_mem_left a hi))
      (Submodule.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)))
  let f := componentMap w hBA d
  let g := componentMul w ha C B hm d
  have hker : LinearMap.ker f ≤ LinearMap.range g := by
    intro x hx
    obtain ⟨p,rfl⟩ := Submodule.mkQ_surjective _ x
    change (Submodule.Quotient.mk p : componentQuotient w A d) = 0 at hx
    have hp : p.val ∈ A := (Submodule.Quotient.mk_eq_zero
      ((A.restrictScalars K).comap (Piece (K := K) w d).subtype)).mp hx
    obtain ⟨i,hi,z,hz,hp⟩ := Submodule.mem_sup.mp hp
    obtain ⟨u,rfl⟩ := Ideal.mem_span_singleton.mp hz
    let v : Piece (K := K) w (d-e) :=
      ⟨weightedHomogeneousComponent w (d-e) u, weightedHomogeneousComponent_mem w u (d-e)⟩
    refine ⟨Submodule.Quotient.mk v, ?_⟩
    change Submodule.Quotient.mk (mulPiece w ha d v) = Submodule.Quotient.mk p
    rw [Submodule.Quotient.eq]
    change a * weightedHomogeneousComponent w (d-e) u - p.val ∈ B
    have he : weightedHomogeneousComponent w d i +
        a * weightedHomogeneousComponent w (d-e) u = p.val := by
      have hh := congrArg (weightedHomogeneousComponent w d) hp
      simpa only [map_add, project_mul w ha,
        weightedHomogeneousComponent_eq_self p.property] using hh
    have hi' := hI i hi d
    have he' : a * weightedHomogeneousComponent w (d-e) u - p.val =
        -(weightedHomogeneousComponent w d i) := by rw [← he]; abel
    rw [he']
    exact Submodule.mem_sup_left (I.neg_mem hi')
  have hk := (Submodule.finrank_mono hker).trans (LinearMap.finrank_range_le g)
  have hf := Submodule.finrank_le (LinearMap.range f)
  have hr := LinearMap.finrank_range_add_finrank_ker f
  dsimp only [B,A,C] at hk hf hr
  omega

end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section Blocks
variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]

end Blocks
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section LinearLeaves
variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]

end LinearLeaves
end PermanentBorder.Multigraded

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.Multigraded
open MvPolynomial


theorem solution : type_of% @_root_.OAI.PermanentBorder.Multigraded.finrank_product_split := @_root_.OAI.PermanentBorder.Multigraded.finrank_product_split
