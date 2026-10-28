-- Prove2me | solution 1 for OAI.Kadison.NormalRepresentation.exists_countable_gns_embedding
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:42:08.127015+00:00
-- url     : https://prove2.me/submissions/49158bbf-e442-413d-b457-cd5384ba558b

import Mathlib
import Definitions.Def_OAIQ039C062
import Theorems.Thm_OAI_Kadison_NormalGNS_separable_gns
import Theorems.Thm_OAI_Kadison_NormalRepresentation_exists_orthogonal_links_of_faithful
import Theorems.Thm_OAI_Kadison_NormalRepresentation_link_intertwines

section
-- module Solutions.OAIQ039_CM.Commutator_CountableOrthogonal
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

namespace Kadison

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [TopologicalSpace.SeparableSpace H]

lemma countable_of_orthonormal_vectors (v : ι → H) (hn : ∀ i,‖v i‖=1)
    (ho : Pairwise (fun i j => inner ℂ (v i) (v j)=0)) : Countable ι := by
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (v i) (1/3:ℝ)) (Metric.ball (v j) (1/3:ℝ))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hsq := norm_sub_sq (𝕜:=ℂ) (v i) (v j)
    rw [hn,hn,ho hij] at hsq
    have hdist : dist (v i) (v j)<2/3 := by
      have hx' : dist (v i) x<1/3 := by simpa only [Metric.mem_ball,dist_comm] using hx
      have hy' : dist x (v j)<1/3 := hy
      linarith [dist_triangle (v i) x (v j)]
    rw [dist_eq_norm] at hdist
    norm_num at hsq
    nlinarith [norm_nonneg (v i-v j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨v i,Metric.mem_ball_self (by norm_num)⟩)

variable [CompleteSpace H]

namespace PartialIsometryOrder

variable (M : VonNeumannAlgebra H) (e f : H →L[ℂ] H)

variable (S : Set (Link M e f)) (hS : OrthogonalLinks M e f S)

include hS

lemma nonzero_links_countable : Countable {v : S // v.val.val≠0} := by
  classical
  let I := {v : S // v.val.val≠0}
  have he (v : I) : ∃ x : H,v.val.val.val x≠0 := by
    by_contra h
    apply v.property
    ext x
    exact not_not.mp (fun hx => h ⟨x,hx⟩)
  choose x hx using he
  let w (v : I) : H := (‖v.val.val.val (x v)‖:ℂ)⁻¹ • v.val.val.val (x v)
  apply countable_of_orthonormal_vectors w
  · intro v
    simp only [w,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hx v))
  · intro v u hvu
    have hne : v.val.val≠u.val.val := fun h => hvu (Subtype.ext (Subtype.ext h))
    have ho := hS v.val.property u.val.property hne
    have hi : inner ℂ (v.val.val.val (x v)) (u.val.val.val (x u))=0 := by
      rw [←ContinuousLinearMap.adjoint_inner_right]
      have hz := congrArg (fun T : H →L[ℂ] H => T (x u)) ho
      change v.val.val.val.adjoint (u.val.val.val (x u))=0 at hz
      rw [hz,inner_zero_right]
    simp only [w,inner_smul_left,inner_smul_right,hi,mul_zero]

lemma links_countable : Countable S := by
  classical
  let : Countable {v : S // v.val.val≠0} := nonzero_links_countable M e f S hS
  let : Subsingleton {v : S // ¬v.val.val≠0} := ⟨by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    apply Link.ext
    exact (not_not.mp a.property).trans (not_not.mp b.property).symm⟩
  exact (Equiv.sumCompl (fun v : S => v.val.val≠0)).symm.injective.countable

end PartialIsometryOrder

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CountableGNSColumn
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped Topology InnerProductSpace ComplexOrder

universe u

namespace Kadison.NormalRepresentation

open HilbertBiprod PartialIsometryOrder BiprodLinkColumn

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma embedding_of_links {G : Type u} {A : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace G]
    (algebra : VonNeumannAlgebra (Space H G))
    (first : A → (H →L[ℂ] H)) (second : A → (G →L[ℂ] G))
    (links : ∃ family : Set (Intertwiner algebra),
      OrthogonalLinks algebra right left family ∧
        (familySpace algebra right left family).starProjection=left)
    (intertwines : ∀ (link : Intertwiner algebra) (element : A),
      (component algebra link).comp (first element)=
        (second element).comp (component algebra link)) :
    ∃ ι : Type u, Countable ι ∧ ∃ embedding : H →ₗᵢ[ℂ] lp (fun _ : ι => G) 2,
      ∀ (element : A) (vector : H) (index : ι),
        embedding (first element vector) index=second element (embedding vector index) := by
  obtain ⟨family,orthogonal,spans⟩ := links
  let embedding := infiniteColumn algebra family orthogonal spans
  refine ⟨family,links_countable algebra right left family orthogonal,embedding,?_⟩
  intro element vector index
  exact congrArg (fun operator : H →L[ℂ] G => operator vector)
    (intertwines index.val element)

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

theorem exists_countable_gns_embedding_oai [TopologicalSpace.SeparableSpace H]
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) :
    ∃ ι : Type u, Countable ι ∧ ∃ V : H →ₗᵢ[ℂ] lp (fun _ : ι => τ.GNS) 2,
      ∀ (a : M) (x : H) (i : ι),V (a.val x) i=τ.gnsStarAlgHom a (V x i) := by
  let : TopologicalSpace.SeparableSpace τ.GNS := NormalGNS.separable_gns M τ hnormal
  exact embedding_of_links (H:=H) (G:=τ.GNS) (A:=M)
    (diagonalAlgebra M τ hnormal).commutant (fun element => element.val) τ.gnsStarAlgHom
    (exists_orthogonal_links_of_faithful (H:=H) M τ hnormal hfaith)
    (link_intertwines M τ hnormal)

end Kadison.NormalRepresentation

end

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.Kadison.NormalRepresentation.exists_countable_gns_embedding_oai.{u} := @OAI.Kadison.NormalRepresentation.exists_countable_gns_embedding_oai.{u}
