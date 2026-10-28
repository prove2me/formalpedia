-- Prove2me | solution 1 for OAI.Kadison.MatrixCornerExtension.extend_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:45:15.291985+00:00
-- url     : https://prove2.me/submissions/24313cea-ee73-4c4a-964f-b853b54e2a99

import Mathlib
import Definitions.Def_OAIQ039C038

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry15
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap

namespace Kadison.ActualHilbertSum

variable {ι H : Type*} (E : ι → Type*)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)]

variable (U : ∀ i, E i →ₗᵢ[ℂ] H)

variable (hU : IsHilbertSum ℂ E U)

lemma project_coordinates (i : ι) (x : H) :
    project E U i x = hU.linearIsometryEquiv x i := by
  classical
  apply ext_inner_left ℂ
  intro y
  rw [project, adjoint_inner_right]
  change inner ℂ (U i y) x = _
  rw [← hU.linearIsometryEquiv_symm_apply_single y]
  have := hU.linearIsometryEquiv.symm.inner_map_map
    (lp.single 2 i y) (hU.linearIsometryEquiv x)
  simpa only [LinearIsometryEquiv.symm_apply_apply, lp.inner_single_left] using this

include hU in
lemma ext_vectors {x y : H} (h : ∀ i, project E U i x=project E U i y) : x=y := by
  apply hU.linearIsometryEquiv.injective
  ext i
  simpa only [project_coordinates E U hU] using h i

end Kadison.ActualHilbertSum
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertModuleExtension
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ENNReal

open ContinuousLinearMap

namespace Kadison.HilbertModuleExtension

variable {ι E F K H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (V : ι → E →ₗᵢ[ℂ] K) (W : ι → F →ₗᵢ[ℂ] H)
  (hV : IsHilbertSum ℂ (fun _ : ι => E) V) (hW : IsHilbertSum ℂ (fun _ : ι => F) W)

lemma project_extend (T : E →L[ℂ] F) (i : ι) (x : K) :
    ActualHilbertSum.project (fun _ : ι => F) W i (extend V W hV hW T x) =
      T (ActualHilbertSum.project (fun _ : ι => E) V i x) := by
  rw [ActualHilbertSum.project_coordinates _ W hW,ActualHilbertSum.project_coordinates _ V hV]
  change (hW.linearIsometryEquiv (hW.linearIsometryEquiv.symm _)) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma extend_intertwines (T : E →L[ℂ] F) (a : K →L[ℂ] K) (b : H →L[ℂ] H)
    (h : ∀ i j x,
      T (ActualHilbertSum.project (fun _ : ι => E) V i (a (V j x))) =
      ActualHilbertSum.project (fun _ : ι => F) W i (b (W j (T x)))) :
    (extend V W hV hW T).comp a=b.comp (extend V W hV hW T) := by
  apply ActualHilbertSum.map_ext (fun _ : ι => E) V hV
  intro j
  ext x
  apply ActualHilbertSum.ext_vectors (fun _ : ι => F) W hW
  intro i
  change ActualHilbertSum.project _ W i (extend V W hV hW T (a (V j x))) =
    ActualHilbertSum.project _ W i (b (extend V W hV hW T (V j x)))
  rw [project_extend,extend_insert]
  exact h i j x

end Kadison.HilbertModuleExtension

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixCornerHilbert
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.MatrixCornerHilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (p : H →L[ℂ] H) (v : ι → H →L[ℂ] H)
  (hcol : ∀ i j, star (v i)*v j=if i=j then p else 0)
  (hinit : ∀ i, p*star (v i)=star (v i))
  (htotal : ∑ i, v i*star (v i)=1)

include hinit in
omit [Fintype ι] in
lemma matrixInsert_adjoint (i : ι) (x : H) :
    (((matrixInsert p v hcol i).toContinuousLinearMap.adjoint x : fixedSpace p) : H)=
      (star (v i)) x := by
  have he : (matrixInsert p v hcol i).toContinuousLinearMap.adjoint x=
      (⟨(star (v i)) x,adjoint_mem_fixed p v hinit i x⟩ : fixedSpace p) := by
    apply ext_inner_left ℂ
    intro y
    rw [adjoint_inner_right]
    change inner ℂ (v i (y:H)) x=inner ℂ (y:H) ((v i).adjoint x)
    rw [adjoint_inner_right]
  exact congrArg (fun y : fixedSpace p => (y:H)) he

end Kadison.MatrixCornerHilbert

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixCornerExtension
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.MatrixCornerExtension

open MatrixCornerHilbert

variable {A K H ι : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι]

variable (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

variable {p : A} (hp : IsStarProjection p) (v : ι → A)
  (hcol : ∀ i j, star (v i)*v j=if i=j then p else 0)
  (hinit : ∀ i, p*star (v i)=star (v i))
  (htotal : ∑ i, v i*star (v i)=1)

include hinit in
omit [Fintype ι] in
lemma columns_project (i : ι) (x : K) :
    (ActualHilbertSum.project (fun _ : ι => fixedSpace (σ p)) (columns σ v hcol) i x : K)=
      (star (σ (v i))) x :=
  matrixInsert_adjoint (σ p) (fun i => σ (v i)) (mapped_col σ v hcol)
    (mapped_init σ v hinit) i x

omit [Fintype ι] in
lemma columns_block (i j : ι) (a : A) (x : fixedSpace (σ p)) :
    ActualHilbertSum.project (fun _ : ι => fixedSpace (σ p)) (columns σ v hcol) i
      (σ a (columns σ v hcol j x)) =
      ReducingRepresentation.corner σ hp (entry hp v hinit i j a) x := by
  apply Subtype.ext
  rw [columns_project σ v hcol hinit]
  change star (σ (v i)) (σ a (σ (v j) x))=σ (star (v i)*a*v j) x
  simp only [map_mul,map_star,mul_apply_eq_comp]

lemma extend_intertwines_oai (T : fixedSpace (σ p) →L[ℂ] fixedSpace (ρ p))
    (hT : ∀ a : Corner hp, T.comp (ReducingRepresentation.corner σ hp a)=
      (ReducingRepresentation.corner ρ hp a).comp T) (a : A) :
    (extend σ ρ v hcol hinit htotal T).comp (σ a)=
      (ρ a).comp (extend σ ρ v hcol hinit htotal T) := by
  apply HilbertModuleExtension.extend_intertwines
  intro i j x
  rw [columns_block σ hp v hcol hinit,columns_block ρ hp v hcol hinit]
  exact congrArg (fun R : fixedSpace (σ p) →L[ℂ] fixedSpace (ρ p) => R x)
    (hT (entry hp v hinit i j a))

end Kadison.MatrixCornerExtension

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Kadison.MatrixCornerExtension.extend_intertwines_oai.{u_1, u_2, u_3, u_4} := @OAI.Kadison.MatrixCornerExtension.extend_intertwines_oai.{u_1, u_2, u_3, u_4}
