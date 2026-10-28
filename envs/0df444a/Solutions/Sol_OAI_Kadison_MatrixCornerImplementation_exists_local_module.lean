-- Prove2me | solution 1 for OAI.Kadison.MatrixCornerImplementation.exists_local_module
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:46:21.967241+00:00
-- url     : https://prove2.me/submissions/b08c4325-d435-497a-a471-a00deb6f3b2f

import Mathlib
import Definitions.Def_OAIQ039C017
import Definitions.Def_OAIQ039C042
import Theorems.Thm_OAI_Kadison_MatrixCornerImplementation_exists_matrix_corner_intertwiner

section
-- module Solutions.OAIQ039_CM.Commutator_ModuleZeroExtension
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

namespace Kadison.ReducingRepresentation

variable {A H F : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F))

variable (K : Submodule ℂ H) [CompleteSpace K]
  (hinv : ∀ (a : A) (x : H), x∈K → σ a x∈K)

lemma project_intertwines (a : A) (x : H) :
    K.orthogonalProjectionOnto (σ a x)=restrict σ K hinv a (K.orthogonalProjectionOnto x) := by
  apply Subtype.ext
  have hm : K.starProjection*σ a=σ a*K.starProjection :=
    projection_commutes_of_invariant K (σ a) (hinv a)
      (by simpa only [←map_star] using hinv (star a))
  exact congrArg (fun T : H →L[ℂ] H => T x) hm

include hinv in
lemma extendZero_intertwines (T : K →L[ℂ] F)
    (hT : ∀ a : A, T.comp (restrict σ K hinv a)=(ρ a).comp T) (a : A) :
    (extendZero (K := K) T).comp (σ a)=(ρ a).comp (extendZero (K := K) T) := by
  ext x
  change T (K.orthogonalProjectionOnto (σ a x))=ρ a (T (K.orthogonalProjectionOnto x))
  rw [project_intertwines σ K hinv]
  exact congrArg (fun L : K →L[ℂ] F => L (K.orthogonalProjectionOnto x)) (hT a)

omit [CompleteSpace H] [CompleteSpace F] in
lemma norm_sub_extendZero_apply_le (G : H →L[ℂ] F) (T : K →L[ℂ] F)
    (δ : ℝ) (hδ : ‖G.comp K.subtypeL-T‖≤δ) (x : K) :
    ‖G (x:H)-extendZero (K := K) T (x:H)‖≤δ*‖(x:H)‖ := by
  rw [extendZero_subtype]
  exact ((G.comp K.subtypeL-T).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hδ (norm_nonneg x))

end Kadison.ReducingRepresentation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicLocalModule
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison.MatrixCornerImplementation

open ConcreteCorner ReducingRepresentation

variable {H ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι]

variable (M : VonNeumannAlgebra H)

lemma cyclic_dense (ξ : H) :
    DenseRange (fun a : Algebra M =>
      restrict (inclusion M) (cyclicSubspace M.toStarSubalgebra ξ)
        (fun a => cyclicSubspace_invariant M.toStarSubalgebra ξ a.property) a
        ⟨ξ,mem_cyclicSubspace_self M.toStarSubalgebra ξ⟩) := by
  let K := cyclicSubspace M.toStarSubalgebra ξ
  let act : Algebra M → K := fun a =>
    ⟨(a:H →L[ℂ] H) ξ,cyclicSubspace_invariant M.toStarSubalgebra ξ a.property ξ
      (mem_cyclicSubspace_self M.toStarSubalgebra ξ)⟩
  have hi : (Subtype.val : K → H) '' Set.range act =
      (orbitSubmodule M.toStarSubalgebra ξ : Set H) := by
    ext x
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      exact ⟨a,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨act ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩,rfl⟩
  intro x
  change x∈closure (Set.range act)
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,hi]
  exact x.property

theorem exists_local_module_oai {p : Algebra M} (hp : IsStarProjection p)
    (v : ι → Algebra M)
    (hcol : ∀ i j, star (v i)*v j=if i=j then p else 0)
    (hinit : ∀ i, p*star (v i)=star (v i))
    (htotal : ∑ i, v i*star (v i)=1)
    (G : H →L[ℂ] H)
    (hGp : G.comp (inclusion M p)=(inclusion M p).comp G)
    (hGv : ∀ i, G.comp (inclusion M (v i))=(inclusion M (v i)).comp G)
    (ξ : H) (hpξ : inclusion M p ξ=ξ)
    {ε : ℝ} (hε : 0≤ε)
    (hδ : ∀ a : Corner hp,
      ‖G.comp (inclusion M (a:Algebra M))-(inclusion M (a:Algebra M)).comp G‖≤ε*‖a‖) :
    ∃ T : H →L[ℂ] H,
      (∀ a : Algebra M, T.comp (inclusion M a)=(inclusion M a).comp T) ∧
      ∀ z∈cyclicSubspace M.toStarSubalgebra ξ, ‖G z-T z‖≤(16*ε)*‖z‖ := by
  let K := cyclicSubspace M.toStarSubalgebra ξ
  let hinv : ∀ (a : Algebra M) (x : H), x∈K → inclusion M a x∈K :=
    fun a => cyclicSubspace_invariant M.toStarSubalgebra ξ a.property
  let σ := restrict (inclusion M) K hinv
  let j : K →ₗᵢ[ℂ] H := K.subtypeₗᵢ
  have hj (a : Algebra M) (x : K) : j (σ a x)=inclusion M a (j x) := rfl
  have hGp' (x : K) : (G.comp K.subtypeL) (σ p x)=inclusion M p ((G.comp K.subtypeL) x) :=
    congrArg (fun F : H →L[ℂ] H => F (x:H)) hGp
  have hGv' (i : ι) (x : K) : (G.comp K.subtypeL) (σ (v i) x)=
      inclusion M (v i) ((G.comp K.subtypeL) x) :=
    congrArg (fun F : H →L[ℂ] H => F (x:H)) (hGv i)
  let Ω : K := ⟨ξ,mem_cyclicSubspace_self M.toStarSubalgebra ξ⟩
  have hδ' (a : Corner hp) :
      ‖(G.comp K.subtypeL).comp (σ (a:Algebra M))-
        (inclusion M (a:Algebra M)).comp (G.comp K.subtypeL)‖≤ε*‖a‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hε (norm_nonneg a))
    intro x
    change ‖G (inclusion M (a:Algebra M) (x:H))-inclusion M (a:Algebra M) (G (x:H))‖≤_
    exact ((G.comp (inclusion M (a:Algebra M))-(inclusion M (a:Algebra M)).comp G).le_opNorm (x:H)).trans
      (mul_le_mul_of_nonneg_right (hδ a) (norm_nonneg _))
  obtain ⟨T,hT,hn⟩ := exists_matrix_corner_intertwiner M σ j hj hp
    (G.comp K.subtypeL) hGp' v hcol hinit htotal hGv' Ω (cyclic_dense M ξ)
    (Subtype.ext hpξ) hε hδ'
  refine ⟨extendZero (K := K) T,extendZero_intertwines (inclusion M) (inclusion M) K hinv T hT,?_⟩
  intro z hz
  exact norm_sub_extendZero_apply_le K G T (16*ε) hn ⟨z,hz⟩

end Kadison.MatrixCornerImplementation

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.MatrixCornerImplementation.exists_local_module_oai.{u_1, u_2} := @OAI.Kadison.MatrixCornerImplementation.exists_local_module_oai.{u_1, u_2}
