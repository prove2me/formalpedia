-- Prove2me | solution 1 for OAI.Kadison.VectorGNS.free_original_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:21:08.095934+00:00
-- url     : https://prove2.me/submissions/dc698a8f-1647-47db-b941-707185cccb16

import Mathlib
import Definitions.Def_OAIQ039C064
import Definitions.Def_OAIQ039C065
import Definitions.Def_OAIQ039C070
import Theorems.Thm_OAI_Kadison_FreeBlocks_normal_free_original_bound
import Theorems.Thm_OAI_Kadison_VectorGNS_factorTrace_generated
import Theorems.Thm_OAI_Kadison_VectorGNS_factorTrace_inclusion_normal
import Theorems.Thm_OAI_Kadison_VectorGNS_gns_generation

section
-- module Solutions.OAIQ039_CM.Commutator_GNSVectorEmbedding
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

open UniformSpace ContinuousLinearMap

namespace Kadison.VectorGNS

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (τ : A →ₚ[ℂ] ℂ) (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
  (hτ : ∀ a,τ a=inner ℂ ξ (φ a ξ))

lemma intertwines (a : A) :
    (embedding τ φ ξ hτ).toContinuousLinearMap.comp (τ.gnsStarAlgHom a)=
      (φ a).comp (embedding τ φ ξ hτ).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  refine (TracialGNS.algebraVector_dense τ).induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  have hl : τ.gnsStarAlgHom a (TracialGNS.algebraVector τ b)=
      TracialGNS.algebraVector τ (a*b) := TracialGNS.left_coe τ a b
  simp only [comp_apply,LinearIsometry.coe_toContinuousLinearMap,hl,embedding_coe,
    map_mul,mul_apply_eq_comp]

lemma adjoint_intertwines (a : A) :
    (τ.gnsStarAlgHom a).comp (embedding τ φ ξ hτ).toContinuousLinearMap.adjoint=
      (embedding τ φ ξ hτ).toContinuousLinearMap.adjoint.comp (φ a) := by
  have he := congrArg (fun T : τ.GNS →L[ℂ] H => T.adjoint) (intertwines τ φ ξ hτ (star a))
  simpa only [adjoint_comp,map_star,star_eq_adjoint,adjoint_adjoint] using he

lemma compression_commutator (T : H →L[ℂ] H) (a : A) :
    compression τ φ ξ hτ T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*compression τ φ ξ hτ T=
      compression τ φ ξ hτ (T*φ a-φ a*T) := by
  simp only [compression,FreeCorner.compress,mul_def,comp_sub,sub_comp]
  congr 1
  · simp only [comp_assoc]
    rw [intertwines τ φ ξ hτ a]
  · simp only [←comp_assoc]
    rw [adjoint_intertwines τ φ ξ hτ a]

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_GNSCornerTransport
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

open scoped InnerProductSpace ComplexOrder

open ContinuousLinearMap

namespace Kadison.VectorGNS

open FreeWordTensor FreeMoments FreeWordAction FreeBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (ξ : H)

variable (htr : ∀ a b : M,subalgebraTrace M ξ (a*b)=subalgebraTrace M ξ (b*a))
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)

variable {D : Type} [CStarAlgebra D] (f : D →⋆ₐ[ℂ] M)
  (R : Bool → StarSubalgebra ℂ M)

lemma commutes (T : H →L[ℂ] H) (a : M)
    (ha : T*(a:H →L[ℂ] H)=(a:H →L[ℂ] H)*T) :
    compression (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ (subalgebraTrace_subtype M ξ) T*
      (subalgebraTrace M ξ).gnsStarAlgHom a=
    (subalgebraTrace M ξ).gnsStarAlgHom a*
      compression (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ (subalgebraTrace_subtype M ξ) T := by
  apply sub_eq_zero.mp
  refine (compression_commutator (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ
    (subalgebraTrace_subtype M ξ) T a).trans ?_
  change compression (subalgebraTrace M ξ) M.toStarSubalgebra.subtype ξ (subalgebraTrace_subtype M ξ)
    (T*(a:H →L[ℂ] H)-(a:H →L[ℂ] H)*T)=0
  rw [ha,sub_self]
  simp only [compression,FreeCorner.compress,comp_zero,zero_comp]

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_VectorFreeOriginalBound
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.VectorGNS

open FreeWordTensor FreeWordAction FreeMoments FreeBlocks

variable {H B : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable (M : VonNeumannAlgebra H) (ξ : H)
  (htr : ∀ a b : M,subalgebraTrace M ξ (a*b)=subalgebraTrace M ξ (b*a))
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)

variable (D : VonNeumannAlgebra H) (hDM : D.toStarSubalgebra≤M.toStarSubalgebra)
  (R : Bool → StarSubalgebra ℂ M) (hR : R false=(inclusion M D hDM).range)
  (hfree : Free R (subalgebraTrace M ξ).toLinearMap)
  (hgen : ∀ a : M,(a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer
    (((iSup R).map M.toStarSubalgebra.subtype) : Set (H →L[ℂ] H))))

variable (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)] [∀ n,Nonempty (I n)]
  (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)
  (inc : ∀ {n m : ℕ},n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (hinc : ∀ n m (h : n ≤ m) a,φ m (inc h a)=φ n a)
  (hsize : ∀ n q : ℕ,∃ m,n ≤ m ∧ q ≤ Fintype.card (I m))
  (hDgen : GeneratedByStages D ξ I φ)

include htr hR hfree hgen hinc hsize hDgen in
theorem free_original_bound_oai
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections D)
    (τ : B →ₚ[ℂ] ℂ) (j : B →⋆ₐ[ℂ] M) (htrace : ∀ a,τ a=subalgebraTrace M ξ (j a))
    (hj : ∀ a : B,j a∈R true)
    (U : H →L[ℂ] H) (T : τ.GNS →L[ℂ] τ.GNS)
    (hGT : ∀ x,subalgebraCompression M ξ U
      (originalEmbedding τ (vectorState M ξ hfaith hone) j htrace x)=
      originalEmbedding τ (vectorState M ξ hfaith hone) j htrace (T x))
    (hGD : ∀ d : D,U*(d:H →L[ℂ] H)=(d:H →L[ℂ] H)*U)
    (s : unitary B) (hs0 : τ (s:B)=0) (hs2 : (s:B)*(s:B)=1)
    {c β : ℝ} (hc : 0 ≤ c) (hβ : 0<β) (hβ1 : β≤1)
    (hC : CornerCommutatorBound M ξ hfaith hone (inclusion M D hDM) R U c (β:ℂ)) :
    ‖T*τ.gnsStarAlgHom (s:B)-τ.gnsStarAlgHom (s:B)*T‖≤1040*c :=
  normal_free_original_bound D (vectorState M ξ hfaith hone) htr
    (inclusion M D hDM) (inclusion_injective M D hDM) R hR hfree
    (gns_generation M ξ hfaith hone R hgen) I φ inc hinc hsize
    (factorTrace_generated D ξ I φ M hfaith hone hDM hDgen)
    (factorTrace_inclusion_normal M ξ hfaith hone D hDM) hdiffuse
    τ j htrace hj (subalgebraCompression M ξ U) T hGT (fun d => commutes M ξ U (inclusion M D hDM d) (hGD d)) s hs0 hs2 c β hc hβ hβ1 hC

end Kadison.VectorGNS

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.VectorGNS.free_original_bound_oai.{u_1} := @OAI.Kadison.VectorGNS.free_original_bound_oai.{u_1}
