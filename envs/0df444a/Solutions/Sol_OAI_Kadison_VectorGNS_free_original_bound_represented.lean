-- Prove2me | solution 1 for OAI.Kadison.VectorGNS.free_original_bound_represented
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:53:39.488386+00:00
-- url     : https://prove2.me/submissions/3d97e811-aeda-4a4f-9ca6-0107a5526464

import Mathlib
import Definitions.Def_OAIQ039C060
import Definitions.Def_OAIQ039C064
import Definitions.Def_OAIQ039C065
import Theorems.Thm_OAI_Kadison_VectorGNS_corner_bound
import Theorems.Thm_OAI_Kadison_VectorGNS_free_original_bound

section
-- module Solutions.OAIQ039_CM.Commutator_TracialGNSCorners
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

open scoped InnerProductSpace ComplexOrder BoundedContinuousFunction

open Filter ContinuousLinearMap

namespace Kadison.VectorGNS

lemma subtype_corner
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (q a : M) (hl : q*a=a) (hr : a*q=a) :
    (q:H →L[ℂ] H)*a*q=a := by
  have hh : q*a*q=a := by rw [hl,hr]
  exact congrArg M.toStarSubalgebra.subtype hh

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RepresentedCornerBound
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

open scoped InnerProductSpace ComplexOrder

namespace Kadison.VectorGNS

open FreeWordTensor FreeMoments FreeWordAction FreeBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (ξ : H)
  (htr : ∀ a b : M,subalgebraTrace M ξ (a*b)=subalgebraTrace M ξ (b*a))
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)

variable (D : VonNeumannAlgebra H) (hDM : D.toStarSubalgebra≤M.toStarSubalgebra)
  (R : Bool → StarSubalgebra ℂ M)

lemma inclusion_projection (q : D) (hq : IsStarProjection (inclusion M D hDM q)) :
    IsStarProjection (q:H →L[ℂ] H) :=
  hq.map M.toStarSubalgebra.subtype

include htr in
lemma represented_corner_bound (U : H →L[ℂ] H) (c : ℝ) (β : ℂ)
    (hb : RepresentedCornerBound M ξ D U c β) :
    CornerCommutatorBound (D:=D) M ξ hfaith hone (inclusion M D hDM) R U c β := by
  apply corner_bound M ξ htr hfaith hone (inclusion M D hDM) R U c β
  intro q hq hqt a hl hr
  exact hb q (inclusion_projection M D hDM q hq) hqt a
    (subtype_corner M (inclusion M D hDM q) a hl hr)

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
theorem free_original_bound_represented_oai
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
    (hC : RepresentedCornerBound M ξ D U c (β:ℂ)) :
    ‖T*τ.gnsStarAlgHom (s:B)-τ.gnsStarAlgHom (s:B)*T‖≤1040*c :=
  free_original_bound M ξ htr hfaith hone D hDM R hR hfree hgen I φ inc hinc
    hsize hDgen hdiffuse τ j htrace hj U T hGT hGD s hs0 hs2 hc hβ hβ1
    (represented_corner_bound M ξ htr hfaith hone D hDM R U c (β:ℂ) hC)

end Kadison.VectorGNS

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.VectorGNS.free_original_bound_represented_oai.{u_1} := @OAI.Kadison.VectorGNS.free_original_bound_represented_oai.{u_1}
