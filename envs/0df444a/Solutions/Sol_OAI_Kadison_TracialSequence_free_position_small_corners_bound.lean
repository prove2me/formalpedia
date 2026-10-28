-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.free_position_small_corners_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T15:43:28.668793+00:00
-- url     : https://prove2.me/submissions/b8741493-d1b4-4807-b957-601bd20869b3

import Mathlib
import Definitions.Def_OAIQ039C072
import Theorems.Thm_OAI_Kadison_TracialSequence_compressed_commutes_of_range
import Theorems.Thm_OAI_Kadison_TracialSequence_double_compression_preserves_small
import Theorems.Thm_OAI_Kadison_TracialSequence_represented_corner_bound
import Theorems.Thm_OAI_Kadison_TracialSequence_subalgebra_tracial
import Theorems.Thm_OAI_Kadison_VectorGNS_free_original_bound_represented

section
-- module Solutions.OAIQ039_CM.Commutator_TracialFreeOriginal
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

open Filter

namespace Kadison.TracialSequence

open FreeWordTensor FreeWordAction FreeMoments FreeBlocks

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
  (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ)≤atTop)

variable (M : VonNeumannAlgebra (boundedSubspace τ ω))
  (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
    Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
  (hone : τ 1=1)
  (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M)

variable (D : VonNeumannAlgebra (boundedSubspace τ ω))
  (hDM : D.toStarSubalgebra≤M.toStarSubalgebra)

variable (R : Bool → StarSubalgebra ℂ M)
  (hR : R false=(VectorGNS.inclusion M D hDM).range)
  (hP : ∀ a : A,constantHom τ ω M hconst a∈R true)
  (hfree : Free R (subalgebraState τ ω hτ M hM hone).functional.toLinearMap)
  (hgen : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
    Set.centralizer (Set.centralizer (((iSup R).map M.toStarSubalgebra.subtype) : Set _)))

variable (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)] [∀ n,Nonempty (I n)]
  (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)
  (inc : ∀ {n m : ℕ},n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (hinc : ∀ n m (h : n ≤ m) a,φ m (inc h a)=φ n a)
  (hsize : ∀ n q : ℕ,∃ m,n ≤ m ∧ q ≤ Fintype.card (I m))

variable (hDgen : VectorGNS.GeneratedByStages D (sequenceVacuum τ ω) I φ)

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (Q : VonNeumannAlgebra K) (j : Q →⋆ₐ[ℂ] A)
  (hDQ : ∀ d : D,(d:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
    Set.range ((leftRestricted τ ω).comp (mapSequence j)))

include hτ hω hM hone hconst hR hP hfree hgen hinc hsize hDgen hDQ in
theorem _root_.solution
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections D)
    (T : τ.GNS →L[ℂ] τ.GNS)
    (hTQ : ∀ q : Q,T*τ.gnsStarAlgHom (j q)=τ.gnsStarAlgHom (j q)*T)
    {b c β : ℝ} (hb : 0≤b) (hc : 0 ≤ c) (hβ : 0<β) (hβ1 : β≤1) (hβb : β<b)
    (hTC : ∀ q : Q,IsStarProjection q → (τ (j q)).re≤b →
      ∀ a : A,j q*a*j q=a → ‖T*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*T‖ ≤ c*‖a‖)
    (s : unitary A) (hs0 : τ (s:A)=0) (hs2 : (s:A)*(s:A)=1) :
    ‖T*τ.gnsStarAlgHom (s:A)-τ.gnsStarAlgHom (s:A)*T‖≤1040*c := by
  refine VectorGNS.free_original_bound_represented M (sequenceVacuum τ ω)
    (subalgebra_tracial τ ω hτ hω M hM)
    (subalgebra_faithful τ ω hτ M hM) (subalgebra_normalized τ ω M hone)
    D hDM R hR hfree hgen I φ inc hinc hsize hDgen hdiffuse
    τ (constantHom τ ω M hconst) (constant_trace τ ω M hconst) hP
    (compressed τ ω T) T ?_
    (fun d => compressed_commutes_of_range τ ω Q j T hTQ d (hDQ d))
    s hs0 hs2 hc hβ hβ1
    ?_
  · with_reducible exact double_compression_preserves_small τ ω M hconst hτ hM hone T
  · exact represented_corner_bound τ ω hτ hω M hM D Q j hDQ T hb hc hβb hTC

end Kadison.TracialSequence

end

end
end

end OAI
end

