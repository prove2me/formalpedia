-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.freeCornerPosition_of_unitary_abstract
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:14:09.782514+00:00
-- url     : https://prove2.me/submissions/2b9457cd-2b09-4a7c-8613-7d42ef353afc

import Mathlib
import Definitions.Def_OAIQ039C072
import Theorems.Thm_OAI_Kadison_EquivariantBicommutant_bicommutant_range
import Theorems.Thm_OAI_Kadison_FreeMoments_Free_mono
import Theorems.Thm_OAI_Kadison_GeneratedMatrixBicommutant_factor
import Theorems.Thm_OAI_Kadison_GeneratedMatrixBicommutant_in_range
import Theorems.Thm_OAI_Kadison_GeneratedMatrixBicommutant_in_represented
import Theorems.Thm_OAI_Kadison_GeneratedMatrixBicommutant_le_vonNeumann
import Theorems.Thm_OAI_Kadison_MatrixDiffuse_noMinimal_of_matrix_stages
import Theorems.Thm_OAI_Kadison_TracialSequence_bicommutant_trace_mul
import Theorems.Thm_OAI_Kadison_VectorGNS_generatedByStages_of_represented
import Theorems.Thm_OAI_Kadison_traceFaithfulHom_injective

section
-- module Solutions.OAIQ039_CM.Commutator_AbstractFreeCornerFromUnitary
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.TracialSequence

open FinitePatching.ConjugatedWords

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (R : VonNeumannAlgebra H) (j : R →⋆ₐ[ℂ] A)

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (size : ℕ → ℕ)

variable (stage : ∀ n,Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ] A)

variable (inc : ∀ {n m : ℕ},n ≤ m → Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ]
  Matrix (Fin (size m+1)) (Fin (size m+1)) ℂ)

theorem freeCornerPosition_of_unitary_abstract_oai
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ)≤atTop)
    (hconstantclosed : Set.centralizer (Set.centralizer (Set.range (constantAction τ ω)))=
      Set.range (constantAction τ ω))
    (hfaith : ∀ a : A,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : A,(∀ n (a : Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ),
      stage n a*b=b*stage n a) → ∃ c : ℂ,b=algebraMap ℂ A c)
    (hstage : ∀ n a,stage n a∈Set.range j)
    (hinc : ∀ n m (h : n ≤ m) a,stage m (inc h a)=stage n a)
    (hsize : ∀ n q : ℕ,∃ m,n ≤ m ∧ q ≤ size m+1)
    (U : unitary (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω))
    (hu : (U:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.range ((leftRestricted τ ω).comp (mapSequence j)))
    (hfree : FreeMoments.Free (pair (A := A) (B := boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) (constantAction τ ω) U) (sequenceTrace τ ω).toLinearMap) :
    Nonempty (FreeCornerPosition τ ω R j) := by
  change Nonempty (FreeCornerPositionData (sequenceVacuum τ ω) (constantAction τ ω)
    (Set.range ((leftRestricted τ ω).comp (mapSequence j))))
  classical
  let : Algebra ℂ (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) :=
    ContinuousLinearMap.algebra
  let α : (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ≃⋆ₐ[ℂ]
      (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) :=
    (Unitary.linearIsometryEquiv U).conjStarAlgEquiv
  let φ : A →⋆ₐ[ℂ] (boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) := by
    with_reducible
      exact α.toStarAlgHom.comp (constantAction τ ω)
  let D := GeneratedMatrixBicommutant.algebra size stage φ
  let ψ := GeneratedMatrixBicommutant.stageHom size stage φ
  have hclosed : Set.centralizer (Set.centralizer (Set.range φ))=Set.range φ := by
    exact EquivariantBicommutant.bicommutant_range α.toMulEquiv (constantAction τ ω)
      hconstantclosed
  have hconstantinj : Function.Injective (constantAction τ ω) := by
    with_reducible
      refine traceFaithfulHom_injective (A := A)
        (B := boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) (constantAction τ ω)
        τ.toLinearMap (sequenceTrace τ ω).toLinearMap ?_ ?_
    · exact hfaith
    · intro a
      change sequenceTrace τ ω (leftRestricted τ ω (constantSequence a))=τ a
      exact trace_constant τ ω a
  have hφinj : Function.Injective φ := α.injective.comp hconstantinj
  have hfactor : FactorCorner.IsFactor D :=
    GeneratedMatrixBicommutant.factor size stage φ hclosed hφinj hirr
  let N := relativeUltrapower τ ω j hτ hω
  have hUN : (U:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈N := hu
  have hstageN (n : ℕ) (a : Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ) : φ (stage n a)∈N := by
    have hc : constantAction τ ω (stage n a)∈N := by
      let q := Classical.choose (hstage n a)
      have hq := Classical.choose_spec (hstage n a)
      refine ⟨constantSequence q,?_⟩
      change constantAction τ ω (j q) = constantAction τ ω (stage n a)
      exact congrArg (constantAction τ ω) hq
    change (U:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)*
      constantAction τ ω (stage n a)*star (U:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈N
    exact N.mul_mem (N.mul_mem hUN hc) (N.star_mem' hUN)
  have hDN : D≤N := GeneratedMatrixBicommutant.le_vonNeumann size stage φ N hstageN
  have hrange (a : D) : (a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.range ((leftRestricted τ ω).comp (mapSequence j)) :=
    hDN a.property
  have hnatural (a : D) : (a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))) := by
    let v := Classical.choose (hrange a)
    have hv := Classical.choose_spec (hrange a)
    exact Set.subset_centralizer_centralizer ⟨mapSequence j v,hv⟩
  have hfreeD : FreeMoments.Free (GeneratedFreePair.ambient D (constantAction τ ω))
      (sequenceTrace τ ω).toLinearMap := by
    apply hfree.mono
    intro c
    cases c with
    | false =>
      intro a ha
      exact GeneratedMatrixBicommutant.in_range size stage φ hclosed ⟨a,ha⟩
    | true => exact le_refl _
  have hdiffuse : DiffuseProjection.HasNoMinimalProjections D := by
    apply MatrixDiffuse.noMinimal_of_matrix_stages D (sequenceTrace τ ω)
      (fun a ha b hb => bicommutant_trace_mul τ ω hτ hω (hnatural ⟨a,ha⟩) (hnatural ⟨b,hb⟩))
      ((trace_one τ ω).trans hone) hfactor
      (fun a ha hz => trace_faithful τ ω hτ (hnatural ⟨a,ha⟩) hz)
      (fun n => size n+1) ψ
    intro q
    obtain ⟨m,_,hm⟩ := hsize 0 (q+1)
    exact ⟨m,by omega⟩
  refine ⟨{ algebra := D
            size := size
            stage := ψ
            inclusion := inc
            compatible := ?_
            unbounded := hsize
            generated := ?_
            free := hfreeD
            in_range := hrange
            diffuse := hdiffuse }⟩
  · intro n m h a
    apply Subtype.ext
    change φ (stage m (inc h a))=φ (stage n a)
    rw [hinc]
  · exact VectorGNS.generatedByStages_of_represented D (sequenceVacuum τ ω)
      (fun n => Fin (size n+1)) ψ (GeneratedMatrixBicommutant.in_represented size stage φ)

end Kadison.TracialSequence

end

end OAI
end

theorem solution : type_of% @OAI.Kadison.TracialSequence.freeCornerPosition_of_unitary_abstract_oai := @OAI.Kadison.TracialSequence.freeCornerPosition_of_unitary_abstract_oai
