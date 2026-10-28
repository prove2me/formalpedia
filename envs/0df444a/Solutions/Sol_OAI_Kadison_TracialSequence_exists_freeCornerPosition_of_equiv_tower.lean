-- Prove2me | solution 1 for OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_tower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:13:47.459314+00:00
-- url     : https://prove2.me/submissions/fd30f8ee-267e-441f-82b4-3ba34c1abe3a

import Mathlib
import Definitions.Def_OAIQ039C053
import Definitions.Def_OAIQ039C067
import Definitions.Def_OAIQ039C069
import Theorems.Thm_OAI_Kadison_FinitePatching_exists_all_unitary_tests
import Theorems.Thm_OAI_Kadison_TracialSequence_constant_range_bicommutant_of_equiv
import Theorems.Thm_OAI_Kadison_TracialSequence_freeCornerPosition_of_unitary_abstract
import Theorems.Thm_OAI_Kadison_TracialSequence_pullUnitary_moment_limits
import Theorems.Thm_OAI_Kadison_TracialSequence_sequenceUnitary_free

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryEquivMoments
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

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

open FinitePatching FinitePatching.Words FinitePatching.ConjugatedWords

variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

section Relative

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H) (hRM : R≤M) (e : A ≃⋆ₐ[ℂ] M) (j : R →⋆ₐ[ℂ] A)
    (hj : ∀ q,e (j q)=NormalSubalgebra.inclusion M R hRM q)
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

include hRM hj in
lemma pullUnitary_in_relative_range (u : ℕ → unitary M)
    (hu : ∀ n,((u n:M):H →L[ℂ] H)∈R) :
    (sequenceUnitary τ ω (fun n => pullUnitary e (u n)) : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.range ((leftRestricted τ ω).comp (mapSequence j)) := by
  have he : mapSequence j (restrictBoundedUnitary M R u hu)=boundedUnitary (fun n => pullUnitary e (u n)) := by
    ext n
    apply e.injective
    change e (j ⟨u n,hu n⟩)=e (e.symm (u n))
    rw [hj,e.apply_symm_apply]
    rfl
  exact ⟨restrictBoundedUnitary M R u hu,congrArg (leftRestricted τ ω) he⟩

end Relative

end Kadison.TracialSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RelativeEquivFreePosition
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

open scoped ComplexOrder Matrix.Norms.L2Operator Topology

open Filter

namespace Kadison.TracialSequence

open FinitePatching FinitePatching.ConjugatedWords

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (M R : VonNeumannAlgebra H) (hRM : R ≤ M) (e : A ≃⋆ₐ[ℂ] M) (j : R →⋆ₐ[ℂ] A)
    (hj : ∀ q,e (j q)=NormalSubalgebra.inclusion M R hRM q)

variable (τ : A →ₚ[ℂ] ℂ) (σ : M →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (size : ℕ → ℕ)

variable (stage : ∀ n,Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ] M)

variable (inc : ∀ {n m : ℕ},n ≤ m → Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ]
  Matrix (Fin (size m+1)) (Fin (size m+1)) ℂ)

include hRM hj in
theorem exists_freeCornerPosition_of_equiv_tower_oai [TopologicalSpace.SeparableSpace σ.GNS]
    (htrace : ∀ a,σ (e a)=τ a)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hσ : ∀ a b : M,σ (a*b)=σ (b*a))
    (hω : (ω : Filter ℕ) ≤ atTop)
    (hnormal : NormalGNS.BoundedWOTContinuous M σ)
    (hfaith : ∀ a : M,σ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M,(∀ n (a : Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ),
      stage n a*b=b*stage n a) → ∃ c : ℂ,b=algebraMap ℂ M c)
    (hstage : ∀ n a,(stage n a : H →L[ℂ] H)∈R)
    (hinc : ∀ n m (h : n ≤ m) a,stage m (inc h a)=stage n a)
    (hgrow : Tendsto (fun n => (size n+1:ℝ)) atTop atTop)
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections R) :
    Nonempty (FreeCornerPosition τ ω R j) := by
  have hσone : σ 1=1 := by rw [←map_one e,htrace,hone]
  have hmono : ∀ {n m : ℕ},n ≤ m → (stage n).range ≤ (stage m).range := by
    intro n m h a ha
    obtain ⟨b,rfl⟩ := ha
    exact ⟨inc h b,hinc n m h b⟩
  obtain ⟨u,huR,_,huword⟩ := exists_all_unitary_tests M R hRM σ hσ stage hmono
    hnormal hfaith hσone hirr (by simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hgrow)
    hstage hdiffuse
  let v := fun n => pullUnitary e (u n)
  have hfree := sequenceUnitary_free τ ω hτ hω v (pullUnitary_moment_limits e τ σ htrace u (by
    intro J x hx hxc l hl hv
    exact huword J Bool x signPower hx hxc (by intro b; cases b <;> norm_num [signPower]) l hl hv))
  let stageA := fun n => e.symm.toStarAlgHom.comp (stage n)
  have hfaithA (a : A) (ha : τ (star a*a)=0) : a=0 := by
    apply (show Function.Injective e from e.injective)
    rw [map_zero]
    apply hfaith
    rw [←map_star e,←map_mul e,htrace,ha]
  have hirrA (b : A) (hb : ∀ n a,stageA n a*b=b*stageA n a) :
      ∃ c : ℂ,b=algebraMap ℂ A c := by
    obtain ⟨c,hc⟩ := hirr (e b) (by
      intro n a
      have hh := congrArg e (hb n a)
      have hsa : e (stageA n a)=stage n a := e.apply_symm_apply _
      simpa only [map_mul,hsa] using hh)
    refine ⟨c,(show Function.Injective e from e.injective) ?_⟩
    rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one]
    exact hc
  have hstageA (n : ℕ) (a : Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ) : stageA n a∈Set.range j := by
    refine ⟨⟨stage n a,hstage n a⟩,(show Function.Injective e from e.injective) ?_⟩
    rw [hj]
    change (stage n a)=e (e.symm (stage n a))
    rw [e.apply_symm_apply]
  apply freeCornerPosition_of_unitary_abstract R j τ ω size stageA inc hτ hω
    (constant_range_bicommutant_of_equiv τ ω M e σ hτ htrace hnormal) hfaithA hone hirrA hstageA
    (fun n m h a => congrArg e.symm (hinc n m h a)) _ (sequenceUnitary τ ω v)
    (pullUnitary_in_relative_range M R hRM e j hj τ ω u huR) hfree
  intro n q
  have he := (tendsto_atTop.1 hgrow) (q:ℝ)
  obtain ⟨m,hmq,hmn⟩ := (he.and (eventually_ge_atTop n)).exists
  exact ⟨m,hmn,by exact_mod_cast hmq⟩

end Kadison.TracialSequence

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_tower_oai := @OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_tower_oai
