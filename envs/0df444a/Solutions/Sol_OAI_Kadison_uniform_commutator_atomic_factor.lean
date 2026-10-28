-- Prove2me | solution 1 for OAI.Kadison.uniform_commutator_atomic_factor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:10:36.770032+00:00
-- url     : https://prove2.me/submissions/9bbba119-2c31-4e0b-a3b9-a7bfbcdf927a

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C000
import Definitions.Def_OAIQ039C030
import Theorems.Thm_OAI_Kadison_AtomicFactor_Decomposition_finite_dimensional
import Theorems.Thm_OAI_Kadison_AtomicFactor_Decomposition_two_isometries
import Theorems.Thm_OAI_Kadison_AtomicFactor_exists_decomposition
import Theorems.Thm_OAI_Kadison_commutatorSeminorm_nonneg
import Theorems.Thm_OAI_Kadison_uniform_commutator_finiteDimensional
import Theorems.Thm_OAI_Kadison_uniform_commutator_of_isometries

section
-- module Solutions.OAIQ039_CM.Commutator_MinimalProjection
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace AtomicFactor

lemma exists_minimal_of_not_diffuse (M : VonNeumannAlgebra H)
    (h : ¬DiffuseProjection.HasNoMinimalProjections M) :
    ∃ p,IsMinimalProjection M p := by
  simp only [DiffuseProjection.HasNoMinimalProjections,not_forall] at h
  obtain ⟨p,hpM,hp,hpn,h⟩ := h
  refine ⟨p,hpM,hp,hpn,?_⟩
  intro q hqM hq hqp
  by_cases hq0 : q=0
  · exact Or.inl hq0
  · right
    by_contra hqne
    exact h ⟨q,hqM,hq,hq0,hqne,hqp⟩

end AtomicFactor

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TwoIsometries
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

section Isometries

variable {A : Type*} [Ring A] [StarRing A] (s t : A)
    (hs : star s*s=1) (ht : star t*t=1) (hst : star s*t=0)

include hs ht hst in
lemma two_isometries_words (n m : ℕ) :
    star (s^n*t)*(s^m*t)=if n=m then 1 else 0 := by
  classical
  have hts : star t*s=0 := by
    have he := congrArg star hst
    simpa only [star_mul,star_star,star_zero] using he
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simpa using ht
    | succ m =>
      simp only [pow_zero,one_mul,pow_succ',Nat.zero_ne_add_one,ite_false]
      rw [show star t*(s*s^m*t)=(star t*s)*(s^m*t) by noncomm_ring,hts,zero_mul]
  | succ n ih =>
    cases m with
    | zero =>
      simp only [pow_zero,one_mul,pow_succ',Nat.add_one_ne_zero,ite_false,star_mul]
      rw [show star t*(star (s^n)*star s)*t=star t*star (s^n)*(star s*t) by noncomm_ring,hst,mul_zero]
    | succ m =>
      rw [pow_succ',pow_succ',star_mul,star_mul]
      rw [show star t*(star (s^n)*star s)*(s*s^m*t)=star (s^n*t)*(star s*s)*(s^m*t) by
        rw [star_mul]; noncomm_ring,hs,mul_one,ih]
      simp

include hs ht hst in
theorem two_isometries_finite_family (h : ℕ) :
    ∃ v : Fin h → A, ∀ i j, star (v i)*v j=if i=j then 1 else 0 := by
  classical
  refine ⟨fun i => s^i.val*t,?_⟩
  intro i j
  simpa only [Fin.val_inj] using two_isometries_words s t hs ht hst i.val j.val

end Isometries

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProperlyInfiniteMain
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem uniform_commutator_of_two_isometries
    (P : VonNeumannAlgebra K) (s t : P)
    (hs : star s*s=1) (ht : star t*t=1) (hst : star s*t=0)
    (Y : K →L[ℂ] K) (h : ℕ)
    (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖ ≤
      9*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  obtain ⟨v,hv⟩ := two_isometries_finite_family s t hs ht hst h
  exact uniform_commutator_of_isometries P Y h v hv X hX

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AtomicFactorMain
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem uniform_commutator_atomic_factor_oai (P : VonNeumannAlgebra H)
    (hfac : FactorCorner.IsFactor P)
    (hatom : ¬DiffuseProjection.HasNoMinimalProjections P)
    (Y : H →L[ℂ] H) (h : ℕ)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖ ≤
      9*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  obtain ⟨p,hp⟩ := AtomicFactor.exists_minimal_of_not_diffuse P hatom
  obtain ⟨D⟩ := AtomicFactor.exists_decomposition P hfac hp
  rcases finite_or_infinite D.I with hD|hD
  · let := hD
    let := D.finite_dimensional hp
    exact (uniform_commutator_finiteDimensional P Y h X hX).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ)≤9)
        (commutatorSeminorm_nonneg P Y)) (norm_nonneg _))
  · let := hD
    obtain ⟨s,t,hs,ht,hst⟩ := D.two_isometries
    exact uniform_commutator_of_two_isometries P s t hs ht hst Y h X hX

end Kadison

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.uniform_commutator_atomic_factor_oai.{u_1} := @OAI.Kadison.uniform_commutator_atomic_factor_oai.{u_1}
