-- Prove2me | solution 1 for OAI.Kadison.IntertwinerCompression.seminorm_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:12:30.088366+00:00
-- url     : https://prove2.me/submissions/eb8a63d1-27cb-445a-8a77-862377caa18d

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C012
import Definitions.Def_OAIQ039C018
import Definitions.Def_OAIQ039C022

section
-- module Solutions.OAIQ039_CM.Commutator_IntertwinerCompression
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
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

namespace Kadison.IntertwinerCompression

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable {A : Type*} [CStarAlgebra A]

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))

variable (T : H →L[ℂ] G) (hT : ∀ a,T.comp (φ a)=(ψ a).comp T)

include hT

lemma adjoint_intertwines (a : A) : T.adjoint.comp (ψ a)=(φ a).comp T.adjoint := by
  have h := congrArg (fun U : H →L[ℂ] G => U.adjoint) (hT (star a))
  simpa only [adjoint_comp,map_star,star_eq_adjoint,adjoint_adjoint] using h.symm

lemma transfer_left (Y : H →L[ℂ] H) (a : A) :
    transfer T (φ a*Y)=ψ a*transfer T Y := by
  simp only [transfer,mul_def,←comp_assoc]
  rw [hT a]

lemma transfer_right (Y : H →L[ℂ] H) (a : A) :
    transfer T (Y*φ a)=transfer T Y*ψ a := by
  simp only [transfer,mul_def,comp_assoc]
  rw [adjoint_intertwines φ ψ T hT]

omit hT

lemma transfer_sub (Y Z : H →L[ℂ] H) : transfer T (Y-Z)=transfer T Y-transfer T Z := by
  simp only [transfer,comp_sub,sub_comp]

lemma transfer_norm_le (hcon : ‖T‖≤1) (Y : H →L[ℂ] H) : ‖transfer T Y‖≤‖Y‖ := by
  calc
    _≤‖T‖*(‖Y‖*‖T.adjoint‖) := (opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
    _≤1*(‖Y‖*1) := mul_le_mul hcon
      (mul_le_mul_of_nonneg_left (by simpa only [adjoint.norm_map] using hcon) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _=‖Y‖ := by ring

include hT

lemma transfer_commutator (Y : H →L[ℂ] H) (a : A) :
    transfer T (Y*φ a-φ a*Y)=transfer T Y*ψ a-ψ a*transfer T Y := by
  rw [transfer_sub,transfer_left φ ψ T hT,transfer_right φ ψ T hT]

lemma transfer_commutator_norm_le (hcon : ‖T‖≤1) (Y : H →L[ℂ] H) (a : A) :
    ‖transfer T Y*ψ a-ψ a*transfer T Y‖≤‖Y*φ a-φ a*Y‖ := by
  rw [←transfer_commutator φ ψ T hT]
  exact transfer_norm_le T hcon _

end Kadison.IntertwinerCompression

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_IntertwinerSeminorm
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
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

namespace Kadison.IntertwinerCompression

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

lemma seminorm_le_of_ball (Q : VonNeumannAlgebra G) (Z : G →L[ℂ] G) (δ : ℝ)
    (hball : ∀ b∈Q,‖b‖≤1 → ‖Z*b-b*Z‖≤δ) : commutatorSeminorm Q Z≤δ := by
  apply csSup_le
  · exact ⟨0,0,Q.zero_mem,by simp,by simp⟩
  rintro r ⟨b,hb,hbn,rfl⟩
  exact hball b hb hbn

lemma faithful_norm (M : VonNeumannAlgebra H)
    (ψ : M →⋆ₐ[ℂ] (G →L[ℂ] G)) (hinj : Function.Injective ψ) (a : M) : ‖ψ a‖=‖a‖ :=
  NonUnitalStarAlgHom.norm_map ψ.toNonUnitalStarAlgHom hinj a

lemma seminorm_le_oai (M : VonNeumannAlgebra H) (Q : VonNeumannAlgebra G)
    (ψ : M →⋆ₐ[ℂ] (G →L[ℂ] G)) (hinj : Function.Injective ψ)
    (hrange : ∀ b∈Q,∃ a : M,ψ a=b)
    (T : H →L[ℂ] G) (hcon : ‖T‖≤1)
    (hT : ∀ a : M,T.comp (a:H →L[ℂ] H)=(ψ a).comp T) (Y : H →L[ℂ] H) :
    commutatorSeminorm Q (transfer T Y) ≤ commutatorSeminorm M Y := by
  apply seminorm_le_of_ball
  intro b hb hbn
  obtain ⟨a,rfl⟩ := hrange b hb
  have han : ‖(a:H →L[ℂ] H)‖≤1 := by
    change ‖a‖≤1
    have hn : ‖ψ a‖=‖a‖ := faithful_norm M ψ hinj a
    rwa [hn] at hbn
  exact (transfer_commutator_norm_le (A:=M) (H:=H) (G:=G) M.toStarSubalgebra.subtype ψ T hT hcon Y a).trans
    (commutator_bound_unitball M Y a.property han)

end Kadison.IntertwinerCompression

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.IntertwinerCompression.seminorm_le_oai.{u_1, u_2} := @OAI.Kadison.IntertwinerCompression.seminorm_le_oai.{u_1, u_2}
