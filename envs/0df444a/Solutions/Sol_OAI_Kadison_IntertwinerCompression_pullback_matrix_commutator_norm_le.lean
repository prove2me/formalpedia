-- Prove2me | solution 1 for OAI.Kadison.IntertwinerCompression.pullback_matrix_commutator_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:16:34.959918+00:00
-- url     : https://prove2.me/submissions/e9ad3f1a-6ea7-4e4d-a4e7-d8761638e23e

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C007
import Definitions.Def_OAIQ039C008
import Definitions.Def_OAIQ039C012
import Definitions.Def_OAIQ039C020

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertFiniteMaps
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology

namespace Kadison.HilbertFiniteMaps

variable {H G K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (ι : Type*) [Fintype ι]

omit [CompleteSpace H] [CompleteSpace G] in
lemma amplify_norm_le (T : H →L[ℂ] G) : ‖amplify ι T‖≤‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have hs : ‖amplify ι T x‖^2≤(‖T‖*‖x‖)^2 := by
    rw [PiLp.norm_sq_eq_of_L2,mul_pow,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => by
      rw [amplify_apply,←mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm (x i)) 2)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T) (norm_nonneg x))).mp hs

omit [CompleteSpace H] [CompleteSpace G] [CompleteSpace K] in
lemma amplify_comp (T : H →L[ℂ] G) (U : G →L[ℂ] K) :
    amplify ι (U.comp T)=(amplify ι U).comp (amplify ι T) := by ext x i; rfl

lemma amplify_adjoint (T : H →L[ℂ] G) : amplify ι T.adjoint=(amplify ι T).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply,amplify_apply,ContinuousLinearMap.adjoint_inner_left]

end Kadison.HilbertFiniteMaps

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_IntertwinerCompression
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

include hT

lemma amplify_intertwines (h : ℕ) (X : Matrix (Fin h) (Fin h) A) :
    (HilbertFiniteMaps.amplify (Fin h) T).comp (matrixOperator h (fun i j => φ (X i j)))=
      (matrixOperator h (fun i j => ψ (X i j))).comp (HilbertFiniteMaps.amplify (Fin h) T) := by
  ext x i
  change T (matrixOperator h (fun i j => φ (X i j)) x i)=
    matrixOperator h (fun i j => ψ (X i j)) (HilbertFiniteMaps.amplify (Fin h) T x) i
  rw [@Kadison.matrixOperator_apply H _ _ h (fun i j => φ (X i j)) x i,
    @Kadison.matrixOperator_apply G _ _ h (fun i j => ψ (X i j)) (HilbertFiniteMaps.amplify (Fin h) T x) i,
    map_sum]
  simp only [HilbertFiniteMaps.amplify_apply]
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun U : H →L[ℂ] G => U (x j)) (hT (X i j))

omit hT

lemma amplify_transfer (h : ℕ) (Y : H →L[ℂ] H) :
    diagonalAmplification h (transfer T Y)=
      transfer (HilbertFiniteMaps.amplify (Fin h) T) (diagonalAmplification h Y) := by
  change HilbertFiniteMaps.amplify (Fin h) (transfer T Y)=_
  rw [transfer,HilbertFiniteMaps.amplify_comp,HilbertFiniteMaps.amplify_comp,
    HilbertFiniteMaps.amplify_adjoint]
  rfl

end Kadison.IntertwinerCompression

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_IntertwinerMatrixTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

open ContinuousLinearMap

namespace Kadison.IntertwinerCompression

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

lemma transfer_raw_commutator (T : H →L[ℂ] G) (A : H →L[ℂ] H) (B : G →L[ℂ] G)
    (hleft : T.comp A=B.comp T) (hright : T.adjoint.comp B=A.comp T.adjoint)
    (Y : H →L[ℂ] H) :
    transfer T (Y*A-A*Y)=transfer T Y*B-B*transfer T Y := by
  have hl : transfer T (A*Y)=B*transfer T Y := by
    simp only [transfer,mul_def,←comp_assoc]
    rw [hleft]
  have hr : transfer T (Y*A)=transfer T Y*B := by
    simp only [transfer,mul_def,comp_assoc]
    rw [hright]
  rw [transfer_sub,hl,hr]

lemma transfer_raw_commutator_norm_le (T : H →L[ℂ] G) (hcon : ‖T‖≤1)
    (A : H →L[ℂ] H) (B : G →L[ℂ] G)
    (hleft : T.comp A=B.comp T) (hright : T.adjoint.comp B=A.comp T.adjoint)
    (Y : H →L[ℂ] H) :
    ‖transfer T Y*B-B*transfer T Y‖≤‖Y*A-A*Y‖ := by
  rw [←transfer_raw_commutator T A B hleft hright]
  exact transfer_norm_le T hcon _

variable {A : Type*} [CStarAlgebra A]

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))

variable (T : H →L[ℂ] G) (hT : ∀ a,T.comp (φ a)=(ψ a).comp T)

include hT

lemma pullback_matrix_commutator_norm_le_oai (hcon : ‖T‖≤1) (h : ℕ)
    (X : Matrix (Fin h) (Fin h) A) (Z : G →L[ℂ] G) :
    ‖diagonalAmplification h (transfer T.adjoint Z)*matrixOperator h (fun i j => φ (X i j))-
      matrixOperator h (fun i j => φ (X i j))*diagonalAmplification h (transfer T.adjoint Z)‖≤
    ‖diagonalAmplification h Z*matrixOperator h (fun i j => ψ (X i j))-
      matrixOperator h (fun i j => ψ (X i j))*diagonalAmplification h Z‖ := by
  rw [amplify_transfer]
  apply transfer_raw_commutator_norm_le
  · exact (HilbertFiniteMaps.amplify_norm_le _ _).trans (by simpa only [adjoint.norm_map] using hcon)
  · exact amplify_intertwines ψ φ T.adjoint (adjoint_intertwines φ ψ T hT) h X
  · rw [←HilbertFiniteMaps.amplify_adjoint,adjoint_adjoint]
    exact amplify_intertwines φ ψ T hT h X

end Kadison.IntertwinerCompression

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.IntertwinerCompression.pullback_matrix_commutator_norm_le_oai.{u_1, u_2, u_3} := @OAI.Kadison.IntertwinerCompression.pullback_matrix_commutator_norm_le_oai.{u_1, u_2, u_3}
