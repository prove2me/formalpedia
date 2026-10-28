-- Prove2me | solution 1 for OAI.Kadison.CyclicSpatial.exists_cyclic_intertwiner
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:21:47.384015+00:00
-- url     : https://prove2.me/submissions/2bfd2a1d-acfb-4ba1-af32-24495ba49030

import Mathlib
import Definitions.Def_OAIQ039C017
import Definitions.Def_OAIQ039C031
import Definitions.Def_OAIQ039C034
import Theorems.Thm_OAI_Kadison_CyclicColumns_cyclic_matrix_bound
import Theorems.Thm_OAI_Kadison_CyclicSpatial_matrixRepresentation_norm_eq
import Theorems.Thm_OAI_Kadison_WOTDistance_exists_commutant_approximation

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

end Kadison.ReducingRepresentation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicSpatialImplementation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.CyclicSpatial

open OperatorAmplification CyclicColumns ReducingRepresentation

variable {A H ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι]

attribute [local instance] OAI.Kadison.CyclicSpatial.instDecidableEq_solutions
variable (lam : A →⋆ₐ[ℂ] (H →L[ℂ] H))
  (K : Submodule ℂ H) [CompleteSpace K]
  (hinv : ∀ (a : A) (x : H), x∈K → lam a x∈K)

lemma delta_derivation (G : K →L[ℂ] H) (a b : A) :
    delta lam K hinv G (a*b)=(delta lam K hinv G a).comp (restrict lam K hinv b)+
      (lam a).comp (delta lam K hinv G b) := by
  ext x
  simp only [delta_apply,map_mul,_root_.sub_apply,_root_.add_apply,
    ContinuousLinearMap.comp_apply,mul_apply_eq_comp,map_sub]
  abel

omit [CompleteSpace H] in
lemma projection_tuple_norm_le (x : SumSpace (H:=H) ι) :
    ‖WithLp.toLp 2 (fun i => K.orthogonalProjectionOnto (x i))‖≤‖x‖ := by
  have hh : ‖WithLp.toLp 2 (fun i => K.orthogonalProjectionOnto (x i))‖^2≤‖x‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _)
      (K.norm_orthogonalProjectionOnto_apply_le (x i)) 2)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hh

lemma extension_matrix_commutator (G : K →L[ℂ] H) (X : CStarMatrix ι ι A)
    (x : SumSpace (H:=H) ι) :
    (diagonal (H:=H) ι (extendZero (K:=K) G)*matrixRepresentation lam X-
      matrixRepresentation lam X*diagonal (H:=H) ι (extendZero (K:=K) G)) x =
    matrixAction (fun i j => delta lam K hinv G (X i j))
      (WithLp.toLp 2 (fun i => K.orthogonalProjectionOnto (x i))) := by
  ext i
  simp only [_root_.sub_apply,mul_apply_eq_comp,PiLp.sub_apply,diagonal_apply,
    represented_matrix_apply,matrixAction_apply,extendZero,ContinuousLinearMap.comp_apply,
    map_sum,delta_apply,Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [project_intertwines lam K hinv]

lemma extension_matrix_norm_bound
    (G : K →L[ℂ] H) (Ω : K)
    (hΩ : DenseRange (fun a : A => restrict lam K hinv a Ω))
    {c : ℝ} (hc : 0 ≤ c)
    (hcol : ∀ (v : ι → A) (ζ : K),
      ‖WithLp.toLp 2 (fun i => delta lam K hinv G (v i) ζ)‖ ≤ c*columnNorm v*‖ζ‖)
    (X : CStarMatrix ι ι A) :
    ‖diagonal (H:=H) ι (extendZero (K:=K) G)*matrixRepresentation lam X-
      matrixRepresentation lam X*diagonal (H:=H) ι (extendZero (K:=K) G)‖≤4*c*‖X‖ := by
  have hcb := cyclic_matrix_bound (restrict lam K hinv) lam (delta lam K hinv G)
    (delta_derivation lam K hinv G) Ω hΩ c hc hcol X
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [extension_matrix_commutator lam K hinv]
  calc
    _ ≤ ‖matrixAction (fun i j => delta lam K hinv G (X i j))‖*
        ‖WithLp.toLp 2 (fun i => K.orthogonalProjectionOnto (x i))‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (4*c*‖X‖)*‖x‖ := mul_le_mul hcb (projection_tuple_norm_le K x)
      (norm_nonneg _) (by positivity)

theorem extension_amplified_bound (M : VonNeumannAlgebra H)
    (hlam : Function.Injective lam) (hrange : Set.range lam=(M : Set (H →L[ℂ] H)))
    (G : K →L[ℂ] H) (Ω : K)
    (hΩ : DenseRange (fun a : A => restrict lam K hinv a Ω))
    {c : ℝ} (hc : 0 ≤ c)
    (hcol : ∀ (n : ℕ) (v : Fin n → A) (ζ : K),
      ‖WithLp.toLp 2 (fun i => delta lam K hinv G (v i) ζ)‖ ≤ c*columnNorm v*‖ζ‖) :
    WOTDistance.AmplifiedBound M (extendZero (K:=K) G) (4*c) := by
  classical
  intro n T hT
  have hex : ∀ i j,∃ a : A,lam a=entry (Fin n) T i j := by
    intro i j
    change entry (Fin n) T i j∈Set.range lam
    rw [hrange]
    exact hT i j
  choose a ha using hex
  let X : CStarMatrix (Fin n) (Fin n) A := CStarMatrix.ofMatrix a
  have hX : matrixRepresentation lam X=T := by
    rw [←reconstruct (Fin n) T]
    change matrixAction (fun i j => lam (X i j)) = matrixAction (entry (Fin n) T)
    congr 1
    funext i j
    exact ha i j
  have hcb := extension_matrix_norm_bound lam K hinv G Ω hΩ hc (hcol n) X
  rw [←matrixRepresentation_norm_eq lam hlam X,hX] at hcb
  exact hcb

omit [PartialOrder A] [StarOrderedRing A] [CompleteSpace H] in
lemma restriction_distance_bound (G : K →L[ℂ] H) (T : H →L[ℂ] H)
    {c : ℝ} (hc : 0 ≤ c) (hn : ‖extendZero (K:=K) G-T‖ ≤ c) :
    ‖G-T.comp K.subtypeL‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  have he : (G-T.comp K.subtypeL) x=(extendZero (K:=K) G-T) (x:H) := by
    change G x-T (x:H)=extendZero (K:=K) G (x:H)-T (x:H)
    rw [extendZero_subtype]
  rw [he]
  exact ((extendZero (K:=K) G-T).le_opNorm (x:H)).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

theorem exists_cyclic_intertwiner_oai (M : VonNeumannAlgebra H)
    (hlam : Function.Injective lam) (hrange : Set.range lam=(M : Set (H →L[ℂ] H)))
    (G : K →L[ℂ] H) (Ω : K)
    (hΩ : DenseRange (fun a : A => restrict lam K hinv a Ω))
    {c : ℝ} (hc : 0 ≤ c)
    (hcol : ∀ (n : ℕ) (v : Fin n → A) (ζ : K),
      ‖WithLp.toLp 2 (fun i => delta lam K hinv G (v i) ζ)‖ ≤ c*columnNorm v*‖ζ‖) :
    ∃ T : K →L[ℂ] H, (∀ a : A,T.comp (restrict lam K hinv a)=(lam a).comp T) ∧
      ‖G-T‖≤4*c := by
  obtain ⟨T,hT,hn⟩ := WOTDistance.exists_commutant_approximation M
    (extendZero (K:=K) G) (by positivity)
    (extension_amplified_bound lam K hinv M hlam hrange G Ω hΩ hc hcol)
  refine ⟨T.comp K.subtypeL,?_,?_⟩
  · intro a
    ext x
    have ha : lam a∈M := by
      change lam a ∈ (M : Set (H →L[ℂ] H))
      rw [←hrange]
      exact Set.mem_range_self a
    have he := (VonNeumannAlgebra.mem_commutant_iff.mp hT) (lam a) ha
    exact (congrArg (fun R : H →L[ℂ] H => R (x:H)) he).symm
  · exact restriction_distance_bound K G T (by positivity) hn

end Kadison.CyclicSpatial

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.CyclicSpatial.exists_cyclic_intertwiner_oai.{u_1, u_2} := @OAI.Kadison.CyclicSpatial.exists_cyclic_intertwiner_oai.{u_1, u_2}
