-- Prove2me | solution 1 for OAI.Kadison.CyclicColumns.cyclic_matrix_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:12:48.994383+00:00
-- url     : https://prove2.me/submissions/ba7f2670-d4fa-4c78-b350-89ec50e0a6f2

import Mathlib
import Definitions.Def_OAIQ039C022

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicColumnFactorization
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.CyclicColumns

variable {A H ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype ι]

theorem regularized_factorization (a : ι → A) (η : ℝ) (hη : 0 < η) :
    ∃ (b : A) (v : ι → A), star b=b ∧
      b*b=(∑ i, star (a i)*a i)+η • (1:A) ∧
      (∑ i, star (v i)*v i) ≤ 1 ∧ ∀ i, v i*b=a i := by
  let q : A := (∑ i, star (a i)*a i)+η • (1:A)
  have hp : IsStrictlyPositive q :=
    IsStrictlyPositive.nonneg_add (Finset.sum_nonneg (fun i _ => star_mul_self_nonneg (a i)))
      (isStrictlyPositive_one.smul hη)
  let b : A := CFC.sqrt q
  have hb : star b=b := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg q)).star_eq
  have hbb : b*b=q := CFC.sqrt_mul_sqrt_self q hp.nonneg
  have hu : IsUnit b := (CFC.isUnit_sqrt_iff q hp.nonneg).mpr hp.isUnit
  let c : A := Ring.inverse b
  have hcb : c*b=1 := Ring.inverse_mul_cancel b hu
  have hbc : b*c=1 := Ring.mul_inverse_cancel b hu
  have hc : star c=c := by dsimp [c]; rw [←Ring.inverse_star,hb]
  let v : ι → A := fun i => a i*c
  refine ⟨b,v,hb,hbb,?_,?_⟩
  · have hle : (∑ i,star (a i)*a i) ≤ q :=
      le_add_of_nonneg_right (smul_nonneg hη.le zero_le_one)
    have h := star_left_conjugate_le_conjugate hle c
    have hright : star c*q*c=1 := by rw [hc,←hbb,←mul_assoc,hcb,one_mul,hbc]
    rw [hright] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [v]
    simp only [star_mul,Finset.mul_sum,Finset.sum_mul,mul_assoc]
  · intro i
    dsimp only [v]
    rw [mul_assoc,hcb,mul_one]

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_image_sq (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) (Ω : H) :
    ‖σ a Ω‖^2 = (inner ℂ Ω (σ (star a*a) Ω)).re := by
  rw [map_mul,map_star,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact (inner_self_eq_norm_sq (𝕜:=ℂ) (σ a Ω)).symm

theorem regularized_vector_factorization (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Ω : H) (a : ι → A) (η : ℝ) (hη : 0 < η) :
    ∃ (ζ : H) (v : ι → A), (∑ i, star (v i)*v i) ≤ 1 ∧
      (∀ i, σ (v i) ζ=σ (a i) Ω) ∧
      ‖ζ‖^2=(∑ i, ‖σ (a i) Ω‖^2)+η*‖Ω‖^2 := by
  obtain ⟨b,v,hb,hbb,hv,hvb⟩ := regularized_factorization a η hη
  refine ⟨σ b Ω,v,hv,?_,?_⟩
  · intro i
    rw [←mul_apply_eq_comp,←map_mul,hvb]
  · rw [norm_image_sq,hb,hbb,map_add,map_sum]
    have hsmul : σ (η • (1:A))=η • (1:H →L[ℂ] H) := by
      change σ ((η:ℂ) • (1:A))=(η:ℂ) • (1:H →L[ℂ] H)
      rw [map_smul,map_one]
    rw [hsmul]
    simp only [add_apply,sum_apply,
      smul_apply,one_apply_eq_self,inner_add_right,
      inner_sum,Complex.add_re,Complex.re_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      exact (norm_image_sq σ (a i) Ω).symm
    · change (inner ℂ Ω ((η:ℂ) • Ω)).re=η*‖Ω‖^2
      rw [inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im]
      simp only [zero_mul,sub_zero]
      congr 1
      exact inner_self_eq_norm_sq (𝕜:=ℂ) Ω

theorem bounded_vector_factorization (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Ω : H) (a : ι → A) (ha : (∑ i, ‖σ (a i) Ω‖^2) ≤ 2) :
    ∃ (ζ : H) (v : ι → A), ‖ζ‖ ≤ 2 ∧ (∑ i, star (v i)*v i) ≤ 1 ∧
      ∀ i, σ (v i) ζ=σ (a i) Ω := by
  let η : ℝ := 1/(‖Ω‖^2+1)
  have ht : 0 < ‖Ω‖^2+1 := by positivity
  have hη : 0 < η := one_div_pos.mpr ht
  obtain ⟨ζ,v,hv,hva,hζ⟩ := regularized_vector_factorization σ Ω a η hη
  have hr : η*‖Ω‖^2 ≤ 1 := by
    dsimp only [η]
    rw [one_div_mul_eq_div]
    exact (div_le_one ht).mpr (by linarith)
  refine ⟨ζ,v,?_,hv,hva⟩
  have hn := norm_nonneg ζ
  nlinarith

omit [PartialOrder A] [StarOrderedRing A] [Fintype ι] in
lemma denseRange_cyclic_columns (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Ω : H) (hΩ : DenseRange (fun a : A => σ a Ω)) :
    DenseRange (fun a : ι → A => WithLp.toLp 2 (fun i => σ (a i) Ω)) := by
  have hpi : DenseRange (Pi.map (fun (_ : ι) (a : A) => σ a Ω)) :=
    DenseRange.piMap (fun _ => hΩ)
  exact (PiLp.homeomorph 2 (fun _ : ι => H)).symm.surjective.denseRange.comp hpi
    (PiLp.homeomorph 2 (fun _ : ι => H)).symm.continuous

theorem approximate_unit_column (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Ω : H) (hΩ : DenseRange (fun a : A => σ a Ω))
    (ξ : PiLp 2 (fun _ : ι => H)) (hξ : ‖ξ‖=1) (ε : ℝ) (hε : 0<ε) :
    ∃ (ζ : H) (v : ι → A), ‖ζ‖ ≤ 2 ∧ (∑ i, star (v i)*v i) ≤ 1 ∧
      ‖ξ-WithLp.toLp 2 (fun i => σ (v i) ζ)‖ < ε := by
  obtain ⟨a,ha⟩ := Metric.denseRange_iff.mp (denseRange_cyclic_columns σ Ω hΩ)
    ξ (min ε (1/4)) (lt_min hε (by norm_num))
  rw [dist_eq_norm] at ha
  have hnorm : ‖WithLp.toLp 2 (fun i => σ (a i) Ω)‖ < 5/4 := by
    have hh := norm_le_norm_add_norm_sub ξ (WithLp.toLp 2 (fun i => σ (a i) Ω))
    rw [hξ] at hh
    have ht := lt_of_lt_of_le ha (min_le_right ε (1/4))
    linarith
  have hb : (∑ i, ‖σ (a i) Ω‖^2) ≤ 2 := by
    rw [←PiLp.norm_sq_eq_of_L2 (fun _ : ι => H) (WithLp.toLp 2 (fun i => σ (a i) Ω))]
    have hn := norm_nonneg (WithLp.toLp 2 (fun i => σ (a i) Ω))
    nlinarith
  obtain ⟨ζ,v,hζ,hv,heq⟩ := bounded_vector_factorization σ Ω a hb
  refine ⟨ζ,v,hζ,hv,?_⟩
  simpa only [heq] using lt_of_lt_of_le ha (min_le_left ε (1/4))

end Kadison.CyclicColumns

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicMatrix
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.CyclicColumns

variable {A H F ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

lemma matrixRepresentation_norm_le (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (X : CStarMatrix ι ι A) :
    ‖matrixRepresentation σ X‖ ≤ ‖X‖ :=
  NonUnitalStarAlgHom.norm_apply_le (matrixRepresentation σ) X

lemma columnNorm_sq (v : ι → A) :
    columnNorm v ^ 2 = ‖∑ i, star (v i)*v i‖ := by
  rw [columnNorm,WithCStarModule.pi_norm_sq]
  simp only [WithCStarModule.equiv_symm_pi_apply,WithCStarModule.inner_def,star_star]

lemma columnNorm_nonneg (v : ι → A) : 0 ≤ columnNorm v := norm_nonneg _

lemma columnNorm_le_one (v : ι → A) (hv : (∑ i,star (v i)*v i)≤1) :
    columnNorm v ≤ 1 := by
  have hp : 0 ≤ ∑ i,star (v i)*v i := Finset.sum_nonneg (fun i _ => star_mul_self_nonneg _)
  have hn : ‖∑ i,star (v i)*v i‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hp).mpr hv
  rw [←columnNorm_sq] at hn
  nlinarith [columnNorm_nonneg v]

lemma columnNorm_matmul_le (X : CStarMatrix ι ι A) (v : ι → A) :
    columnNorm (fun i => ∑ j, X i j*v j) ≤ ‖X‖*columnNorm v := by
  let r := (WithCStarModule.equiv A (ι → A)).symm (fun i => star (v i))
  have heq : (WithCStarModule.equiv A (ι → A)).symm
      (fun i => star (∑ j, X i j*v j)) = CStarMatrix.toCLM (star X) r := by
    ext i
    simp [CStarMatrix.toCLM_apply_eq_sum,CStarMatrix.star_apply,r,star_sum,star_mul]
  dsimp only [columnNorm]
  rw [heq]
  calc ‖CStarMatrix.toCLM (star X) r‖ ≤ ‖CStarMatrix.toCLM (star X)‖*‖r‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖X‖*‖r‖ := by rw [←CStarMatrix.norm_def,norm_star]

end Kadison.CyclicColumns

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclicCb
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.CyclicColumns

variable {A H F ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

local instance cyclicCbDecidableEq_r9aeca8_1 : DecidableEq ι := Classical.decEq ι
omit [PartialOrder A] [StarOrderedRing A] in
lemma derivation_matrix_column (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (Δ : A →L[ℂ] (H →L[ℂ] F))
    (hΔ : ∀ a b, Δ (a*b)=(Δ a).comp (σ b)+(lam a).comp (Δ b))
    (X : CStarMatrix ι ι A) (v : ι → A) (ζ : H) :
    matrixAction (fun i j => Δ (X i j)) (WithLp.toLp 2 (fun i => σ (v i) ζ)) =
      WithLp.toLp 2 (fun i => Δ (∑ j, X i j*v j) ζ)-
        matrixAction (fun i j => lam (X i j)) (WithLp.toLp 2 (fun i => Δ (v i) ζ)) := by
  ext i
  simp only [matrixAction_apply,PiLp.sub_apply,map_sum,hΔ,
    sum_apply,add_apply,ContinuousLinearMap.comp_apply]
  simp only [Finset.sum_add_distrib,add_sub_cancel_right]

theorem cyclic_matrix_bound_oai (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (Δ : A →L[ℂ] (H →L[ℂ] F))
    (hΔ : ∀ a b, Δ (a*b)=(Δ a).comp (σ b)+(lam a).comp (Δ b))
    (Ω : H) (hΩ : DenseRange (fun a : A => σ a Ω)) (c : ℝ) (hc : 0 ≤ c)
    (hcol : ∀ (v : ι → A) (ζ : H),
      ‖WithLp.toLp 2 (fun i => Δ (v i) ζ)‖ ≤ c*columnNorm v*‖ζ‖)
    (X : CStarMatrix ι ι A) :
    ‖matrixAction (fun i j => Δ (X i j))‖ ≤ 4*c*‖X‖ := by
  let D := matrixAction (fun i j => Δ (X i j))
  have hbound (ζ : H) (v : ι → A) (hζ : ‖ζ‖≤2) (hv : (∑ i,star (v i)*v i)≤1) :
      ‖D (WithLp.toLp 2 (fun i => σ (v i) ζ))‖ ≤ 4*c*‖X‖ := by
    have hn : columnNorm v≤1 := columnNorm_le_one v hv
    have hm : columnNorm (fun i => ∑ j,X i j*v j)≤‖X‖ := by
      exact (columnNorm_matmul_le X v).trans (by simpa using mul_le_mul_of_nonneg_left hn (norm_nonneg X))
    have hdv : ‖WithLp.toLp 2 (fun i => Δ (v i) ζ)‖≤2*c := by
      calc _ ≤ c*columnNorm v*‖ζ‖ := hcol v ζ
        _ ≤ c*1*2 := by gcongr
        _ = 2*c := by ring
    have hdxv : ‖WithLp.toLp 2 (fun i => Δ (∑ j, X i j*v j) ζ)‖≤2*c*‖X‖ := by
      calc _ ≤ c*columnNorm (fun i => ∑ j, X i j*v j)*‖ζ‖ := hcol _ ζ
        _ ≤ c*‖X‖*2 := by gcongr
        _ = 2*c*‖X‖ := by ring
    have hlam : ‖matrixAction (fun i j => lam (X i j))
        (WithLp.toLp 2 (fun i => Δ (v i) ζ))‖≤2*c*‖X‖ := by
      calc _ ≤ ‖matrixRepresentation lam X‖*‖WithLp.toLp 2 (fun i => Δ (v i) ζ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖X‖*(2*c) := by gcongr; exact matrixRepresentation_norm_le lam X
        _ = 2*c*‖X‖ := by ring
    dsimp only [D]
    rw [derivation_matrix_column σ lam Δ hΔ]
    exact (norm_sub_le _ _).trans (by linarith)
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro ξ hξ
  have hclosed : IsClosed {x : PiLp 2 (fun _ : ι => H) | ‖D x‖≤4*c*‖X‖} :=
    isClosed_le (D.continuous.norm) continuous_const
  apply hclosed.closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨ζ,v,hζ,hv,ha⟩ := approximate_unit_column σ Ω hΩ ξ hξ ε hε
  exact ⟨WithLp.toLp 2 (fun i => σ (v i) ζ),hbound ζ v hζ hv,by rwa [dist_eq_norm]⟩

end Kadison.CyclicColumns

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Kadison.CyclicColumns.cyclic_matrix_bound_oai.{u_1, u_2, u_3, u_4} := @OAI.Kadison.CyclicColumns.cyclic_matrix_bound_oai.{u_1, u_2, u_3, u_4}
