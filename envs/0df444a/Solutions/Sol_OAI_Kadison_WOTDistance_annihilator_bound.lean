-- Prove2me | solution 1 for OAI.Kadison.WOTDistance.annihilator_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:14:25.233847+00:00
-- url     : https://prove2.me/submissions/f5ef4b0a-743d-4791-808d-6dce6b57790f

import Mathlib
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C021
import Definitions.Def_OAIQ039C029
import Definitions.Def_OAIQ039C031

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteFunctionalFactorization
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorFunctionals

open InnerProductSpace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ι : Type*} [Fintype ι]

lemma eq_sum_coefficients (φ : StrongDual ℂ (H →L[ℂ] H))
    (b : OrthonormalBasis ι ℂ H) (T : H →L[ℂ] H) :
    φ T=∑ i, inner ℂ (coefficient φ (b i)) (T (b i)) := by
  simp only [inner_coefficient,←map_sum]
  congr 1
  ext x
  simp only [sum_apply,rankOne_apply]
  simpa only [map_sum,map_smul,OrthonormalBasis.repr_apply_apply] using congrArg T (b.sum_repr x).symm

omit [CompleteSpace H] in
lemma norm_sq_sum_of_orthogonal (v : ι → H)
    (hv : Pairwise (fun i j => inner ℂ (v i) (v j)=0)) :
    ‖∑ i, v i‖^2=∑ i, ‖v i‖^2 := by
  classical
  simp only [@norm_sq_eq_re_inner ℂ H, sum_inner,inner_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  refine Finset.sum_eq_single i ?_ ?_
  · intro j _ hji
    simp [hv hji]
  · simp

omit [CompleteSpace H] [Fintype ι] in
lemma inner_normalized_of_ne (v : ι → H)
    (hv : Pairwise (fun i j => inner ℂ (v i) (v j)=0)) :
    Pairwise (fun i j => inner ℂ ((‖v i‖⁻¹ : ℝ) • v i)
      ((‖v j‖⁻¹ : ℝ) • v j)=0) := by
  intro i j hij
  simp [hv hij]

omit [CompleteSpace H] in
lemma orthogonalColumn_norm_le (b : OrthonormalBasis ι ℂ H) (u : ι → H)
    (hu : Pairwise (fun i j => inner ℂ (u i) (u j)=0))
    (hn : ∀ i, ‖u i‖≤1) : ‖∑ i, rankOne ℂ (u i) (b i)‖≤1 := by
  apply opNorm_le_bound _ zero_le_one
  intro x
  simp only [one_mul,sum_apply,rankOne_apply]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_sum_of_orthogonal _ (by
    intro i j hij
    simp [hu hij])]
  calc
    _ ≤ ∑ i, ‖inner ℂ (b i) x‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,mul_pow]
      exact mul_le_of_le_one_right (sq_nonneg _) (by nlinarith [norm_nonneg (u i),hn i])
    _ ≤ ‖x‖^2 := b.orthonormal.sum_inner_products_le x

omit [CompleteSpace H] in
lemma orthogonalColumn_apply_basis (b : OrthonormalBasis ι ℂ H) (u : ι → H) (j : ι) :
    (∑ i, rankOne ℂ (u i) (b i)) (b j)=u j := by
  classical
  simp [sum_apply,rankOne_apply,b.inner_eq_ite]

variable [FiniteDimensional ℂ H]

lemma singularBasis_orthogonal (R : H →L[ℂ] H) :
    Pairwise (fun i j => inner ℂ (R (singularBasis R i)) (R (singularBasis R j))=0) := by
  intro i j hij
  rw [←ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ ((R.toLinearMap.adjoint ∘ₗ R.toLinearMap) (singularBasis R i))
    (singularBasis R j)=0
  have he : (R.toLinearMap.adjoint ∘ₗ R.toLinearMap) (singularBasis R i)=
      (R.toLinearMap.isSymmetric_adjoint_comp_self.eigenvalues rfl i : ℂ) • singularBasis R i :=
    R.toLinearMap.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i
  rw [he]
  simp [(singularBasis R).inner_eq_zero hij]

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
lemma norm_inv_smul_norm_le_one (v : H) : ‖(‖v‖⁻¹ : ℝ) • v‖≤1 := by
  by_cases hv : v=0
  · simp [hv]
  · have hn : ‖v‖≠0 := norm_ne_zero_iff.mpr hv
    simp [norm_smul,hn]

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
lemma inner_norm_inv_smul (v : H) :
    inner ℂ v ((‖v‖⁻¹ : ℝ) • v)=(‖v‖ : ℂ) := by
  by_cases hv : v=0
  · simp [hv]
  · have hn : ‖v‖≠0 := norm_ne_zero_iff.mpr hv
    rw [inner_smul_right_eq_smul,inner_self_eq_norm_sq_to_K,Complex.real_smul]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hn]
    rfl

lemma sum_singular_coefficients_le (φ : StrongDual ℂ (H →L[ℂ] H)) :
    ∑ i, ‖coefficient φ (singularBasis (coefficient φ) i)‖≤‖φ‖ := by
  let b := singularBasis (coefficient φ)
  let v := fun i => coefficient φ (b i)
  let u := fun i => (‖v i‖⁻¹ : ℝ) • v i
  let P := ∑ i, rankOne ℂ (u i) (b i)
  have hP : ‖P‖≤1 := orthogonalColumn_norm_le b u
    (inner_normalized_of_ne v (singularBasis_orthogonal (coefficient φ)))
    (fun i => norm_inv_smul_norm_le_one (v i))
  have hφP : φ P=(∑ i, ‖v i‖ : ℝ) := by
    rw [eq_sum_coefficients φ b P,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℂ (v i) (P (b i))=_
    change inner ℂ (v i) ((∑ j, rankOne ℂ (u j) (b j)) (b i))=_
    rw [orthogonalColumn_apply_basis]
    exact inner_norm_inv_smul (v i)
  have hh := (φ.le_opNorm P).trans (mul_le_of_le_one_right (norm_nonneg φ) hP)
  rw [hφP,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at hh
  exact hh

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
lemma balanced_inner (v b : H) (T : H →L[ℂ] H) :
    inner ℂ ((Real.sqrt ‖v‖)⁻¹ • v) (T (Real.sqrt ‖v‖ • b))=inner ℂ v (T b) := by
  by_cases hv : v=0
  · simp [hv]
  have hs : Real.sqrt ‖v‖≠0 := Real.sqrt_ne_zero'.mpr (norm_pos_iff.mpr hv)
  rw [map_smul_of_tower,inner_smul_left_eq_smul,inner_smul_right_eq_smul,
    smul_smul,inv_mul_cancel₀ hs,one_smul]

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
lemma balanced_right_norm_sq (v : H) : ‖(Real.sqrt ‖v‖)⁻¹ • v‖^2=‖v‖ := by
  by_cases hv : v=0
  · simp [hv]
  have hs : Real.sqrt ‖v‖≠0 := Real.sqrt_ne_zero'.mpr (norm_pos_iff.mpr hv)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),mul_pow,inv_pow]
  rw [Real.sq_sqrt (norm_nonneg v)]
  field_simp [norm_ne_zero_iff.mpr hv]

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
lemma balanced_left_norm_sq (v b : H) (hb : ‖b‖=1) :
    ‖Real.sqrt ‖v‖ • b‖^2=‖v‖ := by
  simp [norm_smul,hb,Real.sq_sqrt (norm_nonneg v)]

theorem exists_finite_factorization (φ : StrongDual ℂ (H →L[ℂ] H)) :
    ∃ x y : PiLp 2 (fun _ : Fin (Module.finrank ℂ H) => H),
      (∀ T : H →L[ℂ] H, φ T=∑ i, inner ℂ (y i) (T (x i))) ∧ ‖x‖*‖y‖≤‖φ‖ := by
  let b := singularBasis (coefficient φ)
  let v := fun i => coefficient φ (b i)
  let x : PiLp 2 (fun _ : Fin (Module.finrank ℂ H) => H) :=
    WithLp.toLp 2 (fun i => Real.sqrt ‖v i‖ • b i)
  let y : PiLp 2 (fun _ : Fin (Module.finrank ℂ H) => H) :=
    WithLp.toLp 2 (fun i => (Real.sqrt ‖v i‖)⁻¹ • v i)
  refine ⟨x,y,?_,?_⟩
  · intro T
    rw [eq_sum_coefficients φ b T]
    apply Finset.sum_congr rfl
    intro i _
    exact (balanced_inner (v i) (b i) T).symm
  · have hx : ‖x‖^2=∑ i, ‖v i‖ := by
      rw [PiLp.norm_sq_eq_of_L2]
      apply Finset.sum_congr rfl
      intro i _
      exact balanced_left_norm_sq (v i) (b i) (b.orthonormal.1 i)
    have hy : ‖y‖^2=∑ i, ‖v i‖ := by
      rw [PiLp.norm_sq_eq_of_L2]
      apply Finset.sum_congr rfl
      intro i _
      exact balanced_right_norm_sq (v i)
    have hxy : ‖x‖=‖y‖ := (sq_eq_sq₀ (norm_nonneg x) (norm_nonneg y)).mp (hx.trans hy.symm)
    rw [←hxy,←pow_two,hx]
    exact sum_singular_coefficients_le φ

end Kadison.OperatorFunctionals

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteSupportFactorization
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorFunctionals

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (K : Submodule ℂ H) [K.HasOrthogonalProjection]

attribute [local instance] OAI.Kadison.OperatorFunctionals.instNormedSpaceComplexContinuousLinearMapIdSubtypeMemSubmodule_solutions
attribute [local instance] OAI.Kadison.OperatorFunctionals.instNormedAddCommGroupContinuousLinearMapComplexIdSubtypeMemSubmodule_solutions
lemma extendOperator_norm : ‖extendOperator K‖≤1 := by
  apply LinearMap.mkContinuous_norm_le _ zero_le_one

variable {ι : Type*} [Fintype ι]

omit [CompleteSpace H] [K.HasOrthogonalProjection] in
lemma tuple_coe_norm {n : ℕ} (x : PiLp 2 (fun _ : Fin n => K)) :
    ‖(WithLp.toLp 2 (fun i => (x i : H)) : PiLp 2 (fun _ : Fin n => H))‖=‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2]
  rfl

theorem exists_finite_support_factorization (a b : ι → H) :
    ∃ (n : ℕ) (x y : PiLp 2 (fun _ : Fin n => H)),
      (∀ T : H →L[ℂ] H, finiteFunctional a b T=∑ i, inner ℂ (y i) (T (x i))) ∧
        ‖x‖*‖y‖≤‖finiteFunctional a b‖ := by
  let L : Submodule ℂ H := Submodule.span ℂ (Set.range a ∪ Set.range b)
  let : FiniteDimensional ℂ L := FiniteDimensional.span_of_finite ℂ
    ((Set.finite_range a).union (Set.finite_range b))
  have ha : ∀ i, a i∈L := fun i => Submodule.subset_span (Or.inl ⟨i,rfl⟩)
  have hb : ∀ i, b i∈L := fun i => Submodule.subset_span (Or.inr ⟨i,rfl⟩)
  let ψ := (finiteFunctional a b).comp (extendOperator L)
  obtain ⟨x,y,hxy,hn⟩ := exists_finite_factorization ψ
  let x' : PiLp 2 (fun _ : Fin (Module.finrank ℂ L) => H) := WithLp.toLp 2 (fun i => (x i : H))
  let y' : PiLp 2 (fun _ : Fin (Module.finrank ℂ L) => H) := WithLp.toLp 2 (fun i => (y i : H))
  refine ⟨Module.finrank ℂ L,x',y',?_,?_⟩
  · intro T
    let Tc : L →L[ℂ] L := L.orthogonalProjectionOnto.comp (T.comp L.subtypeL)
    have he : ψ Tc=finiteFunctional a b T := by
      change finiteFunctional a b (extendOperator L Tc)=finiteFunctional a b T
      simp only [finiteFunctional_apply,extendOperator_apply]
      apply Finset.sum_congr rfl
      intro i _
      have hpa : L.orthogonalProjectionOnto (a i)=⟨a i,ha i⟩ :=
        L.orthogonalProjectionOnto_mem_subspace_eq_self ⟨a i,ha i⟩
      rw [hpa]
      change inner ℂ (⟨b i,hb i⟩ : L) (L.orthogonalProjectionOnto (T (a i)))=_
      exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨b i,hb i⟩ _
    rw [←he,hxy Tc]
    apply Finset.sum_congr rfl
    intro i _
    exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (y i) (T (x i))
  · rw [tuple_coe_norm L x,tuple_coe_norm L y]
    exact hn.trans ((opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (extendOperator_norm L)))

end Kadison.OperatorFunctionals

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WOTFunctionals
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMapWOT

namespace Kadison.WOTDistance

open OperatorFunctionals

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma wot_topology : (inferInstance : TopologicalSpace (H →WOT[ℂ] H))=
    ⨅ p : H × StrongDual ℂ H, TopologicalSpace.induced (coeffLM p) inferInstance := by
  change TopologicalSpace.induced (inducingFn (RingHom.id ℂ) H H) Pi.topologicalSpace=_
  rw [induced_to_pi]
  rfl

theorem factorization (φ : (H →WOT[ℂ] H) →L[ℂ] ℂ) :
    ∃ (n : ℕ) (x y : PiLp 2 (fun _ : Fin n => H)),
      (∀ T : H →L[ℂ] H, φ (ofCLM T)=∑ i, inner ℂ (y i) (T (x i))) ∧
        ‖x‖*‖y‖≤‖φ.comp ContinuousLinearMap.WOTofCLM‖ := by
  classical
  have hm : φ.toLinearMap ∈ Submodule.span ℂ (Set.range (coeffLM (H:=H))) := by
    apply (LinearMap.mem_span_iff_continuous _).mpr
    rw [←wot_topology]
    exact φ.continuous
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hm
  let a : c.support → H := fun i => i.1.1
  let b : c.support → H := fun i => star (c i.1) • (InnerProductSpace.toDual ℂ H).symm i.1.2
  have he : φ.comp ContinuousLinearMap.WOTofCLM=finiteFunctional a b := by
    ext T
    change φ.toLinearMap (ofCLM T)=finiteFunctional a b T
    rw [←hc]
    simp only [Finsupp.sum,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,
      finiteFunctional_apply,coeffLM_apply]
    rw [←Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro i _
    simp [a,b,InnerProductSpace.toDual_symm_apply,mul_comm]
  obtain ⟨n,x,y,hxy,hn⟩ := exists_finite_support_factorization a b
  refine ⟨n,x,y,?_,?_⟩
  · intro T
    have hh := congrArg (fun f : StrongDual ℂ (H →L[ℂ] H) => f T) he
    exact hh.trans (hxy T)
  · rwa [he]

end Kadison.WOTDistance

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ArvesonAnnihilator
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMapWOT

namespace Kadison.WOTDistance

open OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem annihilator_bound_oai (M : VonNeumannAlgebra H) (G : H →L[ℂ] H)
    {c : ℝ} (hc : 0 ≤ c) (hcb : AmplifiedBound M G c)
    (φ : (H →WOT[ℂ] H) →L[ℂ] ℂ)
    (hφ : ∀ T∈M.commutant, φ (ofCLM T)=0) :
    ‖φ (ofCLM G)‖ ≤ c*‖φ.comp ContinuousLinearMap.WOTofCLM‖ := by
  classical
  obtain ⟨n,x,y,hxy,hn⟩ := factorization φ
  let S := M.commutant.toStarSubalgebra.map (diagonal (H:=H) (Fin n))
  let K := cyclicSubspace S x
  let Q := K.starProjection
  have hzero : ∀ z∈K, inner ℂ y z=0 := by
    apply closure_minimal (s:=(orbitSubmodule S x : Set (SumSpace (H:=H) (Fin n))))
      (t:={z | inner ℂ y z=0}) ?_ ?_
    · rintro z ⟨a,⟨b,hb,rfl⟩,rfl⟩
      change inner ℂ y (diagonal (H:=H) (Fin n) b x)=0
      simpa only [PiLp.inner_apply,diagonal_apply,←hxy b] using hφ b hb
    · exact isClosed_eq (innerSL ℂ y).continuous continuous_const
  have hQx : Q x=x :=
    Submodule.starProjection_eq_self_iff.mpr (mem_cyclicSubspace_self S x)
  have hQmem : ∀ i j, entry (Fin n) Q i j∈M := by
    intro i j
    rw [←SetLike.mem_coe,←M.centralizer_centralizer]
    intro a ha
    apply entry_commutes (Fin n) Q a
    have ha' : a∈M.commutant := by
      rwa [←SetLike.mem_coe,VonNeumannAlgebra.coe_commutant]
    exact cyclic_projection_mem_commutant S x (diagonal (H:=H) (Fin n) a) ⟨a,ha',rfl⟩
  have hQnorm : ‖diagonal (H:=H) (Fin n) G*Q-Q*diagonal (H:=H) (Fin n) G‖ ≤ c :=
    (hcb n Q hQmem).trans (mul_le_of_le_one_right hc K.starProjection_norm_le)
  have hid : inner ℂ y ((diagonal (H:=H) (Fin n) G*Q-Q*diagonal (H:=H) (Fin n) G) x)=
      φ (ofCLM G) := by
    simp only [_root_.sub_apply,mul_apply_eq_comp,inner_sub_right,hQx]
    rw [hzero _ (K.starProjection_apply_mem _),sub_zero]
    simpa only [PiLp.inner_apply,diagonal_apply] using (hxy G).symm
  rw [←hid]
  calc
    _ ≤ ‖y‖*‖(diagonal (H:=H) (Fin n) G*Q-Q*diagonal (H:=H) (Fin n) G) x‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖y‖*(c*‖x‖) := mul_le_mul_of_nonneg_left
      ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hQnorm (norm_nonneg x))) (norm_nonneg y)
    _ = c*(‖x‖*‖y‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hn hc

end Kadison.WOTDistance

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.WOTDistance.annihilator_bound_oai.{u_1} := @OAI.Kadison.WOTDistance.annihilator_bound_oai.{u_1}
