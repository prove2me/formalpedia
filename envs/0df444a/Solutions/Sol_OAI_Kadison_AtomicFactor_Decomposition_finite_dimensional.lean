-- Prove2me | solution 1 for OAI.Kadison.AtomicFactor.Decomposition.finite_dimensional
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:17:26.43615+00:00
-- url     : https://prove2.me/submissions/d5bb1c14-6e8f-47ba-b906-7bce9688d945

import Mathlib
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C048

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

lemma selfadjoint_corner_scalar (M : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsMinimalProjection M p) {a : H →L[ℂ] H} (haM : a∈M)
    (ha : IsSelfAdjoint a) (hpa : p*a=a) (hap : a*p=a) :
    ∃ z : ℂ,a=z • p := by
  let N := vonNeumannIntersection M (vonNeumannCentralizer {p})
  have haN : a∈N := by
    refine ⟨haM,?_⟩
    change a∈((StarSubalgebra.centralizer ℂ {p} : StarSubalgebra ℂ (H →L[ℂ] H)) : Set _)
    rw [StarSubalgebra.coe_centralizer]
    intro q hq
    rcases hq with hq|hq
    · have he : q=p := Set.mem_singleton_iff.mp hq
      subst q
      exact hpa.trans hap.symm
    · have he : q=star p := by simpa only [Set.star_singleton,Set.mem_singleton_iff] using hq
      rw [he,hp.2.1.isSelfAdjoint.star_eq]
      exact hpa.trans hap.symm
  let K : Submodule ℂ (H →L[ℂ] H) := Submodule.span ℂ {p}
  have hc : IsClosed (K : Set (H →L[ℂ] H)) := K.closed_of_finiteDimensional
  have haK : a∈K := by
    apply hc.closure_subset
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n,q,c,hq,_,he⟩ := Polar.exists_selfadjoint_spectral_sum N haN ha hε
    have hpq (i : Fin n) : p*q i=q i*p := by
      have hh := (hq i).1
      change q i∈M ∧ q i∈vonNeumannCentralizer {p} at hh
      have hh' := hh.2
      change q i∈((StarSubalgebra.centralizer ℂ {p} : StarSubalgebra ℂ (H →L[ℂ] H)) : Set _) at hh'
      rw [StarSubalgebra.coe_centralizer] at hh'
      exact hh' p (Or.inl (Set.mem_singleton p))
    have hmem (i : Fin n) : p*q i∈K := by
      have hproj : IsStarProjection (p*q i) := hp.2.1.mul (hq i).2 (hpq i)
      have hle : p*q i≤p := by
        apply (hproj.le_iff_mul_eq_right hp.2.1).mpr
        rw [←mul_assoc,hp.2.1.isIdempotentElem.eq]
      rcases hp.2.2.2 (p*q i) (M.mul_mem hp.1 (hq i).1.1) hproj hle with hz|hz
      · rw [hz]; exact K.zero_mem
      · rw [hz]; exact Submodule.subset_span (Set.mem_singleton p)
    refine ⟨p*(∑ i,c i • q i),?_,?_⟩
    · rw [Finset.mul_sum]
      apply K.sum_mem
      intro i _
      rw [mul_smul_comm]
      exact K.smul_mem (c i : ℂ) (hmem i)
    · rw [dist_eq_norm,←hpa,←mul_sub]
      have hnorm : ‖p‖≤1 := hp.2.1.norm_le
      exact (norm_mul_le _ _).trans_lt ((mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans_lt
        (by simpa only [one_mul] using he))
  obtain ⟨z,hz⟩ := Submodule.mem_span_singleton.mp haK
  exact ⟨z,hz.symm⟩

end AtomicFactor

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AtomicCoefficients
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

namespace Kadison.AtomicFactor.Decomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (D : Decomposition M p)

lemma support_tendsto (x : H) : Tendsto (fun s : Finset D.I => D.support s x) atTop (𝓝 x) :=
  D.strong x

lemma eq_zero_of_coefficients_zero {a : H →L[ℂ] H}
    (ha : ∀ i j,star (D.v i)*a*D.v j=0) : a=0 := by
  have hleft (i : D.I) : star (D.v i)*a=0 := by
    ext x
    have he (s : Finset D.I) : (star (D.v i)*a) (D.support s x)=0 := by
      have ht : (star (D.v i)*a)*D.support s=0 := by
        rw [support,Finset.mul_sum]
        apply Finset.sum_eq_zero
        intro j hj
        rw [←mul_assoc,ha i j,zero_mul]
      exact congrArg (fun T : H →L[ℂ] H => T x) ht
    exact tendsto_nhds_unique
      (((star (D.v i)*a).continuous.tendsto x).comp (D.support_tendsto x))
      (by simpa only [Function.comp_def,he,zero_apply] using (tendsto_const_nhds : Tendsto (fun _ : Finset D.I => (0:H)) atTop (𝓝 0)))
  ext x
  have he (s : Finset D.I) : D.support s (a x)=0 := by
    have ht : D.support s*a=0 := by
      rw [support,Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro i hi
      rw [mul_assoc,hleft i,mul_zero]
    exact congrArg (fun T : H →L[ℂ] H => T x) ht
  exact tendsto_nhds_unique (D.support_tendsto (a x))
    (by simpa only [Function.comp_def,he,zero_apply] using (tendsto_const_nhds : Tendsto (fun _ : Finset D.I => (0:H)) atTop (𝓝 0)))

lemma eq_of_coefficients_eq {a b : H →L[ℂ] H}
    (h : ∀ i j,star (D.v i)*a*D.v j=star (D.v i)*b*D.v j) : a=b := by
  apply sub_eq_zero.mp
  apply D.eq_zero_of_coefficients_zero
  intro i j
  rw [mul_sub,sub_mul,h i j,sub_self]

end Kadison.AtomicFactor.Decomposition

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MinimalCorner
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.AtomicFactor

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma corner_scalar (M : VonNeumannAlgebra H) {p : H →L[ℂ] H}
    (hp : IsMinimalProjection M p) {a : H →L[ℂ] H} (haM : a∈M)
    (hpa : p*a=a) (hap : a*p=a) : ∃ z : ℂ,a=z • p := by
  have hps : p*star a=star a := by
    simpa only [star_mul,hp.2.1.isSelfAdjoint.star_eq] using congrArg star hap
  have hsp : star a*p=star a := by
    simpa only [star_mul,hp.2.1.isSelfAdjoint.star_eq] using congrArg star hpa
  let ar : H →L[ℂ] H := realPart a
  let ai : H →L[ℂ] H := imaginaryPart a
  have hrM : ar∈M := by
    rw [show ar=(2:ℝ)⁻¹ • (a+star a) from realPart_apply_coe a]
    exact (M.toSubalgebra.restrictScalars ℝ).smul_mem (M.add_mem haM (M.star_mem' haM)) _
  have hiM : ai∈M := by
    rw [show ai= -Complex.I • (2:ℝ)⁻¹ • (a-star a) from imaginaryPart_apply_coe a]
    exact M.smul_mem ((M.toSubalgebra.restrictScalars ℝ).smul_mem (M.sub_mem haM (M.star_mem' haM)) _) _
  have hpr : p*ar=ar := by
    simp only [ar,realPart_apply_coe,mul_smul_comm,mul_add,hpa,hps]
  have hrp : ar*p=ar := by
    simp only [ar,realPart_apply_coe,smul_mul_assoc,add_mul,hap,hsp]
  have hpi : p*ai=ai := by
    simp only [ai,imaginaryPart_apply_coe,mul_smul_comm,mul_sub,hpa,hps]
  have hip : ai*p=ai := by
    simp only [ai,imaginaryPart_apply_coe,smul_mul_assoc,sub_mul,hap,hsp]
  obtain ⟨r,hr⟩ := selfadjoint_corner_scalar M hp hrM (realPart a).property hpr hrp
  obtain ⟨s,hs⟩ := selfadjoint_corner_scalar M hp hiM (imaginaryPart a).property hpi hip
  refine ⟨r+Complex.I*s,?_⟩
  calc
    a=ar+Complex.I • ai := (realPart_add_I_smul_imaginaryPart a).symm
    _=(r+Complex.I*s) • p := by rw [hr,hs,smul_smul,add_smul]

end Kadison.AtomicFactor

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AtomicFinite
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.AtomicFactor.Decomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (D : Decomposition M p)

theorem finite_dimensional_oai [Finite D.I] (hp : IsMinimalProjection M p) :
    FiniteDimensional ℂ M := by
  classical
  let := Fintype.ofFinite D.I
  let K : Submodule ℂ (H →L[ℂ] H) := Submodule.span ℂ {p}
  have hcoeff (a : M) (ij : D.I×D.I) : star (D.v ij.1)*(a:H →L[ℂ] H)*D.v ij.2∈K := by
    have hpa : p*star (D.v ij.1)=star (D.v ij.1) := by
      simpa only [star_mul,hp.2.1.isSelfAdjoint.star_eq] using congrArg star (D.source ij.1)
    obtain ⟨z,hz⟩ := corner_scalar M hp
      (M.mul_mem (M.mul_mem (M.star_mem' (D.mem ij.1)) a.property) (D.mem ij.2))
      (by rw [←mul_assoc,←mul_assoc,hpa])
      (by rw [mul_assoc,D.source])
    rw [hz]
    exact K.smul_mem z (Submodule.subset_span (Set.mem_singleton p))
  let L : M →ₗ[ℂ] ((D.I×D.I) → K) :=
    { toFun := fun a ij => ⟨star (D.v ij.1)*(a:H →L[ℂ] H)*D.v ij.2,hcoeff a ij⟩
      map_add' := by
        intro a b
        funext ij
        apply Subtype.ext
        change star (D.v ij.1)*((a:H →L[ℂ] H)+(b:H →L[ℂ] H))*D.v ij.2=
          star (D.v ij.1)*(a:H →L[ℂ] H)*D.v ij.2+star (D.v ij.1)*(b:H →L[ℂ] H)*D.v ij.2
        rw [mul_add,add_mul]
      map_smul' := by
        intro c a
        funext ij
        apply Subtype.ext
        change star (D.v ij.1)*(c • (a:H →L[ℂ] H))*D.v ij.2=
          c • (star (D.v ij.1)*(a:H →L[ℂ] H)*D.v ij.2)
        rw [mul_smul_comm,smul_mul_assoc] }
  apply FiniteDimensional.of_injective L
  intro a b hab
  apply Subtype.ext
  apply D.eq_of_coefficients_eq
  intro i j
  exact congrArg (fun f : (D.I×D.I) → K => ((f (i,j)):H →L[ℂ] H)) hab

end Kadison.AtomicFactor.Decomposition

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.AtomicFactor.Decomposition.finite_dimensional_oai.{u_1} := @OAI.Kadison.AtomicFactor.Decomposition.finite_dimensional_oai.{u_1}
