-- Prove2me | solution 1 for MomentDRO.WorstCov.optimal_values_eq
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T06:37:32.523982+00:00
-- url     : https://prove2.me/submissions/a3cd9fa2-6998-4f48-ab78-e91834777dce

import Definitions.Def_MomentDRO_WorstCov_Setting

section
set_option autoImplicit false
open MeasureTheory Matrix
namespace MomentWorstCodex
noncomputable def atomicLaw {n k : ℕ} (a : Fin k → Fin n → ℝ) (w : Fin k → ℝ) :
    Measure (Fin n → ℝ) := ∑ i, ENNReal.ofReal (w i) • Measure.dirac (a i)

lemma atomic_integrable {n k : ℕ} (a : Fin k → Fin n → ℝ) (w : Fin k → ℝ)
    (f : (Fin n → ℝ) → ℝ) : Integrable f (atomicLaw a w) := by
  unfold atomicLaw
  apply integrable_finsetSum_measure.mpr
  intro i hi
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma atomic_integral {n k : ℕ} (a : Fin k → Fin n → ℝ) (w : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (f : (Fin n → ℝ) → ℝ) :
    (∫ z, f z ∂atomicLaw a w) = ∑ i, w i * f (a i) := by
  unfold atomicLaw
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (hw i)]
    rfl
  · intro i hi
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma atomic_probability {n k : ℕ} (a : Fin k → Fin n → ℝ) (w : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) : IsProbabilityMeasure (atomicLaw a w) := by
  constructor
  unfold atomicLaw
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply,Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i),hs]
  simp
lemma atomic_memLp_two {n k : ℕ} (a : Fin k → Fin n → ℝ) (w : Fin k → ℝ)
    (f : (Fin n → ℝ) → ℝ) : MemLp f 2 (atomicLaw a w) :=
  (memLp_two_iff_integrable_sq (atomic_integrable a w f).aestronglyMeasurable).mpr
    (atomic_integrable a w (fun z => (f z)^2))

lemma atomic_second_moments {n k : ℕ} (a : Fin k → Fin n → ℝ) (w : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) : MomentDRO.Conf.HasSecondMoments (atomicLaw a w) :=
  ⟨atomic_probability a w hw hs,fun i => atomic_memLp_two a w (fun z => z i)⟩

end MomentWorstCodex


end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf MomentDRO.WorstCov
namespace MomentWorstCodex
lemma coordinate_integrable {n : ℕ} {P : Measure (Fin n → ℝ)}
    (hP : HasSecondMoments P) (i : Fin n) : Integrable (fun z => z i) P := by
  let := hP.1
  exact (hP.2 i).integrable (by norm_num)
lemma coordinate_product_integrable {n : ℕ} {P : Measure (Fin n → ℝ)}
    (hP : HasSecondMoments P) (i j : Fin n) : Integrable (fun z => z i * z j) P := by
  exact (hP.2 i).integrable_mul (hP.2 j)
lemma centered_product_integrable {n : ℕ} {P : Measure (Fin n → ℝ)}
    (hP : HasSecondMoments P) (c : Fin n → ℝ) (i j : Fin n) :
    Integrable (fun z => (z i-c i)*(z j-c j)) P := by
  let := hP.1
  have hi := (hP.2 i).sub (memLp_const (c i))
  have hj := (hP.2 j).sub (memLp_const (c j))
  exact hi.integrable_mul hj
lemma second_about_expansion {n : ℕ} {P : Measure (Fin n → ℝ)}
    (hP : HasSecondMoments P) (c : Fin n → ℝ) :
    secondMomentAbout P c = secondMomentAbout P 0 - vecMulVec (meanVec P) c -
      vecMulVec c (meanVec P) + vecMulVec c c := by
  let := hP.1
  ext i j
  change (∫ z, (z i-c i)*(z j-c j) ∂P) =
    (∫ z, (z i-0)*(z j-0) ∂P) - (∫ z,z i ∂P)*c j -
      c i*(∫ z,z j ∂P) + c i*c j
  have he : (fun z : Fin n → ℝ => (z i-c i)*(z j-c j)) =
      (fun z => ((z i*z j-z i*c j)-c i*z j)+c i*c j) := by funext z; ring
  rw [he,integral_add,integral_sub,integral_sub,integral_mul_const,integral_const_mul]
  · simp
  · exact coordinate_product_integrable hP i j
  · exact (coordinate_integrable hP i).mul_const _
  · exact (coordinate_product_integrable hP i j).sub ((coordinate_integrable hP i).mul_const _)
  · exact (coordinate_integrable hP j).const_mul _
  · exact ((coordinate_product_integrable hP i j).sub ((coordinate_integrable hP i).mul_const _)).sub ((coordinate_integrable hP j).const_mul _)
  · exact integrable_const _
end MomentWorstCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf MomentDRO.WorstCov
namespace MomentWorstCodex
lemma mixture_integrable {n K : ℕ} (v : Fin K → ℝ) (P : Fin K → Measure (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) (hf : ∀ k,Integrable f (P k)) : Integrable f (mixture v P) := by
  unfold mixture
  apply integrable_finsetSum_measure.mpr
  intro k hk
  exact (hf k).smul_measure ENNReal.ofReal_ne_top
lemma mixture_integral {n K : ℕ} (v : Fin K → ℝ) (P : Fin K → Measure (Fin n → ℝ))
    (hv : ∀ k,0 ≤ v k) (f : (Fin n → ℝ) → ℝ) (hf : ∀ k,Integrable f (P k)) :
    (∫ z,f z ∂mixture v P) = ∑ k,v k*(∫ z,f z ∂P k) := by
  unfold mixture
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_smul_measure,ENNReal.toReal_ofReal (hv k)]
    rfl
  · intro k hk
    exact (hf k).smul_measure ENNReal.ofReal_ne_top
lemma mixture_probability {n K : ℕ} (v : Fin K → ℝ) (P : Fin K → Measure (Fin n → ℝ))
    (hv : ∀ k,0 ≤ v k) (hs : ∑ k,v k=1) (hP : ∀ k,IsProbabilityMeasure (P k)) :
    IsProbabilityMeasure (mixture v P) := by
  constructor
  unfold mixture
  rw [Measure.finsetSum_apply]
  have he (k : Fin K) : P k Set.univ=1 := by let := hP k; exact measure_univ
  simp only [Measure.smul_apply,he,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hv k),hs]
  simp
lemma mixture_memLp_two {n K : ℕ} (v : Fin K → ℝ) (P : Fin K → Measure (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) (hm : Measurable f) (hP : ∀ k,MemLp f 2 (P k)) :
    MemLp f 2 (mixture v P) := by
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  exact mixture_integrable v P (fun z => (f z)^2) (fun k => (hP k).integrable_sq)
lemma mixture_second_moments {n K : ℕ} (v : Fin K → ℝ) (P : Fin K → Measure (Fin n → ℝ))
    (hv : ∀ k,0 ≤ v k) (hs : ∑ k,v k=1) (hP : ∀ k,HasSecondMoments (P k)) :
    HasSecondMoments (mixture v P) := by
  refine ⟨mixture_probability v P hv hs (fun k => (hP k).1),?_⟩
  intro i
  exact mixture_memLp_two v P (fun z => z i) (measurable_pi_apply i) (fun k => (hP k).2 i)
lemma mixture_mean {n K : ℕ} (v : Fin K → ℝ) (P : Fin K → Measure (Fin n → ℝ))
    (hv : ∀ k,0 ≤ v k) (hP : ∀ k,HasSecondMoments (P k)) :
    meanVec (mixture v P) = ∑ k,v k • meanVec (P k) := by
  ext i
  change (∫ z,z i ∂mixture v P) = _
  rw [mixture_integral v P hv _ (fun k => coordinate_integrable (hP k) i)]
  simp [meanVec,Finset.sum_apply]
lemma mixture_second_about {n K : ℕ} (v : Fin K → ℝ) (P : Fin K → Measure (Fin n → ℝ))
    (hv : ∀ k,0 ≤ v k) (hP : ∀ k,HasSecondMoments (P k)) (c : Fin n → ℝ) :
    secondMomentAbout (mixture v P) c = ∑ k,v k • secondMomentAbout (P k) c := by
  ext i j
  change (∫ z,(z i-c i)*(z j-c j) ∂mixture v P) = _
  rw [mixture_integral v P hv _ (fun k => centered_product_integrable (hP k) c i j)]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  rfl
end MomentWorstCodex


end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf MomentDRO.WorstCov
namespace MomentWorstCodex
lemma dot_integrable {n : ℕ} {P : Measure (Fin n → ℝ)} (hP : HasSecondMoments P)
    (x : Fin n → ℝ) : Integrable (fun z => z ⬝ᵥ x) P := by
  exact integrable_finsetSum _ (fun i _ => (coordinate_integrable hP i).mul_const (x i))
lemma dot_integral {n : ℕ} {P : Measure (Fin n → ℝ)} (hP : HasSecondMoments P)
    (x : Fin n → ℝ) : (∫ z,z ⬝ᵥ x ∂P) = x ⬝ᵥ meanVec P := by
  unfold dotProduct
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_mul_const,mul_comm]
    rfl
  · intro i hi
    exact (coordinate_integrable hP i).mul_const _
lemma piece_integrable {n K : ℕ} {P : Measure (Fin n → ℝ)} (hP : HasSecondMoments P)
    (a b : Fin K → ℝ) (x : Fin n → ℝ) (k : Fin K) :
    Integrable (fun z => -(a k)*(z ⬝ᵥ x)-b k) P := by
  let := hP.1
  exact ((dot_integrable hP x).const_mul _).sub (integrable_const _)
lemma cost_integrable {n K : ℕ} [NeZero K] {P : Measure (Fin n → ℝ)}
    (hP : HasSecondMoments P) (a b : Fin K → ℝ) (x : Fin n → ℝ) :
    Integrable (pwCost a b x) P := by
  have hi : Integrable (Finset.univ.sup' Finset.univ_nonempty
      (fun k : Fin K => fun z : Fin n → ℝ => -(a k)*(z ⬝ᵥ x)-b k)) P := by
    refine Finset.sup'_induction Finset.univ_nonempty _ (p := fun f => Integrable f P) ?_ ?_
    · intro f hf g hg
      exact hf.sup hg
    · intro k hk
      exact piece_integrable hP a b x k
  have he : (Finset.univ.sup' Finset.univ_nonempty
      (fun k : Fin K => fun z : Fin n → ℝ => -(a k)*(z ⬝ᵥ x)-b k)) = pwCost a b x := by
    funext z
    exact Finset.sup'_apply _ _ _
  rw [he] at hi
  exact hi
lemma piece_integral {n K : ℕ} {P : Measure (Fin n → ℝ)} (hP : HasSecondMoments P)
    (a b : Fin K → ℝ) (x : Fin n → ℝ) (k : Fin K) :
    (∫ z,-(a k)*(z ⬝ᵥ x)-b k ∂P) = -(a k)*(x ⬝ᵥ meanVec P)-b k := by
  let := hP.1
  rw [integral_sub ((dot_integrable hP x).const_mul _) (integrable_const _),
    integral_const_mul,dot_integral hP x]
  simp
end MomentWorstCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf MomentDRO.WorstCov
namespace MomentWorstCodex
lemma cost_continuous {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ) :
    Continuous (pwCost a b x) := by
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro k hk
  fun_prop

def argmaxPred {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x z : Fin n → ℝ) (k : ℕ) : Prop :=
  ∃ h : k<K, -(a ⟨k,h⟩)*(z ⬝ᵥ x)-b ⟨k,h⟩=pwCost a b x z
lemma argmax_exists {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x z : Fin n → ℝ) :
    ∃ k : ℕ,argmaxPred a b x z k := by
  obtain ⟨k,hk,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun k : Fin K => -(a k)*(z ⬝ᵥ x)-b k)
  exact ⟨k.val,k.isLt,he.symm⟩
noncomputable def costIndex {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x z : Fin n → ℝ) : ℕ := by
  classical
  exact Nat.find (argmax_exists a b x z)
lemma cost_index_lt {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x z : Fin n → ℝ) :
    costIndex a b x z<K := by
  classical
  obtain ⟨hk,he⟩ := Nat.find_spec (argmax_exists a b x z)
  exact hk
lemma cost_index_measurable {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ) :
    Measurable (costIndex a b x) := by
  classical
  apply measurable_find (argmax_exists a b x)
  intro k
  by_cases hk : k<K
  · have he : {z : Fin n → ℝ | argmaxPred a b x z k} =
        {z | -(a ⟨k,hk⟩)*(z ⬝ᵥ x)-b ⟨k,hk⟩=pwCost a b x z} := by
      ext z
      simp only [Set.mem_ofPred_eq,argmaxPred]
      exact ⟨fun ⟨h,he⟩ => he,fun he => ⟨hk,he⟩⟩
    rw [he]
    exact (isClosed_eq (by fun_prop) (cost_continuous a b x)).measurableSet
  · have he : {z : Fin n → ℝ | argmaxPred a b x z k}=∅ := by
      ext z
      simp [argmaxPred,hk]
    rw [he]
    exact MeasurableSet.empty

def costCell {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ) (k : Fin K) :
    Set (Fin n → ℝ) := {z | costIndex a b x z=k.val}
lemma cost_cell_measurable {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ) (k : Fin K) :
    MeasurableSet (costCell a b x k) :=
  (cost_index_measurable a b x) (measurableSet_singleton k.val)
lemma cost_cell_cover {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x z : Fin n → ℝ) :
    ∃ k : Fin K,z ∈ costCell a b x k :=
  ⟨⟨costIndex a b x z,cost_index_lt a b x z⟩,rfl⟩
lemma cost_cell_value {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x z : Fin n → ℝ)
    (k : Fin K) (hk : z ∈ costCell a b x k) :
    -(a k)*(z ⬝ᵥ x)-b k=pwCost a b x z := by
  classical
  have hs : argmaxPred a b x z (costIndex a b x z) := Nat.find_spec (argmax_exists a b x z)
  obtain ⟨hlt,he⟩ := hs
  have heq : (⟨costIndex a b x z,hlt⟩ : Fin K)=k := Fin.ext hk
  rwa [heq] at he
lemma cost_cells_disjoint {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ) :
    Pairwise (fun i j => Disjoint (costCell a b x i) (costCell a b x j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hi hj
  apply hij
  exact Fin.ext (hi.symm.trans hj)
lemma cost_cells_union {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ) :
    (⋃ k : Fin K,costCell a b x k)=Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨k,hk⟩ := cost_cell_cover a b x z
  exact Set.mem_iUnion.mpr ⟨k,hk⟩
lemma cost_restrict_sum {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ)
    (P : Measure (Fin n → ℝ)) : (∑ k : Fin K,P.restrict (costCell a b x k))=P := by
  have hh := Measure.restrict_iUnion (μ:=P) (cost_cells_disjoint a b x) (cost_cell_measurable a b x)
  rw [cost_cells_union,Measure.restrict_univ] at hh
  simpa [Measure.sum_fintype] using hh.symm
end MomentWorstCodex


end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf MomentDRO.WorstCov
namespace MomentWorstCodex
lemma partition_integral {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ)
    (P : Measure (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) (hf : Integrable f P) :
    (∫ z,f z ∂P)=∑ k : Fin K,∫ z,f z ∂P.restrict (costCell a b x k) := by
  calc
    _ = ∫ z,f z ∂(∑ k : Fin K,P.restrict (costCell a b x k)) := by rw [cost_restrict_sum]
    _ = _ := integral_finsetSum_measure (fun k _ => hf.restrict)
lemma partition_cost_integral {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ)
    (P : Measure (Fin n → ℝ)) (hP : HasSecondMoments P) :
    (∫ z,pwCost a b x z ∂P)=∑ k : Fin K,∫ z,-(a k)*(z ⬝ᵥ x)-b k ∂P.restrict (costCell a b x k) := by
  rw [partition_integral a b x P _ (cost_integrable hP a b x)]
  apply Finset.sum_congr rfl
  intro k hk
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (cost_cell_measurable a b x k)] with z hz
  exact (cost_cell_value a b x z k hz).symm
end MomentWorstCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf
namespace MomentWorstCodex
lemma finite_coordinate_integrable {n : ℕ} (P : Measure (Fin n → ℝ)) [IsFiniteMeasure P]
    (hP : ∀ i,MemLp (fun z => z i) 2 P) (i : Fin n) : Integrable (fun z => z i) P :=
  (hP i).integrable (by norm_num)
lemma finite_centered_memLp {n : ℕ} (P : Measure (Fin n → ℝ)) [IsFiniteMeasure P]
    (hP : ∀ i,MemLp (fun z => z i) 2 P) (c : Fin n → ℝ) (i : Fin n) :
    MemLp (fun z => z i-c i) 2 P :=
  (hP i).sub (memLp_const _)
noncomputable def centeredFirst {n : ℕ} (P : Measure (Fin n → ℝ)) (c : Fin n → ℝ) :
    Fin n → ℝ := fun i => ∫ z,z i-c i ∂P
noncomputable def lawMass {n : ℕ} (P : Measure (Fin n → ℝ)) : ℝ := ∫ _ ,(1 : ℝ) ∂P
lemma finite_mean_decomposition {n : ℕ} (P : Measure (Fin n → ℝ)) [IsFiniteMeasure P]
    (hP : ∀ i,MemLp (fun z => z i) 2 P) (c : Fin n → ℝ) :
    meanVec P=centeredFirst P c+lawMass P • c := by
  ext i
  change (∫ z,z i ∂P)=(∫ z,z i-c i ∂P)+(∫ _,(1 : ℝ) ∂P)*c i
  rw [integral_sub (finite_coordinate_integrable P hP i) (integrable_const _)]
  simp only [integral_const,smul_eq_mul,mul_one]
  ring
lemma finite_dot_integral {n : ℕ} (P : Measure (Fin n → ℝ)) [IsFiniteMeasure P]
    (hP : ∀ i,MemLp (fun z => z i) 2 P) (x : Fin n → ℝ) :
    (∫ z,z ⬝ᵥ x ∂P)=x ⬝ᵥ meanVec P := by
  unfold dotProduct
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_mul_const,mul_comm]
    rfl
  · intro i hi
    exact (finite_coordinate_integrable P hP i).mul_const _
lemma finite_piece_integral {n : ℕ} (P : Measure (Fin n → ℝ)) [IsFiniteMeasure P]
    (hP : ∀ i,MemLp (fun z => z i) 2 P) (c x : Fin n → ℝ) (a b : ℝ) :
    (∫ z,-a*(z ⬝ᵥ x)-b ∂P) =
      -a*(x ⬝ᵥ (centeredFirst P c+lawMass P • c))-b*lawMass P := by
  have hi : Integrable (fun z => z ⬝ᵥ x) P :=
    integrable_finsetSum _ (fun i _ => (finite_coordinate_integrable P hP i).mul_const _)
  rw [integral_sub (hi.const_mul _) (integrable_const _),integral_const_mul,
    finite_dot_integral P hP x,finite_mean_decomposition P hP c]
  simp [lawMass,integral_const,smul_eq_mul,mul_comm]
end MomentWorstCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf MomentDRO.WorstCov
namespace MomentWorstCodex
lemma partition_second_sum {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x c : Fin n → ℝ)
    (P : Measure (Fin n → ℝ)) (hP : HasSecondMoments P) :
    (∑ k : Fin K,secondMomentAbout (P.restrict (costCell a b x k)) c)=secondMomentAbout P c := by
  ext i j
  rw [Matrix.sum_apply]
  change (∑ k : Fin K,∫ z,(z i-c i)*(z j-c j) ∂P.restrict (costCell a b x k))=
    ∫ z,(z i-c i)*(z j-c j) ∂P
  exact (partition_integral a b x P _ (centered_product_integrable hP c i j)).symm
lemma partition_first_sum {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x c : Fin n → ℝ)
    (P : Measure (Fin n → ℝ)) (hP : HasSecondMoments P) :
    (∑ k : Fin K,centeredFirst (P.restrict (costCell a b x k)) c)=meanVec P-c := by
  let := hP.1
  ext i
  rw [Finset.sum_apply]
  change (∑ k : Fin K,∫ z,z i-c i ∂P.restrict (costCell a b x k))=(∫ z,z i ∂P)-c i
  rw [← partition_integral a b x P (fun z => z i-c i) ((coordinate_integrable hP i).sub (integrable_const _))]
  rw [integral_sub (coordinate_integrable hP i) (integrable_const _)]
  simp
lemma partition_mass_sum {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ)
    (P : Measure (Fin n → ℝ)) (hP : HasSecondMoments P) :
    (∑ k : Fin K,lawMass (P.restrict (costCell a b x k)))=1 := by
  let := hP.1
  change (∑ k : Fin K,∫ _,(1 : ℝ) ∂P.restrict (costCell a b x k))=1
  rw [← partition_integral a b x P _ (integrable_const _)]
  simp
end MomentWorstCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix
namespace MomentWorstCodex
noncomputable def gramMoment {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (P : Measure α) (f : α → ι → ℝ) : Matrix ι ι ℝ := of fun i j => ∫ z,f z i*f z j ∂P
lemma gram_quadratic {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (P : Measure α) (f : α → ι → ℝ) (hf : ∀ i,MemLp (fun z => f z i) 2 P) (q : ι → ℝ) :
    (∫ z,(q ⬝ᵥ f z)^2 ∂P) = q ⬝ᵥ ((gramMoment P f)*ᵥ q) := by
  classical
  have hij (i j : ι) : Integrable (fun z => q i*(f z i*f z j)*q j) P :=
    ((hf i).integrable_mul (hf j)).const_mul (q i) |>.mul_const (q j)
  have hp : (fun z => (q ⬝ᵥ f z)^2) =
      (fun z => ∑ i : ι,∑ j : ι,q i*(f z i*f z j)*q j) := by
    funext z
    unfold dotProduct
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hp,integral_finsetSum]
  · change (∑ i : ι, ∫ z,∑ j : ι,q i*(f z i*f z j)*q j ∂P) =
      ∑ i : ι,q i*(∑ j : ι,(∫ z,f z i*f z j ∂P)*q j)
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum,integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [integral_mul_const,integral_const_mul]
      ring
    · intro j hj
      exact hij i j
  · intro i hi
    exact integrable_finsetSum _ (fun j _ => hij i j)
lemma gram_moment_psd {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (P : Measure α) (f : α → ι → ℝ) (hf : ∀ i,MemLp (fun z => f z i) 2 P) :
    (gramMoment P f).PosSemidef := by
  have hh : (gramMoment P f).IsHermitian := by
    ext i j
    change star (∫ z,f z j*f z i ∂P) = ∫ z,f z i*f z j ∂P
    simp only [star_trivial]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => mul_comm _ _)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro q
  simp only [star_trivial]
  rw [← gram_quadratic P f hf q]
  exact integral_nonneg (fun z => sq_nonneg _)
end MomentWorstCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf MomentDRO.WorstCov
namespace MomentWorstCodex
lemma bordered_moment_psd {n : ℕ} (P : Measure (Fin n → ℝ)) [IsFiniteMeasure P]
    (hP : ∀ i,MemLp (fun z => z i) 2 P) (c : Fin n → ℝ) :
    (bordered (secondMomentAbout P c) (centeredFirst P c) (lawMass P)).PosSemidef := by
  let f : (Fin n → ℝ) → (Fin n ⊕ Fin 1) → ℝ := fun z => Sum.elim (fun i => z i-c i) (fun _ => 1)
  have hf (i : Fin n ⊕ Fin 1) : MemLp (fun z => f z i) 2 P := by
    rcases i with i | i
    · exact finite_centered_memLp P hP c i
    · exact memLp_const 1
  have he : gramMoment P f=bordered (secondMomentAbout P c) (centeredFirst P c) (lawMass P) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [gramMoment,f,bordered,Matrix.fromBlocks,secondMomentAbout,centeredFirst,lawMass]
  rw [← he]
  exact gram_moment_psd P f hf
lemma law_mass_nonnegative {n : ℕ} (P : Measure (Fin n → ℝ)) : 0 ≤ lawMass P :=
  integral_nonneg (fun _ => by norm_num)
end MomentWorstCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf MomentDRO.WorstCov
namespace MomentWorstCodex
lemma fixed_mean_of_mem {n : ℕ} (μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hSig : Sig.PosDef) (γ : ℝ) (Q : Measure (Fin n → ℝ)) (hQ : Q ∈ D1 Set.univ μ Sig 0 γ) :
    meanVec Q=μ := by
  have hInv : Sig⁻¹.PosDef := Matrix.posDef_inv_iff.mpr hSig
  have hz : meanVec Q-μ=0 := by
    by_contra hn
    have hp := hInv.dotProduct_mulVec_pos hn
    simp only [star_trivial] at hp
    have hb := hQ.2.2.1
    change (meanVec Q-μ) ⬝ᵥ (Sig⁻¹*ᵥ (meanVec Q-μ)) ≤ 0 at hb
    exact (not_lt_of_ge hb) hp
  exact sub_eq_zero.mp hz
end MomentWorstCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf MomentDRO.WorstCov
namespace MomentWorstCodex
lemma fixed_law_certificate {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x μ : Fin n → ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (hSig : Sig.PosDef) (γ : ℝ)
    (Q : Measure (Fin n → ℝ)) (hQ : Q ∈ D1 Set.univ μ Sig 0 γ) :
    ∃ (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ) (v : Fin K → ℝ),
      Feasible19 μ Sig γ L l v ∧ (∫ y,pwCost a b x y ∂Q)=obj19 a b x l v := by
  have hP : HasSecondMoments Q := hQ.1
  let := hP.1
  have hmean := fixed_mean_of_mem μ Sig hSig γ Q hQ
  let R : Fin K → Measure (Fin n → ℝ) := fun k => Q.restrict (costCell a b x k)
  let L : Fin K → Matrix (Fin n) (Fin n) ℝ := fun k => secondMomentAbout (R k) 0
  let l : Fin K → Fin n → ℝ := fun k => meanVec (R k)
  let v : Fin K → ℝ := fun k => lawMass (R k)
  have hm0 (P : Measure (Fin n → ℝ)) : centeredFirst P 0=meanVec P := by
    ext i
    simp [centeredFirst,meanVec]
  have hsL : ∑ k,L k=secondMomentAbout Q 0 := partition_second_sum a b x 0 Q hP
  have hsl : ∑ k,l k=μ := by
    have hh := partition_first_sum a b x 0 Q hP
    simp only [hm0,sub_zero,hmean] at hh
    exact hh
  have he : secondMomentAbout Q μ=secondMomentAbout Q 0-vecMulVec μ μ := by
    rw [second_about_expansion hP μ,hmean]
    abel
  have hf : Feasible19 μ Sig γ L l v := by
    refine ⟨?_,⟨hsl,partition_mass_sum a b x Q hP⟩,?_⟩
    · rw [hsL]
      change (γ • Sig+vecMulVec μ μ-secondMomentAbout Q 0).PosSemidef
      have hh : γ • Sig+vecMulVec μ μ-secondMomentAbout Q 0=γ • Sig-secondMomentAbout Q μ := by
        rw [he]
        abel
      rw [hh]
      exact hQ.2.2.2
    · intro k
      have hh := bordered_moment_psd (R k) (fun i => (hP.2 i).restrict _) 0
      rwa [hm0] at hh
  refine ⟨L,l,v,hf,?_⟩
  rw [partition_cost_integral a b x Q hP]
  unfold obj19
  apply Finset.sum_congr rfl
  intro k hk
  have hh := finite_piece_integral (R k) (fun i => (hP.2 i).restrict _) 0 x (a k) (b k)
  simpa only [hm0,smul_zero,add_zero] using hh
end MomentWorstCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf MomentDRO.WorstCov
namespace MomentWorstCodex
lemma weighted_mixture_mean {n K : ℕ} (l : Fin K → Fin n → ℝ) (v : Fin K → ℝ)
    (hv : ∀ k,0 ≤ v k) (P : Fin K → Measure (Fin n → ℝ))
    (hP : ∀ k,HasSecondMoments (P k)) (hm : ∀ k,v k • meanVec (P k)=l k) :
    meanVec (mixture v P)=∑ k,l k := by
  rw [mixture_mean v P hv hP]
  simp_rw [hm]
lemma weighted_mixture_raw {n K : ℕ} (L : Fin K → Matrix (Fin n) (Fin n) ℝ)
    (v : Fin K → ℝ) (hv : ∀ k,0 ≤ v k) (P : Fin K → Measure (Fin n → ℝ))
    (hP : ∀ k,HasSecondMoments (P k)) (hr : ∀ k,v k • secondMomentAbout (P k) 0=L k) :
    secondMomentAbout (mixture v P) 0=∑ k,L k := by
  rw [mixture_second_about v P hv hP]
  simp_rw [hr]
end MomentWorstCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.WorstCov
namespace MomentWorstCodex
lemma weights_nonnegative {n K : ℕ} (μ : Fin n → ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ)
    (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ) (v : Fin K → ℝ)
    (hf : Feasible19 μ Sig γ L l v) (k : Fin K) : 0 ≤ v k := by
  have h : 0 ≤ bordered (L k) (l k) (v k) (Sum.inr (0 : Fin 1)) (Sum.inr 0) :=
    (hf.2.2 k).diag_nonneg
  simpa [bordered,Matrix.fromBlocks] using h

lemma weights_simplex {n K : ℕ} (μ : Fin n → ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ)
    (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ) (v : Fin K → ℝ)
    (hf : Feasible19 μ Sig γ L l v) : v ∈ stdSimplex ℝ (Fin K) :=
  ⟨weights_nonnegative μ Sig γ L l v hf,hf.2.1.2⟩

lemma weights_bounded {n K : ℕ} (μ : Fin n → ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ)
    (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ) (v : Fin K → ℝ)
    (hf : Feasible19 μ Sig γ L l v) (k : Fin K) : v k ≤ 1 := by
  have hs := Finset.single_le_sum (fun i _ => weights_nonnegative μ Sig γ L l v hf i) (Finset.mem_univ k)
  rw [hf.2.1.2] at hs
  exact hs

lemma positive_weight_exists {n K : ℕ} (μ : Fin n → ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ)
    (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ) (v : Fin K → ℝ)
    (hf : Feasible19 μ Sig γ L l v) : ∃ k, 0 < v k := by
  by_contra hn
  push Not at hn
  have hz (k : Fin K) : v k = 0 := le_antisymm (hn k) (weights_nonnegative μ Sig γ L l v hf k)
  have hs := hf.2.1.2
  simp only [hz,Finset.sum_const_zero] at hs
  norm_num at hs
end MomentWorstCodex

end


section
set_option autoImplicit false
open Matrix MomentDRO.WorstCov
open scoped MatrixOrder
namespace MomentWorstCodex
lemma psd_zero_column {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (i : ι) (hi : A i i = 0) :
    ∀ j, A j i = 0 := by
  have hq : star (Pi.single i (1 : ℝ)) ⬝ᵥ (A *ᵥ Pi.single i 1) = 0 := by
    simp [dotProduct,mulVec,Pi.single_apply,hi]
  have hz := (hA.dotProduct_mulVec_zero_iff (Pi.single i 1)).mp hq
  intro j
  have hj := congrFun hz j
  simpa [mulVec,dotProduct,Pi.single_apply] using hj

lemma zero_mass_first_moment {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    (l : Fin n → ℝ) (h : (bordered L l 0).PosSemidef) : l = 0 := by
  have hz := psd_zero_column (bordered L l 0) h (Sum.inr (0 : Fin 1)) (by simp [bordered,fromBlocks])
  funext i
  have hi := hz (Sum.inl i)
  simpa [bordered,fromBlocks] using hi
lemma psd_entry_squared {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (i j : ι) : (A i j)^2 ≤ A i i * A j j := by
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hB]
  simpa [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,star_trivial,
    ← sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => B k i) (fun k => B k j)

lemma psd_gram_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) : ∃ B : Matrix ι ι ℝ, A = Bᵀ * B := by
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  exact ⟨B,by simpa [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using hB⟩

end MomentWorstCodex


end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf
namespace MomentWorstCodex
noncomputable def symAtoms {n : ℕ} (μ : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    Fin (n+n) → Fin n → ℝ :=
  Fin.addCases (fun k => μ + Real.sqrt (n : ℝ) • B k) (fun k => μ - Real.sqrt (n : ℝ) • B k)

noncomputable def symLaw {n : ℕ} (μ : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    Measure (Fin n → ℝ) := atomicLaw (symAtoms μ B) (fun _ => (2*(n : ℝ))⁻¹)

lemma sym_weights {n : ℕ} (hn : 0 < n) :
    (∀ i : Fin (n+n), 0 ≤ (2*(n : ℝ))⁻¹) ∧
    (∑ _ : Fin (n+n), (2*(n : ℝ))⁻¹) = 1 := by
  constructor
  · intro i; positivity
  · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add]
    have h : (2*(n : ℝ)) ≠ 0 := by positivity
    rw [show (n : ℝ)+(n : ℝ) = 2*n by ring]
    exact mul_inv_cancel₀ h

lemma sym_second_moments {n : ℕ} (hn : 0 < n) (μ : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    HasSecondMoments (symLaw μ B) :=
  atomic_second_moments _ _ (sym_weights hn).1 (sym_weights hn).2

lemma sym_integral {n : ℕ} (μ : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (f : (Fin n → ℝ) → ℝ) :
    (∫ z, f z ∂symLaw μ B) = (2*(n : ℝ))⁻¹ *
      ∑ k, (f (μ+Real.sqrt (n : ℝ) • B k) + f (μ-Real.sqrt (n : ℝ) • B k)) := by
  rw [symLaw,atomic_integral _ _ (by intro i; positivity)]
  rw [← Finset.mul_sum,Fin.sum_univ_add]
  simp only [symAtoms,Fin.addCases_left,Fin.addCases_right]
  rw [Finset.sum_add_distrib]

lemma sym_mean {n : ℕ} (hn : 0 < n) (μ : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    meanVec (symLaw μ B) = μ := by
  funext i
  change (∫ z, z i ∂symLaw μ B) = μ i
  rw [sym_integral]
  have hsum : (∑ k : Fin n, ((μ+Real.sqrt (n : ℝ) • B k) i + (μ-Real.sqrt (n : ℝ) • B k) i)) =
      (n : ℝ)*(2*μ i) := by
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    simp_rw [show ∀ k : Fin n, μ i+Real.sqrt (n : ℝ)*B k i+(μ i-Real.sqrt (n : ℝ)*B k i) = 2*μ i by intro k; ring]
    simp
  rw [hsum]
  have h : (n : ℝ) ≠ 0 := by positivity
  field_simp

lemma sym_second {n : ℕ} (hn : 0 < n) (μ : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    secondMomentAbout (symLaw μ B) 0 = Matrix.vecMulVec μ μ + Bᵀ*B := by
  ext i j
  change (∫ z, (z i-0)*(z j-0) ∂symLaw μ B) = _
  simp only [sub_zero]
  rw [sym_integral]
  have he (k : Fin n) :
      (μ+Real.sqrt (n : ℝ) • B k) i*(μ+Real.sqrt (n : ℝ) • B k) j +
      (μ-Real.sqrt (n : ℝ) • B k) i*(μ-Real.sqrt (n : ℝ) • B k) j =
        2*μ i*μ j + 2*(n : ℝ)*(B k i*B k j) := by
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    calc
      _ = 2*μ i*μ j + 2*(Real.sqrt (n : ℝ))^2*(B k i*B k j) := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← Finset.mul_sum]
  simp only [Matrix.add_apply,Matrix.vecMulVec_apply,Matrix.mul_apply,Matrix.transpose_apply]
  have h : (n : ℝ) ≠ 0 := by positivity
  field_simp
end MomentWorstCodex

end


section
set_option autoImplicit false
open Matrix MomentDRO.WorstCov
namespace MomentWorstCodex
lemma bordered_quadratic {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    (l q : Fin n → ℝ) (v t : ℝ) :
    (Sum.elim q (fun _ : Fin 1 => t)) ⬝ᵥ
      (bordered L l v *ᵥ Sum.elim q (fun _ : Fin 1 => t)) =
        q ⬝ᵥ (L *ᵥ q) + 2*t*(q ⬝ᵥ l) + v*t^2 := by
  simp [bordered,dotProduct,mulVec,Fintype.sum_sum_type,Fin.sum_univ_one,Matrix.fromBlocks,
    mul_add,add_mul,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]
  change (∑ i, q i*(∑ j, L i j*q j))+t*(∑ i,l i*q i)+
    ((∑ i,q i*(l i*t))+t*(v*t)) =
      (∑ i,q i*(∑ j,L i j*q j))+2*t*(∑ i,q i*l i)+v*t^2
  have hc : (∑ k, l k*q k) = ∑ k, q k*l k := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have ht : (∑ k, q k*(l k*t)) = t*∑ k, q k*l k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hc,ht]
  ring

lemma scaled_covariance_psd {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    (l : Fin n → ℝ) (v : ℝ) (hv : 0 < v) (h : (bordered L l v).PosSemidef) :
    (v⁻¹ • L - Matrix.vecMulVec (v⁻¹ • l) (v⁻¹ • l)).PosSemidef := by
  have htop : (bordered L l v).submatrix Sum.inl Sum.inl = L := by
    ext i j
    simp [bordered,Matrix.submatrix,Matrix.fromBlocks]
  have hL : L.PosSemidef := by
    rw [← htop]
    exact h.submatrix Sum.inl
  have hμ : (Matrix.vecMulVec (v⁻¹ • l) (v⁻¹ • l)).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (v⁻¹ • l)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((hL.smul (inv_nonneg.mpr hv.le)).1.sub hμ.1)
  intro q
  let d := q ⬝ᵥ l
  have hp := h.dotProduct_mulVec_nonneg (Sum.elim q (fun _ : Fin 1 => -(v⁻¹*d)))
  simp only [star_trivial] at hp
  rw [bordered_quadratic] at hp
  change 0 ≤ q ⬝ᵥ (L *ᵥ q)+2*(-(v⁻¹*d))*d+v*(-(v⁻¹*d))^2 at hp
  have he : q ⬝ᵥ (L *ᵥ q)+2*(-(v⁻¹*d))*d+v*(-(v⁻¹*d))^2 =
      q ⬝ᵥ (L *ᵥ q)-v⁻¹*d^2 := by field_simp [hv.ne']; ring
  rw [he] at hp
  have hdot : q ⬝ᵥ (v⁻¹ • l) = v⁻¹*d := by simp [d,dotProduct_smul,smul_eq_mul]
  have hc : q ⬝ᵥ ((v⁻¹ • L - Matrix.vecMulVec (v⁻¹ • l) (v⁻¹ • l)) *ᵥ q) =
      v⁻¹*(q ⬝ᵥ (L *ᵥ q)-v⁻¹*d^2) := by
    rw [sub_mulVec,smul_mulVec,dotProduct_sub,dotProduct_smul,vecMulVec_mulVec,
      dotProduct_smul]
    simp only [smul_eq_mul,op_smul_eq_mul]
    rw [dotProduct_comm (v⁻¹ • l) q,hdot]
    ring
  simp only [star_trivial]
  rw [hc]
  exact mul_nonneg (inv_nonneg.mpr hv.le) hp

end MomentWorstCodex


end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf MomentDRO.WorstCov
namespace MomentWorstCodex
lemma exists_law_mean_cov {n : ℕ} (μ : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.PosSemidef) :
    ∃ P : Measure (Fin n → ℝ), HasSecondMoments P ∧ meanVec P = μ ∧
      secondMomentAbout P 0 = C + Matrix.vecMulVec μ μ := by
  obtain ⟨B,hB⟩ := psd_gram_factor C hC
  by_cases hn : n = 0
  · subst n
    refine ⟨Measure.dirac μ,⟨inferInstance,fun i => Fin.elim0 i⟩,?_,?_⟩
    · funext i; exact Fin.elim0 i
    · ext i j; exact Fin.elim0 i
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    refine ⟨symLaw μ B,sym_second_moments hpos μ B,sym_mean hpos μ B,?_⟩
    rw [sym_second hpos μ B,← hB,add_comm]

theorem exists_law_of_bordered_psd {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (l : Fin n → ℝ)
    (v : ℝ) (hv : 0 < v) (hpsd : (bordered L l v).PosSemidef) :
    ∃ P : Measure (Fin n → ℝ), HasSecondMoments P ∧
      meanVec P = v⁻¹ • l ∧ secondMomentAbout P 0 = v⁻¹ • L := by
  let μ := v⁻¹ • l
  let C := v⁻¹ • L - Matrix.vecMulVec μ μ
  have hc : C.PosSemidef := scaled_covariance_psd L l v hv hpsd
  obtain ⟨P,hP,hmean,hraw⟩ := exists_law_mean_cov μ C hc
  refine ⟨P,hP,hmean,?_⟩
  rw [hraw]
  dsimp [C]
  abel
end MomentWorstCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf MomentDRO.WorstCov
namespace MomentWorstCodex
lemma realize_weighted_blocks {n K : ℕ} (L : Fin K → Matrix (Fin n) (Fin n) ℝ)
    (l : Fin K → Fin n → ℝ) (v : Fin K → ℝ) (hv : ∀ k,0 ≤ v k)
    (hb : ∀ k,(bordered (L k) (l k) (v k)).PosSemidef)
    (hz : ∀ k,v k=0 → L k=0) :
    ∃ P : Fin K → Measure (Fin n → ℝ), (∀ k,HasSecondMoments (P k)) ∧
      (∀ k,v k • meanVec (P k)=l k) ∧ (∀ k,v k • secondMomentAbout (P k) 0=L k) := by
  classical
  have hk (k : Fin K) : ∃ P : Measure (Fin n → ℝ), HasSecondMoments P ∧
      v k • meanVec P=l k ∧ v k • secondMomentAbout P 0=L k := by
    by_cases hp : 0<v k
    · obtain ⟨P,hP,hm,hr⟩ := exists_law_of_bordered_psd (L k) (l k) (v k) hp (hb k)
      refine ⟨P,hP,?_,?_⟩
      · rw [hm,smul_smul,mul_inv_cancel₀ (ne_of_gt hp),one_smul]
      · rw [hr,smul_smul,mul_inv_cancel₀ (ne_of_gt hp),one_smul]
    · have hv0 : v k=0 := le_antisymm (le_of_not_gt hp) (hv k)
      have hl : l k=0 := by
        apply zero_mass_first_moment (L k)
        simpa only [hv0] using hb k
      let P := atomicLaw (fun _ : Fin 1 => (0 : Fin n → ℝ)) (fun _ => (1 : ℝ))
      have hP : HasSecondMoments P := atomic_second_moments _ _ (by simp) (by simp)
      refine ⟨P,hP,?_,?_⟩
      · simp [hv0,hl]
      · simp [hv0,hz k hv0]
  choose P hP hm hr using hk
  exact ⟨P,hP,hm,hr⟩
end MomentWorstCodex

end


section
set_option autoImplicit false
open Matrix MomentDRO.WorstCov
namespace MomentWorstCodex
lemma block_top_psd {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (l : Fin n → ℝ) (v : ℝ)
    (h : (bordered L l v).PosSemidef) : L.PosSemidef := by
  have he : (bordered L l v).submatrix Sum.inl Sum.inl = L := by
    ext i j
    simp [bordered,Matrix.submatrix,Matrix.fromBlocks]
  rw [← he]
  exact h.submatrix Sum.inl

lemma feasible_diagonal_bounds {n K : ℕ} (μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (γ : ℝ) (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ)
    (v : Fin K → ℝ) (hf : Feasible19 μ Sig γ L l v) (k : Fin K) (i : Fin n) :
    0 ≤ L k i i ∧ L k i i ≤ γ*Sig i i+(μ i)^2 := by
  have hn (j : Fin K) : 0 ≤ L j i i := (block_top_psd _ _ _ (hf.2.2 j)).diag_nonneg
  have hs := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ k)
  have hp : (γ • Sig+Matrix.vecMulVec μ μ-∑ j,L j).PosSemidef := hf.1
  have hd : 0 ≤ (γ • Sig+Matrix.vecMulVec μ μ-∑ j,L j) i i := hp.diag_nonneg
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply,Matrix.sum_apply] at hd
  exact ⟨hn k,by nlinarith⟩

lemma feasible_first_squared {n K : ℕ} (μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (γ : ℝ) (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ)
    (v : Fin K → ℝ) (hf : Feasible19 μ Sig γ L l v) (k : Fin K) (i : Fin n) :
    (l k i)^2 ≤ L k i i*v k := by
  have h := psd_entry_squared (bordered (L k) (l k) (v k)) (hf.2.2 k)
    (Sum.inl i) (Sum.inr (0 : Fin 1))
  simpa [bordered,Matrix.fromBlocks] using h

lemma feasible_uniform_bounds {n K : ℕ} (μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (γ : ℝ) (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ)
    (v : Fin K → ℝ) (hf : Feasible19 μ Sig γ L l v) :
    1 ≤ (1+∑ i : Fin n, |γ*Sig i i+(μ i)^2|) ∧
    ∀ k, (∀ i j, |L k i j| ≤ (1+∑ i : Fin n, |γ*Sig i i+(μ i)^2|)) ∧
      (∀ i, |l k i| ≤ (1+∑ i : Fin n, |γ*Sig i i+(μ i)^2|)) ∧
      |v k| ≤ (1+∑ i : Fin n, |γ*Sig i i+(μ i)^2|) := by
  let B := 1+∑ i : Fin n, |γ*Sig i i+(μ i)^2|
  have hB : 1 ≤ B := by
    have hs : 0 ≤ ∑ i : Fin n, |γ*Sig i i+(μ i)^2| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    dsimp [B]
    linarith
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hb (i : Fin n) : γ*Sig i i+(μ i)^2 ≤ B := by
    have hsum := Finset.single_le_sum (fun j _ => abs_nonneg (γ*Sig j j+(μ j)^2)) (Finset.mem_univ i)
    have h := le_abs_self (γ*Sig i i+(μ i)^2)
    dsimp [B]
    linarith
  have hd (k : Fin K) (i : Fin n) : 0 ≤ L k i i ∧ L k i i ≤ B := by
    have h := feasible_diagonal_bounds μ Sig γ L l v hf k i
    exact ⟨h.1,h.2.trans (hb i)⟩
  refine ⟨hB,?_⟩
  intro k
  refine ⟨?_,?_,?_⟩
  · intro i j
    have hp := psd_entry_squared (L k) (block_top_psd _ _ _ (hf.2.2 k)) i j
    have hm := mul_le_mul (hd k i).2 (hd k j).2 (hd k j).1 hB0
    apply abs_le_of_sq_le_sq _ hB0
    nlinarith
  · intro i
    have hp := feasible_first_squared μ Sig γ L l v hf k i
    have hm := mul_le_mul (hd k i).2 (weights_bounded μ Sig γ L l v hf k)
      (weights_nonnegative μ Sig γ L l v hf k) hB0
    apply abs_le_of_sq_le_sq _ hB0
    nlinarith
  · rw [abs_of_nonneg (weights_nonnegative μ Sig γ L l v hf k)]
    exact (weights_bounded μ Sig γ L l v hf k).trans hB

end MomentWorstCodex


end


section
set_option autoImplicit false
open Matrix
namespace MomentWorstCodex
lemma psd_set_closed {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsClosed {A : Matrix ι ι ℝ | A.PosSemidef} := by
  have he : {A : Matrix ι ι ℝ | A.PosSemidef} =
      {A | Aᴴ = A} ∩ ⋂ q : ι → ℝ, {A | 0 ≤ q ⬝ᵥ (A *ᵥ q)} := by
    ext A
    simp [Matrix.posSemidef_iff_dotProduct_mulVec,Matrix.IsHermitian,star_trivial]
  rw [he]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_id
  · apply isClosed_iInter
    intro q
    exact isClosed_le continuous_const (by fun_prop)
end MomentWorstCodex

end


section
set_option autoImplicit false
open Matrix MomentDRO.WorstCov
namespace MomentWorstCodex
abbrev Var19 (n K : ℕ) := (Fin K → Matrix (Fin n) (Fin n) ℝ) ×
  (Fin K → Fin n → ℝ) × (Fin K → ℝ)

def programSet {n K : ℕ} (μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ) :
    Set (Var19 n K) := {z | Feasible19 μ Sig γ z.1 z.2.1 z.2.2}

lemma program_closed {n K : ℕ} (μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ) :
    IsClosed (programSet (K:=K) μ Sig γ) := by
  have hcov : IsClosed {z : Var19 n K | (γ • Sig+Matrix.vecMulVec μ μ-∑ k,z.1 k).PosSemidef} :=
    psd_set_closed.preimage (by fun_prop)
  have hmean : IsClosed {z : Var19 n K | ∑ k,z.2.1 k = μ} := isClosed_eq (by fun_prop) continuous_const
  have hmass : IsClosed {z : Var19 n K | ∑ k,z.2.2 k = 1} := isClosed_eq (by fun_prop) continuous_const
  have hblocks : IsClosed (⋂ k : Fin K, {z : Var19 n K | (bordered (z.1 k) (z.2.1 k) (z.2.2 k)).PosSemidef}) := by
    apply isClosed_iInter
    intro k
    apply psd_set_closed.preimage
    apply continuous_matrix
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · change Continuous (fun z : Var19 n K => z.1 k i j)
      fun_prop
    · change Continuous (fun z : Var19 n K => z.2.1 k i)
      fun_prop
    · change Continuous (fun z : Var19 n K => z.2.1 k j)
      fun_prop
    · change Continuous (fun z : Var19 n K => z.2.2 k)
      fun_prop
  simpa only [programSet,Feasible19,MomentDRO.Conf.LoewnerLE,
    HighDimStat.RandomMatrices.LoewnerLE,Set.ofPred_and,Set.ofPred_forall] using
      hcov.inter ((hmean.inter hmass).inter hblocks)

lemma program_compact {n K : ℕ} (μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ) :
    IsCompact (programSet (K:=K) μ Sig γ) := by
  let B := 1+∑ i : Fin n, |γ*Sig i i+(μ i)^2|
  let C₁ : Set (Fin K → Matrix (Fin n) (Fin n) ℝ) := Set.pi Set.univ (fun _ => (Set.Icc (-B) B).matrix)
  let C₂ : Set (Fin K → Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Set.Icc (-B) B))
  let C₃ : Set (Fin K → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-B) B)
  have hI : IsCompact (Set.Icc (-B) B) := isCompact_Icc
  have hM : IsCompact ((Set.Icc (-B) B).matrix : Set (Matrix (Fin n) (Fin n) ℝ)) := hI.matrix
  have hc₁ : IsCompact C₁ := by
    convert isCompact_pi_infinite (fun _ : Fin K => hM) using 1
    ext z; simp [C₁]
  have hc₂ : IsCompact C₂ := by
    convert isCompact_pi_infinite (fun _ : Fin K => isCompact_pi_infinite (fun _ : Fin n => hI)) using 1
    ext z; simp [C₂,Pi.le_def,forall_and]
  have hc₃ : IsCompact C₃ := by
    convert isCompact_pi_infinite (fun _ : Fin K => hI) using 1
    ext z; simp [C₃,Pi.le_def,forall_and]
  apply (hc₁.prod (hc₂.prod hc₃)).of_isClosed_subset (program_closed (K:=K) μ Sig γ)
  intro z hz
  have hb := (feasible_uniform_bounds μ Sig γ z.1 z.2.1 z.2.2 hz).2
  refine ⟨?_,?_,?_⟩
  · intro k hk
    intro i j
    exact abs_le.mp ((hb k).1 i j)
  · intro k hk i hi
    exact abs_le.mp ((hb k).2.1 i)
  · intro k hk
    exact abs_le.mp ((hb k).2.2)
end MomentWorstCodex

end


section
set_option autoImplicit false
open Matrix MomentDRO.WorstCov
namespace MomentWorstCodex
lemma bordered_zero_psd {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) :
    (bordered S 0 0).PosSemidef := by
  let E : Matrix (Fin n) (Fin n ⊕ Fin 1) ℝ := fun i j =>
    match j with
    | .inl k => if i = k then 1 else 0
    | .inr _ => 0
  have he : Eᴴ*S*E = bordered S 0 0 := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [E,bordered,Matrix.fromBlocks]
  rw [← he]
  exact hS.conjTranspose_mul_mul_same E

lemma bordered_mean_cov_psd {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef)
    (μ : Fin n → ℝ) : (bordered (S+Matrix.vecMulVec μ μ) μ 1).PosSemidef := by
  let w : (Fin n ⊕ Fin 1) → ℝ := Sum.elim μ (fun _ => 1)
  have hw : (Matrix.vecMulVec w w).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star w
  have he : bordered (S+Matrix.vecMulVec μ μ) μ 1 = bordered S 0 0+Matrix.vecMulVec w w := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [w,bordered,Matrix.fromBlocks,Matrix.vecMulVec_apply]
  rw [he]
  exact (bordered_zero_psd S hS).add hw

lemma program_feasible {n K : ℕ} [NeZero K] (μ : Fin n → ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (hSig : Sig.PosSemidef) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ)
      (v : Fin K → ℝ), Feasible19 μ Sig γ L l v := by
  let j := (0 : Fin K)
  let L : Fin K → Matrix (Fin n) (Fin n) ℝ := Pi.single j (γ • Sig+Matrix.vecMulVec μ μ)
  let l : Fin K → Fin n → ℝ := Pi.single j μ
  let v : Fin K → ℝ := Pi.single j 1
  refine ⟨L,l,v,?_,?_,?_⟩
  · change (γ • Sig+Matrix.vecMulVec μ μ-∑ k,L k).PosSemidef
    simpa [L] using (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)
  · constructor <;> simp [l,v]
  · intro k
    by_cases hk : k = j
    · subst k
      simp only [L,l,v,Pi.single_eq_same]
      exact bordered_mean_cov_psd (γ • Sig) (hSig.smul hγ) μ
    · simp only [L,l,v,Pi.single_eq_of_ne hk]
      exact bordered_zero_psd 0 Matrix.PosSemidef.zero
end MomentWorstCodex

end


section
set_option autoImplicit false
open Matrix MomentDRO.WorstCov
namespace MomentWorstCodex
lemma tighten_blocks {n K : ℕ} (μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ)
    (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ) (v : Fin K → ℝ)
    (hf : Feasible19 μ Sig γ L l v) :
    ∃ L' : Fin K → Matrix (Fin n) (Fin n) ℝ,
      Feasible19 μ Sig γ L' l v ∧ ∑ k,L' k = γ • Sig+Matrix.vecMulVec μ μ := by
  classical
  obtain ⟨j,hj⟩ := positive_weight_exists μ Sig γ L l v hf
  let M := γ • Sig+Matrix.vecMulVec μ μ
  let S := M-∑ k,L k
  have hS : S.PosSemidef := hf.1
  let L' : Fin K → Matrix (Fin n) (Fin n) ℝ := fun k => L k+if k=j then S else 0
  have hs : ∑ k,L' k = M := by
    simp only [L',Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    dsimp [S]
    abel
  have hb : Feasible19 μ Sig γ L' l v := by
    refine ⟨?_,hf.2.1,?_⟩
    · change (M-∑ k,L' k).PosSemidef
      rw [hs,sub_self]
      exact Matrix.PosSemidef.zero
    · intro k
      by_cases hk : k=j
      · subst k
        have he : bordered (L j+S) (l j) (v j) =
            bordered (L j) (l j) (v j)+bordered S 0 0 := by
          ext i r
          rcases i with i | i <;> rcases r with r | r <;>
            simp [bordered,Matrix.fromBlocks,Matrix.add_apply]
        simp only [L',ite_true]
        rw [he]
        exact (hf.2.2 j).add (bordered_zero_psd S hS)
      · simp only [L',if_neg hk,add_zero]
        exact hf.2.2 k
  exact ⟨L',hb,hs⟩

theorem exists_optimal_tight {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ)
    (μhat : Fin n → ℝ) (Sighat : Matrix (Fin n) (Fin n) ℝ) (hSig : Sighat.PosDef)
    (γ2 : ℝ) (hγ2 : 0 < γ2) :
    ∃ (Lam : Fin K → Matrix (Fin n) (Fin n) ℝ) (lam : Fin K → Fin n → ℝ) (nu : Fin K → ℝ),
      Feasible19 μhat Sighat γ2 Lam lam nu ∧
        (∀ (Lam' : Fin K → Matrix (Fin n) (Fin n) ℝ) (lam' : Fin K → Fin n → ℝ)
            (nu' : Fin K → ℝ), Feasible19 μhat Sighat γ2 Lam' lam' nu' →
            obj19 a b x lam' nu' ≤ obj19 a b x lam nu) ∧
        ∑ k, Lam k = γ2 • Sighat + Matrix.vecMulVec μhat μhat := by
  have hn : (programSet (K:=K) μhat Sighat γ2).Nonempty := by
    obtain ⟨L,l,v,hf⟩ := program_feasible (K:=K) μhat Sighat hSig.posSemidef γ2 hγ2.le
    exact ⟨(L,l,v),hf⟩
  have hc : Continuous (fun z : Var19 n K => obj19 a b x z.2.1 z.2.2) := by
    unfold obj19
    fun_prop
  obtain ⟨z,hz,hm⟩ := (hc.upperSemicontinuous.upperSemicontinuousOn
    (programSet (K:=K) μhat Sighat γ2)).exists_isMaxOn hn (program_compact (K:=K) μhat Sighat γ2)
  obtain ⟨L,hf,ht⟩ := tighten_blocks μhat Sighat γ2 z.1 z.2.1 z.2.2 hz
  refine ⟨L,z.2.1,z.2.2,hf,?_,ht⟩
  intro L' l' v' h'
  exact isMaxOn_iff.mp hm (L',l',v') h'
end MomentWorstCodex

end


section
set_option autoImplicit false
open Matrix MomentDRO.WorstCov
namespace MomentWorstCodex
lemma remove_zero_mass_covariance {n K : ℕ} (μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (γ : ℝ) (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ)
    (v : Fin K → ℝ) (hf : Feasible19 μ Sig γ L l v) :
    ∃ L' : Fin K → Matrix (Fin n) (Fin n) ℝ,
      Feasible19 μ Sig γ L' l v ∧ ∑ k,L' k = ∑ k,L k ∧ ∀ k, v k = 0 → L' k = 0 := by
  classical
  obtain ⟨j,hj⟩ := positive_weight_exists μ Sig γ L l v hf
  let S := ∑ k : Fin K, if v k=0 then L k else 0
  have hS : S.PosSemidef := by
    apply Matrix.posSemidef_sum
    intro k hk
    split_ifs
    · exact block_top_psd _ _ _ (hf.2.2 k)
    · exact Matrix.PosSemidef.zero
  let L' : Fin K → Matrix (Fin n) (Fin n) ℝ :=
    fun k => (if v k=0 then 0 else L k)+(if k=j then S else 0)
  have hs : ∑ k,L' k = ∑ k,L k := by
    simp only [L',Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    change (∑ k,if v k=0 then 0 else L k)+(∑ k,if v k=0 then L k else 0) = ∑ k,L k
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs <;> simp
  have hz (k : Fin K) (hk : v k=0) : L' k=0 := by
    have hkj : k ≠ j := by intro he; subst k; linarith
    simp [L',hk,hkj]
  have hb (k : Fin K) : (bordered (L' k) (l k) (v k)).PosSemidef := by
    by_cases hk : v k=0
    · have hl : l k=0 := by
        apply zero_mass_first_moment (L k)
        simpa only [hk] using hf.2.2 k
      rw [hz k hk,hl,hk]
      exact bordered_zero_psd 0 Matrix.PosSemidef.zero
    · by_cases hkj : k=j
      · subst k
        simp only [L',if_neg hk,ite_true]
        have he : bordered (L j+S) (l j) (v j) = bordered (L j) (l j) (v j)+bordered S 0 0 := by
          ext i r
          rcases i with i | i <;> rcases r with r | r <;>
            simp [bordered,Matrix.fromBlocks,Matrix.add_apply]
        rw [he]
        exact (hf.2.2 j).add (bordered_zero_psd S hS)
      · simp only [L',if_neg hk,if_neg hkj,add_zero]
        exact hf.2.2 k
  refine ⟨L',⟨?_,hf.2.1,hb⟩,hs,hz⟩
  change (γ • Sig+Matrix.vecMulVec μ μ-∑ k,L' k).PosSemidef
  rw [hs]
  exact hf.1
end MomentWorstCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf MomentDRO.WorstCov
namespace MomentWorstCodex
lemma mixture_value_weighted {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ)
    (l : Fin K → Fin n → ℝ) (v : Fin K → ℝ) (hv : ∀ k,0 ≤ v k)
    (P : Fin K → Measure (Fin n → ℝ)) (hP : ∀ k,HasSecondMoments (P k))
    (hm : ∀ k,v k • meanVec (P k)=l k) :
    obj19 a b x l v ≤ ∫ z,pwCost a b x z ∂mixture v P := by
  rw [mixture_integral v P hv _ (fun k => cost_integrable (hP k) a b x)]
  apply Finset.sum_le_sum
  intro k hk
  have hle : (∫ z,-(a k)*(z ⬝ᵥ x)-b k ∂P k) ≤ ∫ z,pwCost a b x z ∂P k := by
    apply integral_mono (piece_integrable (hP k) a b x k) (cost_integrable (hP k) a b x)
    intro z
    exact Finset.le_sup' (fun j : Fin K => -(a j)*(z ⬝ᵥ x)-b j) (Finset.mem_univ k)
  have hw := mul_le_mul_of_nonneg_left hle (hv k)
  rw [piece_integral (hP k) a b x k] at hw
  have hd : x ⬝ᵥ (v k • meanVec (P k)) = x ⬝ᵥ l k := congrArg (fun q => x ⬝ᵥ q) (hm k)
  rw [dotProduct_smul] at hd
  change v k*(x ⬝ᵥ meanVec (P k)) = x ⬝ᵥ l k at hd
  have he : v k * (-(a k)*(x ⬝ᵥ meanVec (P k))-b k) =
      -(a k)*(x ⬝ᵥ l k)-b k*v k := by
    calc
      _ = -(a k)*(v k*(x ⬝ᵥ meanVec (P k)))-b k*v k := by ring
      _ = _ := by rw [hd]
  rwa [he] at hw
lemma mixture_value {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ)
    (l : Fin K → Fin n → ℝ) (v : Fin K → ℝ) (hv : ∀ k,0<v k)
    (P : Fin K → Measure (Fin n → ℝ)) (hP : ∀ k,HasSecondMoments (P k))
    (hm : ∀ k,meanVec (P k)=(v k)⁻¹ • l k) :
    obj19 a b x l v ≤ ∫ z,pwCost a b x z ∂mixture v P := by
  apply mixture_value_weighted a b x l v (fun k => (hv k).le) P hP
  intro k
  rw [hm k,smul_smul,mul_inv_cancel₀ (ne_of_gt (hv k)),one_smul]
end MomentWorstCodex


end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf MomentDRO.WorstCov
namespace MomentWorstCodex
lemma weighted_mixture_tight {n K : ℕ} (μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ)
    (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ) (v : Fin K → ℝ)
    (hf : Feasible19 μ Sig γ L l v) (ht : ∑ k,L k=γ • Sig+vecMulVec μ μ)
    (P : Fin K → Measure (Fin n → ℝ)) (hP : ∀ k,HasSecondMoments (P k))
    (hm : ∀ k,v k • meanVec (P k)=l k) (hr : ∀ k,v k • secondMomentAbout (P k) 0=L k) :
    mixture v P ∈ D1 Set.univ μ Sig 0 γ ∧ secondMomentAbout (mixture v P) μ=γ • Sig := by
  have hv := weights_nonnegative μ Sig γ L l v hf
  have hmean : meanVec (mixture v P)=μ := by
    rw [weighted_mixture_mean l v hv P hP hm]
    exact hf.2.1.1
  have hraw : secondMomentAbout (mixture v P) 0=γ • Sig+vecMulVec μ μ := by
    rw [weighted_mixture_raw L v hv P hP hr]
    exact ht
  have hsec : HasSecondMoments (mixture v P) := mixture_second_moments v P hv hf.2.1.2 hP
  have hc : secondMomentAbout (mixture v P) μ=γ • Sig := by
    rw [second_about_expansion hsec μ,hmean,hraw]
    abel
  refine ⟨⟨hsec,Filter.Eventually.of_forall (fun _ => Set.mem_univ _),?_,?_⟩,hc⟩
  · simp [hmean,quadForm]
  · rw [hc]
    change (γ • Sig-γ • Sig).PosSemidef
    rw [sub_self]
    exact Matrix.PosSemidef.zero
lemma feasible_law_bound {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x μ : Fin n → ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ)
    (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ) (v : Fin K → ℝ)
    (hf : Feasible19 μ Sig γ L l v) :
    ∃ Q ∈ D1 Set.univ μ Sig 0 γ, obj19 a b x l v ≤ ∫ y,pwCost a b x y ∂Q := by
  obtain ⟨L',hf',ht⟩ := tighten_blocks μ Sig γ L l v hf
  obtain ⟨L'',hf'',hs,hzero⟩ := remove_zero_mass_covariance μ Sig γ L' l v hf'
  have hv := weights_nonnegative μ Sig γ L'' l v hf''
  obtain ⟨P,hP,hm,hr⟩ := realize_weighted_blocks L'' l v hv hf''.2.2 hzero
  have hQ := weighted_mixture_tight μ Sig γ L'' l v hf'' (hs.trans ht) P hP hm hr
  exact ⟨mixture v P,hQ.1,mixture_value_weighted a b x l v hv P hP hm⟩
end MomentWorstCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.Conf MomentDRO.WorstCov
namespace MomentWorstCodex
lemma optimal_values_eq {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ)
    (μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ) (hSig : Sig.PosDef)
    (γ : ℝ) (v : ℝ) :
    IsGreatest {t | ∃ (L : Fin K → Matrix (Fin n) (Fin n) ℝ) (l : Fin K → Fin n → ℝ)
        (nu : Fin K → ℝ), Feasible19 μ Sig γ L l nu ∧ t=obj19 a b x l nu} v ↔
      IsGreatest ((fun Q => ∫ y,pwCost a b x y ∂Q) '' D1 Set.univ μ Sig 0 γ) v := by
  constructor
  · intro h
    obtain ⟨L,l,nu,hf,hv⟩ := h.1
    obtain ⟨P,hP,hPv⟩ := feasible_law_bound a b x μ Sig γ L l nu hf
    have hle : (∫ y,pwCost a b x y ∂P) ≤ v := by
      obtain ⟨L',l',nu',hf',he⟩ := fixed_law_certificate a b x μ Sig hSig γ P hP
      rw [he]
      exact h.2 ⟨L',l',nu',hf',rfl⟩
    refine ⟨⟨P,hP,le_antisymm hle ?_⟩,?_⟩
    · rwa [hv]
    · rintro t ⟨Q,hQ,rfl⟩
      obtain ⟨L',l',nu',hf',he⟩ := fixed_law_certificate a b x μ Sig hSig γ Q hQ
      change (∫ y,pwCost a b x y ∂Q) ≤ v
      rw [he]
      exact h.2 ⟨L',l',nu',hf',rfl⟩
  · intro h
    obtain ⟨P,hP,hv⟩ := h.1
    obtain ⟨L,l,nu,hf,he⟩ := fixed_law_certificate a b x μ Sig hSig γ P hP
    refine ⟨⟨L,l,nu,hf,?_⟩,?_⟩
    · exact hv.symm.trans he
    · rintro t ⟨L',l',nu',hf',rfl⟩
      obtain ⟨Q,hQ,hle⟩ := feasible_law_bound a b x μ Sig γ L' l' nu' hf'
      exact hle.trans (h.2 ⟨Q,hQ,rfl⟩)
end MomentWorstCodex

end


section
set_option autoImplicit false
open MeasureTheory Matrix MomentDRO.WorstCov
theorem solution {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ)
    (μhat : Fin n → ℝ) (Sighat : Matrix (Fin n) (Fin n) ℝ) (hSig : Sighat.PosDef)
    (γ2 : ℝ) (hγ2 : 0 < γ2) (v : ℝ) :
    IsGreatest {t | ∃ (Lam : Fin K → Matrix (Fin n) (Fin n) ℝ) (lam : Fin K → Fin n → ℝ)
        (nu : Fin K → ℝ), Feasible19 μhat Sighat γ2 Lam lam nu ∧ t = obj19 a b x lam nu} v ↔
      IsGreatest ((fun Q => ∫ ξ, pwCost a b x ξ ∂Q) '' D1 Set.univ μhat Sighat 0 γ2) v := MomentWorstCodex.optimal_values_eq a b x μhat Sighat hSig γ2 v


end

#print axioms solution
