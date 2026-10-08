-- Prove2me | solution 1 for MomentDRO.WorstCov.mixture_value_ge
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T06:03:06.071096+00:00
-- url     : https://prove2.me/submissions/9a7e064f-a681-4ff7-a7d2-a4a5e075b922

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
open MeasureTheory Matrix MomentDRO.WorstCov
theorem solution {n K : ℕ} [NeZero K] (a b : Fin K → ℝ) (x : Fin n → ℝ)
    (μhat : Fin n → ℝ) (Sighat : Matrix (Fin n) (Fin n) ℝ) (hSig : Sighat.PosDef)
    (γ2 : ℝ) (hγ2 : 0 < γ2)
    (Lam : Fin K → Matrix (Fin n) (Fin n) ℝ) (lam : Fin K → Fin n → ℝ) (nu : Fin K → ℝ)
    (hfeas : Feasible19 μhat Sighat γ2 Lam lam nu)
    (hpos : ∀ k, 0 < nu k)
    (Pk : Fin K → Measure (Fin n → ℝ)) (hPk : ∀ k, MomentDRO.Conf.HasSecondMoments (Pk k))
    (hmean : ∀ k, MomentDRO.Conf.meanVec (Pk k) = (nu k)⁻¹ • lam k)
    (hsecond : ∀ k, MomentDRO.Conf.secondMomentAbout (Pk k) 0 = (nu k)⁻¹ • Lam k) :
    obj19 a b x lam nu ≤ ∫ ξ, pwCost a b x ξ ∂(mixture nu Pk) := MomentWorstCodex.mixture_value a b x lam nu hpos Pk hPk hmean


end

#print axioms solution
