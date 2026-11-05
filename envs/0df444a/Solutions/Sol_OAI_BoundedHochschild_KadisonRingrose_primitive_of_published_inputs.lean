-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.primitive_of_published_inputs
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:21:37.759192+00:00
-- url     : https://prove2.me/submissions/1d1ea0e5-d0fa-4fa4-b1b9-1752c8f7c622

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_BoundedHochschild_arbitrary_typeII_ordinary_primitive

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section

namespace BoundedHochschild

section AlgebraicAveraging
variable {M : Type*} [NormedRing M] [NormedAlgebra ℂ M]

@[simp] theorem differentialValue_add {n : ℕ} (f g : Cochain M n)
    (v : Fin (n + 1) → M) :
    differentialValue (f + g) v = differentialValue f v + differentialValue g v := by
  simp only [differentialValue, add_apply, mul_add, add_mul,
    smul_add, Finset.sum_add_distrib]
  abel

@[simp] theorem differentialValue_smul {n : ℕ} (c : ℂ) (f : Cochain M n)
    (v : Fin (n + 1) → M) :
    differentialValue (c • f) v = c • differentialValue f v := by
  simp only [differentialValue, smul_apply, smul_mul_assoc,
    mul_smul_comm, smul_add, Finset.smul_sum, smul_smul]
  congr 2
  · apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm c]
  · rw [mul_comm c]

end AlgebraicAveraging

section TupleIdentities
variable {M : Type*}

@[simp] theorem mergeInputs_snoc_castSucc [Mul M] {n : ℕ} (v : Fin (n + 1) → M)
    (u : M) (j : Fin n) :
    mergeInputs (Fin.snoc v u) j.castSucc = Fin.snoc (mergeInputs v j) u := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · have hlt : ¬ Fin.last n < j.castSucc := by
      simp only [Fin.lt_def, Fin.val_last, Fin.val_castSucc]
      omega
    have heq : Fin.last n ≠ j.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      omega
    simp [mergeInputs, hlt, heq]
  · simp [mergeInputs, ← Fin.castSucc_succ]

@[simp] theorem mergeInputs_snoc_last [Mul M] {n : ℕ} (v : Fin (n + 1) → M) (u : M) :
    mergeInputs (Fin.snoc v u) (Fin.last n) =
      Fin.snoc (fun i : Fin n => v i.castSucc) (v (Fin.last n) * u) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [mergeInputs]
  · simp [mergeInputs]
end TupleIdentities
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

theorem bounded_cochain_ultralimit {n : ℕ} (u : Ultrafilter I)
    (F : I → Cochain M n) (C : ℝ) (hC : 0 ≤ C) (hF : ∀ i, ‖F i‖ ≤ C) :
    ∃ G : Cochain M n, ‖G‖ ≤ C ∧
      ∀ x, PredualTendsto e (fun i => F i x) u (G x) := by
  classical
  have hex (x : Fin n → M) : ∃ b : M, ‖b‖ ≤ C * ∏ k, ‖x k‖ ∧
      PredualTendsto e (fun i => F i x) u b :=
    exists_predual_ultralimit e u (fun i => F i x) _ (fun i =>
      (F i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hF i)
        (Finset.prod_nonneg (fun k _ => norm_nonneg (x k)))))
  choose b hb ht using hex
  let G₀ : MultilinearMap ℂ (fun _ : Fin n => M) M :=
    { toFun := b
      map_update_add' := fun x k a c => by
        apply predual_tendsto_unique e (ht (Function.update x k (a+c)))
        simpa only [ContinuousMultilinearMap.map_update_add] using
          predual_tendsto_add e (ht (Function.update x k a)) (ht (Function.update x k c))
      map_update_smul' := fun x k c a => by
        apply predual_tendsto_unique e (ht (Function.update x k (c • a)))
        simpa only [ContinuousMultilinearMap.map_update_smul] using
          predual_tendsto_smul e (ht (Function.update x k a)) c }
  exact ⟨G₀.mkContinuous C hb, G₀.mkContinuous_norm_le hC hb, ht⟩

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M X I J : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma predual_tendsto_of_norm {a : I → M} {l : Filter I} {b : M}
    (h : Tendsto a l (𝓝 b)) : PredualTendsto e a l b := by
  intro z
  exact (((ContinuousLinearMap.apply ℂ ℂ) z).continuous.tendsto _).comp
    (e.symm.continuous.tendsto _ |>.comp h)
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

namespace HochschildRigidity
open Finset

section FourierWindows
variable {L : ℕ} [NeZero L]

end FourierWindows

section TraceHilbertSpace
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ)

lemma preGNS_norm_star (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (a : A) :
    ‖τ.toPreGNS (star a)‖ = ‖τ.toPreGNS a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply Complex.ofReal_injective
  push_cast
  simp only [τ.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS, star_star]
  exact htr _ _
lemma preGNS_norm_mul_right_le (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (a b : A) :
    ‖τ.toPreGNS (a * b)‖ ≤ ‖b‖ * ‖τ.toPreGNS a‖ := by
  rw [← preGNS_norm_star τ htr, star_mul]
  exact (preGNS_norm_mul_le τ (star b) (star a)).trans_eq
    (by rw [norm_star, preGNS_norm_star τ htr])
end TraceHilbertSpace
end HochschildRigidity
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
namespace HochschildUltrapower
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open TracialUltrapower HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
include h1

lemma norm_trace_le (a : A) : ‖τ a‖ ≤ ‖τ.toPreGNS a‖ := by
  have hin : inner ℂ (τ.toPreGNS 1) (τ.toPreGNS a) = τ a := by
    simp [PositiveLinearMap.preGNS_inner_def]
  rw [← hin]
  have hone : ‖τ.toPreGNS 1‖ = 1 := by
    rw [PositiveLinearMap.preGNS_norm_def]
    simp [h1]
  simpa only [hone,one_mul] using norm_inner_le_norm (𝕜 := ℂ) (τ.toPreGNS 1) (τ.toPreGNS a)
end HochschildUltrapower
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

lemma preGNS_zero_of_predual_limit
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hτ : TraceInPredual e τ) {a : I → M} {l : Filter I} [l.NeBot] {b : M}
    (ha : Tendsto (fun i => ‖τ.toPreGNS (a i)‖) l (𝓝 0))
    (hb : PredualTendsto e a l b) : ‖τ.toPreGNS b‖ = 0 := by
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  simpa only [zero_add] using preGNS_norm_le_of_predual_tendsto e τ hL hτ ε hε.le
    (ha.eventually (ge_mem_nhds hε)) hb

theorem predual_tendsto_of_preGNS
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hτ : TraceInPredual e τ) (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {a : I → M} {l : Filter I} (C : ℝ) (ha : ∀ i, ‖a i‖ ≤ C) {b : M}
    (hb : Tendsto (fun i => ‖τ.toPreGNS (a i-b)‖) l (𝓝 0)) :
    PredualTendsto e a l b := by
  intro z
  apply (tendsto_iff_ultrafilter _ _ _).mpr
  intro u hu
  obtain ⟨c,_hc,ht⟩ := exists_predual_ultralimit e u a C ha
  have hzero := preGNS_zero_of_predual_limit e τ hL hτ (hb.mono_left hu)
    (predual_tendsto_sub e ht (predual_tendsto_const e b (u : Filter I)))
  have hcb : c=b := by
    apply sub_eq_zero.mp
    exact (preGNS_norm_eq_zero_iff τ hfaith (c-b)).mp hzero
  simpa only [hcb] using ht z

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (τ : M →ₚ[ℂ] ℂ)

def GNSTendsto (a : I → M) (l : Filter I) (b : M) : Prop :=
  Tendsto (fun i => ‖τ.toPreGNS (a i-b)‖) l (𝓝 0)

lemma GNSTendsto.const (b : M) (l : Filter I) : GNSTendsto τ (fun _ => b) l b := by
  simp only [GNSTendsto,sub_self,map_zero,norm_zero]
  exact tendsto_const_nhds

lemma GNSTendsto.add {a c : I → M} {l : Filter I} {b d : M}
    (ha : GNSTendsto τ a l b) (hc : GNSTendsto τ c l d) :
    GNSTendsto τ (fun i => a i+c i) l (b+d) := by
  apply squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) (by simpa only [add_zero] using Filter.Tendsto.add ha hc)
  rw [show a i+c i-(b+d)=(a i-b)+(c i-d) by abel,map_add]
  exact norm_add_le _ _

lemma GNSTendsto.neg {a : I → M} {l : Filter I} {b : M} (ha : GNSTendsto τ a l b) :
    GNSTendsto τ (fun i => -a i) l (-b) := by
  simpa only [GNSTendsto,neg_sub_neg,← neg_sub (a := b),map_neg,norm_neg] using ha

lemma GNSTendsto.sub {a c : I → M} {l : Filter I} {b d : M}
    (ha : GNSTendsto τ a l b) (hc : GNSTendsto τ c l d) :
    GNSTendsto τ (fun i => a i-c i) l (b-d) := by
  simpa only [sub_eq_add_neg] using ha.add τ (hc.neg τ)

lemma GNSTendsto.mul (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    {a c : I → M} {l : Filter I} {b d : M}
    (ha : GNSTendsto τ a l b) (hc : GNSTendsto τ c l d)
    (C : ℝ) (hC : ∀ i, ‖a i‖ ≤ C) :
    GNSTendsto τ (fun i => a i*c i) l (b*d) := by
  have ht := (hc.const_mul C).add (ha.const_mul ‖d‖)
  simp only [mul_zero,add_zero] at ht
  apply squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) ht
  rw [show a i*c i-b*d=a i*(c i-d)+(a i-b)*d by noncomm_ring,map_add]
  exact (norm_add_le _ _).trans (add_le_add
    ((preGNS_norm_mul_le τ _ _).trans (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)))
    (preGNS_norm_mul_right_le τ htr _ _))

lemma GNSTendsto.unique (hfaith : ∀ a : M, τ (Star.star a*a)=0 → a=0)
    {a : I → M} {l : Filter I} [l.NeBot] {b c : M}
    (hb : GNSTendsto τ a l b) (hc : GNSTendsto τ a l c) : b=c := by
  have h : GNSTendsto τ (fun _ : I => (0:M)) l (b-c) := by
    simpa only [sub_self] using hb.sub τ hc
  have hz : ‖τ.toPreGNS (b-c)‖=0 := by
    have ht : Tendsto (fun _ : I => ‖τ.toPreGNS (b-c)‖) l (𝓝 0) := by
      simpa only [GNSTendsto,zero_sub,map_neg,norm_neg] using h
    exact tendsto_nhds_unique tendsto_const_nhds ht
  exact sub_eq_zero.mp ((preGNS_norm_eq_zero_iff τ hfaith _).mp hz)

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (Star.star a*a)=0 → a=0)

include hL hτ hfaith in
lemma GNSTendsto.predual {a : ℕ → M} {b : M} (C : ℝ) (ha : ∀ n, ‖a n‖ ≤ C)
    (ht : GNSTendsto τ a atTop b) : PredualTendsto e a atTop b :=
  predual_tendsto_of_preGNS e τ hL hτ hfaith C ha ht

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (Star.star a*a)=0 → a=0)

lemma IsSupportProjection.le_of_support {a p q : M} (hp : IsSupportProjection a p)
    (hq : IsStarProjection q) (haq : a*q=a) : p ≤ q := by
  apply (hp.proj.le_iff_mul_eq_left hq).mpr
  have hh := hp.annihilate (1-q) (by simp only [mul_sub,mul_one,haq,sub_self])
  simpa only [mul_sub,mul_one,sub_eq_zero,eq_comm] using hh
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (Star.star a*a)=0 → a=0)

end BoundedHochschild

open scoped NNReal
namespace BoundedHochschild
variable {M I : Type*} [CStarAlgebra M]

lemma mul_eq_zero_of_supports (x y p q : M) (hxp : x*p=x) (hqy : q*y=y) (hpq : p*q=0) :
    x*y=0 := by
  calc
    x*y=(x*p)*(q*y) := by rw [hxp,hqy]
    _=x*(p*q)*y := by simp only [mul_assoc]
    _=0 := by rw [hpq,mul_zero,zero_mul]

lemma orthogonal_blocks_norm_sum_le (t : I → M)
    (hleft : ∀ i j, i ≠ j → star (t i)*t j=0)
    (hright : ∀ i j, i ≠ j → t i*star (t j)=0)
    (s : Finset I) (R : ℝ) (hR : 0 ≤ R) (ht : ∀ i ∈ s, ‖t i‖ ≤ R) :
    ‖∑ i ∈ s, t i‖ ≤ R := by
  classical
  have hdiag : star (∑ i ∈ s, t i)*(∑ i ∈ s, t i) = ∑ i ∈ s, star (t i)*t i := by
    simp only [star_sum,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_eq_single i (fun j _hj hji => hleft j i hji) (fun h => (h hi).elim)
  have horth : Pairwise (fun i j => (star (t i)*t i)*(star (t j)*t j)=0) := by
    intro i j hij
    calc
      (star (t i)*t i)*(star (t j)*t j) = star (t i)*(t i*star (t j))*t j := by simp only [mul_assoc]
      _ = 0 := by rw [hright i j hij,mul_zero,zero_mul]
  have hs := IsSelfAdjoint.nnnorm_sum_eq_sup s (fun i _hi => IsSelfAdjoint.star_mul_self (t i)) horth
  have hbound : ‖∑ i ∈ s, star (t i)*t i‖₊ ≤ (⟨R^2,sq_nonneg R⟩ : ℝ≥0) := by
    rw [hs]
    apply Finset.sup_le
    intro i hi
    change ‖star (t i)*t i‖ ≤ R^2
    rw [CStarRing.norm_star_mul_self]
    nlinarith [ht i hi,norm_nonneg (t i)]
  change ‖∑ i ∈ s, star (t i)*t i‖ ≤ R^2 at hbound
  rw [← hdiag,CStarRing.norm_star_mul_self] at hbound
  nlinarith [norm_nonneg (∑ i ∈ s, t i)]

lemma supported_sum_norm_le (p t : I → M) (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i*p j=0)
    (hpt : ∀ i, p i*t i=t i) (htp : ∀ i, t i*p i=t i)
    (s : Finset I) (R : ℝ) (hR : 0 ≤ R) (ht : ∀ i ∈ s, ‖t i‖ ≤ R) :
    ‖∑ i ∈ s, t i‖ ≤ R := by
  apply orthogonal_blocks_norm_sum_le t _ _ s R hR ht
  · intro i j hij
    apply mul_eq_zero_of_supports _ _ (p i) (p j) _ (hpt j) (horth i j hij)
    simpa only [star_mul,(hp i).isSelfAdjoint.star_eq] using congrArg Star.star (hpt i)
  · intro i j hij
    apply mul_eq_zero_of_supports _ _ (p i) (p j) (htp i) _ (horth i j hij)
    simpa only [star_mul,(hp j).isSelfAdjoint.star_eq] using congrArg Star.star (htp j)
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open Filter Topology
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

def centralCut {n : ℕ} (z : M) (f : Cochain M n) : Cochain M n :=
  f.compContinuousLinearMap (fun _ => ContinuousLinearMap.mul ℂ M z)

@[simp] lemma centralCut_apply {n : ℕ} (z : M) (f : Cochain M n) (v : Fin n → M) :
    centralCut z f v = f (fun i => z*v i) := rfl

lemma central_mul_assoc (z : M) (hz : ∀ a, z*a=a*z) (a b : M) :
    a*(z*b) = z*(a*b) := by rw [← mul_assoc, ← hz, mul_assoc]

lemma central_idempotent_mul (z : M) (hi : z*z=z) (hz : ∀ a, z*a=a*z) (a b : M) :
    (z*a)*(z*b) = z*(a*b) := by
  rw [mul_assoc, central_mul_assoc z hz, ← mul_assoc z z, hi]

end BoundedHochschild

namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

end BoundedHochschild

namespace BoundedHochschild
variable {M : Type*}

def tupleInsert {n : ℕ} (p : Fin (n+1)) (a : M) (v : Fin n → M) (i : Fin (n+1)) : M :=
  if h : i.val < p.val then v ⟨i.val, by omega⟩
  else if h : i = p then a else v ⟨i.val-1, by have := i.isLt; have := p.isLt; omega⟩

lemma tupleInsert_eq {n : ℕ} (p : Fin (n+1)) (a : M) (v : Fin n → M) :
    tupleInsert p a v = p.insertNth a v := by
  apply (Fin.eq_insertNth_iff).mpr
  constructor
  · simp [tupleInsert]
  · funext i
    change tupleInsert p a v (p.succAbove i) = v i
    by_cases h : i.castSucc < p
    · rw [Fin.succAbove_of_castSucc_lt _ _ h]
      dsimp [tupleInsert]
      rw [dite_eq_left (show i.val < p.val from h)]
    · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt h)]
      dsimp [tupleInsert]
      rw [dite_eq_right (by change ¬i.val < p.val at h; omega),
        ite_eq_right (by intro he; have hv := congrArg Fin.val he; dsimp at hv; change ¬i.val < p.val at h; omega)]

lemma tupleInsert_lt {n : ℕ} (p : Fin (n+1)) (a : M) (v : Fin n → M)
    (i : Fin (n+1)) (h : i.val < p.val) :
    Fin.insertNth (α := fun _ => M) p a v i = v ⟨i.val, by omega⟩ := by
  rw [← tupleInsert_eq]
  simp only [tupleInsert, dite_eq_left h]

lemma tupleInsert_gt {n : ℕ} (p : Fin (n+1)) (a : M) (v : Fin n → M)
    (i : Fin (n+1)) (h : p.val < i.val) :
    Fin.insertNth (α := fun _ => M) p a v i = v ⟨i.val-1, by have := i.isLt; omega⟩ := by
  rw [← tupleInsert_eq]
  simp only [tupleInsert, dite_eq_right (by omega : ¬i.val < p.val),
    dite_eq_right (by intro he; have := congrArg Fin.val he; omega : i ≠ p)]

lemma merge_insert_same [Mul M] {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1)) (q : M)
    (hq : q*v r=v r) : mergeInputs (r.castSucc.insertNth q v) r = v := by
  funext i
  simp only [mergeInputs]
  split_ifs with h h
  · rw [tupleInsert_lt _ _ _ _ (by simpa only [Fin.val_castSucc, Fin.lt_def] using h)]
    rfl
  · subst i
    rw [Fin.insertNth_apply_same, tupleInsert_gt _ _ _ _ (by simp)]
    simpa using hq
  · rw [tupleInsert_gt _ _ _ _ (by simpa only [Fin.val_castSucc,Fin.val_succ] using
        (show r.val < i.val+1 by omega))]
    rfl

lemma merge_insert_before [Mul M] {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1))
    (q : M) (j : Fin n) (hjr : j.val+1 < r.val) :
    mergeInputs (r.castSucc.insertNth q v) (r.succAbove j) =
      (⟨r.val-1, by omega⟩ : Fin (n+1)).insertNth q (mergeInputs v j) := by
  have hs : r.succAbove j=j.castSucc := by
    exact Fin.succAbove_of_castSucc_lt _ _ (by simpa only [Fin.lt_def, Fin.val_castSucc] using (show j.val < r.val by omega))
  rw [hs]
  funext i
  simp only [mergeInputs, ← tupleInsert_eq, tupleInsert, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ, Fin.ext_iff]
  split_ifs <;> try omega
  all_goals first | rfl | congr 1
  all_goals exact Fin.ext (by dsimp; omega)

lemma merge_insert_after [Mul M] {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1))
    (q : M) (j : Fin n) (hjr : r.val ≤ j.val) :
    mergeInputs (r.castSucc.insertNth q v) (r.succAbove j) =
      (⟨r.val, by omega⟩ : Fin (n+1)).insertNth q (mergeInputs v j) := by
  have hs : r.succAbove j=j.succ := by
    exact Fin.succAbove_of_le_castSucc _ _ (by simpa only [Fin.le_def, Fin.val_castSucc] using hjr)
  rw [hs]
  funext i
  simp only [mergeInputs, ← tupleInsert_eq, tupleInsert, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ, Fin.ext_iff]
  split_ifs <;> try omega
  all_goals first | rfl | congr 1
  all_goals first | rfl | (apply Fin.ext; dsimp; omega) |
    (apply congrArg v; apply Fin.ext; dsimp; omega)

lemma tail_insert {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1)) (q : M)
    (hr : 0 < r.val) :
    (fun i : Fin (n+1) => (r.castSucc.insertNth (α := fun _ => M) q v) i.succ) =
    (⟨r.val-1, by omega⟩ : Fin (n+1)).insertNth (α := fun _ => M) q (fun i => v i.succ) := by
  funext i
  simp only [← tupleInsert_eq, tupleInsert, Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]
  split_ifs <;> try omega
  all_goals first | rfl | congr 1
  all_goals exact Fin.ext (by dsimp; omega)

lemma init_insert {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1)) (q : M) :
    (fun i : Fin (n+1) => (r.castSucc.insertNth (α := fun _ => M) q v) i.castSucc) =
    r.insertNth (α := fun _ => M) q (fun i => v i.castSucc) := by
  funext i
  simp only [← tupleInsert_eq, tupleInsert, Fin.val_castSucc, Fin.ext_iff]
  split_ifs <;> rfl

lemma last_insert {n : ℕ} (v : Fin (n+1) → M) (r : Fin (n+1)) (q : M) :
    (r.castSucc.insertNth (α := fun _ => M) q v) (Fin.last (n+1)) = v (Fin.last n) := by
  rw [tupleInsert_gt _ _ _ _ (by simp only [Fin.val_castSucc,Fin.val_last]; omega)]
  rfl

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

def centralJTerm {n : ℕ} (z q : M) (f : Cochain M (n+1)) (i : Fin n) : Cochain M n :=
  (f.curryMid i.castSucc q).compContinuousLinearMap (fun j =>
    if j < i then ContinuousLinearMap.mul ℂ M z
    else if j = i then ContinuousLinearMap.mul ℂ M q
    else ContinuousLinearMap.id ℂ M)

@[simp] lemma centralJTerm_apply {n : ℕ} (z q : M) (f : Cochain M (n+1))
    (i : Fin n) (v : Fin n → M) :
    centralJTerm z q f i v = f (i.castSucc.insertNth q (fun j =>
      if j < i then z*v j else if j = i then q*v j else v j)) := by
  change f (i.castSucc.insertNth q (fun j => (if j < i then ContinuousLinearMap.mul ℂ M z
    else if j = i then ContinuousLinearMap.mul ℂ M q else ContinuousLinearMap.id ℂ M) (v j))) = _
  apply congrArg (fun w => f (i.castSucc.insertNth q w))
  funext j
  split_ifs <;> rfl

def centralJ {n : ℕ} (z q : M) (f : Cochain M (n+1)) : Cochain M n :=
  ∑ i : Fin n, ((-1:ℂ)^(i.val+1)) • centralJTerm z q f i

lemma norm_centralJTerm_le {n : ℕ} (z q : M) (hz : ‖z‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    (f : Cochain M (n+1)) (i : Fin n) : ‖centralJTerm z q f i‖ ≤ ‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro v
  rw [centralJTerm_apply]
  apply (f.norm_map_insertNth_le _ _).trans
  calc
    ‖f‖ * ‖q‖ * (∏ j, ‖if j < i then z*v j else if j = i then q*v j else v j‖) ≤
        ‖f‖ * 1 * (∏ j, ‖v j‖) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hq (norm_nonneg _)
      · apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro j _
        split_ifs
        · exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (v j)])
        · exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (v j)])
        · rfl
      · positivity
      · positivity
    _ = _ := by ring

lemma norm_centralJ_le {n : ℕ} (z q : M) (hz : ‖z‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    (f : Cochain M (n+1)) : ‖centralJ z q f‖ ≤ n*‖f‖ := by
  apply (norm_sum_le _ _).trans
  calc
    ∑ i : Fin n, ‖((-1:ℂ)^(i.val+1)) • centralJTerm z q f i‖ ≤
        ∑ _ : Fin n, ‖f‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        using norm_centralJTerm_le z q hz hq f i
    _ = _ := by simp

lemma centralJ_range {n : ℕ} (z q : M) (f : Cochain M (n+1))
    (hr : ∀ v, z*f v=f v) (v : Fin n → M) : z*centralJ z q f v=centralJ z q f v := by
  simp only [centralJ, sum_apply, smul_apply, centralJTerm_apply, Finset.mul_sum,
    mul_smul_comm, hr]

lemma centralJTerm_eq_zero_lt {n : ℕ} (z q : M) (hzq : q*z=0)
    (f : Cochain M (n+1)) (i r : Fin n) (hir : i < r) (v : Fin n → M)
    (hv : ∀ j, j < r → z*v j=v j) : centralJTerm z q f i v=0 := by
  have hqi : q*v i=0 := by rw [← hv i hir, ← mul_assoc, hzq, zero_mul]
  rw [centralJTerm_apply]
  apply f.map_coord_zero ((i.castSucc).succAbove i)
  simp only [Fin.insertNth_apply_succAbove, lt_self_iff_false, ite_false, ite_true, hqi]

lemma centralJTerm_eq_zero_gt {n : ℕ} (z q : M) (hzq : z*q=0)
    (f : Cochain M (n+1)) (i r : Fin n) (hri : r < i) (v : Fin n → M)
    (hv : q*v r=v r) : centralJTerm z q f i v=0 := by
  have hzr : z*v r=0 := by rw [← hv, ← mul_assoc, hzq, zero_mul]
  rw [centralJTerm_apply]
  apply f.map_coord_zero ((i.castSucc).succAbove r)
  simp only [Fin.insertNth_apply_succAbove, hri, ite_true, hzr]

lemma centralJ_first_q {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (f : Cochain M (n+1)) (r : Fin n) (v : Fin n → M)
    (hv : ∀ j, j < r → z*v j=v j) (hvr : q*v r=v r) :
    centralJ z q f v = ((-1:ℂ)^(r.val+1)) • f (r.castSucc.insertNth q v) := by
  classical
  rw [centralJ, sum_apply, Finset.sum_eq_single r]
  · simp only [smul_apply, centralJTerm_apply]
    apply congrArg (fun w => ((-1:ℂ)^(r.val+1)) • f (r.castSucc.insertNth q w))
    funext j
    split_ifs with h h
    · exact hv j h
    · subst j; exact hvr
    · rfl
  · intro i _ hir
    rw [smul_apply]
    have hi : centralJTerm z q f i v=0 := by
      rcases lt_or_gt_of_ne hir with h | h
      · exact centralJTerm_eq_zero_lt z q hqz f i r h v hv
      · exact centralJTerm_eq_zero_gt z q hzq f i r h v hvr
    rw [hi, smul_zero]
  · simp

lemma centralJ_all_z {n : ℕ} (z q : M) (hqz : q*z=0)
    (f : Cochain M (n+1)) (v : Fin n → M) (hv : ∀ j, z*v j=v j) :
    centralJ z q f v=0 := by
  rw [centralJ, sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  simp only [smul_apply]
  have hi : centralJTerm z q f i v=0 := by
    have hqi : q*v i=0 := by rw [← hv i, ← mul_assoc, hqz, zero_mul]
    rw [centralJTerm_apply]
    apply f.map_coord_zero ((i.castSucc).succAbove i)
    simp only [Fin.insertNth_apply_succAbove, lt_self_iff_false, ite_false, ite_true, hqi]
  rw [hi, smul_zero]

end BoundedHochschild

namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

lemma centralJ_merge_before {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (f : Cochain M (n+1)) (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i < r → z*v i=v i) (hvr : q*v r=v r) (j : Fin n)
    (hjr : j.val+1 < r.val) :
    centralJ z q f (mergeInputs v j) = ((-1:ℂ)^r.val) •
      f (mergeInputs (r.castSucc.insertNth (α := fun _ => M) q v) (r.succAbove j)) := by
  rw [merge_insert_before v r q j hjr]
  let r' : Fin n := ⟨r.val-1, by omega⟩
  have hh : ∀ i, i < r' → z*mergeInputs v j i=mergeInputs v j i := by
    intro i hi
    simp only [mergeInputs]
    split_ifs with h h
    · exact hv i.castSucc (by simp only [Fin.lt_def, Fin.val_castSucc] at *; omega)
    · subst i
      rw [← mul_assoc, hv j.castSucc (by simp only [Fin.lt_def, Fin.val_castSucc]; omega)]
    · exact hv i.succ (by simp only [r', Fin.lt_def,Fin.val_succ] at *; omega)
  have hq : q*mergeInputs v j r'=mergeInputs v j r' := by
    have hlo : ¬r' < j := by simp only [r', Fin.lt_def]; omega
    have hne : r' ≠ j := by intro h; have hh := congrArg Fin.val h; dsimp [r'] at hh; omega
    have he : r'.succ=r := Fin.ext (by dsimp [r']; omega)
    simp only [mergeInputs, hlo, hne, ite_false, he]
    exact hvr
  rw [centralJ_first_q z q hzq hqz f r' _ hh hq]
  have he : r'.val+1=r.val := by dsimp [r']; omega
  rw [he]
  rfl

lemma centralJ_merge_after {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (f : Cochain M (n+1)) (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i < r → z*v i=v i) (hvr : q*v r=v r) (j : Fin n)
    (hjr : r.val ≤ j.val) :
    centralJ z q f (mergeInputs v j) = ((-1:ℂ)^(r.val+1)) •
      f (mergeInputs (r.castSucc.insertNth (α := fun _ => M) q v) (r.succAbove j)) := by
  rw [merge_insert_after v r q j hjr]
  let r' : Fin n := ⟨r.val, by omega⟩
  have hh : ∀ i, i < r' → z*mergeInputs v j i=mergeInputs v j i := by
    intro i hi
    have hh : i<j := by simp only [r', Fin.lt_def] at *; omega
    simp only [mergeInputs, hh, ite_true]
    exact hv i.castSucc (by simpa only [r', Fin.lt_def,Fin.val_castSucc] using hi)
  have hq : q*mergeInputs v j r'=mergeInputs v j r' := by
    have he : r'.castSucc=r := rfl
    simp only [mergeInputs]
    split_ifs with hlt heq
    · simpa only [he] using hvr
    · rw [he, ← mul_assoc, hvr]
    · exfalso
      apply heq
      apply Fin.ext
      change r.val = j.val
      change ¬r.val < j.val at hlt
      omega
  exact centralJ_first_q z q hzq hqz f r' _ hh hq

lemma centralJ_merge_boundary {n : ℕ} (z q : M) (hzq : z*q=0) (hz : ∀ a, z*a=a*z)
    (f : Cochain M (n+1)) (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i < r → z*v i=v i) (hvr : q*v r=v r) (j : Fin n)
    (hjr : j.val+1 = r.val) :
    centralJ z q f (mergeInputs v j)=0 ∧
      f (mergeInputs (r.castSucc.insertNth (α := fun _ => M) q v) (r.succAbove j))=0 := by
  have hjr' : j.succ=r := Fin.ext hjr
  have hlt : j.castSucc<r := by simp only [Fin.lt_def, Fin.val_castSucc]; omega
  have hvj : v j.castSucc*q=0 := by
    rw [← hv _ hlt, mul_assoc, ← central_mul_assoc z hz, hzq, mul_zero]
  constructor
  · apply (centralJ z q f).map_coord_zero j
    simp only [mergeInputs, lt_self_iff_false, ite_false, ite_true, hjr']
    rw [← hvr, ← mul_assoc, hvj, zero_mul]
  · apply f.map_coord_zero j.castSucc
    have hes : r.succAbove j=j.castSucc := Fin.succAbove_of_castSucc_lt _ _ hlt
    rw [hes]
    simp only [mergeInputs, lt_self_iff_false, ite_false, ite_true]
    rw [tupleInsert_lt _ _ _ _ (by simpa only [Fin.val_castSucc] using (show j.val<r.val by omega))]
    have he : j.castSucc.succ=r.castSucc := Fin.ext (by simp only [Fin.val_succ,Fin.val_castSucc]; omega)
    rw [he, Fin.insertNth_apply_same]
    exact hvj

lemma centralJ_inner_cancellation {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (hz : ∀ a, z*a=a*z) (f : Cochain M (n+1)) (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i < r → z*v i=v i) (hvr : q*v r=v r) (j : Fin n) :
    ((-1:ℂ)^(r.val+1)) • (((-1:ℂ)^((r.succAbove j).val+1)) •
      f (mergeInputs (r.castSucc.insertNth (α := fun _ => M) q v) (r.succAbove j))) =
        - (((-1:ℂ)^(j.val+1)) • centralJ z q f (mergeInputs v j)) := by
  rcases lt_trichotomy (j.val+1) r.val with h | h | h
  · rw [centralJ_merge_before z q hzq hqz f v r hv hvr j h]
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def,Fin.val_castSucc]; omega)]
    simp only [Fin.val_castSucc, smul_smul, ← neg_smul]
    congr 1
    rw [pow_succ]
    ring
  · obtain ⟨h₁,h₂⟩ := centralJ_merge_boundary z q hzq hz f v r hv hvr j h
    rw [h₁,h₂,smul_zero,smul_zero,smul_zero,neg_zero]
  · have hrj : r.val ≤ j.val := by omega
    rw [centralJ_merge_after z q hzq hqz f v r hv hvr j hrj]
    rw [Fin.succAbove_of_le_castSucc _ _ (by simpa only [Fin.le_def,Fin.val_castSucc] using hrj)]
    simp only [Fin.val_succ, smul_smul, ← neg_smul, pow_succ]
    congr 1
    ring

lemma centralJ_left_cancellation {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (hz : ∀ a, z*a=a*z) (f : Cochain M (n+1)) (hr : ∀ w, z*f w=f w)
    (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i < r → z*v i=v i) (hvr : q*v r=v r) :
    ((-1:ℂ)^(r.val+1)) • ((r.castSucc.insertNth (α := fun _ => M) q v) 0 *
      f (fun i => (r.castSucc.insertNth (α := fun _ => M) q v) i.succ)) =
        -(v 0 * centralJ z q f (fun i => v i.succ)) := by
  by_cases hro : r.val=0
  · have hre : r=0 := Fin.ext hro
    subst r
    have hqf : ∀ w, q*f w=0 := by intro w; rw [← hr w, ← mul_assoc, hqz, zero_mul]
    have hvrz : v 0*z=0 := by
      rw [← hvr, mul_assoc, ← hz (v 0), ← mul_assoc, hqz, zero_mul]
    have hrj := centralJ_range z q f hr (fun i => v i.succ)
    have hh : v 0*centralJ z q f (fun i => v i.succ)=0 := by
      rw [← hrj, ← mul_assoc, hvrz, zero_mul]
    simp only [Fin.castSucc_zero, Fin.insertNth_apply_same, hqf, smul_zero, hh, neg_zero]
  · have hro : 0<r.val := by omega
    let r' : Fin n := ⟨r.val-1, by omega⟩
    have hv' : ∀ i, i<r' → z*v i.succ=v i.succ := by
      intro i hi
      exact hv _ (by simp only [r', Fin.lt_def,Fin.val_succ] at *; omega)
    have he : r'.succ=r := Fin.ext (by dsimp [r']; omega)
    have hq' : q*v r'.succ=v r'.succ := by simpa only [he] using hvr
    rw [centralJ_first_q z q hzq hqz f r' _ hv' hq', tail_insert v r q hro,
      tupleInsert_lt _ _ _ _ (by simpa only [Fin.val_zero,Fin.val_castSucc] using hro)]
    have he' : r'.val+1=r.val := by dsimp [r']; omega
    rw [he', mul_smul_comm, ← neg_smul, pow_succ]
    congr 1
    ring

lemma centralJ_right_cancellation {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (hz : ∀ a, z*a=a*z) (f : Cochain M (n+1)) (hr : ∀ w, z*f w=f w)
    (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i < r → z*v i=v i) (hvr : q*v r=v r) :
    ((-1:ℂ)^(r.val+1)) • (((-1:ℂ)^(n+2)) •
      (f (fun i => (r.castSucc.insertNth (α := fun _ => M) q v) i.castSucc) *
        (r.castSucc.insertNth (α := fun _ => M) q v) (Fin.last (n+1)))) =
        - (((-1:ℂ)^(n+1)) • (centralJ z q f (fun i => v i.castSucc)*v (Fin.last n))) := by
  rw [init_insert, last_insert]
  by_cases hrl : r.val=n
  · have hre : r=Fin.last n := Fin.ext hrl
    subst r
    have hv' : ∀ i : Fin n, z*v i.castSucc=v i.castSucc := by
      intro i; exact hv _ (by simpa only [Fin.lt_def,Fin.val_last,Fin.val_castSucc] using i.isLt)
    rw [centralJ_all_z z q hqz f _ hv', zero_mul, smul_zero, neg_zero]
    have hh : z*v (Fin.last n)=0 := by rw [← hvr, ← mul_assoc, hzq, zero_mul]
    have he : f ((Fin.last n).insertNth q (fun i => v i.castSucc))*v (Fin.last n)=0 := by
      rw [← hr, hz, mul_assoc, hh, mul_zero]
    rw [he, smul_zero, smul_zero]
  · let r' : Fin n := ⟨r.val, by omega⟩
    have hv' : ∀ i, i<r' → z*v i.castSucc=v i.castSucc := by
      intro i hi; exact hv _ (by simpa only [r', Fin.lt_def,Fin.val_castSucc] using hi)
    have he : r'.castSucc=r := rfl
    have hq' : q*v r'.castSucc=v r'.castSucc := by simpa only [he] using hvr
    rw [centralJ_first_q z q hzq hqz f r' _ hv' hq', he]
    simp only [r', smul_mul_assoc, smul_smul, ← neg_smul, pow_succ]
    congr 1
    ring

lemma differential_centralJ_first_q {n : ℕ} (z q : M) (hzq : z*q=0) (hqz : q*z=0)
    (hz : ∀ a, z*a=a*z) (f : Cochain M (n+1)) (hr : ∀ w, z*f w=f w)
    (hf : ∀ w, differentialValue f w=0) (v : Fin (n+1) → M) (r : Fin (n+1))
    (hv : ∀ i, i<r → z*v i=v i) (hvr : q*v r=v r) :
    differentialValue (centralJ z q f) v=f v := by
  have h := congrArg (fun a => ((-1:ℂ)^(r.val+1)) • a)
    (hf (r.castSucc.insertNth (α := fun _ => M) q v))
  simp only [smul_zero, differentialValue, smul_add] at h
  rw [centralJ_left_cancellation z q hzq hqz hz f hr v r hv hvr,
    centralJ_right_cancellation z q hzq hqz hz f hr v r hv hvr,
    Fin.sum_univ_succAbove _ r, smul_add, merge_insert_same v r q hvr,
    smul_smul, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_smul, Finset.smul_sum] at h
  have hi : ∑ j : Fin n, ((-1:ℂ)^(r.val+1)) •
      (((-1:ℂ)^((r.succAbove j).val+1)) •
        f (mergeInputs (r.castSucc.insertNth (α := fun _ => M) q v) (r.succAbove j))) =
      -(∑ j : Fin n, ((-1:ℂ)^(j.val+1)) • centralJ z q f (mergeInputs v j)) := by
    simp only [centralJ_inner_cancellation z q hzq hqz hz f v r hv hvr, Finset.sum_neg_distrib]
  rw [hi] at h
  have h' : f v - differentialValue (centralJ z q f) v = 0 := by
    convert h using 1
    simp only [differentialValue]
    abel
  exact (sub_eq_zero.mp h').symm

lemma differential_centralJ_all_z {n : ℕ} (z q : M) (hqz : q*z=0)
    (f : Cochain M (n+1)) (v : Fin (n+1) → M) (hv : ∀ i, z*v i=v i) :
    differentialValue (centralJ z q f) v=0 := by
  have hl : centralJ z q f (fun i : Fin n => v i.succ)=0 := centralJ_all_z z q hqz f _ (fun _ => hv _)
  have hr : centralJ z q f (fun i : Fin n => v i.castSucc)=0 := centralJ_all_z z q hqz f _ (fun _ => hv _)
  have hm (j : Fin n) : centralJ z q f (mergeInputs v j)=0 := by
    apply centralJ_all_z z q hqz f
    intro i
    simp only [mergeInputs]
    split_ifs
    · exact hv _
    · rw [← mul_assoc, hv]
    · exact hv _
  simp only [differentialValue, hl,hr,hm,mul_zero,zero_mul,smul_zero,Finset.sum_const_zero,add_zero]

theorem differential_centralJ {n : ℕ} (z : M) (hzz : z*z=z) (hz : ∀ a, z*a=a*z)
    (f : Cochain M (n+1)) (hr : ∀ w, z*f w=f w)
    (hf : ∀ w, differentialValue f w=0) (v : Fin (n+1) → M) :
    differentialValue (centralJ z (1-z) f) v = f v - centralCut z f v := by
  classical
  let q := 1-z
  have hzq : z*q=0 := by dsimp [q]; rw [mul_sub,mul_one,hzz,sub_self]
  have hqz : q*z=0 := by dsimp [q]; rw [sub_mul,one_mul,hzz,sub_self]
  have hqq : q*q=q := by dsimp [q]; rw [mul_sub,sub_mul,sub_mul,one_mul,mul_one,one_mul,hzz]; abel
  let D := differential (centralJ z q f) - f + centralCut z f
  have hall (w : Fin (n+1) → M) (hw : ∀ i, z*w i=w i ∨ q*w i=w i) : D w=0 := by
    by_cases hzall : ∀ i, z*w i=w i
    · have he : (fun i => z*w i)=w := funext hzall
      simp only [D,add_apply,sub_apply,differential_apply,
        differential_centralJ_all_z z q hqz f w hzall, centralCut_apply, he]
      abel
    · let bad : Finset (Fin (n+1)) := Finset.univ.filter (fun i => z*w i≠w i)
      have hb : bad.Nonempty := by
        push Not at hzall
        obtain ⟨i,hi⟩ := hzall
        exact ⟨i, by simp [bad,hi]⟩
      let r := bad.min' hb
      have hrb : r∈bad := Finset.min'_mem bad hb
      have hzr : z*w r≠w r := (Finset.mem_filter.mp hrb).2
      have hqr : q*w r=w r := (hw r).resolve_left hzr
      have hprefix : ∀ i, i<r → z*w i=w i := by
        intro i hi
        by_contra h
        have him : i∈bad := by simp [bad,h]
        have hil : r ≤ i := Finset.min'_le bad i him
        exact (not_le_of_gt hi) hil
      have hc : centralCut z f w=0 := by
        apply f.map_coord_zero r
        change z*w r=0
        rw [← hqr, ← mul_assoc, hzq, zero_mul]
      simp only [D,add_apply,sub_apply,differential_apply,
        differential_centralJ_first_q z q hzq hqz hz f hr hf w r hprefix hqr,
        hc,sub_self,add_zero]
  have hvsum : (fun i => z*v i) + (fun i => q*v i)=v := by
    funext i
    change z*v i+(1-z)*v i=v i
    rw [sub_mul,one_mul]
    abel
  have hd : D v=0 := by
    rw [← hvsum, D.map_add_univ]
    apply Finset.sum_eq_zero
    intro s _
    apply hall
    intro i
    by_cases his : i∈s
    · left
      simp only [Finset.piecewise,his,ite_true,← mul_assoc,hzz]
    · right
      simp only [Finset.piecewise,his,ite_false,← mul_assoc,hqq]
  change differentialValue (centralJ z q f) v = _
  simp only [D,add_apply,sub_apply,differential_apply] at hd
  apply eq_sub_iff_add_eq.mpr
  calc
    _ = (differentialValue (centralJ z q f) v - f v + centralCut z f v) + f v := by abel
    _ = f v := by rw [hd,zero_add]

theorem central_cocycle_correction {n : ℕ} (z : M) (hp : IsStarProjection z)
    (hz : ∀ a, z*a=a*z) (f : Cochain M (n+1)) (hr : ∀ w, z*f w=f w)
    (hf : ∀ w, differentialValue f w=0) :
    ∃ g : Cochain M n, ‖g‖ ≤ n*‖f‖ ∧ (∀ w, z*g w=g w) ∧
      ∀ w, differentialValue g w = f w-centralCut z f w := by
  have hq : IsStarProjection (1-z) := hp.one_sub
  exact ⟨centralJ z (1-z) f, norm_centralJ_le z (1-z) (IsStarProjection.norm_le z hp)
    (IsStarProjection.norm_le (1-z) hq) f, centralJ_range z (1-z) f hr,
    differential_centralJ z hp.isIdempotentElem.eq hz f hr hf⟩
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma central_differential_values {n : ℕ} (p : M) (hp : ∀ a, p*a=a*p)
    (f g : Cochain M n) (hfg : ∀ x, p*f x=g x) (x : Fin (n+1) → M) :
    p*differentialValue f x=differentialValue g x := by
  simp only [differentialValue,mul_add,Finset.mul_sum,mul_smul_comm]
  congr 2
  · rw [← mul_assoc,hp (x 0),mul_assoc,hfg]
  · apply Finset.sum_congr rfl
    intro j _
    rw [hfg]
  · rw [← mul_assoc,hfg]

lemma norm_sum_supported_cochains {n : ℕ} (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i*p j=0) (g : I → Cochain M n)
    (hleft : ∀ i x, p i*g i x=g i x) (hright : ∀ i x, g i x*p i=g i x)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ i, ‖g i‖ ≤ C) (s : Finset I) :
    ‖∑ i ∈ s, g i‖ ≤ C := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro x
  rw [sum_apply]
  apply supported_sum_norm_le p (fun i => g i x) hp horth
    (fun i => hleft i x) (fun i => hright i x) s (C*∏ j,‖x j‖)
    (mul_nonneg hC (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  intro i _
  exact (g i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hg i)
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

theorem primitive_of_central_pieces
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (hcentral : ∀ i a, p i*a=a*p i)
    (horth : ∀ i j, i ≠ j → p i*p j=0)
    (htotal : ∀ x : M, (∀ i, p i*x=0) → x=0)
    {n : ℕ} (f : Cochain M (n+1)) (g : I → Cochain M n)
    (hleft : ∀ i x, p i*g i x=g i x)
    (hdf : ∀ i x, differentialValue (g i) x=p i*f x)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ i, ‖g i‖ ≤ C) :
    ∃ G : Cochain M n, ‖G‖ ≤ C ∧ ∀ x, differentialValue G x=f x := by
  classical
  let F : Finset I → Cochain M n := fun s => ∑ i ∈ s, g i
  have hF (s : Finset I) : ‖F s‖ ≤ C :=
    norm_sum_supported_cochains p hp horth g hleft
      (fun i x => by rw [← hcentral,hleft]) C hC hg s
  let U : Ultrafilter (Finset I) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset I)) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨G,hG,ht⟩ := bounded_cochain_ultralimit e U F C hC hF
  have hproj (i : I) (x : Fin n → M) : p i*G x=g i x := by
    have hlim := (hL (p i)).tendsto e (ht x)
    have hex : (fun s => p i*F s x) =ᶠ[U] (fun _ => g i x) := by
      apply hU
      filter_upwards [eventually_ge_atTop ({i} : Finset I)] with s hs
      have hi : i ∈ s := hs (Finset.mem_singleton_self i)
      change p i*(∑ j ∈ s,g j) x=g i x
      rw [sum_apply,Finset.mul_sum]
      rw [Finset.sum_eq_single i]
      · exact hleft i x
      · intro j _ hji
        calc
          p i*g j x=p i*(p j*g j x) := by rw [hleft]
          _=0 := by rw [← mul_assoc,horth i j hji.symm,zero_mul]
      · exact fun hh => (hh hi).elim
    apply predual_tendsto_unique e hlim
    intro z
    exact tendsto_const_nhds.congr' (hex.mono fun _ h => congrArg (fun a : M => e.symm a z) h.symm)
  refine ⟨G,hG,fun x => sub_eq_zero.mp (htotal _ fun i => ?_)⟩
  rw [mul_sub,central_differential_values (p i) (hcentral i) G (g i) (hproj i),hdf,sub_self]

end BoundedHochschild

open Filter Topology
namespace BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def centralOutput {n : ℕ} (p : M) (f : Cochain M n) : Cochain M n :=
  (ContinuousLinearMap.mul ℂ M p).compContinuousMultilinearMap f

@[simp] lemma centralOutput_apply {n : ℕ} (p : M) (f : Cochain M n) (x : Fin n → M) :
    centralOutput p f x=p*f x := rfl

lemma norm_centralOutput_le {n : ℕ} (p : M) (hp : ‖p‖ ≤ 1) (f : Cochain M n) :
    ‖centralOutput p f‖ ≤ ‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  exact (norm_mul_le p (f x)).trans ((mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans
    (by simpa only [one_mul] using f.le_opNorm x))

theorem primitive_of_central_cut_primitives
    (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
    (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (hcentral : ∀ i a, p i*a=a*p i)
    (horth : ∀ i j, i ≠ j → p i*p j=0)
    (htotal : ∀ x : M, (∀ i, p i*x=0) → x=0)
    {n : ℕ} (f : Cochain M (n+1)) (hf : ∀ x, differentialValue f x=0)
    (b : I → Cochain M n) (hb : ∀ i x, p i*b i x=b i x)
    (hdb : ∀ i x, differentialValue (b i) x=centralCut (p i) (centralOutput (p i) f) x)
    (C : ℝ) (hC : 0 ≤ C) (hbn : ∀ i, ‖b i‖ ≤ C) :
    ∃ G : Cochain M n, ‖G‖ ≤ C+n*‖f‖ ∧ ∀ x, differentialValue G x=f x := by
  have hsupport (i : I) (x : Fin (n+1) → M) :
      p i*centralOutput (p i) f x=centralOutput (p i) f x := by
    simp only [centralOutput_apply,← mul_assoc,(hp i).isIdempotentElem.eq]
  have hcoc (i : I) (x : Fin (n+2) → M) : differentialValue (centralOutput (p i) f) x=0 := by
    rw [← central_differential_values (p i) (hcentral i) f (centralOutput (p i) f)
      (fun _ => rfl),hf,mul_zero]
  choose a han has had using fun i =>
    central_cocycle_correction (p i) (hp i) (hcentral i) (centralOutput (p i) f)
      (hsupport i) (hcoc i)
  let g : I → Cochain M n := fun i => b i+a i
  have hgn (i : I) : ‖g i‖ ≤ C+n*‖f‖ := by
    calc
      ‖g i‖ ≤ ‖b i‖+‖a i‖ := norm_add_le _ _
      _ ≤ C+n*‖centralOutput (p i) f‖ := add_le_add (hbn i) (han i)
      _ ≤ C+n*‖f‖ := add_le_add_right
        (mul_le_mul_of_nonneg_left (norm_centralOutput_le (p i) ((hp i).norm_le) f)
          (Nat.cast_nonneg _)) C
  apply primitive_of_central_pieces e hL p hp hcentral horth htotal f g
    (fun i x => by simp only [g,add_apply,mul_add,hb,has]) _ _ (by positivity) hgn
  intro i x
  simp only [g,differentialValue_add,hdb,had]
  rw [add_sub_cancel,centralOutput_apply]
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder
namespace HochschildTraceNorm
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma norm_mul_eq_abs_mul (b d : A) : ‖b*d‖=‖CFC.abs b*d‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [pow_two,pow_two,← CStarRing.norm_star_mul_self,← CStarRing.norm_star_mul_self]
  congr 1
  simp only [star_mul,(IsSelfAdjoint.of_nonneg (CFC.abs_nonneg b)).star_eq]
  rw [mul_assoc,← mul_assoc (star b),← CFC.abs_mul_abs b]
  simp only [mul_assoc]

theorem exists_approx_polar (b : A) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : A, ‖v‖ ≤ 1 ∧ ‖b-v*CFC.abs b‖ ≤ ε ∧
      ‖CFC.abs b-star v*b‖ ≤ ε := by
  let a := CFC.abs b
  have ha0 : 0 ≤ a := CFC.abs_nonneg b
  have ha : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha0
  let f : ℝ → ℝ := fun t => (t+ε)⁻¹
  have hf : ContinuousOn f (spectrum ℝ a) := by
    apply ContinuousOn.inv₀ ((continuous_id.add continuous_const).continuousOn)
    intro t ht
    have ht0 := spectrum_nonneg_of_nonneg ha0 ht
    exact (show 0 < t+ε from by linarith).ne'
  let q := cfc f a
  have hq : IsSelfAdjoint q := cfc_predicate f a
  have hqa : Commute q a := (Commute.refl a).cfc_real f
  have hab : a*a=star b*b := CFC.abs_mul_abs b
  have haq : a*q=cfc (fun t => t*f t) a := by
    change a*cfc f a = cfc (fun t => id t*f t) a
    rw [cfc_mul id f a continuousOn_id hf,cfc_id ℝ a ha]
  have hnormaq : ‖a*q‖ ≤ 1 := by
    rw [haq]
    apply norm_cfc_le (by positivity)
    intro t ht
    have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg ha0 ht
    have hp : 0 < t+ε := by linarith
    dsimp [f]
    rw [abs_of_nonneg (mul_nonneg ht0 (inv_nonneg.mpr hp.le))]
    exact (mul_inv_le_iff₀ hp).mpr (by linarith)
  have hres : a-q*a*a=cfc (fun t => t-f t*t*t) a := by
    change a-cfc f a*a*a=cfc (fun t => id t - (fun s => f s * id s * id s) t) a
    rw [cfc_sub id (fun s => f s * id s * id s) a continuousOn_id ((hf.mul continuousOn_id).mul continuousOn_id),
      cfc_mul (fun t => f t * id t) id a (hf.mul continuousOn_id) continuousOn_id,
      cfc_mul f id a hf continuousOn_id,cfc_id ℝ a ha]
  have hresnorm : ‖a-q*a*a‖ ≤ ε := by
    rw [hres]
    apply norm_cfc_le hε.le
    intro t ht
    have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg ha0 ht
    have hp : 0 < t+ε := by linarith
    have heq : t-(t+ε)⁻¹*t*t=ε*t/(t+ε) := by field_simp; ring
    dsimp [f]
    rw [heq,abs_of_nonneg (div_nonneg (mul_nonneg hε.le ht0) hp.le)]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  refine ⟨b*q,?_,?_,?_⟩
  · have hh : ‖b*q‖^2 ≤ 1 := by
      rw [pow_two,← CStarRing.norm_star_mul_self]
      have heq : star (b*q)*(b*q)=(a*q)*(a*q) := by
        rw [star_mul,hq.star_eq]
        calc
          q*star b*(b*q)=q*(star b*b)*q := by simp only [mul_assoc]
          _ = q*(a*a)*q := by rw [hab]
          _ = (a*q)*(a*q) := by rw [← mul_assoc q a,hqa.eq]; simp only [mul_assoc]
      rw [heq]
      exact (norm_mul_le _ _).trans ((mul_le_mul hnormaq hnormaq (norm_nonneg _) (by positivity)).trans_eq (by norm_num))
    nlinarith [norm_nonneg (b*q)]
  · have heq : b-b*q*a=b*(1-q*a) := by simp only [mul_sub,mul_one,mul_assoc]
    rw [heq,norm_mul_eq_abs_mul]
    change ‖a*(1-q*a)‖ ≤ ε
    have heq' : a*(1-q*a)=a-q*a*a := by
      rw [mul_sub,mul_one,← mul_assoc,hqa.eq]
    rw [heq']
    exact hresnorm
  · simp only [star_mul,hq.star_eq]
    rw [mul_assoc q (star b),← hab]
    simpa only [mul_assoc] using hresnorm
end HochschildTraceNorm
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open Filter Topology
namespace BoundedHochschild
namespace WeakSubspace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def preannihilator (S : Submodule ℂ (WeakDual ℂ X)) : Submodule ℂ X where
  carrier := {z | ∀ f ∈ S, f z=0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy f hf; simp [map_add,hx f hf,hy f hf]
  smul_mem' := by intro c x hx f hf; simp [map_smul,hx f hf]

lemma preannihilator_closed (S : Submodule ℂ (WeakDual ℂ X)) :
    IsClosed (preannihilator S : Set X) := by
  change IsClosed {z | ∀ f, f ∈ S → f z=0}
  simpa only [Set.ofPred_forall,WeakDual.toStrongDual_apply] using
    (isClosed_iInter fun (f : WeakDual ℂ X) => isClosed_iInter fun (_ : f ∈ S) =>
      isClosed_eq (WeakDual.toStrongDual f).continuous (continuous_const (y := (0 : ℂ))))

lemma mem_iff_annihilates (S : Submodule ℂ (WeakDual ℂ X))
    (hS : IsClosed (S : Set (WeakDual ℂ X))) (f : WeakDual ℂ X) :
    f ∈ S ↔ ∀ z ∈ preannihilator S, f z=0 := by
  let : IsScalarTower ℝ ℂ (WeakDual ℂ X) :=
    inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ X))
  let hc : LocallyConvexSpace ℝ (WeakDual ℂ X) :=
    @WeakBilin.locallyConvexSpace ℂ (StrongDual ℂ X) X _ _ _ _ _ _ _ _ _
  constructor
  · intro hf z hz
    exact hz f hf
  · intro hf
    by_contra hnot
    obtain ⟨F,c,hFc,hcf⟩ := @RCLike.geometric_hahn_banach_closed_point ℂ (WeakDual ℂ X)
      _ _ _ (S : Set (WeakDual ℂ X)) f _ _ _ _ _ hc
      (S.restrictScalars ℝ).convex hS hnot
    have hzero (a : WeakDual ℂ X) (ha : a ∈ S) : F a=0 := by
      by_contra hne
      have hb := hFc ((((c+1 : ℝ) : ℂ) / F a) • a) (S.smul_mem _ ha)
      rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ hne] at hb
      simp only [RCLike.re_to_complex,Complex.ofReal_re] at hb
      linarith
    obtain ⟨z,hz⟩ := LinearMap.dualEmbedding_surjective (topDualPairing ℂ X) F
    have heval (a : WeakDual ℂ X) : F a=a z := by
      rw [← hz]
      rfl
    have hmem : z ∈ preannihilator S := by
      intro a ha
      rw [← heval]
      exact hzero a ha
    have hf0 := hf z hmem
    have hc0 := hFc 0 S.zero_mem
    simp only [map_zero] at hc0
    rw [heval,hf0] at hcf
    simp only [RCLike.zero_re] at hcf
    linarith

def strong (S : Submodule ℂ (WeakDual ℂ X)) : Submodule ℂ (StrongDual ℂ X) :=
  S.map WeakDual.toStrongDual.toLinearMap

lemma mem_strong (S : Submodule ℂ (WeakDual ℂ X)) (f : StrongDual ℂ X) :
    f ∈ strong S ↔ StrongDual.toWeakDual f ∈ S := by
  constructor
  · rintro ⟨g,hg,hgf⟩
    change WeakDual.toStrongDual g=f at hgf
    rw [← hgf]
    exact hg
  · intro hf
    exact ⟨StrongDual.toWeakDual f,hf,rfl⟩

instance preannihilator_closed_instance (S : Submodule ℂ (WeakDual ℂ X)) :
    IsClosed (preannihilator S : Set X) := preannihilator_closed S

lemma quotient_dual_norm (K : Submodule ℂ X) [IsClosed (K : Set X)]
    (F : StrongDual ℂ (X ⧸ K)) : ‖F.comp K.mkQL‖=‖F‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound (F.comp K.mkQL) (norm_nonneg F)
    intro x
    exact (F.le_opNorm (K.mkQL x)).trans
      (mul_le_mul_of_nonneg_left (Submodule.Quotient.norm_mk_le K x) (norm_nonneg _))
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro q
    apply le_of_forall_pos_le_add
    intro ε hε
    let C := ‖F.comp K.mkQL‖
    have hC : 0 ≤ C := norm_nonneg _
    obtain ⟨x,hx,hxn⟩ := Submodule.Quotient.norm_mk_lt q (show 0 < ε/(C+1) by positivity)
    have hb := (F.comp K.mkQL).le_opNorm x
    change ‖F (Submodule.Quotient.mk x)‖ ≤ C*‖x‖ at hb
    rw [hx] at hb
    have hd : C*(ε/(C+1)) ≤ ε := by
      rw [← mul_div_assoc,div_le_iff₀ (by positivity)]
      nlinarith
    calc
      ‖F q‖ ≤ C*‖x‖ := hb
      _ ≤ C*(‖q‖+ε/(C+1)) := mul_le_mul_of_nonneg_left hxn.le hC
      _ ≤ C*‖q‖+ε := by nlinarith

def quotientDual (S : Submodule ℂ (WeakDual ℂ X))
    (hS : IsClosed (S : Set (WeakDual ℂ X))) :
    StrongDual ℂ (X ⧸ preannihilator S) →ₗᵢ[ℂ] strong S where
  toFun F := ⟨F.comp (preannihilator S).mkQL,by
    rw [mem_strong,mem_iff_annihilates S hS]
    intro z hz
    change F (Submodule.Quotient.mk z)=0
    rw [(Submodule.Quotient.mk_eq_zero (preannihilator S)).mpr hz,map_zero]⟩
  map_add' F G := by ext z; rfl
  map_smul' c F := by ext z; rfl
  norm_map' F := quotient_dual_norm (preannihilator S) F

lemma quotientDual_surjective (S : Submodule ℂ (WeakDual ℂ X))
    (hS : IsClosed (S : Set (WeakDual ℂ X))) :
    Function.Surjective (quotientDual S hS) := by
  intro f
  have hk : preannihilator S ≤ f.val.ker := by
    intro z hz
    exact hz (StrongDual.toWeakDual f.val) ((mem_strong S f.val).mp f.property)
  refine ⟨(preannihilator S).liftQL f.val hk,?_⟩
  apply Subtype.ext
  ext z
  rfl

def quotientDualEquiv (S : Submodule ℂ (WeakDual ℂ X))
    (hS : IsClosed (S : Set (WeakDual ℂ X))) :
    StrongDual ℂ (X ⧸ preannihilator S) ≃ₗᵢ[ℂ] strong S :=
  { LinearEquiv.ofBijective (quotientDual S hS).toLinearMap
      ⟨by
        intro a b hab
        ext q
        obtain ⟨z,rfl⟩ := (preannihilator S).mkQ_surjective q
        exact congrArg (fun f : strong S => f.val z) hab,
       quotientDual_surjective S hS⟩ with
    norm_map' := (quotientDual S hS).norm_map }
end WeakSubspace
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open Filter Topology
namespace HochschildSakai
open BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

variable [PartialOrder M] [StarOrderedRing M] [CompleteSpace X]

theorem predual_tendsto_mul_right (a : M) {b : I → M} {l : Filter I} {c : M}
    (hb : PredualTendsto e b l c) :
    PredualTendsto e (fun i => b i*a) l (c*a) :=
  HasPreadjoint.tendsto e (mul_right_hasPreadjoint e a) hb
end HochschildSakai
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open Filter Topology
open scoped ComplexOrder
namespace HochschildDixmier
open BoundedHochschild HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ)

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

end Hilbert

omit [StarOrderedRing M] in
lemma trace_conjugate (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (u : unitary M) (a : M) : τ (conjugate u a)=τ a := by
  rw [conjugate_apply,htr,← mul_assoc,Unitary.star_mul_self_of_mem u.prop,one_mul]
end HochschildDixmier
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
namespace BoundedHochschild
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end BoundedHochschild

open Filter Topology
namespace HochschildPolar
open BoundedHochschild HochschildSakai
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

include e in

theorem exists_polar_contraction (b : M) :
    ∃ v : M, ‖v‖ ≤ 1 ∧ b=v*CFC.abs b ∧ CFC.abs b=star v*b := by
  classical
  have hpos (n : ℕ) : 0 < (1:ℝ)/((n:ℝ)+1) := by positivity
  choose v hv hleft hright using
    fun n : ℕ => HochschildTraceNorm.exists_approx_polar b _ (hpos n)
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨w,hw,ht⟩ := exists_predual_ultralimit e U v 1 hv
  have hε : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Tendsto (fun n => v n*CFC.abs b) atTop (𝓝 b) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _) _ hε
    intro n
    rw [norm_sub_rev]
    exact hleft n
  have hr : Tendsto (fun n => star (v n)*b) atTop (𝓝 (CFC.abs b)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _) _ hε
    intro n
    rw [norm_sub_rev]
    exact hright n
  exact ⟨w,hw,
    predual_tendsto_unique e (predual_tendsto_of_norm e (hl.mono_left hU))
      (predual_tendsto_mul_right e _ ht),
    predual_tendsto_unique e (predual_tendsto_of_norm e (hr.mono_left hU))
      (predual_tendsto_mul_right e _ (predual_tendsto_star e ht))⟩

omit [PartialOrder M] [StarOrderedRing M] in
lemma support_right_annihilate {a p : M} (hp : IsSupportProjection a p)
    (ha : IsSelfAdjoint a) {x : M} (hx : x*a=0) : x*p=0 := by
  have hh := hp.annihilate (star x) (by
    simpa only [star_mul,ha.star_eq,star_zero] using congrArg star hx)
  simpa only [star_mul,star_star,hp.proj.isSelfAdjoint.star_eq,star_zero]
    using congrArg star hh

include e in

theorem exists_polar_partial_isometry (b : M) :
    ∃ v p q : M, IsSupportProjection (CFC.abs b) p ∧
      star v*v=p ∧ v*star v=q ∧ IsStarProjection q ∧ b=v*CFC.abs b ∧
      v*p=v ∧ q*b=b := by
  obtain ⟨w,hw,hb,ha⟩ := exists_polar_contraction e b
  obtain ⟨p,hp⟩ := HochschildSakai.exists_support_projection e (CFC.abs b) (CFC.abs_nonneg b)
  let v := w*p
  have hvp : v*p=v := by
    dsimp [v]
    rw [mul_assoc,hp.proj.isIdempotentElem.eq]
  have hvb : v*CFC.abs b=b := by
    dsimp [v]
    rw [mul_assoc,hp.left,← hb]
  have hv : star v*b=CFC.abs b := by
    dsimp [v]
    rw [star_mul,hp.proj.isSelfAdjoint.star_eq,mul_assoc,← ha,hp.left]
  have hinit : star v*v=p := by
    have hz : (star v*v-p)*CFC.abs b=0 := by
      rw [sub_mul,mul_assoc,hvb,hv,hp.left,sub_self]
    have hh := support_right_annihilate hp (IsSelfAdjoint.of_nonneg (CFC.abs_nonneg b)) hz
    rw [sub_mul,mul_assoc,hvp,hp.proj.isIdempotentElem.eq,sub_eq_zero] at hh
    exact hh
  have hfinal : IsStarProjection (v*star v) := by
    constructor
    · change (v*star v)*(v*star v)=v*star v
      calc
        _ = v*(star v*v)*star v := by simp only [mul_assoc]
        _ = v*star v := by rw [hinit,hvp]
    · exact IsSelfAdjoint.mul_star_self v
  refine ⟨v,p,v*star v,hp,hinit,rfl,hfinal,hvb.symm,hvp,?_⟩
  rw [mul_assoc,hv,hvb]
end HochschildPolar
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open Filter Topology
namespace BoundedHochschild
namespace WeakAlgebra
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def weakEquiv : WeakDual ℂ X ≃ₗ⋆[ℂ] M :=
  WeakDual.toStrongDual.trans e.toLinearEquiv

lemma normal_continuous (A : M →L[ℂ] M) (hA : HasPreadjoint e A) :
    Continuous (fun f : WeakDual ℂ X => (weakEquiv e).symm (A (weakEquiv e f))) := by
  apply WeakBilin.continuous_of_continuous_eval (topDualPairing ℂ X)
  intro z
  obtain ⟨w,hw⟩ := hA z
  change Continuous (fun f : WeakDual ℂ X => e.symm (A (weakEquiv e f)) z)
  simp_rw [hw]
  simpa [weakEquiv] using WeakDual.eval_continuous (𝕜 := ℂ) w

variable (A : StarSubalgebra ℂ M)
    (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
    (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
    (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

end WeakAlgebra
end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
namespace WeakAlgebra
open HochschildTraceNorm
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (A : StarSubalgebra ℂ M)
  (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
  (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
  (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))
  (hτ : TraceInPredual e τ)

end WeakAlgebra
end BoundedHochschild

namespace BoundedHochschild
open TopologicalSpace
variable {M : Type*}

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
namespace WeakAlgebra
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

instance closedSubalgebra_starOrderedRing (B : StarSubalgebra ℂ M)
    [IsClosed (B : Set M)] [StarOrderedRing M] : StarOrderedRing B := by
  apply StarOrderedRing.of_nonneg_iff'
  · intro x y h z
    change (z:M)+(x:M) ≤ (z:M)+(y:M)
    simpa only [add_comm] using add_le_add_left (show (x:M) ≤ (y:M) from h) (z:M)
  · intro a
    constructor
    · intro ha
      have hmem : CFC.sqrt (a:M) ∈ B := by
        rw [CFC.sqrt_eq_real_sqrt (a:M) (show 0 ≤ (a:M) from ha)]
        exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt a.property
      refine ⟨⟨CFC.sqrt (a:M),hmem⟩,Subtype.ext ?_⟩
      change (a:M)=star (CFC.sqrt (a:M))*CFC.sqrt (a:M)
      rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (a:M))).star_eq]
      exact (CFC.sqrt_mul_sqrt_self (a:M) ha).symm
    · rintro ⟨b,rfl⟩
      exact star_mul_self_nonneg (b:M)
end WeakAlgebra
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

end HochschildCorners

open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild BoundedHochschild.WeakAlgebra HochschildRigidity HochschildSakai
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (p : M) (hp : IsStarProjection p)

section Predual
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def weakCorner : Submodule ℂ (WeakDual ℂ X) where
  carrier := {f | weakEquiv e f ∈ corner p hp}
  zero_mem' := by
    change weakEquiv e 0 ∈ corner p hp
    rw [map_zero]
    exact (corner p hp).zero_mem
  add_mem' := by
    intro a b ha hb
    change weakEquiv e (a+b) ∈ corner p hp
    rw [map_add]
    exact (corner p hp).add_mem ha hb
  smul_mem' := by
    intro c a ha
    change weakEquiv e (c • a) ∈ corner p hp
    rw [LinearEquiv.map_smulₛₗ]
    exact (corner p hp).smul_mem (star c) ha

lemma weakCorner_closed : IsClosed (weakCorner p hp e : Set (WeakDual ℂ X)) := by
  have hL := mul_hasPreadjoint e p
  have hR := mul_right_hasPreadjoint e p
  have hLeft := isClosed_eq (normal_continuous e _ hL) (continuous_id : Continuous (id : WeakDual ℂ X → _))
  have hRight := isClosed_eq (normal_continuous e _ hR) (continuous_id : Continuous (id : WeakDual ℂ X → _))
  change IsClosed {f | (weakEquiv e).symm (p*weakEquiv e f)=f} at hLeft
  change IsClosed {f | (weakEquiv e).symm (weakEquiv e f*p)=f} at hRight
  convert hLeft.inter hRight using 1
  ext f
  change (p*weakEquiv e f=weakEquiv e f ∧ weakEquiv e f*p=weakEquiv e f) ↔
    ((weakEquiv e).symm (p*weakEquiv e f)=f ∧ (weakEquiv e).symm (weakEquiv e f*p)=f)
  constructor
  · rintro ⟨h,h'⟩
    exact ⟨by rw [h,LinearEquiv.symm_apply_apply],by rw [h',LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨h,h'⟩
    exact ⟨by simpa only [LinearEquiv.apply_symm_apply] using congrArg (weakEquiv e) h,
      by simpa only [LinearEquiv.apply_symm_apply] using congrArg (weakEquiv e) h'⟩

def CornerPredual := X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)
instance : NormedAddCommGroup (CornerPredual p hp e) := inferInstanceAs
  (NormedAddCommGroup (X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)))
instance : NormedSpace ℂ (CornerPredual p hp e) := inferInstanceAs
  (NormedSpace ℂ (X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)))
instance : CompleteSpace (CornerPredual p hp e) := inferInstanceAs
  (CompleteSpace (X ⧸ WeakSubspace.preannihilator (weakCorner p hp e)))

def cornerStrongEquiv : WeakSubspace.strong (weakCorner p hp e) ≃ₗᵢ⋆[ℂ] Corner p hp where
  toFun f := ⟨e f.val,by
    have hf := (WeakSubspace.mem_strong (weakCorner p hp e) f.val).mp f.property
    exact hf⟩
  invFun a := ⟨e.symm a.val,by
    rw [WeakSubspace.mem_strong]
    change e (e.symm a.val) ∈ corner p hp
    simpa only [LinearIsometryEquiv.apply_symm_apply] using a.property⟩
  left_inv f := Subtype.ext (e.symm_apply_apply f.val)
  right_inv a := Subtype.ext (e.apply_symm_apply a.val)
  map_add' f g := Subtype.ext (map_add e f.val g.val)
  map_smul' c f := Subtype.ext (e.map_smulₛₗ c f.val)
  norm_map' f := e.norm_map f.val

def cornerPredualEquiv : StrongDual ℂ (CornerPredual p hp e) ≃ₗᵢ⋆[ℂ] Corner p hp :=
  (WeakSubspace.quotientDualEquiv (weakCorner p hp e) (weakCorner_closed p hp e)).trans
    (cornerStrongEquiv p hp e)
end Predual
end HochschildCorners
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild
namespace CentralCorner

open HochschildCorners

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (p : M) (hp : IsStarProjection p) (hc : ∀ a : M, p * a = a * p)

def includeMap : Corner p hp →L[ℂ] M :=
  (corner p hp).toNonUnitalSubalgebra.toSubmodule.subtypeL

def compressMap : M →L[ℂ] Corner p hp :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨p * a, by
        constructor
        · rw [← mul_assoc, hp.isIdempotentElem.eq]
        · calc
            (p * a) * p = p * (a * p) := mul_assoc _ _ _
            _ = p * (p * a) := by rw [← hc a]
            _ = p * a := by rw [← mul_assoc, hp.isIdempotentElem.eq]⟩
      map_add' := fun a b => Subtype.ext (mul_add p a b)
      map_smul' := fun c a => Subtype.ext (by
        change p * (c • a) = c • (p * a)
        rw [mul_smul_comm]) }
    1 (fun a => by
      change ‖p * a‖ ≤ 1 * ‖a‖
      exact (norm_mul_le p a).trans (mul_le_mul_of_nonneg_right hp.norm_le (norm_nonneg a)))

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma includeMap_apply (a : Corner p hp) : includeMap p hp a = (a : M) := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma compressMap_coe (a : M) :
    (compressMap p hp hc a : M) = p * a := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma compressMap_includeMap (a : Corner p hp) :
    compressMap p hp hc (includeMap p hp a) = a := Subtype.ext a.property.1

omit [PartialOrder M] [StarOrderedRing M] in
lemma compressMap_mul (a b : M) :
    compressMap p hp hc (a * b) = compressMap p hp hc a * compressMap p hp hc b := by
  apply Subtype.ext
  exact (central_idempotent_mul p hp.isIdempotentElem.eq hc a b).symm

omit [PartialOrder M] [StarOrderedRing M] in
lemma compressMap_left_module (a : Corner p hp) (b : M) :
    compressMap p hp hc ((a : M) * b) = a * compressMap p hp hc b := by
  apply Subtype.ext
  change p * ((a : M) * b) = (a : M) * (p * b)
  rw [← mul_assoc, a.property.1, ← mul_assoc, a.property.2]

omit [PartialOrder M] [StarOrderedRing M] in
lemma compressMap_right_module (a : M) (b : Corner p hp) :
    compressMap p hp hc (a * (b : M)) = compressMap p hp hc a * b := by
  apply Subtype.ext
  exact (mul_assoc p a (b : M)).symm

omit [PartialOrder M] [StarOrderedRing M] in
lemma compressMap_norm (a : M) : ‖compressMap p hp hc a‖ ≤ ‖a‖ := by
  exact (norm_mul_le p a).trans
    ((mul_le_mul_of_nonneg_right hp.norm_le (norm_nonneg a)).trans_eq (one_mul _))

def restrict {n : ℕ} (f : Cochain M n) : Cochain (Corner p hp) n :=
  (compressMap p hp hc).compContinuousMultilinearMap
    (f.compContinuousLinearMap (fun _ => includeMap p hp))

def extend {n : ℕ} (g : Cochain (Corner p hp) n) : Cochain M n :=
  (includeMap p hp).compContinuousMultilinearMap
    (g.compContinuousLinearMap (fun _ => compressMap p hp hc))

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma restrict_apply {n : ℕ} (f : Cochain M n) (x : Fin n → Corner p hp) :
    restrict p hp hc f x = compressMap p hp hc (f (fun i => (x i : M))) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma extend_apply {n : ℕ} (g : Cochain (Corner p hp) n) (x : Fin n → M) :
    extend p hp hc g x = (g (fun i => compressMap p hp hc (x i)) : M) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma restrict_norm {n : ℕ} (f : Cochain M n) : ‖restrict p hp hc f‖ ≤ ‖f‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  exact (compressMap_norm p hp hc _).trans (f.le_opNorm (fun i => (x i : M)))

omit [PartialOrder M] [StarOrderedRing M] in
lemma extend_norm {n : ℕ} (g : Cochain (Corner p hp) n) :
    ‖extend p hp hc g‖ ≤ ‖g‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  exact (g.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => compressMap_norm p hp hc (x i)))
    (norm_nonneg _))

omit [PartialOrder M] [StarOrderedRing M] in
lemma extend_supported {n : ℕ} (g : Cochain (Corner p hp) n) (x : Fin n → M) :
    p * extend p hp hc g x = extend p hp hc g x :=
  (g (fun i => compressMap p hp hc (x i))).property.1

omit [PartialOrder M] [StarOrderedRing M] in
lemma merge_include {n : ℕ} (x : Fin (n + 1) → Corner p hp) (j : Fin n) :
    mergeInputs (fun i => (x i : M)) j = fun i => (mergeInputs (M := Corner p hp) x j i : M) := by
  funext i
  simp only [mergeInputs]
  split_ifs <;> rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma merge_compress {n : ℕ} (x : Fin (n + 1) → M) (j : Fin n) :
    mergeInputs (fun i => compressMap p hp hc (x i)) j =
      fun i => compressMap p hp hc (mergeInputs x j i) := by
  funext i
  simp only [mergeInputs]
  split_ifs <;> first | rfl | exact (compressMap_mul p hp hc _ _).symm

omit [PartialOrder M] [StarOrderedRing M] in

lemma differential_restrict {n : ℕ} (f : Cochain M n)
    (x : Fin (n + 1) → Corner p hp) :
    differentialValue (restrict p hp hc f) x =
      compressMap p hp hc (differentialValue f (fun i => (x i : M))) := by
  simp only [differentialValue, restrict_apply, map_add, map_sum, map_smul,
    merge_include, compressMap_left_module, compressMap_right_module]

omit [PartialOrder M] [StarOrderedRing M] in
lemma restrict_cocycle {n : ℕ} (f : Cochain M n)
    (hf : ∀ x, differentialValue f x = 0) :
    ∀ x, differentialValue (restrict p hp hc f) x = 0 := by
  intro x
  rw [differential_restrict, hf, map_zero]

omit [PartialOrder M] [StarOrderedRing M] in

lemma differential_extend {n : ℕ} (g : Cochain (Corner p hp) n) (x : Fin (n + 1) → M) :
    differentialValue (extend p hp hc g) x =
      (differentialValue (M := Corner p hp) g (fun i => compressMap p hp hc (x i)) : M) := by
  change differentialValue (extend p hp hc g) x =
    includeMap p hp (differentialValue (M := Corner p hp) g (fun i => compressMap p hp hc (x i)))
  simp only [differentialValue, map_add, map_sum, map_smul, extend_apply,
    includeMap_apply, merge_compress]
  congr 2
  · change x 0 * (g _ : M) = (p * x 0) * (g _ : M)
    rw [hc (x 0), mul_assoc, (g _).property.1]
  · change (g _ : M) * x (Fin.last n) = (g _ : M) * (p * x (Fin.last n))
    rw [← mul_assoc, (g _).property.2]

omit [PartialOrder M] [StarOrderedRing M] in
lemma extend_primitive {n : ℕ} (f : Cochain M (n + 1))
    (g : Cochain (Corner p hp) n)
    (hg : ∀ x, differentialValue g x = restrict p hp hc f x)
    (x : Fin (n + 1) → M) :
    differentialValue (extend p hp hc g) x =
      centralCut p (centralOutput p f) x := by
  rw [differential_extend, hg]
  rfl
end CentralCorner
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCorners
open BoundedHochschild HochschildRigidity HochschildDixmier HochschildDiffuse
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (h1 : τ 1 = 1)
  (htr : ∀ a b : M, τ (a*b) = τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a) = 0 → a = 0)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b = c • (1 : M))

include e in

theorem corner_polar {p q b : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hbp : b*p=b) (hqb : q*b=b) :
    ∃ v r s : M, IsStarProjection r ∧ IsStarProjection s ∧
      r ≤ p ∧ s ≤ q ∧ star v*v=r ∧ v*star v=s ∧ v*r=v ∧ s*v=v ∧
      b=v*CFC.abs b := by
  obtain ⟨v,r,s,hr,hi,hf,hs,hb,hvr,hsb⟩ :=
    HochschildPolar.exists_polar_partial_isometry e b
  have habs : star v*b=CFC.abs b := by
    calc
      star v*b = star v*(v*CFC.abs b) := congrArg (fun x => star v*x) hb
      _ = CFC.abs b := by rw [← mul_assoc,hi,hr.left]
  have hrp : r ≤ p := hr.le_of_support hp (by
    rw [← habs,mul_assoc,hbp])
  have hqv : q*v=v := by
    have hz : (q*v-v)*CFC.abs b=0 := by
      rw [sub_mul,mul_assoc,← hb,hqb,sub_self]
    have hzr := HochschildPolar.support_right_annihilate hr
      (IsSelfAdjoint.of_nonneg (CFC.abs_nonneg b)) hz
    simpa only [sub_mul,mul_assoc,hvr,sub_eq_zero] using hzr
  have hsq : s ≤ q := (hs.le_iff_mul_eq_right hq).mpr (by
    rw [← hf,← mul_assoc,hqv])
  have hsv : s*v=v := by rw [← hf,mul_assoc,hi,hvr]
  exact ⟨v,r,s,hr.proj,hs,hrp,hsq,hi,hf,hvr,hsv,hb⟩

end PopaCorners

open Filter Topology
open scoped ComplexOrder
namespace PopaCorners
open BoundedHochschild HochschildRigidity HochschildDixmier HochschildDiffuse
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

structure CornerIso (p q : M) where
  val : M
  init_proj : IsStarProjection (star val*val)
  absorb : val*(star val*val)=val
  init_le : star val*val ≤ p
  final_le : val*star val ≤ q

namespace CornerIso
variable {p q : M}
instance : CoeOut (CornerIso p q) M := ⟨CornerIso.val⟩

omit [StarOrderedRing M] in
@[ext] theorem ext {v w : CornerIso p q} (h : (v:M)=(w:M)) : v=w := by
  cases v; cases w; cases h; rfl

def initial (v : CornerIso p q) : M := star (v:M)*(v:M)
def final (v : CornerIso p q) : M := (v:M)*star (v:M)

omit [StarOrderedRing M] in
lemma initial_proj (v : CornerIso p q) : IsStarProjection v.initial := v.init_proj

omit [StarOrderedRing M] in
lemma mul_initial (v : CornerIso p q) : (v:M)*v.initial=(v:M) := v.absorb

instance : PartialOrder (CornerIso p q) where
  le v w := v.initial ≤ w.initial ∧ (w:M)*v.initial=(v:M)
  le_refl v := ⟨le_rfl,v.absorb⟩
  le_trans v w z hvw hwz := by
    refine ⟨hvw.1.trans hwz.1,?_⟩
    have hvwi := (v.initial_proj.le_iff_mul_eq_right w.initial_proj).mp hvw.1
    calc
      (z:M)*v.initial = (z:M)*(w.initial*v.initial) := by rw [hvwi]
      _ = ((z:M)*w.initial)*v.initial := by rw [mul_assoc]
      _ = (v:M) := by rw [hwz.2,hvw.2]
  le_antisymm v w hvw hwv := by
    apply ext
    have hi := le_antisymm hvw.1 hwv.1
    rw [hi,w.mul_initial] at hvw
    exact hvw.2.symm
end CornerIso
end PopaCorners
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDixmier
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma average_central (a : M) : Central (average e τ hτ htr hfaith a) :=
  (exists_central_average e τ (HochschildSakai.abstract_multiplication_normal e).1
    hτ htr hfaith a).choose_spec.2.1
lemma average_orbit (a : M) :
    gnsVector τ (average e τ hτ htr hfaith a) ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a))) :=
  (exists_central_average e τ (HochschildSakai.abstract_multiplication_normal e).1
    hτ htr hfaith a).choose_spec.2.2

variable (h1 : τ 1=1)
include htr in
omit [StarOrderedRing M] in
lemma central_pair_hull {z : M} (hz : Central z) (a : M) :
    convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) ⊆
      {b | τ (z*b)=τ (z*a)} := by
  apply convexHull_min
  · rintro _ ⟨v,rfl⟩
    change τ (z*conjugate v a)=τ (z*a)
    rw [conjugate_apply]
    have he : z*((v:M)*a*star (v:M))=(v:M)*(z*a)*star (v:M) := by
      calc
        _=(z*(v:M))*a*star (v:M) := by simp only [mul_assoc]
        _=((v:M)*z)*a*star (v:M) := by rw [(hz (v:M)).eq]
        _=_ := by simp only [mul_assoc]
    rw [he]
    exact trace_conjugate τ htr v (z*a)
  · intro x hx y hy r s _hr _hs hrs
    change τ (z*(r • x+s • y))=τ (z*a)
    rw [mul_add,mul_smul_comm,mul_smul_comm,map_add,τ.map_smul_of_tower,
      τ.map_smul_of_tower,hx,hy,←add_smul,hrs,one_smul]

include htr h1 in
lemma central_pair_closure {z : M} (hz : Central z) (a b : M)
    (hb : gnsVector τ b ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a)))) : τ (z*b)=τ (z*a) := by
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp hb
  choose c hc hcy using hy
  have htc : ∀ n, τ (z*c n)=τ (z*a) := fun n => central_pair_hull τ htr hz a (hc n)
  have ht : Tendsto (fun n => ‖τ.toPreGNS (c n-b)‖) atTop (𝓝 0) := by
    have hh := tendsto_iff_norm_sub_tendsto_zero.mp hyt
    simpa only [←hcy,←map_sub,gnsVector_norm] using hh
  have htt : Tendsto (fun n => ‖τ (z*(c n-b))‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => (HochschildUltrapower.norm_trace_le τ h1 _).trans
        (preGNS_norm_mul_le τ z _))
    simpa only [mul_zero] using ht.const_mul ‖z‖
  have he : ‖τ (z*a)-τ (z*b)‖=0 := tendsto_nhds_unique tendsto_const_nhds
    (by simpa only [mul_sub,map_sub,htc] using htt)
  exact (sub_eq_zero.mp (norm_eq_zero.mp he)).symm

include h1
lemma average_pair {z : M} (hz : Central z) (a : M) :
    τ (z*average e τ hτ htr hfaith a)=τ (z*a) :=
  central_pair_closure τ htr h1 hz a _ (average_orbit e τ hτ htr hfaith a)

end PopaCenter

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDixmier
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

lemma average_nonneg {a : M} (ha : 0 ≤ a) : 0 ≤ average e τ hτ htr hfaith a := by
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp (average_orbit e τ hτ htr hfaith a)
  choose c hc hcy using hy
  have hcp : ∀ n, 0 ≤ c n := by
    intro n
    have hsub : convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) ⊆
        Set.Ici (0:M) := by
      apply convexHull_min _ (convex_Ici _)
      rintro _ ⟨v,rfl⟩
      exact star_right_conjugate_nonneg ha (v:M)
    exact hsub (hc n)
  have hcn : ∀ n, ‖c n‖ ≤ ‖a‖ := by
    intro n
    simpa only [Metric.mem_closedBall,dist_zero_right] using orbit_hull_bounded a (hc n)
  have ht : GNSTendsto τ c atTop (average e τ hτ htr hfaith a) := by
    have hh := tendsto_iff_norm_sub_tendsto_zero.mp hyt
    simpa only [GNSTendsto,←hcy,←map_sub,gnsVector_norm] using hh
  exact HochschildSakai.nonneg_of_bounded_predual_limit e ‖a‖ (norm_nonneg a)
    (Eventually.of_forall hcn) (Eventually.of_forall hcp)
    (ht.predual e τ (HochschildSakai.abstract_multiplication_normal e).1 hτ hfaith ‖a‖ hcn)

omit [PartialOrder M] [StarOrderedRing M] in
lemma support_central {a p : M} (hp : IsSupportProjection a p) (ha : Central a) : Central p := by
  have h (x : M) : p*x*p=p*x := by
    have hz : a*(x*p-p*x)=0 := by
      rw [mul_sub,←mul_assoc,(ha x).eq,mul_assoc,hp.right,←mul_assoc,hp.right,(ha x).eq,sub_self]
    have hh := hp.annihilate _ hz
    simpa only [mul_sub,←mul_assoc,hp.proj.isIdempotentElem.eq,sub_eq_zero] using hh
  intro x
  change p*x=x*p
  have hs := congrArg star (h (star x))
  simp only [star_mul,star_star,hp.proj.isSelfAdjoint.star_eq,mul_assoc] at hs
  exact (h x).symm.trans ((mul_assoc _ _ _).trans hs)

include hfaith in
omit [StarOrderedRing M] in
lemma projection_zero_of_trace_zero {p : M} (hp : IsStarProjection p) (ht : τ p=0) : p=0 := by
  apply hfaith
  simpa only [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] using ht

include h1 in
lemma projection_le_support_average {p c : M} (hp : IsStarProjection p)
    (hc : IsSupportProjection (average e τ hτ htr hfaith p) c) : p ≤ c := by
  have hcc := support_central hc (average_central e τ hτ htr hfaith p)
  have hzc : Central (1-c) := fun x => (Commute.one_left x).sub_left (hcc x)
  have hzproj : IsStarProjection ((1-c)*p) := hc.proj.one_sub.mul hp (hzc p)
  have ht : τ ((1-c)*p)=0 := by
    rw [←average_pair e τ hτ htr hfaith h1 hzc,sub_mul,one_mul,hc.left,sub_self,map_zero]
  have hz := projection_zero_of_trace_zero τ hfaith hzproj ht
  apply (hp.le_iff_mul_eq_right hc.proj).mpr
  exact (sub_eq_zero.mp (by simpa only [sub_mul,one_mul] using hz)).symm

include e hτ htr hfaith h1 in
lemma exists_central_support {p : M} (hp : IsStarProjection p) :
    ∃ c : M, IsStarProjection c ∧ Central c ∧ p ≤ c ∧
      ∀ q : M, (∀ a : M, q*a*p=0) → q*c=0 := by
  obtain ⟨c,hc⟩ := HochschildSakai.exists_support_projection e
    (average e τ hτ htr hfaith p) (average_nonneg e τ hτ htr hfaith hp.nonneg)
  refine ⟨c,hc.proj,support_central hc (average_central e τ hτ htr hfaith p),
    projection_le_support_average e τ hτ htr hfaith h1 hp hc,?_⟩
  intro q hq
  have hker : convexHull ℝ (Set.range (fun v : unitary M => conjugate v p)) ⊆
      {a | q*a=0} := by
    apply convexHull_min
    · rintro _ ⟨v,rfl⟩
      change q*((v:M)*p*star (v:M))=0
      rw [←mul_assoc,←mul_assoc,hq,zero_mul]
    · intro a ha b hb r s _ _ _
      change q*(r • a+s • b)=0
      change q*a=0 at ha
      change q*b=0 at hb
      rw [mul_add,mul_smul_comm,mul_smul_comm,ha,hb,smul_zero,smul_zero,add_zero]
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp (average_orbit e τ hτ htr hfaith p)
  choose a ha hay using hy
  have ht : GNSTendsto τ a atTop (average e τ hτ htr hfaith p) := by
    have hh := tendsto_iff_norm_sub_tendsto_zero.mp hyt
    simpa only [GNSTendsto,←hay,←map_sub,gnsVector_norm] using hh
  have han (n : ℕ) : q*a n=0 := hker (ha n)
  have ht0 : GNSTendsto τ (fun n : ℕ => q*a n) atTop 0 := by
    simpa only [han] using GNSTendsto.const τ (0:M) (atTop : Filter ℕ)
  have hz : q*average e τ hτ htr hfaith p=0 := GNSTendsto.unique τ hfaith
    ((GNSTendsto.const τ q (atTop : Filter ℕ)).mul τ htr ht ‖q‖ (fun _ => le_rfl)) ht0
  exact HochschildPolar.support_right_annihilate hc
    (IsSelfAdjoint.of_nonneg (average_nonneg e τ hτ htr hfaith hp.nonneg)) hz
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace BoundedHochschild
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hII : PopaTypeII.NoAbelianCorners M)

include e τ hτ htr hfaith h1 hII

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace PopaSeparable
open BoundedHochschild PopaCenter PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
variable (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
  (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
  (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

end PopaSeparable

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hII : PopaTypeII.NoAbelianCorners M)
include e hτ htr hfaith h1 hII

end BoundedHochschild

open scoped ComplexOrder
namespace PopaTypeII
open BoundedHochschild PopaCenter PopaCorner PopaCorners
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma abelian_transfer {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (v : CornerIso p q) (hv : v.final=q) (hab : AbelianProjection hp) :
    AbelianProjection hq := by
  have hvp : (v:M)*p=(v:M) := by
    calc (v:M)*p=((v:M)*v.initial)*p := by rw [v.mul_initial]
         _=(v:M)*(v.initial*p) := mul_assoc _ _ _
         _=(v:M) := by rw [(v.initial_proj.le_iff_mul_eq_left hp).mp v.init_le,v.mul_initial]
  have hpv : p*star (v:M)=star (v:M) := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hvp
  let F (a : algebra hq) : algebra hp := ⟨star (v:M)*(a:M)*(v:M),by
    constructor
    · rw [←mul_assoc,←mul_assoc,hpv]
    · rw [mul_assoc,mul_assoc,hvp,mul_assoc]⟩
  have hF (a b : algebra hq) : (F a:M)*(F b:M)=star (v:M)*((a:M)*(b:M))*(v:M) := by
    change (star (v:M)*(a:M)*(v:M))*(star (v:M)*(b:M)*(v:M))=_
    have hq' : (v:M)*star (v:M)=q := hv
    calc
      _=(star (v:M)*(a:M))*((v:M)*star (v:M))*(b:M)*(v:M) := by simp only [mul_assoc]
      _=star (v:M)*((a:M)*(b:M))*(v:M) := by rw [hq']; simp only [mul_assoc,b.property.1]
  intro a b
  have hh := congrArg Subtype.val (hab (F a) (F b)).eq
  change (F a:M)*(F b:M)=(F b:M)*(F a:M) at hh
  rw [hF,hF] at hh
  have hback (c : algebra hq) : (v:M)*(star (v:M)*(c:M)*(v:M))*star (v:M)=(c:M) := by
    have hq' : (v:M)*star (v:M)=q := hv
    calc _=((v:M)*star (v:M))*(c:M)*((v:M)*star (v:M)) := by simp only [mul_assoc]
         _=(c:M) := by rw [hq',c.property.1,c.property.2]
  apply Subtype.ext
  exact (hback (a*b)).symm.trans ((congrArg (fun x : M => (v:M)*x*star (v:M)) hh).trans (hback (b*a)))

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include e hτ htr hfaith h1 in

theorem abelian_has_typeI_central_support {p : M} (hp : IsStarProjection p)
    (hp0 : p ≠ 0) (hab : AbelianProjection hp) :
    ∃ z : M, ∃ hz : IsStarProjection z, Central z ∧ z ≠ 0 ∧ TypeICorner hz := by
  obtain ⟨z,hz,hzc,hpz,hann⟩ := exists_central_support e τ hτ htr hfaith h1 hp
  have hz0 : z ≠ 0 := by
    intro he; exact hp0 (le_antisymm (by simpa [he] using hpz) hp.nonneg)
  refine ⟨z,hz,hzc,hz0,?_⟩
  intro r hr hrz hr0
  have hex : ∃ a : M, r*a*p ≠ 0 := by
    by_contra hn
    push Not at hn
    have hh := hann r hn
    rw [(hr.le_iff_mul_eq_left hz).mp hrz] at hh
    exact hr0 hh
  obtain ⟨a,ha⟩ := hex
  obtain ⟨v,s,t,hs,ht,hsp,htr',hvi,hvf,hvs,htv,hvp⟩ := corner_polar e hp hr
    (show (r*a*p)*p=r*a*p by rw [mul_assoc,hp.isIdempotentElem.eq])
    (show r*(r*a*p)=r*a*p by rw [←mul_assoc,←mul_assoc,hr.isIdempotentElem.eq])
  have hv0 : v ≠ 0 := by intro hv; exact ha (by simpa [hv] using hvp)
  have ht0 : t ≠ 0 := by
    intro ht0
    have hh := htv
    rw [ht0,zero_mul] at hh
    exact hv0 hh.symm
  let V : CornerIso p t := ⟨v,by rwa [hvi],by rwa [hvi],by rwa [hvi],by rw [hvf]⟩
  exact ⟨t,ht,htr',ht0,abelian_transfer hp ht V hvf hab⟩

include e hτ htr hfaith h1 in
theorem noTypeICentralPart_iff : NoTypeICentralPart M ↔ NoAbelianCorners M := by
  classical
  constructor
  · intro h p hp hp0
    by_contra hn
    push Not at hn
    have hab : AbelianProjection hp := fun a b => hn a b
    obtain ⟨z,hz,hzc,hz0,hI⟩ := abelian_has_typeI_central_support e τ hτ htr hfaith h1 hp hp0 hab
    exact h z hz hzc hz0 hI
  · intro h z hz hzc hz0 hI
    obtain ⟨q,hq,hqz,hq0,hqa⟩ := hI z hz le_rfl hz0
    obtain ⟨a,b,hab⟩ := h q hq hq0
    exact hab (hqa a b)
end PopaTypeII

open scoped ComplexOrder
namespace BoundedHochschild
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : TraceInPredual e τ)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hII : PopaTypeII.NoTypeICentralPart M)
include e τ hτ htr hfaith h1 hII

theorem source_tracial_ordinary_primitive {n : ℕ} (f : Cochain M (n+2))
    (hf : ∀ v, differentialValue f v=0) :
    ∃ g : Cochain M (n+1), ‖g‖≤12*‖f‖ ∧ ∀ v, differentialValue g v=f v := by
  exact arbitrary_typeII_ordinary_primitive e τ hτ htr hfaith h1
    ((PopaTypeII.noTypeICentralPart_iff e τ hτ htr hfaith h1).mp hII) f hf
end BoundedHochschild
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners
open scoped ComplexOrder

universe u

theorem TracialTypeII.primitive {N : Type u} [CStarAlgebra N]
    [PartialOrder N] [StarOrderedRing N] (hN : TracialTypeII N)
    {n : ℕ} (f : Cochain N (n + 2)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain N (n + 1), ‖g‖ ≤ 12 * ‖f‖ ∧
      ∀ x, differentialValue g x = f x := by
  rcases hN with ⟨X, hX, hXS, hXC, e, τ, hτ, htr, hfaith, h1, hII⟩
  let := hX
  let := hXS
  let := hXC
  exact source_tracial_ordinary_primitive e τ hτ htr hfaith h1 hII f hf

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem primitive_of_published_inputs (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hdecomp : CentralDecompositionInput M) (hclassical : ClassicalVanishingInput.{u})
    {n : ℕ} (f : Cochain M (n + 2)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ∀ x, differentialValue g x = f x := by
  classical
  obtain ⟨D⟩ := hdecomp
  let p := D.projection
  let hp := D.isProjection
  let hc := D.central
  let e0 := cornerPredualEquiv (p none) (hp none) e
  let : WStarAlgebra (Corner (p none) (hp none)) :=
    ⟨⟨CornerPredual (p none) (hp none) e, inferInstance, inferInstance,
      inferInstance, ⟨e0⟩⟩⟩
  let f0 := CentralCorner.restrict (p none) (hp none) (hc none) f
  obtain ⟨b0, hb0⟩ := hclassical _ inferInstance D.exceptional n f0
    (CentralCorner.restrict_cocycle _ _ _ f hf)
  let C : ℝ := max ‖b0‖ (12 * ‖f‖)
  have hpieces (i : Option D.Index) :
      ∃ b : Cochain (Corner (p i) (hp i)) (n + 1), ‖b‖ ≤ C ∧
        ∀ x, differentialValue b x = CentralCorner.restrict (p i) (hp i) (hc i) f x := by
    cases i with
    | none => exact ⟨b0, le_max_left _ _, hb0⟩
    | some i =>
      obtain ⟨b, hbn, hb⟩ := (D.tracial i).primitive
        (CentralCorner.restrict (p (some i)) (hp (some i)) (hc (some i)) f)
        (CentralCorner.restrict_cocycle _ _ _ f hf)
      exact ⟨b, hbn.trans ((mul_le_mul_of_nonneg_left
        (CentralCorner.restrict_norm _ _ _ f) (by norm_num)).trans (le_max_right _ _)), hb⟩
  choose b hbn hb using hpieces
  obtain ⟨g, _, hg⟩ := primitive_of_central_cut_primitives e
    (HochschildSakai.mul_hasPreadjoint e) p hp hc D.orthogonal D.total f hf
    (fun i => CentralCorner.extend (p i) (hp i) (hc i) (b i))
    (fun i => CentralCorner.extend_supported _ _ _ _)
    (fun i => CentralCorner.extend_primitive _ _ _ f (b i) (hb i))
    C ((norm_nonneg b0).trans (le_max_left _ _))
    (fun i => (CentralCorner.extend_norm _ _ _ _).trans (hbn i))
  exact ⟨g, hg⟩
end KadisonRingrose
end BoundedHochschild
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.KadisonRingrose.primitive_of_published_inputs.{u} := @OAI.BoundedHochschild.KadisonRingrose.primitive_of_published_inputs.{u}
