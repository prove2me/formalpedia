-- Prove2me | solution 1 for OAI.PopaCenter.full_center_lift_norm
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:49:23.792065+00:00
-- url     : https://prove2.me/submissions/d980b8bb-e4d9-419c-bfd5-11f6ff1e946d

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_PopaCenter_exists_dyadic_system

set_option Elab.async false
set_option linter.all false

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

lemma preGNS_sq_le_trace (a : M) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖τ.toPreGNS a‖^2 ≤ (τ a).re := by
  have hs := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS a))
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS,
    (IsSelfAdjoint.of_nonneg ha).star_eq,← Complex.ofReal_pow,Complex.ofReal_re] at hs
  rw [hs]
  apply Complex.re_le_re
  apply τ.monotone
  simpa only [pow_two,pow_one] using CStarAlgebra.pow_antitone ha ha1 (show 1 ≤ 2 by omega)

lemma monotone_contractions_preGNS_cauchy (a : ℕ → M) (h0 : ∀ n, 0 ≤ a n)
    (h1 : ∀ n, a n ≤ 1) (hm : Monotone a) : CauchySeq (fun n => τ.toPreGNS (a n)) := by
  have hmono : Monotone (fun n => (τ (a n)).re) := fun n m hnm =>
    Complex.re_le_re (τ.monotone (hm hnm))
  have hbdd : BddAbove (Set.range (fun n => (τ (a n)).re)) :=
    ⟨(τ 1).re,fun _ ⟨n,hn⟩ => hn ▸ Complex.re_le_re (τ.monotone (h1 n))⟩
  have hc := (tendsto_atTop_ciSup hmono hbdd).cauchySeq
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff'.mp hc (ε^2) (sq_pos_of_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have hd0 : 0 ≤ a n-a N := sub_nonneg.mpr (hm hn)
  have hd1 : a n-a N ≤ 1 := (sub_le_self _ (h0 N)).trans (h1 n)
  have hsq := preGNS_sq_le_trace τ (a n-a N) hd0 hd1
  have hdiff := hN n hn
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hmono hn))] at hdiff
  simp only [map_sub,Complex.sub_re] at hsq
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (τ.toPreGNS (a n)-τ.toPreGNS (a N))]

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

lemma GNSTendsto.star (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    {a : I → M} {l : Filter I} {b : M} (ha : GNSTendsto τ a l b) :
    GNSTendsto τ (fun i => star (a i)) l (star b) := by
  simpa only [GNSTendsto,← star_sub,preGNS_norm_star τ htr] using ha

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

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (Star.star a*a)=0 → a=0)

include e hL hτ htr hfaith in
lemma exists_monotone_projection_limit (a : ℕ → M) (ha : ∀ n, IsStarProjection (a n))
    (ham : Monotone a) :
    ∃ p : M, IsStarProjection p ∧ GNSTendsto τ a atTop p ∧ (∀ n, a n ≤ p) ∧
      ∀ q : M, IsStarProjection q → (∀ n, a n ≤ q) → p ≤ q := by
  obtain ⟨p,_hp,ht⟩ := exists_bounded_preGNS_limit e τ hL hτ 1
    (fun n => (ha n).norm_le _)
    (monotone_contractions_preGNS_cauchy τ a (fun n => (ha n).nonneg)
      (fun n => (ha n).le_one) ham)
  change GNSTendsto τ a atTop p at ht
  have hstar : star p=p := by
    apply GNSTendsto.unique τ hfaith (ht.star τ htr)
    simpa only [(ha _).isSelfAdjoint.star_eq] using ht
  have hmul : p*p=p := by
    apply GNSTendsto.unique τ hfaith (ht.mul τ htr ht 1 (fun n => (ha n).norm_le _))
    simpa only [(ha _).isIdempotentElem.eq] using ht
  have hp : IsStarProjection p := ⟨hmul,hstar⟩
  refine ⟨p,hp,ht,?_,?_⟩
  · intro n
    apply ((ha n).le_iff_mul_eq_left hp).mpr
    apply GNSTendsto.unique τ hfaith
      ((GNSTendsto.const τ (a n) (atTop : Filter ℕ)).mul τ htr ht 1
        (fun _ => (ha n).norm_le _))
    change Tendsto (fun m => ‖τ.toPreGNS (a n*a m-a n)‖) atTop (𝓝 0)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with m hm
    simp only [((ha n).le_iff_mul_eq_left (ha m)).mp (ham hm),sub_self,map_zero,norm_zero]
  · intro q hq haq
    apply (hp.le_iff_mul_eq_left hq).mpr
    apply GNSTendsto.unique τ hfaith
      (ht.mul τ htr (GNSTendsto.const τ q atTop) 1 (fun n => (ha n).norm_le _))
    simpa only [((ha _).le_iff_mul_eq_left hq).mp (haq _)] using ht

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

lemma trace_star_mul_self_re (x : M) : (τ (star x*x)).re=‖τ.toPreGNS x‖^2 := by
  have h := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS x))
  simpa only [PositiveLinearMap.ofPreGNS_toPreGNS,← Complex.ofReal_pow,Complex.ofReal_re]
    using h.symm
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
open Filter Topology
open scoped ComplexOrder
namespace HochschildDiffuse
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  (τ : M →ₚ[ℂ] ℂ)

lemma projection_trace_pos (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) : 0 < (τ p).re := by
  have hpos : 0 ≤ τ p := τ.map_nonneg hp.nonneg
  have hre : 0 ≤ (τ p).re := Complex.nonneg_iff.mp hpos |>.1
  apply lt_of_le_of_ne hre
  intro hz
  have he : τ p=0 := Complex.ext hz.symm (Complex.nonneg_iff.mp hpos).2.symm
  apply hp0
  apply hfaith p
  simpa only [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] using he
end HochschildDiffuse
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
lemma final_proj (v : CornerIso p q) : IsStarProjection v.final := by
  refine ⟨?_,IsSelfAdjoint.mul_star_self _⟩
  change ((v:M)*star (v:M))*((v:M)*star (v:M))=(v:M)*star (v:M)
  calc
    _ = ((v:M)*(star (v:M)*(v:M)))*star (v:M) := by simp only [mul_assoc]
    _ = (v:M)*star (v:M) := by rw [v.absorb]

omit [StarOrderedRing M] in
lemma mul_initial (v : CornerIso p q) : (v:M)*v.initial=(v:M) := v.absorb
omit [StarOrderedRing M] in
lemma final_mul (v : CornerIso p q) : v.final*(v:M)=(v:M) := by
  simpa only [final,mul_assoc] using v.absorb

omit [StarOrderedRing M] in
lemma norm_le_one (v : CornerIso p q) : ‖(v:M)‖ ≤ 1 := by
  have hn := v.init_proj.norm_le
  rw [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (v:M)]

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

lemma star_mul_of_le {v w : CornerIso p q} (h : v ≤ w) :
    star (v:M)*(w:M)=v.initial := by
  have he := congrArg star h.2
  simp only [star_mul,v.initial_proj.isSelfAdjoint.star_eq] at he
  calc
    star (v:M)*(w:M) = (v.initial*star (w:M))*(w:M) := by rw [he]
    _ = v.initial*w.initial := by simp only [initial,mul_assoc]
    _ = v.initial := (v.initial_proj.le_iff_mul_eq_left w.initial_proj).mp h.1

lemma star_mul_of_ge {v w : CornerIso p q} (h : v ≤ w) :
    star (w:M)*(v:M)=v.initial := by
  simpa only [star_mul,star_star,v.initial_proj.isSelfAdjoint.star_eq]
    using congrArg star (star_mul_of_le h)

lemma sub_star_mul {v w : CornerIso p q} (h : v ≤ w) :
    star ((w:M)-(v:M))*((w:M)-(v:M))=w.initial-v.initial := by
  simp only [star_sub,sub_mul,mul_sub,star_mul_of_le h,star_mul_of_ge h]
  change w.initial-v.initial-(v.initial-v.initial)=w.initial-v.initial
  rw [sub_self,sub_zero]

lemma final_mono {v w : CornerIso p q} (h : v ≤ w) : v.final ≤ w.final := by
  apply (v.final_proj.le_iff_mul_eq_right w.final_proj).mpr
  change ((w:M)*star (w:M))*((v:M)*star (v:M))=(v:M)*star (v:M)
  calc
    _ = ((w:M)*(star (w:M)*(v:M)))*star (v:M) := by simp only [mul_assoc]
    _ = (v:M)*star (v:M) := by rw [star_mul_of_ge h,h.2]

def rank (τ : M →ₚ[ℂ] ℂ) (v : CornerIso p q) : ℝ := (τ v.initial).re

lemma rank_mono (τ : M →ₚ[ℂ] ℂ) : Monotone (rank τ : CornerIso p q → ℝ) := by
  intro v w h
  exact Complex.re_le_re (τ.monotone h.1)

lemma gns_sub_sq (τ : M →ₚ[ℂ] ℂ) {v w : CornerIso p q} (h : v ≤ w) :
    ‖τ.toPreGNS ((w:M)-(v:M))‖^2=rank τ w-rank τ v := by
  rw [← trace_star_mul_self_re,sub_star_mul h,map_sub,Complex.sub_re]
  rfl

lemma le_of_comparable_rank_le (τ : M →ₚ[ℂ] ℂ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) {v w : CornerIso p q}
    (hc : v ≤ w ∨ w ≤ v) (ht : rank τ v ≤ rank τ w) : v ≤ w := by
  rcases hc with h|h
  · exact h
  · have ha : (v:M)=(w:M) := by
      apply sub_eq_zero.mp
      apply (preGNS_norm_eq_zero_iff τ hfaith _).mp
      have hh := gns_sub_sq τ h
      nlinarith [norm_nonneg (τ.toPreGNS ((v:M)-(w:M)))]
    exact (ext ha).le

lemma monotone_cauchy (τ : M →ₚ[ℂ] ℂ) (v : ℕ → CornerIso p q)
    (hv : Monotone v) : CauchySeq (fun n => τ.toPreGNS (v n : M)) := by
  have hm : Monotone (fun n => rank τ (v n)) := (rank_mono τ).comp hv
  have hb : BddAbove (Set.range (fun n => rank τ (v n))) := by
    refine ⟨(τ 1).re,?_⟩
    rintro _ ⟨n,rfl⟩
    exact Complex.re_le_re (τ.monotone (v n).initial_proj.le_one)
  have hc := (tendsto_atTop_ciSup hm hb).cauchySeq
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff'.mp hc (ε^2) (sq_pos_of_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have hs := gns_sub_sq τ (hv hn)
  have hd := hN n hn
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hm hn))] at hd
  rw [dist_eq_norm]
  rw [map_sub] at hs
  nlinarith [norm_nonneg (τ.toPreGNS (v n:M)-τ.toPreGNS (v N:M))]

lemma projection_mul_zero_of_le_sub {p r t : M} (hp : IsStarProjection p)
    (hr : IsStarProjection r) (ht : IsStarProjection t) (hrp : r ≤ p) (htr : t ≤ p-r) :
    r*t=0 := by
  have hpr : IsStarProjection (p-r) := (hr.le_iff_sub hp).mp hrp
  have hh := (ht.le_iff_mul_eq_right hpr).mp htr
  calc
    r*t = r*((p-r)*t) := by rw [hh]
    _ = (r*p-r*r)*t := by noncomm_ring
    _ = 0 := by rw [(hr.le_iff_mul_eq_left hp).mp hrp,hr.isIdempotentElem.eq,
      sub_self,zero_mul]

lemma add_orthogonal (hp : IsStarProjection p) (hq : IsStarProjection q)
    (v : CornerIso p q) (u : CornerIso (p-v.initial) (q-v.final)) :
    ∃ w : CornerIso p q, (w:M)=(v:M)+(u:M) ∧ v ≤ w := by
  have hi : v.initial*u.initial=0 := projection_mul_zero_of_le_sub hp
    v.initial_proj u.initial_proj v.init_le u.init_le
  have hir : u.initial*v.initial=0 := by
    simpa only [star_mul,v.initial_proj.isSelfAdjoint.star_eq,
      u.initial_proj.isSelfAdjoint.star_eq,star_zero] using congrArg star hi
  have hf : v.final*u.final=0 := projection_mul_zero_of_le_sub hq
    v.final_proj u.final_proj v.final_le u.final_le
  have hvf : star (v:M)*v.final=star (v:M) := by
    simpa only [star_mul,v.final_proj.isSelfAdjoint.star_eq] using congrArg star v.final_mul
  have hui : u.initial*star (u:M)=star (u:M) := by
    simpa only [star_mul,u.initial_proj.isSelfAdjoint.star_eq] using congrArg star u.mul_initial
  have hcrossi : star (v:M)*(u:M)=0 := by
    calc
      _ = (star (v:M)*v.final)*(u.final*(u:M)) := by rw [hvf,u.final_mul]
      _ = star (v:M)*(v.final*u.final)*(u:M) := by simp only [mul_assoc]
      _ = 0 := by rw [hf,mul_zero,zero_mul]
  have hcrossir : star (u:M)*(v:M)=0 := by
    simpa only [star_mul,star_star,star_zero] using congrArg star hcrossi
  have hcrossf : (v:M)*star (u:M)=0 := by
    calc
      _ = ((v:M)*v.initial)*(u.initial*star (u:M)) := by rw [v.mul_initial,hui]
      _ = (v:M)*(v.initial*u.initial)*star (u:M) := by simp only [mul_assoc]
      _ = 0 := by rw [hi,mul_zero,zero_mul]
  have hcrossfr : (u:M)*star (v:M)=0 := by
    simpa only [star_mul,star_star,star_zero] using congrArg star hcrossf
  have hinit : star ((v:M)+(u:M))*((v:M)+(u:M))=v.initial+u.initial := by
    simp only [star_add,add_mul,mul_add,hcrossi,hcrossir,zero_add,add_zero,initial]
  have hfin : ((v:M)+(u:M))*star ((v:M)+(u:M))=v.final+u.final := by
    simp only [star_add,add_mul,mul_add,hcrossf,hcrossfr,zero_add,add_zero,final]
  have hvui : (v:M)*u.initial=0 := by
    calc
      _ = ((v:M)*v.initial)*u.initial := by rw [v.mul_initial]
      _ = 0 := by rw [mul_assoc,hi,mul_zero]
  have huvi : (u:M)*v.initial=0 := by
    calc
      _ = ((u:M)*u.initial)*v.initial := by rw [u.mul_initial]
      _ = 0 := by rw [mul_assoc,hir,mul_zero]
  have hsum : IsStarProjection (v.initial+u.initial) :=
    v.initial_proj.add u.initial_proj hi
  have hsum_le : v.initial+u.initial ≤ p := by
    calc
      _ ≤ v.initial+(p-v.initial) := add_le_add le_rfl u.init_le
      _ = p := by abel
  have hsumf_le : v.final+u.final ≤ q := by
    calc
      _ ≤ v.final+(q-v.final) := add_le_add le_rfl u.final_le
      _ = q := by abel
  let w : CornerIso p q := ⟨(v:M)+(u:M),by rw [hinit]; exact hsum,
    by rw [hinit]; simp only [add_mul,mul_add,v.mul_initial,u.mul_initial,hvui,huvi,
      zero_add,add_zero],by rw [hinit]; exact hsum_le,by rw [hfin]; exact hsumf_le⟩
  refine ⟨w,rfl,?_,?_⟩
  · change v.initial ≤ star ((v:M)+(u:M))*((v:M)+(u:M))
    rw [hinit]
    exact le_add_of_nonneg_right u.initial_proj.nonneg
  · change ((v:M)+(u:M))*v.initial=(v:M)
    rw [add_mul,v.mul_initial,huvi,add_zero]

section Dual
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e hτ htr hfaith in
lemma rank_tendsto {v : ℕ → CornerIso p q} {w : CornerIso p q}
    (ht : GNSTendsto τ (fun n => (v n:M)) atTop (w:M)) :
    Tendsto (fun n => rank τ (v n)) atTop (𝓝 (rank τ w)) := by
  have hL := (HochschildSakai.abstract_multiplication_normal e).1
  have hi := (ht.star τ htr).mul τ htr ht 1 (fun n => by
    simpa only [norm_star] using (v n).norm_le_one)
  have hp := predual_tendsto_of_preGNS e τ hL hτ hfaith 1
    (fun n => (v n).initial_proj.norm_le _) hi
  exact Complex.continuous_re.tendsto _ |>.comp (trace_predual_tendsto e τ hτ hp)

include e hτ htr hfaith in

theorem monotone_limit (hp : IsStarProjection p) (hq : IsStarProjection q)
    (v : ℕ → CornerIso p q) (hv : Monotone v) :
    ∃ w : CornerIso p q, GNSTendsto τ (fun n => (v n:M)) atTop (w:M) ∧
      (∀ n, v n ≤ w) ∧ (∀ z, (∀ n, v n ≤ z) → w ≤ z) := by
  have hL := (HochschildSakai.abstract_multiplication_normal e).1
  obtain ⟨r,hr,hrt,hrn,hrle⟩ := exists_monotone_projection_limit e τ hL hτ htr hfaith
    (fun n => (v n).initial) (fun n => (v n).initial_proj)
    (fun _ _ h => (hv h).1)
  obtain ⟨s,hs,hst,hsn,hsle⟩ := exists_monotone_projection_limit e τ hL hτ htr hfaith
    (fun n => (v n).final) (fun n => (v n).final_proj)
    (fun _ _ h => final_mono (hv h))
  obtain ⟨w,hw,hwt⟩ := exists_bounded_preGNS_limit e τ hL hτ 1
    (fun n => (v n).norm_le_one) (monotone_cauchy τ v hv)
  change GNSTendsto τ (fun n => (v n:M)) atTop w at hwt
  have hwi : star w*w=r := GNSTendsto.unique τ hfaith
    ((hwt.star τ htr).mul τ htr hwt 1 (fun n => by
      simpa only [norm_star] using (v n).norm_le_one)) hrt
  have hwf : w*star w=s := GNSTendsto.unique τ hfaith
    (hwt.mul τ htr (hwt.star τ htr) 1 (fun n => (v n).norm_le_one)) hst
  have hwa : w*r=w := by
    apply GNSTendsto.unique τ hfaith
      (hwt.mul τ htr hrt 1 (fun n => (v n).norm_le_one))
    simpa only [(v _).mul_initial] using hwt
  let W : CornerIso p q := ⟨w,by rw [hwi]; exact hr,
    by rw [hwi]; exact hwa,
    by rw [hwi]; exact hrle p hp (fun n => (v n).init_le),
    by rw [hwf]; exact hsle q hq (fun n => (v n).final_le)⟩
  refine ⟨W,hwt,?_,?_⟩
  · intro n
    change (v n).initial ≤ star w*w ∧ w*(v n).initial=(v n:M)
    refine ⟨by rw [hwi]; exact hrn n,?_⟩
    apply GNSTendsto.unique τ hfaith
      (hwt.mul τ htr (GNSTendsto.const τ (v n).initial atTop) 1
        (fun m => (v m).norm_le_one))
    change Tendsto (fun m => ‖τ.toPreGNS ((v m:M)*(v n).initial-(v n:M))‖) atTop (𝓝 0)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with m hm
    simp only [(hv hm).2,sub_self,map_zero,norm_zero]
  · intro z hz
    change star w*w ≤ z.initial ∧ (z:M)*(star w*w)=w
    rw [hwi]
    refine ⟨hrle z.initial z.initial_proj (fun n => (hz n).1),?_⟩
    apply GNSTendsto.unique τ hfaith
      ((GNSTendsto.const τ (z:M) atTop).mul τ htr hrt 1
        (fun _ => z.norm_le_one))
    simpa only [(hz _).2] using hwt

include e hτ htr hfaith in

theorem chain_upper (hp : IsStarProjection p) (hq : IsStarProjection q)
    (c : Set (CornerIso p q)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ w : CornerIso p q, ∀ v ∈ c, v ≤ w := by
  classical
  let T : Set ℝ := rank τ '' c
  have hTne : T.Nonempty := Set.Nonempty.image _ hne
  have hTbd : BddAbove T := by
    refine ⟨(τ p).re,?_⟩
    rintro _ ⟨v,hv,rfl⟩
    exact Complex.re_le_re (τ.monotone v.init_le)
  obtain ⟨t,htm,_htL,htt,htc⟩ := (isLUB_csSup hTne hTbd).exists_seq_monotone_tendsto hTne
  choose a ha hat using htc
  change ∀ n, rank τ (a n)=t n at hat
  have ham : Monotone a := by
    intro m n hmn
    apply le_of_comparable_rank_le τ hfaith (hc.total (ha m) (ha n))
    rw [hat,hat]
    exact htm hmn
  obtain ⟨w,hwt,hwn,hwl⟩ := monotone_limit e τ hτ htr hfaith hp hq a ham
  have hwr : rank τ w=sSup T := by
    apply tendsto_nhds_unique (rank_tendsto e τ hτ htr hfaith hwt)
    simpa only [hat] using htt
  refine ⟨w,?_⟩
  intro v hv
  by_cases hex : ∃ n, v ≤ a n
  · obtain ⟨n,hn⟩ := hex
    exact hn.trans (hwn n)
  · have haw : ∀ n, a n ≤ v := by
      intro n
      exact (hc.total (ha n) hv).resolve_right (fun h => hex ⟨n,h⟩)
    apply le_of_comparable_rank_le τ hfaith (Or.inr (hwl v haw))
    rw [hwr]
    exact le_csSup hTbd ⟨v,hv,rfl⟩

def zero (hp : IsStarProjection p) (hq : IsStarProjection q) : CornerIso p q :=
  ⟨0,by simpa only [star_zero,zero_mul] using IsStarProjection.zero M,
    by simp only [zero_mul],by simpa only [zero_mul,star_zero] using hp.nonneg,
    by simpa only [zero_mul,star_zero] using hq.nonneg⟩

include e hτ htr hfaith in
lemma exists_maximal (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ v : CornerIso p q, ∀ w : CornerIso p q, v ≤ w → w ≤ v := by
  classical
  obtain ⟨v,_hv,hmax⟩ := zorn_le_nonempty₀ (Set.univ : Set (CornerIso p q))
    (fun c hc hchain y hy => by
      obtain ⟨w,hw⟩ := chain_upper e τ hτ htr hfaith hp hq c hchain ⟨y,hy⟩
      exact ⟨w,Set.mem_univ w,hw⟩) (zero hp hq) (Set.mem_univ _)
  exact ⟨v,fun w hw => hmax.2 (Set.mem_univ w) hw⟩
end Dual
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

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_star {a : M} (ha : Central a) : Central (star a) := by
  intro x
  change star a*x=x*star a
  have h := congrArg star (ha (star x)).eq
  simpa only [star_mul,star_star] using h.symm
omit [PartialOrder M] [StarOrderedRing M] in
lemma central_sub {a b : M} (ha : Central a) (hb : Central b) : Central (a-b) :=
  fun x => (ha x).sub_left (hb x)
omit [PartialOrder M] [StarOrderedRing M] in
lemma central_mul {a b : M} (ha : Central a) (hb : Central b) : Central (a*b) :=
  fun x => (ha x).mul_left (hb x)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma average_norm (a : M) : ‖average e τ hτ htr hfaith a‖ ≤ ‖a‖ :=
  (exists_central_average e τ (HochschildSakai.abstract_multiplication_normal e).1
    hτ htr hfaith a).choose_spec.1
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

omit h1 in
include hfaith in
omit [StarOrderedRing M] in
lemma central_unique {b c : M} (hb : Central b) (hc : Central c)
    (h : ∀ z : M, Central z → τ (z*b)=τ (z*c)) : b=c := by
  apply sub_eq_zero.mp
  apply hfaith
  rw [mul_sub,map_sub,h _ (central_star (central_sub hb hc)),sub_self]

lemma average_eq (a b : M) (hb : Central b)
    (h : ∀ z : M, Central z → τ (z*b)=τ (z*a)) : average e τ hτ htr hfaith a=b := by
  apply central_unique τ hfaith (average_central e τ hτ htr hfaith a) hb
  intro z hz
  rw [average_pair e τ hτ htr hfaith h1 hz,h z hz]

lemma average_id {a : M} (ha : Central a) : average e τ hτ htr hfaith a=a :=
  average_eq e τ hτ htr hfaith h1 a a ha (fun _ _ => rfl)
lemma average_add (a b : M) : average e τ hτ htr hfaith (a+b)=
    average e τ hτ htr hfaith a+average e τ hτ htr hfaith b := by
  apply average_eq e τ hτ htr hfaith h1
  · intro x
    exact (average_central e τ hτ htr hfaith a x).add_left
      (average_central e τ hτ htr hfaith b x)
  · intro z hz
    rw [mul_add,map_add,mul_add,map_add,average_pair e τ hτ htr hfaith h1 hz,
      average_pair e τ hτ htr hfaith h1 hz]
lemma average_smul (r : ℂ) (a : M) : average e τ hτ htr hfaith (r • a)=
    r • average e τ hτ htr hfaith a := by
  apply average_eq e τ hτ htr hfaith h1
  · intro x; exact (average_central e τ hτ htr hfaith a x).smul_left r
  · intro z hz
    rw [mul_smul_comm,mul_smul_comm,map_smul,map_smul,average_pair e τ hτ htr hfaith h1 hz]

def expectation : M →L[ℂ] M := LinearMap.mkContinuous
  { toFun := average e τ hτ htr hfaith
    map_add' := average_add e τ hτ htr hfaith h1
    map_smul' := average_smul e τ hτ htr hfaith h1 }
  1 (by intro a; simpa using average_norm e τ hτ htr hfaith a)
@[simp] lemma expectation_apply (a : M) :
    expectation e τ hτ htr hfaith h1 a=average e τ hτ htr hfaith a := rfl

lemma average_bimodule {z : M} (hz : Central z) (a : M) :
    average e τ hτ htr hfaith (z*a)=z*average e τ hτ htr hfaith a := by
  apply average_eq e τ hτ htr hfaith h1
  · exact central_mul hz (average_central e τ hτ htr hfaith a)
  · intro w hw
    simpa only [←mul_assoc] using average_pair e τ hτ htr hfaith h1 (central_mul hw hz) a
lemma average_trace (a b : M) : average e τ hτ htr hfaith (a*b)=
    average e τ hτ htr hfaith (b*a) := by
  apply average_eq e τ hτ htr hfaith h1
  · exact average_central e τ hτ htr hfaith _
  · intro z hz
    rw [average_pair e τ hτ htr hfaith h1 hz,←mul_assoc,htr,←mul_assoc,
      ←(hz a).eq,mul_assoc]

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

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorners PopaCorners.CornerIso
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include e in
lemma maximal_separates {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (v : CornerIso p q) (hv : ∀ w : CornerIso p q, v ≤ w → w ≤ v) :
    ∀ a : M, (q-v.final)*a*(p-v.initial)=0 := by
  intro a
  by_contra hh
  have hr := (v.initial_proj.le_iff_sub hp).mp v.init_le
  have hs := (v.final_proj.le_iff_sub hq).mp v.final_le
  let b := (q-v.final)*a*(p-v.initial)
  obtain ⟨t,r,s,htI,htF,hrp,hsq,hti,htf,htrt,_hstt,hb⟩ :=
    corner_polar e hr hs (show b*(p-v.initial)=b by
      dsimp [b]; rw [mul_assoc,hr.isIdempotentElem.eq])
      (show (q-v.final)*b=b by dsimp [b]; rw [←mul_assoc,←mul_assoc,hs.isIdempotentElem.eq])
  let u : CornerIso (p-v.initial) (q-v.final) :=
    ⟨t,by rw [hti]; exact htI,by rw [hti]; exact htrt,
      by rw [hti]; exact hrp,by rw [htf]; exact hsq⟩
  obtain ⟨w,hw,hle⟩ := add_orthogonal hp hq v u
  have he : w=v := le_antisymm (hv w hle) hle
  have hsum : (v:M)+t=(v:M) := by simpa only [he] using hw.symm
  have ht0 : t=0 := add_eq_left.mp hsum
  exact hh (by change b=0; rw [hb,ht0,zero_mul])

include htr in
omit [StarOrderedRing M] in
lemma central_rank_trace {p q z : M} (v : CornerIso p q) (hz : Central z) :
    τ (z*v.initial)=τ (z*v.final) := by
  change τ (z*(star (v:M)*(v:M)))=τ (z*((v:M)*star (v:M)))
  rw [←mul_assoc,(hz (star (v:M))).eq,mul_assoc,htr,←mul_assoc]

include e hτ htr hfaith h1 in

theorem exists_full_initial_of_central_cuts {p q : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : ∀ c : M, IsStarProjection c → Central c →
      (τ (c*p)).re ≤ (τ (c*q)).re) :
    ∃ v : CornerIso p q, v.initial=p := by
  obtain ⟨v,hv⟩ := exists_maximal e τ hτ htr hfaith hp hq
  have hr := (v.initial_proj.le_iff_sub hp).mp v.init_le
  have hs := (v.final_proj.le_iff_sub hq).mp v.final_le
  obtain ⟨c,hc,hcc,hrc,hcs⟩ := exists_central_support e τ hτ htr hfaith h1 hr
  have hscr : (q-v.final)*c=0 := hcs _ (maximal_separates e hp hq v hv)
  have hcsr : c*(q-v.final)=0 := (hcc _).eq.trans hscr
  have hcr : c*(p-v.initial)=p-v.initial := (hr.le_iff_mul_eq_right hc).mp hrc
  have hi := central_rank_trace τ htr v hcc
  have hle := hpq c hc hcc
  have hτs : τ (c*q)=τ (c*v.final) := by
    exact sub_eq_zero.mp (by simpa only [mul_sub,map_sub,map_zero] using congrArg τ hcsr)
  have hτr : τ (c*p)-τ (c*v.initial)=τ (p-v.initial) := by
    simpa only [mul_sub,map_sub] using congrArg τ hcr
  have hnr : (τ (p-v.initial)).re ≤ 0 := by
    rw [hτs,←hi] at hle
    have hh := congrArg Complex.re hτr
    simp only [Complex.sub_re] at hh
    linarith
  have hz : p-v.initial=0 := by
    by_contra hh
    exact (not_lt_of_ge hnr) (HochschildDiffuse.projection_trace_pos τ hfaith hr hh)
  exact ⟨v,(sub_eq_zero.mp hz).symm⟩

include e hτ htr hfaith h1 in
theorem exists_full_initial_of_average_le {p q : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : average e τ hτ htr hfaith p ≤ average e τ hτ htr hfaith q) :
    ∃ v : CornerIso p q, v.initial=p := by
  apply exists_full_initial_of_central_cuts e τ hτ htr hfaith h1 hp hq
  intro c hc hcc
  rw [←average_pair e τ hτ htr hfaith h1 hcc p,
    ←average_pair e τ hτ htr hfaith h1 hcc q]
  apply Complex.re_le_re
  apply τ.monotone
  have h := star_right_conjugate_nonneg (sub_nonneg.mpr hpq) c
  rw [hc.isSelfAdjoint.star_eq,mul_sub,sub_mul,
    ←(average_central e τ hτ htr hfaith q c).eq,
    ←(average_central e τ hτ htr hfaith p c).eq,mul_assoc,mul_assoc,
    hc.isIdempotentElem.eq] at h
  rw [(average_central e τ hτ htr hfaith q c).eq,
    (average_central e τ hτ htr hfaith p c).eq] at h
  exact sub_nonneg.mp h
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ}
namespace System
variable (s : System n (1:M))

omit [PartialOrder M] [StarOrderedRing M] in
lemma diagonal_projection (i : Fin n) : IsStarProjection (s.entry i i) := by
  exact ⟨by simp only [IsIdempotentElem,s.mul_entry,↓reduceIte],
    by exact s.star_entry i i⟩

def commutant : StarSubalgebra ℂ M where
  carrier := {a | ∀ i j, Commute a (s.entry i j)}
  zero_mem' := fun _ _ => Commute.zero_left _
  one_mem' := fun _ _ => Commute.one_left _
  add_mem' := fun ha hb i j => (ha i j).add_left (hb i j)
  mul_mem' := fun ha hb i j => (ha i j).mul_left (hb i j)
  algebraMap_mem' := fun c i j => Algebra.commutes c (s.entry i j)
  star_mem' := by
    intro a ha i j
    change star a*s.entry i j=s.entry i j*star a
    have h := congrArg star (ha j i).eq
    simpa only [star_mul,s.star_entry] using h.symm

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma mem_commutant (a : M) : a ∈ s.commutant ↔ ∀ i j, Commute a (s.entry i j) := Iff.rfl
end System
end PopaMatrices
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaMatrices.System
open HochschildRigidity
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} (s : PopaMatrices.System n (1:M))
variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))

end PopaMatrices.System

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
lemma average_diagonal_mul {n : ℕ} (s : System n (1:M)) (i j : Fin n)
    (a : M) (ha : a ∈ s.commutant) :
    average e τ hτ htr hfaith (s.entry i i*a)=average e τ hτ htr hfaith (s.entry j j*a) := by
  calc
    _ = average e τ hτ htr hfaith (s.entry i j*(s.entry j i*a)) := by
      rw [←mul_assoc,s.mul_entry,ite_eq_left rfl]
    _ = average e τ hτ htr hfaith ((s.entry j i*a)*s.entry i j) := average_trace e τ hτ htr hfaith h1 _ _
    _ = _ := by rw [mul_assoc,(ha i j).eq,←mul_assoc,s.mul_entry,ite_eq_left rfl]

include h1 in
lemma average_diagonal {n : ℕ} (s : System n (1:M)) (i : Fin n)
    (a : M) (ha : a ∈ s.commutant) :
    (n:ℝ) • average e τ hτ htr hfaith (s.entry i i*a)=average e τ hτ htr hfaith a := by
  calc
    _ = ∑ j : Fin n, average e τ hτ htr hfaith (s.entry j j*a) := by
      simp only [←average_diagonal_mul e τ hτ htr hfaith h1 s i _ a ha,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.cast_smul_eq_nsmul]
    _ = _ := by
      change (∑ j, expectation e τ hτ htr hfaith h1 (s.entry j j*a))=expectation e τ hτ htr hfaith h1 a
      rw [←map_sum,←Finset.sum_mul,s.sum_diag,one_mul]

include h1 in
lemma average_diagonal_one {n : ℕ} (s : System n (1:M)) (i : Fin n) :
    (n:ℝ) • average e τ hτ htr hfaith (s.entry i i)=1 := by
  simpa only [mul_one,average_id e τ hτ htr hfaith h1 (fun x => Commute.one_left x)] using
    average_diagonal e τ hτ htr hfaith h1 s i 1 s.commutant.one_mem
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {p : M} (hp : IsStarProjection p) (τ : M →ₚ[ℂ] ℂ)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

end PopaCorner

open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaMatrices
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {p : M} (hp : IsStarProjection p)

omit [PartialOrder M] [StarOrderedRing M] in
lemma full_center_lift {n : ℕ} (a b : Fin n → M)
    (ha : ∀ i, a i*p=a i) (hb : ∀ i, p*b i=b i) (hs : ∑ i, a i*b i=1)
    (x : algebra hp) (hx : ∀ z : algebra hp, Commute x z) :
    ∃ c : M, (∀ y : M, Commute c y) ∧ c*p=(x:M) := by
  let c : M := ∑ i, a i*(x:M)*b i
  have hz (z : M) (hz : z*p=z) : c*z=z*(x:M) := by
    have hm (i : Fin n) : b i*z ∈ algebra hp := by
      exact ⟨by rw [←mul_assoc,hb],by rw [mul_assoc,hz]⟩
    have hc (i : Fin n) : (x:M)*(b i*z)=(b i*z)*(x:M) :=
      congrArg Subtype.val (hx ⟨b i*z,hm i⟩).eq
    calc
      c*z = ∑ i, a i*((x:M)*(b i*z)) := by simp only [c,Finset.sum_mul,mul_assoc]
      _ = ∑ i, (a i*b i)*z*(x:M) := by simp only [hc,mul_assoc]
      _ = z*(x:M) := by rw [←Finset.sum_mul,←Finset.sum_mul,hs,one_mul]
  refine ⟨c,fun y => ?_,?_⟩
  · change c*y=y*c
    calc
      c*y = (c*y)*(∑ i, a i*b i) := by rw [hs,mul_one]
      _ = ∑ i, (c*(y*a i))*b i := by simp only [Finset.mul_sum,mul_assoc]
      _ = ∑ i, ((y*a i)*(x:M))*b i := by
        apply Finset.sum_congr rfl; intro i _
        rw [hz (y*a i) (by rw [mul_assoc,ha])]
      _ = y*c := by simp only [c,Finset.mul_sum,mul_assoc]
  · rw [hz p hp.isIdempotentElem.eq,x.property.1]

section Dual
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end Dual
end PopaCorner

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaTypeII PopaMatrices PopaCorner
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
lemma full_corner_center (hII : NoAbelianCorners M) {p : M} (hp : IsStarProjection p)
    {t : ℝ} (ht : 0 < t) (hEp : average e τ hτ htr hfaith p=t • (1:M)) :
    ∃ n : ℕ, ∃ a b : Fin n → M,
      (∀ i, a i*p=a i) ∧ (∀ i, p*b i=b i) ∧ ∑ i, a i*b i=1 := by
  obtain ⟨k,hk⟩ := exists_nat_gt (1/t)
  have hpow : k < 2^(k+1) := lt_trans (Nat.lt_succ_self k) (Nat.lt_two_pow_self)
  have hn : 0 < 2^(k+1) := pow_pos (by omega) _
  have hnR : 0 < ((2^(k+1):ℕ):ℝ) := Nat.cast_pos.mpr hn
  have hle : ((2^(k+1):ℕ):ℝ)⁻¹ ≤ t := by
    have hh := hk.trans (Nat.cast_lt.mpr hpow)
    have hh' := (div_lt_iff₀ ht).mp hh
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hnR).mpr
    nlinarith
  obtain ⟨s⟩ := exists_dyadic_system e τ hτ htr hfaith h1 hII (k+1)
  let i0 : Fin (2^(k+1)) := ⟨0,hn⟩
  have hs := s.diagonal_projection i0
  have hEs : average e τ hτ htr hfaith (s.entry i0 i0)=((2^(k+1):ℕ):ℝ)⁻¹ • (1:M) := by
    have hh := congrArg (fun z : M => ((2^(k+1):ℕ):ℝ)⁻¹ • z)
      (average_diagonal_one e τ hτ htr hfaith h1 s i0)
    simpa only [smul_smul,inv_mul_cancel₀ hnR.ne',one_smul] using hh
  have he : average e τ hτ htr hfaith (s.entry i0 i0) ≤ average e τ hτ htr hfaith p := by
    rw [hEs,hEp]
    exact smul_le_smul_of_nonneg_right hle (zero_le_one)
  obtain ⟨v,hvi⟩ := exists_full_initial_of_average_le e τ hτ htr hfaith h1 hs hp he
  have hpv : p*(v:M)=(v:M) := by
    rw [←v.final_mul,←mul_assoc,(v.final_proj.le_iff_mul_eq_right hp).mp v.final_le,v.final_mul]
  have hvp : star (v:M)*p=star (v:M) := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hpv
  refine ⟨2^(k+1),fun i => s.entry i i0*star (v:M),fun i => (v:M)*s.entry i0 i,?_,?_,?_⟩
  · intro i; rw [mul_assoc,hvp]
  · intro i; rw [←mul_assoc,hpv]
  · have he (i : Fin (2^(k+1))) :
        (s.entry i i0*star (v:M))*((v:M)*s.entry i0 i)=s.entry i i := by
      rw [mul_assoc,←mul_assoc (star _),show star (v:M)*(v:M)=s.entry i0 i0 from hvi,
        ←mul_assoc,s.mul_entry,ite_eq_left rfl,s.mul_entry,ite_eq_left rfl]
    simp only [he,s.sum_diag]
end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorner
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def centerAlgebra : StarSubalgebra ℂ M where
  carrier := {a | Central a}
  zero_mem' := fun x => Commute.zero_left x
  one_mem' := fun x => Commute.one_left x
  add_mem' ha hb := fun x => (ha x).add_left (hb x)
  mul_mem' ha hb := central_mul ha hb
  algebraMap_mem' r := fun x => Algebra.commutes r x
  star_mem' ha := central_star ha

instance centerAlgebra_closed : IsClosed (centerAlgebra (M:=M) : Set M) := by
  change IsClosed {a : M | ∀ x : M, a*x=x*a}
  simpa only [Set.ofPred_forall,id_eq,Pi.mul_apply] using isClosed_iInter (fun x : M => isClosed_eq
    ((continuous_id : Continuous (fun a : M => a)).mul_const x)
    ((continuous_const : Continuous (fun _ : M => x)).mul continuous_id))

def centerCompression {p : M} (hp : IsStarProjection p) :
    centerAlgebra (M:=M) →⋆ₐ[ℂ] algebra hp where
  toFun a := ⟨(a:M)*p,by
    constructor
    · rw [←mul_assoc,←(a.property p).eq,mul_assoc,hp.isIdempotentElem.eq]
    · rw [mul_assoc,hp.isIdempotentElem.eq]⟩
  map_one' := Subtype.ext (one_mul p)
  map_mul' a b := Subtype.ext (by
    change ((a:M)*(b:M))*p=((a:M)*p)*((b:M)*p)
    rw [mul_assoc (a:M) p,←mul_assoc p,←(b.property p).eq,mul_assoc (b:M),hp.isIdempotentElem.eq,mul_assoc])
  map_zero' := Subtype.ext (zero_mul p)
  map_add' a b := Subtype.ext (add_mul (a:M) (b:M) p)
  commutes' r := Subtype.ext (by change (algebraMap ℂ M r)*p=r • p; simp [Algebra.algebraMap_eq_smul_one])
  map_star' a := Subtype.ext (by
    change star (a:M)*p=star ((a:M)*p)
    rw [star_mul,hp.isSelfAdjoint.star_eq]
    exact (central_star a.property p).eq)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1
lemma centerCompression_injective {p : M} (hp : IsStarProjection p)
    {t : ℝ} (ht : 0<t) (hEp : average e τ hτ htr hfaith p=t • (1:M)) :
    Function.Injective (centerCompression hp) := by
  intro a b hab
  have hh := congrArg (average e τ hτ htr hfaith) (congrArg Subtype.val hab)
  change average e τ hτ htr hfaith ((a:M)*p)=average e τ hτ htr hfaith ((b:M)*p) at hh
  rw [average_bimodule e τ hτ htr hfaith h1 a.property,
    average_bimodule e τ hτ htr hfaith h1 b.property,hEp,mul_smul_comm,mul_smul_comm,mul_one,mul_one] at hh
  exact Subtype.ext ((smul_right_injective M ht.ne') hh)

lemma center_compression_norm {p : M} (hp : IsStarProjection p)
    {t : ℝ} (ht : 0<t) (hEp : average e τ hτ htr hfaith p=t • (1:M))
    {a : M} (ha : Central a) : ‖a*p‖=‖a‖ :=
  NonUnitalStarAlgHom.norm_map (centerCompression hp)
    (centerCompression_injective e τ hτ htr hfaith h1 hp ht hEp) ⟨a,ha⟩

lemma full_center_lift_norm (hII : PopaTypeII.NoAbelianCorners M) {p : M}
    (hp : IsStarProjection p) {t : ℝ} (ht : 0<t)
    (hEp : average e τ hτ htr hfaith p=t • (1:M))
    (x : algebra hp) (hx : Central x) :
    ∃ c : M, Central c ∧ c*p=(x:M) ∧ ‖c‖=‖x‖ := by
  obtain ⟨n,a,b,ha,hb,hs⟩ := full_corner_center e τ hτ htr hfaith h1 hII hp ht hEp
  obtain ⟨c,hc,hcp⟩ := full_center_lift hp a b ha hb hs x hx
  refine ⟨c,hc,hcp,?_⟩
  rw [←center_compression_norm e τ hτ htr hfaith h1 hp ht hEp hc,hcp]
  rfl
end PopaCenter
end
end OAI
end

theorem solution.{u} : type_of% @OAI.PopaCenter.full_center_lift_norm.{u} := @OAI.PopaCenter.full_center_lift_norm.{u}
