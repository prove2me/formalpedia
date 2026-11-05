-- Prove2me | solution 1 for OAI.PopaCenter.exists_matrix_energy_decrease_center
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:49:19.730786+00:00
-- url     : https://prove2.me/submissions/b1f49717-01e8-40f8-b67d-8e6e3ef17c1f

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
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

lemma preGNS_norm_unitary_right (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (x : M) (u : unitary M) : ‖τ.toPreGNS (x*(u:M))‖ = ‖τ.toPreGNS x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply Complex.ofReal_injective
  push_cast
  simp only [PositiveLinearMap.preGNS_norm_sq,PositiveLinearMap.ofPreGNS_toPreGNS,star_mul]
  rw [mul_assoc (star (u:M))]
  rw [htr (star (u:M)) (star x*(x*(u:M)))]
  simp [mul_assoc]
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

lemma projection_le_of_comparable_trace_le
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hcomp : p ≤ q ∨ q ≤ p) (ht : (τ p).re ≤ (τ q).re) : p ≤ q := by
  rcases hcomp with h|h
  · exact h
  · have hz : p-q=0 := by
      by_contra hn
      have hh := projection_trace_pos τ hfaith ((hq.le_iff_sub hp).mp h) hn
      rw [map_sub,Complex.sub_re] at hh
      linarith
    exact (sub_eq_zero.mp hz).le
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
lemma trace_average (a : M) : τ (average e τ hτ htr hfaith a)=τ a := by
  simpa only [one_mul] using average_pair e τ hτ htr hfaith h1 (z:=1)
    (fun x => Commute.one_left x) a
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

include h1 in
lemma average_mono : Monotone (average e τ hτ htr hfaith) := by
  intro a b hab
  have hp := average_nonneg e τ hτ htr hfaith (sub_nonneg.mpr hab)
  change 0 ≤ expectation e τ hτ htr hfaith h1 (b-a) at hp
  rw [map_sub] at hp
  exact sub_nonneg.mp hp

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
include e hτ htr hfaith h1 in
theorem equivalent_of_average_eq {p q : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q)
    (hpq : average e τ hτ htr hfaith p=average e τ hτ htr hfaith q) :
    ∃ v : M, star v*v=p ∧ v*star v=q ∧ v*p=v ∧ q*v=v := by
  obtain ⟨v,hvp⟩ := exists_full_initial_of_average_le e τ hτ htr hfaith h1 hp hq hpq.le
  have hpqt : τ p=τ q := by
    rw [←trace_average e τ hτ htr hfaith h1 p,←trace_average e τ hτ htr hfaith h1 q,hpq]
  have htrace : (τ v.final).re=(τ q).re := by
    change (τ ((v:M)*star (v:M))).re=(τ q).re
    rw [htr]
    change (τ v.initial).re=(τ q).re
    rw [hvp,hpqt]
  have hqv : q ≤ v.final := HochschildDiffuse.projection_le_of_comparable_trace_le τ hfaith
    hq v.final_proj (Or.inr v.final_le) htrace.ge
  have hvq : v.final=q := le_antisymm v.final_le hqv
  exact ⟨(v:M),hvp,hvq,by simpa only [hvp] using v.mul_initial,
    by simpa only [hvq] using v.final_mul⟩
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

omit [PartialOrder M] [StarOrderedRing M] in
lemma sumExpect_commutes (x : M) (a b : Fin n) : Commute (s.sumExpect x) (s.entry a b) := by
  classical
  change (∑ i, ∑ j, s.entry i j*x*s.entry j i)*s.entry a b =
    s.entry a b*(∑ i, ∑ j, s.entry i j*x*s.entry j i)
  simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc,s.mul_entry,mul_ite,mul_zero]
  simp only [← mul_assoc,s.mul_entry,ite_mul,zero_mul]
  simp

omit [PartialOrder M] [StarOrderedRing M] in
lemma expect_mem (x : M) : s.expect x ∈ s.commutant := by
  intro a b
  exact (s.sumExpect_commutes x a b).smul_left _

omit [PartialOrder M] [StarOrderedRing M] in
lemma expect_bimodule (a b x : M) (ha : a ∈ s.commutant) (hb : b ∈ s.commutant) :
    s.expect (a*x*b)=a*s.expect x*b := by
  simp only [expect,mul_smul_comm,smul_mul_assoc]
  congr 1
  simp only [sumExpect,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  calc
    s.entry i j*(a*x*b)*s.entry j i = a*s.entry i j*x*(b*s.entry j i) := by
      simp only [← mul_assoc]
      rw [← (ha i j).eq]
    _ = a*(s.entry i j*x*s.entry j i)*b := by rw [(hb j i).eq]; simp only [mul_assoc]

omit [StarOrderedRing M] in
lemma trace_sumExpect (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (x : M) :
    τ (s.sumExpect x)=(n : ℕ) • τ x := by
  classical
  calc
    τ (s.sumExpect x) = ∑ i : Fin n, ∑ j, τ (s.entry j j*x) := by
      simp only [sumExpect,map_sum]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [htr,← mul_assoc,s.mul_entry,ite_eq_left rfl]
    _ = (n : ℕ) • τ x := by
      rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,← map_sum,← Finset.sum_mul,s.sum_diag,one_mul]

omit [StarOrderedRing M] in
lemma trace_expect (hn : 0 < n) (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a)) (x : M) : τ (s.expect x)=τ x := by
  rw [expect,← Complex.coe_smul,map_smul,s.trace_sumExpect τ htr x,
    ← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  have hn0 : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  simp only [Complex.ofReal_inv,Complex.ofReal_natCast,inv_mul_cancel₀ hn0,one_smul]

end System
end PopaMatrices

open scoped ComplexOrder
namespace PopaMatrices.System
open HochschildRigidity
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} (s : PopaMatrices.System n (1:M))
variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))

include htr
omit [StarOrderedRing M] in
lemma expect_pairing (hn : 0 < n) (x a : M) (ha : a ∈ s.commutant) :
    τ (star a*s.expect x)=τ (star a*x) := by
  have he := s.expect_bimodule (star a) 1 x (s.commutant.star_mem' ha) s.commutant.one_mem
  simp only [mul_one] at he
  rw [← he,s.trace_expect hn τ htr]

lemma expect_orthogonal (hn : 0 < n) (x : M) :
    inner ℂ (τ.toPreGNS (s.expect x)) (τ.toPreGNS (x-s.expect x))=0 := by
  rw [PositiveLinearMap.preGNS_inner_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS,mul_sub,map_sub]
  rw [s.expect_pairing τ htr hn x _ (s.expect_mem x),sub_self]

lemma expect_pythagoras (hn : 0 < n) (x : M) :
    ‖τ.toPreGNS x‖^2 = ‖τ.toPreGNS (s.expect x)‖^2 + ‖τ.toPreGNS (x-s.expect x)‖^2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (τ.toPreGNS (s.expect x)) (τ.toPreGNS (x-s.expect x)) (s.expect_orthogonal τ htr hn x)
  simpa only [← map_add,add_sub_cancel,pow_two] using h

lemma commutator_norm_le_residual (x p : M) (hp : IsStarProjection p)
    (hc : Commute (s.expect x) p) :
    ‖τ.toPreGNS (x*p-p*x)‖ ≤ 2*‖τ.toPreGNS (x-s.expect x)‖ := by
  have he : x*p-p*x=(x-s.expect x)*p-p*(x-s.expect x) := by
    simp only [sub_mul,mul_sub,hc.eq]; abel
  rw [he,map_sub]
  calc
    ‖τ.toPreGNS ((x-s.expect x)*p)-τ.toPreGNS (p*(x-s.expect x))‖ ≤
        ‖τ.toPreGNS ((x-s.expect x)*p)‖+‖τ.toPreGNS (p*(x-s.expect x))‖ := norm_sub_le _ _
    _ ≤ ‖p‖*‖τ.toPreGNS (x-s.expect x)‖+‖p‖*‖τ.toPreGNS (x-s.expect x)‖ :=
      add_le_add (preGNS_norm_mul_right_le τ htr _ _) (preGNS_norm_mul_le τ _ _)
    _ ≤ 2*‖τ.toPreGNS (x-s.expect x)‖ := by nlinarith [hp.norm_le,norm_nonneg (τ.toPreGNS (x-s.expect x))]

lemma energy_drop (hn : 0 < n) (x p : M) (hp : IsStarProjection p)
    (hc : Commute (s.expect x) p) :
    ‖τ.toPreGNS (s.expect x)‖^2 ≤ ‖τ.toPreGNS x‖^2 -
      ‖τ.toPreGNS (x*p-p*x)‖^2/4 := by
  have h := s.commutator_norm_le_residual τ htr x p hp hc
  have hh := s.expect_pythagoras τ htr hn x
  nlinarith [norm_nonneg (τ.toPreGNS (x*p-p*x)),norm_nonneg (τ.toPreGNS (x-s.expect x))]
end PopaMatrices.System
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaCorners
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end PopaMatrices

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorners PopaCorners.CornerIso PopaMatrices PopaTypeII
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildSakai
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_smul_real (r : ℝ) {a : M} (ha : Central a) : Central (r • a) := by
  intro x
  change (r • a)*x=x*(r • a)
  rw [smul_mul_assoc,mul_smul_comm,(ha x).eq]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_posPart {a : M} (ha : Central a) : Central a⁺ := by
  intro x
  exact (ha x).cfcₙ_real (fun r : ℝ => r⁺)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

include e in
theorem exists_central_dyadic_projection (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ha : Central a) :
    ∃ p : M, IsStarProjection p ∧ Central p ∧ 0 ≤ (2:ℝ) • a-p ∧ (2:ℝ) • a-p ≤ 1 := by
  let b : M := a-(1/2:ℝ) • (1:M)
  let c : M := b⁺
  let d : M := b⁻
  have hbsa : IsSelfAdjoint b := (IsSelfAdjoint.of_nonneg ha0).sub
    (IsSelfAdjoint.of_nonneg (smul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) zero_le_one))
  have hb : c-d=b := CFC.posPart_sub_negPart b hbsa
  have hc0 : 0 ≤ c := CFC.posPart_nonneg b
  have hd0 : 0 ≤ d := CFC.negPart_nonneg b
  obtain ⟨p,hp⟩ := exists_support_projection e c hc0
  have hpd : p*d=0 := hp.annihilate d (CFC.posPart_mul_negPart b)
  have hdp : d*p=0 := by
    simpa only [star_mul,(IsSelfAdjoint.of_nonneg hd0).star_eq,
      hp.proj.isSelfAdjoint.star_eq,star_zero] using congrArg star hpd
  have hcp : b*p=c := by rw [← hb,sub_mul,hp.right,hdp,sub_zero]
  have hpc : p*b=c := by rw [← hb,mul_sub,hp.left,hpd,sub_zero]
  have hac : Commute a p := by
    change a*p=p*a
    have hh := hcp.trans hpc.symm
    dsimp [b] at hh
    simpa only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,
      sub_left_inj] using hh
  have har : 0 ≤ a*(1-p) :=
    (show Commute a (1-p) from (Commute.one_right a).sub_right hac).mul_nonneg ha0
      (sub_nonneg.mpr hp.proj.le_one)
  have hal : 0 ≤ (1-a)*p :=
    ((Commute.one_left p).sub_left hac).mul_nonneg (sub_nonneg.mpr ha1) hp.proj.nonneg
  have hpa : a*p=c+(1/2:ℝ) • p := by
    dsimp [b] at hcp
    rw [sub_mul,smul_mul_assoc,one_mul] at hcp
    exact sub_eq_iff_eq_add.mp hcp
  have hlow : 0 ≤ a-(1/2:ℝ) • p := by
    have he : a-(1/2:ℝ) • p=c+a*(1-p) := by
      rw [mul_sub,mul_one,hpa]
      module
    rw [he]
    exact add_nonneg hc0 har
  have hhigh : 0 ≤ (1/2:ℝ) • (1:M)-(a-(1/2:ℝ) • p) := by
    have he : (1/2:ℝ) • (1:M)-(a-(1/2:ℝ) • p)=(1-a)*p+d := by
      rw [sub_mul,one_mul,hpa]
      have haa : a=c-d+(1/2:ℝ) • (1:M) := by
        exact (sub_eq_iff_eq_add.mp hb.symm)
      conv_lhs => rw [haa]
      module
    rw [he]
    exact add_nonneg hal hd0
  refine ⟨p,hp.proj,?_,?_,?_⟩
  · apply support_central hp
    exact central_posPart (central_sub ha (central_smul_real _ (fun x => Commute.one_left x)))
  · have hh := smul_nonneg (by norm_num : (0:ℝ) ≤ 2) hlow
    convert hh using 1; module
  · apply sub_nonneg.mp
    have hh := smul_nonneg (by norm_num : (0:ℝ) ≤ 2) hhigh
    convert hh using 1; module

include e in

theorem central_dyadic_digits (k : ℕ) (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ha : Central a) :
    ∃ z : Fin (2^k) → M, (∀ i, IsStarProjection (z i)) ∧ (∀ i, Central (z i)) ∧
      0 ≤ (2:ℝ)^k • a-∑ i, z i ∧ (2:ℝ)^k • a-∑ i, z i ≤ 1 := by
  induction k generalizing a with
  | zero =>
    refine ⟨fun _ => 0,fun _ => IsStarProjection.zero M,fun _ x => Commute.zero_left x,?_,?_⟩ <;>
      simpa only [pow_zero,one_smul,Finset.sum_const_zero,sub_zero]
  | succ k ih =>
    obtain ⟨p,hp,hpc,hp0,hp1⟩ := exists_central_dyadic_projection e a ha0 ha1 ha
    obtain ⟨z,hz,hzc,hz0,hz1⟩ := ih ((2:ℝ) • a-p) hp0 hp1
      (central_sub (central_smul_real 2 ha) hpc)
    rw [pow_succ,Nat.mul_two]
    let y := Fin.append (fun _ : Fin (2^k) => p) z
    have hy (i : Fin (2^k+2^k)) : IsStarProjection (y i) := by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [y,Fin.append_left] using hp
      · simpa only [y,Fin.append_right] using hz j
    have hyc (i : Fin (2^k+2^k)) : Central (y i) := by
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [y,Fin.append_left] using hpc
      · simpa only [y,Fin.append_right] using hzc j
    have he : (2:ℝ)^(k+1) • a-∑ i, y i = (2:ℝ)^k • ((2:ℝ) • a-p)-∑ i, z i := by
      simp only [y,Fin.sum_univ_add,Fin.append_left,Fin.append_right,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,←Nat.cast_smul_eq_nsmul ℝ,Nat.cast_pow,Nat.cast_ofNat,
        pow_succ,smul_sub,smul_smul]
      module
    refine ⟨y,hy,hyc,?_,?_⟩ <;> simpa only [←pow_succ,he] using (by assumption : _)
end PopaCenter
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

variable {n : ℕ}
def diagonal (s : System n (1:M)) (z : Fin n → M) : M := ∑ i, z i*s.entry i i

omit [PartialOrder M] [StarOrderedRing M] in
lemma diagonal_projection (s : System n (1:M)) (z : Fin n → M)
    (hz : ∀ i, IsStarProjection (z i)) (hc : ∀ i, Central (z i)) :
    IsStarProjection (diagonal s z) := by
  classical
  have h (i j : Fin n) : (z i*s.entry i i)*(z j*s.entry j j)=if i=j then z i*s.entry i i else 0 := by
    rw [mul_assoc,←mul_assoc (s.entry i i),(hc j _).eq.symm,mul_assoc (z j),s.mul_entry]
    by_cases hij : i=j
    · subst j; simp only [↓reduceIte,←mul_assoc, (hz i).isIdempotentElem.eq]
    · simp only [ite_eq_right hij,mul_zero]
  refine ⟨?_,?_⟩
  · change (∑ i, z i*s.entry i i)*(∑ i, z i*s.entry i i)=∑ i, z i*s.entry i i
    simp only [Finset.sum_mul,Finset.mul_sum,h]
    simp
  · change star (∑ i, z i*s.entry i i)=∑ i, z i*s.entry i i
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact ((hz i).mul (s.diagonal_projection i) (hc i _)).isSelfAdjoint.star_eq

omit [PartialOrder M] [StarOrderedRing M] in
lemma diagonal_commutes (s : System n (1:M)) (z : Fin n → M)
    (hc : ∀ i, Central (z i)) (a : M) (ha : a ∈ s.commutant) :
    Commute a (diagonal s z) := by
  apply Commute.sum_right
  intro i _
  exact (hc i a).symm.mul_right (ha i i)

include h1 in
lemma average_diagonal_sum (s : System n (1:M)) (z : Fin n → M)
    (hc : ∀ i, Central (z i)) :
    (n:ℝ) • average e τ hτ htr hfaith (diagonal s z)=∑ i, z i := by
  change (n:ℝ) • expectation e τ hτ htr hfaith h1 (∑ i, z i*s.entry i i)=_
  rw [map_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (n:ℝ) • average e τ hτ htr hfaith (z i*s.entry i i)=z i
  rw [average_bimodule e τ hτ htr hfaith h1 (hc i),←mul_smul_comm,
    average_diagonal_one e τ hτ htr hfaith h1,mul_one]
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaMatrices.System
open HochschildRigidity PopaQuantization
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} (s : PopaMatrices.System n (1:M))

variable (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
include htr

end PopaMatrices.System

open Filter Topology
open scoped ComplexOrder
namespace PopaQuantization
open BoundedHochschild HochschildDiffuse HochschildSakai
universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
variable {E : Type v} [SeminormedAddCommGroup E] [NormedSpace ℂ E]

include e
lemma contraction_bound_of_projection_bound (T : M →L[ℂ] E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hp : ∀ p : M, IsStarProjection p → ‖T p‖ ≤ δ)
    (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : ‖T a‖ ≤ δ := by
  have hbound : ∀ n : ℕ, ∀ b : M, 0 ≤ b → b ≤ 1 →
      ‖T b‖ ≤ δ + (1/2:ℝ)^n * ‖T‖ := by
    intro n
    induction n with
    | zero =>
      intro b hb0 hb1
      have h := (T.le_opNorm b).trans
        (mul_le_of_le_one_right (norm_nonneg _)
          ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hb0).mpr hb1))
      simpa only [pow_zero,one_mul] using h.trans (le_add_of_nonneg_left hδ)
    | succ n ih =>
      intro b hb0 hb1
      obtain ⟨p,hp0,h0,h1⟩ := exists_dyadic_projection e b hb0 hb1
      have hh := ih ((2:ℝ) • b-p) h0 h1
      have he : (2:ℝ) • T b=T ((2:ℝ) • b-p)+T p := by
        simp only [map_sub, ← Complex.coe_smul,map_smul]; module
      have hh' := norm_add_le (T ((2:ℝ) • b-p)) (T p)
      rw [← he,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)] at hh'
      have hpp := hp p hp0
      rw [pow_succ]
      nlinarith
  have ht : Tendsto (fun n : ℕ => δ + (1/2:ℝ)^n * ‖T‖) atTop (𝓝 δ) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).mul_const ‖T‖).const_add δ
  exact ge_of_tendsto ht (Eventually.of_forall fun n => hbound n a ha0 ha1)

lemma positive_bound_of_projection_bound (T : M →L[ℂ] E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hp : ∀ p : M, IsStarProjection p → ‖T p‖ ≤ δ)
    (a : M) (ha : 0 ≤ a) : ‖T a‖ ≤ δ*‖a‖ := by
  by_cases ha0 : a=0
  · simp [ha0]
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  let b : M := ‖a‖⁻¹ • a
  have hb0 : 0 ≤ b := smul_nonneg (inv_nonneg.mpr hn.le) ha
  have hbn : ‖b‖=1 := by simp [b,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le),hn.ne']
  have hb1 : b ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hb0).mp hbn.le
  have h := contraction_bound_of_projection_bound e T δ hδ hp b hb0 hb1
  have hab : a=‖a‖ • b := by simp [b,smul_smul,hn.ne']
  calc
    ‖T a‖ = ‖a‖*‖T b‖ := by
      conv_lhs => rw [hab]
      rw [← Complex.coe_smul,map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg a)]
    _ ≤ ‖a‖*δ := mul_le_mul_of_nonneg_left h hn.le
    _ = δ*‖a‖ := mul_comm _ _

lemma bound_of_projection_bound (T : M →L[ℂ] E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hp : ∀ p : M, IsStarProjection p → ‖T p‖ ≤ δ) (a : M) :
    ‖T a‖ ≤ 4*δ*‖a‖ := by
  obtain ⟨x,hx0,hxn,hx⟩ := CStarAlgebra.exists_sum_four_nonneg a
  calc
    ‖T a‖ = ‖∑ i : Fin 4, Complex.I^i.val • T (x i)‖ := by rw [hx,map_sum]; simp
    _ ≤ ∑ i : Fin 4, ‖Complex.I^i.val • T (x i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 4, ‖T (x i)‖ := by simp only [norm_smul,norm_pow,Complex.norm_I,one_pow,one_mul]
    _ ≤ ∑ _i : Fin 4, δ*‖a‖ := Finset.sum_le_sum fun i _ =>
      (positive_bound_of_projection_bound e T δ hδ hp (x i) (hx0 i)).trans
        (mul_le_mul_of_nonneg_left (hxn i) hδ)
    _ = 4*δ*‖a‖ := by simp; ring
end PopaQuantization

open Filter Topology
open scoped ComplexOrder
namespace PopaQuantization
open HochschildRigidity BoundedHochschild HochschildDixmier
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

def commutatorMap (h1 : τ 1=1) (b : M) : M →L[ℂ] τ.PreGNS :=
  (TracialUltrapower.traceHilbertMap τ h1).comp
    (((ContinuousLinearMap.mul ℂ M).flip b)-(ContinuousLinearMap.mul ℂ M b))

@[simp] lemma commutatorMap_apply (h1 : τ 1=1) (b a : M) :
    commutatorMap τ h1 b a=τ.toPreGNS (a*b-b*a) := rfl

end PopaQuantization

open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

lemma projection_norm_sq {p : M} (hp : IsStarProjection p) :
    ‖τ.toPreGNS p‖^2=(τ p).re := by
  have h := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS p))
  simpa only [← Complex.ofReal_pow,Complex.ofReal_re,PositiveLinearMap.ofPreGNS_toPreGNS,
    hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq] using h
end PopaMatrices
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaQuantization
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

include htr in
lemma commutator_difference_bound (b p q : M) :
    ‖τ.toPreGNS (p*b-b*p)‖ ≤ ‖τ.toPreGNS (q*b-b*q)‖ +
      2*‖b‖*‖τ.toPreGNS (p-q)‖ := by
  have he : p*b-b*p=(q*b-b*q)+((p-q)*b-b*(p-q)) := by
    simp only [sub_mul,mul_sub]; abel
  rw [he,map_add]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [map_sub]
  calc
    ‖τ.toPreGNS ((p-q)*b)-τ.toPreGNS (b*(p-q))‖ ≤
        ‖τ.toPreGNS ((p-q)*b)‖+‖τ.toPreGNS (b*(p-q))‖ := norm_sub_le _ _
    _ ≤ ‖b‖*‖τ.toPreGNS (p-q)‖+‖b‖*‖τ.toPreGNS (p-q)‖ :=
      add_le_add (preGNS_norm_mul_right_le τ htr _ _) (preGNS_norm_mul_le τ _ _)
    _ = _ := by ring
end PopaQuantization
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
variable {n : ℕ} (s : PopaMatrices.System n (1:M))
variable (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorners PopaCorners.CornerIso PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include e hτ htr hfaith h1 in
lemma conjugate_of_average_eq {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (he : average e τ hτ htr hfaith p=average e τ hτ htr hfaith q) :
    ∃ u : unitary M, (u:M)*p*star (u:M)=q := by
  obtain ⟨v,hvp,hvq,hvr,hvl⟩ := equivalent_of_average_eq e τ hτ htr hfaith h1 hp hq he
  have hec : average e τ hτ htr hfaith (1-p)=average e τ hτ htr hfaith (1-q) := by
    change expectation e τ hτ htr hfaith h1 (1-p)=expectation e τ hτ htr hfaith h1 (1-q)
    simp only [map_sub,expectation_apply,he]
  obtain ⟨b,hbp,hbq,hbr,hbl⟩ := equivalent_of_average_eq e τ hτ htr hfaith h1 hp.one_sub hq.one_sub hec
  let vi : CornerIso (1:M) 1 := ⟨v,by rw [hvp]; exact hp,by rw [hvp]; exact hvr,
    by rw [hvp]; exact hp.le_one,by rw [hvq]; exact hq.le_one⟩
  let bi : CornerIso (1-vi.initial) (1-vi.final) := ⟨b,by rw [hbp]; exact hp.one_sub,
    by rw [hbp]; exact hbr,by change star b*b ≤ 1-(star v*v); rw [hbp,hvp],
    by change b*star b ≤ 1-(v*star v); rw [hbq,hvq]⟩
  obtain ⟨w,hw,hvw⟩ := add_orthogonal (IsStarProjection.one M) (IsStarProjection.one M) vi bi
  have hcross : star v*b=0 := by
    have hsv : star v*q=star v := by
      simpa only [star_mul,hq.isSelfAdjoint.star_eq] using congrArg star hvl
    calc
      star v*b=(star v*q)*((1-q)*b) := by rw [hsv,hbl]
      _=star v*(q*(1-q))*b := by simp only [mul_assoc]
      _=0 := by rw [mul_sub,mul_one,hq.isIdempotentElem.eq,sub_self,mul_zero,zero_mul]
  have hcross' : star b*v=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hcross
  have hwi : w.initial=1 := by
    change star (w:M)*(w:M)=1
    rw [hw]
    change star (v+b)*(v+b)=1
    simp only [star_add,add_mul,mul_add,hcross,hcross',hvp,hbp,add_zero,zero_add]
    abel
  have hwf : w.final=1 := by
    apply le_antisymm w.final_le
    apply HochschildDiffuse.projection_le_of_comparable_trace_le τ hfaith
      (IsStarProjection.one M) w.final_proj (Or.inr w.final_le)
    have ht : τ w.final=τ w.initial := htr (w:M) (star (w:M))
    rw [hwi] at ht
    exact le_of_eq (congrArg Complex.re ht.symm)
  let u : unitary M := ⟨(w:M),⟨hwi,hwf⟩⟩
  have hu : (u:M)*p=v := by simpa only [vi,initial,hvp] using hvw.2
  refine ⟨u,?_⟩
  calc
    (u:M)*p*star (u:M)=((u:M)*p)*star ((u:M)*p) := by
      simp only [star_mul,hp.isSelfAdjoint.star_eq,mul_assoc,←mul_assoc p p,hp.isIdempotentElem.eq]
    _ = q := by rw [hu,hvq]

namespace System
variable {n : ℕ} (s : PopaMatrices.System n (1:M))

def conjugated (u : unitary M) : PopaMatrices.System n (1:M) where
  entry i j := Unitary.conjStarAlgAut ℂ M u (s.entry i j)
  star_entry i j := by rw [←map_star,s.star_entry]
  mul_entry i j k l := by
    rw [←map_mul,s.mul_entry]
    split_ifs <;> simp only [map_zero]
  sum_diag := by rw [←map_sum,s.sum_diag,map_one]
lemma conjugated_expect (u : unitary M) (x : M) :
    (conjugated s u).expect x=Unitary.conjStarAlgAut ℂ M u
      (s.expect ((Unitary.conjStarAlgAut ℂ M u).symm x)) := by
  have hs (r : ℝ) (a : M) : Unitary.conjStarAlgAut ℂ M u (r • a)=
      r • Unitary.conjStarAlgAut ℂ M u a := by
    simp only [Unitary.conjStarAlgAut_apply,mul_smul_comm,smul_mul_assoc]
  simp only [PopaMatrices.System.expect,PopaMatrices.System.sumExpect,hs,map_sum,map_mul,
    StarAlgEquiv.apply_symm_apply,conjugated]

lemma conjugated_commutes (u : unitary M) (q : M)
    (hq : ∀ x : M, Commute (s.expect x) q) (x : M) :
    Commute ((conjugated s u).expect x) (Unitary.conjStarAlgAut ℂ M u q) := by
  rw [conjugated_expect]
  exact (hq _).map (Unitary.conjStarAlgAut ℂ M u)
end System
end PopaCenter

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaMatrices PopaTypeII PopaCorners PopaCorners.CornerIso
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include e hτ htr hfaith h1 in

theorem exists_matrix_approximating_projection_center (hII : NoAbelianCorners M)
    {p : M} (hp : IsStarProjection p) (η : ℝ) (hη : 0 < η) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : PopaMatrices.System n (1:M), ∃ q : M,
      IsStarProjection q ∧ q ≤ p ∧ ‖τ.toPreGNS (p-q)‖^2 < η ∧
      ∀ x : M, Commute (s.expect x) q := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  obtain ⟨k,hk⟩ := ((tendsto_order.mp ht).2 η hη).exists
  have hkp : 0 < (2:ℝ)^k := pow_pos (by norm_num) _
  have hki : ((2:ℝ)^k)⁻¹ < η := by simpa only [one_div,inv_pow] using hk
  have hn : 0 < 2^k := pow_pos (by omega) _
  obtain ⟨s⟩ := exists_dyadic_system e τ hτ htr hfaith h1 hII k
  have hap := average_nonneg e τ hτ htr hfaith hp.nonneg
  have hap1 : average e τ hτ htr hfaith p ≤ 1 := by
    simpa only [average_id e τ hτ htr hfaith h1 (fun x => Commute.one_left x)] using
      average_mono e τ hτ htr hfaith h1 hp.le_one
  obtain ⟨z,hz,hzc,hz0,hz1⟩ := central_dyadic_digits e k (average e τ hτ htr hfaith p)
    hap hap1 (average_central e τ hτ htr hfaith p)
  let a := diagonal s z
  have ha := diagonal_projection s z hz hzc
  have hea : (2:ℝ)^k • average e τ hτ htr hfaith a=∑ i, z i := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using average_diagonal_sum e τ hτ htr hfaith h1 s z hzc
  have herr : (2:ℝ)^k • (average e τ hτ htr hfaith p-average e τ hτ htr hfaith a)=
      (2:ℝ)^k • average e τ hτ htr hfaith p-∑ i, z i := by rw [smul_sub,hea]
  have hao : average e τ hτ htr hfaith a ≤ average e τ hτ htr hfaith p := by
    apply sub_nonneg.mp
    have hh := smul_nonneg (inv_pos.mpr hkp).le hz0
    rwa [←herr,smul_smul,inv_mul_cancel₀ hkp.ne',one_smul] at hh
  have herror : average e τ hτ htr hfaith p-average e τ hτ htr hfaith a ≤
      ((2:ℝ)^k)⁻¹ • (1:M) := by
    have hh := smul_le_smul_of_nonneg_left hz1 (inv_pos.mpr hkp).le
    rwa [←herr,smul_smul,inv_mul_cancel₀ hkp.ne',one_smul] at hh
  obtain ⟨v,hva⟩ := exists_full_initial_of_average_le e τ hτ htr hfaith h1 ha hp hao
  have hev : average e τ hτ htr hfaith a=average e τ hτ htr hfaith v.final := by
    calc
      _=average e τ hτ htr hfaith v.initial := congrArg (average e τ hτ htr hfaith) hva.symm
      _=_ := average_trace e τ hτ htr hfaith h1 (star (v:M)) (v:M)
  obtain ⟨u,hu⟩ := conjugate_of_average_eq e τ hτ htr hfaith h1 ha v.final_proj hev
  refine ⟨2^k,hn,System.conjugated s u,v.final,v.final_proj,v.final_le,?_,?_⟩
  · rw [projection_norm_sq τ ((v.final_proj.le_iff_sub hp).mp v.final_le),map_sub,Complex.sub_re]
    have hh : (τ (average e τ hτ htr hfaith p-average e τ hτ htr hfaith a)).re ≤
        (τ (((2:ℝ)^k)⁻¹ • (1:M))).re := Complex.re_le_re (τ.monotone herror)
    rw [map_sub,trace_average e τ hτ htr hfaith h1,
      trace_average e τ hτ htr hfaith h1,τ.map_smul_of_tower,h1] at hh
    have heτ : τ a=τ v.final := by
      rw [←trace_average e τ hτ htr hfaith h1 a,hev,trace_average e τ hτ htr hfaith h1]
    simp only [Complex.sub_re,Complex.real_smul,Complex.ofReal_re,mul_one] at hh
    rw [heτ] at hh
    exact hh.trans_lt hki
  · intro x
    have hh := System.conjugated_commutes s u a
      (fun x => diagonal_commutes s z hzc (s.expect x) (s.expect_mem x)) x
    simpa only [Unitary.conjStarAlgAut_apply,a,hu] using hh
end PopaCenter

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDixmier PopaQuantization PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
include e in
lemma center_distance_le_projection_commutators (h1 : τ 1=1)
    (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (b : M) (δ : ℝ) (hδ : 0 ≤ δ)
    (hp : ∀ p : M, IsStarProjection p → ‖τ.toPreGNS (p*b-b*p)‖ ≤ δ) :
    ‖τ.toPreGNS (b-average e τ hτ htr hfaith b)‖ ≤ 4*δ := by
  have : Nontrivial M := nontrivial_of_ne (1:M) 0 (by
    intro hz
    have hh := congrArg τ hz
    exact one_ne_zero (by simpa only [h1,map_zero] using hh))
  have hu (u : unitary M) : ‖τ.toPreGNS (conjugate u b-b)‖ ≤ 4*δ := by
    have hh := bound_of_projection_bound e (commutatorMap τ h1 b) δ hδ
      (fun p hp0 => by simpa only [commutatorMap_apply] using hp p hp0) (u:M)
    have he : conjugate u b-b=((u:M)*b-b*(u:M))*star (u:M) := by
      rw [sub_mul,mul_assoc b,Unitary.mul_star_self_of_mem u.property,mul_one]
      rfl
    rw [he]
    change ‖τ.toPreGNS (((u:M)*b-b*(u:M))*(star u : unitary M))‖ ≤ _
    rw [preGNS_norm_unitary_right τ htr]
    simpa only [CStarRing.norm_coe_unitary,mul_one,commutatorMap_apply] using hh
  have hsub : gnsVector τ '' convexHull ℝ (Set.range (fun u : unitary M => conjugate u b)) ⊆
      Metric.closedBall (gnsVector τ b) (4*δ) := by
    rw [(gnsVector τ).image_convexHull]
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨c,⟨u,rfl⟩,rfl⟩
    simpa only [Metric.mem_closedBall,dist_eq_norm,← map_sub,gnsVector_norm] using hu u
  have hc := average_orbit e τ hτ htr hfaith b
  have hh := closure_minimal hsub Metric.isClosed_closedBall hc
  have hh' : ‖τ.toPreGNS (average e τ hτ htr hfaith b-b)‖ ≤ 4*δ := by
    simpa only [Metric.mem_closedBall,dist_eq_norm,← map_sub,gnsVector_norm] using hh
  simpa only [map_sub,norm_sub_rev] using hh'

include e in

theorem exists_large_projection_commutator_center (h1 : τ 1=1)
    (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (b : M) (hbτ : average e τ hτ htr hfaith b=0) (hb : 0 < ‖τ.toPreGNS b‖) :
    ∃ p : M, IsStarProjection p ∧ ‖τ.toPreGNS b‖/8 < ‖τ.toPreGNS (p*b-b*p)‖ := by
  by_contra h
  push Not at h
  have hh := center_distance_le_projection_commutators e τ h1 hτ htr hfaith b
    (‖τ.toPreGNS b‖/8) (by positivity) h
  simp only [hbτ,sub_zero] at hh
  linarith

variable (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
include e hτ htr hfaith h1 in

theorem exists_matrix_energy_decrease_center (hII : NoAbelianCorners M)
    (b : M) (hbτ : average e τ hτ htr hfaith b=0) (hb : 0 < ‖τ.toPreGNS b‖) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : System n (1:M),
      ‖τ.toPreGNS (s.expect b)‖^2 < (1-1/1024:ℝ)*‖τ.toPreGNS b‖^2 := by
  obtain ⟨p,hp,hcomm⟩ := exists_large_projection_commutator_center e τ h1 hτ htr hfaith b hbτ hb
  let ε : ℝ := ‖τ.toPreGNS b‖/(32*(‖b‖+1))
  have hε : 0 < ε := div_pos hb (by positivity)
  obtain ⟨n,hn,s,q,hq,_hqp,happrox,hcq⟩ := exists_matrix_approximating_projection_center
    e τ hτ htr hfaith h1 hII hp (ε^2) (sq_pos_of_pos hε)
  have hap : ‖τ.toPreGNS (p-q)‖ < ε := by nlinarith [norm_nonneg (τ.toPreGNS (p-q))]
  have hεeq : 32*(‖b‖+1)*ε=‖τ.toPreGNS b‖ := by
    dsimp [ε]; field_simp
  have hsmall : 2*‖b‖*‖τ.toPreGNS (p-q)‖ < ‖τ.toPreGNS b‖/16 := by
    nlinarith [mul_nonneg (norm_nonneg b) (le_of_lt (sub_pos.mpr hap))]
  have hcb := commutator_difference_bound τ htr b p q
  have hlarge : ‖τ.toPreGNS b‖/16 < ‖τ.toPreGNS (b*q-q*b)‖ := by
    rw [map_sub,norm_sub_rev,← map_sub]
    linarith
  have he := s.energy_drop τ htr hn b q hq (hcq b)
  refine ⟨n,hn,s,?_⟩
  nlinarith [sq_nonneg (‖τ.toPreGNS (b*q-q*b)‖-‖τ.toPreGNS b‖/16)]
end PopaCenter
end
end OAI
end

theorem solution.{u} : type_of% @OAI.PopaCenter.exists_matrix_energy_decrease_center.{u} := @OAI.PopaCenter.exists_matrix_energy_decrease_center.{u}
