-- Prove2me | solution 1 for OAI.BoundedHochschild.primitive_of_separable_normal_finite_paths
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:06:10.386184+00:00
-- url     : https://prove2.me/submissions/d6c7bad5-c3a2-4101-b19a-09bb7c81b288

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_BoundedHochschild_primitive_of_walk_and_last_modulus

set_option Elab.async false
set_option linter.all false

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

lemma norm_pow_pos_contraction (b : M) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (n : ℕ) :
    ‖b^n‖ ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (CStarAlgebra.pow_nonneg hb0 n)).mpr
  simpa only [pow_zero] using CStarAlgebra.pow_antitone hb0 hb1 (Nat.zero_le n)

include e hL hτ htr hfaith in

theorem exists_power_projection (b : M) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∃ p : M, IsStarProjection p ∧ GNSTendsto τ (fun n : ℕ => b^n) atTop p ∧
      b*p=p ∧ ∀ x : M, b*x=x → p*x=x := by
  let a : ℕ → M := fun n => 1-b^n
  have ha0 : ∀ n, 0 ≤ a n := fun n => sub_nonneg.mpr (by
    simpa only [pow_zero] using CStarAlgebra.pow_antitone hb0 hb1 (Nat.zero_le n))
  have ha1 : ∀ n, a n ≤ 1 := fun n => sub_le_self _ (CStarAlgebra.pow_nonneg hb0 n)
  have ham : Monotone a := fun n m hnm => sub_le_sub_left
    (CStarAlgebra.pow_antitone hb0 hb1 hnm) 1
  obtain ⟨c,_hc,ht⟩ := exists_bounded_preGNS_limit e τ hL hτ 1
    (fun n => (CStarAlgebra.norm_le_one_iff_of_nonneg _ (ha0 n)).mpr (ha1 n))
    (monotone_contractions_preGNS_cauchy τ a ha0 ha1 ham)
  let p : M := 1-c
  have hp : GNSTendsto τ (fun n : ℕ => b^n) atTop p := by
    simpa only [a,sub_sub_cancel] using (GNSTendsto.const τ (1:M) (atTop : Filter ℕ)).sub τ ht
  have hpstar : star p=p := by
    apply GNSTendsto.unique τ hfaith (hp.star τ htr)
    simpa only [star_pow,(IsSelfAdjoint.of_nonneg hb0).star_eq] using hp
  have htimes : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have hpp : p*p=p := by
    apply GNSTendsto.unique τ hfaith (hp.mul τ htr hp 1 (norm_pow_pos_contraction b hb0 hb1))
    simpa only [GNSTendsto,Function.comp_def,two_mul,pow_add] using
      (show Tendsto (fun n : ℕ => ‖τ.toPreGNS (b^(2*n)-p)‖) atTop (𝓝 0) from hp.comp htimes)
  have hbp : b*p=p := by
    apply GNSTendsto.unique τ hfaith
      ((GNSTendsto.const τ b (atTop : Filter ℕ)).mul τ htr hp ‖b‖ (fun _ => le_rfl))
    simpa only [GNSTendsto,Function.comp_def,pow_succ'] using hp.comp (tendsto_add_atTop_nat 1)
  refine ⟨p,⟨hpp,hpstar⟩,hp,hbp,?_⟩
  intro x hx
  have hpow (n : ℕ) : b^n*x=x := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ',mul_assoc,ih,hx]
  apply GNSTendsto.unique τ hfaith
    (hp.mul τ htr (GNSTendsto.const τ x atTop) 1 (norm_pow_pos_contraction b hb0 hb1))
  simpa only [hpow] using GNSTendsto.const τ x (atTop : Filter ℕ)

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
lemma exists_support_contraction (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ p : M, IsSupportProjection a p ∧
      GNSTendsto τ (fun n : ℕ => 1-(1-a)^n) atTop p := by
  obtain ⟨q,hq,ht,hbq,hqx⟩ := exists_power_projection e τ hL hτ htr hfaith (1-a)
    (sub_nonneg.mpr ha1) (sub_le_self _ ha0)
  have haq : a*q=0 := by
    have hh := hbq
    rw [sub_mul,one_mul] at hh
    exact sub_eq_self.mp hh
  have hqa : q*a=0 := by
    simpa only [star_mul,hq.isSelfAdjoint.star_eq,(IsSelfAdjoint.of_nonneg ha0).star_eq,star_zero]
      using congrArg Star.star haq
  refine ⟨1-q,⟨hq.one_sub,?_,?_,?_⟩,?_⟩
  · simp only [sub_mul,one_mul,hqa,sub_zero]
  · simp only [mul_sub,mul_one,haq,sub_zero]
  · intro x hx
    have hbx : (1-a)*x=x := by simp only [sub_mul,one_mul,hx,sub_zero]
    simp only [sub_mul,one_mul,hqx x hbx,sub_self]
  · exact (GNSTendsto.const τ 1 (atTop : Filter ℕ)).sub τ ht

include e hL hτ htr hfaith in

theorem exists_support_projection (a : M) (ha : 0 ≤ a) :
    ∃ p : M, IsSupportProjection a p := by
  let r : ℝ := ‖a‖+1
  have hr : 0 < r := by dsimp [r]; positivity
  have hi : 0 < r⁻¹ := inv_pos.mpr hr
  have hn : ‖r⁻¹ • a‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hi]
    exact (inv_mul_le_one₀ hr).mpr (by dsimp [r]; linarith)
  have hsa : 0 ≤ r⁻¹ • a := smul_nonneg hi.le ha
  obtain ⟨p,hp,_⟩ := exists_support_contraction e τ hL hτ htr hfaith (r⁻¹ • a) hsa
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hsa).mp hn)
  refine ⟨p,hp.proj,?_,?_,?_⟩
  · have hh := congrArg (fun z : M => r • z) hp.left
    simpa only [mul_smul_comm,smul_smul,mul_inv_cancel₀ hr.ne',one_smul] using hh
  · have hh := congrArg (fun z : M => r • z) hp.right
    simpa only [smul_mul_assoc,smul_smul,mul_inv_cancel₀ hr.ne',one_smul] using hh
  · intro x hx
    apply hp.annihilate x
    simp only [smul_mul_assoc,hx,smul_zero]

lemma IsSupportProjection.le_of_support {a p q : M} (hp : IsSupportProjection a p)
    (hq : IsStarProjection q) (haq : a*q=a) : p ≤ q := by
  apply (hp.proj.le_iff_mul_eq_left hq).mpr
  have hh := hp.annihilate (1-q) (by simp only [mul_sub,mul_one,haq,sub_self])
  simpa only [mul_sub,mul_one,sub_eq_zero,eq_comm] using hh

lemma IsSupportProjection.unique {a p q : M} (hp : IsSupportProjection a p)
    (hq : IsSupportProjection a q) : p=q :=
  le_antisymm (hp.le_of_support hq.proj hq.right) (hq.le_of_support hp.proj hp.right)
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

omit [PartialOrder M] [StarOrderedRing M] in
lemma IsSupportProjection.smul {a p : M} (hp : IsSupportProjection a p)
    (r : ℝ) (hr : r ≠ 0) : IsSupportProjection (r • a) p := by
  refine ⟨hp.proj,?_,?_,?_⟩
  · rw [mul_smul_comm,hp.left]
  · rw [smul_mul_assoc,hp.right]
  · intro x hx
    apply hp.annihilate x
    rw [smul_mul_assoc,smul_eq_zero] at hx
    exact hx.resolve_left hr

omit [StarOrderedRing M] in
include htr in
lemma trace_mul_pow_swap (a b : M) (n : ℕ) : τ ((a*b)^n)=τ ((b*a)^n) := by
  cases n with
  | zero => simp only [pow_zero]
  | succ n => rw [pow_succ,← mul_assoc,htr,mul_pow_mul,← mul_assoc,← pow_succ']

omit [StarOrderedRing M] in
lemma trace_one_sub_pow {a b : M} (h : ∀ n : ℕ, τ (a^n)=τ (b^n)) (n : ℕ) :
    τ ((1-a)^n)=τ ((1-b)^n) := by
  have hn (k : ℕ) : τ ((-a)^k)=τ ((-b)^k) := by
    rw [show -a=(-1:ℂ) • a by simp,show -b=(-1:ℂ) • b by simp,
      smul_pow,smul_pow,map_smul,map_smul,h]
  rw [sub_eq_add_neg,sub_eq_add_neg,(Commute.one_left (-a)).add_pow,
    (Commute.one_left (-b)).add_pow,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [one_pow,one_mul,← nsmul_eq_mul',map_nsmul,hn]

include e hL hτ htr hfaith in
lemma support_trace_eq_of_moments (a b p q : M) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) (hp : IsSupportProjection a p)
    (hq : IsSupportProjection b q) (ht : ∀ n : ℕ, τ (a^n)=τ (b^n)) : τ p=τ q := by
  obtain ⟨p',hp',hpt⟩ := exists_support_contraction e τ hL hτ htr hfaith a ha ha1
  obtain ⟨q',hq',hqt⟩ := exists_support_contraction e τ hL hτ htr hfaith b hb hb1
  have hp'p : p'=p := hp'.unique hp
  have hq'q : q'=q := hq'.unique hq
  subst p'; subst q'
  have hpa : ∀ n : ℕ, ‖1-(1-a)^n‖ ≤ 2 := fun n =>
    (norm_sub_le _ _).trans (by
      have h := norm_pow_pos_contraction (1-a) (sub_nonneg.mpr ha1) (sub_le_self _ ha) n
      have h1 : ‖(1:M)‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ zero_le_one).mpr le_rfl
      linarith)
  have hqa : ∀ n : ℕ, ‖1-(1-b)^n‖ ≤ 2 := fun n =>
    (norm_sub_le _ _).trans (by
      have h := norm_pow_pos_contraction (1-b) (sub_nonneg.mpr hb1) (sub_le_self _ hb) n
      have h1 : ‖(1:M)‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ zero_le_one).mpr le_rfl
      linarith)
  apply tendsto_nhds_unique (trace_predual_tendsto e τ hτ
    (hpt.predual e τ hL hτ hfaith 2 hpa))
  convert trace_predual_tendsto e τ hτ (hqt.predual e τ hL hτ hfaith 2 hqa) using 1
  ext n
  simp only [map_sub,trace_one_sub_pow τ ht]

include e hL hτ htr hfaith in

theorem support_trace_star_mul_self (x p q : M)
    (hp : IsSupportProjection (star x*x) p) (hq : IsSupportProjection (x*star x) q) :
    τ p=τ q := by
  let r : ℝ := (‖x‖^2+1)⁻¹
  have hd : 0 < ‖x‖^2+1 := by positivity
  have hr : 0 < r := inv_pos.mpr hd
  have hpos : 0 ≤ r • (star x*x) := smul_nonneg hr.le (star_mul_self_nonneg x)
  have hpos' : 0 ≤ r • (x*star x) := smul_nonneg hr.le (mul_star_self_nonneg x)
  have hnorm : ‖r • (star x*x)‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,CStarRing.norm_star_mul_self]
    exact (inv_mul_le_one₀ hd).mpr (by linarith)
  have hnorm' : ‖r • (x*star x)‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,CStarRing.norm_self_mul_star]
    exact (inv_mul_le_one₀ hd).mpr (by linarith)
  apply support_trace_eq_of_moments e τ hL hτ htr hfaith _ _ p q hpos hpos'
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos).mp hnorm)
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos').mp hnorm')
    (hp.smul r hr.ne') (hq.smul r hr.ne')
  intro n
  simp only [smul_pow,← Complex.coe_smul,map_smul,trace_mul_pow_swap τ htr (star x) x]

omit [PartialOrder M] [StarOrderedRing M] in
lemma IsSupportProjection.star_mul_self_right {x p : M}
    (hp : IsSupportProjection (star x*x) p) : x*p=x := by
  have h : star (x*(1-p))*(x*(1-p))=0 := by
    rw [star_mul,star_sub,star_one,hp.proj.isSelfAdjoint.star_eq]
    calc
      (1-p)*star x*(x*(1-p)) = (1-p)*((star x*x)*(1-p)) := by simp only [mul_assoc]
      _ = 0 := by rw [mul_sub,mul_one,hp.right,sub_self,mul_zero]
  have hz := (CStarRing.star_mul_self_eq_zero_iff _).mp h
  simpa only [mul_sub,mul_one,sub_eq_zero,eq_comm] using hz

omit [PartialOrder M] [StarOrderedRing M] in
lemma IsSupportProjection.mul_star_self_left {x p : M}
    (hp : IsSupportProjection (x*star x) p) : p*x=x := by
  have hh : star x*p=star x := IsSupportProjection.star_mul_self_right
    (x := star x) (by simpa only [star_star] using hp)
  simpa only [star_mul,star_star,hp.proj.isSelfAdjoint.star_eq] using congrArg Star.star hh

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

lemma IsSupportProjection.left_le {x r p : M}
    (hr : IsSupportProjection (x*star x) r) (hp : IsStarProjection p) (hpx : p*x=x) :
    r ≤ p := by
  apply hr.le_of_support hp
  have hx : star x*p=star x := by
    simpa only [star_mul,star_star,hp.isSelfAdjoint.star_eq] using congrArg Star.star hpx
  rw [mul_assoc,hx]

lemma IsSupportProjection.right_le {x r p : M}
    (hr : IsSupportProjection (star x*x) r) (hp : IsStarProjection p) (hxp : x*p=x) :
    r ≤ p := by
  apply hr.le_of_support hp
  rw [mul_assoc,hxp]

include e hL hτ htr hfaith in

theorem exists_projection_join (p q : M) (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ s : M, IsStarProjection s ∧ p ≤ s ∧ q ≤ s ∧
      (∀ z : M, IsStarProjection z → p ≤ z → q ≤ z → s ≤ z) ∧
      (τ s).re ≤ (τ p).re+(τ q).re := by
  let x := (1-p)*q
  obtain ⟨r,hr⟩ := exists_support_projection e τ hL hτ htr hfaith (x*star x)
    (mul_star_self_nonneg x)
  obtain ⟨t,ht⟩ := exists_support_projection e τ hL hτ htr hfaith (star x*x)
    (star_mul_self_nonneg x)
  have hpx : (1-p)*x=x := by dsimp [x]; rw [← mul_assoc,hp.one_sub.isIdempotentElem.eq]
  have hxq : x*q=x := by dsimp [x]; rw [mul_assoc,hq.isIdempotentElem.eq]
  have hrp : r ≤ 1-p := hr.left_le hp.one_sub hpx
  have htq : t ≤ q := ht.right_le hq hxq
  have hpr : p*r=0 := by
    have hh := (hr.proj.le_iff_mul_eq_right hp.one_sub).mp hrp
    simpa only [sub_mul,one_mul,sub_eq_self] using hh
  have hrp0 : r*p=0 := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq,hr.proj.isSelfAdjoint.star_eq,star_zero]
      using congrArg Star.star hpr
  have hs : IsStarProjection (p+r) := hp.add hr.proj hpr
  have hp_le : p ≤ p+r := (hp.le_iff_mul_eq_left hs).mpr (by
    rw [mul_add,hp.isIdempotentElem.eq,hpr,add_zero])
  have hrq : r*q=(1-p)*q := by
    have hh := hr.mul_star_self_left
    dsimp [x] at hh
    rw [← mul_assoc,mul_sub,mul_one,hrp0,sub_zero] at hh
    exact hh
  have hq_le : q ≤ p+r := (hq.le_iff_mul_eq_right hs).mpr (by
    rw [add_mul,hrq,sub_mul,one_mul,add_sub_cancel])
  refine ⟨p+r,hs,hp_le,hq_le,?_,?_⟩
  · intro z hz hpz hqz
    have hzp : z*p=p := (hp.le_iff_mul_eq_right hz).mp hpz
    have hzq : z*q=q := (hq.le_iff_mul_eq_right hz).mp hqz
    have hzx : z*x=x := by
      dsimp [x]
      rw [← mul_assoc,mul_sub,mul_one,sub_mul,hzq,hzp,sub_mul,one_mul]
    have hrz : r ≤ z := hr.left_le hz hzx
    apply (hs.le_iff_mul_eq_right hz).mpr
    rw [mul_add,hzp,(hr.proj.le_iff_mul_eq_right hz).mp hrz]
  · have hrt : τ r=τ t := (support_trace_star_mul_self e τ hL hτ htr hfaith x t r ht hr).symm
    rw [map_add,Complex.add_re,hrt]
    exact add_le_add le_rfl (Complex.re_le_re (τ.monotone htq))

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

include e hL hτ htr hfaith in
lemma exists_projection_finjoin (a : ℕ → M) (ha : ∀ n, IsStarProjection (a n)) (n : ℕ) :
    ∃ p : M, IsStarProjection p ∧ (∀ i < n, a i ≤ p) ∧
      (∀ q : M, IsStarProjection q → (∀ i < n, a i ≤ q) → p ≤ q) ∧
      (τ p).re ≤ ∑ i ∈ Finset.range n, (τ (a i)).re := by
  induction n with
  | zero =>
    refine ⟨0,IsStarProjection.zero M,by simp,?_,by simp⟩
    intro q hq _h
    exact hq.nonneg
  | succ n ih =>
    obtain ⟨p,hp,had,hl,ht⟩ := ih
    obtain ⟨q,hq,hpq,hanq,hql,hqt⟩ := exists_projection_join e τ hL hτ htr hfaith p (a n) hp (ha n)
    refine ⟨q,hq,?_,?_,?_⟩
    · intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h|rfl
      · exact (had i h).trans hpq
      · exact hanq
    · intro z hz haz
      apply hql z hz (hl z hz (fun i hi => haz i (Nat.lt_succ_of_lt hi)))
      exact haz n (Nat.lt_succ_self n)
    · rw [Finset.sum_range_succ]
      exact hqt.trans (add_le_add ht le_rfl)

include e hL hτ htr hfaith in

theorem exists_projection_countable_join (a : ℕ → M) (ha : ∀ n, IsStarProjection (a n))
    (C : ℝ) (hC : ∀ n : ℕ, (∑ i ∈ Finset.range n, (τ (a i)).re) ≤ C) :
    ∃ p : M, IsStarProjection p ∧ (∀ n, a n ≤ p) ∧
      (∀ q : M, IsStarProjection q → (∀ n, a n ≤ q) → p ≤ q) ∧ (τ p).re ≤ C := by
  classical
  choose b hb had hl ht using exists_projection_finjoin e τ hL hτ htr hfaith a ha
  have hbm : Monotone b := by
    intro n m hnm
    exact hl n (b m) (hb m) (fun i hi => had m i (hi.trans_le hnm))
  obtain ⟨p,hp,hpt,hbp,hpl⟩ := exists_monotone_projection_limit e τ hL hτ htr hfaith b hb hbm
  refine ⟨p,hp,?_,?_,?_⟩
  · intro n
    exact (had (n+1) n (Nat.lt_succ_self n)).trans (hbp (n+1))
  · intro q hq haq
    exact hpl q hq (fun n => hl n q hq (fun i _hi => haq i))
  · exact le_of_tendsto
      ((Complex.continuous_re.tendsto (τ p)).comp
        (trace_predual_tendsto e τ hτ (hpt.predual e τ hL hτ hfaith 1
          (fun n => (hb n).norm_le _))))
      (Filter.Eventually.of_forall (fun n => (ht n).trans (hC n)))

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

include e hL hτ htr hfaith in

theorem exists_spectral_cut (x : M) (α : ℝ) (hα : 0 < α) :
    ∃ p : M, IsStarProjection p ∧ ‖x-x*p‖ ≤ α ∧
      (τ p).re ≤ ‖τ.toPreGNS x‖^2 / α^2 := by
  let a := star x*x
  let b := a-(α^2) • (1:M)
  let c := b⁺
  let d := b⁻
  have hsa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg (star_mul_self_nonneg x)
  have hsb : IsSelfAdjoint b := hsa.sub (IsSelfAdjoint.of_nonneg
    (smul_nonneg (sq_nonneg α) zero_le_one))
  have hc : 0 ≤ c := CFC.posPart_nonneg b
  have hd : 0 ≤ d := CFC.negPart_nonneg b
  have hcd : c*d=0 := CFC.posPart_mul_negPart b
  have had : a=c-d+(α^2) • 1 := by
    have hh := CFC.posPart_sub_negPart b hsb
    dsimp [c,d,b] at *
    rw [hh,sub_add_cancel]
  obtain ⟨p,hp⟩ := exists_support_projection e τ hL hτ htr hfaith c hc
  have hpd : p*d=0 := hp.annihilate d hcd
  have hdp : d*p=0 := by
    simpa only [star_mul,hp.proj.isSelfAdjoint.star_eq,(IsSelfAdjoint.of_nonneg hd).star_eq,
      star_zero] using congrArg Star.star hpd
  have hap : a*p=c+(α^2) • p := by
    rw [had,add_mul,sub_mul,hp.right,hdp,smul_mul_assoc,one_mul,sub_zero]
  have hcomp : a*(1-p)=(α^2) • (1-p)-d := by
    rw [mul_sub,mul_one,hap,had,smul_sub]
    abel
  let z := x*(1-p)
  have hzz : star z*z=(α^2) • (1-p)-d := by
    dsimp [z]
    rw [star_mul,star_sub,star_one,hp.proj.isSelfAdjoint.star_eq]
    calc
      (1-p)*star x*(x*(1-p)) = (1-p)*(a*(1-p)) := by dsimp [a]; simp only [mul_assoc]
      _ = (α^2) • (1-p)-d := by
        rw [hcomp,mul_sub,mul_smul_comm,hp.proj.one_sub.isIdempotentElem.eq,
          sub_mul,one_mul,hpd,sub_zero]
  have hzzle : star z*z ≤ (α^2) • (1:M) := by
    rw [hzz]
    exact (sub_le_self _ hd).trans (smul_le_smul_of_nonneg_left hp.proj.one_sub.le_one (sq_nonneg α))
  have hz : ‖z‖ ≤ α := by
    have hh : ‖star z*z‖ ≤ α^2 := (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg α)
      (star_mul_self_nonneg z)).mpr (by simpa only [Algebra.algebraMap_eq_smul_one] using hzzle)
    rw [CStarRing.norm_star_mul_self] at hh
    nlinarith [norm_nonneg z]
  have htd : (α^2) • p ≤ a := by
    have hpos : 0 ≤ a-a*p := by
      have heq : a-a*p=star z*z := by rw [hzz,← hcomp,mul_sub,mul_one]
      rw [heq]
      exact star_mul_self_nonneg z
    have hh : (α^2) • p ≤ a*p := by rw [hap]; exact le_add_of_nonneg_left hc
    exact hh.trans (sub_nonneg.mp hpos)
  have htrace : (τ ((α^2) • p)).re ≤ (τ a).re := Complex.re_le_re (τ.monotone htd)
  have hsmall : (τ p).re ≤ ‖τ.toPreGNS x‖^2 / α^2 := by
    rw [← Complex.coe_smul,map_smul,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] at htrace
    rw [le_div_iff₀ (sq_pos_of_pos hα),mul_comm]
    simpa only [a,trace_star_mul_self_re τ] using htrace
  refine ⟨p,hp.proj,?_,hsmall⟩
  simpa only [z,mul_sub,mul_one] using hz

include e hL hτ htr hfaith in

theorem exists_small_two_sided_support (x : M) (α : ℝ) (hα : 0 < α) :
    ∃ y p : M, IsStarProjection p ∧ p*y=y ∧ y*p=y ∧ ‖y‖ ≤ ‖x‖ ∧
      ‖x-y‖ ≤ α ∧ (τ p).re ≤ 2*(‖τ.toPreGNS x‖^2 / α^2) := by
  obtain ⟨r,hr,hdiff,hsmall⟩ := exists_spectral_cut e τ hL hτ htr hfaith x α hα
  let y := x*r
  obtain ⟨q,hq⟩ := exists_support_projection e τ hL hτ htr hfaith (y*star y)
    (mul_star_self_nonneg y)
  obtain ⟨t,ht⟩ := exists_support_projection e τ hL hτ htr hfaith (star y*y)
    (star_mul_self_nonneg y)
  have hyr : y*r=y := by dsimp [y]; rw [mul_assoc,hr.isIdempotentElem.eq]
  have htrle : t ≤ r := ht.right_le hr hyr
  have hqtrace : (τ q).re ≤ (τ r).re := by
    rw [← support_trace_star_mul_self e τ hL hτ htr hfaith y t q ht hq]
    exact Complex.re_le_re (τ.monotone htrle)
  obtain ⟨p,hp,hrp,hqp,_hmin,hptrace⟩ :=
    exists_projection_join e τ hL hτ htr hfaith r q hr hq.proj
  refine ⟨y,p,hp,?_,?_,?_,hdiff,?_⟩
  · calc
      p*y = p*(q*y) := by rw [hq.mul_star_self_left]
      _ = y := by rw [← mul_assoc,(hq.proj.le_iff_mul_eq_right hp).mp hqp,hq.mul_star_self_left]
  · calc
      y*p = (y*r)*p := by rw [hyr]
      _ = y := by rw [mul_assoc,(hr.le_iff_mul_eq_left hp).mp hrp,hyr]
  · exact (norm_mul_le x r).trans (by nlinarith [norm_nonneg x,hr.norm_le r])
  · linarith
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
namespace HochschildRare

def q (n : ℕ) : ℝ := (1/2:ℝ)^(2^n)
def p (n : ℕ) : ℝ := q n^2
def time (n : ℕ) : ℕ := 2^(3*2^n)
def slots (n : ℕ) : ℕ := (n+1)*time n
def labels (n : ℕ) : ℕ := slots n^4

lemma q_pos (n : ℕ) : 0 < q n := by unfold q; positivity
lemma q_le (n : ℕ) : q n ≤ 1/2 := by
  unfold q
  exact pow_le_of_le_one (by norm_num) (by norm_num) (by positivity)
lemma p_pos (n : ℕ) : 0 < p n := sq_pos_of_pos (q_pos n)
lemma p_le (n : ℕ) : p n ≤ 1/4 := by
  have := q_le n
  have := q_pos n
  unfold p
  nlinarith
lemma q_succ (n : ℕ) : q (n+1) = p n := by
  dsimp [q, p]
  rw [Nat.pow_succ, pow_mul]
lemma p_succ (n : ℕ) : p (n+1) = p n^2 := by rw [p,q_succ]
lemma p_succ_le (n : ℕ) : p (n+1) ≤ 1/16 := by
  rw [p_succ]
  have := p_pos n
  have := p_le n
  nlinarith
lemma p_antitone : Antitone p := by
  apply antitone_nat_of_succ_le
  intro n
  rw [p_succ]
  exact pow_le_of_le_one (p_pos n).le (by linarith [p_le n]) (by decide)

lemma tail_bound (n k : ℕ) : p (n+1+k) ≤ p n^2*(1/16:ℝ)^k := by
  induction k with
  | zero => simp only [add_zero,pow_zero,mul_one,p_succ,le_refl]
  | succ k ih =>
    rw [show n+1+(k+1) = (n+1+k)+1 by omega,p_succ,pow_two,pow_succ]
    have hp := (p_antitone (show n+1 ≤ n+1+k by omega)).trans (p_succ_le n)
    calc
      p (n+1+k)*p (n+1+k) ≤ (p n^2*(1/16:ℝ)^k)*(1/16) :=
        mul_le_mul ih hp (p_pos _).le (by positivity)
      _ = _ := by ring

lemma geometric_bound (n : ℕ) : p n ≤ (1/4:ℝ)^(n+1) := by
  induction n with
  | zero => norm_num [p,q]
  | succ n ih =>
    rw [p_succ,pow_two,pow_succ]
    exact mul_le_mul ih (p_le n) (p_pos _).le (by positivity)

lemma summable_p : Summable p :=
  Summable.of_nonneg_of_le (fun n => (p_pos n).le) geometric_bound
    ((summable_geometric_of_norm_lt_one (by norm_num : ‖(1/4:ℝ)‖ < 1)).comp_injective
      Nat.succ_injective)

lemma sum_p_le : ∑' n, p n ≤ 1/3 := by
  have hg : (∑' n : ℕ, (1/4:ℝ)^(n+1)) = 1/3 := by
    simp_rw [pow_succ]
    rw [tsum_mul_right,tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/4:ℝ)‖ < 1)]
    norm_num
  rw [← hg]
  exact summable_p.tsum_le_tsum geometric_bound
    ((summable_geometric_of_norm_lt_one (by norm_num : ‖(1/4:ℝ)‖ < 1)).comp_injective
      Nat.succ_injective)

lemma sum_tail_le (n : ℕ) : ∑' k, p (n+1+k) ≤ (16/15:ℝ)*p n^2 := by
  have hs : Summable (fun k => p n^2*(1/16:ℝ)^k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/16:ℝ)‖ < 1)).mul_left _
  have hsp : Summable (fun k => p (n+1+k)) := Summable.of_nonneg_of_le
    (fun k => (p_pos _).le) (tail_bound n) hs
  have hsum := hsp.tsum_le_tsum (tail_bound n) hs
  rw [tsum_mul_left,tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/16:ℝ)‖ < 1)] at hsum
  norm_num at hsum
  nlinarith [hsum]

lemma time_pos (n : ℕ) : 0 < time n := by unfold time; positivity
lemma slots_pos (n : ℕ) : 0 < slots n := Nat.mul_pos (Nat.succ_pos _) (time_pos n)
lemma labels_pos (n : ℕ) : 0 < labels n := pow_pos (slots_pos n) _

lemma successor_le_two_pow (n : ℕ) : n+1 ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.pow_succ]
    have : 0 < 2^n := by positivity
    omega

lemma q_geometric_bound (n : ℕ) : q n ≤ (1/2:ℝ)^(n+1) :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) (successor_le_two_pow n)

lemma tendsto_stage_q : Tendsto (fun n : ℕ => (n+1:ℝ)*q n) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => mul_nonneg (by positivity) (q_pos n).le)
    (fun n => mul_le_mul_of_nonneg_left (q_geometric_bound n) (by positivity))
  have ht := (tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1/2:ℝ) < 1)).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using ht

lemma time_mul_p_mul_q (n : ℕ) : (time n:ℝ)*p n*q n = 1 := by
  unfold time p q
  push_cast
  rw [show 3*2^n = 2^n*3 by omega,pow_mul,div_pow,one_pow]
  field_simp

lemma slots_mul_p_sq (n : ℕ) : (slots n:ℝ)*p n^2 = (n+1:ℝ)*q n := by
  have he := time_mul_p_mul_q n
  have he' : (time n:ℝ)*p n^2 = q n := by
    rw [p] at he ⊢
    nlinarith [congrArg (fun x : ℝ => x*q n) he]
  simp only [slots,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  rw [mul_assoc,he']

lemma geometric_miss_bound (x : ℝ) (_hx : 0 ≤ x) (hx1 : x ≤ 1) (N : ℕ) :
    (1+(N:ℝ)*x)*(1-x)^N ≤ 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hh : (1+((N:ℝ)+1)*x)*(1-x) ≤ 1+(N:ℝ)*x := by
      nlinarith [mul_nonneg (show 0 ≤ (N:ℝ)+1 by positivity) (sq_nonneg x)]
    calc
      (1+((N+1:ℕ):ℝ)*x)*(1-x)^(N+1) =
          ((1+((N:ℝ)+1)*x)*(1-x))*(1-x)^N := by push_cast; ring
      _ ≤ (1+(N:ℝ)*x)*(1-x)^N :=
        mul_le_mul_of_nonneg_right hh (pow_nonneg (by linarith) _)
      _ ≤ 1 := ih

lemma miss_le_q (n : ℕ) : (1-p n)^time n ≤ q n := by
  have hb := geometric_miss_bound (p n) (p_pos n).le (by linarith [p_le n]) (time n)
  have ht := time_mul_p_mul_q n
  have hp : 0 ≤ (1-p n)^time n := pow_nonneg (by linarith [p_le n]) _
  have htpos : 0 < (time n:ℝ)*p n := mul_pos (by exact_mod_cast time_pos n) (p_pos n)
  apply (mul_le_mul_iff_right₀ htpos).mp
  nlinarith

lemma slots_ge_stage (n : ℕ) : n+1 ≤ slots n := by
  exact le_mul_of_one_le_right (by omega) (time_pos n)

lemma slots_tendsto : Tendsto slots atTop atTop := by
  exact tendsto_atTop_mono slots_ge_stage (tendsto_add_atTop_nat 1)

lemma slots_real_tendsto : Tendsto (fun n => (slots n:ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp slots_tendsto

lemma bad_bound_tendsto : Tendsto (fun n =>
    (16/15:ℝ)*(n+1)*q n + (slots n:ℝ)⁻¹ + (1/2:ℝ)*(slots n:ℝ)⁻¹^2 +
    (n+1:ℝ)*(1-p n)^time n) atTop (𝓝 0) := by
  have hmiss : Tendsto (fun n : ℕ => (n+1:ℝ)*(1-p n)^time n) atTop (𝓝 0) :=
    squeeze_zero (fun n => mul_nonneg (by positivity)
      (pow_nonneg (by linarith [p_le n]) _))
      (fun n => mul_le_mul_of_nonneg_left (miss_le_q n) (by positivity)) tendsto_stage_q
  have hinv := tendsto_inv_atTop_zero.comp slots_real_tendsto
  convert (((tendsto_stage_q.const_mul (16/15)).add hinv).add
    ((hinv.pow 2).const_mul (1/2))).add hmiss using 1 <;> simp [mul_assoc]
end HochschildRare
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
open MeasureTheory ProbabilityTheory Filter Topology
namespace HochschildRare
variable {X : Type*} [MeasurableSpace X]
variable (ν : Measure X) [IsProbabilityMeasure ν]

lemma finite_coordinates_mass {I : Type*} [Fintype I] (s : Finset I) (A : Set X) :
    (Measure.pi (fun _ : I => ν)).real {w | ∀ i ∈ s, w i ∈ A} = ν.real A ^ s.card := by
  change ((Measure.pi (fun _ : I => ν)) ((s : Set I).pi (fun _ => A))).toReal = _
  rw [Measure.pi_pi_finset]
  simp only [Finset.prod_const, ENNReal.toReal_pow, Measure.real_def]

lemma some_coordinate_mass_le {I : Type*} [Fintype I] (A : Set X)
    (hA : MeasurableSet A) :
    (Measure.pi (fun _ : I => ν)).real {w | ∃ i, w i ∈ A} ≤ Fintype.card I * ν.real A := by
  have he : {w : I → X | ∃ i, w i ∈ A} = ⋃ i : I, Function.eval i ⁻¹' A := by
    ext w; simp
  rw [he]
  calc
    _ ≤ ∑ i : I, (Measure.pi (fun _ : I => ν)).real (Function.eval i ⁻¹' A) :=
      measureReal_iUnion_fintype_le _
    _ = _ := by
      simp only [(measurePreserving_eval (fun _ : I => ν) _).measureReal_preimage hA.nullMeasurableSet,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma label_collision_mass_le {I J : Type*} [Fintype I] [Fintype J]
    (A : J → Set X) :
    (Measure.pi (fun _ : I => ν)).real
      {w | ∃ i j : I, i ≠ j ∧ ∃ a : J, w i ∈ A a ∧ w j ∈ A a} ≤
      ((Fintype.card I).choose 2 : ℝ) * ∑ a : J, ν.real (A a)^2 := by
  classical
  let Z := (Finset.univ : Finset I).powersetCard 2
  let E (s : Finset I) (a : J) := {w : I → X | ∀ i ∈ s, w i ∈ A a}
  have hsub : {w : I → X | ∃ i j : I, i ≠ j ∧ ∃ a : J, w i ∈ A a ∧ w j ∈ A a} ⊆
      ⋃ s ∈ Z, ⋃ a : J, E s a := by
    rintro w ⟨i,j,hij,a,hi,hj⟩
    refine Set.mem_iUnion.mpr ⟨{i,j},Set.mem_iUnion.mpr ⟨?_,Set.mem_iUnion.mpr ⟨a,?_⟩⟩⟩
    · simp [Z,Finset.mem_powersetCard,hij]
    · intro k hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> assumption
  calc
    _ ≤ (Measure.pi (fun _ : I => ν)).real (⋃ s ∈ Z, ⋃ a : J, E s a) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ s ∈ Z, (Measure.pi (fun _ : I => ν)).real (⋃ a : J, E s a) :=
      measureReal_biUnion_finset_le Z _
    _ ≤ ∑ s ∈ Z, ∑ a : J, (Measure.pi (fun _ : I => ν)).real (E s a) := by
      gcongr with s hs
      exact measureReal_iUnion_fintype_le _
    _ = _ := by
      have hc (s : Finset I) (hs : s ∈ Z) : s.card = 2 := (Finset.mem_powersetCard.mp hs).2
      simp_rw [E,finite_coordinates_mass]
      rw [Finset.sum_congr rfl (fun s hs => by rw [hc s hs])]
      simp [Z,Finset.card_powersetCard,nsmul_eq_mul]

lemma uniform_label_collision_mass_le {I J : Type*} [Fintype I] [Fintype J]
    (A : J → Set X) (p : ℝ) (hA : ∀ j, ν.real (A j) = p / Fintype.card J)
    (hJ : 0 < Fintype.card J) :
    (Measure.pi (fun _ : I => ν)).real
      {w | ∃ i j : I, i ≠ j ∧ ∃ a : J, w i ∈ A a ∧ w j ∈ A a} ≤
      ((Fintype.card I).choose 2 : ℝ) * p^2 / Fintype.card J := by
  have h : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hJ)
  convert label_collision_mass_le ν A using 1
  simp only [hA,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp

lemma path_miss_mass {r n : ℕ} (i : Fin r) (A : Set X) :
    (Measure.pi (fun _ : Fin r × Fin n => ν)).real {w | ∀ j, w (i,j) ∉ A} =
      ν.real Aᶜ ^ n := by
  classical
  let s : Finset (Fin r × Fin n) := Finset.univ.image (fun j : Fin n => (i,j))
  have hs : s.card = n := by
    rw [Finset.card_image_of_injective _ (by intro a b h; exact (Prod.mk.inj h).2)]
    exact Finset.card_fin n
  have he : {w : Fin r × Fin n → X | ∀ j, w (i,j) ∉ A} = {w | ∀ a ∈ s, w a ∈ Aᶜ} := by
    ext w
    simp [s]
  rw [he,finite_coordinates_mass,hs]

lemma some_path_miss_mass_le {r n : ℕ} (A : Set X) (hA : MeasurableSet A) :
    (Measure.pi (fun _ : Fin r × Fin n => ν)).real {w | ∃ i, ∀ j, w (i,j) ∉ A} ≤
      r * (1-ν.real A)^n := by
  have he : {w : Fin r × Fin n → X | ∃ i, ∀ j, w (i,j) ∉ A} =
      ⋃ i : Fin r, {w | ∀ j, w (i,j) ∉ A} := by ext w; simp
  rw [he]
  calc
    _ ≤ ∑ i : Fin r, (Measure.pi (fun _ : Fin r × Fin n => ν)).real {w | ∀ j, w (i,j) ∉ A} :=
      measureReal_iUnion_fintype_le _
    _ = _ := by simp only [path_miss_mass, measureReal_compl hA, probReal_univ,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

def badPaths {r n : ℕ} {J : Type*} (T B A : Set X) (L : J → Set X) : Set (Fin r × Fin n → X) :=
  {w | (∃ i, w i ∈ T) ∨ (∃ i, w i ∈ B) ∨
    (∃ i j, i ≠ j ∧ ∃ a, w i ∈ L a ∧ w j ∈ L a) ∨
      ∃ i, ∀ j, w (i,j) ∉ A}

theorem badPaths_mass_le {r n : ℕ} {J : Type*} [Fintype J]
    (T B A : Set X) (L : J → Set X) (hT : MeasurableSet T) (hB : MeasurableSet B)
    (hA : MeasurableSet A) (p : ℝ) (hL : ∀ j, ν.real (L j) = p / Fintype.card J)
    (hJ : 0 < Fintype.card J) :
    (Measure.pi (fun _ : Fin r × Fin n => ν)).real (badPaths T B A L) ≤
      (r*n:ℕ) * ν.real T + (r*n:ℕ) * ν.real B +
      (((r*n).choose 2:ℕ):ℝ) * p^2 / Fintype.card J + r*(1-ν.real A)^n := by
  let E₁ : Set (Fin r × Fin n → X) := {w | ∃ i, w i ∈ T}
  let E₂ : Set (Fin r × Fin n → X) := {w | ∃ i, w i ∈ B}
  let E₃ : Set (Fin r × Fin n → X) := {w | ∃ i j, i ≠ j ∧ ∃ a, w i ∈ L a ∧ w j ∈ L a}
  let E₄ : Set (Fin r × Fin n → X) := {w | ∃ i, ∀ j, w (i,j) ∉ A}
  have h₁ := some_coordinate_mass_le (I := Fin r × Fin n) ν T hT
  have h₂ := some_coordinate_mass_le (I := Fin r × Fin n) ν B hB
  have h₃ := uniform_label_collision_mass_le (I := Fin r × Fin n) ν L p hL hJ
  have h₄ := some_path_miss_mass_le (r := r) (n := n) ν A hA
  simp only [Fintype.card_prod,Fintype.card_fin] at h₁ h₂ h₃
  have he : badPaths (r := r) (n := n) T B A L = E₁ ∪ (E₂ ∪ (E₃ ∪ E₄)) := rfl
  rw [he]
  have hb₁ := measureReal_union_le (μ := Measure.pi (fun _ : Fin r × Fin n => ν)) E₁ (E₂ ∪ (E₃ ∪ E₄))
  have hb₂ := measureReal_union_le (μ := Measure.pi (fun _ : Fin r × Fin n => ν)) E₂ (E₃ ∪ E₄)
  have hb₃ := measureReal_union_le (μ := Measure.pi (fun _ : Fin r × Fin n => ν)) E₃ E₄
  dsimp [E₁,E₂,E₃,E₄] at hb₁ hb₂ hb₃
  linarith

end HochschildRare

open MeasureTheory Filter Topology
open scoped ENNReal Function
namespace HochschildRare

def baseMass : ℝ := 1 - ∑' n, p n

lemma baseMass_pos : 0 < baseMass := by unfold baseMass; linarith [sum_p_le]

def baseWeight (j : ℕ) : ℝ := (1/2:ℝ)^(j+1)
lemma baseWeight_pos (j : ℕ) : 0 < baseWeight j := by unfold baseWeight; positivity
lemma summable_baseWeight : Summable baseWeight := by
  exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).comp_injective
    Nat.succ_injective
lemma sum_baseWeight : ∑' j, baseWeight j = 1 := by
  simp only [baseWeight,pow_succ]
  rw [tsum_mul_right,tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)]
  norm_num

abbrev Label := ℕ ⊕ ((n : ℕ) × Fin (labels n))
instance : MeasurableSpace Label := ⊤
instance : MeasurableSingletonClass Label := ⟨fun _ => trivial⟩

def labelWeight : Label → ℝ≥0∞
  | .inl j => ENNReal.ofReal (baseMass * baseWeight j)
  | .inr a => ENNReal.ofReal (p a.1 / labels a.1)

lemma sum_uniform_weight (n : ℕ) :
    ∑' _j : Fin (labels n), ENNReal.ofReal (p n / labels n) = ENNReal.ofReal (p n) := by
  have hd : (labels n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (labels_pos n))
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => div_nonneg (p_pos n).le (Nat.cast_nonneg _))]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  congr 1
  field_simp

lemma tsum_labelWeight : ∑' a, labelWeight a = 1 := by
  change (∑' a : ℕ ⊕ ((n : ℕ) × Fin (labels n)), labelWeight a) = _
  rw [ENNReal.summable.tsum_sum ENNReal.summable]
  simp only [labelWeight]
  rw [ENNReal.tsum_sigma']
  simp only [sum_uniform_weight]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg baseMass_pos.le (baseWeight_pos j).le)
      (summable_baseWeight.mul_left baseMass), tsum_mul_left, sum_baseWeight, mul_one,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => (p_pos n).le) summable_p,
    ← ENNReal.ofReal_add baseMass_pos.le (tsum_nonneg (fun n => (p_pos n).le))]
  simp [baseMass]

def labelPMF : PMF Label := ⟨labelWeight, by
  simpa only [tsum_labelWeight] using (ENNReal.summable (f := labelWeight)).hasSum⟩
def labelLaw : Measure Label := labelPMF.toMeasure
instance : IsProbabilityMeasure labelLaw := by unfold labelLaw; infer_instance

lemma labelLaw_singleton (a : Label) : labelLaw {a} = labelWeight a :=
  labelPMF.toMeasure_apply_singleton a (measurableSet_singleton a)

lemma stage_label_mass (n : ℕ) (j : Fin (labels n)) :
    labelLaw.real {Sum.inr ⟨n,j⟩} = p n / labels n := by
  rw [Measure.real_def,labelLaw_singleton]
  exact ENNReal.toReal_ofReal (div_nonneg (p_pos n).le (Nat.cast_nonneg _))

lemma stage_mass (n : ℕ) :
    labelLaw.real {a | ∃ j : Fin (labels n), a = Sum.inr ⟨n,j⟩} = p n := by
  classical
  have he : {a : Label | ∃ j : Fin (labels n), a = Sum.inr ⟨n,j⟩} =
      ⋃ j : Fin (labels n), {Sum.inr ⟨n,j⟩} := by ext a; simp [eq_comm]
  rw [he,measureReal_iUnion_fintype]
  · simp only [stage_label_mass,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hd : (labels n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (labels_pos n))
    field_simp
  · intro i j hij
    simpa only [Function.onFun,Set.disjoint_singleton,ne_eq,Sum.inr.injEq,Sigma.mk.inj_iff,
      true_and,heq_eq_eq] using hij
  · intro j
    exact measurableSet_singleton _

def stageSet (n : ℕ) : Set Label := {a | ∃ j : Fin (labels n), a = Sum.inr ⟨n,j⟩}
def tailSet (n : ℕ) : Set Label := {a | ∃ k, n < k ∧ a ∈ stageSet k}
def baseTail (N : ℕ) : Set Label := {a | ∃ j, N ≤ j ∧ a = Sum.inl j}

lemma stageSet_disjoint : Pairwise (Disjoint on stageSet) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  rintro a ⟨i,rfl⟩ ⟨j,hj⟩
  exact hnm (congrArg Sigma.fst (Sum.inr.inj hj))

lemma tail_mass (n : ℕ) : labelLaw.real (tailSet n) = ∑' k, p (n+1+k) := by
  have he : tailSet n = ⋃ k : ℕ, stageSet (n+1+k) := by
    ext a
    simp only [tailSet,Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · rintro ⟨j,hj,ha⟩
      exact ⟨j-(n+1),by simpa [Nat.add_sub_of_le (by omega : n+1 ≤ j)] using ha⟩
    · rintro ⟨k,hk⟩
      exact ⟨n+1+k,by omega,hk⟩
  rw [Measure.real_def,he,measure_iUnion]
  · rw [ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
    exact tsum_congr (fun k => stage_mass (n+1+k))
  · intro i j hij
    exact stageSet_disjoint (by omega)
  · intro k
    exact Set.Countable.measurableSet (Set.to_countable _)

lemma base_label_mass (j : ℕ) : labelLaw.real {Sum.inl j} = baseMass * baseWeight j := by
  rw [Measure.real_def,labelLaw_singleton]
  exact ENNReal.toReal_ofReal (mul_nonneg baseMass_pos.le (baseWeight_pos j).le)

lemma base_tail_mass (N : ℕ) : labelLaw.real (baseTail N) = baseMass * (1/2:ℝ)^N := by
  have he : baseTail N = ⋃ k : ℕ, {Sum.inl (N+k)} := by
    ext a
    simp only [baseTail,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_singleton_iff]
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact ⟨j-N,by simp [Nat.add_sub_of_le hj]⟩
    · rintro ⟨k,hk⟩
      exact ⟨N+k,by omega,hk⟩
  have hd : Pairwise (Disjoint on (fun k : ℕ => ({Sum.inl (N+k)} : Set Label))) := by
    intro i j hij
    simp only [Function.onFun,Set.disjoint_singleton,ne_eq,Sum.inl.injEq]
    omega
  rw [Measure.real_def,he,measure_iUnion hd (fun _ => measurableSet_singleton _),
    ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  simp only [← Measure.real_def,base_label_mass]
  simp_rw [baseWeight,show ∀ k : ℕ, N+k+1 = N+(k+1) by omega,pow_add]
  rw [tsum_mul_left,tsum_mul_left]
  simp_rw [← pow_add]
  change baseMass * ((1/2:ℝ)^N * ∑' k,baseWeight k) = _
  rw [sum_baseWeight,mul_one]

lemma exists_base_cut (n : ℕ) : ∃ N, labelLaw.real (baseTail N) < (slots n:ℝ)⁻¹^2 := by
  have hp : 0 < (slots n:ℝ)⁻¹^2 := by have := slots_pos n; positivity
  have ht : Tendsto (fun N => baseMass * (1/2:ℝ)^N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).const_mul baseMass
  obtain ⟨N,hN⟩ := (ht.eventually (gt_mem_nhds hp)).exists
  exact ⟨N,by simpa [base_tail_mass] using hN⟩

def signLaw : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
instance : IsProbabilityMeasure signLaw := by unfold signLaw; infer_instance

lemma signLaw_singleton (b : Bool) : signLaw {b} = (2:ℝ≥0∞)⁻¹ := by
  rw [signLaw,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp

lemma sign_flip_preserving : MeasurePreserving Bool.not signLaw signLaw := by
  refine ⟨measurable_of_countable _,Measure.ext_of_singleton (fun b => ?_)⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : Bool.not ⁻¹' {b} = {(!b)} := by ext c; cases b <;> cases c <;> simp
  rw [he,signLaw_singleton,signLaw_singleton]

abbrev Increment := Label × Bool
def incrementLaw : Measure Increment := labelLaw.prod signLaw
instance : IsProbabilityMeasure incrementLaw := by unfold incrementLaw; infer_instance

lemma increment_fst_preserving : MeasurePreserving Prod.fst incrementLaw labelLaw :=
  measurePreserving_fst
lemma increment_flip_preserving :
    MeasurePreserving (fun a : Increment => (a.1,!a.2)) incrementLaw incrementLaw :=
  (MeasurePreserving.id labelLaw).prod sign_flip_preserving

lemma increment_label_mass (A : Set Label) : incrementLaw.real (Prod.fst ⁻¹' A) = labelLaw.real A :=
  increment_fst_preserving.measureReal_preimage
    (Set.Countable.measurableSet (Set.to_countable _)).nullMeasurableSet

abbrev WalkGroup := FreeGroup Label
instance : MeasurableSpace WalkGroup := ⊤
instance : MeasurableSingletonClass WalkGroup := ⟨fun _ => trivial⟩

def incrementValue (a : Increment) : WalkGroup :=
  if a.2 then FreeGroup.of a.1 else (FreeGroup.of a.1)⁻¹

def walkLaw : Measure WalkGroup := incrementLaw.map incrementValue
instance : IsProbabilityMeasure walkLaw :=
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

lemma incrementValue_preserving : MeasurePreserving incrementValue incrementLaw walkLaw :=
  ⟨measurable_of_countable _,rfl⟩

lemma walkLaw_symmetric : walkLaw.map (fun g => g⁻¹) = walkLaw := by
  have he := incrementValue_preserving.comp increment_flip_preserving
  rw [walkLaw,Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  change incrementLaw.map ((fun g : WalkGroup => g⁻¹) ∘ incrementValue) = walkLaw
  have hh : (fun g : WalkGroup => g⁻¹) ∘ incrementValue =
      incrementValue ∘ (fun a : Increment => (a.1,!a.2)) := by
    funext a
    rcases a with ⟨a,b⟩
    cases b <;> simp [incrementValue]
  rw [hh]
  exact he.map_eq

lemma base_atom_pos (j : ℕ) : 0 < walkLaw {FreeGroup.of (Sum.inl j)} := by
  rw [walkLaw,Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hsub : ({(Sum.inl j,true)} : Set Increment) ⊆
      incrementValue ⁻¹' {FreeGroup.of (Sum.inl j)} := by
    rintro a rfl
    simp [incrementValue]
  apply lt_of_lt_of_le _ (measure_mono hsub)
  have he : ({(Sum.inl j,true)} : Set Increment) = {Sum.inl j} ×ˢ {true} := by ext a; simp
  rw [he,incrementLaw,Measure.prod_prod,labelLaw_singleton,signLaw_singleton]
  apply ENNReal.mul_pos
  · exact (ENNReal.ofReal_pos.mpr (mul_pos baseMass_pos (baseWeight_pos j))).ne'
  · norm_num

end HochschildRare

open MeasureTheory Filter Topology
namespace HochschildRare

def badBound (k : ℕ) : ℝ :=
  (16/15:ℝ)*(k+1)*q k + (slots k:ℝ)⁻¹ + (1/2:ℝ)*(slots k:ℝ)⁻¹^2 +
    (k+1:ℝ)*(1-p k)^time k

lemma badBound_tendsto : Tendsto badBound atTop (𝓝 0) := bad_bound_tendsto

lemma rare_four_terms_le (k r : ℕ) (hr : r ≤ k+1) (t b : ℝ)
    (ht : t ≤ (16/15:ℝ)*p k^2) (hb : b ≤ (slots k:ℝ)⁻¹^2) :
    (r*time k:ℕ)*t + (r*time k:ℕ)*b +
      (((r*time k).choose 2:ℕ):ℝ)*p k^2/labels k + r*(1-p k)^time k ≤ badBound k := by
  have hK : 0 < (slots k:ℝ) := by exact_mod_cast slots_pos k
  have hm : (r*time k:ℕ) ≤ slots k := Nat.mul_le_mul_right _ hr
  have hmR : ((r*time k:ℕ):ℝ) ≤ slots k := by exact_mod_cast hm
  have htail : ((r*time k:ℕ):ℝ)*t ≤ (16/15:ℝ)*(k+1)*q k := calc
    _ ≤ ((r*time k:ℕ):ℝ)*((16/15:ℝ)*p k^2) := mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ (slots k:ℝ)*((16/15:ℝ)*p k^2) := mul_le_mul_of_nonneg_right hmR (by positivity)
    _ = _ := by rw [← mul_assoc,mul_comm (slots k:ℝ),mul_assoc,slots_mul_p_sq]; ring
  have hbase : ((r*time k:ℕ):ℝ)*b ≤ (slots k:ℝ)⁻¹ := calc
    _ ≤ ((r*time k:ℕ):ℝ)*(slots k:ℝ)⁻¹^2 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (slots k:ℝ)*(slots k:ℝ)⁻¹^2 := mul_le_mul_of_nonneg_right hmR (by positivity)
    _ = _ := by field_simp
  have hc : (((r*time k).choose 2:ℕ):ℝ) ≤ (slots k:ℝ)^2/2 := by
    rw [Nat.cast_choose_two]
    have hz : 0 ≤ ((r*time k:ℕ):ℝ) := by positivity
    nlinarith [mul_self_le_mul_self hz hmR]
  have hp : p k^2 ≤ 1 := by nlinarith [p_pos k,p_le k]
  have hlabel : 0 < (labels k:ℝ) := by exact_mod_cast labels_pos k
  have hcoll : (((r*time k).choose 2:ℕ):ℝ)*p k^2/labels k ≤ (1/2:ℝ)*(slots k:ℝ)⁻¹^2 := calc
    _ ≤ (((r*time k).choose 2:ℕ):ℝ)/labels k := by
      apply div_le_div_of_nonneg_right _ hlabel.le
      nlinarith [show (0:ℝ) ≤ ((r*time k).choose 2:ℕ) by positivity]
    _ ≤ ((slots k:ℝ)^2/2)/labels k := div_le_div_of_nonneg_right hc hlabel.le
    _ = _ := by simp only [labels,Nat.cast_pow]; field_simp
  have hmiss : (r:ℝ)*(1-p k)^time k ≤ (k+1:ℝ)*(1-p k)^time k := by
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast hr)
    exact pow_nonneg (by linarith [p_le k]) _
  unfold badBound
  linarith

variable {X : Type*} [MeasurableSpace X]
variable (ν : Measure X) [IsProbabilityMeasure ν]

theorem rare_badPaths_le (k r : ℕ) (hr : r ≤ k+1)
    (T B A : Set X) (L : Fin (labels k) → Set X)
    (hT : MeasurableSet T) (hB : MeasurableSet B) (hA : MeasurableSet A)
    (ht : ν.real T ≤ (16/15:ℝ)*p k^2) (hb : ν.real B ≤ (slots k:ℝ)⁻¹^2)
    (ha : ν.real A = p k) (hl : ∀ j, ν.real (L j) = p k / labels k) :
    (Measure.pi (fun _ : Fin r × Fin (time k) => ν)).real (badPaths T B A L) ≤ badBound k := by
  have hh := badPaths_mass_le (r := r) (n := time k) ν T B A L hT hB hA (p k)
    (by simpa only [Fintype.card_fin] using hl) (by simpa using labels_pos k)
  rw [ha,Fintype.card_fin] at hh
  exact hh.trans (rare_four_terms_le k r hr _ _ ht hb)

end HochschildRare

open MeasureTheory Filter Topology
namespace HochschildRare
open HochschildWalk

def baseCut (k : ℕ) : ℕ := (exists_base_cut k).choose
lemma baseCut_spec (k : ℕ) : labelLaw.real (baseTail (baseCut k)) < (slots k:ℝ)⁻¹^2 :=
  (exists_base_cut k).choose_spec

def stageBad (k r : ℕ) : Set (Fin r × Fin (time k) → Increment) :=
  badPaths (Prod.fst ⁻¹' tailSet k) (Prod.fst ⁻¹' baseTail (baseCut k))
    (Prod.fst ⁻¹' stageSet k) (fun j : Fin (labels k) => Prod.fst ⁻¹' {Sum.inr ⟨k,j⟩})

lemma stageBad_mass_le (k r : ℕ) (hr : r ≤ k+1) :
    (Measure.pi (fun _ : Fin r × Fin (time k) => incrementLaw)).real (stageBad k r) ≤ badBound k := by
  apply rare_badPaths_le incrementLaw k r hr
  · exact measurable_fst (Set.to_countable _).measurableSet
  · exact measurable_fst (Set.to_countable _).measurableSet
  · exact measurable_fst (Set.to_countable _).measurableSet
  · rw [increment_label_mass,tail_mass]
    exact sum_tail_le k
  · rw [increment_label_mass]
    exact (baseCut_spec k).le
  · rw [increment_label_mass]
    exact stage_mass k
  · intro j
    rw [increment_label_mass]
    exact stage_label_mass k j

def StageTests (φ : WalkGroup → ℝ) : Prop :=
  ∀ k r, r ≤ k+1 → ∀ w : Fin r × Fin (time k) → Increment, w ∉ stageBad k r →
    ∀ q : FreeGroup (Fin r), q ≠ 1 → q.toWord.length ≤ k+1 →
      φ (FreeGroup.lift (fun i => word (fun j => incrementValue (w (i,j)))) q) < 1/(k+1:ℝ)

lemma stages_time_atTop : Tendsto time atTop atTop := by
  apply tendsto_atTop_mono (f := fun k => k+1) _ (tendsto_add_atTop_nat 1)
  intro k
  have hk := successor_le_two_pow k
  exact hk.trans (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : k ≤ 3*2^k))

theorem finite_tests_freeMoments (φ : WalkGroup → ℝ) (hf : StageTests φ) :
    FreeMomentsInProbability walkLaw φ time := by
  intro r q hq δ hδ
  have ht : Tendsto (fun k : ℕ => 1/(k+1:ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)))
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ badBound_tendsto
  filter_upwards [eventually_ge_atTop (max r q.toWord.length), ht.eventually (gt_mem_nhds hδ)] with k hk hb
  have hr : r ≤ k+1 := by omega
  have hqk : q.toWord.length ≤ k+1 := by omega
  let E : Set (Fin r × Fin (time k) → WalkGroup) :=
    {w | δ ≤ φ (FreeGroup.lift (fun i => word (fun j => w (i,j))) q)}
  have he := measurePreserving_pi (fun _ : Fin r × Fin (time k) => incrementLaw)
    (fun _ : Fin r × Fin (time k) => walkLaw) (fun _ => incrementValue_preserving)
  have hm := he.measureReal_preimage (s := E) (Set.to_countable E).measurableSet.nullMeasurableSet
  change (Measure.pi (fun _ : Fin r × Fin (time k) => walkLaw)).real E ≤ _
  rw [← hm]
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (stageBad_mass_le k r hr)
  intro w hw
  by_contra hw'
  have hh := hf k r hr w hw' q hq hqk
  change δ ≤ φ (FreeGroup.lift (fun i => word (fun j => incrementValue (w (i,j)))) q) at hw
  linarith

end HochschildRare

open MeasureTheory Filter Topology
open scoped ENNReal
namespace HochschildRare
open HochschildWalk

lemma countable_atom_sum {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]
    [Countable G] (μ : Measure G) [IsProbabilityMeasure μ] :
    ∑' g, μ {g} = 1 := by
  have hh := congrArg (fun ν : Measure G => ν Set.univ) μ.sum_smul_dirac
  simpa only [Measure.sum_apply _ MeasurableSet.univ,Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one,measure_univ] using hh

lemma countable_real_atom_sum {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]
    [Countable G] (μ : Measure G) [IsProbabilityMeasure μ] :
    HasSum (fun g => μ.real {g}) 1 := by
  have hs := ENNReal.summable_toReal (by rw [countable_atom_sum μ]; norm_num : ∑' g, μ {g} ≠ ∞)
  apply hs.hasSum_iff.mpr
  rw [← ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _),countable_atom_sum μ,ENNReal.toReal_one]

lemma probability_eq_atomicLaw {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]
    [Countable G] (μ : Measure G) [IsProbabilityMeasure μ] (e : ℕ ≃ G) :
    atomicLaw (fun j => μ.real {e j}) e = μ := by
  simp only [atomicLaw,Measure.real_def,ENNReal.ofReal_toReal (measure_ne_top _ _)]
  change Measure.sum ((fun g => μ {g} • Measure.dirac g) ∘ e) = μ
  rw [Measure.sum_comp_equiv e,Measure.sum_smul_dirac]

instance : Infinite WalkGroup := Infinite.of_injective FreeGroup.of FreeGroup.of_injective

def walkEnum : ℕ ≃ WalkGroup := Classical.choice inferInstance
def walkWeights (j : ℕ) : ℝ := walkLaw.real {walkEnum j}
lemma walkWeights_nonneg (j : ℕ) : 0 ≤ walkWeights j := measureReal_nonneg
lemma walkWeights_sum : HasSum walkWeights 1 :=
  walkEnum.hasSum_iff.mpr (countable_real_atom_sum walkLaw)
lemma walkLaw_eq_atomic : atomicLaw walkWeights walkEnum = walkLaw :=
  probability_eq_atomicLaw walkLaw walkEnum
end HochschildRare
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

include e hL hτ htr hfaith in

theorem exists_projection_tails (a : ℕ → M) (ha : ∀ n, IsStarProjection (a n))
    (hat : ∀ n, (τ (a n)).re ≤ (1/2:ℝ)^n) :
    ∃ p : ℕ → M, (∀ n, IsStarProjection (p n)) ∧ Antitone p ∧
      (∀ n m, n ≤ m → a m ≤ p n) ∧ GNSTendsto τ p atTop 0 := by
  have hsum (n k : ℕ) : (∑ i ∈ Finset.range k, (τ (a (n+i))).re) ≤ 2*(1/2:ℝ)^n := by
    calc
      _ ≤ ∑ i ∈ Finset.range k, (1/2:ℝ)^(n+i) := Finset.sum_le_sum (fun i _ => hat (n+i))
      _ = (1/2:ℝ)^n * ∑ i ∈ Finset.range k, (1/2:ℝ)^i := by simp only [pow_add,Finset.mul_sum]
      _ ≤ (1/2:ℝ)^n * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le k) (by positivity)
      _ = _ := mul_comm _ _
  choose p hp hpa hpl hpt using fun n =>
    exists_projection_countable_join e τ hL hτ htr hfaith (fun i => a (n+i))
      (fun i => ha (n+i)) (2*(1/2:ℝ)^n) (hsum n)
  have hdom (n m : ℕ) (hnm : n ≤ m) : a m ≤ p n := by
    simpa only [Nat.add_sub_of_le hnm] using hpa n (m-n)
  refine ⟨p,hp,?_,hdom,?_⟩
  · intro n m hnm
    exact hpl m (p n) (hp n) (fun i => hdom n (m+i) (by omega))
  · have ht : Tendsto (fun n : ℕ => 2*(1/2:ℝ)^n) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ)<1)).const_mul 2
    have hs : Tendsto (fun n => Real.sqrt (2*(1/2:ℝ)^n)) atTop (𝓝 0) := by
      simpa only [Real.sqrt_zero,Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp ht
    change Tendsto (fun n => ‖τ.toPreGNS (p n-0)‖) atTop (𝓝 0)
    simp only [sub_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hs
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
      ((preGNS_sq_le_trace τ (p n) (hp n).nonneg (hp n).le_one).trans (hpt n))

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

lemma supported_smul_sum_norm_le (p t : I → M) (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i*p j=0)
    (hpt : ∀ i, p i*t i=t i) (htp : ∀ i, t i*p i=t i)
    (c : I → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (s : Finset I) (R : ℝ) (hR : 0 ≤ R) (ht : ∀ i ∈ s, ‖t i‖ ≤ R) :
    ‖∑ i ∈ s, c i • t i‖ ≤ R := by
  apply supported_sum_norm_le p (fun i => c i • t i) hp horth
    (fun i => by rw [mul_smul_comm,hpt i]) (fun i => by rw [smul_mul_assoc,htp i]) s R hR
  intro i hi
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)).trans (by simpa using ht i hi)

end BoundedHochschild

namespace BoundedHochschild
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma exists_signs_energy (n : ℕ) (v : Fin n → H) :
    ∃ c : Fin n → ℂ, (∀ i, c i=1 ∨ c i= -1) ∧
      (∑ i : Fin n, ‖v i‖^2) ≤ ‖∑ i : Fin n, c i • v i‖^2 := by
  induction n with
  | zero => exact ⟨fun _ => 1,fun _ => Or.inl rfl,by simp⟩
  | succ n ih =>
    obtain ⟨c,hc,he⟩ := ih (fun i => v i.succ)
    let w := ∑ i : Fin n, c i • v i.succ
    have hpara := parallelogram_law_with_norm ℂ (v 0) w
    by_cases hplus : ‖v 0‖^2+‖w‖^2 ≤ ‖v 0+w‖^2
    · refine ⟨Fin.cons 1 c,?_,?_⟩
      · intro i
        refine Fin.cases (Or.inl (by simp)) (fun j => ?_) i
        simpa only [Fin.cons_succ] using hc j
      · rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
        simp only [Fin.cons_zero,Fin.cons_succ,one_smul]
        exact (add_le_add le_rfl he).trans hplus
    · have hminus : ‖v 0‖^2+‖w‖^2 ≤ ‖v 0-w‖^2 := by linarith
      refine ⟨Fin.cons (-1) c,?_,?_⟩
      · intro i
        refine Fin.cases (Or.inr (by simp)) (fun j => ?_) i
        simpa only [Fin.cons_succ] using hc j
      · rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
        simp only [Fin.cons_zero,Fin.cons_succ,neg_one_smul]
        have hn : ‖-v 0+w‖=‖v 0-w‖ := by rw [neg_add_eq_sub,norm_sub_rev]
        change ‖v 0‖^2+(∑ i : Fin n, ‖v i.succ‖^2) ≤ ‖-v 0+w‖^2
        rw [hn]
        exact (add_le_add le_rfl he).trans hminus

lemma sign_bounded_energy (n : ℕ) (v : Fin n → H) (C : ℝ) (_hC : 0 ≤ C)
    (hbound : ∀ c : Fin n → ℂ, (∀ i, c i=1 ∨ c i= -1) →
      ‖∑ i : Fin n, c i • v i‖ ≤ C) :
    (∑ i : Fin n, ‖v i‖^2) ≤ C^2 := by
  obtain ⟨c,hc,he⟩ := exists_signs_energy n v
  exact he.trans (pow_le_pow_left₀ (norm_nonneg _) (hbound c hc) 2)

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

omit [PartialOrder M] [StarOrderedRing M] in
lemma norm_compression_le (p x : M) (C R : ℝ) (hC : 0 ≤ C)
    (hp : ‖p‖ ≤ C) (hx : ‖x‖ ≤ R) : ‖p*x*p‖ ≤ C*R*C := by
  exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right
    ((norm_mul_le _ _).trans (mul_le_mul hp hx (norm_nonneg _) hC)) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hp (mul_nonneg hC ((norm_nonneg _).trans hx))))

theorem no_normal_small_support_sequence
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (B : M →L[ℂ] M) (hB : HasPreadjoint e B)
    (p y : ℕ → M) (hp : ∀ n, IsStarProjection (p n))
    (hpm : Antitone p) (hpt : GNSTendsto τ p atTop 0)
    (hpy : ∀ n, p n*y n=y n) (hyp : ∀ n, y n*p n=y n)
    (R η : ℝ) (hR : 0 ≤ R) (hη : 0 < η)
    (hy : ∀ n, ‖y n‖ ≤ R) (hyB : ∀ n, η ≤ ‖τ.toPreGNS (B (y n))‖) : False := by
  let v (j h : ℕ) := (p j-p h)*y j*(p j-p h)
  have hdn (j h : ℕ) : ‖p j-p h‖ ≤ 2 := by
    exact (norm_sub_le _ _).trans (by linarith [(hp j).norm_le (p j),(hp h).norm_le (p h)])
  have hvn (j h : ℕ) : ‖v j h‖ ≤ 4*R := by
    have hh := norm_compression_le (p j-p h) (y j) 2 R (by norm_num) (hdn j h) (hy j)
    dsimp [v]
    nlinarith
  have hvt (j : ℕ) : GNSTendsto τ (v j) atTop (y j) := by
    have hd : GNSTendsto τ (fun h => p j-p h) atTop (p j) := by
      simpa only [sub_zero] using (GNSTendsto.const τ (p j) atTop).sub τ hpt
    have hdy := hd.mul τ htr (GNSTendsto.const τ (y j) atTop) 2 (hdn j)
    have hh := hdy.mul τ htr hd (2*R) (fun h =>
      (norm_mul_le _ _).trans (mul_le_mul (hdn j h) (hy j) (norm_nonneg _) (by norm_num)))
    simpa only [v,hpy j,hyp j] using hh
  have hnext (j : ℕ) : ∃ h : ℕ, j<h ∧ η/2 < ‖τ.toPreGNS (B (v j h))‖ := by
    by_contra hh
    push Not at hh
    have ht := hB.tendsto e (predual_tendsto_of_preGNS e τ hL hτ hfaith (4*R) (hvn j) (hvt j))
    have hle := preGNS_norm_le_of_predual_tendsto e τ hL hτ (η/2) (half_pos hη).le
      (by filter_upwards [eventually_ge_atTop (j+1)] with h hh'; exact hh h (by omega)) ht
    linarith [hyB j]
  choose next hn hnB using hnext
  let s : ℕ → ℕ := Nat.rec 0 (fun _ k => next k)
  have hsuc (n : ℕ) : s (n+1)=next (s n) := rfl
  have hs : StrictMono s := strictMono_nat_of_lt_succ (fun n => by rw [hsuc]; exact hn (s n))
  let q (n : ℕ) := p (s n)-p (s (n+1))
  let t (n : ℕ) := q n*y (s n)*q n
  have hprod (i j : ℕ) (hij : i ≤ j) : p (s i)*p (s j)=p (s j) :=
    ((hp (s j)).le_iff_mul_eq_right (hp (s i))).mp (hpm (hs.monotone hij))
  have hq (n : ℕ) : IsStarProjection (q n) :=
    (hp (s (n+1))).sub_of_mul_eq_right (hp (s n)) (hprod n (n+1) (by omega))
  have hqorth_lt (i j : ℕ) (hij : i<j) : q i*q j=0 := by
    dsimp [q]
    rw [sub_mul,mul_sub,mul_sub,hprod i j (by omega),hprod i (j+1) (by omega),
      hprod (i+1) j (by omega),hprod (i+1) (j+1) (by omega),sub_self]
  have hqorth (i j : ℕ) (hij : i ≠ j) : q i*q j=0 := by
    rcases lt_or_gt_of_ne hij with hij|hij
    · exact hqorth_lt i j hij
    · simpa only [star_mul,(hq i).isSelfAdjoint.star_eq,(hq j).isSelfAdjoint.star_eq,star_zero]
        using congrArg Star.star (hqorth_lt j i hij)
  have hqt (n : ℕ) : q n*t n=t n := by
    dsimp [t]
    rw [← mul_assoc,← mul_assoc,(hq n).isIdempotentElem.eq]
  have htq (n : ℕ) : t n*q n=t n := by
    dsimp [t]
    rw [mul_assoc,(hq n).isIdempotentElem.eq]
  have htn (n : ℕ) : ‖t n‖ ≤ R := by
    simpa only [one_mul,mul_one] using norm_compression_le (q n) (y (s n)) 1 R
      (by norm_num) ((hq n).norm_le _) (hy (s n))
  have htB (n : ℕ) : η/2 ≤ ‖τ.toPreGNS (B (t n))‖ := by
    simpa only [t,q,hsuc,v] using (hnB (s n)).le
  have henergy (N : ℕ) : (N:ℝ)*(η/2)^2 ≤ (‖B‖*R)^2 := by
    let w (i : Fin N) := τ.toPreGNS (B (t i))
    have hsum : (∑ i : Fin N, ‖w i‖^2) ≤ (‖B‖*R)^2 := by
      apply sign_bounded_energy N w (‖B‖*R) (mul_nonneg (norm_nonneg _) hR)
      intro c hc
      have hnorm : ‖∑ i : Fin N, c i • t i‖ ≤ R := by
        apply supported_smul_sum_norm_le (fun i : Fin N => q i) (fun i : Fin N => t i)
          (fun i => hq i) (fun i j hij => hqorth i j (fun h => hij (Fin.ext h)))
          (fun i => hqt i) (fun i => htq i) c _ Finset.univ R hR (fun i _ => htn i)
        intro i
        rcases hc i with h|h <;> simp only [h,norm_one,norm_neg,le_refl]
      have heq : (∑ i : Fin N, c i • w i) = τ.toPreGNS (B (∑ i : Fin N, c i • t i)) := by
        simp only [map_sum,map_smul,w]
      rw [heq]
      exact (preGNS_norm_le τ h1 _).trans ((B.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)))
    have hle : (N:ℝ)*(η/2)^2 ≤ ∑ i : Fin N, ‖w i‖^2 := by
      have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
        (fun i _ => pow_le_pow_left₀ (half_pos hη).le (htB i) 2)
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
    exact hle.trans hsum
  obtain ⟨N,hN⟩ := exists_nat_gt ((‖B‖*R)^2 / (η/2)^2)
  have hh : (‖B‖*R)^2 < (N:ℝ)*(η/2)^2 := (div_lt_iff₀ (sq_pos_of_pos (half_pos hη))).mp hN
  exact (not_lt_of_ge (henergy N)) hh

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

theorem normal_two_norm_modulus
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (B : M →L[ℂ] M) (hB : HasPreadjoint e B) (R ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x : M, ‖x‖ ≤ R → ‖τ.toPreGNS x‖ < δ → ‖τ.toPreGNS (B x)‖ < ε := by
  by_contra hh
  push Not at hh
  let α : ℝ := ε/(2*(‖B‖+1))
  have hα : 0 < α := div_pos hε (by positivity)
  have hBα : ‖B‖*α ≤ ε/2 := by
    have heq : α*(2*(‖B‖+1))=ε := div_mul_cancel₀ ε (by positivity)
    nlinarith [norm_nonneg B]
  have hxex (n : ℕ) : ∃ x : M, ‖x‖ ≤ R ∧
      ‖τ.toPreGNS x‖ < (α/2)*(1/2:ℝ)^n ∧ ε ≤ ‖τ.toPreGNS (B x)‖ :=
    hh ((α/2)*(1/2:ℝ)^n) (by positivity)
  choose x hx hxs hxB using hxex
  have hR : 0 ≤ R := (norm_nonneg _).trans (hx 0)
  choose y a ha hay hya hyn hxy hat using fun n =>
    exists_small_two_sided_support e τ hL hτ htr hfaith (x n) α hα
  have hat' (n : ℕ) : (τ (a n)).re ≤ (1/2:ℝ)^n := by
    apply (hat n).trans
    have hr : 0 < (1/2:ℝ)^n := by positivity
    have hr1 : (1/2:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hx2 : ‖τ.toPreGNS (x n)‖^2 ≤ ((α/2)*(1/2:ℝ)^n)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hxs n).le 2
    have hrr : ((1/2:ℝ)^n)^2 ≤ (1/2:ℝ)^n := by nlinarith
    have hh' : ‖τ.toPreGNS (x n)‖^2 ≤ α^2/4*(1/2:ℝ)^n := by
      nlinarith [mul_nonneg (sq_nonneg α) (sub_nonneg.mpr hrr)]
    rw [← mul_div_assoc,div_le_iff₀ (sq_pos_of_pos hα)]
    nlinarith [mul_pos (sq_pos_of_pos hα) hr]
  obtain ⟨p,hp,hpm,hpa,hpt⟩ := exists_projection_tails e τ hL hτ htr hfaith a ha hat'
  have hpy (n : ℕ) : p n*y n=y n := by
    calc
      p n*y n = p n*(a n*y n) := by rw [hay n]
      _ = y n := by rw [← mul_assoc,((ha n).le_iff_mul_eq_right (hp n)).mp (hpa n n le_rfl),hay n]
  have hyp (n : ℕ) : y n*p n=y n := by
    calc
      y n*p n = (y n*a n)*p n := by rw [hya n]
      _ = y n := by rw [mul_assoc,((ha n).le_iff_mul_eq_left (hp n)).mp (hpa n n le_rfl),hya n]
  have hyB (n : ℕ) : ε/2 ≤ ‖τ.toPreGNS (B (y n))‖ := by
    have hdiff : ‖τ.toPreGNS (B (x n-y n))‖ ≤ ε/2 :=
      (preGNS_norm_le τ h1 _).trans ((B.le_opNorm _).trans
        ((mul_le_mul_of_nonneg_left (hxy n) (norm_nonneg _)).trans hBα))
    have hh' := norm_sub_le (τ.toPreGNS (B (x n))) (τ.toPreGNS (B (x n-y n)))
    have heq : τ.toPreGNS (B (x n))-τ.toPreGNS (B (x n-y n))=τ.toPreGNS (B (y n)) := by
      simp only [map_sub,sub_sub_cancel]
    rw [heq] at hh'
    have htri := norm_add_le (τ.toPreGNS (B (y n))) (τ.toPreGNS (B (x n-y n)))
    have heq' : τ.toPreGNS (B (y n))+τ.toPreGNS (B (x n-y n))=τ.toPreGNS (B (x n)) := by
      simp only [map_sub]; abel
    rw [heq'] at htri
    linarith [hxB n]
  exact no_normal_small_support_sequence e τ hL hτ htr hfaith h1 B hB p y hp hpm hpt hpy hyp
    R (ε/2) hR (half_pos hε) (fun n => (hyn n).trans (hx n)) hyB

end BoundedHochschild

open MeasureTheory Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildWalk HochschildLiouville TracialUltrapower HochschildRare
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

theorem primitive_of_normal_finite_tests
    (h1 : τ 1=1) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    (hτ : TraceInPredual e τ)
    (label : Label → unitary M)
    (htests : StageTests (fun g => ‖τ (FreeGroup.lift label g : M)‖))
    (hdense : ∀ u : unitary M, ∃ j : ℕ → ℕ,
      Tendsto (fun k => ‖τ.toPreGNS ((label (Sum.inl (j k)):M)-(u:M))‖) atTop (𝓝 0))
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0)
    (hnormal : ∀ a : Fin n → M, HasPreadjoint e (f.curryRight a)) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x=f x := by
  refine primitive_of_walk_and_last_modulus e τ h1 htr hfaith hL hR hτ
    (FreeGroup.lift label) walkWeights walkEnum walkWeights_nonneg walkWeights_sum
    ?_ time stages_time_atTop ?_ ?_ f hf ?_
  · rw [walkLaw_eq_atomic]
    exact walkLaw_symmetric
  · rw [walkLaw_eq_atomic]
    exact finite_tests_freeMoments _ htests
  · intro u
    obtain ⟨j,hj⟩ := hdense u
    refine ⟨fun k => FreeGroup.of (Sum.inl (j k)),?_,?_⟩
    · intro k
      rw [walkLaw_eq_atomic]
      exact (base_atom_pos (j k)).ne'
    · simpa only [FreeGroup.lift_apply_of] using hj
  · intro a R ε hε
    exact normal_two_norm_modulus e τ hL hτ htr hfaith h1 (f.curryRight a) (hnormal a) R ε hε

end BoundedHochschild

open MeasureTheory Filter Topology
namespace HochschildRare
open HochschildWalk

abbrev StageAlphabet (k : ℕ) := Fin (baseCut k) ⊕ ((j : Fin (k+1)) × Fin (labels j.val))

def stageEmbedding (k : ℕ) : StageAlphabet k → Label
  | .inl j => .inl j.val
  | .inr a => .inr ⟨a.1.val,a.2⟩

lemma goodPath_label_in_range {k r : ℕ} (w : Fin r × Fin (time k) → Increment)
    (hw : w ∉ stageBad k r) (i : Fin r × Fin (time k)) :
    (w i).1 ∈ Set.range (stageEmbedding k) := by
  classical
  have htail : ¬ ∃ i, (w i).1 ∈ tailSet k := fun h => hw (Or.inl h)
  have hbase : ¬ ∃ i, (w i).1 ∈ baseTail (baseCut k) := fun h => hw (Or.inr (Or.inl h))
  rcases hwi : (w i).1 with j | ⟨s,j⟩
  · have hj : j < baseCut k := by
      by_contra hh
      exact hbase ⟨i,j,by omega,hwi⟩
    exact ⟨Sum.inl ⟨j,hj⟩,by simp [stageEmbedding]⟩
  · have hs : s < k+1 := by
      by_contra hh
      exact htail ⟨i,s,by omega,j,hwi⟩
    exact ⟨Sum.inr ⟨⟨s,hs⟩,j⟩,by simp [stageEmbedding]⟩

theorem goodPath_distinguished {k r : ℕ} (w : Fin r × Fin (time k) → Increment)
    (hw : w ∉ stageBad k r) :
    ∃ (s : Fin r → Fin (time k)) (a : Fin r → Fin (labels k)),
      (∀ i, (w (i,s i)).1 = Sum.inr ⟨k,a i⟩) ∧
      (∀ i z, (w z).1 = Sum.inr ⟨k,a i⟩ → z=(i,s i)) ∧ Function.Injective a := by
  classical
  have hmiss : ¬ ∃ i, ∀ j, (w (i,j)).1 ∉ stageSet k := fun h => hw (Or.inr (Or.inr (Or.inr h)))
  have hhit : ∀ i : Fin r, ∃ j : Fin (time k), ∃ a : Fin (labels k),
      (w (i,j)).1=Sum.inr ⟨k,a⟩ := by
    intro i
    by_contra hh
    push Not at hh
    exact hmiss ⟨i,fun j ⟨a,ha⟩ => hh j a ha⟩
  choose s a ha using hhit
  have huniq : ∀ i z, (w z).1=Sum.inr ⟨k,a i⟩ → z=(i,s i) := by
    intro i z hz
    by_contra hne
    exact hw (Or.inr (Or.inr (Or.inl ⟨z,(i,s i),hne,a i,hz,ha i⟩)))
  refine ⟨s,a,ha,huniq,?_⟩
  intro i j hij
  have hh := huniq i (j,s j) (by rw [ha j,hij])
  exact (Prod.mk.inj hh).1.symm

lemma goodPaths_finite (k r : ℕ) :
    {w : Fin r × Fin (time k) → Increment | w ∉ stageBad k r}.Finite := by
  classical
  let E : StageAlphabet k × Bool → Increment := fun a => (stageEmbedding k a.1,a.2)
  have hf : (Set.pi Set.univ (fun _ : Fin r × Fin (time k) => Set.range E)).Finite :=
    Set.Finite.pi (fun _ => Set.finite_range E)
  apply hf.subset
  intro w hw i _
  obtain ⟨a,ha⟩ := goodPath_label_in_range w hw i
  exact ⟨(a,(w i).2),Prod.ext ha rfl⟩

lemma boundedWords_finite (r N : ℕ) :
    {q : FreeGroup (Fin r) | q ≠ 1 ∧ q.toWord.length ≤ N}.Finite := by
  classical
  apply ((List.finite_length_le (Fin r × Bool) N).preimage FreeGroup.toWord_injective.injOn).subset
  intro q hq
  exact hq.2
end HochschildRare
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
open MeasureTheory Filter Topology
open scoped ComplexOrder
namespace HochschildRare
open HochschildWalk
variable {M : Type*} [CStarAlgebra M]

def assignedLabel (v : ℕ → unitary M)
    (a : ∀ k, Fin (labels k) → unitary M) : Label → unitary M
  | .inl j => v j
  | .inr t => a t.1 t.2

abbrev StepCoeff (k : ℕ) := Fin (baseCut k) ⊕ ((j : Fin k) × Fin (labels j.val))
def stepEmbedding (k : ℕ) : (StepCoeff k ⊕ Fin (labels k)) → Label
  | .inl (.inl j) => .inl j.val
  | .inl (.inr a) => .inr ⟨a.1.val,a.2⟩
  | .inr j => .inr ⟨k,j⟩

lemma stepEmbedding_injective (k : ℕ) : Function.Injective (stepEmbedding k) := by
  rintro (a|a) (b|b)
  · rcases a with a|⟨s,a⟩ <;> rcases b with b|⟨t,b⟩
    · simp only [stepEmbedding,Sum.inl.injEq,Fin.val_inj]
      exact id
    · simp [stepEmbedding]
    · simp [stepEmbedding]
    · intro h
      have hst : s=t := Fin.ext (congrArg Sigma.fst (Sum.inr.inj h))
      subst t
      have hab : a=b := eq_of_heq (Sigma.mk.inj (Sum.inr.inj h)).2
      subst b
      rfl
  · rcases a with a|⟨s,a⟩
    · simp [stepEmbedding]
    · intro h
      have := congrArg Sigma.fst (Sum.inr.inj h)
      exact False.elim ((Nat.ne_of_lt s.isLt) this)
  · rcases b with b|⟨t,b⟩
    · simp [stepEmbedding]
    · intro h
      have := congrArg Sigma.fst (Sum.inr.inj h)
      exact False.elim ((Nat.ne_of_lt t.isLt) this.symm)
  · intro h
    exact congrArg Sum.inr (eq_of_heq (Sigma.mk.inj (Sum.inr.inj h)).2)

lemma goodPath_step_range {k r : ℕ} (w : Fin r × Fin (time k) → Increment)
    (hw : w ∉ stageBad k r) (i : Fin r × Fin (time k)) :
    (w i).1 ∈ Set.range (stepEmbedding k) := by
  obtain ⟨a,ha⟩ := goodPath_label_in_range w hw i
  rcases a with a|⟨s,a⟩
  · exact ⟨.inl (.inl a),ha⟩
  · by_cases hs : s.val < k
    · exact ⟨.inl (.inr ⟨⟨s.val,hs⟩,a⟩),ha⟩
    · have hsk : s.val=k := by omega
      refine ⟨.inr (Fin.cast (congrArg labels hsk) a),?_⟩
      change Sum.inr ⟨k,Fin.cast (congrArg labels hsk) a⟩=(w i).1
      rw [← ha]
      apply congrArg Sum.inr
      exact (Sigma.ext hsk (by apply (Fin.heq_ext_iff (congrArg labels hsk)).mpr; rfl)).symm

lemma lift_pathValue (v : Label → unitary M) {r n : ℕ}
    (w : Fin r × Fin n → Increment) (q : FreeGroup (Fin r)) :
    FreeGroup.lift v (FreeGroup.lift
      (fun i => word (fun j => incrementValue (w (i,j)))) q) =
      FreeGroup.lift (pathValue v w) q := by
  apply FreeGroup.lift_unique ((FreeGroup.lift v).comp (FreeGroup.lift _))
  intro i
  simp only [MonoidHom.coe_comp,Function.comp_apply,FreeGroup.lift_apply_of,
    word,map_list_prod,List.map_ofFn,pathValue]
  congr 2
  funext j
  cases h : (w (i,j)).2 <;> simp [incrementValue,signedValue,h]

abbrev StageTest (k : ℕ) := (r : Fin (k+2)) ×
  {w : Fin r.val × Fin (time k) → Increment // w ∉ stageBad k r.val} ×
  {q : FreeGroup (Fin r.val) // q ≠ 1 ∧ q.toWord.length ≤ k+1}

instance stageTestFintype (k : ℕ) : Fintype (StageTest k) := by
  classical
  letI (r : Fin (k+2)) : Fintype {w : Fin r.val × Fin (time k) → Increment //
      w ∉ stageBad k r.val} := (goodPaths_finite k r.val).fintype
  letI (r : Fin (k+2)) : Fintype {q : FreeGroup (Fin r.val) //
      q ≠ 1 ∧ q.toWord.length ≤ k+1} := (boundedWords_finite r.val (k+1)).fintype
  infer_instance

def encodePath {k r : ℕ} (w : Fin r × Fin (time k) → Increment)
    (hw : w ∉ stageBad k r) (z : Fin r × Fin (time k)) :
    (StepCoeff k ⊕ Fin (labels k)) × Bool :=
  ((goodPath_step_range w hw z).choose,(w z).2)

lemma encodePath_decodes {k r : ℕ} (w : Fin r × Fin (time k) → Increment)
    (hw : w ∉ stageBad k r) (z : Fin r × Fin (time k)) :
    stepEmbedding k (encodePath w hw z).1=(w z).1 :=
  (goodPath_step_range w hw z).choose_spec

lemma encodePath_distinguished {k r : ℕ} (w : Fin r × Fin (time k) → Increment)
    (hw : w ∉ stageBad k r) :
    ∃ (s : Fin r → Fin (time k)) (a : Fin r → Fin (labels k)),
      (∀ i, (encodePath w hw (i,s i)).1=Sum.inr (a i)) ∧
      (∀ i z, (encodePath w hw z).1=Sum.inr (a i) → z=(i,s i)) := by
  obtain ⟨s,a,ha,huniq,_⟩ := goodPath_distinguished w hw
  refine ⟨s,a,fun i => ?_,fun i z hz => ?_⟩
  · apply stepEmbedding_injective k
    rw [encodePath_decodes,ha]
    rfl
  · apply huniq i z
    rw [← encodePath_decodes w hw z,hz]
    rfl

def stageCoeff (v : ℕ → unitary M) (a : ∀ k, Fin (labels k) → unitary M)
    (k : ℕ) : StepCoeff k → unitary M := fun b =>
  assignedLabel v a (stepEmbedding k (Sum.inl b))

lemma updated_step (v : ℕ → unitary M) (a : ∀ k, Fin (labels k) → unitary M)
    (k : ℕ) (u : Fin (labels k) → unitary M) (b : StepCoeff k ⊕ Fin (labels k)) :
    assignedLabel v (Function.update a k u) (stepEmbedding k b)=
      Sum.elim (stageCoeff v a k) u b := by
  classical
  rcases b with (b|⟨j,b⟩)|b
  · rfl
  · simp [assignedLabel,stepEmbedding,stageCoeff,Function.update_of_ne (Nat.ne_of_lt j.isLt)]
  · simp [assignedLabel,stepEmbedding]

lemma pathValue_updated (v : ℕ → unitary M) (a : ∀ k, Fin (labels k) → unitary M)
    {k r : ℕ} (u : Fin (labels k) → unitary M)
    (w : Fin r × Fin (time k) → Increment) (hw : w ∉ stageBad k r) :
    pathValue (assignedLabel v (Function.update a k u)) w =
      pathValue (Sum.elim (stageCoeff v a k) u) (encodePath w hw) := by
  funext i
  unfold pathValue
  congr 1
  funext j
  have hh := updated_step v a k u (encodePath w hw (i,j)).1
  rw [encodePath_decodes] at hh
  unfold signedValue
  change (if (w (i,j)).2 then _ else _)=(if (w (i,j)).2 then _ else _)
  rw [hh]

variable [PartialOrder M]

def AtStage (τ : M →ₚ[ℂ] ℂ) (v : ℕ → unitary M)
    (a : ∀ k, Fin (labels k) → unitary M) (k : ℕ) : Prop :=
  ∀ r, r ≤ k+1 → ∀ w : Fin r × Fin (time k) → Increment, w ∉ stageBad k r →
    ∀ q : FreeGroup (Fin r), q ≠ 1 → q.toWord.length ≤ k+1 →
      ‖τ (FreeGroup.lift (assignedLabel v a) (FreeGroup.lift
        (fun i => word (fun j => incrementValue (w (i,j)))) q) : M)‖ < 1/(k+1:ℝ)

theorem exists_stage_choice (τ : M →ₚ[ℂ] ℂ) (hf : FinitePathTests τ)
    (v : ℕ → unitary M) (a : ∀ k, Fin (labels k) → unitary M) (k : ℕ) :
    ∃ u : Fin (labels k) → unitary M, AtStage τ v (Function.update a k u) k := by
  classical
  obtain ⟨u,hu⟩ := hf (StepCoeff k) (Fin (labels k)) (StageTest k)
    ⟨⟨0,labels_pos k⟩⟩ (stageCoeff v a k) (fun t => t.1.val) (fun _ => time k)
    (fun t => encodePath t.2.1.val t.2.1.property) (fun t => t.2.2.val)
    (fun t => t.2.2.property.1)
    (fun t => encodePath_distinguished t.2.1.val t.2.1.property)
    (1/(k+1:ℝ)) (by positivity)
  refine ⟨u,fun r hr w hw q hq hqn => ?_⟩
  let t : StageTest k := ⟨⟨r,by omega⟩,⟨w,hw⟩,⟨q,hq,hqn⟩⟩
  have ht := hu t
  change ‖τ (FreeGroup.lift (pathValue (Sum.elim (stageCoeff v a k) u) (encodePath w hw)) q : M)‖ < _ at ht
  rw [lift_pathValue,pathValue_updated]
  exact ht

lemma atStage_congr (τ : M →ₚ[ℂ] ℂ) (v : ℕ → unitary M)
    (a b : ∀ k, Fin (labels k) → unitary M) (k : ℕ)
    (hab : ∀ j, j ≤ k → a j=b j) (ha : AtStage τ v a k) : AtStage τ v b k := by
  intro r hr w hw q hq hqn
  have hpath : pathValue (assignedLabel v a) w=pathValue (assignedLabel v b) w := by
    funext i
    unfold pathValue
    congr 1
    funext j
    have he : assignedLabel v a (w (i,j)).1=assignedLabel v b (w (i,j)).1 := by
      obtain ⟨s,hs⟩ := goodPath_label_in_range w hw (i,j)
      rw [← hs]
      rcases s with s|⟨t,s⟩
      · rfl
      · change a t.val s=b t.val s
        rw [hab t.val (by omega)]
    simp only [signedValue,he]
  have hh := ha r hr w hw q hq hqn
  rw [lift_pathValue,hpath,← lift_pathValue] at hh
  exact hh

def stageAssignments (τ : M →ₚ[ℂ] ℂ) (hf : FinitePathTests τ)
    (v : ℕ → unitary M) : ℕ → (∀ k, Fin (labels k) → unitary M)
  | 0 => fun _ _ => 1
  | k+1 => Function.update (stageAssignments τ hf v k) k
      (exists_stage_choice τ hf v (stageAssignments τ hf v k) k).choose

lemma stageAssignments_spec (τ : M →ₚ[ℂ] ℂ) (hf : FinitePathTests τ)
    (v : ℕ → unitary M) (k : ℕ) : AtStage τ v (stageAssignments τ hf v (k+1)) k :=
  (exists_stage_choice τ hf v (stageAssignments τ hf v k) k).choose_spec

lemma stageAssignments_stable (τ : M →ₚ[ℂ] ℂ) (hf : FinitePathTests τ)
    (v : ℕ → unitary M) (j k : ℕ) (hjk : j+1 ≤ k) :
    stageAssignments τ hf v k j=stageAssignments τ hf v (j+1) j := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [stageAssignments,Function.update_of_ne (by omega : j ≠ k),ih]

theorem exists_label_of_finite_paths (τ : M →ₚ[ℂ] ℂ) (hf : FinitePathTests τ)
    (v : ℕ → unitary M) :
    ∃ label : Label → unitary M, (∀ j, label (Sum.inl j)=v j) ∧
      StageTests (fun g => ‖τ (FreeGroup.lift label g : M)‖) := by
  let a : ∀ k, Fin (labels k) → unitary M := fun k => stageAssignments τ hf v (k+1) k
  refine ⟨assignedLabel v a,fun _ => rfl,?_⟩
  change ∀ k, AtStage τ v a k
  intro k
  apply atStage_congr τ v (stageAssignments τ hf v (k+1)) a k
    (fun j hj => stageAssignments_stable τ hf v j (k+1) (by omega))
  exact stageAssignments_spec τ hf v k
end HochschildRare
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

end HochschildTraceNorm

open scoped ComplexOrder
namespace HochschildTraceNorm
open HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (htr : ∀ a b : A, τ (a*b)=τ (b*a))

end HochschildTraceNorm

open scoped ComplexOrder
namespace BoundedHochschild
open HochschildTraceNorm
variable {N X : Type*} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N) (τ : N →ₚ[ℂ] ℂ)

omit [PartialOrder N] [StarOrderedRing N] in
lemma predual_vector_ext (z w : X) (h : ∀ a : N, e.symm a z=e.symm a w) : z=w := by
  apply (NormedSpace.inclusionInDoubleDualLi ℂ).injective
  ext f
  change f z=f w
  simpa only [e.symm_apply_apply] using h (e f)

variable (hL : ∀ b : N, HasPreadjoint e (ContinuousLinearMap.mul ℂ N b))
  (hτ : TraceInPredual e τ)

omit [StarOrderedRing N] in
include hL hτ in
lemma exists_trace_vector (b : N) : ∃ z : X, ∀ a : N, e.symm a z=star (τ (star b*a)) := by
  obtain ⟨z,hz⟩ := hτ
  obtain ⟨w,hw⟩ := hL (star b) z
  refine ⟨w,fun a => ?_⟩
  rw [hz,star_star,← hw]
  rfl

def traceVector (b : N) : X := Classical.choose (exists_trace_vector e τ hL hτ b)

omit [StarOrderedRing N] in
lemma traceVector_spec (b a : N) : e.symm a (traceVector e τ hL hτ b)=star (τ (star b*a)) :=
  Classical.choose_spec (exists_trace_vector e τ hL hτ b) a

def traceVectorLinear : N →ₗ[ℂ] X where
  toFun := traceVector e τ hL hτ
  map_add' b c := by
    apply predual_vector_ext e
    intro a
    simp only [map_add,traceVector_spec,star_add,add_mul]
  map_smul' r b := by
    apply predual_vector_ext e
    intro a
    simp only [traceVector_spec,map_smul,star_smul,smul_mul_assoc,star_star,RingHom.id_apply]

omit [StarOrderedRing N] in
@[simp] lemma traceVectorLinear_apply (b : N) :
    traceVectorLinear e τ hL hτ b=traceVector e τ hL hτ b := rfl
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
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ)

lemma preGNS_sq_le_traceVector (b : M) :
    ‖τ.toPreGNS b‖^2 ≤ ‖b‖*‖traceVectorLinear e τ hL hτ b‖ := by
  have hs : ‖τ.toPreGNS b‖^2=‖τ (star b*b)‖ := by
    have hh := congrArg norm (τ.preGNS_norm_sq (τ.toPreGNS b))
    simpa only [norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),PositiveLinearMap.ofPreGNS_toPreGNS] using hh
  rw [hs]
  have hh := traceVector_spec e τ hL hτ b b
  calc
    _ = ‖e.symm b (traceVectorLinear e τ hL hτ b)‖ := by rw [traceVectorLinear_apply,hh,norm_star]
    _ ≤ ‖e.symm b‖*‖traceVectorLinear e τ hL hτ b‖ := (e.symm b).le_opNorm _
    _ = _ := by rw [e.symm.norm_map]

include hL hτ in

theorem exists_dense_unitary_base [TopologicalSpace.SeparableSpace X] :
    ∃ v : ℕ → unitary M, ∀ u : unitary M, ∃ j : ℕ → ℕ,
      Tendsto (fun k => ‖τ.toPreGNS ((v (j k):M)-(u:M))‖) atTop (𝓝 0) := by
  classical
  let J := traceVectorLinear e τ hL hτ
  let S : Set X := Set.range (fun u : unitary M => J (u:M))
  let : Nonempty S := ⟨⟨J (1:M),⟨1,rfl⟩⟩⟩
  let d : ℕ → S := TopologicalSpace.denseSeq S
  choose v hv using fun n => (d n).property
  refine ⟨v,fun u => ?_⟩
  let z : S := ⟨J (u:M),⟨u,rfl⟩⟩
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp
    ((TopologicalSpace.denseRange_denseSeq S) z)
  choose j hj using hy
  have hconv : Tendsto (fun k => J (v (j k):M)) atTop (𝓝 (J (u:M))) := by
    have ht := continuous_subtype_val.tendsto z |>.comp hyt
    have hf : (fun k => J (v (j k):M))=(fun k => (y k:X)) := by
      funext k
      have hh := congrArg Subtype.val (hj k)
      exact (hv (j k)).trans hh
    rw [hf]
    exact ht
  have hJn : Tendsto (fun k => ‖J ((v (j k):M)-(u:M))‖) atTop (𝓝 0) := by
    have hh := (hconv.sub_const (J (u:M))).norm
    simpa only [map_sub,sub_self,norm_zero] using hh
  have hunit (a : unitary M) : ‖(a:M)‖ ≤ 1 := by
    have hh := CStarRing.norm_coe_unitary_mul a (1:M)
    simp only [mul_one] at hh
    rw [hh]
    by_cases ht : Nontrivial M
    · let : Nontrivial M := ht
      exact (norm_one (α := M)).le
    · have : Subsingleton M := not_nontrivial_iff_subsingleton.mp ht
      simp [Subsingleton.elim (1:M) 0]
  have hbound (k : ℕ) : ‖τ.toPreGNS ((v (j k):M)-(u:M))‖^2 ≤
      2*‖J ((v (j k):M)-(u:M))‖ := by
    apply (preGNS_sq_le_traceVector e τ hL hτ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by linarith [hunit (v (j k)),hunit u])
  have hsq : Tendsto (fun k => ‖τ.toPreGNS ((v (j k):M)-(u:M))‖^2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hbound (by simpa using hJn.const_mul 2)
  refine ⟨j,?_⟩
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using hh

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildWalk HochschildRare
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [TopologicalSpace.SeparableSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

theorem primitive_of_separable_normal_finite_paths
    (h1 : τ 1=1) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    (hτ : TraceInPredual e τ) (hpaths : FinitePathTests τ)
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0)
    (hnormal : ∀ a : Fin n → M, HasPreadjoint e (f.curryRight a)) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x=f x := by
  obtain ⟨v,hv⟩ := exists_dense_unitary_base e τ hL hτ
  obtain ⟨label,hbase,htests⟩ := exists_label_of_finite_paths τ hpaths v
  refine primitive_of_normal_finite_tests e τ h1 htr hfaith hL hR hτ
    label htests ?_ f hf hnormal
  intro u
  obtain ⟨j,hj⟩ := hv u
  refine ⟨j,?_⟩
  simpa only [hbase] using hj
end BoundedHochschild
end
end OAI
end

theorem solution.{u_1,u_2} : type_of% @OAI.BoundedHochschild.primitive_of_separable_normal_finite_paths.{u_1,u_2} := @OAI.BoundedHochschild.primitive_of_separable_normal_finite_paths.{u_1,u_2}
