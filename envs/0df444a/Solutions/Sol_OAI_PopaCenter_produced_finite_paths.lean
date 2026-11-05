-- Prove2me | solution 1 for OAI.PopaCenter.produced_finite_paths
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:00:28.882219+00:00
-- url     : https://prove2.me/submissions/db6c2995-8d17-4fbc-97b0-54963023f677

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_PopaCenter_exists_homogeneous_system
import Theorems.Thm_OAI_PopaCenter_full_center_lift_norm
import Theorems.Thm_OAI_PopaCenter_quantize_words

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
namespace HochschildPaths
variable {C D : Type*} {r n : ℕ}

def signed {G : Type*} [Group G] (g : G) (b : Bool) : G := if b then g else g⁻¹

@[simp] lemma signed_signed {G : Type*} [Group G] (g : G) (b : Bool) :
    signed (signed g b) b=g := by cases b <;> simp [signed]

@[simp] lemma signed_one {G : Type*} [Group G] (b : Bool) : signed (1:G) b=1 := by
  cases b <;> simp [signed]

lemma map_signed {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) (b : Bool) :
    f (signed g b)=signed (f g) b := by cases b <;> simp [signed]

lemma prod_ofFn_single {G : Type*} [Monoid G] {n : ℕ} (f : Fin n → G) (j : Fin n)
    (hf : ∀ i, i ≠ j → f i=1) : (List.ofFn f).prod=f j := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    rw [List.ofFn_succ,List.prod_cons]
    induction j using Fin.cases with
    | zero =>
      have h : (List.ofFn fun i : Fin n => f i.succ).prod=1 := by
        apply List.prod_eq_one
        intro a ha
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
        exact hf i.succ (Fin.succ_ne_zero i)
      rw [h,mul_one]
    | succ j =>
      rw [hf 0 (Ne.symm (Fin.succ_ne_zero j)),one_mul]
      apply ih
      intro i hi
      exact hf i.succ (fun h => hi (Fin.succ_injective _ h))

variable (w : Fin r × Fin n → (C ⊕ D) × Bool)
  (s : Fin r → Fin n) (a : Fin r → D)
  (hpos : ∀ i, (w (i,s i)).1=Sum.inr (a i))
  (huniq : ∀ i z, (w z).1=Sum.inr (a i) → z=(i,s i))

include hpos huniq in
lemma distinguished_injective : Function.Injective a := by
  intro i j hij
  have h := huniq i (j,s j) ((hpos j).trans (congrArg Sum.inr hij.symm))
  exact (congrArg Prod.fst h).symm

def retractLetter (x : C ⊕ D) : FreeGroup (Fin r) := by
  classical
  exact if h : ∃ i, x=Sum.inr (a i) then
    signed (FreeGroup.of h.choose) (w (h.choose,s h.choose)).2
  else 1

include hpos huniq in
lemma retractLetter_distinguished (i : Fin r) :
    retractLetter w s a (Sum.inr (a i))=signed (FreeGroup.of i) (w (i,s i)).2 := by
  classical
  unfold retractLetter
  split_ifs with h
  · have hi : h.choose=i := distinguished_injective w s a hpos huniq
      (Sum.inr.inj h.choose_spec).symm
    simp only [hi]
  · exact False.elim (h ⟨i,rfl⟩)

include huniq in
lemma retractLetter_away (i : Fin r) (j : Fin n) (hj : j ≠ s i) :
    retractLetter w s a (w (i,j)).1=1 := by
  classical
  unfold retractLetter
  split_ifs with h
  · have hz := huniq h.choose (i,j) h.choose_spec
    have hi : i=h.choose := congrArg Prod.fst hz
    have hs : j=s i := (congrArg Prod.snd hz).trans (congrArg s hi.symm)
    exact False.elim (hj hs)
  · rfl

def formalPath (i : Fin r) : FreeGroup (C ⊕ D) :=
  (List.ofFn fun j => signed (FreeGroup.of (w (i,j)).1) (w (i,j)).2).prod

def pathHom : FreeGroup (Fin r) →* FreeGroup (C ⊕ D) :=
  FreeGroup.lift (formalPath w)

def retractHom : FreeGroup (C ⊕ D) →* FreeGroup (Fin r) :=
  FreeGroup.lift (retractLetter w s a)

include hpos huniq in
lemma retract_formalPath (i : Fin r) :
    retractHom w s a (formalPath w i)=FreeGroup.of i := by
  classical
  simp only [formalPath,map_list_prod,List.map_ofFn,retractHom]
  rw [prod_ofFn_single _ (s i)]
  · simp only [Function.comp_apply,map_signed,FreeGroup.lift_apply_of]
    rw [hpos,retractLetter_distinguished w s a hpos huniq,signed_signed]
  · intro j hj
    simp only [Function.comp_apply,map_signed,FreeGroup.lift_apply_of]
    rw [retractLetter_away w s a huniq i j hj,signed_one]

include hpos huniq in

theorem retract_pathHom (q : FreeGroup (Fin r)) :
    retractHom w s a (pathHom w q)=q := by
  have h : (retractHom w s a).comp (pathHom w)=MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro i
    simp only [MonoidHom.comp_apply,pathHom,FreeGroup.lift_apply_of,MonoidHom.id_apply]
    exact retract_formalPath w s a hpos huniq i
  exact congrArg (fun f : FreeGroup (Fin r) →* FreeGroup (Fin r) => f q) h

def freshProjection : FreeGroup (C ⊕ D) →* FreeGroup D :=
  FreeGroup.lift (Sum.elim (fun _ : C => 1) FreeGroup.of)

lemma retract_factors :
    (FreeGroup.lift (fun d : D => retractLetter w s a (Sum.inr d))).comp
      (freshProjection (C := C) (D := D)) = retractHom w s a := by
  classical
  apply FreeGroup.ext_hom
  intro z
  cases z with
  | inl c =>
    simp [freshProjection,retractHom,retractLetter]
  | inr d =>
    simp only [MonoidHom.comp_apply,freshProjection,FreeGroup.lift_apply_of,
      Sum.elim_inr,retractHom]

include hpos huniq in

theorem freshProjection_pathHom_ne_one (q : FreeGroup (Fin r)) (hq : q ≠ 1) :
    freshProjection (pathHom w q) ≠ 1 := by
  intro h
  have hh := congrArg (FreeGroup.lift (fun d : D => retractLetter w s a (Sum.inr d))) h
  change ((FreeGroup.lift (fun d : D => retractLetter w s a (Sum.inr d))).comp
    freshProjection) (pathHom w q)=_ at hh
  rw [retract_factors,retract_pathHom w s a hpos huniq,map_one] at hh
  exact hq hh

end HochschildPaths

namespace HochschildPaths
variable {M C D : Type*} [Ring M] [Algebra ℂ M]
  (B : Subalgebra ℂ M) (v : C → Bˣ) (u : D → Mˣ)

end HochschildPaths

open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildPaths
open HochschildUltrapower HochschildRare
variable {M C D : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1=1) (ω : Ultrafilter ℕ)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))

omit [PartialOrder M] [StarOrderedRing M] in
lemma lift_pathValue_formal {r n : ℕ} (v : C ⊕ D → unitary M)
    (w : Fin r × Fin n → (C ⊕ D) × Bool) (q : FreeGroup (Fin r)) :
    FreeGroup.lift (pathValue v w) q = FreeGroup.lift v (pathHom w q) := by
  have h : FreeGroup.lift (pathValue v w)=(FreeGroup.lift v).comp (pathHom w) := by
    apply FreeGroup.ext_hom
    intro i
    simp only [FreeGroup.lift_apply_of,MonoidHom.comp_apply,pathHom,formalPath,
      map_list_prod,List.map_ofFn,pathValue,HochschildWalk.word]
    congr 2
    funext j
    change signedValue v (w (i,j))=FreeGroup.lift v (signed (FreeGroup.of (w (i,j)).1) (w (i,j)).2)
    rw [map_signed,FreeGroup.lift_apply_of]
    rfl
  exact congrArg (fun f : FreeGroup (Fin r) →* unitary M => f q) h
end HochschildPaths
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

lemma le_def {v w : CornerIso p q} : v ≤ w ↔
    v.initial ≤ w.initial ∧ (w:M)*v.initial=(v:M) := Iff.rfl

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

section Dual
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

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
end Dual
end CornerIso
end PopaCorners
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaCorner
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {p : M} (hp : IsStarProjection p)

end PopaCorner

namespace PopaCorner
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {p : M} (hp : IsStarProjection p)

omit [PartialOrder M] [StarOrderedRing M] in
lemma compress_norm_le (x : M) : ‖compress hp x‖ ≤ ‖x‖ := by
  change ‖p*x*p‖ ≤ ‖x‖
  calc
    _ ≤ (‖p‖*‖x‖)*‖p‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg p))
    _ ≤ (1*‖x‖)*1 := mul_le_mul (mul_le_mul_of_nonneg_right hp.norm_le (norm_nonneg x)) hp.norm_le
      (norm_nonneg p) (by positivity)
    _ = ‖x‖ := by ring
end PopaCorner

open Filter Topology
open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {p : M} (hp : IsStarProjection p)

def weakSpace : Submodule ℂ (WeakDual ℂ X) :=
  (algebra hp).toNonUnitalSubalgebra.toSubmodule.comap (WeakAlgebra.weakEquiv e).toLinearMap

omit [PartialOrder M] [StarOrderedRing M] in
lemma weakSpace_closed : IsClosed (weakSpace e hp : Set (WeakDual ℂ X)) := by
  have hL := WeakAlgebra.normal_continuous e (ContinuousLinearMap.mul ℂ M p)
    ((HochschildSakai.abstract_multiplication_normal e).1 p)
  have hR := WeakAlgebra.normal_continuous e ((ContinuousLinearMap.mul ℂ M).flip p)
    ((HochschildSakai.abstract_multiplication_normal e).2 p)
  have he : (weakSpace e hp : Set (WeakDual ℂ X)) =
      {f | (WeakAlgebra.weakEquiv e).symm (p*WeakAlgebra.weakEquiv e f)=f} ∩
      {f | (WeakAlgebra.weakEquiv e).symm (WeakAlgebra.weakEquiv e f*p)=f} := by
    ext f
    change (p*WeakAlgebra.weakEquiv e f=WeakAlgebra.weakEquiv e f ∧
      WeakAlgebra.weakEquiv e f*p=WeakAlgebra.weakEquiv e f) ↔ _
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,LinearEquiv.symm_apply_eq]
  rw [he]
  exact (isClosed_eq hL continuous_id).inter (isClosed_eq hR continuous_id)

def strongEquiv : WeakSubspace.strong (weakSpace e hp) ≃ₗᵢ⋆[ℂ] algebra hp where
  toFun f := ⟨e f.val,by
    have hh := (WeakSubspace.mem_strong (weakSpace e hp) f.val).mp f.property
    exact hh⟩
  invFun a := ⟨e.symm a.val,by
    rw [WeakSubspace.mem_strong]
    change e (e.symm a.val) ∈ algebra hp
    simp⟩
  left_inv f := by apply Subtype.ext; exact e.symm_apply_apply f.val
  right_inv a := by apply Subtype.ext; exact e.apply_symm_apply a.val
  map_add' f g := by apply Subtype.ext; exact map_add e f.val g.val
  map_smul' c f := by apply Subtype.ext; exact e.map_smulₛₗ c f.val
  norm_map' f := e.norm_map f.val

def predualEquiv : StrongDual ℂ (X ⧸ WeakSubspace.preannihilator (weakSpace e hp)) ≃ₗᵢ⋆[ℂ] algebra hp :=
  (WeakSubspace.quotientDualEquiv (weakSpace e hp) (weakSpace_closed e hp)).trans
    (strongEquiv e hp)

omit [PartialOrder M] [StarOrderedRing M] in
lemma predualEquiv_symm_apply_mk (a : algebra hp) (z : X) :
    (predualEquiv e hp).symm a (Submodule.Quotient.mk z)=e.symm (a:M) z := by
  have hs : ∀ F : StrongDual ℂ (X ⧸ WeakSubspace.preannihilator (weakSpace e hp)),
      e.symm ((predualEquiv e hp F : algebra hp):M) z = F (Submodule.Quotient.mk z) := by
    intro F
    change e.symm (e (F.comp (WeakSubspace.preannihilator (weakSpace e hp)).mkQL)) z=_
    rw [e.symm_apply_apply]
    rfl
  have hh := hs ((predualEquiv e hp).symm a)
  rw [LinearIsometryEquiv.apply_symm_apply] at hh
  exact hh.symm
end PopaCorner
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

lemma average_gns_norm (a : M) :
    ‖τ.toPreGNS (average e τ hτ htr hfaith a)‖ ≤ ‖τ.toPreGNS a‖ := by
  have hsub : gnsVector τ '' convexHull ℝ (Set.range (fun v : unitary M => conjugate v a)) ⊆
      Metric.closedBall (0:τ.GNS) ‖τ.toPreGNS a‖ := by
    rw [LinearMap.image_convexHull]
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
    simp only [Metric.mem_closedBall,dist_zero_right,gnsVector_norm]
    simpa only [gnsVector_norm] using le_of_eq (conjugate_gns_norm τ htr v a)
  have hh := closure_minimal hsub Metric.isClosed_closedBall (average_orbit e τ hτ htr hfaith a)
  simpa only [Metric.mem_closedBall,dist_zero_right,gnsVector_norm] using hh
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaTypeII
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
lemma average_gns_tendsto {I : Type*} {l : Filter I} {a : I → M} {b : M}
    (ha : GNSTendsto τ a l b) :
    GNSTendsto τ (fun n => average e τ hτ htr hfaith (a n)) l (average e τ hτ htr hfaith b) := by
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) ha
  change ‖τ.toPreGNS (expectation e τ hτ htr hfaith h1 (a n)-expectation e τ hτ htr hfaith h1 b)‖≤_
  rw [←map_sub]
  exact average_gns_norm e τ hτ htr hfaith _

include h1 in
lemma homogeneous_limit {a : ℕ → M} {b : M} (ha : ∀ n, Homogeneous e τ hτ htr hfaith (a n))
    (ht : GNSTendsto τ a atTop b) (C : ℝ) (hC : ∀ n, ‖a n‖≤C) :
    Homogeneous e τ hτ htr hfaith b := by
  have htt := Complex.continuous_re.tendsto _ |>.comp
    (trace_predual_tendsto e τ hτ (ht.predual e τ (HochschildSakai.abstract_multiplication_normal e).1 hτ hfaith C hC))
  have htn : Tendsto (fun n => (τ (a n)).re • (1:M)) atTop (𝓝 ((τ b).re • (1:M))) :=
    htt.smul_const 1
  have hgns : GNSTendsto τ (fun n => (τ (a n)).re • (1:M)) atTop ((τ b).re • (1:M)) := by
    have hn := tendsto_iff_norm_sub_tendsto_zero.mp htn
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => preGNS_norm_le τ h1 _) hn
  exact GNSTendsto.unique τ hfaith (average_gns_tendsto e τ hτ htr hfaith h1 ht)
    (by simpa only [show ∀ n, average e τ hτ htr hfaith (a n)=(τ (a n)).re • (1:M) from ha] using hgns)

include h1 in
lemma homogeneous_zero : Homogeneous e τ hτ htr hfaith (0:M) := by
  change expectation e τ hτ htr hfaith h1 0=(τ 0).re • (1:M)
  rw [map_zero, map_zero, Complex.zero_re, zero_smul]

include h1 in
lemma homogeneous_sub {p q : M} (hp : Homogeneous e τ hτ htr hfaith p)
    (hq : Homogeneous e τ hτ htr hfaith q) : Homogeneous e τ hτ htr hfaith (p-q) := by
  change expectation e τ hτ htr hfaith h1 (p-q)=(τ (p-q)).re • (1:M)
  rw [map_sub,show expectation e τ hτ htr hfaith h1 p=(τ p).re • (1:M) from hp,
    show expectation e τ hτ htr hfaith h1 q=(τ q).re • (1:M) from hq,map_sub,Complex.sub_re,sub_smul]

include h1 in
lemma homogeneous_add {p q : M} (hp : Homogeneous e τ hτ htr hfaith p)
    (hq : Homogeneous e τ hτ htr hfaith q) : Homogeneous e τ hτ htr hfaith (p+q) := by
  change expectation e τ hτ htr hfaith h1 (p+q)=(τ (p+q)).re • (1:M)
  rw [map_add,show expectation e τ hτ htr hfaith h1 p=(τ p).re • (1:M) from hp,
    show expectation e τ hτ htr hfaith h1 q=(τ q).re • (1:M) from hq,map_add,Complex.add_re,add_smul]
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
variable (G M : Type*) [Group G] [CStarAlgebra M]

namespace Rep
variable {G M} [PartialOrder M] [StarOrderedRing M]

def support (v : Rep G M) : M := v 1

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma support_mul (v : Rep G M) (g : G) : v.support*v g=v g := by
  rw [support,←v.mul,one_mul]
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma mul_support (v : Rep G M) (g : G) : v g*v.support=v g := by
  rw [support,←v.mul,mul_one]
omit [PartialOrder M] [StarOrderedRing M] in
lemma support_projection (v : Rep G M) : IsStarProjection v.support := by
  constructor
  · exact v.support_mul 1
  · simpa only [IsSelfAdjoint,support,inv_one] using (v.inv 1).symm
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma star_mul_self (v : Rep G M) (g : G) : star (v g)*v g=v.support := by
  rw [←v.inv,←v.mul,inv_mul_cancel,support]
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma mul_star_self (v : Rep G M) (g : G) : v g*star (v g)=v.support := by
  rw [←v.inv,←v.mul,mul_inv_cancel,support]
omit [PartialOrder M] [StarOrderedRing M] in
lemma norm_le (v : Rep G M) (g : G) : ‖v g‖≤1 := by
  have hh := v.support_projection.norm_le
  rw [←v.star_mul_self g,CStarRing.norm_star_mul_self] at hh
  nlinarith [norm_nonneg (v g)]

def zero : Rep G M where
  val _ := 0
  mul _ _ := by simp
  inv _ := by simp

def add (v w : Rep G M) (hvw : v.support*w.support=0) : Rep G M where
  val g := v g+w g
  mul g h := by
    have hfg : w.support*v.support=0 := by
      have hh := congrArg star hvw
      simpa only [star_mul,v.support_projection.isSelfAdjoint.star_eq,
        w.support_projection.isSelfAdjoint.star_eq,star_zero] using hh
    have hvw' : v g*w h=0 := by
      calc
        v g*w h = (v g*v.support)*(w.support*w h) := by rw [v.mul_support,w.support_mul]
        _ = v g*(v.support*w.support)*w h := by simp only [mul_assoc]
        _ = 0 := by rw [hvw,mul_zero,zero_mul]
    have hwv : w g*v h=0 := by
      calc
        w g*v h = (w g*w.support)*(v.support*v h) := by rw [w.mul_support,v.support_mul]
        _ = w g*(w.support*v.support)*v h := by simp only [mul_assoc]
        _ = 0 := by rw [hfg,mul_zero,zero_mul]
    simp only [v.mul,w.mul,add_mul,mul_add,hvw',hwv,zero_add,add_zero]
  inv g := by simp only [v.inv,w.inv,star_add]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma add_apply (v w : Rep G M) (hvw) (g : G) : add v w hvw g=v g+w g := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma add_support (v w : Rep G M) (hvw) : (add v w hvw).support=v.support+w.support := rfl
end Rep
end PopaPatching
end
end OAI
end

section
namespace OAI

noncomputable section

namespace PopaFinite
open FreeGroup
variable {G : Type*} [Group G]

private def partialLeft (B : Finset G) (g : G) :
    {x : B // g*(x:G) ∈ B} ≃ {x : B // g⁻¹*(x:G) ∈ B} where
  toFun x := ⟨⟨g*(x.val:G),x.property⟩,by simp⟩
  invFun x := ⟨⟨g⁻¹*(x.val:G),x.property⟩,by simp⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; apply Subtype.ext; simp

def finiteLeft (B : Finset G) (g : G) : Equiv.Perm B := by
  classical
  exact (partialLeft B g).extendSubtype

lemma finiteLeft_apply (B : Finset G) (g : G) (x : B) (hx : g*(x:G) ∈ B) :
    (finiteLeft B g x : G)=g*(x:G) := by
  classical
  rw [finiteLeft,Equiv.extendSubtype_apply_of_mem _ x hx]
  rfl

lemma finiteLeft_inv_apply (B : Finset G) (g : G) (x : B) (hx : g⁻¹*(x:G) ∈ B) :
    ((finiteLeft B g)⁻¹ x : G)=g⁻¹*(x:G) := by
  let y : B := ⟨g⁻¹*(x:G),hx⟩
  have hy : finiteLeft B g y=x := by
    apply Subtype.ext
    rw [finiteLeft_apply _ _ y (by simp [y])]
    simp [y]
  calc
    ((finiteLeft B g)⁻¹ x : G) = ((finiteLeft B g)⁻¹ (finiteLeft B g y) : G) := by rw [hy]
    _ = (y:G) := by simp
    _ = _ := rfl

universe u
variable {A : Type u}
lemma mk_cons (a : A × Bool) (l : List (A × Bool)) :
    FreeGroup.mk (a::l)=(if a.2 then FreeGroup.of a.1 else (FreeGroup.of a.1)⁻¹)*FreeGroup.mk l := by
  have hh := FreeGroup.lift_mk (f:=FreeGroup.of) (L:=a::l)
  simp only [FreeGroup.lift_of_apply,List.map_cons,List.prod_cons,
    ←FreeGroup.lift_mk,FreeGroup.lift_of_apply] at hh
  cases ha : a.2 <;> simpa only [ha,Bool.cond_false,Bool.cond_true,Bool.false_eq_true,ite_false,ite_true] using hh

lemma finiteLeft_word (B : Finset (FreeGroup A)) (h1 : (1:FreeGroup A) ∈ B)
    (l : List (A × Bool)) (hl : ∀ k ∈ l.tails, FreeGroup.mk k ∈ B) :
    (FreeGroup.lift (fun a => finiteLeft B (FreeGroup.of a)) (FreeGroup.mk l) ⟨1,h1⟩ : FreeGroup A)=FreeGroup.mk l := by
  induction l with
  | nil => simp only [←FreeGroup.one_eq_mk]; rfl
  | cons a l ih =>
    have hl' : ∀ k ∈ l.tails, FreeGroup.mk k ∈ B := by
      intro k hk; exact hl k (by simp only [List.tails_cons,List.mem_cons]; exact Or.inr hk)
    have hm : FreeGroup.mk (a::l) ∈ B := hl _ (by simp)
    rw [mk_cons,_root_.map_mul,Equiv.Perm.mul_apply]
    split_ifs with ha
    · rw [FreeGroup.lift_apply_of]
      rw [finiteLeft_apply]
      · rw [ih hl']
      · simpa only [ih hl',mk_cons,ite_eq_left ha] using hm
    · rw [_root_.map_inv,FreeGroup.lift_apply_of]
      rw [finiteLeft_inv_apply]
      · rw [ih hl']
      · simpa only [ih hl',mk_cons,ite_eq_right ha] using hm

theorem exists_finite_separation (S : Finset (FreeGroup A)) :
    ∃ (H : Type u) (_ : Group H) (_ : Fintype H) (π : FreeGroup A →* H),
      ∀ g ∈ S, g ≠ 1 → π g ≠ 1 := by
  classical
  let B : Finset (FreeGroup A) := insert 1 (S.biUnion (fun g => g.toWord.tails.toFinset.image FreeGroup.mk))
  have h1 : (1:FreeGroup A) ∈ B := Finset.mem_insert_self _ _
  let π : FreeGroup A →* Equiv.Perm B := FreeGroup.lift (fun a => finiteLeft B (FreeGroup.of a))
  refine ⟨Equiv.Perm B,inferInstance,inferInstance,π,?_⟩
  intro g hg hg1 hπ
  have hh := finiteLeft_word B h1 g.toWord (by
    intro k hk
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    exact ⟨g,hg,Finset.mem_image.mpr ⟨k,List.mem_toFinset.mpr hk,rfl⟩⟩)
  rw [FreeGroup.mk_toWord] at hh
  change (π g ⟨1,h1⟩ : FreeGroup A)=g at hh
  rw [hπ] at hh
  exact hg1 hh.symm
end PopaFinite
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
open PopaMatrices
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {n : ℕ} {p : M} (s : System n p)

def permValue (σ : Equiv.Perm (Fin n)) : M := ∑ i, s.entry (σ i) i

omit [PartialOrder M] [StarOrderedRing M] in
lemma permValue_one : permValue s 1=p := by
  exact s.sum_diag

omit [PartialOrder M] [StarOrderedRing M] in
lemma permValue_mul (σ ρ : Equiv.Perm (Fin n)) :
    permValue s (σ*ρ)=permValue s σ*permValue s ρ := by
  classical
  simp [permValue,Finset.sum_mul,Finset.mul_sum,s.mul_entry,Equiv.Perm.mul_apply]

omit [PartialOrder M] [StarOrderedRing M] in
lemma permValue_inv (σ : Equiv.Perm (Fin n)) :
    permValue s σ⁻¹=star (permValue s σ) := by
  classical
  simp only [permValue,star_sum,s.star_entry]
  have hh := Equiv.sum_comp σ (fun i => s.entry (σ⁻¹ i) i)
  simpa using hh.symm

def matrixRep {G : Type*} [Group G] (π : G →* Equiv.Perm (Fin n)) : Rep G M where
  val g := permValue s (π g)
  mul g h := by rw [map_mul,permValue_mul]
  inv g := by rw [map_inv,permValue_inv]

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma matrixRep_support {G : Type*} [Group G] (π : G →* Equiv.Perm (Fin n)) :
    (matrixRep s π).support=p := by
  change permValue s (π 1)=p
  rw [map_one,permValue_one]

universe u v
variable {A : Type u}

def regularPerm {H : Type u} [Group H] [Fintype H] (π : FreeGroup A →* H) :
    FreeGroup A →* Equiv.Perm (Fin (Fintype.card H)) where
  toFun g := (Fintype.equivFin H).symm.trans ((Equiv.mulLeft (π g)).trans (Fintype.equivFin H))
  map_one' := by ext i; simp
  map_mul' g h := by ext i; simp

lemma regularPerm_ne {H : Type u} [Group H] [Fintype H] (π : FreeGroup A →* H)
    (g : FreeGroup A) (hg : π g ≠ 1) (i : Fin (Fintype.card H)) : regularPerm π g i ≠ i := by
  intro hh
  have he := congrArg (Fintype.equivFin H).symm hh
  change (Fintype.equivFin H).symm ((Fintype.equivFin H) (π g*((Fintype.equivFin H).symm i)))=_ at he
  rw [Equiv.symm_apply_apply] at he
  exact hg ((mul_eq_right).mp he)
end PopaPatching
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open PopaMatrices PopaCorners.CornerIso PopaPatching
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaTypeII
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
lemma off_diagonal_average {n : ℕ} {p : M} (s : System n p)
    {i j : Fin n} (hij : i ≠ j) : average e τ hτ htr hfaith (s.entry i j)=0 := by
  have hh := average_trace e τ hτ htr hfaith h1 (s.entry i i) (s.entry i j)
  simp only [s.mul_entry,ite_eq_right (Ne.symm hij)] at hh
  change average e τ hτ htr hfaith (s.entry i j)=average e τ hτ htr hfaith 0 at hh
  have hz : average e τ hτ htr hfaith (0:M)=0 := map_zero (expectation e τ hτ htr hfaith h1)
  exact hh.trans hz

include h1 in
theorem finite_corner_rep {A : Type*} (hII : PopaTypeII.NoAbelianCorners M)
    {p : M} (hp : IsStarProjection p) (hEp : Homogeneous e τ hτ htr hfaith p) (S : Finset (FreeGroup A)) :
    ∃ w : Rep (FreeGroup A) M, w.support=p ∧
      ∀ g ∈ S, g ≠ 1 → average e τ hτ htr hfaith (w g)=0 := by
  classical
  obtain ⟨H,hG,hF,π,hπ⟩ := PopaFinite.exists_finite_separation S
  let := hG
  let := hF
  obtain ⟨s⟩ := exists_homogeneous_system e τ hτ htr hfaith h1 hII (Fintype.card H) Fintype.card_pos hp hEp
  refine ⟨matrixRep s (regularPerm π),matrixRep_support s _,fun g hg hg1 => ?_⟩
  change expectation e τ hτ htr hfaith h1 (∑ i, s.entry (regularPerm π g i) i)=0
  rw [map_sum]
  exact Finset.sum_eq_zero (fun i _ => off_diagonal_average e τ hτ htr hfaith h1 s (regularPerm_ne π g (hπ g hg hg1) i))
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaPatching.Rep
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaCorners
variable {G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
@[ext] lemma ext {v w : Rep G M} (h : ∀ g, v g=w g) : v=w := by
  cases v; cases w; simp_all [Rep.mk.injEq,funext_iff]

instance : PartialOrder (Rep G M) where
  le v w := v.support ≤ w.support ∧ ∀ g, w g*v.support=v g
  le_refl v := ⟨le_rfl,v.mul_support⟩
  le_trans v w z hvw hwz := by
    refine ⟨hvw.1.trans hwz.1,fun g => ?_⟩
    have hp := (v.support_projection.le_iff_mul_eq_right w.support_projection).mp hvw.1
    calc
      z g*v.support = z g*(w.support*v.support) := by rw [hp]
      _ = v g := by rw [←mul_assoc,hwz.2,hvw.2]
  le_antisymm v w hvw hwv := by
    apply ext; intro g
    have hp := le_antisymm hvw.1 hwv.1
    simpa only [hp,w.mul_support] using (hvw.2 g).symm

def toCorner (v : Rep G M) (g : G) : CornerIso (1:M) 1 where
  val := v g
  init_proj := by rw [v.star_mul_self]; exact v.support_projection
  absorb := by rw [v.star_mul_self,v.mul_support]
  init_le := by rw [v.star_mul_self]; exact v.support_projection.le_one
  final_le := by rw [v.mul_star_self]; exact v.support_projection.le_one

@[simp] lemma toCorner_val (v : Rep G M) (g : G) : (toCorner v g : M)=v g := rfl
@[simp] lemma toCorner_initial (v : Rep G M) (g : G) : (toCorner v g).initial=v.support :=
  v.star_mul_self g
lemma toCorner_mono (g : G) : Monotone (fun v : Rep G M => toCorner v g) := by
  intro v w h
  rw [CornerIso.le_def,toCorner_initial,toCorner_initial]
  exact ⟨h.1,h.2 g⟩

def rank (τ : M →ₚ[ℂ] ℂ) (v : Rep G M) : ℝ := (τ v.support).re

lemma le_of_comparable_rank_le (τ : M →ₚ[ℂ] ℂ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) {v w : Rep G M}
    (hc : v ≤ w ∨ w ≤ v) (ht : rank τ v ≤ rank τ w) : v ≤ w := by
  rcases hc with h|h
  · exact h
  · have he : v=w := by
      apply ext; intro g
      have hh := CornerIso.le_of_comparable_rank_le τ hfaith
        (Or.inr (toCorner_mono g h)) (show CornerIso.rank τ (toCorner v g) ≤
          CornerIso.rank τ (toCorner w g) by simpa only [CornerIso.rank,toCorner_initial,rank] using ht)
      have he := le_antisymm hh (toCorner_mono g h)
      exact congrArg CornerIso.val he
    exact he.le

section Dual
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e hτ htr hfaith in
lemma monotone_limit (v : ℕ → Rep G M) (hv : Monotone v) :
    ∃ w : Rep G M, (∀ g, GNSTendsto τ (fun n => v n g) atTop (w g)) ∧
      (∀ n, v n ≤ w) ∧ (∀ z, (∀ n, v n ≤ z) → w ≤ z) := by
  have hL := (HochschildSakai.abstract_multiplication_normal e).1
  have hex (g : G) := CornerIso.monotone_limit e τ hτ htr hfaith
    (IsStarProjection.one M) (IsStarProjection.one M) (fun n => toCorner (v n) g)
    ((toCorner_mono g).comp hv)
  choose w hwt hwn hwl using hex
  have hmul (g h : G) : (w (g*h):M)=(w g:M)*(w h:M) := by
    apply GNSTendsto.unique τ hfaith (hwt (g*h))
    simpa only [toCorner_val,←(v _).mul] using (hwt g).mul τ htr (hwt h) 1 (fun n => (v n).norm_le g)
  have hinv (g : G) : (w g⁻¹:M)=star (w g:M) := by
    apply GNSTendsto.unique τ hfaith (hwt g⁻¹)
    simpa only [toCorner_val,←(v _).inv] using (hwt g).star τ htr
  let W : Rep G M := ⟨fun g => (w g:M),hmul,hinv⟩
  have hW (g : G) : (w g).initial=W.support :=
    (W.star_mul_self g)
  refine ⟨W,hwt,?_,?_⟩
  · intro n
    refine ⟨?_,fun g => by simpa only [toCorner_initial,toCorner_val] using (hwn g n).2⟩
    have hh := (hwn 1 n).1
    simpa only [toCorner_initial,hW] using hh
  · intro z hz
    have hh (g : G) := hwl g (toCorner z g) (fun n => toCorner_mono g (hz n))
    refine ⟨?_,fun g => ?_⟩
    · simpa only [hW,toCorner_initial] using (hh 1).1
    · simpa only [hW,toCorner_val] using (hh g).2

include e hτ hfaith in
lemma rank_tendsto {v : ℕ → Rep G M} {w : Rep G M}
    (ht : ∀ g, GNSTendsto τ (fun n => v n g) atTop (w g)) :
    Tendsto (fun n => rank τ (v n)) atTop (𝓝 (rank τ w)) := by
  have hL := (HochschildSakai.abstract_multiplication_normal e).1
  exact Complex.continuous_re.tendsto _ |>.comp
    (trace_predual_tendsto e τ hτ (predual_tendsto_of_preGNS e τ hL hτ hfaith 1
      (fun n => (v n).norm_le 1) (ht 1)))

include e hτ htr hfaith in

lemma exists_maximal_closed (P : Rep G M → Prop) (hzero : P Rep.zero)
    (hclosed : ∀ (v : ℕ → Rep G M) (w : Rep G M),
      (∀ n, P (v n)) → (∀ g, GNSTendsto τ (fun n => v n g) atTop (w g)) → P w) :
    ∃ v : Rep G M, P v ∧ ∀ w : Rep G M, P w → v ≤ w → w ≤ v := by
  classical
  have hu (c : Set (Rep G M)) (hc : c ⊆ {v | P v})
      (hchain : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
      ∃ w, P w ∧ ∀ v ∈ c, v ≤ w := by
    let T : Set ℝ := rank τ '' c
    have hTne : T.Nonempty := Set.Nonempty.image _ hne
    have hTbd : BddAbove T := by
      refine ⟨(τ 1).re,?_⟩
      rintro _ ⟨v,hv,rfl⟩
      exact Complex.re_le_re (τ.monotone v.support_projection.le_one)
    obtain ⟨t,htm,_htL,htt,htc⟩ := (isLUB_csSup hTne hTbd).exists_seq_monotone_tendsto hTne
    choose a ha hat using htc
    change ∀ n, rank τ (a n)=t n at hat
    have ham : Monotone a := by
      intro m n hmn
      apply le_of_comparable_rank_le τ hfaith (hchain.total (ha m) (ha n))
      rw [hat,hat]; exact htm hmn
    obtain ⟨w,hwt,hwn,hwl⟩ := monotone_limit e τ hτ htr hfaith a ham
    have hwr : rank τ w=sSup T := by
      apply tendsto_nhds_unique (rank_tendsto e τ hτ hfaith hwt)
      simpa only [hat] using htt
    refine ⟨w,hclosed a w (fun n => hc (ha n)) hwt,fun v hv => ?_⟩
    by_cases hex : ∃ n, v ≤ a n
    · obtain ⟨n,hn⟩ := hex
      exact hn.trans (hwn n)
    · have haw : ∀ n, a n ≤ v := fun n =>
        (hchain.total (ha n) hv).resolve_right (fun h => hex ⟨n,h⟩)
      apply le_of_comparable_rank_le τ hfaith (Or.inr (hwl v haw))
      rw [hwr]
      exact le_csSup hTbd ⟨v,hv,rfl⟩
  obtain ⟨v,hv,hmax⟩ := zorn_le_nonempty₀ {v | P v}
    (fun c hc hchain y hy => hu c hc hchain ⟨y,hy⟩) Rep.zero hzero
  exact ⟨v,hmax.1,fun w hw hle => hmax.2 hw hle⟩
end Dual
end PopaPatching.Rep
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaPatching
open BoundedHochschild HochschildRigidity
variable {C B G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def letterDegree (γ : B → G) : Letter C B → G := Sum.elim (fun _ => 1) γ

def degree (γ : B → G) (l : List (Letter C B)) : G := (l.map (letterDegree γ)).prod

@[simp] lemma degree_nil (γ : B → G) : degree (C:=C) γ []=1 := rfl
@[simp] lemma degree_cons (γ : B → G) (x : Letter C B) (l) :
    degree γ (x::l)=letterDegree γ x*degree γ l := rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma letter_norm_le (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (v : Rep G M) (x) :
    ‖letterValue a γ v x‖≤1 := by
  cases x with
  | inl c => exact ha c
  | inr b => exact v.norm_le (γ b)

omit [PartialOrder M] [StarOrderedRing M] in
lemma evaluate_norm_le (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (v : Rep G M) (l) :
    ‖evaluate a γ v l‖≤1 := by
  induction l with
  | nil => exact (IsStarProjection.one M).norm_le
  | cons x l ih =>
    calc
      ‖evaluate a γ v (x::l)‖ ≤ ‖letterValue a γ v x‖ * ‖evaluate a γ v l‖ := norm_mul_le _ _
      _ ≤ 1 * ‖evaluate a γ v l‖ :=
        mul_le_mul_of_nonneg_right (letter_norm_le a ha γ v x) (norm_nonneg _)
      _ ≤ 1 := by simpa only [one_mul] using ih

lemma degree_append (γ : B → G) (l k : List (Letter C B)) : degree γ (l++k)=degree γ l*degree γ k := by
  simp only [degree,List.map_append,List.prod_append]
omit [PartialOrder M] [StarOrderedRing M] in
lemma evaluate_append (a : C → M) (γ : B → G) (v : Rep G M) (l k) :
    evaluate a γ v (l++k)=evaluate a γ v l*evaluate a γ v k := by
  simp only [evaluate,List.map_append,List.prod_append]

omit [PartialOrder M] [StarOrderedRing M] in
lemma evaluate_zero_of_degree_ne_one (a : C → M) (γ : B → G) (l : List (Letter C B))
    (hl : degree γ l ≠ 1) : evaluate a γ Rep.zero l=0 := by
  induction l with
  | nil => exact False.elim (hl rfl)
  | cons x l ih =>
    cases x with
    | inl c =>
      have hh : degree γ l ≠ 1 := by simpa only [degree_cons,letterDegree,Sum.elim_inl,one_mul] using hl
      change a c*evaluate a γ Rep.zero l=0
      rw [ih hh,mul_zero]
    | inr b => exact zero_mul _

section Dual
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include htr in
lemma evaluate_tendsto (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G)
    {v : ℕ → Rep G M} {w : Rep G M}
    (ht : ∀ g, GNSTendsto τ (fun n => v n g) atTop (w g)) (l) :
    GNSTendsto τ (fun n => evaluate a γ (v n) l) atTop (evaluate a γ w l) := by
  induction l with
  | nil => exact GNSTendsto.const τ 1 atTop
  | cons x l ih =>
    have hx : GNSTendsto τ (fun n => letterValue a γ (v n) x) atTop (letterValue a γ w x) := by
      cases x with
      | inl c => exact GNSTendsto.const τ (a c) atTop
      | inr b => exact ht (γ b)
    exact hx.mul τ htr ih 1 (fun n => letter_norm_le a ha γ (v n) x)

end Dual
end PopaPatching

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaPatching
universe u
variable {C B G : Type*} [Group G]
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

def Good (a : C → M) (γ : B → G) (L : ℕ) (ε : ℕ → ℝ) (v : PopaPatching.Rep G M) : Prop :=
  Homogeneous e τ hτ htr hfaith v.support ∧
  ∀ l : List (Letter C B), l.length ≤ L → degree γ l ≠ 1 →
    ‖τ.toPreGNS (average e τ hτ htr hfaith (evaluate a γ v l))‖ ≤ ε l.length*Rep.rank τ v

include h1 in
lemma good_zero (a : C → M) (γ : B → G) (L : ℕ) (ε : ℕ → ℝ) :
    Good e τ hτ htr hfaith a γ L ε Rep.zero := by
  refine ⟨homogeneous_zero e τ hτ htr hfaith h1,fun l hl hd => ?_⟩
  rw [evaluate_zero_of_degree_ne_one a γ l hd]
  change ‖τ.toPreGNS (expectation e τ hτ htr hfaith h1 0)‖≤_
  rw [map_zero,map_zero,norm_zero]
  simp only [Rep.rank,Rep.support,Rep.zero,map_zero,Complex.zero_re,mul_zero,le_refl]

include h1 in
lemma good_closed (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (L : ℕ) (ε : ℕ → ℝ)
    (v : ℕ → Rep G M) (w : Rep G M) (hv : ∀ n, Good e τ hτ htr hfaith a γ L ε (v n))
    (ht : ∀ g, GNSTendsto τ (fun n => v n g) atTop (w g)) : Good e τ hτ htr hfaith a γ L ε w := by
  refine ⟨homogeneous_limit e τ hτ htr hfaith h1 (fun n => (hv n).1) (ht 1) 1
    (fun n => (v n).norm_le 1),fun l hl hd => ?_⟩
  have hrt := Rep.rank_tendsto e τ hτ hfaith ht
  have hvt := average_gns_tendsto e τ hτ htr hfaith h1 (evaluate_tendsto τ htr a ha γ ht l)
  have htn : Tendsto (fun n => τ.toPreGNS (average e τ hτ htr hfaith (evaluate a γ (v n) l)))
      atTop (𝓝 (τ.toPreGNS (average e τ hτ htr hfaith (evaluate a γ w l)))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [GNSTendsto,←map_sub] using hvt
  exact le_of_tendsto_of_tendsto htn.norm (tendsto_const_nhds.mul hrt)
    (Filter.Eventually.of_forall (fun n => (hv n).2 l hl hd))

include h1 in
lemma maximal_good (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (L : ℕ) (ε : ℕ → ℝ) :
    ∃ v : Rep G M, Good e τ hτ htr hfaith a γ L ε v ∧
      ∀ w, Good e τ hτ htr hfaith a γ L ε w → v ≤ w → w ≤ v :=
  Rep.exists_maximal_closed e τ hτ htr hfaith (Good e τ hτ htr hfaith a γ L ε)
    (good_zero e τ hτ htr hfaith h1 a γ L ε) (good_closed e τ hτ htr hfaith h1 a ha γ L ε)
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

lemma norm_sq_eq_trace (a : M) : ‖τ.toPreGNS a‖^2=(τ (star a*a)).re := by
  simpa only [PositiveLinearMap.ofPreGNS_toPreGNS,← Complex.ofReal_pow,Complex.ofReal_re]
    using congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS a))
end PopaMatrices.System
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

lemma trace_faithful (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) :
    ∀ a : algebra hp, trace hp τ (star a*a)=0 → a=0 := by
  intro a ha
  by_cases hp0 : p=0
  · apply Subtype.ext
    change (a:M)=0
    have hh := a.property.1
    simpa only [hp0,zero_mul] using hh.symm
  · have ht : 0 < (τ p).re := projection_trace_pos τ hfaith hp hp0
    apply Subtype.ext
    apply hfaith
    change (((τ p).re⁻¹ : ℝ) : ℂ)*τ (star (a:M)*(a:M))=0 at ha
    exact (mul_eq_zero.mp ha).resolve_left (by exact_mod_cast inv_ne_zero ht.ne')

lemma trace_tracial (htr : ∀ a b : M, τ (a*b)=τ (b*a)) :
    ∀ a b : algebra hp, trace hp τ (a*b)=trace hp τ (b*a) := by
  intro a b
  exact congrArg (fun z => (((τ p).re⁻¹ : ℝ) : ℂ)*z) (htr a.val b.val)

lemma trace_one (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hp0 : p ≠ 0) :
    trace hp τ 1=1 := by
  rw [trace_apply,coe_one]
  have ht : 0 < (τ p).re := projection_trace_pos τ hfaith hp hp0
  have hi := (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).2
  have he : τ p=((τ p).re : ℂ) := by apply Complex.ext <;> simp [hi]
  conv_lhs => rhs; rw [he]
  rw [←Complex.ofReal_mul,inv_mul_cancel₀ ht.ne',Complex.ofReal_one]

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
lemma trace_normal (hτ : TraceInPredual e τ) :
    TraceInPredual (predualEquiv e hp) (trace hp τ) := by
  obtain ⟨z,hz⟩ := hτ
  refine ⟨(((τ p).re⁻¹ : ℝ) : ℂ) • (Submodule.Quotient.mk z),fun a => ?_⟩
  rw [map_smul,predualEquiv_symm_apply_mk,trace_apply,hz a.val]
  simp [smul_eq_mul]

end PopaCorner

open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaMatrices
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {p : M} (hp : IsStarProjection p)

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

end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorner
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

def cornerAverage {p : M} (hp : IsStarProjection p) (a : algebra hp) : algebra hp :=
  average (predualEquiv e hp) (trace hp τ) (trace_normal hp τ e hτ)
    (trace_tracial hp τ htr) (trace_faithful hp τ hfaith) a

lemma cornerAverage_central {p : M} (hp : IsStarProjection p) (a : algebra hp) :
    Central (cornerAverage e τ hτ htr hfaith hp a) :=
  average_central _ _ _ _ _ _

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_corner {p : M} (hp : IsStarProjection p) {z : M} (hz : Central z) :
    Central (centerCompression hp ⟨z,hz⟩) := by
  intro x
  apply Subtype.ext
  change (z*p)*(x:M)=(x:M)*(z*p)
  calc
    (z*p)*(x:M)=z*(x:M) := by rw [mul_assoc,x.property.1]
    _=(x:M)*z := (hz (x:M)).eq
    _=(x:M)*(z*p) := by rw [(hz p).eq,←mul_assoc,x.property.2]

include h1 in
lemma average_cornerAverage {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (a : algebra hp) :
    average e τ hτ htr hfaith (cornerAverage e τ hτ htr hfaith hp a : M)=
      average e τ hτ htr hfaith (a:M) := by
  apply average_eq e τ hτ htr hfaith h1
  · exact average_central e τ hτ htr hfaith _
  · intro z hz
    rw [average_pair e τ hτ htr hfaith h1 hz]
    have hh := average_pair (predualEquiv e hp) (trace hp τ) (trace_normal hp τ e hτ)
      (trace_tracial hp τ htr) (trace_faithful hp τ hfaith) (trace_one hp τ hfaith hp0)
      (central_corner hp hz) a
    have hzmul (b : algebra hp) : ((centerCompression hp ⟨z,hz⟩*b : algebra hp):M)=z*(b:M) := by
      change (z*p)*(b:M)=z*(b:M)
      rw [mul_assoc,b.property.1]
    simp only [trace_apply,hzmul] at hh
    have ht : (((τ p).re⁻¹:ℝ):ℂ) ≠ 0 := by
      exact_mod_cast inv_ne_zero (HochschildDiffuse.projection_trace_pos τ hfaith hp hp0).ne'
    exact (mul_left_cancel₀ ht hh).symm

include h1 in
lemma cornerAverage_lift (hII : PopaTypeII.NoAbelianCorners M) {p : M}
    (hp : IsStarProjection p) (hp0 : p ≠ 0) {t : ℝ} (ht : 0<t)
    (hEp : average e τ hτ htr hfaith p=t • (1:M)) (a : algebra hp) :
    ∃ c : M, Central c ∧ c*p=(cornerAverage e τ hτ htr hfaith hp a:M) ∧
      ‖c‖≤‖a‖ ∧ average e τ hτ htr hfaith (a:M)=t • c := by
  obtain ⟨c,hc,hcp,hcn⟩ := full_center_lift_norm e τ hτ htr hfaith h1 hII hp ht hEp
    (cornerAverage e τ hτ htr hfaith hp a) (cornerAverage_central e τ hτ htr hfaith hp a)
  refine ⟨c,hc,hcp,?_,?_⟩
  · rw [hcn]
    exact average_norm _ _ _ _ _ a
  · rw [←average_cornerAverage e τ hτ htr hfaith h1 hp hp0 a,←hcp,
      average_bimodule e τ hτ htr hfaith h1 hc,hEp,mul_smul_comm,mul_one]
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end PopaMatrices

open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end PopaMatrices

open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

lemma norm_sq_trace_corner {p : M} (hp : IsStarProjection p) (a : algebra hp) :
    ‖(trace hp τ).toPreGNS a‖^2=(τ p).re⁻¹*‖τ.toPreGNS (a:M)‖^2 := by
  rw [PopaMatrices.System.norm_sq_eq_trace,PopaMatrices.System.norm_sq_eq_trace,trace_apply]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rfl

end PopaCorner

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorner
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

lemma cornerCoefficient_central {p : M} (hp : IsStarProjection p) (a : M) :
    Central (cornerCoefficient e τ hτ htr hfaith hp a) := fun x =>
  (average_central e τ hτ htr hfaith _ x).smul_left _

include h1 in
lemma cornerCoefficient_spec (hII : PopaTypeII.NoAbelianCorners M) {p : M}
    (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (hEp : average e τ hτ htr hfaith p=(τ p).re • (1:M)) (a : M) :
    cornerCoefficient e τ hτ htr hfaith hp a*p=
        (cornerAverage e τ hτ htr hfaith hp (compress hp a):M) ∧
      ‖cornerCoefficient e τ hτ htr hfaith hp a‖≤‖a‖ := by
  have ht := HochschildDiffuse.projection_trace_pos τ hfaith hp hp0
  obtain ⟨c,hc,hcp,hcn,hce⟩ := cornerAverage_lift e τ hτ htr hfaith h1 hII hp hp0 ht hEp (compress hp a)
  have he : cornerCoefficient e τ hτ htr hfaith hp a=c := by
    change (τ p).re⁻¹ • average e τ hτ htr hfaith ((compress hp a):M)=c
    rw [hce,smul_smul,inv_mul_cancel₀ ht.ne',one_smul]
  rw [he]
  exact ⟨hcp,hcn.trans (compress_norm_le hp a)⟩

end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorner
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
lemma central_supported_norm_sq {q : M} (hq : IsStarProjection q)
    {t : ℝ} (hEq : average e τ hτ htr hfaith q=t • (1:M)) {z : M} (hz : Central z) :
    ‖τ.toPreGNS (q*z)‖^2=t*‖τ.toPreGNS z‖^2 := by
  have he : star (q*z)*(q*z)=(star z*z)*q := by
    rw [star_mul,hq.isSelfAdjoint.star_eq,mul_assoc,←mul_assoc q,hq.isIdempotentElem.eq,
      ←(hz q).eq,←mul_assoc]
  rw [PopaMatrices.System.norm_sq_eq_trace,he,
    ←average_pair e τ hτ htr hfaith h1 (central_mul (central_star hz) hz),hEq,
    mul_smul_comm,mul_one,τ.map_smul_of_tower]
  rw [PopaMatrices.System.norm_sq_eq_trace]
  simp only [Complex.smul_re,smul_eq_mul]

include h1 in
lemma average_supported_norm_sq {q : M} (hq : IsStarProjection q)
    {t : ℝ} (ht : 0≤t) (hEq : average e τ hτ htr hfaith q=t • (1:M))
    {a : M} (ha : q*a=a) :
    ‖τ.toPreGNS (average e τ hτ htr hfaith a)‖^2 ≤ t*‖τ.toPreGNS a‖^2 := by
  let z := average e τ hτ htr hfaith a
  have hz : Central z := average_central e τ hτ htr hfaith a
  have hsq := central_supported_norm_sq e τ hτ htr hfaith h1 hq hEq hz
  have hi : inner ℂ (τ.toPreGNS (q*z)) (τ.toPreGNS a)=
      inner ℂ (τ.toPreGNS z) (τ.toPreGNS z) := by
    simp only [PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.ofPreGNS_toPreGNS,star_mul,hq.isSelfAdjoint.star_eq,mul_assoc,ha]
    exact (average_pair e τ hτ htr hfaith h1 (central_star hz) a).symm
  have hcs := norm_inner_le_norm (𝕜:=ℂ) (τ.toPreGNS (q*z)) (τ.toPreGNS a)
  rw [hi,inner_self_eq_norm_sq_to_K] at hcs
  simp only [norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg _)] at hcs
  have hcs2 := mul_self_le_mul_self (sq_nonneg _) hcs
  have hnon : 0≤t*‖τ.toPreGNS a‖^2 := mul_nonneg ht (sq_nonneg _)
  change ‖τ.toPreGNS z‖^2 ≤ _
  by_cases hz0 : ‖τ.toPreGNS z‖=0
  · simpa only [hz0,zero_pow (by omega : (2:ℕ) ≠ 0)] using hnon
  · have hzpos : 0<‖τ.toPreGNS z‖^2 := sq_pos_of_ne_zero hz0
    apply le_of_mul_le_mul_left (a:=‖τ.toPreGNS z‖^2) ?_ hzpos
    calc
      _ ≤ ‖τ.toPreGNS (q*z)‖^2*‖τ.toPreGNS a‖^2 := by nlinarith [hcs2]
      _ = _ := by rw [hsq]; ring

include h1 in
lemma average_corner_error {q : M} (hq : IsStarProjection q) (hq0 : q ≠ 0)
    (hEq : average e τ hτ htr hfaith q=(τ q).re • (1:M))
    (a : algebra hq) {θ : ℝ} (hθ : 0≤θ)
    (ha : ‖(trace hq τ).toPreGNS a‖≤θ) :
    ‖τ.toPreGNS (average e τ hτ htr hfaith (a:M))‖≤(τ q).re*θ := by
  have ht := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
  have hsq := average_supported_norm_sq e τ hτ htr hfaith h1 hq ht.le hEq a.property.1
  have hnorm := norm_sq_trace_corner τ hq a
  have ha2 := mul_self_le_mul_self (norm_nonneg _) ha
  have ht0 := ht.ne'
  have he : ‖τ.toPreGNS (a:M)‖^2=(τ q).re*‖(trace hq τ).toPreGNS a‖^2 := by
    rw [hnorm,←mul_assoc,mul_inv_cancel₀ ht0,one_mul]
  rw [he] at hsq
  have hh := mul_le_mul_of_nonneg_left ha2 (sq_nonneg (τ q).re)
  nlinarith [norm_nonneg (τ.toPreGNS (average e τ hτ htr hfaith (a:M))),mul_nonneg ht.le hθ]
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
open BoundedHochschild HochschildRigidity
variable {G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

namespace Rep

def inCorner (v : Rep G M) {p : M} (hp : IsStarProjection p) (hv : v.support=p) :
    G →* PopaCorner.algebra hp where
  toFun g := ⟨v g,by
    change p*v g=v g ∧ v g*p=v g
    rw [←hv]
    exact ⟨v.support_mul g,v.mul_support g⟩⟩
  map_one' := Subtype.ext hv
  map_mul' g h := Subtype.ext (v.mul g h)

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma inCorner_coe (v : Rep G M) {p : M} (hp : IsStarProjection p) (hv) (g) :
    ((inCorner v hp hv g : PopaCorner.algebra hp):M)=v g := rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma inCorner_norm_le (v : Rep G M) {p : M} (hp : IsStarProjection p) (hv) (g) :
    ‖inCorner v hp hv g‖≤1 := v.norm_le g
end Rep

variable {K : Type*}
omit [PartialOrder M] [StarOrderedRing M] in
lemma prod_norm_le (l : List K) (A : K → M) (hA : ∀ i ∈ l, ‖A i‖≤1) :
    ‖(l.map A).prod‖≤1 := by
  induction l with
  | nil => exact (IsStarProjection.one M).norm_le
  | cons i l ih =>
    exact (norm_mul_le _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (hA i (by simp))).trans
        (ih (fun j hj => hA j (by simp [hj]))))

lemma prod_gns_sub_le (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (l : List K) (A B : K → M) (hA : ∀ i ∈ l, ‖A i‖≤1) (hB : ∀ i ∈ l, ‖B i‖≤1) :
    ‖τ.toPreGNS ((l.map A).prod-(l.map B).prod)‖≤
      (l.map (fun i => ‖τ.toPreGNS (A i-B i)‖)).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hA' := fun j hj => hA j (List.mem_cons_of_mem i hj)
    have hB' := fun j hj => hB j (List.mem_cons_of_mem i hj)
    have hh := ih hA' hB'
    have he : A i*(l.map A).prod-B i*(l.map B).prod=
        A i*((l.map A).prod-(l.map B).prod)+(A i-B i)*(l.map B).prod := by noncomm_ring
    simp only [List.map_cons,List.prod_cons,List.sum_cons]
    rw [he,map_add]
    calc
      _ ≤ ‖τ.toPreGNS (A i*((l.map A).prod-(l.map B).prod))‖+
          ‖τ.toPreGNS ((A i-B i)*(l.map B).prod)‖ := norm_add_le _ _
      _ ≤ ‖τ.toPreGNS ((l.map A).prod-(l.map B).prod)‖+
          ‖τ.toPreGNS (A i-B i)‖ := by
        apply add_le_add
        · exact (preGNS_norm_mul_le τ _ _).trans
            (mul_le_of_le_one_left (norm_nonneg _) (hA i (by simp)))
        · exact (preGNS_norm_mul_right_le τ htr _ _).trans
            (mul_le_of_le_one_left (norm_nonneg _) (prod_norm_le l B hB'))
      _ ≤ _ := by linarith

lemma prod_gns_sub_uniform (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (l : List K) (A B : K → M) (hA : ∀ i ∈ l, ‖A i‖≤1) (hB : ∀ i ∈ l, ‖B i‖≤1)
    (θ : ℝ) (he : ∀ i ∈ l, ‖τ.toPreGNS (A i-B i)‖≤θ) :
    ‖τ.toPreGNS ((l.map A).prod-(l.map B).prod)‖≤(l.length:ℝ)*θ := by
  refine (prod_gns_sub_le τ htr l A B hA hB).trans ?_
  calc
    _ ≤ (l.map (fun _ => θ)).sum := List.sum_le_sum (fun i hi => he i hi)
    _ = _ := by simp

end PopaPatching

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorner PopaPatching
variable {G M K : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma cyclic_product_compress {N : Type*} (T : M → N) (hT : ∀ a b : M, T (a*b)=T (b*a))
    (w : Rep G M) {q : M} (hq : IsStarProjection q) (hw : w.support=q)
    (l : List K) (g : K → G) (Y : K → M) (hl : l ≠ []) :
    T ((l.map (fun j => w (g j)*Y j)).prod) =
      T (((l.map (fun j => w.inCorner hq hw (g j)*PopaCorner.compress hq (Y j))).prod :
        PopaCorner.algebra hq):M) := by
  have hleft (ls : List K) : q*((ls.map (fun j => w (g j)*Y j)).prod*q)=
      (ls.map (fun j => w (g j)*Y j)).prod*q := by
    cases ls with
    | nil => simpa using hq.isIdempotentElem.eq
    | cons j ls =>
      simp only [List.map_cons,List.prod_cons,←mul_assoc]
      rw [←hw,w.support_mul]
  have he (ls : List K) :
      (((ls.map (fun j => w.inCorner hq hw (g j)*PopaCorner.compress hq (Y j))).prod :
        PopaCorner.algebra hq):M) = (ls.map (fun j => w (g j)*Y j)).prod*q := by
    induction ls with
    | nil => simp
    | cons j ls ih =>
      change (w (g j)*(q*Y j*q))*
        (((ls.map (fun j => w.inCorner hq hw (g j)*PopaCorner.compress hq (Y j))).prod :
          PopaCorner.algebra hq):M) = (w (g j)*Y j)*(ls.map (fun j => w (g j)*Y j)).prod*q
      rw [ih]
      have hwq : w (g j)*q=w (g j) := by rw [←hw,w.mul_support]
      rw [←mul_assoc (w (g j)),←mul_assoc (w (g j)),hwq]
      rw [mul_assoc (w (g j)*Y j),hleft]
      simp only [mul_assoc]
  rw [he,hT _ q]
  cases l with
  | nil => exact False.elim (hl rfl)
  | cons j ls =>
    simp only [List.map_cons,List.prod_cons,←mul_assoc]
    rw [←hw,w.support_mul]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_list_prod (l : List K) (c : K → M) (hc : ∀ j, Central (c j)) :
    Central ((l.map c).prod) := by
  induction l with
  | nil => exact fun x => Commute.one_left _
  | cons j l ih => exact central_mul (hc j) ih

omit [PartialOrder M] [StarOrderedRing M] in
lemma compress_central {q : M} (hq : IsStarProjection q) {c : M} (hc : Central c) :
    ((compress hq c):M)=c*q := by
  change q*c*q=c*q
  rw [←(hc q).eq,mul_assoc,hq.isIdempotentElem.eq]

omit [PartialOrder M] [StarOrderedRing M] in
lemma central_product (w : Rep G M) {q : M} (hq : IsStarProjection q) (hw : w.support=q)
    (l : List K) (g : K → G) (c : K → M) (hc : ∀ j, Central (c j)) :
    (((l.map (fun j => w.inCorner hq hw (g j)*compress hq (c j))).prod : algebra hq):M)=
      (l.map c).prod*w ((l.map g).prod) := by
  induction l with
  | nil => simp [←hw,Rep.support]
  | cons j l ih =>
    change (w (g j)*((compress hq (c j)):M))*
      (((l.map (fun j => w.inCorner hq hw (g j)*compress hq (c j))).prod : algebra hq):M)=_
    have hterm : w (g j)*((compress hq (c j)):M)=c j*w (g j) := by
      rw [compress_central hq (hc j),←mul_assoc,←(hc j (w (g j))).eq,
        mul_assoc (c j) (w (g j)),←hw,w.mul_support]
    rw [hterm,ih]
    simp only [List.map_cons,List.prod_cons,w.mul]
    calc
      _ = c j*(w (g j)*(l.map c).prod)*w ((l.map g).prod) := by simp only [mul_assoc]
      _ = _ := by rw [←(central_list_prod l c hc (w (g j))).eq]; simp only [mul_assoc]

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
theorem block_average_error (w : Rep G M) {q : M} (hq : IsStarProjection q) (hq0 : q ≠ 0)
    (hw : w.support=q) (hEq : average e τ hτ htr hfaith q=(τ q).re • (1:M))
    (l : List K) (g : K → G) (Y c : K → M) (hcZ : ∀ j, Central (c j)) (hl : l ≠ [])
    (hY : ∀ j ∈ l, ‖Y j‖≤1) (hc : ∀ j ∈ l, ‖c j‖≤1)
    (θ : ℝ) (hθ : 0≤θ) (he : ∀ j ∈ l,
      ‖(trace hq τ).toPreGNS (compress hq (Y j)-compress hq (c j))‖≤θ) :
    ‖τ.toPreGNS (average e τ hτ htr hfaith ((l.map (fun j => w (g j)*Y j)).prod)-
      (l.map c).prod*average e τ hτ htr hfaith (w ((l.map g).prod)))‖≤(l.length:ℝ)*θ*(τ q).re := by
  let t := trace hq τ
  let A := fun j => w.inCorner hq hw (g j)*compress hq (Y j)
  let B := fun j => w.inCorner hq hw (g j)*compress hq (c j)
  have hA (j) (hj : j ∈ l) : ‖A j‖≤1 := (norm_mul_le _ _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (w.inCorner_norm_le hq hw _)).trans
      ((compress_norm_le hq _).trans (hY j hj)))
  have hB (j) (hj : j ∈ l) : ‖B j‖≤1 := (norm_mul_le _ _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (w.inCorner_norm_le hq hw _)).trans
      ((compress_norm_le hq _).trans (hc j hj)))
  have hE (j) (hj : j ∈ l) : ‖t.toPreGNS (A j-B j)‖≤θ := by
    change ‖t.toPreGNS (w.inCorner hq hw (g j)*compress hq (Y j)-
      w.inCorner hq hw (g j)*compress hq (c j))‖≤θ
    rw [←mul_sub]
    exact (preGNS_norm_mul_le t _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (w.inCorner_norm_le hq hw _)).trans (he j hj))
  have hh := average_corner_error e τ hτ htr hfaith h1 hq hq0 hEq
    ((l.map A).prod-(l.map B).prod) (mul_nonneg (Nat.cast_nonneg _) hθ)
    (prod_gns_sub_uniform t (trace_tracial hq τ htr) l A B hA hB θ hE)
  rw [cyclic_product_compress (average e τ hτ htr hfaith) (average_trace e τ hτ htr hfaith h1) w hq hw l g Y hl]
  have heq : average e τ hτ htr hfaith (((l.map A).prod-(l.map B).prod : algebra hq):M)=
      average e τ hτ htr hfaith (((l.map A).prod : algebra hq):M)-
      (l.map c).prod*average e τ hτ htr hfaith (w ((l.map g).prod)) := by
    change expectation e τ hτ htr hfaith h1 (_-_)=_
    rw [map_sub]
    change _-average e τ hτ htr hfaith (((l.map (fun j => w.inCorner hq hw (g j)*compress hq (c j))).prod : algebra hq):M)=_
    rw [central_product w hq hw l g c hcZ,average_bimodule e τ hτ htr hfaith h1 (central_list_prod l c hcZ)]
    rfl
  rw [heq] at hh
  exact hh.trans_eq (by ring)
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
universe u v
variable {A : Type u} [Fintype A]

def shortWords (A : Type u) [Fintype A] : ℕ → Finset (List A)
  | 0 => {[]}
  | n+1 => by
    classical
    exact insert [] (Finset.univ.biUnion (fun a => (shortWords A n).image (List.cons a)))

@[simp] theorem mem_shortWords (l : List A) (n : ℕ) : l ∈ shortWords A n ↔ l.length ≤ n := by
  classical
  induction n generalizing l with
  | zero => simp [shortWords]
  | succ n ih =>
    cases l with
    | nil => simp [shortWords]
    | cons a l => simp [shortWords,ih]
end PopaPatching
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
variable {C B G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

abbrev Mark (C B : Type*) := C ⊕ (B × Bool)
abbrev Block (C B : Type*) := B × List (Letter C B)
def oldMark : Letter C B → Mark C B := Sum.map id (fun b => (b,false))
def eraseMark : Mark C B → Letter C B := Sum.map id Prod.fst

def freshs (m : List (Mark C B)) : List B := m.filterMap (fun x =>
  match x with
  | .inl _ => none
  | .inr (b,t) => if t then some b else none)
def markedValue (a : C → M) (γ : B → G) (v w : Rep G M) : Mark C B → M :=
  Sum.elim a (fun bt => if bt.2 then w (γ bt.1) else v (γ bt.1))
def markedEval (a : C → M) (γ : B → G) (v w : Rep G M) (m : List (Mark C B)) : M :=
  (m.map (markedValue a γ v w)).prod

@[simp] lemma erase_old (x : Letter C B) : eraseMark (oldMark x)=x := by cases x <;> rfl
@[simp] lemma erase_old_list (l : List (Letter C B)) : (l.map oldMark).map eraseMark=l := by
  simpa only [List.map_map] using (show l.map (eraseMark ∘ oldMark)=l from by
    have he : eraseMark ∘ oldMark = (id : Letter C B → Letter C B) := funext erase_old
    rw [he,List.map_id])
@[simp] lemma freshs_old (l : List (Letter C B)) : freshs (l.map oldMark)=[] := by
  induction l with
  | nil => rfl
  | cons x l ih => cases x <;> simp [freshs,oldMark]
@[simp] lemma freshs_append (l k : List (Mark C B)) : freshs (l++k)=freshs l++freshs k :=
  List.filterMap_append
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma markedEval_old (a : C → M) (γ : B → G) (v w : Rep G M) (l : List (Letter C B)) :
    markedEval a γ v w (l.map oldMark)=evaluate a γ v l := by
  simp only [markedEval,evaluate,List.map_map]
  congr 2
  funext x; cases x <;> rfl
omit [PartialOrder M] [StarOrderedRing M] in
lemma markedEval_append (a : C → M) (γ : B → G) (v w : Rep G M) (l k : List (Mark C B)) :
    markedEval a γ v w (l++k)=markedEval a γ v w l*markedEval a γ v w k := by
  simp only [markedEval,List.map_append,List.prod_append]

def variants : List (Letter C B) → List (List (Mark C B))
  | [] => [[]]
  | .inl c :: l => (variants l).map (List.cons (.inl c))
  | .inr b :: l => (variants l).map (List.cons (.inr (b,false))) ++
      (variants l).map (List.cons (.inr (b,true)))

lemma erase_variant (l : List (Letter C B)) (m : List (Mark C B)) (hm : m ∈ variants l) :
    m.map eraseMark=l := by
  induction l generalizing m with
  | nil => simpa [variants] using hm
  | cons x l ih =>
    cases x with
    | inl c =>
      obtain ⟨m,hm0,rfl⟩ := List.mem_map.mp hm
      change Sum.inl c :: m.map eraseMark = Sum.inl c :: l
      rw [ih m hm0]
    | inr b =>
      rcases List.mem_append.mp hm with hm1|hm1
      · obtain ⟨m,hm0,rfl⟩ := List.mem_map.mp hm1
        change Sum.inr b :: m.map eraseMark = Sum.inr b :: l
        rw [ih m hm0]
      · obtain ⟨m,hm0,rfl⟩ := List.mem_map.mp hm1
        change Sum.inr b :: m.map eraseMark = Sum.inr b :: l
        rw [ih m hm0]

lemma variants_length_le (l : List (Letter C B)) : (variants l).length ≤ 2^l.length := by
  induction l with
  | nil => simp [variants]
  | cons x l ih =>
    cases x <;> simp only [variants,List.length_append,List.length_map,List.length_cons,pow_succ] <;> omega

omit [PartialOrder M] [StarOrderedRing M] in
lemma evaluate_add_expansion (a : C → M) (γ : B → G) (v w : Rep G M) (hw)
    (l : List (Letter C B)) :
    evaluate a γ (v.add w hw) l = ((variants l).map (markedEval a γ v w)).sum := by
  induction l with
  | nil => simp [variants,markedEval]
  | cons x l ih =>
    cases x with
    | inl c =>
      simp only [evaluate_cons,letterValue,Sum.elim_inl,variants,List.map_map]
      change a c*evaluate a γ (v.add w hw) l=
        ((variants l).map (fun m => a c*markedEval a γ v w m)).sum
      rw [ih,List.sum_map_mul_left]
    | inr b =>
      simp only [evaluate_cons,letterValue,Sum.elim_inr,Rep.add_apply,variants,
        List.map_append,List.sum_append,List.map_map]
      change (v (γ b)+w (γ b))*evaluate a γ (v.add w hw) l=
        ((variants l).map (fun m => v (γ b)*markedEval a γ v w m)).sum+
        ((variants l).map (fun m => w (γ b)*markedEval a γ v w m)).sum
      rw [ih,add_mul,List.sum_map_mul_left,List.sum_map_mul_left]

def splitMarked : List (Mark C B) → List (Letter C B) × List (Block C B)
  | [] => ([],[])
  | .inl c :: m => let (l,b) := splitMarked m; (.inl c::l,b)
  | .inr (c,false) :: m => let (l,b) := splitMarked m; (.inr c::l,b)
  | .inr (c,true) :: m => let (l,b) := splitMarked m; ([],(c,l)::b)

def flattenBlocks (b : List (Block C B)) : List (Mark C B) :=
  b.flatMap (fun j => .inr (j.1,true)::j.2.map oldMark)
def eraseBlocks (b : List (Block C B)) : List (Letter C B) :=
  b.flatMap (fun j => .inr j.1::j.2)

lemma splitMarked_spec (m : List (Mark C B)) :
    m=(splitMarked m).1.map oldMark++flattenBlocks (splitMarked m).2 := by
  induction m with
  | nil => rfl
  | cons x m ih =>
    cases x with
    | inl c => simpa [splitMarked,oldMark] using congrArg (List.cons (.inl c)) ih
    | inr bt =>
      rcases bt with ⟨b,t⟩
      cases t
      · simpa [splitMarked,oldMark] using congrArg (List.cons (.inr (b,false))) ih
      · simpa [splitMarked,flattenBlocks] using congrArg (List.cons (.inr (b,true))) ih

@[simp] lemma erase_flatten (b : List (Block C B)) :
    (flattenBlocks b).map eraseMark=eraseBlocks b := by
  induction b with
  | nil => rfl
  | cons j b ih =>
    change ((Sum.inr (j.1,true)::j.2.map oldMark)++flattenBlocks b).map eraseMark=
      (Sum.inr j.1::j.2)++eraseBlocks b
    rw [List.map_append,List.map_cons,erase_old_list,ih]
    rfl

@[simp] lemma freshs_flatten (b : List (Block C B)) : freshs (flattenBlocks b)=b.map Prod.fst := by
  induction b with
  | nil => rfl
  | cons j b ih =>
    simp only [flattenBlocks,List.flatMap_cons,freshs_append]
    change (j.1::freshs (j.2.map oldMark))++freshs (flattenBlocks b)=_
    rw [freshs_old,ih]
    rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma markedEval_flatten (a : C → M) (γ : B → G) (v w : Rep G M) (b : List (Block C B)) :
    markedEval a γ v w (flattenBlocks b)=(b.map (fun j => w (γ j.1)*evaluate a γ v j.2)).prod := by
  induction b with
  | nil => rfl
  | cons j b ih =>
    simp only [flattenBlocks,List.flatMap_cons,markedEval_append,List.map_cons,List.prod_cons]
    change (w (γ j.1)*markedEval a γ v w (j.2.map oldMark))*markedEval a γ v w (flattenBlocks b)= _
    rw [markedEval_old,ih]

def appendTail : List (Block C B) → List (Letter C B) → List (Block C B)
  | [], _ => []
  | [b], l => [(b.1,b.2++l)]
  | b::c::cs, l => b::appendTail (c::cs) l

lemma appendTail_spec (b : List (Block C B)) (l : List (Letter C B)) (hb : b ≠ []) :
    flattenBlocks (appendTail b l)=flattenBlocks b++l.map oldMark := by
  induction b with
  | nil => exact False.elim (hb rfl)
  | cons j b ih =>
    cases b with
    | nil => simp [appendTail,flattenBlocks]
    | cons k b =>
      change (Sum.inr (j.1,true)::j.2.map oldMark)++flattenBlocks (appendTail (k::b) l)=
        ((Sum.inr (j.1,true)::j.2.map oldMark)++flattenBlocks (k::b))++l.map oldMark
      rw [show flattenBlocks (appendTail (k::b) l)=flattenBlocks (k::b)++l.map oldMark from ih (by simp)]
      simp only [flattenBlocks,List.flatMap_cons,List.append_assoc]

lemma freshs_nonempty_split (m : List (Mark C B)) (hm : freshs m ≠ []) : (splitMarked m).2 ≠ [] := by
  intro h
  have hh := congrArg freshs (splitMarked_spec m)
  simp only [freshs_append,freshs_old,freshs_flatten,h,List.map_nil,List.nil_append] at hh
  exact hm hh

lemma degree_rotation_ne_one (γ : B → G) (a b : List (Letter C B))
    (h : degree γ (a++b) ≠ 1) : degree γ (b++a) ≠ 1 := by
  rw [degree_append] at h ⊢
  exact fun he => h (mul_eq_one_comm.mp he)

end PopaPatching

open scoped ComplexOrder
namespace PopaPatching
variable {C B G : Type*} [Group G]

def newVariants : List (Letter C B) → List (List (Mark C B))
  | [] => []
  | .inl c :: l => (newVariants l).map (List.cons (.inl c))
  | .inr b :: l => (newVariants l).map (List.cons (.inr (b,false))) ++
      (variants l).map (List.cons (.inr (b,true)))

lemma variants_eq (l : List (Letter C B)) : variants l=l.map oldMark::newVariants l := by
  induction l with
  | nil => rfl
  | cons x l ih => cases x <;> simp [variants,newVariants,ih,oldMark]

lemma mem_newVariants (l : List (Letter C B)) (m : List (Mark C B)) (hm : m ∈ newVariants l) :
    m ∈ variants l ∧ freshs m ≠ [] := by
  refine ⟨by rw [variants_eq]; exact List.mem_cons_of_mem _ hm,?_⟩
  induction l generalizing m with
  | nil => simp [newVariants] at hm
  | cons x l ih =>
    cases x with
    | inl c =>
      obtain ⟨m,hm0,rfl⟩ := List.mem_map.mp hm
      exact ih m hm0
    | inr b =>
      rcases List.mem_append.mp hm with hm1|hm1
      · obtain ⟨m,hm0,rfl⟩ := List.mem_map.mp hm1
        exact ih m hm0
      · obtain ⟨m,hm0,rfl⟩ := List.mem_map.mp hm1
        simp [freshs]

lemma newVariants_length_le (l : List (Letter C B)) : (newVariants l).length≤2^l.length := by
  have hh := variants_length_le l
  rw [variants_eq,List.length_cons] at hh
  omega

lemma eraseBlocks_append (b c : List (Block C B)) : eraseBlocks (b++c)=eraseBlocks b++eraseBlocks c :=
  List.flatMap_append

lemma blocks_length_le (b : List (Block C B)) : b.length ≤ (eraseBlocks b).length := by
  induction b with
  | nil => rfl
  | cons j b ih =>
    change (j::b).length ≤ ((Sum.inr j.1::j.2)++eraseBlocks b).length
    simp only [List.length_append,List.length_cons]
    omega

lemma segment_length_bound (b : List (Block C B)) (j : Block C B) (hj : j ∈ b) :
    j.2.length+b.length ≤ (eraseBlocks b).length := by
  obtain ⟨s,t,rfl⟩ := List.mem_iff_append.mp hj
  have hs := blocks_length_le s
  have ht := blocks_length_le t
  rw [eraseBlocks_append]
  change j.2.length+(s++j::t).length≤(eraseBlocks s++((Sum.inr j.1::j.2)++eraseBlocks t)).length
  simp only [List.length_append,List.length_cons]
  omega

lemma blocks_degree (γ : B → G) (b : List (Block C B))
    (hb : ∀ j ∈ b, degree γ j.2=1) : degree γ (eraseBlocks b)=(b.map (fun j => γ j.1)).prod := by
  induction b with
  | nil => rfl
  | cons j b ih =>
    change degree γ ((Sum.inr j.1::j.2)++eraseBlocks b)=_
    rw [degree_append,degree_cons,hb j (by simp)]
    change (γ j.1*1)*degree γ (eraseBlocks b)=γ j.1*(b.map (fun j => γ j.1)).prod
    rw [mul_one,ih (fun k hk => hb k (by simp [hk]))]

lemma exists_nontrivial_segment (γ : B → G) (b : List (Block C B))
    (hd : degree γ (eraseBlocks b) ≠ 1) (hg : (b.map (fun j => γ j.1)).prod=1) :
    ∃ j ∈ b, degree γ j.2 ≠ 1 := by
  by_contra hh
  push Not at hh
  exact hd ((blocks_degree γ b hh).trans hg)

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
omit [PartialOrder M] [StarOrderedRing M] in
lemma evaluate_blocks (a : C → M) (γ : B → G) (v : Rep G M) (b : List (Block C B)) :
    evaluate a γ v (eraseBlocks b)=(b.map (fun j => v (γ j.1)*evaluate a γ v j.2)).prod := by
  induction b with
  | nil => rfl
  | cons j b ih =>
    change evaluate a γ v ((Sum.inr j.1::j.2)++eraseBlocks b)=_
    rw [evaluate_append,evaluate_cons,ih]
    rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma evaluate_add_new_expansion (a : C → M) (γ : B → G) (v w : Rep G M) (hw)
    (l : List (Letter C B)) : evaluate a γ (v.add w hw) l=
      evaluate a γ v l+((newVariants l).map (markedEval a γ v w)).sum := by
  rw [evaluate_add_expansion,variants_eq,List.map_cons,List.sum_cons,markedEval_old]
end PopaPatching
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
variable {C B G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma rank_nonneg (τ : M →ₚ[ℂ] ℂ) (v : Rep G M) : 0≤Rep.rank τ v :=
  (Complex.nonneg_iff.mp (τ.map_nonneg v.support_projection.nonneg)).1
lemma rank_le_one (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1=1) (v : Rep G M) : Rep.rank τ v≤1 := by
  have hh := Complex.re_le_re (τ.monotone v.support_projection.le_one)
  change (τ v.support).re ≤ (τ 1).re at hh
  simpa only [Rep.rank,h1,Complex.one_re] using hh

end PopaPatching

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaPatching
universe u
variable {C B G : Type*} [Group G]
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

lemma preGNS_real_smul (r : ℝ) (a : M) : τ.toPreGNS (r • a)=r • τ.toPreGNS a := rfl

include h1 in
lemma good_short_bound (a : C → M) (γ : B → G) (L : ℕ) (ε : ℕ → ℝ)
    (hε : ∀ n, 0≤ε n) (hmono : Monotone ε) (v : Rep G M)
    (hv : Good e τ hτ htr hfaith a γ L ε v) (l : List (Letter C B)) (k : ℕ)
    (hl : l.length≤L) (hk : l.length≤k) (hd : degree γ l ≠ 1) :
    ‖τ.toPreGNS (average e τ hτ htr hfaith (evaluate a γ v l))‖≤ε k := by
  exact ((hv.2) l hl hd).trans ((mul_le_mul_of_nonneg_right (hmono hk) (rank_nonneg τ v)).trans
    (mul_le_of_le_one_right (hε k) (rank_le_one τ h1 v)))

include h1 in
lemma residual_coefficient (v : Rep G M) {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (hpv : p=1-v.support) (Y : M) :
    (τ p).re • cornerCoefficient e τ hτ htr hfaith hp Y =
      average e τ hτ htr hfaith Y-average e τ hτ htr hfaith (v.support*Y) := by
  have ht := HochschildDiffuse.projection_trace_pos τ hfaith hp hp0
  rw [cornerCoefficient,smul_smul,mul_inv_cancel₀ ht.ne',one_smul,
    average_trace e τ hτ htr hfaith h1 (p*Y) p,←mul_assoc,hp.isIdempotentElem.eq,
    hpv,sub_mul,one_mul]
  exact map_sub (expectation e τ hτ htr hfaith h1) _ _

include h1 in
lemma residual_coefficient_bound (v : Rep G M) {p : M} (hp : IsStarProjection p)
    (hp0 : p ≠ 0) (hpv : p=1-v.support) (Y : M) (E δ : ℝ) (hδ : 0<δ)
    (hpδ : δ≤(τ p).re) (hY : ‖τ.toPreGNS (average e τ hτ htr hfaith Y)‖≤E)
    (hfY : ‖τ.toPreGNS (average e τ hτ htr hfaith (v.support*Y))‖≤E) :
    ‖τ.toPreGNS (cornerCoefficient e τ hτ htr hfaith hp Y)‖≤2*E/δ := by
  have ht : 0<(τ p).re := lt_of_lt_of_le hδ hpδ
  have hh := norm_sub_le (τ.toPreGNS (average e τ hτ htr hfaith Y))
    (τ.toPreGNS (average e τ hτ htr hfaith (v.support*Y)))
  rw [←map_sub,←residual_coefficient e τ hτ htr hfaith h1 v hp hp0 hpv Y,
    preGNS_real_smul τ,norm_smul,Real.norm_eq_abs,abs_of_pos ht] at hh
  apply (le_div_iff₀ hδ).mpr
  nlinarith [norm_nonneg (τ.toPreGNS (cornerCoefficient e τ hτ htr hfaith hp Y))]

include htr in
lemma product_l2_bound {K : Type*} (l : List K) (c : K → M)
    (hc : ∀ j ∈ l, ‖c j‖≤1) (j : K) (hj : j ∈ l) (E : ℝ)
    (hE : ‖τ.toPreGNS (c j)‖≤E) : ‖τ.toPreGNS ((l.map c).prod)‖≤E := by
  obtain ⟨s,t,rfl⟩ := List.mem_iff_append.mp hj
  have hs := prod_norm_le s c (fun i hi => hc i (by simp [hi]))
  have ht := prod_norm_le t c (fun i hi => hc i (by simp [hi]))
  simp only [List.map_append,List.prod_append,List.map_cons,List.prod_cons]
  exact (preGNS_norm_mul_le τ _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hs).trans
    ((preGNS_norm_mul_right_le τ htr _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) ht).trans hE)))

lemma norm_list_sum {V : Type*} [SeminormedAddCommGroup V] (l : List V) :
    ‖l.sum‖≤(l.map norm).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.sum_cons,List.map_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

lemma patch_sum_bound {V K : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (l : List K) (z : V) (b : K → V) (c : K → ℝ)
    (E r Q H : ℝ) (_hE : 0≤E) (_hr : 0≤r) (hQ : 0≤Q) (_hH : 0≤H)
    (hc : ∀ i ∈ l, 0≤c i) (hc1 : (l.map c).sum≤1)
    (hz : ‖z‖≤E*r) (hb : ∀ i ∈ l, ‖b i+c i • z‖≤H*Q)
    (hN : (l.length:ℝ)*H≤E) : ‖z+(l.map b).sum‖≤E*(r+Q) := by
  let s := (l.map c).sum
  have hsum : (l.map (fun i => c i • z)).sum=s • z := by
    simpa only [List.map_map,Function.comp_def,s] using (List.sum_smul (l:=l.map c) (x:=z)).symm
  have heq : z+(l.map b).sum=(1-s) • z+(l.map (fun i => b i+c i • z)).sum := by
    rw [List.sum_map_add,hsum]
    change _=(1-s) • z+((l.map b).sum+s • z)
    rw [sub_smul,one_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖(1-s) • z‖+‖(l.map (fun i => b i+c i • z)).sum‖ := norm_add_le _ _
    _ ≤ (1-s)*‖z‖+(l.length:ℝ)*(H*Q) := by
      apply add_le_add
      · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hc1)]
      · exact (norm_list_sum _).trans (by
          calc
            _ ≤ (l.map (fun _ => H*Q)).sum := by
              simpa only [List.map_map,Function.comp_def] using List.sum_le_sum hb
            _ = _ := by simp)
    _ ≤ E*r+E*Q := by
      have hs : 0 ≤ s := List.sum_nonneg (by
        intro x hx; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx; exact hc i hi)
      have hcz := mul_le_of_le_one_left (norm_nonneg z) (show 1-s≤1 by linarith)
      have hq := mul_le_mul_of_nonneg_right hN hQ
      nlinarith
    _ = _ := by ring
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
attribute [local instance] Classical.propDecidable
variable {C B G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def identitySingleton (γ : B → G) (bs : List B) : Prop := ∃ b, bs=[b] ∧ γ b=1

@[simp] lemma identitySingleton_one (γ : B → G) (b : B) : identitySingleton γ [b] ↔ γ b=1 := by
  simp [identitySingleton]
@[simp] lemma identitySingleton_two (γ : B → G) (b c : B) (bs : List B) :
    ¬identitySingleton γ (b::c::bs) := by simp [identitySingleton]

end PopaPatching

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaPatching
universe u
variable {G : Type*} [Group G]
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
lemma singleton_cancellation_bound (v : Rep G M) {p q : M} (hp : IsStarProjection p)
    (hp0 : p ≠ 0) (hpv : p=1-v.support) (hq : IsStarProjection q)
    (hEq : average e τ hτ htr hfaith q=(τ q).re • (1:M)) (Y z : M) (E δ θ : ℝ)
    (hE : 0≤E) (hδ : 0<δ) (hpδ : δ≤(τ p).re)
    (hY : ‖τ.toPreGNS (average e τ hτ htr hfaith Y)‖≤E)
    (hz : ‖τ.toPreGNS (z-cornerCoefficient e τ hτ htr hfaith hp Y*average e τ hτ htr hfaith q)‖≤θ*(τ q).re) :
    ‖τ.toPreGNS (z+((τ q).re/(τ p).re) • average e τ hτ htr hfaith (v.support*Y))‖≤(E/δ+θ)*(τ q).re := by
  let c := cornerCoefficient e τ hτ htr hfaith hp Y
  let A : ℝ := (τ q).re/(τ p).re
  have ht : 0<(τ p).re := lt_of_lt_of_le hδ hpδ
  have hqnonneg : 0≤(τ q).re := (Complex.nonneg_iff.mp (τ.map_nonneg hq.nonneg)).1
  have hA : 0≤A := div_nonneg hqnonneg ht.le
  have hc := residual_coefficient e τ hτ htr hfaith h1 v hp hp0 hpv Y
  have hc' : c*average e τ hτ htr hfaith q+A • average e τ hτ htr hfaith (v.support*Y)=
      A • average e τ hτ htr hfaith Y := by
    rw [hEq,mul_smul_comm,mul_one]
    have he : A*(τ p).re=(τ q).re := div_mul_cancel₀ _ ht.ne'
    calc
      _ = A • ((τ p).re • c+average e τ hτ htr hfaith (v.support*Y)) := by
        rw [smul_add,smul_smul,he]
      _ = _ := by rw [hc,sub_add_cancel]
  have he : z+A • average e τ hτ htr hfaith (v.support*Y)=
      (z-c*average e τ hτ htr hfaith q)+A • average e τ hτ htr hfaith Y := by rw [←hc']; abel
  change ‖τ.toPreGNS (z+A • average e τ hτ htr hfaith (v.support*Y))‖≤_
  rw [he,map_add]
  calc
    _ ≤ ‖τ.toPreGNS (z-c*average e τ hτ htr hfaith q)‖+
        ‖τ.toPreGNS (A • average e τ hτ htr hfaith Y)‖ := norm_add_le _ _
    _ ≤ θ*(τ q).re+A*E := by
      apply add_le_add hz
      rw [preGNS_real_smul τ,norm_smul,Real.norm_eq_abs,abs_of_nonneg hA]
      exact mul_le_mul_of_nonneg_left hY hA
    _ ≤ (E/δ+θ)*(τ q).re := by
      have hdiv : E/(τ p).re≤E/δ := div_le_div_of_nonneg_left hE hδ hpδ
      have hh := mul_le_mul_of_nonneg_left hdiv hqnonneg
      dsimp [A]
      simp only [div_eq_mul_inv] at hh ⊢
      nlinarith
end PopaCenter

namespace PopaCenter
open PopaPatching
variable {C B G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
omit [PartialOrder M] [StarOrderedRing M] in
lemma cyclic_blocks {N : Type*} (T : M → N) (hT : ∀ x y : M, T (x*y)=T (y*x))
    (a : C → M) (γ : B → G) (v w : Rep G M) (m : List (Mark C B))
    (hm : freshs m ≠ []) (hd : degree γ (m.map eraseMark) ≠ 1) :
    ∃ b : List (Block C B), b ≠ [] ∧ b.map Prod.fst=freshs m ∧
      (eraseBlocks b).length=m.length ∧ degree γ (eraseBlocks b) ≠ 1 ∧
      T (markedEval a γ v w m)=T ((b.map (fun j => w (γ j.1)*evaluate a γ v j.2)).prod) ∧
      T (evaluate a γ v (m.map eraseMark))=T (evaluate a γ v (eraseBlocks b)) := by
  let pre := (splitMarked m).1
  let bs := (splitMarked m).2
  have hbs : bs ≠ [] := freshs_nonempty_split m hm
  let b := appendTail bs pre
  have he : flattenBlocks b=flattenBlocks bs++pre.map oldMark := appendTail_spec bs pre hbs
  have hm' : m=pre.map oldMark++flattenBlocks bs := splitMarked_spec m
  have her : m.map eraseMark=pre++eraseBlocks bs := by rw [hm']; simp only [List.map_append,erase_old_list,erase_flatten]
  have he' : eraseBlocks b=eraseBlocks bs++pre := by
    rw [←erase_flatten,he,List.map_append,erase_flatten,erase_old_list]
  have hf : b.map Prod.fst=freshs m := by
    rw [←freshs_flatten,he,hm']
    simp
  have hlen : (eraseBlocks b).length=m.length := by
    rw [he',List.length_append,hm',List.length_append,List.length_map]
    have hh := congrArg List.length (erase_flatten bs)
    simp only [List.length_map] at hh
    omega
  refine ⟨b,fun hh => hm (by rw [←hf,hh,List.map_nil]),hf,hlen,?_,?_,?_⟩
  · rw [he']
    exact degree_rotation_ne_one γ pre (eraseBlocks bs) (by rwa [her] at hd)
  · rw [←markedEval_flatten,he,hm',markedEval_append,markedEval_append]
    exact hT _ _
  · rw [her,he',evaluate_append,evaluate_append]
    exact hT _ _
end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaPatching
attribute [local instance] Classical.propDecidable
universe u
variable {C B G : Type*} [Group G]
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
theorem many_blocks_bound (hII : PopaTypeII.NoAbelianCorners M)
    (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (b0 : B) (hb0 : γ b0=1)
    (L : ℕ) (ε : ℕ → ℝ) (hε : ∀ n, 0≤ε n) (hmono : Monotone ε)
    (v : Rep G M) (hv : Good e τ hτ htr hfaith a γ L ε v)
    {p q : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (hpv : p=1-v.support)
    (hEp : Homogeneous e τ hτ htr hfaith p)
    (hq : IsStarProjection q) (hq0 : q ≠ 0) (hEq : Homogeneous e τ hτ htr hfaith q)
    (w : Rep G M) (hw : w.support=q)
    (δ θ : ℝ) (hδ : 0<δ) (hpδ : δ≤(τ p).re) (hθ : 0≤θ)
    (hkill : ∀ bs : List B, bs.length≤L → (bs.map γ).prod ≠ 1 → average e τ hτ htr hfaith (w ((bs.map γ).prod))=0)
    (he : ∀ l : List (Letter C B), l.length≤L →
      ‖(PopaCorner.trace hq τ).toPreGNS (PopaCorner.compress hq (evaluate a γ v l)-
        PopaCorner.compress hq (cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v l)))‖≤θ)
    (b : List (Block C B)) (hb : 2≤b.length) (hL : (eraseBlocks b).length≤L)
    (hd : degree γ (eraseBlocks b) ≠ 1) :
    ‖τ.toPreGNS (average e τ hτ htr hfaith ((b.map (fun j => w (γ j.1)*evaluate a γ v j.2)).prod))‖≤
      (2*ε ((eraseBlocks b).length-1)/δ+(L:ℝ)*θ)*(τ q).re := by
  let k := (eraseBlocks b).length
  let E := ε (k-1)
  let c : Block C B → M := fun j => cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v j.2)
  have hseg (j : Block C B) (hj : j ∈ b) : j.2.length+1≤k-1 := by
    have hh := segment_length_bound b j hj
    dsimp [k]; omega
  have hc (j : Block C B) (hj : j ∈ b) : ‖c j‖≤1 :=
    (cornerCoefficient_spec e τ hτ htr hfaith h1 hII hp hp0 hEp _).2.trans (evaluate_norm_le a ha γ v _)
  have hcZ (j : Block C B) : Central (c j) := cornerCoefficient_central e τ hτ htr hfaith hp _
  have hbe := block_average_error e τ hτ htr hfaith h1 w hq hq0 hw hEq b (fun j => γ j.1)
    (fun j => evaluate a γ v j.2) c hcZ (by intro hh; simp [hh] at hb)
    (fun j _ => evaluate_norm_le a ha γ v _) hc θ hθ
    (fun j hj => he j.2 (by have hh := hseg j hj; dsimp [k] at hh; omega))
  have ht : 0<(τ q).re := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
  have hbl : (b.length:ℝ)≤L := by exact_mod_cast (blocks_length_le b).trans hL
  by_cases hg : (b.map (fun j => γ j.1)).prod=1
  · obtain ⟨j,hj,hjd⟩ := exists_nontrivial_segment γ b hd hg
    have hjlen := hseg j hj
    have hY : ‖τ.toPreGNS (average e τ hτ htr hfaith (evaluate a γ v j.2))‖≤E :=
      good_short_bound e τ hτ htr hfaith h1 a γ L ε hε hmono v hv j.2
        (k-1) (by dsimp [k] at hjlen; omega) (by omega) hjd
    have hfY : ‖τ.toPreGNS (average e τ hτ htr hfaith (v.support*evaluate a γ v j.2))‖≤E := by
      have hh := good_short_bound e τ hτ htr hfaith h1 a γ L ε hε hmono v hv (Sum.inr b0::j.2)
        (k-1) (by simp only [List.length_cons]; dsimp [k] at hjlen; omega)
        (by simp only [List.length_cons]; omega) (by simpa [degree_cons,letterDegree,hb0] using hjd)
      simpa only [evaluate_cons,letterValue,Sum.elim_inr,hb0,Rep.support] using hh
    have hcj : ‖τ.toPreGNS (c j)‖≤2*E/δ := residual_coefficient_bound e τ hτ htr hfaith h1 v hp hp0 hpv
      (evaluate a γ v j.2) E δ hδ hpδ hY hfY
    have hcp := product_l2_bound τ htr b c hc j hj (2*E/δ) hcj
    rw [hg,show w 1=q from hw,hEq,mul_smul_comm,mul_one] at hbe
    have hn := norm_add_le
      (τ.toPreGNS (average e τ hτ htr hfaith ((b.map (fun j => w (γ j.1)*evaluate a γ v j.2)).prod)-
        (τ q).re • (b.map c).prod)) (τ.toPreGNS ((τ q).re • (b.map c).prod))
    rw [←map_add,sub_add_cancel,preGNS_real_smul τ,norm_smul,Real.norm_eq_abs,abs_of_pos ht] at hn
    have hh := mul_le_mul_of_nonneg_left hcp ht.le
    have hθb := mul_le_mul_of_nonneg_right hbl hθ
    change _ ≤ (2*E/δ+(L:ℝ)*θ)*(τ q).re
    nlinarith
  · have hk : average e τ hτ htr hfaith (w ((b.map (fun j => γ j.1)).prod))=0 := by
      have hh := hkill (b.map Prod.fst) (by simpa using (blocks_length_le b).trans hL)
        (by simpa only [List.map_map,Function.comp_def] using hg)
      simpa only [List.map_map,Function.comp_def] using hh
    rw [hk,mul_zero,sub_zero] at hbe
    have hEn : 0≤2*E/δ := div_nonneg (mul_nonneg (by norm_num) (hε _)) hδ.le
    have hθb := mul_le_mul_of_nonneg_right hbl hθ
    change _ ≤ (2*E/δ+(L:ℝ)*θ)*(τ q).re
    nlinarith

include h1 in
theorem all_blocks_bound (hII : PopaTypeII.NoAbelianCorners M)
    (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (b0 : B) (hb0 : γ b0=1)
    (L : ℕ) (ε : ℕ → ℝ) (hε : ∀ n, 0≤ε n) (hmono : Monotone ε)
    (v : Rep G M) (hv : Good e τ hτ htr hfaith a γ L ε v)
    {p q : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (hpv : p=1-v.support)
    (hEp : Homogeneous e τ hτ htr hfaith p)
    (hq : IsStarProjection q) (hq0 : q ≠ 0) (hEq : Homogeneous e τ hτ htr hfaith q)
    (w : Rep G M) (hw : w.support=q)
    (δ θ : ℝ) (hδ : 0<δ) (hpδ : δ≤(τ p).re) (hθ : 0≤θ)
    (hkill : ∀ bs : List B, bs.length≤L → (bs.map γ).prod ≠ 1 → average e τ hτ htr hfaith (w ((bs.map γ).prod))=0)
    (he : ∀ l : List (Letter C B), l.length≤L →
      ‖(PopaCorner.trace hq τ).toPreGNS (PopaCorner.compress hq (evaluate a γ v l)-
        PopaCorner.compress hq (cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v l)))‖≤θ)
    (b : List (Block C B)) (hb : b ≠ []) (hL : (eraseBlocks b).length≤L)
    (hd : degree γ (eraseBlocks b) ≠ 1) :
    ‖τ.toPreGNS (average e τ hτ htr hfaith ((b.map (fun j => w (γ j.1)*evaluate a γ v j.2)).prod)+
      (if identitySingleton γ (b.map Prod.fst) then (τ q).re/(τ p).re else 0 : ℝ) •
        average e τ hτ htr hfaith (evaluate a γ v (eraseBlocks b)))‖≤
      (2*ε ((eraseBlocks b).length-1)/δ+(L:ℝ)*θ)*(τ q).re := by
  classical
  cases b with
  | nil => exact False.elim (hb rfl)
  | cons j bs =>
    cases bs with
    | cons j' bs =>
      simp only [List.map_cons,identitySingleton_two,reduceIte,zero_smul,add_zero]
      exact many_blocks_bound e τ hτ htr hfaith h1 hII a ha γ b0 hb0 L ε hε hmono v hv
        hp hp0 hpv hEp hq hq0 hEq w hw δ θ hδ hpδ hθ hkill he (j::j'::bs) (by simp) hL hd
    | nil =>
      have hlen : (eraseBlocks [j]).length=j.2.length+1 := by simp [eraseBlocks]
      have hjL : j.2.length≤L := by rw [hlen] at hL; omega
      have hL1 : (1:ℝ)≤L := by exact_mod_cast (show 1≤L by rw [hlen] at hL; omega)
      have ht : 0<(τ q).re := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
      let c := cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v j.2)
      have hbe := block_average_error e τ hτ htr hfaith h1 w hq hq0 hw hEq [j] (fun j => γ j.1)
        (fun j => evaluate a γ v j.2) (fun j => cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v j.2))
        (fun j => cornerCoefficient_central e τ hτ htr hfaith hp _) (by simp)
        (fun j _ => evaluate_norm_le a ha γ v _)
        (fun j _ => (cornerCoefficient_spec e τ hτ htr hfaith h1 hII hp hp0 hEp _).2.trans
          (evaluate_norm_le a ha γ v _)) θ hθ
        (fun k hk => by
          have hk' : k=j := by simpa using hk
          subst k
          exact he j.2 hjL)
      simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
        List.length_cons,List.length_nil,Nat.zero_add,Nat.cast_one,one_mul] at hbe
      have hEn := hε j.2.length
      have hEdiv : 0≤ε j.2.length/δ := div_nonneg hEn hδ.le
      simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
        identitySingleton_one,hlen,Nat.add_sub_cancel]
      by_cases hg : γ j.1=1
      · rw [ite_eq_left hg]
        have hYd : degree γ j.2 ≠ 1 := by
          simpa [eraseBlocks,degree_cons,letterDegree,hg] using hd
        have hY := good_short_bound e τ hτ htr hfaith h1 a γ L ε hε hmono v hv j.2 j.2.length hjL le_rfl hYd
        have hold : evaluate a γ v (eraseBlocks [j])=v.support*evaluate a γ v j.2 := by
          rw [evaluate_blocks]
          simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,hg,Rep.support]
        have hbe' : ‖τ.toPreGNS (average e τ hτ htr hfaith (w (γ j.1)*evaluate a γ v j.2)-
            c*average e τ hτ htr hfaith q)‖≤θ*(τ q).re := by
          simpa only [hg,show w 1=q from hw] using hbe
        have hh := singleton_cancellation_bound e τ hτ htr hfaith h1 v hp hp0 hpv hq hEq
          (evaluate a γ v j.2) (average e τ hτ htr hfaith (w (γ j.1)*evaluate a γ v j.2))
          (ε j.2.length) δ θ hEn hδ hpδ hY hbe'
        rw [hold]
        have hθL := mul_le_mul_of_nonneg_right hL1 hθ
        have heq : 2*ε j.2.length/δ=2*(ε j.2.length/δ) := by ring
        rw [heq]
        nlinarith
      · rw [ite_eq_right hg,zero_smul,add_zero]
        have hk := hkill [j.1] (by simp only [List.length_cons,List.length_nil]; rw [hlen] at hL; omega)
          (by simpa using hg)
        simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at hk
        rw [hk,mul_zero,sub_zero] at hbe
        have hθL := mul_le_mul_of_nonneg_right hL1 hθ
        have heq : 2*ε j.2.length/δ=2*(ε j.2.length/δ) := by ring
        rw [heq]
        nlinarith
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaPatching
attribute [local instance] Classical.propDecidable
universe u
variable {C B G : Type*} [Group G]
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
theorem good_add (hII : PopaTypeII.NoAbelianCorners M)
    (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (b0 : B) (hb0 : γ b0=1)
    (L : ℕ) (ε : ℕ → ℝ) (hε : ∀ n, 0≤ε n) (hmono : Monotone ε)
    (v : Rep G M) (hv : Good e τ hτ htr hfaith a γ L ε v)
    {p q : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (hpv : p=1-v.support)
    (hEp : Homogeneous e τ hτ htr hfaith p)
    (hq : IsStarProjection q) (hq0 : q ≠ 0) (hEq : Homogeneous e τ hτ htr hfaith q)
    (w : Rep G M) (hw : w.support=q) (hvw : v.support*w.support=0)
    (δ θ : ℝ) (hδ : 0<δ) (hpδ : δ≤(τ p).re) (hθ : 0≤θ)
    (hsmall : (τ q).re < (τ p).re/((2:ℝ)^L+1))
    (hstep : ∀ k, 1≤k → k≤L → (2:ℝ)^L*(2*ε (k-1)/δ+(L:ℝ)*θ)≤ε k)
    (hkill : ∀ bs : List B, bs.length≤L → (bs.map γ).prod ≠ 1 → average e τ hτ htr hfaith (w ((bs.map γ).prod))=0)
    (he : ∀ l : List (Letter C B), l.length≤L →
      ‖(PopaCorner.trace hq τ).toPreGNS (PopaCorner.compress hq (evaluate a γ v l)-
        PopaCorner.compress hq (cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v l)))‖≤θ) :
    Good e τ hτ htr hfaith a γ L ε (v.add w hvw) := by
  classical
  refine ⟨?_,fun l hl hd => ?_⟩
  · rw [Rep.add_support,hw]
    exact homogeneous_add e τ hτ htr hfaith h1 hv.1 hEq
  have hk : 1≤l.length := by
    by_contra hh
    have he : l=[] := List.length_eq_zero_iff.mp (by omega)
    exact hd (by rw [he]; rfl)
  let H := 2*ε (l.length-1)/δ+(L:ℝ)*θ
  let N : ℝ := 2^L
  let A : ℝ := (τ q).re/(τ p).re
  let c : List (Mark C B) → ℝ := fun m => if identitySingleton γ (freshs m) then A else 0
  have ht : 0<(τ p).re := lt_of_lt_of_le hδ hpδ
  have hqpos : 0<(τ q).re := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
  have hN : 0<N := pow_pos (by norm_num) _
  have hA : 0≤A := div_nonneg hqpos.le ht.le
  have hAeq : A*(τ p).re=(τ q).re := div_mul_cancel₀ _ ht.ne'
  have hNA : N*A≤1 := by
    have hh : (τ q).re*(N+1)<(τ p).re := (lt_div_iff₀ (by positivity)).mp hsmall
    have hh' : (N*A)*(τ p).re≤(τ p).re := by nlinarith
    nlinarith
  have hc0 (m) (_ : m ∈ newVariants l) : 0≤c m := by dsimp [c]; split <;> positivity
  have hcA (m) (_ : m ∈ newVariants l) : c m≤A := by
    dsimp [c]
    split
    · exact le_rfl
    · exact hA
  have hlen : ((newVariants l).length:ℝ)≤N := by
    dsimp [N]
    exact_mod_cast (newVariants_length_le l).trans (Nat.pow_le_pow_right (by decide) hl)
  have hc1 : ((newVariants l).map c).sum≤1 := by
    calc
      _ ≤ ((newVariants l).map (fun _ => A)).sum := List.sum_le_sum hcA
      _ = ((newVariants l).length:ℝ)*A := by simp
      _ ≤ N*A := mul_le_mul_of_nonneg_right hlen hA
      _ ≤ 1 := hNA
  have hH : 0≤H := by
    exact add_nonneg (div_nonneg (mul_nonneg (by norm_num) (hε _)) hδ.le)
      (mul_nonneg (Nat.cast_nonneg _) hθ)
  have hb (m) (hm : m ∈ newVariants l) :
      ‖τ.toPreGNS (average e τ hτ htr hfaith (markedEval a γ v w m))+c m •
        τ.toPreGNS (average e τ hτ htr hfaith (evaluate a γ v l))‖≤H*(τ q).re := by
    have hm' := mem_newVariants l m hm
    have her := erase_variant l m hm'.1
    have hmlen : m.length=l.length := by
      have hh := congrArg List.length her
      simpa only [List.length_map] using hh
    obtain ⟨b,hb,hf,hbl,hd',htrace,hold⟩ := cyclic_blocks (average e τ hτ htr hfaith) (average_trace e τ hτ htr hfaith h1) a γ v w m hm'.2 (by rwa [her])
    have hh := all_blocks_bound e τ hτ htr hfaith h1 hII a ha γ b0 hb0 L ε hε hmono v hv
      hp hp0 hpv hEp hq hq0 hEq w hw δ θ hδ hpδ hθ hkill he b hb (by rwa [hbl,hmlen]) hd'
    rw [hf,hbl,hmlen,←htrace,←hold,her] at hh
    simpa only [map_add,preGNS_real_smul τ] using hh
  have hsum := patch_sum_bound (newVariants l) (τ.toPreGNS (average e τ hτ htr hfaith (evaluate a γ v l)))
    (fun m => τ.toPreGNS (average e τ hτ htr hfaith (markedEval a γ v w m))) c (ε l.length) (Rep.rank τ v) (τ q).re H
    (hε _) (rank_nonneg τ v) hqpos.le hH hc0 hc1 (hv.2 l hl hd) hb
    ((mul_le_mul_of_nonneg_right hlen hH).trans (hstep l.length hk hl))
  have hrank : Rep.rank τ (v.add w hvw)=Rep.rank τ v+(τ q).re := by
    simp only [Rep.rank,Rep.add_support,hw,map_add,Complex.add_re]
  rw [hrank,evaluate_add_new_expansion]
  change ‖τ.toPreGNS (expectation e τ hτ htr hfaith h1 (_+_))‖≤_
  rw [map_add,map_add,map_list_sum,map_list_sum]
  simpa only [List.map_map,Function.comp_def,expectation_apply] using hsum
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

namespace PopaPatching

theorem tolerance_schedule (L : ℕ) (δ E : ℝ) (hδ : 0<δ) (hE : 0<E) :
    ∃ ε : ℕ → ℝ, ∃ θ : ℝ, (∀ k, 0≤ε k) ∧ Monotone ε ∧ 0<θ ∧ ε L<E ∧
      ∀ k, 1≤k → k≤L → (2:ℝ)^L*(2*ε (k-1)/δ+(L:ℝ)*θ)≤ε k := by
  let N : ℝ := 2^L
  let R : ℝ := 2*N/δ+2
  let t : ℝ := E/(R^L+1)
  let ε : ℕ → ℝ := fun k => t*R^k
  let θ : ℝ := t/(N*((L:ℝ)+1))
  have hN : 0<N := pow_pos (by norm_num) _
  have hR : 1≤R := by
    have : 0≤2*N/δ := div_nonneg (by positivity) hδ.le
    dsimp [R]
    linarith
  have hRpos : 0<R := lt_of_lt_of_le (by norm_num) hR
  have ht : 0<t := div_pos hE (by positivity)
  have hθ : 0<θ := div_pos ht (mul_pos hN (by positivity))
  have heps (k) : 0≤ε k := mul_nonneg ht.le (pow_nonneg hRpos.le _)
  have hmono : Monotone ε := by
    apply monotone_nat_of_le_succ
    intro k
    dsimp [ε]
    rw [pow_succ]
    have hr := mul_le_mul_of_nonneg_left hR (pow_nonneg hRpos.le k)
    nlinarith
  have hL : ε L<E := by
    have he : t*(R^L+1)=E := div_mul_cancel₀ _ (by positivity)
    dsimp [ε]
    nlinarith
  refine ⟨ε,θ,heps,hmono,hθ,hL,fun k hk _ => ?_⟩
  have hk' : k=(k-1)+1 := by omega
  have heq : ε k=ε (k-1)*R := by
    change t*R^k=(t*R^(k-1))*R
    conv_lhs => rw [hk',pow_succ]
    ring
  have htε : t≤ε (k-1) := by
    have hh := hmono (show 0≤k-1 from Nat.zero_le _)
    simpa only [ε,pow_zero,mul_one] using hh
  have hθeq : θ*(N*((L:ℝ)+1))=t := div_mul_cancel₀ _ (by positivity)
  have hsmall : N*(L:ℝ)*θ≤ε (k-1) := by nlinarith
  rw [heq]
  dsimp [R]
  simp only [div_eq_mul_inv]
  nlinarith [heps (k-1)]
end PopaPatching

open scoped ComplexOrder
namespace PopaPatching
variable {G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma Rep.le_add (v w : Rep G M) (hvw : v.support*w.support=0) : v≤v.add w hvw := by
  have hwv : w.support*v.support=0 := by
    have hh := congrArg star hvw
    simpa only [star_mul,v.support_projection.isSelfAdjoint.star_eq,
      w.support_projection.isSelfAdjoint.star_eq,star_zero] using hh
  refine ⟨?_,fun g => ?_⟩
  · change v.support≤v.support+w.support
    exact le_add_of_nonneg_right w.support_projection.nonneg
  · change (v g+w g)*v.support=v g
    rw [add_mul,v.mul_support]
    have hh : w g*v.support=0 := by
      calc
        w g*v.support = (w g*w.support)*v.support := by rw [w.mul_support]
        _ = 0 := by rw [mul_assoc,hwv,mul_zero]
    rw [hh,add_zero]

lemma Rep.lt_add (v w : Rep G M) (hvw : v.support*w.support=0) (hw : w.support ≠ 0) :
    v<v.add w hvw := by
  refine lt_of_le_of_ne (v.le_add w hvw) ?_
  intro he
  have hh := congrArg Rep.support he.symm
  change v.support+w.support=v.support at hh
  exact hw (add_left_cancel (show v.support+w.support=v.support+0 by simpa using hh))

universe u v
variable {C B D : Type u} [Fintype C] [Fintype B]
variable {M X : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end PopaPatching

open scoped ComplexOrder
namespace PopaCenter
open PopaPatching
universe u v
variable {C B D : Type u} [Fintype C] [Fintype B]
variable {M X : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in

theorem exists_good_extension (hII : PopaTypeII.NoAbelianCorners M)
    (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → FreeGroup D) (b0 : B) (hb0 : γ b0=1)
    (L : ℕ) (ε : ℕ → ℝ) (hε : ∀ n, 0≤ε n) (hmono : Monotone ε)
    (δ θ : ℝ) (hδ : 0<δ) (hθ : 0<θ)
    (hstep : ∀ k, 1≤k → k≤L → (2:ℝ)^L*(2*ε (k-1)/δ+(L:ℝ)*θ)≤ε k)
    (v : Rep (FreeGroup D) M) (hv : Good e τ hτ htr hfaith a γ L ε v)
    (hpδ : δ≤(τ (1-v.support)).re) :
    ∃ z : Rep (FreeGroup D) M, Good e τ hτ htr hfaith a γ L ε z ∧ v<z := by
  classical
  let p := 1-v.support
  have hp : IsStarProjection p := v.support_projection.one_sub
  have hp0 : p ≠ 0 := by
    intro hh
    have hz : (τ p).re=0 := by rw [hh,map_zero,Complex.zero_re]
    change δ≤(τ p).re at hpδ
    linarith
  have hE1 : Homogeneous e τ hτ htr hfaith (1:M) := by
    change average e τ hτ htr hfaith 1=(τ 1).re • (1:M)
    rw [average_id e τ hτ htr hfaith h1 (fun x => Commute.one_left x),h1,Complex.one_re,one_smul]
  have hEp : Homogeneous e τ hτ htr hfaith p := homogeneous_sub e τ hτ htr hfaith h1 hE1 hv.1
  obtain ⟨q,hq,hq0,hqp,hqt,hEq,he⟩ := quantize_words e τ hτ htr hfaith h1 hII hp hp0 hEp
    a γ v L θ (1/((2:ℝ)^L+1)) hθ (by positivity)
  let S : Finset (FreeGroup D) := (shortWords B L).image (fun bs => (bs.map γ).prod)
  obtain ⟨w,hw,hkill⟩ := finite_corner_rep e τ hτ htr hfaith h1 hII hq hEq S
  have hvw : v.support*w.support=0 := by
    rw [hw]
    have hpeq : p*q=q := (hq.le_iff_mul_eq_right hp).mp hqp
    have hf : v.support*p=0 := by
      dsimp [p]
      rw [mul_sub,mul_one,v.support_projection.isIdempotentElem.eq,sub_self]
    calc
      v.support*q = v.support*(p*q) := by rw [hpeq]
      _ = 0 := by rw [←mul_assoc,hf,zero_mul]
  have hgood := good_add e τ hτ htr hfaith h1 hII a ha γ b0 hb0 L ε hε hmono v hv
    hp hp0 rfl hEp hq hq0 hEq w hw hvw δ θ hδ hpδ hθ.le
    (by simpa only [div_eq_mul_inv,one_mul,mul_comm] using hqt) hstep
    (fun bs hb hd => hkill _ (Finset.mem_image.mpr ⟨bs,(mem_shortWords bs L).mpr hb,rfl⟩) hd) he
  exact ⟨v.add w hvw,hgood,v.lt_add w hvw (by rwa [hw])⟩

include h1 in

theorem exists_almost_full_good (hII : PopaTypeII.NoAbelianCorners M)
    (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → FreeGroup D) (b0 : B) (hb0 : γ b0=1)
    (L : ℕ) (δ E : ℝ) (hδ : 0<δ) (hE : 0<E) :
    ∃ v : Rep (FreeGroup D) M,
      (τ (1-v.support)).re<δ ∧
      ∀ l : List (Letter C B), l.length≤L → degree γ l ≠ 1 → ‖τ.toPreGNS (average e τ hτ htr hfaith (evaluate a γ v l))‖<E := by
  obtain ⟨ε,θ,hε,hmono,hθ,hεL,hstep⟩ := tolerance_schedule L δ E hδ hE
  obtain ⟨v,hv,hmax⟩ := maximal_good e τ hτ htr hfaith h1 a ha γ L ε
  have hpδ : (τ (1-v.support)).re<δ := by
    by_contra hh
    obtain ⟨z,hz,hvz⟩ := exists_good_extension e τ hτ htr hfaith h1 hII
      a ha γ b0 hb0 L ε hε hmono δ θ hδ hθ hstep v hv (le_of_not_gt hh)
    exact hvz.not_ge (hmax z hz hvz.le)
  refine ⟨v,hpδ,fun l hl hd => ?_⟩
  exact (good_short_bound e τ hτ htr hfaith h1 a γ L ε hε hmono v hv l L hl hl hd).trans_lt hεL
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
variable {G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

namespace Rep

def trivial {p : M} (hp : IsStarProjection p) : Rep G M where
  val _ := p
  mul _ _ := hp.isIdempotentElem.eq.symm
  inv _ := hp.isSelfAdjoint.star_eq.symm

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma trivial_support {p : M} (hp : IsStarProjection p) :
    (trivial (G:=G) hp).support=p := rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma residual_orthogonal (v : Rep G M) : v.support*(1-v.support)=0 := by
  rw [mul_sub,mul_one,v.support_projection.isIdempotentElem.eq,sub_self]

def fill (v : Rep G M) : Rep G M :=
  v.add (trivial v.support_projection.one_sub) v.residual_orthogonal

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma fill_apply (v : Rep G M) (g : G) : v.fill g=v g+(1-v.support) := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma fill_support (v : Rep G M) : v.fill.support=1 := by
  change v.support+(1-v.support)=1
  abel

def toUnitary (v : Rep G M) (hv : v.support=1) : G →* unitary M where
  toFun g := ⟨v g,by
    rw [Unitary.mem_iff]
    exact ⟨(v.star_mul_self g).trans hv,(v.mul_star_self g).trans hv⟩⟩
  map_one' := Subtype.ext hv
  map_mul' g h := Subtype.ext (v.mul g h)

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma toUnitary_coe (v : Rep G M) (hv) (g) : (v.toUnitary hv g:M)=v g := rfl
end Rep

variable {C B : Type*}
lemma fill_evaluate_error (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (h1 : τ 1=1) (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G)
    (v : Rep G M) (d : ℝ) (hd : 0≤d) (hv : (τ (1-v.support)).re≤d^2)
    (l : List (Letter C B)) :
    ‖τ (evaluate a γ v.fill l)-τ (evaluate a γ v l)‖≤(l.length:ℝ)*d := by
  have hp := v.support_projection.one_sub
  have hsq : ‖τ.toPreGNS (1-v.support)‖^2=(τ (1-v.support)).re := by
    rw [PopaMatrices.System.norm_sq_eq_trace,hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]
  have hnorm : ‖τ.toPreGNS (1-v.support)‖≤d := by nlinarith [norm_nonneg (τ.toPreGNS (1-v.support))]
  have he (x : Letter C B) (_ : x ∈ l) :
      ‖τ.toPreGNS (letterValue a γ v.fill x-letterValue a γ v x)‖≤d := by
    cases x with
    | inl c => simpa only [letterValue,Sum.elim_inl,sub_self,map_zero,norm_zero] using hd
    | inr b =>
      change ‖τ.toPreGNS ((v (γ b)+(1-v.support))-v (γ b))‖≤d
      simpa only [add_sub_cancel_left] using hnorm
  rw [←map_sub]
  exact (HochschildUltrapower.norm_trace_le τ h1 _).trans
    (prod_gns_sub_uniform τ htr l (letterValue a γ v.fill) (letterValue a γ v)
      (fun x _ => letter_norm_le a ha γ v.fill x)
      (fun x _ => letter_norm_le a ha γ v x) d he)

universe u v
variable {C B D : Type u} [Fintype C] [Fintype B]
variable {M X : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end PopaPatching

open scoped ComplexOrder
namespace PopaCenter
open PopaPatching
universe u v
variable {C B D : Type u} [Fintype C] [Fintype B]
variable {M X : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include e hτ htr hfaith h1 in

theorem finite_unitary_moments (hII : PopaTypeII.NoAbelianCorners M)
    (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → FreeGroup D) (b0 : B) (hb0 : γ b0=1)
    (L : ℕ) (η : ℝ) (hη : 0<η) :
    ∃ v : Rep (FreeGroup D) M, v.support=1 ∧
      ∀ l : List (Letter C B), l.length≤L → degree γ l ≠ 1 → ‖τ (evaluate a γ v l)‖<η := by
  let d : ℝ := η/(2*((L:ℝ)+1))
  have hd : 0<d := div_pos hη (by positivity)
  obtain ⟨v,hv,hgood⟩ := exists_almost_full_good e τ hτ htr hfaith h1 hII
    a ha γ b0 hb0 L (d^2) (η/2) (sq_pos_of_pos hd) (by positivity)
  refine ⟨v.fill,v.fill_support,fun l hl hdg => ?_⟩
  have he := fill_evaluate_error τ htr h1 a ha γ v d hd.le hv.le l
  have ho : ‖τ (evaluate a γ v l)‖<η/2 := by
    rw [←trace_average e τ hτ htr hfaith h1]
    exact (HochschildUltrapower.norm_trace_le τ h1 _).trans_lt (hgood l hl hdg)
  have hdeq : d*(2*((L:ℝ)+1))=η := div_mul_cancel₀ _ (by positivity)
  have hlen : (l.length:ℝ)≤L := by exact_mod_cast hl
  have hbound := norm_add_le (τ (evaluate a γ v.fill l)-τ (evaluate a γ v l)) (τ (evaluate a γ v l))
  rw [sub_add_cancel] at hbound
  nlinarith
end PopaCenter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
namespace MissingFinitePaths
open BoundedHochschild HochschildDiffuse HochschildRare
universe u

end MissingFinitePaths

open scoped ComplexOrder
namespace PopaPatching
open HochschildRare HochschildPaths
variable {C D M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def pathCoefficients (v : C → unitary M) (x : C × Bool) : M := (signedValue v x:M)
def pathDegrees : Option (D × Bool) → FreeGroup D
  | none => 1
  | some (d,b) => signed (FreeGroup.of d) b

def pathEncode : (C ⊕ D) × Bool → Letter (C × Bool) (Option (D × Bool))
  | (.inl c,b) => .inl (c,b)
  | (.inr d,b) => .inr (some (d,b))

omit [PartialOrder M] [StarOrderedRing M] in
lemma pathCoefficients_norm (v : C → unitary M) (x) : ‖pathCoefficients v x‖≤1 := by
  have hh := CStarRing.norm_coe_unitary_mul (signedValue v x) (1:M)
  simpa only [mul_one,pathCoefficients] using hh.le.trans (IsStarProjection.one M).norm_le

lemma pathEncode_degree (l : List ((C ⊕ D) × Bool)) :
    degree pathDegrees (l.map pathEncode)=freshProjection (FreeGroup.mk l) := by
  simp only [degree,List.map_map,freshProjection,FreeGroup.lift_mk]
  congr 2
  funext x
  rcases x with ⟨c|d,b⟩ <;> cases b <;>
    simp [pathEncode,letterDegree,pathDegrees,signed]

omit [PartialOrder M] [StarOrderedRing M] in
lemma pathEncode_evaluate (a : C → unitary M) (v : Rep (FreeGroup D) M) (hv : v.support=1)
    (l : List ((C ⊕ D) × Bool)) :
    evaluate (pathCoefficients a) pathDegrees v (l.map pathEncode)=
      (FreeGroup.lift (Sum.elim a (fun d => v.toUnitary hv (FreeGroup.of d))) (FreeGroup.mk l):M) := by
  simp only [evaluate,List.map_map,FreeGroup.lift_mk]
  change _ = (unitary M).subtype ((l.map _).prod)
  rw [map_list_prod,List.map_map]
  congr 2
  funext x
  rcases x with ⟨c|d,b⟩ <;> cases b <;>
    simp [pathEncode,letterValue,pathCoefficients,signedValue,pathDegrees,signed,
      Rep.toUnitary]
  exact v.inv (FreeGroup.of d)

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end PopaPatching

open scoped ComplexOrder
namespace PopaCenter
open PopaPatching HochschildRare HochschildPaths
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include e hτ htr hfaith h1 in

theorem produced_finite_paths (hII : PopaTypeII.NoAbelianCorners M) :
    FinitePathTests τ := by
  classical
  intro C D T _ _ _ _ a r n w q hq hw η hη
  let g : T → FreeGroup (C ⊕ D) := fun t => pathHom (w t) (q t)
  let l : T → List (Letter (C × Bool) (Option (D × Bool))) := fun t => (g t).toWord.map pathEncode
  let L : ℕ := Finset.univ.sup (fun t => (l t).length)
  obtain ⟨v,hv,hgood⟩ := finite_unitary_moments e τ hτ htr hfaith h1 hII
    (pathCoefficients a) (pathCoefficients_norm a) (pathDegrees (D:=D)) none rfl L η hη
  refine ⟨fun d => v.toUnitary hv (FreeGroup.of d),fun t => ?_⟩
  have hlen : (l t).length≤L := Finset.le_sup (f:=fun t => (l t).length) (Finset.mem_univ t)
  have hdeg : degree pathDegrees (l t) ≠ 1 := by
    dsimp [l]
    rw [pathEncode_degree,FreeGroup.mk_toWord]
    obtain ⟨s,b,hpos,huniq⟩ := hw t
    exact freshProjection_pathHom_ne_one (w t) s b hpos huniq (q t) (hq t)
  have hh := hgood (l t) hlen hdeg
  dsimp [l] at hh
  rw [pathEncode_evaluate a v hv,FreeGroup.mk_toWord] at hh
  rw [lift_pathValue_formal]
  exact hh
end PopaCenter
end
end OAI
end

theorem solution.{u} : type_of% @OAI.PopaCenter.produced_finite_paths.{u} := @OAI.PopaCenter.produced_finite_paths.{u}
