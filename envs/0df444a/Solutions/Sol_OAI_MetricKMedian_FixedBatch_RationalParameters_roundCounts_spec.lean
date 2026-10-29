-- Prove2me | solution 1 for OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:47:25.541997+00:00
-- url     : https://prove2.me/submissions/ed02de4f-0150-46e9-9603-00377349be49

import Mathlib
import Definitions.Def_OAIQ035K012
import Definitions.Def_OAIQ035K047
import Theorems.Thm_OAI_MetricKMedian_FixedBatch_RationalParameters_selectCompleted_spec
import Theorems.Thm_OAI_MetricKMedian_WeightedRounding_exact_law

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_Conditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω : Type*} [Fintype Ω]

 theorem exists_support_le_expect (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    ∃ ω, 0 < μ.weight ω ∧ f ω ≤ μ.expect f := by
  classical
  have hn : ∃ ω, 0 < μ.weight ω := by
    by_contra h
    push Not at h
    have hz : ∀ ω, μ.weight ω=0 := fun ω => le_antisymm (h ω) (μ.nonneg ω)
    have ht := μ.total
    simp only [hz, sum_const_zero] at ht
    norm_num at ht
  by_contra h
  push Not at h
  have hs : μ.expect (fun _ => μ.expect f) < μ.expect f := by
    apply sum_lt_sum
    · intro ω _
      by_cases hp : 0 < μ.weight ω
      · exact mul_le_mul_of_nonneg_left (h ω hp).le (μ.nonneg ω)
      · rw [le_antisymm (le_of_not_gt hp) (μ.nonneg ω), zero_mul, zero_mul]
    · obtain ⟨ω,hω⟩ := hn
      exact ⟨ω, mem_univ _, mul_lt_mul_of_pos_left (h ω hω) hω⟩
  rw [expect_const] at hs
  exact lt_irrefl _ hs

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_AssignmentCopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential
variable {F : Type} [Fintype F] [DecidableEq F] {Δ : ℕ}

omit [Fintype F] [DecidableEq F] in
theorem embedSlots_injective (n : F → ℕ) (hn : ∀ a, n a ≤ Δ) : Function.Injective (embedSlots n hn) := by
  rintro ⟨a,h⟩ ⟨b,k⟩ he
  have hab : a=b := congrArg Prod.fst he
  subst b
  have hhk : h=k := Fin.ext (congrArg (fun x : Copy (F := F) Δ => x.2.val) he)
  subst k
  rfl

theorem activeSlots_mass (n : F → ℕ) (hn : ∀ a, n a ≤ Δ) (g : ℝ) :
    mass g (activeSlots n hn)=∑ a, g*(n a:ℝ) := by
  rw [mass,activeSlots,card_image_of_injective _ (embedSlots_injective n hn),card_univ,Fintype.card_sigma]
  rw [Nat.cast_sum,mul_sum]
  simp only [Fintype.card_fin]

theorem assignment_copies (n : F → ℕ) (hn : ∀ a, n a ≤ Δ) (r d : F → ℝ) {g : ℝ}
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
    (hr0 : ∀ a, 0 ≤ r a) (hr1 : ∀ a, r a ≤ g*(n a:ℝ)) (hsum : ∑ a, r a=1) :
    ∃ S : Finset (Copy (F := F) Δ), S ⊆ activeSlots n hn ∧ mass g S=1 ∧
      PhysicalPotential.cost g (fun a => d a.1) S ≤ ∑ a, r a*d a := by
  classical
  let p : (Σ a, Fin (n a)) → ℝ := fun a => r a.1/(g*(n a.1:ℝ))
  have hzero : ∀ a, n a=0 → r a=0 := by
    intro a ha
    apply le_antisymm _ (hr0 a)
    simpa only [ha,Nat.cast_zero,mul_zero] using hr1 a
  have hp0 : ∀ a, 0 ≤ p a := fun a => div_nonneg (hr0 a.1) (mul_nonneg hg.le (Nat.cast_nonneg _))
  have hp1 : ∀ a, p a ≤ 1 := by
    intro a
    have hn0 : 0 < (n a.1:ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt a.2.isLt)
    exact (div_le_one (mul_pos hg hn0)).mpr (hr1 a.1)
  have hcancel : ∀ a, (n a:ℝ)*(r a/(g*(n a:ℝ)))=r a/g := by
    intro a
    by_cases ha : n a=0
    · simp only [ha,hzero a ha,Nat.cast_zero,mul_zero,zero_div]
    · have hnz : (n a:ℝ) ≠ 0 := by exact_mod_cast ha
      field_simp
  have hps : ∑ a, p a=(Δ:ℝ) := by
    rw [Fintype.sum_sigma]
    simp only [p,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,hcancel]
    rw [← sum_div,hsum]
    exact (div_eq_iff hg.ne').mpr (by nlinarith only [hunit])
  obtain ⟨μ,hcard,hm,_⟩ := WeightedRounding.exact_law p Δ hp0 hp1 hps
  let cost := fun S : Finset (Σ a, Fin (n a)) => g*∑ a ∈ S, d a.1
  have hcost : μ.expect cost=∑ a, r a*d a := by
    have he : ∀ S, cost S=∑ a, (if a ∈ S then (1:ℝ) else 0)*(g*d a.1) := by
      intro S
      simp only [cost,ite_mul,one_mul,zero_mul,sum_ite_mem,univ_inter,mul_sum]
    change μ.expect (fun S => cost S)=_
    simp_rw [he]
    rw [FiniteLaw.expect_sum]
    have hm' : ∀ a, μ.expect (fun S => if a ∈ S then (1:ℝ) else 0)=p a := hm
    simp only [FiniteLaw.expect_mul_right,hm']
    rw [Fintype.sum_sigma]
    simp only [p,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    apply sum_congr rfl
    intro a _
    calc
      _ = ((n a:ℝ)*(r a/(g*(n a:ℝ))))*g*d a := by ring
      _ = _ := by rw [hcancel]; field_simp
  obtain ⟨S,hS,hC⟩ := μ.exists_support_le_expect cost
  refine ⟨S.image (embedSlots n hn),Finset.image_subset_image (subset_univ S),?_,?_⟩
  · rw [mass,card_image_of_injective _ (embedSlots_injective n hn),hcard S hS]
    exact hunit
  · rw [PhysicalPotential.cost,sum_image (fun a _ b _ he => embedSlots_injective n hn he)]
    change (∑ a ∈ S, g*d a.1) ≤ ∑ a, r a*d a
    rw [← mul_sum]
    exact hC.trans_eq hcost

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalGridRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
open Preparation.RationalNearest
variable {τ : ℝ} (q : RationalParameters τ)
variable {F X : Type} [LinearOrder F] [PseudoMetricSpace X] {j : ℕ}

attribute [local instance] OAI.MetricKMedian.FixedBatch.RationalParameters.rationalGridRoundCopyOrder
theorem nearest_spec (d : Fin j → F → ℚ) (A : Finset (Copy (F := F) q.Δ))
    (hA : q.Δ ≤ A.card) (c : Fin j) :
    q.nearest d A c ⊆ A ∧ (q.nearest d A c).card=q.Δ :=
  ⟨(takeNearest_spec (fun a : Copy (F := F) q.Δ => d c a.1) q.Δ A hA).1,
    (takeNearest_spec (fun a : Copy (F := F) q.Δ => d c a.1) q.Δ A hA).2.1⟩

theorem radius_spec (d : Fin j → F → ℚ) (A : Finset (Copy (F := F) q.Δ))
    (hA : q.Δ ≤ A.card) (c : Fin j) :
    (∀ i∈q.nearest d A c, d c i.1 ≤ q.radius d A hA c) ∧
      ∃ i∈q.nearest d A c, q.radius d A hA c=d c i.1 := by
  constructor
  · intro i hi
    exact le_max' ((q.nearest d A c).image (fun a : Copy (F := F) q.Δ => d c a.1))
      (d c i.1) (mem_image.mpr ⟨i,hi,rfl⟩)
  · obtain ⟨i,hi,he⟩ := mem_image.mp (max'_mem
      ((q.nearest d A c).image (fun a : Copy (F := F) q.Δ => d c a.1))
        ((q.nearest_nonempty d A hA c).image _))
    exact ⟨i,hi,he.symm⟩

variable [Fintype F]

theorem roundCounts_spec_oai (hτ : τ<1) (hj : 0<j)
    (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
    (location : F → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (n : F → ℕ) (hn : ∀ a, n a ≤ q.Δ) (hm : 1 ≤ ∑ a, (q.g:ℝ)*(n a:ℝ))
    (r : Fin j → F → ℝ) (hr0 : ∀ c a, 0 ≤ r c a)
    (hr1 : ∀ c a, r c a ≤ (q.g:ℝ)*(n a:ℝ)) (hrsum : ∀ c, ∑ a, r c a=1) :
    ∃ O : Finset F, q.roundCounts d₀ d n=some O ∧ O.Nonempty ∧
      (O.card:ℝ) ≤ (∑ a, (q.g:ℝ)*(n a:ℝ))+(q.allowance:ℝ) ∧
      (score d O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*(∑ c,∑ a, r c a*(d c a:ℝ)) := by
  let A := activeSlots n hn
  have hAm : 1 ≤ mass (q.g:ℝ) A := by rw [activeSlots_mass]; exact hm
  have hA : q.Δ ≤ A.card := by
    rw [← q.unit] at hAm
    exact_mod_cast (mul_le_mul_iff_right₀ q.gpos).mp hAm
  let B := q.nearest d A
  have hB : ∀ c, (B c).Nonempty := q.nearest_nonempty d A hA
  have hBc : ∀ c, (B c).card=q.Δ := fun c => (q.nearest_spec d A hA c).2
  have hBA : ∀ c, B c ⊆ A := fun c => (q.nearest_spec d A hA c).1
  have hBm : ∀ c, mass (q.g:ℝ) (B c)=1 := by intro c; rw [mass,hBc,q.unit]
  let R := q.radius d A hA
  have hdR : ∀ c i, i∈B c → d c i.1 ≤ R c := fun c => (q.radius_spec d A hA c).1
  have hatt : ∀ c, ∃ i∈B c, R c=d c i.1 := fun c => (q.radius_spec d A hA c).2
  have hR : ∀ c, 0 ≤ R c := by
    intro c
    obtain ⟨i,hi,he⟩ := hatt c
    rw [he]
    exact_mod_cast (hd c i.1 ▸ dist_nonneg)
  have hcost : ∀ c, PhysicalPotential.cost (q.g:ℝ)
      (fun i : Copy (F := F) q.Δ => dist (client c) (location i.1)) (B c) ≤
        ∑ a, r c a*(d c a:ℝ) := by
    intro c
    obtain ⟨S,hS,hmS,hcS⟩ := assignment_copies n hn (r c) (fun a => (d c a:ℝ))
      q.gpos q.unit (hr0 c) (hr1 c) (hrsum c)
    have hSc : S.card=q.Δ := by
      have he : (q.g:ℝ)*(S.card:ℝ)=(q.g:ℝ)*(q.Δ:ℝ) := hmS.trans q.unit.symm
      exact_mod_cast (mul_left_cancel₀ q.gpos.ne' he)
    have hl := (takeNearest_spec (fun a => d c a.1) q.Δ A hA).2.2 S hS hSc
    have hlR : (∑ a∈B c,(d c a.1:ℝ)) ≤ ∑ a∈S,(d c a.1:ℝ) := by exact_mod_cast hl
    calc
      _ = (q.g:ℝ)*∑ a∈B c,(d c a.1:ℝ) := by simp only [PhysicalPotential.cost,hd,mul_sum]
      _ ≤ (q.g:ℝ)*∑ a∈S,(d c a.1:ℝ) := mul_le_mul_of_nonneg_left hlR q.gpos.le
      _ ≤ _ := by simpa only [← mul_sum,PhysicalPotential.cost] using hcS
  obtain ⟨O,hO,hnO,hcard,hscore⟩ := q.selectCompleted_spec hτ hj d₀ d location client hd₀ hd
    A B R hB hAm hBA hR hBm hdR hatt
  refine ⟨O,?_,hnO,?_,hscore.trans ?_⟩
  · unfold roundCounts
    rw [dite_eq_left hn]
    change (if hA : q.Δ ≤ A.card then _ else none)=_
    rw [dite_eq_left hA]
    exact hO
  · simpa only [A,activeSlots_mass] using hcard
  · apply mul_le_mul_of_nonneg_left (sum_le_sum (fun c _ => hcost c))
    apply div_nonneg _ (sub_pos.mpr hτ).le
    have hτ0 : 0 ≤ τ := by
      have hh := q.failure
      have hnum : 0 ≤ (q.T:ℝ)*(96*(q.Δ:ℝ)^2*(q.β:ℝ)/
          ((2*(q.h:ℝ)*(q.g:ℝ))*(q.φ:ℝ)^2*(q.g:ℝ))) := by
        have hg := q.gpos; have hh := q.hpos; have hβ := q.βpos
        positivity
      exact hnum.trans hh
    positivity

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts_spec_oai := @OAI.MetricKMedian.FixedBatch.RationalParameters.roundCounts_spec_oai
