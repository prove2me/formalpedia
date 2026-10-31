-- Prove2me | solution 1 for MinBuying.finite_support_wellposed
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:37:17.149984+00:00
-- url     : https://prove2.me/submissions/89c5fa66-2632-4b9c-8360-a1b493db17f6

import Definitions.Def_MinBuying_Model

open MeasureTheory Set MinBuying
open scoped BigOperators ENNReal
noncomputable section
namespace MinBuyingFiniteSupportProof

private lemma finite_support_integrable {n : ℕ} (μ : JointLaw n) [IsFiniteMeasure μ]
    (S : Finset (Valuations n)) (hS : ∀ᵐ v ∂μ, v ∈ S) (f : Valuations n → ℝ) :
    Integrable f μ := by
  rw [Measure.ae_mem_finset_iff.mp hS]
  apply integrable_finsetSum_measure.mpr
  intro v _
  exact (integrable_dirac (by simp)).smul_measure (measure_ne_top μ {v})

private lemma round_scalar (W : Finset ℝ) (hW : W.Nonempty) (h0 : 0 ∈ W)
    (p : ℝ) (hp : 0 ≤ p) :
    ∃ q : ℝ, q ∈ insert (W.max' hW+1) W ∧ 0 ≤ q ∧
      ∀ x ∈ W, (q ≤ x ↔ p ≤ x) ∧ (q ≤ x → p ≤ q) := by
  classical
  let T := insert (W.max' hW+1) W
  let U := T.filter (fun q => p ≤ q)
  by_cases hU : U.Nonempty
  · have hu : U.min' hU ∈ U := Finset.min'_mem _ _
    have hq : p ≤ U.min' hU := (Finset.mem_filter.mp hu).2
    refine ⟨U.min' hU,?_,?_,?_⟩
    · exact (Finset.mem_filter.mp hu).1
    · exact hp.trans hq
    · intro x hx
      refine ⟨⟨fun h => hq.trans h,?_⟩,fun _ => hq⟩
      intro hpx
      exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hx,hpx⟩)
  · let q := W.max' hW+1
    have hM : 0 ≤ W.max' hW := Finset.le_max' _ _ h0
    have hpq : q < p := by
      by_contra h
      exact hU ⟨q,Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _,le_of_not_gt h⟩⟩
    refine ⟨q,Finset.mem_insert_self _ _,by dsimp [q];linarith,?_⟩
    intro x hx
    have hxq : x < q := by
      have h := Finset.le_max' W x hx
      dsimp [q]
      linarith
    refine ⟨?_,fun h => (not_le_of_gt hxq h).elim⟩
    exact iff_of_false (not_le_of_gt hxq) (not_le_of_gt (hxq.trans hpq))

private lemma payment_round {n : ℕ} (p q : Prices n) (v : Valuations n)
    (ha : ∀ i, (q i ≤ v i ↔ p i ≤ v i) ∧ (q i ≤ v i → p i ≤ q i)) :
    payment p v ≤ payment q v := by
  classical
  have hs : affordable p v = affordable q v := by
    ext i
    simp only [affordable,Finset.mem_filter,Finset.mem_univ,true_and]
    exact (ha i).1.symm
  by_cases hq : (affordable q v).Nonempty
  · have hp : (affordable p v).Nonempty := hs.symm ▸ hq
    rw [payment,dif_pos hp,payment,dif_pos hq]
    apply Finset.le_inf'
    intro i hi
    have hpi : i ∈ affordable p v := hs.symm ▸ hi
    exact (Finset.inf'_le p hpi).trans ((ha i).2 (Finset.mem_filter.mp hi).2)
  · have hp : ¬ (affordable p v).Nonempty := by rwa [hs]
    simp only [payment,dif_neg hp,dif_neg hq,le_refl]

end MinBuyingFiniteSupportProof

open MinBuyingFiniteSupportProof

theorem solution (n : ℕ) (μ : JointLaw n) (hμ : IsProbabilityMeasure μ)
    (S : Finset (Valuations n)) (hS : ∀ᵐ v ∂μ, v ∈ S)
    (hpos : ∃ p : ℝ, 0 ≤ p ∧ 0 < uniformRevenue μ p) : WellPosed μ := by
  classical
  haveI : IsProbabilityMeasure μ := hμ
  let W : Finset ℝ := insert 0 (S.biUnion (fun v => Finset.univ.image v))
  have h0 : 0 ∈ W := Finset.mem_insert_self _ _
  have hW : W.Nonempty := ⟨0,h0⟩
  let T := (insert (W.max' hW+1) W).filter (fun q => 0 ≤ q)
  have hT0 : 0 ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem h0,le_rfl⟩
  haveI : Nonempty T := ⟨⟨0,hT0⟩⟩
  have hval : ∀ v ∈ S, ∀ i : Fin n, v i ∈ W := by
    intro v hv i
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
  have hround : ∀ p : ℝ, 0 ≤ p → ∃ q : T,
      ∀ v ∈ S, ∀ i : Fin n, ((q:ℝ) ≤ v i ↔ p ≤ v i) ∧ ((q:ℝ) ≤ v i → p ≤ q) := by
    intro p hp
    obtain ⟨q,hqT,hq0,hq⟩ := MinBuyingFiniteSupportProof.round_scalar W hW h0 p hp
    exact ⟨⟨q,Finset.mem_filter.mpr ⟨hqT,hq0⟩⟩,fun v hv i => hq (v i) (hval v hv i)⟩
  have hDdom : ∀ p : Prices n, FeasiblePrices p → ∃ q : Fin n → T,
      Revenue μ p ≤ Revenue μ (fun i => q i) := by
    intro p hp
    choose q hq using fun i => hround (p i) (hp i)
    refine ⟨q,?_⟩
    apply integral_mono_ae (MinBuyingFiniteSupportProof.finite_support_integrable μ S hS _)
      (MinBuyingFiniteSupportProof.finite_support_integrable μ S hS _)
    filter_upwards [hS] with v hv
    exact MinBuyingFiniteSupportProof.payment_round p (fun i => q i) v (fun i => hq i v hv i)
  have hUdom : ∀ p : ℝ, 0 ≤ p → ∃ q : T, uniformRevenue μ p ≤ uniformRevenue μ q := by
    intro p hp
    obtain ⟨q,hq⟩ := hround p hp
    refine ⟨q,?_⟩
    apply integral_mono_ae (MinBuyingFiniteSupportProof.finite_support_integrable μ S hS _)
      (MinBuyingFiniteSupportProof.finite_support_integrable μ S hS _)
    filter_upwards [hS] with v hv
    exact MinBuyingFiniteSupportProof.payment_round (fun _ => p) (fun _ => q) v (hq v hv)
  obtain ⟨q,_,hmaxD⟩ := Finset.univ.exists_max_image
    (fun q : Fin n → T => Revenue μ (fun i => q i)) Finset.univ_nonempty
  obtain ⟨t,_,hmaxU⟩ := Finset.univ.exists_max_image
    (fun t : T => uniformRevenue μ t) Finset.univ_nonempty
  have hq : FeasiblePrices (fun i => (q i : ℝ)) := fun i => (Finset.mem_filter.mp (q i).property).2
  have ht : 0 ≤ (t:ℝ) := (Finset.mem_filter.mp t.property).2
  have hAD : ∀ r ∈ differentiatedValues μ, r ≤ Revenue μ (fun i => q i) := by
    rintro r ⟨p,hp,rfl⟩
    obtain ⟨q',hdom⟩ := hDdom p hp
    exact hdom.trans (hmaxD q' (Finset.mem_univ _))
  have hAU : ∀ r ∈ uniformValues μ, r ≤ uniformRevenue μ t := by
    rintro r ⟨p,hp,rfl⟩
    obtain ⟨t',hdom⟩ := hUdom p hp
    exact hdom.trans (hmaxU t' (Finset.mem_univ _))
  have hDb : BddAbove (differentiatedValues μ) := ⟨_,hAD⟩
  have hUb : BddAbove (uniformValues μ) := ⟨_,hAU⟩
  have hDm : Revenue μ (fun i => (q i:ℝ)) ∈ differentiatedValues μ := ⟨_,hq,rfl⟩
  have hUm : uniformRevenue μ (t:ℝ) ∈ uniformValues μ := ⟨_,ht,rfl⟩
  have hD : Revenue μ (fun i => (q i:ℝ)) = DPRevenue μ :=
    le_antisymm (le_csSup hDb hDm) (csSup_le ⟨_,hDm⟩ hAD)
  have hU : uniformRevenue μ (t:ℝ) = UPRevenue μ :=
    le_antisymm (le_csSup hUb hUm) (csSup_le ⟨_,hUm⟩ hAU)
  refine ⟨hDb,hUb,⟨_,hq,hD⟩,⟨_,ht,hU⟩,?_⟩
  obtain ⟨p,hp,hpos⟩ := hpos
  exact hpos.trans_le (le_csSup hUb ⟨p,hp,rfl⟩)
