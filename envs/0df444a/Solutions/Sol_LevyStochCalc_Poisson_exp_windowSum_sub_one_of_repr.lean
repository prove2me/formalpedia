-- Prove2me | solution 1 for LevyStochCalc.Poisson.exp_windowSum_sub_one_of_repr
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:27:16.056378+00:00
-- url     : https://prove2.me/submissions/fd1fbb76-ff32-439f-8e9e-3ea34fb476af

import Definitions.Def_LevyStochCalc_Poisson_ChainRule_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jump chain rule for a Poisson random measure

A product over a finite set whose factors are ordered by a key telescopes: the product minus one
is the sum, over the factors, of the product of the earlier ones times the increment of that
factor. On a set of finite reference intensity a Poisson random measure is a finite sum of unit
masses at distinct times, so the exponential of an integral against it obeys that telescoping,
which is the chain rule the exponential family needs.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

section Telescope

variable {α : Type*} [DecidableEq α] {K : Type*} [LinearOrder K] {M : Type*} [CommRing M]

end Telescope

section Pathwise

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]


omit [MeasurableSpace.CountablyGenerated E] in
open scoped Classical in

open scoped Classical in
theorem prod_sub_one_eq_sum' {α : Type*} {K : Type*} [LinearOrder K] {M : Type*} [CommRing M]
    (key : α → K) (z : α → M) :
    ∀ s : Finset α, Set.InjOn key (s : Set α) →
      (∏ p ∈ s, z p) - 1
        = ∑ p ∈ s, (∏ q ∈ s.filter (fun q => key q < key p), z q) * (z p - 1) := by
  intro s
  induction s using Finset.induction_on_max_value key with
  | empty => intro _; simp
  | insert a s ha hmax ih =>
    intro hinj
    have hinj' : Set.InjOn key (s : Set α) :=
      hinj.mono (by simp [Finset.coe_insert, Set.subset_insert])
    have hlt : ∀ x ∈ s, key x < key a := by
      intro x hx
      refine lt_of_le_of_ne (hmax x hx) ?_
      intro h
      have := hinj (by simp [hx]) (by simp) h
      exact ha (this ▸ hx)
    have hfa : (insert a s).filter (fun q => key q < key a) = s := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, h⟩
        · exact absurd h (lt_irrefl _)
        · exact hx
      · intro hx; exact ⟨Or.inr hx, hlt x hx⟩
    have hfp : ∀ p ∈ s, (insert a s).filter (fun q => key q < key p)
        = s.filter (fun q => key q < key p) := by
      intro p hp
      rw [Finset.filter_insert, if_neg (not_lt.mpr (hmax p hp))]
    rw [Finset.sum_insert ha, Finset.prod_insert ha, hfa,
      Finset.sum_congr rfl (fun p hp => by rw [hfp p hp]), ← ih hinj']
    ring


omit [MeasurableSpace.CountablyGenerated E] in
open scoped Classical in
theorem _root_.solution (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (h : ℝ × E → ℝ) {J : Set ℝ} (hJm : MeasurableSet J)
    (hJ0 : J ⊆ Set.Ioi 0) (hJ : ∀ u ∈ J, Set.Ioo (0 : ℝ) u ⊆ J) (ω : Ω)
    (hsrepex : ∃ s : Finset (ℝ × E), (N.N ω).restrict (B ∩ J ×ˢ Set.univ)
      = ∑ p ∈ s, ((N.N ω).restrict (B ∩ J ×ˢ Set.univ)) {p} • Measure.dirac p)
    (hn : ∃ k : ℕ, N.N ω (B ∩ J ×ˢ Set.univ) = k)
    (hIV : Probability.IsIntegerValued ((N.N ω).restrict (B ∩ J ×ˢ Set.univ)))
    (hsimple : ∀ t : ℝ, N.N ω (B ∩ ({t} : Set ℝ) ×ˢ Set.univ) ≤ 1) :
    Complex.exp (Complex.I * ((∫ p in B ∩ J ×ˢ Set.univ, h p ∂(N.N ω) : ℝ) : ℂ)) - 1
      = ∫ p in B ∩ J ×ˢ Set.univ,
          Complex.exp (Complex.I * (windowSumStrict N B h p.1 ω : ℂ))
            * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂(N.N ω) := by
  classical
  set R := B ∩ J ×ˢ (Set.univ : Set E) with hR
  have hRm : MeasurableSet R := hB.inter (hJm.prod MeasurableSet.univ)
  set μ := (N.N ω).restrict R with hμ
  obtain ⟨s, hs⟩ := hsrepex
  obtain ⟨k, hk⟩ := hn
  haveI : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ, hk]; exact ENNReal.natCast_lt_top k⟩
  -- atoms of μ have mass 0 or 1
  have hsub : ∀ p : ℝ × E, {p} ∩ R ⊆ B ∩ ({p.1} : Set ℝ) ×ˢ (Set.univ : Set E) := by
    rintro p x ⟨hx, hxR⟩
    rw [Set.mem_singleton_iff] at hx; subst hx
    exact ⟨hxR.1, rfl, trivial⟩
  have hμp : ∀ p, μ {p} = N.N ω ({p} ∩ R) := fun p => by
    rw [hμ, Measure.restrict_apply (measurableSet_singleton p)]
  have hmass : ∀ p, μ {p} = 0 ∨ μ {p} = 1 := by
    intro p
    obtain ⟨n, hn'⟩ := hIV {p} (measurableSet_singleton p)
    have hle : μ {p} ≤ 1 := by
      rw [hμp]; exact (measure_mono (hsub p)).trans (hsimple p.1)
    rw [hn'] at hle ⊢
    have : n ≤ 1 := by exact_mod_cast hle
    interval_cases n <;> simp
  set s' := s.filter (fun p => μ {p} = 1) with hs'
  -- integrals against μ are sums over s'
  have hsum : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (g : ℝ × E → F),
      ∫ a, g a ∂μ = ∑ p ∈ s', g p := by
    intro F _ _ _ g
    rw [integral_of_eq_sum_dirac' hs g, hs', Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rcases hmass p with h0 | h1
    · rw [h0, if_neg (by simp)]; simp
    · rw [h1, if_pos rfl]; simp
  have hmemR : ∀ p ∈ s', p ∈ R := by
    intro p hp
    have h1 : μ {p} = 1 := (Finset.mem_filter.mp hp).2
    by_contra hpR
    have : μ {p} = 0 := by
      rw [hμp, Set.singleton_inter_eq_empty.mpr hpR, measure_empty]
    rw [this] at h1; exact zero_ne_one h1
  -- the strict window sum at an atom
  have hW : ∀ p ∈ s', windowSumStrict N B h p.1 ω = ∑ q ∈ s'.filter (fun q => q.1 < p.1), h q := by
    intro p hp
    have hpR := hmemR p hp
    have hpJ : p.1 ∈ J := hpR.2.1
    set S := B ∩ Set.Ioo (0 : ℝ) p.1 ×ˢ (Set.univ : Set E) with hS
    have hSm : MeasurableSet S := hB.inter (measurableSet_Ioo.prod MeasurableSet.univ)
    have hSR : S ⊆ R := fun x hx => ⟨hx.1, hJ p.1 hpJ hx.2.1, trivial⟩
    have e1 : windowSumStrict N B h p.1 ω = ∫ x in S, h x ∂μ := by
      rw [windowSumStrict, hμ, Measure.restrict_restrict hSm, Set.inter_eq_left.mpr hSR]
    rw [e1, ← integral_indicator hSm, hsum, Finset.sum_filter (fun q : ℝ × E => q.1 < p.1)]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hqR := hmemR q hq
    have hq0 : 0 < q.1 := hJ0 hqR.2.1
    by_cases hlt : q.1 < p.1
    · rw [if_pos hlt, Set.indicator_of_mem (show q ∈ S from ⟨hqR.1, ⟨hq0, hlt⟩, trivial⟩)]
    · rw [if_neg hlt, Set.indicator_of_notMem (fun hqS => hlt hqS.2.1.2)]
  -- injectivity of the time key on s'
  have hinj : Set.InjOn Prod.fst (s' : Set (ℝ × E)) := by
    intro p hp q hq hpq
    by_contra hne
    have hp1 : μ {p} = 1 := (Finset.mem_filter.mp hp).2
    have hq1 : μ {q} = 1 := (Finset.mem_filter.mp hq).2
    have hpair : μ {p, q} = 2 := by
      rw [Set.insert_eq, measure_union (Set.disjoint_singleton.mpr hne) (measurableSet_singleton q),
        hp1, hq1]; norm_num
    have hle : μ {p, q} ≤ 1 := by
      rw [hμ, Measure.restrict_apply ((measurableSet_singleton q).insert p)]
      refine (measure_mono ?_).trans (hsimple p.1)
      rintro x ⟨hx, hxR⟩
      rcases hx with rfl | hx
      · exact ⟨hxR.1, rfl, trivial⟩
      · rw [Set.mem_singleton_iff] at hx; subst hx
        exact ⟨hxR.1, hpq.symm, trivial⟩
    rw [hpair] at hle; norm_num at hle
  -- assemble
  show Complex.exp (Complex.I * ((∫ p, h p ∂μ : ℝ) : ℂ)) - 1
      = ∫ p, Complex.exp (Complex.I * (windowSumStrict N B h p.1 ω : ℂ))
          * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂μ
  rw [hsum, hsum]
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]
  rw [prod_sub_one_eq_sum' Prod.fst (fun p => Complex.exp (Complex.I * (h p : ℂ))) s' hinj]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [hW p hp]
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]


