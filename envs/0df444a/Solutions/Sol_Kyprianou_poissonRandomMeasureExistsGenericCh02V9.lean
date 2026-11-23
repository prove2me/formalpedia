-- Prove2me | solution 1 for Kyprianou.poissonRandomMeasureExistsGenericCh02V9
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:25:10.275722+00:00
-- url     : https://prove2.me/submissions/e0157748-f0d3-43a4-ab2b-6fc765ac93f4

import Mathlib
import Definitions.Def_Kyprianou_Ch02_AbstractPoissonRandomMeasureV8
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_exists_isPoissonPointFamily
import Theorems.Thm_Kyprianou_Ch02_pointFamilyFinitePRMCoreCh02V1
import Theorems.Thm_Kyprianou_Ch02_pointFamilyPRMResidualV3
import Theorems.Thm_Kyprianou_Ch02_emptyMarkPRMExistsV3

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

private theorem tsum_natCast_pathwise_integer_or_top
    (f : ℕ → ℕ) :
    (∃ n : ℕ, (∑' k, (f k : ENNReal)) = (n : ENNReal)) ∨
      (∑' k, (f k : ENNReal)) = ⊤ := by
  classical
  let t : ENNReal := ∑' k, (f k : ENNReal)
  by_cases ht : t = ⊤
  · exact Or.inr ht
  · obtain ⟨b, hb⟩ := ENNReal.exists_nat_gt ht
    let s : ℕ → ℕ := fun n => ∑ k ∈ Finset.range n, f k
    have hsub (n : ℕ) : (s n : ENNReal) ≤ t := by
      dsimp [s, t]
      rw [Nat.cast_sum]
      exact ENNReal.sum_le_tsum (Finset.range n)
    have hbd (n : ℕ) : s n ≤ b := by
      exact_mod_cast (hsub n).trans hb.le
    have hfin : (Set.range s).Finite :=
      (Set.finite_Iic b).subset (by rintro x ⟨n, rfl⟩; exact hbd n)
    obtain ⟨v, hv, hmax⟩ :=
      hfin.exists_maximal (⟨s 0, ⟨0, rfl⟩⟩)
    have hupper (n : ℕ) : s n ≤ v := by
      by_contra hn
      have hlt : v < s n := lt_of_not_ge hn
      have hback : s n ≤ v := hmax ⟨n, rfl⟩ hlt.le
      exact (not_lt_of_ge hback) hlt
    have ht_iSup : t = ⨆ n : ℕ, (s n : ENNReal) := by
      dsimp [t, s]
      rw [ENNReal.tsum_eq_iSup_nat]
      simp only [Nat.cast_sum]
    have hiSup : (⨆ n : ℕ, (s n : ENNReal)) = (v : ENNReal) := by
      apply le_antisymm
      · exact iSup_le fun n => Nat.cast_le.mpr (hupper n)
      · obtain ⟨n, hn⟩ := hv
        simpa only [hn] using (le_iSup (fun n => (s n : ENNReal)) n)
    exact Or.inl ⟨v, ht_iSup.trans hiSup⟩

private theorem poissonRandomMeasure_pathwise_integer_or_top
    {Ω E : Type} [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (ω : Ω) (A : Set E) (hA : MeasurableSet A) :
    (∃ n : ℕ, ProbabilityTheory.poissonRandomMeasure K Y ω A = (n : ENNReal)) ∨
      ProbabilityTheory.poissonRandomMeasure K Y ω A = ⊤ := by
  rw [ProbabilityTheory.poissonRandomMeasure_apply hA]
  exact tsum_natCast_pathwise_integer_or_top
    (fun k => ProbabilityTheory.thinnedCount K Y A k ω)


theorem solution
    (E : Type) [MeasurableSpace E]
    (m : Measure E) [SigmaFinite m] :
    ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        ∃ N : Ω → Measure E,
          Kyprianou.Ch02.IsAbstractPoissonRandomMeasureCh02V8 P m N
     := by
  classical
  by_cases hE : Nonempty E
  · letI : Nonempty E := hE
    obtain ⟨Ω, mΩ, P, K, Y, hP, hd⟩ :=
      ProbabilityTheory.exists_isPoissonPointFamily m
    letI : MeasurableSpace Ω := mΩ
    letI : IsProbabilityMeasure P := hP
    obtain ⟨hmeas, hlaw, _⟩ :=
      Kyprianou.Ch02.pointFamilyFinitePRMCoreCh02V1 P m K Y hd
    obtain ⟨hnat, hinfinite, hind⟩ :=
      Kyprianou.Ch02.pointFamilyPRMResidualV3 P m K Y hd
    refine ⟨Ω, mΩ, P, hP, ProbabilityTheory.poissonRandomMeasure K Y, ?_⟩
    refine ⟨?_, ?_⟩
    · exact ⟨hmeas, hnat, hlaw, hinfinite, hind⟩
    · exact Filter.Eventually.of_forall
        (fun ω A hA => poissonRandomMeasure_pathwise_integer_or_top K Y ω A hA)
  · obtain ⟨Ω, mΩ, P, hP, N, hV3⟩ :=
      Kyprianou.Ch02.emptyMarkPRMExistsV3 E m hE
    letI : MeasurableSpace Ω := mΩ
    letI : IsProbabilityMeasure P := hP
    refine ⟨Ω, mΩ, P, hP, N, ⟨hV3, ?_⟩⟩
    haveI : IsEmpty E := ⟨fun x => hE ⟨x⟩⟩
    filter_upwards [] with ω
    intro A hA
    left
    exact ⟨0, by simp [Measure.apply_eq_zero_of_isEmpty (N ω) A]⟩
