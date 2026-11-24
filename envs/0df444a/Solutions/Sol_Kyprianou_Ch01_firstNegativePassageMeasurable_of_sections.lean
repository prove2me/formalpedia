-- Prove2me | solution 1 for Kyprianou.Ch01.firstNegativePassageMeasurable_of_sections
-- status  : ACCEPTED   (disprove)
-- author  : @pageman
-- created : 2026-11-24T20:07:48.562487+00:00
-- url     : https://prove2.me/submissions/02bee744-d60e-411d-afe5-9d32e193c985

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Card
import Mathlib.Analysis.Real.Cardinality
import Mathlib.SetTheory.Cardinal.Continuum
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology Cardinal MeasurableSpace
open scoped NNReal ENNReal Cardinal
set_option autoImplicit false

/-- Borel σ-algebra on ℝ is strictly smaller than the power set. -/
theorem exists_not_measurableSet_real : ∃ S : Set ℝ, ¬ MeasurableSet S := by
  let G : Set (Set ℝ) := ⋃ a : ℚ, {Iio (a : ℝ)}
  have hGle : #G ≤ 𝔠 := by
    have : G = range fun a : ℚ => (Iio (a : ℝ) : Set ℝ) := by
      ext s; simp [G, mem_range]
    rw [this]
    calc
      #(range fun a : ℚ => (Iio (a : ℝ) : Set ℝ)) ≤ #ℚ := mk_range_le
      _ = ℵ₀ := by simp
      _ ≤ 𝔠 := aleph0_le_continuum
  have hle : #{ t : Set ℝ | MeasurableSet t } ≤ 𝔠 := by
    have hgen : borel ℝ = generateFrom G := by
      simpa [G] using Real.borel_eq_generateFrom_Iio_rat
    have hspace : Real.measurableSpace = generateFrom G :=
      (@BorelSpace.measurable_eq ℝ _ _ _).trans hgen
    have heq_card :
        #{ t : Set ℝ | MeasurableSet t } =
          #{ t | MeasurableSet[generateFrom G] t } := by
      refine mk_congr ?_
      exact {
        toFun := fun ⟨t, ht⟩ =>
          ⟨t, by
            change MeasurableSet[generateFrom G] t
            rwa [← hspace]⟩
        invFun := fun ⟨t, ht⟩ =>
          ⟨t, by
            change MeasurableSet[Real.measurableSpace] t
            rwa [hspace]⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
      }
    rw [heq_card]
    exact cardinal_measurableSet_le_continuum hGle
  refine (not_forall.1 ?_).imp fun S hS => hS
  intro hforall
  have heq : #{ t : Set ℝ | MeasurableSet t } = #(Set ℝ) := by
    refine mk_congr ⟨fun ⟨t, _⟩ => t, fun t => ⟨t, hforall t⟩, fun _ => rfl, fun _ => rfl⟩
  have hlt : 𝔠 < #(Set ℝ) := by
    rw [mk_set, mk_real]
    exact cantor _
  exact (not_le_of_gt (hlt.trans_eq heq.symm)) hle

private lemma measurableSet_inter_singleton (N : Set ℝ) (a : ℝ) :
    MeasurableSet (N ∩ ({a} : Set ℝ)) :=
  (N ∩ ({a} : Set ℝ)).toFinite.measurableSet

/-- A nonmeasurable subset of `(0, ∞)`. -/
theorem exists_not_measurableSet_Ioi_zero : ∃ N : Set ℝ, N ⊆ Ioi (0 : ℝ) ∧ ¬ MeasurableSet N := by
  obtain ⟨N0, hN0⟩ := exists_not_measurableSet_real
  by_cases hpos : MeasurableSet (N0 ∩ Ioi (0 : ℝ))
  · have hnonpos : ¬ MeasurableSet (N0 ∩ Iic (0 : ℝ)) := by
      intro h
      have : MeasurableSet N0 := by
        have heq : N0 = (N0 ∩ Ioi 0) ∪ (N0 ∩ Iic 0) := by
          ext x
          by_cases hx : (0 : ℝ) < x
          · simp [hx]
          · have : x ≤ 0 := le_of_not_gt hx
            simp [hx, this]
        rw [heq]
        exact hpos.union h
      exact hN0 this
    have hio : ¬ MeasurableSet (N0 ∩ Iio (0 : ℝ)) := by
      intro h
      have : N0 ∩ Iic 0 = (N0 ∩ Iio 0) ∪ (N0 ∩ ({0} : Set ℝ)) := by
        ext x
        simp only [mem_inter_iff, mem_Iic, mem_Iio, mem_singleton_iff, mem_union]
        constructor
        · intro ⟨hxN, hxle⟩
          rcases eq_or_lt_of_le hxle with rfl | hlt
          · exact Or.inr ⟨hxN, rfl⟩
          · exact Or.inl ⟨hxN, hlt⟩
        · intro h
          rcases h with ⟨hxN, hlt⟩ | ⟨hxN, rfl⟩
          · exact ⟨hxN, le_of_lt hlt⟩
          · exact ⟨hxN, le_rfl⟩
      exact hnonpos (by rw [this]; exact h.union (measurableSet_inter_singleton N0 0))
    refine ⟨(fun x : ℝ => -x) '' (N0 ∩ Iio 0), ?_, ?_⟩
    · intro y hy
      rcases (mem_image _ _ _).1 hy with ⟨x, ⟨_, hxlt⟩, rfl⟩
      exact neg_pos.mpr (mem_Iio.mp hxlt)
    · intro hIm
      have hembed := (Homeomorph.neg ℝ).measurableEmbedding
      exact hio ((hembed.measurableSet_image (s := N0 ∩ Iio 0)).1 hIm)
  · exact ⟨N0 ∩ Ioi 0, inter_subset_right, hpos⟩

/-- Diagonal spike on a non-Borel set: sections measurable, passage clock not. -/
theorem solution
    (h : ∀ {Ω : Type} [MeasurableSpace Ω]
        (X : ℝ≥0 → Ω → ℤ)
        (_hX : ∀ t : ℝ≥0, Measurable (X t)),
        Measurable (fun ω : Ω => firstNegativePassage X ω)) :
    False := by
  classical
  obtain ⟨N, hNpos, hN⟩ := exists_not_measurableSet_Ioi_zero
  let X : ℝ≥0 → ℝ → ℤ := fun t ω =>
    if 0 < t ∧ (t : ℝ) = ω ∧ ω ∈ N then (-1 : ℤ) else 1
  have hX : ∀ t : ℝ≥0, Measurable (X t) := by
    intro t
    refine Measurable.ite ?_ measurable_const measurable_const
    · change MeasurableSet {ω : ℝ | 0 < t ∧ (t : ℝ) = ω ∧ ω ∈ N}
      by_cases ht : 0 < t
      · have : {ω : ℝ | 0 < t ∧ (t : ℝ) = ω ∧ ω ∈ N} = {(t : ℝ)} ∩ N := by
          ext ω; simp [ht, eq_comm]
        rw [this]
        convert measurableSet_inter_singleton N (t : ℝ) using 1
        ext; simp [and_comm]
      · have : {ω : ℝ | 0 < t ∧ (t : ℝ) = ω ∧ ω ∈ N} = ∅ := by
          ext ω; simp [ht]
        simpa [this]
  -- Evaluate the passage clock
  have hτ :
      ∀ ω : ℝ,
        firstNegativePassage X ω =
          if ω ∈ N then ((Real.toNNReal ω : ℝ≥0) : WithTop ℝ≥0) else ⊤ := by
    intro ω
    by_cases hωN : ω ∈ N
    · have hωpos : 0 < ω := hNpos hωN
      let tω : ℝ≥0 := Real.toNNReal ω
      have htω : (tω : ℝ) = ω := Real.coe_toNNReal ω (le_of_lt hωpos)
      have htωpos : 0 < tω := by
        change (0 : ℝ) < tω
        simpa [tω, htω] using hωpos
      have hmem : tω ∈ {t : ℝ≥0 | 0 < t ∧ X t ω < 0} := by
        simp [htωpos, X, htω, hωN]
      have huniq : {t : ℝ≥0 | 0 < t ∧ X t ω < 0} = {tω} := by
        ext t
        simp only [mem_setOf_eq, mem_singleton_iff]
        constructor
        · intro ⟨ht, hXneg⟩
          have : (t : ℝ) = ω ∧ ω ∈ N := by
            by_cases hcond : 0 < t ∧ (t : ℝ) = ω ∧ ω ∈ N
            · exact hcond.2
            · simp [X, hcond] at hXneg
          exact NNReal.coe_injective (this.1.trans htω.symm)
        · intro rfl
          exact ⟨htωpos, by simp [X, htωpos, htω, hωN]⟩
      have hex : ∃ t : ℝ≥0, 0 < t ∧ X t ω < 0 := ⟨tω, htωpos, by simp [X, htωpos, htω, hωN]⟩
      have hsInf : sInf ({t : ℝ≥0 | 0 < t ∧ X t ω < 0} : Set ℝ≥0) = tω := by
        rw [huniq, csInf_singleton]
      simp only [firstNegativePassage, hex, ↓reduceIte, hsInf, tω, hωN]
    · have hex : ¬ ∃ t : ℝ≥0, 0 < t ∧ X t ω < 0 := by
        intro ⟨t, ht, hXneg⟩
        have : (t : ℝ) = ω ∧ ω ∈ N := by
          by_cases hcond : 0 < t ∧ (t : ℝ) = ω ∧ ω ∈ N
          · exact hcond.2
          · simp [X, hcond] at hXneg
        exact hωN this.2
      simp [firstNegativePassage, hex, hωN]
  have hmeas : Measurable (fun ω : ℝ => firstNegativePassage X ω) := h (Ω := ℝ) X hX
  have : MeasurableSet N := by
    have hpre :
        N = (fun ω : ℝ => firstNegativePassage X ω) ⁻¹' ({⊤} : Set (WithTop ℝ≥0))ᶜ := by
      ext ω
      simp only [mem_preimage, mem_compl_iff, mem_singleton_iff]
      constructor
      · intro hωN
        rw [hτ ω, if_pos hωN]
        exact nofun
      · intro hne
        by_cases hωN : ω ∈ N
        · exact hωN
        · rw [hτ ω, if_neg hωN] at hne
          exact (hne rfl).elim
    rw [hpre]
    exact hmeas (measurableSet_singleton ⊤).compl
  exact hN this
