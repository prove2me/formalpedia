-- Prove2me | solution 1 for MasulloGRH.dSequence_vitali_covering
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:31:16.986907+00:00
-- url     : https://prove2.me/submissions/7dcdf025-8104-4382-8567-19e7c468ff0f

import Mathlib
import Definitions.Def_MasulloGRH_DSequences

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

open MasulloGRH

theorem solution
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (U : ℕ → Set G) (C : ℝ) (hU : IsDSequence μ U C)
    (F' : Set (Set G)) (B : Set G) (hB : B.Nonempty) (hBU : μ (B * U 0) < ⊤)
    (hcover : ∀ x ∈ B, ∃ k, x • U k ∈ F') :
    ∃ s : Finset (G × ℕ), (∀ a ∈ s, a.1 ∈ B ∧ a.1 • U a.2 ∈ F') ∧
      (↑s : Set (G × ℕ)).PairwiseDisjoint (fun a => a.1 • U a.2) ∧
      μ B / ENNReal.ofReal C < ∑ a ∈ s, μ (U a.2) := by
  classical
  have hanti : Antitone U := antitone_nat_of_succ_le hU.antitone
  -- the family of admissible translates, indexed by (centre, index)
  let translate : G × ℕ → Set G := fun a => a.1 • U a.2
  let t : Set (G × ℕ) := {a | a.1 ∈ B ∧ translate a ∈ F'}
  -- the size function `2⁻ᵏ`: a comparison of sizes up to the factor `3/2` is a comparison of indices
  let priority : G × ℕ → ℝ := fun a => (1 / 2 : ℝ) ^ a.2
  obtain ⟨u, hut, hud, hmatch⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement translate t priority (3 / 2)
      (by norm_num) (fun a _ => by dsimp only [priority]; positivity) 1
      (fun a _ => pow_le_one₀ (by norm_num) (by norm_num))
      (fun a _ => ⟨a.1, Set.mem_smul_set.mpr ⟨1, hU.one_mem a.2, mul_one _⟩⟩)
  let enlarged : u → Set G := fun a => a.val.1 • (U a.val.2 * (U a.val.2)⁻¹)
  -- every point of `B` lies in some enlarged selected translate
  have hcenters : ∀ x ∈ B, ∃ a : u, x ∈ enlarged a := by
    intro x hx
    obtain ⟨k, hk⟩ := hcover x hx
    obtain ⟨a, hau, ⟨z, hz₁, hz₂⟩, hpriority⟩ := hmatch (x, k) ⟨hx, hk⟩
    have ha : a.2 ≤ k := by
      by_contra h
      have h' : k + 1 ≤ a.2 := by omega
      have hpow : (1 / 2 : ℝ) ^ a.2 ≤ (1 / 2) ^ k * (1 / 2) := by
        rw [← pow_succ]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h'
      have hpr : (1 / 2 : ℝ) ^ k ≤ (3 / 2) * (1 / 2) ^ a.2 := hpriority
      have hp : 0 < (1 / 2 : ℝ) ^ k := by positivity
      linarith
    obtain ⟨w, hwU, hw⟩ := Set.mem_smul_set.mp hz₁
    obtain ⟨v, hvU, hv⟩ := Set.mem_smul_set.mp hz₂
    have hw' : x * w = z := hw
    have hv' : a.1 * v = z := hv
    refine ⟨⟨a, hau⟩, Set.mem_smul_set.mpr ⟨v * w⁻¹, ?_, ?_⟩⟩
    · exact Set.mul_mem_mul hvU (Set.mem_inv.mpr (by simpa using hanti ha hwU))
    · show a.1 * (v * w⁻¹) = x
      rw [← mul_assoc, hv', ← hw', mul_assoc, mul_inv_cancel, mul_one]
  have hdisjoint : Pairwise (fun i j : u => Disjoint (translate i) (translate j)) :=
    hud.on_injective Subtype.val_injective Subtype.property
  let mass : u → ℝ≥0∞ := fun a => μ (U a.val.2)
  -- the selected translates are disjoint subsets of `B * U 0`: their total mass is finite
  have hmass : (∑' a : u, mass a) < ⊤ := by
    calc
      (∑' a : u, mass a) = ∑' a : u, μ (translate a) := by
        simp only [mass, translate, measure_smul]
      _ ≤ μ (⋃ a : u, translate a) :=
        tsum_meas_le_meas_iUnion_of_disjoint₀ μ
          (fun a => (hU.nullMeasurable a.val.2).smul a.val.1)
          (fun _ _ hij => (hdisjoint hij).aedisjoint)
      _ ≤ μ (B * U 0) := by
        refine measure_mono (Set.iUnion_subset fun a => ?_)
        rintro y ⟨w, hw, rfl⟩
        exact Set.mul_mem_mul (hut a.property).1 (hanti (Nat.zero_le _) hw)
      _ < ⊤ := hBU
  have hlt : ∀ a : u, μ (enlarged a) < ENNReal.ofReal C * mass a := by
    intro a
    simpa only [enlarged, mass, measure_smul] using (hU.doubling a.val.2).2
  have hscaled_fin : (∑' a : u, ENNReal.ofReal C * mass a) < ⊤ := by
    rw [ENNReal.tsum_mul_left]
    exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmass.ne).lt_top
  have hsum_fin : (∑' a : u, μ (enlarged a)) ≠ ⊤ :=
    ((ENNReal.tsum_le_tsum fun a => (hlt a).le).trans_lt hscaled_fin).ne
  -- positive masses with a finite sum: the selected family is countable
  have hcount : Countable u := by
    have hsupp : Function.support mass = Set.univ :=
      Set.eq_univ_of_forall fun a => (hU.measure_pos a.val.2).ne'
    exact Set.countable_univ_iff.mp (hsupp ▸ Summable.countable_support_ennreal hmass.ne)
  obtain ⟨x₀, hx₀⟩ := hB
  obtain ⟨a₀, _⟩ := hcenters x₀ hx₀
  have hstrict : μ B < ENNReal.ofReal C * ∑' a : u, mass a := by
    calc
      μ B ≤ μ (⋃ a : u, enlarged a) :=
        measure_mono fun x hx => Set.mem_iUnion.mpr (hcenters x hx)
      _ ≤ ∑' a : u, μ (enlarged a) := measure_iUnion_le _
      _ < ∑' a : u, ENNReal.ofReal C * mass a :=
        ENNReal.tsum_lt_tsum hsum_fin (fun a => (hlt a).le) (hlt a₀)
      _ = ENNReal.ofReal C * ∑' a : u, mass a := ENNReal.tsum_mul_left
  have hfinite : μ B / ENNReal.ofReal C < ∑' a : u, mass a :=
    (ENNReal.div_lt_iff (Or.inl (ENNReal.ofReal_pos.mpr hU.const_pos).ne')
      (Or.inl ENNReal.ofReal_ne_top)).mpr (by simpa only [mul_comm] using hstrict)
  -- a finite partial sum already exceeds `μ B / C`
  rw [ENNReal.tsum_eq_iSup_sum, lt_iSup_iff] at hfinite
  obtain ⟨v, hv⟩ := hfinite
  refine ⟨v.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp ha
    exact hut b.property
  · intro a ha b hb hab
    obtain ⟨a', -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp ha)
    obtain ⟨b', -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hb)
    exact hud a'.property b'.property hab
  · rw [Finset.sum_map]
    exact hv
