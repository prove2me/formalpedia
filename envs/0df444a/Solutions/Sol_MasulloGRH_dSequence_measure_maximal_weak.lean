-- Prove2me | solution 1 for MasulloGRH.dSequence_measure_maximal_weak
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:32:27.771191+00:00
-- url     : https://prove2.me/submissions/a3d9324d-66bb-497d-b90c-5a43d60b509d

import Mathlib
import Definitions.Def_MasulloGRH_DSequences

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Sol_MasulloGRH_dSequence_measure_maximal_weak

open MasulloGRH Set

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- Covering theorem for translates of a D-sequence (Theorem A.5.3.1 of the source): if every point
of a nonempty set `s` with `μ (s * U 0) < ∞` is the centre of a translate `x • U k` belonging to a
family `F`, then finitely many pairwise disjoint such translates, centred in `s`, have total mass
`> μ s / C`. -/
theorem exists_disjoint_translates
    (μ : Measure G) [μ.IsHaarMeasure] (U : ℕ → Set G) (C : ℝ) (hU : IsDSequence μ U C)
    {F : Set (Set G)} {s : Set G} (hsne : s.Nonempty) (hsU : μ (s * U 0) < ∞)
    (hcover : ∀ x ∈ s, ∃ k, x • U k ∈ F) :
    ∃ (n : ℕ) (x : Fin n → G) (k : Fin n → ℕ),
      (∀ i, x i ∈ s ∧ x i • U (k i) ∈ F) ∧
      Pairwise (fun i j ↦ Disjoint (x i • U (k i)) (x j • U (k j))) ∧
      μ s / ENNReal.ofReal C < ∑ i, μ (U (k i)) := by
  classical
  have hanti : Antitone U := antitone_nat_of_succ_le hU.antitone
  have hC : 0 < C := hU.const_pos
  let translate (a : G × ℕ) : Set G := a.1 • U a.2
  let t : Set (G × ℕ) := {a | a.1 ∈ s ∧ translate a ∈ F}
  -- The geometric spacing forces the selected index to be at most the candidate index.
  let priority (a : G × ℕ) : ℝ := (1 / 2) ^ a.2
  obtain ⟨u, hut, hud, hmatch⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement translate t priority (3 / 2)
      (by norm_num) (fun _ _ ↦ by dsimp [priority]; positivity) 1
      (fun _ _ ↦ pow_le_one₀ (by norm_num) (by norm_num))
      (fun a _ ↦ ⟨a.1, Set.mem_smul_set.mpr ⟨1, hU.one_mem a.2, mul_one _⟩⟩)
  let enlarged (a : u) : Set G := a.val.1 • (U a.val.2 * (U a.val.2)⁻¹)
  have hcenters (x : G) (hx : x ∈ s) : ∃ a : u, x ∈ enlarged a := by
    obtain ⟨k, hk⟩ := hcover x hx
    obtain ⟨a, hau, ⟨z, hz₁, hz₂⟩, hpriority⟩ := hmatch (x, k) ⟨hx, hk⟩
    have ha : a.2 ≤ k := by
      by_contra! h
      have hpow : (1 / 2 : ℝ) ^ a.2 ≤ (1 / 2) ^ k * (1 / 2) := by
        rw [← pow_succ]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h
      change (1 / 2 : ℝ) ^ k ≤ (3 / 2) * (1 / 2) ^ a.2 at hpriority
      have hp : 0 < (1 / 2 : ℝ) ^ k := by positivity
      linarith
    obtain ⟨w, hwU, hw⟩ := Set.mem_smul_set.mp hz₁
    obtain ⟨v, hvU, hv⟩ := Set.mem_smul_set.mp hz₂
    change x * w = z at hw
    change a.1 * v = z at hv
    refine ⟨⟨a, hau⟩, Set.mem_smul_set.mpr ⟨v * w⁻¹, ?_, ?_⟩⟩
    · exact Set.mul_mem_mul hvU (Set.mem_inv.mpr (by simpa using hanti ha hwU))
    · change a.1 * (v * w⁻¹) = x
      rw [← mul_assoc, hv, ← hw, mul_assoc, mul_inv_cancel, mul_one]
  have hdisjoint : Pairwise (fun i j : u ↦ Disjoint (translate i) (translate j)) :=
    hud.on_injective Subtype.val_injective Subtype.property
  let mass (a : u) : ℝ≥0∞ := μ (U a.val.2)
  have hmass : (∑' a : u, mass a) < ∞ := by
    calc
      (∑' a : u, mass a) = ∑' a : u, μ (translate a) := by
        simp only [mass, translate, measure_smul]
      _ ≤ μ (⋃ a : u, translate a) :=
        tsum_meas_le_meas_iUnion_of_disjoint₀ μ
          (fun a ↦ (hU.nullMeasurable a.val.2).smul a.val.1)
          (fun _ _ hij ↦ (hdisjoint hij).aedisjoint)
      _ ≤ μ (s * U 0) := by
        apply measure_mono (iUnion_subset fun a ↦ ?_)
        rintro y ⟨w, hw, rfl⟩
        exact Set.mul_mem_mul (hut a.property).1 (hanti (Nat.zero_le _) hw)
      _ < ∞ := hsU
  -- Finite total mass and positive mass for every translate give countability.
  have : Countable u := by
    have hsupp : Function.support mass = univ :=
      Set.eq_univ_of_forall fun a ↦ (hU.measure_pos a.val.2).ne'
    exact countable_univ_iff.mp (hsupp ▸ Summable.countable_support_ennreal hmass.ne)
  have hlt (a : u) : μ (enlarged a) < ENNReal.ofReal C * mass a := by
    simpa only [enlarged, mass, measure_smul] using (hU.doubling a.val.2).2
  have hscaled_fin : (∑' a : u, ENNReal.ofReal C * mass a) < ∞ := by
    rw [ENNReal.tsum_mul_left]
    exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmass.ne).lt_top
  have hsum_fin : (∑' a : u, μ (enlarged a)) ≠ ∞ :=
    ((ENNReal.tsum_le_tsum fun a ↦ (hlt a).le).trans_lt hscaled_fin).ne
  obtain ⟨x₀, hx₀⟩ := hsne
  obtain ⟨a₀, _⟩ := hcenters x₀ hx₀
  have hstrict : μ s < ENNReal.ofReal C * ∑' a : u, mass a := by
    calc
      μ s ≤ μ (⋃ a : u, enlarged a) := measure_mono fun x hx ↦ mem_iUnion.mpr (hcenters x hx)
      _ ≤ ∑' a : u, μ (enlarged a) := measure_iUnion_le _
      _ < ∑' a : u, ENNReal.ofReal C * mass a :=
        ENNReal.tsum_lt_tsum hsum_fin (fun a ↦ (hlt a).le) (hlt a₀)
      _ = ENNReal.ofReal C * ∑' a : u, mass a := ENNReal.tsum_mul_left
  have hfinite : μ s / ENNReal.ofReal C < ∑' a : u, mass a :=
    (ENNReal.div_lt_iff (Or.inl (ENNReal.ofReal_pos.mpr hC).ne') (Or.inl ENNReal.ofReal_ne_top)).mpr
      (by simpa only [mul_comm] using hstrict)
  rw [ENNReal.tsum_eq_iSup_sum, lt_iSup_iff] at hfinite
  obtain ⟨v, hv⟩ := hfinite
  let e := (Fintype.equivFin (↑v : Type _)).symm
  refine ⟨_, fun i ↦ (e i).val.val.1, fun i ↦ (e i).val.val.2,
    fun i ↦ hut (e i).val.property, fun i j hij ↦ ?_, ?_⟩
  · exact hdisjoint (Subtype.val_injective.ne (e.injective.ne hij))
  · change μ s / ENNReal.ofReal C < ∑ i, mass (e i).val
    rw [← Fintype.sum_equiv e.symm (fun a ↦ mass a.val) _ (by simp)]
    rwa [← Finset.sum_attach, Finset.attach_eq_univ] at hv

/-- The strict form of the weak type inequality when the level set is nonempty. -/
theorem weak_strict
    (μ : Measure G) [μ.IsHaarMeasure] (U : ℕ → Set G) (C : ℝ) (hU : IsDSequence μ U C)
    (hBorel : ∀ k, MeasurableSet (U k)) (ν : Measure G)
    (B : Set G) (hBU : μ (B * U 0) < ⊤) (α : ℝ) (hα : 0 < α)
    (E : Set G)
    (hE : E = B ∩ {x | ENNReal.ofReal α < limsup (fun k : ℕ => ν (x • U k) / μ (U k)) atTop})
    (hEne : E.Nonempty) :
    μ E < ENNReal.ofReal (C / α) * ν (E * U 0) := by
  classical
  have hanti : Antitone U := antitone_nat_of_succ_le hU.antitone
  have hC : 0 < C := hU.const_pos
  have hEsub : E ⊆ B := hE ▸ inter_subset_left
  let F : Set (Set G) := {V | ENNReal.ofReal α * μ V < ν V}
  have hcover (x : G) (hx : x ∈ E) : ∃ k, x • U k ∈ F := by
    have hlevel : ENNReal.ofReal α < limsup (fun k : ℕ => ν (x • U k) / μ (U k)) atTop := by
      rw [hE] at hx
      exact hx.2
    obtain ⟨k, hk⟩ := (frequently_lt_of_lt_limsup (h := hlevel)).exists
    refine ⟨k, ?_⟩
    change ENNReal.ofReal α * μ (x • U k) < ν (x • U k)
    rw [measure_smul]
    exact lt_of_not_ge fun h ↦ hk.not_ge
      ((ENNReal.div_le_iff (hU.measure_pos k).ne' (hU.measure_lt_top k).ne).mpr
        (by simpa only [mul_comm] using h))
  obtain ⟨n, x, k, hx, hdisjoint, hmass⟩ :=
    exists_disjoint_translates μ U C hU (F := F) hEne
      ((measure_mono (Set.mul_subset_mul hEsub Subset.rfl)).trans_lt hBU) hcover
  have hunion : (⋃ i, x i • U (k i)) ⊆ E * U 0 := by
    refine iUnion_subset fun i ↦ ?_
    rintro y ⟨w, hw, rfl⟩
    exact Set.mul_mem_mul (hx i).1 (hanti (Nat.zero_le _) hw)
  have hsum : ∑ i, ENNReal.ofReal α * μ (U (k i)) ≤ ν (E * U 0) := by
    calc
      _ ≤ ∑ i, ν (x i • U (k i)) := Finset.sum_le_sum fun i _ ↦ by
        have h := (hx i).2
        change ENNReal.ofReal α * μ (x i • U (k i)) < ν (x i • U (k i)) at h
        rw [measure_smul] at h
        exact h.le
      _ = ν (⋃ i, x i • U (k i)) := by
        rw [measure_iUnion hdisjoint, tsum_fintype]
        intro i
        exact (hBorel (k i)).const_smul (x i)
      _ ≤ ν (E * U 0) := measure_mono hunion
  calc
    μ E < ENNReal.ofReal C * ∑ i, μ (U (k i)) := by
      rw [mul_comm, ← ENNReal.div_lt_iff (Or.inl (ENNReal.ofReal_pos.mpr hC).ne')
        (Or.inl ENNReal.ofReal_ne_top)]
      exact hmass
    _ ≤ ENNReal.ofReal C * (ν (E * U 0) / ENNReal.ofReal α) := by
      refine mul_le_mul' le_rfl ?_
      apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hα).ne')
        (Or.inl ENNReal.ofReal_ne_top)).mpr
      simpa only [mul_comm _ (ENNReal.ofReal α), Finset.mul_sum] using hsum
    _ = ENNReal.ofReal (C / α) * ν (E * U 0) := by
      rw [ENNReal.ofReal_div_of_pos hα, ENNReal.div_eq_inv_mul, ← mul_assoc, div_eq_mul_inv]

end Sol_MasulloGRH_dSequence_measure_maximal_weak

open MasulloGRH

theorem solution
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (U : ℕ → Set G) (C : ℝ) (hU : IsDSequence μ U C)
    (hBorel : ∀ k, MeasurableSet (U k)) (ν : Measure G) [ν.Regular]
    (B : Set G) (hB : NullMeasurableSet B μ) (hBU : μ (B * U 0) < ⊤) (α : ℝ) (hα : 0 < α)
    (E : Set G)
    (hE : E = B ∩ {x | ENNReal.ofReal α < limsup (fun k : ℕ => ν (x • U k) / μ (U k)) atTop}) :
    μ E ≤ ENNReal.ofReal (C / α) * ν (E * U 0) ∧
      (μ E = ENNReal.ofReal (C / α) * ν (E * U 0) ↔ E = ∅) := by
  obtain hEe | hEne := E.eq_empty_or_nonempty
  · subst hEe
    simp
  · have hlt := Sol_MasulloGRH_dSequence_measure_maximal_weak.weak_strict μ U C hU hBorel ν B hBU
      α hα E hE hEne
    exact ⟨hlt.le, iff_of_false hlt.ne hEne.ne_empty⟩
