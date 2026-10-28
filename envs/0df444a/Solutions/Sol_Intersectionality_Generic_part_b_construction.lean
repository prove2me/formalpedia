-- Prove2me | solution 1 for Intersectionality.Generic.part_b_construction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T12:49:08.672962+00:00
-- url     : https://prove2.me/submissions/afe84c3f-4fac-455a-9432-e8d371fd207e

import Mathlib
import Definitions.Def_Intersectionality_Generic_Setting

open MeasureTheory Set Filter Topology

namespace IGC
open Intersectionality.Generic

variable {X : Set ℝ} {n : ℕ}

lemma mGrp (g : Grp n) : MeasurableSet {z : ScoreGrp X n | z.2 = g} :=
  measurable_snd (measurableSet_singleton g)

lemma mLe (y : ↥X) (g : Grp n) : MeasurableSet {z : ScoreGrp X n | z.1 ≤ y ∧ z.2 = g} :=
  (measurableSet_le measurable_fst measurable_const).inter (mGrp g)

lemma mLt (y : ↥X) (g : Grp n) : MeasurableSet {z : ScoreGrp X n | z.1 < y ∧ z.2 = g} :=
  (measurableSet_lt measurable_fst measurable_const).inter (mGrp g)

lemma mIoo (a b : ↥X) (g : Grp n) :
    MeasurableSet {z : ScoreGrp X n | a < z.1 ∧ z.1 < b ∧ z.2 = g} :=
  (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_const).inter (mGrp g))

lemma groupMass_nonneg (p : ProbabilityMeasure (ScoreGrp X n)) (g : Grp n) :
    0 ≤ groupMass p g := measureReal_nonneg

/-- atoms vanish for every group (positive mass: by `InP`; zero mass: trivially). -/
lemma atom_zero (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p) (g : Grp n) (y : ↥X) :
    (p : Measure (ScoreGrp X n)) {z | z.1 = y ∧ z.2 = g} = 0 := by
  by_cases hg : 0 < groupMass p g
  · have := (hp g hg).1 y
    rwa [measureReal_eq_zero_iff] at this
  · have h0 : groupMass p g = 0 := le_antisymm (not_lt.1 hg) (groupMass_nonneg p g)
    unfold groupMass at h0
    rw [measureReal_eq_zero_iff] at h0
    exact measure_mono_null (fun z hz => hz.2) h0

lemma lt_eq_le (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p) (g : Grp n) (y : ↥X) :
    (p : Measure (ScoreGrp X n)).real {z | z.1 < y ∧ z.2 = g} =
      (p : Measure (ScoreGrp X n)).real {z | z.1 ≤ y ∧ z.2 = g} := by
  have hsplit : {z : ScoreGrp X n | z.1 ≤ y ∧ z.2 = g} =
      {z | z.1 < y ∧ z.2 = g} ∪ {z | z.1 = y ∧ z.2 = g} := by
    ext z; simp only [mem_setOf_eq, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h1.lt_or_eq with h | h
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1.le, h2⟩
      · exact ⟨h1.le, h2⟩
  rw [hsplit, measureReal_union]
  · rw [measureReal_def (s := {z : ScoreGrp X n | z.1 = y ∧ z.2 = g}), atom_zero p hp g y]; simp
  · rw [Set.disjoint_left]
    rintro z ⟨h1, -⟩ ⟨h2, -⟩
    exact absurd h2 (ne_of_lt h1)
  · exact ((measurableSet_eq_fun measurable_fst measurable_const)).inter (mGrp g)

/-- The unnormalized CDF. -/
noncomputable def G (p : ProbabilityMeasure (ScoreGrp X n)) (g : Grp n) (y : ↥X) : ℝ :=
  (p : Measure (ScoreGrp X n)).real {z | z.1 ≤ y ∧ z.2 = g}

lemma G_strictMono (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p) (g : Grp n)
    (hg : 0 < groupMass p g) : StrictMono (G p g) := by
  intro a b hab
  have hpos := (hp g hg).2 a b hab
  have hsub : {z : ScoreGrp X n | z.1 ≤ a ∧ z.2 = g} ∪ {z | a < z.1 ∧ z.1 < b ∧ z.2 = g} ⊆
      {z | z.1 ≤ b ∧ z.2 = g} := by
    rintro z (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨h1.trans hab.le, h2⟩
    · exact ⟨h2.le, h3⟩
  have hdis : Disjoint {z : ScoreGrp X n | z.1 ≤ a ∧ z.2 = g}
      {z | a < z.1 ∧ z.1 < b ∧ z.2 = g} := by
    rw [Set.disjoint_left]
    rintro z ⟨h1, -⟩ ⟨h2, -⟩
    exact absurd h1 (not_le.2 h2)
  have := measureReal_mono (μ := (p : Measure (ScoreGrp X n))) hsub
  rw [measureReal_union hdis (mIoo a b g)] at this
  unfold G
  linarith

lemma G_le_mass (p : ProbabilityMeasure (ScoreGrp X n)) (g : Grp n) (y : ↥X) :
    G p g y ≤ groupMass p g :=
  measureReal_mono (fun z hz => hz.2)

lemma condCDF_eq (p : ProbabilityMeasure (ScoreGrp X n)) (g : Grp n) (y : ↥X) :
    condCDF p g y = G p g y / groupMass p g := rfl

lemma condCDF_strictMono (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p) (g : Grp n)
    (hg : 0 < groupMass p g) : StrictMono (condCDF p g) := by
  intro a b hab
  rw [condCDF_eq, condCDF_eq]
  exact div_lt_div_of_pos_right (G_strictMono p hp g hg hab) hg

/-! ### existence of the quantile -/

/-- the conditional law of the score of group `g`, as a measure on `ℝ`. -/
noncomputable def law (p : ProbabilityMeasure (ScoreGrp X n)) (g : Grp n) : Measure ℝ :=
  (ProbabilityTheory.cond (p : Measure (ScoreGrp X n)) {z | z.2 = g}).map
    (fun z : ScoreGrp X n => (z.1 : ℝ))

lemma meas_val : Measurable (fun z : ScoreGrp X n => (z.1 : ℝ)) :=
  measurable_subtype_coe.comp measurable_fst

lemma law_apply (p : ProbabilityMeasure (ScoreGrp X n)) (g : Grp n) (s : Set ℝ)
    (hs : MeasurableSet s) :
    law p g s = ((p : Measure (ScoreGrp X n)) {z | z.2 = g})⁻¹ *
      (p : Measure (ScoreGrp X n)) ({z | z.2 = g} ∩ {z | (z.1 : ℝ) ∈ s}) := by
  unfold law
  rw [Measure.map_apply meas_val hs, ProbabilityTheory.cond_apply (mGrp g)]
  rfl

lemma law_prob (p : ProbabilityMeasure (ScoreGrp X n)) (g : Grp n)
    (hg : 0 < groupMass p g) : IsProbabilityMeasure (law p g) := by
  have hne : (p : Measure (ScoreGrp X n)) {z | z.2 = g} ≠ 0 := by
    intro h
    unfold groupMass at hg
    rw [measureReal_def, h] at hg
    simp at hg
  haveI := ProbabilityTheory.cond_isProbabilityMeasure (μ := (p : Measure (ScoreGrp X n))) hne
  exact Measure.isProbabilityMeasure_map meas_val.aemeasurable

lemma law_singleton (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p) (g : Grp n) (x : ℝ) :
    law p g {x} = 0 := by
  rw [law_apply p g {x} (measurableSet_singleton x)]
  by_cases hx : x ∈ X
  · have : {z : ScoreGrp X n | z.2 = g} ∩ {z | (z.1 : ℝ) ∈ ({x} : Set ℝ)} =
        {z | z.1 = ⟨x, hx⟩ ∧ z.2 = g} := by
      ext z
      simp only [mem_inter_iff, mem_setOf_eq, mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Subtype.ext h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, by rw [h1]⟩
    rw [this, atom_zero p hp g ⟨x, hx⟩, mul_zero]
  · have : {z : ScoreGrp X n | z.2 = g} ∩ {z | (z.1 : ℝ) ∈ ({x} : Set ℝ)} = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_setOf_eq, mem_singleton_iff, mem_empty_iff_false,
        iff_false, not_and]
      intro _ h
      exact hx (h ▸ z.1.2)
    rw [this, measure_empty, mul_zero]

lemma cdf_continuous (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : ∀ x, μ {x} = 0) :
    Continuous (ProbabilityTheory.cdf μ) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hm := ProbabilityTheory.monotone_cdf μ
  have hl : Function.leftLim (ProbabilityTheory.cdf μ) x = ProbabilityTheory.cdf μ x := by
    apply le_antisymm (hm.leftLim_le le_rfl)
    have h1 := (ProbabilityTheory.cdf μ).measure_singleton x
    rw [ProbabilityTheory.measure_cdf, h x] at h1
    have := ENNReal.ofReal_eq_zero.1 h1.symm
    linarith
  refine continuousAt_iff_continuous_left'_right'.2 ⟨?_, ?_⟩
  · exact hm.continuousWithinAt_Iio_iff_leftLim_eq.2 hl
  · exact ((ProbabilityTheory.cdf μ).right_continuous x).mono Ioi_subset_Ici_self

lemma condCDF_eq_cdf (p : ProbabilityMeasure (ScoreGrp X n)) (g : Grp n)
    (hg : 0 < groupMass p g) (y : ↥X) :
    condCDF p g y = ProbabilityTheory.cdf (law p g) y := by
  haveI := law_prob p g hg
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def, law_apply p g _ measurableSet_Iic]
  rw [condCDF_eq]
  unfold G groupMass
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, measureReal_def, measureReal_def, div_eq_inv_mul]
  have : {z : ScoreGrp X n | z.2 = g} ∩ {z | (z.1 : ℝ) ∈ Iic (y : ℝ)} =
      {z | z.1 ≤ y ∧ z.2 = g} := by
    ext z
    simp only [mem_setOf_eq, mem_inter_iff, mem_Iic, Subtype.coe_le_coe]
    exact and_comm
  rw [this]

lemma exists_quantile (hX : X.OrdConnected) (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p)
    (g : Grp n) (hg : 0 < groupMass p g) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ y : ↥X, condCDF p g y = c := by
  haveI := law_prob p g hg
  set F := ProbabilityTheory.cdf (law p g)
  have hF : Continuous F := cdf_continuous _ (law_singleton p hp g)
  obtain ⟨a, ha⟩ := ((ProbabilityTheory.tendsto_cdf_atBot (law p g)).eventually
    (gt_mem_nhds hc0)).exists
  obtain ⟨b, hb⟩ := ((ProbabilityTheory.tendsto_cdf_atTop (law p g)).eventually
    (lt_mem_nhds hc1)).exists
  obtain ⟨x, hx⟩ := intermediate_value_univ a b hF ⟨ha.le, hb.le⟩
  -- x ∈ X
  have hlow : ∃ u ∈ X, u ≤ x := by
    by_contra hcon
    push_neg at hcon
    have : law p g (Iic x) = 0 := by
      rw [law_apply p g _ measurableSet_Iic]
      have : {z : ScoreGrp X n | z.2 = g} ∩ {z | (z.1 : ℝ) ∈ Iic x} = ∅ := by
        ext z
        simp only [mem_inter_iff, mem_setOf_eq, mem_Iic, mem_empty_iff_false, iff_false,
          not_and, not_le]
        intro _
        exact hcon _ z.1.2
      rw [this, measure_empty, mul_zero]
    have h2 : F x = 0 := by
      rw [ProbabilityTheory.cdf_eq_real, measureReal_def, this]; rfl
    linarith
  have hhigh : ∃ u ∈ X, x ≤ u := by
    by_contra hcon
    push_neg at hcon
    have : law p g (Iic x) = 1 := by
      have : Iic x ∩ X = X := by
        ext u; simp only [mem_inter_iff, mem_Iic, and_iff_right_iff_imp]
        intro hu; exact (hcon u hu).le
      rw [← measure_univ (μ := law p g)]
      rw [law_apply p g _ measurableSet_Iic, law_apply p g _ MeasurableSet.univ]
      congr 2
      ext z
      simp only [mem_inter_iff, mem_setOf_eq, mem_Iic, mem_univ, and_true, and_iff_left_iff_imp]
      intro _
      exact (hcon _ z.1.2).le
    have h2 : F x = 1 := by
      rw [ProbabilityTheory.cdf_eq_real, measureReal_def, this]; rfl
    linarith
  obtain ⟨u, hu, hux⟩ := hlow
  obtain ⟨v, hv, hxv⟩ := hhigh
  have hxX : x ∈ X := hX.out hu hv ⟨hux, hxv⟩
  refine ⟨⟨x, hxX⟩, ?_⟩
  rw [condCDF_eq_cdf p g hg]
  exact hx

lemma quantile_spec (hX : X.OrdConnected) [Nonempty ↥X] (p : ProbabilityMeasure (ScoreGrp X n))
    (hp : InP p) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (g : Grp n) (hg : 0 < groupMass p g) :
    condCDF p g (quantile p α g) = 1 - α := by
  unfold quantile
  exact Classical.epsilon_spec (exists_quantile hX p hp g hg (1 - α) (by linarith) (by linarith))

lemma quantile_unique (hX : X.OrdConnected) [Nonempty ↥X] (p : ProbabilityMeasure (ScoreGrp X n))
    (hp : InP p) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (g : Grp n) (hg : 0 < groupMass p g)
    (y : ↥X) (hy : condCDF p g y = 1 - α) : y = quantile p α g :=
  (condCDF_strictMono p hp g hg).injective (hy.trans (quantile_spec hX p hp α hα0 hα1 g hg).symm)

/-! ### accepted mass -/

lemma accMass_eq (p : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p)
    (q : Grp n → (↥X → ↥X)) (xs : ↥X) (g : Grp n) (b : ↥X) (hmono : StrictMono (q g))
    (hb : q g b = xs) :
    accMass p q xs g = groupMass p g - G p g b := by
  unfold accMass groupMass G
  rw [← lt_eq_le p hp g b, ← measureReal_sdiff (s₁ := {z : ScoreGrp X n | z.2 = g}) (fun z hz => hz.2) (mLt b g)]
  congr 1
  ext z
  simp only [mem_setOf_eq, mem_diff, not_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun h3 _ => ?_⟩
    rw [← hb] at h2
    exact absurd (hmono.le_iff_le.1 h2) (not_le.2 h3)
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [← hb]
    exact hmono.monotone (not_lt.1 (fun h => h2 h h1))

lemma accMass_le (p : ProbabilityMeasure (ScoreGrp X n))
    (q : Grp n → (↥X → ↥X)) (xs : ↥X) (g : Grp n) : accMass p q xs g ≤ groupMass p g :=
  measureReal_mono (fun z hz => hz.1)

lemma accMass_nonneg (p : ProbabilityMeasure (ScoreGrp X n))
    (q : Grp n → (↥X → ↥X)) (xs : ↥X) (g : Grp n) : 0 ≤ accMass p q xs g := measureReal_nonneg

lemma sum_groupMass (p : ProbabilityMeasure (ScoreGrp X n)) : ∑ g, groupMass p g = 1 := by
  unfold groupMass
  rw [← measureReal_biUnion_finset]
  · have : (⋃ g ∈ (Finset.univ : Finset (Grp n)), {z : ScoreGrp X n | z.2 = g}) = univ := by
      ext z; simp
    rw [this]; simp
  · intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro z h1 h2
    exact hab (h1.symm.trans h2)
  · intro g _; exact mGrp g

/-- representativeness ↔ every group's accepted mass is `α p(g)`. -/
lemma rep_iff_acc (p : ProbabilityMeasure (ScoreGrp X n)) (α : ℝ) (hα0 : 0 < α)
    (q : Grp n → (↥X → ↥X)) (xs : ↥X) :
    IsRepresentative p α q xs ↔ ∀ g, accMass p q xs g = α * groupMass p g := by
  unfold IsRepresentative SatisfiesCapacity share
  constructor
  · rintro ⟨hcap, hsh⟩ g
    have := hsh g
    rw [hcap] at this
    field_simp at this
    linarith
  · intro h
    have hsum : ∑ g, accMass p q xs g = α := by
      simp_rw [h]; rw [← Finset.mul_sum, sum_groupMass, mul_one]
    refine ⟨hsum, fun g => ?_⟩
    rw [hsum, h g]; field_simp

/-- for a group of positive mass: accepted mass is `α p(g)` iff `q_g(β_g) = x*`. -/
lemma acc_iff (hX : X.OrdConnected) [Nonempty ↥X] (p : ProbabilityMeasure (ScoreGrp X n))
    (hp : InP p) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (q : Grp n → (↥X → ↥X)) (xs : ↥X)
    (g : Grp n) (hg : 0 < groupMass p g) (hmono : StrictMono (q g))
    (hsurj : Function.Surjective (q g)) :
    accMass p q xs g = α * groupMass p g ↔ q g (quantile p α g) = xs := by
  obtain ⟨b, hb⟩ := hsurj xs
  rw [accMass_eq p hp q xs g b hmono hb]
  have hG : G p g b = groupMass p g * condCDF p g b := by
    rw [condCDF_eq]; field_simp
  rw [hG]
  constructor
  · intro h
    have : condCDF p g b = 1 - α := by
      have h' : groupMass p g * (1 - condCDF p g b) = groupMass p g * α := by linarith
      have := mul_left_cancel₀ hg.ne' h'
      linarith
    rw [← quantile_unique hX p hp α hα0 hα1 g hg b this, hb]
  · intro h
    have : b = quantile p α g := hmono.injective (hb.trans h.symm)
    rw [this, quantile_spec hX p hp α hα0 hα1 g hg]
    ring

lemma acc_zero_mass (p : ProbabilityMeasure (ScoreGrp X n)) (α : ℝ)
    (q : Grp n → (↥X → ↥X)) (xs : ↥X) (g : Grp n) (hg : ¬ 0 < groupMass p g) :
    accMass p q xs g = α * groupMass p g := by
  have h0 : groupMass p g = 0 := le_antisymm (not_lt.1 hg) (groupMass_nonneg p g)
  rw [h0, mul_zero]
  exact le_antisymm (h0 ▸ accMass_le p q xs g) (accMass_nonneg p q xs g)

end IGC

open Intersectionality.Generic in
theorem solution (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (n : ℕ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (Q : Set (↥X → ↥X)) (hQ : IsPolicyFamily Q) :
    ∀ p : DistSpace X n, ∀ xs : ↥X, ∃ q : Grp n → (↥X → ↥X), (∀ g, q g ∈ Q) ∧
      (∀ g, 0 < groupMass p.1 g → q g (quantile p.1 α g) = xs) ∧
      IsRepresentative p.1 α q xs := by
  intro p xs
  have hspec : ∀ g : Grp n, transport Q (quantile p.1 α g) xs ∈ Q ∧
      transport Q (quantile p.1 α g) xs (quantile p.1 α g) = xs := by
    intro g
    have hex := hQ.rich (quantile p.1 α g) xs
    unfold transport
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  refine ⟨fun g => transport Q (quantile p.1 α g) xs, fun g => (hspec g).1,
    fun g _ => (hspec g).2, ?_⟩
  rw [IGC.rep_iff_acc p.1 α hα0 _ xs]
  intro g
  by_cases hg : 0 < groupMass p.1 g
  · exact (IGC.acc_iff hX p.1 p.2 α hα0 hα1 _ xs g hg (hQ.strictMono _ (hspec g).1)
      (hQ.bijective _ (hspec g).1).2).2 (hspec g).2
  · exact IGC.acc_zero_mass p.1 α _ xs g hg
