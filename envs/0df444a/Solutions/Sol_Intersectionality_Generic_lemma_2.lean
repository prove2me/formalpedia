-- Prove2me | solution 1 for Intersectionality.Generic.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:03:26.363313+00:00
-- url     : https://prove2.me/submissions/9765ca4a-a741-49b7-ad79-5e711eab4a9c

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

namespace IGC
open Intersectionality.Generic

/-- separately continuous + monotone in the first variable ⇒ jointly continuous. -/
lemma joint_cont_mono {α β γ : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] [NoMaxOrder α] [NoMinOrder α]
    [TopologicalSpace β] [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
    (F : α → β → γ) (h1 : ∀ b, Continuous (fun a => F a b)) (h2 : ∀ a, Continuous (F a))
    (hm : ∀ b, Monotone (fun a => F a b)) : Continuous (fun x : α × β => F x.1 x.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨a0, b0⟩
  refine tendsto_order.2 ⟨fun c hc => ?_, fun d hd => ?_⟩
  · have hopen : IsOpen {a | c < F a b0} := isOpen_lt continuous_const (h1 b0)
    obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hopen.mem_nhds hc)
    obtain ⟨a2, hla2, ha2⟩ := exists_between hl
    have hc2 : c < F a2 b0 := hsub ⟨hla2, ha2.trans hu⟩
    have hopen2 : IsOpen {b | c < F a2 b} := isOpen_lt continuous_const (h2 a2)
    have hn : Ioi a2 ×ˢ {b | c < F a2 b} ∈ 𝓝 (a0, b0) :=
      prod_mem_nhds (Ioi_mem_nhds ha2) (hopen2.mem_nhds hc2)
    filter_upwards [hn] with x hx
    exact lt_of_lt_of_le hx.2 (hm x.2 (le_of_lt hx.1))
  · have hopen : IsOpen {a | F a b0 < d} := isOpen_lt (h1 b0) continuous_const
    obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hopen.mem_nhds hd)
    obtain ⟨a1, ha1, ha1u⟩ := exists_between hu
    have hd1 : F a1 b0 < d := hsub ⟨hl.trans ha1, ha1u⟩
    have hopen2 : IsOpen {b | F a1 b < d} := isOpen_lt (h2 a1) continuous_const
    have hn : Iio a1 ×ˢ {b | F a1 b < d} ∈ 𝓝 (a0, b0) :=
      prod_mem_nhds (Iio_mem_nhds ha1) (hopen2.mem_nhds hd1)
    filter_upwards [hn] with x hx
    exact lt_of_le_of_lt (hm x.2 (le_of_lt hx.1)) hx.2

lemma joint_cont_anti {α β γ : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] [NoMaxOrder α] [NoMinOrder α]
    [TopologicalSpace β] [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
    (F : α → β → γ) (h1 : ∀ b, Continuous (fun a => F a b)) (h2 : ∀ a, Continuous (F a))
    (hm : ∀ b, Antitone (fun a => F a b)) : Continuous (fun x : α × β => F x.1 x.2) := by
  have := joint_cont_mono (α := αᵒᵈ) (fun a b => F (OrderDual.ofDual a) b)
    (fun b => (h1 b).comp continuous_ofDual) (fun a => h2 _) (fun b => (hm b).dual_left)
  exact this.comp ((continuous_toDual.comp continuous_fst).prodMk continuous_snd)

variable {X : Set ℝ} {Q : Set (↥X → ↥X)}

lemma T_spec (hQ : IsPolicyFamily Q) (u v : ↥X) :
    transport Q u v ∈ Q ∧ transport Q u v u = v := by
  have hex := hQ.rich u v
  unfold transport; rw [dif_pos hex]; exact Classical.choose_spec hex

lemma Q_unique (hQ : IsPolicyFamily Q) {q q' : ↥X → ↥X} (hq : q ∈ Q) (hq' : q' ∈ Q) (x : ↥X)
    (h : q x = q' x) : q = q' := by
  funext w
  obtain ⟨r, hr, hrx⟩ := hQ.rich x w
  rw [← hrx]
  have e1 := congrFun (hQ.comm q hq r hr) x
  have e2 := congrFun (hQ.comm q' hq' r hr) x
  simp only [Function.comp_apply] at e1 e2
  rw [e1, e2, h]

lemma T_eq (hQ : IsPolicyFamily Q) {q : ↥X → ↥X} (hq : q ∈ Q) (u : ↥X) :
    transport Q u (q u) = q :=
  Q_unique hQ (T_spec hQ u (q u)).1 hq u (T_spec hQ u (q u)).2

lemma Q_pointwise_lt (hQ : IsPolicyFamily Q) {q q' : ↥X → ↥X} (hq : q ∈ Q) (hq' : q' ∈ Q)
    (w0 : ↥X) (h : q w0 < q' w0) (w : ↥X) : q w < q' w := by
  obtain ⟨r, hr, hrx⟩ := hQ.rich w0 w
  rw [← hrx]
  have e1 := congrFun (hQ.comm q hq r hr) w0
  have e2 := congrFun (hQ.comm q' hq' r hr) w0
  simp only [Function.comp_apply] at e1 e2
  rw [e1, e2]; exact hQ.strictMono r hr h

lemma id_mem (hQ : IsPolicyFamily Q) [Nonempty ↥X] : (id : ↥X → ↥X) ∈ Q := by
  obtain ⟨x⟩ := ‹Nonempty ↥X›
  have h := T_spec hQ x x
  have : transport Q x x = id := by
    funext w
    obtain ⟨r, hr, hrx⟩ := hQ.rich x w
    rw [← hrx]
    have e1 := congrFun (hQ.comm _ h.1 r hr) x
    simp only [Function.comp_apply] at e1
    rw [e1, h.2]; rfl
  rw [← this]; exact h.1

lemma T_inv (hQ : IsPolicyFamily Q) (u v y : ↥X) :
    transport Q v u (transport Q u v y) = y := by
  obtain ⟨r, hr, hry⟩ := hQ.rich u y
  rw [← hry]
  have hA := T_spec hQ u v
  have hB := T_spec hQ v u
  have e1 := congrFun (hQ.comm _ hA.1 r hr) u
  simp only [Function.comp_apply] at e1
  rw [e1, hA.2]
  have e2 := congrFun (hQ.comm _ hB.1 r hr) v
  simp only [Function.comp_apply] at e2
  rw [e2, hB.2]

lemma invFun_T [Nonempty ↥X] (hQ : IsPolicyFamily Q) (u v x : ↥X) :
    Function.invFun (transport Q v u) x = transport Q u v x := by
  have hb := hQ.bijective _ (T_spec hQ v u).1
  apply hb.1
  rw [Function.invFun_eq (hb.2 x), T_inv hQ u v x]

lemma T_mono_v (hQ : IsPolicyFamily Q) (u x : ↥X) : StrictMono (fun v => transport Q u v x) := by
  intro v v' hv
  apply Q_pointwise_lt hQ (T_spec hQ u v).1 (T_spec hQ u v').1 u
  rw [(T_spec hQ u v).2, (T_spec hQ u v').2]; exact hv

lemma T_anti_u (hQ : IsPolicyFamily Q) (v x : ↥X) :
    StrictAnti (fun u => transport Q u v x) := by
  intro u u' hu
  apply Q_pointwise_lt hQ (T_spec hQ u' v).1 (T_spec hQ u v).1 u'
  rw [(T_spec hQ u' v).2]
  calc v = transport Q u v u := (T_spec hQ u v).2.symm
    _ < _ := hQ.strictMono _ (T_spec hQ u v).1 hu

lemma T_surj_v (hQ : IsPolicyFamily Q) (u x : ↥X) :
    Function.Surjective (fun v => transport Q u v x) := by
  intro w
  refine ⟨transport Q x w u, ?_⟩
  simp only
  rw [T_eq hQ (T_spec hQ x w).1 u, (T_spec hQ x w).2]

lemma T_surj_u (hQ : IsPolicyFamily Q) (v x : ↥X) :
    Function.Surjective (fun u => transport Q u v x) := by
  intro w
  refine ⟨transport Q w x v, ?_⟩
  simp only
  have h1 : transport Q x w (transport Q w x v) = v := T_inv hQ w x v
  have h2 := T_eq hQ (T_spec hQ x w).1 (transport Q w x v)
  rw [h1] at h2
  rw [h2, (T_spec hQ x w).2]

section cont
variable (hX : X.OrdConnected)
include hX

lemma T_cont_x (hQ : IsPolicyFamily Q) (u v : ↥X) : Continuous (transport Q u v) := by
  haveI := hX
  exact (hQ.strictMono _ (T_spec hQ u v).1).monotone.continuous_of_surjective
    (hQ.bijective _ (T_spec hQ u v).1).2

lemma T_cont_v (hQ : IsPolicyFamily Q) (u x : ↥X) :
    Continuous (fun v => transport Q u v x) := by
  haveI := hX
  exact (T_mono_v hQ u x).monotone.continuous_of_surjective (T_surj_v hQ u x)

lemma T_cont_u (hQ : IsPolicyFamily Q) (v x : ↥X) :
    Continuous (fun u => transport Q u v x) := by
  haveI := hX
  have hm : Monotone (fun u => OrderDual.toDual (transport Q u v x)) :=
    fun a b hab => (T_anti_u hQ v x).antitone hab
  have hs : Function.Surjective (fun u => OrderDual.toDual (transport Q u v x)) := by
    intro w
    obtain ⟨u, hu⟩ := T_surj_u hQ v x (OrderDual.ofDual w)
    exact ⟨u, by simp only at hu ⊢; rw [hu]; rfl⟩
  exact continuous_ofDual.comp (hm.continuous_of_surjective hs)

lemma T_cont [NoMaxOrder ↥X] [NoMinOrder ↥X] (hQ : IsPolicyFamily Q) :
    Continuous (fun y : ↥X × (↥X × ↥X) => transport Q y.1 y.2.1 y.2.2) := by
  haveI := hX
  have inner : ∀ u, Continuous (fun b : ↥X × ↥X => transport Q u b.1 b.2) := fun u =>
    joint_cont_mono (fun v x => transport Q u v x) (fun x => T_cont_v hX hQ u x)
      (fun v => T_cont_x hX hQ u v) (fun x => (T_mono_v hQ u x).monotone)
  exact joint_cont_anti (fun u (b : ↥X × ↥X) => transport Q u b.1 b.2)
    (fun b => T_cont_u hX hQ b.1 b.2) inner (fun b => (T_anti_u hQ b.1 b.2).antitone)

end cont

end IGC

namespace IGC
open Intersectionality.Generic

variable {X : Set ℝ} {n : ℕ}

lemma isClopen_grp (g : Grp n) : IsClopen {z : ScoreGrp X n | z.2 = g} :=
  (isClopen_discrete {g}).preimage continuous_snd

lemma frontier_le_sub (y : ↥X) (g : Grp n) :
    frontier {z : ScoreGrp X n | z.1 ≤ y ∧ z.2 = g} ⊆ {z | z.1 = y ∧ z.2 = g} := by
  have hc : IsClosed {z : ScoreGrp X n | z.1 ≤ y ∧ z.2 = g} :=
    (isClosed_le continuous_fst continuous_const).inter (isClopen_grp g).isClosed
  have ho : IsOpen {z : ScoreGrp X n | z.1 < y ∧ z.2 = g} :=
    (isOpen_lt continuous_fst continuous_const).inter (isClopen_grp g).isOpen
  have hsub : {z : ScoreGrp X n | z.1 < y ∧ z.2 = g} ⊆
      interior {z | z.1 ≤ y ∧ z.2 = g} :=
    ho.subset_interior_iff.2 (fun z hz => ⟨hz.1.le, hz.2⟩)
  intro z hz
  rw [frontier, hc.closure_eq] at hz
  obtain ⟨⟨h1, h2⟩, h3⟩ := hz
  exact ⟨le_antisymm h1 (not_lt.1 fun h => h3 (hsub ⟨h, h2⟩)), h2⟩

lemma tendsto_real {ι : Type*} {L : Filter ι} {ps : ι → ProbabilityMeasure (ScoreGrp X n)}
    {p : ProbabilityMeasure (ScoreGrp X n)} (h : Tendsto ps L (𝓝 p)) {E : Set (ScoreGrp X n)}
    (hE : (p : Measure (ScoreGrp X n)) (frontier E) = 0) :
    Tendsto (fun i => (ps i : Measure (ScoreGrp X n)).real E) L
      (𝓝 ((p : Measure (ScoreGrp X n)).real E)) :=
  (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hE)

lemma tendsto_mass {ι : Type*} {L : Filter ι} {ps : ι → ProbabilityMeasure (ScoreGrp X n)}
    {p : ProbabilityMeasure (ScoreGrp X n)} (h : Tendsto ps L (𝓝 p)) (g : Grp n) :
    Tendsto (fun i => groupMass (ps i) g) L (𝓝 (groupMass p g)) :=
  tendsto_real h (by rw [(isClopen_grp g).frontier_eq, measure_empty])

lemma tendsto_G {ι : Type*} {L : Filter ι} {ps : ι → ProbabilityMeasure (ScoreGrp X n)}
    {p : ProbabilityMeasure (ScoreGrp X n)} (hp : InP p) (h : Tendsto ps L (𝓝 p)) (g : Grp n)
    (y : ↥X) : Tendsto (fun i => G (ps i) g y) L (𝓝 (G p g y)) :=
  tendsto_real h (measure_mono_null (frontier_le_sub y g) (atom_zero p hp g y))

lemma quantile_contAt (hX : X.OrdConnected) [Nonempty ↥X] (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (g : Grp n) (p0 : DistSpace X n) (hg : 0 < groupMass p0.1 g) :
    ContinuousAt (fun p : DistSpace X n => quantile p.1 α g) p0 := by
  haveI := hX
  have hval : Tendsto (fun p : DistSpace X n => p.1) (𝓝 p0) (𝓝 p0.1) :=
    continuous_subtype_val.tendsto p0
  have hcdf : ∀ y : ↥X, Tendsto (fun p : DistSpace X n => condCDF p.1 g y) (𝓝 p0)
      (𝓝 (condCDF p0.1 g y)) := fun y =>
    (tendsto_G p0.2 hval g y).div (tendsto_mass hval g) hg.ne'
  have hm : ∀ᶠ p : DistSpace X n in 𝓝 p0, 0 < groupMass p.1 g :=
    (tendsto_mass hval g).eventually (lt_mem_nhds hg)
  have hspec0 := quantile_spec hX p0.1 p0.2 α hα0 hα1 g hg
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have h1 : condCDF p0.1 g a < 1 - α := hspec0 ▸ condCDF_strictMono p0.1 p0.2 g hg ha
    filter_upwards [hm, (hcdf a).eventually (gt_mem_nhds h1)] with p hpm hpa
    by_contra hcon
    have := (condCDF_strictMono p.1 p.2 g hpm).monotone (not_lt.1 hcon)
    rw [quantile_spec hX p.1 p.2 α hα0 hα1 g hpm] at this
    linarith
  · have h1 : 1 - α < condCDF p0.1 g b := hspec0 ▸ condCDF_strictMono p0.1 p0.2 g hg hb
    filter_upwards [hm, (hcdf b).eventually (lt_mem_nhds h1)] with p hpm hpb
    by_contra hcon
    have := (condCDF_strictMono p.1 p.2 g hpm).monotone (not_lt.1 hcon)
    rw [quantile_spec hX p.1 p.2 α hα0 hα1 g hpm] at this
    linarith

lemma foldl_contAt {Y Z ι : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (F : Y → Z → ι → Z) (y0 : Y)
    (hF : ∀ i, ∀ z0, ContinuousAt (fun yz : Y × Z => F yz.1 yz.2 i) (y0, z0)) :
    ∀ (l : List ι) (init : Y → Z), ContinuousAt init y0 →
      ContinuousAt (fun y => l.foldl (F y) (init y)) y0 := by
  intro l
  induction l with
  | nil => intro init h; simpa using h
  | cons a l ih =>
    intro init h
    simp only [List.foldl_cons]
    apply ih (fun y => F y (init y) a)
    have h2 : ContinuousAt (fun y => (y, init y)) y0 := continuousAt_id.prodMk h
    exact ContinuousAt.comp (g := fun yz : Y × Z => F yz.1 yz.2 a) (f := fun y => (y, init y)) (x := y0) (hF a (init y0)) h2

/-- a measure in `P` exists only if `X` has two distinct points. -/
lemma two_points (p : DistSpace X n) : ∃ a b : ↥X, a < b := by
  by_contra hcon
  push_neg at hcon
  have hsub : ∀ a b : ↥X, a = b := fun a b =>
    le_antisymm (hcon b a) (hcon a b)
  obtain ⟨g, -, hg⟩ : ∃ g ∈ (Finset.univ : Finset (Grp n)), 0 < groupMass p.1 g := by
    by_contra h
    push_neg at h
    have := sum_groupMass p.1
    have : ∑ g, groupMass p.1 g ≤ 0 := Finset.sum_nonpos (fun g hg => h g hg)
    linarith
  obtain ⟨z0, -⟩ : ({z : ScoreGrp X n | z.2 = g}).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]; intro h; unfold groupMass at hg; rw [h] at hg; simp at hg
  have := (p.2 g hg).1 z0.1
  have heq : {z : ScoreGrp X n | z.1 = z0.1 ∧ z.2 = g} = {z | z.2 = g} := by
    ext z; simp only [mem_setOf_eq, and_iff_right_iff_imp]; intro _; exact hsub _ _
  rw [heq] at this
  unfold groupMass at hg
  linarith

end IGC

namespace IGC
open Intersectionality.Generic

/-! ### mixtures -/

noncomputable def mixM {Ω : Type*} [MeasurableSpace Ω] (μ1 μ2 : Measure Ω) (ε : ℝ) : Measure Ω :=
  ENNReal.ofReal (1 - ε) • μ1 + ENNReal.ofReal ε • μ2

lemma mixM_apply {Ω : Type*} [MeasurableSpace Ω] (μ1 μ2 : Measure Ω) (ε : ℝ) (s : Set Ω) :
    mixM μ1 μ2 ε s = ENNReal.ofReal (1 - ε) * μ1 s + ENNReal.ofReal ε * μ2 s := by
  simp [mixM]

lemma mixM_real {Ω : Type*} [MeasurableSpace Ω] (μ1 μ2 : Measure Ω) [IsFiniteMeasure μ1]
    [IsFiniteMeasure μ2] (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (s : Set Ω) :
    (mixM μ1 μ2 ε).real s = (1 - ε) * μ1.real s + ε * μ2.real s := by
  rw [measureReal_def, mixM_apply,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal h0]
  rfl

lemma mixM_prob {Ω : Type*} [MeasurableSpace Ω] (μ1 μ2 : Measure Ω) [IsProbabilityMeasure μ1]
    [IsProbabilityMeasure μ2] (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsProbabilityMeasure (mixM μ1 μ2 ε) := by
  constructor
  rw [mixM_apply, measure_univ, measure_univ, mul_one, mul_one,
    ← ENNReal.ofReal_add (by linarith) h0]
  simp

noncomputable def mixP {Ω : Type*} [MeasurableSpace Ω] (p R : ProbabilityMeasure Ω) (ε : ℝ)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : ProbabilityMeasure Ω :=
  ⟨mixM p R ε, mixM_prob _ _ ε h0 h1⟩

lemma mixP_real {Ω : Type*} [MeasurableSpace Ω] (p R : ProbabilityMeasure Ω) (ε : ℝ)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (s : Set Ω) :
    (mixP p R ε h0 h1 : Measure Ω).real s =
      (1 - ε) * (p : Measure Ω).real s + ε * (R : Measure Ω).real s :=
  mixM_real _ _ ε h0 h1 s

lemma mixP_tendsto {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    (p R : ProbabilityMeasure Ω) (ε : ℕ → ℝ) (h0 : ∀ k, 0 ≤ ε k) (h1 : ∀ k, ε k ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => mixP p R (ε k) (h0 k) (h1 k)) atTop (𝓝 p) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hint : ∀ k, ∫ ω, f ω ∂(mixP p R (ε k) (h0 k) (h1 k) : Measure Ω) =
      (1 - ε k) * ∫ ω, f ω ∂(p : Measure Ω) + ε k * ∫ ω, f ω ∂(R : Measure Ω) := by
    intro k
    show ∫ ω, f ω ∂(mixM (p : Measure Ω) R (ε k)) = _
    unfold mixM
    rw [integral_add_measure ((f.integrable _).smul_measure ENNReal.ofReal_ne_top)
      ((f.integrable _).smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal (by linarith [h1 k]),
      ENNReal.toReal_ofReal (h0 k)]
    simp [smul_eq_mul]
  simp_rw [hint]
  have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hε |>.mul
    (tendsto_const_nhds (x := ∫ ω, f ω ∂(p : Measure Ω)))).add
    (hε.mul (tendsto_const_nhds (x := ∫ ω, f ω ∂(R : Measure Ω))))
  simpa using this

variable {X : Set ℝ} {n : ℕ}

lemma real_zero_of {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (s : Set Ω) (h : μ s = 0) :
    μ.real s = 0 := by rw [measureReal_def, h]; rfl

lemma inP_mix (p R : ProbabilityMeasure (ScoreGrp X n)) (hp : InP p) (hR : InP R) (ε : ℝ)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : InP (mixP p R ε h0 h1) := by
  intro g hg
  unfold groupMass at hg
  rw [mixP_real] at hg
  refine ⟨fun y => ?_, fun a b hab => ?_⟩
  · rw [mixP_real, real_zero_of _ _ (atom_zero p hp g y), real_zero_of _ _ (atom_zero R hR g y)]
    ring
  · rw [mixP_real]
    have hcase : 0 < (1 - ε) * groupMass p g ∨ 0 < ε * groupMass R g := by
      by_contra hc
      push_neg at hc
      unfold groupMass at hc
      linarith [hc.1, hc.2]
    rcases hcase with hc | hc
    · have hm : 0 < groupMass p g := pos_of_mul_pos_right hc (by linarith)
      have he : 0 < 1 - ε := pos_of_mul_pos_left hc (groupMass_nonneg p g)
      exact add_pos_of_pos_of_nonneg (mul_pos he ((hp g hm).2 a b hab))
        (mul_nonneg h0 measureReal_nonneg)
    · have hm : 0 < groupMass R g := pos_of_mul_pos_right hc h0
      have he : 0 < ε := pos_of_mul_pos_left hc (groupMass_nonneg R g)
      exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) measureReal_nonneg)
        (mul_pos he ((hR g hm).2 a b hab))

lemma mass_mix (p R : ProbabilityMeasure (ScoreGrp X n)) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (g : Grp n) :
    groupMass (mixP p R ε h0 h1) g = (1 - ε) * groupMass p g + ε * groupMass R g :=
  mixP_real p R ε h0 h1 _

lemma G_mix (p R : ProbabilityMeasure (ScoreGrp X n)) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (g : Grp n) (y : ↥X) :
    G (mixP p R ε h0 h1) g y = (1 - ε) * G p g y + ε * G R g y :=
  mixP_real p R ε h0 h1 _

/-! ### good base measures on `X` -/

def Good (ν : Measure ↥X) : Prop :=
  IsProbabilityMeasure ν ∧ (∀ x, ν {x} = 0) ∧ ∀ a b : ↥X, a < b → 0 < ν {y | a < y ∧ y < b}

lemma exists_good (hX : X.OrdConnected) (a b : ↥X) (hab : a < b) : ∃ ν : Measure ↥X, Good ν := by
  set γ := ProbabilityTheory.gaussianReal 0 1
  have hemb : MeasurableEmbedding (Subtype.val : ↥X → ℝ) :=
    MeasurableEmbedding.subtype_coe hX.measurableSet
  set ν0 : Measure ↥X := γ.comap Subtype.val
  have hν0 : ∀ s, ν0 s = γ (Subtype.val '' s) := fun s => hemb.comap_apply γ s
  have hIoo : ∀ a b : ↥X, a < b → 0 < ν0 {y | a < y ∧ y < b} := by
    intro a b hab
    rw [hν0]
    have himg : Subtype.val '' {y : ↥X | a < y ∧ y < b} = Ioo (a : ℝ) b := by
      ext x
      constructor
      · rintro ⟨y, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨x, hX.out a.2 b.2 ⟨h1.le, h2.le⟩⟩, ⟨h1, h2⟩, rfl⟩
    rw [himg, pos_iff_ne_zero]
    intro h0
    have := ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 one_ne_zero h0
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at this
    have : (a : ℝ) < b := hab
    linarith
  have hat : ∀ x, ν0 {x} = 0 := by
    intro x
    rw [hν0, image_singleton]
    exact ProbabilityTheory.gaussianReal_absolutelyContinuous 0 one_ne_zero
      (Real.volume_singleton)
  have huniv0 : ν0 univ ≠ 0 := by
    have := hIoo a b hab
    exact (lt_of_lt_of_le this (measure_mono (subset_univ _))).ne'
  have hunivtop : ν0 univ ≠ ⊤ := by
    rw [hν0]; exact measure_ne_top _ _
  refine ⟨ProbabilityTheory.cond ν0 univ,
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite huniv0 hunivtop, fun x => ?_,
    fun a b hab => ?_⟩
  · rw [ProbabilityTheory.cond_apply MeasurableSet.univ, univ_inter, hat, mul_zero]
  · rw [ProbabilityTheory.cond_apply MeasurableSet.univ, univ_inter]
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 hunivtop) (hIoo a b hab).ne'

lemma exists_good' (ν : Measure ↥X) (hν : Good ν) (t : ↥X) (c0 : ℝ) (hc0 : 0 < c0)
    (hc1 : c0 < 1) : ∃ ν' : Measure ↥X, Good ν' ∧ ν'.real {y | y ≤ t} ≠ c0 := by
  haveI := hν.1
  by_cases hc : ν.real {y | y ≤ t} = c0
  · have hne : ν {y | y ≤ t} ≠ 0 := by
      intro h; rw [real_zero_of _ _ h] at hc; linarith
    haveI hcp := ProbabilityTheory.cond_isProbabilityMeasure (μ := ν) hne
    have hmeas : MeasurableSet {y : ↥X | y ≤ t} := measurableSet_le measurable_id measurable_const
    refine ⟨mixM ν (ProbabilityTheory.cond ν {y | y ≤ t}) (1 / 2), ⟨mixM_prob _ _ _ (by norm_num)
      (by norm_num), fun x => ?_, fun a b hab => ?_⟩, ?_⟩
    · rw [mixM_apply, hν.2.1 x, ProbabilityTheory.cond_apply hmeas,
        measure_mono_null inter_subset_right (hν.2.1 x)]
      simp
    · rw [mixM_apply]
      refine lt_of_lt_of_le (ENNReal.mul_pos (by norm_num) (hν.2.2 a b hab).ne') le_self_add
    · rw [mixM_real _ _ _ (by norm_num) (by norm_num), hc,
        measureReal_def, ProbabilityTheory.cond_apply_self hne (measure_ne_top _ _)]
      simp only [ENNReal.toReal_one]
      intro h
      linarith
  · exact ⟨ν, hν, hc⟩

noncomputable def prodP (ν : Measure ↥X) (hν : Good ν) (π : Measure (Grp n))
    [IsProbabilityMeasure π] : ProbabilityMeasure (ScoreGrp X n) :=
  ⟨ν.prod π, by haveI := hν.1; infer_instance⟩

lemma prodP_apply (ν : Measure ↥X) (hν : Good ν) (π : Measure (Grp n)) [IsProbabilityMeasure π]
    (A : Set ↥X) (g : Grp n) :
    (prodP ν hν π : Measure (ScoreGrp X n)) {z | z.1 ∈ A ∧ z.2 = g} = ν A * π {g} := by
  have : {z : ScoreGrp X n | z.1 ∈ A ∧ z.2 = g} = A ×ˢ {g} := by
    ext z; simp [Set.mem_prod]
  rw [this]
  exact Measure.prod_prod _ _

lemma prodP_mass (ν : Measure ↥X) (hν : Good ν) (π : Measure (Grp n)) [IsProbabilityMeasure π]
    (g : Grp n) : groupMass (prodP ν hν π) g = π.real {g} := by
  haveI := hν.1
  unfold groupMass
  have : {z : ScoreGrp X n | z.2 = g} = {z | z.1 ∈ univ ∧ z.2 = g} := by ext; simp
  rw [this, measureReal_def, prodP_apply]
  simp [measureReal_def]

lemma prodP_G (ν : Measure ↥X) (hν : Good ν) (π : Measure (Grp n)) [IsProbabilityMeasure π]
    (g : Grp n) (y : ↥X) : G (prodP ν hν π) g y = ν.real {x | x ≤ y} * π.real {g} := by
  unfold G
  have : {z : ScoreGrp X n | z.1 ≤ y ∧ z.2 = g} = {z | z.1 ∈ {x | x ≤ y} ∧ z.2 = g} := rfl
  rw [this, measureReal_def, prodP_apply, ENNReal.toReal_mul]
  rfl

lemma inP_prodP (ν : Measure ↥X) (hν : Good ν) (π : Measure (Grp n)) [IsProbabilityMeasure π] :
    InP (prodP ν hν π) := by
  intro g hg
  rw [prodP_mass] at hg
  have hπ : π {g} ≠ 0 := by intro h; rw [real_zero_of _ _ h] at hg; exact lt_irrefl _ hg
  refine ⟨fun y => ?_, fun a b hab => ?_⟩
  · apply real_zero_of
    have : {z : ScoreGrp X n | z.1 = y ∧ z.2 = g} = {z | z.1 ∈ ({y} : Set ↥X) ∧ z.2 = g} := rfl
    rw [this, prodP_apply, hν.2.1 y, zero_mul]
  · have : {z : ScoreGrp X n | a < z.1 ∧ z.1 < b ∧ z.2 = g} =
        {z | z.1 ∈ {x | a < x ∧ x < b} ∧ z.2 = g} := by ext; simp [and_assoc]
    rw [this, measureReal_def, prodP_apply]
    apply ENNReal.toReal_pos
    · exact mul_ne_zero (hν.2.2 a b hab).ne' hπ
    · haveI := hν.1
      exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

end IGC

open Intersectionality.Generic in
theorem solution (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (n : ℕ) (hn : 2 ≤ n)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (Q : Set (↥X → ↥X)) (hQ : IsPolicyFamily Q) :
    let S : Set (DistSpace X n) :=
      {p | quantile p.1 α (oneGrp n) ≠
            (List.finRange n).foldl
              (fun x i => Function.invFun
                (transport Q (quantile p.1 α (unitGrp i)) (quantile p.1 α (zeroGrp n))) x)
              (quantile p.1 α (zeroGrp n)) ∧
          ∀ g, 0 < groupMass p.1 g}
    IsOpen S ∧ Dense S := by
  intro S
  haveI := hX
  set tgt : DistSpace X n → ↥X := fun p => (List.finRange n).foldl
      (fun x i => transport Q (quantile p.1 α (zeroGrp n)) (quantile p.1 α (unitGrp i)) x)
      (quantile p.1 α (zeroGrp n)) with htgt
  have hS : ∀ p, p ∈ S ↔ quantile p.1 α (oneGrp n) ≠ tgt p ∧ ∀ g, 0 < groupMass p.1 g := by
    intro p
    have : (fun x i => Function.invFun
        (transport Q (quantile p.1 α (unitGrp i)) (quantile p.1 α (zeroGrp n))) x) =
        (fun x i => transport Q (quantile p.1 α (zeroGrp n)) (quantile p.1 α (unitGrp i)) x) := by
      funext x i; exact IGC.invFun_T hQ _ _ x
    show (_ ∧ _) ↔ _
    rw [this]
  have hz1 : zeroGrp n ≠ oneGrp n := by
    intro h; have := congrFun h ⟨0, by omega⟩; simp [zeroGrp, oneGrp] at this
  have he1 : ∀ i : Fin n, unitGrp i ≠ oneGrp n := by
    intro i h
    obtain ⟨j, hj⟩ : ∃ j : Fin n, j ≠ i := by
      by_cases hi : i.val = 0
      · exact ⟨⟨1, by omega⟩, fun h => by rw [Fin.ext_iff] at h; simp at h; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h => by rw [Fin.ext_iff] at h; simp at h; omega⟩
    have := congrFun h j; simp [unitGrp, oneGrp, hj] at this
  constructor
  · -- openness
    rw [isOpen_iff_mem_nhds]
    intro p0 hp0
    rw [hS] at hp0
    obtain ⟨a, b, hab⟩ := IGC.two_points p0
    haveI : NoMaxOrder ↥X := ⟨fun x => ⟨transport Q a b x, IGC.Q_pointwise_lt hQ (IGC.id_mem hQ)
      (IGC.T_spec hQ a b).1 a (by rw [(IGC.T_spec hQ a b).2]; exact hab) x⟩⟩
    haveI : NoMinOrder ↥X := ⟨fun x => ⟨transport Q b a x, IGC.Q_pointwise_lt hQ
      (IGC.T_spec hQ b a).1 (IGC.id_mem hQ) b (by rw [(IGC.T_spec hQ b a).2]; exact hab) x⟩⟩
    have hβ : ∀ g, ContinuousAt (fun p : DistSpace X n => quantile p.1 α g) p0 := fun g =>
      IGC.quantile_contAt hX α hα0 hα1 g p0 (hp0.2 g)
    have ht : ContinuousAt tgt p0 := by
      apply IGC.foldl_contAt (fun (p : DistSpace X n) x i =>
        transport Q (quantile p.1 α (zeroGrp n)) (quantile p.1 α (unitGrp i)) x) p0 _ _ _ (hβ _)
      intro i z0
      have hc := (IGC.T_cont hX hQ).continuousAt
        (x := (quantile p0.1 α (zeroGrp n), (quantile p0.1 α (unitGrp i), z0)))
      have hin : ContinuousAt (fun yz : DistSpace X n × ↥X =>
          (quantile yz.1.1 α (zeroGrp n), (quantile yz.1.1 α (unitGrp i), yz.2))) (p0, z0) :=
        ((hβ (zeroGrp n)).comp (f := Prod.fst) (x := (p0, z0)) continuousAt_fst).prodMk
          (((hβ (unitGrp i)).comp (f := Prod.fst) (x := (p0, z0)) continuousAt_fst).prodMk
          continuousAt_snd)
      exact ContinuousAt.comp (f := fun yz : DistSpace X n × ↥X =>
          (quantile yz.1.1 α (zeroGrp n), (quantile yz.1.1 α (unitGrp i), yz.2)))
        (x := (p0, z0)) hc hin
    have hev1 := ((hβ (oneGrp n)).ne_iff_eventually_ne ht).1 hp0.1
    have hev2 : ∀ᶠ p in 𝓝 p0, ∀ g, 0 < groupMass (p : DistSpace X n).1 g := by
      rw [Filter.eventually_all]
      intro g
      exact (IGC.tendsto_mass (continuous_subtype_val.tendsto p0) g).eventually
        (lt_mem_nhds (hp0.2 g))
    filter_upwards [hev1, hev2] with p h1 h2
    exact (hS p).2 ⟨h1, h2⟩
  · -- density
    set M : Set (DistSpace X n) := {p | ∀ g, 0 < groupMass p.1 g}
    set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) / 2 with hεdef
    have hεpos : ∀ k, 0 < ε k := fun k => by simp only [hεdef]; positivity
    have hε0 : ∀ k, 0 ≤ ε k := fun k => (hεpos k).le
    have hεlt : ∀ k, ε k < 1 := by
      intro k
      simp only [hεdef]
      have : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
      linarith
    have hε1 : ∀ k, ε k ≤ 1 := fun k => (hεlt k).le
    have hεt : Tendsto ε atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).div_const (2 : ℝ)
      rw [zero_div] at this
      exact this
    have hM : ∀ p0 : DistSpace X n, p0 ∈ closure M := by
      intro p0
      obtain ⟨a, b, hab⟩ := IGC.two_points p0
      obtain ⟨ν, hν⟩ := IGC.exists_good hX a b hab
      set R := IGC.prodP (n := n) ν hν (PMF.uniformOfFintype (Grp n)).toMeasure
      have hRm : ∀ g, 0 < groupMass R g := by
        intro g
        rw [IGC.prodP_mass, measureReal_def, PMF.toMeasure_apply_singleton _ _
          (measurableSet_singleton g), PMF.uniformOfFintype_apply]
        apply ENNReal.toReal_pos
        · exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
        · exact ENNReal.inv_ne_top.2 (by simp)
      let seq : ℕ → DistSpace X n := fun k => ⟨IGC.mixP p0.1 R (ε k) (hε0 k) (hε1 k),
        IGC.inP_mix p0.1 R p0.2 (IGC.inP_prodP ν hν _) _ _ _⟩
      have hT : Tendsto seq atTop (𝓝 p0) :=
        tendsto_subtype_rng.2 (IGC.mixP_tendsto p0.1 R ε hε0 hε1 hεt)
      apply mem_closure_of_tendsto hT
      refine Filter.Eventually.of_forall fun k g => ?_
      show 0 < groupMass (IGC.mixP p0.1 R (ε k) (hε0 k) (hε1 k)) g
      rw [IGC.mass_mix]
      exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith [hε1 k])
        (IGC.groupMass_nonneg _ _)) (mul_pos (hεpos k) (hRm g))
    have hMS : M ⊆ closure S := by
      intro p1 hp1
      by_cases hin : p1 ∈ S
      · exact subset_closure hin
      have heq : quantile p1.1 α (oneGrp n) = tgt p1 := by
        by_contra h; exact hin ((hS p1).2 ⟨h, hp1⟩)
      set t0 := quantile p1.1 α (oneGrp n) with ht0
      have hcdf1 : condCDF p1.1 (oneGrp n) t0 = 1 - α :=
        IGC.quantile_spec hX p1.1 p1.2 α hα0 hα1 _ (hp1 _)
      obtain ⟨a, b, hab⟩ := IGC.two_points p1
      obtain ⟨ν, hν⟩ := IGC.exists_good hX a b hab
      obtain ⟨ν', hν', hw⟩ := IGC.exists_good' ν hν t0 (1 - α) (by linarith) (by linarith)
      haveI := hν'.1
      set R := IGC.prodP (n := n) ν' hν' (Measure.dirac (oneGrp n))
      have hRone : groupMass R (oneGrp n) = 1 := by
        rw [IGC.prodP_mass]; simp [measureReal_def]
      have hRother : ∀ g ≠ oneGrp n, groupMass R g = 0 := by
        intro g hg
        rw [IGC.prodP_mass, measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton g)]
        simp [Set.indicator, Ne.symm hg]
      have hRG : ∀ g ≠ oneGrp n, ∀ y, IGC.G R g y = 0 := by
        intro g hg y
        rw [IGC.prodP_G, measureReal_def (s := {g}), Measure.dirac_apply' _
          (measurableSet_singleton g)]
        simp [Set.indicator, Ne.symm hg]
      have hRG1 : IGC.G R (oneGrp n) t0 = ν'.real {x | x ≤ t0} := by
        rw [IGC.prodP_G]; simp [measureReal_def]
      let seq : ℕ → DistSpace X n := fun k => ⟨IGC.mixP p1.1 R (ε k) (hε0 k) (hε1 k),
        IGC.inP_mix p1.1 R p1.2 (IGC.inP_prodP ν' hν' _) _ _ _⟩
      have hseq : ∀ k, (seq k).1 = IGC.mixP p1.1 R (ε k) (hε0 k) (hε1 k) := fun k => rfl
      have hT : Tendsto seq atTop (𝓝 p1) :=
        tendsto_subtype_rng.2 (IGC.mixP_tendsto p1.1 R ε hε0 hε1 hεt)
      apply mem_closure_of_tendsto hT
      refine Filter.Eventually.of_forall fun k => ?_
      have hmk : ∀ g, 0 < groupMass (seq k).1 g := by
        intro g
        rw [hseq, IGC.mass_mix]
        exact add_pos_of_pos_of_nonneg (mul_pos (by linarith [hεlt k]) (hp1 g))
          (mul_nonneg (hε0 k) (IGC.groupMass_nonneg _ _))
      have hcdf_eq : ∀ g ≠ oneGrp n, condCDF (seq k).1 g = condCDF p1.1 g := by
        intro g hg
        funext y
        rw [IGC.condCDF_eq, IGC.condCDF_eq, hseq, IGC.G_mix, IGC.mass_mix, hRG g hg,
          hRother g hg]
        simp only [mul_zero, add_zero]
        exact mul_div_mul_left _ _ (by linarith [hεlt k])
      have hq_eq : ∀ g ≠ oneGrp n, quantile (seq k).1 α g = quantile p1.1 α g := by
        intro g hg; unfold quantile; rw [hcdf_eq g hg]
      have htk : tgt (seq k) = tgt p1 := by
        simp only [htgt]
        rw [hq_eq _ hz1]
        congr 1
        funext x i
        rw [hq_eq _ (he1 i)]
      rw [hS]
      refine ⟨?_, hmk⟩
      rw [htk, ← heq]
      intro hcontra
      have hs := IGC.quantile_spec hX (seq k).1 (seq k).2 α hα0 hα1 (oneGrp n) (hmk (oneGrp n))
      rw [hcontra, IGC.condCDF_eq, hseq, IGC.G_mix, IGC.mass_mix, hRG1, hRone, mul_one] at hs
      have hG1 : IGC.G p1.1 (oneGrp n) t0 = (1 - α) * groupMass p1.1 (oneGrp n) := by
        rw [IGC.condCDF_eq, div_eq_iff (hp1 _).ne'] at hcdf1
        exact hcdf1
      have hden : 0 < (1 - ε k) * groupMass p1.1 (oneGrp n) + ε k :=
        add_pos_of_nonneg_of_pos (mul_nonneg (by linarith [hεlt k])
          (IGC.groupMass_nonneg _ _)) (hεpos k)
      rw [div_eq_iff hden.ne', hG1] at hs
      apply hw
      have : ε k * ν'.real {x | x ≤ t0} = ε k * (1 - α) := by linear_combination hs
      exact mul_left_cancel₀ (hεpos k).ne' this
    rw [dense_iff_closure_eq, eq_univ_iff_forall]
    intro p
    exact closure_minimal hMS isClosed_closure (hM p)
