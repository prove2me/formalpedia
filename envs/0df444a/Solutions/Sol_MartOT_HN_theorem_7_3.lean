-- Prove2me | solution 1 for MartOT.HN.theorem_7_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:53:51.817717+00:00
-- url     : https://prove2.me/submissions/baa35604-8eda-40a1-8e2e-4424278aaea4

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Opt_optimizer_exists
import Theorems.Thm_MartOT_Abs_theorem_2_6_sufficiency
import Theorems.Thm_MartOT_HN_lemma_1_11
import Theorems.Thm_MartOT_HN_fibres_le_two_straddle
import Theorems.Thm_MartOT_HN_lemma_5_5
import Theorems.Thm_MartOT_HN_graphs_monotone
import Theorems.Thm_MartOT_HN_optimizers_convex
import Theorems.Thm_MartOT_HN_lemma_5_6

open MeasureTheory

/-- The variational property of Lemma 1.11 for `c = -|y - x|`. -/
def hn73r_Var (Γ : Set (ℝ × ℝ)) : Prop :=
  ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
    ∀ α' : Measure (ℝ × ℝ),
      MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
      MartOT.Var.cost (fun x y => -|y - x|) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
        MartOT.Var.cost (fun x y => -|y - x|) α'

lemma hn73r_Var_mono {Γ Γ' : Set (ℝ × ℝ)} (h : Γ' ⊆ Γ) (hΓ : hn73r_Var Γ) : hn73r_Var Γ' :=
  fun S w hS α' hc => hΓ S w (hS.trans h) α' hc

lemma hn73r_cost_le_zero (ρ : Measure (ℝ × ℝ)) :
    MartOT.Var.cost (fun x y => -|y - x|) ρ ≤ 0 := by
  unfold MartOT.Var.cost MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have h1 : ∀ p : ℝ × ℝ, ((-|p.2 - p.1| : ℝ) : EReal).toENNReal = 0 := by
    intro p
    apply EReal.toENNReal_of_nonpos
    exact_mod_cast neg_nonpos.mpr (abs_nonneg _)
  simp only [h1, lintegral_zero, EReal.coe_ennreal_zero, zero_sub]
  exact EReal.neg_le.mpr (by simp only [neg_zero]; exact EReal.coe_ennreal_nonneg _)

/-- The marginal identity `μ D = π (D × ℝ)`. -/
lemma hn73r_marg {μ ν : Measure ℝ} {π : Measure (ℝ × ℝ)}
    (hπ : MartOT.Var.IsMartingalePlan μ ν π) {D : Set ℝ} (hD : MeasurableSet D) :
    μ D = π (Prod.fst ⁻¹' D) := by
  rw [← hπ.1.1, Measure.map_apply measurable_fst hD]

/-- Martingale property: `x` cannot lie strictly below (or strictly above) a whole fibre on a set
of positive measure. -/
lemma hn73r_side {μ ν : Measure ℝ} {π : Measure (ℝ × ℝ)}
    (hπ : MartOT.Var.IsMartingalePlan μ ν π) (K : Set (ℝ × ℝ)) (hK : π Kᶜ = 0)
    (D : Set ℝ) (hD : MeasurableSet D) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hpos : ∀ p ∈ K, p.1 ∈ D → 0 < s * (p.2 - p.1)) : μ D = 0 := by
  have hint := hπ.2.1
  have hm := hπ.2.2
  set f : ℝ × ℝ → ℝ := fun p => (s * D.indicator (fun _ => (1:ℝ)) p.1) * (p.2 - p.1) with hf
  have hρm : Measurable (fun x : ℝ => s * D.indicator (fun _ => (1:ℝ)) x) :=
    (measurable_const.indicator hD).const_mul s
  have hρb : ∃ C, ∀ x, |s * D.indicator (fun _ => (1:ℝ)) x| ≤ C := by
    refine ⟨1, fun x => ?_⟩
    rw [abs_mul]
    have h1 : |s| = 1 := by rcases hs with rfl | rfl <;> simp
    rw [h1, one_mul]
    by_cases hx : x ∈ D <;> simp [hx]
  have hzero : ∫ p, f p ∂π = 0 := hm _ hρm hρb
  have hfint : Integrable f π := by
    obtain ⟨C, hC⟩ := hρb
    refine hint.bdd_mul (c := C) (hρm.comp measurable_fst).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun p => by simpa [Real.norm_eq_abs] using hC p.1)
  have hKae : ∀ᵐ p ∂π, p ∈ K := by
    rw [ae_iff]; simpa [Set.compl_def] using hK
  have hnn : 0 ≤ᵐ[π] f := by
    filter_upwards [hKae] with p hp
    by_cases hpD : p.1 ∈ D
    · have := hpos p hp hpD
      simp only [hf, Pi.zero_apply, Set.indicator_of_mem hpD, mul_one]
      exact this.le
    · simp [hf, Set.indicator_of_notMem hpD]
  have hf0 := (integral_eq_zero_iff_of_nonneg_ae hnn hfint).mp hzero
  have hae : ∀ᵐ p ∂π, p ∉ Prod.fst ⁻¹' D := by
    filter_upwards [hKae, hf0] with p hp hfp hpD
    have h1 := hpos p hp hpD
    simp only [hf, Pi.zero_apply, Set.indicator_of_mem (show p.1 ∈ D from hpD), mul_one] at hfp
    linarith
  rw [hn73r_marg hπ hD]
  exact measure_eq_zero_iff_ae_notMem.2 hae

/-- A countable union of compact sets has measurable projections of its closed slices. -/
lemma hn73r_proj_meas (K : ℕ → Set (ℝ × ℝ)) (hK : ∀ n, IsCompact (K n)) (L : Set (ℝ × ℝ))
    (hL : IsClosed L) : MeasurableSet (Prod.fst '' ((⋃ n, K n) ∩ L)) := by
  rw [Set.iUnion_inter, Set.image_iUnion]
  exact MeasurableSet.iUnion fun n =>
    (((hK n).inter_right hL).image continuous_fst).isClosed.measurableSet

/-- Every optimal plan is concentrated on a Borel set with the variational property, fibres of at
most two points, and fibres straddling their base point. -/
lemma hn73r_good (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (hμc : ∀ x : ℝ, μ {x} = 0) (π : Measure (ℝ × ℝ))
    (hπ : MartOT.Var.IsOptimal (fun x y => -|y - x|) μ ν π) :
    ∃ Γ : Set (ℝ × ℝ), MeasurableSet Γ ∧ π Γᶜ = 0 ∧ hn73r_Var Γ ∧
      (∀ x : ℝ, {y : ℝ | (x, y) ∈ Γ}.encard ≤ 2) ∧
      (∀ a y : ℝ, (a, y) ∈ Γ →
        (∃ y₁ : ℝ, (a, y₁) ∈ Γ ∧ y₁ ≤ a) ∧ (∃ y₂ : ℝ, (a, y₂) ∈ Γ ∧ a ≤ y₂)) := by
  have hmp := hπ.1
  -- Lemma 1.11
  have hcm : Measurable (Function.uncurry fun x y : ℝ => -|y - x|) := by
    show Measurable (fun p : ℝ × ℝ => -|p.2 - p.1|)
    fun_prop
  have hint : MartOT.Var.SuffIntegrable μ ν (fun x y => -|y - x|) := by
    refine ⟨fun x => -|x|, fun y => -|y|, hμν.1.2.abs.neg, hμν.2.1.2.abs.neg, fun x y => ?_⟩
    have := abs_sub (y) (x)
    linarith
  obtain ⟨Γ0, hΓ0m, hΓ0, hΓ0v⟩ := MartOT.HN.lemma_1_11 μ ν hμν _ hcm hint π hπ
    (lt_of_le_of_lt (hn73r_cost_le_zero π) EReal.zero_lt_top)
  -- inner regularity: a σ-compact `K ⊆ Γ0` of full measure
  have huniv : π Set.univ = 1 := by
    rw [← Set.preimage_univ (f := Prod.fst), ← Measure.map_apply measurable_fst MeasurableSet.univ,
      hmp.1.1]; simp
  have hfinΓ : π Γ0 ≠ ⊤ := ne_top_of_le_ne_top (by rw [huniv]; simp) (measure_mono (Set.subset_univ _))
  have hcpt : ∀ n : ℕ, ∃ Kn, Kn ⊆ Γ0 ∧ IsCompact Kn ∧ π (Γ0 \ Kn) < (1 / ((n : ENNReal) + 1)) :=
    fun n => hΓ0m.exists_isCompact_sdiff_lt hfinΓ (by simp)
  choose Kn hKnsub hKncpt hKnlt using hcpt
  set K := ⋃ n, Kn n with hKdef
  have hKm : MeasurableSet K := MeasurableSet.iUnion fun n => (hKncpt n).measurableSet
  have hKsub : K ⊆ Γ0 := Set.iUnion_subset hKnsub
  have hKc : π Kᶜ = 0 := by
    have h1 : π (Γ0 \ K) = 0 := by
      refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) bot_le
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε.ne'
      calc π (Γ0 \ K) ≤ π (Γ0 \ Kn n) := measure_mono (Set.sdiff_subset_sdiff_right
              (Set.subset_iUnion Kn n))
        _ ≤ 1 / ((n : ENNReal) + 1) := (hKnlt n).le
        _ ≤ (n : ENNReal)⁻¹ := by
              rw [one_div]; exact ENNReal.inv_le_inv.mpr le_self_add
        _ ≤ 0 + ε := by rw [zero_add]; exact hn.le
    have : Kᶜ ⊆ Γ0ᶜ ∪ (Γ0 \ K) := by
      intro p hp
      by_cases h : p ∈ Γ0
      · exact Or.inr ⟨h, hp⟩
      · exact Or.inl h
    exact measure_mono_null this (measure_union_null hΓ0 h1)
  -- projections
  set Lle : Set (ℝ × ℝ) := {p | p.2 ≤ p.1} with hLle
  set Lge : Set (ℝ × ℝ) := {p | p.1 ≤ p.2} with hLge
  have hLle_c : IsClosed Lle := isClosed_le continuous_snd continuous_fst
  have hLge_c : IsClosed Lge := isClosed_le continuous_fst continuous_snd
  set P := Prod.fst '' K with hP
  set Ple := Prod.fst '' (K ∩ Lle) with hPle
  set Pge := Prod.fst '' (K ∩ Lge) with hPge
  have hPm : MeasurableSet P := by
    have := hn73r_proj_meas Kn hKncpt Set.univ isClosed_univ
    rwa [Set.inter_univ] at this
  have hPlem : MeasurableSet Ple := hn73r_proj_meas Kn hKncpt Lle hLle_c
  have hPgem : MeasurableSet Pge := hn73r_proj_meas Kn hKncpt Lge hLge_c
  have hPc : μ Pᶜ = 0 := by
    rw [hn73r_marg hmp hPm.compl]
    exact measure_mono_null (fun p hp hpK => hp ⟨p, hpK, rfl⟩) hKc
  have hD1 : μ (P \ Ple) = 0 := by
    refine hn73r_side hmp K hKc _ (hPm.diff hPlem) 1 (Or.inl rfl) fun p hpK hpD => ?_
    have : ¬ p.2 ≤ p.1 := fun h => hpD.2 ⟨p, ⟨hpK, h⟩, rfl⟩
    linarith [not_le.mp this]
  have hD2 : μ (P \ Pge) = 0 := by
    refine hn73r_side hmp K hKc _ (hPm.diff hPgem) (-1) (Or.inr rfl) fun p hpK hpD => ?_
    have : ¬ p.1 ≤ p.2 := fun h => hpD.2 ⟨p, ⟨hpK, h⟩, rfl⟩
    linarith [not_le.mp this]
  set St := Ple ∩ Pge with hSt
  have hStm : MeasurableSet St := hPlem.inter hPgem
  have hStc : μ Stᶜ = 0 := by
    have : Stᶜ ⊆ Pᶜ ∪ (P \ Ple) ∪ (P \ Pge) := by
      intro x hx
      by_cases hxP : x ∈ P
      · rcases not_and_or.mp hx with h | h
        · exact Or.inl (Or.inr ⟨hxP, h⟩)
        · exact Or.inr ⟨hxP, h⟩
      · exact Or.inl (Or.inl hxP)
    exact measure_mono_null this (measure_union_null (measure_union_null hPc hD1) hD2)
  -- restrict to straddling fibres
  set Γ1 := K ∩ Prod.fst ⁻¹' St with hΓ1
  have hΓ1m : MeasurableSet Γ1 := hKm.inter (measurable_fst hStm)
  have hΓ1c : π Γ1ᶜ = 0 := by
    rw [Set.compl_inter]
    refine measure_union_null hKc ?_
    rw [← Set.preimage_compl, ← hn73r_marg hmp hStm.compl]; exact hStc
  have hΓ1v : hn73r_Var Γ1 := hn73r_Var_mono (Set.inter_subset_left.trans hKsub) hΓ0v
  have hΓ1s : ∀ a y : ℝ, (a, y) ∈ Γ1 →
      (∃ y₁ : ℝ, (a, y₁) ∈ Γ1 ∧ y₁ ≤ a) ∧ (∃ y₂ : ℝ, (a, y₂) ∈ Γ1 ∧ a ≤ y₂) := by
    rintro a y ⟨-, haSt⟩
    obtain ⟨⟨q, ⟨hqK, hq⟩, rfl⟩, ⟨r, ⟨hrK, hr⟩, hra⟩⟩ := haSt
    refine ⟨⟨q.2, ⟨hqK, ?_⟩, hq⟩, ⟨r.2, ⟨?_, ?_⟩, ?_⟩⟩
    · exact ⟨⟨q, ⟨hqK, hq⟩, rfl⟩, ⟨r, ⟨hrK, hr⟩, hra⟩⟩
    · have : r = (q.1, r.2) := Prod.ext hra rfl
      rw [← this]; exact hrK
    · exact ⟨⟨q, ⟨hqK, hq⟩, rfl⟩, ⟨r, ⟨hrK, hr⟩, hra⟩⟩
    · have := hr; simp only [hLge, Set.mem_ofPred_eq] at this; rw [← hra]; exact this
  -- remove the countable set of fibres with more than two points
  obtain ⟨hAc, hA0⟩ := MartOT.HN.fibres_le_two_straddle μ hμc Γ1 hΓ1v hΓ1s
  set A := {a : ℝ | 2 < {y : ℝ | (a, y) ∈ Γ1}.encard} with hA
  have hAm : MeasurableSet A := hAc.measurableSet
  refine ⟨Γ1 ∩ Prod.fst ⁻¹' Aᶜ, hΓ1m.inter (measurable_fst hAm.compl), ?_,
    hn73r_Var_mono (Set.inter_subset_left) hΓ1v, ?_, ?_⟩
  · rw [Set.compl_inter, ← Set.preimage_compl, compl_compl]
    refine measure_union_null hΓ1c ?_
    rw [← hn73r_marg hmp hAm]; exact hA0
  · intro x
    by_cases hx : x ∈ A
    · have : {y : ℝ | (x, y) ∈ Γ1 ∩ Prod.fst ⁻¹' Aᶜ} = ∅ := by
        ext y; simp [hx]
      rw [this]; simp
    · refine le_trans (Set.encard_le_encard fun y hy => hy.1) ?_
      exact not_lt.mp hx
  · rintro a y ⟨hay, haA⟩
    obtain ⟨⟨y₁, h1, h1'⟩, ⟨y₂, h2, h2'⟩⟩ := hΓ1s a y hay
    exact ⟨⟨y₁, ⟨h1, haA⟩, h1'⟩, ⟨y₂, ⟨h2, haA⟩, h2'⟩⟩

theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (hμc : ∀ x : ℝ, μ {x} = 0) :
    ∃ π : Measure (ℝ × ℝ), MartOT.Var.IsOptimal (fun x y => -|y - x|) μ ν π ∧
      (∀ π' : Measure (ℝ × ℝ), MartOT.Var.IsOptimal (fun x y => -|y - x|) μ ν π' → π' = π) ∧
      ∃ (S : Set ℝ) (T₁ T₂ : ℝ → ℝ), MeasurableSet S ∧ μ Sᶜ = 0 ∧
        MonotoneOn T₁ S ∧ MonotoneOn T₂ S ∧ (∀ x ∈ S, T₁ x ≤ x ∧ x ≤ T₂ x) ∧
        π {p : ℝ × ℝ | ¬ (p.1 ∈ S ∧ (p.2 = T₁ p.1 ∨ p.2 = T₂ p.1))} = 0 := by
  -- existence
  have hc : LowerSemicontinuous (Function.uncurry fun x y : ℝ => -|y - x|) := by
    have : Continuous (Function.uncurry fun x y : ℝ => -|y - x|) := by
      show Continuous (fun p : ℝ × ℝ => -|p.2 - p.1|)
      fun_prop
    exact this.lowerSemicontinuous
  have hint : MartOT.Var.SuffIntegrable μ ν (fun x y => -|y - x|) := by
    refine ⟨fun x => -|x|, fun y => -|y|, hμν.1.2.abs.neg, hμν.2.1.2.abs.neg, fun x y => ?_⟩
    have := abs_sub (y) (x)
    linarith
  obtain ⟨π, hπ⟩ := MartOT.Opt.optimizer_exists μ ν hμν.1 hμν.2.1 _ hc hint
    (MartOT.Abs.theorem_2_6_sufficiency μ ν hμν)
  refine ⟨π, hπ, ?_, ?_⟩
  · -- uniqueness (Lemma 5.6)
    intro π' hπ'
    set E : Set (Measure (ℝ × ℝ)) :=
      {σ | MartOT.Var.IsOptimal (fun x y => -|y - x|) μ ν σ} with hE
    obtain ⟨σ0, hσ0⟩ := MartOT.HN.lemma_5_6 μ ν hμν E (fun σ hσ => hσ.1) ⟨π, hπ⟩
      (fun σ hσ σ' hσ' t ht => MartOT.HN.optimizers_convex μ ν hμν σ σ' hσ hσ' t ht)
      (fun σ hσ => by
        obtain ⟨Γ, -, hΓ0, -, hfib, -⟩ := hn73r_good μ ν hμν hμc σ hσ
        exact ⟨Γ, hΓ0, hfib⟩)
    have e1 : π ∈ E := hπ
    have e2 : π' ∈ E := hπ'
    rw [hσ0] at e1 e2
    rw [Set.mem_singleton_iff.mp e1, Set.mem_singleton_iff.mp e2]
  · -- structure (Lemma 5.5 and the monotonicity step)
    obtain ⟨Γ, hΓm, hΓ0, hΓv, hfib, hstr⟩ := hn73r_good μ ν hμν hμc π hπ
    obtain ⟨hSm, T₁, T₂, -, -, hT12, hΓeq⟩ := MartOT.HN.lemma_5_5 Γ hΓm hfib
    set S := Prod.fst '' Γ with hS
    have hmemT : ∀ x ∈ S, (x, T₁ x) ∈ Γ ∧ (x, T₂ x) ∈ Γ := by
      intro x hx
      constructor
      · rw [hΓeq]; exact ⟨hx, Or.inl rfl⟩
      · rw [hΓeq]; exact ⟨hx, Or.inr rfl⟩
    have hTx : ∀ x ∈ S, T₁ x ≤ x ∧ x ≤ T₂ x := by
      intro x hx
      obtain ⟨p, hpΓ, hpx⟩ := hx
      have hxy : (x, p.2) ∈ Γ := by rw [← hpx]; exact hpΓ
      obtain ⟨⟨y₁, h1, h1'⟩, ⟨y₂, h2, h2'⟩⟩ := hstr x p.2 hxy
      have hxS : x ∈ S := ⟨p, hpΓ, hpx⟩
      have h12 := hT12 x hxS
      rw [hΓeq] at h1 h2
      obtain ⟨-, h1e⟩ := h1
      obtain ⟨-, h2e⟩ := h2
      constructor
      · rcases h1e with h | h <;> simp only at h <;> linarith
      · rcases h2e with h | h <;> simp only at h <;> linarith
    obtain ⟨hm1, hm2⟩ := MartOT.HN.graphs_monotone Γ hΓv S T₁ T₂ (fun x hx => (hmemT x hx).1)
      (fun x hx => (hmemT x hx).2) hTx
    refine ⟨S, T₁, T₂, hSm, ?_, hm1, hm2, hTx, ?_⟩
    · rw [hn73r_marg hπ.1 hSm.compl]
      exact measure_mono_null (fun p hp hpΓ => hp ⟨p, hpΓ, rfl⟩) hΓ0
    · have : {p : ℝ × ℝ | ¬ (p.1 ∈ S ∧ (p.2 = T₁ p.1 ∨ p.2 = T₂ p.1))} = Γᶜ := by
        conv_rhs => rw [hΓeq]
        rfl
      rw [this]; exact hΓ0
