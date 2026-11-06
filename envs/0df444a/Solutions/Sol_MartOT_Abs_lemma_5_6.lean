-- Prove2me | solution 1 for MartOT.Abs.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T06:02:19.87939+00:00
-- url     : https://prove2.me/submissions/652617a2-5be5-40a7-b09f-10572fd7063f

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_HN_lemma_5_5

open MeasureTheory

/-- Cancelling a positive bounded density. -/
lemma hn56_cancel (n n' : Measure ℝ) [IsFiniteMeasure n] [IsFiniteMeasure n'] (D : Set ℝ)
    (hD : MeasurableSet D) (h : ℝ → ℝ) (hm : Measurable h) (C : ℝ)
    (hpos : ∀ x ∈ D, 0 < h x) (hbd : ∀ x ∈ D, h x ≤ C)
    (heq : ∀ B : Set ℝ, MeasurableSet B → B ⊆ D →
      ∫ x, B.indicator h x ∂n = ∫ x, B.indicator h x ∂n') :
    n.restrict D = n'.restrict D := by
  set f : ℝ → ENNReal := fun x => ENNReal.ofReal (h x) with hf
  have hfm : Measurable f := ENNReal.measurable_ofReal.comp hm
  have hint : ∀ (m : Measure ℝ) [IsFiniteMeasure m] (B : Set ℝ), MeasurableSet B → B ⊆ D →
      IntegrableOn h B m := by
    intro m _ B hB hBD
    refine Measure.integrableOn_of_bounded (M := C) (measure_ne_top _ _)
      hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hB] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (hpos x (hBD hx))]
    exact hbd x (hBD hx)
  have hval : ∀ (m : Measure ℝ) [IsFiniteMeasure m] (B : Set ℝ), MeasurableSet B →
      (m.restrict D).withDensity f B = ENNReal.ofReal (∫ x, (B ∩ D).indicator h x ∂m) := by
    intro m _ B hB
    rw [withDensity_apply _ hB, Measure.restrict_restrict hB, integral_indicator (hB.inter hD),
      ofReal_integral_eq_lintegral_ofReal (hint m _ (hB.inter hD) Set.inter_subset_right)]
    filter_upwards [ae_restrict_mem (hB.inter hD)] with x hx
    exact (hpos x hx.2).le
  have hwd : (n.restrict D).withDensity f = (n'.restrict D).withDensity f := by
    ext B hB
    rw [hval n B hB, hval n' B hB, heq _ (hB.inter hD) Set.inter_subset_right]
  have hne0 : ∀ m : Measure ℝ, ∀ᵐ x ∂(m.restrict D), f x ≠ 0 := by
    intro m
    filter_upwards [ae_restrict_mem hD] with x hx
    simp only [hf, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hpos x hx
  have hnetop : ∀ m : Measure ℝ, ∀ᵐ x ∂(m.restrict D), f x ≠ ⊤ :=
    fun m => Filter.Eventually.of_forall fun x => ENNReal.ofReal_ne_top
  rw [← withDensity_inv_same hfm (hne0 n) (hnetop n),
    ← withDensity_inv_same hfm (hne0 n') (hnetop n'), hwd]

/-- Two martingale plans concentrated on a common Borel set with fibres of at most two points
coincide. -/
lemma hn56_uniq (μ ν : Measure ℝ) [IsFiniteMeasure μ] (Γ : Set (ℝ × ℝ)) (hΓm : MeasurableSet Γ)
    (hfib : ∀ x : ℝ, {y : ℝ | (x, y) ∈ Γ}.encard ≤ 2) (π π' : Measure (ℝ × ℝ))
    (hπ : MartOT.Var.IsMartingalePlan μ ν π) (hπ' : MartOT.Var.IsMartingalePlan μ ν π')
    (h0 : π Γᶜ = 0) (h0' : π' Γᶜ = 0) : π = π' := by
  obtain ⟨hSm, T₁, T₂, hT₁, hT₂, hle, hΓeq⟩ := MartOT.HN.lemma_5_5 Γ hΓm hfib
  set S := Prod.fst '' Γ with hS
  set G₁ : Set (ℝ × ℝ) := {p | p.1 ∈ S ∧ p.2 = T₁ p.1} with hG₁
  set G₂ : Set (ℝ × ℝ) := {p | p.1 ∈ S ∧ p.2 = T₂ p.1 ∧ T₁ p.1 < T₂ p.1} with hG₂
  set D : Set ℝ := {x | x ∈ S ∧ T₁ x < T₂ x} with hD
  have hG₁m : MeasurableSet G₁ :=
    (measurable_fst hSm).inter (measurableSet_eq_fun measurable_snd (hT₁.comp measurable_fst))
  have hG₂m : MeasurableSet G₂ :=
    (measurable_fst hSm).inter ((measurableSet_eq_fun measurable_snd (hT₂.comp measurable_fst)).inter
      (measurableSet_lt (hT₁.comp measurable_fst) (hT₂.comp measurable_fst)))
  have hDm : MeasurableSet D := hSm.inter (measurableSet_lt hT₁ hT₂)
  have hdisj : Disjoint G₁ G₂ := by
    rw [Set.disjoint_left]
    rintro p ⟨-, h1⟩ ⟨-, h2, h3⟩
    rw [h1] at h2; rw [h2] at h3; exact lt_irrefl _ h3
  have hΓU : Γ = G₁ ∪ G₂ := by
    ext p
    constructor
    · intro hp
      rw [hΓeq] at hp
      obtain ⟨hpS, h | h⟩ := hp
      · exact Or.inl ⟨hpS, h⟩
      · rcases eq_or_lt_of_le (hle p.1 hpS) with he | hlt
        · exact Or.inl ⟨hpS, h.trans he.symm⟩
        · exact Or.inr ⟨hpS, h, hlt⟩
    · rintro (⟨hpS, h⟩ | ⟨hpS, h, -⟩) <;> rw [hΓeq]
      · exact ⟨hpS, Or.inl h⟩
      · exact ⟨hpS, Or.inr h⟩
  set φ₁ : ℝ → ℝ × ℝ := fun x => (x, T₁ x) with hφ₁
  set φ₂ : ℝ → ℝ × ℝ := fun x => (x, T₂ x) with hφ₂
  have hφ₁m : Measurable φ₁ := measurable_id.prodMk hT₁
  have hφ₂m : Measurable φ₂ := measurable_id.prodMk hT₂
  set DN : ℕ → Set ℝ := fun N => {x | x ∈ D ∧ |T₁ x - x| ≤ N ∧ |T₂ x - x| ≤ N} with hDN
  have hDNm : ∀ N, MeasurableSet (DN N) := fun N =>
    hDm.inter ((measurableSet_le ((hT₁.sub measurable_id).abs) measurable_const).inter
      (measurableSet_le ((hT₂.sub measurable_id).abs) measurable_const))
  -- the structure of a single plan
  have key : ∀ ρ : Measure (ℝ × ℝ), MartOT.Var.IsMartingalePlan μ ν ρ → ρ Γᶜ = 0 →
      IsFiniteMeasure ρ ∧
      ρ = ((ρ.restrict G₁).map Prod.fst).map φ₁ + ((ρ.restrict G₂).map Prod.fst).map φ₂ ∧
      (ρ.restrict G₁).map Prod.fst + (ρ.restrict G₂).map Prod.fst = μ ∧
      (ρ.restrict G₂).map Prod.fst Dᶜ = 0 ∧
      ∀ N : ℕ, ∀ B : Set ℝ, MeasurableSet B → B ⊆ DN N →
        ∫ x, B.indicator (fun x => T₂ x - T₁ x) x ∂((ρ.restrict G₁).map Prod.fst) =
          ∫ x, B.indicator (fun _ => (1:ℝ)) x * (T₂ x - x) ∂μ := by
    intro ρ hρ hρ0
    have hfin : IsFiniteMeasure ρ := ⟨by
      rw [← Set.preimage_univ (f := Prod.fst), ← Measure.map_apply measurable_fst MeasurableSet.univ,
        hρ.1.1]; exact measure_lt_top μ _⟩
    have hsplit : ρ = ρ.restrict G₁ + ρ.restrict G₂ := by
      rw [← Measure.restrict_union hdisj hG₂m, ← hΓU]
      exact (Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; simpa [Set.compl_def] using hρ0)).symm
    have hpiece : ∀ (G : Set (ℝ × ℝ)) (T : ℝ → ℝ) (φ : ℝ → ℝ × ℝ), MeasurableSet G →
        Measurable φ → (∀ x, φ x = (x, T x)) → (∀ p ∈ G, p.2 = T p.1) →
        ρ.restrict G = ((ρ.restrict G).map Prod.fst).map φ := by
      intro G T φ hGm hφm hφ hGT
      ext U hU
      rw [Measure.map_apply hφm hU, Measure.map_apply measurable_fst (hφm hU),
        Measure.restrict_apply hU, Measure.restrict_apply (measurable_fst (hφm hU))]
      congr 1
      ext p
      constructor
      · rintro ⟨hpU, hpG⟩
        refine ⟨?_, hpG⟩
        show φ p.1 ∈ U
        rw [hφ, ← hGT p hpG]; exact hpU
      · rintro ⟨hpU, hpG⟩
        refine ⟨?_, hpG⟩
        have : φ p.1 ∈ U := hpU
        rw [hφ, ← hGT p hpG] at this; exact this
    have hp1 := hpiece G₁ T₁ φ₁ hG₁m hφ₁m (fun x => rfl) (fun p hp => hp.2)
    have hp2 := hpiece G₂ T₂ φ₂ hG₂m hφ₂m (fun x => rfl) (fun p hp => hp.2.1)
    have hmarg : (ρ.restrict G₁).map Prod.fst + (ρ.restrict G₂).map Prod.fst = μ := by
      rw [← Measure.map_add _ _ measurable_fst, ← hsplit, hρ.1.1]
    refine ⟨hfin, ?_, hmarg, ?_, ?_⟩
    · conv_lhs => rw [hsplit, hp1, hp2]
    · rw [Measure.map_apply measurable_fst hDm.compl, Measure.restrict_apply (measurable_fst hDm.compl)]
      convert measure_empty (μ := ρ)
      ext p
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro hpD hpG
      exact hpD ⟨hpG.1, hpG.2.2⟩
    · intro N B hB hBD
      set n₁ := (ρ.restrict G₁).map Prod.fst with hn₁
      set n₂ := (ρ.restrict G₂).map Prod.fst with hn₂
      haveI : IsFiniteMeasure n₁ := by rw [hn₁]; infer_instance
      haveI : IsFiniteMeasure n₂ := by rw [hn₂]; infer_instance
      set F : (ℝ → ℝ) → ℝ → ℝ := fun T x => B.indicator (fun _ => (1:ℝ)) x * (T x - x) with hF
      have hFb : ∀ T : ℝ → ℝ, (∀ x ∈ DN N, |T x - x| ≤ N) → ∀ x, ‖F T x‖ ≤ N := by
        intro T hT x
        by_cases hx : x ∈ B
        · simp only [hF, Set.indicator_of_mem hx, one_mul, Real.norm_eq_abs]
          exact hT x (hBD hx)
        · simp [hF, Set.indicator_of_notMem hx]
      have hFm : ∀ T : ℝ → ℝ, Measurable T → Measurable (F T) := fun T hT =>
        (measurable_const.indicator hB).mul (hT.sub measurable_id)
      have hFi : ∀ (m : Measure ℝ) [IsFiniteMeasure m] (T : ℝ → ℝ), Measurable T →
          (∀ x ∈ DN N, |T x - x| ≤ N) → Integrable (F T) m := fun m _ T hT hTb =>
        Integrable.of_bound (hFm T hT).aestronglyMeasurable N (Filter.Eventually.of_forall (hFb T hTb))
      have hb1 : ∀ x ∈ DN N, |T₁ x - x| ≤ N := fun x hx => hx.2.1
      have hb2 : ∀ x ∈ DN N, |T₂ x - x| ≤ N := fun x hx => hx.2.2
      -- the martingale identity
      have hmart : ∫ x, F T₁ x ∂n₁ + ∫ x, F T₂ x ∂n₂ = 0 := by
        set g : ℝ × ℝ → ℝ := fun p => B.indicator (fun _ => (1:ℝ)) p.1 * (p.2 - p.1) with hg
        have hgm : Measurable g :=
          ((measurable_const.indicator hB).comp measurable_fst).mul (measurable_snd.sub measurable_fst)
        have hgi : Integrable g ρ := by
          refine hρ.2.1.bdd_mul (c := 1)
            ((measurable_const.indicator hB).comp measurable_fst).aestronglyMeasurable ?_
          refine Filter.Eventually.of_forall (fun p => ?_)
          by_cases hp : p.1 ∈ B <;> simp [hp]
        have h0 : ∫ p, g p ∂ρ = 0 := hρ.2.2 _ (measurable_const.indicator hB)
          ⟨1, fun x => by by_cases hx : x ∈ B <;> simp [hx]⟩
        have hconv : ∀ (G : Set (ℝ × ℝ)) (T : ℝ → ℝ) (φ : ℝ → ℝ × ℝ), Measurable φ →
            (∀ x, φ x = (x, T x)) → ρ.restrict G = ((ρ.restrict G).map Prod.fst).map φ →
            ∫ p, g p ∂(ρ.restrict G) = ∫ x, F T x ∂((ρ.restrict G).map Prod.fst) := by
          intro G T φ hφm hφ hG
          conv_lhs => rw [hG]
          rw [integral_map hφm.aemeasurable hgm.aestronglyMeasurable]
          congr 1
          ext x
          simp only [hg, hF, hφ]
        rw [hsplit, integral_add_measure (hgi.mono_measure Measure.restrict_le_self)
          (hgi.mono_measure Measure.restrict_le_self)] at h0
        rw [hconv G₁ T₁ φ₁ hφ₁m (fun x => rfl) hp1, hconv G₂ T₂ φ₂ hφ₂m (fun x => rfl) hp2] at h0
        exact h0
      have hsplitμ : ∫ x, F T₂ x ∂μ = ∫ x, F T₂ x ∂n₁ + ∫ x, F T₂ x ∂n₂ := by
        rw [← hmarg, integral_add_measure (hFi n₁ T₂ hT₂ hb2) (hFi n₂ T₂ hT₂ hb2)]
      have hind : (fun x => B.indicator (fun x => T₂ x - T₁ x) x) = fun x => F T₂ x - F T₁ x := by
        ext x
        by_cases hx : x ∈ B <;> simp [hF, hx]
      rw [hind, integral_sub (hFi n₁ T₂ hT₂ hb2) (hFi n₁ T₁ hT₁ hb1)]
      show _ = ∫ x, F T₂ x ∂μ
      linarith
  obtain ⟨hf1, ha1, hb1, hc1, hd1⟩ := key π hπ h0
  obtain ⟨hf2, ha2, hb2, hc2, hd2⟩ := key π' hπ' h0'
  set n₁ := (π.restrict G₁).map Prod.fst with hn₁
  set n₂ := (π.restrict G₂).map Prod.fst with hn₂
  set n₁' := (π'.restrict G₁).map Prod.fst with hn₁'
  set n₂' := (π'.restrict G₂).map Prod.fst with hn₂'
  haveI : IsFiniteMeasure n₁ := by rw [hn₁]; infer_instance
  haveI : IsFiniteMeasure n₁' := by rw [hn₁']; infer_instance
  -- the first pieces agree on `D`
  have hD_eq : D = ⋃ N : ℕ, DN N := by
    ext x
    constructor
    · intro hx
      obtain ⟨N, hN⟩ := exists_nat_ge (max |T₁ x - x| |T₂ x - x|)
      exact Set.mem_iUnion.mpr ⟨N, hx, (le_max_left _ _).trans hN, (le_max_right _ _).trans hN⟩
    · intro hx
      obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hx
      exact hN.1
  have hresD : n₁.restrict D = n₁'.restrict D := by
    rw [hD_eq, Measure.restrict_iUnion_congr]
    intro N
    refine hn56_cancel n₁ n₁' (DN N) (hDNm N) (fun x => T₂ x - T₁ x) (hT₂.sub hT₁) (2 * N)
      (fun x hx => by have := hx.1.2; linarith) (fun x hx => ?_) (fun B hB hBD => ?_)
    · have h1 := abs_le.mp hx.2.1
      have h2 := abs_le.mp hx.2.2
      linarith [h1.1, h2.2]
    · rw [hd1 N B hB hBD, hd2 N B hB hBD]
  have hresDc : ∀ (m₁ m₂ : Measure ℝ), m₁ + m₂ = μ → m₂ Dᶜ = 0 → m₁.restrict Dᶜ = μ.restrict Dᶜ := by
    intro m₁ m₂ hm hm2
    rw [← hm, Measure.restrict_add, Measure.restrict_eq_zero.mpr hm2, add_zero]
  have hn1eq : n₁ = n₁' := by
    rw [← Measure.restrict_add_restrict_compl (μ := n₁) hDm,
      ← Measure.restrict_add_restrict_compl (μ := n₁') hDm, hresD, hresDc n₁ n₂ hb1 hc1,
      hresDc n₁' n₂' hb2 hc2]
  have hn2eq : n₂ = n₂' := by
    ext U hU
    have e1 := congrArg (fun m : Measure ℝ => m U) hb1
    have e2 := congrArg (fun m : Measure ℝ => m U) hb2
    simp only [Measure.coe_add, Pi.add_apply] at e1 e2
    rw [← e2, hn1eq] at e1
    exact (ENNReal.add_right_inj (measure_ne_top n₁' U)).mp e1
  rw [ha1, ha2, hn1eq, hn2eq]

theorem solution (μ ν : Measure ℝ) (hμν : MartOT.Var.ConvexLE μ ν) (E : Set (Measure (ℝ × ℝ)))
    (hE : ∀ π ∈ E, MartOT.Var.IsMartingalePlan μ ν π) (hne : E.Nonempty)
    (hconv : ∀ π ∈ E, ∀ π' ∈ E, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal t • π + ENNReal.ofReal (1 - t) • π' ∈ E)
    (hfib : ∀ π ∈ E, ∃ Γ : Set (ℝ × ℝ), π Γᶜ = 0 ∧ ∀ x : ℝ, {y : ℝ | (x, y) ∈ Γ}.encard ≤ 2) :
    ∃ π : Measure (ℝ × ℝ), E = {π} := by
  haveI : IsFiniteMeasure μ := hμν.1.1
  have pair : ∀ π₁ ∈ E, ∀ π₂ ∈ E, π₁ = π₂ := by
    intro π₁ h₁ π₂ h₂
    have hmid := hconv π₁ h₁ π₂ h₂ (1 / 2) ⟨by norm_num, by norm_num⟩
    obtain ⟨Γ, hΓ0, hΓfib⟩ := hfib _ hmid
    obtain ⟨N, hNsup, hNm, hN0⟩ := exists_measurable_superset_of_null hΓ0
    have hhalf : ENNReal.ofReal (1 / 2) ≠ 0 := by simp
    have hhalf' : ENNReal.ofReal (1 - 1 / 2) ≠ 0 := by norm_num
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      add_eq_zero, mul_eq_zero, hhalf, hhalf', false_or] at hN0
    have hfibN : ∀ x : ℝ, {y : ℝ | (x, y) ∈ Nᶜ}.encard ≤ 2 := by
      intro x
      refine le_trans (Set.encard_le_encard fun y hy => ?_) (hΓfib x)
      by_contra hyΓ
      exact hy (hNsup hyΓ)
    exact hn56_uniq μ ν Nᶜ hNm.compl hfibN π₁ π₂ (hE π₁ h₁) (hE π₂ h₂)
      (by rw [compl_compl]; exact hN0.1) (by rw [compl_compl]; exact hN0.2)
  obtain ⟨π₀, h₀⟩ := hne
  refine ⟨π₀, Set.eq_singleton_iff_unique_mem.mpr ⟨h₀, fun σ hσ => pair σ hσ π₀ h₀⟩⟩
