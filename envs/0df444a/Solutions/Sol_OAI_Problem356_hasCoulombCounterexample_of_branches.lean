-- Prove2me | solution 1 for OAI.Problem356.hasCoulombCounterexample_of_branches
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:33:57.037241+00:00
-- url     : https://prove2.me/submissions/4b35a659-44b9-470c-93e9-c581b51e09e7

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure

open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal
theorem pb_map_zero {nu : Measure E3} {g : E3 → Triple} (hg : Measurable g)
    {P : Triple → Prop} (hP : MeasurableSet {t | P t}) (h : ∀ᵐ x ∂nu, P (g x)) :
    Measure.map g nu {t | ¬ P t} = 0 := by
  rw [show {t | ¬ P t} = {t | P t}ᶜ from rfl, Measure.map_apply hg hP.compl]
  exact ae_iff.mp h

theorem pb_ae_branchCoupling (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) {P : Triple → Prop} (hP : MeasurableSet {t | P t})
    (hcycle : ∀ x y z, P (x, (y, z)) → P (y, (z, x)))
    (h12 : ∀ᵐ x ∂nu, P (x, (H1 x, H2 x)))
    (h34 : ∀ᵐ x ∂nu, P (x, (H3 x, H4 x))) :
    ∀ᵐ t ∂branchCoupling nu H1 H2 H3 H4, P t := by
  have hg : ∀ f g h : E3 → E3, Measurable f → Measurable g → Measurable h →
      Measurable (branchGraph f g h) := fun f g h hf hg hh => hf.prodMk (hg.prodMk hh)
  rw [ae_iff]
  simp only [branchCoupling, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  rw [pb_map_zero (hg _ _ _ measurable_id h1 h2) hP h12,
    pb_map_zero (hg _ _ _ h1 h2 measurable_id) hP (h12.mono fun x hx => hcycle _ _ _ hx),
    pb_map_zero (hg _ _ _ h2 measurable_id h1) hP
      (h12.mono fun x hx => hcycle _ _ _ (hcycle _ _ _ hx)),
    pb_map_zero (hg _ _ _ measurable_id h3 h4) hP h34,
    pb_map_zero (hg _ _ _ h3 h4 measurable_id) hP (h34.mono fun x hx => hcycle _ _ _ hx),
    pb_map_zero (hg _ _ _ h4 measurable_id h3) hP
      (h34.mono fun x hx => hcycle _ _ _ (hcycle _ _ _ hx))]
  simp

theorem pb_isProb (nu : Measure E3) [IsProbabilityMeasure nu]
    {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) : IsProbabilityMeasure (branchCoupling nu H1 H2 H3 H4) := by
  have hg : ∀ f g h : E3 → E3, Measurable f → Measurable g → Measurable h →
      Measurable (branchGraph f g h) := fun f g h hf hg hh => hf.prodMk (hg.prodMk hh)
  constructor
  simp only [branchCoupling, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  rw [Measure.map_apply (hg _ _ _ measurable_id h1 h2) MeasurableSet.univ,
    Measure.map_apply (hg _ _ _ h1 h2 measurable_id) MeasurableSet.univ,
    Measure.map_apply (hg _ _ _ h2 measurable_id h1) MeasurableSet.univ,
    Measure.map_apply (hg _ _ _ measurable_id h3 h4) MeasurableSet.univ,
    Measure.map_apply (hg _ _ _ h3 h4 measurable_id) MeasurableSet.univ,
    Measure.map_apply (hg _ _ _ h4 measurable_id h3) MeasurableSet.univ]
  simp only [Set.preimage_univ, measure_univ]
  have : (1 : ℝ≥0∞) + 1 + 1 + 1 + 1 + 1 = 6 := by norm_num
  rw [this]
  exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)

theorem pb_third : (1 / 3 : ℝ≥0∞) = 1 / 6 + 1 / 6 := by
  rw [ENNReal.div_add_div_same]
  rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

theorem pb_map_graph (nu : Measure E3) {f g h : E3 → E3} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) (π : Triple → E3) (hπ : Measurable π) (k : E3 → E3)
    (hk : π ∘ branchGraph f g h = k) :
    Measure.map π (Measure.map (branchGraph f g h) nu) = Measure.map k nu := by
  rw [Measure.map_map hπ (show Measurable (branchGraph f g h) from hf.prodMk (hg.prodMk hh)), hk]

theorem pb_coupling (nu : Measure E3) [IsProbabilityMeasure nu]
    {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) :
    IsThreeCoupling (branchMarginal nu H1 H2 H3 H4) (branchCoupling nu H1 H2 H3 H4) := by
  have hg : ∀ f g h : E3 → E3, Measurable f → Measurable g → Measurable h →
      Measurable (branchGraph f g h) := fun f g h hf hg hh => hf.prodMk (hg.prodMk hh)
  have hm1 : Measurable tripleFst := measurable_fst
  have hm2 : Measurable tripleSnd := measurable_fst.comp measurable_snd
  have hm3 : Measurable tripleThd := measurable_snd.comp measurable_snd
  have hid := (measurable_id : Measurable (id : E3 → E3))
  refine ⟨pb_isProb nu h1 h2 h3 h4, ?_, ?_, ?_⟩ <;>
  · ext s hs
    simp only [branchCoupling, branchMarginal, Measure.map_smul, Measure.map_add _ _ hm1,
      Measure.map_add _ _ hm2, Measure.map_add _ _ hm3,
      pb_map_graph nu hid h1 h2 _ hm1 id rfl, pb_map_graph nu h1 h2 hid _ hm1 H1 rfl,
      pb_map_graph nu h2 hid h1 _ hm1 H2 rfl, pb_map_graph nu hid h3 h4 _ hm1 id rfl,
      pb_map_graph nu h3 h4 hid _ hm1 H3 rfl, pb_map_graph nu h4 hid h3 _ hm1 H4 rfl,
      pb_map_graph nu hid h1 h2 _ hm2 H1 rfl, pb_map_graph nu h1 h2 hid _ hm2 H2 rfl,
      pb_map_graph nu h2 hid h1 _ hm2 id rfl, pb_map_graph nu hid h3 h4 _ hm2 H3 rfl,
      pb_map_graph nu h3 h4 hid _ hm2 H4 rfl, pb_map_graph nu h4 hid h3 _ hm2 id rfl,
      pb_map_graph nu hid h1 h2 _ hm3 H2 rfl, pb_map_graph nu h1 h2 hid _ hm3 id rfl,
      pb_map_graph nu h2 hid h1 _ hm3 H1 rfl, pb_map_graph nu hid h3 h4 _ hm3 H4 rfl,
      pb_map_graph nu h3 h4 hid _ hm3 id rfl, pb_map_graph nu h4 hid h3 _ hm3 H3 rfl,
      Measure.map_id, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
    rw [pb_third]
    ring

theorem pb_cost_cycle (x y z : E3) : coulombCost (y, (z, x)) = coulombCost (x, (y, z)) := by
  simp only [coulombCost, tripleFst, tripleSnd, tripleThd, invDistance]
  rw [norm_sub_rev z x, norm_sub_rev y x]
  ring

theorem pb_cost_meas : Measurable coulombCost := by
  unfold coulombCost invDistance tripleFst tripleSnd tripleThd
  fun_prop

theorem pb_opt {μ : Measure E3} {π0 : Measure Triple} (h0 : IsThreeCoupling μ π0)
    {U : Set E3} (hU : MeasurableSet U) (hmuU : ∀ᵐ x ∂μ, x ∈ U)
    {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂μ) ≠ ⊤)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      triplePotential p t ≤ coulombCost t + C)
    (hcontact : ∀ᵐ t ∂π0, triplePotential p t = coulombCost t + C) :
    (∫⁻ t, coulombCost t ∂π0) = kantorovichValue μ ∧ (∫⁻ t, coulombCost t ∂π0) < ⊤ := by
  have hm1 : Measurable tripleFst := measurable_fst
  have hm2 : Measurable tripleSnd := measurable_fst.comp measurable_snd
  have hm3 : Measurable tripleThd := measurable_snd.comp measurable_snd
  have hval : (∫⁻ t, coulombCost t ∂π0) + C = (∫⁻ x, p x ∂μ) + (∫⁻ x, p x ∂μ) + (∫⁻ x, p x ∂μ) := by
    have := h0.1
    rw [← DualCertificate.lintegral_add_offset, ← DualCertificate.lintegral_potentialSum h0 hp]
    exact (lintegral_congr_ae hcontact).symm
  have hlow : ∀ pi, IsThreeCoupling μ pi → (∫⁻ t, coulombCost t ∂π0) ≤ ∫⁻ t, coulombCost t ∂pi := by
    intro pi hpi
    have := hpi.1
    have a1 : ∀ᵐ t ∂pi, tripleFst t ∈ U := by
      exact (ae_map_iff hm1.aemeasurable hU).mp (by rw [hpi.2.1]; exact hmuU)
    have a2 : ∀ᵐ t ∂pi, tripleSnd t ∈ U := by
      exact (ae_map_iff hm2.aemeasurable hU).mp (by rw [hpi.2.2.1]; exact hmuU)
    have a3 : ∀ᵐ t ∂pi, tripleThd t ∈ U := by
      exact (ae_map_iff hm3.aemeasurable hU).mp (by rw [hpi.2.2.2]; exact hmuU)
    have hle : (∫⁻ t, coulombCost t ∂π0) + C ≤ (∫⁻ t, coulombCost t ∂pi) + C := by
      rw [hval, ← DualCertificate.lintegral_potentialSum hpi hp,
        ← DualCertificate.lintegral_add_offset]
      apply lintegral_mono_ae
      filter_upwards [a1, a2, a3] with t t1 t2 t3
      exact hbound t t1 t2 t3
    exact (ENNReal.add_le_add_iff_right hC).mp hle
  refine ⟨le_antisymm (le_iInf fun pi => le_iInf fun hpi => hlow pi hpi)
    (iInf_le_of_le π0 (iInf_le_of_le h0 le_rfl)), ?_⟩
  have : (∫⁻ t, coulombCost t ∂π0) + C < ⊤ := by
    rw [hval]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hpfinite.lt_top, hpfinite.lt_top⟩, hpfinite.lt_top⟩
  exact lt_of_le_of_lt le_self_add this

theorem pb_ae_marg (nu : Measure E3) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) {B U : Set E3}
    (hU : MeasurableSet U) (hfull : ∀ᵐ x ∂nu, x ∈ B)
    (hBU : B ⊆ U) (hHU : ∀ i, H i '' B ⊆ U) :
    ∀ᵐ x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3), x ∈ U := by
  rw [ae_iff]
  have hc : MeasurableSet {x : E3 | ¬ x ∈ U} := hU.compl
  have key : ∀ i, Measure.map (H i) nu {x : E3 | ¬ x ∈ U} = 0 := by
    intro i
    rw [Measure.map_apply (hH i) hc]
    apply ae_iff.mp
    filter_upwards [hfull] with x hx
    exact hHU i ⟨x, hx, rfl⟩
  have h0 : nu {x : E3 | ¬ x ∈ U} = 0 := by
    apply ae_iff.mp
    filter_upwards [hfull] with x hx
    exact hBU hx
  simp only [branchMarginal, Measure.smul_apply, Measure.add_apply, smul_eq_mul, key, h0]
  simp
theorem pb_map_image_eq {α : Type*} [MeasurableSpace α]
    (ν : Measure α) {B S : Set α} {H : α → α}
    (hν : ∀ᵐ x ∂ν, x ∈ B) (hH : Measurable H)
    (hInj : Set.InjOn H B) (hSB : S ⊆ B)
    (hImage : MeasurableSet (H '' S)) :
    (Measure.map H ν) (H '' S) = ν S := by
  rw [Measure.map_apply hH hImage]
  apply measure_congr
  filter_upwards [hν] with x hx
  apply propext
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := hInj (hSB hy) hx hxy
    show x ∈ S
    exact this ▸ hy
  · intro h
    exact ⟨x, h, rfl⟩

theorem pb_split_image {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (ν : Measure α) (a : ℝ≥0∞) (b : ι → ℝ≥0∞) (H : ι → α → α)
    {B S : Set α} (hν : ∀ᵐ x ∂ν, x ∈ B)
    (hH : ∀ i, Measurable (H i)) (hInj : ∀ i, Set.InjOn (H i) B)
    (hSB : S ⊆ B) (hImage : ∀ i, MeasurableSet (H i '' S))
    (hCentral : ∀ i, Disjoint B (H i '' B))
    (hPair : Pairwise fun i j => Disjoint (H i '' B) (H j '' B)) (j : ι) :
    Splitting.splitMeasure ν a b H (H j '' S) = b j * ν S := by
  classical
  have h0 : ν (H j '' S) = 0 := by
    apply measure_mono_null_ae (t := Bᶜ)
    · filter_upwards with x hx
      exact Set.disjoint_right.mp (hCentral j) (Set.image_mono hSB hx)
    · exact ae_iff.mp hν
  have hi : ∀ i, i ≠ j → Measure.map (H i) ν (H j '' S) = 0 := by
    intro i hij
    rw [Measure.map_apply (hH i) (hImage j)]
    apply measure_mono_null_ae (t := Bᶜ)
    · filter_upwards with x hmem hx
      exact Set.disjoint_left.mp (hPair hij) ⟨x, hx, rfl⟩ (Set.image_mono hSB hmem)
    · exact ae_iff.mp hν
  simp only [Splitting.splitMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul, h0, mul_zero,
    zero_add, Measure.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [hi i hij, mul_zero]) (by simp),
    pb_map_image_eq ν hν (hH j) (hInj j) hSB (hImage j)]

theorem pb_compress {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {μ ν : Measure α} [IsFiniteMeasure ν]
    {T : α → α} {S A : ι → Set α} {c d : ℝ≥0∞}
    (hν : ν Set.univ ≠ 0)
    (hA : ∀ i, MeasurableSet (A i))
    (hsub : ∀ i, S i ⊆ T ⁻¹' A i)
    (hsource : ∀ i, μ (S i) = c * ν (S i))
    (htarget : ∀ i, μ (A i) = d * ν (S i))
    (hdc : d < c)
    (hcover : ∀ᵐ x ∂ν, ∃ i, x ∈ S i) :
    ¬ (Measurable T ∧ Measure.map T μ = μ) := by
  rintro ⟨hT, hmap⟩
  have hzero : ∀ i, ν (S i) = 0 := by
    intro i
    by_contra h0
    have hle : c * ν (S i) ≤ d * ν (S i) := by
      rw [← hsource, ← htarget]
      calc μ (S i) ≤ μ (T ⁻¹' A i) := measure_mono (hsub i)
        _ = Measure.map T μ (A i) := (Measure.map_apply hT (hA i)).symm
        _ = μ (A i) := by rw [hmap]
    have htop : ν (S i) ≠ ⊤ := measure_ne_top ν _
    have hlt : d * ν (S i) < c * ν (S i) := ENNReal.mul_lt_mul_left h0 htop hdc
    exact absurd hle (not_le.mpr hlt)
  have hae : ∀ᵐ x ∂ν, ∀ i, x ∉ S i := by
    rw [ae_all_iff]
    intro i
    exact measure_eq_zero_iff_ae_notMem.mp (hzero i)
  have hF : ∀ᵐ x ∂ν, False := by
    filter_upwards [hcover, hae] with x ⟨i, hi⟩ h
    exact h i hi
  apply hν
  simpa using ae_iff.mp hF

theorem pb_no_pres {α ι : Type*} [MeasurableSpace α] [Countable ι] [MeasurableEq α]
    {μ ν : Measure α} [IsFiniteMeasure ν] {B : Set α}
    {H : ι → α → α} {c d : ℝ≥0∞}
    (hν : ν Set.univ ≠ 0) (hB : MeasurableSet B)
    (hfull : ∀ᵐ x ∂ν, x ∈ B)
    (hH : ∀ i, Measurable (H i))
    (himage : ∀ i S, MeasurableSet S → S ⊆ B →
      MeasurableSet (H i '' S))
    (hsource : ∀ S, MeasurableSet S → S ⊆ B → μ S = c * ν S)
    (htarget : ∀ i S, MeasurableSet S → S ⊆ B →
      μ (H i '' S) = d * ν S)
    (hdc : d < c) :
    ¬ ∃ T : α → α, Measurable T ∧ Measure.map T μ = μ ∧
      (∀ᵐ x ∂ν, ∃ i, T x = H i x) := by
  rintro ⟨T, hT, hmap, hsel⟩
  let S : ι → Set α := fun i => B ∩ {x | T x = H i x}
  have hSm : ∀ i, MeasurableSet (S i) := fun i => hB.inter (measurableSet_eq_fun hT (hH i))
  have hSB : ∀ i, S i ⊆ B := fun i => Set.inter_subset_left
  refine pb_compress (μ := μ) (ν := ν) (T := T) (S := S) (A := fun i => H i '' S i) hν
    (fun i => himage i (S i) (hSm i) (hSB i)) ?_ (fun i => hsource (S i) (hSm i) (hSB i))
    (fun i => htarget i (S i) (hSm i) (hSB i)) hdc ?_ ⟨hT, hmap⟩
  · intro i x hx
    exact ⟨x, hx, hx.2.symm⟩
  · filter_upwards [hfull, hsel] with x hx ⟨i, hi⟩
    exact ⟨i, hx, hi⟩

theorem pb_graph_coupling {μ : Measure E3} [IsProbabilityMeasure μ] {T2 T3 : E3 → E3}
    (h2 : Preserves μ T2) (h3 : Preserves μ T3) :
    IsThreeCoupling μ (Measure.map (graphMap T2 T3) μ) := by
  have hg : Measurable (graphMap T2 T3) := measurable_id.prodMk (h2.1.prodMk h3.1)
  refine ⟨Measure.isProbabilityMeasure_map hg.aemeasurable, ?_, ?_, ?_⟩
  · rw [Measure.map_map (show Measurable tripleFst from measurable_fst) hg]
    exact Measure.map_id
  · rw [Measure.map_map (show Measurable tripleSnd from measurable_fst.comp measurable_snd) hg]
    exact h2.2
  · rw [Measure.map_map (show Measurable tripleThd from measurable_snd.comp measurable_snd) hg]
    exact h3.2

theorem pb_main
    (rho : E3 → ℝ) (hrho : IsSmoothCompactProbabilityDensity rho)
    (nu : Measure E3) [IsProbabilityMeasure nu]
    (H : Fin 4 → E3 → E3) (hH : ∀ i, Measurable (H i))
    (hdensity : densityMeasure rho = branchMarginal nu (H 0) (H 1) (H 2) (H 3))
    {B U : Set E3} (hB : MeasurableSet B) (hU : MeasurableSet U)
    (hfull : ∀ᵐ x ∂nu, x ∈ B) (hBU : B ⊆ U)
    (hHU : ∀ i, H i '' B ⊆ U)
    (hInj : ∀ i, Set.InjOn (H i) B)
    (himage : ∀ i S, MeasurableSet S → S ⊆ B → MeasurableSet (H i '' S))
    (hCentral : ∀ i, Disjoint B (H i '' B))
    (hPair : Pairwise fun i j => Disjoint (H i '' B) (H j '' B))
    {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ≠ ⊤)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      triplePotential p t ≤ coulombCost t + C)
    (hcontact01 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 0 x, H 1 x)) = coulombCost (x, (H 0 x, H 1 x)) + C)
    (hcontact23 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 2 x, H 3 x)) = coulombCost (x, (H 2 x, H 3 x)) + C)
    (hselect : ∀ x y z : E3, x ∈ B → y ∈ U → z ∈ U →
      triplePotential p (x, (y, z)) = coulombCost (x, (y, z)) + C →
      ∃ i, y = H i x) :
    HasCoulombCounterexample rho := by
  have hmuU := pb_ae_marg nu hH hU hfull hBU hHU
  have h0 := pb_coupling nu (hH 0) (hH 1) (hH 2) (hH 3)
  have hPm : MeasurableSet {t : Triple | triplePotential p t = coulombCost t + C} := by
    apply measurableSet_eq_fun
    · unfold triplePotential tripleFst tripleSnd tripleThd; fun_prop
    · exact pb_cost_meas.add measurable_const
  have hcont : ∀ᵐ t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3),
      triplePotential p t = coulombCost t + C := by
    refine pb_ae_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3) hPm ?_ hcontact01 hcontact23
    intro x y z h
    simp only [triplePotential, tripleFst, tripleSnd, tripleThd] at h ⊢
    rw [pb_cost_cycle, ← h]
    ring
  obtain ⟨hopt, hfin⟩ := pb_opt h0 hU hmuU hp hpfinite hC hbound hcont
  have hm1 : Measurable tripleFst := measurable_fst
  have hm2 : Measurable tripleSnd := measurable_fst.comp measurable_snd
  have hm3 : Measurable tripleThd := measurable_snd.comp measurable_snd
  set μ := branchMarginal nu (H 0) (H 1) (H 2) (H 3) with hμ
  have hprob : IsProbabilityMeasure μ := by
    constructor
    rw [← h0.2.1, Measure.map_apply hm1 MeasurableSet.univ]
    exact h0.1.measure_univ
  unfold HasCoulombCounterexample
  rw [hdensity]
  refine ⟨hrho, hprob, hopt ▸ hfin, ⟨_, h0, hopt⟩, ?_⟩
  intro T2 T3 hT2 hT3
  by_contra hcon
  push Not at hcon
  have hgc := pb_graph_coupling hT2 hT3
  have hg : Measurable (graphMap T2 T3) := measurable_id.prodMk (hT2.1.prodMk hT3.1)
  set π := Measure.map (graphMap T2 T3) μ with hπ
  have hval : (∫⁻ t, coulombCost t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3)) + C =
      (∫⁻ x, p x ∂μ) + (∫⁻ x, p x ∂μ) + (∫⁻ x, p x ∂μ) := by
    have := h0.1
    rw [← DualCertificate.lintegral_add_offset, ← DualCertificate.lintegral_potentialSum h0 hp]
    exact (lintegral_congr_ae hcont).symm
  have hπval : (∫⁻ t, triplePotential p t ∂π) =
      (∫⁻ x, p x ∂μ) + (∫⁻ x, p x ∂μ) + (∫⁻ x, p x ∂μ) :=
    DualCertificate.lintegral_potentialSum hgc hp
  have a1 : ∀ᵐ t ∂π, tripleFst t ∈ U :=
    (ae_map_iff hm1.aemeasurable hU).mp (by rw [hgc.2.1]; exact hmuU)
  have a2 : ∀ᵐ t ∂π, tripleSnd t ∈ U :=
    (ae_map_iff hm2.aemeasurable hU).mp (by rw [hgc.2.2.1]; exact hmuU)
  have a3 : ∀ᵐ t ∂π, tripleThd t ∈ U :=
    (ae_map_iff hm3.aemeasurable hU).mp (by rw [hgc.2.2.2]; exact hmuU)
  have hle : ∀ᵐ t ∂π, triplePotential p t ≤ coulombCost t + C := by
    filter_upwards [a1, a2, a3] with t t1 t2 t3
    exact hbound t t1 t2 t3
  have hgcost : graphCost μ T2 T3 = ∫⁻ t, coulombCost t ∂π := by
    rw [hπ, lintegral_map pb_cost_meas hg]
    rfl
  have heq : (fun t => triplePotential p t) =ᵐ[π] fun t => coulombCost t + C := by
    apply ae_eq_of_ae_le_of_lintegral_le hle
    · rw [hπval, ← hval]
      exact ENNReal.add_ne_top.mpr ⟨hfin.ne, hC⟩
    · exact (pb_cost_meas.add measurable_const).aemeasurable
    · have := hgc.1
      rw [DualCertificate.lintegral_add_offset, hπval, ← hval, ← hgcost]
      gcongr
      rw [hopt]; exact hcon
  have hall : ∀ᵐ t ∂π, tripleSnd t ∈ U ∧ tripleThd t ∈ U ∧
      triplePotential p t = coulombCost t + C := by
    filter_upwards [a2, a3, heq] with t t2 t3 te
    exact ⟨t2, t3, te⟩
  have hallμ := ae_of_ae_map hg.aemeasurable hall
  have hac : nu ≪ μ := by
    intro s hs
    rw [hμ] at hs
    simp only [branchMarginal, Measure.add_apply, Measure.smul_apply, smul_eq_mul] at hs
    have := (add_eq_zero.mp hs).1
    rcases mul_eq_zero.mp this with h | h
    · norm_num at h
    · exact h
  have hsel : ∀ᵐ x ∂nu, ∃ i, T2 x = H i x := by
    filter_upwards [hac.ae_le hallμ, hfull] with x ⟨h2, h3, he⟩ hx
    exact hselect x (T2 x) (T3 x) hx h2 h3 he
  have hsplit : μ = Splitting.splitMeasure nu (1 / 3) (fun _ => 1 / 6) H := by
    rw [hμ]
    simp only [branchMarginal, Splitting.splitMeasure, Fin.sum_univ_four, smul_add]
  have hsource : ∀ S, MeasurableSet S → S ⊆ B → μ S = (1 / 3) * nu S := by
    intro S hS hSB
    rw [hsplit]
    simp only [Splitting.splitMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.coe_finsetSum, Finset.sum_apply]
    have hz : ∀ i, Measure.map (H i) nu S = 0 := by
      intro i
      rw [Measure.map_apply (hH i) hS]
      apply measure_mono_null_ae (t := Bᶜ)
      · filter_upwards with x hmem hx
        exact Set.disjoint_left.mp (hCentral i) (hSB hmem) ⟨x, hx, rfl⟩
      · exact ae_iff.mp hfull
    simp [hz]
  have htarget : ∀ i S, MeasurableSet S → S ⊆ B → μ (H i '' S) = (1 / 6) * nu S := by
    intro i S hS hSB
    rw [hsplit]
    exact pb_split_image nu (1 / 3) (fun _ => 1 / 6) H hfull hH hInj hSB
      (fun j => himage j S hS hSB) hCentral hPair i
  apply pb_no_pres (μ := μ) (ν := nu) (H := H) (by simp) hB hfull hH himage hsource htarget
    (by rw [one_div, one_div]; exact ENNReal.inv_lt_inv.mpr (by norm_num))
  exact ⟨T2, hT2.1, hT2.2, hsel⟩

theorem solution
    (rho : E3 → ℝ) (hrho : IsSmoothCompactProbabilityDensity rho)
    (nu : Measure E3) [IsProbabilityMeasure nu]
    (H : Fin 4 → E3 → E3) (hH : ∀ i, Measurable (H i))
    (hdensity : densityMeasure rho = branchMarginal nu (H 0) (H 1) (H 2) (H 3))
    {B U : Set E3} (hB : MeasurableSet B) (hU : MeasurableSet U)
    (hfull : ∀ᵐ x ∂nu, x ∈ B) (hBU : B ⊆ U)
    (hHU : ∀ i, H i '' B ⊆ U)
    (hInj : ∀ i, Set.InjOn (H i) B)
    (himage : ∀ i S, MeasurableSet S → S ⊆ B → MeasurableSet (H i '' S))
    (hCentral : ∀ i, Disjoint B (H i '' B))
    (hPair : Pairwise fun i j => Disjoint (H i '' B) (H j '' B))
    {p : E3 → ℝ≥0∞} (hp : Measurable p)
    (hpfinite : (∫⁻ x, p x ∂branchMarginal nu (H 0) (H 1) (H 2) (H 3)) ≠ ⊤)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hbound : ∀ t, tripleFst t ∈ U → tripleSnd t ∈ U → tripleThd t ∈ U →
      triplePotential p t ≤ coulombCost t + C)
    (hcontact01 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 0 x, H 1 x)) = coulombCost (x, (H 0 x, H 1 x)) + C)
    (hcontact23 : ∀ᵐ x ∂nu,
      triplePotential p (x, (H 2 x, H 3 x)) = coulombCost (x, (H 2 x, H 3 x)) + C)
    (hselect : ∀ x y z : E3, x ∈ B → y ∈ U → z ∈ U →
      triplePotential p (x, (y, z)) = coulombCost (x, (y, z)) + C →
      ∃ i, y = H i x) :
    HasCoulombCounterexample rho := by
  exact pb_main rho hrho nu H hH hdensity hB hU hfull hBU hHU hInj himage hCentral hPair hp hpfinite hC
    hbound hcontact01 hcontact23 hselect

