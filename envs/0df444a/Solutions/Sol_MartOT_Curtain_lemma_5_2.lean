-- Prove2me | solution 1 for MartOT.Curtain.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:07:19.063226+00:00
-- url     : https://prove2.me/submissions/08404cc2-ef72-403d-8138-6dfac81c4314

import Mathlib
import Definitions.Def_MartOT_Curtain_gUV

set_option autoImplicit false
open MeasureTheory Filter Topology

namespace MCL52
open MartOT.Curtain

lemma gUV_meas (a b : ℝ) : Measurable (gUV a b) := by
  unfold gUV
  exact Measurable.ite measurableSet_Icc (measurable_const.sub measurable_id) measurable_const

lemma gUV_bdd (a b x : ℝ) : |gUV a b x| ≤ |b - a| := by
  unfold gUV
  split_ifs with h
  · rw [abs_of_nonneg (by linarith [h.2])]
    rw [abs_of_nonneg (by linarith [h.1, h.2])]
    linarith [h.1]
  · simp

lemma gUV_integrable (ν : Measure ℝ) [IsFiniteMeasure ν] (a b : ℝ) :
    Integrable (gUV a b) ν :=
  Integrable.of_bound (gUV_meas a b).aestronglyMeasurable |b - a|
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact gUV_bdd a b x)

lemma gUV_integral (ν : Measure ℝ) [IsFiniteMeasure ν] (a b : ℝ) (hab : a ≤ b) :
    ∫ x, gUV a b x ∂ν = ∫ t in a..b, (ν (Set.Icc a t)).toReal := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  set F : ℝ → ℝ → ℝ := fun t x => (Set.Icc a t).indicator (fun _ => (1 : ℝ)) x with hF
  have hFm : Measurable (Function.uncurry F) := by
    have : Function.uncurry F = {p : ℝ × ℝ | a ≤ p.2 ∧ p.2 ≤ p.1}.indicator (fun _ => (1 : ℝ)) := by
      ext ⟨t, x⟩; simp [hF, Set.indicator, Set.mem_Icc]
    rw [this]
    exact measurable_const.indicator ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst))
  have hFi : Integrable (Function.uncurry F) ((volume.restrict (Set.Icc a b)).prod ν) := by
    refine Integrable.of_bound hFm.aestronglyMeasurable 1 (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hF, Set.indicator]
    split_ifs <;> simp
  have hswap := integral_integral_swap hFi
  have e1 : ∀ t, ∫ x, F t x ∂ν = (ν (Set.Icc a t)).toReal := by
    intro t; simp only [hF]; rw [integral_indicator_const _ measurableSet_Icc]; simp [Measure.real]
  have e2 : ∀ x, ∫ t, F t x ∂(volume.restrict (Set.Icc a b)) = gUV a b x := by
    intro x
    by_cases hax : a ≤ x
    · have : (fun t => F t x) = (Set.Ici x).indicator (fun _ => (1 : ℝ)) := by
        ext t; simp [hF, Set.indicator, hax, Set.mem_Icc]
      rw [this, integral_indicator_const _ measurableSet_Ici]
      simp only [Measure.real, Measure.restrict_apply measurableSet_Ici, smul_eq_mul, mul_one]
      have hs : Set.Ici x ∩ Set.Icc a b = Set.Icc x b := by
        ext t; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨h1, hax.trans h1, h3⟩
      rw [hs, Real.volume_Icc]
      unfold gUV
      split_ifs with h
      · rw [ENNReal.toReal_ofReal (by linarith [h.2])]
      · have : b - x ≤ 0 := by
          by_contra hc; exact h ⟨hax, by linarith⟩
        rw [ENNReal.ofReal_of_nonpos this]; simp
    · have : (fun t => F t x) = fun _ => 0 := by
        ext t; simp [hF, Set.indicator, hax, Set.mem_Icc]
      rw [this]
      have : gUV a b x = 0 := by unfold gUV; rw [if_neg (fun h => hax h.1)]
      rw [this]; simp
  simp only [e1] at hswap
  rw [hswap]
  exact integral_congr_ae (Eventually.of_forall fun x => (e2 x).symm)

lemma lb_integral (f : ℝ → ℝ) (a m b K κ : ℝ) (ham : a ≤ m) (hmb : m ≤ b)
    (h1 : IntervalIntegrable f volume a m) (h2 : IntervalIntegrable f volume m b)
    (hK : ∀ t ∈ Set.Icc a m, -K ≤ f t) (hκ : ∀ t ∈ Set.Icc m b, κ ≤ f t) :
    -K * (m - a) + κ * (b - m) ≤ ∫ t in a..b, f t := by
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have i1 : -K * (m - a) ≤ ∫ t in a..m, f t := by
    have := intervalIntegral.integral_mono_on ham (intervalIntegrable_const (c := -K)) h1 hK
    simpa [mul_comm] using this
  have i2 : κ * (b - m) ≤ ∫ t in m..b, f t := by
    have := intervalIntegral.integral_mono_on hmb (intervalIntegrable_const (c := κ)) h2 hκ
    simpa [mul_comm] using this
  linarith

end MCL52
namespace MCL52

lemma toReal_split {ν : Measure ℝ} [IsFiniteMeasure ν] {s u w : Set ℝ} (hw : w = s ∪ u)
    (hd : Disjoint s u) (hu : MeasurableSet u) :
    (ν w).toReal = (ν s).toReal + (ν u).toReal := by
  rw [hw, measure_union hd hu, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]

lemma cdf_Iic_split (ν : Measure ℝ) [IsFiniteMeasure ν] {c t : ℝ} (h : c ≤ t) :
    (ν (Set.Iic t)).toReal = (ν (Set.Iic c)).toReal + (ν (Set.Ioc c t)).toReal := by
  refine toReal_split (by ext x; simp only [Set.mem_Iic, Set.mem_union, Set.mem_Ioc]
                          constructor
                          · intro hx; by_cases hxc : x ≤ c
                            · exact Or.inl hxc
                            · exact Or.inr ⟨not_le.mp hxc, hx⟩
                          · rintro (hx | hx)
                            · exact hx.trans h
                            · exact hx.2) ?_ measurableSet_Ioc
  rw [Set.disjoint_left]
  intro x hx hx'
  exact absurd hx (not_le.mpr hx'.1)

lemma cdf_Iio_split (ν : Measure ℝ) [IsFiniteMeasure ν] {c a : ℝ} (h : c < a) :
    (ν (Set.Iio a)).toReal = (ν (Set.Iic c)).toReal + (ν (Set.Ioo c a)).toReal := by
  refine toReal_split (by ext x; simp only [Set.mem_Iio, Set.mem_union, Set.mem_Iic, Set.mem_Ioo]
                          constructor
                          · intro hx; by_cases hxc : x ≤ c
                            · exact Or.inl hxc
                            · exact Or.inr ⟨not_le.mp hxc, hx⟩
                          · rintro (hx | hx)
                            · exact lt_of_le_of_lt hx h
                            · exact hx.2) ?_ measurableSet_Ioo
  rw [Set.disjoint_left]
  intro x hx hx'
  exact absurd hx (not_le.mpr hx'.1)

lemma cdf_Iic_Iio (ν : Measure ℝ) [IsFiniteMeasure ν] {a t : ℝ} (h : a ≤ t) :
    (ν (Set.Iic t)).toReal = (ν (Set.Iio a)).toReal + (ν (Set.Icc a t)).toReal := by
  refine toReal_split (by ext x; simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_Icc]
                          constructor
                          · intro hx; by_cases hxa : x < a
                            · exact Or.inl hxa
                            · exact Or.inr ⟨not_lt.mp hxa, hx⟩
                          · rintro (hx | hx)
                            · exact (hx.trans_le h).le
                            · exact hx.2) ?_ measurableSet_Icc
  rw [Set.disjoint_left]
  intro x hx hx'
  exact absurd hx (not_lt.mpr hx'.1)

lemma cdf_Iic_Ioi (ν : Measure ℝ) [IsFiniteMeasure ν] (c : ℝ) :
    (ν (Set.Iic c)).toReal + (ν (Set.Ioi c)).toReal = (ν Set.univ).toReal := by
  have hw : (Set.univ : Set ℝ) = Set.Iic c ∪ Set.Ioi c := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Ioi, true_iff]
    exact le_or_gt x c
  have hd : Disjoint (Set.Iic c) (Set.Ioi c) := by
    rw [Set.disjoint_left]; intro x hx hx'; exact absurd (show x ≤ c from hx) (not_le.mpr (show c < x from hx'))
  exact (toReal_split hw hd measurableSet_Ioi).symm

lemma small_Ioc (ν : Measure ℝ) [IsFiniteMeasure ν] (T ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ (ν (Set.Ioc T (T + h))).toReal < ε := by
  have hlim : Tendsto (fun n : ℕ => ν (Set.Ioc T (T + 1 / ((n : ℝ) + 1)))) atTop (𝓝 (ν ∅)) := by
    have hset : (⋂ n : ℕ, Set.Ioc T (T + 1 / ((n : ℝ) + 1))) = ∅ := by
      ext x
      simp only [Set.mem_iInter, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false, not_forall]
      by_cases hx : T < x
      · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
        exact ⟨n, fun h => by linarith [h.2]⟩
      · exact ⟨0, fun h => hx h.1⟩
    rw [← hset]
    refine tendsto_measure_iInter_atTop (fun n => measurableSet_Ioc.nullMeasurableSet) ?_
      ⟨0, measure_ne_top _ _⟩
    intro m n hmn
    refine Set.Ioc_subset_Ioc_right ?_
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    linarith
  rw [measure_empty] at hlim
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ENNReal) < ENNReal.ofReal ε by simpa using hε))
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_⟩
  exact ENNReal.toReal_lt_of_lt_ofReal hn

lemma tail_Iic (ν : Measure ℝ) [IsFiniteMeasure ν] (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ s ≤ R, (ν (Set.Iic s)).toReal < ε := by
  have hlim : Tendsto (fun n : ℕ => ν (Set.Iic (-(n : ℝ)))) atTop (𝓝 (ν ∅)) := by
    have hset : (⋂ n : ℕ, Set.Iic (-(n : ℝ))) = ∅ := by
      ext x
      simp only [Set.mem_iInter, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_forall]
      obtain ⟨n, hn⟩ := exists_nat_gt (-x)
      exact ⟨n, fun h => by linarith⟩
    rw [← hset]
    refine tendsto_measure_iInter_atTop (fun n => measurableSet_Iic.nullMeasurableSet) ?_
      ⟨0, measure_ne_top _ _⟩
    intro m n hmn
    refine Set.Iic_subset_Iic.mpr ?_
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  rw [measure_empty] at hlim
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ENNReal) < ENNReal.ofReal ε by simpa using hε))
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨-(n : ℝ), fun s hs => ?_⟩
  exact ENNReal.toReal_lt_of_lt_ofReal (lt_of_le_of_lt (measure_mono (Set.Iic_subset_Iic.mpr hs)) hn)

lemma tail_Ioi (ν : Measure ℝ) [IsFiniteMeasure ν] (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ s ≥ R, (ν (Set.Ioi s)).toReal < ε := by
  have hlim : Tendsto (fun n : ℕ => ν (Set.Ioi ((n : ℝ)))) atTop (𝓝 (ν ∅)) := by
    have hset : (⋂ n : ℕ, Set.Ioi ((n : ℝ))) = ∅ := by
      ext x
      simp only [Set.mem_iInter, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false, not_forall]
      obtain ⟨n, hn⟩ := exists_nat_ge x
      exact ⟨n, fun h => by linarith⟩
    rw [← hset]
    refine tendsto_measure_iInter_atTop (fun n => measurableSet_Ioi.nullMeasurableSet) ?_
      ⟨0, measure_ne_top _ _⟩
    intro m n hmn
    refine Set.Ioi_subset_Ioi ?_
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  rw [measure_empty] at hlim
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ENNReal) < ENNReal.ofReal ε by simpa using hε))
  obtain ⟨n, hn⟩ := hev.exists
  refine ⟨(n : ℝ), fun s hs => ?_⟩
  exact ENNReal.toReal_lt_of_lt_ofReal (lt_of_le_of_lt (measure_mono (Set.Ioi_subset_Ioi hs)) hn)

lemma gap_null (ν : Measure ℝ) {s : Set ℝ} (h : s ∩ ν.support = ∅) : ν s = 0 := by
  refine measure_mono_null ?_ (Measure.measure_compl_support (μ := ν))
  intro x hx hx'
  have : x ∈ s ∩ ν.support := ⟨hx, hx'⟩
  rw [h] at this; exact this

end MCL52
namespace MCL52
open MartOT.Curtain

noncomputable def Phi (σp σm : Measure ℝ) (t : ℝ) : ℝ :=
  (σp (Set.Iic t)).toReal - (σm (Set.Iic t)).toReal
noncomputable def Phi' (σp σm : Measure ℝ) (a : ℝ) : ℝ :=
  (σp (Set.Iio a)).toReal - (σm (Set.Iio a)).toReal
noncomputable def fa (σp σm : Measure ℝ) (a t : ℝ) : ℝ :=
  (σp (Set.Icc a t)).toReal - (σm (Set.Icc a t)).toReal

variable (σp σm : Measure ℝ) [IsFiniteMeasure σp] [IsFiniteMeasure σm]

lemma mono_cdf (ν : Measure ℝ) [IsFiniteMeasure ν] (a : ℝ) :
    Monotone fun t => (ν (Set.Icc a t)).toReal := by
  intro s t hst
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Icc_subset_Icc_right hst))

lemma fa_ii (a x y : ℝ) : IntervalIntegrable (fa σp σm a) volume x y :=
  ((mono_cdf σp a).intervalIntegrable (a := x) (b := y)).sub
    ((mono_cdf σm a).intervalIntegrable (a := x) (b := y))

lemma U_eq (a b : ℝ) (hab : a ≤ b) :
    (∫ x, gUV a b x ∂σp) - ∫ x, gUV a b x ∂σm = ∫ t in a..b, fa σp σm a t := by
  rw [gUV_integral σp a b hab, gUV_integral σm a b hab]
  unfold fa
  rw [intervalIntegral.integral_sub
    ((mono_cdf σp a).intervalIntegrable (a := a) (b := b))
    ((mono_cdf σm a).intervalIntegrable (a := a) (b := b))]

lemma fa_eq {a t : ℝ} (h : a ≤ t) : fa σp σm a t = Phi σp σm t - Phi' σp σm a := by
  unfold fa Phi Phi'
  rw [cdf_Iic_Iio σp h, cdf_Iic_Iio σm h]; ring

lemma Phi'_gap {c a : ℝ} (h : c < a) :
    Phi' σp σm a = Phi σp σm c + (σp (Set.Ioo c a)).toReal - (σm (Set.Ioo c a)).toReal := by
  unfold Phi Phi'
  rw [cdf_Iio_split σp h, cdf_Iio_split σm h]; ring

lemma Phi_split {L T : ℝ} (h : L ≤ T) :
    Phi σp σm T = Phi σp σm L + (σp (Set.Ioc L T)).toReal - (σm (Set.Ioc L T)).toReal := by
  unfold Phi
  rw [cdf_Iic_split σp h, cdf_Iic_split σm h]; ring

lemma Phi_Ioi (hmass : σp Set.univ = σm Set.univ) (c : ℝ) :
    Phi σp σm c = (σm (Set.Ioi c)).toReal - (σp (Set.Ioi c)).toReal := by
  unfold Phi
  have h1 := cdf_Iic_Ioi σp c
  have h2 := cdf_Iic_Ioi σm c
  rw [hmass] at h1
  linarith

lemma exists_support_point {c T : ℝ} (hcT : c < T) (hT : T ∈ σp.support) (ε : ℝ) (hε : 0 < ε) :
    ∃ a ∈ σp.support, c < a ∧ a ≤ T ∧ (σp (Set.Ioo c a)).toReal < ε := by
  obtain ⟨h, hh, hsm⟩ := small_Ioc σp c ε hε
  set h' := min h (T - c) with hh'
  have hh'pos : 0 < h' := lt_min hh (by linarith)
  by_cases hcase : ∃ x ∈ σp.support, x ∈ Set.Ioc c (c + h')
  · obtain ⟨x, hxs, hx1, hx2⟩ := hcase
    refine ⟨x, hxs, hx1, ?_, ?_⟩
    · have : h' ≤ T - c := min_le_right _ _
      linarith
    · refine lt_of_le_of_lt (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)) hsm
      intro y hy
      exact ⟨hy.1, by have : h' ≤ h := min_le_left _ _
                      linarith [hy.2]⟩
  · push_neg at hcase
    have hA : IsClosed (σp.support ∩ Set.Icc (c + h') T) :=
      Measure.isClosed_support.inter isClosed_Icc
    have hne : (σp.support ∩ Set.Icc (c + h') T).Nonempty :=
      ⟨T, hT, by have : h' ≤ T - c := min_le_right _ _
                 exact ⟨by linarith, le_rfl⟩⟩
    have hbdd : BddBelow (σp.support ∩ Set.Icc (c + h') T) := ⟨c + h', fun y hy => hy.2.1⟩
    have hmem := hA.csInf_mem hne hbdd
    set a := sInf (σp.support ∩ Set.Icc (c + h') T) with ha
    refine ⟨a, hmem.1, by linarith [hmem.2.1], hmem.2.2, ?_⟩
    have : σp (Set.Ioo c a) = 0 := by
      refine gap_null σp ?_
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨hy1, hy2⟩, hys⟩
      by_cases hyh : y ≤ c + h'
      · exact hcase y hys ⟨hy1, hyh⟩
      · have : y ∈ σp.support ∩ Set.Icc (c + h') T :=
          ⟨hys, (not_le.mp hyh).le, hy2.le.trans hmem.2.2⟩
        have := csInf_le hbdd this
        linarith
    rw [this]; simpa using hε

end MCL52
namespace MCL52
open MartOT.Curtain

variable (σp σm : Measure ℝ) [IsFiniteMeasure σp] [IsFiniteMeasure σm]

lemma core_pos
    (H : ∀ a ∈ σp.support, ∀ b, a < b →
      (∫ x, gUV a b x ∂σp) - ∫ x, gUV a b x ∂σm ≤ 0)
    (t0 : ℝ) (ht0 : 0 < Phi σp σm t0) : False := by
  set lam := Phi σp σm t0 with hlam
  obtain ⟨Rp, hRp⟩ := tail_Iic σp (lam / 2) (by linarith)
  have hΦle : ∀ s, Phi σp σm s ≤ (σp (Set.Iic s)).toReal := fun s => by
    unfold Phi; linarith [ENNReal.toReal_nonneg (a := σm (Set.Iic s))]
  set S : Set ℝ := {t | lam ≤ Phi σp σm t} with hS
  have ht0S : t0 ∈ S := le_of_eq hlam
  have hlower : ∀ s ∈ S, Rp ≤ s := by
    intro s hs
    by_contra hcon
    have h1 := hRp s (not_le.mp hcon).le
    have h2 := hΦle s
    have hs' : lam ≤ Phi σp σm s := hs
    linarith
  have hSbdd : BddBelow S := ⟨Rp, hlower⟩
  set T := sInf S with hT
  have hTRp : Rp ≤ T := le_csInf ⟨t0, ht0S⟩ hlower
  have hT1 : lam ≤ Phi σp σm T := by
    by_contra hlt
    have hlt' : Phi σp σm T < lam := not_le.mp hlt
    obtain ⟨h, hh, hsm⟩ := small_Ioc σp T (lam - Phi σp σm T) (by linarith)
    have hlb : T + h ≤ T := by
      calc T + h ≤ sInf S := by
            refine le_csInf ⟨t0, ht0S⟩ (fun s hs => ?_)
            by_contra hcon
            have hTs : T ≤ s := csInf_le hSbdd hs
            have hsh : s < T + h := not_le.mp hcon
            have e := Phi_split σp σm hTs
            have h1 : (σp (Set.Ioc T s)).toReal ≤ (σp (Set.Ioc T (T + h))).toReal :=
              ENNReal.toReal_mono (measure_ne_top _ _)
                (measure_mono (Set.Ioc_subset_Ioc_right hsh.le))
            have h2 := ENNReal.toReal_nonneg (a := σm (Set.Ioc T s))
            have hs' : lam ≤ Phi σp σm s := hs
            linarith
        _ = T := rfl
    linarith
  have hT2 : ∀ s < T, Phi σp σm s < lam := fun s hs =>
    not_le.mp (fun h => (notMem_of_lt_csInf hs hSbdd) h)
  have hTA : T ∈ σp.support := by
    have hpos : 0 < σp (Set.Iic T) := by
      by_contra hcon
      have h0 : σp (Set.Iic T) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hcon)
      have h1 := hT1
      unfold Phi at h1
      rw [h0] at h1
      simp only [ENNReal.toReal_zero, zero_sub] at h1
      linarith [ENNReal.toReal_nonneg (a := σm (Set.Iic T))]
    obtain ⟨x0, hx0⟩ := Measure.nonempty_inter_support_of_pos hpos
    set B := Set.Iic T ∩ σp.support with hB
    have hBcl : IsClosed B := isClosed_Iic.inter Measure.isClosed_support
    have hBbdd : BddAbove B := ⟨T, fun y hy => hy.1⟩
    have hL : sSup B ∈ B := hBcl.csSup_mem ⟨x0, hx0⟩ hBbdd
    have hLT : sSup B ≤ T := hL.1
    have hgap : σp (Set.Ioc (sSup B) T) = 0 := by
      refine gap_null σp ?_
      ext y
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨h1, h2⟩, hy⟩
      have : y ∈ B := ⟨h2, hy⟩
      have := le_csSup hBbdd this
      linarith
    have hPhiL : lam ≤ Phi σp σm (sSup B) := by
      have e := Phi_split σp σm hLT
      rw [hgap] at e
      simp only [ENNReal.toReal_zero, add_zero] at e
      linarith [ENNReal.toReal_nonneg (a := σm (Set.Ioc (sSup B) T))]
    have hLS : sSup B ∈ S := hPhiL
    have : T ≤ sSup B := csInf_le hSbdd hLS
    have hLeq : sSup B = T := le_antisymm hLT this
    rw [← hLeq]; exact hL.2
  set t1 := Rp - 1 with ht1
  have ht1T : t1 < T := by linarith
  have hPhit1 : Phi σp σm t1 < lam / 2 :=
    lt_of_le_of_lt (hΦle t1) (hRp t1 (by linarith))
  set I : Set ℝ := Phi σp σm '' Set.Icc t1 T with hI
  have hIne : I.Nonempty := ⟨_, t1, ⟨le_rfl, ht1T.le⟩, rfl⟩
  have hIbdd : BddBelow I := by
    refine ⟨-(σm Set.univ).toReal, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    unfold Phi
    have h1 : (σm (Set.Iic s)).toReal ≤ (σm Set.univ).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
    linarith [ENNReal.toReal_nonneg (a := σp (Set.Iic s))]
  set m := sInf I with hm
  have hm_le : ∀ s ∈ Set.Icc t1 T, m ≤ Phi σp σm s := fun s hs => csInf_le hIbdd ⟨s, hs, rfl⟩
  have hm_lt : m < lam / 2 := lt_of_le_of_lt (hm_le t1 ⟨le_rfl, ht1T.le⟩) hPhit1
  obtain ⟨h, hh, hsmh⟩ := small_Ioc σm T (lam / 4) (by linarith)
  have hΦr : ∀ s ∈ Set.Icc T (T + h), 3 * lam / 4 ≤ Phi σp σm s := by
    intro s hs
    have e := Phi_split σp σm hs.1
    have h1 : (σm (Set.Ioc T s)).toReal ≤ (σm (Set.Ioc T (T + h))).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ioc_subset_Ioc_right hs.2))
    have h2 := ENNReal.toReal_nonneg (a := σp (Set.Ioc T s))
    linarith
  have hTt : 0 < T - t1 + 1 := by linarith
  set ε := min (lam / 16) (lam * h / (32 * (T - t1 + 1))) with hε
  have hεpos : 0 < ε := lt_min (by linarith) (div_pos (mul_pos (by linarith) hh) (by linarith))
  have hε1 : ε ≤ lam / 16 := min_le_left _ _
  have hε2 : ε ≤ lam * h / (32 * (T - t1 + 1)) := min_le_right _ _
  have hε3 : ε * (32 * (T - t1 + 1)) ≤ lam * h := (le_div_iff₀ (by linarith)).mp hε2
  have hlt : m < m + ε := by linarith
  obtain ⟨_, ⟨c, hcI, rfl⟩, hcm⟩ := exists_lt_of_csInf_lt hIne hlt
  have hcT : c < T := by
    refine lt_of_le_of_ne hcI.2 (fun hcT => ?_)
    rw [hcT] at hcm
    linarith
  obtain ⟨a, haS, hca, haT, hap⟩ := exists_support_point σp hcT hTA ε hεpos
  have hPhi'a : Phi' σp σm a < m + 2 * ε := by
    rw [Phi'_gap σp σm hca]
    have := ENNReal.toReal_nonneg (a := σm (Set.Ioo c a))
    linarith
  have hHa := H a haS (T + h) (by linarith)
  rw [U_eq σp σm a (T + h) (by linarith)] at hHa
  have hK : ∀ t ∈ Set.Icc a T, -(2 * ε) ≤ fa σp σm a t := by
    intro t ht
    rw [fa_eq σp σm ht.1]
    have := hm_le t ⟨by linarith [hcI.1, ht.1], ht.2⟩
    linarith
  have hκ : ∀ t ∈ Set.Icc T (T + h), lam / 8 ≤ fa σp σm a t := by
    intro t ht
    rw [fa_eq σp σm (haT.trans ht.1)]
    have := hΦr t ht
    linarith
  have hLB := lb_integral (fa σp σm a) a T (T + h) (2 * ε) (lam / 8) haT (by linarith)
    (fa_ii σp σm a a T) (fa_ii σp σm a T (T + h)) hK hκ
  have hTa : T - a ≤ T - t1 + 1 := by linarith [hcI.1]
  have hprod : ε * (T - a) ≤ ε * (T - t1 + 1) := mul_le_mul_of_nonneg_left hTa hεpos.le
  nlinarith

lemma core_neg (hmass : σp Set.univ = σm Set.univ)
    (H : ∀ a ∈ σp.support, ∀ b, a < b →
      (∫ x, gUV a b x ∂σp) - ∫ x, gUV a b x ∂σm ≤ 0)
    (c : ℝ) (hc : Phi σp σm c < 0) : False := by
  have hΦc := Phi_Ioi σp σm hmass c
  have hpos : 0 < σp (Set.Ioi c) := by
    by_contra hcon
    have h0 : σp (Set.Ioi c) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hcon)
    rw [h0] at hΦc
    simp only [ENNReal.toReal_zero, sub_zero] at hΦc
    linarith [ENNReal.toReal_nonneg (a := σm (Set.Ioi c))]
  obtain ⟨T, hT⟩ := Measure.nonempty_inter_support_of_pos hpos
  set δ := -Phi σp σm c / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  obtain ⟨a, haS, hca, haT, hap⟩ := exists_support_point σp hT.1 hT.2 δ hδpos
  have hPa : Phi' σp σm a < -δ := by
    rw [Phi'_gap σp σm hca]
    have := ENNReal.toReal_nonneg (a := σm (Set.Ioo c a))
    linarith
  obtain ⟨R0, hR0⟩ := tail_Ioi σp (δ / 2) (by linarith)
  set R := max R0 a with hR
  have haR : a ≤ R := le_max_right _ _
  have hfaR : ∀ t ≥ R, δ / 2 ≤ fa σp σm a t := by
    intro t ht
    rw [fa_eq σp σm (haR.trans ht), Phi_Ioi σp σm hmass t]
    have h1 := hR0 t ((le_max_left _ _).trans ht)
    have h2 := ENNReal.toReal_nonneg (a := σm (Set.Ioi t))
    linarith
  set K0 := (σm Set.univ).toReal with hK0
  have hK0nn : 0 ≤ K0 := ENNReal.toReal_nonneg
  have hfaK : ∀ t, a ≤ t → -K0 ≤ fa σp σm a t := by
    intro t _
    unfold fa
    have h1 : (σm (Set.Icc a t)).toReal ≤ K0 :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
    linarith [ENNReal.toReal_nonneg (a := σp (Set.Icc a t))]
  set b := R + 2 * K0 * (R - a) / δ + 1 with hb
  have hnn : 0 ≤ 2 * K0 * (R - a) / δ :=
    div_nonneg (by nlinarith [sub_nonneg.mpr haR]) hδpos.le
  have hRb : R ≤ b := by linarith
  have hab : a < b := by linarith
  have hHa := H a haS b hab
  rw [U_eq σp σm a b hab.le] at hHa
  have hLB := lb_integral (fa σp σm a) a R b K0 (δ / 2) haR hRb (fa_ii σp σm a a R)
    (fa_ii σp σm a R b) (fun t ht => hfaK t ht.1) (fun t ht => hfaR t ht.1)
  have hcalc : δ / 2 * (b - R) = K0 * (R - a) + δ / 2 := by
    rw [hb]; field_simp; ring
  nlinarith

lemma core_zero (hne : σp ≠ σm) (h0 : ∀ t, Phi σp σm t = 0) : False := by
  apply hne
  refine Measure.ext_of_Iic σp σm (fun t => ?_)
  have := h0 t
  unfold Phi at this
  have h : (σp (Set.Iic t)).toReal = (σm (Set.Iic t)).toReal := by linarith
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h

end MCL52

open MCL52 in
theorem solution (σp σm : Measure ℝ) [IsFiniteMeasure σp] [IsFiniteMeasure σm]
    (hsing : σp ⟂ₘ σm) (hmass : σp Set.univ = σm Set.univ) (hne : σp ≠ σm) :
    ∃ a ∈ σp.support, ∃ b : ℝ, a < b ∧
      0 < (∫ x, MartOT.Curtain.gUV a b x ∂σp) - ∫ x, MartOT.Curtain.gUV a b x ∂σm := by
  by_contra hcon
  have H : ∀ a ∈ σp.support, ∀ b, a < b →
      (∫ x, MartOT.Curtain.gUV a b x ∂σp) - ∫ x, MartOT.Curtain.gUV a b x ∂σm ≤ 0 := by
    intro a ha b hab
    by_contra hlt
    exact hcon ⟨a, ha, b, hab, not_le.mp hlt⟩
  by_cases hpos : ∃ t0, 0 < Phi σp σm t0
  · obtain ⟨t0, h⟩ := hpos
    exact core_pos σp σm H t0 h
  by_cases hneg : ∃ c, Phi σp σm c < 0
  · obtain ⟨c, h⟩ := hneg
    exact core_neg σp σm hmass H c h
  · refine core_zero σp σm hne (fun t => le_antisymm ?_ ?_)
    · exact not_lt.mp (fun h => hpos ⟨t, h⟩)
    · exact not_lt.mp (fun h => hneg ⟨t, h⟩)
