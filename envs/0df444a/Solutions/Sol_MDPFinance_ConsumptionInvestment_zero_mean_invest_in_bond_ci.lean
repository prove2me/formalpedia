-- Prove2me | solution 1 for MDPFinance.ConsumptionInvestment.zero_mean_invest_in_bond_ci
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T02:42:16.064779+00:00
-- url     : https://prove2.me/submissions/2b2b2036-e4e5-4972-b5c3-3776c2617ad2

import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_Market

open MeasureTheory ProbabilityTheory


namespace MDPFinance.ConsumptionInvestment


section Det

/-- the one-step objective -/
noncomputable def ciPhi (U W : ℝ → ℝ) (r m c : ℝ) : ℝ := U (max c 0) + W (r * (m - c))

noncomputable def ciWn (U W : ℝ → ℝ) (r y : ℝ) : ℝ :=
  sSup (ciPhi U W r (max y 0) '' Set.Icc 0 (max y 0))

open Classical in
noncomputable def ciCs (U W : ℝ → ℝ) (r y : ℝ) : ℝ :=
  if h : ∃ c ∈ Set.Icc 0 (max y 0), IsMaxOn (ciPhi U W r (max y 0)) (Set.Icc 0 (max y 0)) c
  then h.choose else 0

/-- concave + monotone on `Ici 0` gives an affine upper bound -/
lemma ci_affine_bound {W : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ici 0) W)
    (hm : MonotoneOn W (Set.Ici 0)) {v : ℝ} (hv : 0 ≤ v) :
    W v ≤ W 1 + (W 1 - W 0) * v := by
  have h01 : W 0 ≤ W 1 := hm (by simp) (by simp) (by norm_num)
  rcases le_or_gt v 1 with h | h
  · have := hm (by simpa using hv) (by simp) h
    nlinarith
  · have hv0 : 0 < v := by linarith
    have hb : (0:ℝ) ≤ 1 - 1/v := by rw [sub_nonneg, div_le_one hv0]; linarith
    have := hc.2 (show v ∈ Set.Ici (0:ℝ) from hv) (show (0:ℝ) ∈ Set.Ici (0:ℝ) by simp)
      (show (0:ℝ) ≤ 1/v by positivity) hb (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero] at this
    rw [one_div_mul_cancel hv0.ne'] at this
    have h2 : W v * (1/v) ≤ W 1 - (1 - 1/v) * W 0 := by linarith
    have h3 : W v ≤ (W 1 - (1 - 1/v) * W 0) * v := by
      rwa [← div_le_iff₀ hv0, div_eq_mul_one_div]
    have : (W 1 - (1 - 1/v) * W 0) * v = W 1 + (W 1 - W 0) * v - W 1 + W 0 := by
      field_simp; ring
    nlinarith

variable {U W : ℝ → ℝ} {r : ℝ}

structure CIGood (U : ℝ → ℝ) (W : ℝ → ℝ) : Prop where
  cont : Continuous W
  conc : ConcaveOn ℝ (Set.Ici 0) W
  mono : Monotone W

lemma ciPhi_cont (hU : ContinuousOn U (Set.Ici 0)) (hW : Continuous W) (r m : ℝ) :
    Continuous (ciPhi U W r m) := by
  unfold ciPhi
  have h1 : Continuous (fun c : ℝ => U (max c 0)) :=
    hU.comp_continuous (continuous_id.max continuous_const) (fun c => Set.mem_Ici.2 (le_max_right _ _))
  exact h1.add (hW.comp (continuous_const.mul (continuous_const.sub continuous_id)))

lemma ciCs_spec (hU : ContinuousOn U (Set.Ici 0)) (hW : Continuous W) (y : ℝ) :
    ciCs U W r y ∈ Set.Icc 0 (max y 0) ∧
      IsMaxOn (ciPhi U W r (max y 0)) (Set.Icc 0 (max y 0)) (ciCs U W r y) := by
  have hex : ∃ c ∈ Set.Icc 0 (max y 0), IsMaxOn (ciPhi U W r (max y 0)) (Set.Icc 0 (max y 0)) c :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 (le_max_right _ _))
      (ciPhi_cont hU hW r _).continuousOn
  unfold ciCs
  rw [dif_pos hex]
  exact hex.choose_spec

lemma ciWn_eq (hU : ContinuousOn U (Set.Ici 0)) (hW : Continuous W) (y : ℝ) :
    ciWn U W r y = ciPhi U W r (max y 0) (ciCs U W r y) := by
  obtain ⟨h1, h2⟩ := ciCs_spec (r := r) hU hW y
  unfold ciWn
  apply IsGreatest.csSup_eq
  refine ⟨⟨_, h1, rfl⟩, ?_⟩
  rintro _ ⟨c, hc, rfl⟩
  exact h2 hc

lemma le_ciWn (hU : ContinuousOn U (Set.Ici 0)) (hW : Continuous W) (y c : ℝ)
    (hc : c ∈ Set.Icc 0 (max y 0)) :
    ciPhi U W r (max y 0) c ≤ ciWn U W r y := by
  rw [ciWn_eq hU hW]
  exact (ciCs_spec hU hW y).2 hc

lemma ciWn_max (y : ℝ) : ciWn U W r (max y 0) = ciWn U W r y := by
  unfold ciWn; rw [max_eq_left (le_max_right y 0)]

lemma ciCs_max (y : ℝ) : ciCs U W r (max y 0) = ciCs U W r y := by
  unfold ciCs; rw [max_eq_left (le_max_right y 0)]


section Props
variable (hUm : StrictMonoOn U (Set.Ici 0)) (hUc : StrictConcaveOn ℝ (Set.Ici 0) U)
  (hUk : ContinuousOn U (Set.Ici 0)) (hW : CIGood U W) (hr : 0 < r)
include hUm hUc hUk hW hr

lemma ciWn_upper (y : ℝ) : ciWn U W r y ≤ U (max y 0) + W (r * max y 0) := by
  rw [ciWn_eq hUk hW.cont]
  obtain ⟨⟨h0, h1⟩, -⟩ := ciCs_spec (r := r) hUk hW.cont y
  unfold ciPhi
  have hm0 : (0:ℝ) ≤ max y 0 := le_max_right _ _
  gcongr
  · exact hUm.monotoneOn (Set.mem_Ici.2 (le_max_right _ _)) (Set.mem_Ici.2 hm0)
      (max_le h1 hm0)
  · exact hW.mono (by nlinarith)

lemma ciWn_zero : ciWn U W r 0 = U 0 + W 0 := by
  rw [ciWn_eq hUk hW.cont]
  obtain ⟨⟨h0, h1⟩, -⟩ := ciCs_spec (r := r) hUk hW.cont (0:ℝ)
  have : ciCs U W r 0 = 0 := by simp at h1; linarith
  rw [this]; simp [ciPhi]

lemma ciWn_mono : Monotone (ciWn U W r) := by
  intro y y' hyy
  rw [ciWn_eq hUk hW.cont y]
  obtain ⟨⟨h0, h1⟩, -⟩ := ciCs_spec (r := r) hUk hW.cont y
  have hm : max y 0 ≤ max y' 0 := max_le_max hyy le_rfl
  calc ciPhi U W r (max y 0) (ciCs U W r y) ≤ ciPhi U W r (max y' 0) (ciCs U W r y) := by
        unfold ciPhi; gcongr; exact hW.mono (by nlinarith)
    _ ≤ _ := le_ciWn hUk hW.cont y' _ ⟨h0, h1.trans hm⟩

lemma ciWn_concave : ConcaveOn ℝ (Set.Ici 0) (ciWn U W r) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro y1 hy1 y2 hy2 a b ha hb hab
  simp only [Set.mem_Ici] at hy1 hy2
  simp only [smul_eq_mul]
  obtain ⟨⟨h10, h11⟩, -⟩ := ciCs_spec (r := r) hUk hW.cont y1
  obtain ⟨⟨h20, h21⟩, -⟩ := ciCs_spec (r := r) hUk hW.cont y2
  rw [max_eq_left hy1] at h11
  rw [max_eq_left hy2] at h21
  set c1 := ciCs U W r y1
  set c2 := ciCs U W r y2
  have hy : 0 ≤ a * y1 + b * y2 := by positivity
  have e1 := ciWn_eq (r := r) hUk hW.cont y1
  have e2 := ciWn_eq (r := r) hUk hW.cont y2
  rw [e1, e2]
  have hmem : a * c1 + b * c2 ∈ Set.Icc 0 (max (a * y1 + b * y2) 0) := by
    rw [max_eq_left hy]; constructor
    · positivity
    · nlinarith
  refine le_trans ?_ (le_ciWn hUk hW.cont _ _ hmem)
  unfold ciPhi
  rw [max_eq_left hy1, max_eq_left hy2, max_eq_left hy, max_eq_left h10, max_eq_left h20,
    max_eq_left (by positivity : (0:ℝ) ≤ a * c1 + b * c2)]
  have hU := hUc.concaveOn.2 (Set.mem_Ici.2 h10) (Set.mem_Ici.2 h20) ha hb hab
  have hWc := hW.conc.2 (Set.mem_Ici.2 (show 0 ≤ r * (y1 - c1) by nlinarith))
    (Set.mem_Ici.2 (show 0 ≤ r * (y2 - c2) by nlinarith)) ha hb hab
  simp only [smul_eq_mul] at hU hWc
  have : a * (r * (y1 - c1)) + b * (r * (y2 - c2)) = r * (a * y1 + b * y2 - (a * c1 + b * c2)) := by
    ring
  rw [this] at hWc
  nlinarith

lemma ciWn_cont : Continuous (ciWn U W r) := by
  have hcon := ciWn_concave hUm hUc hUk hW hr
  have hmono := ciWn_mono hUm hUc hUk hW hr
  have hon : ContinuousOn (ciWn U W r) (Set.Ici 0) := by
    intro y hy
    rcases (Set.mem_Ici.1 hy).lt_or_eq with h | h
    · have := hcon.continuousOn_interior
      rw [interior_Ici] at this
      exact (this.continuousAt (Ioi_mem_nhds h)).continuousWithinAt
    · subst h
      have hup : Continuous (fun y : ℝ => U (max y 0) + W (r * max y 0)) :=
        (hUk.comp_continuous (continuous_id.max continuous_const)
          (fun c => Set.mem_Ici.2 (le_max_right _ _))).add
          (hW.cont.comp (continuous_const.mul (continuous_id.max continuous_const)))
      have h1 : Filter.Tendsto (fun y : ℝ => U (max y 0) + W (r * max y 0))
          (nhdsWithin 0 (Set.Ici 0)) (nhds (ciWn U W r 0)) := by
        rw [ciWn_zero hUm hUc hUk hW hr]
        have := (hup.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ici 0))
        simpa using this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact hmono hy
      · filter_upwards with y
        exact ciWn_upper hUm hUc hUk hW hr y
  have : ciWn U W r = (ciWn U W r) ∘ (fun y => max y 0) := by
    funext y; simp [ciWn_max]
  rw [this]
  exact hon.comp_continuous (continuous_id.max continuous_const)
    (fun c => Set.mem_Ici.2 (le_max_right _ _))

lemma ciWn_good : CIGood U (ciWn U W r) :=
  ⟨ciWn_cont hUm hUc hUk hW hr, ciWn_concave hUm hUc hUk hW hr, ciWn_mono hUm hUc hUk hW hr⟩

/-- uniqueness of the maximizer -/
lemma ciCs_unique (y c : ℝ) (hc : c ∈ Set.Icc 0 (max y 0))
    (hmax : ciWn U W r y ≤ ciPhi U W r (max y 0) c) : c = ciCs U W r y := by
  by_contra hne
  obtain ⟨⟨h0, h1⟩, hM⟩ := ciCs_spec (r := r) hUk hW.cont y
  set m := max y 0
  set c2 := ciCs U W r y
  have e := ciWn_eq (r := r) hUk hW.cont y
  have hmid : (1/2 : ℝ) * c + (1/2) * c2 ∈ Set.Icc 0 m := ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have hle : ciPhi U W r m ((1/2)*c + (1/2)*c2) ≤ ciPhi U W r m c2 := hM hmid
  have hU := hUc.2 (Set.mem_Ici.2 hc.1) (Set.mem_Ici.2 h0) hne (show (0:ℝ) < 1/2 by norm_num)
    (show (0:ℝ) < 1/2 by norm_num) (by norm_num)
  have hWc := hW.conc.2 (Set.mem_Ici.2 (show 0 ≤ r * (m - c) by nlinarith [hc.2]))
    (Set.mem_Ici.2 (show 0 ≤ r * (m - c2) by nlinarith)) (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at hU hWc
  have : (1/2:ℝ) * (r * (m - c)) + 1/2 * (r * (m - c2)) = r * (m - ((1/2) * c + (1/2) * c2)) := by
    ring
  rw [this] at hWc
  unfold ciPhi at hle hmax e
  rw [max_eq_left hc.1] at hmax
  rw [max_eq_left h0] at e
  rw [max_eq_left (show (0:ℝ) ≤ 1/2 * c + 1/2 * c2 by linarith [hc.1])] at hle
  rw [max_eq_left h0] at hle
  linarith

lemma ciCs_nonneg (y : ℝ) : 0 ≤ ciCs U W r y := (ciCs_spec (r := r) hUk hW.cont y).1.1

lemma ciCs_mono : Monotone (ciCs U W r) := by
  have key : ∀ y y', 0 ≤ y → y < y' → ciCs U W r y ≤ ciCs U W r y' := by
    intro y y' hy hyy
    by_contra hlt
    push_neg at hlt
    have hy' : 0 ≤ y' := by linarith
    obtain ⟨⟨h0, h1⟩, hM⟩ := ciCs_spec (r := r) hUk hW.cont y
    obtain ⟨⟨h0', h1'⟩, hM'⟩ := ciCs_spec (r := r) hUk hW.cont y'
    rw [max_eq_left hy] at h1 hM
    rw [max_eq_left hy'] at h1' hM'
    set c := ciCs U W r y
    set c' := ciCs U W r y'
    -- supermodularity
    have hsup : W (r * (y - c)) + W (r * (y' - c')) ≤ W (r * (y - c')) + W (r * (y' - c)) := by
      set p := r * (y - c); set s := r * (y' - c'); set q1 := r * (y - c'); set q2 := r * (y' - c)
      have hp : 0 ≤ p := by nlinarith
      have hps : p < s := by nlinarith
      set t := (s - q1) / (s - p)
      have hsp : 0 < s - p := by linarith
      have ht0 : 0 ≤ t := div_nonneg (by nlinarith) hsp.le
      have ht1 : t ≤ 1 := by rw [div_le_one hsp]; nlinarith
      have hq1 : q1 = t * p + (1 - t) * s := by
        simp only [t]; field_simp; ring
      have hq2 : q2 = (1 - t) * p + t * s := by
        have : q2 = p + s - q1 := by simp only [p, s, q1, q2]; ring
        rw [this, hq1]; ring
      have a1 := hW.conc.2 (Set.mem_Ici.2 hp) (Set.mem_Ici.2 (show 0 ≤ s by linarith))
        ht0 (show 0 ≤ 1 - t by linarith) (by ring)
      have a2 := hW.conc.2 (Set.mem_Ici.2 hp) (Set.mem_Ici.2 (show 0 ≤ s by linarith))
        (show 0 ≤ 1 - t by linarith) ht0 (by ring)
      simp only [smul_eq_mul] at a1 a2
      rw [← hq1] at a1; rw [← hq2] at a2
      nlinarith
    have e1 : ciPhi U W r y' c ≤ ciPhi U W r y' c' := hM' (show c ∈ Set.Icc 0 y' from ⟨h0, by linarith⟩)
    have hc'mem : c' ∈ Set.Icc 0 (max y 0) := by rw [max_eq_left hy]; exact ⟨h0', by linarith⟩
    have := ciCs_unique hUm hUc hUk hW hr y c' hc'mem (by
      rw [ciWn_eq hUk hW.cont y, max_eq_left hy]
      unfold ciPhi at e1 ⊢
      linarith)
    exact absurd this (ne_of_lt hlt)
  intro y y' hyy
  rw [← ciCs_max (y := y), ← ciCs_max (y := y')]
  rcases (max_le_max hyy (le_refl (0:ℝ))).lt_or_eq with h | h
  · exact key _ _ (le_max_right _ _) h
  · rw [h]

end Props

end Det



section Prob

/-- concave + monotone on `Ici 0` gives an affine upper bound -/
lemma ci_affine_bound0 {W : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ici 0) W)
    (hm : MonotoneOn W (Set.Ici 0)) {v : ℝ} (hv : 0 ≤ v) :
    W v ≤ W 1 + (W 1 - W 0) * v := by
  have h01 : W 0 ≤ W 1 := hm (by simp) (by simp) (by norm_num)
  rcases le_or_gt v 1 with h | h
  · have := hm (by simpa using hv) (by simp) h
    nlinarith
  · have hv0 : 0 < v := by linarith
    have hb : (0:ℝ) ≤ 1 - 1/v := by rw [sub_nonneg, div_le_one hv0]; linarith
    have := hc.2 (show v ∈ Set.Ici (0:ℝ) from hv) (show (0:ℝ) ∈ Set.Ici (0:ℝ) by simp)
      (show (0:ℝ) ≤ 1/v by positivity) hb (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero] at this
    rw [one_div_mul_cancel hv0.ne'] at this
    have h2 : W v * (1/v) ≤ W 1 - (1 - 1/v) * W 0 := by linarith
    have h3 : W v ≤ (W 1 - (1 - 1/v) * W 0) * v := by
      rwa [← div_le_iff₀ hv0, div_eq_mul_one_div]
    have : (W 1 - (1 - 1/v) * W 0) * v = W 1 + (W 1 - W 0) * v - W 1 + W 0 := by
      field_simp; ring
    nlinarith


lemma ci_affine_bound' {W : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ici 0) W)
    (hm : Monotone W) {v : ℝ} (hv : 0 ≤ v) :
    W v ≤ W 1 + (W 1 - W 0) * v := ci_affine_bound0 hc (hm.monotoneOn _) hv


def ciT {d : ℕ} (g : ℝ → ℝ × (Fin d → ℝ)) (ρ y : ℝ) (z : Fin d → ℝ) : ℝ :=
  ρ * (y - (g y).1 + ∑ j, (g y).2 j * z j)

lemma ciT_meas {d : ℕ} {g : ℝ → ℝ × (Fin d → ℝ)} (hg : Measurable g) (ρ : ℝ) :
    Measurable (fun p : ℝ × (Fin d → ℝ) => ciT g ρ p.1 p.2) := by
  unfold ciT
  have h1 : Measurable (fun p : ℝ × (Fin d → ℝ) => (g p.1).1) := measurable_fst.comp (hg.comp measurable_fst)
  have h2 : ∀ j, Measurable (fun p : ℝ × (Fin d → ℝ) => (g p.1).2 j) := fun j =>
    (measurable_pi_apply j).comp (measurable_snd.comp (hg.comp measurable_fst))
  have h3 : ∀ j, Measurable (fun p : ℝ × (Fin d → ℝ) => p.2 j) := fun j =>
    (measurable_pi_apply j).comp measurable_snd
  refine measurable_const.mul ((measurable_fst.sub h1).add ?_)
  exact Finset.measurable_sum _ (fun j _ => (h2 j).mul (h3 j))

lemma ci_W_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ → ℝ} (hW : Continuous W) (hWc : ConcaveOn ℝ (Set.Ici 0) W) (hWm : Monotone W)
    {f : Ω → ℝ} (hf : Integrable f P) (hf0 : ∀ᵐ ω ∂P, 0 ≤ f ω) :
    Integrable (fun ω => W (f ω)) P := by
  have hb : Integrable (fun ω => |W 0| + |W 1| + |W 1 - W 0| * |f ω|) P :=
    (integrable_const _).add (hf.abs.const_mul _)
  refine hb.mono' (hW.comp_aestronglyMeasurable hf.aestronglyMeasurable) ?_
  filter_upwards [hf0] with ω hω
  have h1 := hWm hω
  have h2 := ci_affine_bound' hWc hWm hω
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := neg_abs_le (W 0)
    have : 0 ≤ |W 1| := abs_nonneg _
    have : 0 ≤ |W 1 - W 0| * |f ω| := by positivity
    linarith
  · have : (W 1 - W 0) * f ω ≤ |W 1 - W 0| * |f ω| := by
      rw [← abs_mul]; exact le_abs_self _
    have := le_abs_self (W 1)
    have := abs_nonneg (W 0)
    linarith


variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
  {Y : Ω → ℝ} {R : Ω → Fin d → ℝ} {g : ℝ → ℝ × (Fin d → ℝ)} {ρ : ℝ}

lemma ci_t_facts (hRi : ∀ j, Integrable (fun ω => R ω j) P) (hR0 : ∀ j, ∫ ω, R ω j ∂P = 0)
    (a : Fin d → ℝ) :
    Integrable (fun ω => ∑ j, a j * R ω j) P ∧ ∫ ω, ∑ j, a j * R ω j ∂P = 0 := by
  refine ⟨integrable_finset_sum _ (fun j _ => (hRi j).const_mul _), ?_⟩
  rw [integral_finset_sum _ (fun j _ => (hRi j).const_mul _)]
  simp [integral_const_mul, hR0]

lemma ci_one_step (hY : Measurable Y) (hR : Measurable R) (hind : IndepFun Y R P)
    (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω) (hYi : Integrable Y P)
    (hRi : ∀ j, Integrable (fun ω => R ω j) P) (hR0 : ∀ j, ∫ ω, R ω j ∂P = 0)
    (hg : Measurable g) (hρ : 0 < ρ)
    (hadm : ∀ y, 0 ≤ y → 0 ≤ (g y).1 ∧ (g y).1 ≤ y ∧
      ∀ᵐ ω ∂P, 0 ≤ ciT g ρ y (R ω))
    {W : ℝ → ℝ} (hW : Continuous W) (hWc : ConcaveOn ℝ (Set.Ici 0) W) (hWm : Monotone W) :
    (∀ᵐ ω ∂P, 0 ≤ ciT g ρ (Y ω) (R ω)) ∧ Integrable (fun ω => ciT g ρ (Y ω) (R ω)) P ∧
      Integrable (fun ω => W (ciT g ρ (Y ω) (R ω))) P ∧
      Integrable (fun ω => W (ρ * (Y ω - (g (Y ω)).1))) P ∧
      ∫ ω, W (ciT g ρ (Y ω) (R ω)) ∂P ≤ ∫ ω, W (ρ * (Y ω - (g (Y ω)).1)) ∂P := by
  set μY := P.map Y
  set μR := P.map R
  haveI : IsProbabilityMeasure μY := Measure.isProbabilityMeasure_map hY.aemeasurable
  haveI : IsProbabilityMeasure μR := Measure.isProbabilityMeasure_map hR.aemeasurable
  have hpair : Measurable (fun ω => (Y ω, R ω)) := hY.prodMk hR
  have hprod : P.map (fun ω => (Y ω, R ω)) = μY.prod μR :=
    (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hR.aemeasurable).1 hind
  have hYae : ∀ᵐ y ∂μY, 0 ≤ y := (ae_map_iff hY.aemeasurable measurableSet_Ici).2 hY0
  have hTm := ciT_meas hg ρ
  -- (1)
  have h1 : ∀ᵐ ω ∂P, 0 ≤ ciT g ρ (Y ω) (R ω) := by
    have hS : MeasurableSet {p : ℝ × (Fin d → ℝ) | ciT g ρ p.1 p.2 < 0} :=
      measurableSet_lt hTm measurable_const
    rw [ae_iff]
    have : {ω | ¬ 0 ≤ ciT g ρ (Y ω) (R ω)} =
        (fun ω => (Y ω, R ω)) ⁻¹' {p : ℝ × (Fin d → ℝ) | ciT g ρ p.1 p.2 < 0} := by
      ext ω; simp
    rw [this, ← Measure.map_apply hpair hS, hprod, Measure.prod_apply hS]
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [hYae] with y hy
    rw [Measure.map_apply hR (measurable_prodMk_left hS)]
    have := (hadm y hy).2.2
    rw [ae_iff] at this
    simpa using this
  -- (2) integrability of the investment part
  have hs_meas : Measurable (fun ω => ∑ j, (g (Y ω)).2 j * R ω j) := by
    refine Finset.measurable_sum _ (fun j _ => ?_)
    exact ((measurable_pi_apply j).comp (measurable_snd.comp (hg.comp hY))).mul
      ((measurable_pi_apply j).comp hR)
  have hinner : ∀ y, 0 ≤ y →
      ∫⁻ ω, ENNReal.ofReal |∑ j, (g y).2 j * R ω j| ∂P ≤ ENNReal.ofReal (2 * y) := by
    intro y hy
    obtain ⟨hti, ht0⟩ := ci_t_facts hRi hR0 (g y).2
    obtain ⟨hc0, hcy, hae⟩ := hadm y hy
    rw [← ofReal_integral_eq_lintegral_ofReal hti.abs (Filter.Eventually.of_forall
      (fun _ => abs_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    calc ∫ ω, |∑ j, (g y).2 j * R ω j| ∂P
        ≤ ∫ ω, (∑ j, (g y).2 j * R ω j + 2 * (y - (g y).1)) ∂P := by
          apply integral_mono_ae hti.abs (hti.add (integrable_const _))
          filter_upwards [hae] with ω hω
          unfold ciT at hω
          have := (mul_nonneg_iff_of_pos_left hρ).1 hω
          simp only [Pi.add_apply]
          rw [abs_le]; constructor <;> linarith
      _ = 2 * (y - (g y).1) := by
          rw [integral_add hti (integrable_const _), ht0]; simp
      _ ≤ 2 * y := by linarith
  have hs_int : Integrable (fun ω => ∑ j, (g (Y ω)).2 j * R ω j) P := by
    refine ⟨hs_meas.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal_abs]
    have hF : Measurable (fun p : ℝ × (Fin d → ℝ) =>
        ENNReal.ofReal |∑ j, (g p.1).2 j * p.2 j|) := by
      refine ENNReal.measurable_ofReal.comp (Measurable.abs ?_)
      exact Finset.measurable_sum _ (fun j _ =>
        ((measurable_pi_apply j).comp (measurable_snd.comp (hg.comp measurable_fst))).mul
        ((measurable_pi_apply j).comp measurable_snd))
    have e : ∫⁻ ω, ENNReal.ofReal |∑ j, (g (Y ω)).2 j * R ω j| ∂P =
        ∫⁻ y, ∫⁻ z, ENNReal.ofReal |∑ j, (g y).2 j * z j| ∂μR ∂μY := by
      rw [← lintegral_prod _ hF.aemeasurable, ← hprod, lintegral_map hF hpair]
    rw [e]
    calc ∫⁻ y, ∫⁻ z, ENNReal.ofReal |∑ j, (g y).2 j * z j| ∂μR ∂μY
        ≤ ∫⁻ y, ENNReal.ofReal (2 * y) ∂μY := by
          apply lintegral_mono_ae
          filter_upwards [hYae] with y hy
          rw [lintegral_map (f := fun z : Fin d → ℝ => ENNReal.ofReal |∑ j, (g y).2 j * z j|)
            (ENNReal.measurable_ofReal.comp (Measurable.abs
            (Finset.measurable_sum _ (fun j _ => measurable_const.mul
              (measurable_pi_apply j))))) hR]
          exact hinner y hy
      _ = ∫⁻ ω, ENNReal.ofReal (2 * Y ω) ∂P := by
          rw [lintegral_map (f := fun y : ℝ => ENNReal.ofReal (2 * y))
            (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id)) hY]
      _ < ⊤ := by
          have := (hYi.const_mul 2).2
          refine lt_of_le_of_lt (lintegral_mono (fun ω => ?_)) this
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hc_int : Integrable (fun ω => Y ω - (g (Y ω)).1) P := by
    refine hYi.mono' (hY.sub (measurable_fst.comp (hg.comp hY))).aestronglyMeasurable ?_
    filter_upwards [hY0] with ω hω
    obtain ⟨a, b, -⟩ := hadm (Y ω) hω
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  have h2 : Integrable (fun ω => ciT g ρ (Y ω) (R ω)) P := by
    have : (fun ω => ciT g ρ (Y ω) (R ω)) =
        fun ω => ρ * (Y ω - (g (Y ω)).1) + ρ * ∑ j, (g (Y ω)).2 j * R ω j := by
      funext ω; unfold ciT; ring
    rw [this]
    exact (hc_int.const_mul ρ).add (hs_int.const_mul ρ)
  have h3 := ci_W_integrable hW hWc hWm h2 h1
  have h4 : Integrable (fun ω => W (ρ * (Y ω - (g (Y ω)).1))) P := by
    refine ci_W_integrable hW hWc hWm (hc_int.const_mul ρ) ?_
    filter_upwards [hY0] with ω hω
    obtain ⟨a, b, -⟩ := hadm (Y ω) hω
    exact mul_nonneg hρ.le (by linarith)
  refine ⟨h1, h2, h3, h4, ?_⟩
  -- (4) the inequality
  have hWT : Measurable (fun p : ℝ × (Fin d → ℝ) => W (ciT g ρ p.1 p.2)) := hW.measurable.comp hTm
  have hWc' : Measurable (fun y : ℝ => W (ρ * (y - (g y).1))) :=
    hW.measurable.comp (measurable_const.mul (measurable_id.sub (measurable_fst.comp hg)))
  have hint_prod : Integrable (fun p : ℝ × (Fin d → ℝ) => W (ciT g ρ p.1 p.2)) (μY.prod μR) := by
    rw [← hprod, integrable_map_measure hWT.aestronglyMeasurable hpair.aemeasurable]
    exact h3
  have eL : ∫ ω, W (ciT g ρ (Y ω) (R ω)) ∂P = ∫ y, ∫ z, W (ciT g ρ y z) ∂μR ∂μY := by
    rw [← integral_prod _ hint_prod, ← hprod,
      integral_map hpair.aemeasurable hWT.aestronglyMeasurable]
  have eR : ∫ ω, W (ρ * (Y ω - (g (Y ω)).1)) ∂P = ∫ y, W (ρ * (y - (g y).1)) ∂μY := by
    rw [integral_map hY.aemeasurable hWc'.aestronglyMeasurable]
  rw [eL, eR]
  apply integral_mono_ae hint_prod.integral_prod_left
  · rw [integrable_map_measure hWc'.aestronglyMeasurable hY.aemeasurable]; exact h4
  filter_upwards [hYae] with y hy
  obtain ⟨hc0, hcy, hae⟩ := hadm y hy
  obtain ⟨hti, ht0⟩ := ci_t_facts hRi hR0 (g y).2
  have hTy_m : Measurable (fun z : Fin d → ℝ => W (ciT g ρ y z)) :=
    hWT.comp (measurable_const.prodMk measurable_id)
  rw [integral_map hR.aemeasurable hTy_m.aestronglyMeasurable]
  have hfi : Integrable (fun ω => ciT g ρ y (R ω)) P := by
    have : (fun ω => ciT g ρ y (R ω)) = fun ω => ρ * (y - (g y).1) + ρ * ∑ j, (g y).2 j * R ω j := by
      funext ω; unfold ciT; ring
    rw [this]; exact (integrable_const _).add (hti.const_mul ρ)
  have hJ := hWc.le_map_integral hW.continuousOn isClosed_Ici hae hfi
    (ci_W_integrable hW hWc hWm hfi hae)
  have hmean : ∫ ω, ciT g ρ y (R ω) ∂P = ρ * (y - (g y).1) := by
    have : (fun ω => ciT g ρ y (R ω)) = fun ω => ρ * (y - (g y).1) + ρ * ∑ j, (g y).2 j * R ω j := by
      funext ω; unfold ciT; ring
    rw [this, integral_add (integrable_const _) (hti.const_mul ρ), integral_const,
      integral_const_mul, ht0]
    simp
  rw [hmean] at hJ
  exact hJ

end Prob


section Glue

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

lemma ci_erealIntegral_of_integrable {P : Measure Ω} {f : Ω → ℝ} (hf : Integrable f P) :
    erealIntegral P (fun ω => (f ω : EReal)) = ((∫ ω, f ω ∂P : ℝ) : EReal) := by
  unfold erealIntegral
  have e1 : ∀ ω, ((f ω : EReal) ⊔ 0).toENNReal = ENNReal.ofReal (f ω) := by
    intro ω
    rcases le_total 0 (f ω) with h | h
    · rw [sup_eq_left.2 (EReal.coe_nonneg.2 h), EReal.real_coe_toENNReal]
    · rw [sup_eq_right.2 (EReal.coe_nonpos.2 h), EReal.toENNReal_zero, ENNReal.ofReal_of_nonpos h]
  have e2 : ∀ ω, ((-(f ω : EReal)) ⊔ 0).toENNReal = ENNReal.ofReal (-f ω) := by
    intro ω
    rw [← EReal.coe_neg]
    rcases le_total 0 (-f ω) with h | h
    · rw [sup_eq_left.2 (EReal.coe_nonneg.2 h), EReal.real_coe_toENNReal]
    · rw [sup_eq_right.2 (EReal.coe_nonpos.2 h), EReal.toENNReal_zero, ENNReal.ofReal_of_nonpos h]
  simp_rw [e1, e2]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  have h1 : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_mono (fun ω => by
      rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _))) hf.2).ne
  have h2 : ∫⁻ ω, ENNReal.ofReal (-f ω) ∂P ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_mono (fun ω => by
      rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (neg_le_abs _))) hf.2).ne
  rw [← EReal.coe_ennreal_toReal h1, ← EReal.coe_ennreal_toReal h2]
  rfl

lemma ci_erealIntegral_congr {P : Measure Ω} {f g : Ω → ℝ} (h : f =ᵐ[P] g) :
    erealIntegral P (fun ω => (f ω : EReal)) = erealIntegral P (fun ω => (g ω : EReal)) := by
  unfold erealIntegral
  have e : ∀ (F : EReal → ENNReal), ∫⁻ ω, F (f ω) ∂P = ∫⁻ ω, F (g ω) ∂P := fun F =>
    lintegral_congr_ae (h.mono fun ω hω => by simp only [hω])
  have a1 := e (fun t => (t ⊔ 0).toENNReal)
  have a2 := e (fun t => ((-t) ⊔ 0).toENNReal)
  rw [a1, a2]

variable (M : ConsumptionInvestmentMarket Ω d)

noncomputable def ciWk : ℕ → ℝ → ℝ
  | 0 => fun y => M.Up (max y 0)
  | k + 1 => ciWn M.Uc (ciWk k) (1 + M.i (M.N - k))

noncomputable def ciWt (n : ℕ) : ℝ → ℝ := ciWk M (M.N - n)

noncomputable def ciUcl (c : ℝ) : ℝ := M.Uc (max c 0)

lemma ciUcl_good (hdomU : M.domU = Set.Ici (0:ℝ)) : CIGood M.Uc (ciUcl M) := by
  have hc := M.hUc_cont; have hm := M.hUc_mono; have hcc := M.hUc_concave
  rw [hdomU] at hc hm hcc
  refine ⟨hc.comp_continuous (continuous_id.max continuous_const)
    (fun c => Set.mem_Ici.2 (le_max_right _ _)), ?_, ?_⟩
  · refine hcc.concaveOn.congr ?_
    intro c hc; simp [ciUcl, max_eq_left (Set.mem_Ici.1 hc)]
  · intro a b hab
    exact hm.monotoneOn (Set.mem_Ici.2 (le_max_right _ _)) (Set.mem_Ici.2 (le_max_right _ _))
      (max_le_max hab le_rfl)

lemma ciWk_good (hdomU : M.domU = Set.Ici (0:ℝ)) : ∀ k, k ≤ M.N → CIGood M.Uc (ciWk M k) := by
  have hc := M.hUc_cont; have hm := M.hUc_mono; have hcc := M.hUc_concave
  have pc := M.hUp_cont; have pm := M.hUp_mono; have pcc := M.hUp_concave
  rw [hdomU] at hc hm hcc pc pm pcc
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨pc.comp_continuous (continuous_id.max continuous_const)
      (fun c => Set.mem_Ici.2 (le_max_right _ _)), ?_, ?_⟩
    · refine pcc.concaveOn.congr ?_
      intro c hc; simp [ciWk, max_eq_left (Set.mem_Ici.1 hc)]
    · intro a b hab
      exact pm.monotoneOn (Set.mem_Ici.2 (le_max_right _ _)) (Set.mem_Ici.2 (le_max_right _ _))
        (max_le_max hab le_rfl)
  | succ k ih =>
    intro hk
    have hr : 0 < 1 + M.i (M.N - k) := M.hi_pos _ (by omega) (by omega)
    exact ciWn_good hm hcc hc (ih (by omega)) hr

lemma ciWt_succ {n : ℕ} (hn : n < M.N) :
    ciWt M n = ciWn M.Uc (ciWt M (n + 1)) (1 + M.i (n + 1)) := by
  unfold ciWt
  have : M.N - n = (M.N - (n + 1)) + 1 := by omega
  rw [this, ciWk]
  congr 3
  omega

lemma ciWt_good (hdomU : M.domU = Set.Ici (0:ℝ)) (n : ℕ) : CIGood M.Uc (ciWt M n) :=
  ciWk_good M hdomU _ (Nat.sub_le _ _)

lemma ciWt_N (y : ℝ) : ciWt M M.N y = M.Up (max y 0) := by
  simp [ciWt, ciWk]

noncomputable def ciCstar (n : ℕ) (y : ℝ) : ℝ := ciCs M.Uc (ciWt M (n + 1)) (1 + M.i (n + 1)) y

noncomputable def ciFstar (n : ℕ) (y : ℝ) : ℝ × (Fin d → ℝ) := (ciCstar M n y, 0)

end Glue

section Glue2

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : ConsumptionInvestmentMarket Ω d)
  (hdomU : M.domU = Set.Ici (0:ℝ))
include hdomU

lemma ciCstar_spec (n : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ ciCstar M n y ∧ ciCstar M n y ≤ y := by
  have hc := M.hUc_cont; rw [hdomU] at hc
  have := (ciCs_spec (r := 1 + M.i (n + 1)) hc (ciWt_good M hdomU (n+1)).cont y).1
  rw [max_eq_left hy] at this
  exact this

lemma ciCstar_value (n : ℕ) (hn : n < M.N) (y : ℝ) (hy : 0 ≤ y) :
    M.Uc (ciCstar M n y) + ciWt M (n + 1) ((1 + M.i (n + 1)) * (y - ciCstar M n y)) =
      ciWt M n y := by
  have hc := M.hUc_cont; rw [hdomU] at hc
  rw [ciWt_succ M hn, ciWn_eq hc (ciWt_good M hdomU (n+1)).cont]
  obtain ⟨h0, -⟩ := ciCstar_spec M hdomU n y hy
  unfold ciPhi ciCstar at *
  rw [max_eq_left hy, max_eq_left h0]

lemma ciDP (n : ℕ) (hn : n < M.N) (y c : ℝ) (hy : 0 ≤ y) (hc0 : 0 ≤ c) (hcy : c ≤ y) :
    ciUcl M c + ciWt M (n + 1) ((1 + M.i (n + 1)) * (y - c)) ≤ ciWt M n y := by
  have hc := M.hUc_cont; rw [hdomU] at hc
  rw [ciWt_succ M hn]
  have := le_ciWn (r := 1 + M.i (n + 1)) hc (ciWt_good M hdomU (n+1)).cont y c
    (by rw [max_eq_left hy]; exact ⟨hc0, hcy⟩)
  unfold ciPhi at this
  rw [max_eq_left hy] at this
  exact this

lemma ciFstar_adm : M.IsAdmissible 0 (ciFstar M) := by
  intro k _ hk
  have hUm := M.hUc_mono; have hUcc := M.hUc_concave; have hc := M.hUc_cont
  rw [hdomU] at hUm hUcc hc
  have hr : 0 < 1 + M.i (k + 1) := M.hi_pos _ (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [hdomU] at hx
    obtain ⟨h0, h1⟩ := ciCstar_spec M hdomU k x hx
    refine ⟨h0, h1, by rw [hdomU]; exact h0, ?_⟩
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [hdomU]
    simp only [ciFstar, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, Set.mem_Ici]
    exact mul_nonneg hr.le (by linarith)
  · unfold ciFstar
    exact (ciCs_mono hUm hUcc hc (ciWt_good M hdomU (k+1)) hr).measurable.prodMk measurable_const

lemma ciFstar_path : ∀ k n y, n + k = M.N → 0 ≤ y → ∀ ω,
    (M.stateAcc (ciFstar M) k n y ω).2 + M.Up (M.stateAcc (ciFstar M) k n y ω).1 = ciWt M n y := by
  intro k
  induction k with
  | zero =>
    intro n y hn hy ω
    rw [show M.stateAcc (ciFstar M) 0 n y ω = (y, 0) from rfl]
    simp only [zero_add]
    rw [show n = M.N by omega, ciWt_N, max_eq_left hy]
  | succ k ih =>
    intro n y hn hy ω
    have hr : 0 < 1 + M.i (n + 1) := M.hi_pos _ (by omega) (by omega)
    obtain ⟨h0, h1⟩ := ciCstar_spec M hdomU n y hy
    simp only [ConsumptionInvestmentMarket.stateAcc, ciFstar, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, add_zero]
    have := ih (n + 1) ((1 + M.i (n + 1)) * (y - ciCstar M n y)) (by omega)
      (mul_nonneg hr.le (by linarith)) ω
    rw [add_assoc, this]
    exact ciCstar_value M hdomU n (by omega) y hy

lemma ciVpi_fstar (x : ℝ) (hx : 0 ≤ x) :
    M.Vpi (ciFstar M) 0 x = ((ciWt M 0 x : ℝ) : EReal) := by
  haveI := M.isProb
  unfold ConsumptionInvestmentMarket.Vpi
  have : (fun ω => (((M.stateAcc (ciFstar M) (M.N - 0) 0 x ω).2 +
      M.Up (M.stateAcc (ciFstar M) (M.N - 0) 0 x ω).1 : ℝ) : EReal)) =
      fun ω => ((fun _ => ciWt M 0 x) ω : EReal) := by
    funext ω
    rw [ciFstar_path M hdomU (M.N - 0) 0 x (by omega) hx ω]
  rw [this, ci_erealIntegral_of_integrable (integrable_const _)]
  simp

end Glue2

section Glue3

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : ConsumptionInvestmentMarket Ω d)

lemma ci_stateAcc_succ (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) : ∀ k n x ω,
    M.stateAcc π (k + 1) n x ω =
      (ciT (π (n + k)) (1 + M.i (n + k + 1)) (M.stateAcc π k n x ω).1 (M.R (n + k + 1) ω),
        (M.stateAcc π k n x ω).2 + M.Uc (π (n + k) (M.stateAcc π k n x ω).1).1) := by
  intro k
  induction k with
  | zero =>
    intro n x ω
    simp [ConsumptionInvestmentMarket.stateAcc, ciT]
  | succ k ih =>
    intro n x ω
    rw [ConsumptionInvestmentMarket.stateAcc, ih (n + 1)]
    conv_rhs => rw [ConsumptionInvestmentMarket.stateAcc]
    simp only
    have e1 : n + 1 + k = n + (k + 1) := by omega
    rw [e1]
    congr 1
    ring

end Glue3

section Glue4

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : ConsumptionInvestmentMarket Ω d)

def ciX (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (x : ℝ) (k : ℕ) (ω : Ω) : ℝ := (M.stateAcc π k 0 x ω).1

lemma ciX_succ (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (x : ℝ) (k : ℕ) (ω : Ω) :
    ciX M π x (k + 1) ω = ciT (π k) (1 + M.i (k + 1)) (ciX M π x k ω) (M.R (k + 1) ω) := by
  unfold ciX
  rw [ci_stateAcc_succ M π k 0 x ω]
  simp only [zero_add]

lemma ciAcc (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (x : ℝ) : ∀ (k : ℕ) (ω : Ω),
    (M.stateAcc π k 0 x ω).2 = ∑ j ∈ Finset.range k, M.Uc (π j (ciX M π x j ω)).1 := by
  intro k
  induction k with
  | zero => intro ω; rfl
  | succ k ih =>
    intro ω
    rw [ci_stateAcc_succ M π k 0 x ω, Finset.sum_range_succ]
    simp only [zero_add]
    rw [ih ω]; rfl

/-- the filtration generated by `R_1, …, R_k` -/
def ciF (k : ℕ) : MeasurableSpace Ω :=
  ⨆ j ∈ {j : Fin M.N | j.val < k}, MeasurableSpace.comap (fun ω => M.R (j.val + 1) ω) inferInstance

lemma ciF_mono {k k' : ℕ} (h : k ≤ k') : ciF M k ≤ ciF M k' :=
  iSup₂_le fun j hj => le_iSup₂_of_le (f := fun (j : Fin M.N) (_ : j ∈ {j : Fin M.N | j.val < k'}) =>
    MeasurableSpace.comap (fun ω => M.R (j.val + 1) ω) inferInstance) j
    (show j.val < k' from lt_of_lt_of_le hj h) le_rfl

lemma ciF_le (k : ℕ) : ciF M k ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun j _ => (M.hR_meas (j.val + 1) (by omega) (by omega)).comap_le

lemma ciR_meas_F (k : ℕ) (hk : k < M.N) : Measurable[ciF M (k + 1)] (M.R (k + 1)) := by
  have : MeasurableSpace.comap (M.R (k + 1)) inferInstance ≤ ciF M (k + 1) :=
    le_iSup₂_of_le (f := fun (j : Fin M.N) (_ : j ∈ {j : Fin M.N | j.val < k + 1}) =>
      MeasurableSpace.comap (fun ω => M.R (j.val + 1) ω) inferInstance) ⟨k, hk⟩
      (show k < k + 1 by omega) le_rfl
  exact Measurable.of_comap_le this

lemma ciX_meas (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (hπ : M.IsAdmissible 0 π) (x : ℝ) :
    ∀ k, k ≤ M.N → Measurable[ciF M k] (ciX M π x k) := by
  intro k
  induction k with
  | zero => intro _; exact measurable_const
  | succ k ih =>
    intro hk
    have h1 : Measurable[ciF M (k + 1)] (ciX M π x k) :=
      (ih (by omega)).mono (ciF_mono M (by omega)) le_rfl
    have h2 := ciR_meas_F M k (by omega)
    have hg := (hπ k (Nat.zero_le _) (by omega)).2
    have : ciX M π x (k + 1) = (fun p : ℝ × (Fin d → ℝ) => ciT (π k) (1 + M.i (k + 1)) p.1 p.2) ∘
        (fun ω => (ciX M π x k ω, M.R (k + 1) ω)) := by
      funext ω; exact ciX_succ M π x k ω
    rw [this]
    exact (ciT_meas hg _).comp (h1.prodMk h2)

lemma ciX_indep (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (hπ : M.IsAdmissible 0 π) (x : ℝ)
    (k : ℕ) (hk : k < M.N) : IndepFun (ciX M π x k) (M.R (k + 1)) M.measIP := by
  rw [IndepFun_iff_Indep]
  have hle : ∀ j : Fin M.N, MeasurableSpace.comap (fun ω => M.R (j.val + 1) ω) inferInstance ≤
      (inferInstance : MeasurableSpace Ω) :=
    fun j => (M.hR_meas (j.val + 1) (by omega) (by omega)).comap_le
  have hI := indep_iSup_of_disjoint hle M.hR_indep.iIndep
    (S := {j : Fin M.N | j.val < k}) (T := {j : Fin M.N | j.val = k}) (by
      rw [Set.disjoint_left]; intro j h1 h2; simp at h1 h2; omega)
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hI ?_) ?_
  · exact (ciX_meas M π hπ x k hk.le).comap_le
  · exact le_iSup₂_of_le (f := fun (j : Fin M.N) (_ : j ∈ {j : Fin M.N | j.val = k}) =>
      MeasurableSpace.comap (fun ω => M.R (j.val + 1) ω) inferInstance) ⟨k, hk⟩ rfl le_rfl

end Glue4

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : ConsumptionInvestmentMarket Ω d)
  (hdomU : M.domU = Set.Ici (0 : ℝ)) (hFM2 : M.FM2)
  (hR0 : ∀ n, 1 ≤ n → n ≤ M.N → ∀ k, ∫ ω, M.R n ω k ∂M.measIP = 0)
  (π : ℕ → ℝ → ℝ × (Fin d → ℝ)) (hπ : M.IsAdmissible 0 π) (x : ℝ) (hx : 0 ≤ x)
include hdomU hFM2 hR0 hπ hx

lemma ci_main : ∀ k, k ≤ M.N →
    (∀ j, j ≤ k → ∀ᵐ ω ∂M.measIP, 0 ≤ ciX M π x j ω) ∧ Integrable (ciX M π x k) M.measIP ∧
    Integrable (fun ω => ∑ j ∈ Finset.range k, ciUcl M (π j (ciX M π x j ω)).1) M.measIP ∧
    Integrable (fun ω => ciWt M k (ciX M π x k ω)) M.measIP ∧
    ∫ ω, (∑ j ∈ Finset.range k, ciUcl M (π j (ciX M π x j ω)).1 + ciWt M k (ciX M π x k ω))
      ∂M.measIP ≤ ciWt M 0 x := by
  haveI := M.isProb
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun j hj => ?_, show Integrable (fun _ => x) _ from integrable_const _, by simp,
      show Integrable (fun _ => ciWt M 0 x) _ from integrable_const _, ?_⟩
    · rw [Nat.le_zero.1 hj]; exact Filter.Eventually.of_forall (fun ω => hx)
    · simp [ciX, ConsumptionInvestmentMarket.stateAcc]
  | succ k ih =>
    intro hk1
    obtain ⟨hae, hXi, hAi, hWi, hle⟩ := ih (by omega)
    have hk : k < M.N := by omega
    have hY : Measurable (ciX M π x k) := (ciX_meas M π hπ x k hk.le).mono (ciF_le M k) le_rfl
    have hR : Measurable (M.R (k + 1)) := M.hR_meas _ (by omega) (by omega)
    have hind := ciX_indep M π hπ x k hk
    have hY0 := hae k le_rfl
    have hRi : ∀ j, Integrable (fun ω => M.R (k + 1) ω j) M.measIP := by
      intro j
      refine (hFM2 (k + 1) (by omega) (by omega)).mono'
        ((measurable_pi_apply j).comp hR).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => ?_))
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun j => |M.R (k + 1) ω j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)
    have hg := (hπ k (Nat.zero_le _) hk).2
    have hρ : 0 < 1 + M.i (k + 1) := M.hi_pos _ (by omega) (by omega)
    have hadm : ∀ y, 0 ≤ y → 0 ≤ (π k y).1 ∧ (π k y).1 ≤ y ∧
        ∀ᵐ ω ∂M.measIP, 0 ≤ ciT (π k) (1 + M.i (k + 1)) y (M.R (k + 1) ω) := by
      intro y hy
      obtain ⟨h0, h1, -, h3⟩ := (hπ k (Nat.zero_le _) hk).1 y (by rw [hdomU]; exact hy)
      refine ⟨h0, h1, h3.mono fun ω h => ?_⟩
      rw [hdomU] at h; exact h
    have hWg := ciWt_good M hdomU (k + 1)
    obtain ⟨h1, h2, h3, h4, h5⟩ := ci_one_step hY hR hind hY0 hXi hRi (hR0 (k + 1) (by omega) (by omega))
      hg hρ hadm hWg.cont hWg.conc hWg.mono
    have eX : ciX M π x (k + 1) = fun ω => ciT (π k) (1 + M.i (k + 1)) (ciX M π x k ω) (M.R (k + 1) ω) :=
      funext (ciX_succ M π x k)
    have hc_int : Integrable (fun ω => (π k (ciX M π x k ω)).1) M.measIP := by
      refine hXi.mono' (measurable_fst.comp (hg.comp hY)).aestronglyMeasurable ?_
      filter_upwards [hY0] with ω hω
      obtain ⟨a, b, -⟩ := hadm _ hω
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    have hUg := ciUcl_good M hdomU
    have hU_int : Integrable (fun ω => ciUcl M (π k (ciX M π x k ω)).1) M.measIP :=
      ci_W_integrable hUg.cont hUg.conc hUg.mono hc_int (by
        filter_upwards [hY0] with ω hω; exact (hadm _ hω).1)
    refine ⟨fun j hj => ?_, ?_, ?_, ?_, ?_⟩
    · rcases (Nat.lt_or_ge j (k + 1)) with h | h
      · exact hae j (by omega)
      · rw [show j = k + 1 by omega, eX]; exact h1
    · rw [eX]; exact h2
    · simp_rw [Finset.sum_range_succ]; exact hAi.add hU_int
    · have : (fun ω => ciWt M (k + 1) (ciX M π x (k + 1) ω)) =
          fun ω => ciWt M (k + 1) (ciT (π k) (1 + M.i (k + 1)) (ciX M π x k ω) (M.R (k + 1) ω)) := by
        funext ω; rw [ciX_succ]
      rw [this]; exact h3
    · have e1 : (fun ω => ∑ j ∈ Finset.range (k + 1), ciUcl M (π j (ciX M π x j ω)).1 +
          ciWt M (k + 1) (ciX M π x (k + 1) ω)) =
          fun ω => (∑ j ∈ Finset.range k, ciUcl M (π j (ciX M π x j ω)).1 +
            ciUcl M (π k (ciX M π x k ω)).1) +
            ciWt M (k + 1) (ciT (π k) (1 + M.i (k + 1)) (ciX M π x k ω) (M.R (k + 1) ω)) := by
        funext ω; rw [Finset.sum_range_succ, ciX_succ]
      have hAU : Integrable (fun ω => ∑ j ∈ Finset.range k, ciUcl M (π j (ciX M π x j ω)).1 +
          ciUcl M (π k (ciX M π x k ω)).1) M.measIP := hAi.add hU_int
      rw [e1, integral_add hAU h3, integral_add hAi hU_int]
      have hDP : ∫ ω, (ciUcl M (π k (ciX M π x k ω)).1 +
            ciWt M (k + 1) ((1 + M.i (k + 1)) * (ciX M π x k ω - (π k (ciX M π x k ω)).1))) ∂M.measIP
          ≤ ∫ ω, ciWt M k (ciX M π x k ω) ∂M.measIP := by
        apply integral_mono_ae (hU_int.add h4) hWi
        filter_upwards [hY0] with ω hω
        obtain ⟨a, b, -⟩ := hadm _ hω
        exact ciDP M hdomU k hk _ _ hω a b
      rw [integral_add hU_int h4] at hDP
      rw [integral_add hAi hWi] at hle
      linarith

lemma ci_upper : M.Vpi π 0 x ≤ ((ciWt M 0 x : ℝ) : EReal) := by
  haveI := M.isProb
  obtain ⟨hae, -, hAi, hWi, hle⟩ := ci_main M hdomU hFM2 hR0 π hπ x hx M.N le_rfl
  have hae_all : ∀ᵐ ω ∂M.measIP, ∀ j : ℕ, j ≤ M.N → 0 ≤ ciX M π x j ω := by
    rw [ae_all_iff]
    intro j
    by_cases hj : j ≤ M.N
    · filter_upwards [hae j hj] with ω h _ using h
    · exact Filter.Eventually.of_forall (fun ω h => absurd h hj)
  unfold ConsumptionInvestmentMarket.Vpi
  rw [Nat.sub_zero]
  have heq : (fun ω => (M.stateAcc π M.N 0 x ω).2 + M.Up (M.stateAcc π M.N 0 x ω).1) =ᵐ[M.measIP]
      fun ω => ∑ j ∈ Finset.range M.N, ciUcl M (π j (ciX M π x j ω)).1 +
        ciWt M M.N (ciX M π x M.N ω) := by
    filter_upwards [hae_all] with ω hω
    rw [ciAcc, ciWt_N, max_eq_left (hω M.N le_rfl)]
    congr 1
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjN : j < M.N := Finset.mem_range.1 hj
    have := ((hπ j (Nat.zero_le _) hjN).1 (ciX M π x j ω) (by rw [hdomU]; exact hω j hjN.le)).1
    simp [ciUcl, max_eq_left this]
  have hAW : Integrable (fun ω => ∑ j ∈ Finset.range M.N, ciUcl M (π j (ciX M π x j ω)).1 +
        ciWt M M.N (ciX M π x M.N ω)) M.measIP := hAi.add hWi
  rw [ci_erealIntegral_congr heq, ci_erealIntegral_of_integrable hAW]
  exact EReal.coe_le_coe_iff.2 hle

end Main

theorem zero_mean_invest_in_bond_ci_core {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : ConsumptionInvestmentMarket Ω d) (hdomU : M.domU = Set.Ici (0 : ℝ)) (hFM2 : M.FM2)
    (hR_zero_mean : ∀ n, 1 ≤ n → n ≤ M.N → ∀ k, ∫ ω, M.R n ω k ∂M.measIP = 0) :
    ∃ fstar : ℕ → ℝ → ℝ × (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
      (∀ n < M.N, ∀ x, (fstar n x).2 = 0) ∧
      ∀ x ∈ M.domU, M.Vpi fstar 0 x = M.V 0 x := by
  refine ⟨ciFstar M, ciFstar_adm M hdomU, fun n _ x => rfl, fun x hx => ?_⟩
  rw [hdomU] at hx
  have hx' : 0 ≤ x := hx
  rw [ciVpi_fstar M hdomU x hx']
  apply le_antisymm
  · rw [← ciVpi_fstar M hdomU x hx']
    exact le_iSup₂ (f := fun π (_ : π ∈ {π : ℕ → ℝ → ℝ × (Fin d → ℝ) | M.IsAdmissible 0 π}) =>
      M.Vpi π 0 x) (ciFstar M) (ciFstar_adm M hdomU)
  · exact iSup₂_le fun π hπ => ci_upper M hdomU hFM2 hR_zero_mean π hπ x hx'

end MDPFinance.ConsumptionInvestment

open MDPFinance.ConsumptionInvestment


theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : ConsumptionInvestmentMarket Ω d) (hdomU : M.domU = Set.Ici (0 : ℝ)) (hFM2 : M.FM2)
    (hR_zero_mean : ∀ n, 1 ≤ n → n ≤ M.N → ∀ k, ∫ ω, M.R n ω k ∂M.measIP = 0) :
    ∃ fstar : ℕ → ℝ → ℝ × (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
      (∀ n < M.N, ∀ x, (fstar n x).2 = 0) ∧
      ∀ x ∈ M.domU, M.Vpi fstar 0 x = M.V 0 x := by
  exact zero_mean_invest_in_bond_ci_core M hdomU hFM2 hR_zero_mean
