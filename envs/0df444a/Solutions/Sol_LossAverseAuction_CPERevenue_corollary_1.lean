-- Prove2me | solution 1 for LossAverseAuction.CPERevenue.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T00:46:39.040497+00:00
-- url     : https://prove2.me/submissions/66b18f21-68db-4f06-858b-9539e50d2758

import Mathlib
import Definitions.Def_LossAverseAuction_CPERevenue_Model

set_option autoImplicit false

namespace LossAverseAuction.CPERevenue.Cor1Aux

open MeasureTheory LossAverseAuction.CPERevenue

lemma gainLoss_eq (η lam x : ℝ) : gainLoss η lam x = η * x + η * (lam - 1) * min x 0 := by
  unfold gainLoss
  split_ifs with h
  · rw [min_eq_right h]; ring
  · rw [min_eq_left (le_of_lt (not_le.mp h))]; ring

lemma continuous_gainLoss (η lam : ℝ) : Continuous (gainLoss η lam) := by
  have : gainLoss η lam = fun x => η * x + η * (lam - 1) * min x 0 := funext (gainLoss_eq η lam)
  rw [this]
  exact (continuous_const.mul continuous_id).add (continuous_const.mul (continuous_id.min continuous_const))

variable {m : ℕ}

lemma signal_prob (E : Env m) (hS : E.Standing) : IsProbabilityMeasure E.signalLaw := by
  obtain ⟨⟨h0, hlt, hfc, hfpos, hint, -⟩, -⟩ := hS
  constructor
  have hfi : IntegrableOn E.f (Set.Icc E.tl E.th) := hfc.integrableOn_compact isCompact_Icc
  show ((volume.restrict (Set.Icc E.tl E.th)).withDensity
    (fun x => ENNReal.ofReal (E.f x))) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hfi
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun x hx => (hfpos x hx).le))]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlt.le]
  rw [show (∫ x in E.tl..E.th, E.f x) = 1 from hint]
  simp

lemma signal_ae_mem (E : Env m) : ∀ᵐ x ∂E.signalLaw, x ∈ Set.Icc E.tl E.th :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)

lemma signal_le (E : Env m) (hS : E.Standing) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a b : ℝ, a ≤ b → E.signalLaw.real (Set.Ico a b) ≤ M * (b - a) := by
  obtain ⟨⟨h0, hlt, hfc, hfpos, hint, -⟩, -⟩ := hS
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  refine ⟨max C 0, le_max_right _ _, fun a b hab => ?_⟩
  have hle : E.signalLaw (Set.Ico a b) ≤ ENNReal.ofReal (max C 0) * ENNReal.ofReal (b - a) := by
    show ((volume.restrict (Set.Icc E.tl E.th)).withDensity
      (fun x => ENNReal.ofReal (E.f x))) (Set.Ico a b) ≤ _
    rw [withDensity_apply _ measurableSet_Ico]
    calc ∫⁻ x in Set.Ico a b, ENNReal.ofReal (E.f x) ∂(volume.restrict (Set.Icc E.tl E.th))
        ≤ ∫⁻ x in Set.Ico a b, ENNReal.ofReal (max C 0) ∂(volume.restrict (Set.Icc E.tl E.th)) := by
          rw [Measure.restrict_restrict measurableSet_Ico]
          apply setLIntegral_mono measurable_const
          intro x hx
          apply ENNReal.ofReal_le_ofReal
          have := hC x hx.2
          exact le_trans (le_abs_self _) (le_trans (by simpa [Real.norm_eq_abs] using this) (le_max_left _ _))
      _ = ENNReal.ofReal (max C 0) * (volume.restrict (Set.Icc E.tl E.th)) (Set.Ico a b) := by
          rw [setLIntegral_const]
      _ ≤ ENNReal.ofReal (max C 0) * ENNReal.ofReal (b - a) := by
          gcongr
          calc (volume.restrict (Set.Icc E.tl E.th)) (Set.Ico a b) ≤ volume (Set.Ico a b) :=
                Measure.restrict_apply_le _ _
            _ = ENNReal.ofReal (b - a) := Real.volume_Ico
  have hrhs : ENNReal.ofReal (max C 0) * ENNReal.ofReal (b - a) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  calc E.signalLaw.real (Set.Ico a b) = (E.signalLaw (Set.Ico a b)).toReal := rfl
    _ ≤ (ENNReal.ofReal (max C 0) * ENNReal.ofReal (b - a)).toReal := ENNReal.toReal_mono hrhs hle
    _ = max C 0 * (b - a) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_max_right _ _),
        ENNReal.toReal_ofReal (sub_nonneg.2 hab)]

lemma abs_gainLoss_le {η lam : ℝ} (hη : 0 ≤ η) (hl : 1 ≤ lam) (u : ℝ) :
    |gainLoss η lam u| ≤ η * lam * |u| := by
  unfold gainLoss
  split_ifs with h
  · rw [abs_mul, abs_of_nonneg hη]
    have := mul_nonneg (mul_nonneg hη (abs_nonneg u)) (sub_nonneg.2 hl)
    nlinarith
  · rw [abs_mul, abs_mul, abs_of_nonneg hη, abs_of_nonneg (by linarith : (0:ℝ) ≤ lam)]

lemma gainLoss_lip {η lam : ℝ} (hη : 0 ≤ η) (hl : 1 ≤ lam) (u u' : ℝ) :
    |gainLoss η lam u - gainLoss η lam u'| ≤ η * lam * |u - u'| := by
  rw [gainLoss_eq, gainLoss_eq]
  have h1 : |min u 0 - min u' 0| ≤ |u - u'| :=
    (abs_min_sub_min_le_max u 0 u' 0).trans (by simp)
  have e : η * u + η * (lam - 1) * min u 0 - (η * u' + η * (lam - 1) * min u' 0)
      = η * (u - u') + (η * (lam - 1)) * (min u 0 - min u' 0) := by ring
  rw [e]
  have hc : 0 ≤ η * (lam - 1) := mul_nonneg hη (by linarith)
  calc _ ≤ |η * (u - u')| + |(η * (lam - 1)) * (min u 0 - min u' 0)| := abs_add_le _ _
    _ = η * |u - u'| + (η * (lam - 1)) * |min u 0 - min u' 0| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hη, abs_of_nonneg hc]
    _ ≤ η * |u - u'| + (η * (lam - 1)) * |u - u'| := by gcongr
    _ = η * lam * |u - u'| := by ring

variable (E : Env m)

lemma opp_def : E.oppLaw = Measure.pi (fun _ : Fin (m+1) => E.signalLaw) := rfl

lemma opp_prob (hS : E.Standing) : IsProbabilityMeasure E.oppLaw := by
  haveI := signal_prob E hS
  rw [opp_def]; infer_instance

lemma opp_ae_mem (hS : E.Standing) : ∀ᵐ s ∂E.oppLaw, ∀ j, s j ∈ Set.Icc E.tl E.th := by
  haveI := signal_prob E hS
  rw [opp_def]
  exact ae_all_iff.2 fun j =>
    (measurePreserving_eval (fun _ : Fin (m+1) => E.signalLaw) j).quasiMeasurePreserving.ae
      (signal_ae_mem E)

lemma opp_coord (hS : E.Standing) (j : Fin (m+1)) {S : Set ℝ} (hSm : MeasurableSet S) :
    E.oppLaw.real {s | s j ∈ S} = E.signalLaw.real S := by
  haveI := signal_prob E hS
  rw [opp_def]
  simp only [Measure.real]
  rw [show {s : Fin (m+1) → ℝ | s j ∈ S} = Function.eval j ⁻¹' S from rfl,
    (measurePreserving_eval (fun _ : Fin (m+1) => E.signalLaw) j).measure_preimage
      hSm.nullMeasurableSet]

lemma opp_box (hS : E.Standing) (S : Set ℝ) :
    E.oppLaw {s | ∀ j, s j ∈ S} = E.signalLaw S ^ (m+1) := by
  haveI := signal_prob E hS
  rw [opp_def, show {s : Fin (m+1) → ℝ | ∀ j, s j ∈ S} = Set.univ.pi (fun _ => S) by ext; simp,
    Measure.pi_pi]
  simp

lemma win_ae (hS : E.Standing) {β : ℝ → ℝ} (hβ : StrictMonoOn β (Set.Icc E.tl E.th)) {x : ℝ}
    (hx : x ∈ Set.Icc E.tl E.th) :
    ∀ᵐ s ∂E.oppLaw, ((∀ j, β (s j) < β x) ↔ (∀ j, s j < x)) := by
  filter_upwards [opp_ae_mem E hS] with s hs
  exact forall_congr' fun j => hβ.lt_iff_lt (hs j) hx

lemma int2 {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (F : ℝ → ℝ → ℝ) (hF : Continuous (fun q : ℝ × ℝ => F q.1 q.2)) (L : ℝ) (hL : 0 ≤ L)
    (hFb : ∀ a c, |F a c| ≤ L * (|a| + |c|)) (g : Ω → ℝ) (hg : Measurable g) (B : ℝ)
    (hgb : ∀ᵐ s ∂ν, |g s| ≤ B) :
    Integrable (fun p : Ω × Ω => F (g p.1) (g p.2)) (ν.prod ν) := by
  refine Integrable.of_bound ?_ (L * (B + B)) ?_
  · exact (hF.measurable.comp ((hg.comp measurable_fst).prodMk
      (hg.comp measurable_snd))).aestronglyMeasurable
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hgb,
      Measure.quasiMeasurePreserving_snd.ae hgb] with p h1 h2
    rw [Real.norm_eq_abs]
    calc |F (g p.1) (g p.2)| ≤ L * (|g p.1| + |g p.2|) := hFb _ _
      _ ≤ L * (B + B) := by gcongr

lemma EU_map {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (g : Ω → ℝ × ℝ) (hg : Measurable g)
    (hint : Integrable (fun p : Ω × Ω => E.U (g p.1) (g p.2)) (ν.prod ν)) :
    E.EU (ν.map g) (ν.map g) = ∫ p, E.U (g p.1) (g p.2) ∂(ν.prod ν) := by
  have hUc : Continuous (fun q : (ℝ × ℝ) × (ℝ × ℝ) => E.U q.1 q.2) := by
    unfold Env.U
    exact (((continuous_fst.fst.sub continuous_fst.snd).add ((continuous_gainLoss _ _).comp
      (continuous_fst.fst.sub continuous_snd.fst))).add ((continuous_gainLoss _ _).comp
      (continuous_snd.snd.sub continuous_fst.snd)))
  have hinner : StronglyMeasurable (fun o : ℝ × ℝ => ∫ r, E.U o r ∂(ν.map g)) :=
    StronglyMeasurable.integral_prod_right (f := fun o r => E.U o r) hUc.stronglyMeasurable
  unfold Env.EU
  rw [integral_map hg.aemeasurable hinner.aestronglyMeasurable, integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  show ∫ r, E.U (g s) r ∂(ν.map g) = ∫ y, E.U (g s) (g y) ∂ν
  have hm : AEStronglyMeasurable (fun r => E.U (g s) r) (ν.map g) :=
    ((hUc.comp (Continuous.prodMk (continuous_const (y := g s)) continuous_id) :
      Continuous fun r => E.U (g s) r)).aestronglyMeasurable
  rw [integral_map hg.aemeasurable hm]

noncomputable def payv (k : Format) (β : ℝ → ℝ) (b : ℝ) (s : Fin (m+1) → ℝ) : ℝ :=
  match k with
  | .FPA => b
  | .SPA => Finset.univ.sup' Finset.univ_nonempty (fun j => β (s j))

lemma outcome_fst (k : Format) (β : ℝ → ℝ) (b t : ℝ) (s : Fin (m+1) → ℝ) :
    (E.outcome k β b t s).1 = if ∀ j, β (s j) < b then E.v t s else 0 := by
  unfold Env.outcome; split_ifs <;> rfl

lemma outcome_snd (k : Format) (β : ℝ → ℝ) (b t : ℝ) (s : Fin (m+1) → ℝ) :
    (E.outcome k β b t s).2 = if ∀ j, β (s j) < b then payv k β b s else 0 := by
  unfold Env.outcome; split_ifs <;> cases k <;> rfl

lemma meas_payv (k : Format) {β : ℝ → ℝ} (hβ : Measurable β) (b : ℝ) :
    Measurable (payv (m := m) k β b) := by
  cases k
  · exact measurable_const
  · show Measurable (fun s : Fin (m+1) → ℝ => Finset.univ.sup' Finset.univ_nonempty (fun j => β (s j)))
    have := Finset.measurable_sup' (Finset.univ_nonempty (α := Fin (m+1)))
      (f := fun j (s : Fin (m+1) → ℝ) => β (s j)) (fun j _ => hβ.comp (measurable_pi_apply j))
    convert this using 1
    ext s; rw [Finset.sup'_apply]

lemma meas_win {β : ℝ → ℝ} (hβ : Measurable β) (b : ℝ) :
    MeasurableSet {s : Fin (m+1) → ℝ | ∀ j, β (s j) < b} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j =>
    measurableSet_lt (hβ.comp (measurable_pi_apply j)) measurable_const

lemma meas_outcome (hS : E.Standing) (k : Format) {β : ℝ → ℝ} (hβ : Measurable β) (b t : ℝ) :
    Measurable (E.outcome k β b t) := by
  obtain ⟨⟨-, -, -, -, -, hvm, -⟩, -⟩ := hS
  have h1 : Measurable (fun s => (E.outcome k β b t s).1) := by
    simp_rw [outcome_fst]
    exact Measurable.ite (meas_win hβ b) (hvm.comp (measurable_const.prodMk measurable_id))
      measurable_const
  have h2 : Measurable (fun s => (E.outcome k β b t s).2) := by
    simp_rw [outcome_snd]
    exact Measurable.ite (meas_win hβ b) (meas_payv k hβ b) measurable_const
  exact h1.prodMk h2

lemma v_bounds (hS : E.Standing) : ∃ V L : ℝ, 0 ≤ V ∧ 0 ≤ L ∧
    (∀ t ∈ Set.Icc E.tl E.th, ∀ s : Fin (m+1) → ℝ, (∀ j, s j ∈ Set.Icc E.tl E.th) →
      |E.v t s| ≤ V) ∧
    (∀ t ∈ Set.Icc E.tl E.th, ∀ x ∈ Set.Icc E.tl E.th, ∀ s : Fin (m+1) → ℝ,
      (∀ j, s j ∈ Set.Icc E.tl E.th) → |E.v t s - E.v x s| ≤ L * |t - x|) := by
  obtain ⟨⟨h0, hlt, -, -, -, -, -, -, -, hcd, -⟩, -⟩ := hS
  set S : Set (ℝ × (Fin (m+1) → ℝ)) :=
    Set.Icc E.tl E.th ×ˢ Set.univ.pi (fun _ => Set.Icc E.tl E.th) with hSdef
  have hSsub : S ⊆ Set.Ici 0 ×ˢ {s | ∀ j, 0 ≤ s j} := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    exact ⟨le_trans h0 ht.1, fun j => le_trans h0 (hs j (Set.mem_univ _)).1⟩
  have hcomp : IsCompact S := isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hconv : Convex ℝ S := (convex_Icc _ _).prod (convex_pi fun _ _ => convex_Icc _ _)
  have hcd' := hcd.mono hSsub
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcd'.continuousOn
  obtain ⟨K, hK⟩ := hcd'.exists_lipschitzOnWith (by simp) hconv hcomp
  refine ⟨max C 0, K, le_max_right _ _, K.coe_nonneg, ?_, ?_⟩
  · intro t ht s hs
    have := hC (t, s) ⟨ht, fun j _ => hs j⟩
    rw [Real.norm_eq_abs] at this
    exact le_trans this (le_max_left _ _)
  · intro t ht x hx s hs
    have := hK.dist_le_mul (t, s) ⟨ht, fun j _ => hs j⟩ (x, s) ⟨hx, fun j _ => hs j⟩
    have hd : dist (t, s) (x, s) = |t - x| := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]; exact max_eq_left (abs_nonneg _)
    rw [hd, Real.dist_eq] at this; exact this

noncomputable def Xv (x t : ℝ) (s : Fin (m+1) → ℝ) : ℝ := if ∀ j, s j < x then E.v t s else 0
noncomputable def itemF (a c : ℝ) : ℝ := a + gainLoss E.etag E.lamg (a - c)
noncomputable def moneyF (y1 y2 : ℝ) : ℝ := -y1 + gainLoss E.etam E.lamm (y2 - y1)
noncomputable def Wt (x t : ℝ) : ℝ :=
  ∫ p, itemF E (Xv E x t p.1) (Xv E x t p.2) ∂(E.oppLaw.prod E.oppLaw)
noncomputable def Yv (k : Format) (β : ℝ → ℝ) (b : ℝ) (s : Fin (m+1) → ℝ) : ℝ :=
  if ∀ j, β (s j) < b then payv k β b s else 0
noncomputable def Cm (k : Format) (β : ℝ → ℝ) (x : ℝ) : ℝ :=
  - ∫ p, moneyF E (Yv k β (β x) p.1) (Yv k β (β x) p.2) ∂(E.oppLaw.prod E.oppLaw)

lemma U_split (o r : ℝ × ℝ) : E.U o r = itemF E o.1 r.1 + moneyF E o.2 r.2 := by
  unfold Env.U itemF moneyF; ring

lemma gainLoss_zero (η lam : ℝ) : gainLoss η lam 0 = 0 := by unfold gainLoss; simp

lemma itemF_lip (hη : 0 ≤ E.etag) (hl : 1 ≤ E.lamg) (a c a' c' : ℝ) :
    |itemF E a c - itemF E a' c'| ≤ (1 + E.etag * E.lamg) * (|a - a'| + |c - c'|) := by
  unfold itemF
  have h1 := gainLoss_lip hη hl (a - c) (a' - c')
  have h2 : |(a - c) - (a' - c')| ≤ |a - a'| + |c - c'| := by
    rw [show (a - c) - (a' - c') = (a - a') + -(c - c') by ring]
    exact (abs_add_le _ _).trans (by rw [abs_neg])
  have h3 : |a + gainLoss E.etag E.lamg (a - c) - (a' + gainLoss E.etag E.lamg (a' - c'))| ≤
      |a - a'| + |gainLoss E.etag E.lamg (a - c) - gainLoss E.etag E.lamg (a' - c')| := by
    rw [show a + gainLoss E.etag E.lamg (a - c) - (a' + gainLoss E.etag E.lamg (a' - c')) =
      (a - a') + (gainLoss E.etag E.lamg (a - c) - gainLoss E.etag E.lamg (a' - c')) by ring]
    exact abs_add_le _ _
  have hp : 0 ≤ E.etag * E.lamg := mul_nonneg hη (by linarith)
  have h4 := mul_le_mul_of_nonneg_left h2 hp
  nlinarith [abs_nonneg (a - a'), abs_nonneg (c - c')]

lemma moneyF_lip (hη : 0 ≤ E.etam) (hl : 1 ≤ E.lamm) (a c a' c' : ℝ) :
    |moneyF E a c - moneyF E a' c'| ≤ (1 + E.etam * E.lamm) * (|a - a'| + |c - c'|) := by
  unfold moneyF
  have h1 := gainLoss_lip hη hl (c - a) (c' - a')
  have h2 : |(c - a) - (c' - a')| ≤ |a - a'| + |c - c'| := by
    rw [show (c - a) - (c' - a') = (c - c') + -(a - a') by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]; linarith
  have h3 : |-a + gainLoss E.etam E.lamm (c - a) - (-a' + gainLoss E.etam E.lamm (c' - a'))| ≤
      |a - a'| + |gainLoss E.etam E.lamm (c - a) - gainLoss E.etam E.lamm (c' - a')| := by
    rw [show -a + gainLoss E.etam E.lamm (c - a) - (-a' + gainLoss E.etam E.lamm (c' - a')) =
      -(a - a') + (gainLoss E.etam E.lamm (c - a) - gainLoss E.etam E.lamm (c' - a')) by ring]
    exact (abs_add_le _ _).trans (by rw [abs_neg])
  have hp : 0 ≤ E.etam * E.lamm := mul_nonneg hη (by linarith)
  have h4 := mul_le_mul_of_nonneg_left h2 hp
  nlinarith [abs_nonneg (a - a'), abs_nonneg (c - c')]

lemma itemF_cont : Continuous (fun q : ℝ × ℝ => itemF E q.1 q.2) := by
  unfold itemF
  exact continuous_fst.add ((continuous_gainLoss _ _).comp (continuous_fst.sub continuous_snd))

lemma moneyF_cont : Continuous (fun q : ℝ × ℝ => moneyF E q.1 q.2) := by
  unfold moneyF
  exact continuous_fst.neg.add ((continuous_gainLoss _ _).comp (continuous_snd.sub continuous_fst))

lemma itemF_bd (hη : 0 ≤ E.etag) (hl : 1 ≤ E.lamg) (a c : ℝ) :
    |itemF E a c| ≤ (1 + E.etag * E.lamg) * (|a| + |c|) := by
  have := itemF_lip E hη hl a c 0 0
  have h0 : itemF E 0 0 = 0 := by unfold itemF; simp [gainLoss_zero]
  simpa [h0] using this

lemma moneyF_bd (hη : 0 ≤ E.etam) (hl : 1 ≤ E.lamm) (a c : ℝ) :
    |moneyF E a c| ≤ (1 + E.etam * E.lamm) * (|a| + |c|) := by
  have := moneyF_lip E hη hl a c 0 0
  have h0 : moneyF E 0 0 = 0 := by unfold moneyF; simp [gainLoss_zero]
  simpa [h0] using this

lemma payv_bounds {k : Format} {β : ℝ → ℝ} (hβs : StrictMonoOn β (Set.Icc E.tl E.th))
    (hβnn : ∀ t ∈ Set.Icc E.tl E.th, 0 ≤ β t) {x : ℝ} (hx : x ∈ Set.Icc E.tl E.th)
    {s : Fin (m+1) → ℝ} (hs : ∀ j, s j ∈ Set.Icc E.tl E.th) :
    0 ≤ payv k β (β x) s ∧ payv k β (β x) s ≤ β E.th := by
  have hth : E.th ∈ Set.Icc E.tl E.th := ⟨hx.1.trans hx.2, le_rfl⟩
  cases k
  · exact ⟨hβnn x hx, hβs.monotoneOn hx hth hx.2⟩
  · refine ⟨?_, ?_⟩
    · show 0 ≤ Finset.univ.sup' Finset.univ_nonempty (fun j => β (s j))
      exact le_trans (hβnn (s 0) (hs 0)) (Finset.le_sup' (fun j => β (s j)) (Finset.mem_univ 0))
    · show Finset.univ.sup' Finset.univ_nonempty (fun j => β (s j)) ≤ β E.th
      exact Finset.sup'_le _ _ (fun j _ => hβs.monotoneOn (hs j) hth (hs j).2)

lemma Xv_meas (hS : E.Standing) (x t : ℝ) : Measurable (Xv E x t) := by
  obtain ⟨⟨-, -, -, -, -, hvm, -⟩, -⟩ := hS
  unfold Xv
  refine Measurable.ite ?_ (hvm.comp (measurable_const.prodMk measurable_id)) measurable_const
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j => measurableSet_lt (measurable_pi_apply j) measurable_const

lemma Xv_int (hS : E.Standing) {x t : ℝ} (ht : t ∈ Set.Icc E.tl E.th) :
    Integrable (fun p => itemF E (Xv E x t p.1) (Xv E x t p.2)) (E.oppLaw.prod E.oppLaw) := by
  haveI := opp_prob E hS
  obtain ⟨V, L, hV0, hL0, hV, hL⟩ := v_bounds E hS
  refine int2 _ (itemF E) (itemF_cont E) _ (by have := hS.2.1; have := hS.2.2.1; positivity)
    (itemF_bd E hS.2.1 hS.2.2.1.le) _ (Xv_meas E hS x t) V ?_
  filter_upwards [opp_ae_mem E hS] with s hs
  unfold Xv; split_ifs
  · exact hV t ht s hs
  · simpa using hV0

lemma EU_decomp (hS : E.Standing) (k : Format) {β : ℝ → ℝ} (hβm : Measurable β)
    (hβs : StrictMonoOn β (Set.Icc E.tl E.th)) (hβnn : ∀ t ∈ Set.Icc E.tl E.th, 0 ≤ β t)
    {x t : ℝ} (hx : x ∈ Set.Icc E.tl E.th) (ht : t ∈ Set.Icc E.tl E.th) :
    E.EU (E.Γ k β (β x) t) (E.Γ k β (β x) t) = Wt E x t - Cm E k β x := by
  haveI := opp_prob E hS
  obtain ⟨V, L, hV0, hL0, hV, hL⟩ := v_bounds E hS
  have hout := meas_outcome E hS k hβm (β x) t
  have hI : Integrable (fun p => itemF E (E.outcome k β (β x) t p.1).1
      (E.outcome k β (β x) t p.2).1) (E.oppLaw.prod E.oppLaw) := by
    refine int2 _ (itemF E) (itemF_cont E) _ (by have := hS.2.1; have := hS.2.2.1; positivity)
      (itemF_bd E hS.2.1 hS.2.2.1.le) (fun s => (E.outcome k β (β x) t s).1) hout.fst V ?_
    filter_upwards [opp_ae_mem E hS] with s hs
    rw [outcome_fst]; split_ifs
    · exact hV t ht s hs
    · simpa using hV0
  have hM : Integrable (fun p => moneyF E (E.outcome k β (β x) t p.1).2
      (E.outcome k β (β x) t p.2).2) (E.oppLaw.prod E.oppLaw) := by
    refine int2 _ (moneyF E) (moneyF_cont E) _ (by have := hS.2.2.2.1; have := hS.2.2.2.2; positivity)
      (moneyF_bd E hS.2.2.2.1 hS.2.2.2.2.le) (fun s => (E.outcome k β (β x) t s).2) hout.snd
      (β E.th) ?_
    filter_upwards [opp_ae_mem E hS] with s hs
    rw [outcome_snd]; split_ifs
    · have := payv_bounds E (k := k) hβs hβnn hx hs
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    · simpa using le_trans (hβnn x hx) (hβs.monotoneOn hx ⟨hx.1.trans hx.2, le_rfl⟩ hx.2)
  have hU : Integrable (fun p => E.U (E.outcome k β (β x) t p.1) (E.outcome k β (β x) t p.2))
      (E.oppLaw.prod E.oppLaw) :=
    (hI.add hM).congr (Filter.Eventually.of_forall fun p => (U_split E _ _).symm)
  rw [show E.Γ k β (β x) t = E.oppLaw.map (E.outcome k β (β x) t) from rfl,
    EU_map E _ _ hout hU,
    integral_congr_ae (Filter.Eventually.of_forall fun p => U_split E _ _), integral_add hI hM]
  unfold Wt Cm
  rw [sub_neg_eq_add]
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (win_ae E hS hβs hx),
      Measure.quasiMeasurePreserving_snd.ae (win_ae E hS hβs hx)] with p h1 h2
    show itemF E (E.outcome k β (β x) t p.1).1 (E.outcome k β (β x) t p.2).1 =
      itemF E (Xv E x t p.1) (Xv E x t p.2)
    rw [outcome_fst, outcome_fst, if_congr h1 rfl rfl, if_congr h2 rfl rfl]
    rfl
  · refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show moneyF E (E.outcome k β (β x) t p.1).2 (E.outcome k β (β x) t p.2).2 =
      moneyF E (Yv k β (β x) p.1) (Yv k β (β x) p.2)
    rw [outcome_snd, outcome_snd]
    rfl

lemma IC_ineq (hS : E.Standing) {k : Format} {β : ℝ → ℝ} (hβ : E.IsSymCPE k β)
    {x t : ℝ} (hx : x ∈ Set.Icc E.tl E.th) (ht : t ∈ Set.Icc E.tl E.th) :
    Wt E x t - Cm E k β x ≤ Wt E t t - Cm E k β t := by
  obtain ⟨hβm, hβs, hβnn, hic⟩ := hβ
  have := hic t ht (β x) (hβnn x hx)
  rwa [EU_decomp E hS k hβm hβs hβnn hx ht, EU_decomp E hS k hβm hβs hβnn ht ht] at this

lemma alg4 (F : ℝ → ℝ → ℝ) (Li : ℝ) (hLi : 0 ≤ Li)
    (hF : ∀ a c a' c', |F a c - F a' c'| ≤ Li * (|a - a'| + |c - c'|))
    (a1 a2 a3 a4 c1 c2 c3 c4 d : ℝ) (h13 : |a1 - a3| ≤ d) (h24 : |a2 - a4| ≤ d)
    (hc13 : |c1 - c3| ≤ d) (hc24 : |c2 - c4| ≤ d) :
    F a1 c1 - F a2 c2 - F a3 c3 + F a4 c4 ≤ 4 * Li * d := by
  have e1 := hF a1 c1 a3 c3
  have e2 := hF a2 c2 a4 c4
  have f1 := le_abs_self (F a1 c1 - F a3 c3)
  have f2 := neg_abs_le (F a2 c2 - F a4 c4)
  have g1 : Li * (|a1 - a3| + |c1 - c3|) ≤ Li * (d + d) := by gcongr
  have g2 : Li * (|a2 - a4| + |c2 - c4|) ≤ Li * (d + d) := by gcongr
  nlinarith

lemma const_of_sq (D : ℝ → ℝ) (a b K : ℝ) (hK : 0 ≤ K)
    (h : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, y ≤ x → |D x - D y| ≤ K * (x - y) ^ 2) :
    ∀ x ∈ Set.Icc a b, D x = D a := by
  intro x hx
  have hxa : 0 ≤ x - a := by linarith [hx.1]
  have key : ∀ n : ℕ, |D x - D a| ≤ K * (x - a) ^ 2 / (n + 1) := by
    intro n
    set hh := (x - a) / (n + 1) with hhdef
    have hn1 : (0:ℝ) < n + 1 := by positivity
    have hh0 : 0 ≤ hh := div_nonneg hxa hn1.le
    have hnh : ((n:ℝ) + 1) * hh = x - a := by rw [hhdef]; field_simp
    have hmem : ∀ i : ℕ, i ≤ n + 1 → a + i * hh ∈ Set.Icc a b := by
      intro i hi
      constructor
      · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hh0)
      · have : (i:ℝ) * hh ≤ ((n:ℝ) + 1) * hh := by
          gcongr; exact_mod_cast hi
        linarith [hx.2]
    have ind : ∀ i : ℕ, i ≤ n + 1 → |D (a + i * hh) - D a| ≤ i * (K * hh ^ 2) := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ i ih =>
        intro hi
        have h1 := ih (by omega)
        have h2 := h (a + ((i+1:ℕ):ℝ) * hh) (hmem (i+1) hi) (a + i * hh) (hmem i (by omega))
          (by push_cast; nlinarith [hh0])
        have e : a + ((i+1 : ℕ) : ℝ) * hh - (a + i * hh) = hh := by push_cast; ring
        rw [e] at h2
        calc |D (a + ((i+1:ℕ):ℝ) * hh) - D a|
            ≤ |D (a + ((i+1:ℕ):ℝ) * hh) - D (a + i * hh)| + |D (a + i * hh) - D a| :=
              abs_sub_le _ _ _
          _ ≤ K * hh ^ 2 + i * (K * hh ^ 2) := add_le_add h2 h1
          _ = ((i+1:ℕ):ℝ) * (K * hh ^ 2) := by push_cast; ring
    have := ind (n+1) le_rfl
    have e2 : a + ((n+1:ℕ):ℝ) * hh = x := by push_cast; linarith [hnh]
    rw [e2] at this
    calc |D x - D a| ≤ ((n+1:ℕ):ℝ) * (K * hh ^ 2) := this
      _ = K * (x - a) ^ 2 / (n + 1) := by
        rw [← hnh]; push_cast; field_simp
  by_contra hne
  have hpos : 0 < |D x - D a| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (K * (x - a) ^ 2 / |D x - D a|)
  have h4 := key n
  rw [div_lt_iff₀ hpos] at hn
  rw [le_div_iff₀ (by positivity)] at h4
  have : (n:ℝ) * |D x - D a| < |D x - D a| * (n + 1) := by nlinarith
  nlinarith

lemma Xv_eq_of_not_bad {x t : ℝ} (hxt : x ≤ t) {s : Fin (m+1) → ℝ}
    (hs : s ∉ ⋃ j, {s : Fin (m+1) → ℝ | s j ∈ Set.Ico x t}) (τ : ℝ) :
    Xv E t τ s = Xv E x τ s := by
  unfold Xv
  refine if_congr ⟨fun h j => ?_, fun h j => lt_of_lt_of_le (h j) hxt⟩ rfl rfl
  by_contra hc
  exact hs (Set.mem_iUnion.2 ⟨j, ⟨not_lt.1 hc, h j⟩⟩)

lemma Xv_lip {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ t ∈ Set.Icc E.tl E.th, ∀ x ∈ Set.Icc E.tl E.th, ∀ s : Fin (m+1) → ℝ,
      (∀ j, s j ∈ Set.Icc E.tl E.th) → |E.v t s - E.v x s| ≤ L * |t - x|)
    (a : ℝ) {t x : ℝ} (ht : t ∈ Set.Icc E.tl E.th) (hx : x ∈ Set.Icc E.tl E.th)
    {s : Fin (m+1) → ℝ} (hs : ∀ j, s j ∈ Set.Icc E.tl E.th) :
    |Xv E a t s - Xv E a x s| ≤ L * |t - x| := by
  unfold Xv; split_ifs
  · exact hL t ht x hx s hs
  · simp only [sub_self, abs_zero]; exact mul_nonneg hL0 (abs_nonneg _)

lemma width (hS : E.Standing) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Set.Icc E.tl E.th,
    ∀ t ∈ Set.Icc E.tl E.th, x ≤ t → Wt E t t - Wt E x t - Wt E t x + Wt E x x ≤ K * (t - x) ^ 2 := by
  haveI := opp_prob E hS
  obtain ⟨V, L, hV0, hL0, hV, hL⟩ := v_bounds E hS
  obtain ⟨M, hM0, hM⟩ := signal_le E hS
  have hηg := hS.2.1
  have hlg := hS.2.2.1
  set Li := 1 + E.etag * E.lamg with hLidef
  have hLi : 0 ≤ Li := by
    rw [hLidef]; have := mul_nonneg hηg (by linarith : (0:ℝ) ≤ E.lamg); linarith
  refine ⟨8 * Li * L * (m+1) * M, by positivity, ?_⟩
  intro x hx t ht hxt
  set Bad : Set (Fin (m+1) → ℝ) := ⋃ j, {s : Fin (m+1) → ℝ | s j ∈ Set.Ico x t} with hBad
  have hBm : MeasurableSet Bad :=
    MeasurableSet.iUnion fun j => (measurable_pi_apply j) measurableSet_Ico
  have hνB : E.oppLaw.real Bad ≤ (m+1) * (M * (t - x)) := by
    calc E.oppLaw.real Bad
        ≤ ∑ j : Fin (m+1), E.oppLaw.real {s : Fin (m+1) → ℝ | s j ∈ Set.Ico x t} :=
          measureReal_iUnion_fintype_le _
      _ = ∑ j : Fin (m+1), E.signalLaw.real (Set.Ico x t) :=
          Finset.sum_congr rfl fun j _ => opp_coord E hS j measurableSet_Ico
      _ ≤ ∑ j : Fin (m+1), M * (t - x) := Finset.sum_le_sum fun j _ => hM x t hxt
      _ = (m+1) * (M * (t - x)) := by simp
  set c := 4 * Li * (L * (t - x)) with hc
  have htx : 0 ≤ t - x := by linarith
  have hc0 : 0 ≤ c := by positivity
  have hI : ∀ a τ, τ ∈ Set.Icc E.tl E.th → Integrable
      (fun p => itemF E (Xv E a τ p.1) (Xv E a τ p.2)) (E.oppLaw.prod E.oppLaw) :=
    fun a τ hτ => Xv_int E hS (x := a) hτ
  have hi1 : Integrable (Bad.indicator (1 : (Fin (m+1) → ℝ) → ℝ)) E.oppLaw :=
    (integrable_const (1:ℝ)).indicator hBm
  have hind : Integrable (fun p : (Fin (m+1) → ℝ) × (Fin (m+1) → ℝ) =>
      c * (Bad.indicator 1 p.1 + Bad.indicator 1 p.2)) (E.oppLaw.prod E.oppLaw) :=
    Integrable.const_mul (Integrable.add (hi1.comp_fst _) (hi1.comp_snd _)) c
  have hd : ∀ a (s : Fin (m+1) → ℝ), (∀ j, s j ∈ Set.Icc E.tl E.th) →
      |Xv E a t s - Xv E a x s| ≤ L * (t - x) := by
    intro a s hs
    rw [← abs_of_nonneg htx]; exact Xv_lip E hL0 hL a ht hx hs
  have heq : (∫ p, itemF E (Xv E t t p.1) (Xv E t t p.2) ∂(E.oppLaw.prod E.oppLaw)) -
      (∫ p, itemF E (Xv E x t p.1) (Xv E x t p.2) ∂(E.oppLaw.prod E.oppLaw)) -
      (∫ p, itemF E (Xv E t x p.1) (Xv E t x p.2) ∂(E.oppLaw.prod E.oppLaw)) +
      (∫ p, itemF E (Xv E x x p.1) (Xv E x x p.2) ∂(E.oppLaw.prod E.oppLaw)) =
      ∫ p, (itemF E (Xv E t t p.1) (Xv E t t p.2) - itemF E (Xv E x t p.1) (Xv E x t p.2) -
        itemF E (Xv E t x p.1) (Xv E t x p.2) + itemF E (Xv E x x p.1) (Xv E x x p.2))
        ∂(E.oppLaw.prod E.oppLaw) := by
    rw [integral_add ?_ (hI x x hx), integral_sub ?_ (hI t x hx),
      integral_sub (hI t t ht) (hI x t ht)]
    all_goals first
      | exact ((hI t t ht).sub (hI x t ht)).sub (hI t x hx)
      | exact (hI t t ht).sub (hI x t ht)
  unfold Wt
  rw [heq]
  calc _ ≤ ∫ p, c * (Bad.indicator 1 p.1 + Bad.indicator 1 p.2) ∂(E.oppLaw.prod E.oppLaw) := by
        refine integral_mono_ae ((((hI t t ht).sub (hI x t ht)).sub (hI t x hx)).add (hI x x hx))
          hind ?_
        filter_upwards [Measure.quasiMeasurePreserving_fst.ae (opp_ae_mem E hS),
          Measure.quasiMeasurePreserving_snd.ae (opp_ae_mem E hS)] with p h1 h2
        show itemF E (Xv E t t p.1) (Xv E t t p.2) - itemF E (Xv E x t p.1) (Xv E x t p.2) -
            itemF E (Xv E t x p.1) (Xv E t x p.2) + itemF E (Xv E x x p.1) (Xv E x x p.2) ≤
            c * (Bad.indicator 1 p.1 + Bad.indicator 1 p.2)
        have hmain : itemF E (Xv E t t p.1) (Xv E t t p.2) - itemF E (Xv E x t p.1) (Xv E x t p.2) -
            itemF E (Xv E t x p.1) (Xv E t x p.2) + itemF E (Xv E x x p.1) (Xv E x x p.2) ≤ c :=
          alg4 (itemF E) Li hLi (itemF_lip E hηg hlg.le) _ _ _ _ _ _ _ _ _
            (hd t p.1 h1) (hd x p.1 h1) (hd t p.2 h2) (hd x p.2 h2)
        have hn1 : (0:ℝ) ≤ Bad.indicator 1 p.1 := Set.indicator_nonneg (fun _ _ => zero_le_one) _
        have hn2 : (0:ℝ) ≤ Bad.indicator 1 p.2 := Set.indicator_nonneg (fun _ _ => zero_le_one) _
        by_cases b1 : p.1 ∈ Bad
        · rw [Set.indicator_of_mem b1]
          have : c * 1 ≤ c * (1 + Bad.indicator 1 p.2) := by gcongr; linarith
          simp only [Pi.one_apply] at this ⊢
          linarith
        by_cases b2 : p.2 ∈ Bad
        · rw [Set.indicator_of_mem b2]
          have : c * 1 ≤ c * (Bad.indicator 1 p.1 + 1) := by gcongr; linarith
          simp only [Pi.one_apply] at this ⊢
          linarith
        rw [Xv_eq_of_not_bad E hxt b1, Xv_eq_of_not_bad E hxt b1, Xv_eq_of_not_bad E hxt b2,
          Xv_eq_of_not_bad E hxt b2, Set.indicator_of_notMem b1, Set.indicator_of_notMem b2]
        linarith
    _ = c * (E.oppLaw.real Bad + E.oppLaw.real Bad) := by
        rw [integral_const_mul, integral_add (hi1.comp_fst _) (hi1.comp_snd _),
          integral_fun_fst (fun s => Bad.indicator (1 : (Fin (m+1) → ℝ) → ℝ) s),
          integral_fun_snd (fun s => Bad.indicator (1 : (Fin (m+1) → ℝ) → ℝ) s),
          integral_indicator_one hBm]
        simp
    _ ≤ c * ((m+1) * (M * (t - x)) + (m+1) * (M * (t - x))) := by gcongr
    _ = 8 * Li * L * (m+1) * M * (t - x) ^ 2 := by rw [hc]; ring

lemma Cm_tl (hS : E.Standing) {k : Format} {β : ℝ → ℝ} (hβs : StrictMonoOn β (Set.Icc E.tl E.th)) :
    Cm E k β E.tl = 0 := by
  haveI := opp_prob E hS
  have htl : E.tl ∈ Set.Icc E.tl E.th := ⟨le_rfl, hS.1.2.1.le⟩
  have hY : ∀ᵐ s ∂E.oppLaw, Yv k β (β E.tl) s = 0 := by
    filter_upwards [win_ae E hS hβs htl, opp_ae_mem E hS] with s h1 h2
    unfold Yv
    rw [if_neg]
    intro hc
    exact absurd (h2 0).1 (not_le.2 ((h1.1 hc) 0))
  unfold Cm
  rw [integral_congr_ae (g := fun _ => (0:ℝ)) ?_]
  · simp
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hY,
    Measure.quasiMeasurePreserving_snd.ae hY] with p h1 h2
  show moneyF E (Yv k β (β E.tl) p.1) (Yv k β (β E.tl) p.2) = 0
  rw [h1, h2]; unfold moneyF; simp [gainLoss_zero]

lemma Cm_eq (hS : E.Standing) {βI βII : ℝ → ℝ} (hI : E.IsSymCPE .FPA βI)
    (hII : E.IsSymCPE .SPA βII) :
    ∀ t ∈ Set.Icc E.tl E.th, Cm E .FPA βI t = Cm E .SPA βII t := by
  obtain ⟨K, hK0, hK⟩ := width E hS
  have hconst := const_of_sq (fun t => Cm E .FPA βI t - Cm E .SPA βII t) E.tl E.th K hK0 (by
    intro t ht x hx hxt
    have a1 := IC_ineq E hS hI hx ht
    have a2 := IC_ineq E hS hI ht hx
    have b1 := IC_ineq E hS hII hx ht
    have b2 := IC_ineq E hS hII ht hx
    have w := hK x hx t ht hxt
    rw [abs_le]; constructor <;> linarith)
  intro t ht
  have := hconst t ht
  simp only [Cm_tl E hS hI.2.1, Cm_tl E hS hII.2.1] at this
  linarith

lemma signal_Ioo_pos (hS : E.Standing) {a b : ℝ} (ha : E.tl ≤ a) (hab : a < b) (hb : b ≤ E.th) :
    0 < E.signalLaw.real (Set.Ioo a b) := by
  haveI := signal_prob E hS
  obtain ⟨⟨h0, hlt, hfc, hfpos, -⟩, -⟩ := hS
  have hsub : Set.Ioo a b ⊆ Set.Icc E.tl E.th := fun y hy => ⟨ha.trans hy.1.le, hy.2.le.trans hb⟩
  have hne : E.signalLaw (Set.Ioo a b) ≠ 0 := by
    show ((volume.restrict (Set.Icc E.tl E.th)).withDensity
      (fun x => ENNReal.ofReal (E.f x))) (Set.Ioo a b) ≠ 0
    rw [withDensity_apply _ measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_eq_left.2 hsub]
    intro h
    rw [lintegral_eq_zero_iff' ?_] at h
    · have h2 : ∀ᵐ y ∂(volume.restrict (Set.Ioo a b)), False := by
        filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with y hy hy2
        have := hfpos y (hsub hy2)
        simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hy
        linarith
      rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot, Measure.restrict_eq_zero,
        Real.volume_Ioo] at h2
      exact absurd h2 (by simpa using hab)
    · exact ENNReal.measurable_ofReal.comp_aemeasurable
        ((hfc.mono hsub).aemeasurable measurableSet_Ioo)
  rw [measureReal_def]
  exact ENNReal.toReal_pos hne (measure_ne_top _ _)

lemma box_pos (hS : E.Standing) {a b : ℝ} (ha : E.tl ≤ a) (hab : a < b) (hb : b ≤ E.th) :
    0 < E.oppLaw.real {s : Fin (m+1) → ℝ | ∀ j, s j ∈ Set.Ioo a b} := by
  have h := signal_Ioo_pos E hS ha hab hb
  rw [measureReal_def, opp_box E hS, ENNReal.toReal_pow]
  rw [measureReal_def] at h
  positivity

lemma Yv_meas (k : Format) {β : ℝ → ℝ} (hβm : Measurable β) (b : ℝ) :
    Measurable (Yv (m := m) k β b) := by
  unfold Yv
  exact Measurable.ite (meas_win hβm b) (meas_payv k hβm b) measurable_const

lemma Yv_bd (hS : E.Standing) {k : Format} {β : ℝ → ℝ} (hβs : StrictMonoOn β (Set.Icc E.tl E.th))
    (hβnn : ∀ t ∈ Set.Icc E.tl E.th, 0 ≤ β t) {x : ℝ} (hx : x ∈ Set.Icc E.tl E.th) :
    ∀ᵐ s ∂E.oppLaw, |Yv k β (β x) s| ≤ β E.th := by
  filter_upwards [opp_ae_mem E hS] with s hs
  unfold Yv; split_ifs
  · have := payv_bounds E (k := k) hβs hβnn hx hs
    exact abs_le.2 ⟨by linarith [this.1, this.2], this.2⟩
  · simpa using le_trans (hβnn x hx) (hβs.monotoneOn hx ⟨hx.1.trans hx.2, le_rfl⟩ hx.2)

lemma neg_moneyF (y1 y2 : ℝ) :
    -moneyF E y1 y2 = (1 + E.etam) * y1 - E.etam * y2 + E.Lm * max (y1 - y2) 0 := by
  unfold moneyF Env.Lm
  rw [gainLoss_eq]
  rcases le_total y1 y2 with h | h
  · rw [min_eq_right (by linarith : (0:ℝ) ≤ y2 - y1), max_eq_right (by linarith : y1 - y2 ≤ 0)]
    ring
  · rw [min_eq_left (by linarith : y2 - y1 ≤ 0), max_eq_left (by linarith : 0 ≤ y1 - y2)]
    ring

noncomputable def wI (β : ℝ → ℝ) (b : ℝ) (s : Fin (m+1) → ℝ) : ℝ :=
  if ∀ j, β (s j) < b then 1 else 0

noncomputable def Qv (k : Format) (β : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ p, (max (Yv k β (β x) p.1 - Yv k β (β x) p.2) 0 - Yv k β (β x) p.1 * (1 - wI β (β x) p.2))
    ∂(E.oppLaw.prod E.oppLaw)

noncomputable def pw (β : ℝ → ℝ) (x : ℝ) : ℝ := E.oppLaw.real {s | ∀ j, β (s j) < β x}

lemma MQ_int (hS : E.Standing) {k : Format} {β : ℝ → ℝ} (hβm : Measurable β)
    (hβs : StrictMonoOn β (Set.Icc E.tl E.th)) (hβnn : ∀ t ∈ Set.Icc E.tl E.th, 0 ≤ β t)
    {x : ℝ} (hx : x ∈ Set.Icc E.tl E.th) :
    Integrable (fun p : (Fin (m+1) → ℝ) × (Fin (m+1) → ℝ) =>
      max (Yv k β (β x) p.1 - Yv k β (β x) p.2) 0) (E.oppLaw.prod E.oppLaw) ∧
    Integrable (fun p : (Fin (m+1) → ℝ) × (Fin (m+1) → ℝ) =>
      Yv k β (β x) p.1 * (1 - wI β (β x) p.2)) (E.oppLaw.prod E.oppLaw) ∧
    Integrable (fun p : (Fin (m+1) → ℝ) × (Fin (m+1) → ℝ) => Yv k β (β x) p.1)
      (E.oppLaw.prod E.oppLaw) ∧
    Integrable (fun p : (Fin (m+1) → ℝ) × (Fin (m+1) → ℝ) => Yv k β (β x) p.2)
      (E.oppLaw.prod E.oppLaw) := by
  haveI := opp_prob E hS
  have hYm := Yv_meas (m := m) k hβm (β x)
  have hYb := Yv_bd E hS (k := k) hβs hβnn hx
  have hwm : Measurable (wI (m := m) β (β x)) := by
    unfold wI; exact Measurable.ite (meas_win hβm (β x)) measurable_const measurable_const
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine int2 _ (fun a c => max (a - c) 0)
      ((continuous_fst.sub continuous_snd).max continuous_const) 1 zero_le_one ?_ _ hYm _ hYb
    intro a c
    rw [abs_of_nonneg (le_max_right _ _), one_mul]
    exact max_le (by linarith [le_abs_self a, neg_le_abs c]) (by positivity)
  · refine Integrable.of_bound (((hYm.comp measurable_fst).mul
      (measurable_const.sub (hwm.comp measurable_snd))).aestronglyMeasurable) (β E.th) ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hYb] with p hp
    have h1 : |1 - wI β (β x) p.2| ≤ 1 := by unfold wI; split_ifs <;> simp
    rw [Real.norm_eq_abs, abs_mul]
    calc |Yv k β (β x) p.1| * |1 - wI β (β x) p.2| ≤ β E.th * 1 :=
          mul_le_mul hp h1 (abs_nonneg _) (le_trans (abs_nonneg _) hp)
      _ = β E.th := mul_one _
  · exact int2 _ (fun a _ => a) continuous_fst 1 zero_le_one
      (fun a c => by rw [one_mul]; linarith [abs_nonneg c]) _ hYm _ hYb
  · exact int2 _ (fun _ c => c) continuous_snd 1 zero_le_one
      (fun a c => by rw [one_mul]; linarith [abs_nonneg a]) _ hYm _ hYb

lemma Cm_split (hS : E.Standing) {k : Format} {β : ℝ → ℝ} (hβm : Measurable β)
    (hβs : StrictMonoOn β (Set.Icc E.tl E.th)) (hβnn : ∀ t ∈ Set.Icc E.tl E.th, 0 ≤ β t)
    {x : ℝ} (hx : x ∈ Set.Icc E.tl E.th) :
    Cm E k β x = (∫ s, Yv k β (β x) s ∂E.oppLaw) +
      E.Lm * ∫ p, max (Yv k β (β x) p.1 - Yv k β (β x) p.2) 0 ∂(E.oppLaw.prod E.oppLaw) := by
  haveI := opp_prob E hS
  obtain ⟨i3, -, i1, i2⟩ := MQ_int E hS (k := k) hβm hβs hβnn hx
  unfold Cm
  rw [← integral_neg, integral_congr_ae (Filter.Eventually.of_forall fun p => neg_moneyF E _ _)]
  rw [integral_add ?_ (i3.const_mul E.Lm), integral_sub (i1.const_mul _) (i2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_fun_fst (fun s => Yv k β (β x) s), integral_fun_snd (fun s => Yv k β (β x) s)]
  · simp; ring
  · exact (i1.const_mul _).sub (i2.const_mul _)

lemma M_split (hS : E.Standing) {k : Format} {β : ℝ → ℝ} (hβm : Measurable β)
    (hβs : StrictMonoOn β (Set.Icc E.tl E.th)) (hβnn : ∀ t ∈ Set.Icc E.tl E.th, 0 ≤ β t)
    {x : ℝ} (hx : x ∈ Set.Icc E.tl E.th) :
    ∫ p, max (Yv k β (β x) p.1 - Yv k β (β x) p.2) 0 ∂(E.oppLaw.prod E.oppLaw) =
      (∫ s, Yv k β (β x) s ∂E.oppLaw) * (1 - pw E β x) + Qv E k β x := by
  haveI := opp_prob E hS
  obtain ⟨i3, i4, -, -⟩ := MQ_int E hS (k := k) hβm hβs hβnn hx
  have hA : MeasurableSet {s : Fin (m+1) → ℝ | ∀ j, β (s j) < β x} := meas_win hβm (β x)
  have hw : wI β (β x) = {s : Fin (m+1) → ℝ | ∀ j, β (s j) < β x}.indicator 1 := by
    funext s; unfold wI; simp [Set.indicator_apply]
  have e1 : ∫ p, Yv k β (β x) p.1 * (1 - wI β (β x) p.2) ∂(E.oppLaw.prod E.oppLaw) =
      (∫ s, Yv k β (β x) s ∂E.oppLaw) * ∫ s, (1 - wI β (β x) s) ∂E.oppLaw :=
    integral_prod_mul (Yv k β (β x)) (fun s => 1 - wI β (β x) s)
  have e2 : ∫ s, (1 - wI β (β x) s) ∂E.oppLaw = 1 - pw E β x := by
    rw [integral_sub (integrable_const 1) ?_, hw, integral_indicator_one hA]
    · simp [pw]
    · rw [hw]; exact (integrable_const (1:ℝ)).indicator hA
  unfold Qv
  rw [integral_sub i3 i4, e1, e2]; ring

lemma Q_FPA {β : ℝ → ℝ} (hβnn : ∀ t ∈ Set.Icc E.tl E.th, 0 ≤ β t) {x : ℝ}
    (hx : x ∈ Set.Icc E.tl E.th) : Qv E .FPA β x = 0 := by
  have hb := hβnn x hx
  unfold Qv
  rw [integral_congr_ae (g := fun _ => (0:ℝ)) (Filter.Eventually.of_forall fun p => ?_)]
  · simp
  simp only [Yv, wI, payv, max_def]
  split_ifs <;> linarith

lemma gQ_nonneg {a a' : Prop} [Decidable a] [Decidable a'] {Z Z' : ℝ} (hZ : 0 ≤ Z)
    (hZ' : 0 ≤ Z') :
    0 ≤ max ((if a then Z else 0) - (if a' then Z' else 0)) 0 -
      (if a then Z else 0) * (1 - if a' then 1 else 0) := by
  by_cases ha : a <;> by_cases ha' : a'
  · rw [if_pos ha, if_pos ha', if_pos ha']; linarith [le_max_right (Z - Z') 0]
  · rw [if_pos ha, if_neg ha', if_neg ha', max_eq_left (by linarith : (0:ℝ) ≤ Z - 0)]; linarith
  · rw [if_neg ha, if_pos ha', if_pos ha']; linarith [le_max_right (0 - Z') 0]
  · rw [if_neg ha, if_neg ha', if_neg ha']; linarith [le_max_right ((0:ℝ) - 0) 0]

lemma Q_SPA (hS : E.Standing) {β : ℝ → ℝ} (hβ : E.IsSymCPE .SPA β) {x : ℝ}
    (hx : x ∈ Set.Icc E.tl E.th) :
    0 ≤ Qv E .SPA β x ∧ (E.tl < x → 0 < Qv E .SPA β x) := by
  haveI := opp_prob E hS
  obtain ⟨hβm, hβs, hβnn, -⟩ := hβ
  obtain ⟨i3, i4, -, -⟩ := MQ_int E hS (k := .SPA) hβm hβs hβnn hx
  have hZ : ∀ s : Fin (m+1) → ℝ, (∀ j, s j ∈ Set.Icc E.tl E.th) →
      0 ≤ payv .SPA β (β x) s := fun s hs => (payv_bounds E hβs hβnn hx hs).1
  have hnn : ∀ᵐ p ∂(E.oppLaw.prod E.oppLaw), (0:ℝ) ≤
      max (Yv .SPA β (β x) p.1 - Yv .SPA β (β x) p.2) 0 -
        Yv .SPA β (β x) p.1 * (1 - wI β (β x) p.2) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (opp_ae_mem E hS),
      Measure.quasiMeasurePreserving_snd.ae (opp_ae_mem E hS)] with p h1 h2
    unfold Yv wI
    exact gQ_nonneg (hZ p.1 h1) (hZ p.2 h2)
  refine ⟨integral_nonneg_of_ae hnn, fun hlx => ?_⟩
  set c := E.tl + (x - E.tl) / 3 with hcdef
  set c' := E.tl + 2 * (x - E.tl) / 3 with hc'def
  have hc : c ∈ Set.Icc E.tl E.th := ⟨by rw [hcdef]; linarith, by rw [hcdef]; linarith [hx.2]⟩
  have hc' : c' ∈ Set.Icc E.tl E.th := ⟨by rw [hc'def]; linarith, by rw [hc'def]; linarith [hx.2]⟩
  have hcc : c < c' := by rw [hcdef, hc'def]; linarith
  have hcx : c < x := by rw [hcdef]; linarith
  have hc'x : c' < x := by rw [hc'def]; linarith
  have hδ : 0 < β c' - β c := sub_pos.2 (hβs hc hc' hcc)
  set S1 : Set (Fin (m+1) → ℝ) := {s | ∀ j, s j ∈ Set.Ioo c' x} with hS1
  set S2 : Set (Fin (m+1) → ℝ) := {s | ∀ j, s j ∈ Set.Ioo E.tl c} with hS2
  have hS1m : MeasurableSet S1 := by
    rw [hS1]; simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => (measurable_pi_apply j) measurableSet_Ioo
  have hS2m : MeasurableSet S2 := by
    rw [hS2]; simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => (measurable_pi_apply j) measurableSet_Ioo
  have hlow : ∀ᵐ p ∂(E.oppLaw.prod E.oppLaw),
      (β c' - β c) * (S1.indicator (1 : (Fin (m+1) → ℝ) → ℝ) p.1 *
        S2.indicator (1 : (Fin (m+1) → ℝ) → ℝ) p.2) ≤
      max (Yv .SPA β (β x) p.1 - Yv .SPA β (β x) p.2) 0 -
        Yv .SPA β (β x) p.1 * (1 - wI β (β x) p.2) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (opp_ae_mem E hS),
      Measure.quasiMeasurePreserving_snd.ae (opp_ae_mem E hS)] with p h1 h2
    by_cases hb : p.1 ∈ S1 ∧ p.2 ∈ S2
    · rw [Set.indicator_of_mem hb.1, Set.indicator_of_mem hb.2]
      simp only [Pi.one_apply, mul_one]
      have hb1 : ∀ j, p.1 j ∈ Set.Ioo c' x := hb.1
      have hb2 : ∀ j, p.2 j ∈ Set.Ioo E.tl c := hb.2
      have hA1 : ∀ j, β (p.1 j) < β x := fun j => (hβs.lt_iff_lt (h1 j) hx).2 (hb1 j).2
      have hA2 : ∀ j, β (p.2 j) < β x :=
        fun j => (hβs.lt_iff_lt (h2 j) hx).2 ((hb2 j).2.trans hcx)
      have hZ1 : β c' < payv .SPA β (β x) p.1 := by
        show β c' < Finset.univ.sup' Finset.univ_nonempty (fun j => β (p.1 j))
        exact lt_of_lt_of_le ((hβs.lt_iff_lt hc' (h1 0)).2 (hb1 0).1)
          (Finset.le_sup' (fun j => β (p.1 j)) (Finset.mem_univ 0))
      have hZ2 : payv .SPA β (β x) p.2 < β c := by
        show Finset.univ.sup' Finset.univ_nonempty (fun j => β (p.2 j)) < β c
        exact (Finset.sup'_lt_iff _).2 fun j _ => (hβs.lt_iff_lt (h2 j) hc).2 (hb2 j).2
      unfold Yv wI
      simp only [if_pos hA1, if_pos hA2]
      linarith [le_max_left (payv .SPA β (β x) p.1 - payv .SPA β (β x) p.2) 0]
    · have h0 : S1.indicator (1 : (Fin (m+1) → ℝ) → ℝ) p.1 *
          S2.indicator (1 : (Fin (m+1) → ℝ) → ℝ) p.2 = 0 := by
        by_cases hb1 : p.1 ∈ S1
        · rw [Set.indicator_of_notMem (fun h => hb ⟨hb1, h⟩), mul_zero]
        · rw [Set.indicator_of_notMem hb1, zero_mul]
      rw [h0, mul_zero]
      unfold Yv wI
      exact gQ_nonneg (hZ p.1 h1) (hZ p.2 h2)
  have hint_low : Integrable (fun p : (Fin (m+1) → ℝ) × (Fin (m+1) → ℝ) =>
      (β c' - β c) * (S1.indicator (1 : (Fin (m+1) → ℝ) → ℝ) p.1 *
        S2.indicator (1 : (Fin (m+1) → ℝ) → ℝ) p.2)) (E.oppLaw.prod E.oppLaw) :=
    (((integrable_const (1:ℝ)).indicator hS1m).mul_prod
      ((integrable_const (1:ℝ)).indicator hS2m)).const_mul _
  have hval : ∫ p, (β c' - β c) * (S1.indicator (1 : (Fin (m+1) → ℝ) → ℝ) p.1 *
        S2.indicator (1 : (Fin (m+1) → ℝ) → ℝ) p.2) ∂(E.oppLaw.prod E.oppLaw) =
      (β c' - β c) * (E.oppLaw.real S1 * E.oppLaw.real S2) := by
    rw [integral_const_mul]
    congr 1
    have := integral_prod_mul (μ := E.oppLaw) (ν := E.oppLaw)
      (S1.indicator (1 : (Fin (m+1) → ℝ) → ℝ)) (S2.indicator (1 : (Fin (m+1) → ℝ) → ℝ))
    rw [this, integral_indicator_one hS1m, integral_indicator_one hS2m]
  have hpos : 0 < (β c' - β c) * (E.oppLaw.real S1 * E.oppLaw.real S2) :=
    mul_pos hδ (mul_pos (box_pos E hS hc'.1 hc'x hx.2) (box_pos E hS le_rfl (by linarith) hc.2))
  calc (0:ℝ) < _ := hpos
    _ = _ := hval.symm
    _ ≤ Qv E .SPA β x := by unfold Qv; exact integral_mono_ae hint_low (i3.sub i4) hlow

lemma pw_eq (hS : E.Standing) {β1 β2 : ℝ → ℝ} (h1 : StrictMonoOn β1 (Set.Icc E.tl E.th))
    (h2 : StrictMonoOn β2 (Set.Icc E.tl E.th)) {x : ℝ} (hx : x ∈ Set.Icc E.tl E.th) :
    pw E β1 x = pw E β2 x := by
  unfold pw
  have e1 : {s : Fin (m+1) → ℝ | ∀ j, β1 (s j) < β1 x} =ᵐ[E.oppLaw] {s | ∀ j, s j < x} :=
    (win_ae E hS h1 hx).mono fun s h => propext h
  have e2 : {s : Fin (m+1) → ℝ | ∀ j, β2 (s j) < β2 x} =ᵐ[E.oppLaw] {s | ∀ j, s j < x} :=
    (win_ae E hS h2 hx).mono fun s h => propext h
  rw [measureReal_congr e1, measureReal_congr e2]

lemma interim_eq (k : Format) (β : ℝ → ℝ) (t : ℝ) :
    E.interimPayment k β t = ∫ s, Yv k β (β t) s ∂E.oppLaw := by
  unfold Env.interimPayment
  congr 1; funext s; rw [outcome_snd]; rfl

lemma revenue_eq (hS : E.Standing) {k : Format} {β : ℝ → ℝ} (hβm : Measurable β)
    (hβs : StrictMonoOn β (Set.Icc E.tl E.th)) (hβnn : ∀ t ∈ Set.Icc E.tl E.th, 0 ≤ β t) :
    E.revenue k β = (m + 2) * ∫ t, E.interimPayment k β t ∂E.signalLaw ∧
      Integrable (fun t => E.interimPayment k β t) E.signalLaw := by
  haveI := signal_prob E hS
  haveI := opp_prob E hS
  set g : ℝ × (Fin (m+1) → ℝ) → ℝ := fun q => (E.outcome k β (β q.1) q.1 q.2).2 with hg
  have hgm : Measurable g := by
    have hset : MeasurableSet {q : ℝ × (Fin (m+1) → ℝ) | ∀ j, β (q.2 j) < β q.1} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j => measurableSet_lt
        (hβm.comp ((measurable_pi_apply j).comp measurable_snd)) (hβm.comp measurable_fst)
    have hp : Measurable (fun q : ℝ × (Fin (m+1) → ℝ) => payv k β (β q.1) q.2) := by
      cases k
      · exact hβm.comp measurable_fst
      · exact (meas_payv Format.SPA hβm 0).comp measurable_snd
    have : g = fun q => if ∀ j, β (q.2 j) < β q.1 then payv k β (β q.1) q.2 else 0 := by
      funext q; exact outcome_snd E k β _ _ _
    rw [this]; exact Measurable.ite hset hp measurable_const
  have hgi : Integrable g (E.signalLaw.prod E.oppLaw) := by
    refine Integrable.of_bound hgm.aestronglyMeasurable (β E.th) ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (signal_ae_mem E),
      Measure.quasiMeasurePreserving_snd.ae (opp_ae_mem E hS)] with q h1 h2
    rw [Real.norm_eq_abs, hg]
    simp only
    rw [outcome_snd]
    split_ifs
    · have := payv_bounds E (k := k) hβs hβnn h1 h2
      exact abs_le.2 ⟨by linarith [this.1, this.2], this.2⟩
    · simpa using le_trans (hβnn q.1 h1) (hβs.monotoneOn h1 ⟨h1.1.trans h1.2, le_rfl⟩ h1.2)
  have hpi : ∀ i : Fin (m+2), ∫ σ, (E.outcome k β (β (σ i)) (σ i)
      (fun j => σ (i.succAbove j))).2 ∂E.allLaw = ∫ t, E.interimPayment k β t ∂E.signalLaw := by
    intro i
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m+2) => E.signalLaw) i
    have h1 : ∫ σ, g (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+2) => ℝ) i σ)
        ∂(Measure.pi fun _ : Fin (m+2) => E.signalLaw) =
        ∫ q, g q ∂(E.signalLaw.prod E.oppLaw) := hmp.integral_comp' g
    exact h1.trans (integral_prod g hgi)
  have hii : ∀ i : Fin (m+2), Integrable (fun σ : Fin (m+2) → ℝ => (E.outcome k β (β (σ i)) (σ i)
      (fun j => σ (i.succAbove j))).2) E.allLaw := by
    intro i
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m+2) => E.signalLaw) i
    exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hgi
  refine ⟨?_, hgi.integral_prod_left⟩
  unfold Env.revenue
  rw [integral_finsetSum _ (fun i _ => hii i)]
  simp only [hpi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

theorem main {m : ℕ} (E : Env m) (hS : E.Standing) (βI βII : ℝ → ℝ)
    (hI : E.IsSymCPE .FPA βI) (hII : E.IsSymCPE .SPA βII) :
    (E.Lm = 0 → E.revenue .SPA βII = E.revenue .FPA βI) ∧
    (0 < E.Lm → E.revenue .SPA βII < E.revenue .FPA βI) := by
  haveI := signal_prob E hS
  haveI := opp_prob E hS
  obtain ⟨hRI, hPIi⟩ := revenue_eq E hS (k := .FPA) hI.1 hI.2.1 hI.2.2.1
  obtain ⟨hRII, hPIIi⟩ := revenue_eq E hS (k := .SPA) hII.1 hII.2.1 hII.2.2.1
  have key : ∀ t ∈ Set.Icc E.tl E.th,
      (E.interimPayment .FPA βI t - E.interimPayment .SPA βII t) *
        (1 + E.Lm * (1 - pw E βI t)) = E.Lm * Qv E .SPA βII t := by
    intro t ht
    have h1 := Cm_eq E hS hI hII t ht
    rw [Cm_split E hS hI.1 hI.2.1 hI.2.2.1 ht, Cm_split E hS hII.1 hII.2.1 hII.2.2.1 ht,
      M_split E hS hI.1 hI.2.1 hI.2.2.1 ht, M_split E hS hII.1 hII.2.1 hII.2.2.1 ht,
      Q_FPA E hI.2.2.1 ht, ← pw_eq E hS hI.2.1 hII.2.1 ht] at h1
    rw [interim_eq, interim_eq]
    linear_combination h1
  have hp1 : ∀ t, pw E βI t ≤ 1 := fun t =>
    (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)).trans (by simp)
  constructor
  · intro h0
    rw [hRI, hRII]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [signal_ae_mem E] with t ht
    have := key t ht
    rw [h0] at this
    linarith
  · intro hpos
    rw [hRI, hRII]
    have hdiff : 0 < ∫ t, (E.interimPayment .FPA βI t - E.interimPayment .SPA βII t)
        ∂E.signalLaw := by
      have hd : ∀ t ∈ Set.Icc E.tl E.th, 0 ≤ E.interimPayment .FPA βI t -
          E.interimPayment .SPA βII t ∧ (E.tl < t → 0 < E.interimPayment .FPA βI t -
          E.interimPayment .SPA βII t) := by
        intro t ht
        have hk := key t ht
        have hD : 0 < 1 + E.Lm * (1 - pw E βI t) := by
          have := mul_nonneg hpos.le (sub_nonneg.2 (hp1 t)); linarith
        have hq := Q_SPA E hS hII ht
        have heq : E.interimPayment .FPA βI t - E.interimPayment .SPA βII t =
            E.Lm * Qv E .SPA βII t / (1 + E.Lm * (1 - pw E βI t)) :=
          eq_div_of_mul_eq hD.ne' hk
        rw [heq]
        exact ⟨div_nonneg (mul_nonneg hpos.le hq.1) hD.le,
          fun hlt => div_pos (mul_pos hpos (hq.2 hlt)) hD⟩
      refine (integral_pos_iff_support_of_nonneg_ae (f := fun t => E.interimPayment .FPA βI t -
        E.interimPayment .SPA βII t) ?_ (hPIi.sub hPIIi)).2 ?_
      · filter_upwards [signal_ae_mem E] with t ht
        exact (hd t ht).1
      · have hsub : Set.Ioo E.tl E.th ⊆ Function.support
            (fun t => E.interimPayment .FPA βI t - E.interimPayment .SPA βII t) := by
          intro t ht
          exact ((hd t ⟨ht.1.le, ht.2.le⟩).2 ht.1).ne'
        have h3 := signal_Ioo_pos E hS le_rfl hS.1.2.1 le_rfl
        rw [measureReal_def] at h3
        exact lt_of_lt_of_le (ENNReal.toReal_pos_iff.1 h3).1 (measure_mono hsub)
    rw [integral_sub hPIi hPIIi] at hdiff
    have hm : (0:ℝ) < m + 2 := by positivity
    nlinarith

end LossAverseAuction.CPERevenue.Cor1Aux

open LossAverseAuction.CPERevenue MeasureTheory in
theorem solution {m : ℕ} (E : Env m) (hS : E.Standing)
    (hA1 : E.Assumption1) (βI βII : ℝ → ℝ)
    (hI : E.IsSymCPE .FPA βI) (hII : E.IsSymCPE .SPA βII) :
    (E.Lm = 0 → E.revenue .SPA βII = E.revenue .FPA βI) ∧
    (0 < E.Lm → E.revenue .SPA βII < E.revenue .FPA βI) := by
  exact LossAverseAuction.CPERevenue.Cor1Aux.main E hS βI βII hI hII
