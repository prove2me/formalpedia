-- Prove2me | solution 1 for GongReusable.Myopic.theorem_1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T12:34:36.784905+00:00
-- url     : https://prove2.me/submissions/bf3bcf35-f1e9-4ec0-a573-b1bd38232a6d

import Mathlib
import Definitions.Def_GongReusable_Myopic_Process

open MeasureTheory Set
open scoped ENNReal
noncomputable section

namespace GongReusable.Myopic

def ceModel : Model Bool Bool where
  capacity := fun _ => 1
  feasible := {∅, Finset.univ}
  choice := fun z S o =>
    if z ∈ S then
      if o = some z then 1 else 0
    else
      if o = none then 1 else 0
  duration := fun _ => Measure.dirac ⊤
  rentalRevenue := fun j _ => if j then 10 else 1

def ceArrivals : Arrivals Bool 2 where
  epoch := fun _ => 0
  type := fun t => if t.val = 0 then false else true
  ordered := fun _ _ _ => le_rfl

def optPolicy : Policy Bool where
  act := fun i _ _ => if i.1 = 0 then ∅ else Finset.univ
  measurable_act := fun _ => measurable_const

lemma meanRevenue_ce (j : Bool) :
    meanRevenue ceModel j = if j then 10 else 1 := by
  unfold meanRevenue ceModel
  simp

lemma ceModel_valid : Valid ceModel where
  reject := by simp [ceModel]
  prob := fun _ => by dsimp [ceModel]; infer_instance
  fee_measurable := fun _ => by
    dsimp [ceModel]
    exact measurable_const
  fee_integrable := fun _ => by
    dsimp [ceModel]
    exact integrable_const _
  mean_nonneg := fun j => by
    rw [meanRevenue_ce]
    cases j <;> norm_num
  choice_law := fun z =>
    { nonneg := fun S o => by
        dsimp [ceModel]
        split_ifs <;> norm_num
      total := fun S => by
        dsimp [ceModel]
        by_cases hz : z ∈ S <;> simp [hz]
      support := fun S j hj => by
        dsimp [ceModel]
        by_cases hz : z ∈ S
        · have hne : (some j : Option Bool) ≠ some z := by
            intro h
            cases h
            exact hj hz
          simp [hz, hne]
        · simp [hz] }
  regular := fun z S U hSU _ j hj => by
    dsimp [ceModel]
    by_cases hjz : j = z
    · subst hjz
      simp [hj, hSU hj]
    · have hne : (some j : Option Bool) ≠ some z := by
        intro h
        exact hjz (Option.some.inj h)
      by_cases hzU : z ∈ U <;> by_cases hzS : z ∈ S <;> simp [hzU, hzS, hne]

lemma revenue_ce_empty (z : Bool) :
    revenue ceModel (ceModel.choice z) ∅ = 0 := by
  simp [revenue]

lemma revenue_ce_univ (z : Bool) :
    revenue ceModel (ceModel.choice z) Finset.univ = if z then 10 else 1 := by
  unfold revenue
  rw [Fintype.sum_bool]
  rw [meanRevenue_ce true, meanRevenue_ce false]
  dsimp [ceModel]
  cases z <;> norm_num

lemma pickList_eq_none_of_some_zero (p : Option Bool → ℝ)
    (hp : ∀ j : Bool, p (some j) = 0) (hnone : 0 ≤ p none) :
    ∀ (l : List (Option Bool)) {u : ℝ}, 0 ≤ u → pickList none p l u = none
  | [], _, _ => rfl
  | none :: rest, u, hu => by
    dsimp [pickList]
    split_ifs with hlt
    · rfl
    · exact pickList_eq_none_of_some_zero p hp hnone rest (sub_nonneg.mpr (not_lt.mp hlt))
  | some j :: rest, u, hu => by
    dsimp [pickList]
    rw [hp j, if_neg (not_lt.mpr hu), sub_zero]
    exact pickList_eq_none_of_some_zero p hp hnone rest hu

lemma choose_empty_eq_none (z : Bool) {u : ℝ} (hu : 0 ≤ u) :
    choose (ceModel.choice z ∅) u = none := by
  unfold choose
  apply pickList_eq_none_of_some_zero _ _ _ _ hu
  · intro j
    simp [ceModel]
  · simp [ceModel]

lemma pickList_eq_some_of_ind (target : Option Bool) (p : Option Bool → ℝ)
    (ht : p target = 1) (ho : ∀ a ≠ target, p a = 0) :
    ∀ (l : List (Option Bool)), target ∈ l → ∀ {u : ℝ}, 0 ≤ u → u < 1 →
      pickList none p l u = target
  | [], hmem, _, _, _ => False.elim (List.not_mem_nil hmem)
  | a :: rest, hmem, u, hu0, hu1 => by
    dsimp [pickList]
    by_cases ha : a = target
    · subst ha
      rw [ht, if_pos hu1]
    · rw [ho a ha, if_neg (not_lt.mpr hu0), sub_zero]
      rcases List.mem_cons.mp hmem with rfl | hrest
      · exact False.elim (ha rfl)
      · exact pickList_eq_some_of_ind target p ht ho rest hrest hu0 hu1

lemma choose_univ_eq_some (z : Bool) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    choose (ceModel.choice z Finset.univ) u = some z := by
  unfold choose
  apply pickList_eq_some_of_ind (some z) (ceModel.choice z Finset.univ)
  · simp [ceModel]
  · intro a ha
    dsimp [ceModel]
    simp [ha]
  · exact Finset.mem_toList.mpr (Finset.mem_univ (some z))
  · exact hu0
  · exact hu1

lemma available_zero (a : NNReal) (h : History Bool) :
    available ceModel 0 a h = Finset.univ := by
  ext j
  simp [available, ceModel]

lemma offers_eq_feasible_of_available_univ {t : ℕ} {a : NNReal} {h : History Bool}
    (havail : available ceModel t a h = Finset.univ) :
    offers ceModel t a h = ceModel.feasible := by
  ext S
  simp only [offers, Finset.mem_filter, havail, and_iff_left_iff_imp]
  intro _
  exact Finset.subset_univ S

lemma offers_zero (a : NNReal) (h : History Bool) :
    offers ceModel 0 a h = ceModel.feasible :=
  offers_eq_feasible_of_available_univ (available_zero a h)

lemma mem_feasible_ce (S : Finset Bool) :
    S ∈ ceModel.feasible ↔ S = ∅ ∨ S = Finset.univ := by
  simp [ceModel]

lemma maximizers_zero_false :
    maximizers ceModel 0 0 (ceModel.choice false) initialHistory = {Finset.univ} := by
  ext S
  simp only [maximizers, offers_zero, mem_feasible_ce, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | rfl, hmax⟩
    · have h1 := hmax Finset.univ (Or.inr rfl)
      rw [revenue_ce_empty, revenue_ce_univ] at h1
      norm_num at h1
    · rfl
  · rintro rfl
    refine ⟨Or.inr rfl, ?_⟩
    intro U hU
    rcases hU with rfl | rfl
    · rw [revenue_ce_empty, revenue_ce_univ]
      norm_num
    · exact le_rfl

lemma myopicOffer_eq_of_maximizers {t : ℕ} {a : NNReal} {q : ChoiceProb Bool} {h : History Bool}
    {S : Finset Bool} (hmax : maximizers ceModel t a q h = {S}) (u : ℝ) :
    myopicOffer ceModel rejection t a q h u = S := by
  dsimp only [myopicOffer]
  rw [hmax]
  by_cases hmem : rejection.act (t, a, q) h u ∈ ({S} : Finset (Finset Bool))
  · rw [if_pos hmem]
    exact Finset.mem_singleton.mp hmem
  · rw [if_neg hmem]
    simp

lemma mem_available_one (h : History Bool) (j : Bool) :
    j ∈ available ceModel 1 0 h ↔
      ¬ ((h 0).2.2.1 = some j ∧ (0 : ℝ≥0∞) < (h 0).1 + (h 0).2.2.2) := by
  simp [available, ceModel, Finset.range_one, Finset.filter_singleton]

lemma run_one (A : OfferRule Bool) (w : Tape Bool 2) :
    run ceModel ceArrivals A w 1 =
      step A 0 0 (ceModel.choice false) initialHistory (w 0) := rfl

lemma run_two (A : OfferRule Bool) (w : Tape Bool 2) :
    run ceModel ceArrivals A w 2 =
      step A 1 0 (ceModel.choice true) (run ceModel ceArrivals A w 1) (w 1) := rfl

lemma step_apply_self (A : OfferRule Bool) (t : ℕ) (a : NNReal) (q : ChoiceProb Bool)
    (h : History Bool) (w : Noise Bool) :
    (step A t a q h w t).2.1 = A t a q h w.1.1 := by
  unfold step
  rw [Function.update_self]

lemma step_apply_of_ne (A : OfferRule Bool) {s t : ℕ} (hne : s ≠ t) (a : NNReal)
    (q : ChoiceProb Bool) (h : History Bool) (w : Noise Bool) :
    step A t a q h w s = h s := by
  unfold step
  exact Function.update_of_ne hne _ _

lemma myopic_pathRevenue_eq_one {w : Tape Bool 2}
    (hu0 : 0 ≤ (w 0).1.2) (hu1 : (w 0).1.2 < 1) (hd : (w 0).2 false = ⊤) :
    pathRevenue ceModel ceArrivals (run ceModel ceArrivals (myopicOffer ceModel rejection) w 2) = 1 := by
  have hmyopic0 : ∀ u, myopicOffer ceModel rejection 0 0 (ceModel.choice false) initialHistory u = Finset.univ :=
    myopicOffer_eq_of_maximizers maximizers_zero_false
  have hrun1 : run ceModel ceArrivals (myopicOffer ceModel rejection) w 1 =
      Function.update initialHistory 0 (0, Finset.univ, some false, ⊤) := by
    rw [run_one]
    dsimp only [step]
    rw [hmyopic0, choose_univ_eq_some false hu0 hu1]
    simp [hd]
  have hnot_avail : false ∉ available ceModel 1 0 (run ceModel ceArrivals (myopicOffer ceModel rejection) w 1) := by
    rw [mem_available_one, hrun1, Function.update_self]
    simp
  have hoffers1 : offers ceModel 1 0 (run ceModel ceArrivals (myopicOffer ceModel rejection) w 1) = {∅} := by
    ext S
    simp only [offers, Finset.mem_filter, mem_feasible_ce, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, hsub⟩
      · rfl
      · exact False.elim (hnot_avail (hsub (Finset.mem_univ false)))
    · rintro rfl
      exact ⟨Or.inl rfl, Finset.empty_subset _⟩
  have hmax1 : maximizers ceModel 1 0 (ceModel.choice true)
      (run ceModel ceArrivals (myopicOffer ceModel rejection) w 1) = {∅} := by
    ext S
    simp only [maximizers, hoffers1, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl, _⟩
      rfl
    · rintro rfl
      refine ⟨rfl, ?_⟩
      intro U hU
      rw [hU]
  have hmyopic1 : ∀ u, myopicOffer ceModel rejection 1 0 (ceModel.choice true)
      (run ceModel ceArrivals (myopicOffer ceModel rejection) w 1) u = ∅ :=
    myopicOffer_eq_of_maximizers hmax1
  have hrun2_0 : (run ceModel ceArrivals (myopicOffer ceModel rejection) w 2 0).2.1 = Finset.univ := by
    rw [run_two, step_apply_of_ne _ (by decide : (0 : ℕ) ≠ 1), run_one, step_apply_self, hmyopic0]
  have hrun2_1 : (run ceModel ceArrivals (myopicOffer ceModel rejection) w 2 1).2.1 = ∅ := by
    rw [run_two, step_apply_self, hmyopic1]
  unfold pathRevenue
  rw [Fin.sum_univ_two]
  change revenue ceModel (ceModel.choice false)
      (run ceModel ceArrivals (myopicOffer ceModel rejection) w 2 0).2.1 +
    revenue ceModel (ceModel.choice true)
      (run ceModel ceArrivals (myopicOffer ceModel rejection) w 2 1).2.1 = 1
  rw [hrun2_0, hrun2_1, revenue_ce_univ, revenue_ce_empty]
  norm_num

lemma opt_pathRevenue_eq_ten {w : Tape Bool 2} (hu0 : 0 ≤ (w 0).1.2) :
    pathRevenue ceModel ceArrivals (run ceModel ceArrivals (offer ceModel optPolicy) w 2) = 10 := by
  have hoffer0 : ∀ u, offer ceModel optPolicy 0 0 (ceModel.choice false) initialHistory u = ∅ := by
    intro u
    dsimp only [offer]
    rw [offers_zero]
    simp [optPolicy, ceModel]
  have hrun1 : run ceModel ceArrivals (offer ceModel optPolicy) w 1 =
      Function.update initialHistory 0 (0, ∅, none, 0) := by
    rw [run_one]
    dsimp only [step]
    rw [hoffer0, choose_empty_eq_none false hu0]
    rfl
  have havail1 : available ceModel 1 0 (run ceModel ceArrivals (offer ceModel optPolicy) w 1) = Finset.univ := by
    ext j
    simp only [Finset.mem_univ, iff_true, mem_available_one, hrun1, Function.update_self]
    simp
  have hoffers1 : offers ceModel 1 0 (run ceModel ceArrivals (offer ceModel optPolicy) w 1) = ceModel.feasible :=
    offers_eq_feasible_of_available_univ havail1
  have hoffer1 : ∀ u, offer ceModel optPolicy 1 0 (ceModel.choice true)
      (run ceModel ceArrivals (offer ceModel optPolicy) w 1) u = Finset.univ := by
    intro u
    dsimp only [offer]
    rw [hoffers1]
    simp [optPolicy, ceModel]
  have hrun2_0 : (run ceModel ceArrivals (offer ceModel optPolicy) w 2 0).2.1 = ∅ := by
    rw [run_two, step_apply_of_ne _ (by decide : (0 : ℕ) ≠ 1), run_one, step_apply_self, hoffer0]
  have hrun2_1 : (run ceModel ceArrivals (offer ceModel optPolicy) w 2 1).2.1 = Finset.univ := by
    rw [run_two, step_apply_self, hoffer1]
  unfold pathRevenue
  rw [Fin.sum_univ_two]
  change revenue ceModel (ceModel.choice false)
      (run ceModel ceArrivals (offer ceModel optPolicy) w 2 0).2.1 +
    revenue ceModel (ceModel.choice true)
      (run ceModel ceArrivals (offer ceModel optPolicy) w 2 1).2.1 = 10
  rw [hrun2_0, hrun2_1, revenue_ce_empty, revenue_ce_univ]
  norm_num

instance uniform_isProb : IsProbabilityMeasure uniform := by
  constructor
  unfold uniform
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num

instance ce_noiseLaw_isProb : IsProbabilityMeasure (noiseLaw ceModel) := by
  unfold noiseLaw
  have : ∀ j : Bool, IsProbabilityMeasure (ceModel.duration j) := ceModel_valid.prob
  infer_instance

instance ce_tapeLaw_isProb : IsProbabilityMeasure (tapeLaw ceModel 2) := by
  unfold tapeLaw
  infer_instance

lemma ae_uniform_Ico : ∀ᵐ u ∂uniform, 0 ≤ u ∧ u < 1 := by
  have h1 : ∀ᵐ u ∂uniform, u ∈ Icc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Icc
  have h2 : ∀ᵐ u ∂uniform, u ≠ 1 := by
    rw [ae_iff]
    have hsub : {u : ℝ | ¬ u ≠ 1} = {(1 : ℝ)} := by ext u; simp
    rw [hsub]
    unfold uniform
    rw [Measure.restrict_apply (measurableSet_singleton 1)]
    exact measure_mono_null Set.inter_subset_left (by simp)
  filter_upwards [h1, h2] with u hu1 hu2
  exact ⟨hu1.1, lt_of_le_of_ne hu1.2 hu2⟩

lemma ae_duration_top : ∀ᵐ d ∂ceModel.duration false, d = ⊤ := by
  change ∀ᵐ d ∂(Measure.dirac (⊤ : ℝ≥0∞)), d = ⊤
  rw [ae_iff]
  have hsub : {d : ℝ≥0∞ | ¬ d = ⊤} = ({⊤} : Set ℝ≥0∞)ᶜ := rfl
  rw [hsub, Measure.dirac_apply' _ (measurableSet_singleton ⊤).compl]
  simp

lemma ae_tapeLaw_good :
    ∀ᵐ w ∂tapeLaw ceModel 2, (0 ≤ (w 0).1.2 ∧ (w 0).1.2 < 1) ∧ (w 0).2 false = ⊤ := by
  have : ∀ j : Bool, IsProbabilityMeasure (ceModel.duration j) := ceModel_valid.prob
  have h0 : MeasurePreserving (Function.eval (0 : Fin 2)) (tapeLaw ceModel 2) (noiseLaw ceModel) :=
    measurePreserving_eval (fun _ : Fin 2 => noiseLaw ceModel) 0
  have h1 : MeasurePreserving Prod.fst (noiseLaw ceModel) (uniform.prod uniform) :=
    measurePreserving_fst
  have h2 : MeasurePreserving Prod.snd (uniform.prod uniform) uniform :=
    measurePreserving_snd
  have h3 : MeasurePreserving Prod.snd (noiseLaw ceModel) (Measure.pi ceModel.duration) :=
    measurePreserving_snd
  have h4 : MeasurePreserving (Function.eval false) (Measure.pi ceModel.duration) (ceModel.duration false) :=
    measurePreserving_eval ceModel.duration false
  have hae1 : ∀ᵐ w ∂tapeLaw ceModel 2, 0 ≤ (w 0).1.2 ∧ (w 0).1.2 < 1 :=
    (h2.comp (h1.comp h0)).quasiMeasurePreserving.ae ae_uniform_Ico
  have hae2 : ∀ᵐ w ∂tapeLaw ceModel 2, (w 0).2 false = ⊤ :=
    (h4.comp (h3.comp h0)).quasiMeasurePreserving.ae ae_duration_top
  filter_upwards [hae1, hae2] with w hw1 hw2
  exact ⟨hw1, hw2⟩

lemma myopicValue_ce : myopicValue ceModel ceArrivals rejection = 1 := by
  unfold myopicValue valueFor
  have hae : (fun w => pathRevenue ceModel ceArrivals
      (run ceModel ceArrivals (myopicOffer ceModel rejection) w 2)) =ᵐ[tapeLaw ceModel 2]
      fun _ => (1 : ℝ) := by
    filter_upwards [ae_tapeLaw_good] with w ⟨⟨hu0, hu1⟩, hd⟩
    exact myopic_pathRevenue_eq_one hu0 hu1 hd
  rw [integral_congr_ae hae, integral_const]
  simp [Measure.real]

lemma policyValue_opt_ce : policyValue ceModel ceArrivals optPolicy = 10 := by
  unfold policyValue valueFor
  have hae : (fun w => pathRevenue ceModel ceArrivals
      (run ceModel ceArrivals (offer ceModel optPolicy) w 2)) =ᵐ[tapeLaw ceModel 2]
      fun _ => (10 : ℝ) := by
    filter_upwards [ae_tapeLaw_good] with w ⟨⟨hu0, _⟩, _⟩
    exact opt_pathRevenue_eq_ten hu0
  rw [integral_congr_ae hae, integral_const]
  simp [Measure.real]

lemma revenue_ce_le (z : Bool) (S : Finset Bool) :
    revenue ceModel (ceModel.choice z) S ≤ if z then 10 else 1 := by
  unfold revenue
  rw [Finset.sum_subset (Finset.subset_univ S)]
  · rw [Fintype.sum_bool, meanRevenue_ce true, meanRevenue_ce false]
    dsimp [ceModel]
    by_cases hz : z ∈ S <;> cases z <;> norm_num [hz]
  · intro j _ hj
    have h0 : ceModel.choice z S (some j) = 0 :=
      (ceModel_valid.choice_law z).support S j hj
    rw [h0, mul_zero]

lemma pathRevenue_le_eleven (h : History Bool) :
    pathRevenue ceModel ceArrivals h ≤ 11 := by
  unfold pathRevenue
  rw [Fin.sum_univ_two]
  have h0 := revenue_ce_le false (h 0).2.1
  have h1 := revenue_ce_le true (h 1).2.1
  dsimp at h0 h1
  change revenue ceModel (ceModel.choice false) (h 0).2.1 +
    revenue ceModel (ceModel.choice true) (h 1).2.1 ≤ 11
  linarith

lemma policyValue_bddAbove : BddAbove (Set.range (policyValue ceModel ceArrivals)) := by
  refine ⟨11, ?_⟩
  rintro v ⟨π, rfl⟩
  unfold policyValue valueFor
  by_cases hint : Integrable (fun w => pathRevenue ceModel ceArrivals
      (run ceModel ceArrivals (offer ceModel π) w 2)) (tapeLaw ceModel 2)
  · calc ∫ w, pathRevenue ceModel ceArrivals (run ceModel ceArrivals (offer ceModel π) w 2) ∂tapeLaw ceModel 2
      _ ≤ ∫ _, (11 : ℝ) ∂tapeLaw ceModel 2 := by
        apply integral_mono hint (integrable_const 11)
        intro w
        exact pathRevenue_le_eleven _
      _ = 11 := by simp [Measure.real]
  · rw [integral_undef hint]
    norm_num

lemma optimalValue_ge_ten : 10 ≤ optimalValue ceModel ceArrivals := by
  unfold optimalValue
  rw [← policyValue_opt_ce]
  exact le_csSup policyValue_bddAbove ⟨optPolicy, rfl⟩

end GongReusable.Myopic

theorem solution : ¬ (∀ {P Z : Type} [Fintype P] {T : ℕ}
    (M : GongReusable.Myopic.Model P Z) (_hM : GongReusable.Myopic.Valid M)
    (x : GongReusable.Myopic.Arrivals Z T) (tie : GongReusable.Myopic.Policy P),
    (1 / 2 : ℝ) * GongReusable.Myopic.optimalValue M x ≤ GongReusable.Myopic.myopicValue M x tie) := by
  intro h
  have hce := h GongReusable.Myopic.ceModel GongReusable.Myopic.ceModel_valid
    GongReusable.Myopic.ceArrivals GongReusable.Myopic.rejection
  rw [GongReusable.Myopic.myopicValue_ce] at hce
  have hopt := GongReusable.Myopic.optimalValue_ge_ten
  linarith
