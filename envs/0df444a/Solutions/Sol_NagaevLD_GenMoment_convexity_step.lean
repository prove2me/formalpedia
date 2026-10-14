-- Prove2me | solution 1 for NagaevLD.GenMoment.convexity_step
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T21:32:46.220995+00:00
-- url     : https://prove2.me/submissions/adffa66c-ac6b-425c-9399-7a8a170ef9b7

import Mathlib
import Definitions.Def_NagaevLD_GenMoment_Setting

open MeasureTheory ProbabilityTheory


namespace NagaevLD.GenMoment

/-- Tangent-type bounds for g with monotone derivative on [0,∞). -/
lemma gm_mvt (g g' : ℝ → ℝ) (hg : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (g' u) u)
    (hg'mono : MonotoneOn g' (Set.Ici 0)) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    g' a * (b - a) ≤ g b - g a ∧ g b - g a ≤ g' b * (b - a) := by
  rcases hab.eq_or_lt with h | h
  · subst h; simp
  have hcont : ContinuousOn g (Set.Icc a b) := fun u hu =>
    (hg u (le_trans ha hu.1)).continuousAt.continuousWithinAt
  have hder : ∀ u ∈ Set.Ioo a b, HasDerivAt g (g' u) u := fun u hu =>
    hg u (le_trans ha hu.1.le)
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope g g' h hcont hder
  have hba : 0 < b - a := by linarith
  have hgc : g b - g a = g' c * (b - a) := by
    rw [hceq]; field_simp
  have h1 : g' a ≤ g' c := hg'mono (Set.mem_Ici.2 ha) (Set.mem_Ici.2 (by linarith [hc.1]))
    hc.1.le
  have h2 : g' c ≤ g' b := hg'mono (Set.mem_Ici.2 (by linarith [hc.1]))
    (Set.mem_Ici.2 (by linarith)) hc.2.le
  constructor
  · rw [hgc]; exact mul_le_mul_of_nonneg_right h1 hba.le
  · rw [hgc]; exact mul_le_mul_of_nonneg_right h2 hba.le

theorem convexity_step_core (g g' : ℝ → ℝ) (hg : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (g' u) u)
    (hg'pos : ∀ u : ℝ, 0 ≤ u → 0 < g' u) (hg'mono : MonotoneOn g' (Set.Ici 0))
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 < x) (h : ℝ) (hh : h = g' (x / n)) :
    g (x / n) - g 0 ≤ g' (x / n) * (x / n) ∧
      Real.exp (-g 0) ≤ Real.exp (h * (x / n) - g (x / n)) := by
  have hs : 0 ≤ x / n := by positivity
  have := (gm_mvt g g' hg hg'mono 0 (x / n) le_rfl hs).2
  rw [sub_zero] at this
  refine ⟨this, ?_⟩
  rw [Real.exp_le_exp, hh]; linarith

theorem eq_2_47_core (g g' : ℝ → ℝ) (hg : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (g' u) u)
    (hg'pos : ∀ u : ℝ, 0 ≤ u → 0 < g' u) (hg'mono : MonotoneOn g' (Set.Ici 0))
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 < x) (h : ℝ) (hh : h = g' (x / n)) :
    IsGreatest ((fun u : ℝ => Real.exp (h * u - g u)) '' Set.Ici 0)
      (Real.exp (h * (x / n) - g (x / n))) := by
  have hs : 0 ≤ x / n := by positivity
  refine ⟨⟨x / n, Set.mem_Ici.2 hs, rfl⟩, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  simp only [Real.exp_le_exp]
  rw [Set.mem_Ici] at hu
  rcases le_total u (x / n) with hus | hus
  · have := (gm_mvt g g' hg hg'mono u (x / n) hu hus).2
    rw [hh]; nlinarith
  · have := (gm_mvt g g' hg hg'mono (x / n) u hs hus).1
    rw [hh]; nlinarith

theorem eq_2_45_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ) (hXm : ∀ j, Measurable (X j)) (hind : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (h : ℝ) (hh : 0 ≤ h)
    (hint : ∀ j, Integrable (fun ω => Real.exp (h * X j ω)) P) :
    P.real {ω | x ≤ NagaevLD.FukNagaev.S n X ω} ≤ Real.exp (-(h * x)) * ∏ j, ∫ ω, Real.exp (h * X j ω) ∂P := by
  have hS : (fun ω => NagaevLD.FukNagaev.S n X ω) = ∑ i, X i := by
    funext ω; simp [NagaevLD.FukNagaev.S, Finset.sum_apply]
  have hI := hind.integrable_exp_mul_sum (t := h) hXm (s := Finset.univ) (fun i _ => hint i)
  have := measure_ge_le_exp_mul_mgf (μ := P) (X := ∑ i, X i) x hh hI
  rw [hind.mgf_sum hXm] at this
  have e : {ω | x ≤ NagaevLD.FukNagaev.S n X ω} = {ω | x ≤ (∑ i, X i) ω} := by
    rw [← hS]
  rw [e]
  convert this using 2
  · ring
  · rfl

theorem eq_2_46_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ j, Measurable (X j)) (g : ℝ → ℝ) (j : Fin n)
    (hbg : IntegrableOn (fun ω => Real.exp (g (X j ω))) {ω | 0 ≤ X j ω} P)
    (h M : ℝ) (hh : 0 ≤ h) (hM : ∀ u : ℝ, 0 ≤ u → Real.exp (h * u - g u) ≤ M) :
    (∫ ω, Real.exp (h * X j ω) ∂P) =
        (∫ ω in {ω | X j ω < 0}, Real.exp (h * X j ω) ∂P) +
          (∫ ω in {ω | 0 ≤ X j ω},
            Real.exp (h * X j ω - g (X j ω)) * Real.exp (g (X j ω)) ∂P) ∧
      (∫ ω, Real.exp (h * X j ω) ∂P)
        ≤ (∫ ω in {ω | X j ω < 0}, Real.exp (h * X j ω) ∂P) + bg P X g j * M := by
  have hmeasS : MeasurableSet {ω | 0 ≤ X j ω} := measurableSet_le measurable_const (hXm j)
  have hmeasN : MeasurableSet {ω | X j ω < 0} := measurableSet_lt (hXm j) measurable_const
  have hfm : Measurable (fun ω => Real.exp (h * X j ω)) :=
    (measurable_const.mul (hXm j)).exp
  have hpt : ∀ ω, Real.exp (h * X j ω - g (X j ω)) * Real.exp (g (X j ω))
      = Real.exp (h * X j ω) := by
    intro ω; rw [← Real.exp_add]; ring_nf
  -- integrability on the nonneg part
  have hIpos : IntegrableOn (fun ω => Real.exp (h * X j ω)) {ω | 0 ≤ X j ω} P := by
    refine Integrable.mono' (hbg.const_mul M) hfm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' hmeasS).2 (Filter.Eventually.of_forall ?_)
    intro ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← hpt ω]
    exact mul_le_mul_of_nonneg_right (hM _ hω) (Real.exp_pos _).le
  have hIneg : IntegrableOn (fun ω => Real.exp (h * X j ω)) {ω | X j ω < 0} P := by
    refine Integrable.mono' (integrable_const (1:ℝ)) hfm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' hmeasN).2 (Filter.Eventually.of_forall ?_)
    intro ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonneg_of_nonpos hh (le_of_lt hω)
  have hcompl : {ω | X j ω < 0}ᶜ = {ω | 0 ≤ X j ω} := by
    ext ω; simp
  have hsplit : (∫ ω, Real.exp (h * X j ω) ∂P) =
      (∫ ω in {ω | X j ω < 0}, Real.exp (h * X j ω) ∂P) +
        (∫ ω in {ω | 0 ≤ X j ω}, Real.exp (h * X j ω) ∂P) := by
    rw [← hcompl]
    exact (integral_add_compl hmeasN (by
      have := hIneg.union hIpos
      rwa [← hcompl, Set.union_compl_self, integrableOn_univ] at this)).symm
  have hEq : (∫ ω, Real.exp (h * X j ω) ∂P) =
        (∫ ω in {ω | X j ω < 0}, Real.exp (h * X j ω) ∂P) +
          (∫ ω in {ω | 0 ≤ X j ω},
            Real.exp (h * X j ω - g (X j ω)) * Real.exp (g (X j ω)) ∂P) := by
    rw [hsplit]; simp only [hpt]
  refine ⟨hEq, ?_⟩
  rw [hsplit]
  gcongr
  unfold bg
  rw [mul_comm, ← integral_const_mul]
  refine setIntegral_mono_on hIpos (hbg.const_mul M) hmeasS ?_
  intro ω hω
  rw [← hpt ω]
  exact mul_le_mul_of_nonneg_right (hM _ hω) (Real.exp_pos _).le

theorem eq_2_48_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ) (hXm : ∀ j, Measurable (X j))
    (g g' : ℝ → ℝ) (hg : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (g' u) u)
    (hg'pos : ∀ u : ℝ, 0 ≤ u → 0 < g' u) (hg'mono : MonotoneOn g' (Set.Ici 0)) (j : Fin n) (x : ℝ) (hx : 0 < x) (h : ℝ) (hh : h = g' (x / n)) :
    ∫ ω in {ω | X j ω < 0}, Real.exp (h * X j ω) ∂P
      ≤ Real.exp (g 0 + h * (x / n) - g (x / n))
          * ∫ ω in {ω | X j ω < 0}, Real.exp (h * X j ω) ∂P := by
  have hc := (convexity_step_core g g' hg hg'pos hg'mono n hn x hx h hh).1
  have h1 : 1 ≤ Real.exp (g 0 + h * (x / n) - g (x / n)) := by
    rw [Real.one_le_exp_iff, hh]; linarith
  have h0 : 0 ≤ ∫ ω in {ω | X j ω < 0}, Real.exp (h * X j ω) ∂P :=
    setIntegral_nonneg (measurableSet_lt (hXm j) measurable_const)
      (fun _ _ => (Real.exp_pos _).le)
  nlinarith

theorem per_factor_bound_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ) (hXm : ∀ j, Measurable (X j))
    (g g' : ℝ → ℝ) (hg : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (g' u) u)
    (hg'pos : ∀ u : ℝ, 0 ≤ u → 0 < g' u) (hg'mono : MonotoneOn g' (Set.Ici 0)) (j : Fin n)
    (hbg : IntegrableOn (fun ω => Real.exp (g (X j ω))) {ω | 0 ≤ X j ω} P)
    (x : ℝ) (hx : 0 < x) (h : ℝ) (hh : h = g' (x / n)) :
    ∫ ω, Real.exp (h * X j ω) ∂P
      ≤ (bj P X g g' j (x / n) + bg P X g j) * Real.exp (h * (x / n) - g (x / n)) := by
  have hs : 0 ≤ x / n := by positivity
  have hhnn : 0 ≤ h := by rw [hh]; exact (hg'pos _ hs).le
  have hG := eq_2_47_core g g' hg hg'pos hg'mono n hn x hx h hh
  have hM : ∀ u : ℝ, 0 ≤ u → Real.exp (h * u - g u) ≤ Real.exp (h * (x / n) - g (x / n)) :=
    fun u hu => hG.2 ⟨u, Set.mem_Ici.2 hu, rfl⟩
  have h46 := (eq_2_46_core P n X hXm g j hbg h _ hhnn hM).2
  have h48 := eq_2_48_core P n hn X hXm g g' hg hg'pos hg'mono j x hx h hh
  have hbj : bj P X g g' j (x / n) * Real.exp (h * (x / n) - g (x / n))
      = Real.exp (g 0 + h * (x / n) - g (x / n))
          * ∫ ω in {ω | X j ω < 0}, Real.exp (h * X j ω) ∂P := by
    unfold bj
    rw [← hh, show g 0 + h * (x / n) - g (x / n) = g 0 + (h * (x / n) - g (x / n)) by ring,
      Real.exp_add]
    ring
  rw [add_mul, hbj]
  linarith

theorem theorem_2_5_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0 < n) (X : Fin n → Ω → ℝ) (hXm : ∀ j, Measurable (X j)) (hind : iIndepFun X P)
    (g g' : ℝ → ℝ) (hg : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (g' u) u)
    (hg'pos : ∀ u : ℝ, 0 ≤ u → 0 < g' u) (hg'mono : MonotoneOn g' (Set.Ici 0))
    (hbg : ∀ j, IntegrableOn (fun ω => Real.exp (g (X j ω))) {ω | 0 ≤ X j ω} P)
    (x : ℝ) (hx : 0 < x) :
    P.real {ω | x ≤ NagaevLD.FukNagaev.S n X ω}
      ≤ (∏ j, (bj P X g g' j (x / n) + bg P X g j)) * Real.exp (-(n * g (x / n))) := by
  set h := g' (x / n) with hh
  have hs : 0 ≤ x / n := by positivity
  have hhnn : 0 ≤ h := (hg'pos _ hs).le
  have hG := eq_2_47_core g g' hg hg'pos hg'mono n hn x hx h hh
  have hM : ∀ u : ℝ, 0 ≤ u → Real.exp (h * u - g u) ≤ Real.exp (h * (x / n) - g (x / n)) :=
    fun u hu => hG.2 ⟨u, Set.mem_Ici.2 hu, rfl⟩
  -- integrability of exp(h X_j)
  have hint : ∀ j, Integrable (fun ω => Real.exp (h * X j ω)) P := by
    intro j
    have hmeasS : MeasurableSet {ω | 0 ≤ X j ω} := measurableSet_le measurable_const (hXm j)
    have hfm : Measurable (fun ω => Real.exp (h * X j ω)) :=
      (measurable_const.mul (hXm j)).exp
    have hIpos : IntegrableOn (fun ω => Real.exp (h * X j ω)) {ω | 0 ≤ X j ω} P := by
      refine Integrable.mono' ((hbg j).const_mul (Real.exp (h * (x / n) - g (x / n))))
        hfm.aestronglyMeasurable ?_
      refine (ae_restrict_iff' hmeasS).2 (Filter.Eventually.of_forall ?_)
      intro ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have : Real.exp (h * X j ω) = Real.exp (h * X j ω - g (X j ω)) * Real.exp (g (X j ω)) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]
      exact mul_le_mul_of_nonneg_right (hM _ hω) (Real.exp_pos _).le
    have hIneg : IntegrableOn (fun ω => Real.exp (h * X j ω)) {ω | 0 ≤ X j ω}ᶜ P := by
      refine Integrable.mono' (integrable_const (1:ℝ)) hfm.aestronglyMeasurable ?_
      refine (ae_restrict_iff' hmeasS.compl).2 (Filter.Eventually.of_forall ?_)
      intro ω hω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      exact mul_nonpos_of_nonneg_of_nonpos hhnn (le_of_lt hω)
    have := hIpos.union hIneg
    rwa [Set.union_compl_self, integrableOn_univ] at this
  have h45 := eq_2_45_core P n hn X hXm hind x hx h hhnn hint
  have hpf : ∀ j, ∫ ω, Real.exp (h * X j ω) ∂P
      ≤ (bj P X g g' j (x / n) + bg P X g j) * Real.exp (h * (x / n) - g (x / n)) :=
    fun j => per_factor_bound_core P n hn X hXm g g' hg hg'pos hg'mono j (hbg j) x hx h hh
  have hprod : ∏ j, ∫ ω, Real.exp (h * X j ω) ∂P
      ≤ ∏ j, ((bj P X g g' j (x / n) + bg P X g j) * Real.exp (h * (x / n) - g (x / n))) :=
    Finset.prod_le_prod (fun j _ => integral_nonneg (fun _ => (Real.exp_pos _).le))
      (fun j _ => hpf j)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_nat_mul] at hprod
  calc P.real {ω | x ≤ NagaevLD.FukNagaev.S n X ω}
      ≤ Real.exp (-(h * x)) * ∏ j, ∫ ω, Real.exp (h * X j ω) ∂P := h45
    _ ≤ Real.exp (-(h * x)) * ((∏ j, (bj P X g g' j (x / n) + bg P X g j)) *
          Real.exp (n * (h * (x / n) - g (x / n)))) :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = (∏ j, (bj P X g g' j (x / n) + bg P X g j)) * Real.exp (-(n * g (x / n))) := by
        have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        field_simp
        ring

end NagaevLD.GenMoment

open NagaevLD.GenMoment


theorem solution (g g' : ℝ → ℝ) (hg : ∀ u : ℝ, 0 ≤ u → HasDerivAt g (g' u) u)
    (hg'pos : ∀ u : ℝ, 0 ≤ u → 0 < g' u) (hg'mono : MonotoneOn g' (Set.Ici 0))
    (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 < x) (h : ℝ) (hh : h = g' (x / n)) :
    g (x / n) - g 0 ≤ g' (x / n) * (x / n) ∧
      Real.exp (-g 0) ≤ Real.exp (h * (x / n) - g (x / n)) := by
  exact convexity_step_core g g' hg hg'pos hg'mono n hn x hx h hh
