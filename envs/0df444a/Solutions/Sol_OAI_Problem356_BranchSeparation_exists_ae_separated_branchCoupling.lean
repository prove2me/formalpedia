-- Prove2me | solution 1 for OAI.Problem356.BranchSeparation.exists_ae_separated_branchCoupling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:18:23.014523+00:00
-- url     : https://prove2.me/submissions/1eee21bf-996a-43d8-9490-14a995fcaa4b

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation

open OAI OAI.Problem356 OAI.Problem356.BranchSeparation
open MeasureTheory Set
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

theorem pb_sep {α ι : Type*} [MetricSpace α] [Finite ι]
    (K : ι → Set α) (hcompact : ∀ i, IsCompact (K i))
    (hdisjoint : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, eta ≤ dist x y := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  have hpair : ∀ p : ι × ι, ∃ e : ℝ, 0 < e ∧ (p.1 ≠ p.2 → ∀ x ∈ K p.1, ∀ y ∈ K p.2, e ≤ dist x y) := by
    rintro ⟨i, j⟩
    by_cases hij : i = j
    · exact ⟨1, one_pos, fun h => absurd hij h⟩
    · obtain ⟨r, hr, hr'⟩ := Metric.exists_pos_forall_lt_edist (hcompact i) (hcompact j).isClosed (hdisjoint hij)
      refine ⟨r, by exact_mod_cast hr, fun _ x hx y hy => ?_⟩
      have := hr' x hx y hy
      rw [edist_dist] at this
      rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff'] at this
      have h2 := this.1
      exact h2.le
  choose e he hesep using hpair
  obtain ⟨p0, hp0⟩ := Finite.exists_min e
  refine ⟨e p0, he p0, fun i j hij x hx y hy => le_trans (hp0 (i, j)) (hesep (i, j) hij x hx y hy)⟩

theorem solution
    {nu : Measure E3} {K : Set E3} (hK : IsCompact K)
    (hnu : ∀ᵐ x ∂nu, x ∈ K) {H : Fin 4 → E3 → E3}
    (hH : ∀ i, Measurable (H i)) (hcont : ∀ i, ContinuousOn (H i) K)
    (hdisjoint : Pairwise (fun i j => Disjoint (components K H i) (components K H j))) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ᵐ t ∂branchCoupling nu (H 0) (H 1) (H 2) (H 3),
        CoulombEstimates.Separated eta t := by
  have hcomp : ∀ i, IsCompact (components K H i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hK
    · exact hK.image_of_continuousOn (hcont j)
  obtain ⟨eta, heta, hsep⟩ := pb_sep (components K H) hcomp hdisjoint
  refine ⟨eta, heta, ?_⟩
  have hc0 : ∀ x ∈ K, x ∈ components K H 0 := fun x hx => hx
  have hcs : ∀ (j : Fin 4), ∀ x ∈ K, H j x ∈ components K H j.succ :=
    fun j x hx => ⟨x, hx, rfl⟩
  have hmeas : MeasurableSet {t : Triple | CoulombEstimates.Separated eta t} := by
    apply IsClosed.measurableSet
    unfold CoulombEstimates.Separated
    simp only [Set.ofPred_and]
    exact (isClosed_le continuous_const (by fun_prop : Continuous fun t : Triple => dist t.1 t.2.1)).inter
      ((isClosed_le continuous_const (by fun_prop : Continuous fun t : Triple => dist t.1 t.2.2)).inter
      (isClosed_le continuous_const (by fun_prop : Continuous fun t : Triple => dist t.2.1 t.2.2)))
  apply pb_ae_branchCoupling nu (hH 0) (hH 1) (hH 2) (hH 3) hmeas
  · rintro x y z ⟨h1, h2, h3⟩
    refine ⟨h3, ?_, ?_⟩
    · rwa [dist_comm]
    · rwa [dist_comm]
  · filter_upwards [hnu] with x hx
    refine ⟨hsep 0 (Fin.succ 0) (by decide) _ (hc0 x hx) _ (hcs 0 x hx),
      hsep 0 (Fin.succ 1) (by decide) _ (hc0 x hx) _ (hcs 1 x hx),
      hsep (Fin.succ 0) (Fin.succ 1) (by decide) _ (hcs 0 x hx) _ (hcs 1 x hx)⟩
  · filter_upwards [hnu] with x hx
    refine ⟨hsep 0 (Fin.succ 2) (by decide) _ (hc0 x hx) _ (hcs 2 x hx),
      hsep 0 (Fin.succ 3) (by decide) _ (hc0 x hx) _ (hcs 3 x hx),
      hsep (Fin.succ 2) (Fin.succ 3) (by decide) _ (hcs 2 x hx) _ (hcs 3 x hx)⟩

