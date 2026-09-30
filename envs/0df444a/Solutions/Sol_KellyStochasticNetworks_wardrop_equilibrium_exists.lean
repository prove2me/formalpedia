-- Prove2me | solution 1 for KellyStochasticNetworks.wardrop_equilibrium_exists
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T23:11:53.014984+00:00
-- url     : https://prove2.me/submissions/1676a8d5-d7df-491e-83f2-b5b446447b22

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace KellyStochasticNetworks

/-- For monotone continuous `D`, `∫_y^{y+h} D ≤ h · D(y+h)` for every real `h`. -/
lemma wm_int_le (D : ℝ → ℝ) (hD : Continuous D) (hmono : Monotone D) (y h : ℝ) :
    ∫ u in y..(y + h), D u ≤ h * D (y + h) := by
  rcases le_total 0 h with hh | hh
  · have hle : y ≤ y + h := by linarith
    have := intervalIntegral.integral_mono_on hle (hD.intervalIntegrable (μ := MeasureTheory.volume) y (y + h))
      (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) y (y + h))
      (fun u hu => hmono hu.2 : ∀ u ∈ Set.Icc y (y + h), D u ≤ D (y + h))
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  · have hle : y + h ≤ y := by linarith
    have := intervalIntegral.integral_mono_on hle
      (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) (y + h) y)
      (hD.intervalIntegrable (μ := MeasureTheory.volume) (y + h) y)
      (fun u hu => hmono hu.1 : ∀ u ∈ Set.Icc (y + h) y, D (y + h) ≤ D u)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    rw [intervalIntegral.integral_symm]
    linarith

theorem wm_main {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (D : Fin J → ℝ → ℝ) (f : Fin Sd → ℝ)
    (hD : ∀ j, Continuous (D j)) (hmono : ∀ j, Monotone (D j))
    (x : Fin R → ℝ) (hx : x ∈ wardropFeasible s f)
    (hmin : ∀ z ∈ wardropFeasible s f, wardropObjective A D x ≤ wardropObjective A D z) :
    IsWardropEquilibrium A s D f x := by
  refine ⟨hx, fun r r' hs hxr => ?_⟩
  by_contra hlt
  push Not at hlt
  have hrr : r ≠ r' := by rintro rfl; exact lt_irrefl _ hlt
  set c : Fin J → ℝ := fun j => A j r' - A j r with hc
  set g : ℝ → ℝ := fun t => ∑ j, c j * D j (linkFlow A x j + t * c j) with hg
  have hg0 : g 0 < 0 := by
    have : g 0 = ∑ j, D j (linkFlow A x j) * A j r' - ∑ j, D j (linkFlow A x j) * A j r := by
      simp only [hg, hc, zero_mul, add_zero, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]; linarith
  have hgc : Continuous g := by
    simp only [hg]
    exact continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((hD j).comp (continuous_const.add (continuous_id.mul continuous_const)))
  have hev : ∀ᶠ t in nhds (0 : ℝ), g t < 0 := hgc.continuousAt.eventually_lt continuousAt_const hg0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set t := min (x r) (ε / 2) with ht
  have ht0 : 0 < t := lt_min hxr (by linarith)
  have htx : t ≤ x r := min_le_left _ _
  have hgt : g t < 0 := by
    apply hball
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- the shifted flow
  set z : Fin R → ℝ := fun k => x k + t * ((if k = r' then 1 else 0) - (if k = r then 1 else 0))
    with hz
  have hzlink : ∀ j, linkFlow A z j = linkFlow A x j + t * c j := by
    intro j
    simp only [linkFlow, hz, hc, mul_add, Finset.sum_add_distrib]
    congr 1
    simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hzfeas : z ∈ wardropFeasible s f := by
    refine ⟨fun k => ?_, fun σ => ?_⟩
    · simp only [hz]
      by_cases hk : k = r
      · subst hk; simp [hrr]; linarith
      · have := hx.1 k
        simp only [hk, if_false, sub_zero]
        split_ifs <;> nlinarith
    · rw [← hx.2 σ]
      simp only [hz, Finset.sum_add_distrib, add_eq_left, ← Finset.mul_sum,
        Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hs]; simp
  have hobj : wardropObjective A D z - wardropObjective A D x ≤ t * g t := by
    simp only [wardropObjective, ← Finset.sum_sub_distrib, hg, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [hzlink j, intervalIntegral.integral_interval_sub_left
      ((hD j).intervalIntegrable _ _) ((hD j).intervalIntegrable _ _)]
    have := wm_int_le (D j) (hD j) (hmono j) (linkFlow A x j) (t * c j)
    linarith
  have := hmin z hzfeas
  nlinarith

/-- The feasible set is nonempty: put the whole demand `f σ` on one route serving `σ`. -/
lemma we_nonempty {R Sd : ℕ} (s : Fin R → Fin Sd) (f : Fin Sd → ℝ)
    (hf : ∀ σ, 0 ≤ f σ) (hserved : ∀ σ, ∃ r, s r = σ) :
    (wardropFeasible s f).Nonempty := by
  choose rep hrep using hserved
  refine ⟨fun r => if rep (s r) = r then f (s r) else 0, fun r => ?_, fun σ => ?_⟩
  · dsimp only
    split_ifs
    · exact hf _
    · exact le_rfl
  · have h1 : ∀ r ∈ Finset.univ.filter (fun r => s r = σ),
        (if rep (s r) = r then f (s r) else 0) = if rep σ = r then f σ else 0 := by
      intro r hr
      rw [(Finset.mem_filter.mp hr).2]
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq]
    simp [hrep σ]

/-- The feasible set is closed and contained in the box `∏_r [0, f (s r)]`, hence compact. -/
lemma we_compact {R Sd : ℕ} (s : Fin R → Fin Sd) (f : Fin Sd → ℝ) :
    IsCompact (wardropFeasible s f) := by
  have hclosed : IsClosed (wardropFeasible s f) := by
    show IsClosed ({x : Fin R → ℝ | ∀ r, 0 ≤ x r} ∩
      {x | ∀ σ, (∑ r ∈ Finset.univ.filter (fun r => s r = σ), x r) = f σ})
    refine IsClosed.inter ?_ ?_
    · rw [Set.ofPred_forall]
      exact isClosed_iInter fun r => isClosed_le continuous_const (continuous_apply r)
    · rw [Set.ofPred_forall]
      exact isClosed_iInter fun σ =>
        isClosed_eq (continuous_finsetSum _ fun r _ => continuous_apply r) continuous_const
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun r => isCompact_Icc (a := (0 : ℝ)) (b := f (s r))) hclosed ?_
  intro x hx r _
  refine ⟨hx.1 r, ?_⟩
  rw [← hx.2 (s r)]
  exact Finset.single_le_sum (fun r' _ => hx.1 r')
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)

/-- The objective `∑_j ∫_0^{y_j} D_j` is continuous in the route flows. -/
lemma we_continuous {J R : ℕ} (A : Fin J → Fin R → ℝ) (D : Fin J → ℝ → ℝ)
    (hD : ∀ j, Continuous (D j)) : Continuous (wardropObjective A D) := by
  unfold wardropObjective
  refine continuous_finsetSum _ fun j _ => ?_
  have hprim : Continuous fun y : ℝ => ∫ u in (0:ℝ)..y, D j u := by
    rw [continuous_iff_continuousAt]
    intro y
    exact ((hD j).integral_hasStrictDerivAt 0 y).hasDerivAt.continuousAt
  have hlink : Continuous fun x : Fin R → ℝ => linkFlow A x j := by
    unfold linkFlow
    exact continuous_finsetSum _ fun r _ => continuous_const.mul (continuous_apply r)
  exact hprim.comp hlink

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (D : Fin J → ℝ → ℝ) (f : Fin Sd → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hD : ∀ j, Continuous (D j)) (hmono : ∀ j, Monotone (D j))
    (hf : ∀ σ, 0 ≤ f σ) (hserved : ∀ σ, ∃ r, s r = σ) :
    ∃ x : Fin R → ℝ, IsWardropEquilibrium A s D f x := by
  obtain ⟨x, hx, hmin⟩ := (we_compact s f).exists_isMinOn (we_nonempty s f hf hserved)
    (we_continuous A D hD).continuousOn
  exact ⟨x, wm_main A s D f hD hmono x hx fun z hz => isMinOn_iff.mp hmin z hz⟩
