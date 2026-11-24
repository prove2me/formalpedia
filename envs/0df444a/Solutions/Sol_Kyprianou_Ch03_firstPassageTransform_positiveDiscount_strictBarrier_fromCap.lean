-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassageTransform_positiveDiscount_strictBarrier_fromCap
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:42:49.888414+00:00
-- url     : https://prove2.me/submissions/d0bf2f53-7694-4887-a080-bddcc8001df3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes

open MeasureTheory AvramDividend.Classical Filter Topology Set
open scoped NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
`T → ∞` limit of the capped Esscher identity → first-passage Laplace transform.
-/

namespace Kyprianou.Ch03

private lemma firstHittingIoi_le_of_mem
    {Omega : Type} (X : NNReal → Omega → Real) (x : Real) (ω : Omega)
    {t : NNReal} (ht : 0 < t) (htmem : X t ω ∈ Ioi x) :
    firstHittingTime X (Ioi x) ω ≤ (t : WithTop NNReal) := by
  refine csInf_le (OrderBot.bddBelow _) ?_
  exact ⟨t, ⟨ht, htmem⟩, rfl⟩

private lemma firstHittingIoi_eq_top_not_mem
    {Omega : Type} (X : NNReal → Omega → Real) (x : Real) (ω : Omega)
    (htop : firstHittingTime X (Ioi x) ω = ⊤) {t : NNReal} (ht : 0 < t) :
    X t ω ∉ Ioi x := by
  intro htmem
  have hle := firstHittingIoi_le_of_mem X x ω ht htmem
  rw [htop] at hle
  exact WithTop.not_top_le_coe t hle

private lemma firstHittingIoi_eq_top_le
    {Omega : Type} (X : NNReal → Omega → Real) (x : Real) (ω : Omega)
    (htop : firstHittingTime X (Ioi x) ω = ⊤)
    (hX0 : X 0 ω = 0) (hx : 0 ≤ x) (t : NNReal) :
    X t ω ≤ x := by
  by_cases ht : 0 < t
  · exact not_lt.mp (firstHittingIoi_eq_top_not_mem X x ω htop ht)
  · have ht0 : t = 0 := le_antisymm (not_lt.mp ht) bot_le
    simpa [ht0, hX0] using hx

private lemma le_barrier_before_selector
    {Omega : Type}
    (X : NNReal → Omega → Real) (x : Real) (ω : Omega)
    (finiteTime : Omega → NNReal)
    (hfin : firstHittingTime X (Ioi x) ω != ⊤ →
      firstHittingTime X (Ioi x) ω = (finiteTime ω : WithTop NNReal))
    (hX0 : X 0 ω = 0) (hx : 0 ≤ x) (T : NNReal)
    (hnot : ¬ (firstHittingTime X (Ioi x) ω ≠ ⊤ ∧ finiteTime ω ≤ T)) :
    X T ω ≤ x := by
  by_cases htop : firstHittingTime X (Ioi x) ω = ⊤
  · exact firstHittingIoi_eq_top_le X x ω htop hX0 hx T
  · have hbne : firstHittingTime X (Ioi x) ω != ⊤ := by
      simpa [bne_iff_ne] using htop
    have hτ : firstHittingTime X (Ioi x) ω = (finiteTime ω : WithTop NNReal) :=
      hfin hbne
    have hgt : ¬ finiteTime ω ≤ T := fun hle => hnot ⟨htop, hle⟩
    by_cases hT0 : T = 0
    · simpa [hT0, hX0] using hx
    · have hTpos : 0 < T := lt_of_le_of_ne bot_le (Ne.symm hT0)
      by_contra hXt
      have htmem : X T ω ∈ Ioi x := lt_of_not_ge hXt
      have hle := firstHittingIoi_le_of_mem X x ω hTpos htmem
      rw [hτ] at hle
      exact hgt (WithTop.coe_le_coe.mp hle)

private lemma capIntegrand_nonneg
    {Omega : Type} (X : NNReal → Omega → Real) (x phi q : Real) (ω : Omega)
    (finiteTime : Omega → NNReal) (T : NNReal) :
    0 ≤ (if firstHittingTime X (Ioi x) ω ≠ ⊤ ∧ finiteTime ω ≤ T
      then Real.exp (phi * x - q * (finiteTime ω : Real))
      else Real.exp (phi * X T ω - q * (T : Real))) := by
  split_ifs <;> exact (Real.exp_pos _).le

private lemma capIntegrand_le_exp
    {Omega : Type}
    (X : NNReal → Omega → Real) (x phi q : Real) (ω : Omega)
    (finiteTime : Omega → NNReal)
    (hfin : firstHittingTime X (Ioi x) ω != ⊤ →
      firstHittingTime X (Ioi x) ω = (finiteTime ω : WithTop NNReal))
    (hX0 : X 0 ω = 0) (hx : 0 ≤ x) (hφ : 0 ≤ phi) (hq : 0 ≤ q) (T : NNReal) :
    (if firstHittingTime X (Ioi x) ω ≠ ⊤ ∧ finiteTime ω ≤ T
      then Real.exp (phi * x - q * (finiteTime ω : Real))
      else Real.exp (phi * X T ω - q * (T : Real))) ≤
      Real.exp (phi * x) := by
  by_cases hcond : firstHittingTime X (Ioi x) ω ≠ ⊤ ∧ finiteTime ω ≤ T
  · rw [if_pos hcond]
    have : phi * x - q * (finiteTime ω : Real) ≤ phi * x :=
      sub_le_self _ (mul_nonneg hq (NNReal.coe_nonneg _))
    exact Real.exp_le_exp.mpr this
  · rw [if_neg hcond]
    have hXT : X T ω ≤ x :=
      le_barrier_before_selector X x ω finiteTime hfin hX0 hx T hcond
    have : phi * X T ω - q * (T : Real) ≤ phi * x := by
      have h1 : phi * X T ω ≤ phi * x := mul_le_mul_of_nonneg_left hXT hφ
      have h2 : 0 ≤ q * (T : Real) := mul_nonneg hq (NNReal.coe_nonneg _)
      linarith
    exact Real.exp_le_exp.mpr this

private lemma eventually_nat_ge_nnreal (t : NNReal) :
    ∀ᶠ n : ℕ in atTop, t ≤ (n : NNReal) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have : ∀ᶠ n : ℕ in atTop, (t : ℝ) ≤ (n : ℝ) :=
    h.eventually (eventually_ge_atTop (t : ℝ))
  filter_upwards [this] with n hn
  exact NNReal.coe_le_coe.mp hn

private lemma tendsto_exp_phi_x_sub_q_n
    (phi x q : Real) (hq : 0 < q) :
    Tendsto (fun n : ℕ => Real.exp (phi * x - q * (n : Real))) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hmul : Tendsto (fun n : ℕ => (n : ℝ) * q) atTop atTop :=
    hnat.atTop_mul_const hq
  have hneg : Tendsto (fun n : ℕ => -((n : ℝ) * q)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hmul
  have hlin : Tendsto (fun n : ℕ => phi * x - q * (n : ℝ)) atTop atBot := by
    have h' := tendsto_atBot_add_const_left atTop (phi * x) hneg
    convert h' using 1
    ext n
    ring
  exact Real.tendsto_exp_atBot.comp hlin

private lemma capIntegrand_tendsto
    {Omega : Type}
    (X : NNReal → Omega → Real) (x phi q : Real) (ω : Omega)
    (finiteTime : Omega → NNReal)
    (_hfin : firstHittingTime X (Ioi x) ω != ⊤ →
      firstHittingTime X (Ioi x) ω = (finiteTime ω : WithTop NNReal))
    (hX0 : X 0 ω = 0) (hx : 0 ≤ x) (hφ : 0 ≤ phi) (hq : 0 < q) :
    Tendsto
      (fun n : ℕ =>
        if firstHittingTime X (Ioi x) ω ≠ ⊤ ∧ finiteTime ω ≤ (n : NNReal)
        then Real.exp (phi * x - q * (finiteTime ω : Real))
        else Real.exp (phi * X n ω - q * (n : Real)))
      atTop
      (𝓝 (if firstHittingTime X (Ioi x) ω = ⊤
        then (0 : Real)
        else Real.exp (phi * x - q * (finiteTime ω : Real)))) := by
  by_cases htop : firstHittingTime X (Ioi x) ω = ⊤
  · -- Rewrite both the sequence and the limit using `htop`.
    have hseq :
        (fun n : ℕ =>
          if firstHittingTime X (Ioi x) ω ≠ ⊤ ∧ finiteTime ω ≤ (n : NNReal)
          then Real.exp (phi * x - q * (finiteTime ω : Real))
          else Real.exp (phi * X (n : NNReal) ω - q * (n : Real))) =
          fun n : ℕ => Real.exp (phi * X (n : NNReal) ω - q * (n : Real)) := by
      funext n
      have : ¬ (firstHittingTime X (Ioi x) ω ≠ ⊤ ∧ finiteTime ω ≤ (n : NNReal)) :=
        fun h => h.1 htop
      rw [if_neg this]
    rw [hseq, if_pos htop]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds (tendsto_exp_phi_x_sub_q_n phi x q hq)
      (fun n => (Real.exp_pos _).le)
      (fun n => ?_)
    · have hXT : X (n : NNReal) ω ≤ x :=
        firstHittingIoi_eq_top_le X x ω htop hX0 hx (n : NNReal)
      have : phi * X (n : NNReal) ω - q * (n : Real) ≤
          phi * x - q * (n : Real) := by
        linarith [mul_le_mul_of_nonneg_left hXT hφ]
      exact Real.exp_le_exp.mpr this
  · rw [if_neg htop]
    have hEv := eventually_nat_ge_nnreal (finiteTime ω)
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hEv] with n hn
    have hcond : firstHittingTime X (Ioi x) ω ≠ ⊤ ∧ finiteTime ω ≤ (n : NNReal) :=
      ⟨htop, hn⟩
    rw [if_pos hcond]

end Kyprianou.Ch03

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega)))
    (q : Real) (hq : 0 < q)
    (phi : Real)
    (hRoot : 0 ≤ phi ∧ L.ψ phi = q ∧
      (∀ theta : Real, 0 ≤ theta → L.ψ theta = q → theta ≤ phi))
    (x : Real) (hx : 0 < x)
    (finiteTime : Omega → NNReal)
    (hfin : ∀ omega,
      firstHittingTime L.X (Set.Ioi x) omega != ⊤ →
        firstHittingTime L.X (Set.Ioi x) omega =
          (finiteTime omega : WithTop NNReal))
    (hCap : ∀ T : NNReal,
      (∫ omega,
        (if firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ ∧
            finiteTime omega ≤ T
          then Real.exp (phi * x - q * (finiteTime omega : Real))
          else Real.exp (phi * L.X T omega - q * (T : Real))) ∂P) = 1)
    (hCreep : ∀ᵐ omega ∂P,
      firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ →
        L.X (finiteTime omega) omega = x) :
    (∫ omega,
      if firstHittingTime L.X (Set.Ioi x) omega = ⊤
      then (0 : Real)
      else Real.exp (-q * (finiteTime omega : Real)) ∂P) =
      Real.exp (-phi * x) := by
  have _ := hNotDecreasing
  have _ := hCreep
  have hφ : 0 ≤ phi := hRoot.1
  have hx0 : 0 ≤ x := hx.le
  have hq0 : 0 ≤ q := hq.le
  let F : ℕ → Omega → ℝ := fun n ω =>
    if firstHittingTime L.X (Ioi x) ω ≠ ⊤ ∧ finiteTime ω ≤ (n : NNReal)
    then Real.exp (phi * x - q * (finiteTime ω : Real))
    else Real.exp (phi * L.X n ω - q * (n : Real))
  let fLim : Omega → ℝ := fun ω =>
    if firstHittingTime L.X (Ioi x) ω = ⊤
    then (0 : Real)
    else Real.exp (phi * x - q * (finiteTime ω : Real))
  let g : Omega → ℝ := fun ω =>
    if firstHittingTime L.X (Ioi x) ω = ⊤
    then (0 : Real)
    else Real.exp (-q * (finiteTime ω : Real))
  have hFn : ∀ n, ∫ ω, F n ω ∂P = 1 := fun n => hCap (n : NNReal)
  have hF_nonneg : ∀ n ω, 0 ≤ F n ω := fun n ω =>
    capIntegrand_nonneg L.X x phi q ω finiteTime n
  have hF_le : ∀ n ω, F n ω ≤ Real.exp (phi * x) := fun n ω =>
    capIntegrand_le_exp L.X x phi q ω finiteTime (hfin ω) (L.X_zero ω) hx0 hφ hq0 n
  have hF_int : ∀ n, Integrable (F n) P := fun n =>
    integrable_of_integral_eq_one (hFn n)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (fLim ω)) :=
    Eventually.of_forall fun ω =>
      capIntegrand_tendsto L.X x phi q ω finiteTime (hfin ω) (L.X_zero ω) hx0 hφ hq
  have hbound_int : Integrable (fun _ : Omega => Real.exp (phi * x)) P :=
    integrable_const _
  have hDCT :
      Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 (∫ ω, fLim ω ∂P)) :=
    tendsto_integral_of_dominated_convergence
      (fun _ => Real.exp (phi * x))
      (fun n => (hF_int n).aestronglyMeasurable)
      hbound_int
      (fun n => Eventually.of_forall fun ω => by
        change ‖F n ω‖ ≤ Real.exp (phi * x)
        rw [Real.norm_of_nonneg (hF_nonneg n ω)]
        exact hF_le n ω)
      hlim
  have hconst : Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 (1 : ℝ)) := by
    convert tendsto_const_nhds (x := (1 : ℝ)) using 1
    ext n
    exact hFn n
  have hfLim_one : (∫ ω, fLim ω ∂P) = 1 := tendsto_nhds_unique hDCT hconst
  have hfactor : fLim = fun ω => Real.exp (phi * x) * g ω := by
    funext ω
    by_cases htop : firstHittingTime L.X (Ioi x) ω = ⊤
    · simp [fLim, g, htop]
    · simp only [fLim, g, htop, ↓reduceIte]
      have : phi * x - q * (finiteTime ω : Real) =
          phi * x + (-q * (finiteTime ω : Real)) := by ring
      rw [this, Real.exp_add]
  have hprod : (∫ ω, fLim ω ∂P) = Real.exp (phi * x) * ∫ ω, g ω ∂P := by
    rw [hfactor, integral_const_mul]
  have hgoal : (∫ ω, g ω ∂P) = Real.exp (-phi * x) := by
    have h : (1 : ℝ) = Real.exp (phi * x) * ∫ ω, g ω ∂P := by
      rw [← hfLim_one, hprod]
    have hne : Real.exp (phi * x) ≠ 0 := Real.exp_ne_zero _
    apply mul_left_cancel₀ hne
    rw [← h, ← Real.exp_add]
    ring_nf
    exact (Real.exp_zero).symm
  simpa [g] using hgoal
