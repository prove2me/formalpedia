-- Prove2me | solution 1 for HighDimStat.MetricEntropy.one_step_discretization_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T12:51:46.495285+00:00
-- url     : https://prove2.me/submissions/b28c526f-6214-48c3-9e39-cd0d63841e1f

import Mathlib
import Definitions.Def_HighDimStat_MetricEntropy_SubGaussianProcess
import Definitions.Def_HighDimStat_MetricEntropy_CoveringNumber
import Definitions.Def_HighDimStat_MetricEntropy_Diameter
import Definitions.Def_HighDimStat_MetricEntropy_IncrementSup
import Definitions.Def_HighDimStat_MetricEntropy_LocalIncrementSup


open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace DudleyProof

lemma integrable_iSup_finite {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [Nonempty ι] (P : Measure Ω) (X : ι → Ω → ℝ)
    (hX : ∀ i, Integrable (X i) P) :
    Integrable (fun ω => ⨆ i, X i ω) P := by
  classical
  have hi : Integrable ((Finset.univ : Finset ι).sup' Finset.univ_nonempty X) P :=
    Finset.sup'_induction Finset.univ_nonempty X (p := fun Z : Ω → ℝ => Integrable Z P)
      (fun _ hf _ hg => hf.sup hg) (fun i _ => hX i)
  convert hi using 1
  funext ω
  rw [Finset.sup'_apply, Finset.sup'_univ_eq_ciSup]

/-- The exponential-moment maximum estimate, without any independence assumption. -/
lemma finite_max_mgf_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i, Integrable (X i) P) (β c : ℝ) (hβ : 0 < β)
    (hExp : ∀ i, Integrable (fun ω => Real.exp (β * X i ω)) P)
    (hMGF : ∀ i, ∫ ω, Real.exp (β * X i ω) ∂P ≤ Real.exp c) :
    β * (∫ ω, (⨆ i, X i ω) ∂P) ≤ Real.log (Fintype.card ι) + c := by
  classical
  let M : Ω → ℝ := fun ω => ⨆ i, X i ω
  have hM : Integrable M P := integrable_iSup_finite P X hX
  have hsum : Integrable (fun ω => ∑ i, Real.exp (β * X i ω)) P :=
    integrable_finsetSum Finset.univ (fun i _ => hExp i)
  have hpoint (ω : Ω) : Real.exp (β * M ω) ≤ ∑ i, Real.exp (β * X i ω) := by
    obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => X i ω)
    change Real.exp (β * (⨆ i, X i ω)) ≤ _
    rw [← hi]
    exact Finset.single_le_sum (f := fun j => Real.exp (β * X j ω))
      (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)
  have hEM : Integrable (fun ω => Real.exp (β * M ω)) P :=
    hsum.mono' (Real.continuous_exp.comp_aestronglyMeasurable
      (hM.const_mul β).aestronglyMeasurable) (Filter.Eventually.of_forall (fun ω => by
        simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hpoint ω))
  have hJ := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (hM.const_mul β) hEM
  have hI : (∫ ω, Real.exp (β * M ω) ∂P) ≤
      (Fintype.card ι : ℝ) * Real.exp c := by
    calc
      _ ≤ ∫ ω, (∑ i, Real.exp (β * X i ω)) ∂P := integral_mono hEM hsum hpoint
      _ = ∑ i, ∫ ω, Real.exp (β * X i ω) ∂P :=
        integral_finsetSum Finset.univ (fun i _ => hExp i)
      _ ≤ ∑ _i : ι, Real.exp c := Finset.sum_le_sum (fun i _ => hMGF i)
      _ = _ := by simp
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have he : Real.exp (β * ∫ ω, M ω ∂P) ≤
      Real.exp (Real.log (Fintype.card ι) + c) := by
    rw [Real.exp_add, Real.exp_log hn]
    simpa only [integral_const_mul] using hJ.trans hI
  exact Real.exp_le_exp.mp he

end DudleyProof


open MeasureTheory

namespace DudleyProof
open HighDimStat.MetricEntropy

lemma exists_min_cover {T : Type*} [Fintype T] [PseudoMetricSpace T]
    (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ C : Finset T, C.card = CoveringNumber T δ ∧
      ∀ θ : T, ∃ θi ∈ C, dist θ θi ≤ δ := by
  classical
  unfold CoveringNumber
  change sInf {N : ℕ | ∃ C : Finset T, C.card = N ∧
    ∀ θ : T, ∃ θi ∈ C, dist θ θi ≤ δ} ∈
    {N : ℕ | ∃ C : Finset T, C.card = N ∧ ∀ θ : T, ∃ θi ∈ C, dist θ θi ≤ δ}
  apply csInf_mem
  exact ⟨Fintype.card T, Finset.univ, by simp, fun θ =>
    ⟨θ, Finset.mem_univ θ, by simpa using hδ⟩⟩

lemma dist_le_diameter {T : Type*} [Fintype T] [Nonempty T] [PseudoMetricSpace T]
    (x y : T) : dist x y ≤ Diameter T := by
  unfold Diameter
  exact le_ciSup (Set.finite_range (fun p : T × T => dist p.1 p.2)).bddAbove (x, y)

lemma diameter_nonneg {T : Type*} [Fintype T] [Nonempty T] [PseudoMetricSpace T] :
    0 ≤ Diameter T :=
  (dist_nonneg (x := Classical.choice inferInstance) (y := Classical.choice inferInstance)).trans
    (dist_le_diameter _ _)

lemma coveringNumber_le_one_of_diameter_nonpos {T : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] (δ : ℝ) (hδ : 0 ≤ δ) (hD : Diameter T ≤ 0) :
    CoveringNumber T δ ≤ 1 := by
  classical
  apply csInf_le (OrderBot.bddBelow _)
  refine ⟨{Classical.choice (inferInstance : Nonempty T)}, by simp, fun θ => ?_⟩
  refine ⟨Classical.choice inferInstance, by simp, ?_⟩
  exact (dist_le_diameter _ _).trans (hD.trans hδ)

lemma integrable_incrementSup {T Ω : Type*} [Fintype T] [Nonempty T]
    [MeasurableSpace Ω] (P : Measure Ω) (X : T → Ω → ℝ)
    (hX : ∀ θ, Integrable (X θ) P) : Integrable (IncrementSup X) P :=
  integrable_iSup_finite P (fun p : T × T => fun ω => X p.1 ω - X p.2 ω)
    (fun p => (hX p.1).sub (hX p.2))

lemma integrable_localIncrementSup {T Ω : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] [MeasurableSpace Ω] (P : Measure Ω) (X : T → Ω → ℝ)
    (hX : ∀ θ, Integrable (X θ) P) (δ : ℝ) (hδ : 0 ≤ δ) :
    Integrable (LocalIncrementSup X δ) P := by
  classical
  letI : Nonempty {p : T × T // dist p.1 p.2 ≤ δ} :=
    ⟨⟨(Classical.choice inferInstance, Classical.choice inferInstance), by simpa using hδ⟩⟩
  exact integrable_iSup_finite P
    (fun p : {p : T × T // dist p.1 p.2 ≤ δ} => fun ω => X p.1.1 ω - X p.1.2 ω)
    (fun p => (hX p.1.1).sub (hX p.1.2))

/-- The deterministic cover approximation used by both discretization and chaining. -/
lemma incrementSup_le_cover {T Ω : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] (X : T → Ω → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (C : Finset T) (hC : ∀ θ : T, ∃ θi ∈ C, dist θ θi ≤ δ) (ω : Ω) :
    IncrementSup X ω ≤ 2 * LocalIncrementSup X δ ω +
      (⨆ p : (↥C × ↥C), X p.1.1 ω - X p.2.1 ω) := by
  classical
  obtain ⟨a, ha, _⟩ := hC (Classical.choice inferInstance)
  letI : Nonempty ↥C := ⟨⟨a, ha⟩⟩
  letI : Nonempty {p : T × T // dist p.1 p.2 ≤ δ} :=
    ⟨⟨(a, a), by simpa using hδ⟩⟩
  unfold IncrementSup
  apply ciSup_le
  intro p
  obtain ⟨u, hu, hpu⟩ := hC p.1
  obtain ⟨v, hv, hpv⟩ := hC p.2
  have h1 : X p.1 ω - X u ω ≤ LocalIncrementSup X δ ω := by
    unfold LocalIncrementSup
    exact le_ciSup (f := fun q : {q : T × T // dist q.1 q.2 ≤ δ} =>
      X q.1.1 ω - X q.1.2 ω) (Set.finite_range _).bddAbove ⟨(p.1, u), hpu⟩
  have h2 : X v ω - X p.2 ω ≤ LocalIncrementSup X δ ω := by
    unfold LocalIncrementSup
    exact le_ciSup (f := fun q : {q : T × T // dist q.1 q.2 ≤ δ} =>
      X q.1.1 ω - X q.1.2 ω) (Set.finite_range _).bddAbove
      ⟨(v, p.2), by simpa [dist_comm] using hpv⟩
  have h3 : X u ω - X v ω ≤
      (⨆ q : (↥C × ↥C), X q.1.1 ω - X q.2.1 ω) :=
    le_ciSup (f := fun q : (↥C × ↥C) => X q.1.1 ω - X q.2.1 ω)
      (Set.finite_range _).bddAbove (⟨u, hu⟩, ⟨v, hv⟩)
  linarith

/-- One-step discretization, with the book's constant and hypotheses. -/
theorem one_step_discretization {T Ω : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : T → Ω → ℝ) (hSG : SubGaussianProcess P X) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδD : δ ≤ Diameter T) (hN : 10 ≤ CoveringNumber T δ) :
    ∫ ω, IncrementSup X ω ∂P ≤
      2 * (∫ ω, LocalIncrementSup X δ ω ∂P) +
      4 * Real.sqrt (Diameter T ^ 2 * Real.log (CoveringNumber T δ)) := by
  classical
  obtain ⟨C, hcard, hcover⟩ := exists_min_cover (T := T) δ hδ0
  have hC : C.Nonempty := by
    obtain ⟨a, ha, _⟩ := hcover (Classical.choice inferInstance)
    exact ⟨a, ha⟩
  letI : Nonempty ↥C := hC.coe_sort
  let D := Diameter T
  let L := Real.log (CoveringNumber T δ)
  let r := Real.sqrt (D ^ 2 * L)
  let β := r / D ^ 2
  let M : Ω → ℝ := fun ω => ⨆ p : (↥C × ↥C), X p.1.1 ω - X p.2.1 ω
  have hD : 0 < D := by
    by_contra h
    have := coveringNumber_le_one_of_diameter_nonpos δ hδ0 (le_of_not_gt h)
    omega
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < CoveringNumber T δ by omega))
  have hDs : 0 < D ^ 2 := sq_pos_of_pos hD
  have hr : 0 < r := Real.sqrt_pos.2 (mul_pos hDs hL)
  have hrsq : r ^ 2 = D ^ 2 * L := Real.sq_sqrt (mul_nonneg hDs.le hL.le)
  have hβ : 0 < β := div_pos hr hDs
  have hM : Integrable M P := integrable_iSup_finite P
    (fun p : (↥C × ↥C) => fun ω => X p.1.1 ω - X p.2.1 ω)
    (fun p => (hSG.1 p.1.1).sub (hSG.1 p.2.1))
  have hbound := finite_max_mgf_bound P
    (fun p : (↥C × ↥C) => fun ω => X p.1.1 ω - X p.2.1 ω)
    (fun p => (hSG.1 p.1.1).sub (hSG.1 p.2.1)) β (β ^ 2 * D ^ 2 / 2) hβ
    (fun p => hSG.2.2.1 p.1.1 p.2.1 β) (fun p => by
      apply (hSG.2.2.2 p.1.1 p.2.1 β).trans
      apply Real.exp_le_exp.mpr
      have hd := dist_le_diameter p.1.1 p.2.1
      have hs : dist p.1.1 p.2.1 ^ 2 ≤ D ^ 2 :=
        pow_le_pow_left₀ dist_nonneg hd 2
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs (sq_nonneg β)) (by norm_num))
  have hlog : Real.log (Fintype.card (↥C × ↥C)) = 2 * L := by
    simp only [Fintype.card_prod, Fintype.card_coe, Nat.cast_mul]
    rw [Real.log_mul (by exact_mod_cast hC.card_pos.ne') (by exact_mod_cast hC.card_pos.ne')]
    rw [hcard]
    ring
  have hcoeff : β ^ 2 * D ^ 2 / 2 = L / 2 := by
    dsimp [β]
    field_simp [ne_of_gt hD]
    nlinarith [hrsq]
  change β * (∫ ω, M ω ∂P) ≤ _ at hbound
  rw [hlog, hcoeff] at hbound
  have hmul := mul_le_mul_of_nonneg_left hbound hDs.le
  have heq : D ^ 2 * (β * (∫ ω, M ω ∂P)) = r * (∫ ω, M ω ∂P) := by
    dsimp [β]
    field_simp [ne_of_gt hD]
  rw [heq] at hmul
  have hnet : (∫ ω, M ω ∂P) ≤ 4 * r := by nlinarith [hrsq]
  have hlocal := integrable_localIncrementSup P X hSG.1 δ hδ0
  calc
    _ ≤ ∫ ω, (2 * LocalIncrementSup X δ ω + M ω) ∂P :=
      integral_mono (integrable_incrementSup P X hSG.1)
        ((hlocal.const_mul 2).add hM) (incrementSup_le_cover X δ hδ0 C hcover)
    _ = 2 * (∫ ω, LocalIncrementSup X δ ω ∂P) + (∫ ω, M ω ∂P) := by
      rw [integral_add (hlocal.const_mul 2) hM, integral_const_mul]
    _ ≤ _ := add_le_add le_rfl hnet

end DudleyProof

open HighDimStat.MetricEntropy
theorem solution {T Ω : Type*} [Fintype T] [Nonempty T]
    [PseudoMetricSpace T] [MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (X : T → Ω → ℝ) (hSG : SubGaussianProcess Prob X) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδD : δ ≤ Diameter T) (hN : 10 ≤ CoveringNumber T δ) :
    ∫ ω, IncrementSup X ω ∂Prob ≤
      2 * (∫ ω, LocalIncrementSup X δ ω ∂Prob) +
      4 * Real.sqrt (Diameter T ^ 2 * Real.log (CoveringNumber T δ)) := by
  exact DudleyProof.one_step_discretization X hSG δ hδ0 hδD hN

#print axioms solution
