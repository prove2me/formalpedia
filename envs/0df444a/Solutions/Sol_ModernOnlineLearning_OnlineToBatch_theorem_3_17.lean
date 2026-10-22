-- Prove2me | solution 1 for ModernOnlineLearning.OnlineToBatch.theorem_3_17
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T06:00:05.687422+00:00
-- url     : https://prove2.me/submissions/c9f6dd75-d708-44f9-8244-877bf34b1793

import Definitions.Def_ModernOnlineLearning_OnlineToBatch_Defs
open MeasureTheory ProbabilityTheory ModernOnlineLearning.OnlineToBatch

private lemma fixed_loss_tail {D : Type*} [MeasurableSpace D]
    (ρ : Measure D) [IsProbabilityMeasure ρ] (f : D → ℝ)
    (hf : Measurable f) (hb : ∀ z, 0 ≤ f z ∧ f z ≤ 1)
    (T : ℕ) (hT : 1 ≤ T) (r : ℝ) (hr : 0 ≤ r) :
    (Measure.infinitePi (fun _ : ℕ => ρ)).real
      {ω : ℕ → D | r < |(∑ t ∈ Finset.Icc 1 T, f (ω t))/(T:ℝ)-(∫ z, f z ∂ρ)|} ≤
      2 * Real.exp (-((T:ℝ)*r^2)/2) := by
  let P : Measure (ℕ → D) := Measure.infinitePi (fun _ : ℕ => ρ)
  let m : ℝ := ∫ z, f z ∂ρ
  let X : ℕ → (ℕ → D) → ℝ := fun t ω => f (ω t)-m
  have hbase : HasSubgaussianMGF (fun z => f z-m) 1 ρ := by
    have h := hasSubgaussianMGF_of_mem_Icc (μ := ρ) (X := f) (a := (-1:ℝ)) (b := (1:ℝ)) hf.aemeasurable
      (Filter.Eventually.of_forall (fun z => show f z ∈ Set.Icc (-1:ℝ) 1 from ⟨by linarith [(hb z).1], (hb z).2⟩))
    norm_num at h
    exact h
  have hX (t : ℕ) : HasSubgaussianMGF (X t) 1 P := by
    have hm : HasSubgaussianMGF (fun z => f z-m) 1 (P.map (fun ω : ℕ → D => ω t)) := by
      simpa [P, Measure.infinitePi_map_eval] using hbase
    exact HasSubgaussianMGF.of_map (μ := P) (X := fun z => f z-m)
      (Y := fun ω : ℕ → D => ω t) (measurable_pi_apply t).aemeasurable hm
  have hi : iIndepFun X P := iIndepFun_infinitePi (fun _ => hf.sub_const m)
  have hS := HasSubgaussianMGF.sum_of_iIndepFun hi (s := Finset.Icc 1 T) (fun t ht => hX t)
  have hp := hS.measure_ge_le (show 0 ≤ (T:ℝ)*r by positivity)
  have hn := hS.neg.measure_ge_le (show 0 ≤ (T:ℝ)*r by positivity)
  have hT0 : 0 < (T:ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hexp : -((T:ℝ)*r)^2/(2*(∑ _t ∈ Finset.Icc 1 T, (1:NNReal) : NNReal)) = -((T:ℝ)*r^2)/2 := by
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one, NNReal.coe_natCast]
    field_simp
  rw [hexp] at hp hn
  have hsum (ω : ℕ → D) : (∑ t ∈ Finset.Icc 1 T, X t ω) =
      (T:ℝ)*((∑ t ∈ Finset.Icc 1 T, f (ω t))/(T:ℝ)-m) := by
    simp only [X, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    field_simp
  have hsubset : {ω : ℕ → D | r < |(∑ t ∈ Finset.Icc 1 T, f (ω t))/(T:ℝ)-m|} ⊆
      {ω | (T:ℝ)*r ≤ ∑ t ∈ Finset.Icc 1 T, X t ω} ∪
      {ω | (T:ℝ)*r ≤ -(∑ t ∈ Finset.Icc 1 T, X t ω)} := by
    intro ω hω
    change r < |(∑ t ∈ Finset.Icc 1 T, f (ω t))/(T:ℝ)-m| at hω
    rcases lt_abs.mp hω with h | h
    · left
      simp only [Set.mem_setOf_eq, hsum]
      nlinarith
    · right
      simp only [Set.mem_setOf_eq, hsum]
      nlinarith
  have hm := measureReal_mono (μ := P) hsubset
  have hu := measureReal_union_le (μ := P)
    {ω | (T:ℝ)*r ≤ ∑ t ∈ Finset.Icc 1 T, X t ω}
    {ω | (T:ℝ)*r ≤ -(∑ t ∈ Finset.Icc 1 T, X t ω)}
  change P.real _ ≤ _
  change P.real {ω | (T:ℝ)*r ≤ -(∑ t ∈ Finset.Icc 1 T, X t ω)} ≤ _ at hn
  linarith



theorem solution (d : ℕ) {D : Type*} [MeasurableSpace D]
    (ρ : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure ρ]
    (V : Set (Decision d)) (S : Finset (Decision d)) (f : Decision d → D → ℝ)
    (T : ℕ) (δ : ℝ) (xHat : (ℕ → D) → Decision d)
    (hT : 1 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hS : S.Nonempty) (hSV : ∀ x ∈ S, x ∈ V)
    (hf_meas : ∀ x ∈ V, Measurable (f x))
    (hf_bounds : ∀ x ∈ V, ∀ z, 0 ≤ f x z ∧ f x z ≤ 1)
    (hxHat : ∀ ω, xHat ω ∈ S)
    (hxMin : ∀ ω, ∀ x ∈ S, empiricalRisk f ω (xHat ω) T ≤ empiricalRisk f ω x T)
    (hxMeas : Measurable xHat) :
    (MeasureTheory.Measure.infinitePi (fun _ : ℕ => ρ)).real
      {ω : ℕ → D | risk ρ f (xHat ω) ≤ bestRisk ρ f S +
        2 * Real.sqrt (2 * Real.log (2 * (S.card : ℝ) / δ) / (T : ℝ))} ≥
      1 - δ := by
  classical
  let P : Measure (ℕ → D) := Measure.infinitePi (fun _ : ℕ => ρ)
  let r : ℝ := Real.sqrt (2 * Real.log (2 * (S.card:ℝ) / δ) / (T:ℝ))
  have hTpos : 0 < (T:ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hSc : 0 < (S.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  have hSc1 : (1:ℝ) ≤ S.card := by exact_mod_cast (Finset.card_pos.mpr hS)
  have hq : 0 < 2 * (S.card:ℝ)/δ := by positivity
  have hq1 : 1 ≤ 2 * (S.card:ℝ)/δ := by
    apply (le_div_iff₀ hδ0).mpr
    nlinarith
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2=2*Real.log (2*(S.card:ℝ)/δ)/(T:ℝ) :=
    Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hq1)) hTpos.le)
  let B : Set (ℕ → D) := ⋃ x ∈ S, {ω | r < |empiricalRisk f ω x T-risk ρ f x|}
  have hemp (x : Decision d) (hx : x ∈ S) : Measurable (fun ω : ℕ → D => empiricalRisk f ω x T) := by
    unfold empiricalRisk
    apply Measurable.div_const
    apply Finset.measurable_fun_sum
    intro t ht
    exact (hf_meas x (hSV x hx)).comp (measurable_pi_apply t)
  have hBm : MeasurableSet B := by
    apply Finset.measurableSet_biUnion
    intro x hx
    exact measurableSet_lt measurable_const ((hemp x hx).sub_const _).abs
  have hB : P.real B ≤ δ := by
    have hu := measureReal_biUnion_finset_le (μ := P) S (fun x => {ω | r < |empiricalRisk f ω x T-risk ρ f x|})
    have hs := Finset.sum_le_sum (s := S) (fun x hx =>
      fixed_loss_tail ρ (f x) (hf_meas x (hSV x hx)) (hf_bounds x (hSV x hx)) T hT r hr)
    have hval : (∑ _x ∈ S, 2*Real.exp (-((T:ℝ)*r^2)/2))=δ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have he : -((T:ℝ)*r^2)/2 = -Real.log (2*(S.card:ℝ)/δ) := by rw [hr2]; field_simp
      rw [he, Real.exp_neg, Real.exp_log hq]
      field_simp
    rw [hval] at hs
    exact hu.trans hs
  obtain ⟨u, hu, hmin⟩ := S.exists_min_image (risk ρ f) hS
  have hbest : bestRisk ρ f S = risk ρ f u := by
    apply IsLeast.csInf_eq
    constructor
    · exact ⟨u, hu, rfl⟩
    · rintro v ⟨x, hx, rfl⟩
      exact hmin x hx
  have hgood : Bᶜ ⊆ {ω | risk ρ f (xHat ω) ≤ bestRisk ρ f S+2*r} := by
    intro ω hω
    have hall (x : Decision d) (hx : x ∈ S) : |empiricalRisk f ω x T-risk ρ f x| ≤ r := by
      by_contra h
      have hb : ω ∈ B := Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, lt_of_not_ge h⟩⟩
      exact hω hb
    have hxerr := abs_le.mp (hall (xHat ω) (hxHat ω))
    have huerr := abs_le.mp (hall u hu)
    have hcomp := hxMin ω u hu
    change risk ρ f (xHat ω) ≤ bestRisk ρ f S+2*r
    rw [hbest]
    linarith [hxerr.1, huerr.2]
  have hm := measureReal_mono (μ := P) hgood
  rw [probReal_compl_eq_one_sub hBm] at hm
  change P.real {ω | risk ρ f (xHat ω) ≤ bestRisk ρ f S+2*r} ≥ 1-δ
  linarith

