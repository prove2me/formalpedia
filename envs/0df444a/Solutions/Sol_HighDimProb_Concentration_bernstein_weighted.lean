-- Prove2me | solution 1 for HighDimProb.Concentration.bernstein_weighted
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T14:10:49.184285+00:00
-- url     : https://prove2.me/submissions/39d70104-a2e4-4f41-bb75-65ee6f97322b

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubexponentialNorm

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

theorem bw4b30_exp_le (x : ℝ) : Real.exp x ≤ 1 + x + x ^ 2 * Real.exp |x| := by
  have h1 : 1 ≤ Real.exp |x| := Real.one_le_exp (abs_nonneg x)
  rcases le_or_gt |x| 1 with hx | hx
  · have h := Real.abs_exp_sub_one_sub_id_le hx
    have h2 : Real.exp x - 1 - x ≤ x ^ 2 := le_trans (le_abs_self _) h
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg x)]
  · rcases le_or_gt 0 x with h0 | h0
    · rw [abs_of_nonneg h0] at hx h1 ⊢
      have hx2 : 1 ≤ x ^ 2 := by nlinarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hx2) (Real.exp_pos x).le]
    · rw [abs_of_neg h0] at hx
      have he : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr h0.le
      have hx2 : -x ≤ x ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg x)]

theorem bw4b30_mgf_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (hmean : ∫ ω, X ω ∂P = 0) (s : ℝ) (hs : 0 < s)
    (hint : Integrable (fun ω => Real.exp (|X ω| / s)) P)
    (hle : ∫ ω, Real.exp (|X ω| / s) ∂P ≤ 2) (μ : ℝ) (hμ : |μ| ≤ 1 / (2 * s)) :
    Integrable (fun ω => Real.exp (μ * X ω)) P ∧
      ∫ ω, Real.exp (μ * X ω) ∂P ≤ Real.exp (16 * μ ^ 2 * s ^ 2) := by
  have hμX : ∀ ω, |μ * X ω| ≤ |X ω| / (2 * s) := by
    intro ω
    rw [abs_mul]
    calc |μ| * |X ω| ≤ 1 / (2 * s) * |X ω| := mul_le_mul_of_nonneg_right hμ (abs_nonneg _)
      _ = |X ω| / (2 * s) := by ring
  have hhalf : ∀ ω, |X ω| / (2 * s) ≤ |X ω| / s := by
    intro ω
    exact div_le_div_of_nonneg_left (abs_nonneg _) hs (by linarith)
  have hXint : Integrable X P := by
    refine Integrable.mono' (hint.const_mul s) hX.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs]
    have h1 := Real.add_one_le_exp (|X ω| / s)
    calc |X ω| = s * (|X ω| / s) := by field_simp
      _ ≤ s * Real.exp (|X ω| / s) := mul_le_mul_of_nonneg_left (by linarith) hs.le
  have hE : Integrable (fun ω => Real.exp (μ * X ω)) P := by
    refine Integrable.mono' hint (by fun_prop : Measurable fun ω => Real.exp (μ * X ω)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans ((hμX ω).trans (hhalf ω)))
  have hbound : ∀ ω, X ω ^ 2 * Real.exp |μ * X ω| ≤ 8 * s ^ 2 * Real.exp (|X ω| / s) := by
    intro ω
    set u := |X ω| / (2 * s) with hu
    have hu0 : 0 ≤ u := by positivity
    have hq := Real.quadratic_le_exp_of_nonneg hu0
    have h2u : |X ω| / s = u + u := by rw [hu]; field_simp; ring
    have hA : X ω ^ 2 = 4 * s ^ 2 * u ^ 2 := by
      have h' : |X ω| = 2 * s * u := by rw [hu]; field_simp
      rw [← sq_abs, h']; ring
    have hB : Real.exp |μ * X ω| ≤ Real.exp u := Real.exp_le_exp.mpr (hμX ω)
    have hC : u ^ 2 ≤ 2 * Real.exp u := by nlinarith
    rw [h2u, Real.exp_add, hA]
    have hexp0 : 0 ≤ Real.exp |μ * X ω| := (Real.exp_pos _).le
    calc 4 * s ^ 2 * u ^ 2 * Real.exp |μ * X ω|
        ≤ 4 * s ^ 2 * (2 * Real.exp u) * Real.exp u := by
          apply mul_le_mul _ hB hexp0 (by positivity)
          exact mul_le_mul_of_nonneg_left hC (by positivity)
      _ = 8 * s ^ 2 * (Real.exp u * Real.exp u) := by ring
  have hQ : Integrable (fun ω => X ω ^ 2 * Real.exp |μ * X ω|) P := by
    refine Integrable.mono' (hint.const_mul (8 * s ^ 2))
      (by fun_prop : Measurable fun ω => X ω ^ 2 * Real.exp |μ * X ω|).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_of_nonneg (by positivity)]
    exact hbound ω
  have hpt : ∀ ω, Real.exp (μ * X ω) ≤ 1 + μ * X ω + μ ^ 2 * (X ω ^ 2 * Real.exp |μ * X ω|) := by
    intro ω
    calc Real.exp (μ * X ω) ≤ 1 + μ * X ω + (μ * X ω) ^ 2 * Real.exp |μ * X ω| := bw4b30_exp_le _
      _ = 1 + μ * X ω + μ ^ 2 * (X ω ^ 2 * Real.exp |μ * X ω|) := by ring
  have hint2 : Integrable (fun ω => 1 + μ * X ω + μ ^ 2 * (X ω ^ 2 * Real.exp |μ * X ω|)) P :=
    ((integrable_const 1).add (hXint.const_mul μ)).add (hQ.const_mul (μ ^ 2))
  have hmono := integral_mono hE hint2 hpt
  have hsplit : ∫ ω, (1 + μ * X ω + μ ^ 2 * (X ω ^ 2 * Real.exp |μ * X ω|)) ∂P =
      1 + μ ^ 2 * ∫ ω, X ω ^ 2 * Real.exp |μ * X ω| ∂P := by
    have hf1 : Integrable (fun ω => 1 + μ * X ω) P := (integrable_const 1).add (hXint.const_mul μ)
    have hf2 : Integrable (fun ω => μ ^ 2 * (X ω ^ 2 * Real.exp |μ * X ω|)) P := hQ.const_mul _
    rw [integral_add hf1 hf2, integral_add (integrable_const 1) (hXint.const_mul μ), integral_const,
      integral_const_mul, integral_const_mul, hmean]
    simp
  have hQle : ∫ ω, X ω ^ 2 * Real.exp |μ * X ω| ∂P ≤ 16 * s ^ 2 := by
    calc ∫ ω, X ω ^ 2 * Real.exp |μ * X ω| ∂P
        ≤ ∫ ω, 8 * s ^ 2 * Real.exp (|X ω| / s) ∂P := integral_mono hQ (hint.const_mul _) hbound
      _ = 8 * s ^ 2 * ∫ ω, Real.exp (|X ω| / s) ∂P := integral_const_mul _ _
      _ ≤ 8 * s ^ 2 * 2 := by gcongr
      _ = 16 * s ^ 2 := by ring
  refine ⟨hE, ?_⟩
  rw [hsplit] at hmono
  have h3 := Real.add_one_le_exp (16 * μ ^ 2 * s ^ 2)
  have h4 : μ ^ 2 * ∫ ω, X ω ^ 2 * Real.exp |μ * X ω| ∂P ≤ μ ^ 2 * (16 * s ^ 2) :=
    mul_le_mul_of_nonneg_left hQle (sq_nonneg μ)
  nlinarith

theorem bw4b30_witness {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X)
    (hsub : ∃ s > 0, Integrable (fun ω => Real.exp (|X ω| / s)) P ∧
      ∫ ω, Real.exp (|X ω| / s) ∂P ≤ 2)
    (r : ℝ) (hr : HighDimProb.Concentration.subexponentialNorm P X < r) :
    Integrable (fun ω => Real.exp (|X ω| / r)) P ∧ ∫ ω, Real.exp (|X ω| / r) ∂P ≤ 2 := by
  obtain ⟨s0, hs0, hi0, hl0⟩ := hsub
  have hne : ({t : ℝ | 0 < t ∧ Integrable (fun ω => Real.exp (|X ω| / t)) P ∧
      ∫ ω, Real.exp (|X ω| / t) ∂P ≤ 2}).Nonempty := ⟨s0, hs0, hi0, hl0⟩
  obtain ⟨t, ⟨htp, hti, htl⟩, htr⟩ := exists_lt_of_csInf_lt hne hr
  have hrp : 0 < r := htp.trans htr
  have hle : ∀ ω, Real.exp (|X ω| / r) ≤ Real.exp (|X ω| / t) := by
    intro ω
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (abs_nonneg _) htp htr.le)
  have hI : Integrable (fun ω => Real.exp (|X ω| / r)) P := by
    refine Integrable.mono' hti (by fun_prop : Measurable fun ω => Real.exp (|X ω| / r)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hle ω
  exact ⟨hI, (integral_mono hI hti hle).trans htl⟩

theorem bw4b30_main {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (X : Fin N → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hsub : ∀ i, ∃ s > 0, Integrable (fun ω => Real.exp (|X i ω| / s)) P ∧
                       ∫ ω, Real.exp (|X i ω| / s) ∂P ≤ 2)
    (a : Fin N → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t ≤ |∑ i, a i * X i ω|} ≤
      2 * Real.exp (-(1 / 256 * min
        (t ^ 2 / ((⨆ i, HighDimProb.Concentration.subexponentialNorm P (X i)) ^ 2 * ∑ i, (a i) ^ 2))
        (t / ((⨆ i, HighDimProb.Concentration.subexponentialNorm P (X i)) * ⨆ i, |a i|)))) := by
  set K := ⨆ i, HighDimProb.Concentration.subexponentialNorm P (X i) with hK
  set A := ∑ i, (a i) ^ 2 with hA
  set B := ⨆ i, |a i| with hB
  have hprob : P.real {ω | t ≤ |∑ i, a i * X i ω|} ≤ 1 := measureReal_le_one
  have hKi : ∀ i, HighDimProb.Concentration.subexponentialNorm P (X i) ≤ K :=
    fun i => le_ciSup (f := fun i => HighDimProb.Concentration.subexponentialNorm P (X i))
      (Set.finite_range _).bddAbove i
  have hBi : ∀ i, |a i| ≤ B := fun i => le_ciSup (f := fun i => |a i|) (Set.finite_range _).bddAbove i
  have hK0 : 0 ≤ K := by
    rcases isEmpty_or_nonempty (Fin N) with hN | hN
    · rw [hK, Real.iSup_of_isEmpty]
    · obtain ⟨i⟩ := hN
      exact le_trans (Real.sInf_nonneg (fun x hx => hx.1.le)) (hKi i)
  have hB0 : 0 ≤ B := by
    rcases isEmpty_or_nonempty (Fin N) with hN | hN
    · rw [hB, Real.iSup_of_isEmpty]
    · obtain ⟨i⟩ := hN
      exact le_trans (abs_nonneg _) (hBi i)
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  by_cases hdeg : K = 0 ∨ A = 0 ∨ B = 0
  · have hmin : min (t ^ 2 / (K ^ 2 * A)) (t / (K * B)) ≤ 0 := by
      rcases hdeg with h | h | h
      · exact (min_le_left _ _).trans (by rw [h]; simp)
      · exact (min_le_left _ _).trans (by rw [h]; simp)
      · exact (min_le_right _ _).trans (by rw [h]; simp)
    have : 1 ≤ Real.exp (-(1 / 256 * min (t ^ 2 / (K ^ 2 * A)) (t / (K * B)))) :=
      Real.one_le_exp (by linarith)
    linarith
  simp only [not_or] at hdeg
  obtain ⟨hKne, hAne, hBne⟩ := hdeg
  have hKp : 0 < K := lt_of_le_of_ne hK0 (Ne.symm hKne)
  have hAp : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAne)
  have hBp : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hBne)
  have hwit : ∀ i, Integrable (fun ω => Real.exp (|X i ω| / (2 * K))) P ∧
      ∫ ω, Real.exp (|X i ω| / (2 * K)) ∂P ≤ 2 :=
    fun i => bw4b30_witness P (X i) (hX i) (hsub i) (2 * K) (by linarith [hKi i])
  -- the weighted summands
  set Y : Fin N → Ω → ℝ := fun i ω => a i * X i ω with hY
  have hYmeas : ∀ i, Measurable (Y i) := fun i => (hX i).const_mul (a i)
  have hYind : iIndepFun Y P := by
    have := hind.comp (fun i x => a i * x) (fun i => measurable_const.mul measurable_id)
    exact this
  have hSeq : ∀ ω, (∑ i, Y i) ω = ∑ i, a i * X i ω := by
    intro ω
    simp [hY, Finset.sum_apply]
  -- per-summand mgf bound
  have hYmgf : ∀ μ : ℝ, |μ| ≤ 1 / (4 * K * B) → ∀ i,
      Integrable (fun ω => Real.exp (μ * Y i ω)) P ∧
        mgf (Y i) P μ ≤ Real.exp (64 * μ ^ 2 * K ^ 2 * (a i) ^ 2) := by
    intro μ hμ i
    have hc : |μ * a i| ≤ 1 / (2 * (2 * K)) := by
      rw [abs_mul]
      calc |μ| * |a i| ≤ 1 / (4 * K * B) * B :=
            mul_le_mul hμ (hBi i) (abs_nonneg _) (by positivity)
        _ = 1 / (2 * (2 * K)) := by field_simp; ring
    obtain ⟨hI, hL⟩ := bw4b30_mgf_le P (X i) (hX i) (hmean i) (2 * K) (by linarith)
      (hwit i).1 (hwit i).2 (μ * a i) hc
    have hfun : (fun ω => Real.exp (μ * Y i ω)) = fun ω => Real.exp (μ * a i * X i ω) := by
      funext ω; simp only [hY]; ring_nf
    refine ⟨by rw [hfun]; exact hI, ?_⟩
    calc mgf (Y i) P μ = ∫ ω, Real.exp (μ * a i * X i ω) ∂P := by
          rw [mgf]; exact congrArg (fun f => ∫ ω, f ω ∂P) hfun
      _ ≤ Real.exp (16 * (μ * a i) ^ 2 * (2 * K) ^ 2) := hL
      _ = Real.exp (64 * μ ^ 2 * K ^ 2 * (a i) ^ 2) := by ring_nf
  have hSmgf : ∀ μ : ℝ, |μ| ≤ 1 / (4 * K * B) →
      Integrable (fun ω => Real.exp (μ * (∑ i, Y i) ω)) P ∧
        mgf (∑ i, Y i) P μ ≤ Real.exp (64 * μ ^ 2 * K ^ 2 * A) := by
    intro μ hμ
    refine ⟨hYind.integrable_exp_mul_sum hYmeas (fun i _ => (hYmgf μ hμ i).1), ?_⟩
    rw [hYind.mgf_sum hYmeas]
    calc ∏ i, mgf (Y i) P μ ≤ ∏ i, Real.exp (64 * μ ^ 2 * K ^ 2 * (a i) ^ 2) :=
          Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => (hYmgf μ hμ i).2)
      _ = Real.exp (64 * μ ^ 2 * K ^ 2 * A) := by
          rw [← Real.exp_sum, hA, Finset.mul_sum]
  -- choice of λ
  set l := min (t / (128 * K ^ 2 * A)) (1 / (4 * K * B)) with hl
  have hl0 : 0 ≤ l := le_min (by positivity) (by positivity)
  have hl1 : l ≤ t / (128 * K ^ 2 * A) := min_le_left _ _
  have hl2 : l ≤ 1 / (4 * K * B) := min_le_right _ _
  have habs1 : |l| ≤ 1 / (4 * K * B) := by rw [abs_of_nonneg hl0]; exact hl2
  have habs2 : |-l| ≤ 1 / (4 * K * B) := by rw [abs_neg, abs_of_nonneg hl0]; exact hl2
  have hquad : 64 * l ^ 2 * K ^ 2 * A ≤ l * t / 2 := by
    have : 128 * K ^ 2 * A * l ≤ t := by
      have h := mul_le_mul_of_nonneg_left hl1 (by positivity : (0 : ℝ) ≤ 128 * K ^ 2 * A)
      rwa [mul_div_cancel₀ _ (by positivity)] at h
    nlinarith
  have hexpo : Real.exp (-l * t) * Real.exp (64 * l ^ 2 * K ^ 2 * A) ≤ Real.exp (-(l * t / 2)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hupper : P.real {ω | t ≤ ∑ i, a i * X i ω} ≤ Real.exp (-(l * t / 2)) := by
    have h := measure_ge_le_exp_mul_mgf (X := ∑ i, Y i) (μ := P) t hl0 (hSmgf l habs1).1
    simp only [hSeq] at h
    refine h.trans ((mul_le_mul_of_nonneg_left (hSmgf l habs1).2 (Real.exp_pos _).le).trans hexpo)
  have hlower : P.real {ω | ∑ i, a i * X i ω ≤ -t} ≤ Real.exp (-(l * t / 2)) := by
    have h := measure_le_le_exp_mul_mgf (X := ∑ i, Y i) (μ := P) (-t) (by linarith : -l ≤ 0)
      (hSmgf (-l) habs2).1
    simp only [hSeq] at h
    have h2 := (hSmgf (-l) habs2).2
    rw [neg_sq] at h2
    have e : -(-l) * -t = -l * t := by ring
    rw [e] at h
    exact h.trans ((mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le).trans hexpo)
  have hsub_set : {ω | t ≤ |∑ i, a i * X i ω|} ⊆
      {ω | t ≤ ∑ i, a i * X i ω} ∪ {ω | ∑ i, a i * X i ω ≤ -t} := by
    intro ω hω
    have hω' : t ≤ |∑ i, a i * X i ω| := hω
    rcases le_abs'.mp hω' with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hfinal : 1 / 256 * min (t ^ 2 / (K ^ 2 * A)) (t / (K * B)) ≤ l * t / 2 := by
    rcases min_cases (t / (128 * K ^ 2 * A)) (1 / (4 * K * B)) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [hl, h]
      calc 1 / 256 * min (t ^ 2 / (K ^ 2 * A)) (t / (K * B)) ≤ 1 / 256 * (t ^ 2 / (K ^ 2 * A)) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
        _ = t / (128 * K ^ 2 * A) * t / 2 := by field_simp; ring
    · rw [hl, h]
      calc 1 / 256 * min (t ^ 2 / (K ^ 2 * A)) (t / (K * B)) ≤ 1 / 256 * (t / (K * B)) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
        _ ≤ 1 / (4 * K * B) * t / 2 := by
            have hKB : 0 < K * B := by positivity
            have e1 : 1 / 256 * (t / (K * B)) = t / (K * B) * (1 / 256) := by ring
            have e2 : 1 / (4 * K * B) * t / 2 = t / (K * B) * (1 / 8) := by field_simp; ring
            rw [e1, e2]
            exact mul_le_mul_of_nonneg_left (by norm_num) (div_nonneg ht hKB.le)
  calc P.real {ω | t ≤ |∑ i, a i * X i ω|}
      ≤ P.real ({ω | t ≤ ∑ i, a i * X i ω} ∪ {ω | ∑ i, a i * X i ω ≤ -t}) :=
        measureReal_mono hsub_set
    _ ≤ P.real {ω | t ≤ ∑ i, a i * X i ω} + P.real {ω | ∑ i, a i * X i ω ≤ -t} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-(l * t / 2)) + Real.exp (-(l * t / 2)) := add_le_add hupper hlower
    _ = 2 * Real.exp (-(l * t / 2)) := by ring
    _ ≤ 2 * Real.exp (-(1 / 256 * min (t ^ 2 / (K ^ 2 * A)) (t / (K * B)))) := by
        gcongr

open MeasureTheory ProbabilityTheory Real HighDimProb.Concentration in
theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {N : ℕ} (X : Fin N → Ω → ℝ), (∀ i, Measurable (X i)) → iIndepFun X P →
        (∀ i, ∫ ω, X i ω ∂P = 0) →
        (∀ i, ∃ s > 0, Integrable (fun ω => Real.exp (|X i ω| / s)) P ∧
                       ∫ ω, Real.exp (|X i ω| / s) ∂P ≤ 2) →
        ∀ (a : Fin N → ℝ) {t : ℝ}, 0 ≤ t →
        P.real {ω | t ≤ |∑ i, a i * X i ω|} ≤
          2 * Real.exp (-(c * min
            (t ^ 2 / ((⨆ i, subexponentialNorm P (X i)) ^ 2 * ∑ i, (a i) ^ 2))
            (t / ((⨆ i, subexponentialNorm P (X i)) * ⨆ i, |a i|)))) := by
  refine ⟨1 / 256, by norm_num, ?_⟩
  intro Ω _ P _ N X hX hind hmean hsub a t ht
  exact bw4b30_main P X hX hind hmean hsub a ht
