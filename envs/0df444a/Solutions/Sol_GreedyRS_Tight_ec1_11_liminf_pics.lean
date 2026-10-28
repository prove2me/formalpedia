-- Prove2me | solution 1 for GreedyRS.Tight.ec1_11_liminf_pics
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T10:56:57.891315+00:00
-- url     : https://prove2.me/submissions/d1005d18-6540-4694-bd21-c3f5baf94810

import Mathlib
import Definitions.Def_GreedyRS_Tight_Setting
import Theorems.Thm_GreedyRS_Tight_ec1_8_pics_event
import Theorems.Thm_GreedyRS_Greedy_lemma2_crossing_time
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace G11
open GreedyRS.Greedy

lemma iInf_coe_eq_iff (p : ℕ → Prop) (m : ℕ) :
    (⨅ (n : ℕ) (_ : p n), (n : ℕ∞)) = m ↔ p m ∧ ∀ n, p n → m ≤ n := by
  constructor
  · intro h
    have hle : ∀ n, p n → m ≤ n := by
      intro n hn
      have : (m : ℕ∞) ≤ n := h ▸ iInf₂_le n hn
      exact_mod_cast this
    refine ⟨?_, hle⟩
    by_contra hpm
    have : ((m + 1 : ℕ) : ℕ∞) ≤ ⨅ (n : ℕ) (_ : p n), (n : ℕ∞) := by
      refine le_iInf₂ fun n hn => ?_
      have h1 := hle n hn
      have h2 : n ≠ m := fun h => hpm (h ▸ hn)
      exact_mod_cast (show m + 1 ≤ n by omega)
    rw [h] at this
    have : m + 1 ≤ m := by exact_mod_cast this
    omega
  · rintro ⟨hpm, hle⟩
    apply le_antisymm
    · exact iInf₂_le m hpm
    · exact le_iInf₂ fun n hn => by exact_mod_cast hle n hn

lemma iInf_coe_eq_top_iff (p : ℕ → Prop) :
    (⨅ (n : ℕ) (_ : p n), (n : ℕ∞)) = ⊤ ↔ ∀ n, ¬ p n := by
  simp only [iInf_eq_top, ENat.coe_ne_top, imp_false]

lemma meas_hit {α : Type*} [MeasurableSpace α] (p : α → ℕ → Prop)
    (hp : ∀ n, MeasurableSet {a | p a n}) :
    Measurable fun a => ⨅ (n : ℕ) (_ : p a n), (n : ℕ∞) := by
  apply measurable_to_countable'
  intro N
  induction N using ENat.recTopCoe with
  | top =>
    have : (fun a => ⨅ (n : ℕ) (_ : p a n), (n : ℕ∞)) ⁻¹' {⊤} = ⋂ n, {a | p a n}ᶜ := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_compl_iff]
      rw [iInf_coe_eq_top_iff]; rfl
    rw [this]; exact MeasurableSet.iInter fun n => (hp n).compl
  | coe m =>
    have : (fun a => ⨅ (n : ℕ) (_ : p a n), (n : ℕ∞)) ⁻¹' {(m : ℕ∞)} =
        {a | p a m} ∩ ⋂ n ∈ Finset.range m, {a | p a n}ᶜ := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_compl_iff, Finset.mem_range]
      rw [iInf_coe_eq_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun n hn hpn => ?_⟩
        have := h2 n hpn; omega
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun n hpn => ?_⟩
        by_contra hlt
        exact h2 n (by omega) hpn
    rw [this]
    exact (hp m).inter (MeasurableSet.biInter (Finset.range m).countable_toSet
      fun n _ => (hp n).compl)

lemma meas_crossTime (x : ℝ) : Measurable fun z : ℕ → ℝ => crossTime x 1 z := by
  unfold crossTime
  apply meas_hit (fun z n => 1 ≤ n ∧ zbar z n < x)
  intro n
  show MeasurableSet ({z : ℕ → ℝ | 1 ≤ n} ∩ {z | zbar z n < x})
  refine (MeasurableSet.const _).inter (measurableSet_lt ?_ measurable_const)
  unfold zbar
  exact (Finset.measurable_sum _ fun j _ => measurable_pi_apply j).div_const _

/-- Standardisation of a row turns `crossBelow` of its running mean into `crossTime`. -/
lemma crossBelow_eq_crossTime (x : ℕ → ℝ) (m L σ : ℝ) (hσ : 0 < σ) :
    crossBelow (fun n => (∑ j ∈ Finset.range n, x j) / n) L 1 =
      crossTime ((L - m) / σ) 1 (fun j => (x j - m) / σ) := by
  unfold crossBelow crossTime
  refine iInf_congr fun n => iInf_congr_Prop ?_ (fun _ => rfl)
  · constructor
    · rintro ⟨hn, h⟩
      refine ⟨hn, ?_⟩
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      unfold zbar
      rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, div_div, div_lt_div_iff₀ (by positivity) hσ]
      rw [div_lt_iff₀ hn'] at h
      nlinarith
    · rintro ⟨hn, h⟩
      refine ⟨hn, ?_⟩
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      unfold zbar at h
      rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, div_div, div_lt_div_iff₀ (by positivity) hσ] at h
      rw [div_lt_iff₀ hn']
      nlinarith

lemma gauss_standardize (m : ℝ) (w : ℝ≥0) (hw : 0 < w) :
    (gaussianReal m w).map (fun t => (t - m) / Real.sqrt w) = gaussianReal 0 1 := by
  have hσ : 0 < Real.sqrt w := Real.sqrt_pos.2 (by exact_mod_cast hw)
  have : (fun t => (t - m) / Real.sqrt w) = (fun t => t / Real.sqrt w) ∘ (fun t => t - m) := rfl
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_sub_const,
    gaussianReal_map_div_const]
  congr 1
  · simp
  · ext
    simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_one]
    rw [Real.sq_sqrt (NNReal.coe_nonneg w)]
    exact div_self (by exact_mod_cast hw.ne')

variable {Ω : Type*} [MeasurableSpace Ω]

lemma rows_law (P : Measure Ω) [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (X : ℕ → ℕ → Ω → ℝ) (hX : NormalArray P μ v X) :
    P.map (fun ω i j => X i j ω) =
      Measure.infinitePi (fun i => Measure.infinitePi (fun _ : ℕ => gaussianReal (μ i) (v i))) := by
  have hjm : Measurable (fun ω (p : ℕ × ℕ) => X p.1 p.2 ω) :=
    measurable_pi_lambda _ fun p => hX.meas p.1 p.2
  have hjoint : P.map (fun ω (p : ℕ × ℕ) => X p.1 p.2 ω) =
      Measure.infinitePi (fun p : ℕ × ℕ => gaussianReal (μ p.1) (v p.1)) := by
    have h := hX.indep.map_fun_eq_infinitePi_map (fun p : ℕ × ℕ => hX.meas p.1 p.2)
    rw [h]
    congr 1; ext1 p; exact hX.law p.1 p.2
  have hcomp : (fun ω i j => X i j ω) =
      (MeasurableEquiv.curry ℕ ℕ ℝ) ∘ (fun ω (p : ℕ × ℕ) => X p.1 p.2 ω) := by
    ext ω i j; rfl
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.curry ℕ ℕ ℝ).measurable hjm, hjoint]
  exact Measure.infinitePi_map_curry (fun i (_ : ℕ) => gaussianReal (μ i) (v i))

lemma row_law (P : Measure Ω) [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (X : ℕ → ℕ → Ω → ℝ) (hX : NormalArray P μ v X) (i : ℕ) :
    P.map (fun ω j => X i j ω) = Measure.infinitePi (fun _ : ℕ => gaussianReal (μ i) (v i)) := by
  have hrm : Measurable (fun ω i j => X i j ω) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hX.meas i j
  have : (fun ω j => X i j ω) = (fun f : ℕ → ℕ → ℝ => f i) ∘ (fun ω i j => X i j ω) := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply i) hrm, rows_law P μ v X hX,
    Measure.infinitePi_map_eval]

lemma rows_indep (P : Measure Ω) [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (X : ℕ → ℕ → Ω → ℝ) (hX : NormalArray P μ v X) :
    iIndepFun (fun i ω j => X i j ω) P := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun i => measurable_pi_lambda _ fun j => hX.meas i j)]
  rw [rows_law P μ v X hX]
  congr 1; ext1 i
  exact (row_law P μ v X hX i).symm

end G11

namespace G11
open GreedyRS.Greedy

variable {Ω : Type*} [MeasurableSpace Ω]

/-- SLLN for the boundary-crossing times of the inferior alternatives under the SC-CV. -/
lemma slln_cross (P : Measure Ω) [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (X : ℕ → ℕ → Ω → ℝ) (hX : NormalArray P μ v X) (γ : ℝ)
    (hslip : ∀ i, 1 ≤ i → μ i = μ 0 - γ) (w : ℝ≥0) (hw : 0 < w) (hcv : ∀ i, v i = w)
    (L : ℝ)
    (hfin : stdNormalSeq {z | crossTime ((L - (μ 0 - γ)) / Real.sqrt w) 1 z < ⊤} = 1)
    (hmean : Cn0 ((L - (μ 0 - γ)) / Real.sqrt w) 1 =
      ENNReal.ofReal (Cfun ((L - (μ 0 - γ)) / Real.sqrt w))) :
    ∀ᵐ ω ∂P, (∀ i, crossBelow (runMean (fun i j => X i j ω) (i + 1)) L 1 < ⊤) ∧
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        ((crossBelow (runMean (fun i j => X i j ω) (i + 1)) L 1 : ℕ∞) : ℝ≥0∞).toReal)
        atTop (𝓝 (Cfun ((L - (μ 0 - γ)) / Real.sqrt w))) := by
  haveI : IsProbabilityMeasure stdNormalSeq := by unfold stdNormalSeq; infer_instance
  have hfinset : ∀ x : ℝ, MeasurableSet {z : ℕ → ℝ | crossTime x 1 z < ⊤} := by
    intro x
    have : {z : ℕ → ℝ | crossTime x 1 z < ⊤} = (fun z => crossTime x 1 z) ⁻¹' {⊤}ᶜ := by
      ext z; simp [lt_top_iff_ne_top]
    rw [this]; exact meas_crossTime x (MeasurableSet.singleton _).compl
  set σ := Real.sqrt w with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 (by exact_mod_cast hw)
  set m := μ 0 - γ with hm
  set x0 := (L - m) / σ with hx0
  set φ : (ℕ → ℝ) → (ℕ → ℝ) := fun x j => (x j - m) / σ with hφ
  have hφm : Measurable φ := measurable_pi_lambda _ fun j =>
    ((measurable_pi_apply j).sub_const _).div_const _
  set R : ℕ → Ω → (ℕ → ℝ) := fun i ω j => X i j ω with hR
  have hRm : ∀ i, Measurable (R i) := fun i => measurable_pi_lambda _ fun j => hX.meas i j
  set Z : ℕ → Ω → (ℕ → ℝ) := fun i => φ ∘ R (i + 1) with hZ
  have hZm : ∀ i, Measurable (Z i) := fun i => hφm.comp (hRm _)
  have hZlaw : ∀ i, P.map (Z i) = stdNormalSeq := by
    intro i
    rw [hZ, ← Measure.map_map hφm (hRm _), row_law P μ v X hX (i + 1), hslip (i + 1) (by omega),
      hcv (i + 1)]
    have h := Measure.infinitePi_map_pi (fun _ : ℕ => gaussianReal m w)
      (f := fun (_ : ℕ) (t : ℝ) => (t - m) / σ) (fun _ => by fun_prop)
    refine h.trans ?_
    unfold stdNormalSeq
    congr 1; ext1 j
    exact gauss_standardize m w hw
  set H : (ℕ → ℝ) → ℝ := fun z => ((crossTime x0 1 z : ℕ∞) : ℝ≥0∞).toReal with hH
  have hHm : Measurable H :=
    (measurable_of_countable (fun n : ℕ∞ => ((n : ℝ≥0∞)).toReal)).comp (meas_crossTime x0)
  have hcross : ∀ ω i, crossBelow (runMean (fun i j => X i j ω) (i + 1)) L 1 =
      crossTime x0 1 (Z i ω) := by
    intro ω i
    exact crossBelow_eq_crossTime (fun j => X (i + 1) j ω) m L σ hσ
  -- SLLN
  set Y : ℕ → Ω → ℝ := fun i => H ∘ Z i with hY
  have hYm : ∀ i, Measurable (Y i) := fun i => hHm.comp (hZm i)
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := by
    intro i
    have hz : IdentDistrib (Z i) (Z 0) P P :=
      ⟨(hZm i).aemeasurable, (hZm 0).aemeasurable, by rw [hZlaw i, hZlaw 0]⟩
    exact hz.comp hHm
  have hRind := rows_indep P μ v X hX
  have hindep : Pairwise (Function.onFun (fun f g => IndepFun f g P) Y) := by
    intro i j hij
    have h1 : IndepFun (R (i + 1)) (R (j + 1)) P := hRind.indepFun (by omega)
    exact h1.comp (hHm.comp hφm) (hHm.comp hφm)
  have hlin : ∫⁻ z, ((crossTime x0 1 z : ℕ∞) : ℝ≥0∞) ∂stdNormalSeq = ENNReal.ofReal (Cfun x0) :=
    hmean
  have hHint : Integrable H stdNormalSeq := by
    refine integrable_toReal_of_lintegral_ne_top
      ((measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (meas_crossTime x0)).aemeasurable
      ?_
    rw [hlin]; exact ENNReal.ofReal_ne_top
  have hint : Integrable (Y 0) P := by
    have : Integrable H (P.map (Z 0)) := by rw [hZlaw 0]; exact hHint
    exact (integrable_map_measure hHm.aestronglyMeasurable (hZm 0).aemeasurable).1 this
  have hfinae : ∀ᵐ z ∂stdNormalSeq, crossTime x0 1 z < ⊤ := by
    have hms : MeasurableSet {z | crossTime x0 1 z < ⊤} := hfinset x0
    rw [ae_iff]
    have : {z | ¬ crossTime x0 1 z < ⊤} = {z | crossTime x0 1 z < ⊤}ᶜ := by ext; simp
    rw [this, prob_compl_eq_one_sub hms, hfin, tsub_self]
  have hmeanY : P[Y 0] = Cfun x0 := by
    have h1 : ∫ ω, Y 0 ω ∂P = ∫ z, H z ∂(P.map (Z 0)) :=
      (integral_map (hZm 0).aemeasurable hHm.aestronglyMeasurable).symm
    rw [h1, hZlaw 0]
    show ∫ z, ((crossTime x0 1 z : ℕ∞) : ℝ≥0∞).toReal ∂stdNormalSeq = _
    rw [integral_toReal (f := fun z => ((crossTime x0 1 z : ℕ∞) : ℝ≥0∞))
      ((measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (meas_crossTime x0)).aemeasurable
      (hfinae.mono fun z hz => by simpa using hz), hlin,
      ENNReal.toReal_ofReal (by unfold Cfun; exact (Real.exp_pos _).le)]
  have hslln := strong_law_ae Y hint hindep hident
  have hfinω : ∀ᵐ ω ∂P, ∀ i, crossTime x0 1 (Z i ω) < ⊤ := by
    rw [ae_all_iff]
    intro i
    have := (ae_map_iff (hZm i).aemeasurable (hfinset x0)).1
      (by rw [hZlaw i]; exact hfinae)
    exact this
  filter_upwards [hslln, hfinω] with ω h1 h2
  refine ⟨fun i => by rw [hcross]; exact h2 i, ?_⟩
  rw [hmeanY] at h1
  refine h1.congr fun n => ?_
  simp only [smul_eq_mul, hcross, hY, hH, Function.comp_apply]

end G11

namespace G11
open GreedyRS.Greedy GreedyRS.Tight

lemma crossBelow_spec' (y : ℕ → ℝ) (b : ℝ) (m : ℕ) (h : crossBelow y b 1 = m) :
    1 ≤ m ∧ y m < b := by
  unfold crossBelow at h
  exact ((iInf_coe_eq_iff _ m).1 h).1

lemma prefixCross_le_crossBelow (yi y : ℕ → ℝ) (m : ℕ) (L : ℝ)
    (h : ∀ j ∈ Finset.Icc 1 m, L ≤ y j) : prefixCross yi y m ≤ crossBelow yi L 1 := by
  induction hN : crossBelow yi L 1 using ENat.recTopCoe with
  | top => exact le_top
  | coe s =>
    obtain ⟨hs1, hs⟩ := crossBelow_spec' yi L s hN
    unfold prefixCross
    exact iInf₂_le s ⟨hs1, fun j hj => lt_of_lt_of_le hs (h j hj)⟩

lemma crossBelow_le_prefixCross (yi y : ℕ → ℝ) (m : ℕ) (L : ℝ) (hm : 1 ≤ m) (hym : y m < L) :
    crossBelow yi L 1 ≤ prefixCross yi y m := by
  induction hN : prefixCross yi y m using ENat.recTopCoe with
  | top => exact le_top
  | coe s =>
    unfold prefixCross at hN
    obtain ⟨hs1, hs⟩ := ((iInf_coe_eq_iff _ s).1 hN).1
    unfold crossBelow
    exact iInf₂_le s ⟨hs1, lt_trans (hs m (Finset.mem_Icc.2 ⟨hm, le_rfl⟩)) hym⟩

/-- A finite `ℕ∞`-valued family: the `ENNReal.toReal` of its cast is the natural cast. -/
lemma toReal_coe_nat (a : ℕ) : (((a : ℕ∞) : ℝ≥0∞)).toReal = (a : ℝ) := by
  simp

end G11

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ) (hX : GreedyRS.Greedy.NormalArray P μ v X)
    (γ : ℝ) (hγ : 0 < γ) (hslip : ∀ i, 1 ≤ i → μ i = μ 0 - γ)
    (w : ℝ≥0) (hw : 0 < w) (hcv : ∀ i, v i = w)
    (c : ℝ) (hc : GreedyRS.Greedy.Cfun (γ / Real.sqrt w) < c)
    (ε : ℝ) (hε : 0 < 2 * ε ∧ 2 * ε < c - GreedyRS.Greedy.Cfun (γ / Real.sqrt w))
    (γm γp : ℝ) (hγm : γm ∈ Set.Ioo 0 γ) (hγp : γp ∈ Set.Ioo 0 γ)
    (hCm : GreedyRS.Greedy.Cfun ((γ - γm) / Real.sqrt w) = c - 2 * ε)
    (hCp : GreedyRS.Greedy.Cfun ((γ - γp) / Real.sqrt w) = c + 2 * ε) :
    P {ω | ∃ m : ℕ, GreedyRS.Greedy.crossBelow (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) (μ 0 - γp) 1 = m ∧
        ∀ n ∈ Finset.Icc 1 (m - 1), μ 0 - γm ≤ GreedyRS.Greedy.runMean (fun i j => X i j ω) 0 n}
      ≤ Filter.liminf
          (fun k : ℕ => P {ω | GreedyRS.Greedy.greedySelect k ⌊c * k⌋₊ (fun i j => X i j ω) ≠ 0}) atTop := by
  open GreedyRS.Greedy GreedyRS.Tight in
  have hσ : 0 < Real.sqrt w := Real.sqrt_pos.2 (by exact_mod_cast hw)
  have hv : ∀ i, 0 < v i := fun i => by rw [hcv i]; exact hw
  have hCpos : 0 < Cfun (γ / Real.sqrt w) := by unfold Cfun; exact Real.exp_pos _
  have hcpos : 0 < c := by linarith
  have hεpos : 0 < ε := by linarith [hε.1]
  have hL2 := (GreedyRS.Greedy.lemma2_crossing_time).1
  -- levels
  have hxm : (μ 0 - γm - (μ 0 - γ)) / Real.sqrt w = (γ - γm) / Real.sqrt w := by ring_nf
  have hxp : (μ 0 - γp - (μ 0 - γ)) / Real.sqrt w = (γ - γp) / Real.sqrt w := by ring_nf
  have hxm0 : 0 < (γ - γm) / Real.sqrt w := div_pos (by linarith [hγm.2]) hσ
  have hxp0 : 0 < (γ - γp) / Real.sqrt w := div_pos (by linarith [hγp.2]) hσ
  have hSm := G11.slln_cross P μ v X hX γ hslip w hw hcv (μ 0 - γm)
    (by rw [hxm]; exact (hL2 _ hxm0).1) (by rw [hxm]; exact (hL2 _ hxm0).2)
  have hSp := G11.slln_cross P μ v X hX γ hslip w hw hcv (μ 0 - γp)
    (by rw [hxp]; exact (hL2 _ hxp0).1) (by rw [hxp]; exact (hL2 _ hxp0).2)
  rw [hxm, hCm] at hSm
  rw [hxp, hCp] at hSp
  -- the events of (EC.1.8)
  set E : ℕ → Set Ω := fun k => {ω | ∃ m : ℕ,
      crossBelow (runMean (fun i j => X i j ω) 0) (μ 0 - γp) 1 = m ∧
      (∑ i ∈ Finset.Ico 1 k, prefixCross (runMean (fun i j => X i j ω) i)
          (runMean (fun i j => X i j ω) 0) (m - 1)) + m ≤ ⌊c * k⌋₊ ∧
      ((⌊c * k⌋₊ : ℕ) : ℕ∞) < (∑ i ∈ Finset.Ico 1 k, prefixCross (runMean (fun i j => X i j ω) i)
          (runMean (fun i j => X i j ω) 0) m) + m} with hE
  have hEle : ∀ k : ℕ, P (E k) ≤
      P {ω | greedySelect k ⌊c * k⌋₊ (fun i j => X i j ω) ≠ 0} := fun k =>
    GreedyRS.Tight.ec1_8_pics_event P μ v X hX hv k ⌊c * k⌋₊ γp
  set Bε := {ω | ∃ m : ℕ, crossBelow (runMean (fun i j => X i j ω) 0) (μ 0 - γp) 1 = m ∧
        ∀ n ∈ Finset.Icc 1 (m - 1), μ 0 - γm ≤ runMean (fun i j => X i j ω) 0 n} with hBε
  set G : Set Ω := {ω | ((∀ i, crossBelow (runMean (fun i j => X i j ω) (i + 1)) (μ 0 - γm) 1 < ⊤) ∧
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        ((crossBelow (runMean (fun i j => X i j ω) (i + 1)) (μ 0 - γm) 1 : ℕ∞) : ℝ≥0∞).toReal)
        atTop (𝓝 (c - 2 * ε))) ∧
      ((∀ i, crossBelow (runMean (fun i j => X i j ω) (i + 1)) (μ 0 - γp) 1 < ⊤) ∧
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        ((crossBelow (runMean (fun i j => X i j ω) (i + 1)) (μ 0 - γp) 1 : ℕ∞) : ℝ≥0∞).toReal)
        atTop (𝓝 (c + 2 * ε)))} with hG
  have hGc : P Gᶜ = 0 := by
    have := hSm.and hSp
    rw [ae_iff] at this
    exact this
  set D : ℕ → Set Ω := fun K => ⋂ k, ⋂ (_ : K ≤ k), E k with hD
  have hDmono : Monotone D := by
    intro K K' hKK' ω hω
    simp only [hD, Set.mem_iInter] at hω ⊢
    exact fun k hk => hω k (hKK'.trans hk)
  -- pathwise inclusion
  have hsub : Bε ∩ G ⊆ ⋃ K, D K := by
    rintro ω ⟨⟨m, hm, hbefore⟩, ⟨⟨hfm, htm⟩, ⟨hfp, htp⟩⟩⟩
    obtain ⟨hm1, hym⟩ := G11.crossBelow_spec' _ _ _ hm
    set y : ℕ → ℕ → ℝ := fun i => runMean (fun i j => X i j ω) i with hy
    -- finite values
    choose a ha using fun i => ENat.ne_top_iff_exists.1 (hfm i).ne
    choose b hb using fun i => ENat.ne_top_iff_exists.1 (hfp i).ne
    have hta : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (a i : ℝ)) atTop
        (𝓝 (c - 2 * ε)) := by
      refine htm.congr fun n => ?_
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← ha i]; simp
    have htb : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (b i : ℝ)) atTop
        (𝓝 (c + 2 * ε)) := by
      refine htp.congr fun n => ?_
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hb i]; simp
    have hev1 : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (a i : ℝ) < c - ε :=
      hta.eventually (gt_mem_nhds (by linarith))
    have hev2 : ∀ᶠ n : ℕ in atTop, c + ε < (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (b i : ℝ) :=
      htb.eventually (lt_mem_nhds (by linarith))
    have hev3 : ∀ᶠ n : ℕ in atTop, (m : ℝ) + c ≤ (n : ℝ) * ε := by
      have : Tendsto (fun n : ℕ => (n : ℝ) * ε) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_mul_const hεpos
      exact this.eventually_ge_atTop _
    have hev4 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
    obtain ⟨N, hN⟩ := eventually_atTop.1 (((hev1.and hev2).and hev3).and hev4)
    refine Set.mem_iUnion.2 ⟨N + 1, ?_⟩
    simp only [hD, Set.mem_iInter]
    intro k hk
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hN (k - 1) (by omega)
    have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have hkpos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < k - 1 by omega)
    rw [inv_mul_lt_iff₀ hkpos] at h1
    rw [lt_inv_mul_iff₀ hkpos] at h2
    -- reindex the sums over `Ico 1 k`
    have hre : ∀ f : ℕ → ℕ∞, ∑ i ∈ Finset.Ico 1 k, f i = ∑ i ∈ Finset.range (k - 1), f (i + 1) := by
      intro f
      rw [Finset.sum_Ico_eq_sum_range]
      exact Finset.sum_congr rfl fun i _ => by rw [add_comm]
    refine ⟨m, hm, ?_, ?_⟩
    · -- lower half
      have hle : ∑ i ∈ Finset.Ico 1 k, prefixCross (y i) (y 0) (m - 1) ≤
          ((∑ i ∈ Finset.range (k - 1), a i : ℕ) : ℕ∞) := by
        rw [hre, Nat.cast_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [ha i]
        exact G11.prefixCross_le_crossBelow _ _ _ _ hbefore
      have hnat : (∑ i ∈ Finset.range (k - 1), a i) + m ≤ ⌊c * k⌋₊ := by
        apply Nat.le_floor
        push_cast
        have : ((k - 1 : ℕ) : ℝ) * (c - ε) + m ≤ c * k := by rw [hk1] at h3 ⊢; nlinarith [hcpos]
        linarith
      calc (∑ i ∈ Finset.Ico 1 k, prefixCross (y i) (y 0) (m - 1)) + (m : ℕ∞)
          ≤ ((∑ i ∈ Finset.range (k - 1), a i : ℕ) : ℕ∞) + m := by gcongr
        _ = (((∑ i ∈ Finset.range (k - 1), a i) + m : ℕ) : ℕ∞) := by push_cast; rfl
        _ ≤ (⌊c * k⌋₊ : ℕ∞) := by exact_mod_cast hnat
    · -- upper half
      have hge : ((∑ i ∈ Finset.range (k - 1), b i : ℕ) : ℕ∞) ≤
          ∑ i ∈ Finset.Ico 1 k, prefixCross (y i) (y 0) m := by
        rw [hre, Nat.cast_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hb i]
        exact G11.crossBelow_le_prefixCross _ _ _ _ hm1 hym
      have hnat : ⌊c * k⌋₊ < (∑ i ∈ Finset.range (k - 1), b i) + m := by
        have hfl : (⌊c * k⌋₊ : ℝ) ≤ c * k := Nat.floor_le (by positivity)
        have hmpos : (1 : ℝ) ≤ m := by exact_mod_cast hm1
        have : c * k < ((k - 1 : ℕ) : ℝ) * (c + ε) + m := by rw [hk1] at h3 ⊢; nlinarith [hmpos, h3, hcpos]
        have : (⌊c * k⌋₊ : ℝ) < ((∑ i ∈ Finset.range (k - 1), b i + m : ℕ) : ℝ) := by
          push_cast; linarith
        exact_mod_cast this
      calc ((⌊c * k⌋₊ : ℕ) : ℕ∞) < (((∑ i ∈ Finset.range (k - 1), b i) + m : ℕ) : ℕ∞) := by
            exact_mod_cast hnat
        _ = ((∑ i ∈ Finset.range (k - 1), b i : ℕ) : ℕ∞) + m := by push_cast; rfl
        _ ≤ (∑ i ∈ Finset.Ico 1 k, prefixCross (y i) (y 0) m) + m := by gcongr
  -- measure-theoretic conclusion
  have hliminf : ⨆ K, P (D K) ≤ Filter.liminf (fun k : ℕ => P (E k)) atTop := by
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
    refine iSup_mono fun K => le_iInf₂ fun k hk => measure_mono ?_
    intro ω hω
    simp only [hD, Set.mem_iInter] at hω
    exact hω k hk
  calc P Bε ≤ P (Bε ∩ G) + P Gᶜ := by
        calc P Bε ≤ P ((Bε ∩ G) ∪ Gᶜ) := measure_mono (fun ω hω => by
                by_cases h : ω ∈ G
                · exact Or.inl ⟨hω, h⟩
                · exact Or.inr h)
          _ ≤ P (Bε ∩ G) + P Gᶜ := measure_union_le _ _
    _ = P (Bε ∩ G) := by rw [hGc, add_zero]
    _ ≤ P (⋃ K, D K) := measure_mono hsub
    _ = ⨆ K, P (D K) := hDmono.measure_iUnion
    _ ≤ Filter.liminf (fun k : ℕ => P (E k)) atTop := hliminf
    _ ≤ _ := Filter.liminf_le_liminf (Eventually.of_forall hEle)
