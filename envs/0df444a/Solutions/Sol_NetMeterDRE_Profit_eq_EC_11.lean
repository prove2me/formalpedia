-- Prove2me | solution 1 for NetMeterDRE.Profit.eq_EC_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T11:56:57.581754+00:00
-- url     : https://prove2.me/submissions/553786bb-d424-4aaa-9469-8c4f931230bd

import Mathlib
import Definitions.Def_NetMeterDRE_Profit_SFE
import Definitions.Def_NetMeterDRE_Profit_Model

namespace NetMeterDRE.Profit.SolAux

open MeasureTheory ProbabilityTheory

section BddLib

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Measurable and essentially bounded. -/
def Bdd (P : Measure Ω) (f : Ω → ℝ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ᵐ ω ∂P, |f ω| ≤ C

lemma Bdd.const (P : Measure Ω) (a : ℝ) : Bdd P (fun _ => a) :=
  ⟨measurable_const, |a|, Filter.Eventually.of_forall fun _ => le_rfl⟩

lemma Bdd.add {P : Measure Ω} {f g : Ω → ℝ} (hf : Bdd P f) (hg : Bdd P g) :
    Bdd P (fun ω => f ω + g ω) := by
  obtain ⟨mf, C, hC⟩ := hf
  obtain ⟨mg, C', hC'⟩ := hg
  refine ⟨mf.add mg, C + C', ?_⟩
  filter_upwards [hC, hC'] with ω h1 h2
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

lemma Bdd.neg {P : Measure Ω} {f : Ω → ℝ} (hf : Bdd P f) : Bdd P (fun ω => - f ω) := by
  obtain ⟨mf, C, hC⟩ := hf
  exact ⟨mf.neg, C, by filter_upwards [hC] with ω h; rwa [abs_neg]⟩

lemma Bdd.sub {P : Measure Ω} {f g : Ω → ℝ} (hf : Bdd P f) (hg : Bdd P g) :
    Bdd P (fun ω => f ω - g ω) := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

lemma Bdd.mul {P : Measure Ω} {f g : Ω → ℝ} (hf : Bdd P f) (hg : Bdd P g) :
    Bdd P (fun ω => f ω * g ω) := by
  obtain ⟨mf, C, hC⟩ := hf
  obtain ⟨mg, C', hC'⟩ := hg
  refine ⟨mf.mul mg, C * C', ?_⟩
  filter_upwards [hC, hC'] with ω h1 h2
  rw [abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

lemma Bdd.max0 {P : Measure Ω} {f : Ω → ℝ} (hf : Bdd P f) : Bdd P (fun ω => max (f ω) 0) := by
  obtain ⟨mf, C, hC⟩ := hf
  refine ⟨mf.max measurable_const, C, ?_⟩
  filter_upwards [hC] with ω h
  have : |max (f ω) 0| ≤ |f ω| := by
    rcases le_total (f ω) 0 with h' | h'
    · rw [max_eq_right h', abs_zero]; exact abs_nonneg _
    · rw [max_eq_left h']
  exact this.trans h

lemma Bdd.sum {ι : Type*} {P : Measure Ω} (s : Finset ι) (f : ι → Ω → ℝ)
    (h : ∀ i ∈ s, Bdd P (f i)) : Bdd P (fun ω => ∑ i ∈ s, f i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Bdd.const P 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma Bdd.integrable {P : Measure Ω} [IsFiniteMeasure P] {f : Ω → ℝ} (hf : Bdd P f) :
    Integrable f P := by
  obtain ⟨mf, C, hC⟩ := hf
  exact Integrable.mono' (integrable_const C) mf.aestronglyMeasurable
    (by filter_upwards [hC] with ω h; simpa [Real.norm_eq_abs] using h)

lemma Bdd.of_Icc {P : Measure Ω} {f : Ω → ℝ} {a b : ℝ} (hm : Measurable f)
    (h : ∀ᵐ ω ∂P, f ω ∈ Set.Icc a b) : Bdd P f := by
  refine ⟨hm, |a| + |b|, ?_⟩
  filter_upwards [h] with ω hω
  rw [abs_le]
  constructor
  · linarith [neg_abs_le a, abs_nonneg b, hω.1]
  · linarith [le_abs_self b, abs_nonneg a, hω.2]


/-- Replacing an independent factor by its mean inside an expectation. -/
lemma repl {P : Measure Ω} [IsProbabilityMeasure P] (F G R : Ω → ℝ) (hF : Bdd P F)
    (hG : Bdd P G) (hR : Bdd P R) (hind : IndepFun G R P) (a : ℝ) :
    ∫ ω, (F ω + a * G ω * R ω) ∂P = ∫ ω, (F ω + a * G ω * ∫ ω', R ω' ∂P) ∂P := by
  have h1 : ∫ ω, G ω * R ω ∂P = (∫ ω, G ω ∂P) * (∫ ω, R ω ∂P) :=
    hind.integral_fun_mul_eq_mul_integral hG.1.aestronglyMeasurable hR.1.aestronglyMeasurable
  have i1 : Integrable (fun ω => a * G ω * R ω) P := by
    have : Bdd P (fun ω => a * G ω * R ω) := by (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg))
    exact this.integrable
  have i2 : Integrable (fun ω => a * G ω * ∫ ω', R ω' ∂P) P := by
    have : Bdd P (fun ω => a * G ω * ∫ ω', R ω' ∂P) := by (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg))
    exact this.integrable
  rw [integral_add hF.integrable i1, integral_add hF.integrable i2]
  congr 1
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_const_mul, h1, integral_mul_const]

end BddLib

section Model
set_option linter.unusedSectionVars false

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

lemma pw_eq {N : ℕ} {c : ℝ} (hN : 2 < N) (hc : 0 < c) {pw : ℝ → ℝ}
    (hpw : ∀ x, IsClearing (fun _ : Fin N => symSupply N c) x (pw x)) :
    ∀ x, pw x = alpha N c * x := by
  intro x
  have h := hpw x
  unfold IsClearing symSupply at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hN' : (2 : ℝ) < N := by exact_mod_cast hN
  have h1 : (N : ℝ) - 2 ≠ 0 := by linarith
  have h2 : (N : ℝ) - 1 ≠ 0 := by linarith
  have h3 : (N : ℝ) ≠ 0 := by linarith
  have hc' : c ≠ 0 := hc.ne'
  unfold alpha
  conv_rhs => rw [← h]
  field_simp

lemma alpha_pos {N : ℕ} {c : ℝ} (hN : 2 < N) (hc : 0 < c) : 0 < alpha N c := by
  have hN' : (2 : ℝ) < N := by exact_mod_cast hN
  unfold alpha
  apply div_pos
  · apply mul_pos (by linarith); linarith
  · apply mul_pos (by linarith); linarith

/-- The rest of the market, written over the subtype `{i // i ≠ j}`. -/
noncomputable def Rs (U : Market ι) (j : ι) (D Δ : ι → Ω → ℝ) (ξ : Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i : {i // i ≠ j}, (U.beta * D i.1 ω - Δ i.1 ω - U.K i.1) + ξ ω

lemma setK_beta (U : Market ι) (j : ι) (k : ℝ) : (U.setK j k).beta = U.beta := rfl
lemma setK_pu (U : Market ι) (j : ι) (k : ℝ) : (U.setK j k).pu = U.pu := rfl
lemma setK_ct (U : Market ι) (j : ι) (k : ℝ) : (U.setK j k).ct = U.ct := rfl
lemma setK_Kj (U : Market ι) (j : ι) (k : ℝ) : (U.setK j k).K j = k := by
  simp [Market.setK]

lemma sum_erase_eq (j : ι) (f : ι → ℝ) :
    ∑ i ∈ Finset.univ.erase j, f i = ∑ i : {i // i ≠ j}, f i.1 :=
  Finset.sum_subtype (Finset.univ.erase j) (p := fun i => i ≠ j) (by simp) f

lemma netDemand_setK (U : Market ι) (j : ι) (k : ℝ) (D Δ : ι → Ω → ℝ) (ξ : Ω → ℝ) (ω : Ω) :
    netDemand (U.setK j k) D Δ ξ ω = (U.beta * D j ω - k - Δ j ω) + Rs U j D Δ ξ ω := by
  unfold netDemand Rs
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), sum_erase_eq, setK_Kj, setK_beta]
  have h2 : ∀ i : {i // i ≠ j}, U.beta * D i.1 ω - (U.setK j k).K i.1 - Δ i.1 ω
      = U.beta * D i.1 ω - Δ i.1 ω - U.K i.1 := fun i => by
    simp only [Market.setK, Function.update_of_ne i.2]; ring
  rw [Finset.sum_congr rfl (fun i _ => h2 i)]
  ring

lemma nu_eq (P : Measure Ω) (U : Market ι) (j : ι) (D Δ : ι → Ω → ℝ) (ξ : Ω → ℝ) :
    nu P U j D Δ ξ = ∫ ω, Rs U j D Δ ξ ω ∂P := by
  unfold nu Rs
  congr 1; funext ω
  rw [sum_erase_eq j (fun i => U.beta * D i ω - Δ i ω - U.K i)]

lemma nuHat_eq (P : Measure Ω) (U : Market ι) (j : ι) (D : ι → Ω → ℝ) (ξ : Ω → ℝ) :
    nuHat P U j D ξ = ∫ ω, Rs U j D (fun _ _ => 0) ξ ω ∂P := by
  unfold nuHat Rs
  congr 1; funext ω
  rw [sum_erase_eq j (fun i => U.beta * D i ω - U.K i)]
  simp

lemma integrand_r (U : Market ι) (j : ι) (k : ℝ) (D Δ : ι → Ω → ℝ) (ξ : Ω → ℝ)
    (pw : ℝ → ℝ) (a : ℝ) (hpw : ∀ x, pw x = a * x) (ω : Ω) :
    profitIntegrand (U.setK j k) pw .r j D Δ ξ ω =
      ((U.beta * D j ω - Δ j ω) * U.pu j
        + a * (Δ j ω + k - U.beta * D j ω) * (U.beta * D j ω - k - Δ j ω) - k * U.ct)
      + a * (Δ j ω + k - U.beta * D j ω) * Rs U j D Δ ξ ω := by
  simp only [profitIntegrand, buybackPrice, hpw, netDemand_setK, setK_Kj, setK_beta, setK_pu,
    setK_ct]
  have hmx : max (D j ω - Δ j ω) 0 - max (Δ j ω - D j ω) 0 = D j ω - Δ j ω := by
    rcases le_total (D j ω - Δ j ω) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  split_ifs with h1 h2 h2
  · exfalso; linarith
  · linear_combination (U.pu j) * hmx
  · linear_combination (U.pu j) * hmx
  · exfalso; push Not at h1 h2; linarith

lemma integrand_m (U : Market ι) (j : ι) (k : ℝ) (D Δ : ι → Ω → ℝ) (ξ : Ω → ℝ)
    (pw : ℝ → ℝ) (a : ℝ) (hpw : ∀ x, pw x = a * x) (ω : Ω) :
    profitIntegrand (U.setK j k) pw .m j D Δ ξ ω =
      ((U.beta * D j ω - D j ω + max (D j ω - Δ j ω) 0) * U.pu j
        + a * (Δ j ω + k - U.beta * D j ω - max (Δ j ω - D j ω) 0)
            * (U.beta * D j ω - k - Δ j ω) - k * U.ct)
      + a * (Δ j ω + k - U.beta * D j ω - max (Δ j ω - D j ω) 0) * Rs U j D Δ ξ ω := by
  simp only [profitIntegrand, buybackPrice, hpw, netDemand_setK, setK_Kj, setK_beta, setK_pu,
    setK_ct]
  split_ifs with h1 h2 h2
  · exfalso; linarith
  · ring
  · ring
  · exfalso; push Not at h1 h2; linarith

lemma integrand_0 (U : Market ι) (j : ι) (k : ℝ) (D : ι → Ω → ℝ) (ξ : Ω → ℝ)
    (pw : ℝ → ℝ) (a : ℝ) (hpw : ∀ x, pw x = a * x) (ω : Ω) :
    profitIntegrand (U.setK j k) pw .r j D (fun _ _ => 0) ξ ω =
      (U.beta * D j ω * U.pu j
        + a * (k - U.beta * D j ω) * (U.beta * D j ω - k) - k * U.ct)
      + a * (k - U.beta * D j ω) * Rs U j D (fun _ _ => 0) ξ ω := by
  rw [integrand_r U j k D (fun _ _ => 0) ξ pw a hpw ω]
  simp only [sub_zero, zero_add]

end Model

section Main
set_option linter.unusedSectionVars false

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {U : Market ι} {D Δ : ι → Ω → ℝ} {ξ : Ω → ℝ} {j : ι}

lemma bdd_Rs (hDB : ∀ i, Bdd P (D i)) (hΔB : ∀ i, Bdd P (Δ i)) (hξB : Bdd P ξ) :
    Bdd P (Rs U j D Δ ξ) := by
  unfold Rs
  refine Bdd.add ?_ hξB
  apply Bdd.sum
  intro i _
  have := hDB i.1
  have := hΔB i.1
  (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg))

lemma indep_gen (hI : RegionIndep P D Δ ξ j) (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) :
    IndepFun (fun ω => φ (D j ω, Δ j ω)) (Rs U j D Δ ξ) P :=
  hI.comp (φ := φ)
    (ψ := fun q : ({i // i ≠ j} → ℝ × ℝ) × ℝ =>
      ∑ i, (U.beta * (q.1 i).1 - (q.1 i).2 - U.K i.1) + q.2) hφ (by fun_prop)

lemma indep_gen0 (hI : RegionIndep P D Δ ξ j) (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) :
    IndepFun (fun ω => φ (D j ω, Δ j ω)) (Rs U j D (fun _ _ => 0) ξ) P :=
  hI.comp (φ := φ)
    (ψ := fun q : ({i // i ≠ j} → ℝ × ℝ) × ℝ =>
      ∑ i, (U.beta * (q.1 i).1 - 0 - U.K i.1) + q.2) hφ (by fun_prop)

end Main

section Main2
set_option linter.unusedSectionVars false

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {U : Market ι} {D Δ : ι → Ω → ℝ} {ξ : Ω → ℝ} {j : ι}

lemma expProfit_r_eq (hDB : ∀ i, Bdd P (D i)) (hΔB : ∀ i, Bdd P (Δ i)) (hξB : Bdd P ξ)
    (hI : RegionIndep P D Δ ξ j) (pw : ℝ → ℝ) (a : ℝ) (hpw : ∀ x, pw x = a * x) (k : ℝ) :
    expProfit P (U.setK j k) pw .r j D Δ ξ =
      ∫ ω, (((U.beta * D j ω - Δ j ω) * U.pu j
        + a * (Δ j ω + k - U.beta * D j ω) * (U.beta * D j ω - k - Δ j ω) - k * U.ct)
      + a * (Δ j ω + k - U.beta * D j ω) * nu P U j D Δ ξ) ∂P := by
  unfold expProfit
  simp_rw [integrand_r U j k D Δ ξ pw a hpw]
  have := hDB j
  have := hΔB j
  have hR := bdd_Rs (U := U) (j := j) hDB hΔB hξB
  rw [nu_eq]
  refine repl _ _ _ ?_ ?_ hR
    (indep_gen hI (fun p => p.2 + k - U.beta * p.1) (by fun_prop)) a
  · (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg))
  · (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg))

lemma expProfit_m_eq (hDB : ∀ i, Bdd P (D i)) (hΔB : ∀ i, Bdd P (Δ i)) (hξB : Bdd P ξ)
    (hI : RegionIndep P D Δ ξ j) (pw : ℝ → ℝ) (a : ℝ) (hpw : ∀ x, pw x = a * x) (k : ℝ) :
    expProfit P (U.setK j k) pw .m j D Δ ξ =
      ∫ ω, (((U.beta * D j ω - D j ω + max (D j ω - Δ j ω) 0) * U.pu j
        + a * (Δ j ω + k - U.beta * D j ω - max (Δ j ω - D j ω) 0)
            * (U.beta * D j ω - k - Δ j ω) - k * U.ct)
      + a * (Δ j ω + k - U.beta * D j ω - max (Δ j ω - D j ω) 0) * nu P U j D Δ ξ) ∂P := by
  unfold expProfit
  simp_rw [integrand_m U j k D Δ ξ pw a hpw]
  have := hDB j
  have := hΔB j
  have hR := bdd_Rs (U := U) (j := j) hDB hΔB hξB
  rw [nu_eq]
  refine repl _ _ _ ?_ ?_ hR
    (indep_gen hI (fun p => p.2 + k - U.beta * p.1 - max (p.2 - p.1) 0) (by fun_prop)) a
  · (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg))
  · (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg))

lemma noDRE_eq (hDB : ∀ i, Bdd P (D i)) (hξB : Bdd P ξ)
    (hI : RegionIndep P D Δ ξ j) (pw : ℝ → ℝ) (a : ℝ) (hpw : ∀ x, pw x = a * x) (k : ℝ) :
    noDREProfit P (U.setK j k) pw j D ξ =
      ∫ ω, ((U.beta * D j ω * U.pu j
        + a * (k - U.beta * D j ω) * (U.beta * D j ω - k) - k * U.ct)
      + a * (k - U.beta * D j ω) * nuHat P U j D ξ) ∂P := by
  unfold noDREProfit expProfit
  simp_rw [integrand_0 U j k D ξ pw a hpw]
  have := hDB j
  have h0 : ∀ i : ι, Bdd P ((fun (_ : ι) (_ : Ω) => (0:ℝ)) i) := fun _ => Bdd.const P 0
  have hR := bdd_Rs (U := U) (j := j) hDB h0 hξB
  rw [nuHat_eq]
  refine repl _ _ _ ?_ ?_ hR
    (indep_gen0 hI (fun p => k - U.beta * p.1) (by fun_prop)) a
  · (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg))
  · (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg))

end Main2

section Main3
set_option linter.unusedSectionVars false

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {U : Market ι} {D Δ : ι → Ω → ℝ} {ξ : Ω → ℝ} {j : ι}

lemma diff_r (hDB : ∀ i, Bdd P (D i)) (hΔB : ∀ i, Bdd P (Δ i)) (hξB : Bdd P ξ)
    (hI : RegionIndep P D Δ ξ j) (pw : ℝ → ℝ) (a : ℝ) (hpw : ∀ x, pw x = a * x) (k : ℝ) :
    expProfit P (U.setK j k) pw .r j D Δ ξ - noDREProfit P (U.setK j k) pw j D ξ =
      a * gammaDen P U .r j D Δ ξ - gammaNum P U .r j D Δ
        - k * (a * ∫ ω, (2 * Δ j ω + (nuHat P U j D ξ - nu P U j D Δ ξ)) ∂P) := by
  rw [expProfit_r_eq hDB hΔB hξB hI pw a hpw k, noDRE_eq hDB hξB hI pw a hpw k]
  have := hDB j
  have := hΔB j
  rw [← integral_sub (Bdd.integrable (by (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg)))) (Bdd.integrable (by (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg))))]
  simp only [gammaDen, gammaNum]
  rw [← integral_mul_const, ← integral_const_mul a, ← integral_const_mul a,
    ← integral_const_mul k, ← integral_sub (Bdd.integrable (by (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg)))) (Bdd.integrable (by (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg)))),
    ← integral_sub (Bdd.integrable (by (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg)))) (Bdd.integrable (by (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg))))]
  congr 1; funext ω; ring

lemma diff_m (hDB : ∀ i, Bdd P (D i)) (hΔB : ∀ i, Bdd P (Δ i)) (hξB : Bdd P ξ)
    (hI : RegionIndep P D Δ ξ j) (pw : ℝ → ℝ) (a : ℝ) (hpw : ∀ x, pw x = a * x) (k : ℝ) :
    expProfit P (U.setK j k) pw .m j D Δ ξ - noDREProfit P (U.setK j k) pw j D ξ =
      a * gammaDen P U .m j D Δ ξ - gammaNum P U .m j D Δ
        - k * (a * ∫ ω, (2 * Δ j ω + (nuHat P U j D ξ - nu P U j D Δ ξ)
            - max (Δ j ω - D j ω) 0) ∂P) := by
  rw [expProfit_m_eq hDB hΔB hξB hI pw a hpw k, noDRE_eq hDB hξB hI pw a hpw k]
  have := hDB j
  have := hΔB j
  rw [← integral_sub (Bdd.integrable (by (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg)))) (Bdd.integrable (by (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg))))]
  simp only [gammaDen, gammaNum]
  rw [← integral_mul_const, ← integral_const_mul a, ← integral_const_mul a,
    ← integral_const_mul k, ← integral_sub (Bdd.integrable (by (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg)))) (Bdd.integrable (by (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg)))),
    ← integral_sub (Bdd.integrable (by (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg)))) (Bdd.integrable (by (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg))))]
  congr 1; funext ω; ring

end Main3

section Final
set_option linter.unusedSectionVars false

lemma final_logic (α num den B A : ℝ) (diff : ℝ → ℝ) (hα : 0 < α) (hnum : 0 ≤ num)
    (hB : 0 ≤ B) (hB0 : B = 0 → A ≤ 0) (hA : A = α * den - num)
    (hdiff : ∀ k, diff k = A - k * B) :
    ∃ Kbar : ℝ, ∀ k : ℝ, 0 ≤ k → (0 < diff k ↔ k < Kbar ∧ num / den < α) := by
  have key : 0 < A → num / den < α := by
    intro hA0
    have hden : 0 < den := by
      by_contra h
      push Not at h
      nlinarith
    rw [div_lt_iff₀ hden]; linarith
  rcases hB.lt_or_eq with hBpos | hBz
  · by_cases hg : num / den < α
    · refine ⟨A / B, fun k _ => ?_⟩
      rw [hdiff, lt_div_iff₀ hBpos]
      simp only [hg, and_true]
      constructor <;> intro h <;> linarith
    · refine ⟨0, fun k hk => ?_⟩
      have hA0 : A ≤ 0 := by
        by_contra h
        exact hg (key (lt_of_not_ge h))
      rw [hdiff]
      constructor
      · intro h; nlinarith
      · intro h; exact absurd h.2 hg
  · refine ⟨0, fun k hk => ?_⟩
    have hA0 := hB0 hBz.symm
    rw [hdiff, ← hBz, mul_zero, sub_zero]
    constructor
    · intro h; linarith
    · intro h; linarith [h.1]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma bzero (b δ : Ω → ℝ) (s : ℝ) (hb : Bdd P b) (hδ : ∀ᵐ ω ∂P, 0 ≤ δ ω) (hs : 0 ≤ s)
    (hlow : ∀ᵐ ω ∂P, δ ω + s ≤ b ω) (h0 : ∫ ω, b ω ∂P = 0) :
    (∀ᵐ ω ∂P, δ ω = 0) ∧ s = 0 := by
  have hnn : 0 ≤ᵐ[P] b := by
    filter_upwards [hδ, hlow] with ω h1 h2
    show 0 ≤ b ω
    linarith
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hb.integrable).1 h0
  have hall : ∀ᵐ ω ∂P, δ ω = 0 ∧ s = 0 := by
    filter_upwards [hz, hδ, hlow] with ω h1 h2 h3
    have : b ω = 0 := h1
    constructor <;> linarith
  refine ⟨hall.mono fun ω h => h.1, ?_⟩
  obtain ⟨ω, h⟩ := hall.exists
  exact h.2

end Final

end NetMeterDRE.Profit.SolAux


namespace NetMeterDRE.Profit.SolAux
open MeasureTheory ProbabilityTheory
lemma setK_self {ι : Type*} [DecidableEq ι] (U : Market ι) (j : ι) : U.setK j (U.K j) = U := by
  cases U
  simp [Market.setK]
lemma integral_add_const' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Integrable f P) (c : ℝ) : ∫ ω, (f ω + c) ∂P = ∫ ω, f ω ∂P + c := by
  rw [integral_add hf (integrable_const c)]
  simp
end NetMeterDRE.Profit.SolAux

open MeasureTheory ProbabilityTheory NetMeterDRE.Profit NetMeterDRE.Profit.SolAux

theorem solution {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : ℕ) (c : ℝ) (U : Market ι)
    (D Δ : ι → Ω → ℝ) (ξ : Ω → ℝ) (j : ι)
    (hS : Standing N c U) (hR : Primitives P U D Δ ξ) (hI : RegionIndep P D Δ ξ j)
    (pw : ℝ → ℝ) (hpw : ∀ x, IsClearing (fun _ : Fin N => symSupply N c) x (pw x))
    :
    expProfit P U pw .m j D Δ ξ =
        U.pu j * ∫ ω, (U.beta * D j ω - D j ω + max (D j ω - Δ j ω) 0) ∂P
        + ∫ ω, ((Δ j ω + U.K j - U.beta * D j ω) - max (Δ j ω - D j ω) 0)
            * (alpha N c * (U.beta * D j ω - U.K j - Δ j ω + nu P U j D Δ ξ)) ∂P
        - U.K j * U.ct := by
  obtain ⟨hN, hc, -, hct, hpuct, -⟩ := hS
  obtain ⟨hDm, hΔm, hξm, hDb, hΔb, hξb, -⟩ := hR
  have hDB : ∀ i, Bdd P (D i) := fun i => Bdd.of_Icc (hDm i) (hDb i)
  have hΔB : ∀ i, Bdd P (Δ i) := fun i => Bdd.of_Icc (hΔm i) (hΔb i)
  have hξB : Bdd P ξ := Bdd.of_Icc hξm hξb
  have hpw' := pw_eq hN hc hpw
  have hα := alpha_pos hN hc
  have hpu : 0 < U.pu j := hct.trans (hpuct j)
  have := hDB j
  have := hΔB j
  have e : expProfit P U pw .m j D Δ ξ = expProfit P (U.setK j (U.K j)) pw .m j D Δ ξ := by
    rw [setK_self]
  rw [e, expProfit_m_eq hDB hΔB hξB hI pw _ hpw' (U.K j), ← integral_const_mul,
    ← integral_add (Bdd.integrable (by (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg))))
      (Bdd.integrable (by (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg))))]
  rw [eq_sub_iff_add_eq, ← integral_add_const' _ (Bdd.integrable (by (repeat (first | assumption | apply Bdd.const | apply Bdd.add | apply Bdd.sub | apply Bdd.mul | apply Bdd.max0 | apply Bdd.neg))))]
  congr 1; funext ω; ring
