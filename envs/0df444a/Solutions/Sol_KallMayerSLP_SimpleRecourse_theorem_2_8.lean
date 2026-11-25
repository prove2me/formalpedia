-- Prove2me | solution 1 for KallMayerSLP.SimpleRecourse.theorem_2_8
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-25T08:29:39.369064+00:00
-- url     : https://prove2.me/submissions/10f06e14-ddf4-4ac9-addd-c769e65eb68f

import Mathlib
import Definitions.Def_KallMayerSLP_SimpleRecourse_IsMSRTData
import Definitions.Def_KallMayerSLP_SimpleRecourse_expectedMSRT
import Definitions.Def_KallMayerSLP_SimpleRecourse_mixtureCdf
import Definitions.Def_KallMayerSLP_SimpleRecourse_mixtureConst
import Definitions.Def_KallMayerSLP_SimpleRecourse_IsOptimal259

open MeasureTheory ProbabilityTheory
open KallMayerSLP.SimpleRecourse

/-- Nonnegative reweighting of the `u`-shifted components (the `k = 0` weights are merged). -/
noncomputable def srWU {K : ℕ} (α β : Fin K → ℝ) (k : Fin K) : ℝ :=
  if k.val = 0 then α k + β k else α k

/-- Nonnegative reweighting of the `l`-shifted components. -/
noncomputable def srWL {K : ℕ} (β : Fin K → ℝ) (k : Fin K) : ℝ :=
  if k.val = 0 then 0 else β k

/-- Part 1: the reweighting does not change any `α/β`-combination whose `k = 0` terms agree. -/
lemma sr_reweight {K : ℕ} (α β gu gl : Fin K → ℝ) (h0 : ∀ k : Fin K, k.val = 0 → gu k = gl k) :
    ∑ k, α k * gu k + ∑ k, β k * gl k = ∑ k, srWU α β k * gu k + ∑ k, srWL β k * gl k := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k.val = 0
  · simp only [srWU, srWL, hk, if_true, h0 k hk]; ring
  · simp only [srWU, srWL, hk, if_false]

lemma sr_wU_nonneg {K : ℕ} {α β u l : Fin K → ℝ} (hd : IsMSRTData K α β u l) (k : Fin K) :
    0 ≤ srWU α β k := by
  unfold srWU; split_ifs with hk
  · exact hd.nonneg_zero k hk
  · exact hd.alpha_nonneg k hk

lemma sr_wL_nonneg {K : ℕ} {α β u l : Fin K → ℝ} (hd : IsMSRTData K α β u l) (k : Fin K) :
    0 ≤ srWL β k := by
  unfold srWL; split_ifs with hk
  · exact le_rfl
  · exact hd.beta_nonneg k hk

lemma sr_sum_w {K : ℕ} (α β : Fin K → ℝ) :
    ∑ k, (srWU α β k + srWL β k) = ∑ k, (α k + β k) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold srWU srWL; split_ifs <;> ring

/-- The mixture measure `ν₀`. -/
noncomputable def srMix {K : ℕ} (α β u l : Fin K → ℝ) (P : Measure ℝ) : Measure ℝ :=
  (ENNReal.ofReal (∑ k, (α k + β k)))⁻¹ •
    ∑ k, (ENNReal.ofReal (srWU α β k) • P.map (fun ξ => ξ - u k) +
      ENNReal.ofReal (srWL β k) • P.map (fun ξ => ξ + l k))

/-- Part 2: integrals against the mixture. -/
lemma sr_integral_mix {K : ℕ} {α β u l : Fin K → ℝ} (hd : IsMSRTData K α β u l)
    (P : Measure ℝ) (g : ℝ → ℝ)
    (hu : ∀ k, Integrable g (P.map (fun ξ => ξ - u k)))
    (hl : ∀ k, Integrable g (P.map (fun ξ => ξ + l k))) :
    ∫ x, g x ∂(srMix α β u l P) =
      (∑ k, (srWU α β k * ∫ x, g x ∂(P.map (fun ξ => ξ - u k)) +
        srWL β k * ∫ x, g x ∂(P.map (fun ξ => ξ + l k)))) / ∑ k, (α k + β k) := by
  have hS := hd.sum_pos
  unfold srMix
  rw [integral_smul_measure, integral_finset_sum_measure]
  · rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hS.le, smul_eq_mul, div_eq_inv_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_add_measure ((hu k).smul_measure ENNReal.ofReal_ne_top)
      ((hl k).smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal (sr_wU_nonneg hd k), ENNReal.toReal_ofReal (sr_wL_nonneg hd k),
      smul_eq_mul, smul_eq_mul]
  · intro k _
    exact ((hu k).smul_measure ENNReal.ofReal_ne_top).add_measure
      ((hl k).smul_measure ENNReal.ofReal_ne_top)

/-- Part 3: the mixture is a probability measure. -/
lemma sr_mix_prob {K : ℕ} {α β u l : Fin K → ℝ} (hd : IsMSRTData K α β u l)
    (P : Measure ℝ) [IsProbabilityMeasure P] : IsProbabilityMeasure (srMix α β u l P) := by
  constructor
  have hS := hd.sum_pos
  unfold srMix
  simp only [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, Measure.add_apply,
    smul_eq_mul]
  have hm : ∀ k, (P.map (fun ξ => ξ - u k)) Set.univ = 1 ∧ (P.map (fun ξ => ξ + l k)) Set.univ = 1 :=
    fun k => ⟨by rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]; simp,
      by rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]; simp⟩
  simp only [hm, mul_one]
  rw [show (∑ k, (ENNReal.ofReal (srWU α β k) + ENNReal.ofReal (srWL β k))) =
      ENNReal.ofReal (∑ k, (α k + β k)) by
    rw [← sr_sum_w, ENNReal.ofReal_sum_of_nonneg
      (fun k _ => add_nonneg (sr_wU_nonneg hd k) (sr_wL_nonneg hd k))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ENNReal.ofReal_add (sr_wU_nonneg hd _) (sr_wL_nonneg hd _)]]
  exact ENNReal.inv_mul_cancel (by simpa using hS) ENNReal.ofReal_ne_top

/-- Part 4: integrals of `(x - z)^±` against a shifted law. -/
lemma sr_shift_facts (P : Measure ℝ) [IsProbabilityMeasure P] (hP : Integrable (fun ξ => ξ) P)
    (φ : ℝ → ℝ) (c : ℝ) (hφ : φ = fun ξ => ξ + c) (z : ℝ) :
    Integrable (fun x => (x - z)⁺) (P.map φ) ∧ Integrable (fun x => (x - z)⁻) (P.map φ) ∧
    ∫ x, (x - z)⁺ ∂(P.map φ) = ∫ ξ, (ξ + c - z)⁺ ∂P ∧
    ∫ x, (x - z)⁻ ∂(P.map φ) = ∫ ξ, (ξ + c - z)⁻ ∂P ∧
    ∫ x, (x - z)⁺ ∂(P.map φ) - ∫ x, (x - z)⁻ ∂(P.map φ) = (∫ ξ, ξ ∂P) + c - z := by
  subst hφ
  have hφm : Measurable (fun ξ : ℝ => ξ + c) := by fun_prop
  have hlin : Integrable (fun ξ => ξ + c - z) P := (hP.add (integrable_const c)).sub
    (integrable_const z)
  have hpos : Integrable (fun ξ => (ξ + c - z)⁺) P := by
    simpa [posPart, max_comm] using hlin.pos_part
  have hneg : Integrable (fun ξ => (ξ + c - z)⁻) P := by
    simpa [negPart, max_comm] using hlin.neg_part
  have hm1 : ∫ x, (x - z)⁺ ∂(P.map (fun ξ => ξ + c)) = ∫ ξ, (ξ + c - z)⁺ ∂P :=
    integral_map hφm.aemeasurable (by fun_prop)
  have hm2 : ∫ x, (x - z)⁻ ∂(P.map (fun ξ => ξ + c)) = ∫ ξ, (ξ + c - z)⁻ ∂P :=
    integral_map hφm.aemeasurable (by fun_prop)
  refine ⟨(integrable_map_measure (by fun_prop) hφm.aemeasurable).mpr hpos,
    (integrable_map_measure (by fun_prop) hφm.aemeasurable).mpr hneg, hm1, hm2, ?_⟩
  rw [hm1, hm2, ← integral_sub hpos hneg]
  simp only [posPart_sub_negPart]
  have e : ∫ a, (a + c - z) ∂P = ∫ a, (a + c) ∂P - ∫ _a, z ∂P :=
    integral_sub (hP.add (integrable_const c)) (integrable_const z)
  have e2 : ∫ a, (a + c) ∂P = ∫ a, a ∂P + ∫ _a, c ∂P := integral_add hP (integrable_const c)
  rw [e, e2]; simp

/-- Part 5: the distribution function of the mixture. -/
lemma sr_mix_cdf {K : ℕ} {α β u l : Fin K → ℝ} (hd : IsMSRTData K α β u l)
    (P : Measure ℝ) [IsProbabilityMeasure P] :
    haveI := sr_mix_prob hd P
    ⇑(cdf (srMix α β u l P)) = mixtureCdf α β u l P := by
  haveI := sr_mix_prob hd P
  funext x
  have hfin : ∀ (c : ℝ), IsProbabilityMeasure (P.map (fun ξ => ξ + c)) :=
    fun c => Measure.isProbabilityMeasure_map (by fun_prop)
  have hmapU : ∀ k, (P.map (fun ξ => ξ - u k)) = P.map (fun ξ => ξ + (-u k)) := by
    intro k; simp only [sub_eq_add_neg]
  have hind : ∀ c : ℝ, ∫ y, (Set.Iic x).indicator (1 : ℝ → ℝ) y ∂(P.map (fun ξ => ξ + c)) =
      cdf P (x - c) := by
    intro c
    rw [integral_indicator_one measurableSet_Iic, cdf_eq_real, measureReal_def, measureReal_def,
      Measure.map_apply (by fun_prop) measurableSet_Iic]
    all_goals (congr 2; ext ξ; simp [le_sub_iff_add_le])
  have hint : ∀ c : ℝ, Integrable ((Set.Iic x).indicator (1 : ℝ → ℝ)) (P.map (fun ξ => ξ + c)) :=
    fun c => (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  rw [cdf_eq_real, measureReal_def, ← measureReal_def, ← integral_indicator_one measurableSet_Iic,
    sr_integral_mix hd P _ (fun k => by rw [hmapU]; exact hint _) (fun k => hint (l k))]
  unfold mixtureCdf mixtureH
  congr 1
  rw [sr_reweight α β (fun k => cdf P (x + u k)) (fun k => cdf P (x - l k))
    (fun k hk => by simp [hd.u_zero k hk, hd.l_zero k hk]), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hmapU, hind, hind]
  simp

theorem solution {K : ℕ} (α β u l : Fin K → ℝ) (hd : IsMSRTData K α β u l) (γ : ℝ)
    (P : Measure ℝ) [IsProbabilityMeasure P] (hP : Integrable (fun ξ => ξ) P) :
    (∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ⇑(cdf ν) = mixtureCdf α β u l P) ∧
    ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ⇑(cdf ν) = mixtureCdf α β u l P →
      (∀ z : ℝ,
        ∑ k, α k * ∫ ξ, (ξ - z)⁺ ∂(P.map (fun ξ => ξ - u k)) +
            ∑ k, β k * ∫ ξ, (ξ - z)⁻ ∂(P.map (fun ξ => ξ + l k)) =
          (∑ k, α k) * ∫ ξ, (ξ - z)⁺ ∂ν + (∑ k, β k) * ∫ ξ, (ξ - z)⁻ ∂ν -
            mixtureConst α β u l) ∧
      (∀ z : ℝ, expectedMSRT α β u l γ P z =
          (∑ k, α k) * ∫ ξ, (ξ - z)⁺ ∂ν + (∑ k, β k) * ∫ ξ, (ξ - z)⁻ ∂ν -
            mixtureConst α β u l - γ) ∧
      (∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c t : Fin n → ℝ)
          (x : Fin n → ℝ) (z : ℝ),
        IsOptimal259 A b c t (expectedMSRT α β u l γ P) x z ↔
          IsOptimal259 A b c t
            (fun z' => (∑ k, α k) * ∫ ξ, (ξ - z')⁺ ∂ν + (∑ k, β k) * ∫ ξ, (ξ - z')⁻ ∂ν -
              mixtureConst α β u l) x z) := by
  haveI hmixP := sr_mix_prob hd P
  refine ⟨⟨srMix α β u l P, hmixP, sr_mix_cdf hd P⟩, fun ν hν hcdf => ?_⟩
  have hνeq : ν = srMix α β u l P := by
    apply Measure.eq_of_cdf
    ext x
    exact congrFun (hcdf.trans (sr_mix_cdf hd P).symm) x
  subst hνeq
  -- Part 6: the identity (2.60) = (2.61).
  have hid : ∀ z : ℝ,
      ∑ k, α k * ∫ ξ, (ξ - z)⁺ ∂(P.map (fun ξ => ξ - u k)) +
          ∑ k, β k * ∫ ξ, (ξ - z)⁻ ∂(P.map (fun ξ => ξ + l k)) =
        (∑ k, α k) * ∫ ξ, (ξ - z)⁺ ∂(srMix α β u l P) +
          (∑ k, β k) * ∫ ξ, (ξ - z)⁻ ∂(srMix α β u l P) - mixtureConst α β u l := by
    intro z
    have hS : 0 < ∑ k, (α k + β k) := hd.sum_pos
    have hU := fun k => sr_shift_facts P hP (fun ξ => ξ - u k) (-u k)
      (by funext ξ; ring) z
    have hL := fun k => sr_shift_facts P hP (fun ξ => ξ + l k) (l k) rfl z
    have h0 : ∀ k : Fin K, k.val = 0 →
        (fun ξ : ℝ => ξ - u k) = (fun ξ : ℝ => ξ + l k) := by
      intro k hk; funext ξ; simp [hd.u_zero k hk, hd.l_zero k hk]
    have hmixpos : ∫ ξ, (ξ - z)⁺ ∂(srMix α β u l P) =
        (∑ k, α k * ∫ ξ, (ξ - z)⁺ ∂(P.map (fun ξ => ξ - u k)) +
          ∑ k, β k * ∫ ξ, (ξ - z)⁺ ∂(P.map (fun ξ => ξ + l k))) / ∑ k, (α k + β k) := by
      rw [sr_integral_mix hd P _ (fun k => (hU k).1) (fun k => (hL k).1)]
      congr 1
      rw [sr_reweight α β _ _ (fun k hk => by rw [h0 k hk]), ← Finset.sum_add_distrib]
    have hmixneg : ∫ ξ, (ξ - z)⁻ ∂(srMix α β u l P) =
        (∑ k, α k * ∫ ξ, (ξ - z)⁻ ∂(P.map (fun ξ => ξ - u k)) +
          ∑ k, β k * ∫ ξ, (ξ - z)⁻ ∂(P.map (fun ξ => ξ + l k))) / ∑ k, (α k + β k) := by
      rw [sr_integral_mix hd P _ (fun k => (hU k).2.1) (fun k => (hL k).2.1)]
      congr 1
      rw [sr_reweight α β _ _ (fun k hk => by rw [h0 k hk]), ← Finset.sum_add_distrib]
    set m := ∫ ξ, ξ ∂P with hm
    have h1 : ∑ k, α k * ∫ ξ, (ξ - z)⁺ ∂(P.map (fun ξ => ξ - u k)) =
        ∑ k, α k * ∫ ξ, (ξ - z)⁻ ∂(P.map (fun ξ => ξ - u k)) + (∑ k, α k) * (m - z) -
          ∑ k, α k * u k := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := (hU k).2.2.2.2
      linear_combination α k * this
    have h2 : ∑ k, β k * ∫ ξ, (ξ - z)⁺ ∂(P.map (fun ξ => ξ + l k)) =
        ∑ k, β k * ∫ ξ, (ξ - z)⁻ ∂(P.map (fun ξ => ξ + l k)) + (∑ k, β k) * (m - z) +
          ∑ k, β k * l k := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := (hL k).2.2.2.2
      linear_combination β k * this
    have hAB : ∑ k, (α k + β k) = ∑ k, α k + ∑ k, β k := Finset.sum_add_distrib
    rw [hmixpos, hmixneg, h1, h2]
    unfold mixtureConst
    rw [hAB] at hS ⊢
    field_simp
    ring
  -- Part 7: the expected MSRT function.
  have hposI : ∀ a : ℝ, Integrable (fun ξ => (ξ - a)⁺) P := fun a => by
    simpa [posPart, max_comm] using (hP.sub (integrable_const a)).pos_part
  have hnegI : ∀ a : ℝ, Integrable (fun ξ => (ξ - a)⁻) P := fun a => by
    simpa [negPart, max_comm] using (hP.sub (integrable_const a)).neg_part
  have hmsrt : ∀ z : ℝ, expectedMSRT α β u l γ P z =
      (∑ k, α k) * ∫ ξ, (ξ - z)⁺ ∂(srMix α β u l P) +
        (∑ k, β k) * ∫ ξ, (ξ - z)⁻ ∂(srMix α β u l P) - mixtureConst α β u l - γ := by
    intro z
    rw [← hid z]
    unfold expectedMSRT
    have hp : ∀ k, (fun ξ => (ξ - z - u k)⁺) = (fun ξ => (ξ - (z + u k))⁺) := fun k => by
      funext ξ; ring_nf
    have hn : ∀ k, (fun ξ => (ξ - z + l k)⁻) = (fun ξ => (ξ - (z - l k))⁻) := fun k => by
      funext ξ; ring_nf
    rw [integral_finset_sum]
    · congr 1
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_add ((hp k ▸ hposI (z + u k)).const_mul (α k))
        ((hn k ▸ hnegI (z - l k)).const_mul (β k)), integral_const_mul, integral_const_mul]
      have hU := (sr_shift_facts P hP (fun ξ => ξ - u k) (-u k) (by funext ξ; ring) z).2.2.1
      have hL := (sr_shift_facts P hP (fun ξ => ξ + l k) (l k) rfl z).2.2.2.1
      rw [hU, hL]
      congr 2
      · congr 1; funext ξ; ring_nf
      · congr 1; funext ξ; ring_nf
    · intro k _
      exact ((hp k ▸ hposI (z + u k)).const_mul (α k)).add
        ((hn k ▸ hnegI (z - l k)).const_mul (β k))
  refine ⟨hid, hmsrt, ?_⟩
  -- Part 8: the two problems differ by the constant `γ`.
  intro m n A b c t x z
  unfold IsOptimal259
  simp only [hmsrt]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x' z' ha hb hc => by linarith [h2 x' z' ha hb hc]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun x' z' ha hb hc => by linarith [h2 x' z' ha hb hc]⟩
