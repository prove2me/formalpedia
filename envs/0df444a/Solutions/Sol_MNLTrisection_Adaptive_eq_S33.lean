-- Prove2me | solution 1 for MNLTrisection.Adaptive.eq_S33
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:18:32.033908+00:00
-- url     : https://prove2.me/submissions/a880a5eb-bfc7-40bf-90fd-1d3ccf69208e

import Mathlib
import Definitions.Def_UnderstandingML_Framework
import Definitions.Def_MNLTrisection_Adaptive_Model
import Theorems.Thm_MNLTrisection_Adaptive_lemma_8

namespace MNLTriS33

open MNLTrisection.Adaptive MeasureTheory UnderstandingML

theorem eps_succ (k : ℕ) : eps (k + 1) = 2 / 3 * eps k := by
  unfold eps; rw [pow_succ]; ring

theorem eps_pos (k : ℕ) : 0 < eps k := by unfold eps; positivity

theorem eps_zero : eps 0 = 1 / 3 := by simp [eps]

theorem eps_le (k : ℕ) : eps k ≤ 1 / 3 := by
  unfold eps
  have : (2 / 3 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

theorem nEpoch_ge (T τ : ℕ) :
    8 * Real.log (8 * T * eps τ ^ 2) ≤ (nEpoch T τ : ℝ) * eps τ ^ 2 := by
  have he := eps_pos τ
  set L := Real.log (8 * T * eps τ ^ 2)
  have h1 : ((eps τ)⁻¹ ^ 2 * L) ≤ (⌈(eps τ)⁻¹ ^ 2 * L⌉₊ : ℝ) := Nat.le_ceil _
  have h2n : 8 * ⌈(eps τ)⁻¹ ^ 2 * L⌉₊ ≤ nEpoch T τ := by
    unfold nEpoch innerLen; exact le_max_right _ _
  have h2 : (8 * ⌈(eps τ)⁻¹ ^ 2 * L⌉₊ : ℝ) ≤ (nEpoch T τ : ℝ) := by exact_mod_cast h2n
  have h3 : (eps τ)⁻¹ ^ 2 * eps τ ^ 2 = 1 := by field_simp
  have he2 : 0 < eps τ ^ 2 := by positivity
  calc 8 * L = 8 * ((eps τ)⁻¹ ^ 2 * L) * eps τ ^ 2 := by
        rw [show 8 * ((eps τ)⁻¹ ^ 2 * L) * eps τ ^ 2 = 8 * L * ((eps τ)⁻¹ ^ 2 * eps τ ^ 2) by ring,
          h3, mul_one]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ he2.le
        linarith

/-- `n_τ ε_τ² ≤ 8 ln(8Tε_τ²) + 8 ε_τ²` when the logarithm is nonnegative. -/
theorem nEpoch_le (T τ : ℕ) (hlog : 0 ≤ Real.log (8 * T * eps τ ^ 2)) :
    (nEpoch T τ : ℝ) * eps τ ^ 2 ≤ 8 * Real.log (8 * T * eps τ ^ 2) + 8 * eps τ ^ 2 := by
  have he := eps_pos τ
  set L := Real.log (8 * T * eps τ ^ 2)
  set z := (eps τ)⁻¹ ^ 2 * L
  have hz : 0 ≤ z := by positivity
  have hc : (⌈z⌉₊ : ℝ) < z + 1 := Nat.ceil_lt_add_one hz
  have hn : (nEpoch T τ : ℝ) ≤ 8 * z + 8 := by
    unfold nEpoch innerLen
    rw [Nat.cast_max]
    apply max_le
    · push_cast; linarith
    · push_cast; linarith
  have h3 : (eps τ)⁻¹ ^ 2 * eps τ ^ 2 = 1 := by field_simp
  have he2 : 0 < eps τ ^ 2 := by positivity
  calc (nEpoch T τ : ℝ) * eps τ ^ 2 ≤ (8 * z + 8) * eps τ ^ 2 :=
        mul_le_mul_of_nonneg_right hn he2.le
    _ = 8 * L * ((eps τ)⁻¹ ^ 2 * eps τ ^ 2) + 8 * eps τ ^ 2 := by ring
    _ = _ := by rw [h3, mul_one]

/-- If epoch `τ` can start and `T ≥ 25` then `8 T ε_τ² ≥ 22`. -/
theorem x_ge (T τ : ℕ) (hT : 25 ≤ T) (hτ : ∑ τ' ∈ Finset.range τ, nEpoch T τ' < T) :
    22 ≤ 8 * (T : ℝ) * eps τ ^ 2 := by
  by_contra hcon
  push Not at hcon
  have hTpos : (25 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hex : ∃ k, 8 * (T : ℝ) * eps k ^ 2 < 99 / 2 := ⟨τ, by linarith⟩
  classical
  let k := Nat.find hex
  have hk : 8 * (T : ℝ) * eps k ^ 2 < 99 / 2 := Nat.find_spec hex
  have hkτ : k ≤ τ := Nat.find_min' hex (by linarith)
  have hxk : 22 ≤ 8 * (T : ℝ) * eps k ^ 2 := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, eps_zero]; linarith
    · obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hjnot : ¬ (8 * (T : ℝ) * eps j ^ 2 < 99 / 2) := Nat.find_min hex (by omega)
      push Not at hjnot
      rw [hj, eps_succ]; nlinarith
  have hkne : k ≠ τ := by
    intro he; rw [he] at hxk; linarith
  have hklt : k < τ := lt_of_le_of_ne hkτ hkne
  set x := 8 * (T : ℝ) * eps k ^ 2 with hx
  have hxpos : 0 < x := by linarith
  have hlog : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hxpos]
    have := Real.exp_one_lt_d9
    linarith
  have hn := nEpoch_ge T k
  rw [← hx] at hn
  have he2 : eps k ^ 2 = x / (8 * T) := by rw [hx]; field_simp
  have hnx : (nEpoch T k : ℝ) * x = 8 * T * ((nEpoch T k : ℝ) * eps k ^ 2) := by
    rw [he2]; field_simp
  have hA : 64 * T ≤ (nEpoch T k : ℝ) * x := by
    have := mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ 8 * T)
    nlinarith
  have hnk : (T : ℝ) < nEpoch T k := by
    by_contra hle
    push Not at hle
    have : (nEpoch T k : ℝ) * x ≤ T * (99 / 2) := by
      have h0 : (0 : ℝ) ≤ nEpoch T k := by positivity
      calc (nEpoch T k : ℝ) * x ≤ (nEpoch T k : ℝ) * (99 / 2) :=
            mul_le_mul_of_nonneg_left hk.le h0
        _ ≤ T * (99 / 2) := by linarith
    linarith
  have hsum : (nEpoch T k : ℝ) ≤ ∑ τ' ∈ Finset.range τ, (nEpoch T τ' : ℝ) :=
    Finset.single_le_sum (f := fun τ' => (nEpoch T τ' : ℝ)) (fun _ _ => by positivity)
      (Finset.mem_range.mpr hklt)
  have hτR : (∑ τ' ∈ Finset.range τ, (nEpoch T τ' : ℝ)) < T := by exact_mod_cast hτ
  linarith

end MNLTriS33

open MeasureTheory UnderstandingML MNLTrisection.Adaptive in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (D : Measure Ω) [IsProbabilityMeasure D]
      (X : Ω → ℝ), Measurable X → (∀ᵐ ω ∂D, X ω ∈ Set.Icc (0 : ℝ) 1) →
      ∀ (y : ℝ), y ≤ ∫ x, X x ∂D →
      ∀ T τ : ℕ, 25 ≤ T → ∑ τ' ∈ Finset.range τ, nEpoch T τ' < T →
      iidLaw D (nEpoch T τ) {ω | ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ nEpoch T τ ∧
          (∑ i ∈ Finset.univ.filter (fun i : Fin (nEpoch T τ) => (i : ℕ) < ℓ), X (ω i)) / ℓ +
            radius T ℓ < y} ≤
        ENNReal.ofReal (C * (nEpoch T τ : ℝ) / T) ∧
      iidLaw D (nEpoch T τ) {ω | ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ nEpoch T τ ∧
          (∑ i ∈ Finset.univ.filter (fun i : Fin (nEpoch T τ) => (i : ℕ) < ℓ), X (ω i)) / ℓ +
            radius T ℓ < y} ≤
        ENNReal.ofReal (C * Real.log (T * eps τ ^ 2) / (T * eps τ ^ 2)) := by
  refine ⟨65, by norm_num, ?_⟩
  intro Ω _ D _ X hX hX01 y hy T τ hT hτ
  set n := nEpoch T τ with hn
  set μ := ∫ x, X x ∂D with hμ
  set P := iidLaw D n with hP
  haveI : IsProbabilityMeasure P := by rw [hP]; unfold iidLaw; infer_instance
  have hTR : (25 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  set E := {ω : Fin n → Ω | ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ n ∧
          (∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < ℓ), X (ω i)) / ℓ +
            radius T ℓ < y} with hE
  set G := {ω : Fin n → Ω | ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ n →
        |(∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < ℓ), X (ω i)) / ℓ - μ| ≤
          Real.sqrt (2 * (1 - 0) ^ 2 * Real.log (8 / ((1 / (T : ℝ)) * ℓ)) / ℓ)} with hG
  have h8 := lemma_8 D X hX (a := 0) (b := 1) (hX01.mono (fun x hx => hx)) n
    (δ := 1 / (T : ℝ)) (by positivity) (by rw [div_le_one hT0]; linarith)
  rw [← hP] at h8
  -- `G` is measurable
  have hGm : MeasurableSet G := by
    have : G = ⋂ ℓ : ℕ, ⋂ (_ : 1 ≤ ℓ), ⋂ (_ : ℓ ≤ n), {ω : Fin n → Ω |
        |(∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < ℓ), X (ω i)) / ℓ - μ| ≤
          Real.sqrt (2 * (1 - 0) ^ 2 * Real.log (8 / ((1 / (T : ℝ)) * ℓ)) / ℓ)} := by
      ext ω; simp [hG]
    rw [this]
    refine MeasurableSet.iInter (fun ℓ => MeasurableSet.iInter (fun _ =>
      MeasurableSet.iInter (fun _ => measurableSet_le ?_ measurable_const)))
    apply Measurable.abs
    apply Measurable.sub_const
    apply Measurable.div_const
    exact Finset.measurable_sum _ (fun i _ => hX.comp (measurable_pi_apply i))
  -- `E ⊆ Gᶜ`
  have hEG : E ⊆ Gᶜ := by
    intro ω hω hGω
    obtain ⟨ℓ, hℓ1, hℓn, hlt⟩ := hω
    have h := hGω ℓ hℓ1 hℓn
    have hrad : Real.sqrt (2 * (1 - 0) ^ 2 * Real.log (8 / ((1 / (T : ℝ)) * ℓ)) / ℓ) =
        radius T ℓ := by
      unfold radius
      congr 1
      rw [show (8 : ℝ) / ((1 / (T : ℝ)) * ℓ) = 8 * T / ℓ by field_simp]
      ring
    rw [hrad] at h
    have := (abs_le.mp h).1
    linarith
  -- `P(E) ≤ n/T`
  have hPE : P E ≤ ENNReal.ofReal ((n : ℝ) / T) := by
    calc P E ≤ P Gᶜ := measure_mono hEG
      _ = 1 - P G := prob_compl_eq_one_sub hGm
      _ ≤ ENNReal.ofReal ((n : ℝ) / T) := by
          apply tsub_le_iff_right.mpr
          have hq : (n : ℝ) * (1 / (T : ℝ)) = (n : ℝ) / T := by ring
          rw [hq] at h8
          calc (1 : ENNReal) ≤ ENNReal.ofReal ((n : ℝ) / T) + ENNReal.ofReal (1 - (n : ℝ) / T) := by
                rcases le_or_gt ((n : ℝ) / T) 1 with hle | hgt
                · rw [← ENNReal.ofReal_add (by positivity) (by linarith)]
                  simp
                · calc (1 : ENNReal) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
                    _ ≤ ENNReal.ofReal ((n : ℝ) / T) := ENNReal.ofReal_le_ofReal hgt.le
                    _ ≤ _ := le_self_add
            _ ≤ ENNReal.ofReal ((n : ℝ) / T) + P G := add_le_add le_rfl h8
  -- arithmetic for the second bound
  have hx := MNLTriS33.x_ge T τ hT hτ
  have hepos := MNLTriS33.eps_pos τ
  set u := (T : ℝ) * eps τ ^ 2 with hu
  have hupos : 0 < u := by positivity
  have hu8 : 8 * (T : ℝ) * eps τ ^ 2 = 8 * u := by rw [hu]; ring
  have hlogu : 1 ≤ Real.log u := by
    rw [Real.le_log_iff_exp_le hupos]
    have := Real.exp_one_lt_d9
    linarith
  have hlog8u : Real.log (8 * u) ≤ 7 + Real.log u := by
    rw [Real.log_mul (by norm_num) hupos.ne']
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    linarith
  have hl8 : 0 ≤ Real.log (8 * u) := Real.log_nonneg (by linarith)
  have hnle := MNLTriS33.nEpoch_le T τ (by rw [hu8]; exact hl8)
  rw [hu8, ← hn] at hnle
  have he2 : eps τ ^ 2 ≤ 1 / 9 := by
    have := MNLTriS33.eps_le τ
    nlinarith
  have hnT : (n : ℝ) / T ≤ 65 * Real.log u / u := by
    rw [div_le_div_iff₀ hT0 hupos]
    -- n * u = T * (n ε²) ≤ T (8 ln(8u) + 8 ε²)
    have h1 : (n : ℝ) * u = T * ((n : ℝ) * eps τ ^ 2) := by rw [hu]; ring
    rw [h1]
    have h2 : (T : ℝ) * ((n : ℝ) * eps τ ^ 2) ≤ T * (8 * Real.log (8 * u) + 8 * eps τ ^ 2) :=
      mul_le_mul_of_nonneg_left hnle hT0.le
    have h3 : 8 * eps τ ^ 2 ≤ 1 := by linarith
    nlinarith
  refine ⟨?_, ?_⟩
  · refine hPE.trans (ENNReal.ofReal_le_ofReal ?_)
    have : (0 : ℝ) ≤ (n : ℝ) / T := by positivity
    rw [mul_div_assoc]
    linarith
  · refine hPE.trans (ENNReal.ofReal_le_ofReal ?_)
    exact hnT
