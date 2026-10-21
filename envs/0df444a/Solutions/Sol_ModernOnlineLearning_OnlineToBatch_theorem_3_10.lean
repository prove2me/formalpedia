-- Prove2me | solution 1 for ModernOnlineLearning.OnlineToBatch.theorem_3_10
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T05:24:40.079841+00:00
-- url     : https://prove2.me/submissions/6d767d76-2e39-41b4-88d1-3308140b5f13

import Mathlib
import Definitions.Def_ModernOnlineLearning_OnlineToBatch_Defs

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace O2BHelpers4161

lemma update_preimage_pi {D : Type*} (k : ℕ) (s : Finset ℕ) (t : ℕ → Set D) :
    (fun p : (ℕ → D) × D => Function.update p.1 k p.2) ⁻¹' (Set.pi (s : Set ℕ) t) =
      (Set.pi ((s.erase k : Finset ℕ) : Set ℕ) t) ×ˢ (if k ∈ s then t k else Set.univ) := by
  ext ⟨ω, z⟩
  simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase]
  constructor
  · intro h
    refine ⟨fun i ⟨hik, his⟩ => ?_, ?_⟩
    · have := h i his
      rwa [Function.update_of_ne hik] at this
    · split_ifs with hk
      · have := h k hk
        rwa [Function.update_self] at this
      · exact Set.mem_univ _
  · rintro ⟨h1, h2⟩ i his
    by_cases hik : i = k
    · subst hik
      rw [Function.update_self]
      simpa [his] using h2
    · rw [Function.update_of_ne hik]
      exact h1 i ⟨hik, his⟩

lemma measurePreserving_update {D : Type*} [MeasurableSpace D] (ρ : Measure D)
    [IsProbabilityMeasure ρ] (k : ℕ) :
    MeasurePreserving (fun p : (ℕ → D) × D => Function.update p.1 k p.2)
      ((Measure.infinitePi (fun _ : ℕ => ρ)).prod ρ) (Measure.infinitePi (fun _ : ℕ => ρ)) where
  measurable := measurable_update'
  map_eq := by
    refine Measure.eq_infinitePi _ (fun s t ht => ?_)
    rw [Measure.map_apply measurable_update'
      (MeasurableSet.pi s.countable_toSet (fun i _ => ht i)), update_preimage_pi,
      Measure.prod_prod, Measure.infinitePi_pi (fun _ : ℕ => ρ) (fun i _ => ht i)]
    split_ifs with hk
    · rw [Finset.prod_erase_mul _ _ hk]
    · rw [Finset.erase_eq_of_notMem hk, measure_univ, mul_one]

lemma integrable_of_abs_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : α → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x, |F x| ≤ B) : Integrable F μ :=
  (integrable_const B).mono' hF.aestronglyMeasurable
    (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact hB x))

lemma integral_exp_mul_le_of_update {D : Type*} [MeasurableSpace D] (ρ : Measure D)
    [IsProbabilityMeasure ρ] (k : ℕ) (g h : (ℕ → D) → ℝ) (B C : ℝ)
    (hg : Measurable g) (hh : Measurable h)
    (hgb : ∀ ω, |g ω| ≤ B) (hhb : ∀ ω, |h ω| ≤ B)
    (hginv : ∀ ω z, g (Function.update ω k z) = g ω)
    (hC : ∀ ω, ∫ z, Real.exp (h (Function.update ω k z)) ∂ρ ≤ C) :
    ∫ ω, Real.exp (g ω) * Real.exp (h ω) ∂(Measure.infinitePi (fun _ : ℕ => ρ)) ≤
      C * ∫ ω, Real.exp (g ω) ∂(Measure.infinitePi (fun _ : ℕ => ρ)) := by
  have hΦ := measurePreserving_update ρ k
  have hF : Measurable (fun ω => Real.exp (g ω) * Real.exp (h ω)) := by fun_prop
  have hbound : ∀ ω, |Real.exp (g ω) * Real.exp (h ω)| ≤ Real.exp B * Real.exp B := by
    intro ω
    rw [abs_of_pos (by positivity)]
    exact mul_le_mul (Real.exp_le_exp.2 (abs_le.1 (hgb ω)).2)
      (Real.exp_le_exp.2 (abs_le.1 (hhb ω)).2) (by positivity) (by positivity)
  have hint : Integrable (fun p : (ℕ → D) × D =>
      Real.exp (g (Function.update p.1 k p.2)) * Real.exp (h (Function.update p.1 k p.2)))
      ((Measure.infinitePi (fun _ : ℕ => ρ)).prod ρ) :=
    integrable_of_abs_le _ _ (hF.comp measurable_update') _ (fun p => hbound _)
  have hmap := integral_map (μ := (Measure.infinitePi (fun _ : ℕ => ρ)).prod ρ)
    hΦ.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hΦ.map_eq] at hmap
  have hgint : Integrable (fun ω => Real.exp (g ω) * C) (Measure.infinitePi (fun _ : ℕ => ρ)) :=
    (integrable_of_abs_le _ _ hg.exp (Real.exp B) (fun ω => by
      rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.2 (abs_le.1 (hgb ω)).2)).mul_const C
  calc ∫ ω, Real.exp (g ω) * Real.exp (h ω) ∂(Measure.infinitePi (fun _ : ℕ => ρ))
      = ∫ p, Real.exp (g (Function.update p.1 k p.2)) * Real.exp (h (Function.update p.1 k p.2))
          ∂((Measure.infinitePi (fun _ : ℕ => ρ)).prod ρ) := hmap
    _ = ∫ ω, ∫ z, Real.exp (g ω) * Real.exp (h (Function.update ω k z)) ∂ρ
          ∂(Measure.infinitePi (fun _ : ℕ => ρ)) := by
        rw [integral_prod _ hint]
        simp only [hginv]
    _ ≤ ∫ ω, Real.exp (g ω) * C ∂(Measure.infinitePi (fun _ : ℕ => ρ)) := by
        apply integral_mono
        · have := hint.integral_prod_left
          simpa only [hginv] using this
        · exact hgint
        · intro ω
          simp only
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (hC ω) (Real.exp_pos _).le
    _ = C * ∫ ω, Real.exp (g ω) ∂(Measure.infinitePi (fun _ : ℕ => ρ)) := by
        rw [integral_mul_const, mul_comm]

lemma mgf_sum_le {D : Type*} [MeasurableSpace D] (ρ : Measure D) [IsProbabilityMeasure ρ]
    (Z : ℕ → (ℕ → D) → ℝ) (N : ℕ)
    (hmeas : ∀ t, 1 ≤ t → t ≤ N → Measurable (Z t))
    (hbd : ∀ t, 1 ≤ t → t ≤ N → ∀ ω, |Z t ω| ≤ 2)
    (hdep : ∀ t, 1 ≤ t → t ≤ N → ∀ ω k z, t < k → Z t (Function.update ω k z) = Z t ω)
    (hstep : ∀ t, 1 ≤ t → t ≤ N → ∀ ω (l : ℝ),
      ∫ z, Real.exp (l * Z t (Function.update ω t z)) ∂ρ ≤ Real.exp (l ^ 2 / 2)) :
    ∀ n, n ≤ N → ∀ l : ℝ, ∫ ω, Real.exp (l * ∑ t ∈ Finset.Icc 1 n, Z t ω)
      ∂(Measure.infinitePi (fun _ : ℕ => ρ)) ≤ Real.exp (n * l ^ 2 / 2) := by
  intro n
  induction n with
  | zero => intro _ l; simp
  | succ n ih =>
    intro hn l
    have hS : ∀ ω, ∑ t ∈ Finset.Icc 1 (n + 1), Z t ω = ∑ t ∈ Finset.Icc 1 n, Z t ω + Z (n + 1) ω := by
      intro ω; rw [Finset.sum_Icc_succ_top (by omega)]
    simp_rw [hS, mul_add, Real.exp_add]
    have hmS : Measurable (fun ω => l * ∑ t ∈ Finset.Icc 1 n, Z t ω) := by
      refine Measurable.const_mul (Finset.measurable_sum _ (fun t ht => ?_)) l
      rw [Finset.mem_Icc] at ht; exact hmeas t ht.1 (by omega)
    have hbS : ∀ ω, |l * ∑ t ∈ Finset.Icc 1 n, Z t ω| ≤ |l| * (2 * n) + |l| * 2 := by
      intro ω
      rw [abs_mul]
      have h1 : |∑ t ∈ Finset.Icc 1 n, Z t ω| ≤ 2 * n := by
        calc |∑ t ∈ Finset.Icc 1 n, Z t ω| ≤ ∑ t ∈ Finset.Icc 1 n, |Z t ω| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ t ∈ Finset.Icc 1 n, (2 : ℝ) := by
              apply Finset.sum_le_sum
              intro t ht; rw [Finset.mem_Icc] at ht; exact hbd t ht.1 (by omega) ω
          _ = 2 * n := by simp [mul_comm]
      nlinarith [abs_nonneg l]
    have hbZ : ∀ ω, |l * Z (n + 1) ω| ≤ |l| * (2 * n) + |l| * 2 := by
      intro ω
      rw [abs_mul]
      have := hbd (n + 1) (by omega) hn ω
      have : (0 : ℝ) ≤ |l| * (2 * n) := by positivity
      nlinarith [abs_nonneg l]
    calc _ ≤ Real.exp (l ^ 2 / 2) * ∫ ω, Real.exp (l * ∑ t ∈ Finset.Icc 1 n, Z t ω)
            ∂(Measure.infinitePi (fun _ : ℕ => ρ)) := by
          refine integral_exp_mul_le_of_update ρ (n + 1) _ _ (|l| * (2 * n) + |l| * 2) _ hmS
            ((hmeas (n + 1) (by omega) hn).const_mul l) hbS hbZ ?_ ?_
          · intro ω z
            congr 1
            apply Finset.sum_congr rfl
            intro t ht
            rw [Finset.mem_Icc] at ht
            exact hdep t ht.1 (by omega) ω (n + 1) z (by omega)
          · intro ω
            exact hstep (n + 1) (by omega) hn ω l
      _ ≤ Real.exp (l ^ 2 / 2) * Real.exp (n * l ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (ih (by omega) l) (Real.exp_pos _).le
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * l ^ 2 / 2) := by
          rw [← Real.exp_add]; push_cast; ring_nf

end O2BHelpers4161

-- Orabona, arXiv:1912.13213v10, Theorem 3.10, p. 27.
open ModernOnlineLearning.OnlineToBatch in
theorem solution (d : ℕ) {D : Type*} [MeasurableSpace D]
    (ρ : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure ρ]
    (V : Set (Decision d)) (f : Decision d → D → ℝ) (A : ℕ → (ℕ → D) → Decision d)
    (R : Decision d → ℕ → ℝ) (T : ℕ) (δ : ℝ) (uStar : Decision d)
    (hT : 1 ≤ T) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hf_meas : ∀ x ∈ V, Measurable (f x))
    (hf_bounds : ∀ x ∈ V, ∀ z, 0 ≤ f x z ∧ f x z ≤ 1)
    (hA : IsOnlineAlgorithm V A)
    (hA_meas : ∀ t ∈ Finset.Icc 1 T, Measurable (A t))
    (hloss_meas : ∀ t ∈ Finset.Icc 1 T,
      Measurable (fun ω : ℕ → D => f (A t ω) (ω t)))
    (hrisk_meas : ∀ t ∈ Finset.Icc 1 T,
      Measurable (fun ω : ℕ → D => risk ρ f (A t ω)))
    (hregret : ∀ ω : ℕ → D, ∀ u ∈ V, regret f A ω u T ≤ R u T)
    (huStar : uStar ∈ V)
    (hmin : ∀ u ∈ V,
      risk ρ f uStar + R uStar T / (T : ℝ) ≤
        risk ρ f u + R u T / (T : ℝ)) :
    (MeasureTheory.Measure.infinitePi (fun _ : ℕ => ρ)).real
      {ω : ℕ → D |
        (∑ t ∈ Finset.Icc 1 T, risk ρ f (A t ω)) / (T : ℝ) ≤
          risk ρ f uStar + R uStar T / (T : ℝ) +
            2 * Real.sqrt (2 * Real.log (2 / δ) / (T : ℝ))} ≥ 1 - δ := by
  classical
  have hint : ∀ x ∈ V, Integrable (f x) ρ := fun x hx =>
    O2BHelpers4161.integrable_of_abs_le ρ (f x) (hf_meas x hx) 1 (fun z => by
      rw [abs_le]; constructor <;> linarith [hf_bounds x hx z])
  have hrisk01 : ∀ x ∈ V, 0 ≤ risk ρ f x ∧ risk ρ f x ≤ 1 := by
    intro x hx
    constructor
    · exact integral_nonneg (fun z => (hf_bounds x hx z).1)
    · calc risk ρ f x = ∫ z, f x z ∂ρ := rfl
        _ ≤ ∫ _z, (1 : ℝ) ∂ρ := integral_mono (hint x hx) (integrable_const 1)
            (fun z => (hf_bounds x hx z).2)
        _ = 1 := by simp
  have hAdep : ∀ t, 1 ≤ t → ∀ ω k z, t ≤ k → A t (Function.update ω k z) = A t ω := by
    intro t ht ω k z htk
    exact hA.2 t _ _ ht (fun s _ hs => Function.update_of_ne (by omega) z ω)
  let Z : ℕ → (ℕ → D) → ℝ := fun t ω =>
    (risk ρ f (A t ω) - f (A t ω) (ω t)) - (risk ρ f uStar - f uStar (ω t))
  have hmeasZ : ∀ t, 1 ≤ t → t ≤ T → Measurable (Z t) := by
    intro t h1 h2
    have ht : t ∈ Finset.Icc 1 T := Finset.mem_Icc.2 ⟨h1, h2⟩
    exact ((hrisk_meas t ht).sub (hloss_meas t ht)).sub
      (measurable_const.sub ((hf_meas uStar huStar).comp (measurable_pi_apply t)))
  have hbdZ : ∀ t, 1 ≤ t → t ≤ T → ∀ ω, |Z t ω| ≤ 2 := by
    intro t h1 _ ω
    have hx := hA.1 t ω h1
    have a1 := hrisk01 _ hx
    have a2 := hrisk01 _ huStar
    have a3 := hf_bounds _ hx (ω t)
    have a4 := hf_bounds _ huStar (ω t)
    simp only [Z]
    rw [abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]
  have hdepZ : ∀ t, 1 ≤ t → t ≤ T → ∀ ω k z, t < k → Z t (Function.update ω k z) = Z t ω := by
    intro t h1 _ ω k z htk
    simp only [Z]
    rw [hAdep t h1 ω k z htk.le, Function.update_of_ne (by omega : t ≠ k)]
  have hstepZ : ∀ t, 1 ≤ t → t ≤ T → ∀ ω (l : ℝ),
      ∫ z, Real.exp (l * Z t (Function.update ω t z)) ∂ρ ≤ Real.exp (l ^ 2 / 2) := by
    intro t h1 _ ω l
    set x := A t ω with hxdef
    have hx : x ∈ V := hA.1 t ω h1
    have hZ : ∀ z, Z t (Function.update ω t z) =
        (f uStar z - f x z) - ∫ z', (f uStar z' - f x z') ∂ρ := by
      intro z
      simp only [Z]
      rw [hAdep t h1 ω t z le_rfl, Function.update_self, integral_sub (hint _ huStar) (hint _ hx)]
      simp only [risk]
      ring
    have hX := hasSubgaussianMGF_of_mem_Icc (μ := ρ) (X := fun z => f uStar z - f x z)
      (a := -1) (b := 1) ((hf_meas _ huStar).sub (hf_meas _ hx)).aemeasurable
      (ae_of_all _ (fun z => by
        have a3 := hf_bounds _ hx z
        have a4 := hf_bounds _ huStar z
        constructor <;> linarith [a3.1, a3.2, a4.1, a4.2]))
    have hc : ((‖(1 : ℝ) - -1‖₊ / 2) ^ 2 : NNReal) = 1 := by
      have : ‖(1 : ℝ) - -1‖₊ = 2 := by
        rw [show (1 : ℝ) - -1 = 2 by norm_num]
        simp
      rw [this]; norm_num
    have := hX.mgf_le l
    rw [hc] at this
    simp only [mgf, NNReal.coe_one, one_mul] at this
    simp_rw [hZ]
    exact this
  have hmgf := O2BHelpers4161.mgf_sum_le ρ Z T hmeasZ hbdZ hdepZ hstepZ T le_rfl
  let S : (ℕ → D) → ℝ := fun ω => ∑ t ∈ Finset.Icc 1 T, Z t ω
  have hSmeas : Measurable S := Finset.measurable_sum _ (fun t ht => by
    rw [Finset.mem_Icc] at ht; exact hmeasZ t ht.1 ht.2)
  have hSbd : ∀ ω, |S ω| ≤ 2 * T := by
    intro ω
    calc |S ω| ≤ ∑ t ∈ Finset.Icc 1 T, |Z t ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Finset.Icc 1 T, (2 : ℝ) := by
          apply Finset.sum_le_sum
          intro t ht; rw [Finset.mem_Icc] at ht; exact hbdZ t ht.1 ht.2 ω
      _ = 2 * T := by simp [mul_comm]
  have hsub : HasSubgaussianMGF S (T : NNReal) (Measure.infinitePi (fun _ : ℕ => ρ)) := by
    refine ⟨fun l => ?_, fun l => ?_⟩
    · refine O2BHelpers4161.integrable_of_abs_le _ _ (hSmeas.const_mul l).exp
        (Real.exp (|l| * (2 * T))) (fun ω => ?_)
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.2
      calc l * S ω ≤ |l * S ω| := le_abs_self _
        _ = |l| * |S ω| := abs_mul _ _
        _ ≤ |l| * (2 * T) := mul_le_mul_of_nonneg_left (hSbd ω) (abs_nonneg l)
    · simp only [mgf, NNReal.coe_natCast]
      exact hmgf l
  have hδ2 : 1 < 2 / δ := by rw [lt_div_iff₀ hδ0]; linarith
  have hL : 0 < Real.log (2 / δ) := Real.log_pos hδ2
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  set L := Real.log (2 / δ) with hLdef
  set ε := (T : ℝ) * (2 * Real.sqrt (2 * L / T)) with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have htail := hsub.measure_ge_le hε0
  have hε2 : ε ^ 2 = 8 * T * L := by
    rw [hεdef, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have hexp : Real.exp (-ε ^ 2 / (2 * ((T : NNReal) : ℝ))) ≤ δ := by
    rw [NNReal.coe_natCast, hε2]
    have h4 : -(8 * (T : ℝ) * L) / (2 * T) = -(4 * L) := by field_simp; ring
    rw [h4]
    calc Real.exp (-(4 * L)) ≤ Real.exp (-L) := Real.exp_le_exp.2 (by linarith)
      _ = δ / 2 := by
          rw [Real.exp_neg, hLdef, Real.exp_log (by positivity)]
          field_simp
      _ ≤ δ := by linarith
  have hsubset : {ω | ε ≤ S ω}ᶜ ⊆ {ω : ℕ → D |
        (∑ t ∈ Finset.Icc 1 T, risk ρ f (A t ω)) / (T : ℝ) ≤
          risk ρ f uStar + R uStar T / (T : ℝ) +
            2 * Real.sqrt (2 * Real.log (2 / δ) / (T : ℝ))} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω ⊢
    have hreg := hregret ω uStar huStar
    simp only [regret] at hreg
    have hSexp : S ω = (∑ t ∈ Finset.Icc 1 T, risk ρ f (A t ω)) -
        (∑ t ∈ Finset.Icc 1 T, f (A t ω) (ω t)) -
        (T * risk ρ f uStar - ∑ t ∈ Finset.Icc 1 T, f uStar (ω t)) := by
      simp only [S, Z, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      push_cast
      ring
    rw [div_le_iff₀ hTpos, add_mul, add_mul, div_mul_cancel₀ _ hTpos.ne']
    have hεT : 2 * Real.sqrt (2 * L / T) * T = ε := by rw [hεdef]; ring
    rw [← hLdef, hεT]
    linarith
  have hmeasSet : MeasurableSet {ω | ε ≤ S ω} := measurableSet_le measurable_const hSmeas
  calc (Measure.infinitePi (fun _ : ℕ => ρ)).real {ω : ℕ → D |
        (∑ t ∈ Finset.Icc 1 T, risk ρ f (A t ω)) / (T : ℝ) ≤
          risk ρ f uStar + R uStar T / (T : ℝ) +
            2 * Real.sqrt (2 * Real.log (2 / δ) / (T : ℝ))}
      ≥ (Measure.infinitePi (fun _ : ℕ => ρ)).real {ω | ε ≤ S ω}ᶜ := measureReal_mono hsubset
    _ = 1 - (Measure.infinitePi (fun _ : ℕ => ρ)).real {ω | ε ≤ S ω} :=
        probReal_compl_eq_one_sub hmeasSet
    _ ≥ 1 - δ := by linarith
