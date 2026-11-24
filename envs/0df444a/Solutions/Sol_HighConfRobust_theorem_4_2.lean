-- Prove2me | solution 1 for HighConfRobust.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T10:49:55.909949+00:00
-- url     : https://prove2.me/submissions/767c5923-89b7-4de2-8af0-5c2198329edd

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_HighConfRobust_IsHighConfidence
import Definitions.Def_HighConfRobust_IsTVRobust
import Definitions.Def_HighConfRobust_extFamily
import Theorems.Thm_HighConfRobust_lemma_4_3
import Theorems.Thm_HighConfRobust_fact_3_3_ii
import Theorems.Thm_HighConfRobust_fact_3_3_iv
import Theorems.Thm_MarkovChainCLT_tvDist_comp_le

open MeasureTheory ProbabilityTheory HighConfRobust

private lemma tvDist_self' {X : Type*} [MeasurableSpace X] (μ : Measure X) :
    MarkovChainCLT.tvDist μ μ = 0 := by
  unfold MarkovChainCLT.tvDist
  have : {r : ℝ | ∃ A : Set X, MeasurableSet A ∧ r = |(μ A).toReal - (μ A).toReal|} = {0} := by
    ext r; simp only [sub_self, abs_zero, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨∅, MeasurableSet.empty, h⟩⟩
  rw [this, csSup_singleton]

private lemma tvDist_le_one' {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MarkovChainCLT.tvDist μ ν ≤ 1 := by
  unfold MarkovChainCLT.tvDist
  refine csSup_le ⟨0, ∅, MeasurableSet.empty, by simp⟩ ?_
  rintro r ⟨A, -, rfl⟩
  have h1 : (μ A).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono (by simp) prob_le_one
  have h2 : (ν A).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono (by simp) prob_le_one
  have h3 := ENNReal.toReal_nonneg (a := μ A)
  have h4 := ENNReal.toReal_nonneg (a := ν A)
  rw [abs_le]; constructor <;> linarith

theorem solution {X Y Ω : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]
    (loss : Y → Y → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hloss_nonneg : ∀ y y', 0 ≤ loss y y') (hloss_symm : ∀ y y', loss y y' = loss y' y)
    (hloss_tri : ∀ y₁ y₂ y₃, loss y₁ y₂ ≤ C * (loss y₁ y₃ + loss y₃ y₂))
    (hloss_meas : ∀ y, Measurable fun z => loss z y)
    (F : Set (ProbabilityMeasure X)) (θ : ProbabilityMeasure X → Y)
    (f : X → X) (hf : Measurable f) (g : Y → Y) (a L K Δ α β ε : ℝ) (n : ℕ)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (A : (Fin n → X) → Ω → Y)
    (hA : Measurable (Function.uncurry A))
    (ha : 0 < a) (hL : 0 < L) (haα : a ≤ α / L) (hαL : α / L < 1 / 2)
    (hLip : ∀ E ∈ extFamily f hf a F, ∀ E' ∈ extFamily f hf a F,
      loss (θ E) (θ E') ≤ L * MarkovChainCLT.tvDist (E : Measure X) (E' : Measure X))
    (hΔ : ∀ D ∈ F, loss (θ D) (g (θ (D.map hf.aemeasurable))) ≤ Δ)
    (hK : 0 ≤ K) (hg : ∀ y y', loss (g y) (g y') ≤ K * loss y y')
    (hHC : IsHighConfidence loss θ A ν α β (extFamily f hf a F))
    (hβ : 0 ≤ β) (hε : 0 < ε)
    (hεβ : β ≤ Real.exp (-(4 * n * ε * max 1 (Real.log (ε / a))))) :
    IsTVRobust loss θ (fun S ω => g (A (f ∘ S) ω)) ν ε (C ^ 2 * (2 * K * α + Δ))
      (Real.exp (-(n * ε))) F := by
  intro D hD D' hDD'
  -- the truncated contamination level
  set ε₀ : ℝ := min ε 1 with hε₀
  have hε₀pos : 0 < ε₀ := lt_min hε one_pos
  have hε₀1 : ε₀ ≤ 1 := min_le_right _ _
  have hε₀ε : ε₀ ≤ ε := min_le_left _ _
  have hTV₀ : MarkovChainCLT.tvDist (D : Measure X) (D' : Measure X) ≤ ε₀ :=
    le_min hDD' (tvDist_le_one' _ _)
  have hαpos : 0 < α := by
    have : 0 < α / L := lt_of_lt_of_le ha haα
    exact (div_pos_iff_of_pos_right hL).mp this
  have ha1 : a < 1 := by linarith
  have hLa : L * a ≤ α := by
    have := mul_le_mul_of_nonneg_left haα hL.le
    rwa [mul_div_cancel₀ _ hL.ne'] at this
  -- Lemma 4.3
  set κ : ℝ := 1 / max 1 (Real.log (ε₀ / a)) with hκ
  have h43 : (0 < κ ∧ κ ≤ 1) ∧
      ∃ R : Measure X, IsProbabilityMeasure R ∧ MarkovChainCLT.tvDist (D : Measure X) R ≤ a ∧
        renyiDivergence (1 + κ) (D' : Measure X) R ≤ ((2 * ε₀ / κ : ℝ) : EReal) :=
    lemma_4_3 (D : Measure X) (D' : Measure X) ε₀ a hε₀pos hε₀1 hTV₀ ha ha1
  obtain ⟨⟨hκ0, hκ1⟩, R, hRprob, hTVR, hRen⟩ := h43
  let Rp : ProbabilityMeasure X := ⟨R, hRprob⟩
  let E : ProbabilityMeasure X := Rp.map hf.aemeasurable
  let ED : ProbabilityMeasure X := D.map hf.aemeasurable
  have hE : E ∈ extFamily f hf a F := ⟨D, hD, Rp, hTVR, rfl⟩
  have hED : ED ∈ extFamily f hf a F := ⟨D, hD, D, by rw [tvDist_self']; exact ha.le, rfl⟩
  have hTVE : MarkovChainCLT.tvDist (ED : Measure X) (E : Measure X) ≤ a := by
    have h := MarkovChainCLT.tvDist_comp_le (Kernel.deterministic f hf) (D : Measure X) R
    simp only [ED, E, Rp, ProbabilityMeasure.toMeasure_map]
    rw [Measure.deterministic_comp_eq_map, Measure.deterministic_comp_eq_map] at h
    exact h.trans hTVR
  -- the bad event
  set B : Set ((Fin n → X) × Ω) := {p | α < loss (A (f ∘ p.1) p.2) (θ E)} with hB
  set B' : Set ((Fin n → X) × Ω) := {p | α < loss (A p.1 p.2) (θ E)} with hB'
  have hB'meas : MeasurableSet B' :=
    measurableSet_lt measurable_const ((hloss_meas _).comp hA)
  have hfS : Measurable (fun S : Fin n → X => f ∘ S) :=
    measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)
  have hPM : Measurable (Prod.map (fun S : Fin n → X => f ∘ S) (id : Ω → Ω)) :=
    hfS.prodMap measurable_id
  have hBpre : B = Prod.map (fun S : Fin n → X => f ∘ S) id ⁻¹' B' := rfl
  -- the failure set of A' is contained in the bad event
  have hΔnn : 0 ≤ Δ := (hloss_nonneg _ _).trans (hΔ D hD)
  have hsub : {p : (Fin n → X) × Ω | C ^ 2 * (2 * K * α + Δ) <
      loss ((fun S ω => g (A (f ∘ S) ω)) p.1 p.2) (θ D)} ⊆ B := by
    intro p hp
    by_contra hpB
    simp only [Set.mem_ofPred_eq, hB, not_lt] at hp hpB
    set y := A (f ∘ p.1) p.2
    have h1 : loss (θ ED) y ≤ C * (2 * α) := by
      calc loss (θ ED) y ≤ C * (loss (θ ED) (θ E) + loss (θ E) y) := hloss_tri _ _ _
        _ ≤ C * (L * a + α) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by linarith)
          · exact (hLip ED hED E hE).trans (mul_le_mul_of_nonneg_left hTVE hL.le)
          · rw [hloss_symm]; exact hpB
        _ ≤ C * (2 * α) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2 : loss (θ D) (g y) ≤ C * (Δ + K * (C * (2 * α))) := by
      calc loss (θ D) (g y) ≤ C * (loss (θ D) (g (θ ED)) + loss (g (θ ED)) (g y)) :=
            hloss_tri _ _ _
        _ ≤ C * (Δ + K * (C * (2 * α))) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by linarith)
          · exact hΔ D hD
          · exact (hg _ _).trans (mul_le_mul_of_nonneg_left h1 hK)
    rw [hloss_symm] at hp
    have hC2 : C ≤ C ^ 2 := by nlinarith
    have : C * (Δ + K * (C * (2 * α))) ≤ C ^ 2 * (2 * K * α + Δ) := by
      have : C * Δ ≤ C ^ 2 * Δ := mul_le_mul_of_nonneg_right hC2 hΔnn
      nlinarith
    linarith
  -- the probability of the bad event under the reference law
  have hQB : ((Measure.pi fun _ : Fin n => R).prod ν) B ≤ ENNReal.ofReal β := by
    have hmap : ((Measure.pi fun _ : Fin n => R).prod ν).map
        (Prod.map (fun S : Fin n → X => f ∘ S) id) =
        (Measure.pi fun _ : Fin n => (E : Measure X)).prod ν := by
      rw [← Measure.map_prod_map _ _ hfS measurable_id, Measure.map_id]
      congr 1
      have := Measure.pi_map_pi (μ := fun _ : Fin n => R) (f := fun _ => f)
        (fun _ => hf.aemeasurable)
      show _ = Measure.pi fun _ : Fin n => R.map f
      rw [← this]
      rfl
    rw [hBpre, ← Measure.map_apply hPM hB'meas, hmap]
    exact hHC E hE
  -- change of measure
  have hTens := fact_3_3_ii (D' : Measure X) R ν n (1 + κ) (by linarith)
  set Dval : ℝ := n * (2 * ε₀ / κ) with hDval
  have hRenP : renyiDivergence (1 + κ) ((Measure.pi fun _ : Fin n => (D' : Measure X)).prod ν)
      ((Measure.pi fun _ : Fin n => R).prod ν) ≤ (Dval : EReal) := by
    rw [hTens, hDval, EReal.coe_mul]
    exact mul_le_mul_of_nonneg_left hRen (by exact_mod_cast Nat.cast_nonneg n)
  have hcm := (fact_3_3_iv ((Measure.pi fun _ : Fin n => (D' : Measure X)).prod ν)
      ((Measure.pi fun _ : Fin n => R).prod ν) B
      (hPM hB'meas)).1 (1 + κ) Dval (by linarith) hRenP
  have hq : (1 + κ - 1) / (1 + κ) = κ / (1 + κ) := by ring
  rw [hq] at hcm
  -- numerical bound
  have hQBr : (((Measure.pi fun _ : Fin n => R).prod ν) B).toReal ≤ β := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hQB
    rwa [ENNReal.toReal_ofReal hβ] at this
  have hlogmono : max 1 (Real.log (ε₀ / a)) ≤ max 1 (Real.log (ε / a)) := by
    exact max_le_max le_rfl
      (Real.log_le_log (div_pos hε₀pos ha) (div_le_div_of_nonneg_right hε₀ε ha.le))
  have hmpos : 0 < max 1 (Real.log (ε₀ / a)) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hκinv : 1 / κ = max 1 (Real.log (ε₀ / a)) := by rw [hκ, one_div_one_div]
  have hβ' : β ≤ Real.exp (-(4 * n * ε / κ)) := by
    refine hεβ.trans (Real.exp_le_exp.mpr ?_)
    have : 4 * n * ε / κ = 4 * n * ε * max 1 (Real.log (ε₀ / a)) := by
      rw [← hκinv]; ring
    rw [this, neg_le_neg_iff]
    have : 0 ≤ 4 * (n : ℝ) * ε := by positivity
    exact mul_le_mul_of_nonneg_left hlogmono this
  set t : ℝ := κ / (1 + κ) with ht
  have htpos : 0 < t := by positivity
  have hfinal : (((Measure.pi fun _ : Fin n => R).prod ν) B).toReal ^ t *
      Real.exp (t * Dval) ≤ Real.exp (-(n * ε)) := by
    have hb1 : (((Measure.pi fun _ : Fin n => R).prod ν) B).toReal ^ t ≤
        Real.exp (-(4 * n * ε / κ)) ^ t :=
      Real.rpow_le_rpow ENNReal.toReal_nonneg (hQBr.trans hβ') htpos.le
    rw [← Real.exp_mul] at hb1
    calc (((Measure.pi fun _ : Fin n => R).prod ν) B).toReal ^ t * Real.exp (t * Dval)
        ≤ Real.exp (-(4 * n * ε / κ) * t) * Real.exp (t * Dval) := by gcongr
      _ = Real.exp (-(4 * n * ε / κ) * t + t * Dval) := by rw [Real.exp_add]
      _ ≤ Real.exp (-(n * ε)) := by
        apply Real.exp_le_exp.mpr
        have e1 : -(4 * n * ε / κ) * t + t * Dval = (2 * n * ε₀ - 4 * n * ε) / (1 + κ) := by
          rw [ht, hDval]; field_simp; ring
        rw [e1, div_le_iff₀ (by linarith)]
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have : (n : ℝ) * ε₀ ≤ n * ε := mul_le_mul_of_nonneg_left hε₀ε hn
        have : 0 ≤ (n : ℝ) * ε * κ := by positivity
        nlinarith
  -- conclude
  have hPB : ((Measure.pi fun _ : Fin n => (D' : Measure X)).prod ν) B ≤
      ENNReal.ofReal (Real.exp (-(n * ε))) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ B)]
    exact ENNReal.ofReal_le_ofReal (hcm.trans hfinal)
  exact (measure_mono hsub).trans hPB
