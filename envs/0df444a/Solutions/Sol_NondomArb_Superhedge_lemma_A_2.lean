-- Prove2me | solution 1 for NondomArb.Superhedge.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T06:33:48.769265+00:00
-- url     : https://prove2.me/submissions/16ce4dcc-e533-44a1-b1b3-008def088abf

import Mathlib
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_General
open MeasureTheory Filter Topology NondomArb.Superhedge.General
open NondomArb.Superhedge

namespace LemmaA2Aux

lemma tendsto_ind {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (D : ℕ → Set Ω)
    (hD : ∀ n, MeasurableSet (D n)) (hmono : Monotone D)
    (hae : ∀ᵐ ω ∂Q, ∃ n, ω ∈ D n) (F : Ω → ENNReal) (hF : AEMeasurable F Q) :
    Tendsto (fun n => ∫⁻ ω, (D n).indicator F ω ∂Q) atTop (𝓝 (∫⁻ ω, F ω ∂Q)) := by
  refine lintegral_tendsto_of_tendsto_of_monotone (fun n => hF.indicator (hD n))
    (Eventually.of_forall fun ω i j hij =>
      Set.indicator_le_indicator_of_subset (hmono hij) (fun _ => bot_le) ω) ?_
  filter_upwards [hae] with ω hω
  obtain ⟨n, hn⟩ := hω
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop n] with k hk
  rw [Set.indicator_of_mem (hmono hk hn)]

lemma lint_eq {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) {u v : Ω → ℝ}
    (hu : Integrable u Q) (hv : Integrable v Q) (h : ∫ ω, u ω ∂Q = ∫ ω, v ω ∂Q) :
    (∫⁻ ω, ENNReal.ofReal (u ω) ∂Q) + ∫⁻ ω, ENNReal.ofReal (-v ω) ∂Q =
      (∫⁻ ω, ENNReal.ofReal (v ω) ∂Q) + ∫⁻ ω, ENNReal.ofReal (-u ω) ∂Q := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hu,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hv] at h
  have h1 := hu.lintegral_lt_top
  have h2 := hu.neg.lintegral_lt_top
  have h3 := hv.lintegral_lt_top
  have h4 := hv.neg.lintegral_lt_top
  simp only [Pi.neg_apply] at h2 h4
  rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.add_lt_top.mpr ⟨h1, h4⟩).ne
    (ENNReal.add_lt_top.mpr ⟨h3, h2⟩).ne, ENNReal.toReal_add h1.ne h4.ne,
    ENNReal.toReal_add h3.ne h2.ne]
  linarith

lemma ofReal_ind {Ω : Type*} (D : Set Ω) (g : Ω → ℝ) (ω : Ω) :
    ENNReal.ofReal (D.indicator g ω) = D.indicator (fun ω => ENNReal.ofReal (g ω)) ω := by
  by_cases h : ω ∈ D <;> simp [h]

lemma ofReal_neg_ind {Ω : Type*} (D : Set Ω) (g : Ω → ℝ) (ω : Ω) :
    ENNReal.ofReal (-D.indicator g ω) = D.indicator (fun ω => ENNReal.ofReal (-g ω)) ω := by
  by_cases h : ω ∈ D <;> simp [h]

end LemmaA2Aux

namespace LemmaA2Aux

variable {Ω : Type*} {m' m : MeasurableSpace Ω}

lemma integral_mul_eq_zero (hm : m' ≤ m) (Q : Measure Ω)
    [IsProbabilityMeasure Q]
    {ξ Y : Ω → ℝ} (hξ : Measurable[m'] ξ) {c : ℝ} (hc : ∀ ω, |ξ ω| ≤ c)
    (hY : Integrable Y Q) (hY0 : Q[Y | m'] =ᵐ[Q] 0) :
    Integrable (fun ω => ξ ω * Y ω) Q ∧ ∫ ω, ξ ω * Y ω ∂Q = 0 := by
  have hint : Integrable (fun ω => ξ ω * Y ω) Q :=
    hY.bdd_mul (hξ.mono hm le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hc ω)
  refine ⟨hint, ?_⟩
  have h1 := integral_condExp hm (μ := Q) (f := ξ * Y)
  have h2 : Q[ξ * Y | m'] =ᵐ[Q] ξ * Q[Y | m'] :=
    condExp_mul_of_stronglyMeasurable_left hξ.stronglyMeasurable hint hY
  have h3 : ∫ ω, ξ ω * Y ω ∂Q = ∫ ω, (ξ * Y) ω ∂Q := rfl
  rw [h3, ← h1, integral_congr_ae h2]
  rw [integral_congr_ae (g := fun _ => (0:ℝ)) (hY0.mono fun ω hω => by simp [Pi.mul_apply, hω])]
  simp


lemma key (hm : m' ≤ m) (Q : Measure Ω) [IsProbabilityMeasure Q] {d : ℕ}
    (V : Ω → ℝ) (hV : Measurable[m'] V) (Z : Ω → Fin d → ℝ) (hZ : Measurable[m'] Z)
    (Y : Ω → Fin d → ℝ) (B : Set Ω)
    (hYi : ∀ i, Integrable (B.indicator (fun ω => Y ω i)) Q)
    (hY0 : ∀ i, Q[B.indicator (fun ω => Y ω i) | m'] =ᵐ[Q] 0)
    (A : Set Ω) (hA : MeasurableSet[m'] A) (hAB : A ⊆ B) (c : ℝ) (hc0 : 0 ≤ c)
    (hcV : ∀ ω ∈ A, |V ω| ≤ c) (hcZ : ∀ ω ∈ A, ∀ i, |Z ω i| ≤ c) :
    Integrable (A.indicator V) Q ∧ Integrable (A.indicator (fun ω => Z ω ⬝ᵥ Y ω)) Q ∧
      ∫ ω, A.indicator (fun ω => Z ω ⬝ᵥ Y ω) ω ∂Q = 0 := by
  have hZi : ∀ i, Measurable[m'] (fun ω => Z ω i) := fun i => (measurable_pi_apply i).comp hZ
  have hξ : ∀ i, Measurable[m'] (A.indicator (fun ω => Z ω i)) :=
    fun i => (hZi i).indicator hA
  have hξb : ∀ i ω, |A.indicator (fun ω => Z ω i) ω| ≤ c := by
    intro i ω
    by_cases h : ω ∈ A
    · simp [Set.indicator_of_mem h, hcZ ω h i]
    · simp [Set.indicator_of_notMem h, hc0]
  have hterm := fun i => integral_mul_eq_zero hm Q (hξ i) (hξb i) (hYi i) (hY0 i)
  have hEq : A.indicator (fun ω => Z ω ⬝ᵥ Y ω) =
      fun ω => ∑ i, A.indicator (fun ω => Z ω i) ω * B.indicator (fun ω => Y ω i) ω := by
    funext ω
    by_cases h : ω ∈ A
    · simp [Set.indicator_of_mem h, Set.indicator_of_mem (hAB h), dotProduct]
    · simp [Set.indicator_of_notMem h]
  refine ⟨?_, ?_, ?_⟩
  · refine Integrable.of_bound (((hV.indicator hA).mono hm le_rfl).aestronglyMeasurable) c
      (Eventually.of_forall fun ω => ?_)
    by_cases h : ω ∈ A
    · simp [Set.indicator_of_mem h, Real.norm_eq_abs, hcV ω h]
    · simp [Set.indicator_of_notMem h, hc0]
  · rw [hEq]
    exact integrable_finsetSum _ fun i _ => (hterm i).1
  · rw [hEq, integral_finsetSum _ fun i _ => (hterm i).1]
    simp [fun i => (hterm i).2]

lemma step (hm : m' ≤ m) (Q : Measure Ω) [IsProbabilityMeasure Q] {d : ℕ}
    (V : Ω → ℝ) (hV : Measurable[m'] V) (Z : Ω → Fin d → ℝ) (hZ : Measurable[m'] Z)
    (Y : Ω → Fin d → ℝ) (hYm : Measurable Y) (B : ℕ → Set Ω)
    (hB : ∀ n, MeasurableSet[m'] (B n))
    (hBmono : Monotone B) (hBae : ∀ᵐ ω ∂Q, ∃ n, ω ∈ B n)
    (hYi : ∀ n i, Integrable ((B n).indicator (fun ω => Y ω i)) Q)
    (hY0 : ∀ n i, Q[(B n).indicator (fun ω => Y ω i) | m'] =ᵐ[Q] 0) :
    (∫⁻ ω, ENNReal.ofReal (V ω + Z ω ⬝ᵥ Y ω) ∂Q) + ∫⁻ ω, ENNReal.ofReal (-V ω) ∂Q =
      (∫⁻ ω, ENNReal.ofReal (V ω) ∂Q) + ∫⁻ ω, ENNReal.ofReal (-(V ω + Z ω ⬝ᵥ Y ω)) ∂Q ∧
    (∫⁻ ω, ENNReal.ofReal (-V ω) ∂Q) ≤ ∫⁻ ω, ENNReal.ofReal (-(V ω + Z ω ⬝ᵥ Y ω)) ∂Q := by
  set W : Ω → ℝ := fun ω => Z ω ⬝ᵥ Y ω with hWdef
  have hZi : ∀ i, Measurable[m'] (fun ω => Z ω i) := fun i => (measurable_pi_apply i).comp hZ
  have hVm : Measurable V := hV.mono hm le_rfl
  have hWm : Measurable W := by
    show Measurable fun ω => ∑ i, Z ω i * Y ω i
    exact Finset.measurable_sum _ fun i _ =>
      ((hZi i).mono hm le_rfl).mul ((measurable_pi_apply i).comp hYm)
  let D : ℕ → Set Ω := fun n => B n ∩ (V ⁻¹' Set.Icc (-(n:ℝ)) n ∩
    ⋂ i, (fun ω => Z ω i) ⁻¹' Set.Icc (-(n:ℝ)) n)
  have hDm' : ∀ n, MeasurableSet[m'] (D n) := fun n =>
    (hB n).inter ((hV measurableSet_Icc).inter
      (MeasurableSet.iInter fun i => hZi i measurableSet_Icc))
  have hDm : ∀ n, MeasurableSet (D n) := fun n => hm _ (hDm' n)
  have hDmono : Monotone D := by
    intro a b hab ω hω
    simp only [D, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc, Set.mem_iInter] at hω ⊢
    have hab' : (a:ℝ) ≤ b := by exact_mod_cast hab
    exact ⟨hBmono hab hω.1, ⟨by linarith [hω.2.1.1], by linarith [hω.2.1.2]⟩,
      fun i => ⟨by linarith [(hω.2.2 i).1], by linarith [(hω.2.2 i).2]⟩⟩
  have hDB : ∀ n, D n ⊆ B n := fun n ω hω => hω.1
  have hDV : ∀ n, ∀ ω ∈ D n, |V ω| ≤ n := fun n ω hω => abs_le.mpr hω.2.1
  have hDZ : ∀ n, ∀ ω ∈ D n, ∀ i, |Z ω i| ≤ n := fun n ω hω i => by
    have := hω.2.2
    simp only [Set.mem_iInter, Set.mem_preimage] at this
    exact abs_le.mpr (this i)
  have hDae : ∀ᵐ ω ∂Q, ∃ n, ω ∈ D n := by
    filter_upwards [hBae] with ω hω
    obtain ⟨n0, hn0⟩ := hω
    obtain ⟨N, hN⟩ := exists_nat_ge (|V ω| + ∑ i, |Z ω i|)
    refine ⟨max n0 N, ?_⟩
    have hNle : (N:ℝ) ≤ ((max n0 N : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    have hsum : ∀ i, |Z ω i| ≤ ∑ j, |Z ω j| := fun i =>
      Finset.single_le_sum (f := fun j => |Z ω j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have hs0 : 0 ≤ ∑ j, |Z ω j| := Finset.sum_nonneg (fun j _ => abs_nonneg (Z ω j))
    simp only [D, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc, Set.mem_iInter]
    refine ⟨hBmono (le_max_left _ _) hn0, abs_le.mp (by linarith), fun i => abs_le.mp ?_⟩
    linarith [hsum i, abs_nonneg (V ω)]
  -- part 1 on each D n
  have hkey := fun n => key hm Q V hV Z hZ Y (B n) (hYi n) (hY0 n) (D n) (hDm' n) (hDB n) n
    (Nat.cast_nonneg n) (hDV n) (hDZ n)
  have heq : ∀ n, (∫⁻ ω, (D n).indicator (fun ω => ENNReal.ofReal (V ω + W ω)) ω ∂Q) +
      ∫⁻ ω, (D n).indicator (fun ω => ENNReal.ofReal (-V ω)) ω ∂Q =
      (∫⁻ ω, (D n).indicator (fun ω => ENNReal.ofReal (V ω)) ω ∂Q) +
      ∫⁻ ω, (D n).indicator (fun ω => ENNReal.ofReal (-(V ω + W ω))) ω ∂Q := by
    intro n
    obtain ⟨h1, h2, h3⟩ := hkey n
    have hu : (D n).indicator (fun ω => V ω + W ω) = (D n).indicator V + (D n).indicator W := by
      funext ω; by_cases h : ω ∈ (D n) <;> simp [h]
    have hui : Integrable ((D n).indicator (fun ω => V ω + W ω)) Q := by rw [hu]; exact h1.add h2
    have hint : ∫ ω, (D n).indicator (fun ω => V ω + W ω) ω ∂Q = ∫ ω, (D n).indicator V ω ∂Q := by
      rw [hu]; simp only [Pi.add_apply]; rw [integral_add h1 h2]
      rw [show (∫ ω, (D n).indicator W ω ∂Q) = 0 from h3, add_zero]
    have := lint_eq Q hui h1 hint
    simp only [ofReal_ind, ofReal_neg_ind] at this
    exact this
  have hmeas : ∀ g : Ω → ℝ, Measurable g → AEMeasurable (fun ω => ENNReal.ofReal (g ω)) Q :=
    fun g hg => (ENNReal.measurable_ofReal.comp hg).aemeasurable
  have t1 := tendsto_ind Q D hDm hDmono hDae _ (hmeas _ (hVm.add hWm))
  have t2 := tendsto_ind Q D hDm hDmono hDae _ (hmeas _ hVm.neg)
  have t3 := tendsto_ind Q D hDm hDmono hDae _ (hmeas _ hVm)
  have t4 := tendsto_ind Q D hDm hDmono hDae _ (hmeas _ (hVm.add hWm).neg)
  refine ⟨tendsto_nhds_unique (t1.add t2) ((t3.add t4).congr fun n => (heq n).symm), ?_⟩
  -- part 2
  refine le_of_tendsto' t2 fun n => ?_
  let A := D n ∩ V ⁻¹' Set.Iio 0
  have hAm' : MeasurableSet[m'] A := (hDm' n).inter (hV measurableSet_Iio)
  obtain ⟨h1, h2, h3⟩ := key hm Q V hV Z hZ Y (B n) (hYi n) (hY0 n) A hAm'
    (fun ω hω => hDB n hω.1) n (Nat.cast_nonneg n) (fun ω hω => hDV n ω hω.1)
    (fun ω hω => hDZ n ω hω.1)
  have hu : A.indicator (fun ω => V ω + W ω) = A.indicator V + A.indicator W := by
    funext ω; by_cases h : ω ∈ A <;> simp [h]
  have hui : Integrable (A.indicator (fun ω => V ω + W ω)) Q := by rw [hu]; exact h1.add h2
  have hint : ∫ ω, A.indicator (fun ω => V ω + W ω) ω ∂Q = ∫ ω, A.indicator V ω ∂Q := by
    rw [hu]; simp only [Pi.add_apply]; rw [integral_add h1 h2]
    rw [show (∫ ω, A.indicator W ω ∂Q) = 0 from h3, add_zero]
  have hle := lint_eq Q hui h1 hint
  have hP : (∫⁻ ω, ENNReal.ofReal (A.indicator V ω) ∂Q) = 0 := by
    refine lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun ω => ?_)
    by_cases h : ω ∈ A
    · have : V ω < 0 := h.2
      simp [Set.indicator_of_mem h, this.le]
    · simp [Set.indicator_of_notMem h]
  rw [hP, zero_add] at hle
  calc ∫⁻ ω, (D n).indicator (fun ω => ENNReal.ofReal (-V ω)) ω ∂Q
      = ∫⁻ ω, ENNReal.ofReal (-A.indicator V ω) ∂Q := by
        refine lintegral_congr fun ω => ?_
        rw [ofReal_neg_ind]
        by_cases h : ω ∈ D n
        · by_cases h' : V ω < 0
          · have hA : ω ∈ A := ⟨h, h'⟩
            simp [Set.indicator_of_mem h, Set.indicator_of_mem hA]
          · have hA : ω ∉ A := fun hA => h' hA.2
            simp [Set.indicator_of_mem h, Set.indicator_of_notMem hA, not_lt.mp h']
        · have hA : ω ∉ A := fun hA => h hA.1
          simp [Set.indicator_of_notMem h, Set.indicator_of_notMem hA]
    _ ≤ (∫⁻ ω, ENNReal.ofReal (A.indicator (fun ω => V ω + W ω) ω) ∂Q) +
          ∫⁻ ω, ENNReal.ofReal (-A.indicator V ω) ∂Q := le_add_self
    _ = ∫⁻ ω, ENNReal.ofReal (-A.indicator (fun ω => V ω + W ω) ω) ∂Q := hle
    _ ≤ ∫⁻ ω, ENNReal.ofReal (-(V ω + W ω)) ∂Q := by
        refine lintegral_mono fun ω => ?_
        rw [ofReal_neg_ind]
        exact Set.indicator_le_self _ _ ω

end LemmaA2Aux

namespace LemmaA2Aux

lemma ereal_sub_fin {a b : ENNReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a : EReal) - (b : EReal) = ((a.toReal - b.toReal : ℝ) : EReal) := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  show ((a:ENNReal):EReal) - ((b:ENNReal):EReal) = (((a:ℝ) - (b:ℝ) : ℝ) : EReal)
  rw [EReal.coe_sub]; rfl

lemma ofReal_abs_eq (r : ℝ) : ENNReal.ofReal |r| = ENNReal.ofReal r + ENNReal.ofReal (-r) := by
  rcases le_total 0 r with h | h
  · simp [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (neg_nonpos.mpr h)]
  · simp [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h]

lemma integrable_of_fin {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) {u : Ω → ℝ}
    (hu : Measurable u) (h1 : ∫⁻ ω, ENNReal.ofReal (u ω) ∂Q ≠ ⊤)
    (h2 : ∫⁻ ω, ENNReal.ofReal (-u ω) ∂Q ≠ ⊤) : Integrable u Q := by
  refine ⟨hu.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp only [Real.enorm_eq_ofReal_abs, ofReal_abs_eq]
  rw [lintegral_add_left (f := fun ω => ENNReal.ofReal (u ω)) (ENNReal.measurable_ofReal.comp hu)]
  exact ENNReal.add_lt_top.mpr ⟨h1.lt_top, h2.lt_top⟩

lemma extExp_coe_eq {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (u : Ω → ℝ) :
    extExp Q (fun ω => ((u ω : ℝ) : EReal)) =
      ((∫⁻ ω, ENNReal.ofReal (u ω) ∂Q : ENNReal) : EReal) -
        ((∫⁻ ω, ENNReal.ofReal (-u ω) ∂Q : ENNReal) : EReal) := by
  unfold NondomArb.Superhedge.extExp
  congr 3

lemma extExp_zero {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) {u : Ω → ℝ}
    (hu : Measurable u) (h : extExp Q (fun ω => ((u ω : ℝ) : EReal)) = 0) :
    Integrable u Q ∧ ∫ ω, u ω ∂Q = 0 := by
  rw [extExp_coe_eq] at h
  set A := ∫⁻ ω, ENNReal.ofReal (u ω) ∂Q with hA
  set B := ∫⁻ ω, ENNReal.ofReal (-u ω) ∂Q with hB
  have hAt : A ≠ ⊤ := by
    intro hA'
    rw [hA', EReal.coe_ennreal_top] at h
    by_cases hB' : B = ⊤
    · rw [hB', EReal.coe_ennreal_top, EReal.sub_top] at h; exact absurd h (by simp)
    · rw [EReal.top_sub (fun h' => hB' (EReal.coe_ennreal_eq_top_iff.mp h'))] at h
      exact absurd h (by simp)
  have hBt : B ≠ ⊤ := by
    intro hB'
    rw [hB', EReal.coe_ennreal_top, EReal.sub_top] at h; exact absurd h (by simp)
  have hi := integrable_of_fin Q hu hAt hBt
  refine ⟨hi, ?_⟩
  rw [ereal_sub_fin hAt hBt] at h
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi]
  exact_mod_cast h

end LemmaA2Aux

theorem solution {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℕ m)
    (Q : Measure Ω) [IsProbabilityMeasure Q] {T d e : ℕ}
    (S : ℕ → Ω → (Fin d → ℝ)) (hS : ∀ t ≤ T, Measurable[ℱ t] (S t))
    (f : Ω → EReal) (hf : Measurable f) (g : Ω → (Fin e → ℝ)) (hg : Measurable g)
    (hgQ : ∀ i : Fin e, extExp Q (fun ω => ((g ω i : ℝ) : EReal)) = 0)
    (hloc : IsLocalMartingaleOn Q ℱ T (fun t ω => S t ω - S 0 ω))
    (x : ℝ) (H : ℕ → Ω → (Fin d → ℝ)) (hH : IsPredictable ℱ T H) (h : Fin e → ℝ)
    (hsup : ∀ᵐ ω ∂Q, f ω ≤ ((x + wealth T S H ω + h ⬝ᵥ g ω : ℝ) : EReal)) :
    extExp Q f ≤ x := by
  classical
  obtain ⟨τ, hτ, hτmono, hτae, hmart⟩ := hloc
  let M : ℕ → Ω → ℝ := fun t ω => ∑ u ∈ Finset.range t, H u ω ⬝ᵥ (S (u + 1) ω - S u ω)
  have hMsucc : ∀ t ω, M (t+1) ω = M t ω + H t ω ⬝ᵥ (S (t + 1) ω - S t ω) :=
    fun t ω => Finset.sum_range_succ _ _
  have hdot : ∀ {m0 : MeasurableSpace Ω} (A Bv : Ω → Fin d → ℝ), Measurable[m0] A →
      Measurable[m0] Bv → Measurable[m0] (fun ω => A ω ⬝ᵥ Bv ω) := by
    intro m0 A Bv hA hB
    show Measurable[m0] fun ω => ∑ i, A ω i * Bv ω i
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp hA).mul ((measurable_pi_apply i).comp hB)
  have hMm : ∀ t ≤ T, Measurable[ℱ t] (M t) := by
    intro t ht
    show Measurable[ℱ t] fun ω => ∑ u ∈ Finset.range t, H u ω ⬝ᵥ (S (u + 1) ω - S u ω)
    refine Finset.measurable_sum _ fun u hu => ?_
    have hut : u < t := Finset.mem_range.mp hu
    refine hdot _ _ ((hH u (by omega)).mono (ℱ.mono hut.le) le_rfl) ?_
    exact ((hS (u+1) (by omega)).mono (ℱ.mono hut) le_rfl).sub
      ((hS u (by omega)).mono (ℱ.mono hut.le) le_rfl)
  have hstep : ∀ t < T, (∫⁻ ω, ENNReal.ofReal (M (t+1) ω) ∂Q) + ∫⁻ ω, ENNReal.ofReal (-M t ω) ∂Q =
      (∫⁻ ω, ENNReal.ofReal (M t ω) ∂Q) + ∫⁻ ω, ENNReal.ofReal (-M (t+1) ω) ∂Q ∧
      (∫⁻ ω, ENNReal.ofReal (-M t ω) ∂Q) ≤ ∫⁻ ω, ENNReal.ofReal (-M (t+1) ω) ∂Q := by
    intro t ht
    let Y : Ω → Fin d → ℝ := fun ω => S (t + 1) ω - S t ω
    let B : ℕ → Set Ω := fun n => {ω | t < τ n ω}
    have hB : ∀ n, MeasurableSet[ℱ t] (B n) := by
      intro n
      have : B n = {ω | τ n ω ≤ t}ᶜ := by ext ω; simp [B]
      rw [this]; exact (hτ n t).compl
    have hBmono : Monotone B := fun a b hab ω hω => lt_of_lt_of_le hω (hτmono ω hab)
    have hBae : ∀ᵐ ω ∂Q, ∃ n, ω ∈ B n := by
      filter_upwards [hτae] with ω hω
      exact (hω.eventually (eventually_gt_atTop t)).exists
    have hYm : Measurable Y :=
      ((hS (t+1) ht).mono (ℱ.le _) le_rfl).sub ((hS t ht.le).mono (ℱ.le _) le_rfl)
    let X1 : ℕ → Fin d → Ω → ℝ := fun n i ω => (S (min (t+1) (τ n ω)) ω - S 0 ω) i
    let X0 : ℕ → Fin d → Ω → ℝ := fun n i ω => (S (min t (τ n ω)) ω - S 0 ω) i
    have hind : ∀ n i, (B n).indicator (fun ω => Y ω i) = fun ω => X1 n i ω - X0 n i ω := by
      intro n i; funext ω
      by_cases hω : t < τ n ω
      · have h1 : min (t+1) (τ n ω) = t+1 := min_eq_left hω
        have h2 : min t (τ n ω) = t := min_eq_left hω.le
        simp [X1, X0, Set.indicator_of_mem (show ω ∈ B n from hω), h1, h2, Y]
      · have hle : τ n ω ≤ t := not_lt.mp hω
        have h1 : min (t+1) (τ n ω) = τ n ω := min_eq_right (by omega)
        have h2 : min t (τ n ω) = τ n ω := min_eq_right hle
        simp [X1, X0, Set.indicator_of_notMem (show ω ∉ B n from hω), h1, h2]
    have hX1 : ∀ n i, Measurable[ℱ (t+1)] (X1 n i) ∧ Integrable (X1 n i) Q :=
      fun n i => (hmart n).1 (t+1) ht i
    have hX0 : ∀ n i, Measurable[ℱ t] (X0 n i) ∧ Integrable (X0 n i) Q :=
      fun n i => (hmart n).1 t ht.le i
    have hYi : ∀ n i, Integrable ((B n).indicator (fun ω => Y ω i)) Q := by
      intro n i; rw [hind]; exact (hX1 n i).2.sub (hX0 n i).2
    have hY0 : ∀ n i, Q[(B n).indicator (fun ω => Y ω i) | ℱ t] =ᵐ[Q] 0 := by
      intro n i
      rw [hind]
      have e1 : Q[X1 n i - X0 n i | ℱ t] =ᵐ[Q] Q[X1 n i | ℱ t] - Q[X0 n i | ℱ t] :=
        condExp_sub (hX1 n i).2 (hX0 n i).2 (ℱ t)
      have e2 : Q[X1 n i | ℱ t] =ᵐ[Q] X0 n i := (hmart n).2 t ht i
      have e3 : Q[X0 n i | ℱ t] = X0 n i :=
        condExp_of_stronglyMeasurable (ℱ.le t) (hX0 n i).1.stronglyMeasurable (hX0 n i).2
      have e4 : (fun ω => X1 n i ω - X0 n i ω) = X1 n i - X0 n i := rfl
      rw [e4]
      filter_upwards [e1, e2] with ω h1 h2
      rw [h1, Pi.sub_apply, h2, e3]; simp
    have := LemmaA2Aux.step (ℱ.le t) Q (M t) (hMm t ht.le) (H t) (hH t ht) Y hYm B hB hBmono
      hBae hYi hY0
    simp only [hMsucc]
    exact this
  have hgi : ∀ i, Integrable (fun ω => g ω i) Q ∧ ∫ ω, g ω i ∂Q = 0 := fun i =>
    LemmaA2Aux.extExp_zero Q ((measurable_pi_apply i).comp hg) (hgQ i)
  have hext : extExp Q f = ((∫⁻ ω, (f ω).toENNReal ∂Q : ENNReal) : EReal) -
      ((∫⁻ ω, (-f ω).toENNReal ∂Q : ENNReal) : EReal) := rfl
  by_cases hNtop : ∫⁻ ω, (-f ω).toENNReal ∂Q = ⊤
  · rw [hext, hNtop, EReal.coe_ennreal_top, EReal.sub_top]; exact bot_le
  let G : Ω → ℝ := fun ω => x + M T ω + h ⬝ᵥ g ω
  have hGeq : ∀ ω, wealth T S H ω = M T ω := fun ω => rfl
  have hsup' : ∀ᵐ ω ∂Q, f ω ≤ ((G ω : ℝ) : EReal) := by
    filter_upwards [hsup] with ω hω
    simpa [G, hGeq] using hω
  let gs : Ω → ℝ := fun ω => |x| + ∑ i, |h i| * |g ω i|
  have hgsi : Integrable gs Q :=
    (integrable_const _).add (integrable_finsetSum _ fun i _ => ((hgi i).1.abs.const_mul |h i|))
  have hhg : ∀ ω, h ⬝ᵥ g ω ≤ ∑ i, |h i| * |g ω i| := by
    intro ω
    show ∑ i, h i * g ω i ≤ _
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← abs_mul]; exact le_abs_self _
  have hnegG : ∀ᵐ ω ∂Q, ENNReal.ofReal (-G ω) ≤ (-f ω).toENNReal := by
    filter_upwards [hsup'] with ω hω
    have : (((-G ω : ℝ)) : EReal) ≤ -f ω := by
      rw [EReal.coe_neg]; exact EReal.neg_le_neg_iff.mpr hω
    simpa using EReal.toENNReal_le_toENNReal this
  have hMTm : Measurable (M T) := (hMm T le_rfl).mono (ℱ.le T) le_rfl
  have hgsm : Measurable gs := by
    show Measurable fun ω => |x| + ∑ i, |h i| * |g ω i|
    exact measurable_const.add (Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((measurable_pi_apply i).comp hg).abs)
  have hbT : ∫⁻ ω, ENNReal.ofReal (-M T ω) ∂Q ≠ ⊤ := by
    have hle : ∫⁻ ω, ENNReal.ofReal (-M T ω) ∂Q ≤
        ∫⁻ ω, ((-f ω).toENNReal + ENNReal.ofReal (gs ω)) ∂Q := by
      refine lintegral_mono_ae ?_
      filter_upwards [hnegG] with ω hω
      have h1 : -M T ω ≤ -G ω + gs ω := by
        simp only [G, gs]; linarith [hhg ω, le_abs_self x]
      calc ENNReal.ofReal (-M T ω) ≤ ENNReal.ofReal (-G ω + gs ω) := ENNReal.ofReal_le_ofReal h1
        _ ≤ ENNReal.ofReal (-G ω) + ENNReal.ofReal (gs ω) := ENNReal.ofReal_add_le
        _ ≤ _ := add_le_add_left hω _
    rw [lintegral_add_right _ hgsm.ennreal_ofReal] at hle
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hNtop, hgsi.lintegral_lt_top.ne⟩) hle
  -- backward induction: all negative parts finite
  have hb : ∀ k ≤ T, ∫⁻ ω, ENNReal.ofReal (-M (T - k) ω) ∂Q ≠ ⊤ := by
    intro k
    induction k with
    | zero => intro _; simpa using hbT
    | succ k ih =>
      intro hk
      have ht : T - (k+1) < T := by omega
      have := (hstep (T - (k+1)) ht).2
      have e : T - (k+1) + 1 = T - k := by omega
      rw [e] at this
      exact ne_top_of_le_ne_top (ih (by omega)) this
  have hb' : ∀ t ≤ T, ∫⁻ ω, ENNReal.ofReal (-M t ω) ∂Q ≠ ⊤ := by
    intro t ht
    have := hb (T - t) (by omega)
    rwa [show T - (T - t) = t by omega] at this
  have hab : ∀ t ≤ T, ∫⁻ ω, ENNReal.ofReal (M t ω) ∂Q = ∫⁻ ω, ENNReal.ofReal (-M t ω) ∂Q := by
    intro t
    induction t with
    | zero => intro _; simp [M]
    | succ t ih =>
      intro ht
      have h1 := (hstep t (by omega)).1
      rw [ih (by omega), add_comm (∫⁻ ω, ENNReal.ofReal (-M t ω) ∂Q)] at h1
      exact (ENNReal.add_left_inj (hb' t (by omega))).mp h1
  have hMTi : Integrable (M T) Q :=
    LemmaA2Aux.integrable_of_fin Q hMTm (by rw [hab T le_rfl]; exact hb' T le_rfl) (hb' T le_rfl)
  have hMT0 : ∫ ω, M T ω ∂Q = 0 := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hMTi, hab T le_rfl, sub_self]
  have hhgi : Integrable (fun ω => h ⬝ᵥ g ω) Q := by
    show Integrable (fun ω => ∑ i, h i * g ω i) Q
    exact integrable_finsetSum _ fun i _ => (hgi i).1.const_mul (h i)
  have hGi : Integrable G Q := ((integrable_const x).add hMTi).add hhgi
  have hGint : ∫ ω, G ω ∂Q = x := by
    show ∫ ω, x + M T ω + h ⬝ᵥ g ω ∂Q = x
    rw [integral_add (f := fun ω => x + M T ω) (g := fun ω => h ⬝ᵥ g ω)
      ((integrable_const x).add hMTi) hhgi,
      integral_add (f := fun _ => x) (g := M T) (integrable_const x) hMTi, hMT0]
    have : ∫ ω, h ⬝ᵥ g ω ∂Q = 0 := by
      show ∫ ω, ∑ i, h i * g ω i ∂Q = 0
      rw [integral_finsetSum _ fun i _ => (hgi i).1.const_mul (h i)]
      simp [integral_const_mul, (hgi _).2]
    rw [this]; simp
  have hpos : ∫⁻ ω, (f ω).toENNReal ∂Q ≤ ∫⁻ ω, ENNReal.ofReal (G ω) ∂Q := by
    refine lintegral_mono_ae ?_
    filter_upwards [hsup'] with ω hω
    simpa using EReal.toENNReal_le_toENNReal hω
  have hneg : ∫⁻ ω, ENNReal.ofReal (-G ω) ∂Q ≤ ∫⁻ ω, (-f ω).toENNReal ∂Q :=
    lintegral_mono_ae hnegG
  rw [hext]
  calc ((∫⁻ ω, (f ω).toENNReal ∂Q : ENNReal) : EReal) - ((∫⁻ ω, (-f ω).toENNReal ∂Q : ENNReal) : EReal)
      ≤ ((∫⁻ ω, ENNReal.ofReal (G ω) ∂Q : ENNReal) : EReal) -
          ((∫⁻ ω, ENNReal.ofReal (-G ω) ∂Q : ENNReal) : EReal) :=
        EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hpos)
          (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hneg)
    _ = ((∫ ω, G ω ∂Q : ℝ) : EReal) := by
        have hGp : ∫⁻ ω, ENNReal.ofReal (G ω) ∂Q ≠ ⊤ := hGi.lintegral_lt_top.ne
        have hGn : ∫⁻ ω, ENNReal.ofReal (-G ω) ∂Q ≠ ⊤ := hGi.neg.lintegral_lt_top.ne
        rw [LemmaA2Aux.ereal_sub_fin hGp hGn,
          integral_eq_lintegral_pos_part_sub_lintegral_neg_part hGi]
    _ = x := by rw [hGint]
