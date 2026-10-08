-- Prove2me | solution 1 for KingmanSubadditive.BanachAlgebra.logNormProcess_conditions
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:17:25.692479+00:00
-- url     : https://prove2.me/submissions/8e8bf94f-a8e1-4157-ac8c-1c17588a777a

import Mathlib
import Definitions.Def_KingmanSubadditive_BanachAlgebra_Process
import Definitions.Def_KingmanSubadditive_BanachAlgebra_RandomProduct



namespace KingmanSubadditive.BanachAlgebra

open MeasureTheory

/-- the product of a list of coordinates as a function of the sequence -/
def listProdSeq {𝔅 : Type*} [Monoid 𝔅] (l : List ℕ) (f : ℕ → 𝔅) : 𝔅 := (l.map f).prod

theorem prodRange_eq_core {Ω 𝔅 : Type*} [Monoid 𝔅] (Y : ℕ → Ω → 𝔅) (s t : ℕ) (ω : Ω) :
    prodRange Y s t ω = listProdSeq (List.range' s (t - s)) (fun k => Y (k + 1) ω) := by
  unfold prodRange listProdSeq
  rw [show s + 1 = 1 + s by omega, ← List.map_add_range', List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  simp [add_comm]

theorem prodRange_shift_eq_core {Ω 𝔅 : Type*} [Monoid 𝔅] (Y : ℕ → Ω → 𝔅) (s t : ℕ) (ω : Ω) :
    prodRange Y (s + 1) (t + 1) ω = listProdSeq (List.range' s (t - s)) (fun k => Y (k + 2) ω) := by
  unfold prodRange listProdSeq
  rw [Nat.add_sub_add_right, show s + 1 + 1 = 2 + s by omega, ← List.map_add_range', List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  simp [add_comm]

theorem prodRange_mul_core {Ω 𝔅 : Type*} [Monoid 𝔅] (Y : ℕ → Ω → 𝔅) (s t u : ℕ) (ω : Ω)
    (hst : s ≤ t) (htu : t ≤ u) :
    prodRange Y s u ω = prodRange Y s t ω * prodRange Y t u ω := by
  unfold prodRange
  rw [← List.prod_append, ← List.map_append]
  congr 2
  have : u - s = (t - s) + (u - t) := by omega
  rw [this, ← List.range'_append_1]
  congr 2
  omega

theorem logNorm_mul_le_core {𝔅 : Type*} [NormedRing 𝔅] (a b : 𝔅) :
    logNorm (a * b) ≤ logNorm a + logNorm b := by
  unfold logNorm
  rw [← ENNReal.log_mul_add, ← ENNReal.ofReal_mul (norm_nonneg a)]
  exact ENNReal.log_le_log (ENNReal.ofReal_le_ofReal (norm_mul_le a b))

theorem measurable_logNorm_core {𝔅 : Type*} [NormedRing 𝔅] [MeasurableSpace 𝔅] [BorelSpace 𝔅] :
    Measurable (logNorm : 𝔅 → EReal) := by
  unfold logNorm
  exact (ENNReal.log_monotone.measurable).comp (ENNReal.measurable_ofReal.comp measurable_norm)

theorem stronglyMeasurable_prodRange_core {𝕜 𝔅 Ω : Type*} [RCLike 𝕜] [NormedRing 𝔅]
    [NormedAlgebra 𝕜 𝔅] [MeasurableSpace Ω] (Y : ℕ → Ω → 𝔅)
    (hY : ∀ n : ℕ, 1 ≤ n → StronglyMeasurable (Y n)) (l : List ℕ) (hl : ∀ i ∈ l, 1 ≤ i) :
    StronglyMeasurable (fun ω => ((l.map (fun i => Y i ω)).prod)) := by
  induction l with
  | nil => simpa using stronglyMeasurable_const
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hY i (hl i (by simp))).mul (ih (fun j hj => hl j (by simp [hj])))

theorem aestronglyMeasurable_listProdSeq_core {𝕜 𝔅 Ω : Type*} [RCLike 𝕜] [NormedRing 𝔅]
    [NormedAlgebra 𝕜 𝔅] [MeasurableSpace 𝔅] [BorelSpace 𝔅]
    [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → Ω → 𝔅)
    (hY : ∀ n : ℕ, 1 ≤ n → StronglyMeasurable (Y n)) (l : List ℕ) :
    AEStronglyMeasurable (listProdSeq l : (ℕ → 𝔅) → 𝔅)
      (Measure.map (fun ω (k : ℕ) => Y (k + 1) ω) P) := by
  have hseq : Measurable (fun ω (k : ℕ) => Y (k + 1) ω) := by
    rw [measurable_pi_iff]; intro k; exact (hY (k + 1) (by omega)).measurable
  have hcoord : ∀ k : ℕ, AEStronglyMeasurable (fun f : ℕ → 𝔅 => f k)
      (Measure.map (fun ω (k : ℕ) => Y (k + 1) ω) P) := by
    intro k
    rw [aestronglyMeasurable_iff_aemeasurable_separable]
    refine ⟨(measurable_pi_apply k).aemeasurable, closure (Set.range (Y (k + 1))), ?_, ?_⟩
    · exact (hY (k + 1) (by omega)).isSeparable_range.closure
    · rw [ae_map_iff hseq.aemeasurable]
      · exact Filter.Eventually.of_forall (fun ω => subset_closure (Set.mem_range_self ω))
      · exact isClosed_closure.measurableSet.preimage (measurable_pi_apply k)
  show AEStronglyMeasurable (fun f : ℕ → 𝔅 => (l.map f).prod) _
  induction l with
  | nil => simpa using aestronglyMeasurable_const
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hcoord i).mul ih

theorem logNormProcess_conditions_core {𝕜 𝔅 Ω : Type*} [RCLike 𝕜] [NormedRing 𝔅]
    [NormedAlgebra 𝕜 𝔅] [CompleteSpace 𝔅] [MeasurableSpace 𝔅] [BorelSpace 𝔅]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → 𝔅)
    (hY : ∀ n : ℕ, 1 ≤ n → StronglyMeasurable (Y n)) (hstat : IsStationarySeq P Y)
    (hlog : ∫⁻ ω, (logNorm (Y 1 ω)).toENNReal ∂P < ⊤) :
    IsMeasurableFamily (logNormProcess Y) ∧
      (∀ (s t u : ℕ) (ω : Ω), s < t → t < u →
        logNormProcess Y s u ω ≤ logNormProcess Y s t ω + logNormProcess Y t u ω) ∧
      S2 P (logNormProcess Y) ∧
      ∫⁻ ω, (logNormProcess Y 0 1 ω).toENNReal ∂P < ⊤ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s t hst
    unfold logNormProcess
    refine measurable_logNorm_core.comp ?_
    have := stronglyMeasurable_prodRange_core (𝕜 := 𝕜) Y hY (List.range' (s + 1) (t - s))
      (fun i hi => by rw [List.mem_range'_1] at hi; omega)
    exact this.measurable
  · intro s t u ω hst htu
    unfold logNormProcess
    rw [prodRange_mul_core Y s t u ω hst.le htu.le]
    exact logNorm_mul_le_core _ _
  · unfold S2
    let G : (ℕ → 𝔅) → (KingmanSubadditive.Ergodic.Interval → EReal) :=
      fun f p => logNorm (listProdSeq (List.range' p.1.1 (p.1.2 - p.1.1)) f)
    have e1 : shiftedPath (logNormProcess Y) = G ∘ (fun ω (k : ℕ) => Y (k + 2) ω) := by
      funext ω p
      simp only [shiftedPath, logNormProcess, G, Function.comp]
      rw [prodRange_shift_eq_core]
    have e2 : path (logNormProcess Y) = G ∘ (fun ω (k : ℕ) => Y (k + 1) ω) := by
      funext ω p
      simp only [path, logNormProcess, G, Function.comp]
      rw [prodRange_eq_core]
    have hseq : Measurable (fun ω (k : ℕ) => Y (k + 1) ω) := by
      rw [measurable_pi_iff]; intro k; exact (hY (k + 1) (by omega)).measurable
    have hseq2 : Measurable (fun ω (k : ℕ) => Y (k + 2) ω) := by
      rw [measurable_pi_iff]; intro k; exact (hY (k + 2) (by omega)).measurable
    have hG : AEMeasurable G (Measure.map (fun ω (k : ℕ) => Y (k + 1) ω) P) := by
      rw [aemeasurable_pi_iff]
      intro p
      exact measurable_logNorm_core.comp_aemeasurable
        (aestronglyMeasurable_listProdSeq_core (𝕜 := 𝕜) P Y hY _).aemeasurable
    have hG2 : AEMeasurable G (Measure.map (fun ω (k : ℕ) => Y (k + 2) ω) P) := by
      unfold IsStationarySeq at hstat
      rw [hstat]; exact hG
    rw [e1, e2, ← AEMeasurable.map_map_of_aemeasurable hG2 hseq2.aemeasurable,
      ← AEMeasurable.map_map_of_aemeasurable hG hseq.aemeasurable]
    unfold IsStationarySeq at hstat
    rw [hstat]
  · have : ∀ ω, logNormProcess Y 0 1 ω = logNorm (Y 1 ω) := by
      intro ω
      simp [logNormProcess, prodRange]
    simp only [this]
    exact hlog

end KingmanSubadditive.BanachAlgebra

open KingmanSubadditive.BanachAlgebra
open MeasureTheory

theorem solution {𝕜 𝔅 Ω : Type*} [RCLike 𝕜] [NormedRing 𝔅]
    [NormedAlgebra 𝕜 𝔅] [CompleteSpace 𝔅] [MeasurableSpace 𝔅] [BorelSpace 𝔅]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → 𝔅)
    (hY : ∀ n : ℕ, 1 ≤ n → StronglyMeasurable (Y n)) (hstat : IsStationarySeq P Y)
    (hlog : ∫⁻ ω, (logNorm (Y 1 ω)).toENNReal ∂P < ⊤) :
    IsMeasurableFamily (logNormProcess Y) ∧
      (∀ (s t u : ℕ) (ω : Ω), s < t → t < u →
        logNormProcess Y s u ω ≤ logNormProcess Y s t ω + logNormProcess Y t u ω) ∧
      S2 P (logNormProcess Y) ∧
      ∫⁻ ω, (logNormProcess Y 0 1 ω).toENNReal ∂P < ⊤ := by
  exact logNormProcess_conditions_core (𝕜 := 𝕜) P Y hY hstat hlog
