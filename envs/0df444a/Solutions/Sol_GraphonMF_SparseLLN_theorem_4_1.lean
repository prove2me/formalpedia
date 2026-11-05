-- Prove2me | solution 1 for GraphonMF.SparseLLN.theorem_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T22:33:17.921127+00:00
-- url     : https://prove2.me/submissions/f76e1986-121a-4386-bdad-c89f3fdc188b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GraphonMF_SparseLLN_eq_4_3
import Theorems.Thm_GraphonMF_SparseLLN_lemma_7_2
import Theorems.Thm_GraphonMF_SparseLLN_remark_2_1

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false

open GraphonMF.SparseLLN in
theorem solution
    {T : ℝ≥0} {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hT : 0 < T) (hd : 0 < d)
    (P : Measure Ω) (X0 : GraphonMF.Stability.I → Ω → Vec d) (B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d)
    (hnoise : NoiseSetting P X0 B)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G)
    (b : Vec d → Vec d → Vec d) (σ : Vec d → Matrix (Fin d) (Fin d) ℝ)
    (β : ℕ → ℝ) (h41 : Cond41 (initialLaw P X0) b σ β)
    (N : ℕ) (J : Fin N → Set GraphonMF.Stability.I)
    (h22a : Cond22a (initialLaw P X0) J)
    (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ)
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
    (hξ : ∀ n i j, Measurable (fun ω => ξ n ω i j))
    (h42 : Cond42 P X0 B ξ Gs β G)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d)
    (hX : IsGraphonSolution42 P X0 B hnoise G b σ X)
    (Xn : (n : ℕ) → Fin n → Ω → GraphonMF.Stability.Cd T d)
    (hXn : ∀ n, IsParticleSolution41 P X0 B hnoise ξ hξ β b σ n (Xn n)) :
    ConvergesInProbability P (empiricalSeq Xn) (solutionMixture hX) ∧
      (Cond22b G J → Tendsto
        (fun n => errorAvg P X (n + 1) (Xn (n + 1))) atTop (𝓝 (0 : ℝ≥0∞))) := by
  refine ⟨eq_4_3 hT hd P X0 B hnoise G hG b σ β h41 N J h22a Gs ξ hξ h42 X hX Xn hXn, ?_⟩
  intro h22b
  obtain ⟨κ, -, hκ⟩ := lemma_7_2 hT hd P X0 B hnoise G hG b σ β h41 N J h22a h22b X hX
  -- operator-norm convergence from cut-norm convergence (Remark 2.1), along `n + 1`
  have hop : Tendsto (fun n => GraphonMF.Stability.opNorm (fun u v => Gs (n + 1) u v - G u v))
      atTop (𝓝 0) :=
    remark_2_1 G (fun n => Gs (n + 1)) hG (fun n => (h42.1.1 (n + 1) (by omega)).1)
      (h42.2.comp (tendsto_add_atTop_nat 1))
  have hlimop : limsup (fun n => ENNReal.ofReal (GraphonMF.Stability.opNorm
      (fun u v => Gs n u v - G u v))) atTop = 0 := by
    rw [← Filter.limsup_nat_add _ 1]
    have := (ENNReal.tendsto_ofReal hop)
    rw [ENNReal.ofReal_zero] at this
    exact this.limsup_eq
  -- the coupling error has limsup ≤ κ / M² for every M > 0
  have hbound : ∀ m : ℕ, limsup (fun n => errorAvg P X n (Xn n)) atTop ≤
      ENNReal.ofReal (κ / ((m : ℝ) + 1) ^ 2) := by
    intro m
    obtain ⟨κM, -, hκM⟩ := hκ ((m : ℝ) + 1) (by positivity)
    have h := hκM Gs ξ hξ h42.1 Xn hXn
    rwa [hlimop, mul_zero, zero_add] at h
  have hsmall : Tendsto (fun m : ℕ => ENNReal.ofReal (κ / ((m : ℝ) + 1) ^ 2)) atTop (𝓝 0) := by
    have : Tendsto (fun m : ℕ => κ / ((m : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      have h1 : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      exact (tendsto_pow_atTop two_ne_zero).comp h1
    simpa using ENNReal.tendsto_ofReal this
  have hlim : limsup (fun n => errorAvg P X n (Xn n)) atTop = 0 :=
    le_antisymm (ge_of_tendsto' hsmall hbound) bot_le
  have htend : Tendsto (fun n => errorAvg P X n (Xn n)) atTop (𝓝 0) :=
    tendsto_of_le_liminf_of_limsup_le bot_le hlim.le
  exact htend.comp (tendsto_add_atTop_nat 1)
