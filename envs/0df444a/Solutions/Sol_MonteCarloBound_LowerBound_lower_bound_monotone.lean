-- Prove2me | solution 1 for MonteCarloBound.LowerBound.lower_bound_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T09:01:34.176126+00:00
-- url     : https://prove2.me/submissions/4fc85a6b-843a-4401-b388-0a21325a394d

import Mathlib
import Definitions.Def_SolutionQuality_SRP_Setting
import Definitions.Def_MonteCarloBound_LowerBound_Setting

set_option autoImplicit false

namespace MCBLowerAux

open MeasureTheory ProbabilityTheory SolutionQuality.SRP MonteCarloBound.LowerBound

lemma skipIndex_injective (i : ℕ) : Function.Injective (skipIndex i) := by
  intro a b h
  unfold skipIndex at h
  split_ifs at h <;> omega

lemma sum_skip (g : ℕ → ℝ) : ∀ n i, i ≤ n →
    ∑ j ∈ Finset.range n, g (skipIndex i j) + g i = ∑ k ∈ Finset.range (n + 1), g k := by
  intro n
  induction n with
  | zero =>
    intro i hi
    have : i = 0 := by omega
    subst this
    simp
  | succ n ih =>
    intro i hi
    rcases Nat.lt_or_ge n i with h | h
    · have hi' : i = n + 1 := by omega
      subst hi'
      have hc : ∀ j ∈ Finset.range (n + 1), g (skipIndex (n + 1) j) = g j := by
        intro j hj
        have hj' : j < n + 1 := Finset.mem_range.mp hj
        unfold skipIndex
        rw [if_pos hj']
      rw [Finset.sum_congr rfl hc, Finset.sum_range_succ _ (n + 1)]
    · have h1 : skipIndex i n = n + 1 := by
        unfold skipIndex
        rw [if_neg (by omega)]
      rw [Finset.sum_range_succ, Finset.sum_range_succ _ (n + 1), h1, ← ih i h]
      ring

lemma mean_identity {d : ℕ} {Ξ : Type*} (f : E d → Ξ → ℝ) (s : ℕ → Ξ) (n : ℕ) (hn : 1 ≤ n)
    (x : E d) :
    sampleMean f s (n + 1) x = (1 / ((n : ℝ) + 1)) * ∑ i ∈ Finset.range (n + 1),
      sampleMean f (fun j => s (skipIndex i j)) n x := by
  unfold sampleMean
  have key : ∀ i ∈ Finset.range (n + 1),
      (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, f x (s (skipIndex i j)) =
      (1 / (n : ℝ)) * ((∑ k ∈ Finset.range (n + 1), f x (s k)) - f x (s i)) := by
    intro i hi
    have := sum_skip (fun k => f x (s k)) n i (by have := Finset.mem_range.mp hi; omega)
    congr 1
    linarith
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  push_cast
  field_simp
  ring

lemma saa_le {d : ℕ} {Ξ : Type*} (f : E d → Ξ → ℝ) (X : Set (E d)) (s : ℕ → Ξ) (m : ℕ)
    (h : ∃ x ∈ X, ∀ y ∈ X, sampleMean f s m x ≤ sampleMean f s m y) {x : E d} (hx : x ∈ X) :
    saaValue f X s m ≤ sampleMean f s m x := by
  obtain ⟨x0, _, hx0⟩ := h
  unfold saaValue
  exact csInf_le ⟨sampleMean f s m x0, by rintro _ ⟨y, hy, rfl⟩; exact hx0 y hy⟩ ⟨x, hx, rfl⟩

lemma path_law_precomp {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ) (g : ℕ → ℕ) (hg : Function.Injective g) :
    P.map (fun ω j => ξ (g j) ω) = pathLaw P ξ := by
  obtain ⟨hm, hind, hlaw⟩ := hξ
  unfold pathLaw
  rw [hind.map_fun_eq_infinitePi_map₀ (measurable_pi_lambda _ hm).aemeasurable,
    (hind.precomp hg).map_fun_eq_infinitePi_map₀
      (measurable_pi_lambda _ (fun j => hm (g j))).aemeasurable]
  have h1 : (fun i => P.map (ξ (g i))) = fun _ => μ := funext fun i => hlaw _
  have h2 : (fun i => P.map (ξ i)) = fun _ => μ := funext fun i => hlaw _
  simp only [h1, h2]

end MCBLowerAux

open MeasureTheory ProbabilityTheory SolutionQuality.SRP MonteCarloBound.LowerBound in
theorem solution {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E d → Ξ → ℝ) (X : Set (E d))
    (hint : ∀ x ∈ X, Integrable (f x) μ)
    (hopt : ∃ xs ∈ X, ∀ y ∈ X, expectedCost μ f xs ≤ expectedCost μ f y)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample P μ ξ)
    (n : ℕ) (hn : 1 ≤ n)
    (hmin : ∀ᵐ s ∂(pathLaw P ξ), ∀ m, 1 ≤ m →
      ∃ x ∈ X, ∀ y ∈ X, sampleMean f s m x ≤ sampleMean f s m y)
    (hzint : Integrable (fun ω => saaValue f X (fun i => ξ i ω) n) P)
    (hzint1 : Integrable (fun ω => saaValue f X (fun i => ξ i ω) (n + 1)) P)
    (hzmeas : Measurable (fun s : ℕ → Ξ => saaValue f X s n)) :
    (∫ ω, saaValue f X (fun i => ξ i ω) n ∂P ≤
        ∫ ω, saaValue f X (fun i => ξ i ω) (n + 1) ∂P) ∧
      ∫ ω, saaValue f X (fun i => ξ i ω) (n + 1) ∂P ≤ optValue μ f X := by
  obtain ⟨xs, hxsX, hxs⟩ := hopt
  have hξ' := hξ
  obtain ⟨hm, _, hlaw⟩ := hξ'
  have hpm : Measurable (fun ω i => ξ i ω) := measurable_pi_lambda _ hm
  have hminP : ∀ᵐ ω ∂P, ∀ m, 1 ≤ m →
      ∃ x ∈ X, ∀ y ∈ X, sampleMean f (fun i => ξ i ω) m x ≤ sampleMean f (fun i => ξ i ω) m y :=
    ae_of_ae_map hpm.aemeasurable hmin
  have hint_i : ∀ x ∈ X, ∀ i, Integrable (fun ω => f x (ξ i ω)) P := by
    intro x hx i
    have : Integrable (f x) (P.map (ξ i)) := by rw [hlaw i]; exact hint x hx
    exact this.comp_measurable (hm i)
  have hE : ∀ x ∈ X, ∀ i, ∫ ω, f x (ξ i ω) ∂P = expectedCost μ f x := by
    intro x hx i
    unfold expectedCost
    rw [← hlaw i, integral_map (hm i).aemeasurable]
    rw [hlaw i]
    exact (hint x hx).aestronglyMeasurable
  have hSMint : Integrable (fun ω => sampleMean f (fun i => ξ i ω) (n + 1) xs) P := by
    unfold sampleMean
    exact (integrable_finsetSum _ fun i _ => hint_i xs hxsX i).const_mul _
  have hSM : ∫ ω, sampleMean f (fun i => ξ i ω) (n + 1) xs ∂P = expectedCost μ f xs := by
    show ∫ ω, (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i ∈ Finset.range (n + 1), f xs (ξ i ω) ∂P = _
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => hint_i xs hxsX i)]
    simp only [hE xs hxsX, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hopt_eq : optValue μ f X = expectedCost μ f xs := by
    unfold optValue
    apply le_antisymm
    · exact csInf_le ⟨expectedCost μ f xs, by rintro _ ⟨y, hy, rfl⟩; exact hxs y hy⟩
        ⟨xs, hxsX, rfl⟩
    · exact le_csInf ⟨_, xs, hxsX, rfl⟩ (by rintro _ ⟨y, hy, rfl⟩; exact hxs y hy)
  have hz_le : ∀ᵐ ω ∂P, saaValue f X (fun i => ξ i ω) (n + 1) ≤
      sampleMean f (fun i => ξ i ω) (n + 1) xs := by
    filter_upwards [hminP] with ω hω
    exact MCBLowerAux.saa_le f X _ _ (hω (n + 1) (by omega)) hxsX
  refine ⟨?_, ?_⟩
  swap
  · rw [hopt_eq, ← hSM]
    exact integral_mono_ae hzint1 hSMint hz_le
  -- first inequality: leave-one-out averaging and exchangeability
  have hlawi : ∀ i, P.map (fun ω j => ξ (skipIndex i j) ω) = pathLaw P ξ := fun i =>
    MCBLowerAux.path_law_precomp μ P ξ hξ (skipIndex i) (MCBLowerAux.skipIndex_injective i)
  have hpmi : ∀ i, Measurable (fun ω j => ξ (skipIndex i j) ω) := fun i =>
    measurable_pi_lambda _ (fun j => hm (skipIndex i j))
  have hZL : Integrable (fun s : ℕ → Ξ => saaValue f X s n) (pathLaw P ξ) :=
    (integrable_map_measure hzmeas.aestronglyMeasurable hpm.aemeasurable).mpr hzint
  have hLint : ∀ i, Integrable (fun ω => saaValue f X (fun j => ξ (skipIndex i j) ω) n) P := by
    intro i
    have h := (integrable_map_measure (μ := P) hzmeas.aestronglyMeasurable
      (hpmi i).aemeasurable).mp (by rw [hlawi i]; exact hZL)
    exact h
  have hLeq : ∀ i, ∫ ω, saaValue f X (fun j => ξ (skipIndex i j) ω) n ∂P =
      ∫ ω, saaValue f X (fun i => ξ i ω) n ∂P := by
    intro i
    have e1 := integral_map (μ := P) (hpmi i).aemeasurable
      (f := fun s : ℕ → Ξ => saaValue f X s n) hzmeas.aestronglyMeasurable
    have e2 := integral_map (μ := P) hpm.aemeasurable
      (f := fun s : ℕ → Ξ => saaValue f X s n) hzmeas.aestronglyMeasurable
    rw [hlawi i] at e1
    unfold pathLaw at e1
    rw [← e1, e2]
  have hminLi : ∀ᵐ ω ∂P, ∀ i, ∀ m, 1 ≤ m → ∃ x ∈ X, ∀ y ∈ X,
      sampleMean f (fun j => ξ (skipIndex i j) ω) m x ≤
        sampleMean f (fun j => ξ (skipIndex i j) ω) m y := by
    rw [ae_all_iff]
    intro i
    exact ae_of_ae_map (hpmi i).aemeasurable (by rw [hlawi i]; exact hmin)
  have hlow : ∀ᵐ ω ∂P, (1 / ((n : ℝ) + 1)) * ∑ i ∈ Finset.range (n + 1),
      saaValue f X (fun j => ξ (skipIndex i j) ω) n ≤
        saaValue f X (fun i => ξ i ω) (n + 1) := by
    filter_upwards [hminLi] with ω hω
    show _ ≤ sInf ((fun x => sampleMean f (fun i => ξ i ω) (n + 1) x) '' X)
    refine le_csInf ⟨_, xs, hxsX, rfl⟩ ?_
    rintro _ ⟨x, hx, rfl⟩
    show _ ≤ sampleMean f (fun i => ξ i ω) (n + 1) x
    rw [MCBLowerAux.mean_identity f _ n hn x]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum fun i _ => MCBLowerAux.saa_le f X _ n (hω i n hn) hx
  have hLHSint : Integrable (fun ω => (1 / ((n : ℝ) + 1)) * ∑ i ∈ Finset.range (n + 1),
      saaValue f X (fun j => ξ (skipIndex i j) ω) n) P :=
    (integrable_finsetSum _ fun i _ => hLint i).const_mul _
  have hmono := integral_mono_ae hLHSint hzint1 hlow
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hLint i)] at hmono
  simp only [hLeq, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hmono
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast at hmono
  rw [← mul_assoc, one_div_mul_cancel hn1, one_mul] at hmono
  exact hmono
