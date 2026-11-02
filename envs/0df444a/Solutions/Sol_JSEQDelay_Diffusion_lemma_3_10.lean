-- Prove2me | solution 1 for JSEQDelay.Diffusion.lemma_3_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:08:47.27174+00:00
-- url     : https://prove2.me/submissions/416bffcf-adb8-4a55-9320-e885a1a11701

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_CTight
import Definitions.Def_JSEQDelay_Diffusion_Model
import Definitions.Def_JSEQDelay_Diffusion_Assumptions
import Definitions.Def_JSEQDelay_Diffusion_Example3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open BellWilliams2001.ThresholdPolicy RankBasedSDI.LoadBalancing JSEQDelay.Diffusion

namespace JSEQL310Aux

lemma tau_le {K : ℕ} {τ : ℝ → Fin K → ℝ} (hτ : DelayFunction τ) {s : ℝ} (hs : 0 ≤ s) (k : Fin K) :
    τ s k ≤ s := by
  rcases eq_or_lt_of_le hs with h0 | hpos
  · subst h0
    by_contra hc
    push Not at hc
    have hε : 0 < τ 0 k / 2 := by linarith
    have h1 := hτ.2.1 k (Set.mem_Ici.2 (le_refl (0:ℝ))) (Set.mem_Ici.2 hε.le) hε.le
    have h2 := hτ.2.2 _ hε k
    simp only at h1
    linarith
  · exact hτ.2.2 s hpos k

lemma tau_mem {K : ℕ} {τ : ℝ → Fin K → ℝ} (hτ : DelayFunction τ) {s T : ℝ} (hs : s ∈ Set.Icc 0 T)
    (k : Fin K) : τ s k ∈ Set.Icc 0 T :=
  ⟨hτ.1 s hs.1 k, (tau_le hτ hs.1 k).trans hs.2⟩

lemma psiHat_eq {K : ℕ} (n : ℕ) (hn : 1 ≤ n) (mu : Fin K → ℝ) (τ : ℝ → Fin K → ℝ)
    (h : ℝ → (Fin K → ℝ) → (Fin K → ℝ) → Fin K → ℝ) (q a : Path K) (t : ℝ) (k : Fin K) :
    PsiHat n mu (ex3Psi n mu τ h) q a t k = ex3PsiLim τ h q a t k := by
  have hs : Real.sqrt n ≠ 0 := by
    have : (0:ℝ) < n := by exact_mod_cast hn
    exact (Real.sqrt_pos.2 this).ne'
  simp only [PsiHat, ex3Psi, ex3PsiLim]
  have e1 : (fun j => Real.sqrt n * q (τ t j) j / Real.sqrt n) = fun j => q (τ t j) j := by
    funext j; field_simp
  have e2 : (fun j => (Real.sqrt n * a t j + mu j * t - (Real.sqrt n * a (τ t j) j + mu j * τ t j)
      - mu j * (t - τ t j)) / Real.sqrt n) = fun j => a t j - a (τ t j) j := by
    funext j; field_simp; ring
  rw [e1, e2]
  field_simp

lemma psiHat_zero {K : ℕ} (mu : Fin K → ℝ) (Ψ : Path K → Path K → Path K) (q a : Path K)
    (t : ℝ) (k : Fin K) : PsiHat 0 mu Ψ q a t k = 0 := by
  simp [PsiHat]


lemma scalarModulus_le {f : ℝ → ℝ} {T δ : ℝ} {C : ℝ≥0∞}
    (h : ∀ u s, u ∈ Set.Icc 0 T → s ∈ Set.Icc 0 T → |u - s| ≤ δ → ENNReal.ofReal |f u - f s| ≤ C) :
    scalarModulus f T δ ≤ C := by
  unfold scalarModulus modulus
  refine iSup₂_le fun u s => iSup_le fun hc => ?_
  simpa using h u s hc.1 hc.2.1 hc.2.2

lemma le_scalarModulus (f : ℝ → ℝ) {T δ u s : ℝ} (hu : u ∈ Set.Icc 0 T) (hs : s ∈ Set.Icc 0 T)
    (hus : |u - s| ≤ δ) : ENNReal.ofReal |f u - f s| ≤ scalarModulus f T δ := by
  unfold scalarModulus modulus
  refine le_iSup₂_of_le u s (le_iSup_of_le ⟨hu, hs, hus⟩ ?_)
  simp

lemma supDist_le {K : ℕ} {f g : ℝ → Fin K → ℝ} {T : ℝ} {C : ℝ≥0∞}
    (h : ∀ s ∈ Set.Icc 0 T, ENNReal.ofReal (∑ i, |f s i - g s i|) ≤ C) : supDist f g T ≤ C :=
  iSup₂_le h

lemma le_supDist {K : ℕ} (f g : ℝ → Fin K → ℝ) {T s : ℝ} (hs : s ∈ Set.Icc 0 T) :
    ENNReal.ofReal (∑ i, |f s i - g s i|) ≤ supDist f g T :=
  le_iSup₂ (f := fun s (_ : s ∈ Set.Icc 0 T) => ENNReal.ofReal (∑ i, |f s i - g s i|)) s hs

lemma coord_le_supDist {K : ℕ} (f g : ℝ → Fin K → ℝ) {T s : ℝ} (hs : s ∈ Set.Icc 0 T) (k : Fin K) :
    ENNReal.ofReal |f s k - g s k| ≤ supDist f g T :=
  (ENNReal.ofReal_le_ofReal (Finset.single_le_sum (f := fun i => |f s i - g s i|)
    (fun i _ => abs_nonneg _) (Finset.mem_univ k))).trans (le_supDist f g hs)

end JSEQL310Aux

open JSEQL310Aux in
theorem solution {K : ℕ} (hK : 2 ≤ K)
    (τ : ℝ → Fin K → ℝ) (hτ : DelayFunction τ) (mu : ℕ → Fin K → ℝ)
    (h : ℝ → (Fin K → ℝ) → (Fin K → ℝ) → Fin K → ℝ) (hh : Example3Uniform h) :
    Assumption35 (fun n => PsiHat n (mu n) (ex3Psi n (mu n) τ h)) (ex3PsiLim τ h) ∧
    Assumption38 τ (fun n => PsiHat n (mu n) (ex3Psi n (mu n) τ h)) ∧
    Assumption39 τ (ex3PsiLim τ h) := by
  obtain ⟨_, _, η, hη0, hη1, hκ⟩ := hh
  refine ⟨?_, ?_, ?_⟩
  · -- Assumption 3.5
    intro qn an q a hD hC hq ha T hT
    obtain ⟨κ, _, _, hκ0, _, hL⟩ := hκ T hT
    have hbound : ∀ n, 1 ≤ n →
        supDist (PsiHat n (mu n) (ex3Psi n (mu n) τ h) (qn n) (an n)) (ex3PsiLim τ h q a) T ≤
          (K : ℝ≥0∞) * (supDist (qn n) q T + supDist (an n) a T + supDist (an n) a T) := by
      intro n hn
      apply supDist_le
      intro s hs
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
      calc ∑ k, ENNReal.ofReal |PsiHat n (mu n) (ex3Psi n (mu n) τ h) (qn n) (an n) s k -
              ex3PsiLim τ h q a s k|
          ≤ ∑ _k : Fin K, (supDist (qn n) q T + supDist (an n) a T + supDist (an n) a T) := by
            apply Finset.sum_le_sum
            intro k _
            rw [psiHat_eq n hn]
            simp only [ex3PsiLim]
            have hτs := tau_mem hτ hs k
            have hL1 := hL s hs s hs (fun j => qn n (τ s j) j) (fun j => q (τ s j) j)
              (fun j => (hD n).2.2.2.2 _ (hτ.1 s hs.1 j) j)
              (fun j => hC.2.2.2.2 _ (hτ.1 s hs.1 j) j)
              (fun j => an n s j - an n (τ s j) j) (fun j => a s j - a (τ s j) j) k
            simp only [sub_self, abs_zero, hκ0, zero_add] at hL1
            have e : |an n s k - an n (τ s k) k - (a s k - a (τ s k) k)| ≤
                |an n s k - a s k| + |an n (τ s k) k - a (τ s k) k| := by
              rw [show an n s k - an n (τ s k) k - (a s k - a (τ s k) k) =
                (an n s k - a s k) - (an n (τ s k) k - a (τ s k) k) by ring]
              exact abs_sub _ _
            have hX : |h s (fun j => qn n (τ s j) j) (fun j => an n s j - an n (τ s j) j) k -
                h s (fun j => q (τ s j) j) (fun j => a s j - a (τ s j) j) k| ≤
                |qn n (τ s k) k - q (τ s k) k| + |an n s k - a s k| +
                  |an n (τ s k) k - a (τ s k) k| := by
              have := mul_le_mul_of_nonneg_left e hη0
              have h3 : η * (|an n s k - a s k| + |an n (τ s k) k - a (τ s k) k|) ≤
                  |an n s k - a s k| + |an n (τ s k) k - a (τ s k) k| := by
                have := add_nonneg (abs_nonneg (an n s k - a s k))
                  (abs_nonneg (an n (τ s k) k - a (τ s k) k))
                nlinarith
              linarith
            calc ENNReal.ofReal _ ≤ ENNReal.ofReal (|qn n (τ s k) k - q (τ s k) k| +
                  |an n s k - a s k| + |an n (τ s k) k - a (τ s k) k|) := ENNReal.ofReal_le_ofReal hX
              _ ≤ ENNReal.ofReal |qn n (τ s k) k - q (τ s k) k| + ENNReal.ofReal |an n s k - a s k| +
                  ENNReal.ofReal |an n (τ s k) k - a (τ s k) k| := by
                refine (ENNReal.ofReal_add_le).trans ?_
                gcongr
                exact ENNReal.ofReal_add_le
              _ ≤ _ := by
                gcongr
                · exact coord_le_supDist (qn n) q hτs k
                · exact coord_le_supDist (an n) a hs k
                · exact coord_le_supDist (an n) a hτs k
        _ = _ := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_add]
    have hlim : Tendsto (fun n => (K : ℝ≥0∞) *
        (supDist (qn n) q T + supDist (an n) a T + supDist (an n) a T)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (((hq T hT).add (ha T hT)).add (ha T hT))
        (Or.inr (ENNReal.natCast_ne_top K))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hbound n hn
  · -- Assumption 3.8
    classical
    let o : ℝ → ℝ → ℕ → ℝ := fun T δ _ => if hT : 0 ≤ T then (Classical.choose (hκ T hT)) δ else 0
    refine ⟨η, hη0, hη1, o, ?_, ?_⟩
    · intro n q a hqa T δ hδ hδT k
      have hT : 0 ≤ T := by linarith
      have hspec := Classical.choose_spec (hκ T hT)
      set κ := Classical.choose (hκ T hT)
      obtain ⟨hmono, _, hκ0, hκnn, hL⟩ := hspec
      have ho : o T δ n = κ δ := by simp only [o, dif_pos hT]; rfl
      rw [ho]
      apply scalarModulus_le
      intro u s hu hs hus
      simp only
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp [psiHat_zero]
      rw [psiHat_eq n hn, psiHat_eq n hn]
      simp only [ex3PsiLim]
      have hL1 := hL u hu s hs (fun j => q (τ u j) j) (fun j => q (τ s j) j)
        (fun j => hqa.2.2.2.2 _ (hτ.1 u hu.1 j) j) (fun j => hqa.2.2.2.2 _ (hτ.1 s hs.1 j) j)
        (fun j => a u j - a (τ u j) j) (fun j => a s j - a (τ s j) j) k
      have hκus : κ |u - s| ≤ κ δ := hmono ⟨abs_nonneg _, by
          rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hs.1, hs.2]⟩
        ⟨hδ.le, hδT.le⟩ hus
      have e : |a u k - a (τ u k) k - (a s k - a (τ s k) k)| ≤
          |a u k - a s k| + |a (τ u k) k - a (τ s k) k| := by
        rw [show a u k - a (τ u k) k - (a s k - a (τ s k) k) =
          (a u k - a s k) - (a (τ u k) k - a (τ s k) k) by ring]
        exact abs_sub _ _
      have hX : |h u (fun j => q (τ u j) j) (fun j => a u j - a (τ u j) j) k -
          h s (fun j => q (τ s j) j) (fun j => a s j - a (τ s j) j) k| ≤
          |q (τ u k) k - q (τ s k) k| + |a (τ u k) k - a (τ s k) k| + η * |a u k - a s k| + κ δ := by
        have h1 := mul_le_mul_of_nonneg_left e hη0
        have h2 : η * |a (τ u k) k - a (τ s k) k| ≤ |a (τ u k) k - a (τ s k) k| := by
          have := abs_nonneg (a (τ u k) k - a (τ s k) k); nlinarith
        nlinarith
      have hqm := le_scalarModulus (fun t => q (τ t k) k) hu hs hus
      have ham := le_scalarModulus (fun t => a (τ t k) k) hu hs hus
      have ha := le_scalarModulus (fun t => a t k) hu hs hus
      calc ENNReal.ofReal _ ≤ ENNReal.ofReal (|q (τ u k) k - q (τ s k) k| +
            |a (τ u k) k - a (τ s k) k| + η * |a u k - a s k| + κ δ) := ENNReal.ofReal_le_ofReal hX
        _ ≤ ENNReal.ofReal |q (τ u k) k - q (τ s k) k| + ENNReal.ofReal |a (τ u k) k - a (τ s k) k| +
            ENNReal.ofReal η * ENNReal.ofReal |a u k - a s k| + ENNReal.ofReal (κ δ) := by
          rw [← ENNReal.ofReal_mul hη0]
          refine ENNReal.ofReal_add_le.trans ?_
          gcongr
          refine ENNReal.ofReal_add_le.trans ?_
          gcongr
          exact ENNReal.ofReal_add_le
        _ ≤ _ := by
          gcongr
          exact ham.trans (le_mul_of_one_le_left bot_le (by norm_num))
    · intro T ε hT hε
      have hspec := Classical.choose_spec (hκ T hT.le)
      set κ := Classical.choose (hκ T hT.le)
      obtain ⟨_, hcont, hκ0, _, _⟩ := hspec
      have hc0 := hcont 0 ⟨le_rfl, hT.le⟩
      rw [Metric.continuousWithinAt_iff] at hc0
      obtain ⟨δ₀, hδ₀, hδc⟩ := hc0 ε hε
      refine ⟨min δ₀ T, lt_min hδ₀ hT, fun δ hδ hδlt => Eventually.of_forall fun n => ?_⟩
      have ho : o T δ n = κ δ := by simp only [o, dif_pos hT.le]; rfl
      rw [ho]
      have := @hδc δ ⟨hδ.le, (hδlt.trans_le (min_le_right _ _)).le⟩
        (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; exact hδlt.trans_le (min_le_left _ _))
      rw [Real.dist_eq, hκ0, sub_zero] at this
      exact (le_abs_self _).trans this.le
  · -- Assumption 3.9
    refine ⟨η, hη0, hη1, ?_⟩
    intro q a a' hqa hqa' t ht k
    obtain ⟨κ, _, _, hκ0, _, hL⟩ := hκ t ht.le
    have hv : ∀ j, 0 ≤ q (τ t j) j := fun j => hqa.2.2.2.2 _ (hτ.1 t ht.le j) j
    have hL1 := hL t ⟨ht.le, le_rfl⟩ t ⟨ht.le, le_rfl⟩ (fun j => q (τ t j) j) (fun j => q (τ t j) j)
      hv hv (fun j => a t j - a (τ t j) j) (fun j => a' t j - a' (τ t j) j) k
    simp only [sub_self, abs_zero, hκ0, zero_add] at hL1
    simp only [ex3PsiLim]
    calc ENNReal.ofReal _ ≤ ENNReal.ofReal (η * |a t k - a (τ t k) k - (a' t k - a' (τ t k) k)|) :=
          ENNReal.ofReal_le_ofReal hL1
      _ = ENNReal.ofReal η * ENNReal.ofReal |a t k - a (τ t k) k - (a' t k - a' (τ t k) k)| :=
          ENNReal.ofReal_mul hη0
      _ ≤ _ := by
        gcongr
        exact le_iSup₂ (f := fun s (_ : s ∈ Set.Icc (τ t k) t) =>
          ENNReal.ofReal |(a s k - a (τ t k) k) - (a' s k - a' (τ t k) k)|) t
          ⟨tau_le hτ ht.le k, le_rfl⟩
