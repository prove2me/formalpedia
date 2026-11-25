-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.cloud_pair_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:57.270212+00:00
-- url     : https://prove2.me/submissions/1305bed3-48e8-4a0b-b2c2-026c667d12cf

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_PairOKOfInterlace
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_InterlacingGrids_CloudPair
import Theorems.Thm_GroundTheory_BlockD_FourierDecayAlt_WaveGridLiftGrid_cloud_pair_factor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.BlockD GroundTheory.BlockD.FourierDecayAlt GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
open Finset
namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
theorem _root_.solution (k : ℕ) (lam v : ℕ → ℝ) (e : ℕ) (c g b Y ε : ℝ) (hk : 2 ≤ k) (hc : 0 ≤ c) (hg : 1 + c ≤ g)
    (hε : ε = 0 ∨ ε = 1) (hcb : c + 1 ≤ b) (hY : |Y| ≤ b)
    (hlam : ∀ s, 1 ≤ s → s ≤ k - 1 → |lam s| ≤ b)
    (hgap : ∀ s, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + g ≤ lam s)
    (hp : PairOK k lam v e (-Y)) (hden : ∀ i, 1 ≤ i → i ≤ k → 1 ≤ |Y + 1 / 2 + v i|) :
    ∏ s ∈ Icc 1 (k - 1), (|Y + ε + lam s| + c) ≤
      3 * b * (∏ s ∈ Icc 1 (k - 1), (1 + (1 + c) / max |Y + lam s| 1)) *
        ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| := by
  let φ : ℕ → ℕ := fun s => if 0 < Y + lam s then s else s + 1
  have hF1 : ∀ s, 1 ≤ (1 + (1 + c) / max |Y + lam s| 1) := fun s => by
    have : 0 ≤ (1 + c) / max |Y + lam s| 1 :=
      div_nonneg (by linarith) (le_trans zero_le_one (le_max_right _ _))
    linarith
  have hA0 : ∀ s, 0 ≤ |Y + ε + lam s| + c := fun s => by positivity
  have hD0 : ∀ i, 0 ≤ |Y + 1 / 2 + v i| := fun i => abs_nonneg _
  have hε1 : |ε| ≤ 1 := by rcases hε with h | h <;> simp [h]
  have hmaps : ∀ s ∈ ((Icc 1 (k - 1)).erase e), φ s ∈ Icc 1 k := by
    intro s hs
    rw [Finset.mem_erase, Finset.mem_Icc] at hs
    rw [Finset.mem_Icc]
    by_cases hpos : 0 < Y + lam s
    · simp only [φ, hpos, if_true]
      omega
    · simp only [φ, hpos, if_false]
      omega
  have hkey : ∀ s ∈ ((Icc 1 (k - 1)).erase e),
      |Y + ε + lam s| + c ≤ (1 + (1 + c) / max |Y + lam s| 1) * |Y + 1 / 2 + v (φ s)| := by
    intro s hs
    have hs' := hs
    rw [Finset.mem_erase, Finset.mem_Icc] at hs'
    obtain ⟨hne, h1, h2⟩ := hs'
    have hPs := hp s h1 h2 hne
    have hmem := hmaps s hs
    rw [Finset.mem_Icc] at hmem
    apply cloud_pair_factor _ _ _ _ hc
    · have h3 : |Y + ε + lam s| ≤ |Y + lam s| + |ε| := by
        have h4 : Y + ε + lam s = (Y + lam s) + ε := by ring
        rw [h4]
        exact abs_add_le _ _
      linarith
    · by_cases hpos : 0 < Y + lam s
      · simp only [φ, hpos, if_true]
        have hv := hPs.1 (by linarith)
        rw [abs_of_pos hpos]
        calc Y + lam s ≤ Y + 1 / 2 + v s := by linarith
          _ ≤ |Y + 1 / 2 + v s| := le_abs_self _
      · simp only [φ, hpos, if_false]
        have hv := hPs.2 (by linarith)
        rw [abs_of_nonpos (not_lt.1 hpos)]
        calc -(Y + lam s) ≤ -(Y + 1 / 2 + v (s + 1)) := by linarith
          _ ≤ |Y + 1 / 2 + v (s + 1)| := neg_le_abs _
    · exact hden _ hmem.1 hmem.2
  have hinj : ∀ s ∈ ((Icc 1 (k - 1)).erase e), ∀ t ∈ ((Icc 1 (k - 1)).erase e), φ s = φ t → s = t := by
    intro s hs t ht hst
    rw [Finset.mem_erase, Finset.mem_Icc] at hs ht
    by_cases h1 : 0 < Y + lam s <;> by_cases h2 : 0 < Y + lam t
    · simpa [φ, h1, h2] using hst
    · simp only [φ, h1, h2, if_true, if_false] at hst
      exfalso
      have hg := hgap t ht.2.1 (by omega)
      subst hst
      linarith [not_lt.1 h2]
    · simp only [φ, h1, h2, if_true, if_false] at hst
      exfalso
      have hg := hgap s hs.2.1 (by omega)
      subst hst
      linarith [not_lt.1 h1]
    · simp only [φ, h1, h2, if_false] at hst
      omega
  have hFnn : ∀ s, 0 ≤ (1 + (1 + c) / max |Y + lam s| 1) := fun s => le_trans zero_le_one (hF1 s)
  have hprodA : ∏ s ∈ ((Icc 1 (k - 1)).erase e), (|Y + ε + lam s| + c) ≤
      (∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1)) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| := by
    calc ∏ s ∈ ((Icc 1 (k - 1)).erase e), (|Y + ε + lam s| + c)
        ≤ ∏ s ∈ ((Icc 1 (k - 1)).erase e), ((1 + (1 + c) / max |Y + lam s| 1) * |Y + 1 / 2 + v (φ s)|) :=
          Finset.prod_le_prod (fun s _ => hA0 s) hkey
      _ = (∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1)) * ∏ s ∈ ((Icc 1 (k - 1)).erase e), |Y + 1 / 2 + v (φ s)| :=
          Finset.prod_mul_distrib
      _ = (∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1)) * ∏ i ∈ ((Icc 1 (k - 1)).erase e).image φ, |Y + 1 / 2 + v i| := by
          rw [Finset.prod_image hinj]
      _ ≤ (∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1)) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| := by
          apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun s _ => hFnn s)
          have hsub : ((Icc 1 (k - 1)).erase e).image φ ⊆ Icc 1 k := fun i hi => by
            obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hi
            exact hmaps s hs
          rw [← Finset.prod_sdiff hsub]
          have h1 : 1 ≤ ∏ i ∈ Icc 1 k \ ((Icc 1 (k - 1)).erase e).image φ, |Y + 1 / 2 + v i| := by
            have h5 := Finset.prod_le_prod (s := Icc 1 k \ ((Icc 1 (k - 1)).erase e).image φ) (f := fun _ => (1 : ℝ))
              (g := fun i => |Y + 1 / 2 + v i|) (fun _ _ => zero_le_one) (fun i hi => by
                have hi' := (Finset.mem_Icc.1 (Finset.mem_sdiff.1 hi).1)
                exact hden i hi'.1 hi'.2)
            simpa using h5
          have h0 : 0 ≤ ∏ i ∈ ((Icc 1 (k - 1)).erase e).image φ, |Y + 1 / 2 + v i| := Finset.prod_nonneg fun i _ => hD0 i
          nlinarith
  have hFS : ∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1) ≤ ∏ s ∈ (Icc 1 (k - 1)), (1 + (1 + c) / max |Y + lam s| 1) := by
    by_cases he : e ∈ (Icc 1 (k - 1))
    · rw [← Finset.mul_prod_erase _ _ he]
      have h0 : 0 ≤ ∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1) := Finset.prod_nonneg fun s _ => hFnn s
      nlinarith [hF1 e]
    · rw [Finset.erase_eq_of_notMem he]
  have hDnn : 0 ≤ ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| := Finset.prod_nonneg fun i _ => hD0 i
  have hFSnn : 0 ≤ ∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1) := Finset.prod_nonneg fun s _ => hFnn s
  have hb1 : 1 ≤ b := by linarith
  by_cases he : e ∈ (Icc 1 (k - 1))
  · rw [← Finset.mul_prod_erase _ _ he]
    have hAe : |Y + ε + lam e| + c ≤ 3 * b := by
      rw [Finset.mem_Icc] at he
      have hl := hlam e he.1 he.2
      have h6 : |Y + ε + lam e| ≤ |Y| + |ε| + |lam e| := abs_add_three Y ε (lam e)
      linarith
    have hAnn : 0 ≤ ∏ s ∈ ((Icc 1 (k - 1)).erase e), (|Y + ε + lam s| + c) := Finset.prod_nonneg fun s _ => hA0 s
    calc (|Y + ε + lam e| + c) * ∏ s ∈ ((Icc 1 (k - 1)).erase e), (|Y + ε + lam s| + c)
        ≤ 3 * b * ((∏ s ∈ ((Icc 1 (k - 1)).erase e), (1 + (1 + c) / max |Y + lam s| 1)) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i|) :=
          mul_le_mul hAe hprodA hAnn (by linarith)
      _ ≤ 3 * b * (∏ s ∈ (Icc 1 (k - 1)), (1 + (1 + c) / max |Y + lam s| 1)) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| := by
          linarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hFS hDnn)
            (show (0 : ℝ) ≤ 3 * b by linarith)]
  · rw [Finset.erase_eq_of_notMem he] at hprodA
    have hX : 0 ≤ (∏ s ∈ (Icc 1 (k - 1)), (1 + (1 + c) / max |Y + lam s| 1)) * ∏ i ∈ Icc 1 k, |Y + 1 / 2 + v i| :=
      mul_nonneg (Finset.prod_nonneg fun s _ => hFnn s) hDnn
    linarith [mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 3 * b by linarith) hX]
end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
