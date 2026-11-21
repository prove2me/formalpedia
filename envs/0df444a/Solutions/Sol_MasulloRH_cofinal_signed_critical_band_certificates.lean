-- Prove2me | solution 1 for MasulloRH.cofinal_signed_critical_band_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pragyan
-- created : 2026-11-21T04:00:51.380486+00:00
-- url     : https://prove2.me/submissions/f439f62b-9b59-4b18-9121-71ebbb7f5b68
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_unit_height_signed_critical_band_certificates
import Theorems.Thm_MasulloRH_critical_zero_band_of_signed_brackets
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Mathlib

open MasulloRH Set Finset Filter Topology

private theorem multiplicity_pos (ρ : ZetaZerosInTraceStrip (1/2)) :
    0 < analyticOrderNatAt riemannZeta ρ.val := by
  have h1 : ρ.val ≠ 1 := fun h => by
    have hr := congrArg Complex.re h
    simp only [Complex.one_re] at hr
    linarith [ρ.prop.2.2.1]
  have hA := analyticOn_riemannZeta
  have htwo : analyticOrderAt riemannZeta 2 = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
  have hfin := hA.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1:ℂ)).isPreconnected
    (show (2:ℂ) ∈ ({1}:Set ℂ)ᶜ by norm_num) h1 (htwo ▸ ENat.zero_ne_top)
  apply Nat.pos_of_ne_zero
  unfold analyticOrderNatAt
  exact fun h => (ENat.toNat_eq_zero.mp h).elim
    ((hA _ h1).analyticOrderAt_ne_zero.mpr ρ.prop.1) hfin

private theorem finite_zeros_to_height (H : ℝ) (hH : 0 ≤ H) :
    {z : ZetaZerosInTraceStrip (1/2) | |z.val.im| ≤ H}.Finite := by
  let w := zeroDecayWeight (1/2)
  have hlim : Tendsto w cofinite (𝓝 0) := (weighted_zero_summability (1/2) (by norm_num)).tendsto_cofinite_zero
  have he := hlim.eventually (gt_mem_nhds (show (0:ℝ) < 1/(1+H^2) by positivity))
  have hbad : {z | ¬ w z < 1/(1+H^2)}.Finite := by
    simpa only [eventually_cofinite] using he
  apply hbad.subset
  intro z hz
  change |z.val.im| ≤ H at hz
  change ¬w z < 1/(1+H^2)
  apply not_lt.mpr
  have hysq : z.val.im^2 ≤ H^2 := by nlinarith [sq_abs z.val.im,mul_self_le_mul_self (abs_nonneg _) hz]
  have hm : (1:ℝ) ≤ analyticOrderNatAt riemannZeta z.val := by exact_mod_cast multiplicity_pos z
  exact (one_div_le_one_div_of_le (by positivity) (by linarith only [hysq])).trans
    (div_le_div_of_nonneg_right hm (by positivity))

private theorem positive_band_zero_on_line (z : ZetaZerosInTraceStrip (1/2))
    (hz : 100000 < z.val.im) : z.val.re = 1/2 := by
  let d : ℝ := z.val.im-100000
  have hd : 0 < d := by dsimp [d]; linarith
  let n : ℕ := Nat.ceil d - 1
  have hn : 1 ≤ Nat.ceil d := Nat.one_le_ceil_iff.mpr hd
  have hnlower : (n:ℝ) < d := Nat.add_one_le_ceil_iff.mp (by dsimp [n]; omega)
  have hncast : (n:ℝ)+1 = (Nat.ceil d : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel hn : (Nat.ceil d-1)+1=Nat.ceil d)
  have hnupper : d ≤ (n:ℝ)+1 := by rw [hncast]; exact Nat.le_ceil d
  obtain ⟨E,B,hE,hB,hD,hED,hcount⟩ := unit_height_signed_critical_band_certificates n
  have h := critical_zero_band_of_signed_brackets ((100000:ℝ)+n) ((100000:ℝ)+n+1)
    E B hE hB hD hED hcount
  apply h z
  · rw [abs_of_pos (by linarith : 0 < z.val.im)]
    dsimp [d] at hnlower
    linarith
  · rw [abs_of_pos (by linarith : 0 < z.val.im)]
    dsimp [d] at hnupper
    linarith

open Set Finset

theorem solution (T : ℕ) :
    ∃ H : ℕ, T ≤ H ∧ ∃ (E : Finset (ZetaZerosInTraceStrip (1/2))) (B : Finset (ℚ×ℚ)),
      (∀ z ∈ E, 100000 < z.val.im ∧ z.val.im ≤ (H:ℝ) ∧ z.val.re=1/2) ∧
      (∀ i ∈ B, 100000 ≤ (i.1:ℝ) ∧ i.1 < i.2 ∧ (i.2:ℝ) ≤ H ∧
        (completedRiemannZeta (1/2+(i.1:ℂ)*Complex.I)).re * (completedRiemannZeta (1/2+(i.2:ℂ)*Complex.I)).re < 0) ∧
      (∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (Set.Ioo (i.1:ℝ) (i.2:ℝ)) (Set.Ioo (j.1:ℝ) (j.2:ℝ))) ∧
      (∀ z ∈ E, ∀ i ∈ B, z.val.im ∉ Set.Ioo (i.1:ℝ) (i.2:ℝ)) ∧
      Set.encard {z : ZetaZerosInTraceStrip (1/2) | 100000<z.val.im ∧ z.val.im ≤ H} ≤ ((E.card+B.card+1:ℕ):ℕ∞)  := by
  classical
  let H : ℕ := max T 100000
  let Z : Set (ZetaZerosInTraceStrip (1/2)) :=
    {z | 100000 < z.val.im ∧ z.val.im ≤ (H:ℝ)}
  have hfin : Z.Finite := (finite_zeros_to_height (H:ℝ) (Nat.cast_nonneg H)).subset (by
    intro z hz
    change 100000 < z.val.im ∧ z.val.im ≤ (H:ℝ) at hz
    change |z.val.im| ≤ (H:ℝ)
    rw [abs_of_pos (by linarith [hz.1] : 0 < z.val.im)]
    exact hz.2)
  let E := hfin.toFinset
  refine ⟨H, le_max_left _ _, E, ∅, ?_, by simp, by simp, by simp, ?_⟩
  · intro z hz
    have h : z ∈ Z := (hfin.mem_toFinset).mp hz
    exact ⟨h.1, h.2, positive_band_zero_on_line z h.1⟩
  · change Set.encard Z ≤ ((E.card + (∅ : Finset (ℚ×ℚ)).card + 1 : ℕ):ℕ∞)
    rw [hfin.encard_eq_coe_toFinset_card]
    simp only [Finset.card_empty, Nat.add_zero]
    exact_mod_cast (Nat.le_succ E.card)


