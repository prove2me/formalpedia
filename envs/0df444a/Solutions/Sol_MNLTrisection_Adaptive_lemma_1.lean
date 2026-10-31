-- Prove2me | solution 1 for MNLTrisection.Adaptive.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T16:58:06.503987+00:00
-- url     : https://prove2.me/submissions/026e4bc1-8bec-4674-93ff-61045af67d50

import Mathlib
import Definitions.Def_MNLTrisection_Adaptive_Model

namespace MNLTriAux

open MNLTrisection.Adaptive MNLBandit.UCB ChoiceCDLP.MNL Filter Topology

variable {N : ℕ}

theorem rev_def (v r : Fin N → ℝ) (S : Finset (Fin N)) :
    rev v r S = (∑ j ∈ S, r j * v j) / (∑ j ∈ S, v j + 1) := by
  simp [rev, mnlObjective, mul_comm]

theorem den_pos (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N)) :
    0 < ∑ j ∈ S, v j + 1 := by
  have := Finset.sum_nonneg (fun j (_ : j ∈ S) => hv j); linarith

theorem sum_shift (v r : Fin N → ℝ) (S : Finset (Fin N)) (θ : ℝ) :
    ∑ j ∈ S, (r j - θ) * v j = ∑ j ∈ S, r j * v j - θ * ∑ j ∈ S, v j := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

theorem le_rev_iff (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N)) (θ : ℝ) :
    θ ≤ rev v r S ↔ θ ≤ ∑ j ∈ S, (r j - θ) * v j := by
  rw [rev_def, le_div_iff₀ (den_pos v hv S), sum_shift]
  constructor <;> intro h <;> linarith

theorem rev_le_iff (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N)) (θ : ℝ) :
    rev v r S ≤ θ ↔ ∑ j ∈ S, (r j - θ) * v j ≤ θ := by
  rw [rev_def, div_le_iff₀ (den_pos v hv S), sum_shift]
  constructor <;> intro h <;> linarith

theorem sum_le_level (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N)) (θ : ℝ) :
    ∑ j ∈ S, (r j - θ) * v j ≤ ∑ j ∈ levelSet r θ, (r j - θ) * v j := by
  calc ∑ j ∈ S, (r j - θ) * v j ≤ ∑ j ∈ S.filter (fun j => θ ≤ r j), (r j - θ) * v j := by
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro j _
        split_ifs with h
        · exact le_rfl
        · push Not at h
          exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hv j)
    _ ≤ ∑ j ∈ levelSet r θ, (r j - θ) * v j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [Finset.mem_filter] at hj
          simp [levelSet, hj.2]
        · intro j hj _
          simp only [levelSet, Finset.mem_filter] at hj
          exact mul_nonneg (by linarith [hj.2]) (hv j)

theorem exists_opt (v r : Fin N → ℝ) :
    ∃ S : Finset (Fin N), ∀ S' : Finset (Fin N), rev v r S' ≤ rev v r S := by
  obtain ⟨S, -, hS⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset (Fin N)))
    (rev v r) ⟨∅, Finset.mem_univ _⟩
  exact ⟨S, fun S' => hS S' (Finset.mem_univ _)⟩

theorem optRev_eq (v r : Fin N → ℝ) (S : Finset (Fin N))
    (hS : ∀ S' : Finset (Fin N), rev v r S' ≤ rev v r S) : optRev v r = rev v r S := by
  unfold optRev optRevenue
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun S' _ => hS S')
  · exact Finset.le_sup' (fun S => mnlObjective v r 1 S) (Finset.mem_univ S)

theorem rev_empty (v r : Fin N → ℝ) : rev v r ∅ = 0 := by simp [rev, mnlObjective]

theorem rev_le_optRev (v r : Fin N → ℝ) (S : Finset (Fin N)) : rev v r S ≤ optRev v r := by
  obtain ⟨S0, hS0⟩ := exists_opt v r
  rw [optRev_eq v r S0 hS0]; exact hS0 S

theorem optRev_nonneg (v r : Fin N → ℝ) : 0 ≤ optRev v r := by
  have := rev_le_optRev v r ∅; rwa [rev_empty] at this

/-- The optimal revenue is a fixed point of `F`. -/
theorem F_optRev (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) : F v r (optRev v r) = optRev v r := by
  obtain ⟨S0, hS0⟩ := exists_opt v r
  have hR := optRev_eq v r S0 hS0
  apply le_antisymm (rev_le_optRev v r _)
  show optRev v r ≤ rev v r (levelSet r (optRev v r))
  rw [le_rev_iff v r hv]
  have h1 : optRev v r ≤ rev v r S0 := hR.le
  rw [le_rev_iff v r hv] at h1
  exact h1.trans (sum_le_level v r hv S0 _)

theorem Fstar_eq (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) : Fstar v r = optRev v r := by
  unfold Fstar
  apply IsGreatest.csSup_eq
  refine ⟨⟨optRev v r, optRev_nonneg v r, F_optRev v r hv⟩, ?_⟩
  rintro _ ⟨θ, -, rfl⟩
  exact rev_le_optRev v r _

theorem thetaStar_eq (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) : thetaStar v r = optRev v r :=
  Fstar_eq v r hv

theorem sum_filter_split (r g : Fin N → ℝ) (θ : ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i => θ ≤ r i), g i =
      ∑ i ∈ Finset.univ.filter (fun i => θ < r i), g i +
        ∑ i ∈ Finset.univ.filter (fun i => r i = θ), g i := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases lt_trichotomy θ (r i) with h | h | h
  · simp [h, h.le, h.ne']
  · simp [h]
  · simp [not_le.mpr h, not_lt.mpr h.le, h.ne]

theorem rightLim_F (v r : Fin N → ℝ) (θ : ℝ) :
    Function.rightLim (F v r) θ = rev v r (Finset.univ.filter (fun i => θ < r i)) := by
  apply rightLim_eq_of_tendsto
  have key : ∀ i : Fin N, ∀ᶠ y in 𝓝[>] θ, (y ≤ r i ↔ θ < r i) := by
    intro i
    by_cases h : θ < r i
    · have : ∀ᶠ y in 𝓝[>] θ, y < r i := nhdsWithin_le_nhds (Iio_mem_nhds h)
      filter_upwards [this] with y hy
      exact ⟨fun _ => h, fun _ => hy.le⟩
    · push Not at h
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy' : θ < y := hy
      exact ⟨fun h' => by linarith, fun h' => by linarith⟩
  have hall := Filter.eventually_all.2 key
  apply tendsto_const_nhds.congr'
  filter_upwards [hall] with y hy
  unfold F levelSet
  congr 1
  ext i
  simp [hy i]

theorem jump_identity (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (θ : ℝ) :
    F v r θ - rev v r (Finset.univ.filter (fun i => θ < r i)) =
      (∑ i ∈ Finset.univ.filter (fun i => r i = θ), v i) /
          (1 + ∑ i ∈ Finset.univ.filter (fun i => θ ≤ r i), v i) *
        (θ - rev v r (Finset.univ.filter (fun i => θ < r i))) := by
  unfold F levelSet
  rw [rev_def, rev_def, sum_filter_split r (fun i => r i * v i) θ,
    sum_filter_split r v θ]
  have he : ∑ i ∈ Finset.univ.filter (fun i => r i = θ), r i * v i =
      θ * ∑ i ∈ Finset.univ.filter (fun i => r i = θ), v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_filter] at hi
    rw [hi.2]
  rw [he]
  set A := ∑ i ∈ Finset.univ.filter (fun i => θ < r i), r i * v i
  set B := ∑ i ∈ Finset.univ.filter (fun i => θ < r i), v i
  set V := ∑ i ∈ Finset.univ.filter (fun i => r i = θ), v i
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => hv i)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun i _ => hv i)
  have h1 : (B + 1) ≠ 0 := by positivity
  have h2 : (B + V + 1) ≠ 0 := by positivity
  have h3 : (1 + (B + V)) ≠ 0 := by positivity
  field_simp
  ring

theorem jump_coef_nonneg (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (θ : ℝ) :
    0 ≤ (∑ i ∈ Finset.univ.filter (fun i => r i = θ), v i) /
          (1 + ∑ i ∈ Finset.univ.filter (fun i => θ ≤ r i), v i) := by
  apply div_nonneg (Finset.sum_nonneg (fun i _ => hv i))
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ.filter (fun i => θ ≤ r i)) => hv i)
  linarith

theorem le_F_of_le (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (θ : ℝ) (hθ : θ ≤ optRev v r) :
    θ ≤ F v r θ := by
  obtain ⟨S0, hS0⟩ := exists_opt v r
  have hR := optRev_eq v r S0 hS0
  have h1 : optRev v r ≤ rev v r S0 := hR.le
  rw [le_rev_iff v r hv] at h1
  unfold F
  rw [le_rev_iff v r hv]
  refine le_trans ?_ (sum_le_level v r hv S0 θ)
  have hsplit : ∑ j ∈ S0, (r j - θ) * v j =
      ∑ j ∈ S0, (r j - optRev v r) * v j + (optRev v r - θ) * ∑ j ∈ S0, v j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hVs : 0 ≤ ∑ j ∈ S0, v j := Finset.sum_nonneg (fun j _ => hv j)
  rw [hsplit]
  nlinarith

theorem le_rev_strict_of_le (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (θ : ℝ)
    (hθ : θ ≤ optRev v r) : θ ≤ rev v r (Finset.univ.filter (fun i => θ < r i)) := by
  have h := le_F_of_le v r hv θ hθ
  unfold F levelSet at h
  rw [le_rev_iff v r hv] at h ⊢
  rw [sum_filter_split r (fun j => (r j - θ) * v j) θ] at h
  have h0 : ∑ i ∈ Finset.univ.filter (fun i => r i = θ), (r i - θ) * v i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_filter] at hi
    simp [hi.2]
  linarith

end MNLTriAux

open MNLTrisection.Adaptive in
theorem solution {N : ℕ} (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) :
    ∃ Sstar : Finset (Fin N), (∀ S : Finset (Fin N), rev v r S ≤ rev v r Sstar) ∧
      ∃ θ : ℝ, 0 ≤ θ ∧ rev v r (levelSet r θ) = rev v r Sstar := by
  obtain ⟨S0, hS0⟩ := MNLTriAux.exists_opt v r
  refine ⟨S0, hS0, optRev v r, MNLTriAux.optRev_nonneg v r, ?_⟩
  rw [← MNLTriAux.optRev_eq v r S0 hS0]
  exact MNLTriAux.F_optRev v r hv
