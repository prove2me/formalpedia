-- Prove2me | solution 1 for MultiwayCut.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:16:25.682249+00:00
-- url     : https://prove2.me/submissions/56de9885-4ca1-4eff-a734-288b980e9092

import Mathlib
import Definitions.Def_MultiwayCut_CKR

open MeasureTheory

namespace Aux_MultiwayCut_lemma_2_2

open MultiwayCut

/-- Description of the CKR output: either a minimal admissible index, or the last terminal. -/
theorem ckr_spec {k : ℕ} [NeZero k] (r : ℝ) (σ : Equiv.Perm (Fin k)) (w : Fin k → ℝ) :
    (∃ m : Fin k, m.val < k - 1 ∧ r ≤ w (σ m) ∧
        (∀ m' : Fin k, m'.val < k - 1 → r ≤ w (σ m') → m ≤ m') ∧ ckr r σ w = σ m) ∨
      ((∀ m : Fin k, m.val < k - 1 → w (σ m) < r) ∧
        ckr r σ w = σ ⟨k - 1, Nat.sub_one_lt (NeZero.ne k)⟩) := by
  simp only [ckr]
  split_ifs with h
  · left
    have hm := Finset.min'_mem _ h
    rw [Finset.mem_filter] at hm
    refine ⟨_, hm.2.1, hm.2.2, fun m' hm' hr => Finset.min'_le _ _ ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm', hr⟩
  · right
    refine ⟨fun m hm => ?_, rfl⟩
    by_contra hlt
    exact h ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm, not_lt.mp hlt⟩⟩

theorem first_of_min {k : ℕ} (r : ℝ) (σ : Equiv.Perm (Fin k)) (w : Fin k → ℝ)
    (hw : Antitone w) (m : Fin k) (hmk : m.val < k - 1)
    (hmin : ∀ m' : Fin k, m'.val < k - 1 → r ≤ w (σ m') → m ≤ m') (hr : r ≤ w (σ m)) :
    ∀ ℓ' : Fin k, ℓ' < σ m → σ.symm (σ m) < σ.symm ℓ' := by
  intro ℓ' hℓ'
  rw [Equiv.symm_apply_apply]
  by_contra hle
  push_neg at hle
  have hne : σ.symm ℓ' ≠ m := by
    intro h
    have : ℓ' = σ m := by rw [← h, Equiv.apply_symm_apply]
    exact absurd hℓ' (by rw [this]; exact lt_irrefl _)
  have hlt : σ.symm ℓ' < m := lt_of_le_of_ne hle hne
  have h1 : r ≤ w (σ (σ.symm ℓ')) := by
    rw [Equiv.apply_symm_apply]
    exact hr.trans (hw (le_of_lt hℓ'))
  have h2 := hmin (σ.symm ℓ') (by have := Fin.lt_def.mp hlt; omega) h1
  exact absurd hlt (not_lt.mpr h2)

theorem ioc_of {a b r : ℝ} (h1 : b < r) (h2 : r ≤ a) : r ∈ Set.Ioc (min a b) (max a b) :=
  ⟨min_lt_of_right_lt h1, le_max_of_le_left h2⟩

theorem ioc_of' {a b r : ℝ} (h1 : b < r) (h2 : r ≤ a) : r ∈ Set.Ioc (min b a) (max b a) := by
  rw [min_comm, max_comm]
  exact ioc_of h1 h2

theorem sep_sub {k : ℕ} [NeZero k] (u v : Fin k → ℝ) (hu : Antitone u) (hv : Antitone v)
    (σ : Equiv.Perm (Fin k)) (r : ℝ) (hne : ckr r σ u ≠ ckr r σ v) :
    ∃ ℓ : Fin k, (∀ ℓ' : Fin k, ℓ' < ℓ → σ.symm ℓ < σ.symm ℓ') ∧
      r ∈ Set.Ioc (min (u ℓ) (v ℓ)) (max (u ℓ) (v ℓ)) := by
  rcases ckr_spec r σ u with ⟨mu, hmu, hru, hminu, hcu⟩ | ⟨hnu, hcu⟩ <;>
    rcases ckr_spec r σ v with ⟨mv, hmv, hrv, hminv, hcv⟩ | ⟨hnv, hcv⟩
  · rcases lt_trichotomy mu mv with h | h | h
    · refine ⟨σ mu, first_of_min r σ u hu mu hmu hminu hru, ioc_of ?_ hru⟩
      by_contra hc
      exact absurd (hminv mu hmu (not_lt.mp hc)) (not_le.mpr h)
    · exact absurd (by rw [hcu, hcv, h]) hne
    · refine ⟨σ mv, first_of_min r σ v hv mv hmv hminv hrv, ioc_of' ?_ hrv⟩
      by_contra hc
      exact absurd (hminu mv hmv (not_lt.mp hc)) (not_le.mpr h)
  · exact ⟨σ mu, first_of_min r σ u hu mu hmu hminu hru, ioc_of (hnv mu hmu) hru⟩
  · exact ⟨σ mv, first_of_min r σ v hv mv hmv hminv hrv, ioc_of' (hnu mv hmv) hrv⟩
  · exact absurd (by rw [hcu, hcv]) hne

theorem perm_symm_swap {k : ℕ} (τ σ : Equiv.Perm (Fin k)) (hτ : ∀ x, τ (τ x) = x) (x : Fin k) :
    (τ * σ).symm x = σ.symm (τ x) := by
  rw [Equiv.symm_apply_eq, Equiv.Perm.mul_apply, Equiv.apply_symm_apply, hτ]

theorem swap_le {k : ℕ} (j ℓ x : Fin k) (hj : j ≤ ℓ) (hx : x ≤ ℓ) : Equiv.swap j ℓ x ≤ ℓ := by
  rw [Equiv.swap_apply_def]
  split_ifs <;> first | exact hj | exact le_refl _ | exact hx

theorem count_bound {k : ℕ} (ℓ : Fin k) :
    (ℓ.val + 1) * (Finset.univ.filter
      (fun σ : Equiv.Perm (Fin k) => ∀ ℓ' : Fin k, ℓ' < ℓ → σ.symm ℓ < σ.symm ℓ')).card ≤
      Fintype.card (Equiv.Perm (Fin k)) := by
  classical
  let A : Fin k → Finset (Equiv.Perm (Fin k)) := fun j => Finset.univ.filter
    (fun σ => ∀ ℓ' : Fin k, ℓ' ≤ ℓ → ℓ' ≠ j → σ.symm j < σ.symm ℓ')
  have hAℓ : (Finset.univ.filter
      (fun σ : Equiv.Perm (Fin k) => ∀ ℓ' : Fin k, ℓ' < ℓ → σ.symm ℓ < σ.symm ℓ')) = A ℓ := by
    apply Finset.filter_congr
    intro σ _
    constructor
    · intro h ℓ' h1 h2
      exact h ℓ' (lt_of_le_of_ne h1 h2)
    · intro h ℓ' h1
      exact h ℓ' (le_of_lt h1) (ne_of_lt h1)
  have hcard : ∀ j ∈ Finset.Iic ℓ, (A j).card = (A ℓ).card := by
    intro j hj
    rw [Finset.mem_Iic] at hj
    have hτ : ∀ x, Equiv.swap j ℓ (Equiv.swap j ℓ x) = x := Equiv.swap_apply_self j ℓ
    apply Finset.card_nbij' (fun σ => Equiv.swap j ℓ * σ) (fun σ => Equiv.swap j ℓ * σ)
    · intro σ hσ
      have hσ' := (Finset.mem_filter.mp (Finset.mem_coe.mp hσ)).2
      apply Finset.mem_coe.mpr
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro ℓ' h1 h2
      show (Equiv.swap j ℓ * σ).symm ℓ < (Equiv.swap j ℓ * σ).symm ℓ'
      rw [perm_symm_swap _ _ hτ, perm_symm_swap _ _ hτ, Equiv.swap_apply_right]
      refine hσ' _ (swap_le j ℓ ℓ' hj h1) ?_
      intro h
      apply h2
      have := congrArg (Equiv.swap j ℓ) h
      rw [hτ, Equiv.swap_apply_left] at this
      exact this
    · intro σ hσ
      have hσ' := (Finset.mem_filter.mp (Finset.mem_coe.mp hσ)).2
      apply Finset.mem_coe.mpr
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro ℓ' h1 h2
      show (Equiv.swap j ℓ * σ).symm j < (Equiv.swap j ℓ * σ).symm ℓ'
      rw [perm_symm_swap _ _ hτ, perm_symm_swap _ _ hτ, Equiv.swap_apply_left]
      refine hσ' _ (swap_le j ℓ ℓ' hj h1) ?_
      intro h
      apply h2
      have := congrArg (Equiv.swap j ℓ) h
      rw [hτ, Equiv.swap_apply_right] at this
      exact this
    · intro σ _
      exact Equiv.swap_mul_self_mul j ℓ σ
    · intro σ _
      exact Equiv.swap_mul_self_mul j ℓ σ
  have hdisj : (↑(Finset.Iic ℓ) : Set (Fin k)).PairwiseDisjoint A := by
    intro x hxm y hym hxy
    have hxl : x ≤ ℓ := Finset.mem_Iic.mp (Finset.mem_coe.mp hxm)
    have hyl : y ≤ ℓ := Finset.mem_Iic.mp (Finset.mem_coe.mp hym)
    show Disjoint (A x) (A y)
    apply Finset.disjoint_left.mpr
    intro σ hx hy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    have h1 := hx' y hyl (Ne.symm hxy)
    have h2 := hy' x hxl hxy
    exact absurd h1 (not_lt.mpr (le_of_lt h2))
  have hsum : ∑ j ∈ Finset.Iic ℓ, (A j).card = (ℓ.val + 1) * (A ℓ).card := by
    rw [Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul, Fin.card_Iic]
  rw [hAℓ, ← hsum, ← Finset.card_biUnion hdisj]
  exact Finset.card_le_univ _

end Aux_MultiwayCut_lemma_2_2

open MultiwayCut Aux_MultiwayCut_lemma_2_2 in
theorem solution {k : ℕ} [NeZero k] (u v : Fin k → ℝ) (hu : ∀ ℓ, u ℓ ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ ℓ, v ℓ ∈ Set.Icc (0 : ℝ) 1) (hu_anti : Antitone u) (hv_anti : Antitone v) :
    sepCKR u v ≤ ∑ ℓ : Fin k, |u ℓ - v ℓ| / ((ℓ.val : ℝ) + 1) := by
  classical
  let G : Equiv.Perm (Fin k) → Fin k → Prop :=
    fun σ ℓ => ∀ ℓ' : Fin k, ℓ' < ℓ → σ.symm ℓ < σ.symm ℓ'
  have hNpos : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin k)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have key1 : ∀ σ : Equiv.Perm (Fin k),
      (volume {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ ckr r σ u ≠ ckr r σ v}).toReal ≤
        ∑ ℓ ∈ Finset.univ.filter (G σ), |u ℓ - v ℓ| := by
    intro σ
    have hsub : {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ ckr r σ u ≠ ckr r σ v} ⊆
        ⋃ ℓ ∈ Finset.univ.filter (G σ), Set.Ioc (min (u ℓ) (v ℓ)) (max (u ℓ) (v ℓ)) := by
      intro r hr
      obtain ⟨_, hne⟩ := hr
      obtain ⟨ℓ, hG, hI⟩ := sep_sub u v hu_anti hv_anti σ r hne
      exact Set.mem_iUnion₂.mpr ⟨ℓ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG⟩, hI⟩
    have hle : volume {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ ckr r σ u ≠ ckr r σ v} ≤
        ∑ ℓ ∈ Finset.univ.filter (G σ), ENNReal.ofReal |u ℓ - v ℓ| := by
      calc volume {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ ckr r σ u ≠ ckr r σ v}
          ≤ volume (⋃ ℓ ∈ Finset.univ.filter (G σ),
              Set.Ioc (min (u ℓ) (v ℓ)) (max (u ℓ) (v ℓ))) := measure_mono hsub
        _ ≤ ∑ ℓ ∈ Finset.univ.filter (G σ),
              volume (Set.Ioc (min (u ℓ) (v ℓ)) (max (u ℓ) (v ℓ))) :=
            measure_biUnion_finset_le _ _
        _ = ∑ ℓ ∈ Finset.univ.filter (G σ), ENNReal.ofReal |u ℓ - v ℓ| := by
            refine Finset.sum_congr rfl (fun ℓ _ => ?_)
            rw [Real.volume_Ioc, max_sub_min_eq_abs, abs_sub_comm]
    calc (volume {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ ckr r σ u ≠ ckr r σ v}).toReal
        ≤ (∑ ℓ ∈ Finset.univ.filter (G σ), ENNReal.ofReal |u ℓ - v ℓ|).toReal :=
          ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top)) hle
      _ = ∑ ℓ ∈ Finset.univ.filter (G σ), |u ℓ - v ℓ| := by
          rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
          exact Finset.sum_congr rfl (fun ℓ _ => ENNReal.toReal_ofReal (abs_nonneg _))
  have key2 : ∀ ℓ : Fin k,
      ((Finset.univ.filter (fun σ => G σ ℓ)).card : ℝ) * ((ℓ.val : ℝ) + 1) ≤
        (Fintype.card (Equiv.Perm (Fin k)) : ℝ) := by
    intro ℓ
    have := count_bound ℓ
    have h2 : ((ℓ.val + 1) * (Finset.univ.filter (fun σ => G σ ℓ)).card : ℕ) ≤
        Fintype.card (Equiv.Perm (Fin k)) := by
      convert this using 3
    have h3 : (((ℓ.val + 1) * (Finset.univ.filter (fun σ => G σ ℓ)).card : ℕ) : ℝ) ≤
        (Fintype.card (Equiv.Perm (Fin k)) : ℝ) := by exact_mod_cast h2
    push_cast at h3
    nlinarith [h3]
  have hswap : ∑ σ : Equiv.Perm (Fin k), ∑ ℓ ∈ Finset.univ.filter (G σ), |u ℓ - v ℓ| =
      ∑ ℓ : Fin k, |u ℓ - v ℓ| * ((Finset.univ.filter (fun σ => G σ ℓ)).card : ℝ) := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  unfold sepCKR ckrProb
  calc (∑ σ : Equiv.Perm (Fin k),
        (volume {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ ckr r σ u ≠ ckr r σ v}).toReal) /
        (Fintype.card (Equiv.Perm (Fin k)) : ℝ)
      ≤ (∑ σ : Equiv.Perm (Fin k), ∑ ℓ ∈ Finset.univ.filter (G σ), |u ℓ - v ℓ|) /
        (Fintype.card (Equiv.Perm (Fin k)) : ℝ) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hNpos)
        exact Finset.sum_le_sum (fun σ _ => key1 σ)
    _ = ∑ ℓ : Fin k, |u ℓ - v ℓ| * ((Finset.univ.filter (fun σ => G σ ℓ)).card : ℝ) /
        (Fintype.card (Equiv.Perm (Fin k)) : ℝ) := by
        rw [hswap, Finset.sum_div]
    _ ≤ ∑ ℓ : Fin k, |u ℓ - v ℓ| / ((ℓ.val : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro ℓ _
        have hpos : (0 : ℝ) < (ℓ.val : ℝ) + 1 := by positivity
        rw [div_le_div_iff₀ hNpos hpos]
        have := mul_le_mul_of_nonneg_left (key2 ℓ) (abs_nonneg (u ℓ - v ℓ))
        nlinarith [this]
