-- Prove2me | solution 1 for MultiwayCut.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:40:42.106442+00:00
-- url     : https://prove2.me/submissions/adad4e61-c36a-4ba8-b2a0-2a6a76be337d

import Mathlib
import Definitions.Def_MultiwayCut_CKR
import Definitions.Def_MultiwayCut_CutDensity
import Definitions.Def_MultiwayCut_Transformation
import Definitions.Def_MultiwayCut_A53

open MeasureTheory Matrix

namespace Aux_MultiwayCut_lemma_5_2


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


theorem sep_bound {k : ℕ} [NeZero k] (u v : Fin k → ℝ) (hu : ∀ ℓ, u ℓ ∈ Set.Icc (0 : ℝ) 1)
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



/-- Abel summation: an antitone nonnegative weight against a sequence with nonnegative prefix
sums gives a nonnegative sum. -/
theorem abel_nonneg (g : ℕ → ℝ) : ∀ (n : ℕ) (f : ℕ → ℝ),
    (∀ i j, i ≤ j → j < n → f j ≤ f i) → (0 < n → 0 ≤ f (n - 1)) →
    (∀ r, 1 ≤ r → r ≤ n → 0 ≤ ∑ i ∈ Finset.range r, g i) →
    0 ≤ ∑ i ∈ Finset.range n, f i * g i := by
  intro n
  induction n with
  | zero => intros; simp
  | succ n ih =>
    intro f hmono hlast hpre
    have hfn : 0 ≤ f n := by simpa using hlast (Nat.succ_pos n)
    have key : ∑ i ∈ Finset.range (n + 1), f i * g i =
        ∑ i ∈ Finset.range n, (f i - f n) * g i + f n * ∑ i ∈ Finset.range (n + 1), g i := by
      rw [Finset.mul_sum, Finset.sum_range_succ, Finset.sum_range_succ (fun i => f n * g i)]
      have : ∑ i ∈ Finset.range n, f i * g i =
          ∑ i ∈ Finset.range n, ((f i - f n) * g i + f n * g i) := by
        refine Finset.sum_congr rfl (fun i _ => by ring)
      rw [this, Finset.sum_add_distrib]
      ring
    rw [key]
    have h1 : 0 ≤ ∑ i ∈ Finset.range n, (f i - f n) * g i := by
      apply ih (fun i => f i - f n)
      · intro i j hij hjn
        have := hmono i j hij (by omega)
        show f j - f n ≤ f i - f n
        linarith
      · intro hn
        have := hmono (n - 1) n (by omega) (by omega)
        show 0 ≤ f (n - 1) - f n
        linarith
      · intro r h1 h2
        exact hpre r h1 (by omega)
    have h2 : 0 ≤ ∑ i ∈ Finset.range (n + 1), g i := hpre (n + 1) (by omega) le_rfl
    have h3 := mul_nonneg hfn h2
    linarith

/-- Extension of a `Fin k`-indexed vector by zero. -/
noncomputable def ext {k : ℕ} (a : Fin k → ℝ) (n : ℕ) : ℝ := if h : n < k then a ⟨n, h⟩ else 0

theorem ext_val {k : ℕ} (a : Fin k → ℝ) (i : Fin k) : ext a i.val = a i := by
  simp [ext, i.isLt]

theorem univ_conv {k : ℕ} (a : Fin k → ℝ) :
    ∑ i : Fin k, a i = ∑ n ∈ Finset.range k, ext a n := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun i _ => (ext_val a i).symm)

theorem Iic_conv {k : ℕ} (a : Fin k → ℝ) (ℓ : Fin k) :
    ∑ i ∈ Finset.Iic ℓ, a i = ∑ n ∈ Finset.range (ℓ.val + 1), ext a n := by
  refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Iic] at hi
    show i.val ∈ Finset.range (ℓ.val + 1)
    rw [Finset.mem_range]
    have := Fin.le_def.mp hi
    omega
  · intro a₁ _ a₂ _ h
    exact Fin.ext h
  · intro n hn
    rw [Finset.mem_range] at hn
    refine ⟨⟨n, by have := ℓ.isLt; omega⟩, ?_, rfl⟩
    rw [Finset.mem_Iic, Fin.le_def]
    show n ≤ ℓ.val
    omega
  · intro i _
    exact (ext_val a i).symm

theorem P_lt {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ) (hcond : Lemma51Conditions A)
    (ℓ r : Fin k) (h : ℓ ≤ r) : 0 ≤ ∑ i ∈ Finset.Iic ℓ, ∑ j ∈ Finset.Iic r, A i j := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact hcond.2.1 _
  · have hsplit : ∀ i, ∑ j ∈ Finset.Iic r, A i j =
        ∑ j ∈ Finset.Iic ℓ, A i j + ∑ j ∈ Finset.Ioc ℓ r, A i j := by
      intro i
      rw [← Finset.sum_union, Finset.Iic_union_Ioc_eq_Iic (le_of_lt h)]
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_Iic] at hx
      rw [Finset.mem_Ioc] at hx'
      exact absurd hx'.1 (not_lt.mpr hx)
    simp_rw [hsplit, Finset.sum_add_distrib]
    exact add_nonneg (hcond.2.1 ℓ) (hcond.2.2 ℓ r h)

theorem P_nonneg {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsSymm)
    (hcond : Lemma51Conditions A) (ℓ r : Fin k) :
    0 ≤ ∑ i ∈ Finset.Iic ℓ, ∑ j ∈ Finset.Iic r, A i j := by
  rcases le_total ℓ r with h | h
  · exact P_lt A hcond ℓ r h
  · rw [show (∑ i ∈ Finset.Iic ℓ, ∑ j ∈ Finset.Iic r, A i j) =
        ∑ j ∈ Finset.Iic r, ∑ i ∈ Finset.Iic ℓ, A i j from Finset.sum_comm]
    have : ∑ y ∈ Finset.Iic r, ∑ x ∈ Finset.Iic ℓ, A x y =
        ∑ y ∈ Finset.Iic r, ∑ x ∈ Finset.Iic ℓ, A y x := by
      refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
      exact hA.apply y x
    rw [this]
    exact P_lt A hcond r ℓ h

/-- The bilinear form is nonnegative on antitone nonnegative vectors. -/
theorem B_nonneg {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsSymm)
    (hcond : Lemma51Conditions A) (t t' : Fin k → ℝ) (ht : Antitone t) (ht0 : ∀ m, 0 ≤ t m)
    (ht' : Antitone t') (ht'0 : ∀ m, 0 ≤ t' m) : 0 ≤ t ⬝ᵥ (A *ᵥ t') := by
  have hmono : ∀ (a : Fin k → ℝ), Antitone a →
      ∀ i j, i ≤ j → j < k → ext a j ≤ ext a i := by
    intro a ha i j hij hjk
    have hik : i < k := by omega
    simp only [ext, dif_pos hjk, dif_pos hik]
    exact ha (Fin.le_def.mpr hij)
  have hlast : ∀ (a : Fin k → ℝ), (∀ m, 0 ≤ a m) → 0 < k → 0 ≤ ext a (k - 1) := by
    intro a ha hk
    simp only [ext, dif_pos (show k - 1 < k by omega)]
    exact ha _
  have hdot : t ⬝ᵥ (A *ᵥ t') = ∑ n ∈ Finset.range k, ext t n * ext (A *ᵥ t') n := by
    rw [dotProduct, univ_conv]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases hn : n < k
    · simp only [ext, dif_pos hn]
    · simp only [ext, dif_neg hn, mul_zero]
  rw [hdot]
  apply abel_nonneg _ k _ (hmono t ht) (hlast t ht0)
  intro r hr1 hrk
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Fin k, ℓ.val + 1 = r :=
    ⟨⟨r - 1, by omega⟩, by show r - 1 + 1 = r; omega⟩
  rw [← hℓ, ← Iic_conv]
  have hsw : ∑ i ∈ Finset.Iic ℓ, (A *ᵥ t') i =
      ∑ j : Fin k, t' j * ∑ i ∈ Finset.Iic ℓ, A i j := by
    simp only [mulVec, dotProduct]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsw, univ_conv]
  have hprod : ∀ n, ext (fun j => t' j * ∑ i ∈ Finset.Iic ℓ, A i j) n =
      ext t' n * ext (fun j => ∑ i ∈ Finset.Iic ℓ, A i j) n := by
    intro n
    by_cases hn : n < k
    · simp only [ext, dif_pos hn]
    · simp only [ext, dif_neg hn, mul_zero]
  simp_rw [hprod]
  apply abel_nonneg _ k _ (hmono t' ht') (hlast t' ht'0)
  intro s hs1 hsk
  obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : Fin k, ℓ'.val + 1 = s :=
    ⟨⟨s - 1, by omega⟩, by show s - 1 + 1 = s; omega⟩
  rw [← hℓ', ← Iic_conv, Finset.sum_comm]
  exact P_nonneg A hA hcond ℓ ℓ'

theorem sym_form {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsSymm) (v w : Fin k → ℝ) :
    v ⬝ᵥ (A *ᵥ w) = w ⬝ᵥ (A *ᵥ v) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  rw [hA.apply j i]
  ring

theorem sorted_anti {k : ℕ} (u : Fin k → ℝ) : Antitone (u ∘ sortPerm u) := by
  intro a b hab
  have := Tuple.monotone_sort (-u) hab
  simp only [Function.comp_apply, Pi.neg_apply] at this
  show u (sortPerm u b) ≤ u (sortPerm u a)
  unfold sortPerm
  linarith

theorem flat_anti {k : ℕ} (s : Fin k → ℝ) (hs : Antitone s) (ℓ : Fin k) :
    Antitone (flat s ℓ) := by
  intro a b hab
  simp only [flat]
  by_cases ha : a < ℓ
  · by_cases hb : b < ℓ
    · simp only [if_pos ha, if_pos hb, le_refl]
    · simp only [if_pos ha, if_neg hb]
      exact hs (not_lt.mp hb)
  · have hb : ¬ b < ℓ := fun hb => ha (lt_of_le_of_lt hab hb)
    simp only [if_neg ha, if_neg hb]
    exact hs hab

theorem flat_nonneg {k : ℕ} (s : Fin k → ℝ) (hs : ∀ m, 0 ≤ s m) (ℓ : Fin k) :
    ∀ m, 0 ≤ flat s ℓ m := by
  intro m
  simp only [flat]
  split_ifs
  · exact hs ℓ
  · exact hs m

theorem flat_le {k : ℕ} (s : Fin k → ℝ) (hs : Antitone s) (ℓ : Fin k) :
    ∀ m, flat s ℓ m ≤ s m := by
  intro m
  simp only [flat]
  split_ifs with h
  · exact hs (le_of_lt h)
  · exact le_refl _

theorem flat_flat {k : ℕ} (s : Fin k → ℝ) (ℓ ℓ' : Fin k) (h : ℓ ≤ ℓ') :
    flat (flat s ℓ) ℓ' = flat s ℓ' := by
  funext m
  simp only [flat]
  by_cases hm : m < ℓ'
  · simp only [if_pos hm, if_neg (not_lt.mpr h)]
  · have : ¬ m < ℓ := fun h' => hm (lt_of_lt_of_le h' h)
    simp only [if_neg hm, if_neg this]

theorem diff_anti {k : ℕ} (t : Fin k → ℝ) (ht : Antitone t) (ℓ : Fin k) :
    Antitone (t - flat t ℓ) := by
  intro a b hab
  simp only [Pi.sub_apply, flat]
  by_cases ha : a < ℓ
  · by_cases hb : b < ℓ
    · simp only [if_pos ha, if_pos hb]
      linarith [ht hab]
    · simp only [if_pos ha, if_neg hb]
      linarith [ht (le_of_lt ha)]
  · have hb : ¬ b < ℓ := fun hb => ha (lt_of_le_of_lt hab hb)
    simp only [if_neg ha, if_neg hb, sub_self, le_refl]

theorem diff_nonneg {k : ℕ} (t : Fin k → ℝ) (ht : Antitone t) (ℓ : Fin k) :
    ∀ m, 0 ≤ (t - flat t ℓ) m := by
  intro m
  simp only [Pi.sub_apply, flat]
  split_ifs with h
  · linarith [ht (le_of_lt h)]
  · simp

theorem quad_eq {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (u : Fin k → ℝ) (m : Fin k) :
    quadTransform A u m = flat (u ∘ sortPerm u) ((sortPerm u).symm m) ⬝ᵥ
      (A *ᵥ flat (u ∘ sortPerm u) ((sortPerm u).symm m)) := rfl


theorem feasible {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsSymm)
    (hcond : Lemma51Conditions A) :
    IsFeasibleTransform (quadTransform A) := by
  refine ⟨?_, ?_, ?_⟩
  · -- range
    intro u hu ℓ
    obtain ⟨hu0, hu1⟩ := hu
    have hsa := sorted_anti u
    have hs0 : ∀ m, 0 ≤ (u ∘ sortPerm u) m := fun m => hu0 _
    have hsum_s : ∑ m, (u ∘ sortPerm u) m = 1 := by
      simp only [Function.comp_apply]
      rw [Equiv.sum_comp (sortPerm u) u]
      exact hu1
    obtain ⟨π, hπ⟩ : ∃ π, π = sortPerm u := ⟨_, rfl⟩
    rw [← hπ] at hsa hs0 hsum_s
    rw [quad_eq, ← hπ]
    obtain ⟨t, ht⟩ : ∃ t, t = flat (u ∘ π) (π.symm ℓ) := ⟨_, rfl⟩
    rw [← ht]
    have hta : Antitone t := by rw [ht]; exact flat_anti _ hsa _
    have ht0 : ∀ m, 0 ≤ t m := by rw [ht]; exact flat_nonneg _ hs0 _
    have hts : ∀ m, t m ≤ (u ∘ π) m := by rw [ht]; exact flat_le _ hsa _
    have hsum_t : ∑ m, t m ≤ 1 := by
      rw [← hsum_s]
      exact Finset.sum_le_sum (fun m _ => hts m)
    have hsum_t0 : 0 ≤ ∑ m, t m := Finset.sum_nonneg (fun m _ => ht0 m)
    refine ⟨B_nonneg A hA hcond t t hta ht0 hta ht0, ?_⟩
    have hle : t ⬝ᵥ (A *ᵥ t) ≤ (∑ m, t m) * (∑ m, t m) := by
      simp only [dotProduct, mulVec]
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun i _ => ?_)
      apply mul_le_mul_of_nonneg_left _ (ht0 i)
      refine Finset.sum_le_sum (fun j _ => ?_)
      have := hcond.1.2 i j
      nlinarith [ht0 j]
    nlinarith [mul_nonneg hsum_t0 (sub_nonneg.mpr hsum_t)]
  · -- vertices
    intro i
    have hsa := sorted_anti ((Pi.single i 1 : Fin k → ℝ))
    obtain ⟨π, hπ⟩ : ∃ π, π = sortPerm ((Pi.single i 1 : Fin k → ℝ)) := ⟨_, rfl⟩
    rw [← hπ] at hsa
    have hπ0 : π 0 = i := by
      by_contra hne
      have h1 : ((Pi.single i 1 : Fin k → ℝ) ∘ π) (π.symm i) = 1 := by
        simp only [Function.comp_apply, Equiv.apply_symm_apply, Pi.single_eq_same]
      have h2 : ((Pi.single i 1 : Fin k → ℝ) ∘ π) 0 = 0 := by
        simp only [Function.comp_apply]
        exact Pi.single_eq_of_ne hne 1
      have := hsa (Fin.zero_le (π.symm i))
      linarith
    have hsval : ∀ a, (Pi.single i 1 : Fin k → ℝ) (π a) = if a = 0 then 1 else 0 := by
      intro a
      by_cases ha : a = 0
      · rw [if_pos ha, ha, hπ0, Pi.single_eq_same]
      · rw [if_neg ha]
        apply Pi.single_eq_of_ne
        intro h
        apply ha
        have : π a = π 0 := by rw [h, hπ0]
        exact π.injective this
    funext m
    rw [quad_eq, ← hπ]
    by_cases hm : m = i
    · rw [hm]
      have hl : π.symm i = 0 := by rw [Equiv.symm_apply_eq, hπ0]
      rw [hl]
      have hfl : flat ((Pi.single i 1 : Fin k → ℝ) ∘ π) 0 = Pi.single 0 1 := by
        funext a
        have ha : ¬ a < 0 := not_lt.mpr (Fin.zero_le a)
        simp only [flat, if_neg ha, Function.comp_apply, hsval, Pi.single_apply]
      rw [hfl, Pi.single_eq_same, Matrix.mulVec_single_one, single_dotProduct, one_mul]
      exact hcond.1.1
    · have hl : π.symm m ≠ 0 := by
        intro h
        apply hm
        rw [← hπ0, ← h, Equiv.apply_symm_apply]
      have hfl : flat ((Pi.single i 1 : Fin k → ℝ) ∘ π) (π.symm m) = 0 := by
        funext a
        simp only [flat, Pi.zero_apply, Function.comp_apply]
        by_cases ha : a < π.symm m
        · rw [if_pos ha, Equiv.apply_symm_apply]
          exact Pi.single_eq_of_ne hm 1
        · rw [if_neg ha, hsval]
          have : a ≠ 0 := by
            intro h
            apply ha
            rw [h]
            exact lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hl)
          rw [if_neg this]
      rw [hfl, Pi.single_eq_of_ne hm]
      simp
  · -- order preservation
    intro u hu π' hanti
    obtain ⟨hu0, _⟩ := hu
    have hsa := sorted_anti u
    have hs0 : ∀ m, 0 ≤ (u ∘ sortPerm u) m := fun m => hu0 _
    have hsv : ∀ x, (u ∘ sortPerm u) ((sortPerm u).symm x) = u x := by
      intro x
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
    obtain ⟨π, hπ⟩ : ∃ π, π = sortPerm u := ⟨_, rfl⟩
    rw [← hπ] at hsa hs0 hsv
    intro p q hpq
    show quadTransform A u (π' q) ≤ quadTransform A u (π' p)
    rw [quad_eq, quad_eq, ← hπ]
    obtain ⟨a, ha⟩ : ∃ a, a = π' p := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = π' q := ⟨_, rfl⟩
    rw [← ha, ← hb]
    have hab : u b ≤ u a := by
      rw [ha, hb]
      exact hanti hpq
    by_cases heq : u a = u b
    · have e1 : (u ∘ π) (π.symm a) = (u ∘ π) (π.symm b) := by rw [hsv, hsv, heq]
      have hflat : flat (u ∘ π) (π.symm b) = flat (u ∘ π) (π.symm a) := by
        funext m
        simp only [flat]
        by_cases h1 : m < π.symm b
        · by_cases h2 : m < π.symm a
          · rw [if_pos h1, if_pos h2]
            exact e1.symm
          · rw [if_pos h1, if_neg h2]
            exact le_antisymm (hsa (le_of_lt h1)) (e1 ▸ hsa (not_lt.mp h2))
        · by_cases h2 : m < π.symm a
          · rw [if_neg h1, if_pos h2]
            exact le_antisymm (e1.symm ▸ hsa (not_lt.mp h1)) (hsa (le_of_lt h2))
          · rw [if_neg h1, if_neg h2]
      exact le_of_eq (by rw [hflat])
    · have hlt : u b < u a := lt_of_le_of_ne hab (Ne.symm heq)
      have hord : π.symm a ≤ π.symm b := by
        by_contra hc
        have := hsa (le_of_lt (not_le.mp hc))
        rw [hsv, hsv] at this
        linarith
      obtain ⟨t, ht⟩ : ∃ t, t = flat (u ∘ π) (π.symm a) := ⟨_, rfl⟩
      have hta : Antitone t := by rw [ht]; exact flat_anti _ hsa _
      have ht0 : ∀ m, 0 ≤ t m := by rw [ht]; exact flat_nonneg _ hs0 _
      have htb : flat (u ∘ π) (π.symm b) = flat t (π.symm b) := by
        rw [ht, flat_flat _ _ _ hord]
      rw [htb, ← ht]
      obtain ⟨t2, ht2⟩ : ∃ t2, t2 = flat t (π.symm b) := ⟨_, rfl⟩
      rw [← ht2]
      have ht2a : Antitone t2 := by rw [ht2]; exact flat_anti t hta _
      have ht20 : ∀ m, 0 ≤ t2 m := by rw [ht2]; exact flat_nonneg t ht0 _
      have hDa : Antitone (t - t2) := by rw [ht2]; exact diff_anti t hta _
      have hD0 : ∀ m, 0 ≤ (t - t2) m := by rw [ht2]; exact diff_nonneg t hta _
      have hD := B_nonneg A hA hcond (t - t2) (t + t2) hDa hD0 (hta.add ht2a)
        (fun m => add_nonneg (ht0 m) (ht20 m))
      have hexp : (t - t2) ⬝ᵥ (A *ᵥ (t + t2)) = t ⬝ᵥ (A *ᵥ t) - t2 ⬝ᵥ (A *ᵥ t2) := by
        rw [Matrix.mulVec_add, sub_dotProduct, dotProduct_add, dotProduct_add,
          sym_form A hA t t2]
        ring
      linarith

theorem quad_anti {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (u : Fin k → ℝ) (hu : Antitone u)
    (ℓ : Fin k) : quadTransform A u ℓ = flat u ℓ ⬝ᵥ (A *ᵥ flat u ℓ) := by
  rw [quad_eq]
  have hs : sortPerm u = Equiv.refl _ := by
    unfold sortPerm
    exact Tuple.sort_eq_refl_iff_monotone.mpr hu.neg
  rw [hs]
  rfl

theorem dval {k : ℕ} (i j m : Fin k) :
    (Pi.single i 1 - Pi.single j 1 : Fin k → ℝ) m =
      (if m = i then 1 else 0) - (if m = j then 1 else 0) := by
  simp only [Pi.sub_apply, Pi.single_apply]

theorem shift_apply {k : ℕ} (u : Fin k → ℝ) (i j : Fin k) (ε : ℝ) (m : Fin k) :
    ijShift u i j ε m = u m + ε * (Pi.single i 1 - Pi.single j 1 : Fin k → ℝ) m := by
  simp only [ijShift, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem shift_anti {k : ℕ} (u : Fin k → ℝ) (i j : Fin k) (ε : ℝ) (hij : i < j) (hε : 0 ≤ ε)
    (hu : Antitone u)
    (hgi : ∀ i' : Fin k, i'.val + 1 = i.val → u i + ε ≤ u i')
    (hgj : ∀ j' : Fin k, j'.val = j.val + 1 → u j' ≤ u j - ε) :
    Antitone (ijShift u i j ε) := by
  have hne : i ≠ j := ne_of_lt hij
  have hik := i.isLt
  have hjk := j.isLt
  have hpred : ∀ a : Fin k, a < i → u i + ε ≤ u a := by
    intro a ha
    have ha' := Fin.lt_def.mp ha
    have h1 := hgi ⟨i.val - 1, by omega⟩ (by show i.val - 1 + 1 = i.val; omega)
    have h2 : u ⟨i.val - 1, by omega⟩ ≤ u a := hu (Fin.le_def.mpr (by show a.val ≤ i.val - 1; omega))
    linarith
  have hsucc : ∀ b : Fin k, j < b → u b ≤ u j - ε := by
    intro b hb
    have hb' := Fin.lt_def.mp hb
    have hbk := b.isLt
    have h1 := hgj ⟨j.val + 1, by omega⟩ rfl
    have h2 : u b ≤ u ⟨j.val + 1, by omega⟩ :=
      hu (Fin.le_def.mpr (by show j.val + 1 ≤ b.val; omega))
    linarith
  have dI : (Pi.single i 1 - Pi.single j 1 : Fin k → ℝ) i = 1 := by
    rw [dval, if_pos rfl, if_neg hne, sub_zero]
  have dJ : (Pi.single i 1 - Pi.single j 1 : Fin k → ℝ) j = -1 := by
    rw [dval, if_neg hne.symm, if_pos rfl, zero_sub]
  have dO : ∀ m, m ≠ i → m ≠ j → (Pi.single i 1 - Pi.single j 1 : Fin k → ℝ) m = 0 := by
    intro m h1 h2
    rw [dval, if_neg h1, if_neg h2, sub_zero]
  intro a b hab
  rw [shift_apply, shift_apply]
  have huij : u j ≤ u i := hu (le_of_lt hij)
  by_cases hbi : b = i
  · rw [hbi] at hab ⊢
    rw [dI]
    by_cases hai : a = i
    · simp only [hai, dI, le_refl]
    · have hlt : a < i := lt_of_le_of_ne hab hai
      have haj : a ≠ j := fun h => absurd (h ▸ hlt) (not_lt.mpr (le_of_lt hij))
      rw [dO a hai haj]
      linarith [hpred a hlt]
  · by_cases hbj : b = j
    · rw [hbj] at hab ⊢
      rw [dJ]
      by_cases hai : a = i
      · rw [hai, dI]
        nlinarith
      · by_cases haj : a = j
        · simp only [haj, dJ, le_refl]
        · rw [dO a hai haj]
          have := hu hab
          nlinarith
    · rw [dO b hbi hbj]
      by_cases hai : a = i
      · rw [hai, dI]
        rw [hai] at hab
        have := hu hab
        nlinarith
      · by_cases haj : a = j
        · rw [haj, dJ]
          rw [haj] at hab
          have hlt : j < b := lt_of_le_of_ne hab (Ne.symm hbj)
          have := hsucc b hlt
          nlinarith
        · rw [dO a hai haj]
          have := hu hab
          nlinarith

theorem flat_shift {k : ℕ} (u : Fin k → ℝ) (i j : Fin k) (ε : ℝ) (ℓ : Fin k) :
    flat (ijShift u i j ε) ℓ = flat u ℓ + ε • flat (Pi.single i 1 - Pi.single j 1) ℓ := by
  funext m
  simp only [flat, Pi.add_apply, Pi.smul_apply, smul_eq_mul, shift_apply]
  split_ifs <;> rfl

theorem quad_expand {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsSymm)
    (t δ : Fin k → ℝ) (ε : ℝ) :
    (t + ε • δ) ⬝ᵥ (A *ᵥ (t + ε • δ)) =
      t ⬝ᵥ (A *ᵥ t) + 2 * ε * (δ ⬝ᵥ (A *ᵥ t)) + ε ^ 2 * (δ ⬝ᵥ (A *ᵥ δ)) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [sym_form A hA t δ]
  ring

theorem sum_single_w {k : ℕ} (w : Fin k → ℝ) (i : Fin k) :
    ∑ m, (if m = i then (1 : ℝ) else 0) * w m = w i := by
  simp

theorem sum_le_w {k : ℕ} (w : Fin k → ℝ) (i : Fin k) :
    ∑ m, (if m ≤ i then (1 : ℝ) else 0) * w m = ∑ m ∈ Finset.Iic i, w m := by
  have hI : Finset.Iic i = Finset.univ.filter (fun m : Fin k => m ≤ i) := by
    ext m
    simp
  rw [hI, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  split_ifs <;> simp

/-- The per-coordinate first-order coefficient. -/
theorem coeff_eq {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (i j : Fin k) (hij : i < j)
    (t : Fin k → ℝ) (ℓ : Fin k) :
    2 * |flat (Pi.single i 1 - Pi.single j 1 : Fin k → ℝ) ℓ ⬝ᵥ (A *ᵥ t)| / ((ℓ.val : ℝ) + 1) =
      (if ℓ < i then 2 / ((ℓ.val : ℝ) + 1) * |(A i - A j) ⬝ᵥ t| else 0) +
      (if ℓ = i then 2 / ((i.val : ℝ) + 1) * |((∑ l ∈ Finset.Iic i, A l) - A j) ⬝ᵥ t| else 0) +
      (if i < ℓ ∧ ℓ < j then 2 / ((ℓ.val : ℝ) + 1) * |A j ⬝ᵥ t| else 0) +
      (if ℓ = j then 2 / ((j.val : ℝ) + 1) * |(∑ l ∈ Finset.Iic j, A l) ⬝ᵥ t| else 0) := by
  have hne : i ≠ j := ne_of_lt hij
  obtain ⟨w, hw⟩ : ∃ w, w = A *ᵥ t := ⟨_, rfl⟩
  have hAi : ∀ l, A l ⬝ᵥ t = w l := fun l => by rw [hw]; rfl
  have hsub : (A i - A j) ⬝ᵥ t = w i - w j := by rw [sub_dotProduct, hAi, hAi]
  have hsumi : ((∑ l ∈ Finset.Iic i, A l) - A j) ⬝ᵥ t = ∑ l ∈ Finset.Iic i, w l - w j := by
    rw [sub_dotProduct, sum_dotProduct (Finset.Iic i) (fun l => A l) t, hAi]
    simp_rw [hAi]
  have hsumj : (∑ l ∈ Finset.Iic j, A l) ⬝ᵥ t = ∑ l ∈ Finset.Iic j, w l := by
    rw [sum_dotProduct (Finset.Iic j) (fun l => A l) t]
    simp_rw [hAi]
  rw [hsub, hsumi, hsumj, hAi j, ← hw]
  have hdot : flat (Pi.single i 1 - Pi.single j 1 : Fin k → ℝ) ℓ ⬝ᵥ w =
      ∑ m, (if m < ℓ then (if ℓ = i then (1 : ℝ) else 0) - (if ℓ = j then 1 else 0)
        else (if m = i then 1 else 0) - (if m = j then 1 else 0)) * w m := by
    simp only [dotProduct, flat, dval]
  rw [hdot]
  rcases lt_trichotomy ℓ i with h1 | h1 | h1
  · -- ℓ < i
    have hℓi : ℓ ≠ i := ne_of_lt h1
    have hℓj : ℓ ≠ j := ne_of_lt (lt_trans h1 hij)
    have hc : ∀ m, (if m < ℓ then (if ℓ = i then (1 : ℝ) else 0) - (if ℓ = j then 1 else 0)
        else (if m = i then 1 else 0) - (if m = j then 1 else 0)) =
        (if m = i then 1 else 0) - (if m = j then 1 else 0) := by
      intro m
      by_cases hm : m < ℓ
      · have hmi : m ≠ i := ne_of_lt (lt_trans hm h1)
        have hmj : m ≠ j := ne_of_lt (lt_trans hm (lt_trans h1 hij))
        rw [if_pos hm, if_neg hℓi, if_neg hℓj, if_neg hmi, if_neg hmj]
      · rw [if_neg hm]
    simp_rw [hc, sub_mul, Finset.sum_sub_distrib, sum_single_w]
    rw [if_pos h1, if_neg hℓi, if_neg (fun h => absurd h.1 (not_lt.mpr (le_of_lt h1))),
      if_neg hℓj]
    ring
  · -- ℓ = i
    have hℓj : ℓ ≠ j := h1 ▸ hne
    have hc : ∀ m, (if m < ℓ then (if ℓ = i then (1 : ℝ) else 0) - (if ℓ = j then 1 else 0)
        else (if m = i then 1 else 0) - (if m = j then 1 else 0)) =
        (if m ≤ ℓ then 1 else 0) - (if m = j then 1 else 0) := by
      intro m
      by_cases hm : m < ℓ
      · have hmj : m ≠ j := ne_of_lt (lt_trans hm (h1 ▸ hij))
        rw [if_pos hm, if_pos h1, if_neg hℓj, if_pos (le_of_lt hm), if_neg hmj]
      · rw [if_neg hm]
        by_cases hm' : m = ℓ
        · rw [if_pos (hm'.trans h1), if_pos (le_of_eq hm')]
        · rw [if_neg (fun h => hm' (h.trans h1.symm)),
            if_neg (fun h => hm (lt_of_le_of_ne h hm'))]
    simp_rw [hc, sub_mul, Finset.sum_sub_distrib, sum_single_w, sum_le_w]
    subst h1
    rw [if_neg (lt_irrefl ℓ), if_pos rfl, if_neg (fun h => lt_irrefl ℓ h.1), if_neg hne]
    ring
  · rcases lt_trichotomy ℓ j with h2 | h2 | h2
    · -- i < ℓ < j
      have hℓi : ℓ ≠ i := ne_of_gt h1
      have hℓj : ℓ ≠ j := ne_of_lt h2
      have hc : ∀ m, (if m < ℓ then (if ℓ = i then (1 : ℝ) else 0) - (if ℓ = j then 1 else 0)
          else (if m = i then 1 else 0) - (if m = j then 1 else 0)) =
          -(if m = j then 1 else 0) := by
        intro m
        by_cases hm : m < ℓ
        · have hmj : m ≠ j := ne_of_lt (lt_trans hm h2)
          rw [if_pos hm, if_neg hℓi, if_neg hℓj, if_neg hmj]
          ring
        · rw [if_neg hm]
          have hmi : m ≠ i := fun h => hm (h ▸ h1)
          rw [if_neg hmi]
          ring
      simp_rw [hc, neg_mul, Finset.sum_neg_distrib, sum_single_w, abs_neg]
      rw [if_neg (not_lt.mpr (le_of_lt h1)), if_neg hℓi, if_pos ⟨h1, h2⟩, if_neg hℓj]
      ring
    · -- ℓ = j
      have hℓi : ℓ ≠ i := ne_of_gt h1
      have hc : ∀ m, (if m < ℓ then (if ℓ = i then (1 : ℝ) else 0) - (if ℓ = j then 1 else 0)
          else (if m = i then 1 else 0) - (if m = j then 1 else 0)) =
          -(if m ≤ ℓ then 1 else 0) := by
        intro m
        by_cases hm : m < ℓ
        · rw [if_pos hm, if_neg hℓi, if_pos h2, if_pos (le_of_lt hm)]
          ring
        · rw [if_neg hm]
          have hmi : m ≠ i := fun h => hm (h ▸ h1)
          rw [if_neg hmi]
          by_cases hm' : m = ℓ
          · rw [if_pos (hm'.trans h2), if_pos (le_of_eq hm')]
            ring
          · rw [if_neg (fun h => hm' (h.trans h2.symm)),
              if_neg (fun h => hm (lt_of_le_of_ne h hm'))]
            ring
      simp_rw [hc, neg_mul, Finset.sum_neg_distrib, sum_le_w, abs_neg]
      subst h2
      rw [if_neg (not_lt.mpr (le_of_lt h1)), if_neg (ne_of_gt h1),
        if_neg (fun h => lt_irrefl ℓ h.2), if_pos rfl]
      ring
    · -- ℓ > j
      have hℓi : ℓ ≠ i := ne_of_gt h1
      have hℓj : ℓ ≠ j := ne_of_gt h2
      have hc : ∀ m, (if m < ℓ then (if ℓ = i then (1 : ℝ) else 0) - (if ℓ = j then 1 else 0)
          else (if m = i then 1 else 0) - (if m = j then 1 else 0)) = 0 := by
        intro m
        by_cases hm : m < ℓ
        · rw [if_pos hm, if_neg hℓi, if_neg hℓj]
          ring
        · rw [if_neg hm]
          have hmi : m ≠ i := fun h => hm (h ▸ h1)
          have hmj : m ≠ j := fun h => hm (h ▸ h2)
          rw [if_neg hmi, if_neg hmj]
          ring
      simp_rw [hc, zero_mul, Finset.sum_const_zero, abs_zero]
      rw [if_neg (not_lt.mpr (le_of_lt h1)), if_neg hℓi,
        if_neg (fun h => absurd h.2 (not_lt.mpr (le_of_lt h2))), if_neg hℓj]
      ring

theorem sum_split {k : ℕ} (i j : Fin k) (F1 F3 : Fin k → ℝ) (c2 c4 : ℝ) :
    ∑ ℓ, ((if ℓ < i then F1 ℓ else 0) + (if ℓ = i then c2 else 0) +
      (if i < ℓ ∧ ℓ < j then F3 ℓ else 0) + (if ℓ = j then c4 else 0)) =
      ∑ l ∈ Finset.Iio i, F1 l + c2 + ∑ l ∈ Finset.Ioo i j, F3 l + c4 := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have e1 : ∑ ℓ, (if ℓ < i then F1 ℓ else 0) = ∑ l ∈ Finset.Iio i, F1 l := by
    rw [← Finset.sum_filter]
    congr 1
    ext m
    simp
  have e3 : ∑ ℓ, (if i < ℓ ∧ ℓ < j then F3 ℓ else 0) = ∑ l ∈ Finset.Ioo i j, F3 l := by
    rw [← Finset.sum_filter]
    congr 1
    ext m
    simp
  have e2 : ∑ ℓ, (if ℓ = i then c2 else 0) = c2 := by simp
  have e4 : ∑ ℓ, (if ℓ = j then c4 else 0) = c4 := by simp
  rw [e1, e2, e3, e4]

end Aux_MultiwayCut_lemma_5_2

open MultiwayCut Aux_MultiwayCut_lemma_5_2 Filter Topology in
theorem Aux_MultiwayCut_lemma_5_2.L52 {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsSymm)
    (hcond : Lemma51Conditions A) (u : Fin k → ℝ) (i j : Fin k) :
    IJDensityLE (fun x y => sepCKR (quadTransform A x) (quadTransform A y))
      (Equiv.refl (Fin k)) i j u
      (∑ l ∈ Finset.Iio i, 2 / ((l.val : ℝ) + 1) * |(A i - A j) ⬝ᵥ flat u l| +
        2 / ((i.val : ℝ) + 1) * |((∑ l ∈ Finset.Iic i, A l) - A j) ⬝ᵥ flat u i| +
        ∑ l ∈ Finset.Ioo i j, 2 / ((l.val : ℝ) + 1) * |A j ⬝ᵥ flat u l| +
        2 / ((j.val : ℝ) + 1) * |(∑ l ∈ Finset.Iic j, A l) ⬝ᵥ flat u j|) := by
  intro η hη
  obtain ⟨d, hd⟩ : ∃ d : Fin k → ℝ, d = Pi.single i 1 - Pi.single j 1 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ,
      K = ∑ ℓ : Fin k, |flat d ℓ ⬝ᵥ (A *ᵥ flat d ℓ)| / ((ℓ.val : ℝ) + 1) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact Finset.sum_nonneg (fun ℓ _ => div_nonneg (abs_nonneg _) (by positivity))
  have hmem : Set.Ioo (0 : ℝ) (η / (K + 1)) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (div_pos hη (by linarith))
  filter_upwards [hmem] with ε hε
  intro hedge
  obtain ⟨hu, hv, hij, hε0, hanti, hgi, hgj, _⟩ := hedge
  simp only [Equiv.refl_apply, Equiv.coe_refl, Function.comp_id] at hanti hgi hgj hv ⊢
  have hεpos : 0 < ε := hε.1
  have hua : Antitone u := fun a b h => hanti h
  have hva : Antitone (ijShift u i j ε) := shift_anti u i j ε hij hε0 hua hgi hgj
  have hF := feasible A hA hcond
  -- the transformed points are sorted and in [0,1]
  have hfu01 := hF.1 u hu
  have hfv01 := hF.1 _ hv
  have hfua : Antitone (quadTransform A u) :=
    fun a b h => hF.2.2 u hu (Equiv.refl _) (fun x y hxy => hua hxy) h
  have hfva : Antitone (quadTransform A (ijShift u i j ε)) :=
    fun a b h => hF.2.2 _ hv (Equiv.refl _) (fun x y hxy => hva hxy) h
  have hsep := sep_bound (quadTransform A u) (quadTransform A (ijShift u i j ε)) hfu01 hfv01
    hfua hfva
  -- coordinatewise differences
  have hdiff : ∀ ℓ : Fin k,
      |quadTransform A u ℓ - quadTransform A (ijShift u i j ε) ℓ| ≤
        ε * (2 * |flat d ℓ ⬝ᵥ (A *ᵥ flat u ℓ)|) + ε ^ 2 * |flat d ℓ ⬝ᵥ (A *ᵥ flat d ℓ)| := by
    intro ℓ
    rw [quad_anti A u hua, quad_anti A _ hva, flat_shift, ← hd, quad_expand A hA]
    have e : flat u ℓ ⬝ᵥ (A *ᵥ flat u ℓ) -
        (flat u ℓ ⬝ᵥ (A *ᵥ flat u ℓ) + 2 * ε * (flat d ℓ ⬝ᵥ (A *ᵥ flat u ℓ)) +
          ε ^ 2 * (flat d ℓ ⬝ᵥ (A *ᵥ flat d ℓ))) =
        -(2 * ε * (flat d ℓ ⬝ᵥ (A *ᵥ flat u ℓ)) + ε ^ 2 * (flat d ℓ ⬝ᵥ (A *ᵥ flat d ℓ))) := by
      ring
    rw [e, abs_neg]
    calc |2 * ε * (flat d ℓ ⬝ᵥ (A *ᵥ flat u ℓ)) + ε ^ 2 * (flat d ℓ ⬝ᵥ (A *ᵥ flat d ℓ))|
        ≤ |2 * ε * (flat d ℓ ⬝ᵥ (A *ᵥ flat u ℓ))| + |ε ^ 2 * (flat d ℓ ⬝ᵥ (A *ᵥ flat d ℓ))| :=
          abs_add_le _ _
      _ = ε * (2 * |flat d ℓ ⬝ᵥ (A *ᵥ flat u ℓ)|) + ε ^ 2 * |flat d ℓ ⬝ᵥ (A *ᵥ flat d ℓ)| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
            abs_of_nonneg hε0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)]
          ring
  have hG : ∑ ℓ : Fin k, 2 * |flat d ℓ ⬝ᵥ (A *ᵥ flat u ℓ)| / ((ℓ.val : ℝ) + 1) =
      ∑ l ∈ Finset.Iio i, 2 / ((l.val : ℝ) + 1) * |(A i - A j) ⬝ᵥ flat u l| +
        2 / ((i.val : ℝ) + 1) * |((∑ l ∈ Finset.Iic i, A l) - A j) ⬝ᵥ flat u i| +
        ∑ l ∈ Finset.Ioo i j, 2 / ((l.val : ℝ) + 1) * |A j ⬝ᵥ flat u l| +
        2 / ((j.val : ℝ) + 1) * |(∑ l ∈ Finset.Iic j, A l) ⬝ᵥ flat u j| := by
    rw [← sum_split i j (fun l => 2 / ((l.val : ℝ) + 1) * |(A i - A j) ⬝ᵥ flat u l|)
      (fun l => 2 / ((l.val : ℝ) + 1) * |A j ⬝ᵥ flat u l|)]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    rw [hd, coeff_eq A i j hij (flat u ℓ) ℓ]
    by_cases h1 : ℓ = i
    · subst h1
      simp only [if_neg (ne_of_lt hij)]
    · by_cases h2 : ℓ = j
      · subst h2
        simp only [if_neg h1]
      · simp only [if_neg h1, if_neg h2]
  have hsum : ∑ ℓ : Fin k,
      |quadTransform A u ℓ - quadTransform A (ijShift u i j ε) ℓ| / ((ℓ.val : ℝ) + 1) ≤
        ε * ∑ ℓ : Fin k, 2 * |flat d ℓ ⬝ᵥ (A *ᵥ flat u ℓ)| / ((ℓ.val : ℝ) + 1) + ε ^ 2 * K := by
    rw [hK, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun ℓ _ => ?_)
    have hpos : (0 : ℝ) < (ℓ.val : ℝ) + 1 := by positivity
    calc |quadTransform A u ℓ - quadTransform A (ijShift u i j ε) ℓ| / ((ℓ.val : ℝ) + 1)
        ≤ (ε * (2 * |flat d ℓ ⬝ᵥ (A *ᵥ flat u ℓ)|) +
            ε ^ 2 * |flat d ℓ ⬝ᵥ (A *ᵥ flat d ℓ)|) / ((ℓ.val : ℝ) + 1) :=
          div_le_div_of_nonneg_right (hdiff ℓ) (le_of_lt hpos)
      _ = ε * (2 * |flat d ℓ ⬝ᵥ (A *ᵥ flat u ℓ)| / ((ℓ.val : ℝ) + 1)) +
            ε ^ 2 * (|flat d ℓ ⬝ᵥ (A *ᵥ flat d ℓ)| / ((ℓ.val : ℝ) + 1)) := by
          ring
  have hεK : ε * K ≤ η := by
    have h1 := hε.2
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < K + 1)] at h1
    nlinarith
  rw [hG] at hsum
  rw [div_le_iff₀ hεpos]
  have hfinal := hsep.trans hsum
  nlinarith [hfinal, hεK, mul_le_mul_of_nonneg_left hεK (le_of_lt hεpos)]

namespace Aux_MultiwayCut_lemma_5_4

open MultiwayCut

/-! ### An `ℕ`-indexed model of the matrix `A53` -/

noncomputable def aN (m n : ℕ) : ℝ :=
  if m = 0 ∧ n = 0 then 1
  else if m = 0 ∨ n = 0 then 5 / 27
  else if m = n ∧ (m = 1 ∨ m = 2) then 1 / 9
  else if m = 3 ∧ n = 3 then -5 / 18
  else if m ≤ 2 ∨ n ≤ 2 then 5 / 108
  else 0

lemma A_eq {k : ℕ} (m n : Fin k) : A53 k m n = aN m.val n.val := by
  unfold A53 aN
  by_cases h : m = n
  · subst h
    simp
  · have h' : m.val ≠ n.val := fun e => h (Fin.ext e)
    simp [h, h']

lemma aN_symm (m n : ℕ) : aN m n = aN n m := by
  unfold aN
  split_ifs <;> first | rfl | (simp_all; done) | (exfalso; omega) | (norm_num; done) | (exfalso; simp_all; done)

lemma aN_col0 (r : ℕ) : aN r 0 = if r = 0 then 1 else 5 / 27 := by
  unfold aN
  split_ifs <;> first | rfl | (simp_all; done) | (exfalso; omega) | (norm_num; done) | (exfalso; simp_all; done)

lemma aN_col1 (r : ℕ) : aN r 1 = if r = 0 then 5 / 27 else if r = 1 then 1 / 9 else 5 / 108 := by
  unfold aN
  split_ifs <;> first | rfl | (simp_all; done) | (exfalso; omega) | (norm_num; done) | (exfalso; simp_all; done)

lemma aN_col2 (r : ℕ) : aN r 2 = if r = 0 then 5 / 27 else if r = 2 then 1 / 9 else 5 / 108 := by
  unfold aN
  split_ifs <;> first | rfl | (simp_all; done) | (exfalso; omega) | (norm_num; done) | (exfalso; simp_all; done)

lemma aN_col3 (r : ℕ) :
    aN r 3 = if r = 0 then 5 / 27 else if r ≤ 2 then 5 / 108 else if r = 3 then -5 / 18 else 0 := by
  unfold aN
  split_ifs <;> first | rfl | (simp_all; done) | (exfalso; omega) | (norm_num; done) | (exfalso; simp_all; done)

lemma aN_tail (r n : ℕ) (hn : 4 ≤ n) :
    aN r n = if r = 0 then 5 / 27 else if r ≤ 2 then 5 / 108 else 0 := by
  unfold aN
  split_ifs <;> first | rfl | (simp_all; done) | (exfalso; omega) | (norm_num; done) | (exfalso; simp_all; done)

lemma aN_big (r n : ℕ) (hr : 4 ≤ r) : aN r n = aN 4 n := by
  unfold aN
  split_ifs <;> first | rfl | (simp_all; done) | (exfalso; omega) | (norm_num; done) | (exfalso; simp_all; done)

lemma aN_row0 (n : ℕ) : aN 0 n = if n = 0 then 1 else 5 / 27 := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> norm_num [aN]
  · have h0 : n ≠ 0 := by omega
    simp [aN, h0]

lemma aN_row1 (n : ℕ) : aN 1 n = if n = 0 then 5 / 27 else if n = 1 then 1 / 9 else 5 / 108 := by
  unfold aN
  split_ifs <;> first | rfl | (simp_all; done) | (exfalso; omega) | (norm_num; done) | (exfalso; simp_all; done)

lemma aN_row2 (n : ℕ) : aN 2 n = if n = 0 then 5 / 27 else if n = 2 then 1 / 9 else 5 / 108 := by
  unfold aN
  split_ifs <;> first | rfl | (simp_all; done) | (exfalso; omega) | (norm_num; done) | (exfalso; simp_all; done)

lemma aN_row3 (n : ℕ) :
    aN 3 n = if n = 0 then 5 / 27 else if n ≤ 2 then 5 / 108 else if n = 3 then -5 / 18 else 0 := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> norm_num [aN]
  · have h0 : n ≠ 0 := by omega
    have h3 : n ≠ 3 := by omega
    have h3' : (3 : ℕ) ≠ n := by omega
    have h2 : ¬ n ≤ 2 := by omega
    simp [aN, h0, h3, h3', h2]

lemma aN_rowbig (m n : ℕ) (hm : 4 ≤ m) :
    aN m n = if n = 0 then 5 / 27 else if n ≤ 2 then 5 / 108 else 0 := by
  unfold aN
  split_ifs <;> first | rfl | (simp_all; done) | (exfalso; omega) | (norm_num; done) | (exfalso; simp_all; done)

lemma aN_ge3_small (j n : ℕ) (hj : 3 ≤ j) (hn : n ≤ 2) : aN j n = aN 3 n := by
  rcases Nat.lt_or_ge j 4 with h | h
  · have : j = 3 := by omega
    rw [this]
  · rw [aN_rowbig j n h, aN_row3]
    split_ifs <;> first | (norm_num; done) | (exfalso; omega)

lemma aN_le0 (j n : ℕ) (hj : 1 ≤ j) : aN j n ≤ aN 0 n := by
  rw [aN_row0]
  rcases Nat.lt_or_ge j 4 with h | h
  · interval_cases j
    · rw [aN_row1]
      split_ifs <;> first | (norm_num; done) | (exfalso; omega)
    · rw [aN_row2]
      split_ifs <;> first | (norm_num; done) | (exfalso; omega)
    · rw [aN_row3]
      split_ifs <;> first | (norm_num; done) | (exfalso; omega)
  · rw [aN_rowbig j n h]
    split_ifs <;> first | (norm_num; done) | (exfalso; omega)

lemma aN_le12 (i j n : ℕ) (hi : 1 ≤ i ∧ i ≤ 2) (hj : 3 ≤ j) : aN j n ≤ aN i n := by
  unfold aN
  split_ifs <;> first | (norm_num; done) | (simp_all; done) | (exfalso; omega) | (exfalso; simp_all; done)

lemma aN_le3 (j n : ℕ) (hj : 4 ≤ j) : aN 3 n ≤ aN j n := by
  rw [aN_rowbig j n hj, aN_row3]
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

lemma aN_le_one (m n : ℕ) : aN m n ≤ 1 := by
  unfold aN
  split_ifs <;> norm_num

lemma aN_nonneg' (m n : ℕ) (h : ¬ (m = 3 ∧ n = 3)) : 0 ≤ aN m n := by
  unfold aN
  split_ifs <;> first | (norm_num; done) | (simp_all; done) | (exfalso; omega) | (exfalso; simp_all; done)

/-! ### Prefix sums -/

noncomputable def pN (r m : ℕ) : ℝ := ∑ n ∈ Finset.range (m + 1), aN r n

noncomputable def QN (i m : ℕ) : ℝ := ∑ l ∈ Finset.range (i + 1), pN l m

lemma pN_succ (r m : ℕ) : pN r (m + 1) = pN r m + aN r (m + 1) := by
  unfold pN
  exact Finset.sum_range_succ _ _

lemma QN_succ (i m : ℕ) : QN (i + 1) m = QN i m + pN (i + 1) m := by
  unfold QN
  exact Finset.sum_range_succ _ _

noncomputable def pT (r t : ℕ) : ℝ :=
  if r = 0 then 1 + 5 / 27 * ((t : ℝ) + 3) else if r ≤ 2 then (42 + 5 * (t : ℝ)) / 108
  else if r = 3 then 0 else 5 / 18

lemma pN_three (r : ℕ) : pN r 3 = pT r 0 := by
  unfold pN pT
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, aN_col0, aN_col1, aN_col2, aN_col3]
  split_ifs <;> first | (norm_num; done) | (simp_all; done) | (exfalso; omega) | (exfalso; simp_all; done)

lemma pN_t (r t : ℕ) : pN r (t + 3) = pT r t := by
  induction t with
  | zero => exact pN_three r
  | succ t ih =>
    rw [show t + 1 + 3 = t + 3 + 1 by ring, pN_succ, ih, aN_tail r (t + 3 + 1) (by omega)]
    unfold pT
    split_ifs <;> first | ring1 | (push_cast; ring1) | (simp_all; done) | (exfalso; omega) | (norm_num; done) | (exfalso; simp_all; done)

noncomputable def QT (r t : ℕ) : ℝ :=
  if r = 0 then (168 + 20 * (t : ℝ)) / 108 else if r = 1 then (210 + 25 * (t : ℝ)) / 108
  else if r = 2 then (252 + 30 * (t : ℝ)) / 108
  else (252 + 30 * (t : ℝ)) / 108 + ((r : ℝ) - 3) * (5 / 18)

lemma QN_t (r t : ℕ) : QN r (t + 3) = QT r t := by
  induction r with
  | zero =>
    have e : QN 0 (t + 3) = pN 0 (t + 3) := by
      unfold QN
      simp
    rw [e, pN_t]
    unfold pT QT
    rw [if_pos rfl, if_pos rfl]
    ring1
  | succ r ih =>
    rw [QN_succ, ih, pN_t]
    unfold QT pT
    split_ifs <;> first | ring1 | (push_cast; ring1) | (exfalso; omega) | (subst_vars; push_cast; ring1) | (subst_vars; norm_num; done) | (simp_all; done) | (norm_num; done) | (exfalso; simp_all; done)

lemma pbig_t (r t : ℕ) (hr : 4 ≤ r) : pN r (t + 3) = 5 / 18 := by
  rw [pN_t]
  unfold pT
  rw [if_neg (show ¬ r = 0 by omega), if_neg (show ¬ r ≤ 2 by omega),
    if_neg (show ¬ r = 3 by omega)]

lemma p3_t (t : ℕ) : pN 3 (t + 3) = 0 := by
  rw [pN_t]
  unfold pT
  norm_num

lemma Qbig_t (r t : ℕ) (hr : 3 ≤ r) :
    QN r (t + 3) = (252 + 30 * (t : ℝ)) / 108 + ((r : ℝ) - 3) * (5 / 18) := by
  rw [QN_t]
  unfold QT
  rw [if_neg (show ¬ r = 0 by omega), if_neg (show ¬ r = 1 by omega),
    if_neg (show ¬ r = 2 by omega)]

lemma p_ge3_small (j m : ℕ) (hj : 3 ≤ j) (hm : m ≤ 2) : pN j m = pN 3 m :=
  Finset.sum_congr rfl (fun n hn => aN_ge3_small j n hj
    (by have := Finset.mem_range.mp hn; omega))

/-! ### Signs -/

lemma pN_nonneg (r m : ℕ) : 0 ≤ pN r m := by
  rcases Nat.lt_or_ge m 3 with hm | hm
  · interval_cases m <;>
      (unfold pN
       simp only [Finset.sum_range_succ, Finset.sum_range_zero, aN_col0, aN_col1, aN_col2]
       split_ifs <;> norm_num)
  · obtain ⟨t, rfl⟩ : ∃ t, m = t + 3 := ⟨m - 3, by omega⟩
    rw [pN_t]
    unfold pT
    split_ifs <;> positivity

lemma QN_nonneg (i m : ℕ) : 0 ≤ QN i m := Finset.sum_nonneg (fun l _ => pN_nonneg l m)

lemma p_le_p0 (j m : ℕ) (hj : 1 ≤ j) : pN j m ≤ pN 0 m :=
  Finset.sum_le_sum (fun n _ => aN_le0 j n hj)

lemma Qp_nonneg (i j m : ℕ) (hij : i < j) : 0 ≤ QN i m - pN j m := by
  have h1 : pN 0 m ≤ QN i m :=
    Finset.single_le_sum (f := fun l => pN l m) (fun l _ => pN_nonneg l m)
      (Finset.mem_range.mpr (Nat.succ_pos i))
  have h2 := p_le_p0 j m (by omega)
  linarith

lemma p12 (m : ℕ) : 0 ≤ pN 1 m - pN 2 m := by
  rcases Nat.lt_or_ge m 3 with hm | hm
  · interval_cases m <;>
      (unfold pN
       simp only [Finset.sum_range_succ, Finset.sum_range_zero, aN_col0, aN_col1, aN_col2]
       norm_num)
  · obtain ⟨t, rfl⟩ : ∃ t, m = t + 3 := ⟨m - 3, by omega⟩
    rw [pN_t, pN_t]
    unfold pT
    norm_num

lemma pp_nonneg (i j m : ℕ) (hij : i < j) (hi3 : i ≠ 3) : 0 ≤ pN i m - pN j m := by
  rcases Nat.lt_or_ge i 4 with hi | hi
  · interval_cases i
    · linarith [p_le_p0 j m (by omega)]
    · rcases Nat.lt_or_ge j 3 with hj | hj
      · have hj2 : j = 2 := by omega
        subst hj2
        exact p12 m
      · have h := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range (m + 1)) =>
          aN_le12 1 j n ⟨le_refl _, by norm_num⟩ hj)
        unfold pN
        linarith
    · have hj : 3 ≤ j := by omega
      have h := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range (m + 1)) =>
        aN_le12 2 j n ⟨by norm_num, le_refl _⟩ hj)
      unfold pN
      linarith
    · exact absurd rfl hi3
  · have e1 : pN i m = pN 4 m := Finset.sum_congr rfl (fun n _ => aN_big i n hi)
    have e2 : pN j m = pN 4 m := Finset.sum_congr rfl (fun n _ => aN_big j n (by omega))
    rw [e1, e2, sub_self]

lemma p3_le (j m : ℕ) (hj : 3 < j) : pN 3 m - pN j m ≤ 0 := by
  have h := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range (m + 1)) => aN_le3 j n hj)
  unfold pN
  linarith

/-! ### Harmonic weights -/

noncomputable def W1N (i m : ℕ) : ℝ :=
  ∑ l ∈ Finset.range i, if l ≤ m then 2 / ((l : ℝ) + 1) else 0

noncomputable def W3N (i j m : ℕ) : ℝ :=
  ∑ l ∈ Finset.Ioo i j, if l ≤ m then 2 / ((l : ℝ) + 1) else 0

lemma W3_range (i j m : ℕ) :
    W3N i j m = ∑ l ∈ Finset.range j, if i < l ∧ l ≤ m then 2 / ((l : ℝ) + 1) else 0 := by
  unfold W3N
  have hset : (Finset.range j).filter (fun l => i < l) = Finset.Ioo i j := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h2, h1⟩
  rw [← hset, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  by_cases h1 : i < l
  · by_cases h2 : l ≤ m
    · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2)]
  · rw [if_neg h1, if_neg (fun h => h1 h.1)]

lemma W3_lt (i j m : ℕ) (h : m + 1 ≤ j) :
    W3N i j m = ∑ l ∈ Finset.range (m + 1), if i < l then 2 / ((l : ℝ) + 1) else 0 := by
  rw [W3_range]
  symm
  have hsub : Finset.range (m + 1) ⊆ Finset.range j := Finset.range_mono h
  calc ∑ l ∈ Finset.range (m + 1), (if i < l then 2 / ((l : ℝ) + 1) else 0)
      = ∑ l ∈ Finset.range (m + 1), (if i < l ∧ l ≤ m then 2 / ((l : ℝ) + 1) else 0) := by
        refine Finset.sum_congr rfl (fun l hl => ?_)
        have hl' : l ≤ m := by have := Finset.mem_range.mp hl; omega
        by_cases h1 : i < l
        · rw [if_pos h1, if_pos ⟨h1, hl'⟩]
        · rw [if_neg h1, if_neg (fun h => h1 h.1)]
    _ = ∑ l ∈ Finset.range j, (if i < l ∧ l ≤ m then 2 / ((l : ℝ) + 1) else 0) := by
        apply Finset.sum_subset hsub
        intro l _ hl'
        have hlm : ¬ l ≤ m := by
          intro h'
          exact hl' (Finset.mem_range.mpr (by omega))
        rw [if_neg (fun h => hlm h.2)]

lemma W3_ge (i j m : ℕ) (h : j ≤ m + 1) :
    W3N i j m = ∑ l ∈ Finset.range j, if i < l then 2 / ((l : ℝ) + 1) else 0 := by
  rw [W3_range]
  refine Finset.sum_congr rfl (fun l hl => ?_)
  have hl' : l ≤ m := by have := Finset.mem_range.mp hl; omega
  by_cases h1 : i < l
  · rw [if_pos h1, if_pos ⟨h1, hl'⟩]
  · rw [if_neg h1, if_neg (fun h => h1 h.1)]

lemma W3_zero (i j m : ℕ) (h : m ≤ i) : W3N i j m = 0 := by
  rw [W3_range]
  exact Finset.sum_eq_zero (fun l _ => if_neg (fun h' => by omega))

lemma W1_full (i m : ℕ) (h : i ≤ m + 1) :
    W1N i m = ∑ l ∈ Finset.range i, 2 / ((l : ℝ) + 1) := by
  unfold W1N
  refine Finset.sum_congr rfl (fun l hl => ?_)
  have hl' : l ≤ m := by have := Finset.mem_range.mp hl; omega
  rw [if_pos hl']

lemma head_zero (i N : ℕ) (hN : N ≤ i + 1) :
    ∑ l ∈ Finset.range N, (if i < l then 2 / ((l : ℝ) + 1) else 0) = 0 :=
  Finset.sum_eq_zero (fun l hl => if_neg (by have := Finset.mem_range.mp hl; omega))

lemma HbA (i a N : ℕ) (ha : 4 ≤ a) (haN : a ≤ N) :
    ∑ l ∈ Finset.range N, (if i < l then 2 / ((l : ℝ) + 1) else 0) ≤
      ∑ l ∈ Finset.range a, (if i < l then 2 / ((l : ℝ) + 1) else 0) + 2 / 5 * ((N : ℝ) - a) := by
  induction N, haN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_range_succ]
    have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast (le_trans ha hN)
    have hterm : (if i < N then 2 / ((N : ℝ) + 1) else 0) ≤ 2 / 5 := by
      split_ifs
      · rw [div_le_div_iff₀ (show (0 : ℝ) < (N : ℝ) + 1 by positivity)
          (show (0 : ℝ) < 5 by norm_num)]
        linarith
      · norm_num
    push_cast
    linarith

/-! ### The right-hand side -/

noncomputable def RN (i j m : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (m + 1), if n = i ∨ n = j then (44 / 27 : ℝ) else 55 / 108

lemma RN_eq (i j m : ℕ) (hij : i ≠ j) :
    RN i j m = 55 / 108 * ((m : ℝ) + 1) +
      121 / 108 * ((if i ≤ m then (1 : ℝ) else 0) + (if j ≤ m then (1 : ℝ) else 0)) := by
  unfold RN
  have hpt : ∀ n : ℕ, (if n = i ∨ n = j then (44 / 27 : ℝ) else 55 / 108) =
      55 / 108 + 121 / 108 * ((if n = i then (1 : ℝ) else 0) + (if n = j then (1 : ℝ) else 0)) := by
    intro n
    by_cases h1 : n = i
    · have h2 : ¬ n = j := fun h => hij (h1.symm.trans h)
      rw [if_pos (Or.inl h1), if_pos h1, if_neg h2]
      norm_num
    · by_cases h2 : n = j
      · rw [if_pos (Or.inr h2), if_neg h1, if_pos h2]
        norm_num
      · rw [if_neg (show ¬ (n = i ∨ n = j) by tauto), if_neg h1, if_neg h2]
        norm_num
  rw [Finset.sum_congr rfl (fun n _ => hpt n), Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq']
  simp only [Finset.mem_range, Nat.lt_add_one_iff, nsmul_eq_mul]
  push_cast
  ring

lemma R_nonneg (i j m : ℕ) :
    0 ≤ 55 / 108 * ((m : ℝ) + 1) +
      121 / 108 * ((if i ≤ m then (1 : ℝ) else 0) + (if j ≤ m then (1 : ℝ) else 0)) := by
  split_ifs <;> positivity

/-! ### Two rational bounds -/

lemma fracT (t j : ℕ) (h4 : 4 ≤ j) (hjt : j ≤ t + 3) :
    2 / ((j : ℝ) + 1) * ((252 + 30 * (t : ℝ)) / 108 + ((j : ℝ) - 3) * (5 / 18)) ≤
      (120 + 2 * (12 + 30 * ((t : ℝ) + 3 - j)) / 5) / 108 := by
  have hj : (4 : ℝ) ≤ j := by exact_mod_cast h4
  have hjt' : (j : ℝ) ≤ t + 3 := by exact_mod_cast hjt
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ 12 + 30 * ((t : ℝ) + 3 - j) by linarith)
    (show (0 : ℝ) ≤ (j : ℝ) - 4 by linarith)]

lemma fracT2 (t i : ℕ) (h4 : 4 ≤ i) (hit : i ≤ t + 3) :
    2 / ((i : ℝ) + 1) * ((252 + 30 * (t : ℝ)) / 108 + ((i : ℝ) - 3) * (5 / 18) - 5 / 18) ≤
      (120 + 12 * ((t : ℝ) + 3 - i)) / 108 := by
  have hi : (4 : ℝ) ≤ i := by exact_mod_cast h4
  have hit' : (i : ℝ) ≤ t + 3 := by exact_mod_cast hit
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < (i : ℝ) + 1)]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ (t : ℝ) + 3 - i by linarith)
    (show (0 : ℝ) ≤ (i : ℝ) - 4 by linarith)]

/-! ### The scalar inequality -/

noncomputable def GN (i j m : ℕ) : ℝ :=
  W1N i m * |pN i m - pN j m| + (if i ≤ m then 2 / ((i : ℝ) + 1) else 0) * |QN i m - pN j m| +
    W3N i j m * |pN j m| + (if j ≤ m then 2 / ((j : ℝ) + 1) else 0) * |QN j m|

set_option maxHeartbeats 1600000 in
theorem IV (i j m : ℕ) (hij : i < j) : GN i j m ≤ RN i j m := by
  rw [RN_eq i j m (Nat.ne_of_lt hij)]
  unfold GN
  rw [abs_of_nonneg (Qp_nonneg i j m hij), abs_of_nonneg (pN_nonneg j m),
    abs_of_nonneg (QN_nonneg j m)]
  rcases eq_or_ne i 3 with hi3 | hi3
  · -- the row `i = 3`
    subst hi3
    rw [abs_of_nonpos (p3_le j m hij)]
    have hjm' : 4 ≤ j := hij
    rcases Nat.lt_or_ge m 3 with hm | hm
    · have hn3 : ¬ 3 ≤ m := by omega
      have hnj : ¬ j ≤ m := by omega
      rw [p_ge3_small j m (by omega) (by omega), sub_self, neg_zero, mul_zero,
        W3_zero 3 j m (by omega)]
      simp only [if_neg hn3, if_neg hnj]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    · obtain ⟨t, rfl⟩ : ∃ t, m = t + 3 := ⟨m - 3, by omega⟩
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      have h3m : 3 ≤ t + 3 := by omega
      rw [p3_t, pbig_t j t hjm', Qbig_t 3 t le_rfl, W1_full 3 (t + 3) (by omega)]
      simp only [if_pos h3m]
      rcases Nat.lt_or_ge (t + 3) j with hjm | hjm
      · have hnj : ¬ j ≤ t + 3 := by omega
        simp only [if_neg hnj]
        rw [W3_lt 3 j (t + 3) (by omega)]
        have hS := HbA 3 4 (t + 3 + 1) le_rfl (by omega)
        generalize (∑ l ∈ Finset.range (t + 3 + 1),
          if 3 < l then 2 / ((l : ℝ) + 1) else 0) = S at hS ⊢
        norm_num [Finset.sum_range_succ] at hS ⊢
        linarith
      · simp only [if_pos hjm]
        rw [W3_ge 3 j (t + 3) (by omega), Qbig_t j t (by omega)]
        have hS := HbA 3 4 j le_rfl hjm'
        have hT := fracT t j hjm' hjm
        have hj' : (j : ℝ) ≤ t + 3 := by exact_mod_cast hjm
        generalize (∑ l ∈ Finset.range j,
          if 3 < l then 2 / ((l : ℝ) + 1) else 0) = S at hS ⊢
        generalize (2 / ((j : ℝ) + 1) * ((252 + 30 * (t : ℝ)) / 108 +
          ((j : ℝ) - 3) * (5 / 18))) = T at hT ⊢
        norm_num [Finset.sum_range_succ] at hS ⊢
        linarith
  · rw [abs_of_nonneg (pp_nonneg i j m hij hi3)]
    rcases Nat.lt_or_ge m 3 with hm | hm
    · -- small `m`
      rcases Nat.lt_or_ge j 3 with hj | hj
      · interval_cases m <;> interval_cases j <;> interval_cases i <;>
          norm_num [W1N, W3_range, pN, QN, aN, Finset.sum_range_succ]
      · have hnj : ¬ j ≤ m := by omega
        simp only [if_neg hnj, zero_mul, add_zero]
        rw [W3_lt i j m (by omega), p_ge3_small j m hj (by omega)]
        rcases Nat.lt_or_ge i 3 with hi | hi
        · interval_cases m <;> interval_cases i <;>
            norm_num [W1N, pN, QN, aN, Finset.sum_range_succ]
        · have hni : ¬ i ≤ m := by omega
          rw [p_ge3_small i m hi (by omega), sub_self, mul_zero, head_zero i (m + 1) (by omega)]
          simp only [if_neg hni]
          have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith
    · obtain ⟨t, rfl⟩ : ∃ t, m = t + 3 := ⟨m - 3, by omega⟩
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      rcases Nat.lt_or_ge j 4 with hj | hj
      · -- both indices at most three
        have hi' : i ≤ t + 3 := by omega
        have hj' : j ≤ t + 3 := by omega
        simp only [if_pos hi', if_pos hj']
        rw [W1_full i (t + 3) (by omega), W3_ge i j (t + 3) (by omega), pN_t i t, pN_t j t,
          QN_t i t, QN_t j t]
        interval_cases j <;> interval_cases i <;>
          norm_num [pT, QT, Finset.sum_range_succ] <;> linarith
      · rw [pbig_t j t hj]
        rcases Nat.lt_or_ge i 3 with hi | hi
        · have hi' : i ≤ t + 3 := by omega
          simp only [if_pos hi']
          rw [W1_full i (t + 3) (by omega), pN_t i t, QN_t i t]
          rcases Nat.lt_or_ge (t + 3) j with hjm | hjm
          · have hnj : ¬ j ≤ t + 3 := by omega
            simp only [if_neg hnj, zero_mul, add_zero]
            rw [W3_lt i j (t + 3) (by omega)]
            have hS := HbA i 4 (t + 3 + 1) le_rfl (by omega)
            generalize (∑ l ∈ Finset.range (t + 3 + 1),
              if i < l then 2 / ((l : ℝ) + 1) else 0) = S at hS ⊢
            interval_cases i <;> norm_num [pT, QT, Finset.sum_range_succ] at hS ⊢ <;> linarith
          · simp only [if_pos hjm]
            rw [W3_ge i j (t + 3) (by omega), Qbig_t j t (by omega)]
            have hS := HbA i 4 j le_rfl hj
            have hT := fracT t j hj hjm
            have hj' : (j : ℝ) ≤ t + 3 := by exact_mod_cast hjm
            generalize (∑ l ∈ Finset.range j,
              if i < l then 2 / ((l : ℝ) + 1) else 0) = S at hS ⊢
            generalize (2 / ((j : ℝ) + 1) * ((252 + 30 * (t : ℝ)) / 108 +
              ((j : ℝ) - 3) * (5 / 18))) = T at hT ⊢
            interval_cases i <;> norm_num [pT, QT, Finset.sum_range_succ] at hS ⊢ <;> linarith
        · have hi4 : 4 ≤ i := by omega
          rw [pbig_t i t hi4, sub_self, mul_zero, zero_add]
          rcases Nat.lt_or_ge (t + 3) i with him | him
          · have hni : ¬ i ≤ t + 3 := by omega
            have hnj : ¬ j ≤ t + 3 := by omega
            rw [W3_zero i j (t + 3) (by omega)]
            simp only [if_neg hni, if_neg hnj]
            push_cast
            linarith
          · simp only [if_pos him]
            rw [Qbig_t i t (by omega)]
            have hT2 := fracT2 t i hi4 him
            have hi4' : (4 : ℝ) ≤ i := by exact_mod_cast hi4
            have hi' : (i : ℝ) ≤ t + 3 := by exact_mod_cast him
            generalize (2 / ((i : ℝ) + 1) * ((252 + 30 * (t : ℝ)) / 108 +
              ((i : ℝ) - 3) * (5 / 18) - 5 / 18)) = T2 at hT2 ⊢
            rcases Nat.lt_or_ge (t + 3) j with hjm | hjm
            · have hnj : ¬ j ≤ t + 3 := by omega
              simp only [if_neg hnj, zero_mul, add_zero]
              rw [W3_lt i j (t + 3) (by omega)]
              have hS := HbA i (i + 1) (t + 3 + 1) (by omega) (by omega)
              rw [head_zero i (i + 1) le_rfl] at hS
              generalize (∑ l ∈ Finset.range (t + 3 + 1),
                if i < l then 2 / ((l : ℝ) + 1) else 0) = S at hS ⊢
              push_cast at hS ⊢
              linarith
            · simp only [if_pos hjm]
              rw [W3_ge i j (t + 3) (by omega), Qbig_t j t (by omega)]
              have hS := HbA i (i + 1) j (by omega) (by omega)
              rw [head_zero i (i + 1) le_rfl] at hS
              have hT := fracT t j hj hjm
              have hj' : (j : ℝ) ≤ t + 3 := by exact_mod_cast hjm
              have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
              generalize (∑ l ∈ Finset.range j,
                if i < l then 2 / ((l : ℝ) + 1) else 0) = S at hS ⊢
              generalize (2 / ((j : ℝ) + 1) * ((252 + 30 * (t : ℝ)) / 108 +
                ((j : ℝ) - 3) * (5 / 18))) = T at hT ⊢
              push_cast at hS ⊢
              linarith

/-! ### The matrix `A53` satisfies the hypotheses of Lemma 5.2 -/

lemma conv_Iio {k : ℕ} (g : ℕ → ℝ) (i : Fin k) :
    ∑ l ∈ Finset.Iio i, g l.val = ∑ x ∈ Finset.range i.val, g x := by
  rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.sum_map]
  rfl

lemma conv_Ioo {k : ℕ} (g : ℕ → ℝ) (i j : Fin k) :
    ∑ l ∈ Finset.Ioo i j, g l.val = ∑ x ∈ Finset.Ioo i.val j.val, g x := by
  rw [← Fin.map_valEmbedding_Ioo, Finset.sum_map]
  rfl

lemma conv_Iic {k : ℕ} (g : ℕ → ℝ) (i : Fin k) :
    ∑ l ∈ Finset.Iic i, g l.val = ∑ x ∈ Finset.range (i.val + 1), g x := by
  rw [Nat.range_succ_eq_Iic, ← Fin.map_valEmbedding_Iic, Finset.sum_map]
  rfl

lemma A53_symm {k : ℕ} : (A53 k).IsSymm :=
  Matrix.IsSymm.ext (fun m n => by rw [A_eq, A_eq, aN_symm])

lemma A53_cond {k : ℕ} [NeZero k] : Lemma51Conditions (A53 k) := by
  unfold Lemma51Conditions
  refine ⟨⟨?_, fun m n => by rw [A_eq]; exact aN_le_one _ _⟩, fun ℓ => ?_, fun ℓ r _ => ?_⟩
  · rw [A_eq]
    simp [aN]
  · refine Finset.sum_nonneg (fun m _ => ?_)
    have e : ∑ n ∈ Finset.Iic ℓ, A53 k m n = pN m.val ℓ.val := by
      simp only [A_eq]
      exact conv_Iic (fun x => aN m.val x) ℓ
    rw [e]
    exact pN_nonneg _ _
  · refine Finset.sum_nonneg (fun m hm => Finset.sum_nonneg (fun n hn => ?_))
    rw [A_eq]
    apply aN_nonneg'
    have h1 := Fin.le_iff_val_le_val.mp (Finset.mem_Iic.mp hm)
    have h2 := Fin.lt_iff_val_lt_val.mp (Finset.mem_Ioc.mp hn).1
    omega

/-! ### Abel summation over the extreme rays of the sorted cone -/

noncomputable def extU {k : ℕ} (u : Fin k → ℝ) (n : ℕ) : ℝ := if h : n < k then u ⟨n, h⟩ else 0

lemma extU_val {k : ℕ} (u : Fin k → ℝ) (m : Fin k) : extU u m.val = u m := by
  simp [extU, m.isLt]

lemma extU_k {k : ℕ} (u : Fin k → ℝ) : extU u k = 0 := by
  simp [extU]

noncomputable def Lam {k : ℕ} (u : Fin k → ℝ) (m : Fin k) : ℝ :=
  u m - (if h : m.val + 1 < k then u ⟨m.val + 1, h⟩ else 0)

lemma Lam_eq {k : ℕ} (u : Fin k → ℝ) (m : Fin k) : Lam u m = extU u m.val - extU u (m.val + 1) := by
  unfold Lam
  rw [extU_val] <;> rfl

lemma Lam_nonneg {k : ℕ} (u : Fin k → ℝ) (hu0 : ∀ x, 0 ≤ u x) (hanti : Antitone u) (m : Fin k) :
    0 ≤ Lam u m := by
  unfold Lam
  split_ifs with h
  · have hle : m ≤ (⟨m.val + 1, h⟩ : Fin k) := by
      rw [Fin.le_iff_val_le_val]
      show m.val ≤ m.val + 1
      omega
    linarith [hanti hle]
  · linarith [hu0 m]

lemma tele_nat (U : ℕ → ℝ) (x : ℕ) : ∀ K : ℕ, x ≤ K →
    ∑ n ∈ Finset.range K, (if x ≤ n then U n - U (n + 1) else 0) = U x - U K := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
    rw [sub_self]
    exact Finset.sum_eq_zero (fun n hn => if_neg (by have := Finset.mem_range.mp hn; omega))
  | succ K hK ih =>
    rw [Finset.sum_range_succ, ih, if_pos hK]
    ring

lemma tele {k : ℕ} (u : Fin k → ℝ) (x : Fin k) :
    u x = ∑ m : Fin k, if x ≤ m then Lam u m else 0 := by
  have hsum : ∑ m : Fin k, (if x ≤ m then Lam u m else 0) =
      ∑ n ∈ Finset.range k, (if x.val ≤ n then extU u n - extU u (n + 1) else 0) := by
    calc ∑ m : Fin k, (if x ≤ m then Lam u m else 0)
        = ∑ m : Fin k, (if x.val ≤ m.val then extU u m.val - extU u (m.val + 1) else 0) := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [Lam_eq]
          by_cases h : x ≤ m
          · rw [if_pos h, if_pos (Fin.le_iff_val_le_val.mp h)]
          · rw [if_neg h, if_neg (fun h' => h (Fin.le_iff_val_le_val.mpr h'))]
      _ = ∑ n ∈ Finset.range k, (if x.val ≤ n then extU u n - extU u (n + 1) else 0) :=
          Fin.sum_univ_eq_sum_range (fun n => if x.val ≤ n then extU u n - extU u (n + 1) else 0) k
  rw [hsum, tele_nat (extU u) x.val k x.isLt.le, extU_val, extU_k, sub_zero]

lemma flat_expand {k : ℕ} (u : Fin k → ℝ) (l n : Fin k) :
    MultiwayCut.flat u l n = ∑ m : Fin k, if l ≤ m ∧ n ≤ m then Lam u m else 0 := by
  show (if n < l then u l else u n) = _
  by_cases h : n < l
  · rw [if_pos h, tele u l]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases hl : l ≤ m
    · rw [if_pos hl, if_pos ⟨hl, h.le.trans hl⟩]
    · rw [if_neg hl, if_neg (fun h' => hl h'.1)]
  · rw [if_neg h, tele u n]
    push_neg at h
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases hn : n ≤ m
    · rw [if_pos hn, if_pos ⟨h.trans hn, hn⟩]
    · rw [if_neg hn, if_neg (fun h' => hn h'.2)]

noncomputable def Pf {k : ℕ} (D : Fin k → ℝ) (m : Fin k) : ℝ := ∑ n : Fin k, if n ≤ m then D n else 0

lemma dot_expand {k : ℕ} (D u : Fin k → ℝ) (l : Fin k) :
    D ⬝ᵥ MultiwayCut.flat u l = ∑ m : Fin k, if l ≤ m then Lam u m * Pf D m else 0 := by
  rw [dotProduct]
  simp_rw [flat_expand u l, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  by_cases hl : l ≤ m
  · rw [if_pos hl]
    unfold Pf
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases hn : n ≤ m
    · rw [if_pos ⟨hl, hn⟩, if_pos hn]
      ring
    · rw [if_neg (fun h => hn h.2), if_neg hn]
      ring
  · rw [if_neg hl]
    exact Finset.sum_eq_zero (fun n _ => by rw [if_neg (fun h => hl h.1), mul_zero])

lemma weighted {k : ℕ} (S : Finset (Fin k)) (w : Fin k → ℝ) (hw : ∀ l, 0 ≤ w l)
    (D u : Fin k → ℝ) (hu0 : ∀ x, 0 ≤ u x) (hanti : Antitone u) :
    ∑ l ∈ S, w l * |D ⬝ᵥ MultiwayCut.flat u l| ≤
      ∑ m : Fin k, Lam u m * ((∑ l ∈ S, if l ≤ m then w l else 0) * |Pf D m|) := by
  calc ∑ l ∈ S, w l * |D ⬝ᵥ MultiwayCut.flat u l|
      ≤ ∑ l ∈ S, w l * ∑ m : Fin k, (if l ≤ m then Lam u m * |Pf D m| else 0) := by
        refine Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left ?_ (hw l))
        rw [dot_expand]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun m _ => ?_))
        split_ifs
        · exact le_of_eq (by rw [abs_mul, abs_of_nonneg (Lam_nonneg u hu0 hanti m)])
        · simp
    _ = ∑ m : Fin k, Lam u m * ((∑ l ∈ S, if l ≤ m then w l else 0) * |Pf D m|) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        split_ifs <;> ring

lemma weighted' {k : ℕ} (S : Finset (Fin k)) (D u : Fin k → ℝ) (hu0 : ∀ x, 0 ≤ u x)
    (hanti : Antitone u) :
    ∑ l ∈ S, 2 / ((l.val : ℝ) + 1) * |D ⬝ᵥ MultiwayCut.flat u l| ≤
      ∑ m : Fin k, Lam u m *
        ((∑ l ∈ S, if l ≤ m then 2 / ((l.val : ℝ) + 1) else 0) * |Pf D m|) :=
  weighted S (fun l => 2 / ((l.val : ℝ) + 1)) (fun l => div_nonneg (by norm_num) (by positivity))
    D u hu0 hanti

lemma weighted1 {k : ℕ} (i : Fin k) (D u : Fin k → ℝ) (hu0 : ∀ x, 0 ≤ u x)
    (hanti : Antitone u) :
    2 / ((i.val : ℝ) + 1) * |D ⬝ᵥ MultiwayCut.flat u i| ≤
      ∑ m : Fin k, Lam u m * ((if i ≤ m then 2 / ((i.val : ℝ) + 1) else 0) * |Pf D m|) := by
  have h := weighted' {i} D u hu0 hanti
  simp only [Finset.sum_singleton] at h
  exact h

lemma conv_Pf {k : ℕ} (h : ℕ → ℝ) (m : Fin k) :
    ∑ n : Fin k, (if n ≤ m then h n.val else 0) = ∑ x ∈ Finset.range (m.val + 1), h x := by
  calc ∑ n : Fin k, (if n ≤ m then h n.val else 0)
      = ∑ n : Fin k, (if n.val ≤ m.val then h n.val else 0) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        by_cases hn : n ≤ m
        · rw [if_pos hn, if_pos (Fin.le_iff_val_le_val.mp hn)]
        · rw [if_neg hn, if_neg (fun h' => hn (Fin.le_iff_val_le_val.mpr h'))]
    _ = ∑ x ∈ Finset.range k, (if x ≤ m.val then h x else 0) :=
        Fin.sum_univ_eq_sum_range (fun x => if x ≤ m.val then h x else 0) k
    _ = ∑ x ∈ Finset.range (m.val + 1), h x := by
        rw [← Finset.sum_filter]
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_range]
        have := m.isLt
        constructor
        · intro hx
          omega
        · intro hx
          omega

lemma Pf_sub {k : ℕ} (D E : Fin k → ℝ) (m : Fin k) : Pf (D - E) m = Pf D m - Pf E m := by
  unfold Pf
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases hn : n ≤ m
  · rw [if_pos hn, if_pos hn, if_pos hn, Pi.sub_apply]
  · rw [if_neg hn, if_neg hn, if_neg hn, sub_zero]

lemma Pf_A {k : ℕ} (r m : Fin k) : Pf (A53 k r) m = pN r.val m.val := by
  unfold Pf
  simp only [A_eq]
  exact conv_Pf (fun x => aN r.val x) m

lemma Pf_sumIic {k : ℕ} (i m : Fin k) :
    Pf (∑ l ∈ Finset.Iic i, A53 k l) m = QN i.val m.val := by
  have e : Pf (∑ l ∈ Finset.Iic i, A53 k l) m = ∑ l ∈ Finset.Iic i, Pf (A53 k l) m := by
    unfold Pf
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    have hs : (∑ l ∈ Finset.Iic i, A53 k l) n = ∑ l ∈ Finset.Iic i, A53 k l n :=
      Finset.sum_apply n (Finset.Iic i) (fun l => A53 k l)
    by_cases hn : n ≤ m
    · exact (if_pos hn).trans (hs.trans (Finset.sum_congr rfl (fun l _ => (if_pos hn).symm)))
    · exact (if_neg hn).trans (Finset.sum_eq_zero (fun l _ => if_neg hn)).symm
  rw [e]
  simp only [Pf_A]
  exact conv_Iic (fun x => pN x m.val) i

lemma conv_W1 {k : ℕ} (i m : Fin k) :
    (∑ l ∈ Finset.Iio i, if l ≤ m then 2 / ((l.val : ℝ) + 1) else 0) = W1N i.val m.val := by
  have e : (∑ l ∈ Finset.Iio i, if l ≤ m then 2 / ((l.val : ℝ) + 1) else 0) =
      ∑ l ∈ Finset.Iio i, (if l.val ≤ m.val then 2 / ((l.val : ℝ) + 1) else 0) := by
    refine Finset.sum_congr rfl (fun l _ => ?_)
    by_cases hl : l ≤ m
    · rw [if_pos hl, if_pos (Fin.le_iff_val_le_val.mp hl)]
    · rw [if_neg hl, if_neg (fun h' => hl (Fin.le_iff_val_le_val.mpr h'))]
  rw [e]
  exact conv_Iio (fun x : ℕ => if x ≤ m.val then 2 / ((x : ℝ) + 1) else 0) i

lemma conv_W3 {k : ℕ} (i j m : Fin k) :
    (∑ l ∈ Finset.Ioo i j, if l ≤ m then 2 / ((l.val : ℝ) + 1) else 0) = W3N i.val j.val m.val := by
  have e : (∑ l ∈ Finset.Ioo i j, if l ≤ m then 2 / ((l.val : ℝ) + 1) else 0) =
      ∑ l ∈ Finset.Ioo i j, (if l.val ≤ m.val then 2 / ((l.val : ℝ) + 1) else 0) := by
    refine Finset.sum_congr rfl (fun l _ => ?_)
    by_cases hl : l ≤ m
    · rw [if_pos hl, if_pos (Fin.le_iff_val_le_val.mp hl)]
    · rw [if_neg hl, if_neg (fun h' => hl (Fin.le_iff_val_le_val.mpr h'))]
  rw [e]
  exact conv_Ioo (fun x : ℕ => if x ≤ m.val then 2 / ((x : ℝ) + 1) else 0) i j

lemma if_conv {k : ℕ} (i m : Fin k) (x : ℝ) :
    (if i ≤ m then x else 0) = (if i.val ≤ m.val then x else 0) := by
  by_cases h : i ≤ m
  · rw [if_pos h, if_pos (Fin.le_iff_val_le_val.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (Fin.le_iff_val_le_val.mpr h'))]

lemma rhs_eq {k : ℕ} (u : Fin k → ℝ) (i j : Fin k) (hij : i ≠ j) :
    44 / 27 * (u i + u j) + 55 / 108 * ∑ ℓ ∈ Finset.univ \ {i, j}, u ℓ =
      ∑ m : Fin k, Lam u m * RN i.val j.val m.val := by
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have h1 : 44 / 27 * (u i + u j) + 55 / 108 * ∑ ℓ ∈ Finset.univ \ {i, j}, u ℓ =
      ∑ n : Fin k, (if n.val = i.val ∨ n.val = j.val then (44 / 27 : ℝ) else 55 / 108) * u n := by
    rw [← Finset.sum_sdiff (Finset.subset_univ {i, j}), Finset.sum_pair hij, Finset.mul_sum]
    have e1 : ∀ n ∈ Finset.univ \ {i, j},
        (if n.val = i.val ∨ n.val = j.val then (44 / 27 : ℝ) else 55 / 108) * u n =
          55 / 108 * u n := by
      intro n hn
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hn
      rw [if_neg (show ¬ (n.val = i.val ∨ n.val = j.val) from fun h => hn.2 (h.elim
        (fun h' => Or.inl (Fin.ext h')) (fun h' => Or.inr (Fin.ext h'))))]
    rw [Finset.sum_congr rfl e1, if_pos (Or.inl rfl), if_pos (Or.inr rfl)]
    ring
  rw [h1]
  calc ∑ n : Fin k, (if n.val = i.val ∨ n.val = j.val then (44 / 27 : ℝ) else 55 / 108) * u n
      = ∑ n : Fin k, (if n.val = i.val ∨ n.val = j.val then (44 / 27 : ℝ) else 55 / 108) *
          ∑ m : Fin k, (if n ≤ m then Lam u m else 0) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [← tele u n]
    _ = ∑ m : Fin k, Lam u m * ∑ n : Fin k,
          (if n ≤ m then (if n.val = i.val ∨ n.val = j.val then (44 / 27 : ℝ) else 55 / 108)
            else 0) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
        split_ifs <;> ring
    _ = ∑ m : Fin k, Lam u m * RN i.val j.val m.val := by
        refine Finset.sum_congr rfl (fun m _ => ?_)
        congr 1
        exact conv_Pf (fun x => if x = i.val ∨ x = j.val then (44 / 27 : ℝ) else 55 / 108) m

lemma main_ineq {k : ℕ} (u : Fin k → ℝ) (i j : Fin k) (hu : u ∈ stdSimplex ℝ (Fin k))
    (hanti : Antitone u) (hij : i < j) :
    (∑ l ∈ Finset.Iio i, 2 / ((l.val : ℝ) + 1) * |(A53 k i - A53 k j) ⬝ᵥ MultiwayCut.flat u l| +
        2 / ((i.val : ℝ) + 1) *
          |((∑ l ∈ Finset.Iic i, A53 k l) - A53 k j) ⬝ᵥ MultiwayCut.flat u i| +
        ∑ l ∈ Finset.Ioo i j, 2 / ((l.val : ℝ) + 1) * |A53 k j ⬝ᵥ MultiwayCut.flat u l| +
        2 / ((j.val : ℝ) + 1) * |(∑ l ∈ Finset.Iic j, A53 k l) ⬝ᵥ MultiwayCut.flat u j|) ≤
      44 / 27 * (u i + u j) + 55 / 108 * ∑ ℓ ∈ Finset.univ \ {i, j}, u ℓ := by
  have hu0 : ∀ x, 0 ≤ u x := hu.1
  have h1 := weighted' (Finset.Iio i) (A53 k i - A53 k j) u hu0 hanti
  have h2 := weighted1 i ((∑ l ∈ Finset.Iic i, A53 k l) - A53 k j) u hu0 hanti
  have h3 := weighted' (Finset.Ioo i j) (A53 k j) u hu0 hanti
  have h4 := weighted1 j (∑ l ∈ Finset.Iic j, A53 k l) u hu0 hanti
  rw [rhs_eq u i j (ne_of_lt hij)]
  refine le_trans (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun m _ => ?_)
  rw [← mul_add, ← mul_add, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (Lam_nonneg u hu0 hanti m)
  simp only [Pf_sub, Pf_A, Pf_sumIic]
  rw [conv_W1, conv_W3, if_conv i m, if_conv j m]
  exact IV i.val j.val m.val hij

end Aux_MultiwayCut_lemma_5_4

open MultiwayCut Filter Topology in
theorem solution {k : ℕ} [NeZero k] (u : Fin k → ℝ) (i j : Fin k) :
    IJDensityLE (fun x y => sepCKR (quadTransform (A53 k) x) (quadTransform (A53 k) y))
      (Equiv.refl (Fin k)) i j u
      (44 / 27 * (u i + u j) + 55 / 108 * ∑ ℓ ∈ Finset.univ \ {i, j}, u ℓ) := by
  by_cases H : u ∈ stdSimplex ℝ (Fin k) ∧ Antitone u ∧ i < j
  · obtain ⟨hu, hanti, hij⟩ := H
    have h52 := Aux_MultiwayCut_lemma_5_2.L52 (A53 k) Aux_MultiwayCut_lemma_5_4.A53_symm
      Aux_MultiwayCut_lemma_5_4.A53_cond u i j
    have hle := Aux_MultiwayCut_lemma_5_4.main_ineq u i j hu hanti hij
    intro η hη
    filter_upwards [h52 η hη] with ε hε hedge
    exact (hε hedge).trans (by linarith [hle])
  · intro η _
    refine Filter.Eventually.of_forall (fun ε hε => ?_)
    exfalso
    obtain ⟨h1, _, h3, _, h5, _⟩ := hε
    exact H ⟨h1, fun a b hab => h5 hab, h3⟩
