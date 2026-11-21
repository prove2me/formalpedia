-- Prove2me | solution 1 for MultiwayCut.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:42:30.63559+00:00
-- url     : https://prove2.me/submissions/d3cfee7f-448b-4b08-a2c8-905469ba6777

import Mathlib
import Definitions.Def_MultiwayCut_CKR
import Definitions.Def_MultiwayCut_CutDensity
import Definitions.Def_MultiwayCut_Transformation

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
theorem solution {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsSymm)
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
