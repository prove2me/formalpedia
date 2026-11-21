-- Prove2me | solution 1 for MultiwayCut.theorem_1_2_density
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:17:40.348011+00:00
-- url     : https://prove2.me/submissions/fe6a6b36-f968-49a5-8255-dc6747663424

import Mathlib
import Definitions.Def_MultiwayCut_Algorithm3
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

open MultiwayCut Aux_MultiwayCut_lemma_5_2 Filter Topology in
theorem Aux_MultiwayCut_lemma_5_2.L52U {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.IsSymm) (hcond : Lemma51Conditions A) (u : Fin k → ℝ) (i j : Fin k) (ε : ℝ)
    (hedge : IsIJEdge (Equiv.refl (Fin k)) i j ε u
      (ijShift u ((Equiv.refl (Fin k)) i) ((Equiv.refl (Fin k)) j) ε)) :
    sepCKR (quadTransform A u) (quadTransform A
        (ijShift u ((Equiv.refl (Fin k)) i) ((Equiv.refl (Fin k)) j) ε)) ≤
      ε * (∑ l ∈ Finset.Iio i, 2 / ((l.val : ℝ) + 1) * |(A i - A j) ⬝ᵥ flat u l| +
        2 / ((i.val : ℝ) + 1) * |((∑ l ∈ Finset.Iic i, A l) - A j) ⬝ᵥ flat u i| +
        ∑ l ∈ Finset.Ioo i j, 2 / ((l.val : ℝ) + 1) * |A j ⬝ᵥ flat u l| +
        2 / ((j.val : ℝ) + 1) * |(∑ l ∈ Finset.Iic j, A l) ⬝ᵥ flat u j|) +
      ε ^ 2 * ∑ ℓ : Fin k, |flat (Pi.single i 1 - Pi.single j 1 : Fin k → ℝ) ℓ ⬝ᵥ
        (A *ᵥ flat (Pi.single i 1 - Pi.single j 1 : Fin k → ℝ) ℓ)| / ((ℓ.val : ℝ) + 1) := by
  obtain ⟨d, hd⟩ : ∃ d : Fin k → ℝ, d = Pi.single i 1 - Pi.single j 1 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ,
      K = ∑ ℓ : Fin k, |flat d ℓ ⬝ᵥ (A *ᵥ flat d ℓ)| / ((ℓ.val : ℝ) + 1) := ⟨_, rfl⟩
  obtain ⟨hu, hv, hij, hε0, hanti, hgi, hgj, _⟩ := hedge
  simp only [Equiv.refl_apply, Equiv.coe_refl, Function.comp_id] at hanti hgi hgj hv ⊢
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
  rw [hG, hK, hd] at hsum
  exact hsep.trans hsum


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


namespace Aux_MultiwayCut_theorem_1_2_density

open MultiwayCut MeasureTheory ProbabilityTheory Set

/-! ### Shifts -/

lemma shA {k : ℕ} (z : Fin k → ℝ) (a b : Fin k) (ε : ℝ) (c : Fin k) :
    ijShift z a b ε c =
      z c + ε * ((if c = a then (1:ℝ) else 0) - (if c = b then (1:ℝ) else 0)) := by
  simp only [ijShift, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul]

lemma sh_a {k : ℕ} (z : Fin k → ℝ) {a b : Fin k} (h : a ≠ b) (ε : ℝ) :
    ijShift z a b ε a = z a + ε := by
  rw [shA, if_pos rfl, if_neg h]; ring

lemma sh_b {k : ℕ} (z : Fin k → ℝ) {a b : Fin k} (h : a ≠ b) (ε : ℝ) :
    ijShift z a b ε b = z b - ε := by
  rw [shA, if_neg (Ne.symm h), if_pos rfl]; ring

lemma sh_o {k : ℕ} (z : Fin k → ℝ) {a b c : Fin k} (hca : c ≠ a) (hcb : c ≠ b) (ε : ℝ) :
    ijShift z a b ε c = z c := by
  rw [shA, if_neg hca, if_neg hcb]; ring

/-! ### The exponential law -/

instance instE : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure (by norm_num)

lemma gpdf_eq (x : ℝ) :
    gammaPDF 1 1 x = if 0 ≤ x then ENNReal.ofReal (Real.exp (-x)) else 0 := by
  rw [gammaPDF_eq]
  split_ifs with h
  · congr 1
    simp
  · simp

lemma measurable_gpdf : Measurable (gammaPDF 1 1) :=
  (measurable_gammaPDFReal 1 1).ennreal_ofReal

lemma E_Ioi (t : ℝ) (ht : 0 ≤ t) :
    expMeasure 1 (Ioi t) = ENNReal.ofReal (Real.exp (-t)) := by
  rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Ioi,
    setLIntegral_congr_fun (f := gammaPDF 1 1) (g := fun x => ENNReal.ofReal (Real.exp (-x)))
      measurableSet_Ioi (fun x hx => by rw [gpdf_eq, if_pos (le_trans ht (le_of_lt hx))]),
    ← ofReal_integral_eq_lintegral_ofReal, integral_exp_neg_Ioi]
  · have hI : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi t) := by
      simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) t
    exact hI
  · exact Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)

lemma E_Iio0 : expMeasure 1 (Iio (0 : ℝ)) = 0 := by
  rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

lemma E_singleton (c : ℝ) : expMeasure 1 {c} = 0 := by
  rw [expMeasure, gammaMeasure]
  exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

lemma lint_E (g : ℝ → ENNReal) (hg : Measurable g) (c : ℝ) (hc : 0 ≤ c)
    (hgx : ∀ x, 0 ≤ x → g x = ENNReal.ofReal (Real.exp (-(c * x)))) :
    ∫⁻ x, g x ∂(expMeasure 1) = ENNReal.ofReal (1 / (c + 1)) := by
  rw [expMeasure, gammaMeasure, lintegral_withDensity_eq_lintegral_mul _ measurable_gpdf hg]
  have h1 : (gammaPDF 1 1 * g) =
      (Ici (0 : ℝ)).indicator (fun x => ENNReal.ofReal (Real.exp ((-(c + 1)) * x))) := by
    funext x
    simp only [Pi.mul_apply]
    rw [gpdf_eq]
    by_cases hx : 0 ≤ x
    · rw [if_pos hx, hgx x hx, indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    · rw [if_neg hx, zero_mul, indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx)]
  have hneg : -(c + 1) < 0 := by linarith
  rw [h1, lintegral_indicator measurableSet_Ici, ← ofReal_integral_eq_lintegral_ofReal,
    integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi hneg]
  · congr 1
    rw [mul_zero, Real.exp_zero, neg_div_neg_eq]
  · have hI : IntegrableOn (fun x : ℝ => Real.exp ((-(c + 1)) * x)) (Ici 0) :=
      (integrableOn_exp_mul_Ioi hneg 0).congr_set_ae Ioi_ae_eq_Ici.symm
    exact hI
  · exact Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)

/-! ### Races between exponential clocks -/

def Win {n : ℕ} (w : Fin (n + 1) → ℝ) (l : Fin (n + 1)) : Set (Fin (n + 1) → ℝ) :=
  {Z | ∀ m, m ≠ l → 0 < w m → Z l * w m < Z m * w l}

def Bad {n : ℕ} (w : Fin (n + 1) → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {Z | (∃ m, Z m < 0) ∨ ∃ m m', m ≠ m' ∧ 0 < w m ∧ 0 < w m' ∧ Z m * w m' = Z m' * w m}

lemma win_meas {n : ℕ} (w : Fin (n + 1) → ℝ) (l : Fin (n + 1)) : MeasurableSet (Win w l) := by
  have e : Win w l = ⋂ m, {Z : Fin (n + 1) → ℝ | m ≠ l → 0 < w m → Z l * w m < Z m * w l} := by
    ext Z
    simp [Win]
  rw [e]
  refine MeasurableSet.iInter (fun m => ?_)
  by_cases h : m ≠ l ∧ 0 < w m
  · have e2 : {Z : Fin (n + 1) → ℝ | m ≠ l → 0 < w m → Z l * w m < Z m * w l} =
        {Z | Z l * w m < Z m * w l} := by
      ext Z
      simp only [Set.mem_setOf_eq]
      exact ⟨fun hZ => hZ h.1 h.2, fun hZ _ _ => hZ⟩
    rw [e2]
    exact measurableSet_lt ((measurable_pi_apply l).mul_const _)
      ((measurable_pi_apply m).mul_const _)
  · have e2 : {Z : Fin (n + 1) → ℝ | m ≠ l → 0 < w m → Z l * w m < Z m * w l} = Set.univ := by
      ext Z
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ h
    rw [e2]
    exact MeasurableSet.univ

lemma race {n : ℕ} (w : Fin (n + 1) → ℝ) (hw : ∀ m, 0 ≤ w m) (l : Fin (n + 1)) (hl : 0 < w l) :
    clockLaw (n + 1) (Win w l) = ENNReal.ofReal (w l / ∑ m, w m) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => expMeasure (1 : ℝ)) l
  set T : Set (ℝ × (Fin n → ℝ)) :=
    {p | ∀ j : Fin n, 0 < w (l.succAbove j) → p.1 * w (l.succAbove j) < p.2 j * w l} with hTdef
  have hT : MeasurableSet T := by
    have e : T = ⋂ j : Fin n, {p : ℝ × (Fin n → ℝ) |
        0 < w (l.succAbove j) → p.1 * w (l.succAbove j) < p.2 j * w l} := by
      ext p
      simp [hTdef]
    rw [e]
    refine MeasurableSet.iInter (fun j => ?_)
    by_cases hj : 0 < w (l.succAbove j)
    · have e2 : {p : ℝ × (Fin n → ℝ) |
          0 < w (l.succAbove j) → p.1 * w (l.succAbove j) < p.2 j * w l} =
          {p | p.1 * w (l.succAbove j) < p.2 j * w l} := by
        ext p
        simp only [Set.mem_setOf_eq]
        exact ⟨fun hp => hp hj, fun hp _ => hp⟩
      rw [e2]
      exact measurableSet_lt (measurable_fst.mul_const _)
        (((measurable_pi_apply j).comp measurable_snd).mul_const _)
    · have e2 : {p : ℝ × (Fin n → ℝ) |
          0 < w (l.succAbove j) → p.1 * w (l.succAbove j) < p.2 j * w l} = Set.univ := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro h1
        exact absurd h1 hj
      rw [e2]
      exact MeasurableSet.univ
  have hWin : Win w l = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) l) ⁻¹' T := by
    ext Z
    simp only [Win, Set.mem_setOf_eq, Set.mem_preimage, hTdef]
    constructor
    · intro h j hj
      exact h _ (Fin.succAbove_ne l j) hj
    · intro h m hm hwm
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hm
      exact h j hwm
  have hsum : ∑ m, w m = w l + ∑ j : Fin n, w (l.succAbove j) := Fin.sum_univ_succAbove w l
  have hS0 : 0 ≤ ∑ j : Fin n, w (l.succAbove j) := Finset.sum_nonneg (fun j _ => hw _)
  rw [hWin, clockLaw, hmp.measure_preimage hT.nullMeasurableSet, Measure.prod_apply hT]
  have hmeas : Measurable fun x : ℝ =>
      (Measure.pi fun _ : Fin n => expMeasure (1 : ℝ)) (Prod.mk x ⁻¹' T) :=
    measurable_measure_prodMk_left hT
  have key := lint_E (fun x : ℝ =>
      (Measure.pi fun _ : Fin n => expMeasure (1 : ℝ)) (Prod.mk x ⁻¹' T)) hmeas
    ((∑ j : Fin n, w (l.succAbove j)) / w l) (div_nonneg hS0 hl.le) (by
      intro x hx
      have hslice : Prod.mk x ⁻¹' T = Set.pi Set.univ (fun j : Fin n =>
          if 0 < w (l.succAbove j) then Ioi (x * w (l.succAbove j) / w l) else Set.univ) := by
        ext y
        simp only [Set.mem_preimage, hTdef, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
          true_implies]
        refine forall_congr' (fun j => ?_)
        by_cases hj : 0 < w (l.succAbove j)
        · rw [if_pos hj, Set.mem_Ioi, div_lt_iff₀ hl]
          exact ⟨fun h => h hj, fun h _ => h⟩
        · rw [if_neg hj]
          exact ⟨fun _ => Set.mem_univ _, fun _ h => absurd h hj⟩
      have hfac : ∀ j : Fin n, expMeasure 1 (if 0 < w (l.succAbove j) then
          Ioi (x * w (l.succAbove j) / w l) else Set.univ) =
          ENNReal.ofReal (Real.exp (-(x * w (l.succAbove j) / w l))) := by
        intro j
        by_cases hj : 0 < w (l.succAbove j)
        · rw [if_pos hj, E_Ioi _ (div_nonneg (mul_nonneg hx hj.le) hl.le)]
        · have hj0 : w (l.succAbove j) = 0 := le_antisymm (not_lt.mp hj) (hw _)
          rw [if_neg hj, measure_univ, hj0, mul_zero, zero_div, neg_zero, Real.exp_zero,
            ENNReal.ofReal_one]
      show (Measure.pi fun _ : Fin n => expMeasure (1 : ℝ)) (Prod.mk x ⁻¹' T) = _
      rw [hslice, Measure.pi_pi]
      calc ∏ j : Fin n, (expMeasure (1 : ℝ)) (if 0 < w (l.succAbove j) then
            Ioi (x * w (l.succAbove j) / w l) else Set.univ)
          = ∏ j : Fin n, ENNReal.ofReal (Real.exp (-(x * w (l.succAbove j) / w l))) :=
            Finset.prod_congr rfl (fun j _ => hfac j)
        _ = ENNReal.ofReal (Real.exp (-((∑ j : Fin n, w (l.succAbove j)) / w l * x))) := by
            rw [← ENNReal.ofReal_prod_of_nonneg
              (f := fun j => Real.exp (-(x * w (l.succAbove j) / w l)))
              (fun j _ => (Real.exp_pos _).le), ← Real.exp_sum]
            congr 2
            rw [Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.mul_sum]
            ring)
  have key' : ∫⁻ x, (Measure.pi fun _ : Fin n => expMeasure (1 : ℝ)) (Prod.mk x ⁻¹' T)
      ∂((fun _ : Fin (n + 1) => expMeasure (1 : ℝ)) l) =
      ENNReal.ofReal (1 / ((∑ j : Fin n, w (l.succAbove j)) / w l + 1)) := key
  rw [key', hsum]
  congr 1
  rw [div_add_one hl.ne', one_div_div, add_comm]

lemma neg_null {n : ℕ} (m : Fin (n + 1)) : clockLaw (n + 1) {Z | Z m < 0} = 0 := by
  have hmp := measurePreserving_eval (fun _ : Fin (n + 1) => expMeasure (1 : ℝ)) m
  have e : {Z : Fin (n + 1) → ℝ | Z m < 0} = Function.eval m ⁻¹' Iio 0 := rfl
  rw [e, clockLaw, hmp.measure_preimage measurableSet_Iio.nullMeasurableSet]
  exact E_Iio0

lemma tie_null {n : ℕ} (m m' : Fin (n + 1)) (hmm : m ≠ m') (a b : ℝ) (ha : 0 < a) :
    clockLaw (n + 1) {Z | Z m * a = Z m' * b} = 0 := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => expMeasure (1 : ℝ)) m
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (Ne.symm hmm)
  set T : Set (ℝ × (Fin n → ℝ)) := {p | p.1 * a = p.2 j * b} with hTdef
  have hT : MeasurableSet T := measurableSet_eq_fun (measurable_fst.mul_const _)
    (((measurable_pi_apply j).comp measurable_snd).mul_const _)
  have hset : {Z : Fin (n + 1) → ℝ | Z m * a = Z m' * b} =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) m) ⁻¹' T := by
    ext Z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hTdef]
    rw [← hj]
    rfl
  rw [hset, clockLaw, hmp.measure_preimage hT.nullMeasurableSet, Measure.prod_apply_symm hT]
  refine (lintegral_congr (fun y => ?_)).trans lintegral_zero
  have e : (fun x => (x, y)) ⁻¹' T = {y j * b / a} := by
    ext x
    simp only [Set.mem_preimage, hTdef, Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [eq_div_iff ha.ne']
  rw [e]
  exact E_singleton _

lemma bad_null {n : ℕ} (w : Fin (n + 1) → ℝ) : clockLaw (n + 1) (Bad w) = 0 := by
  have h1 : Bad w ⊆ (⋃ m, {Z : Fin (n + 1) → ℝ | Z m < 0}) ∪
      ⋃ m, ⋃ m', {Z : Fin (n + 1) → ℝ |
        m ≠ m' ∧ 0 < w m ∧ 0 < w m' ∧ Z m * w m' = Z m' * w m} := by
    intro Z hZ
    rcases hZ with ⟨m, hm⟩ | ⟨m, m', h⟩
    · exact Or.inl (Set.mem_iUnion.mpr ⟨m, hm⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨m', h⟩⟩)
  refine measure_mono_null h1 (measure_union_null (measure_iUnion_null (fun m => neg_null m))
    (measure_iUnion_null (fun m => measure_iUnion_null (fun m' => ?_))))
  by_cases hc : m ≠ m' ∧ 0 < w m ∧ 0 < w m'
  · exact measure_mono_null (fun Z hZ => hZ.2.2.2) (tie_null m m' hc.1 (w m') (w m) hc.2.2)
  · have e : {Z : Fin (n + 1) → ℝ | m ≠ m' ∧ 0 < w m ∧ 0 < w m' ∧ Z m * w m' = Z m' * w m} =
        ∅ := by
      ext Z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hc ⟨h.1, h.2.1, h.2.2.1⟩
    rw [e]
    exact measure_empty

lemma win_label {n : ℕ} (w : Fin (n + 1) → ℝ) (l : Fin (n + 1)) (hl : 0 < w l)
    (Z : Fin (n + 1) → ℝ) (hZ : Z ∈ Win w l) : expClock Z w = l := by
  have hlS : l ∈ Finset.univ.filter
      (fun i => 0 < w i ∧ ∀ j, 0 < w j → Z i * w j ≤ Z j * w i) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hl, fun j hj => ?_⟩
    by_cases hjl : j = l
    · subst hjl
      exact le_refl _
    · exact (hZ j hjl hj).le
  have huniq : ∀ i ∈ Finset.univ.filter
      (fun i => 0 < w i ∧ ∀ j, 0 < w j → Z i * w j ≤ Z j * w i), i = l := by
    intro i hi
    rw [Finset.mem_filter] at hi
    by_contra hil
    have h1 := hi.2.2 l hl
    have h2 := hZ i hil hi.2.1
    linarith
  simp only [expClock]
  rw [dif_pos ⟨l, hlS⟩]
  exact huniq _ (Finset.min'_mem _ _)

lemma label_sub {n : ℕ} (w : Fin (n + 1) → ℝ) (hsupp : ∃ m, 0 < w m) (l : Fin (n + 1))
    (Z : Fin (n + 1) → ℝ) (hZ : expClock Z w = l) : (0 < w l ∧ Z ∈ Win w l) ∨ Z ∈ Bad w := by
  have hne : (Finset.univ.filter
      (fun i => 0 < w i ∧ ∀ j, 0 < w j → Z i * w j ≤ Z j * w i)).Nonempty := by
    obtain ⟨m0, hm0⟩ := hsupp
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun i => 0 < w i))
      (fun i => Z i / w i) ⟨m0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm0⟩⟩
    rw [Finset.mem_filter] at hi
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.2, fun j hj => ?_⟩⟩
    have h := hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
    rw [div_le_div_iff₀ hi.2 hj] at h
    exact h
  simp only [expClock] at hZ
  rw [dif_pos hne] at hZ
  have hmem := Finset.min'_mem _ hne
  rw [hZ, Finset.mem_filter] at hmem
  obtain ⟨_, hwl, hle⟩ := hmem
  by_cases hwin : Z ∈ Win w l
  · exact Or.inl ⟨hwl, hwin⟩
  · right
    simp only [Win, Set.mem_setOf_eq, not_forall, not_lt] at hwin
    obtain ⟨m, hml, hwm, hge⟩ := hwin
    have hle' := hle m hwm
    exact Or.inr ⟨l, m, Ne.symm hml, hwl, hwm, le_antisymm hle' hge⟩

lemma diff_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (A B N : Set α) (hB : MeasurableSet B) (hBA : B ⊆ A ∪ N) (hN : μ N = 0) :
    μ (A \ B) ≤ μ A - μ B := by
  have h1 := measure_sdiff_add_inter (μ := μ) A hB
  have h2 : μ B ≤ μ (A ∩ B) := by
    calc μ B ≤ μ (B ∩ A) + μ (B \ A) := measure_le_inter_add_sdiff μ B A
      _ ≤ μ (A ∩ B) + μ N := by
          rw [Set.inter_comm]
          exact add_le_add le_rfl (measure_mono (fun x hx => (hBA hx.1).resolve_left hx.2))
      _ = μ (A ∩ B) := by rw [hN, add_zero]
  apply ENNReal.le_sub_of_add_le_right (measure_ne_top μ B)
  calc μ (A \ B) + μ B ≤ μ (A \ B) + μ (A ∩ B) := add_le_add le_rfl h2
    _ = μ A := h1

/-! ### Lemma 2.1: the exponential clocks separation bound -/

set_option maxHeartbeats 1600000 in
lemma sepExp_le {n : ℕ} (u v : Fin (n + 1) → ℝ) (hu : u ∈ stdSimplex ℝ (Fin (n + 1)))
    (hv : v ∈ stdSimplex ℝ (Fin (n + 1))) (a b : Fin (n + 1)) (hab : a ≠ b) (ε : ℝ)
    (hε : 0 ≤ ε) (huv : v = ijShift u a b ε) : sepExp u v ≤ ε * (2 - u a - u b) := by
  haveI : IsProbabilityMeasure (clockLaw (n + 1)) := by
    unfold clockLaw
    infer_instance
  have hva : v a = u a + ε := by rw [huv, sh_a u hab]
  have hvb : v b = u b - ε := by rw [huv, sh_b u hab]
  have hvo : ∀ m, m ≠ a → m ≠ b → v m = u m := fun m h1 h2 => by rw [huv, sh_o u h1 h2]
  have hu0 : ∀ m, 0 ≤ u m := hu.1
  have hv0 : ∀ m, 0 ≤ v m := hv.1
  have hsupp : ∃ m, 0 < u m := by
    by_contra h
    push_neg at h
    have h1 : ∑ m, u m ≤ 0 := Finset.sum_nonpos (fun m _ => h m)
    have h2 := hu.2
    linarith
  have hvb0 : 0 ≤ u b - ε := by rw [← hvb]; exact hv0 b
  have hab2 : u a + u b ≤ 1 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {a, b})
      (f := u) (fun m _ _ => hu0 m)
    rw [Finset.sum_pair hab, hu.2] at h
    exact h
  set ws : Fin (n + 1) → ℝ := fun m => if m = a then u a + ε else u m with hws
  have hws0 : ∀ m, 0 ≤ ws m := by
    intro m
    simp only [hws]
    split_ifs
    · linarith [hu0 a]
    · exact hu0 m
  have hwsum : ∑ m, ws m = 1 + ε := by
    have e : ∀ m, ws m = u m + (if m = a then ε else 0) := by
      intro m
      simp only [hws]
      split_ifs with h
      · rw [h]
      · ring
    rw [Finset.sum_congr rfl (fun m _ => e m), Finset.sum_add_distrib, hu.2,
      Finset.sum_ite_eq']
    simp
  set μ := clockLaw (n + 1) with hμ
  -- reduction to a race
  have hred : ∀ (l : Fin (n + 1)) (W' : Set (Fin (n + 1) → ℝ)),
      W' ⊆ {Z | expClock Z v = l} ∪ Bad u →
      {Z | expClock Z u = l} \ {Z | expClock Z v = l} ⊆ (Win u l \ W') ∪ Bad u := by
    intro l W' hW' Z hZ
    rcases label_sub u hsupp l Z hZ.1 with ⟨_, hwin⟩ | hbad
    · by_cases hW : Z ∈ W'
      · rcases hW' hW with h | h
        · exact absurd h hZ.2
        · exact Or.inr h
      · exact Or.inl ⟨hwin, hW⟩
    · exact Or.inr hbad
  -- the three cases
  have bound_a : μ ({Z | expClock Z u = a} \ {Z | expClock Z v = a}) ≤ ENNReal.ofReal 0 := by
    have hsub : {Z | expClock Z u = a} \ {Z | expClock Z v = a} ⊆ Bad u := by
      intro Z hZ
      rcases label_sub u hsupp a Z hZ.1 with ⟨hpos, hwin⟩ | hbad
      · by_cases hneg : ∃ m, Z m < 0
        · exact Or.inl hneg
        · push_neg at hneg
          exfalso
          apply hZ.2
          have hvap : 0 < v a := by rw [hva]; linarith
          refine win_label v a hvap Z (fun m hm hvm => ?_)
          rw [hva]
          by_cases hmb : m = b
          · rw [hmb] at hm hvm ⊢
            rw [hvb] at hvm ⊢
            have hub : 0 < u b := by linarith
            have h1 := hwin b hm hub
            nlinarith [mul_nonneg (hneg a) hε, mul_nonneg (hneg b) hε]
          · rw [hvo m hm hmb] at hvm ⊢
            have h1 := hwin m hm hvm
            nlinarith [mul_nonneg (hneg m) hε]
      · exact hbad
    calc μ _ ≤ μ (Bad u) := measure_mono hsub
      _ = 0 := bad_null u
      _ ≤ ENNReal.ofReal 0 := bot_le
  have bound_b : μ ({Z | expClock Z u = b} \ {Z | expClock Z v = b}) ≤ ENNReal.ofReal ε := by
    by_cases hub : u b = 0
    · have hsub : {Z | expClock Z u = b} \ {Z | expClock Z v = b} ⊆ Bad u := by
        intro Z hZ
        rcases label_sub u hsupp b Z hZ.1 with ⟨hpos, _⟩ | hbad
        · exact absurd hub (ne_of_gt hpos)
        · exact hbad
      calc μ _ ≤ μ (Bad u) := measure_mono hsub
        _ = 0 := bad_null u
        _ ≤ ENNReal.ofReal ε := bot_le
    have hubp : 0 < u b := lt_of_le_of_ne (hu0 b) (Ne.symm hub)
    by_cases hvbz : u b - ε = 0
    · have hsub : {Z | expClock Z u = b} \ {Z | expClock Z v = b} ⊆ Win u b ∪ Bad u := by
        intro Z hZ
        rcases label_sub u hsupp b Z hZ.1 with ⟨_, hwin⟩ | hbad
        · exact Or.inl hwin
        · exact Or.inr hbad
      calc μ _ ≤ μ (Win u b ∪ Bad u) := measure_mono hsub
        _ ≤ μ (Win u b) + μ (Bad u) := measure_union_le _ _
        _ = ENNReal.ofReal ε := by
          rw [bad_null u, add_zero, hμ, race u hu0 b hubp, hu.2, div_one]
          congr 1
          linarith
    · have hvbp : 0 < v b := by rw [hvb]; exact lt_of_le_of_ne hvb0 (Ne.symm hvbz)
      have hsub := hred b (Win v b) (fun Z hZ => Or.inl (win_label v b hvbp Z hZ))
      have hincl : Win v b ⊆ Win u b ∪ Bad u := by
        intro Z hZ
        by_cases hneg : ∃ m, Z m < 0
        · exact Or.inr (Or.inl hneg)
        · push_neg at hneg
          left
          intro m hm hum
          by_cases hma : m = a
          · rw [hma] at hm hum ⊢
            have hvap : 0 < v a := by rw [hva]; linarith
            have h1 := hZ a hm hvap
            rw [hva, hvb] at h1
            nlinarith [mul_nonneg (hneg a) hε, mul_nonneg (hneg b) hε]
          · have hvm : v m = u m := hvo m hma hm
            have h1 := hZ m hm (by rw [hvm]; exact hum)
            rw [hvm, hvb] at h1
            nlinarith [mul_nonneg (hneg m) hε]
      calc μ _ ≤ μ ((Win u b \ Win v b) ∪ Bad u) := measure_mono hsub
        _ ≤ μ (Win u b \ Win v b) + μ (Bad u) := measure_union_le _ _
        _ ≤ (μ (Win u b) - μ (Win v b)) + 0 :=
          add_le_add (diff_le μ _ _ _ (win_meas v b) hincl (bad_null u)) (bad_null u).le
        _ = ENNReal.ofReal ε := by
          rw [add_zero, hμ, race u hu0 b hubp, race v hv0 b hvbp, hu.2, hv.2, div_one, div_one,
            ← ENNReal.ofReal_sub _ (hv0 b), hvb]
          congr 1
          ring
  have bound_R : ∀ l, l ≠ a → l ≠ b →
      μ ({Z | expClock Z u = l} \ {Z | expClock Z v = l}) ≤
        ENNReal.ofReal (u l - u l / (1 + ε)) := by
    intro l hla hlb
    by_cases hul : u l = 0
    · have hsub : {Z | expClock Z u = l} \ {Z | expClock Z v = l} ⊆ Bad u := by
        intro Z hZ
        rcases label_sub u hsupp l Z hZ.1 with ⟨hpos, _⟩ | hbad
        · exact absurd hul (ne_of_gt hpos)
        · exact hbad
      calc μ _ ≤ μ (Bad u) := measure_mono hsub
        _ = 0 := bad_null u
        _ ≤ _ := bot_le
    have hulp : 0 < u l := lt_of_le_of_ne (hu0 l) (Ne.symm hul)
    have hwsl : ws l = u l := by simp only [hws, if_neg hla]
    have hvl : v l = u l := hvo l hla hlb
    have hincl1 : Win ws l ⊆ Win u l ∪ Bad u := by
      intro Z hZ
      by_cases hneg : ∃ m, Z m < 0
      · exact Or.inr (Or.inl hneg)
      · push_neg at hneg
        left
        intro m hm hum
        by_cases hma : m = a
        · rw [hma] at hm hum ⊢
          have hwa : ws a = u a + ε := by simp only [hws, if_pos rfl]
          have h1 := hZ a hm (by rw [hwa]; linarith)
          rw [hwa, hwsl] at h1
          nlinarith [mul_nonneg (hneg l) hε]
        · have hwm : ws m = u m := by simp only [hws, if_neg hma]
          have h1 := hZ m hm (by rw [hwm]; exact hum)
          rw [hwm, hwsl] at h1
          exact h1
    have hincl2 : Win ws l ⊆ {Z | expClock Z v = l} ∪ Bad u := by
      intro Z hZ
      by_cases hneg : ∃ m, Z m < 0
      · exact Or.inr (Or.inl hneg)
      · push_neg at hneg
        left
        refine win_label v l (by rw [hvl]; exact hulp) Z (fun m hm hvm => ?_)
        rw [hvl]
        by_cases hma : m = a
        · rw [hma] at hm hvm ⊢
          have hwa : ws a = u a + ε := by simp only [hws, if_pos rfl]
          have h1 := hZ a hm (by rw [hwa, ← hva]; exact hvm)
          rw [hwa, hwsl] at h1
          rw [hva]
          exact h1
        · by_cases hmb : m = b
          · rw [hmb] at hm hvm ⊢
            have hwb : ws b = u b := by simp only [hws, if_neg (Ne.symm hab)]
            rw [hvb] at hvm ⊢
            have hub : 0 < u b := by linarith
            have h1 := hZ b hm (by rw [hwb]; exact hub)
            rw [hwb, hwsl] at h1
            nlinarith [mul_nonneg (hneg l) hε]
          · have hwm : ws m = u m := by simp only [hws, if_neg hma]
            have hvm' : v m = u m := hvo m hma hmb
            rw [hvm'] at hvm ⊢
            have h1 := hZ m hm (by rw [hwm]; exact hvm)
            rw [hwm, hwsl] at h1
            exact h1
    have hsub := hred l (Win ws l) hincl2
    have hdiv0 : 0 ≤ u l / (1 + ε) := div_nonneg (hu0 l) (by linarith)
    calc μ _ ≤ μ ((Win u l \ Win ws l) ∪ Bad u) := measure_mono hsub
      _ ≤ μ (Win u l \ Win ws l) + μ (Bad u) := measure_union_le _ _
      _ ≤ (μ (Win u l) - μ (Win ws l)) + 0 :=
        add_le_add (diff_le μ _ _ _ (win_meas ws l) hincl1 (bad_null u)) (bad_null u).le
      _ = ENNReal.ofReal (u l - u l / (1 + ε)) := by
        rw [add_zero, hμ, race u hu0 l hulp, race ws hws0 l (by rw [hwsl]; exact hulp), hu.2,
          hwsum, div_one, hwsl, ← ENNReal.ofReal_sub _ hdiv0]
  -- assemble
  set B : Fin (n + 1) → ℝ := fun l =>
    if l = b then ε else if l = a then 0 else u l - u l / (1 + ε) with hB
  have hTl : ∀ l, μ ({Z | expClock Z u = l} \ {Z | expClock Z v = l}) ≤ ENNReal.ofReal (B l) := by
    intro l
    by_cases hlb : l = b
    · rw [hlb]
      simp only [hB, if_pos rfl]
      exact bound_b
    · by_cases hla : l = a
      · rw [hla]
        simp only [hB, if_neg hab, if_pos rfl]
        exact bound_a
      · simp only [hB, if_neg hlb, if_neg hla]
        exact bound_R l hla hlb
  have hB0 : ∀ l, 0 ≤ B l := by
    intro l
    simp only [hB]
    split_ifs
    · exact hε
    · exact le_refl _
    · exact sub_nonneg.mpr (div_le_self (hu0 l) (by linarith))
  have hBle : ∀ l, B l ≤ ε * u l + (if l = b then ε * (1 - u b) else 0) -
      (if l = a then ε * u a else 0) := by
    intro l
    simp only [hB]
    by_cases hlb : l = b
    · rw [if_pos hlb, if_pos hlb, if_neg (fun h => hab (h.symm.trans hlb)), hlb]
      linarith
    · by_cases hla : l = a
      · rw [if_neg hlb, if_pos hla, if_neg hlb, if_pos hla, hla]
        linarith
      · rw [if_neg hlb, if_neg hla, if_neg hlb, if_neg hla]
        have h1 : u l - ε * u l ≤ u l / (1 + ε) := by
          rw [le_div_iff₀ (by linarith)]
          nlinarith [mul_nonneg (hu0 l) (sq_nonneg ε)]
        linarith
  have hsumC : ∑ l, (ε * u l + (if l = b then ε * (1 - u b) else 0) -
      (if l = a then ε * u a else 0)) = ε * (2 - u a - u b) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hu.2,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    ring
  have hBsum : ∑ l, B l ≤ ε * (2 - u a - u b) := by
    rw [← hsumC]
    exact Finset.sum_le_sum (fun l _ => hBle l)
  have hcover : {Z | expClock Z u ≠ expClock Z v} ⊆
      ⋃ l, ({Z | expClock Z u = l} \ {Z | expClock Z v = l}) := by
    intro Z hZ
    exact Set.mem_iUnion.mpr ⟨expClock Z u, rfl, fun h => hZ (Eq.symm h)⟩
  have hS : μ {Z | expClock Z u ≠ expClock Z v} ≤ ENNReal.ofReal (ε * (2 - u a - u b)) := by
    calc μ {Z | expClock Z u ≠ expClock Z v}
        ≤ μ (⋃ l, ({Z | expClock Z u = l} \ {Z | expClock Z v = l})) := measure_mono hcover
      _ ≤ ∑ l, μ ({Z | expClock Z u = l} \ {Z | expClock Z v = l}) :=
          measure_iUnion_fintype_le μ _
      _ ≤ ∑ l, ENNReal.ofReal (B l) := Finset.sum_le_sum (fun l _ => hTl l)
      _ = ENNReal.ofReal (∑ l, B l) := (ENNReal.ofReal_sum_of_nonneg (fun l _ => hB0 l)).symm
      _ ≤ ENNReal.ofReal (ε * (2 - u a - u b)) := ENNReal.ofReal_le_ofReal hBsum
  have hnn : 0 ≤ ε * (2 - u a - u b) := mul_nonneg hε (by linarith)
  unfold sepExp
  exact ENNReal.toReal_le_of_le_ofReal hnn hS

/-! ### Relabelling invariance -/

lemma flat_tie {k : ℕ} (s : Fin k → ℝ) (hs : Antitone s) (r1 r2 : Fin k) (h : s r1 = s r2) :
    MultiwayCut.flat s r1 = MultiwayCut.flat s r2 := by
  wlog hle : r1 ≤ r2 generalizing r1 r2
  · exact (this r2 r1 h.symm ((le_total r1 r2).resolve_left hle)).symm
  funext n
  show (if n < r1 then s r1 else s n) = (if n < r2 then s r2 else s n)
  by_cases h1 : n < r1
  · rw [if_pos h1, if_pos (lt_of_lt_of_le h1 hle), h]
  · by_cases h2 : n < r2
    · rw [if_neg h1, if_pos h2]
      have e1 : s n ≤ s r1 := hs (not_lt.mp h1)
      have e2 : s r2 ≤ s n := hs h2.le
      linarith
    · rw [if_neg h1, if_neg h2]

lemma sort_comp {k : ℕ} (u : Fin k → ℝ) (π : Equiv.Perm (Fin k)) :
    (u ∘ π) ∘ sortPerm (u ∘ π) = u ∘ sortPerm u := by
  have hmono : Monotone ((-u) ∘ (π * sortPerm (u ∘ π) : Equiv.Perm (Fin k))) := by
    have h := Tuple.monotone_sort (-(u ∘ π))
    intro x y hxy
    exact h hxy
  have h := (Tuple.comp_sort_eq_comp_iff_monotone (f := -u)
    (σ := π * sortPerm (u ∘ π))).mpr hmono
  funext m
  have hm : -u (π (sortPerm (u ∘ π) m)) = -u (Tuple.sort (-u) m) := congrFun h m
  exact neg_inj.mp hm

lemma quad_equiv {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (u : Fin k → ℝ)
    (π : Equiv.Perm (Fin k)) : quadTransform A (u ∘ π) = quadTransform A u ∘ π := by
  funext m
  have hs := sort_comp u π
  have hanti : Antitone (u ∘ sortPerm u) := Aux_MultiwayCut_lemma_5_2.sorted_anti u
  have h1 : (u ∘ sortPerm u) ((sortPerm (u ∘ π)).symm m) = u (π m) := by
    rw [← hs]
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  have h2 : (u ∘ sortPerm u) ((sortPerm u).symm (π m)) = u (π m) := by
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  show MultiwayCut.flat ((u ∘ π) ∘ sortPerm (u ∘ π)) ((sortPerm (u ∘ π)).symm m) ⬝ᵥ
      (A *ᵥ MultiwayCut.flat ((u ∘ π) ∘ sortPerm (u ∘ π)) ((sortPerm (u ∘ π)).symm m)) =
    MultiwayCut.flat (u ∘ sortPerm u) ((sortPerm u).symm (π m)) ⬝ᵥ
      (A *ᵥ MultiwayCut.flat (u ∘ sortPerm u) ((sortPerm u).symm (π m)))
  rw [hs, flat_tie (u ∘ sortPerm u) hanti _ _ (h1.trans h2.symm)]

lemma ckr_comp {k : ℕ} [NeZero k] (r : ℝ) (σ π : Equiv.Perm (Fin k)) (x : Fin k → ℝ) :
    ckr r σ (x ∘ π) = π.symm (ckr r (π * σ) x) := by
  apply π.injective
  rw [Equiv.apply_symm_apply]
  simp only [ckr]
  first
    | (rw [apply_dite π]; rfl)
    | (split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1 h2 | exact absurd h2 h1)

lemma sepCKR_comp {k : ℕ} [NeZero k] (x y : Fin k → ℝ) (π : Equiv.Perm (Fin k)) :
    sepCKR (x ∘ π) (y ∘ π) = sepCKR x y := by
  unfold sepCKR ckrProb
  congr 1
  calc ∑ σ : Equiv.Perm (Fin k),
        (volume {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ ckr r σ (x ∘ π) ≠ ckr r σ (y ∘ π)}).toReal
      = ∑ σ : Equiv.Perm (Fin k), (fun τ : Equiv.Perm (Fin k) =>
          (volume {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ ckr r τ x ≠ ckr r τ y}).toReal)
          (Equiv.mulLeft π σ) := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        show (volume {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ ckr r σ (x ∘ π) ≠ ckr r σ (y ∘ π)}).toReal =
          (volume {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ ckr r (π * σ) x ≠ ckr r (π * σ) y}).toReal
        congr 2
        ext r
        simp only [Set.mem_setOf_eq, ckr_comp]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun h => h2 (by rw [h])⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun h => h2 (π.symm.injective h)⟩
    _ = ∑ σ : Equiv.Perm (Fin k),
        (volume {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ ckr r σ x ≠ ckr r σ y}).toReal :=
        Equiv.sum_comp (Equiv.mulLeft π) (fun τ : Equiv.Perm (Fin k) =>
          (volume {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧ ckr r τ x ≠ ckr r τ y}).toReal)

end Aux_MultiwayCut_theorem_1_2_density

open MultiwayCut Matrix in
theorem solution {k : ℕ} [NeZero k] :
    ∃ C : ℝ, ∀ (π : Equiv.Perm (Fin k)) (i j : Fin k) (ε : ℝ) (u v : Fin k → ℝ),
      IsIJEdge π i j ε u v →
        alg3Sep (121 / 229) (quadTransform (A53 k)) u v ≤ 297 / 229 * ε + C * ε ^ 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := NeZero.ne k; omega⟩
  obtain ⟨K, hK⟩ : ∃ K : Fin (n + 1) → Fin (n + 1) → ℝ, K = fun i j =>
      ∑ ℓ : Fin (n + 1), |flat (Pi.single i 1 - Pi.single j 1 : Fin (n + 1) → ℝ) ℓ ⬝ᵥ
        (A53 (n + 1) *ᵥ flat (Pi.single i 1 - Pi.single j 1 : Fin (n + 1) → ℝ) ℓ)| /
          ((ℓ.val : ℝ) + 1) := ⟨_, rfl⟩
  have hK0 : ∀ i j, 0 ≤ K i j := by
    intro i j
    rw [hK]
    exact Finset.sum_nonneg (fun ℓ _ => div_nonneg (abs_nonneg _) (by positivity))
  refine ⟨108 / 229 * ∑ i, ∑ j, K i j, ?_⟩
  intro π i j ε u v hedge
  obtain ⟨hu, hv, hij, hε0, hanti, hgi, hgj, huv⟩ := hedge
  have hπij : π i ≠ π j := fun h => (ne_of_lt hij) (π.injective h)
  -- the exponential clocks part
  have hexp := Aux_MultiwayCut_theorem_1_2_density.sepExp_le u v hu hv (π i) (π j) hπij ε hε0 huv
  -- relabelled points
  have hu' : u ∘ π ∈ stdSimplex ℝ (Fin (n + 1)) :=
    ⟨fun m => hu.1 (π m), (Equiv.sum_comp π u).trans hu.2⟩
  have hvπ : v ∘ π = ijShift (u ∘ π) i j ε := by
    funext m
    rw [huv]
    simp only [Function.comp_apply, ijShift, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      Pi.single_apply, smul_eq_mul, π.injective.eq_iff]
  have hv' : v ∘ π ∈ stdSimplex ℝ (Fin (n + 1)) :=
    ⟨fun m => hv.1 (π m), (Equiv.sum_comp π v).trans hv.2⟩
  have hedge' : IsIJEdge (Equiv.refl (Fin (n + 1))) i j ε (u ∘ π)
      (ijShift (u ∘ π) ((Equiv.refl (Fin (n + 1))) i) ((Equiv.refl (Fin (n + 1))) j) ε) := by
    unfold IsIJEdge
    refine ⟨hu', ?_, hij, hε0, hanti, hgi, hgj, rfl⟩
    have e : ijShift (u ∘ π) ((Equiv.refl (Fin (n + 1))) i) ((Equiv.refl (Fin (n + 1))) j) ε =
      v ∘ π := hvπ.symm
    rw [e]
    exact hv'
  have hckr := Aux_MultiwayCut_lemma_5_2.L52U (A53 (n + 1)) Aux_MultiwayCut_lemma_5_4.A53_symm
    Aux_MultiwayCut_lemma_5_4.A53_cond (u ∘ π) i j ε hedge'
  have hCK : sepCKR (quadTransform (A53 (n + 1)) u) (quadTransform (A53 (n + 1)) v) =
      sepCKR (quadTransform (A53 (n + 1)) (u ∘ π))
        (quadTransform (A53 (n + 1))
          (ijShift (u ∘ π) ((Equiv.refl (Fin (n + 1))) i) ((Equiv.refl (Fin (n + 1))) j) ε)) := by
    have e : ijShift (u ∘ π) ((Equiv.refl (Fin (n + 1))) i) ((Equiv.refl (Fin (n + 1))) j) ε =
      v ∘ π := hvπ.symm
    rw [e, Aux_MultiwayCut_theorem_1_2_density.quad_equiv,
      Aux_MultiwayCut_theorem_1_2_density.quad_equiv,
      Aux_MultiwayCut_theorem_1_2_density.sepCKR_comp]
  have hmain := Aux_MultiwayCut_lemma_5_4.main_ineq (u ∘ π) i j hu' hanti hij
  have hsumu : ∑ ℓ ∈ Finset.univ \ {i, j}, (u ∘ π) ℓ = 1 - u (π i) - u (π j) := by
    have h := Finset.sum_sdiff (Finset.subset_univ {i, j}) (f := u ∘ π)
    rw [Finset.sum_pair (ne_of_lt hij), hu'.2] at h
    have e1 : (u ∘ π) i = u (π i) := rfl
    have e2 : (u ∘ π) j = u (π j) := rfl
    rw [e1, e2] at h
    linarith
  rw [hsumu] at hmain
  simp only [Function.comp_apply] at hmain
  have hmul := mul_le_mul_of_nonneg_left hmain hε0
  have hKij : K i j ≤ ∑ i, ∑ j, K i j := by
    calc K i j ≤ ∑ j', K i j' :=
          Finset.single_le_sum (f := fun j' => K i j') (fun j' _ => hK0 i j') (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', K i' j' :=
          Finset.single_le_sum (f := fun i' => ∑ j', K i' j')
            (fun i' _ => Finset.sum_nonneg (fun j' _ => hK0 i' j')) (Finset.mem_univ i)
  have hKij' : (∑ ℓ : Fin (n + 1), |flat (Pi.single i 1 - Pi.single j 1 : Fin (n + 1) → ℝ) ℓ ⬝ᵥ
        (A53 (n + 1) *ᵥ flat (Pi.single i 1 - Pi.single j 1 : Fin (n + 1) → ℝ) ℓ)| /
          ((ℓ.val : ℝ) + 1)) = K i j := by
    rw [hK]
  rw [hKij'] at hckr
  rw [← hCK] at hckr
  have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
  have hKm := mul_le_mul_of_nonneg_left hKij hε2
  unfold alg3Sep
  linarith [hexp, hckr, hmul, hKm]
