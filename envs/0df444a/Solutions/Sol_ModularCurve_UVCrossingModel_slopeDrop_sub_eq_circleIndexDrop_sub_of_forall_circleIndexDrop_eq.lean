-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.slopeDrop_sub_eq_circleIndexDrop_sub_of_forall_circleIndexDrop_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/45ea5847-e449-5b1d-a0bc-7db4da70daba

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Theorems.Thm_ModularCurve_UVCrossingModel_repGaussOrder_normalForm_eq_iInf_termOrder
import Theorems.Thm_ModularCurve_UVCrossingModel_dominantIndices_scale
import Theorems.Thm_ModularCurve_UVCrossingModel_gaussOrder_scaled_eq_repGaussOrder_normalForm
import Theorems.Thm_ModularCurve_UVCrossingModel_gaussOrder_succ_sub_eq_sInf_dominantIndices
import Theorems.Thm_ModularCurve_UVCrossingModel_gaussOrder_sub_pred_eq_sSup_dominantIndices
import Theorems.Thm_ModularCurve_UVCrossingModel_dominantIndices_finite_nonempty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_slopeDrop_sub_eq_circleIndexDrop_sub_of_forall_circleIndexDrop_eq

set_option autoImplicit false

universe u

namespace AnnulusNoKink

open ModularCurve ModularCurve.UVCrossingModel

variable {W : Type*} [CommRing W]

theorem termOrder_eq (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder v E t ab n = v (nfCoeff ab n) + ((n.toNat * t + (-n).toNat * (E - t) : ℕ) : ℕ∞) := by
  cases n with
  | ofNat i =>
      show v (nfCoeff ab (Int.ofNat i)) + ((annulusWeight E t (Finsupp.single 0 i) : ℕ) : ℕ∞) = _
      simp [annulusWeight]
  | negSucc j =>
      show v (nfCoeff ab (Int.negSucc j)) + ((annulusWeight E t (Finsupp.single 1 (j + 1)) : ℕ) : ℕ∞) = _
      simp [annulusWeight]

theorem termOrder_ne_top_iff (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder v E t ab n ≠ ⊤ ↔ v (nfCoeff ab n) ≠ ⊤ := by
  rw [termOrder_eq]
  constructor
  · intro h h'; exact h (by rw [h', top_add])
  · intro h; exact WithTop.add_ne_top.mpr ⟨h, ENat.coe_ne_top _⟩

theorem termOrder_step (v : W → ℕ∞) (E : ℕ) {t t' : ℕ} (htt' : t ≤ t') (ht'E : t' ≤ E)
    (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder v E t' ab n + (((-n).toNat * (t' - t) : ℕ) : ℕ∞) =
      termOrder v E t ab n + ((n.toNat * (t' - t) : ℕ) : ℕ∞) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htt'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht'E
  rw [termOrder_eq, termOrder_eq]
  have h1 : t + d + k - (t + d) = k := by omega
  have h2 : t + d + k - t = d + k := by omega
  have h3 : t + d - t = d := by omega
  rw [h1, h2, h3]
  push_cast
  ring

theorem mem_dominantIndices_iff (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    n ∈ dominantIndices v E t ab ↔ ∀ k, termOrder v E t ab n ≤ termOrder v E t ab k := by
  show termOrder v E t ab n = repGaussOrder v E t (inU ab.1 + inV ab.2) ↔ _
  rw [repGaussOrder_normalForm_eq_iInf_termOrder v hv0 E t ab hb]
  constructor
  · intro h k; rw [h]; exact iInf_le _ k
  · intro h; exact le_antisymm (le_iInf h) (iInf_le _ n)

theorem dominantIndices_nonempty (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) : (dominantIndices v E t ab).Nonempty := by
  obtain ⟨n, hn⟩ := ENat.exists_eq_iInf (fun k => termOrder v E t ab k)
  refine ⟨n, (mem_dominantIndices_iff v hv0 E t ab hb n).mpr fun k => ?_⟩
  rw [hn]; exact iInf_le _ k

theorem ne_top_of_mem (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (hne : ∃ n : ℤ, v (nfCoeff ab n) ≠ ⊤)
    {n : ℤ} (hn : n ∈ dominantIndices v E t ab) : v (nfCoeff ab n) ≠ ⊤ := by
  obtain ⟨k, hk⟩ := hne
  rw [← termOrder_ne_top_iff v E t] at hk ⊢
  have := (mem_dominantIndices_iff v hv0 E t ab hb n).mp hn k
  exact ne_top_of_le_ne_top hk this

theorem bddBelow_dominantIndices (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ht : t < E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hne : ∃ n : ℤ, v (nfCoeff ab n) ≠ ⊤) : BddBelow (dominantIndices v E t ab) := by
  obtain ⟨k, hk⟩ := hne
  rw [← termOrder_ne_top_iff v E t] at hk
  obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.mp hk
  refine ⟨-(g : ℤ), fun n hn => ?_⟩
  have hle := (mem_dominantIndices_iff v hv0 E t ab hb n).mp hn k
  rw [← hg, termOrder_eq] at hle
  have hw : (((n.toNat * t + (-n).toNat * (E - t) : ℕ) : ℕ∞)) ≤ g := le_trans le_add_self hle
  have hw' : n.toNat * t + (-n).toNat * (E - t) ≤ g := by exact_mod_cast hw
  have h1 : (-n).toNat ≤ (-n).toNat * (E - t) := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem bddAbove_dominantIndices (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ht : 0 < t)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hne : ∃ n : ℤ, v (nfCoeff ab n) ≠ ⊤) : BddAbove (dominantIndices v E t ab) := by
  obtain ⟨k, hk⟩ := hne
  rw [← termOrder_ne_top_iff v E t] at hk
  obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.mp hk
  refine ⟨(g : ℤ), fun n hn => ?_⟩
  have hle := (mem_dominantIndices_iff v hv0 E t ab hb n).mp hn k
  rw [← hg, termOrder_eq] at hle
  have hw : (((n.toNat * t + (-n).toNat * (E - t) : ℕ) : ℕ∞)) ≤ g := le_trans le_add_self hle
  have hw' : n.toNat * t + (-n).toNat * (E - t) ≤ g := by exact_mod_cast hw
  have h1 : n.toNat ≤ n.toNat * t := Nat.le_mul_of_pos_right _ ht
  omega

theorem sInf_mem (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ht : t < E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hne : ∃ n : ℤ, v (nfCoeff ab n) ≠ ⊤) :
    sInf (dominantIndices v E t ab) ∈ dominantIndices v E t ab :=
  Int.csInf_mem (dominantIndices_nonempty v hv0 E t ab hb) (bddBelow_dominantIndices v hv0 E t ht ab hb hne)

theorem sSup_mem (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ht : 0 < t)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hne : ∃ n : ℤ, v (nfCoeff ab n) ≠ ⊤) :
    sSup (dominantIndices v E t ab) ∈ dominantIndices v E t ab :=
  Int.csSup_mem (dominantIndices_nonempty v hv0 E t ab hb) (bddAbove_dominantIndices v hv0 E t ht ab hb hne)

theorem le_of_mem_of_mem (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E : ℕ) {t t' : ℕ} (htt' : t < t') (ht'E : t' ≤ E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hne : ∃ n : ℤ, v (nfCoeff ab n) ≠ ⊤)
    {m n : ℤ} (hm : m ∈ dominantIndices v E t ab) (hn : n ∈ dominantIndices v E t' ab) : n ≤ m := by
  by_contra hlt
  push Not at hlt
  have h1 := (mem_dominantIndices_iff v hv0 E t ab hb m).mp hm n
  have h2 := (mem_dominantIndices_iff v hv0 E t' ab hb n).mp hn m
  have sm := termOrder_step v E htt'.le ht'E ab m
  have sn := termOrder_step v E htt'.le ht'E ab n
  have hfin : termOrder v E t' ab m ≠ ⊤ :=
    (termOrder_ne_top_iff v E t' ab m).mpr (ne_top_of_mem v hv0 E t ab hb hne hm)
  set d := t' - t with hd
  have hdpos : 0 < d := by omega

  have key : termOrder v E t' ab m + (((-m).toNat * d + n.toNat * d : ℕ) : ℕ∞) ≤
      termOrder v E t' ab m + (((-n).toNat * d + m.toNat * d : ℕ) : ℕ∞) := by
    calc termOrder v E t' ab m + (((-m).toNat * d + n.toNat * d : ℕ) : ℕ∞)
        = (termOrder v E t' ab m + (((-m).toNat * d : ℕ) : ℕ∞)) + ((n.toNat * d : ℕ) : ℕ∞) := by
          push_cast; ring
      _ = (termOrder v E t ab m + ((m.toNat * d : ℕ) : ℕ∞)) + ((n.toNat * d : ℕ) : ℕ∞) := by rw [sm]
      _ ≤ (termOrder v E t ab n + ((m.toNat * d : ℕ) : ℕ∞)) + ((n.toNat * d : ℕ) : ℕ∞) :=
          add_le_add (add_le_add h1 le_rfl) le_rfl
      _ = (termOrder v E t ab n + ((n.toNat * d : ℕ) : ℕ∞)) + ((m.toNat * d : ℕ) : ℕ∞) := by ring
      _ = (termOrder v E t' ab n + (((-n).toNat * d : ℕ) : ℕ∞)) + ((m.toNat * d : ℕ) : ℕ∞) := by rw [sn]
      _ ≤ (termOrder v E t' ab m + (((-n).toNat * d : ℕ) : ℕ∞)) + ((m.toNat * d : ℕ) : ℕ∞) :=
          add_le_add (add_le_add h2 le_rfl) le_rfl
      _ = termOrder v E t' ab m + (((-n).toNat * d + m.toNat * d : ℕ) : ℕ∞) := by push_cast; ring
  rw [ENat.add_le_add_iff_left hfin] at key
  have key' : (-m).toNat * d + n.toNat * d ≤ (-n).toNat * d + m.toNat * d := by exact_mod_cast key
  have e1 : (m.toNat : ℤ) - ((-m).toNat : ℤ) = m := Int.toNat_sub_toNat_neg m
  have e2 : (n.toNat : ℤ) - ((-n).toNat : ℤ) = n := Int.toNat_sub_toNat_neg n
  have key'' : ((-m).toNat + n.toNat) * d ≤ ((-n).toNat + m.toNat) * d := by nlinarith [key']
  have := Nat.le_of_mul_le_mul_right key'' hdpos
  omega

theorem sSup_eq_sInf_pred (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E : ℕ) {S : ℕ} (hS1 : 1 ≤ S) (hSE : S ≤ E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hne : ∃ n : ℤ, v (nfCoeff ab n) ≠ ⊤)
    (h : sInf (dominantIndices v E (S - 1) ab) ∈ dominantIndices v E S ab) :
    sSup (dominantIndices v E S ab) = sInf (dominantIndices v E (S - 1) ab) := by
  apply IsGreatest.csSup_eq
  refine ⟨h, fun k hk => ?_⟩
  exact le_of_mem_of_mem v hv0 E (by omega) hSE ab hb hne
    (sInf_mem v hv0 E (S - 1) (by omega) ab hb hne) hk

theorem sInf_mem_succ_of_dvd (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E r : ℕ) (hr : 1 ≤ r) (S : ℕ) (hS : S + 1 ≤ r * E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hne : ∃ n : ℤ, v (nfCoeff ab n) ≠ ⊤)
    (hdvd : ∀ δ : ℕ, 1 ≤ δ → (δ : ℤ) = sInf (dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) S ab) -
        sSup (dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) (S + 1) ab) → δ ∣ r) :
    sInf (dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) S ab) ∈
      dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) (S + 1) ab := by
  set vr : W → ℕ∞ := fun w => (r : ℕ∞) * v w with hvr
  have hr0 : (r : ℕ∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hvr0 : vr 0 = ⊤ := by simp only [hvr, hv0]; exact WithTop.mul_top hr0
  have hner : ∃ n : ℤ, vr (nfCoeff ab n) ≠ ⊤ := by
    obtain ⟨n, hn⟩ := hne
    exact ⟨n, WithTop.mul_ne_top (ENat.coe_ne_top r) hn⟩
  set n₀ := sInf (dominantIndices vr (r * E) S ab) with hn₀
  set m := sSup (dominantIndices vr (r * E) (S + 1) ab) with hm
  have hn₀mem : n₀ ∈ dominantIndices vr (r * E) S ab := sInf_mem vr hvr0 (r * E) S (by omega) ab hb hner
  have hmmem : m ∈ dominantIndices vr (r * E) (S + 1) ab := sSup_mem vr hvr0 (r * E) (S + 1) (by omega) ab hb hner
  have hmn : m ≤ n₀ := le_of_mem_of_mem vr hvr0 (r * E) (Nat.lt_succ_self S) hS ab hb hner hn₀mem hmmem
  rcases hmn.eq_or_lt with heq | hlt
  · rw [← heq]; exact hmmem

  obtain ⟨r', hr'⟩ := hdvd (n₀ - m).toNat (by omega) (Int.toNat_of_nonneg (by omega))
  have hδ : ((n₀ - m).toNat : ℤ) = n₀ - m := Int.toNat_of_nonneg (by omega)

  have hfin0 : v (nfCoeff ab n₀) ≠ ⊤ := by
    have := ne_top_of_mem vr hvr0 (r * E) S ab hb hner hn₀mem
    simp only [hvr] at this
    exact fun h => this (by rw [h]; exact WithTop.mul_top hr0)
  have hfin1 : v (nfCoeff ab m) ≠ ⊤ := by
    have := ne_top_of_mem vr hvr0 (r * E) (S + 1) ab hb hner hmmem
    simp only [hvr] at this
    exact fun h => this (by rw [h]; exact WithTop.mul_top hr0)
  obtain ⟨a₀, ha₀⟩ := ENat.ne_top_iff_exists.mp hfin0
  obtain ⟨a₁, ha₁⟩ := ENat.ne_top_iff_exists.mp hfin1

  have hT : ∀ (n : ℤ) (a : ℕ), v (nfCoeff ab n) = a → ∀ P : ℕ,
      termOrder vr (r * E) P ab n = ((r * a + n.toNat * P + (-n).toNat * (r * E - P) : ℕ) : ℕ∞) := by
    intro n a ha P
    rw [termOrder_eq]
    simp only [hvr, ha]
    push_cast
    ring

  have h1 : termOrder vr (r * E) S ab n₀ < termOrder vr (r * E) S ab m := by
    have hle := (mem_dominantIndices_iff vr hvr0 (r * E) S ab hb n₀).mp hn₀mem m
    refine lt_of_le_of_ne hle fun heq => ?_
    have hmS : m ∈ dominantIndices vr (r * E) S ab := by
      rw [mem_dominantIndices_iff vr hvr0 (r * E) S ab hb]
      intro k
      rw [← heq]
      exact (mem_dominantIndices_iff vr hvr0 (r * E) S ab hb n₀).mp hn₀mem k
    have : n₀ ≤ m := by
      rw [hn₀]
      exact csInf_le (bddBelow_dominantIndices vr hvr0 (r * E) S (by omega) ab hb hner) hmS
    omega
  rw [hT n₀ a₀ ha₀.symm S, hT m a₁ ha₁.symm S, Nat.cast_lt] at h1

  suffices h2 : termOrder vr (r * E) (S + 1) ab n₀ ≤ termOrder vr (r * E) (S + 1) ab m by
    rw [mem_dominantIndices_iff vr hvr0 (r * E) (S + 1) ab hb]
    intro k
    exact le_trans h2 ((mem_dominantIndices_iff vr hvr0 (r * E) (S + 1) ab hb m).mp hmmem k)
  rw [hT n₀ a₀ ha₀.symm (S + 1), hT m a₁ ha₁.symm (S + 1), Nat.cast_le]

  obtain ⟨d, hd⟩ : ∃ d, r * E = S + 1 + d := ⟨r * E - (S + 1), by omega⟩
  have e0 : r * E - S = d + 1 := by omega
  have e1 : r * E - (S + 1) = d := by omega
  rw [e0] at h1
  rw [e1]
  have en₀ : (n₀.toNat : ℤ) - ((-n₀).toNat : ℤ) = n₀ := Int.toNat_sub_toNat_neg n₀
  have em : (m.toNat : ℤ) - ((-m).toNat : ℤ) = m := Int.toNat_sub_toNat_neg m
  zify at h1 hr' ⊢
  have hδpos : (0 : ℤ) < n₀ - m := by omega
  have hr'' : (r : ℤ) = (n₀ - m) * r' := by rw [← hδ]; exact_mod_cast hr'

  set K : ℤ := ((a₁ : ℤ) - a₀) + (E : ℤ) * (((-m).toNat : ℤ) - ((-n₀).toNat : ℤ)) with hK
  have hdz : ((r : ℕ) : ℤ) * E = S + 1 + d := by exact_mod_cast hd
  have hrK : (r : ℤ) * a₁ - r * a₀ + ((S : ℤ) + 1 + d) * (((-m).toNat : ℤ) - ((-n₀).toNat : ℤ)) = r * K := by
    rw [hK, ← hdz]; ring
  have p1 := congrArg (fun z : ℤ => z * (S : ℤ)) en₀
  have p2 := congrArg (fun z : ℤ => z * (S : ℤ)) em

  have hX : (n₀ - m) * (S : ℤ) < r * K := by
    rw [← hrK]; linarith [h1, p1, p2]
  rw [hr'', mul_assoc] at hX
  have hX' : (S : ℤ) < r' * K := lt_of_mul_lt_mul_left hX hδpos.le
  have hY : (n₀ - m) * ((S : ℤ) + 1) ≤ (n₀ - m) * (r' * K) := mul_le_mul_of_nonneg_left (by omega) hδpos.le
  rw [← mul_assoc, ← hr'', ← hrK] at hY
  have q1 := congrArg (fun z : ℤ => z * ((S : ℤ) + 1)) en₀
  have q2 := congrArg (fun z : ℤ => z * ((S : ℤ) + 1)) em
  linarith [hY, q1, q2]

private theorem _root_.AnnulusNoKink.main (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E : ℕ) (hE : 1 ≤ E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hne : ∃ n : ℤ, v (nfCoeff ab n) ≠ ⊤) :
    ∃ N : ℕ, ∀ r : ℕ, 1 ≤ r → Nat.factorial N ∣ r →
      (∀ S : ℕ, S + 1 ≤ r * E →
        sInf (dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) S ab) ∈
          dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) (S + 1) ab) ∧
      (∀ S : ℕ, 1 ≤ S → S ≤ r * E →
        sSup (dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) S ab) ∈
          dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) (S - 1) ab) := by
  set β := sInf (dominantIndices v E 0 ab) with hβ
  set α := sSup (dominantIndices v E E ab) with hα
  refine ⟨(β - α).toNat, fun r hr hdvd => ?_⟩
  set vr : W → ℕ∞ := fun w => (r : ℕ∞) * v w with hvr
  have hr0 : (r : ℕ∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hvr0 : vr 0 = ⊤ := by simp only [hvr, hv0]; exact WithTop.mul_top hr0
  have hner : ∃ n : ℤ, vr (nfCoeff ab n) ≠ ⊤ := by
    obtain ⟨n, hn⟩ := hne
    exact ⟨n, WithTop.mul_ne_top (ENat.coe_ne_top r) hn⟩
  have hrE : 1 ≤ r * E := le_trans hr (Nat.le_mul_of_pos_right r hE)

  have hdom0 : dominantIndices vr (r * E) 0 ab = dominantIndices v E 0 ab := by
    have := dominantIndices_scale v E 0 r hr ab
    rwa [Nat.mul_zero] at this
  have hdomE : dominantIndices vr (r * E) (r * E) ab = dominantIndices v E E ab :=
    dominantIndices_scale v E E r hr ab
  have hβmem : β ∈ dominantIndices vr (r * E) 0 ab := by
    rw [hdom0, hβ, ← hdom0]; exact sInf_mem vr hvr0 (r * E) 0 (by omega) ab hb hner
  have hαmem : α ∈ dominantIndices vr (r * E) (r * E) ab := by
    rw [hdomE, hα, ← hdomE]; exact sSup_mem vr hvr0 (r * E) (r * E) (by omega) ab hb hner

  have hright : ∀ S : ℕ, S + 1 ≤ r * E →
      sInf (dominantIndices vr (r * E) S ab) ∈ dominantIndices vr (r * E) (S + 1) ab := by
    intro S hS
    apply sInf_mem_succ_of_dvd v hv0 E r hr S hS ab hb hne
    set n₀ := sInf (dominantIndices vr (r * E) S ab) with hn₀
    set m := sSup (dominantIndices vr (r * E) (S + 1) ab) with hm
    have hn₀mem : n₀ ∈ dominantIndices vr (r * E) S ab := sInf_mem vr hvr0 (r * E) S (by omega) ab hb hner
    have hmmem : m ∈ dominantIndices vr (r * E) (S + 1) ab :=
      sSup_mem vr hvr0 (r * E) (S + 1) (by omega) ab hb hner

    have h1 : n₀ ≤ β := by
      rcases Nat.eq_zero_or_pos S with hS0 | hS0
      ·
        have : n₀ = β := by rw [hn₀, hβ, hS0, hdom0]
        exact this.le
      · exact le_of_mem_of_mem vr hvr0 (r * E) hS0 (by omega) ab hb hner hβmem hn₀mem
    have h2 : α ≤ m := by
      rcases (Nat.lt_or_ge (S + 1) (r * E)) with hlt | hge
      · exact le_of_mem_of_mem vr hvr0 (r * E) hlt le_rfl ab hb hner hmmem hαmem
      · have hSE : S + 1 = r * E := le_antisymm hS hge
        have : m = α := by rw [hm, hα, hSE, hdomE]
        exact this.ge
    intro δ hδ1 hδeq
    have hle : δ ≤ (β - α).toNat := by omega
    exact dvd_trans (Nat.dvd_factorial (by omega) hle) hdvd
  refine ⟨hright, fun S hS1 hSE => ?_⟩
  have h := hright (S - 1) (by omega)
  rw [Nat.sub_add_cancel hS1] at h
  rw [sSup_eq_sInf_pred vr hvr0 (r * E) hS1 hSE ab hb hner h]
  exact sInf_mem vr hvr0 (r * E) (S - 1) (by omega) ab hb hner

p2m_export "AnnulusNoKink" "main"
end AnnulusNoKink

namespace AnnulusG3

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing Finset

variable {W : Type*} [CommRing W]

theorem annulusWeight_scale (E t r : ℕ) (d : Fin 2 →₀ ℕ) :
    annulusWeight (r * E) (r * t) d = r * annulusWeight E t d := by
  simp only [annulusWeight]
  rw [← Nat.mul_sub r E t]
  ring

theorem repGaussOrder_scale (v : W → ℕ∞) (E t r : ℕ) (F : MvPowerSeries (Fin 2) W) :
    repGaussOrder (fun w => (r : ℕ∞) * v w) (r * E) (r * t) F = (r : ℕ∞) * repGaussOrder v E t F := by
  unfold repGaussOrder
  have hterm : ∀ d : Fin 2 →₀ ℕ, (r : ℕ∞) * v (MvPowerSeries.coeff d F) + (annulusWeight (r * E) (r * t) d : ℕ∞) =
      (r : ℕ∞) * (v (MvPowerSeries.coeff d F) + (annulusWeight E t d : ℕ∞)) := by
    intro d; rw [annulusWeight_scale, Nat.cast_mul, mul_add]
  simp_rw [hterm]
  apply le_antisymm
  · obtain ⟨d₀, hd₀⟩ := ENat.exists_eq_iInf (fun d => v (MvPowerSeries.coeff d F) + (annulusWeight E t d : ℕ∞))
    rw [← hd₀]
    exact iInf_le _ d₀
  · exact le_iInf fun d => mul_le_mul_right (iInf_le _ d) _

theorem toNat_natCast_mul (r : ℕ) (g : ℕ∞) : ((r : ℕ∞) * g).toNat = r * g.toNat := by
  induction g using ENat.recTopCoe with
  | top =>
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp
      · have h : (r : ℕ∞) * ⊤ = ⊤ := WithTop.mul_top (Nat.cast_ne_zero.mpr (by omega))
        rw [h]; simp
  | coe n => rw [← Nat.cast_mul, ENat.toNat_coe, ENat.toNat_coe]

section DVR

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]

theorem vscale_eq (R q : ℕ) :
    (fun w => (R : ℕ∞) * ((q : ℕ∞) * IsDiscreteValuationRing.addVal W w)) =
      fun w => ((R * q : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w := by
  funext w; push_cast; ring

theorem dominantIndices_scale' (R q e p : ℕ) (hR : 1 ≤ R) (ab : PowerSeries W × PowerSeries W) :
    dominantIndices (fun w => ((R * q : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (R * q * e) (R * p) ab =
      dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab := by
  have := dominantIndices_scale (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p R hR ab
  rw [vscale_eq, ← Nat.mul_assoc] at this
  exact this

theorem exists_nfCoeff_finite (ϖ : W) (e q : ℕ) (hq : 1 ≤ q) (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) :
    ∃ n : ℤ, (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (nfCoeff ab n) ≠ ⊤ := by
  by_contra h
  push Not at h
  have hall : ∀ n : ℤ, nfCoeff ab n = 0 := by
    intro n
    have := h n
    by_contra hne
    exact WithTop.mul_ne_top (ENat.coe_ne_top q) (mt IsDiscreteValuationRing.addVal_eq_top_iff.mp hne) this
  apply hx
  rw [← habx]
  have ha : ∀ i : ℕ, PowerSeries.coeff i ab.1 = 0 := fun i => hall (Int.ofNat i)
  have hb' : ∀ j : ℕ, PowerSeries.coeff j ab.2 = 0 := by
    intro j
    cases j with
    | zero => rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hb
    | succ k => exact hall (Int.negSucc k)
  have hF : inU ab.1 + inV ab.2 = 0 := by
    ext d
    simp only [map_add, coeff_inU, coeff_inV, ha, hb', map_zero]
    simp
  rw [hF, map_zero]

theorem gaussOrder_toNat_scale (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (R : ℕ) (hR : 1 ≤ R) (x : UVCrossingModel W (ϖ ^ e))
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) (p : ℕ) (hp : p ≤ q * e) :
    ((gaussOrder (fun w => ((R * q : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (R * q * e) (R * p) x).toNat : ℤ) =
      R * (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x).toNat := by
  have hRq : 1 ≤ R * q := le_trans hR (Nat.le_mul_of_pos_right R hq)
  rw [gaussOrder_scaled_eq_repGaussOrder_normalForm ϖ hϖ e he (R * q) hRq x ab hb habx (R * p)
      (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left R hp),
    gaussOrder_scaled_eq_repGaussOrder_normalForm ϖ hϖ e he q hq x ab hb habx p hp]
  have := repGaussOrder_scale (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p R
    (inU ab.1 + inV ab.2)
  rw [vscale_eq, ← Nat.mul_assoc] at this
  rw [this, toNat_natCast_mul, Nat.cast_mul]

theorem fine_secants (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (Q : ℕ) (hQ : 1 ≤ Q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (hright : ∀ S : ℕ, S + 1 ≤ Q * e →
      sInf (dominantIndices (fun w => (Q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (Q * e) S ab) ∈
        dominantIndices (fun w => (Q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (Q * e) (S + 1) ab)
    (hleft : ∀ S : ℕ, 1 ≤ S → S ≤ Q * e →
      sSup (dominantIndices (fun w => (Q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (Q * e) S ab) ∈
        dominantIndices (fun w => (Q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (Q * e) (S - 1) ab) :
    (∀ S : ℕ, S + 1 ≤ Q * e →
      ((gaussOrder (fun w => (Q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (Q * e) (S + 1) x).toNat : ℤ) -
        (gaussOrder (fun w => (Q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (Q * e) S x).toNat =
      sInf (dominantIndices (fun w => (Q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (Q * e) S ab)) ∧
    (∀ S : ℕ, 1 ≤ S → S ≤ Q * e →
      sSup (dominantIndices (fun w => (Q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (Q * e) S ab) =
      sInf (dominantIndices (fun w => (Q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (Q * e) (S - 1) ab)) := by
  have h1 : ∀ S : ℕ, S + 1 ≤ Q * e →
      ((gaussOrder (fun w => (Q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (Q * e) (S + 1) x).toNat : ℤ) -
        (gaussOrder (fun w => (Q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (Q * e) S x).toNat =
      sInf (dominantIndices (fun w => (Q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (Q * e) S ab) :=
    fun S hS => gaussOrder_succ_sub_eq_sInf_dominantIndices ϖ hϖ e he Q hQ x hx ab hb habx S hS (hright S hS)
  refine ⟨h1, fun S hS1 hSE => ?_⟩
  have h2 := gaussOrder_sub_pred_eq_sSup_dominantIndices ϖ hϖ e he Q hQ x hx ab hb habx S hS1 hSE (hleft S hS1 hSE)
  have h3 := h1 (S - 1) (by omega)
  rw [Nat.sub_add_cancel hS1] at h3
  rw [← h2, ← h3]

end DVR

theorem block_const (δ : ℕ → ℤ) (a R : ℕ) (h : ∀ S : ℕ, a < S → S < a + R → δ S = δ (S - 1)) :
    ∀ k : ℕ, k < R → δ (a + k) = δ a := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      rw [← Nat.add_assoc, h (a + k + 1) (by omega) (by omega), Nat.add_sub_cancel]
      exact ih (by omega)

theorem telescope (f : ℕ → ℤ) (a R : ℕ) :
    f (a + R) - f a = ∑ k ∈ range R, (f (a + k + 1) - f (a + k)) := by
  have := Finset.sum_range_sub (fun k => f (a + k)) R
  simp only [Nat.add_zero] at this
  rw [← this]
  simp only [Nat.add_assoc]

section Main

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]

private theorem _root_.AnnulusG3.main
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (x' : UVCrossingModel W (ϖ ^ e)) (hx' : x' ≠ 0)
    (ab' : PowerSeries W × PowerSeries W) (hb' : PowerSeries.constantCoeff ab'.2 = 0)
    (habx' : mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) = x')
    (hoff : ∀ r s : ℕ, 1 ≤ r → ¬ r ∣ s → 0 < s → s < r * q * e →
        circleIndexDrop (fun w => ((r * q : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (r * q * e) s ab =
          circleIndexDrop (fun w => ((r * q : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (r * q * e) s ab') :

    ∀ p : ℕ, p + 1 ≤ q * e →
      (((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p + 1) x).toNat : ℤ)
          - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p + 1) x').toNat)
        - (((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x).toNat : ℤ)
          - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x').toNat)
        = sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab)
          - sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab') ∧
      (((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p + 1) x).toNat : ℤ)
          - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p + 1) x').toNat)
        - (((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x).toNat : ℤ)
          - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x').toNat)
        = sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (p + 1) ab)
          - sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (p + 1) ab') := by

  set Vq : W → ℕ∞ := fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w with hVq
  have hq0 : (q : ℕ∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hVq0 : Vq 0 = ⊤ := by
    simp only [hVq, IsDiscreteValuationRing.addVal_zero]; exact WithTop.mul_top hq0
  have hqe : 1 ≤ q * e := le_trans hq (Nat.le_mul_of_pos_right q he)

  obtain ⟨N₁, hN₁⟩ := AnnulusNoKink.main Vq hVq0 (q * e) hqe ab hb
    (exists_nfCoeff_finite ϖ e q hq x hx ab hb habx)
  obtain ⟨N₂, hN₂⟩ := AnnulusNoKink.main Vq hVq0 (q * e) hqe ab' hb'
    (exists_nfCoeff_finite ϖ e q hq x' hx' ab' hb' habx')
  set R : ℕ := Nat.factorial N₁ * Nat.factorial N₂ with hRdef
  have hR : 1 ≤ R := Nat.mul_pos (Nat.factorial_pos N₁) (Nat.factorial_pos N₂)
  obtain ⟨hr1, hl1⟩ := hN₁ R hR (dvd_mul_right _ _)
  obtain ⟨hr2, hl2⟩ := hN₂ R hR (dvd_mul_left _ _)

  have hRq : 1 ≤ R * q := le_trans hR (Nat.le_mul_of_pos_right R hq)
  have hsp : (fun w => (R : ℕ∞) * Vq w) = fun w => ((R * q : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w := by
    rw [hVq]; exact vscale_eq R q
  have hE : R * (q * e) = R * q * e := (Nat.mul_assoc R q e).symm
  rw [hsp, hE] at hr1 hl1 hr2 hl2
  obtain ⟨sec1, sup1⟩ := fine_secants ϖ hϖ e he (R * q) hRq x hx ab hb habx hr1 hl1
  obtain ⟨sec2, sup2⟩ := fine_secants ϖ hϖ e he (R * q) hRq x' hx' ab' hb' habx' hr2 hl2

  set GQ : UVCrossingModel W (ϖ ^ e) → ℕ → ℤ := fun y S =>
    ((gaussOrder (fun w => ((R * q : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (R * q * e) S y).toNat : ℤ)
    with hGQ
  set σ : (PowerSeries W × PowerSeries W) → ℕ → ℤ := fun c S =>
    sInf (dominantIndices (fun w => ((R * q : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (R * q * e) S c)
    with hσ
  have hsec1 : ∀ S, S + 1 ≤ R * q * e → GQ x (S + 1) - GQ x S = σ ab S := sec1
  have hsec2 : ∀ S, S + 1 ≤ R * q * e → GQ x' (S + 1) - GQ x' S = σ ab' S := sec2

  set δ : ℕ → ℤ := fun S => σ ab S - σ ab' S with hδ
  have hstep : ∀ S : ℕ, 1 ≤ S → S + 1 ≤ R * q * e → ¬ R ∣ S → δ S = δ (S - 1) := by
    intro S hS1 hSE hndvd
    have hcid := hoff R S hR hndvd (by omega) (by omega)

    simp only [circleIndexDrop] at hcid
    rw [sup1 S hS1 (by omega), sup2 S hS1 (by omega)] at hcid

    have hfin1 := dominantIndices_finite_nonempty ϖ hϖ e he (R * q) hRq x hx ab hb habx S hS1 hSE
    have hfin2 := dominantIndices_finite_nonempty ϖ hϖ e he (R * q) hRq x' hx' ab' hb' habx' S hS1 hSE
    have hnn1 : 0 ≤ σ ab (S - 1) - σ ab S := by
      have := csInf_le_csSup hfin1.2 hfin1.1.bddBelow hfin1.1.bddAbove
      rw [sup1 S hS1 (by omega)] at this
      simp only [hσ]; linarith
    have hnn2 : 0 ≤ σ ab' (S - 1) - σ ab' S := by
      have := csInf_le_csSup hfin2.2 hfin2.1.bddBelow hfin2.1.bddAbove
      rw [sup2 S hS1 (by omega)] at this
      simp only [hσ]; linarith
    have heq : σ ab (S - 1) - σ ab S = σ ab' (S - 1) - σ ab' S := by
      have := congrArg (fun n : ℕ => (n : ℤ)) hcid
      rwa [Int.toNat_of_nonneg hnn1, Int.toNat_of_nonneg hnn2] at this
    simp only [hδ]; linarith

  have hblock : ∀ p : ℕ, p + 1 ≤ q * e → ∀ k : ℕ, k < R → δ (R * p + k) = δ (R * p) := by
    intro p hp
    apply block_const δ (R * p) R
    intro S hS1 hS2
    have hRp1 : R * p + R = R * (p + 1) := by ring
    have hle : R * (p + 1) ≤ R * q * e :=
      calc R * (p + 1) ≤ R * (q * e) := Nat.mul_le_mul_left R hp
        _ = R * q * e := (Nat.mul_assoc R q e).symm
    refine hstep S (by omega) (by omega) ?_
    rintro ⟨m, rfl⟩
    have h1 : p < m := Nat.lt_of_mul_lt_mul_left hS1
    have h2 : m < p + 1 := Nat.lt_of_mul_lt_mul_left (by omega)
    omega

  intro p hp
  have hRp : R * p + R = R * (p + 1) := by ring
  have hblk : ∀ k, k < R → δ (R * p + k) = δ (R * p) := hblock p hp
  have hRpe : R * (p + 1) ≤ R * q * e :=
    calc R * (p + 1) ≤ R * (q * e) := Nat.mul_le_mul_left R hp
      _ = R * q * e := (Nat.mul_assoc R q e).symm

  have hsum : (GQ x (R * (p + 1)) - GQ x' (R * (p + 1))) - (GQ x (R * p) - GQ x' (R * p)) = R * δ (R * p) := by
    have t1 := telescope (GQ x) (R * p) R
    have t2 := telescope (GQ x') (R * p) R
    rw [hRp] at t1 t2
    have hs : ∑ k ∈ range R, ((GQ x (R * p + k + 1) - GQ x (R * p + k)) - (GQ x' (R * p + k + 1) - GQ x' (R * p + k)))
        = ∑ k ∈ range R, δ (R * p) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [hsec1 (R * p + k) (by omega), hsec2 (R * p + k) (by omega), ← hblk k hk]
    rw [Finset.sum_sub_distrib, ← t1, ← t2, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
    linarith

  have s1 := gaussOrder_toNat_scale ϖ hϖ e he q hq R hR x ab hb habx (p + 1) hp
  have s2 := gaussOrder_toNat_scale ϖ hϖ e he q hq R hR x' ab' hb' habx' (p + 1) hp
  have s3 := gaussOrder_toNat_scale ϖ hϖ e he q hq R hR x ab hb habx p (by omega)
  have s4 := gaussOrder_toNat_scale ϖ hϖ e he q hq R hR x' ab' hb' habx' p (by omega)
  have hGQ1 : GQ x (R * (p + 1)) = R * (gaussOrder Vq (ϖ ^ e) (q * e) (p + 1) x).toNat := s1
  have hGQ2 : GQ x' (R * (p + 1)) = R * (gaussOrder Vq (ϖ ^ e) (q * e) (p + 1) x').toNat := s2
  have hGQ3 : GQ x (R * p) = R * (gaussOrder Vq (ϖ ^ e) (q * e) p x).toNat := s3
  have hGQ4 : GQ x' (R * p) = R * (gaussOrder Vq (ϖ ^ e) (q * e) p x').toNat := s4
  rw [hGQ1, hGQ2, hGQ3, hGQ4] at hsum
  have hR0 : (R : ℤ) ≠ 0 := by exact_mod_cast (show R ≠ 0 by omega)
  have hcoarse : (((gaussOrder Vq (ϖ ^ e) (q * e) (p + 1) x).toNat : ℤ) - (gaussOrder Vq (ϖ ^ e) (q * e) (p + 1) x').toNat)
      - (((gaussOrder Vq (ϖ ^ e) (q * e) p x).toNat : ℤ) - (gaussOrder Vq (ϖ ^ e) (q * e) p x').toNat) = δ (R * p) := by
    apply mul_left_cancel₀ hR0
    linarith

  have hleftend : δ (R * p) = sInf (dominantIndices Vq (q * e) p ab) - sInf (dominantIndices Vq (q * e) p ab') := by
    simp only [hδ, hσ]
    rw [dominantIndices_scale' R q e p hR ab, dominantIndices_scale' R q e p hR ab']
  have hrightend : δ (R * p) = sSup (dominantIndices Vq (q * e) (p + 1) ab) -
      sSup (dominantIndices Vq (q * e) (p + 1) ab') := by
    rw [← hblk (R - 1) (by omega)]
    simp only [hδ, hσ]
    have e1 : R * (p + 1) - 1 = R * p + (R - 1) := by rw [Nat.mul_succ]; omega
    rw [← dominantIndices_scale' R q e (p + 1) hR ab, ← dominantIndices_scale' R q e (p + 1) hR ab',
      sup1 (R * (p + 1)) (by omega) hRpe, sup2 (R * (p + 1)) (by omega) hRpe, e1]
  exact ⟨hcoarse.trans hleftend, hcoarse.trans hrightend⟩

p2m_export "AnnulusG3" "main"
end Main

end AnnulusG3

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing in
theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (x' : UVCrossingModel W (ϖ ^ e)) (hx' : x' ≠ 0)
    (ab' : PowerSeries W × PowerSeries W) (hb' : PowerSeries.constantCoeff ab'.2 = 0)
    (habx' : mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) = x')
    (hoff : ∀ r s : ℕ, 1 ≤ r → ¬ r ∣ s → 0 < s → s < r * q * e →
        circleIndexDrop (fun w => ((r * q : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (r * q * e) s ab =
          circleIndexDrop (fun w => ((r * q : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W w) (r * q * e) s ab') :
    (∀ p : ℕ, 1 ≤ p → p + 1 ≤ q * e →
      ((((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x).toNat : ℤ)
          - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x').toNat)
        - (((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p - 1) x).toNat : ℤ)
          - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p - 1) x').toNat))
      - ((((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p + 1) x).toNat : ℤ)
          - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p + 1) x').toNat)
        - (((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x).toNat : ℤ)
          - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x').toNat))
      = (circleIndexDrop (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab : ℤ)
        - circleIndexDrop (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab') ∧
    ((((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) 1 x).toNat : ℤ)
        - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) 1 x').toNat)
      - (((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) 0 x).toNat : ℤ)
        - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) 0 x').toNat)
      = sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) 0 ab)
        - sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) 0 ab')) ∧
    ((((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (q * e) x).toNat : ℤ)
        - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (q * e) x').toNat)
      - (((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (q * e - 1) x).toNat : ℤ)
        - (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (q * e - 1) x').toNat)
      = sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (q * e) ab)
        - sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (q * e) ab')) := by
  have H := AnnulusG3.main ϖ hϖ e he q hq x hx ab hb habx x' hx' ab' hb' habx' hoff
  have hqe : 1 ≤ q * e := le_trans hq (Nat.le_mul_of_pos_right q he)
  refine ⟨fun p hp1 hpe => ?_, ?_, ?_⟩
  · obtain ⟨hA, -⟩ := H p hpe
    obtain ⟨-, hB⟩ := H (p - 1) (by omega)
    rw [Nat.sub_add_cancel hp1] at hB
    have hfin := dominantIndices_finite_nonempty ϖ hϖ e he q hq x hx ab hb habx p hp1 hpe
    have hfin' := dominantIndices_finite_nonempty ϖ hϖ e he q hq x' hx' ab' hb' habx' p hp1 hpe
    have hle := csInf_le_csSup hfin.2 hfin.1.bddBelow hfin.1.bddAbove
    have hle' := csInf_le_csSup hfin'.2 hfin'.1.bddBelow hfin'.1.bddAbove
    have c1 : ((circleIndexDrop (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab : ℕ) : ℤ) =
        sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) -
          sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) := by
      simp only [circleIndexDrop]; rw [Int.toNat_of_nonneg (by linarith)]
    have c2 : ((circleIndexDrop (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab' : ℕ) : ℤ) =
        sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab') -
          sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab') := by
      simp only [circleIndexDrop]; rw [Int.toNat_of_nonneg (by linarith)]
    rw [c1, c2]
    linarith
  · have := (H 0 (by omega)).1
    rw [Nat.zero_add] at this
    exact this
  · have := (H (q * e - 1) (by omega)).2
    rw [Nat.sub_add_cancel hqe] at this
    exact this

end S_ModularCurve_UVCrossingModel_slopeDrop_sub_eq_circleIndexDrop_sub_of_forall_circleIndexDrop_eq
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_slopeDrop_sub_eq_circleIndexDrop_sub_of_forall_circleIndexDrop_eq (solution)
