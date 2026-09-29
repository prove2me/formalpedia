-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_forall_factorial_dvd_sInf_dominantIndices_mem_succ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a07acd90-2598-5d4c-a588-b0f02e499ef4

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Theorems.Thm_ModularCurve_UVCrossingModel_repGaussOrder_normalForm_eq_iInf_termOrder
import Theorems.Thm_ModularCurve_UVCrossingModel_dominantIndices_scale
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_forall_factorial_dvd_sInf_dominantIndices_mem_succ

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

theorem main (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E : ℕ) (hE : 1 ≤ E)
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

end AnnulusNoKink

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing in
theorem solution
    {W : Type u} [CommRing W] (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E : ℕ) (hE : 1 ≤ E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hne : ∃ n : ℤ, v (nfCoeff ab n) ≠ ⊤) :
    ∃ N : ℕ, ∀ r : ℕ, 1 ≤ r → Nat.factorial N ∣ r →
      (∀ S : ℕ, S + 1 ≤ r * E →
        sInf (dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) S ab) ∈
          dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) (S + 1) ab) ∧
      (∀ S : ℕ, 1 ≤ S → S ≤ r * E →
        sSup (dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) S ab) ∈
          dominantIndices (fun w => (r : ℕ∞) * v w) (r * E) (S - 1) ab) :=
  AnnulusNoKink.main v hv0 E hE ab hb hne

end S_ModularCurve_UVCrossingModel_exists_forall_factorial_dvd_sInf_dominantIndices_mem_succ
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_forall_factorial_dvd_sInf_dominantIndices_mem_succ (solution)
