-- Prove2me | solution 1 for GlobalTheory.DI.AltClosed.prodL_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:09:40.304902+00:00
-- url     : https://prove2.me/submissions/6d6eeaa0-fe22-4a25-a2b0-0d05544d0d44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductCocycle
import Theorems.Thm_GlobalTheory_DI_AltClosed_oneC_empty
import Theorems.Thm_GlobalTheory_DI_AltClosed_dtot_oneC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI.AltClosed
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]
private theorem cubeSign_min_eq_one (s : Finset ι) (hs : s.Nonempty) : GlobalTheory.cubeSign s (s.min' hs) = 1 := by
  unfold GlobalTheory.cubeSign
  have e : ({x ∈ s | x < s.min' hs}) = ∅ := by
    apply Finset.filter_false_of_mem
    intro x hx
    exact not_lt.mpr (s.min'_le x hx)
  rw [e]
  simp
private theorem cubeSign_eq_neg_cubeSign_erase_min (s : Finset ι) (hs : s.Nonempty) (i : ι) (hi : i ∈ s.erase (s.min' hs)) :
    GlobalTheory.cubeSign s i = -GlobalTheory.cubeSign (s.erase (s.min' hs)) i := by
  have hne : i ≠ s.min' hs := Finset.ne_of_mem_erase hi
  have his : i ∈ s := Finset.mem_of_mem_erase hi
  have hlt : s.min' hs < i := lt_of_le_of_ne (s.min'_le i his) hne.symm
  unfold GlobalTheory.cubeSign
  have hfil : ({x ∈ s | x < i}) = insert (s.min' hs) ({x ∈ s.erase (s.min' hs) | x < i}) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hxs, hxi⟩
      by_cases hx : x = s.min' hs
      · exact Or.inl hx
      · exact Or.inr ⟨⟨hx, hxs⟩, hxi⟩
    · rintro (hx | ⟨⟨_, hxs⟩, hxi⟩)
      · rw [hx]
        exact ⟨s.min'_mem hs, hlt⟩
      · exact ⟨hxs, hxi⟩
  rw [hfil, Finset.card_insert_of_notMem (by simp), pow_succ]
  ring
private theorem delta_eq_erase_min_sub_sum_cubeSign {E : Type} [AddCommGroup E] (c : Finset ι → E) (s : Finset ι) (hs : s.Nonempty) :
    delta c s = c (s.erase (s.min' hs)) -
      ∑ i ∈ s.erase (s.min' hs), GlobalTheory.cubeSign (s.erase (s.min' hs)) i • c (s.erase i) := by
  unfold delta
  rw [← Finset.add_sum_erase s _ (s.min'_mem hs), cubeSign_min_eq_one s hs, one_smul, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [cubeSign_eq_neg_cubeSign_erase_min s hs i hi, neg_smul]
private theorem Lop_apply_of_min_eq (f : ι → V →+ V) (h : ι → ι → V →+ K) (v : V)
    (y : Finset ι → ExteriorAlgebra K V) (t : Finset ι) (m0 : ι) (ht : t.Nonempty) (hm : t.min' ht = m0) :
    Lop f h v y t = (-1 : ℤ) ^ t.card • (ExteriorAlgebra.ι K (f m0 v) * y t) +
      (if h2 : (t.erase m0).Nonempty then h m0 ((t.erase m0).min' h2) v • y (t.erase m0) else 0) := by
  subst hm
  unfold Lop
  rw [dif_pos ht]
private theorem neg_one_pow_card_erase_of_mem (t : Finset ι) (i : ι) (hi : i ∈ t) :
    (-1 : ℤ) ^ (t.erase i).card = -(-1) ^ t.card := by
  rw [Finset.card_erase_of_mem hi]
  obtain ⟨k, hk⟩ : ∃ k, t.card = k + 1 := ⟨t.card - 1, by have := Finset.card_pos.mpr ⟨i, hi⟩; omega⟩
  rw [hk, Nat.add_sub_cancel, pow_succ]
  ring
private theorem Dtot_Lop_eq_zero_of_Dtot_eq_zero_of_empty_eq_zero (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V)
    (h : ι → ι → V →+ K) (hd : IsOddDer d) (hD : IsDatum p d f h) (v : V)
    (y : Finset ι → ExteriorAlgebra K V) (hy : Dtot d y = 0) (hy0 : y ∅ = 0) :
    Dtot d (Lop f h v y) = 0 := by
  have hys : ∀ s : Finset ι, d (y s) = -((-1 : ℤ) ^ s.card • delta y s) := by
    intro s
    have e0 := congrFun hy s
    simp only [Dtot, Pi.zero_apply] at e0
    have e2 : (-1 : ℤ) ^ s.card • d (y s) = -delta y s := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact e0
    have e1 : ((-1 : ℤ) ^ s.card * (-1) ^ s.card) = 1 := by
      rw [← mul_pow]
      simp
    calc d (y s) = ((-1 : ℤ) ^ s.card * (-1) ^ s.card) • d (y s) := by rw [e1, one_smul]
      _ = (-1 : ℤ) ^ s.card • ((-1 : ℤ) ^ s.card • d (y s)) := mul_smul _ _ _
      _ = -((-1 : ℤ) ^ s.card • delta y s) := by rw [e2, smul_neg]
  have dsm : ∀ (k : K) (x : ExteriorAlgebra K V), d (k • x) = d (algebraMap K _ k) * x + k • d x := by
    intro k x
    rw [Algebra.smul_def, hd.mul, AlgHom.commutes, ← Algebra.smul_def]
  have dω : ∀ (i : ι) (x : ExteriorAlgebra K V),
      d (ExteriorAlgebra.ι K (f i v) * x) = -(ExteriorAlgebra.ι K (f i v) * d x) := by
    intro i x
    rw [hd.mul, hD.closed, zero_mul, zero_add]
    rw [show CliffordAlgebra.involute (ExteriorAlgebra.ι K (f i v)) = -ExteriorAlgebra.ι K (f i v) from
      CliffordAlgebra.involute_ι _, neg_mul]
  have hε : ∀ (n : ℕ) (x : ExteriorAlgebra K V), (-1 : ℤ) ^ n • ((-1 : ℤ) ^ n • x) = x := by
    intro n x
    rw [← mul_smul, ← mul_pow]
    simp
  funext s
  simp only [Dtot, Pi.zero_apply]
  by_cases hs : s.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp [delta, Lop]
  · rw [delta_eq_erase_min_sub_sum_cubeSign _ s hs]
    have hdy := delta_eq_erase_min_sub_sum_cubeSign y s hs
    set m := s.min' hs
    set s' := s.erase m
    have hms : m ∈ s := s.min'_mem hs
    have hLs := Lop_apply_of_min_eq f h v y s m hs rfl
    have hLi : ∀ i ∈ s', Lop f h v y (s.erase i) =
        -((-1 : ℤ) ^ s.card • (ExteriorAlgebra.ι K (f m v) * y (s.erase i))) +
        (if h2 : (s'.erase i).Nonempty then h m ((s'.erase i).min' h2) v • y (s'.erase i) else 0) := by
      intro i hi
      have hne : i ≠ m := Finset.ne_of_mem_erase hi
      have his : i ∈ s := Finset.mem_of_mem_erase hi
      have hmi : m ∈ s.erase i := Finset.mem_erase.mpr ⟨hne.symm, hms⟩
      have hmin : (s.erase i).min' ⟨m, hmi⟩ = m :=
        le_antisymm ((s.erase i).min'_le m hmi)
          (Finset.le_min' _ _ _ (fun z hz => s.min'_le z (Finset.mem_of_mem_erase hz)))
      rw [Lop_apply_of_min_eq f h v y (s.erase i) m ⟨m, hmi⟩ hmin, neg_one_pow_card_erase_of_mem s i his, neg_smul,
        Finset.erase_right_comm]
    have hsum : ∑ i ∈ s', GlobalTheory.cubeSign s' i • Lop f h v y (s.erase i) =
        -((-1 : ℤ) ^ s.card • (ExteriorAlgebra.ι K (f m v) * ∑ i ∈ s', GlobalTheory.cubeSign s' i • y (s.erase i))) +
        ∑ i ∈ s', GlobalTheory.cubeSign s' i •
          (if h2 : (s'.erase i).Nonempty then h m ((s'.erase i).min' h2) v • y (s'.erase i) else 0) := by
      rw [Finset.mul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hLi i hi, smul_add, smul_neg, mul_smul_comm, smul_comm (GlobalTheory.cubeSign s' i)]
    have hX : ∑ i ∈ s', GlobalTheory.cubeSign s' i • y (s.erase i) = y s' - delta y s := by
      rw [hdy]
      abel
    have hLs2 : Lop f h v y s = (-1 : ℤ) ^ s.card • (ExteriorAlgebra.ι K (f m v) * y s) +
        (if h2 : s'.Nonempty then h m (s'.min' h2) v • y s' else 0) := hLs
    rw [hsum, hLs2, hX, map_add, map_zsmul, dω, hys s]
    by_cases h2 : s'.Nonempty
    · set n := s'.min' h2 with hn_eq
      have hns : n ∈ s' := s'.min'_mem h2
      have hLs' : Lop f h v y s' = (-1 : ℤ) ^ s'.card • (ExteriorAlgebra.ι K (f n v) * y s') +
          (if h3 : (s'.erase n).Nonempty then h n ((s'.erase n).min' h3) v • y (s'.erase n) else 0) :=
        Lop_apply_of_min_eq f h v y s' n h2 rfl
      have hc : (-1 : ℤ) ^ s'.card = -(-1) ^ s.card := neg_one_pow_card_erase_of_mem s m hms
      have hSh : ∑ i ∈ s', GlobalTheory.cubeSign s' i •
          (if h3 : (s'.erase i).Nonempty then h m ((s'.erase i).min' h3) v • y (s'.erase i) else 0) =
          (if h3 : (s'.erase n).Nonempty then h n ((s'.erase n).min' h3) v • y (s'.erase n) else 0) +
            h m n v • delta y s' := by
        rw [← sub_eq_iff_eq_add]
        unfold delta
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.sum_eq_single n]
        · rw [show GlobalTheory.cubeSign s' n = 1 from cubeSign_min_eq_one s' h2]
          simp only [one_smul]
          by_cases h3 : (s'.erase n).Nonempty
          · rw [dif_pos h3, dif_pos h3, ← sub_smul]
            congr 1
            rw [← hD.cocycle m n ((s'.erase n).min' h3) v]
            ring
          · rw [dif_neg h3, dif_neg h3, Finset.not_nonempty_iff_eq_empty.mp h3, hy0]
            simp
        · intro b hb hbn
          have hnb : n ∈ s'.erase b := Finset.mem_erase.mpr ⟨fun e => hbn e.symm, hns⟩
          have hmin : (s'.erase b).min' ⟨n, hnb⟩ = n :=
            le_antisymm ((s'.erase b).min'_le n hnb)
              (Finset.le_min' _ _ _ (fun z hz => s'.min'_le z (Finset.mem_of_mem_erase hz)))
          rw [dif_pos ⟨n, hnb⟩, hmin, smul_comm (h m n v) (GlobalTheory.cubeSign s' b), sub_self]
        · intro hn
          exact absurd hns hn
      have hcomm : ∀ x : ExteriorAlgebra K V,
          h m n v • ((-1 : ℤ) ^ s.card • x) = (-1 : ℤ) ^ s.card • (h m n v • x) :=
        fun x => smul_comm _ _ _
      rw [dif_pos h2, ← hn_eq, hSh, hLs', dsm, hD.dh, hys s', hc]
      simp only [neg_smul, smul_neg, neg_neg, mul_neg, mul_sub, sub_mul, smul_add, smul_sub,
        mul_smul_comm, hε, hcomm]
      abel
    · have hs'e : s' = ∅ := Finset.not_nonempty_iff_eq_empty.mp h2
      have hdy0 : delta y s = 0 := by
        rw [hdy, hs'e]
        simp [hy0]
      rw [dif_neg h2, hdy0, hs'e]
      simp [Lop, hy0]
end GlobalTheory.DI.AltClosed
end

set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI GlobalTheory.DI.AltClosed
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]
namespace GlobalTheory.DI.AltClosed
theorem _root_.solution (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V)
    (h : ι → ι → V →+ K) (hd : IsOddDer d) (hD : IsDatum p d f h) (vs : List V) :
    Dtot d (prodL f h vs) = 0 ∧ prodL f h vs ∅ = 0 := by
  induction vs with
  | nil => exact ⟨dtot_oneC d hd, oneC_empty (ι := ι)⟩
  | cons v vs ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · exact Dtot_Lop_eq_zero_of_Dtot_eq_zero_of_empty_eq_zero p d f h hd hD v _ h1 h2
    · simp [prodL, Lop]
end GlobalTheory.DI.AltClosed
