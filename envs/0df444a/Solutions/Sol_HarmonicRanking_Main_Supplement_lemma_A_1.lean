-- Prove2me | solution 1 for HarmonicRanking.Main.Supplement.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T13:32:13.277878+00:00
-- url     : https://prove2.me/submissions/b6e63b37-48bb-4d0f-8202-60fb23ae79f8

import Definitions.Def_HarmonicRanking_Main_Supplement_GridGames

set_option autoImplicit false

namespace HarmonicRanking.Main.Supplement

def cntA1 {m : ℕ} (c : Fin (m + 1) → Fin (m + 1)) (r : Fin m) : ℝ :=
  ((Finset.univ.filter fun j : Fin m => r.val < (c j.castSucc).val).card : ℝ)

lemma cntA1_nonneg {m : ℕ} (c : Fin (m + 1) → Fin (m + 1)) (r : Fin m) : 0 ≤ cntA1 c r := by
  unfold cntA1; positivity

lemma ell_eqA1 {m : ℕ} (c : Fin (m + 1) → Fin (m + 1)) (hc : IsPath c) (i : Fin m) :
    ell c i = cntA1 c i / m := by
  have hm : (0:ℝ) < m := by exact_mod_cast Fin.pos i
  set S : Set ℕ := {k : ℕ | ∃ hk : k < m + 1, i.val < (c ⟨k, hk⟩).val} with hS
  have hlast : c ⟨m, by omega⟩ = Fin.last m := hc.2
  have hne : S.Nonempty := ⟨m, by omega, by rw [hlast]; simpa using i.isLt⟩
  have hpmem : sInf S ∈ S := Nat.sInf_mem hne
  obtain ⟨hp, hip⟩ := hpmem
  have hfil : (Finset.univ.filter fun j : Fin m => i.val < (c j.castSucc).val)
      = Finset.univ.filter fun j : Fin m => sInf S ≤ j.val := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_contra hlt
      push Not at hlt
      exact Nat.notMem_of_lt_sInf hlt ⟨by omega, h⟩
    · intro h
      have : c ⟨sInf S, hp⟩ ≤ c j.castSucc := hc.1 (by
        show sInf S ≤ j.val
        exact h)
      exact lt_of_lt_of_le hip (by exact_mod_cast this)
  have hcard : (Finset.univ.filter fun j : Fin m => sInf S ≤ j.val).card = m - sInf S := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun j : Fin m => j.val < sInf S)
    have h2 : (Finset.univ.filter fun j : Fin m => j.val < sInf S).card = min m (sInf S) := by
      rw [← Fin.card_filter_val_lt]
    simp only [not_lt, Finset.card_univ, Fintype.card_fin] at h1
    omega
  unfold ell cntA1 pathInv
  rw [hfil, hcard]
  rw [Nat.cast_sub (by omega)]
  field_simp
  rfl


lemma phi_mulA1 {m : ℕ} (hm : 1 ≤ m) (g : Fin m → Fin m → ℝ) (c d : Fin (m + 1) → Fin (m + 1))
    (hc : IsPath c) (hd : IsPath d) :
    (m : ℝ) ^ 2 * Phi g c d = (m : ℝ) ^ 2
      + ∑ r : Fin m, ((d r.castSucc).val * (gAt g r (d r.castSucc).val - 1) )
      + ∑ r : Fin m, ((c r.castSucc).val * (gAt g r (c r.castSucc).val - 1)
          + cntA1 d r * gAt g r (c r.castSucc).val + cntA1 c r * gAt g r (d r.castSucc).val) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  unfold Phi
  have h2 : ∑ i : Fin m, (ell d i * gAt g i (c i.castSucc).val + ell c i * gAt g i (d i.castSucc).val)
      = (∑ i : Fin m, (cntA1 d i * gAt g i (c i.castSucc).val + cntA1 c i * gAt g i (d i.castSucc).val)) / m := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [ell_eqA1 c hc, ell_eqA1 d hd]; ring
  rw [h2]
  have h3 : ∑ i : Fin m, (((c i.castSucc).val : ℝ) * (gAt g i (c i.castSucc).val - 1) +
          ((d i.castSucc).val : ℝ) * (gAt g i (d i.castSucc).val - 1))
      = ∑ r : Fin m, (((c r.castSucc).val : ℝ) * (gAt g r (c r.castSucc).val - 1))
        + ∑ r : Fin m, ((d r.castSucc).val * (gAt g r (d r.castSucc).val - 1) ) := by
    rw [← Finset.sum_add_distrib]
  have h4 : ∑ r : Fin m, ((c r.castSucc).val * (gAt g r (c r.castSucc).val - 1)
          + cntA1 d r * gAt g r (c r.castSucc).val + cntA1 c r * gAt g r (d r.castSucc).val)
      = ∑ r : Fin m, (((c r.castSucc).val : ℝ) * (gAt g r (c r.castSucc).val - 1))
        + ∑ i : Fin m, (cntA1 d i * gAt g i (c i.castSucc).val + cntA1 c i * gAt g i (d i.castSucc).val) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h3, h4]
  field_simp
  ring

def toPath {m : ℕ} (a : Fin m → Fin (m + 1)) : Fin (m + 1) → Fin (m + 1) :=
  fun k => if h : k.val < m then ⟨m - (a (Fin.rev ⟨k.val, h⟩)).val, by omega⟩ else Fin.last m

def fromPath {m : ℕ} (c : Fin (m + 1) → Fin (m + 1)) : Fin m → Fin (m + 1) :=
  fun i => ⟨m - (c (Fin.rev i).castSucc).val, by omega⟩

lemma toPath_cs {m : ℕ} (a : Fin m → Fin (m + 1)) (j : Fin m) :
    (toPath a j.castSucc).val = m - (a (Fin.rev j)).val := by
  unfold toPath
  rw [dif_pos (show (j.castSucc).val < m from j.isLt)]
  rfl

lemma toPath_isPath {m : ℕ} (a : Fin m → Fin (m + 1)) (ha : Monotone a) : IsPath (toPath a) := by
  refine ⟨?_, ?_⟩
  · intro k k' hkk
    by_cases hk' : k'.val < m
    · have hk : k.val < m := lt_of_le_of_lt hkk hk'
      have h1 : Fin.rev (⟨k'.val, hk'⟩ : Fin m) ≤ Fin.rev ⟨k.val, hk⟩ := by
        rw [Fin.rev_le_rev]; exact hkk
      have h2 := ha h1
      have h3 : (a (Fin.rev ⟨k'.val, hk'⟩)).val ≤ (a (Fin.rev ⟨k.val, hk⟩)).val := h2
      show (toPath a k).val ≤ (toPath a k').val
      unfold toPath
      rw [dif_pos hk, dif_pos hk']
      show m - _ ≤ m - _
      omega
    · have : toPath a k' = Fin.last m := by unfold toPath; rw [dif_neg hk']
      rw [this]; exact Fin.le_last _
  · unfold toPath; rw [dif_neg (by simp)]

lemma fromPath_mono {m : ℕ} (c : Fin (m + 1) → Fin (m + 1)) (hc : IsPath c) :
    Monotone (fromPath c) := by
  intro i j hij
  have h1 : Fin.rev j ≤ Fin.rev i := by rw [Fin.rev_le_rev]; exact hij
  have h2 : c (Fin.rev j).castSucc ≤ c (Fin.rev i).castSucc := hc.1 (by simpa using h1)
  have h3 : (c (Fin.rev j).castSucc).val ≤ (c (Fin.rev i).castSucc).val := h2
  show (fromPath c i).val ≤ (fromPath c j).val
  unfold fromPath
  show m - _ ≤ m - _
  omega

lemma fromPath_toPath {m : ℕ} (a : Fin m → Fin (m + 1)) : fromPath (toPath a) = a := by
  funext i
  apply Fin.ext
  unfold fromPath
  show m - (toPath a (Fin.rev i).castSucc).val = _
  rw [toPath_cs]
  have := (a i).isLt
  simp only [Fin.rev_rev]
  omega

lemma toPath_fromPath {m : ℕ} (c : Fin (m + 1) → Fin (m + 1)) (hc : IsPath c) :
    toPath (fromPath c) = c := by
  funext k
  apply Fin.ext
  by_cases hk : k.val < m
  · have : k = (⟨k.val, hk⟩ : Fin m).castSucc := rfl
    rw [this, toPath_cs]
    unfold fromPath
    simp only [Fin.rev_rev]
    have := (c (⟨k.val, hk⟩ : Fin m).castSucc).isLt
    show m - (m - _) = _
    omega
  · have hk' : k = Fin.last m := Fin.ext (by have := k.isLt; simp; omega)
    subst hk'
    rw [hc.2]
    unfold toPath; rw [dif_neg (by simp)]

def Xf {m : ℕ} (c : Fin (m + 1) → Fin (m + 1)) (i j : Fin m) : ℝ :=
  if j.val + 1 ≤ (c i.castSucc).val then 1 else 0

lemma Xf_row {m : ℕ} (c : Fin (m + 1) → Fin (m + 1)) (i : Fin m) :
    ∑ j : Fin m, Xf c i j = ((c i.castSucc).val : ℝ) := by
  unfold Xf
  rw [Finset.sum_boole]
  have : (Finset.univ.filter fun j : Fin m => j.val + 1 ≤ (c i.castSucc).val)
      = Finset.univ.filter fun j : Fin m => j < (c i.castSucc).val := by
    ext j; simp [Nat.succ_le_iff]
  rw [this, Fin.card_filter_val_lt]
  have := (c i.castSucc).isLt
  have : min m (c i.castSucc).val = (c i.castSucc).val := by omega
  rw [this]

lemma Xf_col {m : ℕ} (c : Fin (m + 1) → Fin (m + 1)) (j : Fin m) :
    ∑ i : Fin m, Xf c i j = cntA1 c j := by
  unfold Xf cntA1
  rw [Finset.sum_boole]
  congr 3

lemma core {m : ℕ} (hm : 1 ≤ m) (g : Fin m → Fin m → ℝ) (c d : Fin (m + 1) → Fin (m + 1))
    (hc : IsPath c) (hd : IsPath d) (hfree : ∀ i j : Fin m, Xf c i j * Xf d j i = 0) :
    Phi g c d = (∑ i : Fin m, ∑ j : Fin m,
      ((1 - Xf c i j) * (1 - Xf d j i) + (Xf c i j + Xf d j i) *
        (gAt g i (c i.castSucc).val + gAt g j (d j.castSucc).val))) / (m : ℝ) ^ 2 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff (by positivity), mul_comm, phi_mulA1 hm g c d hc hd]
  have hterm : ∀ i j : Fin m,
      ((1 - Xf c i j) * (1 - Xf d j i) + (Xf c i j + Xf d j i) *
        (gAt g i (c i.castSucc).val + gAt g j (d j.castSucc).val))
      = 1 - Xf c i j - Xf d j i + gAt g i (c i.castSucc).val * Xf c i j
        + gAt g i (c i.castSucc).val * Xf d j i + gAt g j (d j.castSucc).val * Xf c i j
        + gAt g j (d j.castSucc).val * Xf d j i := by
    intro i j
    have := hfree i j
    linear_combination this
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Xf_row]
  have e2 : ∑ i : Fin m, ∑ j : Fin m, Xf d j i = ∑ j : Fin m, ((d j.castSucc).val : ℝ) := by
    rw [Finset.sum_comm]; simp only [Xf_row]
  have e3 : ∑ i : Fin m, gAt g i (c i.castSucc).val * ∑ j : Fin m, Xf d j i
      = ∑ i : Fin m, gAt g i (c i.castSucc).val * cntA1 d i := by
    apply Finset.sum_congr rfl; intro i _
    rw [← Xf_col d i]
  have e4 : ∑ i : Fin m, ∑ j : Fin m, gAt g j (d j.castSucc).val * Xf c i j
      = ∑ j : Fin m, gAt g j (d j.castSucc).val * cntA1 c j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [← Xf_col c j, Finset.mul_sum]
  have e5 : ∑ i : Fin m, ∑ j : Fin m, gAt g j (d j.castSucc).val * Xf d j i
      = ∑ j : Fin m, gAt g j (d j.castSucc).val * ((d j.castSucc).val : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.mul_sum, Xf_row]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [e2, e3, e4, e5]
  simp only [mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have k1 : ∑ x : Fin m, cntA1 d x * gAt g x (c x.castSucc).val
      = ∑ i : Fin m, gAt g i (c i.castSucc).val * cntA1 d i := by
    apply Finset.sum_congr rfl; intro i _; ring
  have k2 : ∑ x : Fin m, cntA1 c x * gAt g x (d x.castSucc).val
      = ∑ i : Fin m, gAt g i (d i.castSucc).val * cntA1 c i := by
    apply Finset.sum_congr rfl; intro i _; ring
  have k3 : ∑ x : Fin m, ((c x.castSucc).val : ℝ) * gAt g x (c x.castSucc).val
      = ∑ i : Fin m, gAt g i (c i.castSucc).val * ((c i.castSucc).val : ℝ) := by
    apply Finset.sum_congr rfl; intro i _; ring
  have k4 : ∑ x : Fin m, ((d x.castSucc).val : ℝ) * gAt g x (d x.castSucc).val
      = ∑ i : Fin m, gAt g i (d i.castSucc).val * ((d i.castSucc).val : ℝ) := by
    apply Finset.sum_congr rfl; intro i _; ring
  rw [k1, k2, k3, k4]
  ring

open HarmonicRanking.Main in
lemma hU {m : ℕ} (a b : Fin m → Fin (m + 1)) (i j : Fin m) :
    discreteU (a, b) (Fin.rev i) (Fin.rev j) = Xf (toPath a) i j := by
  unfold discreteU Xf
  rw [toPath_cs]
  simp only [Fin.val_rev]
  have := (a (Fin.rev i)).isLt
  have := j.isLt
  have := i.isLt
  congr 1
  apply propext
  omega

open HarmonicRanking.Main in
lemma hV {m : ℕ} (a b : Fin m → Fin (m + 1)) (i j : Fin m) :
    discreteV (a, b) (Fin.rev i) (Fin.rev j) = Xf (toPath b) j i := by
  unfold discreteV Xf
  rw [toPath_cs]
  have := (b (Fin.rev j)).isLt
  have := j.isLt
  have := i.isLt
  congr 1
  apply propext
  simp only [Fin.val_rev]
  omega

open HarmonicRanking.Main in
lemma hG {m : ℕ} (gh : Fin m → Fin m → ℝ) (a : Fin m → Fin (m + 1)) (i : Fin m) :
    ghatNext gh (Fin.rev i) (a (Fin.rev i)).val = gAt (reflect gh) i (toPath a i.castSucc).val := by
  unfold ghatNext gAt reflect
  rw [toPath_cs]
  have h1 := (a (Fin.rev i)).isLt
  by_cases h : (a (Fin.rev i)).val < m
  · rw [dif_pos h, dif_pos ⟨by omega, by omega⟩]
    congr 2
    show _ = m - ((m - _ - 1) + 1)
    omega
  · rw [dif_neg h, dif_neg (by omega)]

open HarmonicRanking.Main in
lemma gamma_eq {m : ℕ} (gh : Fin m → Fin m → ℝ) (a b : Fin m → Fin (m + 1)) :
    GammaHat gh (a, b) = (∑ i : Fin m, ∑ j : Fin m,
      ((1 - Xf (toPath a) i j) * (1 - Xf (toPath b) j i) + (Xf (toPath a) i j + Xf (toPath b) j i) *
        (gAt (reflect gh) i (toPath a i.castSucc).val
          + gAt (reflect gh) j (toPath b j.castSucc).val))) / (m : ℝ) ^ 2 := by
  unfold GammaHat
  congr 1
  rw [← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl; intro i _
  rw [← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl; intro j _
  simp only [Fin.revPerm_apply, hU, hV, hG]

lemma reflect_bij (m : ℕ) : Set.BijOn (reflect (m := m)) {gh | IsCompTable gh} {g | IsKTable g} := by
  have hrr : ∀ g : Fin m → Fin m → ℝ, reflect (reflect g) = g := by
    intro g; funext k r; simp [reflect]
  refine ⟨?_, ?_, ?_⟩
  · intro gh h
    obtain ⟨hb, hm, ha, hs⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · intro i; exact (hb _ _).1
    · intro i r r' hrr'
      exact ha _ (Fin.rev_le_rev.mpr hrr')
    · intro i r
      have := hs (Fin.rev i) (Fin.rev r)
      simpa [reflect] using this
  · intro g1 _ g2 _ h
    rw [← hrr g1, h, hrr]
  · intro g hg
    obtain ⟨h0, hmono, hs⟩ := hg
    have hge : ∀ i r, 0 ≤ g i r := fun i r =>
      le_trans (h0 i) (hmono i (show (⟨0, Fin.pos i⟩ : Fin m) ≤ r from Nat.zero_le _))
    refine ⟨reflect g, ?_, hrr g⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j
      refine ⟨hge _ _, ?_⟩
      have := hs (Fin.rev j) (Fin.rev i)
      have := hge (Fin.rev i) (Fin.rev j)
      simp only [reflect]
      linarith [hs (Fin.rev i) (Fin.rev j), hge (Fin.rev j) (Fin.rev i)]
    · intro j i i' hii'
      simp only [reflect]
      have h1 := hs (Fin.rev i) (Fin.rev j)
      have h2 := hs (Fin.rev i') (Fin.rev j)
      have := hmono (Fin.rev j) (Fin.rev_le_rev.mpr hii')
      linarith
    · intro i j j' hjj'
      exact hmono _ (Fin.rev_le_rev.mpr hjj')
    · intro i j
      have := hs (Fin.rev i) (Fin.rev j)
      simp only [reflect]
      linarith [hs (Fin.rev i) (Fin.rev j), hs (Fin.rev j) (Fin.rev i)]

lemma free_of_tf {m : ℕ} (c d : Fin (m + 1) → Fin (m + 1)) (h : IsTransposeFree c d) (i j : Fin m) :
    Xf c i j * Xf d j i = 0 := by
  have := h.2.2 i j
  unfold Xf
  by_cases h1 : j.val + 1 ≤ (c i.castSucc).val
  · by_cases h2 : i.val + 1 ≤ (d j.castSucc).val
    · exact absurd ⟨h1, h2⟩ this
    · simp [h2]
  · simp [h1]

open HarmonicRanking.Main in
lemma tf_of_adm {m : ℕ} (a b : Fin m → Fin (m + 1)) (ha : Monotone a) (hb : Monotone b)
    (h : discreteAdmissible (a, b)) : IsTransposeFree (toPath a) (toPath b) := by
  refine ⟨toPath_isPath a ha, toPath_isPath b hb, ?_⟩
  intro k r ⟨h1, h2⟩
  have := h (Fin.rev k) (Fin.rev r)
  rw [hU, hV] at this
  unfold Xf at this
  rw [if_pos h1, if_pos h2] at this
  norm_num at this

theorem solution_inner (m : ℕ) (hm : 1 ≤ m) :
    Set.BijOn (reflect (m := m)) {gh | IsCompTable gh} {g | IsKTable g} ∧
    ∀ gh : Fin m → Fin m → ℝ, IsCompTable gh →
      wholeCellMin gh = transposeFreeMin (reflect gh) := by
  refine ⟨reflect_bij m, ?_⟩
  intro gh _
  apply le_antisymm
  · unfold transposeFreeMin
    refine le_iInf fun c => le_iInf fun d => le_iInf fun h => ?_
    have hc := h.1
    have hd := h.2.1
    have hmc := fromPath_mono c hc
    have hmd := fromPath_mono d hd
    have hadm : discreteAdmissible (fromPath c, fromPath d) := by
      intro i j
      have := free_of_tf c d h (Fin.rev i) (Fin.rev j)
      have e1 := hU (fromPath c) (fromPath d) (Fin.rev i) (Fin.rev j)
      have e2 := hV (fromPath c) (fromPath d) (Fin.rev i) (Fin.rev j)
      rw [Fin.rev_rev, Fin.rev_rev] at e1 e2
      rw [e1, e2, toPath_fromPath c hc, toPath_fromPath d hd]
      exact this
    have hT : IsTUW (fromPath c, fromPath d) := ⟨hadm, hmc, hmd⟩
    have hfree : ∀ i j : Fin m, Xf c i j * Xf d j i = 0 := free_of_tf c d h
    have key : GammaHat gh (fromPath c, fromPath d) = Phi (reflect gh) c d := by
      rw [gamma_eq, core hm _ c d hc hd hfree, toPath_fromPath c hc, toPath_fromPath d hd]
    unfold wholeCellMin
    refine iInf_le_of_le (fromPath c, fromPath d) (iInf_le_of_le hT ?_)
    rw [key]
  · unfold wholeCellMin
    refine le_iInf fun cc => le_iInf fun hT => ?_
    obtain ⟨a, b⟩ := cc
    obtain ⟨hadm, hma, hmb⟩ := hT
    have htf := tf_of_adm a b hma hmb hadm
    have hfree : ∀ i j : Fin m, Xf (toPath a) i j * Xf (toPath b) j i = 0 :=
      free_of_tf _ _ htf
    have key : GammaHat gh (a, b) = Phi (reflect gh) (toPath a) (toPath b) := by
      rw [gamma_eq, core hm _ _ _ htf.1 htf.2.1 hfree]
    unfold transposeFreeMin
    refine iInf_le_of_le (toPath a) (iInf_le_of_le (toPath b) (iInf_le_of_le htf ?_))
    rw [key]

end HarmonicRanking.Main.Supplement

theorem solution (m : ℕ) (hm : 1 ≤ m) :
    Set.BijOn (HarmonicRanking.Main.Supplement.reflect (m := m)) {gh | HarmonicRanking.Main.Supplement.IsCompTable gh} {g | HarmonicRanking.Main.Supplement.IsKTable g} ∧
    ∀ gh : Fin m → Fin m → ℝ, HarmonicRanking.Main.Supplement.IsCompTable gh →
      HarmonicRanking.Main.Supplement.wholeCellMin gh = HarmonicRanking.Main.Supplement.transposeFreeMin (HarmonicRanking.Main.Supplement.reflect gh) :=
  HarmonicRanking.Main.Supplement.solution_inner m hm

