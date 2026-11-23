-- Prove2me | solution 1 for HarmonicRanking.Main.Supplement.theorem_B_3
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T17:59:06.070838+00:00
-- url     : https://prove2.me/submissions/24a30d45-e7e5-4220-9ded-2cef2f099090

import Definitions.Def_HarmonicRanking_Main_Supplement_PriceLP

set_option autoImplicit false

namespace HarmonicRanking.Main.Supplement

noncomputable section

open Classical

/-! ## Definitions -/

/-- `F_{s,r}` extended by `0` for `s ≥ m`. -/
def Fext {m : ℕ} (F : Fin m → Fin m → ℝ) (r : Fin m) (s : ℕ) : ℝ :=
  if h : s < m then F ⟨s, h⟩ r else 0

/-- Abel coefficients `c_{ℓ r} = F_{ℓ r} - F_{ℓ+1, r}` (with `F_{m,r} = 0`). -/
def cc {m : ℕ} (F : Fin m → Fin m → ℝ) (ℓ r : Fin m) : ℝ :=
  Fext F r ℓ.val - Fext F r (ℓ.val + 1)

/-- `z_i(c) = max ({j+1 : c_j ≤ i} ∪ {0})` (zero-based). -/
def zc {m : ℕ} (c : Fin m → ℕ) (i : Fin m) : ℕ :=
  (Finset.univ.filter (fun j : Fin m => c j ≤ i.val)).sup (fun j => j.val + 1)

/-- Reflected occupation level of column `k` in a canonical cover. -/
def sel (x z k : ℕ) : ℕ := if k + 1 ≤ z then max x (k + 1) else x

/-- Cost of the canonical doubled cover with full-row counts `a`, `b`. -/
def Ccost {m : ℕ} (g : Fin m → Fin m → ℝ) (a b : Fin m → ℕ) : ℝ :=
  ∑ i : Fin m, ∑ k : Fin m,
    (gAt g i (sel (a i) (zc b i) k.val) + gAt g i (sel (b i) (zc a i) k.val))

/-- Path `(a_0,…,a_{m-1}, m)`. -/
def toPath {m : ℕ} (a : Fin m → ℕ) : Fin (m + 1) → Fin (m + 1) := fun k =>
  if h : k.val < m then ⟨min (a ⟨k.val, h⟩) m, by omega⟩ else Fin.last m

/-- `â_i = min_{j ≥ i} a_j`. -/
def amono {m : ℕ} (a : Fin m → ℕ) (i : Fin m) : ℕ :=
  (Finset.univ.filter (fun j : Fin m => i ≤ j)).inf' ⟨i, by simp⟩ a

/-- `m² Φ` written on sequences. -/
def PhiS {m : ℕ} (g : Fin m → Fin m → ℝ) (a b : Fin m → ℕ) : ℝ :=
  (m : ℝ) ^ 2 + ∑ i : Fin m,
    ((a i : ℝ) * gAt g i (a i) - a i + (b i : ℝ) * gAt g i (b i) - b i +
      ((m : ℝ) - zc b i) * gAt g i (a i) + ((m : ℝ) - zc a i) * gAt g i (b i))

/-- Number of full rows of the table of passive rank `rev i`. -/
def nfull {m : ℕ} (A : Fin m → Fin m → Fin m → Prop) (i : Fin m) : ℕ :=
  (Finset.univ.filter (fun ℓ : Fin m => ∀ p, A ℓ (Fin.rev i) p)).card

theorem tele_range (f : ℕ → ℝ) (n s : ℕ) (hs : s ≤ n) :
    ∑ ℓ ∈ Finset.range n, (if s ≤ ℓ then f ℓ - f (ℓ + 1) else 0) = f s - f n := by
  induction n with
  | zero => obtain rfl : s = 0 := by omega
            simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge n s with h | h
    · obtain rfl : s = n + 1 := by omega
      rw [if_neg (by omega), Finset.sum_eq_zero]
      · ring
      · intro ℓ hℓ; rw [Finset.mem_range] at hℓ; rw [if_neg (by omega)]
    · rw [ih h, if_pos h]; ring

theorem sum_cc_ge {m : ℕ} (F : Fin m → Fin m → ℝ) (r : Fin m) (s : ℕ) (hs : s ≤ m) :
    ∑ ℓ : Fin m, (if s ≤ ℓ.val then cc F ℓ r else 0) = Fext F r s := by
  have := Fin.sum_univ_eq_sum_range
    (fun ℓ => if s ≤ ℓ then Fext F r ℓ - Fext F r (ℓ + 1) else 0) m
  simp only [cc]
  rw [this, tele_range _ m s hs]
  simp [Fext]

theorem abel {m : ℕ} (F : Fin m → Fin m → ℝ) (x : Fin m → Fin m → Fin m → ℝ) (r p : Fin m) :
    ∑ ℓ, F ℓ r * x ℓ r p = ∑ ℓ, cc F ℓ r * cumY x ℓ r p := by
  simp only [cumY, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  have e : ∀ ℓ : Fin m, cc F ℓ r * (if h ≤ ℓ then x h r p else 0) =
      x h r p * (if h.val ≤ ℓ.val then cc F ℓ r else 0) := by
    intro ℓ
    by_cases hh : h.val ≤ ℓ.val
    · simp [Fin.le_iff_val_le_val, hh, mul_comm]
    · simp [Fin.le_iff_val_le_val, hh]
  simp only [e, ← Finset.mul_sum]
  rw [sum_cc_ge F r h.val h.isLt.le]
  simp [Fext, mul_comm]

theorem gAt_reflect {m : ℕ} (F : Fin m → Fin m → ℝ) (i : Fin m) (k : ℕ) (hk : k ≤ m) :
    gAt (priceReflect F) i k = Fext F (Fin.rev i) (m - k) := by
  unfold gAt Fext priceReflect
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · rw [dif_pos ⟨hk0, hk⟩, dif_pos (by omega)]
    congr 1
    ext; simp [Fin.val_rev]; omega

theorem cc_nonneg {m : ℕ} (F : Fin m → Fin m → ℝ) (hF : InA F) (ℓ r : Fin m) :
    0 ≤ cc F ℓ r := by
  obtain ⟨-, hb, ha, -⟩ := hF
  unfold cc Fext
  rw [dif_pos ℓ.isLt]
  split_ifs with h
  · have := ha r (show ℓ ≤ ⟨ℓ.val + 1, h⟩ from Fin.le_iff_val_le_val.mpr (by simp))
    simp only at this; linarith
  · linarith [(hb ℓ r).1]

theorem zc_le {m : ℕ} (c : Fin m → ℕ) (i : Fin m) : zc c i ≤ m :=
  Finset.sup_le fun j _ => j.isLt

theorem lt_zc_iff {m : ℕ} (c : Fin m → ℕ) (hc : Monotone c) (i q : Fin m) :
    q.val < zc c i ↔ c q ≤ i.val := by
  constructor
  · intro h
    obtain ⟨j, hj, hqj⟩ := (Finset.lt_sup_iff (s := Finset.univ.filter (fun j : Fin m => c j ≤ i.val))
      (f := fun j : Fin m => j.val + 1)).mp h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact (hc (Fin.le_iff_val_le_val.mpr (by omega))).trans hj
  · intro h
    have : q.val + 1 ≤ zc c i :=
      Finset.le_sup (f := fun j : Fin m => j.val + 1) (by simp [h])
    omega

theorem zc_mono {m : ℕ} (c : Fin m → ℕ) : Monotone (zc c) := by
  intro i i' h
  apply Finset.sup_mono
  intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro hj; exact hj.trans (Fin.le_iff_val_le_val.mp h)

theorem toPath_val {m : ℕ} (a : Fin m → ℕ) (ha : ∀ i, a i ≤ m) (i : Fin m) :
    (toPath a i.castSucc).val = a i := by
  simp [toPath, ha i]

theorem pathInv_toPath {m : ℕ} (a : Fin m → ℕ) (ha : ∀ i, a i ≤ m) (hma : Monotone a)
    (i : Fin m) : pathInv (toPath a) i.val = zc a i := by
  unfold pathInv
  have hz := zc_le a i
  have hmem : zc a i ∈ {k : ℕ | ∃ hk : k < m + 1, i.val < (toPath a ⟨k, hk⟩).val} := by
    refine ⟨by omega, ?_⟩
    rcases Nat.lt_or_ge (zc a i) m with h | h
    · have h1 := (lt_zc_iff a hma i ⟨zc a i, h⟩).not.mp (lt_irrefl _)
      simp [toPath, h, ha]; omega
    · have : zc a i = m := by omega
      simp [toPath, this]
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨_, hmem⟩
  rintro k ⟨hk, hlt⟩
  by_contra hcon
  push_neg at hcon
  have h1 := (lt_zc_iff a hma i ⟨k, by omega⟩).mp hcon
  simp [toPath, show k < m by omega] at hlt
  omega

theorem path_seq {m : ℕ} (P : Fin (m + 1) → Fin (m + 1)) (hP : IsPath P) :
    (∀ i : Fin m, (P i.castSucc).val ≤ m) ∧ Monotone (fun i : Fin m => (P i.castSucc).val) ∧
      toPath (fun i : Fin m => (P i.castSucc).val) = P := by
  refine ⟨fun i => by have := (P i.castSucc).isLt; omega, fun i j h => hP.1 (by simpa using h), ?_⟩
  funext k
  unfold toPath
  split_ifs with h
  · ext; simp only; rw [min_eq_left (by have := (P (Fin.castSucc ⟨k.val, h⟩)).isLt; omega)]; rfl
  · have : k = Fin.last m := by ext; simp; omega
    rw [this, hP.2]

theorem toPath_isPath {m : ℕ} (a : Fin m → ℕ) (hma : Monotone a) : IsPath (toPath a) := by
  refine ⟨fun k k' h => ?_, by simp [toPath]⟩
  unfold toPath
  have h' := Fin.le_iff_val_le_val.mp h
  split_ifs with h1 h2 h2
  · simp only [Fin.le_iff_val_le_val]
    exact min_le_min_right _ (hma (Fin.le_iff_val_le_val.mpr (by simpa using h')))
  · simp [Fin.le_iff_val_le_val]
  · omega
  · exact le_rfl

theorem PhiS_eq {m : ℕ} (g : Fin m → Fin m → ℝ) (hm : 1 ≤ m) (a b : Fin m → ℕ)
    (ha : ∀ i, a i ≤ m) (hb : ∀ i, b i ≤ m) (hma : Monotone a) (hmb : Monotone b) :
    PhiS g a b = (m : ℝ) ^ 2 * Phi g (toPath a) (toPath b) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold Phi PhiS ell
  simp only [toPath_val a ha, toPath_val b hb, pathInv_toPath a ha hma, pathInv_toPath b hb hmb]
  rw [mul_add, mul_add, mul_div_cancel₀ _ (pow_ne_zero 2 hm0), mul_one]
  rw [show (m : ℝ) ^ 2 * ((∑ i : Fin m, ((1 - (zc b i : ℝ) / m) * gAt g i (a i) +
      (1 - (zc a i : ℝ) / m) * gAt g i (b i))) / m) =
      ∑ i : Fin m, ((m : ℝ) * ((1 - (zc b i : ℝ) / m) * gAt g i (a i) +
      (1 - (zc a i : ℝ) / m) * gAt g i (b i))) by
    rw [← Finset.mul_sum]; field_simp]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp
  ring

/-! ## Telescoping / Abel summation -/





theorem sel_le {m : ℕ} (x z k : ℕ) (hx : x ≤ m) (hk : k < m) : sel x z k ≤ m := by
  unfold sel; split_ifs <;> omega

theorem sel_mono_x (x x' z k : ℕ) (h : x ≤ x') : sel x z k ≤ sel x' z k := by
  unfold sel; split_ifs <;> omega

theorem sel_z (x z z' k : ℕ) (h : z' ≤ max z x) : sel x z' k ≤ sel x z k := by
  unfold sel; split_ifs <;> omega

theorem x_le_sel (x z k : ℕ) : x ≤ sel x z k := by
  unfold sel; split_ifs <;> omega

theorem Fext_anti {m : ℕ} (F : Fin m → Fin m → ℝ) (hF : InA F) (r : Fin m) (s s' : ℕ)
    (h : s ≤ s') : Fext F r s' ≤ Fext F r s := by
  obtain ⟨-, hb, ha, -⟩ := hF
  unfold Fext
  split_ifs with h1 h2 h2
  · exact ha r (Fin.le_iff_val_le_val.mpr h)
  · omega
  · exact (hb _ r).1
  · exact le_rfl

theorem gAt_mono {m : ℕ} (F : Fin m → Fin m → ℝ) (hF : InA F) (i : Fin m) (k k' : ℕ)
    (h : k ≤ k') (hk' : k' ≤ m) :
    gAt (priceReflect F) i k ≤ gAt (priceReflect F) i k' := by
  rw [gAt_reflect F i k (by omega), gAt_reflect F i k' hk']
  exact Fext_anti F hF _ _ _ (by omega)

theorem amono_le {m : ℕ} (a : Fin m → ℕ) (i : Fin m) : amono a i ≤ a i :=
  Finset.inf'_le _ (by simp)

theorem amono_mono {m : ℕ} (a : Fin m → ℕ) : Monotone (amono a) := by
  intro i i' h
  apply Finset.inf'_mono
  intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun hj => h.trans hj

theorem zc_amono {m : ℕ} (a : Fin m → ℕ) : zc (amono a) = zc a := by
  funext i
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨j', hj', he⟩ := Finset.exists_mem_eq_inf'
      (s := Finset.univ.filter (fun j' : Fin m => j ≤ j')) ⟨j, by simp⟩ a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
    have : j'.val + 1 ≤ zc a i :=
      Finset.le_sup (f := fun j : Fin m => j.val + 1) (by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        unfold amono at hj; rw [he] at hj; exact hj)
    have := Fin.le_iff_val_le_val.mp hj'
    omega
  · apply Finset.sup_mono
    intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun hj => (amono_le a j).trans hj

theorem zc_overlap {m : ℕ} (c d : Fin m → ℕ) (q : Fin m) :
    zc (fun i => min (c i) (zc d i)) q ≤ max (zc c q) (d q) := by
  apply Finset.sup_le
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  rcases le_total (c j) (zc d j) with h | h
  · rw [min_eq_left h] at hj
    have : j.val + 1 ≤ zc c q :=
      Finset.le_sup (f := fun j : Fin m => j.val + 1) (by simp [hj])
    omega
  · rw [min_eq_right h] at hj
    by_contra hcon
    have hdq : d q ≤ j.val := by omega
    have : q.val + 1 ≤ zc d j :=
      Finset.le_sup (f := fun j : Fin m => j.val + 1) (by simp [hdq])
    omega

theorem Ccost_mono {m : ℕ} (F : Fin m → Fin m → ℝ) (hF : InA F) (a b a' b' : Fin m → ℕ)
    (ha : ∀ i, a i ≤ m) (hb : ∀ i, b i ≤ m)
    (hA : ∀ i k : Fin m, sel (a' i) (zc b' i) k ≤ sel (a i) (zc b i) k)
    (hB : ∀ i k : Fin m, sel (b' i) (zc a' i) k ≤ sel (b i) (zc a i) k) :
    Ccost (priceReflect F) a' b' ≤ Ccost (priceReflect F) a b := by
  unfold Ccost
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => add_le_add ?_ ?_
  · exact gAt_mono F hF i _ _ (hA i k) (sel_le _ _ _ (ha i) k.isLt)
  · exact gAt_mono F hF i _ _ (hB i k) (sel_le _ _ _ (hb i) k.isLt)

theorem reduce {m : ℕ} (F : Fin m → Fin m → ℝ) (hF : InA F) (a b : Fin m → ℕ)
    (ha : ∀ i, a i ≤ m) (hb : ∀ i, b i ≤ m) :
    ∃ a' b' : Fin m → ℕ, (∀ i, a' i ≤ m) ∧ (∀ i, b' i ≤ m) ∧ Monotone a' ∧ Monotone b' ∧
      (∀ i, a' i ≤ zc b' i) ∧
      Ccost (priceReflect F) a' b' ≤ Ccost (priceReflect F) a b := by
  have ham : ∀ i, amono a i ≤ m := fun i => (amono_le a i).trans (ha i)
  have hbm : ∀ i, amono b i ≤ m := fun i => (amono_le b i).trans (hb i)
  refine ⟨fun i => min (amono a i) (zc (amono b) i), amono b, fun i => (min_le_left _ _).trans (ham i),
    hbm, fun i j h => min_le_min (amono_mono a h) (zc_mono _ h), amono_mono b,
    fun i => min_le_right _ _, ?_⟩
  refine (Ccost_mono F hF _ _ _ _ ham hbm ?_ ?_).trans (Ccost_mono F hF _ _ _ _ ha hb ?_ ?_)
  · intro i k; exact sel_mono_x _ _ _ _ (min_le_left _ _)
  · intro i k; exact sel_z _ _ _ _ (zc_overlap _ _ i)
  · intro i k; rw [zc_amono]; exact sel_mono_x _ _ _ _ (amono_le a i)
  · intro i k; rw [zc_amono]; exact sel_mono_x _ _ _ _ (amono_le b i)

theorem count_Ico (m x z : ℕ) (hxz : x ≤ z) (hz : z ≤ m) :
    ∑ k : Fin m, (if x ≤ k.val ∧ k.val < z then (1 : ℝ) else 0) = (z : ℝ) - x := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if x ≤ k ∧ k < z then (1 : ℝ) else 0) m,
    Finset.sum_boole]
  have : (Finset.range m).filter (fun k => x ≤ k ∧ k < z) = Finset.Ico x z := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [this, Nat.card_Ico, Nat.cast_sub hxz]

theorem Hsum {m : ℕ} (g : Fin m → Fin m → ℝ) (i : Fin m) (x z : ℕ) (hxz : x ≤ z) (hz : z ≤ m) :
    ∑ k : Fin m, gAt g i (sel x z k.val) =
      ((x : ℝ) + m - z) * gAt g i x +
        ∑ k : Fin m, (if x ≤ k.val ∧ k.val < z then gAt g i (k.val + 1) else 0) := by
  have e : ∀ k : Fin m, gAt g i (sel x z k.val) =
      (if x ≤ k.val ∧ k.val < z then gAt g i (k.val + 1) else 0) +
        (1 - (if x ≤ k.val ∧ k.val < z then (1 : ℝ) else 0)) * gAt g i x := by
    intro k; unfold sel
    by_cases h : x ≤ k.val ∧ k.val < z
    · rw [if_pos (by omega), max_eq_right (by omega), if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]
      split_ifs with h2
      · rw [max_eq_left (by omega)]; ring
      · ring
  simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
    count_Ico m x z hxz hz]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

theorem gAt_succ {m : ℕ} (g : Fin m → Fin m → ℝ) (i k : Fin m) :
    gAt g i (k.val + 1) = g i k := by
  unfold gAt
  rw [dif_pos ⟨by omega, k.isLt⟩]
  simp

theorem b_le_zc {m : ℕ} (a b : Fin m → ℕ) (hb : ∀ i, b i ≤ m) (hmb : Monotone b)
    (hma : Monotone a) (hab : ∀ i, a i ≤ zc b i) (q : Fin m) : b q ≤ zc a q := by
  by_contra hcon
  push_neg at hcon
  have hbq := hb q
  set j : Fin m := ⟨b q - 1, by omega⟩
  have h1 : ¬ a j ≤ q.val := fun h => by
    have := (lt_zc_iff a hma q j).mpr h
    simp [j] at this; omega
  have h2 : q.val < zc b j := by have := hab j; omega
  have h3 := (lt_zc_iff b hmb j q).mp h2
  simp [j] at h3; omega

theorem identity {m : ℕ} (F : Fin m → Fin m → ℝ) (hF : InA F) (a b : Fin m → ℕ)
    (ha : ∀ i, a i ≤ m) (hb : ∀ i, b i ≤ m) (hma : Monotone a) (hmb : Monotone b)
    (hab : ∀ i, a i ≤ zc b i) :
    Ccost (priceReflect F) a b = PhiS (priceReflect F) a b := by
  set g := priceReflect F
  have hba := b_le_zc a b hb hmb hma hab
  have hcomp : ∀ i k : Fin m, g i k + g k i = 1 := fun i k => by
    simp only [g, priceReflect]; exact hF.1 _ _
  -- residual sums
  set RA : Fin m → Fin m → ℝ := fun i k =>
    if a i ≤ k.val ∧ k.val < zc b i then gAt g i (k.val + 1) else 0
  set RB : Fin m → Fin m → ℝ := fun i k =>
    if b i ≤ k.val ∧ k.val < zc a i then gAt g i (k.val + 1) else 0
  have hC : Ccost g a b = ∑ i : Fin m, ((((a i : ℝ) + m - zc b i) * gAt g i (a i) +
      (((b i : ℝ) + m - zc a i) * gAt g i (b i))) + ∑ k, RA i k + ∑ k, RB i k) := by
    unfold Ccost
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_add_distrib, Hsum g i _ _ (hab i) (zc_le b i),
      Hsum g i _ _ (hba i) (zc_le a i)]
    ring
  have hcond : ∀ i k : Fin m, (b k ≤ i.val ∧ i.val < zc a k) ↔ (a i ≤ k.val ∧ k.val < zc b i) := by
    intro i k
    rw [lt_zc_iff a hma, lt_zc_iff b hmb]; tauto
  have hR : ∑ i, ∑ k, RA i k + ∑ i, ∑ k, RB i k =
      ∑ i : Fin m, ∑ k : Fin m, (if a i ≤ k.val ∧ k.val < zc b i then (1 : ℝ) else 0) := by
    rw [Finset.sum_comm (f := RB), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [RA, RB, hcond]
    split_ifs
    · rw [gAt_succ, gAt_succ, hcomp]
    · ring
  have hcount : ∑ i : Fin m, ∑ k : Fin m,
      (if a i ≤ k.val ∧ k.val < zc b i then (1 : ℝ) else 0) =
      (m : ℝ) ^ 2 - ∑ i : Fin m, ((a i : ℝ) + b i) := by
    simp only [fun i => count_Ico m (a i) (zc b i) (hab i) (zc_le b i)]
    have hz : ∀ i : Fin m, (zc b i : ℝ) =
        ∑ k : Fin m, (if b k ≤ i.val then (1 : ℝ) else 0) := by
      intro i
      rw [← Nat.sub_zero (zc b i), Nat.cast_sub (Nat.zero_le _),
        ← count_Ico m 0 (zc b i) (Nat.zero_le _) (zc_le b i)]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Nat.zero_le, true_and, lt_zc_iff b hmb]
    simp only [hz, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    have hk : ∀ k : Fin m, ∑ i : Fin m, (if b k ≤ i.val then (1 : ℝ) else 0) = (m : ℝ) - b k := by
      intro k
      rw [← count_Ico m (b k) m (hb k) le_rfl]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [i.isLt]
    simp only [hk, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hC]
  unfold PhiS
  have key : ∑ i : Fin m,
      ((a i : ℝ) * gAt g i (a i) - a i + (b i : ℝ) * gAt g i (b i) - b i +
        ((m : ℝ) - zc b i) * gAt g i (a i) + ((m : ℝ) - zc a i) * gAt g i (b i)) =
      ∑ i : Fin m, ((((a i : ℝ) + m - zc b i) * gAt g i (a i) +
        (((b i : ℝ) + m - zc a i) * gAt g i (b i)))) - ∑ i : Fin m, ((a i : ℝ) + b i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [key, Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith [hR, hcount]

theorem zc_eq_of {m : ℕ} (c : Fin m → ℕ) (hc : Monotone c) (q : Fin m) (z : ℕ) (hz : z ≤ m)
    (h : ∀ k : Fin m, k.val < z ↔ c k ≤ q.val) : zc c q = z := by
  have h1 := zc_le c q
  rcases lt_trichotomy (zc c q) z with hlt | heq | hgt
  · have := (h ⟨zc c q, by omega⟩).mp hlt
    have := (lt_zc_iff c hc q ⟨zc c q, by omega⟩).mpr this
    simp at this
  · exact heq
  · have := (lt_zc_iff c hc q ⟨z, by omega⟩).mp hgt
    have := (h ⟨z, by omega⟩).mpr this
    simp at this

theorem g_anti_first {m : ℕ} (F : Fin m → Fin m → ℝ) (hF : InA F) (j j' q : Fin m) (h : j ≤ j') :
    priceReflect F j' q ≤ priceReflect F j q := by
  unfold priceReflect
  exact hF.2.2.2 _ (Fin.rev_le_rev.mpr h)

theorem phi_one_step {m : ℕ} (F : Fin m → Fin m → ℝ) (hF : InA F) (a b : Fin m → ℕ)
    (ha : ∀ i, a i ≤ m) (hb : ∀ i, b i ≤ m) (hma : Monotone a) (hmb : Monotone b)
    (i : Fin m) (hi : zc b i < a i) :
    ∃ a'' : Fin m → ℕ, (∀ j, a'' j ≤ m) ∧ Monotone a'' ∧ (∀ j, a'' j ≤ a j) ∧
      (∃ j, a'' j < a j) ∧
      PhiS (priceReflect F) a'' b ≤ PhiS (priceReflect F) a b := by
  set g := priceReflect F
  set s := a i with hs
  have hs1 : 1 ≤ s := by omega
  have hsm : s ≤ m := ha i
  obtain ⟨i0, hi0m, hi0min⟩ := (Finset.univ.filter (fun j => a j = s)).exists_min_image
    (fun j : Fin m => j) ⟨i, by simp [hs]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi0m hi0min
  have hi0i : i0 ≤ i := hi0min i rfl
  have hlt : ∀ j, j < i0 → a j < s := by
    intro j hj
    have h1 : a j ≤ s := hi0m ▸ hma hj.le
    rcases h1.lt_or_eq with h | h
    · exact h
    · exact absurd (hi0min j h) (not_le.mpr hj)
  have hge : ∀ j, i0 ≤ j → s ≤ a j := fun j hj => hi0m ▸ hma hj
  set a'' := Function.update a i0 (s - 1) with ha''
  have hval : ∀ j, a'' j = if j = i0 then s - 1 else a j := by
    intro j; simp only [ha'', Function.update_apply]
  have hle : ∀ j, a'' j ≤ a j := by
    intro j; rw [hval]; split_ifs with h
    · subst h; omega
    · exact le_rfl
  have hmono : Monotone a'' := by
    intro j j' hjj
    rw [hval, hval]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · have := hge j' (h1 ▸ hjj); omega
    · have : j < i0 := lt_of_le_of_ne (h2 ▸ hjj) h1
      have := hlt j this; omega
    · exact hma hjj
  set q0 : Fin m := ⟨s - 1, by omega⟩
  -- zc computations
  have hzq : ∀ q : Fin m, q ≠ q0 → zc a'' q = zc a q := by
    intro q hq
    rw [zc_eq_of a'' hmono q (zc a q) (zc_le a q)]
    intro k
    rw [lt_zc_iff a hma, hval]
    split_ifs with h
    · subst h
      have : q.val ≠ s - 1 := fun e => hq (Fin.ext e)
      rw [hi0m]; omega
    · exact Iff.rfl
  have hzq0 : zc a q0 = i0.val := by
    apply zc_eq_of a hma q0 _ (by omega)
    intro k
    constructor
    · intro hk; have := hlt k (Fin.lt_def.mpr hk); simp [q0]; omega
    · intro hk; by_contra hcon
      have := hge k (Fin.le_iff_val_le_val.mpr (by omega)); simp [q0] at hk; omega
  have hzq0'' : zc a'' q0 = i0.val + 1 := by
    apply zc_eq_of a'' hmono q0 _ (by omega)
    intro k
    rw [hval]
    constructor
    · intro hk
      split_ifs with h
      · simp [q0]
      · have : k < i0 := Fin.lt_def.mpr (by
          have : k.val ≠ i0.val := fun e => h (Fin.ext e)
          omega)
        have := hlt k this; simp [q0]; omega
    · intro hk
      split_ifs at hk with h
      · rw [h]; omega
      · by_contra hcon
        have := hge k (Fin.le_iff_val_le_val.mpr (by omega)); simp [q0] at hk; omega
  -- b at q0 exceeds i0
  have hbq0 : i0.val + 1 ≤ b q0 := by
    have h1 : zc b i0 ≤ zc b i := zc_mono b hi0i
    have h2 : ¬ (q0.val < zc b i0) := by simp [q0]; omega
    rw [lt_zc_iff b hmb] at h2
    omega
  -- the change of the objective
  set z := zc b i0
  have hzm : z ≤ m := zc_le b i0
  set D1 : ℝ := ((s - 1 : ℕ) : ℝ) * gAt g i0 (s - 1) - ((s - 1 : ℕ) : ℝ) +
      ((m : ℝ) - z) * gAt g i0 (s - 1) -
      ((s : ℝ) * gAt g i0 s - s + ((m : ℝ) - z) * gAt g i0 s)
  set D2 : ℝ := -gAt g q0 (b q0)
  have hpt : ∀ j : Fin m,
      ((a'' j : ℝ) * gAt g j (a'' j) - a'' j + (b j : ℝ) * gAt g j (b j) - b j +
        ((m : ℝ) - zc b j) * gAt g j (a'' j) + ((m : ℝ) - zc a'' j) * gAt g j (b j)) =
      ((a j : ℝ) * gAt g j (a j) - a j + (b j : ℝ) * gAt g j (b j) - b j +
        ((m : ℝ) - zc b j) * gAt g j (a j) + ((m : ℝ) - zc a j) * gAt g j (b j)) +
      ((if j = i0 then D1 else 0) + (if j = q0 then D2 else 0)) := by
    intro j
    have e1 : (if j = i0 then D1 else 0) = ((a'' j : ℝ) * gAt g j (a'' j) - a'' j +
        ((m : ℝ) - zc b j) * gAt g j (a'' j)) -
        ((a j : ℝ) * gAt g j (a j) - a j + ((m : ℝ) - zc b j) * gAt g j (a j)) := by
      rw [hval]
      split_ifs with h
      · subst h; rw [hi0m]
      · ring
    have e2 : (if j = q0 then D2 else 0) = ((m : ℝ) - zc a'' j) * gAt g j (b j) -
        ((m : ℝ) - zc a j) * gAt g j (b j) := by
      split_ifs with h
      · subst h; rw [hzq0, hzq0'']; push_cast; ring
      · rw [hzq j h]; ring
    rw [e1, e2]; ring
  have hdiff : PhiS g a'' b = PhiS g a b + (D1 + D2) := by
    unfold PhiS
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  -- D1 + D2 ≤ 0
  have hcomp : gAt g q0 (b q0) = 1 - g ⟨b q0 - 1, by have := hb q0; omega⟩ q0 := by
    unfold gAt
    rw [dif_pos ⟨by omega, hb q0⟩]
    have := hF.1 (Fin.rev q0) (Fin.rev ⟨b q0 - 1, by have := hb q0; omega⟩)
    simp only [g, priceReflect]; linarith
  have hg1 : g ⟨b q0 - 1, by have := hb q0; omega⟩ q0 ≤ gAt g i0 s := by
    have : gAt g i0 s = g i0 q0 := by
      have := gAt_succ g i0 q0; simp only [q0] at this ⊢
      rw [← this]; congr 1; omega
    rw [this]
    exact g_anti_first F hF _ _ _ (Fin.le_iff_val_le_val.mpr (by simp; omega))
  have hmon := gAt_mono F hF i0 (s - 1) s (by omega) hsm
  have hcast : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
    rw [Nat.cast_sub hs1]; simp
  have hzr : (z : ℝ) ≤ m := by exact_mod_cast hzm
  have hs1r : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hfin : D1 + D2 ≤ 0 := by
    simp only [D1, D2, hcast]
    rw [hcomp]
    have : 0 ≤ ((s : ℝ) - 1 + m - z) * (gAt g i0 s - gAt g i0 (s - 1)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  refine ⟨a'', fun j => (hle j).trans (ha j), hmono, hle, ⟨i0, ?_⟩, by rw [hdiff]; linarith⟩
  rw [hval, if_pos rfl, hi0m]; omega

theorem phi_step {m : ℕ} (F : Fin m → Fin m → ℝ) (hF : InA F) (a b : Fin m → ℕ)
    (ha : ∀ i, a i ≤ m) (hb : ∀ i, b i ≤ m) (hma : Monotone a) (hmb : Monotone b) :
    ∃ a' : Fin m → ℕ, (∀ i, a' i ≤ m) ∧ Monotone a' ∧ (∀ i, a' i ≤ zc b i) ∧
      PhiS (priceReflect F) a' b ≤ PhiS (priceReflect F) a b := by
  suffices H : ∀ n, ∀ a : Fin m → ℕ, ∑ i, a i = n → (∀ i, a i ≤ m) → Monotone a →
      ∃ a' : Fin m → ℕ, (∀ i, a' i ≤ m) ∧ Monotone a' ∧ (∀ i, a' i ≤ zc b i) ∧
        PhiS (priceReflect F) a' b ≤ PhiS (priceReflect F) a b from H _ a rfl ha hma
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a hn ha hma
    by_cases hov : ∀ i, a i ≤ zc b i
    · exact ⟨a, ha, hma, hov, le_rfl⟩
    · push_neg at hov
      obtain ⟨i, hi⟩ := hov
      obtain ⟨a'', ha'', hma'', hle, ⟨j, hj⟩, hP⟩ := phi_one_step F hF a b ha hb hma hmb i hi
      have hsum : ∑ i, a'' i < n := hn ▸ Finset.sum_lt_sum (fun i _ => hle i) ⟨j, by simp, hj⟩
      obtain ⟨a', h1, h2, h3, h4⟩ := ih _ hsum a'' rfl ha'' hma''
      exact ⟨a', h1, h2, h3, h4.trans hP⟩

/-- First occupied row of column `p` of the canonical table of passive rank `r`. -/
def sfirst {m : ℕ} (a b : Fin m → ℕ) (r p : Fin m) : ℕ :=
  m - sel (a (Fin.rev r)) (zc b (Fin.rev r)) (Fin.rev p).val

def ind {m : ℕ} (s : ℕ) (ℓ : Fin m) : ℝ := if s ≤ ℓ.val then 1 else 0

theorem sum_first {m : ℕ} (s : ℕ) (ℓ : Fin m) :
    ∑ h : Fin m, (if h ≤ ℓ then (if h.val = s then (1 : ℝ) else 0) else 0) = ind s ℓ := by
  unfold ind
  by_cases hs : s < m
  · have e : ∀ h : Fin m, (if h ≤ ℓ then (if h.val = s then (1 : ℝ) else 0) else 0) =
        if (⟨s, hs⟩ : Fin m) = h then (if s ≤ ℓ.val then 1 else 0) else 0 := by
      intro h
      by_cases h1 : h.val = s
      · have : (⟨s, hs⟩ : Fin m) = h := Fin.ext h1.symm
        rw [if_pos this]; subst this
        by_cases h2 : (⟨s, hs⟩ : Fin m) ≤ ℓ
        · rw [if_pos h2, if_pos rfl, if_pos (Fin.le_iff_val_le_val.mp h2)]
        · rw [if_neg h2, if_neg (fun h3 => h2 (Fin.le_iff_val_le_val.mpr h3))]
      · have hne : ¬ (⟨s, hs⟩ : Fin m) = h := fun e => h1 (by rw [← e])
        rw [if_neg hne, if_neg h1]; split_ifs <;> rfl
    rw [Finset.sum_congr rfl fun h _ => e h, Finset.sum_ite_eq]; simp
  · rw [if_neg (by omega)]
    refine Finset.sum_eq_zero fun h _ => ?_
    rw [if_neg (by omega : h.val ≠ s)]; simp

theorem ind_le {m : ℕ} (s s' : ℕ) (ℓ ℓ' : Fin m) (h : s ≤ ℓ.val → s' ≤ ℓ'.val) :
    ind s ℓ ≤ ind s' ℓ' := by
  unfold ind; split_ifs with h1 h2 <;> first | exact absurd (h h1) h2 | norm_num

theorem ind_nonneg {m : ℕ} (s : ℕ) (ℓ : Fin m) : 0 ≤ ind s ℓ := by
  unfold ind; split_ifs <;> norm_num

theorem sel_succ (x z k : ℕ) : sel x z (k + 1) ≤ sel x z k + 1 := by
  unfold sel; split_ifs <;> omega

theorem le_sel_iff (x z k t : ℕ) (h : k + 1 < t) : t ≤ sel x z k ↔ t ≤ x := by
  unfold sel; split_ifs <;> omega

theorem cross {m : ℕ} (a b : Fin m → ℕ) (hb : ∀ i, b i ≤ m) (r ℓ p : Fin m) :
    sfirst a b r ℓ ≤ ℓ.val ∨ sfirst b a ℓ p ≤ r.val := by
  unfold sfirst
  by_cases h : (Fin.rev ℓ).val + 1 ≤ sel (a (Fin.rev r)) (zc b (Fin.rev r)) (Fin.rev ℓ).val
  · left; simp only [Fin.val_rev] at h ⊢; omega
  · right
    have h1 : ¬ (Fin.rev ℓ).val + 1 ≤ zc b (Fin.rev r) := by
      intro h2; apply h; unfold sel; rw [if_pos h2]; omega
    have h2 : ¬ b (Fin.rev ℓ) ≤ (Fin.rev r).val := by
      intro h3; apply h1
      exact Finset.le_sup (f := fun j : Fin m => j.val + 1) (by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h3)
    have h3 := x_le_sel (b (Fin.rev ℓ)) (zc a (Fin.rev ℓ)) (Fin.rev p).val
    simp only [Fin.val_rev] at h2 h3 ⊢
    omega

theorem construct {m : ℕ} (hm : 1 ≤ m) (F : Fin m → Fin m → ℝ) (a b : Fin m → ℕ)
    (ha : ∀ i, a i ≤ m) (hb : ∀ i, b i ≤ m) :
    ∃ x : Fin m → Fin m → Fin m → ℝ, InC x ∧
      (m : ℝ) ^ 2 * pricedObjective F x = Ccost (priceReflect F) a b := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set c : ℝ := 1 / (2 * m) with hc
  have hc0 : 0 < c := by positivity
  set x : Fin m → Fin m → Fin m → ℝ := fun ℓ r p =>
    c * ((if ℓ.val = sfirst a b r p then 1 else 0) + (if ℓ.val = sfirst b a r p then 1 else 0))
  have hY : ∀ ℓ r p, cumY x ℓ r p = c * (ind (sfirst a b r p) ℓ + ind (sfirst b a r p) ℓ) := by
    intro ℓ r p
    unfold cumY
    rw [← sum_first, ← sum_first, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [x]; split_ifs <;> ring
  -- monotonicity in `p` of the first rows
  have hsucc : ∀ (a b : Fin m → ℕ), (∀ i, a i ≤ m) → ∀ (r p : Fin m) (hp : p.val + 1 < m),
      sfirst a b r ⟨p.val + 1, hp⟩ ≤ sfirst a b r p + 1 := by
    intro a b ha r p hp
    unfold sfirst
    have h1 := sel_succ (a (Fin.rev r)) (zc b (Fin.rev r)) (Fin.rev (⟨p.val + 1, hp⟩ : Fin m)).val
    have h2 : (Fin.rev (⟨p.val + 1, hp⟩ : Fin m)).val + 1 = (Fin.rev p).val := by
      simp [Fin.val_rev]; omega
    rw [h2] at h1
    have h3 := sel_le (a (Fin.rev r)) (zc b (Fin.rev r)) (Fin.rev p).val (ha _) (Fin.rev p).isLt
    omega
  have hupper : ∀ (a b : Fin m → ℕ), (∀ i, a i ≤ m) → ∀ (r ℓ p : Fin m), ℓ < p →
      (sfirst a b r p ≤ ℓ.val ↔ m - ℓ.val ≤ a (Fin.rev r)) := by
    intro a b ha r ℓ p hlp
    unfold sfirst
    have := le_sel_iff (a (Fin.rev r)) (zc b (Fin.rev r)) (Fin.rev p).val (m - ℓ.val)
      (by simp [Fin.val_rev]; have := Fin.lt_def.mp hlp; omega)
    have h3 := sel_le (a (Fin.rev r)) (zc b (Fin.rev r)) (Fin.rev p).val (ha _) (Fin.rev p).isLt
    constructor
    · intro h; apply this.mp; have := ℓ.isLt; omega
    · intro h; have := this.mpr h; omega
  have hor : ∀ (s s' : ℕ) (ℓ ℓ' : Fin m), s ≤ ℓ.val ∨ s' ≤ ℓ'.val → 1 ≤ ind s ℓ + ind s' ℓ' := by
    intro s s' ℓ ℓ' h
    have := ind_nonneg s ℓ; have := ind_nonneg s' ℓ'
    rcases h with h | h
    · have : ind s ℓ = 1 := by unfold ind; rw [if_pos h]
      linarith
    · have : ind s' ℓ' = 1 := by unfold ind; rw [if_pos h]
      linarith
  refine ⟨x, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro ℓ r p
    exact mul_nonneg hc0.le (by split_ifs <;> norm_num)
  · intro ℓ r p
    rw [hY, hY]
    have h1 := hor _ _ _ _ (cross a b hb r ℓ p)
    have h2 := hor _ _ _ _ (cross b a ha r ℓ p)
    have : 1 / (m : ℝ) = c * 2 := by rw [hc]; field_simp
    rw [this]
    nlinarith
  · intro ℓ r p hℓ hp
    rw [hY, hY]
    refine mul_le_mul_of_nonneg_left (add_le_add (ind_le _ _ _ _ ?_) (ind_le _ _ _ _ ?_)) hc0.le
    · intro h; have := hsucc a b ha r p (by omega); simp only at this ⊢; omega
    · intro h; have := hsucc b a hb r p (by omega); simp only at this ⊢; omega
  · intro ℓ r p hℓ hlp
    rw [hY, hY]
    have hl1 : ℓ < (⟨ℓ.val + 1, hℓ⟩ : Fin m) := Fin.lt_def.mpr (by simp)
    unfold ind
    simp only [hupper a b ha r ℓ p hlp, hupper a b ha r ℓ _ hl1, hupper b a hb r ℓ p hlp,
      hupper b a hb r ℓ _ hl1]
  · intro ℓ r p hℓ hpl
    rw [hY, hY]
    have hl1 : ℓ < (⟨ℓ.val + 1, hℓ⟩ : Fin m) := Fin.lt_def.mpr (by simp)
    refine mul_le_mul_of_nonneg_left (add_le_add (ind_le _ _ _ _ ?_) (ind_le _ _ _ _ ?_)) hc0.le
    · intro h
      have h1 := (hupper a b ha r ℓ _ hl1).mp h
      have h2 := x_le_sel (a (Fin.rev r)) (zc b (Fin.rev r)) (Fin.rev p).val
      simp only [sfirst]; omega
    · intro h
      have h1 := (hupper b a hb r ℓ _ hl1).mp h
      have h2 := x_le_sel (b (Fin.rev r)) (zc a (Fin.rev r)) (Fin.rev p).val
      simp only [sfirst]; omega
  · have hpick : ∀ (r : Fin m) (s : ℕ),
        ∑ ℓ : Fin m, F ℓ r * (if ℓ.val = s then (1 : ℝ) else 0) = Fext F r s := by
      intro r s
      unfold Fext
      split_ifs with hs
      · rw [Finset.sum_eq_single (⟨s, hs⟩ : Fin m)]
        · simp
        · intro ℓ _ hne; rw [if_neg (fun e => hne (Fin.ext e))]; ring
        · simp
      · refine Finset.sum_eq_zero fun ℓ _ => ?_
        rw [if_neg (by omega)]; ring
    have hobj : ∑ ℓ, ∑ r, ∑ p, F ℓ r * x ℓ r p =
        c * ∑ r, ∑ p, (Fext F r (sfirst a b r p) + Fext F r (sfirst b a r p)) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← hpick, ← hpick, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      simp only [x]; ring
    have hC : Ccost (priceReflect F) a b =
        ∑ r, ∑ p, (Fext F r (sfirst a b r p) + Fext F r (sfirst b a r p)) := by
      unfold Ccost
      rw [← Equiv.sum_comp Fin.revPerm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Equiv.sum_comp Fin.revPerm]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [Fin.revPerm_apply]
      rw [gAt_reflect F _ _ (sel_le _ _ _ (ha _) (Fin.rev p).isLt),
        gAt_reflect F _ _ (sel_le _ _ _ (hb _) (Fin.rev p).isLt), Fin.rev_rev]
      rfl
    unfold pricedObjective
    rw [hobj, hC, hc]
    field_simp

theorem full_suffix {m : ℕ} (P : Fin m → Prop) (hP : ∀ ℓ ℓ' : Fin m, ℓ ≤ ℓ' → P ℓ → P ℓ')
    (ℓ : Fin m) : m - (Finset.univ.filter P).card ≤ ℓ.val ↔ P ℓ := by
  constructor
  · intro h
    by_contra hn
    have hsub : Finset.univ.filter P ⊆ Finset.Ioi ℓ := by
      intro ℓ' h'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h'
      simp only [Finset.mem_Ioi]
      by_contra hle; push_neg at hle
      exact hn (hP _ _ hle h')
    have := Finset.card_le_card hsub
    rw [Fin.card_Ioi] at this
    omega
  · intro h
    have hsub : Finset.Ici ℓ ⊆ Finset.univ.filter P := by
      intro ℓ' h'
      simp only [Finset.mem_Ici] at h'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hP _ _ h' h
    have := Finset.card_le_card hsub
    rw [Fin.card_Ici] at this
    omega

theorem cone {m : ℕ} (A : Fin m → Fin m → Fin m → Prop)
    (hmA : ∀ (ℓ ℓ' r p : Fin m), ℓ ≤ ℓ' → A ℓ r p → A ℓ' r p)
    (h51A : ∀ (ℓ r p : Fin m) (hℓ : ℓ.val + 1 < m) (hp : p.val ≤ ℓ.val),
      A ℓ r p → A ⟨ℓ.val + 1, hℓ⟩ r ⟨p.val + 1, by omega⟩)
    (ℓ0 r : Fin m) (h0 : A ℓ0 r ℓ0) (ℓ p : Fin m) (h1 : ℓ0 ≤ p) (h2 : p ≤ ℓ) : A ℓ r p := by
  have hd : ∀ d : ℕ, ∀ hd : ℓ0.val + d < m, A ⟨ℓ0.val + d, hd⟩ r ⟨ℓ0.val + d, hd⟩ := by
    intro d
    induction d with
    | zero => intro hd; simpa using h0
    | succ d ih =>
      intro hd
      have := h51A ⟨ℓ0.val + d, by omega⟩ r ⟨ℓ0.val + d, by omega⟩ (by simp; omega) le_rfl
        (ih (by omega))
      simpa [Nat.add_assoc] using this
  have hp := hd (p.val - ℓ0.val) (by have := Fin.le_def.mp h1; omega)
  have e : (⟨ℓ0.val + (p.val - ℓ0.val), by omega⟩ : Fin m) = p := by
    ext; simp; have := Fin.le_def.mp h1; omega
  rw [e] at hp
  exact hmA _ _ _ _ h2 hp

theorem half_lower {m : ℕ} (F : Fin m → Fin m → ℝ) (hF : InA F)
    (A B : Fin m → Fin m → Fin m → Prop)
    (hmA : ∀ (ℓ ℓ' r p : Fin m), ℓ ≤ ℓ' → A ℓ r p → A ℓ' r p)
    (hmB : ∀ (ℓ ℓ' r p : Fin m), ℓ ≤ ℓ' → B ℓ r p → B ℓ' r p)
    (h51A : ∀ (ℓ r p : Fin m) (hℓ : ℓ.val + 1 < m) (hp : p.val ≤ ℓ.val),
      A ℓ r p → A ⟨ℓ.val + 1, hℓ⟩ r ⟨p.val + 1, by omega⟩)
    (hAB : ∀ ℓ r p, A ℓ r ℓ ∨ B r ℓ p) :
    ∑ i : Fin m, ∑ k : Fin m, gAt (priceReflect F) i (sel (nfull A i) (zc (nfull B) i) k.val) ≤
      ∑ ℓ, ∑ r, ∑ p, cc F ℓ r * (if A ℓ r p then 1 else 0) := by
  have hnA : ∀ i, nfull A i ≤ m := fun i => (Finset.card_le_univ _).trans (by simp)
  -- key claim
  have key : ∀ r p ℓ : Fin m,
      m - sel (nfull A (Fin.rev r)) (zc (nfull B) (Fin.rev r)) (Fin.rev p).val ≤ ℓ.val →
        A ℓ r p := by
    intro r p ℓ h
    have hn : nfull A (Fin.rev r) = (Finset.univ.filter (fun ℓ => ∀ p', A ℓ r p')).card := by
      simp [nfull]
    have hsA : ∀ ℓ : Fin m, m - nfull A (Fin.rev r) ≤ ℓ.val ↔ ∀ p', A ℓ r p' := by
      intro ℓ
      rw [hn]
      convert full_suffix (fun ℓ => ∀ p', A ℓ r p') (fun ℓ ℓ' hl h p' => hmA _ _ _ _ hl (h p')) ℓ
    unfold sel at h
    split_ifs at h with hz
    · rcases le_total (nfull A (Fin.rev r)) ((Fin.rev p).val + 1) with hx | hx
      · rw [max_eq_right hx] at h
        have hne : (Finset.univ.filter (fun j : Fin m => nfull B j ≤ (Fin.rev r).val)).Nonempty := by
          by_contra hemp
          rw [Finset.not_nonempty_iff_eq_empty] at hemp
          simp only [zc, hemp, Finset.sup_empty, Nat.bot_eq_zero] at hz
          omega
        obtain ⟨j, hj, hjz⟩ := Finset.exists_mem_eq_sup _ hne (fun j : Fin m => j.val + 1)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [← zc] at hjz
        have hnf : ¬ ∀ p', B r (Fin.rev j) p' := by
          intro hfull
          have : m - nfull B j ≤ r.val := by
            unfold nfull
            convert (full_suffix (fun ℓ => ∀ p', B ℓ (Fin.rev j) p')
              (fun ℓ ℓ' hl h p' => hmB _ _ _ _ hl (h p')) r).mpr hfull
          simp only [Fin.val_rev] at hj
          have := r.isLt
          omega
        push_neg at hnf
        obtain ⟨p', hp'⟩ := hnf
        have hdiag : A (Fin.rev j) r (Fin.rev j) := (hAB (Fin.rev j) r p').resolve_right hp'
        apply cone A hmA h51A (Fin.rev j) r hdiag ℓ p
        · rw [Fin.le_def]; simp only [Fin.val_rev]
          have : (Fin.rev p).val + 1 ≤ j.val + 1 := hjz ▸ hz
          simp only [Fin.val_rev] at this; omega
        · rw [Fin.le_def]; simp only [Fin.val_rev] at h; omega
      · rw [max_eq_left hx] at h
        exact (hsA ℓ).mp h p
    · exact (hsA ℓ).mp h p
  have hL : ∑ i : Fin m, ∑ k : Fin m,
      gAt (priceReflect F) i (sel (nfull A i) (zc (nfull B) i) k.val) =
      ∑ r : Fin m, ∑ p : Fin m, gAt (priceReflect F) (Fin.rev r)
        (sel (nfull A (Fin.rev r)) (zc (nfull B) (Fin.rev r)) (Fin.rev p).val) := by
    rw [← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Equiv.sum_comp Fin.revPerm]
    rfl
  have hR : ∑ ℓ, ∑ r, ∑ p, cc F ℓ r * (if A ℓ r p then (1 : ℝ) else 0) =
      ∑ r, ∑ p, ∑ ℓ, cc F ℓ r * (if A ℓ r p then (1 : ℝ) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
  rw [hL, hR]
  refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun p _ => ?_
  rw [gAt_reflect F _ _ (sel_le _ _ _ (hnA _) (Fin.rev p).isLt), Fin.rev_rev,
    ← sum_cc_ge F r _ (by omega)]
  refine Finset.sum_le_sum fun ℓ _ => ?_
  split_ifs with h1 h2
  · simp
  · exact absurd (key r p ℓ h1) h2
  · simp [cc_nonneg F hF]
  · simp

theorem cover_lower {m : ℕ} (F : Fin m → Fin m → ℝ) (hF : InA F)
    (A B : Fin m → Fin m → Fin m → Prop)
    (hmA : ∀ (ℓ ℓ' r p : Fin m), ℓ ≤ ℓ' → A ℓ r p → A ℓ' r p)
    (hmB : ∀ (ℓ ℓ' r p : Fin m), ℓ ≤ ℓ' → B ℓ r p → B ℓ' r p)
    (h51A : ∀ (ℓ r p : Fin m) (hℓ : ℓ.val + 1 < m) (hp : p.val ≤ ℓ.val),
      A ℓ r p → A ⟨ℓ.val + 1, hℓ⟩ r ⟨p.val + 1, by omega⟩)
    (h51B : ∀ (ℓ r p : Fin m) (hℓ : ℓ.val + 1 < m) (hp : p.val ≤ ℓ.val),
      B ℓ r p → B ⟨ℓ.val + 1, hℓ⟩ r ⟨p.val + 1, by omega⟩)
    (hAB : ∀ ℓ r p, A ℓ r ℓ ∨ B r ℓ p) (hBA : ∀ ℓ r p, B ℓ r ℓ ∨ A r ℓ p) :
    Ccost (priceReflect F) (nfull A) (nfull B) ≤
      ∑ ℓ, ∑ r, ∑ p, cc F ℓ r * ((if A ℓ r p then 1 else 0) + (if B ℓ r p then 1 else 0)) := by
  have h1 := half_lower F hF A B hmA hmB h51A hAB
  have h2 := half_lower F hF B A hmB hmA h51B hBA
  have e : ∑ ℓ, ∑ r, ∑ p, cc F ℓ r * ((if A ℓ r p then (1 : ℝ) else 0) + (if B ℓ r p then 1 else 0)) =
      ∑ ℓ, ∑ r, ∑ p, cc F ℓ r * (if A ℓ r p then 1 else 0) +
        ∑ ℓ, ∑ r, ∑ p, cc F ℓ r * (if B ℓ r p then 1 else 0) := by
    simp only [mul_add, Finset.sum_add_distrib]
  rw [e]
  unfold Ccost
  simp only [Finset.sum_add_distrib]
  linarith

/-! ## Lower bound for 0/1 covers -/


/-! ## Reduction of `Ccost` to overlap-free monotone pairs -/





/-! ## Construction of a point of `C_m` -/


theorem integral_le_ind (c : ℝ) (hc : 0 ≤ c) :
    ∫ θ in (0 : ℝ)..1, (if θ ≤ c then (1 : ℝ) else 0) = min c 1 := by
  have hmem : min c 1 ∈ Set.Icc (0 : ℝ) 1 := ⟨le_min hc zero_le_one, min_le_right _ _⟩
  rw [intervalIntegral.integral_congr (g := Set.indicator {x | x ≤ min c 1} (fun _ => (1 : ℝ)))]
  · rw [intervalIntegral.integral_indicator hmem]; simp
  · intro θ hθ
    rw [Set.uIcc_of_le zero_le_one] at hθ
    simp only [Set.indicator, Set.mem_ofPred_eq, le_min_iff, hθ.2, and_true]

theorem integral_ge_ind (c : ℝ) (hc : 0 ≤ c) :
    ∫ θ in (0 : ℝ)..1, (if 1 - θ ≤ c then (1 : ℝ) else 0) = min c 1 := by
  have := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1)
    (fun t : ℝ => if t ≤ c then (1 : ℝ) else 0) 1
  simp only [sub_self, sub_zero] at this
  rw [this, integral_le_ind c hc]

theorem ii_le (c : ℝ) :
    IntervalIntegrable (fun θ : ℝ => if θ ≤ c then (1 : ℝ) else 0) MeasureTheory.volume 0 1 := by
  apply Antitone.intervalIntegrable
  intro x y hxy
  simp only
  split_ifs <;> first | (exfalso; linarith) | norm_num

theorem ii_ge (c : ℝ) :
    IntervalIntegrable (fun θ : ℝ => if 1 - θ ≤ c then (1 : ℝ) else 0) MeasureTheory.volume 0 1 := by
  apply Monotone.intervalIntegrable
  intro x y hxy
  simp only
  split_ifs <;> first | (exfalso; linarith) | norm_num

theorem layer {ι : Type*} [Fintype ι] (w u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hu : ∀ i, 0 ≤ u i)
    (K : ℝ)
    (h : ∀ θ ∈ Set.Icc (0 : ℝ) 1, K ≤ ∑ i, w i *
      ((if θ ≤ u i then 1 else 0) + (if 1 - θ ≤ u i then 1 else 0))) :
    K ≤ ∑ i, w i * (2 * u i) := by
  have hf : ∀ i, IntervalIntegrable (fun θ : ℝ => w i *
      ((if θ ≤ u i then (1 : ℝ) else 0) + (if 1 - θ ≤ u i then 1 else 0)))
      MeasureTheory.volume 0 1 := fun i => ((ii_le (u i)).add (ii_ge (u i))).const_mul (w i)
  have hG : IntervalIntegrable (fun θ : ℝ => ∑ i, w i *
      ((if θ ≤ u i then (1 : ℝ) else 0) + (if 1 - θ ≤ u i then 1 else 0)))
      MeasureTheory.volume 0 1 := by
    have := IntervalIntegrable.sum Finset.univ (fun i _ => hf i)
    rw [Finset.sum_fn] at this
    exact this
  have hmono := intervalIntegral.integral_mono_on zero_le_one
    (intervalIntegrable_const (c := K)) hG h
  rw [intervalIntegral.integral_const, intervalIntegral.integral_finsetSum (fun i _ => hf i)]
    at hmono
  simp only [sub_zero, one_smul] at hmono
  refine hmono.trans (Finset.sum_le_sum fun i _ => ?_)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (ii_le _) (ii_ge _),
    integral_le_ind _ (hu i), integral_ge_ind _ (hu i)]
  have := min_le_left (u i) 1
  have := hw i
  nlinarith

theorem lower_bound {m : ℕ} (hm : 1 ≤ m) (F : Fin m → Fin m → ℝ) (hF : InA F) (K : ℝ)
    (hK : ∀ a b : Fin m → ℕ, (∀ i, a i ≤ m) → (∀ i, b i ≤ m) →
      (m : ℝ) ^ 2 * K ≤ Ccost (priceReflect F) a b)
    (x : Fin m → Fin m → Fin m → ℝ) (hx : InC x) :
    K ≤ pricedObjective F x := by
  obtain ⟨hx0, h50, h51, -, -⟩ := hx
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set u : Fin m → Fin m → Fin m → ℝ := fun ℓ r p => (m : ℝ) * cumY x ℓ r p
  have hy0 : ∀ ℓ r p, 0 ≤ cumY x ℓ r p := fun ℓ r p =>
    Finset.sum_nonneg fun h _ => by split_ifs <;> first | exact hx0 _ _ _ | exact le_rfl
  have hu0 : ∀ ℓ r p, 0 ≤ u ℓ r p := fun ℓ r p => mul_nonneg hm0.le (hy0 ℓ r p)
  have hymono : ∀ ℓ ℓ' r p : Fin m, ℓ ≤ ℓ' → u ℓ r p ≤ u ℓ' r p := by
    intro ℓ ℓ' r p hl
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ => ?_) hm0.le
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (h1.trans hl) h2
    · exact hx0 _ _ _
    · exact le_rfl
  have hfull : ∀ (A : Fin m → Fin m → Fin m → Prop) (i : Fin m), nfull A i ≤ m :=
    fun A i => (Finset.card_le_univ _).trans (by simp)
  have hcov : ∀ θ ∈ Set.Icc (0 : ℝ) 1, (m : ℝ) ^ 2 * K ≤
      ∑ ℓ, ∑ r, ∑ p, cc F ℓ r *
        ((if θ ≤ u ℓ r p then 1 else 0) + (if 1 - θ ≤ u ℓ r p then 1 else 0)) := by
    intro θ hθ
    refine (hK _ _ (hfull _) (hfull _)).trans
      (cover_lower F hF (fun ℓ r p => θ ≤ u ℓ r p) (fun ℓ r p => 1 - θ ≤ u ℓ r p) ?_ ?_ ?_ ?_ ?_ ?_)
    · intro ℓ ℓ' r p hl h; exact h.trans (hymono ℓ ℓ' r p hl)
    · intro ℓ ℓ' r p hl h; exact h.trans (hymono ℓ ℓ' r p hl)
    · intro ℓ r p hℓ hp h
      exact h.trans (mul_le_mul_of_nonneg_left (h51 ℓ r p hℓ hp) hm0.le)
    · intro ℓ r p hℓ hp h
      exact h.trans (mul_le_mul_of_nonneg_left (h51 ℓ r p hℓ hp) hm0.le)
    · intro ℓ r p
      have h1 := h50 ℓ r p
      have h2 : 1 ≤ u ℓ r ℓ + u r ℓ p := by
        simp only [u]; rw [← mul_add]
        have := mul_le_mul_of_nonneg_left h1 hm0.le
        rwa [mul_one_div_cancel hm0.ne'] at this
      by_cases h3 : θ ≤ u ℓ r ℓ
      · exact Or.inl h3
      · right; linarith
    · intro ℓ r p
      have h1 := h50 ℓ r p
      have h2 : 1 ≤ u ℓ r ℓ + u r ℓ p := by
        simp only [u]; rw [← mul_add]
        have := mul_le_mul_of_nonneg_left h1 hm0.le
        rwa [mul_one_div_cancel hm0.ne'] at this
      by_cases h3 : 1 - θ ≤ u ℓ r ℓ
      · exact Or.inl h3
      · right; linarith
  have hL := layer (ι := Fin m × Fin m × Fin m) (fun q => cc F q.1 q.2.1)
    (fun q => u q.1 q.2.1 q.2.2) (fun q => cc_nonneg F hF _ _) (fun q => hu0 _ _ _)
    ((m : ℝ) ^ 2 * K) (by
      intro θ hθ
      simp only [Fintype.sum_prod_type]
      exact hcov θ hθ)
  simp only [Fintype.sum_prod_type] at hL
  have e1 : ∀ f : Fin m → Fin m → Fin m → ℝ,
      ∑ ℓ, ∑ r, ∑ p, f ℓ r p = ∑ r, ∑ p, ∑ ℓ, f ℓ r p := by
    intro f; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => by rw [Finset.sum_comm]
  have hS : ∑ ℓ, ∑ r, ∑ p, F ℓ r * x ℓ r p = ∑ ℓ, ∑ r, ∑ p, cc F ℓ r * cumY x ℓ r p := by
    calc ∑ ℓ, ∑ r, ∑ p, F ℓ r * x ℓ r p = ∑ r, ∑ p, ∑ ℓ, F ℓ r * x ℓ r p :=
          e1 (fun ℓ r p => F ℓ r * x ℓ r p)
      _ = ∑ r, ∑ p, ∑ ℓ, cc F ℓ r * cumY x ℓ r p :=
          Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun p _ => abel F x r p
      _ = _ := (e1 (fun ℓ r p => cc F ℓ r * cumY x ℓ r p)).symm
  have hL' : ∑ ℓ, ∑ r, ∑ p, cc F ℓ r * (2 * u ℓ r p) =
      2 * m * ∑ ℓ, ∑ r, ∑ p, cc F ℓ r * cumY x ℓ r p := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun r _ =>
      Finset.sum_congr rfl fun p _ => by simp only [u]; ring
  rw [hL'] at hL
  unfold pricedObjective
  rw [hS]
  set S := ∑ ℓ, ∑ r, ∑ p, cc F ℓ r * cumY x ℓ r p
  rw [div_mul_eq_mul_div, le_div_iff₀ hm0]
  nlinarith

/-! ## Layer-cake lower bound -/


/-! ## Paths as sequences -/



/-! ## Main theorem -/

theorem theorem_B_3_aux (m : ℕ) (hm : 1 ≤ m) (F : Fin m → Fin m → ℝ)
    (hF : InA F) :
    Rm F = twoPathMin (priceReflect F) := by
  set g := priceReflect F with hg
  have hmpos : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  apply le_antisymm
  · unfold twoPathMin
    refine le_iInf fun P => le_iInf fun hP => le_iInf fun Q => le_iInf fun hQ => ?_
    obtain ⟨haP, hmP, hPe⟩ := path_seq P hP
    obtain ⟨haQ, hmQ, hQe⟩ := path_seq Q hQ
    obtain ⟨a', ha', hma', hov, hle⟩ := phi_step F hF _ _ haP haQ hmP hmQ
    obtain ⟨x, hx, hxc⟩ := construct hm F a' _ ha' haQ
    have hid := identity F hF a' _ ha' haQ hma' hmQ hov
    have hPQ := PhiS_eq g hm _ _ haP haQ hmP hmQ
    rw [hPe, hQe] at hPQ
    have h1 : pricedObjective F x ≤ Phi g P Q := by
      have : (m : ℝ) ^ 2 * pricedObjective F x ≤ (m : ℝ) ^ 2 * Phi g P Q := by
        rw [hxc, hid, ← hPQ]; exact hle
      exact le_of_mul_le_mul_left this hmpos
    exact (iInf₂_le x hx).trans (by exact_mod_cast h1)
  · -- a minimiser of `Φ` over pairs of paths
    obtain ⟨pq, hpqm, hpq⟩ := Finset.exists_min_image
      (Finset.univ.filter (fun pq : (Fin (m + 1) → Fin (m + 1)) × (Fin (m + 1) → Fin (m + 1)) =>
        IsPath pq.1 ∧ IsPath pq.2)) (fun pq => Phi g pq.1 pq.2)
      ⟨(fun _ => Fin.last m, fun _ => Fin.last m), Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ⟨monotone_const, rfl⟩, monotone_const, rfl⟩⟩
    have hmin : ∀ P Q, IsPath P → IsPath Q → Phi g pq.1 pq.2 ≤ Phi g P Q := fun P Q hP hQ =>
      hpq (P, Q) (by simp [hP, hQ])
    have hK : ∀ a b : Fin m → ℕ, (∀ i, a i ≤ m) → (∀ i, b i ≤ m) →
        (m : ℝ) ^ 2 * Phi g pq.1 pq.2 ≤ Ccost g a b := by
      intro a b ha hb
      obtain ⟨a', b', ha', hb', hma', hmb', hov, hle⟩ := reduce F hF a b ha hb
      have h1 := identity F hF a' b' ha' hb' hma' hmb' hov
      have h2 := PhiS_eq g hm a' b' ha' hb' hma' hmb'
      have h3 := hmin _ _ (toPath_isPath a' hma') (toPath_isPath b' hmb')
      calc (m : ℝ) ^ 2 * Phi g pq.1 pq.2 ≤ (m : ℝ) ^ 2 * Phi g (toPath a') (toPath b') := by
            gcongr
        _ = Ccost g a' b' := by rw [h1, h2]
        _ ≤ Ccost g a b := hle
    have hle : twoPathMin g ≤ ((Phi g pq.1 pq.2 : ℝ) : EReal) := by
      unfold twoPathMin
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpqm
      exact (iInf₂_le pq.1 hpqm.1).trans (iInf₂_le pq.2 hpqm.2)
    refine le_iInf fun x => le_iInf fun hx => ?_
    exact hle.trans (by exact_mod_cast lower_bound hm F hF _ hK x hx)

end

end HarmonicRanking.Main.Supplement

theorem solution (m : ℕ) (hm : 1 ≤ m) (F : Fin m → Fin m → ℝ)
    (hF : HarmonicRanking.Main.Supplement.InA F) :
    HarmonicRanking.Main.Supplement.Rm F =
      HarmonicRanking.Main.Supplement.twoPathMin (HarmonicRanking.Main.Supplement.priceReflect F) :=
  HarmonicRanking.Main.Supplement.theorem_B_3_aux m hm F hF
