-- Prove2me | solution 1 for GeomScoring.Characterization.proposition_4_losers
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:16:27.793148+00:00
-- url     : https://prove2.me/submissions/2a61aafe-d877-4aae-8c7d-f1970cf2d197

import Mathlib
import Definitions.Def_GeomScoring_Characterization_Model
open GeomScoring.Characterization

namespace GSP4

lemma aff_refl {k : ℕ} (u : Fin k → ℝ) : AffEquiv u u := ⟨1, 0, one_pos, fun j => by ring⟩

lemma aff_symm {k : ℕ} {u v : Fin k → ℝ} (h : AffEquiv u v) : AffEquiv v u := by
  obtain ⟨a, b, ha, h⟩ := h
  refine ⟨1 / a, -b / a, by positivity, fun j => ?_⟩
  rw [h j]; field_simp; ring

lemma aff_trans {k : ℕ} {u v w : Fin k → ℝ} (h1 : AffEquiv u v) (h2 : AffEquiv v w) :
    AffEquiv u w := by
  obtain ⟨a, b, ha, h1⟩ := h1
  obtain ⟨c, d, hc, h2⟩ := h2
  exact ⟨a * c, a * d + b, mul_pos ha hc, fun j => by rw [h1 j, h2 j]; ring⟩

lemma s_congr (s : ScoringRule) {N N' : ℕ} (i : Fin N) (j : Fin N') (h : N = N')
    (hv : i.val = j.val) : s N i = s N' j := by
  subst h; rw [Fin.ext hv]

lemma perm_exists {k : ℕ} (a b i j : Fin k) (hab : a ≠ b) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin k), σ a = i ∧ σ b = j := by
  set σ1 := Equiv.swap a i with hσ1
  have h1 : σ1 a = i := Equiv.swap_apply_left a i
  set c := σ1 b with hc
  have hci : c ≠ i := by rw [← h1]; exact σ1.injective.ne hab.symm
  refine ⟨σ1.trans (Equiv.swap c j), ?_, ?_⟩
  · simp only [Equiv.trans_apply]; rw [h1]; exact Equiv.swap_apply_of_ne_of_ne hci.symm hij
  · simp only [Equiv.trans_apply]; exact Equiv.swap_apply_left c j

/-- If two score vectors induce the same comparisons between two athletes in every profile,
they are affinely equivalent. -/
lemma core (k : ℕ) (u v : Fin k → ℝ)
    (H : ∀ (n : ℕ) (f g : Fin n → Fin k), 0 < n → (∀ r, f r ≠ g r) →
      ((∑ r, v (f r) ≤ ∑ r, v (g r)) ↔ (∑ r, u (f r) ≤ ∑ r, u (g r)))) :
    AffEquiv u v := by
  have H2 : ∀ (Q R : ℕ) (i1 j1 i2 j2 : Fin k), 0 < Q + R → i1 ≠ j1 → i2 ≠ j2 →
      ((Q:ℝ) * (v i1 - v j1) + R * (v i2 - v j2) ≤ 0 ↔
        (Q:ℝ) * (u i1 - u j1) + R * (u i2 - u j2) ≤ 0) := by
    intro Q R i1 j1 i2 j2 hQR h1 h2
    have := H (Q+R) (Fin.append (fun _ : Fin Q => i1) (fun _ : Fin R => i2))
      (Fin.append (fun _ : Fin Q => j1) (fun _ : Fin R => j2)) hQR (by
        intro r; refine Fin.addCases (fun r => ?_) (fun r => ?_) r <;> simp [h1, h2])
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    constructor
    · intro h; have := this.1 (by linarith); linarith
    · intro h; have := this.2 (by linarith); linarith
  by_cases hc : ∀ i j, v i ≤ v j
  · have hu : ∀ i j, u i ≤ u j := by
      intro i j
      by_cases hij : i = j
      · rw [hij]
      have := (H2 1 0 i j i j (by norm_num) hij hij).1 (by have := hc i j; simp; linarith)
      simp at this; linarith
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; exact ⟨1, 0, one_pos, fun j => j.elim0⟩
    refine ⟨1, u ⟨0, hk⟩ - v ⟨0, hk⟩, one_pos, fun j => ?_⟩
    have := hc j ⟨0,hk⟩; have := hc ⟨0,hk⟩ j; have := hu j ⟨0,hk⟩; have := hu ⟨0,hk⟩ j
    linarith
  push Not at hc
  obtain ⟨i0, j0, hlt⟩ := hc
  have hne : i0 ≠ j0 := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
  have hult : u j0 < u i0 := by
    by_contra hh; push Not at hh
    have := (H2 1 0 i0 j0 i0 j0 (by norm_num) hne hne).2 (by simp; linarith)
    simp at this; linarith
  set Dv := v i0 - v j0 with hDvdef
  set Du := u i0 - u j0 with hDudef
  have hDv : 0 < Dv := by linarith
  have hDu : 0 < Du := by linarith
  have HG : ∀ (Q : ℕ) (P : ℤ) (l : Fin k), 0 < Q → l ≠ j0 →
      ((Q:ℝ) * (v l - v j0) - P * Dv ≤ 0 ↔ (Q:ℝ) * (u l - u j0) - P * Du ≤ 0) := by
    intro Q P l hQ hl
    rcases le_or_gt 0 P with hP | hP
    · have := H2 Q P.toNat l j0 j0 i0 (by omega) hl hne.symm
      have e : ((P.toNat : ℕ) : ℝ) = (P : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hP
      rw [e] at this
      constructor <;> intro h
      · have := this.1 (by linarith); linarith
      · have := this.2 (by linarith); linarith
    · have := H2 Q (-P).toNat l j0 i0 j0 (by omega) hl hne
      have e : (((-P).toNat : ℕ) : ℝ) = -(P : ℝ) := by
        have := Int.toNat_of_nonneg (show 0 ≤ -P by omega); exact_mod_cast this
      rw [e] at this
      constructor <;> intro h
      · have := this.1 (by linarith); linarith
      · have := this.2 (by linarith); linarith
  refine ⟨Du / Dv, u j0 - Du / Dv * v j0, div_pos hDu hDv, fun l => ?_⟩
  by_cases hl : l = j0
  · subst hl; ring
  have key : (u l - u j0) / Du = (v l - v j0) / Dv := by
    by_contra hneq
    have hden : (0:ℝ) < (1:ℝ) := one_pos
    rcases lt_or_gt_of_ne hneq with h | h
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h
      have hd : (0:ℝ) < q.den := by exact_mod_cast q.pos
      rw [Rat.cast_def, div_lt_div_iff₀ hDu hd] at hq1
      rw [Rat.cast_def, div_lt_div_iff₀ hd hDv] at hq2
      have := (HG q.den q.num l q.pos hl).2 (by linarith)
      linarith
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h
      have hd : (0:ℝ) < q.den := by exact_mod_cast q.pos
      rw [Rat.cast_def, div_lt_div_iff₀ hDv hd] at hq1
      rw [Rat.cast_def, div_lt_div_iff₀ hd hDu] at hq2
      have := (HG q.den q.num l q.pos hl).1 (by linarith)
      linarith
  have h1 : u l - u j0 = (u l - u j0) / Du * Du := by field_simp
  rw [key] at h1
  have : Du / Dv * v l + (u j0 - Du / Dv * v j0) = u j0 + (v l - v j0) / Dv * Du := by ring
  linarith

end GSP4
namespace GSP4L

open GSP4

noncomputable def race {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    Option (Fin k) ≃ Fin (Fintype.card (Option (Fin k))) :=
  (Equiv.optionCongr σ).trans (finSuccEquivLast.symm.trans (finCongr (by simp)))

lemma race_some {k : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    ((race σ (some i) : Fin _) : ℕ) = (σ i : ℕ) := by
  simp [race]

lemma race_none {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    ((race σ none : Fin _) : ℕ) = k := by
  simp [race]

lemma card_ne_none (k : ℕ) : Fintype.card {a : Option (Fin k) // a ≠ none} = k := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]; simp

def eNone (k : ℕ) : {a : Option (Fin k) // a ≠ none} ≃ Fin k :=
  (Equiv.subtypeEquivRight (fun a => Option.ne_none_iff_isSome)).trans (Equiv.optionIsSomeEquiv _)

lemma eNone_some (k : ℕ) (i : Fin k) (h : (some i : Option (Fin k)) ≠ none) :
    eNone k ⟨some i, h⟩ = i := rfl

noncomputable def qrace {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    {a : Option (Fin k) // a ≠ none} ≃ Fin (Fintype.card {a : Option (Fin k) // a ≠ none}) :=
  (eNone k).trans (σ.trans (finCongr (card_ne_none k).symm))

lemma qrace_val {k : ℕ} (σ : Equiv.Perm (Fin k)) (a : {a : Option (Fin k) // a ≠ none}) :
    ((qrace σ a : Fin _) : ℕ) = (σ (eNone k a) : ℕ) := by
  simp [qrace]

lemma some_eNone {k : ℕ} (a : {a : Option (Fin k) // a ≠ none}) : a.1 = some (eNone k a) := by
  obtain ⟨a, ha⟩ := a
  cases a with
  | none => exact absurd rfl ha
  | some i => rfl

lemma last_lt (M : ℕ∞) (s : ScoringRule) (hL : IndepUnanimousLosers M s) (k : ℕ)
    (hk : ((k + 1 : ℕ) : ℕ∞) ≤ M) (j : Fin k) :
    s (k+1) (Fin.last k) < s (k+1) j.castSucc := by
  let P : Profile (Option (Fin k)) 1 := fun _ => race 1
  have hUL : IsUnanimousLoser P none := by
    intro i; simp only [P]; rw [race_none]; simp
  have ax := (hL (Option (Fin k)) (by simpa using hk) 1 one_pos P none hUL).1 (some j) (by simp)
  simp only [totalScore, Fin.sum_univ_one, P] at ax
  have e1 : s (Fintype.card (Option (Fin k))) (race 1 none) = s (k+1) (Fin.last k) :=
    s_congr s _ _ (by simp) (by rw [race_none]; simp)
  have e2 : s (Fintype.card (Option (Fin k))) (race 1 (some j)) = s (k+1) j.castSucc :=
    s_congr s _ _ (by simp) (by rw [race_some]; simp)
  rw [e1, e2] at ax
  exact ax

lemma step (M : ℕ∞) (s : ScoringRule) (hL : IndepUnanimousLosers M s) (k : ℕ)
    (hk : ((k + 1 : ℕ) : ℕ∞) ≤ M) : AffEquiv (s k) (initSeg (s (k+1)) k) := by
  apply core
  intro n f g hn hfg
  have h01 := hfg ⟨0, hn⟩
  have hk2 : 2 ≤ k := by
    have := Fin.val_ne_of_ne h01; have := (f ⟨0,hn⟩).2; have := (g ⟨0,hn⟩).2; omega
  let A : Fin k := ⟨0, by omega⟩
  let B : Fin k := ⟨1, by omega⟩
  have hAB : A ≠ B := by simp [A, B, Fin.ext_iff]
  choose σ hσ using fun r => perm_exists A B (f r) (g r) hAB (hfg r)
  let P : Profile (Option (Fin k)) n := fun r => race (σ r)
  have hUL : IsUnanimousLoser P none := by
    intro i; simp only [P]; rw [race_none]; simp
  have ax := hL (Option (Fin k)) (by simpa using hk) n hn P none hUL
  let Q : Profile {a : Option (Fin k) // a ≠ none} n := fun r => qrace (σ r)
  have hQ : IsLoserRemoval P none Q := by
    intro r a
    simp only [P, Q]
    rw [qrace_val, some_eNone a, race_some]
  have hP : ∀ i : Fin k, totalScore s P (some i) = ∑ r, initSeg (s (k+1)) k (σ r i) := by
    intro i
    unfold totalScore
    refine Finset.sum_congr rfl (fun r _ => ?_)
    simp only [initSeg]
    rw [dif_pos (by have := (σ r i).2; omega)]
    exact s_congr s _ _ (by simp) (by simp only [P]; rw [race_some])
  have hQs : ∀ (i : Fin k) (h : (some i : Option (Fin k)) ≠ none),
      totalScore s Q ⟨some i, h⟩ = ∑ r, s k (σ r i) := by
    intro i h
    unfold totalScore
    refine Finset.sum_congr rfl (fun r _ => ?_)
    exact s_congr s _ _ (card_ne_none k) (by simp only [Q]; rw [qrace_val, eNone_some])
  have := ax.2 Q hQ ⟨some A, by simp⟩ ⟨some B, by simp⟩
  rw [hP, hP, hQs, hQs] at this
  simp only [(hσ _).1, (hσ _).2] at this
  exact this

lemma initSeg_aff {N : ℕ} {u v : Fin N → ℝ} (h : AffEquiv u v) (K : ℕ) (hK : K ≤ N) :
    AffEquiv (initSeg u K) (initSeg v K) := by
  obtain ⟨a, b, ha, h⟩ := h
  refine ⟨a, b, ha, fun j => ?_⟩
  simp only [initSeg]
  rw [dif_pos (by omega), dif_pos (by omega)]
  exact h _

lemma initSeg_initSeg {N : ℕ} (w : Fin N → ℝ) (K L : ℕ) (hKL : K ≤ L) (hL : L ≤ N) :
    initSeg (initSeg w L) K = initSeg w K := by
  funext j
  have := j.2
  simp only [initSeg]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma chain (M : ℕ∞) (s : ScoringRule) (hL : IndepUnanimousLosers M s) (k : ℕ) :
    ∀ d : ℕ, ((k + d + 1 : ℕ) : ℕ∞) ≤ M → AffEquiv (s k) (initSeg (s (k + d + 1)) k) := by
  intro d
  induction d with
  | zero => intro h; exact step M s hL k h
  | succ d ih =>
    intro h
    have h' : ((k + d + 1 : ℕ) : ℕ∞) ≤ M := le_trans (by exact_mod_cast (by omega)) h
    have h1 := ih h'
    have h2 := step M s hL (k + d + 1) h
    have h3 := initSeg_aff h2 k (by omega)
    rw [initSeg_initSeg _ k (k + d + 1) (by omega) (by omega)] at h3
    have e : k + (d + 1) + 1 = k + d + 1 + 1 := by omega
    rw [e]
    exact aff_trans h1 h3

lemma strict (M : ℕ∞) (s : ScoringRule) (hL : IndepUnanimousLosers M s) (m : ℕ)
    (hm : (m : ℕ∞) ≤ M) : StrictAnti (s m) := by
  cases m with
  | zero => intro a; exact a.elim0
  | succ k =>
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    by_cases hi : i.val + 1 = k
    · have e : i.succ = Fin.last k := Fin.ext (by simp; omega)
      rw [e]; exact last_lt M s hL k hm i
    · have ht : i.val + 2 < k + 1 := by have := i.2; omega
      obtain ⟨a, b, ha, hab⟩ := chain M s hL (i.val + 2) (k - i.val - 2)
        (by rw [show i.val + 2 + (k - i.val - 2) + 1 = k + 1 by omega]; exact hm)
      have hlt : s (i.val + 2) (Fin.last (i.val + 1)) < s (i.val + 2) (Fin.castSucc ⟨i.val, by omega⟩) :=
        last_lt M s hL (i.val + 1) (le_trans (by exact_mod_cast (by omega)) hm) ⟨i.val, by omega⟩
      have e1 := hab (Fin.last (i.val + 1))
      have e2 := hab (Fin.castSucc ⟨i.val, by omega⟩)
      simp only [initSeg] at e1 e2
      rw [dif_pos (by simp; omega)] at e1
      rw [dif_pos (by simp; omega)] at e2
      set N := i.val + 2 + (k - i.val - 2) + 1 with hN
      have hlt' : a * s N ⟨(Fin.last (i.val + 1) : ℕ), by simp; omega⟩
          < a * s N ⟨((Fin.castSucc ⟨i.val, by omega⟩ : Fin (i.val + 2)) : ℕ), by simp; omega⟩ := by
        linarith
      have hlt'' := lt_of_mul_lt_mul_left hlt' ha.le
      have f1 : s N ⟨(Fin.last (i.val + 1) : ℕ), by simp; omega⟩ = s (k+1) i.succ :=
        s_congr s _ _ (by omega) (by simp)
      have f2 : s N ⟨((Fin.castSucc ⟨i.val, by omega⟩ : Fin (i.val + 2)) : ℕ), by simp; omega⟩
          = s (k+1) i.castSucc := s_congr s _ _ (by omega) (by simp)
      rw [f1, f2] at hlt''
      exact hlt''

end GSP4L
namespace GSP4L
open GSP4

lemma converse (M : ℕ∞) (s : ScoringRule)
    (hS : ∀ m : ℕ, (m : ℕ∞) ≤ M → StrictAnti (s m))
    (hA : ∀ k m : ℕ, k < m → (m : ℕ∞) ≤ M → AffEquiv (s k) (initSeg (s m) k)) :
    IndepUnanimousLosers M s := by
  intro α _ _ hcard n hn P x hx
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  refine ⟨fun a hax => ?_, fun Q hQ a b => ?_⟩
  · unfold totalScore
    apply Finset.sum_lt_sum_of_nonempty hne
    intro i _
    apply hS _ hcard
    have h1 := hx i
    have h2 : P i a ≠ P i x := (P i).injective.ne hax
    have h3 := (P i a).2
    rw [Fin.lt_def]
    have : (P i a : ℕ) ≠ (P i x : ℕ) := Fin.val_ne_of_ne h2
    omega
  · have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨x⟩
    have hK : Fintype.card {a // a ≠ x} = Fintype.card α - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    obtain ⟨A, B, hA0, hAB⟩ := hA (Fintype.card {a // a ≠ x}) (Fintype.card α) (by omega) hcard
    have hT : ∀ c : {a // a ≠ x}, totalScore s Q c = A * totalScore s P c.1 + n * B := by
      intro c
      unfold totalScore
      rw [Finset.mul_sum]
      have : ∀ i, s (Fintype.card {a // a ≠ x}) (Q i c) = A * s (Fintype.card α) (P i c.1) + B := by
        intro i
        rw [hAB (Q i c)]
        simp only [initSeg]
        rw [dif_pos (by have := (Q i c).2; omega)]
        congr 2
        exact s_congr s _ _ rfl (hQ i c)
      simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [hT a, hT b]
    constructor
    · intro h
      have := mul_le_mul_of_nonneg_left h hA0.le
      linarith
    · intro h
      exact le_of_mul_le_mul_left (by linarith) hA0

end GSP4L

open GSP4 GSP4L in
theorem solution (M : ℕ∞) (s : ScoringRule) :
    IndepUnanimousLosers M s ↔
      (∀ m : ℕ, (m : ℕ∞) ≤ M → StrictAnti (s m)) ∧
        ∀ k m : ℕ, k < m → (m : ℕ∞) ≤ M → AffEquiv (s k) (initSeg (s m) k) := by
  constructor
  · intro hL
    refine ⟨fun m hm => strict M s hL m hm, fun k m hkm hm => ?_⟩
    have e : m = k + (m - k - 1) + 1 := by omega
    rw [e] at hm ⊢
    exact chain M s hL k (m - k - 1) hm
  · rintro ⟨hS, hA⟩
    exact converse M s hS hA
