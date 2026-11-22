-- Prove2me | solution 1 for NOFSeparation750.CodedGIP.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-22T21:04:55.203003+00:00
-- url     : https://prove2.me/submissions/9692940c-9671-47b9-ac5c-a92df1845203

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_Model

open NOFSeparation750.CodedGIP Finset

namespace P41Aux

/-- speaker `i` sends an `m`-bit message computed from its view, then continue -/
def sendBits {k : ℕ} {X : Fin k → Type} (i : Fin k) :
    (m : ℕ) → (View X i → Bits m) → (Bits m → BitProtocol X) → BitProtocol X
  | 0, _, cont => cont (fun j => j.elim0)
  | m+1, f, cont => .send i (fun v => f v 0)
      (sendBits i m (fun v => Fin.tail (f v)) (fun bs => cont (Fin.cons false bs)))
      (sendBits i m (fun v => Fin.tail (f v)) (fun bs => cont (Fin.cons true bs)))

theorem run_sendBits {k : ℕ} {X : Fin k → Type} (i : Fin k) : ∀ (m : ℕ)
    (f : View X i → Bits m) (cont : Bits m → BitProtocol X) (x : Input X),
    (sendBits i m f cont).run x =
      (((cont (f (visible i x))).run x).1, ((cont (f (visible i x))).run x).2 + m)
  | 0, f, cont, x => by
      have : (fun j : Fin 0 => j.elim0) = f (visible i x) := funext fun j => j.elim0
      simp [sendBits, this]
  | m+1, f, cont, x => by
      simp only [sendBits, BitProtocol.run]
      cases h : f (visible i x) 0
      · simp only [Bool.false_eq_true, if_false]
        rw [run_sendBits i m]
        have : (Fin.cons false (Fin.tail (f (visible i x))) : Bits (m+1)) = f (visible i x) := by
          rw [← h]; exact Fin.cons_self_tail _
        simp [this]; ring
      · simp only [if_true]
        rw [run_sendBits i m]
        have : (Fin.cons true (Fin.tail (f (visible i x))) : Bits (m+1)) = f (visible i x) := by
          rw [← h]; exact Fin.cons_self_tail _
        simp [this]; ring


section
variable {F : Type} [Field F] [Fintype F] {r b : ℕ} (D : CodePair F r)
  (codec : (Fin b → Bool) ≃ F) (ℓ : ℕ)

/-- the ℓ+1 field symbols of a forehead at coordinate t -/
noncomputable def vals (t : Fin r) (x0 : Bits (nativeLength D ℓ b)) : Fin (ℓ+1) → F :=
  fun h' => if hh : (h' : ℕ) < ℓ then ((decodeForehead D codec ℓ x0).1 ⟨h', hh⟩).val t
    else (decodeForehead D codec ℓ x0).2.val t

noncomputable def encodeVals (v : Fin (ℓ+1) → F) : Bits ((ℓ+1) * b) :=
  fun j => codec.symm (v (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2

noncomputable def decodeVals (bits : Bits ((ℓ+1) * b)) : Fin (ℓ+1) → F :=
  fun h' => codec (fun s => bits (finProdFinEquiv (h', s)))

omit [Fintype F] in
omit [Field F] in
theorem decode_encode (v : Fin (ℓ+1) → F) : decodeVals codec ℓ (encodeVals codec ℓ v) = v := by
  funext h'
  simp [decodeVals, encodeVals]

end

end P41Aux

theorem solution (k ℓ r b : ℕ) (hk : 2 ≤ k) (ε : ℝ)
    (F : Type) [Field F] [Fintype F] (D : CodePair F r)
    (codec : (Fin b → Bool) ≃ F)
    (hD : Compatible D.small.code D.large.code k ε (3 / 4)) :
    ∃ P : PublicProtocol (fun _ : Fin k => Bits (nativeLength D ℓ b)),
      P.Bounded ((ℓ + 1) * b + 1) ∧
      P.OneSided (nativeFunction D codec ℓ k) (1 / 4) := by
  classical
  obtain ⟨_, hr, _, _, _, _, _, hprod, _, hdist⟩ := hD
  set n := nativeLength D ℓ b with hn
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  let dec := decodeForehead D codec ℓ
  let decide0 : Fin r → Bits ((ℓ+1) * b) → View (fun _ : Fin k => Bits n) i0 → Bool :=
    fun t bits v0 => decide
      ((∑ h : Fin ℓ, ∏ i : Fin k, (if hi : i = i0 then P41Aux.decodeVals codec ℓ bits (Fin.castSucc h)
          else ((dec (v0 ⟨i, hi⟩)).1 h).val t)) =
        ∑ i : Fin k, (if hi : i = i0 then P41Aux.decodeVals codec ℓ bits (Fin.last ℓ)
          else (dec (v0 ⟨i, hi⟩)).2.val t))
  let tree : Fin r → BitProtocol (fun _ : Fin k => Bits n) := fun t =>
    P41Aux.sendBits i1 ((ℓ+1) * b)
      (fun v1 => P41Aux.encodeVals codec ℓ (P41Aux.vals D codec ℓ t (v1 ⟨i0, h01⟩)))
      (fun bits => .send i0 (decide0 t bits) (.leaf false) (.leaf true))
  let LHS : Input (fun _ : Fin k => Bits n) → Fin r → F := fun x =>
    ∑ h : Fin ℓ, (fun t => ∏ i : Fin k, ((dec (x i)).1 h).val t)
  let RHS : Input (fun _ : Fin k => Bits n) → Fin r → F := fun x =>
    ∑ i : Fin k, (dec (x i)).2.val
  have hrun : ∀ t x, (tree t).run x = (decide (LHS x t = RHS x t), (ℓ+1) * b + 1) := by
    intro t x
    simp only [tree, P41Aux.run_sendBits, BitProtocol.run]
    have hvals := P41Aux.decode_encode codec ℓ
      (P41Aux.vals D codec ℓ t ((visible i1 x) ⟨i0, h01⟩))
    have hA : ∀ (h : Fin ℓ) (i : Fin k),
        (if hi : i = i0 then P41Aux.decodeVals codec ℓ (P41Aux.encodeVals codec ℓ
          (P41Aux.vals D codec ℓ t ((visible i1 x) ⟨i0, h01⟩))) (Fin.castSucc h)
          else ((dec ((visible i0 x) ⟨i, hi⟩)).1 h).val t) = ((dec (x i)).1 h).val t := by
      intro h i
      split_ifs with hi
      · subst hi; rw [hvals]; simp [P41Aux.vals, visible, dec]
      · rfl
    have hC : ∀ (i : Fin k),
        (if hi : i = i0 then P41Aux.decodeVals codec ℓ (P41Aux.encodeVals codec ℓ
          (P41Aux.vals D codec ℓ t ((visible i1 x) ⟨i0, h01⟩))) (Fin.last ℓ)
          else (dec ((visible i0 x) ⟨i, hi⟩)).2.val t) = (dec (x i)).2.val t := by
      intro i
      split_ifs with hi
      · subst hi; rw [hvals]; simp [P41Aux.vals, visible, dec]
      · rfl
    simp only [decide0, hA, hC, LHS, RHS, Finset.sum_apply]
    by_cases hh : (∑ h : Fin ℓ, ∏ i : Fin k, ((dec (x i)).1 h).val t) = ∑ i : Fin k, (dec (x i)).2.val t
    · simp only [hh, decide_true, if_true]; ext <;> simp; ring
    · simp only [hh, decide_false, if_false]; ext <;> simp; ring
  have hnat : ∀ x, nativeFunction D codec ℓ k x = decide (LHS x = RHS x) := fun x => rfl
  have hrpos : (0:ℝ) < r := by exact_mod_cast hr
  have hacc : ∀ x, ∑ t : Fin r, (if ((tree t).run x).1 then (1 / (r:ℝ)) else 0) =
      ((univ.filter fun t => LHS x t = RHS x t).card : ℝ) / r := by
    intro x
    simp only [hrun, decide_eq_true_eq]
    rw [← sum_filter, sum_const, nsmul_eq_mul]; ring
  refine ⟨⟨r, fun _ => 1 / (r:ℝ), fun _ => by positivity, ?_, tree⟩, ?_, ?_, ?_⟩
  · simp [sum_const, card_univ, Fintype.card_fin]; field_simp
  · intro s x; simp [hrun]
  · intro x hx
    simp only [PublicProtocol.acceptance]
    rw [hacc]
    rw [hnat, decide_eq_true_eq] at hx
    have : univ.filter (fun t => LHS x t = RHS x t) = univ := by
      ext t; simp [hx]
    rw [this, card_univ, Fintype.card_fin]; field_simp
  · intro x hx
    simp only [PublicProtocol.acceptance]
    rw [hacc]
    rw [hnat, decide_eq_false_iff_not] at hx
    set bv := LHS x - RHS x with hbv
    have hne : bv ≠ 0 := sub_ne_zero.mpr hx
    have hmem : bv ∈ D.large.code := by
      refine Submodule.sub_mem _ (Submodule.sum_mem _ fun h _ => hprod ?_)
        (Submodule.sum_mem _ fun i _ => (dec (x i)).2.2)
      exact Submodule.subset_span ⟨fun i => (dec (x i)).1 h, rfl⟩
    have hd : distance D.large.code ≤ weight bv := Nat.sInf_le ⟨bv, hmem, hne, rfl⟩
    have hsplit := card_filter_add_card_filter_not
      (s := (univ : Finset (Fin r))) (fun t => LHS x t = RHS x t)
    have hw : weight bv = (univ.filter fun t => ¬ LHS x t = RHS x t).card := by
      unfold weight; congr 1; ext t; simp [hbv, sub_eq_zero]
    rw [card_univ, Fintype.card_fin] at hsplit
    have h1 : (3 / 4 : ℝ) * r ≤ (weight bv : ℝ) := hdist.trans (by exact_mod_cast hd)
    rw [hw] at h1
    have h2 : ((univ.filter fun t => LHS x t = RHS x t).card : ℝ) +
        ((univ.filter fun t => ¬ LHS x t = RHS x t).card : ℝ) = r := by exact_mod_cast hsplit
    rw [div_le_iff₀ hrpos]
    linarith
