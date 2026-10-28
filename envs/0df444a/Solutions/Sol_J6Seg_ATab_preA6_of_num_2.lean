-- Prove2me | solution 2 for J6Seg.ATab.preA6_of_num
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:46:47.149986+00:00
-- url     : https://prove2.me/submissions/343f135e-d122-47c8-abbc-0b7db8640952

import Definitions.Def_IntMul_Kappa_R6_Defs69
import Theorems.Thm_J6Seg_PJ_setup_of_native
import Theorems.Thm_J6Seg_ATab_natUp_sp
import Theorems.Thm_J6Seg_PJ_tearP_sp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

open IntMul NLogN NLogN.KIL RS J6Seg.PJ IntMul.HvdH IntMul.Kappa.R6 Function
open J6Seg J6Seg.ATab

/-! Private helpers for the native-layout bridge. -/

private theorem fne {a b : Fin HS} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

private theorem fwd_at {m : ℕ} (a b : Fin m → Fin HS) (ha : Injective a) (k : Fin m) :
    fwd a b (a k) = b k := by
  have h : ∃ j, a j = a k := ⟨k, rfl⟩
  simp only [fwd, dif_pos h]
  rw [ha h.choose_spec]

private theorem fwd_out {m : ℕ} (a b : Fin m → Fin HS) {x : Fin HS} (h : ¬ ∃ k, a k = x) :
    fwd a b x = x := by
  simp only [fwd, dif_neg h]

private theorem fwd_fwd {m : ℕ} (a b : Fin m → Fin HS)
    (ha : Injective a) (hb : Injective b) (h55 : ∀ k, (a k).val = 55 ↔ (b k).val = 55)
    (hlt : ∀ k, (a k).val < 56) (hlt' : ∀ k, (b k).val < 56) (x : Fin HS)
    (hx : (∃ k, a k = x) ∨ 55 ≤ x.val) : fwd b a (fwd a b x) = x := by
  by_cases h : ∃ k, a k = x
  · obtain ⟨k, rfl⟩ := h
    rw [fwd_at a b ha, fwd_at b a hb]
  · rw [fwd_out a b h]
    have hx' : 55 ≤ x.val := hx.resolve_left h
    have hn : ¬ ∃ k, b k = x := by
      rintro ⟨k, hk⟩
      have h1 := hlt' k
      have h2 : (b k).val = 55 := by rw [hk] at h1 ⊢; omega
      have h3 := (h55 k).mpr h2
      exact h ⟨k, by apply Fin.ext; rw [h3, ← h2, hk]⟩
    exact fwd_out b a hn

private theorem fwd_mem {m : ℕ} (a b : Fin m → Fin HS)
    (hb : Injective b) (h55 : ∀ k, (a k).val = 55 ↔ (b k).val = 55)
    (hlt : ∀ k, (a k).val < 56) (x : Fin HS) (hx : (∃ k, a k = x) ∨ 55 ≤ x.val) :
    (∃ k, b k = fwd a b x) ∨ 55 ≤ (fwd a b x).val := by
  by_cases h : ∃ k, a k = x
  · left; exact ⟨h.choose, by simp only [fwd, dif_pos h]⟩
  · right; rw [fwd_out a b h]; exact hx.resolve_left h

private theorem exists_perm {m : ℕ} (a b : Fin m → Fin HS)
    (ha : Injective a) (hb : Injective b)
    (h55 : ∀ k, (a k).val = 55 ↔ (b k).val = 55) (hlt : ∀ k, (a k).val < 56)
    (hlt' : ∀ k, (b k).val < 56) :
    ∃ σ : Equiv.Perm (Fin HS), FixHi σ ∧ ∀ k, σ (a k) = b k := by
  have h55' : ∀ k, (b k).val = 55 ↔ (a k).val = 55 := fun k => (h55 k).symm
  let e : { x : Fin HS // (∃ k, a k = x) ∨ 55 ≤ x.val } ≃
      { x : Fin HS // (∃ k, b k = x) ∨ 55 ≤ x.val } :=
    { toFun := fun x => ⟨fwd a b x.1, fwd_mem a b hb h55 hlt x.1 x.2⟩
      invFun := fun y => ⟨fwd b a y.1, fwd_mem b a ha h55' hlt' y.1 y.2⟩
      left_inv := fun x => Subtype.ext (fwd_fwd a b ha hb h55 hlt hlt' x.1 x.2)
      right_inv := fun y => Subtype.ext (fwd_fwd b a hb ha h55' hlt' hlt y.1 y.2) }
  refine ⟨Equiv.extendSubtype e, fun i hi => ?_, fun k => ?_⟩
  · rw [Equiv.extendSubtype_apply_of_mem e i (Or.inr hi)]
    show fwd a b i = i
    by_cases h : ∃ k, a k = i
    · obtain ⟨k, rfl⟩ := h
      have := hlt k
      have h2 : (a k).val = 55 := by omega
      have h3 := (h55 k).mp h2
      rw [fwd_at a b ha]; apply Fin.ext; rw [h2, h3]
    · exact fwd_out a b h
  · rw [Equiv.extendSubtype_apply_of_mem e (a k) (Or.inl ⟨k, rfl⟩)]
    exact fwd_at a b ha k

private theorem oNf_val (ρ : Fin 19 → Fin HS) (i : Fin 19) :
    (oNf ρ i).val = 55 ∨ ((oNf ρ i).val = i.val + 1 ∧ (ρ i).val ≠ 55) := by
  unfold oNf; split_ifs with h
  · left; rfl
  · right; exact ⟨rfl, h⟩

private theorem nativeLayout (ρ : Fin 19 → Fin HS) (dA : Fin HS) (hρ : Injective ρ)
    (hd : ∀ i, ρ i ≠ dA) (hlt : ∀ i, (ρ i).val < 56) (hdlt : dA.val < 56) :
    ∃ σ : Equiv.Perm (Fin HS), FixHi σ ∧ σ (Znf dA) = dA ∧ ∀ i, σ (oNf ρ i) = ρ i := by
  have hO55 : ∀ i, (oNf ρ i).val = 55 ↔ (ρ i).val = 55 := by
    intro i; unfold oNf; split_ifs with h
    · simp [h]
    · simp only [h, iff_false]; have := i.2; omega
  have hOinj : Injective (oNf ρ) := by
    intro i j h
    rcases oNf_val ρ i with hi | ⟨hi, hi'⟩ <;> rcases oNf_val ρ j with hj | ⟨hj, hj'⟩
    · exact hρ (Fin.ext (by rw [(hO55 i).mp hi, (hO55 j).mp hj]))
    · have := congrArg Fin.val h; have := j.2; omega
    · have := congrArg Fin.val h; have := i.2; omega
    · have := congrArg Fin.val h; exact Fin.ext (by omega)
  have hZv : ((Znf dA).val = 55 ∧ dA.val = 55) ∨ ((Znf dA).val = 49 ∧ dA.val ≠ 55) := by
    unfold Znf; split_ifs with h
    · left; exact ⟨rfl, h⟩
    · right; exact ⟨rfl, h⟩
  have hZ55 : (Znf dA).val = 55 ↔ dA.val = 55 := by omega
  have hZO : ∀ i, oNf ρ i ≠ Znf dA := by
    intro i h
    have hv := congrArg Fin.val h
    rcases oNf_val ρ i with hi | ⟨hi, hi'⟩
    · have h1 := (hO55 i).mp hi
      have h2 := hZ55.mp (by rw [← hv]; exact hi)
      exact hd i (Fin.ext (by rw [h1, h2]))
    · have := i.2; omega
  have ha : Injective (Fin.cons (Znf dA) (oNf ρ) : Fin 20 → Fin HS) :=
    Fin.cons_injective_iff.mpr ⟨fun ⟨i, hi⟩ => hZO i hi, hOinj⟩
  have hb : Injective (Fin.cons dA ρ : Fin 20 → Fin HS) :=
    Fin.cons_injective_iff.mpr ⟨fun ⟨i, hi⟩ => hd i hi, hρ⟩
  obtain ⟨σ, hσ, hk⟩ := exists_perm _ _ ha hb
    (fun k => Fin.cases (by simpa using hZ55) (fun i => by simpa using hO55 i) k)
    (fun k => Fin.cases (by simp only [Fin.cons_zero]; omega) (fun i => by
      simp only [Fin.cons_succ]; rcases oNf_val ρ i with hi | ⟨hi, _⟩ <;> rw [hi] <;>
        have := i.2 <;> omega) k)
    (fun k => Fin.cases (by simpa using hdlt) (fun i => by simpa using hlt i) k)
  exact ⟨σ, hσ, by simpa using hk 0, fun i => by simpa using hk i.succ⟩

private theorem kerRegs_vsA (w w' f pre nc post : ℕ) (T : List ℤ) (i : Fin 9) :
    kerRegs w w' f pre nc post T (Fin.castLE (by omega) i) =
      [(vsA w w' f pre nc post).getD i 0] := by
  fin_cases i <;> rfl

private theorem kerRegs_hi' (w w' f pre nc post : ℕ) (T : List ℤ) (i : Fin 19)
    (h : 11 ≤ i.val) : kerRegs w w' f pre nc post T i = [] := by
  have h0 : i.val ≠ 0 := by omega
  have h1 : i.val ≠ 1 := by omega
  have h2 : i.val ≠ 2 := by omega
  have h3 : i.val ≠ 3 := by omega
  have h4 : i.val ≠ 4 := by omega
  have h5 : i.val ≠ 5 := by omega
  have h6 : i.val ≠ 6 := by omega
  have h7 : i.val ≠ 7 := by omega
  have h8 : i.val ≠ 8 := by omega
  have h9 : i.val ≠ 9 := by omega
  have h10 : i.val ≠ 10 := by omega
  simp only [kerRegs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, if_false]

/-- `PreA6` from the numeric facts via the native layout and relocated set-up pair. -/
theorem solution {P : Prm} {pkA pkC bA bC : ℕ} (h : NumA6 P pkA pkC bA bC)
    (tab : Fin 1 → IStmt HS 1) : PreA6 P pkA pkC bA bC tab := by
  intro ρ dA hρ hd h0 h49 hd0 hd49 hlt hdlt
  obtain ⟨σ, hσ, hZ, hO⟩ := nativeLayout ρ dA hρ hd hlt hdlt
  have hinj : Injective (oNf ρ) := fun i j e => hρ (by rw [← hO i, ← hO j, e])
  have hZo : ∀ i, oNf ρ i ≠ Znf dA := fun i e => hd i (by rw [← hO i, e, hZ])
  have hOv : ∀ i, (oNf ρ i).val < 31 ∨ (oNf ρ i).val = 55 := fun i => by
    rcases oNf_val ρ i with h | ⟨h, -⟩
    · exact Or.inr h
    · left; rw [h]; have := i.2; omega
  have hZv : (Znf dA).val = 49 ∨ (Znf dA).val = 55 := by
    unfold Znf; split_ifs
    · right; rfl
    · left; rfl
  have v48 : (cLC : Fin HS).val = 48 := rfl
  have hC : ∀ i, oNf ρ i ≠ cLC := fun i => fne (by have := hOv i; omega)
  have hZC : cLC ≠ Znf dA := fne (by omega)
  have hlt' : ∀ i, (oNf ρ i).val < 56 := fun i => by have := hOv i; omega
  obtain ⟨Cp, A, n₁, hCp, hN⟩ := h
  refine ⟨2, fun E idx i => if i.val = 0 then ((natUp pkA pkC bA bC (Znf dA) (oNf ρ)).ren σ).code
    else ((tearP (oNf ρ)).ren σ).code, 0, 1, Cp, A, n₁, hCp, ?_⟩
  intro n hn src hsrc D hD k hk E ext idx hU Isym
  obtain ⟨W, B, hok, hcU, hcD⟩ := hN n hn src hsrc D hD k hk
  refine setup_of_native Isym _ (idx 0) (idx 1) ρ dA (descAx6 P n src D k)
    (aRegs6 P n src D k (pkA6 pkA pkC (pP6 P n)) (bA6 bA bC (pP6 P n))) _ σ hσ (Znf dA) (oNf ρ)
    hinj hZ hO (natUp pkA pkC bA bC (Znf dA) (oNf ρ)) (tearP (oNf ρ)) (by rw [hU]; rfl)
    (by rw [hU]; rfl) _ _ (fun s0 => natUp_sp s0 (Znf dA) (oNf ρ) hinj hOv hZv hZo hok.hdL hok.hp1
      hok.hα1 hok.hmW hok.hP hok.hA hok.hrW hok.hdB hok.h8 hok.hvB hok.hlB hok.hTB)
    (fun s0 => tearP_sp s0 (oNf ρ) hinj hlt' hC _ (fun i => by rw [F0, update_of_ne (hZo i)])
      (by rw [F0, update_of_ne hZC]) _ _
      (fun i => ((vsA (pP6 P n + 2) (pkA * pP6 P n + pkC + 1)
        (Nat.log 2 (sWidth (pP6 P n) (αN6 P n)) + 3) (preT P n D k)
        (ncA (pP6 P n) (tF6 P n k) (αN6 P n)) (postT P n D k)).getD i 0))
      (fun i => kerRegs_vsA _ _ _ _ _ _ _ i) rfl rfl (kerRegs_hi' _ _ _ _ _ _ _) B
      (fun i => hok.hvB _ (by fin_cases i <;> simp [vsA])) hok.hlB hok.hTB) hcU hcD

end
