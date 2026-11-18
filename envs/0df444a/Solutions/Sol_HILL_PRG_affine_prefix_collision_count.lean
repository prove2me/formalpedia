-- Prove2me | solution 1 for HILL.PRG.affine_prefix_collision_count
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-18T01:41:02.568088+00:00
-- url     : https://prove2.me/submissions/22467f2b-4684-4544-930a-2b028ef920c0

import Definitions.Def_HILL_PRG_Model
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.FinRange

open HILL.PRG
open scoped BigOperators

namespace HILL.PRG.AffineCollisionSubmission

theorem mem_cube_iff_length {x : Bits} {T : ℕ} : x ∈ cube T ↔ x.length = T := by
  unfold cube Levin2003.cube
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, rfl⟩
    simp
  · intro h
    subst T
    exact ⟨fun i => x[i.val], List.ofFn_getElem⟩

namespace Blocks

def flatten {k : ℕ} (xs : Fin k → Bits) : Bits := (List.ofFn xs).flatten

def block {k : ℕ} (T : ℕ) (x : Bits) (i : Fin k) : Bits :=
  (x.drop (i.val * T)).take T

theorem flatten_length {k T : ℕ} (xs : Fin k → Bits)
    (hx : ∀ i, (xs i).length = T) : (flatten xs).length = k * T := by
  induction k with
  | zero => simp [flatten]
  | succ k ih =>
    simp only [flatten, List.ofFn_succ, List.flatten_cons, List.length_append, hx]
    rw [← flatten, ih _ (fun i => hx i.succ), Nat.succ_mul, Nat.add_comm]

theorem block_length {k T : ℕ} {x : Bits} (h : x.length = k * T) (i : Fin k) :
    (block T x i).length = T := by
  have hbound : (i.val + 1) * T ≤ k * T := Nat.mul_le_mul_right T i.isLt
  rw [Nat.add_mul, one_mul] at hbound
  simpa [block, h] using (Nat.min_eq_left (show T ≤ k * T - i.val * T by omega))

theorem block_flatten {k T : ℕ} (xs : Fin k → Bits)
    (hx : ∀ i, (xs i).length = T) (i : Fin k) : block T (flatten xs) i = xs i := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [block, flatten, List.ofFn_succ] using
        List.take_left' (l₂ := flatten (fun i : Fin k => xs i.succ)) (hx 0)
    · have hdrop : (flatten xs).drop T = flatten (fun i : Fin k => xs i.succ) := by
        simpa [flatten, List.ofFn_succ] using
          List.drop_left' (l₂ := flatten (fun i : Fin k => xs i.succ)) (hx 0)
      change ((flatten xs).drop ((j.val + 1) * T)).take T = xs j.succ
      rw [Nat.add_mul, one_mul, Nat.add_comm (j.val * T) T, ← List.drop_drop, hdrop]
      exact ih _ (fun i => hx i.succ) j

theorem flatten_block {k T : ℕ} {x : Bits} (h : x.length = k * T) :
    flatten (block (k := k) T x) = x := by
  induction k generalizing x with
  | zero => exact (List.length_eq_zero_iff.mp (by simpa using h)).symm
  | succ k ih =>
    have hTail : (x.drop T).length = k * T := by
      simp [h, Nat.succ_mul]
    have hBlock (i : Fin k) : block T x i.succ = block T (x.drop T) i := by
      simp [block, Nat.add_mul, Nat.add_comm, List.drop_drop]
    simp only [flatten, List.ofFn_succ, List.flatten_cons, hBlock]
    have hHead : block T x (0 : Fin (k + 1)) = x.take T := by simp [block]
    rw [hHead]
    change x.take T ++ flatten (block (k := k) T (x.drop T)) = x
    rw [ih hTail, List.take_append_drop]

theorem flatten_bijOn (k T : ℕ) :
    Set.BijOn (flatten (k := k)) (↑(Fintype.piFinset (fun _ : Fin k => cube T)) : Set (Fin k → Bits))
      (cube (k * T) : Set Bits) := by
  have hl (xs : Fin k → Bits) (hxs : xs ∈ Fintype.piFinset (fun _ => cube T)) :
      ∀ i, (xs i).length = T := fun i => mem_cube_iff_length.mp (Fintype.mem_piFinset.mp hxs i)
  refine ⟨?_, ?_, ?_⟩
  · exact fun xs hxs => mem_cube_iff_length.mpr (flatten_length xs (hl xs hxs))
  · intro x hx y hy hxy
    funext i
    rw [← block_flatten x (hl x hx) i, hxy, block_flatten y (hl y hy) i]
  · intro x hx
    exact ⟨block T x, Fintype.mem_piFinset.mpr (fun i =>
      mem_cube_iff_length.mpr (block_length (mem_cube_iff_length.mp hx) i)),
      flatten_block (mem_cube_iff_length.mp hx)⟩

end Blocks

section

variable {A B : Type*}

theorem finset_card_eq_of_bijOn {f : A → B} {S : Finset A} {T : Finset B}
    (h : Set.BijOn f ↑S ↑T) : S.card = T.card :=
  Finset.card_bij (fun x _ => f x) h.mapsTo h.injOn (fun _ hb => by
    obtain ⟨x, hx, he⟩ := h.surjOn hb
    exact ⟨x, hx, he⟩)

end

theorem cube_card (T : ℕ) : (cube T).card = 2 ^ T := by
  unfold cube Levin2003.cube
  rw [Finset.card_image_of_injective _ List.ofFn_injective]
  simp

private def keyWidth (N : ℕ) : ℕ := N * (N + 1)

private def affinePrefix (N j : ℕ) (r x : Bits) : Bits :=
  (List.range j).map fun i =>
    Bool.xor (r.getD (i * (N + 1)) false)
      (ip ((r.drop (i * (N + 1) + 1)).take N) (x.take N))

private theorem parity_succ (n : ℕ) :
    ((n + 1) % 2 == 1) = !(n % 2 == 1) := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h <;> simp [Nat.add_mod n 1 2, h]

theorem ip_cons (a b : Bool) (x y : Bits) :
    ip (a :: x) (b :: y) = Bool.xor (a && b) (ip x y) := by
  cases a <;> cases b <;> simp [ip, List.zip_cons_cons]
  exact parity_succ _

private theorem innerXor (a b c p q : Bool) :
    Bool.xor (Bool.xor (a && b) p) (Bool.xor (a && c) q) =
      Bool.xor (a && Bool.xor b c) (Bool.xor p q) := by
  cases a <;> cases b <;> cases c <;> cases p <;> cases q <;> rfl

theorem ip_xor_right (c x y : Bits) (h : x.length = y.length) :
    ip c (List.zipWith Bool.xor x y) = Bool.xor (ip c x) (ip c y) := by
  induction c generalizing x y with
  | nil => simp [ip]
  | cons a c ih =>
    cases x with
    | nil =>
      have hy : y = [] := List.length_eq_zero_iff.mp h.symm
      simp [hy, ip]
    | cons b x =>
      cases y with
      | nil => simp at h
      | cons d y =>
        have hl : x.length = y.length := by simpa using h
        simp only [List.zipWith_cons_cons, ip_cons, ih x y hl, innerXor]

theorem xor_zip_has_true (x y : Bits) (h : x.length = y.length) (hxy : x ≠ y) :
    true ∈ List.zipWith Bool.xor x y := by
  induction x generalizing y with
  | nil => exact False.elim (hxy (List.length_eq_zero_iff.mp h.symm).symm)
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      by_cases hab : a = b
      · subst b
        have hLen : x.length = y.length := by simpa using h
        have hNe : x ≠ y := fun he => hxy (congrArg (List.cons a) he)
        exact List.mem_cons_of_mem _ (ih y hLen hNe)
      · have hxor : Bool.xor a b = true := by cases a <;> cases b <;> simp_all
        exact List.mem_cons.mpr (Or.inl hxor.symm)

private theorem xor_eq_false_iff (a b : Bool) : Bool.xor a b = false ↔ a = b := by
  cases a <;> cases b <;> decide

private theorem card_cube_filter_tail (N : ℕ) (p : Bits → Prop) [DecidablePred p] :
    ((cube (N + 1)).filter (fun x => p x.tail)).card =
      2 * ((cube N).filter p).card := by
  let S := (Finset.univ : Finset Bool) ×ˢ (cube N).filter p
  let T := (cube (N + 1)).filter (fun x => p x.tail)
  have h : Set.BijOn (fun q : Bool × Bits => q.1 :: q.2) ↑S ↑T := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨b, x⟩ hx
      obtain ⟨_, h⟩ := Finset.mem_product.mp hx
      obtain ⟨hLen, hP⟩ := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨mem_cube_iff_length.mpr (by simp [mem_cube_iff_length.mp hLen]), hP⟩
    · rintro ⟨b, x⟩ _ ⟨c, y⟩ _ he
      simpa only [List.cons.injEq, Prod.mk.injEq] using he
    · intro z hz
      obtain ⟨hl, hp⟩ := Finset.mem_filter.mp hz
      cases z with
      | nil => simp [mem_cube_iff_length] at hl
      | cons b w =>
        have hw : w.length = N := by simpa using mem_cube_iff_length.mp hl
        exact ⟨(b, w), Finset.mem_product.mpr
          ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨mem_cube_iff_length.mpr hw, hp⟩⟩, rfl⟩
  rw [← finset_card_eq_of_bijOn h]
  simp [S]

private theorem card_even_innerProduct (w : Bits) (hw : true ∈ w) :
    ((cube w.length).filter (fun c => ip c w = false)).card * 2 = 2 ^ w.length := by
  induction w with
  | nil => simp at hw
  | cons b w ih =>
    cases b with
    | false =>
      have hFilter : (cube (false :: w).length).filter (fun c => ip c (false :: w) = false) =
          (cube (w.length + 1)).filter (fun c => ip c.tail w = false) := by
        ext c
        have hc : ip c (false :: w) = ip c.tail w := by cases c <;> simp [ip]
        simp only [List.length_cons, Finset.mem_filter, hc]
      rw [hFilter, card_cube_filter_tail w.length (fun c => ip c w = false)]
      have h := ih (by simpa using hw)
      rw [List.length_cons, pow_succ, Nat.mul_comm (2 ^ w.length) 2, ← h, Nat.mul_assoc]
    | true =>
      have h : Set.BijOn (fun c : Bits => c.tail)
          ↑((cube (w.length + 1)).filter (fun c => ip c (true :: w) = false)) ↑(cube w.length) := by
        refine ⟨?_, ?_, ?_⟩
        · intro c hc
          apply mem_cube_iff_length.mpr
          have hl := mem_cube_iff_length.mp (Finset.mem_filter.mp hc).1
          simp [hl]
        · intro c hc d hd he
          obtain ⟨hcL, hcI⟩ := Finset.mem_filter.mp hc
          obtain ⟨hdL, hdI⟩ := Finset.mem_filter.mp hd
          cases c with
          | nil => simp [mem_cube_iff_length] at hcL
          | cons a c =>
            cases d with
            | nil => simp [mem_cube_iff_length] at hdL
            | cons b d =>
              have ha : a = ip c w := by
                apply (xor_eq_false_iff _ _).mp
                simpa only [ip_cons, Bool.and_true] using hcI
              have hb : b = ip d w := by
                apply (xor_eq_false_iff _ _).mp
                simpa only [ip_cons, Bool.and_true] using hdI
              simp only [List.cons.injEq]
              exact ⟨ha.trans ((congrArg (fun v => ip v w) he).trans hb.symm), he⟩
        · intro c hc
          refine ⟨ip c w :: c, Finset.mem_filter.mpr ⟨mem_cube_iff_length.mpr ?_, ?_⟩, rfl⟩
          · simp [mem_cube_iff_length.mp hc]
          · simp [ip_cons]
      rw [List.length_cons, finset_card_eq_of_bijOn h, cube_card, pow_succ]

private def rowOutput (r x : Bits) : Bool := Bool.xor (r.headD false) (ip r.tail x)

private theorem row_collision_card {N : ℕ} (x y : Bits)
    (hx : x.length = N) (hy : y.length = N) (hxy : x ≠ y) :
    ((cube (N + 1)).filter (fun r => rowOutput r x = rowOutput r y)).card = 2 ^ N := by
  let w := List.zipWith Bool.xor x y
  have hLen : w.length = N := by simp [w, hx, hy]
  have hTrue : true ∈ w := xor_zip_has_true x y (hx.trans hy.symm) hxy
  have hFilt : (cube (N + 1)).filter (fun r => rowOutput r x = rowOutput r y) =
      (cube (N + 1)).filter (fun r => ip r.tail w = false) := by
    ext r
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [rowOutput, w, ip_xor_right _ _ _ (hx.trans hy.symm)]
    apply and_congr_right
    intro _
    cases r.headD false <;> cases ip r.tail x <;> cases ip r.tail y <;> decide
  rw [hFilt, card_cube_filter_tail N (fun c => ip c w = false), Nat.mul_comm 2]
  simpa only [hLen] using card_even_innerProduct w hTrue

private theorem rowOutput_eq_key_bit (r x : Bits) {N : ℕ} (hx : x.length = N)
    (i : Fin N) :
    rowOutput (Blocks.block (N + 1) r i) x =
      Bool.xor (r.getD (i.val * (N + 1)) false)
        (ip ((r.drop (i.val * (N + 1) + 1)).take N) (x.take N)) := by
  rw [List.take_of_length_le hx.le]
  let d := i.val * (N + 1)
  have hHead : (r.drop d).headD false = r.getD d false := by
    simp [List.getD_eq_getElem?_getD]
  have hTail : r.drop (d + 1) = (r.drop d).tail := by
    rw [← List.drop_drop]
    simp
  change rowOutput ((r.drop d).take (N + 1)) x =
    Bool.xor (r.getD d false) (ip ((r.drop (d + 1)).take N) x)
  unfold rowOutput
  rw [← hHead, hTail]
  cases r.drop d <;> simp

open scoped BigOperators

set_option maxHeartbeats 1000000 in
/-- For distinct inputs each retained affine row imposes one independent
bit constraint on the full key. -/
private theorem affineCollision (N j : ℕ) (hj : j ≤ N) (x y : Bits)
    (hx : x ∈ cube N) (hy : y ∈ cube N) (hxy : x ≠ y) :
    ((cube (keyWidth N)).filter (fun r => affinePrefix N j r x = affinePrefix N j r y)).card *
      2 ^ j = 2 ^ keyWidth N := by
  classical
  have hX := mem_cube_iff_length.mp hx
  have hY := mem_cube_iff_length.mp hy
  let R := cube (N + 1)
  let A := R.filter (fun r => rowOutput r x = rowOutput r y)
  let Q := Fintype.piFinset (fun _ : Fin N => R)
  let U : Fin N → Finset Bits := fun i => if i.val < j then A else R
  let S := Fintype.piFinset U
  let D := (cube (keyWidth N)).filter (fun r => affinePrefix N j r x = affinePrefix N j r y)
  have hQ := Blocks.flatten_bijOn N (N + 1)
  have hKey (rs : Fin N → Bits) (hrs : rs ∈ Q) :
      Blocks.flatten rs ∈ D ↔ rs ∈ S := by
    have hLen (i : Fin N) : (rs i).length = N + 1 :=
      mem_cube_iff_length.mp (Fintype.mem_piFinset.mp hrs i)
    have hEq :
        affinePrefix N j (Blocks.flatten rs) x = affinePrefix N j (Blocks.flatten rs) y ↔
          ∀ i : Fin N, i.val < j → rowOutput (rs i) x = rowOutput (rs i) y := by
      simp only [affinePrefix, List.map_inj_left, List.mem_range]
      constructor
      · intro h i hi
        rw [← Blocks.block_flatten rs hLen i, rowOutput_eq_key_bit _ _ hX, rowOutput_eq_key_bit _ _ hY]
        exact h i.val hi
      · intro h i hi
        let k : Fin N := ⟨i, hi.trans_le hj⟩
        have he := h k hi
        rw [← Blocks.block_flatten rs hLen k, rowOutput_eq_key_bit _ _ hX,
          rowOutput_eq_key_bit _ _ hY] at he
        exact he
    change
      Blocks.flatten rs ∈ (cube (keyWidth N)).filter
        (fun r => affinePrefix N j r x = affinePrefix N j r y) ↔
      rs ∈ Fintype.piFinset U
    rw [Finset.mem_filter, Fintype.mem_piFinset, hEq]
    have hMem : Blocks.flatten rs ∈ cube (keyWidth N) := hQ.mapsTo hrs
    constructor
    · rintro ⟨_, hh⟩ i
      have hRi : rs i ∈ R := Fintype.mem_piFinset.mp hrs i
      by_cases hi : i.val < j
      · simpa only [U, if_pos hi, A, Finset.mem_filter] using And.intro hRi (hh i hi)
      · simpa only [U, if_neg hi] using hRi
    · intro h
      refine ⟨hMem, fun i hi => ?_⟩
      simpa only [U, if_pos hi, A, Finset.mem_filter, and_iff_right
        (Fintype.mem_piFinset.mp hrs i)] using h i
  have hSubset : S ⊆ Q := by
    intro rs hrs
    apply Fintype.mem_piFinset.mpr
    intro i
    have hi := Fintype.mem_piFinset.mp hrs i
    by_cases h : i.val < j
    · exact (Finset.mem_filter.mp (by simpa only [U, if_pos h] using hi : rs i ∈ A)).1
    · simpa only [U, if_neg h] using hi
  have hBij : Set.BijOn (Blocks.flatten (k := N)) ↑S ↑D := by
    refine ⟨fun rs hr => (hKey rs (hSubset hr)).mpr hr, hQ.injOn.mono hSubset, ?_⟩
    intro r hr
    obtain ⟨rs, hrs, rfl⟩ := hQ.surjOn (Finset.mem_filter.mp hr).1
    exact ⟨rs, (hKey rs hrs).mp hr, rfl⟩
  have hSorted : ((Finset.univ : Finset (Fin N)).filter (fun i => i.val < j)).card = j := by
    refine (Finset.card_bij (t := Finset.range j) (fun i _ => i.val) ?_ ?_ ?_).trans
      (Finset.card_range j)
    · exact fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    · exact fun i _ k _ he => Fin.ext he
    · intro i hi
      have hij := Finset.mem_range.mp hi
      exact ⟨⟨i, hij.trans_le hj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩
  have hTwo : (∏ i : Fin N, if i.val < j then (2 : ℕ) else 1) = 2 ^ j := by
    rw [Finset.prod_ite]
    simp [hSorted]
  have hA : A.card = 2 ^ N := row_collision_card x y hX hY hxy
  have hRow (i : Fin N) :
      (U i).card * (if i.val < j then (2 : ℕ) else 1) = 2 ^ (N + 1) := by
    by_cases h : i.val < j
    · simp [U, h, hA, pow_succ]
    · simp [U, h, R, cube_card]
  change D.card * 2 ^ j = 2 ^ keyWidth N
  rw [← finset_card_eq_of_bijOn hBij, Fintype.card_piFinset, ← hTwo, ← Finset.prod_mul_distrib]
  simp only [hRow, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul, keyWidth, Nat.mul_comm (N + 1) N]

end HILL.PRG.AffineCollisionSubmission

theorem solution (N j : ℕ) (hj : j ≤ N) (x y : Bits)
    (hx : x ∈ cube N) (hy : y ∈ cube N) (hxy : x ≠ y) :
    let affine := fun (r w : Bits) =>
      (List.range j).map fun i =>
        Bool.xor (r.getD (i * (N + 1)) false)
          (ip ((r.drop (i * (N + 1) + 1)).take N) (w.take N))
    ((cube (N * (N + 1))).filter (fun r => affine r x = affine r y)).card *
      2 ^ j = 2 ^ (N * (N + 1)) := by
  exact HILL.PRG.AffineCollisionSubmission.affineCollision N j hj x y hx hy hxy
