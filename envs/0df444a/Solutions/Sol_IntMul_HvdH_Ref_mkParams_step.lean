-- Prove2me | solution 1 for IntMul.HvdH.Ref.mkParams_step
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T19:14:18.135034+00:00
-- url     : https://prove2.me/submissions/e7f02a1e-fb1a-4384-83b9-7e28b993079f

import Theorems.Thm_IntMul_HvdH_bluestein_fp
import Theorems.Thm_IntMul_HvdH_mulZ_disc
import Theorems.Thm_IntMul_HvdH_coprime_window
import Theorems.Thm_IntMul_HvdH_dftC_eq_dftBox
import Theorems.Thm_IntMul_HvdH_exactConv_eq
import Theorems.Thm_IntMul_HvdH_kpack_polyMul
import Theorems.Thm_IntMul_HvdH_kunpack_kpack
import Theorems.Thm_IntMul_HvdH_convC_round
import Definitions.Def_IntMul_HvdH_MachineRef
import Definitions.Def_IntMul_HvdH_KronMul
import Definitions.Def_IntMul_HvdH_Fermat
import Definitions.Def_IntMul_HvdH_FermConv
import Definitions.Def_IntMul_HvdH_SynFFT
import Definitions.Def_IntMul_HvdH_FixedPoint
import Definitions.Def_IntMul_HvdH_ConvR
import Definitions.Def_IntMul_HvdH_ConvC
import Theorems.Thm_IntMul_HvdH_twiddle_bound
import Definitions.Def_IntMul_HvdH_ExactConv
import Theorems.Thm_IntMul_HvdH_mulZ_err
import Theorems.Thm_IntMul_HvdH_thm_4_1_fp
import Theorems.Thm_IntMul_HvdH_fp_comp
import Mathlib

set_option maxHeartbeats 1000000

theorem IntMul.HvdH.BoxConv.ns_anchor : True := trivial
theorem IntMul.HvdH.CRPf.ns_anchor : True := trivial
theorem IntMul.HvdH.CRProp.ns_anchor : True := trivial
theorem IntMul.HvdH.ExId.ns_anchor : True := trivial
theorem IntMul.HvdH.ExPf.ns_anchor : True := trivial
theorem IntMul.HvdH.FCPf.ns_anchor : True := trivial
theorem IntMul.HvdH.FP.ns_anchor : True := trivial
theorem IntMul.HvdH.FPPf.ns_anchor : True := trivial
theorem IntMul.HvdH.FermPf.ns_anchor : True := trivial
theorem IntMul.HvdH.KronPf.ns_anchor : True := trivial
theorem IntMul.HvdH.RCv.ns_anchor : True := trivial
theorem IntMul.HvdH.Ref.ns_anchor : True := trivial
theorem IntMul.HvdH.TKer.ns_anchor : True := trivial

-- ===== Solutions.HvdH.Ref.Spec
section

/-! Interfaces for the correctness proof of `refStep`. -/

namespace IntMul.HvdH.RefPf
open IntMul.HvdH IntMul.HvdH.Ref

/-- the index function of a list index -/
def ixf (l : List ℕ) : ℕ → ℕ := fun i => l.getD i 0

/-- The cyclic convolution on the box with sides `s`, arrays as row-major lists. -/
def cconv (s : List ℕ) (u v : List ℤ) (j : ℕ → ℕ) : ℤ :=
  ((boxIdxs s).map fun l => u.getD (rmPos s (ixf l)) 0 *
    v.getD (rmPos s (fun i => (j i + s.getD i 1 - l.getD i 0) % s.getD i 1)) 0).sum

end IntMul.HvdH.RefPf

end

-- ===== Solutions.HvdH.Ref.SSAlg
section

/-! Algebra of the Schönhage–Strassen transforms over `ℤ/(2^n+1)` (copied from the machine
thread's `NLogN.SSAlg`, stated for the copies in `IntMul.HvdH.Ref`). -/

namespace IntMul.HvdH.RefPf
open IntMul.HvdH IntMul.HvdH.Ref

theorem length_bflyT (F : ℤ) : ∀ (A B : List ℤ), A.length = B.length →
    (bflyT F A B).length = A.length
  | [], [], _ => rfl
  | u :: A, v :: B, h => by
    simp only [bflyT, List.length_cons, add_left_inj] at h ⊢; exact length_bflyT F A B h
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem length_bflyB (F : ℤ) (E : ℕ) : ∀ (j : ℕ) (A B : List ℤ), A.length = B.length →
    (bflyB F E j A B).length = A.length
  | _, [], [], _ => rfl
  | j, u :: A, v :: B, h => by
    simp only [bflyB, List.length_cons, add_left_inj] at h ⊢; exact length_bflyB F E (j + 1) A B h
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h

/-! ## The butterfly step -/

theorem length_dcomX (F : ℤ) (n E : ℕ) : ∀ (i : ℕ) (A B : List ℤ), A.length = B.length →
    (dcomX F n E i A B).length = A.length
  | _, [], [], _ => rfl
  | i, u :: A, v :: B, h => by
    simp only [dcomX, List.length_cons, add_left_inj] at h ⊢; exact length_dcomX F n E (i + 1) A B h
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h

theorem length_dcomY (F : ℤ) (n E : ℕ) : ∀ (i : ℕ) (A B : List ℤ), A.length = B.length →
    (dcomY F n E i A B).length = A.length
  | _, [], [], _ => rfl
  | i, u :: A, v :: B, h => by
    simp only [dcomY, List.length_cons, add_left_inj] at h ⊢; exact length_dcomY F n E (i + 1) A B h
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h

theorem length_ditZ (F : ℤ) (n : ℕ) : ∀ (j E : ℕ) (B : List ℤ), B.length = 2 ^ j →
    (ditZ F n E j B).length = 2 ^ j
  | 0, E, B, h => by simpa [ditZ] using h
  | j + 1, E, B, h => by
    have h1 : (B.take (2 ^ j)).length = 2 ^ j := by
      rw [List.length_take, h, pow_succ]; omega
    have h2 : (B.drop (2 ^ j)).length = 2 ^ j := by
      rw [List.length_drop, h, pow_succ]; omega
    have e1 := length_ditZ F n j (2 * E) _ h1
    have e2 := length_ditZ F n j (2 * E) _ h2
    simp only [ditZ, List.length_append]
    rw [length_dcomX _ _ _ _ _ _ (by rw [e1, e2]), length_dcomY _ _ _ _ _ _ (by rw [e1, e2]), e1,
      pow_succ]
    ring

theorem length_difZ (F : ℤ) : ∀ (j E : ℕ) (A : List ℤ), A.length = 2 ^ j →
    (difZ F E j A).length = 2 ^ j
  | 0, E, A, h => by simpa [difZ] using h
  | j + 1, E, A, h => by
    have h1 : (A.take (2 ^ j)).length = 2 ^ j := by
      rw [List.length_take, h, pow_succ]; omega
    have h2 : (A.drop (2 ^ j)).length = 2 ^ j := by
      rw [List.length_drop, h, pow_succ]; omega
    have e1 := length_difZ F j (2 * E) _
      (by rw [length_bflyT F (A.take (2 ^ j)) (A.drop (2 ^ j)) (by rw [h1, h2]), h1])
    have e2 := length_difZ F j (2 * E) _
      (by rw [length_bflyB F E 0 (A.take (2 ^ j)) (A.drop (2 ^ j)) (by rw [h1, h2]), h1])
    simp only [difZ, List.length_append]
    rw [e1, e2, pow_succ]; ring

section ring

variable (n : ℕ)

theorem cast_emod (a : ℤ) : (((a % (2 ^ n + 1) : ℤ)) : (ZMod (2 ^ n + 1))) = (a : (ZMod (2 ^ n + 1))) := by
  have := ZMod.intCast_mod a (2 ^ n + 1); push_cast at this; exact this

theorem two_pow_eq_neg_one : (2 : (ZMod (2 ^ n + 1))) ^ n = -1 := by
  have : ((2 ^ n + 1 : ℕ) : (ZMod (2 ^ n + 1))) = 0 := ZMod.natCast_self _
  push_cast at this
  exact eq_neg_of_add_eq_zero_left this

/-- One level of the inverse butterflies undoes one level of the forward butterflies. -/
theorem dcom_inv (E : ℕ) (c : (ZMod (2 ^ n + 1))) : ∀ (i : ℕ) (lo hi T Bt : List ℤ), lo.length = hi.length →
    (i + lo.length) * E ≤ n →
    T.map (Int.cast : ℤ → (ZMod (2 ^ n + 1))) = (bflyT (2 ^ n + 1) lo hi).map (fun a : ℤ => c * (a : (ZMod (2 ^ n + 1)))) →
    Bt.map (Int.cast : ℤ → (ZMod (2 ^ n + 1))) = (bflyB (2 ^ n + 1) E i lo hi).map (fun a : ℤ => c * (a : (ZMod (2 ^ n + 1)))) →
    (dcomX (2 ^ n + 1) n E i T Bt).map (Int.cast : ℤ → (ZMod (2 ^ n + 1))) = lo.map (fun a : ℤ => 2 * c * (a : (ZMod (2 ^ n + 1)))) ∧
    (dcomY (2 ^ n + 1) n E i T Bt).map (Int.cast : ℤ → (ZMod (2 ^ n + 1))) = hi.map (fun a : ℤ => 2 * c * (a : (ZMod (2 ^ n + 1))))
  | i, u :: lo, v :: hi, t :: T, b :: Bt, hl, hE, hT, hB => by
    simp only [bflyT, bflyB, List.map_cons, List.cons.injEq] at hT hB
    simp only [List.length_cons, add_left_inj] at hl
    obtain ⟨ih1, ih2⟩ := dcom_inv E c (i + 1) lo hi T Bt hl (by simp at hE; linarith) hT.2 hB.2
    simp only [dcomX, dcomY, List.map_cons, ih1, ih2, and_true]
    have hiE : i * E + (n - i * E) = n := by
      have : i * E ≤ n := le_trans (Nat.mul_le_mul_right _ (by simp)) hE
      omega
    have h2 : (2 : (ZMod (2 ^ n + 1))) ^ (i * E) * 2 ^ (n - i * E) = -1 := by
      rw [← pow_add, hiE, two_pow_eq_neg_one]
    have ht := hT.1; have hb := hB.1
    simp only [cast_emod] at ht hb
    push_cast at ht hb
    simp only [cast_emod]
    push_cast
    simp only [cast_emod]
    push_cast
    rw [ht, hb]
    simp only [List.cons.injEq, and_true]
    constructor
    · linear_combination (-(c * (-(v : (ZMod (2 ^ n + 1))) + u))) * h2
    · linear_combination (c * (-(v : (ZMod (2 ^ n + 1))) + u)) * h2
  | i, [], [], T, Bt, _, _, hT, hB => by
    simp [bflyT, bflyB] at hT hB; subst hT; subst hB; simp [dcomX, dcomY]
  | i, u :: lo, v :: hi, [], _, _, _, hT, _ => by simp [bflyT] at hT
  | i, u :: lo, v :: hi, _ :: _, [], _, _, _, hB => by simp [bflyB] at hB
  | _, [], _ :: _, _, _, hl, _, _, _ => by simp at hl
  | _, _ :: _, [], _, _, hl, _, _, _ => by simp at hl

/-- The inverse transform inverts the forward transform up to the factor `2^j`. -/
theorem dit_dif : ∀ (j E : ℕ) (A : List ℤ), A.length = 2 ^ j → (j = 0 ∨ 2 ^ j * E = 2 * n) →
    (ditZ (2 ^ n + 1) n E j (difZ (2 ^ n + 1) E j A)).map (Int.cast : ℤ → (ZMod (2 ^ n + 1))) =
      A.map (fun a : ℤ => (2 : (ZMod (2 ^ n + 1))) ^ j * (a : (ZMod (2 ^ n + 1))))
  | 0, E, A, _, _ => by simp [ditZ, difZ]
  | j + 1, E, A, hA, hjE => by
    have hjE' : 2 ^ j * E = n := by
      rcases hjE with h | h
      · omega
      · rw [pow_succ] at h; linarith
    set lo := A.take (2 ^ j) with hlo
    set hi := A.drop (2 ^ j) with hhi
    have hlol : lo.length = 2 ^ j := by rw [List.length_take, hA, pow_succ]; omega
    have hhil : hi.length = 2 ^ j := by rw [List.length_drop, hA, pow_succ]; omega
    set tops := bflyT (2 ^ n + 1) lo hi
    set bots := bflyB (2 ^ n + 1) E 0 lo hi
    have htl : tops.length = 2 ^ j := by rw [length_bflyT _ _ _ (by rw [hlol, hhil]), hlol]
    have hbl : bots.length = 2 ^ j := by rw [length_bflyB _ _ _ _ _ (by rw [hlol, hhil]), hlol]
    have hd1 := length_difZ (2 ^ n + 1) j (2 * E) tops htl
    have hjE2 : j = 0 ∨ 2 ^ j * (2 * E) = 2 * n := by right; rw [← hjE']; ring
    have ih1 := dit_dif j (2 * E) tops htl hjE2
    have ih2 := dit_dif j (2 * E) bots hbl hjE2
    have e1 : difZ (2 ^ n + 1) E (j + 1) A =
        difZ (2 ^ n + 1) (2 * E) j tops ++ difZ (2 ^ n + 1) (2 * E) j bots := by
      simp only [difZ, tops, bots, lo, hi]
    rw [e1]
    simp only [ditZ]
    rw [List.take_left' hd1, List.drop_left' hd1]
    obtain ⟨r1, r2⟩ := dcom_inv n E ((2 : (ZMod (2 ^ n + 1))) ^ j) 0 lo hi _ _ (by rw [hlol, hhil])
      (by rw [hlol, zero_add, hjE']) (by rw [ih1])
      (by rw [ih2])
    rw [List.map_append, r1, r2, ← List.map_append, List.take_append_drop]
    congr 1; funext a; ring

/-! ## The forward transform evaluates at roots of unity -/

/-- `∑_{i<m} A_i x^i`. -/
def peval (A : List ℤ) (x : (ZMod (2 ^ n + 1))) (m : ℕ) : (ZMod (2 ^ n + 1)) := ∑ i ∈ Finset.range m, (A.getD i 0 : (ZMod (2 ^ n + 1))) * x ^ i

end ring

theorem getD_take (A : List ℤ) {h i : ℕ} (hi : i < h) : (A.take h).getD i 0 = A.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi]

theorem getD_drop (A : List ℤ) (h i : ℕ) : (A.drop h).getD i 0 = A.getD (h + i) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_append_left (A B : List ℤ) {r : ℕ} (hr : r < A.length) :
    (A ++ B).getD r 0 = A.getD r 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hr]

theorem getD_append_right (A B : List ℤ) {r : ℕ} (hr : A.length ≤ r) :
    (A ++ B).getD r 0 = B.getD (r - A.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hr]

theorem bflyT_getD (F : ℤ) : ∀ (A B : List ℤ) (i : ℕ), i < A.length → A.length = B.length →
    (bflyT F A B).getD i 0 = (B.getD i 0 + A.getD i 0) % F
  | u :: A, v :: B, 0, _, _ => by simp [bflyT]
  | u :: A, v :: B, i + 1, hi, hl => by
    simp only [bflyT, List.getD_cons_succ]
    exact bflyT_getD F A B i (by simpa using hi) (by simpa using hl)
  | [], _, _, hi, _ => by simp at hi
  | _ :: _, [], _, _, hl => by simp at hl

theorem bflyB_getD (F : ℤ) (E : ℕ) : ∀ (j : ℕ) (A B : List ℤ) (i : ℕ), i < A.length →
    A.length = B.length →
    (bflyB F E j A B).getD i 0 = ((-B.getD i 0 + A.getD i 0) * 2 ^ ((j + i) * E)) % F
  | j, u :: A, v :: B, 0, _, _ => by simp [bflyB]
  | j, u :: A, v :: B, i + 1, hi, hl => by
    simp only [bflyB, List.getD_cons_succ]
    rw [bflyB_getD F E (j + 1) A B i (by simpa using hi) (by simpa using hl)]
    congr 3; ring
  | _, [], _, _, hi, _ => by simp at hi
  | _, _ :: _, [], _, _, hl => by simp at hl

section ring2

variable (n : ℕ)

theorem difZ_eval : ∀ (j E : ℕ), (j = 0 ∨ 2 ^ j * E = 2 * n) → ∀ r < 2 ^ j, ∃ x : (ZMod (2 ^ n + 1)),
    x ^ (2 ^ j) = 1 ∧ ∀ A : List ℤ, A.length = 2 ^ j →
      (((difZ (2 ^ n + 1) E j A).getD r 0 : ℤ) : (ZMod (2 ^ n + 1))) = peval n A x (2 ^ j)
  | 0, E, _, r, hr => by
    refine ⟨1, by simp, fun A _ => ?_⟩
    have : r = 0 := by simpa using hr
    subst this
    simp [difZ, peval]
  | j + 1, E, hjE, r, hr => by
    have hjE' : 2 ^ j * E = n := by
      rcases hjE with h | h
      · omega
      · rw [pow_succ] at h; linarith
    have hjE2 : j = 0 ∨ 2 ^ j * (2 * E) = 2 * n := by right; rw [← hjE']; ring
    have hpow : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [pow_succ]; ring
    -- common facts about the halves
    have key : ∀ A : List ℤ, A.length = 2 ^ (j + 1) →
        (A.take (2 ^ j)).length = 2 ^ j ∧ (A.drop (2 ^ j)).length = 2 ^ j := by
      intro A hA
      exact ⟨by rw [List.length_take, hA, pow_succ]; omega,
        by rw [List.length_drop, hA, pow_succ]; omega⟩
    have split : ∀ (A : List ℤ) (x : (ZMod (2 ^ n + 1))), peval n A x (2 ^ (j + 1)) =
        ∑ i ∈ Finset.range (2 ^ j), ((A.getD i 0 : (ZMod (2 ^ n + 1))) * x ^ i +
          (A.getD (2 ^ j + i) 0 : (ZMod (2 ^ n + 1))) * x ^ (2 ^ j) * x ^ i) := by
      intro A x
      rw [peval, hpow, Finset.sum_range_add, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_add]; ring
    rcases lt_or_ge r (2 ^ j) with hr1 | hr1
    · obtain ⟨x, hx, hev⟩ := difZ_eval j (2 * E) hjE2 r hr1
      refine ⟨x, by rw [pow_succ, pow_mul, hx, one_pow], fun A hA => ?_⟩
      obtain ⟨h1, h2⟩ := key A hA
      have htl := length_bflyT (2 ^ n + 1) _ _ (h1.trans h2.symm)
      have hd := length_difZ (2 ^ n + 1) j (2 * E) _ (htl.trans h1)
      simp only [difZ]
      rw [getD_append_left _ _ (by rw [hd]; exact hr1), hev _ (htl.trans h1), split, peval]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i < 2 ^ j := Finset.mem_range.mp hi
      rw [bflyT_getD _ _ _ i (by rw [h1]; exact hi') (h1.trans h2.symm), cast_emod, getD_take _ hi',
        getD_drop, hx]
      push_cast; ring
    · obtain ⟨x', hx', hev⟩ := difZ_eval j (2 * E) hjE2 (r - 2 ^ j) (by rw [hpow] at hr; omega)
      have hxh : ((2 : (ZMod (2 ^ n + 1))) ^ E * x') ^ (2 ^ j) = -1 := by
        rw [mul_pow, hx', mul_one, ← pow_mul, mul_comm, hjE', two_pow_eq_neg_one]
      refine ⟨(2 : (ZMod (2 ^ n + 1))) ^ E * x', by rw [pow_succ, pow_mul, hxh]; norm_num, fun A hA => ?_⟩
      obtain ⟨h1, h2⟩ := key A hA
      have htl := length_bflyT (2 ^ n + 1) _ _ (h1.trans h2.symm)
      have hbl := length_bflyB (2 ^ n + 1) E 0 _ _ (h1.trans h2.symm)
      have hd := length_difZ (2 ^ n + 1) j (2 * E) _ (htl.trans h1)
      simp only [difZ]
      rw [getD_append_right _ _ (by rw [hd]; exact hr1), hd, hev _ (hbl.trans h1), split, peval]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i < 2 ^ j := Finset.mem_range.mp hi
      rw [bflyB_getD _ _ _ _ _ i (by rw [h1]; exact hi') (h1.trans h2.symm), cast_emod,
        getD_take _ hi', getD_drop, hxh]
      push_cast
      rw [zero_add, pow_mul, mul_pow]
      ring

end ring2

/-! ## Cyclic convolution and pointwise products -/

theorem length_pmulZ (F : ℤ) : ∀ (A B : List ℤ), A.length = B.length →
    (pmulZ F A B).length = A.length
  | [], [], _ => rfl
  | a :: A, b :: B, h => by
    simp only [pmulZ, List.length_cons, add_left_inj] at h ⊢; exact length_pmulZ F A B h
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem pmulZ_getD (F : ℤ) : ∀ (A B : List ℤ) (i : ℕ), i < A.length → A.length = B.length →
    (pmulZ F A B).getD i 0 = (A.getD i 0 * B.getD i 0) % F
  | a :: A, b :: B, 0, _, _ => by simp [pmulZ]
  | a :: A, b :: B, i + 1, hi, hl => by
    simp only [pmulZ, List.getD_cons_succ]
    exact pmulZ_getD F A B i (by simpa using hi) (by simpa using hl)
  | [], _, _, hi, _ => by simp at hi
  | _ :: _, [], _, _, hl => by simp at hl

section ring3

variable (n : ℕ)

end ring3

end IntMul.HvdH.RefPf

end

-- ===== Solutions.HvdH.Ref.ListBox
section

/-! General lemmas about `boxIdxs`, `listOf`, `rmPos`. -/

namespace IntMul.HvdH.RefPf
open IntMul.HvdH IntMul.HvdH.Ref

theorem sum_map_range_finset {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

theorem length_flatMap_range_const {α : Type*} (n P : ℕ) (g : ℕ → List α)
    (hg : ∀ i < n, (g i).length = P) : ((List.range n).flatMap g).length = n * P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih (fun i hi => hg i (by omega))]
    simp [hg n (by omega)]
    ring

theorem length_boxIdxs (dims : List ℕ) : (boxIdxs dims).length = dims.prod := by
  induction dims with
  | nil => rfl
  | cons n ns ih =>
    rw [boxIdxs, length_flatMap_range_const n ns.prod _ (fun i _ => by simp [ih])]
    simp

theorem length_listOf {α : Type*} (dims : List ℕ) (f : (ℕ → ℕ) → α) :
    (listOf dims f).length = dims.prod := by
  simp [listOf, length_boxIdxs]

theorem mem_boxIdxs {dims l : List ℕ} :
    l ∈ boxIdxs dims ↔ l.length = dims.length ∧ ∀ i < l.length, l.getD i 0 < dims.getD i 1 := by
  induction dims generalizing l with
  | nil => cases l <;> simp [boxIdxs]
  | cons n ns ih =>
    cases l with
    | nil => simp [boxIdxs]
    | cons a l =>
      simp only [boxIdxs, List.mem_flatMap, List.mem_range, List.mem_map, ih]
      constructor
      · rintro ⟨i, hi, l', ⟨hl1, hl2⟩, he⟩
        obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.1 he
        refine ⟨by simp [hl1], ?_⟩
        intro j hj
        cases j with
        | zero => simpa using hi
        | succ j => simpa using hl2 j (by simpa using hj)
      · rintro ⟨h1, h2⟩
        exact ⟨a, by simpa using h2 0 (by simp), l,
          ⟨by simpa using h1, fun j hj => by simpa using h2 (j + 1) (by simpa using hj)⟩, rfl⟩

theorem nodup_boxIdxs (dims : List ℕ) : (boxIdxs dims).Nodup := by
  induction dims with
  | nil => simp [boxIdxs]
  | cons n ns ih =>
    rw [boxIdxs, List.nodup_flatMap]
    refine ⟨fun i _ => ih.map (fun a b h => List.cons_injective h), ?_⟩
    refine (List.pairwise_lt_range (n := n)).imp ?_
    intro i j hij x hx1 hx2
    simp only [List.mem_map] at hx1 hx2
    obtain ⟨a, _, rfl⟩ := hx1
    obtain ⟨b, _, hb⟩ := hx2
    have := (List.cons_eq_cons.1 hb).1
    omega

theorem getElem?_flatMap_const {α : Type*} (n P : ℕ) (g : ℕ → List α)
    (hg : ∀ i < n, (g i).length = P) (i r : ℕ) (hi : i < n) (hr : r < P) :
    ((List.range n).flatMap g)[i * P + r]? = (g i)[r]? := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hlen := length_flatMap_range_const n P g (fun i hi => hg i (by omega))
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · have : i * P + r < n * P := by
        have : (i + 1) * P ≤ n * P := Nat.mul_le_mul_right _ h
        nlinarith
      rw [List.getElem?_append_left (by rw [hlen]; exact this)]
      exact ih (fun i hi => hg i (by omega)) h
    · subst h
      rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]
      simp

theorem getElem?_rmPos {dims l : List ℕ} (hl : l ∈ boxIdxs dims) :
    (boxIdxs dims)[rmPos dims (ixf l)]? = some l := by
  induction dims generalizing l with
  | nil =>
    simp [boxIdxs] at hl
    subst hl
    simp [rmPos, boxIdxs]
  | cons n ns ih =>
    have hl0 := hl
    simp only [boxIdxs, List.mem_flatMap, List.mem_range, List.mem_map] at hl0
    obtain ⟨i, hi, l', hl', rfl⟩ := hl0
    have h1 : rmPos (n :: ns) (ixf (i :: l')) = i * ns.prod + rmPos ns (ixf l') := by
      simp only [rmPos]
      rfl
    have hr : rmPos ns (ixf l') < ns.prod := by
      have := ih hl'
      rw [List.getElem?_eq_some_iff] at this
      obtain ⟨h, _⟩ := this
      rwa [length_boxIdxs] at h
    rw [h1, boxIdxs,
      getElem?_flatMap_const n ns.prod _ (fun _ _ => by simp [length_boxIdxs]) i _ hi hr,
      List.getElem?_map, ih hl']
    rfl

theorem rmPos_lt {dims l : List ℕ} (hl : l ∈ boxIdxs dims) : rmPos dims (ixf l) < dims.prod := by
  have := getElem?_rmPos hl
  rw [List.getElem?_eq_some_iff] at this
  obtain ⟨h, _⟩ := this
  rwa [length_boxIdxs] at h

theorem getD_listOf {α : Type*} (dims : List ℕ) (f : (ℕ → ℕ) → α) (d : α) {l : List ℕ}
    (hl : l ∈ boxIdxs dims) : (listOf dims f).getD (rmPos dims (ixf l)) d = f (ixf l) := by
  rw [listOf, List.getD_eq_getElem?_getD, List.getElem?_map, getElem?_rmPos hl]
  rfl

/-- An explicit box index. -/
theorem map_range_mem_boxIdxs (s : List ℕ) (g : ℕ → ℕ) (hg : ∀ i < s.length, g i < s.getD i 1) :
    (List.range s.length).map g ∈ boxIdxs s := by
  rw [mem_boxIdxs]
  refine ⟨by simp, fun i hi => ?_⟩
  simp only [List.length_map, List.length_range] at hi
  simpa [List.getD_eq_getElem?_getD, hi] using hg i hi

theorem ixf_map_range (K : ℕ) (g : ℕ → ℕ) (hg : ∀ i, K ≤ i → g i = 0) :
    ixf ((List.range K).map g) = g := by
  funext i
  by_cases hi : i < K
  · simp [ixf, List.getD_eq_getElem?_getD, hi]
  · simp [ixf, List.getD_eq_getElem?_getD, hi, hg i (by omega)]

theorem getD_mem_or {α : Type*} (c : List α) (n : ℕ) (d : α) : c.getD n d ∈ c ∨ c.getD n d = d := by
  by_cases h : n < c.length
  · left; rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
  · right; exact List.getD_eq_default _ _ (by omega)

end IntMul.HvdH.RefPf

end

-- ===== Solutions.HvdH.Ref.MDif
section

/-! Multi-axis Fermat-ring transforms `mdif` / `mdit`: list bookkeeping. -/

namespace IntMul.HvdH.RefPf
open IntMul.HvdH IntMul.HvdH.Ref

section lists
variable {α : Type*}

lemma chunkL_eq (n m : ℕ) (hn : 0 < n) (L : List α) (hL : L.length = m * n) :
    chunkL n L = (List.range m).map fun i => (L.drop (i * n)).take n := by
  unfold chunkL
  have : (L.length + n - 1) / n = m := by
    rw [hL, show m * n + n - 1 = (n - 1) + n * m by rw [mul_comm]; omega,
      Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt (by omega), zero_add]
  rw [this]

lemma flatten_getD_uniform (n : ℕ) (d : α) : ∀ (rows : List (List α)),
    (∀ row ∈ rows, row.length = n) → ∀ c < rows.length, ∀ a < n,
    rows.flatten.getD (c * n + a) d = (rows.getD c []).getD a d
  | [], _, c, hc, _, _ => by simp at hc
  | row :: rows, h, c, hc, a, ha => by
    have hrow : row.length = n := h row (by simp)
    rcases c with _ | c
    · simp only [List.flatten_cons, zero_mul, zero_add, List.getD_cons_zero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD]
    · simp only [List.flatten_cons, List.getD_cons_succ]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hrow]; nlinarith),
        ← List.getD_eq_getElem?_getD, hrow]
      have : (c + 1) * n + a - n = c * n + a := by rw [add_mul, one_mul]; omega
      rw [this]
      exact flatten_getD_uniform n d rows (fun r hr => h r (by simp [hr])) c
        (by simp at hc; omega) a ha

lemma length_flatten_uniform (n : ℕ) : ∀ (rows : List (List α)),
    (∀ row ∈ rows, row.length = n) → rows.flatten.length = rows.length * n
  | [], _ => by simp
  | row :: rows, h => by
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [h row (by simp), length_flatten_uniform n rows (fun r hr => h r (by simp [hr]))]
    ring

lemma chunkL_flatten (n : ℕ) (hn : 0 < n) (rows : List (List α))
    (h : ∀ row ∈ rows, row.length = n) : chunkL n rows.flatten = rows := by
  rw [chunkL_eq n rows.length hn _ (length_flatten_uniform n rows h)]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  have hr := h (rows[i]) (List.getElem_mem _)
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, length_flatten_uniform n rows h, hr]
    have : i < rows.length := h2
    have : i * n + n ≤ rows.length * n := by nlinarith
    omega
  intro a ha1 ha2
  have ha : a < n := by rw [hr] at ha2; exact ha2
  simp only [List.getElem_take, List.getElem_drop]
  have hlt : i * n + a < rows.flatten.length := by
    rw [length_flatten_uniform n rows h]; nlinarith
  obtain ⟨d⟩ : Nonempty α := ⟨rows[i][a]'(by rw [hr]; exact ha)⟩
  have := flatten_getD_uniform n d rows h i h2 a ha
  rw [List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ h2,
    List.getD_eq_getElem _ _ (by rw [hr]; exact ha)] at this
  exact this

lemma transposeL_length [Inhabited α] (n m : ℕ) (L : List α) : (transposeL n m L).length = m * n := by
  simp [transposeL]

lemma transposeL_getD [Inhabited α] (n m : ℕ) (L : List α) (q : ℕ) (hq : q < m * n) :
    (transposeL n m L).getD q default = L.getD ((q % n) * m + q / n) default := by
  rw [List.getD_eq_getElem _ _ (by rw [transposeL_length]; exact hq)]
  simp [transposeL]

end lists

/-- column `c` of a `2^j × B` row-major array -/
def colL (j B : ℕ) (A : List ℤ) (c : ℕ) : List ℤ :=
  (List.range (2 ^ j)).map fun a => A.getD (a * B + c) 0

lemma colL_length (j B : ℕ) (A : List ℤ) (c : ℕ) : (colL j B A c).length = 2 ^ j := by simp [colL]

lemma colL_getD (j B : ℕ) (A : List ℤ) (c a : ℕ) (ha : a < 2 ^ j) :
    (colL j B A c).getD a 0 = A.getD (a * B + c) 0 := by
  rw [List.getD_eq_getElem _ _ (by rw [colL_length]; exact ha)]; simp [colL]

lemma colMap_length (j B : ℕ) (f : List ℤ → List ℤ) (A : List ℤ) :
    (colMap j B f A).length = 2 ^ j * B := by
  simp [colMap, transposeL_length]

lemma colMap_rows (j B : ℕ) (A : List ℤ) :
    chunkL (2 ^ j) (transposeL (2 ^ j) B A) = (List.range B).map (colL j B A) := by
  rw [chunkL_eq (2 ^ j) B (by positivity) _ (by rw [transposeL_length])]
  apply List.ext_getElem (by simp)
  intro c h1 h2
  simp only [List.getElem_map, List.getElem_range]
  have hc : c < B := by simpa using h2
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, transposeL_length, colL_length]
    have : c * 2 ^ j + 2 ^ j ≤ B * 2 ^ j := by
      have := Nat.mul_le_mul_right (2 ^ j) (show c + 1 ≤ B by omega); rw [add_mul, one_mul] at this
      exact this
    omega
  intro a ha1 ha2
  have ha : a < 2 ^ j := by rw [colL_length] at ha2; exact ha2
  simp only [List.getElem_take, List.getElem_drop]
  have hlt : c * 2 ^ j + a < B * 2 ^ j := by nlinarith
  have e1 := transposeL_getD (2 ^ j) B A (c * 2 ^ j + a) hlt
  rw [List.getD_eq_getElem _ _ (by rw [transposeL_length]; exact hlt)] at e1
  rw [e1, ← List.getD_eq_getElem _ _ ha2, colL_getD _ _ _ _ _ ha]
  have hpos : 0 < 2 ^ j := by positivity
  rw [show (c * 2 ^ j + a) % 2 ^ j = a by rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt ha,
    show (c * 2 ^ j + a) / 2 ^ j = c by
      rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt ha]; simp]
  rfl

lemma colMap_getD (j B : ℕ) (f : List ℤ → List ℤ) (hf : ∀ X : List ℤ, X.length = 2 ^ j → (f X).length = 2 ^ j)
    (A : List ℤ) (a c : ℕ) (ha : a < 2 ^ j) (hc : c < B) :
    (colMap j B f A).getD (a * B + c) 0 = (f (colL j B A c)).getD a 0 := by
  unfold colMap
  rw [colMap_rows, List.flatMap_def]
  have hrows : ∀ row ∈ ((List.range B).map (colL j B A)).map f, row.length = 2 ^ j := by
    intro row hrow
    simp only [List.map_map, List.mem_map, List.mem_range, Function.comp] at hrow
    obtain ⟨c', _, rfl⟩ := hrow
    exact hf _ (colL_length _ _ _ _)
  have hlt : a * B + c < 2 ^ j * B := by nlinarith
  have := transposeL_getD B (2 ^ j) (((List.range B).map (colL j B A)).map f).flatten (a * B + c) hlt
  rw [show (default : ℤ) = 0 from rfl] at this
  rw [this]
  have hB : 0 < B := by omega
  rw [show (a * B + c) % B = c by rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hc,
    show (a * B + c) / B = a by
      rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hc]; simp]
  rw [flatten_getD_uniform (2 ^ j) 0 _ hrows c (by simpa using hc) a ha]
  congr 1
  rw [List.getD_eq_getElem?_getD]
  simp [hc]

/-! ## Boxes -/

def dimsOf (ax : List (ℕ × ℕ)) : List ℕ := ax.map fun p => 2 ^ p.1

lemma blockSize_cons (j E : ℕ) (rest : List (ℕ × ℕ)) :
    blockSize ((j, E) :: rest) = 2 ^ j * blockSize rest := by
  simp [blockSize, pow_add]

lemma blockSize_eq (ax : List (ℕ × ℕ)) : blockSize ax = (dimsOf ax).prod := by
  induction ax with
  | nil => simp [blockSize, dimsOf]
  | cons p rest ih =>
    obtain ⟨j, E⟩ := p
    rw [blockSize_cons, ih]; simp [dimsOf]

lemma blockSize_pos (ax : List (ℕ × ℕ)) : 0 < blockSize ax := by simp [blockSize]

lemma ixf_cons_zero (b : ℕ) (l : List ℕ) : ixf (b :: l) 0 = b := rfl

lemma ixf_cons_succ (b : ℕ) (l : List ℕ) : (fun i => ixf (b :: l) (i + 1)) = ixf l := by
  funext i; simp [ixf]

lemma rmPos_cons (n : ℕ) (ns : List ℕ) (b : ℕ) (l : List ℕ) :
    rmPos (n :: ns) (ixf (b :: l)) = b * ns.prod + rmPos ns (ixf l) := by
  simp only [rmPos, ixf_cons_zero, ixf_cons_succ]

lemma mem_boxIdxs_cons (n : ℕ) (ns : List ℕ) (l : List ℕ) :
    l ∈ boxIdxs (n :: ns) ↔ ∃ b < n, ∃ l' ∈ boxIdxs ns, l = b :: l' := by
  simp only [boxIdxs, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨b, hb, l', hl', rfl⟩; exact ⟨b, hb, l', hl', rfl⟩
  · rintro ⟨b, hb, l', hl', rfl⟩; exact ⟨b, hb, l', hl', rfl⟩

lemma list_sum_range {M : Type*} [AddCommMonoid M] (n : ℕ) (h : ℕ → M) :
    ((List.range n).map h).sum = ∑ b ∈ Finset.range n, h b := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

lemma list_sum_finset_comm {M ι : Type*} [AddCommMonoid M] (L : List ι) (S : Finset ℕ)
    (f : ℕ → ι → M) : (L.map fun l => ∑ b ∈ S, f b l).sum = ∑ b ∈ S, (L.map fun l => f b l).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, Finset.sum_add_distrib]

lemma sum_boxIdxs_cons {M : Type*} [AddCommMonoid M] (n : ℕ) (ns : List ℕ) (g : List ℕ → M) :
    ((boxIdxs (n :: ns)).map g).sum = ∑ b ∈ Finset.range n, ((boxIdxs ns).map fun l => g (b :: l)).sum := by
  simp only [boxIdxs, List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map,
    Function.comp_def]
  exact list_sum_range n (fun b => ((boxIdxs ns).map fun l => g (b :: l)).sum)

/-! ## Rows of the first-axis transform -/

lemma colMap_chunk (j B : ℕ) (hB : 0 < B) (f : List ℤ → List ℤ)
    (hf : ∀ X : List ℤ, X.length = 2 ^ j → (f X).length = 2 ^ j) (A : List ℤ) :
    chunkL B (colMap j B f A) =
      (List.range (2 ^ j)).map fun a => (List.range B).map fun c => (f (colL j B A c)).getD a 0 := by
  rw [chunkL_eq B (2 ^ j) hB _ (colMap_length _ _ _ _)]
  apply List.ext_getElem (by simp)
  intro a h1 h2
  have ha : a < 2 ^ j := by simpa using h2
  simp only [List.getElem_map, List.getElem_range]
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, colMap_length, List.length_map, List.length_range]
    have : a * B + B ≤ 2 ^ j * B := by
      have := Nat.mul_le_mul_right B (show a + 1 ≤ 2 ^ j by omega); rw [add_mul, one_mul] at this
      exact this
    omega
  intro c hc1 hc2
  have hc : c < B := by simpa using hc2
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
  have hlt : a * B + c < (colMap j B f A).length := by
    rw [colMap_length]
    have : a * B + B ≤ 2 ^ j * B := by
      have := Nat.mul_le_mul_right B (show a + 1 ≤ 2 ^ j by omega); rw [add_mul, one_mul] at this
      exact this
    omega
  rw [← colMap_getD j B f hf A a c ha hc, List.getD_eq_getElem _ _ hlt]

/-- row `a` of the first-axis transform of `A` -/
def rowA (F : ℤ) (j E B : ℕ) (A : List ℤ) (a : ℕ) : List ℤ :=
  (List.range B).map fun c => (difZ F E j (colL j B A c)).getD a 0

lemma length_mdif (F : ℤ) : ∀ (ax : List (ℕ × ℕ)) (A : List ℤ), A.length = blockSize ax →
    (mdif F ax A).length = blockSize ax
  | [], A, h => by simpa [mdif] using h
  | (j, E) :: rest, A, h => by
    rw [mdif, colMap_chunk j _ (blockSize_pos rest) _ (fun X hX => length_difZ F j E X hX),
      List.flatMap_def, length_flatten_uniform (blockSize rest), blockSize_cons]
    · simp
    · intro row hrow
      simp only [List.map_map, List.mem_map, List.mem_range, Function.comp] at hrow
      obtain ⟨a, _, rfl⟩ := hrow
      exact length_mdif F rest _ (by simp)

lemma mdif_getD (F : ℤ) (j E : ℕ) (rest : List (ℕ × ℕ)) (A : List ℤ) (a p : ℕ) (ha : a < 2 ^ j)
    (hp : p < blockSize rest) :
    (mdif F ((j, E) :: rest) A).getD (a * blockSize rest + p) 0 =
      (mdif F rest (rowA F j E (blockSize rest) A a)).getD p 0 := by
  rw [mdif, colMap_chunk j _ (blockSize_pos rest) _ (fun X hX => length_difZ F j E X hX),
    List.flatMap_def]
  have hrows : ∀ row ∈ ((List.range (2 ^ j)).map fun a => (List.range (blockSize rest)).map
      fun c => (difZ F E j (colL j (blockSize rest) A c)).getD a 0).map (mdif F rest),
      row.length = blockSize rest := by
    intro row hrow
    simp only [List.map_map, List.mem_map, List.mem_range, Function.comp] at hrow
    obtain ⟨a, _, rfl⟩ := hrow
    exact length_mdif F rest _ (by simp)
  rw [flatten_getD_uniform _ 0 _ hrows a (by simpa using ha) p hp]
  congr 1
  rw [List.getD_eq_getElem?_getD]
  simp [ha, rowA]

/-- digitwise addition on a box -/
def addB : List ℕ → List ℕ → List ℕ → List ℕ
  | n :: ns, a :: l1, b :: l2 => ((a + b) % n) :: addB ns l1 l2
  | _, _, _ => []

section eval
variable (n : ℕ)

/-- The multi-axis transform evaluates at a character of the box. -/
theorem mdif_eval : ∀ (ax : List (ℕ × ℕ)), (∀ p ∈ ax, p.1 = 0 ∨ 2 ^ p.1 * p.2 = 2 * n) →
    ∀ pos < blockSize ax, ∃ φ : List ℕ → (ZMod (2 ^ n + 1)),
      (∀ l1 ∈ boxIdxs (dimsOf ax), ∀ l2 ∈ boxIdxs (dimsOf ax),
        φ (addB (dimsOf ax) l1 l2) = φ l1 * φ l2) ∧
      ∀ A : List ℤ, A.length = blockSize ax →
        (((mdif (2 ^ n + 1) ax A).getD pos 0 : ℤ) : (ZMod (2 ^ n + 1))) =
          ((boxIdxs (dimsOf ax)).map fun l => ((A.getD (rmPos (dimsOf ax) (ixf l)) 0 : ℤ) : (ZMod (2 ^ n + 1))) * φ l).sum
  | [], _, pos, hpos => by
    refine ⟨fun _ => 1, fun _ _ _ _ => by simp, fun A hA => ?_⟩
    have : pos = 0 := by simpa [blockSize] using hpos
    subst this
    simp [mdif, boxIdxs, dimsOf, rmPos]
  | (j, E) :: rest, hax, pos, hpos => by
    set B := blockSize rest with hB
    have hB0 : 0 < B := blockSize_pos rest
    have hjE : j = 0 ∨ 2 ^ j * E = 2 * n := hax (j, E) (by simp)
    have hrest : ∀ p ∈ rest, p.1 = 0 ∨ 2 ^ p.1 * p.2 = 2 * n := fun p hp => hax p (by simp [hp])
    rw [blockSize_cons] at hpos
    have ha : pos / B < 2 ^ j := by
      rw [Nat.div_lt_iff_lt_mul hB0]; linarith
    have hp : pos % B < B := Nat.mod_lt _ hB0
    obtain ⟨x, hx, hev⟩ := difZ_eval n j E hjE (pos / B) ha
    obtain ⟨φ', hφ'c, hφ'⟩ := mdif_eval rest hrest (pos % B) hp
    refine ⟨fun l => match l with
      | [] => 1
      | b :: l' => x ^ b * φ' l', ?_, ?_⟩
    · intro l1 h1 l2 h2
      obtain ⟨a1, ha1, l1', hl1', rfl⟩ := (mem_boxIdxs_cons _ _ _).1 h1
      obtain ⟨a2, ha2, l2', hl2', rfl⟩ := (mem_boxIdxs_cons _ _ _).1 h2
      simp only [dimsOf, List.map_cons, addB]
      rw [show (rest.map fun p => 2 ^ p.1) = dimsOf rest from rfl, hφ'c l1' hl1' l2' hl2']
      have : x ^ ((a1 + a2) % 2 ^ j) = x ^ a1 * x ^ a2 := by
        rw [← pow_add]
        conv_rhs => rw [← Nat.div_add_mod (a1 + a2) (2 ^ j), pow_add, pow_mul, hx, one_pow, one_mul]
      rw [this]; ring
    · intro A hA
      have hpos' : pos = pos / B * B + pos % B := (Nat.div_add_mod' pos B).symm
      rw [hpos', mdif_getD _ j E rest A _ _ ha hp]
      have hrowlen : (rowA (2 ^ n + 1) j E B A (pos / B)).length = B := by simp [rowA]
      rw [hφ' _ hrowlen]
      simp only [dimsOf, List.map_cons]
      rw [show (rest.map fun p => 2 ^ p.1) = dimsOf rest from rfl, sum_boxIdxs_cons]
      have hBd : B = (dimsOf rest).prod := by rw [hB, blockSize_eq]
      -- expand the row entries
      have hrow : ∀ l' ∈ boxIdxs (dimsOf rest),
          (((rowA (2 ^ n + 1) j E B A (pos / B)).getD (rmPos (dimsOf rest) (ixf l')) 0 : ℤ) : (ZMod (2 ^ n + 1))) =
            ∑ b ∈ Finset.range (2 ^ j), ((A.getD (b * B + rmPos (dimsOf rest) (ixf l')) 0 : ℤ) : (ZMod (2 ^ n + 1))) * x ^ b := by
        intro l' hl'
        have hlt : rmPos (dimsOf rest) (ixf l') < B := by rw [hBd]; exact rmPos_lt hl'
        have : (rowA (2 ^ n + 1) j E B A (pos / B)).getD (rmPos (dimsOf rest) (ixf l')) 0 =
            (difZ (2 ^ n + 1) E j (colL j B A (rmPos (dimsOf rest) (ixf l')))).getD (pos / B) 0 := by
          rw [List.getD_eq_getElem?_getD]; simp [rowA, hlt]
        rw [this, hev _ (colL_length _ _ _ _), peval]
        apply Finset.sum_congr rfl
        intro b hb
        rw [colL_getD _ _ _ _ _ (Finset.mem_range.1 hb)]
      rw [List.map_congr_left (l := boxIdxs (dimsOf rest))
        (g := fun l' => (∑ b ∈ Finset.range (2 ^ j),
          ((A.getD (b * B + rmPos (dimsOf rest) (ixf l')) 0 : ℤ) : (ZMod (2 ^ n + 1))) * x ^ b) * φ' l')
        (fun l' hl' => by rw [hrow l' hl'])]
      simp only [Finset.sum_mul]
      rw [list_sum_finset_comm]
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      apply List.map_congr_left
      intro l' _
      rw [rmPos_cons, ← hBd]
      ring

end eval

/-- digitwise difference on a box -/
def subL : List ℕ → List ℕ → List ℕ → List ℕ
  | n :: ns, a :: l1, b :: l2 => ((a + n - b) % n) :: subL ns l1 l2
  | _, _, _ => []

lemma list_sum_comm {M ι κ : Type*} [AddCommMonoid M] (L : List ι) (L' : List κ) (f : ι → κ → M) :
    (L.map fun l => (L'.map fun l' => f l l').sum).sum =
      (L'.map fun l' => (L.map fun l => f l l').sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [← List.sum_map_add]

lemma sum_range_shift {M : Type*} [AddCommMonoid M] (n b : ℕ) (hb : b < n) (h : ℕ → M) :
    ∑ a ∈ Finset.range n, h ((a + n - b) % n) = ∑ a ∈ Finset.range n, h a := by
  apply Finset.sum_nbij' (fun a => (a + n - b) % n) (fun c => (c + b) % n)
  · intro a _; try simp only [Finset.mem_coe, Finset.mem_range, Finset.coe_range, Set.mem_Iio]; exact Nat.mod_lt _ (by omega)
  · intro a _; try simp only [Finset.mem_coe, Finset.mem_range, Finset.coe_range, Set.mem_Iio]; exact Nat.mod_lt _ (by omega)
  · intro a ha
    try simp only [Finset.mem_range, Finset.coe_range, Set.mem_Iio] at *; try simp only [Finset.mem_coe, Finset.mem_range] at *
    rw [Nat.mod_add_mod, show a + n - b + b = a + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
  · intro c hc
    try simp only [Finset.mem_range, Finset.coe_range, Set.mem_Iio] at *; try simp only [Finset.mem_coe, Finset.mem_range] at *
    have h1 : (c + b) % n + n - b ≡ c [MOD n] := by
      have : ((c + b) % n + n - b) + b = (c + b) % n + n := by
        have := Nat.mod_lt (c + b) (show 0 < n by omega); omega
      apply Nat.ModEq.add_right_cancel' b
      rw [this]
      calc (c + b) % n + n ≡ (c + b) % n [MOD n] := Nat.add_modEq_right
        _ ≡ c + b [MOD n] := Nat.mod_modEq _ _
    rw [h1, Nat.mod_eq_of_lt hc]
  · intro a _; rfl

lemma subL_mem : ∀ (dims l l1 : List ℕ), l ∈ boxIdxs dims → l1 ∈ boxIdxs dims →
    subL dims l l1 ∈ boxIdxs dims
  | [], l, l1, h, _ => by simp [boxIdxs] at h ⊢; subst h; simp [subL]
  | n :: ns, l, l1, h, h1 => by
    obtain ⟨a, ha, l', hl', rfl⟩ := (mem_boxIdxs_cons n ns l).1 h
    obtain ⟨b, hb, l1', hl1', rfl⟩ := (mem_boxIdxs_cons n ns l1).1 h1
    rw [subL, mem_boxIdxs_cons]
    exact ⟨_, Nat.mod_lt _ (by omega), _, subL_mem ns l' l1' hl' hl1', rfl⟩

lemma sum_subL {M : Type*} [AddCommMonoid M] : ∀ (dims l1 : List ℕ), l1 ∈ boxIdxs dims →
    ∀ g : List ℕ → M,
    ((boxIdxs dims).map fun l => g (subL dims l l1)).sum = ((boxIdxs dims).map g).sum
  | [], l1, h, g => by simp [boxIdxs] at h ⊢; subst h; simp [subL]
  | n :: ns, l1, h, g => by
    obtain ⟨b, hb, l1', hl1', rfl⟩ := (mem_boxIdxs_cons n ns l1).1 h
    rw [sum_boxIdxs_cons, sum_boxIdxs_cons]
    simp only [subL]
    rw [Finset.sum_congr rfl (fun a _ => sum_subL ns l1' hl1' (fun l => g (((a + n - b) % n) :: l)))]
    exact sum_range_shift n b hb (fun a => ((boxIdxs ns).map fun l => g (a :: l)).sum)

lemma addB_subL : ∀ (dims l l1 : List ℕ), l ∈ boxIdxs dims → l1 ∈ boxIdxs dims →
    addB dims l1 (subL dims l l1) = l
  | [], l, l1, h, _ => by simp [boxIdxs] at h; subst h; simp [addB]
  | n :: ns, l, l1, h, h1 => by
    obtain ⟨a, ha, l', hl', rfl⟩ := (mem_boxIdxs_cons n ns l).1 h
    obtain ⟨b, hb, l1', hl1', rfl⟩ := (mem_boxIdxs_cons n ns l1).1 h1
    simp only [subL, addB, addB_subL ns l' l1' hl' hl1', List.cons.injEq, and_true]
    rw [Nat.add_mod_mod, show b + (a + n - b) = a + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt ha]

lemma ixf_subL : ∀ (dims l l1 : List ℕ), l ∈ boxIdxs dims → l1 ∈ boxIdxs dims →
    ixf (subL dims l l1) = fun i => (ixf l i + dims.getD i 1 - ixf l1 i) % dims.getD i 1
  | [], l, l1, h, h1 => by
    simp [boxIdxs] at h h1; subst h; subst h1; funext i; simp [subL, ixf]
  | n :: ns, l, l1, h, h1 => by
    obtain ⟨a, ha, l', hl', rfl⟩ := (mem_boxIdxs_cons n ns l).1 h
    obtain ⟨b, hb, l1', hl1', rfl⟩ := (mem_boxIdxs_cons n ns l1).1 h1
    funext i
    rcases i with _ | i
    · simp [subL, ixf]
    · have := congrFun (ixf_subL ns l' l1' hl' hl1') i
      simp only [subL] at this ⊢
      simpa [ixf] using this

section evc
variable (n : ℕ)

/-- evaluation of a box array at a weight function -/
def evB (dims : List ℕ) (φ : List ℕ → (ZMod (2 ^ n + 1))) (A : List ℤ) : (ZMod (2 ^ n + 1)) :=
  ((boxIdxs dims).map fun l => ((A.getD (rmPos dims (ixf l)) 0 : ℤ) : (ZMod (2 ^ n + 1))) * φ l).sum

theorem evB_cconv (dims : List ℕ) (φ : List ℕ → (ZMod (2 ^ n + 1)))
    (hφ : ∀ l1 ∈ boxIdxs dims, ∀ l2 ∈ boxIdxs dims, φ (addB dims l1 l2) = φ l1 * φ l2)
    (a b : List ℤ) :
    evB n dims φ (listOf dims (cconv dims a b)) = evB n dims φ a * evB n dims φ b := by
  unfold evB
  rw [List.map_congr_left (fun l hl => by rw [getD_listOf dims _ 0 hl])]
  simp only [cconv]
  -- expand
  have step1 : ∀ l ∈ boxIdxs dims, ((((boxIdxs dims).map fun l1 => a.getD (rmPos dims (ixf l1)) 0 *
      b.getD (rmPos dims (fun i => (ixf l i + dims.getD i 1 - l1.getD i 0) % dims.getD i 1)) 0).sum : ℤ) : (ZMod (2 ^ n + 1)))
        * φ l =
      ((boxIdxs dims).map fun l1 => ((a.getD (rmPos dims (ixf l1)) 0 : ℤ) : (ZMod (2 ^ n + 1))) * φ l1 *
        (((b.getD (rmPos dims (ixf (subL dims l l1))) 0 : ℤ) : (ZMod (2 ^ n + 1))) * φ (subL dims l l1))).sum := by
    intro l hl
    rw [Int.cast_list_sum, List.map_map, ← List.sum_map_mul_right]
    congr 1
    apply List.map_congr_left
    intro l1 hl1
    simp only [Function.comp]
    rw [ixf_subL dims l l1 hl hl1]
    have := hφ l1 hl1 _ (subL_mem dims l l1 hl hl1)
    rw [addB_subL dims l l1 hl hl1] at this
    rw [this]; push_cast; simp only [ixf]; ring
  rw [List.map_congr_left step1, list_sum_comm, ← List.sum_map_mul_right]
  congr 1
  apply List.map_congr_left
  intro l1 hl1
  rw [← List.sum_map_mul_left]
  exact sum_subL dims l1 hl1 (fun l2 => (((a.getD (rmPos dims (ixf l1)) 0 : ℤ) : (ZMod (2 ^ n + 1))) * φ l1) *
    (((b.getD (rmPos dims (ixf l2)) 0 : ℤ) : (ZMod (2 ^ n + 1))) * φ l2))

end evc

lemma flatten_chunkL {α : Type*} (n m : ℕ) (hn : 0 < n) (L : List α) (hL : L.length = m * n) :
    (chunkL n L).flatten = L := by
  rw [chunkL_eq n m hn L hL]
  have hrows : ∀ row ∈ (List.range m).map (fun i => (L.drop (i * n)).take n), row.length = n := by
    intro row hrow
    simp only [List.mem_map, List.mem_range] at hrow
    obtain ⟨i, hi, rfl⟩ := hrow
    simp only [List.length_take, List.length_drop, hL]
    have : i * n + n ≤ m * n := by
      have := Nat.mul_le_mul_right n (show i + 1 ≤ m by omega); rw [add_mul, one_mul] at this
      exact this
    omega
  apply List.ext_getElem
  · rw [length_flatten_uniform n _ hrows]; simp [hL]
  intro q h1 h2
  obtain ⟨d⟩ : Nonempty α := ⟨L[q]⟩
  have hq : q = q / n * n + q % n := (Nat.div_add_mod' q n).symm
  have hqm : q / n < m := by rw [Nat.div_lt_iff_lt_mul hn]; rw [← hL]; exact h2
  have := flatten_getD_uniform n d _ hrows (q / n) (by simpa using hqm) (q % n) (Nat.mod_lt _ hn)
  rw [← hq, List.getD_eq_getElem _ _ h1] at this
  have hr : ((List.range m).map fun i => (L.drop (i * n)).take n).getD (q / n) [] =
      (L.drop (q / n * n)).take n := by
    rw [List.getD_eq_getElem?_getD]; simp [hqm]
  rw [this, hr, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (Nat.mod_lt _ hn), List.getElem?_drop,
    ← hq, List.getElem?_eq_getElem h2]
  rfl

section rel
variable (n : ℕ)

/-- `X ≡ c · Y` entrywise in `ℤ/(2^n+1)` -/
def RelC (c : (ZMod (2 ^ n + 1))) (X Y : List ℤ) : Prop :=
  X.map (Int.cast : ℤ → (ZMod (2 ^ n + 1))) = Y.map fun y : ℤ => c * (y : (ZMod (2 ^ n + 1)))

lemma relC_iff (c : (ZMod (2 ^ n + 1))) (X Y : List ℤ) : RelC n c X Y ↔
    X.length = Y.length ∧ ∀ k, ((X.getD k 0 : ℤ) : (ZMod (2 ^ n + 1))) = c * ((Y.getD k 0 : ℤ) : (ZMod (2 ^ n + 1))) := by
  unfold RelC
  constructor
  · intro h
    have hl : X.length = Y.length := by simpa using congrArg List.length h
    refine ⟨hl, fun k => ?_⟩
    by_cases hk : k < X.length
    · have := congrArg (fun L => L.getD k 0) h
      rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ (by simpa [hl] using hk)]
        at this
      simp only [List.getElem_map] at this
      rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ (by omega)]
      exact this
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]; simp
  · rintro ⟨hl, h⟩
    apply List.ext_getElem (by simp [hl])
    intro k h1 h2
    simp only [List.getElem_map]
    have := h k
    rw [List.getD_eq_getElem _ _ (by simpa using h1), List.getD_eq_getElem _ _ (by simpa using h2)] at this
    exact this

lemma relC_trans (c1 c2 : (ZMod (2 ^ n + 1))) (P Q S : List ℤ) (h1 : RelC n c1 P Q) (h2 : RelC n c2 Q S) :
    RelC n (c1 * c2) P S := by
  unfold RelC at *
  have : P.map (Int.cast : ℤ → (ZMod (2 ^ n + 1))) = (Q.map (Int.cast : ℤ → (ZMod (2 ^ n + 1)))).map (fun y => c1 * y) := by
    rw [h1, List.map_map]; rfl
  rw [this, h2, List.map_map]
  congr 1; funext y; simp [Function.comp]; ring

lemma relC_append (c : (ZMod (2 ^ n + 1))) (A B A' B' : List ℤ) (hA : RelC n c A A') (hB : RelC n c B B') :
    RelC n c (A ++ B) (A' ++ B') := by
  unfold RelC at *; simp [hA, hB]

lemma dcomX_rel (c : (ZMod (2 ^ n + 1))) (E : ℕ) : ∀ (i : ℕ) (T B T' B' : List ℤ), RelC n c T T' → RelC n c B B' →
    RelC n c (dcomX (2 ^ n + 1) n E i T B) (dcomX (2 ^ n + 1) n E i T' B')
  | i, t :: T, b :: B, t' :: T', b' :: B', hT, hB => by
    unfold RelC at *
    simp only [List.map_cons, List.cons.injEq] at hT hB
    simp only [dcomX, List.map_cons, List.cons.injEq]
    refine ⟨?_, dcomX_rel c E (i + 1) T B T' B' hT.2 hB.2⟩
    simp only [cast_emod, Int.cast_add, Int.cast_neg, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    rw [hT.1, hB.1]; ring
  | i, [], B, T', B', hT, hB => by
    unfold RelC at *; simp at hT; subst hT; simp [dcomX]
  | i, _ :: _, [], T', B', hT, hB => by
    unfold RelC at *; simp at hB; subst hB
    cases T' <;> simp [dcomX]
  | i, _ :: _, _ :: _, [], B', hT, hB => by unfold RelC at hT; simp at hT
  | i, _ :: _, _ :: _, _ :: _, [], hT, hB => by unfold RelC at hB; simp at hB

lemma dcomY_rel (c : (ZMod (2 ^ n + 1))) (E : ℕ) : ∀ (i : ℕ) (T B T' B' : List ℤ), RelC n c T T' → RelC n c B B' →
    RelC n c (dcomY (2 ^ n + 1) n E i T B) (dcomY (2 ^ n + 1) n E i T' B')
  | i, t :: T, b :: B, t' :: T', b' :: B', hT, hB => by
    unfold RelC at *
    simp only [List.map_cons, List.cons.injEq] at hT hB
    simp only [dcomY, List.map_cons, List.cons.injEq]
    refine ⟨?_, dcomY_rel c E (i + 1) T B T' B' hT.2 hB.2⟩
    simp only [cast_emod, Int.cast_add, Int.cast_neg, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    rw [hT.1, hB.1]; ring
  | i, [], B, T', B', hT, hB => by
    unfold RelC at *; simp at hT; subst hT; simp [dcomY]
  | i, _ :: _, [], T', B', hT, hB => by
    unfold RelC at *; simp at hB; subst hB
    cases T' <;> simp [dcomY]
  | i, _ :: _, _ :: _, [], B', hT, hB => by unfold RelC at hT; simp at hT
  | i, _ :: _, _ :: _, _ :: _, [], hT, hB => by unfold RelC at hB; simp at hB

lemma ditZ_rel (c : (ZMod (2 ^ n + 1))) : ∀ (j E : ℕ) (X X' : List ℤ), RelC n c X X' →
    RelC n c (ditZ (2 ^ n + 1) n E j X) (ditZ (2 ^ n + 1) n E j X')
  | 0, E, X, X', h => by simpa [ditZ] using h
  | j + 1, E, X, X', h => by
    have ht : RelC n c (X.take (2 ^ j)) (X'.take (2 ^ j)) := by
      unfold RelC at *; rw [List.map_take, List.map_take, h]
    have hd : RelC n c (X.drop (2 ^ j)) (X'.drop (2 ^ j)) := by
      unfold RelC at *; rw [List.map_drop, List.map_drop, h]
    have h1 := ditZ_rel c j (2 * E) _ _ ht
    have h2 := ditZ_rel c j (2 * E) _ _ hd
    simp only [ditZ]
    exact relC_append n c _ _ _ _ (dcomX_rel n c E 0 _ _ _ _ h1 h2) (dcomY_rel n c E 0 _ _ _ _ h1 h2)

lemma colL_rel (c : (ZMod (2 ^ n + 1))) (j B : ℕ) (A A' : List ℤ) (h : RelC n c A A') (k : ℕ) :
    RelC n c (colL j B A k) (colL j B A' k) := by
  rw [relC_iff] at h ⊢
  refine ⟨by simp [colL_length], fun a => ?_⟩
  by_cases ha : a < 2 ^ j
  · rw [colL_getD _ _ _ _ _ ha, colL_getD _ _ _ _ _ ha]; exact h.2 _
  · rw [List.getD_eq_default _ _ (by rw [colL_length]; omega),
      List.getD_eq_default _ _ (by rw [colL_length]; omega)]; simp

lemma colMap_rel (c : (ZMod (2 ^ n + 1))) (j B : ℕ) (f : List ℤ → List ℤ)
    (hf : ∀ X : List ℤ, X.length = 2 ^ j → (f X).length = 2 ^ j)
    (hfr : ∀ X X' : List ℤ, RelC n c X X' → RelC n c (f X) (f X'))
    (A A' : List ℤ) (h : RelC n c A A') : RelC n c (colMap j B f A) (colMap j B f A') := by
  rw [relC_iff]
  refine ⟨by simp [colMap_length], fun q => ?_⟩
  by_cases hq : q < 2 ^ j * B
  · have hB : 0 < B := by
      rcases Nat.eq_zero_or_pos B with h0 | h0
      · subst h0; simp at hq
      · exact h0
    have hq' : q = q / B * B + q % B := (Nat.div_add_mod' q B).symm
    have ha : q / B < 2 ^ j := by rw [Nat.div_lt_iff_lt_mul hB]; exact hq
    rw [hq', colMap_getD j B f hf A _ _ ha (Nat.mod_lt _ hB), colMap_getD j B f hf A' _ _ ha (Nat.mod_lt _ hB)]
    exact ((relC_iff n c _ _).1 (hfr _ _ (colL_rel n c j B A A' h _))).2 _
  · rw [List.getD_eq_default _ _ (by rw [colMap_length]; omega),
      List.getD_eq_default _ _ (by rw [colMap_length]; omega)]; simp

lemma flatMap_rel (c : (ZMod (2 ^ n + 1))) : ∀ (I : List ℕ) (f f' : ℕ → List ℤ), (∀ i ∈ I, RelC n c (f i) (f' i)) →
    RelC n c (I.flatMap f) (I.flatMap f')
  | [], f, f', _ => by unfold RelC; simp
  | i :: I, f, f', h => by
    simp only [List.flatMap_cons]
    exact relC_append n c _ _ _ _ (h i (by simp)) (flatMap_rel c I f f' (fun k hk => h k (by simp [hk])))

lemma chunk_flatMap_rel (c : (ZMod (2 ^ n + 1))) (B : ℕ) (g : List ℤ → List ℤ)
    (hg : ∀ X X' : List ℤ, RelC n c X X' → RelC n c (g X) (g X'))
    (X X' : List ℤ) (h : RelC n c X X') :
    RelC n c ((chunkL B X).flatMap g) ((chunkL B X').flatMap g) := by
  have hl : X.length = X'.length := ((relC_iff n c X X').1 h).1
  unfold chunkL
  rw [hl, List.flatMap_map, List.flatMap_map]
  apply flatMap_rel
  intro i _
  apply hg
  unfold RelC at *
  rw [List.map_take, List.map_drop, List.map_take, List.map_drop, h]

lemma mdit_rel (c : (ZMod (2 ^ n + 1))) : ∀ (ax : List (ℕ × ℕ)) (X X' : List ℤ), RelC n c X X' →
    RelC n c (mdit (2 ^ n + 1) n ax X) (mdit (2 ^ n + 1) n ax X')
  | [], X, X', h => by simpa [mdit] using h
  | (j, E) :: rest, X, X', h => by
    simp only [mdit]
    apply colMap_rel n c j _ _ (fun Y hY => length_ditZ _ n j E Y hY) (fun Y Y' hY => ditZ_rel n c j E Y Y' hY)
    exact chunk_flatMap_rel n c _ _ (fun Y Y' hY => mdit_rel c rest Y Y' hY) X X' h

lemma colMap_dit_dif (j E : ℕ) (hjE : j = 0 ∨ 2 ^ j * E = 2 * n) (B : ℕ) (X : List ℤ)
    (hX : X.length = 2 ^ j * B) :
    RelC n (2 ^ j) (colMap j B (ditZ (2 ^ n + 1) n E j) (colMap j B (difZ (2 ^ n + 1) E j) X)) X := by
  rw [relC_iff]
  refine ⟨by rw [colMap_length, hX], fun q => ?_⟩
  by_cases hq : q < 2 ^ j * B
  · have hB : 0 < B := by
      rcases Nat.eq_zero_or_pos B with h0 | h0
      · subst h0; simp at hq
      · exact h0
    have hq' : q = q / B * B + q % B := (Nat.div_add_mod' q B).symm
    have ha : q / B < 2 ^ j := by rw [Nat.div_lt_iff_lt_mul hB]; exact hq
    have hc : q % B < B := Nat.mod_lt _ hB
    rw [hq', colMap_getD j B _ (fun Y hY => length_ditZ _ n j E Y hY) _ _ _ ha hc]
    have hcol : colL j B (colMap j B (difZ (2 ^ n + 1) E j) X) (q % B) =
        difZ (2 ^ n + 1) E j (colL j B X (q % B)) := by
      apply List.ext_getElem
      · rw [colL_length, length_difZ _ j E _ (colL_length _ _ _ _)]
      intro a h1 h2
      rw [colL_length] at h1
      rw [← List.getD_eq_getElem _ 0 (by rw [colL_length]; exact h1), ← List.getD_eq_getElem _ 0 h2,
        colL_getD _ _ _ _ _ h1, colMap_getD j B _ (fun Y hY => length_difZ _ j E Y hY) _ _ _ h1 hc]
    rw [hcol]
    have := dit_dif n j E (colL j B X (q % B)) (colL_length j B X (q % B)) hjE
    have h2 := ((relC_iff n (2 ^ j) _ _).1 this).2 (q / B)
    rw [h2, colL_getD _ _ _ _ _ ha]
  · rw [List.getD_eq_default _ _ (by rw [colMap_length]; omega),
      List.getD_eq_default _ _ (by omega)]; simp

def sumJ (ax : List (ℕ × ℕ)) : ℕ := (ax.map Prod.fst).sum

theorem mdit_mdif : ∀ (ax : List (ℕ × ℕ)), (∀ p ∈ ax, p.1 = 0 ∨ 2 ^ p.1 * p.2 = 2 * n) →
    ∀ X : List ℤ, X.length = blockSize ax →
    RelC n (2 ^ sumJ ax) (mdit (2 ^ n + 1) n ax (mdif (2 ^ n + 1) ax X)) X
  | [], _, X, _ => by unfold RelC; simp [mdit, mdif, sumJ]
  | (j, E) :: rest, hax, X, hX => by
    have hjE : j = 0 ∨ 2 ^ j * E = 2 * n := hax (j, E) (by simp)
    have hrest : ∀ p ∈ rest, p.1 = 0 ∨ 2 ^ p.1 * p.2 = 2 * n := fun p hp => hax p (by simp [hp])
    set B := blockSize rest
    have hB0 : 0 < B := blockSize_pos rest
    set Y := colMap j B (difZ (2 ^ n + 1) E j) X with hY
    have hYl : Y.length = 2 ^ j * B := colMap_length _ _ _ _
    rw [blockSize_cons] at hX
    have hrows : ∀ row ∈ chunkL B Y, row.length = B := by
      rw [chunkL_eq B (2 ^ j) hB0 Y hYl]
      intro row hrow
      simp only [List.mem_map, List.mem_range] at hrow
      obtain ⟨i, hi, rfl⟩ := hrow
      simp only [List.length_take, List.length_drop, hYl]
      have : i * B + B ≤ 2 ^ j * B := by
        have := Nat.mul_le_mul_right B (show i + 1 ≤ 2 ^ j by omega); rw [add_mul, one_mul] at this
        exact this
      omega
    have hmd : ∀ row ∈ (chunkL B Y).map (mdif (2 ^ n + 1) rest), row.length = B := by
      intro row hrow
      simp only [List.mem_map] at hrow
      obtain ⟨r, hr, rfl⟩ := hrow
      exact length_mdif _ rest r (hrows r hr)
    have e1 : mdif (2 ^ n + 1) ((j, E) :: rest) X = ((chunkL B Y).map (mdif (2 ^ n + 1) rest)).flatten := by
      simp only [mdif, List.flatMap_def]; rfl
    rw [e1]
    simp only [mdit]
    rw [chunkL_flatten B hB0 _ hmd, List.flatMap_map]
    have hZ : RelC n (2 ^ sumJ rest) ((chunkL B Y).flatMap fun r => mdit (2 ^ n + 1) n rest
        (mdif (2 ^ n + 1) rest r)) Y := by
      have : Y = (chunkL B Y).flatMap id := by
        rw [List.flatMap_id, flatten_chunkL B (2 ^ j) hB0 Y hYl]
      conv_rhs => rw [this]
      unfold chunkL
      rw [List.flatMap_map, List.flatMap_map]
      apply flatMap_rel
      intro i hi
      apply mdit_mdif rest hrest
      have := hrows _ (by
        unfold chunkL; exact List.mem_map.2 ⟨i, hi, rfl⟩)
      exact this
    have h1 := colMap_rel n _ j B _ (fun Z hZ => length_ditZ _ n j E Z hZ)
      (fun Z Z' hZZ => ditZ_rel n _ j E Z Z' hZZ) _ _ hZ
    have h2 := colMap_dit_dif n j E hjE B X hX
    have := relC_trans n _ _ _ _ _ h1 h2
    rw [show sumJ ((j, E) :: rest) = sumJ rest + j by simp [sumJ]; ring, pow_add]
    exact this

end rel

section main
variable (n : ℕ)

theorem pmul_mdif (ax : List (ℕ × ℕ)) (hax : ∀ p ∈ ax, p.1 = 0 ∨ 2 ^ p.1 * p.2 = 2 * n)
    (A B : List ℤ) (hA : A.length = blockSize ax) (hB : B.length = blockSize ax) :
    RelC n 1 (pmulZ (2 ^ n + 1) (mdif (2 ^ n + 1) ax A) (mdif (2 ^ n + 1) ax B))
      (mdif (2 ^ n + 1) ax (listOf (dimsOf ax) (cconv (dimsOf ax) A B))) := by
  have hZ : (listOf (dimsOf ax) (cconv (dimsOf ax) A B)).length = blockSize ax := by
    rw [length_listOf, blockSize_eq]
  have lA := length_mdif (2 ^ n + 1) ax A hA
  have lB := length_mdif (2 ^ n + 1) ax B hB
  have lZ := length_mdif (2 ^ n + 1) ax _ hZ
  have lP := length_pmulZ (2 ^ n + 1) _ _ (lA.trans lB.symm)
  rw [relC_iff]
  refine ⟨by rw [lP, lA, lZ], fun pos => ?_⟩
  by_cases hpos : pos < blockSize ax
  · obtain ⟨φ, hφ, hev⟩ := mdif_eval n ax hax pos hpos
    rw [pmulZ_getD _ _ _ pos (by rw [lA]; exact hpos) (lA.trans lB.symm), cast_emod]
    push_cast
    rw [hev A hA, hev B hB, hev _ hZ, one_mul]
    exact (evB_cconv n (dimsOf ax) φ hφ A B).symm
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]; simp

/-- **Multi-axis convolution theorem**: the inverse transform of the pointwise product of the
transforms is `2^{Σ jᵢ}` times the cyclic convolution on the box. -/
theorem mdit_pmul_mdif (ax : List (ℕ × ℕ)) (hax : ∀ p ∈ ax, p.1 = 0 ∨ 2 ^ p.1 * p.2 = 2 * n)
    (A B : List ℤ) (hA : A.length = blockSize ax) (hB : B.length = blockSize ax) :
    RelC n (2 ^ sumJ ax)
      (mdit (2 ^ n + 1) n ax (pmulZ (2 ^ n + 1) (mdif (2 ^ n + 1) ax A) (mdif (2 ^ n + 1) ax B)))
      (listOf (dimsOf ax) (cconv (dimsOf ax) A B)) := by
  have hZ : (listOf (dimsOf ax) (cconv (dimsOf ax) A B)).length = blockSize ax := by
    rw [length_listOf, blockSize_eq]
  have h1 := mdit_rel n 1 ax _ _ (pmul_mdif n ax hax A B hA hB)
  have h2 := mdit_mdif n ax hax _ hZ
  have := relC_trans n _ _ _ _ _ h1 h2
  rwa [one_mul] at this

end main

end IntMul.HvdH.RefPf

end

-- ===== Solutions.HvdH.KronMul
section

open Finset

namespace IntMul.HvdH.KronPf
open IntMul.HvdH

lemma kpack_eq_sum (B : ℤ) (c : List ℤ) :
    kpack B c = ∑ i ∈ range c.length, c.getD i 0 * B ^ i := by
  induction c with
  | nil => simp [kpack]
  | cons a cs ih =>
    rw [kpack, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]; congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_); ring

lemma sum_abs_getD_le (a : List ℤ) (M : ℤ) (ha : ∀ x ∈ a, |x| ≤ M) (N : ℕ) :
    ∑ i ∈ range N, |a.getD i 0| ≤ a.length * M := by
  have hz : ∀ i ∈ range N, i ∉ range N ∩ range a.length → |a.getD i 0| = 0 := by
    intro i hi hni
    have : a.length ≤ i := by
      by_contra h; exact hni (Finset.mem_inter.2 ⟨hi, Finset.mem_range.2 (by omega)⟩)
    rw [List.getD_eq_default _ _ this, abs_zero]
  rw [← Finset.sum_subset Finset.inter_subset_left hz]
  calc ∑ i ∈ range N ∩ range a.length, |a.getD i 0| ≤ ∑ i ∈ range a.length, |a.getD i 0| :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          (fun i _ _ => abs_nonneg _)
    _ ≤ ∑ _i ∈ range a.length, M := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        rw [List.getD_eq_getElem _ _ (Finset.mem_range.1 hi)]
        exact ha _ (List.getElem_mem _)
    _ = a.length * M := by simp

lemma polyMul_coeff_bound (a b : List ℤ) (M : ℤ) (hM0 : 0 ≤ M) (ha : ∀ x ∈ a, |x| ≤ M)
    (hb : ∀ x ∈ b, |x| ≤ M) : ∀ x ∈ polyMul a b, |x| ≤ a.length * M * M := by
  intro x hx
  unfold polyMul at hx
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  have hM : ∀ j, |b.getD j 0| ≤ M := by
    intro j
    by_cases hj : j < b.length
    · rw [List.getD_eq_getElem _ _ hj]; exact hb _ (List.getElem_mem _)
    · push Not at hj
      rw [List.getD_eq_default _ _ hj, abs_zero]
      exact hM0
  calc |∑ i ∈ range (k + 1), a.getD i 0 * b.getD (k - i) 0|
      ≤ ∑ i ∈ range (k + 1), |a.getD i 0 * b.getD (k - i) 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range (k + 1), |a.getD i 0| * M := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
    _ = (∑ i ∈ range (k + 1), |a.getD i 0|) * M := by rw [Finset.sum_mul]
    _ ≤ a.length * M * M := by
        exact mul_le_mul_of_nonneg_right (sum_abs_getD_le a M ha _) hM0

lemma polyMul_length (a b : List ℤ) : (polyMul a b).length = a.length + b.length - 1 := by
  simp [polyMul]

end IntMul.HvdH.KronPf

end

-- ===== Solutions.HvdH.Fermat
section

open Finset

namespace IntMul.HvdH.FermPf
open IntMul.HvdH IntMul.HvdH.KronPf

lemma kpack_abs (B : ℤ) (hB : 0 < B) (c : List ℤ) (hc : ∀ x ∈ c, 2 * |x| < B) :
    2 * |kpack B c| ≤ B ^ c.length - 1 := by
  induction c with
  | nil => simp [kpack]
  | cons a cs ih =>
    have ha : 2 * |a| < B := hc a (by simp)
    have ih' := ih (fun x hx => hc x (by simp [hx]))
    simp only [kpack, List.length_cons]
    calc 2 * |a + B * kpack B cs| ≤ 2 * |a| + B * (2 * |kpack B cs|) := by
          have := abs_add_le a (B * kpack B cs)
          rw [abs_mul, abs_of_pos hB] at this; linarith
      _ ≤ (B - 1) + B * (B ^ cs.length - 1) := by gcongr; omega
      _ = B ^ (cs.length + 1) - 1 := by ring

lemma balMod_eq (F x y : ℤ) (hF : 0 < F) (hodd : Odd F) (hxy : x % F = y % F)
    (hy : 2 * |y| < F) : balMod F x = y := by
  unfold balMod
  have hc0 : 0 ≤ x % F := Int.emod_nonneg _ hF.ne'
  have hc1 : x % F < F := Int.emod_lt_of_pos _ hF
  have hy' := abs_lt.1 (show |y| < F by linarith [abs_nonneg y])
  have hd : F ∣ x % F - y := by
    rw [hxy, Int.emod_def]; exact ⟨-(y / F), by ring⟩
  obtain ⟨k, hk⟩ := hodd
  dsimp only
  split_ifs with h
  · have hd' : F ∣ (x % F - F) - y := by
      rw [show x % F - F - y = (x % F - y) - F by ring]; exact dvd_sub hd dvd_rfl
    have := Int.eq_zero_of_abs_lt_dvd hd' (by
      rw [abs_lt]; constructor
      · have := le_abs_self y; have := neg_abs_le y; omega
      · have := le_abs_self y; have := neg_abs_le y; omega)
    linarith
  · have := Int.eq_zero_of_abs_lt_dvd hd (by
      rw [abs_lt]; constructor
      · have := le_abs_self y; have := neg_abs_le y; omega
      · have := le_abs_self y; have := neg_abs_le y; omega)
    linarith

end IntMul.HvdH.FermPf

end

-- ===== Solutions.HvdH.FermConv
section

open Finset

namespace IntMul.HvdH.FCPf
open IntMul.HvdH IntMul.HvdH.KronPf IntMul.HvdH.FermPf

lemma polyMul_getD_all (a b : List ℤ) (c : ℕ) :
    (polyMul a b).getD c 0 = ∑ i ∈ range (c + 1), a.getD i 0 * b.getD (c - i) 0 := by
  by_cases hc : c < (polyMul a b).length
  · rw [List.getD_eq_getElem _ _ hc]
    simp [polyMul]
  · rw [List.getD_eq_default _ _ (by omega)]
    rw [polyMul_length] at hc
    symm
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.1 hi
    by_cases ha : i < a.length
    · rw [List.getD_eq_default b 0 (show b.length ≤ c - i by omega), mul_zero]
    · rw [List.getD_eq_default a 0 (by omega), zero_mul]

lemma fold_eq (a b : List ℤ) (r : ℕ) (ha : a.length = r) (hb : b.length = r) (c : ℕ) (hc : c < r) :
    (polyMul a b).getD c 0 + (polyMul a b).getD (c + r) 0 =
      ∑ i ∈ range r, a.getD i 0 * b.getD ((c + r - i) % r) 0 := by
  rw [polyMul_getD_all, polyMul_getD_all]
  rw [← Finset.sum_range_add_sum_Ico _ (show c + 1 ≤ r by omega)]
  rw [← Finset.sum_range_add_sum_Ico _ (show c + 1 ≤ c + r + 1 by omega),
    ← Finset.sum_Ico_consecutive _ (show c + 1 ≤ r by omega) (show r ≤ c + r + 1 by omega)]
  have z1 : ∑ i ∈ range (c + 1), a.getD i 0 * b.getD (c + r - i) 0 = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    have := Finset.mem_range.1 hi
    rw [List.getD_eq_default b 0 (by omega), mul_zero]
  have z2 : ∑ i ∈ Ico r (c + r + 1), a.getD i 0 * b.getD (c + r - i) 0 = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    have := (Finset.mem_Ico.1 hi).1
    rw [List.getD_eq_default a 0 (by omega), zero_mul]
  rw [z1, z2, zero_add, add_zero]
  congr 1
  · apply Finset.sum_congr rfl; intro i hi
    have := Finset.mem_range.1 hi
    rw [show (c + r - i) % r = c - i by
      rw [show c + r - i = (c - i) + r by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
  · apply Finset.sum_congr rfl; intro i hi
    have := Finset.mem_Ico.1 hi
    rw [Nat.mod_eq_of_lt (show c + r - i < r by omega)]

end IntMul.HvdH.FCPf

end

-- ===== Solutions.HvdH.Ref.FermatW
section

/-! `fermatW` computes the exact Gaussian cyclic convolution on the target box. -/

namespace IntMul.HvdH.RefPf
open IntMul.HvdH IntMul.HvdH.Ref IntMul.HvdH.KronPf IntMul.HvdH.FermPf IntMul.HvdH.FCPf

/-! ## One block -/

lemma kpack_append (B : ℤ) : ∀ (l1 l2 : List ℤ), kpack B (l1 ++ l2) = kpack B l1 + B ^ l1.length * kpack B l2
  | [], l2 => by simp [kpack]
  | a :: l1, l2 => by
    simp only [List.cons_append, kpack, kpack_append B l1 l2, List.length_cons, pow_succ]; ring

lemma kpack_replicate_zero (B : ℤ) (r : ℕ) : kpack B (List.replicate r 0) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih => simp [List.replicate_succ, kpack, ih]

lemma encBlk_eq (P r : ℕ) (blk : List (ℤ × ℤ)) (hb : blk.length = r) :
    encBlk P r blk = kpack (2 ^ P) (blk.map Prod.fst) + (2 ^ P) ^ (2 * r) * kpack (2 ^ P) (blk.map Prod.snd) := by
  unfold encBlk
  rw [kpack_append, kpack_append, kpack_replicate_zero]
  simp [hb, two_mul, pow_add]

/-- the coefficient list of the product of two encoded blocks modulo `y^{4r}+1` -/
def pcoef (r : ℕ) (a b : List (ℤ × ℤ)) : List ℤ :=
  (List.range (4 * r)).map fun c =>
    if c < 2 * r then (polyMul (a.map Prod.fst) (b.map Prod.fst)).getD c 0 -
      (polyMul (a.map Prod.snd) (b.map Prod.snd)).getD c 0
    else (polyMul (a.map Prod.fst) (b.map Prod.snd)).getD (c - 2 * r) 0 +
      (polyMul (a.map Prod.snd) (b.map Prod.fst)).getD (c - 2 * r) 0

lemma pcoef_length (r : ℕ) (a b : List (ℤ × ℤ)) : (pcoef r a b).length = 4 * r := by simp [pcoef]

lemma kpack_getD_range (B : ℤ) (m : ℕ) (l : List ℤ) (hl : l.length ≤ m) :
    kpack B l = ∑ c ∈ Finset.range m, l.getD c 0 * B ^ c := by
  rw [kpack_eq_sum]
  apply Finset.sum_subset (Finset.range_mono hl)
  intro c hc hc'
  simp only [Finset.mem_range, not_lt] at hc hc'
  rw [List.getD_eq_default _ _ hc']; simp

lemma kpack_pcoef (P r : ℕ) (a b : List (ℤ × ℤ)) (ha : a.length = r) (hb : b.length = r) :
    kpack (2 ^ P) (pcoef r a b) =
      (kpack (2 ^ P) (a.map Prod.fst) * kpack (2 ^ P) (b.map Prod.fst) -
        kpack (2 ^ P) (a.map Prod.snd) * kpack (2 ^ P) (b.map Prod.snd)) +
      (2 ^ P) ^ (2 * r) * (kpack (2 ^ P) (a.map Prod.fst) * kpack (2 ^ P) (b.map Prod.snd) +
        kpack (2 ^ P) (a.map Prod.snd) * kpack (2 ^ P) (b.map Prod.fst)) := by
  set B : ℤ := 2 ^ P
  have hlen : ∀ (x y : List ℤ), x.length = r → y.length = r → (polyMul x y).length ≤ 2 * r := by
    intro x y hx hy; rw [polyMul_length, hx, hy]; omega
  simp only [← kpack_polyMul]
  rw [kpack_getD_range B (2 * r) _ (hlen _ _ (by simp [ha]) (by simp [hb])),
    kpack_getD_range B (2 * r) _ (hlen _ _ (by simp [ha]) (by simp [hb])),
    kpack_getD_range B (2 * r) _ (hlen _ _ (by simp [ha]) (by simp [hb])),
    kpack_getD_range B (2 * r) _ (hlen _ _ (by simp [ha]) (by simp [hb])),
    kpack_eq_sum, pcoef_length, show 4 * r = 2 * r + 2 * r by ring, Finset.sum_range_add]
  rw [← Finset.sum_add_distrib (s := Finset.range (2 * r)) (f := fun c =>
      (polyMul (List.map Prod.fst a) (List.map Prod.snd b)).getD c 0 * B ^ c),
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  have hc' : c < 2 * r := Finset.mem_range.1 hc
  have e1 : (pcoef r a b).getD c 0 = (polyMul (a.map Prod.fst) (b.map Prod.fst)).getD c 0 -
      (polyMul (a.map Prod.snd) (b.map Prod.snd)).getD c 0 := by
    rw [List.getD_eq_getElem?_getD]; simp [pcoef, hc', show c < 4 * r by omega]
  have e2 : (pcoef r a b).getD (2 * r + c) 0 = (polyMul (a.map Prod.fst) (b.map Prod.snd)).getD c 0 +
      (polyMul (a.map Prod.snd) (b.map Prod.fst)).getD c 0 := by
    rw [List.getD_eq_getElem?_getD]; simp [pcoef, show 2 * r + c < 4 * r by omega]
  rw [e1, e2, pow_add]; ring

/-- The product of two encoded blocks is `kpack` of `pcoef` modulo `2^{4rP}+1`. -/
lemma encBlk_mul (P r : ℕ) (a b : List (ℤ × ℤ)) (ha : a.length = r) (hb : b.length = r) :
    ∃ t : ℤ, encBlk P r a * encBlk P r b = kpack (2 ^ P) (pcoef r a b) + (2 ^ (4 * r * P) + 1) * t := by
  rw [encBlk_eq P r a ha, encBlk_eq P r b hb, kpack_pcoef P r a b ha hb]
  refine ⟨kpack (2 ^ P) (a.map Prod.snd) * kpack (2 ^ P) (b.map Prod.snd), ?_⟩
  have : (2 : ℤ) ^ (4 * r * P) = ((2 ^ P) ^ (2 * r)) ^ 2 := by
    rw [← pow_mul, ← pow_mul]; ring_nf
  rw [this]; ring

/-! ## Splitting off the last axis -/

lemma boxIdxs_snoc (r : ℕ) : ∀ ns : List ℕ,
    boxIdxs (ns ++ [r]) = (boxIdxs ns).flatMap fun l => (List.range r).map fun c => l ++ [c]
  | [] => by
    simp only [List.nil_append, boxIdxs, List.map_cons, List.map_nil, List.flatMap_def]
    induction (List.range r) <;> simp_all
  | n :: ns => by
    simp only [List.cons_append, boxIdxs, boxIdxs_snoc r ns, List.flatMap_assoc, List.map_flatMap,
      List.flatMap_map, List.map_map]
    rfl

lemma rmPos_snoc (r : ℕ) : ∀ (ns : List ℕ) (g : ℕ → ℕ),
    rmPos (ns ++ [r]) g = rmPos ns g * r + g ns.length
  | [], g => by simp [rmPos]
  | n :: ns, g => by
    simp only [List.cons_append, rmPos, rmPos_snoc r ns, List.prod_append, List.prod_cons,
      List.prod_nil, List.length_cons]
    ring

lemma ixf_snoc_lt (l : List ℕ) (c i : ℕ) (hi : i < l.length) : ixf (l ++ [c]) i = ixf l i := by
  simp [ixf, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma ixf_snoc_len (l : List ℕ) (c : ℕ) : ixf (l ++ [c]) l.length = c := by
  simp [ixf, List.getD_eq_getElem?_getD]

lemma rmPos_congr : ∀ (ns : List ℕ) (g g' : ℕ → ℕ), (∀ i < ns.length, g i = g' i) →
    rmPos ns g = rmPos ns g'
  | [], _, _, _ => rfl
  | n :: ns, g, g', h => by
    simp only [rmPos]
    rw [h 0 (by simp), rmPos_congr ns _ _ (fun i hi => h (i + 1) (by simp; omega))]

lemma rmPos_ixf_snoc (r : ℕ) (ns l : List ℕ) (hl : l ∈ boxIdxs ns) (c : ℕ) :
    rmPos (ns ++ [r]) (ixf (l ++ [c])) = rmPos ns (ixf l) * r + c := by
  have hlen : l.length = ns.length := (mem_boxIdxs.1 hl).1
  rw [rmPos_snoc, ← hlen, ixf_snoc_len,
    rmPos_congr ns _ (ixf l) (fun i hi => ixf_snoc_lt l c i (by omega))]

lemma sum_boxIdxs_snoc {M : Type*} [AddCommMonoid M] (r : ℕ) (ns : List ℕ) (f : List ℕ → M) :
    ((boxIdxs (ns ++ [r])).map f).sum = ((boxIdxs ns).map fun l => ∑ c ∈ Finset.range r, f (l ++ [c])).sum := by
  rw [boxIdxs_snoc, List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  simp only [Function.comp, List.map_map]
  exact list_sum_range r _

lemma listOf_snoc {α : Type*} (r : ℕ) (ns : List ℕ) (f : (ℕ → ℕ) → α) :
    listOf (ns ++ [r]) f = (boxIdxs ns).flatMap fun l => (List.range r).map fun c => f (ixf (l ++ [c])) := by
  simp only [listOf, boxIdxs_snoc, List.map_flatMap, List.map_map]
  rfl

/-- any list of the right length is `listOf` of its own entries -/
lemma listOf_self (ns : List ℕ) (X : List ℤ) (hX : X.length = ns.prod) :
    X = listOf ns (fun j => X.getD (rmPos ns j) 0) := by
  apply List.ext_getElem (by rw [length_listOf, hX])
  intro k h1 h2
  rw [length_listOf] at h2
  have hk : k < (boxIdxs ns).length := by rw [length_boxIdxs]; exact h2
  set l := (boxIdxs ns)[k]
  have hl : l ∈ boxIdxs ns := List.getElem_mem hk
  have hpos := getElem?_rmPos hl
  have hnd := nodup_boxIdxs ns
  have hk' : rmPos ns (ixf l) = k := by
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 hpos
    exact (List.Nodup.getElem_inj_iff hnd).1 heq
  simp only [listOf, List.getElem_map]
  show X[k] = X.getD (rmPos ns (ixf l)) 0
  rw [hk', List.getD_eq_getElem _ _ h1]

/-! ## Decoding -/

lemma decBlk_of (P r : ℕ) (hP : 1 ≤ P) (hr : 1 ≤ r) (z : ℤ) (S : List ℤ) (hS : S.length = 4 * r)
    (hSb : ∀ x ∈ S, 2 * |x| < 2 ^ P)
    (hz : z % (2 ^ (4 * r * P) + 1) = kpack (2 ^ P) S % (2 ^ (4 * r * P) + 1)) :
    decBlk (2 ^ (4 * r * P) + 1) P r z = (List.range r).map fun c =>
      (S.getD c 0 + S.getD (c + r) 0, S.getD (2 * r + c) 0 + S.getD (3 * r + c) 0) := by
  set B : ℤ := 2 ^ P
  have hB : 0 < B := by positivity
  have hBe : Even B := Int.even_pow.2 ⟨even_two, by omega⟩
  have hF : (2 : ℤ) ^ (4 * r * P) + 1 = B ^ (4 * r) + 1 := by
    simp only [B]; rw [← pow_mul]; ring_nf
  have hk := kpack_abs B hB S hSb
  rw [hS] at hk
  have hbal : balMod (2 ^ (4 * r * P) + 1) z = kpack B S := by
    apply balMod_eq _ _ _ (by positivity) (by rw [hF]; exact (Int.even_pow.2 ⟨hBe, by omega⟩).add_one) hz
    rw [hF]; omega
  unfold decBlk
  simp only
  rw [hbal, ← hS, kunpack_kpack B hB hBe S hSb]

/-! ## The Gaussian convolution -/

def gmul (a b : ℤ × ℤ) : ℤ × ℤ := (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

/-- the Gaussian cyclic convolution on the box with sides `s` -/
def gconv (s : List ℕ) (U V : List (ℤ × ℤ)) (j : ℕ → ℕ) : ℤ × ℤ :=
  ((boxIdxs s).map fun l => gmul (U.getD (rmPos s (ixf l)) (0, 0))
    (V.getD (rmPos s (fun i => (j i + s.getD i 1 - l.getD i 0) % s.getD i 1)) (0, 0))).sum

lemma list_sum_abs_le {ι : Type*} (L : List ι) (f : ι → ℤ) (m : ℤ) (h : ∀ x ∈ L, |f x| ≤ m) :
    |(L.map f).sum| ≤ L.length * m := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    push_cast
    calc |f a + (L.map f).sum| ≤ |f a| + |(L.map f).sum| := abs_add_le _ _
      _ ≤ m + L.length * m := add_le_add h1 h2
      _ = (L.length + 1) * m := by ring

/-- blocks of the last axis -/
def blkOf (r : ℕ) (U : List (ℤ × ℤ)) (k : ℕ) : List (ℤ × ℤ) := (chunkL r U).getD k []

lemma blkOf_spec (r m : ℕ) (hr : 0 < r) (U : List (ℤ × ℤ)) (hU : U.length = m * r) (k : ℕ) (hk : k < m) :
    (blkOf r U k).length = r ∧ ∀ c < r, (blkOf r U k).getD c (0, 0) = U.getD (k * r + c) (0, 0) := by
  have e : blkOf r U k = (U.drop (k * r)).take r := by
    unfold blkOf; rw [chunkL_eq r m hr U hU, List.getD_eq_getElem?_getD]; simp [hk]
  rw [e]
  have : k * r + r ≤ m * r := by
    have := Nat.mul_le_mul_right r (show k + 1 ≤ m by omega); rw [add_mul, one_mul] at this
    exact this
  refine ⟨by simp [hU]; omega, fun c hc => ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hc,
    List.getElem?_drop]

lemma map_getD_fst (L : List (ℤ × ℤ)) (i : ℕ) : (L.map Prod.fst).getD i 0 = (L.getD i (0, 0)).1 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  cases h : L[i]? <;> simp [h]

lemma map_getD_snd (L : List (ℤ × ℤ)) (i : ℕ) : (L.map Prod.snd).getD i 0 = (L.getD i (0, 0)).2 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  cases h : L[i]? <;> simp [h]

lemma gconv_snoc (od : List ℕ) (r : ℕ) (hr : 0 < r) (U V : List (ℤ × ℤ))
    (hU : U.length = od.prod * r) (hV : V.length = od.prod * r)
    (l : List ℕ) (hl : l ∈ boxIdxs od) (c : ℕ) (hc : c < r) :
    gconv (od ++ [r]) U V (ixf (l ++ [c])) = ((boxIdxs od).map fun l1 => ∑ c1 ∈ Finset.range r,
      gmul ((blkOf r U (rmPos od (ixf l1))).getD c1 (0, 0))
        ((blkOf r V (rmPos od (ixf (subL od l l1)))).getD ((c + r - c1) % r) (0, 0))).sum := by
  unfold gconv
  rw [sum_boxIdxs_snoc]
  congr 1
  apply List.map_congr_left
  intro l1 hl1
  apply Finset.sum_congr rfl
  intro c1 hc1
  have hc1' : c1 < r := Finset.mem_range.1 hc1
  have hlen : l.length = od.length := (mem_boxIdxs.1 hl).1
  have hlen1 : l1.length = od.length := (mem_boxIdxs.1 hl1).1
  have hk1 : rmPos od (ixf l1) < od.prod := rmPos_lt hl1
  have hk2 : rmPos od (ixf (subL od l l1)) < od.prod := rmPos_lt (subL_mem od l l1 hl hl1)
  congr 1
  · rw [rmPos_ixf_snoc r od l1 hl1 c1, (blkOf_spec r od.prod hr U hU _ hk1).2 c1 hc1']
  · rw [(blkOf_spec r od.prod hr V hV _ hk2).2 _ (Nat.mod_lt _ hr), rmPos_snoc]
    congr 2
    · congr 1
      rw [ixf_subL od l l1 hl hl1]
      apply rmPos_congr
      intro i hi
      have h1 : (od ++ [r]).getD i 1 = od.getD i 1 := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      have h2 : (l1 ++ [c1]).getD i 0 = l1.getD i 0 := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega)]
      rw [h1, h2, ixf_snoc_lt l c i (by omega)]
      rfl
    · have h1 : (od ++ [r]).getD od.length 1 = r := by
        rw [List.getD_eq_getElem?_getD]; simp
      have h2 : (l1 ++ [c1]).getD od.length 0 = c1 := by
        rw [List.getD_eq_getElem?_getD, ← hlen1]; simp
      rw [h1, h2, ← hlen, ixf_snoc_len]

lemma pcoef_bound (r : ℕ) (a b : List (ℤ × ℤ)) (ha : a.length = r) (hb : b.length = r) (M : ℤ) (hM0 : 0 ≤ M)
    (hab : ∀ z ∈ a, |z.1| ≤ M ∧ |z.2| ≤ M) (hbb : ∀ z ∈ b, |z.1| ≤ M ∧ |z.2| ≤ M) :
    ∀ x ∈ pcoef r a b, |x| ≤ 2 * (r * M * M) := by
  have hpm : ∀ (x y : List ℤ), x.length = r → (∀ z ∈ x, |z| ≤ M) → (∀ z ∈ y, |z| ≤ M) →
      ∀ c, |(polyMul x y).getD c 0| ≤ r * M * M := by
    intro x y hx hxb hyb c
    rcases getD_mem_or (polyMul x y) c 0 with h | h
    · have := polyMul_coeff_bound x y M hM0 hxb hyb _ h; rwa [hx] at this
    · rw [h]; simp; positivity
  have h1 : ∀ z ∈ a.map Prod.fst, |z| ≤ M := by
    intro z hz; simp only [List.mem_map] at hz; obtain ⟨w, hw, rfl⟩ := hz; exact (hab w hw).1
  have h2 : ∀ z ∈ a.map Prod.snd, |z| ≤ M := by
    intro z hz; simp only [List.mem_map] at hz; obtain ⟨w, hw, rfl⟩ := hz; exact (hab w hw).2
  have h3 : ∀ z ∈ b.map Prod.fst, |z| ≤ M := by
    intro z hz; simp only [List.mem_map] at hz; obtain ⟨w, hw, rfl⟩ := hz; exact (hbb w hw).1
  have h4 : ∀ z ∈ b.map Prod.snd, |z| ≤ M := by
    intro z hz; simp only [List.mem_map] at hz; obtain ⟨w, hw, rfl⟩ := hz; exact (hbb w hw).2
  have la : (a.map Prod.fst).length = r := by simp [ha]
  have la' : (a.map Prod.snd).length = r := by simp [ha]
  intro x hx
  simp only [pcoef, List.mem_map, List.mem_range] at hx
  obtain ⟨c, _, rfl⟩ := hx
  split_ifs
  · calc _ ≤ |(polyMul (a.map Prod.fst) (b.map Prod.fst)).getD c 0| +
          |(polyMul (a.map Prod.snd) (b.map Prod.snd)).getD c 0| := abs_sub _ _
      _ ≤ r * M * M + r * M * M := add_le_add (hpm _ _ la h1 h3 c) (hpm _ _ la' h2 h4 c)
      _ = _ := by ring
  · calc _ ≤ |(polyMul (a.map Prod.fst) (b.map Prod.snd)).getD (c - 2 * r) 0| +
          |(polyMul (a.map Prod.snd) (b.map Prod.fst)).getD (c - 2 * r) 0| := abs_add_le _ _
      _ ≤ r * M * M + r * M * M := add_le_add (hpm _ _ la h1 h4 _) (hpm _ _ la' h2 h3 _)
      _ = _ := by ring

lemma pcoef_getD_lo (r : ℕ) (a b : List (ℤ × ℤ)) (c : ℕ) (hc : c < 2 * r) :
    (pcoef r a b).getD c 0 = (polyMul (a.map Prod.fst) (b.map Prod.fst)).getD c 0 -
      (polyMul (a.map Prod.snd) (b.map Prod.snd)).getD c 0 := by
  rw [List.getD_eq_getElem?_getD]; simp [pcoef, hc, show c < 4 * r by omega]

lemma pcoef_getD_hi (r : ℕ) (a b : List (ℤ × ℤ)) (c : ℕ) (hc : c < 2 * r) :
    (pcoef r a b).getD (2 * r + c) 0 = (polyMul (a.map Prod.fst) (b.map Prod.snd)).getD c 0 +
      (polyMul (a.map Prod.snd) (b.map Prod.fst)).getD c 0 := by
  rw [List.getD_eq_getElem?_getD]; simp [pcoef, show 2 * r + c < 4 * r by omega]

/-- The folded block product is the Gaussian cyclic convolution along the last axis. -/
lemma fold_pcoef (r : ℕ) (a b : List (ℤ × ℤ)) (ha : a.length = r) (hb : b.length = r) (c : ℕ) (hc : c < r) :
    ((pcoef r a b).getD c 0 + (pcoef r a b).getD (c + r) 0,
      (pcoef r a b).getD (2 * r + c) 0 + (pcoef r a b).getD (3 * r + c) 0) =
    ∑ c1 ∈ Finset.range r, gmul (a.getD c1 (0, 0)) (b.getD ((c + r - c1) % r) (0, 0)) := by
  have la : ∀ f : ℤ × ℤ → ℤ, (a.map f).length = r := by simp [ha]
  have lb : ∀ f : ℤ × ℤ → ℤ, (b.map f).length = r := by simp [hb]
  rw [pcoef_getD_lo r a b c (by omega), pcoef_getD_lo r a b (c + r) (by omega),
    show 3 * r + c = 2 * r + (c + r) by ring,
    pcoef_getD_hi r a b c (by omega), pcoef_getD_hi r a b (c + r) (by omega)]
  ext
  · rw [Prod.fst_sum]
    simp only [gmul]
    rw [Finset.sum_sub_distrib]
    have e1 := fold_eq _ _ r (la Prod.fst) (lb Prod.fst) c hc
    have e2 := fold_eq _ _ r (la Prod.snd) (lb Prod.snd) c hc
    simp only [map_getD_fst, map_getD_snd] at e1 e2
    rw [← e1, ← e2]; ring
  · rw [Prod.snd_sum]
    simp only [gmul]
    rw [Finset.sum_add_distrib]
    have e1 := fold_eq _ _ r (la Prod.fst) (lb Prod.snd) c hc
    have e2 := fold_eq _ _ r (la Prod.snd) (lb Prod.fst) c hc
    simp only [map_getD_fst, map_getD_snd] at e1 e2
    rw [← e1, ← e2]; ring

/-- the coefficient list of one output block -/
def Scoef (r : ℕ) (od : List ℕ) (U V : List (ℤ × ℤ)) (l : List ℕ) : List ℤ :=
  (List.range (4 * r)).map fun c => ((boxIdxs od).map fun l1 =>
    (pcoef r (blkOf r U (rmPos od (ixf l1))) (blkOf r V (rmPos od (ixf (subL od l l1))))).getD c 0).sum

theorem fermatW_core (ax : List (ℕ × ℕ)) (r P : ℕ) (hr : 1 ≤ r) (hP : 1 ≤ P)
    (hax : ∀ p ∈ ax, p.1 = 0 ∨ 2 ^ p.1 * p.2 = 2 * (4 * r * P)) (lo : ℕ) (hlo : sumJ ax = lo)
    (hlo2 : lo ≤ 2 * (4 * r * P))
    (U V : List (ℤ × ℤ)) (hU : U.length = blockSize ax * r) (hV : V.length = blockSize ax * r)
    (M : ℤ) (hM0 : 0 ≤ M) (hUb : ∀ z ∈ U, |z.1| ≤ M ∧ |z.2| ≤ M) (hVb : ∀ z ∈ V, |z.1| ≤ M ∧ |z.2| ≤ M)
    (hPM : 4 * ((blockSize ax * r : ℕ) : ℤ) * M ^ 2 < 2 ^ P) :
    ((mdit (2 ^ (4 * r * P) + 1) (4 * r * P) ax
      (pmulZ (2 ^ (4 * r * P) + 1)
        (mdif (2 ^ (4 * r * P) + 1) ax ((chunkL r U).map fun blk => encBlk P r blk % (2 ^ (4 * r * P) + 1)))
        (mdif (2 ^ (4 * r * P) + 1) ax ((chunkL r V).map fun blk => encBlk P r blk % (2 ^ (4 * r * P) + 1))))).map
      fun z => (z * 2 ^ (2 * (4 * r * P) - lo)) % (2 ^ (4 * r * P) + 1)).flatMap
      (decBlk (2 ^ (4 * r * P) + 1) P r) =
    listOf (dimsOf ax ++ [r]) (gconv (dimsOf ax ++ [r]) U V) := by
  set n := 4 * r * P with hn
  set F : ℤ := 2 ^ n + 1 with hF
  set od := dimsOf ax with hod
  set Bo := blockSize ax with hBo
  have hBod : Bo = od.prod := blockSize_eq ax
  have hr0 : 0 < r := by omega
  set encA := (chunkL r U).map fun blk => encBlk P r blk % F with hencA
  set encB := (chunkL r V).map fun blk => encBlk P r blk % F with hencB
  have hchU : (chunkL r U).length = Bo := by rw [chunkL_eq r Bo hr0 U hU]; simp
  have hchV : (chunkL r V).length = Bo := by rw [chunkL_eq r Bo hr0 V hV]; simp
  have hA : encA.length = Bo := by simp [encA, hchU]
  have hB : encB.length = Bo := by simp [encB, hchV]
  have hencA_get : ∀ k < Bo, encA.getD k 0 = encBlk P r (blkOf r U k) % F := by
    intro k hk
    rw [List.getD_eq_getElem?_getD]
    simp [encA, blkOf, List.getD_eq_getElem?_getD, hk, hchU]
  have hencB_get : ∀ k < Bo, encB.getD k 0 = encBlk P r (blkOf r V k) % F := by
    intro k hk
    rw [List.getD_eq_getElem?_getD]
    simp [encB, blkOf, List.getD_eq_getElem?_getD, hk, hchV]
  set C := mdit F n ax (pmulZ F (mdif F ax encA) (mdif F ax encB)) with hC
  have hRel := mdit_pmul_mdif n ax hax encA encB hA hB
  have hCl : C.length = Bo := by
    rw [((relC_iff n _ _ _).1 hRel).1, length_listOf, hBod]
  set C' := C.map fun z => (z * 2 ^ (2 * n - lo)) % F with hC'
  have hC'l : C'.length = od.prod := by simp [C', hCl, hBod]
  rw [listOf_self od C' hC'l, listOf_snoc, listOf, List.flatMap_map]
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro l hl
  set k := rmPos od (ixf l) with hk
  have hkB : k < Bo := by rw [hBod]; exact rmPos_lt hl
  -- the coefficient list
  set S := Scoef r od U V l with hS
  have hSl : S.length = 4 * r := by simp [S, Scoef]
  have hblk : ∀ l1 ∈ boxIdxs od, (blkOf r U (rmPos od (ixf l1))).length = r ∧
      (blkOf r V (rmPos od (ixf (subL od l l1)))).length = r := by
    intro l1 hl1
    exact ⟨(blkOf_spec r Bo hr0 U hU _ (by rw [hBod]; exact rmPos_lt hl1)).1,
      (blkOf_spec r Bo hr0 V hV _ (by rw [hBod]; exact rmPos_lt (subL_mem od l l1 hl hl1))).1⟩
  have hblkb : ∀ (W : List (ℤ × ℤ)), (∀ z ∈ W, |z.1| ≤ M ∧ |z.2| ≤ M) → ∀ k, ∀ z ∈ blkOf r W k,
      |z.1| ≤ M ∧ |z.2| ≤ M := by
    intro W hW k z hz
    unfold blkOf at hz
    rcases getD_mem_or (chunkL r W) k [] with h | h
    · unfold chunkL at h
      obtain ⟨i, _, hi⟩ := List.mem_map.1 h
      unfold chunkL at hz
      rw [← hi] at hz
      exact hW z (List.mem_of_mem_drop (List.mem_of_mem_take hz))
    · rw [h] at hz; simp at hz
  set pc : List ℕ → List ℤ := fun l1 =>
    pcoef r (blkOf r U (rmPos od (ixf l1))) (blkOf r V (rmPos od (ixf (subL od l l1)))) with hpc
  have hSget : ∀ c < 4 * r, S.getD c 0 = ((boxIdxs od).map fun l1 => (pc l1).getD c 0).sum := by
    intro c hc
    rw [List.getD_eq_getElem?_getD]; simp [S, Scoef, hc, pc]
  -- integer identity for kpack S
  have hkS : kpack (2 ^ P) S = ((boxIdxs od).map fun l1 => kpack (2 ^ P) (pc l1)).sum := by
    rw [kpack_eq_sum, hSl]
    rw [Finset.sum_congr rfl (fun c hc => by rw [hSget c (Finset.mem_range.1 hc), ← List.sum_map_mul_right])]
    rw [← list_sum_finset_comm]
    congr 1
    apply List.map_congr_left
    intro l1 _
    rw [kpack_eq_sum, pcoef_length]
  -- the cast of `C'` at `k`
  have hcast : ((C'.getD k 0 : ℤ) : ZMod (2 ^ n + 1)) = ((kpack (2 ^ P) S : ℤ) : ZMod (2 ^ n + 1)) := by
    have e1 : C'.getD k 0 = (C.getD k 0 * 2 ^ (2 * n - lo)) % F := by
      rw [List.getD_eq_getElem _ _ (by simp [C', hCl]; exact hkB), List.getElem_map,
        ← List.getD_eq_getElem _ 0 (by rw [hCl]; exact hkB)]
    have e2 : ((C.getD k 0 : ℤ) : ZMod (2 ^ n + 1)) =
        2 ^ sumJ ax * ((cconv od encA encB (ixf l) : ℤ) : ZMod (2 ^ n + 1)) := by
      have := ((relC_iff n _ _ _).1 hRel).2 k
      rw [hk, getD_listOf od _ 0 hl] at this
      exact this
    rw [e1, hF, cast_emod]
    push_cast
    rw [e2, hlo]
    have hpow : (2 : ZMod (2 ^ n + 1)) ^ lo * 2 ^ (2 * n - lo) = 1 := by
      rw [← pow_add, show lo + (2 * n - lo) = n * 2 by omega, pow_mul (2 : ZMod (2 ^ n + 1)) n 2,
        two_pow_eq_neg_one n]; ring
    have e3 : ((cconv od encA encB (ixf l) : ℤ) : ZMod (2 ^ n + 1)) =
        ((kpack (2 ^ P) S : ℤ) : ZMod (2 ^ n + 1)) := by
      rw [hkS, cconv]
      push_cast
      rw [List.map_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro l1 hl1
      simp only [Function.comp]
      have hsub : (fun i => (ixf l i + od.getD i 1 - l1.getD i 0) % od.getD i 1) = ixf (subL od l l1) :=
        (ixf_subL od l l1 hl hl1).symm
      rw [hsub, hencA_get _ (by rw [hBod]; exact rmPos_lt hl1),
        hencB_get _ (by rw [hBod]; exact rmPos_lt (subL_mem od l l1 hl hl1))]
      obtain ⟨t, ht⟩ := encBlk_mul P r _ _ (hblk l1 hl1).1 (hblk l1 hl1).2
      rw [Int.cast_mul, hF, cast_emod, cast_emod, ← Int.cast_mul, ht]
      push_cast
      have : ((2 : ZMod (2 ^ n + 1)) ^ n + 1) = 0 := by rw [two_pow_eq_neg_one]; ring
      rw [this]; ring
    rw [← e3]
    calc (2 : ZMod (2 ^ n + 1)) ^ lo * ((cconv od encA encB (ixf l) : ℤ) : ZMod (2 ^ n + 1)) * 2 ^ (2 * n - lo)
        = ((cconv od encA encB (ixf l) : ℤ) : ZMod (2 ^ n + 1)) * (2 ^ lo * 2 ^ (2 * n - lo)) := by ring
      _ = _ := by rw [hpow, mul_one]
  have hz : C'.getD k 0 % (2 ^ (4 * r * P) + 1) = kpack (2 ^ P) S % (2 ^ (4 * r * P) + 1) := by
    have := (ZMod.intCast_eq_intCast_iff' _ _ (2 ^ n + 1)).1 hcast
    push_cast at this
    exact this
  -- bounds
  have hSb : ∀ x ∈ S, 2 * |x| < 2 ^ P := by
    intro x hx
    simp only [S, Scoef, List.mem_map, List.mem_range] at hx
    obtain ⟨c, _, rfl⟩ := hx
    have hb := list_sum_abs_le (boxIdxs od) (fun l1 => (pc l1).getD c 0) (2 * (r * M * M)) (by
      intro l1 hl1
      rcases getD_mem_or (pc l1) c 0 with h | h
      · exact pcoef_bound r _ _ (hblk l1 hl1).1 (hblk l1 hl1).2 M hM0 (hblkb U hUb _) (hblkb V hVb _) _ h
      · rw [h]; simp; positivity)
    rw [length_boxIdxs, ← hBod] at hb
    have : (2 : ℤ) * (Bo * (2 * (r * M * M))) = 4 * ((Bo * r : ℕ) : ℤ) * M ^ 2 := by push_cast; ring
    simp only [pc] at hb
    linarith
  have hd : decBlk F P r (C'.getD k 0) = (List.range r).map fun c =>
      (S.getD c 0 + S.getD (c + r) 0, S.getD (2 * r + c) 0 + S.getD (3 * r + c) 0) :=
    decBlk_of P r hP hr _ S hSl hSb hz
  show decBlk F P r (C'.getD k 0) = (List.range r).map fun c => gconv (od ++ [r]) U V (ixf (l ++ [c]))
  rw [hd]
  apply List.map_congr_left
  intro c hc
  have hc' : c < r := List.mem_range.1 hc
  rw [gconv_snoc od r hr0 U V (by rw [hU, hBod]) (by rw [hV, hBod]) l hl c hc',
    hSget c (by omega), hSget (c + r) (by omega), hSget (2 * r + c) (by omega), hSget (3 * r + c) (by omega)]
  rw [← List.sum_map_add, ← List.sum_map_add]
  have : ∀ (L : List (List ℕ)) (f g : List ℕ → ℤ), ((L.map f).sum, (L.map g).sum) =
      (L.map fun x => (f x, g x)).sum := by
    intro L f g
    induction L with
    | nil => rfl
    | cons a L ih => simp only [List.map_cons, List.sum_cons]; rw [← ih]; rfl
  rw [this]
  congr 1
  apply List.map_congr_left
  intro l1 hl1
  exact fold_pcoef r _ _ (hblk l1 hl1).1 (hblk l1 hl1).2 c hc'

/-! ## The parameters -/

lemma te_le (q : Params) (i : ℕ) : q.te i ≤ q.e := by unfold Params.te; split_ifs <;> omega

lemma dimsOf_outer (q : Params) : dimsOf q.outerAxes = (List.range (q.K - 1)).map fun i => 2 ^ q.te i := by
  simp [dimsOf, Params.outerAxes, List.map_map, Function.comp_def]

lemma tdims_split (q : Params) (hK : 1 ≤ q.K) (hdh : q.dh < q.K) :
    q.tdims = dimsOf q.outerAxes ++ [q.r] := by
  rw [dimsOf_outer, Params.tdims]
  obtain ⟨K', hK'⟩ : ∃ K', q.K = K' + 1 := ⟨q.K - 1, by omega⟩
  rw [hK', List.range_succ, List.map_append]
  simp only [Nat.add_sub_cancel, List.map_cons, List.map_nil, Params.r]
  congr 3
  unfold Params.te; rw [if_neg (by omega)]

lemma sumJ_outer (q : Params) : sumJ q.outerAxes = q.logOuter := by
  simp [sumJ, Params.outerAxes, Params.logOuter, List.map_map, Function.comp_def]

lemma outer_hax (q : Params) : ∀ p ∈ q.outerAxes, p.1 = 0 ∨ 2 ^ p.1 * p.2 = 2 * (4 * q.r * q.P) := by
  intro p hp
  simp only [Params.outerAxes, List.mem_map, List.mem_range] at hp
  obtain ⟨i, _, rfl⟩ := hp
  right
  simp only [Params.fn]
  apply Nat.mul_div_cancel'
  have h1 : 2 ^ q.te i ∣ 2 ^ q.e := pow_dvd_pow 2 (te_le q i)
  have h2 : 2 ^ q.e ∣ 2 * (4 * q.r * q.P) := by
    simp only [Params.r]; exact Dvd.intro (8 * q.P) (by ring)
  exact h1.trans h2

theorem fermatW_eq (q : Params) (hK : 1 ≤ q.K) (he : 1 ≤ q.e) (hdh : q.dh < q.K) (hP : 1 ≤ q.P)
    (hlog : q.logOuter ≤ 2 * q.fn)
    (U V : List (ℤ × ℤ)) (hU : U.length = q.tdims.prod) (hV : V.length = q.tdims.prod)
    (M : ℤ) (hM0 : 0 ≤ M) (hUb : ∀ z ∈ U, |z.1| ≤ M ∧ |z.2| ≤ M) (hVb : ∀ z ∈ V, |z.1| ≤ M ∧ |z.2| ≤ M)
    (hPM : 4 * (q.tdims.prod : ℤ) * M ^ 2 < 2 ^ q.P) :
    fermatW q U V = listOf q.tdims (gconv q.tdims U V) := by
  have hsplit := tdims_split q hK hdh
  have hprod : q.tdims.prod = blockSize q.outerAxes * q.r := by
    rw [hsplit, List.prod_append, blockSize_eq]; simp
  have hr : 1 ≤ q.r := Nat.one_le_two_pow
  rw [hprod] at hU hV
  rw [hprod] at hPM
  rw [hsplit]
  have := fermatW_core q.outerAxes q.r q.P hr hP (outer_hax q) q.logOuter (sumJ_outer q) hlog U V hU hV
    M hM0 hUb hVb (by exact_mod_cast hPM)
  rw [← this]
  rfl

end IntMul.HvdH.RefPf

end

-- ===== Solutions.HvdH.SynFFT
section

open Complex

namespace IntMul.HvdH.SynPf
open IntMul.HvdH

@[simp] lemma gC_re (z : ℤ × ℤ) : (gC z).re = z.1 := by simp [gC]
@[simp] lemma gC_im (z : ℤ × ℤ) : (gC z).im = z.2 := by simp [gC]

lemma gC_add (a b : ℤ × ℤ) : gC (a + b) = gC a + gC b := by
  simp only [gC, Prod.fst_add, Prod.snd_add, Int.cast_add]; ring

end IntMul.HvdH.SynPf

end

-- ===== Solutions.HvdH.FixedPoint
section

namespace IntMul.HvdH.FP
open IntMul.HvdH

lemma rho0_abs_le (x : ℝ) : |((rho0 x : ℤ) : ℝ)| ≤ |x| := by
  unfold rho0
  split_ifs with h
  · rw [abs_of_nonneg (by exact_mod_cast Int.floor_nonneg.2 h), abs_of_nonneg h]
    exact Int.floor_le x
  · push Not at h
    have h1 : ((⌈x⌉ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast Int.ceil_le.2 (by simpa using h.le)
    rw [abs_of_nonpos h1, abs_of_neg h]
    linarith [Int.le_ceil x]

lemma rho0_sub_lt (x : ℝ) : |((rho0 x : ℤ) : ℝ) - x| < 1 := by
  unfold rho0
  split_ifs with h
  · rw [abs_lt]; constructor <;> linarith [Int.floor_le x, Int.lt_floor_add_one x]
  · rw [abs_lt]; constructor <;> linarith [Int.le_ceil x, Int.ceil_lt_add_one x]

lemma norm_rho0C_le (u : ℂ) : ‖rho0C u‖ ≤ ‖u‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
  apply Real.sqrt_le_sqrt
  have h1 := rho0_abs_le u.re
  have h2 := rho0_abs_le u.im
  have hre : (rho0C u).re = rho0 u.re := by simp [rho0C]
  have him : (rho0C u).im = rho0 u.im := by simp [rho0C]
  rw [hre, him]
  nlinarith [sq_abs ((rho0 u.re : ℤ) : ℝ), sq_abs u.re, sq_abs ((rho0 u.im : ℤ) : ℝ), sq_abs u.im,
    abs_nonneg ((rho0 u.re : ℤ) : ℝ), abs_nonneg ((rho0 u.im : ℤ) : ℝ)]

lemma norm_rho0C_sub_lt (u : ℂ) : ‖rho0C u - u‖ < Real.sqrt 2 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  apply Real.sqrt_lt_sqrt (by positivity)
  have h1 := rho0_sub_lt u.re
  have h2 := rho0_sub_lt u.im
  simp only [rho0C, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.intCast_re, Complex.intCast_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im]
  simp only [mul_zero, sub_zero, mul_one, zero_add, add_zero, zero_mul]
  have a1 : (((rho0 u.re : ℤ) : ℝ) - u.re) ^ 2 < 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (((rho0 u.re : ℤ) : ℝ) - u.re)]
  have a2 : (((rho0 u.im : ℤ) : ℝ) - u.im) ^ 2 < 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (((rho0 u.im : ℤ) : ℝ) - u.im)]
  linarith

end IntMul.HvdH.FP

end

-- ===== Solutions.HvdH.ConvRfp
section

open Complex

namespace IntMul.HvdH.CRPf
open IntMul.HvdH IntMul.HvdH.FPPf

/-! ### Pointwise products in `R` -/

lemma tdiv_eq_rho0 (W : ℤ) (N : ℕ) (hN : 0 < N) : W.tdiv N = rho0 ((W : ℝ) / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold rho0
  split_ifs with h
  · have hW : 0 ≤ W := by
      have : (0 : ℝ) ≤ W := by
        by_contra hc; push_neg at hc
        have := div_neg_of_neg_of_pos hc hN'; linarith
      exact_mod_cast this
    rw [Int.tdiv_eq_ediv_of_nonneg hW, Int.floor_div_natCast, Int.floor_intCast]
  · have hW : W < 0 := by
      by_contra hc; push_neg at hc
      exact h (div_nonneg (by exact_mod_cast hc) hN'.le)
    have e : (W : ℝ) / N = -(((-W : ℤ) : ℝ) / N) := by push_cast; ring
    rw [e, Int.ceil_neg, Int.floor_div_natCast, Int.floor_intCast,
      ← Int.tdiv_eq_ediv_of_nonneg (by omega), Int.neg_tdiv, neg_neg]

lemma gC_tdiv_eq (A B : ℤ) (N : ℕ) (hN : 0 < N) (z : ℂ) (hz : z = ((A : ℂ) + (B : ℂ) * Complex.I) / N) :
    gC (A.tdiv N, B.tdiv N) = rho0C z := by
  have e : z = (((A : ℝ) / N : ℝ) : ℂ) + (((B : ℝ) / N : ℝ) : ℂ) * Complex.I := by
    rw [hz]; push_cast; ring
  have hre : z.re = (A : ℝ) / N := by rw [e]; simp
  have him : z.im = (B : ℝ) / N := by rw [e]; simp
  unfold gC rho0C
  rw [hre, him, tdiv_eq_rho0 A N hN, tdiv_eq_rho0 B N hN]

/-! ### Scaling by a power of two (Lemma 2.2) -/

lemma ceilSqrt_real (N : ℕ) : Real.sqrt N ≤ ceilSqrt N ∧ (ceilSqrt N : ℝ) < Real.sqrt N + 1 := by
  have h1 := Nat.sqrt_le' N
  have h2 := Nat.lt_succ_sqrt' N
  have hs : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt N :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast h1)
  unfold ceilSqrt
  split_ifs with h
  · refine ⟨?_, ?_⟩
    · push_cast
      calc Real.sqrt N ≤ Real.sqrt (((Nat.sqrt N : ℝ) + 1) ^ 2) :=
            Real.sqrt_le_sqrt (by exact_mod_cast h2.le)
        _ = (Nat.sqrt N : ℝ) + 1 := Real.sqrt_sq (by positivity)
    · have : ((Nat.sqrt N : ℕ) : ℝ) < Real.sqrt N :=
        (Real.lt_sqrt (by positivity)).2 (by rw [sq]; exact_mod_cast h)
      push_cast; linarith
  · have e : Nat.sqrt N * Nat.sqrt N = N := by
      have := Nat.sqrt_le N; omega
    have : Real.sqrt N = Nat.sqrt N := by
      rw [show (N : ℝ) = (Nat.sqrt N : ℝ) * (Nat.sqrt N : ℝ) by exact_mod_cast e.symm]
      exact Real.sqrt_mul_self (Nat.cast_nonneg _)
    rw [this]; exact ⟨le_refl _, by linarith⟩

lemma norm_gC_eq (z : ℤ × ℤ) : ‖gC z‖ = Real.sqrt ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, SynPf.gC_re, SynPf.gC_im]

theorem scaleZ_bound (p k : ℕ) (z : ℤ × ℤ) (w : ℂ) (hw : ‖(2 : ℂ) ^ k * w‖ ≤ 1) :
    ‖gC (scaleZ p k z)‖ ≤ 2 ^ p ∧
      ‖gC (scaleZ p k z) - 2 ^ p * (2 ^ k * w)‖ ≤ 2 * 2 ^ k * ‖gC z - 2 ^ p * w‖ + 3 := by
  set W : ℤ × ℤ := (2 ^ k * z.1, 2 ^ k * z.2) with hWdef
  have hgW : gC W = 2 ^ k * gC z := by simp only [W, gC]; push_cast; ring
  set D := ‖gC W - 2 ^ p * (2 ^ k * w)‖ with hD
  have hD' : D = 2 ^ k * ‖gC z - 2 ^ p * w‖ := by
    rw [hD, hgW, show (2 : ℂ) ^ k * gC z - 2 ^ p * (2 ^ k * w) = 2 ^ k * (gC z - 2 ^ p * w) by ring,
      norm_mul, norm_pow, Complex.norm_two]
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hT : ‖(2 : ℂ) ^ p * (2 ^ k * w)‖ ≤ 2 ^ p := by
    rw [norm_mul, norm_pow, Complex.norm_two]
    calc _ ≤ (2 : ℝ) ^ p * 1 := mul_le_mul_of_nonneg_left hw hp.le
      _ = _ := mul_one _
  have ha : ‖gC W‖ ≤ D + 2 ^ p := by
    have := norm_sub_norm_le (gC W) (2 ^ p * (2 ^ k * w)); linarith
  have hDnn : 0 ≤ D := norm_nonneg _
  have hW2 : ‖gC W‖ ^ 2 = ((W.1 ^ 2 + W.2 ^ 2 : ℤ) : ℝ) := by
    rw [norm_gC_eq, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hsc : scaleZ p k z = if W.1 ^ 2 + W.2 ^ 2 ≤ 4 ^ p then W else
      ((W.1 * 2 ^ p).tdiv (ceilSqrt (W.1 ^ 2 + W.2 ^ 2).toNat : ℤ),
        (W.2 * 2 ^ p).tdiv (ceilSqrt (W.1 ^ 2 + W.2 ^ 2).toNat : ℤ)) := rfl
  rw [hsc]
  rw [show 2 * 2 ^ k * ‖gC z - 2 ^ p * w‖ = 2 * D by rw [hD']; ring]
  split_ifs with h
  · refine ⟨?_, by linarith⟩
    have : ‖gC W‖ ^ 2 ≤ ((2 : ℝ) ^ p) ^ 2 := by
      rw [hW2, ← pow_mul, mul_comm, pow_mul]; norm_num; exact_mod_cast h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hp.le (by norm_num)).1 this
  · push_neg at h
    set N : ℕ := (W.1 ^ 2 + W.2 ^ 2).toNat with hN
    have hNr : (N : ℝ) = ‖gC W‖ ^ 2 := by
      rw [hW2]
      have hz : ((N : ℕ) : ℤ) = W.1 ^ 2 + W.2 ^ 2 := Int.toNat_of_nonneg (by positivity)
      rw [← hz]; norm_cast
    have hsq : Real.sqrt N = ‖gC W‖ := by rw [hNr, Real.sqrt_sq (norm_nonneg _)]
    obtain ⟨hm1, hm2⟩ := ceilSqrt_real N
    rw [hsq] at hm1 hm2
    have hagt : (2 : ℝ) ^ p < ‖gC W‖ := by
      have : ((2 : ℝ) ^ p) ^ 2 < ‖gC W‖ ^ 2 := by
        rw [hW2, ← pow_mul, mul_comm, pow_mul]; norm_num; exact_mod_cast h
      exact (pow_lt_pow_iff_left₀ hp.le (norm_nonneg _) (by norm_num)).1 this
    set m := ceilSqrt N with hm
    have hm0 : (0 : ℝ) < m := by linarith
    have hm0' : 0 < m := by exact_mod_cast hm0
    set X : ℂ := gC W * 2 ^ p / m with hX
    have hR : gC ((W.1 * 2 ^ p).tdiv (m : ℤ), (W.2 * 2 ^ p).tdiv (m : ℤ)) = rho0C X := by
      apply gC_tdiv_eq _ _ _ hm0'
      rw [hX]; simp only [gC]; push_cast; ring
    rw [hR]
    have hXn : ‖X‖ = ‖gC W‖ * 2 ^ p / m := by
      rw [hX, norm_div, norm_mul, norm_pow, Complex.norm_two, Complex.norm_natCast]
    have hXle : ‖X‖ ≤ 2 ^ p := by
      rw [hXn, div_le_iff₀ hm0]; nlinarith [norm_nonneg (gC W)]
    refine ⟨(FP.norm_rho0C_le X).trans hXle, ?_⟩
    have h1 := FP.norm_rho0C_sub_lt X
    have hs2 : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have h2 : ‖X - gC W‖ ≤ ‖gC W‖ - 2 ^ p + 1 := by
      have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0'.ne'
      have e : X - gC W = gC W * ((2 ^ p - m) / m : ℂ) := by
        rw [hX]; field_simp; try ring
      rw [e, norm_mul]
      have e2 : ((2 : ℂ) ^ p - m) / m = (((2 : ℝ) ^ p - m) / m : ℝ) := by push_cast; ring
      rw [e2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos]
      · rw [div_eq_mul_inv]
        have key : ‖gC W‖ * (-(((2 : ℝ) ^ p - m) * (m : ℝ)⁻¹)) ≤ ‖gC W‖ - 2 ^ p + 1 := by
          rw [show ‖gC W‖ * (-(((2 : ℝ) ^ p - m) * (m : ℝ)⁻¹)) = ‖gC W‖ - ‖gC W‖ * 2 ^ p / m by
            field_simp; ring]
          have : (2 : ℝ) ^ p - 1 ≤ ‖gC W‖ * 2 ^ p / m := by
            rw [le_div_iff₀ hm0]; nlinarith
          linarith
        linarith
      · apply div_nonpos_of_nonpos_of_nonneg _ hm0.le; linarith
    have e : rho0C X - 2 ^ p * (2 ^ k * w) = (rho0C X - X) + (X - gC W) + (gC W - 2 ^ p * (2 ^ k * w)) := by
      ring
    rw [e]
    calc _ ≤ ‖(rho0C X - X) + (X - gC W)‖ + D := norm_add_le _ _
      _ ≤ ‖rho0C X - X‖ + ‖X - gC W‖ + D := by gcongr; exact norm_add_le _ _
      _ ≤ 2 * D + 3 := by linarith

end IntMul.HvdH.CRPf

end

-- ===== Solutions.HvdH.SynId
section

open Complex

namespace IntMul.HvdH.SynId
open IntMul.HvdH

/-- Evaluation of a coefficient array at `z` (a root of `y^r + 1`). -/
noncomputable def ev (r : ℕ) (z : ℂ) (a : ℕ → ℂ) : ℂ := ∑ c ∈ Finset.range r, a c * z ^ c

/-! ### Evaluating arrays over `R` -/

/-- Evaluate the `R`-entry at position `k` at the root `z`. -/
noncomputable def E (r : ℕ) (z : ℂ) {d : ℕ} (u : (Fin (d + 1) → ℕ) → ℂ) (k : Fin d → ℕ) : ℂ :=
  ev r z (fun c => u (Fin.snoc k c))

/-! ### The convolution theorem on boxes -/

/-! ### The convolution identity over `R` -/

end IntMul.HvdH.SynId

end

-- ===== Solutions.HvdH.ConvC
section

open Complex

namespace IntMul.HvdH.CCPf
open IntMul.HvdH IntMul.HvdH.FPPf IntMul.HvdH.CRPf IntMul.HvdH.CRProp

lemma twD_bound (p n j : ℕ) (hn : 0 < n) :
    ‖gC (twD p n j)‖ ≤ 2 ^ p ∧
      ‖gC (twD p n j) - 2 ^ p * Complex.exp (2 * Real.pi * Complex.I * j / n)‖ ≤ 5 := by
  have hw : ‖(2 : ℂ) ^ 0 * Complex.exp (2 * Real.pi * Complex.I * j / n)‖ ≤ 1 := by
    rw [pow_zero, one_mul, Complex.norm_exp]
    have : (2 * Real.pi * Complex.I * j / n).re = 0 := by
      simp [Complex.div_re, Complex.mul_re]
    rw [this, Real.exp_zero]
  obtain ⟨h1, h2⟩ := scaleZ_bound p 0 (twiddle p n j) _ hw
  refine ⟨h1, ?_⟩
  have ht := IntMul.HvdH.twiddle_bound p n j hn
  have hg : gC (twiddle p n j) = ((twiddle p n j).1 : ℂ) + ((twiddle p n j).2 : ℂ) * Complex.I := rfl
  rw [pow_zero, one_mul] at h2
  unfold twD
  calc _ ≤ 2 * 2 ^ 0 * ‖gC (twiddle p n j) - 2 ^ p * Complex.exp (2 * Real.pi * Complex.I * j / n)‖ + 3 := h2
    _ ≤ 2 * 1 * 1 + 3 := by rw [hg]; gcongr; norm_num
    _ = 5 := by norm_num

/-! ### Theorem 3.1 (Bluestein) -/

lemma gC_conjZ (z : ℤ × ℤ) : gC (conjZ z) = (starRingEnd ℂ) (gC z) := by
  simp [gC, conjZ, map_add, map_mul, Complex.conj_I]

end IntMul.HvdH.CCPf

end

-- ===== Solutions.HvdH.FermOracle
section

open Finset Complex

namespace IntMul.HvdH.FOr
open IntMul.HvdH IntMul.HvdH.FP IntMul.HvdH.FCPf IntMul.HvdH.RCv

lemma part_bound (p : ℕ) (z : ℤ × ℤ) (h : ‖gC z‖ ≤ 2 ^ p) :
    |z.1| ≤ (2 : ℤ) ^ p ∧ |z.2| ≤ (2 : ℤ) ^ p := by
  have h1 : |(gC z).re| ≤ ‖gC z‖ := Complex.abs_re_le_norm _
  have h2 : |(gC z).im| ≤ ‖gC z‖ := Complex.abs_im_le_norm _
  simp only [gC] at h1 h2 h
  simp at h1 h2
  constructor
  · have : ((|z.1| : ℤ) : ℝ) ≤ ((2 ^ p : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have : ((|z.2| : ℤ) : ℝ) ≤ ((2 ^ p : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

end IntMul.HvdH.FOr

end

-- ===== Solutions.HvdH.DftAdapt
section

open Finset Complex

namespace IntMul.HvdH.DAd
open IntMul.HvdH

lemma sum_snoc {d : ℕ} (t : Fin d → ℕ) (r : ℕ) (f : (Fin (d + 1) → ℕ) → ℂ) :
    ∑ K ∈ Fintype.piFinset (fun i => range ((Fin.snoc t r : Fin (d + 1) → ℕ) i)), f K =
      ∑ k ∈ Fintype.piFinset (fun i => range (t i)), ∑ c ∈ range r, f (Fin.snoc k c) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun K => (Fin.init K, K (Fin.last d))) (fun kc => Fin.snoc kc.1 kc.2)
    ?_ ?_ ?_ ?_ ?_
  · intro K hK
    have h := Fintype.mem_piFinset.1 hK
    simp only [mem_product, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, ?_⟩
    · have := h i.castSucc; simpa [Fin.init] using this
    · have := h (Fin.last d); simpa using this
  · intro kc hkc
    simp only [mem_product, Fintype.mem_piFinset] at hkc
    simp only [Fintype.mem_piFinset]
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hkc.2
    · simpa using hkc.1 i
  · intro K _; simp
  · intro kc _; simp
  · intro K _; simp

end IntMul.HvdH.DAd

end

-- ===== Solutions.HvdH.Ref.Oracle
section

/-! The list oracles `convL` / `FtL` meet the hypotheses of `bluestein_fp` / `exactConv_eq`. -/

open Finset

namespace IntMul.HvdH.RefPf
open IntMul.HvdH IntMul.HvdH.Ref

/-! ## Lists over a box versus functions on `Fin m → ℕ` -/

/-- extend an index function by zero -/
def natFn {m : ℕ} (x : Fin m → ℕ) : ℕ → ℕ := fun i => if h : i < m then x ⟨i, h⟩ else 0

/-- the list of an array on the box `dims` -/
def toL {m : ℕ} (dims : List ℕ) (U : (Fin m → ℕ) → ℤ × ℤ) : List (ℤ × ℤ) :=
  listOf dims fun j => U fun i => j i

/-- the array of a list on the box `dims` -/
def ofL {m : ℕ} (dims : List ℕ) (L : List (ℤ × ℤ)) : (Fin m → ℕ) → ℤ × ℤ :=
  fun x => L.getD (rmPos dims (natFn x)) (0, 0)

lemma ofFn_mem_boxIdxs {m : ℕ} (dims : List ℕ) (hd : dims.length = m) (g : ℕ → ℕ)
    (hg : ∀ i < m, g i < dims.getD i 1) :
    List.ofFn (fun i : Fin m => g i) ∈ boxIdxs dims := by
  rw [mem_boxIdxs]
  refine ⟨by simp [hd], fun i hi => ?_⟩
  simp only [List.length_ofFn] at hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_ofFn]
  exact hg i hi

lemma ixf_ofFn {m : ℕ} (g : ℕ → ℕ) (hg : ∀ i, m ≤ i → g i = 0) :
    ixf (List.ofFn (fun i : Fin m => g i)) = g := by
  funext i
  by_cases hi : i < m
  · simp [ixf, List.getD_eq_getElem?_getD, hi]
  · rw [hg i (by omega)]; simp [ixf, List.getD_eq_getElem?_getD, hi]

/-- reading a `listOf` at an in-box index function -/
lemma getD_listOf_fn {m : ℕ} {α : Type*} (dims : List ℕ) (hd : dims.length = m)
    (U : (Fin m → ℕ) → α) (d : α) (g : ℕ → ℕ) (hg0 : ∀ i, m ≤ i → g i = 0)
    (hg : ∀ i < m, g i < dims.getD i 1) :
    (listOf dims fun j => U fun i => j i).getD (rmPos dims g) d = U fun i => g i := by
  have hl := ofFn_mem_boxIdxs dims hd g hg
  have := getD_listOf dims (fun j => U fun i => j i) d hl
  rw [ixf_ofFn g hg0] at this
  exact this

lemma natFn_zero {m : ℕ} (x : Fin m → ℕ) : ∀ i, m ≤ i → natFn x i = 0 := by
  intro i hi; simp [natFn, show ¬ i < m by omega]

lemma natFn_val {m : ℕ} (x : Fin m → ℕ) (i : Fin m) : natFn x i = x i := by simp [natFn]

lemma listOf_congr {α : Type*} (dims : List ℕ) (f g : (ℕ → ℕ) → α)
    (h : ∀ l ∈ boxIdxs dims, f (ixf l) = g (ixf l)) : listOf dims f = listOf dims g := by
  unfold listOf; exact List.map_congr_left h

lemma toL_ofL {m : ℕ} (dims : List ℕ) (hd : dims.length = m) (L : List (ℤ × ℤ))
    (hL : L.length = dims.prod) : toL dims (ofL (m := m) dims L) = L := by
  have hself : L = listOf dims (fun j => L.getD (rmPos dims j) (0, 0)) := by
    apply List.ext_getElem (by rw [length_listOf, hL])
    intro k h1 h2
    rw [length_listOf] at h2
    have hk : k < (boxIdxs dims).length := by rw [length_boxIdxs]; exact h2
    set l := (boxIdxs dims)[k]
    have hl : l ∈ boxIdxs dims := List.getElem_mem hk
    have hk' : rmPos dims (ixf l) = k := by
      obtain ⟨_, heq⟩ := List.getElem?_eq_some_iff.1 (getElem?_rmPos hl)
      exact (List.Nodup.getElem_inj_iff (nodup_boxIdxs dims)).1 heq
    simp only [listOf, List.getElem_map]
    show L[k] = L.getD (rmPos dims (ixf l)) (0, 0)
    rw [hk', List.getD_eq_getElem _ _ h1]
  conv_rhs => rw [hself]
  unfold toL ofL
  apply listOf_congr
  intro l hl
  have hlen : l.length = m := by rw [(mem_boxIdxs.1 hl).1, hd]
  congr 2
  funext i
  by_cases hi : i < m
  · simp [natFn, hi]
  · simp only [natFn, hi, dite_false, ixf]
    rw [List.getD_eq_default _ _ (by omega)]

lemma toL_length {m : ℕ} (dims : List ℕ) (U : (Fin m → ℕ) → ℤ × ℤ) : (toL dims U).length = dims.prod := by
  simp [toL, length_listOf]

lemma ofL_toL {m : ℕ} (dims : List ℕ) (hd : dims.length = m) (U : (Fin m → ℕ) → ℤ × ℤ)
    (x : Fin m → ℕ) (hx : ∀ i, x i < dims.getD i 1) : ofL dims (toL dims U) x = U x := by
  unfold ofL toL
  rw [getD_listOf_fn dims hd U _ _ (natFn_zero x) (fun i hi => by
    have := hx ⟨i, hi⟩; simpa [natFn, hi] using this)]
  congr 1; funext i; exact natFn_val x i

/-- sums over `boxIdxs` as sums over `piFinset` -/
lemma sum_boxIdxs_piFinset {m : ℕ} {M : Type*} [AddCommMonoid M] (dims : List ℕ) (hd : dims.length = m)
    (g : List ℕ → M) :
    ((boxIdxs dims).map g).sum =
      ∑ k ∈ Fintype.piFinset (fun i : Fin m => range (dims.getD i 1)), g (List.ofFn k) := by
  have hof : ∀ l ∈ boxIdxs dims, List.ofFn (fun i : Fin m => l.getD i 0) = l := by
    intro l hl
    have hl' := mem_boxIdxs.1 hl
    apply List.ext_getElem (by simp [hl'.1, hd])
    intro i h1 h2
    simp only [List.getElem_ofFn]
    rw [List.getD_eq_getElem _ _ h2]
  rw [← List.sum_toFinset _ (nodup_boxIdxs dims)]
  refine Finset.sum_nbij' (fun l => fun i : Fin m => l.getD i 0) (fun k => List.ofFn k) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    have hl' := mem_boxIdxs.1 (List.mem_toFinset.1 hl)
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
    intro i
    exact hl'.2 i (by rw [hl'.1, hd]; exact i.2)
  · intro k hk
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range] at hk
    simp only [Finset.mem_coe, List.mem_toFinset]
    exact ofFn_mem_boxIdxs dims hd (natFn k) (fun i hi => by simpa [natFn, hi] using hk ⟨i, hi⟩) |>
      fun h => by
        have : (fun i : Fin m => natFn k i) = k := by funext i; exact natFn_val k i
        rwa [this] at h
  · intro l hl
    exact hof l (List.mem_toFinset.1 (Finset.mem_coe.1 hl))
  · intro k _
    funext i
    simp [List.getD_eq_getElem?_getD]
  · intro l hl; rw [hof l (List.mem_toFinset.1 hl)]

lemma gC_add (a b : ℤ × ℤ) : gC (a + b) = gC a + gC b := by
  simp only [gC, Prod.fst_add, Prod.snd_add]; push_cast; ring

lemma gC_zero : gC (0 : ℤ × ℤ) = 0 := by simp [gC]

lemma gC_list_sum {ι : Type*} (L : List ι) (f : ι → ℤ × ℤ) : gC (L.map f).sum = (L.map fun x => gC (f x)).sum := by
  induction L with
  | nil => simp [gC_zero]
  | cons a L ih => simp [gC_add, ih]

lemma gC_gmul (a b : ℤ × ℤ) : gC (gmul a b) = gC a * gC b := by
  simp only [gC, gmul]; push_cast; ring_nf; rw [Complex.I_sq]; ring

lemma gC_gconv {m : ℕ} (dims : List ℕ) (hd : dims.length = m)
    (U V : (Fin m → ℕ) → ℤ × ℤ) (j : Fin m → ℕ) (hj : ∀ i, j i < dims.getD i 1) :
    gC (gconv dims (toL dims U) (toL dims V) (natFn j)) =
      ∑ k ∈ Fintype.piFinset (fun i : Fin m => range (dims.getD i 1)),
        gC (U k) * gC (V fun i => (j i + dims.getD i 1 - k i) % dims.getD i 1) := by
  unfold gconv
  rw [gC_list_sum, sum_boxIdxs_piFinset dims hd]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Fintype.mem_piFinset] at hk
  simp only [Finset.mem_range] at hk
  rw [gC_gmul]
  have hk' : List.ofFn k = List.ofFn (fun i : Fin m => natFn k i) := by
    congr 1; funext i; exact (natFn_val k i).symm
  have hix : ixf (List.ofFn k) = natFn k := by rw [hk', ixf_ofFn _ (natFn_zero k)]
  congr 2
  · unfold toL
    rw [hix, getD_listOf_fn dims hd U _ _ (natFn_zero k) (fun i hi => by simpa [natFn, hi] using hk ⟨i, hi⟩)]
    congr 1; funext i; exact natFn_val k i
  · unfold toL
    have hdflt : ∀ i, m ≤ i → dims.getD i 1 = 1 := by
      intro i hi; rw [List.getD_eq_default _ _ (by omega)]
    rw [getD_listOf_fn dims hd V _ _ (fun i hi => by
        rw [natFn_zero j i hi, hdflt i hi]; simp [Nat.mod_one])
      (fun i hi => by have h := hj ⟨i, hi⟩; simp only [Fin.val_mk] at h; exact Nat.mod_lt _ (by omega))]
    congr 1; funext i
    rw [natFn_val j i]
    congr 2
    show ixf (List.ofFn k) i = k i
    rw [hix, natFn_val k i]

/-! ## Parameter facts -/

lemma tdims_length (q : Params) : q.tdims.length = q.K := by simp [Params.tdims]

lemma tdims_getD (q : Params) (i : ℕ) (hi : i < q.K) : q.tdims.getD i 1 = 2 ^ q.te i := by
  rw [List.getD_eq_getElem?_getD]; simp [Params.tdims, hi]

lemma tdims_snoc (q : Params) (d : ℕ) (hK : q.K = d + 1) (hdh : q.dh < q.K) :
    (fun i : Fin (d + 1) => q.tdims.getD i 1) = Fin.snoc (fun i : Fin d => 2 ^ q.te i) q.r := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Fin.snoc_last, tdims_getD q _ (by simp [hK]), Params.r]
    unfold Params.te; rw [if_neg (by simp; omega)]
  · rw [Fin.snoc_castSucc, tdims_getD q _ (by simp only [Fin.coe_castSucc]; omega)]; rfl

lemma logOuter_eq (q : Params) (d : ℕ) (hK : q.K = d + 1) : q.logOuter = ∑ i : Fin d, q.te i := by
  simp only [Params.logOuter, hK, Nat.add_sub_cancel]
  rw [Fin.sum_univ_eq_sum_range (fun i => q.te i) d, ← list_sum_range]

lemma logT_eq (q : Params) (d : ℕ) (hK : q.K = d + 1) (hdh : q.dh < q.K) :
    q.logT = ∑ i : Fin d, q.te i + q.e := by
  rw [← logOuter_eq q d hK]
  simp only [Params.logT, Params.logOuter, hK, Nat.add_sub_cancel, List.range_succ, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  congr 1
  unfold Params.te; rw [if_neg (by omega)]

lemma tdims_prod (q : Params) (d : ℕ) (hK : q.K = d + 1) (hdh : q.dh < q.K) :
    q.tdims.prod = 2 ^ q.logT := by
  rw [Params.tdims, Params.logT]
  induction (List.range q.K) with
  | nil => simp
  | cons a L ih => simp [ih, pow_add]

/-! ## The convolution oracle -/

/-- the convolution oracle as a function on the target box -/
def Mq (q : Params) (d : ℕ) (U V : (Fin (d + 1) → ℕ) → ℤ × ℤ) : (Fin (d + 1) → ℕ) → ℤ × ℤ :=
  ofL q.tdims (convL q (toL q.tdims U) (toL q.tdims V))

theorem Mq_spec (q : Params) (d : ℕ) (hK : q.K = d + 1) (he : 1 ≤ q.e) (hdh : q.dh < q.K)
    (hP : 1 ≤ q.P) (hlog : q.logOuter ≤ 2 * q.fn)
    (hPM : 4 * (q.tdims.prod : ℤ) * ((2 : ℤ) ^ q.p) ^ 2 < 2 ^ q.P) :
    ∀ U V : (Fin (d + 1) → ℕ) → ℤ × ℤ,
      (∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ q.te i) → x (Fin.last d) < q.r →
        ‖gC (U x)‖ ≤ 2 ^ q.p) →
      (∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ q.te i) → x (Fin.last d) < q.r →
        ‖gC (V x)‖ ≤ 2 ^ q.p) →
      ∀ j : Fin (d + 1) → ℕ, (∀ i : Fin d, j i.castSucc < 2 ^ q.te i) → j (Fin.last d) < q.r →
        ‖gC (Mq q d U V j)‖ ≤ 2 ^ q.p ∧
        ‖gC (Mq q d U V j) - 2 ^ q.p *
          convC q.r (fun i : Fin d => q.te i) (fun x => gC (U x) / 2 ^ q.p)
            (fun x => gC (V x) / 2 ^ q.p) j‖ ≤ Real.sqrt 2 := by
  intro U V hU hV j hj hc
  have hlen := tdims_length q
  have hsn := tdims_snoc q d hK hdh
  -- in-box in list terms
  have inbox : ∀ x : Fin (d + 1) → ℕ, (∀ i : Fin (d + 1), x i < q.tdims.getD i 1) ↔
      ((∀ i : Fin d, x i.castSucc < 2 ^ q.te i) ∧ x (Fin.last d) < q.r) := by
    intro x
    constructor
    · intro h
      refine ⟨fun i => ?_, ?_⟩
      · have := h i.castSucc; rw [show q.tdims.getD (i.castSucc : ℕ) 1 = _ from congrFun hsn i.castSucc,
          Fin.snoc_castSucc] at this; exact this
      · have := h (Fin.last d); rw [show q.tdims.getD ((Fin.last d : Fin (d+1)) : ℕ) 1 = _ from
          congrFun hsn (Fin.last d), Fin.snoc_last] at this; exact this
    · rintro ⟨h1, h2⟩ i
      rw [show q.tdims.getD (i : ℕ) 1 = _ from congrFun hsn i]
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [Fin.snoc_last]; exact h2
      · rw [Fin.snoc_castSucc]; exact h1 i
  have hjb := (inbox j).2 ⟨hj, hc⟩
  -- entry bounds of the lists
  have hbnd : ∀ (W : (Fin (d + 1) → ℕ) → ℤ × ℤ),
      (∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ q.te i) → x (Fin.last d) < q.r →
        ‖gC (W x)‖ ≤ 2 ^ q.p) → ∀ z ∈ toL q.tdims W, |z.1| ≤ 2 ^ q.p ∧ |z.2| ≤ 2 ^ q.p := by
    intro W hW z hz
    simp only [toL, listOf, List.mem_map] at hz
    obtain ⟨l, hl, rfl⟩ := hz
    have hl' := mem_boxIdxs.1 hl
    have hx : ∀ i : Fin (d + 1), ixf l i < q.tdims.getD i 1 := by
      intro i; exact hl'.2 i (by rw [hl'.1, hlen, hK]; exact i.2)
    obtain ⟨h1, h2⟩ := (inbox _).1 hx
    exact FOr.part_bound q.p _ (hW _ h1 h2)
  have hFW := fermatW_eq q (by omega) he hdh hP hlog (toL q.tdims U) (toL q.tdims V) (toL_length _ _)
    (toL_length _ _) _ (by positivity) (hbnd U hU) (hbnd V hV) hPM
  -- the entry of the oracle
  have hN : ((2 ^ (q.p + q.logT) : ℕ) : ℤ) = ((2 ^ q.p * (q.r * 2 ^ (∑ i : Fin d, q.te i)) : ℕ) : ℤ) := by
    rw [logT_eq q d hK hdh, Params.r]; push_cast; ring
  have hMj : Mq q d U V j = ((gconv q.tdims (toL q.tdims U) (toL q.tdims V) (natFn j)).1.tdiv
      ((2 ^ q.p * (q.r * 2 ^ (∑ i : Fin d, q.te i)) : ℕ) : ℤ),
      (gconv q.tdims (toL q.tdims U) (toL q.tdims V) (natFn j)).2.tdiv
      ((2 ^ q.p * (q.r * 2 ^ (∑ i : Fin d, q.te i)) : ℕ) : ℤ)) := by
    unfold Mq ofL convL
    rw [hFW, ← hN]
    have hl := ofFn_mem_boxIdxs q.tdims (by rw [hlen, hK]) (natFn j)
      (fun i hi => by simpa [natFn, hi] using hjb ⟨i, hi⟩)
    have hix : ixf (List.ofFn fun i : Fin (d + 1) => natFn j i) = natFn j := ixf_ofFn _ (natFn_zero j)
    have hlt : rmPos q.tdims (natFn j) < (listOf q.tdims (gconv q.tdims (toL q.tdims U) (toL q.tdims V))).length := by
      rw [length_listOf, ← hix]; exact rmPos_lt hl
    rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map,
      ← List.getD_eq_getElem _ (0, 0) hlt]
    have := getD_listOf q.tdims (gconv q.tdims (toL q.tdims U) (toL q.tdims V)) (0, 0) hl
    rw [hix] at this
    rw [this]
  rw [hMj]
  apply IntMul.HvdH.convC_round q.p q.r (fun i : Fin d => q.te i) (by simp [Params.r]) U V hU hV j
    (W := fun j => gconv q.tdims (toL q.tdims U) (toL q.tdims V) (natFn j))
  -- the exact convolution identity
  show gC (gconv q.tdims (toL q.tdims U) (toL q.tdims V) (natFn j)) = _
  rw [gC_gconv q.tdims (by rw [hlen, hK]) U V j hjb]
  have hsum := DAd.sum_snoc (fun i : Fin d => 2 ^ q.te i) q.r (fun k =>
    gC (U k) * gC (V fun i => (j i + q.tdims.getD i 1 - k i) % q.tdims.getD i 1))
  rw [← hsn] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro c _
  congr 3
  funext i
  rw [show q.tdims.getD (i : ℕ) 1 = _ from congrFun hsn i]
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [Fin.snoc_last]
  · simp [Fin.snoc_castSucc]

/-! ## The DFT oracle -/

lemma zipWith_listOf {α β γ : Type*} (dims : List ℕ) (f : α → β → γ) (a : (ℕ → ℕ) → α) (b : (ℕ → ℕ) → β) :
    List.zipWith f (listOf dims a) (listOf dims b) = listOf dims fun j => f (a j) (b j) := by
  unfold listOf
  induction boxIdxs dims with
  | nil => rfl
  | cons l L ih => simp [ih]

/-- the chirp as a function on the target box -/
def Aq (q : Params) (d : ℕ) : (Fin (d + 1) → ℕ) → ℤ × ℤ :=
  fun j => twD q.p (2 * q.r) (chirpIdx q.r (fun i : Fin d => q.te i) j)

lemma chirpL_eq (q : Params) (d : ℕ) (hK : q.K = d + 1) : chirpL q = toL q.tdims (Aq q d) := by
  unfold chirpL toL Aq
  congr 1; funext j
  congr 2
  unfold chirpIdxL chirpIdx
  rw [hK, Nat.add_sub_cancel, list_sum_range, ← Fin.sum_univ_eq_sum_range (fun i => q.r / 2 ^ q.te i * j i ^ 2) d]
  simp

/-- the DFT oracle as a function on the target box -/
def Ftq (q : Params) (d : ℕ) (U : (Fin (d + 1) → ℕ) → ℤ × ℤ) : (Fin (d + 1) → ℕ) → ℤ × ℤ :=
  ofL q.tdims (FtL q (toL q.tdims U))

theorem Ftq_spec (q : Params) (d : ℕ) (hK : q.K = d + 1) (he : 2 ≤ q.e) (hdh : q.dh < q.K)
    (hP : 1 ≤ q.P) (hlog : q.logOuter ≤ 2 * q.fn)
    (hPM : 4 * (q.tdims.prod : ℤ) * ((2 : ℤ) ^ q.p) ^ 2 < 2 ^ q.P)
    (U : (Fin (d + 1) → ℕ) → ℤ × ℤ) (hU : InDisc q.p U)
    (j : Fin (d + 1) → ℕ) (hj : ∀ i, j i < (Fin.snoc (fun i : Fin d => 2 ^ q.te i) q.r : Fin (d + 1) → ℕ) i) :
    ‖gC (Ftq q d U j)‖ ≤ 2 ^ q.p ∧
    ‖gC (Ftq q d U j) - 2 ^ q.p * dftBox (Fin.snoc (fun i : Fin d => 2 ^ q.te i) q.r)
      (fun x => gC (U x) / 2 ^ q.p) j‖ ≤ Real.sqrt 2 + 3 * 5 + 3 := by
  have hlen := tdims_length q
  have hsn := tdims_snoc q d hK hdh
  have hj1 : ∀ i : Fin d, j i.castSucc < 2 ^ q.te i := fun i => by simpa using hj i.castSucc
  have hj2 : j (Fin.last d) < q.r := by simpa using hj (Fin.last d)
  have hjb : ∀ i : Fin (d + 1), j i < q.tdims.getD i 1 := fun i => by rw [congrFun hsn i]; exact hj i
  have hr : 1 ≤ q.r := Nat.one_le_two_pow
  have hAb : ∀ x : Fin (d + 1) → ℕ, ‖gC (Aq q d x)‖ ≤ 2 ^ q.p := fun x =>
    (CCPf.twD_bound q.p (2 * q.r) _ (by omega)).1
  set Xf : (Fin (d + 1) → ℕ) → ℤ × ℤ := fun k => mulZ q.p (conjZ (Aq q d k)) (U k)
  have hXb : ∀ x, ‖gC (Xf x)‖ ≤ 2 ^ q.p := by
    intro x
    exact IntMul.HvdH.mulZ_disc q.p _ _ (by rw [CCPf.gC_conjZ, Complex.norm_conj]; exact hAb x) (hU x)
  have hconv : convL q (toL q.tdims Xf) (toL q.tdims (Aq q d)) = toL q.tdims (Mq q d Xf (Aq q d)) := by
    unfold Mq
    rw [toL_ofL q.tdims (by rw [hlen, hK])]
    have hbnd : ∀ (W : (Fin (d + 1) → ℕ) → ℤ × ℤ), (∀ x, ‖gC (W x)‖ ≤ 2 ^ q.p) →
        ∀ z ∈ toL q.tdims W, |z.1| ≤ 2 ^ q.p ∧ |z.2| ≤ 2 ^ q.p := by
      intro W hW z hz
      simp only [toL, listOf, List.mem_map] at hz
      obtain ⟨l, _, rfl⟩ := hz
      exact FOr.part_bound q.p _ (hW _)
    unfold convL
    rw [fermatW_eq q (by omega) (by omega) hdh hP hlog _ _ (toL_length _ _) (toL_length _ _) _
      (by positivity) (hbnd _ hXb) (hbnd _ hAb) hPM]
    simp [length_listOf]
  have hFt : FtL q (toL q.tdims U) =
      toL q.tdims (fun j => mulZ q.p (conjZ (Aq q d j)) (Mq q d Xf (Aq q d) j)) := by
    unfold FtL
    simp only
    rw [chirpL_eq q d hK]
    have hX : List.zipWith (fun a u => mulZ q.p (conjZ a) u) (toL q.tdims (Aq q d)) (toL q.tdims U) =
        toL q.tdims Xf := by
      unfold toL; rw [zipWith_listOf]
    rw [hX, hconv]
    unfold toL; rw [zipWith_listOf]
  have hval : Ftq q d U j = mulZ q.p (conjZ (Aq q d j)) (Mq q d Xf (Aq q d) j) := by
    unfold Ftq; rw [hFt, ofL_toL q.tdims (by rw [hlen, hK]) _ j (fun i => hjb i)]
  rw [hval, ← IntMul.HvdH.dftC_eq_dftBox q.r _ _ j hj1 hj2]
  have hhe1 : ∀ i : Fin d, 1 ≤ q.te i := by
    intro i; unfold Params.te; split_ifs <;> omega
  have hhe : ∀ i : Fin d, 2 ^ q.te i ∣ q.r := fun i => pow_dvd_pow 2 (te_le q i)
  have hr2 : Even q.r := by
    simp only [Params.r]; exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
  exact IntMul.HvdH.bluestein_fp q.p q.r (fun i : Fin d => q.te i) hr hr2 hhe1 hhe (Mq q d) (Real.sqrt 2)
    (Mq_spec q d hK (by omega) hdh hP hlog hPM) (Aq q d) 5
    (fun x _ _ => CCPf.twD_bound q.p (2 * q.r) _ (by omega)) U (fun x _ _ => hU x) j hj1 hj2

end IntMul.HvdH.RefPf

end

-- ===== Solutions.HvdH.Ref.TGo
section

namespace IntMul.HvdH.RefPf

open IntMul.HvdH IntMul.HvdH.Ref

lemma map_rmPos_boxIdxs (rest : List ℕ) :
    (boxIdxs rest).map (fun l => rmPos rest (ixf l)) = List.range rest.prod := by
  apply List.ext_getElem (by simp [length_boxIdxs])
  intro p h1 h2
  simp only [List.getElem_map, List.getElem_range]
  have hp : p < (boxIdxs rest).length := by simpa using h1
  have hmem : (boxIdxs rest)[p] ∈ boxIdxs rest := List.getElem_mem _
  have h := getElem?_rmPos hmem
  have hlt' : rmPos rest (ixf (boxIdxs rest)[p]) < (boxIdxs rest).length := by
    rw [length_boxIdxs]; exact rmPos_lt hmem
  rw [List.getElem?_eq_getElem hlt', Option.some_inj] at h
  exact (nodup_boxIdxs rest).getElem_inj_iff.1 h

lemma tensor_step (n n' : ℕ) (hn : 0 < n) (rest : List ℕ) (B : (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ))
    (hB : ∀ U U' : ℕ → ℤ × ℤ, (∀ j < n, U j = U' j) → B U = B U')
    (f f' : (ℕ → ℕ) → ℤ × ℤ)
    (hf : ∀ l ∈ boxIdxs rest, ∀ c < n', f' (ixf (l ++ [c])) = B (fun k => f (ixf (k :: l))) c) :
    (chunkL n (transposeL n rest.prod (listOf (n :: rest) f))).flatMap
      (fun X : List (ℤ × ℤ) => (List.range n').map (B fun j => X.getD j (0, 0))) =
    listOf (rest ++ [n']) f' := by
  have hT : (transposeL n rest.prod (listOf (n :: rest) f)).length = rest.prod * n :=
    transposeL_length _ _ _
  rw [chunkL_eq n rest.prod hn _ hT, listOf_snoc, ← map_rmPos_boxIdxs rest]
  simp only [List.flatMap_def, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  simp only [Function.comp_apply]
  apply List.map_congr_left
  intro c hc
  rw [hf l hl c (List.mem_range.1 hc)]
  refine congrFun (hB _ _ ?_) c
  intro j hj
  have hp := rmPos_lt hl
  set p := rmPos rest (ixf l)
  have e1 : (((transposeL n rest.prod (listOf (n :: rest) f)).drop (p * n)).take n).getD j (0, 0)
      = (transposeL n rest.prod (listOf (n :: rest) f)).getD (p * n + j) (0, 0) := by
    simp [List.getD_eq_getElem?_getD, hj]
  have hq : p * n + j < rest.prod * n := by nlinarith
  have e2 := transposeL_getD n rest.prod (listOf (n :: rest) f) (p * n + j) hq
  simp only [show (default : ℤ × ℤ) = (0, 0) from rfl] at e2
  rw [e1, e2, show p * n + j = j + n * p by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj,
    Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hj, zero_add, ← rmPos_cons n rest j l]
  exact getD_listOf _ _ _ ((mem_boxIdxs_cons n rest _).2 ⟨j, hj, l, hl, rfl⟩)

/-- the list of steps fed to `tensorGo` -/
def tgSteps (K : ℕ) (ns' : List ℕ) (A : ℕ → (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ)) :
    List (ℕ × (List (ℤ × ℤ) → List (ℤ × ℤ))) :=
  (List.range K).map fun i => (ns'.getD i 1, fun X : List (ℤ × ℤ) =>
    (List.range (ns'.getD i 1)).map (A i fun j => X.getD j (0, 0)))

lemma rot_arith (K m i : ℕ) (hm : m < K) (hi : i < K) (hne : i ≠ m) :
    (i + K - m) % K = (i + K - (m + 1)) % K + 1 ∧ (i + K - (m + 1)) % K < K - 1 := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · rw [Nat.mod_eq_of_lt (by omega : i + K - m < K), Nat.mod_eq_of_lt (by omega : i + K - (m+1) < K)]
    omega
  · rw [show i + K - m = (i - m) + K by omega, show i + K - (m + 1) = (i - (m + 1)) + K by omega,
      Nat.add_mod_right, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i - m < K),
      Nat.mod_eq_of_lt (by omega : i - (m + 1) < K)]
    omega

theorem tensorGo_stage (K : ℕ) (ns ns' : List ℕ) (hns : ns.length = K) (hns' : ns'.length = K)
    (hpos : ∀ i < K, 0 < ns.getD i 1)
    (A : ℕ → (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ))
    (hloc : ∀ i < K, ∀ U U' : ℕ → ℤ × ℤ, (∀ j < ns.getD i 1, U j = U' j) → A i U = A i U') :
    ∀ t m, m + t = K → ∀ h : (Fin K → ℕ) → ℤ × ℤ,
      tensorGo ((tgSteps K ns' A).drop m) (ns.drop m ++ ns'.take m)
        (listOf (ns.drop m ++ ns'.take m) fun j => h fun i => j ((i.val + K - m) % K)) =
      listOf ns' fun j => sliceCompZ (fun i : Fin K => A i) ((List.finRange K).drop m) h
        fun i => j i := by
  intro t
  induction t with
  | zero =>
    intro m hm h
    obtain rfl : m = K := by omega
    have h1 : (tgSteps m ns' A).drop m = [] := List.drop_eq_nil_of_le (by simp [tgSteps])
    have h2 : (List.finRange m).drop m = [] := List.drop_eq_nil_of_le (by simp)
    rw [h1, h2, List.drop_eq_nil_of_le (by omega), List.take_of_length_le (by omega),
      List.nil_append, tensorGo]
    congr 1
    funext j
    congr 1
    funext i
    rw [Nat.add_sub_cancel, Nat.mod_eq_of_lt i.2]
  | succ t ih =>
    intro m hmt h
    have hm : m < K := by omega
    have hdm : ns.drop m = ns.getD m 1 :: ns.drop (m + 1) := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.drop_eq_getElem_cons (by omega)
    have hsm : (tgSteps K ns' A).drop m = (ns'.getD m 1, fun X : List (ℤ × ℤ) =>
        (List.range (ns'.getD m 1)).map (A m fun j => X.getD j (0, 0))) ::
        (tgSteps K ns' A).drop (m + 1) := by
      rw [List.drop_eq_getElem_cons (by simp [tgSteps]; omega)]
      simp [tgSteps]
    have hfm : (List.finRange K).drop m = ⟨m, hm⟩ :: (List.finRange K).drop (m + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; omega)]
      simp
    have hD : ns.drop (m + 1) ++ ns'.take m ++ [ns'.getD m 1] = ns.drop (m + 1) ++ ns'.take (m + 1) := by
      rw [List.append_assoc, List.take_add_one, List.getElem?_eq_getElem (by omega),
        List.getD_eq_getElem _ _ (by omega)]
      rfl
    have hlenR : (ns.drop (m + 1) ++ ns'.take m).length = K - 1 := by
      simp [hns, hns']; omega
    rw [hsm, hdm, List.cons_append, tensorGo, hfm]
    rw [tensor_step (ns.getD m 1) (ns'.getD m 1) (hpos m hm) _ (A m) (hloc m hm) _
      (fun j => sliceMapZ ⟨m, hm⟩ (A m) h fun i => j ((i.val + K - (m + 1)) % K)), hD]
    · exact ih (m + 1) (by omega) _
    · intro l hl c hc
      have hl' : l.length = K - 1 := by rw [(mem_boxIdxs.1 hl).1, hlenR]
      simp only [sliceMapZ]
      have hx : (m + K - (m + 1)) % K = l.length := by
        rw [hl', Nat.mod_eq_of_lt (by omega)]; omega
      rw [hx, ixf_snoc_len]
      congr 1
      funext k
      congr 1
      funext i
      by_cases hi : i = ⟨m, hm⟩
      · subst hi
        rw [Function.update_self]
        simp [ixf]
      · rw [Function.update_of_ne hi]
        have hne : i.val ≠ m := fun e => hi (Fin.ext e)
        obtain ⟨e1, e2⟩ := rot_arith K m i.val hm i.2 hne
        rw [e1, ixf_snoc_lt l c _ (by omega)]
        exact (congrFun (ixf_cons_succ k l) _).symm

theorem tensorGo_eq (K : ℕ) (ns ns' : List ℕ) (hns : ns.length = K) (hns' : ns'.length = K)
    (hpos : ∀ i < K, 0 < ns.getD i 1)
    (A : ℕ → (ℕ → ℤ × ℤ) → (ℕ → ℤ × ℤ))
    (hloc : ∀ i < K, ∀ U U' : ℕ → ℤ × ℤ, (∀ j < ns.getD i 1, U j = U' j) → A i U = A i U')
    (g : (Fin K → ℕ) → ℤ × ℤ) :
    tensorGo ((List.range K).map fun i => (ns'.getD i 1, fun X : List (ℤ × ℤ) =>
        (List.range (ns'.getD i 1)).map (A i fun j => X.getD j (0, 0))))
      ns (listOf ns fun j => g fun i => j i) =
    listOf ns' fun j => tensorMapZ (fun i : Fin K => A i) g fun i => j i := by
  have := tensorGo_stage K ns ns' hns hns' hpos A hloc K 0 (by omega) g
  simp only [List.drop_zero, List.take_zero, List.append_nil, Nat.sub_zero] at this
  have e : (fun j : ℕ → ℕ => g fun i : Fin K => j ((i.val + K) % K)) = fun j => g fun i => j i := by
    funext j; congr 1; funext i; rw [Nat.add_mod_right, Nat.mod_eq_of_lt i.2]
  rw [e] at this
  exact this

end IntMul.HvdH.RefPf

end

-- ===== Solutions.HvdH.ExactMain
section

open Finset Complex

namespace IntMul.HvdH.ExMain
open IntMul.HvdH IntMul.HvdH.TKer IntMul.HvdH.ExId IntMul.HvdH.BoxConv IntMul.HvdH.ExPf

lemma gC_conjZ (z : ℤ × ℤ) : gC (conjZ z) = (starRingEnd ℂ) (gC z) := by
  simp [gC, conjZ, map_add, map_mul, Complex.conj_I]

end IntMul.HvdH.ExMain

end

-- ===== Solutions.HvdH.Ref.ExactL
section

/-! `exactConvL` is `exactConv` with the oracle `Ftq`, read on the source box. -/

open Finset

namespace IntMul.HvdH.RefPf
open IntMul.HvdH IntMul.HvdH.Ref

lemma length_fermatW (q : Params) (hK : 1 ≤ q.K) (hdh : q.dh < q.K) (U V : List (ℤ × ℤ))
    (hU : U.length = q.tdims.prod) (hV : V.length = q.tdims.prod) :
    (fermatW q U V).length = q.tdims.prod := by
  have hsplit := tdims_split q hK hdh
  have hprod : q.tdims.prod = blockSize q.outerAxes * q.r := by
    rw [hsplit, List.prod_append, blockSize_eq]; simp
  have hr0 : 0 < q.r := Nat.one_le_two_pow
  rw [hprod] at hU hV ⊢
  have hchU : (chunkL q.r U).length = blockSize q.outerAxes := by
    rw [chunkL_eq q.r _ hr0 U hU]; simp
  have hchV : (chunkL q.r V).length = blockSize q.outerAxes := by
    rw [chunkL_eq q.r _ hr0 V hV]; simp
  have hRel := mdit_pmul_mdif q.fn q.outerAxes (by simpa [Params.fn] using outer_hax q)
    ((chunkL q.r U).map fun blk => encBlk q.P q.r blk % q.F)
    ((chunkL q.r V).map fun blk => encBlk q.P q.r blk % q.F) (by simp [hchU]) (by simp [hchV])
  have hCl := ((relC_iff _ _ _ _).1 hRel).1
  rw [length_listOf, ← blockSize_eq] at hCl
  unfold fermatW
  simp only [Params.F] at hCl ⊢
  rw [List.length_flatMap]
  have hdec : ∀ z, (decBlk (2 ^ q.fn + 1) q.P q.r z).length = q.r := by simp [decBlk]
  simp only [hdec, List.map_map, Function.comp_def, List.map_const', List.sum_replicate,
    List.length_map, hCl, smul_eq_mul]

lemma length_FtL (q : Params) (hK : 1 ≤ q.K) (hdh : q.dh < q.K) (U : List (ℤ × ℤ))
    (hU : U.length = q.tdims.prod) : (FtL q U).length = q.tdims.prod := by
  have hA : (chirpL q).length = q.tdims.prod := by simp [chirpL, length_listOf]
  have hX : (List.zipWith (fun a u => mulZ q.p (conjZ a) u) (chirpL q) U).length = q.tdims.prod := by
    simp [hA, hU]
  unfold FtL convL
  simp [hA, length_fermatW q hK hdh _ _ hX hA]

lemma sapprox_loc (p s t α : ℕ) (hs : 0 < s) (U U' : ℕ → ℤ × ℤ) (h : ∀ j < s, U j = U' j) :
    Sapprox p s t α U = Sapprox p s t α U' := by
  funext k
  have e : ∀ j : ℤ, sTerm p s t α k U j = sTerm p s t α k U' j := by
    intro j
    have h0 : 0 ≤ j % (s : ℤ) := Int.emod_nonneg _ (by omega)
    have h1 : j % (s : ℤ) < s := Int.emod_lt_of_pos _ (by omega)
    unfold sTerm
    rw [h _ (by generalize j % (s : ℤ) = m at h0 h1 ⊢; omega)]
  unfold Sapprox; simp only [e]

lemma bapprox_loc (p s t α : ℕ) (ht : 0 < t) (U U' : ℕ → ℤ × ℤ) (h : ∀ j < t, U j = U' j) :
    Bapprox p s t α U = Bapprox p s t α U' := by
  have : NeZero t := ⟨by omega⟩
  have e : ptPerm s t U = ptPerm s t U' := by
    funext k; unfold ptPerm; exact h _ (ZMod.val_lt _)
  unfold Bapprox; rw [e]

/-- the source lengths as a function -/
abbrev sF (q : Params) (d : ℕ) : Fin (d + 1) → ℕ := fun i => q.s.getD i 1
/-- the target lengths as a function -/
abbrev tF (q : Params) (d : ℕ) : Fin (d + 1) → ℕ := fun i => 2 ^ q.te i

theorem fwdL_eq (q : Params) (d : ℕ) (hK : q.K = d + 1) (hdh : q.dh < q.K)
    (hslen : q.s.length = q.K) (hspos : ∀ i < q.K, 0 < q.s.getD i 1)
    (U : (Fin (d + 1) → ℕ) → ℤ × ℤ) :
    fwdL q (toL q.s U) = toL q.s (fwdZ q.p q.α (sF q d) (tF q d) (Ftq q d) U) := by
  have htl := tdims_length q
  have hS : ((List.range q.K).map fun i =>
      (2 ^ q.te i, sapL q.p (q.s.getD i 1) (2 ^ q.te i) q.α)) =
      (List.range (d + 1)).map fun i => (q.tdims.getD i 1, fun X : List (ℤ × ℤ) =>
        (List.range (q.tdims.getD i 1)).map
          ((fun i => Sapprox q.p (q.s.getD i 1) (2 ^ q.te i) q.α) i fun j => X.getD j (0, 0))) := by
    rw [← hK]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [tdims_getD q i hi]; rfl
  have hB : ((List.range q.K).map fun i =>
      (q.s.getD i 1, bapL q.p (q.s.getD i 1) (2 ^ q.te i) q.α)) =
      (List.range (d + 1)).map fun i => (q.s.getD i 1, fun X : List (ℤ × ℤ) =>
        (List.range (q.s.getD i 1)).map
          ((fun i => Bapprox q.p (q.s.getD i 1) (2 ^ q.te i) q.α) i fun j => X.getD j (0, 0))) := by
    rw [← hK]; rfl
  unfold fwdL
  simp only
  rw [hS, hB]
  have hsd : q.sdims = q.s := rfl
  rw [hsd]
  unfold toL
  rw [tensorGo_eq (d + 1) q.s q.tdims (by omega) (by omega) (fun i hi => hspos i (by omega))
    (fun i => Sapprox q.p (q.s.getD i 1) (2 ^ q.te i) q.α) (fun i hi U U' h => sapprox_loc _ _ _ _ (hspos i (by omega)) U U' h)]
  set G := tensorMapZ (fun i : Fin (d + 1) => Sapprox q.p (q.s.getD i 1) (2 ^ q.te i) q.α) U
  have hFt : FtL q (listOf q.tdims fun j => G fun i => j i) =
      listOf q.tdims fun j => maskZ (tF q d) (Ftq q d G) fun i => j i := by
    have h1 : FtL q (listOf q.tdims fun j => G fun i => j i) = toL q.tdims (Ftq q d G) := by
      unfold Ftq; rw [toL_ofL q.tdims (by rw [htl, hK])]
      · rfl
      · exact length_FtL q (by omega) hdh _ (toL_length _ _)
    rw [h1]; unfold toL
    apply listOf_congr
    intro l hl
    have hl' := mem_boxIdxs.1 hl
    unfold maskZ
    rw [if_pos]
    intro i
    have := hl'.2 i (by rw [hl'.1, htl, hK]; exact i.2)
    rw [tdims_getD q i (by omega)] at this
    exact this
  rw [hFt, tensorGo_eq (d + 1) q.tdims q.s (by omega) (by omega)
    (fun i hi => by rw [tdims_getD q i (by omega)]; positivity)
    (fun i => Bapprox q.p (q.s.getD i 1) (2 ^ q.te i) q.α) (fun i hi U U' h => bapprox_loc _ _ _ _ (by positivity) U U'
      (by rwa [tdims_getD q i (by omega)] at h))]
  rfl

/-- the integer array of a list on the box `dims` -/
def ofLZ {m : ℕ} (dims : List ℕ) (L : List ℤ) : (Fin m → ℕ) → ℤ :=
  fun x => L.getD (rmPos dims (natFn x)) 0

lemma natFn_ixf {m : ℕ} (l : List ℕ) (hl : l.length = m) : natFn (fun i : Fin m => ixf l i) = ixf l := by
  funext i
  by_cases hi : i < m
  · simp [natFn, hi]
  · simp only [natFn, hi, dite_false, ixf]
    rw [List.getD_eq_default _ _ (by omega)]

lemma map_toL {m : ℕ} (dims : List ℕ) (hd : dims.length = m) (L : List ℤ) (hL : L.length = dims.prod)
    (f : ℤ → ℤ × ℤ) : L.map f = toL dims (fun x : Fin m → ℕ => f (ofLZ dims L x)) := by
  rw [← toL_ofL (m := m) dims hd (L.map f) (by simp [hL])]
  unfold toL; apply listOf_congr; intro l hl
  have hlen : l.length = m := by rw [(mem_boxIdxs.1 hl).1, hd]
  unfold ofL ofLZ
  simp only [natFn_ixf l hlen]
  have hk : rmPos dims (ixf l) < L.length := hL ▸ rmPos_lt hl
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
    Option.map_some, Option.getD_some]

lemma zipWith_toL {m : ℕ} (dims : List ℕ) (f : ℤ × ℤ → ℤ × ℤ → ℤ × ℤ) (A B : (Fin m → ℕ) → ℤ × ℤ) :
    List.zipWith f (toL dims A) (toL dims B) = toL dims fun x => f (A x) (B x) := by
  unfold toL; rw [zipWith_listOf]

lemma toL_map {m : ℕ} {β : Type*} (dims : List ℕ) (g : ℤ × ℤ → β) (A : (Fin m → ℕ) → ℤ × ℤ) :
    (toL dims A).map g = listOf dims fun j => g (A fun i => j i) := by
  unfold toL listOf; rw [List.map_map]; rfl

lemma prod_fin (s : List ℕ) (d : ℕ) (hs : s.length = d + 1) :
    s.prod = ∏ i : Fin (d + 1), s.getD i 1 := by
  have : s = List.ofFn (fun i : Fin (d + 1) => s.getD i 1) := by
    apply List.ext_getElem (by simp [hs])
    intro k h1 h2
    simp only [List.getElem_ofFn]
    rw [List.getD_eq_getElem _ _ h1]
  conv_lhs => rw [this]
  rw [List.prod_ofFn]

theorem exactConvL_eq (q : Params) (d : ℕ) (hK : q.K = d + 1) (hdh : q.dh < q.K)
    (hslen : q.s.length = q.K) (hspos : ∀ i < q.K, 0 < q.s.getD i 1)
    (u v : List ℤ) (hu : u.length = q.S) (hv : v.length = q.S) :
    exactConvL q u v = listOf q.s fun j =>
      exactConv q.p q.α q.b (sF q d) (tF q d) (Ftq q d) (ofLZ q.s u) (ofLZ q.s v) fun i => j i := by
  have hsd : q.s.length = d + 1 := by omega
  unfold exactConvL
  simp only
  rw [map_toL q.s hsd u hu, map_toL q.s hsd v hv, fwdL_eq q d hK hdh hslen hspos,
    fwdL_eq q d hK hdh hslen hspos, zipWith_toL, fwdL_eq q d hK hdh hslen hspos, toL_map]
  apply listOf_congr
  intro l _
  unfold exactConv
  rw [Params.S, prod_fin q.s d hsd, hK]

lemma convBox_cconv (s : List ℕ) (d : ℕ) (hs : s.length = d + 1) (u v : List ℤ) (l : List ℕ)
    (hl : l ∈ boxIdxs s) :
    convBox (fun i : Fin (d + 1) => s.getD i 1) (ofLZ s u) (ofLZ s v) (fun i => ixf l i) =
      cconv s u v (ixf l) := by
  unfold convBox cconv
  rw [sum_boxIdxs_piFinset s hs]
  apply Finset.sum_congr rfl
  intro k _
  have hk : ixf (List.ofFn k) = natFn k := by
    have := ixf_ofFn (m := d + 1) (natFn k) (natFn_zero k)
    have e : (fun i : Fin (d + 1) => natFn k i) = k := by funext i; exact natFn_val k i
    rw [e] at this; exact this
  unfold ofLZ
  rw [hk]
  congr 2
  apply rmPos_congr
  intro i hi
  rw [hs] at hi
  have h1 : (List.ofFn k).getD i 0 = k ⟨i, hi⟩ := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
  simp only [natFn, hi, dite_true]
  rw [h1]

/-- the hypotheses of `exactConv_eq` for the list pipeline give the cyclic convolution -/
theorem exactConvL_cconv (q : Params) (d : ℕ) (hK : q.K = d + 1) (hdh : q.dh < q.K)
    (hslen : q.s.length = q.K) (hspos : ∀ i < q.K, 0 < q.s.getD i 1)
    (he : 2 ≤ q.e) (hP : 1 ≤ q.P) (hlog : q.logOuter ≤ 2 * q.fn)
    (hPM : 4 * (q.tdims.prod : ℤ) * ((2 : ℤ) ^ q.p) ^ 2 < 2 ^ q.P)
    (hst : ∀ i : Fin (d + 1), sF q d i < tF q d i)
    (hcop : ∀ i : Fin (d + 1), Nat.Coprime (sF q d i) (tF q d i))
    (hα : 2 ≤ q.α) (hαp : q.α ^ 2 ≤ q.p)
    (hx : ∀ i : Fin (d + 1), sF q d i ≤ q.α ^ 2 * (tF q d i - sF q d i))
    (hp : ∀ i : Fin (d + 1), 100 * (jIter q.p (sF q d i) (tF q d i) q.α * (10 * eWidth q.p q.α + 12) + 1)
      ≤ 2 ^ q.p)
    (hpA : 4 * (6 * sWidth q.p q.α + 4) ≤ 2 ^ q.p) (hb : q.b ≤ q.p)
    (hprec : 2 * (3 * ((∑ _i : Fin (d + 1), (6 * sWidth q.p q.α + 4 : ℝ)) + (Real.sqrt 2 + 3 * 5 + 3) +
        ∑ i, ((jIter q.p (sF q d i) (tF q d i) q.α : ℝ) * (10 * eWidth q.p q.α + 12) + 4)) + 2) *
        ((∏ i, sF q d i : ℕ) : ℝ) ^ 2 * 2 ^ (2 * q.b + 6 * (d + 1) * q.α ^ 2) < 2 ^ q.p)
    (u v : List ℤ) (hu : u.length = q.S) (hv : v.length = q.S)
    (hub : ∀ a ∈ u, 0 ≤ a ∧ a < 2 ^ q.b) (hvb : ∀ a ∈ v, 0 ≤ a ∧ a < 2 ^ q.b) :
    exactConvL q u v = listOf q.s (cconv q.s u v) := by
  have hsd : q.s.length = d + 1 := by omega
  have : ∀ i, NeZero (sF q d i) := fun i => ⟨(hspos i (by omega)).ne'⟩
  have : ∀ i, NeZero (tF q d i) := fun i => ⟨by positivity⟩
  have hsn : (Fin.snoc (fun i : Fin d => 2 ^ q.te i) q.r : Fin (d + 1) → ℕ) = tF q d := by
    rw [← tdims_snoc q d hK hdh]; funext i; exact tdims_getD q i (by omega)
  have hFt : ∀ U : (Fin (d + 1) → ℕ) → ℤ × ℤ, InDisc q.p U → ∀ j : Fin (d + 1) → ℕ,
      (∀ i, j i < tF q d i) →
      ‖gC (Ftq q d U j)‖ ≤ 2 ^ q.p ∧
      ‖gC (Ftq q d U j) - 2 ^ q.p * dftBox (tF q d) (fun x => gC (U x) / 2 ^ q.p) j‖ ≤
        Real.sqrt 2 + 3 * 5 + 3 := by
    intro U hU j hj
    have := Ftq_spec q d hK he hdh hP hlog hPM U hU j (by rw [hsn]; exact hj)
    rwa [hsn] at this
  have hbd : ∀ (w : List ℤ), (∀ a ∈ w, 0 ≤ a ∧ a < 2 ^ q.b) → ∀ x : Fin (d + 1) → ℕ,
      |ofLZ q.s w x| < 2 ^ q.b := by
    intro w hw x
    unfold ofLZ
    rcases getD_mem_or w (rmPos q.s (natFn x)) 0 with h | h
    · have := hw _ h; rw [abs_of_nonneg this.1]; exact this.2
    · rw [h]; simp
  rw [exactConvL_eq q d hK hdh hslen hspos u v hu hv]
  apply listOf_congr
  intro l hl
  have hl' := mem_boxIdxs.1 hl
  rw [IntMul.HvdH.exactConv_eq q.p q.α q.b (sF q d) (tF q d) hst hcop hα hαp hx hp hpA (Ftq q d) _ hFt hb
    _ _ (hbd u hub) (hbd v hvb) hprec (fun i => ixf l i) (fun i => hl'.2 i (by rw [hl'.1, hsd]; exact i.2))]
  exact convBox_cconv q.s d hsd u v l hl

end IntMul.HvdH.RefPf

end

-- ===== Solutions.HvdH.Ref.Crt
section

/-! Correctness of `refStep` given the exact convolution `exactConvL`. -/

namespace IntMul.HvdH.RefPf
open IntMul.HvdH IntMul.HvdH.Ref

section CRT

variable {s : List ℕ}

theorem prod_eq_finset (s : List ℕ) : s.prod = ∏ i ∈ Finset.range s.length, s.getD i 1 := by
  induction s with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons, List.length_cons, Finset.prod_range_succ', ih]
    simp [mul_comm]

theorem dvd_prod_of_lt (s : List ℕ) {i : ℕ} (hi : i < s.length) : s.getD i 1 ∣ s.prod := by
  rw [prod_eq_finset]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hi)

theorem prod_pos_of (hpos : ∀ i < s.length, 0 < s.getD i 1) : 0 < s.prod := by
  rw [prod_eq_finset]
  exact Finset.prod_pos fun i hi => hpos i (Finset.mem_range.1 hi)

theorem prod_div_eq (hpos : ∀ i < s.length, 0 < s.getD i 1) {i : ℕ} (hi : i < s.length) :
    s.prod / s.getD i 1 = ∏ j ∈ (Finset.range s.length).erase i, s.getD j 1 := by
  rw [prod_eq_finset, ← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hi),
    Nat.mul_div_cancel_left _ (hpos i hi)]

theorem crtCoef_self (hpos : ∀ i < s.length, 0 < s.getD i 1)
    (hcop : ∀ i < s.length, ∀ j < s.length, i ≠ j → Nat.Coprime (s.getD i 1) (s.getD j 1))
    {i : ℕ} (hi : i < s.length) : (crtCoef s i : ZMod (s.getD i 1)) = 1 := by
  have hm : Nat.Coprime (s.prod / s.getD i 1) (s.getD i 1) := by
    rw [prod_div_eq hpos hi]
    apply Nat.Coprime.prod_left
    intro j hj
    rw [Finset.mem_erase, Finset.mem_range] at hj
    exact hcop j hj.2 i hi hj.1
  have : NeZero (s.getD i 1) := ⟨(hpos i hi).ne'⟩
  unfold crtCoef
  rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.coe_mul_inv_eq_one _ hm]

theorem crtCoef_other (hpos : ∀ i < s.length, 0 < s.getD i 1)
    {i j : ℕ} (hi : i < s.length) (hj : j < s.length) (hij : i ≠ j) :
    (crtCoef s i : ZMod (s.getD j 1)) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  unfold crtCoef
  apply Dvd.dvd.mul_right
  rw [prod_div_eq hpos hi]
  exact Finset.dvd_prod_of_mem _ (by simp [Finset.mem_erase, hj, Ne.symm hij])

theorem crtIdx_cast (hpos : ∀ i < s.length, 0 < s.getD i 1)
    (hcop : ∀ i < s.length, ∀ j < s.length, i ≠ j → Nat.Coprime (s.getD i 1) (s.getD j 1))
    (j : ℕ → ℕ) {m : ℕ} (hm : m < s.length) : (crtIdx s j : ZMod (s.getD m 1)) = j m := by
  unfold crtIdx
  rw [(ZMod.natCast_eq_natCast_iff' _ _ _).2 (Nat.mod_mod_of_dvd _ (dvd_prod_of_lt s hm)),
    sum_map_range_finset, Nat.cast_sum, Finset.sum_eq_single m]
  · simp [crtCoef_self hpos hcop hm]
  · intro i hi him
    rw [Finset.mem_range] at hi
    simp [crtCoef_other hpos hi hm him]
  · intro h; exact absurd (Finset.mem_range.2 hm) h

theorem crtIdx_mod (hpos : ∀ i < s.length, 0 < s.getD i 1)
    (hcop : ∀ i < s.length, ∀ j < s.length, i ≠ j → Nat.Coprime (s.getD i 1) (s.getD j 1))
    (j : ℕ → ℕ) {m : ℕ} (hm : m < s.length) : crtIdx s j % s.getD m 1 = j m % s.getD m 1 :=
  (ZMod.natCast_eq_natCast_iff' _ _ _).1 (crtIdx_cast hpos hcop j hm)

theorem crtIdx_lt (hpos : ∀ i < s.length, 0 < s.getD i 1) (j : ℕ → ℕ) : crtIdx s j < s.prod :=
  Nat.mod_lt _ (prod_pos_of hpos)

theorem getD_eq_crtIdx_mod (hpos : ∀ i < s.length, 0 < s.getD i 1)
    (hcop : ∀ i < s.length, ∀ j < s.length, i ≠ j → Nat.Coprime (s.getD i 1) (s.getD j 1))
    {l : List ℕ} (hl : l ∈ boxIdxs s) {i : ℕ} (hi : i < s.length) :
    l.getD i 0 = crtIdx s (ixf l) % s.getD i 1 := by
  rw [mem_boxIdxs] at hl
  rw [crtIdx_mod hpos hcop _ hi, ixf, Nat.mod_eq_of_lt (hl.2 i (by omega))]

theorem crtIdx_inj (hpos : ∀ i < s.length, 0 < s.getD i 1)
    (hcop : ∀ i < s.length, ∀ j < s.length, i ≠ j → Nat.Coprime (s.getD i 1) (s.getD j 1))
    {l l' : List ℕ} (hl : l ∈ boxIdxs s) (hl' : l' ∈ boxIdxs s)
    (h : crtIdx s (ixf l) = crtIdx s (ixf l')) : l = l' := by
  have h1 := (mem_boxIdxs.1 hl).1
  have h2 := (mem_boxIdxs.1 hl').1
  apply List.ext_getElem (by omega)
  intro i hi1 hi2
  have e1 := getD_eq_crtIdx_mod hpos hcop hl (i := i) (by omega)
  have e2 := getD_eq_crtIdx_mod hpos hcop hl' (i := i) (by omega)
  rw [List.getD_eq_getElem _ _ hi1] at e1
  rw [List.getD_eq_getElem _ _ hi2] at e2
  rw [e1, e2, h]

theorem image_crtIdx (hpos : ∀ i < s.length, 0 < s.getD i 1)
    (hcop : ∀ i < s.length, ∀ j < s.length, i ≠ j → Nat.Coprime (s.getD i 1) (s.getD j 1)) :
    (boxIdxs s).toFinset.image (fun l => crtIdx s (ixf l)) = Finset.range s.prod := by
  have hinj : Set.InjOn (fun l => crtIdx s (ixf l)) ((boxIdxs s).toFinset : Set (List ℕ)) :=
    fun l hl l' hl' h => crtIdx_inj hpos hcop (by simpa using hl) (by simpa using hl') h
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    simp only [Finset.mem_image] at ha
    obtain ⟨l, _, rfl⟩ := ha
    exact Finset.mem_range.2 (crtIdx_lt hpos _)
  · rw [Finset.card_image_of_injOn hinj, List.toFinset_card_of_nodup (nodup_boxIdxs s),
      length_boxIdxs, Finset.card_range]

theorem sum_boxIdxs_crt (hpos : ∀ i < s.length, 0 < s.getD i 1)
    (hcop : ∀ i < s.length, ∀ j < s.length, i ≠ j → Nat.Coprime (s.getD i 1) (s.getD j 1))
    (H : ℕ → ℤ) :
    ((boxIdxs s).map fun l => H (crtIdx s (ixf l))).sum = ∑ a ∈ Finset.range s.prod, H a := by
  have hinj : Set.InjOn (fun l => crtIdx s (ixf l)) ((boxIdxs s).toFinset : Set (List ℕ)) :=
    fun l hl l' hl' h => crtIdx_inj hpos hcop (by simpa using hl) (by simpa using hl') h
  rw [← List.sum_toFinset _ (nodup_boxIdxs s), ← image_crtIdx hpos hcop,
    Finset.sum_image hinj]

theorem crt_unique (hpos : ∀ i < s.length, 0 < s.getD i 1)
    (hcop : ∀ i < s.length, ∀ j < s.length, i ≠ j → Nat.Coprime (s.getD i 1) (s.getD j 1))
    {a a' : ℕ} (ha : a < s.prod) (ha' : a' < s.prod)
    (h : ∀ m < s.length, a % s.getD m 1 = a' % s.getD m 1) : a = a' := by
  rw [← Finset.mem_range, ← image_crtIdx hpos hcop, Finset.mem_image] at ha ha'
  obtain ⟨l, hl, rfl⟩ := ha
  obtain ⟨l', hl', rfl⟩ := ha'
  rw [List.mem_toFinset] at hl hl'
  have h1 := (mem_boxIdxs.1 hl).1
  have h2 := (mem_boxIdxs.1 hl').1
  suffices hll : l = l' by rw [hll]
  apply List.ext_getElem (by omega)
  intro i hi1 hi2
  have e1 := getD_eq_crtIdx_mod hpos hcop hl (i := i) (by omega)
  have e2 := getD_eq_crtIdx_mod hpos hcop hl' (i := i) (by omega)
  rw [List.getD_eq_getElem _ _ hi1] at e1
  rw [List.getD_eq_getElem _ _ hi2] at e2
  rw [e1, e2, h i (by omega)]

end CRT

section Conv

variable {s : List ℕ}

theorem mod_sub_cast (n k a S : ℕ) (hd : n ∣ S) (ha : a < S) :
    (k % n + n - a % n) % n % n = (k + S - a) % n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_dvd_iff] at hd; omega)
  have := Nat.mod_lt a hn
  rw [Nat.mod_mod, ← ZMod.natCast_eq_natCast_iff', Nat.cast_sub (by omega),
    Nat.cast_sub (by omega)]
  rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_mod, ZMod.natCast_mod, ZMod.natCast_self,
    (ZMod.natCast_eq_zero_iff S n).2 hd]

theorem cconv_crtIn (hpos : ∀ i < s.length, 0 < s.getD i 1)
    (hcop : ∀ i < s.length, ∀ j < s.length, i ≠ j → Nat.Coprime (s.getD i 1) (s.getD j 1))
    (c c' : List ℤ) (k : ℕ) :
    cconv s (crtIn s c) (crtIn s c') (fun i => k % s.getD i 1) =
      ∑ a ∈ Finset.range s.prod, c.getD a 0 * c'.getD ((k + s.prod - a) % s.prod) 0 := by
  rw [← sum_boxIdxs_crt hpos hcop
    (fun a => c.getD a 0 * c'.getD ((k + s.prod - a) % s.prod) 0)]
  unfold cconv
  congr 1
  apply List.map_congr_left
  intro l hl
  have hlm := mem_boxIdxs.1 hl
  set g : ℕ → ℕ := fun i => (k % s.getD i 1 + s.getD i 1 - l.getD i 0) % s.getD i 1 with hg
  have hl2 : (List.range s.length).map g ∈ boxIdxs s :=
    map_range_mem_boxIdxs s g (fun i hi => Nat.mod_lt _ (hpos i hi))
  have he : ixf ((List.range s.length).map g) = g := by
    apply ixf_map_range
    intro i hi
    have h1 : s.getD i 1 = 1 := List.getD_eq_default s 1 hi
    simp only [hg, h1, Nat.mod_one]
  rw [← he, crtIn, crtIn, getD_listOf _ _ _ hl, getD_listOf _ _ _ hl2]
  congr 2
  apply crt_unique hpos hcop (crtIdx_lt hpos _) (Nat.mod_lt _ (prod_pos_of hpos))
  intro m hm
  rw [crtIdx_mod hpos hcop _ hm, he, Nat.mod_mod_of_dvd _ (dvd_prod_of_lt s hm), hg]
  beta_reduce
  rw [getD_eq_crtIdx_mod hpos hcop hl hm]
  exact mod_sub_cast _ _ _ _ (dvd_prod_of_lt s hm) (crtIdx_lt hpos _)

theorem cyc_eq (L S k : ℕ) (f g : ℕ → ℤ) (hf : ∀ a, L ≤ a → f a = 0)
    (hg : ∀ a, L ≤ a → g a = 0) (hS : 2 * L - 1 ≤ S) (hk : k < 2 * L - 1) :
    ∑ a ∈ Finset.range S, f a * g ((k + S - a) % S) =
      ∑ a ∈ Finset.range (k + 1), f a * g (k - a) := by
  rw [← Finset.sum_range_add_sum_Ico _ (show k + 1 ≤ S by omega)]
  rw [Finset.sum_eq_zero (s := Finset.Ico _ _), add_zero]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mem_range] at ha
    rw [show k + S - a = (k - a) + S by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · intro a ha
    rw [Finset.mem_Ico] at ha
    by_cases h : L ≤ a
    · simp [hf a h]
    rw [Nat.mod_eq_of_lt (by omega), hg _ (by omega), mul_zero]

theorem digits_sum (b : ℕ) : ∀ (L x : ℕ), x < 2 ^ (b * L) →
    ∑ a ∈ Finset.range L, x / 2 ^ (b * a) % 2 ^ b * 2 ^ (b * a) = x
  | 0, x, h => by simp at h; simp [h]
  | L + 1, x, h => by
    rw [Finset.sum_range_succ']
    have hx : x / 2 ^ b < 2 ^ (b * L) := by
      apply Nat.div_lt_of_lt_mul
      rw [← pow_add]; convert h using 2; ring
    have ih := digits_sum b L (x / 2 ^ b) hx
    have e : ∀ a, x / 2 ^ (b * (a + 1)) % 2 ^ b * 2 ^ (b * (a + 1)) =
        2 ^ b * (x / 2 ^ b / 2 ^ (b * a) % 2 ^ b * 2 ^ (b * a)) := by
      intro a
      rw [Nat.div_div_eq_div_mul, ← pow_add, show b * (a + 1) = b + b * a by ring, pow_add]
      ring
    simp_rw [e]
    rw [← Finset.mul_sum, ih]
    simp only [mul_zero, pow_zero, Nat.div_one, mul_one]
    exact Nat.div_add_mod x (2 ^ b)

open Polynomial in
theorem conv_sum (L : ℕ) (hL : 1 ≤ L) (f g : ℕ → ℤ) (hf : ∀ a, L ≤ a → f a = 0)
    (hg : ∀ a, L ≤ a → g a = 0) (z : ℤ) :
    ∑ k ∈ Finset.range (2 * L - 1), (∑ a ∈ Finset.range (k + 1), f a * g (k - a)) * z ^ k =
      (∑ a ∈ Finset.range L, f a * z ^ a) * (∑ a ∈ Finset.range L, g a * z ^ a) := by
  let P : ℤ[X] := ∑ a ∈ Finset.range L, C (f a) * X ^ a
  let Q : ℤ[X] := ∑ a ∈ Finset.range L, C (g a) * X ^ a
  have hPc : ∀ n, P.coeff n = f n := by
    intro n
    simp only [P, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · rw [Finset.mem_range] at h; rw [hf n (by omega)]
  have hQc : ∀ n, Q.coeff n = g n := by
    intro n
    simp only [Q, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · rw [Finset.mem_range] at h; rw [hg n (by omega)]
  have hPd : P.natDegree ≤ L - 1 :=
    natDegree_le_iff_coeff_eq_zero.2 (fun N hN => by rw [hPc, hf]; omega)
  have hQd : Q.natDegree ≤ L - 1 :=
    natDegree_le_iff_coeff_eq_zero.2 (fun N hN => by rw [hQc, hg]; omega)
  have hPQ : (P * Q).natDegree < 2 * L - 1 :=
    lt_of_le_of_lt natDegree_mul_le (by omega)
  have h1 := eval_eq_sum_range' hPQ z
  rw [eval_mul] at h1
  have hPe : P.eval z = ∑ a ∈ Finset.range L, f a * z ^ a := by simp [P, eval_finsetSum]
  have hQe : Q.eval z = ∑ a ∈ Finset.range L, g a * z ^ a := by simp [Q, eval_finsetSum]
  rw [← hPe, ← hQe, h1]
  apply Finset.sum_congr rfl
  intro k _
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i * Q.coeff j)]
  simp [hPc, hQc]

theorem getD_chunksL (b L x a : ℕ) :
    (chunksL b L x).getD a 0 = if a < L then ((x / 2 ^ (b * a) % 2 ^ b : ℕ) : ℤ) else 0 := by
  split_ifs with h
  · simp [chunksL, List.getD_eq_getElem?_getD, h]
  · exact List.getD_eq_default _ _ (by simp [chunksL]; omega)

theorem chunksL_prod (b L x y : ℕ) (hL : 1 ≤ L) (hx : x < 2 ^ (b * L)) (hy : y < 2 ^ (b * L)) :
    ∑ k ∈ Finset.range (2 * L - 1), (∑ a ∈ Finset.range (k + 1),
      (chunksL b L x).getD a 0 * (chunksL b L y).getD (k - a) 0) * 2 ^ (b * k) =
      ((x * y : ℕ) : ℤ) := by
  have hf : ∀ (z a : ℕ), L ≤ a → (chunksL b L z).getD a 0 = 0 := by
    intro z a ha; rw [getD_chunksL, if_neg (by omega)]
  simp_rw [pow_mul]
  rw [conv_sum L hL _ _ (hf x) (hf y)]
  have hs : ∀ z : ℕ, z < 2 ^ (b * L) →
      ∑ a ∈ Finset.range L, (chunksL b L z).getD a 0 * ((2 : ℤ) ^ b) ^ a = (z : ℤ) := by
    intro z hz
    conv_rhs => rw [← digits_sum b L z hz]
    push_cast
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mem_range] at ha
    rw [getD_chunksL, if_pos ha, ← pow_mul]
    push_cast
    ring
  rw [hs x hx, hs y hy]
  push_cast
  ring

end Conv

section Main

theorem crtOut_listOf {s : List ℕ} (hpos : ∀ i < s.length, 0 < s.getD i 1) (N : ℕ)
    (F : (ℕ → ℕ) → ℤ) (k : ℕ) :
    (crtOut s N (listOf s F)).getD k 0 = if k < N then F (fun i => k % s.getD i 1) else 0 := by
  split_ifs with hk
  · have hl : (List.range s.length).map (fun i => k % s.getD i 1) ∈ boxIdxs s :=
      map_range_mem_boxIdxs s _ (fun i hi => Nat.mod_lt _ (hpos i hi))
    have he : ixf ((List.range s.length).map (fun i => k % s.getD i 1)) =
        fun i => k % s.getD i 1 := by
      apply ixf_map_range
      intro i hi
      have h1 : s.getD i 1 = 1 := List.getD_eq_default s 1 hi
      simp only [h1, Nat.mod_one]
    rw [crtOut, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
      Option.map_some, Option.getD_some]
    rw [← he, getD_listOf _ _ _ hl]
  · exact List.getD_eq_default _ _ (by simp [crtOut]; omega)

theorem crtIn_len (s : List ℕ) (c : List ℤ) : (crtIn s c).length = s.prod := by
  simp [crtIn, length_listOf]

theorem crtIn_range (s : List ℕ) (b L x : ℕ) :
    ∀ a ∈ crtIn s (chunksL b L x), 0 ≤ a ∧ a < 2 ^ b := by
  intro a ha
  simp only [crtIn, listOf, List.mem_map] at ha
  obtain ⟨l, _, rfl⟩ := ha
  have hp : (0 : ℤ) < 2 ^ b := by positivity
  have hc : ∀ a ∈ chunksL b L x, 0 ≤ a ∧ a < 2 ^ b := by
    intro a ha
    simp only [chunksL, List.mem_map] at ha
    obtain ⟨k, _, rfl⟩ := ha
    constructor
    · positivity
    · have := Nat.mod_lt (x / 2 ^ (b * k)) (Nat.pos_of_ne_zero (by positivity : 2 ^ b ≠ 0))
      exact_mod_cast this
  rcases getD_mem_or (chunksL b L x) (crtIdx s fun i => l.getD i 0) 0 with h | h
  · exact hc _ h
  · rw [h]; exact ⟨le_refl _, hp⟩

theorem refStep_eq_of (q : Params) (hlen : q.s.length = q.K)
    (hpos : ∀ i < q.K, 0 < q.s.getD i 1)
    (hcop : ∀ i < q.K, ∀ j < q.K, i ≠ j → Nat.Coprime (q.s.getD i 1) (q.s.getD j 1))
    (hL : 1 ≤ q.L) (hS : 2 * q.L - 1 ≤ q.S)
    (hconv : ∀ u v : List ℤ, u.length = q.S → v.length = q.S →
      (∀ a ∈ u, 0 ≤ a ∧ a < 2 ^ q.b) → (∀ a ∈ v, 0 ≤ a ∧ a < 2 ^ q.b) →
      exactConvL q u v = listOf q.s (cconv q.s u v))
    (x y : ℕ) (hx : x < 2 ^ (q.b * q.L)) (hy : y < 2 ^ (q.b * q.L)) :
    refStep q x y = x * y := by
  replace hpos : ∀ i < q.s.length, 0 < q.s.getD i 1 := by rw [hlen]; exact hpos
  replace hcop : ∀ i < q.s.length, ∀ j < q.s.length, i ≠ j →
      Nat.Coprime (q.s.getD i 1) (q.s.getD j 1) := by rw [hlen]; exact hcop
  have hS' : q.S = q.s.prod := rfl
  unfold refStep
  simp only []
  rw [hconv _ _ (crtIn_len _ _) (crtIn_len _ _) (crtIn_range _ _ _ _) (crtIn_range _ _ _ _),
    evalDigits, sum_map_range_finset]
  have hlenO : (crtOut q.s (2 * q.L - 1)
      (listOf q.s (cconv q.s (crtIn q.s (chunksL q.b q.L x)) (crtIn q.s (chunksL q.b q.L y))))).length
      = 2 * q.L - 1 := by simp [crtOut]
  rw [hlenO]
  have := chunksL_prod q.b q.L x y hL hx hy
  push_cast at this
  rw [← this]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hf : ∀ (z a : ℕ), q.L ≤ a → (chunksL q.b q.L z).getD a 0 = 0 := by
    intro z a ha; rw [getD_chunksL, if_neg (by omega)]
  rw [crtOut_listOf hpos, if_pos hk, cconv_crtIn hpos hcop, ← hS',
    cyc_eq q.L q.S k (fun a => (chunksL q.b q.L x).getD a 0)
      (fun a => (chunksL q.b q.L y).getD a 0) (hf x) (hf y) hS hk]

/-- the digits read back by `crtOut` are the (nonnegative) linear convolution coefficients -/
theorem refStep_digits_of (q : Params) (hlen : q.s.length = q.K)
    (hpos : ∀ i < q.K, 0 < q.s.getD i 1)
    (hcop : ∀ i < q.K, ∀ j < q.K, i ≠ j → Nat.Coprime (q.s.getD i 1) (q.s.getD j 1))
    (hL : 1 ≤ q.L) (hS : 2 * q.L - 1 ≤ q.S)
    (hconv : ∀ u v : List ℤ, u.length = q.S → v.length = q.S →
      (∀ a ∈ u, 0 ≤ a ∧ a < 2 ^ q.b) → (∀ a ∈ v, 0 ≤ a ∧ a < 2 ^ q.b) →
      exactConvL q u v = listOf q.s (cconv q.s u v))
    (x y : ℕ) :
    ∀ c ∈ crtOut q.s (2 * q.L - 1)
      (exactConvL q (crtIn q.s (chunksL q.b q.L x)) (crtIn q.s (chunksL q.b q.L y))),
      0 ≤ c ∧ c < q.L * 2 ^ (2 * q.b) := by
  replace hpos : ∀ i < q.s.length, 0 < q.s.getD i 1 := by rw [hlen]; exact hpos
  replace hcop : ∀ i < q.s.length, ∀ j < q.s.length, i ≠ j →
      Nat.Coprime (q.s.getD i 1) (q.s.getD j 1) := by rw [hlen]; exact hcop
  have hS' : q.S = q.s.prod := rfl
  rw [hconv _ _ (crtIn_len _ _) (crtIn_len _ _) (crtIn_range _ _ _ _) (crtIn_range _ _ _ _)]
  intro c hc
  obtain ⟨k, hk, rfl⟩ : ∃ k, k < 2 * q.L - 1 ∧ (crtOut q.s (2 * q.L - 1)
      (listOf q.s (cconv q.s (crtIn q.s (chunksL q.b q.L x)) (crtIn q.s (chunksL q.b q.L y))))).getD k 0 = c := by
    obtain ⟨k, hk, he⟩ := List.getElem_of_mem hc
    refine ⟨k, by simpa [crtOut] using hk, ?_⟩
    rw [List.getD_eq_getElem _ _ hk]; exact he
  have hf : ∀ (z a : ℕ), q.L ≤ a → (chunksL q.b q.L z).getD a 0 = 0 := by
    intro z a ha; rw [getD_chunksL, if_neg (by omega)]
  rw [crtOut_listOf hpos, if_pos hk, cconv_crtIn hpos hcop, ← hS',
    cyc_eq q.L q.S k (fun a => (chunksL q.b q.L x).getD a 0)
      (fun a => (chunksL q.b q.L y).getD a 0) (hf x) (hf y) hS hk]
  have hb : ∀ (z a : ℕ), 0 ≤ (chunksL q.b q.L z).getD a 0 ∧ (chunksL q.b q.L z).getD a 0 < 2 ^ q.b ∧
      (q.L ≤ a → (chunksL q.b q.L z).getD a 0 = 0) := by
    intro z a
    rw [getD_chunksL]
    split_ifs with h
    · refine ⟨by positivity, ?_, fun h' => by omega⟩
      exact_mod_cast Nat.mod_lt _ (by positivity)
    · exact ⟨le_rfl, by positivity, fun _ => rfl⟩
  have hterm : ∀ a ∈ Finset.range (k + 1),
      (chunksL q.b q.L x).getD a 0 * (chunksL q.b q.L y).getD (k - a) 0 ≤
        if a < q.L then (2 : ℤ) ^ (2 * q.b) - 1 else 0 := by
    intro a _
    obtain ⟨x0, x1, x2⟩ := hb x a
    obtain ⟨y0, y1, _⟩ := hb y (k - a)
    split_ifs with h
    · have : (chunksL q.b q.L x).getD a 0 * (chunksL q.b q.L y).getD (k - a) 0 ≤
          (2 ^ q.b - 1) * (2 ^ q.b - 1) := mul_le_mul (by omega) (by omega) y0 (by
            have : (1 : ℤ) ≤ 2 ^ q.b := one_le_pow₀ (by norm_num); omega)
      have e : ((2 : ℤ) ^ q.b - 1) * (2 ^ q.b - 1) ≤ 2 ^ (2 * q.b) - 1 := by
        have : (1 : ℤ) ≤ 2 ^ q.b := one_le_pow₀ (by norm_num)
        rw [pow_mul', sq]; nlinarith
      linarith
    · rw [x2 (by omega), zero_mul]
  constructor
  · apply Finset.sum_nonneg; intro a _
    exact mul_nonneg (hb x a).1 (hb y (k - a)).1
  · calc _ ≤ ∑ a ∈ Finset.range (k + 1), (if a < q.L then (2 : ℤ) ^ (2 * q.b) - 1 else 0) :=
          Finset.sum_le_sum hterm
      _ ≤ ∑ a ∈ Finset.range q.L, ((2 : ℤ) ^ (2 * q.b) - 1) := by
          rw [← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro a ha; simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢; exact ha.2
          · intro a _ _; have : (1 : ℤ) ≤ 2 ^ (2 * q.b) := one_le_pow₀ (by norm_num); linarith
      _ < q.L * 2 ^ (2 * q.b) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have : (1 : ℤ) ≤ q.L := by exact_mod_cast hL
          nlinarith

end Main

end IntMul.HvdH.RefPf

end

-- ===== Solutions.HvdH.Ref.Final
section

/-! `refStep q x y = x * y` from simple size conditions on the parameters. -/

open Finset

namespace IntMul.HvdH.RefPf
open IntMul.HvdH IntMul.HvdH.Ref

lemma pow_poly (n : ℕ) (hn : 20 ≤ n) : 2200 * n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc 2200 * (n + 1) ^ 2 ≤ 2 * (2200 * n ^ 2) := by nlinarith
      _ ≤ 2 * 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by ring

lemma ceilSqrt_le (p : ℕ) : ceilSqrt p ≤ p := by
  unfold ceilSqrt
  split_ifs with h
  · have h1 : Nat.sqrt p ≤ p := Nat.sqrt_le_self p
    by_contra hc
    have e : Nat.sqrt p = p := by omega
    rw [e] at h
    nlinarith
  · exact Nat.sqrt_le_self p

lemma eWidth_le (p α : ℕ) (hα : 1 ≤ α) : eWidth p α ≤ p + 1 := by
  unfold eWidth
  have hc := ceilSqrt_le p
  have h1 : ceilSqrt p ≤ ceilSqrt p * α := Nat.le_mul_of_pos_right _ hα
  have : (ceilSqrt p + α - 1) / α < ceilSqrt p + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega), add_mul, one_mul]; omega
  omega

lemma jIter_le (p s t α : ℕ) (hs : s ≤ α ^ 2 * (t - s)) (hX : 0 < α ^ 2 * (t - s)) :
    jIter p s t α ≤ p := by
  unfold jIter
  have : (p * s + α ^ 2 * (t - s) - 1) / (α ^ 2 * (t - s)) < p + 1 := by
    rw [Nat.div_lt_iff_lt_mul hX, add_mul, one_mul]
    have : p * s ≤ p * (α ^ 2 * (t - s)) := Nat.mul_le_mul_left p hs
    omega
  omega

lemma bern (K : ℕ) (hK : 1 ≤ K) : (4 * K) ^ K ≤ 2 * (4 * K - 2) ^ K := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have ha : (-2 : ℝ) ≤ -(1 / (2 * K)) := by
    have : 1 / (2 * (K : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have h1 := one_add_mul_le_pow ha K
  have e1 : (1 : ℝ) + K * -(1 / (2 * K)) = 1 / 2 := by field_simp; ring
  have e2 : (1 : ℝ) + -(1 / (2 * K)) = ((4 * K - 2 : ℕ) : ℝ) / (4 * K) := by
    rw [Nat.cast_sub (by omega)]; push_cast; field_simp; ring
  rw [e1, e2, div_pow] at h1
  have hpos : (0 : ℝ) < (4 * K) ^ K := by positivity
  rw [le_div_iff₀ hpos] at h1
  have : ((4 * K : ℕ) : ℝ) ^ K ≤ 2 * ((4 * K - 2 : ℕ) : ℝ) ^ K := by push_cast at h1 ⊢; linarith
  exact_mod_cast this

lemma prec_real (d p α b logT sW eW S K : ℕ) (jI : Fin (d + 1) → ℕ) (hK : K = d + 1) (hK1 : 1 ≤ K)
    (hp64 : 64 ≤ p) (hsW : sW ≤ p * p) (hE : eW ≤ p + 1) (hJ : ∀ i, jI i ≤ p) (hSle : S ≤ 2 ^ logT)
    (hprec : 250 * K * p ^ 2 * 2 ^ (2 * logT + 2 * b + 6 * K * α ^ 2) ≤ 2 ^ p) :
    2 * (3 * ((∑ _i : Fin (d + 1), (6 * sW + 4 : ℝ)) + (Real.sqrt 2 + 3 * 5 + 3) +
      ∑ i, ((jI i : ℝ) * (10 * eW + 12) + 4)) + 2) *
      ((S : ℕ) : ℝ) ^ 2 * 2 ^ (2 * b + 6 * (d + 1) * α ^ 2) < 2 ^ p := by
  have hKr : ((d + 1 : ℕ) : ℝ) = K := by rw [hK]
  have hpr : (64 : ℝ) ≤ p := by exact_mod_cast hp64
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hs1 : (∑ _i : Fin (d + 1), (6 * sW + 4 : ℝ)) ≤ K * (6 * p ^ 2 + 4) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hKr]
    have : (sW : ℝ) ≤ p * p := by exact_mod_cast hsW
    gcongr; nlinarith
  have hs2 : ∑ i : Fin (d + 1), ((jI i : ℝ) * (10 * eW + 12) + 4) ≤ K * (p * (10 * (p + 1) + 12) + 4) := by
    have hEr : (eW : ℝ) ≤ p + 1 := by exact_mod_cast hE
    calc _ ≤ ∑ _i : Fin (d + 1), ((p : ℝ) * (10 * (p + 1) + 12) + 4) := by
          apply Finset.sum_le_sum; intro i _
          have : (jI i : ℝ) ≤ p := by exact_mod_cast hJ i
          gcongr
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hKr]
  have hsq : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hKP : 64 * (K : ℝ) ≤ K * p := by nlinarith
  have hKP2 : 64 * ((K : ℝ) * p) ≤ K * p ^ 2 := by
    have : (0 : ℝ) ≤ K * p := by positivity
    nlinarith
  have key : 2 * (3 * ((K : ℝ) * (6 * p ^ 2 + 4) + 20 + K * (p * (10 * (p + 1) + 12) + 4)) + 2)
      ≤ 110 * K * p ^ 2 := by
    ring_nf; linarith
  have hA : 2 * (3 * ((∑ _i : Fin (d + 1), (6 * sW + 4 : ℝ)) + (Real.sqrt 2 + 3 * 5 + 3) +
      ∑ i, ((jI i : ℝ) * (10 * eW + 12) + 4)) + 2) ≤ 110 * K * p ^ 2 := by
    linarith
  have hS2 : ((S : ℕ) : ℝ) ^ 2 ≤ 2 ^ (2 * logT) := by
    rw [pow_mul']
    gcongr
    exact_mod_cast hSle
  have hpr2 : (250 * K * p ^ 2 * 2 ^ (2 * logT + 2 * b + 6 * K * α ^ 2) : ℝ) ≤ 2 ^ p := by
    have := (Nat.cast_le (α := ℝ)).2 hprec
    push_cast at this
    exact this
  rw [pow_add, pow_add] at hpr2
  have e3 : (2 : ℝ) ^ (2 * b + 6 * (d + 1) * α ^ 2) = 2 ^ (2 * b) * 2 ^ (6 * K * α ^ 2) := by
    rw [hK, pow_add]
  have hpos2 : (0 : ℝ) < K * p ^ 2 := by positivity
  have hpos3 : (0 : ℝ) < 2 ^ (2 * logT) := by positivity
  calc _ ≤ (110 * K * p ^ 2 * 2 ^ (2 * logT) * 2 ^ (2 * b + 6 * (d + 1) * α ^ 2) : ℝ) := by
        gcongr
    _ < (250 * K * p ^ 2 * 2 ^ (2 * logT) * 2 ^ (2 * b + 6 * (d + 1) * α ^ 2) : ℝ) := by
        gcongr; norm_num
    _ ≤ 2 ^ p := by rw [e3]; linarith

theorem refStep_conds (q : Params) (d : ℕ) (hK : q.K = d + 1)
    (hslen : q.s.length = q.K)
    (hsodd : ∀ i < q.K, Odd (q.s.getD i 1))
    (hscop : ∀ i < q.K, ∀ j < q.K, i ≠ j → Nat.Coprime (q.s.getD i 1) (q.s.getD j 1))
    (hsb : ∀ i < q.K, (4 * q.K - 2) * 2 ^ q.te i < 4 * q.K * q.s.getD i 1 ∧
      4 * q.K * q.s.getD i 1 ≤ (4 * q.K - 1) * 2 ^ q.te i)
    (hL : 1 ≤ q.L) (hT : 4 * q.L ≤ 2 ^ q.logT) (hdh : q.dh < q.K) (he : 2 ≤ q.e)
    (hlog : q.logOuter ≤ 2 * q.fn) (hPdef : q.P = 2 * q.p + q.logT + 8)
    (hα : 2 * q.K ≤ q.α) (hαp : q.α ^ 2 ≤ q.p) (hb : q.b ≤ q.p) (hp64 : 64 ≤ q.p)
    (hprec : 250 * q.K * q.p ^ 2 * 2 ^ (2 * q.logT + 2 * q.b + 6 * q.K * q.α ^ 2) ≤ 2 ^ q.p) :
    (∀ i < q.K, 0 < q.s.getD i 1) ∧ 2 * q.L - 1 ≤ q.S ∧
    (∀ u v : List ℤ, u.length = q.S → v.length = q.S →
      (∀ a ∈ u, 0 ≤ a ∧ a < 2 ^ q.b) → (∀ a ∈ v, 0 ≤ a ∧ a < 2 ^ q.b) →
      exactConvL q u v = listOf q.s (cconv q.s u v)) := by
  have hspos : ∀ i < q.K, 0 < q.s.getD i 1 := fun i hi => (hsodd i hi).pos
  have hK1 : 1 ≤ q.K := by omega
  have hsd : q.s.length = d + 1 := by omega
  -- per-axis facts
  have hst : ∀ i : Fin (d + 1), sF q d i < tF q d i := by
    intro i
    have h2 := (hsb i (by omega)).2
    have h4 : 0 < 2 ^ q.te i := by positivity
    show q.s.getD i 1 < 2 ^ q.te i
    by_contra hc; push Not at hc
    have : 4 * q.K * 2 ^ q.te i ≤ 4 * q.K * q.s.getD i 1 := Nat.mul_le_mul_left _ hc
    have : (4 * q.K - 1) * 2 ^ q.te i < 4 * q.K * 2 ^ q.te i :=
      Nat.mul_lt_mul_of_pos_right (by omega) h4
    omega
  have hcop : ∀ i : Fin (d + 1), Nat.Coprime (sF q d i) (tF q d i) := fun i =>
    (Nat.coprime_two_right.2 (hsodd i (by omega))).pow_right _
  have hα2 : 4 * q.K ≤ q.α ^ 2 := by nlinarith
  have hx' : ∀ i : Fin (d + 1), sF q d i ≤ q.α ^ 2 * (tF q d i - sF q d i) := by
    intro i
    have h2 := (hsb i (by omega)).2
    have hlt := hst i
    show q.s.getD i 1 ≤ q.α ^ 2 * (2 ^ q.te i - q.s.getD i 1)
    change q.s.getD i 1 < 2 ^ q.te i at hlt
    obtain ⟨w, hw⟩ : ∃ w, 2 ^ q.te i = q.s.getD i 1 + w := ⟨_, (Nat.add_sub_cancel' hlt.le).symm⟩
    rw [hw] at h2 ⊢
    rw [Nat.add_sub_cancel_left]
    obtain ⟨m, hm⟩ : ∃ m, 4 * q.K = m + 1 := ⟨4 * q.K - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel, add_mul, one_mul, mul_add] at h2
    have : m * w ≤ q.α ^ 2 * w := Nat.mul_le_mul_right w (by omega)
    omega
  have hαpos : 1 ≤ q.α := by omega
  have hαle : q.α ≤ q.p := le_trans (Nat.le_self_pow (by norm_num) _) hαp
  have hpoly := pow_poly q.p (by omega)
  have hJ : ∀ i : Fin (d + 1), jIter q.p (sF q d i) (tF q d i) q.α ≤ q.p := fun i =>
    jIter_le _ _ _ _ (hx' i) (lt_of_lt_of_le (hspos i (by omega)) (hx' i))
  have hE := eWidth_le q.p q.α hαpos
  have hp : ∀ i : Fin (d + 1),
      100 * (jIter q.p (sF q d i) (tF q d i) q.α * (10 * eWidth q.p q.α + 12) + 1) ≤ 2 ^ q.p := by
    intro i
    have := hJ i
    calc _ ≤ 100 * (q.p * (10 * (q.p + 1) + 12) + 1) := by gcongr
      _ ≤ 2200 * q.p ^ 2 := by nlinarith
      _ ≤ _ := hpoly
  have hsW : sWidth q.p q.α ≤ q.p * q.p := Nat.mul_le_mul (ceilSqrt_le _) hαle
  have hpA : 4 * (6 * sWidth q.p q.α + 4) ≤ 2 ^ q.p := by nlinarith
  -- the Fermat precision
  have hPM : 4 * (q.tdims.prod : ℤ) * ((2 : ℤ) ^ q.p) ^ 2 < 2 ^ q.P := by
    rw [tdims_prod q d hK hdh, hPdef]
    push_cast
    rw [← pow_mul, show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  -- products
  have htprod : ∏ i : Fin (d + 1), tF q d i = 2 ^ q.logT := by
    rw [← tdims_prod q d hK hdh, prod_fin q.tdims d (by rw [tdims_length, hK])]
    apply Finset.prod_congr rfl; intro i _; rw [tdims_getD q i (by omega)]
  have hSfin : q.S = ∏ i : Fin (d + 1), sF q d i := prod_fin q.s d hsd
  have hSle : q.S ≤ 2 ^ q.logT := by
    rw [hSfin, ← htprod]; exact Finset.prod_le_prod' fun i _ => (hst i).le
  have hS : 2 * q.L - 1 ≤ q.S := by
    have h1 : ∏ i : Fin (d + 1), ((4 * q.K - 2) * tF q d i) ≤ ∏ i : Fin (d + 1), (4 * q.K * sF q d i) :=
      Finset.prod_le_prod' fun i _ => (hsb i (by omega)).1.le
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, htprod, ← hSfin, ← hK] at h1
    have hb' := bern q.K hK1
    have h2 : (4 * q.K) ^ q.K * 2 ^ q.logT ≤ (4 * q.K) ^ q.K * (2 * q.S) := by
      calc (4 * q.K) ^ q.K * 2 ^ q.logT ≤ 2 * (4 * q.K - 2) ^ q.K * 2 ^ q.logT :=
            Nat.mul_le_mul_right _ hb'
        _ ≤ 2 * ((4 * q.K) ^ q.K * q.S) := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ h1
        _ = (4 * q.K) ^ q.K * (2 * q.S) := by ring
    have h3 := Nat.le_of_mul_le_mul_left h2 (by positivity)
    omega
  -- the final precision condition
  have hSle' : ∏ i : Fin (d + 1), sF q d i ≤ 2 ^ q.logT := hSfin ▸ hSle
  have hprec' := prec_real d q.p q.α q.b q.logT (sWidth q.p q.α) (eWidth q.p q.α) _ q.K
    (fun i => jIter q.p (sF q d i) (tF q d i) q.α) hK hK1 hp64 hsW hE hJ hSle' hprec
  refine ⟨hspos, hS, ?_⟩
  intro u v hu hv hub hvb
  exact exactConvL_cconv q d hK hdh hslen hspos he (by omega) hlog hPM hst hcop (by omega) hαp hx' hp hpA
    hb hprec' u v hu hv hub hvb

theorem refStep_correct (q : Params) (d : ℕ) (hK : q.K = d + 1)
    (hslen : q.s.length = q.K)
    (hsodd : ∀ i < q.K, Odd (q.s.getD i 1))
    (hscop : ∀ i < q.K, ∀ j < q.K, i ≠ j → Nat.Coprime (q.s.getD i 1) (q.s.getD j 1))
    (hsb : ∀ i < q.K, (4 * q.K - 2) * 2 ^ q.te i < 4 * q.K * q.s.getD i 1 ∧
      4 * q.K * q.s.getD i 1 ≤ (4 * q.K - 1) * 2 ^ q.te i)
    (hL : 1 ≤ q.L) (hT : 4 * q.L ≤ 2 ^ q.logT) (hdh : q.dh < q.K) (he : 2 ≤ q.e)
    (hlog : q.logOuter ≤ 2 * q.fn) (hPdef : q.P = 2 * q.p + q.logT + 8)
    (hα : 2 * q.K ≤ q.α) (hαp : q.α ^ 2 ≤ q.p) (hb : q.b ≤ q.p) (hp64 : 64 ≤ q.p)
    (hprec : 250 * q.K * q.p ^ 2 * 2 ^ (2 * q.logT + 2 * q.b + 6 * q.K * q.α ^ 2) ≤ 2 ^ q.p)
    (x y : ℕ) (hx : x < 2 ^ (q.b * q.L)) (hy : y < 2 ^ (q.b * q.L)) :
    refStep q x y = x * y := by
  obtain ⟨hspos, hS, hconv⟩ := refStep_conds q d hK hslen hsodd hscop hsb hL hT hdh he hlog hPdef hα hαp hb hp64 hprec
  exact refStep_eq_of q hslen hspos hscop hL hS hconv x y hx hy

theorem refStep_digits (q : Params) (d : ℕ) (hK : q.K = d + 1)
    (hslen : q.s.length = q.K)
    (hsodd : ∀ i < q.K, Odd (q.s.getD i 1))
    (hscop : ∀ i < q.K, ∀ j < q.K, i ≠ j → Nat.Coprime (q.s.getD i 1) (q.s.getD j 1))
    (hsb : ∀ i < q.K, (4 * q.K - 2) * 2 ^ q.te i < 4 * q.K * q.s.getD i 1 ∧
      4 * q.K * q.s.getD i 1 ≤ (4 * q.K - 1) * 2 ^ q.te i)
    (hL : 1 ≤ q.L) (hT : 4 * q.L ≤ 2 ^ q.logT) (hdh : q.dh < q.K) (he : 2 ≤ q.e)
    (hlog : q.logOuter ≤ 2 * q.fn) (hPdef : q.P = 2 * q.p + q.logT + 8)
    (hα : 2 * q.K ≤ q.α) (hαp : q.α ^ 2 ≤ q.p) (hb : q.b ≤ q.p) (hp64 : 64 ≤ q.p)
    (hprec : 250 * q.K * q.p ^ 2 * 2 ^ (2 * q.logT + 2 * q.b + 6 * q.K * q.α ^ 2) ≤ 2 ^ q.p)
    (x y : ℕ) :
    ∀ c ∈ crtOut q.s (2 * q.L - 1)
      (exactConvL q (crtIn q.s (chunksL q.b q.L x)) (crtIn q.s (chunksL q.b q.L y))),
      0 ≤ c ∧ c < 2 ^ (2 * q.b + q.logT) := by
  obtain ⟨hspos, hS, hconv⟩ := refStep_conds q d hK hslen hsodd hscop hsb hL hT hdh he hlog hPdef hα hαp hb hp64 hprec
  intro c hc
  obtain ⟨h0, h1⟩ := refStep_digits_of q hslen hspos hscop hL hS hconv x y c hc
  refine ⟨h0, lt_of_lt_of_le h1 ?_⟩
  rw [pow_add, mul_comm]
  have : (q.L : ℤ) ≤ 2 ^ q.logT := by
    have : 4 * q.L ≤ 2 ^ q.logT := hT
    exact_mod_cast (by omega : q.L ≤ 2 ^ q.logT)
  exact mul_le_mul_of_nonneg_left this (by positivity)

end IntMul.HvdH.RefPf

end

-- ===== Solutions.HvdH.Coprime
section

namespace IntMul.HvdH.Cop

/-- One group of the parameter choice: below `(1-η) t` with `η = 1/(4d)` there are `d` numbers
`1 + Q (m₀ - i)` in `((1-2η) t, (1-η) t]`. -/
lemma group_choice (d t Q : ℕ) (hd : 1 ≤ d) (hQ : 0 < Q) (ht : 4 * d * d * Q + 4 * d ≤ t) :
    d ≤ ((4 * d - 1) * t - 4 * d) / (4 * d * Q) ∧ ∀ i < d,
      (4 * d - 2) * t < 4 * d * (1 + Q * (((4 * d - 1) * t - 4 * d) / (4 * d * Q) - i)) ∧
      4 * d * (1 + Q * (((4 * d - 1) * t - 4 * d) / (4 * d * Q) - i)) ≤ (4 * d - 1) * t := by
  set N := 4 * d * Q with hN
  have hN0 : 0 < N := by positivity
  set a := (4 * d - 1) * t - 4 * d with ha
  set m0 := a / N with hm0
  have h1 : N * m0 ≤ a := Nat.mul_div_le a N
  have h2 : a < N * (m0 + 1) := Nat.lt_mul_div_succ a hN0
  have h4d : 4 ≤ 4 * d := by omega
  have hta : (4 * d - 1) * t = a + 4 * d := by
    have : 4 * d ≤ (4 * d - 1) * t := by
      calc 4 * d ≤ t := by nlinarith
        _ ≤ (4 * d - 1) * t := Nat.le_mul_of_pos_left t (by omega)
    omega
  have hNd : N * d ≤ t := by
    have : N * d = 4 * d * d * Q := by rw [hN]; ring
    omega
  have hm0d : d ≤ m0 := by
    by_contra hc
    push Not at hc
    have : N * (m0 + 1) ≤ N * d := Nat.mul_le_mul_left N hc
    -- a < N d ≤ t but a = (4d-1) t - 4d ≥ 3t - 4d ≥ t
    have h3 : 3 * t ≤ (4 * d - 1) * t := Nat.mul_le_mul_right t (by omega)
    omega
  refine ⟨hm0d, fun i hi => ?_⟩
  have hsub : Q * (m0 - i) = Q * m0 - Q * i := Nat.mul_sub _ _ _
  have hNi : N * i ≤ N * m0 := Nat.mul_le_mul_left N (by omega)
  have hNi' : N * i + N ≤ N * d := by
    have := Nat.mul_le_mul_left N (show i + 1 ≤ d by omega); rwa [mul_add, mul_one] at this
  have hA : 4 * d * (Q * m0) = N * m0 := by rw [hN]; ring
  have hB : 4 * d * (Q * i) = N * i := by rw [hN]; ring
  have e1 : 4 * d * (1 + Q * (m0 - i)) = 4 * d + (N * m0 - N * i) := by
    rw [Nat.mul_sub, mul_add, mul_one, Nat.mul_sub, hA, hB]
  have h3 : (4 * d - 2) * t + t = (4 * d - 1) * t := by
    rw [← Nat.succ_mul]; congr 1; omega
  rw [e1]
  rw [mul_add, mul_one] at h2
  generalize N * m0 = P at *
  generalize N * i = Pi at *
  generalize N * d = Pd at *
  constructor
  · omega
  · omega

end IntMul.HvdH.Cop

end

-- ===== Solutions.HvdH.Ref.MkParams
section

/-! The parameters `mkParams K N` meet the conditions of `refStep_correct` for large `N`. -/

namespace IntMul.HvdH.RefPf
open IntMul.HvdH IntMul.HvdH.Ref

theorem copS_spec (d d' r : ℕ) (hd : 1 ≤ d) (hd' : d' ≤ d) (hr : 2 ∣ r)
    (hbig : 64 * d ^ 2 * (256 * d ^ 2).factorial ≤ r) :
    (∀ i < d, Odd ((copS d d' r).getD i 1)) ∧
    (∀ i < d, ∀ j < d, i ≠ j → Nat.Coprime ((copS d d' r).getD i 1) ((copS d d' r).getD j 1)) ∧
      ∀ i < d, (4 * d - 2) * (if i < d' then r / 2 else r) < 4 * d * (copS d d' r).getD i 1 ∧
        4 * d * (copS d d' r).getD i 1 ≤ (4 * d - 1) * (if i < d' then r / 2 else r) := by
  set D := 256 * d ^ 2 with hD
  set F := D.factorial with hF
  have hF0 : 0 < F := Nat.factorial_pos D
  set Q := 2 * F * (r / (2 * F * D) + 1) with hQ
  have hQ0 : 0 < Q := by positivity
  have hD0 : 0 < D := by positivity
  -- `Q D > r` and `Q ≤ r / D + 2F`
  have hQD : r < Q * D := by
    have := Nat.lt_div_mul_add (a := r) (show 0 < 2 * F * D by positivity)
    rw [hQ]; nlinarith
  have hQle : Q * D ≤ r + 2 * F * D := by
    rw [hQ, mul_add, mul_one, add_mul]
    have := Nat.div_mul_le_self r (2 * F * D)
    nlinarith
  -- both groups satisfy the size hypothesis
  have hbig' : 64 * d ^ 2 * F ≤ r := hbig
  have hsize : ∀ t, r ≤ 2 * t → 4 * d * d * Q + 4 * d ≤ t := by
    intro t ht
    -- 4 d² Q * 64 = Q * D / 4 * ... : 256 d² Q = Q D ≤ r + 2 F D
    have e : 256 * (4 * d * d * Q) = 4 * (Q * D) := by rw [hD]; ring
    have hFD : 2 * F * D = 512 * d ^ 2 * F := by rw [hD]; ring
    have h4d : 64 * 4 * d ≤ r := by
      have hDF : D ≤ F := Nat.self_le_factorial D
      have hd2 : d ≤ d ^ 2 := by nlinarith
      have : 64 * 4 * d ≤ 64 * d ^ 2 * D := by
        rw [hD]
        have : 1 ≤ d ^ 2 := by nlinarith
        nlinarith
      have : 64 * d ^ 2 * D ≤ 64 * d ^ 2 * F := Nat.mul_le_mul_left _ hDF
      omega
    nlinarith
  obtain ⟨g1d, g1⟩ := Cop.group_choice d (r / 2) Q hd hQ0 (hsize _ (by omega))
  obtain ⟨g2d, g2⟩ := Cop.group_choice d r Q hd hQ0 (hsize _ (by omega))
  set m1 := ((4 * d - 1) * (r / 2) - 4 * d) / (4 * d * Q)
  set m2 := ((4 * d - 1) * r - 4 * d) / (4 * d * Q)
  let m : ℕ → ℕ := fun i => if i < d' then m1 - i else m2 - (i - d')
  have hget : ∀ i < d, (copS d d' r).getD i 1 = 1 + Q * m i := by
    intro i hi
    simp [copS, copQ, List.getD_eq_getElem?_getD, hi, m, m1, m2, Q, F, D]
  refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_, fun i hi => ?_⟩
  · rw [hget i hi]
    have hE : Even Q := even_iff_two_dvd.2 ⟨F * (r / (2 * F * D) + 1), by rw [hQ]; ring⟩
    exact (hE.mul_right (m i)).one_add
  · -- coprimality via the window lemma: all indices are ≤ D
    have hmD : ∀ k, m k ≤ D := by
      intro k
      have hm2 : m2 ≤ D := by
        apply Nat.div_le_of_le_mul
        have h2 : (4 * d - 1) * r - 4 * d ≤ 4 * d * r := by
          have : (4 * d - 1) * r ≤ 4 * d * r := Nat.mul_le_mul_right r (by omega)
          omega
        calc (4 * d - 1) * r - 4 * d ≤ 4 * d * r := h2
          _ ≤ 4 * d * (Q * D) := Nat.mul_le_mul_left _ hQD.le
          _ = 4 * d * Q * D := by ring
      have h12 : m1 ≤ m2 := Nat.div_le_div_right (by
        have : (4 * d - 1) * (r / 2) ≤ (4 * d - 1) * r := Nat.mul_le_mul_left _ (by omega)
        omega)
      simp only [m]; split_ifs
      · exact ((Nat.sub_le _ _).trans h12).trans hm2
      · exact (Nat.sub_le _ _).trans hm2
    have hval : ∀ k < d, 4 * d * (1 + Q * m k) ≤ (4 * d - 1) * (if k < d' then r / 2 else r) ∧
        (4 * d - 2) * (if k < d' then r / 2 else r) < 4 * d * (1 + Q * m k) := by
      intro k hk0
      simp only [m]
      split_ifs with hk
      · exact ⟨(g1 k (by omega)).2, (g1 k (by omega)).1⟩
      · exact ⟨(g2 (k - d') (by omega)).2, (g2 (k - d') (by omega)).1⟩
    have hlt : (4 * d - 1) * (r / 2) < (4 * d - 2) * r := by
      have e2 : (4 * d - 1) * (r / 2) * 2 = (4 * d - 1) * r := by
        rw [mul_assoc, Nat.div_mul_cancel hr]
      have hr0 : 0 < r := by
        have : 0 < 64 * d ^ 2 * F := by positivity
        omega
      have : (4 * d - 1) * r < 2 * ((4 * d - 2) * r) := by
        rw [← mul_assoc]; exact Nat.mul_lt_mul_of_pos_right (by omega) hr0
      omega
    have hne : m i ≠ m j := by
      intro heq
      have hvi := hval i hi
      have hvj := hval j hj
      rw [heq] at hvi
      by_cases hi' : i < d' <;> by_cases hj' : j < d'
      · dsimp only [m] at heq; rw [if_pos hi', if_pos hj'] at heq
        exact hij (by omega)
      · rw [if_pos hi'] at hvi; rw [if_neg hj'] at hvj; omega
      · rw [if_neg hi'] at hvi; rw [if_pos hj'] at hvj; omega
      · dsimp only [m] at heq; rw [if_neg hi', if_neg hj'] at heq
        exact hij (by omega)
    rw [hget i hi, hget j hj]
    exact IntMul.HvdH.coprime_window D Q (m i) (m j) (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) hne
      (by have := hmD i; omega) (by have := hmD j; omega)
  · rw [hget i hi]
    simp only [m]
    split_ifs with hk
    · exact g1 i (by omega)
    · exact g2 (i - d') (by omega)

lemma ceilSqrt_sq (x : ℕ) : ceilSqrt x ^ 2 ≤ 4 * x := by
  unfold ceilSqrt
  have h1 := Nat.sqrt_le' x
  split_ifs with h
  · have hx : 1 ≤ x := by
      rcases Nat.eq_zero_or_pos x with h0 | h0
      · subst h0; simp at h
      · exact h0
    have hs : 1 ≤ Nat.sqrt x := Nat.sqrt_pos.2 (by omega)
    nlinarith
  · nlinarith

lemma ceilSqrt_pos (x : ℕ) (hx : 1 ≤ x) : 1 ≤ ceilSqrt x := by
  unfold ceilSqrt
  split_ifs
  · omega
  · exact Nat.sqrt_pos.2 hx

lemma logT_add (q : Params) (hdh : q.dh ≤ q.K) (he : 1 ≤ q.e) : q.logT + q.dh = q.K * q.e := by
  have key : ∀ n, ((List.range n).map q.te).sum + min n q.dh = n * q.e := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have hte : q.te n = if n < q.dh then q.e - 1 else q.e := rfl
      rw [hte, add_mul, one_mul]
      split_ifs with h
      · have : min (n + 1) q.dh = min n q.dh + 1 := by omega
        omega
      · have : min (n + 1) q.dh = min n q.dh := by omega
        omega
  have := key q.K
  rw [min_eq_right hdh] at this
  exact this

lemma two_mul_le_pow (n : ℕ) (hn : 4 ≤ n) : 2 * n ≤ 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have : 2 ^ (n + 1 - 1) = 2 * 2 ^ (n - 1) := by
      rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]; ring
    omega

lemma E_lower (N b L E B : ℕ) (hb : b = Nat.size N) (hN : 1 ≤ N) (hL : N ≤ b * L)
    (hE : 4 * L ≤ 2 ^ E) (hB : B = Nat.size b) : b + 1 < B + E := by
  have hb1 : 1 ≤ b := by rw [hb]; exact Nat.lt_size.2 (by simpa using hN)
  have h1 : 2 ^ (b - 1) ≤ N := Nat.lt_size.1 (by omega)
  have h2 : b < 2 ^ B := by rw [hB]; exact Nat.lt_size_self b
  have h3 : 2 ^ (b + 1) = 4 * 2 ^ (b - 1) := by
    rw [show b + 1 = (b - 1) + 2 by omega, pow_add]; ring
  have h4 : 2 ^ (b + 1) < 2 ^ (B + E) := by
    calc 2 ^ (b + 1) ≤ 4 * N := by omega
      _ ≤ 4 * (b * L) := by omega
      _ = b * (4 * L) := by ring
      _ ≤ b * 2 ^ E := Nat.mul_le_mul_left _ hE
      _ < 2 ^ B * 2 ^ E := Nat.mul_lt_mul_of_pos_right h2 (by positivity)
      _ = 2 ^ (B + E) := by rw [pow_add]
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h4

lemma prec_mk (K b B E c p : ℕ) (hK : 1 ≤ K) (hc : 1 ≤ c) (hc4 : c ^ 4 ≤ 64 * b) (hKb : K ≤ b)
    (hBb : B ≤ b) (hbB : b < 2 ^ B) (hE : E ≤ b + 3)
    (hp : p = 2 * b + 2 * E + 6 * K * (K * (c + 2)) ^ 2 + 8 * B + 4 * K + 64) :
    250 * K * p ^ 2 ≤ 2 ^ (8 * B + 4 * K + 64) := by
  have hb : 1 ≤ b := le_trans hK hKb
  set X := K ^ 3 * c ^ 2 * b with hX
  have hK3 : 1 ≤ K ^ 3 := Nat.one_le_pow _ _ hK
  have hc2 : 1 ≤ c ^ 2 := Nat.one_le_pow _ _ hc
  have hX1 : 1 ≤ X := Nat.mul_le_mul (Nat.mul_le_mul hK3 hc2) hb
  have hbX : b ≤ X := by
    calc b = 1 * 1 * b := by ring
      _ ≤ K ^ 3 * c ^ 2 * b := Nat.mul_le_mul_right _ (Nat.mul_le_mul hK3 hc2)
  have hKX : K ≤ X := le_trans hKb hbX
  have hα : K * (c + 2) ≤ 3 * K * c := by nlinarith
  have hα2 : (K * (c + 2)) ^ 2 ≤ 9 * K ^ 2 * c ^ 2 := by
    calc (K * (c + 2)) ^ 2 ≤ (3 * K * c) ^ 2 := Nat.pow_le_pow_left hα 2
      _ = 9 * K ^ 2 * c ^ 2 := by ring
  have hmid : 6 * K * (K * (c + 2)) ^ 2 ≤ 54 * X := by
    calc 6 * K * (K * (c + 2)) ^ 2 ≤ 6 * K * (9 * K ^ 2 * c ^ 2) := Nat.mul_le_mul_left _ hα2
      _ = 54 * (K ^ 3 * c ^ 2 * 1) := by ring
      _ ≤ 54 * X := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb)
  have hp' : p ≤ 140 * X := by omega
  have hX2 : X ^ 2 ≤ 64 * (K ^ 6 * b ^ 3) := by
    calc X ^ 2 = K ^ 6 * c ^ 4 * b ^ 2 := by rw [hX]; ring
      _ ≤ K ^ 6 * (64 * b) * b ^ 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hc4)
      _ = 64 * (K ^ 6 * b ^ 3) := by ring
  have hK4 : K ^ 4 ≤ 2 ^ (4 * K) := by
    rw [pow_mul']; exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le 4
  have hb6 : b ^ 6 ≤ 2 ^ (6 * B) := by
    rw [pow_mul']; exact Nat.pow_le_pow_left hbB.le 6
  have hK7 : K ^ 7 * b ^ 3 ≤ K ^ 4 * b ^ 6 := by
    have : K ^ 3 ≤ b ^ 3 := Nat.pow_le_pow_left hKb 3
    calc K ^ 7 * b ^ 3 = K ^ 4 * (K ^ 3 * b ^ 3) := by ring
      _ ≤ K ^ 4 * (b ^ 3 * b ^ 3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ this)
      _ = K ^ 4 * b ^ 6 := by ring
  calc 250 * K * p ^ 2 ≤ 250 * K * (140 * X) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp' 2)
    _ = 250 * 19600 * K * X ^ 2 := by ring
    _ ≤ 250 * 19600 * K * (64 * (K ^ 6 * b ^ 3)) := Nat.mul_le_mul_left _ hX2
    _ = 313600000 * (K ^ 7 * b ^ 3) := by ring
    _ ≤ 2 ^ 29 * (K ^ 4 * b ^ 6) := Nat.mul_le_mul (by norm_num) hK7
    _ ≤ 2 ^ 29 * (2 ^ (4 * K) * 2 ^ (6 * B)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hK4 hb6)
    _ = 2 ^ (29 + 4 * K + 6 * B) := by rw [pow_add, pow_add]; ring
    _ ≤ 2 ^ (8 * B + 4 * K + 64) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- One recursive step with the explicit threshold: the product is exact and the digits handed to
`evalDigits` are the nonnegative convolution coefficients, below `2^(2b + logT)`. -/
theorem mkParams_step (K : ℕ) (hK : 1 ≤ K) (N : ℕ)
    (hN : 2 ^ 2 ^ (K * (64 * K ^ 2 * (256 * K ^ 2).factorial) + 4) ≤ N)
    (x y : ℕ) (hx : x < 2 ^ N) (hy : y < 2 ^ N) :
    refStep (mkParams K N) x y = x * y ∧
    ∀ c ∈ crtOut (mkParams K N).s (2 * (mkParams K N).L - 1)
      (exactConvL (mkParams K N) (crtIn (mkParams K N).s (chunksL (mkParams K N).b (mkParams K N).L x))
        (crtIn (mkParams K N).s (chunksL (mkParams K N).b (mkParams K N).L y))),
      0 ≤ c ∧ c < 2 ^ (2 * (mkParams K N).b + (mkParams K N).logT) := by
  set C := 64 * K ^ 2 * (256 * K ^ 2).factorial with hC
  set q := mkParams K N with hq
  have qK : q.K = K := rfl
  have qb : q.b = Nat.size N := rfl
  have qL : q.L = (N + q.b - 1) / q.b := rfl
  have qe : q.e = (Nat.clog 2 (4 * q.L) + K - 1) / K := rfl
  have qdh : q.dh = K * q.e - Nat.clog 2 (4 * q.L) := rfl
  have qs : q.s = copS K q.dh (2 ^ q.e) := rfl
  have qα : q.α = K * (ceilSqrt (ceilSqrt q.b) + 2) := rfl
  have qp : q.p = 2 * q.b + 2 * Nat.clog 2 (4 * q.L) + 6 * K * q.α ^ 2 + 8 * Nat.size q.b + 4 * K + 64 := rfl
  have qP : q.P = 2 * q.p + Nat.clog 2 (4 * q.L) + 8 := rfl
  have qfn : q.fn = 4 * q.r * q.P := rfl
  set b := q.b with hb
  set L := q.L with hLdef
  set E := Nat.clog 2 (4 * L) with hEdef
  set B := Nat.size b with hBdef
  set c := ceilSqrt (ceilSqrt b) with hcdef
  -- sizes
  have hC64 : 64 ≤ C := by
    have := Nat.factorial_pos (256 * K ^ 2)
    have : 1 ≤ K ^ 2 := Nat.one_le_pow _ _ hK
    rw [hC]; nlinarith
  have hKC : K ≤ K * C := Nat.le_mul_of_pos_right K (by omega)
  have hbig1 : 2 ^ (K * C + 4) < b := by rw [qb]; exact Nat.lt_size.2 hN
  have hB : K * C + 4 < B := Nat.lt_size.2 hbig1.le
  have hNpos : 1 ≤ N := le_trans Nat.one_le_two_pow hN
  have hb1 : 1 ≤ b := lt_of_le_of_lt (Nat.zero_le _) hbig1
  have hbB : 2 ^ (B - 1) ≤ b := Nat.lt_size.1 (by omega)
  have hbB' : b < 2 ^ B := Nat.lt_size_self b
  have hNb : N < 2 ^ b := by rw [qb]; exact Nat.lt_size_self N
  have hBb : B ≤ b := Nat.size_le.2 Nat.lt_two_pow_self
  have hbb : b < 2 ^ b := Nat.lt_two_pow_self
  -- L
  have hNbL : N ≤ b * L := by
    have h := Nat.lt_mul_div_succ (N + b - 1) (show 0 < b by omega)
    rw [qL]
    rw [mul_add, mul_one] at h
    omega
  have hL1 : 1 ≤ L := by
    rw [qL]
    exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hLb : L * b ≤ N + b - 1 := by rw [qL]; exact Nat.div_mul_le_self _ _
  have hLle : L ≤ N + b := by
    have : L ≤ L * b := Nat.le_mul_of_pos_right L (by omega)
    omega
  -- E
  have hE4 : 4 * L ≤ 2 ^ E := Nat.le_pow_clog (by norm_num) _
  have hEle : E ≤ b + 3 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add]; omega
  have hElow := E_lower N b L E B qb hNpos hNbL hE4 rfl
  have h2B : 2 * B ≤ 2 ^ (B - 1) := two_mul_le_pow B (by omega)
  have hEC : K * C + 6 ≤ E := by omega
  -- e and dh
  have he' : q.e = (E + K - 1) / K := qe
  have hKe1 : E ≤ K * q.e := by
    have h := Nat.lt_mul_div_succ (E + K - 1) (show 0 < K by omega)
    rw [he']; rw [mul_add, mul_one] at h; omega
  have hKe2 : K * q.e ≤ E + K - 1 := by rw [he']; exact Nat.mul_div_le _ _
  have hdh : q.dh < K := by rw [qdh]; omega
  have heC : C ≤ q.e := by
    have : K * C ≤ K * q.e := by omega
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have he2 : 2 ≤ q.e := by omega
  have hbig : 64 * K ^ 2 * (256 * K ^ 2).factorial ≤ 2 ^ q.e :=
    le_trans Nat.lt_two_pow_self.le (Nat.pow_le_pow_right (by norm_num) heC)
  have hlogT : q.logT = E := by
    have := logT_add q (by rw [qK]; omega) (by omega)
    rw [qK, qdh] at this
    omega
  -- the source lengths
  obtain ⟨hodd, hcop, hsb⟩ := copS_spec K q.dh (2 ^ q.e) hK hdh.le (dvd_pow_self 2 (by omega)) hbig
  have hte : ∀ i, 2 ^ q.te i = if i < q.dh then 2 ^ q.e / 2 else 2 ^ q.e := by
    intro i
    unfold Params.te
    split_ifs
    · rw [show 2 ^ q.e = 2 * 2 ^ (q.e - 1) by rw [← pow_succ']; congr 1; omega]
      simp
    · rfl
  -- α and p
  have hc1 : 1 ≤ c := ceilSqrt_pos _ (ceilSqrt_pos _ hb1)
  have hc4 : c ^ 4 ≤ 64 * b := by
    have h1 := ceilSqrt_sq (ceilSqrt b)
    have h2 := ceilSqrt_sq b
    calc c ^ 4 = (c ^ 2) ^ 2 := by ring
      _ ≤ (4 * ceilSqrt b) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = 16 * ceilSqrt b ^ 2 := by ring
      _ ≤ 16 * (4 * b) := Nat.mul_le_mul_left _ h2
      _ = 64 * b := by ring
  have hα : 2 * K ≤ q.α := by rw [qα, mul_add]; omega
  have hαp : q.α ^ 2 ≤ q.p := by
    rw [qp]
    have : q.α ^ 2 ≤ 6 * K * q.α ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hbp : b ≤ q.p := by rw [qp]; omega
  have hp64 : 64 ≤ q.p := by rw [qp]; omega
  have hKb : K ≤ b := by
    have : K * C + 4 < 2 ^ (K * C + 4) := Nat.lt_two_pow_self
    omega
  have hpm := prec_mk K b B E c q.p hK hc1 hc4 hKb hBb hbB' hEle (by rw [qp, qα])
  have hprec : 250 * q.K * q.p ^ 2 * 2 ^ (2 * q.logT + 2 * q.b + 6 * q.K * q.α ^ 2) ≤ 2 ^ q.p := by
    rw [qK, hlogT]
    have e : 2 ^ q.p = 2 ^ (8 * B + 4 * K + 64) * 2 ^ (2 * E + 2 * b + 6 * K * q.α ^ 2) := by
      rw [← pow_add]; congr 1; rw [qp]; omega
    rw [e]
    exact Nat.mul_le_mul_right _ hpm
  have hlog : q.logOuter ≤ 2 * q.fn := by
    have h1 := logT_eq q (K - 1) (by omega) (by omega)
    have h2 := logOuter_eq q (K - 1) (by omega)
    have h3 : q.P ≤ q.fn := by
      rw [qfn]; exact Nat.le_mul_of_pos_left _ (by simp [Params.r])
    rw [qP] at h3
    omega
  have hx' : x < 2 ^ (q.b * q.L) := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hNbL)
  have hy' : y < 2 ^ (q.b * q.L) := lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) hNbL)
  exact ⟨refStep_correct q (K - 1) (by omega) (by rw [qs, qK]; simp [copS])
    (fun i hi => by rw [qs]; exact hodd i hi)
    (fun i hi j hj hij => by rw [qs]; exact hcop i hi j hj hij)
    (fun i hi => by rw [hte i, qs, qK]; exact hsb i hi)
    hL1 (by rw [hlogT]; exact hE4) hdh he2 hlog (by rw [qP, hlogT]) hα hαp hbp hp64 hprec x y hx' hy',
    refStep_digits q (K - 1) (by omega) (by rw [qs, qK]; simp [copS])
    (fun i hi => by rw [qs]; exact hodd i hi)
    (fun i hi j hj hij => by rw [qs]; exact hcop i hi j hj hij)
    (fun i hi => by rw [hte i, qs, qK]; exact hsb i hi)
    hL1 (by rw [hlogT]; exact hE4) hdh he2 hlog (by rw [qP, hlogT]) hα hαp hbp hp64 hprec x y⟩

end IntMul.HvdH.RefPf

end

open IntMul.HvdH IntMul.HvdH.Ref

theorem solution (K : ℕ) (hK : 1 ≤ K) (N : ℕ)
    (hN : 2 ^ 2 ^ (K * (64 * K ^ 2 * (256 * K ^ 2).factorial) + 4) ≤ N)
    (x y : ℕ) (hx : x < 2 ^ N) (hy : y < 2 ^ N) :
    refStep (mkParams K N) x y = x * y ∧
    ∀ c ∈ crtOut (mkParams K N).s (2 * (mkParams K N).L - 1)
      (exactConvL (mkParams K N) (crtIn (mkParams K N).s (chunksL (mkParams K N).b (mkParams K N).L x))
        (crtIn (mkParams K N).s (chunksL (mkParams K N).b (mkParams K N).L y))),
      0 ≤ c ∧ c < 2 ^ (2 * (mkParams K N).b + (mkParams K N).logT) :=
  IntMul.HvdH.RefPf.mkParams_step K hK N hN x y hx hy
