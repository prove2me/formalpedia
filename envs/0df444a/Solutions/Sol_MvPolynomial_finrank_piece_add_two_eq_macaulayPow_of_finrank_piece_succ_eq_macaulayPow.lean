-- Prove2me | solution 1 for MvPolynomial.finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/0e3118df-de7b-59c8-ac23-0d2750af9772

import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map
import Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow
import Theorems.Thm_MvPolynomial_exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le
import Theorems.Thm_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow

set_option autoImplicit false

namespace GotzStep

namespace Mac

def top (d a : ℕ) : ℕ := Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)

def rem (d a : ℕ) : ℕ := a - (top d a).choose (d + 1)

theorem macaulayPow_zero (a : ℕ) : Nat.macaulayPow 0 a = 0 := by simp [Nat.macaulayPow]

theorem macaulayPow_succ (d a : ℕ) :
    Nat.macaulayPow (d + 1) a = (top d a + 1).choose (d + 2) + Nat.macaulayPow d (rem d a) := by
  rw [Nat.macaulayPow]; rfl

theorem sub_le_choose (d : ℕ) : ∀ k : ℕ, k - d ≤ k.choose (d + 1)
  | 0 => by simp
  | k + 1 => by
      rw [Nat.choose_succ_succ']
      have ih := sub_le_choose d k
      rcases lt_or_ge k d with h | h
      · have : k + 1 - d = 0 := by omega
        omega
      · have hpos : 1 ≤ k.choose d := Nat.choose_pos h
        omega

theorem choose_top_le (d a : ℕ) : (top d a).choose (d + 1) ≤ a :=
  Nat.findGreatest_spec (P := fun k => k.choose (d + 1) ≤ a) (Nat.zero_le _) (by simp)

theorem lt_choose_of_top_lt (d a : ℕ) {k : ℕ} (hk : top d a < k) : a < k.choose (d + 1) := by
  rcases le_or_gt k (a + d + 1) with h | h
  · have := Nat.findGreatest_is_greatest (P := fun k => k.choose (d + 1) ≤ a) hk h
    simpa using this
  · have := sub_le_choose d k
    omega

theorem lt_choose_top_succ (d a : ℕ) : a < (top d a + 1).choose (d + 1) :=
  lt_choose_of_top_lt d a (Nat.lt_succ_self _)

theorem top_eq_of (d a k : ℕ) (h₁ : k.choose (d + 1) ≤ a) (h₂ : a < (k + 1).choose (d + 1)) :
    top d a = k := by
  apply le_antisymm
  · by_contra h
    push Not at h
    have : (k + 1).choose (d + 1) ≤ (top d a).choose (d + 1) := Nat.choose_le_choose _ h
    have := choose_top_le d a
    omega
  · by_contra h
    push Not at h
    have := lt_choose_of_top_lt d a h
    omega

theorem le_top_of_choose_le (d a k : ℕ) (h : k.choose (d + 1) ≤ a) : k ≤ top d a := by
  by_contra h'
  push Not at h'
  have := lt_choose_of_top_lt d a h'
  omega

theorem top_lt_of_lt_choose (d a k : ℕ) (h : a < k.choose (d + 1)) : top d a < k := by
  by_contra h'
  push Not at h'
  have : k.choose (d + 1) ≤ (top d a).choose (d + 1) := Nat.choose_le_choose _ h'
  have := choose_top_le d a
  omega

theorem d_le_top (d a : ℕ) : d ≤ top d a := le_top_of_choose_le d a d (by simp)

theorem top_zero_right (d : ℕ) : top d 0 = d := top_eq_of d 0 d (by simp) (by simp)

theorem d_lt_top_of_pos (d a : ℕ) (ha : 0 < a) : d < top d a := by
  have := le_top_of_choose_le d a (d + 1) (by simp; omega)
  omega

theorem top_zero_left (a : ℕ) : top 0 a = a := top_eq_of 0 a a (by simp) (by simp)

theorem rem_zero_left (a : ℕ) : rem 0 a = 0 := by simp [rem, top_zero_left]

theorem rem_zero_right (d : ℕ) : rem d 0 = 0 := by simp [rem]

theorem rem_add_choose (d a : ℕ) : rem d a + (top d a).choose (d + 1) = a := by
  unfold rem; have := choose_top_le d a; omega

theorem rem_lt (d a : ℕ) : rem d a < (top d a).choose d := by
  have h := lt_choose_top_succ d a
  rw [Nat.choose_succ_succ'] at h
  unfold rem; have := choose_top_le d a; omega

theorem macaulayPow_lt_choose : ∀ (d m r : ℕ), r < m.choose d →
    Nat.macaulayPow d r < (m + 1).choose (d + 1)
  | 0, m, r, _ => by simp [macaulayPow_zero]
  | d + 1, m, r, h => by
      rw [macaulayPow_succ]
      show _ < (m + 1).choose (d + 2)
      have hK : top d r < m := top_lt_of_lt_choose d r m h
      have hrem : Nat.macaulayPow d (rem d r) < (top d r + 1).choose (d + 1) :=
        macaulayPow_lt_choose d (top d r) (rem d r) (rem_lt d r)
      have h1 : (top d r + 1).choose (d + 2) + (top d r + 1).choose (d + 1) =
          (top d r + 2).choose (d + 2) := by
        rw [Nat.choose_succ_succ' (top d r + 1) (d + 1), add_comm]
      have h2 : (top d r + 2).choose (d + 2) ≤ (m + 1).choose (d + 2) :=
        Nat.choose_le_choose _ (by omega)
      omega

theorem macaulayPow_mono : ∀ (d : ℕ) {a b : ℕ}, a ≤ b → Nat.macaulayPow d a ≤ Nat.macaulayPow d b
  | 0, a, b, _ => by simp [macaulayPow_zero]
  | d + 1, a, b, h => by
      have ht : top d a ≤ top d b := le_top_of_choose_le d b _ ((choose_top_le d a).trans h)
      rcases ht.eq_or_lt with ht | ht
      · rw [macaulayPow_succ, macaulayPow_succ, ht]
        have hr : rem d a ≤ rem d b := by
          have ha := rem_add_choose d a; have hb := rem_add_choose d b; rw [ht] at ha; omega
        have := macaulayPow_mono d hr
        omega
      · have h1 : Nat.macaulayPow (d + 1) a < (top d a + 1 + 1).choose (d + 1 + 1) :=
          macaulayPow_lt_choose (d + 1) (top d a + 1) a (lt_choose_top_succ d a)
        have h2 : (top d a + 1 + 1).choose (d + 1 + 1) ≤ (top d b + 1).choose (d + 1 + 1) :=
          Nat.choose_le_choose _ (by omega)
        have h3 : (top d b + 1).choose (d + 1 + 1) ≤ Nat.macaulayPow (d + 1) b := by
          rw [macaulayPow_succ]; exact Nat.le_add_right _ _
        omega

theorem macaulayPow_one (a : ℕ) : Nat.macaulayPow 1 a = (a + 1).choose 2 := by
  rw [macaulayPow_succ, top_zero_left, rem_zero_left, macaulayPow_zero]; rfl

theorem macaulayPow_zero_right : ∀ d : ℕ, Nat.macaulayPow d 0 = 0
  | 0 => macaulayPow_zero 0
  | d + 1 => by
      rw [macaulayPow_succ, top_zero_right, rem_zero_right, macaulayPow_zero_right d,
        Nat.choose_eq_zero_of_lt (by omega)]

theorem top_succ_of_le (d a : ℕ) (ha : 1 ≤ a) (h : a ≤ d + 2) : top (d + 1) a = d + 2 :=
  top_eq_of (d + 1) a (d + 2) (by rw [Nat.choose_self]; exact ha)
    (by have : (d + 2 + 1).choose (d + 1 + 1) = d + 2 + 1 := Nat.choose_succ_self_right (d + 2); omega)

theorem macaulayPow_eq_self : ∀ (d a : ℕ), a ≤ d + 1 → Nat.macaulayPow (d + 1) a = a
  | d, 0, _ => macaulayPow_zero_right (d + 1)
  | 0, a + 1, h => by
      obtain rfl : a = 0 := by omega
      rw [macaulayPow_one]; rfl
  | d + 1, a + 1, h => by
      have ht : top (d + 1) (a + 1) = d + 2 := top_succ_of_le d (a + 1) (by omega) (by omega)
      have hr : rem (d + 1) (a + 1) = a := by simp [rem, ht]
      rw [macaulayPow_succ, ht, hr, macaulayPow_eq_self d a (by omega)]
      have : (d + 2 + 1).choose (d + 1 + 2) = 1 := by
        rw [show d + 1 + 2 = d + 2 + 1 by omega, Nat.choose_self]
      omega

def low : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d + 1, a => (top d a - 1).choose (d + 1) + low d (rem d a)

theorem low_zero (a : ℕ) : low 0 a = 0 := rfl

theorem low_succ (d a : ℕ) : low (d + 1) a = (top d a - 1).choose (d + 1) + low d (rem d a) := rfl

theorem low_zero_right : ∀ d : ℕ, low d 0 = 0
  | 0 => rfl
  | d + 1 => by
      rw [low_succ, top_zero_right, rem_zero_right, low_zero_right d, Nat.choose_eq_zero_of_lt (by omega)]

theorem low_eq_zero : ∀ (d a : ℕ), a ≤ d + 1 → low (d + 1) a = 0
  | d, 0, _ => low_zero_right _
  | 0, a + 1, h => by
      obtain rfl : a = 0 := by omega
      rw [low_succ, top_zero_left, low_zero]; rfl
  | d + 1, a + 1, h => by
      have ht : top (d + 1) (a + 1) = d + 2 := top_succ_of_le d (a + 1) (by omega) (by omega)
      have hr : rem (d + 1) (a + 1) = a := by simp [rem, ht]
      rw [low_succ, ht, hr, low_eq_zero d a (by omega), Nat.choose_eq_zero_of_lt (by omega)]

theorem low_lt_choose : ∀ (d m r : ℕ), r < (m + 1).choose (d + 1) → d + 1 ≤ m →
    low (d + 1) r < m.choose (d + 1)
  | 0, m, r, h, hm => by
      rw [low_succ, top_zero_left, low_zero]
      simp only [zero_add, Nat.choose_one_right, add_zero] at h ⊢
      omega
  | d + 1, m, r, h, hm => by
      rw [low_succ]
      show (top (d + 1) r - 1).choose (d + 2) + low (d + 1) (rem (d + 1) r) < m.choose (d + 2)
      have hT : top (d + 1) r ≤ m := Nat.lt_succ_iff.1 (top_lt_of_lt_choose (d + 1) r (m + 1) h)
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr
        rw [top_zero_right, rem_zero_right, low_zero_right, Nat.choose_eq_zero_of_lt (by omega),
          zero_add]
        exact Nat.choose_pos (by omega)
      · have hT' : d + 1 < top (d + 1) r := d_lt_top_of_pos _ _ hr
        have hRlt : rem (d + 1) r < (top (d + 1) r - 1 + 1).choose (d + 1) := by
          rw [Nat.sub_add_cancel (by omega)]; exact rem_lt (d + 1) r
        have ih := low_lt_choose d (top (d + 1) r - 1) (rem (d + 1) r) hRlt (by omega)
        have h1 : (top (d + 1) r - 1).choose (d + 2) + (top (d + 1) r - 1).choose (d + 1) =
            (top (d + 1) r).choose (d + 2) := by
          have := Nat.choose_succ_succ' (top (d + 1) r - 1) (d + 1)
          rw [Nat.sub_add_cancel (show 1 ≤ top (d + 1) r by omega)] at this
          rw [add_comm]; exact this.symm
        have h2 : (top (d + 1) r).choose (d + 2) ≤ m.choose (d + 2) := Nat.choose_le_choose _ hT
        omega

theorem macaulayPow_low_add : ∀ (d a : ℕ),
    Nat.macaulayPow (d + 1) (low (d + 1) a) + a = Nat.macaulayPow (d + 1) a
  | 0, a => by
      rw [low_succ, top_zero_left, low_zero, add_zero, macaulayPow_one, macaulayPow_one,
        Nat.choose_one_right]
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rfl
      · have h2 : (a + 1).choose 2 = a + a.choose 2 := by
          have := Nat.choose_succ_succ' a 1; rw [Nat.choose_one_right] at this; exact this
        rw [Nat.sub_add_cancel ha]; omega
  | d + 1, a => by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rw [low_zero_right, add_zero]
      · set T := top (d + 1) a with hT
        set R := rem (d + 1) a with hR
        have hTd : d + 1 < T := d_lt_top_of_pos _ _ ha
        have hRa : R + T.choose (d + 2) = a := rem_add_choose (d + 1) a
        have hRlt : R < T.choose (d + 1) := rem_lt (d + 1) a
        have ih := macaulayPow_low_add d R
        rw [low_succ, macaulayPow_succ (d + 1) a]
        show Nat.macaulayPow (d + 2) ((T - 1).choose (d + 2) + low (d + 1) R) + a =
          (T + 1).choose (d + 3) + Nat.macaulayPow (d + 1) R
        rcases (show T = d + 2 ∨ d + 3 ≤ T by omega) with hT2 | hT3
        ·
          have hC : (d + 2).choose (d + 1) = d + 2 := Nat.choose_succ_self_right (d + 1)
          have hR1 : R ≤ d + 1 := by rw [hT2] at hRlt; omega
          rw [hT2, show d + 2 - 1 = d + 1 from rfl, Nat.choose_succ_self, zero_add, low_eq_zero d R hR1,
            macaulayPow_zero_right, macaulayPow_eq_self d R hR1, Nat.choose_self]
          rw [hT2, Nat.choose_self] at hRa
          omega
        ·
          have hlow : low (d + 1) R < (T - 1).choose (d + 1) :=
            low_lt_choose d (T - 1) R (by rw [Nat.sub_add_cancel (by omega)]; exact hRlt) (by omega)
          have hpasc : (T - 1).choose (d + 2) + (T - 1).choose (d + 1) = T.choose (d + 2) := by
            have := Nat.choose_succ_succ' (T - 1) (d + 1)
            rw [Nat.sub_add_cancel (show 1 ≤ T by omega)] at this
            rw [add_comm]; exact this.symm
          have hpasc' : T.choose (d + 3) + T.choose (d + 2) = (T + 1).choose (d + 3) := by
            rw [Nat.choose_succ_succ' T (d + 2), add_comm]
          have htop : top (d + 1) ((T - 1).choose (d + 2) + low (d + 1) R) = T - 1 :=
            top_eq_of (d + 1) _ (T - 1) (Nat.le_add_right _ _)
              (by rw [Nat.sub_add_cancel (show 1 ≤ T by omega)]; show _ < T.choose (d + 2); omega)
          have hrem : rem (d + 1) ((T - 1).choose (d + 2) + low (d + 1) R) = low (d + 1) R := by
            simp [rem, htop]
          rw [macaulayPow_succ, htop, hrem, Nat.sub_add_cancel (show 1 ≤ T by omega)]
          show T.choose (d + 3) + Nat.macaulayPow (d + 1) (low (d + 1) R) + a = _
          omega

theorem top_macaulayPow (d a : ℕ) :
    top (d + 1) (Nat.macaulayPow (d + 1) a) = top d a + 1 := by
  apply top_eq_of
  · rw [macaulayPow_succ]; exact Nat.le_add_right _ _
  · rw [macaulayPow_succ]
    show _ < (top d a + 1 + 1).choose (d + 1 + 1)
    rw [Nat.choose_succ_succ' (top d a + 1) (d + 1)]
    show (top d a + 1).choose (d + 2) + Nat.macaulayPow d (rem d a) <
      (top d a + 1).choose (d + 1) + (top d a + 1).choose (d + 2)
    have := macaulayPow_lt_choose d (top d a) (rem d a) (rem_lt d a)
    omega

theorem rem_macaulayPow (d a : ℕ) :
    rem (d + 1) (Nat.macaulayPow (d + 1) a) = Nat.macaulayPow d (rem d a) := by
  show Nat.macaulayPow (d + 1) a - (top (d + 1) (Nat.macaulayPow (d + 1) a)).choose (d + 1 + 1) = _
  rw [top_macaulayPow, macaulayPow_succ]
  simp

theorem le_macaulayPow (d a : ℕ) : a ≤ Nat.macaulayPow (d + 1) a := by
  have := macaulayPow_low_add d a; omega

theorem low_macaulayPow : ∀ (d a : ℕ), low (d + 1) (Nat.macaulayPow d a) = Nat.macaulayPow d a - a
  | 0, a => by rw [macaulayPow_zero, low_zero_right]; omega
  | d + 1, a => by
      rw [low_succ, top_macaulayPow, rem_macaulayPow, low_macaulayPow d (rem d a), Nat.add_sub_cancel,
        macaulayPow_succ]
      have hf : (top d a).choose (d + 1 + 1) = (top d a).choose (d + 2) := rfl
      rw [hf]
      have h1 : rem d a + (top d a).choose (d + 1) = a := rem_add_choose d a
      have h2 : rem d a ≤ Nat.macaulayPow d (rem d a) := by
        cases d with
        | zero => rw [rem_zero_left]; exact Nat.zero_le _
        | succ d => exact le_macaulayPow d _
      have h3 : (top d a).choose (d + 2) + (top d a).choose (d + 1) = (top d a + 1).choose (d + 2) := by
        rw [Nat.choose_succ_succ' (top d a) (d + 1), add_comm]
      omega

theorem macaulayPow_macaulayPow (d a : ℕ) :
    Nat.macaulayPow (d + 1) (Nat.macaulayPow d a) =
      Nat.macaulayPow d a + Nat.macaulayPow (d + 1) (Nat.macaulayPow d a - a) := by
  have h := macaulayPow_low_add d (Nat.macaulayPow d a)
  rw [low_macaulayPow] at h
  omega

theorem lt_of_macaulayPow_add_le {d t s : ℕ} (h : Nat.macaulayPow d t + s ≤ Nat.macaulayPow d s) (hs : 0 < s) :
    t < s := by
  by_contra ht
  have := macaulayPow_mono d (not_lt.mp ht)
  omega

end Mac

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

section Pieces

variable {L : Type} [Field L]

noncomputable def Ik (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) :
    Submodule L ↥(homogeneousSubmodule (Fin (n + 1)) L d) :=
  Submodule.comap (homogeneousSubmodule (Fin (n + 1)) L d).subtype (I.restrictScalars L)

theorem mem_Ik {I : Ideal (MvPolynomial (Fin (n + 1)) L)} {d : ℕ}
    (x : ↥(homogeneousSubmodule (Fin (n + 1)) L d)) :
    x ∈ Ik I d ↔ (x : MvPolynomial (Fin (n + 1)) L) ∈ I := Iff.rfl

theorem Ik_mono {I I' : Ideal (MvPolynomial (Fin (n + 1)) L)} (h : I ≤ I') (d : ℕ) : Ik I d ≤ Ik I' d :=
  fun x hx => (mem_Ik x).mpr (h ((mem_Ik x).mp hx))

theorem piece_eq (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) :
    piece I d = (↥(homogeneousSubmodule (Fin (n + 1)) L d) ⧸ Ik I d) := rfl

scoped instance finite_homogeneousSubmodule (d : ℕ) :
    Module.Finite L ↥(homogeneousSubmodule (Fin (n + 1)) L d) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  haveI : Finite {x : Fin (n + 1) →₀ ℕ | x.degree = d} :=
    ((Finsupp.finite_of_degree_le d).subset fun x (hx : x.degree = d) => le_of_eq hx).to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport L {x : Fin (n + 1) →₀ ℕ | x.degree = d})

scoped instance finite_piece (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) : Module.Finite L (piece I d) :=
  Module.Finite.quotient L _

theorem finrank_piece_add (I : Ideal (MvPolynomial (Fin (n + 1)) L)) (d : ℕ) :
    Module.finrank L (piece I d) + Module.finrank L ↥(Ik I d) =
      Module.finrank L ↥(homogeneousSubmodule (Fin (n + 1)) L d) := by
  unfold Ik; exact Submodule.finrank_quotient_add_finrank _

theorem finrank_piece_eq_of_Ik_eq {I I' : Ideal (MvPolynomial (Fin (n + 1)) L)} {d : ℕ} (h : Ik I d = Ik I' d) :
    Module.finrank L (piece I d) = Module.finrank L (piece I' d) := by
  unfold Ik at h; exact (Submodule.quotEquivOfEq _ _ h).finrank_eq

theorem finrank_piece_anti {I I' : Ideal (MvPolynomial (Fin (n + 1)) L)} (h : I ≤ I') (d : ℕ) :
    Module.finrank L (piece I' d) ≤ Module.finrank L (piece I d) := by
  have h1 := finrank_piece_add I d
  have h2 := finrank_piece_add I' d
  have h3 : Module.finrank L ↥(Ik I d) ≤ Module.finrank L ↥(Ik I' d) := Submodule.finrank_mono (Ik_mono h d)
  omega

theorem finrank_piece_eq_zero_of_forall {I : Ideal (MvPolynomial (Fin (n + 1)) L)} {d : ℕ}
    (h : ∀ f : MvPolynomial (Fin (n + 1)) L, f.IsHomogeneous d → f ∈ I) : Module.finrank L (piece I d) = 0 := by
  have htop : Ik I d = ⊤ := eq_top_iff.mpr fun x _ => (mem_Ik x).mpr (h x x.2)
  have h1 := finrank_piece_add I d
  rw [htop, finrank_top] at h1
  omega

theorem mem_of_finrank_piece_eq_zero {I : Ideal (MvPolynomial (Fin (n + 1)) L)} {d : ℕ}
    (h : Module.finrank L (piece I d) = 0) (f : MvPolynomial (Fin (n + 1)) L) (hf : f.IsHomogeneous d) :
    f ∈ I := by
  have h1 := finrank_piece_add I d
  rw [h, zero_add] at h1
  have htop : Ik I d = ⊤ := Submodule.eq_top_of_finrank_eq h1
  have : (⟨f, hf⟩ : ↥(homogeneousSubmodule (Fin (n + 1)) L d)) ∈ Ik I d := by rw [htop]; trivial
  exact (mem_Ik _).mp this

theorem decompose_eq (q : MvPolynomial (Fin (n + 1)) L) (d : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) L) q d : MvPolynomial (Fin (n + 1)) L) =
      homogeneousComponent d q :=
  MvPolynomial.decomposition.decompose'_apply q d

theorem homogeneousComponent_mul_add {G : MvPolynomial (Fin (n + 1)) L} {m : ℕ} (hG : G.IsHomogeneous m)
    (a : MvPolynomial (Fin (n + 1)) L) (d : ℕ) :
    homogeneousComponent (m + d) (a * G) = homogeneousComponent d a * G := by
  have := DirectSum.coe_decompose_mul_of_right_mem_of_le (𝒜 := homogeneousSubmodule (Fin (n + 1)) L)
    (a := a) (show G ∈ homogeneousSubmodule (Fin (n + 1)) L m from hG) (Nat.le_add_right m d)
  rw [decompose_eq, decompose_eq, Nat.add_sub_cancel_left] at this
  exact this

theorem span_homogeneous (s : Set (MvPolynomial (Fin (n + 1)) L))
    (hs : ∀ p ∈ s, ∃ i : ℕ, p.IsHomogeneous i) :
    ∀ p ∈ Ideal.span s, ∀ d : ℕ, homogeneousComponent d p ∈ Ideal.span s := by
  intro p hp d
  have H := Ideal.homogeneous_span (homogeneousSubmodule (Fin (n + 1)) L) s (fun x hx => hs x hx)
  have := H d hp
  rwa [decompose_eq] at this

theorem finrank_piece_succ_eq_add (I : Ideal (MvPolynomial (Fin (n + 1)) L))
    (hI : ∀ p ∈ I, ∀ i : ℕ, homogeneousComponent i p ∈ I)
    (ℓ : MvPolynomial (Fin (n + 1)) L) (hℓ : ℓ.IsHomogeneous 1) (k : ℕ)
    (hcol : ∀ f : MvPolynomial (Fin (n + 1)) L, f.IsHomogeneous k → ℓ * f ∈ I → f ∈ I) :
    Module.finrank L (piece I (k + 1)) =
      Module.finrank L (piece I k) + Module.finrank L (piece (I ⊔ Ideal.span {ℓ}) (k + 1)) := by
  by_cases hℓ0 : ℓ = 0
  · subst hℓ0
    have h0 : Module.finrank L (piece I k) = 0 :=
      finrank_piece_eq_zero_of_forall fun f hf => hcol f hf (by rw [zero_mul]; exact I.zero_mem)
    have hbot : Ideal.span ({0} : Set (MvPolynomial (Fin (n + 1)) L)) = ⊥ := Ideal.span_singleton_eq_bot.mpr rfl
    rw [h0, zero_add, hbot, sup_bot_eq]

  let μ : ↥(homogeneousSubmodule (Fin (n + 1)) L k) →ₗ[L] ↥(homogeneousSubmodule (Fin (n + 1)) L (k + 1)) :=
    LinearMap.codRestrict (homogeneousSubmodule (Fin (n + 1)) L (k + 1))
      ((LinearMap.mulLeft L ℓ) ∘ₗ (homogeneousSubmodule (Fin (n + 1)) L k).subtype)
      (fun f => by
        show (ℓ * (f : MvPolynomial (Fin (n + 1)) L)).IsHomogeneous (k + 1)
        have := hℓ.mul f.2; rwa [Nat.add_comm 1 k] at this)
  have hμ : ∀ f : ↥(homogeneousSubmodule (Fin (n + 1)) L k),
      (μ f : MvPolynomial (Fin (n + 1)) L) = ℓ * f := fun f => rfl
  have hμinj : Function.Injective μ := by
    intro f g hfg
    have := congrArg Subtype.val hfg
    rw [hμ, hμ] at this
    exact Subtype.ext (mul_left_cancel₀ hℓ0 this)

  have hA1 : Ik (I ⊔ Ideal.span {ℓ}) (k + 1) = Ik I (k + 1) ⊔ LinearMap.range μ := by
    apply le_antisymm
    · intro x hx
      rw [mem_Ik] at hx
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      have hx1 : (x : MvPolynomial (Fin (n + 1)) L) = homogeneousComponent (k + 1) x := by
        rw [homogeneousComponent_of_mem x.2, if_pos rfl]
      have hgl : homogeneousComponent (k + 1) (g * ℓ) = homogeneousComponent k g * ℓ := by
        rw [Nat.add_comm k 1]; exact homogeneousComponent_mul_add hℓ g k
      have hyk : homogeneousComponent (k + 1) y ∈ homogeneousSubmodule (Fin (n + 1)) L (k + 1) :=
        homogeneousComponent_isHomogeneous _ _
      have hgk : homogeneousComponent k g ∈ homogeneousSubmodule (Fin (n + 1)) L k :=
        homogeneousComponent_isHomogeneous _ _
      have hxeq : (x : MvPolynomial (Fin (n + 1)) L) =
          homogeneousComponent (k + 1) y + ℓ * homogeneousComponent k g := by
        calc (x : MvPolynomial (Fin (n + 1)) L) = homogeneousComponent (k + 1) (y + g * ℓ) := by
              rw [hyz]; exact hx1
          _ = homogeneousComponent (k + 1) y + ℓ * homogeneousComponent k g := by
              rw [map_add, hgl, mul_comm ℓ]
      have hxeq' : x = ⟨homogeneousComponent (k + 1) y, hyk⟩ + μ ⟨homogeneousComponent k g, hgk⟩ := by
        apply Subtype.ext
        rw [Submodule.coe_add, hμ]
        exact hxeq
      rw [hxeq']
      exact Submodule.add_mem_sup ((mem_Ik _).mpr (hI y hy (k + 1))) (LinearMap.mem_range_self μ _)
    · apply sup_le (Ik_mono (I := I) (I' := I ⊔ Ideal.span {ℓ}) le_sup_left (k + 1))
      rintro _ ⟨f, rfl⟩
      rw [mem_Ik, hμ]
      exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ℓ))

  have hA2 : Ik I (k + 1) ⊓ LinearMap.range μ = (Ik I k).map μ := by
    apply le_antisymm
    · rintro y ⟨hyI, ⟨f, rfl⟩⟩
      have hyI' : ℓ * (f : MvPolynomial (Fin (n + 1)) L) ∈ I := by rw [← hμ]; exact (mem_Ik _).mp hyI
      have hf : f ∈ Ik I k := (mem_Ik f).mpr (hcol f f.2 hyI')
      exact Submodule.mem_map_of_mem hf
    · rintro _ ⟨f, hf, rfl⟩
      refine ⟨(mem_Ik _).mpr ?_, LinearMap.mem_range_self μ f⟩
      rw [hμ]; exact I.mul_mem_left ℓ ((mem_Ik f).mp hf)
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq (Ik I (k + 1)) (LinearMap.range μ)
  rw [← hA1, hA2, LinearMap.finrank_range_of_inj hμinj,
    (Submodule.equivMapOfInjective μ hμinj (Ik I k)).symm.finrank_eq] at e1
  have e2 := finrank_piece_add I k
  have e3 := finrank_piece_add I (k + 1)
  have e4 := finrank_piece_add (I ⊔ Ideal.span {ℓ}) (k + 1)
  omega

end Pieces

section Regen

variable {L : Type} [Field L]

theorem exists_eq_sum_X_mul (k : ℕ) (g : MvPolynomial (Fin (n + 1)) L) (hg : g.IsHomogeneous (k + 1)) :
    ∃ q : Fin (n + 1) → MvPolynomial (Fin (n + 1)) L, (∀ i, (q i).IsHomogeneous k) ∧ g = ∑ i, X i * q i := by
  classical
  have hg' : g ∈ (Submodule.span L ((fun μ : Fin (n + 1) →₀ ℕ => monomial μ (1 : L)) ''
      {μ : Fin (n + 1) →₀ ℕ | μ.degree = k + 1}) : Submodule L (MvPolynomial (Fin (n + 1)) L)) := by
    have : g ∈ homogeneousSubmodule (Fin (n + 1)) L (k + 1) := hg
    rw [homogeneousSubmodule_eq_finsupp_supported, AddMonoidAlgebra.supported_eq_span_single] at this
    exact this
  clear hg
  induction hg' using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨μ, hμ, rfl⟩ := hx
      have hμ' : μ.degree = k + 1 := hμ
      have hne : μ ≠ 0 := by rintro rfl; simp at hμ'
      obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
        by_contra h; push Not at h; exact hne (Finsupp.ext h)
      have hle : Finsupp.single i 1 ≤ μ := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
      have hdeg : (μ - Finsupp.single i 1).degree = k := by
        have h1 : μ - Finsupp.single i 1 + Finsupp.single i 1 = μ := tsub_add_cancel_of_le hle
        have h2 := congrArg Finsupp.degree h1
        rw [map_add, Finsupp.degree_single, hμ'] at h2
        omega
      refine ⟨Pi.single i (monomial (μ - Finsupp.single i 1) 1), fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj; rw [Pi.single_eq_same]; exact isHomogeneous_monomial _ hdeg
        · rw [Pi.single_eq_of_ne hj]; exact isHomogeneous_zero _ _ _
      · rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
          (fun h => (h (Finset.mem_univ i)).elim), Pi.single_eq_same]
        show (monomial μ (1 : L)) = monomial (Finsupp.single i 1) 1 * monomial (μ - Finsupp.single i 1) 1
        rw [monomial_mul, one_mul, add_tsub_cancel_of_le hle]
  | zero => exact ⟨0, fun _ => isHomogeneous_zero _ _ _, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨q₁, hq₁, rfl⟩ := hx
      obtain ⟨q₂, hq₂, rfl⟩ := hy
      exact ⟨q₁ + q₂, fun i => (hq₁ i).add (hq₂ i), by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, mul_add]⟩
  | smul c x _ hx =>
      obtain ⟨q, hq, rfl⟩ := hx
      refine ⟨fun i => C c * q i, fun i => (hq i).C_mul c, ?_⟩
      rw [smul_eq_C_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_left_comm]

theorem finrank_piece_succ_eq_zero {I : Ideal (MvPolynomial (Fin (n + 1)) L)} {k : ℕ}
    (h : Module.finrank L (piece I k) = 0) : Module.finrank L (piece I (k + 1)) = 0 := by
  apply finrank_piece_eq_zero_of_forall
  intro g hg
  obtain ⟨q, hq, rfl⟩ := exists_eq_sum_X_mul k g hg
  exact I.sum_mem fun i _ => I.mul_mem_left _ (mem_of_finrank_piece_eq_zero h (q i) (hq i))

variable {m : ℕ} (J : Ideal (MvPolynomial (Fin (n + 1)) L))
  (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) L), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
  (ℓ : MvPolynomial (Fin (n + 1)) L) (hℓ : ℓ.IsHomogeneous 1)

include hJ in
theorem homogeneous_of_gen : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J := by
  obtain ⟨s, hs, rfl⟩ := hJ
  exact span_homogeneous s fun p hp => ⟨m, hs p hp⟩

include hJ hℓ in

theorem homogeneous_sup : ∀ p ∈ J ⊔ Ideal.span {ℓ}, ∀ i : ℕ, homogeneousComponent i p ∈ J ⊔ Ideal.span {ℓ} := by
  obtain ⟨s, hs, rfl⟩ := hJ
  have : Ideal.span s ⊔ Ideal.span {ℓ} = Ideal.span (s ∪ {ℓ}) := (Submodule.span_union s {ℓ}).symm
  rw [this]
  refine span_homogeneous (s ∪ {ℓ}) ?_
  rintro p (hp | hp)
  · exact ⟨m, hs p hp⟩
  · exact ⟨1, by rw [Set.mem_singleton_iff.mp hp]; exact hℓ⟩

noncomputable def regen (m : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) L)) (ℓ : MvPolynomial (Fin (n + 1)) L) :
    Ideal (MvPolynomial (Fin (n + 1)) L) :=
  Ideal.span {p | p ∈ J ⊔ Ideal.span {ℓ} ∧ p.IsHomogeneous m}

theorem regen_le : regen m J ℓ ≤ J ⊔ Ideal.span {ℓ} := Ideal.span_le.mpr fun _ hp => hp.1

theorem regen_generated : ∃ s : Set (MvPolynomial (Fin (n + 1)) L), (∀ p ∈ s, p.IsHomogeneous m) ∧
    regen m J ℓ = Ideal.span s := ⟨_, fun _ hp => hp.2, rfl⟩

include hJ in
theorem le_regen : J ≤ regen m J ℓ := by
  obtain ⟨s, hs, rfl⟩ := hJ
  exact Ideal.span_le.mpr fun p hp => Ideal.subset_span ⟨Ideal.mem_sup_left (Ideal.subset_span hp), hs p hp⟩

include hJ hℓ in

theorem mem_regen_of_mem (hm : 1 ≤ m) : ∀ (j : ℕ) (x : MvPolynomial (Fin (n + 1)) L),
    x.IsHomogeneous (m + j) → x ∈ J ⊔ Ideal.span {ℓ} → x ∈ regen m J ℓ
  | 0, x, hx, hxI => Ideal.subset_span ⟨hxI, hx⟩
  | j + 1, x, hx, hxI => by
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hxI
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      have hx1 : x = homogeneousComponent (m + j + 1) x := by
        rw [homogeneousComponent_of_mem (show x ∈ homogeneousSubmodule (Fin (n + 1)) L (m + j + 1) from hx),
          if_pos rfl]
      have hgl : homogeneousComponent (m + j + 1) (g * ℓ) = homogeneousComponent (m + j) g * ℓ := by
        rw [Nat.add_comm (m + j) 1]; exact homogeneousComponent_mul_add hℓ g (m + j)
      rw [hx1, ← hyz, map_add, hgl]
      refine Ideal.add_mem _ (le_regen J hJ ℓ (homogeneous_of_gen J hJ y hy _)) ?_

      have hmj : m + j = (m + j - 1) + 1 := by omega
      obtain ⟨q, hq, hgq⟩ := exists_eq_sum_X_mul (m + j - 1) (homogeneousComponent (m + j) g)
        (by rw [← hmj]; exact homogeneousComponent_isHomogeneous _ _)
      rw [hgq, Finset.sum_mul]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [mul_assoc]
      refine Ideal.mul_mem_left _ _ (mem_regen_of_mem hm j (q i * ℓ) ?_ ?_)
      · have := (hq i).mul hℓ; rwa [← hmj] at this
      · exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self ℓ))

include hJ hℓ in
theorem Ik_regen_eq (hm : 1 ≤ m) {k : ℕ} (hk : m ≤ k) : Ik (regen m J ℓ) k = Ik (J ⊔ Ideal.span {ℓ}) k := by
  apply le_antisymm (Ik_mono (regen_le J ℓ) k)
  intro x hx
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact (mem_Ik x).mpr (mem_regen_of_mem J hJ ℓ hℓ hm j x x.2 ((mem_Ik x).mp hx))

end Regen

section BaseChange

variable (K L : Type) [Field K] [Field L] [Algebra K L]

theorem finrank_piece_map (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J) (d : ℕ) :
    Module.finrank L (piece (J.map (MvPolynomial.map (algebraMap K L))) d) = Module.finrank K (piece J d) := by
  obtain ⟨-, h⟩ := AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map n K L J hJ
  obtain ⟨e, -⟩ := h d
  rw [← e.finrank_eq, Module.finrank_baseChange]

theorem map_generated {m : ℕ} (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s) :
    ∃ s : Set (MvPolynomial (Fin (n + 1)) L), (∀ p ∈ s, p.IsHomogeneous m) ∧
      J.map (MvPolynomial.map (algebraMap K L)) = Ideal.span s := by
  obtain ⟨s, hs, rfl⟩ := hJ
  refine ⟨MvPolynomial.map (algebraMap K L) '' s, ?_, Ideal.map_span _ _⟩
  rintro _ ⟨p, hp, rfl⟩
  exact (hs p hp).map _

end BaseChange

section Core

variable {L : Type} [Field L]

theorem isHomogeneous_linearForm (a : Fin (n + 1) → L) :
    (∑ i, C (a i) * X i : MvPolynomial (Fin (n + 1)) L).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X (a i) i

variable [Infinite L]

theorem exists_eval_ne_zero {G₁ G₂ : MvPolynomial (Fin (n + 1)) L} (h₁ : G₁ ≠ 0) (h₂ : G₂ ≠ 0) :
    ∃ a : Fin (n + 1) → L, MvPolynomial.eval a G₁ ≠ 0 ∧ MvPolynomial.eval a G₂ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply mul_ne_zero h₁ h₂
  apply MvPolynomial.funext
  intro a
  rw [map_mul, map_zero]
  by_cases h1 : MvPolynomial.eval a G₁ = 0
  · rw [h1, zero_mul]
  · rw [hcon a h1, mul_zero]

theorem core {m : ℕ} (hm : 1 ≤ m) : ∀ (N : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) L)),
    (∃ s : Set (MvPolynomial (Fin (n + 1)) L), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s) →
    Module.finrank L (piece J m) ≤ N →
    Module.finrank L (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank L (piece J m)) →
    Module.finrank L (piece J (m + 2)) = Nat.macaulayPow (m + 1) (Module.finrank L (piece J (m + 1))) := by
  intro N
  induction N with
  | zero =>
      intro J _ hN hmax
      have h0 : Module.finrank L (piece J m) = 0 := Nat.le_zero.mp hN
      rw [h0, Mac.macaulayPow_zero_right] at hmax
      rw [hmax, finrank_piece_succ_eq_zero hmax, Mac.macaulayPow_zero_right]
  | succ N ih =>
      intro J hJ hN hmax
      by_cases hs : Module.finrank L (piece J m) ≤ N
      · exact ih J hJ hs hmax
      have hs0 : 0 < Module.finrank L (piece J m) := by omega
      have hJh := homogeneous_of_gen J hJ

      obtain ⟨G₁, hG₁, H₁⟩ :=
        MvPolynomial.exists_forall_eval_ne_zero_macaulayPow_finrank_piece_sup_add_le n m hm L J hJh
      obtain ⟨G₂, hG₂, H₂⟩ :=
        MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow n m L J hJ hmax
      obtain ⟨a, ha₁, ha₂⟩ := exists_eval_ne_zero hG₁ hG₂
      have hrt := H₁ a ha₁
      have hcol := H₂ a ha₂
      set ℓ : MvPolynomial (Fin (n + 1)) L := ∑ i, C (a i) * X i with hℓdef
      have hℓ : ℓ.IsHomogeneous 1 := isHomogeneous_linearForm a
      have hJ'h := homogeneous_sup J hJ ℓ hℓ

      have hA := finrank_piece_succ_eq_add J hJh ℓ hℓ m (fun f hf h => hcol m le_rfl f hf h)
      have hB := finrank_piece_succ_eq_add J hJh ℓ hℓ (m + 1) (fun f hf h => hcol (m + 1) (Nat.le_succ m) f hf h)
      have hmac := MvPolynomial.finrank_piece_succ_le_macaulayPow n m hm L (J ⊔ Ideal.span {ℓ}) hJ'h

      have hreg : ∀ k, m ≤ k →
          Module.finrank L (piece (regen m J ℓ) k) = Module.finrank L (piece (J ⊔ Ideal.span {ℓ}) k) :=
        fun k hk => finrank_piece_eq_of_Ik_eq (Ik_regen_eq J hJ ℓ hℓ hm hk)
      set s0 := Module.finrank L (piece J m) with hs0def
      set s1 := Module.finrank L (piece J (m + 1)) with hs1def
      set s2 := Module.finrank L (piece J (m + 2)) with hs2def
      set t0 := Module.finrank L (piece (J ⊔ Ideal.span {ℓ}) m) with ht0def
      set t1 := Module.finrank L (piece (J ⊔ Ideal.span {ℓ}) (m + 1)) with ht1def
      set t2 := Module.finrank L (piece (J ⊔ Ideal.span {ℓ}) (m + 2)) with ht2def

      have ht1 : t1 = Nat.macaulayPow m t0 := by omega
      have hlt : t0 < s0 := Mac.lt_of_macaulayPow_add_le hrt hs0

      have ihr := ih (regen m J ℓ) (regen_generated J ℓ) (by rw [hreg m le_rfl]; omega)
        (by rw [hreg m le_rfl, hreg (m + 1) (Nat.le_succ m)]; exact ht1)
      rw [hreg (m + 1) (Nat.le_succ m), hreg (m + 2) (by omega), ← ht1def, ← ht2def] at ihr

      have key := Mac.macaulayPow_macaulayPow m s0
      have ht1' : t1 = Nat.macaulayPow m s0 - s0 := by omega
      rw [hB, ihr, ht1', hmax, key]

end Core

theorem main (n m : ℕ) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    Module.finrank K (piece J (m + 2)) = Nat.macaulayPow (m + 1) (Module.finrank K (piece J (m + 1))) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  ·
    change Module.finrank K (piece J 1) = Nat.macaulayPow 0 (Module.finrank K (piece J 0)) at hmax
    change Module.finrank K (piece J 2) = Nat.macaulayPow 1 (Module.finrank K (piece J 1))
    rw [Mac.macaulayPow_zero] at hmax
    have h2 : Module.finrank K (piece J 2) = 0 := finrank_piece_succ_eq_zero hmax
    rw [hmax, h2, Mac.macaulayPow_zero_right]
  ·
    have hJh := homogeneous_of_gen J hJ
    have e := finrank_piece_map K (AlgebraicClosure K) J hJh
    have h := core hm (Module.finrank (AlgebraicClosure K)
        (piece (J.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)))) m))
      (J.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)))) (map_generated K (AlgebraicClosure K) J hJ)
      le_rfl (by rw [e, e]; exact hmax)
    rw [e, e] at h
    exact h

end GotzStep
p2m_reactivate "P2MW.S_MvPolynomial_finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow.GotzStep"

open MvPolynomial AlgebraicGeometry.HilbertFunctor in
theorem solution
    (n m : ℕ) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank K (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank K (piece J m))) :
    Module.finrank K (piece J (m + 2)) = Nat.macaulayPow (m + 1) (Module.finrank K (piece J (m + 1))) :=
  GotzStep.main n m K J hJ hmax

end S_MvPolynomial_finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow
end P2MW
export P2MW.S_MvPolynomial_finrank_piece_add_two_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow (solution)
