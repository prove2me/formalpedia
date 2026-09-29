-- Prove2me | solution 1 for Matrix.exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/16d8f011-9b90-508c-8853-efad7bd7c1f9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow

set_option autoImplicit false

namespace ASM21
namespace M2L

variable {ℓ : ℕ}

def row0 (x : Fin 2 → ZMod ℓ) : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := Matrix.of ![x, 0]

@[scoped simp] theorem row0_apply_zero (x : Fin 2 → ZMod ℓ) : row0 x 0 = x := rfl
@[scoped simp] theorem row0_apply_one (x : Fin 2 → ZMod ℓ) : row0 x 1 = 0 := rfl

theorem row0_add (x y : Fin 2 → ZMod ℓ) : row0 (x + y) = row0 x + row0 y := by
  ext i j; fin_cases i <;> simp [row0]
theorem row0_zero : row0 (0 : Fin 2 → ZMod ℓ) = 0 := by
  ext i j; fin_cases i <;> simp [row0]
theorem row0_smul (c : ZMod ℓ) (x : Fin 2 → ZMod ℓ) : row0 (c • x) = (algebraMap (ZMod ℓ) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) c) * row0 x := by
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  ext i j; fin_cases i <;> simp [row0]
theorem row0_eq_zero_iff (x : Fin 2 → ZMod ℓ) : row0 x = 0 ↔ x = 0 := by
  constructor
  · intro h; funext j; have := congrFun (congrFun h 0) j; simpa [row0] using this
  · rintro rfl; exact row0_zero

theorem single_mul_eq_row0 (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (i : Fin 2) :
    Matrix.of (fun a b => if a = 0 ∧ b = i then (1 : ZMod ℓ) else 0) * X = row0 (X i) := by
  ext a b; fin_cases a <;> fin_cases i <;> simp [row0, Matrix.mul_apply, Fin.sum_univ_two]

theorem low_mul_row0 (y : Fin 2 → ZMod ℓ) :
    Matrix.of (fun a b => if a = 1 ∧ b = 0 then (1 : ZMod ℓ) else 0) * row0 y = Matrix.of ![0, y] := by
  ext a b; fin_cases a <;> simp [row0, Matrix.mul_apply, Fin.sum_univ_two]
theorem eq_row0_add (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) : X = row0 (X 0) + Matrix.of ![0, X 1] := by
  ext a b; fin_cases a <;> simp [row0]

def rowSp (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ) where
  carrier := {x | row0 x ∈ I}
  zero_mem' := by show row0 0 ∈ I; rw [row0_zero]; exact I.zero_mem
  add_mem' := by intro x y hx hy; show row0 (x + y) ∈ I; rw [row0_add]; exact I.add_mem hx hy
  smul_mem' := by intro c x hx; show row0 (c • x) ∈ I; rw [row0_smul]; exact I.smul_mem _ hx

theorem mem_rowSp (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) (x : Fin 2 → ZMod ℓ) : x ∈ rowSp I ↔ row0 x ∈ I := Iff.rfl

def idealOf (W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)) : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) where
  carrier := {X | ∀ i, X i ∈ W}
  zero_mem' := by
    show ∀ i, (0 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) i ∈ W
    intro i; exact W.zero_mem
  add_mem' := by
    intro X Y hX hY
    show ∀ i, (X + Y) i ∈ W
    intro i; exact W.add_mem (hX i) (hY i)
  smul_mem' := by
    intro Y X hX i
    have : (Y • X) i = ∑ k, Y i k • X k := by
      funext j; simp [Matrix.mul_apply, Finset.sum_apply]
    rw [this]
    exact W.sum_mem (fun k _ => W.smul_mem _ (hX k))

theorem mem_idealOf (W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)) (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) : X ∈ idealOf W ↔ ∀ i, X i ∈ W := Iff.rfl

theorem rowSp_idealOf (W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)) : rowSp (idealOf W) = W := by
  ext x
  rw [mem_rowSp, mem_idealOf]
  constructor
  · intro h; simpa using h 0
  · intro h i; fin_cases i <;> simp [h]

theorem idealOf_rowSp (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) : idealOf (rowSp I) = I := by
  ext X
  rw [mem_idealOf]
  constructor
  · intro h
    have h0 : row0 (X 0) ∈ I := (mem_rowSp I _).1 (h 0)
    have h1 : row0 (X 1) ∈ I := (mem_rowSp I _).1 (h 1)
    rw [eq_row0_add X, ← low_mul_row0]
    exact I.add_mem h0 (I.smul_mem _ h1)
  · intro hX i
    rw [mem_rowSp, ← single_mul_eq_row0]
    exact I.smul_mem _ hX

def idealEquiv : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) ≃ Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ) where
  toFun := rowSp
  invFun := idealOf
  left_inv := idealOf_rowSp
  right_inv := rowSp_idealOf

theorem rowSp_bot : rowSp (⊥ : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) = ⊥ := by
  ext x; rw [mem_rowSp, Submodule.mem_bot, Submodule.mem_bot, row0_eq_zero_iff]
theorem rowSp_top : rowSp (⊤ : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ))) = ⊤ := by
  ext x; simp [mem_rowSp]
theorem idealOf_inf (W W' : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)) : idealOf (W ⊓ W') = idealOf W ⊓ idealOf W' := by
  ext X; simp only [mem_idealOf, Submodule.mem_inf]; exact forall_and
theorem idealOf_bot : idealOf (⊥ : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ)) = ⊥ := by
  rw [← rowSp_bot, idealOf_rowSp]

def properEquiv :
    {I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) // I ≠ ⊥ ∧ I ≠ ⊤} ≃
    {W : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ) // W ≠ ⊥ ∧ W ≠ ⊤} where
  toFun I := ⟨rowSp I.1, fun h => I.2.1 (by rw [← idealOf_rowSp I.1, h, ← rowSp_bot, idealOf_rowSp]),
    fun h => I.2.2 (by rw [← idealOf_rowSp I.1, h, ← rowSp_top, idealOf_rowSp])⟩
  invFun W := ⟨idealOf W.1, fun h => W.2.1 (by rw [← rowSp_idealOf W.1, h, rowSp_bot]),
    fun h => W.2.2 (by rw [← rowSp_idealOf W.1, h, rowSp_top])⟩
  left_inv I := Subtype.ext (idealOf_rowSp I.1)
  right_inv W := Subtype.ext (rowSp_idealOf W.1)

end ASM21.M2L
p2m_reactivate "P2MW.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow.ASM21 P2MW.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow.ASM21.M2L"
p2m_reactivate "P2MW.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow.ASM21"

namespace ASM21
namespace M2LL
open ASM21.M2L

section gen
variable {n : ℕ}

def idealOfAddEquiv (W : Submodule (ZMod n) (Fin 2 → ZMod n)) : ↥(idealOf W) ≃+ (↥W × ↥W) where
  toFun X := (⟨X.1 0, X.2 0⟩, ⟨X.1 1, X.2 1⟩)
  invFun p := ⟨Matrix.of ![(p.1 : Fin 2 → ZMod n), (p.2 : Fin 2 → ZMod n)], by
    intro i; fin_cases i
    · exact p.1.2
    · exact p.2.2⟩
  left_inv X := by
    apply Subtype.ext; ext i j; fin_cases i <;> rfl
  right_inv p := by
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p; rfl
  map_add' X Y := by rfl

theorem natCast_smul_apply (c : ℕ) (X : Matrix (Fin 2) (Fin 2) (ZMod n)) (i : Fin 2) :
    ((c : Matrix (Fin 2) (Fin 2) (ZMod n)) • X) i = (c : ZMod n) • X i := by
  have : (c : Matrix (Fin 2) (Fin 2) (ZMod n)) = (c : ZMod n) • (1 : Matrix (Fin 2) (Fin 2) (ZMod n)) := by
    rw [← map_natCast (algebraMap (ZMod n) (Matrix (Fin 2) (Fin 2) (ZMod n))) c, Algebra.algebraMap_eq_smul_one]
  rw [this, smul_eq_mul, smul_one_mul]
  rfl

noncomputable def spanSingletonEquiv [NeZero n] (w : Fin 2 → ZMod n) (hw : addOrderOf w = n) :
    ZMod n ≃+ ↥(Submodule.span (ZMod n) ({w} : Set (Fin 2 → ZMod n))) := by
  classical
  let F : ZMod n →+ ↥(Submodule.span (ZMod n) ({w} : Set (Fin 2 → ZMod n))) :=
    { toFun := fun a => ⟨a • w, Submodule.mem_span_singleton.2 ⟨a, rfl⟩⟩
      map_zero' := by apply Subtype.ext; exact zero_smul _ _
      map_add' := fun a b => by apply Subtype.ext; exact add_smul a b w }
  have hF : ∀ a, (F a : Fin 2 → ZMod n) = a • w := fun a => rfl
  refine AddEquiv.ofBijective F ⟨?_, ?_⟩
  · intro a b hab
    have h : (a - b) • w = 0 := by
      have := congrArg Subtype.val hab
      rw [hF, hF] at this
      rw [sub_smul, this, sub_self]
    have hval : (a - b).val • w = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_zmod_val]; exact h
    have hdvd : addOrderOf w ∣ (a - b).val := addOrderOf_dvd_of_nsmul_eq_zero hval
    rw [hw] at hdvd
    have : (a - b).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
    rw [ZMod.val_eq_zero, sub_eq_zero] at this
    exact this
  · rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    exact ⟨a, rfl⟩

end gen
p2m_reactivate "P2MW.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow.ASM21 P2MW.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow.ASM21.M2L"

section ell
variable (ℓ : ℕ) [Fact ℓ.Prime] (e : ℕ)

theorem exists_eq_mul_of_pow_mul_eq_zero (a : ZMod (ℓ ^ (e + 1))) (h : ((ℓ ^ e : ℕ) : ZMod (ℓ ^ (e + 1))) * a = 0) :
    ∃ a' : ZMod (ℓ ^ (e + 1)), a = (ℓ : ZMod (ℓ ^ (e + 1))) * a' := by
  haveI : NeZero (ℓ ^ (e + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have h1 : ((ℓ ^ e * a.val : ℕ) : ZMod (ℓ ^ (e + 1))) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact h
  have h1' : ℓ ^ e * ℓ ∣ ℓ ^ e * a.val := by
    rw [← pow_succ]; exact (CharP.cast_eq_zero_iff (ZMod (ℓ ^ (e + 1))) (ℓ ^ (e + 1)) _).1 h1
  have h2 : ℓ ∣ a.val := Nat.dvd_of_mul_dvd_mul_left (pow_pos (Fact.out : ℓ.Prime).pos e) h1'
  obtain ⟨t, ht⟩ := h2
  refine ⟨(t : ZMod (ℓ ^ (e + 1))), ?_⟩
  rw [← ZMod.natCast_zmod_val a, ht, Nat.cast_mul]

theorem exists_eq_smul_of_pow_smul_eq_zero (r : Fin 2 → ZMod (ℓ ^ (e + 1))) (h : (ℓ ^ e) • r = 0) :
    ∃ r' : Fin 2 → ZMod (ℓ ^ (e + 1)), r = (ℓ : ZMod (ℓ ^ (e + 1))) • r' := by
  have hc : ∀ i, ((ℓ ^ e : ℕ) : ZMod (ℓ ^ (e + 1))) * r i = 0 := by
    intro i
    have := congrFun h i
    rw [Pi.smul_apply, Pi.zero_apply, ← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ (e + 1))), smul_eq_mul] at this
    exact this
  choose r' hr' using fun i => exists_eq_mul_of_pow_mul_eq_zero ℓ e (r i) (hc i)
  exact ⟨r', funext fun i => by rw [Pi.smul_apply, smul_eq_mul]; exact hr' i⟩

theorem addOrderOf_eq_pow_succ (w : Fin 2 → ZMod (ℓ ^ (e + 1))) (hw : (ℓ ^ e) • w ≠ 0) :
    addOrderOf w = ℓ ^ (e + 1) := by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow (Fact.out : ℓ.Prime)
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero]; exact hw
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero, ← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ (e + 1))), ZMod.natCast_self, zero_smul]

end ell
p2m_reactivate "P2MW.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow.ASM21 P2MW.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow.ASM21.M2L"
end ASM21.M2LL
p2m_reactivate "P2MW.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow.ASM21 P2MW.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow.ASM21.M2L"
p2m_reactivate "P2MW.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow.ASM21 P2MW.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow.ASM21.M2L"

namespace ASM21
namespace M2LL

theorem addOrderOf_eq_prime_pow_succ {G : Type*} [AddMonoid G] (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) (w : G)
    (h1 : (ℓ ^ k) • w ≠ 0) (h2 : (ℓ ^ (k + 1)) • w = 0) : addOrderOf w = ℓ ^ (k + 1) := by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow (Fact.out : ℓ.Prime)
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero]; exact h1
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero]; exact h2

end ASM21.M2LL
p2m_reactivate "P2MW.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow.ASM21 P2MW.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow.ASM21.M2L"
p2m_reactivate "P2MW.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow.ASM21 P2MW.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow.ASM21.M2L"

theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime] (e : ℕ)
    (I : Submodule (Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e + 1)))) (Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e + 1)))))
    (hI : Nonempty (↥I ≃+ (ZMod (ℓ ^ e) × ZMod (ℓ ^ e)))) :
    ∃ J : Submodule (Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e + 1)))) (Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e + 1)))),
      I ≤ J ∧ Nonempty (↥J ≃+ (ZMod (ℓ ^ (e + 1)) × ZMod (ℓ ^ (e + 1)))) ∧
      ∀ x ∈ J, (ℓ : Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e + 1)))) • x ∈ I := by
  classical
  have hℓ := (Fact.out : ℓ.Prime)
  haveI : NeZero (ℓ ^ (e + 1)) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  obtain ⟨f⟩ := hI
  have hIW : ASM21.M2L.idealOf (ASM21.M2L.rowSp I) = I := ASM21.M2L.idealOf_rowSp I
  have hrows : ∀ (X : Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e + 1)))), X ∈ I → ∀ i, X i ∈ ASM21.M2L.rowSp I := by
    intro X hX; rw [← hIW] at hX; exact hX

  have key : ∃ wt : Fin 2 → ZMod (ℓ ^ (e + 1)), addOrderOf wt = ℓ ^ (e + 1) ∧
      (ℓ : ZMod (ℓ ^ (e + 1))) • wt ∈ ASM21.M2L.rowSp I ∧
      ∀ x ∈ ASM21.M2L.rowSp I, x ∈ Submodule.span (ZMod (ℓ ^ (e + 1))) ({wt} : Set (Fin 2 → ZMod (ℓ ^ (e + 1)))) := by
    rcases Nat.eq_zero_or_pos e with he | he
    ·
      subst he
      have hsub : ∀ y : ↥I, y = 0 := by
        have hc : Nat.card ↥I = 1 := by
          rw [Nat.card_congr f.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card]; simp
        have := (Nat.card_eq_one_iff_unique.1 hc).1
        intro y; exact Subsingleton.elim y 0
      have hW0 : ∀ x ∈ ASM21.M2L.rowSp I, x = 0 := by
        intro x hx
        rw [ASM21.M2L.mem_rowSp] at hx
        have := congrArg Subtype.val (hsub ⟨_, hx⟩)
        exact (ASM21.M2L.row0_eq_zero_iff x).1 this
      haveI : Fact (1 < ℓ ^ (0 + 1)) := ⟨by rw [zero_add, pow_one]; exact hℓ.one_lt⟩
      refine ⟨Pi.single 0 1, ?_, ?_, ?_⟩
      · apply ASM21.M2LL.addOrderOf_eq_prime_pow_succ ℓ 0
        · rw [pow_zero, one_smul]; intro h
          have := congrFun h 0
          simp at this
        · rw [← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ (0 + 1))), ZMod.natCast_self, zero_smul]
      · have : (ℓ : ZMod (ℓ ^ (0 + 1))) = 0 := (CharP.cast_eq_zero_iff (ZMod (ℓ ^ (0 + 1))) (ℓ ^ (0 + 1)) ℓ).2 (by simp)
        rw [this, zero_smul]; exact (ASM21.M2L.rowSp I).zero_mem
      · intro x hx; rw [hW0 x hx]; exact Submodule.zero_mem _
    ·
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      set z : ↥I := f.symm (1, 0) with hzdef
      have hfz : f z = (1, 0) := by rw [hzdef, AddEquiv.apply_symm_apply]
      have hz1 : (ℓ ^ (e' + 1)) • z = 0 := by
        apply f.injective
        rw [map_nsmul, hfz, map_zero, Prod.smul_mk, smul_zero, nsmul_eq_mul, mul_one, ZMod.natCast_self, Prod.mk_zero_zero]
      have hz2 : (ℓ ^ e') • z ≠ 0 := by
        intro h
        have := congrArg f h
        rw [map_nsmul, hfz, map_zero, Prod.smul_mk, smul_zero, nsmul_eq_mul, mul_one, Prod.mk_eq_zero] at this
        have h2 := (CharP.cast_eq_zero_iff (ZMod (ℓ ^ (e' + 1))) (ℓ ^ (e' + 1)) (ℓ ^ e')).1 this.1
        rw [Nat.pow_dvd_pow_iff_le_right hℓ.one_lt] at h2
        omega

      have hex : ∃ i : Fin 2, (ℓ ^ e') • (z : Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e' + 1 + 1)))) i ≠ 0 := by
        by_contra hall
        push_neg at hall
        apply hz2
        apply Subtype.ext
        rw [AddSubmonoidClass.coe_nsmul, Submodule.coe_zero]
        ext i j
        exact congrFun (hall i) j
      obtain ⟨i, hi⟩ := hex
      have hw₀W : (z : Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e' + 1 + 1)))) i ∈ ASM21.M2L.rowSp I := hrows _ z.2 i
      have hw₀e : (ℓ ^ (e' + 1)) • (z : Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e' + 1 + 1)))) i = 0 := by
        have h := congrArg Subtype.val hz1
        rw [AddSubmonoidClass.coe_nsmul, Submodule.coe_zero] at h
        exact congrFun h i
      obtain ⟨wt, hwt⟩ := ASM21.M2LL.exists_eq_smul_of_pow_smul_eq_zero ℓ (e' + 1) _ hw₀e
      have hℓwt : ℓ • wt = (z : Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e' + 1 + 1)))) i := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ (e' + 1 + 1))), ← hwt]
      have hord_wt : addOrderOf wt = ℓ ^ (e' + 1 + 1) := by
        apply ASM21.M2LL.addOrderOf_eq_prime_pow_succ ℓ (e' + 1) wt
        · have : ℓ ^ (e' + 1) • wt = ℓ ^ e' • (ℓ • wt) := by rw [smul_smul, ← pow_succ]
          rw [this, hℓwt]; exact hi
        · rw [← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ (e' + 1 + 1))), ZMod.natCast_self, zero_smul]
      have hord_w₀ : addOrderOf ((z : Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e' + 1 + 1)))) i) = ℓ ^ (e' + 1) :=
        ASM21.M2LL.addOrderOf_eq_prime_pow_succ ℓ e' _ hi hw₀e

      have hcardW : Nat.card ↥(ASM21.M2L.rowSp I) = ℓ ^ (e' + 1) := by
        have h1 : Nat.card ↥I = ℓ ^ (e' + 1) * ℓ ^ (e' + 1) := by
          haveI : NeZero (ℓ ^ (e' + 1)) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
          rw [Nat.card_congr f.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card]
        have h2 : Nat.card ↥I = Nat.card ↥(ASM21.M2L.rowSp I) * Nat.card ↥(ASM21.M2L.rowSp I) := by
          rw [← Nat.card_prod]
          rw [Nat.card_congr (LinearEquiv.ofEq _ _ hIW.symm).toEquiv, Nat.card_congr (ASM21.M2LL.idealOfAddEquiv (ASM21.M2L.rowSp I)).toEquiv]
        have : Nat.card ↥(ASM21.M2L.rowSp I) ^ 2 = (ℓ ^ (e' + 1)) ^ 2 := by rw [sq, sq, ← h2, h1]
        exact Nat.pow_left_injective two_ne_zero this
      refine ⟨wt, hord_wt, by rw [← hwt]; exact hw₀W, ?_⟩

      intro x hx
      have hsub : AddSubgroup.zmultiples ((z : Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e' + 1 + 1)))) i) = (ASM21.M2L.rowSp I).toAddSubgroup := by
        apply AddSubgroup.eq_of_le_of_card_ge
        · rw [AddSubgroup.zmultiples_le]; exact hw₀W
        · rw [Nat.card_zmultiples, hord_w₀]
          exact hcardW.le
      have hx' : x ∈ AddSubgroup.zmultiples ((z : Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ (e' + 1 + 1)))) i) := by
        rw [hsub]; exact hx
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hx'
      rw [Submodule.mem_span_singleton]
      refine ⟨((k * ℓ : ℤ) : ZMod (ℓ ^ (e' + 1 + 1))), ?_⟩
      rw [Int.cast_smul_eq_zsmul, ← hℓwt, ← natCast_zsmul wt ℓ, smul_smul]
  obtain ⟨wt, hord, hℓwt, hWle⟩ := key
  refine ⟨ASM21.M2L.idealOf (Submodule.span (ZMod (ℓ ^ (e + 1))) ({wt} : Set (Fin 2 → ZMod (ℓ ^ (e + 1))))), ?_, ⟨?_⟩, ?_⟩
  ·
    intro X hX i
    exact hWle _ (hrows X hX i)
  ·
    exact (ASM21.M2LL.idealOfAddEquiv _).trans
      (AddEquiv.prodCongr (ASM21.M2LL.spanSingletonEquiv wt hord).symm (ASM21.M2LL.spanSingletonEquiv wt hord).symm)
  ·
    intro X hX
    rw [← hIW]
    intro i
    rw [ASM21.M2LL.natCast_smul_apply]
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hX i)
    rw [← ha, smul_comm]
    exact (ASM21.M2L.rowSp I).smul_mem a hℓwt

end S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow
end P2MW
export P2MW.S_Matrix_exists_submodule_addEquiv_zmod_pow_succ_of_addEquiv_zmod_pow (solution)
