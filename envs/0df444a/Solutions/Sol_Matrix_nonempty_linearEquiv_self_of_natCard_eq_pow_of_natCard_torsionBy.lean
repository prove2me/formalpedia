-- Prove2me | solution 1 for Matrix.nonempty_linearEquiv_self_of_natCard_eq_pow_of_natCard_torsionBy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/4fe2d57e-cc44-5f86-983d-e6401f64ba50

import Mathlib
import Theorems.Thm_AddCommGroup_nonempty_basis_zmod_pow_of_card_torsionBy
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_nonempty_linearEquiv_self_of_natCard_eq_pow_of_natCard_torsionBy

set_option autoImplicit false

universe u

namespace ASM21
namespace M2

variable {ℓ : ℕ}

def e (ℓ : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := !![1, 0; 0, 0]

def f (ℓ : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := !![0, 0; 0, 1]

def w (ℓ : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := !![0, 1; 1, 0]

theorem e_add_f : e ℓ + f ℓ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e, f]
theorem e_mul_e : e ℓ * e ℓ = e ℓ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e, Matrix.mul_apply, Fin.sum_univ_two]
theorem f_mul_f : f ℓ * f ℓ = f ℓ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [f, Matrix.mul_apply, Fin.sum_univ_two]
theorem e_mul_f : e ℓ * f ℓ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e, f, Matrix.mul_apply, Fin.sum_univ_two]
theorem f_mul_e : f ℓ * e ℓ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e, f, Matrix.mul_apply, Fin.sum_univ_two]
theorem w_mul_w : w ℓ * w ℓ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [w, Matrix.mul_apply, Fin.sum_univ_two]
theorem w_mul_e : w ℓ * e ℓ = f ℓ * w ℓ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [w, e, f, Matrix.mul_apply, Fin.sum_univ_two]
theorem e_mul_w : e ℓ * w ℓ = w ℓ * f ℓ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [w, e, f, Matrix.mul_apply, Fin.sum_univ_two]

theorem decomp (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) :
    X = X 0 0 • e ℓ + X 0 1 • (e ℓ * w ℓ) + X 1 0 • (w ℓ * e ℓ) + X 1 1 • f ℓ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [w, e, f, Matrix.mul_apply, Fin.sum_univ_two]

theorem card_R [Fact ℓ.Prime] : Nat.card (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = ℓ ^ 4 := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  rw [Nat.card_eq_fintype_card, show Fintype.card (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) = Fintype.card (Fin 2 → Fin 2 → ZMod ℓ) from rfl,
    Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  ring

end ASM21.M2

namespace ASM21
namespace M2

section module
variable {ℓ : ℕ} (V : Type u) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V]

def sc (c : ZMod ℓ) (v : V) : V := (algebraMap (ZMod ℓ) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) c) • v

theorem smul_matrix_smul (c : ZMod ℓ) (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (v : V) : (c • X) • v = sc V c (X • v) := by
  rw [Algebra.smul_def, mul_smul]; rfl

theorem X_sc (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (c : ZMod ℓ) (v : V) : X • sc V c v = sc V c (X • v) := by
  show X • ((algebraMap (ZMod ℓ) _ c) • v) = (algebraMap (ZMod ℓ) _ c) • (X • v)
  rw [← mul_smul, ← mul_smul, Algebra.commutes]

theorem sc_add (c : ZMod ℓ) (u v : V) : sc V c (u + v) = sc V c u + sc V c v := smul_add _ _ _
theorem sc_zero (c : ZMod ℓ) : sc V c (0 : V) = 0 := smul_zero _
theorem mul_sc (c d : ZMod ℓ) (v : V) : sc V (c * d) v = sc V c (sc V d v) := by
  show (algebraMap (ZMod ℓ) _ (c * d)) • v = _; rw [map_mul, mul_smul]; rfl
theorem one_sc (v : V) : sc V (1 : ZMod ℓ) v = v := by
  show (algebraMap (ZMod ℓ) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) 1) • v = v; rw [map_one, one_smul]
theorem zero_sc (v : V) : sc V (0 : ZMod ℓ) v = 0 := by
  show (algebraMap (ZMod ℓ) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) 0) • v = 0; rw [map_zero, zero_smul]
theorem neg_sc (c : ZMod ℓ) (v : V) : sc V (-c) v = -(sc V c v) := by
  show (algebraMap (ZMod ℓ) _ (-c)) • v = _; rw [map_neg, neg_smul]; rfl

theorem e_add_f_smul (v : V) : e ℓ • v + f ℓ • v = v := by rw [← add_smul, e_add_f, one_smul]
theorem e_e (v : V) : e ℓ • (e ℓ • v) = e ℓ • v := by rw [← mul_smul, e_mul_e]
theorem e_f (v : V) : e ℓ • (f ℓ • v) = 0 := by rw [← mul_smul, e_mul_f, zero_smul]
theorem f_e (v : V) : f ℓ • (e ℓ • v) = 0 := by rw [← mul_smul, f_mul_e, zero_smul]
theorem w_w (v : V) : w ℓ • (w ℓ • v) = v := by rw [← mul_smul, w_mul_w, one_smul]
theorem w_e (v : V) : w ℓ • (e ℓ • v) = f ℓ • (w ℓ • v) := by rw [← mul_smul, w_mul_e, mul_smul]
theorem e_w (v : V) : e ℓ • (w ℓ • v) = w ℓ • (f ℓ • v) := by rw [← mul_smul, e_mul_w, mul_smul]

theorem e_w_of_e {v : V} (hv : e ℓ • v = v) : e ℓ • (w ℓ • v) = 0 := by
  rw [e_w, ← hv, f_e, smul_zero]
theorem f_of_e {v : V} (hv : e ℓ • v = v) : f ℓ • v = 0 := by rw [← hv, f_e]
theorem f_w_of_e {v : V} (hv : e ℓ • v = v) : f ℓ • (w ℓ • v) = w ℓ • v := by
  rw [← w_e, hv]

def split : V ≃ {v : V // e ℓ • v = v} × {v : V // e ℓ • v = v} where
  toFun v := (⟨e ℓ • v, e_e V v⟩, ⟨e ℓ • (w ℓ • v), e_e V _⟩)
  invFun p := (p.1 : V) + w ℓ • (p.2 : V)
  left_inv v := by
    show e ℓ • v + w ℓ • (e ℓ • (w ℓ • v)) = v
    rw [e_w, w_w, e_add_f_smul]
  right_inv p := by
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p
    simp only [Prod.mk.injEq, Subtype.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [smul_add, hx, e_w_of_e V hy, add_zero]
    · rw [smul_add, smul_add, e_w_of_e V hx, zero_add, w_w, hy]

theorem natCard_eFixed [Fact ℓ.Prime] [Finite V] (hV : Nat.card V = ℓ ^ 4) : Nat.card {v : V // e ℓ • v = v} = ℓ ^ 2 := by
  have h := Nat.card_congr (split V (ℓ := ℓ))
  rw [Nat.card_prod, hV] at h
  have : (Nat.card {v : V // e ℓ • v = v}) ^ 2 = (ℓ ^ 2) ^ 2 := by rw [sq, ← h]; ring
  exact Nat.pow_left_injective two_ne_zero this

theorem exists_indep [Fact ℓ.Prime] [Finite V] (hV : Nat.card V = ℓ ^ 4) :
    ∃ v₁ v₂ : V, e ℓ • v₁ = v₁ ∧ e ℓ • v₂ = v₂ ∧
      ∀ α β : ZMod ℓ, sc V α v₁ + sc V β v₂ = 0 → α = 0 ∧ β = 0 := by
  classical
  have hcard := natCard_eFixed V hV
  have hℓ : 1 < ℓ := (Fact.out : ℓ.Prime).one_lt
  have h1 : 1 < Nat.card {v : V // e ℓ • v = v} := by
    rw [hcard]; exact Nat.one_lt_pow two_ne_zero hℓ
  haveI : Nontrivial {v : V // e ℓ • v = v} := Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨⟨v₁, hv₁⟩, hne⟩ := exists_ne (⟨0, smul_zero _⟩ : {v : V // e ℓ • v = v})
  have hv₁0 : v₁ ≠ 0 := fun h => hne (Subtype.ext h)
  let line : ZMod ℓ → {v : V // e ℓ • v = v} := fun c => ⟨sc V c v₁, by rw [X_sc, hv₁]⟩
  have hlt : Nat.card (Set.range line) < Nat.card {v : V // e ℓ • v = v} := by
    calc Nat.card (Set.range line) ≤ Nat.card (ZMod ℓ) := Finite.card_range_le line
      _ = ℓ := by rw [Nat.card_eq_fintype_card, ZMod.card]
      _ < ℓ ^ 2 := by nlinarith
      _ = _ := hcard.symm
  have hnot : ∃ v₂ : {v : V // e ℓ • v = v}, v₂ ∉ Set.range line := by
    by_contra h
    push_neg at h
    have : Set.range line = Set.univ := Set.eq_univ_of_forall h
    rw [this, Nat.card_univ] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨⟨v₂, hv₂⟩, hv₂n⟩ := hnot
  refine ⟨v₁, v₂, hv₁, hv₂, fun α β hαβ => ?_⟩
  by_cases hβ : β = 0
  · refine ⟨?_, hβ⟩
    rw [hβ, zero_sc, add_zero] at hαβ
    by_contra hα
    apply hv₁0
    have := congrArg (sc V α⁻¹) hαβ
    rwa [← mul_sc, inv_mul_cancel₀ hα, one_sc, sc_zero] at this
  · exfalso
    apply hv₂n
    have h2 : sc V β v₂ = -(sc V α v₁) := eq_neg_of_add_eq_zero_right hαβ
    have h3 : v₂ = sc V (-(β⁻¹ * α)) v₁ := by
      have := congrArg (sc V β⁻¹) h2
      rw [← mul_sc, inv_mul_cancel₀ hβ, one_sc] at this
      rw [this, ← neg_sc, ← mul_sc, neg_mul_eq_mul_neg]
    exact ⟨-(β⁻¹ * α), Subtype.ext h3.symm⟩

theorem eq_zero_of_smul_gen_eq_zero {v₁ v₂ : V} (hv₁ : e ℓ • v₁ = v₁) (hv₂ : e ℓ • v₂ = v₂)
    (hind : ∀ α β : ZMod ℓ, sc V α v₁ + sc V β v₂ = 0 → α = 0 ∧ β = 0)
    (X : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (hX : X • (v₁ + w ℓ • v₂) = 0) : X = 0 := by
  have a2 : (e ℓ * w ℓ) • v₁ = 0 := by rw [mul_smul, e_w_of_e V hv₁]
  have a3 : (w ℓ * e ℓ) • v₁ = w ℓ • v₁ := by rw [mul_smul, hv₁]
  have a4 : f ℓ • v₁ = 0 := f_of_e V hv₁
  have b1 : e ℓ • (w ℓ • v₂) = 0 := e_w_of_e V hv₂
  have b2 : (e ℓ * w ℓ) • (w ℓ • v₂) = v₂ := by rw [mul_smul, w_w, hv₂]
  have b3 : (w ℓ * e ℓ) • (w ℓ • v₂) = 0 := by rw [mul_smul, e_w_of_e V hv₂, smul_zero]
  have b4 : f ℓ • (w ℓ • v₂) = w ℓ • v₂ := f_w_of_e V hv₂
  have h0 := hX
  rw [decomp X] at h0
  simp only [add_smul, smul_add, smul_matrix_smul, hv₁, a2, a3, a4, b1, b2, b3, b4, sc_zero, add_zero, zero_add] at h0

  have he := congrArg (fun t => e ℓ • t) h0
  simp only [smul_add, smul_zero, X_sc, hv₁, hv₂, e_w_of_e V hv₁, e_w_of_e V hv₂, sc_zero, add_zero, zero_add] at he
  obtain ⟨ha, hb⟩ := hind _ _ he

  have hf := congrArg (fun t => w ℓ • (f ℓ • t)) h0
  simp only [smul_add, smul_zero, X_sc, a4, f_of_e V hv₂, b4, f_w_of_e V hv₁, w_w, sc_zero, add_zero, zero_add] at hf
  obtain ⟨hc, hd⟩ := hind _ _ hf
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

end module

theorem nonempty_linearEquiv (ℓ : ℕ) [Fact ℓ.Prime] (V : Type u) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) V] [Finite V]
    (hV : Nat.card V = ℓ ^ 4) :
    Nonempty (V ≃ₗ[Matrix (Fin 2) (Fin 2) (ZMod ℓ)] Matrix (Fin 2) (Fin 2) (ZMod ℓ)) := by
  classical
  obtain ⟨v₁, v₂, hv₁, hv₂, hind⟩ := exists_indep V hV
  let T : Matrix (Fin 2) (Fin 2) (ZMod ℓ) →ₗ[Matrix (Fin 2) (Fin 2) (ZMod ℓ)] V :=
    { toFun := fun X => X • (v₁ + w ℓ • v₂)
      map_add' := fun X Y => add_smul X Y _
      map_smul' := fun a X => mul_smul a X _ }
  have hT : ∀ X, T X = X • (v₁ + w ℓ • v₂) := fun X => rfl
  have hTinj : Function.Injective T := by
    intro X Y hXY
    rw [hT, hT] at hXY
    have h0 : (X - Y) • (v₁ + w ℓ • v₂) = 0 := by rw [sub_smul, hXY, sub_self]
    exact sub_eq_zero.1 (eq_zero_of_smul_gen_eq_zero V hv₁ hv₂ hind (X - Y) h0)
  have hTbij : Function.Bijective T :=
    hTinj.bijective_of_nat_card_le (by rw [hV, card_R])
  exact ⟨(LinearEquiv.ofBijective T hTbij).symm⟩

end ASM21.M2

namespace ASM21
namespace M2P
open ASM21.M2

theorem card_R' (n : ℕ) [NeZero n] : Nat.card (Matrix (Fin 2) (Fin 2) (ZMod n)) = n ^ 4 := by
  rw [Nat.card_eq_fintype_card, show Fintype.card (Matrix (Fin 2) (Fin 2) (ZMod n)) = Fintype.card (Fin 2 → Fin 2 → ZMod n) from rfl,
    Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  ring

section mod
variable {n : ℕ} (V : Type u) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod n)) V]

theorem e_nsmul (k : ℕ) (v : V) : e n • (k • v) = k • (e n • v) := smul_comm _ _ _
theorem w_nsmul (k : ℕ) (v : V) : w n • (k • v) = k • (w n • v) := smul_comm _ _ _

def splitTors (k : ℕ) :
    {v : V // k • v = 0} ≃ {v : V // e n • v = v ∧ k • v = 0} × {v : V // e n • v = v ∧ k • v = 0} where
  toFun v := (⟨e n • (v : V), e_e V _, by rw [← e_nsmul, v.2, smul_zero]⟩,
              ⟨e n • (w n • (v : V)), e_e V _, by rw [← e_nsmul, ← w_nsmul, v.2, smul_zero, smul_zero]⟩)
  invFun p := ⟨(p.1 : V) + w n • (p.2 : V), by rw [smul_add, ← w_nsmul, p.1.2.2, p.2.2.2, smul_zero, add_zero]⟩
  left_inv v := by
    apply Subtype.ext
    show e n • (v : V) + w n • (e n • (w n • (v : V))) = v
    rw [e_w, w_w, e_add_f_smul]
  right_inv p := by
    obtain ⟨⟨x, hx, hxk⟩, ⟨y, hy, hyk⟩⟩ := p
    simp only [Prod.mk.injEq, Subtype.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [smul_add, hx, e_w_of_e V hy, add_zero]
    · rw [smul_add, smul_add, e_w_of_e V hx, zero_add, w_w, hy]

def Vz (n : ℕ) (V : Type u) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod n)) V] : Type u := V

scoped instance instAddCommGroupVz : AddCommGroup (Vz n V) := inferInstanceAs (AddCommGroup V)
scoped instance instModVz : Module (ZMod n) (Vz n V) :=
  (Module.compHom V (algebraMap (ZMod n) (Matrix (Fin 2) (Fin 2) (ZMod n))) : Module (ZMod n) V)

def toVz (v : V) : Vz n V := v

def ofVz (x : Vz n V) : V := x
theorem ofVz_toVz (v : V) : ofVz (n := n) V (toVz V v) = v := rfl
theorem toVz_ofVz (x : Vz n V) : toVz V (ofVz V x) = x := rfl
theorem ofVz_add (x y : Vz n V) : ofVz V (x + y) = ofVz V x + ofVz V y := rfl
theorem ofVz_zero : ofVz V (0 : Vz n V) = 0 := rfl
theorem ofVz_smul (c : ZMod n) (x : Vz n V) : ofVz V (c • x) = sc V c (ofVz V x) := rfl
theorem ofVz_nsmul (k : ℕ) (x : Vz n V) : ofVz V (k • x) = k • ofVz V x := rfl

def eSubZ : Submodule (ZMod n) (Vz n V) where
  carrier := {x | e n • ofVz V x = ofVz V x}
  zero_mem' := by show e n • (0 : V) = 0; exact smul_zero _
  add_mem' := by
    intro x y hx hy
    show e n • (ofVz V x + ofVz V y) = ofVz V x + ofVz V y
    rw [smul_add, hx, hy]
  smul_mem' := by
    intro c x hx
    show e n • sc V c (ofVz V x) = sc V c (ofVz V x)
    rw [X_sc, hx]

theorem mem_eSubZ (x : Vz n V) : x ∈ eSubZ V ↔ e n • ofVz V x = ofVz V x := Iff.rfl

def torsEquiv (k : ℕ) :
    ↥(Submodule.torsionBy ℤ (↥(eSubZ (n := n) V)) (k : ℤ)) ≃ {v : V // e n • v = v ∧ k • v = 0} where
  toFun x := ⟨ofVz V x.1.1, x.1.2, by
    have h : (k : ℤ) • x.1 = 0 := (Submodule.mem_torsionBy_iff _ _).1 x.2
    rw [natCast_zsmul] at h
    have := congrArg (fun t : ↥(eSubZ (n := n) V) => ofVz V t.1) h
    exact this⟩
  invFun v := ⟨⟨toVz V v.1, v.2.1⟩, by
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
    exact Subtype.ext v.2.2⟩
  left_inv x := rfl
  right_inv v := rfl

end mod
end ASM21.M2P
p2m_reactivate "P2MW.S_Matrix_nonempty_linearEquiv_self_of_natCard_eq_pow_of_natCard_torsionBy.ASM21 P2MW.S_Matrix_nonempty_linearEquiv_self_of_natCard_eq_pow_of_natCard_torsionBy.ASM21.M2P"
p2m_reactivate "P2MW.S_Matrix_nonempty_linearEquiv_self_of_natCard_eq_pow_of_natCard_torsionBy.ASM21"

theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime] (m : ℕ) [NeZero m]
    (V : Type u) [AddCommGroup V] [Module (Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ m))) V] [Finite V]
    (hV : ∀ j ≤ m, Nat.card {v : V // ℓ ^ j • v = 0} = ℓ ^ (4 * j)) :
    Nonempty (V ≃ₗ[Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ m))] Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ m))) := by
  classical
  have hℓ0 : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  haveI : NeZero (ℓ ^ m) := ⟨pow_ne_zero m hℓ0⟩

  have hcardE : ∀ j ≤ m, Nat.card ↥(Submodule.torsionBy ℤ (↥(ASM21.M2P.eSubZ (n := ℓ ^ m) V)) ((ℓ ^ j : ℕ) : ℤ)) = (ℓ ^ j) ^ 2 := by
    intro j hj
    have h1 := Nat.card_congr (ASM21.M2P.torsEquiv (n := ℓ ^ m) V (ℓ ^ j))
    have h2 := Nat.card_congr (ASM21.M2P.splitTors (n := ℓ ^ m) V (ℓ ^ j))
    rw [Nat.card_prod, hV j hj] at h2
    have hsq : Nat.card {v : V // ASM21.M2.e (ℓ ^ m) • v = v ∧ ℓ ^ j • v = 0} ^ 2 = ((ℓ ^ j) ^ 2) ^ 2 := by
      rw [sq, ← h2]; ring
    rw [h1]
    exact Nat.pow_left_injective two_ne_zero hsq

  have hrange : ∀ x : ↥(ASM21.M2P.eSubZ (n := ℓ ^ m) V),
      x ∈ (AddMonoidHom.id ↥(ASM21.M2P.eSubZ (n := ℓ ^ m) V)).range ↔ ((ℓ ^ m : ℕ) : ℤ) • x = 0 := by
    intro x
    constructor
    · intro _
      rw [← Int.cast_smul_eq_zsmul (ZMod (ℓ ^ m)), Int.cast_natCast, ZMod.natCast_self, zero_smul]
    · intro _; exact ⟨x, rfl⟩
  obtain ⟨bs⟩ := AddCommGroup.nonempty_basis_zmod_pow_of_card_torsionBy ℓ 2 m hcardE
    (AddMonoidHom.id _) (fun _ _ h => h) hrange

  obtain ⟨v₁, hv₁, hv₁def⟩ : ∃ v₁ : V, ASM21.M2.e (ℓ ^ m) • v₁ = v₁ ∧ v₁ = ASM21.M2P.ofVz V (bs 0).1 := ⟨_, (bs 0).2, rfl⟩
  obtain ⟨v₂, hv₂, hv₂def⟩ : ∃ v₂ : V, ASM21.M2.e (ℓ ^ m) • v₂ = v₂ ∧ v₂ = ASM21.M2P.ofVz V (bs 1).1 := ⟨_, (bs 1).2, rfl⟩
  have hind : ∀ α β : ZMod (ℓ ^ m), ASM21.M2.sc V α v₁ + ASM21.M2.sc V β v₂ = 0 → α = 0 ∧ β = 0 := by
    intro α β h
    have hli := LinearIndependent.pair_iff.1 (by
      have : (![bs 0, bs 1] : Fin 2 → ↥(ASM21.M2P.eSubZ (n := ℓ ^ m) V)) = ⇑bs := by
        funext i; fin_cases i <;> rfl
      rw [this]; exact bs.linearIndependent)
    apply hli α β
    apply Subtype.ext
    show ASM21.M2P.ofVz V ((α • bs 0 + β • bs 1 : ↥(ASM21.M2P.eSubZ (n := ℓ ^ m) V)).1) =
      ASM21.M2P.ofVz V ((0 : ↥(ASM21.M2P.eSubZ (n := ℓ ^ m) V)).1)
    rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_zero, ASM21.M2P.ofVz_add,
      ASM21.M2P.ofVz_smul, ASM21.M2P.ofVz_smul, ASM21.M2P.ofVz_zero, ← hv₁def, ← hv₂def]
    exact h

  have hR0 : ((ℓ ^ m : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ m))) = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hkill : ∀ v : V, ℓ ^ m • v = 0 := fun v => by
    rw [← Nat.cast_smul_eq_nsmul (Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ m))) (ℓ ^ m) v, hR0, zero_smul]
  have hcardV : Nat.card V = ℓ ^ (4 * m) := by
    rw [← hV m le_rfl]
    exact (Nat.card_congr (Equiv.subtypeUnivEquiv hkill)).symm

  let T : Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ m)) →ₗ[Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ m))] V :=
    { toFun := fun X => X • (v₁ + ASM21.M2.w (ℓ ^ m) • v₂)
      map_add' := fun X Y => add_smul X Y _
      map_smul' := fun c X => mul_smul c X _ }
  have hT : ∀ X, T X = X • (v₁ + ASM21.M2.w (ℓ ^ m) • v₂) := fun X => rfl
  have hTinj : Function.Injective T := by
    intro X Y hXY
    rw [hT, hT] at hXY
    have h0 : (X - Y) • (v₁ + ASM21.M2.w (ℓ ^ m) • v₂) = 0 := by rw [sub_smul, hXY, sub_self]
    exact sub_eq_zero.1 (ASM21.M2.eq_zero_of_smul_gen_eq_zero V hv₁ hv₂ hind (X - Y) h0)
  have hTbij : Function.Bijective T :=
    hTinj.bijective_of_nat_card_le (by rw [hcardV, ASM21.M2P.card_R', ← pow_mul, mul_comm])
  exact ⟨(LinearEquiv.ofBijective T hTbij).symm⟩

end S_Matrix_nonempty_linearEquiv_self_of_natCard_eq_pow_of_natCard_torsionBy
end P2MW
export P2MW.S_Matrix_nonempty_linearEquiv_self_of_natCard_eq_pow_of_natCard_torsionBy (solution)
