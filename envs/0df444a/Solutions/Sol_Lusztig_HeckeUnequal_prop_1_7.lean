-- Prove2me | solution 1 for Lusztig.HeckeUnequal.prop_1_7
-- status  : ACCEPTED   (prove)
-- author  : @lookeng
-- created : 2026-11-13T18:09:47.263778+00:00
-- url     : https://prove2.me/submissions/a8635169-b6ea-4842-85c1-88f65edde106

import Mathlib.GroupTheory.Coxeter.Inversion

/-!
Proof of Lusztig, *Hecke algebras with unequal parameters*, Prop. 1.7, via the action of `W`
on `W × ℤ/2` from Prop. 1.5 (`U_s (t, ε) = (s t s, ε + [t = s])`).
-/

open CoxeterSystem

namespace Lusztig.HeckeUnequal.TitsAction

attribute [local instance] Classical.propDecidable

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- Lusztig's permutation `U_s` of `W × ℤ/2` (Prop. 1.5, with `T` enlarged to `W`). -/
noncomputable def U (i : B) : Equiv.Perm (W × ZMod 2) where
  toFun x := (cs.simple i * x.1 * cs.simple i, x.2 + if x.1 = cs.simple i then 1 else 0)
  invFun x := (cs.simple i * x.1 * cs.simple i, x.2 + if x.1 = cs.simple i then 1 else 0)
  left_inv x := by
    obtain ⟨y, ε⟩ := x
    have h : cs.simple i * y * cs.simple i = cs.simple i ↔ y = cs.simple i := by
      constructor
      · intro h
        have := congrArg (fun z => cs.simple i * z * cs.simple i) h
        simpa [mul_assoc, cs.simple_mul_simple_cancel_left] using this
      · rintro rfl; simp [mul_assoc]
    ext
    · simp [mul_assoc]
    · by_cases hy : y = cs.simple i
      · subst hy
        have h3 : cs.simple i * cs.simple i * cs.simple i = cs.simple i := by simp
        simp only [h3, ↓reduceIte]
        rw [add_assoc, show (1 : ZMod 2) + 1 = 0 from rfl, add_zero]
      · simp [hy, (not_congr h).mpr hy]
  right_inv x := by
    obtain ⟨y, ε⟩ := x
    have h : cs.simple i * y * cs.simple i = cs.simple i ↔ y = cs.simple i := by
      constructor
      · intro h
        have := congrArg (fun z => cs.simple i * z * cs.simple i) h
        simpa [mul_assoc, cs.simple_mul_simple_cancel_left] using this
      · rintro rfl; simp [mul_assoc]
    ext
    · simp [mul_assoc]
    · by_cases hy : y = cs.simple i
      · subst hy
        have h3 : cs.simple i * cs.simple i * cs.simple i = cs.simple i := by simp
        simp only [h3, ↓reduceIte]
        rw [add_assoc, show (1 : ZMod 2) + 1 = 0 from rfl, add_zero]
      · simp [hy, (not_congr h).mpr hy]

theorem U_apply (i : B) (y : W) (ε : ZMod 2) :
    U cs i (y, ε) = (cs.simple i * y * cs.simple i, ε + if y = cs.simple i then 1 else 0) := rfl

/-- The product `U_{a₁} ⋯ U_{aₙ}` attached to a word. -/
noncomputable def Φ (ω : List B) : Equiv.Perm (W × ZMod 2) := (ω.map (U cs)).prod

/-- Explicit formula: `Φ ω` conjugates by `π ω` and adds the number of occurrences of the
conjugated element in the left inversion sequence. -/
theorem Φ_apply (ω : List B) (y : W) (ε : ZMod 2) :
    Φ cs ω (y, ε) = (cs.wordProd ω * y * (cs.wordProd ω)⁻¹,
      ε + (((cs.leftInvSeq ω).count (cs.wordProd ω * y * (cs.wordProd ω)⁻¹) : ℕ) : ZMod 2)) := by
  induction ω generalizing y ε with
  | nil => simp [Φ, CoxeterSystem.leftInvSeq]
  | cons a ω ih =>
    have hΦ : Φ cs (a :: ω) = U cs a * Φ cs ω := by simp [Φ]
    rw [hΦ, Equiv.Perm.mul_apply, ih, U_apply]
    set z := cs.wordProd ω * y * (cs.wordProd ω)⁻¹ with hz
    have hz' : cs.wordProd (a :: ω) * y * (cs.wordProd (a :: ω))⁻¹ =
        cs.simple a * z * cs.simple a := by
      simp [hz, cs.wordProd_cons, mul_assoc]
    rw [hz']
    have hcount : (cs.leftInvSeq (a :: ω)).count (cs.simple a * z * cs.simple a) =
        (cs.leftInvSeq ω).count z + if z = cs.simple a then 1 else 0 := by
      have hinj : Function.Injective (MulAut.conj (cs.simple a)) :=
        (MulAut.conj (cs.simple a)).injective
      have hc : MulAut.conj (cs.simple a) z = cs.simple a * z * cs.simple a := by
        simp [MulAut.conj_apply]
      simp only [CoxeterSystem.leftInvSeq]
      rw [List.count_cons, ← hc, List.count_map_of_injective _ _ hinj]
      congr 1
      by_cases h : z = cs.simple a
      · simp [h, hc, mul_assoc]
      · have : ¬ cs.simple a = MulAut.conj (cs.simple a) z := by
          intro h'
          apply h
          have := congrArg (MulAut.conj (cs.simple a)).symm h'
          simpa [MulAut.conj_symm_apply, MulAut.conj_apply, mul_assoc] using this.symm
        simp only [h, ↓reduceIte, List.count_cons]
        simp only [beq_iff_eq, this, ↓reduceIte]
    refine Prod.ext rfl ?_
    simp only [hcount, Nat.cast_add]
    split_ifs <;> simp [add_assoc, add_comm]

theorem Φ_alternatingWord (i j : B) (p : ℕ) :
    Φ cs (CoxeterSystem.alternatingWord i j (2 * p)) = (U cs i * U cs j) ^ p := by
  induction p with
  | zero => simp [Φ, CoxeterSystem.alternatingWord]
  | succ p ih =>
    have hw : CoxeterSystem.alternatingWord i j (2 * (p + 1)) =
        i :: j :: CoxeterSystem.alternatingWord i j (2 * p) := by
      rw [show 2 * (p + 1) = 2 * p + 1 + 1 by ring, CoxeterSystem.alternatingWord_succ',
        CoxeterSystem.alternatingWord_succ']
      have h1 : ¬ Even (2 * p + 1) := by simp [parity_simps]
      have h2 : Even (2 * p) := by simp
      simp [h1, h2]
    rw [hw, pow_succ', ← ih]
    simp [Φ, mul_assoc]

/-- The left inversion sequence of the braid word of length `2 m(i,j)` repeats with period
`m(i,j)`, so every element occurs an even number of times in it. -/
theorem count_leftInvSeq_braid_even (i j : B) (y : W) :
    (((cs.leftInvSeq (CoxeterSystem.alternatingWord i j (2 * M i j))).count y : ℕ) : ZMod 2) = 0 := by
  set p := M i j with hp
  have hlen : (cs.leftInvSeq (CoxeterSystem.alternatingWord i j (2 * p))).length = 2 * p := by
    simp [CoxeterSystem.length_alternatingWord]
  have hper : ∀ k (hk : k < 2 * p) (hk' : p ≤ k),
      (cs.leftInvSeq (CoxeterSystem.alternatingWord i j (2 * p)))[k]'(by omega) =
        (cs.leftInvSeq (CoxeterSystem.alternatingWord i j (2 * p)))[k - p]'(by omega) := by
    intro k hk hk'
    rw [cs.getElem_leftInvSeq_alternatingWord i j p k hk,
      cs.getElem_leftInvSeq_alternatingWord i j p (k - p) (by omega),
      cs.prod_alternatingWord_eq_mul_pow, cs.prod_alternatingWord_eq_mul_pow]
    have e1 : (2 * k + 1) / 2 = (k - p) + p := by omega
    have e2 : (2 * (k - p) + 1) / 2 = k - p := by omega
    rw [e1, e2, pow_add]
    have hM : (cs.simple j * cs.simple i) ^ p = 1 := by
      rw [hp, M.symmetric i j]; exact cs.simple_mul_simple_pow j i
    have o1 : ¬ Even (2 * k + 1) := by simp [parity_simps]
    have o2 : ¬ Even (2 * (k - p) + 1) := by simp [parity_simps]
    rw [hM, mul_one]
    simp only [o1, o2, ↓reduceIte]
  set L := cs.leftInvSeq (CoxeterSystem.alternatingWord i j (2 * p)) with hL
  have hsplit : L = L.take p ++ L.take p := by
    apply List.ext_getElem
    · simp [hlen]; omega
    · intro k h1 h2
      by_cases hk : k < p
      · rw [List.getElem_append_left (by simp; omega)]
        simp
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_take]
        have : min p L.length = p := by omega
        simp only [List.length_take, this]
        exact hper k (by omega) (by omega)
  rw [hsplit, List.count_append, ← two_mul, Nat.cast_mul]
  simp only [Nat.cast_ofNat]
  rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]

theorem isLiftable : M.IsLiftable (U cs) := by
  intro i j
  rw [← Φ_alternatingWord]
  ext ⟨y, ε⟩ <;> rw [Φ_apply]
  · have h1 : cs.wordProd (CoxeterSystem.alternatingWord i j (2 * M i j)) = 1 := by
      rw [cs.prod_alternatingWord_eq_mul_pow]
      simp [cs.simple_mul_simple_pow]
    simp [h1]
  · have h1 : cs.wordProd (CoxeterSystem.alternatingWord i j (2 * M i j)) = 1 := by
      rw [cs.prod_alternatingWord_eq_mul_pow]
      simp [cs.simple_mul_simple_pow]
    simp only [h1, mul_one, inv_one, Equiv.Perm.one_apply]
    rw [count_leftInvSeq_braid_even, add_zero]

/-- The homomorphism `U : W → Perm (W × ℤ/2)` of Lusztig, Prop. 1.5. -/
noncomputable def φ : W →* Equiv.Perm (W × ZMod 2) := cs.lift ⟨U cs, isLiftable cs⟩

theorem φ_wordProd (ω : List B) : φ cs (cs.wordProd ω) = Φ cs ω := by
  simp only [φ, CoxeterSystem.wordProd, map_list_prod, List.map_map, Φ]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [cs.lift_apply_simple]

/-- Lusztig's sign `η(w, t)`, written additively. -/
noncomputable def N (w t : W) : ZMod 2 := (φ cs w (w⁻¹ * t * w, 0)).2

theorem N_wordProd (ω : List B) (t : W) :
    N cs (cs.wordProd ω) t = (((cs.leftInvSeq ω).count t : ℕ) : ZMod 2) := by
  simp [N, φ_wordProd, Φ_apply, mul_assoc]

theorem φ_apply (w y : W) (ε : ZMod 2) :
    φ cs w (y, ε) = (w * y * w⁻¹, ε + N cs w (w * y * w⁻¹)) := by
  obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
  rw [φ_wordProd, Φ_apply, N_wordProd]

theorem N_mul (u v t : W) : N cs (u * v) t = N cs u t + N cs v (u⁻¹ * t * u) := by
  have h := φ_apply cs (u * v) ((u * v)⁻¹ * t * (u * v)) 0
  rw [map_mul, Equiv.Perm.mul_apply, φ_apply, φ_apply] at h
  have e1 : v * ((u * v)⁻¹ * t * (u * v)) * v⁻¹ = u⁻¹ * t * u := by group
  have e2 : u * (u⁻¹ * t * u) * u⁻¹ = t := by group
  have e3 : u * v * ((u * v)⁻¹ * t * (u * v)) * (u * v)⁻¹ = t := by group
  rw [e1, e2, e3] at h
  have := congrArg Prod.snd h
  simp only [zero_add] at this
  rw [← this]; ring

theorem N_one (t : W) : N cs 1 t = 0 := by
  simpa using N_wordProd cs [] t

theorem N_self_of_isReflection {t : W} (ht : cs.IsReflection t) : N cs t t = 1 := by
  obtain ⟨x, i, rfl⟩ := ht
  set r := x * cs.simple i * x⁻¹
  have hs : N cs (cs.simple i) (cs.simple i) = 1 := by
    have := N_wordProd cs [i] (cs.simple i)
    simpa [CoxeterSystem.leftInvSeq] using this
  have h1 := N_mul cs x (cs.simple i * x⁻¹) r
  have h2 := N_mul cs (cs.simple i) x⁻¹ (x⁻¹ * r * x)
  have h3 := N_mul cs x x⁻¹ r
  have e1 : x⁻¹ * r * x = cs.simple i := by simp [r, mul_assoc]
  have e2 : (cs.simple i)⁻¹ * cs.simple i * cs.simple i = cs.simple i := by simp
  rw [e1] at h2
  rw [e2] at h2
  rw [e1, mul_inv_cancel, N_one] at h3
  rw [show x * (cs.simple i * x⁻¹) = r by simp [r, mul_assoc], e1, h2, hs] at h1
  rw [h1, add_left_comm, ← h3, add_zero]

/-- Strong exchange (Lusztig 2.2 (iii) ⇒ (ii)): if `t` is a reflection with `l(tw) < l(w)`,
then `t` occurs in the left inversion sequence of every word for `w`. -/
theorem mem_leftInvSeq_of_length_lt {t : W} (ht : cs.IsReflection t) (ω : List B)
    (hlt : cs.length (t * cs.wordProd ω) < cs.length (cs.wordProd ω)) :
    t ∈ cs.leftInvSeq ω := by
  by_contra hmem
  have h0 : N cs (cs.wordProd ω) t = 0 := by
    rw [N_wordProd, List.count_eq_zero_of_not_mem hmem]; simp
  have h1 : N cs (t * cs.wordProd ω) t = 1 := by
    rw [N_mul, N_self_of_isReflection cs ht, ht.inv, ht.mul_self, one_mul, h0, add_zero]
  obtain ⟨ω', hω', hω'eq⟩ := cs.exists_isReduced (t * cs.wordProd ω)
  rw [hω'eq, N_wordProd] at h1
  have hpos : t ∈ cs.leftInvSeq ω' := by
    apply List.count_pos_iff.mp
    rcases Nat.eq_zero_or_pos ((cs.leftInvSeq ω').count t) with h | h
    · rw [h] at h1; exact absurd h1 (by decide)
    · exact h
  have hinv := (cs.isLeftInversion_of_mem_leftInvSeq hω' hpos).2
  rw [← hω'eq, ← mul_assoc, ht.mul_self, one_mul] at hinv
  omega

end Lusztig.HeckeUnequal.TitsAction

open Lusztig.HeckeUnequal.TitsAction in
theorem solution {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
    (w : W) (s : B) (hs : cs.length (cs.simple s * w) = cs.length w - 1)
    (ω : List B) (hω : cs.IsReduced ω) (hw : w = cs.wordProd ω) :
    ∃ j : ℕ, j < ω.length ∧
      cs.simple s * cs.wordProd (ω.take j) = cs.wordProd (ω.take (j + 1)) := by
  subst hw
  have hlt : cs.length (cs.simple s * cs.wordProd ω) < cs.length (cs.wordProd ω) := by
    have hne := cs.length_simple_mul_ne (cs.wordProd ω) s
    omega
  have hmem := mem_leftInvSeq_of_length_lt cs (cs.isReflection_simple s) ω hlt
  obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hmem
  rw [cs.length_leftInvSeq] at hj
  refine ⟨j, hj, ?_⟩
  rw [cs.getElem_leftInvSeq ω j hj] at hjeq
  rw [List.take_succ_eq_append_getElem hj, cs.wordProd_append, cs.wordProd_singleton, ← hjeq]
  group
