-- Prove2me | solution 2 for OAI.CirculantHadamard.order_even_of_sign_norm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:15:13.770188+00:00
-- url     : https://prove2.me/submissions/4fa854c3-7ab0-44e7-bdb1-31712634b976

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/OrderSquareEven.lean:L52-L67
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.order_even_of_sign_norm. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm

-- ---- from OAI.LinearAlgebra.CirculantHadamard.CyclicRing ----
namespace OAI

universe uR uG

/-! The finite cyclic group ring, with coefficient conjugation and index reversal. -/

namespace CirculantHadamard.CyclicRing

open scoped BigOperators

section Convolution

variable {R : Type uR} {G : Type uG} [Semiring R] [AddCommGroup G] [Fintype G]

end Convolution

theorem mul_apply {R : Type uR} [Semiring R] {n : ℕ} [NeZero n]
    (f g : Elem R n) (a : ZMod n) : (f * g).coeff a = ∑ j, f.coeff j * g.coeff (a - j) :=
  group_mul_apply f g a

theorem mul_ringStar_apply {R : Type uR} [Semiring R] [StarRing R]
    {n : ℕ} [NeZero n] (f : Elem R n) (a : ZMod n) :
    (f * ringStar f).coeff a = ∑ j, f.coeff j * star (f.coeff (j - a)) := by
  simp only [mul_apply, ringStar_apply, neg_sub]

end CirculantHadamard.CyclicRing

end OAI

-- ---- from OAI.LinearAlgebra.CirculantHadamard.OrderSquareEven ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uIota

/-!
# Square and even order from actual circulant sign rows

Augmentation of the cyclic norm identity gives an integer square. A
nonidentity correlation is a zero sum of signs; reduction modulo two makes
its number of summands even. Both conclusions follow from the actual real
circulant Hadamard matrix predicate.
-/

namespace CirculantHadamard

open scoped BigOperators

private theorem even_card_of_sign_sum_zero {ι : Type uIota} [Fintype ι]
    (f : ι → ℤ) (hsign : ∀ i, IsSign (f i)) (hsum : ∑ i, f i = 0) :
    Even (Fintype.card ι) := by
  classical
  let φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  have hcast (i : ι) : φ (f i) = 1 := by
    rcases hsign i with h | h
    · rw [h, map_one]
    · rw [h, map_neg, map_one]
      exact ZMod.neg_eq_self_mod_two (1 : ZMod 2)
  have hcard : (Fintype.card ι : ZMod 2) = 0 := by
    have h := congrArg φ hsum
    simpa only [map_sum, hcast, map_zero, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] using h
  exact even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff _ _).mp hcard)

/-- A nonidentity norm coefficient is a zero sum of exactly `n` signs. -/
theorem order_even_of_sign_norm {n : ℕ} [NeZero n] (hn : 1 < n)
    (f : CyclicRing.Elem ℤ n) (hsign : CyclicSignRow f)
    (hnorm : f * CyclicRing.ringStar f = CyclicRing.scalar n (n : ℤ)) :
    Even n := by
  classical
  let : Fact (1 < n) := ⟨hn⟩
  have hcorr : (∑ a : ZMod n, f.coeff a * f.coeff (a - 1)) = 0 := by
    have h := congrArg (fun g : CyclicRing.Elem ℤ n => g.coeff 1) hnorm
    simpa only [CyclicRing.mul_ringStar_apply, star_trivial, CyclicRing.scalar_apply,
      ite_eq_right (one_ne_zero : (1 : ZMod n) ≠ 0)] using h
  have heven := even_card_of_sign_sum_zero (fun a : ZMod n => f.coeff a * f.coeff (a - 1))
    (fun a => by
      rcases hsign a with ha | ha <;> rcases hsign (a - 1) with hb | hb <;>
        simp [IsSign, ha, hb]) hcorr
  simpa only [ZMod.card] using heven

end CirculantHadamard

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.CirculantHadamard.order_even_of_sign_norm := @_root_.OAI.CirculantHadamard.order_even_of_sign_norm
