-- Prove2me | solution 1 for OAI.Erdos970.ErdosHyperbolaError.normalized_spectral_error_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:43:30.361208+00:00
-- url     : https://prove2.me/submissions/428e30cb-3ad6-429e-bbea-c9060372f2d0

import Mathlib
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
import Definitions.Def_OAIQ247J002
import Definitions.Def_OAIQ247J003

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PairCollisionCount
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators ComplexConjugate

namespace ErdosKloosterman

attribute [local instance] Classical.decEq

theorem sum_swap {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (a b : R) : sum ψ a b = sum ψ b a := by
  have h := Equiv.sum_comp (Equiv.inv Rˣ) (fun u : Rˣ => ψ (a * (u : R) + b * (↑u⁻¹ : R)))
  simpa only [Equiv.inv_apply, inv_inv, add_comm, sum] using h.symm

theorem sum_unit_scale {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (a b : R) (c : Rˣ) :
    sum ψ (a * c) (b * (↑c⁻¹ : R)) = sum ψ a b := by
  have h := Equiv.sum_comp (Equiv.mulLeft c)
    (fun u : Rˣ => ψ (a * (u : R) + b * (↑u⁻¹ : R)))
  simpa only [sum, Equiv.coe_mulLeft, mul_inv_rev, Units.val_mul,
    mul_assoc, mul_comm, mul_left_comm] using h

theorem sum_ringEquiv {R S : Type*} [CommRing R] [Fintype R] [CommRing S] [Fintype S]
    (e : R ≃+* S) (ψ : AddChar S ℂ) (a b : R) :
    sum (ψ.compAddMonoidHom e.toAddMonoidHom) a b = sum ψ (e a) (e b) := by
  have h := Equiv.sum_comp (Units.mapEquiv e.toMulEquiv).toEquiv
    (fun u : Sˣ => ψ (e a * (u : S) + e b * (↑u⁻¹ : S)))
  simpa [sum, ← map_inv] using h

theorem sum_zero_zero {R : Type*} [CommRing R] [Fintype R] (ψ : AddChar R ℂ) :
    sum ψ 0 0 = Fintype.card Rˣ := by simp [sum]

end ErdosKloosterman

end

section

open scoped BigOperators

namespace ErdosKloosterman

attribute [local instance] Classical.decEq

theorem sum_product {R S : Type*} [CommRing R] [CommRing S]
    [Fintype R] [Fintype S] (ψ : AddChar R ℂ) (φ : AddChar S ℂ)
    (a b : R × S) :
    sum (productChar ψ φ) a b = sum ψ a.1 b.1 * sum φ a.2 b.2 := by
  let : DecidableEq (R × S) := Classical.decEq _
  let e : (R × S)ˣ ≃ Rˣ × Sˣ :=
    { toFun := fun u => (Units.map (RingHom.fst R S).toMonoidHom u,
        Units.map (RingHom.snd R S).toMonoidHom u)
      invFun := fun u => ⟨((u.1 : R),(u.2 : S)), ((↑u.1⁻¹ : R),(↑u.2⁻¹ : S)),
        by ext <;> simp, by ext <;> simp⟩
      left_inv := fun u => by apply Units.ext; rfl
      right_inv := fun u => by apply Prod.ext <;> apply Units.ext <;> rfl }
  have h := Equiv.sum_comp e.symm
    (fun u : (R × S)ˣ => productChar ψ φ (a * (u : R × S) + b * (↑u⁻¹ : R × S)))
  calc
    _ = ∑ u : Rˣ, ∑ v : Sˣ,
        ψ (a.1 * (u : R) + b.1 * (↑u⁻¹ : R)) *
          φ (a.2 * (v : S) + b.2 * (↑v⁻¹ : S)) := by
      simpa [sum, Fintype.sum_prod_type, productChar, e] using! h.symm
    _ = _ := by
      simp only [sum, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

theorem sum_product_ringEquiv {T R S : Type*}
    [CommRing T] [CommRing R] [CommRing S] [Fintype T] [Fintype R] [Fintype S]
    (e : T ≃+* R × S) (ψ : AddChar R ℂ) (φ : AddChar S ℂ) (a b : T) :
    sum ((productChar ψ φ).compAddMonoidHom e.toAddMonoidHom) a b =
      sum ψ (e a).1 (e b).1 * sum φ (e a).2 (e b).2 := by
  rw [sum_ringEquiv, sum_product]

end ErdosKloosterman

end

section

namespace ErdosKloosterman.PrimePower

variable {R : Type*} [CommRing R]

theorem phase_shift (a b : R) (u : Rˣ) (t : R) (ht : t^2 = 0) :
    a * (shiftUnit u t ht : R) + b * (↑(shiftUnit u t ht)⁻¹ : R) =
      a * (u : R) + b * (↑u⁻¹ : R) + t * (a - b * (↑u⁻¹ : R)^2) := by
  rw [shiftUnit_val, shiftUnit_inv_val]
  ring

end ErdosKloosterman.PrimePower

end

section

open scoped BigOperators

namespace ErdosKloosterman

variable {F : Type*} [Field F]

theorem pair_eq_or_swap {u v z w : F}
    (hs : u + v = z + w) (hp : u * v = z * w) :
    (u = z ∧ v = w) ∨ (u = w ∧ v = z) := by
  have h : (u - z) * (u - w) = 0 := by
    linear_combination u * hs - hp
  rcases mul_eq_zero.mp h with h | h
  · left
    have hu := sub_eq_zero.mp h
    exact ⟨hu, by rw [hu] at hs; exact add_left_cancel hs⟩
  · right
    have hu := sub_eq_zero.mp h
    exact ⟨hu, by rw [hu, add_comm z w] at hs; exact add_left_cancel hs⟩

theorem inverse_pair_collision (u v z w : Fˣ)
    (hs : (u : F) + v = z + w)
    (hi : (↑u⁻¹ : F) + ↑v⁻¹ = ↑z⁻¹ + ↑w⁻¹) :
    ((u : F) + v = 0 ∧ (z : F) + w = 0) ∨
      (u = z ∧ v = w) ∨ (u = w ∧ v = z) := by
  by_cases hz : (u : F) + v = 0
  · exact Or.inl ⟨hz, hs.symm.trans hz⟩
  right
  have hid : (u : F)⁻¹ + (v : F)⁻¹ = (z : F)⁻¹ + (w : F)⁻¹ := by
    simpa only [Units.val_inv_eq_inv_val] using hi
  have hp : (u : F) * v = z * w := by
    have hzero : ((u : F) + v) * ((z : F) * w - (u : F) * v) = 0 := by
      field_simp at hid
      linear_combination hid - ((u : F) * v) * hs
    have hd := (mul_eq_zero.mp hzero).resolve_left hz
    exact (sub_eq_zero.mp hd).symm
  rcases pair_eq_or_swap hs hp with ⟨huz, hvw⟩ | ⟨huw, hvz⟩
  · exact Or.inl ⟨Units.ext huz, Units.ext hvw⟩
  · exact Or.inr ⟨Units.ext huw, Units.ext hvz⟩

end ErdosKloosterman

end

section

open scoped BigOperators

namespace ErdosKloosterman

attribute [local instance] Classical.decEq

variable (F : Type*) [Field F] [Fintype F]

theorem pairCollisions_card_le :
    (pairCollisions F).card ≤ 3 * (Fintype.card Fˣ) ^ 2 := by
  let zeroFamily := (Finset.univ : Finset (Fˣ × Fˣ)).image
    (fun p => ((p.1, -p.1), (p.2, -p.2)))
  let diagonalFamily := (Finset.univ : Finset (Fˣ × Fˣ)).image (fun p => (p, p))
  let swappedFamily := (Finset.univ : Finset (Fˣ × Fˣ)).image
    (fun p => (p, (p.2, p.1)))
  have cover : pairCollisions F ⊆ zeroFamily ∪ diagonalFamily ∪ swappedFamily := by
    rintro ⟨⟨u,v⟩,⟨z,w⟩⟩ hx
    obtain ⟨hs, hi⟩ := (Finset.mem_filter.mp hx).2
    rcases inverse_pair_collision u v z w hs hi with hz | hd | he
    · have hv : v = -u := by
        apply Units.ext
        change (v : F) = -(u : F)
        linear_combination hz.1
      have hw : w = -z := by
        apply Units.ext
        change (w : F) = -(z : F)
        linear_combination hz.2
      subst v; subst w
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨(u,z), Finset.mem_univ _, rfl⟩))
    · rcases hd with ⟨huz, hvw⟩
      subst z; subst w
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨(u,v), Finset.mem_univ _, rfl⟩))
    · rcases he with ⟨huw, hvz⟩
      subst w; subst z
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨(u,v), Finset.mem_univ _, rfl⟩)
  have hz : zeroFamily.card ≤ (Fintype.card Fˣ)^2 := by
    simpa only [Finset.card_univ, Fintype.card_prod, pow_two] using
      (Finset.card_image_le (s := (Finset.univ : Finset (Fˣ × Fˣ)))
        (f := fun p : Fˣ × Fˣ => ((p.1, -p.1), (p.2, -p.2))))
  have hd : diagonalFamily.card ≤ (Fintype.card Fˣ)^2 := by
    simpa only [Finset.card_univ, Fintype.card_prod, pow_two] using
      (Finset.card_image_le (s := (Finset.univ : Finset (Fˣ × Fˣ)))
        (f := fun p : Fˣ × Fˣ => (p,p)))
  have hs : swappedFamily.card ≤ (Fintype.card Fˣ)^2 := by
    simpa only [Finset.card_univ, Fintype.card_prod, pow_two] using
      (Finset.card_image_le (s := (Finset.univ : Finset (Fˣ × Fˣ)))
        (f := fun p : Fˣ × Fˣ => (p,(p.2,p.1))))
  have h1 := Finset.card_union_le zeroFamily diagonalFamily
  have h2 := Finset.card_union_le (zeroFamily ∪ diagonalFamily) swappedFamily
  have h3 := Finset.card_le_card cover
  omega

end ErdosKloosterman

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_StationaryPhase
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosKloosterman.PrimePower

variable {R : Type*} [CommRing R] [Fintype R]

attribute [local instance] Classical.decEq

private theorem sum_shift (ψ : AddChar R ℂ) (a b q : R) (hq : q^2 = 0) (z : R) :
    sum ψ a b = ∑ u : Rˣ,
      ψ (a * (u : R) + b * (↑u⁻¹ : R)) *
        ψ (z * (q * (a - b * (↑u⁻¹ : R)^2))) := by
  have ht : (q*z)^2 = 0 := by rw [mul_pow, hq, zero_mul]
  have he := Equiv.sum_comp (shiftEquiv (q*z) ht)
    (fun u : Rˣ => ψ (a * (u : R) + b * (↑u⁻¹ : R)))
  unfold sum
  rw [← he]
  apply Finset.sum_congr rfl
  intro u _
  change ψ (a * (shiftUnit u (q*z) ht : R) +
    b * (↑(shiftUnit u (q*z) ht)⁻¹ : R)) = _
  rw [phase_shift, AddChar.map_add_eq_mul]
  congr 1
  congr 1
  ring

theorem stationary_phase_identity (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (a b q : R) (hq : q^2 = 0) :
    sum ψ a b = ∑ u ∈ stationaryUnits q a b,
      ψ (a * (u : R) + b * (↑u⁻¹ : R)) := by
  have hcard : (Fintype.card R : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hcard
  calc
    (Fintype.card R : ℂ) * sum ψ a b = ∑ _z : R, sum ψ a b := by simp
    _ = ∑ z : R, ∑ u : Rˣ,
        ψ (a * (u : R) + b * (↑u⁻¹ : R)) *
          ψ (z * (q * (a - b * (↑u⁻¹ : R)^2))) := by
      apply Finset.sum_congr rfl
      intro z _
      exact sum_shift ψ a b q hq z
    _ = ∑ u : Rˣ, ψ (a * (u : R) + b * (↑u⁻¹ : R)) *
        (∑ z : R, ψ (z * (q * (a - b * (↑u⁻¹ : R)^2)))) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = _ := by
      simp_rw [AddChar.sum_mulShift _ hψ]
      rw [Finset.mul_sum]
      simp [stationaryUnits, Finset.sum_filter, mul_comm]

theorem norm_sum_le_stationary_card (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (a b q : R) (hq : q^2 = 0) :
    ‖sum ψ a b‖ ≤ (stationaryUnits q a b).card := by
  rw [stationary_phase_identity ψ hψ a b q hq]
  calc
    _ ≤ ∑ u ∈ stationaryUnits q a b, ‖ψ (a * (u : R) + b * (↑u⁻¹ : R))‖ :=
      norm_sum_le _ _
    _ = _ := by simp [AddChar.norm_apply]

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimePowerStationarity
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosKloosterman.PrimePower

theorem stationary_iff_quadratic {R : Type*} [CommRing R] (q a b : R) (u : Rˣ) :
    q * (a - b * (↑u⁻¹ : R)^2) = 0 ↔ q * (a * (u : R)^2 - b) = 0 := by
  have he : q * (a - b * (↑u⁻¹ : R)^2) * (u : R)^2 =
      q * (a * (u : R)^2 - b) := by
    calc
      _ = q * a * (u : R)^2 - q * b * ((↑u⁻¹ : R) * u)^2 := by ring
      _ = _ := by simp <;> ring
  rw [← he]
  change _ ↔ _ * ((u^2 : Rˣ) : R) = 0
  exact (Units.mul_left_eq_zero (u^2)).symm

theorem mul_annihilator_iff (n d : ℕ) [NeZero (n*d)] (hn : 0 < n) (x : ZMod (n*d)) :
    (n : ZMod (n*d)) * x = 0 ↔ (x.val : ZMod d) = 0 := by
  nth_rw 1 [← x.natCast_zmod_val]
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff]
  exact Nat.mul_dvd_mul_iff_left hn

theorem power_shift_square_zero (p r s : ℕ) (hsr : s ≤ r) :
    ((p^r : ℕ) : ZMod (p^(r+s)))^2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff, ← pow_mul]
  exact pow_dvd_pow p (by omega)

theorem standard_norm_le_stationary_card (p r s : ℕ) [NeZero (p^(r+s))] (hsr : s ≤ r)
    (h k : ℤ) :
    ‖standardSum (p^(r+s)) h k‖ ≤
      (stationaryUnits ((p^r : ℕ) : ZMod (p^(r+s))) (h : ZMod (p^(r+s))) k).card := by
  exact norm_sum_le_stationary_card (R := ZMod (p^(r+s)))
    (ZMod.stdAddChar (N := p^(r+s))) (ZMod.isPrimitive_stdAddChar (p^(r+s)))
    (h : ZMod (p^(r+s))) (k : ZMod (p^(r+s))) ((p^r : ℕ) : ZMod (p^(r+s))) (power_shift_square_zero p r s hsr)

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ResidueFibres
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosKloosterman.PrimePower

attribute [local instance] Classical.decEq

private theorem card_mul_fibre {A B : Type*} [AddGroup A] [Fintype A]
    [AddGroup B] [Fintype B] (f : A →+ B) (hf : Function.Surjective f) (b : B) :
    Fintype.card B * ((Finset.univ : Finset A).filter fun x => f x = b).card =
      Fintype.card A := by
  calc
    _ = ∑ _y : B, ((Finset.univ : Finset A).filter fun x => f x = b).card := by simp
    _ = ∑ y : B, ((Finset.univ : Finset A).filter fun x => f x = y).card := by
      apply Finset.sum_congr rfl
      intro y _
      exact AddMonoidHom.card_fiber_eq_of_mem_range f (hf b) (hf y)
    _ = _ := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      simp

theorem reduction_fibre_card (n d : ℕ) [NeZero n] [NeZero d] (y : ZMod d) :
    ((Finset.univ : Finset (ZMod (n*d))).filter fun x => reduction n d x = y).card = n := by
  have hf : Function.Surjective (reduction n d) :=
    ZMod.castHom_surjective (dvd_mul_left d n)
  have hc := card_mul_fibre (reduction n d).toAddMonoidHom hf y
  simp only [ZMod.card] at hc
  apply Nat.eq_of_mul_eq_mul_left (NeZero.pos d)
  convert hc.trans (Nat.mul_comm n d) using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem reduction_preimage_card (n d : ℕ) [NeZero n] [NeZero d] (S : Finset (ZMod d)) :
    ((Finset.univ : Finset (ZMod (n*d))).filter fun x => reduction n d x ∈ S).card =
      S.card * n := by
  rw [← Finset.sum_card_fiberwise_eq_card_filter]
  simp only [reduction_fibre_card, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_StationaryFibres
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman.PrimePower

attribute [local instance] Classical.decEq

theorem reduction_apply_val (n d : ℕ) [NeZero n] [NeZero d] (x : ZMod (n*d)) :
    reduction n d x = (x.val : ZMod d) := by
  nth_rw 1 [← x.natCast_zmod_val]
  simp [reduction]

theorem mem_stationary_iff_reduction (n d : ℕ) [NeZero n] [NeZero d]
    (a b : ZMod (n*d)) (u : (ZMod (n*d))ˣ) :
    u ∈ stationaryUnits (n : ZMod (n*d)) a b ↔
      reduction n d (u : ZMod (n*d)) ∈
        quadraticUnitRoots d (reduction n d a) (reduction n d b) := by
  have hu : IsUnit (reduction n d (u : ZMod (n*d))) :=
    (u.isUnit).map (reduction n d)
  simp only [stationaryUnits, Finset.mem_filter, Finset.mem_univ, true_and,
    quadraticUnitRoots, hu]
  rw [stationary_iff_quadratic, mul_annihilator_iff n d (NeZero.pos n),
    ← reduction_apply_val]
  simp only [map_sub, map_mul, map_pow, sub_eq_zero]

theorem stationary_card_le_root_card_mul (n d : ℕ) [NeZero n] [NeZero d]
    (a b : ZMod (n*d)) :
    (stationaryUnits (n : ZMod (n*d)) a b).card ≤
      (quadraticUnitRoots d (reduction n d a) (reduction n d b)).card * n := by
  let S := quadraticUnitRoots d (reduction n d a) (reduction n d b)
  rw [← reduction_preimage_card n d S]
  apply Finset.card_le_card_of_injOn (fun u : (ZMod (n*d))ˣ => (u : ZMod (n*d)))
  · intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (mem_stationary_iff_reduction n d a b u).mp hu⟩
  · intro u _ v _ huv
    exact Units.val_injective huv

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_OddPrimeRoots
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman.PrimePower

attribute [local instance] Classical.decEq

theorem isUnit_iff_primeReduction_ne_zero (p s : ℕ) [Fact p.Prime] (hs : 0 < s)
    (x : ZMod (p^s)) : IsUnit x ↔ primeReduction p s hs x ≠ 0 := by
  have hx : primeReduction p s hs x = (x.val : ZMod p) := by
    rw [primeReduction, ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [hx, ne_eq, ZMod.natCast_eq_zero_iff]
  nth_rw 1 [← x.natCast_zmod_val]
  exact ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hs

theorem eq_or_neg_of_sq_eq_odd (p s : ℕ) [Fact p.Prime] (hs : 0 < s) (hp2 : p ≠ 2)
    (x y : ZMod (p^s)) (hy : IsUnit y) (hxy : x^2 = y^2) : x = y ∨ x = -y := by
  let f := primeReduction p s hs
  have hyf : f y ≠ 0 := (isUnit_iff_primeReduction_ne_zero p s hs y).mp hy
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hp1 | hp2'
    · exact (Fact.out : p.Prime).ne_one hp1
    · exact hp2 hp2'
  have hfactor : (x-y)*(x+y) = 0 := by linear_combination hxy
  have hunits : IsUnit (x-y) ∨ IsUnit (x+y) := by
    rw [isUnit_iff_primeReduction_ne_zero p s hs,
      isUnit_iff_primeReduction_ne_zero p s hs]
    change f (x-y) ≠ 0 ∨ f (x+y) ≠ 0
    by_cases hm : f (x-y) = 0
    · right
      have he : f x = f y := sub_eq_zero.mp (by simpa only [map_sub] using hm)
      rw [map_add, he, ← two_mul]
      exact mul_ne_zero htwo hyf
    · exact Or.inl hm
  rcases hunits with hm | hp
  · right
    exact eq_neg_of_add_eq_zero_left ((hm.mul_right_eq_zero).mp hfactor)
  · left
    exact sub_eq_zero.mp ((hp.mul_left_eq_zero).mp hfactor)

theorem quadraticUnitRoots_card_le_two (p s : ℕ) [Fact p.Prime] (hs : 0 < s)
    (hp2 : p ≠ 2) (a b : ZMod (p^s)) (ha : IsUnit a) :
    (quadraticUnitRoots (p^s) a b).card ≤ 2 := by
  by_cases hempty : (quadraticUnitRoots (p^s) a b).Nonempty
  · obtain ⟨y, hy⟩ := hempty
    obtain ⟨hyunit, hyeq⟩ := (Finset.mem_filter.mp hy).2
    have hsubset : quadraticUnitRoots (p^s) a b ⊆ {y,-y} := by
      intro x hx
      obtain ⟨_, hxeq⟩ := (Finset.mem_filter.mp hx).2
      have hsq : x^2 = y^2 := by
        rcases ha with ⟨u, rfl⟩
        have h := congrArg (fun z : ZMod (p^s) => (↑u⁻¹ : ZMod (p^s)) * z)
          (hxeq.trans hyeq.symm)
        simpa only [Units.inv_mul_cancel_left] using h
      rcases eq_or_neg_of_sq_eq_odd p s hs hp2 x y hyunit hsq with he | he
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he))
    exact (Finset.card_le_card hsubset).trans (by simpa using Finset.card_insert_le y ({-y} : Finset (ZMod (p^s))))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
    simp

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_TwoPowerDivisibility
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman.PrimePower

theorem two_pow_dvd_of_four_not_dvd (s : ℕ) (a b : ℤ) (ha : ¬4 ∣ a)
    (hab : (2 : ℤ)^(s+1) ∣ a*b) : (2 : ℤ)^s ∣ b := by
  have hp : Prime (2 : ℤ) := by norm_num
  by_cases htwo : (2 : ℤ) ∣ a
  · obtain ⟨c, rfl⟩ := htwo
    have hc : ¬(2 : ℤ) ∣ c := by
      rintro ⟨d, rfl⟩
      exact ha ⟨d, by ring⟩
    have hcan : (2 : ℤ)^s ∣ c*b := by
      apply (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp
      simpa only [pow_succ', mul_assoc] using hab
    exact hp.pow_dvd_of_dvd_mul_left s hc hcan
  · exact (pow_dvd_pow (2 : ℤ) (Nat.le_succ s)).trans
      (hp.pow_dvd_of_dvd_mul_left (s+1) htwo hab)

theorem two_power_square_congruence (s : ℕ) (x y : ℤ) (hy : ¬(2 : ℤ) ∣ y)
    (hxy : (2 : ℤ)^(s+1) ∣ x^2-y^2) :
    (2 : ℤ)^s ∣ x-y ∨ (2 : ℤ)^s ∣ x+y := by
  have hproduct : (2 : ℤ)^(s+1) ∣ (x-y)*(x+y) := by
    convert hxy using 1 <;> first | rfl | ring
  by_cases hm : (4 : ℤ) ∣ x-y
  · have hp : ¬(4 : ℤ) ∣ x+y := by
      intro hp
      have h2y : (4 : ℤ) ∣ 2*y := by
        have he : (x+y)-(x-y) = 2*y := by ring
        simpa only [he] using dvd_sub hp hm
      apply hy
      apply (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp
      exact h2y
    exact Or.inl (two_pow_dvd_of_four_not_dvd s (x+y) (x-y) hp
      (by simpa only [mul_comm] using hproduct))
  · exact Or.inr (two_pow_dvd_of_four_not_dvd s (x-y) (x+y) hm hproduct)

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_TwoPrimeRoots
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman.PrimePower

attribute [local instance] Classical.decEq

theorem two_sq_eq_reduction (s : ℕ) (x y : ZMod (2 * 2^s)) (hy : IsUnit y)
    (hxy : x^2 = y^2) :
    reduction 2 (2^s) x = reduction 2 (2^s) y ∨
      reduction 2 (2^s) x = -reduction 2 (2^s) y := by
  have hycast : IsUnit (y.val : ZMod (2*2^s)) := by
    simpa only [ZMod.natCast_zmod_val] using hy
  have hcop : y.val.Coprime 2 :=
    Nat.Coprime.of_dvd_right (dvd_mul_right 2 (2^s))
      ((ZMod.isUnit_iff_coprime y.val (2*2^s)).mp hycast)
  have hyodd : ¬(2 : ℤ) ∣ (y.val : ℤ) := by
    exact_mod_cast (Nat.prime_two.coprime_iff_not_dvd.mp hcop.symm)
  have hdiv : (2 : ℤ)^(s+1) ∣ (x.val : ℤ)^2-(y.val : ℤ)^2 := by
    have hz : (((x.val : ℤ)^2-(y.val : ℤ)^2 : ℤ) : ZMod (2*2^s)) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      exact sub_eq_zero.mpr hxy
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2*2^s)).mp hz
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, pow_succ'] using h
  rcases two_power_square_congruence s (x.val : ℤ) (y.val : ℤ) hyodd hdiv with hm | hp
  · left
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((x.val : ℤ)-(y.val : ℤ)) (2^s)).mpr (by exact_mod_cast hm)
    push_cast at hz
    rw [reduction_apply_val, reduction_apply_val]
    exact sub_eq_zero.mp hz
  · right
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((x.val : ℤ)+(y.val : ℤ)) (2^s)).mpr (by exact_mod_cast hp)
    push_cast at hz
    rw [reduction_apply_val, reduction_apply_val]
    exact eq_neg_of_add_eq_zero_left hz

theorem quadraticUnitRoots_card_le_four_twice (s : ℕ) (a b : ZMod (2*2^s))
    (ha : IsUnit a) : (quadraticUnitRoots (2*2^s) a b).card ≤ 4 := by
  by_cases hempty : (quadraticUnitRoots (2*2^s) a b).Nonempty
  · obtain ⟨y, hy⟩ := hempty
    obtain ⟨hyunit, hyeq⟩ := (Finset.mem_filter.mp hy).2
    let S : Finset (ZMod (2^s)) := {reduction 2 (2^s) y, -reduction 2 (2^s) y}
    have hsubset : quadraticUnitRoots (2*2^s) a b ⊆
        Finset.univ.filter (fun x => reduction 2 (2^s) x ∈ S) := by
      intro x hx
      obtain ⟨_, hxeq⟩ := (Finset.mem_filter.mp hx).2
      have hsq : x^2 = y^2 := by
        rcases ha with ⟨u, rfl⟩
        have h := congrArg (fun z : ZMod (2*2^s) => (↑u⁻¹ : ZMod (2*2^s)) * z)
          (hxeq.trans hyeq.symm)
        simpa only [Units.inv_mul_cancel_left] using h
      have hc := two_sq_eq_reduction s x y hyunit hsq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [S, Finset.mem_insert,
        Finset.mem_singleton] using hc⟩
    have hScard : S.card ≤ 2 := by
      simpa only [Finset.card_singleton] using
        Finset.card_insert_le (reduction 2 (2^s) y) ({-reduction 2 (2^s) y} : Finset _)
    calc
      _ ≤ (Finset.univ.filter (fun x => reduction 2 (2^s) x ∈ S)).card :=
        Finset.card_le_card hsubset
      _ = S.card * 2 := reduction_preimage_card 2 (2^s) S
      _ ≤ 4 := by omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
    simp

theorem quadraticUnitRoots_card_le_four (s : ℕ) (hs : 0 < s) (a b : ZMod (2^s))
    (ha : IsUnit a) : (quadraticUnitRoots (2^s) a b).card ≤ 4 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  have transport (n : ℕ) (hn : n = 2*2^t) [NeZero n]
      (a b : ZMod n) (ha : IsUnit a) : (quadraticUnitRoots n a b).card ≤ 4 := by
    subst n
    exact quadraticUnitRoots_card_le_four_twice t a b ha
  exact transport (2^t.succ) Nat.pow_succ' a b ha

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_PrimitiveThreeQuarters
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman.PrimePower

theorem quadraticUnitRoots_card_le_four_prime_power (p s : ℕ) [Fact p.Prime]
    (hs : 0 < s) (a b : ZMod (p^s)) (ha : IsUnit a) :
    (quadraticUnitRoots (p^s) a b).card ≤ 4 := by
  by_cases hp2 : p = 2
  · subst p
    exact quadraticUnitRoots_card_le_four s hs a b ha
  · exact (quadraticUnitRoots_card_le_two p s hs hp2 a b ha).trans (by decide)

theorem int_frequency_isUnit (p s : ℕ) [Fact p.Prime] (hs : 0 < s) (h : ℤ)
    (hh : (h : ZMod p) ≠ 0) : IsUnit (h : ZMod (p^s)) := by
  apply (isUnit_iff_primeReduction_ne_zero p s hs _).mpr
  simpa only [map_intCast] using hh

theorem primitive_half_bound (p r s : ℕ) [Fact p.Prime] (hs : 0 < s) (hsr : s ≤ r)
    (h k : ℤ) (hhk : (h : ZMod p) ≠ 0 ∨ (k : ZMod p) ≠ 0) :
    ‖standardSum (p^(r+s)) h k‖ ≤ 4 * (p^r : ℕ) := by
  have left (h k : ℤ) (hh : (h : ZMod p) ≠ 0) :
      ‖standardSum (p^(r+s)) h k‖ ≤ 4 * (p^r : ℕ) := by
    have hn := standard_norm_le_stationary_card p r s hsr h k
    have hc := stationary_card_le_root_card_mul (p^r) (p^s)
      (h : ZMod (p^r*p^s)) (k : ZMod (p^r*p^s))
    have hr : (quadraticUnitRoots (p^s)
        (reduction (p^r) (p^s) (h : ZMod (p^r*p^s)))
        (reduction (p^r) (p^s) (k : ZMod (p^r*p^s)))).card ≤ 4 := by
      simpa only [map_intCast] using quadraticUnitRoots_card_le_four_prime_power p s hs
        (h : ZMod (p^s)) (k : ZMod (p^s)) (int_frequency_isUnit p s hs h hh)
    have hc4 := hc.trans (Nat.mul_le_mul_right (p^r) hr)
    have hc4real : ((stationaryUnits ((p^r : ℕ) : ZMod (p^r*p^s))
        (h : ZMod (p^r*p^s)) k).card : ℝ) ≤ 4 * (p^r : ℕ) := by
      exact_mod_cast hc4
    have transport (N : ℕ) [NeZero N] (hN : N = p^r*p^s) :
        ((stationaryUnits ((p^r : ℕ) : ZMod N) (h : ZMod N) k).card : ℝ) ≤
          4 * (p^r : ℕ) := by
      subst N
      exact hc4real
    exact hn.trans (transport (p^(r+s)) (pow_add p r s))
  rcases hhk with hh | hk
  · exact left h k hh
  · have he : standardSum (p^(r+s)) h k = standardSum (p^(r+s)) k h :=
      sum_swap ZMod.stdAddChar (h : ZMod (p^(r+s))) (k : ZMod (p^(r+s)))
    rw [he]
    exact left k h hk

end ErdosKloosterman.PrimePower

end

section

namespace ErdosKloosterman.PrimePower

theorem standardSum_modulus_congr (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N = M) (h k : ℤ) : standardSum N h k = standardSum M h k := by
  subst M
  rfl

theorem ceiling_half_le_three_quarters (p a : ℕ) (hp : 1 ≤ p) (ha : 2 ≤ a) :
    ((p^(a-a/2) : ℕ) : ℝ) ≤ ((p^a : ℕ) : ℝ)^((3 : ℝ)/4) := by
  have hexp : (a-a/2)*4 ≤ a*3 := by omega
  have hnat : (p^(a-a/2))^4 ≤ (p^a)^3 := by
    rw [← pow_mul, ← pow_mul]
    exact Nat.pow_le_pow_right hp hexp
  have hreal : (((p^(a-a/2) : ℕ) : ℝ))^4 ≤ (((p^a : ℕ) : ℝ))^3 := by
    exact_mod_cast hnat
  have he : ((((p^a : ℕ) : ℝ))^((3 : ℝ)/4))^4 = (((p^a : ℕ) : ℝ))^3 := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    norm_num
  rw [← he] at hreal
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 4 ≠ 0)).mp hreal

theorem primitive_three_quarter_bound (p a : ℕ) [Fact p.Prime] (ha : 2 ≤ a)
    (h k : ℤ) (hhk : (h : ZMod p) ≠ 0 ∨ (k : ZMod p) ≠ 0) :
    ‖standardSum (p^a) h k‖ ≤ 4 * ((p^a : ℕ) : ℝ)^((3 : ℝ)/4) := by
  have hs : 0 < a/2 := by omega
  have hsr : a/2 ≤ a-a/2 := by omega
  have he : a-a/2+a/2 = a := by omega
  have hhalf := primitive_half_bound p (a-a/2) (a/2) hs hsr h k hhk
  rw [standardSum_modulus_congr _ (p^a) (congrArg (p^·) he)] at hhalf
  exact hhalf.trans (mul_le_mul_of_nonneg_left
    (ceiling_half_le_three_quarters p a (Fact.out : p.Prime).one_le ha) (by positivity))

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_CharacterChord
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosHyperbolaFourier

theorem characterProgression_factor (N : ℕ) [NeZero N]
    (start step : ZMod N) (J : ℕ) :
    characterProgression N start step J =
      ZMod.stdAddChar start * ∑ j ∈ Finset.range J, (ZMod.stdAddChar step)^j := by
  unfold characterProgression
  simp only [AddChar.map_add_eq_mul, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow,
    Finset.mul_sum]

theorem norm_geom_mul_sub_le_two (z : ℂ) (hz : ‖z‖ = 1) (J : ℕ) :
    ‖∑ j ∈ Finset.range J, z^j‖ * ‖1-z‖ ≤ 2 := by
  rw [← norm_mul, geom_sum_mul_neg]
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖z^J‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

theorem norm_characterProgression_mul_chord (N : ℕ) [NeZero N]
    (start step : ZMod N) (J : ℕ) :
    ‖characterProgression N start step J‖ * ‖1-ZMod.stdAddChar step‖ ≤ 2 := by
  rw [characterProgression_factor, norm_mul, AddChar.norm_apply, one_mul]
  exact norm_geom_mul_sub_le_two _ (AddChar.norm_apply _ _) J

end ErdosHyperbolaFourier

end

section

namespace ErdosHyperbolaFourier

theorem cyclicDistance_pos (N : ℕ) [NeZero N] (step : ZMod N) (hs : step ≠ 0) :
    0 < cyclicDistance N step := by
  have hv : 0 < step.val := Nat.pos_of_ne_zero (fun hv => hs ((ZMod.val_eq_zero step).mp hv))
  exact lt_min hv (Nat.sub_pos_of_lt step.val_lt)

private theorem sine_half_lower (x : ℝ) (hx : 0 ≤ x) (hxhalf : x ≤ 1/2) :
    2*x ≤ Real.sin (Real.pi*x) := by
  have ht : Real.pi*x ≤ Real.pi/2 := by nlinarith [Real.pi_pos]
  have h := Real.mul_le_sin (mul_nonneg Real.pi_pos.le hx) ht
  calc
    _ = (2/Real.pi)*(Real.pi*x) := by field_simp
    _ ≤ _ := h

theorem sine_distance_lower (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    2*min x (1-x) ≤ Real.sin (Real.pi*x) := by
  by_cases hh : x ≤ 1/2
  · rw [min_eq_left (by linarith)]
    exact sine_half_lower x hx hh
  · rw [min_eq_right (by linarith)]
    have h := sine_half_lower (1-x) (by linarith) (by linarith)
    have he : Real.pi*(1-x) = Real.pi-Real.pi*x := by ring
    simpa only [he, Real.sin_pi_sub] using h

theorem exponential_chord_lower (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    4*min x (1-x) ≤ ‖Complex.exp (Complex.I * ((2*Real.pi*x : ℝ) : ℂ))-1‖ := by
  have hs := sine_distance_lower x hx hx1
  have hs0 : 0 ≤ Real.sin (Real.pi*x) :=
    (mul_nonneg (by norm_num) (le_min hx (sub_nonneg.mpr hx1))).trans hs
  rw [Complex.norm_exp_I_mul_ofReal_sub_one,
    show (2*Real.pi*x)/2 = Real.pi*x by ring, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by norm_num) hs0)]
  nlinarith

theorem standard_character_chord_lower (N : ℕ) [NeZero N] (step : ZMod N) :
    4*(cyclicDistance N step : ℝ)/(N : ℝ) ≤ ‖1-ZMod.stdAddChar step‖ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hv : (step.val : ℝ) ≤ N := by exact_mod_cast step.val_lt.le
  have he : ZMod.stdAddChar step =
      Complex.exp (Complex.I * ((2*Real.pi*((step.val : ℝ)/N) : ℝ) : ℂ)) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    congr 1
    push_cast
    ring
  have h := exponential_chord_lower ((step.val : ℝ)/N) (by positivity)
    ((div_le_one hN).mpr hv)
  have hsub : ((N-step.val : ℕ) : ℝ) = (N : ℝ)-step.val := by
    exact Nat.cast_sub step.val_lt.le
  have hmin : min ((step.val : ℝ)/N) (1-(step.val : ℝ)/N) =
      (cyclicDistance N step : ℝ)/(N : ℝ) := by
    rw [show 1-(step.val : ℝ)/N = ((N : ℝ)-step.val)/N by field_simp,
      min_div_div_right hN.le]
    simp only [cyclicDistance, Nat.cast_min, hsub]
  rw [hmin] at h
  rw [he, norm_sub_rev]
  convert h using 1 <;> first | rfl | ring

end ErdosHyperbolaFourier

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_IntervalCuts
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbolaFourier

theorem lowerCut_bounds (x : ℝ) (closed : Bool) :
    x ≤ (lowerCut x closed : ℝ) ∧ (lowerCut x closed : ℝ) ≤ x+1 := by
  have hf := Int.floor_le x
  have hf' := Int.lt_floor_add_one x
  have hc := Int.le_ceil x
  have hc' := Int.ceil_lt_add_one x
  cases closed <;> simp only [lowerCut, Bool.false_eq_true, ite_false, if_false, ite_true, if_true, Int.cast_add,
    Int.cast_one] <;> constructor <;> linarith

theorem upperCut_bounds (x : ℝ) (closed : Bool) :
    x ≤ (upperCut x closed : ℝ) ∧ (upperCut x closed : ℝ) ≤ x+1 :=
  lowerCut_bounds x (!closed)

theorem cut_count_error (x y : ℝ) (hxy : x ≤ y) (lc rc : Bool) :
    |(((upperCut y rc-lowerCut x lc).toNat : ℕ) : ℝ) - (y-x)| ≤ 1 := by
  obtain ⟨hL, hL'⟩ := lowerCut_bounds x lc
  obtain ⟨hU, hU'⟩ := upperCut_bounds y rc
  by_cases hpos : 0 ≤ upperCut y rc-lowerCut x lc
  · have hc : (((upperCut y rc-lowerCut x lc).toNat : ℕ) : ℝ) =
        (upperCut y rc : ℝ)-(lowerCut x lc : ℝ) := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hpos)
      push_cast at h
      exact h
    rw [hc, abs_le]
    constructor <;> linarith
  · have hc : (upperCut y rc-lowerCut x lc).toNat = 0 := Int.toNat_of_nonpos (by omega)
    have hUL : (upperCut y rc : ℝ) ≤ (lowerCut x lc : ℝ) := by exact_mod_cast (by omega : upperCut y rc ≤ lowerCut x lc)
    rw [hc]
    norm_num only [Nat.cast_zero, zero_sub, abs_neg]
    rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
    linarith

end ErdosHyperbolaFourier

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_RealProgressionPoints
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbolaFourier

theorem progressionPoint_injective (a : ℤ) (T : ℕ) (hT : 0 < T) :
    Function.Injective (progressionPoint a T) := by
  intro i j hij
  have hT0 : (T : ℤ) ≠ 0 := by exact_mod_cast hT.ne'
  exact mul_left_cancel₀ hT0 (add_left_cancel hij)

theorem progressionPoints_card (x y : ℝ) (lc rc : Bool) (T : ℕ) (a : ℤ) (hT : 0 < T) :
    (progressionPoints x y lc rc T a).card =
      (upperIndex y T a rc-lowerIndex x T a lc).toNat := by
  unfold progressionPoints
  rw [Finset.card_image_of_injective _ (progressionPoint_injective a T hT), Int.card_Ico]

theorem progressionPoints_count_error (x y : ℝ) (hxy : x ≤ y) (lc rc : Bool)
    (T : ℕ) (a : ℤ) (hT : 0 < T) :
    |((progressionPoints x y lc rc T a).card : ℝ) - (y-x)/(T : ℝ)| ≤ 1 := by
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hlohi : (x-a)/(T : ℝ) ≤ (y-a)/(T : ℝ) :=
    div_le_div_of_nonneg_right (sub_le_sub_right hxy _) hTR.le
  have h := cut_count_error ((x-a)/(T : ℝ)) ((y-a)/(T : ℝ)) hlohi lc rc
  rw [show (y-a)/(T : ℝ)-(x-a)/(T : ℝ) = (y-x)/(T : ℝ) by ring] at h
  rw [progressionPoints_card x y lc rc T a hT]
  exact h

end ErdosHyperbolaFourier

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_DivisorHarmonic
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators

namespace ErdosHyperbola

theorem harmonicWeight_nonneg (N : ℕ) : 0 ≤ harmonicWeight N := by
  unfold harmonicWeight
  positivity

theorem multiple_reciprocal_sum_le (N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·), 1/(n : ℝ)) ≤
      (1/(d : ℝ))*harmonicWeight N := by
  let S := (Finset.Icc 1 N).filter (d ∣ ·)
  let f : ℕ → ℕ := fun n => n/d
  have hi : Set.InjOn f (S : Set ℕ) := by
    intro a ha b hb he
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    calc
      a = d*(a/d) := (Nat.mul_div_cancel' ha').symm
      _ = d*(b/d) := by rw [show a/d = b/d from he]
      _ = b := Nat.mul_div_cancel' hb'
  have hsub : S.image f ⊆ Finset.Icc 1 N := by
    intro j hj
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hnI,hnD⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1,hnN⟩ := Finset.mem_Icc.mp hnI
    have he := Nat.mul_div_cancel' hnD
    have hjp : 0 < (n/d : ℕ) := by
      apply Nat.pos_of_ne_zero
      intro hz
      rw [hz,mul_zero] at he
      omega
    exact Finset.mem_Icc.mpr ⟨hjp,(Nat.div_le_self n d).trans hnN⟩
  have heq : (∑ n ∈ S, 1/(n : ℝ)) =
      (1/(d : ℝ)) * ∑ j ∈ S.image f, 1/(j : ℝ) := by
    rw [Finset.mul_sum,Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro n hn
      have hnD := (Finset.mem_filter.mp hn).2
      dsimp only [f]
      rw [one_div_mul_one_div,← Nat.cast_mul,Nat.mul_div_cancel' hnD]
    · exact fun a ha b hb he => hi ha hb he
  change (∑ n ∈ S, 1/(n : ℝ)) ≤ _
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

theorem sqrt_multiple_sum_le (N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·), Real.sqrt d/(n : ℝ)) ≤ harmonicWeight N := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : Real.sqrt (d : ℝ) ≤ (d : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith⟩
  have hs : Real.sqrt (d : ℝ)/(d : ℝ) ≤ 1 := (div_le_one hdp).mpr hsqrt
  calc
    _ = Real.sqrt d * (∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·),1/(n : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ Real.sqrt d * ((1/(d : ℝ))*harmonicWeight N) :=
      mul_le_mul_of_nonneg_left (multiple_reciprocal_sum_le N d hd) (Real.sqrt_nonneg _)
    _ = (Real.sqrt (d : ℝ)/(d : ℝ))*harmonicWeight N := by ring
    _ ≤ 1*harmonicWeight N := mul_le_mul_of_nonneg_right hs (harmonicWeight_nonneg N)
    _ = _ := one_mul _

theorem gcd_harmonic_sum_le (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Finset.Icc 1 N, Real.sqrt (Nat.gcd n N)/(n : ℝ)) ≤
      (N.divisors.card : ℝ)*harmonicWeight N := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ N.divisors,
        if d ∣ n then Real.sqrt d/(n : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      have hg : Nat.gcd n N ∈ N.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _,Nat.ne_of_gt hN⟩
      have h := Finset.single_le_sum (s := N.divisors)
        (f := fun d => if d ∣ n then Real.sqrt d/(n : ℝ) else 0)
        (fun _ _ => by positivity) hg
      simpa only [ite_eq_left (Nat.gcd_dvd_left n N)] using h
    _ = ∑ d ∈ N.divisors,
        ∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·),Real.sqrt d/(n : ℝ) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ ∑ _d ∈ N.divisors,harmonicWeight N := by
      apply Finset.sum_le_sum
      intro d hd
      exact sqrt_multiple_sum_le N d (Nat.pos_of_mem_divisors hd)
    _ = _ := by simp

end ErdosHyperbola

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_UnitCyclicBounds
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbola

theorem harmonicWeight_eq (N : ℕ) : harmonicWeight N = (harmonic N : ℝ) := by
  simp only [harmonicWeight,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,
    Rat.cast_natCast,one_div]

theorem harmonicWeight_log_le (N : ℕ) (hN : 0 < N) :
    harmonicWeight N ≤ harmonicConstant * Real.log (2*(N : ℝ)) := by
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 : Real.log 2 ≤ Real.log (2*(N : ℝ)) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have h1 : (1 : ℝ) ≤ Real.log (2*(N : ℝ))/Real.log 2 :=
    (le_div_iff₀ htwo).mpr (by simpa using h2)
  have hlog : Real.log (N : ℝ) ≤ Real.log (2*(N : ℝ)) :=
    Real.log_le_log hp (by linarith)
  calc
    _ ≤ 1+Real.log (N : ℝ) := by rw [harmonicWeight_eq]; exact harmonic_le_one_add_log N
    _ ≤ Real.log (2*(N : ℝ))/Real.log 2+Real.log (2*(N : ℝ)) :=
      add_le_add h1 hlog
    _ = _ := by unfold harmonicConstant; ring

end ErdosHyperbola

end

section

open scoped BigOperators

namespace ErdosHyperbola

open ErdosHyperbolaFourier

attribute [local instance] Classical.decEq

theorem cyclic_weight_sum_le (N : ℕ) [NeZero N] (w : ZMod N → ℝ)
    (hw : ∀ r, 0 ≤ w r) (heven : ∀ r, w (-r) = w r) :
    (∑ r : ZMod N, w r/(cyclicDistance N r : ℝ)) ≤
      2 * ∑ r : ZMod N, w r/(r.val : ℝ) := by
  have hp (r : ZMod N) :
      w r/(cyclicDistance N r : ℝ) ≤ w r/(r.val : ℝ) + w (-r)/((-r).val : ℝ) := by
    by_cases hr : r = 0
    · simp [hr,cyclicDistance]
    have hneg : (-r).val = N-r.val := by rw [ZMod.neg_val,ite_eq_right hr]
    have hdist : (cyclicDistance N r : ℝ) = min (r.val : ℝ) ((-r).val : ℝ) := by
      simp only [cyclicDistance,Nat.cast_min,hneg]
    rw [hdist,heven r]
    rcases le_total (r.val : ℝ) ((-r).val : ℝ) with h | h
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (div_nonneg (hw _) (Nat.cast_nonneg _))
    · rw [min_eq_right h]
      exact le_add_of_nonneg_left (div_nonneg (hw _) (Nat.cast_nonneg _))
  have hsym : (∑ r : ZMod N,w (-r)/((-r).val : ℝ)) =
      ∑ r : ZMod N,w r/(r.val : ℝ) := by
    have h := Equiv.sum_comp (Equiv.neg (ZMod N)) (fun r => w r/(r.val : ℝ))
    simpa only [Equiv.neg_apply] using h
  calc
    _ ≤ ∑ r : ZMod N,(w r/(r.val : ℝ) + w (-r)/((-r).val : ℝ)) :=
      Finset.sum_le_sum (fun r _ => hp r)
    _ = _ := by rw [Finset.sum_add_distrib,hsym]; ring

theorem sum_representatives_le (N : ℕ) [NeZero N] (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (hf0 : f 0 = 0) :
    (∑ r : ZMod N, f r.val) ≤ ∑ n ∈ Finset.Icc 1 N, f n := by
  let S := (Finset.univ : Finset (ZMod N)).filter (· ≠ 0)
  have hzero : (∑ r ∈ S,f r.val) = ∑ r : ZMod N,f r.val := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : r = 0 <;> simp [hr,hf0]
  have hi : Set.InjOn (ZMod.val : ZMod N → ℕ) (S : Set (ZMod N)) :=
    (ZMod.val_injective N).injOn
  have hsub : S.image ZMod.val ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hn
    have hr0 := (Finset.mem_filter.mp hr).2
    have hval : 0 < r.val := Nat.pos_of_ne_zero (fun hz => hr0 ((ZMod.val_eq_zero r).mp hz))
    exact Finset.mem_Icc.mpr ⟨hval,r.val_lt.le⟩
  rw [← hzero]
  calc
    _ = ∑ n ∈ S.image ZMod.val,f n := by
      rw [Finset.sum_image]
      exact fun a ha b hb h => hi ha hb h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)

end ErdosHyperbola

end

section

open scoped BigOperators

namespace ErdosHyperbola

open ErdosHyperbolaFourier

theorem gcd_val_neg (N : ℕ) [NeZero N] (r : ZMod N) :
    Nat.gcd (-r).val N = Nat.gcd r.val N := by
  by_cases hr : r = 0
  · simp [hr]
  rw [ZMod.neg_val,ite_eq_right hr]
  exact Nat.gcd_self_sub_left r.val_lt.le

theorem cyclic_inverse_sum_le (N : ℕ) [NeZero N] :
    (∑ r : ZMod N, 1/(cyclicDistance N r : ℝ)) ≤
      (2*harmonicConstant)*Real.log (2*(N : ℝ)) := by
  have h := cyclic_weight_sum_le N (fun _ => 1) (fun _ => zero_le_one) (fun _ => rfl)
  have hr : (∑ r : ZMod N,1/(r.val : ℝ)) ≤ harmonicWeight N :=
    sum_representatives_le N (fun n => 1/(n : ℝ)) (fun _ => by positivity) (by simp)
  calc
    _ ≤ 2*harmonicWeight N := h.trans (mul_le_mul_of_nonneg_left hr (by norm_num))
    _ ≤ 2*(harmonicConstant*Real.log (2*(N : ℝ))) :=
      mul_le_mul_of_nonneg_left (harmonicWeight_log_le N (NeZero.pos N)) (by norm_num)
    _ = _ := by ring

theorem sqrt_gcd_cyclic_sum_le (N : ℕ) [NeZero N] :
    (∑ r : ZMod N, Real.sqrt (Nat.gcd r.val N)/(cyclicDistance N r : ℝ)) ≤
      (2*harmonicConstant)*(N.divisors.card : ℝ)*Real.log (2*(N : ℝ)) := by
  have heven (r : ZMod N) : Real.sqrt (Nat.gcd (-r).val N) = Real.sqrt (Nat.gcd r.val N) := by
    rw [gcd_val_neg]
  have h := cyclic_weight_sum_le N (fun r => Real.sqrt (Nat.gcd r.val N))
    (fun _ => Real.sqrt_nonneg _) heven
  have hr : (∑ r : ZMod N, Real.sqrt (Nat.gcd r.val N)/(r.val : ℝ)) ≤
      (N.divisors.card : ℝ)*harmonicWeight N :=
    (sum_representatives_le N (fun n => Real.sqrt (Nat.gcd n N)/(n : ℝ))
      (fun _ => by positivity) (by simp)).trans (gcd_harmonic_sum_le N (NeZero.pos N))
  calc
    _ ≤ 2*((N.divisors.card : ℝ)*harmonicWeight N) :=
      h.trans (mul_le_mul_of_nonneg_left hr (by norm_num))
    _ ≤ 2*((N.divisors.card : ℝ)*(harmonicConstant*Real.log (2*(N : ℝ)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (harmonicWeight_log_le N (NeZero.pos N)) (Nat.cast_nonneg _))
        (by norm_num)
    _ = _ := by ring

end ErdosHyperbola

end

section

open scoped BigOperators

namespace ErdosHyperbola

open ErdosHyperbolaFourier

theorem gcd_mul_unit (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) (r : ZMod N) :
    Nat.gcd (r*(u : ZMod N)).val N = Nat.gcd r.val N := by
  have hu : u.val.val.Coprime N := (ZMod.isUnit_iff_coprime u.val.val N).mp
    (by simpa only [ZMod.natCast_zmod_val] using u.isUnit)
  have he : r*(u : ZMod N) = ((r.val*u.val.val : ℕ) : ZMod N) := by simp
  rw [he,ZMod.val_natCast,← Nat.gcd_rec,Nat.gcd_comm N,hu.gcd_mul_right_cancel]

theorem unit_cyclic_inverse_sum_le (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    (∑ r : ZMod N,1/(cyclicDistance N (r*(u : ZMod N)) : ℝ)) ≤
      (2*harmonicConstant)*Real.log (2*(N : ℝ)) := by
  have he := Equiv.sum_comp (mulUnitEquiv N u)
    (fun r => 1/(cyclicDistance N r : ℝ))
  simp only [mulUnitEquiv_apply] at he
  rw [he]
  exact cyclic_inverse_sum_le N

theorem unit_sqrt_gcd_cyclic_sum_le (N : ℕ) [NeZero N] (u : (ZMod N)ˣ) :
    (∑ r : ZMod N,Real.sqrt (Nat.gcd r.val N)/
      (cyclicDistance N (r*(u : ZMod N)) : ℝ)) ≤
      (2*harmonicConstant)*(N.divisors.card : ℝ)*Real.log (2*(N : ℝ)) := by
  have he := Equiv.sum_comp (mulUnitEquiv N u)
    (fun r => Real.sqrt (Nat.gcd r.val N)/(cyclicDistance N r : ℝ))
  simp only [mulUnitEquiv_apply,gcd_mul_unit] at he
  rw [he]
  exact sqrt_gcd_cyclic_sum_le N

end ErdosHyperbola

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_IntervalHyperbolaAdapter
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbolaFourier

theorem norm_characterProgression_le (N : ℕ) [NeZero N]
    (start step : ZMod N) (J : ℕ) (hs : step ≠ 0) :
    ‖characterProgression N start step J‖ ≤ (N : ℝ)/(cyclicDistance N step : ℝ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hd : (0 : ℝ) < cyclicDistance N step := by
    exact_mod_cast cyclicDistance_pos N step hs
  have hm := (mul_le_mul_of_nonneg_left (standard_character_chord_lower N step)
    (norm_nonneg (characterProgression N start step J))).trans
      (norm_characterProgression_mul_chord N start step J)
  have hm' : ‖characterProgression N start step J‖ * (4*(cyclicDistance N step : ℝ)) ≤
      2*(N : ℝ) := by
    apply (div_le_iff₀ hN).mp
    convert hm using 1 <;> first | rfl | ring
  apply (le_div_iff₀ hd).mpr
  nlinarith

end ErdosHyperbolaFourier

end

section

open scoped BigOperators
namespace ErdosHyperbolaFourier

theorem intervalWeight_eq_progression (N : ℕ) [NeZero N] (h : ZMod N)
    (x y : ℝ) (lc rc : Bool) (T : ℕ) (a : ℤ) (hT : 0 < T) :
    intervalWeight N h x y lc rc T a =
      characterProgression N (-h*(progressionPoint a T (lowerIndex x T a lc) : ZMod N))
        (-h*(T : ZMod N)) (upperIndex y T a rc-lowerIndex x T a lc).toNat := by
  unfold intervalWeight progressionPoints
  rw [Finset.sum_image]
  · rw [Int.Ico_eq_finset_map, Finset.sum_map]
    unfold characterProgression
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    change -h * (((a+(T : ℤ)*(lowerIndex x T a lc+(i : ℤ)) : ℤ)) : ZMod N) =
      -h * (((a+(T : ℤ)*lowerIndex x T a lc : ℤ)) : ZMod N) +
        (i : ZMod N)*(-h*(T : ZMod N))
    push_cast
    ring
  · intro i _ j _ hij
    exact progressionPoint_injective a T hT hij

theorem intervalWeight_zero (N : ℕ) [NeZero N] (x y : ℝ) (lc rc : Bool) (T : ℕ) (a : ℤ) :
    intervalWeight N 0 x y lc rc T a = (progressionPoints x y lc rc T a).card := by
  simp [intervalWeight]

theorem norm_intervalWeight_le (N : ℕ) [NeZero N] (h : ZMod N)
    (x y : ℝ) (lc rc : Bool) (T : ℕ) (a : ℤ) (hT : 0 < T)
    (hs : -h*(T : ZMod N) ≠ 0) :
    ‖intervalWeight N h x y lc rc T a‖ ≤ (N : ℝ)/(cyclicDistance N (-h*(T : ZMod N)) : ℝ) := by
  rw [intervalWeight_eq_progression N h x y lc rc T a hT]
  exact norm_characterProgression_le N _ _ _ hs

theorem norm_intervalWeight_le_of_coprime (N : ℕ) [NeZero N] (h : ZMod N) (hh : h ≠ 0)
    (x y : ℝ) (lc rc : Bool) (T : ℕ) (a : ℤ) (hT : 0 < T) (hTN : T.Coprime N) :
    ‖intervalWeight N h x y lc rc T a‖ ≤ (N : ℝ)/(cyclicDistance N (-h*(T : ZMod N)) : ℝ) := by
  have hunit : IsUnit (T : ZMod N) := (ZMod.isUnit_iff_coprime T N).mpr hTN
  apply norm_intervalWeight_le N h x y lc rc T a hT
  intro hs
  exact hh (neg_eq_zero.mp (hunit.mul_left_eq_zero.mp hs))

end ErdosHyperbolaFourier

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_FourierL1
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators

namespace ErdosHyperbola

open ErdosHyperbolaFourier
attribute [local instance] Classical.decEq

theorem intervalWeight_l1 (N : ℕ) [NeZero N] (x y : ℝ) (lc rc : Bool)
    (T : ℕ) (a : ℤ) (hT : 0 < T) (hTN : T.Coprime N) :
    (∑ h ∈ (Finset.univ : Finset (ZMod N)).filter (· ≠ 0),
      ‖intervalWeight N h x y lc rc T a‖) ≤
      (2*harmonicConstant)*(N : ℝ)*Real.log (2*(N : ℝ)) := by
  have hu : IsUnit (-(T : ZMod N)) := ((ZMod.isUnit_iff_coprime T N).mpr hTN).neg
  obtain ⟨u,hu⟩ := hu
  have he (h : ZMod N) : h*(u : ZMod N) = -h*(T : ZMod N) := by rw [hu]; ring
  calc
    _ ≤ ∑ h ∈ (Finset.univ : Finset (ZMod N)).filter (· ≠ 0),
        (N : ℝ)/(cyclicDistance N (h*(u : ZMod N)) : ℝ) := by
      apply Finset.sum_le_sum
      intro h hh
      rw [he]
      exact norm_intervalWeight_le_of_coprime N h (Finset.mem_filter.mp hh).2 x y lc rc T a hT hTN
    _ ≤ ∑ h : ZMod N,(N : ℝ)/(cyclicDistance N (h*(u : ZMod N)) : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (N : ℝ)*∑ h : ZMod N,1/(cyclicDistance N (h*(u : ZMod N)) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ ≤ (N : ℝ)*((2*harmonicConstant)*Real.log (2*(N : ℝ))) :=
      mul_le_mul_of_nonneg_left (unit_cyclic_inverse_sum_le N u) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem intervalWeight_gcd_l1 (N : ℕ) [NeZero N] (x y : ℝ) (lc rc : Bool)
    (T : ℕ) (a : ℤ) (hT : 0 < T) (hTN : T.Coprime N) :
    (∑ h ∈ (Finset.univ : Finset (ZMod N)).filter (· ≠ 0),
      ‖intervalWeight N h x y lc rc T a‖*Real.sqrt (Nat.gcd h.val N)) ≤
      (2*harmonicConstant)*(N : ℝ)*(N.divisors.card : ℝ)*Real.log (2*(N : ℝ)) := by
  have hu : IsUnit (-(T : ZMod N)) := ((ZMod.isUnit_iff_coprime T N).mpr hTN).neg
  obtain ⟨u,hu⟩ := hu
  have he (h : ZMod N) : h*(u : ZMod N) = -h*(T : ZMod N) := by rw [hu]; ring
  calc
    _ ≤ ∑ h ∈ (Finset.univ : Finset (ZMod N)).filter (· ≠ 0),
        ((N : ℝ)/(cyclicDistance N (h*(u : ZMod N)) : ℝ))*Real.sqrt (Nat.gcd h.val N) := by
      apply Finset.sum_le_sum
      intro h hh
      rw [he]
      exact mul_le_mul_of_nonneg_right
        (norm_intervalWeight_le_of_coprime N h (Finset.mem_filter.mp hh).2 x y lc rc T a hT hTN)
        (Real.sqrt_nonneg _)
    _ ≤ ∑ h : ZMod N,
        ((N : ℝ)/(cyclicDistance N (h*(u : ZMod N)) : ℝ))*Real.sqrt (Nat.gcd h.val N) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (N : ℝ)*∑ h : ZMod N,Real.sqrt (Nat.gcd h.val N)/
        (cyclicDistance N (h*(u : ZMod N)) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ ≤ (N : ℝ)*((2*harmonicConstant)*(N.divisors.card : ℝ)*Real.log (2*(N : ℝ))) :=
      mul_le_mul_of_nonneg_left (unit_sqrt_gcd_cyclic_sum_le N u) (Nat.cast_nonneg _)
    _ = _ := by ring

end ErdosHyperbola

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_DilationCoordinates
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

theorem l1Norm_nonneg (N : ℕ) [NeZero N] (P : ProgressionInterval) : 0 ≤ l1Norm N P := by
  unfold l1Norm
  positivity

theorem gcdL1Norm_nonneg (N : ℕ) [NeZero N] (P : ProgressionInterval) : 0 ≤ gcdL1Norm N P := by
  unfold gcdL1Norm
  positivity

theorem l1Norm_le (N : ℕ) [NeZero N] (P : ProgressionInterval) (hP : P.step.Coprime N) :
    l1Norm N P ≤ (2*ErdosHyperbola.harmonicConstant)*(N : ℝ)*Real.log (2*(N : ℝ)) :=
  ErdosHyperbola.intervalWeight_l1 N P.left P.right P.leftClosed P.rightClosed P.step P.residue P.step_pos hP

theorem gcdL1Norm_le (N : ℕ) [NeZero N] (P : ProgressionInterval) (hP : P.step.Coprime N) :
    gcdL1Norm N P ≤ (2*ErdosHyperbola.harmonicConstant)*(N : ℝ)*(N.divisors.card : ℝ)*
      Real.log (2*(N : ℝ)) :=
  ErdosHyperbola.intervalWeight_gcd_l1 N P.left P.right P.leftClosed P.rightClosed P.step P.residue P.step_pos hP

theorem intervalLength_nonneg (P : ProgressionInterval) (hP : P.left ≤ P.right) :
    0 ≤ intervalLength P := sub_nonneg.mpr hP

theorem weight_zero_eq_count (N : ℕ) [NeZero N] (P : ProgressionInterval) :
    P.weight N 0 = (P.points.card : ℂ) :=
  ErdosHyperbolaFourier.intervalWeight_zero N P.left P.right P.leftClosed P.rightClosed P.step P.residue

theorem interval_count_error (P : ProgressionInterval) (hP : P.left ≤ P.right) :
    |(P.points.card : ℝ)-intervalLength P/(P.step : ℝ)| ≤ 1 :=
  ErdosHyperbolaFourier.progressionPoints_count_error P.left P.right hP P.leftClosed P.rightClosed
    P.step P.residue P.step_pos

theorem interval_average_le_length (P : ProgressionInterval) (hP : P.left ≤ P.right) :
    intervalLength P/(P.step : ℝ) ≤ intervalLength P := by
  have hs : (0 : ℝ) < P.step := by exact_mod_cast P.step_pos
  have hs1 : (1 : ℝ) ≤ P.step := by exact_mod_cast P.step_pos
  apply (div_le_iff₀ hs).mpr
  exact le_mul_of_one_le_right (intervalLength_nonneg P hP) hs1

theorem interval_count_le_length_add_one (P : ProgressionInterval) (hP : P.left ≤ P.right) :
    (P.points.card : ℝ) ≤ intervalLength P+1 := by
  have h := (abs_le.mp (interval_count_error P hP)).2
  have hu := interval_average_le_length P hP
  linarith

theorem norm_weight_zero_le (N : ℕ) [NeZero N] (P : ProgressionInterval) (hP : P.left ≤ P.right) :
    ‖P.weight N 0‖ ≤ intervalLength P+1 := by
  rw [weight_zero_eq_count]
  simpa using interval_count_le_length_add_one P hP

end ErdosHyperbolaError

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_CharacterReduction
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman.PrimePower

theorem standard_character_reduction (n d : ℕ) [NeZero n] [NeZero d]
    (x : ZMod (n*d)) :
    ZMod.stdAddChar ((n : ZMod (n*d)) * x) =
      ZMod.stdAddChar (reduction n d x) := by
  have hl : (n : ZMod (n*d)) * x =
      (((n : ℤ) * (x.val : ℤ) : ℤ) : ZMod (n*d)) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  have hr : reduction n d x = ((x.val : ℤ) : ZMod d) := by
    simpa only [Int.cast_natCast] using reduction_apply_val n d x
  rw [hl, hr, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  field_simp

theorem scaled_phase_reduction (n d : ℕ) [NeZero n] [NeZero d] (h k : ℤ)
    (u : (ZMod (n*d))ˣ) :
    ZMod.stdAddChar ((((n : ℤ)*h : ℤ) : ZMod (n*d)) * (u : ZMod (n*d)) +
      (((n : ℤ)*k : ℤ) : ZMod (n*d)) * (↑u⁻¹ : ZMod (n*d))) =
    ZMod.stdAddChar ((h : ZMod d) * (ZMod.unitsMap (dvd_mul_left d n) u : ZMod d) +
      (k : ZMod d) * (↑(ZMod.unitsMap (dvd_mul_left d n) u)⁻¹ : ZMod d)) := by
  have hphase : (((n : ℤ)*h : ℤ) : ZMod (n*d)) * (u : ZMod (n*d)) +
      (((n : ℤ)*k : ℤ) : ZMod (n*d)) * (↑u⁻¹ : ZMod (n*d)) =
      (n : ZMod (n*d)) * ((h : ZMod (n*d))*u + (k : ZMod (n*d))*↑u⁻¹) := by
    push_cast
    ring
  rw [hphase, standard_character_reduction]
  congr 1
  simp [reduction, ZMod.unitsMap_def, ← map_inv]

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Partitions_UnitReductionFibres
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosKloosterman.PrimePower

attribute [local instance] Classical.decEq

private theorem card_mul_group_fibre {A B : Type*} [Group A] [Fintype A]
    [Group B] [Fintype B] (f : A →* B) (hf : Function.Surjective f) (b : B) :
    Fintype.card B * ((Finset.univ : Finset A).filter fun x => f x = b).card =
      Fintype.card A := by
  calc
    _ = ∑ _y : B, ((Finset.univ : Finset A).filter fun x => f x = b).card := by simp
    _ = ∑ y : B, ((Finset.univ : Finset A).filter fun x => f x = y).card := by
      apply Finset.sum_congr rfl
      intro y _
      exact MonoidHom.card_fiber_eq_of_mem_range f (hf b) (hf y)
    _ = _ := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      simp

theorem unit_reduction_fibre_card (p s : ℕ) [Fact p.Prime] (hs : 0 < s)
    (v : (ZMod (p^s))ˣ) :
    ((Finset.univ : Finset (ZMod (p*p^s))ˣ).filter fun u =>
      ZMod.unitsMap (dvd_mul_left (p^s) p) u = v).card = p := by
  let f : (ZMod (p*p^s))ˣ →* (ZMod (p^s))ˣ := ZMod.unitsMap (dvd_mul_left (p^s) p)
  have hf : Function.Surjective f := ZMod.unitsMap_surjective (dvd_mul_left (p^s) p)
  have hc := card_mul_group_fibre f hf v
  have htot : Fintype.card (ZMod (p*p^s))ˣ = Fintype.card (ZMod (p^s))ˣ * p := by
    rw [ZMod.card_units_eq_totient, ZMod.card_units_eq_totient, ← pow_succ',
      Nat.totient_prime_pow_succ (Fact.out : p.Prime),
      Nat.totient_prime_pow (Fact.out : p.Prime) hs]
    have he : p^s = p^(s-1)*p := by
      rw [← pow_succ]
      congr 1
      omega
    rw [he]
    ring
  rw [htot] at hc
  simpa only [f] using Nat.eq_of_mul_eq_mul_left
    (show 0 < Fintype.card (ZMod (p^s))ˣ from Fintype.card_pos) hc

theorem sum_comp_unit_reduction (p s : ℕ) [Fact p.Prime] (hs : 0 < s)
    (f : (ZMod (p^s))ˣ → ℂ) :
    (∑ u : (ZMod (p*p^s))ˣ, f (ZMod.unitsMap (dvd_mul_left (p^s) p) u)) =
      (p : ℂ) * ∑ v : (ZMod (p^s))ˣ, f v := by
  rw [← Finset.sum_fiberwise' Finset.univ (ZMod.unitsMap (dvd_mul_left (p^s) p)) f]
  simp only [Finset.sum_const, unit_reduction_fibre_card p s hs, nsmul_eq_mul,
    ← Finset.mul_sum]

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_CommonFrequencyLift
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosKloosterman.PrimePower

theorem common_frequency_lift_product (p s : ℕ) [Fact p.Prime] (hs : 0 < s)
    (h k : ℤ) :
    standardSum (p*p^s) ((p : ℤ)*h) ((p : ℤ)*k) =
      (p : ℂ) * standardSum (p^s) h k := by
  unfold standardSum sum
  simp_rw [scaled_phase_reduction p (p^s) h k]
  convert! sum_comp_unit_reduction p s hs
    (fun u : (ZMod (p^s))ˣ => (ZMod.stdAddChar (N := p^s)) ((h : ZMod (p^s))*(u : ZMod (p^s)) +
      (k : ZMod (p^s))*(↑u⁻¹ : ZMod (p^s)))) using 1
  · apply Finset.sum_congr (by ext u; simp)
    intro u _
    rfl
  · congr 1
    apply Finset.sum_congr (by ext u; simp)
    intro u _
    rfl

theorem common_frequency_lift (p s : ℕ) [Fact p.Prime] (hs : 0 < s) (h k : ℤ) :
    standardSum (p^(s+1)) ((p : ℤ)*h) ((p : ℤ)*k) =
      (p : ℂ) * standardSum (p^s) h k := by
  rw [standardSum_modulus_congr _ (p*p^s) (pow_succ' p s)]
  exact common_frequency_lift_product p s hs h k

theorem common_frequency_gcd (p s : ℕ) (h k : ℤ) :
    Nat.gcd (p^(s+1)) (Int.gcd ((p : ℤ)*h) ((p : ℤ)*k)) =
      p * Nat.gcd (p^s) (Int.gcd h k) := by
  rw [pow_succ', Int.gcd_mul_left, Int.natAbs_natCast, Nat.gcd_mul_left]

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Probability_KloostermanFourthMoment
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators ComplexConjugate

namespace ErdosKloosterman

attribute [local instance] Classical.decEq

variable {F : Type*} [Field F] [Fintype F]

private theorem fourth_expand (ψ : AddChar F ℂ) (a b : F) :
    sum ψ a b * sum ψ a b * conj (sum ψ a b) * conj (sum ψ a b) =
    ∑ x : (Fˣ × Fˣ) × (Fˣ × Fˣ), ψ
      (a * ((x.2.1 : F) + x.2.2 - x.1.1 - x.1.2) +
       b * ((↑x.2.1⁻¹ : F) + ↑x.2.2⁻¹ - ↑x.1.1⁻¹ - ↑x.1.2⁻¹)) := by
  simp only [sum, map_sum, Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro w _
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_neg_eq_conj,
    ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  ring

private theorem two_frequency_orthogonality (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (x y : F) :
    (∑ a : F, ∑ b : F, ψ (a*x + b*y)) =
      if x = 0 ∧ y = 0 then (Fintype.card F : ℂ)^2 else 0 := by
  simp_rw [AddChar.map_add_eq_mul, ← Finset.mul_sum,
    AddChar.sum_mulShift _ hψ, ← Finset.sum_mul, AddChar.sum_mulShift _ hψ]
  split_ifs <;> simp_all [pow_two]

theorem fourth_moment_identity (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    (∑ a : F, ∑ b : F,
      sum ψ a b * sum ψ a b * conj (sum ψ a b) * conj (sum ψ a b)) =
    (Fintype.card F : ℂ)^2 * (pairCollisions F).card := by
  simp_rw [fourth_expand]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [two_frequency_orthogonality ψ hψ]
  have heq (x : (Fˣ × Fˣ) × (Fˣ × Fˣ)) :
      ((x.2.1 : F) + x.2.2 - x.1.1 - x.1.2 = 0 ∧
        (↑x.2.1⁻¹ : F) + ↑x.2.2⁻¹ - ↑x.1.1⁻¹ - ↑x.1.2⁻¹ = 0) ↔
      ((x.1.1 : F) + x.1.2 = x.2.1 + x.2.2 ∧
        (↑x.1.1⁻¹ : F) + ↑x.1.2⁻¹ = ↑x.2.1⁻¹ + ↑x.2.2⁻¹) := by
    simp only [sub_sub, sub_eq_zero, eq_comm]
  simp_rw [heq]
  rw [← Finset.sum_filter]
  simp only [pairCollisions, Finset.sum_const, nsmul_eq_mul]
  ring

end ErdosKloosterman

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_KloostermanPrimeBound
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators ComplexConjugate

namespace ErdosKloosterman

attribute [local instance] Classical.decEq

variable {F : Type*} [Field F] [Fintype F]

private theorem fourth_product_eq_norm (z : ℂ) :
    z*z*conj z*conj z = ((‖z‖^4 : ℝ) : ℂ) := by
  calc
    _ = (z * conj z)^2 := by ring
    _ = _ := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]
      congr 1
      ring

theorem fourth_norm_identity (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    (∑ a : F, ∑ b : F, ‖sum ψ a b‖^4) =
      (Fintype.card F : ℝ)^2 * (pairCollisions F).card := by
  have h := fourth_moment_identity ψ hψ
  simp_rw [fourth_product_eq_norm] at h
  exact_mod_cast h

private theorem unit_orbit_bound (ψ : AddChar F ℂ) (a b : F) (ha : a ≠ 0) :
    (Fintype.card Fˣ : ℝ) * ‖sum ψ a b‖^4 ≤
      ∑ x : F × F, ‖sum ψ x.1 x.2‖^4 := by
  let f : Fˣ → F × F := fun c => (a * (c : F), b * (↑c⁻¹ : F))
  have hf : Function.Injective f := by
    intro c d h
    apply Units.ext
    exact mul_left_cancel₀ ha (congrArg Prod.fst h)
  have heq : (∑ x ∈ Finset.univ.image f, ‖sum ψ x.1 x.2‖^4) =
      (Fintype.card Fˣ : ℝ) * ‖sum ψ a b‖^4 := by
    rw [Finset.sum_image]
    · simp only [f, sum_unit_scale, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    · exact fun c _ d _ h => hf h
  rw [← heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)

theorem fourth_norm_le (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a b : F) (hab : a ≠ 0 ∨ b ≠ 0) :
    ‖sum ψ a b‖^4 ≤ 3 * (Fintype.card F : ℝ)^3 := by
  have left (a b : F) (ha : a ≠ 0) :
      ‖sum ψ a b‖^4 ≤ 3 * (Fintype.card F : ℝ)^3 := by
    have horbit := unit_orbit_bound ψ a b ha
    rw [Fintype.sum_prod_type, fourth_norm_identity ψ hψ] at horbit
    have hc : ((pairCollisions F).card : ℝ) ≤ 3 * (Fintype.card Fˣ : ℝ)^2 := by
      exact_mod_cast pairCollisions_card_le F
    have hu : (0 : ℝ) < Fintype.card Fˣ := by exact_mod_cast Fintype.card_pos
    have hf : (Fintype.card Fˣ : ℝ) ≤ (Fintype.card F : ℝ) := by
      exact_mod_cast Fintype.card_le_of_injective (fun x : Fˣ => (x : F)) Units.val_injective
    have hbound : (Fintype.card Fˣ : ℝ) * ‖sum ψ a b‖^4 ≤
        (Fintype.card Fˣ : ℝ) * (3 * (Fintype.card F : ℝ)^2 * Fintype.card Fˣ) := by
      calc
        _ ≤ (Fintype.card F : ℝ)^2 * (pairCollisions F).card := horbit
        _ ≤ (Fintype.card F : ℝ)^2 * (3 * (Fintype.card Fˣ : ℝ)^2) :=
          mul_le_mul_of_nonneg_left hc (sq_nonneg _)
        _ = _ := by ring
    have hcancel := (mul_le_mul_iff_right₀ hu).mp hbound
    calc
      _ ≤ 3 * (Fintype.card F : ℝ)^2 * Fintype.card Fˣ := hcancel
      _ ≤ 3 * (Fintype.card F : ℝ)^2 * Fintype.card F :=
        mul_le_mul_of_nonneg_left hf (by positivity)
      _ = _ := by ring
  rcases hab with ha | hb
  · exact left a b ha
  · rw [sum_swap]
    exact left b a hb

end ErdosKloosterman

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_KloostermanPrimeExponent
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman

theorem norm_le_three_quarters {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (a b : F) (hab : a ≠ 0 ∨ b ≠ 0) :
    ‖sum ψ a b‖ ≤ 2 * (Fintype.card F : ℝ)^((3 : ℝ)/4) := by
  have hfour := fourth_norm_le ψ hψ a b hab
  have hq : 0 ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
  have hp : ((Fintype.card F : ℝ)^((3 : ℝ)/4))^4 = (Fintype.card F : ℝ)^3 := by
    rw [← Real.rpow_mul_natCast hq]
    norm_num
  have hright : (2 * (Fintype.card F : ℝ)^((3 : ℝ)/4))^4 =
      16 * (Fintype.card F : ℝ)^3 := by rw [mul_pow, hp]; norm_num
  have hb : ‖sum ψ a b‖^4 ≤ (2 * (Fintype.card F : ℝ)^((3 : ℝ)/4))^4 := by
    rw [hright]
    nlinarith [show 0 ≤ (Fintype.card F : ℝ)^3 by positivity]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by decide : 4 ≠ 0)).mp hb

theorem standardSum_prime_bound (p : ℕ) [Fact p.Prime] (h k : ℤ)
    (hk : (h : ZMod p) ≠ 0 ∨ (k : ZMod p) ≠ 0) :
    ‖standardSum p h k‖ ≤ 2 * (p : ℝ)^((3 : ℝ)/4) := by
  simpa only [standardSum, ZMod.card] using
    norm_le_three_quarters ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar p)
      (h : ZMod p) (k : ZMod p) hk

end ErdosKloosterman

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Primes_PrimePowerBound
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman.PrimePower

theorem envelope_ge_primitive (p a : ℕ) [Fact p.Prime] (ha : 0 < a) (h k : ℤ) :
    4 * ((p^a : ℕ) : ℝ)^((3 : ℝ)/4) ≤ envelope p a h k := by
  have hg : 0 < Nat.gcd (p^a) (Int.gcd h k) :=
    Nat.gcd_pos_of_pos_left _ (pow_pos (Fact.out : p.Prime).pos a)
  have hg1 : (1 : ℝ) ≤ ((Nat.gcd (p^a) (Int.gcd h k) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hg)
  have hgp := Real.one_le_rpow hg1 (by norm_num : (0 : ℝ) ≤ 1/4)
  have ha2 : (2 : ℝ) ≤ ((a+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ a+1)
  have hc : (4 : ℝ) ≤ ((a+1 : ℕ) : ℝ)^2 := by nlinarith
  unfold envelope
  calc
    _ ≤ ((a+1 : ℕ) : ℝ)^2 * ((p^a : ℕ) : ℝ)^((3 : ℝ)/4) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hgp

theorem quarter_scale (p Q g : ℝ) (hp : 0 < p) (hQ : 0 ≤ Q) (hg : 0 ≤ g) :
    p * (Q^((3 : ℝ)/4) * g^((1 : ℝ)/4)) =
      (p*Q)^((3 : ℝ)/4) * (p*g)^((1 : ℝ)/4) := by
  rw [Real.mul_rpow hp.le hQ, Real.mul_rpow hp.le hg]
  have he : p^((3 : ℝ)/4) * p^((1 : ℝ)/4) = p := by
    rw [← Real.rpow_add hp]
    norm_num
  calc
    _ = (p^((3 : ℝ)/4) * p^((1 : ℝ)/4)) *
        (Q^((3 : ℝ)/4) * g^((1 : ℝ)/4)) := by rw [he]
    _ = _ := by ring

theorem envelope_scale (p a : ℕ) [Fact p.Prime] (h k : ℤ) :
    (p : ℝ) * envelope p a h k ≤ envelope p (a+1) ((p : ℤ)*h) ((p : ℤ)*k) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hc : ((a+1 : ℕ) : ℝ)^2 ≤ ((a+1+1 : ℕ) : ℝ)^2 := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ a from Nat.cast_nonneg a]
  unfold envelope
  rw [common_frequency_gcd, pow_succ' p a, Nat.cast_mul, Nat.cast_mul]
  calc
    _ = ((a+1 : ℕ) : ℝ)^2 * ((p : ℝ) *
        (((p^a : ℕ) : ℝ)^((3 : ℝ)/4) *
          ((Nat.gcd (p^a) (Int.gcd h k) : ℕ) : ℝ)^((1 : ℝ)/4))) := by ring
    _ = _ := by rw [quarter_scale _ _ _ hp (by positivity) (by positivity)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end ErdosKloosterman.PrimePower

end

section

namespace ErdosKloosterman.PrimePower

private theorem prime_zero_envelope (p : ℕ) [Fact p.Prime] (h k : ℤ)
    (hh : (h : ZMod p) = 0) (hk : (k : ZMod p) = 0) :
    envelope p 1 h k = 4 * (p : ℝ) := by
  have hd : p ∣ Int.gcd h k := Int.dvd_gcd
    ((ZMod.intCast_zmod_eq_zero_iff_dvd h p).mp hh)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd k p).mp hk)
  have hg := Nat.gcd_eq_left_iff_dvd.mpr hd
  unfold envelope
  rw [pow_one, hg]
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  calc
    _ = 4 * ((p : ℝ)^((3 : ℝ)/4) * (p : ℝ)^((1 : ℝ)/4)) := by norm_num <;> ring
    _ = _ := by rw [← Real.rpow_add hp]; norm_num

theorem prime_envelope_bound (p : ℕ) [Fact p.Prime] (h k : ℤ) :
    ‖standardSum p h k‖ ≤ envelope p 1 h k := by
  have primitive (hab : (h : ZMod p) ≠ 0 ∨ (k : ZMod p) ≠ 0) :
      ‖standardSum p h k‖ ≤ envelope p 1 h k := by
    calc
      _ ≤ 2 * (p : ℝ)^((3 : ℝ)/4) := standardSum_prime_bound p h k hab
      _ ≤ 4 * (p : ℝ)^((3 : ℝ)/4) := by
        nlinarith [Real.rpow_nonneg (Nat.cast_nonneg p) ((3 : ℝ)/4)]
      _ ≤ _ := by simpa only [pow_one] using envelope_ge_primitive p 1 (by decide) h k
  by_cases hh : (h : ZMod p) = 0
  · by_cases hk : (k : ZMod p) = 0
    · have he : standardSum p h k = (Fintype.card (ZMod p)ˣ : ℂ) := by
        simp only [standardSum, hh, hk, sum_zero_zero, ← Nat.card_eq_fintype_card]
      have hc : (Fintype.card (ZMod p)ˣ : ℝ) ≤ p := by
        have hc := Fintype.card_le_of_injective (fun u : (ZMod p)ˣ => (u : ZMod p))
          Units.val_injective
        simpa only [ZMod.card] using (show (Fintype.card (ZMod p)ˣ : ℝ) ≤
          Fintype.card (ZMod p) by exact_mod_cast hc)
      rw [he]
      calc
        _ = (Fintype.card (ZMod p)ˣ : ℝ) := by simp
        _ ≤ p := hc
        _ ≤ envelope p 1 h k := by
          rw [prime_zero_envelope p h k hh hk]
          nlinarith [show (0 : ℝ) ≤ p from Nat.cast_nonneg p]
    · exact primitive (Or.inr hk)
  · exact primitive (Or.inl hh)

theorem prime_power_envelope_bound (p : ℕ) [Fact p.Prime] :
    ∀ a : ℕ, 0 < a → ∀ h k : ℤ, ‖standardSum (p^a) h k‖ ≤ envelope p a h k := by
  intro a
  induction a with
  | zero => intro ha; omega
  | succ a ih =>
    intro ha h k
    by_cases haz : a = 0
    · subst a
      simpa only [Nat.zero_add, pow_one] using prime_envelope_bound p h k
    have ha0 : 0 < a := by omega
    by_cases hprimitive : (h : ZMod p) ≠ 0 ∨ (k : ZMod p) ≠ 0
    · exact (primitive_three_quarter_bound p (a+1) (by omega) h k hprimitive).trans
        (envelope_ge_primitive p (a+1) (by omega) h k)
    push Not at hprimitive
    obtain ⟨hh, hk⟩ := hprimitive
    obtain ⟨h', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd h p).mp hh
    obtain ⟨k', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd k p).mp hk
    rw [common_frequency_lift p a ha0, norm_mul]
    have hn : ‖(p : ℂ)‖ = (p : ℝ) := by simp
    rw [hn]
    exact (mul_le_mul_of_nonneg_left (ih ha0 h' k') (Nat.cast_nonneg p)).trans
      (envelope_scale p a h' k')

theorem standardSum_prime_power_bound (p a : ℕ) [Fact p.Prime] (ha : 1 ≤ a) (h k : ℤ) :
    ‖standardSum (p^a) h k‖ ≤ ((a+1 : ℕ) : ℝ)^2 * ((p^a : ℕ) : ℝ)^((3 : ℝ)/4) *
      ((Nat.gcd (p^a) (Int.gcd h k) : ℕ) : ℝ)^((1 : ℝ)/4) :=
  prime_power_envelope_bound p a ha h k

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_KloostermanCRTCharacter
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman

theorem stdAddChar_bezout (m n : ℕ) [NeZero m] [NeZero n]
    (A B z : ℤ) (hab : (m : ℤ)*A + (n : ℤ)*B = 1) :
    ZMod.stdAddChar (z : ZMod (m*n)) =
      ZMod.stdAddChar ((B*z : ℤ) : ZMod m) *
        ZMod.stdAddChar ((A*z : ℤ) : ZMod n) := by
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hc : (m : ℂ)*(A : ℂ) + (n : ℂ)*(B : ℂ) = 1 := by exact_mod_cast hab
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  linear_combination -(z : ℂ) * hc

theorem stdAddChar_crt (m n : ℕ) [NeZero m] [NeZero n] (hmn : m.Coprime n) :
    (ZMod.stdAddChar : AddChar (ZMod (m*n)) ℂ) =
      (productChar
        (ZMod.stdAddChar.mulShift (Nat.gcdB m n : ZMod m))
        (ZMod.stdAddChar.mulShift (Nat.gcdA m n : ZMod n))).compAddMonoidHom
          (ZMod.chineseRemainder hmn).toAddMonoidHom := by
  have hab : (m : ℤ)*Nat.gcdA m n + (n : ℤ)*Nat.gcdB m n = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hmn.gcd_eq_one]
    rfl
  ext x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  simpa [productChar, AddChar.compAddMonoidHom_apply, AddChar.mulShift_apply,
    ← Int.cast_mul] using stdAddChar_bezout m n (Nat.gcdA m n) (Nat.gcdB m n) z hab

end ErdosKloosterman

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_KloostermanCRT
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman

attribute [local instance] Classical.decEq

theorem sum_mulShift {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (r a b : R) :
    sum (ψ.mulShift r) a b = sum ψ (r*a) (r*b) := by
  unfold sum
  apply Finset.sum_congr rfl
  intro u _
  rw [AddChar.mulShift_apply]
  congr 1
  ring

theorem standardSum_crt (m n : ℕ) [NeZero m] [NeZero n] (hmn : m.Coprime n)
    (h k : ℤ) :
    standardSum (m*n) h k =
      standardSum m (Nat.gcdB m n * h) (Nat.gcdB m n * k) *
        standardSum n (Nat.gcdA m n * h) (Nat.gcdA m n * k) := by
  unfold standardSum
  rw [stdAddChar_crt m n hmn, sum_product_ringEquiv]
  simp only [map_intCast, Prod.fst_intCast, Prod.snd_intCast, sum_mulShift,
    Int.cast_mul]

theorem norm_standardSum_crt (m n : ℕ) [NeZero m] [NeZero n] (hmn : m.Coprime n)
    (h k : ℤ) :
    ‖standardSum (m*n) h k‖ =
      ‖standardSum m (Nat.gcdB m n * h) (Nat.gcdB m n * k)‖ *
        ‖standardSum n (Nat.gcdA m n * h) (Nat.gcdA m n * k)‖ := by
  rw [standardSum_crt m n hmn, norm_mul]

end ErdosKloosterman

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Sieve_ResidueGCDBounds
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbolaError

theorem gcd_three_le_second (N x y : ℕ) (hN : 0 < N) :
    Nat.gcd N (Nat.gcd x y) ≤ Nat.gcd y N := by
  apply Nat.le_of_dvd (Nat.gcd_pos_of_pos_right y hN)
  exact Nat.dvd_gcd ((Nat.gcd_dvd_right N (Nat.gcd x y)).trans (Nat.gcd_dvd_right x y))
    (Nat.gcd_dvd_left N (Nat.gcd x y))

theorem gcd_natCast_val (N : ℕ) [NeZero N] (x : ℕ) :
    Nat.gcd ((x : ZMod N).val) N = Nat.gcd x N := by
  rw [ZMod.val_natCast, ← Nat.gcd_rec, Nat.gcd_comm N]

theorem gcd_shift_le (H T x j : ℕ) (hH : 0 < H) (hT : 0 < T) :
    Nat.gcd (x+H*j) (H*T) ≤ T * Nat.gcd x (H*T) := by
  let g := Nat.gcd (x+H*j) (H*T)
  have hgx : g ∣ x+H*j := Nat.gcd_dvd_left _ _
  have hgN : g ∣ H*T := Nat.gcd_dvd_right _ _
  have hsum : g ∣ T*(x+H*j) := dvd_mul_of_dvd_right hgx T
  have hNj : g ∣ (H*T)*j := dvd_mul_of_dvd_left hgN j
  have he : T*(x+H*j) = T*x+(H*T)*j := by ring
  rw [he] at hsum
  have hTx : g ∣ T*x := (Nat.dvd_add_iff_left hNj).mpr hsum
  have hTN : g ∣ T*(H*T) := dvd_mul_of_dvd_right hgN T
  have hd : g ∣ T*Nat.gcd x (H*T) := by
    simpa only [Nat.gcd_mul_left] using Nat.dvd_gcd hTx hTN
  exact Nat.le_of_dvd (mul_pos hT (Nat.gcd_pos_of_pos_right x (mul_pos hH hT))) hd

theorem shifted_gcd_le (H T : ℕ) [NeZero H] [NeZero T]
    (h : ZMod (H*T)) (j : ZMod T) :
    Nat.gcd (h+(H : ZMod (H*T))*(j.val : ZMod (H*T))).val (H*T) ≤
      T*Nat.gcd h.val (H*T) := by
  have he : h+(H : ZMod (H*T))*(j.val : ZMod (H*T)) =
      ((h.val+H*j.val : ℕ) : ZMod (H*T)) := by simp
  rw [he, gcd_natCast_val]
  exact gcd_shift_le H T h.val j.val (NeZero.pos H) (NeZero.pos T)

end ErdosHyperbolaError

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Estimates_ScalarErrorBudget
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman

theorem dvd_frequencyGcd_iff (d N : ℕ) (h k : ℤ) :
    d ∣ frequencyGcd N h k ↔ d ∣ N ∧ (d : ℤ) ∣ h ∧ (d : ℤ) ∣ k := by
  simp only [frequencyGcd, Int.gcd_def, Nat.dvd_gcd_iff, Int.natCast_dvd]

theorem frequencyGcd_scale (N : ℕ) (c A B h k : ℤ)
    (hab : (N : ℤ)*A + c*B = 1) :
    frequencyGcd N (c*h) (c*k) = frequencyGcd N h k := by
  apply Nat.dvd_antisymm
  · obtain ⟨hdN, hdh, hdk⟩ := (dvd_frequencyGcd_iff _ _ _ _).mp
      (dvd_refl (frequencyGcd N (c*h) (c*k)))
    have hdN' : (frequencyGcd N (c*h) (c*k) : ℤ) ∣ N := by exact_mod_cast hdN
    apply (dvd_frequencyGcd_iff _ _ _ _).mpr
    refine ⟨hdN, ?_, ?_⟩
    · have hd := dvd_add (dvd_mul_of_dvd_left hdN' (A*h)) (dvd_mul_of_dvd_right hdh B)
      have heq : (N : ℤ)*(A*h) + B*(c*h) = h := by
        linear_combination h * hab
      rwa [heq] at hd
    · have hd := dvd_add (dvd_mul_of_dvd_left hdN' (A*k)) (dvd_mul_of_dvd_right hdk B)
      have heq : (N : ℤ)*(A*k) + B*(c*k) = k := by
        linear_combination k * hab
      rwa [heq] at hd
  · obtain ⟨hdN, hdh, hdk⟩ := (dvd_frequencyGcd_iff _ _ _ _).mp
      (dvd_refl (frequencyGcd N h k))
    exact (dvd_frequencyGcd_iff _ _ _ _).mpr
      ⟨hdN, dvd_mul_of_dvd_right hdh c, dvd_mul_of_dvd_right hdk c⟩

theorem frequencyGcd_coprime_mul (m n : ℕ) (hmn : m.Coprime n) (h k : ℤ) :
    frequencyGcd (m*n) h k = frequencyGcd m h k * frequencyGcd n h k := by
  apply Nat.dvd_antisymm
  · have hg : frequencyGcd (m*n) h k ∣ m*n := Nat.gcd_dvd_left _ _
    have heq := (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hmn).mpr hg
    have hd : Nat.gcd (frequencyGcd (m*n) h k) m ∣ frequencyGcd m h k := by
      apply Nat.dvd_gcd (Nat.gcd_dvd_right _ _)
      exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    have he : Nat.gcd (frequencyGcd (m*n) h k) n ∣ frequencyGcd n h k := by
      apply Nat.dvd_gcd (Nat.gcd_dvd_right _ _)
      exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    rw [← heq]
    exact Nat.mul_dvd_mul hd he
  · have hd : frequencyGcd m h k ∣ frequencyGcd (m*n) h k := by
      apply Nat.dvd_gcd
      · exact (Nat.gcd_dvd_left _ _).trans (dvd_mul_right m n)
      · exact Nat.gcd_dvd_right _ _
    have he : frequencyGcd n h k ∣ frequencyGcd (m*n) h k := by
      apply Nat.dvd_gcd
      · exact (Nat.gcd_dvd_left _ _).trans (dvd_mul_left n m)
      · exact Nat.gcd_dvd_right _ _
    exact (hmn.of_dvd (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)).mul_dvd_of_dvd_of_dvd hd he

end ErdosKloosterman

end

section

namespace ErdosKloosterman

theorem envelope_nonneg (N : ℕ) (h k : ℤ) : 0 ≤ envelope N h k := by
  unfold envelope
  positivity

theorem envelope_coprime_mul (m n : ℕ) (hmn : m.Coprime n) (h k : ℤ) :
    envelope (m*n) h k = envelope m h k * envelope n h k := by
  unfold envelope
  rw [hmn.card_divisors_mul, frequencyGcd_coprime_mul m n hmn]
  push_cast
  rw [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n),
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

theorem envelope_scale (N : ℕ) (c A B h k : ℤ)
    (hab : (N : ℤ)*A + c*B = 1) :
    envelope N (c*h) (c*k) = envelope N h k := by
  unfold envelope
  rw [frequencyGcd_scale N c A B h k hab]

theorem envelope_crt_scaled (m n : ℕ) (hmn : m.Coprime n) (h k : ℤ) :
    envelope m (Nat.gcdB m n*h) (Nat.gcdB m n*k) *
      envelope n (Nat.gcdA m n*h) (Nat.gcdA m n*k) = envelope (m*n) h k := by
  have hab : (m : ℤ)*Nat.gcdA m n + (n : ℤ)*Nat.gcdB m n = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hmn.gcd_eq_one]
    rfl
  rw [envelope_scale m (Nat.gcdB m n) (Nat.gcdA m n) n h k (by nlinarith [hab]),
      envelope_scale n (Nat.gcdA m n) (Nat.gcdB m n) m h k (by nlinarith [hab]),
      envelope_coprime_mul m n hmn]

theorem standardSum_one (h k : ℤ) : standardSum 1 h k = 1 := by
  let : DecidableEq (ZMod 1) := Classical.decEq _
  have h0 : (h : ZMod 1) = 0 := Subsingleton.elim _ _
  have k0 : (k : ZMod 1) = 0 := Subsingleton.elim _ _
  have hc : Fintype.card (ZMod 1)ˣ = 1 := Fintype.card_unique
  simp only [standardSum, h0, k0, sum_zero_zero, hc, Nat.cast_one]

theorem envelope_one (h k : ℤ) : envelope 1 h k = 1 := by
  simp [envelope, frequencyGcd]

theorem boundAt_zero : BoundAt 0 := by
  intro h0 h k
  exact False.elim (NeZero.ne 0 rfl)

theorem boundAt_one : BoundAt 1 := by
  intro _ h k
  simp [standardSum_one, envelope_one]

theorem boundAt_coprime (m n : ℕ) (hm : 1 < m) (hn : 1 < n) (hmn : m.Coprime n)
    (hbm : BoundAt m) (hbn : BoundAt n) : BoundAt (m*n) := by
  let : NeZero m := ⟨by omega⟩
  let : NeZero n := ⟨by omega⟩
  intro _ h k
  rw [norm_standardSum_crt m n hmn]
  calc
    _ ≤ envelope m (Nat.gcdB m n*h) (Nat.gcdB m n*k) *
        envelope n (Nat.gcdA m n*h) (Nat.gcdA m n*k) :=
      mul_le_mul (hbm _ _) (hbn _ _) (norm_nonneg _) (envelope_nonneg _ _ _)
    _ = _ := envelope_crt_scaled m n hmn h k

theorem boundAt_all_of_prime_powers
    (local_bound : ∀ p a : ℕ, p.Prime → 0 < a → BoundAt (p^a)) :
    ∀ N : ℕ, BoundAt N :=
  Nat.recOnPosPrimePosCoprime local_bound boundAt_zero boundAt_one boundAt_coprime

end ErdosKloosterman

end

section

open scoped BigOperators
namespace ErdosHyperbolaIdentities

attribute [local instance] Classical.decEq

private theorem restricted_phase (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c u : (ZMod (H*T))ˣ) (h k : ZMod (H*T)) (j : ZMod T) :
    ZMod.stdAddChar (-j*(a : ZMod T)) *
      ZMod.stdAddChar ((h+(H : ZMod (H*T))*(j.val : ZMod (H*T)))*(u : ZMod (H*T)) +
        (k*(c : ZMod (H*T)))*(↑u⁻¹ : ZMod (H*T))) =
      ZMod.stdAddChar (h*(u : ZMod (H*T)) + k*(c : ZMod (H*T))*(↑u⁻¹ : ZMod (H*T))) *
        ZMod.stdAddChar (j*((ZMod.unitsMap (dvd_mul_left T H) u : ZMod T)-(a : ZMod T))) := by
  have he : (h+(H : ZMod (H*T))*(j.val : ZMod (H*T)))*(u : ZMod (H*T)) +
      (k*(c : ZMod (H*T)))*(↑u⁻¹ : ZMod (H*T)) =
      (h*(u : ZMod (H*T)) + k*(c : ZMod (H*T))*(↑u⁻¹ : ZMod (H*T))) +
        (H : ZMod (H*T))*((j.val : ZMod (H*T))*(u : ZMod (H*T))) := by ring
  rw [he, AddChar.map_add_eq_mul, ErdosKloosterman.PrimePower.standard_character_reduction]
  have hred : ErdosKloosterman.PrimePower.reduction H T
      ((j.val : ZMod (H*T))*(u : ZMod (H*T))) =
      j*(ZMod.unitsMap (dvd_mul_left T H) u : ZMod T) := by
    simp only [map_mul, map_natCast, ZMod.natCast_zmod_val,
      ErdosKloosterman.PrimePower.reduction, ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe]
  rw [hred]
  have hc : ZMod.stdAddChar (-j*(a : ZMod T)) *
      ZMod.stdAddChar (j*(ZMod.unitsMap (dvd_mul_left T H) u : ZMod T)) =
      ZMod.stdAddChar (j*((ZMod.unitsMap (dvd_mul_left T H) u : ZMod T)-(a : ZMod T))) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  calc
    _ = ZMod.stdAddChar (h*(u : ZMod (H*T)) + k*(c : ZMod (H*T))*(↑u⁻¹ : ZMod (H*T))) *
        (ZMod.stdAddChar (-j*(a : ZMod T)) *
          ZMod.stdAddChar (j*(ZMod.unitsMap (dvd_mul_left T H) u : ZMod T))) := by ring
    _ = _ := by rw [hc]

theorem restricted_average_mul (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (h k : ZMod (H*T)) :
    (∑ j : ZMod T, ZMod.stdAddChar (-j*(a : ZMod T)) *
      ErdosKloosterman.sum ZMod.stdAddChar
        (h+(H : ZMod (H*T))*(j.val : ZMod (H*T))) (k*(c : ZMod (H*T)))) =
      (T : ℂ) * restrictedSum (H*T) T (dvd_mul_left T H) a c h k := by
  unfold ErdosKloosterman.sum
  simp_rw [Finset.mul_sum, restricted_phase]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar T)]
  have he (u : (ZMod (H*T))ˣ) :
      ((ZMod.unitsMap (dvd_mul_left T H) u : ZMod T)-(a : ZMod T) = 0) ↔
        ZMod.unitsMap (dvd_mul_left T H) u = a := by rw [sub_eq_zero, Units.val_inj]
  simp_rw [he]
  simp [restrictedSum, unitClass, Finset.sum_filter, Finset.mul_sum, mul_comm]
  apply Finset.sum_congr (by ext u; simp)
  intro u _
  rfl

theorem restricted_average (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (h k : ZMod (H*T)) :
    restrictedSum (H*T) T (dvd_mul_left T H) a c h k =
      (∑ j : ZMod T, ZMod.stdAddChar (-j*(a : ZMod T)) *
        ErdosKloosterman.sum ZMod.stdAddChar
          (h+(H : ZMod (H*T))*(j.val : ZMod (H*T))) (k*(c : ZMod (H*T))))/(T : ℂ) := by
  have hT : (T : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne T
  apply (eq_div_iff hT).mpr
  simpa only [mul_comm] using (restricted_average_mul H T a c h k).symm

end ErdosHyperbolaIdentities

end

section

namespace ErdosKloosterman

theorem boundAt_prime_power (p a : ℕ) (hp : p.Prime) (ha : 0 < a) : BoundAt (p^a) := by
  let : Fact p.Prime := ⟨hp⟩
  intro _ h k
  have hc : (p^a).divisors.card = a+1 := by
    rw [← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  simpa only [envelope, frequencyGcd, hc] using
    PrimePower.standardSum_prime_power_bound p a ha h k

theorem standardSum_bound (N : ℕ) [NeZero N] (h k : ℤ) :
    ‖standardSum N h k‖ ≤
      (N.divisors.card : ℝ)^2 * (N : ℝ)^((3 : ℝ)/4) *
        ((Nat.gcd N (Int.gcd h k) : ℕ) : ℝ)^((1 : ℝ)/4) :=
  boundAt_all_of_prime_powers boundAt_prime_power N h k

theorem standardSum_bound_half_gcd (N : ℕ) [NeZero N] (h k : ℤ) :
    ‖standardSum N h k‖ ≤
      (N.divisors.card : ℝ)^2 * (N : ℝ)^((3 : ℝ)/4) *
        ((Nat.gcd N (Int.gcd h k) : ℕ) : ℝ)^((1 : ℝ)/2) := by
  have hg : 0 < Nat.gcd N (Int.gcd h k) := Nat.gcd_pos_of_pos_left _ (NeZero.pos N)
  have hg1 : (1 : ℝ) ≤ ((Nat.gcd N (Int.gcd h k) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hg)
  exact (standardSum_bound N h k).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hg1 (by norm_num)) (by positivity))

end ErdosKloosterman

end

section

namespace ErdosHyperbolaError

theorem completeScale_nonneg (N : ℕ) : 0 ≤ completeScale N := by
  unfold completeScale
  positivity

theorem sum_as_standard (N : ℕ) [NeZero N] (h k : ZMod N) :
    ErdosKloosterman.sum ZMod.stdAddChar h k =
      ErdosKloosterman.standardSum N (h.val : ℤ) (k.val : ℤ) := by
  simp only [ErdosKloosterman.standardSum, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem norm_sum_le_sqrt_second (N : ℕ) [NeZero N] (h k : ZMod N) :
    ‖ErdosKloosterman.sum ZMod.stdAddChar h k‖ ≤
      completeScale N * Real.sqrt (Nat.gcd k.val N) := by
  have hb := ErdosKloosterman.standardSum_bound_half_gcd N (h.val : ℤ) (k.val : ℤ)
  rw [← sum_as_standard N h k] at hb
  simp only [Int.gcd_def, Int.natAbs_natCast, ← Real.sqrt_eq_rpow] at hb
  have hg : (Nat.gcd N (Nat.gcd h.val k.val) : ℝ) ≤ Nat.gcd k.val N := by
    exact_mod_cast gcd_three_le_second N h.val k.val (NeZero.pos N)
  exact hb.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg) (completeScale_nonneg N))

theorem norm_sum_le_sqrt_first (N : ℕ) [NeZero N] (h k : ZMod N) :
    ‖ErdosKloosterman.sum ZMod.stdAddChar h k‖ ≤
      completeScale N * Real.sqrt (Nat.gcd h.val N) := by
  rw [ErdosKloosterman.sum_swap]
  exact norm_sum_le_sqrt_second N k h

end ErdosHyperbolaError

end

section

open scoped BigOperators
namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

theorem logFactor_one_le (N : ℕ) [NeZero N] : 1 ≤ logFactor N := by
  have hm : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, NeZero.pos N⟩
  have hh := Finset.single_le_sum (s := Finset.Icc 1 N) (f := fun n : ℕ => 1/(n : ℝ))
    (fun _ _ => by positivity) hm
  have hh' : (1 : ℝ) ≤ ErdosHyperbola.harmonicWeight N := by
    simpa only [Nat.cast_one, div_one, ErdosHyperbola.harmonicWeight] using hh
  exact hh'.trans (ErdosHyperbola.harmonicWeight_log_le N (NeZero.pos N))

theorem sqrt_modulus_one_le (T : ℕ) [NeZero T] : 1 ≤ Real.sqrt T := by
  have hT : (1 : ℝ) ≤ T := by exact_mod_cast NeZero.pos T
  simpa using Real.sqrt_le_sqrt hT

theorem l1Norm_le_logFactor (N : ℕ) [NeZero N] (P : ProgressionInterval) (hP : P.step.Coprime N) :
    l1Norm N P ≤ 2*(N : ℝ)*logFactor N := by
  calc
    _ ≤ _ := l1Norm_le N P hP
    _ = _ := by unfold logFactor; ring

theorem gcdL1Norm_le_logFactor (N : ℕ) [NeZero N] (P : ProgressionInterval) (hP : P.step.Coprime N) :
    gcdL1Norm N P ≤ 2*(N : ℝ)*(N.divisors.card : ℝ)*logFactor N := by
  calc
    _ ≤ _ := gcdL1Norm_le N P hP
    _ = _ := by unfold logFactor; ring

end ErdosHyperbolaError

end

section

open scoped BigOperators
namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

theorem restrictedSum_norm_le_average (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (h k : ZMod (H*T)) :
    ‖restrictedSum (H*T) T (dvd_mul_left T H) a c h k‖ ≤
      (∑ j : ZMod T, ‖ErdosKloosterman.sum ZMod.stdAddChar
        (h+(H : ZMod (H*T))*(j.val : ZMod (H*T))) (k*(c : ZMod (H*T)))‖)/(T : ℝ) := by
  rw [restricted_average, norm_div]
  have ht : ‖(T : ℂ)‖ = (T : ℝ) := by simp
  rw [ht]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg T)
  calc
    _ ≤ ∑ j : ZMod T, ‖ZMod.stdAddChar (-j*(a : ZMod T)) *
        ErdosKloosterman.sum ZMod.stdAddChar
          (h+(H : ZMod (H*T))*(j.val : ZMod (H*T))) (k*(c : ZMod (H*T)))‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_mul, AddChar.norm_apply, one_mul]

theorem restrictedSum_norm_le_second (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (h k : ZMod (H*T)) :
    ‖restrictedSum (H*T) T (dvd_mul_left T H) a c h k‖ ≤
      completeScale (H*T) * Real.sqrt (Nat.gcd k.val (H*T)) := by
  calc
    _ ≤ _ := restrictedSum_norm_le_average H T a c h k
    _ ≤ (∑ _j : ZMod T, completeScale (H*T) * Real.sqrt (Nat.gcd k.val (H*T)))/(T : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg T)
      apply Finset.sum_le_sum
      intro j _
      have hb := norm_sum_le_sqrt_second (H*T)
        (h+(H : ZMod (H*T))*(j.val : ZMod (H*T))) (k*(c : ZMod (H*T)))
      rw [ErdosHyperbola.gcd_mul_unit] at hb
      exact hb
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      have ht : (T : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne T
      field_simp

theorem restrictedSum_norm_le_first (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (h k : ZMod (H*T)) :
    ‖restrictedSum (H*T) T (dvd_mul_left T H) a c h k‖ ≤
      completeScale (H*T) * Real.sqrt T * Real.sqrt (Nat.gcd h.val (H*T)) := by
  calc
    _ ≤ _ := restrictedSum_norm_le_average H T a c h k
    _ ≤ (∑ _j : ZMod T, completeScale (H*T) * Real.sqrt T *
        Real.sqrt (Nat.gcd h.val (H*T)))/(T : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg T)
      apply Finset.sum_le_sum
      intro j _
      have hg : (Nat.gcd (h+(H : ZMod (H*T))*(j.val : ZMod (H*T))).val (H*T) : ℝ) ≤
          (T : ℝ) * Nat.gcd h.val (H*T) := by
        exact_mod_cast shifted_gcd_le H T h j
      calc
        _ ≤ _ := norm_sum_le_sqrt_first (H*T)
          (h+(H : ZMod (H*T))*(j.val : ZMod (H*T))) (k*(c : ZMod (H*T)))
        _ ≤ completeScale (H*T) * Real.sqrt ((T : ℝ)*Nat.gcd h.val (H*T)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg) (completeScale_nonneg _)
        _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg T)]; ring
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      have ht : (T : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne T
      field_simp

end ErdosHyperbolaError

end

section

namespace ErdosHyperbolaError

theorem axis_quadrant_budget (D d s t n U V : ℝ) (hD : 0 ≤ D) (hd : 0 ≤ d)
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hn : 1 ≤ n) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    D*((2*n*d*t)*(U+1)+s*(2*n*d*t)*(V+1)+(2*n*t)*(2*n*d*t))/n^2 ≤
      8*(D*d*s*t^2)*(1+U/n+V/n) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have ht2 : t ≤ t^2 := by nlinarith
  have hst : t ≤ s*t^2 := by
    calc
      _ ≤ t^2 := ht2
      _ = 1*t^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hs (sq_nonneg t)
  let E := D*d*s*t^2
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have hA : D*((2*n*d*t)*(U+1)) ≤ 2*E*n*(U+1) := by
    calc
      _ = (2*D*n*d)*(U+1)*t := by ring
      _ ≤ (2*D*n*d)*(U+1)*(s*t^2) := mul_le_mul_of_nonneg_left hst (by positivity)
      _ = _ := by dsimp [E] <;> ring
  have hB : D*(s*(2*n*d*t)*(V+1)) ≤ 2*E*n*(V+1) := by
    calc
      _ = (2*D*s*n*d)*(V+1)*t := by ring
      _ ≤ (2*D*s*n*d)*(V+1)*t^2 := mul_le_mul_of_nonneg_left ht2 (by positivity)
      _ = _ := by dsimp [E] <;> ring
  have hC : D*((2*n*t)*(2*n*d*t)) ≤ 4*E*n^2 := by
    calc
      _ = (4*D*d*n^2*t^2)*1 := by ring
      _ ≤ (4*D*d*n^2*t^2)*s := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by dsimp [E] <;> ring
  have hpoly : 2*n*(U+1)+2*n*(V+1)+4*n^2 ≤ 8*(n^2+n*U+n*V) := by
    have hn2 : n ≤ n^2 := by nlinarith
    nlinarith [mul_nonneg hn0.le hU, mul_nonneg hn0.le hV]
  have hsum : D*((2*n*d*t)*(U+1)+s*(2*n*d*t)*(V+1)+(2*n*t)*(2*n*d*t)) ≤
      8*E*(n^2+n*U+n*V) := by
    calc
      _ = D*((2*n*d*t)*(U+1))+D*(s*(2*n*d*t)*(V+1))+D*((2*n*t)*(2*n*d*t)) := by ring
      _ ≤ 2*E*n*(U+1)+2*E*n*(V+1)+4*E*n^2 := add_le_add (add_le_add hA hB) hC
      _ = E*(2*n*(U+1)+2*n*(V+1)+4*n^2) := by ring
      _ ≤ E*(8*(n^2+n*U+n*V)) := mul_le_mul_of_nonneg_left hpoly hE
      _ = _ := by ring
  calc
    _ ≤ (8*E*(n^2+n*U+n*V))/n^2 := div_le_div_of_nonneg_right hsum (sq_nonneg n)
    _ = _ := by dsimp [E]; field_simp [hn0.ne']

end ErdosHyperbolaError

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Harmonic_NormalizedSpectralError
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosHyperbolaError

theorem sum_zero_add_nonzero (N : ℕ) [NeZero N] (f : ZMod N → ℂ) :
    (∑ h : ZMod N, f h) = f 0 + ∑ h ∈ nonzeroFrequencies N, f h := by
  have he : nonzeroFrequencies N = (Finset.univ : Finset (ZMod N)).erase 0 := by
    ext h
    simp [nonzeroFrequencies]
  rw [he]
  exact (Finset.add_sum_erase Finset.univ f (Finset.mem_univ 0)).symm

theorem double_sum_decomposition (N : ℕ) [NeZero N] (F : ZMod N → ZMod N → ℂ) :
    (∑ h : ZMod N, ∑ k : ZMod N, F h k) =
      F 0 0 + (∑ h ∈ nonzeroFrequencies N, F h 0) +
        (∑ k ∈ nonzeroFrequencies N, F 0 k) +
        ∑ h ∈ nonzeroFrequencies N, ∑ k ∈ nonzeroFrequencies N, F h k := by
  rw [sum_zero_add_nonzero N (fun h => ∑ k : ZMod N, F h k), sum_zero_add_nonzero N (F 0)]
  simp_rw [sum_zero_add_nonzero N]
  rw [Finset.sum_add_distrib]
  ring

theorem double_remainder_norm_le (N : ℕ) [NeZero N] (F : ZMod N → ZMod N → ℂ) :
    ‖(∑ h : ZMod N, ∑ k : ZMod N, F h k)-F 0 0‖ ≤
      (∑ h ∈ nonzeroFrequencies N, ‖F h 0‖) +
        (∑ k ∈ nonzeroFrequencies N, ‖F 0 k‖) +
        ∑ h ∈ nonzeroFrequencies N, ∑ k ∈ nonzeroFrequencies N, ‖F h k‖ := by
  let X := ∑ h ∈ nonzeroFrequencies N, F h 0
  let Y := ∑ k ∈ nonzeroFrequencies N, F 0 k
  let Z := ∑ h ∈ nonzeroFrequencies N, ∑ k ∈ nonzeroFrequencies N, F h k
  rw [double_sum_decomposition]
  change ‖F 0 0+X+Y+Z-F 0 0‖ ≤ _
  rw [show F 0 0+X+Y+Z-F 0 0 = X+Y+Z by ring]
  have hX : ‖X‖ ≤ ∑ h ∈ nonzeroFrequencies N, ‖F h 0‖ := norm_sum_le _ _
  have hY : ‖Y‖ ≤ ∑ k ∈ nonzeroFrequencies N, ‖F 0 k‖ := norm_sum_le _ _
  have hZ : ‖Z‖ ≤ ∑ h ∈ nonzeroFrequencies N, ∑ k ∈ nonzeroFrequencies N, ‖F h k‖ := by
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun h _ => norm_sum_le _ _))
  calc
    _ ≤ ‖X+Y‖+‖Z‖ := norm_add_le _ _
    _ ≤ ‖X‖+‖Y‖+‖Z‖ := add_le_add (norm_add_le X Y) le_rfl
    _ ≤ _ := add_le_add (add_le_add hX hY) hZ

end ErdosHyperbolaError

end

section

open scoped BigOperators
namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

theorem spectral_remainder_bound (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (P Q : ProgressionInterval) :
    ‖(∑ h : ZMod (H*T), ∑ k : ZMod (H*T), spectralTerm H T a c P Q h k)-
      spectralTerm H T a c P Q 0 0‖ ≤
      ‖Q.weight (H*T) 0‖ * completeScale (H*T) * Real.sqrt T * gcdL1Norm (H*T) P +
      ‖P.weight (H*T) 0‖ * completeScale (H*T) * gcdL1Norm (H*T) Q +
      completeScale (H*T) * l1Norm (H*T) P * gcdL1Norm (H*T) Q := by
  have hleft : (∑ h ∈ nonzeroFrequencies (H*T), ‖spectralTerm H T a c P Q h 0‖) ≤
      ‖Q.weight (H*T) 0‖ * completeScale (H*T) * Real.sqrt T * gcdL1Norm (H*T) P := by
    unfold gcdL1Norm
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h _
    rw [spectralTerm, norm_mul, norm_mul]
    calc
      _ ≤ (‖P.weight (H*T) h‖*‖Q.weight (H*T) 0‖) *
          (completeScale (H*T)*Real.sqrt T*Real.sqrt (Nat.gcd h.val (H*T))) :=
        mul_le_mul_of_nonneg_left (restrictedSum_norm_le_first H T a c h 0) (by positivity)
      _ = _ := by ring
  have hright : (∑ k ∈ nonzeroFrequencies (H*T), ‖spectralTerm H T a c P Q 0 k‖) ≤
      ‖P.weight (H*T) 0‖ * completeScale (H*T) * gcdL1Norm (H*T) Q := by
    unfold gcdL1Norm
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    rw [spectralTerm, norm_mul, norm_mul]
    calc
      _ ≤ (‖P.weight (H*T) 0‖*‖Q.weight (H*T) k‖) *
          (completeScale (H*T)*Real.sqrt (Nat.gcd k.val (H*T))) :=
        mul_le_mul_of_nonneg_left (restrictedSum_norm_le_second H T a c 0 k) (by positivity)
      _ = _ := by ring
  have hboth : (∑ h ∈ nonzeroFrequencies (H*T), ∑ k ∈ nonzeroFrequencies (H*T),
      ‖spectralTerm H T a c P Q h k‖) ≤
        completeScale (H*T)*l1Norm (H*T) P*gcdL1Norm (H*T) Q := by
    have hp (h k : ZMod (H*T)) : ‖spectralTerm H T a c P Q h k‖ ≤
        completeScale (H*T)*‖P.weight (H*T) h‖ *
          (‖Q.weight (H*T) k‖*Real.sqrt (Nat.gcd k.val (H*T))) := by
      rw [spectralTerm, norm_mul, norm_mul]
      calc
        _ ≤ (‖P.weight (H*T) h‖*‖Q.weight (H*T) k‖) *
            (completeScale (H*T)*Real.sqrt (Nat.gcd k.val (H*T))) :=
          mul_le_mul_of_nonneg_left (restrictedSum_norm_le_second H T a c h k) (by positivity)
        _ = _ := by ring
    calc
      _ ≤ ∑ h ∈ nonzeroFrequencies (H*T), ∑ k ∈ nonzeroFrequencies (H*T),
          completeScale (H*T)*‖P.weight (H*T) h‖ *
            (‖Q.weight (H*T) k‖*Real.sqrt (Nat.gcd k.val (H*T))) :=
        Finset.sum_le_sum (fun h _ => Finset.sum_le_sum (fun k _ => hp h k))
      _ = _ := by
        unfold l1Norm gcdL1Norm
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
  exact (double_remainder_norm_le (H*T) (spectralTerm H T a c P Q)).trans
    (add_le_add (add_le_add hleft hright) hboth)

end ErdosHyperbolaError

end

section

open scoped BigOperators
namespace ErdosHyperbolaError

open ErdosHyperbolaIdentities

theorem normalized_spectral_error_jb247_oai (H T : ℕ) [NeZero H] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod (H*T))ˣ) (P Q : ProgressionInterval)
    (hP : P.left ≤ P.right) (hQ : Q.left ≤ Q.right)
    (hPN : P.step.Coprime (H*T)) (hQN : Q.step.Coprime (H*T)) :
    ‖(∑ h : ZMod (H*T), ∑ k : ZMod (H*T), spectralTerm H T a c P Q h k)-
      spectralTerm H T a c P Q 0 0‖/((H*T : ℕ) : ℝ)^2 ≤
      8*errorBase (H*T) T*(1+intervalLength P/((H*T : ℕ) : ℝ)+intervalLength Q/((H*T : ℕ) : ℝ)) := by
  have hD := completeScale_nonneg (H*T)
  have hs := Real.sqrt_nonneg (T : ℝ)
  have ht : 0 ≤ logFactor (H*T) := le_trans (by norm_num) (logFactor_one_le (H*T))
  have hU := intervalLength_nonneg P hP
  have hV := intervalLength_nonneg Q hQ
  have hA0 := norm_weight_zero_le (H*T) P hP
  have hB0 := norm_weight_zero_le (H*T) Q hQ
  have hA := l1Norm_le_logFactor (H*T) P hPN
  have hAg := gcdL1Norm_le_logFactor (H*T) P hPN
  have hBg := gcdL1Norm_le_logFactor (H*T) Q hQN
  have hAg0 := gcdL1Norm_nonneg (H*T) P
  have hBg0 := gcdL1Norm_nonneg (H*T) Q
  have hApos := l1Norm_nonneg (H*T) P
  have hnum : ‖(∑ h : ZMod (H*T), ∑ k : ZMod (H*T), spectralTerm H T a c P Q h k)-
      spectralTerm H T a c P Q 0 0‖ ≤
      completeScale (H*T)*
        ((2*((H*T : ℕ) : ℝ)*((H*T).divisors.card : ℝ)*logFactor (H*T))*(intervalLength P+1)+
          Real.sqrt T*(2*((H*T : ℕ) : ℝ)*((H*T).divisors.card : ℝ)*logFactor (H*T))*(intervalLength Q+1)+
          (2*((H*T : ℕ) : ℝ)*logFactor (H*T))*
            (2*((H*T : ℕ) : ℝ)*((H*T).divisors.card : ℝ)*logFactor (H*T))) := by
    calc
      _ ≤ _ := spectral_remainder_bound H T a c P Q
      _ ≤ (intervalLength Q+1)*completeScale (H*T)*Real.sqrt T*
          (2*((H*T : ℕ) : ℝ)*((H*T).divisors.card : ℝ)*logFactor (H*T))+
          (intervalLength P+1)*completeScale (H*T)*
            (2*((H*T : ℕ) : ℝ)*((H*T).divisors.card : ℝ)*logFactor (H*T))+
          completeScale (H*T)*(2*((H*T : ℕ) : ℝ)*logFactor (H*T))*
            (2*((H*T : ℕ) : ℝ)*((H*T).divisors.card : ℝ)*logFactor (H*T)) := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ _ := div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ ≤ _ := axis_quadrant_budget (completeScale (H*T)) ((H*T).divisors.card : ℝ)
      (Real.sqrt T) (logFactor (H*T)) ((H*T : ℕ) : ℝ) (intervalLength P) (intervalLength Q)
      hD (Nat.cast_nonneg _) (sqrt_modulus_one_le T) (logFactor_one_le (H*T))
      (by exact_mod_cast Nat.mul_pos (NeZero.pos H) (NeZero.pos T)) hU hV

end ErdosHyperbolaError

end

end Erdos970

end OAI
end

theorem solution : type_of% @OAI.Erdos970.ErdosHyperbolaError.normalized_spectral_error_jb247_oai := @OAI.Erdos970.ErdosHyperbolaError.normalized_spectral_error_jb247_oai
