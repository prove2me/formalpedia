-- Prove2me | solution 1 for OAI.DimensionTen.fixed_mod139_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:03:28.628897+00:00
-- url     : https://prove2.me/submissions/71233872-8f07-41b0-ab63-efc9eb4bd360

import Mathlib
import Definitions.Def_OAIQ057D009

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_FrobeniusRoots
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen

lemma iterate_pow_perm {ι R : Type*} [Monoid R] (σ : Equiv.Perm ι) (r : ι → R)
    (p : ℕ) (h : ∀ i, r (σ i) = r i ^ p) (n : ℕ) :
    ∀ i, r ((σ ^ n) i) = r i ^ (p ^ n) := by
  induction n with
  | zero => intro i; simp
  | succ n ih =>
    intro i
    rw [pow_succ', Equiv.Perm.mul_apply, h, ih, ← pow_mul, pow_succ]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Model
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

theorem initial {R : Type*} [CommRing R] (z : R) : z ^ (139 ^ 0) = u0 z := by simp [u0]

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Powers01
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

theorem pow1_2_mul_integer {R : Type*} [CommRing R] (z : R) :
    u0 z * u0 z = pow1_2_q z * f z + pow1_2 z + (139 : R) * pow1_2_mul_t z := by
  simp only [u0, pow1_2_q, f, pow1_2, pow1_2_mul_t]
  
  ring

theorem pow1_2_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    u0 z * u0 z = pow1_2_q z * f z + pow1_2 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_2_mul_integer z


theorem pow1_2_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z * u0 z = pow1_2 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_2_mul z


theorem pow1_2_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 2 = pow1_2 z := by
  calc
    _ = u0 z ^ 1 * u0 z ^ 1 := by ring
    _ = u0 z * u0 z := by simp only [pow_one]
    _ = _ := pow1_2_root z hz


theorem pow1_4_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_2 z * pow1_2 z = pow1_4_q z * f z + pow1_4 z + (139 : R) * pow1_4_mul_t z := by
  simp only [pow1_2, pow1_4_q, f, pow1_4, pow1_4_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_4_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_2 z * pow1_2 z = pow1_4_q z * f z + pow1_4 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_4_mul_integer z


theorem pow1_4_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_2 z * pow1_2 z = pow1_4 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_4_mul z


theorem pow1_4_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 4 = pow1_4 z := by
  calc
    _ = u0 z ^ 2 * u0 z ^ 2 := by ring
    _ = pow1_2 z * pow1_2 z := by rw [pow1_2_pow z hz]
    _ = _ := pow1_4_root z hz


theorem pow1_8_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_4 z * pow1_4 z = pow1_8_q z * f z + pow1_8 z + (139 : R) * pow1_8_mul_t z := by
  simp only [pow1_4, pow1_8_q, f, pow1_8, pow1_8_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_8_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_4 z * pow1_4 z = pow1_8_q z * f z + pow1_8 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_8_mul_integer z


theorem pow1_8_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_4 z * pow1_4 z = pow1_8 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_8_mul z


theorem pow1_8_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 8 = pow1_8 z := by
  calc
    _ = u0 z ^ 4 * u0 z ^ 4 := by ring
    _ = pow1_4 z * pow1_4 z := by rw [pow1_4_pow z hz]
    _ = _ := pow1_8_root z hz


theorem pow1_16_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_8 z * pow1_8 z = pow1_16_q z * f z + pow1_16 z + (139 : R) * pow1_16_mul_t z := by
  simp only [pow1_8, pow1_16_q, f, pow1_16, pow1_16_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_16_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_8 z * pow1_8 z = pow1_16_q z * f z + pow1_16 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_16_mul_integer z


theorem pow1_16_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_8 z * pow1_8 z = pow1_16 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_16_mul z


theorem pow1_16_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 16 = pow1_16 z := by
  calc
    _ = u0 z ^ 8 * u0 z ^ 8 := by ring
    _ = pow1_8 z * pow1_8 z := by rw [pow1_8_pow z hz]
    _ = _ := pow1_16_root z hz


theorem pow1_17_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_16 z * u0 z = pow1_17_q z * f z + pow1_17 z + (139 : R) * pow1_17_mul_t z := by
  simp only [pow1_16, u0, pow1_17_q, f, pow1_17, pow1_17_mul_t]
  simp only [pow1_2_q]
  ring

theorem pow1_17_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_16 z * u0 z = pow1_17_q z * f z + pow1_17 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_17_mul_integer z


theorem pow1_17_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_16 z * u0 z = pow1_17 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_17_mul z


theorem pow1_17_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 17 = pow1_17 z := by
  rw [show 17 = 16 + 1 by rfl, pow_succ, pow1_16_pow z hz]
  exact pow1_17_root z hz


theorem pow1_34_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_17 z * pow1_17 z = pow1_34_q z * f z + pow1_34 z + (139 : R) * pow1_34_mul_t z := by
  simp only [pow1_17, pow1_34_q, f, pow1_34, pow1_34_mul_t]
  
  ring

theorem pow1_34_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_17 z * pow1_17 z = pow1_34_q z * f z + pow1_34 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_34_mul_integer z


theorem pow1_34_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_17 z * pow1_17 z = pow1_34 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_34_mul z


theorem pow1_34_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 34 = pow1_34 z := by
  calc
    _ = u0 z ^ 17 * u0 z ^ 17 := by ring
    _ = pow1_17 z * pow1_17 z := by rw [pow1_17_pow z hz]
    _ = _ := pow1_34_root z hz


theorem pow1_68_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_34 z * pow1_34 z = pow1_68_q z * f z + pow1_68 z + (139 : R) * pow1_68_mul_t z := by
  simp only [pow1_34, pow1_68_q, f, pow1_68, pow1_68_mul_t]
  
  ring

theorem pow1_68_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_34 z * pow1_34 z = pow1_68_q z * f z + pow1_68 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_68_mul_integer z


theorem pow1_68_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_34 z * pow1_34 z = pow1_68 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_68_mul z


theorem pow1_68_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 68 = pow1_68 z := by
  calc
    _ = u0 z ^ 34 * u0 z ^ 34 := by ring
    _ = pow1_34 z * pow1_34 z := by rw [pow1_34_pow z hz]
    _ = _ := pow1_68_root z hz


theorem pow1_69_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_68 z * u0 z = pow1_69_q z * f z + pow1_69 z + (139 : R) * pow1_69_mul_t z := by
  simp only [pow1_68, u0, pow1_69_q, f, pow1_69, pow1_69_mul_t]
  
  ring

theorem pow1_69_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_68 z * u0 z = pow1_69_q z * f z + pow1_69 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_69_mul_integer z


theorem pow1_69_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_68 z * u0 z = pow1_69 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_69_mul z


theorem pow1_69_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 69 = pow1_69 z := by
  rw [show 69 = 68 + 1 by rfl, pow_succ, pow1_68_pow z hz]
  exact pow1_69_root z hz


theorem pow1_138_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_69 z * pow1_69 z = pow1_138_q z * f z + pow1_138 z + (139 : R) * pow1_138_mul_t z := by
  simp only [pow1_69, pow1_138_q, f, pow1_138, pow1_138_mul_t]
  
  ring

theorem pow1_138_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_69 z * pow1_69 z = pow1_138_q z * f z + pow1_138 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_138_mul_integer z


theorem pow1_138_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_69 z * pow1_69 z = pow1_138 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_138_mul z


theorem pow1_138_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 138 = pow1_138 z := by
  calc
    _ = u0 z ^ 69 * u0 z ^ 69 := by ring
    _ = pow1_69 z * pow1_69 z := by rw [pow1_69_pow z hz]
    _ = _ := pow1_138_root z hz


theorem pow1_139_mul_integer {R : Type*} [CommRing R] (z : R) :
    pow1_138 z * u0 z = pow1_139_q z * f z + pow1_139 z + (139 : R) * pow1_139_mul_t z := by
  simp only [pow1_138, u0, pow1_139_q, f, pow1_139, pow1_139_mul_t]
  
  ring

theorem pow1_139_mul {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    pow1_138 z * u0 z = pow1_139_q z * f z + pow1_139 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using pow1_139_mul_integer z


theorem pow1_139_root {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : pow1_138 z * u0 z = pow1_139 z := by
  simpa only [hz, mul_zero, zero_add] using pow1_139_mul z


theorem pow1_139_pow {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : u0 z ^ 139 = pow1_139 z := by
  rw [show 139 = 138 + 1 by rfl, pow_succ, pow1_138_pow z hz]
  exact pow1_139_root z hz


theorem iterate1 {R : Type*} [CommRing R] [CharP R 139]
    (z : R) (hz : f z = 0) : z ^ (139 ^ 1) = u1 z := by
  calc
    _ = (z ^ (139 ^ 0)) ^ 139 := by rw [← pow_mul]; rfl
    _ = u0 z ^ 139 := congrArg (fun x : R => x ^ 139) (initial z )
    _ = _ := pow1_139_pow z hz


end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Mod139Result
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

theorem bezout1_integer {R : Type*} [CommRing R] (z : R) :
    a1 z * f z + b1 z * (u1 z - z) = g1 z + (139 : R) * bezout1_t z := by
  simp only [a1, b1, f, u1, g1, bezout1_t]
  simp only [pow1_139]
  ring

theorem bezout1 {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    a1 z * f z + b1 z * (u1 z - z) = g1 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using bezout1_integer z


theorem factor1_f_integer {R : Type*} [CommRing R] (z : R) :
    f z = g1 z * div1_f z + (139 : R) * factor1_f_t z := by
  simp only [f, g1, div1_f, factor1_f_t]
  
  ring

theorem factor1_f {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    f z = g1 z * div1_f z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using factor1_f_integer z


theorem factor1_u1_integer {R : Type*} [CommRing R] (z : R) :
    (u1 z - z) = g1 z * div1_u1 z + (139 : R) * factor1_u1_t z := by
  simp only [u1, g1, div1_u1, factor1_u1_t]
  simp only [pow1_139]
  ring

theorem factor1_u1 {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    (u1 z - z) = g1 z * div1_u1 z := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using factor1_u1_integer z


theorem separable_bezout_integer {R : Type*} [CommRing R] (z : R) :
    da z * f z + db z * df z = 1 + (139 : R) * separable_bezout_t z := by
  simp only [da, db, df, f, separable_bezout_t]
  
  ring

theorem separable_bezout {R : Type*} [CommRing R] [CharP R 139] (z : R) :
    da z * f z + db z * df z = 1 := by
  have h : (139 : R) = 0 := CharP.cast_eq_zero R 139
  simpa only [h, zero_mul, add_zero] using separable_bezout_integer z

end DimensionTen.Mod139

section
noncomputable section
open Polynomial
namespace DimensionTen.Mod139

lemma horner_monic_degree {R : Type*} [CommRing R] [Nontrivial R] {p : R[X]} {n : ℕ}
    (hp : p.IsMonicOfDegree n) (a : R) :
    (C a + X * p).IsMonicOfDegree (n+1) := by
  apply (isMonicOfDegree_iff _ _).mpr
  constructor
  · rw [natDegree_C_add, monic_X.natDegree_mul hp.monic, natDegree_X, hp.natDegree_eq]
    omega
  · simp only [coeff_add, coeff_C, Nat.add_one_ne_zero, ite_false, zero_add, coeff_X_mul]
    simpa only [hp.natDegree_eq] using hp.monic.coeff_natDegree

lemma horner_zero_degree {R : Type*} [CommRing R] [Nontrivial R] {p : R[X]} {n : ℕ}
    (hp : p.IsMonicOfDegree n) : (0 + X * p).IsMonicOfDegree (n+1) := by
  simpa only [C_0] using horner_monic_degree hp 0

lemma degree_g {R : Type*} [CommRing R] [Nontrivial R] :
    (g1 (X : R[X])).IsMonicOfDegree 1 := by
  unfold g1
  repeat' first | apply horner_monic_degree | apply horner_zero_degree
  exact ⟨natDegree_one, monic_one⟩

lemma map_f {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (f z) = f (φ z) := by
  simp only [f, map_add, map_mul, map_ofNat, map_one, map_zero]

lemma map_g1 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (z : R) :
    φ (g1 z) = g1 (φ z) := by
  simp only [g1, map_add, map_mul, map_ofNat, map_one]

lemma derivative_identity {R : Type*} [CommRing R] :
    Polynomial.derivative (f (X : R[X])) = df X + (139 : R[X]) * derivative_extra X := by
  simp only [f, df, derivative_extra, derivative_add, derivative_mul, derivative_X,
    derivative_ofNat, derivative_one, derivative_zero]
  ring

lemma separable_f {k : Type*} [Field k] [CharP k 139] :
    (f (X : k[X])).Separable := by
  change IsCoprime _ _
  have h : (139 : k[X]) = 0 := CharP.cast_eq_zero _ 139
  rw [derivative_identity, h, zero_mul, add_zero]
  exact ⟨da X, db X, separable_bezout _⟩

lemma fixed_iff_g_zero {k : Type*} [Field k] [CharP k 139] (z : k) (hz : f z = 0) :
    z ^ (139 ^ 1) = z ↔ g1 z = 0 := by
  rw [iterate1 z hz]
  constructor
  · intro h
    have hb := bezout1 z
    simpa only [hz, mul_zero, h, sub_self, zero_add] using hb.symm
  · intro h
    apply sub_eq_zero.mp
    rw [factor1_u1, h, zero_mul]

end DimensionTen.Mod139

end
end

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_RootPermutation
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial
namespace DimensionTen


theorem card_fixed_of_factor {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
    (r : ι → k) (hr : Function.Injective r) (σ : Equiv.Perm ι)
    (f g : k[X]) (hf : f = ∏ i, (X - C (r i))) (hs : f.Separable)
    (hd : g ∣ f) (hroot : ∀ i, g.eval (r i) = 0 ↔ σ i = i) :
    Fintype.card {i : ι // σ i = i} = g.natDegree := by
  classical
  have hf0 : f ≠ 0 := by rw [hf]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => X_sub_C_ne_zero _)
  have hg0 : g ≠ 0 := ne_zero_of_dvd_ne_zero hf0 hd
  have hsplit : f.Splits := by rw [hf]; exact Splits.prod (fun _ _ => Splits.X_sub_C _)
  have hgr : ∀ x : k, g.eval x = 0 → ∃ i, r i = x := by
    intro x hx
    have hx' : f.eval x = 0 := by
      obtain ⟨q, rfl⟩ := hd
      simp [eval_mul, hx]
    rw [hf, eval_prod] at hx'
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hx'
    simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hi
    exact ⟨i, hi.symm⟩
  let u : {i : ι // σ i = i} → g.rootSet k :=
    fun i => ⟨r i, mem_rootSet.mpr ⟨hg0, by simpa using (hroot i).mpr i.property⟩⟩
  have hu : Function.Injective u := by
    intro i j h
    apply Subtype.ext
    apply hr
    exact congrArg Subtype.val h
  have hus : Function.Surjective u := by
    intro x
    have hx : g.eval (x : k) = 0 := by simpa using (mem_rootSet.mp x.property).2
    obtain ⟨i, hi⟩ := hgr x hx
    refine ⟨⟨i, (hroot i).mp (hi ▸ hx)⟩, ?_⟩
    exact Subtype.ext hi
  let e := Equiv.ofBijective u ⟨hu, hus⟩
  rw [Fintype.card_congr e]
  exact card_rootSet_eq_natDegree (hs.of_dvd hd) (by simpa using (hsplit.of_dvd hf0 hd))

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_ModularPermutations
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Polynomial
namespace DimensionTen

lemma root_of_product {k ι : Type*} [Field k] [Fintype ι]
    (r : ι → k) (f : k[X]) (hf : f = ∏ i, (X - C (r i))) (i : ι) :
    f.eval (r i) = 0 := by
  classical
  rw [hf, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

lemma eval_mod139_f {k : Type*} [CommRing k] (x : k) :
    (Mod139.f (X : k[X])).eval x = Mod139.f x :=
  (Mod139.map_f (evalRingHom x) X).trans (congrArg Mod139.f (eval_X))

lemma eval_mod139_g {k : Type*} [CommRing k] (x : k) :
    (Mod139.g1 (X : k[X])).eval x = Mod139.g1 x :=
  (Mod139.map_g1 (evalRingHom x) X).trans (congrArg Mod139.g1 (eval_X))

lemma fixed_mod139_s2_oai {k ι : Type*} [Field k] [CharP k 139] [Fintype ι] [DecidableEq ι]
    (r : ι → k) (hinj : Function.Injective r) (π : Equiv.Perm ι)
    (hfact : Mod139.f X = ∏ i, (X - C (r i)))
    (hfrob : ∀ i, r (π i) = r i ^ 139) :
    Fintype.card {i : ι // (π ^ 1) i = i} = 1 := by
  have hfroot (i : ι) : Mod139.f (r i) = 0 := by
    rw [← eval_mod139_f]; exact root_of_product r _ hfact i
  have hfix (i : ι) : (Mod139.g1 (X : k[X])).eval (r i) = 0 ↔ (π ^ 1) i = i := by
    rw [eval_mod139_g, ← Mod139.fixed_iff_g_zero _ (hfroot i),
      ← iterate_pow_perm π r 139 hfrob 1 i, hinj.eq_iff]
  have hd : Mod139.g1 (X : k[X]) ∣ Mod139.f X :=
    ⟨Mod139.div1_f X, Mod139.factor1_f X⟩
  exact (card_fixed_of_factor r hinj (π ^ 1) _ _ hfact Mod139.separable_f hd hfix).trans
    Mod139.degree_g.natDegree_eq

end DimensionTen

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.DimensionTen.fixed_mod139_s2_oai.{u_1, u_2} := @OAI.DimensionTen.fixed_mod139_s2_oai.{u_1, u_2}
