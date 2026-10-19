-- Prove2me | solution 1 for OAI.NCHitting.order_le_wronskian_add
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:22:14.858002+00:00
-- url     : https://prove2.me/submissions/a6e7df00-5e4f-4e58-88f3-4297aa78fb14

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/WronskianBound.lean:L33-L72
-- (upload_full_project.md Phase 4): solution for node OAI.NCHitting.order_le_wronskian_add. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FormulaHitting
import Definitions.Def_OAI_Algebra_FormulaHitting_Wronskian
import Definitions.Def_OAI_Algebra_FormulaHitting_NumeratorRows
import Definitions.Def_OAI_Algebra_FormulaHitting_OrderBasis

-- ---- from OAI.Algebra.FormulaHitting.Wronskian ----
namespace OAI

noncomputable section

namespace NCHitting

open PowerSeries Matrix

variable {F : Type*} [Field F]

theorem derivativeIter_sum {ι : Type*} (j : ℕ) (s : Finset ι) (f : ι → PowerSeries F) :
    derivativeIter j (∑ i ∈ s, f i) = ∑ i ∈ s, derivativeIter j (f i) := by
  induction j with
  | zero => rfl
  | succ j ih => simp [derivativeIter, ih]

theorem coeff_derivativeIter (j r : ℕ) (f : PowerSeries F) :
    PowerSeries.coeff r (derivativeIter j f) =
      PowerSeries.coeff (r+j) f * ((r+j).descFactorial j : F) := by
  induction j generalizing r with
  | zero => simp [derivativeIter]
  | succ j ih =>
    rw [derivativeIter, PowerSeries.coeff_derivative, ih]
    have he : r + 1 + j = r + (j + 1) := by omega
    have hs : r + (j + 1) - j = r + 1 := by omega
    rw [he, Nat.descFactorial_succ, hs, Nat.cast_mul]
    push_cast
    ring

end NCHitting

end

end OAI

-- ---- from OAI.Algebra.FormulaHitting.Minors ----
namespace OAI

noncomputable section

namespace NCHitting

open Matrix Finset Polynomial

variable {R : Type*} [CommRing R]
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

theorem dvd_det_of_column_dvd (A : Matrix I I R) (c : I) (p : R)
    (h : ∀ i, p ∣ A i c) : p ∣ A.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  apply dvd_mul_of_dvd_right
  exact (h (σ c)).trans (Finset.dvd_prod_of_mem (fun i => A (σ i) i) (Finset.mem_univ c))

end NCHitting

end

end OAI

-- ---- from OAI.Algebra.FormulaHitting.WronskianBound ----
namespace OAI

noncomputable section

namespace NCHitting

open PowerSeries Matrix Submodule

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem derivativeIter_X_dvd (f : PowerSeries F) {a j : ℕ}
    (h : a+j ≤ f.order.toNat) :
    PowerSeries.X^a ∣ derivativeIter j f := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro r hr
  rw [coeff_derivativeIter, PowerSeries.coeff_of_lt_order_toNat _ (by omega), zero_mul]

omit [CharZero F] in
theorem derivativeIter_column_X_dvd (f : PowerSeries F) {k : ℕ}
    (j : Fin k) :
    PowerSeries.X^(f.order.toNat+1-k) ∣ derivativeIter j.val f := by
  by_cases hk : k ≤ f.order.toNat+1
  · apply derivativeIter_X_dvd
    have hj := j.isLt
    omega
  · have ha : f.order.toNat+1-k = 0 := by omega
    simp [ha]

omit [CharZero F] in
theorem order_le_wronskian_add {k : ℕ} (b : Fin k → PowerSeries F)
    (hb : wronskian b ≠ 0) (y : PowerSeries F) (hy : y ≠ 0)
    (hspan : y ∈ Submodule.span F (Set.range b)) :
    y.order.toNat ≤ (wronskian b).order.toNat + k - 1 := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hspan
  have hex : ∃ l, c l ≠ 0 := by
    by_contra h
    push Not at h
    apply hy
    rw [← hc]
    simp [h]
  obtain ⟨l, hl⟩ := hex
  let W := (wronskianMatrix b).updateCol l (fun j => derivativeIter j.val y)
  have he : W.det = PowerSeries.C (c l) * wronskian b := by
    have hcol : (fun j : Fin k => derivativeIter j.val y) =
        fun j => ∑ i : Fin k, PowerSeries.C (c i) • wronskianMatrix b j i := by
      funext j
      rw [← hc, derivativeIter_sum]
      simp only [derivativeIter_smul]
      simp only [wronskianMatrix, PowerSeries.smul_eq_C_mul, smul_eq_mul]
    change ((wronskianMatrix b).updateCol l _).det = _
    rw [hcol, Matrix.det_updateCol_sum]
    rfl
  have hd : PowerSeries.X^(y.order.toNat+1-k) ∣ W.det := by
    apply dvd_det_of_column_dvd W l
    intro j
    simpa [W] using derivativeIter_column_X_dvd y j
  have hco : (PowerSeries.C (c l)).order = 0 := by
    apply PowerSeries.order_eq_nat.mpr
    exact ⟨by simpa using hl, fun r hr => (Nat.not_lt_zero r hr).elim⟩
  have hlow : ((y.order.toNat+1-k : ℕ) : ℕ∞) ≤ (wronskian b).order := by
    have hx := PowerSeries.nat_le_order W.det (y.order.toNat+1-k)
      (PowerSeries.X_pow_dvd_iff.mp hd)
    rwa [he, PowerSeries.order_mul, hco, zero_add] at hx
  rw [← PowerSeries.coe_toNat_order hb] at hlow
  have hn : y.order.toNat+1-k ≤ (wronskian b).order.toNat := by exact_mod_cast hlow
  have hk := l.isLt
  omega

end NCHitting

end

end OAI

-- ---- platform node ----
open OAI OAI.NCHitting
open PowerSeries Matrix Submodule


theorem solution : type_of% @_root_.OAI.NCHitting.order_le_wronskian_add := @_root_.OAI.NCHitting.order_le_wronskian_add
