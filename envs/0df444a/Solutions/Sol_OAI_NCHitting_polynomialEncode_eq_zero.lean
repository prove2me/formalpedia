-- Prove2me | solution 1 for OAI.NCHitting.polynomialEncode_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:35:40.7452+00:00
-- url     : https://prove2.me/submissions/22ae025e-cee0-46bf-b189-7704379a5073

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/WordIndependence.lean:L227-L317
-- (upload_full_project.md Phase 4): solution for node OAI.NCHitting.polynomialEncode_eq_zero. The node keeps its source
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
import Definitions.Def_OAI_Algebra_FormulaHitting_Multiplicity
import Definitions.Def_OAI_Algebra_FormulaHitting_Formula
import Definitions.Def_OAI_Algebra_FormulaHitting_Representation
import Definitions.Def_OAI_Algebra_FormulaHitting_Series
import Definitions.Def_OAI_Algebra_FormulaHitting_System
import Definitions.Def_OAI_Algebra_FormulaHitting_Evaluation
import Definitions.Def_OAI_Algebra_FormulaHitting_FormulaSeries
import Definitions.Def_OAI_Algebra_FormulaHitting_Independence
import Definitions.Def_OAI_Algebra_FormulaHitting_WordIndependence
import Theorems.Thm_OAI_NCHitting_eq_smul_of_wronskian_eq_zero
import Theorems.Thm_OAI_NCHitting_kernel_mul_linear
import Theorems.Thm_OAI_NCHitting_no_polynomial_log_primitive

-- ---- from OAI.Algebra.FormulaHitting.Independence ----
namespace OAI

noncomputable section
open Polynomial
namespace NCHitting

variable {F : Type*} [Field F] [CharZero F]

section FormalResidue
open PowerSeries

end FormalResidue

section DistinctPoles
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CharZero F] in
theorem poleProduct_eq (a : ι → F) (i : ι) :
    poleProduct a = (Polynomial.X - Polynomial.C (a i)) * puncturedPoleProduct a i := by
  exact (Finset.mul_prod_erase Finset.univ (fun j => Polynomial.X - Polynomial.C (a j))
    (Finset.mem_univ i)).symm

end DistinctPoles

end NCHitting

end

end OAI

-- ---- from OAI.Algebra.FormulaHitting.WordIndependence ----
namespace OAI

noncomputable section
open Polynomial PowerSeries
namespace NCHitting

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

omit [CharZero F] in
theorem polynomialEncode_transform (q p0 : F[X]) (Q : Fin n → F[X])
    (hq : ∀ (i : Fin n) (w : List (Fin n)),
      (q : PowerSeries F) * PowerSeries.derivative (R := F) (wordSeries (i :: w)) =
        (Q i : PowerSeries F) * wordSeries w)
    (c : PolyWords F n) :
    polynomialEncode (polynomialTransform q p0 Q c) =
      (q : PowerSeries F) * ((p0 : PowerSeries F) *
        PowerSeries.derivative (R := F) (polynomialEncode c) -
          (p0.derivative : PowerSeries F) * polynomialEncode c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add, hc, hd]
    ring
  | single w p =>
    cases w with
    | nil => simp [PowerSeries.derivative_coe]
    | cons i w =>
      rw [polynomialTransform_single_cons, map_add, polynomialEncode_single,
        polynomialEncode_single, polynomialEncode_single]
      simp only [Polynomial.coe_mul, Polynomial.coe_sub]
      symm
      calc
        _ = ((q : PowerSeries F) * ((p0 : PowerSeries F) *
              (p.derivative : PowerSeries F) - (p0.derivative : PowerSeries F) *
                (p : PowerSeries F))) *
              wordSeries (i :: w) +
            ((p0 : PowerSeries F) * (p : PowerSeries F)) *
              ((q : PowerSeries F) * PowerSeries.derivative (R := F) (wordSeries (i :: w))) := by
          rw [Derivation.leibniz, PowerSeries.derivative_coe]
          simp only [smul_eq_mul]
          ring
        _ = _ := by rw [hq]; ring

theorem naturalPoles_injective : Function.Injective (naturalPoles (F := F) (n := n)) := by
  intro i j h
  apply Fin.ext
  have he : ((i.val + 1 : ℕ) : F) = ((j.val + 1 : ℕ) : F) := neg_injective h
  have hn := Nat.cast_injective he
  omega

omit [CharZero F] in
theorem natural_poleProduct_ne_zero : poleProduct (naturalPoles (F := F) (n := n)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact Polynomial.X_sub_C_ne_zero _

theorem natural_poleProduct_mul_kernel (i : Fin n) :
    (poleProduct (naturalPoles (F := F) (n := n)) : PowerSeries F) * kernel (i.val + 1) =
      (puncturedPoleProduct (naturalPoles (F := F)) i : PowerSeries F) := by
  rw [poleProduct_eq _ i]
  simp only [Polynomial.coe_mul, Polynomial.coe_add,
    Polynomial.coe_X, Polynomial.coe_C,
    naturalPoles, map_neg, sub_neg_eq_add]
  calc
    _ = (puncturedPoleProduct (naturalPoles (F := F)) i : PowerSeries F) *
          (kernel (i.val + 1) * (PowerSeries.X + PowerSeries.C (((i.val + 1 : ℕ) : F)))) := by ring
    _ = _ := by rw [kernel_mul_linear _ (Nat.succ_ne_zero _)]; simp

theorem natural_poleProduct_derivative (i : Fin n) (w : List (Fin n)) :
    (poleProduct (naturalPoles (F := F) (n := n)) : PowerSeries F) *
      PowerSeries.derivative (R := F) (wordSeries (i :: w)) =
        (puncturedPoleProduct (naturalPoles (F := F)) i : PowerSeries F) * wordSeries w := by
  rw [derivative_wordSeries_cons]
  rw [mul_left_comm, natural_poleProduct_mul_kernel, mul_comm]

omit [CharZero F] in
theorem transform_lengthBound (D : ℕ) (c : PolyWords F n) (hc : LengthBound D c)
    (q p0 : F[X]) (Q : Fin n → F[X]) : LengthBound D (polynomialTransform q p0 Q c) := by
  intro w hw
  by_contra hlen
  have hcw : c w = 0 := by
    by_contra hne
    exact hlen (hc w hne)
  have hchild : ∀ i, c (i :: w) = 0 := by
    intro i
    by_contra hne
    have hb := hc (i :: w) hne
    simp only [List.length_cons] at hb
    omega
  apply hw
  simp [hcw, hchild]

omit [CharZero F] in
theorem transform_top_coefficient (D : ℕ) (c : PolyWords F n) (hc : LengthBound D c)
    (q p0 : F[X]) (Q : Fin n → F[X]) (w : List (Fin n)) (hw : w.length = D) :
    polynomialTransform q p0 Q c w = q * (p0 * (c w).derivative - p0.derivative * c w) := by
  have hchild : ∀ i, c (i :: w) = 0 := by
    intro i
    by_contra hne
    have hb := hc (i :: w) hne
    simp only [List.length_cons, hw] at hb
    omega
  simp [hchild]

omit [CharZero F] in
private theorem topSupport_transform_ssubset (D : ℕ) (c : PolyWords F n)
    (hc : LengthBound D c) (q : F[X]) (Q : Fin n → F[X])
    (w0 : List (Fin n)) (hw0 : w0 ∈ topSupport D c) :
    topSupport D (polynomialTransform q (c w0) Q c) ⊂ topSupport D c := by
  have hsub : topSupport D (polynomialTransform q (c w0) Q c) ⊆ topSupport D c := by
    intro w hw
    obtain ⟨hne, hlen⟩ := (mem_topSupport _ _ _).mp hw
    apply (mem_topSupport _ _ _).mpr
    refine ⟨?_, hlen⟩
    intro hz
    apply hne
    rw [transform_top_coefficient D c hc q (c w0) Q w hlen, hz]
    simp
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro heq
  have hm : w0 ∈ topSupport D (polynomialTransform q (c w0) Q c) := by rwa [heq]
  have hz : polynomialTransform q (c w0) Q c w0 = 0 := by
    rw [transform_top_coefficient D c hc q (c w0) Q w0
      ((mem_topSupport _ _ _).mp hw0).2]
    ring
  exact ((mem_topSupport _ _ _).mp hm).1 hz

theorem polynomialEncode_eq_zero (D : ℕ) (c : PolyWords F n)
    (hc : LengthBound D c) (he : polynomialEncode c = 0) : c = 0 := by
  classical
  induction D generalizing c with
  | zero =>
    have hs : c = Finsupp.single [] (c []) := by
      ext w
      cases w with
      | nil => simp
      | cons i w =>
        have hz : c (i :: w) = 0 := by
          by_contra hne
          have hh := hc (i :: w) hne
          simp [List.length_cons] at hh
        simp [hz]
    have hz : c [] = 0 := by
      have hh := he
      rw [hs, polynomialEncode_single, wordSeries_nil, mul_one] at hh
      exact Polynomial.coe_eq_zero_iff.mp hh
    rw [hs, hz, Finsupp.single_zero]
  | succ D ih =>
    by_contra hcne
    have top_exists : ∀ b : PolyWords F n, LengthBound (D+1) b →
        polynomialEncode b = 0 → b ≠ 0 → (topSupport (D+1) b).Nonempty := by
      intro b hb hbe hbne
      by_contra hn
      apply hbne
      apply ih b ?_ hbe
      intro w hw
      have hbnd := hb w hw
      have hneq : w.length ≠ D+1 := by
        intro hlen
        exact hn ⟨w, (mem_topSupport _ _ _).mpr ⟨hw, hlen⟩⟩
      omega
    let P : ℕ → Prop := fun k => ∃ b : PolyWords F n,
      LengthBound (D+1) b ∧ polynomialEncode b = 0 ∧ b ≠ 0 ∧
        (topSupport (D+1) b).card = k
    have hex : ∃ k, P k := ⟨(topSupport (D+1) c).card, c, hc, he, hcne, rfl⟩
    obtain ⟨b, hb, hbe, hbne, hbcard⟩ := Nat.find_spec hex
    obtain ⟨w0, hw0⟩ := top_exists b hb hbe hbne
    have hp0 : b w0 ≠ 0 := ((mem_topSupport _ _ _).mp hw0).1
    have hwlen : w0.length = D+1 := ((mem_topSupport _ _ _).mp hw0).2
    let q := poleProduct (naturalPoles (F := F) (n := n))
    let Q := puncturedPoleProduct (naturalPoles (F := F) (n := n))
    let p0 := b w0
    let b' := polynomialTransform q p0 Q b
    have hb' : LengthBound (D+1) b' := transform_lengthBound _ b hb q p0 Q
    have hb'e : polynomialEncode b' = 0 := by
      rw [polynomialEncode_transform q p0 Q natural_poleProduct_derivative, hbe]
      simp
    have hcard : (topSupport (D+1) b').card < (topSupport (D+1) b).card :=
      Finset.card_lt_card (topSupport_transform_ssubset (D+1) b hb q Q w0 hw0)
    have hb'zero : b' = 0 := by
      by_contra hne
      have hmin : Nat.find hex ≤ (topSupport (D+1) b').card :=
        Nat.find_min' hex ⟨b', hb', hb'e, hne, rfl⟩
      omega
    have htop : ∀ w, w.length = D+1 →
        Polynomial.wronskian p0 (b w) = 0 := by
      intro w hw
      have hh : polynomialTransform q p0 Q b w = 0 := by
        exact DFunLike.congr_fun hb'zero w
      rw [transform_top_coefficient (D+1) b hb q p0 Q w hw] at hh
      have hq : q ≠ 0 := natural_poleProduct_ne_zero
      exact (mul_eq_zero.mp hh).resolve_left hq
    cases w0 with
    | nil => simp at hwlen
    | cons i v =>
      have hvl : v.length = D := by simpa using hwlen
      have hprop : ∀ j : Fin n, ∃ a : F, b (j :: v) = a • p0 := by
        intro j
        apply eq_smul_of_wronskian_eq_zero p0 (b (j :: v)) hp0
        apply htop
        simp [hvl]
      choose a ha using hprop
      have hraw : q * (p0 * (b v).derivative - p0.derivative * b v) +
          ∑ j, (p0 * Q j) * b (j :: v) = 0 := by
        rw [← polynomialTransform_apply]
        exact DFunLike.congr_fun hb'zero v
      have hsum : (∑ j, (p0 * Q j) * b (j :: v)) =
          p0^2 * (∑ j, Polynomial.C (a j) * Q j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [ha j, Polynomial.smul_eq_C_mul]
        ring
      rw [hsum] at hraw
      have ha0 := no_polynomial_log_primitive (naturalPoles (F := F) (n := n))
        naturalPoles_injective p0 (b v) hp0 a hraw i
      apply hp0
      rw [ha i, ha0, zero_smul]

end NCHitting

end

end OAI

-- ---- platform node ----
open OAI OAI.NCHitting
open Polynomial PowerSeries


theorem solution : type_of% @_root_.OAI.NCHitting.polynomialEncode_eq_zero := @_root_.OAI.NCHitting.polynomialEncode_eq_zero
