-- Prove2me | solution 1 for OAI.PermanentBorder.KernelBilinear.mixed_coefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:42:20.214796+00:00
-- url     : https://prove2.me/submissions/9a3998b4-5f72-44f7-bfa1-93e2447b8ebc

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/KernelCharts.lean:L302-L318
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.KernelBilinear.mixed_coefficient_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts

-- ---- from OAI.Algebra.Determinantal.KernelCharts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical

section Reindex
variable {ι σ E L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [Fintype E] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

end Reindex
end PermanentBorder.Multigraded

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical

variable {κ : Type} [Fintype κ] {n : ℕ}

lemma mixedPolynomial_eq :
    Multigraded.mixedPolynomial (firstGroup (κ := κ) (n := n)) secondGroup =
      (X none + X (some false))^(n+1) * (X none + X (some true))^n *
        (X (some false) + X (some true))^Fintype.card κ := by
  simp [Multigraded.mixedPolynomial, firstGroup, secondGroup, Fintype.prod_sum_type,
    mul_assoc]

end PermanentBorder.KernelBilinear

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical
variable {σ : Type*} [DecidableEq σ]
lemma collapse_monomial (i : σ) (d : σ →₀ ℕ) (a : ℕ) :
    collapse i (monomial d a) = Polynomial.C a * Polynomial.X^(d i) := by
  rw [collapse, eval₂Hom_monomial]
  congr 1
  have h := Finsupp.prod_ite_eq d i (fun _ n => (Polynomial.X : Polynomial ℕ)^n)
  by_cases hi : i ∈ d.support
  · simpa only [ite_eq_left hi, eq_comm, ite_pow, one_pow] using h
  · simpa only [ite_eq_right hi, Finsupp.notMem_support_iff.mp hi, pow_zero,
      eq_comm, ite_pow, one_pow] using h

lemma coeff_le_collapse (i : σ) (p : MvPolynomial σ ℕ) (d : σ →₀ ℕ) :
    p.coeff d ≤ (collapse i p).coeff (d i) := by
  by_cases hd : d ∈ p.support
  · have he : (collapse i p).coeff (d i) =
        ∑ k ∈ p.support, (collapse i (monomial k (p.coeff k))).coeff (d i) := by
      conv_lhs => rw [as_sum p]
      simp only [map_sum, Polynomial.finsetSum_coeff]
    rw [he]
    have h := Finset.single_le_sum (fun k (_ : k ∈ p.support) =>
      Nat.zero_le ((collapse i (monomial k (p.coeff k))).coeff (d i))) hd
    simpa [collapse_monomial, Polynomial.coeff_C_mul] using h
  · rw [notMem_support_iff.mp hd]
    exact Nat.zero_le _
end PermanentBorder.Multigraded

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}
lemma mixed_coefficient_bound :
    (Multigraded.mixedPolynomial (firstGroup (κ := κ) (n := n)) secondGroup).coeff
      (dimensions κ n) ≤ 2^Fintype.card κ * (2*n+1).choose (Fintype.card κ+1) := by
  have h := Multigraded.coeff_le_collapse none
    (Multigraded.mixedPolynomial (firstGroup (κ := κ) (n := n)) secondGroup)
    (dimensions κ n)
  have hp : Multigraded.collapse none
      (Multigraded.mixedPolynomial (firstGroup (κ := κ) (n := n)) secondGroup) =
      (Polynomial.X + 1)^(2*n+1) * Polynomial.C (2^Fintype.card κ) := by
    rw [mixedPolynomial_eq]
    simp only [map_mul, map_pow, map_add, Multigraded.collapse, eval₂Hom_X']
    simp only [↓reduceIte, Option.some_ne_none, one_add_one_eq_two]
    rw [← pow_add, show n+1+n = 2*n+1 by omega]
    simp
  rw [hp, dimensions_none, Polynomial.coeff_mul_C, Polynomial.coeff_X_add_one_pow,
    mul_comm] at h
  exact h
end PermanentBorder.KernelBilinear

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology

section Elimination
variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

end Elimination
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Calculus
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

end Calculus
end PermanentBorder.PolarAnalysis.Schur

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical


theorem solution : type_of% @_root_.OAI.PermanentBorder.KernelBilinear.mixed_coefficient_bound := @_root_.OAI.PermanentBorder.KernelBilinear.mixed_coefficient_bound
