-- Prove2me | solution 1 for OAI.PermanentBorder.Polar.rows_independent_of_derivations
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:22:54.75877+00:00
-- url     : https://prove2.me/submissions/617d5d78-b5c5-4291-ba7d-acc85923c233

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/GenericPolars.lean:L79-L147
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Polar.rows_independent_of_derivations. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
import Definitions.Def_OAI_Algebra_Determinantal_GenericPolars

-- ---- from OAI.Algebra.Determinantal.SliceCertificates ----
namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters
namespace PermanentBorder.CI
open MvPolynomial PermanentBorder.SliceParameters
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.CI
open Polynomial Matrix
open scoped Classical

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial PermanentBorder.SliceParameters
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.Polar
open MvPolynomial
open scoped TensorProduct

variable {K R L : Type*} [CommRing K] [CommRing R] [CommRing L]
  [Algebra K R] [Algebra K L] [Algebra R L] [IsScalarTower K R L]

section Generic
universe u v
variable (K : Type u) [Field K] [CharZero K] (ι : Type v)

end Generic

section ChainRule
variable {K L σ : Type*} [CommRing K] [CommRing L] [Algebra K L] [Fintype σ]

lemma derivation_aeval (D : Derivation K L L) (x : σ → L) (f : MvPolynomial σ K) :
    D (aeval x f) = ∑ j, aeval x (pderiv j f) * D (x j) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg, add_mul, Finset.sum_add_distrib]
  | mul_X f i hf =>
    simp only [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, hf,
      map_add, pderiv_X]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    simp [Pi.single_apply, mul_comm]

end ChainRule
end PermanentBorder.Polar

end OAI

-- ---- from OAI.Algebra.Determinantal.GenericPolars ----
namespace OAI
namespace PermanentBorder.Polar
open MvPolynomial

section Parametric
variable {K L σ τ : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype σ] [Fintype τ]

omit [Fintype τ] in
lemma derivation_polarValue (D : Derivation K L L) (w : τ → σ → L)
    (f : MvPolynomial σ K) (y : σ → L) (i : τ) :
    D (polarValue w f y i) = (∑ j, D (w i j) * aeval y (pderiv j f)) +
      ∑ j, polarGradient w f y i j * D (y j) := by
  simp only [polarValue, map_sum, Derivation.leibniz, smul_eq_mul, derivation_aeval,
    Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  · simp only [polarGradient, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]

lemma rows_independent_of_derivations [DecidableEq τ] [DecidableEq σ]
    (w : τ → σ → L) (l : σ → L) (f : MvPolynomial σ K) (y : σ → L)
    (D : Option τ × σ → Derivation K L L)
    (hw : ∀ a b i j, D (a,b) (w i j) = if (a,b) = (some i,j) then 1 else 0)
    (hl : ∀ a b j, D (a,b) (l j) = if (a,b) = (none,j) then 1 else 0)
    (hf : aeval y f = 0) (hp : ∀ i, polarValue w f y i = 0)
    (hn : ∑ j, l j * y j = 0 ∨ ∑ j, l j * y j = 1)
    (hy : ∃ j, y j ≠ 0) (hg : ∃ j, aeval y (pderiv j f) ≠ 0)
    (c z : L) (cfs : τ → L)
    (hdep : ∀ j, c * aeval y (pderiv j f) +
      ∑ i, cfs i * polarGradient w f y i j + z * l j = 0) :
    c = 0 ∧ z = 0 ∧ cfs = 0 := by
  have hf' (a : Option τ) (b : σ) :
      ∑ j, aeval y (pderiv j f) * D (a,b) (y j) = 0 := by
    rw [← derivation_aeval, hf, map_zero]
  have hp' (a : Option τ) (b : σ) (i : τ) :
      (if a = some i then aeval y (pderiv b f) else 0) +
        ∑ j, polarGradient w f y i j * D (a,b) (y j) = 0 := by
    have hd := congrArg (D (a,b)) (hp i)
    rw [derivation_polarValue, map_zero] at hd
    convert hd using 1
    by_cases ha : a = some i
    · simp [hw, ha]
    · simp [hw, ha]
  have hl' (a : Option τ) (b : σ) :
      (if a = none then y b else 0) + ∑ j, l j * D (a,b) (y j) = 0 := by
    have hd : D (a,b) (∑ j, l j * y j) = 0 := by
      rcases hn with h | h <;> simp [h]
    simp only [map_sum, Derivation.leibniz, smul_eq_mul, hl,
      Finset.sum_add_distrib] at hd
    by_cases ha : a = none
    · simpa [ha, add_comm] using hd
    · simpa [ha] using hd
  have combine (a : Option τ) (b : σ) :
      c * (∑ j, aeval y (pderiv j f) * D (a,b) (y j)) +
        ∑ i, cfs i * (∑ j, polarGradient w f y i j * D (a,b) (y j)) +
          z * (∑ j, l j * D (a,b) (y j)) = 0 := by
    calc
      _ = ∑ j, (c * aeval y (pderiv j f) +
          ∑ i, cfs i * polarGradient w f y i j + z * l j) * D (a,b) (y j) := by
        simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, add_mul, mul_assoc]
        rw [Finset.sum_comm]
      _ = 0 := by simp [hdep]
  obtain ⟨b,hyb⟩ := hy
  have hz : z = 0 := by
    have hc := combine none b
    have hpp (i : τ) : ∑ j, polarGradient w f y i j * D (none,b) (y j) = 0 := by
      simpa using hp' none b i
    simp only [hf', hpp, mul_zero, Finset.sum_const_zero, add_zero, zero_add] at hc
    have hll := hl' none b
    simp only [ite_true] at hll
    have : z * y b = 0 := by linear_combination z * hll - hc
    exact (mul_eq_zero.mp this).resolve_right hyb
  obtain ⟨b,hgb⟩ := hg
  have hcfs : ∀ i, cfs i = 0 := by
    intro i
    have hc := combine (some i) b
    simp only [hf', mul_zero, zero_add, hz, zero_mul, add_zero] at hc
    have hs : ∑ a, cfs a * ((if some i = some a then aeval y (pderiv b f) else 0) +
        ∑ j, polarGradient w f y a j * D (some i,b) (y j)) = 0 := by
      simp only [hp', mul_zero, Finset.sum_const_zero]
    have : cfs i * aeval y (pderiv b f) = 0 := by
      simpa [mul_add, Finset.sum_add_distrib, hc] using hs
    exact (mul_eq_zero.mp this).resolve_right hgb
  have hc : c = 0 := by
    have hd := hdep b
    simp only [hz, zero_mul, hcfs, Finset.sum_const_zero, add_zero] at hd
    exact (mul_eq_zero.mp hd).resolve_right hgb
  exact ⟨hc,hz,funext hcfs⟩

end Parametric
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Square
variable {K L τ : Type*} [Field K] [Field L] [Algebra K L] [Fintype τ]
end Square

section GenericSquare
variable {K τ : Type*} [Field K] [CharZero K] [Fintype τ] [DecidableEq τ]
local notation "P" => (Option τ × PolarVars τ)
local notation "E" => GenericField K P

end GenericSquare
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Polynomials
variable {R σ τ : Type*} [CommRing R] [Fintype σ] [Fintype τ]

end Polynomials

section Evaluation
variable {K L σ τ : Type*} [Field K] [Field L] [Algebra K L] [Fintype σ] [Fintype τ]

end Evaluation
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Map
variable {R S σ τ : Type*} [CommRing R] [CommRing S] [Fintype σ] [Fintype τ]

end Map
end PermanentBorder.Polar

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.Polar
open MvPolynomial


theorem solution : type_of% @_root_.OAI.PermanentBorder.Polar.rows_independent_of_derivations := @_root_.OAI.PermanentBorder.Polar.rows_independent_of_derivations
