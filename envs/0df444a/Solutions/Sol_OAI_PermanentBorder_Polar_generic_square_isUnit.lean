-- Prove2me | solution 1 for OAI.PermanentBorder.Polar.generic_square_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:30:29.029563+00:00
-- url     : https://prove2.me/submissions/173ef530-791d-4a8b-ba7d-a61294e2eb25

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/GenericPolars.lean:L247-L275
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Polar.generic_square_isUnit. The node keeps its source
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
import Theorems.Thm_OAI_PermanentBorder_Polar_generic_no_infinity
import Theorems.Thm_OAI_PermanentBorder_Polar_square_isUnit_of_independent

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

lemma extendDerivation_algebraMap [Algebra.FormallyEtale R L]
    (D : Derivation K R L) (x : R) :
    extendDerivation D (algebraMap R L x) = D x := by
  simp [extendDerivation, LinearMap.compDer,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]

section Generic
universe u v
variable (K : Type u) [Field K] [CharZero K] (ι : Type v)

lemma parameterDerivation_parameter [DecidableEq ι] (i j : ι) :
    parameterDerivation K ι i (genericParameter K ι j) = if i = j then 1 else 0 := by
  classical
  simp [parameterDerivation, genericParameter, extendDerivation_algebraMap, Pi.single_apply,
    eq_comm]

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

lemma polar_rows_independent_of_derivations [DecidableEq τ] [DecidableEq σ]
    (w : τ → σ → L) (f : MvPolynomial σ K) (y : σ → L)
    (D : τ × σ → Derivation K L L)
    (hw : ∀ a b i j, D (a,b) (w i j) = if (a,b) = (i,j) then 1 else 0)
    (hf : aeval y f = 0) (hp : ∀ i, polarValue w f y i = 0)
    (hg : ∃ j, aeval y (pderiv j f) ≠ 0)
    (c : L) (cfs : τ → L)
    (hdep : ∀ j, c * aeval y (pderiv j f) +
      ∑ i, cfs i * polarGradient w f y i j = 0) :
    c = 0 ∧ cfs = 0 := by
  obtain ⟨b,hb⟩ := hg
  have hf' (a : τ) : ∑ j, aeval y (pderiv j f) * D (a,b) (y j) = 0 := by
    rw [← derivation_aeval, hf, map_zero]
  have hp' (a i : τ) : (if a = i then aeval y (pderiv b f) else 0) +
      ∑ j, polarGradient w f y i j * D (a,b) (y j) = 0 := by
    have hd := congrArg (D (a,b)) (hp i)
    rw [derivation_polarValue, map_zero] at hd
    convert hd using 1
    by_cases ha : a = i
    · simp [hw, ha]
    · simp [hw, ha]
  have hcfs : ∀ a, cfs a = 0 := by
    intro a
    have hs : ∑ i, cfs i * (∑ j, polarGradient w f y i j * D (a,b) (y j)) = 0 := by
      have hh : c * (∑ j, aeval y (pderiv j f) * D (a,b) (y j)) +
          ∑ i, cfs i * (∑ j, polarGradient w f y i j * D (a,b) (y j)) = 0 := by
        calc
          _ = ∑ j, (c * aeval y (pderiv j f) +
              ∑ i, cfs i * polarGradient w f y i j) * D (a,b) (y j) := by
            simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib,
              add_mul, mul_assoc]
            rw [Finset.sum_comm]
          _ = 0 := by simp [hdep]
      simpa only [hf', mul_zero, zero_add] using hh
    have hh : ∑ i, cfs i * ((if a = i then aeval y (pderiv b f) else 0) +
        ∑ j, polarGradient w f y i j * D (a,b) (y j)) = 0 := by
      simp only [hp', mul_zero, Finset.sum_const_zero]
    have : cfs a * aeval y (pderiv b f) = 0 := by
      simpa [mul_add, Finset.sum_add_distrib, hs] using hh
    exact (mul_eq_zero.mp this).resolve_right hb
  have hc : c = 0 := by
    have hh := hdep b
    simp only [hcfs, zero_mul, Finset.sum_const_zero, add_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_right hb
  exact ⟨hc,funext hcfs⟩

end Parametric
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Square
variable {K L τ : Type*} [Field K] [Field L] [Algebra K L] [Fintype τ]
lemma euler_aeval {σ : Type*} [Fintype σ] {f : MvPolynomial σ K} {r : ℕ}
    (hf : f.IsHomogeneous r) (y : σ → L) :
    ∑ j, aeval y (pderiv j f) * y j = (r : L) * aeval y f := by
  classical
  have h := congrArg (aeval y) hf.sum_X_mul_pderiv
  simpa [map_sum, mul_comm] using h

lemma polar_euler_aeval (w : τ → PolarVars τ → L)
    {f : MvPolynomial (PolarVars τ) K} {r : ℕ} (hf : f.IsHomogeneous r)
    (y : PolarVars τ → L) (i : τ) :
    ∑ j, polarGradient w f y i j * y j = ((r-1 : ℕ) : L) * polarValue w f y i := by
  classical
  simp only [polarGradient, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, euler_aeval hf.pderiv]
  simp only [polarValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Square

section GenericSquare
variable {K τ : Type*} [Field K] [CharZero K] [Fintype τ] [DecidableEq τ]
local notation "P" => (Option τ × PolarVars τ)
local notation "E" => GenericField K P

lemma generic_square_isUnit (f : MvPolynomial (PolarVars τ) K) {r : ℕ}
    (hhom : f.IsHomogeneous r) (y : PolarVars τ → E)
    (hf : aeval y f = 0) (hp : ∀ i, polarValue genericDirections f y i = 0)
    (hy : y ≠ 0) (hg : ∃ j, aeval y (pderiv j f) ≠ 0) :
    IsUnit (squareJacobian genericDirections genericLinear f y) := by
  classical
  have hn : ∑ j, genericLinear j * y j ≠ 0 := fun h =>
    hy (generic_no_infinity f hhom y hf hp hg h)
  apply square_isUnit_of_independent
  intro c z cfs hdep
  have hz : z = 0 := by
    have hs : ∑ j, (c * aeval y (pderiv j f) +
        ∑ i, cfs i * polarGradient genericDirections f y i j + z * genericLinear j) * y j = 0 := by
      simp [hdep]
    have he : c * (∑ j, aeval y (pderiv j f) * y j) +
        ∑ i, cfs i * (∑ j, polarGradient genericDirections f y i j * y j) +
        z * (∑ j, genericLinear j * y j) = 0 := by
      convert hs using 1
      simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib,
        add_mul, mul_assoc]
      rw [Finset.sum_comm]
    simp only [euler_aeval hhom, polar_euler_aeval _ hhom, hf, hp,
      mul_zero, Finset.sum_const_zero, zero_add] at he
    exact (mul_eq_zero.mp he).resolve_right hn
  obtain ⟨hc,hcfs⟩ := polar_rows_independent_of_derivations genericDirections f y
    (fun (a,b) => parameterDerivation K P (some a,b))
    (by intros; simp only [genericDirections, parameterDerivation_parameter,
      Prod.mk.injEq, Option.some.injEq]) hf hp hg c cfs (by simpa [hz] using hdep)
  exact ⟨hc,hz,hcfs⟩

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
open MvPolynomial Matrix


theorem solution : type_of% @_root_.OAI.PermanentBorder.Polar.generic_square_isUnit := @_root_.OAI.PermanentBorder.Polar.generic_square_isUnit
