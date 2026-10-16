-- Prove2me | solution 1 for OAI.BeamLadder.discarded_covariance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:43:15.735952+00:00
-- url     : https://prove2.me/submissions/e410fee6-961b-4ae1-9070-26fcf7e4716e

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/BeamTrace.lean:L218-L241
-- (upload_full_project.md Phase 4): solution for node OAI.BeamLadder.discarded_covariance. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Theorems.Thm_OAI_BeamLadder_coefficient_W
import Theorems.Thm_OAI_BeamLadder_lowerL_single
import Theorems.Thm_OAI_BeamLadder_lowerR_single
import Theorems.Thm_OAI_EntropyPhotonNumber_beam_product_lower

-- ---- from OAI.MathematicalPhysics.Fock.Beam ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial

namespace FischerBeam
variable {J : Type*} [Fintype J] [DecidableEq J]

end FischerBeam

namespace FischerBeam

end FischerBeam

namespace FischerBeam

end FischerBeam

namespace FischerBeam

end FischerBeam

end

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

namespace BlockUnitary

variable {S : Type*} {I : S → Type*} [∀ s, Fintype (I s)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable [CompleteSpace E]

end BlockUnitary

namespace BlockUnitary
variable {S : Type*} {I : S → Type*} [∀ s, Fintype (I s)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end BlockUnitary

namespace EntropyPhotonNumber
open FischerBeam

end EntropyPhotonNumber

namespace EntropyPhotonNumber
open FischerBeam

end EntropyPhotonNumber

namespace FischerBeam
open MvPolynomial

theorem pderiv_one_rotated (c s : ℝ) (a b : ℕ) :
    pderiv 1 (rotated c s a b) =
      (-(s*(a:ℝ))) • rotated c s (a-1) b + (c*(b:ℝ)) • rotated c s a (b-1) := by
  simp [rotated, creatorA, creatorB, pderiv_X, smul_eq_C_mul]
  ring

theorem coeff_lower_one (c s : ℝ) (k e a b : ℕ) :
    ((e:ℝ)+1)*(rotated c s a b).coeff (degree k (e+1)) =
      -(s*(a:ℝ))*(rotated c s (a-1) b).coeff (degree k e)+
      c*(b:ℝ)*(rotated c s a (b-1)).coeff (degree k e) := by
  have hh := congrArg (fun polynomial : Poly => polynomial.coeff (degree k e))
    (pderiv_one_rotated c s a b)
  simpa only [coeff_pderiv, degree_one, degree_add_one, AddMonoidAlgebra.coeff_add,
    MvPolynomial.coeff_add,
    Finsupp.add_apply, coeff_smul,
    smul_eq_mul, mul_comm] using hh

theorem sqrt_weight_succ_left (a b : ℕ) :
    Real.sqrt (weight (degree (a+1) b)) =
      Real.sqrt ((a:ℝ)+1)*Real.sqrt (weight (degree a b)) := by
  simp only [weight_degree, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [mul_assoc, Real.sqrt_mul (by positivity)]

theorem sqrt_weight_succ_right (a b : ℕ) :
    Real.sqrt (weight (degree a (b+1))) =
      Real.sqrt ((b:ℝ)+1)*Real.sqrt (weight (degree a b)) := by
  simp only [weight_degree, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [show (a.factorial:ℝ)*((b+1)*b.factorial) = ((b:ℝ)+1)*(a.factorial*b.factorial) by ring]
  rw [Real.sqrt_mul (by positivity)]

theorem sqrt_lower_left (a b : ℕ) :
    (a:ℝ)/Real.sqrt (weight (degree a b)) =
      Real.sqrt a/Real.sqrt (weight (degree (a-1) b)) := by
  cases a with
  | zero => simp
  | succ a =>
    simp only [Nat.add_one_sub_one, Nat.cast_add, Nat.cast_one,
      sqrt_weight_succ_left]
    have h := Real.sq_sqrt (by positivity : 0 ≤ (a:ℝ)+1)
    have hp := Real.sqrt_pos.mpr (by positivity : 0 < (a:ℝ)+1)
    have hw := sqrt_weight_degree_pos a b
    field_simp
    nlinarith

theorem sqrt_lower_right (a b : ℕ) :
    (b:ℝ)/Real.sqrt (weight (degree a b)) =
      Real.sqrt b/Real.sqrt (weight (degree a (b-1))) := by
  cases b with
  | zero => simp
  | succ b =>
    simp only [Nat.add_one_sub_one, Nat.cast_add, Nat.cast_one,
      sqrt_weight_succ_right]
    have h := Real.sq_sqrt (by positivity : 0 ≤ (b:ℝ)+1)
    have hp := Real.sqrt_pos.mpr (by positivity : 0 < (b:ℝ)+1)
    have hw := sqrt_weight_degree_pos a b
    field_simp
    nlinarith

theorem oscillator_lower_one (c s : ℝ) (k e a b : ℕ) :
    Real.sqrt ((e:ℝ)+1)*oscillatorCoefficient c s k (e+1) a b =
      -(s*Real.sqrt a)*oscillatorCoefficient c s k e (a-1) b+
      c*Real.sqrt b*oscillatorCoefficient c s k e a (b-1) := by
  unfold oscillatorCoefficient
  rw [sqrt_weight_succ_right]
  have hh := coeff_lower_one c s k e a b
  calc
    _ = (Real.sqrt ((e:ℝ)+1))^2*(Real.sqrt (weight (degree k e))/Real.sqrt (weight (degree a b)))*
      (rotated c s a b).coeff (degree k (e+1)) := by ring
    _ = (Real.sqrt (weight (degree k e))/Real.sqrt (weight (degree a b)))*
        (((e:ℝ)+1)*(rotated c s a b).coeff (degree k (e+1))) := by rw [Real.sq_sqrt (by positivity)]; ring
    _ = -s*Real.sqrt (weight (degree k e))*((a:ℝ)/Real.sqrt (weight (degree a b)))*(rotated c s (a-1) b).coeff (degree k e)+
      c*Real.sqrt (weight (degree k e))*((b:ℝ)/Real.sqrt (weight (degree a b)))*(rotated c s a (b-1)).coeff (degree k e) := by rw [hh]; ring
    _ = _ := by rw [sqrt_lower_left, sqrt_lower_right]; ring

end FischerBeam

namespace EntropyPhotonNumber
open FischerBeam

theorem oneMode_discarded_lower (η : ℝ) (k e a b : ℕ) :
    Real.sqrt ((e:ℝ)+1)*oneModeBeamCoefficient η k (e+1) a b =
      -(Real.sqrt (1-η)*Real.sqrt a)*oneModeBeamCoefficient η k e (a-1) b+
      Real.sqrt η*Real.sqrt b*oneModeBeamCoefficient η k e a (b-1) := by
  simpa only [oneModeBeamCoefficient_eq, oscillatorCoefficient] using
    oscillator_lower_one (Real.sqrt η) (Real.sqrt (1-η)) k e a b

end EntropyPhotonNumber

namespace EntropyPhotonNumber
open FischerBeam
variable {n : ℕ}

theorem beamCoefficient_sector_zero (η : ℝ) (S T : NumberIndex n)
    (k : ∀ j, Fin (S j+1)) (a : ∀ j, Fin (T j+1)) (h : S ≠ T) :
    beamCoefficient η (fun j => k j) (fun j => S j-k j)
      (fun j => a j) (fun j => T j-a j)=0 := by
  classical
  obtain ⟨j,hj⟩ := Function.ne_iff.mp h
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  apply ite_eq_right
  change ¬ ((k j:ℕ)+(S j-k j)=(a j:ℕ)+(T j-a j))
  have hk := (k j).isLt
  have ha := (a j).isLt
  omega

theorem beamUnitary_apply_sector (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (T : NumberIndex n) (a : ∀ j, Fin (T j+1)) :
    beamUnitary η hη (jointSectorBasis n ⟨T,a⟩)=
      BlockUnitary.rotated (jointSectorBasis n)
        (fun T k a => multiSectorMatrix (Real.sqrt η) (Real.sqrt (1-η)) T k a) ⟨T,a⟩ := by
  exact BlockUnitary.unitary_apply_basis (jointSectorBasis n)
    (fun T k a => multiSectorMatrix (Real.sqrt η) (Real.sqrt (1-η)) T k a) _ _ _

theorem beam_coordinate_sector (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (S T : NumberIndex n) (k : ∀ j, Fin (S j+1)) (a : ∀ j, Fin (T j+1)) :
    inner ℂ (jointSectorBasis n ⟨S,k⟩) (beamUnitary η hη (jointSectorBasis n ⟨T,a⟩)) =
      (beamCoefficient η (fun j => k j) (fun j => S j-k j)
        (fun j => a j) (fun j => T j-a j) : ℂ) := by
  rw [beamUnitary_apply_sector]
  by_cases h : S=T
  · subst T
    erw [BlockUnitary.inner_basis_rotated_same, beam_sectorCoefficient]
  · erw [BlockUnitary.inner_basis_rotated_ne _ _ h,
      beamCoefficient_sector_zero η S T k a h, Complex.ofReal_zero]

theorem beam_coordinate (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (k e a b : NumberIndex n) :
    beamUnitary η hη (lp.single 2 (a,b) 1) (k,e)=(beamCoefficient η k e a b : ℂ) := by
  have hh := beam_coordinate_sector η hη (fun j => k j+e j) (fun j => a j+b j)
    (fun j => (⟨k j, by omega⟩ : Fin (k j+e j+1)))
    (fun j => (⟨a j, by omega⟩ : Fin (a j+b j+1)))
  simp only [jointSectorBasis_apply, sectorEquiv, Nat.add_sub_cancel_left, Equiv.coe_fn_mk] at hh
  simpa only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] using hh
end EntropyPhotonNumber

end

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.BeamTrace ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}
end Annihilation

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}
theorem up_update (j : Fin n) (k : NumberIndex n) : up j k=Function.update k j (k j+1) := by
  funext i
  by_cases he : i=j
  · subst i; simp
  · simp [he]

end BeamLadder

namespace EntropyPhotonNumber
 theorem beam_discarded_lower {n : ℕ} (η : ℝ) (j : Fin n) (k e a b : NumberIndex n) :
    Real.sqrt ((e j:ℝ)+1)*beamCoefficient η k (Function.update e j (e j+1)) a b =
      -(Real.sqrt (1-η)*Real.sqrt (a j))*beamCoefficient η k e (Function.update a j (a j-1)) b+
      Real.sqrt η*Real.sqrt (b j)*beamCoefficient η k e a (Function.update b j (b j-1)) := by
  exact beam_product_lower j (fun _ e k a b => oneModeBeamCoefficient η k e a b) e k a b
    _ _ _ (oneMode_discarded_lower η (k j) (e j) (a j) (b j))
end EntropyPhotonNumber

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}

theorem inverse_W_coefficient_right (η : ℝ) (j : Fin n) (k e a b : NumberIndex n) :
    (W (k,e)+1)⁻¹*beamCoefficient η k (up j e) a b=
      (W (a,b))⁻¹*beamCoefficient η k (up j e) a b := by
  by_cases hc : beamCoefficient η k (up j e) a b=0
  · simp [hc]
  · have hh : W (k,e)+1=W (a,b) := by
      rw [← W_upR j (k,e)]
      exact coefficient_W η _ _ _ _ hc
    rw [hh]

theorem discarded_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) :
    lowerR j ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (-(Real.sqrt (1-η):ℂ) • lowerL j+(Real.sqrt η:ℂ) • lowerR j) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2:ENNReal) ≠ ⊤)
  intro ab
  apply ContinuousLinearMap.ext_ring
  change lowerR j (beamUnitary η hη (lp.single 2 ab 1))=
    beamUnitary η hη ((-(Real.sqrt (1-η):ℂ) • lowerL j+(Real.sqrt η:ℂ) • lowerR j) (lp.single 2 ab 1))
  obtain ⟨a,b⟩ := ab
  simp only [add_apply, smul_apply, lowerL_single, lowerR_single, map_add, map_smul]
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  simp only [lowerR_apply, upR, beam_coordinate, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hh := beam_discarded_lower η j k e a b
  rw [← up_update] at hh
  change _= -(Real.sqrt (1-η):ℂ)*(((Real.sqrt (a j)/W (a,b):ℝ):ℂ)*(beamCoefficient η k e (down j a) b:ℂ))+
    (Real.sqrt η:ℂ)*(((Real.sqrt (b j)/W (a,b):ℝ):ℂ)*(beamCoefficient η k e a (down j b):ℂ))
  have hw := inverse_W_coefficient_right η j k e a b
  norm_cast
  dsimp [down] at *
  norm_num only [Nat.cast_add, Nat.cast_one] at *
  linear_combination (Real.sqrt ((e j:ℝ)+1))*hw+(W (a,b))⁻¹*hh
end

section
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

end BeamLadder

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap

namespace KrausBounded

section
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace E] [CompleteSpace H]

end

variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

end KrausBounded

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J : Type*}

end TensorLp

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end BeamLadder

end

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal

namespace EntropyPhotonNumber
variable {n : ℕ}
end EntropyPhotonNumber

namespace TensorLp
variable {A B I : Type*}
end TensorLp

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end CrossEnsemble

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace TensorLp
variable {A B I : Type*}

end TensorLp

namespace TraceEnsemble
open TensorLp
variable {A B I J : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber
open TensorLp
end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.BeamLadder
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open EntropyPhotonNumber QuantumTrace Annihilation


theorem solution : type_of% @_root_.OAI.BeamLadder.discarded_covariance := @_root_.OAI.BeamLadder.discarded_covariance
