-- Prove2me | solution 1 for OAI.BeamLadder.radial_covariance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:45:07.446776+00:00
-- url     : https://prove2.me/submissions/c8b0ef52-3b62-4f90-ba08-cab119ecf024

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/BeamTrace.lean:L270-L288
-- (upload_full_project.md Phase 4): solution for node OAI.BeamLadder.radial_covariance. The node keeps its source
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

end FischerBeam

namespace EntropyPhotonNumber
open FischerBeam

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
end BeamLadder

namespace EntropyPhotonNumber
end EntropyPhotonNumber

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

theorem radial_single (f : ℝ → ℝ) (C : ℝ) (hC : 0≤C)
    (hf : ∀ ke : NumberIndex n × NumberIndex n, |f (W ke)|≤C)
    (ke : NumberIndex n × NumberIndex n) :
    radial f C hC hf (lp.single 2 ke 1)=(f (W ke):ℂ) • lp.single 2 ke 1 := by
  apply lp.ext
  funext ab
  by_cases he : ab=ke
  · subst ab
    simp only [radial_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply]
  · simp only [radial_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_single, Pi.single_apply, ite_eq_right he, mul_zero]

theorem radial_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (f : ℝ → ℝ) (C : ℝ) (hC : 0≤C)
    (hf : ∀ ke : NumberIndex n × NumberIndex n, |f (W ke)|≤C) :
    radial f C hC hf ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L radial f C hC hf := by
  apply lp.ext_continuousLinearMap (by norm_num : (2:ENNReal)≠⊤)
  intro ab
  apply ContinuousLinearMap.ext_ring
  change radial f C hC hf (beamUnitary η hη (lp.single 2 ab 1))=
    beamUnitary η hη (radial f C hC hf (lp.single 2 ab 1))
  rw [radial_single, map_smul]
  obtain ⟨a,b⟩ := ab
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  simp only [radial_apply, beam_coordinate, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hc : beamCoefficient η k e a b=0
  · simp only [hc, Complex.ofReal_zero, mul_zero]
  · rw [coefficient_W η k e a b hc]

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
open scoped ComplexConjugate


theorem solution : type_of% @_root_.OAI.BeamLadder.radial_covariance := @_root_.OAI.BeamLadder.radial_covariance
