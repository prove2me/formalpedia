-- Prove2me | solution 1 for OAI.QuantumTrace.gibbs_form_energy_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:58:36.167343+00:00
-- url     : https://prove2.me/submissions/3978e1cd-d4ef-457d-9872-4e5949c7b2f9

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Entropy.lean:L1911-L1975
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.gibbs_form_energy_identity. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy

-- ---- from OAI.Analysis.QuantumTrace.Basic ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

namespace QuantumTrace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open Filter

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

end

section
open Filter ContinuousLinearMap InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End Submodule
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End
open scoped ContinuousFunctionalCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

end

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section

open Filter Topology
open scoped Classical
variable {ι : Type*}
theorem diagonalMap_injective (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (hn : ∀ i, a i ≠ 0) : Function.Injective (diagonalMap a ha) := by
  intro x y h
  ext i
  exact mul_left_cancel₀ (hn i) (congrArg (fun z : SequenceHilbert ι => z i) h)

end

section
open Filter Topology
open scoped Classical
variable {ι : Type*}

end

section
open Filter Topology
variable {ι : Type*}

theorem inversePower_injective (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p : ℕ) :
    Function.Injective (inversePower s hs p) := by
  apply diagonalMap_injective
  intro i
  exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ (by linarith [hs i])))

end

section
open ContinuousLinearMap Module.End Submodule
universe v
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section
open Filter Topology
variable {ι : Type*}

end

section
open Filter Topology

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*}

end

section
variable {ι J : Type*}

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

end

open scoped BigOperators ComplexConjugate
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end QuantumTrace

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace QuantumTrace
variable {ι J : Type*}

end QuantumTrace

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Entropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace Annihilation
open EntropyPhotonNumber QuantumTrace WeightedShift
open scoped ComplexConjugate
variable {n : ℕ}

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped BigOperators
variable {n : ℕ} {I : Type*}

end WeightedGenerator

namespace WeightedShift
variable {I K : Type*}
end WeightedShift

namespace EntropyPhotonNumber
open QuantumTrace WeightedShift Annihilation
variable {n : ℕ}

end EntropyPhotonNumber

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

namespace QuantumTrace

section
open Filter Topology

open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

end

section
open ContinuousLinearMap InnerProductSpace Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

end

section
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

section
open ContinuousLinearMap InnerProductSpace Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

end

section
open ContinuousLinearMap Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end QuantumTrace

end

namespace EntropyPhotonNumber
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

end EntropyPhotonNumber

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal

namespace TraceEnsemble
open Filter Topology
open scoped BigOperators
variable {I A E G : Type*}
variable [NormedAddCommGroup G] [CompleteSpace G]

variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end TraceEnsemble

namespace TensorLp
variable {A B : Type*}

end TensorLp

namespace EntropyPhotonNumber

section
open Filter Topology TensorLp

end

open QuantumTrace TraceEnsemble
end EntropyPhotonNumber

namespace QuantumTrace
open scoped ENNReal

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace
end

open QuantumTrace Filter Topology

namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I J : Type*}

variable [CompleteSpace E]

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace

end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace TensorLp

end

open QuantumTrace

end EntropyPhotonNumber

namespace QuantumTrace

section
variable {ι J L : Type*}

theorem gibbs_form_energy_identity (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i)
    (A : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) (hA : IsStrictlyPositive A)
    (c : HilbertBasis L ℂ (SequenceHilbert ι)) (u : L → ℝ) (hu : ∀ l, 0 < u l)
    (heU : ∀ l, (inversePower s hs 4*Ring.inverse A*inversePower s hs 4) (c l) =
      (((u l)⁻¹ : ℝ) : ℂ) • c l)
    (b : HilbertBasis J ℂ (SequenceHilbert ι))
    (T : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (heT : ∀ j, T (b j) = (p j : ℂ) • b j)
    (hm : Summable (fun i => s i^8*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re)) :
    ∃ y : J → SequenceHilbert ι,
      (∀ j i, y j i = (s i^4 : ℂ)*((Real.sqrt (p j) : ℂ)*b j i)) ∧
      (∀ j, inversePower s hs 4 (y j) = (Real.sqrt (p j) : ℂ) • b j) ∧
      Summable (fun j => ‖y j‖^2) ∧
      (∑' j, ‖y j‖^2) = ∑' i, s i^8*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re ∧
      Summable (fun j => (inner ℂ (y j) (A (y j))).re) ∧
      HasSum (fun l => u l*(inner ℂ (c l) (T (c l))).re)
        (∑' j, (inner ℂ (y j) (A (y j))).re) := by
  have hm' : Summable (fun i => (s i^4)^2*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re) := by
    simpa only [← pow_mul] using hm
  obtain ⟨y, hy, hyS, hyE⟩ := weighted_spectral_vectors b T p hp heT (fun i => s i^4) hm'
  have hxy (j : J) : inversePower s hs 4 (y j) = (Real.sqrt (p j) : ℂ) • b j := by
    ext i
    rw [inversePower_apply, hy]
    change (((s i^4)⁻¹ : ℝ) : ℂ)*(((s i^4 : ℝ) : ℂ)*((Real.sqrt (p j) : ℂ)*b j i)) = (Real.sqrt (p j) : ℂ)*b j i
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero _ (by linarith [hs i]))]
    simp
  have hAp : A.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive _).mp hA.nonneg
  have hsum : Summable (fun j => (inner ℂ (y j) (A (y j))).re) := by
    apply Summable.of_nonneg_of_le (fun j => hAp.re_inner_nonneg_right _) _ (hyS.mul_left ‖A‖)
    intro j
    calc
      _ ≤ ‖inner ℂ (y j) (A (y j))‖ := Complex.re_le_norm _
      _ ≤ ‖y j‖*‖A (y j)‖ := norm_inner_le_norm _ _
      _ ≤ ‖y j‖*(‖A‖*‖y j‖) := mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  let f : J × L → ℝ := fun a => u a.2*(p a.1*‖inner ℂ (c a.2) (b a.1)‖^2)
  have hf0 (a : J × L) : 0 ≤ f a := mul_nonneg (hu _).le (mul_nonneg (hp _) (sq_nonneg _))
  have hrow (j : J) : HasSum (fun l => f (j,l)) (inner ℂ (y j) (A (y j))).re := by
    have hh := inverse_factor_form_parseval c A (inversePower s hs 4) hA
      (inversePower_positive s hs 4).isSymmetric (inversePower_injective s hs 4) u hu heU (y j)
    rw [hxy] at hh
    simpa only [f, inner_smul_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs, Real.sq_sqrt (hp j)] using hh
  have hf : Summable f := by
    apply (summable_prod_of_nonneg hf0).mpr
    refine ⟨fun j => (hrow j).summable, ?_⟩
    simpa only [(hrow _).tsum_eq] using hsum
  have hcol (l : L) : HasSum (fun j => f (j,l)) (u l*(inner ℂ (c l) (T (c l))).re) := by
    have hh := (hasSum_quadratic_eigenbasis b T p heT (c l)).mul_left (u l)
    simpa only [f, norm_inner_symm] using hh
  have hh : HasSum (fun l => u l*(inner ℂ (c l) (T (c l))).re)
      (∑' j, (inner ℂ (y j) (A (y j))).re) := by
    have hcols : Summable (fun l => u l*(inner ℂ (c l) (T (c l))).re) := by
      have hc : Summable (fun l => ∑' j, f (j,l)) := hf.prod_symm.prod
      simpa only [(hcol _).tsum_eq] using hc
    have heq : (∑' l, u l*(inner ℂ (c l) (T (c l))).re) =
        ∑' j, (inner ℂ (y j) (A (y j))).re := calc
      _ = ∑' l, ∑' j, f (j,l) := tsum_congr (fun l => (hcol l).tsum_eq.symm)
      _ = ∑' j, ∑' l, f (j,l) := Summable.tsum_comm (f := fun j l => f (j,l)) hf
      _ = _ := tsum_congr (fun j => (hrow j).tsum_eq)
    exact heq ▸ hcols.hasSum
  refine ⟨y, ?_, hxy, hyS, ?_, hsum, hh⟩
  · intro j i
    simpa only [Complex.ofReal_pow] using hy j i
  · simpa only [← pow_mul] using hyE

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace TensorLp

end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {J : Type*}

end QuantumTrace

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber
open QuantumTrace TraceEnsemble

end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.QuantumTrace
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.QuantumTrace.gibbs_form_energy_identity := @_root_.OAI.QuantumTrace.gibbs_form_energy_identity
