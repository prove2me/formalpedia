-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.combined_form_representation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:57:01.054307+00:00
-- url     : https://prove2.me/submissions/4bf1605d-86ed-49fb-8ec8-96e02c564438

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Entropy.lean:L1847-L1867
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.combined_form_representation. The node keeps its source
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
import Theorems.Thm_OAI_EntropyPhotonNumber_number_form_representation

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

theorem combined_form_representation {n : ℕ} {J I : Type*}
    (b : HilbertBasis J ℂ (Fock n)) (w : J → ℝ≥0∞) (V : I → Fock n →L[ℂ] Fock n)
    {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive)
    (he : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re = sliceMoment b w V (energyInverse n x))
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ∃ C : Fock n →L[ℂ] Fock n, C.IsPositive ∧ ∀ x,
      ENNReal.ofReal (inner ℂ x (C x)).re =
        ENNReal.ofReal α*sliceMoment b w V (energyInverse n x)+
        ENNReal.ofReal β*numberVectorMoment (energyInverse n x) := by
  obtain ⟨D,hD,hDe⟩ := number_form_representation n
  let C := (α : ℂ) • B+(β : ℂ) • D
  have hC : C.IsPositive := (hB.smul_of_nonneg (by exact_mod_cast hα)).add
    (hD.smul_of_nonneg (by exact_mod_cast hβ))
  refine ⟨C,hC,fun x => ?_⟩
  have hx : (inner ℂ x (C x)).re = α*(inner ℂ x (B x)).re+β*(inner ℂ x (D x)).re := by
    change (inner ℂ x ((α : ℂ) • B x+(β : ℂ) • D x)).re = _
    simp
  have hBx : 0 ≤ (inner ℂ x (B x)).re := hB.re_inner_nonneg_right x
  have hDx : 0 ≤ (inner ℂ x (D x)).re := hD.re_inner_nonneg_right x
  rw [hx, ENNReal.ofReal_add (mul_nonneg hα hBx) (mul_nonneg hβ hDx), ENNReal.ofReal_mul hα,
    ENNReal.ofReal_mul hβ, he, hDe]

end EntropyPhotonNumber

namespace QuantumTrace

section
variable {ι J L : Type*}

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
open OAI OAI.EntropyPhotonNumber
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open QuantumTrace


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.combined_form_representation := @_root_.OAI.EntropyPhotonNumber.combined_form_representation
