-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.gibbs_slice_real_trace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:08:40.14265+00:00
-- url     : https://prove2.me/submissions/f6f4735f-5fa4-492b-8636-727bfa5ede4e

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/GibbsVariational.lean:L443-L475
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.gibbs_slice_real_trace. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Theorems.Thm_OAI_EntropyPhotonNumber_gibbs_slice_trace

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
theorem numberMoment_nonneg {n : ℕ} (m : ℕ) (ρ : State n) : 0 ≤ numberMoment m ρ :=
  tsum_nonneg (fun k => mul_nonneg (by positivity) (ρ.positive.re_inner_nonneg_right _))

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

theorem basisExpectation_ofReal (b : HilbertBasis J ℂ E) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) {T : E →L[ℂ] E} (hp : T.IsPositive)
    (hs : Summable (fun j => w j*(inner ℂ (b j) (T (b j))).re)) :
    basisExpectation b (fun j => ENNReal.ofReal (w j)) T =
      ENNReal.ofReal (∑' j, w j*(inner ℂ (b j) (T (b j))).re) := by
  simp only [basisExpectation, ← ENNReal.ofReal_mul (hw _)]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (hw j)
    (hp.re_inner_nonneg_right _)) hs).symm

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

-- ---- from OAI.InformationTheory.PhotonNumber.GibbsVariational ----
namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal

namespace QuantumTrace

section
open scoped BigOperators
open Filter Topology

namespace StochasticOverlap
variable {I J : Type*} (a : StochasticOverlap I J)

end StochasticOverlap
end

section
open scoped BigOperators
variable {I J : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

end

variable {J : Type*}

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace

end EntropyPhotonNumber

namespace QuantumTrace
variable {n : ℕ} {J : Type*} [Nonempty J]

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace
end

section
open QuantumTrace TraceEnsemble

theorem gibbs_slice_real_trace {n : ℕ} {J L K I : Type*}
    (c : HilbertBasis L ℂ (Fock n)) (u : L → ℝ) (hu : ∀ l, 0 < u l)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1)
    (ρ : State n) (heρ : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (hm : FiniteMoment 4 ρ)
    (a : HilbertBasis K ℂ (Fock n)) (w : K → ℝ) (hw : ∀ j, 0 ≤ w j)
    (V : I → Fock n →L[ℂ] Fock n) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (σ : State n)
    (heσ : TraceEnsemble.operator (fun z : I × J => V z.1 (diagonalVector b p z.2)) = σ.op)
    (hc : Summable (fun j => w j*(inner ℂ (a j) (σ.op (a j))).re))
    {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hform : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re =
      ENNReal.ofReal α*sliceMoment a (fun j => ENNReal.ofReal (w j)) V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x))
    {k : ℝ} (hk : 0 < k)
    (heK : ∀ l, gibbsInverse rootNumberWeight rootNumberWeight_one_le k B (c l) =
      (((u l)⁻¹ : ℝ) : ℂ) • c l) :
    HasSum (fun l => u l*(inner ℂ (c l) (ρ.op (c l))).re)
      (k*numberMoment 4 ρ + α*(∑' j, w j*(inner ℂ (a j) (σ.op (a j))).re) + β*energy ρ) := by
  obtain ⟨E,hE,he⟩ := gibbs_slice_trace c u hu b p hp hs ρ heρ hm a
    (fun j => ENNReal.ofReal (w j)) V hV σ heσ hB hform hk heK
  have hE0 : 0 ≤ E := hE.tsum_eq ▸ tsum_nonneg
    (fun j => mul_nonneg (hu j).le (ρ.positive.re_inner_nonneg_right _))
  have hc0 : 0 ≤ ∑' j, w j*(inner ℂ (a j) (σ.op (a j))).re :=
    tsum_nonneg (fun j => mul_nonneg (hw j) (σ.positive.re_inner_nonneg_right _))
  rw [basisExpectation_ofReal a w hw σ.positive hc,
    ← ENNReal.ofReal_mul hk.le, ← ENNReal.ofReal_mul hα, ← ENNReal.ofReal_mul hβ,
    ← ENNReal.ofReal_add (mul_nonneg hα hc0) (mul_nonneg hβ (energy_nonneg ρ)),
    ← ENNReal.ofReal_add (mul_nonneg hk.le (numberMoment_nonneg 4 ρ))
      (add_nonneg (mul_nonneg hα hc0) (mul_nonneg hβ (energy_nonneg ρ)))] at he
  have he' := (ENNReal.ofReal_eq_ofReal_iff hE0
    (add_nonneg (mul_nonneg hk.le (numberMoment_nonneg 4 ρ))
      (add_nonneg (mul_nonneg hα hc0) (mul_nonneg hβ (energy_nonneg ρ))))).mp he
  simpa only [he', add_assoc] using hE

end

section
open QuantumTrace

end

section
open QuantumTrace TensorLp

namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end

section
open QuantumTrace
namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end

open QuantumTrace TraceEnsemble

namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)
end GibbsData

end EntropyPhotonNumber

namespace TensorLp
variable {A B I J : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp

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
open QuantumTrace TraceEnsemble


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.gibbs_slice_real_trace := @_root_.OAI.EntropyPhotonNumber.gibbs_slice_real_trace
