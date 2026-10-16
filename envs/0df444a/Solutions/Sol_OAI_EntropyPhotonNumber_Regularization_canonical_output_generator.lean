-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.Regularization.canonical_output_generator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:15:20.066893+00:00
-- url     : https://prove2.me/submissions/b7c3d05f-cf40-42b3-956f-2a6991a3c575

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/PhysicalMinimum.lean:L710-L751
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.Regularization.canonical_output_generator. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Contraction
import Definitions.Def_OAI_InformationTheory_PhotonNumber_FiniteVariation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_PhysicalMinimum
import Theorems.Thm_OAI_EntropyPhotonNumber_beamOutput_powerMoment_le
import Theorems.Thm_OAI_EntropyPhotonNumber_weighted_replaced_threeport_generator

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
theorem mixture_finiteMoment {n : ℕ} (m : ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 1) {ρ σ : State n}
    (hρ : FiniteMoment m ρ) (hσ : FiniteMoment m σ) : FiniteMoment m (mixture t ht ρ σ) := by
  unfold FiniteMoment
  convert! (hρ.mul_left t).add (hσ.mul_left (1-t)) using 1
  funext k
  simp only [mixture_entry, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

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

theorem powerMoment_eq {n : ℕ} (m : ℕ) (ρ : State n) :
    powerMoment m ρ = ∑' k, ENNReal.ofReal ((1+(totalNumber k : ℝ))^m*(entry ρ.op k k).re) := by
  unfold powerMoment matrixMoment
  congr 1
  funext k
  rw [ENNReal.ofReal_mul (pow_nonneg (by positivity) _),
    ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_one, ENNReal.ofReal_natCast]
  rfl

theorem finiteMoment_iff {n : ℕ} (m : ℕ) (ρ : State n) :
    FiniteMoment m ρ ↔ powerMoment m ρ < ⊤ := by
  rw [powerMoment_eq]
  have hp (k : NumberIndex n) : 0 ≤ (1+(totalNumber k : ℝ))^m*(entry ρ.op k k).re :=
    mul_nonneg (pow_nonneg (by positivity) _) (ρ.positive.re_inner_nonneg_right _)
  constructor
  · intro h
    exact h.tsum_ofReal_lt_top
  · intro h
    have hs := ENNReal.summable_toReal h.ne
    change Summable (fun k => (1+(totalNumber k : ℝ))^m*(entry ρ.op k k).re)
    simpa only [ENNReal.toReal_ofReal (hp _)] using hs

theorem beamOutput_finiteMoment {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) {m : ℕ} {ρA ρB : State n}
    (hA : FiniteMoment m ρA) (hB : FiniteMoment m ρB) : FiniteMoment m (beamOutput η hη ρA ρB) := by
  apply (finiteMoment_iff _ _).mpr
  exact (beamOutput_powerMoment_le η hη m ρA ρB).trans_lt
    (ENNReal.mul_lt_top ((finiteMoment_iff _ _).mp hA) ((finiteMoment_iff _ _).mp hB))

end EntropyPhotonNumber

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.PhysicalMinimum ----
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
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open MeasureTheory NormedSpace
open Filter Asymptotics Topology
open ContinuousLinearMap

namespace TensorLp
open scoped ENNReal
variable {A B : Type*}

end TensorLp

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {J : Type*}

end BeamLadder

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ}
namespace GibbsData
variable {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end GibbsData

namespace WeightedColumns

end WeightedColumns

end

section
open QuantumTrace TensorLp

end

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} {k : ℝ} {ρ : State n}
namespace GibbsData
variable (G : GibbsData n k ρ)

end GibbsData
end

namespace Regularization
open QuantumTrace
variable {n : ℕ} (R : Regularization n)

end Regularization

open QuantumTrace Annihilation BeamLadder TensorLp
namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end EntropyPhotonNumber

namespace WeightedGenerator
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ} {I : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} {k : ℝ} {ρ : State n}
namespace GibbsData
variable (G : GibbsData n k ρ)
end GibbsData
end

namespace Regularization

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} (R : Regularization n)

end

open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} (R : Regularization n)

theorem canonical_output_generator (ρ σ : State n)
    (hmρ : FiniteMoment 6 ρ) (hmσ : FiniteMoment 6 σ)
    (hmD : FiniteMoment 6 R.τD) (hmO : FiniteMoment 6 R.τ0)
    (a b d r0 : ℝ) (hd : 0<d) (hr0 : 0<r0)
    (heq : r0=(1-R.δ)*(R.η*a+(1-R.η)*b)+(1-(1-R.δ))*d)
    (hD : ∀ k l, entry R.τD.op k l=if k=l then (thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry R.τ0.op k l=if k=l then (thermalWeight n r0 k:ℂ) else 0)
    (B : Fock n →L[ℂ] Fock n) :
    ∃ hm0 : FiniteMoment 6 (R.output ρ σ),
      WeightedGenerator.pairing r0 (WeightedColumns.canonical (R.output ρ σ) hm0).vector B=
      ((1-R.κ:ℝ):ℂ)*
        (WeightedGenerator.pairing a (WeightedColumns.canonical ρ hmρ).vector
          ((WeightedColumns.canonical σ hmσ).slice R.η R.hη
            ((WeightedColumns.canonical R.τD hmD).slice (1-R.δ)
              ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩ B))+
         WeightedGenerator.pairing b (WeightedColumns.canonical σ hmσ).vector
          ((WeightedColumns.canonical ρ hmρ).sliceRight R.η R.hη
            ((WeightedColumns.canonical R.τD hmD).slice (1-R.δ)
              ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩ B))) := by
  subst r0
  have hmM := beamOutput_finiteMoment R.η R.hη hmρ hmσ
  have hmG : FiniteMoment 6 (R.rawOutput ρ σ) :=
    beamOutput_finiteMoment (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩ hmM hmD
  have hm0 : FiniteMoment 6 (R.output ρ σ) :=
    mixture_finiteMoment 6 (1-R.κ) ⟨sub_nonneg.mpr R.hκ.2,sub_le_self _ R.hκ.1⟩ hmG hmO
  refine ⟨hm0,?_⟩
  apply weighted_replaced_threeport_generator R.η (1-R.δ) R.κ a b d R.hη
    ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩ ρ σ R.τD
      (beamOutput R.η R.hη ρ σ) (R.rawOutput ρ σ) R.τ0 (R.output ρ σ)
      (beamOutput_spec R.η R.hη ρ σ)
      (beamOutput_spec (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
        (beamOutput R.η R.hη ρ σ) R.τD)
      (WeightedColumns.canonical ρ hmρ) (WeightedColumns.canonical σ hmσ)
      (WeightedColumns.canonical R.τD hmD)
      (WeightedColumns.canonical (beamOutput R.η R.hη ρ σ) hmM)
      (WeightedColumns.canonical (R.rawOutput ρ σ) hmG)
      (WeightedColumns.canonical R.τ0 hmO)
      (WeightedColumns.canonical (R.output ρ σ) hm0) hd hr0 hD hO ?_ B
  change ((1-R.κ:ℝ):ℂ) • (R.rawOutput ρ σ).op+
    ((1-(1-R.κ):ℝ):ℂ) • R.τ0.op=
    ((1-R.κ:ℝ):ℂ) • (R.rawOutput ρ σ).op+(R.κ:ℂ) • R.τ0.op
  rw [sub_sub_cancel]
end Regularization

open QuantumTrace Annihilation BeamLadder TensorLp

namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.Regularization
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open MeasureTheory NormedSpace
open Filter Asymptotics Topology
open ContinuousLinearMap
open QuantumTrace Annihilation BeamLadder


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.Regularization.canonical_output_generator := @_root_.OAI.EntropyPhotonNumber.Regularization.canonical_output_generator
