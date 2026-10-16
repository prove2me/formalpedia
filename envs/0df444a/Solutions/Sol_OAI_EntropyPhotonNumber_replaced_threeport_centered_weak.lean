-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.replaced_threeport_centered_weak
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:00:36.79497+00:00
-- url     : https://prove2.me/submissions/e98b97e2-59cf-436e-82f1-1bb9944fa45d

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Generator.lean:L675-L718
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.replaced_threeport_centered_weak. The node keeps its source
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
import Theorems.Thm_OAI_CrossEnsemble_operator_comp_left
import Theorems.Thm_OAI_EntropyPhotonNumber_replaced_threeport_weak
import Theorems.Thm_OAI_KrausBounded_dual_one

-- ---- from OAI.MathematicalPhysics.Fock.Operators ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate

namespace WeightedShift
variable {I J : Type*}
variable [DecidableEq I] [DecidableEq J]

end WeightedShift

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

end Annihilation

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped ComplexConjugate
variable {n : ℕ}

end Annihilation

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

end Annihilation

namespace CrossEnsemble
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem trace_norm_summable (b : HilbertBasis J ℂ E) {u v : I → E}
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2)) :
    Summable (fun ij : I × J => ‖inner ℂ (b ij.2) (u ij.1)*inner ℂ (v ij.1) (b ij.2)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((square_coordinates_summable b hu).add (square_coordinates_summable b hv))
  intro ij
  rw [norm_mul, norm_inner_symm (v ij.1)]
  nlinarith [sq_nonneg (‖inner ℂ (b ij.2) (u ij.1)‖-‖inner ℂ (b ij.2) (v ij.1)‖)]

theorem trace_hasSum (b : HilbertBasis J ℂ E) {u v : I → E}
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2)) :
    HasSum (fun j => inner ℂ (b j) (operator u v (b j)))
      (∑' i, inner ℂ (v i) (u i)) := by
  have hh := (trace_norm_summable b hu hv).of_norm
  have hi (i : I) : HasSum (fun j => inner ℂ (b j) (u i)*inner ℂ (v i) (b j)) (inner ℂ (v i) (u i)) := by
    simpa only [mul_comm] using b.hasSum_inner_mul_inner (v i) (u i)
  have he (j : J) := entry_hasSum hu hv (b j) (b j)
  have hf := hh.hasSum.prod_fiberwise (f := fun ij : I × J => inner ℂ (b ij.2) (u ij.1)*inner ℂ (v ij.1) (b ij.2)) hi
  have hg := hh.prod_symm.hasSum.prod_fiberwise (f := fun ji : J × I => inner ℂ (b ji.1) (u ji.2)*inner ℂ (v ji.2) (b ji.1)) he
  have ht : (∑' j, inner ℂ (b j) (operator u v (b j)))=∑' i, inner ℂ (v i) (u i) := by
    rw [hg.tsum_eq, hf.tsum_eq]
    exact (Equiv.prodComm J I).tsum_eq (fun ij : I × J => inner ℂ (b ij.2) (u ij.1)*inner ℂ (v ij.1) (b ij.2))
  exact ht ▸ hg.summable.hasSum

theorem pairing_trace (b : HilbertBasis J ℂ E) {u v : I → E}
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2)) (Z : E →L[ℂ] E) :
    HasSum (fun j => inner ℂ (b j) (Z (operator u v (b j)))) (pairing u v Z) := by
  have hh := trace_hasSum b (applied_summable hu Z) hv
  rw [← operator_comp_left hu hv Z] at hh
  exact hh

 theorem pairing_eq_of_operator_eq {K : Type*} (b : HilbertBasis J ℂ E)
    {u v : I → E} {x y : K → E}
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2))
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (he : operator u v=operator x y) (Z : E →L[ℂ] E) : pairing u v Z=pairing x y Z := by
  apply HasSum.unique (pairing_trace b hu hv Z)
  rw [he]
  exact pairing_trace b hx hy Z
end CrossEnsemble

namespace CrossEnsemble
open scoped BigOperators ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped BigOperators ComplexConjugate
variable {n : ℕ}

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end WeightedGenerator

end

end

end OAI

-- ---- from OAI.Analysis.TensorLp ----
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

namespace TensorLp
variable {A B : Type*}
end TensorLp

namespace TensorLp
variable {A B : Type*}

end TensorLp

namespace TensorLp
variable {A B : Type*}

theorem hasSum_slice_inner (x y : H (A × B)) :
    HasSum (fun b => inner ℂ (slice x b) (slice y b)) (inner ℂ x y) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) x y
  have hr (b : B) : HasSum (fun a => inner ℂ (x (a,b)) (y (a,b)))
      (inner ℂ (slice x b) (slice y b)) := lp.hasSum_inner (𝕜 := ℂ) (slice x b) (slice y b)
  have hc : HasSum (fun ba : B × A => inner ℂ (x (ba.2,ba.1)) (y (ba.2,ba.1)))
      (inner ℂ x y) := (Equiv.prodComm B A).hasSum_iff.mpr h
  exact hc.prod_fiberwise hr

end TensorLp

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

end

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

theorem conjugate_inner (η : ℝ) (hη : η ∈ Set.Icc 0 1) (Z : Fock n →L[ℂ] Fock n)
    (x y : JointFock n) :
    inner ℂ x (conjugate η hη Z y)=inner ℂ (beamUnitary η hη x) (liftLeft Z (beamUnitary η hη y)) := by
  change inner ℂ x ((beamUnitary η hη).symm (liftLeft Z (beamUnitary η hη y)))=_
  rw [← (beamUnitary η hη).inner_map_map, (beamUnitary η hη).apply_symm_apply]

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

 theorem conditionalLeft_entry (y : J → H B) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) (u v : H A) :
    HasSum (fun j => inner ℂ (tensor u (y j)) (Z (tensor v (y j)))) (inner ℂ u (conditionalLeft y hy Z v)) :=
  KrausBounded.dual_entry _ _ _ _ _

 theorem conditionalRight_entry (x : I → H A) (hx : HasSum (fun i => ‖x i‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) (u v : H B) :
    HasSum (fun i => inner ℂ (tensor (x i) u) (Z (tensor (x i) v))) (inner ℂ u (conditionalRight x hx Z v)) :=
  KrausBounded.dual_entry _ _ _ _ _

 theorem tensorFamily_summable (x : I → H A) (y : J → H B)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2)) :
    Summable (fun ij : I × J => ‖tensor (x ij.1) (y ij.2)‖^2) := by
  simpa only [tensor_norm_sq] using hx.mul_of_nonneg hy (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)

theorem pairing_conditionalLeft (u v : I → H A) (y : J → H B)
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2))
    (hy : HasSum (fun j => ‖y j‖^2) 1) (Z : H (A × B) →L[ℂ] H (A × B)) :
    CrossEnsemble.pairing (fun ij : I × J => tensor (u ij.1) (y ij.2))
      (fun ij : I × J => tensor (v ij.1) (y ij.2)) Z=
      CrossEnsemble.pairing u v (conditionalLeft y hy Z) := by
  have hh := (CrossEnsemble.pairing_summable (tensorFamily_summable u y hu hy.summable)
    (tensorFamily_summable v y hv hy.summable) Z).hasSum.prod_fiberwise
      (fun i => conditionalLeft_entry y hy Z (v i) (u i))
  exact hh.tsum_eq.symm

theorem pairing_conditionalRight (x : I → H A) (u v : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1)
    (hu : Summable (fun j => ‖u j‖^2)) (hv : Summable (fun j => ‖v j‖^2))
    (Z : H (A × B) →L[ℂ] H (A × B)) :
    CrossEnsemble.pairing (fun ij : I × J => tensor (x ij.1) (u ij.2))
      (fun ij : I × J => tensor (x ij.1) (v ij.2)) Z=
      CrossEnsemble.pairing u v (conditionalRight x hx Z) := by
  have hs := CrossEnsemble.pairing_summable (tensorFamily_summable x u hx.summable hu)
    (tensorFamily_summable x v hx.summable hv) Z
  have hh := hs.prod_symm.hasSum.prod_fiberwise
      (fun j => conditionalRight_entry x hx Z (v j) (u j))
  have he := (Equiv.prodComm J I).tsum_eq
    (fun ij : I × J => inner ℂ (tensor (x ij.1) (v ij.2)) (Z (tensor (x ij.1) (u ij.2))))
  change (∑' ji : J × I, inner ℂ (tensor (x ji.swap.1) (v ji.swap.2))
    (Z (tensor (x ji.swap.1) (u ji.swap.2))))=_ at he
  rw [he] at hh
  exact hh.tsum_eq.symm
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
theorem slice_family_summable (x : I → H (A × B)) (hx : Summable (fun i => ‖x i‖^2)) :
    Summable (fun ie : I × B => ‖slice (x ie.1) ie.2‖^2) := by
  apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
  refine ⟨fun i => (hasSum_slice_norm_sq (x i)).summable, ?_⟩
  simpa only [(hasSum_slice_norm_sq _).tsum_eq] using hx

theorem pairing_liftLeft (x y : I → H (A × B))
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (Z : H A →L[ℂ] H A) :
    CrossEnsemble.pairing x y (liftLeft Z)=
      CrossEnsemble.pairing (fun ie : I × B => slice (x ie.1) ie.2)
        (fun ie : I × B => slice (y ie.1) ie.2) Z := by
  have hh := (CrossEnsemble.pairing_summable (slice_family_summable x hx)
    (slice_family_summable y hy) Z).hasSum.prod_fiberwise
      (fun i => by simpa only [slice_liftLeft] using hasSum_slice_inner (y i) (liftLeft Z (x i)))
  exact hh.tsum_eq
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

-- ---- from OAI.InformationTheory.PhotonNumber.BeamForms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

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

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

theorem physical_ensemble_output (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (hτ : IsBeamSplitterOutput η ρ σ τ)
    (v : I → Fock n) (w : J → Fock n)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1)
    (hev : TraceEnsemble.operator v=ρ.op) (hew : TraceEnsemble.operator w=σ.op) :
    partialTrace (fun ij : I × J => beamUnitary η hη (tensor (v ij.1) (w ij.2)))=τ.op := by
  have hs : Summable (fun ij : I × J => ‖beamUnitary η hη (tensor (v ij.1) (w ij.2))‖^2) := by
    simpa only [LinearIsometryEquiv.norm_map] using (TraceEnsemble.hasSum_tensor_norm hv hw).summable
  apply entry_ext
  intro k l
  have he := partialTrace_entry hs k l
  simp only [beam_ensemble_entry η hη ρ σ v w hv hw hev hew] at he
  exact he.unique (hτ k l)

theorem cross_slice_eq_partialTrace (v : I → JointFock n) :
    CrossEnsemble.operator (fun ie : I × NumberIndex n => slice (v ie.1) ie.2)
      (fun ie : I × NumberIndex n => slice (v ie.1) ie.2)=partialTrace v := by
  exact (Equiv.prodComm I (NumberIndex n)).tsum_eq
    (fun ei => InnerProductSpace.rankOne ℂ (slice (v ei.2) ei.1) (slice (v ei.2) ei.1))

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end CrossEnsemble

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

end BeamLadder

namespace EnsemblePullback

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {I : Type*}

end

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {I J : Type*}

end EnsemblePullback

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace CrossEnsemble
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {I : Type*}
end CrossEnsemble

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

end Annihilation

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I : Type*}

end BeamLadder

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I K : Type*}

end WeightedGenerator

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end BeamLadder

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I : Type*}

end CrossEnsemble

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Generator ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

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

namespace PhysicalGenerator
open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I : Type*}

end PhysicalGenerator

namespace QuantumTrace
end QuantumTrace

namespace PhysicalGenerator

section
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ} {I : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I J K : Type*}

end PhysicalGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder

namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

end WeightedColumns

end EntropyPhotonNumber

namespace PhysicalGenerator
open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I J K : Type*}

end PhysicalGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder TensorLp
namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

end WeightedColumns

end EntropyPhotonNumber

namespace KrausBounded
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
end KrausBounded

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}
theorem conjugate_one (η : ℝ) (hη : η ∈ Set.Icc 0 1) :
    conjugate (n:=n) η hη 1=1 := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [conjugate,liftLeft_one,ContinuousLinearMap.comp_apply,one_apply_eq_self]
  change (beamUnitary η hη).symm (beamUnitary η hη x)=x
  exact (beamUnitary η hη).symm_apply_apply x
end BeamLadder

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder TensorLp
namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

theorem rawSlice_one (η : ℝ) (hη : η ∈ Set.Icc 0 1) : X.rawSlice η hη 1=1 := by
  simp only [rawSlice,conjugate_one,conditionalLeft,KrausBounded.dual_one]

theorem rawSliceRight_one (η : ℝ) (hη : η ∈ Set.Icc 0 1) : X.rawSliceRight η hη 1=1 := by
  simp only [rawSliceRight,conjugate_one,conditionalRight,KrausBounded.dual_one]

theorem expectation_affine {σ τ : State n} (Y : WeightedColumns σ) (Z : WeightedColumns τ)
    (c d : ℂ) (he : τ.op=c • ρ.op+d • σ.op) (A : Fock n →L[ℂ] Fock n) :
    Z.expectation A=c*X.expectation A+d*Y.expectation A := by
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hx := CrossEnsemble.pairing_trace bas X.normalized.summable X.normalized.summable A
  have hy := CrossEnsemble.pairing_trace bas Y.normalized.summable Y.normalized.summable A
  have hz := CrossEnsemble.pairing_trace bas Z.normalized.summable Z.normalized.summable A
  change HasSum (fun k => inner ℂ (bas k) (A (TraceEnsemble.operator
    (fun i => inverseWeight 3 (X.vector i)) (bas k)))) (X.expectation A) at hx
  rw [X.density] at hx
  change HasSum (fun k => inner ℂ (bas k) (A (TraceEnsemble.operator
    (fun i => inverseWeight 3 (Y.vector i)) (bas k)))) (Y.expectation A) at hy
  rw [Y.density] at hy
  change HasSum (fun k => inner ℂ (bas k) (A (TraceEnsemble.operator
    (fun i => inverseWeight 3 (Z.vector i)) (bas k)))) (Z.expectation A) at hz
  rw [Z.density] at hz
  exact hz.unique (by
    simpa only [he,add_apply,smul_apply,map_add,map_smul,inner_add_right,inner_smul_right] using
      (hx.mul_left c).add (hy.mul_left d))
end WeightedColumns

theorem physical_rawSlice_expectation {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (hτ : IsBeamSplitterOutput η ρ σ τ)
    (X : WeightedColumns ρ) (Y : WeightedColumns σ) (T : WeightedColumns τ)
    (Z : Fock n →L[ℂ] Fock n) :
    X.expectation (Y.rawSlice η hη Z)=T.expectation Z ∧
      Y.expectation (X.rawSliceRight η hη Z)=T.expectation Z := by
  let v := fun i => inverseWeight 3 (X.vector i)
  let w := fun j => inverseWeight 3 (Y.vector j)
  let U := fun ij : X.Index × Y.Index => beamUnitary η hη (tensor (v ij.1) (w ij.2))
  have hu : Summable (fun ij => ‖U ij‖^2) := by
    simpa only [U,LinearIsometryEquiv.norm_map] using
      tensorFamily_summable v w X.normalized.summable Y.normalized.summable
  have hd := physical_ensemble_output η hη ρ σ τ hτ v w X.normalized Y.normalized X.density Y.density
  have hs := slice_family_summable U hu
  have he : CrossEnsemble.operator (fun ie : (X.Index × Y.Index) × NumberIndex n => slice (U ie.1) ie.2)
      (fun ie : (X.Index × Y.Index) × NumberIndex n => slice (U ie.1) ie.2)=
    CrossEnsemble.operator (fun i => inverseWeight 3 (T.vector i)) (fun i => inverseWeight 3 (T.vector i)) := by
    rw [cross_slice_eq_partialTrace]
    change partialTrace U=TraceEnsemble.operator _
    rw [T.density]
    exact hd
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hp := CrossEnsemble.pairing_eq_of_operator_eq bas hs hs T.normalized.summable T.normalized.summable he Z
  have hpair : CrossEnsemble.pairing (fun ij : X.Index × Y.Index => tensor (v ij.1) (w ij.2))
      (fun ij : X.Index × Y.Index => tensor (v ij.1) (w ij.2)) (conjugate η hη Z)=T.expectation Z := by
    calc
      _ = CrossEnsemble.pairing U U (liftLeft Z) := by
        unfold CrossEnsemble.pairing
        congr 1
        funext ij
        exact conjugate_inner η hη Z _ _
      _ = _ := (pairing_liftLeft U U hu hu Z).trans hp
  constructor
  · rw [← hpair]
    exact (pairing_conditionalLeft v v w X.normalized.summable X.normalized.summable Y.normalized
      (conjugate η hη Z)).symm
  · rw [← hpair]
    exact (pairing_conditionalRight v w w X.normalized Y.normalized.summable Y.normalized.summable
      (conjugate η hη Z)).symm

theorem replaced_threeport_centered_weak
    {n : ℕ} (η θ κ a b d : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ σ τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η ρ σ m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (X : WeightedColumns ρ) (Y : WeightedColumns σ) (D : WeightedColumns τD)
    (M : WeightedColumns m) (G : WeightedColumns γ) (O : WeightedColumns ω) (R : WeightedColumns ρ0)
    (hd : 0<d) (hr0 : 0<θ*(η*a+(1-η)*b)+(1-θ)*d)
    (hD : ∀ k l, entry τD.op k l=if k=l then (thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (thermalWeight n (θ*(η*a+(1-η)*b)+(1-θ)*d) k:ℂ) else 0)
    (hrepl : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op)
    (j : Fin n) (Z : Fock n →L[ℂ] Fock n) :
    R.centeredWeak (θ*(η*a+(1-η)*b)+(1-θ)*d) j Z=
      ((1-κ:ℝ):ℂ)*((Real.sqrt θ:ℂ)*(Real.sqrt η:ℂ)*
        X.centeredWeak a j (Y.rawSlice η hη (D.rawSlice θ hθ Z))+
        (Real.sqrt θ:ℂ)*(Real.sqrt (1-η):ℂ)*
        Y.centeredWeak b j (X.rawSliceRight η hη (D.rawSlice θ hθ Z)))+
      (κ:ℂ)*((1-κ:ℝ):ℂ)*G.weakMean (θ*(η*a+(1-η)*b)+(1-θ)*d) j*
        (G.expectation Z-O.expectation Z) := by
  let r0 := θ*(η*a+(1-η)*b)+(1-θ)*d
  have hp (A : Fock n →L[ℂ] Fock n) := replaced_threeport_weak η θ κ a b d hη hθ
    ρ σ τD m γ ω ρ0 h1 h2 X Y D M G O R hd hr0 hD hO hrepl j A
  have hg (A : Fock n →L[ℂ] Fock n) := replaced_threeport_weak η θ 0 a b d hη hθ
    ρ σ τD m γ ω γ h1 h2 X Y D M G O G hd hr0 hD hO (by
      simp only [sub_zero,Complex.ofReal_one,Complex.ofReal_zero,one_smul]
      apply ContinuousLinearMap.ext
      intro vector
      simp only [add_apply,smul_apply,zero_smul,add_zero]) j A
  have hmG : G.weakMean r0 j=(Real.sqrt θ:ℂ)*(Real.sqrt η:ℂ)*X.weakMean a j+
      (Real.sqrt θ:ℂ)*(Real.sqrt (1-η):ℂ)*Y.weakMean b j := by
    simpa only [WeightedColumns.weakMean,WeightedColumns.rawSlice_one,WeightedColumns.rawSliceRight_one,
      sub_zero,Complex.ofReal_one,one_mul] using hg 1
  have hmR : R.weakMean r0 j=((1-κ:ℝ):ℂ)*G.weakMean r0 j := by
    rw [hmG]
    simpa only [WeightedColumns.weakMean,WeightedColumns.rawSlice_one,WeightedColumns.rawSliceRight_one] using hp 1
  have he2 := (physical_rawSlice_expectation θ hθ m τD γ h2 M D G Z).1
  have he1 := physical_rawSlice_expectation η hη ρ σ m h1 X Y M (D.rawSlice θ hθ Z)
  have hex := he1.1.trans he2
  have hey := he1.2.trans he2
  have her := G.expectation_affine O R ((1-κ:ℝ):ℂ) (κ:ℂ) hrepl Z
  change R.centeredWeak r0 j Z=_
  unfold WeightedColumns.centeredWeak
  rw [hp,hmR,her,hex,hey,hmG]
  simp only [Complex.ofReal_sub,Complex.ofReal_one]
  ring
end EntropyPhotonNumber

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

end BeamLadder

namespace EntropyPhotonNumber

namespace WeightedColumns
open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

end WeightedColumns

end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber
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
open QuantumTrace Annihilation BeamLadder TensorLp


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.replaced_threeport_centered_weak := @_root_.OAI.EntropyPhotonNumber.replaced_threeport_centered_weak
