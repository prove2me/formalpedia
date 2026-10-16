-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.SpectralLogData.entropy_production
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:25:46.120708+00:00
-- url     : https://prove2.me/submissions/4437e600-108f-4aea-94e8-786317e99a97

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/SpectralLog.lean:L312-L329
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.SpectralLogData.entropy_production. The node keeps its source
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
import Theorems.Thm_OAI_CrossEnsemble_operator_comp_left
import Theorems.Thm_OAI_ThermalMetric_defectVector_mem_centeredSpace
import Theorems.Thm_OAI_WeightedGenerator_centered_K_sum
import Theorems.Thm_OAI_WeightedGenerator_thermal_log_spectral

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

theorem operator_adjoint {u v : I → E} (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) : (operator u v).adjoint=operator v u := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hh := (entry_hasSum hu hv y x).mapL Complex.conjCLE.toContinuousLinearMap
  change HasSum (fun i => conj (inner ℂ y (u i)*inner ℂ (v i) x))
    (conj (inner ℂ y (operator u v x))) at hh
  simp only [map_mul, inner_conj_symm] at hh
  have hh' : HasSum (fun i => inner ℂ x (v i)*inner ℂ (u i) y)
      (inner ℂ (operator u v x) y) := by
    convert! hh using 1
    ext i
    ring
  exact hh'.unique (entry_hasSum hv hu x y)

theorem operator_sandwich {u v : I → E} (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (Z : E →L[ℂ] E) :
    Z ∘L operator u v ∘L Z.adjoint=operator (fun i => Z (u i)) (fun i => Z (v i)) := by
  have hr : operator u v ∘L Z.adjoint=operator u (fun i => Z (v i)) := by
    have hh := congrArg ContinuousLinearMap.adjoint (operator_comp_left hv hu Z)
    simpa only [ContinuousLinearMap.adjoint_comp, operator_adjoint hv hu,
      operator_adjoint (applied_summable hv Z) hu] using hh
  rw [hr, operator_comp_left hu (applied_summable hv Z) Z]
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

-- ---- from OAI.InformationTheory.PhotonNumber.Gibbs ----
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace TraceEnsemble

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber

end EntropyPhotonNumber

namespace WeightedShift
open scoped BigOperators ComplexConjugate
variable {I K : Type*} [DecidableEq K]

end WeightedShift

namespace EntropyPhotonNumber
open QuantumTrace WeightedShift Annihilation
variable {n : ℕ}

end EntropyPhotonNumber

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped ComplexConjugate
variable {n : ℕ}

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end WeightedGenerator

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation
variable {n : ℕ} {J : Type*}

end EntropyPhotonNumber

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem sandwich_injective (X : E →L[ℂ] E) (hX : IsSelfAdjoint X)
    (hi : Function.Injective X) {A B : E →L[ℂ] E}
    (h : X ∘L A ∘L X = X ∘L B ∘L X) : A = B := by
  have hr : A ∘L X = B ∘L X := by
    ext y
    exact hi (congrArg (fun T : E →L[ℂ] E => T y) h)
  have hl := congrArg ContinuousLinearMap.adjoint hr
  simp only [ContinuousLinearMap.adjoint_comp, show X.adjoint=X from hX] at hl
  have ha : A.adjoint=B.adjoint := by
    ext y
    exact hi (congrArg (fun T : E →L[ℂ] E => T y) hl)
  simpa only [ContinuousLinearMap.adjoint_adjoint] using congrArg ContinuousLinearMap.adjoint ha

theorem pairing_transform (x : I → E) (A B Z : E →L[ℂ] E) :
    pairing (fun i => A (x i)) (fun i => B (x i)) Z =
      pairing x x (B.adjoint ∘L Z ∘L A) := by
  unfold pairing
  apply tsum_congr
  intro i
  exact (ContinuousLinearMap.adjoint_inner_right B (x i) (Z (A (x i)))).symm

theorem pairing_transform_eq (b : HilbertBasis J ℂ E) {K : Type*}
    {x : I → E} {y : K → E} (hx : Summable (fun i => ‖x i‖^2))
    (hy : Summable (fun i => ‖y i‖^2)) (he : operator x x=operator y y)
    (A B Z : E →L[ℂ] E) :
    pairing (fun i => A (x i)) (fun i => B (x i)) Z =
      pairing (fun i => A (y i)) (fun i => B (y i)) Z := by
  rw [pairing_transform, pairing_transform]
  exact pairing_eq_of_operator_eq b hx hx hy hy he _

end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
variable {n : ℕ} {I J K : Type*}

theorem pairing_eq_of_operator_eq (b : HilbertBasis K ℂ (Fock n))
    {x : I → Fock n} {y : J → Fock n} (hx : Summable (fun i => ‖x i‖^2))
    (hy : Summable (fun i => ‖y i‖^2))
    (he : CrossEnsemble.operator x x=CrossEnsemble.operator y y)
    (r : ℝ) (Z : Fock n →L[ℂ] Fock n) : pairing r x Z=pairing r y Z := by
  unfold pairing
  congr 1
  funext j
  simp only [CrossEnsemble.pairing_transform_eq b hx hy he]
end WeightedGenerator

namespace EntropyPhotonNumber
open Annihilation CrossEnsemble
variable {n : ℕ} {J : Type*}

theorem weightedRoot_operator_eq (ρ : State n) (hm : FiniteMoment 6 ρ)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hs : Summable p) (he : ∀ j, ρ.op (b j)=(p j : ℂ) • b j)
    (x : J → Fock n) (hx : Summable (fun j => ‖x j‖^2))
    (hi : ∀ j, inverseWeight 3 (x j)=eigenEnsemble b p j) :
    operator (weightedRoot 3 ρ hm) (weightedRoot 3 ρ hm)=operator x x := by
  apply sandwich_injective (inverseWeight 3) (inverseWeight_selfAdjoint 3) (inverseWeight_injective 3)
  have hleft := operator_sandwich (weightedRoot_summable 3 ρ hm) (weightedRoot_summable 3 ρ hm) (inverseWeight 3)
  have hright := operator_sandwich hx hx (inverseWeight 3)
  rw [show (inverseWeight 3 : Fock n →L[ℂ] Fock n).adjoint=inverseWeight 3 from inverseWeight_selfAdjoint 3] at hleft hright
  rw [hleft, hright]
  simp only [inverse_weightedRoot, hi]
  change TraceEnsemble.operator (rootColumn ρ)=operator (eigenEnsemble b p) (eigenEnsemble b p)
  rw [rootColumn_operator, eigenEnsemble_operator b p hp hs ρ.op ρ.positive.isSymmetric he]
end EntropyPhotonNumber

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
open scoped ComplexConjugate
variable {n : ℕ}

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation

variable {n : ℕ} {k : ℝ} {ρ : State n}

namespace GibbsData
variable (G : GibbsData n k ρ)

end GibbsData
end EntropyPhotonNumber

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation
variable {n : ℕ} {k : ℝ} {ρ : State n}
namespace GibbsData
variable (G : GibbsData n k ρ)

end GibbsData
end EntropyPhotonNumber

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.ThermalMetric ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace ThermalMetric

section
open EntropyPhotonNumber DiagonalForms.System

end

section
open DiagonalForms.System

end

section
open EntropyPhotonNumber
variable {J : Type*}

theorem defectVector_norm_sq (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (d : J × J → ℂ) (hd) :
    ‖defectVector r hr p hp d hd‖^2=∑' a : J × J,
      (1-frequency r (p a.1) (p a.2))*defectCoefficient r (p a.1) (p a.2)*‖d a‖^2 := by
  have hh := lp.hasSum_norm (p := 2) (by norm_num : 0 < (2:ENNReal).toReal) (defectVector r hr p hp d hd)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, defectVector_apply,
    defectVector_entry_norm r _ _ hr (hp _) (hp _)] using hh.tsum_eq.symm

end

section
variable {J : Type*}

theorem defectFunctional_norm_sq (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (d : J × J → ℂ) (hd) :
    ‖defectFunctional r hr p hp d hd‖^2=∑' a : J × J,
      (1-frequency r (p a.1) (p a.2))*defectCoefficient r (p a.1) (p a.2)*‖d a‖^2 := by
  rw [defectFunctional, innerSL_apply_norm, defectVector_norm_sq]

theorem defectFunctional_restrict_norm (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (d : J × J → ℂ) (hd) (P : Submodule ℂ (lp (fun _ : J × J => ℂ) 2))
    (hv : defectVector r hr p hp d hd ∈ P) :
    ‖(defectFunctional r hr p hp d hd).comp P.subtypeL‖=
      ‖defectFunctional r hr p hp d hd‖ := by
  have he : (defectFunctional r hr p hp d hd).comp P.subtypeL =
      innerSL ℂ (⟨defectVector r hr p hp d hd,hv⟩ : P) := by
    ext z
    rfl
  rw [he, innerSL_apply_norm, defectFunctional, innerSL_apply_norm]
  rfl
end

open scoped ComplexConjugate
variable {J : Type*}

theorem centered_defect_norm_sq (r : ℝ) (hr : 0<r) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) (d : J × J → ℂ) (hd)
    (hc : HasSum (fun j => (p j:ℂ)*d (j,j)) 0) :
    ‖(defectFunctional r hr p hp d hd).comp (centeredSpace r hr p hp hs).subtypeL‖^2=
      ∑' a : J × J, (1-frequency r (p a.1) (p a.2))*defectCoefficient r (p a.1) (p a.2)*‖d a‖^2 := by
  rw [defectFunctional_restrict_norm r hr p hp d hd _
    (defectVector_mem_centeredSpace r hr p hp hs d hd hc), defectFunctional_norm_sq]

theorem coefficient_series_summable (t : ℝ) (p : J → ℝ) (d : J × J → ℂ)
    (h₁ : Summable (fun a : J × J => p a.2*‖d a‖^2))
    (h₂ : Summable (fun a : J × J => p a.1*‖d a‖^2)) :
    Summable (fun a : J × J => defectCoefficient t (p a.1) (p a.2)*‖d a‖^2) := by
  convert! (h₁.mul_left (t+1)).sub (h₂.mul_left t) using 1
  ext a
  simp only [defectCoefficient]
  ring

theorem production_series_subtraction (t : ℝ) (p : J → ℝ) (c : J → ℝ)
    (hc : ∀ j, c j = -Real.log (p j)) (d : J × J → ℂ)
    (hd : Summable (fun a : J × J => (1-frequency t (p a.1) (p a.2))*
      defectCoefficient t (p a.1) (p a.2)*‖d a‖^2))
    (hk : Summable (fun a : J × J => defectCoefficient t (p a.1) (p a.2)*‖d a‖^2)) :
    (∑' a : J × J, (c a.1-c a.2)*defectCoefficient t (p a.1) (p a.2)*‖d a‖^2)/h t =
      (∑' a : J × J, (1-frequency t (p a.1) (p a.2))*
        defectCoefficient t (p a.1) (p a.2)*‖d a‖^2)-
      (∑' a : J × J, defectCoefficient t (p a.1) (p a.2)*‖d a‖^2) := by
  rw [← tsum_div_const, ← hd.tsum_sub hk]
  apply tsum_congr
  intro a
  simp only [hc, frequency]
  ring

theorem diagonal_mean_summable (p : J → ℝ) (hp : ∀ j, 0≤p j) (hs : Summable p)
    (d : J × J → ℂ) (hd : Summable (fun a : J × J => p a.2*‖d a‖^2)) :
    Summable (fun j => (p j:ℂ)*d (j,j)) := by
  have hi : Function.Injective (fun j : J => (j,j)) := fun _ _ he => (Prod.mk.inj he).1
  have hh := hd.comp_injective hi
  apply Summable.of_norm_bounded (hh.add hs)
  intro j
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp j)]
  have hn : ‖d (j,j)‖≤‖d (j,j)‖^2+1 := by nlinarith [sq_nonneg (‖d (j,j)‖-1)]
  simpa only [mul_add, mul_one, Function.comp_apply] using mul_le_mul_of_nonneg_left hn (hp j)

theorem diagonal_centering (p : J → ℝ) (hs : HasSum p 1)
    (d : J × J → ℂ) (hd : Summable (fun j => (p j:ℂ)*d (j,j))) :
    HasSum (fun j => (p j:ℂ)*(d (j,j)-diagonalMean p d)) 0 := by
  have hh := hd.hasSum.sub ((Complex.hasSum_ofReal.mpr hs).mul_right (diagonalMean p d))
  simpa only [diagonalMean, Complex.ofReal_one, one_mul, sub_self, mul_sub] using hh

end ThermalMetric

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate BigOperators
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace Annihilation
open EntropyPhotonNumber
variable {n : ℕ} {J : Type*}

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate BigOperators
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber.GibbsData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end EntropyPhotonNumber.GibbsData

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace ThermalMetric
open scoped ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalMetric

namespace EntropyPhotonNumber.GibbsData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end EntropyPhotonNumber.GibbsData

namespace Annihilation
open EntropyPhotonNumber
variable {n : ℕ}

end Annihilation

namespace EntropyPhotonNumber
open Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

end EntropyPhotonNumber

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace EntropyPhotonNumber.GibbsData
open Annihilation WeightedGenerator
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end EntropyPhotonNumber.GibbsData

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.SpectralLog ----
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
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace SquareAnalysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I : Type*}

variable [CompleteSpace E]

end SquareAnalysis

namespace QuantumTrace
open scoped ComplexConjugate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace Annihilation

namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n}

end GibbsData
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

theorem spectralColumns_operator (hm : FiniteMoment 6 ρ) :
    CrossEnsemble.operator (weightedRoot 3 ρ hm) (weightedRoot 3 ρ hm)=
      CrossEnsemble.operator G.spectralColumns G.spectralColumns := by
  exact weightedRoot_operator_eq ρ hm G.basis G.probability
    (fun r => (G.probability_pos r).le) G.probability_sum.summable G.eigen
    G.spectralColumns G.spectralColumns_summable G.spectralColumns_inverse

theorem thermalGenerator_logarithmic_trace (hm : FiniteMoment 6 ρ) (t : ℝ) :
    (WeightedGenerator.pairing t (weightedRoot 3 ρ hm) G.logSandwich).re =
      ∑ j, ∑' a : G.J × G.J,
        (G.logCoefficient a.1-G.logCoefficient a.2)*
        ((t+1)*G.probability a.2-t*G.probability a.1)*
        ‖WeightedGenerator.loweringEntry G.basis G.probability G.spectralColumns j a.1 a.2‖^2 := by
  rw [WeightedGenerator.pairing_eq_of_operator_eq G.basis
    (weightedRoot_summable 3 ρ hm) G.spectralColumns_summable (G.spectralColumns_operator hm)]
  exact WeightedGenerator.thermal_log_spectral G.basis G.probability G.probability_pos
    G.spectralColumns G.spectralColumns_summable G.spectralColumns_inverse
    G.logSandwich G.logSandwich_symmetric G.logCoefficient G.logCoefficient_nonneg
    G.logSandwich_parseval G.logSandwich_preimage t

end SpectralLogData
end EntropyPhotonNumber

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

theorem annihilation_mean_summable (j : Fin n) :
    Summable (fun r => (G.probability r:ℂ)*G.annihilationMatrix j (r,r)) := by
  apply diagonal_mean_summable G.probability (fun r => (G.probability_pos r).le)
    G.probability_sum.summable
  have hh := nonlog_summable G.basis G.spectralColumns G.spectralColumns_summable j false
  simpa only [spectralGain_lowering_sq G.basis G.probability G.probability_pos,
    annihilationMatrix] using hh

theorem centeredMatrix_mean_zero (j : Fin n) :
    HasSum (fun r => (G.probability r:ℂ)*G.centeredMatrix j (r,r)) 0 := by
  classical
  simpa only [centeredMatrix, centeredEntry, ↓reduceIte, annihilationMean, annihilationMatrix]
    using diagonal_centering G.probability G.probability_sum
      (G.annihilationMatrix j) (G.annihilation_mean_summable j)

theorem defect_norm_sq (t : ℝ) (ht : 0<t) (j : Fin n) :
    ‖G.defect t ht j‖^2=∑' a : G.J × G.J,
      (1-frequency t (G.probability a.1) (G.probability a.2))*
      defectCoefficient t (G.probability a.1) (G.probability a.2)*‖G.centeredMatrix j a‖^2 :=
  centered_defect_norm_sq t ht G.probability G.probability_pos G.probability_sum.summable
    (G.centeredMatrix j) (G.centeredMatrix_defect_summable t j) (G.centeredMatrix_mean_zero j)

theorem thermalGenerator_centered_logarithmic_trace (hm : FiniteMoment 6 ρ) (t : ℝ) :
    (WeightedGenerator.pairing t (weightedRoot 3 ρ hm) G.logSandwich).re =
      ∑ j, ∑' a : G.J × G.J,
        (G.logCoefficient a.1-G.logCoefficient a.2)*
        defectCoefficient t (G.probability a.1) (G.probability a.2)*‖G.centeredMatrix j a‖^2 := by
  classical
  rw [G.thermalGenerator_logarithmic_trace hm t]
  apply Finset.sum_congr rfl
  intro j _
  apply tsum_congr
  intro a
  by_cases he : a.1=a.2
  · simp only [he, sub_self, zero_mul]
  · simp only [centeredMatrix, centeredEntry, he, ↓reduceIte, sub_zero, defectCoefficient]

theorem entropy_production (hm : FiniteMoment 6 ρ) (t : ℝ) (ht : 0<t) :
    (WeightedGenerator.pairing t (weightedRoot 3 ρ hm) G.logSandwich).re/h t =
      (∑ j, ‖G.defect t ht j‖^2)-(G.centeredEnergy-(n:ℝ)*t) := by
  rw [G.thermalGenerator_centered_logarithmic_trace hm t, Finset.sum_div]
  have hj (j : Fin n) :
      (∑' a : G.J × G.J, (G.logCoefficient a.1-G.logCoefficient a.2)*
        defectCoefficient t (G.probability a.1) (G.probability a.2)*‖G.centeredMatrix j a‖^2)/h t =
        ‖G.defect t ht j‖^2-
        ∑' a : G.J × G.J, defectCoefficient t (G.probability a.1) (G.probability a.2)*‖G.centeredMatrix j a‖^2 := by
    rw [G.defect_norm_sq t ht j]
    have hh := G.centeredMatrix_six_sums j
    exact production_series_subtraction t G.probability G.logCoefficient (fun _ => rfl)
      (G.centeredMatrix j) (G.centeredMatrix_defect_summable t j)
      (coefficient_series_summable t G.probability (G.centeredMatrix j) hh.1 hh.2.1)
  simp only [hj, Finset.sum_sub_distrib]
  congr 1
  exact centered_K_sum G.basis G.probability G.probability_pos G.spectralColumns
    G.spectralColumns_summable G.spectralColumns_inverse G.spectralColumns_normalized G.annihilationMean t

end EntropyPhotonNumber.SpectralLogData

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation
variable {n : ℕ} {J : Type} {ρ : State n}

end

end EntropyPhotonNumber

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber
open QuantumTrace TraceEnsemble

end EntropyPhotonNumber

namespace QuantumTrace

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I : Type*}

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace

end

open QuantumTrace Annihilation
variable {n : ℕ}

end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.SpectralLogData
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
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open QuantumTrace Annihilation WeightedGenerator ThermalMetric


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.SpectralLogData.entropy_production := @_root_.OAI.EntropyPhotonNumber.SpectralLogData.entropy_production
