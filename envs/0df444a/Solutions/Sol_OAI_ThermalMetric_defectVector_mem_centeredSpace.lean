-- Prove2me | solution 1 for OAI.ThermalMetric.defectVector_mem_centeredSpace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:21:56.049254+00:00
-- url     : https://prove2.me/submissions/1e7af103-7fa7-4b2e-abec-6dcd83bfb7e9

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/ThermalMetric.lean:L259-L283
-- (upload_full_project.md Phase 4): solution for node OAI.ThermalMetric.defectVector_mem_centeredSpace. The node keeps its source
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

theorem defectVector_pairing (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (d : J × J → ℂ) (hd) (z : J × J → ℂ)
    (hz : Summable (fun a : J × J => metricCoefficient r (p a.1) (p a.2)*‖z a‖^2)) :
    HasSum (fun a : J × J => (defectCoefficient r (p a.1) (p a.2):ℂ)*conj (d a)*z a)
      (inner ℂ (defectVector r hr p hp d hd)
        (weightedVector (fun a => metricCoefficient r (p a.1) (p a.2)) z hz
          (fun a => (metricCoefficient_pos hr (hp a.1) (hp a.2)).le))) := by
  have hh := lp.hasSum_inner (𝕜 := ℂ) (defectVector r hr p hp d hd)
    (weightedVector (fun a => metricCoefficient r (p a.1) (p a.2)) z hz
      (fun a => (metricCoefficient_pos hr (hp a.1) (hp a.2)).le))
  convert! hh using 1
  ext a
  simp only [defectVector_apply, weightedVector_apply, RCLike.inner_apply,
    map_mul, Complex.ofReal_div, map_div₀, Complex.conj_ofReal]
  have hn : (Real.sqrt (metricCoefficient r (p a.1) (p a.2)):ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (metricCoefficient_pos hr (hp a.1) (hp a.2))).ne'
  field_simp

end

section
variable {J : Type*}

end

open scoped ComplexConjugate
variable {J : Type*}

theorem hasSum_diagonal [DecidableEq J] {f : J → ℂ} {s : ℂ} (hf : HasSum f s) :
    HasSum (fun a : J × J => if a.1=a.2 then f a.1 else 0) s := by
  have hi : Function.Injective (fun j : J => (j,j)) := fun _ _ he => (Prod.mk.inj he).1
  apply (hi.hasSum_iff (fun a ha => ?_)).mp
  · simpa only [Function.comp_def, ↓reduceIte] using hf
  · have hn : a.1≠a.2 := by
      intro he
      apply ha
      exact ⟨a.1, Prod.ext rfl he⟩
    simp only [hn, ↓reduceIte]

theorem defectVector_mem_centeredSpace (r : ℝ) (hr : 0<r) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) (d : J × J → ℂ) (hd)
    (hc : HasSum (fun j => (p j:ℂ)*d (j,j)) 0) :
    defectVector r hr p hp d hd ∈ centeredSpace r hr p hp hs := by
  classical
  have ht := hasSum_diagonal (Complex.hasSum_conj'.mpr hc)
  have hz : HasSum (fun a : J × J => (defectCoefficient r (p a.1) (p a.2):ℂ)*
      conj (d a)*identityEntry a) 0 := by
    convert! ht using 1
    · ext a
      by_cases he : a.1=a.2
      · obtain ⟨l,q⟩ := a
        dsimp only [Prod.fst, Prod.snd] at he ⊢
        subst q
        simp only [identityEntry, ↓reduceIte, mul_one, map_mul, Complex.conj_ofReal]
        congr 1
        unfold defectCoefficient
        push_cast
        ring
      · simp only [identityEntry, he, ↓reduceIte, mul_zero]
    · simp
  have hh := defectVector_pairing r hr p hp d hd identityEntry (identityEntry_summable r hr p hp hs)
  have he : inner ℂ (defectVector r hr p hp d hd) (identityVector r hr p hp hs)=0 := hh.unique hz
  change inner ℂ (identityVector r hr p hp hs) (defectVector r hr p hp d hd)=0
  rw [← inner_conj_symm, he, map_zero]

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

-- ---- platform node ----
open OAI OAI.ThermalMetric
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped ComplexConjugate


theorem solution : type_of% @_root_.OAI.ThermalMetric.defectVector_mem_centeredSpace := @_root_.OAI.ThermalMetric.defectVector_mem_centeredSpace
