-- Prove2me | solution 1 for OAI.ThermalDual.dual_bound_from_core
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:22:43.047302+00:00
-- url     : https://prove2.me/submissions/37657872-3961-4d4d-860a-80e0e0a4d850

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Duality.lean:L421-L456
-- (upload_full_project.md Phase 4): solution for node OAI.ThermalDual.dual_bound_from_core. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Duality
import Theorems.Thm_OAI_CrossEnsemble_operator_comp_left
import Theorems.Thm_OAI_DiagonalForms_System_comparison_logMean
import Theorems.Thm_OAI_EnsembleL2_secondMoment_eq_of_operator_eq
import Theorems.Thm_OAI_EntropyPhotonNumber_logarithmicMean_exp_pair

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

-- ---- from OAI.Analysis.DiagonalForms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace DiagonalForms.System
end DiagonalForms.System

namespace QuantumCalculus
end QuantumCalculus

namespace DiagonalForms.System
end DiagonalForms.System

namespace DiagonalForms.System
open EntropyPhotonNumber

theorem logMean_arithmetic_plus {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    logMean p q*f ((Real.log p-Real.log q)/2)*Real.exp ((Real.log p-Real.log q)/2)=p := by
  rw [logMean_mul_f hp hq, ← Real.exp_add]
  convert Real.exp_log hp using 1
  congr 1
  ring

theorem logMean_arithmetic_minus {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    logMean p q*f ((Real.log p-Real.log q)/2)*Real.exp (-((Real.log p-Real.log q)/2))=q := by
  rw [logMean_mul_f hp hq, ← Real.exp_add]
  convert Real.exp_log hq using 1
  congr 1
  ring

end DiagonalForms.System

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
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace DiagonalForms

namespace System

variable {P I J : Type*} (D : System P I J)

end System

end DiagonalForms

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

section CompactIntegral
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (k₀ : K)

end CompactIntegral
end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (k₀ : K)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]

end DiagonalForms.System

namespace DiagonalForms.System
open Function
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

end

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

theorem weightedVector_norm_sq (a : J → ℝ) (z : J → ℂ)
    (hz : Summable (fun j => a j*‖z j‖^2)) (ha : ∀ j, 0 ≤ a j) :
    ‖weightedVector a z hz ha‖^2=∑' j, a j*‖z j‖^2 := by
  have hh := lp.hasSum_norm (p := 2) (by norm_num : 0 < (2:ENNReal).toReal) (weightedVector a z hz ha)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, weightedVector_apply, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (ha _)] using hh.tsum_eq.symm

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

-- ---- from OAI.InformationTheory.PhotonNumber.SpectralForms ----
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
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory

namespace BKM

section
open scoped ComplexConjugate
variable {J K E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem hasSum_row (b : HilbertBasis J ℂ E) (Z : E →L[ℂ] E) (i : J) :
    HasSum (fun j => Complex.normSq (entry b Z i j)) (‖Z.adjoint (b i)‖^2) := by
  have h := hasSum_column b Z.adjoint i
  simpa only [entry_adjoint, Complex.normSq_conj] using h

end

open scoped BigOperators
variable {J : Type*}

end BKM

namespace SpectralTests
open scoped BigOperators ComplexConjugate
variable {A I P : Type*}

end SpectralTests

namespace CenteredTests
open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable [CompleteSpace E]

end CenteredTests

namespace ThermalMetric

section
open scoped ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section
open scoped ComplexConjugate
variable {J : Type*}

theorem centerProjection_mem (e x : lp (fun _ : J => ℂ) 2)
    (he : inner ℂ e e=1) : centerProjection e x ∈ (innerSL ℂ e).ker := by
  change inner ℂ e (x-inner ℂ e x • e)=0
  simp only [inner_sub_right, inner_smul_right, he, mul_one, sub_self]

theorem centerProjection_eq (e x : lp (fun _ : J => ℂ) 2)
    (hx : x ∈ (innerSL ℂ e).ker) : centerProjection e x=x := by
  change inner ℂ e x=0 at hx
  simp only [centerProjection_apply, hx, zero_smul, sub_zero]

variable [DecidableEq J]

theorem centered_single_dense (e : lp (fun _ : J => ℂ) 2)
    (he : inner ℂ e e=1) :
    (Submodule.span ℂ (Set.range (fun j => centerProjection e (lp.single 2 j (1:ℂ))))).topologicalClosure =
      (innerSL ℂ e).ker := by
  classical
  let S := Submodule.span ℂ (Set.range (fun j => centerProjection e (lp.single 2 j (1:ℂ))))
  apply le_antisymm
  · apply S.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact centerProjection_mem _ _ he
    · exact (innerSL ℂ e).isClosed_ker
  · intro x hx
    have hh := (lp.hasSum_single (by norm_num : (2:ENNReal)≠⊤) x).mapL (centerProjection e)
    rw [centerProjection_eq _ _ hx] at hh
    apply S.isClosed_topologicalClosure.mem_of_tendsto hh
    apply Filter.Eventually.of_forall
    intro s
    apply S.topologicalClosure.sum_mem
    intro j _
    have hs : centerProjection e (lp.single 2 j (x j)) ∈ S := by
      have hsingle : lp.single (E := fun _ : J => ℂ) 2 j (x j)=(x j) • lp.single 2 j (1:ℂ) := by
        rw [← lp.single_smul]
        simp only [smul_eq_mul, mul_one]
      rw [hsingle, map_smul]
      exact S.smul_mem _ (Submodule.subset_span ⟨j,rfl⟩)
    exact S.le_topologicalClosure hs

theorem identityVector_inner (r : ℝ) (hr : 0<r) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : HasSum p 1) :
    inner ℂ (identityVector r hr p hp hs.summable) (identityVector r hr p hp hs.summable)=1 := by
  classical
  have hh := hasSum_diagonal (Complex.hasSum_ofReal.mpr hs)
  have ht := lp.hasSum_inner (𝕜 := ℂ) (identityVector r hr p hp hs.summable)
    (identityVector r hr p hp hs.summable)
  apply ht.unique
  convert! hh using 1
  ext ij
  simp only [identityVector_apply, RCLike.inner_apply]
  split_ifs with he
  · simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hp _).le]
  · simp

theorem matrixGenerator_projection (r : ℝ) (hr : 0<r) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) (ij : J × J) :
    matrixGenerator r hr p hp hs ij =
      (Real.sqrt (metricCoefficient r (p ij.1) (p ij.2)):ℂ) •
        centerProjection (identityVector r hr p hp hs) (lp.single 2 ij 1) := by
  classical
  rw [matrixGenerator, centerProjection_apply, smul_sub, smul_smul]
  congr 1
  congr 1
  rw [lp.inner_single_right, RCLike.inner_apply, one_mul, identityVector_apply]
  split_ifs with he
  · rw [he, metricCoefficient_self hr (hp _), Complex.conj_ofReal,
      ← Complex.ofReal_mul, Real.mul_self_sqrt (hp _).le]
  · simp

theorem matrixGenerator_dense (r : ℝ) (hr : 0<r) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : HasSum p 1) :
    (Submodule.span ℂ (Set.range (matrixGenerator r hr p hp hs.summable))).topologicalClosure =
      centeredSpace r hr p hp hs.summable := by
  let e := identityVector r hr p hp hs.summable
  have hh := centered_single_dense e (identityVector_inner r hr p hp hs)
  have he : Submodule.span ℂ (Set.range (matrixGenerator r hr p hp hs.summable))=
      Submodule.span ℂ (Set.range (fun j => centerProjection e (lp.single 2 j (1:ℂ)))) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨ij,rfl⟩
      rw [matrixGenerator_projection]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij,rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨ij,rfl⟩
      have hz : (Real.sqrt (metricCoefficient r (p ij.1) (p ij.2)):ℂ)≠0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (metricCoefficient_pos hr (hp _) (hp _)))
      have ht : centerProjection e (lp.single 2 ij 1)=
          (Real.sqrt (metricCoefficient r (p ij.1) (p ij.2)):ℂ)⁻¹ • matrixGenerator r hr p hp hs.summable ij := by
        rw [matrixGenerator_projection, smul_smul, inv_mul_cancel₀ hz, one_smul]
      dsimp only
      rw [ht]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij,rfl⟩)
  rw [he]
  exact hh
end

open scoped ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem observable_core_dense (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1) (t : ℝ) (ht : 0 < t) :
    ((CenteredTests.operatorSpace b p).map
      (observableMap b p hp hs.summable t ht)).topologicalClosure =
      centeredSpace t ht p hp hs.summable := by
  classical
  rw [CenteredTests.operatorSpace, Submodule.map_span, ← Set.range_comp]
  simpa only [Function.comp_def, observableMap_generator] using
    matrixGenerator_dense t ht p hp hs

theorem functional_bound_of_core (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1) (t : ℝ) (ht : 0 < t)
    (q : lp (fun _ : J × J => ℂ) 2 →L[ℂ] ℂ) (C : ℝ)
    (hc : ∀ Z, Z ∈ CenteredTests.operatorSpace b p →
      ‖q (observableMap b p hp hs.summable t ht Z)‖ ≤
        C*‖observableMap b p hp hs.summable t ht Z‖) :
    ∀ x ∈ centeredSpace t ht p hp hs.summable, ‖q x‖ ≤ C*‖x‖ := by
  have hclosed : IsClosed {x : lp (fun _ : J × J => ℂ) 2 | ‖q x‖ ≤ C*‖x‖} :=
    isClosed_le q.continuous.norm (continuous_const.mul continuous_norm)
  have himage : (((CenteredTests.operatorSpace b p).map
      (observableMap b p hp hs.summable t ht) : Submodule ℂ _) : Set _) ⊆
        {x | ‖q x‖ ≤ C*‖x‖} := by
    rintro _ ⟨Z,hZ,rfl⟩
    exact hc Z hZ
  have hh := closure_minimal himage hclosed
  rw [← Submodule.topologicalClosure_coe, observable_core_dense b p hp hs t ht] at hh
  exact hh

theorem restricted_norm_bound_of_core (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1) (t : ℝ) (ht : 0 < t)
    (q : lp (fun _ : J × J => ℂ) 2 →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ Z, Z ∈ CenteredTests.operatorSpace b p →
      ‖q (observableMap b p hp hs.summable t ht Z)‖ ≤
        C*‖observableMap b p hp hs.summable t ht Z‖) :
    ‖q.comp (centeredSpace t ht p hp hs.summable).subtypeL‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  exact functional_bound_of_core b p hp hs t ht q C hc x.val x.property

end ThermalMetric

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
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace CenteredTests
open scoped BigOperators
variable {J T E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem realize_entries (b : HilbertBasis J ℂ E) (p : J → ℝ) (w : J × J → ℝ)
    (hw : ∀ ij, 0 < w ij) (z : coordinates b p w) : entryMap b w (realize b p w hw z)=z.val := by
  exact LinearEquiv.ofInjective_symm_apply (h := entryMap_injective b w hw) _ _

omit [CompleteSpace E] in
theorem realize_mem (b : HilbertBasis J ℂ E) (p : J → ℝ) (w : J × J → ℝ)
    (hw : ∀ ij, 0 < w ij) (z : coordinates b p w) : realize b p w hw z ∈ operatorSpace b p := by
  obtain ⟨Z,hZ,he⟩ := z.property
  have hh : realize b p w hw z=Z := entryMap_injective b w hw ((realize_entries b p w hw z).trans he.symm)
  rw [hh]
  exact hZ

end CenteredTests

namespace ThermalMetric
open EntropyPhotonNumber DiagonalForms.System

end ThermalMetric

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

namespace Space
variable (S : Space E)
theorem base_pos (ij : S.I × S.I) : 0 < S.base ij := mul_pos (h_pos S.rpos) (logMean_pos (S.pos _) (S.pos _))
theorem coords_norm (Z : E →L[ℂ] E) (ij : S.I × S.I) :
    Complex.normSq (S.coords Z ij)=S.base ij*Complex.normSq (BKM.entry S.basis Z ij.1 ij.2) := by
  simp only [coords, CenteredTests.entryMap_apply, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (S.base_pos ij).le]

theorem freq_cancel (ij : S.I × S.I) :
    h S.r*(S.param ij).2/2=(Real.log (S.p ij.1)-Real.log (S.p ij.2))/2 := by
  dsimp [param, frequency]
  field_simp [(h_pos S.rpos).ne']

theorem plus_entry (Z : E →L[ℂ] E) (ij : S.I × S.I) :
    plus (S.param ij)*Complex.normSq (S.coords Z ij)=S.p ij.1*Complex.normSq (BKM.entry S.basis Z ij.1 ij.2) := by
  rw [coords_norm]
  simp only [plus, param]
  have hh := logMean_arithmetic_plus (S.pos ij.1) (S.pos ij.2)
  have hf := S.freq_cancel ij
  change h S.r*frequency S.r (S.p ij.1) (S.p ij.2)/2 = _ at hf
  rw [hf]
  dsimp [base]
  have hn := (h_pos S.rpos).ne'
  field_simp
  linear_combination Complex.normSq (BKM.entry S.basis Z ij.1 ij.2)*hh

theorem minus_entry (Z : E →L[ℂ] E) (ij : S.I × S.I) :
    minus (S.param ij)*Complex.normSq (S.coords Z ij)=S.p ij.2*Complex.normSq (BKM.entry S.basis Z ij.1 ij.2) := by
  rw [coords_norm]
  simp only [minus, param]
  have hh := logMean_arithmetic_minus (S.pos ij.1) (S.pos ij.2)
  have hf := S.freq_cancel ij
  change h S.r*frequency S.r (S.p ij.1) (S.p ij.2)/2 = _ at hf
  rw [hf]
  dsimp [base]
  have hn := (h_pos S.rpos).ne'
  field_simp
  linear_combination Complex.normSq (BKM.entry S.basis Z ij.1 ij.2)*hh

theorem constant_summable (c : ℝ) (Z : E →L[ℂ] E) :
    Summable (fun ij => c*Complex.normSq (S.coords Z ij)) := by
  have hh := ((BKM.logMean_summable S.basis S.p S.pos S.sum.summable Z).mul_left (h S.r)).mul_left c
  simpa only [S.coords_norm, base, mul_assoc] using hh
end Space

theorem plusWeight_pos (q : Param) : 0 < plusWeight q :=
  mul_pos (mul_pos (one_div_pos.mpr (h_pos q.1.property)) (f_pos _)) (Real.exp_pos _)
theorem minusWeight_pos (q : Param) : 0 < minusWeight q :=
  mul_pos (mul_pos (one_div_pos.mpr (h_pos q.1.property)) (f_pos _)) (Real.exp_pos _)

end ThermalSpectral

namespace ThermalMetric
open EntropyPhotonNumber DiagonalForms.System

theorem mixtureConstant_sq {r : ℝ} (hr : 0<r) :
    mixtureConstant r^2=1/(h r*lowerWeight r) := by
  rw [mixtureConstant, inv_pow, Real.sq_sqrt (mul_pos (h_pos hr) (lowerWeight_pos hr)).le, one_div]

theorem BKM_weight_bound {r : ℝ} (hr : 0<r) (v : ℝ) :
    1/h r ≤ mixtureConstant r^2*weight r v := by
  rw [mixtureConstant_sq hr]
  have hh := (lowerWeight_bounds hr).2 v
  have he : (1/(h r*lowerWeight r))*weight r v=weight r v/(h r*lowerWeight r) := by ring
  rw [he]
  apply (div_le_div_iff₀ (h_pos hr) (mul_pos (h_pos hr) (lowerWeight_pos hr))).mpr
  nlinarith [mul_le_mul_of_nonneg_left hh (h_pos hr).le]
end ThermalMetric

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

theorem observable_norm_sq (Z : E →L[ℂ] E) :
    ‖S.observable Z‖^2=S.pquad thermalWeight Z := by
  rw [observable, observableMap, LinearMap.coe_mk, AddHom.coe_mk, weightedVector_norm_sq]
  simp only [pquad, S.coords_norm, Complex.normSq_eq_norm_sq]
  apply tsum_congr
  intro a
  simp only [thermalWeight, pparam, param, base, metricCoefficient]
  ring

theorem thermal_summable (Z : E →L[ℂ] E) :
    Summable (fun ij => thermalWeight (S.pparam ij)*Complex.normSq (S.coords Z ij)) := by
  have hn (ij : S.I × S.I) : 0 ≤ thermalWeight (S.pparam ij)*Complex.normSq (S.coords Z ij) :=
    mul_nonneg (weight_pos S.rpos _).le (Complex.normSq_nonneg _)
  have hb (ij : S.I × S.I) :
      thermalWeight (S.pparam ij)*Complex.normSq (S.coords Z ij) ≤
        (S.r+1)*Complex.normSq (S.coords Z ij) := by
    have hh : thermalWeight (S.pparam ij) ≤ S.r+1 :=
      (weight_frequency_bounds S.rpos (S.pos ij.1) (S.pos ij.2)).2
    exact mul_le_mul_of_nonneg_right hh (Complex.normSq_nonneg _)
  exact Summable.of_nonneg_of_le hn hb (S.constant_summable (S.r+1) Z)

theorem BKM_thermal_bound (Z : E →L[ℂ] E) :
    S.pquad (fun _ => 1/h S.r) Z ≤ mixtureConstant S.r^2*‖S.observable Z‖^2 := by
  rw [S.observable_norm_sq]
  simp only [pquad, ← tsum_mul_left]
  apply Summable.tsum_le_tsum
  · intro a
    have hh := BKM_weight_bound S.rpos (S.param a).2
    exact (mul_le_mul_of_nonneg_right hh (Complex.normSq_nonneg _)).trans_eq (mul_assoc _ _ _)
  · exact S.constant_summable (1/h S.r) Z
  · exact (S.thermal_summable Z).mul_left _

end ThermalSpectral.Space

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation BeamLadder ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

end WeightedGenerator

namespace ThermalSpectral.Space
open EntropyPhotonNumber Annihilation WeightedGenerator ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} (S : Space (Fock n))

end ThermalSpectral.Space

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Contraction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

namespace EnsembleL2

section
open scoped BigOperators ComplexConjugate
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem shifted_secondMoment (v : I → E) (hv : HasSum (fun i => ‖v i‖^2) 1)
    (Z : E →L[ℂ] E) (c : ℂ) :
    secondMoment v (Z-c • ContinuousLinearMap.id ℂ E)=
      secondMoment v Z-2*(c*conj (mean v Z)).re+‖c‖^2 := by
  have hm := ((mean_hasSum v hv.summable Z).mapL Complex.conjCLE.toContinuousLinearMap).mul_left c
  change HasSum (fun i => c*conj (inner ℂ (v i) (Z (v i)))) (c*conj (mean v Z)) at hm
  have hr := (hm.mapL Complex.reCLM).mul_left 2
  have hh := ((image_summable v hv.summable Z).hasSum.sub hr).add (hv.mul_left (‖c‖^2))
  have he (i : I) : ‖(Z-c • ContinuousLinearMap.id ℂ E) (v i)‖^2 =
      ‖Z (v i)‖^2-2*(c*conj (inner ℂ (v i) (Z (v i)))).re+‖c‖^2*‖v i‖^2 := by
    simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply, norm_sub_sq (𝕜 := ℂ),
      inner_smul_right, inner_conj_symm, norm_smul, mul_pow]
    rfl
  have hs : HasSum (fun i => ‖(Z-c • ContinuousLinearMap.id ℂ E) (v i)‖^2)
      (secondMoment v Z-2*(c*conj (mean v Z)).re+‖c‖^2) := by
    simpa only [he, secondMoment, Complex.reCLM_apply, Complex.conjCLE_apply, mul_one] using hh
  exact hs.tsum_eq

theorem center_secondMoment (v : I → E) (hv : HasSum (fun i => ‖v i‖^2) 1)
    (Z : E →L[ℂ] E) :
    secondMoment v (center v Z)=secondMoment v Z-‖mean v Z‖^2 := by
  rw [center, shifted_secondMoment v hv Z, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]
  ring

theorem mixture_norm_left (v : I → E) (w : J → E) {t : ℝ} (ht : 0 ≤ t) (i : I) :
    ‖mixture v w t (.inl i)‖^2=t*‖v i‖^2 := by
  simp only [mixture, Sum.elim_inl, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg t), mul_pow, Real.sq_sqrt ht]

theorem mixture_norm_right (v : I → E) (w : J → E) {t : ℝ} (ht : t ≤ 1) (j : J) :
    ‖mixture v w t (.inr j)‖^2=(1-t)*‖w j‖^2 := by
  simp only [mixture, Sum.elim_inr, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg (1-t)), mul_pow, Real.sq_sqrt (sub_nonneg.mpr ht)]

theorem mixture_hasSum (v : I → E) (w : J → E) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1) :
    HasSum (fun k => ‖mixture v w t k‖^2) 1 := by
  have h₁ : HasSum ((fun k => ‖mixture v w t k‖^2) ∘ Sum.inl) t := by
    simpa only [Function.comp_def, mixture_norm_left v w ht.1, mul_one] using hv.mul_left t
  have h₂ : HasSum ((fun k => ‖mixture v w t k‖^2) ∘ Sum.inr) (1-t) := by
    simpa only [Function.comp_def, mixture_norm_right v w ht.2, mul_one] using hw.mul_left (1-t)
  simpa only [add_sub_cancel] using h₁.sum h₂

theorem mixture_mean (v : I → E) (w : J → E) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2)) (Z : E →L[ℂ] E) :
    mean (mixture v w t) Z=(t:ℂ)*mean v Z+((1-t:ℝ):ℂ)*mean w Z := by
  have he {a : ℝ} (ha : 0 ≤ a) (x : E) :
      inner ℂ ((Real.sqrt a:ℂ) • x) (Z ((Real.sqrt a:ℂ) • x))=(a:ℂ)*inner ℂ x (Z x) := by
    simp only [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt ha]
  have h₁ : HasSum ((fun k => inner ℂ (mixture v w t k) (Z (mixture v w t k))) ∘ Sum.inl)
      ((t:ℂ)*mean v Z) := by
    simpa only [Function.comp_def, mixture, Sum.elim_inl, he ht.1] using
      (mean_hasSum v hv Z).mul_left (t:ℂ)
  have h₂ : HasSum ((fun k => inner ℂ (mixture v w t k) (Z (mixture v w t k))) ∘ Sum.inr)
      (((1-t:ℝ):ℂ)*mean w Z) := by
    simpa only [Function.comp_def, mixture, Sum.elim_inr, he (sub_nonneg.mpr ht.2)] using
      (mean_hasSum w hw Z).mul_left ((1-t:ℝ):ℂ)
  exact (h₁.sum h₂).tsum_eq

theorem mixture_secondMoment (v : I → E) (w : J → E) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2)) (Z : E →L[ℂ] E) :
    secondMoment (mixture v w t) Z=t*secondMoment v Z+(1-t)*secondMoment w Z := by
  have h₁ : HasSum ((fun k => ‖Z (mixture v w t k)‖^2) ∘ Sum.inl) (t*secondMoment v Z) := by
    simpa only [Function.comp_def, mixture, Sum.elim_inl, map_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt ht.1, secondMoment] using
      (image_summable v hv Z).hasSum.mul_left t
  have h₂ : HasSum ((fun k => ‖Z (mixture v w t k)‖^2) ∘ Sum.inr) ((1-t)*secondMoment w Z) := by
    simpa only [Function.comp_def, mixture, Sum.elim_inr, map_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (sub_nonneg.mpr ht.2), secondMoment] using
      (image_summable w hw Z).hasSum.mul_left (1-t)
  exact (h₁.sum h₂).tsum_eq
end

open scoped BigOperators
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem complex_mixture_square (t : ℝ) (a b : ℂ) :
    t*‖a‖^2+(1-t)*‖b‖^2-‖(t:ℂ)*a+((1-t:ℝ):ℂ)*b‖^2 = t*(1-t)*‖a-b‖^2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem mixture_variance (v : I → E) (w : J → E) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1) (Z : E →L[ℂ] E) :
    secondMoment (mixture v w t) (center (mixture v w t) Z)=
      t*secondMoment v (center v Z)+(1-t)*secondMoment w (center w Z)+
        t*(1-t)*‖mean v Z-mean w Z‖^2 := by
  rw [center_secondMoment _ (mixture_hasSum v w ht hv hw),
    mixture_secondMoment v w ht hv.summable hw.summable,
    mixture_mean v w ht hv.summable hw.summable,
    center_secondMoment v hv, center_secondMoment w hw]
  linear_combination complex_mixture_square t (mean v Z) (mean w Z)

theorem mixture_between_variance (v : I → E) (w : J → E) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1) (Z : E →L[ℂ] E) :
    t*(1-t)*‖mean v Z-mean w Z‖^2 ≤ secondMoment (mixture v w t) (center (mixture v w t) Z) := by
  rw [mixture_variance v w ht hv hw Z]
  have h₁ : 0 ≤ t*secondMoment v (center v Z) :=
    mul_nonneg ht.1 (tsum_nonneg (fun _ => sq_nonneg _))
  have h₂ : 0 ≤ (1-t)*secondMoment w (center w Z) :=
    mul_nonneg (sub_nonneg.mpr ht.2) (tsum_nonneg (fun _ => sq_nonneg _))
  linarith
end EnsembleL2

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

theorem ensemble_norm (i : S.I) : ‖S.ensemble i‖^2=S.p i := by
  simp only [ensemble, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), S.basis.orthonormal.norm_eq_one i, mul_one]
  exact Real.sq_sqrt (S.pos i).le

theorem ensemble_hasSum : HasSum (fun i => ‖S.ensemble i‖^2) 1 := by
  simpa only [S.ensemble_norm] using S.sum

theorem image_ensemble_norm (Z : E →L[ℂ] E) (i : S.I) :
    ‖Z (S.ensemble i)‖^2=S.p i*‖Z (S.basis i)‖^2 := by
  simp only [ensemble, map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (S.pos i).le]

theorem minus_quad_ensemble (Z : E →L[ℂ] E) :
    S.quad minus Z=∑' i, ‖Z (S.ensemble i)‖^2 := by
  simp only [quad, S.minus_entry Z, S.image_ensemble_norm Z]
  have hs := BKM.weighted_column_summable S.basis S.p (fun i => (S.pos i).le) S.sum.summable Z
  rw [hs.tsum_prod, ← hs.tsum_comm]
  simp only [tsum_mul_left, (BKM.hasSum_column S.basis Z _).tsum_eq]

theorem plus_quad_ensemble (Z : E →L[ℂ] E) :
    S.quad plus Z=∑' i, ‖Z.adjoint (S.ensemble i)‖^2 := by
  simp only [quad, S.plus_entry Z, S.image_ensemble_norm Z.adjoint]
  rw [(BKM.weighted_row_summable S.basis S.p (fun i => (S.pos i).le) S.sum.summable Z).tsum_prod]
  simp only [tsum_mul_left, (BKM.hasSum_row S.basis Z _).tsum_eq]
end ThermalSpectral.Space

namespace EnsembleL2
open scoped ComplexConjugate
variable {E I J K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem mean_eq_of_operator_eq (b : HilbertBasis K ℂ E) {v : I → E} {w : J → E}
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    (he : TraceEnsemble.operator v=TraceEnsemble.operator w) (Z : E →L[ℂ] E) :
    mean v Z=mean w Z :=
  CrossEnsemble.pairing_eq_of_operator_eq b hv hv hw hw he Z

end EnsembleL2

namespace BKM
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
end BKM

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

theorem ensemble_mean (Z : E →L[ℂ] E) : EnsembleL2.mean S.ensemble Z=BKM.mean S.basis S.p Z := by
  unfold EnsembleL2.mean BKM.mean
  apply tsum_congr
  intro j
  simp only [ensemble, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (S.pos j).le]
  rfl

theorem minus_quad_of_ensemble {I : Type*} (v : I → E)
    (hv : Summable (fun i => ‖v i‖^2)) (he : TraceEnsemble.operator S.ensemble=TraceEnsemble.operator v)
    (Z : E →L[ℂ] E) : S.quad minus Z=EnsembleL2.secondMoment v Z := by
  rw [S.minus_quad_ensemble]
  exact EnsembleL2.secondMoment_eq_of_operator_eq S.basis S.ensemble_hasSum.summable hv he Z

theorem plus_quad_of_ensemble {I : Type*} (v : I → E)
    (hv : Summable (fun i => ‖v i‖^2)) (he : TraceEnsemble.operator S.ensemble=TraceEnsemble.operator v)
    (Z : E →L[ℂ] E) : S.quad plus Z=EnsembleL2.secondMoment v Z.adjoint := by
  rw [S.plus_quad_ensemble]
  exact EnsembleL2.secondMoment_eq_of_operator_eq S.basis S.ensemble_hasSum.summable hv he Z.adjoint
end ThermalSpectral.Space

namespace TensorLp
open KrausBounded
variable {A B I J : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp KrausBounded
open scoped BigOperators ComplexConjugate

end EntropyPhotonNumber

namespace EnsembleL2
open scoped ComplexConjugate
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem mean_adjoint (v : I → E) (Z : E →L[ℂ] E) : mean v Z.adjoint=conj (mean v Z) := by
  simp only [mean, ContinuousLinearMap.adjoint_inner_right, inner_conj_symm, Complex.conj_tsum]

end EnsembleL2

namespace EntropyPhotonNumber
open TensorLp KrausBounded
open scoped BigOperators ComplexConjugate
variable {n : ℕ}

end EntropyPhotonNumber

namespace EnsembleL2
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end EnsembleL2

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace EntropyPhotonNumber
open ThermalSpectral ThermalSpectral.Space
variable {n : ℕ}

end EntropyPhotonNumber

namespace BKM

section
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem entry_id [DecidableEq J] (b : HilbertBasis J ℂ E) (i j : J) :
    entry b (ContinuousLinearMap.id ℂ E) i j = if i=j then 1 else 0 := by
  exact orthonormal_iff_ite.mp b.orthonormal i j

theorem mean_id (b : HilbertBasis J ℂ E) (p : J → ℝ) (hs : HasSum p 1) :
    mean b p (ContinuousLinearMap.id ℂ E)=1 := by
  classical
  simp only [mean, entry_id, ite_true, mul_one]
  exact (hs.mapL Complex.ofRealCLM).tsum_eq

end

section
open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem mean_neg (b : HilbertBasis J ℂ E) (p : J → ℝ) (Z : E →L[ℂ] E) :
    mean b p (-Z) = -mean b p Z := by
  simpa only [neg_one_smul, neg_one_mul] using mean_smul b p (-1) Z

theorem mean_sub (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p)
    (Z T : E →L[ℂ] E) : mean b p (Z-T)=mean b p Z-mean b p T := by
  rw [sub_eq_add_neg, mean_add b p hp hs, mean_neg, sub_eq_add_neg]

theorem mean_center (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : HasSum p 1)
    (Z : E →L[ℂ] E) : mean b p (center b p Z)=0 := by
  rw [center, mean_sub b p hp hs.summable, mean_smul, mean_id b p hs, mul_one, sub_self]

end

open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem mean_rankOne [DecidableEq J] (b : HilbertBasis J ℂ E) (p : J → ℝ) (i j : J) :
    mean b p (InnerProductSpace.rankOne ℂ (b i) (b j))=if i=j then (p i:ℂ) else 0 := by
  classical
  rw [mean, tsum_eq_single i]
  · simp only [entry, InnerProductSpace.rankOne_apply, inner_smul_right,
      orthonormal_iff_ite.mp b.orthonormal, ite_true, mul_one]
    split_ifs <;> simp_all
  · intro k hk
    simp only [entry, InnerProductSpace.rankOne_apply, inner_smul_right,
      orthonormal_iff_ite.mp b.orthonormal, ite_eq_right hk, mul_zero]

end BKM

namespace CenteredTests
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem generator_eq_center (b : HilbertBasis J ℂ E) (p : J → ℝ) (ij : J × J) :
    generator b p ij=BKM.center b p (InnerProductSpace.rankOne ℂ (b ij.1) (b ij.2)) := by
  classical
  rw [BKM.center, BKM.mean_rankOne]
  rfl

theorem mean_eq_zero (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : HasSum p 1)
    {Z : E →L[ℂ] E} (hZ : Z ∈ operatorSpace b p) : BKM.mean b p Z=0 := by
  obtain ⟨c,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hZ
  have hc : (c.sum fun ij a => a • generator b p ij)=
      BKM.centerLM b p hp hs.summable (c.sum fun ij a => a • InnerProductSpace.rankOne ℂ (b ij.1) (b ij.2)) := by
    simp only [Finsupp.sum, map_sum, map_smul, BKM.centerLM_apply, ← generator_eq_center]
  rw [hc, BKM.centerLM_apply]
  exact BKM.mean_center b p hp hs _

end CenteredTests

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace EntropyPhotonNumber
open TensorLp KrausBounded ThermalSpectral ThermalSpectral.Space
variable {n : ℕ}

end EntropyPhotonNumber

namespace BKM
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
end BKM

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end ThermalSpectral

namespace EntropyPhotonNumber
open TensorLp KrausBounded ThermalSpectral ThermalSpectral.Space ThermalMetric
variable {n : ℕ}

end EntropyPhotonNumber

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

end EntropyPhotonNumber.SpectralLogData

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Duality ----
namespace OAI

noncomputable section

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation BeamLadder TensorLp ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
end EntropyPhotonNumber.SpectralLogData

section
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace TensorLp
open EntropyPhotonNumber
variable {A B I J : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp KrausBounded BeamLadder Annihilation
variable {n : ℕ}

namespace WeightedColumns
variable {ρ σ τ : State n}

end WeightedColumns
end EntropyPhotonNumber

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem scalar_comparison (S : Space E) (q : (E →L[ℂ] E) →ₗ[ℂ] ℂ)
    (w : Param → ℝ)
    (hh : ∀ Z, Z ∈ CenteredTests.operatorSpace S.basis S.p →
      Complex.normSq (q Z) ≤ S.pquad w Z) :
    (scalarDiagram S q).Comparison (scalarWeight w) := by
  intro z s
  let Z := CenteredTests.realize S.basis S.p S.base S.base_pos z
  have hz : S.coords Z=z.val := CenteredTests.realize_entries S.basis S.p S.base S.base_pos z
  have hm : Z ∈ CenteredTests.operatorSpace S.basis S.p :=
    CenteredTests.realize_mem S.basis S.p S.base S.base_pos z
  have hh' := hh Z hm
  have ht : (∑ _u ∈ s, Complex.normSq (q Z)) ≤ Complex.normSq (q Z) := by
    have hh := (hasSum_fintype (fun _u : Unit => Complex.normSq (q Z))).summable.sum_le_tsum
      s (fun _ _ => Complex.normSq_nonneg _)
    simpa using hh
  change (∑ _u ∈ s, 1*Complex.normSq (q Z)) ≤ _
  simp only [one_mul]
  convert! ht.trans hh' using 1
  simp only [sourceForm, scalarDiagram, CenteredTests.system, scalarWeight, Space.pquad, hz]

theorem scalar_logMean_bound (S : Space E) (q : (E →L[ℂ] E) →ₗ[ℂ] ℂ)
    (v w : Param → ℝ) (hv : ∀ p, 0 < v p) (hw : ∀ p, 0 < w p)
    (hV : ∀ Z, Z ∈ CenteredTests.operatorSpace S.basis S.p →
      Complex.normSq (q Z) ≤ S.pquad v Z)
    (hW : ∀ Z, Z ∈ CenteredTests.operatorSpace S.basis S.p →
      Complex.normSq (q Z) ≤ S.pquad w Z)
    (Z : E →L[ℂ] E) (hZ : Z ∈ CenteredTests.operatorSpace S.basis S.p) :
    Complex.normSq (q Z) ≤ S.pquad (fun p => logMean (v p) (w p)) Z := by
  let D := scalarDiagram S q
  have hv' : ∀ p, 0 < scalarWeight v p := by intro p; cases p <;> simp [scalarWeight,hv]
  have hw' : ∀ p, 0 < scalarWeight w p := by intro p; cases p <;> simp [scalarWeight,hw]
  have hi := D.comparison_logMean (scalar_comparison S q v hV) (scalar_comparison S q w hW) hv' hw'
  let z : D.tests := ⟨S.coords Z, ⟨Z,hZ,rfl⟩⟩
  have hz : CenteredTests.realize S.basis S.p S.base S.base_pos z=Z := by
    apply CenteredTests.entryMap_injective S.basis S.base S.base_pos
    exact CenteredTests.realize_entries S.basis S.p S.base S.base_pos z
  have hh := hi z Finset.univ
  change (∑ _u : Unit, logMean 1 1*Complex.normSq (q
    (CenteredTests.realize S.basis S.p S.base S.base_pos z))) ≤ _ at hh
  rw [hz] at hh
  simpa only [logMean_self, one_mul, Finset.univ_unique, Finset.sum_singleton,
    sourceForm, D, scalarDiagram, CenteredTests.system, scalarWeight, Space.pquad, z]
    using hh

theorem scalar_arithmetic_BKM (S : Space E) (q : (E →L[ℂ] E) →ₗ[ℂ] ℂ)
    (hV : ∀ Z, Z ∈ CenteredTests.operatorSpace S.basis S.p →
      Complex.normSq (q Z) ≤ S.pquad plusWeight Z)
    (hW : ∀ Z, Z ∈ CenteredTests.operatorSpace S.basis S.p →
      Complex.normSq (q Z) ≤ S.pquad minusWeight Z)
    (Z : E →L[ℂ] E) (hZ : Z ∈ CenteredTests.operatorSpace S.basis S.p) :
    Complex.normSq (q Z) ≤ S.pquad (fun _ => 1/h S.r) Z := by
  have hh := scalar_logMean_bound S q plusWeight minusWeight plusWeight_pos minusWeight_pos hV hW Z hZ
  convert! hh using 1
  apply tsum_congr
  intro a
  congr 1
  exact (EntropyPhotonNumber.logarithmicMean_exp_pair (one_div_pos.mpr (h_pos S.rpos))
    (h S.r*(S.param a).2/2)).symm

end ThermalSpectral

end

open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology Complex MeasureTheory

namespace EnsembleL2
open scoped BigOperators ComplexConjugate
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem mixtureFunctional_apply (v : I → E) (w : J → E)
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    (t : ℝ) (Z : E →L[ℂ] E) :
    mixtureFunctional v w hv hw t Z = (Real.sqrt (t*(1-t)) : ℂ)*(mean v Z-mean w Z) := rfl

omit [CompleteSpace E] in
theorem mixtureFunctional_square (v : I → E) (w : J → E)
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) (Z : E →L[ℂ] E) :
    Complex.normSq (mixtureFunctional v w hv hw t Z)=t*(1-t)*‖mean v Z-mean w Z‖^2 := by
  rw [mixtureFunctional_apply, Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)), Complex.normSq_eq_norm_sq]

theorem mixtureFunctional_adjoint_square (v : I → E) (w : J → E)
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) (Z : E →L[ℂ] E) :
    Complex.normSq (mixtureFunctional v w hv hw t Z.adjoint)=
      Complex.normSq (mixtureFunctional v w hv hw t Z) := by
  simp only [mixtureFunctional_square v w hv hw ht, mean_adjoint, ← map_sub,
    Complex.norm_conj]
end EnsembleL2

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem mixture_arithmetic_bounds (S : Space E) (v : I → E) (w : J → E)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1)
    (he : TraceEnsemble.operator S.ensemble=TraceEnsemble.operator (EnsembleL2.mixture v w t))
    (Z : E →L[ℂ] E) (hZ : Z ∈ CenteredTests.operatorSpace S.basis S.p) :
    Complex.normSq (EnsembleL2.mixtureFunctional v w hv.summable hw.summable t Z) ≤ S.pquad plusWeight Z ∧
    Complex.normSq (EnsembleL2.mixtureFunctional v w hv.summable hw.summable t Z) ≤ S.pquad minusWeight Z := by
  let u := EnsembleL2.mixture v w t
  have hu : HasSum (fun a => ‖u a‖^2) 1 := EnsembleL2.mixture_hasSum v w ht hv hw
  have hz : EnsembleL2.mean u Z=0 := by
    rw [← EnsembleL2.mean_eq_of_operator_eq S.basis S.ensemble_hasSum.summable hu.summable he Z,
      S.ensemble_mean]
    exact CenteredTests.mean_eq_zero S.basis S.p (fun j => (S.pos j).le) S.sum hZ
  have hza : EnsembleL2.mean u Z.adjoint=0 := by rw [EnsembleL2.mean_adjoint, hz, map_zero]
  have hc : EnsembleL2.center u Z=Z := by simp only [EnsembleL2.center,hz,zero_smul,sub_zero]
  have hca : EnsembleL2.center u Z.adjoint=Z.adjoint := by simp only [EnsembleL2.center,hza,zero_smul,sub_zero]
  have hm := EnsembleL2.mixture_between_variance v w ht hv hw Z
  have hp := EnsembleL2.mixture_between_variance v w ht hv hw Z.adjoint
  change _ ≤ EnsembleL2.secondMoment u (EnsembleL2.center u Z) at hm
  change _ ≤ EnsembleL2.secondMoment u (EnsembleL2.center u Z.adjoint) at hp
  rw [hc] at hm
  rw [hca] at hp
  rw [← EnsembleL2.mixtureFunctional_square v w hv.summable hw.summable ht Z] at hm
  rw [← EnsembleL2.mixtureFunctional_square v w hv.summable hw.summable ht Z.adjoint,
    EnsembleL2.mixtureFunctional_adjoint_square v w hv.summable hw.summable ht Z] at hp
  constructor
  · change _ ≤ S.quad Space.plus Z
    rw [S.plus_quad_of_ensemble u hu.summable he Z]
    exact hp
  · change _ ≤ S.quad Space.minus Z
    rw [S.minus_quad_of_ensemble u hu.summable he Z]
    exact hm

theorem mixture_BKM_bound (S : Space E) (v : I → E) (w : J → E)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1)
    (he : TraceEnsemble.operator S.ensemble=TraceEnsemble.operator (EnsembleL2.mixture v w t))
    (Z : E →L[ℂ] E) (hZ : Z ∈ CenteredTests.operatorSpace S.basis S.p) :
    Complex.normSq (EnsembleL2.mixtureFunctional v w hv.summable hw.summable t Z) ≤
      S.pquad (fun _ => 1/h S.r) Z :=
  scalar_arithmetic_BKM S _ (fun Y hY => (mixture_arithmetic_bounds S v w ht hv hw he Y hY).1)
    (fun Y hY => (mixture_arithmetic_bounds S v w ht hv hw he Y hY).2) Z hZ
end ThermalSpectral

namespace ThermalDual

variable {I J : Type*} [Fintype I] [Fintype J]

theorem weighted_sum_bound (w a b : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∑ i, w i*a i*b i ≤ Real.sqrt (∑ i, w i*a i^2)*Real.sqrt (∑ i, w i*b i^2) := by
  have hh := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => Real.sqrt (w i)*a i) (fun i => Real.sqrt (w i)*b i)
  have he (i : I) : Real.sqrt (w i)*a i*(Real.sqrt (w i)*b i)=w i*a i*b i := by
    linear_combination a i*b i*(Real.sq_sqrt (hw i))
  simpa only [he, mul_pow, Real.sq_sqrt (hw _)] using hh

theorem weighted_functionals_bound (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (E : I → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    (q : (i : I) → E i →L[ℂ] ℂ) (z : (i : I) → E i) :
    ‖∑ i, (w i:ℂ)*q i (z i)‖ ≤
      Real.sqrt (∑ i, w i*‖q i‖^2)*Real.sqrt (∑ i, w i*‖z i‖^2) := by
  calc
    _ ≤ ∑ i, ‖(w i:ℂ)*q i (z i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i*‖q i‖*‖z i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw i), mul_assoc]
      exact mul_le_mul_of_nonneg_left ((q i).le_opNorm (z i)) (hw i)
    _ ≤ _ := weighted_sum_bound w (fun i => ‖q i‖) (fun i => ‖z i‖) hw

end ThermalDual

namespace ThermalSpectral
open EntropyPhotonNumber ThermalMetric
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem mixture_thermal_bound (S : Space E) (v : I → E) (w : J → E)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1)
    (he : TraceEnsemble.operator S.ensemble=TraceEnsemble.operator (EnsembleL2.mixture v w t))
    (Z : E →L[ℂ] E) (hZ : Z ∈ CenteredTests.operatorSpace S.basis S.p) :
    ‖EnsembleL2.mixtureFunctional v w hv.summable hw.summable t Z‖ ≤
      mixtureConstant S.r*‖S.observable Z‖ := by
  have hh := (mixture_BKM_bound S v w ht hv hw he Z hZ).trans (S.BKM_thermal_bound Z)
  rw [Complex.normSq_eq_norm_sq] at hh
  have hm := mul_nonneg (mixtureConstant_pos S.rpos).le (norm_nonneg (S.observable Z))
  nlinarith [norm_nonneg (EnsembleL2.mixtureFunctional v w hv.summable hw.summable t Z)]
end ThermalSpectral

namespace ThermalDual

section
open EntropyPhotonNumber ThermalMetric ThermalSpectral
open scoped BigOperators
variable {E I J K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Fintype K]

theorem dual_bound_from_core (S₀ : Space E) (S : K → Space E)
    (w : K → ℝ) (hw : ∀ i, 0 ≤ w i)
    (L : (i : K) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E))
    (q₀ : lp (fun _ : S₀.I × S₀.I => ℂ) 2 →L[ℂ] ℂ)
    (q : (i : K) → lp (fun _ : (S i).I × (S i).I => ℂ) 2 →L[ℂ] ℂ)
    (v : I → E) (u : J → E) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hu : HasSum (fun j => ‖u j‖^2) 1)
    (he : TraceEnsemble.operator S₀.ensemble=TraceEnsemble.operator (EnsembleL2.mixture v u t))
    (c : ℂ)
    (hL : ∀ Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      ∑ i, w i*(S i).pquad thermalWeight (L i Z) ≤ S₀.pquad thermalWeight Z)
    (hq : ∀ Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      q₀ (S₀.observable Z) = (∑ i, (w i:ℂ)*q i ((S i).observable (L i Z)))+
        c*EnsembleL2.mixtureFunctional v u hv.summable hu.summable t Z) :
    ‖q₀.comp (centeredSpace S₀.r S₀.rpos S₀.p S₀.pos S₀.sum.summable).subtypeL‖ ≤
      Real.sqrt (∑ i, w i*‖q i‖^2)+‖c‖*mixtureConstant S₀.r := by
  apply restricted_norm_bound_of_core S₀.basis S₀.p S₀.pos S₀.sum S₀.r S₀.rpos q₀ _
    (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (norm_nonneg _) (mixtureConstant_pos S₀.rpos).le))
  intro Z hZ
  change ‖q₀ (S₀.observable Z)‖ ≤ _*‖S₀.observable Z‖
  rw [hq Z hZ]
  have hh := weighted_functionals_bound w hw
    (fun i => lp (fun _ : (S i).I × (S i).I => ℂ) 2) q (fun i => (S i).observable (L i Z))
  have hc : ∑ i, w i*‖(S i).observable (L i Z)‖^2 ≤ ‖S₀.observable Z‖^2 := by
    simpa only [Space.observable_norm_sq] using hL Z hZ
  have hs : Real.sqrt (∑ i, w i*‖(S i).observable (L i Z)‖^2) ≤ ‖S₀.observable Z‖ := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using Real.sqrt_le_sqrt hc
  have hj := mixture_thermal_bound S₀ v u ht hv hu he Z hZ
  calc
    _ ≤ ‖∑ i, (w i:ℂ)*q i ((S i).observable (L i Z))‖+
        ‖c*EnsembleL2.mixtureFunctional v u hv.summable hu.summable t Z‖ := norm_add_le _ _
    _ ≤ Real.sqrt (∑ i, w i*‖q i‖^2)*‖S₀.observable Z‖+
        ‖c‖*(mixtureConstant S₀.r*‖S₀.observable Z‖) :=
      add_le_add (hh.trans (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)))
        (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left hj (norm_nonneg _))
    _ = _ := by ring
end

section
variable {I J : Type*} [Fintype I] [Fintype J]

end

open scoped ComplexConjugate

end ThermalDual

end

end OAI

-- ---- platform node ----
open OAI OAI.ThermalDual
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology Complex MeasureTheory
open EntropyPhotonNumber ThermalMetric ThermalSpectral
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.ThermalDual.dual_bound_from_core := @_root_.OAI.ThermalDual.dual_bound_from_core
