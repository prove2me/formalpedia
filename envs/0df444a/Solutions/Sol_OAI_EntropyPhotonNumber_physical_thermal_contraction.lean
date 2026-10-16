-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.physical_thermal_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:43:55.178035+00:00
-- url     : https://prove2.me/submissions/0a2a827d-3495-4f67-a251-d3b19210334a

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Contraction.lean:L854-L889
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.physical_thermal_contraction. The node keeps its source
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
import Theorems.Thm_OAI_CrossEnsemble_operator_comp_left
import Theorems.Thm_OAI_EnsembleL2_mixture_operator
import Theorems.Thm_OAI_EnsembleL2_secondMoment_eq_of_operator_eq
import Theorems.Thm_OAI_EntropyPhotonNumber_four_weight_interpolation
import Theorems.Thm_OAI_ThermalSpectral_diagram_comparison

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

theorem inner_tensor (x z : H A) (y w : H B) :
    inner ℂ (tensor x y) (tensor z w) = inner ℂ x z * inner ℂ y w := by
  have ha : Summable (fun a => ‖inner ℂ (x a) (z a)‖) := (lp.summable_inner (𝕜 := ℂ) x z).norm
  have hb : Summable (fun b => ‖inner ℂ (y b) (w b)‖) := (lp.summable_inner (𝕜 := ℂ) y w).norm
  apply (lp.hasSum_inner (𝕜 := ℂ) (tensor x y) (tensor z w)).unique
  convert! (lp.hasSum_inner (𝕜 := ℂ) x z).mul (lp.hasSum_inner (𝕜 := ℂ) y w)
    (summable_mul_of_summable_norm
      (f := fun a => inner ℂ (x a) (z a)) (g := fun b => inner ℂ (y b) (w b)) ha hb) using 1
  ext ab
  change inner ℂ (x ab.1*y ab.2) (z ab.1*w ab.2) = _
  simp only [RCLike.inner_apply, map_mul]
  ring

end TensorLp

namespace TensorLp
variable {A B : Type*}

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

omit [CompleteSpace E] [CompleteSpace H] in
 theorem analysis_norm (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2)) :
    ‖analysis V hV‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  exact wave_bound V (fun y => (hV y).summable) (by norm_num : (0:ℝ) ≤ 1) (by intro y; simp [(hV y).tsum_eq]) x

end

variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

 theorem dual_adjoint (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Z : H →L[ℂ] H) : dual V hV Z.adjoint = (dual V hV Z).adjoint := by
  ext y
  apply ext_inner_left ℂ
  intro x
  have hh := (dual_entry V hV Z y x).mapL Complex.conjCLE.toContinuousLinearEquiv.toContinuousLinearMap
  change HasSum (fun i => starRingEnd ℂ (inner ℂ (V i y) (Z (V i x))))
    (starRingEnd ℂ (inner ℂ y (dual V hV Z x))) at hh
  exact (dual_entry V hV Z.adjoint x y).unique (by
    simpa only [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm] using hh)

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

-- ---- from OAI.InformationTheory.PhotonNumber.Continuity ----
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

namespace EntropyPhotonNumber
open TensorLp
end EntropyPhotonNumber

namespace BlockUnitary
variable {J : Type*} [Fintype J]

variable {S : Type*} {I : S → Type*} [∀ s, Fintype (I s)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end BlockUnitary

namespace TensorLp
variable {A B I : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp FischerBeam

end EntropyPhotonNumber

namespace TensorLp
variable {A B : Type*}

end TensorLp

namespace EntropyPhotonNumber
open TensorLp

end EntropyPhotonNumber

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber
open TensorLp
end EntropyPhotonNumber

namespace EnsembleL2
open scoped BigOperators ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

omit [InnerProductSpace ℂ E] in
theorem norm_sum (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) :
    HasSum (fun i => ‖v i‖^2) (‖vector v hv‖^2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, vector_apply] using
    lp.hasSum_norm (p := 2) (by norm_num) (vector v hv)

theorem projection_bound (x a b : E) (hab : inner ℂ a b = 0)
    (hax : inner ℂ a x = inner ℂ a a) (hbx : inner ℂ b x = inner ℂ b b) :
    ‖a‖^2+‖b‖^2 ≤ ‖x‖^2 := by
  have hba : inner ℂ b a = 0 := by rw [← inner_conj_symm b a, hab, map_zero]
  have hxa : inner ℂ x a = inner ℂ a a := by
    rw [← inner_conj_symm x a, hax, inner_self_conj]
  have hxb : inner ℂ x b = inner ℂ b b := by
    rw [← inner_conj_symm x b, hbx, inner_self_conj]
  have hh : 0 ≤ (inner ℂ (x-a-b) (x-a-b)).re := inner_self_nonneg (𝕜 := ℂ) (x := x-a-b)
  simp only [inner_sub_left, inner_sub_right, hax, hbx, hxa, hxb, hab, hba] at hh
  simp only [Complex.sub_re, Complex.zero_re] at hh
  have hn (v : E) : (inner ℂ v v).re = ‖v‖^2 := by
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
  simp only [hn] at hh
  nlinarith

theorem projection_sums (x a b : I → E) (u v w : ℝ)
    (hx : HasSum (fun i => ‖x i‖^2) w) (ha : HasSum (fun i => ‖a i‖^2) u)
    (hb : HasSum (fun i => ‖b i‖^2) v)
    (hab : HasSum (fun i => inner ℂ (a i) (b i)) 0)
    (hax : HasSum (fun i => inner ℂ (a i) (x i)) (u : ℂ))
    (hbx : HasSum (fun i => inner ℂ (b i) (x i)) (v : ℂ)) : u+v ≤ w := by
  have hna := (norm_sum a ha.summable).unique ha
  have hnb := (norm_sum b hb.summable).unique hb
  have hnx := (norm_sum x hx.summable).unique hx
  have hh := projection_bound (vector x hx.summable) (vector a ha.summable) (vector b hb.summable)
    ((inner_sum a b ha.summable hb.summable).unique hab)
    (by rw [(inner_sum a x ha.summable hx.summable).unique hax, inner_self_eq_norm_sq_to_K]
        change (u:ℂ)=(‖vector a ha.summable‖:ℂ)^2
        rw [← Complex.ofReal_pow, hna])
    (by rw [(inner_sum b x hb.summable hx.summable).unique hbx, inner_self_eq_norm_sq_to_K]
        change (v:ℂ)=(‖vector b hb.summable‖:ℂ)^2
        rw [← Complex.ofReal_pow, hnb])
  rwa [hna, hnb, hnx] at hh

theorem fubini_inner (a z : I × J → E) (u : I → ℂ) (t : ℂ)
    (ha : Summable (fun ij => ‖a ij‖^2)) (hz : Summable (fun ij => ‖z ij‖^2))
    (hrow : ∀ i, HasSum (fun j => inner ℂ (a (i,j)) (z (i,j))) (u i))
    (hu : HasSum u t) : HasSum (fun ij => inner ℂ (a ij) (z ij)) t := by
  have hh := inner_sum a z ha hz
  exact (hh.prod_fiberwise hrow).unique hu ▸ hh

theorem fubini_inner_second (a z : I × J → E) (u : J → ℂ) (t : ℂ)
    (ha : Summable (fun ij => ‖a ij‖^2)) (hz : Summable (fun ij => ‖z ij‖^2))
    (hrow : ∀ j, HasSum (fun i => inner ℂ (a (i,j)) (z (i,j))) (u j))
    (hu : HasSum u t) : HasSum (fun ij => inner ℂ (a ij) (z ij)) t := by
  have hh := fubini_inner (fun ji : J × I => a (ji.2,ji.1))
    (fun ji : J × I => z (ji.2,ji.1)) u t
    ha.prod_symm hz.prod_symm hrow hu
  exact (Equiv.prodComm J I).hasSum_iff (f := fun ij => inner ℂ (a ij) (z ij)) |>.mp hh

theorem self_inner_hasSum (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) :
    HasSum (fun i => inner ℂ (v i) (v i)) (((∑' i, ‖v i‖^2):ℝ):ℂ) := by
  have hh := hv.hasSum.mapL Complex.ofRealCLM
  have he (i : I) : inner ℂ (v i) (v i) = (((‖v i‖^2):ℝ):ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    change (‖v i‖:ℂ)^2=(((‖v i‖^2):ℝ):ℂ)
    rw [Complex.ofReal_pow]
  simpa only [he, Complex.ofRealCLM_apply] using hh

end EnsembleL2

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J : Type*}
theorem conditional_left_overlap (x : I → H A) (y : J → H B)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) (S : H A →L[ℂ] H A)
    (hentry : ∀ u v, HasSum (fun j => inner ℂ (tensor u (y j)) (Z (tensor v (y j)))) (inner ℂ u (S v))) :
    HasSum (fun ij : I × J => inner ℂ (tensor (S (x ij.1)) (y ij.2))
      (Z (tensor (x ij.1) (y ij.2)))) (((∑' i, ‖S (x i)‖^2) : ℝ):ℂ) := by
  exact EnsembleL2.fubini_inner
    (fun ij : I × J => tensor (S (x ij.1)) (y ij.2))
    (fun ij : I × J => Z (tensor (x ij.1) (y ij.2)))
    (fun i => inner ℂ (S (x i)) (S (x i))) _
    (tensorFamily_summable (fun i => S (x i)) y (EnsembleL2.image_summable x hx S) hy.summable)
    (EnsembleL2.image_summable (fun ij : I × J => tensor (x ij.1) (y ij.2))
      (tensorFamily_summable x y hx hy.summable) Z)
    (fun i => hentry (S (x i)) (x i))
    (EnsembleL2.self_inner_hasSum (fun i => S (x i)) (EnsembleL2.image_summable x hx S))

theorem conditional_right_overlap (x : I → H A) (y : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1) (hy : Summable (fun j => ‖y j‖^2))
    (Z : H (A × B) →L[ℂ] H (A × B)) (T : H B →L[ℂ] H B)
    (hentry : ∀ u v, HasSum (fun i => inner ℂ (tensor (x i) u) (Z (tensor (x i) v))) (inner ℂ u (T v))) :
    HasSum (fun ij : I × J => inner ℂ (tensor (x ij.1) (T (y ij.2)))
      (Z (tensor (x ij.1) (y ij.2)))) (((∑' j, ‖T (y j)‖^2) : ℝ):ℂ) := by
  exact EnsembleL2.fubini_inner_second
    (fun ij : I × J => tensor (x ij.1) (T (y ij.2)))
    (fun ij : I × J => Z (tensor (x ij.1) (y ij.2)))
    (fun j => inner ℂ (T (y j)) (T (y j))) _
    (tensorFamily_summable x (fun j => T (y j)) hx.summable (EnsembleL2.image_summable y hy T))
    (EnsembleL2.image_summable (fun ij : I × J => tensor (x ij.1) (y ij.2))
      (tensorFamily_summable x y hx.summable hy) Z)
    (fun j => hentry (T (y j)) (y j))
    (EnsembleL2.self_inner_hasSum (fun j => T (y j)) (EnsembleL2.image_summable y hy T))

 theorem tensorFamily_norm (x : I → H A) (y : J → H B) (α β : ℝ)
    (hx : HasSum (fun i => ‖x i‖^2) α) (hy : HasSum (fun j => ‖y j‖^2) β) :
    HasSum (fun ij : I × J => ‖tensor (x ij.1) (y ij.2)‖^2) (α*β) := by
  have hs := hx.summable.mul_of_nonneg hy.summable (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  simpa only [tensor_norm_sq] using hx.mul hy hs

 theorem tensorFamily_orthogonal (x x' : I → H A) (y y' : J → H B)
    (hx : Summable (fun i => ‖x i‖^2)) (hx' : Summable (fun i => ‖x' i‖^2))
    (hy : Summable (fun j => ‖y j‖^2)) (hy' : Summable (fun j => ‖y' j‖^2))
    (hleft : HasSum (fun i => inner ℂ (x i) (x' i)) 0)
    (hright : HasSum (fun j => inner ℂ (y j) (y' j)) 0) :
    HasSum (fun ij : I × J => inner ℂ (tensor (x ij.1) (y ij.2)) (tensor (x' ij.1) (y' ij.2))) 0 := by
  have hs := (EnsembleL2.inner_sum
    (fun ij : I × J => tensor (x ij.1) (y ij.2))
    (fun ij : I × J => tensor (x' ij.1) (y' ij.2))
    (tensorFamily_summable x y hx hy) (tensorFamily_summable x' y' hx' hy')).summable
  simp only [inner_tensor] at hs
  simpa only [inner_tensor, zero_mul] using hleft.mul hright hs

theorem arithmetic_projection (x : I → H A) (y : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B))
    (S : H A →L[ℂ] H A) (T : H B →L[ℂ] H B)
    (hSentry : ∀ u v, HasSum (fun j => inner ℂ (tensor u (y j)) (Z (tensor v (y j)))) (inner ℂ u (S v)))
    (hTentry : ∀ u v, HasSum (fun i => inner ℂ (tensor (x i) u) (Z (tensor (x i) v))) (inner ℂ u (T v)))
    (hleft : HasSum (fun i => inner ℂ (x i) (S (x i))) 0)
    (hright : HasSum (fun j => inner ℂ (y j) (T (y j))) 0) :
    (∑' i, ‖S (x i)‖^2)+(∑' j, ‖T (y j)‖^2) ≤
      ∑' ij : I × J, ‖Z (tensor (x ij.1) (y ij.2))‖^2 := by
  have hS := EnsembleL2.image_summable x hx.summable S
  have hT := EnsembleL2.image_summable y hy.summable T
  let z := fun ij : I × J => Z (tensor (x ij.1) (y ij.2))
  let a := fun ij : I × J => tensor (S (x ij.1)) (y ij.2)
  let b := fun ij : I × J => tensor (x ij.1) (T (y ij.2))
  have hz : Summable (fun ij => ‖z ij‖^2) :=
    EnsembleL2.image_summable (fun ij : I × J => tensor (x ij.1) (y ij.2)) (tensorFamily_summable x y hx.summable hy.summable) Z
  have ha : HasSum (fun ij => ‖a ij‖^2) (∑' i, ‖S (x i)‖^2) := by
    exact mul_one (∑' i, ‖S (x i)‖^2) ▸ tensorFamily_norm (fun i => S (x i)) y _ 1 hS.hasSum hy
  have hb : HasSum (fun ij => ‖b ij‖^2) (∑' j, ‖T (y j)‖^2) := by
    exact one_mul (∑' j, ‖T (y j)‖^2) ▸ tensorFamily_norm x (fun j => T (y j)) 1 _ hx hT.hasSum
  have hcl : HasSum (fun i => inner ℂ (S (x i)) (x i)) 0 := by
    have hh := hleft.mapL Complex.conjCLE.toContinuousLinearMap
    change HasSum (fun i => conj (inner ℂ (x i) (S (x i)))) (conj 0) at hh
    simpa only [map_zero, inner_conj_symm] using hh
  have hab : HasSum (fun ij => inner ℂ (a ij) (b ij)) 0 :=
    tensorFamily_orthogonal (fun i => S (x i)) x y (fun j => T (y j)) hS hx.summable hy.summable hT hcl hright
  exact EnsembleL2.projection_sums z a b _ _ _ hz.hasSum ha hb hab
    (conditional_left_overlap x y hx.summable hy Z S hSentry) (conditional_right_overlap x y hx hy.summable Z T hTentry)
end TensorLp

namespace KrausBounded
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

theorem dual_point_square (V : I → E →L[ℂ] H)
    (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (Z : H →L[ℂ] H) (x : E) :
    ‖dual V hV Z x‖^2 ≤ ∑' i, ‖Z (V i x)‖^2 := by
  have hn : ‖(analysis V hV).adjoint‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact analysis_norm V hV
  have ht : ‖dual V hV Z x‖ ≤ ‖acted V hV Z x‖ := by
    exact ((analysis V hV).adjoint.le_opNorm (acted V hV Z x)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hn (norm_nonneg (acted V hV Z x)))
  have hs : HasSum (fun i => ‖Z (V i x)‖^2) (‖acted V hV Z x‖^2) := by
    convert! lp.hasSum_norm (p:=2) (by norm_num) (acted V hV Z x) using 1 <;> simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rfl
  rw [hs.tsum_eq]
  exact pow_le_pow_left₀ (norm_nonneg _) ht 2
end KrausBounded

namespace EnsembleL2
open scoped BigOperators ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
omit [CompleteSpace E] in
theorem center_mean (v : I → E) (hv : HasSum (fun i => ‖v i‖^2) 1) (Z : E →L[ℂ] E) :
    HasSum (fun i => inner ℂ (v i) (center v Z (v i))) 0 := by
  have hi : HasSum (fun i => inner ℂ (v i) (v i)) (1:ℂ) := by
    simpa only [hv.tsum_eq, Complex.ofReal_one] using self_inner_hasSum v hv.summable
  have hh := (mean_hasSum v hv.summable Z).sub (hi.mul_left (mean v Z))
  simpa only [center, sub_apply, smul_apply, inner_sub_right, inner_smul_right,
    ContinuousLinearMap.id_apply, mul_one, sub_self] using hh
end EnsembleL2

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J : Type*}

theorem conditionalLeft_mean (x : I → H A) (y : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) :
    HasSum (fun i => inner ℂ (x i) (conditionalLeft y hy Z (x i)))
      (EnsembleL2.mean (fun ij : I × J => tensor (x ij.1) (y ij.2)) Z) := by
  have hh := EnsembleL2.mean_hasSum (fun ij : I × J => tensor (x ij.1) (y ij.2))
    (tensorFamily_summable x y hx.summable hy.summable) Z
  exact hh.prod_fiberwise (fun i => conditionalLeft_entry y hy Z (x i) (x i))

theorem conditionalRight_mean (x : I → H A) (y : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) :
    HasSum (fun j => inner ℂ (y j) (conditionalRight x hx Z (y j)))
      (EnsembleL2.mean (fun ij : I × J => tensor (x ij.1) (y ij.2)) Z) := by
  have hh := EnsembleL2.mean_hasSum (fun ij : I × J => tensor (x ij.1) (y ij.2))
    (tensorFamily_summable x y hx.summable hy.summable) Z
  exact ((Equiv.prodComm J I).hasSum_iff.mpr hh).prod_fiberwise
    (fun j => conditionalRight_entry x hx Z (y j) (y j))

theorem centered_arithmetic_projection (x : I → H A) (y : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) :
    let T := EnsembleL2.center (fun ij : I × J => tensor (x ij.1) (y ij.2)) Z
    (∑' i, ‖conditionalLeft y hy T (x i)‖^2)+(∑' j, ‖conditionalRight x hx T (y j)‖^2) ≤
      ∑' ij : I × J, ‖T (tensor (x ij.1) (y ij.2))‖^2 := by
  dsimp only
  let T := EnsembleL2.center (fun ij : I × J => tensor (x ij.1) (y ij.2)) Z
  have hv : HasSum (fun ij : I × J => ‖tensor (x ij.1) (y ij.2)‖^2) 1 := by
    simpa only [one_mul] using tensorFamily_norm x y 1 1 hx hy
  have hm := EnsembleL2.center_mean (fun ij : I × J => tensor (x ij.1) (y ij.2)) hv Z
  have hz : EnsembleL2.mean (fun ij : I × J => tensor (x ij.1) (y ij.2)) T=0 := hm.tsum_eq
  apply arithmetic_projection x y hx hy T (conditionalLeft y hy T) (conditionalRight x hx T)
    (conditionalLeft_entry y hy T) (conditionalRight_entry x hx T)
  · exact hz ▸ conditionalLeft_mean x y hx hy T
  · exact hz ▸ conditionalRight_mean x y hx hy T
end TensorLp

namespace KrausBounded

section
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

theorem dual_id (V : I → E →L[ℂ] H) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2)) :
    dual V hV (ContinuousLinearMap.id ℂ H)=ContinuousLinearMap.id ℂ E := by
  have he : acted V hV (ContinuousLinearMap.id ℂ H)=analysis V hV := by
    ext x i
    rfl
  rw [dual, he]
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp
  intro x
  have hh : ‖analysis V hV x‖^2=‖x‖^2 := (wave_square V (fun y => (hV y).summable) x).trans (hV x).tsum_eq
  nlinarith [norm_nonneg (analysis V hV x), norm_nonneg x]
end

open scoped BigOperators ComplexConjugate
variable {E H K I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

theorem dual_output_mean (V : K → E →L[ℂ] H)
    (hV : ∀ x, HasSum (fun k => ‖V k x‖^2) (‖x‖^2))
    (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) (Z : H →L[ℂ] H) :
    EnsembleL2.mean v (dual V hV Z)=EnsembleL2.mean (fun ik : I × K => V ik.2 (v ik.1)) Z := by
  have hw := family_hasSum V hV v _ hv.hasSum
  have hh := EnsembleL2.mean_hasSum (fun ik : I × K => V ik.2 (v ik.1)) hw.summable Z
  exact (EnsembleL2.mean_hasSum v hv (dual V hV Z)).unique
    (hh.prod_fiberwise (fun i => dual_entry V hV Z (v i) (v i)))

theorem dual_center (V : K → E →L[ℂ] H)
    (hV : ∀ x, HasSum (fun k => ‖V k x‖^2) (‖x‖^2))
    (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) (Z : H →L[ℂ] H) :
    EnsembleL2.center v (dual V hV Z)=
      dual V hV (EnsembleL2.center (fun ik : I × K => V ik.2 (v ik.1)) Z) := by
  unfold EnsembleL2.center
  rw [dual_output_mean V hV v hv Z]
  simp only [sub_eq_add_neg, ← neg_smul, dual_add, dual_smul, dual_id]

theorem dual_variance (V : K → E →L[ℂ] H)
    (hV : ∀ x, HasSum (fun k => ‖V k x‖^2) (‖x‖^2))
    (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) (Z : H →L[ℂ] H) :
    (∑' i, ‖EnsembleL2.center v (dual V hV Z) (v i)‖^2) ≤
      ∑' ik : I × K, ‖EnsembleL2.center (fun ik : I × K => V ik.2 (v ik.1)) Z (V ik.2 (v ik.1))‖^2 := by
  let T := EnsembleL2.center (fun ik : I × K => V ik.2 (v ik.1)) Z
  have hw := family_hasSum V hV v _ hv.hasSum
  have hs := EnsembleL2.image_summable (fun ik : I × K => V ik.2 (v ik.1)) hw.summable T
  rw [dual_center V hV v hv Z, hs.tsum_prod]
  exact Summable.tsum_le_tsum (fun i => dual_point_square V hV T (v i))
    (EnsembleL2.image_summable v hv (dual V hV T)) hs.prod
end KrausBounded

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J K E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem channel_arithmetic_projection (x : I → H A) (y : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (V : K → H (A × B) →L[ℂ] E)
    (hV : ∀ z, HasSum (fun k => ‖V k z‖^2) (‖z‖^2))
    (Z : E →L[ℂ] E) :
    let v := fun ij : I × J => tensor (x ij.1) (y ij.2)
    let T := EnsembleL2.center v (KrausBounded.dual V hV Z)
    (∑' i, ‖conditionalLeft y hy T (x i)‖^2)+(∑' j, ‖conditionalRight x hx T (y j)‖^2) ≤
      ∑' ik : (I × J) × K, ‖EnsembleL2.center (fun ik : (I × J) × K => V ik.2 (v ik.1)) Z (V ik.2 (v ik.1))‖^2 := by
  exact (centered_arithmetic_projection x y hx hy (KrausBounded.dual V hV Z)).trans
    (KrausBounded.dual_variance V hV (fun ij : I × J => tensor (x ij.1) (y ij.2))
      (tensorFamily_summable x y hx.summable hy.summable) Z)
end TensorLp

namespace KrausBounded
open scoped BigOperators ComplexConjugate
variable {E H F I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace E] [CompleteSpace H] [CompleteSpace F]

end KrausBounded

namespace EntropyPhotonNumber
open TensorLp KrausBounded
open scoped BigOperators ComplexConjugate

theorem physical_arithmetic_projection {n : ℕ} (η θ : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (ρ σ τ : State n)
    (Z : Fock n →L[ℂ] Fock n) :
    let x := rootColumn ρ
    let y := rootColumn σ
    let v := fun ij : NumberIndex n × NumberIndex n => tensor (x ij.1) (y ij.2)
    let T := EnsembleL2.center v (rawDual η θ hη hθ τ Z)
    let out := fun ik : (NumberIndex n × NumberIndex n) × (NumberIndex n × (NumberIndex n × NumberIndex n)) =>
      rawJointKraus η θ hη hθ τ ik.2 (v ik.1)
    (∑' i, ‖conditionalLeft y (rootColumn_norm σ) T (x i)‖^2)+
      (∑' j, ‖conditionalRight x (rootColumn_norm ρ) T (y j)‖^2) ≤
      ∑' ik, ‖EnsembleL2.center out Z (out ik)‖^2 :=
  channel_arithmetic_projection (rootColumn ρ) (rootColumn σ) (rootColumn_norm ρ)
    (rootColumn_norm σ) (rawJointKraus η θ hη hθ τ) (rawJointKraus_norm η θ hη hθ τ) Z

end EntropyPhotonNumber

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

variable [DecidableEq J]

end

open scoped ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

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

end CenteredTests

namespace ThermalMetric
open EntropyPhotonNumber DiagonalForms.System

theorem reference_plus {r : ℝ} (hr : 0<r) :
    (1/h r)*f (-h r/2)*Real.exp (-h r/2)=r := by
  have hh := logMean_arithmetic_plus hr (show 0<r+1 by linarith)
  rw [logMean_reference hr] at hh
  have he : -h r/2=(Real.log r-Real.log (r+1))/2 := by unfold h; ring
  simpa only [he] using hh

theorem reference_minus {r : ℝ} (hr : 0<r) :
    (1/h r)*f (-h r/2)*Real.exp (-(-h r/2))=r+1 := by
  have hh := logMean_arithmetic_minus hr (show 0<r+1 by linarith)
  rw [logMean_reference hr] at hh
  have he : -h r/2=(Real.log r-Real.log (r+1))/2 := by unfold h; ring
  simpa only [he] using hh
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

theorem plus_summable (Z : E →L[ℂ] E) : Summable (fun ij => plus (S.param ij)*Complex.normSq (S.coords Z ij)) := by
  simpa only [S.plus_entry Z] using BKM.weighted_row_summable S.basis S.p (fun i => (S.pos i).le) S.sum.summable Z

theorem minus_summable (Z : E →L[ℂ] E) : Summable (fun ij => minus (S.param ij)*Complex.normSq (S.coords Z ij)) := by
  simpa only [S.minus_entry Z] using BKM.weighted_column_summable S.basis S.p (fun i => (S.pos i).le) S.sum.summable Z

theorem constant_summable (c : ℝ) (Z : E →L[ℂ] E) :
    Summable (fun ij => c*Complex.normSq (S.coords Z ij)) := by
  have hh := ((BKM.logMean_summable S.basis S.p S.pos S.sum.summable Z).mul_left (h S.r)).mul_left c
  simpa only [S.coords_norm, base, mul_assoc] using hh
end Space

theorem targetMap_norm (S : Fin 2 → Space E) (w : Fin 2 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (L : (i : Fin 2) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E))
    (Z : E →L[ℂ] E) (a : Σ i, (S i).I × (S i).I) :
    Complex.normSq (targetMap S w L Z a)=w a.1*Complex.normSq ((S a.1).coords (L a.1 Z) a.2) := by
  simp only [targetMap, LinearMap.coe_mk, AddHom.coe_mk, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (hw _)]

theorem plusWeight_pos (q : Param) : 0 < plusWeight q :=
  mul_pos (mul_pos (one_div_pos.mpr (h_pos q.1.property)) (f_pos _)) (Real.exp_pos _)
theorem minusWeight_pos (q : Param) : 0 < minusWeight q :=
  mul_pos (mul_pos (one_div_pos.mpr (h_pos q.1.property)) (f_pos _)) (Real.exp_pos _)

theorem diagram_thermal (S₀ : Space E) (S : Fin 2 → Space E) (w : Fin 2 → ℝ)
    (L : (i : Fin 2) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E))
    (hp : (diagram S₀ S w L).Comparison plusWeight)
    (hm : (diagram S₀ S w L).Comparison minusWeight)
    (hr : (diagram S₀ S w L).Comparison (fun q => q.1.val))
    (hs : (diagram S₀ S w L).Comparison (fun q => q.1.val+1)) :
    (diagram S₀ S w L).Comparison thermalWeight := by
  have h₁ : (fun q : Param => (1/h q.1.val)*f (-h q.1.val/2)*Real.exp (-h q.1.val/2)) =
      (fun q => q.1.val) := funext (fun q => reference_plus q.1.property)
  have h₂ : (fun q : Param => (1/h q.1.val)*f (-h q.1.val/2)*Real.exp (-(-h q.1.val/2))) =
      (fun q => q.1.val+1) := funext (fun q => reference_minus q.1.property)
  have hh := four_weight_interpolation (diagram S₀ S w L)
    (fun q => 1/h q.1.val) (fun q => h q.1.val*q.2/2) (fun q => -h q.1.val/2)
    (fun q => one_div_pos.mpr (h_pos q.1.property)) hp hm (by rwa [h₁]) (by rwa [h₂])
  exact hh
end ThermalSpectral

namespace ThermalMetric
open EntropyPhotonNumber DiagonalForms.System

end ThermalMetric

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

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

theorem mixture_variance_left (v : I → E) (w : J → E) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1) (Z : E →L[ℂ] E) :
    t*secondMoment v (center v Z) ≤ secondMoment (mixture v w t) (center (mixture v w t) Z) := by
  rw [mixture_variance v w ht hv hw Z]
  have h₁ : 0 ≤ (1-t)*secondMoment w (center w Z) :=
    mul_nonneg (sub_nonneg.mpr ht.2) (tsum_nonneg (fun _ => sq_nonneg _))
  have h₂ := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) (sq_nonneg ‖mean v Z-mean w Z‖)
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

theorem center_eq_of_operator_eq (b : HilbertBasis K ℂ E) {v : I → E} {w : J → E}
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    (he : TraceEnsemble.operator v=TraceEnsemble.operator w) (Z : E →L[ℂ] E) :
    center v Z=center w Z := by
  simp only [center, mean_eq_of_operator_eq b hv hw he Z]

end EnsembleL2

namespace BKM
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
end BKM

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

theorem ensemble_operator (T : E →L[ℂ] E) (hT : T.IsSymmetric)
    (he : ∀ j, T (S.basis j)=(S.p j : ℂ) • S.basis j) :
    TraceEnsemble.operator S.ensemble=T :=
  CrossEnsemble.eigenEnsemble_operator S.basis S.p (fun j => (S.pos j).le) S.sum.summable T hT he

theorem ensemble_mean (Z : E →L[ℂ] E) : EnsembleL2.mean S.ensemble Z=BKM.mean S.basis S.p Z := by
  unfold EnsembleL2.mean BKM.mean
  apply tsum_congr
  intro j
  simp only [ensemble, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (S.pos j).le]
  rfl

theorem ensemble_center (Z : E →L[ℂ] E) : EnsembleL2.center S.ensemble Z=BKM.center S.basis S.p Z := by
  simp only [EnsembleL2.center, S.ensemble_mean, BKM.center]

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

theorem conditionalLeft_center (x : I → H A) (y : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) :
    conditionalLeft y hy (EnsembleL2.center (fun ij : I × J => tensor (x ij.1) (y ij.2)) Z)=
      EnsembleL2.center x (conditionalLeft y hy Z) := by
  have hh : EnsembleL2.mean x (conditionalLeft y hy Z)=
      EnsembleL2.mean (fun ij : I × J => tensor (x ij.1) (y ij.2)) Z :=
    (conditionalLeft_mean x y hx hy Z).tsum_eq
  simp only [EnsembleL2.center]
  rw [hh]
  simp only [conditionalLeft, sub_eq_add_neg, ← neg_smul, dual_add, dual_smul, dual_id]

theorem conditionalRight_center (x : I → H A) (y : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) :
    conditionalRight x hx (EnsembleL2.center (fun ij : I × J => tensor (x ij.1) (y ij.2)) Z)=
      EnsembleL2.center y (conditionalRight x hx Z) := by
  have hh : EnsembleL2.mean y (conditionalRight x hx Z)=
      EnsembleL2.mean (fun ij : I × J => tensor (x ij.1) (y ij.2)) Z :=
    (conditionalRight_mean x y hx hy Z).tsum_eq
  simp only [EnsembleL2.center]
  rw [hh]
  simp only [conditionalRight, sub_eq_add_neg, ← neg_smul, dual_add, dual_smul, dual_id]
end TensorLp

namespace EntropyPhotonNumber
open TensorLp KrausBounded
open scoped BigOperators ComplexConjugate

theorem rawEnsemble_norm {n : ℕ} (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ σ τ : State n) : HasSum (fun i => ‖rawEnsemble η θ hη hθ ρ σ τ i‖^2) 1 := by
  let v : NumberIndex n × NumberIndex n → H (NumberIndex n × NumberIndex n) :=
    fun ij => tensor (rootColumn ρ ij.1) (rootColumn σ ij.2)
  have hv : HasSum (fun ij => ‖v ij‖^2) 1 := by
    simpa only [one_mul] using tensorFamily_norm (rootColumn ρ) (rootColumn σ) 1 1
      (rootColumn_norm ρ) (rootColumn_norm σ)
  have hh := family_hasSum (rawJointKraus η θ hη hθ τ) (rawJointKraus_norm η θ hη hθ τ) v 1 hv
  exact hh

theorem rawEnsemble_operator {n : ℕ} (η θ : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (ρ σ τ : State n) :
    TraceEnsemble.operator (rawEnsemble η θ hη hθ ρ σ τ)=
      (beamOutput θ hθ (beamOutput η hη ρ σ) τ).op := by
  let v : NumberIndex n × (NumberIndex n × NumberIndex n) → Fock n := fun i =>
    slice (beamUnitary η hη (tensor (rootColumn ρ i.2.1) (rootColumn σ i.2.2))) i.1
  have hv : HasSum (fun i => ‖v i‖^2) 1 := by
    change HasSum (fun bi : NumberIndex n × (NumberIndex n × NumberIndex n) =>
      ‖slice (mixedVector η hη ρ σ bi.2) bi.1‖^2) 1
    exact hasSum_slice_family (v := mixedVector η hη ρ σ) (mixedVector_norm η hη ρ σ)
  have he : TraceEnsemble.operator v=(beamOutput η hη ρ σ).op := rfl
  have hr := TraceEnsemble.operator_reindex (rawEnsembleEquiv n)
    (fun i => firstKraus θ hθ τ i.1 (v i.2))
  exact hr.trans (firstKraus_ensemble θ hθ (beamOutput η hη ρ σ) τ v hv he)

theorem raw_centered_arithmetic {n : ℕ} (η θ : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (ρ σ τ : State n)
    (Z : Fock n →L[ℂ] Fock n) :
    EnsembleL2.secondMoment (rootColumn ρ)
      (EnsembleL2.center (rootColumn ρ)
        (conditionalLeft (rootColumn σ) (rootColumn_norm σ) (rawDual η θ hη hθ τ Z)))+
    EnsembleL2.secondMoment (rootColumn σ)
      (EnsembleL2.center (rootColumn σ)
        (conditionalRight (rootColumn ρ) (rootColumn_norm ρ) (rawDual η θ hη hθ τ Z))) ≤
      EnsembleL2.secondMoment (rawEnsemble η θ hη hθ ρ σ τ)
        (EnsembleL2.center (rawEnsemble η θ hη hθ ρ σ τ) Z) := by
  have hh := physical_arithmetic_projection η θ hη hθ ρ σ τ Z
  dsimp only at hh
  rw [conditionalLeft_center _ _ (rootColumn_norm ρ) (rootColumn_norm σ),
    conditionalRight_center _ _ (rootColumn_norm ρ) (rootColumn_norm σ)] at hh
  exact hh
end EntropyPhotonNumber

namespace EnsembleL2
open scoped ComplexConjugate
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem mean_adjoint (v : I → E) (Z : E →L[ℂ] E) : mean v Z.adjoint=conj (mean v Z) := by
  simp only [mean, ContinuousLinearMap.adjoint_inner_right, inner_conj_symm, Complex.conj_tsum]

theorem center_adjoint (v : I → E) (Z : E →L[ℂ] E) : center v Z.adjoint=(center v Z).adjoint := by
  simp only [center, mean_adjoint, map_sub, map_smulₛₗ,
    ContinuousLinearMap.adjoint_id]
end EnsembleL2

namespace EntropyPhotonNumber
open TensorLp KrausBounded
open scoped BigOperators ComplexConjugate
variable {n : ℕ}

theorem rawFirstSlice_adjoint (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (σ τ : State n) (Z : Fock n →L[ℂ] Fock n) :
    rawFirstSlice η θ hη hθ σ τ Z.adjoint=(rawFirstSlice η θ hη hθ σ τ Z).adjoint := by
  simp only [rawFirstSlice, conditionalLeft, rawDual, dual_adjoint]

theorem rawSecondSlice_adjoint (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ τ : State n) (Z : Fock n →L[ℂ] Fock n) :
    rawSecondSlice η θ hη hθ ρ τ Z.adjoint=(rawSecondSlice η θ hη hθ ρ τ Z).adjoint := by
  simp only [rawSecondSlice, conditionalRight, rawDual, dual_adjoint]

theorem replaced_arithmetic {J : Type*} (η θ κ : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (v : J → Fock n) (hv : HasSum (fun j => ‖v j‖^2) 1)
    (Z : Fock n →L[ℂ] Fock n) :
    let m := EnsembleL2.mixture (rawEnsemble η θ hη hθ ρ σ τ) v (1-κ)
    (1-κ)*(EnsembleL2.secondMoment (rootColumn ρ)
      (EnsembleL2.center (rootColumn ρ) (rawFirstSlice η θ hη hθ σ τ Z))+
      EnsembleL2.secondMoment (rootColumn σ)
      (EnsembleL2.center (rootColumn σ) (rawSecondSlice η θ hη hθ ρ τ Z))) ≤
      EnsembleL2.secondMoment m (EnsembleL2.center m Z) ∧
    (1-κ)*(EnsembleL2.secondMoment (rootColumn ρ)
      (EnsembleL2.center (rootColumn ρ) (rawFirstSlice η θ hη hθ σ τ Z)).adjoint+
      EnsembleL2.secondMoment (rootColumn σ)
      (EnsembleL2.center (rootColumn σ) (rawSecondSlice η θ hη hθ ρ τ Z)).adjoint) ≤
      EnsembleL2.secondMoment m (EnsembleL2.center m Z).adjoint := by
  dsimp only
  have hk : 1-κ ∈ Set.Icc (0:ℝ) 1 := ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
  have hh (T : Fock n →L[ℂ] Fock n) :=
    (mul_le_mul_of_nonneg_left (raw_centered_arithmetic η θ hη hθ ρ σ τ T) hk.1).trans
      (EnsembleL2.mixture_variance_left (rawEnsemble η θ hη hθ ρ σ τ) v hk
        (rawEnsemble_norm η θ hη hθ ρ σ τ) hv T)
  refine ⟨hh Z, ?_⟩
  have ha := hh Z.adjoint
  change (1-κ)*(EnsembleL2.secondMoment (rootColumn ρ)
      (EnsembleL2.center (rootColumn ρ) (rawFirstSlice η θ hη hθ σ τ Z.adjoint))+
    EnsembleL2.secondMoment (rootColumn σ)
      (EnsembleL2.center (rootColumn σ) (rawSecondSlice η θ hη hθ ρ τ Z.adjoint))) ≤ _ at ha
  simpa only [rawFirstSlice_adjoint, rawSecondSlice_adjoint, EnsembleL2.center_adjoint] using ha
end EntropyPhotonNumber

namespace EnsembleL2
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end EnsembleL2

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

theorem minus_center_of_ensemble (v : I → E) (hv : Summable (fun i => ‖v i‖^2))
    (he : TraceEnsemble.operator S.ensemble=TraceEnsemble.operator v) (Z : E →L[ℂ] E) :
    S.quad minus (BKM.center S.basis S.p Z)=EnsembleL2.secondMoment v (EnsembleL2.center v Z) := by
  rw [S.minus_quad_of_ensemble v hv he, ← S.ensemble_center,
    EnsembleL2.center_eq_of_operator_eq S.basis S.ensemble_hasSum.summable hv he]

theorem plus_center_of_ensemble (v : I → E) (hv : Summable (fun i => ‖v i‖^2))
    (he : TraceEnsemble.operator S.ensemble=TraceEnsemble.operator v) (Z : E →L[ℂ] E) :
    S.quad plus (BKM.center S.basis S.p Z)=EnsembleL2.secondMoment v (EnsembleL2.center v Z).adjoint := by
  rw [S.plus_quad_of_ensemble v hv he, ← S.ensemble_center,
    EnsembleL2.center_eq_of_operator_eq S.basis S.ensemble_hasSum.summable hv he]
end ThermalSpectral.Space

namespace EntropyPhotonNumber
open ThermalSpectral ThermalSpectral.Space
variable {n : ℕ}

theorem replaced_spectral_arithmetic (η θ κ : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1)
    (ρ σ τ ω : State n) (S₀ S₁ S₂ : Space (Fock n))
    (he₁ : ∀ j, ρ.op (S₁.basis j)=(S₁.p j:ℂ) • S₁.basis j)
    (he₂ : ∀ j, σ.op (S₂.basis j)=(S₂.p j:ℂ) • S₂.basis j)
    (he₀ : TraceEnsemble.operator S₀.ensemble=
      ((1-κ:ℝ):ℂ) • (beamOutput θ hθ (beamOutput η hη ρ σ) τ).op+(κ:ℂ) • ω.op)
    (Z : Fock n →L[ℂ] Fock n) :
    (1-κ)*(S₁.quad minus (BKM.center S₁.basis S₁.p (rawFirstSlice η θ hη hθ σ τ Z))+
      S₂.quad minus (BKM.center S₂.basis S₂.p (rawSecondSlice η θ hη hθ ρ τ Z))) ≤
      S₀.quad minus (BKM.center S₀.basis S₀.p Z) ∧
    (1-κ)*(S₁.quad plus (BKM.center S₁.basis S₁.p (rawFirstSlice η θ hη hθ σ τ Z))+
      S₂.quad plus (BKM.center S₂.basis S₂.p (rawSecondSlice η θ hη hθ ρ τ Z))) ≤
      S₀.quad plus (BKM.center S₀.basis S₀.p Z) := by
  have hr : TraceEnsemble.operator S₁.ensemble=TraceEnsemble.operator (rootColumn ρ) :=
    (S₁.ensemble_operator ρ.op ρ.positive.isSymmetric he₁).trans (rootColumn_operator ρ).symm
  have hs : TraceEnsemble.operator S₂.ensemble=TraceEnsemble.operator (rootColumn σ) :=
    (S₂.ensemble_operator σ.op σ.positive.isSymmetric he₂).trans (rootColumn_operator σ).symm
  let v := EnsembleL2.mixture (rawEnsemble η θ hη hθ ρ σ τ) (rootColumn ω) (1-κ)
  have hk : 1-κ ∈ Set.Icc (0:ℝ) 1 := ⟨sub_nonneg.mpr hκ.2,sub_le_self _ hκ.1⟩
  have hv := EnsembleL2.mixture_hasSum (rawEnsemble η θ hη hθ ρ σ τ) (rootColumn ω) hk
    (rawEnsemble_norm η θ hη hθ ρ σ τ) (rootColumn_norm ω)
  have he : TraceEnsemble.operator S₀.ensemble=TraceEnsemble.operator v := by
    dsimp only [v]
    rw [he₀, EnsembleL2.mixture_operator _ _ hk (rawEnsemble_norm η θ hη hθ ρ σ τ).summable
      (rootColumn_norm ω).summable, rawEnsemble_operator, rootColumn_operator, sub_sub_cancel]
  rw [S₁.minus_center_of_ensemble _ (rootColumn_norm ρ).summable hr,
    S₂.minus_center_of_ensemble _ (rootColumn_norm σ).summable hs,
    S₀.minus_center_of_ensemble v hv.summable he,
    S₁.plus_center_of_ensemble _ (rootColumn_norm ρ).summable hr,
    S₂.plus_center_of_ensemble _ (rootColumn_norm σ).summable hs,
    S₀.plus_center_of_ensemble v hv.summable he]
  exact replaced_arithmetic η θ κ hη hθ hκ ρ σ τ (rootColumn ω) (rootColumn_norm ω) Z
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

theorem quad_smul (X : ℝ × ℝ → ℝ) (c : ℂ) (Z : E →L[ℂ] E) :
    S.quad X (c • Z)=Complex.normSq c*S.quad X Z := by
  simp only [quad, map_smul, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
    mul_left_comm (X _) (Complex.normSq c), tsum_mul_left]

theorem pquad_smul (X : ThermalSpectral.Param → ℝ) (c : ℂ) (Z : E →L[ℂ] E) :
    S.pquad X (c • Z)=Complex.normSq c*S.pquad X Z := by
  simp only [pquad, map_smul, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
    mul_left_comm (X _) (Complex.normSq c), tsum_mul_left]

theorem pquad_nonneg {X : ThermalSpectral.Param → ℝ} (hX : ∀ q, 0 ≤ X q)
    (Z : E →L[ℂ] E) : 0 ≤ S.pquad X Z :=
  tsum_nonneg (fun _ij => mul_nonneg (hX _) (Complex.normSq_nonneg _))

theorem center_of_mem {Z : E →L[ℂ] E} (hZ : Z ∈ CenteredTests.operatorSpace S.basis S.p) :
    BKM.center S.basis S.p Z=Z := by
  simp only [BKM.center, CenteredTests.mean_eq_zero S.basis S.p (fun j => (S.pos j).le) S.sum hZ,
    zero_smul, sub_zero]

theorem normalize_quad {lam : ℝ} (hlam : 0 < lam) (X : ℝ × ℝ → ℝ) (Z : E →L[ℂ] E) :
    lam*S.quad X (S.normalize lam Z)=S.quad X (BKM.center S.basis S.p Z) := by
  change lam*S.quad X ((Real.sqrt lam:ℂ)⁻¹ • BKM.center S.basis S.p Z)=_
  rw [S.quad_smul, Complex.normSq_inv, Complex.normSq_ofReal,
    Real.mul_self_sqrt hlam.le, ← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul]
theorem normalize_pquad {lam : ℝ} (hlam : 0 < lam) (X : ThermalSpectral.Param → ℝ) (Z : E →L[ℂ] E) :
    lam*S.pquad X (S.normalize lam Z)=S.pquad X (BKM.center S.basis S.p Z) := by
  change lam*S.pquad X ((Real.sqrt lam:ℂ)⁻¹ • BKM.center S.basis S.p Z)=_
  rw [S.pquad_smul, Complex.normSq_inv, Complex.normSq_ofReal,
    Real.mul_self_sqrt hlam.le, ← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul]
end ThermalSpectral.Space

namespace EntropyPhotonNumber
open TensorLp KrausBounded ThermalSpectral ThermalSpectral.Space
variable {n : ℕ}

theorem physical_diagram_arithmetic (η θ κ : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1)
    (ρ σ τ ω : State n) (S₀ : Space (Fock n)) (S : Fin 2 → Space (Fock n))
    (lam : Fin 2 → ℝ) (hlam : ∀ i, 0 < lam i)
    (he₁ : ∀ j, ρ.op ((S 0).basis j)=((S 0).p j:ℂ) • (S 0).basis j)
    (he₂ : ∀ j, σ.op ((S 1).basis j)=((S 1).p j:ℂ) • (S 1).basis j)
    (he₀ : TraceEnsemble.operator S₀.ensemble=
      ((1-κ:ℝ):ℂ) • (beamOutput θ hθ (beamOutput η hη ρ σ) τ).op+(κ:ℂ) • ω.op) :
    let D := diagram S₀ S (fun i => (1-κ)*lam i) (normalizedSlices η θ hη hθ ρ σ τ S lam)
    D.Comparison minusWeight ∧ D.Comparison plusWeight := by
  dsimp only
  have hw (i : Fin 2) : 0 ≤ (1-κ)*lam i := mul_nonneg (sub_nonneg.mpr hκ.2) (hlam i).le
  have hmain (X : Param → ℝ) (X' : ℝ × ℝ → ℝ) (heX : X=X' ∘ raw)
      (hX : ∀ q, 0 ≤ X q)
      (hs : ∀ i Z, Summable (fun ij => X ((S i).pparam ij)*Complex.normSq ((S i).coords Z ij)))
      (hp : ∀ Z, (1-κ)*((S 0).quad X' (BKM.center (S 0).basis (S 0).p (rawFirstSlice η θ hη hθ σ τ Z))+
        (S 1).quad X' (BKM.center (S 1).basis (S 1).p (rawSecondSlice η θ hη hθ ρ τ Z))) ≤
          S₀.quad X' (BKM.center S₀.basis S₀.p Z)) :
      (diagram S₀ S (fun i => (1-κ)*lam i) (normalizedSlices η θ hη hθ ρ σ τ S lam)).Comparison X := by
    apply diagram_comparison S₀ S _ hw _ X hX hs
    intro Z hZ
    have hh := hp Z
    rw [S₀.center_of_mem hZ] at hh
    simp only [Fin.sum_univ_two, heX, Space.pquad, Function.comp_apply]
    change (1-κ)*lam 0*(S 0).quad X' ((S 0).normalize (lam 0) (rawFirstSlice η θ hη hθ σ τ Z))+
      (1-κ)*lam 1*(S 1).quad X' ((S 1).normalize (lam 1) (rawSecondSlice η θ hη hθ ρ τ Z)) ≤ S₀.quad X' Z
    rw [mul_assoc, mul_assoc, (S 0).normalize_quad (hlam 0), (S 1).normalize_quad (hlam 1), ← mul_add]
    exact hh
  have hh := replaced_spectral_arithmetic η θ κ hη hθ hκ ρ σ τ ω S₀ (S 0) (S 1) he₁ he₂ he₀
  exact ⟨hmain minusWeight minus rfl (fun q => (minusWeight_pos q).le)
      (fun i Z => (S i).minus_summable Z) (fun Z => (hh Z).1),
    hmain plusWeight plus rfl (fun q => (plusWeight_pos q).le)
      (fun i Z => (S i).plus_summable Z) (fun Z => (hh Z).2)⟩
end EntropyPhotonNumber

namespace BKM
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
end BKM

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

theorem pquad_one (Z : E →L[ℂ] E) :
    S.pquad (fun _ => 1) Z=h S.r*BKM.quadratic S.basis S.p Z := by
  simp only [pquad, one_mul, S.coords_norm, base, BKM.quadratic, mul_assoc, tsum_mul_left]

theorem normalized_hessian (S₀ : ThermalSpectral.Space E) {lam κ ε : ℝ}
    (hlam : 0 < lam) (hκ : κ < 1) (T Z : E →L[ℂ] E)
    (hh : (1-κ)^2*BKM.quadratic S.basis S.p (BKM.center S.basis S.p T) ≤
      (1+ε)*(1-κ)*lam*(h S₀.r/h S.r)*BKM.quadratic S₀.basis S₀.p Z) :
    (1-κ)*S.pquad (fun _ => 1) (S.normalize lam T) ≤ (1+ε)*S₀.pquad (fun _ => 1) Z := by
  have hn : lam*S.pquad (fun _ => 1) (S.normalize lam T)=S.pquad (fun _ => 1) (BKM.center S.basis S.p T) :=
    S.normalize_pquad hlam (fun _ => 1) T
  apply (mul_le_mul_iff_right₀ (mul_pos (sub_pos.mpr hκ) hlam)).mp
  calc
    _ = (1-κ)^2*(lam*S.pquad (fun _ => 1) (S.normalize lam T)) := by ring
    _ = h S.r*((1-κ)^2*BKM.quadratic S.basis S.p (BKM.center S.basis S.p T)) := by
      rw [hn, S.pquad_one]; ring
    _ ≤ h S.r*((1+ε)*(1-κ)*lam*(h S₀.r/h S.r)*BKM.quadratic S₀.basis S₀.p Z) :=
      mul_le_mul_of_nonneg_left hh (h_pos S.rpos).le
    _ = _ := by rw [S₀.pquad_one]; field_simp [(h_pos S.rpos).ne']
end ThermalSpectral.Space

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem diagram_constant (S₀ : Space E) (S : Fin 2 → Space E) (lam : Fin 2 → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (κ ε : ℝ) (hκ : κ ≤ 1)
    (L : (i : Fin 2) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E))
    (hh : ∀ i Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      (1-κ)*(S i).pquad (fun _ => 1) (L i Z) ≤ (1+ε)*S₀.pquad (fun _ => 1) Z)
    (X : Param → ℝ) (hX : ∀ q, 0 ≤ X q) (c₀ : ℝ) (c : Fin 2 → ℝ) (hc : ∀ i, 0 ≤ c i)
    (he₀ : ∀ a, X (S₀.pparam a)=c₀) (he : ∀ i a, X ((S i).pparam a)=c i)
    (hslack : (1+ε)*(∑ i, lam i*c i) ≤ c₀) :
    (diagram S₀ S (fun i => (1-κ)*lam i) L).Comparison X := by
  have hw i : 0 ≤ (1-κ)*lam i := mul_nonneg (sub_nonneg.mpr hκ) (hlam i)
  have hq₀ Z : S₀.pquad X Z=c₀*S₀.pquad (fun _ => 1) Z := by
    simp only [Space.pquad, he₀, one_mul, tsum_mul_left]
  have hq i Z : (S i).pquad X Z=c i*(S i).pquad (fun _ => 1) Z := by
    simp only [Space.pquad, he, one_mul, tsum_mul_left]
  apply diagram_comparison S₀ S _ hw L X hX
  · intro i Z
    simpa only [he] using (S i).constant_summable (c i) Z
  intro Z hZ
  rw [hq₀]
  calc
    _ = ∑ i, (lam i*c i)*((1-κ)*(S i).pquad (fun _ => 1) (L i Z)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hq]; ring
    _ ≤ ∑ i, (lam i*c i)*((1+ε)*S₀.pquad (fun _ => 1) Z) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hh i Z hZ) (mul_nonneg (hlam i) (hc i))
    _ = ((1+ε)*∑ i, lam i*c i)*S₀.pquad (fun _ => 1) Z := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hslack (S₀.pquad_nonneg (fun _ => zero_le_one) Z)

theorem diagram_reference (S₀ : Space E) (S : Fin 2 → Space E) (lam : Fin 2 → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (κ ε : ℝ) (hκ : κ ≤ 1)
    (L : (i : Fin 2) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E))
    (hh : ∀ i Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      (1-κ)*(S i).pquad (fun _ => 1) (L i Z) ≤ (1+ε)*S₀.pquad (fun _ => 1) Z)
    (hr : (1+ε)*(∑ i, lam i*(S i).r) ≤ S₀.r)
    (hs : (1+ε)*(∑ i, lam i*((S i).r+1)) ≤ S₀.r+1) :
    (diagram S₀ S (fun i => (1-κ)*lam i) L).Comparison (fun q => q.1.val) ∧
    (diagram S₀ S (fun i => (1-κ)*lam i) L).Comparison (fun q => q.1.val+1) := by
  constructor
  · exact diagram_constant S₀ S lam hlam κ ε hκ L hh (fun q => q.1.val) (fun q => q.1.property.le)
      S₀.r (fun i => (S i).r) (fun i => (S i).rpos.le) (fun _ => rfl) (fun _ _ => rfl) hr
  · exact diagram_constant S₀ S lam hlam κ ε hκ L hh (fun q => q.1.val+1) (fun q => by linarith [q.1.property])
      (S₀.r+1) (fun i => (S i).r+1) (fun i => by linarith [(S i).rpos])
      (fun _ => rfl) (fun _ _ => rfl) hs

theorem diagram_observable (S₀ : Space E) (S : Fin 2 → Space E) (w : Fin 2 → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (L : (i : Fin 2) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E)) (X : Param → ℝ)
    (hX : ∀ q, 0 ≤ X q)
    (hs : ∀ i Z, Summable (fun a => X ((S i).pparam a)*Complex.normSq ((S i).coords Z a)))
    (hh : (diagram S₀ S w L).Comparison X) (Z : E →L[ℂ] E)
    (hZ : Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p) :
    ∑ i, w i*(S i).pquad X (L i Z) ≤ S₀.pquad X Z := by
  let z : CenteredTests.coordinates S₀.basis S₀.p S₀.base := ⟨S₀.coords Z, ⟨Z,hZ,rfl⟩⟩
  have hz : CenteredTests.realize S₀.basis S₀.p S₀.base S₀.base_pos z=Z := by
    apply CenteredTests.entryMap_injective S₀.basis S₀.base S₀.base_pos
    exact CenteredTests.realize_entries S₀.basis S₀.p S₀.base S₀.base_pos z
  have hn (a : Σ i, (S i).I × (S i).I) : 0 ≤ X ((S a.1).pparam a.2)*
      (w a.1*Complex.normSq ((S a.1).coords (L a.1 Z) a.2)) :=
    mul_nonneg (hX _) (mul_nonneg (hw _) (Complex.normSq_nonneg _))
  have ht : Summable (fun a : Σ i, (S i).I × (S i).I => X ((S a.1).pparam a.2)*
      (w a.1*Complex.normSq ((S a.1).coords (L a.1 Z) a.2))) := by
    apply (summable_sigma_of_nonneg hn).mpr
    refine ⟨fun i => ?_, (hasSum_fintype _).summable⟩
    simpa only [mul_left_comm] using (hs i (L i Z)).mul_left (w i)
  have hsum : (∑' a : Σ i, (S i).I × (S i).I, X ((S a.1).pparam a.2)*
      (w a.1*Complex.normSq ((S a.1).coords (L a.1 Z) a.2))) =
      ∑ i, w i*(S i).pquad X (L i Z) := by
    rw [ht.tsum_sigma]
    simp only [tsum_fintype, Space.pquad, mul_left_comm (X _) (w _), tsum_mul_left]
  rw [← hsum]
  apply ht.tsum_le_of_sum_le
  intro s
  have hh' := hh z s
  change (∑ a ∈ s, X ((S a.1).pparam a.2)*Complex.normSq
    (targetMap S w L (CenteredTests.realize S₀.basis S₀.p S₀.base S₀.base_pos z) a)) ≤
      S₀.pquad X Z at hh'
  simpa only [hz, targetMap_norm S w hw L] using hh'
end ThermalSpectral

namespace EntropyPhotonNumber
open TensorLp KrausBounded ThermalSpectral ThermalSpectral.Space ThermalMetric
variable {n : ℕ}

theorem physical_thermal_contraction (η θ κ ε : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1) (hκ1 : κ < 1)
    (ρ σ τ ω : State n) (S₀ : Space (Fock n)) (S : Fin 2 → Space (Fock n))
    (lam : Fin 2 → ℝ) (hlam : ∀ i, 0 < lam i)
    (he₁ : ∀ j, ρ.op ((S 0).basis j)=((S 0).p j:ℂ) • (S 0).basis j)
    (he₂ : ∀ j, σ.op ((S 1).basis j)=((S 1).p j:ℂ) • (S 1).basis j)
    (he₀ : TraceEnsemble.operator S₀.ensemble=
      ((1-κ:ℝ):ℂ) • (beamOutput θ hθ (beamOutput η hη ρ σ) τ).op+(κ:ℂ) • ω.op)
    (hh₁ : ∀ Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      (1-κ)^2*BKM.quadratic (S 0).basis (S 0).p
        (BKM.center (S 0).basis (S 0).p (rawFirstSlice η θ hη hθ σ τ Z)) ≤
      (1+ε)*(1-κ)*lam 0*(h S₀.r/h (S 0).r)*BKM.quadratic S₀.basis S₀.p Z)
    (hh₂ : ∀ Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      (1-κ)^2*BKM.quadratic (S 1).basis (S 1).p
        (BKM.center (S 1).basis (S 1).p (rawSecondSlice η θ hη hθ ρ τ Z)) ≤
      (1+ε)*(1-κ)*lam 1*(h S₀.r/h (S 1).r)*BKM.quadratic S₀.basis S₀.p Z)
    (hr : (1+ε)*(∑ i, lam i*(S i).r) ≤ S₀.r)
    (hs : (1+ε)*(∑ i, lam i*((S i).r+1)) ≤ S₀.r+1)
    (Z : Fock n →L[ℂ] Fock n) (hZ : Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p) :
    ∑ i, ((1-κ)*lam i)*(S i).pquad thermalWeight
      (normalizedSlices η θ hη hθ ρ σ τ S lam i Z) ≤ S₀.pquad thermalWeight Z := by
  have ha := physical_diagram_arithmetic η θ κ hη hθ hκ ρ σ τ ω S₀ S lam hlam he₁ he₂ he₀
  have hh : ∀ i Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      (1-κ)*(S i).pquad (fun _ => 1) (normalizedSlices η θ hη hθ ρ σ τ S lam i Z) ≤
        (1+ε)*S₀.pquad (fun _ => 1) Z := by
    intro i U hU
    fin_cases i
    · exact (S 0).normalized_hessian S₀ (hlam 0) hκ1 _ U (hh₁ U hU)
    · exact (S 1).normalized_hessian S₀ (hlam 1) hκ1 _ U (hh₂ U hU)
  have hc := diagram_reference S₀ S lam (fun i => (hlam i).le) κ ε hκ.2
    (normalizedSlices η θ hη hθ ρ σ τ S lam) hh hr hs
  have ht := diagram_thermal S₀ S (fun i => (1-κ)*lam i)
    (normalizedSlices η θ hη hθ ρ σ τ S lam) ha.2 ha.1 hc.1 hc.2
  exact diagram_observable S₀ S _ (fun i => mul_nonneg (sub_nonneg.mpr hκ.2) (hlam i).le)
    _ thermalWeight (fun q => (weight_pos q.1.property _).le)
    (fun i U => (S i).thermal_summable U) ht Z hZ
end EntropyPhotonNumber

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

end EntropyPhotonNumber.SpectralLogData

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
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open TensorLp KrausBounded ThermalSpectral ThermalSpectral.Space ThermalMetric


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.physical_thermal_contraction := @_root_.OAI.EntropyPhotonNumber.physical_thermal_contraction
