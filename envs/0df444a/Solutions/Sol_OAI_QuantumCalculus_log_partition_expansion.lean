-- Prove2me | solution 1 for OAI.QuantumCalculus.log_partition_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:56:33.563842+00:00
-- url     : https://prove2.me/submissions/a2d6730d-68e1-48de-a5d9-e3e7e1196958

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/FiniteVariation.lean:L1099-L1123
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumCalculus.log_partition_expansion. The node keeps its source
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

-- ---- from OAI.InformationTheory.PhotonNumber.FiniteVariation ----
namespace OAI

noncomputable section

section
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

namespace FiniteBlock

section
variable {I J E : Type*} [Fintype I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable (b : HilbertBasis (I ⊕ J) ℂ E) (c : OrthonormalBasis I ℂ (EuclideanSpace ℂ I))

variable [CompleteSpace E]

variable [DecidableEq I]

end

open NormedSpace Matrix
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

end FiniteBlock

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I J : Type*}

variable [CompleteSpace E]

end QuantumTrace

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber

section
open TraceEnsemble

end

open QuantumTrace TraceEnsemble

end EntropyPhotonNumber

namespace FiniteBlock

section
open QuantumTrace
variable {I J E K : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FiniteBlock

namespace EntropyPhotonNumber
open QuantumTrace
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

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
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator

namespace FiniteBlock
variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FiniteBlock

namespace EntropyPhotonNumber

section
open QuantumTrace TraceEnsemble
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

end

section
open QuantumTrace
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

end

open QuantumTrace TraceEnsemble
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

end EntropyPhotonNumber

end

section
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

namespace QuantumCalculus

section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance] OAI.QuantumCalculus.instNormedAlgebraRat_oAI
theorem exp_sub_eq_integral (a b : A) :
    exp b - exp a = ∫ s in (0 : ℝ)..1, exp ((1-s) • a) * (b-a) * exp (s • b) := by
  have hd (s : ℝ) : HasDerivAt (fun t : ℝ => exp ((1-t) • a) * exp (t • b))
      (exp ((1-s) • a) * (b-a) * exp (s • b)) s := by
    have hleft : HasDerivAt (fun t : ℝ => exp ((1-t) • a))
        (-(exp ((1-s) • a) * a)) s := by
      simpa [Function.comp_def] using (hasDerivAt_exp_smul_const a (1-s)).scomp s
        ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s))
    have hright := hasDerivAt_exp_smul_const' b s
    have heq : exp ((1-s) • a) * (b-a) * exp (s • b) =
        -(exp ((1-s) • a) * a) * exp (s • b) +
          exp ((1-s) • a) * (b * exp (s • b)) := by noncomm_ring
    rw [heq]
    exact hleft.mul hright
  have hc : Continuous (fun s : ℝ => exp ((1-s) • a) * (b-a) * exp (s • b)) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable 0 1)
  simpa using h.symm

theorem exp_add_smul_sub (a z : A) (t : ℝ) :
    exp (a+t • z) - exp a =
      t • (∫ s in (0 : ℝ)..1, exp ((1-s) • a) * z * exp (s • (a+t • z))) := by
  rw [exp_sub_eq_integral, ← intervalIntegral.integral_smul]
  congr 1
  funext s
  simp

theorem continuous_duhamel (a z : A) :
    Continuous (fun t : ℝ =>
      ∫ s in (0 : ℝ)..1, exp ((1-s) • a) * z * exp (s • (a+t • z))) := by
  have hc : Continuous (Function.uncurry (fun t s : ℝ =>
      exp ((1-s) • a) * z * exp (s • (a+t • z)))) := by fun_prop
  have hh := continuous_parametric_integral_of_continuous (μ := volume) hc (s := Set.Icc (0:ℝ) 1) isCompact_Icc
  convert! hh using 1
  funext t
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

theorem hasDerivAt_exp_add_smul_zero (a z : A) :
    HasDerivAt (fun t : ℝ => exp (a+t • z))
      (∫ s in (0 : ℝ)..1, exp ((1-s) • a) * z * exp (s • a)) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hc := (continuous_duhamel a z).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 0)
  apply Filter.Tendsto.congr' ?_ (by simpa only [zero_smul, add_zero] using hc)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  rw [slope_def_module]
  simp only [zero_smul, add_zero, sub_zero, exp_add_smul_sub, smul_smul, inv_mul_cancel₀ ht0,
    one_smul]

theorem hasDerivAt_exp_add_smul (a z : A) (t : ℝ) :
    HasDerivAt (fun u : ℝ => exp (a+u • z))
      (∫ s in (0 : ℝ)..1, exp ((1-s) • (a+t • z)) * z * exp (s • (a+t • z))) t := by
  have hh := (hasDerivAt_exp_add_smul_zero (a+t • z) z).scomp_of_eq t
    ((hasDerivAt_id t).sub_const t) (by simp)
  convert! hh using 1
  · funext u
    simp [sub_smul]
  · simp

end

section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
attribute [local instance] OAI.QuantumCalculus.instNormedAlgebraRat_oAI_1
theorem trace_duhamel (τ : A →L[ℝ] ℝ) (hτ : ∀ x y, τ (x*y) = τ (y*x))
    (a z : A) :
    τ (∫ s in (0 : ℝ)..1, exp ((1-s) • a) * z * exp (s • a)) = τ (exp a * z) := by
  have hc : Continuous (fun s : ℝ => exp ((1-s) • a) * z * exp (s • a)) := by fun_prop
  rw [← τ.intervalIntegral_comp_comm (hc.intervalIntegrable 0 1)]
  have heq (s : ℝ) : τ (exp ((1-s) • a) * z * exp (s • a)) = τ (exp a * z) := by
    rw [hτ, ← mul_assoc, ← exp_add_of_commute
      (((Commute.refl a).smul_left s).smul_right (1-s)), ← add_smul]
    simp
  simp_rw [heq]
  simp

theorem hasDerivAt_trace_exp (τ : A →L[ℝ] ℝ) (hτ : ∀ x y, τ (x*y) = τ (y*x))
    (a z : A) (t : ℝ) :
    HasDerivAt (fun u : ℝ => τ (exp (a+u • z))) (τ (exp (a+t • z)*z)) t := by
  have hh := τ.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_add_smul a z t)
  simpa only [Function.comp_def, trace_duhamel τ hτ] using hh

theorem hasDerivAt_trace_exp_mul (τ : A →L[ℝ] ℝ)
    (a z : A) (t : ℝ) :
    HasDerivAt (fun u : ℝ => τ (exp (a+u • z)*z))
      (τ ((∫ s in (0 : ℝ)..1,
         exp ((1-s) • (a+t • z))*z*exp (s • (a+t • z)))*z)) t := by
  exact τ.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_exp_add_smul a z t).mul_const z)

end

section
open scoped Matrix.Norms.Operator ComplexConjugate
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

end

section
open Filter Asymptotics

theorem quadratic_expansion {f f' : ℝ → ℝ} {d : ℝ}
    (hff' : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt f (f' t) t)
    (hd : HasDerivAt f' d 0) :
    (fun t => f t-f 0-f' 0*t-d/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2) := by
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.mp hff'
  let R : ℝ → ℝ := fun t => f t-f 0-f' 0*t-d/2*t^2
  let R' : ℝ → ℝ := fun t => f' t-f' 0-d*t
  have he : R' =o[𝓝 (0:ℝ)] (fun t => t) := by
    simpa only [R', sub_zero, smul_eq_mul, mul_comm d] using hd.isLittleO
  have hs := (convex_ball (0:ℝ) δ).isLittleO_pow_succ_real
    (Metric.mem_ball_self hδ) (n := 1) (f := R) (f' := R') ?_ ?_
  · have hn : 𝓝[Metric.ball (0:ℝ) δ] (0:ℝ) = 𝓝 0 :=
      nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds 0 hδ)
    simpa [R, hn] using hs
  · intro t ht
    have hf := hh ht
    have hpoly := ((hasDerivAt_const t (f' 0)).mul (hasDerivAt_id t))
    have hquad := ((hasDerivAt_id t).pow 2).const_mul (d/2)
    convert (((hf.sub_const (f 0)).sub hpoly).sub hquad).hasDerivWithinAt using 1
    · funext u
      dsimp [R]
    · dsimp [R']
      ring
  · simpa only [sub_zero, pow_one] using he.mono nhdsWithin_le_nhds

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
attribute [local instance] OAI.QuantumCalculus.instNormedAlgebraRat_oAI_2
theorem log_partition_expansion (τ : A →L[ℝ] ℝ)
    (hτ : ∀ x y, τ (x*y) = τ (y*x)) (a z : A) (c : ℝ)
    (hn : c+τ (exp a) = 1) :
    (fun t : ℝ => Real.log (c+τ (exp (a+t • z))) -
      τ (exp a*z)*t -
      (τ ((∫ s in (0:ℝ)..1, exp ((1-s) • a)*z*exp (s • a))*z) -
        (τ (exp a*z))^2)/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2) := by
  let P : ℝ → ℝ := fun t => c+τ (exp (a+t • z))
  let M : ℝ → ℝ := fun t => τ (exp (a+t • z)*z)
  have hP (t : ℝ) : HasDerivAt P (M t) t := (hasDerivAt_trace_exp τ hτ a z t).const_add c
  have hP0 : P 0 = 1 := by simpa [P] using hn
  have hnz : ∀ᶠ t in 𝓝 (0:ℝ), P t ≠ 0 :=
    (hP 0).continuousAt.eventually_ne (by simp [hP0])
  have hlog : ∀ᶠ t in 𝓝 (0:ℝ),
      HasDerivAt (fun t => Real.log (P t)) (M t/P t) t := by
    filter_upwards [hnz] with t ht using (hP t).log ht
  have hd := (hasDerivAt_trace_exp_mul τ a z 0).div (hP 0) (by simp [hP0])
  have hd' : HasDerivAt (fun t => M t/P t)
      (τ ((∫ s in (0:ℝ)..1, exp ((1-s) • a)*z*exp (s • a))*z) -
        (τ (exp a*z))^2) 0 := by
    convert hd using 1 <;>
    first | rfl |
      simp only [M, zero_smul, add_zero, hP0, mul_one, div_one, pow_two]
  have hh := quadratic_expansion hlog hd'
  simpa only [P, M, zero_smul, add_zero, hn, Real.log_one, sub_zero, div_one] using hh

end

section
open Matrix Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

end

section
open Filter Asymptotics
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
attribute [local instance] OAI.QuantumCalculus.instNormedAlgebraRat_oAI_3
end

open Matrix Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

end QuantumCalculus

namespace FiniteBlock
open QuantumCalculus
variable {I J : Type*} [Fintype I] [DecidableEq I]

end FiniteBlock

namespace EntropyPhotonNumber
open QuantumCalculus QuantumTrace Filter Asymptotics
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

end EntropyPhotonNumber

namespace FiniteBlock
variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FiniteBlock

namespace EntropyPhotonNumber
open QuantumTrace
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

end EntropyPhotonNumber

namespace QuantumCalculus
open Matrix Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

end QuantumCalculus

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

namespace QuantumCalculus

end QuantumCalculus

end

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

namespace EntropyPhotonNumber

section
open QuantumTrace TraceEnsemble
variable {n : ℕ}

end

section
open QuantumCalculus QuantumTrace Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

end

open QuantumCalculus QuantumTrace Filter Asymptotics

end EntropyPhotonNumber

namespace FiniteBlock
open DiagonalForms.System
variable {I J : Type*} [Fintype I]
end FiniteBlock

namespace EntropyPhotonNumber
open QuantumCalculus QuantumTrace Filter Asymptotics
open scoped Matrix.Norms.Operator

end EntropyPhotonNumber

namespace FiniteBlock
open DiagonalForms.System
open scoped ComplexConjugate
variable {I J : Type*} [Fintype I]

end FiniteBlock

namespace BKM
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end BKM

namespace EntropyPhotonNumber

section
open QuantumTrace DiagonalForms.System
open scoped ComplexConjugate
variable {n : ℕ} {J K L : Type*} [Fintype K] [DecidableEq K]

end

open QuantumTrace DiagonalForms.System
variable {n : ℕ} {K L : Type*} [Fintype K] [DecidableEq K]

end EntropyPhotonNumber

namespace BKM
open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

end BKM

namespace Complex
open scoped _root_.Complex
open scoped ComplexConjugate
end Complex

namespace BKM

section
open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
end

section
open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

end

open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end BKM

namespace EntropyPhotonNumber

section
open scoped ComplexConjugate ComplexStarModule
variable {n : ℕ} {J : Type*}

end

section
open QuantumTrace DiagonalForms.System
open scoped ComplexStarModule
variable {n : ℕ} {K L J : Type*} [Fintype K] [DecidableEq K]

end

open QuantumTrace DiagonalForms.System
variable {n : ℕ} {J K L : Type*} [Fintype K] [DecidableEq K]
end EntropyPhotonNumber

namespace BKM
open scoped BigOperators
open DiagonalForms.System
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end BKM

namespace EntropyPhotonNumber
open QuantumTrace DiagonalForms.System
variable {n : ℕ} {J : Type*} [DecidableEq J]

end EntropyPhotonNumber

namespace BKM

section
open scoped BigOperators ComplexConjugate
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

end BKM

namespace CenteredTests
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
end CenteredTests

namespace EntropyPhotonNumber

section
open QuantumTrace DiagonalForms.System
variable {n : ℕ} {I J : Type*} [DecidableEq J]

end

open QuantumTrace DiagonalForms.System
variable {n : ℕ} {J : Type*} [DecidableEq J]
end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace
namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

end GibbsData
end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.QuantumCalculus
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
open Filter Asymptotics
attribute [local instance] OAI.QuantumCalculus.instNormedAlgebraRat_oAI_2


theorem solution : type_of% @_root_.OAI.QuantumCalculus.log_partition_expansion := @_root_.OAI.QuantumCalculus.log_partition_expansion
