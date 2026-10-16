-- Prove2me | solution 1 for OAI.QuantumTrace.negativeLog_form_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:28:56.128077+00:00
-- url     : https://prove2.me/submissions/c93efac0-d39a-43dc-8af5-8d2f5d533ac5

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/SpectralLog.lean:L556-L612
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.negativeLog_form_mono. The node keeps its source
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
import Theorems.Thm_OAI_QuantumTrace_cfc_apply_eigenvector

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

end SpectralLogData
end EntropyPhotonNumber

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

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

theorem log_apply_eigenvector {T : E →L[ℂ] E} (hT : IsStrictlyPositive T)
    {x : E} {p : ℝ} (he : T x = (p : ℂ) • x) :
    CFC.log T x = (Real.log p : ℂ) • x := by
  have hs := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hT.nonneg).isSymmetric
  change cfc Real.log T x = _
  rw [cfc_real_eq_complex Real.log hs.isSelfAdjoint]
  have hf : ContinuousOn (fun z : ℂ => (Real.log z.re : ℂ)) (spectrum ℂ T) := by
    intro z hz
    have hp : 0 < z.re :=
      (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R := ℝ) T hs.isSelfAdjoint).mp hT
        z.re (hs.isSelfAdjoint.spectrumRestricts.apply_mem hz)
    exact (Complex.continuous_ofReal.continuousAt.comp
      ((Real.continuousAt_log hp.ne').comp Complex.continuous_re.continuousAt)).continuousWithinAt
  simpa using cfc_apply_eigenvector hs he _ hf

theorem add_scalar_strictPositive {T : E →L[ℂ] E} (hT : T.IsPositive)
    {ε : ℝ} (hε : 0 < ε) : IsStrictlyPositive (T + ε • 1) := by
  exact (IsStrictlyPositive.smul hε isStrictlyPositive_one).nonneg_add
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hT)

theorem regularNegLog_eigen {T : E →L[ℂ] E} (hT : T.IsPositive)
    {ε : ℝ} (hε : 0 < ε) {x : E} {p : ℝ} (he : T x = (p : ℂ) • x) :
    regularNegLog T ε x = ((Real.log (1+ε)-Real.log (p+ε) : ℝ) : ℂ) • x := by
  have ht : (T + ε • 1) x = ((p+ε : ℝ) : ℂ) • x := by
    simp [he, add_smul]
  rw [regularNegLog, sub_apply,
    log_apply_eigenvector (add_scalar_strictPositive hT hε) ht]
  simp [sub_smul]

theorem regularNegLog_antitone {R T : E →L[ℂ] E} (hR : R.IsPositive)
    (hRT : R ≤ T) {ε : ℝ} (hε : 0 < ε) : regularNegLog T ε ≤ regularNegLog R ε := by
  have hRT' : R + ε • (1 : E →L[ℂ] E) ≤ T + ε • 1 := add_le_add_left hRT _
  have hRp : IsStrictlyPositive (R + ε • (1 : E →L[ℂ] E)) := add_scalar_strictPositive hR hε
  have hh : CFC.log (R + ε • (1 : E →L[ℂ] E)) ≤ CFC.log (T + ε • 1) := by
    apply CFC.log_le_log
    · exact hRT'
    · exact hRp
  change Real.log (1+ε) • 1 - CFC.log (T + ε • 1) ≤
    Real.log (1+ε) • 1 - CFC.log (R + ε • 1)
  exact sub_le_sub_left hh _

theorem regularNegLog_scalar_bounds {p ε : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hε : 0 ≤ ε) : 0 ≤ Real.log (1+ε)-Real.log (p+ε) ∧
      Real.log (1+ε)-Real.log (p+ε) ≤ -Real.log p := by
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
  · have hh : p*(1+ε) ≤ p+ε := by nlinarith
    have hl := Real.log_le_log (mul_pos hp (by linarith)) hh
    rw [Real.log_mul hp.ne' (by linarith : (1+ε : ℝ) ≠ 0)] at hl
    linarith

theorem negativeLog_form_mono (b : HilbertBasis I ℂ E) (c : HilbertBasis J ℂ E)
    {T R : E →L[ℂ] E} (hT : T.IsPositive) (hR : R.IsPositive) (hRT : R ≤ T)
    (p : I → ℝ) (q : J → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j)
    (hp1 : ∀ i, p i ≤ 1) (hq1 : ∀ j, q j ≤ 1)
    (heT : ∀ i, T (b i) = (p i : ℂ) • b i)
    (heR : ∀ j, R (c j) = (q j : ℂ) • c j) (x : E)
    (hfin : Summable (fun j => -Real.log (q j)*‖inner ℂ (c j) x‖^2)) :
    Summable (fun i => -Real.log (p i)*‖inner ℂ (b i) x‖^2) ∧
      (∑' i, -Real.log (p i)*‖inner ℂ (b i) x‖^2) ≤
        ∑' j, -Real.log (q j)*‖inner ℂ (c j) x‖^2 := by
  have hnp (i : I) : 0 ≤ -Real.log (p i)*‖inner ℂ (b i) x‖^2 :=
    mul_nonneg (neg_nonneg.mpr (Real.log_nonpos (hp i).le (hp1 i))) (sq_nonneg _)
  have hpartial (s : Finset I) :
      ∑ i ∈ s, -Real.log (p i)*‖inner ℂ (b i) x‖^2 ≤
        ∑' j, -Real.log (q j)*‖inner ℂ (c j) x‖^2 := by
    have hbdd (ε : ℝ) (hε : 0 < ε) :
        ∑ i ∈ s, (Real.log (1+ε)-Real.log (p i+ε))*‖inner ℂ (b i) x‖^2 ≤
          ∑' j, -Real.log (q j)*‖inner ℂ (c j) x‖^2 := by
      have ht := hasSum_quadratic_eigenbasis b (regularNegLog T ε)
        (fun i => Real.log (1+ε)-Real.log (p i+ε))
        (fun i => regularNegLog_eigen hT hε (heT i)) x
      have hr := hasSum_quadratic_eigenbasis c (regularNegLog R ε)
        (fun j => Real.log (1+ε)-Real.log (q j+ε))
        (fun j => regularNegLog_eigen hR hε (heR j)) x
      have hquad : (inner ℂ x (regularNegLog T ε x)).re ≤
          (inner ℂ x (regularNegLog R ε x)).re := by
        have hh := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
          (sub_nonneg.mpr (regularNegLog_antitone hR hRT hε))).re_inner_nonneg_right x
        simpa [inner_sub_right] using hh
      calc
        _ ≤ (inner ℂ x (regularNegLog T ε x)).re := by
          rw [← ht.tsum_eq]
          exact ht.summable.sum_le_tsum s (fun i _ =>
            mul_nonneg (regularNegLog_scalar_bounds (hp i) (hp1 i) hε.le).1 (sq_nonneg _))
        _ ≤ (inner ℂ x (regularNegLog R ε x)).re := hquad
        _ ≤ _ := by
          rw [← hr.tsum_eq]
          exact Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_right
            (regularNegLog_scalar_bounds (hq j) (hq1 j) hε.le).2 (sq_nonneg _)) hr.summable hfin
    have hc : ContinuousAt (fun ε : ℝ =>
      ∑ i ∈ s, (Real.log (1+ε)-Real.log (p i+ε))*‖inner ℂ (b i) x‖^2) 0 := by
      apply tendsto_finsetSum
      intro i _
      apply ContinuousAt.mul_const
      apply ContinuousAt.sub
      · exact (Real.continuousAt_log (by norm_num : (1+(0:ℝ)) ≠ 0)).comp
          (continuousAt_const.add continuousAt_id)
      · exact (Real.continuousAt_log (by simpa using (hp i).ne')).comp
          (continuousAt_const.add continuousAt_id)
    have hl : Filter.Tendsto (fun ε : ℝ =>
        ∑ i ∈ s, (Real.log (1+ε)-Real.log (p i+ε))*‖inner ℂ (b i) x‖^2)
        (𝓝[>] 0) (𝓝 (∑ i ∈ s, -Real.log (p i)*‖inner ℂ (b i) x‖^2)) := by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto hl (eventually_mem_nhdsWithin.mono fun ε hε => hbdd ε hε)
  have hs := summable_of_sum_le hnp hpartial
  refine ⟨hs, ?_⟩
  exact le_of_tendsto hs.hasSum (Filter.Eventually.of_forall hpartial)

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
open OAI OAI.QuantumTrace
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


theorem solution : type_of% @_root_.OAI.QuantumTrace.negativeLog_form_mono := @_root_.OAI.QuantumTrace.negativeLog_form_mono
