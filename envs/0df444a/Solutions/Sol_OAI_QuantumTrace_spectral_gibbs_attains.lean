-- Prove2me | solution 1 for OAI.QuantumTrace.spectral_gibbs_attains
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:05:13.604135+00:00
-- url     : https://prove2.me/submissions/c7df4783-f1be-4cb0-ad60-e7c0b445aff4

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/GibbsVariational.lean:L239-L290
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.spectral_gibbs_attains. The node keeps its source
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
import Theorems.Thm_OAI_QuantumTrace_cfc_apply_eigenvector
import Theorems.Thm_OAI_QuantumTrace_hasSum_trace_basis
import Theorems.Thm_OAI_QuantumTrace_summable_polynomial_heat

-- ---- from OAI.Analysis.QuantumTrace.Basic ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
private theorem CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

namespace QuantumTrace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

theorem quadratic_le_trace_mul_norm_sq (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hT : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) (x : E) :
    (inner ℂ x (T x)).re ≤ τ * ‖x‖ ^ 2 := by
  let S := CFC.sqrt T
  have hs : S.IsSymmetric :=
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg T)).isSymmetric
  have ht' : HasSum (fun i => ‖S (b i)‖ ^ 2) τ := by
    simpa only [sqrt_inner_eq hT] using ht
  rw [sqrt_inner_eq hT, ← (basis_hasSum_norm_sq b (S x)).tsum_eq,
    ← ht'.tsum_eq, ← tsum_mul_right]
  apply Summable.tsum_le_tsum
  · intro i
    have he : inner ℂ (b i) (S x) = inner ℂ (S (b i)) x := (hs (b i) x).symm
    rw [he]
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) (S (b i)) x) 2
  · exact (basis_hasSum_norm_sq b (S x)).summable
  · exact ht'.summable.mul_right _

theorem operator_le_trace_smul_id (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hT : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) :
    T ≤ (τ : ℂ) • ContinuousLinearMap.id ℂ E := by
  rw [ContinuousLinearMap.le_def]
  refine ⟨?_, ?_⟩
  · exact (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.id).sub hT.isSymmetric
  · intro x
    change 0 ≤ (inner ℂ (((τ : ℂ) • ContinuousLinearMap.id ℂ E - T) x) x).re
    rw [sub_apply, smul_apply, ContinuousLinearMap.id_apply, inner_sub_left, inner_smul_left,
      hT.inner_left_eq_inner_right x x]
    simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using
      sub_nonneg.mpr (quadratic_le_trace_mul_norm_sq b hT ht x)

theorem norm_le_trace (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hT : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) : ‖T‖ ≤ τ := by
  have hn : 0 ≤ τ := ht.nonneg (fun i => hT.re_inner_nonneg_right (b i))
  have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (operator_le_trace_smul_id b hT ht) ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hT)
  apply h.trans
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
  exact mul_le_of_le_one_right hn ContinuousLinearMap.norm_id_le

end

section
open Filter

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

end

section
open Filter ContinuousLinearMap InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End Submodule
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End
open scoped ContinuousFunctionalCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem entropyOperator_eq_complex {T : E →L[ℂ] E} (hs : T.IsSymmetric) :
    entropyOperator T = cfc (fun z : ℂ => (-(z.re * Real.log z.re) : ℂ)) T := by
  rw [entropyOperator, cfc_real_eq_complex Real.negMulLog hs.isSelfAdjoint]
  congr 1
  funext z
  simp [Real.negMulLog_def]

theorem entropyOperator_positive {T : E →L[ℂ] E} (hp : T.IsPositive) (hn : ‖T‖ ≤ 1) :
    (entropyOperator T).IsPositive := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    have : entropyOperator T = 0 := Subsingleton.elim _ _
    rw [this]
    exact isPositive_zero
  | inr h =>
    apply (ContinuousLinearMap.nonneg_iff_isPositive _).mp
    exact cfc_nonneg (fun x hx => Real.negMulLog_nonneg
    (spectrum_nonneg_of_nonneg ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hp) hx)
    ((Real.le_norm_self _).trans ((spectrum.norm_le_norm_of_mem hx).trans hn)))

end

section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

end

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem entropyOperator_apply_eigenvector {T : E →L[ℂ] E} (hs : T.IsSymmetric)
    {x : E} {p : ℝ} (he : T x = (p : ℂ) • x) :
    entropyOperator T x = (Real.negMulLog p : ℂ) • x := by
  rw [entropyOperator_eq_complex hs]
  have hf : Continuous (fun z : ℂ => (Real.negMulLog z.re : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_negMulLog.comp Complex.continuous_re)
  simpa [Real.negMulLog_def] using cfc_apply_eigenvector hs he _ hf.continuousOn

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

end

section

open Filter Topology
open scoped Classical
variable {ι : Type*}
end

section
open Filter Topology
open scoped Classical
variable {ι : Type*}

end

section
open Filter Topology
variable {ι : Type*}

end

section
open ContinuousLinearMap Module.End Submodule
universe v
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section
open Filter Topology
variable {ι : Type*}

end

section
open Filter Topology

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*}

theorem basisDiagonal_positive (b : HilbertBasis ι ℂ E) (p : ι → ℝ)
    (hb : ∃ C : ℝ, ∀ i, ‖(p i : ℂ)‖ ≤ C) (hp : ∀ i, 0 ≤ p i) :
    (basisDiagonal b p hb).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  change ((inner ℂ (b.repr.symm (diagonalMap _ hb (b.repr x))) x).re : ℂ) = inner ℂ (b.repr.symm (diagonalMap _ hb (b.repr x))) x ∧
    0 ≤ (inner ℂ (b.repr.symm (diagonalMap _ hb (b.repr x))) x).re
  rw [b.repr.symm.inner_map_eq_flip]
  simp only [LinearIsometryEquiv.symm_symm]
  exact (ContinuousLinearMap.isPositive_iff_complex _).mp (diagonalMap_positive p hb hp) (b.repr x)

theorem basisDiagonal_hasSum_trace (b : HilbertBasis ι ℂ E) (p : ι → ℝ)
    (hb : ∃ C : ℝ, ∀ i, ‖(p i : ℂ)‖ ≤ C) {z : ℝ} (hp : HasSum p z) :
    HasSum (fun i => (inner ℂ (b i) (basisDiagonal b p hb (b i))).re) z := by
  convert hp using 1
  funext i
  rw [basisDiagonal_eigen, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  simp

theorem spectralGibbs_positive [Nonempty ι] (b : HilbertBasis ι ℂ E) (u : ι → ℝ)
    (hs : Summable (fun i => Real.exp (-u i))) : (spectralGibbs b u hs).IsPositive :=
  basisDiagonal_positive b _ _ (fun i => (gibbsWeight_pos u hs i).le)

theorem spectralGibbs_trace_one [CompleteSpace E] [Nonempty ι] (b : HilbertBasis ι ℂ E) (u : ι → ℝ)
    (hs : Summable (fun i => Real.exp (-u i))) {κ : Type*} (c : HilbertBasis κ ℂ E) :
    HasSum (fun j => (inner ℂ (c j) (spectralGibbs b u hs (c j))).re) 1 := by
  exact hasSum_trace_basis b c (spectralGibbs_positive b u hs)
    (basisDiagonal_hasSum_trace b _ _ (gibbsWeight_hasSum u hs))

end

section
variable {ι J : Type*}

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

end

open scoped BigOperators ComplexConjugate
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end QuantumTrace

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace QuantumTrace
variable {ι J : Type*}

end QuantumTrace

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

theorem spectral_gibbs_attains {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [Nonempty J] {I : Type*} (a : HilbertBasis I ℂ E)
    (b : HilbertBasis J ℂ E) (u : J → ℝ) (hu : ∀ j, 0 ≤ u j)
    (hheat : Summable (fun j => Real.exp (-u j)))
    (hhalf : Summable (fun j => Real.exp (-(1/2 : ℝ)*u j))) :
    let ω := spectralGibbs b u hheat
    Summable (fun j => u j*(inner ℂ (b j) (ω (b j))).re) ∧
      Summable (fun i => (inner ℂ (a i) (entropyOperator ω (a i))).re) ∧
      (∑' j, u j*(inner ℂ (b j) (ω (b j))).re) -
        (∑' i, (inner ℂ (a i) (entropyOperator ω (a i))).re) = -Real.log (heatPartition u) := by
  let ω := spectralGibbs b u hheat
  have he (j : J) : (inner ℂ (b j) (ω (b j))).re = gibbsWeight u j := by
    rw [show ω = spectralGibbs b u hheat from rfl, spectralGibbs_eigen,
      inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
    simp
  have hE : Summable (fun j => u j*gibbsWeight u j) := by
    have hh : Summable (fun j => Real.exp (-u j)*u j) := by
      apply Summable.of_nonneg_of_le (fun j => mul_nonneg (Real.exp_nonneg _) (hu j)) _
        (summable_polynomial_heat u hu hhalf)
      intro j
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      nlinarith [sq_nonneg (u j-1)]
    apply (hh.div_const (heatPartition u)).congr
    intro j
    dsimp [gibbsWeight]
    ring
  have hH : HasSum (fun j => Real.negMulLog (gibbsWeight u j))
      ((∑' j, u j*gibbsWeight u j)+Real.log (heatPartition u)) := by
    have hh := hE.hasSum.add ((gibbsWeight_hasSum u hheat).mul_right (Real.log (heatPartition u)))
    convert! hh using 1
    · funext j
      rw [show Real.negMulLog (gibbsWeight u j) = gibbsWeight u j * (-Real.log (gibbsWeight u j)) by
        rw [Real.negMulLog]; ring, log_gibbsWeight u hheat]
      ring
    · ring
  have hHb : HasSum (fun j => (inner ℂ (b j) (entropyOperator ω (b j))).re)
      ((∑' j, u j*gibbsWeight u j)+Real.log (heatPartition u)) := by
    convert! hH using 1
    funext j
    rw [entropyOperator_apply_eigenvector (spectralGibbs_positive b u hheat).isSymmetric
      (spectralGibbs_eigen b u hheat j), inner_smul_right, inner_self_eq_norm_sq_to_K,
      b.orthonormal.norm_eq_one]
    simp
  have hHa := hasSum_trace_basis b a
    (entropyOperator_positive (spectralGibbs_positive b u hheat)
      (norm_le_trace b (spectralGibbs_positive b u hheat) (spectralGibbs_trace_one b u hheat b))) hHb
  refine ⟨?_, hHa.summable, ?_⟩
  · change Summable (fun j => u j*(inner ℂ (b j) (ω (b j))).re)
    simpa only [he] using hE
  · change (∑' j, u j*(inner ℂ (b j) (ω (b j))).re) - _ = _
    simp only [he, hHa.tsum_eq]
    ring

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

end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.QuantumTrace
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.QuantumTrace.spectral_gibbs_attains := @_root_.OAI.QuantumTrace.spectral_gibbs_attains
