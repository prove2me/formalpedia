-- Prove2me | solution 1 for OAI.QuantumTrace.quantum_klein
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:03:39.091777+00:00
-- url     : https://prove2.me/submissions/c87973f1-8ece-4c0e-9626-ca1402b4da1d

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/GibbsVariational.lean:L155-L189
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.quantum_klein. The node keeps its source
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
import Theorems.Thm_OAI_QuantumTrace_StochasticOverlap_hasSum_row_product
import Theorems.Thm_OAI_QuantumTrace_negMulLog_le_crossEntropy

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

theorem negMulLog_lt_crossEntropy {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hne : p ≠ q) :
    Real.negMulLog p < q - p + p * (-Real.log q) := by
  by_cases hz : p = 0
  · simp [hz, hq]
  have hneq : p/q ≠ 1 := by
    intro h
    exact hne ((div_eq_one_iff_eq hq.ne').mp h)
  have h := mul_lt_mul_of_pos_left
    (Real.negMulLog_lt_one_sub_self (div_nonneg hp hq.le) hneq) hq
  change q * (-(p / q) * Real.log (p / q)) < q * (1 - p / q) at h
  rw [Real.log_div hz hq.ne'] at h
  have hl : q * (-(p / q) * (Real.log p - Real.log q)) =
      -p * Real.log p + p * Real.log q := by field_simp; ring
  have hr : q * (1 - p / q) = q - p := by field_simp
  rw [hl, hr] at h
  dsimp [Real.negMulLog]
  linarith

namespace StochasticOverlap
variable {I J : Type*} (a : StochasticOverlap I J)

theorem hasSum_col_product (q : J → ℝ) {s : ℝ} (hq : HasSum q s) :
    HasSum (fun ij : I × J => a.value ij.1 ij.2 * q ij.2) s := by
  exact (Equiv.prodComm J I).hasSum_iff.mp (a.transpose.hasSum_row_product q hq)

theorem hasSum_prod_nonneg {v : I × J → ℝ} {c : I → ℝ} {s : ℝ}
    (hv : ∀ ij, 0 ≤ v ij) (hf : ∀ i, HasSum (fun j => v (i,j)) (c i))
    (hc : HasSum c s) : HasSum v s := by
  have hs : Summable v := (summable_prod_of_nonneg hv).mpr
    ⟨fun i => (hf i).summable, by simpa only [(hf _).tsum_eq] using hc.summable⟩
  convert hs.hasSum using 1
  rw [hs.tsum_prod]
  simp only [(hf _).tsum_eq, hc.tsum_eq]

theorem hasSum_crossEntropy {p : I → ℝ} {q : J → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp1 : HasSum p 1)
    (hq : ∀ j, 0 < q j) (hq1 : HasSum q 1)
    {C : ℝ} (hc : HasSum (fun j => a.diagonal p j * (-Real.log (q j))) C) :
    HasSum (fun ij : I × J => a.value ij.1 ij.2 * p ij.1 * (-Real.log (q ij.2))) C := by
  have hpairs := a.hasSum_row_product p hp1
  have hl (j : J) : 0 ≤ -Real.log (q j) := by
    apply neg_nonneg.mpr
    apply Real.log_nonpos (hq j).le
    rw [← hq1.tsum_eq]
    exact hq1.summable.le_tsum j (fun j _ => (hq j).le)
  apply (Equiv.prodComm J I).hasSum_iff.mp
  apply hasSum_prod_nonneg (c := fun j => a.diagonal p j * (-Real.log (q j)))
    (fun ji => mul_nonneg (mul_nonneg (a.nonneg _ _) (hp _)) (hl _)) _ hc
  intro j
  exact (hpairs.summable.prod_symm.prod_factor j).hasSum.mul_right _

theorem klein {p : I → ℝ} {q : J → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp1 : HasSum p 1)
    (hq : ∀ j, 0 < q j) (hq1 : HasSum q 1)
    {H C : ℝ} (hh : HasSum (fun i => Real.negMulLog (p i)) H)
    (hc : HasSum (fun j => a.diagonal p j * (-Real.log (q j))) C) :
    H ≤ C ∧ (H = C → ∀ i j, a.value i j ≠ 0 → p i = q j) := by
  let d (ij : I × J) : ℝ := a.value ij.1 ij.2 *
    (q ij.2 - p ij.1 + p ij.1 * (-Real.log (q ij.2)) - Real.negMulLog (p ij.1))
  have hd (ij : I × J) : 0 ≤ d ij :=
    mul_nonneg (a.nonneg _ _) (sub_nonneg.mpr (negMulLog_le_crossEntropy (hp _) (hq _)))
  have hdSum : HasSum d (C-H) := by
    have h := (((a.hasSum_col_product q hq1).sub (a.hasSum_row_product p hp1)).add
      (a.hasSum_crossEntropy hp hp1 hq hq1 hc)).sub
      (a.hasSum_row_product (fun i => Real.negMulLog (p i)) hh)
    convert! h using 1
    · funext ij
      dsimp [d]
      ring
    · ring
  refine ⟨sub_nonneg.mp (hdSum.tsum_eq ▸ tsum_nonneg hd), ?_⟩
  intro he i j ha
  by_contra hne
  have hpos : 0 < d (i,j) := mul_pos (lt_of_le_of_ne (a.nonneg i j) (Ne.symm ha))
    (sub_pos.mpr (negMulLog_lt_crossEntropy (hp i) (hq j) hne))
  have hx := hdSum.summable.le_tsum (i,j) (fun ij _ => hd ij)
  rw [hdSum.tsum_eq, he, sub_self] at hx
  exact (not_lt_of_ge hx) hpos

end StochasticOverlap
end

section
open scoped BigOperators
variable {I J : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem basisOverlap_diagonal (b : HilbertBasis I ℂ E) (c : HilbertBasis J ℂ E)
    (T : E →L[ℂ] E) (p : I → ℝ) (he : ∀ i, T (b i) = (p i : ℂ) • b i) (j : J) :
    (basisOverlap b c).diagonal p j = (inner ℂ (c j) (T (c j))).re := by
  have hh := hasSum_quadratic_eigenbasis b T p he (c j)
  simpa only [StochasticOverlap.diagonal, basisOverlap, norm_inner_symm, mul_comm] using hh.tsum_eq

theorem quantum_klein (b : HilbertBasis I ℂ E) (c : HilbertBasis J ℂ E)
    {T S : E →L[ℂ] E} (hs : S.IsSymmetric)
    {p : I → ℝ} {q : J → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : HasSum p 1)
    (hq : ∀ j, 0 < q j) (hq1 : HasSum q 1)
    (heT : ∀ i, T (b i) = (p i : ℂ) • b i)
    (heS : ∀ j, S (c j) = (q j : ℂ) • c j)
    {H C : ℝ} (hh : HasSum (fun i => Real.negMulLog (p i)) H)
    (hc : HasSum (fun j => (inner ℂ (c j) (T (c j))).re * (-Real.log (q j))) C) :
    H ≤ C ∧ (H = C → T = S) := by
  have hcc : HasSum (fun j => (basisOverlap b c).diagonal p j * (-Real.log (q j))) C := by
    simpa only [basisOverlap_diagonal b c T p heT] using hc
  obtain ⟨hle, heq⟩ := (basisOverlap b c).klein hp hp1 hq hq1 hh hcc
  refine ⟨hle, ?_⟩
  intro he
  have hcoef (i : I) (j : J) :
      (q j : ℂ) * inner ℂ (c j) (b i) = (p i : ℂ) * inner ℂ (c j) (b i) := by
    by_cases hz : inner ℂ (c j) (b i) = 0
    · simp [hz]
    · rw [heq he i j (by simpa only [basisOverlap, ne_eq, sq_eq_zero_iff,
          norm_eq_zero] using hz)]
  have hb (i : I) : T (b i) = S (b i) := by
    apply c.repr.injective
    apply lp.ext
    funext j
    simp only [c.repr_apply_apply, heT, inner_smul_right]
    have hsym : inner ℂ (S (c j)) (b i) = inner ℂ (c j) (S (b i)) := hs _ _
    rw [← hsym, heS, inner_smul_left]
    simpa only [Complex.conj_ofReal] using (hcoef i j).symm
  ext x
  have ht := T.hasSum (b.hasSum_repr x)
  have hu := S.hasSum (b.hasSum_repr x)
  apply ht.unique
  convert hu using 1
  funext i
  simp only [ContinuousLinearMap.map_smul, hb]

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
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.QuantumTrace.quantum_klein := @_root_.OAI.QuantumTrace.quantum_klein
