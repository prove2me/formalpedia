-- Prove2me | solution 1 for OAI.GAD.entropy_le_of_logDetShift_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:38:59.487558+00:00
-- url     : https://prove2.me/submissions/0d1432eb-205d-416e-8b81-b4cac87382f7

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/LogDetEntropy.lean:L139-L166
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.entropy_le_of_logDetShift_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Theorems.Thm_OAI_GAD_entropy_sum_le_of_log_sum_le
import Theorems.Thm_OAI_GAD_logDetShift_eq_sum

-- ---- from OAI.InformationTheory.AmplitudeDamping.SpectralEntropy ----
namespace OAI

universe u_1

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

/-- Trace invariance under a unitary change of basis. -/
theorem trace_unitary_conj (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp

/-- Spectral trace for any function on the finite real spectrum. -/
theorem trace_cfc_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, (f (hA.eigenvalues i) : ℂ) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, trace_unitary_conj]
  simp [Matrix.trace_diagonal, Function.comp_def]

theorem entropy_eq_sum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    entropy A = ∑ i, Real.negMulLog (hA.eigenvalues i) := by
  simp [entropy, trace_cfc_eq hA]

end GAD

end

end OAI

-- ---- from OAI.InformationTheory.AmplitudeDamping.LogDetEntropy ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder

open scoped BigOperators Topology
open Filter Set
namespace GAD

end GAD

open scoped BigOperators ComplexOrder MatrixOrder Topology
open Matrix
namespace GAD
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

/-- Entropy may be compared between unequal matrix sizes by their resolvent determinants. -/
theorem entropy_le_of_logDetShift_le {κ : Type u_3} [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrace : A.trace.re = B.trace.re)
    (hlog : ∀ r : ℝ, 0 < r → logDetShift r A ≤ logDetShift r B) :
    entropy A ≤ entropy B := by
  have htA : A.trace.re = ∑ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]; simp
  have htB : B.trace.re = ∑ i, hB.isHermitian.eigenvalues i := by
    rw [hB.isHermitian.trace_eq_sum_eigenvalues]; simp
  have hh := entropy_sum_le_of_log_sum_le
    (Sum.elim (fun _ : ι ↦ (1 : ℝ)) (fun _ : κ ↦ -1))
    (Sum.elim hA.isHermitian.eigenvalues hB.isHermitian.eigenvalues) ?_ ?_ ?_
  · simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, one_mul, neg_one_mul,
      Finset.sum_neg_distrib, add_neg_le_iff_le_add, zero_add, entropy_eq_sum hA.isHermitian,
      entropy_eq_sum hB.isHermitian] using hh
  · intro i
    cases i with
    | inl i => exact hA.eigenvalues_nonneg i
    | inr i => exact hB.eigenvalues_nonneg i
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, one_mul, neg_one_mul,
      Finset.sum_neg_distrib, ← htA, ← htB, htrace, add_neg_cancel]
  · intro t ht
    have hh := hlog t⁻¹ (inv_pos.mpr ht)
    rw [logDetShift_eq_sum hA (inv_nonneg.mpr ht.le),
      logDetShift_eq_sum hB (inv_nonneg.mpr ht.le)] at hh
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, one_mul, neg_one_mul,
      Finset.sum_neg_distrib, add_neg_le_iff_le_add, zero_add, div_eq_mul_inv, mul_comm] using hh

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.entropy_le_of_logDetShift_le := @_root_.OAI.GAD.entropy_le_of_logDetShift_le
