-- Prove2me | solution 1 for OAI.QuantumTrace.energySet_totallyBounded
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:41:56.550566+00:00
-- url     : https://prove2.me/submissions/026031f9-8312-4bf7-8e76-c5128167401f

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Entropy.lean:L744-L790
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.energySet_totallyBounded. The node keeps its source
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
import Theorems.Thm_OAI_QuantumTrace_double_compression_norm_le

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

end

section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

end

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

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

-- ---- from OAI.InformationTheory.PhotonNumber.Entropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

section
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace Annihilation
open EntropyPhotonNumber QuantumTrace WeightedShift
open scoped ComplexConjugate
variable {n : ℕ}

end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped BigOperators
variable {n : ℕ} {I : Type*}

end WeightedGenerator

namespace WeightedShift
variable {I K : Type*}
end WeightedShift

namespace EntropyPhotonNumber
open QuantumTrace WeightedShift Annihilation
variable {n : ℕ}

end EntropyPhotonNumber

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

namespace QuantumTrace

section
open Filter Topology

theorem numberBox_compl_weight {n K : ℕ} {k : Fin n → ℕ}
    (hk : k ∉ numberBox n K) : (K + 1 : ℝ) ≤ ∑ j, (k j : ℝ) := by
  classical
  simp only [numberBox, Fintype.mem_piFinset, Finset.mem_range, not_forall] at hk
  obtain ⟨j, hj⟩ := hk
  have hh : K + 1 ≤ k j := Nat.le_of_not_gt hj
  have hs := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => Nat.zero_le (k i))
    (Finset.mem_univ j)
  exact_mod_cast hh.trans hs

theorem number_tail_mass_le {n K : ℕ} (p : (Fin n → ℕ) → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hs : Summable p)
    (hE : Summable (fun k => (∑ j, (k j : ℝ)) * p k)) :
    (∑' k : {k // k ∉ numberBox n K}, p k) ≤
      (∑' k, (∑ j, (k j : ℝ)) * p k) / (K + 1) := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < K + 1)]
  rw [← tsum_mul_right]
  calc
    _ ≤ ∑' k : {k // k ∉ numberBox n K}, (∑ j, ((k : Fin n → ℕ) j : ℝ)) * p k := by
      apply ((hs.subtype _).mul_right _).tsum_le_tsum _ (hE.subtype _)
      intro k
      change p k * (K + 1) ≤ (∑ j, ((k : Fin n → ℕ) j : ℝ)) * p k
      nlinarith [numberBox_compl_weight k.property, hp k]
    _ ≤ _ := Summable.tsum_subtype_le _ _ (fun k => mul_nonneg
      (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (hp k)) hE

open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

end

section
open ContinuousLinearMap InnerProductSpace Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

end

section
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

section
open ContinuousLinearMap InnerProductSpace Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

omit [CompleteSpace H] in
theorem matrixEmbed_continuous (b : HilbertBasis ι ℂ H) (s : Finset ι) :
    Continuous (matrixEmbed b s) := by
  unfold matrixEmbed
  fun_prop

omit [CompleteSpace H] in
theorem matrixEmbed_entries (b : HilbertBasis ι ℂ H) (s : Finset ι) (T : H →L[ℂ] H) :
    matrixEmbed b s (fun i j => inner ℂ (b i) (T (b j))) =
      basisProjection b s ∘L T ∘L basisProjection b s := by
  classical
  apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  rintro _ ⟨k, rfl⟩
  simp only [comp_apply, basisProjection_apply_basis]
  by_cases hk : k ∈ s
  · simp only [ite_eq_left hk, matrixEmbed, sum_apply, smul_apply, rankOne_apply,
      orthonormal_iff_ite.mp b.orthonormal]
    simp only [smul_ite, smul_zero, one_smul, ite_smul, zero_smul]
    have hj (j : s) : ((j : ι) = k) = (j = ⟨k, hk⟩) := by
      apply propext
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp_rw [hj]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    calc
      _ = ∑ i ∈ s, inner ℂ (b i) (T (b k)) • b i :=
        Finset.sum_coe_sort s (fun i : ι => inner ℂ (b i) (T (b k)) • b i)
      _ = _ := by simp [basisProjection, basisApprox, sum_apply, rankOne_apply]
  · simp only [ite_eq_right hk, map_zero, matrixEmbed, sum_apply, smul_apply, rankOne_apply,
      orthonormal_iff_ite.mp b.orthonormal]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hj : (j : ι) ≠ k := fun hh => hk (hh ▸ j.property)
    simp [hj]

omit [CompleteSpace H] in
theorem entry_norm_le_one (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H} (hT : ‖T‖ ≤ 1)
    (i j : ι) : ‖inner ℂ (b i) (T (b j))‖ ≤ 1 := by
  calc
    _ ≤ ‖b i‖ * ‖T (b j)‖ := norm_inner_le_norm _ _
    _ = ‖T (b j)‖ := by rw [b.orthonormal.norm_eq_one, one_mul]
    _ ≤ ‖T‖ * ‖b j‖ := T.le_opNorm _
    _ ≤ 1 := by simpa only [b.orthonormal.norm_eq_one, mul_one] using hT

omit [CompleteSpace H] in

theorem double_compressions_compact (b : HilbertBasis ι ℂ H) (s : Finset ι) :
    ∃ C : Set (H →L[ℂ] H), IsCompact C ∧
      ∀ T : H →L[ℂ] H, ‖T‖ ≤ 1 → basisProjection b s ∘L T ∘L basisProjection b s ∈ C := by
  let C := matrixEmbed b s '' Metric.closedBall (0 : s → s → ℂ) 1
  refine ⟨C, (isCompact_closedBall _ _).image (matrixEmbed_continuous b s), ?_⟩
  intro T hT
  refine ⟨(fun i j => inner ℂ (b i) (T (b j))), ?_, matrixEmbed_entries b s T⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro j
  exact entry_norm_le_one b hT i j

end

section
open ContinuousLinearMap Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem energySet_totallyBounded {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H) (E : ℝ) :
    TotallyBounded (energySet b E) := by
  classical
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (E / (ε / 4) ^ 2)
  have hcut : E / (K + 1) < (ε / 4) ^ 2 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < K + 1)]
    have hh := (div_lt_iff₀ (by positivity : (0 : ℝ) < (ε / 4) ^ 2)).mp hK
    nlinarith
  let s := numberBox n K
  let P := basisProjection b s
  obtain ⟨C, hC, hPC⟩ := double_compressions_compact b s
  obtain ⟨t, htfin, hcover⟩ := Metric.totallyBounded_iff.mp hC.totallyBounded (ε / 2) (by positivity)
  refine ⟨t, htfin, ?_⟩
  intro T hT
  have hp := hT.1
  have htr := hT.2.1
  have hmass : (1 - ∑ k ∈ s, (inner ℂ (b k) (T (b k))).re) =
      ∑' k : {k // k ∉ s}, (inner ℂ (b k) (T (b k))).re := by
    have hh := htr.summable.sum_add_tsum_compl (s := s)
    rw [htr.tsum_eq] at hh
    change (∑ k ∈ s, (inner ℂ (b k) (T (b k))).re) +
      (∑' k : {k // k ∉ s}, (inner ℂ (b k) (T (b k))).re) = 1 at hh
    linarith
  have hq0 : 0 ≤ 1 - ∑ k ∈ s, (inner ℂ (b k) (T (b k))).re := by
    rw [hmass]
    exact tsum_nonneg (fun k => hp.re_inner_nonneg_right (b k))
  have hqb : 1 - ∑ k ∈ s, (inner ℂ (b k) (T (b k))).re < (ε / 4) ^ 2 := by
    rw [hmass]
    apply lt_of_le_of_lt _ hcut
    exact (number_tail_mass_le _ (fun k => hp.re_inner_nonneg_right (b k)) htr.summable hT.2.2.1).trans
      (div_le_div_of_nonneg_right hT.2.2.2 (by positivity))
  have happ : dist T (P ∘L T ∘L P) < ε / 2 := by
    rw [dist_eq_norm]
    apply (double_compression_norm_le b hp htr s).trans_lt
    have hs := Real.sq_sqrt hq0
    have hn := Real.sqrt_nonneg (1 - ∑ k ∈ s, (inner ℂ (b k) (T (b k))).re)
    nlinarith
  have hc : P ∘L T ∘L P ∈ C := hPC T (norm_le_trace b hp htr)
  obtain ⟨y, hy, hdist⟩ : ∃ y ∈ t, dist (P ∘L T ∘L P) y < ε / 2 := by
    rcases Set.mem_iUnion.mp (hcover hc) with ⟨y, hy⟩
    rcases Set.mem_iUnion.mp hy with ⟨hyt, hy⟩
    exact ⟨y, hyt, hy⟩
  simp only [Set.mem_iUnion, Metric.mem_ball]
  refine ⟨y, hy, ?_⟩
  exact (dist_triangle T (P ∘L T ∘L P) y).trans_lt (by linarith)

end

open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end QuantumTrace

end

namespace EntropyPhotonNumber
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

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

namespace TraceEnsemble
open Filter Topology
open scoped BigOperators
variable {I A E G : Type*}
variable [NormedAddCommGroup G] [CompleteSpace G]

variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end TraceEnsemble

namespace TensorLp
variable {A B : Type*}

end TensorLp

namespace EntropyPhotonNumber

section
open Filter Topology TensorLp

end

open QuantumTrace TraceEnsemble
end EntropyPhotonNumber

namespace QuantumTrace
open scoped ENNReal

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace
end

open QuantumTrace Filter Topology

namespace Regularization
variable {n : ℕ} (R : Regularization n)

end Regularization
end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I J : Type*}

variable [CompleteSpace E]

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace

end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace TensorLp

end

open QuantumTrace

end EntropyPhotonNumber

namespace QuantumTrace

section
variable {ι J L : Type*}

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace TensorLp

end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {J : Type*}

end QuantumTrace

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

end TraceEnsemble

namespace EntropyPhotonNumber
open QuantumTrace TraceEnsemble

end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.QuantumTrace
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open ContinuousLinearMap Filter Topology


theorem solution : type_of% @_root_.OAI.QuantumTrace.energySet_totallyBounded := @_root_.OAI.QuantumTrace.energySet_totallyBounded
