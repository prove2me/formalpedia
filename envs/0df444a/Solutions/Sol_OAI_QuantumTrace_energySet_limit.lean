-- Prove2me | solution 1 for OAI.QuantumTrace.energySet_limit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:40:35.395986+00:00
-- url     : https://prove2.me/submissions/70d07b94-ff2f-440e-b7fc-8f5473cf87f5

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Entropy.lean:L610-L659
-- (upload_full_project.md Phase 4): solution for node OAI.QuantumTrace.energySet_limit. The node keeps its source
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
import Theorems.Thm_OAI_QuantumTrace_tendsto_tsum_of_uniform_tail

-- ---- from OAI.InformationTheory.PhotonNumber.Entropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

theorem tsum_bound_of_tendsto {α ι : Type*} {l : Filter α} [NeBot l]
    {f : α → ι → ℝ} {g : ι → ℝ} {C : ℝ}
    (hfp : ∀ a i, 0 ≤ f a i) (hfs : ∀ a, Summable (f a))
    (hfb : ∀ a, (∑' i, f a i) ≤ C)
    (hlim : ∀ i, Tendsto (fun a => f a i) l (𝓝 (g i))) :
    Summable g ∧ (∑' i, g i) ≤ C := by
  have hg : ∀ i, 0 ≤ g i := fun i => ge_of_tendsto (hlim i) (Eventually.of_forall (fun a => hfp a i))
  have hs : ∀ s : Finset ι, (∑ i ∈ s, g i) ≤ C := by
    intro s
    apply le_of_tendsto (tendsto_finsetSum s (fun i _ => hlim i))
    exact Eventually.of_forall (fun a => ((hfs a).sum_le_tsum s (fun i _ => hfp a i)).trans (hfb a))
  exact ⟨summable_of_sum_le hg hs, Real.tsum_le_of_sum_le hg hs⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem energySet_limit {α : Type*} {l : Filter α} [NeBot l] {n : ℕ}
    (b : HilbertBasis (Fin n → ℕ) ℂ H) {E : ℝ}
    {T : α → H →L[ℂ] H} {A : H →L[ℂ] H}
    (hT : ∀ a, T a ∈ energySet b E) (hlim : Tendsto T l (𝓝 A)) : A ∈ energySet b E := by
  have hA : A.IsPositive := by
    apply (ContinuousLinearMap.nonneg_iff_isPositive _).mp
    exact isClosed_Ici.mem_of_tendsto hlim (Eventually.of_forall (fun a =>
      (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (hT a).1))
  have hdiag (k : Fin n → ℕ) :
      Tendsto (fun a => (inner ℂ (b k) (T a (b k))).re) l
        (𝓝 (inner ℂ (b k) (A (b k))).re) := by
    have heval : Continuous (fun B : H →L[ℂ] H => B (b k)) :=
      continuous_id.clm_apply continuous_const
    exact Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_const_nhds.inner (heval.continuousAt.tendsto.comp hlim))
  have hds := tsum_bound_of_tendsto
    (fun a k => (hT a).1.re_inner_nonneg_right (b k))
    (fun a => (hT a).2.1.summable) (fun a => (hT a).2.1.tsum_eq.le) hdiag
  have hes := tsum_bound_of_tendsto
    (fun a k => mul_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
      ((hT a).1.re_inner_nonneg_right (b k)))
    (fun a => (hT a).2.2.1) (fun a => (hT a).2.2.2)
    (fun k => tendsto_const_nhds.mul (hdiag k))
  have hsum : Tendsto (fun a => ∑' k, (inner ℂ (b k) (T a (b k))).re) l
      (𝓝 (∑' k, (inner ℂ (b k) (A (b k))).re)) := by
    apply tendsto_tsum_of_uniform_tail
      (fun a => (hT a).2.1.summable) hds.1
      (fun a k => (hT a).1.re_inner_nonneg_right (b k))
      (fun k => hA.re_inner_nonneg_right (b k)) hdiag
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_gt (E / ε)
    have hb : E / (K + 1) < ε := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < K + 1)]
      have hh := (div_lt_iff₀ hε).mp hK
      nlinarith
    refine ⟨numberBox n K, ?_, ?_⟩
    · intro a
      apply lt_of_le_of_lt _ hb
      exact (number_tail_mass_le _ (fun k => (hT a).1.re_inner_nonneg_right (b k))
        (hT a).2.1.summable (hT a).2.2.1).trans
        (div_le_div_of_nonneg_right (hT a).2.2.2 (by positivity))
    · apply lt_of_le_of_lt _ hb
      exact (number_tail_mass_le _ (fun k => hA.re_inner_nonneg_right (b k))
        hds.1 hes.1).trans (div_le_div_of_nonneg_right hes.2 (by positivity))
  have heq : (∑' k, (inner ℂ (b k) (A (b k))).re) = 1 := by
    apply tendsto_nhds_unique hsum
    convert! (tendsto_const_nhds : Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1)) using 1
    funext a
    exact (hT a).2.1.tsum_eq
  exact ⟨hA, heq ▸ hds.1.hasSum, hes⟩

end

section
open ContinuousLinearMap InnerProductSpace Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

end

section
open ContinuousLinearMap Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

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
open Filter Topology


theorem solution : type_of% @_root_.OAI.QuantumTrace.energySet_limit := @_root_.OAI.QuantumTrace.energySet_limit
