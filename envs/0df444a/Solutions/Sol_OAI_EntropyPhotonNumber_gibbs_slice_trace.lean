-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.gibbs_slice_trace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:00:11.98662+00:00
-- url     : https://prove2.me/submissions/c3aa0194-77d6-4de6-8b1d-519d0eddd142

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Entropy.lean:L2115-L2176
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.gibbs_slice_trace. The node keeps its source
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
import Theorems.Thm_OAI_QuantumTrace_gibbs_form_energy_identity

-- ---- from OAI.Analysis.QuantumTrace.Basic ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
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

theorem inversePower_mul (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p q : ℕ) :
    inversePower s hs p * inversePower s hs q = inversePower s hs (p+q) := by
  ext x i
  simp only [mul_apply_eq_comp, inversePower_apply, pow_add, mul_inv,
    Complex.ofReal_mul, mul_assoc]

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

theorem rootNumberWeight_pow_eight {n : ℕ} (i : Fin n → ℕ) :
    rootNumberWeight i^8 = numberWeight i^4 := by
  rw [show (8 : ℕ) = 2*4 from rfl, pow_mul, rootNumberWeight, Real.sq_sqrt (by linarith [numberWeight_one_le i])]

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

theorem basisExpectation_ensemble (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞)
    {v : J → E} (hv : Summable (fun j => ‖v j‖^2)) :
    basisExpectation b w (TraceEnsemble.operator v) = ∑' j, basisMoment b w (v j) := by
  have he (i : I) : ENNReal.ofReal (inner ℂ (b i) (TraceEnsemble.operator v (b i))).re =
      ∑' j, ENNReal.ofReal (‖inner ℂ (b i) (v j)‖^2) := by
    have hs := TraceEnsemble.hasSum_quadratic hv (b i)
    rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs.summable]
  simp only [basisExpectation, he, ← ENNReal.tsum_mul_left, basisMoment]
  exact ENNReal.tsum_comm

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

theorem numberWeight_eq {n : ℕ} (i : NumberIndex n) :
    numberWeight i = 1+(totalNumber i : ℝ) := by
  simp only [numberWeight, totalNumber, Nat.cast_sum]

end

open QuantumTrace

theorem gibbsFactor_quadratic {ι : Type*} (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i)
    (k : ℝ) (B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) (x : SequenceHilbert ι) :
    (inner ℂ x (gibbsFactor s hs k B x)).re = k*‖x‖^2+
      (inner ℂ (inversePower s hs 3 x) (B (inversePower s hs 3 x))).re := by
  have hh : inner ℂ (inversePower s hs 3 x) (B (inversePower s hs 3 x)) =
      inner ℂ x (inversePower s hs 3 (B (inversePower s hs 3 x))) :=
    (inversePower_positive s hs 3).isSymmetric x (B (inversePower s hs 3 x))
  change (inner ℂ x (k • x+inversePower s hs 3 (B (inversePower s hs 3 x)))).re = _
  rw [inner_add_right, Complex.add_re, ← hh]
  rw [inner_smul_right_eq_smul, Complex.smul_re]
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

theorem energyInverse_mul_three {n : ℕ} (x : Fock n) :
    energyInverse n (inversePower rootNumberWeight rootNumberWeight_one_le 3 x) =
      inversePower rootNumberWeight rootNumberWeight_one_le 4 x := by
  exact congrArg (fun T : Fock n →L[ℂ] Fock n => T x)
    (inversePower_mul rootNumberWeight rootNumberWeight_one_le 1 3)

theorem gibbsFactor_slice_form {n : ℕ} {J I : Type*}
    (b : HilbertBasis J ℂ (Fock n)) (w : J → ℝ≥0∞) (V : I → Fock n →L[ℂ] Fock n)
    {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive) {α β : ℝ}
    (he : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re =
      ENNReal.ofReal α*sliceMoment b w V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x))
    {k : ℝ} (hk : 0 ≤ k) (x : Fock n) :
    ENNReal.ofReal (inner ℂ x (gibbsFactor rootNumberWeight rootNumberWeight_one_le k B x)).re =
      ENNReal.ofReal k*ENNReal.ofReal (‖x‖^2)+
      (ENNReal.ofReal α*sliceMoment b w V (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)+
      ENNReal.ofReal β*numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) := by
  have hBx : 0 ≤ (inner ℂ (inversePower rootNumberWeight rootNumberWeight_one_le 3 x)
      (B (inversePower rootNumberWeight rootNumberWeight_one_le 3 x))).re :=
    hB.re_inner_nonneg_right _
  rw [gibbsFactor_quadratic, ENNReal.ofReal_add (mul_nonneg hk (sq_nonneg _))
    hBx, ENNReal.ofReal_mul hk, he, energyInverse_mul_three]

end EntropyPhotonNumber

namespace QuantumTrace

section
variable {ι J L : Type*}

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

theorem sliceMoment_ensemble (b : HilbertBasis K ℂ E) (w : K → ℝ≥0∞)
    (V : I → E →L[ℂ] E) {v : J → E}
    (hs : Summable (fun ij : I × J => ‖V ij.1 (v ij.2)‖^2)) :
    (∑' j, sliceMoment b w V (v j)) =
      basisExpectation b w (TraceEnsemble.operator (fun ij : I × J => V ij.1 (v ij.2))) := by
  rw [basisExpectation_ensemble b w hs]
  simp only [sliceMoment, ENNReal.tsum_prod']
  exact ENNReal.tsum_comm

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace TensorLp

end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {J : Type*}

theorem basisExpectation_ofReal (b : HilbertBasis J ℂ E) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) {T : E →L[ℂ] E} (hp : T.IsPositive)
    (hs : Summable (fun j => w j*(inner ℂ (b j) (T (b j))).re)) :
    basisExpectation b (fun j => ENNReal.ofReal (w j)) T =
      ENNReal.ofReal (∑' j, w j*(inner ℂ (b j) (T (b j))).re) := by
  simp only [basisExpectation, ← ENNReal.ofReal_mul (hw _)]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (hw j)
    (hp.re_inner_nonneg_right _)) hs).symm

end QuantumTrace

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

theorem diagonalVector_operator (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hs : Summable p) (T : E →L[ℂ] E)
    (he : ∀ j, T (b j) = (p j : ℂ) • b j) : operator (diagonalVector b p) = T := by
  have hb (j : J) : operator (diagonalVector b p) (b j) = T (b j) := by
    rw [diagonalVector_eigen b p hp hs j, he]
  ext x
  have hh := (operator (diagonalVector b p)).hasSum (b.hasSum_repr x)
  apply hh.unique
  convert T.hasSum (b.hasSum_repr x) using 1
  funext j
  simp only [ContinuousLinearMap.map_smul, hb]

end TraceEnsemble

namespace EntropyPhotonNumber
open QuantumTrace TraceEnsemble

theorem sequenceBasis_numberKet {n : ℕ} (i : NumberIndex n) :
    sequenceBasis (NumberIndex n) i = numberKet i := by
  apply lp.ext
  funext j
  by_cases h : i = j
  · subst j; simp [sequenceBasis_apply, numberKet, lp.single_apply]
  · simp [sequenceBasis_apply, numberKet, lp.single_apply, h]

theorem gibbs_slice_trace {n : ℕ} {J L K I : Type*}
    (c : HilbertBasis L ℂ (Fock n)) (u : L → ℝ) (hu : ∀ l, 0 < u l)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1)
    (ρ : State n) (heρ : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (hm : FiniteMoment 4 ρ)
    (a : HilbertBasis K ℂ (Fock n)) (w : K → ℝ≥0∞)
    (V : I → Fock n →L[ℂ] Fock n) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (σ : State n)
    (heσ : TraceEnsemble.operator (fun z : I × J => V z.1 (diagonalVector b p z.2)) = σ.op)
    {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive) {α β : ℝ}
    (hform : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re =
      ENNReal.ofReal α*sliceMoment a w V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x))
    {k : ℝ} (hk : 0 < k)
    (heK : ∀ l, gibbsInverse rootNumberWeight rootNumberWeight_one_le k B (c l) =
      (((u l)⁻¹ : ℝ) : ℂ) • c l) :
    ∃ E : ℝ, HasSum (fun l => u l*(inner ℂ (c l) (ρ.op (c l))).re) E ∧
      ENNReal.ofReal E = ENNReal.ofReal k*ENNReal.ofReal (numberMoment 4 ρ)+
        (ENNReal.ofReal α*basisExpectation a w σ.op+
         ENNReal.ofReal β*ENNReal.ofReal (energy ρ)) := by
  classical
  have hm' : Summable (fun i => rootNumberWeight i^8*
      (inner ℂ (sequenceBasis _ i) (ρ.op (sequenceBasis _ i))).re) := by
    simpa only [rootNumberWeight_pow_eight, numberWeight_eq, sequenceBasis_numberKet,
      FiniteMoment, entry] using hm
  obtain ⟨y, _, hy, hyS, hyE, hyA, hK⟩ := gibbs_form_energy_identity
    rootNumberWeight rootNumberWeight_one_le (gibbsFactor rootNumberWeight rootNumberWeight_one_le k B)
    (gibbsFactor_strictPositive _ _ hk hB) c u hu heK b ρ.op p hp heρ hm'
  have hnorm : (∑' j, ‖y j‖^2) = numberMoment 4 ρ := by
    simpa only [rootNumberWeight_pow_eight, numberWeight_eq, numberMoment,
      sequenceBasis_numberKet, entry] using hyE
  have hv : HasSum (fun j => ‖diagonalVector b p j‖^2) 1 := by
    simpa only [diagonalVector_norm_sq b p hp] using hs
  have hρv := diagonalVector_operator b p hp hs.summable ρ.op heρ
  have hSv : (∑' j, sliceMoment a w V (diagonalVector b p j)) = basisExpectation a w σ.op := by
    rw [sliceMoment_ensemble a w V (TraceEnsemble.kraus_hasSum hV hv).summable, heσ]
  have hNv : (∑' j, numberVectorMoment (diagonalVector b p j)) = ENNReal.ofReal (energy ρ) := by
    rw [show (∑' j, numberVectorMoment (diagonalVector b p j)) =
      basisExpectation (numberBasis n) (fun i => (totalNumber i : ℝ≥0∞))
        (TraceEnsemble.operator (diagonalVector b p)) from
      (basisExpectation_ensemble _ _ hv.summable).symm, hρv]
    have he := basisExpectation_ofReal (numberBasis n) (fun i => (totalNumber i : ℝ))
      (fun _ => Nat.cast_nonneg _) ρ.positive (by simpa only [FiniteEnergy, numberBasis_apply, entry] using (finiteMoment_finiteEnergy (by norm_num : 1 ≤ 4) hm))
    simpa only [ENNReal.ofReal_natCast, energy, numberBasis_apply, entry] using he
  let A := gibbsFactor rootNumberWeight rootNumberWeight_one_le k B
  have hA : A.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (gibbsFactor_strictPositive _ _ hk hB).nonneg
  refine ⟨_, hK, ?_⟩
  change ENNReal.ofReal (∑' j, (inner ℂ (y j) (A (y j))).re) = _
  have hsum : ENNReal.ofReal (∑' j, (inner ℂ (y j) (A (y j))).re) =
      ∑' j, ENNReal.ofReal (inner ℂ (y j) (A (y j))).re :=
    ENNReal.ofReal_tsum_of_nonneg (fun j => hA.re_inner_nonneg_right (y j)) hyA
  rw [hsum]
  have hQ (j : J) : ENNReal.ofReal (inner ℂ (y j) (A (y j))).re =
      ENNReal.ofReal k*ENNReal.ofReal (‖y j‖^2)+
      (ENNReal.ofReal α*sliceMoment a w V (diagonalVector b p j)+
       ENNReal.ofReal β*numberVectorMoment (diagonalVector b p j)) := by
    have hh := gibbsFactor_slice_form a w V hB hform hk.le (y j)
    simpa only [hy, diagonalVector, A] using hh
  simp_rw [hQ]
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left,
    ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, hSv, hNv,
    ← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hyS, hnorm]

end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open QuantumTrace TraceEnsemble


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.gibbs_slice_trace := @_root_.OAI.EntropyPhotonNumber.gibbs_slice_trace
