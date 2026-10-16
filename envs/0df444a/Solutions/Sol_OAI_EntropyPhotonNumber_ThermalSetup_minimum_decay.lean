-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.ThermalSetup.minimum_decay
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:52:17.66759+00:00
-- url     : https://prove2.me/submissions/23c4f324-342a-4b1f-a295-d5bd27cffffe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Minimum.lean:L1406-L1475
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.ThermalSetup.minimum_decay. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Minimum
import Theorems.Thm_OAI_BeamLadder_adjoint_covariance
import Theorems.Thm_OAI_BeamLadder_discarded_covariance
import Theorems.Thm_OAI_BeamLadder_output_weak
import Theorems.Thm_OAI_BeamLadder_radial_covariance
import Theorems.Thm_OAI_BeamLadder_retained_covariance
import Theorems.Thm_OAI_BeamLadder_tensorPreimage_lowerL
import Theorems.Thm_OAI_BeamLadder_tensorPreimage_lowerR
import Theorems.Thm_OAI_BeamLadder_tensorPreimage_raiseL
import Theorems.Thm_OAI_BeamLadder_tensorPreimage_raiseR
import Theorems.Thm_OAI_CrossEnsemble_operator_comp_left
import Theorems.Thm_OAI_CrossEnsemble_shifted_both_operator_eq
import Theorems.Thm_OAI_EntropyPhotonNumber_Regularization_minimum_spectral_pairing_balance
import Theorems.Thm_OAI_EntropyPhotonNumber_SpectralLogData_centeredEnergy_lowerEnergy
import Theorems.Thm_OAI_EntropyPhotonNumber_SpectralLogData_entropy_production
import Theorems.Thm_OAI_EntropyPhotonNumber_ThermalSetup_physical_estimate
import Theorems.Thm_OAI_EntropyPhotonNumber_WeightedColumns_lowerEnergy_hasSum
import Theorems.Thm_OAI_EntropyPhotonNumber_WeightedColumns_thermal_lowerEnergy
import Theorems.Thm_OAI_EntropyPhotonNumber_WeightedColumns_weakMean_trace
import Theorems.Thm_OAI_EntropyPhotonNumber_beamOutput_powerMoment_le
import Theorems.Thm_OAI_EntropyPhotonNumber_thermalGenerator_drift
import Theorems.Thm_OAI_KrausBounded_dual_one
import Theorems.Thm_OAI_PhysicalGenerator_weakOperator_entry
import Theorems.Thm_OAI_ThermalMetric_defectVector_mem_centeredSpace
import Theorems.Thm_OAI_WeightedGenerator_weakDefect_spectral

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

theorem hasSum_slice_inner (x y : H (A × B)) :
    HasSum (fun b => inner ℂ (slice x b) (slice y b)) (inner ℂ x y) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) x y
  have hr (b : B) : HasSum (fun a => inner ℂ (x (a,b)) (y (a,b)))
      (inner ℂ (slice x b) (slice y b)) := lp.hasSum_inner (𝕜 := ℂ) (slice x b) (slice y b)
  have hc : HasSum (fun ba : B × A => inner ℂ (x (ba.2,ba.1)) (y (ba.2,ba.1)))
      (inner ℂ x y) := (Equiv.prodComm B A).hasSum_iff.mpr h
  exact hc.prod_fiberwise hr

end TensorLp

end

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.BeamTrace ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
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
theorem weight_down (j : Fin n) (k : NumberIndex n) (hk : 0 < k j) :
    numberWeight (down j k)=numberWeight k-1 := by
  have hh := weight_up j (down j k)
  rw [up_down j k hk] at hh
  linarith
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

theorem retained_adjoint_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) :
    (lowerL j).adjoint ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        ((Real.sqrt η:ℂ) • (lowerL j).adjoint+(Real.sqrt (1-η):ℂ) • (lowerR j).adjoint) := by
  simpa only [map_add, map_smulₛₗ, Complex.conj_ofReal] using
    adjoint_covariance (beamUnitary η hη) (lowerL j) _ (retained_covariance η hη j)

theorem discarded_adjoint_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) :
    (lowerR j).adjoint ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (-(Real.sqrt (1-η):ℂ) • (lowerL j).adjoint+(Real.sqrt η:ℂ) • (lowerR j).adjoint) := by
  simpa only [map_add, map_smulₛₗ, map_neg, Complex.conj_ofReal] using
    adjoint_covariance (beamUnitary η hη) (lowerR j) _ (discarded_covariance η hη j)
end

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}

theorem retained_creation_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) :
    raiseL j ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        ((Real.sqrt η:ℂ) • raiseL j+(Real.sqrt (1-η):ℂ) • raiseR j) := by
  unfold raiseL raiseR
  rw [ContinuousLinearMap.comp_assoc, retained_adjoint_covariance,
    ← ContinuousLinearMap.comp_assoc, radial_covariance, ContinuousLinearMap.comp_assoc]
  congr 1
  ext x ke
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply, map_add, map_smul]

theorem discarded_creation_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) :
    raiseR j ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (-(Real.sqrt (1-η):ℂ) • raiseL j+(Real.sqrt η:ℂ) • raiseR j) := by
  unfold raiseL raiseR
  rw [ContinuousLinearMap.comp_assoc, discarded_adjoint_covariance,
    ← ContinuousLinearMap.comp_assoc, radial_covariance, ContinuousLinearMap.comp_assoc]
  congr 1
  ext x ke
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply, map_add, map_smul]

theorem raiseR_up (j : Fin n) (x : JointFock n) (ke : NumberIndex n × NumberIndex n) :
    raiseR j x (upR j ke)=((Real.sqrt ((ke.2 j:ℝ)+1)/W ke:ℝ):ℂ)*x ke := by
  change (increase (W (upR j ke)):ℂ)*((lowerR j).adjoint x (upR j ke))=_
  rw [lowerR, WeightedShift.adjoint_apply_image]
  have hw : 0<W ke := by linarith [W_one_le ke]
  simp only [W_upR, increase, ite_eq_left (by linarith : 1<W ke+1), add_sub_cancel_right,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, map_div₀, map_add, map_one, Complex.conj_ofReal]
  have hw1 : (W ke:ℂ)+1≠0 := by exact_mod_cast (by linarith : W ke+1≠0)
  field_simp

theorem raiseR_zero (j : Fin n) (x : JointFock n) (ke : NumberIndex n × NumberIndex n)
    (hk : ke.2 j=0) : raiseR j x ke=0 := by
  change _*((lowerR j).adjoint x ke)=0
  rw [lowerR, WeightedShift.adjoint_apply_outside]
  · exact mul_zero _
  · intro ab he
    have hh := congrArg (fun q => q.2 j) he
    simp only [upR, up_same, hk] at hh
    omega
end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

theorem inverse_selfAdjoint : IsSelfAdjoint (inverse (n:=n)) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  apply HasSum.unique (lp.hasSum_inner (𝕜:=ℂ) (inverse x) y)
  convert! lp.hasSum_inner (𝕜:=ℂ) x (inverse y) using 1
  ext ke
  simp only [inverse_apply, RCLike.inner_apply, map_mul, map_inv₀, Complex.conj_ofReal]
  ring

theorem inverse_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) :
    inverse ∘L (beamUnitary (n:=n) η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L inverse :=
  radial_covariance η hη (fun t => t⁻¹) 1 (by norm_num) inverse_bound

theorem slice_raiseR_up (j : Fin n) (x : JointFock n) (e : NumberIndex n) :
    slice (raiseR j x) (up j e)=(Real.sqrt ((e j:ℝ)+1):ℂ) • slice (inverse x) e := by
  apply lp.ext
  funext k
  change raiseR j x (upR j (k,e))=_
  rw [raiseR_up]
  simp only [slice_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, inverse_apply,
    div_eq_mul_inv]
  push_cast
  ring

theorem slice_raiseR_zero (j : Fin n) (x : JointFock n) (e : NumberIndex n)
    (he : e j=0) : slice (raiseR j x) e=0 := by
  apply lp.ext
  funext k
  exact raiseR_zero j x (k,e) he

theorem discarded_commutator_operator (j : Fin n) (Z : Fock n →L[ℂ] Fock n) :
    inverse ∘L liftLeft Z ∘L raiseR j =
      (lowerR j).adjoint ∘L liftLeft Z ∘L inverse := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  by_cases he : 0<e j
  · obtain ⟨f,hf⟩ : ∃ f, e=up j f := ⟨down j e,(up_down j e he).symm⟩
    subst e
    change inverse (liftLeft Z (raiseR j x)) (k,up j f)=
      (lowerR j).adjoint (liftLeft Z (inverse x)) (upR j (k,f))
    rw [inverse_apply, liftLeft_apply]
    rw [slice_raiseR_up, map_smul]
    rw [lowerR, WeightedShift.adjoint_apply_image]
    simp only [show W (k,up j f)=W (k,f)+1 from W_upR j (k,f),
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, liftLeft_apply, Complex.ofReal_add,
      Complex.ofReal_one, Complex.ofReal_div, map_div₀, map_add, map_one, Complex.conj_ofReal]
    ring
  · have hz : e j=0 := Nat.eq_zero_of_not_pos he
    change _*Z (slice (raiseR j x) e) k=(lowerR j).adjoint (liftLeft Z (inverse x)) (k,e)
    rw [slice_raiseR_zero j x e hz, map_zero]
    rw [lowerR, WeightedShift.adjoint_apply_outside]
    · exact mul_zero _
    · intro ab hh
      have h := congrArg (fun q => q.2 j) hh
      simp only [upR, up_same, hz] at h
      omega

theorem discarded_commutator (j : Fin n) (Z : Fock n →L[ℂ] Fock n)
    (x y : JointFock n) :
    inner ℂ (inverse x) (liftLeft Z (raiseR j y))=
      inner ℂ (lowerR j x) (liftLeft Z (inverse y)) := by
  have hi : inner ℂ (inverse x) (liftLeft Z (raiseR j y))=
      inner ℂ x (inverse (liftLeft Z (raiseR j y))) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (inverse_selfAdjoint (n:=n))) x _
  rw [hi]
  have hh := congrArg (fun T : JointFock n →L[ℂ] JointFock n => T y)
    (discarded_commutator_operator j Z)
  change inverse (liftLeft Z (raiseR j y))=(lowerR j).adjoint (liftLeft Z (inverse y)) at hh
  rw [hh, ContinuousLinearMap.adjoint_inner_right]

theorem conjugate_inner (η : ℝ) (hη : η ∈ Set.Icc 0 1) (Z : Fock n →L[ℂ] Fock n)
    (x y : JointFock n) :
    inner ℂ x (conjugate η hη Z y)=inner ℂ (beamUnitary η hη x) (liftLeft Z (beamUnitary η hη y)) := by
  change inner ℂ x ((beamUnitary η hη).symm (liftLeft Z (beamUnitary η hη y)))=_
  rw [← (beamUnitary η hη).inner_map_map, (beamUnitary η hη).apply_symm_apply]

theorem covariance_lower_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    lowerL j (beamUnitary η hη x)=(Real.sqrt η:ℂ) • beamUnitary η hη (lowerL j x)+
      (Real.sqrt (1-η):ℂ) • beamUnitary η hη (lowerR j x) := by
  have hh := congrArg (fun T : JointFock n →L[ℂ] JointFock n => T x) (retained_covariance η hη j)
  change lowerL j (beamUnitary η hη x)=beamUnitary η hη ((Real.sqrt η:ℂ) • lowerL j x+(Real.sqrt (1-η):ℂ) • lowerR j x) at hh
  simpa only [map_add, map_smul] using hh

theorem covariance_raise_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    raiseL j (beamUnitary η hη x)=(Real.sqrt η:ℂ) • beamUnitary η hη (raiseL j x)+
      (Real.sqrt (1-η):ℂ) • beamUnitary η hη (raiseR j x) := by
  have hh := congrArg (fun T : JointFock n →L[ℂ] JointFock n => T x) (retained_creation_covariance η hη j)
  change raiseL j (beamUnitary η hη x)=beamUnitary η hη ((Real.sqrt η:ℂ) • raiseL j x+(Real.sqrt (1-η):ℂ) • raiseR j x) at hh
  simpa only [map_add, map_smul] using hh

theorem covariance_inverse_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (x : JointFock n) :
    inverse (beamUnitary η hη x)=beamUnitary η hη (inverse x) :=
  congrArg (fun T : JointFock n →L[ℂ] JointFock n => T x) (inverse_covariance η hη)

theorem covariance_discarded_lower_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    lowerR j (beamUnitary η hη x)=-(Real.sqrt (1-η):ℂ) • beamUnitary η hη (lowerL j x)+
      (Real.sqrt η:ℂ) • beamUnitary η hη (lowerR j x) := by
  have hh := congrArg (fun T : JointFock n →L[ℂ] JointFock n => T x) (discarded_covariance η hη j)
  change lowerR j (beamUnitary η hη x)=beamUnitary η hη (-(Real.sqrt (1-η):ℂ) • lowerL j x+(Real.sqrt η:ℂ) • lowerR j x) at hh
  simpa only [map_add, map_smul] using hh

theorem covariance_discarded_raise_apply (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    raiseR j (beamUnitary η hη x)=-(Real.sqrt (1-η):ℂ) • beamUnitary η hη (raiseL j x)+
      (Real.sqrt η:ℂ) • beamUnitary η hη (raiseR j x) := by
  have hh := congrArg (fun T : JointFock n →L[ℂ] JointFock n => T x) (discarded_creation_covariance η hη j)
  change raiseR j (beamUnitary η hη x)=beamUnitary η hη (-(Real.sqrt (1-η):ℂ) • raiseL j x+(Real.sqrt η:ℂ) • raiseR j x) at hh
  simpa only [map_add, map_smul] using hh

theorem two_port_algebra (c s r a b A B C D : ℂ) (hs : c^2+s^2=1)
    (hr : r=c^2*a+s^2*b) (hd : -s*A+c*B= -s*C+c*D) :
    (r+1)*(c*A+s*B)-r*(c*C+s*D)=
      c*((a+1)*A-a*C)+s*((b+1)*B-b*D) := by
  rw [hr]
  linear_combination (c*a*(A-C)+s*b*(B-D))*hs+c*s*(a-b)*hd

theorem physical_weak_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (a b : ℝ) (j : Fin n)
    (x y : JointFock n) (Z : Fock n →L[ℂ] Fock n) :
    weakL (η*a+(1-η)*b) j (beamUnitary η hη x) (beamUnitary η hη y) (liftLeft Z)=
      (Real.sqrt η:ℂ)*weakL a j x y (conjugate η hη Z)+
        (Real.sqrt (1-η):ℂ)*weakR b j x y (conjugate η hη Z) := by
  have hd := discarded_commutator j Z (beamUnitary η hη x) (beamUnitary η hη y)
  rw [covariance_inverse_apply, covariance_inverse_apply, covariance_discarded_lower_apply,
    covariance_discarded_raise_apply] at hd
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, map_neg, Complex.conj_ofReal, ← conjugate_inner] at hd
  unfold weakL weakR
  rw [covariance_lower_apply, covariance_raise_apply, covariance_inverse_apply, covariance_inverse_apply]
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal, ← conjugate_inner]
  apply two_port_algebra
  · have hc : (Real.sqrt η:ℂ)^2=(η:ℂ) := by exact_mod_cast Real.sq_sqrt hη.1
    have hs : (Real.sqrt (1-η):ℂ)^2=(1-η:ℂ) := by exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hη.2)
    rw [hc, hs]
    ring
  · norm_cast
    rw [Real.sq_sqrt hη.1, Real.sq_sqrt (sub_nonneg.mpr hη.2)]
  · exact hd.symm
end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

theorem tensorPreimage_apply (x y : Fock n) (k e : NumberIndex n) :
    tensorPreimage x y (k,e)=(W (k,e):ℂ)*inverseWeight 3 x k*inverseWeight 3 y e := by
  have hk : (numberWeight k:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le k] : numberWeight k≠0)
  have he : (numberWeight e:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le e] : numberWeight e≠0)
  simp only [tensorPreimage, lp.coeFn_sub, lp.coeFn_add, Pi.sub_apply, Pi.add_apply,
    tensor_apply, inverseWeight_apply, W]
  push_cast
  field_simp

theorem tensorPreimage_inverse (x y : Fock n) :
    inverse (tensorPreimage x y)=tensor (inverseWeight 3 x) (inverseWeight 3 y) := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  rw [inverse_apply, tensorPreimage_apply, tensor_apply]
  have hw : (W (k,e):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (k,e)] : W (k,e)≠0)
  field_simp

theorem square_add_summable {I E : Type*} [NormedAddCommGroup E] {x y : I → E}
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2)) :
    Summable (fun i => ‖x i+y i‖^2) := by
  have hmx : Memℓp x 2 := by
    simpa only [memℓp_gen_iff (by norm_num : (0:ℝ)<(2:ENNReal).toReal), ENNReal.toReal_ofNat, Real.rpow_two] using hx
  have hmy : Memℓp y 2 := by
    simpa only [memℓp_gen_iff (by norm_num : (0:ℝ)<(2:ENNReal).toReal), ENNReal.toReal_ofNat, Real.rpow_two] using hy
  simpa only [memℓp_gen_iff (by norm_num : (0:ℝ)<(2:ENNReal).toReal), ENNReal.toReal_ofNat, Real.rpow_two, Pi.add_apply] using hmx.add hmy

theorem tensorPreimage_summable {I J : Type*} (x : I → Fock n) (y : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2)) :
    Summable (fun ij : I × J => ‖tensorPreimage (x ij.1) (y ij.2)‖^2) := by
  have ht (a b : ℕ) : Summable (fun ij : I × J => ‖tensor (inverseWeight a (x ij.1)) (inverseWeight b (y ij.2))‖^2) := by
    simpa only [tensor_norm_sq] using
      (CrossEnsemble.applied_summable hx (inverseWeight a)).mul_of_nonneg
        (CrossEnsemble.applied_summable hy (inverseWeight b)) (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  have hn : Summable (fun ij : I × J => ‖-tensor (inverseWeight 3 (x ij.1)) (inverseWeight 3 (y ij.2))‖^2) := by
    simpa only [norm_neg] using ht 3 3
  simpa only [tensorPreimage, sub_eq_add_neg] using square_add_summable (square_add_summable (ht 2 3) (ht 3 2)) hn
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

end

variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

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

theorem pairing_conditionalLeft (u v : I → H A) (y : J → H B)
    (hu : Summable (fun i => ‖u i‖^2)) (hv : Summable (fun i => ‖v i‖^2))
    (hy : HasSum (fun j => ‖y j‖^2) 1) (Z : H (A × B) →L[ℂ] H (A × B)) :
    CrossEnsemble.pairing (fun ij : I × J => tensor (u ij.1) (y ij.2))
      (fun ij : I × J => tensor (v ij.1) (y ij.2)) Z=
      CrossEnsemble.pairing u v (conditionalLeft y hy Z) := by
  have hh := (CrossEnsemble.pairing_summable (tensorFamily_summable u y hu hy.summable)
    (tensorFamily_summable v y hv hy.summable) Z).hasSum.prod_fiberwise
      (fun i => conditionalLeft_entry y hy Z (v i) (u i))
  exact hh.tsum_eq.symm

theorem pairing_conditionalRight (x : I → H A) (u v : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1)
    (hu : Summable (fun j => ‖u j‖^2)) (hv : Summable (fun j => ‖v j‖^2))
    (Z : H (A × B) →L[ℂ] H (A × B)) :
    CrossEnsemble.pairing (fun ij : I × J => tensor (x ij.1) (u ij.2))
      (fun ij : I × J => tensor (x ij.1) (v ij.2)) Z=
      CrossEnsemble.pairing u v (conditionalRight x hx Z) := by
  have hs := CrossEnsemble.pairing_summable (tensorFamily_summable x u hx.summable hu)
    (tensorFamily_summable x v hx.summable hv) Z
  have hh := hs.prod_symm.hasSum.prod_fiberwise
      (fun j => conditionalRight_entry x hx Z (v j) (u j))
  have he := (Equiv.prodComm J I).tsum_eq
    (fun ij : I × J => inner ℂ (tensor (x ij.1) (v ij.2)) (Z (tensor (x ij.1) (u ij.2))))
  change (∑' ji : J × I, inner ℂ (tensor (x ji.swap.1) (v ji.swap.2))
    (Z (tensor (x ji.swap.1) (u ji.swap.2))))=_ at he
  rw [he] at hh
  exact hh.tsum_eq.symm
end TensorLp

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

theorem weakL_summable (r : ℝ) (j : Fin n) (x y : I → JointFock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (T : JointFock n →L[ℂ] JointFock n) :
    Summable (fun i => weakL r j (x i) (y i) T) :=
  ((CrossEnsemble.pairing_summable (CrossEnsemble.applied_summable hy inverse)
    (CrossEnsemble.applied_summable hx (lowerL j)) T).mul_left _).sub
  ((CrossEnsemble.pairing_summable (CrossEnsemble.applied_summable hy (raiseL j))
    (CrossEnsemble.applied_summable hx inverse) T).mul_left _)

theorem weakR_summable (r : ℝ) (j : Fin n) (x y : I → JointFock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (T : JointFock n →L[ℂ] JointFock n) :
    Summable (fun i => weakR r j (x i) (y i) T) :=
  ((CrossEnsemble.pairing_summable (CrossEnsemble.applied_summable hy inverse)
    (CrossEnsemble.applied_summable hx (lowerR j)) T).mul_left _).sub
  ((CrossEnsemble.pairing_summable (CrossEnsemble.applied_summable hy (raiseR j))
    (CrossEnsemble.applied_summable hx inverse) T).mul_left _)

theorem weakL_product (r : ℝ) (j : Fin n) (x : I → Fock n) (y : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2))
    (hy : HasSum (fun j => ‖inverseWeight 3 (y j)‖^2) 1)
    (Z : JointFock n →L[ℂ] JointFock n) :
    (∑' ij : I × J, weakL r j (tensorPreimage (x ij.1) (y ij.2))
      (tensorPreimage (x ij.1) (y ij.2)) Z)=
        singleWeak r j x (conditionalLeft (fun j => inverseWeight 3 (y j)) hy Z) := by
  have hi := CrossEnsemble.applied_summable hx (inverseWeight 3)
  have hl := CrossEnsemble.applied_summable hx (sandwich 0 3 (by omega) j)
  have hr := CrossEnsemble.applied_summable hx (creationSandwich 0 3 (by omega) j)
  simp only [weakL, tensorPreimage_lowerL, tensorPreimage_inverse, tensorPreimage_raiseL]
  rw [Summable.tsum_sub (((CrossEnsemble.pairing_summable (tensorFamily_summable _ _ hi hy.summable)
    (tensorFamily_summable _ _ hl hy.summable) Z).mul_left _))
    (((CrossEnsemble.pairing_summable (tensorFamily_summable _ _ hr hy.summable)
    (tensorFamily_summable _ _ hi hy.summable) Z).mul_left _)), tsum_mul_left, tsum_mul_left]
  change (r+1:ℂ)*CrossEnsemble.pairing _ _ Z-(r:ℂ)*CrossEnsemble.pairing _ _ Z=_
  rw [pairing_conditionalLeft _ _ _ hi hl hy, pairing_conditionalLeft _ _ _ hr hi hy]
  rfl

theorem weakR_product (r : ℝ) (j : Fin n) (x : I → Fock n) (y : J → Fock n)
    (hx : HasSum (fun i => ‖inverseWeight 3 (x i)‖^2) 1)
    (hy : Summable (fun j => ‖y j‖^2))
    (Z : JointFock n →L[ℂ] JointFock n) :
    (∑' ij : I × J, weakR r j (tensorPreimage (x ij.1) (y ij.2))
      (tensorPreimage (x ij.1) (y ij.2)) Z)=
        singleWeak r j y (conditionalRight (fun i => inverseWeight 3 (x i)) hx Z) := by
  have hi := CrossEnsemble.applied_summable hy (inverseWeight 3)
  have hl := CrossEnsemble.applied_summable hy (sandwich 0 3 (by omega) j)
  have hr := CrossEnsemble.applied_summable hy (creationSandwich 0 3 (by omega) j)
  simp only [weakR, tensorPreimage_lowerR, tensorPreimage_inverse, tensorPreimage_raiseR]
  rw [Summable.tsum_sub (((CrossEnsemble.pairing_summable (tensorFamily_summable _ _ hx.summable hi)
    (tensorFamily_summable _ _ hx.summable hl) Z).mul_left _))
    (((CrossEnsemble.pairing_summable (tensorFamily_summable _ _ hx.summable hr)
    (tensorFamily_summable _ _ hx.summable hi) Z).mul_left _)), tsum_mul_left, tsum_mul_left]
  change (r+1:ℂ)*CrossEnsemble.pairing _ _ Z-(r:ℂ)*CrossEnsemble.pairing _ _ Z=_
  rw [pairing_conditionalRight _ _ _ hx hi hl, pairing_conditionalRight _ _ _ hx hr hi]
  rfl

theorem product_weak_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1) (a b : ℝ) (j : Fin n)
    (x : I → Fock n) (y : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hxn : HasSum (fun i => ‖inverseWeight 3 (x i)‖^2) 1)
    (hyn : HasSum (fun j => ‖inverseWeight 3 (y j)‖^2) 1)
    (Z : Fock n →L[ℂ] Fock n) :
    (∑' ij : I × J, weakL (η*a+(1-η)*b) j
      (beamUnitary η hη (tensorPreimage (x ij.1) (y ij.2)))
      (beamUnitary η hη (tensorPreimage (x ij.1) (y ij.2))) (liftLeft Z))=
    (Real.sqrt η:ℂ)*singleWeak a j x (conditionalLeft (fun j => inverseWeight 3 (y j)) hyn (conjugate η hη Z))+
    (Real.sqrt (1-η):ℂ)*singleWeak b j y (conditionalRight (fun i => inverseWeight 3 (x i)) hxn (conjugate η hη Z)) := by
  have hs := tensorPreimage_summable x y hx hy
  simp only [physical_weak_covariance]
  rw [Summable.tsum_add ((weakL_summable a j _ _ hs hs _).mul_left _)
    ((weakR_summable b j _ _ hs hs _).mul_left _), tsum_mul_left, tsum_mul_left,
    weakL_product a j x y hx hyn, weakR_product b j x y hxn hy]
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
theorem slice_family_summable (x : I → H (A × B)) (hx : Summable (fun i => ‖x i‖^2)) :
    Summable (fun ie : I × B => ‖slice (x ie.1) ie.2‖^2) := by
  apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
  refine ⟨fun i => (hasSum_slice_norm_sq (x i)).summable, ?_⟩
  simpa only [(hasSum_slice_norm_sq _).tsum_eq] using hx

theorem pairing_liftLeft (x y : I → H (A × B))
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (Z : H A →L[ℂ] H A) :
    CrossEnsemble.pairing x y (liftLeft Z)=
      CrossEnsemble.pairing (fun ie : I × B => slice (x ie.1) ie.2)
        (fun ie : I × B => slice (y ie.1) ie.2) Z := by
  have hh := (CrossEnsemble.pairing_summable (slice_family_summable x hx)
    (slice_family_summable y hy) Z).hasSum.prod_fiberwise
      (fun i => by simpa only [slice_liftLeft] using hasSum_slice_inner (y i) (liftLeft Z (x i)))
  exact hh.tsum_eq
end TensorLp

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end CrossEnsemble

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

theorem lowerL_inverse_apply (j : Fin n) (x : JointFock n) (k e : NumberIndex n) :
    lowerL j x (k,e)=(Real.sqrt ((k j:ℝ)+1):ℂ)*inverse x (up j k,e) := by
  simp only [lowerL_apply, inverse_apply,
    show W (up j k,e)=W (k,e)+1 from W_upL j (k,e)]
  push_cast
  rw [div_eq_mul_inv, mul_assoc]
  rfl

theorem single_lower_inverse_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    sandwich 0 3 (by omega) j x k=(Real.sqrt ((k j:ℝ)+1):ℂ)*inverseWeight 3 x (up j k) := by
  simp only [sandwich_apply, coefficient, pow_zero, one_mul, inverseWeight_apply]
  push_cast
  ring

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

theorem defectVector_pairing (r : ℝ) (hr : 0<r) (p : J → ℝ) (hp : ∀ j, 0<p j)
    (d : J × J → ℂ) (hd) (z : J × J → ℂ)
    (hz : Summable (fun a : J × J => metricCoefficient r (p a.1) (p a.2)*‖z a‖^2)) :
    HasSum (fun a : J × J => (defectCoefficient r (p a.1) (p a.2):ℂ)*conj (d a)*z a)
      (inner ℂ (defectVector r hr p hp d hd)
        (weightedVector (fun a => metricCoefficient r (p a.1) (p a.2)) z hz
          (fun a => (metricCoefficient_pos hr (hp a.1) (hp a.2)).le))) := by
  have hh := lp.hasSum_inner (𝕜 := ℂ) (defectVector r hr p hp d hd)
    (weightedVector (fun a => metricCoefficient r (p a.1) (p a.2)) z hz
      (fun a => (metricCoefficient_pos hr (hp a.1) (hp a.2)).le))
  convert! hh using 1
  ext a
  simp only [defectVector_apply, weightedVector_apply, RCLike.inner_apply,
    map_mul, Complex.ofReal_div, map_div₀, Complex.conj_ofReal]
  have hn : (Real.sqrt (metricCoefficient r (p a.1) (p a.2)):ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (metricCoefficient_pos hr (hp a.1) (hp a.2))).ne'
  field_simp

end

section
variable {J : Type*}

end

open scoped ComplexConjugate
variable {J : Type*}

theorem diagonal_mean_summable (p : J → ℝ) (hp : ∀ j, 0≤p j) (hs : Summable p)
    (d : J × J → ℂ) (hd : Summable (fun a : J × J => p a.2*‖d a‖^2)) :
    Summable (fun j => (p j:ℂ)*d (j,j)) := by
  have hi : Function.Injective (fun j : J => (j,j)) := fun _ _ he => (Prod.mk.inj he).1
  have hh := hd.comp_injective hi
  apply Summable.of_norm_bounded (hh.add hs)
  intro j
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp j)]
  have hn : ‖d (j,j)‖≤‖d (j,j)‖^2+1 := by nlinarith [sq_nonneg (‖d (j,j)‖-1)]
  simpa only [mul_add, mul_one, Function.comp_apply] using mul_le_mul_of_nonneg_left hn (hp j)

theorem diagonal_centering (p : J → ℝ) (hs : HasSum p 1)
    (d : J × J → ℂ) (hd : Summable (fun j => (p j:ℂ)*d (j,j))) :
    HasSum (fun j => (p j:ℂ)*(d (j,j)-diagonalMean p d)) 0 := by
  have hh := hd.hasSum.sub ((Complex.hasSum_ofReal.mpr hs).mul_right (diagonalMean p d))
  simpa only [diagonalMean, Complex.ofReal_one, one_mul, sub_self, mul_sub] using hh

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

theorem lowering_weighted_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    lowering j (inverseWeight 2 x) k=
      (Real.sqrt ((k j:ℝ)+1):ℂ)*inverseWeight 3 x (up j k) := by
  rw [lowering_apply]
  change _ * ((inverseWeight 1 ∘L inverseWeight 2) x) _ = _
  rw [← inverseWeight_add]

theorem raising_weighted_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    raising j (inverseWeight 2 x) k=
      (Real.sqrt (k j:ℝ):ℂ)*inverseWeight 3 x (down j k) := by
  rcases index_cases j k with hk | ⟨l,rfl⟩
  · simp only [raising_zero j _ k hk, hk, Nat.cast_zero, Real.sqrt_zero,
      Complex.ofReal_zero, zero_mul]
  · rw [raising_up]
    change _ * ((inverseWeight 1 ∘L inverseWeight 2) x) _ = _
    rw [← inverseWeight_add, up_same, down_up]
    norm_cast
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

-- ---- from OAI.InformationTheory.PhotonNumber.BeamForms ----
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

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

theorem physical_ensemble_output (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (hτ : IsBeamSplitterOutput η ρ σ τ)
    (v : I → Fock n) (w : J → Fock n)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1)
    (hev : TraceEnsemble.operator v=ρ.op) (hew : TraceEnsemble.operator w=σ.op) :
    partialTrace (fun ij : I × J => beamUnitary η hη (tensor (v ij.1) (w ij.2)))=τ.op := by
  have hs : Summable (fun ij : I × J => ‖beamUnitary η hη (tensor (v ij.1) (w ij.2))‖^2) := by
    simpa only [LinearIsometryEquiv.norm_map] using (TraceEnsemble.hasSum_tensor_norm hv hw).summable
  apply entry_ext
  intro k l
  have he := partialTrace_entry hs k l
  simp only [beam_ensemble_entry η hη ρ σ v w hv hw hev hew] at he
  exact he.unique (hτ k l)

theorem cross_slice_eq_partialTrace (v : I → JointFock n) :
    CrossEnsemble.operator (fun ie : I × NumberIndex n => slice (v ie.1) ie.2)
      (fun ie : I × NumberIndex n => slice (v ie.1) ie.2)=partialTrace v := by
  exact (Equiv.prodComm I (NumberIndex n)).tsum_eq
    (fun ei => InnerProductSpace.rankOne ℂ (slice (v ei.2) ei.1) (slice (v ei.2) ei.1))

theorem physical_weighted_output (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (hτ : IsBeamSplitterOutput η ρ σ τ)
    (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hxn : HasSum (fun i => ‖inverseWeight 3 (x i)‖^2) 1)
    (hyn : HasSum (fun j => ‖inverseWeight 3 (y j)‖^2) 1)
    (hex : TraceEnsemble.operator (fun i => inverseWeight 3 (x i))=ρ.op)
    (hey : TraceEnsemble.operator (fun j => inverseWeight 3 (y j))=σ.op)
    (hez : TraceEnsemble.operator (fun k => inverseWeight 3 (z k))=τ.op) :
    CrossEnsemble.operator
      (fun ie : (I × J) × NumberIndex n => slice (inverse
        (beamUnitary η hη (tensorPreimage (x ie.1.1) (y ie.1.2)))) ie.2)
      (fun ie : (I × J) × NumberIndex n => slice (inverse
        (beamUnitary η hη (tensorPreimage (x ie.1.1) (y ie.1.2)))) ie.2)=
      CrossEnsemble.operator (fun k => inverseWeight 3 (z k)) (fun k => inverseWeight 3 (z k)) := by
  rw [cross_slice_eq_partialTrace (fun ij : I × J => inverse
      (beamUnitary η hη (tensorPreimage (x ij.1) (y ij.2))))]
  simp only [covariance_inverse_apply, tensorPreimage_inverse]
  change partialTrace _=TraceEnsemble.operator _
  rw [hez]
  exact physical_ensemble_output η hη ρ σ τ hτ (fun i => inverseWeight 3 (x i)) (fun j => inverseWeight 3 (y j)) hxn hyn hex hey

theorem physical_product_weak (η a b : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (hτ : IsBeamSplitterOutput η ρ σ τ)
    (j : Fin n) (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hz : Summable (fun k => ‖z k‖^2))
    (hxn : HasSum (fun i => ‖inverseWeight 3 (x i)‖^2) 1)
    (hyn : HasSum (fun j => ‖inverseWeight 3 (y j)‖^2) 1)
    (hex : TraceEnsemble.operator (fun i => inverseWeight 3 (x i))=ρ.op)
    (hey : TraceEnsemble.operator (fun j => inverseWeight 3 (y j))=σ.op)
    (hez : TraceEnsemble.operator (fun k => inverseWeight 3 (z k))=τ.op)
    (Z : Fock n →L[ℂ] Fock n) :
    singleWeak (η*a+(1-η)*b) j z Z=
      (Real.sqrt η:ℂ)*singleWeak a j x
        (conditionalLeft (fun j => inverseWeight 3 (y j)) hyn (conjugate η hη Z))+
      (Real.sqrt (1-η):ℂ)*singleWeak b j y
        (conditionalRight (fun i => inverseWeight 3 (x i)) hxn (conjugate η hη Z)) := by
  have hs := tensorPreimage_summable x y hx hy
  have hu : Summable (fun ij : I × J => ‖beamUnitary η hη (tensorPreimage (x ij.1) (y ij.2))‖^2) := by
    simpa only [LinearIsometryEquiv.norm_map] using hs
  have he := physical_weighted_output η hη ρ σ τ hτ x y z hxn hyn hex hey hez
  rw [← output_weak _ j _ z hu hz he Z]
  exact product_weak_covariance η hη a b j x y hx hy hxn hyn Z
end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end CrossEnsemble

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

theorem single_lower_third_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    sandwich 0 3 (by omega) j x k=
      (Real.sqrt ((k j:ℝ)+1):ℂ)*inverseWeight 3 x (up j k) := by
  simp only [sandwich_apply,coefficient,inverseWeight_apply,pow_zero,one_mul]
  push_cast
  ring

theorem single_raise_third_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    creationSandwich 0 3 (by omega) j x k=
      (if k j=0 then (0:ℂ) else (Real.sqrt (k j:ℝ):ℂ))*inverseWeight 3 x (down j k) := by
  by_cases hk : k j=0
  · rw [creationSandwich_zero _ _ _ _ _ k hk,ite_eq_left hk,zero_mul]
  · rw [ite_eq_right hk]
    obtain ⟨a,rfl⟩ : ∃ a,k=up j a := ⟨down j k,(up_down j k (Nat.pos_of_ne_zero hk)).symm⟩
    rw [creationSandwich_up,down_up,up_same]
    simp only [creationCoefficient,inverseWeight_apply,pow_zero,one_mul]
    push_cast
    ring

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

end BeamLadder

namespace EnsemblePullback

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {I : Type*}

end

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {I J : Type*}

end EnsemblePullback

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace CrossEnsemble
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {I : Type*}
end CrossEnsemble

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

end Annihilation

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I : Type*}

end BeamLadder

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I K : Type*}

end WeightedGenerator

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end BeamLadder

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I : Type*}

end CrossEnsemble

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Generator ----
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

namespace PhysicalGenerator
open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I : Type*}

end PhysicalGenerator

namespace QuantumTrace
theorem thermalWeight_number (n : ℕ) (r : ℝ) (k : Fin n → ℕ) :
    thermalWeight n r k=(r+1)⁻¹^n*(r/(r+1))^(∑ j,k j) := by
  simp [thermalWeight,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]

theorem thermalWeight_up {n : ℕ} (r : ℝ) (j : Fin n) (k : Fin n → ℕ) :
    thermalWeight n r (Annihilation.up j k)=r/(r+1)*thermalWeight n r k := by
  have hs : (∑ i,Annihilation.up j k i)=(∑ i,k i)+1 := by
    simp [Annihilation.up,Finset.sum_add_distrib]
  rw [thermalWeight_number,thermalWeight_number,hs,pow_succ]
  ring

theorem thermalWeight_balance {n : ℕ} (r : ℝ) (hr : 0<r) (j : Fin n) (k : Fin n → ℕ) :
    ((r+1:ℝ):ℂ)*(thermalWeight n r (Annihilation.up j k):ℂ)=
      (r:ℂ)*(thermalWeight n r k:ℂ) := by
  have h : (r+1)*thermalWeight n r (Annihilation.up j k)=r*thermalWeight n r k := by
    rw [thermalWeight_up]
    have hr1 : r+1≠0 := by positivity
    field_simp
  exact_mod_cast h
end QuantumTrace

namespace PhysicalGenerator

section
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ} {I : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I J K : Type*}

end PhysicalGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder

namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

theorem base_density :
    CrossEnsemble.operator (PhysicalGenerator.baseFamily X.vector) (PhysicalGenerator.baseFamily X.vector)=ρ.op :=
  X.density

end WeightedColumns

end EntropyPhotonNumber

namespace PhysicalGenerator
open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I J K : Type*}

theorem weak_pairing_hasSum {L : Type*} (b : HilbertBasis L ℂ (Fock n))
    (r : ℝ) (j : Fin n) (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun k => inner ℂ (b k) (Z (weakOperator r j x (b k)))) (singleWeak r j x Z) := by
  have hi := CrossEnsemble.applied_summable hx (inverseWeight 3)
  have hl := CrossEnsemble.applied_summable hx (sandwich 0 3 (by omega) j)
  have hr := CrossEnsemble.applied_summable hx (creationSandwich 0 3 (by omega) j)
  have hh := ((CrossEnsemble.pairing_trace b hi hl Z).mul_left (r+1:ℂ)).sub
    ((CrossEnsemble.pairing_trace b hr hi Z).mul_left (r:ℂ))
  unfold weakOperator
  simp only [smul_apply,sub_apply,map_sub,map_smul,inner_sub_right,inner_smul_right]
  exact hh

theorem weakOperator_affine (r : ℝ) (j : Fin n) (c d : ℂ)
    (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hz : Summable (fun k => ‖z k‖^2))
    (he : CrossEnsemble.operator (baseFamily z) (baseFamily z)=
      c • CrossEnsemble.operator (baseFamily x) (baseFamily x)+
      d • CrossEnsemble.operator (baseFamily y) (baseFamily y)) :
    weakOperator r j z=c • weakOperator r j x+d • weakOperator r j y := by
  apply entry_ext
  intro k l
  have e (T U : Fock n →L[ℂ] Fock n) (a b : NumberIndex n) :
      entry (c • T+d • U) a b=c*entry T a b+d*entry U a b := by
    simp only [entry,add_apply,smul_apply,inner_add_right,inner_smul_right]
  rw [weakOperator_entry r j z hz,e,weakOperator_entry r j x hx,weakOperator_entry r j y hy,he]
  rw [e,e]
  ring

theorem weak_pairing_affine (r : ℝ) (j : Fin n) (c d : ℂ)
    (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hz : Summable (fun k => ‖z k‖^2))
    (he : CrossEnsemble.operator (baseFamily z) (baseFamily z)=
      c • CrossEnsemble.operator (baseFamily x) (baseFamily x)+
      d • CrossEnsemble.operator (baseFamily y) (baseFamily y)) (Z : Fock n →L[ℂ] Fock n) :
    singleWeak r j z Z=c*singleWeak r j x Z+d*singleWeak r j y Z := by
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  apply (weak_pairing_hasSum bas r j z hz Z).unique
  rw [weakOperator_affine r j c d x y z hx hy hz he]
  simpa only [add_apply,smul_apply,map_add,map_smul,inner_add_right,inner_smul_right] using
    ((weak_pairing_hasSum bas r j x hx Z).mul_left c).add ((weak_pairing_hasSum bas r j y hy Z).mul_left d)

theorem weakOperator_zero_of_geometric_diagonal (r : ℝ) (p : NumberIndex n → ℝ)
    (hb : ∀ j k, (r+1:ℂ)*(p (up j k):ℂ)=(r:ℂ)*(p k:ℂ))
    (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (he : ∀ k l, entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) k l=
      if k=l then (p k:ℂ) else 0) (j : Fin n) : weakOperator r j x=0 := by
  apply entry_ext
  intro k l
  rw [weakOperator_entry r j x hx,he,he]
  simp only [entry, zero_apply, inner_zero_right]
  by_cases hk : k=up j l
  · subst k
    have hc : raiseCoefficient j (up j l)=conj (lowerCoefficient j l) := by
      simp [raiseCoefficient, lowerCoefficient, up_same]
    rw [ite_eq_left rfl,down_up,ite_eq_left rfl,hc]
    calc
      _ = conj (lowerCoefficient j l)*((r+1:ℂ)*(p (up j l):ℂ)-(r:ℂ)*(p l:ℂ)) := by ring
      _ = 0 := by rw [hb]; ring
  · rw [ite_eq_right hk,mul_zero,zero_sub]
    by_cases hz : k j=0
    · simp [raiseCoefficient,hz]
    · have hd : down j k≠l := by
        intro h
        apply hk
        rw [← h,up_down j k (Nat.pos_of_ne_zero hz)]
      rw [ite_eq_right hd,mul_zero,neg_zero]

theorem weak_thermal_pairing_zero (r : ℝ) (hr : 0<r)
    (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (he : ∀ k l, entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) k l=
      if k=l then (thermalWeight n r k:ℂ) else 0) (j : Fin n) (Z : Fock n →L[ℂ] Fock n) :
    singleWeak r j x Z=0 := by
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hh := weak_pairing_hasSum bas r j x hx Z
  have he0 := weakOperator_zero_of_geometric_diagonal r (thermalWeight n r) (fun j k => by simpa only [Complex.ofReal_add, Complex.ofReal_one] using thermalWeight_balance r hr j k) x hx he j
  have hzero : HasSum (fun _ : NumberIndex n => (0:ℂ)) 0 := hasSum_zero
  have hz : HasSum (fun _ : NumberIndex n => (0:ℂ)) (singleWeak r j x Z) := by
    simpa only [he0,zero_apply,map_zero,inner_zero_right] using hh
  exact hz.unique hzero
end PhysicalGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder TensorLp
namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

theorem thermal_weak_zero (r : ℝ) (hr : 0<r)
    (he : ∀ k l, entry ρ.op k l=if k=l then (thermalWeight n r k:ℂ) else 0)
    (j : Fin n) (Z : Fock n →L[ℂ] Fock n) : singleWeak r j X.vector Z=0 := by
  apply PhysicalGenerator.weak_thermal_pairing_zero r hr X.vector X.summable
  intro k l
  rw [X.base_density,he]
end WeightedColumns

end EntropyPhotonNumber

namespace KrausBounded
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
end KrausBounded

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}
theorem conjugate_one (η : ℝ) (hη : η ∈ Set.Icc 0 1) :
    conjugate (n:=n) η hη 1=1 := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [conjugate,liftLeft_one,ContinuousLinearMap.comp_apply,one_apply_eq_self]
  change (beamUnitary η hη).symm (beamUnitary η hη x)=x
  exact (beamUnitary η hη).symm_apply_apply x
end BeamLadder

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder TensorLp
namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

theorem expectation_one : X.expectation 1=1 := by
  have hh := X.normalized.mapL Complex.ofRealCLM
  unfold expectation CrossEnsemble.pairing
  have hs : HasSum (fun i => inner ℂ (inverseWeight 3 (X.vector i))
      ((1 : Fock n →L[ℂ] Fock n) (inverseWeight 3 (X.vector i)))) (1:ℂ) := by
    convert! hh using 1
    ext i
    simp only [one_apply_eq_self,inner_self_eq_norm_sq_to_K,Complex.ofRealCLM_apply,Complex.ofReal_pow]
    rfl
  exact hs.tsum_eq

theorem rawSlice_one (η : ℝ) (hη : η ∈ Set.Icc 0 1) : X.rawSlice η hη 1=1 := by
  simp only [rawSlice,conjugate_one,conditionalLeft,KrausBounded.dual_one]

theorem rawSliceRight_one (η : ℝ) (hη : η ∈ Set.Icc 0 1) : X.rawSliceRight η hη 1=1 := by
  simp only [rawSliceRight,conjugate_one,conditionalRight,KrausBounded.dual_one]

end WeightedColumns

end EntropyPhotonNumber

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

end BeamLadder

namespace EntropyPhotonNumber

namespace WeightedColumns
open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

theorem weakMean_reference (a b : ℝ) (j : Fin n) : X.weakMean a j=X.weakMean b j := by
  rw [X.weakMean_trace,X.weakMean_trace]
end WeightedColumns

end EntropyPhotonNumber

end

end OAI

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

theorem annihilation_mean_summable (j : Fin n) :
    Summable (fun r => (G.probability r:ℂ)*G.annihilationMatrix j (r,r)) := by
  apply diagonal_mean_summable G.probability (fun r => (G.probability_pos r).le)
    G.probability_sum.summable
  have hh := nonlog_summable G.basis G.spectralColumns G.spectralColumns_summable j false
  simpa only [spectralGain_lowering_sq G.basis G.probability G.probability_pos,
    annihilationMatrix] using hh

theorem centeredMatrix_mean_zero (j : Fin n) :
    HasSum (fun r => (G.probability r:ℂ)*G.centeredMatrix j (r,r)) 0 := by
  classical
  simpa only [centeredMatrix, centeredEntry, ↓reduceIte, annihilationMean, annihilationMatrix]
    using diagonal_centering G.probability G.probability_sum
      (G.annihilationMatrix j) (G.annihilation_mean_summable j)

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
 theorem tensorFamily_norm (x : I → H A) (y : J → H B) (α β : ℝ)
    (hx : HasSum (fun i => ‖x i‖^2) α) (hy : HasSum (fun j => ‖y j‖^2) β) :
    HasSum (fun ij : I × J => ‖tensor (x ij.1) (y ij.2)‖^2) (α*β) := by
  have hs := hx.summable.mul_of_nonneg hy.summable (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  simpa only [tensor_norm_sq] using hx.mul hy hs

end TensorLp

namespace KrausBounded
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

end KrausBounded

namespace EnsembleL2
open scoped BigOperators ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
end EnsembleL2

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J : Type*}

end TensorLp

namespace KrausBounded

section
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

end

open scoped BigOperators ComplexConjugate
variable {E H K I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace E] [CompleteSpace H]

end KrausBounded

namespace TensorLp
open scoped BigOperators ComplexConjugate
variable {A B I J K E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

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

end EntropyPhotonNumber

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

theorem powerMoment_eq {n : ℕ} (m : ℕ) (ρ : State n) :
    powerMoment m ρ = ∑' k, ENNReal.ofReal ((1+(totalNumber k : ℝ))^m*(entry ρ.op k k).re) := by
  unfold powerMoment matrixMoment
  congr 1
  funext k
  rw [ENNReal.ofReal_mul (pow_nonneg (by positivity) _),
    ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_one, ENNReal.ofReal_natCast]
  rfl

theorem finiteMoment_iff {n : ℕ} (m : ℕ) (ρ : State n) :
    FiniteMoment m ρ ↔ powerMoment m ρ < ⊤ := by
  rw [powerMoment_eq]
  have hp (k : NumberIndex n) : 0 ≤ (1+(totalNumber k : ℝ))^m*(entry ρ.op k k).re :=
    mul_nonneg (pow_nonneg (by positivity) _) (ρ.positive.re_inner_nonneg_right _)
  constructor
  · intro h
    exact h.tsum_ofReal_lt_top
  · intro h
    have hs := ENNReal.summable_toReal h.ne
    change Summable (fun k => (1+(totalNumber k : ℝ))^m*(entry ρ.op k k).re)
    simpa only [ENNReal.toReal_ofReal (hp _)] using hs

theorem beamOutput_finiteMoment {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) {m : ℕ} {ρA ρB : State n}
    (hA : FiniteMoment m ρA) (hB : FiniteMoment m ρB) : FiniteMoment m (beamOutput η hη ρA ρB) := by
  apply (finiteMoment_iff _ _).mpr
  exact (beamOutput_powerMoment_le η hη m ρA ρB).trans_lt
    (ENNReal.mul_lt_top ((finiteMoment_iff _ _).mp hA) ((finiteMoment_iff _ _).mp hB))

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
end Space

end ThermalSpectral

namespace ThermalMetric
open EntropyPhotonNumber DiagonalForms.System

end ThermalMetric

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace CrossEnsemble
open scoped ComplexConjugate
variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem pairing_sub_right (u v w : I → E) (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun i => ‖w i‖^2))
    (c : ℂ) (Z : E →L[ℂ] E) :
    pairing u (fun i => v i-c • w i) Z=pairing u v Z-conj c*pairing u w Z := by
  simp only [pairing, inner_sub_left, inner_smul_left]
  rw [(pairing_summable hu hv Z).tsum_sub ((pairing_summable hu hw Z).mul_left (conj c)), tsum_mul_left]

omit [CompleteSpace E] in
theorem pairing_sub_left (u v w : I → E) (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun i => ‖w i‖^2))
    (c : ℂ) (Z : E →L[ℂ] E) :
    pairing (fun i => u i-c • v i) w Z=pairing u w Z-c*pairing v w Z := by
  simp only [pairing, map_sub, map_smul, inner_sub_right, inner_smul_right]
  rw [(pairing_summable hu hw Z).tsum_sub ((pairing_summable hv hw Z).mul_left c), tsum_mul_left]
end CrossEnsemble

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation BeamLadder ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} {J : Type*}

theorem centeredLadder_lower (j : Fin n) (μ : ℂ) (x : Fock n) :
    centeredLadder j μ false x=sandwich 0 3 (by omega) j x-μ • inverseWeight 3 x := by
  have hw : inverseWeight 1 (inverseWeight 2 x)=inverseWeight 3 x := by
    change (inverseWeight 1 ∘L inverseWeight 2) x=_
    rw [← inverseWeight_add]
  simp only [centeredLadder, Bool.false_eq_true, ↓reduceIte, ContinuousLinearMap.comp_apply,
    sub_apply, smul_apply, hw]
  congr 1
  ext k
  rw [lowering_weighted_apply, single_lower_third_apply]

theorem centeredLadder_raise (j : Fin n) (μ : ℂ) (x : Fock n) :
    centeredLadder j μ true x=creationSandwich 0 3 (by omega) j x-conj μ • inverseWeight 3 x := by
  have hw : inverseWeight 1 (inverseWeight 2 x)=inverseWeight 3 x := by
    change (inverseWeight 1 ∘L inverseWeight 2) x=_
    rw [← inverseWeight_add]
  simp only [centeredLadder, ↓reduceIte, ContinuousLinearMap.comp_apply, sub_apply, smul_apply, hw]
  congr 1
  ext k
  rw [raising_weighted_apply, single_raise_third_apply]
  by_cases hk : k j=0
  · simp only [hk, Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero, zero_mul, ↓reduceIte]
  · rw [ite_eq_right hk]

theorem weakDefect_uncentered (t : ℝ) (x : J → Fock n)
    (hx : Summable (fun r => ‖x r‖^2)) (j : Fin n) (μ : ℂ) (Z : Fock n →L[ℂ] Fock n) :
    weakDefect t x j μ Z=singleWeak t j x Z-conj μ*
      CrossEnsemble.pairing (fun r => inverseWeight 3 (x r)) (fun r => inverseWeight 3 (x r)) Z := by
  have hi := CrossEnsemble.applied_summable hx (inverseWeight 3)
  have hl := CrossEnsemble.applied_summable hx (sandwich 0 3 (by omega) j)
  have hr := CrossEnsemble.applied_summable hx (creationSandwich 0 3 (by omega) j)
  simp only [weakDefect, centeredLadder_lower, centeredLadder_raise]
  rw [CrossEnsemble.pairing_sub_right _ _ _ hi hl hi,
    CrossEnsemble.pairing_sub_left _ _ _ hr hi hi]
  unfold singleWeak
  ring
end WeightedGenerator

namespace ThermalSpectral.Space
open EntropyPhotonNumber Annihilation WeightedGenerator ThermalMetric
open scoped ComplexConjugate
variable {n : ℕ} (S : Space (Fock n))

theorem defectFunctional_observable (x : S.I → Fock n)
    (hx : Summable (fun r => ‖x r‖^2))
    (hi : ∀ r, inverseWeight 3 (x r)=(Real.sqrt (S.p r):ℂ) • S.basis r)
    (j : Fin n) (μ : ℂ)
    (hd : Summable (fun a : S.I × S.I =>
      (1-frequency S.r (S.p a.1) (S.p a.2))*defectCoefficient S.r (S.p a.1) (S.p a.2)*
        ‖centeredEntry S.basis S.p x j μ a.1 a.2‖^2)) (Z : Fock n →L[ℂ] Fock n) :
    defectFunctional S.r S.rpos S.p S.pos (fun a => centeredEntry S.basis S.p x j μ a.1 a.2) hd
        (S.observable Z)=weakDefect S.r x j μ Z := by
  exact (defectVector_pairing S.r S.rpos S.p S.pos _ hd
    (fun a => inner ℂ (S.basis a.1) (Z (S.basis a.2)))
    (observable_summable S.basis S.p S.pos S.sum.summable S.r S.rpos Z)).unique
      (weakDefect_spectral S.basis S.p S.pos x hx hi S.r j μ Z)

theorem defectFunctional_one (d : S.I × S.I → ℂ) (hd)
    (hc : HasSum (fun j => (S.p j:ℂ)*d (j,j)) 0) :
    defectFunctional S.r S.rpos S.p S.pos d hd (S.observable 1)=0 := by
  have hh := defectVector_mem_centeredSpace S.r S.rpos S.p S.pos S.sum.summable d hd hc
  change inner ℂ (identityVector S.r S.rpos S.p S.pos S.sum.summable)
    (defectVector S.r S.rpos S.p S.pos d hd)=0 at hh
  change inner ℂ (defectVector S.r S.rpos S.p S.pos d hd) (S.observable 1)=0
  have he : S.observable 1=identityVector S.r S.rpos S.p S.pos S.sum.summable :=
    observableMap_id S.basis S.p S.pos S.sum.summable S.r S.rpos
  rw [he, ← inner_conj_symm, hh, map_zero]

end ThermalSpectral.Space

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Contraction ----
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

namespace EnsembleL2

section
open scoped BigOperators ComplexConjugate
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end

open scoped BigOperators
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end EnsembleL2

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

end ThermalSpectral.Space

namespace EnsembleL2
open scoped ComplexConjugate
variable {E I J K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end EnsembleL2

namespace BKM
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
end BKM

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

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
end

section
open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end

open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
end BKM

namespace CenteredTests
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

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

theorem ambientDefect_observable (t : ℝ) (ht : 0<t) (j : Fin n) (Z : Fock n →L[ℂ] Fock n) :
    G.ambientDefect t ht j ((G.thermalSpace t ht).observable Z)=
      weakDefect t G.spectralColumns j (G.annihilationMean j) Z :=
  (G.thermalSpace t ht).defectFunctional_observable G.spectralColumns G.spectralColumns_summable
    G.spectralColumns_inverse j (G.annihilationMean j) (G.centeredMatrix_defect_summable t j) Z

theorem ambientDefect_one (t : ℝ) (ht : 0<t) (j : Fin n) :
    G.ambientDefect t ht j ((G.thermalSpace t ht).observable 1)=0 :=
  (G.thermalSpace t ht).defectFunctional_one (G.centeredMatrix j)
    (G.centeredMatrix_defect_summable t j) (G.centeredMatrix_mean_zero j)

theorem weakMean_eq_conj (t : ℝ) (ht : 0<t) (j : Fin n) :
    G.weightedColumns.weakMean t j=conj (G.annihilationMean j) := by
  have hz := G.ambientDefect_one t ht j
  rw [G.ambientDefect_observable, weakDefect_uncentered _ _ G.spectralColumns_summable] at hz
  change G.weightedColumns.weakMean t j-conj (G.annihilationMean j)*G.weightedColumns.expectation 1=0 at hz
  rw [G.weightedColumns.expectation_one, mul_one] at hz
  exact sub_eq_zero.mp hz

end EntropyPhotonNumber.SpectralLogData

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Minimum ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology _root_.Complex _root_.OAI.Complex Metric
open MeasureTheory Set Filter Topology _root_.Complex _root_.OAI.Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology _root_.Complex _root_.OAI.Complex MeasureTheory

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder TensorLp ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp BeamLadder
open scoped ComplexConjugate
variable {n : ℕ}

end

open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp
variable {n : ℕ}
end EntropyPhotonNumber

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

theorem output_lower_square (j : Fin n) (x : I → JointFock n) (z : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hz : Summable (fun j => ‖z j‖^2))
    (he : CrossEnsemble.operator (fun ie : I × NumberIndex n => slice (inverse (x ie.1)) ie.2)
        (fun ie : I × NumberIndex n => slice (inverse (x ie.1)) ie.2)=
      CrossEnsemble.operator (fun j => inverseWeight 3 (z j)) (fun j => inverseWeight 3 (z j))) :
    (∑' i, ‖lowerL j (x i)‖^2) = ∑' i, ‖sandwich 0 3 (by omega) j (z i)‖^2 := by
  have hi := CrossEnsemble.applied_summable hx inverse
  have hl := CrossEnsemble.applied_summable hx (lowerL j)
  have hzi := CrossEnsemble.applied_summable hz (inverseWeight 3)
  have hzl := CrossEnsemble.applied_summable hz (sandwich 0 3 (by omega) j)
  have his := slice_family_summable _ hi
  have hls := slice_family_summable _ hl
  have heL := CrossEnsemble.shifted_both_operator_eq _ _ _ _ his hls hzi hzl
    (up j) (fun k => (Real.sqrt ((k j:ℝ)+1):ℂ))
    (fun ie k => lowerL_inverse_apply j (x ie.1) k ie.2)
    (fun i k => single_lower_inverse_apply j (z i) k) he
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hp := CrossEnsemble.pairing_eq_of_operator_eq bas hls hls hzl hzl heL 1
  rw [← pairing_liftLeft _ _ hl hl, liftLeft_one] at hp
  have hh1 := (EnsembleL2.self_inner_hasSum (fun i => lowerL j (x i)) hl).tsum_eq
  have hh2 := (EnsembleL2.self_inner_hasSum (fun i => sandwich 0 3 (by omega) j (z i)) hzl).tsum_eq
  simpa only [CrossEnsemble.pairing,one_apply_eq_self,hh1,hh2,Complex.ofReal_inj] using hp
end BeamLadder

namespace EnsembleL2
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem real_smul_add_square (c d : ℝ) (x y : E) :
    ‖(c:ℂ) • x+(d:ℂ) • y‖^2=c^2*‖x‖^2+d^2*‖y‖^2+2*c*d*(inner ℂ x y).re := by
  rw [norm_add_sq (𝕜:=ℂ)]
  simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,
    inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  change _+2*((d:ℂ)*((c:ℂ)*inner ℂ x y)).re+_=_
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem real_smul_add_hasSum (c d : ℝ) (x y : I → E) (a b : ℝ) (v : ℂ)
    (hx : HasSum (fun i => ‖x i‖^2) a) (hy : HasSum (fun i => ‖y i‖^2) b)
    (hxy : HasSum (fun i => inner ℂ (x i) (y i)) v) :
    HasSum (fun i => ‖(c:ℂ) • x i+(d:ℂ) • y i‖^2) (c^2*a+d^2*b+2*c*d*v.re) := by
  simpa only [real_smul_add_square,Complex.reCLM_apply] using
    ((hx.mul_left (c^2)).add (hy.mul_left (d^2))).add
      ((hxy.mapL Complex.reCLM).mul_left (2*c*d))
end EnsembleL2

namespace TensorLp
variable {A B I J : Type*}
theorem tensorFamily_inner (x x' : I → H A) (y y' : J → H B)
    (hx : Summable (fun i => ‖x i‖^2)) (hx' : Summable (fun i => ‖x' i‖^2))
    (hy : Summable (fun j => ‖y j‖^2)) (hy' : Summable (fun j => ‖y' j‖^2))
    (a b : ℂ) (hleft : HasSum (fun i => inner ℂ (x i) (x' i)) a)
    (hright : HasSum (fun j => inner ℂ (y j) (y' j)) b) :
    HasSum (fun ij : I × J => inner ℂ (tensor (x ij.1) (y ij.2)) (tensor (x' ij.1) (y' ij.2))) (a*b) := by
  have hs := (EnsembleL2.inner_sum
    (fun ij : I × J => tensor (x ij.1) (y ij.2))
    (fun ij : I × J => tensor (x' ij.1) (y' ij.2))
    (tensorFamily_summable x y hx hy) (tensorFamily_summable x' y' hx' hy')).summable
  simp only [inner_tensor] at hs
  simpa only [inner_tensor] using hleft.mul hright hs
end TensorLp

namespace EntropyPhotonNumber.WeightedColumns
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} {ρ σ τ : State n}

theorem weakMean_hasSum (X : WeightedColumns ρ) (r : ℝ) (j : Fin n) :
    HasSum (fun i => inner ℂ (sandwich 0 3 (by omega) j (X.vector i))
      (inverseWeight 3 (X.vector i))) (X.weakMean r j) := by
  rw [X.weakMean_trace]
  exact (EnsembleL2.inner_sum _ _
    (CrossEnsemble.applied_summable X.summable (sandwich 0 3 (by omega) j))
    X.normalized.summable).summable.hasSum

theorem physical_lowerEnergy (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (r s : ℝ) (j : Fin n) (X : WeightedColumns ρ) (Y : WeightedColumns σ)
    (T : WeightedColumns τ) (hτ : IsBeamSplitterOutput η ρ σ τ) :
    T.lowerEnergy j=η*X.lowerEnergy j+(1-η)*Y.lowerEnergy j+
      2*Real.sqrt η*Real.sqrt (1-η)*(X.weakMean r j*conj (Y.weakMean s j)).re := by
  let xl := fun i => sandwich 0 3 (by omega) j (X.vector i)
  let yl := fun i => sandwich 0 3 (by omega) j (Y.vector i)
  let xb := fun i => inverseWeight 3 (X.vector i)
  let yb := fun i => inverseWeight 3 (Y.vector i)
  have hxl := CrossEnsemble.applied_summable X.summable (sandwich 0 3 (by omega) j)
  have hyl := CrossEnsemble.applied_summable Y.summable (sandwich 0 3 (by omega) j)
  have hmY : HasSum (fun i => inner ℂ (yb i) (yl i)) (conj (Y.weakMean s j)) := by
    convert! (Y.weakMean_hasSum s j).mapL Complex.conjCLE.toContinuousLinearMap using 1
    ext i
    exact (inner_conj_symm _ _).symm
  have hxy := tensorFamily_inner xl xb yb yl hxl X.normalized.summable
    Y.normalized.summable hyl (X.weakMean r j) (conj (Y.weakMean s j))
    (X.weakMean_hasSum r j) hmY
  have ha : HasSum (fun ij : X.Index × Y.Index => ‖tensor (xl ij.1) (yb ij.2)‖^2) (X.lowerEnergy j) := by
    simpa only [mul_one, lowerEnergy] using tensorFamily_norm xl yb _ _ hxl.hasSum Y.normalized
  have hb : HasSum (fun ij : X.Index × Y.Index => ‖tensor (xb ij.1) (yl ij.2)‖^2) (Y.lowerEnergy j) := by
    simpa only [one_mul, lowerEnergy] using tensorFamily_norm xb yl _ _ X.normalized hyl.hasSum
  have hh := EnsembleL2.real_smul_add_hasSum (Real.sqrt η) (Real.sqrt (1-η))
    (fun ij : X.Index × Y.Index => tensor (xl ij.1) (yb ij.2))
    (fun ij : X.Index × Y.Index => tensor (xb ij.1) (yl ij.2)) _ _ _ ha hb hxy
  rw [Real.sq_sqrt hη.1,Real.sq_sqrt (sub_nonneg.mpr hη.2)] at hh
  let v := fun ij : X.Index × Y.Index => beamUnitary η hη (tensorPreimage (X.vector ij.1) (Y.vector ij.2))
  have hv : Summable (fun ij => ‖v ij‖^2) := by
    simpa only [v,LinearIsometryEquiv.norm_map] using tensorPreimage_summable X.vector Y.vector X.summable Y.summable
  have he := physical_weighted_output η hη ρ σ τ hτ X.vector Y.vector T.vector
    X.normalized Y.normalized X.density Y.density T.density
  have ho := output_lower_square j v T.vector hv T.summable he
  change (∑' i, ‖sandwich 0 3 (by omega) j (T.vector i)‖^2)=_
  rw [← ho]
  convert! hh.tsum_eq using 1
  apply tsum_congr
  intro ij
  dsimp [v]
  rw [covariance_lower_apply,tensorPreimage_lowerL,tensorPreimage_lowerR,
    ← map_smul,← map_smul,← map_add,LinearIsometryEquiv.norm_map]
  rfl
end EntropyPhotonNumber.WeightedColumns

namespace EnsembleL2
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end EnsembleL2

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

end EntropyPhotonNumber.SpectralLogData

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}
end Annihilation

namespace EntropyPhotonNumber.WeightedColumns

section
open QuantumTrace Annihilation
variable {n : ℕ} {ρ : State n}

end

section
open QuantumTrace Annihilation
variable {n : ℕ}

theorem lowerEnergy_affine {ρ σ τ : State n} (X : WeightedColumns ρ) (Y : WeightedColumns σ)
    (T : WeightedColumns τ) (s t : ℝ) (he : τ.op=(s:ℂ) • ρ.op+(t:ℂ) • σ.op) (j : Fin n) :
    T.lowerEnergy j=s*X.lowerEnergy j+t*Y.lowerEnergy j := by
  apply (T.lowerEnergy_hasSum j).unique
  convert! ((X.lowerEnergy_hasSum j).mul_left s).add ((Y.lowerEnergy_hasSum j).mul_left t) using 1
  funext k
  simp only [entry,he,add_apply,smul_apply,inner_add_right,inner_smul_right,Complex.add_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

end

section
open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} {ρ σ τ : State n}

theorem beam_weakMean (η : ℝ) (hη : η ∈ Set.Icc 0 1) (r s u : ℝ) (j : Fin n)
    (X : WeightedColumns ρ) (Y : WeightedColumns σ) (T : WeightedColumns τ)
    (hτ : IsBeamSplitterOutput η ρ σ τ) :
    T.weakMean u j=(Real.sqrt η:ℂ)*X.weakMean r j+(Real.sqrt (1-η):ℂ)*Y.weakMean s j := by
  rw [T.weakMean_reference u (η*r+(1-η)*s)]
  have hh := physical_product_weak η r s hη ρ σ τ hτ j X.vector Y.vector T.vector
    X.summable Y.summable T.summable X.normalized Y.normalized X.density Y.density T.density 1
  change T.weakMean (η*r+(1-η)*s) j=_ at hh
  change T.weakMean (η*r+(1-η)*s) j=
    (Real.sqrt η:ℂ)*singleWeak r j X.vector (Y.rawSlice η hη 1)+
    (Real.sqrt (1-η):ℂ)*singleWeak s j Y.vector (X.rawSliceRight η hη 1) at hh
  simpa only [Y.rawSlice_one,X.rawSliceRight_one,weakMean] using hh

theorem weakMean_affine (X : WeightedColumns ρ) (Y : WeightedColumns σ) (T : WeightedColumns τ)
    (c d : ℂ) (he : τ.op=c • ρ.op+d • σ.op) (r : ℝ) (j : Fin n) :
    T.weakMean r j=c*X.weakMean r j+d*Y.weakMean r j := by
  apply PhysicalGenerator.weak_pairing_affine r j c d X.vector Y.vector T.vector
    X.summable Y.summable T.summable _ 1
  change TraceEnsemble.operator (fun i => inverseWeight 3 (T.vector i))=
    c • TraceEnsemble.operator (fun i => inverseWeight 3 (X.vector i))+
    d • TraceEnsemble.operator (fun i => inverseWeight 3 (Y.vector i))
  rw [T.density,X.density,Y.density,he]

theorem sqrt_complex_square (η : ℝ) (hη : η ∈ Set.Icc 0 1) (x y : ℂ) :
    ‖(Real.sqrt η:ℂ)*x+(Real.sqrt (1-η):ℂ)*y‖^2=
      η*‖x‖^2+(1-η)*‖y‖^2+2*Real.sqrt η*Real.sqrt (1-η)*(x*conj y).re := by
  have hh := EnsembleL2.real_smul_add_square (Real.sqrt η) (Real.sqrt (1-η)) x y
  rw [Real.sq_sqrt hη.1,Real.sq_sqrt (sub_nonneg.mpr hη.2)] at hh
  convert! hh using 1
  simp only [RCLike.inner_apply,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

theorem beam_centeredLowerEnergy (η : ℝ) (hη : η ∈ Set.Icc 0 1) (r s u : ℝ) (j : Fin n)
    (X : WeightedColumns ρ) (Y : WeightedColumns σ) (T : WeightedColumns τ)
    (hτ : IsBeamSplitterOutput η ρ σ τ) :
    T.centeredLowerEnergy u j=η*X.centeredLowerEnergy r j+(1-η)*Y.centeredLowerEnergy s j := by
  rw [centeredLowerEnergy,physical_lowerEnergy η hη r s j X Y T hτ,
    beam_weakMean η hη r s u j X Y T hτ,sqrt_complex_square η hη]
  simp only [centeredLowerEnergy]
  ring

theorem thermal_centeredLowerEnergy (X : WeightedColumns ρ) (r u : ℝ) (hr : 0<r)
    (he : ∀ k l, entry ρ.op k l=if k=l then (thermalWeight n r k:ℂ) else 0) (j : Fin n) :
    X.centeredLowerEnergy u j=r := by
  rw [centeredLowerEnergy,thermal_lowerEnergy X r hr he,
    X.weakMean_reference u r]
  have hm : X.weakMean r j=0 := X.thermal_weak_zero r hr he j 1
  rw [hm,norm_zero,zero_pow (by decide : 2≠0),sub_zero]

theorem replacement_centeredLowerEnergy (X : WeightedColumns ρ) (O : WeightedColumns σ)
    (T : WeightedColumns τ) (κ r : ℝ) (hr : 0<r)
    (hO : ∀ k l, entry σ.op k l=if k=l then (thermalWeight n r k:ℂ) else 0)
    (he : τ.op=((1-κ:ℝ):ℂ) • ρ.op+(κ:ℂ) • σ.op) (j : Fin n) :
    T.centeredLowerEnergy r j=(1-κ)*X.centeredLowerEnergy r j+κ*r+
      κ*(1-κ)*‖X.weakMean r j‖^2 := by
  have ho : O.weakMean r j=0 := O.thermal_weak_zero r hr hO j 1
  rw [centeredLowerEnergy,lowerEnergy_affine X O T (1-κ) κ he,
    thermal_lowerEnergy O r hr hO,weakMean_affine X O T _ _ he,ho,mul_zero,add_zero,
    norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,centeredLowerEnergy]
  ring
end

open QuantumTrace
variable {n : ℕ}

theorem threeport_centered_energy_mode (η θ κ a b d : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (hd : 0<d)
    (hr0 : 0<θ*(η*a+(1-η)*b)+(1-θ)*d)
    (ρ σ τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η ρ σ m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (X : WeightedColumns ρ) (Y : WeightedColumns σ) (D : WeightedColumns τD)
    (M : WeightedColumns m) (V : WeightedColumns γ) (O : WeightedColumns ω) (T : WeightedColumns ρ0)
    (hD : ∀ k l, entry τD.op k l=if k=l then (thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (thermalWeight n (θ*(η*a+(1-η)*b)+(1-θ)*d) k:ℂ) else 0)
    (hrepl : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op) (j : Fin n) :
    T.centeredLowerEnergy (θ*(η*a+(1-η)*b)+(1-θ)*d) j-(θ*(η*a+(1-η)*b)+(1-θ)*d)=
      ((1-κ)*θ*η)*(X.centeredLowerEnergy a j-a)+((1-κ)*θ*(1-η))*(Y.centeredLowerEnergy b j-b)+
      κ*(1-κ)*‖V.weakMean (θ*(η*a+(1-η)*b)+(1-θ)*d) j‖^2 := by
  rw [replacement_centeredLowerEnergy V O T κ _ hr0 hO hrepl j,
    beam_centeredLowerEnergy θ hθ (η*a+(1-η)*b) d _ j M D V h2,
    beam_centeredLowerEnergy η hη a b _ j X Y M h1,
    thermal_centeredLowerEnergy D d d hd hD]
  ring
end EntropyPhotonNumber.WeightedColumns

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace WeightedColumns
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

theorem centeredEnergy_eq_sum (t : ℝ) (ht : 0<t) :
    G.centeredEnergy=∑ j, G.weightedColumns.centeredLowerEnergy t j := by
  rw [G.centeredEnergy_lowerEnergy t ht]
  simp only [centeredLowerEnergy,G.weakMean_eq_conj t ht,Complex.norm_conj]
end EntropyPhotonNumber.SpectralLogData

namespace EntropyPhotonNumber
open QuantumTrace WeightedColumns
variable {n : ℕ}

theorem physical_centered_energy_identity (η θ κ a b d : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (hd : 0<d) (ha : 0<a) (hb : 0<b)
    (hr0 : 0<θ*(η*a+(1-η)*b)+(1-θ)*d)
    (ρ σ τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η ρ σ m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (G1 : SpectralLogData n ρ) (G2 : SpectralLogData n σ) (G0 : SpectralLogData n ρ0)
    (D : WeightedColumns τD) (M : WeightedColumns m) (V : WeightedColumns γ) (O : WeightedColumns ω)
    (hD : ∀ k l, entry τD.op k l=if k=l then (thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (thermalWeight n (θ*(η*a+(1-η)*b)+(1-θ)*d) k:ℂ) else 0)
    (hrepl : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op) :
    G0.centeredEnergy-(n:ℝ)*(θ*(η*a+(1-η)*b)+(1-θ)*d)=
      ((1-κ)*θ*η)*(G1.centeredEnergy-(n:ℝ)*a)+((1-κ)*θ*(1-η))*(G2.centeredEnergy-(n:ℝ)*b)+
      κ*(1-κ)*(∑ j, ‖V.weakMean (θ*(η*a+(1-η)*b)+(1-θ)*d) j‖^2) := by
  have hh := Finset.sum_congr (s₁:=Finset.univ) rfl (fun j _ =>
    threeport_centered_energy_mode η θ κ a b d hη hθ hd hr0 ρ σ τD m γ ω ρ0 h1 h2
      G1.weightedColumns G2.weightedColumns D M V O G0.weightedColumns hD hO hrepl j)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← G0.centeredEnergy_eq_sum _ hr0,
    ← G1.centeredEnergy_eq_sum a ha,← G2.centeredEnergy_eq_sum b hb] at hh
  convert! hh using 1; ring
end EntropyPhotonNumber

end

namespace EntropyPhotonNumber
open scoped BigOperators ComplexConjugate

section
open TensorLp KrausBounded BeamLadder
variable {n : ℕ}

namespace Regularization
open QuantumTrace
variable (R : Regularization n)

end Regularization
end

open QuantumTrace Annihilation
variable {n : ℕ} {J : Type} {ρ : State n}

namespace GibbsData
variable {k : ℝ} (G : GibbsData n k ρ)
end GibbsData

end EntropyPhotonNumber

section
open scoped BigOperators

namespace WeightedGenerator

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}
theorem drift_radial (r : ℝ) (f : ℝ → ℝ) (k : NumberIndex n) :
    drift r (fun k => f (numberWeight k)) k =
      (r+1)*(numberWeight k-1)*(f (numberWeight k-1)-f (numberWeight k))+
        r*(numberWeight k-1+n)*(f (numberWeight k+1)-f (numberWeight k)) := by
  have he (j : Fin n) : (r+1)*(k j:ℝ)*(f (numberWeight (down j k))-f (numberWeight k)) =
      ((k j:ℝ)*(r+1))*(f (numberWeight k-1)-f (numberWeight k)) := by
    by_cases hk : k j=0
    · simp [hk]
    · rw [weight_down j k (Nat.pos_of_ne_zero hk)]
      ring
  simp only [drift, he, weight_up, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, numberWeight]
  ring

theorem drift_number (r : ℝ) (k : NumberIndex n) :
    drift r (fun k => (totalNumber k:ℝ)) k = n*r-totalNumber k := by
  have he (k : NumberIndex n) : (totalNumber k:ℝ)=numberWeight k-1 := by
    simp [totalNumber, numberWeight]
  have hh := drift_radial r (fun t => t-1) k
  simp_rw [he]
  rw [hh]
  ring

end

end WeightedGenerator

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation
variable {n : ℕ}

theorem drift_number_div_bound (r : ℝ) (k : NumberIndex n) :
    |WeightedGenerator.drift r (fun k => (totalNumber k:ℝ)) k/numberWeight k^6|≤|(n:ℝ)*r|+1 := by
  rw [WeightedGenerator.drift_number,abs_div,abs_of_pos (pow_pos (lt_of_lt_of_le zero_lt_one (numberWeight_one_le k)) _)]
  apply (div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one (numberWeight_one_le k)) _)).mpr
  have hw : 1≤numberWeight k^6 := one_le_pow₀ (numberWeight_one_le k)
  have hn : (totalNumber k:ℝ)≤numberWeight k^6 :=
    (number_le_weight k).trans (le_self_pow₀ (numberWeight_one_le k) (by norm_num))
  calc
    |(n:ℝ)*r-totalNumber k|≤|(n:ℝ)*r|+|(totalNumber k:ℝ)| := abs_sub _ _
    _ ≤ (|(n:ℝ)*r|+1)*numberWeight k^6 := by
      have hnabs : |(totalNumber k:ℝ)|=(totalNumber k:ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
      rw [hnabs]
      nlinarith [mul_le_mul_of_nonneg_left hw (abs_nonneg ((n:ℝ)*r))]

theorem thermalGenerator_number (r : ℝ) (ρ : State n) (hm : FiniteMoment 6 ρ) :
    (WeightedGenerator.pairing r (weightedRoot 3 ρ hm) (numberSandwich n)).re=(n:ℝ)*r-energy ρ := by
  have hh := thermalGenerator_drift r ρ hm (fun k => (totalNumber k:ℝ)) 1 (|(n:ℝ)*r|+1)
    (by norm_num) number_div_weight_bound (drift_number_div_bound r)
  have he := (ρ.trace_one.mul_left ((n:ℝ)*r)).sub (finiteMoment_finiteEnergy (by norm_num) hm).hasSum
  change HasSum _ (WeightedGenerator.pairing r (weightedRoot 3 ρ hm) (numberSandwich n)).re at hh
  apply hh.unique
  simpa only [WeightedGenerator.drift_number, sub_mul, mul_one, energy] using he
end

open QuantumTrace Annihilation WeightedGenerator
variable {n : ℕ}

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate

namespace EntropyPhotonNumber.Regularization
open QuantumTrace Annihilation
variable {n : ℕ} (R : Regularization n)

theorem thermal_state_diagonal (r : ℝ) (hr : 0<r) (k l : NumberIndex n) :
    entry (thermalState n r hr).op k l=if k=l then (thermalWeight n r k:ℂ) else 0 := by
  rw [entry,← numberBasis_apply n k,← numberBasis_apply n l]
  change inner ℂ (numberBasis n k) ((diagonalState _ _ _).op (numberBasis n l))=_
  rw [diagonalState_eigen,inner_smul_right,
    orthonormal_iff_ite.mp (numberBasis n).orthonormal k l]
  split_ifs with h
  · subst l; simp only [mul_one]
  · simp only [mul_zero]

end EntropyPhotonNumber.Regularization

namespace EntropyPhotonNumber

section
open QuantumTrace ThermalMetric

namespace ThermalSetup
variable (P : ThermalSetup)
theorem raw_finiteMoment {n m : ℕ} {ρ σ : State n} (hρ : FiniteMoment m ρ) (hσ : FiniteMoment m σ) :
    FiniteMoment m (P.raw ρ σ) :=
  beamOutput_finiteMoment _ _ (beamOutput_finiteMoment _ _ hρ hσ) (thermalState_finiteMoment n m P.d P.hd)
theorem output_op {n : ℕ} (ζ : ℝ) (hζ : 0<ζ) (ρ σ : State n) :
    ((P.reg n ζ hζ).output ρ σ).op=((1-P.κ:ℝ):ℂ) • (P.raw ρ σ).op+
      (P.κ:ℂ) • (thermalState n P.r0 P.r0_pos).op := by
  simp only [Regularization.output,reg,regularizedOutput,sub_sub_cancel,mixture,raw,middle]
end ThermalSetup

namespace WeightedColumns
variable {n : ℕ} {ρ : State n}
theorem sum_lowerEnergy (X : WeightedColumns ρ) : (∑ j, X.lowerEnergy j)=energy ρ := by
  have hh := hasSum_sum (fun j (_hj : j ∈ (Finset.univ : Finset (Fin n))) => X.lowerEnergy_hasSum j)
  have he : HasSum (fun k => (totalNumber k:ℝ)*(entry ρ.op k k).re) (∑ j, X.lowerEnergy j) := by
    simpa only [totalNumber,Nat.cast_sum,Finset.sum_mul] using hh
  exact he.tsum_eq.symm
end WeightedColumns
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
theorem centeredEnergy_eq_energy (t : ℝ) (ht : 0<t) :
    G.centeredEnergy=energy ρ-(∑ j, ‖G.annihilationMean j‖^2) := by
  rw [G.centeredEnergy_lowerEnergy t ht,Finset.sum_sub_distrib,G.weightedColumns.sum_lowerEnergy]
end SpectralLogData
end

open QuantumTrace ThermalMetric Annihilation
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
end SpectralLogData
namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)
end GibbsData
namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)

theorem physical_energy (ζ : ℝ) (hζ : 0<ζ) (ρ σ : State n)
    (G1 : SpectralLogData n ρ) (G2 : SpectralLogData n σ)
    (G0 : SpectralLogData n ((P.reg n ζ hζ).output ρ σ))
    (h6ρ : FiniteMoment 6 ρ) (h6σ : FiniteMoment 6 σ) :
    ∃ v : ℝ, 0≤v ∧ G0.centeredEnergy-(n:ℝ)*P.r0=
      P.w1*(G1.centeredEnergy-(n:ℝ)*P.r1)+P.w2*(G2.centeredEnergy-(n:ℝ)*P.r2)+P.κ*(1-P.κ)*v := by
  let D := WeightedColumns.canonical (thermalState n P.d P.hd) (thermalState_finiteMoment n 6 P.d P.hd)
  let M := WeightedColumns.canonical (P.middle ρ σ) (beamOutput_finiteMoment _ _ h6ρ h6σ)
  let V := WeightedColumns.canonical (P.raw ρ σ) (P.raw_finiteMoment h6ρ h6σ)
  let O := WeightedColumns.canonical (thermalState n P.r0 P.r0_pos) (thermalState_finiteMoment n 6 P.r0 P.r0_pos)
  refine ⟨∑ j, ‖V.weakMean P.r0 j‖^2,Finset.sum_nonneg (fun _j _ => sq_nonneg _),?_⟩
  exact physical_centered_energy_identity P.η P.θ P.κ P.r1 P.r2 P.d P.η_mem P.θ_mem P.hd P.hr1 P.hr2 P.r0_pos
    ρ σ (thermalState n P.d P.hd) (P.middle ρ σ) (P.raw ρ σ) (thermalState n P.r0 P.r0_pos)
    ((P.reg n ζ hζ).output ρ σ) (beamOutput_spec _ _ _ _) (beamOutput_spec _ _ _ _) G1 G2 G0 D M V O
    (Regularization.thermal_state_diagonal P.d P.hd) (Regularization.thermal_state_diagonal P.r0 P.r0_pos)
    (P.output_op ζ hζ ρ σ)
end ThermalSetup

namespace ThermalDual

theorem decay_from_cancellation (q A M ε K ζ D C : ℝ) (hε : 0<ε) (hζ : 0≤ζ)
    (hK : 0≤K) (hD : D≤C)
    (hq : q≤A+ε/2*(A+M)) (hc : 0=q-(1+ε)*A-ε*M-K+ζ*D) :
    A+M≤(2*C/ε)*ζ := by
  have hh : ε/2*(A+M)≤ζ*C := by nlinarith [mul_le_mul_of_nonneg_left hD hζ]
  calc
    (A+M) ≤ (2*C*ζ)/ε := by apply (le_div_iff₀ hε).mpr; nlinarith only [hh]
    _ = (2*C/ε)*ζ := by ring

end ThermalDual
namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)

theorem minimum_decay (C1 C2 : ℝ)
    (hC1 : ∀ (ρ : State n) (hm : FiniteMoment 6 ρ),
      (WeightedGenerator.pairing P.r1 (weightedRoot 3 ρ hm) (1 : Fock n →L[ℂ] Fock n)).re≤C1)
    (hC2 : ∀ (ρ : State n) (hm : FiniteMoment 6 ρ),
      (WeightedGenerator.pairing P.r2 (weightedRoot 3 ρ hm) (1 : Fock n →L[ℂ] Fock n)).re≤C2)
    (ζ : ℝ) (hζ : 0<ζ) (ρ σ : State n) (hmρ : FiniteMoment 4 ρ) (hmσ : FiniteMoment 4 σ)
    (hmin : ∀ ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' →
      (P.reg n ζ hζ).objective ρ σ≤(P.reg n ζ hζ).objective ρ' σ') :
    ∃ (G1 : GibbsData n (ζ/((1+P.ε)*P.w1/h P.r1)) ρ)
      (G2 : GibbsData n (ζ/((1+P.ε)*P.w2/h P.r2)) σ),
      P.w1*((∑ j, ‖G1.defect (div_pos hζ (P.reg n ζ hζ).ha1) P.r1 P.hr1 j‖^2)+
        (∑ j, ‖G1.annihilationMean j‖^2))+
      P.w2*((∑ j, ‖G2.defect (div_pos hζ (P.reg n ζ hζ).ha2) P.r2 P.hr2 j‖^2)+
        (∑ j, ‖G2.annihilationMean j‖^2)) ≤ (2*(C1+C2)/P.ε)*ζ := by
  let R := P.reg n ζ hζ
  obtain ⟨G1,G2,G0,h6ρ,h6σ,h60,hbal,hh1,hh2⟩ := R.minimum_spectral_pairing_balance ρ σ hmρ hmσ
    P.r1 P.r2 P.d P.r0 P.hd P.r0_pos (by simp only [R,reg,sub_sub_cancel]; rfl) rfl rfl P.hκ.1 hmin
  let E1 := G1.toSpectralLogData (div_pos R.hζ R.ha1)
  let E2 := G2.toSpectralLogData (div_pos R.hζ R.ha2)
  have hH1 : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-P.κ)^2*BKM.quadratic E1.basis E1.probability
        (BKM.center E1.basis E1.probability (rawFirstSlice P.η P.θ P.η_mem P.θ_mem σ (thermalState n P.d P.hd) Z))≤
        ((1+P.ε)*P.w1/h P.r1)/(1/h P.r0)*BKM.quadratic G0.basis G0.probability Z := by
    intro Z hZ
    simpa only [E1,GibbsData.toSpectralLogData,R,reg,sub_sub_cancel] using hh1 Z hZ
  have hH2 : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-P.κ)^2*BKM.quadratic E2.basis E2.probability
        (BKM.center E2.basis E2.probability (rawSecondSlice P.η P.θ P.η_mem P.θ_mem ρ (thermalState n P.d P.hd) Z))≤
        ((1+P.ε)*P.w2/h P.r2)/(1/h P.r0)*BKM.quadratic G0.basis G0.probability Z := by
    intro Z hZ
    simpa only [E2,GibbsData.toSpectralLogData,R,reg,sub_sub_cancel] using hh2 Z hZ
  have hdef := P.physical_estimate ζ hζ ρ σ E1 E2 G0 h6ρ h6σ hH1 hH2
  obtain ⟨v,hv,hce⟩ := P.physical_energy ζ hζ ρ σ E1 E2 G0 h6ρ h6σ
  have hbalr := congrArg Complex.re hbal
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hbalr
  have hstat :
      (1+P.ε)*P.w1*((WeightedGenerator.pairing P.r1 (weightedRoot 3 ρ h6ρ) E1.logSandwich).re/h P.r1)+
      (1+P.ε)*P.w2*((WeightedGenerator.pairing P.r2 (weightedRoot 3 σ h6σ) E2.logSandwich).re/h P.r2)=
      (WeightedGenerator.pairing P.r0 (weightedRoot 3 (R.output ρ σ) h60) G0.logSandwich).re/h P.r0+
      P.ε*P.w1*(WeightedGenerator.pairing P.r1 (weightedRoot 3 ρ h6ρ) (numberSandwich n)).re+
      P.ε*P.w2*(WeightedGenerator.pairing P.r2 (weightedRoot 3 σ h6σ) (numberSandwich n)).re+
      ζ*((WeightedGenerator.pairing P.r1 (weightedRoot 3 ρ h6ρ) (1 : Fock n →L[ℂ] Fock n)).re+
        (WeightedGenerator.pairing P.r2 (weightedRoot 3 σ h6σ) (1 : Fock n →L[ℂ] Fock n)).re) := by
    convert hbalr using 1 <;> dsimp only [R,reg,E1,E2,GibbsData.toSpectralLogData] <;> ring
  rw [E1.entropy_production h6ρ P.r1 P.hr1,E2.entropy_production h6σ P.r2 P.hr2,
    G0.entropy_production h60 P.r0 P.r0_pos,thermalGenerator_number,thermalGenerator_number] at hstat
  have he1 : energy ρ=E1.centeredEnergy+E1.meanSquared := by
    have hh := E1.centeredEnergy_eq_energy P.r1 P.hr1
    change E1.centeredEnergy=energy ρ-E1.meanSquared at hh
    linarith
  have he2 : energy σ=E2.centeredEnergy+E2.meanSquared := by
    have hh := E2.centeredEnergy_eq_energy P.r2 P.hr2
    change E2.centeredEnergy=energy σ-E2.meanSquared at hh
    linarith
  rw [he1,he2,hce] at hstat
  have hc : 0=G0.defectSquared P.r0 P.r0_pos-
      (1+P.ε)*(P.w1*E1.defectSquared P.r1 P.hr1+P.w2*E2.defectSquared P.r2 P.hr2)-
      P.ε*(P.w1*E1.meanSquared+P.w2*E2.meanSquared)-P.κ*(1-P.κ)*v+
      ζ*((WeightedGenerator.pairing P.r1 (weightedRoot 3 ρ h6ρ) (1 : Fock n →L[ℂ] Fock n)).re+
        (WeightedGenerator.pairing P.r2 (weightedRoot 3 σ h6σ) (1 : Fock n →L[ℂ] Fock n)).re) := by
    dsimp only [SpectralLogData.defectSquared]
    linear_combination hstat
  have hdec := ThermalDual.decay_from_cancellation _ _ _ _ _ _ _ (C1+C2) P.hε hζ.le
    (mul_nonneg (mul_nonneg P.hκ.1.le (sub_nonneg.mpr P.hκ.2.le)) hv)
    (add_le_add (hC1 ρ h6ρ) (hC2 σ h6σ)) hdef hc
  refine ⟨G1,G2,?_⟩
  change P.w1*(E1.defectSquared P.r1 P.hr1+E1.meanSquared)+
    P.w2*(E2.defectSquared P.r2 P.hr2+E2.meanSquared)≤(2*(C1+C2)/P.ε)*ζ
  nlinarith only [hdec]

end ThermalSetup
end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.ThermalSetup
open scoped BigOperators ComplexConjugate
open QuantumTrace ThermalMetric Annihilation


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.ThermalSetup.minimum_decay := @_root_.OAI.EntropyPhotonNumber.ThermalSetup.minimum_decay
