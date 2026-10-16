-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.replaced_threeport_weak
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:55:37.652982+00:00
-- url     : https://prove2.me/submissions/baf073e7-d214-473a-986e-ecc5a9e1c350

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Generator.lean:L514-L547
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.replaced_threeport_weak. The node keeps its source
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
import Theorems.Thm_OAI_PhysicalGenerator_weakOperator_entry

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

-- ---- from OAI.InformationTheory.PhotonNumber.BeamForms ----
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

theorem replaced_threeport_weak
    {n : ℕ} (η θ κ a b d : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ σ τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η ρ σ m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (X : WeightedColumns ρ) (Y : WeightedColumns σ) (D : WeightedColumns τD)
    (M : WeightedColumns m) (G : WeightedColumns γ) (O : WeightedColumns ω) (R : WeightedColumns ρ0)
    (hd : 0<d) (hr0 : 0<θ*(η*a+(1-η)*b)+(1-θ)*d)
    (hD : ∀ k l, entry τD.op k l=if k=l then (thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (thermalWeight n (θ*(η*a+(1-η)*b)+(1-θ)*d) k:ℂ) else 0)
    (hrepl : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op)
    (j : Fin n) (Z : Fock n →L[ℂ] Fock n) :
    singleWeak (θ*(η*a+(1-η)*b)+(1-θ)*d) j R.vector Z=
      ((1-κ:ℝ):ℂ)*((Real.sqrt θ:ℂ)*(Real.sqrt η:ℂ)*
        singleWeak a j X.vector (Y.rawSlice η hη (D.rawSlice θ hθ Z))+
        (Real.sqrt θ:ℂ)*(Real.sqrt (1-η):ℂ)*
        singleWeak b j Y.vector (X.rawSliceRight η hη (D.rawSlice θ hθ Z))) := by
  have hr := PhysicalGenerator.weak_pairing_affine
    (θ*(η*a+(1-η)*b)+(1-θ)*d) j ((1-κ:ℝ):ℂ) (κ:ℂ)
    G.vector O.vector R.vector G.summable O.summable R.summable
    (by rw [G.base_density,O.base_density,R.base_density,hrepl]) Z
  rw [hr,O.thermal_weak_zero _ hr0 hO,mul_zero,add_zero]
  have hh2 := physical_product_weak θ (η*a+(1-η)*b) d hθ m τD γ h2 j
    M.vector D.vector G.vector M.summable D.summable G.summable M.normalized D.normalized
    M.density D.density G.density Z
  have hh1 := physical_product_weak η a b hη ρ σ m h1 j
    X.vector Y.vector M.vector X.summable Y.summable M.summable X.normalized Y.normalized
    X.density Y.density M.density (D.rawSlice θ hθ Z)
  change singleWeak (θ*(η*a+(1-η)*b)+(1-θ)*d) j G.vector Z=
    (Real.sqrt θ:ℂ)*singleWeak (η*a+(1-η)*b) j M.vector (D.rawSlice θ hθ Z)+
    (Real.sqrt (1-θ):ℂ)*singleWeak d j D.vector (M.rawSliceRight θ hθ Z) at hh2
  rw [D.thermal_weak_zero d hd hD,mul_zero,add_zero,hh1] at hh2
  rw [hh2]
  dsimp only [WeightedColumns.rawSlice,WeightedColumns.rawSliceRight]
  ring
end EntropyPhotonNumber

namespace KrausBounded
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
end KrausBounded

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}
end BeamLadder

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder TensorLp
namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

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

end WeightedColumns

end EntropyPhotonNumber

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
open QuantumTrace Annihilation BeamLadder TensorLp


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.replaced_threeport_weak := @_root_.OAI.EntropyPhotonNumber.replaced_threeport_weak
