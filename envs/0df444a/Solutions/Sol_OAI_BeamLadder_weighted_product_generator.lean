-- Prove2me | solution 1 for OAI.BeamLadder.weighted_product_generator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:42:16.346953+00:00
-- url     : https://prove2.me/submissions/217dba28-766d-4891-ab44-0a358aba548a

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/BeamForms.lean:L1610-L1664
-- (upload_full_project.md Phase 4): solution for node OAI.BeamLadder.weighted_product_generator. The node keeps its source
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
import Theorems.Thm_OAI_Annihilation_weighted_trace_ext
import Theorems.Thm_OAI_BeamLadder_adjoint_covariance
import Theorems.Thm_OAI_BeamLadder_discarded_covariance
import Theorems.Thm_OAI_BeamLadder_generatorPairingL_product
import Theorems.Thm_OAI_BeamLadder_generatorPairingR_product
import Theorems.Thm_OAI_BeamLadder_numberL_minus
import Theorems.Thm_OAI_BeamLadder_radial_covariance
import Theorems.Thm_OAI_BeamLadder_retained_covariance
import Theorems.Thm_OAI_BeamLadder_tensorPreimage2_summable
import Theorems.Thm_OAI_CrossEnsemble_operator_comp_left
import Theorems.Thm_OAI_CrossEnsemble_shifted_both_operator_eq
import Theorems.Thm_OAI_CrossEnsemble_shifted_left_operator_eq
import Theorems.Thm_OAI_CrossEnsemble_shifted_right_operator_eq
import Theorems.Thm_OAI_WeightedGenerator_pairing_hasSum

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

theorem raiseL_up (j : Fin n) (x : JointFock n) (ke : NumberIndex n × NumberIndex n) :
    raiseL j x (upL j ke)=((Real.sqrt ((ke.1 j:ℝ)+1)/W ke:ℝ):ℂ)*x ke := by
  change (increase (W (upL j ke)):ℂ)*((lowerL j).adjoint x (upL j ke))=_
  rw [lowerL, WeightedShift.adjoint_apply_image]
  have hw : 0<W ke := by linarith [W_one_le ke]
  simp only [W_upL, increase, ite_eq_left (by linarith : 1<W ke+1), add_sub_cancel_right,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, map_div₀, map_add, map_one, Complex.conj_ofReal]
  have hw1 : (W ke:ℂ)+1≠0 := by exact_mod_cast (by linarith : W ke+1≠0)
  field_simp

theorem raiseR_up (j : Fin n) (x : JointFock n) (ke : NumberIndex n × NumberIndex n) :
    raiseR j x (upR j ke)=((Real.sqrt ((ke.2 j:ℝ)+1)/W ke:ℝ):ℂ)*x ke := by
  change (increase (W (upR j ke)):ℂ)*((lowerR j).adjoint x (upR j ke))=_
  rw [lowerR, WeightedShift.adjoint_apply_image]
  have hw : 0<W ke := by linarith [W_one_le ke]
  simp only [W_upR, increase, ite_eq_left (by linarith : 1<W ke+1), add_sub_cancel_right,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, map_div₀, map_add, map_one, Complex.conj_ofReal]
  have hw1 : (W ke:ℂ)+1≠0 := by exact_mod_cast (by linarith : W ke+1≠0)
  field_simp

theorem raiseL_zero (j : Fin n) (x : JointFock n) (ke : NumberIndex n × NumberIndex n)
    (hk : ke.1 j=0) : raiseL j x ke=0 := by
  change _*((lowerL j).adjoint x ke)=0
  rw [lowerL, WeightedShift.adjoint_apply_outside]
  · exact mul_zero _
  · intro ab he
    have hh := congrArg (fun q => q.1 j) he
    simp only [upL, up_same, hk] at hh
    omega

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

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

theorem inverse_preLowerL (j : Fin n) (x : JointFock n) :
    inverse (preLowerL j x)=lowerL j (inverse x) := by
  apply lp.ext
  funext ke
  have hw : (W ke:ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le ke] : W ke≠0)
  have hu : (W ke:ℂ)+1≠0 := by exact_mod_cast (by linarith [W_one_le ke] : W ke+1≠0)
  simp only [preLowerL, ContinuousLinearMap.comp_apply, inverse_apply, lowerL_apply,
    sub_apply, one_apply_eq_self, lp.coeFn_sub, Pi.sub_apply, W_upL]
  push_cast
  field_simp
  ring

theorem inverse_preLowerR (j : Fin n) (x : JointFock n) :
    inverse (preLowerR j x)=lowerR j (inverse x) := by
  apply lp.ext
  funext ke
  have hw : (W ke:ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le ke] : W ke≠0)
  have hu : (W ke:ℂ)+1≠0 := by exact_mod_cast (by linarith [W_one_le ke] : W ke+1≠0)
  simp only [preLowerR, ContinuousLinearMap.comp_apply, inverse_apply, lowerR_apply,
    sub_apply, one_apply_eq_self, lp.coeFn_sub, Pi.sub_apply, W_upR]
  push_cast
  field_simp
  ring

theorem inverse_preRaiseL (j : Fin n) (x : JointFock n) :
    inverse (preRaiseL j x)=raiseL j (inverse x) := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  by_cases hk : k j=0
  · simp only [preRaiseL, ContinuousLinearMap.comp_apply, inverse_apply,
      raiseL_zero j _ (k,e) hk, mul_zero]
  · obtain ⟨a,rfl⟩ : ∃ a, k=up j a := ⟨down j k,(up_down j k (Nat.pos_of_ne_zero hk)).symm⟩
    change inverse (raiseL j ((1+inverse) x)) (upL j (a,e))=raiseL j (inverse x) (upL j (a,e))
    have hw : (W (a,e):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (a,e)] : W (a,e)≠0)
    have hu : (W (a,e):ℂ)+1≠0 := by exact_mod_cast (by linarith [W_one_le (a,e)] : W (a,e)+1≠0)
    simp only [inverse_apply, W_upL, raiseL_up, add_apply, one_apply_eq_self, lp.coeFn_add, Pi.add_apply]
    push_cast
    field_simp

theorem inverse_preRaiseR (j : Fin n) (x : JointFock n) :
    inverse (preRaiseR j x)=raiseR j (inverse x) := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  by_cases he : e j=0
  · simp only [preRaiseR, ContinuousLinearMap.comp_apply, inverse_apply,
      raiseR_zero j _ (k,e) he, mul_zero]
  · obtain ⟨a,rfl⟩ : ∃ a, e=up j a := ⟨down j e,(up_down j e (Nat.pos_of_ne_zero he)).symm⟩
    change inverse (raiseR j ((1+inverse) x)) (upR j (k,a))=raiseR j (inverse x) (upR j (k,a))
    have hw : (W (k,a):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (k,a)] : W (k,a)≠0)
    have hu : (W (k,a):ℂ)+1≠0 := by exact_mod_cast (by linarith [W_one_le (k,a)] : W (k,a)+1≠0)
    simp only [inverse_apply, W_upR, raiseR_up, add_apply, one_apply_eq_self, lp.coeFn_add, Pi.add_apply]
    push_cast
    field_simp

theorem liftLeft_adjoint_inner {A B : Type*} (Z : H A →L[ℂ] H A)
    (x y : H (A × B)) :
    inner ℂ (liftLeft Z.adjoint x) y=inner ℂ x (liftLeft Z y) := by
  apply HasSum.unique (hasSum_slice_inner (liftLeft Z.adjoint x) y)
  convert! hasSum_slice_inner x (liftLeft Z y) using 1
  ext b
  simp only [slice_liftLeft, ContinuousLinearMap.adjoint_inner_left]

theorem discarded_commutator_star (j : Fin n) (Z : Fock n →L[ℂ] Fock n)
    (x y : JointFock n) :
    inner ℂ (raiseR j x) (liftLeft Z (inverse y))=
      inner ℂ (inverse x) (liftLeft Z (lowerR j y)) := by
  have hh := congrArg (conj : ℂ → ℂ) (discarded_commutator j Z.adjoint y x)
  simpa only [inner_conj_symm, liftLeft_adjoint_inner] using hh

theorem quadMinusR_zero (j : Fin n) (x y : JointFock n) (Z : Fock n →L[ℂ] Fock n) :
    quadMinusR j x y (liftLeft Z)=0 := by
  have h₁ := discarded_commutator j Z (inverse x) (preLowerR j y)
  have h₂ := discarded_commutator_star j Z (preLowerR j x) (inverse y)
  rw [inverse_preLowerR] at h₁ h₂
  unfold quadMinusR
  rw [h₁, h₂]
  ring

theorem quadPlusR_zero (j : Fin n) (x y : JointFock n) (Z : Fock n →L[ℂ] Fock n) :
    quadPlusR j x y (liftLeft Z)=0 := by
  have h₁ := discarded_commutator_star j Z (inverse x) (preRaiseR j y)
  have h₂ := discarded_commutator j Z (preRaiseR j x) (inverse y)
  rw [inverse_preRaiseR] at h₁ h₂
  unfold quadPlusR
  rw [← h₁, ← h₂]
  ring

theorem cross_raise_lower (j : Fin n) (x : JointFock n) :
    raiseL j (preLowerR j x)=lowerR j (preRaiseL j x) := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  by_cases hk : k j=0
  · rw [raiseL_zero j _ (k,e) hk, lowerR_apply]
    change 0=_*raiseL j ((1+inverse) x) (k,up j e)
    rw [raiseL_zero j _ (k,up j e) hk, mul_zero]
  · obtain ⟨a,rfl⟩ : ∃ a,k=up j a := ⟨down j k,(up_down j k (Nat.pos_of_ne_zero hk)).symm⟩
    change raiseL j (preLowerR j x) (upL j (a,e))=_
    rw [raiseL_up, lowerR_apply]
    change _=_*raiseL j ((1+inverse) x) (upL j (a,up j e))
    rw [raiseL_up]
    have hw : (W (a,e):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (a,e)] : W (a,e)≠0)
    have hu : (W (a,e):ℂ)+1≠0 := by exact_mod_cast (by linarith [W_one_le (a,e)] : W (a,e)+1≠0)
    have hv : (W (a,e):ℂ)+1+1≠0 := by exact_mod_cast (by linarith [W_one_le (a,e)] : W (a,e)+1+1≠0)
    simp only [preLowerR, ContinuousLinearMap.comp_apply, lowerR_apply,
      sub_apply, add_apply, one_apply_eq_self, lp.coeFn_sub, lp.coeFn_add,
      Pi.sub_apply, Pi.add_apply, inverse_apply]
    change _=_
    simp only [show W (a,up j e)=W (a,e)+1 from W_upR j (a,e),
      show W (up j a,e)=W (a,e)+1 from W_upL j (a,e), upR]
    push_cast
    field_simp
    ring

theorem cross_lower_raise (j : Fin n) (x : JointFock n) :
    raiseR j (preLowerL j x)=lowerL j (preRaiseR j x) := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  by_cases he : e j=0
  · rw [raiseR_zero j _ (k,e) he, lowerL_apply]
    change 0=_*raiseR j ((1+inverse) x) (up j k,e)
    rw [raiseR_zero j _ (up j k,e) he, mul_zero]
  · obtain ⟨a,rfl⟩ : ∃ a,e=up j a := ⟨down j e,(up_down j e (Nat.pos_of_ne_zero he)).symm⟩
    change raiseR j (preLowerL j x) (upR j (k,a))=_
    rw [raiseR_up, lowerL_apply]
    change _=_*raiseR j ((1+inverse) x) (upR j (up j k,a))
    rw [raiseR_up]
    have hw : (W (k,a):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (k,a)] : W (k,a)≠0)
    have hu : (W (k,a):ℂ)+1≠0 := by exact_mod_cast (by linarith [W_one_le (k,a)] : W (k,a)+1≠0)
    have hv : (W (k,a):ℂ)+1+1≠0 := by exact_mod_cast (by linarith [W_one_le (k,a)] : W (k,a)+1+1≠0)
    simp only [preLowerL, ContinuousLinearMap.comp_apply, lowerL_apply,
      sub_apply, add_apply, one_apply_eq_self, lp.coeFn_sub, lp.coeFn_add,
      Pi.sub_apply, Pi.add_apply, inverse_apply]
    simp only [show W (up j k,a)=W (k,a)+1 from W_upL j (k,a),
      show W (k,up j a)=W (k,a)+1 from W_upR j (k,a), upL]
    push_cast
    field_simp
    ring

theorem cross_heat_zero (j : Fin n) (x y : JointFock n) (Z : Fock n →L[ℂ] Fock n) :
    crossMinus j x y (liftLeft Z)+crossPlus j x y (liftLeft Z)=0 := by
  have h₁ := discarded_commutator j Z (inverse x) (preLowerL j y)
  have h₂ := discarded_commutator_star j Z (preLowerL j x) (inverse y)
  have h₃ := discarded_commutator_star j Z (inverse x) (preRaiseL j y)
  have h₄ := discarded_commutator j Z (preRaiseL j x) (inverse y)
  rw [inverse_preLowerL] at h₁ h₂
  rw [inverse_preRaiseL] at h₃ h₄
  unfold crossMinus crossPlus
  simp only [← cross_lower_raise, cross_raise_lower]
  rw [h₁, h₂, ← h₃, ← h₄]
  ring

theorem covariance_preLowerL (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    preLowerL j (beamUnitary η hη x)=(Real.sqrt η:ℂ) • beamUnitary η hη (preLowerL j x)+
      (Real.sqrt (1-η):ℂ) • beamUnitary η hη (preLowerR j x) := by
  have hi : (1-inverse) (beamUnitary η hη x)=beamUnitary η hη ((1-inverse) x) := by
    simp only [sub_apply,one_apply_eq_self,map_sub,covariance_inverse_apply]
  simp only [preLowerL, preLowerR,ContinuousLinearMap.comp_apply]
  rw [hi, covariance_lower_apply]

theorem covariance_preLowerR (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    preLowerR j (beamUnitary η hη x)=-(Real.sqrt (1-η):ℂ) • beamUnitary η hη (preLowerL j x)+
      (Real.sqrt η:ℂ) • beamUnitary η hη (preLowerR j x) := by
  have hi : (1-inverse) (beamUnitary η hη x)=beamUnitary η hη ((1-inverse) x) := by
    simp only [sub_apply,one_apply_eq_self,map_sub,covariance_inverse_apply]
  simp only [preLowerL, preLowerR,ContinuousLinearMap.comp_apply]
  rw [hi, covariance_discarded_lower_apply]

theorem covariance_preRaiseL (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    preRaiseL j (beamUnitary η hη x)=(Real.sqrt η:ℂ) • beamUnitary η hη (preRaiseL j x)+
      (Real.sqrt (1-η):ℂ) • beamUnitary η hη (preRaiseR j x) := by
  have hi : (1+inverse) (beamUnitary η hη x)=beamUnitary η hη ((1+inverse) x) := by
    simp only [add_apply,one_apply_eq_self,map_add,covariance_inverse_apply]
  simp only [preRaiseL, preRaiseR,ContinuousLinearMap.comp_apply]
  rw [hi, covariance_raise_apply]

theorem covariance_preRaiseR (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    preRaiseR j (beamUnitary η hη x)=-(Real.sqrt (1-η):ℂ) • beamUnitary η hη (preRaiseL j x)+
      (Real.sqrt η:ℂ) • beamUnitary η hη (preRaiseR j x) := by
  have hi : (1+inverse) (beamUnitary η hη x)=beamUnitary η hη ((1+inverse) x) := by
    simp only [add_apply,one_apply_eq_self,map_add,covariance_inverse_apply]
  simp only [preRaiseL, preRaiseR,ContinuousLinearMap.comp_apply]
  rw [hi, covariance_discarded_raise_apply]

theorem undo_rotation {E : Type*} [AddCommGroup E] [Module ℂ E]
    (c s : ℂ) (hc : c^2+s^2=1) (X Y : E) :
    c • (c • X+s • Y)-s • (-s • X+c • Y)=X ∧
    s • (c • X+s • Y)+c • (-s • X+c • Y)=Y := by
  constructor
  · calc
      _=(c^2+s^2) • X := by module
      _=X := by rw [hc,one_smul]
  · calc
      _=(c^2+s^2) • Y := by module
      _=Y := by rw [hc,one_smul]

theorem beam_squares (η : ℝ) (hη : η ∈ Set.Icc 0 1) :
    (Real.sqrt η:ℂ)^2+(Real.sqrt (1-η):ℂ)^2=1 := by
  norm_cast
  rw [Real.sq_sqrt hη.1,Real.sq_sqrt (sub_nonneg.mpr hη.2)]
  ring

theorem undo_lowerL (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    beamUnitary η hη (lowerL j x)=(Real.sqrt η:ℂ) • lowerL j (beamUnitary η hη x)-(Real.sqrt (1-η):ℂ) • lowerR j (beamUnitary η hη x) := by
  rw [covariance_lower_apply, covariance_discarded_lower_apply]
  exact (undo_rotation _ _ (beam_squares η hη) _ _).1.symm

theorem undo_lowerR (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    beamUnitary η hη (lowerR j x)=(Real.sqrt (1-η):ℂ) • lowerL j (beamUnitary η hη x)+(Real.sqrt η:ℂ) • lowerR j (beamUnitary η hη x) := by
  rw [covariance_lower_apply, covariance_discarded_lower_apply]
  exact (undo_rotation _ _ (beam_squares η hη) _ _).2.symm

theorem undo_raiseL (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    beamUnitary η hη (raiseL j x)=(Real.sqrt η:ℂ) • raiseL j (beamUnitary η hη x)-(Real.sqrt (1-η):ℂ) • raiseR j (beamUnitary η hη x) := by
  rw [covariance_raise_apply, covariance_discarded_raise_apply]
  exact (undo_rotation _ _ (beam_squares η hη) _ _).1.symm

theorem undo_raiseR (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    beamUnitary η hη (raiseR j x)=(Real.sqrt (1-η):ℂ) • raiseL j (beamUnitary η hη x)+(Real.sqrt η:ℂ) • raiseR j (beamUnitary η hη x) := by
  rw [covariance_raise_apply, covariance_discarded_raise_apply]
  exact (undo_rotation _ _ (beam_squares η hη) _ _).2.symm

theorem undo_preLowerL (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    beamUnitary η hη (preLowerL j x)=(Real.sqrt η:ℂ) • preLowerL j (beamUnitary η hη x)-(Real.sqrt (1-η):ℂ) • preLowerR j (beamUnitary η hη x) := by
  rw [covariance_preLowerL, covariance_preLowerR]
  exact (undo_rotation _ _ (beam_squares η hη) _ _).1.symm

theorem undo_preLowerR (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    beamUnitary η hη (preLowerR j x)=(Real.sqrt (1-η):ℂ) • preLowerL j (beamUnitary η hη x)+(Real.sqrt η:ℂ) • preLowerR j (beamUnitary η hη x) := by
  rw [covariance_preLowerL, covariance_preLowerR]
  exact (undo_rotation _ _ (beam_squares η hη) _ _).2.symm

theorem undo_preRaiseL (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    beamUnitary η hη (preRaiseL j x)=(Real.sqrt η:ℂ) • preRaiseL j (beamUnitary η hη x)-(Real.sqrt (1-η):ℂ) • preRaiseR j (beamUnitary η hη x) := by
  rw [covariance_preRaiseL, covariance_preRaiseR]
  exact (undo_rotation _ _ (beam_squares η hη) _ _).1.symm

theorem undo_preRaiseR (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n) (x : JointFock n) :
    beamUnitary η hη (preRaiseR j x)=(Real.sqrt (1-η):ℂ) • preRaiseL j (beamUnitary η hη x)+(Real.sqrt η:ℂ) • preRaiseR j (beamUnitary η hη x) := by
  rw [covariance_preRaiseL, covariance_preRaiseR]
  exact (undo_rotation _ _ (beam_squares η hη) _ _).2.symm

theorem expand_quadMinusL (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n)
    (x y : JointFock n) (Z : Fock n →L[ℂ] Fock n) :
    quadMinusL j x y (conjugate η hη Z)=
      (Real.sqrt (η):ℂ)^2*quadMinusL j (beamUnitary η hη x) (beamUnitary η hη y) (liftLeft Z)+
      (Real.sqrt (1-η):ℂ)^2*quadMinusR j (beamUnitary η hη x) (beamUnitary η hη y) (liftLeft Z)-
      (Real.sqrt η:ℂ)*(Real.sqrt (1-η):ℂ)*crossMinus j (beamUnitary η hη x) (beamUnitary η hη y) (liftLeft Z) := by
  unfold quadMinusL quadMinusR crossMinus
  simp only [conjugate_inner, undo_lowerL, undo_raiseL, undo_preLowerL,
    ← covariance_inverse_apply]
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  ring

theorem expand_quadMinusR (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n)
    (x y : JointFock n) (Z : Fock n →L[ℂ] Fock n) :
    quadMinusR j x y (conjugate η hη Z)=
      (Real.sqrt (1-η):ℂ)^2*quadMinusL j (beamUnitary η hη x) (beamUnitary η hη y) (liftLeft Z)+
      (Real.sqrt (η):ℂ)^2*quadMinusR j (beamUnitary η hη x) (beamUnitary η hη y) (liftLeft Z)+
      (Real.sqrt η:ℂ)*(Real.sqrt (1-η):ℂ)*crossMinus j (beamUnitary η hη x) (beamUnitary η hη y) (liftLeft Z) := by
  unfold quadMinusL quadMinusR crossMinus
  simp only [conjugate_inner, undo_lowerR, undo_raiseR, undo_preLowerR,
    ← covariance_inverse_apply]
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  ring

theorem expand_quadPlusL (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n)
    (x y : JointFock n) (Z : Fock n →L[ℂ] Fock n) :
    quadPlusL j x y (conjugate η hη Z)=
      (Real.sqrt (η):ℂ)^2*quadPlusL j (beamUnitary η hη x) (beamUnitary η hη y) (liftLeft Z)+
      (Real.sqrt (1-η):ℂ)^2*quadPlusR j (beamUnitary η hη x) (beamUnitary η hη y) (liftLeft Z)-
      (Real.sqrt η:ℂ)*(Real.sqrt (1-η):ℂ)*crossPlus j (beamUnitary η hη x) (beamUnitary η hη y) (liftLeft Z) := by
  unfold quadPlusL quadPlusR crossPlus
  simp only [conjugate_inner, undo_raiseL, undo_lowerL, undo_preRaiseL,
    ← covariance_inverse_apply]
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  ring

theorem expand_quadPlusR (η : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n)
    (x y : JointFock n) (Z : Fock n →L[ℂ] Fock n) :
    quadPlusR j x y (conjugate η hη Z)=
      (Real.sqrt (1-η):ℂ)^2*quadPlusL j (beamUnitary η hη x) (beamUnitary η hη y) (liftLeft Z)+
      (Real.sqrt (η):ℂ)^2*quadPlusR j (beamUnitary η hη x) (beamUnitary η hη y) (liftLeft Z)+
      (Real.sqrt η:ℂ)*(Real.sqrt (1-η):ℂ)*crossPlus j (beamUnitary η hη x) (beamUnitary η hη y) (liftLeft Z) := by
  unfold quadPlusL quadPlusR crossPlus
  simp only [conjugate_inner, undo_raiseR, undo_lowerR, undo_preRaiseR,
    ← covariance_inverse_apply]
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  ring

theorem generator_covariance (η a b : ℝ) (hη : η ∈ Set.Icc 0 1) (j : Fin n)
    (x y : JointFock n) (Z : Fock n →L[ℂ] Fock n) :
    ((η*a+(1-η)*b:ℝ)+1:ℂ)*quadMinusL j (beamUnitary η hη x) (beamUnitary η hη y) (liftLeft Z)+
      (η*a+(1-η)*b:ℂ)*quadPlusL j (beamUnitary η hη x) (beamUnitary η hη y) (liftLeft Z)=
      (a+1:ℂ)*quadMinusL j x y (conjugate η hη Z)+(a:ℂ)*quadPlusL j x y (conjugate η hη Z)+
      (b+1:ℂ)*quadMinusR j x y (conjugate η hη Z)+(b:ℂ)*quadPlusR j x y (conjugate η hη Z) := by
  rw [expand_quadMinusL,expand_quadPlusL,expand_quadMinusR,expand_quadPlusR,
    quadMinusR_zero,quadPlusR_zero]
  have hc : (Real.sqrt η:ℂ)^2=(η:ℂ) := by exact_mod_cast Real.sq_sqrt hη.1
  have hs : (Real.sqrt (1-η):ℂ)^2=(1-η:ℂ) := by exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hη.2)
  rw [hc,hs]
  push_cast
  have hh := cross_heat_zero j (beamUnitary η hη x) (beamUnitary η hη y) Z
  linear_combination (Real.sqrt η:ℂ)*(Real.sqrt (1-η):ℂ)*(a-b)*hh

theorem numberL_plus (j : Fin n) (x : JointFock n) (k e : NumberIndex n) :
    lowerL j (preRaiseL j x) (k,e)=(k j+1:ℂ)*inverse (inverse x) (k,e) := by
  rw [lowerL_apply]
  change _*raiseL j ((1+inverse) x) (upL j (k,e))=_
  rw [raiseL_up]
  have hw : (W (k,e):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (k,e)] : W (k,e)≠0)
  have hu : (W (k,e):ℂ)+1≠0 := by exact_mod_cast (by linarith [W_one_le (k,e)] : W (k,e)+1≠0)
  have hs : (Real.sqrt ((k j:ℝ)+1):ℂ)^2=((k j:ℝ)+1:ℂ) := by exact_mod_cast Real.sq_sqrt (by positivity : 0≤(k j:ℝ)+1)
  simp only [add_apply,one_apply_eq_self,lp.coeFn_add,Pi.add_apply,inverse_apply]
  push_cast
  field_simp
  linear_combination x (k,e)*hs

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

theorem tensorPreimage2_apply (x y : Fock n) (k e : NumberIndex n) :
    tensorPreimage2 x y (k,e)=(W (k,e):ℂ)^2*inverseWeight 3 x k*inverseWeight 3 y e := by
  have hk : (numberWeight k:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le k] : numberWeight k≠0)
  have he : (numberWeight e:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le e] : numberWeight e≠0)
  simp only [tensorPreimage2,lp.coeFn_sub,lp.coeFn_add,lp.coeFn_smul,Pi.sub_apply,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,tensor_apply,inverseWeight_apply,W,pow_one]
  push_cast
  field_simp
  ring

theorem tensorPreimage2_inverse (x y : Fock n) :
    inverse (tensorPreimage2 x y)=tensorPreimage x y := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  rw [inverse_apply,tensorPreimage2_apply,tensorPreimage_apply]
  have hw : (W (k,e):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (k,e)] : W (k,e)≠0)
  field_simp

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

theorem dissipator_summable (x y : I → JointFock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (A B C Z : JointFock n →L[ℂ] JointFock n) :
    Summable (fun i => inner ℂ (A (x i)) (Z (A (y i)))-
      (2:ℂ)⁻¹*(inner ℂ (B (x i)) (Z (C (y i)))+
        inner ℂ (C (x i)) (Z (B (y i))))) := by
  have ha := CrossEnsemble.pairing_summable
    (CrossEnsemble.applied_summable hy A) (CrossEnsemble.applied_summable hx A) Z
  have hb := CrossEnsemble.pairing_summable
    (CrossEnsemble.applied_summable hy C) (CrossEnsemble.applied_summable hx B) Z
  have hc := CrossEnsemble.pairing_summable
    (CrossEnsemble.applied_summable hy B) (CrossEnsemble.applied_summable hx C) Z
  exact ha.sub ((hb.add hc).mul_left (2:ℂ)⁻¹)

theorem quadMinusL_summable (j : Fin n) (x y : I → JointFock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (Z : JointFock n →L[ℂ] JointFock n) :
    Summable (fun i => quadMinusL j (x i) (y i) Z) :=
  dissipator_summable x y hx hy (lowerL j ∘L inverse) (inverse ∘L inverse) (raiseL j ∘L preLowerL j) Z

theorem quadPlusL_summable (j : Fin n) (x y : I → JointFock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (Z : JointFock n →L[ℂ] JointFock n) :
    Summable (fun i => quadPlusL j (x i) (y i) Z) :=
  dissipator_summable x y hx hy (raiseL j ∘L inverse) (inverse ∘L inverse) (lowerL j ∘L preRaiseL j) Z

theorem quadMinusR_summable (j : Fin n) (x y : I → JointFock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (Z : JointFock n →L[ℂ] JointFock n) :
    Summable (fun i => quadMinusR j (x i) (y i) Z) :=
  dissipator_summable x y hx hy (lowerR j ∘L inverse) (inverse ∘L inverse) (raiseR j ∘L preLowerR j) Z

theorem quadPlusR_summable (j : Fin n) (x y : I → JointFock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (Z : JointFock n →L[ℂ] JointFock n) :
    Summable (fun i => quadPlusR j (x i) (y i) Z) :=
  dissipator_summable x y hx hy (raiseR j ∘L inverse) (inverse ∘L inverse) (lowerR j ∘L preRaiseR j) Z

theorem generatorPairing_covariance (η a b : ℝ) (hη : η ∈ Set.Icc 0 1)
    (x y : I → JointFock n) (hx : Summable (fun i => ‖x i‖^2))
    (hy : Summable (fun i => ‖y i‖^2)) (Z : Fock n →L[ℂ] Fock n) :
    generatorPairingL (η*a+(1-η)*b)
      (fun i => beamUnitary η hη (x i)) (fun i => beamUnitary η hη (y i)) (liftLeft Z)=
    generatorPairingL a x y (conjugate η hη Z)+generatorPairingR b x y (conjugate η hη Z) := by
  have hx' := CrossEnsemble.applied_summable hx (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap
  have hy' := CrossEnsemble.applied_summable hy (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap
  change Summable (fun i => ‖beamUnitary η hη (x i)‖^2) at hx'
  change Summable (fun i => ‖beamUnitary η hη (y i)‖^2) at hy'
  unfold generatorPairingL generatorPairingR
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h1 := quadMinusL_summable j x y hx hy (conjugate η hη Z)
  have h2 := quadPlusL_summable j x y hx hy (conjugate η hη Z)
  have h3 := quadMinusR_summable j x y hx hy (conjugate η hη Z)
  have h4 := quadPlusR_summable j x y hx hy (conjugate η hη Z)
  have h5 := quadMinusL_summable j _ _ hx' hy' (liftLeft Z)
  have h6 := quadPlusL_summable j _ _ hx' hy' (liftLeft Z)
  have hh := congrArg (fun f : I → ℂ => ∑' i, f i)
    (funext (fun i => generator_covariance η a b hη j (x i) (y i) Z))
  have hl := (h5.mul_left ((η*a+(1-η)*b:ℝ)+1:ℂ)).tsum_add
    (h6.mul_left ((η:ℂ)*a+(1-(η:ℂ))*b))
  have hr := (((h1.mul_left ((a:ℂ)+1)).add (h2.mul_left (a:ℂ))).add
    (h3.mul_left ((b:ℂ)+1))).tsum_add (h4.mul_left (b:ℂ))
  rw [hl,hr,((h1.mul_left ((a:ℂ)+1)).add (h2.mul_left (a:ℂ))).tsum_add
    (h3.mul_left ((b:ℂ)+1)),(h1.mul_left ((a:ℂ)+1)).tsum_add (h2.mul_left (a:ℂ))] at hh
  simp only [tsum_mul_left] at hh
  convert hh using 1 <;> push_cast <;> ring

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

theorem lowerL_second_inverse_apply (j : Fin n) (x : JointFock n) (k e : NumberIndex n) :
    lowerL j (inverse x) (k,e)=(Real.sqrt ((k j:ℝ)+1):ℂ)*inverse (inverse x) (up j k,e) := by
  exact lowerL_inverse_apply j (inverse x) k e

theorem raiseL_second_inverse_apply (j : Fin n) (x : JointFock n) (k e : NumberIndex n) :
    raiseL j (inverse x) (k,e)=
      (if k j=0 then (0:ℂ) else (Real.sqrt (k j:ℝ):ℂ))*inverse (inverse x) (down j k,e) := by
  by_cases hk : k j=0
  · rw [raiseL_zero j _ (k,e) hk,ite_eq_left hk,zero_mul]
  · rw [ite_eq_right hk]
    obtain ⟨a,rfl⟩ : ∃ a,k=up j a := ⟨down j k,(up_down j k (Nat.pos_of_ne_zero hk)).symm⟩
    change raiseL j (inverse x) (upL j (a,e))=_
    rw [raiseL_up,down_up,up_same]
    have hw : (W (a,e):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (a,e)] : W (a,e)≠0)
    simp only [inverse_apply]
    push_cast
    field_simp

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

theorem single_number_third_apply (j : Fin n) (u : Bool) (x : Fock n) (k : NumberIndex n) :
    inverseWeight 2 (modeBound j u x) k=
      ((k j:ℂ)+(if u then 1 else 0))*inverseWeight 3 x k := by
  have hk : (numberWeight k:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le k] : numberWeight k≠0)
  simp only [inverseWeight_apply,modeBound_apply]
  push_cast
  cases u <;> simp only [Bool.false_eq_true,↓reduceIte,add_zero] <;> field_simp <;> push_cast <;> ring

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

theorem slice_dissipator (x y z : I → JointFock n) (u v w : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (hz : Summable (fun i => ‖z i‖^2)) (hu : Summable (fun k => ‖u k‖^2))
    (hv : Summable (fun k => ‖v k‖^2)) (hw : Summable (fun k => ‖w k‖^2))
    (f g : NumberIndex n → NumberIndex n) (c d : NumberIndex n → ℂ)
    (hyx : ∀ i k e, y i (k,e)=c k*x i (f k,e))
    (hzx : ∀ i k e, z i (k,e)=d k*x i (g k,e))
    (hvu : ∀ i k, v i k=c k*u i (f k)) (hwu : ∀ i k, w i k=d k*u i (g k))
    (he : CrossEnsemble.operator (fun ie : I × NumberIndex n => slice (x ie.1) ie.2)
        (fun ie : I × NumberIndex n => slice (x ie.1) ie.2)=CrossEnsemble.operator u u)
    (Z : Fock n →L[ℂ] Fock n) :
    (∑' i, (inner ℂ (y i) (liftLeft Z (y i))-
      (2:ℂ)⁻¹*(inner ℂ (x i) (liftLeft Z (z i))+inner ℂ (z i) (liftLeft Z (x i)))))=
    CrossEnsemble.pairing v v Z-(2:ℂ)⁻¹*(CrossEnsemble.pairing w u Z+CrossEnsemble.pairing u w Z) := by
  have hxs := slice_family_summable x hx
  have hys := slice_family_summable y hy
  have hzs := slice_family_summable z hz
  have h1 := CrossEnsemble.shifted_both_operator_eq _ _ _ _ hxs hys hu hv f c
    (fun ie k => hyx ie.1 k ie.2) hvu he
  have h2 := CrossEnsemble.shifted_left_operator_eq _ _ _ _ hxs hzs hu hw g d
    (fun ie k => hzx ie.1 k ie.2) hwu he
  have h3 := CrossEnsemble.shifted_right_operator_eq _ _ _ _ hxs hzs hu hw g d
    (fun ie k => hzx ie.1 k ie.2) hwu he
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hp1 := CrossEnsemble.pairing_eq_of_operator_eq bas hys hys hv hv h1 Z
  have hp2 := CrossEnsemble.pairing_eq_of_operator_eq bas hzs hxs hw hu h2 Z
  have hp3 := CrossEnsemble.pairing_eq_of_operator_eq bas hxs hzs hu hw h3 Z
  rw [(CrossEnsemble.pairing_summable hy hy (liftLeft Z)).tsum_sub
    (((CrossEnsemble.pairing_summable hz hx (liftLeft Z)).add
      (CrossEnsemble.pairing_summable hx hz (liftLeft Z))).mul_left _),tsum_mul_left,
    (CrossEnsemble.pairing_summable hz hx (liftLeft Z)).tsum_add
      (CrossEnsemble.pairing_summable hx hz (liftLeft Z))]
  change CrossEnsemble.pairing y y (liftLeft Z)-(2:ℂ)⁻¹*
    (CrossEnsemble.pairing z x (liftLeft Z)+CrossEnsemble.pairing x z (liftLeft Z))=_
  rw [pairing_liftLeft _ _ hy hy,pairing_liftLeft _ _ hz hx,pairing_liftLeft _ _ hx hz,hp1,hp2,hp3]

theorem output_generator (r : ℝ) (x : I → JointFock n) (z : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hz : Summable (fun j => ‖z j‖^2))
    (he : CrossEnsemble.operator
        (fun ie : I × NumberIndex n => slice (inverse (inverse (x ie.1))) ie.2)
        (fun ie : I × NumberIndex n => slice (inverse (inverse (x ie.1))) ie.2)=
      CrossEnsemble.operator (fun j => inverseWeight 3 (z j)) (fun j => inverseWeight 3 (z j)))
    (Z : Fock n →L[ℂ] Fock n) :
    generatorPairingL r x x (liftLeft Z)=singleGeneratorPairing r z Z := by
  unfold generatorPairingL singleGeneratorPairing
  apply Finset.sum_congr rfl
  intro j _
  have hi := CrossEnsemble.applied_summable hx (inverse ∘L inverse)
  have hl := CrossEnsemble.applied_summable hx (lowerL j ∘L inverse)
  have hr := CrossEnsemble.applied_summable hx (raiseL j ∘L inverse)
  have hm := CrossEnsemble.applied_summable hx (raiseL j ∘L preLowerL j)
  have hn := CrossEnsemble.applied_summable hx (lowerL j ∘L preRaiseL j)
  have hzi := CrossEnsemble.applied_summable hz (inverseWeight 3)
  have hzl := CrossEnsemble.applied_summable hz (sandwich 0 3 (by omega) j)
  have hzr := CrossEnsemble.applied_summable hz (creationSandwich 0 3 (by omega) j)
  have hzm := CrossEnsemble.applied_summable hz (inverseWeight 2 ∘L modeBound j false)
  have hzn := CrossEnsemble.applied_summable hz (inverseWeight 2 ∘L modeBound j true)
  have hm' := slice_dissipator _ _ _ _ _ _ hi hl hm hzi hzl hzm
    (up j) id (fun k => (Real.sqrt ((k j:ℝ)+1):ℂ)) (fun k => (k j:ℂ))
    (fun i k e => lowerL_second_inverse_apply j (x i) k e)
    (fun i k e => numberL_minus j (x i) k e)
    (fun i k => single_lower_third_apply j (z i) k)
    (fun i k => by simpa only [Bool.false_eq_true,↓reduceIte,add_zero,id_eq,ContinuousLinearMap.comp_apply] using single_number_third_apply j false (z i) k)
    he Z
  have hp' := slice_dissipator _ _ _ _ _ _ hi hr hn hzi hzr hzn
    (down j) id (fun k => if k j=0 then (0:ℂ) else (Real.sqrt (k j:ℝ):ℂ)) (fun k => (k j:ℂ)+1)
    (fun i k e => raiseL_second_inverse_apply j (x i) k e)
    (fun i k e => numberL_plus j (x i) k e)
    (fun i k => single_raise_third_apply j (z i) k)
    (fun i k => by simpa only [↓reduceIte,id_eq,ContinuousLinearMap.comp_apply] using single_number_third_apply j true (z i) k)
    he Z
  exact congrArg₂ HAdd.hAdd (congrArg (fun t : ℂ => ((r+1:ℝ):ℂ)*t) hm')
    (congrArg (fun t : ℂ => (r:ℂ)*t) hp')
end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

theorem physical_product_generator (η a b : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (hτ : IsBeamSplitterOutput η ρ σ τ)
    (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hz : Summable (fun k => ‖z k‖^2))
    (hxn : HasSum (fun i => ‖inverseWeight 3 (x i)‖^2) 1)
    (hyn : HasSum (fun j => ‖inverseWeight 3 (y j)‖^2) 1)
    (hex : TraceEnsemble.operator (fun i => inverseWeight 3 (x i))=ρ.op)
    (hey : TraceEnsemble.operator (fun j => inverseWeight 3 (y j))=σ.op)
    (hez : TraceEnsemble.operator (fun k => inverseWeight 3 (z k))=τ.op)
    (Z : Fock n →L[ℂ] Fock n) :
    singleGeneratorPairing (η*a+(1-η)*b) z Z=
      singleGeneratorPairing a x
        (conditionalLeft (fun j => inverseWeight 3 (y j)) hyn (conjugate η hη Z))+
      singleGeneratorPairing b y
        (conditionalRight (fun i => inverseWeight 3 (x i)) hxn (conjugate η hη Z)) := by
  have hs := tensorPreimage2_summable x y hx hy
  have hu : Summable (fun ij : I × J => ‖beamUnitary η hη (tensorPreimage2 (x ij.1) (y ij.2))‖^2) := by
    simpa only [LinearIsometryEquiv.norm_map] using hs
  have he := physical_weighted_output η hη ρ σ τ hτ x y z hxn hyn hex hey hez
  have hi (u v : Fock n) : inverse (inverse (beamUnitary η hη (tensorPreimage2 u v)))=
      inverse (beamUnitary η hη (tensorPreimage u v)) := by
    rw [covariance_inverse_apply,tensorPreimage2_inverse]
  have he' : CrossEnsemble.operator
      (fun ie : (I × J) × NumberIndex n => slice (inverse (inverse
        (beamUnitary η hη (tensorPreimage2 (x ie.1.1) (y ie.1.2))))) ie.2)
      (fun ie : (I × J) × NumberIndex n => slice (inverse (inverse
        (beamUnitary η hη (tensorPreimage2 (x ie.1.1) (y ie.1.2))))) ie.2)=
      CrossEnsemble.operator (fun k => inverseWeight 3 (z k)) (fun k => inverseWeight 3 (z k)) := by
    simpa only [hi] using he
  rw [← output_generator _ _ z hu hz he' Z]
  rw [generatorPairing_covariance η a b hη _ _ hs hs Z]
  rw [generatorPairingL_product a x y hx hy hyn, generatorPairingR_product b x y hx hy hxn]
end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

theorem tensorRatioCLM_norm (z : JointFock n) : ‖tensorRatioCLM z‖≤‖z‖ := by
  have hb : ‖tensorRatioCLM z‖ ≤ 1*‖z‖ := WeightedShift.pull_bound id Function.injective_id
    (fun ke : NumberIndex n × NumberIndex n => ((tensorRatio ke)^2:ℂ))
    1 (by norm_num) (fun ke => by simpa only [Complex.real_smul,mul_one,Complex.ofReal_pow] using ratioSquare_norm (tensorRatio_mem ke)) z
  simpa only [one_mul] using hb

theorem retainedRatioCLM_norm (z : JointFock n) : ‖retainedRatioCLM z‖≤‖z‖ := by
  have hb : ‖retainedRatioCLM z‖ ≤ 1*‖z‖ := WeightedShift.pull_bound id Function.injective_id
    (fun ke : NumberIndex n × NumberIndex n => ((retainedRatio ke)^2:ℂ))
    1 (by norm_num) (fun ke => by simpa only [Complex.real_smul,mul_one,Complex.ofReal_pow] using ratioSquare_norm (retainedRatio_mem ke)) z
  simpa only [one_mul] using hb

theorem weightedColumn_norm (η : ℝ) (hη : η ∈ Set.Icc 0 1) (y : Fock n) :
    ‖weightedColumn η hη y‖≤‖y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg y)
  intro x
  rw [weightedColumn_apply]
  calc
    _ ≤ ‖beamUnitary η hη (tensorRatioCLM (tensor x y))‖ := retainedRatioCLM_norm _
    _ = ‖tensorRatioCLM (tensor x y)‖ := (beamUnitary η hη).norm_map _
    _ ≤ ‖tensor x y‖ := tensorRatioCLM_norm _
    _ = ‖y‖*‖x‖ := by rw [tensor_norm,mul_comm]

theorem weightedColumn_summable {I : Type*} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (y : I → Fock n) (hy : Summable (fun i => ‖y i‖^2)) :
    Summable (fun i => ‖weightedColumn η hη (y i)‖^2) :=
  hy.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i =>
    pow_le_pow_left₀ (norm_nonneg _) (weightedColumn_norm η hη (y i)) 2)

theorem tensorRatio_inverse (x y : Fock n) :
    inverse (inverse (tensorRatioCLM (tensor x y)))=tensor (inverseWeight 2 x) (inverseWeight 2 y) := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  have hw : (W (k,e):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (k,e)] : W (k,e)≠0)
  have hk : (numberWeight k:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le k] : numberWeight k≠0)
  have he : (numberWeight e:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le e] : numberWeight e≠0)
  simp only [inverse_apply,tensorRatioCLM,WeightedShift.pullCLM_apply,tensorRatio,
    id_eq,tensor_apply,inverseWeight_apply,Complex.ofReal_div,Complex.ofReal_mul]
  field_simp

theorem retainedRatio_inverse (z : JointFock n) :
    liftLeft (inverseWeight 2) (retainedRatioCLM z)=inverse (inverse z) := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  have hw : (W (k,e):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (k,e)] : W (k,e)≠0)
  have hk : (numberWeight k:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le k] : numberWeight k≠0)
  simp only [liftLeft_apply,inverseWeight_apply,slice_apply,retainedRatioCLM,
    WeightedShift.pullCLM_apply,retainedRatio,id_eq,inverse_apply,Complex.ofReal_div]
  field_simp

theorem weightedColumn_inverse (η : ℝ) (hη : η ∈ Set.Icc 0 1) (x y : Fock n) :
    liftLeft (inverseWeight 2) (weightedColumn η hη y x)=
      beamUnitary η hη (tensor (inverseWeight 2 x) (inverseWeight 2 y)) := by
  rw [weightedColumn_apply]
  rw [retainedRatio_inverse,covariance_inverse_apply,covariance_inverse_apply,tensorRatio_inverse]

end BeamLadder

namespace EnsemblePullback

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {I : Type*}

theorem compression_norm (V : E →L[ℂ] F) (Z : F →L[ℂ] F) :
    ‖compression V Z‖ ≤ ‖Z‖*‖V‖^2 := by
  calc
    _ ≤ ‖V.adjoint‖*‖Z ∘L V‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖V.adjoint‖*(‖Z‖*‖V‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = _ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring

theorem summable_compression {V : I → E →L[ℂ] F} (hV : Summable (fun i => ‖V i‖^2))
    (Z : F →L[ℂ] F) : Summable (fun i => compression (V i) Z) := by
  apply Summable.of_norm_bounded (hV.mul_left ‖Z‖)
  exact fun i => compression_norm _ _

theorem compression_entry (V : E →L[ℂ] F) (Z : F →L[ℂ] F) (x y : E) :
    inner ℂ x (compression V Z y) = inner ℂ (V x) (Z (V y)) := by
  exact ContinuousLinearMap.adjoint_inner_right V x (Z (V y))

theorem hasSum_entry {V : I → E →L[ℂ] F} (hV : Summable (fun i => ‖V i‖^2))
    (Z : F →L[ℂ] F) (x y : E) :
    HasSum (fun i => inner ℂ (V i x) (Z (V i y))) (inner ℂ x (pullback V Z y)) := by
  convert! (((summable_compression hV Z).hasSum).mapL
    (ContinuousLinearMap.apply ℂ E y)).mapL (innerSL ℂ x) using 1
  ext i
  exact (compression_entry _ _ _ _).symm

end

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {I J : Type*}

omit [CompleteSpace E] [CompleteSpace F] in
theorem applied_family_summable (V : J → E →L[ℂ] F)
    (hV : Summable (fun j => ‖V j‖^2)) (x : I → E)
    (hx : Summable (fun i => ‖x i‖^2)) :
    Summable (fun ij : I × J => ‖V ij.2 (x ij.1)‖^2) := by
  have hs := hx.mul_of_nonneg hV (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  apply hs.of_nonneg_of_le (fun _ => sq_nonneg _)
  intro ij
  calc
    _ ≤ (‖V ij.2‖*‖x ij.1‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.le_opNorm _ _) 2
    _ = ‖x ij.1‖^2*‖V ij.2‖^2 := by ring

theorem pairing_pullback (V : J → E →L[ℂ] F)
    (hV : Summable (fun j => ‖V j‖^2)) (x y : I → E)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun i => ‖y i‖^2))
    (Z : F →L[ℂ] F) :
    CrossEnsemble.pairing (fun ij : I × J => V ij.2 (x ij.1))
      (fun ij : I × J => V ij.2 (y ij.1)) Z =
      CrossEnsemble.pairing x y (pullback V Z) := by
  have hs := CrossEnsemble.pairing_summable (applied_family_summable V hV x hx)
    (applied_family_summable V hV y hy) Z
  exact (hs.hasSum.prod_fiberwise (fun i => hasSum_entry hV Z (y i) (x i))).tsum_eq.symm
end EnsemblePullback

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

theorem weightedSlices_summable (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (y : J → Fock n) (hy : Summable (fun j => ‖y j‖^2))
    (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2)) :
    Summable (fun ije => ‖weightedSlices η hη y x ije‖^2) :=
  by
  have hs : Summable (fun ij : I × J => ‖weightedColumn η hη (y ij.2) (x ij.1)‖^2) :=
    EnsemblePullback.applied_family_summable
      (fun j => weightedColumn η hη (y j)) (weightedColumn_summable η hη y hy) x hx
  exact slice_family_summable (fun ij : I × J => weightedColumn η hη (y ij.2) (x ij.1)) hs

theorem weighted_pairing_slicing (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (y : J → Fock n) (hy : Summable (fun j => ‖y j‖^2))
    (u v : I → Fock n) (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (B : Fock n →L[ℂ] Fock n) :
    CrossEnsemble.pairing (weightedSlices η hη y u) (weightedSlices η hη y v) B =
      CrossEnsemble.pairing u v (weightedConditional η hη y B) := by
  have hV := weightedColumn_summable η hη y hy
  unfold weightedSlices weightedConditional
  rw [← pairing_liftLeft _ _
    (EnsemblePullback.applied_family_summable _ hV u hu)
    (EnsemblePullback.applied_family_summable _ hV v hv)]
  exact EnsemblePullback.pairing_pullback _ hV u v hu hv (liftLeft B)

end BeamLadder

namespace CrossEnsemble
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {I : Type*}
theorem pairing_selfAdjoint_sandwich (x y : I → E) (P Z : E →L[ℂ] E)
    (hP : IsSelfAdjoint P) :
    pairing x y (P ∘L Z ∘L P)=pairing (fun i => P (x i)) (fun i => P (y i)) Z := by
  unfold pairing
  apply tsum_congr
  intro i
  simp only [ContinuousLinearMap.comp_apply]
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP (y i) (Z (P (x i)))).symm
end CrossEnsemble

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

end Annihilation

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I : Type*}

theorem gain_inverse_apply (j : Fin n) (u : Bool) (x : Fock n) :
    inverseWeight 2 (gain j u x)=
      if u then creationSandwich 0 3 (by omega) j x else sandwich 0 3 (by omega) j x := by
  cases u
  · exact congrArg (fun T : Fock n →L[ℂ] Fock n => T x) (sandwich_factor 2 3 (by omega) j).symm
  · exact congrArg (fun T : Fock n →L[ℂ] Fock n => T x) (creationSandwich_factor 2 3 (by omega) j).symm

theorem inverse_two_one (x : Fock n) : inverseWeight 2 (inverseWeight 1 x)=inverseWeight 3 x :=
  congrArg (fun T : Fock n →L[ℂ] Fock n => T x) (inverseWeight_add 2 1).symm

theorem weighted_pairing_physical (r : ℝ) (x : I → Fock n)
    (Z : Fock n →L[ℂ] Fock n) :
    WeightedGenerator.pairing r x (inverseWeight 2 ∘L Z ∘L inverseWeight 2)=
      singleGeneratorPairing r x Z := by
  simp only [WeightedGenerator.pairing,singleGeneratorPairing,
    CrossEnsemble.pairing_selfAdjoint_sandwich _ _ _ _ (inverseWeight_selfAdjoint 2),
    gain_inverse_apply,inverse_two_one,Bool.false_eq_true,ite_false,ite_true]
end BeamLadder

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I K : Type*}

theorem pushedPairing_hasSum {J : Type*} (b : HilbertBasis J ℂ (Fock n))
    (F : (I → Fock n) → K → Fock n)
    (hF : ∀ u, Summable (fun i => ‖u i‖^2) → Summable (fun k => ‖F u k‖^2))
    (r : ℝ) (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun k => inner ℂ (b k) (Z (pushedGenerator F r x (b k)))) (pushedPairing F r x Z) := by
  have ha (j : Fin n) (u : Bool) := hF _ (CrossEnsemble.applied_summable hx (gain j u))
  have hb (j : Fin n) (u : Bool) := hF _ (CrossEnsemble.applied_summable hx (modeBound j u))
  have hc := hF _ (CrossEnsemble.applied_summable hx (inverseWeight 1))
  have h (j : Fin n) (u : Bool) :=
    (CrossEnsemble.pairing_trace b (ha j u) (ha j u) Z).sub
      (((CrossEnsemble.pairing_trace b (hb j u) hc Z).add
        (CrossEnsemble.pairing_trace b hc (hb j u) Z)).mul_left (2:ℂ)⁻¹)
  have hh := hasSum_sum fun j (_hj : j ∈ (Finset.univ : Finset (Fin n))) =>
    ((h j false).mul_left ((r+1:ℝ):ℂ)).add ((h j true).mul_left (r:ℂ))
  convert! hh using 1
  ext k
  simp only [pushedGenerator,pushedDissipator,sum_apply,add_apply,sub_apply,smul_apply,
    map_sum,map_add,map_sub,map_smul,inner_sum,inner_sub_right,inner_add_right,inner_smul_right]

theorem pushedPairing_slicing (F : (I → Fock n) → K → Fock n)
    (B Z : Fock n →L[ℂ] Fock n)
    (hF : ∀ u v, Summable (fun i => ‖u i‖^2) → Summable (fun i => ‖v i‖^2) →
      CrossEnsemble.pairing (F u) (F v) B=CrossEnsemble.pairing u v Z)
    (r : ℝ) (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2)) :
    pushedPairing F r x B=pairing r x Z := by
  have ha (j : Fin n) (u : Bool) := CrossEnsemble.applied_summable hx (gain j u)
  have hb (j : Fin n) (u : Bool) := CrossEnsemble.applied_summable hx (modeBound j u)
  have hc := CrossEnsemble.applied_summable hx (inverseWeight 1)
  unfold pushedPairing pairing
  apply Finset.sum_congr rfl
  intro j _
  rw [hF _ _ (ha j false) (ha j false),hF _ _ (hb j false) hc,hF _ _ hc (hb j false),
    hF _ _ (ha j true) (ha j true),hF _ _ (hb j true) hc,hF _ _ hc (hb j true)]
end WeightedGenerator

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

theorem weightedSlices_inverse (η : ℝ) (hη : η ∈ Set.Icc 0 1) (y : J → Fock n)
    (u : I → Fock n) (ije : (I × J) × NumberIndex n) :
    inverseWeight 2 (weightedSlices η hη y u ije)=
      slice (beamUnitary η hη (tensor (inverseWeight 2 (u ije.1.1)) (inverseWeight 2 (y ije.1.2)))) ije.2 := by
  unfold weightedSlices
  rw [← slice_liftLeft,weightedColumn_inverse]

theorem weighted_pairing_bounded_physical (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (y : J → Fock n) (hyn : HasSum (fun j => ‖inverseWeight 2 (y j)‖^2) 1)
    (u v : I → Fock n) (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (Z : Fock n →L[ℂ] Fock n) :
    CrossEnsemble.pairing (weightedSlices η hη y u) (weightedSlices η hη y v)
      (inverseWeight 2 ∘L Z ∘L inverseWeight 2)=
    CrossEnsemble.pairing (fun i => inverseWeight 2 (u i)) (fun i => inverseWeight 2 (v i))
      (conditionalLeft (fun j => inverseWeight 2 (y j)) hyn (conjugate η hη Z)) := by
  have hu' := CrossEnsemble.applied_summable hu (inverseWeight 2)
  have hv' := CrossEnsemble.applied_summable hv (inverseWeight 2)
  have hs := tensorFamily_summable (fun i => inverseWeight 2 (u i)) _ hu' hyn.summable
  have ht := tensorFamily_summable (fun i => inverseWeight 2 (v i)) _ hv' hyn.summable
  have hsu : Summable (fun ij : I × J => ‖beamUnitary η hη (tensor (inverseWeight 2 (u ij.1)) (inverseWeight 2 (y ij.2)))‖^2) := by
    simpa only [LinearIsometryEquiv.norm_map] using hs
  have htu : Summable (fun ij : I × J => ‖beamUnitary η hη (tensor (inverseWeight 2 (v ij.1)) (inverseWeight 2 (y ij.2)))‖^2) := by
    simpa only [LinearIsometryEquiv.norm_map] using ht
  rw [CrossEnsemble.pairing_selfAdjoint_sandwich _ _ _ _ (inverseWeight_selfAdjoint 2)]
  simp only [weightedSlices_inverse]
  rw [← pairing_liftLeft _ _ hsu htu]
  calc
    _ = CrossEnsemble.pairing
        (fun ij : I × J => tensor (inverseWeight 2 (u ij.1)) (inverseWeight 2 (y ij.2)))
        (fun ij : I × J => tensor (inverseWeight 2 (v ij.1)) (inverseWeight 2 (y ij.2))) (conjugate η hη Z) := by
      unfold CrossEnsemble.pairing
      apply tsum_congr
      intro ij
      exact (conjugate_inner η hη Z _ _).symm
    _ = _ := pairing_conditionalLeft _ _ _ hu' hv' hyn _

theorem weightedColumnRight_norm (η : ℝ) (hη : η ∈ Set.Icc 0 1) (y : Fock n) :
    ‖weightedColumnRight η hη y‖≤‖y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg y)
  intro x
  rw [weightedColumnRight_apply]
  calc
    _ ≤ ‖beamUnitary η hη (tensorRatioCLM (tensor y x))‖ := retainedRatioCLM_norm _
    _ = ‖tensorRatioCLM (tensor y x)‖ := (beamUnitary η hη).norm_map _
    _ ≤ ‖tensor y x‖ := tensorRatioCLM_norm _
    _ = ‖y‖*‖x‖ := tensor_norm y x

theorem weightedColumnRight_summable (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (y : J → Fock n) (hy : Summable (fun i => ‖y i‖^2)) :
    Summable (fun i => ‖weightedColumnRight η hη (y i)‖^2) :=
  hy.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i =>
    pow_le_pow_left₀ (norm_nonneg _) (weightedColumnRight_norm η hη (y i)) 2)

theorem weightedColumnRight_inverse (η : ℝ) (hη : η ∈ Set.Icc 0 1) (x y : Fock n) :
    liftLeft (inverseWeight 2) (weightedColumnRight η hη y x)=
      beamUnitary η hη (tensor (inverseWeight 2 y) (inverseWeight 2 x)) := by
  rw [weightedColumnRight_apply,retainedRatio_inverse,covariance_inverse_apply,
    covariance_inverse_apply,tensorRatio_inverse]

theorem weightedSlicesRight_summable (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (y : J → Fock n) (hy : Summable (fun j => ‖y j‖^2))
    (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2)) :
    Summable (fun ije => ‖weightedSlicesRight η hη y x ije‖^2) := by
  have hs : Summable (fun ij : I × J => ‖weightedColumnRight η hη (y ij.2) (x ij.1)‖^2) :=
    EnsemblePullback.applied_family_summable
      (fun j => weightedColumnRight η hη (y j)) (weightedColumnRight_summable η hη y hy) x hx
  exact slice_family_summable (fun ij : I × J => weightedColumnRight η hη (y ij.2) (x ij.1)) hs

theorem weighted_pairing_slicing_right (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (y : J → Fock n) (hy : Summable (fun j => ‖y j‖^2))
    (u v : I → Fock n) (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (B : Fock n →L[ℂ] Fock n) :
    CrossEnsemble.pairing (weightedSlicesRight η hη y u) (weightedSlicesRight η hη y v) B =
      CrossEnsemble.pairing u v (weightedConditionalRight η hη y B) := by
  have hV := weightedColumnRight_summable η hη y hy
  unfold weightedSlicesRight weightedConditionalRight
  rw [← pairing_liftLeft _ _
    (EnsemblePullback.applied_family_summable _ hV u hu)
    (EnsemblePullback.applied_family_summable _ hV v hv)]
  exact EnsemblePullback.pairing_pullback _ hV u v hu hv (liftLeft B)

theorem weightedSlicesRight_inverse (η : ℝ) (hη : η ∈ Set.Icc 0 1) (y : J → Fock n)
    (u : I → Fock n) (ije : (I × J) × NumberIndex n) :
    inverseWeight 2 (weightedSlicesRight η hη y u ije)=
      slice (beamUnitary η hη (tensor (inverseWeight 2 (y ije.1.2)) (inverseWeight 2 (u ije.1.1)))) ije.2 := by
  unfold weightedSlicesRight
  rw [← slice_liftLeft,weightedColumnRight_inverse]

theorem weighted_pairing_bounded_physical_right (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (y : J → Fock n) (hyn : HasSum (fun j => ‖inverseWeight 2 (y j)‖^2) 1)
    (u v : I → Fock n) (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (Z : Fock n →L[ℂ] Fock n) :
    CrossEnsemble.pairing (weightedSlicesRight η hη y u) (weightedSlicesRight η hη y v)
      (inverseWeight 2 ∘L Z ∘L inverseWeight 2)=
    CrossEnsemble.pairing (fun i => inverseWeight 2 (u i)) (fun i => inverseWeight 2 (v i))
      (conditionalRight (fun j => inverseWeight 2 (y j)) hyn (conjugate η hη Z)) := by
  have hu' := CrossEnsemble.applied_summable hu (inverseWeight 2)
  have hv' := CrossEnsemble.applied_summable hv (inverseWeight 2)
  have hs := (tensorFamily_summable _ (fun i => inverseWeight 2 (u i)) hyn.summable hu').prod_symm
  have ht := (tensorFamily_summable _ (fun i => inverseWeight 2 (v i)) hyn.summable hv').prod_symm
  have hsu : Summable (fun ij : I × J => ‖beamUnitary η hη (tensor (inverseWeight 2 (y ij.2)) (inverseWeight 2 (u ij.1)))‖^2) := by
    simpa only [LinearIsometryEquiv.norm_map,Prod.swap] using hs
  have htu : Summable (fun ij : I × J => ‖beamUnitary η hη (tensor (inverseWeight 2 (y ij.2)) (inverseWeight 2 (v ij.1)))‖^2) := by
    simpa only [LinearIsometryEquiv.norm_map,Prod.swap] using ht
  rw [CrossEnsemble.pairing_selfAdjoint_sandwich _ _ _ _ (inverseWeight_selfAdjoint 2)]
  simp only [weightedSlicesRight_inverse]
  rw [← pairing_liftLeft _ _ hsu htu]
  calc
    _ = CrossEnsemble.pairing
        (fun ji : J × I => tensor (inverseWeight 2 (y ji.1)) (inverseWeight 2 (u ji.2)))
        (fun ji : J × I => tensor (inverseWeight 2 (y ji.1)) (inverseWeight 2 (v ji.2))) (conjugate η hη Z) := by
      unfold CrossEnsemble.pairing
      simp only [← conjugate_inner]
      simpa only [Equiv.prodComm_apply,Prod.swap] using
        (Equiv.prodComm I J).tsum_eq (fun ji : J × I =>
          inner ℂ (tensor (inverseWeight 2 (y ji.1)) (inverseWeight 2 (v ji.2)))
            (conjugate η hη Z (tensor (inverseWeight 2 (y ji.1)) (inverseWeight 2 (u ji.2)))))
    _ = _ := pairing_conditionalRight _ _ _ hyn hu' hv' _
end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

theorem weighted_pushed_pairing_physical (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (y : J → Fock n) (hyn : HasSum (fun j => ‖inverseWeight 2 (y j)‖^2) 1)
    (r : ℝ) (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (Z : Fock n →L[ℂ] Fock n) :
    WeightedGenerator.pushedPairing (weightedSlices η hη y) r x
      (inverseWeight 2 ∘L Z ∘L inverseWeight 2)=
    singleGeneratorPairing r x
      (conditionalLeft (fun j => inverseWeight 2 (y j)) hyn (conjugate η hη Z)) := by
  rw [← weighted_pairing_physical]
  apply WeightedGenerator.pushedPairing_slicing _ _ _ _ r x hx
  intro u v hu hv
  rw [weighted_pairing_bounded_physical η hη y hyn u v hu hv Z,
    CrossEnsemble.pairing_selfAdjoint_sandwich _ _ _ _ (inverseWeight_selfAdjoint 2)]

theorem weighted_pushed_pairing_physical_right (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (y : J → Fock n) (hyn : HasSum (fun j => ‖inverseWeight 2 (y j)‖^2) 1)
    (r : ℝ) (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (Z : Fock n →L[ℂ] Fock n) :
    WeightedGenerator.pushedPairing (weightedSlicesRight η hη y) r x
      (inverseWeight 2 ∘L Z ∘L inverseWeight 2)=
    singleGeneratorPairing r x
      (conditionalRight (fun j => inverseWeight 2 (y j)) hyn (conjugate η hη Z)) := by
  rw [← weighted_pairing_physical]
  apply WeightedGenerator.pushedPairing_slicing _ _ _ _ r x hx
  intro u v hu hv
  rw [weighted_pairing_bounded_physical_right η hη y hyn u v hu hv Z,
    CrossEnsemble.pairing_selfAdjoint_sandwich _ _ _ _ (inverseWeight_selfAdjoint 2)]

theorem weighted_product_generator (η a b : ℝ) (hη : η ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (hτ : IsBeamSplitterOutput η ρ σ τ)
    (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hz : Summable (fun k => ‖z k‖^2))
    (hxn : HasSum (fun i => ‖inverseWeight 3 (x i)‖^2) 1)
    (hyn : HasSum (fun j => ‖inverseWeight 3 (y j)‖^2) 1)
    (hex : TraceEnsemble.operator (fun i => inverseWeight 3 (x i))=ρ.op)
    (hey : TraceEnsemble.operator (fun j => inverseWeight 3 (y j))=σ.op)
    (hez : TraceEnsemble.operator (fun k => inverseWeight 3 (z k))=τ.op)
    (B : Fock n →L[ℂ] Fock n) :
    WeightedGenerator.pairing (η*a+(1-η)*b) z B=
      WeightedGenerator.pairing a x
        (weightedConditional η hη (fun j => inverseWeight 1 (y j)) B)+
      WeightedGenerator.pairing b y
        (weightedConditionalRight η hη (fun i => inverseWeight 1 (x i)) B) := by
  let y2 := fun j => inverseWeight 1 (y j)
  let x2 := fun i => inverseWeight 1 (x i)
  let F1 := weightedSlices η hη y2 (I := I)
  let F2 := weightedSlicesRight η hη x2 (I := J)
  have hy2 : Summable (fun j => ‖y2 j‖^2) := CrossEnsemble.applied_summable hy (inverseWeight 1)
  have hx2 : Summable (fun i => ‖x2 i‖^2) := CrossEnsemble.applied_summable hx (inverseWeight 1)
  have hy2n : HasSum (fun j => ‖inverseWeight 2 (y2 j)‖^2) 1 := by
    simpa only [y2,inverse_two_one] using hyn
  have hx2n : HasSum (fun i => ‖inverseWeight 2 (x2 i)‖^2) 1 := by
    simpa only [x2,inverse_two_one] using hxn
  have hF1 : ∀ u, Summable (fun i => ‖u i‖^2) → Summable (fun k => ‖F1 u k‖^2) :=
    fun u hu => weightedSlices_summable η hη y2 hy2 u hu
  have hF2 : ∀ u, Summable (fun j => ‖u j‖^2) → Summable (fun k => ‖F2 u k‖^2) :=
    fun u hu => weightedSlicesRight_summable η hη x2 hx2 u hu
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hh : ∀ Z, WeightedGenerator.pairing (η*a+(1-η)*b) z Z=
      WeightedGenerator.pushedPairing F1 a x Z+WeightedGenerator.pushedPairing F2 b y Z := by
    apply weighted_trace_ext bas (WeightedGenerator.generator (η*a+(1-η)*b) z)
      (WeightedGenerator.pushedGenerator F1 a x+WeightedGenerator.pushedGenerator F2 b y)
    · exact fun Z => WeightedGenerator.pairing_hasSum bas _ z hz Z
    · intro Z
      simpa only [add_apply,map_add,inner_add_right] using
        (WeightedGenerator.pushedPairing_hasSum bas F1 hF1 a x hx Z).add
          (WeightedGenerator.pushedPairing_hasSum bas F2 hF2 b y hy Z)
    · intro Z
      rw [weighted_pairing_physical,
        weighted_pushed_pairing_physical η hη y2 hy2n a x hx Z,
        weighted_pushed_pairing_physical_right η hη x2 hx2n b y hy Z]
      simp only [y2,x2,inverse_two_one]
      exact physical_product_generator η a b hη ρ σ τ hτ x y z hx hy hz hxn hyn hex hey hez Z
  rw [hh]
  congr 1
  · apply WeightedGenerator.pushedPairing_slicing F1 B _ _ a x hx
    intro u v hu hv
    exact weighted_pairing_slicing η hη y2 hy2 u v hu hv B
  · apply WeightedGenerator.pushedPairing_slicing F2 B _ _ b y hy
    intro u v hu hv
    exact weighted_pairing_slicing_right η hη x2 hx2 u v hu hv B
end BeamLadder

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I : Type*}

end CrossEnsemble

end

end OAI

-- ---- platform node ----
open OAI OAI.BeamLadder
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
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp


theorem solution : type_of% @_root_.OAI.BeamLadder.weighted_product_generator := @_root_.OAI.BeamLadder.weighted_product_generator
