-- Prove2me | solution 1 for OAI.BeamLadder.output_weak
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:57:35.81069+00:00
-- url     : https://prove2.me/submissions/2e63ec8a-c878-4b95-ac6e-ad15fe952b77

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/BeamTrace.lean:L1130-L1162
-- (upload_full_project.md Phase 4): solution for node OAI.BeamLadder.output_weak. The node keeps its source
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
import Theorems.Thm_OAI_CrossEnsemble_operator_comp_left
import Theorems.Thm_OAI_CrossEnsemble_shifted_left_operator_eq
import Theorems.Thm_OAI_CrossEnsemble_shifted_right_operator_eq

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

end

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}

theorem raiseL_up (j : Fin n) (x : JointFock n) (ke : NumberIndex n × NumberIndex n) :
    raiseL j x (upL j ke)=((Real.sqrt ((ke.1 j:ℝ)+1)/W ke:ℝ):ℂ)*x ke := by
  change (increase (W (upL j ke)):ℂ)*((lowerL j).adjoint x (upL j ke))=_
  rw [lowerL, WeightedShift.adjoint_apply_image]
  have hw : 0<W ke := by linarith [W_one_le ke]
  simp only [W_upL, increase, ite_eq_left (by linarith : 1<W ke+1), add_sub_cancel_right,
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

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

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

theorem raiseL_inverse_apply (j : Fin n) (x : JointFock n) (k e : NumberIndex n) :
    raiseL j x (k,e)=(Real.sqrt (k j:ℝ):ℂ)*inverse x (down j k,e) := by
  rcases index_cases j k with hk | ⟨a,rfl⟩
  · simp only [raiseL_zero j x (k,e) hk, hk, Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero, zero_mul]
  · change raiseL j x (upL j (a,e))=_
    rw [raiseL_up, up_same, down_up, inverse_apply]
    push_cast
    ring

theorem single_lower_inverse_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    sandwich 0 3 (by omega) j x k=(Real.sqrt ((k j:ℝ)+1):ℂ)*inverseWeight 3 x (up j k) := by
  simp only [sandwich_apply, coefficient, pow_zero, one_mul, inverseWeight_apply]
  push_cast
  ring

theorem single_raise_inverse_apply (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    creationSandwich 0 3 (by omega) j x k=(Real.sqrt (k j:ℝ):ℂ)*inverseWeight 3 x (down j k) := by
  rcases index_cases j k with hk | ⟨a,rfl⟩
  · simp only [creationSandwich_zero _ _ _ _ _ k hk, hk, Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero, zero_mul]
  · rw [creationSandwich_up, up_same, down_up, inverseWeight_apply]
    simp only [creationCoefficient, pow_zero, one_mul]
    push_cast
    ring

theorem output_weak (r : ℝ) (j : Fin n) (x : I → JointFock n) (z : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hz : Summable (fun j => ‖z j‖^2))
    (he : CrossEnsemble.operator (fun ie : I × NumberIndex n => slice (inverse (x ie.1)) ie.2)
        (fun ie : I × NumberIndex n => slice (inverse (x ie.1)) ie.2)=
      CrossEnsemble.operator (fun j => inverseWeight 3 (z j)) (fun j => inverseWeight 3 (z j)))
    (Z : Fock n →L[ℂ] Fock n) :
    (∑' i, weakL r j (x i) (x i) (liftLeft Z))=singleWeak r j z Z := by
  have hi := CrossEnsemble.applied_summable hx inverse
  have hl := CrossEnsemble.applied_summable hx (lowerL j)
  have hr := CrossEnsemble.applied_summable hx (raiseL j)
  have hzi := CrossEnsemble.applied_summable hz (inverseWeight 3)
  have hzl := CrossEnsemble.applied_summable hz (sandwich 0 3 (by omega) j)
  have hzr := CrossEnsemble.applied_summable hz (creationSandwich 0 3 (by omega) j)
  have his := slice_family_summable _ hi
  have hls := slice_family_summable _ hl
  have hrs := slice_family_summable _ hr
  have heL := CrossEnsemble.shifted_right_operator_eq _ _ _ _ his hls hzi hzl
    (up j) (fun k => (Real.sqrt ((k j:ℝ)+1):ℂ))
    (fun ie k => lowerL_inverse_apply j (x ie.1) k ie.2)
    (fun i k => single_lower_inverse_apply j (z i) k) he
  have heR := CrossEnsemble.shifted_left_operator_eq _ _ _ _ his hrs hzi hzr
    (down j) (fun k => (Real.sqrt (k j:ℝ):ℂ))
    (fun ie k => raiseL_inverse_apply j (x ie.1) k ie.2)
    (fun i k => single_raise_inverse_apply j (z i) k) he
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hpL := CrossEnsemble.pairing_eq_of_operator_eq bas his hls hzi hzl heL Z
  have hpR := CrossEnsemble.pairing_eq_of_operator_eq bas hrs his hzr hzi heR Z
  simp only [weakL]
  rw [Summable.tsum_sub ((CrossEnsemble.pairing_summable hi hl (liftLeft Z)).mul_left _)
    ((CrossEnsemble.pairing_summable hr hi (liftLeft Z)).mul_left _), tsum_mul_left, tsum_mul_left]
  change (r+1:ℂ)*CrossEnsemble.pairing _ _ (liftLeft Z)-(r:ℂ)*CrossEnsemble.pairing _ _ (liftLeft Z)=_
  rw [pairing_liftLeft _ _ hi hl, pairing_liftLeft _ _ hr hi, hpL, hpR]
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


theorem solution : type_of% @_root_.OAI.BeamLadder.output_weak := @_root_.OAI.BeamLadder.output_weak
