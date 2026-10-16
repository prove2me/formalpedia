-- Prove2me | solution 1 for OAI.BeamLadder.generatorPairingR_product
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:38:34.282791+00:00
-- url     : https://prove2.me/submissions/fbea8435-3446-43b5-b2da-e3d9bd082c40

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/BeamForms.lean:L941-L992
-- (upload_full_project.md Phase 4): solution for node OAI.BeamLadder.generatorPairingR_product. The node keeps its source
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
import Theorems.Thm_OAI_BeamLadder_tensorPreimage2_summable
import Theorems.Thm_OAI_BeamLadder_tensorPreimage_lowerR
import Theorems.Thm_OAI_BeamLadder_tensorPreimage_raiseR

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

 theorem conditionalRight_entry (x : I → H A) (hx : HasSum (fun i => ‖x i‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) (u v : H B) :
    HasSum (fun i => inner ℂ (tensor (x i) u) (Z (tensor (x i) v))) (inner ℂ u (conditionalRight x hx Z v)) :=
  KrausBounded.dual_entry _ _ _ _ _

 theorem tensorFamily_summable (x : I → H A) (y : J → H B)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2)) :
    Summable (fun ij : I × J => ‖tensor (x ij.1) (y ij.2)‖^2) := by
  simpa only [tensor_norm_sq] using hx.mul_of_nonneg hy (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)

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

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

theorem numberR_minus (j : Fin n) (x : JointFock n) (e k : NumberIndex n) :
    raiseR j (preLowerR j x) (k,e)=(e j:ℂ)*inverse (inverse x) (k,e) := by
  by_cases hk : e j=0
  · rw [raiseR_zero j _ (k,e) hk, hk, Nat.cast_zero,zero_mul]
  · obtain ⟨a,rfl⟩ : ∃ a,e=up j a := ⟨down j e,(up_down j e (Nat.pos_of_ne_zero hk)).symm⟩
    change raiseR j (preLowerR j x) (upR j (k,a))=(up j a j:ℂ)*inverse (inverse x) (upR j (k,a))
    rw [raiseR_up]
    have hw : (W (k,a):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (k,a)] : W (k,a)≠0)
    have hu : (W (k,a):ℂ)+1≠0 := by exact_mod_cast (by linarith [W_one_le (k,a)] : W (k,a)+1≠0)
    have hs : (Real.sqrt ((a j:ℝ)+1):ℂ)^2=((a j:ℝ)+1:ℂ) := by exact_mod_cast Real.sq_sqrt (by positivity : 0≤(a j:ℝ)+1)
    simp only [preLowerR,ContinuousLinearMap.comp_apply,lowerR_apply,sub_apply,one_apply_eq_self,
      lp.coeFn_sub,Pi.sub_apply,inverse_apply,up_same,W_upR]
    push_cast
    field_simp
    linear_combination x (upR j (k,a))*(W (k,a):ℂ)*hs

theorem numberR_plus (j : Fin n) (x : JointFock n) (e k : NumberIndex n) :
    lowerR j (preRaiseR j x) (k,e)=(e j+1:ℂ)*inverse (inverse x) (k,e) := by
  rw [lowerR_apply]
  change _*raiseR j ((1+inverse) x) (upR j (k,e))=_
  rw [raiseR_up]
  have hw : (W (k,e):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (k,e)] : W (k,e)≠0)
  have hu : (W (k,e):ℂ)+1≠0 := by exact_mod_cast (by linarith [W_one_le (k,e)] : W (k,e)+1≠0)
  have hs : (Real.sqrt ((e j:ℝ)+1):ℂ)^2=((e j:ℝ)+1:ℂ) := by exact_mod_cast Real.sq_sqrt (by positivity : 0≤(e j:ℝ)+1)
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

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

theorem tensorPreimage2_numberR_minus (j : Fin n) (x y : Fock n) :
    raiseR j (preLowerR j (tensorPreimage2 x y))=
      tensor (inverseWeight 3 x) (inverseWeight 2 (modeBound j false y)) := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  rw [numberR_minus,tensorPreimage2_inverse,tensorPreimage_inverse,tensor_apply,tensor_apply]
  have he : (numberWeight e:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le e] : numberWeight e≠0)
  simp only [inverseWeight_apply,modeBound_apply,Bool.false_eq_true,↓reduceIte,add_zero]
  push_cast
  field_simp

theorem tensorPreimage2_numberR_plus (j : Fin n) (x y : Fock n) :
    lowerR j (preRaiseR j (tensorPreimage2 x y))=
      tensor (inverseWeight 3 x) (inverseWeight 2 (modeBound j true y)) := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  rw [numberR_plus,tensorPreimage2_inverse,tensorPreimage_inverse,tensor_apply,tensor_apply]
  have he : (numberWeight e:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le e] : numberWeight e≠0)
  simp only [inverseWeight_apply,modeBound_apply,↓reduceIte]
  push_cast
  field_simp

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

theorem generatorPairingR_product (r : ℝ) (x : I → Fock n) (y : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hxn : HasSum (fun i => ‖inverseWeight 3 (x i)‖^2) 1)
    (Z : JointFock n →L[ℂ] JointFock n) :
    generatorPairingR r (fun ij : I × J => tensorPreimage2 (x ij.1) (y ij.2))
      (fun ij : I × J => tensorPreimage2 (x ij.1) (y ij.2)) Z=
      singleGeneratorPairing r y (conditionalRight (fun i => inverseWeight 3 (x i)) hxn Z) := by
  have hp := tensorPreimage2_summable x y hx hy
  have hi := CrossEnsemble.applied_summable hy (inverseWeight 3)
  have hm (j : Fin n) (u : Bool) := CrossEnsemble.applied_summable hy (inverseWeight 2 ∘L modeBound j u)
  have hl (j : Fin n) := CrossEnsemble.applied_summable hy (sandwich 0 3 (by omega) j)
  have hr (j : Fin n) := CrossEnsemble.applied_summable hy (creationSandwich 0 3 (by omega) j)
  unfold generatorPairingR singleGeneratorPairing
  apply Finset.sum_congr rfl
  intro j _
  have hts (u v : J → Fock n) (hu : Summable (fun i => ‖u i‖^2))
      (hv : Summable (fun i => ‖v i‖^2)) :=
    pairing_conditionalRight (fun i => inverseWeight 3 (x i)) u v hxn hu hv Z
  have h1 := hts _ _ (hl j) (hl j)
  have h2 := hts _ _ (hm j false) hi
  have h3 := hts _ _ hi (hm j false)
  have h4 := hts _ _ (hr j) (hr j)
  have h5 := hts _ _ (hm j true) hi
  have h6 := hts _ _ hi (hm j true)
  unfold quadMinusR quadPlusR
  simp only [tensorPreimage2_inverse,tensorPreimage_inverse,tensorPreimage_lowerR,
    tensorPreimage_raiseR,tensorPreimage2_numberR_minus,tensorPreimage2_numberR_plus]
  have hA := CrossEnsemble.pairing_summable
    (CrossEnsemble.applied_summable hp (lowerR j ∘L inverse))
    (CrossEnsemble.applied_summable hp (lowerR j ∘L inverse)) Z
  have hB := CrossEnsemble.pairing_summable
    (CrossEnsemble.applied_summable hp (raiseR j ∘L preLowerR j))
    (CrossEnsemble.applied_summable hp (inverse ∘L inverse)) Z
  have hC := CrossEnsemble.pairing_summable
    (CrossEnsemble.applied_summable hp (inverse ∘L inverse))
    (CrossEnsemble.applied_summable hp (raiseR j ∘L preLowerR j)) Z
  have hD := CrossEnsemble.pairing_summable
    (CrossEnsemble.applied_summable hp (raiseR j ∘L inverse))
    (CrossEnsemble.applied_summable hp (raiseR j ∘L inverse)) Z
  have hE := CrossEnsemble.pairing_summable
    (CrossEnsemble.applied_summable hp (lowerR j ∘L preRaiseR j))
    (CrossEnsemble.applied_summable hp (inverse ∘L inverse)) Z
  have hF := CrossEnsemble.pairing_summable
    (CrossEnsemble.applied_summable hp (inverse ∘L inverse))
    (CrossEnsemble.applied_summable hp (lowerR j ∘L preRaiseR j)) Z
  simp only [ContinuousLinearMap.comp_apply,tensorPreimage2_inverse,tensorPreimage_inverse,
    tensorPreimage_lowerR,tensorPreimage_raiseR,tensorPreimage2_numberR_minus,tensorPreimage2_numberR_plus] at hA hB hC hD hE hF
  rw [hA.tsum_sub ((hB.add hC).mul_left _), hD.tsum_sub ((hE.add hF).mul_left _),
    tsum_mul_left,tsum_mul_left,hB.tsum_add hC,hE.tsum_add hF]
  simpa only [CrossEnsemble.pairing, ContinuousLinearMap.comp_apply] using congrArg₂ HAdd.hAdd
    (congrArg (fun z : ℂ => ((r+1:ℝ):ℂ)*z) (congrArg₂ HSub.hSub h1 (congrArg (fun z : ℂ => (2:ℂ)⁻¹*z) (congrArg₂ HAdd.hAdd h2 h3))))
    (congrArg (fun z : ℂ => (r:ℂ)*z) (congrArg₂ HSub.hSub h4 (congrArg (fun z : ℂ => (2:ℂ)⁻¹*z) (congrArg₂ HAdd.hAdd h5 h6))))
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
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.BeamLadder.generatorPairingR_product := @_root_.OAI.BeamLadder.generatorPairingR_product
