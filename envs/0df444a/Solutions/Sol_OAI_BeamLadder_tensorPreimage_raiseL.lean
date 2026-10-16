-- Prove2me | solution 1 for OAI.BeamLadder.tensorPreimage_raiseL
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:50:59.468034+00:00
-- url     : https://prove2.me/submissions/4d5f3d6e-b1fb-4f17-b2ba-092dbf7be1e0

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/BeamTrace.lean:L646-L658
-- (upload_full_project.md Phase 4): solution for node OAI.BeamLadder.tensorPreimage_raiseL. The node keeps its source
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

theorem tensorPreimage_apply (x y : Fock n) (k e : NumberIndex n) :
    tensorPreimage x y (k,e)=(W (k,e):ℂ)*inverseWeight 3 x k*inverseWeight 3 y e := by
  have hk : (numberWeight k:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le k] : numberWeight k≠0)
  have he : (numberWeight e:ℂ)≠0 := by exact_mod_cast (by linarith [numberWeight_one_le e] : numberWeight e≠0)
  simp only [tensorPreimage, lp.coeFn_sub, lp.coeFn_add, Pi.sub_apply, Pi.add_apply,
    tensor_apply, inverseWeight_apply, W]
  push_cast
  field_simp

theorem tensorPreimage_raiseL (j : Fin n) (x y : Fock n) :
    raiseL j (tensorPreimage x y)=tensor (creationSandwich 0 3 (by omega) j x) (inverseWeight 3 y) := by
  apply lp.ext
  funext ke
  obtain ⟨k,e⟩ := ke
  rcases index_cases j k with hk | ⟨a,rfl⟩
  · rw [raiseL_zero j _ (k,e) hk, tensor_apply, creationSandwich_zero _ _ _ _ _ k hk, zero_mul]
  · change raiseL j (tensorPreimage x y) (upL j (a,e))=_
    rw [raiseL_up, tensorPreimage_apply, tensor_apply, creationSandwich_up]
    have hw : (W (a,e):ℂ)≠0 := by exact_mod_cast (by linarith [W_one_le (a,e)] : W (a,e)≠0)
    simp only [creationCoefficient, pow_zero, one_mul, inverseWeight_apply]
    push_cast
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
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp


theorem solution : type_of% @_root_.OAI.BeamLadder.tensorPreimage_raiseL := @_root_.OAI.BeamLadder.tensorPreimage_raiseL
