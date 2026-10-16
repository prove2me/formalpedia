-- Prove2me | solution 1 for OAI.TensorLp.liftLeft_positive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:34:45.334381+00:00
-- url     : https://prove2.me/submissions/96c9d35a-36ab-4ef5-acf2-76582345c159

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TensorLp.lean:L221-L233
-- (upload_full_project.md Phase 4): solution for node OAI.TensorLp.liftLeft_positive. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp

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

theorem liftLeft_symmetric {Z : H A →L[ℂ] H A} (hZ : Z.IsSymmetric) :
    (liftLeft (B := B) Z).IsSymmetric := by
  intro x y
  apply HasSum.unique (hasSum_slice_inner (liftLeft Z x) y)
  convert! hasSum_slice_inner x (liftLeft Z y) using 1
  ext b
  simp only [slice_liftLeft]
  exact hZ _ _

theorem liftLeft_positive {Z : H A →L[ℂ] H A} (hZ : Z.IsPositive) :
    (liftLeft (B := B) Z).IsPositive := by
  refine ⟨liftLeft_symmetric hZ.isSymmetric, ?_⟩
  intro x
  have h := (hasSum_slice_inner x (liftLeft Z x)).mapL Complex.reCLM
  have hp (b : B) : 0 ≤ (inner ℂ (slice x b) (Z (slice x b))).re := hZ.re_inner_nonneg_right _
  have hh : HasSum (fun b => (inner ℂ (slice x b) (Z (slice x b))).re)
      (inner ℂ x (liftLeft Z x)).re := by simpa only [Complex.reCLM_apply, slice_liftLeft] using h
  change 0 ≤ (inner ℂ (liftLeft Z x) x).re
  have he : (inner ℂ (liftLeft Z x) x).re = (inner ℂ x (liftLeft Z x)).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  rw [he]
  exact hh.nonneg hp

end TensorLp

end

end

end OAI

-- ---- platform node ----
open OAI OAI.TensorLp
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule


theorem solution : type_of% @_root_.OAI.TensorLp.liftLeft_positive := @_root_.OAI.TensorLp.liftLeft_positive
