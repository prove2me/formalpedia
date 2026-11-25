-- Prove2me | solution 1 for GlobalTheory.classicalTheta_level_and_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:16:15.507591+00:00
-- url     : https://prove2.me/submissions/90b66329-c4a8-4c69-8f80-bd382abae4ce

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ClassicalThetaLevelAndLinearIndependent
import Theorems.Thm_GlobalTheory_bijective_fin_zmod
import Theorems.Thm_GlobalTheory_levelTheta_zero_zero_mem
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    _root_.ReciprocityTheory.PTheta.SiegelSubDomainStatement → _root_.ReciprocityTheory.PTheta.ThetaHoloStatement → _root_.ReciprocityTheory.PTheta.ThetaMTestStatement → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) := by
  intro _ _ _ g τ hτ N hN
  have hN0 : 0 < N := hN
  have heq : ∀ c : Fin g → Fin N, (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) =
      _root_.GlobalTheory.levelTheta 0 0 N τ (fun i => ((c i : ℕ) : ℤ)) := by
    intro c
    funext z
    rw [_root_.GlobalTheory.levelTheta_zero_zero]
    simp
  refine ⟨fun c => ?_, ?_⟩
  · rw [heq c]
    exact _root_.GlobalTheory.mem_thetaLevel.1 (_root_.GlobalTheory.levelTheta_zero_zero_mem hτ hN0 _)
  · have := _root_.GlobalTheory.linearIndependent_levelTheta (a := 0) (b := 0) hτ hN0
      (r := fun (c : Fin g → Fin N) i => ((c i : ℕ) : ℤ))
      (_root_.GlobalTheory.bijective_fin_zmod (ι := Fin g) hN0).injective
    convert this using 1
    funext c
    exact heq c
end _root_.GlobalTheory
end GlobalTheory
