-- Prove2me | solution 1 for GlobalTheory.ThetaSpan.mem_span_theta_of_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:03:31.195888+00:00
-- url     : https://prove2.me/submissions/6b5cf043-b976-4f48-aebe-c11389505547

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemSpanThetaOfLevel
import Theorems.Thm_GlobalTheory_isSiegel_iff_mem_siegelH
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_PTheta_eC_zero
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
open GlobalTheory GlobalTheory.ThetaSpan
open Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory.ThetaSpan
namespace _root_.GlobalTheory.ThetaSpan
theorem _root_.solution :
  (∀ (g n : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (b : Fin g → ℂ), 1 ≤ n → (∀ j, b j ≠ 0) → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, (Differentiable ℂ (f k) ∧ (∀ (i : Fin g) z, (f k) (z + Pi.single i 1) = (f k) z) ∧ ∀ (j : Fin g) z, (f k) (z + τ.mulVec (Pi.single j 1)) = b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * (f k) z)) → LinearIndependent ℂ f → N ≤ n ^ g) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)))) := by
  intro _ H g τ hτ N hN f hf
  have hN0 : 0 < N := hN
  obtain ⟨hmem, hli⟩ := H g τ hτ N hN
  have hV : _root_.GlobalTheory.thetaLevel N τ = _root_.GlobalTheory.thetaLevelChar 0 0 N τ := by
    ext φ
    simp [_root_.GlobalTheory.mem_thetaLevel, _root_.GlobalTheory.mem_thetaLevelChar, _root_.ReciprocityTheory.PTheta.eC_zero]
  have hsymm : τ.IsSymm := (_root_.GlobalTheory.isSiegel_iff_mem_siegelH.2 hτ).isSymm
  haveI : FiniteDimensional ℂ (_root_.GlobalTheory.thetaLevel N τ) := by
    rw [hV]
    exact _root_.GlobalTheory.finiteDimensional_thetaLevelChar hsymm hN0
  have hrank : Module.finrank ℂ (_root_.GlobalTheory.thetaLevel N τ) = N ^ g := by
    rw [hV, _root_.GlobalTheory.finrank_thetaLevelChar hτ hN0, Fintype.card_fin]
  let v : (Fin g → Fin N) → _root_.GlobalTheory.thetaLevel N τ := fun c => ⟨_, _root_.GlobalTheory.mem_thetaLevel.2 (hmem c)⟩
  have hvli : LinearIndependent ℂ v := LinearIndependent.of_comp (_root_.GlobalTheory.thetaLevel N τ).subtype hli
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ :=
    hvli.span_eq_top_of_card_eq_finrank' (by simp [hrank])
  have hfv : (⟨f, _root_.GlobalTheory.mem_thetaLevel.2 hf⟩ : _root_.GlobalTheory.thetaLevel N τ) ∈ Submodule.span ℂ (Set.range v) := by
    rw [hspan]
    exact Submodule.mem_top
  have := Submodule.mem_map_of_mem (f := (_root_.GlobalTheory.thetaLevel N τ).subtype) hfv
  rw [Submodule.map_span, ← Set.range_comp] at this
  exact this
end _root_.GlobalTheory.ThetaSpan
end GlobalTheory.ThetaSpan
