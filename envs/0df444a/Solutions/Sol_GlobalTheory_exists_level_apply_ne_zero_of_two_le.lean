-- Prove2me | solution 1 for GlobalTheory.exists_level_apply_ne_zero_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:04:23.441241+00:00
-- url     : https://prove2.me/submissions/21c03aa0-aa6f-4381-bfa8-98903c569298

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsApplySubSmulNeZeroAndApplyAddNeZero
import Theorems.Thm_GlobalTheory_eC_nat_mul
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_PTheta_eC_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply


section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory
open Complex Matrix Filter Topology in
open scoped BigOperators Real in
private lemma dense_setOf_ne_zero_of_differentiable_ne_zero {g : ℕ} {h : (Fin g → ℂ) → ℂ}
    (hd : Differentiable ℂ h) (hne : h ≠ 0) : Dense {u | h u ≠ 0} := by
  have hc : {u | h u ≠ 0} = {u | h u = 0}ᶜ := by
    ext u
    simp
  rw [hc, ← interior_eq_empty_iff_dense_compl, Set.eq_empty_iff_forall_notMem]
  intro x hx
  apply hne
  have hev : ∀ᶠ w in 𝓝 x, h w = 0 := mem_interior_iff_mem_nhds.1 hx
  funext y
  have ht : Filter.Tendsto (fun t : ℂ => x + t • (y - x)) (𝓝 0) (𝓝 x) := by
    have hcont : Continuous (fun t : ℂ => x + t • (y - x)) := by fun_prop
    simpa using hcont.tendsto 0
  have hφd : Differentiable ℂ (fun t : ℂ => h (x + t • (y - x))) :=
    hd.comp ((differentiable_id.smul_const (y - x)).const_add x)
  have hφ0 : (fun t : ℂ => h (x + t • (y - x))) =ᶠ[𝓝 0] 0 := ht.eventually hev
  have hφa : AnalyticOnNhd ℂ (fun t : ℂ => h (x + t • (y - x))) Set.univ :=
    fun t _ => hφd.analyticAt t
  have := hφa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ 0) hφ0 (Set.mem_univ 1)
  simpa using this
end GlobalTheory
end

set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → (Differentiable ℂ (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) z) ∧ (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) ≠ 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → ∀ N : ℕ, 2 ≤ N → ∀ z, ∃ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * f z) ∧ f z ≠ 0) := by
  intro H g τ hτ N hN z
  obtain ⟨⟨hd, hq⟩, hne⟩ := H g τ hτ
  have hq' : ∀ (n n' : Fin g → ℤ) v, _root_.ReciprocityTheory.PTheta.theta 0 0 (v + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') τ =
      _root_.ReciprocityTheory.PTheta.eC (-(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ v)) * _root_.ReciprocityTheory.PTheta.theta 0 0 v τ :=
    fun n n' v => hq n n' v
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hM : (M : ℂ) ≠ 0 := by
    have : M ≠ 0 := by omega
    exact_mod_cast this
  have hd1 : Differentiable ℂ (fun u => _root_.ReciprocityTheory.PTheta.theta 0 0 (z + u) τ) := hd.comp (differentiable_id.const_add z)
  have hd2 : Differentiable ℂ (fun u => _root_.ReciprocityTheory.PTheta.theta 0 0 (z - (M : ℂ) • u) τ) :=
    hd.comp ((differentiable_id.const_smul (M : ℂ)).const_sub z)
  have hne1 : (fun u => _root_.ReciprocityTheory.PTheta.theta 0 0 (z + u) τ) ≠ 0 := by
    intro h0
    apply hne
    funext w
    have := congr_fun h0 (w - z)
    simpa using this
  have hne2 : (fun u => _root_.ReciprocityTheory.PTheta.theta 0 0 (z - (M : ℂ) • u) τ) ≠ 0 := by
    intro h0
    apply hne
    funext w
    have := congr_fun h0 (-(M : ℂ)⁻¹ • (w - z))
    simp only [smul_neg, smul_smul, mul_inv_cancel₀ hM, one_smul, sub_neg_eq_add,
      add_sub_cancel, Pi.zero_apply] at this
    simpa [mul_inv_cancel₀ hM] using this
  have hopen : IsOpen {u | _root_.ReciprocityTheory.PTheta.theta 0 0 (z + u) τ ≠ 0} :=
    isOpen_ne_fun hd1.continuous continuous_const
  obtain ⟨u, hu1, hu2⟩ := ((dense_setOf_ne_zero_of_differentiable_ne_zero hd1 hne1).inter_of_isOpen_left
    (dense_setOf_ne_zero_of_differentiable_ne_zero hd2 hne2) hopen).nonempty
  refine ⟨fun w => _root_.ReciprocityTheory.PTheta.theta 0 0 (w + u) τ ^ M * _root_.ReciprocityTheory.PTheta.theta 0 0 (w - (M : ℂ) • u) τ, ⟨?_, ?_⟩, ?_⟩
  · exact ((hd.comp (differentiable_id.add_const u)).pow M).mul
      (hd.comp (differentiable_id.sub_const _))
  · intro n n' w
    have e1 : w + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n' + u = (w + u) + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n' := by abel
    have e2 : w + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n' - (M : ℂ) • u =
        (w - (M : ℂ) • u) + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n' := by abel
    simp only
    rw [e1, e2, hq' n n' (w + u), hq' n n' (w - (M : ℂ) • u), mul_pow, ← _root_.GlobalTheory.eC_nat_mul]
    have key : _root_.ReciprocityTheory.PTheta.eC ((M : ℂ) * (-(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (w + u)))) *
        _root_.ReciprocityTheory.PTheta.eC (-(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (w - (M : ℂ) • u))) =
        _root_.ReciprocityTheory.PTheta.eC (-((M + 1 : ℕ) : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ w)) := by
      rw [← _root_.ReciprocityTheory.PTheta.eC_add]
      congr 1
      simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      push_cast
      ring
    rw [← key]
    ring
  · exact mul_ne_zero (pow_ne_zero _ hu1) hu2
end _root_.GlobalTheory
end GlobalTheory
