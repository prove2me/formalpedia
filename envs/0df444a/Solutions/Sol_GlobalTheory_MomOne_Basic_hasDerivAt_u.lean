-- Prove2me | solution 1 for GlobalTheory.MomOne.Basic.hasDerivAt_u
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:58:25.234857+00:00
-- url     : https://prove2.me/submissions/2ffb9558-c07c-4e37-b283-c22241c40929

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.MomOne
variable {q : ℕ} [Fact q.Prime]
open GlobalTheory.MomOne.Basic
open Filter Topology
namespace GlobalTheory.MomOne.Basic
theorem _root_.solution (M : Mdl q) (hc : M.c ≠ 0) : HasDerivAt M.u M.c 0 := by
  have ha := M.L.analyticAt_weierstrassPExcept 0
  have hb := M.L.analyticAt_derivWeierstrassPExcept 0
  set β := M.ι.symm (M.W.b₂ / 12)
  set a1 := M.ι.symm M.W.a₁
  set a3 := M.ι.symm M.W.a₃
  obtain ⟨A, hAd⟩ : ∃ A : ℂ → ℂ, A = fun z => (1 + z ^ 2 * M.L.weierstrassPExcept 0 z) / M.c ^ 2 - β * z ^ 2 := ⟨_, rfl⟩
  have hA : AnalyticAt ℂ A 0 := by rw [hAd]; fun_prop
  obtain ⟨B, hBd⟩ : ∃ B : ℂ → ℂ, B = fun z =>
      ((z ^ 3 * M.L.derivWeierstrassPExcept 0 z - 2) / M.c ^ 3 - a1 * z * A z - a3 * z ^ 3) / 2 := ⟨_, rfl⟩
  have hB : AnalyticAt ℂ B 0 := by rw [hBd]; fun_prop
  have hA0 : A 0 = 1 / M.c ^ 2 := by simp [hAd]
  have hB0 : B 0 = -1 / M.c ^ 3 := by simp [hBd]; ring
  have hB0' : B 0 ≠ 0 := by rw [hB0]; exact div_ne_zero (by norm_num) (pow_ne_zero _ hc)
  have hx : ∀ z : ℂ, z ≠ 0 → M.x z = A z / z ^ 2 := by
    intro z hz
    have h := M.L.weierstrassPExcept_add 0 z
    simp only [ZeroMemClass.coe_zero, sub_zero] at h
    rw [Mdl.x, ← h, hAd]
    field_simp
    ring
  have hy : ∀ z : ℂ, z ≠ 0 → M.y z = B z / z ^ 3 := by
    intro z hz
    have h := M.L.derivWeierstrassPExcept_sub 0 z
    simp only [ZeroMemClass.coe_zero, sub_zero] at h
    rw [Mdl.y, ← h, hBd, hx z hz]
    simp only [a1, a3]
    field_simp
  have hQ : AnalyticAt ℂ (fun z => -A z / B z) 0 := hA.neg.div hB hB0'
  have h := (hasDerivAt_id (0 : ℂ)).mul hQ.differentiableAt.hasDerivAt
  have e : -A 0 / B 0 = M.c := by rw [hA0, hB0]; field_simp
  simp only [id, zero_mul, add_zero, one_mul, e] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hB.continuousAt.eventually_ne hB0', M.L.compl_lattice_sdiff_singleton_mem_nhds 0] with z h2 h3
  by_cases hz : z = 0
  · subst hz; simp [Mdl.u]
  · have : z ∉ M.L.lattice := fun h => h3 ⟨h, hz⟩
    simp only [Mdl.u, if_neg this, hx z hz, hy z hz, Pi.mul_apply, id]
    field_simp
end GlobalTheory.MomOne.Basic
