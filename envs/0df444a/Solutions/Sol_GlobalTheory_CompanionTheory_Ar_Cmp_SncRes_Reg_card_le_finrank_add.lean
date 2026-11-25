-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.card_le_finrank_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:58:04.503224+00:00
-- url     : https://prove2.me/submissions/a274ae7c-f202-4d96-a81e-b1de1198b6e1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
theorem _root_.solution (σ : Type) [Fintype σ] (V : Submodule ℂ (σ → ℂ)) (e : ℕ) (b : Fin e → σ → ℂ)
    (h : ∀ v : σ → ℂ, (∀ a ∈ V, ∑ q, a q * v q = 0) → v ∈ Submodule.span ℂ (Set.range b)) :
    Fintype.card σ ≤ Module.finrank ℂ V + e := by
  let B : (σ → ℂ) →ₗ[ℂ] (σ → ℂ) →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun v a => ∑ q, a q * v q)
    (fun v v' a => by simp [mul_add, Finset.sum_add_distrib])
    (fun c v a => by simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun v a a' => by simp [add_mul, Finset.sum_add_distrib])
    (fun c v a => by simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring)
  let T : (σ → ℂ) →ₗ[ℂ] Module.Dual ℂ V := B.compl₂ V.subtype
  have hk : LinearMap.ker T ≤ Submodule.span ℂ (Set.range b) := by
    intro v hv
    refine h v fun a ha => ?_
    have := DFunLike.congr_fun (LinearMap.mem_ker.1 hv) ⟨a, ha⟩
    exact this
  have h1 := LinearMap.finrank_range_add_finrank_ker T
  have h2 : Module.finrank ℂ (LinearMap.range T) ≤ Module.finrank ℂ V := by
    calc _ ≤ Module.finrank ℂ (Module.Dual ℂ V) := Submodule.finrank_le _
      _ = _ := Subspace.dual_finrank_eq
  have h3 : Module.finrank ℂ (LinearMap.ker T) ≤ e := by
    calc _ ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range b)) := Submodule.finrank_mono hk
      _ ≤ e := by
        have := finrank_range_le_card (R := ℂ) b
        simpa [Set.finrank] using this
  simp only [Module.finrank_fintype_fun_eq_card] at h1
  omega
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
