-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:51:16.204602+00:00
-- url     : https://prove2.me/submissions/b0c944ee-5d1f-4409-a2f9-18c3274b93c0

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OmegaScalar
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_OmScalP_evAt_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.OmScalP
open Formalism.REAL (qdet qminor Tm)
open _root_.CompanionTheory.RgExh
open _root_.CompanionTheory.RgExh.Hk
namespace GlobalTheory.CompanionTheory.RgExhHecke.OmScalP
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M] (p : (Module.End ℂ M)[X]) (q : ℂ[X]) (h : M) (b : ℂ)
    (H : ∀ u, u ≠ b → evAt u p h = q.eval u • h) : evAt b p h = q.eval b • h := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  set r : ℂ[X] := ∑ k ∈ p.support, monomial k (φ (p.coeff k h)) - q * C (φ h) with hr
  have hev : ∀ u, r.eval u = φ (evAt u p h - q.eval u • h) := by
    intro u
    have e1 : evAt u p h = ∑ k ∈ p.support, u ^ k • p.coeff k h := by
      rw [evAt_apply, eval₂_eq_sum, Polynomial.sum_def, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← map_pow, RingHom.id_apply, ← Algebra.commutes, ← Algebra.smul_def]
      rfl
    rw [e1, hr]
    simp [eval_finsetSum, map_sum, eval_monomial, mul_comm]
  have hz : r = 0 := by
    refine eq_zero_of_infinite_isRoot r ?_
    refine Set.Infinite.mono (s := {b}ᶜ) ?_ (Set.finite_singleton b).infinite_compl
    intro u hu
    have hu' : u ≠ b := hu
    change r.eval u = 0
    rw [hev, H u hu', sub_self, map_zero]
  rw [← hev, hz, eval_zero]
end GlobalTheory.CompanionTheory.RgExhHecke.OmScalP
