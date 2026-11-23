-- Prove2me | solution 1 for GlobalTheory.Chow.aeval_eq_zero_of_mem_elimIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:59.658273+00:00
-- url     : https://prove2.me/submissions/49da0a5e-cd7a-4171-9822-8ee24e811d92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Theorems.Thm_GlobalTheory_Chow_genericForm_eq
import Theorems.Thm_GlobalTheory_Chow_incidenceIdeal_le
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
variable {K : Type*} [CommRing K] {σ β β' : Type*} [Fintype σ]
namespace GlobalTheory.Chow
theorem _root_.solution {G : Type*} [CommRing G] [IsDomain G] [Algebra K G]
    {p : Ideal (MvPolynomial σ K)} {ξ : σ → G} (hξ : ∀ g ∈ p, aeval ξ g = 0) (hne : ξ ≠ 0)
    {t : β × σ → G} (ht : ∀ i, ∑ j, t (i, j) * ξ j = 0)
    {f : MvPolynomial (β × σ) K} (hf : f ∈ elimIdeal β p) : aeval t f = 0 := by
  obtain ⟨m, hm⟩ := hf
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  let ev : MvPolynomial (β × σ) (MvPolynomial σ K) →+* G :=
    eval₂Hom (aeval ξ : MvPolynomial σ K →ₐ[K] G).toRingHom t
  have hle : incidenceIdeal β p ≤ RingHom.ker ev := by
    refine incidenceIdeal_le.2 ⟨fun g hg => ?_, fun i => ?_⟩
    · simpa [ev, RingHom.mem_ker] using hξ g hg
    · rw [RingHom.mem_ker, genericForm_eq, map_sum, ← ht i]
      exact Finset.sum_congr rfl fun j _ => by simp [ev, mul_comm]
  have h := hle (hm j)
  have h2 : ev (map C f) = aeval t f := by
    have : ev.comp (map C) = (aeval t : _ →ₐ[K] G).toRingHom := by
      ext <;> simp [ev]
    exact DFunLike.congr_fun this f
  rw [RingHom.mem_ker, map_mul, h2] at h
  refine (mul_eq_zero.1 h).resolve_right ?_
  simpa [ev] using fun h0 => absurd h0 hj
end GlobalTheory.Chow
