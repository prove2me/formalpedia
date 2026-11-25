-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.adelicNorm_le_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:21:39.15154+00:00
-- url     : https://prove2.me/submissions/3f5ba7c6-a160-4f6a-9b63-13950a9ab65e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIdele
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite
import Theorems.Thm_GroundTheory_Automorphic_Reduction_finprod_le_finprod_of_nonneg
import Theorems.Thm_GroundTheory_Automorphic_Reduction_HasFiniteContent_finite_mulSupport
import Theorems.Thm_GroundTheory_Automorphic_Reduction_euclidNorm_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {y y' : Fin n → 𝔸[K]} (hy : HasFiniteContent y)
    (hy' : HasFiniteContent y') (a : InfinitePlace K → ℝ) (b : HeightOneSpectrum (𝓞 K) → ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hinf : ∀ w, euclidNorm (infComp w y) ≤ a w * euclidNorm (infComp w y'))
    (hb1 : ∀ v, v ∉ S → b v = 1)
    (hfin : ∀ v, ‖finComp v y‖ ≤ b v * ‖finComp v y'‖) :
    adelicNorm y ≤ (∏ w, a w ^ w.mult) * (∏ v ∈ S, b v) * adelicNorm y' := by
  have hbS : (Function.mulSupport b).Finite :=
    S.finite_toSet.subset fun v hv => by
      by_contra h
      exact hv (hb1 v h)
  have hprod : ∏ᶠ v, b v = ∏ v ∈ S, b v :=
    finprod_eq_prod_of_mulSupport_subset b fun v hv => by
      by_contra h
      exact hv (hb1 v h)
  rw [adelicNorm, adelicNorm]
  have hinf' : ∏ w, euclidNorm (infComp w y) ^ w.mult ≤
      (∏ w, a w ^ w.mult) * ∏ w, euclidNorm (infComp w y') ^ w.mult := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun w _ => pow_nonneg (euclidNorm_nonneg _) _) fun w _ => by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (euclidNorm_nonneg _) (hinf w) _
  have hfin' : ∏ᶠ v, ‖finComp v y‖ ≤ (∏ v ∈ S, b v) * ∏ᶠ v, ‖finComp v y'‖ := by
    rw [← hprod, ← finprod_mul_distrib hbS hy'.finite_mulSupport]
    refine finprod_le_finprod_of_nonneg hy.finite_mulSupport ?_ (fun _ => norm_nonneg _) hfin
    exact (hbS.union hy'.finite_mulSupport).subset (Function.mulSupport_mul _ _)
  have h1 : 0 ≤ ∏ᶠ v, ‖finComp v y‖ := finprod_nonneg fun _ => norm_nonneg _
  have h2 : 0 ≤ (∏ w, a w ^ w.mult) * ∏ w, euclidNorm (infComp w y') ^ w.mult :=
    le_trans (Finset.prod_nonneg fun _ _ => pow_nonneg (euclidNorm_nonneg _) _) hinf'
  calc (∏ w, euclidNorm (infComp w y) ^ w.mult) * ∏ᶠ v, ‖finComp v y‖
      ≤ ((∏ w, a w ^ w.mult) * ∏ w, euclidNorm (infComp w y') ^ w.mult) *
          ((∏ v ∈ S, b v) * ∏ᶠ v, ‖finComp v y'‖) := mul_le_mul hinf' hfin' h1 h2
    _ = _ := by ring
end GroundTheory.Automorphic.Reduction
