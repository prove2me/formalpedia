-- Prove2me | solution 1 for GlobalTheory.Avoid.exists_minor_ne_zero_of_separating
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:52.105132+00:00
-- url     : https://prove2.me/submissions/b34582d7-47a5-4f61-8b23-e2c1fc9d0aef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisMapOfLiftBaseChangeSurjective
import Theorems.Thm_P2M_GlobalTheory_Avoid_pairingDual__Multi_comp_bbdba73fb990

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open scoped TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.Avoid
open exteriorPower
namespace GlobalTheory.Avoid
theorem _root_.solution {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Finite ι] [LinearOrder ι] (c : ι → Dual K V)
    (hc : ∀ v : V, (∀ j, c j v = 0) → v = 0) {r : ℕ} (x : ⋀[K]^r V) (hx : x ≠ 0) :
    ∃ J : Set.powersetCard ι r, pairingDual K V r (ιMulti_family K r c J) x ≠ 0 := by
  let φ : V →ₗ[K] (ι → K) := LinearMap.pi c
  have hφ : Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact hc v fun j => congrFun hv j
  have hinj : Injective (exteriorPower.map r φ) := map_injective_field hφ
  by_contra! h
  apply hx
  apply hinj
  rw [map_zero]
  apply ((Pi.basisFun K ι).exteriorPower r).repr.injective
  ext J
  rw [basis_repr_apply, ιMultiDual, ιMulti_family, ← pairingDual_ιMulti_comp, map_zero,
    Finsupp.zero_apply, ← h J, ιMulti_family]
  congr 3
end GlobalTheory.Avoid
