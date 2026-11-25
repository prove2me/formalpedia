-- Prove2me | solution 1 for GlobalTheory.topFormOrd_vw_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:59:30.436605+00:00
-- url     : https://prove2.me/submissions/78516397-fe6e-41d6-8ad4-bfff6ade36d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_GlobalTheory_topFormOrd_vw_eq_top_iff
import Theorems.Thm_GlobalTheory_le_topFormOrd_vw_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (V : Type*) {F : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
  [Algebra V F] [IsFractionRing V F]
variable {V}
variable (F) {K : Type*} [CommRing K] [Algebra K V] [Algebra K F] [IsScalarTower K V F] {n : ℕ}
variable {F} (b : Basis (Fin n) V Ω[V⁄K])
namespace GlobalTheory
theorem _root_.solution (b' : Basis (Fin n) V Ω[V⁄K]) (ω : ⋀[F]^n Ω[F⁄K]) :
    topFormOrd_vw F b ω = topFormOrd_vw F b' ω := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  have key : ∀ c c' : Basis (Fin n) V Ω[V⁄K], topFormOrd_vw F c ω ≤ topFormOrd_vw F c' ω := by
    intro c c'
    by_cases h : topFormOrd_vw F c ω = ⊤
    · rw [(topFormOrd_vw_eq_top_iff c' ω).mpr ((topFormOrd_vw_eq_top_iff c ω).mp h)]
      exact le_top
    · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp h
      rw [← hm, le_topFormOrd_vw_iff c' ht, ← le_topFormOrd_vw_iff c ht, hm]
  exact le_antisymm (key b b') (key b' b)
end GlobalTheory
