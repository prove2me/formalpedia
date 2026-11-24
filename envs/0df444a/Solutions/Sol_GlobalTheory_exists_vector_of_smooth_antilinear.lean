-- Prove2me | solution 1 for GlobalTheory.exists_vector_of_smooth_antilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:47:48.550746+00:00
-- url     : https://prove2.me/submissions/31878555-3af5-456e-bbc5-70422f80615b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryAdmissibleMatrixCoefficient
import Theorems.Thm_GlobalTheory_SmoothRiesz_exists_eq_of_invariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
open scoped Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V)
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), IsAdmissible σ → (∀ v w, Bf w v = starRingEnd ℂ (Bf v w)) →
    (∀ v, v ≠ 0 → 0 < (Bf v v).re) → (∀ g v w, Bf (σ g v) (σ g w) = Bf v w) →
    ∀ (L : V →ₗ⋆[ℂ] ℂ) (S : Subgroup (GL (Fin r) k)), IsOpen (S : Set (GL (Fin r) k)) →
      (∀ s ∈ S, ∀ w, L (σ s w) = L w) → ∃ u : V, ∀ w, L w = Bf u w := by
  intro k _ _ _ _ r V _ _ σ Bf hadm _ hpos hinv L S hSo hL
  have hKo : IsOpen ((S ⊓ KO k (Fin r) : Subgroup _) : Set (GL (Fin r) k)) :=
    hSo.inter SplitFlip.isOpen_KO
  have hKc : IsCompact ((S ⊓ KO k (Fin r) : Subgroup _) : Set (GL (Fin r) k)) :=
    SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKo) inf_le_right
  exact SmoothRiesz.exists_eq_of_invariant σ Bf hadm hpos hinv L _ hKo hKc
    fun s hs => hL s hs.1
end GlobalTheory
