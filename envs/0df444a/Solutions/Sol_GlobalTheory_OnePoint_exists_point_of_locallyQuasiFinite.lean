-- Prove2me | solution 1 for GlobalTheory.OnePoint.exists_point_of_locallyQuasiFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:16.987987+00:00
-- url     : https://prove2.me/submissions/b1798e60-88bd-44db-9d95-e7c528ad9948

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
import Theorems.Thm_GlobalTheory_OnePoint_point_ext
import Theorems.Thm_GlobalTheory_OnePoint_exists_section_of_locallyQuasiFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
variable {K : Type u} [Field K]
namespace GlobalTheory.OnePoint
theorem _root_.solution {X Y : Scheme.{u}} (κ : X ⟶ Y)
    [LocallyQuasiFinite κ] (L : Type u) [Field L] [Algebra K L] [IsIntegrallyClosedIn K L]
    (x : Spec (.of L) ⟶ X) (y : Spec (.of K) ⟶ Y) (hx : x ≫ κ = specAlg(K, L) ≫ y) :
    ∃ x₀ : Spec (.of K) ⟶ X, specAlg(K, L) ≫ x₀ = x ∧ x₀ ≫ κ = y ∧
      ∀ x₁ : Spec (.of K) ⟶ X, specAlg(K, L) ≫ x₁ = x → x₁ = x₀ := by
  obtain ⟨s, hs, hs', -⟩ := exists_section_of_locallyQuasiFinite (K := K) (pullback.snd κ y) L
    (pullback.lift x _ hx) (pullback.lift_snd _ _ _)
  have hg : specAlg(K, L) ≫ s ≫ pullback.fst κ y = x := by
    rw [reassoc_of% hs, pullback.lift_fst]
  refine ⟨s ≫ pullback.fst κ y, hg, ?_, fun x₁ h₁ ↦ point_ext _ (h₁.trans hg.symm)⟩
  rw [Category.assoc, pullback.condition, reassoc_of% hs']
end GlobalTheory.OnePoint
