-- Prove2me | solution 1 for GlobalTheory.HL.EichlerLocal.moved_locally_constant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:14:13.867199+00:00
-- url     : https://prove2.me/submissions/e785a407-812e-43c0-9bb2-37922c20920c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerLatticeLocallyConstantData
import Theorems.Thm_P2M_GlobalTheory_HL_EichlerLocal_smul_mem__68d4331394de
import Theorems.Thm_GlobalTheory_HL_EichlerLocal_mem_of_close
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.EichlerLocal
open GlobalTheory.HL.Eichler
namespace GlobalTheory.HL.EichlerLocal
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ Λ : Submodule L.O S.V, IsSD L S.Hm Λ → ∀ c : ℕ, ∃ N : ℕ, ∀ (x x₁ u u₁ : S.V) (s s₁ : E), S.h x x = 0 → S.h u x = 0 → s + L.cj s = S.h u u → S.h x₁ x₁ = 0 → S.h u₁ x₁ = 0 → s₁ + L.cj s₁ = S.h u₁ u₁ → algebraMap F E ((S.ϖ : F) ^ c) • x ∈ Λ → u ∈ Λ → s ∈ L.O → (∃ y ∈ Λ, x₁ - x = algebraMap F E ((S.ϖ : F) ^ N) • y) → (∃ y ∈ Λ, u₁ - u = algebraMap F E ((S.ϖ : F) ^ N) • y) → (∃ y ∈ L.O, s₁ - s = algebraMap F E ((S.ϖ : F) ^ N) * y) → S.moved Λ x₁ u₁ s₁ = S.moved Λ x u s := by
  intro F _ _ _ _ _ E _ _ _ L r k S Λ hΛ c
  refine ⟨c * 4, ?_⟩
  rintro x x₁ u u₁ s s₁ hx hu hs hx₁ hu₁ hs₁ hxΛ huΛ hsO ⟨a, ha, ea⟩ ⟨b, hb, eb⟩ ⟨t, ht, et⟩
  rw [pow_mul, map_pow] at ea eb et
  have hp : algebraMap F E ((S.ϖ : F) ^ c) ∈ L.O :=
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (Subring.pow_mem _ S.ϖ.2 c)
  have hpc : L.cj (algebraMap F E ((S.ϖ : F) ^ c)) = algebraMap F E ((S.ϖ : F) ^ c) :=
    L.cj.commutes _
  generalize algebraMap F E ((S.ϖ : F) ^ c) = p at *
  obtain rfl : x₁ = x + p ^ 4 • a := by rw [← ea]; abel
  obtain rfl : u₁ = u + p ^ 4 • b := by rw [← eb]; abel
  obtain rfl : s₁ = s + p ^ 4 * t := by rw [← et]; ring
  ext v
  constructor
  · intro hv
    have h := mem_of_close L S.herm.1 hΛ hp hpc hx₁ hu₁ hs₁
      (by
        rw [smul_add]
        exact Λ.add_mem hxΛ (smul_mem' L hp (smul_mem' L (L.O.pow_mem hp 4) ha)))
      (Λ.add_mem huΛ (smul_mem' L (L.O.pow_mem hp 4) hb))
      (L.O.add_mem hsO (L.O.mul_mem (L.O.pow_mem hp 4) ht))
      (Λ.neg_mem ha) (Λ.neg_mem hb) (L.O.neg_mem ht) hv
    simp only [smul_neg, mul_neg, add_neg_cancel_right] at h
    exact h
  · intro hv
    exact mem_of_close L S.herm.1 hΛ hp hpc hx hu hs hxΛ huΛ hsO ha hb ht hv
end GlobalTheory.HL.EichlerLocal
