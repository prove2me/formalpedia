-- Prove2me | solution 1 for GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:31:58.849707+00:00
-- url     : https://prove2.me/submissions/593e751e-ab9d-4471-b9ac-1293124a65d1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Theorems.Thm_GlobalTheory_HL_SelfDual_span_range_eq_top
import Theorems.Thm_GlobalTheory_HL_SelfDual_exists_isom
import Theorems.Thm_GlobalTheory_HL_SelfDual_exists_orthonormal
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.SelfDual
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → (∀ Λ, IsSD L Hm Λ → ∃ b : Fin n → Fin n → E, (∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0) ∧ Λ = Submodule.span L.O (Set.range b)) ∧ ∀ Λ Λ', IsSD L Hm Λ → IsSD L Hm Λ' → ∃ g ∈ isomG L Hm, g • Λ = Λ' := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH
  refine ⟨fun Λ hΛ => exists_orthonormal L hH hΛ, fun Λ Λ' hΛ hΛ' => ?_⟩
  obtain ⟨b, ho, rfl⟩ := exists_orthonormal L hH hΛ
  obtain ⟨b', ho', rfl⟩ := exists_orthonormal L hH hΛ'
  obtain ⟨g, hg, h⟩ := exists_isom L (span_range_eq_top L hΛ.1) (span_range_eq_top L hΛ'.1) ho ho'
  refine ⟨g, hg, ?_⟩
  rw [Submodule.smul_span, Set.smul_set_range]
  simp only [LinearEquiv.smul_def, h]
end GlobalTheory.HL.SelfDual
