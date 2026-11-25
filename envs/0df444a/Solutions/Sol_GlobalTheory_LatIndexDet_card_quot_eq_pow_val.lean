-- Prove2me | solution 1 for GlobalTheory.LatIndexDet.card_quot_eq_pow_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:40:03.016688+00:00
-- url     : https://prove2.me/submissions/3ecd8266-d54f-44b9-a4c4-afe784b401b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapDetRestrict
import Theorems.Thm_GlobalTheory_LatIndexDet_val_algebraMap
import Theorems.Thm_GlobalTheory_LatIndexDet_isTorsionFree_lat
import Theorems.Thm_GlobalTheory_LatIndexDet_algebraMap_det_restrict
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_card_coker_eq_pow_addVal_det
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
noncomputable section
open GlobalTheory GlobalTheory.LatIndexDet
namespace GlobalTheory.LatIndexDet
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (V : Type) [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V] [FiniteDimensional E V] (N : Submodule O V), N.FG → Submodule.span E (N : Set V) = ⊤ → ∀ T : V →ₗ[E] V, LinearMap.det T ≠ 0 → (∀ x ∈ N, T x ∈ N) → (Nat.card (↥N ⧸ (N.map (T.restrictScalars O)).comap N.subtype) : ℚ) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (LinearMap.det T) := by
  intro O _ _ _ _ E _ _ _ V _ _ _ _ _ N hfg hspan T hdet hT
  haveI := isTorsionFree_lat O E N
  haveI : Module.Finite O N := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free O N := Module.free_of_finite_type_torsion_free'
  let T' : N →ₗ[O] N := (T.restrictScalars O).restrict hT
  have hdetT : algebraMap O E (LinearMap.det T') = LinearMap.det T := algebraMap_det_restrict O E N hspan T hT
  have hdet' : LinearMap.det T' ≠ 0 := fun h => hdet (by rw [← hdetT, h, map_zero])
  have hrange : (N.map (T.restrictScalars O)).comap N.subtype = LinearMap.range T' := by
    ext ⟨x, hx⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
    · rintro ⟨⟨y, hy⟩, hyx⟩
      exact ⟨y, hy, congrArg Subtype.val hyx⟩
  rw [hrange, GlobalTheory.UnramOrder.card_coker_eq_pow_addVal_det T' hdet', ← hdetT, val_algebraMap O E hdet']
  push_cast
  rw [zpow_natCast]
end GlobalTheory.LatIndexDet
