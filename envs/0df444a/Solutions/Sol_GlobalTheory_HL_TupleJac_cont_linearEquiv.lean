-- Prove2me | solution 1 for GlobalTheory.HL.TupleJac.cont_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:03:02.79027+00:00
-- url     : https://prove2.me/submissions/3568d5d7-d9f4-4d07-9913-b982cfeb13e0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelVolMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometry
import Theorems.Thm_GlobalTheory_HL_TupleJac_exists_int_basis
import Theorems.Thm_GlobalTheory_HL_TupleJac_exists_lat_basis
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_ContAut_cont_image
import Theorems.Thm_GlobalTheory_T_relative_lattice_volume_of_det_valuation
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_inj
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TupleJac
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.TupleJac
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) (ϖ : 𝒪[F])
    (hϖ : Irreducible ϖ) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (hH : IsHermND L Hm) (Λ : Submodule L.O (Fin n → E))
    (hΛ : IsSD L Hm Λ) (m : ℕ) (φ : (Fin m → Fin n → E) ≃ₗ[E] (Fin m → Fin n → E))
    (a : ℤ) (u : (𝒪[F])ˣ)
    (hd : LinearMap.det φ.toLinearMap * L.cj (LinearMap.det φ.toLinearMap)
      = algebraMap F E ((ϖ : F) ^ a * ((u : 𝒪[F]) : F))) :
    ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) (φ '' T) ∧
      cont (tupLat L Λ m) (φ '' T) = (resQ ϖ : ℝ) ^ (-a) * cont (tupLat L Λ m) T := by
  obtain ⟨c, hc, hN⟩ := exists_int_basis L
  obtain ⟨B, hB⟩ := exists_lat_basis L Hm hH Λ hΛ
  have := L.free
  have h := GlobalTheory.T.relative_lattice_volume_of_det_valuation ϖ hϖ (Pi.basis fun _ : Fin m => c.smulTower B) (φ.restrictScalars F) a u
    (by
      apply GlobalTheory.UnramOrder.algebraMap_inj L
      rw [← hd, ← hN, ← LinearMap.det_restrictScalars]
      rfl) (tupLat L Λ m) (by
      intro x
      simp only [tupLat, AddSubgroup.mem_pi, Set.mem_univ, true_imp_iff,
        Submodule.mem_toAddSubgroup, hB, hc, Pi.basis_repr, Module.Basis.smulTower_repr]
      exact ⟨fun h i => h _ _ _, fun h j i k => h ⟨j, (k, i)⟩⟩)
  intro T hT
  have h2 := GlobalTheory.HL.ContAut.cont_image (tupLat L Λ m) (φ.restrictScalars F).toAddEquiv h.1 h.2.1 T hT
  rw [h.2.2] at h2
  exact h2
end GlobalTheory.HL.TupleJac
