-- Prove2me | solution 1 for GlobalTheory.HL.QuotMass.relIndex_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:12:04.073329+00:00
-- url     : https://prove2.me/submissions/6e8ec717-21a6-48e0-ad4c-f7b75adc9a3d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerCommensurableUnramifiedHermitiaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruenceSubgroupLatticeStabilizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentIndependentNonnegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ThickOrbitSelfDualUnramifiedLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalisedContentThickenedSetIndependentOfLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ContentThickenedTupleOrbitNormalSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitaryGroupOrthogonalComplementUnimodularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MassEqConstMulContent
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_SelfDual_orthonormal_basis_and_one_orbit
import Theorems.Thm_GlobalTheory_T_latticeStabilizer_commensurable_unramified_hermitian
import Theorems.Thm_GlobalTheory_T_unitaryGroup_orthogonalComplement_unimodular
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.QuotMass
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [CharZero F]
namespace GlobalTheory.HL.QuotMass
theorem _root_.solution (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (hH : IsHermND L Hm)
    {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) (hΛ' : IsSD L Hm Λ') :
    ((isomG L Hm ⊓ stabL L Λ').relIndex (isomG L Hm ⊓ stabL L Λ) : ℝ) =
      (isomG L Hm ⊓ stabL L Λ).relIndex (isomG L Hm ⊓ stabL L Λ') := by
  obtain ⟨g, hg, hgΛ⟩ := (GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit L Hm hH).2 Λ Λ' hΛ hΛ'
  have hfix : fixG L Hm (Submodule.span E (Set.range (Fin.elim0 : Fin 0 → Fin n → E))) =
      isomG L Hm := by
    rw [Set.range_eq_empty, Submodule.span_empty]
    refine inf_eq_left.2 fun a _ => ⟨fun v => by simp, fun v hv => ?_⟩
    rw [(Submodule.mem_bot E).1 hv]; simp
  have h := GlobalTheory.T.unitaryGroup_orthogonalComplement_unimodular L Hm hH 0 Fin.elim0 (by simp) Λ Λ hΛ.1 hΛ.1 g (by rwa [hfix])
  rw [hfix, hgΛ] at h
  have hne : ((isomG L Hm ⊓ stabL L Λ).relIndex (isomG L Hm ⊓ stabL L Λ') : ℝ) ≠ 0 := by
    exact_mod_cast (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ' Λ hΛ'.1 hΛ.1 (isomG L Hm)).1
  simp only [invVol, Subgroup.relIndex_self, Nat.cast_one, div_one] at h
  exact (div_eq_one_iff_eq hne).1 h
end GlobalTheory.HL.QuotMass
