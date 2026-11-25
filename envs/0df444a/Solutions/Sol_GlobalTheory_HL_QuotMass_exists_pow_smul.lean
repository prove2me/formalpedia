-- Prove2me | solution 1 for GlobalTheory.HL.QuotMass.exists_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:24:39.013811+00:00
-- url     : https://prove2.me/submissions/015670ee-85f3-4d3c-930b-145e8b480557

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
import Theorems.Thm_GlobalTheory_HL_QuotMass_exists_pow_mul
import Theorems.Thm_GlobalTheory_HL_QuotMass_pow_smul_mono
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_ThickOrbit_smul_mem
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
namespace GlobalTheory.HL.QuotMass
theorem _root_.solution (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {n : ℕ}
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) {m : ℕ} (x : Fin m → Fin n → E) :
    ∃ e : ℕ, ∀ a, algebraMap F E ((ϖ : F) ^ e) • x a ∈ Λ := by
  have h1 : ∀ v : Fin n → E, ∃ e : ℕ, algebraMap F E ((ϖ : F) ^ e) • v ∈ Λ := by
    intro v
    have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
    induction hv using Submodule.span_induction with
    | mem v hv => exact ⟨0, by simpa using hv⟩
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨e, he⟩ := ha
      obtain ⟨f, hf⟩ := hb
      refine ⟨max e f, ?_⟩
      rw [smul_add]
      exact Λ.add_mem (pow_smul_mono L ϖ Λ (le_max_left _ _) he)
        (pow_smul_mono L ϖ Λ (le_max_right _ _) hf)
    | smul c a _ ha =>
      obtain ⟨e, he⟩ := ha
      obtain ⟨f, hf⟩ := exists_pow_mul L ϖ hϖ c
      refine ⟨f + e, ?_⟩
      have : algebraMap F E ((ϖ : F) ^ (f + e)) • c • a =
          (algebraMap F E ((ϖ : F) ^ f) * c) • algebraMap F E ((ϖ : F) ^ e) • a := by
        rw [smul_smul, smul_smul, pow_add, map_mul]; congr 1; ring
      rw [this]
      exact Λ.smul_mem (⟨_, hf⟩ : L.O) he
  choose e he using h1
  exact ⟨Finset.univ.sup fun a => e (x a), fun a =>
    pow_smul_mono L ϖ Λ (Finset.le_sup (f := fun a => e (x a)) (Finset.mem_univ a)) (he _)⟩
end GlobalTheory.HL.QuotMass
