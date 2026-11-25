-- Prove2me | solution 1 for GlobalTheory.MoveFine.sOf_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:17:54.048423+00:00
-- url     : https://prove2.me/submissions/39cf371d-8ae3-43cd-8124-21680e52f8d5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerLatticeLocallyConstantDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFineSubgroupMovesAtLattice
import Theorems.Thm_GlobalTheory_MoveFine_h_add_l
import Theorems.Thm_GlobalTheory_MoveFine_h_smul_l
import Theorems.Thm_GlobalTheory_MoveFine_h_add_r
import Theorems.Thm_GlobalTheory_MoveFine_h_smul_r
import Theorems.Thm_GlobalTheory_MoveFine_algO
import Theorems.Thm_GlobalTheory_MoveFine_mem_intP
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.MoveFine
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.MoveFine
theorem _root_.solution {Λ : Submodule L.O S.V} (hΛ : IsSD L S.Hm Λ) (M v : ℕ)
    (hv : algebraMap F E S.ϖ ^ v * algebraMap F E 2⁻¹ ∈ L.O) (w y : S.MW) (hw : w.2.1 ∈ Λ) (hy : y ∈ intP S Λ) :
    ∃ z ∈ L.O, S.sOf (w + algebraMap F E S.ϖ ^ (M + v) • y) - S.sOf w = algebraMap F E S.ϖ ^ M * z := by
  obtain ⟨-, h3, h4⟩ := (mem_intP S).1 hy
  have hp := fun n => L.O.pow_mem (algO S S.ϖ) n
  have hi : ∀ x ∈ Λ, ∀ y ∈ Λ, S.h x y ∈ L.O := fun x hx y hy => (hΛ.2 y).2 hy x hx
  refine ⟨_, L.O.add_mem (L.O.mul_mem hv (L.O.add_mem (L.O.add_mem (hi _ hw _ h3) (hi _ h3 _ hw))
    (L.O.mul_mem (hp (M + v)) (hi _ h3 _ h3)))) (L.O.mul_mem (hp v) h4), ?_⟩
  simp only [Frames.sOf, Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, h_add_l, h_add_r, h_smul_l,
    h_smul_r, map_pow, AlgEquiv.commutes, smul_eq_mul]
  ring
end GlobalTheory.MoveFine
