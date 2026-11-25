-- Prove2me | solution 1 for GlobalTheory.HL.GlobalWit.symm_mem_of_maps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:49:15.560479+00:00
-- url     : https://prove2.me/submissions/f5bd19c2-3a5d-4be1-98d3-f37350abad7a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NumberFieldLatticeDeterminedByLocalLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationUnipotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CoordinateLatticeUniqueTermAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GlobalHermitianFramesRationalWitnessesPhase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.GlobalWit
section Local
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}
private lemma hf_apply_apply_of_mem_isomG (S : Frames L r k) {u : S.GLV} (hu : u ∈ isomG L S.Hm) (x y : S.V) :
    hf L S.Hm (u x) (u y) = hf L S.Hm x y := hu x y
variable [IsNonarchimedeanLocalField F] [CharZero F]
end Local
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
end GlobalTheory.HL.GlobalWit
end
end

set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GlobalWit
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}
namespace GlobalTheory.HL.GlobalWit
theorem _root_.solution (S : Frames L r k) {Λ : Submodule L.O S.V} (hsd : IsSD L S.Hm Λ) (u : S.GLV)
    (hu : u ∈ isomG L S.Hm) (hmap : ∀ x ∈ Λ, u x ∈ Λ) : ∀ y ∈ Λ, u.symm y ∈ Λ := by
  obtain ⟨-, hsd2⟩ := hsd
  intro y hy
  refine (hsd2 (u.symm y)).1 fun x hx => ?_
  rw [← hf_apply_apply_of_mem_isomG S hu x (u.symm y), LinearEquiv.apply_symm_apply]
  exact (hsd2 y).2 hy (u x) (hmap x hx)
end GlobalTheory.HL.GlobalWit
