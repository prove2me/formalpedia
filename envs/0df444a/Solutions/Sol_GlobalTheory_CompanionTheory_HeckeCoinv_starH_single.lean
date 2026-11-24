-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeCoinv.starH_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:39:20.3488+00:00
-- url     : https://prove2.me/submissions/b02ef45b-0de0-448b-95f2-e518b5c821a4

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ModularityStatement
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.Fl
open scoped InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeCoinv
variable {G : Type} [Group G] {K : Subgroup G}
namespace GlobalTheory.CompanionTheory.HeckeCoinv
theorem _root_.solution (hp : IsHeckePair K) (h : Hk K) (x : G ⧸ K) :
    (starH hp h).1 (Finsupp.single x 1) = rowF hp h x := by
  simp [starH]
end GlobalTheory.CompanionTheory.HeckeCoinv
