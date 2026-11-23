-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeTransfer.hk_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:13.000291+00:00
-- url     : https://prove2.me/submissions/a7fd9516-1e3e-484d-b55b-0b9f27b59c98

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithfulStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TransferStatementBis
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
open CompanionTheory.D.gk.admitted (stdPoly word word_nil word_cons)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeTransfer
variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {K : Subgroup G} {σ : G →* (H →L[ℂ] H)} {v : H}
namespace GlobalTheory.CompanionTheory.HeckeTransfer
theorem _root_.solution (h : Hk K) (g : G) (f : (G ⧸ K) →₀ ℂ) :
    lam K g ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) f) = (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (lam K g f) := by
  have hc := (Subalgebra.mem_centralizer_iff ℂ).1 h.2 (lam K g) ⟨g, rfl⟩
  exact congrArg (fun T : Module.End ℂ ((G ⧸ K) →₀ ℂ) => T f) hc
end GlobalTheory.CompanionTheory.HeckeTransfer
