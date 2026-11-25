-- Prove2me | solution 1 for GlobalTheory.HWL.exists_of_layers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:58.700557+00:00
-- url     : https://prove2.me/submissions/73d4b376-b9d1-4df7-b092-a99b3729ee09

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsOfLayers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HWL
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct
variable {l : ℕ} [Fact l.Prime]
variable {P : LocPrime l} {K : FinExt l} {s : ℕ} {LL : FinExt l} {Γ : GamS P K s LL}
set_option maxHeartbeats 2000000
namespace GlobalTheory.HWL
theorem _root_.solution (P : LocPrime l) (AI : LocAinf l P)
    (h : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → Nonempty (Layers P AI K s LL))
    (ht : ∀ K : FinExt l, P.ιB (AI.ιA AI.μ) - P.ιB P.tB ∈ (P.PD K).Fil 2)
    (hπ : ∀ K : FinExt l, ∃ u ∈ (P.PD K).Fil 0, P.ιB (AI.ιA AI.π₁) * u = 1) :
    ∃ H : LocHW l P, ∃ F : LocFon l P AI H, Nonempty (LocCmpT l P AI H F) :=
  ⟨⟨fun K s LL g => toWach (h K s LL g).some.Cl (h K s LL g).some.Cm, fun _ _ _ _ => rfl,
      fun K s LL g T => (h K s LL g).some.Mo.N_proj T⟩,
    ⟨fun K s LL g => ⟨toEt (h K s LL g).some.Cl (h K s LL g).some.Cm, (h K s LL g).some.ioW⟩⟩,
    ⟨⟨fun K s LL g => ⟨toCmp (h K s LL g).some.Cl (h K s LL g).some.Cm, ht K, hπ K⟩⟩⟩⟩
end GlobalTheory.HWL
