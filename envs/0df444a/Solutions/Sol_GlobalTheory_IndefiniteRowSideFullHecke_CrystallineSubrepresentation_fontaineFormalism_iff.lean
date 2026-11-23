-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.fontaineFormalism_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:23.324178+00:00
-- url     : https://prove2.me/submissions/f2e11c7e-3d43-4728-a183-549981a830a6

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_CrystallineSubrepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct
variable (l : ℕ) [Fact l.Prime] (P : LocPrime l)
namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation
theorem _root_.solution :
    FontaineFormalism l P ↔ ∀ K LL : FinExt l, FormalismFor (P.PD K) ↥LL.1 :=
  ⟨fun h K LL => ⟨h.1 K, h.2.1 K LL, h.2.2.1 K LL, h.2.2.2.1 K LL, h.2.2.2.2.1 K LL,
      h.2.2.2.2.2.1 K LL, h.2.2.2.2.2.2.1 K LL, h.2.2.2.2.2.2.2.1 K LL, h.2.2.2.2.2.2.2.2.1 K LL,
      h.2.2.2.2.2.2.2.2.2 K LL⟩,
    fun h => ⟨fun K => (h K K).1, fun K LL => (h K LL).2.1, fun K LL => (h K LL).2.2.1,
      fun K LL => (h K LL).2.2.2.1, fun K LL => (h K LL).2.2.2.2.1,
      fun K LL => (h K LL).2.2.2.2.2.1, fun K LL => (h K LL).2.2.2.2.2.2.1,
      fun K LL => (h K LL).2.2.2.2.2.2.2.1, fun K LL => (h K LL).2.2.2.2.2.2.2.2.1,
      fun K LL => (h K LL).2.2.2.2.2.2.2.2.2⟩⟩
end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation
