-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.cocycle_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:53:25.514114+00:00
-- url     : https://prove2.me/submissions/1530a40f-241a-4964-b3cf-dce26af6b86d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_AdmissibleCharUnramified
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_AdmissibleCharUnramified_twCoef_chi_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct GlobalTheory.AdmLoc
open ReciprocityTheory.Def (Z1 H1)
variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (Γ : GalData G Qp LL O)
    (X : Type) [AddCommGroup X] [Module O X]
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified
theorem _root_.solution (z : ↥(Z1 (twCoef (Γ.Wchi 1) Γ.χ₁ X) ⊤)) (g h : G) :
    (z : G → O ⊗[O] X) (g * h) = (z : G → O ⊗[O] X) g + (z : G → O ⊗[O] X) h := by
  rw [cocycle_mul z g h, twCoef_chi_one]
end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified
