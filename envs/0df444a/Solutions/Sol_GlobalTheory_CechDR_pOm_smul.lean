-- Prove2me | solution 1 for GlobalTheory.CechDR.pOm_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:37:34.756797+00:00
-- url     : https://prove2.me/submissions/126decf9-4551-4d40-8a6f-9baf03c0a596

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_mOm_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
open CatCoh
universe v u v' u' v'' u''
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
variable {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'')
namespace GlobalTheory.CechDR
theorem _root_.solution {j : ℕ} (b : F.obj T) (x : Om R (F.obj T) j) :
    pOm F j φ (b • x) = mp F φ b • pOm F j φ x := by
  unfold pOm
  exact (semiHom_mp F φ).mOm_smul b x
end GlobalTheory.CechDR
