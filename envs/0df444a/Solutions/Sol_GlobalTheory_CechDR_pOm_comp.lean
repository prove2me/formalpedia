-- Prove2me | solution 1 for GlobalTheory.CechDR.pOm_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:38:58.927372+00:00
-- url     : https://prove2.me/submissions/c1b73ec9-e9c5-404b-bf89-d70dcd748ac7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_mOm_mOm


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
theorem _root_.solution {j : ℕ} (x : Om R (F.obj T) j) : pOm F j (φ ≫ ψ) x = pOm F j ψ (pOm F j φ x) := by
  unfold pOm
  exact ((semiHom_mp F φ).mOm_mOm (semiHom_mp F ψ) (semiHom_mp F (φ ≫ ψ))
    (fun b ↦ (mp_comp F φ ψ b).symm) x).symm
end GlobalTheory.CechDR
