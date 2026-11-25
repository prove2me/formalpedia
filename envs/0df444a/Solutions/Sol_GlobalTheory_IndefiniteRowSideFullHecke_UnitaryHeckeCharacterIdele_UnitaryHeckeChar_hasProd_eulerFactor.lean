-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.hasProd_eulerFactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:56:19.687518+00:00
-- url     : https://prove2.me/submissions/24e0818b-a21d-4c8f-a873-46d53a45ad58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_UnitaryHeckeChar_multipliable_eulerFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
variable {E : Type} [Field E] [NumberField E]
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
theorem _root_.solution (χ : UnitaryHeckeChar E) (s : {s : ℂ // 1 < s.re}) :
    HasProd (fun P => χ.eulerFactor P s) (χ.finiteL s) :=
  (χ.multipliable_eulerFactor s.2).hasProd
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
