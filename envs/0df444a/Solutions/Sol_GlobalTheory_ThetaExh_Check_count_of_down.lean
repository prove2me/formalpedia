-- Prove2me | solution 1 for GlobalTheory.ThetaExh.Check.count_of_down
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:37:36.624363+00:00
-- url     : https://prove2.me/submissions/d3db632b-b762-45bf-bb97-1718e3f3e368

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_HeckeSplitOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_SplitLiftOfLiftParam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaExh GlobalTheory.ThetaExh.Check
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.ThetaExh
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.ThetaExh.Check
theorem _root_.solution (i : N.Loc) (h1 : TypeNZ N A i) (h2 : DownMem N A i) : Count N A i := by
  intro x hx Sig hS
  let g : ↥(eigC N A i x) →ₗ[ℂ] ↥(MjSig N A i Sig) :=
    ((what₂.thetaP (N.mu i) (N.j i)).domRestrict (eigC N A i x)).codRestrict (MjSig N A i Sig)
      (fun v => h2 x hx Sig hS (Submodule.mem_map_of_mem v.2))
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv' : what₂.thetaP (N.mu i) (N.j i) (v : what₂.Mt (N.mu i) (N.j i)) = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.1 hv)
    exact Subtype.ext (h1 x hx v v.2 hv')
  exact LinearMap.finrank_le_finrank_of_injective hinj
end GlobalTheory.ThetaExh.Check
