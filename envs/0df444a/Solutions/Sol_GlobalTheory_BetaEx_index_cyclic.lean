-- Prove2me | solution 1 for GlobalTheory.BetaEx.index_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:40.308841+00:00
-- url     : https://prove2.me/submissions/a3b29de0-f297-4b19-a742-db3e72468dba

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal

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
open GlobalTheory GlobalTheory.BetaEx
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
namespace GlobalTheory.BetaEx
theorem _root_.solution (M' : Submodule (𝓞 E) (Fin n → E)) (m : Fin n → E) :
    Ideal.absNorm (M'.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)) =
      M'.toAddSubgroup.relIndex (M' ⊔ Submodule.span (𝓞 E) {m}).toAddSubgroup := by
  rw [Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left, LinearMap.span_singleton_eq_range,
    Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact AddSubgroup.index_comap M'.toAddSubgroup (LinearMap.toSpanSingleton (𝓞 E) _ m).toAddMonoidHom
end GlobalTheory.BetaEx
