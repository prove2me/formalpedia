-- Prove2me | solution 1 for GlobalTheory.OrbitScalar.exists_mem_dom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:15:38.127804+00:00
-- url     : https://prove2.me/submissions/d95c7363-9d42-4ae4-8b01-fad85d698f75

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsSmulOfPreservesFrameOrbits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix
open GlobalTheory GlobalTheory.OrbitScalar
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.OrbitScalar
namespace _root_.GlobalTheory.OrbitScalar
theorem _root_.solution (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) : X.dom.Nonempty := by
  choose P hP hG using X.signature
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  change 0 < _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i * (_root_.ReciprocityTheory.ChartRestriction.G.FD.lminor (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (P τ)) i).re
  rw [hG τ]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn
  rw [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
  simp only [Function.comp_apply, Fin.coe_castLE]
  rw [← Complex.ofReal_prod, Complex.ofReal_re,
    Fin.prod_univ_eq_prod_range (fun a => _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a) i]
  refine mul_self_pos.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => ?_)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
  split_ifs <;> norm_num
end _root_.GlobalTheory.OrbitScalar
end GlobalTheory.OrbitScalar
