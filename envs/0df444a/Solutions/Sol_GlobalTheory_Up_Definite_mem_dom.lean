-- Prove2me | solution 1 for GlobalTheory.Up.Definite.mem_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:39:40.591958+00:00
-- url     : https://prove2.me/submissions/178c2fba-147c-4741-ab01-b5266aceddb9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_IsStrictDom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SingleMemIntVec
import Theorems.Thm_GlobalTheory_Up_Definite_gram_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate ComplexOrder Matrix
open GlobalTheory GlobalTheory.Up GlobalTheory.Up.Definite
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.Up.Definite
theorem _root_.solution (x : Frame (data E r).Ψ r) : x ∈ (data E r).dom ↔ ∀ τ, (mat x τ).det ≠ 0 := by
  refine ⟨fun h τ => (h τ).1, fun h τ => ⟨h τ, fun i => ?_⟩⟩
  have hp : psgn r i = 1 := by
    refine Finset.prod_eq_one fun a ha => ?_
    have := Finset.mem_range.mp ha
    have := i.isLt
    exact if_pos (by omega)
  have hd : ((mat x τ).map conj).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using h τ
  have hpd : (gram τ.1 (1 : Matrix (Fin r) (Fin r) E) (mat x τ)).PosDef := by
    rw [gram_one]
    exact Matrix.PosDef.conjTranspose_mul_self _
      (Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hd.isUnit))
  have := (hpd.submatrix (Fin.castLE_injective (Nat.le_of_lt_succ i.isLt))).det_pos
  change 0 < psgn r i * (lminor (gram τ.1 (1 : Matrix (Fin r) (Fin r) E) (mat x τ)) i).re
  rw [hp, one_mul]
  exact (Complex.lt_def.mp this).1
end GlobalTheory.Up.Definite
