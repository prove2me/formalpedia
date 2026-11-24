-- Prove2me | solution 1 for GlobalTheory.Published.landherrSt_of_landherr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:29:39.825015+00:00
-- url     : https://prove2.me/submissions/b6918752-641d-4aa6-b640-67ae410d3f9e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__LandherrStIffLandherr_9fec213082f17e18
import Theorems.Thm_GlobalTheory_Published_LandherrSt_herm_mulVec
import Theorems.Thm_GlobalTheory_Published_Landherr_of_signature
import Theorems.Thm_GlobalTheory_Published_cc_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.Published
namespace LandherrSt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end LandherrSt
open NumberField Matrix in
open scoped nonZeroDivisors in
private lemma cc_inv' {E : Type} [Field E] [NumberField E] [IsCMField E] (z : E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.cc z⁻¹ = (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc z)⁻¹ := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  exact map_inv₀ _ _
namespace LandherrSt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end LandherrSt
end GlobalTheory.Published
end

set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open NumberField Matrix
open scoped nonZeroDivisors
namespace GlobalTheory.Published
namespace _root_.GlobalTheory.Published
theorem _root_.solution (H : _root_.GlobalTheory.Published.Landherr) :
    _root_.GlobalTheory.Published.LandherrSt := by
  intro E _ _ _ r G G' hG hG' hd hd' hsig hdet
  obtain ⟨z, hz⟩ := hdet
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_mul] at hz
    exact hd' hz
  obtain ⟨P, hP, hPG⟩ :=
    _root_.GlobalTheory.Published.Landherr.of_signature H hG hG'
      hd hd' Set.univ (fun _ => Or.inl trivial) (fun τ _ => hsig τ) ⟨z⁻¹, by
        rw [hz, cc_inv']
        field_simp [_root_.GlobalTheory.Published.cc_ne_zero hz0]⟩
  refine ⟨nonsingInvUnit P (isUnit_iff_ne_zero.2 hP), fun x y => ?_⟩
  rw [show ((nonsingInvUnit P (isUnit_iff_ne_zero.2 hP) : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = P
    from rfl, _root_.GlobalTheory.Published.LandherrSt.herm_mulVec, ← hPG]
end _root_.GlobalTheory.Published
end GlobalTheory.Published
