-- Prove2me | solution 1 for GlobalTheory.SW.Base.classSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:06:13.137806+00:00
-- url     : https://prove2.me/submissions/03d6a4c4-4ed1-4ef5-93e3-3735ff56eaae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Theorems.Thm_GlobalTheory_SW_Base_cls_eq_iff
import Theorems.Thm_GlobalTheory_SW_Base_wt_moves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open GlobalTheory GlobalTheory.SW
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
open GlobalTheory.SW.Base
namespace GlobalTheory.SW.Base
theorem _root_.solution {M : ℕ} {f : Lt E n → ℂ} (hf : IsClassFn M f) (s : Cls E n M → Vset E n M)
    (hs : ∀ c, Quot.mk _ (s c) = c) :
    classSum M f = ∑ᶠ c : Cls E n M, (wt M (s c).1 : ℂ) * f (s c).1 := by
  refine finsum_congr fun c => ?_
  obtain ⟨h, hh, m⟩ := (cls_eq_iff (s c) (Quot.out c)).1 ((hs c).trans (Quot.out_eq c).symm)
  rw [wt_moves hh m, hf h hh _ (s c).2 _ (Quot.out c).2 m]
end GlobalTheory.SW.Base
