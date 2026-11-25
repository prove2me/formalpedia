-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections.toData_M_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:57:20.932464+00:00
-- url     : https://prove2.me/submissions/6509b4f9-7218-4334-be51-6a4f5040e392

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SectionInputData
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ZeroWeightSections_valZ_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable (Xo c)
variable {Xo c}
variable [Fintype (Comp Xo c)] (I : Input Xo c) (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
namespace GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
theorem _root_.solution (x : ∀ Z : Comp Xo c, AC Z) (hx : x ∈ (I.toData h δ fn yP).M) (Z : Comp Xo c) :
    x Z ∈ AG Z (I.toData h δ fn yP).ka := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨f, -, rfl⟩ := hx; exact valZ_mem h _ f Z
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx =>
    have : (a • x) Z = algebraMap c.F (Om Z) (a : c.F) • x Z := by
      rw [algebraMap_smul]; rfl
    rw [this]; exact Submodule.smul_mem _ _ hx
end GlobalTheory.IndefiniteRowSideFullHecke.ZeroWeightSections
