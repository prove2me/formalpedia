-- Prove2me | solution 1 for GlobalTheory.LocSplit.exists_val_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:44.503353+00:00
-- url     : https://prove2.me/submissions/08e73dd8-5b79-4b03-88e9-ecc14227a197

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIrreducible
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open Formalism.MainNotions.S.Loc NumberField IsDedekindDomain ValuativeRel
open GlobalTheory GlobalTheory.LocSplit
variable {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (ι : F →+* K) (hd : DenseRange ι)
  (hv : ∀ x y : F, valuation K (ι x) ≤ valuation K (ι y) ↔ p.valuation F x ≤ p.valuation F y)
include hd
namespace GlobalTheory.LocSplit
theorem _root_.solution (x : K) (hx : x ≠ 0) :
    ∃ y : F, y ≠ 0 ∧ valuation K (ι y) = valuation K x := by
  have h0 : valuation K x ≠ 0 := by simpa using hx
  obtain ⟨y, hy⟩ := hd.mem_nhds ((valuation K).locally_const h0)
  refine ⟨y, ?_, hy⟩
  rintro rfl
  exact h0 (by simpa using (show valuation K (ι 0) = valuation K x from hy).symm)
end GlobalTheory.LocSplit
