-- Prove2me | solution 1 for GlobalTheory.LocalInv.galPol_speh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:19:05.014811+00:00
-- url     : https://prove2.me/submissions/1a4b6057-3fb8-4476-b296-aae54cf07658

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt
import Theorems.Thm_GlobalTheory_LocalInv_galPol_foldr
import Theorems.Thm_GlobalTheory_LocalInv_list_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LocalInv
open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.LocalInv
theorem _root_.solution (p : Part A.CG) (w : PlE H) (ha : A.unr (A.locG p.π w)) (s : ℝ) :
    A.unr (spehLoc N A p w) ∧ galPol A (A.lpTw (spehLoc N A p w) s) =
      ∏ k ∈ Finset.range p.d, galPol A (A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k + s)) := by
  have h := galPol_foldr N A _ ha (fun k => ((p.d : ℝ) - 1) / 2 - k) s
    (do let a ← List.range p.d; pure ((a : ℕ) : ℝ))
  refine ⟨h.1, h.2.trans ?_⟩
  rw [list_coe, List.map_map, ← List.prod_toFinset _ List.nodup_range, List.toFinset_range]
  rfl
end GlobalTheory.LocalInv
