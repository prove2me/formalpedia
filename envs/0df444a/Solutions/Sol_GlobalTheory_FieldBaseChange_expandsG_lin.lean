-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.expandsG_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:35:05.375798+00:00
-- url     : https://prove2.me/submissions/d3b8eee5-62e3-4210-b42e-9a55b697dd61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Theorems.Thm_GlobalTheory_FieldBaseChange_expandsG_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution (k : ℕ) (c : F) {v v' : GroupSec U F k} {s s' : Fam D.toPre F k}
    (h : U.ExpandsG F k v s) (h' : U.ExpandsG F k v' s') :
    U.ExpandsG F k (c • v + v' : GroupSec U F k) (c • s + s') := by
  obtain ⟨n, a, x, hx, e₁, e₂⟩ := (expandsG_iff U F k v s).1 h
  obtain ⟨n', a', x', hx', e₁', e₂'⟩ := (expandsG_iff U F k v' s').1 h'
  refine (expandsG_iff U F k _ _).2 ⟨n + n', Fin.append (fun i => c * a i) a', Fin.append x x',
    fun i => ?_, ?_, fun α => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hx i
    · rw [Fin.append_right]; exact hx' i
  · rw [Fin.sum_univ_add, e₁, e₁', Finset.smul_sum]
    simp only [Fin.append_left, Fin.append_right, smul_smul]
  · rw [Fin.sum_univ_add, map_add, map_smul, e₂, e₂', Finset.smul_sum]
    simp only [Fin.append_left, Fin.append_right, smul_smul]
end GlobalTheory.FieldBaseChange
