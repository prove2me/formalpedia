-- Prove2me | solution 1 for GlobalTheory.SqLB.pq_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:38:40.155574+00:00
-- url     : https://prove2.me/submissions/04d2a621-8283-44b2-a431-967979648dc6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSquareGeneratorThroughSquareIso
import Theorems.Thm_GlobalTheory_SqLB_gq_trans
import Theorems.Thm_GlobalTheory_SqLB_trF_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SqLB
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace GlobalTheory.SqLB
theorem _root_.solution {w : LB.Iso (sq L') ((sq L).pull F)} (hw : PGen w) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y)
    (z : Z) {p p' : K → L.ι} {q q' : K → L'.ι} (hp : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p)
    (hp' : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p') (hq : r z ∈ LB.wchart L' φ' q) (hq' : r z ∈ LB.wchart L' φ' q') :
    pq w φ' ε r z p q = trF (fun k => φ' k ≫ F) (fun k => 2 * ε k) r z p p' *
      (trF φ' (fun k => 2 * ε k) r z q q')⁻¹ * pq w φ' ε r z p' q' := by
  rw [trF_two, trF_two, pq, pq, trF, trF, ← Finset.prod_zpow, ← Finset.prod_zpow, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [gq_trans hw (r ≫ φ' k) z (Set.mem_iInter.1 hp k) (Set.mem_iInter.1 hp' k) (Set.mem_iInter.1 hq k)
    (Set.mem_iInter.1 hq' k), Category.assoc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  rw [smul_add, smul_add, smul_comm (ε k) (2 : ℤ), smul_neg, smul_comm (ε k) (2 : ℤ)]
end GlobalTheory.SqLB
