-- Prove2me | solution 1 for GlobalTheory.Jet.polyDeriv_smul_dir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:21:12.517057+00:00
-- url     : https://prove2.me/submissions/1d46837f-723b-4017-a24b-5e6ca0248413

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Theorems.Thm_GlobalTheory_Jet_card_toMultiset_eq_degree
import Theorems.Thm_GlobalTheory_Jet_degree_eq_of_mem_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.Jet
variable {σ W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup W'] [NormedSpace ℂ W']
namespace GlobalTheory.Jet
theorem _root_.solution {P : MvPolynomial σ ℂ} {a : ℕ} (hP : P.IsHomogeneous a) (c : ℂ)
    (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv P (fun i => c • u i) F x = c ^ a * polyDeriv P u F x := by
  unfold polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [ContinuousMultilinearMap.map_smul_univ _ (fun _ => c), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  have h : c ^ Multiset.card (Finsupp.toMultiset m) = c ^ a := by
    rw [card_toMultiset_eq_degree, degree_eq_of_mem_support hP hm]
  rw [h]
  ring
end GlobalTheory.Jet
