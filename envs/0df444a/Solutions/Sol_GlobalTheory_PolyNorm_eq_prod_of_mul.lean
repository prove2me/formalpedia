-- Prove2me | solution 1 for GlobalTheory.PolyNorm.eq_prod_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:54.566994+00:00
-- url     : https://prove2.me/submissions/37fd94e8-0f3d-4459-9d37-4851569547f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.PolyNorm
namespace GlobalTheory.PolyNorm
theorem _root_.solution {K : Type} [Field K] [IsAlgClosed K] (M : K[X] →* K) (a : Multiset K)
    (hc : ∀ c, M (C c) = c ^ Multiset.card a)
    (hl : ∀ β, M (C β - X) = (a.map fun x => β - x).prod) (F : K[X]) :
    M F = (a.map fun x => F.eval x).prod := by
  let M' : K[X] →* K :=
    { toFun := fun F => (a.map fun x => F.eval x).prod
      map_one' := by simp
      map_mul' := by simp [Multiset.prod_map_mul] }
  have hc' : ∀ c, M (C c) = M' (C c) := fun c => by simp [hc, M']
  have hl' : ∀ β, M (X - C β) = M' (X - C β) := fun β => by
    have : (X - C β : K[X]) = C (-1) * (C β - X) := by simp
    rw [this, map_mul, map_mul, hc', hl]
    simp [M']
  change M F = M' F
  rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (p := F) IsAlgClosed.card_roots_eq_natDegree,
    map_mul, map_mul, hc', map_multiset_prod, map_multiset_prod, Multiset.map_map,
    Multiset.map_map]
  simp [hl']
end GlobalTheory.PolyNorm
