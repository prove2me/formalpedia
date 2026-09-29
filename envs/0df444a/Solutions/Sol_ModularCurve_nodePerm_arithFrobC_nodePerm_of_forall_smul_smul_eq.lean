-- Prove2me | solution 1 for ModularCurve.nodePerm_arithFrobC_nodePerm_of_forall_smul_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/0f17e162-9b50-57f1-9e15-1d2ecaa14bcf

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_nodePerm_arithFrobC_nodePerm_of_forall_smul_smul_eq
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem solution
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k]
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hfix : ∀ w ∈ W, arithFrobC q k N • (arithFrobC q k N • w) = w)
    (hstab : SemilinearAut.IsNodeStable (nodePairsOfPlaces (arithFrobC q k N) W)
      (arithFrobC q k N))
    (s : ↥(nodePairsOfPlaces (arithFrobC q k N) W)) :
    SemilinearAut.nodePerm (nodePairsOfPlaces (arithFrobC q k N) W) (arithFrobC q k N) hstab
        (SemilinearAut.nodePerm (nodePairsOfPlaces (arithFrobC q k N) W) (arithFrobC q k N)
          hstab s) = s := by
  obtain ⟨s, hs⟩ := s
  obtain ⟨w, hw, rfl⟩ := (mem_nodePairsOfPlaces_iff (arithFrobC q k N) W s).mp hs
  apply Subtype.ext
  rw [SemilinearAut.nodePerm_apply, SemilinearAut.nodePerm_apply]
  show (arithFrobC q k N • (arithFrobC q k N • (smulNodePair (arithFrobC q k N) w).1),
      arithFrobC q k N • (arithFrobC q k N • (smulNodePair (arithFrobC q k N) w).2))
    = smulNodePair (arithFrobC q k N) w
  rw [smulNodePair_fst, smulNodePair_snd, hfix w hw]
  rfl

end S_ModularCurve_nodePerm_arithFrobC_nodePerm_of_forall_smul_smul_eq
end P2MW
export P2MW.S_ModularCurve_nodePerm_arithFrobC_nodePerm_of_forall_smul_smul_eq (solution)
