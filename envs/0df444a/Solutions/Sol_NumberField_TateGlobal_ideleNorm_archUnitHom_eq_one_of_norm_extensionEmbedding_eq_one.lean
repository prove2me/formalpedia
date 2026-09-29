-- Prove2me | solution 1 for NumberField.TateGlobal.ideleNorm_archUnitHom_eq_one_of_norm_extensionEmbedding_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/89e002dc-5b2c-5d35-9a85-eed66600f9b5

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_NormPowChar

import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_ideleNorm_archUnitHom_eq_one_of_norm_extensionEmbedding_eq_one
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical

open NumberField.AdelicVolume in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : InfinitePlace K) (x : (v.Completion)ˣ)
    (hx : ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1) :
    ideleNorm K (archUnitHom v x) = 1 := by
  have h := NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K
    (archUnitHom v x) rfl
  rw [h]
  refine Finset.prod_eq_one fun w _ => ?_
  show ‖Function.update (1 : InfiniteAdeleRing K) v (x : v.Completion) w‖ ^ w.mult = 1
  by_cases hw : w = v
  · subst hw
    rw [Function.update_self, ← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _), hx, one_pow]
  · rw [Function.update_of_ne hw]
    show ‖(1 : w.Completion)‖ ^ w.mult = 1
    rw [norm_one, one_pow]

end S_NumberField_TateGlobal_ideleNorm_archUnitHom_eq_one_of_norm_extensionEmbedding_eq_one
end P2MW
export P2MW.S_NumberField_TateGlobal_ideleNorm_archUnitHom_eq_one_of_norm_extensionEmbedding_eq_one (solution)
