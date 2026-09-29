-- Prove2me | solution 1 for M4aHerbrand.IdeleGaloisDescent.exists_mulDistribMulAction_smul_eq_classAct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2f0c9563-fba3-546b-8be2-40af307686b2

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_mulDistribMulAction_smul_eq_classAct

set_option autoImplicit false
open NumberField M4aHerbrand

theorem solution
    (E F : Type*) [Field E] [Field F] [NumberField F] [Algebra E F]
    (D : IdeleGaloisDescent (𝓞 F) E F) :
    ∃ (_ : MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)),
      ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c := by
  classical

  have h1 : ∀ c : IdeleClassGroup (𝓞 F) F, D.classAct 1 c = c := by
    intro c
    induction c using QuotientGroup.induction_on with
    | H u =>
      show (QuotientGroup.mk (D.unitsAct 1 u) : IdeleClassGroup (𝓞 F) F) = QuotientGroup.mk u
      rw [map_one]
      rfl
  have hmul : ∀ (g h : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F),
      D.classAct (g * h) c = D.classAct g (D.classAct h c) := by
    intro g h c
    induction c using QuotientGroup.induction_on with
    | H u =>
      show (QuotientGroup.mk (D.unitsAct (g * h) u) : IdeleClassGroup (𝓞 F) F)
        = QuotientGroup.mk (D.unitsAct g (D.unitsAct h u))
      rw [map_mul]
      rfl
  refine ⟨{ smul := fun g c => D.classAct g c
            one_smul := fun c => h1 c
            mul_smul := fun g h c => hmul g h c
            smul_mul := fun g c c' => map_mul (D.classAct g) c c'
            smul_one := fun g => map_one (D.classAct g) }, fun g c => rfl⟩

end S_M4aHerbrand_IdeleGaloisDescent_exists_mulDistribMulAction_smul_eq_classAct
end P2MW
export P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_mulDistribMulAction_smul_eq_classAct (solution)
