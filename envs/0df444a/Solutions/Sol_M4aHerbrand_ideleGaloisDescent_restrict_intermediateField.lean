-- Prove2me | solution 1 for M4aHerbrand.ideleGaloisDescent_restrict_intermediateField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/f0f2cbf9-2210-547b-b178-068de38636fc

import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_ideleGaloisDescent_restrict_intermediateField

set_option autoImplicit false

namespace M4aHerbrandRestrict

variable {R E F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
  [Algebra R F] [IsFractionRing R F] [Algebra E F]

private def restrictScalarsHom (E' : IntermediateField E F) : (F ≃ₐ[E'] F) →* (F ≃ₐ[E] F) where
  toFun g := g.restrictScalars E
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

private noncomputable def restrictDescent (D : M4aHerbrand.IdeleGaloisDescent R E F) (E' : IntermediateField E F) :
    M4aHerbrand.IdeleGaloisDescent R E' F where
  act := D.act.comp (restrictScalarsHom E')
  compat g x := D.compat (g.restrictScalars E) x
  continuous_act g := D.continuous_act (g.restrictScalars E)

end M4aHerbrandRestrict

open M4aHerbrandRestrict in
theorem solution
    (R E F : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Field F]
    [Algebra R F] [IsFractionRing R F] [Algebra E F]
    (D : M4aHerbrand.IdeleGaloisDescent R E F) (E' : IntermediateField E F) :
    (∀ (D' : M4aHerbrand.IdeleGaloisDescent R E' F) (g : F ≃ₐ[E'] F),
        D'.act g = D.act (g.restrictScalars E)) ∧
    (∀ (D' : M4aHerbrand.IdeleGaloisDescent R E' F) (g : F ≃ₐ[E'] F)
        (c : M4aHerbrand.IdeleClassGroup R F),
        D'.classAct g c = D.classAct (g.restrictScalars E) c) ∧
    Nonempty (M4aHerbrand.IdeleGaloisDescent R E' F) := by
  haveI : Subsingleton (M4aHerbrand.IdeleGaloisDescent R E' F) :=
    M4aHerbrand.subsingleton_ideleGaloisDescent R E' F
  refine ⟨fun D' g => ?_, fun D' g c => ?_, ⟨restrictDescent D E'⟩⟩
  · obtain rfl : D' = restrictDescent D E' := Subsingleton.elim _ _
    rfl
  · obtain rfl : D' = restrictDescent D E' := Subsingleton.elim _ _
    rfl

end S_M4aHerbrand_ideleGaloisDescent_restrict_intermediateField
end P2MW
export P2MW.S_M4aHerbrand_ideleGaloisDescent_restrict_intermediateField (solution)
