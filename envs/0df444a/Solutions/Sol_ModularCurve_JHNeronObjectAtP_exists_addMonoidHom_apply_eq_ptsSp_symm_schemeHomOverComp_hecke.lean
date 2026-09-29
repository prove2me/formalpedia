-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_addMonoidHom_apply_eq_ptsSp_symm_schemeHomOverComp_hecke
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/a50abde6-12bf-561c-9528-65dbc170dbfa

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addMonoidHom_apply_eq_ptsSp_symm_schemeHomOverComp_hecke

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

open ModularCurve.JHNeronObjectAtP

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (S : Set ℕ) (t : CohCarrier.Gen M S) :
    ∃ Φ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset →+
        GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
      ∀ ξ, Φ ξ = O.ptsSp.symm (NeronModelInfra.schemeHomOverComp (O.ptsSp ξ) (O.hecke S t)) := by

  have key : ∀ X Y : SchemeHomOver (resPt A ≫ Λ.σA) O.g,
      NeronModelInfra.schemeHomOverComp
          (ofFibrePt ((O.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt X) (toFibrePt Y))) (O.hecke S t) =
        ofFibrePt ((O.L.baseChange (resPt A ≫ Λ.σA)).mul _
          (toFibrePt (NeronModelInfra.schemeHomOverComp X (O.hecke S t)))
          (toFibrePt (NeronModelInfra.schemeHomOverComp Y (O.hecke S t)))) := by
    intro X Y
    apply Subtype.ext
    simp only [NeronModelInfra.schemeHomOverComp_coe, toFibrePt, ofFibrePt, RelativeGroupLaw.baseChange_mul,
      RelativeGroupLaw.baseChangePointToBase_ofBase]
    have h := congrArg Subtype.val (O.hecke_mul S t (𝟙 _ ≫ resPt A ≫ Λ.σA) (overId X) (overId Y))
    rw [NeronModelInfra.schemeHomOverComp_coe] at h
    rw [h]
    rfl
  refine ⟨AddMonoidHom.mk' (fun ξ => O.ptsSp.symm (NeronModelInfra.schemeHomOverComp (O.ptsSp ξ) (O.hecke S t))) ?_,
    fun ξ => rfl⟩
  intro ξ η
  apply O.ptsSp.injective
  rw [Equiv.apply_symm_apply, O.ptsSp_add, O.ptsSp_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply, key]

#print axioms solution

end S_ModularCurve_JHNeronObjectAtP_exists_addMonoidHom_apply_eq_ptsSp_symm_schemeHomOverComp_hecke
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addMonoidHom_apply_eq_ptsSp_symm_schemeHomOverComp_hecke (solution)
