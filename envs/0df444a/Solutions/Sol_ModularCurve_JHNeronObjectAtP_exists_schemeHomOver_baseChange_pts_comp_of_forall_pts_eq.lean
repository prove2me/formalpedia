-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_baseChange_pts_comp_of_forall_pts_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/381a9ffa-1ec5-590c-87e4-08332517050e

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_schemeHomOver_baseChange_pts_comp_of_forall_pts_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)

    (w w₁ w₂ w₃ : JH M H → JH M H) (hw : ∀ x : JH M H, w x = w₁ (w₂ (w₃ x)))

    (W₁ W₂ W₃ : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.σA O.g) (RelativeGroupLaw.baseChangeStr Λ.σA O.g))
    (hWmul₁ : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥A))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.σA O.g)),
      NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.σA).mul s x y) W₁ =
        (O.L.baseChange Λ.σA).mul s (NeronModelInfra.schemeHomOverComp x W₁) (NeronModelInfra.schemeHomOverComp y W₁))
    (hWpts₁ : ∀ x : JH M H, O.pts (w₁ x) =
      genOfBaseChangePt Λ.hσA (NeronModelInfra.schemeHomOverComp
        (RelativeGroupLaw.baseChangePointOfBase Λ.σA (castOver Λ.hσA.symm (O.pts x))) W₁))
    (hWmul₂ : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥A))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.σA O.g)),
      NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.σA).mul s x y) W₂ =
        (O.L.baseChange Λ.σA).mul s (NeronModelInfra.schemeHomOverComp x W₂) (NeronModelInfra.schemeHomOverComp y W₂))
    (hWpts₂ : ∀ x : JH M H, O.pts (w₂ x) =
      genOfBaseChangePt Λ.hσA (NeronModelInfra.schemeHomOverComp
        (RelativeGroupLaw.baseChangePointOfBase Λ.σA (castOver Λ.hσA.symm (O.pts x))) W₂))
    (hWmul₃ : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥A))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.σA O.g)),
      NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.σA).mul s x y) W₃ =
        (O.L.baseChange Λ.σA).mul s (NeronModelInfra.schemeHomOverComp x W₃) (NeronModelInfra.schemeHomOverComp y W₃))
    (hWpts₃ : ∀ x : JH M H, O.pts (w₃ x) =
      genOfBaseChangePt Λ.hσA (NeronModelInfra.schemeHomOverComp
        (RelativeGroupLaw.baseChangePointOfBase Λ.σA (castOver Λ.hσA.symm (O.pts x))) W₃)) :
    ∃ W : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.σA O.g) (RelativeGroupLaw.baseChangeStr Λ.σA O.g),
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥A))
          (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.σA O.g)),
        NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.σA).mul s x y) W =
          (O.L.baseChange Λ.σA).mul s (NeronModelInfra.schemeHomOverComp x W) (NeronModelInfra.schemeHomOverComp y W)) ∧
      (∀ x : JH M H, O.pts (w x) =
        genOfBaseChangePt Λ.hσA (NeronModelInfra.schemeHomOverComp
          (RelativeGroupLaw.baseChangePointOfBase Λ.σA (castOver Λ.hσA.symm (O.pts x))) W)) := by

  refine ⟨NeronModelInfra.schemeHomOverComp W₃ (NeronModelInfra.schemeHomOverComp W₂ W₁), ?_, ?_⟩
  · intro T s x y
    have hassoc : ∀ z : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.σA O.g),
        NeronModelInfra.schemeHomOverComp z (NeronModelInfra.schemeHomOverComp W₃ (NeronModelInfra.schemeHomOverComp W₂ W₁)) =
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp z W₃) W₂) W₁ :=
      fun z => Subtype.ext (by simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc])
    rw [hassoc, hWmul₃, hWmul₂, hWmul₁, ← hassoc, ← hassoc]
  · intro x

    have hlg : ∀ q : SchemeHomOver (barPt A) (RelativeGroupLaw.baseChangeStr Λ.σA O.g),
        RelativeGroupLaw.baseChangePointOfBase Λ.σA (castOver Λ.hσA.symm (genOfBaseChangePt Λ.hσA q)) = q := by
      intro q
      have hc : castOver Λ.hσA.symm (genOfBaseChangePt Λ.hσA q) = RelativeGroupLaw.baseChangePointToBase Λ.σA q :=
        Subtype.ext rfl
      rw [hc, RelativeGroupLaw.baseChangePointOfBase_toBase]
    have hassoc' : ∀ z : SchemeHomOver (barPt A) (RelativeGroupLaw.baseChangeStr Λ.σA O.g),
        NeronModelInfra.schemeHomOverComp z (NeronModelInfra.schemeHomOverComp W₃ (NeronModelInfra.schemeHomOverComp W₂ W₁)) =
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp z W₃) W₂) W₁ :=
      fun z => Subtype.ext (by simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc])
    rw [hw, hWpts₁, hWpts₂, hlg, hWpts₃, hlg, hassoc']

end S_ModularCurve_JHNeronObjectAtP_exists_schemeHomOver_baseChange_pts_comp_of_forall_pts_eq
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_schemeHomOver_baseChange_pts_comp_of_forall_pts_eq (solution)
