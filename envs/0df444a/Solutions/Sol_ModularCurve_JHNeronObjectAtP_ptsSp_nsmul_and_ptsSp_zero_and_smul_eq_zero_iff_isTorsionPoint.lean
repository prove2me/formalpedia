-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.ptsSp_nsmul_and_ptsSp_zero_and_smul_eq_zero_iff_isTorsionPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/27d4347d-863e-5c93-bad8-19422631d142

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_nsmul_and_ptsSp_zero_and_smul_eq_zero_iff_isTorsionPoint

set_option autoImplicit false
set_option maxHeartbeats 3200000

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing
open ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

namespace N6Aux

theorem ofFibrePt_baseChange_mul {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (a b : SchemeHomOver ι f) :
    ofFibrePt ((L.baseChange ι).mul (𝟙 _) (toFibrePt a) (toFibrePt b)) = L.mul ι a b := by
  apply Subtype.ext

  show (RelativeGroupLaw.baseChangePointToBase ι ((L.baseChange ι).mul (𝟙 _) (toFibrePt a) (toFibrePt b))).1 = _
  rw [RelativeGroupLaw.baseChangePointToBase_mul]
  show (L.mul _ (RelativeGroupLaw.baseChangePointToBase ι (toFibrePt a)) (RelativeGroupLaw.baseChangePointToBase ι (toFibrePt b))).1 = _
  have ha : RelativeGroupLaw.baseChangePointToBase ι (toFibrePt a) = schemeHomOverComp (𝟙 _) rfl a := by
    rw [toFibrePt, RelativeGroupLaw.baseChangePointToBase_ofBase]
    exact Subtype.ext (Category.id_comp _).symm
  have hb : RelativeGroupLaw.baseChangePointToBase ι (toFibrePt b) = schemeHomOverComp (𝟙 _) rfl b := by
    rw [toFibrePt, RelativeGroupLaw.baseChangePointToBase_ofBase]
    exact Subtype.ext (Category.id_comp _).symm
  rw [ha, hb, ← L.mul_natural ι (𝟙 _ ≫ ι) (𝟙 _) rfl a b, GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp]

theorem eq_one_of_mul_self {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t f)
    (h : L.mul t a a = a) : a = L.one t := by
  have h1 : L.mul t (L.inv t a) (L.mul t a a) = L.mul t (L.inv t a) a := by rw [h]
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at h1
  exact h1

end N6Aux

open N6Aux

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ) :
    (∀ (k : ℕ) (z : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset),
      O.ptsSp (k • z) = O.L.nsmul (resPt A ≫ Λ.σA) k (O.ptsSp z)) ∧
    O.ptsSp 0 = O.L.one (resPt A ≫ Λ.σA) ∧
    (∀ (k : ℕ) (z : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset),
      k • z = 0 ↔ O.L.IsTorsionPoint (resPt A ≫ Λ.σA) k (O.ptsSp z)) := by

  have hadd : ∀ x y, O.ptsSp (x + y) = O.L.mul (resPt A ≫ Λ.σA) (O.ptsSp x) (O.ptsSp y) := by
    intro x y
    rw [O.ptsSp_add, ofFibrePt_baseChange_mul]

  have hzero : O.ptsSp 0 = O.L.one (resPt A ≫ Λ.σA) := by
    have h := hadd 0 0
    have h0 : (0 : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) + 0 = 0 := by abel
    rw [h0] at h
    exact eq_one_of_mul_self _ _ _ h.symm

  have hnsmul : ∀ (k : ℕ) (z : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset),
      O.ptsSp (k • z) = O.L.nsmul (resPt A ≫ Λ.σA) k (O.ptsSp z) := by
    intro k z
    induction k with
    | zero => rw [zero_nsmul, RelativeGroupLaw.nsmul_zero, hzero]
    | succ k ih => rw [succ_nsmul, hadd, ih, RelativeGroupLaw.nsmul_succ]
  refine ⟨hnsmul, hzero, fun k z => ?_⟩
  rw [RelativeGroupLaw.isTorsionPoint_def, ← hnsmul, ← hzero]
  exact O.ptsSp.injective.eq_iff.symm

end S_ModularCurve_JHNeronObjectAtP_ptsSp_nsmul_and_ptsSp_zero_and_smul_eq_zero_iff_isTorsionPoint
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_nsmul_and_ptsSp_zero_and_smul_eq_zero_iff_isTorsionPoint (solution)
