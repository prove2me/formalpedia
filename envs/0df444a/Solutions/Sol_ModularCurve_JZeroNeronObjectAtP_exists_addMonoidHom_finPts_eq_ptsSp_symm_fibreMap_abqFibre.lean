-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.exists_addMonoidHom_finPts_eq_ptsSp_symm_fibreMap_abqFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/c0e8ed49-6fc9-5f18-8881-ac282120d430

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_mem_finPts_iff
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_addMonoidHom_finPts_eq_ptsSp_symm_fibreMap_abqFibre

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

noncomputable section

namespace NUABQ

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p} {Λ : LevelData N₀ p A}

omit [Fact (Nat.Prime p)] [NeZero p] in
theorem ext_unique_aux {X : Scheme.{0}} {f : X ⟶ base p} [IsSeparated f]
    (P Q : SchemeHomOver Λ.σA f) (h : barPt A ≫ P.1 = barPt A ≫ Q.1) : P = Q := by
  haveI : IsSeparated (RelativeGroupLaw.baseChangeStr Λ.σA f) := by
    show IsSeparated (pullback.snd f Λ.σA); infer_instance
  have key : toFibrePt P = toFibrePt Q := by
    refine AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
      (R := ↥A) (AlgebraicClosure ℚ) (AlgebraicClosure ℚ) (gY := 𝟙 (Spec (CommRingCat.of ↥A)))
      (gX := RelativeGroupLaw.baseChangeStr Λ.σA f) (toFibrePt P) (toFibrePt Q) ?_
    intro z
    have hz : z.1 = barPt A := by have h__af := z.2; simp at h__af; exact h__af
    rw [hz]
    show barPt A ≫ pullback.lift P.1 (𝟙 _) _ = barPt A ≫ pullback.lift Q.1 (𝟙 _) _
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using h
    · simp only [Category.assoc, pullback.lift_snd]
  apply Subtype.ext
  have h1 : P.1 = (toFibrePt P).1 ≫ pullback.fst f Λ.σA := by
    show P.1 = pullback.lift P.1 (𝟙 _) _ ≫ pullback.fst f Λ.σA
    rw [pullback.lift_fst]
  have h2 : Q.1 = (toFibrePt Q).1 ≫ pullback.fst f Λ.σA := by
    show Q.1 = pullback.lift Q.1 (𝟙 _) _ ≫ pullback.fst f Λ.σA
    rw [pullback.lift_fst]
  rw [h1, h2, key]

theorem ext_unique (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (P Q : SchemeHomOver Λ.σA O.g) (h : barPt A ≫ P.1 = barPt A ≫ Q.1) : P = Q := by
  haveI : IsSeparated O.g := O.separated
  exact ext_unique_aux P Q h

def extPt (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) {m : ℕ} (x : ↥(O.finPts m)) : SchemeHomOver Λ.σA O.g :=
  (((mem_finPts_iff O m (x : JZero (N₀ * p))).mp x.2).2).choose

theorem extPt_spec (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) {m : ℕ} (x : ↥(O.finPts m)) :
    (O.pts (x : JZero (N₀ * p))).1 = barPt A ≫ (extPt O x).1 :=
  (((mem_finPts_iff O m (x : JZero (N₀ * p))).mp x.2).2).choose_spec

theorem extPt_eq_of (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) {m : ℕ} (x : ↥(O.finPts m))
    (s : SchemeHomOver Λ.σA O.g) (hs : (O.pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1) : s = extPt O x :=
  ext_unique O s (extPt O x) (hs.symm.trans (extPt_spec O x))

theorem coe_mul_castOver {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {ι ι' : T ⟶ Spec (CommRingCat.of R)} (h : ι = ι') (u v : SchemeHomOver ι f) :
    (L.mul ι' (castOver h u) (castOver h v)).1 = (L.mul ι u v).1 := by
  subst h; rfl

theorem barPt_comp_mul (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (P Q : SchemeHomOver Λ.σA O.g) :
    barPt A ≫ (O.L.mul Λ.σA P Q).1 =
      (O.L.mul (barPt A ≫ Λ.σA) (GoodReductionJacobian.schemeHomOverComp (barPt A) rfl P)
        (GoodReductionJacobian.schemeHomOverComp (barPt A) rfl Q)).1 := by
  have h := congrArg Subtype.val (O.L.mul_natural Λ.σA (barPt A ≫ Λ.σA) (barPt A) rfl P Q)
  simpa [GoodReductionJacobian.schemeHomOverComp_coe] using h

theorem extPt_add (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) {m : ℕ} (x y : ↥(O.finPts m)) :
    extPt O (x + y) = O.L.mul Λ.σA (extPt O x) (extPt O y) := by
  symm
  apply extPt_eq_of
  rw [barPt_comp_mul]
  have hadd : O.pts ((x : JZero (N₀ * p)) + (y : JZero (N₀ * p))) = O.L.mul _ (O.pts x) (O.pts y) := O.pts_add x y
  have hx : O.pts (x : JZero (N₀ * p)) = castOver Λ.hσA (GoodReductionJacobian.schemeHomOverComp (barPt A) rfl (extPt O x)) :=
    Subtype.ext (extPt_spec O x)
  have hy : O.pts (y : JZero (N₀ * p)) = castOver Λ.hσA (GoodReductionJacobian.schemeHomOverComp (barPt A) rfl (extPt O y)) :=
    Subtype.ext (extPt_spec O y)
  rw [AddSubgroup.coe_add, hadd, hx, hy]
  exact coe_mul_castOver O.L Λ.hσA _ _

def redPt (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (s : SchemeHomOver Λ.σA O.g) :
    SchemeHomOver (resPt A ≫ Λ.σA) O.g :=
  GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s

theorem redPt_mul (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (P Q : SchemeHomOver Λ.σA O.g) :
    redPt O (O.L.mul Λ.σA P Q) = O.L.mul (resPt A ≫ Λ.σA) (redPt O P) (redPt O Q) :=
  O.L.mul_natural Λ.σA (resPt A ≫ Λ.σA) (resPt A) rfl P Q

theorem mul_castOver {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {ι ι' : T ⟶ Spec (CommRingCat.of R)} (h : ι = ι') (u v : SchemeHomOver ι f) :
    L.mul ι' (castOver h u) (castOver h v) = castOver h (L.mul ι u v) := by
  subst h; rfl

theorem overId_eq_castOver {B T X : Scheme.{0}} {ι : T ⟶ B} {f : X ⟶ B} (x : SchemeHomOver ι f) :
    overId x = castOver (Category.id_comp ι).symm x := Subtype.ext rfl

theorem toFibrePt_mul {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (u v : SchemeHomOver ι f) :
    toFibrePt (L.mul ι u v) = (L.baseChange ι).mul (𝟙 _) (toFibrePt u) (toFibrePt v) := by
  rw [RelativeGroupLaw.baseChange_mul]
  show RelativeGroupLaw.baseChangePointOfBase ι (overId (L.mul ι u v)) = _
  rw [toFibrePt, toFibrePt, RelativeGroupLaw.baseChangePointToBase_ofBase, RelativeGroupLaw.baseChangePointToBase_ofBase,
    overId_eq_castOver, overId_eq_castOver, overId_eq_castOver, mul_castOver]

theorem ofFibrePt_mul {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (a b : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f)) :
    ofFibrePt ((L.baseChange ι).mul (𝟙 _) a b) = L.mul ι (ofFibrePt a) (ofFibrePt b) := by
  apply Subtype.ext
  show (RelativeGroupLaw.baseChangePointToBase ι ((L.baseChange ι).mul (𝟙 _) a b)).1 = _
  rw [RelativeGroupLaw.baseChangePointToBase_mul]
  have ha : RelativeGroupLaw.baseChangePointToBase ι a = castOver (Category.id_comp ι).symm (ofFibrePt a) :=
    Subtype.ext rfl
  have hb : RelativeGroupLaw.baseChangePointToBase ι b = castOver (Category.id_comp ι).symm (ofFibrePt b) :=
    Subtype.ext rfl
  rw [ha, hb, mul_castOver]
  rfl

theorem fibreMap_abqFibre_mul (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (i : Fin 2)
    (u v : SchemeHomOver (resPt A ≫ Λ.σA) O.g) :
    fibreMap (O.abqFibre i) (O.L.mul _ u v) = Λ.L.mul _ (fibreMap (O.abqFibre i) u) (fibreMap (O.abqFibre i) v) := by
  unfold fibreMap
  rw [toFibrePt_mul, O.abqFibre_mul i, ofFibrePt_mul]

def cls (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (i : Fin 2) (s : SchemeHomOver Λ.σA O.g) :
    JZeroC (ResidueField ↥A) N₀ :=
  Λ.ptsSp.symm (fibreMap (O.abqFibre i) (redPt O s))

theorem ptsSp_symm_mul (hΛ : Λ.IsJacobian) (a b : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f) :
    Λ.ptsSp.symm (Λ.L.mul _ a b) = Λ.ptsSp.symm a + Λ.ptsSp.symm b := by
  apply Λ.ptsSp.injective
  rw [Equiv.apply_symm_apply, hΛ.2.2.2.2.1, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem cls_mul (hΛ : Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (i : Fin 2) (P Q : SchemeHomOver Λ.σA O.g) :
    cls O i (O.L.mul Λ.σA P Q) = cls O i P + cls O i Q := by
  unfold cls
  rw [redPt_mul, fibreMap_abqFibre_mul, ptsSp_symm_mul hΛ]

def clsHom (hΛ : Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (i : Fin 2) (m : ℕ) :
    ↥(O.finPts m) →+ JZeroC (ResidueField ↥A) N₀ :=
  AddMonoidHom.mk' (fun x => cls O i (extPt O x)) (fun x y => by
    show cls O i (extPt O (x + y)) = cls O i (extPt O x) + cls O i (extPt O y)
    rw [extPt_add, cls_mul hΛ])

theorem clsHom_apply (hΛ : Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (i : Fin 2) (m : ℕ) (x : ↥(O.finPts m)) :
    clsHom hΛ O i m x = cls O i (extPt O x) := rfl

theorem nsmul_clsHom_eq_zero (hΛ : Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (i : Fin 2) (m : ℕ)
    (x : ↥(O.finPts m)) : m • clsHom hΛ O i m x = 0 := by
  have hx := ((mem_finPts_iff O m (x : JZero (N₀ * p))).mp x.2).1
  have hmx : m • x = 0 := by
    apply Subtype.ext
    show m • (x : JZero (N₀ * p)) = 0
    have h2 : ((m : ℤ)) • (x : JZero (N₀ * p)) = 0 := by simpa using hx
    simpa [natCast_zsmul] using h2
  rw [← map_nsmul, hmx, map_zero]

theorem cls_eq (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (i : Fin 2) (s : SchemeHomOver Λ.σA O.g) :
    cls O i s = Λ.ptsSp.symm (fibreMap (O.abqFibre i) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) := rfl

end NUABQ

open NUABQ in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (i : Fin 2) (m : ℕ) :
    ∃ ν : ↥(O.finPts m) →+ JZeroC (ResidueField ↥A) N₀,
      (∀ (x : ↥(O.finPts m)) (s : SchemeHomOver Λ.σA O.g),
        (O.pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1 →
          ν x = Λ.ptsSp.symm (fibreMap (O.abqFibre i)
            (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s))) ∧
      (∀ x : ↥(O.finPts m), m • ν x = 0) := by
  refine ⟨clsHom hΛ O i m, ?_, nsmul_clsHom_eq_zero hΛ O i m⟩
  intro x s hs
  rw [clsHom_apply, ← extPt_eq_of O x s hs, cls_eq]

end

end S_ModularCurve_JZeroNeronObjectAtP_exists_addMonoidHom_finPts_eq_ptsSp_symm_fibreMap_abqFibre
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_addMonoidHom_finPts_eq_ptsSp_symm_fibreMap_abqFibre (solution)
