-- Prove2me | solution 1 for ModularCurve.forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp_of_forall_heckeGen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/c8bf56f6-f09b-50d5-bd79-ac8d6b61a26e

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp_of_forall_heckeGen

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve

noncomputable section

namespace HeckeRingClosure

universe u

variable {R : Type u} [CommRing R] {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R g)

def compPt {T X W : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    {e : W ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver s f) (P : SchemeHomOver f e) : SchemeHomOver s e :=
  ⟨x.1 ≫ P.1, by rw [Category.assoc, P.2, x.2]⟩

@[scoped simp] theorem compPt_coe {T X W : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    {e : W ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver s f) (P : SchemeHomOver f e) :
    (compPt x P).1 = x.1 ≫ P.1 := rfl

theorem compPt_assoc {T X W V : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    {e : W ⟶ Spec (CommRingCat.of R)} {d : V ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver s f) (P : SchemeHomOver f e) (Q : SchemeHomOver e d) :
    compPt (compPt x P) Q = compPt x (compPt P Q) :=
  Subtype.ext (Category.assoc _ _ _)

theorem comp_eq_transition {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver s g)
    (P : SchemeHomOver g g) :
    compPt x P = GoodReductionJacobian.schemeHomOverComp x.1 x.2 P :=
  Subtype.ext rfl

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t g) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) =
      L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural t t' ψ hψ, L.inv_mul_cancel, L.one_natural t t' ψ hψ]
  exact eq_inv_of_mul_eq_one_left h

def IsHom (P : SchemeHomOver g g) : Prop :=
  ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s g),
    compPt (L.mul s x y) P =
      L.mul s (compPt x P) (compPt y P)

variable {L}

theorem comp_mulPt {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver s g)
    (P Q : SchemeHomOver g g) :
    compPt x (L.mul g P Q) =
      L.mul s (compPt x P) (compPt x Q) := by
  rw [comp_eq_transition, comp_eq_transition, comp_eq_transition, L.mul_natural g s x.1 x.2]

theorem comp_invPt {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver s g)
    (P : SchemeHomOver g g) :
    compPt x (L.inv g P) = L.inv s (compPt x P) := by
  rw [comp_eq_transition, comp_eq_transition, inv_natural L g s x.1 x.2]

theorem comp_onePt {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver s g) :
    compPt x (L.one g) = L.one s := by
  rw [comp_eq_transition, L.one_natural g s x.1 x.2]

theorem comp_idPoint {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver s g) :
    compPt x (RelativeGroupLaw.idPoint : SchemeHomOver g g) = x :=
  Subtype.ext (Category.comp_id _)

theorem isHom_idPoint : IsHom L (RelativeGroupLaw.idPoint : SchemeHomOver g g) := by
  intro T s x y
  rw [comp_idPoint, comp_idPoint, comp_idPoint]

theorem isHom_one : IsHom L (L.one g) := by
  intro T s x y
  rw [comp_onePt, comp_onePt, comp_onePt, L.one_mul]

theorem isHom_mul (hcomm : L.IsCommutative) {P Q : SchemeHomOver g g} (hP : IsHom L P) (hQ : IsHom L Q) :
    IsHom L (L.mul g P Q) := by
  intro T s x y
  rw [comp_mulPt, comp_mulPt, comp_mulPt, hP, hQ]

  rw [L.mul_assoc, L.mul_assoc, ← L.mul_assoc s (compPt y P),
    hcomm s (compPt y P), L.mul_assoc]

theorem isHom_inv (hcomm : L.IsCommutative) {P : SchemeHomOver g g} (hP : IsHom L P) :
    IsHom L (L.inv g P) := by
  intro T s x y
  letI := L.pointGroup s
  rw [comp_invPt, comp_invPt, comp_invPt, hP]
  show (compPt x P * compPt y P)⁻¹ =
    (compPt x P)⁻¹ * (compPt y P)⁻¹
  rw [mul_inv_rev]
  exact hcomm s _ _

theorem isHom_comp {P Q : SchemeHomOver g g} (hP : IsHom L P) (hQ : IsHom L Q) :
    IsHom L (compPt P Q) := by
  intro T s x y
  rw [← compPt_assoc, hP, hQ, compPt_assoc,
    compPt_assoc]

end HeckeRingClosure
p2m_reactivate "P2MW.S_ModularCurve_forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp_of_forall_heckeGen.HeckeRingClosure"

end
p2m_reactivate "P2MW.S_ModularCurve_forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp_of_forall_heckeGen.HeckeRingClosure"

open HeckeRingClosure in
theorem solution
    (R : Type) [CommRing R] [Algebra R (AlgebraicClosure ℚ)] (N : ℕ) [NeZero N]
    {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R g) (hcomm : L.IsCommutative)
    (pts : JZero N ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) g)
    (pts_add : ∀ x y : JZero N, pts (x + y) = L.mul _ (pts x) (pts y))
    (hgen : letI := heckeModuleBar N
      ∀ ℓ : Nat.Primes, ∃ φ : SchemeHomOver g g,
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s g),
          NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
            L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
        ∀ x : JZero N, (pts (heckeGen ℓ • x)).1 = (pts x).1 ≫ φ.1) :
    letI := heckeModuleBar N
    ∀ t : HeckeAlg, ∃ φ : SchemeHomOver g g,
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s g),
          NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
            L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : JZero N, (pts (t • x)).1 = (pts x).1 ≫ φ.1 := by
  letI := heckeModuleBar N
  letI grp : Group (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (AlgebraicClosure ℚ)))) g) :=
    L.pointGroup _

  have pts_zero : pts 0 = L.one _ := by
    have h : L.mul _ (pts 0) (pts 0) = pts 0 := by rw [← pts_add, add_zero]
    have h2 : pts 0 * pts 0 = pts 0 * 1 := by rw [mul_one]; exact h
    exact mul_left_cancel h2
  have pts_neg : ∀ x : JZero N, pts (-x) = L.inv _ (pts x) := by
    intro x
    have h : L.mul _ (pts x) (pts (-x)) = L.one _ := by rw [← pts_add, add_neg_cancel, pts_zero]
    exact eq_inv_of_mul_eq_one_right h

  have hgen' : ∀ ℓ : Nat.Primes, ∃ ψ : SchemeHomOver g g, IsHom L ψ ∧
      ∀ x : JZero N, pts (heckeGen ℓ • x) = compPt (pts x) ψ := by
    intro ℓ
    obtain ⟨ψ, hψ, hψx⟩ := hgen ℓ
    refine ⟨ψ, fun s x y => ?_, fun x => Subtype.ext (hψx x)⟩
    have := hψ s x y
    exact Subtype.ext (by have h__af := congrArg Subtype.val this; simp only [NeronModelInfra.schemeHomOverComp_coe, compPt_coe] at h__af; exact h__af)

  have key : ∀ t : HeckeAlg, ∃ φ : SchemeHomOver g g, IsHom L φ ∧
      ∀ x : JZero N, pts (t • x) = compPt (pts x) φ := by
    intro t
    induction t using MvPolynomial.induction_on with
    | C a =>
        induction a using Int.induction_on with
        | zero =>
            refine ⟨L.one g, isHom_one, fun x => ?_⟩
            rw [heckeModuleBar_C_smul, zero_zsmul, pts_zero, comp_onePt]
        | succ n ih =>
            obtain ⟨φ, hφ, hφx⟩ := ih
            have hφx' : ∀ x : JZero N, pts ((n : ℤ) • x) = compPt (pts x) φ := fun x => by
              rw [← hφx x, heckeModuleBar_C_smul]
            refine ⟨L.mul g φ RelativeGroupLaw.idPoint, isHom_mul hcomm hφ isHom_idPoint, fun x => ?_⟩
            rw [heckeModuleBar_C_smul, add_zsmul, one_zsmul, pts_add, comp_mulPt, comp_idPoint, hφx']
        | pred n ih =>
            obtain ⟨φ, hφ, hφx⟩ := ih
            have hφx' : ∀ x : JZero N, pts ((-(n : ℤ)) • x) = compPt (pts x) φ := fun x => by
              rw [← hφx x, heckeModuleBar_C_smul]
            refine ⟨L.mul g φ (L.inv g RelativeGroupLaw.idPoint),
              isHom_mul hcomm hφ (isHom_inv hcomm isHom_idPoint), fun x => ?_⟩
            rw [heckeModuleBar_C_smul, sub_zsmul, one_zsmul, pts_add, pts_neg, comp_mulPt,
              comp_invPt, comp_idPoint, hφx']
    | add t t' ht ht' =>
        obtain ⟨φ, hφ, hφx⟩ := ht
        obtain ⟨φ', hφ', hφ'x⟩ := ht'
        refine ⟨L.mul g φ φ', isHom_mul hcomm hφ hφ', fun x => ?_⟩
        rw [add_smul, pts_add, hφx, hφ'x, comp_mulPt]
    | mul_X t ℓ ht =>
        obtain ⟨φ, hφ, hφx⟩ := ht
        obtain ⟨ψ, hψ, hψx⟩ := hgen' ℓ
        refine ⟨compPt ψ φ, isHom_comp hψ hφ, fun x => ?_⟩
        have h1 : pts (MvPolynomial.X ℓ • x) = compPt (pts x) ψ := hψx x
        rw [mul_smul, hφx, h1, compPt_assoc]
  intro t
  obtain ⟨φ, hφ, hφx⟩ := key t
  refine ⟨φ, fun s x y => ?_, fun x => congrArg Subtype.val (hφx x)⟩
  exact Subtype.ext (by have h__af := congrArg Subtype.val (hφ s x y); simp only [NeronModelInfra.schemeHomOverComp_coe, compPt_coe] at h__af; exact h__af)

#print axioms solution

end S_ModularCurve_forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp_of_forall_heckeGen
end P2MW
export P2MW.S_ModularCurve_forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp_of_forall_heckeGen (solution)
