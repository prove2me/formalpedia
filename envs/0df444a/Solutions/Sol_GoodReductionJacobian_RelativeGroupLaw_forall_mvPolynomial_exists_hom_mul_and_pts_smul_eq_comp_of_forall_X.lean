-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.forall_mvPolynomial_exists_hom_mul_and_pts_smul_eq_comp_of_forall_X
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6d9a0e46-dda8-59cb-9371-c6c0f8b8d1f3

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_forall_mvPolynomial_exists_hom_mul_and_pts_smul_eq_comp_of_forall_X

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

noncomputable section

namespace AlgClosureGeneric

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

def idPt : SchemeHomOver g g := ⟨𝟙 G, Category.id_comp _⟩

@[scoped simp] theorem idPt_coe : (idPt : SchemeHomOver g g).1 = 𝟙 G := rfl

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
    compPt (L.mul s x y) P = L.mul s (compPt x P) (compPt y P)

variable {L}

theorem comp_mulPt {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver s g)
    (P Q : SchemeHomOver g g) :
    compPt x (L.mul g P Q) = L.mul s (compPt x P) (compPt x Q) := by
  rw [comp_eq_transition, comp_eq_transition, comp_eq_transition, L.mul_natural g s x.1 x.2]

theorem comp_invPt {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver s g)
    (P : SchemeHomOver g g) :
    compPt x (L.inv g P) = L.inv s (compPt x P) := by
  rw [comp_eq_transition, comp_eq_transition, inv_natural L g s x.1 x.2]

theorem comp_onePt {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver s g) :
    compPt x (L.one g) = L.one s := by
  rw [comp_eq_transition, L.one_natural g s x.1 x.2]

theorem comp_idPt {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver s g) :
    compPt x (idPt : SchemeHomOver g g) = x :=
  Subtype.ext (Category.comp_id _)

theorem isHom_idPt : IsHom L (idPt : SchemeHomOver g g) := by
  intro T s x y
  rw [comp_idPt, comp_idPt, comp_idPt]

theorem isHom_one : IsHom L (L.one g) := by
  intro T s x y
  rw [comp_onePt, comp_onePt, comp_onePt, L.one_mul]

theorem isHom_mul (hcomm : L.IsCommutative) {P Q : SchemeHomOver g g} (hP : IsHom L P) (hQ : IsHom L Q) :
    IsHom L (L.mul g P Q) := by
  intro T s x y
  rw [comp_mulPt, comp_mulPt, comp_mulPt, hP, hQ]
  rw [L.mul_assoc, L.mul_assoc, ← L.mul_assoc s (compPt y P), hcomm s (compPt y P), L.mul_assoc]

theorem isHom_inv (hcomm : L.IsCommutative) {P : SchemeHomOver g g} (hP : IsHom L P) :
    IsHom L (L.inv g P) := by
  intro T s x y
  letI := L.pointGroup s
  rw [comp_invPt, comp_invPt, comp_invPt, hP]
  show (compPt x P * compPt y P)⁻¹ = (compPt x P)⁻¹ * (compPt y P)⁻¹
  rw [mul_inv_rev]
  exact hcomm s _ _

theorem isHom_comp {P Q : SchemeHomOver g g} (hP : IsHom L P) (hQ : IsHom L Q) :
    IsHom L (compPt P Q) := by
  intro T s x y
  rw [← compPt_assoc, hP, hQ, compPt_assoc, compPt_assoc]

end AlgClosureGeneric
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_forall_mvPolynomial_exists_hom_mul_and_pts_smul_eq_comp_of_forall_X.AlgClosureGeneric"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_forall_mvPolynomial_exists_hom_mul_and_pts_smul_eq_comp_of_forall_X.AlgClosureGeneric"

universe u v w

open AlgClosureGeneric in

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (hG : G.IsCommutative)
    {σ : Type v} {J : Type w} [AddCommGroup J] [Module (MvPolynomial σ ℤ) J]
    {T₀ : Scheme.{u}} {s₀ : T₀ ⟶ Spec (CommRingCat.of R)} (pts : J → SchemeHomOver s₀ f)
    (hpts : ∀ x y : J, pts (x + y) = G.mul s₀ (pts x) (pts y))
    (hX : ∀ i : σ, ∃ φ : SchemeHomOver f f,
      (∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
        NeronModelInfra.schemeHomOverComp (G.mul s x y) φ =
          G.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : J, (pts ((MvPolynomial.X i : MvPolynomial σ ℤ) • x)).1 = (pts x).1 ≫ φ.1) :
    ∀ t : MvPolynomial σ ℤ, ∃ φ : SchemeHomOver f f,
      (∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
        NeronModelInfra.schemeHomOverComp (G.mul s x y) φ =
          G.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : J, (pts (t • x)).1 = (pts x).1 ≫ φ.1 := by
  letI grp : Group (SchemeHomOver s₀ f) := G.pointGroup s₀

  have C_smul : ∀ (a : ℤ) (x : J), (MvPolynomial.C a : MvPolynomial σ ℤ) • x = a • x := fun a x => by
    rw [eq_intCast, Int.cast_smul_eq_zsmul]

  have pts_zero : pts 0 = G.one _ := by
    have h : G.mul _ (pts 0) (pts 0) = pts 0 := by rw [← hpts, add_zero]
    have h2 : pts 0 * pts 0 = pts 0 * 1 := by rw [mul_one]; exact h
    exact mul_left_cancel h2
  have pts_neg : ∀ x : J, pts (-x) = G.inv _ (pts x) := by
    intro x
    have h : G.mul _ (pts x) (pts (-x)) = G.one _ := by rw [← hpts, add_neg_cancel, pts_zero]
    exact eq_inv_of_mul_eq_one_right h

  have hgen' : ∀ i : σ, ∃ ψ : SchemeHomOver f f, IsHom G ψ ∧
      ∀ x : J, pts ((MvPolynomial.X i : MvPolynomial σ ℤ) • x) = compPt (pts x) ψ := by
    intro i
    obtain ⟨ψ, hψ, hψx⟩ := hX i
    refine ⟨ψ, fun s x y => ?_, fun x => Subtype.ext (hψx x)⟩
    have := hψ s x y
    exact Subtype.ext (by have h__af := congrArg Subtype.val this; simp only [NeronModelInfra.schemeHomOverComp_coe, compPt_coe] at h__af; exact h__af)

  have key : ∀ t : MvPolynomial σ ℤ, ∃ φ : SchemeHomOver f f, IsHom G φ ∧
      ∀ x : J, pts (t • x) = compPt (pts x) φ := by
    intro t
    induction t using MvPolynomial.induction_on with
    | C a =>
        induction a using Int.induction_on with
        | zero =>
            refine ⟨G.one f, isHom_one, fun x => ?_⟩
            rw [C_smul, zero_zsmul, pts_zero, comp_onePt]
        | succ n ih =>
            obtain ⟨φ, hφ, hφx⟩ := ih
            have hφx' : ∀ x : J, pts ((n : ℤ) • x) = compPt (pts x) φ := fun x => by
              rw [← hφx x, C_smul]
            refine ⟨G.mul f φ idPt, isHom_mul hG hφ isHom_idPt, fun x => ?_⟩
            rw [C_smul, add_zsmul, one_zsmul, hpts, comp_mulPt, comp_idPt, hφx']
        | pred n ih =>
            obtain ⟨φ, hφ, hφx⟩ := ih
            have hφx' : ∀ x : J, pts ((-(n : ℤ)) • x) = compPt (pts x) φ := fun x => by
              rw [← hφx x, C_smul]
            refine ⟨G.mul f φ (G.inv f idPt), isHom_mul hG hφ (isHom_inv hG isHom_idPt), fun x => ?_⟩
            rw [C_smul, sub_zsmul, one_zsmul, hpts, pts_neg, comp_mulPt, comp_invPt, comp_idPt, hφx']
    | add t t' ht ht' =>
        obtain ⟨φ, hφ, hφx⟩ := ht
        obtain ⟨φ', hφ', hφ'x⟩ := ht'
        refine ⟨G.mul f φ φ', isHom_mul hG hφ hφ', fun x => ?_⟩
        rw [add_smul, hpts, hφx, hφ'x, comp_mulPt]
    | mul_X t i ht =>
        obtain ⟨φ, hφ, hφx⟩ := ht
        obtain ⟨ψ, hψ, hψx⟩ := hgen' i
        refine ⟨compPt ψ φ, isHom_comp hψ hφ, fun x => ?_⟩
        rw [mul_smul, hφx, hψx x, compPt_assoc]
  intro t
  obtain ⟨φ, hφ, hφx⟩ := key t
  refine ⟨φ, fun s x y => ?_, fun x => congrArg Subtype.val (hφx x)⟩
  exact Subtype.ext (by have h__af := congrArg Subtype.val (hφ s x y); simp only [NeronModelInfra.schemeHomOverComp_coe, compPt_coe] at h__af; exact h__af)

end S_GoodReductionJacobian_RelativeGroupLaw_forall_mvPolynomial_exists_hom_mul_and_pts_smul_eq_comp_of_forall_X
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_forall_mvPolynomial_exists_hom_mul_and_pts_smul_eq_comp_of_forall_X (solution)
