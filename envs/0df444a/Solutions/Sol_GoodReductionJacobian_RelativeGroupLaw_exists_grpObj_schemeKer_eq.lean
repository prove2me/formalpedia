-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_grpObj_schemeKer_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/716ccdd7-3118-5e86-81b6-9efc0178fb82

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_schemeKer_eq

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.CartesianMonoidalCategory NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_schemeKer_eq.GoodReductionJacobian"

open scoped CategoryTheory.MonObj

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nsmul nsmul_succ nsmul_unit nsmul_natural IsTorsionPoint torsionSubset isTorsionPoint_unit idPoint schemeNsmul schemeNsmul_over schemeKer schemeKerStr IsCommutative mul_inv_cancel one_natural mul_assoc mul_one one mul_natural mk inv one_mul inv_mul_cancel mul grpObjOverMk overHomToSchemeHomOver_mul isCommMonObj_grpObjOverMk_iff_mul_comm"
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}

section ptsEquiv
variable (L : RelativeGroupLaw R f) (n : ℕ)

private abbrev _root_.GoodReductionJacobian.RelativeGroupLaw.schemeKerIncl : L.schemeKer n ⟶ J := pullback.fst _ _

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "schemeKerIncl"
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.schemeKerIncl_over : L.schemeKerIncl n ≫ f = L.schemeKerStr n := by
  have h1 : L.schemeKerIncl n ≫ L.schemeNsmul n =
      L.schemeKerStr n ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := pullback.condition
  have h2 : (L.schemeKerIncl n ≫ L.schemeNsmul n) ≫ f = L.schemeKerIncl n ≫ f := by
    rw [Category.assoc, L.schemeNsmul_over]
  rw [h1, Category.assoc, (L.one (𝟙 _)).2, Category.comp_id] at h2
  exact h2.symm

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "schemeKerIncl_over"
variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.nsmul_coe_eq (x : SchemeHomOver t f) :
    (L.nsmul t n x).1 = x.1 ≫ L.schemeNsmul n := by
  have hid : schemeHomOverComp x.1 x.2 (idPoint : SchemeHomOver f f) = x := by
    apply Subtype.ext; simp [schemeHomOverComp]
  have h := L.nsmul_natural f t x.1 x.2 n idPoint
  rw [hid] at h; rw [← h]; rfl

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nsmul_coe_eq"
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.one_coe_eq : (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h := L.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t)
  rw [← h]; rfl

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "one_coe_eq"
private def _root_.GoodReductionJacobian.RelativeGroupLaw.ptsToSchemeHomOver (a : SchemeHomOver t (L.schemeKerStr n)) : SchemeHomOver t f :=
  ⟨a.1 ≫ L.schemeKerIncl n, by rw [Category.assoc, L.schemeKerIncl_over, a.2]⟩

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "ptsToSchemeHomOver"
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.ptsToSchemeHomOver_mem_torsionSubset (a : SchemeHomOver t (L.schemeKerStr n)) :
    L.ptsToSchemeHomOver n t a ∈ L.torsionSubset t n := by
  show L.nsmul t n (L.ptsToSchemeHomOver n t a) = L.one t
  apply Subtype.ext
  rw [L.nsmul_coe_eq, L.one_coe_eq]
  show (a.1 ≫ L.schemeKerIncl n) ≫ L.schemeNsmul n =
    t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1
  rw [Category.assoc, pullback.condition, ← Category.assoc, a.2]

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "ptsToSchemeHomOver_mem_torsionSubset"
private def _root_.GoodReductionJacobian.RelativeGroupLaw.ptsFwd (a : SchemeHomOver t (L.schemeKerStr n)) : ↥(L.torsionSubset t n) :=
  ⟨L.ptsToSchemeHomOver n t a, L.ptsToSchemeHomOver_mem_torsionSubset n t a⟩

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "ptsFwd"
private def _root_.GoodReductionJacobian.RelativeGroupLaw.ptsBwd (x : ↥(L.torsionSubset t n)) : SchemeHomOver t (L.schemeKerStr n) := by
  refine ⟨pullback.lift x.1.1 t ?_, ?_⟩
  · rw [← L.nsmul_coe_eq, ← L.one_coe_eq]; exact congrArg Subtype.val x.2
  · exact pullback.lift_snd _ _ _

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "ptsBwd"
theorem ptsBwd_coe (x : ↥(L.torsionSubset t n)) :
    (L.ptsBwd n t x).1 = pullback.lift x.1.1 t
      (by rw [← L.nsmul_coe_eq, ← L.one_coe_eq]; exact congrArg Subtype.val x.2) := rfl

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.ptsFwd_ptsBwd (x : ↥(L.torsionSubset t n)) : L.ptsFwd n t (L.ptsBwd n t x) = x := by
  apply Subtype.ext; apply Subtype.ext
  show ((L.ptsBwd n t x).1 ≫ L.schemeKerIncl n) = x.1.1
  rw [ptsBwd_coe]; exact pullback.lift_fst _ _ _

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "ptsFwd_ptsBwd"
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.ptsBwd_ptsFwd (a : SchemeHomOver t (L.schemeKerStr n)) :
    L.ptsBwd n t (L.ptsFwd n t a) = a := by
  apply Subtype.ext; rw [ptsBwd_coe]
  apply pullback.hom_ext
  · rw [pullback.lift_fst]; rfl
  · rw [pullback.lift_snd]; exact a.2.symm

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "ptsBwd_ptsFwd"
private def _root_.GoodReductionJacobian.RelativeGroupLaw.ptsEquiv : SchemeHomOver t (L.schemeKerStr n) ≃ ↥(L.torsionSubset t n) where
  toFun := L.ptsFwd n t
  invFun := L.ptsBwd n t
  left_inv := L.ptsBwd_ptsFwd n t
  right_inv := L.ptsFwd_ptsBwd n t

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "ptsEquiv"
@[scoped simp] theorem ptsEquiv_apply_coe_coe (a : SchemeHomOver t (L.schemeKerStr n)) :
    ((L.ptsEquiv n t a : SchemeHomOver t f) : T ⟶ J) = a.1 ≫ L.schemeKerIncl n := rfl

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.ptsEquiv_natural {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (a : SchemeHomOver t (L.schemeKerStr n)) :
    (L.ptsEquiv n t' (schemeHomOverComp ψ hψ a) : SchemeHomOver t' f) =
      schemeHomOverComp ψ hψ (L.ptsEquiv n t a : SchemeHomOver t f) := by
  apply Subtype.ext
  show (ψ ≫ a.1) ≫ L.schemeKerIncl n = ψ ≫ (a.1 ≫ L.schemeKerIncl n)
  rw [Category.assoc]

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "ptsEquiv_natural"
end ptsEquiv

section Lker
variable (L : RelativeGroupLaw R f)
  (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
    L.mul t x y = L.mul t y x)
  (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

include hcomm in
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.nsmul_mul_of_comm (x y : SchemeHomOver t f) (m : ℕ) :
    L.nsmul t m (L.mul t x y) = L.mul t (L.nsmul t m x) (L.nsmul t m y) := by
  induction m with
  | zero => simp [L.one_mul]
  | succ m ih =>
      rw [nsmul_succ, ih, nsmul_succ, nsmul_succ]
      rw [L.mul_assoc, ← L.mul_assoc _ (L.nsmul t m y) x y, hcomm _ (L.nsmul t m y) x,
        L.mul_assoc _ x (L.nsmul t m y) y, ← L.mul_assoc]

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nsmul_mul_of_comm"
include hcomm in
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.isTorsionPoint_mul {x y : SchemeHomOver t f}
    (hx : L.IsTorsionPoint t n x) (hy : L.IsTorsionPoint t n y) :
    L.IsTorsionPoint t n (L.mul t x y) := by
  show L.nsmul t n (L.mul t x y) = L.one t
  rw [L.nsmul_mul_of_comm hcomm t x y n, hx, hy, L.one_mul]

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "isTorsionPoint_mul"
include hcomm in
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.isTorsionPoint_inv {x : SchemeHomOver t f} (hx : L.IsTorsionPoint t n x) :
    L.IsTorsionPoint t n (L.inv t x) := by
  show L.nsmul t n (L.inv t x) = L.one t
  have h : L.mul t (L.nsmul t n x) (L.nsmul t n (L.inv t x)) = L.one t := by
    rw [← L.nsmul_mul_of_comm hcomm, L.mul_inv_cancel, L.nsmul_unit]
  rw [hx, L.one_mul] at h
  exact h

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "isTorsionPoint_inv"
include hcomm in

private def _root_.GoodReductionJacobian.RelativeGroupLaw.kerRGL : RelativeGroupLaw R (L.schemeKerStr n) where
  mul t x y := (L.ptsEquiv n t).symm
    ⟨L.mul t (L.ptsEquiv n t x).1 (L.ptsEquiv n t y).1,
     L.isTorsionPoint_mul hcomm n t (L.ptsEquiv n t x).2 (L.ptsEquiv n t y).2⟩
  one t := (L.ptsEquiv n t).symm ⟨L.one t, L.isTorsionPoint_unit t n⟩
  inv t x := (L.ptsEquiv n t).symm
    ⟨L.inv t (L.ptsEquiv n t x).1, L.isTorsionPoint_inv hcomm n t (L.ptsEquiv n t x).2⟩
  mul_assoc t x y z := (L.ptsEquiv n t).injective (by
    simp only [Equiv.apply_symm_apply]
    exact Subtype.ext (L.mul_assoc t _ _ _))
  one_mul t x := (L.ptsEquiv n t).injective (by
    simp only [Equiv.apply_symm_apply]
    exact Subtype.ext (L.one_mul t _))
  mul_one t x := (L.ptsEquiv n t).injective (by
    simp only [Equiv.apply_symm_apply]
    exact Subtype.ext (L.mul_one t _))
  inv_mul_cancel t x := (L.ptsEquiv n t).injective (by
    simp only [Equiv.apply_symm_apply]
    exact Subtype.ext (L.inv_mul_cancel t _))
  mul_natural t t' ψ hψ x y := (L.ptsEquiv n t').injective (by
    apply Subtype.ext
    rw [Subtype.val, Equiv.apply_symm_apply]
    show (L.ptsEquiv n t' (schemeHomOverComp ψ hψ ((L.ptsEquiv n t).symm _))).1 =
      L.mul t' (L.ptsEquiv n t' (schemeHomOverComp ψ hψ x)).1
        (L.ptsEquiv n t' (schemeHomOverComp ψ hψ y)).1
    rw [L.ptsEquiv_natural n t t' ψ hψ, Equiv.apply_symm_apply,
      L.ptsEquiv_natural n t t' ψ hψ x, L.ptsEquiv_natural n t t' ψ hψ y]
    exact L.mul_natural t t' ψ hψ _ _)

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "kerRGL"
include hcomm in
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.kerRGL_isCommutative : (L.kerRGL hcomm n).IsCommutative := fun t x y => by
  show (L.ptsEquiv n t).symm _ = (L.ptsEquiv n t).symm _
  exact congrArg _ (Subtype.ext (hcomm t _ _))

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "kerRGL_isCommutative"
include hcomm in
@[scoped simp] private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.ptsEquiv_kerRGL_mul_coe (x y : SchemeHomOver t (L.schemeKerStr n)) :
    ((L.ptsEquiv n t ((L.kerRGL hcomm n).mul t x y)) : SchemeHomOver t f) =
      L.mul t (L.ptsEquiv n t x).1 (L.ptsEquiv n t y).1 := by
  show ((L.ptsEquiv n t) ((L.ptsEquiv n t).symm _)).1 = _
  rw [Equiv.apply_symm_apply]

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "ptsEquiv_kerRGL_mul_coe"
end Lker

end GoodReductionJacobian.RelativeGroupLaw
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_schemeKer_eq.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_schemeKer_eq.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_schemeKer_eq.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_schemeKer_eq.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_schemeKer_eq.GoodReductionJacobian.RelativeGroupLaw"

open _root_.GoodReductionJacobian.RelativeGroupLaw _root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_schemeKer_eq.GoodReductionJacobian.RelativeGroupLaw in
set_option maxHeartbeats 6400000 in
theorem solution
    {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) :
    ∃ (_ : GrpObj (Over.mk (L.schemeKerStr n))) (_ : IsCommMonObj (Over.mk (L.schemeKerStr n))),
      ∃ pts : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
          (Over.mk t ⟶ Over.mk (L.schemeKerStr n)) ≃ L.torsionSubset t n,
        (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
            (a b : Over.mk t ⟶ Over.mk (L.schemeKerStr n)),
          (↑(pts t (a * b)) : SchemeHomOver t f) =
            L.mul t (↑(pts t a)) (↑(pts t b))) ∧
        (∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
            (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
            (a : Over.mk t ⟶ Over.mk (L.schemeKerStr n)),
          (↑(pts t' (Over.homMk (U := Over.mk t') (V := Over.mk t) ψ hψ ≫ a)) : SchemeHomOver t' f) =
            schemeHomOverComp ψ hψ (↑(pts t a))) := by
  letI gK : GrpObj (Over.mk (L.schemeKerStr n)) := (L.kerRGL hcomm n).grpObjOverMk

  haveI gKcomm : IsCommMonObj (Over.mk (L.schemeKerStr n)) :=
    (L.kerRGL hcomm n).isCommMonObj_grpObjOverMk_iff_mul_comm.mpr
      (fun t x y => L.kerRGL_isCommutative hcomm n t x y)
  refine ⟨gK, gKcomm,
    fun {T} t => (schemeHomOverEquivOverHom t (L.schemeKerStr n)).symm.trans (L.ptsEquiv n t),
    ?_, ?_⟩
  ·
    intro T t a b
    show (L.ptsEquiv n t (overHomToSchemeHomOver (a * b))).1 =
      L.mul t (L.ptsEquiv n t (overHomToSchemeHomOver a)).1
        (L.ptsEquiv n t (overHomToSchemeHomOver b)).1
    rw [(L.kerRGL hcomm n).overHomToSchemeHomOver_mul t a b]
    exact L.ptsEquiv_kerRGL_mul_coe hcomm n t _ _
  ·
    intro T T' t t' ψ hψ a
    show (L.ptsEquiv n t' (overHomToSchemeHomOver (Over.homMk (U := Over.mk t') (V := Over.mk t) ψ hψ ≫ a))).1 =
      schemeHomOverComp ψ hψ (L.ptsEquiv n t (overHomToSchemeHomOver a)).1
    have hcomp : overHomToSchemeHomOver (Over.homMk (U := Over.mk t') (V := Over.mk t) ψ hψ ≫ a) =
        schemeHomOverComp ψ hψ (overHomToSchemeHomOver a) := by
      apply Subtype.ext; simp [overHomToSchemeHomOver, schemeHomOverComp]
    rw [hcomp, L.ptsEquiv_natural n t t' ψ hψ]

end S_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_schemeKer_eq
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_schemeKer_eq (solution)
