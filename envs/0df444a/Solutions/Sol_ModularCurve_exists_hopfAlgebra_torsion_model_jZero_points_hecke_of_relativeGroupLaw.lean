-- Prove2me | solution 1 for ModularCurve.exists_hopfAlgebra_torsion_model_jZero_points_hecke_of_relativeGroupLaw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/a77c68f2-0ef9-52a4-93dc-16b3025a992f

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hopfAlgebra_torsion_of_isFinite_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_hopfAlgebra_torsion_model_jZero_points_hecke_of_relativeGroupLaw
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve

namespace B1b

variable {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}

theorem eq_one_of_mul_self (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) (h : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.inv t x) (L.mul t x x) := by rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul]
    _ = L.mul t (L.inv t x) x := by rw [h]
    _ = L.one t := L.inv_mul_cancel t x

theorem comp_one (L : RelativeGroupLaw R f) (φ : SchemeHomOver f f)
    (hφ : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
      schemeHomOverComp (L.mul s x y) φ = L.mul s (schemeHomOverComp x φ) (schemeHomOverComp y φ))
    {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) :
    schemeHomOverComp (L.one s) φ = L.one s :=
  eq_one_of_mul_self L s _ (by rw [← hφ, L.one_mul])

theorem comp_nsmul (L : RelativeGroupLaw R f) (φ : SchemeHomOver f f)
    (hφ : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
      schemeHomOverComp (L.mul s x y) φ = L.mul s (schemeHomOverComp x φ) (schemeHomOverComp y φ))
    {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver s f) :
    schemeHomOverComp (L.nsmul s n x) φ = L.nsmul s n (schemeHomOverComp x φ) := by
  induction n with
  | zero => exact comp_one L φ hφ s
  | succ n ih => rw [L.nsmul_succ, L.nsmul_succ, hφ, ih]

theorem isTorsionPoint_comp (L : RelativeGroupLaw R f) (φ : SchemeHomOver f f)
    (hφ : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
      schemeHomOverComp (L.mul s x y) φ = L.mul s (schemeHomOverComp x φ) (schemeHomOverComp y φ))
    {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) {x : SchemeHomOver s f}
    (hx : L.IsTorsionPoint s n x) : L.IsTorsionPoint s n (schemeHomOverComp x φ) := by
  rw [RelativeGroupLaw.isTorsionPoint_def] at hx ⊢
  rw [← comp_nsmul L φ hφ, hx, comp_one L φ hφ]

section Pts
variable {M : Type} [AddCommGroup M] (L : RelativeGroupLaw R f)
  {S : Scheme.{0}} {s : S ⟶ Spec (CommRingCat.of R)} (pts : M ≃ SchemeHomOver s f)
  (hadd : ∀ x y : M, pts (x + y) = L.mul s (pts x) (pts y))
include hadd

theorem pts_zero : pts 0 = L.one s :=
  eq_one_of_mul_self L s _ (by rw [← hadd, add_zero])

theorem pts_nsmul (n : ℕ) (x : M) : pts (n • x) = L.nsmul s n (pts x) := by
  induction n with
  | zero => rw [zero_smul, L.nsmul_zero]; exact pts_zero L pts hadd
  | succ n ih => rw [add_smul, one_smul, hadd, ih, L.nsmul_succ]

private theorem _root_.B1b.mem_torsionBy_iff (n : ℕ) (x : M) :
    x ∈ Submodule.torsionBy ℤ M ((n : ℤ) ^ 1) ↔ pts x ∈ L.torsionSubset s n := by
  rw [pow_one, Submodule.mem_torsionBy_iff, RelativeGroupLaw.mem_torsionSubset,
    RelativeGroupLaw.isTorsionPoint_def, ← pts_nsmul L pts hadd, ← pts_zero L pts hadd,
    pts.apply_eq_iff_eq, natCast_zsmul]

p2m_export "B1b" "mem_torsionBy_iff"
end Pts

end B1b

open B1b in
set_option maxHeartbeats 6400000 in
theorem solution
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))}
    (L : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt p) f)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))
      (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)
    (pts : JZero N ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) f)
    (hpts_add : ∀ x y : JZero N, pts (x + y) = L.mul _ (pts x) (pts y))
    (hpts_gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero N),
      (pts (σ • x)).1 =
        Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (φJ : HeckeAlg → SchemeHomOver f f)
    (hφJ_mul : ∀ (t : HeckeAlg) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))
      (x y : SchemeHomOver s f),
      NeronModelInfra.schemeHomOverComp (L.mul s x y) (φJ t) =
        L.mul s (NeronModelInfra.schemeHomOverComp x (φJ t))
          (NeronModelInfra.schemeHomOverComp y (φJ t)))
    (hφJ_pts : letI := heckeModuleBar N
      ∀ (t : HeckeAlg) (x : JZero N), (pts (t • x)).1 = (pts x).1 ≫ (φJ t).1)
    (hfin : IsFinite (L.schemeNsmul p)) (hflat : Flat (L.schemeNsmul p)) :
    letI := heckeModuleBar N
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ↥(GaloisRep.ratLocalizedAt p) H),
      Module.Finite ↥(GaloisRep.ratLocalizedAt p) H ∧ Module.Flat ↥(GaloisRep.ratLocalizedAt p) H ∧ Coalgebra.IsCocomm ↥(GaloisRep.ratLocalizedAt p) H ∧
      ∃ (eT : ∀ (T : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T],
          WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T) ≃
            L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) T))) p)
        (e : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ) ≃
          ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)))
        (φ : HeckeAlg → (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] H)),

        (∀ (T : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T] (g h : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T)),
          ((eT T (g * h)).val : SchemeHomOver _ f) = L.mul _ (eT T g).val (eT T h).val) ∧

        (∀ (T T' : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T] [CommRing T'] [Algebra ↥(GaloisRep.ratLocalizedAt p) T']
            (u : T →ₐ[↥(GaloisRep.ratLocalizedAt p)] T') (g : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T)),
          ((eT T' (.toConv (u.comp g.ofConv))).val : SchemeHomOver _ f).1 =
            Spec.map (CommRingCat.ofHom u.toRingHom) ≫ (eT T g).val.1) ∧

        (∀ g : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ),
          pts (e g : JZero N) = (eT (AlgebraicClosure ℚ) g).val) ∧

        (∀ g h : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ), e (g * h) = e g + e h) ∧

        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
            (g h : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ)),
          (∀ x : H, h x = σ (g x)) → ((e h : JZero N)) = σ • (e g : JZero N)) ∧

        (∀ t : HeckeAlg,
          RingHom.ker (Bialgebra.counitAlgHom ↥(GaloisRep.ratLocalizedAt p) H) ≤
            (RingHom.ker (Bialgebra.counitAlgHom ↥(GaloisRep.ratLocalizedAt p) H)).comap (φ t)) ∧

        (∀ (t : HeckeAlg) (T : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T] (g : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T)),
          ((eT T (.toConv (g.ofConv.comp (φ t)))).val : SchemeHomOver _ f).1 =
            (eT T g).val.1 ≫ (φJ t).1) ∧

        (∀ (t : HeckeAlg) (g h : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ)),
          (∀ x : H, h x = g (φ t x)) → ((e h : JZero N)) = t • (e g : JZero N)) := by
  classical

  obtain ⟨H, instCR, instHA, hfinH, hflatH, hcocomm, eT, heT_mul, heT_nat⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_hopfAlgebra_torsion_of_isFinite_of_flat L hcomm p hfin hflat

  let ptsT : ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)) ≃
      ↥(L.torsionSubset (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))) p) :=
    pts.subtypeEquiv (fun x => mem_torsionBy_iff L pts hpts_add p x)
  let e : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ) ≃
      ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)) := (eT (AlgebraicClosure ℚ)).trans ptsT.symm
  have he3 : ∀ g, pts (e g : JZero N) = (eT (AlgebraicClosure ℚ) g).val := by
    intro g
    show pts ((ptsT.symm (eT (AlgebraicClosure ℚ) g)) : JZero N) = _
    exact congrArg Subtype.val (ptsT.apply_symm_apply (eT (AlgebraicClosure ℚ) g))

  let Φ : HeckeAlg → ∀ (T : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T],
      ↥(L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) T))) p) →
      ↥(L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) T))) p) :=
    fun t T _ _ x => ⟨schemeHomOverComp x.1 (φJ t), isTorsionPoint_comp L (φJ t) (hφJ_mul t) _ p x.2⟩

  let Ψ : HeckeAlg → ∀ (T : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T],
      WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T) → WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T) :=
    fun t T _ _ g => (eT T).symm (Φ t T (eT T g))
  let φ : HeckeAlg → (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] H) := fun t => (Ψ t H (.toConv (AlgHom.id _ _))).ofConv

  have hΨ : ∀ (t : HeckeAlg) (T : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T]
      (g : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T)),
      Ψ t T g = .toConv (g.ofConv.comp (φ t)) := by
    intro t T _ _ g
    apply (eT T).injective

    apply Subtype.ext; apply Subtype.ext
    have hL : ((eT T (Ψ t T g)).val : SchemeHomOver _ f).1 = (eT T g).val.1 ≫ (φJ t).1 := by
      show ((eT T ((eT T).symm (Φ t T (eT T g)))).val : SchemeHomOver _ f).1 = _
      rw [Equiv.apply_symm_apply]
      rfl
    have hg : ((eT T g).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g.ofConv.toRingHom) ≫ (eT H (.toConv (AlgHom.id _ _))).val.1 := by
      have := heT_nat H T g.ofConv (.toConv (AlgHom.id _ _))
      rw [show g.ofConv.comp (WithConv.toConv (AlgHom.id ↥(GaloisRep.ratLocalizedAt p) H)).ofConv = g.ofConv
        from AlgHom.comp_id _] at this
      exact this
    have hR : ((eT T (.toConv (g.ofConv.comp (φ t)))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g.ofConv.toRingHom) ≫ ((eT H (.toConv (AlgHom.id _ _))).val.1 ≫ (φJ t).1) := by
      have h1 := heT_nat H T g.ofConv (Ψ t H (.toConv (AlgHom.id _ _)))
      have h2 : ((eT H (Ψ t H (.toConv (AlgHom.id _ _)))).val : SchemeHomOver _ f).1 =
          (eT H (.toConv (AlgHom.id _ _))).val.1 ≫ (φJ t).1 := by
        show ((eT H ((eT H).symm (Φ t H (eT H (.toConv (AlgHom.id _ _)))))).val : SchemeHomOver _ f).1 = _
        rw [Equiv.apply_symm_apply]
        rfl
      rw [h2] at h1
      exact h1
    rw [hL, hR, hg, Category.assoc]
  have h7 : ∀ (t : HeckeAlg) (T : Type) [CommRing T] [Algebra ↥(GaloisRep.ratLocalizedAt p) T]
      (g : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] T)),
      ((eT T (.toConv (g.ofConv.comp (φ t)))).val : SchemeHomOver _ f).1 = (eT T g).val.1 ≫ (φJ t).1 := by
    intro t T _ _ g
    rw [← hΨ t T g]
    show ((eT T ((eT T).symm (Φ t T (eT T g)))).val : SchemeHomOver _ f).1 = _
    rw [Equiv.apply_symm_apply]
    rfl
  refine ⟨H, instCR, instHA, hfinH, hflatH, hcocomm, eT, e, φ, heT_mul, heT_nat, he3, ?_, ?_, ?_, h7, ?_⟩
  ·
    intro g h
    apply Subtype.ext
    apply pts.injective
    rw [Submodule.coe_add, hpts_add, he3, he3, he3, heT_mul]
  ·
    intro σ g h hσ
    apply pts.injective
    apply Subtype.ext
    let u : AlgebraicClosure ℚ →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ :=
      (σ.restrictScalars ↥(GaloisRep.ratLocalizedAt p)).toAlgHom
    have hh : h = .toConv (u.comp g.ofConv) := by
      apply WithConv.ext; apply AlgHom.ext; intro x; exact hσ x
    have hu : CommRingCat.ofHom u.toRingHom =
        CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) := rfl
    rw [hpts_gal, he3, he3, hh, heT_nat _ _ u g, hu]
  ·
    intro t x hx
    rw [Ideal.mem_comap, RingHom.mem_ker]
    rw [RingHom.mem_ker] at hx

    have h1val : ((eT ↥(GaloisRep.ratLocalizedAt p) 1).val : SchemeHomOver _ f) = L.one _ :=
      eq_one_of_mul_self L _ _ (by rw [← heT_mul, mul_one])
    have hΦ1 : Φ t ↥(GaloisRep.ratLocalizedAt p) (eT ↥(GaloisRep.ratLocalizedAt p) 1) =
        eT ↥(GaloisRep.ratLocalizedAt p) 1 := by
      apply Subtype.ext
      show schemeHomOverComp (eT ↥(GaloisRep.ratLocalizedAt p) 1).val (φJ t) = _
      rw [h1val, comp_one L (φJ t) (hφJ_mul t)]
    have hΨ1 : Ψ t ↥(GaloisRep.ratLocalizedAt p) 1 = 1 := by
      show (eT ↥(GaloisRep.ratLocalizedAt p)).symm (Φ t _ (eT _ 1)) = 1
      rw [hΦ1, Equiv.symm_apply_apply]
    rw [hΨ t] at hΨ1

    have key := congrArg (fun w : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(GaloisRep.ratLocalizedAt p)) => w.ofConv x) hΨ1
    simp only [AlgHom.comp_apply] at key
    change (1 : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(GaloisRep.ratLocalizedAt p))) (φ t x) =
      (1 : WithConv (H →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(GaloisRep.ratLocalizedAt p))) x at key
    rw [AlgHom.convOne_apply, AlgHom.convOne_apply, Algebra.algebraMap_self, RingHom.id_apply,
      RingHom.id_apply] at key
    change Coalgebra.counit (φ t x) = 0
    change Coalgebra.counit x = 0 at hx
    rw [key, hx]
  ·
    intro t g h hgh
    apply pts.injective
    apply Subtype.ext
    have hh : h = .toConv (g.ofConv.comp (φ t)) := by
      apply WithConv.ext; apply AlgHom.ext; intro x; exact hgh x
    rw [hφJ_pts, he3, he3, hh, h7]

end S_ModularCurve_exists_hopfAlgebra_torsion_model_jZero_points_hecke_of_relativeGroupLaw
end P2MW
export P2MW.S_ModularCurve_exists_hopfAlgebra_torsion_model_jZero_points_hecke_of_relativeGroupLaw (solution)
