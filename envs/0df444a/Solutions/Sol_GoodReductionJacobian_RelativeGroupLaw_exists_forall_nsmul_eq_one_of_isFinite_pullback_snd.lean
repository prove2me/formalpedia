-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_forall_nsmul_eq_one_of_isFinite_pullback_snd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/b3d4cac5-8561-517f-9918-0c45b349d962

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_eq
import Theorems.Thm_AlgebraicGeometry_exists_hopfAlgebra_of_grpObj_over_spec
import Theorems.Thm_HopfAlgebra_convPow_finrank_eq_one_of_isCocomm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_nsmul_eq_one_of_isFinite_pullback_snd
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
p2m_open_scoped "CategoryTheory.MonObj CategoryTheory.MonoidalCategory"

universe u

namespace P2mKill

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

section KernelLaw

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  {fX : X ⟶ Spec (CommRingCat.of R)} {fY : Y ⟶ Spec (CommRingCat.of R)}

def IsHomFor (LX : RelativeGroupLaw R fX) (LY : RelativeGroupLaw R fY) (φ : SchemeHomOver fX fY) :
    Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t fX),
    (LX.mul t x y) ⊚ φ = LY.mul t (x ⊚ φ) (y ⊚ φ)

theorem IsHomFor.one {LX : RelativeGroupLaw R fX} {LY : RelativeGroupLaw R fY} {φ : SchemeHomOver fX fY}
    (H : IsHomFor LX LY φ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (LX.one t) ⊚ φ = LY.one t := by
  letI := LY.pointGroup t
  have h := H t (LX.one t) (LX.one t)
  rw [LX.one_mul] at h
  have h' : ((LX.one t) ⊚ φ) * 1 = ((LX.one t) ⊚ φ) * ((LX.one t) ⊚ φ) := by
    rw [mul_one]; exact h
  exact (mul_left_cancel h').symm

theorem IsHomFor.inv {LX : RelativeGroupLaw R fX} {LY : RelativeGroupLaw R fY} {φ : SchemeHomOver fX fY}
    (H : IsHomFor LX LY φ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t fX) :
    (LX.inv t x) ⊚ φ = LY.inv t (x ⊚ φ) := by
  letI := LY.pointGroup t
  have h : ((LX.inv t x) ⊚ φ) * (x ⊚ φ) = 1 := by
    change LY.mul t ((LX.inv t x) ⊚ φ) (x ⊚ φ) = LY.one t
    rw [← H, LX.inv_mul_cancel, H.one]
  exact eq_inv_of_mul_eq_one_left h

theorem one_coe (LY : RelativeGroupLaw R fY) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (LY.one t).1 = t ≫ (LY.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  rw [← LY.one_natural (𝟙 _) t t (Category.comp_id t)]
  rfl

variable (LY : RelativeGroupLaw R fY) (u : SchemeHomOver fX fY)

abbrev unitY : Spec (CommRingCat.of R) ⟶ Y := (LY.one (𝟙 (Spec (CommRingCat.of R)))).1

abbrev Ker : Scheme.{u} := pullback u.1 (unitY LY)

abbrev kerStr : Ker LY u ⟶ Spec (CommRingCat.of R) := pullback.snd u.1 (unitY LY)

theorem fst_comp_fX : pullback.fst u.1 (unitY LY) ≫ fX = kerStr LY u := by
  calc pullback.fst u.1 (unitY LY) ≫ fX
      = pullback.fst u.1 (unitY LY) ≫ (u.1 ≫ fY) := by rw [u.2]
    _ = (pullback.fst u.1 (unitY LY) ≫ u.1) ≫ fY := (Category.assoc _ _ _).symm
    _ = (pullback.snd u.1 (unitY LY) ≫ unitY LY) ≫ fY := by rw [pullback.condition]
    _ = pullback.snd u.1 (unitY LY) ≫ (unitY LY ≫ fY) := Category.assoc _ _ _
    _ = kerStr LY u := by rw [(LY.one (𝟙 _)).2, Category.comp_id]

def incl {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (z : SchemeHomOver t (kerStr LY u)) :
    SchemeHomOver t fX :=
  ⟨z.1 ≫ pullback.fst u.1 (unitY LY), by rw [Category.assoc, fst_comp_fX, z.2]⟩

@[scoped simp] theorem incl_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (z : SchemeHomOver t (kerStr LY u)) : (incl LY u z).1 = z.1 ≫ pullback.fst u.1 (unitY LY) := rfl

theorem incl_injective {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} :
    Function.Injective (incl LY u (T := T) (t := t)) := by
  intro z w h
  apply Subtype.ext
  apply pullback.hom_ext
  · exact congrArg Subtype.val h
  · rw [z.2, w.2]

theorem incl_comp_u {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (z : SchemeHomOver t (kerStr LY u)) : (incl LY u z) ⊚ u = LY.one t := by
  apply Subtype.ext
  rw [one_coe]
  change (z.1 ≫ pullback.fst u.1 (unitY LY)) ≫ u.1 = t ≫ unitY LY
  rw [Category.assoc, pullback.condition, ← Category.assoc, z.2]

def klift {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t fX)
    (hx : x ⊚ u = LY.one t) : SchemeHomOver t (kerStr LY u) :=
  ⟨pullback.lift x.1 t (by
      have h := congrArg Subtype.val hx
      rw [one_coe] at h
      exact h), pullback.lift_snd _ _ _⟩

@[scoped simp] theorem incl_klift {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t fX)
    (hx : x ⊚ u = LY.one t) : incl LY u (klift LY u x hx) = x :=
  Subtype.ext (pullback.lift_fst _ _ _)

theorem incl_natural {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (z : SchemeHomOver t (kerStr LY u)) :
    incl LY u (GoodReductionJacobian.schemeHomOverComp ψ hψ z) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (incl LY u z) :=
  Subtype.ext (Category.assoc _ _ _)

variable {LY u} {LX : RelativeGroupLaw R fX} (hu : IsHomFor LX LY u)
include hu

theorem mul_mem {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t fX)
    (hx : x ⊚ u = LY.one t) (hy : y ⊚ u = LY.one t) : (LX.mul t x y) ⊚ u = LY.one t := by
  rw [hu, hx, hy, LY.one_mul]

theorem inv_mem {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t fX)
    (hx : x ⊚ u = LY.one t) : (LX.inv t x) ⊚ u = LY.one t := by
  letI := LY.pointGroup t
  rw [hu.inv, hx]
  exact inv_one

def kmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (z w : SchemeHomOver t (kerStr LY u)) :
    SchemeHomOver t (kerStr LY u) :=
  klift LY u (LX.mul t (incl LY u z) (incl LY u w))
    (mul_mem hu t _ _ (incl_comp_u LY u z) (incl_comp_u LY u w))

def kone {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : SchemeHomOver t (kerStr LY u) :=
  klift LY u (LX.one t) (hu.one t)

def kinv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (z : SchemeHomOver t (kerStr LY u)) :
    SchemeHomOver t (kerStr LY u) :=
  klift LY u (LX.inv t (incl LY u z)) (inv_mem hu t _ (incl_comp_u LY u z))

@[scoped simp] theorem incl_kmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z w : SchemeHomOver t (kerStr LY u)) :
    incl LY u (kmul hu t z w) = LX.mul t (incl LY u z) (incl LY u w) :=
  incl_klift _ _ _ _

@[scoped simp] theorem incl_kone {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    incl LY u (kone hu t) = LX.one t :=
  incl_klift _ _ _ _

@[scoped simp] theorem incl_kinv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z : SchemeHomOver t (kerStr LY u)) :
    incl LY u (kinv hu t z) = LX.inv t (incl LY u z) :=
  incl_klift _ _ _ _

def kerLaw : RelativeGroupLaw R (kerStr LY u) where
  mul t z w := kmul hu t z w
  one t := kone hu t
  inv t z := kinv hu t z
  mul_assoc t x y z := incl_injective LY u (by
    rw [incl_kmul, incl_kmul, incl_kmul, incl_kmul, LX.mul_assoc])
  one_mul t x := incl_injective LY u (by rw [incl_kmul, incl_kone, LX.one_mul])
  mul_one t x := incl_injective LY u (by rw [incl_kmul, incl_kone, LX.mul_one])
  inv_mul_cancel t x := incl_injective LY u (by rw [incl_kmul, incl_kinv, incl_kone, LX.inv_mul_cancel])
  mul_natural t t' ψ hψ x y := incl_injective LY u (by
    rw [incl_natural, incl_kmul, incl_kmul, LX.mul_natural, incl_natural, incl_natural])

theorem kerLaw_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z w : SchemeHomOver t (kerStr LY u)) : (kerLaw hu).mul t z w = kmul hu t z w := rfl

theorem kerLaw_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (kerLaw hu).one t = kone hu t := rfl

theorem incl_kerLaw_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z w : SchemeHomOver t (kerStr LY u)) :
    incl LY u ((kerLaw hu).mul t z w) = LX.mul t (incl LY u z) (incl LY u w) :=
  incl_kmul hu t z w

theorem incl_kerLaw_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    incl LY u ((kerLaw hu).one t) = LX.one t :=
  incl_kone hu t

theorem incl_kerLaw_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (z : SchemeHomOver t (kerStr LY u)) :
    incl LY u ((kerLaw hu).nsmul t n z) = LX.nsmul t n (incl LY u z) := by
  induction n with
  | zero => exact incl_kone hu t
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, incl_kerLaw_mul, ih]

theorem kerLaw_isCommutative (hcX : LX.IsCommutative) : (kerLaw hu).IsCommutative := by
  intro T t z w
  exact incl_injective LY u (by rw [incl_kerLaw_mul, incl_kerLaw_mul, hcX.mul_comm])

end KernelLaw

section OverField

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
  {fX : X ⟶ Spec (CommRingCat.of K)} {fY : Y ⟶ Spec (CommRingCat.of K)}
  {LX : RelativeGroupLaw K fX} {LY : RelativeGroupLaw K fY} {u : SchemeHomOver fX fY}

theorem overHom_pow (hu : IsHomFor LX LY u) (g : GrpObj (Over.mk (kerStr LY u)))
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (a b : Over.mk t ⟶ Over.mk (kerStr LY u)),
      overHomToSchemeHomOver (CartesianMonoidalCategory.lift a b ≫ g.mul) =
        (kerLaw hu).mul t (overHomToSchemeHomOver a) (overHomToSchemeHomOver b))
    (hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)),
      overHomToSchemeHomOver (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ g.one) = (kerLaw hu).one t)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (a : Over.mk t ⟶ Over.mk (kerStr LY u))
    (n : ℕ) :
    letI : GrpObj (Over.mk (kerStr LY u)) := g
    overHomToSchemeHomOver (a ^ n) = (kerLaw hu).nsmul t n (overHomToSchemeHomOver a) := by
  letI : GrpObj (Over.mk (kerStr LY u)) := g
  induction n with
  | zero =>
      rw [pow_zero, RelativeGroupLaw.nsmul_zero]
      exact hone t
  | succ n ih =>
      rw [pow_succ, RelativeGroupLaw.nsmul_succ, ← ih]
      exact hmul t (a ^ n) a

theorem exists_kill_specPoints (hu : IsHomFor LX LY u) (hcX : LX.IsCommutative)
    (hker : IsFinite (kerStr LY u)) :
    ∃ N : ℕ, 0 < N ∧ ∀ (L : Type u) [CommRing L] [Algebra K L]
      (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) (kerStr LY u)),
      (kerLaw hu).nsmul _ N z = (kerLaw hu).one _ := by

  obtain ⟨g, hmul, hone, -⟩ := (kerLaw hu).exists_grpObj_eq
  letI : GrpObj (Over.mk (kerStr LY u)) := g
  have hcommK : (kerLaw hu).IsCommutative := kerLaw_isCommutative hu hcX
  have hswap : ∀ (a b : Over.mk (kerStr LY u) ⊗ Over.mk (kerStr LY u) ⟶ Over.mk (kerStr LY u)),
      CartesianMonoidalCategory.lift a b ≫ μ[Over.mk (kerStr LY u)] =
        CartesianMonoidalCategory.lift b a ≫ μ[Over.mk (kerStr LY u)] := by
    intro a b
    have ha := hmul (Over.mk (kerStr LY u) ⊗ Over.mk (kerStr LY u)).hom a b
    have hb := hmul (Over.mk (kerStr LY u) ⊗ Over.mk (kerStr LY u)).hom b a
    rw [hcommK.mul_comm] at ha
    rw [← hb] at ha
    have hinj : Function.Injective
        (overHomToSchemeHomOver (g := (Over.mk (kerStr LY u) ⊗ Over.mk (kerStr LY u)).hom)
          (f := kerStr LY u)) :=
      (schemeHomOverEquivOverHom (Over.mk (kerStr LY u) ⊗ Over.mk (kerStr LY u)).hom
        (kerStr LY u)).symm.injective
    exact hinj ha
  haveI : IsCommMonObj (Over.mk (kerStr LY u)) := ⟨by
    calc (β_ (Over.mk (kerStr LY u)) (Over.mk (kerStr LY u))).hom ≫ μ[Over.mk (kerStr LY u)]
        = CartesianMonoidalCategory.lift
            (CartesianMonoidalCategory.snd (Over.mk (kerStr LY u)) (Over.mk (kerStr LY u)))
            (CartesianMonoidalCategory.fst (Over.mk (kerStr LY u)) (Over.mk (kerStr LY u))) ≫
            μ[Over.mk (kerStr LY u)] := by
          rw [CartesianMonoidalCategory.lift_snd_fst]
      _ = CartesianMonoidalCategory.lift
            (CartesianMonoidalCategory.fst (Over.mk (kerStr LY u)) (Over.mk (kerStr LY u)))
            (CartesianMonoidalCategory.snd (Over.mk (kerStr LY u)) (Over.mk (kerStr LY u))) ≫
            μ[Over.mk (kerStr LY u)] := hswap _ _
      _ = μ[Over.mk (kerStr LY u)] := by
          rw [CartesianMonoidalCategory.lift_fst_snd, Category.id_comp]⟩
  haveI : IsFinite (Over.mk (kerStr LY u)).hom := hker

  obtain ⟨A, instA, instH, hfinA, hcocomm, e, hemul, -⟩ :=
    AlgebraicGeometry.exists_hopfAlgebra_of_grpObj_over_spec K (Over.mk (kerStr LY u))
  letI := instA
  letI := instH
  haveI := hfinA
  haveI := hcocomm

  have he_one : ∀ (L : Type u) [CommRing L] [Algebra K L], e L 1 = 1 := by
    intro L _ _
    have h := hemul L 1 1
    rw [mul_one] at h
    have h' : e L 1 * 1 = e L 1 * e L 1 := by rw [mul_one]; exact h
    exact (mul_left_cancel h').symm
  have he_pow : ∀ (L : Type u) [CommRing L] [Algebra K L] (φ : WithConv (A →ₐ[K] L)) (n : ℕ),
      e L (φ ^ n) = (e L φ) ^ n := by
    intro L _ _ φ n
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact he_one L
    | succ n ih => rw [pow_succ, pow_succ, hemul, ih]

  have hApos : 0 < Module.finrank K A := by
    have f₀ : A →ₐ[K] K := ((e K).symm 1).ofConv
    haveI : Nontrivial A := f₀.toRingHom.domain_nontrivial
    exact Module.finrank_pos
  refine ⟨Module.finrank K A, hApos, ?_⟩
  intro L _ _ z
  let a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ Over.mk (kerStr LY u) :=
    schemeHomOverToOverHom z

  have hkill : a ^ Module.finrank K A = 1 := by
    have h := HopfAlgebra.convPow_finrank_eq_one_of_isCocomm K A L ((e L).symm a)
    have h' := congrArg (e L) h
    rw [he_pow, he_one, Equiv.apply_symm_apply] at h'
    exact h'
  have hz : overHomToSchemeHomOver a = z := overHomToSchemeHomOver_schemeHomOverToOverHom z
  have hp := overHom_pow hu g hmul hone (Spec.map (CommRingCat.ofHom (algebraMap K L))) a
    (Module.finrank K A)
  rw [hkill, hz] at hp
  rw [← hp]
  exact hone _

theorem exists_kill (hu : IsHomFor LX LY u) (hcX : LX.IsCommutative)
    (hker : IsFinite (kerStr LY u)) :
    ∃ N : ℕ, 0 < N ∧ ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (z : SchemeHomOver t (kerStr LY u)), (kerLaw hu).nsmul t N z = (kerLaw hu).one t := by
  obtain ⟨N, hN, hkill⟩ := exists_kill_specPoints hu hcX hker
  refine ⟨N, hN, ?_⟩
  intro T t z

  haveI : IsFinite (kerStr LY u) := hker
  haveI : IsAffine (Ker LY u) := isAffine_of_isAffineHom (kerStr LY u)
  set H : Scheme.{u} := Ker LY u with hH
  set φ : Spec Γ(H, ⊤) ⟶ Spec (CommRingCat.of K) := H.isoSpec.inv ≫ kerStr LY u with hφ
  set ρ : CommRingCat.of K ⟶ Γ(H, ⊤) := Spec.preimage φ with hρ
  letI : Algebra K Γ(H, ⊤) := ρ.hom.toAlgebra
  have hρ' : CommRingCat.ofHom (algebraMap K Γ(H, ⊤)) = ρ := CommRingCat.ofHom_hom ρ
  have ht₀ : Spec.map (CommRingCat.ofHom (algebraMap K Γ(H, ⊤))) = φ := by
    rw [hρ', hρ, Spec.map_preimage]

  let z₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Γ(H, ⊤)))) (kerStr LY u) :=
    ⟨H.isoSpec.inv, by rw [ht₀]⟩
  have h₀ := hkill Γ(H, ⊤) z₀

  have hψ : (z.1 ≫ H.isoSpec.hom) ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(H, ⊤))) = t := by
    rw [ht₀, hφ, Category.assoc, Iso.hom_inv_id_assoc, z.2]
  have hzz : GoodReductionJacobian.schemeHomOverComp (z.1 ≫ H.isoSpec.hom) hψ z₀ = z := by
    apply Subtype.ext
    change (z.1 ≫ H.isoSpec.hom) ≫ H.isoSpec.inv = z.1
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← hzz, ← (kerLaw hu).nsmul_natural _ _ _ hψ, h₀, (kerLaw hu).one_natural]

theorem main (LX : RelativeGroupLaw K fX) (hcX : LX.IsCommutative) (LY : RelativeGroupLaw K fY)
    (u : SchemeHomOver fX fY) (hu : IsHomFor LX LY u)
    (hker : IsFinite (pullback.snd u.1 (LY.one (𝟙 (Spec (CommRingCat.of K)))).1)) :
    ∃ N : ℕ, 0 < N ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t fX),
        x ⊚ u = LY.one t → LX.nsmul t N x = LX.one t := by
  obtain ⟨N, hN, hkill⟩ := exists_kill hu hcX hker
  refine ⟨N, hN, ?_⟩
  intro T t x hx
  have h := congrArg (incl LY u) (hkill t (klift LY u x hx))
  rw [incl_kerLaw_nsmul, incl_klift, incl_kerLaw_one] at h
  exact h

end OverField

end P2mKill
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_nsmul_eq_one_of_isFinite_pullback_snd.P2mKill"

theorem solution
    {K : Type u} [Field K]
    {X : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of K)} (LX : RelativeGroupLaw K fX)
    (hcX : LX.IsCommutative)
    {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of K)} (LY : RelativeGroupLaw K fY)
    (u : SchemeHomOver fX fY)
    (hu : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t fX),
      NeronModelInfra.schemeHomOverComp (LX.mul t x y) u =
        LY.mul t (NeronModelInfra.schemeHomOverComp x u) (NeronModelInfra.schemeHomOverComp y u))
    (hker : IsFinite (pullback.snd u.1 (LY.one (𝟙 (Spec (CommRingCat.of K)))).1)) :
    ∃ N : ℕ, 0 < N ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t fX),
        NeronModelInfra.schemeHomOverComp x u = LY.one t → LX.nsmul t N x = LX.one t := by
  obtain ⟨N, hN, h⟩ := P2mKill.main LX hcX LY u (fun T t x y => hu t x y) hker
  exact ⟨N, hN, fun t x hx => h t x hx⟩

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_nsmul_eq_one_of_isFinite_pullback_snd.P2mKill"

end S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_nsmul_eq_one_of_isFinite_pullback_snd
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_forall_nsmul_eq_one_of_isFinite_pullback_snd (solution)
