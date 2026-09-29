-- Prove2me | solution 1 for GoodReductionJacobian.lift_comp_mul_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/50c05302-d26b-5b23-8053-b060a0b00965

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Theorems.Thm_AlgebraicGeometry_eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
import Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_lift_comp_mul_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace P2mWs49AxiomsUniq

section Setup

variable {R : Type u} [CommRing R] (I : Ideal R) {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))

theorem isPullback_thickening (n : ℕ) :
    IsPullback (adicThickeningι f I n) (adicThickeningToBase f I n) f (adicThickeningBase I n) :=
  IsPullback.of_hasPullback f (adicThickeningBase I n)

def mkPt (n : ℕ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))} (k : T ⟶ A)
    (hk : k ≫ f = t ≫ adicThickeningBase I n) : SchemeHomOver t (adicThickeningToBase f I n) :=
  ⟨(isPullback_thickening I f n).lift k t hk, (isPullback_thickening I f n).lift_snd _ _ _⟩

@[scoped simp] theorem mkPt_ι (n : ℕ) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))} (k : T ⟶ A)
    (hk : k ≫ f = t ≫ adicThickeningBase I n) : (mkPt I f n k hk).1 ≫ adicThickeningι f I n = k :=
  (isPullback_thickening I f n).lift_fst _ _ _

def upt (n : ℕ) : SchemeHomOver (adicThickeningToBase f I n) (adicThickeningToBase f I n) :=
  ⟨𝟙 _, Category.id_comp _⟩

@[scoped simp] theorem upt_coe (n : ℕ) : (upt I f n).1 = 𝟙 _ := rfl

theorem one_coe_eq {S : Type u} [CommRing S] {B T : Scheme.{u}} {b : B ⟶ Spec (CommRingCat.of S)}
    (G : RelativeGroupLaw S b) (t : T ⟶ Spec (CommRingCat.of S)) :
    (G.one t).1 = t ≫ (G.one (𝟙 (Spec (CommRingCat.of S)))).1 :=
  (congrArg Subtype.val (G.one_natural (𝟙 _) t t (Category.comp_id t))).symm

variable (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
  (L : ∀ n : ℕ, RelativeGroupLaw (R ⧸ I ^ (n + 1)) (adicThickeningToBase f I n))

theorem one_ι (hone : ∀ n : ℕ, ((L n).one (𝟙 _)).1 ≫ adicThickeningι f I n = adicThickeningBase I n ≫ e.1)
    (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))) :
    ((L n).one t).1 ≫ adicThickeningι f I n = t ≫ adicThickeningBase I n ≫ e.1 := by
  rw [one_coe_eq (L n) t, Category.assoc, hone n]

theorem mul_ι (m : pullback f f ⟶ A)
    (hmul : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
        (x y : SchemeHomOver t (adicThickeningToBase f I n)),
        pullback.lift (x.1 ≫ adicThickeningι f I n) (y.1 ≫ adicThickeningι f I n)
            (by rw [Category.assoc, Category.assoc, adicThickeningι_comp, ← Category.assoc, ← Category.assoc, x.2, y.2]) ≫ m =
          ((L n).mul t x y).1 ≫ adicThickeningι f I n)
    (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
    (x y : SchemeHomOver t (adicThickeningToBase f I n)) (k : T ⟶ pullback f f)
    (h1 : k ≫ pullback.fst f f = x.1 ≫ adicThickeningι f I n) (h2 : k ≫ pullback.snd f f = y.1 ≫ adicThickeningι f I n) :
    k ≫ m = ((L n).mul t x y).1 ≫ adicThickeningι f I n := by
  have hk : k = pullback.lift (x.1 ≫ adicThickeningι f I n) (y.1 ≫ adicThickeningι f I n)
      (by rw [Category.assoc, Category.assoc, adicThickeningι_comp, ← Category.assoc, ← Category.assoc, x.2, y.2]) :=
    pullback.hom_ext (by rw [pullback.lift_fst, h1]) (by rw [pullback.lift_snd, h2])
  rw [hk]
  exact hmul n t x y

theorem inv_ι (i : A ⟶ A)
    (hinv : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
        (x : SchemeHomOver t (adicThickeningToBase f I n)),
        x.1 ≫ adicThickeningι f I n ≫ i = ((L n).inv t x).1 ≫ adicThickeningι f I n)
    (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
    (x : SchemeHomOver t (adicThickeningToBase f I n)) (k : T ⟶ A) (hk : k = x.1 ≫ adicThickeningι f I n) :
    k ≫ i = ((L n).inv t x).1 ≫ adicThickeningι f I n := by
  rw [hk, Category.assoc]
  exact hinv n t x

end Setup

end P2mWs49AxiomsUniq
p2m_reactivate "P2MW.S_GoodReductionJacobian_lift_comp_mul_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete.P2mWs49AxiomsUniq"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_lift_comp_mul_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete.P2mWs49AxiomsUniq"

open P2mWs49AxiomsUniq in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ι : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hι : IsClosedImmersion ι)
    (hιf : ι ≫ ProjSpace.π R N = f)
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (L : ∀ n : ℕ, RelativeGroupLaw (R ⧸ I ^ (n + 1)) (adicThickeningToBase f I n))
    (hone : ∀ n : ℕ, ((L n).one (𝟙 _)).1 ≫ adicThickeningι f I n = adicThickeningBase I n ≫ e.1)
    (m : pullback f f ⟶ A) (hm : m ≫ f = pullback.fst f f ≫ f)
    (hmul : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
        (x y : SchemeHomOver t (adicThickeningToBase f I n)),
        pullback.lift (x.1 ≫ adicThickeningι f I n) (y.1 ≫ adicThickeningι f I n)
            (by rw [Category.assoc, Category.assoc, adicThickeningι_comp, ← Category.assoc, ← Category.assoc, x.2, y.2]) ≫ m =
          ((L n).mul t x y).1 ≫ adicThickeningι f I n)
    (i : A ⟶ A) (hi : i ≫ f = f)
    (hinv : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1))))
        (x : SchemeHomOver t (adicThickeningToBase f I n)),
        x.1 ≫ adicThickeningι f I n ≫ i = ((L n).inv t x).1 ≫ adicThickeningι f I n) :
    pullback.lift (f ≫ e.1) (𝟙 A) (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]) ≫ m = 𝟙 A ∧
    pullback.lift (𝟙 A) (f ≫ e.1) (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]) ≫ m = 𝟙 A ∧
    pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ m) (pullback.snd (pullback.fst f f ≫ f) f)
          (by rw [Category.assoc, hm]; exact pullback.condition) ≫ m =
        pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.fst f f)
          (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f) (pullback.snd (pullback.fst f f ≫ f) f)
              (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition) ≫ m)
          (by rw [Category.assoc, Category.assoc, hm, pullback.lift_fst_assoc, Category.assoc,
                ← pullback.condition (f := f) (g := f)]) ≫ m ∧
    pullback.lift i (𝟙 A) (by rw [hi, Category.id_comp]) ≫ m = f ≫ e.1 := by

  obtain ⟨K, ι₂, -, hι₂, hι₂f⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion f f N ι hι hιf N ι hι hιf
  obtain ⟨K₃, ι₃, -, hι₃, hι₃f⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
      (pullback.fst f f ≫ f) f K ι₂ hι₂ hι₂f N ι hι hιf
  have hP : ∀ n : ℕ, IsPullback (adicThickeningι f I n) (adicThickeningToBase f I n) f (adicThickeningBase I n) :=
    fun n => isPullback_thickening I f n

  have hupt : ∀ n : ℕ, adicThickeningι f I n = (upt I f n).1 ≫ adicThickeningι f I n := fun n => by
    rw [upt_coe, Category.id_comp]

  have hιfe : ∀ n : ℕ, adicThickeningι f I n ≫ f ≫ e.1 =
      ((L n).one (adicThickeningToBase f I n)).1 ≫ adicThickeningι f I n := fun n => by
    rw [one_ι I f e L hone, ← Category.assoc, (hP n).w, Category.assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    apply AlgebraicGeometry.eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
      I f f N ι hι hιf N ι hι hιf
    · rw [Category.assoc, hm, pullback.lift_fst_assoc, Category.assoc, e.2, Category.comp_id]
    · exact Category.id_comp f
    · intro n
      have key := mul_ι I f L m hmul n (adicThickeningToBase f I n) ((L n).one _) (upt I f n)
        (adicThickeningι f I n ≫ pullback.lift (f ≫ e.1) (𝟙 A)
          (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]))
        (by rw [Category.assoc, pullback.lift_fst, hιfe])
        (by rw [Category.assoc, pullback.lift_snd, Category.comp_id, ← hupt])
      rw [← Category.assoc, key, (L n).one_mul, ← hupt, Category.comp_id]
  ·
    apply AlgebraicGeometry.eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
      I f f N ι hι hιf N ι hι hιf
    · rw [Category.assoc, hm, pullback.lift_fst_assoc, Category.id_comp]
    · exact Category.id_comp f
    · intro n
      have key := mul_ι I f L m hmul n (adicThickeningToBase f I n) (upt I f n) ((L n).one _)
        (adicThickeningι f I n ≫ pullback.lift (𝟙 A) (f ≫ e.1)
          (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]))
        (by rw [Category.assoc, pullback.lift_fst, Category.comp_id, ← hupt])
        (by rw [Category.assoc, pullback.lift_snd, hιfe])
      rw [← Category.assoc, key, (L n).mul_one, ← hupt, Category.comp_id]
  ·
    apply AlgebraicGeometry.eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
      I (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) f K₃ ι₃ hι₃ hι₃f N ι hι hιf
    · simp only [Category.assoc, hm, pullback.lift_fst_assoc]
    · simp only [Category.assoc, hm, pullback.lift_fst_assoc]
    · intro n
      have hP₃ := isPullback_thickening I (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) n

      have hx : (adicThickeningι (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n ≫ pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.fst f f) ≫ f = adicThickeningToBase (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n ≫ adicThickeningBase I n := by
        simp only [Category.assoc]; exact hP₃.w
      have hy : (adicThickeningι (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n ≫ pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f) ≫ f = adicThickeningToBase (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n ≫ adicThickeningBase I n := by
        simp only [Category.assoc]; rw [← pullback.condition]; exact hP₃.w
      have hz : (adicThickeningι (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n ≫ pullback.snd (pullback.fst f f ≫ f) f) ≫ f = adicThickeningToBase (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n ≫ adicThickeningBase I n := by
        simp only [Category.assoc]; rw [← pullback.condition]; exact hP₃.w
      let x := mkPt I f n _ hx
      let y := mkPt I f n _ hy
      let z := mkPt I f n _ hz
      have hxι : x.1 ≫ adicThickeningι f I n = adicThickeningι (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n ≫ pullback.fst _ _ ≫ pullback.fst f f := mkPt_ι I f n _ hx
      have hyι : y.1 ≫ adicThickeningι f I n = adicThickeningι (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n ≫ pullback.fst _ _ ≫ pullback.snd f f := mkPt_ι I f n _ hy
      have hzι : z.1 ≫ adicThickeningι f I n = adicThickeningι (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n ≫ pullback.snd _ _ := mkPt_ι I f n _ hz

      have hxy : adicThickeningι (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n ≫ pullback.fst _ _ ≫ m = ((L n).mul (adicThickeningToBase (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n) x y).1 ≫ adicThickeningι f I n := by
        have h := mul_ι I f L m hmul n (adicThickeningToBase (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n) x y (adicThickeningι (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n ≫ pullback.fst _ _)
          (by simp only [Category.assoc]; exact hxι.symm) (by simp only [Category.assoc]; exact hyι.symm)
        simpa only [Category.assoc] using h
      have lhs : adicThickeningι (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n ≫ pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ m) (pullback.snd (pullback.fst f f ≫ f) f)
          (by rw [Category.assoc, hm]; exact pullback.condition) ≫ m =
          ((L n).mul (adicThickeningToBase (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n) ((L n).mul (adicThickeningToBase (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n) x y) z).1 ≫ adicThickeningι f I n := by
        have h := mul_ι I f L m hmul n (adicThickeningToBase (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n) ((L n).mul (adicThickeningToBase (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n) x y) z
          (adicThickeningι (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n ≫ pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ m) (pullback.snd (pullback.fst f f ≫ f) f)
            (by rw [Category.assoc, hm]; exact pullback.condition))
          (by simp only [Category.assoc, pullback.lift_fst]; exact hxy)
          (by simp only [Category.assoc, pullback.lift_snd]; exact hzι.symm)
        simpa only [Category.assoc] using h

      have hyz : adicThickeningι (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n ≫ pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f)
          (pullback.snd (pullback.fst f f ≫ f) f)
          (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition) ≫ m =
          ((L n).mul (adicThickeningToBase (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n) y z).1 ≫ adicThickeningι f I n := by
        have h := mul_ι I f L m hmul n (adicThickeningToBase (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n) y z
          (adicThickeningι (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n ≫ pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f)
            (pullback.snd (pullback.fst f f ≫ f) f)
            (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition))
          (by simp only [Category.assoc, pullback.lift_fst]; exact hyι.symm)
          (by simp only [Category.assoc, pullback.lift_snd]; exact hzι.symm)
        simpa only [Category.assoc] using h
      have rhs : adicThickeningι (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n ≫ pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.fst f f)
          (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f) (pullback.snd (pullback.fst f f ≫ f) f)
              (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition) ≫ m)
          (by rw [Category.assoc, Category.assoc, hm, pullback.lift_fst_assoc, Category.assoc,
                ← pullback.condition (f := f) (g := f)]) ≫ m =
          ((L n).mul (adicThickeningToBase (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n) x ((L n).mul (adicThickeningToBase (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n) y z)).1 ≫ adicThickeningι f I n := by
        have h := mul_ι I f L m hmul n (adicThickeningToBase (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n) x ((L n).mul (adicThickeningToBase (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n) y z)
          (adicThickeningι (pullback.fst (pullback.fst f f ≫ f) f ≫ (pullback.fst f f ≫ f)) I n ≫ pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.fst f f)
            (pullback.lift (pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f) (pullback.snd (pullback.fst f f ≫ f) f)
                (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition) ≫ m)
            (by rw [Category.assoc, Category.assoc, hm, pullback.lift_fst_assoc, Category.assoc,
                  ← pullback.condition (f := f) (g := f)]))
          (by simp only [Category.assoc, pullback.lift_fst]; exact hxι.symm)
          (by simp only [Category.assoc, pullback.lift_snd]; exact hyz)
        simpa only [Category.assoc] using h
      rw [lhs, rhs, (L n).mul_assoc]
  ·
    apply AlgebraicGeometry.eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
      I f f N ι hι hιf N ι hι hιf
    · rw [Category.assoc, hm, pullback.lift_fst_assoc, hi]
    · rw [Category.assoc, e.2, Category.comp_id]
    · intro n
      have hk : adicThickeningι f I n ≫ i = ((L n).inv _ (upt I f n)).1 ≫ adicThickeningι f I n :=
        inv_ι I f L i hinv n _ (upt I f n) _ (hupt n)
      have key := mul_ι I f L m hmul n (adicThickeningToBase f I n) ((L n).inv _ (upt I f n)) (upt I f n)
        (adicThickeningι f I n ≫ pullback.lift i (𝟙 A) (by rw [hi, Category.id_comp]))
        (by rw [Category.assoc, pullback.lift_fst, hk])
        (by rw [Category.assoc, pullback.lift_snd, Category.comp_id, ← hupt])
      rw [← Category.assoc, key, (L n).inv_mul_cancel, hιfe]

end S_GoodReductionJacobian_lift_comp_mul_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete
end P2MW
export P2MW.S_GoodReductionJacobian_lift_comp_mul_eq_of_forall_relativeGroupLaw_adicThickening_of_isAdicComplete (solution)
