-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isCommutative_forall_mul_comp_eq_of_charts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/0f60054d-6e93-5610-9fcf-cbcbb77f9ae6

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_one_comp_eq_one_comp_of_charts
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_inv_comp_eq_inv_comp_of_charts
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_forall_mul_comp_eq_of_charts

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace BenchQLG

section transport
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)

theorem mul_val_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (x y : SchemeHomOver t f) :
    (G.mul t x y).1 = (G.mul t' ⟨x.1, x.2.trans h⟩ ⟨y.1, y.2.trans h⟩).1 := by subst h; rfl

theorem one_val_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') :
    (G.one t).1 = (G.one t').1 := by subst h; rfl

theorem inv_val_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (x : SchemeHomOver t f) : (G.inv t x).1 = (G.inv t' ⟨x.1, x.2.trans h⟩).1 := by subst h; rfl

theorem mul_congr_pts {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {x x' y y' : SchemeHomOver t f}
    (hx : x.1 = x'.1) (hy : y.1 = y'.1) : (G.mul t x y).1 = (G.mul t x' y').1 := by
  rw [Subtype.ext hx, Subtype.ext hy]

noncomputable def compHom {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    letI := G.pointGroup t; letI := G.pointGroup t'
    SchemeHomOver t f →* SchemeHomOver t' f :=
  letI := G.pointGroup t; letI := G.pointGroup t'
  MonoidHom.mk' (schemeHomOverComp ψ hψ) (G.mul_natural t t' ψ hψ)

theorem comp_inv {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t; letI := G.pointGroup t'
  exact map_inv (compHom G t t' ψ hψ) x

end transport

section glue

variable {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
  (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of S))
  {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (ι : ∀ i, A' i ⟶ Y)
  [∀ i, IsOpenImmersion (ι i)]
  (hsq : ∀ i, CategoryTheory.IsPullback (ι i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
  (L' : ∀ i, RelativeGroupLaw (B i) (f' i))

noncomputable abbrev σ (S : Type u) [CommRing S] {k : ℕ} (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)]
    (i : Fin k) : Spec (CommRingCat.of (B i)) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (B i)))

omit hr f' ι hsq L' in
include r in
theorem isOpenImmersion_σ (i : Fin k) : IsOpenImmersion (σ S B i) := IsOpenImmersion.of_isLocalization (r i)

omit hr f' ι hsq L' in
theorem range_σ (i : Fin k) : Set.range (σ S B i) = (PrimeSpectrum.basicOpen (r i) : Set (PrimeSpectrum S)) :=
  PrimeSpectrum.localization_away_comap_range (B i) (r i)

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))

noncomputable abbrev V (i : Fin k) : T.Opens := t ⁻¹ᵁ (PrimeSpectrum.basicOpen (r i))

include hr in
theorem isOpenCover_V : TopologicalSpace.IsOpenCover (V r t) := by
  apply TopologicalSpace.IsOpenCover.mk
  show ⨆ i, t ⁻¹ᵁ (PrimeSpectrum.basicOpen (r i)) = ⊤
  rw [← Scheme.Hom.preimage_iSup]
  have : (⨆ i, PrimeSpectrum.basicOpen (r i) : TopologicalSpace.Opens (PrimeSpectrum S)) = ⊤ :=
    (PrimeSpectrum.iSup_basicOpen_eq_top_iff).mpr hr
  erw [this]
  first
    | rfl
    | exact Scheme.Hom.preimage_top t
    | (ext x; simp)

noncomputable def 𝒱 : T.OpenCover := T.openCoverOfIsOpenCover (V r t) (isOpenCover_V r hr t)

noncomputable def tV (i : Fin k) : (V r t i : Scheme.{u}) ⟶ Spec (CommRingCat.of (B i)) :=
  haveI := isOpenImmersion_σ r B i
  IsOpenImmersion.lift (σ S B i) ((V r t i).ι ≫ t) (by
    rw [range_σ r B i]
    rintro _ ⟨x, rfl⟩
    exact x.2)

omit hr in
theorem tV_σ (i : Fin k) : tV r B t i ≫ σ S B i = (V r t i).ι ≫ t := by
  haveI := isOpenImmersion_σ r B i
  exact IsOpenImmersion.lift_fac _ _ _

noncomputable def liftPt (i : Fin k) (x : SchemeHomOver t f) : SchemeHomOver (tV r B t i) (f' i) :=
  ⟨(hsq i).lift ((V r t i).ι ≫ x.1) (tV r B t i) (by rw [Category.assoc, x.2, tV_σ]), (hsq i).lift_snd _ _ _⟩

omit hr in
theorem liftPt_ι (i : Fin k) (x : SchemeHomOver t f) : (liftPt r B f f' ι hsq t i x).1 ≫ ι i = (V r t i).ι ≫ x.1 :=
  (hsq i).lift_fst _ _ _

noncomputable def mulV (i : Fin k) (x y : SchemeHomOver t f) : (V r t i : Scheme.{u}) ⟶ Y :=
  ((L' i).mul (tV r B t i) (liftPt r B f f' ι hsq t i x) (liftPt r B f f' ι hsq t i y)).1 ≫ ι i

variable (hagree : ∀ (i j : Fin k) {T : Scheme.{u}} (tᵢ : T ⟶ Spec (CommRingCat.of (B i))) (tⱼ : T ⟶ Spec (CommRingCat.of (B j)))
    (a b : SchemeHomOver tᵢ (f' i)) (a' b' : SchemeHomOver tⱼ (f' j)),
    a.1 ≫ ι i = a'.1 ≫ ι j → b.1 ≫ ι i = b'.1 ≫ ι j →
      ((L' i).mul tᵢ a b).1 ≫ ι i = ((L' j).mul tⱼ a' b').1 ≫ ι j)

omit hr in

theorem comp_mulV {W : Scheme.{u}} (i : Fin k) (x y : SchemeHomOver t f) (p : W ⟶ (V r t i : Scheme.{u})) :
    p ≫ mulV r B f f' ι hsq L' t i x y =
      ((L' i).mul (p ≫ tV r B t i) (schemeHomOverComp p rfl (liftPt r B f f' ι hsq t i x))
        (schemeHomOverComp p rfl (liftPt r B f f' ι hsq t i y))).1 ≫ ι i := by
  show p ≫ ((L' i).mul _ _ _).1 ≫ ι i = _
  rw [← Category.assoc]
  congr 1
  exact congrArg Subtype.val ((L' i).mul_natural (tV r B t i) (p ≫ tV r B t i) p rfl _ _)

omit hr in
include hagree in
theorem mulV_compat (x y : SchemeHomOver t f) (i j : Fin k) :
    pullback.fst ((V r t i).ι) ((V r t j).ι) ≫ mulV r B f f' ι hsq L' t i x y =
      pullback.snd ((V r t i).ι) ((V r t j).ι) ≫ mulV r B f f' ι hsq L' t j x y := by
  rw [comp_mulV, comp_mulV]
  apply hagree i j
  · show (pullback.fst _ _ ≫ (liftPt r B f f' ι hsq t i x).1) ≫ ι i = (pullback.snd _ _ ≫ (liftPt r B f f' ι hsq t j x).1) ≫ ι j
    rw [Category.assoc, liftPt_ι, Category.assoc, liftPt_ι, ← Category.assoc, ← Category.assoc, pullback.condition]
  · show (pullback.fst _ _ ≫ (liftPt r B f f' ι hsq t i y).1) ≫ ι i = (pullback.snd _ _ ≫ (liftPt r B f f' ι hsq t j y).1) ≫ ι j
    rw [Category.assoc, liftPt_ι, Category.assoc, liftPt_ι, ← Category.assoc, ← Category.assoc, pullback.condition]

noncomputable def mulG (x y : SchemeHomOver t f) : T ⟶ Y :=
  Scheme.Cover.glueMorphisms (𝒱 r hr t) (fun i => mulV r B f f' ι hsq L' t i x y)
    (fun i j => mulV_compat r B f f' ι hsq L' t hagree x y i j)

include hagree in
theorem ι_mulG (x y : SchemeHomOver t f) (i : Fin k) :
    (V r t i).ι ≫ mulG r hr B f f' ι hsq L' t hagree x y = mulV r B f f' ι hsq L' t i x y := by
  have := Scheme.Cover.ι_glueMorphisms (𝒱 r hr t) (fun i => mulV r B f f' ι hsq L' t i x y)
    (fun i j => mulV_compat r B f f' ι hsq L' t hagree x y i j) i
  exact this

omit hr in
theorem mulV_f (i : Fin k) (x y : SchemeHomOver t f) : mulV r B f f' ι hsq L' t i x y ≫ f = (V r t i).ι ≫ t := by
  show (((L' i).mul _ _ _).1 ≫ ι i) ≫ f = _
  rw [Category.assoc, (hsq i).w, ← Category.assoc, ((L' i).mul _ _ _).2, tV_σ]

include hagree in
theorem mulG_f (x y : SchemeHomOver t f) : mulG r hr B f f' ι hsq L' t hagree x y ≫ f = t := by
  apply Scheme.Cover.hom_ext (𝒱 r hr t)
  intro i
  show (V r t i).ι ≫ _ ≫ f = (V r t i).ι ≫ t
  rw [← Category.assoc, ι_mulG, mulV_f]

noncomputable def oneV (i : Fin k) : (V r t i : Scheme.{u}) ⟶ Y := ((L' i).one (tV r B t i)).1 ≫ ι i

noncomputable def invV (i : Fin k) (x : SchemeHomOver t f) : (V r t i : Scheme.{u}) ⟶ Y :=
  ((L' i).inv (tV r B t i) (liftPt r B f f' ι hsq t i x)).1 ≫ ι i

omit hr in
theorem base_compat (i j : Fin k) :
    (pullback.fst ((V r t i).ι) ((V r t j).ι) ≫ tV r B t i) ≫ σ S B i =
      (pullback.snd ((V r t i).ι) ((V r t j).ι) ≫ tV r B t j) ≫ σ S B j := by
  rw [Category.assoc, tV_σ, Category.assoc, tV_σ, ← Category.assoc, ← Category.assoc, pullback.condition]

omit hr in
include hsq hagree in
theorem oneV_compat (i j : Fin k) :
    pullback.fst ((V r t i).ι) ((V r t j).ι) ≫ oneV r B f' ι L' t i =
      pullback.snd ((V r t i).ι) ((V r t j).ι) ≫ oneV r B f' ι L' t j := by
  show pullback.fst _ _ ≫ ((L' i).one _).1 ≫ ι i = pullback.snd _ _ ≫ ((L' j).one _).1 ≫ ι j
  have e1 := congrArg Subtype.val ((L' i).one_natural (tV r B t i) (pullback.fst ((V r t i).ι) ((V r t j).ι) ≫ tV r B t i) _ rfl)
  have e2 := congrArg Subtype.val ((L' j).one_natural (tV r B t j) (pullback.snd ((V r t i).ι) ((V r t j).ι) ≫ tV r B t j) _ rfl)
  simp only [schemeHomOverComp_coe] at e1 e2
  rw [← Category.assoc, ← Category.assoc, e1, e2]
  exact GoodReductionJacobian.RelativeGroupLaw.one_comp_eq_one_comp_of_charts f (f' i) (ι i) (hsq i).w (f' j) (ι j) (hsq j)
    (L' i) (L' j) (fun t₁ t₂ a b a' b' => hagree i j t₁ t₂ a b a' b') _ _ (base_compat r B t i j)

omit hr in
include hagree in
theorem invV_compat (x : SchemeHomOver t f) (i j : Fin k) :
    pullback.fst ((V r t i).ι) ((V r t j).ι) ≫ invV r B f f' ι hsq L' t i x =
      pullback.snd ((V r t i).ι) ((V r t j).ι) ≫ invV r B f f' ι hsq L' t j x := by
  show pullback.fst _ _ ≫ ((L' i).inv _ _).1 ≫ ι i = pullback.snd _ _ ≫ ((L' j).inv _ _).1 ≫ ι j
  have e1 := congrArg Subtype.val (comp_inv (L' i) (tV r B t i)
    (pullback.fst ((V r t i).ι) ((V r t j).ι) ≫ tV r B t i) _ rfl (liftPt r B f f' ι hsq t i x))
  have e2 := congrArg Subtype.val (comp_inv (L' j) (tV r B t j)
    (pullback.snd ((V r t i).ι) ((V r t j).ι) ≫ tV r B t j) _ rfl (liftPt r B f f' ι hsq t j x))
  simp only [schemeHomOverComp_coe] at e1 e2
  rw [← Category.assoc, ← Category.assoc, e1, e2]
  apply GoodReductionJacobian.RelativeGroupLaw.inv_comp_eq_inv_comp_of_charts f (f' i) (ι i) (hsq i).w (f' j) (ι j) (hsq j)
    (L' i) (L' j) (fun t₁ t₂ a b a' b' => hagree i j t₁ t₂ a b a' b') _ _ (base_compat r B t i j)
  show (pullback.fst _ _ ≫ (liftPt r B f f' ι hsq t i x).1) ≫ ι i = (pullback.snd _ _ ≫ (liftPt r B f f' ι hsq t j x).1) ≫ ι j
  rw [Category.assoc, liftPt_ι, Category.assoc, liftPt_ι, ← Category.assoc, ← Category.assoc, pullback.condition]

noncomputable def oneG : T ⟶ Y :=
  Scheme.Cover.glueMorphisms (𝒱 r hr t) (fun i => oneV r B f' ι L' t i)
    (fun i j => oneV_compat r B f f' ι hsq L' t hagree i j)

noncomputable def invG (x : SchemeHomOver t f) : T ⟶ Y :=
  Scheme.Cover.glueMorphisms (𝒱 r hr t) (fun i => invV r B f f' ι hsq L' t i x)
    (fun i j => invV_compat r B f f' ι hsq L' t hagree x i j)

include hagree in
theorem ι_oneG (i : Fin k) : (V r t i).ι ≫ oneG r hr B f f' ι hsq L' t hagree = oneV r B f' ι L' t i :=
  Scheme.Cover.ι_glueMorphisms (𝒱 r hr t) _ _ i

include hagree in
theorem ι_invG (x : SchemeHomOver t f) (i : Fin k) :
    (V r t i).ι ≫ invG r hr B f f' ι hsq L' t hagree x = invV r B f f' ι hsq L' t i x :=
  Scheme.Cover.ι_glueMorphisms (𝒱 r hr t) _ _ i

include hagree in
theorem oneG_f : oneG r hr B f f' ι hsq L' t hagree ≫ f = t := by
  apply Scheme.Cover.hom_ext (𝒱 r hr t)
  intro i
  show (V r t i).ι ≫ _ ≫ f = (V r t i).ι ≫ t
  rw [← Category.assoc, ι_oneG]
  show (((L' i).one _).1 ≫ ι i) ≫ f = _
  rw [Category.assoc, (hsq i).w, ← Category.assoc, ((L' i).one _).2, tV_σ]

include hagree in
theorem invG_f (x : SchemeHomOver t f) : invG r hr B f f' ι hsq L' t hagree x ≫ f = t := by
  apply Scheme.Cover.hom_ext (𝒱 r hr t)
  intro i
  show (V r t i).ι ≫ _ ≫ f = (V r t i).ι ≫ t
  rw [← Category.assoc, ι_invG]
  show (((L' i).inv _ _).1 ≫ ι i) ≫ f = _
  rw [Category.assoc, (hsq i).w, ← Category.assoc, ((L' i).inv _ _).2, tV_σ]

noncomputable def mulPt (x y : SchemeHomOver t f) : SchemeHomOver t f :=
  ⟨mulG r hr B f f' ι hsq L' t hagree x y, mulG_f r hr B f f' ι hsq L' t hagree x y⟩

noncomputable def onePt : SchemeHomOver t f :=
  ⟨oneG r hr B f f' ι hsq L' t hagree, oneG_f r hr B f f' ι hsq L' t hagree⟩

noncomputable def invPt (x : SchemeHomOver t f) : SchemeHomOver t f :=
  ⟨invG r hr B f f' ι hsq L' t hagree x, invG_f r hr B f f' ι hsq L' t hagree x⟩

omit hr in

theorem liftPt_eq_of_ι (i : Fin k) (z : SchemeHomOver t f) (w : SchemeHomOver (tV r B t i) (f' i))
    (h : w.1 ≫ ι i = (V r t i).ι ≫ z.1) : liftPt r B f f' ι hsq t i z = w := by
  apply Subtype.ext
  apply (hsq i).hom_ext
  · rw [liftPt_ι, h]
  · rw [(liftPt r B f f' ι hsq t i z).2, w.2]

include hagree in
theorem liftPt_mulPt (i : Fin k) (x y : SchemeHomOver t f) :
    liftPt r B f f' ι hsq t i (mulPt r hr B f f' ι hsq L' t hagree x y) =
      (L' i).mul (tV r B t i) (liftPt r B f f' ι hsq t i x) (liftPt r B f f' ι hsq t i y) := by
  apply liftPt_eq_of_ι
  show _ = (V r t i).ι ≫ mulG r hr B f f' ι hsq L' t hagree x y
  rw [ι_mulG]; rfl

include hagree in
theorem liftPt_onePt (i : Fin k) :
    liftPt r B f f' ι hsq t i (onePt r hr B f f' ι hsq L' t hagree) = (L' i).one (tV r B t i) := by
  apply liftPt_eq_of_ι
  show _ = (V r t i).ι ≫ oneG r hr B f f' ι hsq L' t hagree
  rw [ι_oneG]; rfl

include hagree in
theorem liftPt_invPt (i : Fin k) (x : SchemeHomOver t f) :
    liftPt r B f f' ι hsq t i (invPt r hr B f f' ι hsq L' t hagree x) =
      (L' i).inv (tV r B t i) (liftPt r B f f' ι hsq t i x) := by
  apply liftPt_eq_of_ι
  show _ = (V r t i).ι ≫ invG r hr B f f' ι hsq L' t hagree x
  rw [ι_invG]; rfl

noncomputable def glued : RelativeGroupLaw S f where
  mul t x y := mulPt r hr B f f' ι hsq L' t hagree x y
  one t := onePt r hr B f f' ι hsq L' t hagree
  inv t x := invPt r hr B f f' ι hsq L' t hagree x
  mul_assoc t x y z := by
    apply Subtype.ext
    apply Scheme.Cover.hom_ext (𝒱 r hr t)
    intro i
    show (V r t i).ι ≫ mulG r hr B f f' ι hsq L' t hagree _ _ = (V r t i).ι ≫ mulG r hr B f f' ι hsq L' t hagree _ _
    rw [ι_mulG, ι_mulG]
    show ((L' i).mul _ _ _).1 ≫ ι i = ((L' i).mul _ _ _).1 ≫ ι i
    rw [liftPt_mulPt, liftPt_mulPt, (L' i).mul_assoc]
  one_mul t x := by
    apply Subtype.ext
    apply Scheme.Cover.hom_ext (𝒱 r hr t)
    intro i
    show (V r t i).ι ≫ mulG r hr B f f' ι hsq L' t hagree _ _ = (V r t i).ι ≫ x.1
    rw [ι_mulG]
    show ((L' i).mul _ _ _).1 ≫ ι i = _
    rw [liftPt_onePt, (L' i).one_mul, liftPt_ι]
  mul_one t x := by
    apply Subtype.ext
    apply Scheme.Cover.hom_ext (𝒱 r hr t)
    intro i
    show (V r t i).ι ≫ mulG r hr B f f' ι hsq L' t hagree _ _ = (V r t i).ι ≫ x.1
    rw [ι_mulG]
    show ((L' i).mul _ _ _).1 ≫ ι i = _
    rw [liftPt_onePt, (L' i).mul_one, liftPt_ι]
  inv_mul_cancel t x := by
    apply Subtype.ext
    apply Scheme.Cover.hom_ext (𝒱 r hr t)
    intro i
    show (V r t i).ι ≫ mulG r hr B f f' ι hsq L' t hagree _ _ = (V r t i).ι ≫ oneG r hr B f f' ι hsq L' t hagree
    rw [ι_mulG, ι_oneG]
    show ((L' i).mul _ _ _).1 ≫ ι i = ((L' i).one _).1 ≫ ι i
    rw [liftPt_invPt, (L' i).inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    subst hψ
    apply Subtype.ext
    apply Scheme.Cover.hom_ext (𝒱 r hr (ψ ≫ t))
    intro i
    show (V r (ψ ≫ t) i).ι ≫ ψ ≫ mulG r hr B f f' ι hsq L' t hagree x y =
      (V r (ψ ≫ t) i).ι ≫ mulG r hr B f f' ι hsq L' (ψ ≫ t) hagree _ _

    let ψV : (V r (ψ ≫ t) i : Scheme.{u}) ⟶ (V r t i : Scheme.{u}) :=
      ψ.resLE (V r t i) (V r (ψ ≫ t) i) (le_of_eq (Scheme.Hom.comp_preimage ψ t _))
    have hres : (V r (ψ ≫ t) i).ι ≫ ψ = ψV ≫ (V r t i).ι := (Scheme.Hom.resLE_comp_ι _ _).symm
    rw [ι_mulG, ← Category.assoc, hres, Category.assoc, ι_mulG, comp_mulV]

    haveI := isOpenImmersion_σ r B i
    have hb : ψV ≫ tV r B t i = tV r B (ψ ≫ t) i := by
      rw [← cancel_mono (σ S B i), Category.assoc, tV_σ, tV_σ, ← Category.assoc, ← hres, Category.assoc]

    have hp : ∀ z : SchemeHomOver t f,
        (schemeHomOverComp ψV rfl (liftPt r B f f' ι hsq t i z)).1 =
          (liftPt r B f f' ι hsq (ψ ≫ t) i (schemeHomOverComp ψ rfl z)).1 := by
      intro z
      apply (hsq i).hom_ext
      · show (ψV ≫ (liftPt r B f f' ι hsq t i z).1) ≫ ι i = _
        rw [Category.assoc, liftPt_ι, liftPt_ι, ← Category.assoc, ← hres, Category.assoc]; rfl
      · show (ψV ≫ (liftPt r B f f' ι hsq t i z).1) ≫ f' i = _
        rw [Category.assoc, (liftPt r B f f' ι hsq t i z).2, hb, (liftPt r B f f' ι hsq (ψ ≫ t) i _).2]
    show _ = ((L' i).mul _ _ _).1 ≫ ι i
    rw [mul_val_congr (L' i) hb]
    have ex : ∀ z : SchemeHomOver t f,
        (⟨(schemeHomOverComp ψV rfl (liftPt r B f f' ι hsq t i z)).1,
          (schemeHomOverComp ψV rfl (liftPt r B f f' ι hsq t i z)).2.trans hb⟩ :
            SchemeHomOver (tV r B (ψ ≫ t) i) (f' i)) =
        liftPt r B f f' ι hsq (ψ ≫ t) i (schemeHomOverComp ψ rfl z) := fun z => Subtype.ext (hp z)
    rw [ex x, ex y]

include hagree in
theorem glued_comm (hcomm : ∀ i, (L' i).IsCommutative) :
    (glued r hr B f f' ι hsq L' hagree).IsCommutative := by
  intro T t x y
  apply Subtype.ext
  apply Scheme.Cover.hom_ext (𝒱 r hr t)
  intro i
  show (V r t i).ι ≫ mulG r hr B f f' ι hsq L' t hagree x y = (V r t i).ι ≫ mulG r hr B f f' ι hsq L' t hagree y x
  rw [ι_mulG, ι_mulG]
  show ((L' i).mul _ _ _).1 ≫ ι i = ((L' i).mul _ _ _).1 ≫ ι i
  rw [hcomm i (tV r B t i)]

include hagree in
theorem glued_hom (i : Fin k) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of (B i))) (x y : SchemeHomOver t' (f' i)) :
    ((L' i).mul t' x y).1 ≫ ι i =
      ((glued r hr B f f' ι hsq L' hagree).mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (B i))))
        ⟨x.1 ≫ ι i, by rw [Category.assoc, (hsq i).w, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ ι i, by rw [Category.assoc, (hsq i).w, ← Category.assoc, y.2]⟩).1 := by
  apply Scheme.Cover.hom_ext (𝒱 r hr (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
  intro j
  show (V r _ j).ι ≫ ((L' i).mul t' x y).1 ≫ ι i = (V r _ j).ι ≫ mulG r hr B f f' ι hsq L' _ hagree _ _
  rw [ι_mulG]
  show _ = ((L' j).mul _ _ _).1 ≫ ι j
  have e1 := congrArg Subtype.val ((L' i).mul_natural t' ((V r (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (B i)))) j).ι ≫ t') _ rfl x y)
  simp only [schemeHomOverComp_coe] at e1
  rw [← Category.assoc, e1]
  apply hagree i j
  · show ((V r _ j).ι ≫ x.1) ≫ ι i = _
    rw [liftPt_ι, Category.assoc]
  · show ((V r _ j).ι ≫ y.1) ≫ ι i = _
    rw [liftPt_ι, Category.assoc]

end glue

end BenchQLG

theorem solution
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of S))
    {A' : Fin k → Scheme.{u}} (f' : ∀ i, A' i ⟶ Spec (CommRingCat.of (B i))) (ι : ∀ i, A' i ⟶ Y)
    [∀ i, IsOpenImmersion (ι i)]
    (hsq : ∀ i, CategoryTheory.IsPullback (ι i) (f' i) f (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))))
    (hsurj : ∀ y : ↥Y, ∃ (i : Fin k) (x : ↥(A' i)), (ι i).base x = y)
    (L' : ∀ i, RelativeGroupLaw (B i) (f' i)) (hcomm : ∀ i, (L' i).IsCommutative)
    (hagree : ∀ (i j : Fin k) {T : Scheme.{u}} (tᵢ : T ⟶ Spec (CommRingCat.of (B i))) (tⱼ : T ⟶ Spec (CommRingCat.of (B j)))
        (a b : SchemeHomOver tᵢ (f' i)) (a' b' : SchemeHomOver tⱼ (f' j)),
        a.1 ≫ ι i = a'.1 ≫ ι j → b.1 ≫ ι i = b'.1 ≫ ι j →
          ((L' i).mul tᵢ a b).1 ≫ ι i = ((L' j).mul tⱼ a' b').1 ≫ ι j) :
    ∃ L : RelativeGroupLaw S f, L.IsCommutative ∧
      ∀ (i : Fin k) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of (B i))) (x y : SchemeHomOver t' (f' i)),
        ((L' i).mul t' x y).1 ≫ ι i =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (B i))))
            ⟨x.1 ≫ ι i, by rw [Category.assoc, (hsq i).w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ ι i, by rw [Category.assoc, (hsq i).w, ← Category.assoc, y.2]⟩).1 :=
  ⟨BenchQLG.glued r hr B f f' ι hsq L' hagree, BenchQLG.glued_comm r hr B f f' ι hsq L' hagree hcomm,
    fun i _ t' x y => BenchQLG.glued_hom r hr B f f' ι hsq L' hagree i t' x y⟩

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_forall_mul_comp_eq_of_charts
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_forall_mul_comp_eq_of_charts (solution)
