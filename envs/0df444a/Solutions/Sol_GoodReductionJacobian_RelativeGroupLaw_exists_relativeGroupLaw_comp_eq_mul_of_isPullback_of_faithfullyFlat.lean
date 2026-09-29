-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/8ab8e28c-c75e-597a-bb7f-c5d13f9b9ceb

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

noncomputable section

namespace P2mWs30RglDescent

section Base

variable (S : Type u) [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']

abbrev ιb : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S S'))

abbrev ι₁ : Spec (CommRingCat.of (S' ⊗[S] S')) ⟶ Spec (CommRingCat.of S') :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)

abbrev ι₂ : Spec (CommRingCat.of (S' ⊗[S] S')) ⟶ Spec (CommRingCat.of S') :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)

theorem ι₁_comp : ι₁ S S' ≫ ιb S S' = ιb S (S' ⊗[S] S') := by
  rw [ιb, ιb, ι₁, ← Spec.map_comp]
  congr 1

theorem ι₂_comp : ι₂ S S' ≫ ιb S S' = ιb S (S' ⊗[S] S') := by
  rw [ιb, ιb, ι₂, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext s
  simp [Algebra.algebraMap_eq_smul_one]

end Base

section Test

variable {S : Type u} [CommRing S] {S' : Type u} [CommRing S'] [Algebra S S']
variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))

abbrev Tb (S' : Type u) [CommRing S'] [Algebra S S'] : Scheme.{u} := pullback t (ιb S S')
abbrev pT (S' : Type u) [CommRing S'] [Algebra S S'] : Tb t S' ⟶ T := pullback.fst t (ιb S S')
abbrev tb (S' : Type u) [CommRing S'] [Algebra S S'] : Tb t S' ⟶ Spec (CommRingCat.of S') :=
  pullback.snd t (ιb S S')

abbrev Tbb (S' : Type u) [CommRing S'] [Algebra S S'] : Scheme.{u} := pullback t (ιb S (S' ⊗[S] S'))
abbrev pTT (S' : Type u) [CommRing S'] [Algebra S S'] : Tbb t S' ⟶ T := pullback.fst t (ιb S (S' ⊗[S] S'))
abbrev tbb (S' : Type u) [CommRing S'] [Algebra S S'] :
    Tbb t S' ⟶ Spec (CommRingCat.of (S' ⊗[S] S')) := pullback.snd t (ιb S (S' ⊗[S] S'))

def q₁ (S' : Type u) [CommRing S'] [Algebra S S'] : Tbb t S' ⟶ Tb t S' :=
  pullback.lift (pTT t S') (tbb t S' ≫ ι₁ S S')
    (by rw [Category.assoc, ι₁_comp]; exact pullback.condition)

def q₂ (S' : Type u) [CommRing S'] [Algebra S S'] : Tbb t S' ⟶ Tb t S' :=
  pullback.lift (pTT t S') (tbb t S' ≫ ι₂ S S')
    (by rw [Category.assoc, ι₂_comp]; exact pullback.condition)

@[scoped simp] theorem q₁_pT : q₁ t S' ≫ pT t S' = pTT t S' := pullback.lift_fst _ _ _
@[scoped simp] theorem q₁_tb : q₁ t S' ≫ tb t S' = tbb t S' ≫ ι₁ S S' := pullback.lift_snd _ _ _
@[scoped simp] theorem q₂_pT : q₂ t S' ≫ pT t S' = pTT t S' := pullback.lift_fst _ _ _
@[scoped simp] theorem q₂_tb : q₂ t S' ≫ tb t S' = tbb t S' ≫ ι₂ S S' := pullback.lift_snd _ _ _

theorem q_pT : q₁ t S' ≫ pT t S' = q₂ t S' ≫ pT t S' := by rw [q₁_pT, q₂_pT]

theorem isPullback_pT : IsPullback (pT t S') (tb t S') t (ιb S S') := IsPullback.of_hasPullback _ _

theorem isPullback_q₁ : IsPullback (q₁ t S') (tbb t S') (tb t S') (ι₁ S S') := by
  have h : IsPullback (q₁ t S' ≫ pT t S') (tbb t S') t (ι₁ S S' ≫ ιb S S') := by
    rw [q₁_pT, ι₁_comp]; exact IsPullback.of_hasPullback _ _
  exact h.of_right (q₁_tb t) (isPullback_pT t)

theorem isPullback_q₂ : IsPullback (q₂ t S') (tbb t S') (tb t S') (ι₂ S S') := by
  have h : IsPullback (q₂ t S' ≫ pT t S') (tbb t S') t (ι₂ S S' ≫ ιb S S') := by
    rw [q₂_pT, ι₂_comp]; exact IsPullback.of_hasPullback _ _
  exact h.of_right (q₂_tb t) (isPullback_pT t)

variable [Module.FaithfullyFlat S S']

theorem descent {Y : Scheme.{u}} (φ' : Tb t S' ⟶ Y) (h : q₁ t S' ≫ φ' = q₂ t S' ≫ φ') :
    ∃! φ : T ⟶ Y, pT t S' ≫ φ = φ' :=
  AlgebraicGeometry.existsUnique_comp_eq_of_isPullback_of_faithfullyFlat t (tb t S') (pT t S')
    (isPullback_pT t) (tbb t S') (q₁ t S') (q₂ t S') (isPullback_q₁ t) (isPullback_q₂ t) (q_pT t) φ' h

def desc {Y : Scheme.{u}} (φ' : Tb t S' ⟶ Y) (h : q₁ t S' ≫ φ' = q₂ t S' ≫ φ') : T ⟶ Y :=
  (descent t φ' h).exists.choose

@[scoped simp] theorem pT_desc {Y : Scheme.{u}} (φ' : Tb t S' ⟶ Y) (h : q₁ t S' ≫ φ' = q₂ t S' ≫ φ') :
    pT t S' ≫ desc t φ' h = φ' :=
  (descent t φ' h).exists.choose_spec

theorem eq_of_pT_comp_eq (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {Y : Scheme.{u}} {a b : T ⟶ Y} (h : pT t S' ≫ a = pT t S' ≫ b) : a = b :=
  (descent t (pT t S' ≫ b) (by rw [← Category.assoc, q_pT, Category.assoc])).unique h rfl

end Test

section PointGroups

theorem map_one_of_map_mul {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] {A₁ A₂ T₁ T₂ : Scheme.{u}}
    {f₁ : A₁ ⟶ Spec (CommRingCat.of R₁)} {f₂ : A₂ ⟶ Spec (CommRingCat.of R₂)}
    (G₁ : RelativeGroupLaw R₁ f₁) (G₂ : RelativeGroupLaw R₂ f₂)
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R₁)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R₂)}
    (φ : SchemeHomOver t₁ f₁ → SchemeHomOver t₂ f₂)
    (hφ : ∀ x y, φ (G₁.mul t₁ x y) = G₂.mul t₂ (φ x) (φ y)) :
    φ (G₁.one t₁) = G₂.one t₂ := by
  letI := G₁.pointGroup t₁
  letI := G₂.pointGroup t₂
  exact map_one (MonoidHom.mk' φ hφ)

theorem map_inv_of_map_mul {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] {A₁ A₂ T₁ T₂ : Scheme.{u}}
    {f₁ : A₁ ⟶ Spec (CommRingCat.of R₁)} {f₂ : A₂ ⟶ Spec (CommRingCat.of R₂)}
    (G₁ : RelativeGroupLaw R₁ f₁) (G₂ : RelativeGroupLaw R₂ f₂)
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R₁)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R₂)}
    (φ : SchemeHomOver t₁ f₁ → SchemeHomOver t₂ f₂)
    (hφ : ∀ x y, φ (G₁.mul t₁ x y) = G₂.mul t₂ (φ x) (φ y)) (x : SchemeHomOver t₁ f₁) :
    φ (G₁.inv t₁ x) = G₂.inv t₂ (φ x) := by
  letI := G₁.pointGroup t₁
  letI := G₂.pointGroup t₂
  exact map_inv (MonoidHom.mk' φ hφ) x

theorem inv_natural {R : Type u} [CommRing R] {A T T' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) =
      G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) :=
  map_inv_of_map_mul G G (GoodReductionJacobian.schemeHomOverComp ψ hψ) (G.mul_natural t t' ψ hψ) x

end PointGroups

structure Datum (S : Type u) [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] where
  X : Scheme.{u}
  A' : Scheme.{u}
  A'' : Scheme.{u}
  f : X ⟶ Spec (CommRingCat.of S)
  f' : A' ⟶ Spec (CommRingCat.of S')
  c : A' ⟶ X
  hc : IsPullback c f' f (ιb S S')
  f'' : A'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))
  a₁ : A'' ⟶ A'
  a₂ : A'' ⟶ A'
  ha₁ : IsPullback a₁ f'' f' (ι₁ S S')
  ha₂ : IsPullback a₂ f'' f' (ι₂ S S')
  hca : a₁ ≫ c = a₂ ≫ c
  L' : RelativeGroupLaw S' f'
  L'' : RelativeGroupLaw (S' ⊗[S] S') f''
  ha₁mul : ∀ {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (x y : SchemeHomOver t'' f''),
    (L''.mul t'' x y).1 ≫ a₁ =
      (L'.mul (t'' ≫ ι₁ S S')
        ⟨x.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, y.2]⟩).1
  ha₂mul : ∀ {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (x y : SchemeHomOver t'' f''),
    (L''.mul t'' x y).1 ≫ a₂ =
      (L'.mul (t'' ≫ ι₂ S S')
        ⟨x.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, y.2]⟩).1

namespace Datum

variable {S : Type u} [CommRing S] {S' : Type u} [CommRing S'] [Algebra S S'] (D : Datum S S')

def toA₁ {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (P : SchemeHomOver t'' D.f'') :
    SchemeHomOver (t'' ≫ ι₁ S S') D.f' :=
  ⟨P.1 ≫ D.a₁, by rw [Category.assoc, D.ha₁.w, ← Category.assoc, P.2]⟩

def toA₂ {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (P : SchemeHomOver t'' D.f'') :
    SchemeHomOver (t'' ≫ ι₂ S S') D.f' :=
  ⟨P.1 ≫ D.a₂, by rw [Category.assoc, D.ha₂.w, ← Category.assoc, P.2]⟩

@[scoped simp] theorem toA₁_coe {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S')))
    (P : SchemeHomOver t'' D.f'') : (D.toA₁ t'' P).1 = P.1 ≫ D.a₁ := rfl
@[scoped simp] theorem toA₂_coe {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S')))
    (P : SchemeHomOver t'' D.f'') : (D.toA₂ t'' P).1 = P.1 ≫ D.a₂ := rfl

theorem toA₁_mul {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S')))
    (x y : SchemeHomOver t'' D.f'') :
    D.toA₁ t'' (D.L''.mul t'' x y) = D.L'.mul _ (D.toA₁ t'' x) (D.toA₁ t'' y) :=
  Subtype.ext (D.ha₁mul t'' x y)

theorem toA₂_mul {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S')))
    (x y : SchemeHomOver t'' D.f'') :
    D.toA₂ t'' (D.L''.mul t'' x y) = D.L'.mul _ (D.toA₂ t'' x) (D.toA₂ t'' y) :=
  Subtype.ext (D.ha₂mul t'' x y)

theorem toA₁_one {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) :
    D.toA₁ t'' (D.L''.one t'') = D.L'.one _ :=
  map_one_of_map_mul D.L'' D.L' (D.toA₁ t'') (D.toA₁_mul t'')

theorem toA₂_one {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) :
    D.toA₂ t'' (D.L''.one t'') = D.L'.one _ :=
  map_one_of_map_mul D.L'' D.L' (D.toA₂ t'') (D.toA₂_mul t'')

theorem toA₁_inv {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S')))
    (x : SchemeHomOver t'' D.f'') : D.toA₁ t'' (D.L''.inv t'' x) = D.L'.inv _ (D.toA₁ t'' x) :=
  map_inv_of_map_mul D.L'' D.L' (D.toA₁ t'') (D.toA₁_mul t'') x

theorem toA₂_inv {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S')))
    (x : SchemeHomOver t'' D.f'') : D.toA₂ t'' (D.L''.inv t'' x) = D.L'.inv _ (D.toA₂ t'' x) :=
  map_inv_of_map_mul D.L'' D.L' (D.toA₂ t'') (D.toA₂_mul t'') x

section Test

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))

def bc (x : SchemeHomOver t D.f) : SchemeHomOver (tb t S') D.f' :=
  ⟨D.hc.lift (pT t S' ≫ x.1) (tb t S') (by rw [Category.assoc, x.2]; exact pullback.condition),
    D.hc.lift_snd _ _ _⟩

@[scoped simp] theorem bc_c (x : SchemeHomOver t D.f) : (D.bc t x).1 ≫ D.c = pT t S' ≫ x.1 :=
  D.hc.lift_fst _ _ _

theorem bc_eq {x : SchemeHomOver t D.f} {y : SchemeHomOver (tb t S') D.f'}
    (h : y.1 ≫ D.c = pT t S' ≫ x.1) : D.bc t x = y :=
  Subtype.ext (D.hc.hom_ext (by rw [bc_c, h]) (by rw [(D.bc t x).2, y.2]))

def lift₁ (x : SchemeHomOver t D.f) : SchemeHomOver (tbb t S') D.f'' :=
  ⟨D.ha₁.lift (q₁ t S' ≫ (D.bc t x).1) (tbb t S')
      (by rw [Category.assoc, (D.bc t x).2, q₁_tb]),
    D.ha₁.lift_snd _ _ _⟩

theorem toA₁_lift₁ (x : SchemeHomOver t D.f) :
    D.toA₁ (tbb t S') (D.lift₁ t x) = GoodReductionJacobian.schemeHomOverComp (q₁ t S') (q₁_tb t) (D.bc t x) :=
  Subtype.ext (D.ha₁.lift_fst _ _ _)

theorem toA₂_lift₁ (x : SchemeHomOver t D.f) :
    D.toA₂ (tbb t S') (D.lift₁ t x) = GoodReductionJacobian.schemeHomOverComp (q₂ t S') (q₂_tb t) (D.bc t x) := by
  apply Subtype.ext
  apply D.hc.hom_ext
  · show ((D.lift₁ t x).1 ≫ D.a₂) ≫ D.c = (q₂ t S' ≫ (D.bc t x).1) ≫ D.c
    have hl : (D.lift₁ t x).1 ≫ D.a₁ = q₁ t S' ≫ (D.bc t x).1 := D.ha₁.lift_fst _ _ _
    rw [Category.assoc, ← D.hca, ← Category.assoc, hl, Category.assoc, bc_c,
      Category.assoc, bc_c, ← Category.assoc, ← Category.assoc, q_pT]
  · show ((D.lift₁ t x).1 ≫ D.a₂) ≫ D.f' = (q₂ t S' ≫ (D.bc t x).1) ≫ D.f'
    rw [Category.assoc, D.ha₂.w, ← Category.assoc, (D.lift₁ t x).2, Category.assoc, (D.bc t x).2,
      q₂_tb]

def mul' (x y : SchemeHomOver t D.f) : Tb t S' ⟶ D.X := (D.L'.mul (tb t S') (D.bc t x) (D.bc t y)).1 ≫ D.c

theorem q_mul' (x y : SchemeHomOver t D.f) : q₁ t S' ≫ D.mul' t x y = q₂ t S' ≫ D.mul' t x y := by
  have h1 : q₁ t S' ≫ (D.L'.mul (tb t S') (D.bc t x) (D.bc t y)).1 =
      (D.L'.mul (tbb t S' ≫ ι₁ S S') (D.toA₁ _ (D.lift₁ t x)) (D.toA₁ _ (D.lift₁ t y))).1 := by
    rw [toA₁_lift₁, toA₁_lift₁, ← D.L'.mul_natural (tb t S') _ (q₁ t S') (q₁_tb t)]
    rfl
  have h2 : q₂ t S' ≫ (D.L'.mul (tb t S') (D.bc t x) (D.bc t y)).1 =
      (D.L'.mul (tbb t S' ≫ ι₂ S S') (D.toA₂ _ (D.lift₁ t x)) (D.toA₂ _ (D.lift₁ t y))).1 := by
    rw [toA₂_lift₁, toA₂_lift₁, ← D.L'.mul_natural (tb t S') _ (q₂ t S') (q₂_tb t)]
    rfl
  rw [mul', ← Category.assoc, h1, ← toA₁_mul, toA₁_coe, Category.assoc, D.hca, ← Category.assoc,
    ← toA₂_coe, toA₂_mul, ← h2, Category.assoc]

theorem q_one' : q₁ t S' ≫ ((D.L'.one (tb t S')).1 ≫ D.c) = q₂ t S' ≫ ((D.L'.one (tb t S')).1 ≫ D.c) := by
  have h1 : q₁ t S' ≫ (D.L'.one (tb t S')).1 = (D.L'.one (tbb t S' ≫ ι₁ S S')).1 :=
    congrArg Subtype.val (D.L'.one_natural (tb t S') _ (q₁ t S') (q₁_tb t))
  have h2 : q₂ t S' ≫ (D.L'.one (tb t S')).1 = (D.L'.one (tbb t S' ≫ ι₂ S S')).1 :=
    congrArg Subtype.val (D.L'.one_natural (tb t S') _ (q₂ t S') (q₂_tb t))
  rw [← Category.assoc, h1, ← toA₁_one, toA₁_coe, Category.assoc, D.hca, ← Category.assoc,
    ← toA₂_coe, toA₂_one, ← h2, Category.assoc]

theorem q_inv' (x : SchemeHomOver t D.f) :
    q₁ t S' ≫ ((D.L'.inv (tb t S') (D.bc t x)).1 ≫ D.c) =
      q₂ t S' ≫ ((D.L'.inv (tb t S') (D.bc t x)).1 ≫ D.c) := by
  have h1 : q₁ t S' ≫ (D.L'.inv (tb t S') (D.bc t x)).1 =
      (D.L'.inv (tbb t S' ≫ ι₁ S S') (D.toA₁ _ (D.lift₁ t x))).1 := by
    rw [toA₁_lift₁, ← inv_natural D.L' (tb t S') _ (q₁ t S') (q₁_tb t)]
    rfl
  have h2 : q₂ t S' ≫ (D.L'.inv (tb t S') (D.bc t x)).1 =
      (D.L'.inv (tbb t S' ≫ ι₂ S S') (D.toA₂ _ (D.lift₁ t x))).1 := by
    rw [toA₂_lift₁, ← inv_natural D.L' (tb t S') _ (q₂ t S') (q₂_tb t)]
    rfl
  rw [← Category.assoc, h1, ← toA₁_inv, toA₁_coe, Category.assoc, D.hca, ← Category.assoc,
    ← toA₂_coe, toA₂_inv, ← h2, Category.assoc]

variable [Module.FaithfullyFlat S S']

def mulD (x y : SchemeHomOver t D.f) : SchemeHomOver t D.f :=
  ⟨desc t (D.mul' t x y) (D.q_mul' t x y), by
    apply eq_of_pT_comp_eq t S'
    rw [← Category.assoc, pT_desc, mul', Category.assoc, D.hc.w, ← Category.assoc,
      (D.L'.mul _ _ _).2]
    exact pullback.condition.symm⟩

@[scoped simp] theorem pT_mulD (x y : SchemeHomOver t D.f) : pT t S' ≫ (D.mulD t x y).1 = D.mul' t x y :=
  pT_desc t (D.mul' t x y) (D.q_mul' t x y)

theorem bc_mulD (x y : SchemeHomOver t D.f) :
    D.bc t (D.mulD t x y) = D.L'.mul (tb t S') (D.bc t x) (D.bc t y) :=
  D.bc_eq t (by rw [pT_mulD]; rfl)

def oneD : SchemeHomOver t D.f :=
  ⟨desc t ((D.L'.one (tb t S')).1 ≫ D.c) (D.q_one' t), by
    apply eq_of_pT_comp_eq t S'
    rw [← Category.assoc, pT_desc, Category.assoc, D.hc.w, ← Category.assoc, (D.L'.one _).2]
    exact pullback.condition.symm⟩

@[scoped simp] theorem pT_oneD : pT t S' ≫ (D.oneD t).1 = (D.L'.one (tb t S')).1 ≫ D.c :=
  pT_desc t _ (D.q_one' t)

theorem bc_oneD : D.bc t (D.oneD t) = D.L'.one (tb t S') := D.bc_eq t (by rw [pT_oneD])

def invD (x : SchemeHomOver t D.f) : SchemeHomOver t D.f :=
  ⟨desc t ((D.L'.inv (tb t S') (D.bc t x)).1 ≫ D.c) (D.q_inv' t x), by
    apply eq_of_pT_comp_eq t S'
    rw [← Category.assoc, pT_desc, Category.assoc, D.hc.w, ← Category.assoc, (D.L'.inv _ _).2]
    exact pullback.condition.symm⟩

@[scoped simp] theorem pT_invD (x : SchemeHomOver t D.f) :
    pT t S' ≫ (D.invD t x).1 = (D.L'.inv (tb t S') (D.bc t x)).1 ≫ D.c :=
  pT_desc t _ (D.q_inv' t x)

theorem bc_invD (x : SchemeHomOver t D.f) : D.bc t (D.invD t x) = D.L'.inv (tb t S') (D.bc t x) :=
  D.bc_eq t (by rw [pT_invD])

end Test

end Datum
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat.P2mWs30RglDescent.Datum"

namespace Datum

variable {S : Type u} [CommRing S] {S' : Type u} [CommRing S'] [Algebra S S'] (D : Datum S S')
variable [Module.FaithfullyFlat S S']

section Axioms

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))

theorem mulD_assoc (x y z : SchemeHomOver t D.f) :
    D.mulD t (D.mulD t x y) z = D.mulD t x (D.mulD t y z) := by
  apply Subtype.ext
  apply eq_of_pT_comp_eq t S'
  rw [pT_mulD, pT_mulD, mul', mul', bc_mulD, bc_mulD, D.L'.mul_assoc]

theorem oneD_mulD (x : SchemeHomOver t D.f) : D.mulD t (D.oneD t) x = x := by
  apply Subtype.ext
  apply eq_of_pT_comp_eq t S'
  rw [pT_mulD, mul', bc_oneD, D.L'.one_mul, bc_c]

theorem mulD_oneD (x : SchemeHomOver t D.f) : D.mulD t x (D.oneD t) = x := by
  apply Subtype.ext
  apply eq_of_pT_comp_eq t S'
  rw [pT_mulD, mul', bc_oneD, D.L'.mul_one, bc_c]

theorem invD_mulD_cancel (x : SchemeHomOver t D.f) : D.mulD t (D.invD t x) x = D.oneD t := by
  apply Subtype.ext
  apply eq_of_pT_comp_eq t S'
  rw [pT_mulD, mul', bc_invD, D.L'.inv_mul_cancel, pT_oneD]

end Axioms
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat.P2mWs30RglDescent.Datum"

theorem mulD_natural {T T₂ : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t₂ : T₂ ⟶ Spec (CommRingCat.of S))
    (ψ : T₂ ⟶ T) (hψ : ψ ≫ t = t₂) (x y : SchemeHomOver t D.f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (D.mulD t x y) =
      D.mulD t₂ (GoodReductionJacobian.schemeHomOverComp ψ hψ x)
        (GoodReductionJacobian.schemeHomOverComp ψ hψ y) := by

  let ψ' : Tb t₂ S' ⟶ Tb t S' :=
    pullback.lift (pT t₂ S' ≫ ψ) (tb t₂ S') (by rw [Category.assoc, hψ]; exact pullback.condition)
  have hψ'₁ : ψ' ≫ pT t S' = pT t₂ S' ≫ ψ := pullback.lift_fst _ _ _
  have hψ'₂ : ψ' ≫ tb t S' = tb t₂ S' := pullback.lift_snd _ _ _
  have hbc : ∀ z : SchemeHomOver t D.f,
      D.bc t₂ (GoodReductionJacobian.schemeHomOverComp ψ hψ z) =
        GoodReductionJacobian.schemeHomOverComp ψ' hψ'₂ (D.bc t z) := by
    intro z
    apply D.bc_eq t₂
    show (ψ' ≫ (D.bc t z).1) ≫ D.c = pT t₂ S' ≫ (ψ ≫ z.1)
    rw [Category.assoc, bc_c, ← Category.assoc, hψ'₁, Category.assoc]
  apply Subtype.ext
  apply eq_of_pT_comp_eq t₂ S'
  show pT t₂ S' ≫ (ψ ≫ (D.mulD t x y).1) = pT t₂ S' ≫ (D.mulD t₂ _ _).1
  rw [pT_mulD, mul', hbc, hbc, ← D.L'.mul_natural (tb t S') (tb t₂ S') ψ' hψ'₂, ← Category.assoc,
    ← hψ'₁, Category.assoc, pT_mulD, mul']
  rfl

def law : RelativeGroupLaw S D.f where
  mul t x y := D.mulD t x y
  one t := D.oneD t
  inv t x := D.invD t x
  mul_assoc t x y z := D.mulD_assoc t x y z
  one_mul t x := D.oneD_mulD t x
  mul_one t x := D.mulD_oneD t x
  inv_mul_cancel t x := D.invD_mulD_cancel t x
  mul_natural t t' ψ hψ x y := D.mulD_natural t t' ψ hψ x y

theorem mul_c {T : Scheme.{u}} (t₁ : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t₁ D.f') :
    (D.L'.mul t₁ x y).1 ≫ D.c =
      (D.mulD (t₁ ≫ ιb S S')
        ⟨x.1 ≫ D.c, by rw [Category.assoc, D.hc.w, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ D.c, by rw [Category.assoc, D.hc.w, ← Category.assoc, y.2]⟩).1 := by
  set t : T ⟶ Spec (CommRingCat.of S) := t₁ ≫ ιb S S' with ht

  let sT : T ⟶ Tb t S' := pullback.lift (𝟙 T) t₁ (by rw [Category.id_comp])
  have hs₁ : sT ≫ pT t S' = 𝟙 T := pullback.lift_fst _ _ _
  have hs₂ : sT ≫ tb t S' = t₁ := pullback.lift_snd _ _ _
  have hsec : ∀ z : SchemeHomOver t₁ D.f',
      GoodReductionJacobian.schemeHomOverComp sT hs₂
        (D.bc t ⟨z.1 ≫ D.c, by rw [Category.assoc, D.hc.w, ← Category.assoc, z.2]⟩) = z := by
    intro z
    apply Subtype.ext
    apply D.hc.hom_ext
    · show (sT ≫ (D.bc t _).1) ≫ D.c = z.1 ≫ D.c
      rw [Category.assoc, bc_c, ← Category.assoc, hs₁, Category.id_comp]
    · show (sT ≫ (D.bc t _).1) ≫ D.f' = z.1 ≫ D.f'
      rw [Category.assoc, (D.bc t _).2, hs₂, z.2]
  have key : ∀ M : T ⟶ D.X, sT ≫ pT t S' ≫ M = M := fun M => by
    rw [← Category.assoc, hs₁, Category.id_comp]
  rw [← key (D.mulD t _ _).1, pT_mulD, mul', ← Category.assoc]
  congr 1
  have := congrArg Subtype.val
    (D.L'.mul_natural (tb t S') t₁ sT hs₂
      (D.bc t ⟨x.1 ≫ D.c, by rw [Category.assoc, D.hc.w, ← Category.assoc, x.2]⟩)
      (D.bc t ⟨y.1 ≫ D.c, by rw [Category.assoc, D.hc.w, ← Category.assoc, y.2]⟩))
  rw [hsec, hsec] at this
  exact this.symm

theorem law_isCommutative (h : D.L'.IsCommutative) : D.law.IsCommutative := by
  intro T t x y
  show D.mulD t x y = D.mulD t y x
  apply Subtype.ext
  apply eq_of_pT_comp_eq t S'
  rw [pT_mulD, pT_mulD, mul', mul', h.mul_comm]

end Datum
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat.P2mWs30RglDescent.Datum"

end P2mWs30RglDescent
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat.P2mWs30RglDescent.Datum P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat.P2mWs30RglDescent"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat.P2mWs30RglDescent.Datum P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat.P2mWs30RglDescent"

open P2mWs30RglDescent in
theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X A' A'' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (f' : A' ⟶ Spec (CommRingCat.of S'))
    (c : A' ⟶ X) (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (f'' : A'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (a₁ a₂ : A'' ⟶ A')
    (ha₁ : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hca : a₁ ≫ c = a₂ ≫ c)
    (L' : RelativeGroupLaw S' f') (L'' : RelativeGroupLaw (S' ⊗[S] S') f'')
    (ha₁mul : ∀ {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (x y : SchemeHomOver t'' f''),
      (L''.mul t'' x y).1 ≫ a₁ =
        (L'.mul (t'' ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom))
          ⟨x.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, y.2]⟩).1)
    (ha₂mul : ∀ {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (x y : SchemeHomOver t'' f''),
      (L''.mul t'' x y).1 ≫ a₂ =
        (L'.mul (t'' ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom))
          ⟨x.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, y.2]⟩).1) :
    ∃ L : RelativeGroupLaw S f,
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' f'),
        (L'.mul t' x y).1 ≫ c =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
            ⟨x.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, y.2]⟩).1) ∧
      (L'.IsCommutative → L.IsCommutative) := by
  let D : P2mWs30RglDescent.Datum S S' :=
    { X := X, A' := A', A'' := A'', f := f, f' := f', c := c, hc := hc, f'' := f'', a₁ := a₁, a₂ := a₂,
      ha₁ := ha₁, ha₂ := ha₂, hca := hca, L' := L', L'' := L'',
      ha₁mul := fun t'' x y => ha₁mul t'' x y, ha₂mul := fun t'' x y => ha₂mul t'' x y }
  refine ⟨D.law, fun t' x y => ?_, fun h => D.law_isCommutative h⟩
  exact D.mul_c t' x y

end S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat (solution)
