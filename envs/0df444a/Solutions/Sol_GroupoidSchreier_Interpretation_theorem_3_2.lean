-- Prove2me | solution 1 for GroupoidSchreier.Interpretation.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:21:27.101993+00:00
-- url     : https://prove2.me/submissions/1eadde31-1f85-45d0-b6f7-89ef3577cdaf

import Mathlib
import Definitions.Def_GroupoidSchreier_Interpretation_WeakAction
import Definitions.Def_GroupoidSchreier_Interpretation_Extension

namespace GroupoidSchreier.Interpretation
open CategoryTheory
universe u
set_option linter.unusedSimpArgs false

namespace Extension
variable {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)] (E : Extension G K)

theorem inv_comp_assoc {A B Z : G} (f : E.Hom A B) (x : E.Hom Z A) :
    E.comp (E.inv f) (E.comp f x) = x := by
  rw [← E.assoc, E.inv_comp, E.id_comp]

theorem comp_inv_assoc {A B Z : G} (f : E.Hom A B) (x : E.Hom Z B) :
    E.comp f (E.comp (E.inv f) x) = x := by
  rw [← E.assoc, E.comp_inv, E.id_comp]

theorem inv_id (A : G) : E.inv (E.id A) = E.id A := by
  have := E.inv_comp (E.id A)
  rwa [E.comp_id] at this

theorem eq_inv_of_comp {A B : G} {g : E.Hom B A} {f : E.Hom A B} (h : E.comp g f = E.id A) :
    g = E.inv f := by
  calc g = E.comp g (E.id B) := (E.comp_id g).symm
    _ = E.comp g (E.comp f (E.inv f)) := by rw [E.comp_inv]
    _ = E.comp (E.comp g f) (E.inv f) := (E.assoc _ _ _).symm
    _ = E.inv f := by rw [h, E.id_comp]

theorem comp_cancel_right {A B C : G} {x y : E.Hom B C} {s : E.Hom A B}
    (h : E.comp x s = E.comp y s) : x = y := by
  have := congrArg (fun z => E.comp z (E.inv s)) h
  simpa [E.assoc, E.comp_inv, E.comp_id] using this

theorem comp_cancel_left {A B C : G} {x y : E.Hom A B} {s : E.Hom B C}
    (h : E.comp s x = E.comp s y) : x = y := by
  have := congrArg (fun z => E.comp (E.inv s) z) h
  simpa [E.inv_comp_assoc] using this

theorem ι_one (A : G) : E.ι A 1 = E.id A := by
  have h := E.ι_mul A 1 1
  rw [one_mul] at h
  have : E.comp (E.ι A 1) (E.ι A 1) = E.comp (E.id A) (E.ι A 1) := by
    rw [← h, E.id_comp]
  exact E.comp_cancel_right this

theorem P_ι {A : G} (k : K A) : E.P (E.ι A k) = 𝟙 A := (E.ι_range A _).2 ⟨k, rfl⟩

theorem P_inv {A B : G} (f : E.Hom A B) : E.P (E.inv f) = CategoryTheory.inv (E.P f) := by
  have := E.P_comp (E.inv f) f
  rw [E.inv_comp, E.P_id] at this
  exact IsIso.eq_inv_of_hom_inv_id this.symm

theorem P_conj {A B : G} (f : E.Hom A B) (x : E.Hom A A) (hx : E.P x = 𝟙 A) :
    E.P (E.comp f (E.comp x (E.inv f))) = 𝟙 B := by
  simp [E.P_comp, E.P_inv, hx]

theorem P_conj' {A B : G} (f : E.Hom A B) (x : E.Hom B B) (hx : E.P x = 𝟙 B) :
    E.P (E.comp (E.inv f) (E.comp x f)) = 𝟙 A := by
  simp [E.P_comp, E.P_inv, hx]

/-- the fiber element -/
noncomputable def fib {A : G} (e : E.Hom A A) (h : E.P e = 𝟙 A) : K A :=
  Classical.choose ((E.ι_range A e).1 h)

theorem ι_fib {A : G} (e : E.Hom A A) (h : E.P e = 𝟙 A) : E.ι A (E.fib e h) = e :=
  Classical.choose_spec ((E.ι_range A e).1 h)

theorem fib_eq {A : G} {e : E.Hom A A} (h : E.P e = 𝟙 A) {x : K A} (hx : E.ι A x = e) :
    E.fib e h = x := E.ι_injective A (by rw [ι_fib, hx])

theorem eq_comp_inv_of {A B C : G} {a : E.Hom B C} {b : E.Hom A B} {c : E.Hom A C}
    (h : E.comp a b = c) : a = E.comp c (E.inv b) := by
  rw [← h]; simp [E.assoc, E.comp_inv, E.comp_id]


theorem eq_conj_of {A B : G} {x : E.Hom B B} {f : E.Hom A B} {y : E.Hom A A}
    (h : E.comp x f = E.comp f y) : x = E.comp f (E.comp y (E.inv f)) := by
  rw [← E.assoc]; exact E.eq_comp_inv_of h

section Sec
variable (s : ∀ ⦃A B : G⦄, (A ⟶ B) → E.Hom A B)

noncomputable def secF {A B : G} (u : A ⟶ B) : K A ≃* K B where
  toFun k := E.fib (E.comp (s u) (E.comp (E.ι A k) (E.inv (s u)))) (E.P_conj _ _ (E.P_ι _))
  invFun k := E.fib (E.comp (E.inv (s u)) (E.comp (E.ι B k) (s u))) (E.P_conj' _ _ (E.P_ι _))
  left_inv k := by
    apply E.ι_injective
    rw [ι_fib]
    simp [ι_fib, E.assoc, E.inv_comp, E.comp_inv, E.inv_comp_assoc, E.comp_inv_assoc, E.id_comp, E.comp_id]
  right_inv k := by
    apply E.ι_injective
    rw [ι_fib]
    simp [ι_fib, E.assoc, E.inv_comp, E.comp_inv, E.inv_comp_assoc, E.comp_inv_assoc, E.id_comp, E.comp_id]
  map_mul' x y := by
    apply E.ι_injective
    simp only [ι_fib, E.ι_mul]
    simp [ι_fib, E.assoc, E.inv_comp, E.comp_inv, E.inv_comp_assoc, E.comp_inv_assoc, E.id_comp, E.comp_id]

theorem ι_secF {A B : G} (u : A ⟶ B) (k : K A) :
    E.ι B (E.secF s u k) = E.comp (s u) (E.comp (E.ι A k) (E.inv (s u))) :=
  E.ι_fib _ (E.P_conj _ _ (E.P_ι _))

noncomputable def secσ (hs : ∀ ⦃A B : G⦄ (u : A ⟶ B), E.P (s u) = u) {A B C : G}
    (u : A ⟶ B) (v : B ⟶ C) : K C :=
  E.fib (E.comp (s v) (E.comp (s u) (E.inv (s (u ≫ v))))) (by simp [E.P_comp, E.P_inv, hs])

theorem ι_secσ (hs : ∀ ⦃A B : G⦄ (u : A ⟶ B), E.P (s u) = u) {A B C : G}
    (u : A ⟶ B) (v : B ⟶ C) :
    E.ι C (E.secσ s hs u v) = E.comp (s v) (E.comp (s u) (E.inv (s (u ≫ v)))) :=
  E.ι_fib _ _

noncomputable def ofSection (hs : IsNormalizedSection E s) : WeakAction G K where
  F := fun {A B} u => E.secF s u
  σ := fun {A B C} u v => E.secσ s hs.1 u v
  map_id A x := by
    apply E.ι_injective
    simp [ι_secF, hs.2, E.inv_id, E.id_comp, E.comp_id]
  σ_id A := by
    apply E.ι_injective
    simp [ι_secσ, hs.2, E.inv_id, E.id_comp, E.comp_id, E.ι_one]
  conj u v x := by
    apply E.ι_injective
    simp only [E.ι_mul, ι_secF, ι_secσ]
    simp [ι_fib, E.assoc, E.inv_comp, E.comp_inv, E.inv_comp_assoc, E.comp_inv_assoc, E.id_comp, E.comp_id]
  cocycle u v w := by
    apply E.ι_injective
    simp only [E.ι_mul, ι_secF, ι_secσ]
    simp [ι_fib, E.assoc, E.inv_comp, E.comp_inv, E.inv_comp_assoc, E.comp_inv_assoc, E.id_comp, E.comp_id]

theorem fiberVia_ofSection (hs : IsNormalizedSection E s) :
    FiberVia E s (E.ofSection s hs) :=
  ⟨by intro A B u k; exact E.ι_secF s u k, by intro A B C u v; exact E.ι_secσ s hs.1 u v⟩

end Sec

theorem exists_section : ∃ s : ∀ ⦃A B : G⦄, (A ⟶ B) → E.Hom A B, IsNormalizedSection E s := by
  classical
  refine ⟨fun A B u => if h : ∃ hAB : A = B, HEq u (𝟙 A) then
      (Eq.rec (motive := fun B _ => E.Hom A B) (E.id A) h.choose)
    else Classical.choose (E.P_surj u), ?_, ?_⟩
  · intro A B u
    by_cases h : ∃ hAB : A = B, HEq u (𝟙 A)
    · obtain ⟨hAB, hu⟩ := h
      subst hAB
      have hu' := eq_of_heq hu
      subst hu'
      have hex : ∃ hAB : A = A, HEq (𝟙 A) (𝟙 A) := ⟨rfl, HEq.rfl⟩
      beta_reduce
      rw [dif_pos hex]
      exact E.P_id A
    · simp only [dif_neg h]
      exact Classical.choose_spec (E.P_surj u)
  · intro A
    have hex : ∃ hAB : A = A, HEq (𝟙 A) (𝟙 A) := ⟨rfl, HEq.rfl⟩
    beta_reduce
    rw [dif_pos hex]

end Extension

namespace WeakAction
variable {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)] (F : WeakAction G K)

theorem σ_id_left {A B : G} (w : A ⟶ B) : F.σ (𝟙 A) w = 1 := by
  have h := F.cocycle (𝟙 A) (𝟙 A) w
  simp only [Category.id_comp, F.σ_id, map_one, one_mul] at h
  have h2 : F.σ (𝟙 A) w * F.σ (𝟙 A) w = F.σ (𝟙 A) w * 1 := by rw [mul_one]; exact h
  exact mul_left_cancel h2

theorem σ_id_right {A B : G} (u : A ⟶ B) : F.σ u (𝟙 B) = 1 := by
  have h := F.cocycle u (𝟙 B) (𝟙 B)
  simp only [Category.id_comp, Category.comp_id, F.σ_id, F.map_id, one_mul] at h
  have h2 : F.σ u (𝟙 B) * F.σ u (𝟙 B) = F.σ u (𝟙 B) * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel h2

theorem twistedComp_assoc {A B C D : G} (h : (C ⟶ D) × K D) (g : (B ⟶ C) × K C)
    (f : (A ⟶ B) × K B) :
    twistedComp F (twistedComp F h g) f = twistedComp F h (twistedComp F g f) := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨g1, g2⟩ := g
  obtain ⟨f1, f2⟩ := f
  simp only [twistedComp, Prod.mk.injEq, Category.assoc, true_and, map_mul]
  have c1 := F.cocycle f1 g1 h1
  have c2 := F.conj g1 h1 f2
  calc h2 * F.F h1 g2 * F.σ g1 h1 * F.F (g1 ≫ h1) f2 * F.σ f1 (g1 ≫ h1)
      = h2 * F.F h1 g2 * (F.σ g1 h1 * F.F (g1 ≫ h1) f2) * F.σ f1 (g1 ≫ h1) := by
        simp only [mul_assoc]
    _ = h2 * F.F h1 g2 * (F.F h1 (F.F g1 f2) * F.σ g1 h1) * F.σ f1 (g1 ≫ h1) := by rw [c2]
    _ = h2 * F.F h1 g2 * F.F h1 (F.F g1 f2) * (F.σ g1 h1 * F.σ f1 (g1 ≫ h1)) := by
        simp only [mul_assoc]
    _ = h2 * F.F h1 g2 * F.F h1 (F.F g1 f2) * (F.F h1 (F.σ f1 g1) * F.σ (f1 ≫ g1) h1) := by
        rw [c1]
    _ = _ := by simp only [mul_assoc]

theorem twistedComp_id_left {A B : G} (f : (A ⟶ B) × K B) :
    twistedComp F (𝟙 B, (1 : K B)) f = f := by
  obtain ⟨f1, f2⟩ := f
  simp [twistedComp, F.map_id, F.σ_id_right]

theorem twistedComp_id_right {A B : G} (f : (A ⟶ B) × K B) :
    twistedComp F f (𝟙 A, (1 : K A)) = f := by
  obtain ⟨f1, f2⟩ := f
  simp [twistedComp, F.σ_id_left]

/-- left inverse -/
noncomputable def twInv {A B : G} (f : (A ⟶ B) × K B) : (B ⟶ A) × K A :=
  (CategoryTheory.inv f.1, (F.F (CategoryTheory.inv f.1) f.2 * F.σ f.1 (CategoryTheory.inv f.1))⁻¹)

theorem twInv_comp {A B : G} (f : (A ⟶ B) × K B) :
    twistedComp F (F.twInv f) f = (𝟙 A, (1 : K A)) := by
  obtain ⟨f1, f2⟩ := f
  simp [twistedComp, twInv]

theorem twComp_inv {A B : G} (f : (A ⟶ B) × K B) :
    twistedComp F f (F.twInv f) = (𝟙 B, (1 : K B)) := by
  set g := F.twInv f with hg
  set h := F.twInv g with hh
  have h1 : twistedComp F g f = (𝟙 A, (1 : K A)) := F.twInv_comp f
  have h2 : twistedComp F h g = (𝟙 B, (1 : K B)) := F.twInv_comp g
  calc twistedComp F f g = twistedComp F (𝟙 B, (1 : K B)) (twistedComp F f g) :=
        (F.twistedComp_id_left _).symm
    _ = twistedComp F (twistedComp F h g) (twistedComp F f g) := by rw [h2]
    _ = twistedComp F h (twistedComp F g (twistedComp F f g)) := F.twistedComp_assoc _ _ _
    _ = twistedComp F h (twistedComp F (twistedComp F g f) g) := by
        rw [F.twistedComp_assoc]
    _ = twistedComp F h g := by rw [h1, F.twistedComp_id_left]
    _ = _ := h2

/-- the twisted product extension -/
noncomputable def tw : Extension G K where
  Hom A B := (A ⟶ B) × K B
  id A := (𝟙 A, 1)
  comp g f := twistedComp F g f
  inv f := F.twInv f
  id_comp f := F.twistedComp_id_left f
  comp_id f := F.twistedComp_id_right f
  assoc h g f := F.twistedComp_assoc h g f
  inv_comp f := F.twInv_comp f
  comp_inv f := F.twComp_inv f
  P f := f.1
  P_id A := rfl
  P_comp g f := rfl
  P_surj u := ⟨(u, 1), rfl⟩
  ι A k := (𝟙 A, k)
  ι_mul A x y := by simp [twistedComp, F.map_id, F.σ_id]
  ι_injective A x y h := by simpa using h
  ι_range A e := by
    constructor
    · intro h
      exact ⟨e.2, Prod.ext h.symm rfl⟩
    · rintro ⟨k, rfl⟩
      rfl

/-- the canonical section of the twisted product -/
def twSec : ∀ ⦃A B : G⦄, (A ⟶ B) → (F.tw).Hom A B := fun _ _ u => (u, 1)

theorem twSec_normalized : IsNormalizedSection F.tw F.twSec :=
  ⟨fun _ _ _ => rfl, fun _ => rfl⟩

theorem twSec_fiber : FiberVia F.tw F.twSec F := by
  constructor
  · intro A B u k
    apply F.tw.eq_conj_of
    show twistedComp F (𝟙 B, F.F u k) (u, 1) = twistedComp F (u, 1) (𝟙 A, k)
    simp [twistedComp, F.σ_id_left, F.σ_id_right]
  · intro A B C u v
    rw [← F.tw.assoc]
    apply F.tw.eq_comp_inv_of
    show twistedComp F (𝟙 C, F.σ u v) (u ≫ v, 1) = twistedComp F (v, 1) (u, 1)
    simp [twistedComp, F.σ_id_left, F.σ_id_right]

end WeakAction

namespace Extension
variable {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)] (E : Extension G K)
variable {s : ∀ ⦃A B : G⦄, (A ⟶ B) → E.Hom A B} {F : WeakAction G K}

theorem fv_conj (h : FiberVia E s F) {A B : G} (u : A ⟶ B) (k : K A) :
    E.comp (E.ι B (F.F u k)) (s u) = E.comp (s u) (E.ι A k) := by
  rw [h.1 u k]
  simp [E.assoc, E.inv_comp, E.comp_inv, E.inv_comp_assoc, E.comp_inv_assoc, E.id_comp, E.comp_id]

theorem fv_σ (h : FiberVia E s F) {A B C : G} (u : A ⟶ B) (v : B ⟶ C) :
    E.comp (E.ι C (F.σ u v)) (s (u ≫ v)) = E.comp (s v) (s u) := by
  rw [h.2 u v]
  simp [E.assoc, E.inv_comp, E.comp_inv, E.inv_comp_assoc, E.comp_inv_assoc, E.id_comp, E.comp_id]

theorem comp_decomp (h : FiberVia E s F) {A B C : G} (u : A ⟶ B) (u' : B ⟶ C) (k : K B)
    (k' : K C) :
    E.comp (E.comp (E.ι C k') (s u')) (E.comp (E.ι B k) (s u)) =
      E.comp (E.ι C (k' * F.F u' k * F.σ u u')) (s (u ≫ u')) := by
  have c1 := E.fv_conj h u' k
  have c2 := E.fv_σ h u u'
  rw [E.ι_mul, E.ι_mul]
  calc E.comp (E.comp (E.ι C k') (s u')) (E.comp (E.ι B k) (s u))
      = E.comp (E.ι C k') (E.comp (E.comp (s u') (E.ι B k)) (s u)) := by simp [E.assoc]
    _ = E.comp (E.ι C k') (E.comp (E.comp (E.ι C (F.F u' k)) (s u')) (s u)) := by rw [c1]
    _ = E.comp (E.ι C k') (E.comp (E.ι C (F.F u' k)) (E.comp (s u') (s u))) := by
        simp [E.assoc]
    _ = E.comp (E.ι C k') (E.comp (E.ι C (F.F u' k))
          (E.comp (E.ι C (F.σ u u')) (s (u ≫ u')))) := by rw [c2]
    _ = _ := by simp [E.assoc]

theorem P_decomp (hs : ∀ ⦃A B : G⦄ (u : A ⟶ B), E.P (s u) = u) {A B : G} (u : A ⟶ B) (k : K B) :
    E.P (E.comp (E.ι B k) (s u)) = u := by
  rw [E.P_comp, hs, E.P_ι, Category.comp_id]

/-- the fiber part of an arrow w.r.t. a section -/
noncomputable def kOf (hs : ∀ ⦃A B : G⦄ (u : A ⟶ B), E.P (s u) = u) {A B : G} (e : E.Hom A B) :
    K B :=
  E.fib (E.comp e (E.inv (s (E.P e)))) (by
    simp [E.P_comp, E.P_inv, hs])

theorem decomp (hs : ∀ ⦃A B : G⦄ (u : A ⟶ B), E.P (s u) = u) {A B : G} (e : E.Hom A B) :
    e = E.comp (E.ι B (E.kOf hs e)) (s (E.P e)) := by
  unfold kOf
  rw [ι_fib]
  simp [E.assoc, E.inv_comp, E.comp_inv, E.inv_comp_assoc, E.comp_inv_assoc, E.id_comp, E.comp_id]

theorem kOf_eq (hs : ∀ ⦃A B : G⦄ (u : A ⟶ B), E.P (s u) = u) {A B : G} (u : A ⟶ B) (k : K B) :
    E.kOf hs (E.comp (E.ι B k) (s u)) = k := by
  unfold kOf
  apply E.fib_eq
  rw [E.P_decomp hs]
  simp [E.assoc, E.inv_comp, E.comp_inv, E.inv_comp_assoc, E.comp_inv_assoc, E.id_comp, E.comp_id]

end Extension

namespace Part3
variable {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
variable {E₁ E₂ : Extension G K}
variable {s₁ : ∀ ⦃A B : G⦄, (A ⟶ B) → E₁.Hom A B} {s₂ : ∀ ⦃A B : G⦄, (A ⟶ B) → E₂.Hom A B}
variable {F₁ F₂ : WeakAction G K}

theorem extHom_ext (Γ Γ' : ExtHom E₁ E₂) (h : ∀ {A B : G} (e : E₁.Hom A B), Γ.map e = Γ'.map e) :
    Γ = Γ' := by
  obtain ⟨m, a, b, c, d⟩ := Γ
  obtain ⟨m', a', b', c', d'⟩ := Γ'
  have : @m = @m' := by
    funext A B e
    exact h e
  subst this
  rfl

theorem actHom_ext (T T' : ActHom F₁ F₂) (h : ∀ {A B : G} (u : A ⟶ B), T.τ u = T'.τ u) :
    T = T' := by
  obtain ⟨m, a, b, c⟩ := T
  obtain ⟨m', a', b', c'⟩ := T'
  have : @m = @m' := by
    funext A B e
    exact h e
  subst this
  rfl

theorem extHom_map_inv (Γ : ExtHom E₁ E₂) {A B : G} (f : E₁.Hom A B) :
    Γ.map (E₁.inv f) = E₂.inv (Γ.map f) :=
  E₂.eq_inv_of_comp (by rw [← Γ.map_comp, E₁.inv_comp, Γ.map_id])

noncomputable def θ (hs₁ : IsNormalizedSection E₁ s₁) (hs₂ : IsNormalizedSection E₂ s₂)
    (Γ : ExtHom E₁ E₂) {A B : G} (u : A ⟶ B) : K B :=
  E₂.fib (E₂.comp (Γ.map (s₁ u)) (E₂.inv (s₂ u)))
    (by simp [E₂.P_comp, E₂.P_inv, Γ.map_P, hs₁.1, hs₂.1])

theorem map_s (hs₁ : IsNormalizedSection E₁ s₁) (hs₂ : IsNormalizedSection E₂ s₂)
    (Γ : ExtHom E₁ E₂) {A B : G} (u : A ⟶ B) :
    Γ.map (s₁ u) = E₂.comp (E₂.ι B (θ hs₁ hs₂ Γ u)) (s₂ u) := by
  unfold θ
  rw [E₂.ι_fib]
  simp [E₂.assoc, E₂.inv_comp, E₂.comp_inv, E₂.inv_comp_assoc, E₂.comp_inv_assoc, E₂.id_comp,
    E₂.comp_id]

theorem θ_nat (hs₁ : IsNormalizedSection E₁ s₁) (hs₂ : IsNormalizedSection E₂ s₂)
    (h₁ : FiberVia E₁ s₁ F₁) (h₂ : FiberVia E₂ s₂ F₂)
    (Γ : ExtHom E₁ E₂) {A B : G} (u : A ⟶ B) (k : K A) :
    F₁.F u k * θ hs₁ hs₂ Γ u = θ hs₁ hs₂ Γ u * F₂.F u k := by
  apply E₂.ι_injective
  rw [E₂.ι_mul, E₂.ι_mul]
  apply E₂.comp_cancel_right (s := s₂ u)
  have c1 := E₁.fv_conj h₁ u k
  have c2 := E₂.fv_conj h₂ u k
  have c3 := congrArg Γ.map c1
  rw [Γ.map_comp, Γ.map_comp, Γ.fiber, Γ.fiber, map_s hs₁ hs₂ Γ u] at c3
  calc E₂.comp (E₂.comp (E₂.ι B (F₁.F u k)) (E₂.ι B (θ hs₁ hs₂ Γ u))) (s₂ u)
      = E₂.comp (E₂.ι B (F₁.F u k)) (E₂.comp (E₂.ι B (θ hs₁ hs₂ Γ u)) (s₂ u)) := E₂.assoc _ _ _
    _ = E₂.comp (E₂.comp (E₂.ι B (θ hs₁ hs₂ Γ u)) (s₂ u)) (E₂.ι A k) := c3
    _ = E₂.comp (E₂.ι B (θ hs₁ hs₂ Γ u)) (E₂.comp (s₂ u) (E₂.ι A k)) := E₂.assoc _ _ _
    _ = E₂.comp (E₂.ι B (θ hs₁ hs₂ Γ u)) (E₂.comp (E₂.ι B (F₂.F u k)) (s₂ u)) := by rw [c2]
    _ = _ := (E₂.assoc _ _ _).symm

theorem θ_one (hs₁ : IsNormalizedSection E₁ s₁) (hs₂ : IsNormalizedSection E₂ s₂)
    (Γ : ExtHom E₁ E₂) (A : G) : θ hs₁ hs₂ Γ (𝟙 A) = 1 := by
  apply E₂.fib_eq
  simp [hs₁.2, hs₂.2, Γ.map_id, E₂.inv_id, E₂.ι_one, E₂.comp_id]

theorem θ_coh (hs₁ : IsNormalizedSection E₁ s₁) (hs₂ : IsNormalizedSection E₂ s₂)
    (h₁ : FiberVia E₁ s₁ F₁) (h₂ : FiberVia E₂ s₂ F₂)
    (Γ : ExtHom E₁ E₂) {A B C : G} (u : A ⟶ B) (v : B ⟶ C) :
    θ hs₁ hs₂ Γ v * F₂.F v (θ hs₁ hs₂ Γ u) * F₂.σ u v =
      F₁.σ u v * θ hs₁ hs₂ Γ (u ≫ v) := by
  apply E₂.ι_injective
  simp only [E₂.ι_mul]
  apply E₂.comp_cancel_right (s := s₂ (u ≫ v))
  have c1 := E₂.fv_conj h₂ v (θ hs₁ hs₂ Γ u)
  have c2 := E₂.fv_σ h₂ u v
  have c3 := congrArg Γ.map (E₁.fv_σ h₁ u v)
  rw [Γ.map_comp, Γ.map_comp, Γ.fiber, map_s hs₁ hs₂ Γ (u ≫ v), map_s hs₁ hs₂ Γ u,
    map_s hs₁ hs₂ Γ v] at c3
  calc E₂.comp (E₂.comp (E₂.comp (E₂.ι C (θ hs₁ hs₂ Γ v))
        (E₂.ι C (F₂.F v (θ hs₁ hs₂ Γ u)))) (E₂.ι C (F₂.σ u v))) (s₂ (u ≫ v))
      = E₂.comp (E₂.ι C (θ hs₁ hs₂ Γ v)) (E₂.comp (E₂.ι C (F₂.F v (θ hs₁ hs₂ Γ u)))
          (E₂.comp (E₂.ι C (F₂.σ u v)) (s₂ (u ≫ v)))) := by simp [E₂.assoc]
    _ = E₂.comp (E₂.ι C (θ hs₁ hs₂ Γ v)) (E₂.comp (E₂.ι C (F₂.F v (θ hs₁ hs₂ Γ u)))
          (E₂.comp (s₂ v) (s₂ u))) := by rw [c2]
    _ = E₂.comp (E₂.ι C (θ hs₁ hs₂ Γ v)) (E₂.comp (E₂.comp (s₂ v) (E₂.ι B (θ hs₁ hs₂ Γ u)))
          (s₂ u)) := by rw [← c1]; simp [E₂.assoc]
    _ = E₂.comp (E₂.comp (E₂.ι C (θ hs₁ hs₂ Γ v)) (s₂ v))
          (E₂.comp (E₂.ι B (θ hs₁ hs₂ Γ u)) (s₂ u)) := by simp [E₂.assoc]
    _ = E₂.comp (E₂.ι C (F₁.σ u v)) (E₂.comp (E₂.ι C (θ hs₁ hs₂ Γ (u ≫ v))) (s₂ (u ≫ v))) := c3.symm
    _ = _ := by simp [E₂.assoc]

end Part3

namespace Part3
variable {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
variable {E₁ E₂ : Extension G K}
variable {s₁ : ∀ ⦃A B : G⦄, (A ⟶ B) → E₁.Hom A B} {s₂ : ∀ ⦃A B : G⦄, (A ⟶ B) → E₂.Hom A B}
variable {F₁ F₂ : WeakAction G K}

noncomputable def toAct (hs₁ : IsNormalizedSection E₁ s₁) (hs₂ : IsNormalizedSection E₂ s₂)
    (h₁ : FiberVia E₁ s₁ F₁) (h₂ : FiberVia E₂ s₂ F₂) (Γ : ExtHom E₁ E₂) : ActHom F₁ F₂ where
  τ := fun {A B} u => (θ hs₁ hs₂ Γ u)⁻¹
  naturality := by
    intro A B u k
    have := θ_nat hs₁ hs₂ h₁ h₂ Γ u k
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
    exact this
  normalization := by
    intro A
    simp [θ_one hs₁ hs₂ Γ A]
  coherence := by
    intro A B C u v
    have R := θ_coh hs₁ hs₂ h₁ h₂ Γ u v
    have hσ : F₁.σ u v = θ hs₁ hs₂ Γ v * F₂.F v (θ hs₁ hs₂ Γ u) * F₂.σ u v *
        (θ hs₁ hs₂ Γ (u ≫ v))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]; exact R.symm
    rw [hσ, map_inv]
    group

noncomputable def ofActMap (s₂ : ∀ ⦃A B : G⦄, (A ⟶ B) → E₂.Hom A B)
    (hs₁ : IsNormalizedSection E₁ s₁) (T : ActHom F₁ F₂) {A B : G} (e : E₁.Hom A B) :
    E₂.Hom A B :=
  E₂.comp (E₂.ι B (E₁.kOf hs₁.1 e * (T.τ (E₁.P e))⁻¹)) (s₂ (E₁.P e))

theorem ofActMap_decomp (hs₁ : IsNormalizedSection E₁ s₁) (T : ActHom F₁ F₂)
    {A B : G} (u : A ⟶ B) (k : K B) :
    ofActMap s₂ hs₁ T (E₁.comp (E₁.ι B k) (s₁ u)) =
      E₂.comp (E₂.ι B (k * (T.τ u)⁻¹)) (s₂ u) := by
  unfold ofActMap
  rw [E₁.kOf_eq hs₁.1, E₁.P_decomp hs₁.1]

theorem ofActMap_comp (hs₁ : IsNormalizedSection E₁ s₁)
    (h₁ : FiberVia E₁ s₁ F₁) (h₂ : FiberVia E₂ s₂ F₂) (T : ActHom F₁ F₂)
    {A B C : G} (u : A ⟶ B) (u' : B ⟶ C) (k : K B) (k' : K C) :
    ofActMap s₂ hs₁ T (E₁.comp (E₁.comp (E₁.ι C k') (s₁ u')) (E₁.comp (E₁.ι B k) (s₁ u))) =
      E₂.comp (ofActMap s₂ hs₁ T (E₁.comp (E₁.ι C k') (s₁ u')))
        (ofActMap s₂ hs₁ T (E₁.comp (E₁.ι B k) (s₁ u))) := by
  rw [E₁.comp_decomp h₁, ofActMap_decomp hs₁, ofActMap_decomp hs₁, ofActMap_decomp hs₁,
    E₂.comp_decomp h₂]
  congr 2
  have n := T.naturality u' k
  have c := T.coherence u u'
  have e1 : F₁.F u' k = (T.τ u')⁻¹ * (F₂.F u' k * T.τ u') := by
    rw [eq_inv_mul_iff_mul_eq]; exact n
  have e2 : F₁.σ u u' = (F₂.F u' (T.τ u) * T.τ u')⁻¹ * (F₂.σ u u' * T.τ (u ≫ u')) := by
    rw [eq_inv_mul_iff_mul_eq]; exact c
  rw [e1, e2, map_mul, map_inv]
  group

noncomputable def ofAct (hs₁ : IsNormalizedSection E₁ s₁) (hs₂ : IsNormalizedSection E₂ s₂)
    (h₁ : FiberVia E₁ s₁ F₁) (h₂ : FiberVia E₂ s₂ F₂) (T : ActHom F₁ F₂) : ExtHom E₁ E₂ where
  map := fun {A B} e => ofActMap s₂ hs₁ T e
  map_id := by
    intro A
    have := ofActMap_decomp (s₂ := s₂) hs₁ T (𝟙 A) 1
    rw [E₁.ι_one, hs₁.2, E₁.comp_id] at this
    rw [this, T.normalization, hs₂.2]
    simp [E₂.ι_one, E₂.comp_id]
  map_comp := by
    intro A B C g f
    have key := ofActMap_comp (s₂ := s₂) hs₁ h₁ h₂ T (E₁.P f) (E₁.P g) (E₁.kOf hs₁.1 f)
      (E₁.kOf hs₁.1 g)
    rw [← E₁.decomp hs₁.1 g, ← E₁.decomp hs₁.1 f] at key
    exact key
  map_P := by
    intro A B e
    exact E₂.P_decomp hs₂.1 (E₁.P e) _
  fiber := by
    intro A k
    have := ofActMap_decomp (s₂ := s₂) hs₁ T (𝟙 A) k
    rw [hs₁.2, E₁.comp_id] at this
    show ofActMap s₂ hs₁ T (E₁.ι A k) = E₂.ι A k
    rw [this, T.normalization, hs₂.2]
    simp [E₂.comp_id]

end Part3

namespace Part3
variable {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)]
variable {E₁ E₂ : Extension G K}
variable {s₁ : ∀ ⦃A B : G⦄, (A ⟶ B) → E₁.Hom A B} {s₂ : ∀ ⦃A B : G⦄, (A ⟶ B) → E₂.Hom A B}
variable {F₁ F₂ : WeakAction G K}

noncomputable def extEquiv (hs₁ : IsNormalizedSection E₁ s₁) (hs₂ : IsNormalizedSection E₂ s₂)
    (h₁ : FiberVia E₁ s₁ F₁) (h₂ : FiberVia E₂ s₂ F₂) : ExtHom E₁ E₂ ≃ ActHom F₁ F₂ where
  toFun := toAct hs₁ hs₂ h₁ h₂
  invFun := ofAct hs₁ hs₂ h₁ h₂
  left_inv Γ := by
    apply extHom_ext
    intro A B e
    show ofActMap s₂ hs₁ (toAct hs₁ hs₂ h₁ h₂ Γ) e = Γ.map e
    have key : ∀ {A B : G} (u : A ⟶ B) (k : K B),
        ofActMap s₂ hs₁ (toAct hs₁ hs₂ h₁ h₂ Γ) (E₁.comp (E₁.ι B k) (s₁ u)) =
          Γ.map (E₁.comp (E₁.ι B k) (s₁ u)) := by
      intro A B u k
      rw [ofActMap_decomp hs₁, Γ.map_comp, Γ.fiber, map_s hs₁ hs₂ Γ u]
      show E₂.comp (E₂.ι B (k * ((θ hs₁ hs₂ Γ u)⁻¹)⁻¹)) (s₂ u) =
        E₂.comp (E₂.ι B k) (E₂.comp (E₂.ι B (θ hs₁ hs₂ Γ u)) (s₂ u))
      rw [inv_inv, E₂.ι_mul, E₂.assoc]
    have := key (E₁.P e) (E₁.kOf hs₁.1 e)
    rw [← E₁.decomp hs₁.1 e] at this
    exact this
  right_inv T := by
    apply actHom_ext
    intro A B u
    show (θ hs₁ hs₂ (ofAct hs₁ hs₂ h₁ h₂ T) u)⁻¹ = T.τ u
    have h1 := map_s hs₁ hs₂ (ofAct hs₁ hs₂ h₁ h₂ T) u
    have h2 : (ofAct hs₁ hs₂ h₁ h₂ T).map (s₁ u) = E₂.comp (E₂.ι B (T.τ u)⁻¹) (s₂ u) := by
      show ofActMap s₂ hs₁ T (s₁ u) = _
      have := ofActMap_decomp (s₂ := s₂) hs₁ T u 1
      rw [E₁.ι_one, E₁.id_comp, one_mul] at this
      exact this
    rw [h2] at h1
    have h3 := E₂.comp_cancel_right h1
    have h4 := E₂.ι_injective B h3
    rw [← h4, inv_inv]

theorem part3 (hs₁ : IsNormalizedSection E₁ s₁) (hs₂ : IsNormalizedSection E₂ s₂)
    (h₁ : FiberVia E₁ s₁ F₁) (h₂ : FiberVia E₂ s₂ F₂) :
    ∃ e : ExtHom E₁ E₂ ≃ ActHom F₁ F₂,
      ∀ (Γ : ExtHom E₁ E₂) {A B : G} (u : A ⟶ B),
        Γ.map (s₁ u) = E₂.comp (E₂.ι B ((e Γ).τ u)⁻¹) (s₂ u) := by
  refine ⟨extEquiv hs₁ hs₂ h₁ h₂, ?_⟩
  intro Γ A B u
  show _ = E₂.comp (E₂.ι B ((θ hs₁ hs₂ Γ u)⁻¹)⁻¹) (s₂ u)
  rw [inv_inv]
  exact map_s hs₁ hs₂ Γ u

end Part3

theorem theorem_3_2' {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)] :
    (∀ F : WeakAction G K, ∃ E : Extension G K, IsFiberAction E F) ∧
    (∀ E : Extension G K, ∃ F : WeakAction G K, IsFiberAction E F) ∧
    ∀ (E₁ E₂ : Extension G K)
      (s₁ : ∀ ⦃A B : G⦄, (A ⟶ B) → E₁.Hom A B) (s₂ : ∀ ⦃A B : G⦄, (A ⟶ B) → E₂.Hom A B)
      (F₁ F₂ : WeakAction G K),
      IsNormalizedSection E₁ s₁ → FiberVia E₁ s₁ F₁ →
      IsNormalizedSection E₂ s₂ → FiberVia E₂ s₂ F₂ →
      ∃ e : ExtHom E₁ E₂ ≃ ActHom F₁ F₂,
        ∀ (Γ : ExtHom E₁ E₂) {A B : G} (u : A ⟶ B),
          Γ.map (s₁ u) = E₂.comp (E₂.ι B ((e Γ).τ u)⁻¹) (s₂ u) := by
  refine ⟨?_, ?_, ?_⟩
  · intro F
    exact ⟨F.tw, F.twSec, F.twSec_normalized, F.twSec_fiber⟩
  · intro E
    obtain ⟨s, hs⟩ := E.exists_section
    exact ⟨E.ofSection s hs, s, hs, E.fiberVia_ofSection s hs⟩
  · intro E₁ E₂ s₁ s₂ F₁ F₂ hs₁ h₁ hs₂ h₂
    exact Part3.part3 hs₁ hs₂ h₁ h₂

end GroupoidSchreier.Interpretation

open GroupoidSchreier.Interpretation CategoryTheory
universe u
theorem solution {G : Type u} [Groupoid.{u} G] {K : G → Type u} [∀ A, Group (K A)] :
    (∀ F : WeakAction G K, ∃ E : Extension G K, IsFiberAction E F) ∧
    (∀ E : Extension G K, ∃ F : WeakAction G K, IsFiberAction E F) ∧
    ∀ (E₁ E₂ : Extension G K)
      (s₁ : ∀ ⦃A B : G⦄, (A ⟶ B) → E₁.Hom A B) (s₂ : ∀ ⦃A B : G⦄, (A ⟶ B) → E₂.Hom A B)
      (F₁ F₂ : WeakAction G K),
      IsNormalizedSection E₁ s₁ → FiberVia E₁ s₁ F₁ →
      IsNormalizedSection E₂ s₂ → FiberVia E₂ s₂ F₂ →
      ∃ e : ExtHom E₁ E₂ ≃ ActHom F₁ F₂,
        ∀ (Γ : ExtHom E₁ E₂) {A B : G} (u : A ⟶ B),
          Γ.map (s₁ u) = E₂.comp (E₂.ι B ((e Γ).τ u)⁻¹) (s₂ u) :=
  GroupoidSchreier.Interpretation.theorem_3_2'
