-- Prove2me | solution 1 for OAI.Grothendieck.elementary_expansion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T14:46:44.427769+00:00
-- url     : https://prove2.me/submissions/f9fd4502-c4dc-46fd-a54b-69dfb7ace49d

import Mathlib
import Definitions.Def_GrothendieckElementaryExpansion

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
alias Finset.prod_le_prod₀ := Finset.prod_le_prod
end OAICompat434

universe u v w

section
section
namespace OAI


namespace Grothendieck

namespace GlobularSet

theorem Joined.parallel {X : GlobularSet.{u}} {n : ℕ} {x y : X.Cell n}
    (h : X.Joined n x y) : X.Parallel n x y := by
  obtain ⟨h, rfl, rfl⟩ := h
  cases n with
  | zero => trivial
  | succ n => exact ⟨X.source_source n h, X.target_source n h⟩

theorem Hom.map_joined {X Y : GlobularSet.{u}} (f : Hom X Y) {n : ℕ}
    {x y : X.Cell n} (h : X.Joined n x y) : Y.Joined n (f.app n x) (f.app n y) := by
  obtain ⟨h, hs, ht⟩ := h
  exact ⟨f.app (n + 1) h, by rw [← f.source_app, hs], by rw [← f.target_app, ht]⟩

theorem Hom.map_parallel {X Y : GlobularSet.{u}} (f : Hom X Y) {n : ℕ}
    {x y : X.Cell n} (h : X.Parallel n x y) :
    Y.Parallel n (f.app n x) (f.app n y) := by
  cases n with
  | zero => trivial
  | succ n =>
    change _ = _ ∧ _ = _
    exact ⟨by rw [← f.source_app, ← f.source_app, h.1],
      by rw [← f.target_app, ← f.target_app, h.2]⟩

end GlobularSet

open CategoryTheory CategoryTheory.Limits Opposite

namespace Globe

namespace Face

@[simp]
theorem id_comp {m n} (f : Face m n) : comp (.id m) f = f := rfl

@[simp]
theorem comp_id {m n} (f : Face m n) : comp f (.id n) = f := by cases f <;> rfl

theorem assoc {a b c d} (f : Face a b) (g : Face b c) (h : Face c d) :
    comp (comp f g) h = comp f (comp g h) := by
  cases f <;> cases g <;> cases h <;> rfl

end Face

instance : Category Globe where
  Hom m n := Face m.dim n.dim
  id m := .id m.dim
  comp := Face.comp
  id_comp _ := rfl
  comp_id {X Y} f := by cases X; cases Y; cases f <;> rfl
  assoc {W X Y Z} f g h := by
    cases W; cases X; cases Y; cases Z
    cases f <;> cases g <;> cases h <;> rfl

@[simp]
theorem source_source (n) : source n ≫ source (n + 1) = source n ≫ target (n + 1) := rfl

@[simp]
theorem target_source (n) : target n ≫ source (n + 1) = target n ≫ target (n + 1) := rfl

end Globe

namespace GlobularPresheaf

end GlobularPresheaf

namespace Table

end Table

namespace Shape

noncomputable instance : Category Shape where
  Hom S T := S.realize ⟶ T.realize
  id S := 𝟙 S.realize
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

end Shape

namespace TheoryData

instance (C : TheoryData.{v}) : Category C.Obj where
  Hom S T := C.Hom S.shape T.shape
  id S := C.id S.shape
  comp f g := C.comp f g
  id_comp := C.id_comp
  comp_id := C.comp_id
  assoc := C.assoc

end TheoryData

namespace GlobularTheory

namespace Morphism

end Morphism

namespace Model

instance (C : GlobularTheory.{v}) : Category C.Model where
  Hom X Y := X.presheaf ⟶ Y.presheaf
  id X := 𝟙 X.presheaf
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

end Model

end GlobularTheory

namespace GlobularTheory.Model

theorem map_unitCell {C : GlobularTheory.{v}} {X Y : C.Model} (f : X ⟶ Y)
    (hC : C.IsCoherator) (n : ℕ) (x : X.underlying.Cell n) :
    (underlyingMap f).app (n + 1) (X.unitCell hC n x) =
      Y.unitCell hC n ((underlyingMap f).app n x) := by
  exact ConcreteCategory.congr_hom (f.naturality
    (show (op (⟨Shape.globe n⟩ : C.Obj)) ⟶ op ⟨Shape.globe (n+1)⟩ from
      Quiver.Hom.op (C.unit hC n))) x

theorem map_baseCell {C : GlobularTheory.{v}} {X Y : C.Model} (f : X ⟶ Y)
    (hC : C.IsCoherator) (x : X.underlying.Cell 0) (n : ℕ) :
    (underlyingMap f).app n (X.baseCell hC x n) =
      Y.baseCell hC ((underlyingMap f).app 0 x) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [baseCell, map_unitCell, ih]

end GlobularTheory.Model

end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
namespace GlobularSet
@[simps]
def Hom.id (X : GlobularSet.{u}) : Hom X X where
  app _ := _root_.id
  source_app _ _ := rfl
  target_app _ _ := rfl

@[simps]
def Hom.comp {X Y Z : GlobularSet.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  app n x := g.app n (f.app n x)
  source_app n x := by rw [f.source_app, g.source_app]
  target_app n x := by rw [f.target_app, g.target_app]

instance : CategoryTheory.Category GlobularSet.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := by ext; rfl
  comp_id _ := by ext; rfl
  assoc _ _ _ := by ext; rfl
@[simp]
theorem Hom.boundary_app {X Y : GlobularSet.{u}} (f : Hom X Y) (n) (x : X.Cell n) :
    f.boundaryMap n (X.boundary n x) = Y.boundary n (f.app n x) := by
  cases n with
  | zero => rfl
  | succ n => exact Subtype.ext (Prod.ext (f.source_app n x) (f.target_app n x))

def ExactBoundaryTest {X Y : GlobularSet.{u}} (f : Hom X Y) : Prop :=
  ∀ (n) (b : X.Boundary n) (y : Y.Cell n), Y.boundary n y = f.boundaryMap n b →
    ∃ x : X.Cell n, X.boundary n x = b ∧ Y.Joined n (f.app n x) y

theorem parallel_iff_boundary_eq (X : GlobularSet.{u}) (n) (x y : X.Cell n) :
    X.Parallel n x y ↔ X.boundary n x = X.boundary n y := by
  cases n with
  | zero => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | succ n =>
    constructor
    · intro h
      exact Subtype.ext (Prod.ext h.1 h.2)
    · intro h
      have h' := congrArg Subtype.val h
      exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩

theorem ExactBoundaryTest.reflects_joined {X Y : GlobularSet.{u}} {f : Hom X Y}
    (hf : ExactBoundaryTest f) {n} {x y : X.Cell n} (hp : X.Parallel n x y)
    (h : Y.Joined n (f.app n x) (f.app n y)) : X.Joined n x y := by
  obtain ⟨h, hs, ht⟩ := h
  let b : X.Boundary (n + 1) := ⟨(x, y), hp⟩
  have hb : Y.boundary (n + 1) h = f.boundaryMap (n + 1) b := by
    exact Subtype.ext (Prod.ext hs ht)
  obtain ⟨z, hz, _⟩ := hf (n + 1) b h hb
  have hz' := congrArg Subtype.val hz
  exact ⟨z, congrArg Prod.fst hz', congrArg Prod.snd hz'⟩

@[simp]
theorem Hom.boundaryMap_comp {X Y Z : GlobularSet.{u}} (f : Hom X Y) (g : Hom Y Z)
    (n) (b : X.Boundary n) :
    (f.comp g).boundaryMap n b = g.boundaryMap n (f.boundaryMap n b) := by
  cases n <;> rfl

theorem ExactBoundaryTest.of_mutual_composites {X Y : GlobularSet.{u}}
    (i : Hom X Y) (r : Hom Y X)
    (hu : ExactBoundaryTest (i.comp r)) (hv : ExactBoundaryTest (r.comp i)) :
    ExactBoundaryTest i := by
  intro n b y hy
  have hb : X.boundary n (r.app n y) = (i.comp r).boundaryMap n b := by
    rw [← r.boundary_app, hy, Hom.boundaryMap_comp]
  obtain ⟨x, hx, h⟩ := hu n b (r.app n y) hb
  refine ⟨x, hx, hv.reflects_joined ?_ (i.map_joined h)⟩
  rw [parallel_iff_boundary_eq, ← i.boundary_app, hx, hy]

end GlobularSet

open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularTheory.Model
noncomputable def cellEquiv {C : GlobularTheory.{v}} (X : C.Model) (n : ℕ) :
    (disk C n ⟶ X) ≃ X.underlying.Cell n :=
  show (yoneda.obj (⟨Shape.globe n⟩ : C.Obj) ⟶ X.presheaf) ≃
    X.presheaf.obj (op (⟨Shape.globe n⟩ : C.Obj)) from yonedaEquiv

end GlobularTheory.Model

namespace GlobularTheory
theorem unit_source (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    C.comp (C.base (Shape.source n)) (C.unit hC n) = C.id (Shape.globe n) :=
  (Classical.choose_spec (hC.2 (C.unitPair n))).1

theorem unit_target (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    C.comp (C.base (Shape.target n)) (C.unit hC n) = C.id (Shape.globe n) :=
  (Classical.choose_spec (hC.2 (C.unitPair n))).2

end GlobularTheory

namespace GlobularTheory.Model
theorem eval_comp {C : GlobularTheory.{v}} (X : C.Model) {R S T : Shape}
    (f : C.Hom R S) (g : C.Hom S T) (x : X.presheaf.obj (op (⟨T⟩ : C.Obj))) :
    X.eval (C.comp f g) x = X.eval f (X.eval g x) := by
  exact ConcreteCategory.congr_hom
    (X.presheaf.map_comp (show (op (⟨T⟩ : C.Obj)) ⟶ op ⟨S⟩ from Quiver.Hom.op g)
      (show (op (⟨S⟩ : C.Obj)) ⟶ op ⟨R⟩ from Quiver.Hom.op f)) x

@[simp]
theorem eval_id {C : GlobularTheory.{v}} (X : C.Model) {S : Shape}
    (x : X.presheaf.obj (op (⟨S⟩ : C.Obj))) : X.eval (C.id S) x = x := by
  exact ConcreteCategory.congr_hom (X.presheaf.map_id (op (⟨S⟩ : C.Obj))) x
@[simp]
theorem unitCell_source {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (x : X.underlying.Cell n) : X.underlying.source n (X.unitCell hC n x) = x := by
  change X.presheaf.obj (op (⟨Shape.globe n⟩ : C.Obj)) at x
  change X.eval (C.base (Shape.source n)) (X.eval (C.unit hC n) x) = x
  rw [← eval_comp, C.unit_source, eval_id]

@[simp]
theorem unitCell_target {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (x : X.underlying.Cell n) : X.underlying.target n (X.unitCell hC n x) = x := by
  change X.presheaf.obj (op (⟨Shape.globe n⟩ : C.Obj)) at x
  change X.eval (C.base (Shape.target n)) (X.eval (C.unit hC n) x) = x
  rw [← eval_comp, C.unit_target, eval_id]

end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularSet

theorem Parallel.symm {X : GlobularSet.{u}} {n} {x y : X.Cell n}
    (h : X.Parallel n x y) : X.Parallel n y x := by
  cases n with
  | zero => trivial
  | succ n => exact ⟨h.1.symm, h.2.symm⟩

theorem outer_parallel {X : GlobularSet.{u}} {n} {f g : X.Cell (n + 1)}
    (h : X.target n f = X.source n g) :
    X.Parallel n (X.source n f) (X.target n g) := by
  cases n with
  | zero => trivial
  | succ n =>
    exact ⟨(X.source_source n f).trans ((congrArg (X.source n) h).trans
      (X.source_source n g)),
      (X.target_source n f).trans ((congrArg (X.target n) h).trans
      (X.target_source n g))⟩

def LiftsBoundaries {X Y : GlobularSet.{u}} (f : Hom X Y) : Prop :=
  ∀ (n) (b : X.Boundary n) (y : Y.Cell n), Y.boundary n y = f.boundaryMap n b →
    ∃ x : X.Cell n, X.boundary n x = b ∧ f.app n x = y

theorem exactBoundaryTest_endpoint_section {P X : GlobularSet.{u}}
    (p₀ p₁ : Hom P X) (h : Hom X P)
    (h₀ : LiftsBoundaries p₀) (h₁ : LiftsBoundaries p₁)
    (s : ∀ n x, p₀.app n (h.app n x) = x)
    (units : ∀ n x, X.Joined n x x) : ExactBoundaryTest (h.comp p₁) := by
  intro n b y hy
  obtain ⟨z, hz, hzy⟩ := h₁ n (h.boundaryMap n b) y
    (by simpa only [Hom.boundaryMap_comp] using hy)
  let x := p₀.app n z
  have hb : X.boundary n x = b := by
    rw [← p₀.boundary_app, hz]
    cases n with
    | zero => rfl
    | succ n => exact Subtype.ext (Prod.ext (s n _) (s n _))
  have hp : P.Parallel n (h.app n x) z := by
    rw [parallel_iff_boundary_eq, ← h.boundary_app, hb, hz]
  obtain ⟨e, es, et⟩ := units n x
  have he : X.boundary (n + 1) e =
      p₀.boundaryMap (n + 1) (⟨(h.app n x, z), hp⟩ : P.Boundary (n + 1)) := by
    apply Subtype.ext
    exact Prod.ext (es.trans (s n x).symm) et
  obtain ⟨c, hc, _⟩ := h₀ (n + 1) ⟨(h.app n x, z), hp⟩ e he
  have hc' := congrArg Subtype.val hc
  refine ⟨x, hb, ?_⟩
  have joined : P.Joined n (h.app n x) z :=
    ⟨c, congrArg Prod.fst hc', congrArg Prod.snd hc'⟩
  simpa only [Hom.comp_app, hzy] using p₁.map_joined joined

end GlobularSet

namespace Shape

theorem source_source (n : ℕ) :
    source n ≫ source (n + 1) = source n ≫ target (n + 1) := by
  have h := congrArg (fun f => GlobularTheory.shapeGlobes.map f) (Globe.source_source n)
  exact (GlobularTheory.shapeGlobes.map_comp _ _).symm.trans
    (h.trans (GlobularTheory.shapeGlobes.map_comp _ _))

theorem target_source (n : ℕ) :
    target n ≫ source (n + 1) = target n ≫ target (n + 1) := by
  have h := congrArg (fun f => GlobularTheory.shapeGlobes.map f) (Globe.target_source n)
  exact (GlobularTheory.shapeGlobes.map_comp _ _).symm.trans
    (h.trans (GlobularTheory.shapeGlobes.map_comp _ _))

theorem seam_inl (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    S.seam hl ≫ S.inl b h hl hr = face hr false ≫ S.inr b h hl hr := by
  have eq := pushout.condition (f := GlobularPresheaf.face hl true ≫ S.2.lastInclusion)
    (g := GlobularPresheaf.face hr false)
  exact eq

@[simp]
theorem globe_seam (n : ℕ) : (globe (n + 1)).seam (Nat.lt_succ_self n) = target n := by
  exact Category.comp_id (GlobularPresheaf.face (Nat.lt_succ_self n) true)

end Shape

namespace GlobularTheory

noncomputable def inversePair (C : GlobularTheory.{v}) (n : ℕ) : C.AdmissiblePair where
  n := n
  arity := Shape.globe (n + 1)
  height := le_rfl
  source := C.base (Shape.target n)
  target := C.base (Shape.source n)
  parallel := by
    cases n with
    | zero => trivial
    | succ n =>
      constructor
      · rw [← C.base_comp, ← C.base_comp]
        exact congrArg C.base (Shape.source_source n).symm
      · rw [← C.base_comp, ← C.base_comp]
        exact congrArg C.base (Shape.target_source n).symm

namespace Model

theorem joined_refl {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (x : X.underlying.Cell n) : X.underlying.Joined n x x :=
  ⟨X.unitCell hC n x, X.unitCell_source hC n x, X.unitCell_target hC n x⟩

theorem joined_symm {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    {n : ℕ} {x y : X.underlying.Cell n} (h : X.underlying.Joined n x y) :
    X.underlying.Joined n y x := by
  obtain ⟨z, rfl, rfl⟩ := h
  obtain ⟨w, hs, ht⟩ := hC.2 (C.inversePair n)
  change C.Hom (Shape.globe (n + 1)) (Shape.globe (n + 1)) at w
  change C.comp (C.base (Shape.source n)) w = C.base (Shape.target n) at hs
  change C.comp (C.base (Shape.target n)) w = C.base (Shape.source n) at ht
  refine ⟨X.eval w z, ?_, ?_⟩
  · change X.presheaf.obj (op (⟨Shape.globe (n + 1)⟩ : C.Obj)) at z
    change X.eval (C.base (Shape.source n)) (X.eval w z) =
      X.eval (C.base (Shape.target n)) z
    rw [← eval_comp, hs]
  · change X.presheaf.obj (op (⟨Shape.globe (n + 1)⟩ : C.Obj)) at z
    change X.eval (C.base (Shape.target n)) (X.eval w z) =
      X.eval (C.base (Shape.source n)) z
    rw [← eval_comp, ht]

end Model

def compositionShape (n : ℕ) : Shape :=
  (Shape.globe (n + 1)).attach n (n + 1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def compositionLeft (n : ℕ) : Shape.globe (n + 1) ⟶ compositionShape n :=
  (Shape.globe (n + 1)).inl n (n + 1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def compositionRight (n : ℕ) : Shape.globe (n + 1) ⟶ compositionShape n :=
  (Shape.globe (n + 1)).inr n (n + 1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

theorem composition_seam (n : ℕ) :
    Shape.target n ≫ compositionLeft n = Shape.source n ≫ compositionRight n := by
  simpa only [Shape.globe_seam, Shape.source, compositionLeft, compositionRight,
    compositionShape] using Shape.seam_inl (Shape.globe (n + 1)) n
    (n + 1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def compositionPair (C : GlobularTheory.{v}) (n : ℕ) : C.AdmissiblePair where
  n := n
  arity := compositionShape n
  height := Nat.max_self (n + 1) ▸ le_rfl
  source := C.base (Shape.source n ≫ compositionLeft n)
  target := C.base (Shape.target n ≫ compositionRight n)
  parallel := by
    cases n with
    | zero => trivial
    | succ n =>
      constructor
      · rw [← C.base_comp, ← C.base_comp]
        apply congrArg C.base
        calc
          _ = (Shape.source n ≫ Shape.target (n+1)) ≫ compositionLeft (n+1) := by
            rw [← Category.assoc, Shape.source_source]
          _ = Shape.source n ≫ (Shape.source (n+1) ≫ compositionRight (n+1)) := by
            rw [Category.assoc, composition_seam]
          _ = _ := by rw [← Category.assoc, Shape.source_source, Category.assoc]
      · rw [← C.base_comp, ← C.base_comp]
        apply congrArg C.base
        calc
          _ = (Shape.target n ≫ Shape.target (n+1)) ≫ compositionLeft (n+1) := by
            rw [← Category.assoc, Shape.target_source]
          _ = Shape.target n ≫ (Shape.source (n+1) ≫ compositionRight (n+1)) := by
            rw [Category.assoc, composition_seam]
          _ = _ := by rw [← Category.assoc, Shape.target_source, Category.assoc]

namespace Model

theorem joined_trans {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    {n : ℕ} {x y z : X.underlying.Cell n}
    (h : X.underlying.Joined n x y) (k : X.underlying.Joined n y z) :
    X.underlying.Joined n x z := by
  obtain ⟨a, ha, ha'⟩ := h
  obtain ⟨b, hb, hb'⟩ := k
  have hab : X.eval (C.base ((Shape.globe (n+1)).seam (Nat.lt_succ_self n))) a =
      X.eval (C.base (Shape.face (Nat.lt_succ_self n) false)) b := by
    rw [Shape.globe_seam]
    exact ha'.trans hb.symm
  obtain ⟨t, htl, htr⟩ := Types.exists_of_isPullback
    (X.sums (Shape.globe (n+1)) n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)) a b hab
  change X.presheaf.obj (op (⟨compositionShape n⟩ : C.Obj)) at t
  change X.eval (C.base (compositionLeft n)) t = a at htl
  change X.eval (C.base (compositionRight n)) t = b at htr
  obtain ⟨w, hs, ht⟩ := hC.2 (C.compositionPair n)
  change C.Hom (Shape.globe (n+1)) (compositionShape n) at w
  change C.comp (C.base (Shape.source n)) w = C.base (Shape.source n ≫ compositionLeft n) at hs
  change C.comp (C.base (Shape.target n)) w = C.base (Shape.target n ≫ compositionRight n) at ht
  refine ⟨X.eval w t, ?_, ?_⟩
  · change X.eval (C.base (Shape.source n)) (X.eval w t) = x
    rw [← eval_comp, hs, C.base_comp, eval_comp, htl]
    exact ha
  · change X.eval (C.base (Shape.target n)) (X.eval w t) = z
    rw [← eval_comp, ht, C.base_comp, eval_comp, htr]
    exact hb'

theorem joined_equivalence {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) : Equivalence (X.underlying.Joined n) :=
  ⟨X.joined_refl hC n, X.joined_symm hC, X.joined_trans hC⟩

end Model
namespace Morphism

@[simp] theorem id_comp {C D : GlobularTheory.{v}} (f : Morphism C D) :
    (id C).comp f = f := by ext; rfl

@[simp] theorem comp_id {C D : GlobularTheory.{v}} (f : Morphism C D) :
    f.comp (id D) = f := by ext; rfl

theorem comp_assoc {B C D E : GlobularTheory.{v}}
    (f : Morphism B C) (g : Morphism C D) (h : Morphism D E) :
    (f.comp g).comp h = f.comp (g.comp h) := by ext; rfl

def mapPair {C D : GlobularTheory.{v}} (f : Morphism C D) (p : C.AdmissiblePair) :
    D.AdmissiblePair where
  n := p.n
  arity := p.arity
  height := p.height
  source := f.map p.source
  target := f.map p.target
  parallel := by
    cases p with
    | mk n S hd s t hp =>
      cases n with
      | zero => trivial
      | succ n =>
        change _ = _ ∧ _ = _
        change _ = _ ∧ _ = _ at hp
        constructor
        · rw [← f.map_base, ← f.map_comp, ← f.map_comp, hp.1]
        · rw [← f.map_base, ← f.map_comp, ← f.map_comp, hp.2]

end Morphism

theorem Fills.map {C D E : GlobularTheory.{v}} {a : Morphism C D}
    {p : C.AdmissiblePair} {z : D.Hom (Shape.globe (p.n + 1)) p.arity}
    (hz : Fills a p z) (b : Morphism D E) : Fills (a.comp b) p (b.map z) := by
  constructor
  · change E.comp (E.base _) (b.map z) = b.map (a.map p.source)
    rw [← b.map_base, ← b.map_comp, hz.1]
  · change E.comp (E.base _) (b.map z) = b.map (a.map p.target)
    rw [← b.map_base, ← b.map_comp, hz.2]

theorem IsFreeExtension.hom_ext {C D : GlobularTheory.{v}} {f : Morphism C D}
    {G : Type v} {pair : G → C.AdmissiblePair}
    {filler : ∀ g, D.Hom (Shape.globe ((pair g).n + 1)) (pair g).arity}
    (hf : IsFreeExtension f G pair filler) {E : GlobularTheory.{v}}
    (a b : Morphism D E) (h : f.comp a = f.comp b)
    (hg : ∀ g, a.map (filler g) = b.map (filler g)) : a = b := by
  obtain ⟨c, _, hc⟩ := hf.2 E (f.comp a) (fun g => a.map (filler g))
    (fun g => (hf.1 g).map a)
  exact (hc a ⟨rfl, fun _ => rfl⟩).trans
    (hc b ⟨h.symm, fun g => (hg g).symm⟩).symm

def LiftsFillers {E D : GlobularTheory.{v}} (p : Morphism E D) : Prop :=
  ∀ (a : E.AdmissiblePair) (z : D.Hom (Shape.globe (a.n + 1)) a.arity),
    Fills p a z → ∃ w, Fills (Morphism.id E) a w ∧ p.map w = z

namespace CellularPresentation

theorem hom_ext {C : GlobularTheory.{v}} (P : C.CellularPresentation)
    {D : GlobularTheory.{v}} (a b : Morphism C D)
    (h : ∀ r, (P.inclusion r).comp a = (P.inclusion r).comp b) : a = b := by
  obtain ⟨c, _, hc⟩ := P.colimit D (fun r => (P.inclusion r).comp a)
    (fun r => by rw [← Morphism.comp_assoc, P.compatible])
  exact (hc a (fun _ => rfl)).trans (hc b (fun r => (h r).symm)).symm

theorem lift {C E D : GlobularTheory.{v}} (P : C.CellularPresentation)
    (p : Morphism E D) (hp : LiftsFillers p) (f : Morphism C D) :
    ∃ a : Morphism C E, a.comp p = f := by
  classical
  let StageLift (r : ℕ) :=
    { a : Morphism (P.stage r) E // a.comp p = (P.inclusion r).comp f }
  have initial : Nonempty (StageLift 0) := by
    let : Unique (Morphism (P.stage 0) E) := (P.initial E).some
    let : Unique (Morphism (P.stage 0) D) := (P.initial D).some
    exact ⟨⟨default, Subsingleton.elim _ _⟩⟩
  have next (r : ℕ) (a : StageLift r) :
      ∃ b : StageLift (r + 1), (P.step r).comp b.1 = a.1 := by
    let z (g : P.generators r) := f.map ((P.inclusion (r+1)).map (P.filler r g))
    have hz (g : P.generators r) : Fills (a.1.comp p) (P.pair r g) (z g) := by
      have h := ((P.free r).1 g).map ((P.inclusion (r+1)).comp f)
      rw [a.2, ← Morphism.comp_assoc, P.compatible] at *
      exact h
    have hw (g : P.generators r) :
        ∃ w, Fills a.1 (P.pair r g) w ∧ p.map w = z g := by
      obtain ⟨w, hw, he⟩ := hp (a.1.mapPair (P.pair r g)) (z g) (hz g)
      exact ⟨w, hw, he⟩
    choose w hw he using hw
    obtain ⟨b, ⟨hb, hbg⟩, _⟩ := (P.free r).2 E a.1 w hw
    have hbp : b.comp p = (P.inclusion (r+1)).comp f := by
      apply (P.free r).hom_ext
      · rw [← Morphism.comp_assoc, hb, a.2, ← Morphism.comp_assoc, P.compatible]
      · intro g
        change p.map (b.map (P.filler r g)) = z g
        rw [hbg, he]
    exact ⟨⟨b, hbp⟩, hb⟩
  let a : (r : ℕ) → StageLift r := fun r => Nat.rec initial.some
    (fun r a => (next r a).choose) r
  have ha (r : ℕ) : (P.step r).comp (a (r+1)).1 = (a r).1 :=
    (next r (a r)).choose_spec
  obtain ⟨b, hb, _⟩ := P.colimit E (fun r => (a r).1) ha
  refine ⟨b, P.hom_ext _ _ (fun r => ?_)⟩
  rw [← Morphism.comp_assoc, hb, (a r).2]

end CellularPresentation
end GlobularTheory

structure TupleSystem where
  presheaf : Shapeᵒᵖ ⥤ Type v
  sums : ∀ (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h),
    IsPullback
      (presheaf.map (S.inl b h hl hr).op)
      (presheaf.map (S.inr b h hl hr).op)
      (presheaf.map (S.seam hl).op)
      (presheaf.map (Shape.face hr false).op)

namespace TupleSystem

noncomputable def endData (T : TupleSystem.{v}) : TheoryData.{v} where
  Hom S R := T.presheaf.obj (op R) ⟶ T.presheaf.obj (op S)
  id _ := 𝟙 _
  comp f g := g ≫ f
  id_comp f := Category.comp_id f
  comp_id f := Category.id_comp f
  assoc f g h := (Category.assoc h g f).symm
  base f := T.presheaf.map f.op
  base_id S := T.presheaf.map_id (op S)
  base_comp f g := T.presheaf.map_comp g.op f.op

noncomputable def endEmbedding (T : TupleSystem.{v}) : T.endData.Obj ⥤ (Type v)ᵒᵖ where
  obj S := op (T.presheaf.obj (op S.shape))
  map f := f.op
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def endEmbedding_fullyFaithful (T : TupleSystem.{v}) :
    T.endEmbedding.FullyFaithful where
  preimage f := f.unop

noncomputable def endTheory (T : TupleSystem.{v}) : GlobularTheory.{v} where
  toTheoryData := T.endData
  sums S b h hl hr := by
    let : T.endEmbedding.Full := T.endEmbedding_fullyFaithful.full
    let : T.endEmbedding.Faithful := T.endEmbedding_fullyFaithful.faithful
    apply IsPushout.of_map_of_faithful T.endEmbedding
    exact (T.sums S b h hl hr).op.flip

noncomputable def model {C : GlobularTheory.{v}} (T : TupleSystem.{v})
    (a : GlobularTheory.Morphism C T.endTheory) : C.Model where
  presheaf :=
    { obj := fun S => T.presheaf.obj (op S.unop.shape)
      map := fun f => a.map f.unop
      map_id := fun S => a.map_id S.unop.shape
      map_comp := fun f g => a.map_comp g.unop f.unop }
  sums S b h hl hr := by
    change IsPullback (a.map (C.base (S.inl b h hl hr)))
      (a.map (C.base (S.inr b h hl hr))) (a.map (C.base (S.seam hl)))
      (a.map (C.base (Shape.face hr false)))
    rw [a.map_base, a.map_base, a.map_base, a.map_base]
    exact T.sums S b h hl hr

end TupleSystem

namespace GlobularTheory.Model

noncomputable abbrev tuples {C : GlobularTheory.{v}} (X : C.Model) : TupleSystem.{v} where
  presheaf := C.toTheoryData.arity.op ⋙ X.presheaf
  sums := X.sums

noncomputable def interpretation {C : GlobularTheory.{v}} (X : C.Model) :
    Morphism C X.tuples.endTheory where
  map f := X.presheaf.map (show (⟨_⟩ : C.Obj) ⟶ ⟨_⟩ from f).op
  map_id S := X.presheaf.map_id (op (⟨S⟩ : C.Obj))
  map_comp f g := X.presheaf.map_comp (show (op (⟨_⟩ : C.Obj)) ⟶ op ⟨_⟩ from Quiver.Hom.op (show (⟨_⟩ : C.Obj) ⟶ ⟨_⟩ from g))
    (show (op (⟨_⟩ : C.Obj)) ⟶ op ⟨_⟩ from
      Quiver.Hom.op (show (⟨_⟩ : C.Obj) ⟶ ⟨_⟩ from f))
  map_base _ := rfl

end GlobularTheory.Model

end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularTheory.Model

theorem components_eq_iff {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (x y : X.underlying.Cell 0) :
    Quot.mk (X.underlying.Joined 0) x = Quot.mk (X.underlying.Joined 0) y ↔
      X.underlying.Joined 0 x y :=
  ⟨fun h => (X.joined_equivalence hC 0).eqvGen_iff.mp (Quot.eqvGen_exact h), Quot.sound⟩

theorem loops_joined_equivalence {C : GlobularTheory.{v}} (X : C.Model)
    (hC : C.IsCoherator) (x : X.underlying.Cell 0) (n : ℕ) :
    Equivalence (fun a b : X.Loops hC x n => X.underlying.Joined (n+1) a.1 b.1) :=
  ⟨fun a => X.joined_refl hC (n+1) a.1, fun h => X.joined_symm hC h,
    fun h k => X.joined_trans hC h k⟩

theorem weakEquivalence_of_exactBoundaryTest {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X Y : C.Model} (f : X ⟶ Y) (hf : GlobularSet.ExactBoundaryTest (underlyingMap f)) :
    WeakEquivalence hC f := by
  constructor
  · constructor
    · intro a b hab
      induction a using Quot.inductionOn with | h a =>
        induction b using Quot.inductionOn with | h b =>
          apply Quot.sound
          apply hf.reflects_joined (n := 0) trivial
          exact (Y.components_eq_iff hC _ _).mp hab
    · intro b
      induction b using Quot.inductionOn with | h b =>
        obtain ⟨a, _, ha⟩ := hf 0 PUnit.unit b rfl
        exact ⟨Quot.mk _ a, Quot.sound ha⟩
  · intro x n
    constructor
    · intro a b hab
      induction a using Quot.inductionOn with | h a =>
        induction b using Quot.inductionOn with | h b =>
          apply Quot.sound
          apply hf.reflects_joined
          · exact ⟨a.2.1.trans b.2.1.symm, a.2.2.trans b.2.2.symm⟩
          · exact (Y.loops_joined_equivalence hC _ n).eqvGen_iff.mp
              (Quot.eqvGen_exact hab)
    · intro b
      induction b using Quot.inductionOn with | h b =>
        let c := X.baseCell hC x n
        let bd : X.underlying.Boundary (n+1) :=
          ⟨(c, c), by cases n <;> simp [GlobularSet.Parallel]⟩
        have hb : Y.underlying.boundary (n+1) b.1 =
            (underlyingMap f).boundaryMap (n+1) bd := by
          apply Subtype.ext
          exact Prod.ext (b.2.1.trans (map_baseCell f hC x n).symm)
            (b.2.2.trans (map_baseCell f hC x n).symm)
        obtain ⟨a, ha, hab⟩ := hf (n+1) bd b.1 hb
        have ha' := congrArg Subtype.val ha
        let a' : X.Loops hC x n :=
          ⟨a, congrArg Prod.fst ha', congrArg Prod.snd ha'⟩
        exact ⟨Quot.mk _ a', Quot.sound hab⟩

end GlobularTheory.Model

namespace GlobularSet

def cutoffCell (X : GlobularSet.{u}) (q n : ℕ) : Type u :=
  if n ≤ q then X.Cell n else X.Boundary (q+1)

def cutoffFace (X : GlobularSet.{u}) (q n : ℕ) (side : Bool) :
    X.cutoffCell q (n+1) → X.cutoffCell q n := by
  by_cases h : n+1 ≤ q
  · have hn : n ≤ q := Nat.le_trans (Nat.le_succ n) h
    simpa only [cutoffCell, ite_eq_left h, ite_eq_left hn] using
      (if side then X.target n else X.source n)
  · by_cases hn : n = q
    · subst n
      simpa only [cutoffCell, ite_eq_right h, ite_eq_left (Nat.le_refl q)] using
        (fun b : X.Boundary (q+1) => if side then b.1.2 else b.1.1)
    · have hnq : ¬ n ≤ q := by omega
      simpa only [cutoffCell, ite_eq_right h, ite_eq_right hnq] using
        (_root_.id : X.Boundary (q+1) → X.Boundary (q+1))

theorem cutoffCell_low (X : GlobularSet.{u}) {q n : ℕ} (h : n ≤ q) :
    X.cutoffCell q n = X.Cell n := ite_eq_left h

theorem cutoffCell_high (X : GlobularSet.{u}) {q n : ℕ} (h : ¬ n ≤ q) :
    X.cutoffCell q n = X.Boundary (q+1) := ite_eq_right h

theorem cutoffFace_low (X : GlobularSet.{u}) {q n : ℕ} (h : n+1 ≤ q) (side) :
    HEq (X.cutoffFace q n side) (if side then X.target n else X.source n) := by
  simp only [cutoffFace, dite_eq_left h]
  exact cast_heq _ _

theorem cutoffFace_seam (X : GlobularSet.{u}) (q : ℕ) (side) :
    HEq (X.cutoffFace q q side)
      (fun b : X.Boundary (q+1) => if side then b.1.2 else b.1.1) := by
  simp only [cutoffFace, dite_eq_right (Nat.not_succ_le_self q)]
  exact cast_heq _ _

private theorem comp_eq_of_heq {A B C A' B' C' : Type u}
    (ha : A = A') (hb : B = B') (hc : C = C')
    {s t : A → B} {s' t' : A' → B'} {l : B → C} {l' : B' → C'}
    (hs : HEq s s') (ht : HEq t t') (hl : HEq l l')
    (w : ∀ x, l' (s' x) = l' (t' x)) : ∀ x, l (s x) = l (t x) := by
  cases ha; cases hb; cases hc
  cases eq_of_heq hs; cases eq_of_heq ht; cases eq_of_heq hl
  exact w

def cutoff (X : GlobularSet.{u}) (q : ℕ) : GlobularSet.{u} where
  Cell := X.cutoffCell q
  source n := X.cutoffFace q n false
  target n := X.cutoffFace q n true
  source_source n x := by
    by_cases h : n+1+1 ≤ q
    · have h₁ : n+1 ≤ q := by omega
      have h₀ : n ≤ q := by omega
      exact comp_eq_of_heq (X.cutoffCell_low h) (X.cutoffCell_low h₁)
        (X.cutoffCell_low h₀) (X.cutoffFace_low h false) (X.cutoffFace_low h true)
        (X.cutoffFace_low h₁ false) (X.source_source n) x
    · by_cases h₁ : n+1 = q
      · subst q
        exact comp_eq_of_heq (X.cutoffCell_high (Nat.not_succ_le_self (n+1)))
          (X.cutoffCell_low le_rfl) (X.cutoffCell_low (Nat.le_succ n))
          (X.cutoffFace_seam (n+1) false) (X.cutoffFace_seam (n+1) true)
          (X.cutoffFace_low le_rfl false) (fun x => x.2.1) x
      · by_cases h₀ : n = q
        · subst q
          simp [cutoffFace]
        · have h₁' : ¬ n+1 ≤ q := by omega
          simp [cutoffFace, h, h₁, h₀, h₁']
  target_source n x := by
    by_cases h : n+1+1 ≤ q
    · have h₁ : n+1 ≤ q := by omega
      have h₀ : n ≤ q := by omega
      exact comp_eq_of_heq (X.cutoffCell_low h) (X.cutoffCell_low h₁)
        (X.cutoffCell_low h₀) (X.cutoffFace_low h false) (X.cutoffFace_low h true)
        (X.cutoffFace_low h₁ true) (X.target_source n) x
    · by_cases h₁ : n+1 = q
      · subst q
        exact comp_eq_of_heq (X.cutoffCell_high (Nat.not_succ_le_self (n+1)))
          (X.cutoffCell_low le_rfl) (X.cutoffCell_low (Nat.le_succ n))
          (X.cutoffFace_seam (n+1) false) (X.cutoffFace_seam (n+1) true)
          (X.cutoffFace_low le_rfl true) (fun x => x.2.2) x
      · by_cases h₀ : n = q
        · subst q
          simp [cutoffFace]
        · have h₁' : ¬ n+1 ≤ q := by omega
          simp [cutoffFace, h, h₁, h₀, h₁']

end GlobularSet

namespace GlobularTheory.Model

@[simp]
theorem underlyingMap_id {C : GlobularTheory.{v}} (X : C.Model) :
    underlyingMap (𝟙 X) = GlobularSet.Hom.id X.underlying := rfl

@[simp]
theorem underlyingMap_comp {C : GlobularTheory.{v}} {X Y Z : C.Model}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    underlyingMap (f ≫ g) = (underlyingMap f).comp (underlyingMap g) := rfl

theorem BoundaryAttachment.hasLiftingProperty {C : GlobularTheory.{v}}
    {X Y P Q : C.Model} {i : X ⟶ Y} (A : BoundaryAttachment i) (p : P ⟶ Q)
    (hp : GlobularSet.LiftsBoundaries (underlyingMap p)) : HasLiftingProperty i p := by
  classical
  constructor
  intro f g sq
  have liftcell : ∀ k, ∃ z : P.underlying.Cell (A.dimension k),
      P.underlying.boundary _ z = (underlyingMap f).boundaryMap _ (A.boundary k) ∧
      (underlyingMap p).app _ z = (underlyingMap g).app _ (A.cell k) := by
    intro k
    apply hp
    rw [← (underlyingMap g).boundary_app, A.cell_boundary]
    have eq := congrArg (fun e => (underlyingMap e).boundaryMap _ (A.boundary k)) sq.w
    simpa only [underlyingMap_comp, GlobularSet.Hom.boundaryMap_comp] using eq.symm
  choose z hz hzp using liftcell
  obtain ⟨l, hl, huniq⟩ := A.universal P f z hz
  have hcomp : l ≫ p = g := by
    obtain ⟨_, _, unique⟩ := A.universal Q (i ≫ g)
      (fun k => (underlyingMap g).app _ (A.cell k))
      (fun k => by rw [← (underlyingMap g).boundary_app, A.cell_boundary,
        underlyingMap_comp, GlobularSet.Hom.boundaryMap_comp])
    apply (unique (l ≫ p) ?_).trans (unique g ?_).symm
    · constructor
      · rw [← Category.assoc, hl.1, sq.w]
      · intro k
        change (underlyingMap p).app _ ((underlyingMap l).app _ (A.cell k)) = _
        rw [hl.2, hzp]
    · exact ⟨rfl, fun _ => rfl⟩
  exact CommSq.HasLift.mk' ⟨l, hl.1, hcomp⟩

theorem section_of_isCellular {C : GlobularTheory.{v}} {X P : C.Model}
    (hX : X.IsCellular) (p : P ⟶ X)
    (hp : GlobularSet.LiftsBoundaries (underlyingMap p)) : ∃ s : X ⟶ P, s ≫ p = 𝟙 X := by
  obtain ⟨A⟩ := hX
  let := A.linearOrder
  let := A.orderBot
  let := A.succOrder
  let := A.wellFoundedLT
  have : A.chain.F.IsWellOrderContinuous := A.chain.isWellOrderContinuous
  have : HasLiftingProperty (A.chain.incl.app ⊥) p :=
    HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot
      (hc := A.chain.isColimit)
      (fun j hj => (A.attachment j hj).hasLiftingProperty p hp)
  let f : A.chain.F.obj ⊥ ⟶ P := A.chain.isoBot.hom ≫ A.isInitial.to P
  have sq : CommSq f (A.chain.incl.app ⊥) p (𝟙 X) := by
    constructor
    dsimp [f]
    rw [Category.comp_id, Category.assoc]
    have eq : A.isInitial.to P ≫ p = A.start := A.isInitial.hom_ext _ _
    rw [eq]
    exact (congrArg (A.chain.isoBot.hom ≫ ·) A.chain.fac.symm).trans
      (by simp only [Iso.hom_inv_id_assoc])
  exact ⟨sq.lift, sq.fac_right⟩


noncomputable def unitMap (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    disk C (n+1) ⟶ disk C n :=
  show (disk C (n+1)).presheaf ⟶ (disk C n).presheaf from
    yoneda.map (show (⟨Shape.globe (n+1)⟩ : C.Obj) ⟶ ⟨Shape.globe n⟩ from C.unit hC n)

@[simp]
theorem J_comp_unitMap (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    J C n ≫ unitMap C hC n = 𝟙 (disk C n) := by
  apply NatTrans.ext
  funext S
  apply ConcreteCategory.hom_ext
  intro f
  change C.Hom S.unop.shape (Shape.globe n) at f
  change C.comp (C.comp f (C.base (Shape.source n))) (C.unit hC n) = f
  rw [C.assoc, C.unit_source, C.comp_id]

theorem elementary_pushout_retraction {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X Y : C.Model} (n : ℕ) (a : disk C n ⟶ X) (i : X ⟶ Y)
    (b : disk C (n+1) ⟶ Y) (sq : IsPushout a (J C n) i b) :
    ∃ r : Y ⟶ X, i ≫ r = 𝟙 X := by
  have w : a ≫ 𝟙 X = J C n ≫ (unitMap C hC n ≫ a) := by
    rw [← Category.assoc, J_comp_unitMap, Category.id_comp, Category.comp_id]
  exact ⟨sq.desc (𝟙 X) (unitMap C hC n ≫ a) w, sq.inl_desc _ _ w⟩

theorem weakEquivalence_of_partialPath_data {C : GlobularTheory.{v}}
    (hC : C.IsCoherator) {X Y : C.Model} (hX : X.IsCellular)
    (n : ℕ) (a : disk C n ⟶ X) (i : X ⟶ Y) (b : disk C (n+1) ⟶ Y)
    (sq : IsPushout a (J C n) i b)
    (PX PY : C.Model) (pX₀ pX₁ : PX ⟶ X) (pY₀ pY₁ : PY ⟶ Y)
    (Pi : PX ⟶ PY) (nat₀ : Pi ≫ pY₀ = pX₀ ≫ i) (nat₁ : Pi ≫ pY₁ = pX₁ ≫ i)
    (hpX₀ : GlobularSet.LiftsBoundaries (underlyingMap pX₀))
    (hpX₁ : GlobularSet.LiftsBoundaries (underlyingMap pX₁))
    (hpY₀ : GlobularSet.LiftsBoundaries (underlyingMap pY₀))
    (hpY₁ : GlobularSet.LiftsBoundaries (underlyingMap pY₁))
    (joint : ∀ (t : disk C n ⟶ PY) (u₀ u₁ : disk C (n+1) ⟶ Y),
      t ≫ pY₀ = J C n ≫ u₀ → t ≫ pY₁ = J C n ≫ u₁ →
      ∃ l : disk C (n+1) ⟶ PY,
        J C n ≫ l = t ∧ l ≫ pY₀ = u₀ ∧ l ≫ pY₁ = u₁) :
    WeakEquivalence hC i := by
  obtain ⟨r, hr⟩ := elementary_pushout_retraction hC n a i b sq
  obtain ⟨h, hh⟩ := section_of_isCellular hX pX₀ hpX₀
  let u : X ⟶ X := h ≫ pX₁
  let ru : Y ⟶ X := r ≫ u
  have diu : i ≫ ru = u := by simp only [ru, ← Category.assoc, hr, Category.id_comp]
  have w₀ : (a ≫ h ≫ Pi) ≫ pY₀ = J C n ≫ b := by
    simp only [Category.assoc, nat₀]
    rw [← Category.assoc h, hh, Category.id_comp, ← sq.w]
  have w₁ : (a ≫ h ≫ Pi) ≫ pY₁ = J C n ≫ (b ≫ ru ≫ i) := by
    simp only [Category.assoc, nat₁]
    rw [← Category.assoc h]
    change a ≫ (u ≫ i) = _
    rw [← diu]
    simp only [← Category.assoc]
    rw [sq.w]
  obtain ⟨l, hl, hl₀, hl₁⟩ := joint (a ≫ h ≫ Pi) b (b ≫ ru ≫ i) w₀ w₁
  let f : Y ⟶ PY := sq.desc (h ≫ Pi) l hl.symm
  have hf₀ : f ≫ pY₀ = 𝟙 Y := by
    apply sq.hom_ext
    · dsimp [f]
      rw [← Category.assoc, sq.inl_desc, Category.assoc, nat₀,
        ← Category.assoc, hh, Category.id_comp, Category.comp_id]
    · dsimp [f]
      rw [← Category.assoc, sq.inr_desc, hl₀, Category.comp_id]
  have hf₁ : f ≫ pY₁ = ru ≫ i := by
    apply sq.hom_ext
    · dsimp [f]
      rw [← Category.assoc, sq.inl_desc, Category.assoc, nat₁]
      rw [← Category.assoc i, diu]
      rfl
    · dsimp [f]
      rw [← Category.assoc, sq.inr_desc, hl₁]
  apply weakEquivalence_of_exactBoundaryTest hC
  apply GlobularSet.ExactBoundaryTest.of_mutual_composites (underlyingMap i) (underlyingMap ru)
  · have test := GlobularSet.exactBoundaryTest_endpoint_section
      (underlyingMap pX₀) (underlyingMap pX₁) (underlyingMap h) hpX₀ hpX₁
      (fun k x => congrFun (congrArg (fun e => (underlyingMap e).app k) hh) x)
      (X.joined_refl hC)
    rw [← underlyingMap_comp, diu]
    exact test
  · have test := GlobularSet.exactBoundaryTest_endpoint_section
      (underlyingMap pY₀) (underlyingMap pY₁) (underlyingMap f) hpY₀ hpY₁
      (fun k x => congrFun (congrArg (fun e => (underlyingMap e).app k) hf₀) x)
      (Y.joined_refl hC)
    rw [← underlyingMap_comp]
    rw [← underlyingMap_comp, hf₁] at test
    exact test

end GlobularTheory.Model

namespace GlobularSet

def faceMap (X : GlobularSet.{u}) {m n : ℕ} (h : m < n) (side : Bool) :
    X.Cell n → X.Cell m :=
  Nat.leRecOn (C := fun k => X.Cell k → X.Cell m) h
    (fun {k} f x => f (X.source k x)) (if side then X.target m else X.source m)

@[simp]
theorem faceMap_succ (X : GlobularSet.{u}) (m : ℕ) (side : Bool) :
    X.faceMap (Nat.lt_succ_self m) side = (if side then X.target m else X.source m) :=
  Nat.leRecOn_self _

theorem faceMap_source (X : GlobularSet.{u}) {m n : ℕ} (h : m < n) (side : Bool)
    (x : X.Cell (n+1)) :
    X.faceMap (Nat.lt_succ_of_lt h) side x = X.faceMap h side (X.source n x) := by
  unfold faceMap
  rw [Nat.leRecOn_succ h]

theorem faceMap_target (X : GlobularSet.{u}) {m n : ℕ} (h : m < n) (side : Bool)
    (x : X.Cell (n+1)) :
    X.faceMap h side (X.source n x) = X.faceMap h side (X.target n x) := by
  induction n, h using Nat.le_induction with
  | base =>
    simp only [faceMap_succ]
    cases side
    · exact X.source_source m x
    · exact X.target_source m x
  | succ n h _ =>
    rw [faceMap_source X h, faceMap_source X h, X.source_source]

theorem faceMap_comp (X : GlobularSet.{u}) {m n k : ℕ}
    (h : m < n) (h' : n < k) (side side' : Bool) (x : X.Cell k) :
    X.faceMap (h.trans h') side x =
      X.faceMap h side (X.faceMap h' side' x) := by
  induction k, h' using Nat.le_induction with
  | base =>
    rw [faceMap_source X h, faceMap_succ]
    cases side'
    · rfl
    · exact X.faceMap_target h side x
  | succ k h' ih =>
    rw [faceMap_source X (h.trans h'), faceMap_source X h']
    exact ih (X.source k x)

def evalFace (X : GlobularSet.{u}) {m n : ℕ} : Globe.Face m n → (X.Cell n → X.Cell m)
  | .id _ => _root_.id
  | .face h side => X.faceMap h side

theorem evalFace_comp (X : GlobularSet.{u}) {m n k : ℕ} (f : Globe.Face m n)
    (g : Globe.Face n k) (x : X.Cell k) :
    X.evalFace (f.comp g) x = X.evalFace f (X.evalFace g x) := by
  cases f with
  | id => rfl
  | face h side =>
    cases g with
    | id => rfl
    | face h' side' => exact X.faceMap_comp h h' side side' x

def presheaf (X : GlobularSet.{u}) : GlobularPresheaf.{u} where
  obj n := X.Cell n.unop.dim
  map f := TypeCat.ofHom (X.evalFace f.unop)
  map_id _ := rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact X.evalFace_comp g.unop f.unop x

end GlobularSet

end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace Shape

noncomputable def realization : Shape ⥤ GlobularPresheaf.{0} where
  obj := realize
  map f := f

noncomputable def liftedRealization : Shape ⥤ GlobularPresheaf.{v} :=
  realization ⋙ (Functor.whiskeringRight Globeᵒᵖ (Type) (Type v)).obj uliftFunctor.{v,0}

theorem realization_pushout (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    IsPushout (realization.map (S.seam hl)) (realization.map (face hr false))
      (realization.map (S.inl b h hl hr)) (realization.map (S.inr b h hl hr)) :=
  IsPushout.of_hasPushout _ _

theorem liftedRealization_pushout (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    IsPushout (liftedRealization.{v}.map (S.seam hl))
      (liftedRealization.{v}.map (face hr false))
      (liftedRealization.{v}.map (S.inl b h hl hr))
      (liftedRealization.{v}.map (S.inr b h hl hr)) :=
  (realization_pushout S b h hl hr).map
    ((Functor.whiskeringRight Globeᵒᵖ (Type) (Type v)).obj uliftFunctor.{v,0})

end Shape

namespace GlobularPresheaf

noncomputable def tuples (X : GlobularPresheaf.{v}) : TupleSystem.{v} where
  presheaf := Shape.liftedRealization.op ⋙ yoneda.obj X
  sums S b h hl hr :=
    ((Shape.liftedRealization_pushout S b h hl hr).op.flip).map (yoneda.obj X)

end GlobularPresheaf

namespace TupleSystem

noncomputable def relativeData {T U : TupleSystem.{v}} (f : T.presheaf ⟶ U.presheaf) :
    TheoryData.{v} where
  Hom S R := Arrow.mk (f.app (op R)) ⟶ Arrow.mk (f.app (op S))
  id _ := 𝟙 _
  comp a b := b ≫ a
  id_comp a := Category.comp_id a
  comp_id a := Category.id_comp a
  assoc a b c := (Category.assoc c b a).symm
  base a := Arrow.homMk (T.presheaf.map a.op) (U.presheaf.map a.op) (f.naturality a.op)
  base_id S := by apply Arrow.hom_ext <;> exact CategoryTheory.Functor.map_id _ _
  base_comp a b := by apply Arrow.hom_ext <;> exact CategoryTheory.Functor.map_comp _ b.op a.op

noncomputable def relativeEmbedding {T U : TupleSystem.{v}}
    (f : T.presheaf ⟶ U.presheaf) : (relativeData f).Obj ⥤ (Arrow (Type v))ᵒᵖ where
  obj S := op (Arrow.mk (f.app (op S.shape)))
  map a := a.op

noncomputable def relativeEmbedding_fullyFaithful {T U : TupleSystem.{v}}
    (f : T.presheaf ⟶ U.presheaf) : (relativeEmbedding f).FullyFaithful where
  preimage a := a.unop

private theorem arrow_isPullback {P X Y Z : Arrow (Type v)}
    {a : P ⟶ X} {b : P ⟶ Y} {c : X ⟶ Z} {d : Y ⟶ Z}
    (hl : IsPullback a.left b.left c.left d.left)
    (hr : IsPullback a.right b.right c.right d.right) : IsPullback a b c d where
  w := Arrow.hom_ext _ _ hl.w hr.w
  isLimit' := ⟨Comma.fstSndJointlyReflectLimit
    ((PullbackCone.isLimitMapConeEquiv _ _).symm hl.isLimit)
    ((PullbackCone.isLimitMapConeEquiv _ _).symm hr.isLimit)⟩

noncomputable def relativeTheory {T U : TupleSystem.{v}}
    (f : T.presheaf ⟶ U.presheaf) : GlobularTheory.{v} where
  toTheoryData := relativeData f
  sums S b h hl hr := by
    let : (relativeEmbedding f).Full := (relativeEmbedding_fullyFaithful f).full
    let : (relativeEmbedding f).Faithful := (relativeEmbedding_fullyFaithful f).faithful
    apply IsPushout.of_map_of_faithful (relativeEmbedding f)
    exact (arrow_isPullback (T.sums S b h hl hr) (U.sums S b h hl hr)).op.flip

noncomputable def relativeSource {T U : TupleSystem.{v}}
    (f : T.presheaf ⟶ U.presheaf) : GlobularTheory.Morphism (relativeTheory f) T.endTheory where
  map a := a.left
  map_id _ := rfl
  map_comp _ _ := rfl
  map_base _ := rfl

noncomputable def relativeTarget {T U : TupleSystem.{v}}
    (f : T.presheaf ⟶ U.presheaf) : GlobularTheory.Morphism (relativeTheory f) U.endTheory where
  map a := a.right
  map_id _ := rfl
  map_comp _ _ := rfl
  map_base _ := rfl

noncomputable def relativeModelMap {C : GlobularTheory.{v}} {T U : TupleSystem.{v}}
    (f : T.presheaf ⟶ U.presheaf) (a : GlobularTheory.Morphism C (relativeTheory f)) :
    T.model (a.comp (relativeSource f)) ⟶ U.model (a.comp (relativeTarget f)) where
  app S := f.app (op S.unop.shape)
  naturality _ _ g := (a.map g.unop).w

end TupleSystem

namespace GlobularSet

theorem lift_operation {X Y : GlobularSet.{v}} (η : X.Hom Y)
    {A B : Type v} (f : A → B) (n : ℕ)
    (s t : A → X.Cell n) (s' t' : B → Y.Cell n)
    (hs : ∀ a, η.app n (s a) = s' (f a))
    (ht : ∀ a, η.app n (t a) = t' (f a))
    (hp : ∀ b, Y.Parallel n (s' b) (t' b))
    (z : A → X.Cell (n+1)) (hzs : ∀ a, X.source n (z a) = s a)
    (hzt : ∀ a, X.target n (z a) = t a)
    (h : Function.Bijective f ∨ Function.Bijective (Y.boundary (n+1))) :
    ∃ z' : B → Y.Cell (n+1),
      (∀ b, Y.source n (z' b) = s' b) ∧
      (∀ b, Y.target n (z' b) = t' b) ∧
      (∀ a, η.app (n+1) (z a) = z' (f a)) := by
  classical
  rcases h with h | h
  · let e : A ≃ B := Equiv.ofBijective f h
    refine ⟨fun b => η.app (n+1) (z (e.symm b)), ?_, ?_, ?_⟩
    · intro b
      rw [← η.source_app, hzs, hs]
      exact congrArg s' (e.apply_symm_apply b)
    · intro b
      rw [← η.target_app, hzt, ht]
      exact congrArg t' (e.apply_symm_apply b)
    · intro a
      exact congrArg (fun a => η.app (n+1) (z a)) (e.symm_apply_apply a).symm
  · let e : Y.Cell (n+1) ≃ Y.Boundary (n+1) := Equiv.ofBijective _ h
    let b (x : B) : Y.Boundary (n+1) := ⟨(s' x, t' x), hp x⟩
    have hb (x : B) : Y.boundary (n+1) (e.symm (b x)) = b x := e.apply_symm_apply _
    refine ⟨fun x => e.symm (b x), ?_, ?_, ?_⟩
    · intro x
      exact congrArg (fun a => a.1.1) (hb x)
    · intro x
      exact congrArg (fun a => a.1.2) (hb x)
    · intro a
      apply h.1
      rw [hb, ← η.boundary_app]
      apply Subtype.ext
      change (η.app n (X.source n (z a)), η.app n (X.target n (z a))) =
        (s' (f a), t' (f a))
      rw [hzs, hs, hzt, ht]

end GlobularSet

namespace TupleSystem

noncomputable def underlying (T : TupleSystem.{v}) : GlobularSet.{v} :=
  GlobularPresheaf.underlying (GlobularTheory.shapeGlobes.op ⋙ T.presheaf)

noncomputable def underlyingMap {T U : TupleSystem.{v}} (f : T.presheaf ⟶ U.presheaf) :
    T.underlying.Hom U.underlying :=
  GlobularPresheaf.underlyingMap (Functor.whiskerLeft GlobularTheory.shapeGlobes.op f)

theorem parallel_eval (T : TupleSystem.{v}) {S : Shape} (n : ℕ)
    (s t : T.presheaf.obj (op S) ⟶ T.presheaf.obj (op (Shape.globe n)))
    (hp : T.endTheory.Parallel n s t)
    (x : T.presheaf.obj (op S)) : T.underlying.Parallel n (s x) (t x) := by
  cases n with
  | zero => trivial
  | succ n =>
    exact ⟨ConcreteCategory.congr_hom hp.1 x, ConcreteCategory.congr_hom hp.2 x⟩

theorem relativeSource_liftsFillers {T U : TupleSystem.{v}}
    (f : T.presheaf ⟶ U.presheaf) (q : ℕ)
    (hlow : ∀ S : Shape, S.height ≤ q → Function.Bijective (f.app (op S)))
    (hhigh : ∀ k, q < k → Function.Bijective (U.underlying.boundary k)) :
    GlobularTheory.LiftsFillers (relativeSource f) := by
  intro a z hz
  change T.presheaf.obj (op a.arity) ⟶ T.presheaf.obj (op (Shape.globe (a.n+1))) at z
  have hp := U.parallel_eval a.n a.source.right a.target.right
    ((relativeTarget f).mapPair a).parallel
  have choice : Function.Bijective (f.app (op a.arity)) ∨
      Function.Bijective (U.underlying.boundary (a.n+1)) := by
    by_cases h : a.n+1 ≤ q
    · exact Or.inl (hlow _ (a.height.trans h))
    · exact Or.inr (hhigh _ (Nat.lt_of_not_ge h))
  obtain ⟨z', hzs, hzt, hη⟩ := GlobularSet.lift_operation (underlyingMap f)
    (f.app (op a.arity)) a.n a.source.left a.target.left a.source.right a.target.right
    (fun x => ConcreteCategory.congr_hom a.source.w x)
    (fun x => ConcreteCategory.congr_hom a.target.w x) hp z
    (fun x => ConcreteCategory.congr_hom hz.1 x)
    (fun x => ConcreteCategory.congr_hom hz.2 x) choice
  let w : (relativeTheory f).Hom (Shape.globe (a.n+1)) a.arity :=
    Arrow.homMk z (TypeCat.ofHom z') (ConcreteCategory.hom_ext _ _ hη)
  refine ⟨w, ⟨?_, ?_⟩, rfl⟩
  · apply Arrow.hom_ext
    · exact hz.1
    · exact ConcreteCategory.hom_ext _ _ hzs
  · apply Arrow.hom_ext
    · exact hz.2
    · exact ConcreteCategory.hom_ext _ _ hzt


private theorem bijective_pullback_map
    {P A B R P' A' B' R' : Type v}
    (l : P ⟶ A) (r : P ⟶ B) (s : A ⟶ R) (t : B ⟶ R)
    (l' : P' ⟶ A') (r' : P' ⟶ B') (s' : A' ⟶ R') (t' : B' ⟶ R')
    (h : IsPullback l r s t) (h' : IsPullback l' r' s' t')
    (p : P ⟶ P') (a : A ⟶ A') (b : B ⟶ B') (c : R ⟶ R')
    (wl : l ≫ a = p ≫ l') (wr : r ≫ b = p ≫ r')
    (ws : s ≫ c = a ≫ s') (wt : t ≫ c = b ≫ t')
    (ha : Function.Bijective a) (hb : Function.Bijective b)
    (hc : Function.Injective c) : Function.Bijective p := by
  have hl (x : P) : a (l x) = l' (p x) := ConcreteCategory.congr_hom wl x
  have hr (x : P) : b (r x) = r' (p x) := ConcreteCategory.congr_hom wr x
  have hs (x : A) : c (s x) = s' (a x) := ConcreteCategory.congr_hom ws x
  have ht (x : B) : c (t x) = t' (b x) := ConcreteCategory.congr_hom wt x
  constructor
  · intro x y hp
    apply Types.ext_of_isPullback h
    · apply ha.1
      rw [hl, hl, hp]
    · apply hb.1
      rw [hr, hr, hp]
  · intro x
    obtain ⟨y, hy⟩ := ha.2 (l' x)
    obtain ⟨z, hz⟩ := hb.2 (r' x)
    have w : s y = t z := by
      apply hc
      rw [hs, ht, hy, hz]
      exact ConcreteCategory.congr_hom h'.w x
    obtain ⟨u, hu, hv⟩ := Types.exists_of_isPullback h y z w
    refine ⟨u, Types.ext_of_isPullback h' ?_ ?_⟩
    · rw [← hl, hu, hy]
    · rw [← hr, hv, hz]

theorem bijective_of_globes {T U : TupleSystem.{v}} (f : T.presheaf ⟶ U.presheaf)
    (q : ℕ) (hg : ∀ k, k ≤ q → Function.Bijective (f.app (op (Shape.globe k))))
    (S : Shape) (hS : S.height ≤ q) : Function.Bijective (f.app (op S)) := by
  cases S with
  | mk k table =>
    induction table with
    | globe k => exact hg k hS
    | @attach last tab b h hl hr ih =>
      have htab : (Shape.height ⟨last, tab⟩) ≤ q := (max_le_iff.mp hS).1
      have hh : h ≤ q := (max_le_iff.mp hS).2
      apply bijective_pullback_map
        (T.presheaf.map (Shape.inl ⟨last, tab⟩ b h hl hr).op)
        (T.presheaf.map (Shape.inr ⟨last, tab⟩ b h hl hr).op)
        (T.presheaf.map (Shape.seam ⟨last, tab⟩ hl).op)
        (T.presheaf.map (Shape.face hr false).op)
        (U.presheaf.map (Shape.inl ⟨last, tab⟩ b h hl hr).op)
        (U.presheaf.map (Shape.inr ⟨last, tab⟩ b h hl hr).op)
        (U.presheaf.map (Shape.seam ⟨last, tab⟩ hl).op)
        (U.presheaf.map (Shape.face hr false).op)
        (T.sums _ b h hl hr) (U.sums _ b h hl hr)
        _ (f.app (op ⟨last, tab⟩)) (f.app (op (Shape.globe h)))
        (f.app (op (Shape.globe b)))
      · exact f.naturality _
      · exact f.naturality _
      · exact f.naturality _
      · exact f.naturality _
      · exact ih htab
      · exact hg h hh
      · exact (hg b (Nat.le_trans (Nat.le_of_lt hr) hh)).1

end TupleSystem

end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularSet

def cutoffLow (X : GlobularSet.{u}) {q n : ℕ} (h : n ≤ q) :
    (X.cutoff q).Cell n ≃ X.Cell n := Equiv.cast (X.cutoffCell_low h)

def cutoffHigh (X : GlobularSet.{u}) {q n : ℕ} (h : q < n) :
    (X.cutoff q).Cell n ≃ X.Boundary (q+1) :=
  Equiv.cast (X.cutoffCell_high (Nat.not_le_of_gt h))

theorem cutoffFace_high (X : GlobularSet.{u}) {q n : ℕ} (h : q < n) (side) :
    HEq (X.cutoffFace q n side) (_root_.id : X.Boundary (q+1) → _) := by
  have hn : ¬ n+1 ≤ q := by omega
  have hne : n ≠ q := by omega
  simp only [cutoffFace, dite_eq_right hn, dite_eq_right hne]
  exact cast_heq _ _

private theorem coord_face {A B A' B' : Type u} (e : A ≃ A') (f : B ≃ B')
    (he : ∀ x, HEq (e x) x) (hf : ∀ x, HEq (f x) x)
    (g : A → B) (g' : A' → B') (hg : HEq g g') (x : A) :
    f (g x) = g' (e x) := by
  have ha : A = A' := (type_eq_of_heq (he x)).symm
  have hb : B = B' := (type_eq_of_heq (hf (g x))).symm
  cases ha; cases hb
  rw [eq_of_heq (hf (g x)), eq_of_heq hg, eq_of_heq (he x)]

theorem cutoffLow_face (X : GlobularSet.{u}) {q n : ℕ} (h : n+1 ≤ q)
    (side : Bool) (x : (X.cutoff q).Cell (n+1)) :
    X.cutoffLow (Nat.le_trans (Nat.le_succ n) h) (X.cutoffFace q n side x) =
      (if side then X.target n else X.source n) (X.cutoffLow h x) :=
  coord_face _ _ (fun _ => cast_heq _ _) (fun _ => cast_heq _ _)
    _ _ (X.cutoffFace_low h side) x

theorem cutoff_seam_face (X : GlobularSet.{u}) (q : ℕ) (side : Bool)
    (x : (X.cutoff q).Cell (q+1)) :
    X.cutoffLow (q := q) le_rfl (X.cutoffFace q q side x) =
      (if side then (X.cutoffHigh (Nat.lt_succ_self q) x).1.2
        else (X.cutoffHigh (Nat.lt_succ_self q) x).1.1) :=
  coord_face _ _ (fun _ => cast_heq _ _) (fun _ => cast_heq _ _)
    _ _ (X.cutoffFace_seam q side) x

theorem cutoff_high_face (X : GlobularSet.{u}) {q n : ℕ} (h : q < n)
    (side : Bool) (x : (X.cutoff q).Cell (n+1)) :
    X.cutoffHigh h (X.cutoffFace q n side x) =
      X.cutoffHigh (Nat.lt_trans h (Nat.lt_succ_self n)) x :=
  coord_face _ _ (fun _ => cast_heq _ _) (fun _ => cast_heq _ _)
    _ _ (X.cutoffFace_high h side) x

theorem cutoffLow_parallel (X : GlobularSet.{u}) {q n : ℕ} (h : n ≤ q)
    (x y : (X.cutoff q).Cell n) :
    (X.cutoff q).Parallel n x y ↔ X.Parallel n (X.cutoffLow h x) (X.cutoffLow h y) := by
  cases n with
  | zero => rfl
  | succ n =>
    change (_ = _ ∧ _ = _) ↔ (_ = _ ∧ _ = _)
    have hs z := X.cutoffLow_face h false z
    have ht z := X.cutoffLow_face h true z
    change ∀ z, X.cutoffLow _ ((X.cutoff q).source n z) = X.source n (X.cutoffLow h z) at hs
    change ∀ z, X.cutoffLow _ ((X.cutoff q).target n z) = X.target n (X.cutoffLow h z) at ht
    constructor
    · intro ⟨a, b⟩
      exact ⟨by rw [← hs, ← hs, a], by rw [← ht, ← ht, b]⟩
    · intro ⟨a, b⟩
      exact ⟨(X.cutoffLow _).injective (by rw [hs, hs, a]),
        (X.cutoffLow _).injective (by rw [ht, ht, b])⟩

theorem cutoff_boundary_seam_bijective (X : GlobularSet.{u}) (q : ℕ) :
    Function.Bijective ((X.cutoff q).boundary (q+1)) := by
  constructor
  · intro x y h
    apply (X.cutoffHigh (Nat.lt_succ_self q)).injective
    apply Subtype.ext
    apply Prod.ext
    · have hs := congrArg (fun b : (X.cutoff q).Boundary (q+1) =>
        X.cutoffLow (q := q) le_rfl b.1.1) h
      change X.cutoffLow _ (X.cutoffFace q q false x) =
        X.cutoffLow _ (X.cutoffFace q q false y) at hs
      rw [X.cutoff_seam_face q false x, X.cutoff_seam_face q false y] at hs
      exact hs
    · have ht := congrArg (fun b : (X.cutoff q).Boundary (q+1) =>
        X.cutoffLow (q := q) le_rfl b.1.2) h
      change X.cutoffLow _ (X.cutoffFace q q true x) =
        X.cutoffLow _ (X.cutoffFace q q true y) at ht
      rw [X.cutoff_seam_face q true x, X.cutoff_seam_face q true y] at ht
      exact ht
  · intro b
    let c : X.Boundary (q+1) :=
      ⟨(X.cutoffLow le_rfl b.1.1, X.cutoffLow le_rfl b.1.2),
        (X.cutoffLow_parallel le_rfl _ _).mp b.2⟩
    refine ⟨(X.cutoffHigh (Nat.lt_succ_self q)).symm c, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · apply (X.cutoffLow (q := q) le_rfl).injective
      change X.cutoffLow _ (X.cutoffFace q q false _) = _
      rw [X.cutoff_seam_face]
      change (X.cutoffHigh (Nat.lt_succ_self q)
        ((X.cutoffHigh (Nat.lt_succ_self q)).symm c)).1.1 = c.1.1
      exact congrArg (fun b : X.Boundary (q+1) => b.1.1)
        ((X.cutoffHigh (Nat.lt_succ_self q)).apply_symm_apply c)
    · apply (X.cutoffLow (q := q) le_rfl).injective
      change X.cutoffLow _ (X.cutoffFace q q true _) = _
      rw [X.cutoff_seam_face]
      change (X.cutoffHigh (Nat.lt_succ_self q)
        ((X.cutoffHigh (Nat.lt_succ_self q)).symm c)).1.2 = c.1.2
      exact congrArg (fun b : X.Boundary (q+1) => b.1.2)
        ((X.cutoffHigh (Nat.lt_succ_self q)).apply_symm_apply c)

theorem cutoff_boundary_bijective (X : GlobularSet.{u}) (q j : ℕ) (hj : q < j) :
    Function.Bijective ((X.cutoff q).boundary j) := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases h : j = q
    · subst j; exact X.cutoff_boundary_seam_bijective q
    have hq : q < j := by omega
    have hs (x : (X.cutoff q).Cell (j+1)) :
        X.cutoffHigh hq ((X.cutoff q).source j x) =
          X.cutoffHigh (Nat.lt_trans hq (Nat.lt_succ_self j)) x :=
      X.cutoff_high_face hq false x
    have ht (x : (X.cutoff q).Cell (j+1)) :
        X.cutoffHigh hq ((X.cutoff q).target j x) =
          X.cutoffHigh (Nat.lt_trans hq (Nat.lt_succ_self j)) x :=
      X.cutoff_high_face hq true x
    constructor
    · intro a b hab
      apply (X.cutoffHigh (Nat.lt_trans hq (Nat.lt_succ_self j))).injective
      rw [← hs, ← hs]
      exact congrArg (fun c : (X.cutoff q).Boundary (j+1) =>
        X.cutoffHigh hq c.1.1) hab
    · intro b
      have w : b.1.1 = b.1.2 := (ih hq).1
        (((X.cutoff q).parallel_iff_boundary_eq j _ _).mp b.2)
      let z := (X.cutoffHigh (Nat.lt_trans hq (Nat.lt_succ_self j))).symm
        (X.cutoffHigh hq b.1.1)
      refine ⟨z, Subtype.ext (Prod.ext ?_ ?_)⟩
      · apply (X.cutoffHigh hq).injective
        exact (hs z).trans (Equiv.apply_symm_apply _ _)
      · apply (X.cutoffHigh hq).injective
        exact (ht z).trans ((Equiv.apply_symm_apply _ _).trans (congrArg _ w))


theorem faceMap_parallel (X : GlobularSet.{u}) {q n : ℕ} (h : q < n) (x : X.Cell n) :
    X.Parallel q (X.faceMap h false x) (X.faceMap h true x) := by
  cases q with
  | zero => trivial
  | succ q =>
    constructor
    · simpa only [faceMap_succ, Bool.false_eq_true, ↓reduceIte] using (X.faceMap_comp (Nat.lt_succ_self q) h false false x).symm.trans
        (X.faceMap_comp (Nat.lt_succ_self q) h false true x)
    · simpa only [faceMap_succ, ↓reduceIte] using (X.faceMap_comp (Nat.lt_succ_self q) h true false x).symm.trans
        (X.faceMap_comp (Nat.lt_succ_self q) h true true x)

def cutoffUnitCell (X : GlobularSet.{u}) (q n : ℕ) (x : X.Cell n) : (X.cutoff q).Cell n :=
  if h : n ≤ q then (X.cutoffLow h).symm x
  else (X.cutoffHigh (Nat.lt_of_not_ge h)).symm
    ⟨(X.faceMap (Nat.lt_of_not_ge h) false x, X.faceMap (Nat.lt_of_not_ge h) true x),
      X.faceMap_parallel (Nat.lt_of_not_ge h) x⟩

@[simp]
theorem cutoffUnitCell_low (X : GlobularSet.{u}) {q n : ℕ} (h : n ≤ q) (x : X.Cell n) :
    X.cutoffLow h (X.cutoffUnitCell q n x) = x := by
  unfold cutoffUnitCell
  rw [dite_eq_left h]
  exact (X.cutoffLow h).apply_symm_apply x

@[simp]
theorem cutoffUnitCell_high (X : GlobularSet.{u}) {q n : ℕ} (h : q < n) (x : X.Cell n) :
    X.cutoffHigh h (X.cutoffUnitCell q n x) =
      ⟨(X.faceMap h false x, X.faceMap h true x), X.faceMap_parallel h x⟩ := by
  unfold cutoffUnitCell
  rw [dite_eq_right (Nat.not_le_of_gt h)]
  exact (X.cutoffHigh h).apply_symm_apply _

theorem cutoffUnitCell_face (X : GlobularSet.{u}) (q n : ℕ) (side : Bool)
    (x : X.Cell (n+1)) :
    X.cutoffUnitCell q n ((if side then X.target n else X.source n) x) =
      X.cutoffFace q n side (X.cutoffUnitCell q (n+1) x) := by
  by_cases h : n+1 ≤ q
  · apply (X.cutoffLow (Nat.le_trans (Nat.le_succ n) h)).injective
    rw [X.cutoffLow_face h side, X.cutoffUnitCell_low, X.cutoffUnitCell_low]
  · by_cases hn : n = q
    · subst n
      apply (X.cutoffLow (q := q) le_rfl).injective
      rw [X.cutoff_seam_face, X.cutoffUnitCell_low, X.cutoffUnitCell_high]
      cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, faceMap_succ]
    · have hq : q < n := by omega
      apply (X.cutoffHigh hq).injective
      rw [X.cutoff_high_face hq side, X.cutoffUnitCell_high, X.cutoffUnitCell_high]
      apply Subtype.ext
      apply Prod.ext
      · change X.faceMap hq false ((if side then X.target n else X.source n) x) =
          X.faceMap (Nat.lt_trans hq (Nat.lt_succ_self n)) false x
        rw [X.faceMap_source hq false]
        cases side
        · rfl
        · exact (X.faceMap_target hq false x).symm
      · change X.faceMap hq true ((if side then X.target n else X.source n) x) =
          X.faceMap (Nat.lt_trans hq (Nat.lt_succ_self n)) true x
        rw [X.faceMap_source hq true]
        cases side
        · rfl
        · exact (X.faceMap_target hq true x).symm

def cutoffUnit (X : GlobularSet.{u}) (q : ℕ) : Hom X (X.cutoff q) where
  app := X.cutoffUnitCell q
  source_app n x := X.cutoffUnitCell_face q n false x
  target_app n x := X.cutoffUnitCell_face q n true x

theorem cutoffUnit_bijective (X : GlobularSet.{u}) {q n : ℕ} (h : n ≤ q) :
    Function.Bijective ((X.cutoffUnit q).app n) := by
  have w : (X.cutoffUnit q).app n = (X.cutoffLow h).symm := by
    funext x
    apply (X.cutoffLow h).injective
    exact (X.cutoffUnitCell_low h x).trans ((X.cutoffLow h).apply_symm_apply x).symm
  rw [w]
  exact (X.cutoffLow h).symm.bijective

theorem Hom.evalFace_app {X Y : GlobularSet.{u}} (f : Hom X Y)
    {k j : ℕ} (a : Globe.Face k j) (x : X.Cell j) :
    f.app k (X.evalFace a x) = Y.evalFace a (f.app j x) := by
  cases a with
  | id => rfl
  | @face j h side =>
    change f.app k (X.faceMap h side x) = Y.faceMap h side (f.app j x)
    induction j, h using Nat.le_induction with
    | base =>
      simp only [faceMap_succ]
      cases side
      · exact f.source_app k x
      · exact f.target_app k x
    | succ j h ih =>
      rw [X.faceMap_source h side, Y.faceMap_source h side, ← f.source_app]
      exact ih (X.source j x)

def Hom.presheafMap {X Y : GlobularSet.{u}} (f : Hom X Y) : X.presheaf ⟶ Y.presheaf where
  app n := TypeCat.ofHom (f.app n.unop.dim)
  naturality _ _ a := ConcreteCategory.hom_ext _ _ (f.evalFace_app a.unop)

end GlobularSet

namespace GlobularPresheaf

noncomputable def tupleCellEquiv (X : GlobularPresheaf.{v}) (n : ℕ) :
    X.tuples.presheaf.obj (op (Shape.globe n)) ≃ X.obj (op (Globe.mk n)) where
  toFun f := f.app (op (Globe.mk n)) ⟨⟨𝟙 (Globe.mk n)⟩⟩
  invFun x :=
    { app k := TypeCat.ofHom (fun f => X.map f.down.down.op x)
      naturality k l f := by
        apply ConcreteCategory.hom_ext
        intro g
        change X.map (g.down.down.op ≫ f) x = X.map f (X.map g.down.down.op x)
        rw [X.map_comp]
        rfl }
  left_inv f := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro g
    let e : (Shape.liftedRealization.obj (Shape.globe n)).obj (op (Globe.mk n)) :=
      ⟨⟨𝟙 (Globe.mk n)⟩⟩
    have h := ConcreteCategory.congr_hom (f.naturality g.down.down.op) e
    change X.map g.down.down.op (f.app (op (Globe.mk n)) e) = f.app k g
    change f.app k ⟨⟨g.down.down ≫ 𝟙 (Globe.mk n)⟩⟩ =
      X.map g.down.down.op (f.app (op (Globe.mk n)) e) at h
    exact h.symm.trans (congrArg (fun t => f.app k t)
      (show (⟨⟨g.down.down ≫ 𝟙 (Globe.mk n)⟩⟩ :
        (Shape.liftedRealization.obj (Shape.globe n)).obj k) = g from
        by apply ULift.ext; apply ULift.ext; exact Category.comp_id _))
  right_inv x := by
    change X.map (𝟙 _) x = x
    rw [X.map_id]
    rfl

noncomputable def tuplesMap {X Y : GlobularPresheaf.{v}} (f : X ⟶ Y) :
    X.tuples.presheaf ⟶ Y.tuples.presheaf :=
  Functor.whiskerLeft Shape.liftedRealization.op (yoneda.map f)

@[simp]
theorem tupleCellEquiv_map {X Y : GlobularPresheaf.{v}} (f : X ⟶ Y) (n : ℕ)
    (x : X.tuples.presheaf.obj (op (Shape.globe n))) :
    Y.tupleCellEquiv n ((tuplesMap f).app (op (Shape.globe n)) x) =
      f.app (op (Globe.mk n)) (X.tupleCellEquiv n x) := rfl

theorem tupleCellEquiv_face (X : GlobularPresheaf.{v}) {m n : ℕ} (h : m < n)
    (side : Bool) (x : X.tuples.presheaf.obj (op (Shape.globe n))) :
    X.tupleCellEquiv m (X.tuples.presheaf.map (Shape.face h side).op x) =
      X.map (Globe.face h side).op (X.tupleCellEquiv n x) := by
  let e : (Shape.liftedRealization.obj (Shape.globe n)).obj (op (Globe.mk n)) :=
    ⟨⟨𝟙 (Globe.mk n)⟩⟩
  have w := ConcreteCategory.congr_hom (x.naturality (Globe.face h side).op) e
  change x.app (op (Globe.mk m)) ⟨⟨𝟙 (Globe.mk m) ≫ Globe.face h side⟩⟩ =
    X.map (Globe.face h side).op (x.app (op (Globe.mk n)) e)
  change x.app (op (Globe.mk m)) ⟨⟨Globe.face h side ≫ 𝟙 (Globe.mk n)⟩⟩ =
    X.map (Globe.face h side).op (x.app (op (Globe.mk n)) e) at w
  have hi := congrArg (fun a : Globe.mk m ⟶ Globe.mk n =>
    x.app (op (Globe.mk m)) ⟨⟨a⟩⟩) (Category.id_comp (Globe.face h side))
  have hc := congrArg (fun a : Globe.mk m ⟶ Globe.mk n =>
    x.app (op (Globe.mk m)) ⟨⟨a⟩⟩) (Category.comp_id (Globe.face h side))
  exact hi.trans (hc.symm.trans w)

noncomputable def tupleUnderlyingMap (X : GlobularPresheaf.{v}) :
    GlobularSet.Hom X.tuples.underlying X.underlying where
  app := fun n => X.tupleCellEquiv n
  source_app n x := X.tupleCellEquiv_face (Nat.lt_succ_self n) false x
  target_app n x := X.tupleCellEquiv_face (Nat.lt_succ_self n) true x

theorem tuplesMap_bijective_globe {X Y : GlobularPresheaf.{v}} (f : X ⟶ Y)
    (n : ℕ) (h : Function.Bijective (f.app (op (Globe.mk n)))) :
    Function.Bijective ((tuplesMap f).app (op (Shape.globe n))) := by
  have w : (tuplesMap f).app (op (Shape.globe n)) =
      (Y.tupleCellEquiv n).symm ∘ f.app (op (Globe.mk n)) ∘ X.tupleCellEquiv n := by
    funext x
    apply (Y.tupleCellEquiv n).injective
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using tupleCellEquiv_map f n x
  rw [w]
  exact (Y.tupleCellEquiv n).symm.bijective.comp (h.comp (X.tupleCellEquiv n).bijective)

end GlobularPresheaf

end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularSet

theorem Hom.reflects_parallel {X Y : GlobularSet.{u}} (f : Hom X Y)
    (hf : ∀ n, Function.Injective (f.app n)) {n : ℕ} {x y : X.Cell n}
    (h : Y.Parallel n (f.app n x) (f.app n y)) : X.Parallel n x y := by
  cases n with
  | zero => trivial
  | succ n =>
    exact ⟨hf n (by rw [f.source_app, f.source_app]; exact h.1),
      hf n (by rw [f.target_app, f.target_app]; exact h.2)⟩

theorem Hom.boundaryMap_bijective {X Y : GlobularSet.{u}} (f : Hom X Y)
    (hf : ∀ n, Function.Bijective (f.app n)) (n : ℕ) :
    Function.Bijective (f.boundaryMap n) := by
  cases n with
  | zero =>
    change Function.Bijective (fun _ : PUnit => (PUnit.unit : PUnit))
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨PUnit.unit, rfl⟩⟩
  | succ n =>
    constructor
    · intro x y h
      have hv := congrArg Subtype.val h
      exact Subtype.ext (Prod.ext ((hf n).1 (congrArg Prod.fst hv))
        ((hf n).1 (congrArg Prod.snd hv)))
    · intro b
      obtain ⟨x, hx⟩ := (hf n).2 b.1.1
      obtain ⟨y, hy⟩ := (hf n).2 b.1.2
      have hp : X.Parallel n x y := f.reflects_parallel (fun k => (hf k).1)
        (by rw [hx, hy]; exact b.2)
      exact ⟨⟨(x,y), hp⟩, Subtype.ext (Prod.ext hx hy)⟩

theorem Hom.boundary_bijective_iff {X Y : GlobularSet.{u}} (f : Hom X Y)
    (hf : ∀ n, Function.Bijective (f.app n)) (n : ℕ) :
    Function.Bijective (X.boundary n) ↔ Function.Bijective (Y.boundary n) := by
  have w : f.boundaryMap n ∘ X.boundary n = Y.boundary n ∘ f.app n := by
    funext x; exact f.boundary_app n x
  constructor
  · intro h
    have hb := (f.boundaryMap_bijective hf n).comp h
    rw [w] at hb
    exact (Function.Bijective.of_comp_iff _ (hf n)).mp hb
  · intro h
    have hb := h.comp (hf n)
    rw [← w] at hb
    constructor
    · exact fun _ _ hxy => hb.1 (congrArg (f.boundaryMap n) hxy)
    · intro b
      obtain ⟨x, hx⟩ := hb.2 (f.boundaryMap n b)
      exact ⟨x, (f.boundaryMap_bijective hf n).1 hx⟩

end GlobularSet

namespace Shape

noncomputable def cellArrow (S : Shape) (k : Globeᵒᵖ) (x : S.realize.obj k) :
    globe k.unop.dim ⟶ S := uliftYonedaEquiv.symm x

theorem cellArrow_map (S : Shape) {k l : Globeᵒᵖ} (a : k ⟶ l) (x : S.realize.obj k) :
    S.cellArrow l (S.realize.map a x) =
      GlobularTheory.shapeGlobes.map a.unop ≫ S.cellArrow k x :=
  uliftYonedaEquiv_symm_map a x

theorem cellArrow_naturality {S R : Shape} (f : S ⟶ R) (k : Globeᵒᵖ)
    (x : S.realize.obj k) :
    R.cellArrow k (f.app k x) = S.cellArrow k x ≫ f :=
  (uliftYonedaEquiv_symm_comp x f).symm

theorem cellArrow_identity (n : ℕ) :
    (globe n).cellArrow (op (Globe.mk n)) ⟨𝟙 (Globe.mk n)⟩ = 𝟙 (globe n) := by
  apply uliftYonedaEquiv.injective
  simp only [cellArrow]
  rfl

end Shape

namespace TupleSystem

noncomputable def globularPresheaf (T : TupleSystem.{v}) : GlobularPresheaf.{v} :=
  GlobularTheory.shapeGlobes.op ⋙ T.presheaf

noncomputable def evaluation (T : TupleSystem.{v}) :
    T.presheaf ⟶ T.globularPresheaf.tuples.presheaf where
  app S := TypeCat.ofHom (fun x =>
    { app k := TypeCat.ofHom (fun s => T.presheaf.map (S.unop.cellArrow k s.down).op x)
      naturality k l a := by
        apply ConcreteCategory.hom_ext
        intro s
        change ULift.{v} (S.unop.realize.obj k) at s
        change T.presheaf.map
            (S.unop.cellArrow l (S.unop.realize.map a s.down)).op x =
          T.presheaf.map (GlobularTheory.shapeGlobes.map a.unop).op
            (T.presheaf.map (S.unop.cellArrow k s.down).op x)
        rw [Shape.cellArrow_map]
        exact ConcreteCategory.congr_hom (T.presheaf.map_comp _ _) x })
  naturality S R f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro s
    change ULift.{v} (R.unop.realize.obj k) at s
    change T.presheaf.map (R.unop.cellArrow k s.down).op (T.presheaf.map f x) =
      T.presheaf.map (S.unop.cellArrow k (f.unop.app k s.down)).op x
    rw [Shape.cellArrow_naturality]
    exact (ConcreteCategory.congr_hom (T.presheaf.map_comp _ _) x).symm

@[simp]
theorem evaluation_globe (T : TupleSystem.{v}) (n : ℕ)
    (x : T.presheaf.obj (op (Shape.globe n))) :
    T.globularPresheaf.tupleCellEquiv n ((T.evaluation.app (op (Shape.globe n))) x) = x := by
  change T.presheaf.map
    ((Shape.globe n).cellArrow (op (Globe.mk n)) ⟨𝟙 (Globe.mk n)⟩).op x = x
  rw [Shape.cellArrow_identity, op_id, T.presheaf.map_id]
  rfl

theorem evaluation_bijective_globe (T : TupleSystem.{v}) (n : ℕ) :
    Function.Bijective (T.evaluation.app (op (Shape.globe n))) := by
  have h : (fun x => T.evaluation.app (op (Shape.globe n)) x) =
      (T.globularPresheaf.tupleCellEquiv n).symm := by
    funext x
    apply (T.globularPresheaf.tupleCellEquiv n).injective
    exact (T.evaluation_globe n x).trans (Equiv.apply_symm_apply _ _).symm
  change Function.Bijective (fun x => T.evaluation.app (op (Shape.globe n)) x)
  rw [h]
  exact (T.globularPresheaf.tupleCellEquiv n).symm.bijective

theorem evaluation_bijective (T : TupleSystem.{v}) (S : Shape) :
    Function.Bijective (T.evaluation.app (op S)) :=
  bijective_of_globes T.evaluation S.height (fun k _ => T.evaluation_bijective_globe k) S le_rfl

end TupleSystem

namespace GlobularPresheaf

theorem underlying_evalFace (X : GlobularPresheaf.{u}) {k j : ℕ}
    (a : Globe.Face k j) (x : X.obj (op (Globe.mk j))) :
    X.underlying.evalFace a x = X.map (show Globe.mk k ⟶ Globe.mk j from a).op x := by
  cases a with
  | id =>
    change x = X.map (𝟙 _) x
    rw [X.map_id]
    rfl
  | @face j h side =>
    change X.underlying.faceMap h side x = X.map (Globe.face h side).op x
    induction j, h using Nat.le_induction with
    | base =>
      rw [GlobularSet.faceMap_succ]
      cases side <;> rfl
    | succ j h ih =>
      apply (X.underlying.faceMap_source h side x).trans
      apply (ih (X.underlying.source j x)).trans
      have w : Globe.face (Nat.lt_succ_of_lt h) side = Globe.face h side ≫ Globe.source j := rfl
      rw [w, op_comp, X.map_comp]
      rfl

def underlyingPresheafIso (X : GlobularPresheaf.{u}) : X.underlying.presheaf ≅ X where
  hom :=
    { app _ := 𝟙 _
      naturality k j a := by
        apply ConcreteCategory.hom_ext
        intro x
        exact X.underlying_evalFace a.unop x }
  inv :=
    { app _ := 𝟙 _
      naturality k j a := by
        apply ConcreteCategory.hom_ext
        intro x
        exact (X.underlying_evalFace a.unop x).symm }

end GlobularPresheaf

namespace GlobularSet

def presheafUnderlyingMap (X : GlobularSet.{u}) : Hom X.presheaf.underlying X where
  app _ := _root_.id
  source_app n x := by
    change X.faceMap (Nat.lt_succ_self n) false x = X.source n x
    rw [X.faceMap_succ]
    rfl
  target_app n x := by
    change X.faceMap (Nat.lt_succ_self n) true x = X.target n x
    rw [X.faceMap_succ]
    rfl

end GlobularSet

namespace TupleSystem

noncomputable def modelUnderlyingMap {C : GlobularTheory.{v}} (T : TupleSystem.{v})
    (a : GlobularTheory.Morphism C T.endTheory) :
    GlobularSet.Hom (T.model a).underlying T.underlying where
  app _ := _root_.id
  source_app n x := ConcreteCategory.congr_hom (a.map_base (Shape.source n)) x
  target_app n x := ConcreteCategory.congr_hom (a.map_base (Shape.target n)) x

end TupleSystem

namespace GlobularTheory.Model

theorem exists_cutoff {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (X : C.Model) (q : ℕ) :
    ∃ (R : C.Model) (η : X ⟶ R),
      (∀ n, n ≤ q → Function.Bijective ((underlyingMap η).app n)) ∧
      (∀ j, q < j → Function.Bijective (R.underlying.boundary j)) := by
  let G := X.tuples.globularPresheaf
  let Z := G.underlying.cutoff q
  let U := Z.presheaf.tuples
  let g : G ⟶ Z.presheaf := G.underlyingPresheafIso.inv ≫
    (G.underlying.cutoffUnit q).presheafMap
  let f : X.tuples.presheaf ⟶ U.presheaf := X.tuples.evaluation ≫
    GlobularPresheaf.tuplesMap g
  have hlow (S : Shape) (hS : S.height ≤ q) : Function.Bijective (f.app (op S)) := by
    apply TupleSystem.bijective_of_globes f q _ S hS
    intro k hk
    exact (GlobularPresheaf.tuplesMap_bijective_globe g k
      (G.underlying.cutoffUnit_bijective hk)).comp (X.tuples.evaluation_bijective_globe k)
  have hhigh (j : ℕ) (hj : q < j) : Function.Bijective (U.underlying.boundary j) := by
    apply ((Z.presheaf.tupleUnderlyingMap).boundary_bijective_iff
      (fun k => (Z.presheaf.tupleCellEquiv k).bijective) j).mpr
    apply (Z.presheafUnderlyingMap.boundary_bijective_iff
      (fun _ => Function.bijective_id) j).mpr
    exact G.underlying.cutoff_boundary_bijective q j hj
  obtain ⟨a, ha⟩ := hC.1.some.lift (TupleSystem.relativeSource f)
    (TupleSystem.relativeSource_liftsFillers f q hlow hhigh) X.interpretation
  let R := U.model (a.comp (TupleSystem.relativeTarget f))
  let η : X ⟶ R :=
    { app S := f.app (op S.unop.shape)
      naturality S T g := by
        have w := (a.map g.unop).w
        have hm := congrArg (fun z : Morphism C X.tuples.endTheory => z.map g.unop) ha
        change (a.map g.unop).left = X.presheaf.map g at hm
        rw [hm] at w
        exact w }
  refine ⟨R, η, ?_, ?_⟩
  · intro k hk
    exact hlow (Shape.globe k) hk
  · intro j hj
    exact ((U.modelUnderlyingMap (a.comp (TupleSystem.relativeTarget f))).boundary_bijective_iff
      (fun _ => Function.bijective_id) j).mpr (hhigh j hj)

end GlobularTheory.Model

end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularSet

structure FactorStage {X R Y : GlobularSet.{v}} (η : Hom X R) (f : Hom X Y) (n : ℕ) where
  app : ∀ k, k ≤ n → R.Cell k → Y.Cell k
  source_app : ∀ k (h : k+1 ≤ n) x,
    app k (by omega) (R.source k x) = Y.source k (app (k+1) h x)
  target_app : ∀ k (h : k+1 ≤ n) x,
    app k (by omega) (R.target k x) = Y.target k (app (k+1) h x)
  fac : ∀ k (h : k ≤ n) x, app k h (η.app k x) = f.app k x

namespace FactorStage

variable {X R Y : GlobularSet.{v}} {η : Hom X R} {f : Hom X Y}

noncomputable def zero (h : Function.Bijective (η.app 0)) : FactorStage η f 0 where
  app k hk x := by
    have e : k = 0 := by omega
    subst k
    exact f.app 0 ((Equiv.ofBijective _ h).symm x)
  source_app k hk := by omega
  target_app k hk := by omega
  fac k hk x := by
    have e : k = 0 := by omega
    subst k
    exact congrArg (f.app 0) ((Equiv.ofBijective _ h).symm_apply_apply x)

def nextBoundary {n : ℕ} (a : FactorStage η f n) (x : R.Cell (n+1)) :
    Y.Boundary (n+1) :=
  ⟨(a.app n le_rfl (R.source n x), a.app n le_rfl (R.target n x)), by
    cases n with
    | zero => trivial
    | succ n =>
      constructor
      · rw [← a.source_app n le_rfl, ← a.source_app n le_rfl, R.source_source]
      · rw [← a.target_app n le_rfl, ← a.target_app n le_rfl, R.target_source]⟩

def extend {n : ℕ} (a : FactorStage η f n) (z : R.Cell (n+1) → Y.Cell (n+1))
    (hs : ∀ x, a.app n le_rfl (R.source n x) = Y.source n (z x))
    (ht : ∀ x, a.app n le_rfl (R.target n x) = Y.target n (z x))
    (hf : ∀ x, z (η.app (n+1) x) = f.app (n+1) x) : FactorStage η f (n+1) where
  app k hk x := if h : k ≤ n then a.app k h x else by
    have e : k = n+1 := by omega
    subst k
    exact z x
  source_app k hk x := by
    dsimp only
    split_ifs with h h'
    · exact a.source_app k h' x
    · have e : k = n := by omega
      subst k
      exact hs x
    · omega
    · omega
  target_app k hk x := by
    dsimp only
    split_ifs with h h'
    · exact a.target_app k h' x
    · have e : k = n := by omega
      subst k
      exact ht x
    · omega
    · omega
  fac k hk x := by
    dsimp only
    split_ifs with h
    · exact a.fac k h x
    · have e : k = n+1 := by omega
      subst k
      exact hf x

@[simp] theorem extend_old {n : ℕ} (a : FactorStage η f n) (z hs ht hf)
    (k : ℕ) (hk : k ≤ n) (x : R.Cell k) :
    (a.extend z hs ht hf).app k (by omega) x = a.app k hk x := by
  simp only [extend, dite_eq_left hk]

theorem exists_extend {n q : ℕ} (a : FactorStage η f n)
    (hη : ∀ k, k ≤ q → Function.Bijective (η.app k))
    (hY : ∀ j, q < j → Function.Bijective (Y.boundary j)) :
    ∃ b : FactorStage η f (n+1), ∀ k (hk : k ≤ n) x,
      b.app k (by omega) x = a.app k hk x := by
  classical
  by_cases hn : n+1 ≤ q
  · let e := Equiv.ofBijective (η.app (n+1)) (hη _ hn)
    let z (x : R.Cell (n+1)) := f.app (n+1) (e.symm x)
    have hs x : a.app n le_rfl (R.source n x) = Y.source n (z x) := by
      rw [show x = η.app (n+1) (e.symm x) from (e.apply_symm_apply x).symm,
        ← η.source_app, a.fac, f.source_app]
      exact congrArg (fun x => Y.source n (f.app (n+1) x)) (e.symm_apply_apply _).symm
    have ht x : a.app n le_rfl (R.target n x) = Y.target n (z x) := by
      rw [show x = η.app (n+1) (e.symm x) from (e.apply_symm_apply x).symm,
        ← η.target_app, a.fac, f.target_app]
      exact congrArg (fun x => Y.target n (f.app (n+1) x)) (e.symm_apply_apply _).symm
    have hf x : z (η.app (n+1) x) = f.app (n+1) x :=
      congrArg (f.app (n+1)) (e.symm_apply_apply x)
    exact ⟨a.extend z hs ht hf, fun k hk x => a.extend_old z hs ht hf k hk x⟩
  · let e := Equiv.ofBijective (Y.boundary (n+1)) (hY _ (by omega))
    let z (x : R.Cell (n+1)) := e.symm (a.nextBoundary x)
    have hb x : Y.boundary (n+1) (z x) = a.nextBoundary x := e.apply_symm_apply _
    have hs x : a.app n le_rfl (R.source n x) = Y.source n (z x) :=
      (congrArg (fun b => b.1.1) (hb x)).symm
    have ht x : a.app n le_rfl (R.target n x) = Y.target n (z x) :=
      (congrArg (fun b => b.1.2) (hb x)).symm
    have hf x : z (η.app (n+1) x) = f.app (n+1) x := by
      apply e.injective
      change Y.boundary (n+1) (z _) = Y.boundary (n+1) _
      rw [hb, ← f.boundary_app]
      apply Subtype.ext
      apply Prod.ext
      · change a.app n _ (R.source n (η.app (n+1) x)) = f.app n (X.source n x)
        rw [← η.source_app, a.fac]
      · change a.app n _ (R.target n (η.app (n+1) x)) = f.app n (X.target n x)
        rw [← η.target_app, a.fac]
    exact ⟨a.extend z hs ht hf, fun k hk x => a.extend_old z hs ht hf k hk x⟩

end FactorStage

theorem existsUnique_factor_low_bijective {X R Y : GlobularSet.{v}}
    (η : Hom X R) (f : Hom X Y) (q : ℕ)
    (hη : ∀ k, k ≤ q → Function.Bijective (η.app k))
    (hY : ∀ j, q < j → Function.Bijective (Y.boundary j)) :
    ∃! g : Hom R Y, η.comp g = f := by
  classical
  let a : (n : ℕ) → FactorStage η f n := fun n => Nat.rec
    (FactorStage.zero (hη 0 (Nat.zero_le _)))
    (fun _ a => (a.exists_extend hη hY).choose) n
  have ha (n k : ℕ) (hk : k ≤ n) (x : R.Cell k) :
      (a (n+1)).app k (by omega) x = (a n).app k hk x :=
    (FactorStage.exists_extend (a n) hη hY).choose_spec k hk x
  let g : Hom R Y :=
    { app n := (a n).app n le_rfl
      source_app n x := by
        rw [← ha n n le_rfl]
        exact (a (n+1)).source_app n le_rfl x
      target_app n x := by
        rw [← ha n n le_rfl]
        exact (a (n+1)).target_app n le_rfl x }
  have hg : η.comp g = f := by
    ext n x
    exact (a n).fac n le_rfl x
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  ext n x
  induction n with
  | zero =>
    obtain ⟨y, rfl⟩ := (hη 0 (Nat.zero_le q)).2 x
    exact (congrArg (fun h : Hom X Y => h.app 0 y) hg').trans
      (congrArg (fun h : Hom X Y => h.app 0 y) hg).symm
  | succ n ih =>
    by_cases hn : n+1 ≤ q
    · obtain ⟨y, rfl⟩ := (hη (n+1) hn).2 x
      exact (congrArg (fun h : Hom X Y => h.app (n+1) y) hg').trans
        (congrArg (fun h : Hom X Y => h.app (n+1) y) hg).symm
    · apply (hY (n+1) (by omega)).1
      apply Subtype.ext
      apply Prod.ext
      · exact (g'.source_app n x).symm.trans ((ih _).trans (g.source_app n x))
      · exact (g'.target_app n x).symm.trans ((ih _).trans (g.target_app n x))

end GlobularSet

namespace TupleSystem

noncomputable def evaluationIso (T : TupleSystem.{v}) :
    T.presheaf ≅ T.globularPresheaf.tuples.presheaf :=
  NatIso.ofComponents
    (fun S => (Equiv.ofBijective (T.evaluation.app S) (T.evaluation_bijective S.unop)).toIso)
    (fun g => T.evaluation.naturality g)

theorem hom_ext_globes {T U : TupleSystem.{v}} (f g : T.presheaf ⟶ U.presheaf)
    (h : ∀ n, f.app (op (Shape.globe n)) = g.app (op (Shape.globe n))) : f = g := by
  apply NatTrans.ext
  funext S
  apply ConcreteCategory.hom_ext
  intro x
  apply (U.evaluation_bijective S.unop).1
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro z
  change U.presheaf.map (S.unop.cellArrow k z.down).op (f.app S x) =
    U.presheaf.map (S.unop.cellArrow k z.down).op (g.app S x)
  have hf := ConcreteCategory.congr_hom (f.naturality (S.unop.cellArrow k z.down).op) x
  have hg := ConcreteCategory.congr_hom (g.naturality (S.unop.cellArrow k z.down).op) x
  change f.app (op (Shape.globe k.unop.dim)) _ = _ at hf
  change g.app (op (Shape.globe k.unop.dim)) _ = _ at hg
  rw [h] at hf
  exact hf.symm.trans hg

noncomputable def mapFromUnderlying {T U : TupleSystem.{v}}
    (g : GlobularSet.Hom T.underlying U.underlying) : T.presheaf ⟶ U.presheaf :=
  T.evaluationIso.hom ≫ GlobularPresheaf.tuplesMap
    (T.globularPresheaf.underlyingPresheafIso.inv ≫ g.presheafMap ≫
      U.globularPresheaf.underlyingPresheafIso.hom) ≫ U.evaluationIso.inv

@[simp] theorem mapFromUnderlying_globe {T U : TupleSystem.{v}}
    (g : GlobularSet.Hom T.underlying U.underlying) (n : ℕ)
    (x : T.underlying.Cell n) :
    (mapFromUnderlying g).app (op (Shape.globe n)) x = g.app n x := by
  apply (U.evaluation_bijective_globe n).1
  change U.evaluationIso.hom.app (op (Shape.globe n))
    (U.evaluationIso.inv.app (op (Shape.globe n)) _) = _
  rw [Iso.inv_hom_id_app_apply]
  apply U.globularPresheaf.tupleCellEquiv n |>.injective
  have w := GlobularPresheaf.tupleCellEquiv_map
    (T.globularPresheaf.underlyingPresheafIso.inv ≫ g.presheafMap ≫
      U.globularPresheaf.underlyingPresheafIso.hom) n (T.evaluation.app _ x)
  apply w.trans
  change g.app n (T.globularPresheaf.tupleCellEquiv n (T.evaluation.app _ x)) =
    U.globularPresheaf.tupleCellEquiv n (U.evaluation.app _ (g.app n x))
  exact (congrArg (g.app n) (T.evaluation_globe n x)).trans
    (U.evaluation_globe n (g.app n x)).symm

end TupleSystem

namespace GlobularTheory.Model

theorem underlyingMap_injective {C : GlobularTheory.{v}} {X Y : C.Model} :
    Function.Injective (@underlyingMap _ X Y) := by
  intro f g h
  have w : (show X.tuples.presheaf ⟶ Y.tuples.presheaf from
      Functor.whiskerLeft C.toTheoryData.arity.op f) =
      Functor.whiskerLeft C.toTheoryData.arity.op g := by
    apply TupleSystem.hom_ext_globes
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun k : GlobularSet.Hom X.underlying Y.underlying => k.app n x) h
  apply NatTrans.ext
  funext S
  exact congrArg (fun k => k.app (op S.unop.shape)) w

end GlobularTheory.Model

end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularTheory.Model

def OperationCompatible {C : GlobularTheory.{v}} {R Y : C.Model}
    (g : R.tuples.presheaf ⟶ Y.tuples.presheaf) {S T : Shape} (u : C.Hom S T) : Prop :=
  ∀ x, g.app (op S) (R.eval u x) = Y.eval u (g.app (op T) x)

noncomputable def compatibleData {C : GlobularTheory.{v}} {R Y : C.Model}
    (g : R.tuples.presheaf ⟶ Y.tuples.presheaf) : TheoryData.{v} where
  Hom S T := {u : C.Hom S T // OperationCompatible g u}
  id S := ⟨C.id S, fun x => (congrArg (g.app (op S)) (R.eval_id x)).trans
      (Y.eval_id _).symm⟩
  comp {S _T U} a b := ⟨C.comp a.1 b.1, fun x =>
    (congrArg (g.app (op S)) (R.eval_comp a.1 b.1 x)).trans
      ((a.2 (R.eval b.1 x)).trans
        ((congrArg (Y.eval a.1) (b.2 x)).trans
          (Y.eval_comp a.1 b.1 (g.app (op U) x)).symm))⟩
  id_comp a := Subtype.ext (C.id_comp a.1)
  comp_id a := Subtype.ext (C.comp_id a.1)
  assoc a b c := Subtype.ext (C.assoc a.1 b.1 c.1)
  base u := ⟨C.base u, fun x => ConcreteCategory.congr_hom (g.naturality u.op) x⟩
  base_id S := Subtype.ext (C.base_id S)
  base_comp a b := Subtype.ext (C.base_comp a b)

noncomputable def compatibleTheory {C : GlobularTheory.{v}} {R Y : C.Model}
    (g : R.tuples.presheaf ⟶ Y.tuples.presheaf) : GlobularTheory.{v} where
  toTheoryData := compatibleData g
  sums S b h hl hr := by
    apply IsPushout.mk'
    · apply Subtype.ext
      exact (C.sums S b h hl hr).w
    · intro T a a' ha hb
      apply Subtype.ext
      apply (C.sums S b h hl hr).hom_ext (W := (⟨T.shape⟩ : C.Obj))
      · exact congrArg Subtype.val ha
      · exact congrArg Subtype.val hb
    · intro T a b' hab
      let d : C.Hom (S.attach b h hl hr) T.shape :=
        (C.sums S b h hl hr).desc (W := (⟨T.shape⟩ : C.Obj)) a.1 b'.1
          (congrArg Subtype.val hab)
      have hd₀ : C.comp (C.base (S.inl b h hl hr)) d = a.1 :=
        (C.sums S b h hl hr).inl_desc _ _ _
      have hd₁ : C.comp (C.base (S.inr b h hl hr)) d = b'.1 :=
        (C.sums S b h hl hr).inr_desc _ _ _
      have hd : OperationCompatible g d := by
        intro x
        apply Types.ext_of_isPullback (Y.sums S b h hl hr)
        · have w := ConcreteCategory.congr_hom
            (g.naturality (S.inl b h hl hr).op) (R.eval d x)
          change g.app (op S) (R.eval (C.base (S.inl b h hl hr)) (R.eval d x)) = _ at w
          have wr := (R.eval_comp (C.base (S.inl b h hl hr)) d x).symm.trans
            (congrArg (fun z => R.eval z x) hd₀)
          have wy := (Y.eval_comp (C.base (S.inl b h hl hr)) d
            (g.app (op T.shape) x)).symm.trans
            (congrArg (fun z => Y.eval z (g.app (op T.shape) x)) hd₀)
          exact w.symm.trans ((congrArg (g.app (op S)) wr).trans ((a.2 x).trans wy.symm))
        · have w := ConcreteCategory.congr_hom
            (g.naturality (S.inr b h hl hr).op) (R.eval d x)
          have wr := (R.eval_comp (C.base (S.inr b h hl hr)) d x).symm.trans
            (congrArg (fun z => R.eval z x) hd₁)
          have wy := (Y.eval_comp (C.base (S.inr b h hl hr)) d
            (g.app (op T.shape) x)).symm.trans
            (congrArg (fun z => Y.eval z (g.app (op T.shape) x)) hd₁)
          exact w.symm.trans ((congrArg (g.app (op (Shape.globe h))) wr).trans
            ((b'.2 x).trans wy.symm))
      exact ⟨⟨d, hd⟩, Subtype.ext hd₀, Subtype.ext hd₁⟩

noncomputable def compatibleProjection {C : GlobularTheory.{v}} {R Y : C.Model}
    (g : R.tuples.presheaf ⟶ Y.tuples.presheaf) : Morphism (compatibleTheory g) C where
  map u := u.1
  map_id _ := rfl
  map_comp _ _ := rfl
  map_base _ := rfl

theorem compatibleProjection_liftsFillers {C : GlobularTheory.{v}}
    {X R Y : C.Model} (η : X ⟶ R) (f : X ⟶ Y)
    (g : R.tuples.presheaf ⟶ Y.tuples.presheaf) (q : ℕ)
    (hη : ∀ k, k ≤ q → Function.Bijective ((underlyingMap η).app k))
    (hY : ∀ j, q < j → Function.Bijective (Y.underlying.boundary j))
    (hg : (Functor.whiskerLeft C.toTheoryData.arity.op η) ≫ g =
      Functor.whiskerLeft C.toTheoryData.arity.op f) :
    LiftsFillers (compatibleProjection g) := by
  intro p z hz
  have hnat : OperationCompatible g z := by
    intro x
    by_cases hn : p.n+1 ≤ q
    · have ht : Function.Bijective
          ((Functor.whiskerLeft C.toTheoryData.arity.op η).app (op p.arity)) :=
        TupleSystem.bijective_of_globes (T := X.tuples) (U := R.tuples)
          (Functor.whiskerLeft C.toTheoryData.arity.op η) q hη p.arity (p.height.trans hn)
      obtain ⟨x, rfl⟩ := ht.2 x
      have hηz := ConcreteCategory.congr_hom
        (η.naturality (show (⟨Shape.globe (p.n+1)⟩ : C.Obj) ⟶ ⟨p.arity⟩ from z).op) x
      have hfz := ConcreteCategory.congr_hom
        (f.naturality (show (⟨Shape.globe (p.n+1)⟩ : C.Obj) ⟶ ⟨p.arity⟩ from z).op) x
      have fac (S : Shape) (x : X.presheaf.obj (op (⟨S⟩ : C.Obj))) :
          g.app (op S) (η.app (op ⟨S⟩) x) = f.app (op ⟨S⟩) x :=
        ConcreteCategory.congr_hom (congrArg (fun k : X.tuples.presheaf ⟶ Y.tuples.presheaf => k.app (op S)) hg) x
      exact (congrArg (g.app (op (Shape.globe (p.n+1)))) hηz.symm).trans
        ((fac (Shape.globe (p.n+1)) (X.eval z x)).trans
          (hfz.trans (congrArg (Y.eval z) (fac p.arity x).symm)))
    · apply (hY (p.n+1) (by omega)).1
      apply Subtype.ext
      apply Prod.ext
      · have gs := ConcreteCategory.congr_hom
          (g.naturality (Shape.source p.n).op) (R.eval z x)
        have hs : C.comp (C.base (Shape.source p.n)) z = p.source.1 := hz.1
        have wr := (R.eval_comp (C.base (Shape.source p.n)) z x).symm.trans
          (congrArg (fun u => R.eval u x) hs)
        have wy := (Y.eval_comp (C.base (Shape.source p.n)) z (g.app (op p.arity) x)).symm.trans
          (congrArg (fun u => Y.eval u (g.app (op p.arity) x)) hs)
        exact gs.symm.trans ((congrArg (g.app (op (Shape.globe p.n))) wr).trans
          ((p.source.2 x).trans wy.symm))
      · have gt := ConcreteCategory.congr_hom
          (g.naturality (Shape.target p.n).op) (R.eval z x)
        have ht : C.comp (C.base (Shape.target p.n)) z = p.target.1 := hz.2
        have wr := (R.eval_comp (C.base (Shape.target p.n)) z x).symm.trans
          (congrArg (fun u => R.eval u x) ht)
        have wy := (Y.eval_comp (C.base (Shape.target p.n)) z (g.app (op p.arity) x)).symm.trans
          (congrArg (fun u => Y.eval u (g.app (op p.arity) x)) ht)
        exact gt.symm.trans ((congrArg (g.app (op (Shape.globe p.n))) wr).trans
          ((p.target.2 x).trans wy.symm))
  refine ⟨⟨z, hnat⟩, ?_, rfl⟩
  exact ⟨Subtype.ext hz.1, Subtype.ext hz.2⟩


theorem existsUnique_factor_coskeletal {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X R Y : C.Model} (η : X ⟶ R) (f : X ⟶ Y) (q : ℕ)
    (hη : ∀ k, k ≤ q → Function.Bijective ((underlyingMap η).app k))
    (hY : ∀ j, q < j → Function.Bijective (Y.underlying.boundary j)) :
    ∃! l : R ⟶ Y, η ≫ l = f := by
  obtain ⟨g₀, hg₀, hgUnique⟩ := GlobularSet.existsUnique_factor_low_bijective
    (underlyingMap η) (underlyingMap f) q hη hY
  let g : R.tuples.presheaf ⟶ Y.tuples.presheaf := TupleSystem.mapFromUnderlying (T := R.tuples) (U := Y.tuples) g₀
  have hg : (Functor.whiskerLeft C.toTheoryData.arity.op η) ≫ g =
      Functor.whiskerLeft C.toTheoryData.arity.op f := by
    apply TupleSystem.hom_ext_globes (T := X.tuples) (U := Y.tuples)
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    change (TupleSystem.mapFromUnderlying (T := R.tuples) (U := Y.tuples) g₀).app (op (Shape.globe n))
      ((underlyingMap η).app n x) = (underlyingMap f).app n x
    exact (TupleSystem.mapFromUnderlying_globe (T := R.tuples) (U := Y.tuples) g₀ n _).trans
      (congrArg (fun h : GlobularSet.Hom X.underlying Y.underlying => h.app n x) hg₀)
  obtain ⟨a, ha⟩ := hC.1.some.lift (compatibleProjection g)
    (compatibleProjection_liftsFillers η f g q hη hY hg) (Morphism.id C)
  have hav {S T : Shape} (u : C.Hom S T) : (a.map u).1 = u :=
    congrArg (fun k : Morphism C C => k.map u) ha
  let l : R ⟶ Y :=
    { app S := g.app (op S.unop.shape)
      naturality S T u := by
        apply ConcreteCategory.hom_ext
        intro x
        have w := (a.map u.unop).2 x
        exact (congrArg (g.app (op T.unop.shape))
          (congrArg (fun z => R.eval z x) (hav u.unop)).symm).trans
          (w.trans (congrArg (fun z => Y.eval z (g.app (op S.unop.shape) x)) (hav u.unop))) }
  have hl : η ≫ l = f := by
    apply NatTrans.ext
    funext S
    exact congrArg (fun k => k.app (op S.unop.shape)) hg
  have hlg : underlyingMap l = g₀ := by
    ext n x
    exact TupleSystem.mapFromUnderlying_globe (T := R.tuples) (U := Y.tuples) g₀ n x
  refine ⟨l, hl, ?_⟩
  intro l' hl'
  apply underlyingMap_injective
  apply Eq.trans _ hlg.symm
  apply hgUnique
  exact congrArg (fun k : X ⟶ Y => underlyingMap k) hl'

def IsCoskeletal {C : GlobularTheory.{v}} (X : C.Model) (q : ℕ) : Prop :=
  ∀ j, q < j → Function.Bijective (X.underlying.boundary j)

theorem exists_cutoff_reflection {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (X : C.Model) (q : ℕ) :
    ∃ (R : C.Model) (η : X ⟶ R),
      (∀ n, n ≤ q → Function.Bijective ((underlyingMap η).app n)) ∧
      R.IsCoskeletal q ∧
      ∀ (Y : C.Model), Y.IsCoskeletal q → ∀ f : X ⟶ Y, ∃! l : R ⟶ Y, η ≫ l = f := by
  obtain ⟨R, η, hlo, hhi⟩ := exists_cutoff hC X q
  exact ⟨R, η, hlo, hhi, fun _ hY f => existsUnique_factor_coskeletal hC η f q hlo hY⟩


def CoskeletalLocalMap {C : GlobularTheory.{v}} (q : ℕ) {X Y : C.Model}
    (i : X ⟶ Y) : Prop :=
  ∀ (Z : C.Model), Z.IsCoskeletal q → ∀ g : X ⟶ Z, ∃! h : Y ⟶ Z, i ≫ h = g

theorem coskeletalLocalMap_iff {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {X Y : C.Model} (i : X ⟶ Y) :
    CoskeletalLocalMap q i ↔
      ∀ k, k ≤ q → Function.Bijective ((underlyingMap i).app k) := by
  constructor
  · intro hi
    obtain ⟨RX, ηX, hX, hRX, uX⟩ := exists_cutoff_reflection hC X q
    obtain ⟨RY, ηY, hY, hRY, _⟩ := exists_cutoff_reflection hC Y q
    obtain ⟨g, hg, _⟩ := hi RX hRX ηX
    obtain ⟨a, ha, _⟩ := uX RY hRY (i ≫ ηY)
    obtain ⟨_, _, unique⟩ := hi RY hRY (i ≫ ηY)
    have hy : g ≫ a = ηY := (unique (g ≫ a)
      ((Category.assoc i g a).symm.trans ((congrArg (· ≫ a) hg).trans ha))).trans
      (unique ηY rfl).symm
    intro k hk
    constructor
    · intro x y h
      apply (hX k hk).1
      have fac := congrArg (fun f : X ⟶ RX => (underlyingMap f).app k) hg
      exact (congrFun fac x).symm.trans ((congrArg ((underlyingMap g).app k) h).trans
        (congrFun fac y))
    · intro y
      obtain ⟨x, hx⟩ := (hX k hk).2 ((underlyingMap g).app k y)
      refine ⟨x, (hY k hk).1 ?_⟩
      have fac := congrArg (fun f : X ⟶ RY => (underlyingMap f).app k x) ha
      have fac' := congrArg (fun f : Y ⟶ RY => (underlyingMap f).app k y) hy
      exact fac.symm.trans ((congrArg ((underlyingMap a).app k) hx).trans fac')
  · intro hi Z hZ g
    exact existsUnique_factor_coskeletal hC i g q hi hZ

theorem BoundaryAttachment.coskeletalLocalMap {C : GlobularTheory.{v}}
    {X Y : C.Model} {i : X ⟶ Y} (A : BoundaryAttachment i) (q : ℕ)
    (hA : ∀ k, q < A.dimension k) : CoskeletalLocalMap q i := by
  intro Z hZ g
  have cells : ∀ k, ∃! z, Z.underlying.boundary (A.dimension k) z =
      (underlyingMap g).boundaryMap _ (A.boundary k) := by
    intro k
    exact (hZ (A.dimension k) (hA k)).existsUnique _
  choose z hz uniqueCell using cells
  obtain ⟨h, hh, unique⟩ := A.universal Z g z hz
  refine ⟨h, hh.1, ?_⟩
  intro h' hh'
  apply unique h'
  refine ⟨hh', ?_⟩
  intro k
  apply uniqueCell
  rw [← (underlyingMap h').boundary_app, A.cell_boundary]
  simpa only [underlyingMap_comp, GlobularSet.Hom.boundaryMap_comp] using
    congrArg (fun f : X ⟶ Z => (underlyingMap f).boundaryMap _ (A.boundary k)) hh'

theorem BoundaryAttachment.low_bijective {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X Y : C.Model} {i : X ⟶ Y} (A : BoundaryAttachment i) (q : ℕ)
    (hA : ∀ k, q < A.dimension k) (j : ℕ) (hj : j ≤ q) :
    Function.Bijective ((underlyingMap i).app j) :=
  (coskeletalLocalMap_iff hC q i).1 (A.coskeletalLocalMap q hA) j hj

end GlobularTheory.Model

end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularSet

theorem source_bijective_of_coskeletal (X : GlobularSet.{u}) (q n : ℕ)
    (hX : ∀ j, q < j → Function.Bijective (X.boundary j)) (hn : q < n) :
    Function.Bijective (X.source n) := by
  have ht (z : X.Cell (n+1)) : X.source n z = X.target n z :=
    (hX n hn).1 ((X.parallel_iff_boundary_eq n _ _).1 (Joined.parallel ⟨z, rfl, rfl⟩))
  constructor
  · intro x y h
    apply (hX (n+1) (by omega)).1
    exact Subtype.ext (Prod.ext h ((ht x).symm.trans (h.trans (ht y))))
  · intro x
    have hp : X.Parallel n x x := by cases n <;> simp [Parallel]
    obtain ⟨z, hz⟩ := (hX (n+1) (by omega)).2 ⟨(x, x), hp⟩
    exact ⟨z, congrArg (fun b => b.1.1) hz⟩

end GlobularSet

namespace GlobularTheory.Model

@[simp] theorem cellEquiv_comp {C : GlobularTheory.{v}} {X Y : C.Model}
    (n : ℕ) (a : disk C n ⟶ X) (f : X ⟶ Y) :
    cellEquiv Y n (a ≫ f) = (underlyingMap f).app n (cellEquiv X n a) := rfl

@[simp] theorem cellEquiv_J {C : GlobularTheory.{v}} {X : C.Model}
    (n : ℕ) (a : disk C (n+1) ⟶ X) :
    cellEquiv X n (J C n ≫ a) = X.underlying.source n (cellEquiv X (n+1) a) := by
  exact (yonedaEquiv_naturality a
    (show (⟨Shape.globe n⟩ : C.Obj) ⟶ ⟨Shape.globe (n+1)⟩ from
      C.base (Shape.source n))).symm

theorem J_coskeletalLocalMap (C : GlobularTheory.{v}) (k n : ℕ) (hkn : k < n) :
    CoskeletalLocalMap k (J C n) := by
  intro Z hZ g
  obtain ⟨z, hz, unique⟩ := (Z.underlying.source_bijective_of_coskeletal k n hZ hkn).existsUnique
    (cellEquiv Z n g)
  refine ⟨(cellEquiv Z (n+1)).symm z, ?_, ?_⟩
  · apply (cellEquiv Z n).injective
    simpa only [cellEquiv_J, Equiv.apply_symm_apply] using hz
  · intro a ha
    apply (cellEquiv Z (n+1)).injective
    rw [Equiv.apply_symm_apply]
    apply unique
    exact (cellEquiv_J n a).symm.trans (congrArg (cellEquiv Z n) ha)

theorem CoskeletalLocalMap.pushout {C : GlobularTheory.{v}} (q : ℕ)
    {A B X Y : C.Model} (f : A ⟶ B) (a : A ⟶ X) (i : X ⟶ Y) (b : B ⟶ Y)
    (sq : IsPushout a f i b) (hf : CoskeletalLocalMap q f) :
    CoskeletalLocalMap q i := by
  intro Z hZ x
  obtain ⟨z, hz, unique⟩ := hf Z hZ (a ≫ x)
  refine ⟨sq.desc x z hz.symm, sq.inl_desc _ _ _, ?_⟩
  intro y hy
  apply sq.hom_ext
  · exact hy.trans (sq.inl_desc _ _ _).symm
  · have hz' : b ≫ y = z := unique (b ≫ y)
      ((Category.assoc f b y).symm.trans
        ((congrArg (· ≫ y) sq.w.symm).trans ((Category.assoc a i y).trans (congrArg (a ≫ ·) hy))))
    exact hz'.trans (sq.inr_desc _ _ _).symm

theorem elementary_pushout_low_bijective {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X Y : C.Model} (n : ℕ) (a : disk C n ⟶ X) (i : X ⟶ Y)
    (b : disk C (n+1) ⟶ Y) (sq : IsPushout a (J C n) i b)
    (k : ℕ) (hkn : k < n) :
    Function.Bijective ((underlyingMap i).app k) :=
  (coskeletalLocalMap_iff hC k i).1
    ((J_coskeletalLocalMap C k n hkn).pushout k (J C n) a i b sq) k le_rfl

theorem low_bijections_eq_local (C : GlobularTheory.{v}) (hC : C.IsCoherator) (q : ℕ) :
    (fun {X Y : C.Model} (f : X ⟶ Y) =>
      ∀ k, k ≤ q → Function.Bijective ((underlyingMap f).app k) : MorphismProperty C.Model) =
    ObjectProperty.isLocal (fun X : C.Model => X.IsCoskeletal q) := by
  ext X Y f
  rw [← coskeletalLocalMap_iff hC q f]
  exact forall_congr' (fun Z => imp_congr_right (fun _ =>
    (Function.bijective_iff_existsUnique (fun g : Y ⟶ Z => f ≫ g)).symm))

theorem low_bijective_transfinite {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {X Y : C.Model} (f : X ⟶ Y)
    {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    (H : TransfiniteCompositionOfShape J f)
    (hH : ∀ j, ¬ IsMax j → ∀ k, k ≤ q → Function.Bijective
      ((underlyingMap (H.F.map (homOfLE (Order.le_succ j)))).app k)) :
    ∀ k, k ≤ q → Function.Bijective ((underlyingMap f).app k) := by
  let P : ObjectProperty C.Model := fun X => X.IsCoskeletal q
  have hf : P.isLocal f := P.isLocal.transfiniteCompositionsOfShape_le J f
    ⟨{ toTransfiniteCompositionOfShape := H
       map_mem j hj := by
         change ObjectProperty.isLocal (fun X : C.Model => X.IsCoskeletal q) _
         rw [← low_bijections_eq_local C hC q]
         exact hH j hj }⟩
  change ObjectProperty.isLocal (fun X : C.Model => X.IsCoskeletal q) f at hf
  rwa [← low_bijections_eq_local C hC q] at hf

end GlobularTheory.Model

namespace GlobularSet

theorem exactBoundaryTest_split_into_coskeletal {X Y : GlobularSet.{u}}
    (i : Hom X Y) (r : Hom Y X) (hr : i.comp r = Hom.id X) (q : ℕ)
    (hlo : ∀ k, k < q → Function.Surjective (i.app k))
    (hhi : ∀ j, q < j → Function.Surjective (Y.boundary j))
    (hrefl : ∀ j x, Y.Joined j x x) : ExactBoundaryTest i := by
  intro d b y hy
  have hb : X.boundary d (r.app d y) = b := by
    rw [← r.boundary_app, hy, ← Hom.boundaryMap_comp]
    have hh := congrArg (fun f : Hom X X => f.boundaryMap d b) hr
    cases d with
    | zero => exact PUnit.ext _ _
    | succ d => exact hh
  refine ⟨r.app d y, hb, ?_⟩
  by_cases hd : d < q
  · obtain ⟨x, rfl⟩ := hlo d hd y
    have hx : r.app d (i.app d x) = x := congrArg (fun f : Hom X X => f.app d x) hr
    rw [hx]
    exact hrefl d _
  · have hp : Y.Parallel d (i.app d (r.app d y)) y := by
      apply (Y.parallel_iff_boundary_eq d _ _).2
      rw [← i.boundary_app, hb, hy]
    obtain ⟨z, hz⟩ := hhi (d+1) (by omega) ⟨(_, _), hp⟩
    exact ⟨z, congrArg (fun z => z.1.1) hz, congrArg (fun z => z.1.2) hz⟩

end GlobularSet

namespace GlobularTheory.Model

theorem elementary_pushout_to_coskeletal {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X Y : C.Model} (n : ℕ) (a : disk C n ⟶ X) (i : X ⟶ Y)
    (b : disk C (n+1) ⟶ Y) (sq : IsPushout a (J C n) i b)
    (hY : Y.IsCoskeletal n) : WeakEquivalence hC i := by
  obtain ⟨r, hr⟩ := elementary_pushout_retraction hC n a i b sq
  apply weakEquivalence_of_exactBoundaryTest hC
  apply GlobularSet.exactBoundaryTest_split_into_coskeletal (underlyingMap i) (underlyingMap r)
    (show (underlyingMap i).comp (underlyingMap r) = GlobularSet.Hom.id X.underlying from
      congrArg (fun f : X ⟶ X => underlyingMap f) hr) n
  · exact fun k hk => (elementary_pushout_low_bijective hC n a i b sq k hk).2
  · exact fun j hj => (hY j hj).2
  · exact Y.joined_refl hC

end GlobularTheory.Model

namespace GlobularTheory

structure SumIndex where
  S : Shape
  b : ℕ
  h : ℕ
  left : b < S.1
  right : b < h

noncomputable def sumDiagram (C : GlobularTheory.{v}) (t : SumIndex) :
    WalkingCospan ⥤ C.Objᵒᵖ :=
  cospan (C.toTheoryData.arity.map (t.S.seam t.left)).op
    (C.toTheoryData.arity.map (Shape.face t.right false)).op

noncomputable def sumCone (C : GlobularTheory.{v}) (t : SumIndex) : Cone (C.sumDiagram t) :=
  PullbackCone.mk (C.toTheoryData.arity.map (t.S.inl t.b t.h t.left t.right)).op
    (C.toTheoryData.arity.map (t.S.inr t.b t.h t.left t.right)).op
    (by simpa only [← op_comp] using congrArg Quiver.Hom.op (C.sums t.S t.b t.h t.left t.right).w)

noncomputable def sumConeIsLimit (C : GlobularTheory.{v}) (t : SumIndex) :
    IsLimit (C.sumCone t) :=
  (C.sums t.S t.b t.h t.left t.right).op.flip.isLimit

noncomputable def sumComparison (C : GlobularTheory.{v}) (t : SumIndex) :=
  Presheaf.coconePtToShrinkYoneda (C.sumCone t)
    (colimit.isColimit ((C.sumDiagram t).leftOp ⋙ shrinkYoneda.{v}))

noncomputable def sumComparisons (C : GlobularTheory.{v}) :
    MorphismProperty (C.Objᵒᵖ ⥤ Type v) :=
  MorphismProperty.ofHoms C.sumComparison

attribute [local instance] Cardinal.fact_isRegular_aleph0

instance shrinkYoneda_cardinalPresentable (C : GlobularTheory.{v})
    (S : C.Obj) : IsCardinalPresentable (shrinkYoneda.{v}.obj S) Cardinal.aleph0.{v} where
  preservesColimitOfShape J _ _ := by
    let e : coyoneda.obj (op (shrinkYoneda.{v}.obj S)) ≅
        (evaluation C.Objᵒᵖ (Type v)).obj (op S) :=
      NatIso.ofComponents (fun P => Equiv.toIso shrinkYonedaEquiv)
    exact preservesColimitsOfShape_of_natIso e.symm

instance sumComparison_source_presentable (C : GlobularTheory.{v}) (t : SumIndex) :
    IsCardinalPresentable (colimit ((C.sumDiagram t).leftOp ⋙ shrinkYoneda.{v}))
      Cardinal.aleph0.{v} := by
  let (k : WalkingCospanᵒᵖ) : IsCardinalPresentable
      (((C.sumDiagram t).leftOp ⋙ shrinkYoneda.{v}).obj k) Cardinal.aleph0.{v} :=
    C.shrinkYoneda_cardinalPresentable (((C.sumDiagram t).obj k.unop).unop)
  apply isCardinalPresentable_of_isColimit _ (colimit.isColimit _) Cardinal.aleph0.{v}
  exact hasCardinalLT_of_finite _ _ le_rfl

theorem sumComparisons_rightAdjoint (C : GlobularTheory.{v}) :
    C.sumComparisons.isLocal.ι.IsRightAdjoint := by
  let : MorphismProperty.IsSmall.{v} (MorphismProperty.ofHoms C.sumComparison) :=
    MorphismProperty.isSmall_ofHoms.{v} (ι := SumIndex) C.sumComparison
  change (MorphismProperty.ofHoms C.sumComparison).isLocal.ι.IsRightAdjoint
  apply MorphismProperty.isRightAdjoint_ι_isLocal _ Cardinal.aleph0.{v}
  rintro X Y f ⟨t⟩
  exact ⟨C.sumComparison_source_presentable t,
    C.shrinkYoneda_cardinalPresentable (C.sumCone t).pt.unop⟩


theorem sumComparison_local_iff (C : GlobularTheory.{v})
    (P : C.Objᵒᵖ ⥤ Type v) (t : SumIndex) :
    (MorphismProperty.single (C.sumComparison t)).isLocal P ↔
      IsPullback
        (P.map (C.toTheoryData.arity.map (t.S.inl t.b t.h t.left t.right)).op)
        (P.map (C.toTheoryData.arity.map (t.S.inr t.b t.h t.left t.right)).op)
        (P.map (C.toTheoryData.arity.map (t.S.seam t.left)).op)
        (P.map (C.toTheoryData.arity.map (Shape.face t.right false)).op) := by
  unfold sumComparison
  rw [← Presheaf.nonempty_isLimit_mapCone_iff.{v} (C.sumCone t)
    (colimit.isColimit ((C.sumDiagram t).leftOp ⋙ shrinkYoneda.{v})) P]
  constructor
  · rintro ⟨h⟩
    exact IsPullback.of_isLimit_cone h
  · intro h
    exact ⟨(PullbackCone.isLimitMapConeEquiv _ P).symm h.isLimit⟩

namespace Model

theorem sums_local {C : GlobularTheory.{v}} (M : C.Model) :
    C.sumComparisons.isLocal M.presheaf := by
  rintro A B f ⟨t⟩
  exact (MorphismProperty.isLocal_single_iff_bijective _ _).1
    ((C.sumComparison_local_iff M.presheaf t).2 (M.sums t.S t.b t.h t.left t.right))

noncomputable def toLocal (C : GlobularTheory.{v}) :
    C.Model ⥤ C.sumComparisons.isLocal.FullSubcategory where
  obj X := ⟨X.presheaf, X.sums_local⟩
  map f := ObjectProperty.homMk f

theorem local_sums (C : GlobularTheory.{v})
    (P : C.sumComparisons.isLocal.FullSubcategory) (t : SumIndex) :
    IsPullback
      (P.obj.map (C.toTheoryData.arity.map (t.S.inl t.b t.h t.left t.right)).op)
      (P.obj.map (C.toTheoryData.arity.map (t.S.inr t.b t.h t.left t.right)).op)
      (P.obj.map (C.toTheoryData.arity.map (t.S.seam t.left)).op)
      (P.obj.map (C.toTheoryData.arity.map (Shape.face t.right false)).op) := by
  apply (C.sumComparison_local_iff P.obj t).mp
  apply (MorphismProperty.isLocal_single_iff_bijective (C.sumComparison t) P.obj).mpr
  exact P.property (C.sumComparison t) (MorphismProperty.ofHoms.mk t)

noncomputable def fromLocal (C : GlobularTheory.{v}) :
    C.sumComparisons.isLocal.FullSubcategory ⥤ C.Model where
  obj P :=
    { presheaf := P.obj
      sums := fun S b h hl hr => local_sums C P ⟨S,b,h,hl,hr⟩ }
  map f := f.hom

noncomputable def localEquivalence (C : GlobularTheory.{v}) :
    C.Model ≌ C.sumComparisons.isLocal.FullSubcategory where
  functor := toLocal C
  inverse := fromLocal C
  unitIso := NatIso.ofComponents (fun X => Iso.refl X)
  counitIso := NatIso.ofComponents (fun X => Iso.refl X)

noncomputable instance hasColimits (C : GlobularTheory.{v}) : HasColimitsOfSize.{v,v} C.Model := by
  let := C.sumComparisons_rightAdjoint
  let : Reflective C.sumComparisons.isLocal.ι :=
    ⟨_, Adjunction.ofIsRightAdjoint C.sumComparisons.isLocal.ι⟩
  let : HasColimitsOfSize.{v,v} C.sumComparisons.isLocal.FullSubcategory :=
    hasColimits_of_reflective C.sumComparisons.isLocal.ι
  exact Adjunction.has_colimits_of_equivalence (localEquivalence C).functor

end Model
end GlobularTheory

namespace GlobularTheory.Model

abbrev CutoffModels (C : GlobularTheory.{v}) (q : ℕ) :=
  ObjectProperty.FullSubcategory (fun X : C.Model => X.IsCoskeletal q)

noncomputable def chosenCutoff {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : C.Model) : C.Model :=
  (exists_cutoff_reflection hC X q).choose

noncomputable def cutoffUnit {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : C.Model) : X ⟶ chosenCutoff hC q X :=
  (exists_cutoff_reflection hC X q).choose_spec.choose

theorem cutoffUnit_low_bijective {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : C.Model) (k : ℕ) (hk : k ≤ q) :
    Function.Bijective ((underlyingMap (cutoffUnit hC q X)).app k) :=
  (exists_cutoff_reflection hC X q).choose_spec.choose_spec.1 k hk

theorem chosenCutoff_coskeletal {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : C.Model) : (chosenCutoff hC q X).IsCoskeletal q :=
  (exists_cutoff_reflection hC X q).choose_spec.choose_spec.2.1

theorem cutoffUnit_universal {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : C.Model) (Y : CutoffModels C q) (f : X ⟶ Y.obj) :
    ∃! l : chosenCutoff hC q X ⟶ Y.obj, cutoffUnit hC q X ≫ l = f :=
  (exists_cutoff_reflection hC X q).choose_spec.choose_spec.2.2 Y.obj Y.property f

noncomputable def cutoffObject {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : C.Model) : CutoffModels C q :=
  ⟨chosenCutoff hC q X, chosenCutoff_coskeletal hC q X⟩

noncomputable def cutoffEquiv {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : C.Model) (Y : CutoffModels C q) :
    (cutoffObject hC q X ⟶ Y) ≃ (X ⟶ Y.obj) :=
  Equiv.ofBijective (fun f => cutoffUnit hC q X ≫ f.hom) (by
    constructor
    · intro f g h
      apply ObjectProperty.hom_ext
      obtain ⟨_, _, hu⟩ := cutoffUnit_universal hC q X Y (cutoffUnit hC q X ≫ f.hom)
      exact (hu f.hom rfl).trans (hu g.hom h.symm).symm
    · intro f
      obtain ⟨l, hl, _⟩ := cutoffUnit_universal hC q X Y f
      exact ⟨ObjectProperty.homMk l, hl⟩)

theorem cutoffEquiv_natural {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : C.Model) (Y Y' : CutoffModels C q) (g : Y ⟶ Y')
    (h : cutoffObject hC q X ⟶ Y) :
    cutoffEquiv hC q X Y' (h ≫ g) = cutoffEquiv hC q X Y h ≫ g.hom := by
  change cutoffUnit hC q X ≫ (h.hom ≫ g.hom) = (cutoffUnit hC q X ≫ h.hom) ≫ g.hom
  exact (Category.assoc _ _ _).symm

noncomputable def cutoffFunctor {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) : C.Model ⥤ CutoffModels C q :=
  Adjunction.leftAdjointOfEquiv (G := (ObjectProperty.ι (fun X : C.Model => X.IsCoskeletal q)))
    (cutoffEquiv hC q) (cutoffEquiv_natural hC q)

noncomputable def cutoffAdjunction {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) : cutoffFunctor hC q ⊣ (ObjectProperty.ι (fun X : C.Model => X.IsCoskeletal q)) :=
  Adjunction.adjunctionOfEquivLeft _ _

@[instance_reducible] noncomputable def cutoffReflective {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) : Reflective (ObjectProperty.ι (fun X : C.Model => X.IsCoskeletal q)) :=
  ⟨cutoffFunctor hC q, cutoffAdjunction hC q⟩

theorem cutoff_hasColimits {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) : HasColimitsOfSize.{v,v} (CutoffModels C q) := by
  let := cutoffReflective hC q
  exact hasColimits_of_reflective (ObjectProperty.ι (fun X : C.Model => X.IsCoskeletal q))

end GlobularTheory.Model

end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace Globe

def faceLE {m n : ℕ} (h : m ≤ n) (side : Bool) : Globe.mk m ⟶ Globe.mk n :=
  if e : m = n then e ▸ Face.id m else Face.face (lt_of_le_of_ne h e) side

@[simp] theorem faceLE_refl (n : ℕ) (side : Bool) : faceLE (le_refl n) side = 𝟙 (Globe.mk n) := by
  simp only [faceLE, dite_true]
  rfl

@[simp] theorem faceLE_of_lt {m n : ℕ} (h : m < n) (side : Bool) :
    faceLE h.le side = face h side := by
  simp [faceLE, h.ne, face]

end Globe

namespace GlobularPresheaf

noncomputable def faceLE {m n : ℕ} (h : m ≤ n) (side : Bool) : disk.{u} m ⟶ disk.{u} n :=
  uliftYoneda.{u}.map (Globe.faceLE h side)

@[simp] theorem faceLE_refl (n : ℕ) (side : Bool) : faceLE (le_refl n) side = 𝟙 (disk.{u} n) := by
  change uliftYoneda.map (Globe.faceLE (le_refl n) side) = 𝟙 _
  rw [Globe.faceLE_refl, uliftYoneda.map_id]

@[simp] theorem faceLE_of_lt {m n : ℕ} (h : m < n) (side : Bool) :
    faceLE.{u} h.le side = face h side := by
  unfold faceLE face
  rw [Globe.faceLE_of_lt]

theorem face_low_bijective {m n k : ℕ} (h : m < n) (hk : k < m) (side : Bool) :
    Function.Bijective ((face.{u} h side).app (op (Globe.mk k))) := by
  constructor
  · rintro ⟨a⟩ ⟨b⟩ he
    cases a with
    | id => omega
    | face ha ba =>
      cases b with
      | id => omega
      | face hb bb =>
        have : ba = bb := by
          change ULift.up (Globe.Face.face (ha.trans h) ba) =
            ULift.up (Globe.Face.face (hb.trans h) bb) at he
          cases he
          rfl
        subst bb
        rfl
  · rintro ⟨a⟩
    cases a with
    | id => omega
    | face ha ba =>
      exact ⟨⟨Globe.Face.face hk ba⟩, rfl⟩

theorem face_low_equal {m n k : ℕ} (h : m < n) (hk : k < m) (b c : Bool) :
    (face.{u} h b).app (op (Globe.mk k)) = (face h c).app (op (Globe.mk k)) := by
  apply ConcreteCategory.hom_ext
  rintro ⟨a⟩
  cases a with
  | id => omega
  | face ha ba => rfl

theorem faceLE_low_bijective {m n k : ℕ} (h : m ≤ n) (hk : k < m) (side : Bool) :
    Function.Bijective ((faceLE.{u} h side).app (op (Globe.mk k))) := by
  rcases lt_or_eq_of_le h with h | rfl
  · rw [faceLE_of_lt h]
    exact face_low_bijective h hk side
  · rw [faceLE_refl]
    exact Function.bijective_id


theorem face_comp_faceLE {a b c : ℕ} (hab : a < b) (hbc : b ≤ c) (s t : Bool) :
    face.{u} hab s ≫ faceLE hbc t = face (hab.trans_le hbc) s := by
  rcases lt_or_eq_of_le hbc with hbc | rfl
  · rw [faceLE_of_lt hbc]
    change uliftYoneda.map (Globe.face hab s) ≫ uliftYoneda.map (Globe.face hbc t) = _
    rw [← uliftYoneda.map_comp]
    rfl
  · rw [faceLE_refl, Category.comp_id]

theorem globeMap_low_equal {m n k : ℕ} (f g : Globe.mk m ⟶ Globe.mk n) (hk : k < m) :
    (uliftYoneda.{u}.map f).app (op (Globe.mk k)) =
      (uliftYoneda.{u}.map g).app (op (Globe.mk k)) := by
  change Globe.Face m n at f g
  apply ConcreteCategory.hom_ext
  rintro ⟨a⟩
  cases a with
  | id => omega
  | face ha ba =>
    cases f with
    | id =>
      cases g with
      | id => rfl
      | face hg bg => omega
    | face hf bf =>
      cases g with
      | id => omega
      | face hg bg => rfl

theorem disk_hom_ext {n : ℕ} {X : GlobularPresheaf.{u}} {f g : disk n ⟶ X}
    (h : f.app (op (Globe.mk n)) = g.app (op (Globe.mk n))) : f = g := by
  apply uliftYonedaEquiv.injective
  exact ConcreteCategory.congr_hom h _

theorem pushout_comparison_isIso {D : Type u} [Category.{v} D]
    {A B E P A' B' E' P' : D}
    {f : A ⟶ B} {g : A ⟶ E} {i : B ⟶ P} {j : E ⟶ P}
    {f' : A' ⟶ B'} {g' : A' ⟶ E'} {i' : B' ⟶ P'} {j' : E' ⟶ P'}
    (h : IsPushout f g i j) (h' : IsPushout f' g' i' j')
    (a : A ⟶ A') (b : B ⟶ B') (e : E ⟶ E') (p : P ⟶ P')
    [IsIso a] [IsIso b] [IsIso e]
    (hf : f ≫ b = a ≫ f') (hg : g ≫ e = a ≫ g')
    (hi : i ≫ p = b ≫ i') (hj : j ≫ p = e ≫ j') : IsIso p := by
  let r : P' ⟶ P := h'.desc (inv b ≫ i) (inv e ≫ j) (by
    apply (cancel_epi a).1
    simp only [← Category.assoc, ← hf, ← hg]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact h.w)
  refine ⟨r, ?_, ?_⟩
  · apply h.hom_ext
    · rw [← Category.assoc, hi, Category.assoc]
      simp only [r, IsPushout.inl_desc, IsIso.hom_inv_id_assoc, Category.comp_id]
    · rw [← Category.assoc, hj, Category.assoc]
      simp only [r, IsPushout.inr_desc, IsIso.hom_inv_id_assoc, Category.comp_id]
  · apply h'.hom_ext
    · simp only [r, IsPushout.inl_desc_assoc, hi, Category.assoc,
        IsIso.inv_hom_id_assoc, Category.comp_id]
    · simp only [r, IsPushout.inr_desc_assoc, hj, Category.assoc,
        IsIso.inv_hom_id_assoc, Category.comp_id]


theorem faceLE_cap_bijective {q d n k : ℕ} (hd : d = min n (q+1))
    (h : d ≤ n) (hk : k ≤ q) :
    Function.Bijective ((faceLE.{u} h false).app (op (Globe.mk k))) := by
  rcases lt_or_eq_of_le h with hlt | rfl
  · apply faceLE_low_bijective
    have : d = q+1 := by omega
    omega
  · rw [faceLE_refl]
    exact Function.bijective_id

theorem face_comp_eq_of_app_eq {m n : ℕ} {X : GlobularPresheaf.{u}}
    (h : m < n) (s : Bool) (a b : disk n ⟶ X)
    (hab : a.app (op (Globe.mk m)) = b.app (op (Globe.mk m))) :
    face h s ≫ a = face h s ≫ b := by
  apply disk_hom_ext
  exact congrArg (fun t => (face h s).app (op (Globe.mk m)) ≫ t) hab

end GlobularPresheaf

namespace Shape

noncomputable def last (S : Shape) : GlobularPresheaf.disk S.1 ⟶ S.realize :=
  S.2.lastInclusion

end Shape

end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace Table

structure SpineData {n : ℕ} (T : Table n) (q : ℕ) where
  S : Shape
  last_eq : S.1 = min n (q+1)
  height_le : S.height ≤ q+1
  map : S.realize ⟶ T.realize
  low_bijective : ∀ k, k ≤ q → Function.Bijective (map.app (op (Globe.mk k)))
  last_low : ∀ k, k ≤ q →
    (S.last ≫ map).app (op (Globe.mk k)) =
      (GlobularPresheaf.faceLE (show S.1 ≤ n by rw [last_eq]; exact min_le_left _ _) false ≫
        T.lastInclusion).app (op (Globe.mk k))

namespace SpineData

noncomputable def globe (q n : ℕ) : (Table.globe n).SpineData q where
  S := Shape.globe (min n (q+1))
  last_eq := rfl
  height_le := min_le_right _ _
  map := GlobularPresheaf.faceLE (min_le_left n (q+1)) false
  low_bijective _ hk := GlobularPresheaf.faceLE_cap_bijective rfl _ hk
  last_low _ _ := rfl

noncomputable def attachHigh {n : ℕ} {T : Table n} {q : ℕ}
    (P : T.SpineData q) (b h : ℕ) (hl : b < n) (hr : b < h) (hb : q < b) :
    (Table.attach T b h hl hr).SpineData q := by
  have hdim : P.S.1 = q+1 := by rw [P.last_eq]; omega
  have hn : P.S.1 ≤ n := by omega
  have hh : P.S.1 ≤ h := by omega
  have hsb : P.S.1 ≤ b := by omega
  let i : T.realize ⟶ (Table.attach T b h hl hr).realize := Shape.inl ⟨n,T⟩ b h hl hr
  let j : GlobularPresheaf.disk h ⟶ (Table.attach T b h hl hr).realize :=
    Shape.inr ⟨n,T⟩ b h hl hr
  have sq : IsPushout (GlobularPresheaf.face hl true ≫ T.lastInclusion)
      (GlobularPresheaf.face hr false) i j := IsPushout.of_hasPushout _ _
  refine ⟨P.S, ?_, P.height_le, P.map ≫ i, ?_, ?_⟩
  · rw [hdim]
    omega
  · intro k hk
    let E := (evaluation Globeᵒᵖ (Type 0)).obj (op (Globe.mk k))
    have hg : IsIso (E.map (GlobularPresheaf.face hr false)) :=
      (isIso_iff_bijective _).2 (GlobularPresheaf.face_low_bijective hr (by omega) false)
    have hi : IsIso (E.map i) := (sq.map E).isIso_inl_of_isIso hg
    exact ((isIso_iff_bijective _).1 hi).comp (P.low_bijective k hk)
  · intro k hk
    let c := op (Globe.mk k)
    let bridge := GlobularPresheaf.faceLE hsb false
    have e1 : (GlobularPresheaf.faceLE hn false).app c =
        (bridge ≫ GlobularPresheaf.face hl true).app c := by
      change (uliftYoneda.map (Globe.faceLE hn false)).app c =
        (uliftYoneda.map (Globe.faceLE hsb false) ≫ uliftYoneda.map (Globe.face hl true)).app c
      rw [← uliftYoneda.map_comp]
      exact GlobularPresheaf.globeMap_low_equal _ _ (by omega)
    have e2 : (bridge ≫ GlobularPresheaf.face hr false).app c =
        (GlobularPresheaf.faceLE hh false).app c := by
      change (uliftYoneda.map (Globe.faceLE hsb false) ≫ uliftYoneda.map (Globe.face hr false)).app c =
        (uliftYoneda.map (Globe.faceLE hh false)).app c
      rw [← uliftYoneda.map_comp]
      exact GlobularPresheaf.globeMap_low_equal _ _ (by omega)
    have hp := P.last_low k hk
    have hw := congrArg (fun a => a.app c) sq.w
    simp only [NatTrans.comp_app] at hp hw e1 e2
    change P.S.last.app c ≫ (P.map.app c ≫ i.app c) =
      (GlobularPresheaf.faceLE hh false).app c ≫ j.app c
    rw [← Category.assoc, hp, e1]
    calc
      ((bridge.app c ≫ (GlobularPresheaf.face hl true).app c) ≫ T.lastInclusion.app c) ≫ i.app c =
          bridge.app c ≫ (((GlobularPresheaf.face hl true).app c ≫ T.lastInclusion.app c) ≫ i.app c) := by simp only [Category.assoc]
      _ = bridge.app c ≫ ((GlobularPresheaf.face hr false).app c ≫ j.app c) := by rw [hw]
      _ = (GlobularPresheaf.faceLE hh false).app c ≫ j.app c := by rw [← Category.assoc, e2]

end SpineData
end Table

namespace Table.SpineData

noncomputable def attachLow {n : ℕ} {T : Table n} {q : ℕ}
    (P : T.SpineData q) (b h : ℕ) (hl : b < n) (hr : b < h) (hb : b ≤ q) :
    (Table.attach T b h hl hr).SpineData q := by
  have hn : P.S.1 ≤ n := by rw [P.last_eq]; exact min_le_left _ _
  have hbl : b < P.S.1 := by rw [P.last_eq]; omega
  have hbr : b < min h (q+1) := by omega
  let N : Shape := P.S.attach b (min h (q+1)) hbl hbr
  let il : P.S.realize ⟶ N.realize := Shape.inl P.S b (min h (q+1)) hbl hbr
  let ir : GlobularPresheaf.disk (min h (q+1)) ⟶ N.realize :=
    Shape.inr P.S b (min h (q+1)) hbl hbr
  let cap := GlobularPresheaf.faceLE (min_le_left h (q+1)) false
  let il' : T.realize ⟶ (Table.attach T b h hl hr).realize := Shape.inl ⟨n,T⟩ b h hl hr
  let ir' : GlobularPresheaf.disk h ⟶ (Table.attach T b h hl hr).realize :=
    Shape.inr ⟨n,T⟩ b h hl hr
  have sl : GlobularPresheaf.face hbl true ≫ P.S.last ≫ P.map =
      GlobularPresheaf.face hl true ≫ T.lastInclusion := by
    rw [GlobularPresheaf.face_comp_eq_of_app_eq hbl true _ _ (P.last_low b hb)]
    rw [← Category.assoc,
      GlobularPresheaf.face_comp_faceLE hbl hn true false]
  have sr : GlobularPresheaf.face hbr false ≫ cap = GlobularPresheaf.face hr false :=
    GlobularPresheaf.face_comp_faceLE hbr _ false false
  have sq : IsPushout (GlobularPresheaf.face hbl true ≫ P.S.last)
      (GlobularPresheaf.face hbr false) il ir := IsPushout.of_hasPushout _ _
  have sq' : IsPushout (GlobularPresheaf.face hl true ≫ T.lastInclusion)
      (GlobularPresheaf.face hr false) il' ir' := IsPushout.of_hasPushout _ _
  let f : N.realize ⟶ (Table.attach T b h hl hr).realize :=
    sq.desc (P.map ≫ il') (cap ≫ ir') (by
      calc
        (GlobularPresheaf.face hbl true ≫ P.S.last) ≫ (P.map ≫ il') =
            (GlobularPresheaf.face hbl true ≫ P.S.last ≫ P.map) ≫ il' := by simp only [Category.assoc]
        _ = (GlobularPresheaf.face hl true ≫ T.lastInclusion) ≫ il' := congrArg (fun a => a ≫ il') sl
        _ = GlobularPresheaf.face hr false ≫ ir' := sq'.w
        _ = GlobularPresheaf.face hbr false ≫ (cap ≫ ir') := by rw [← Category.assoc, sr])
  have fi : il ≫ f = P.map ≫ il' := sq.inl_desc _ _ _
  have fj : ir ≫ f = cap ≫ ir' := sq.inr_desc _ _ _
  refine ⟨N, rfl, ?_, f, ?_, ?_⟩
  · exact max_le P.height_le (min_le_right _ _)
  · intro k hk
    let E := (evaluation Globeᵒᵖ (Type 0)).obj (op (Globe.mk k))
    have : IsIso (E.map P.map) := (isIso_iff_bijective _).2 (P.low_bijective k hk)
    have : IsIso (E.map cap) := (isIso_iff_bijective _).2
      (GlobularPresheaf.faceLE_cap_bijective rfl _ hk)
    apply (isIso_iff_bijective _).1
    apply GlobularPresheaf.pushout_comparison_isIso (sq.map E) (sq'.map E)
      (𝟙 _) (E.map P.map) (E.map cap) (E.map f)
    · simpa only [Category.id_comp, ← E.map_comp, Category.assoc] using congrArg E.map sl
    · simpa only [Category.id_comp, ← E.map_comp] using congrArg E.map sr
    · simpa only [← E.map_comp] using congrArg E.map fi
    · simpa only [← E.map_comp] using congrArg E.map fj
  · intro k hk
    exact congrArg (fun a => a.app (op (Globe.mk k))) fj

end Table.SpineData

namespace Table

noncomputable def spine (q : ℕ) : {n : ℕ} → (T : Table n) → T.SpineData q
  | _, .globe n => SpineData.globe q n
  | _, .attach T b h hl hr =>
    if hb : b ≤ q then (spine q T).attachLow b h hl hr hb
    else (spine q T).attachHigh b h hl hr (by omega)

end Table

namespace GlobularPresheaf

theorem underlyingMap_injective {X Y : GlobularPresheaf.{u}} :
    Function.Injective (fun f : X ⟶ Y => underlyingMap f) := by
  intro f g h
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  exact congrArg (fun a => a.app k.unop.dim x) h

theorem existsUnique_factor_low_bijective {X R Y : GlobularPresheaf.{u}}
    (η : X ⟶ R) (f : X ⟶ Y) (q : ℕ)
    (hη : ∀ k, k ≤ q → Function.Bijective (η.app (op (Globe.mk k))))
    (hY : ∀ j, q < j → Function.Bijective (Y.underlying.boundary j)) :
    ∃! g : R ⟶ Y, η ≫ g = f := by
  obtain ⟨g, hg, hu⟩ := GlobularSet.existsUnique_factor_low_bijective
    (underlyingMap η) (underlyingMap f) q hη hY
  let l : R ⟶ Y := R.underlyingPresheafIso.inv ≫ g.presheafMap ≫ Y.underlyingPresheafIso.hom
  have hl : underlyingMap l = g := by ext n x; rfl
  have hf : η ≫ l = f := by
    apply underlyingMap_injective
    change (underlyingMap η).comp (underlyingMap l) = underlyingMap f
    rw [hl, hg]
  refine ⟨l, hf, ?_⟩
  intro l' hl'
  apply underlyingMap_injective
  apply Eq.trans _ hl.symm
  apply hu
  exact congrArg (fun a : X ⟶ Y => underlyingMap a) hl'

theorem precomp_bijective_low {X R Y : GlobularPresheaf.{u}}
    (η : X ⟶ R) (q : ℕ)
    (hη : ∀ k, k ≤ q → Function.Bijective (η.app (op (Globe.mk k))))
    (hY : ∀ j, q < j → Function.Bijective (Y.underlying.boundary j)) :
    Function.Bijective (fun g : R ⟶ Y => η ≫ g) := by
  constructor
  · intro a b hab
    obtain ⟨_, _, hu⟩ := existsUnique_factor_low_bijective η (η ≫ b) q hη hY
    exact (hu a hab).trans (hu b rfl).symm
  · intro f
    obtain ⟨g, hg, _⟩ := existsUnique_factor_low_bijective η f q hη hY
    exact ⟨g, hg⟩

end GlobularPresheaf

namespace TupleSystem

theorem map_bijective_of_low {T : TupleSystem.{v}} {S R : Shape} (f : S ⟶ R)
    (q : ℕ) (hf : ∀ k, k ≤ q → Function.Bijective (f.app (op (Globe.mk k))))
    (hT : ∀ j, q < j → Function.Bijective (T.underlying.boundary j)) :
    Function.Bijective (T.presheaf.map f.op) := by
  have hg : ∀ k, k ≤ q → Function.Bijective
      ((Shape.liftedRealization.{v}.map f).app (op (Globe.mk k))) := by
    intro k hk
    exact ULift.map_bijective.mpr (hf k hk)
  have hb := GlobularPresheaf.precomp_bijective_low
    (Y := T.globularPresheaf) (Shape.liftedRealization.map f) q hg hT
  have hn (x : T.presheaf.obj (op R)) :
      T.evaluation.app (op S) (T.presheaf.map f.op x) =
        Shape.liftedRealization.map f ≫ T.evaluation.app (op R) x :=
    ConcreteCategory.congr_hom (T.evaluation.naturality f.op) x
  constructor
  · intro x y h
    apply (T.evaluation_bijective R).1
    apply hb.1
    exact (hn x).symm.trans ((congrArg (T.evaluation.app (op S)) h).trans (hn y))
  · intro y
    obtain ⟨g, hg⟩ := hb.2 (T.evaluation.app (op S) y)
    obtain ⟨x, hx⟩ := (T.evaluation_bijective R).2 g
    refine ⟨x, (T.evaluation_bijective S).1 ?_⟩
    exact (hn x).trans ((congrArg (fun g => Shape.liftedRealization.map f ≫ g) hx).trans hg)

end TupleSystem

end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularTheory.Model

noncomputable def freeShapeMap (C : GlobularTheory.{v}) {S T : Shape}
    (f : S ⟶ T) : freeShape C S ⟶ freeShape C T :=
  yoneda.map (C.toTheoryData.arity.map f)

theorem freeShapeMap_low_bijective {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {S T : Shape} (f : S ⟶ T) (q : ℕ)
    (hf : ∀ k, k ≤ q → Function.Bijective (f.app (op (Globe.mk k)))) :
    ∀ k, k ≤ q → Function.Bijective ((underlyingMap (freeShapeMap C f)).app k) := by
  apply (coskeletalLocalMap_iff hC q (freeShapeMap C f)).mp
  intro Z hZ g
  have hb := TupleSystem.map_bijective_of_low (T := Z.tuples) f q hf hZ
  obtain ⟨x, hx⟩ := hb.2 (yonedaEquiv g)
  let h : freeShape C T ⟶ Z := yonedaEquiv.symm x
  have hh : freeShapeMap C f ≫ h = g := by
    apply yonedaEquiv.injective
    have hv : yonedaEquiv h = x := Equiv.apply_symm_apply _ _
    exact (yonedaEquiv_naturality h (C.toTheoryData.arity.map f)).symm.trans
      ((congrArg (Z.tuples.presheaf.map f.op) hv).trans hx)
  refine ⟨h, hh, ?_⟩
  intro h' hh'
  apply yonedaEquiv.injective
  apply hb.1
  exact (yonedaEquiv_naturality h' (C.toTheoryData.arity.map f)).trans
    ((congrArg yonedaEquiv hh').trans
      ((congrArg yonedaEquiv hh).symm.trans
        (yonedaEquiv_naturality h (C.toTheoryData.arity.map f)).symm))

end GlobularTheory.Model

namespace GlobularSet

def HasFillers (X : GlobularSet.{u}) : Prop := ∀ n, Function.Surjective (X.boundary n)

theorem Hom.reflects_parallel_of_low {X Y : GlobularSet.{u}} (f : Hom X Y)
    {n : ℕ} (hf : ∀ k, k < n → Function.Injective (f.app k))
    {a b : X.Cell n} (h : Y.Parallel n (f.app n a) (f.app n b)) :
    X.Parallel n a b := by
  cases n with
  | zero => trivial
  | succ n =>
    exact ⟨hf n (Nat.lt_succ_self n) (by rw [f.source_app, f.source_app]; exact h.1),
      hf n (Nat.lt_succ_self n) (by rw [f.target_app, f.target_app]; exact h.2)⟩

theorem Hom.boundaryMap_bijective_of_low {X Y : GlobularSet.{u}} (f : Hom X Y)
    (n : ℕ) (hf : ∀ k, k < n → Function.Bijective (f.app k)) :
    Function.Bijective (f.boundaryMap n) := by
  cases n with
  | zero =>
    change Function.Bijective (fun _ : PUnit => (PUnit.unit : PUnit))
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨PUnit.unit, rfl⟩⟩
  | succ n =>
    constructor
    · intro a b h
      exact Subtype.ext (Prod.ext
        ((hf n (Nat.lt_succ_self n)).1 (congrArg (fun b => b.1.1) h))
        ((hf n (Nat.lt_succ_self n)).1 (congrArg (fun b => b.1.2) h)))
    · intro b
      obtain ⟨x, hx⟩ := (hf n (Nat.lt_succ_self n)).2 b.1.1
      obtain ⟨y, hy⟩ := (hf n (Nat.lt_succ_self n)).2 b.1.2
      have hp : X.Parallel n x y := f.reflects_parallel_of_low
        (fun k hk => (hf k (by omega)).1) (by rw [hx, hy]; exact b.2)
      exact ⟨⟨(x, y), hp⟩, Subtype.ext (Prod.ext hx hy)⟩

theorem HasFillers.of_low_bijective {X Y : GlobularSet.{u}}
    (hX : X.HasFillers) (f : Hom X Y) (q : ℕ)
    (hf : ∀ k, k ≤ q → Function.Bijective (f.app k))
    (hY : ∀ j, q < j → Function.Surjective (Y.boundary j)) : Y.HasFillers := by
  intro n
  by_cases hn : n ≤ q
  · intro b
    obtain ⟨b', hb'⟩ := (f.boundaryMap_bijective_of_low n (fun k hk => hf k (by omega))).2 b
    obtain ⟨x, hx⟩ := hX n b'
    exact ⟨f.app n x, (f.boundary_app n x).symm.trans ((congrArg (f.boundaryMap n) hx).trans hb')⟩
  · exact hY n (by omega)

end GlobularSet

namespace GlobularTheory.Model

theorem freeShape_joined (C : GlobularTheory.{v}) (hC : C.IsCoherator) (S : Shape)
    (n : ℕ) (a b : (freeShape C S).underlying.Cell n)
    (hp : (freeShape C S).underlying.Parallel n a b) :
    (freeShape C S).underlying.Joined n a b := by
  let P := S.2.spine n
  let f : P.S ⟶ S := P.map
  let i := underlyingMap (freeShapeMap C f)
  have hi : ∀ k, k ≤ n → Function.Bijective (i.app k) :=
    freeShapeMap_low_bijective hC f n P.low_bijective
  obtain ⟨a', ha⟩ := (hi n le_rfl).2 a
  obtain ⟨b', hb⟩ := (hi n le_rfl).2 b
  have hp' : (freeShape C P.S).underlying.Parallel n a' b' :=
    i.reflects_parallel_of_low (fun k hk => (hi k (by omega)).1) (by rw [ha, hb]; exact hp)
  have hp'' : C.Parallel n a' b' := by
    cases n <;> exact hp'
  let pair : C.AdmissiblePair := ⟨n, P.S, P.height_le, a', b', hp''⟩
  obtain ⟨z, hs, ht⟩ := hC.2 pair
  have hz : (freeShape C P.S).underlying.Joined n a' b' := ⟨z, hs, ht⟩
  have hz' := i.map_joined hz
  rw [ha, hb] at hz'
  exact hz'

theorem freeShape_hasFillers (C : GlobularTheory.{v}) (hC : C.IsCoherator) (S : Shape) :
    (freeShape C S).underlying.HasFillers := by
  intro n
  cases n with
  | zero =>
    intro b
    let f : Shape.globe 0 ⟶ S :=
      show GlobularPresheaf.disk 0 ⟶ S.realize from
        GlobularPresheaf.faceLE (Nat.zero_le S.1) false ≫ S.last
    refine ⟨C.base f, ?_⟩
    change PUnit.unit = b
    exact Subsingleton.elim _ _
  | succ n =>
    intro b
    obtain ⟨z, hs, ht⟩ := freeShape_joined C hC S n b.1.1 b.1.2 b.2
    exact ⟨z, Subtype.ext (Prod.ext hs ht)⟩

theorem cutoff_freeShape_hasFillers (C : GlobularTheory.{v}) (hC : C.IsCoherator)
    (S : Shape) (q : ℕ) :
    (chosenCutoff hC q (freeShape C S)).underlying.HasFillers :=
  (freeShape_hasFillers C hC S).of_low_bijective
    (underlyingMap (cutoffUnit hC q (freeShape C S))) q
    (cutoffUnit_low_bijective hC q _)
    (fun j hj => (chosenCutoff_coskeletal hC q _ j hj).2)

end GlobularTheory.Model

end Grothendieck

namespace Grothendieck.GlobularTheory.Model

open CategoryTheory CategoryTheory.Limits Opposite

def presheafFunctor (C : GlobularTheory.{v}) : C.Model ⥤ (C.Objᵒᵖ ⥤ Type v) where
  obj X := X.presheaf
  map f := f

noncomputable def forgetGlobular (C : GlobularTheory.{v}) : C.Model ⥤ GlobularPresheaf.{v} :=
  presheafFunctor C ⋙ (Functor.whiskeringLeft Globeᵒᵖ C.Objᵒᵖ (Type v)).obj C.globes.op

@[instance_reducible] noncomputable def presheafReflection (C : GlobularTheory.{v}) :
    Reflective C.sumComparisons.isLocal.ι := by
  let := C.sumComparisons_rightAdjoint
  exact ⟨_, Adjunction.ofIsRightAdjoint C.sumComparisons.isLocal.ι⟩

noncomputable def freePresheaf (C : GlobularTheory.{v}) :
    (C.Objᵒᵖ ⥤ Type v) ⥤ C.Model := by
  let := presheafReflection C
  exact reflector C.sumComparisons.isLocal.ι ⋙ fromLocal C

noncomputable def presheafAdjunction (C : GlobularTheory.{v}) :
    freePresheaf C ⊣ presheafFunctor C := by
  let := presheafReflection C
  exact ((reflectorAdjunction C.sumComparisons.isLocal.ι).comp
    (localEquivalence C).symm.toAdjunction)

noncomputable def freeGlobular (C : GlobularTheory.{v}) : GlobularPresheaf.{v} ⥤ C.Model :=
  C.globes.op.lan ⋙ freePresheaf C

noncomputable def globularAdjunction (C : GlobularTheory.{v}) :
    freeGlobular C ⊣ forgetGlobular C :=
  (C.globes.op.lanAdjunction (Type v)).comp (presheafAdjunction C)

instance freeGlobular_preservesColimits (C : GlobularTheory.{v}) :
    PreservesColimitsOfSize.{v,v} (freeGlobular C) :=
  (globularAdjunction C).leftAdjoint_preservesColimits

end Grothendieck.GlobularTheory.Model

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularTheory

noncomputable def composition (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    C.Hom (Shape.globe (n+1)) (compositionShape n) :=
  (hC.2 (C.compositionPair n)).choose

theorem composition_source (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    C.comp (C.base (Shape.source n)) (C.composition hC n) =
      C.base (Shape.source n ≫ compositionLeft n) :=
  (hC.2 (C.compositionPair n)).choose_spec.1

theorem composition_target (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    C.comp (C.base (Shape.target n)) (C.composition hC n) =
      C.base (Shape.target n ≫ compositionRight n) :=
  (hC.2 (C.compositionPair n)).choose_spec.2

noncomputable def inverse (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    C.Hom (Shape.globe (n+1)) (Shape.globe (n+1)) :=
  (hC.2 (C.inversePair n)).choose

theorem inverse_source (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    C.comp (C.base (Shape.source n)) (C.inverse hC n) = C.base (Shape.target n) :=
  (hC.2 (C.inversePair n)).choose_spec.1

theorem inverse_target (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    C.comp (C.base (Shape.target n)) (C.inverse hC n) = C.base (Shape.source n) :=
  (hC.2 (C.inversePair n)).choose_spec.2

namespace Model

theorem map_eval {C : GlobularTheory.{v}} {X Y : C.Model} (f : X ⟶ Y)
    {S T : Shape} (a : C.Hom S T) (t : X.presheaf.obj (op (⟨T⟩ : C.Obj))) :
    f.app (op (⟨S⟩ : C.Obj)) (X.eval a t) =
      Y.eval a (f.app (op (⟨T⟩ : C.Obj)) t) :=
  (ConcreteCategory.congr_hom (f.naturality
    (show (op (⟨T⟩ : C.Obj)) ⟶ op ⟨S⟩ from Quiver.Hom.op a)) t)

noncomputable def sumTuple {C : GlobularTheory.{v}} (X : C.Model)
    (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h)
    (a : X.presheaf.obj (op (⟨S⟩ : C.Obj))) (d : X.underlying.Cell h)
    (w : X.eval (C.base (S.seam hl)) a = X.eval (C.base (Shape.face hr false)) d) :
    X.presheaf.obj (op (⟨S.attach b h hl hr⟩ : C.Obj)) :=
  (Types.exists_of_isPullback (X.sums S b h hl hr) a d w).choose

@[simp] theorem sumTuple_left {C : GlobularTheory.{v}} (X : C.Model)
    (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h)
    (a : X.presheaf.obj (op (⟨S⟩ : C.Obj))) (d : X.underlying.Cell h)
    (w : X.eval (C.base (S.seam hl)) a = X.eval (C.base (Shape.face hr false)) d) :
    X.eval (C.base (S.inl b h hl hr)) (X.sumTuple S b h hl hr a d w) = a :=
  (Types.exists_of_isPullback (X.sums S b h hl hr) a d w).choose_spec.1

@[simp] theorem sumTuple_right {C : GlobularTheory.{v}} (X : C.Model)
    (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h)
    (a : X.presheaf.obj (op (⟨S⟩ : C.Obj))) (d : X.underlying.Cell h)
    (w : X.eval (C.base (S.seam hl)) a = X.eval (C.base (Shape.face hr false)) d) :
    X.eval (C.base (S.inr b h hl hr)) (X.sumTuple S b h hl hr a d w) = d :=
  (Types.exists_of_isPullback (X.sums S b h hl hr) a d w).choose_spec.2

noncomputable def compositionTuple {C : GlobularTheory.{v}} (X : C.Model) (n : ℕ)
    (a b : X.underlying.Cell (n+1)) (hab : X.underlying.target n a = X.underlying.source n b) :
    X.presheaf.obj (op (⟨compositionShape n⟩ : C.Obj)) :=
  X.sumTuple (Shape.globe (n+1)) n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)
    a b (by rw [Shape.globe_seam]; exact hab)

@[simp] theorem compositionTuple_left {C : GlobularTheory.{v}} (X : C.Model) (n : ℕ)
    (a b : X.underlying.Cell (n+1)) (hab : X.underlying.target n a = X.underlying.source n b) :
    X.eval (C.base (compositionLeft n)) (X.compositionTuple n a b hab) = a :=
  X.sumTuple_left _ _ _ _ _ _ _ _

@[simp] theorem compositionTuple_right {C : GlobularTheory.{v}} (X : C.Model) (n : ℕ)
    (a b : X.underlying.Cell (n+1)) (hab : X.underlying.target n a = X.underlying.source n b) :
    X.eval (C.base (compositionRight n)) (X.compositionTuple n a b hab) = b :=
  X.sumTuple_right _ _ _ _ _ _ _ _

noncomputable def compCell {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator) (n : ℕ)
    (a b : X.underlying.Cell (n+1)) (hab : X.underlying.target n a = X.underlying.source n b) :
    X.underlying.Cell (n+1) := X.eval (C.composition hC n) (X.compositionTuple n a b hab)

@[simp] theorem compCell_source {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator) (n : ℕ)
    (a b : X.underlying.Cell (n+1)) (hab : X.underlying.target n a = X.underlying.source n b) :
    X.underlying.source n (X.compCell hC n a b hab) = X.underlying.source n a := by
  change X.eval (C.base (Shape.source n)) (X.eval _ _) = _
  rw [← eval_comp, composition_source, C.base_comp, eval_comp, compositionTuple_left]
  rfl

@[simp] theorem compCell_target {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator) (n : ℕ)
    (a b : X.underlying.Cell (n+1)) (hab : X.underlying.target n a = X.underlying.source n b) :
    X.underlying.target n (X.compCell hC n a b hab) = X.underlying.target n b := by
  change X.eval (C.base (Shape.target n)) (X.eval _ _) = _
  rw [← eval_comp, composition_target, C.base_comp, eval_comp, compositionTuple_right]
  rfl

noncomputable def inverseCell {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator) (n : ℕ)
    (a : X.underlying.Cell (n+1)) : X.underlying.Cell (n+1) := X.eval (C.inverse hC n) a

@[simp] theorem inverseCell_source {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a : X.underlying.Cell (n+1)) :
    X.underlying.source n (X.inverseCell hC n a) = X.underlying.target n a := by
  change X.presheaf.obj (op (⟨Shape.globe (n+1)⟩ : C.Obj)) at a
  change X.eval (C.base (Shape.source n)) (X.eval _ a) = _
  rw [← eval_comp, inverse_source]
  rfl

@[simp] theorem inverseCell_target {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a : X.underlying.Cell (n+1)) :
    X.underlying.target n (X.inverseCell hC n a) = X.underlying.source n a := by
  change X.presheaf.obj (op (⟨Shape.globe (n+1)⟩ : C.Obj)) at a
  change X.eval (C.base (Shape.target n)) (X.eval _ a) = _
  rw [← eval_comp, inverse_target]
  rfl

theorem map_inverseCell {C : GlobularTheory.{v}} {X Y : C.Model} (f : X ⟶ Y)
    (hC : C.IsCoherator) (n : ℕ) (a : X.underlying.Cell (n+1)) :
    (underlyingMap f).app (n+1) (X.inverseCell hC n a) =
      Y.inverseCell hC n ((underlyingMap f).app (n+1) a) :=
  map_eval f (C.inverse hC n) a

end Model
end GlobularTheory
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model

theorem sumTuple_ext {C : GlobularTheory.{v}} (X : C.Model)
    (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h)
    {x y : X.presheaf.obj (op (⟨S.attach b h hl hr⟩ : C.Obj))}
    (h₀ : X.eval (C.base (S.inl b h hl hr)) x = X.eval (C.base (S.inl b h hl hr)) y)
    (h₁ : X.eval (C.base (S.inr b h hl hr)) x = X.eval (C.base (S.inr b h hl hr)) y) : x = y :=
  Types.ext_of_isPullback (X.sums S b h hl hr) h₀ h₁

theorem map_compositionTuple {C : GlobularTheory.{v}} {X Y : C.Model} (f : X ⟶ Y)
    (n : ℕ) (a b : X.underlying.Cell (n+1))
    (hab : X.underlying.target n a = X.underlying.source n b) :
    f.app (op (⟨compositionShape n⟩ : C.Obj)) (X.compositionTuple n a b hab) =
      Y.compositionTuple n ((underlyingMap f).app (n+1) a) ((underlyingMap f).app (n+1) b)
        (by rw [← (underlyingMap f).target_app, ← (underlyingMap f).source_app, hab]) := by
  apply Y.sumTuple_ext (Shape.globe (n+1)) n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)
  · change Y.eval (C.base (compositionLeft n)) (f.app _ _) = Y.eval (C.base (compositionLeft n)) _
    rw [← map_eval, compositionTuple_left, compositionTuple_left]
    rfl
  · change Y.eval (C.base (compositionRight n)) (f.app _ _) = Y.eval (C.base (compositionRight n)) _
    rw [← map_eval, compositionTuple_right, compositionTuple_right]
    rfl

theorem map_compCell {C : GlobularTheory.{v}} {X Y : C.Model} (f : X ⟶ Y)
    (hC : C.IsCoherator) (n : ℕ) (a b : X.underlying.Cell (n+1))
    (hab : X.underlying.target n a = X.underlying.source n b) :
    (underlyingMap f).app (n+1) (X.compCell hC n a b hab) =
      Y.compCell hC n ((underlyingMap f).app (n+1) a) ((underlyingMap f).app (n+1) b)
        (by rw [← (underlyingMap f).target_app, ← (underlyingMap f).source_app, hab]) := by
  exact (map_eval f (C.composition hC n) (X.compositionTuple n a b hab)).trans
    (congrArg (Y.eval (C.composition hC n)) (map_compositionTuple f n a b hab))

noncomputable def tupleMap {C : GlobularTheory.{v}} (X : C.Model) (S : Shape)
    (t : X.presheaf.obj (op (⟨S⟩ : C.Obj))) : freeShape C S ⟶ X :=
  yonedaEquiv.symm t

@[simp] theorem tupleMap_app {C : GlobularTheory.{v}} (X : C.Model) (S : Shape)
    (t : X.presheaf.obj (op (⟨S⟩ : C.Obj))) (n : ℕ)
    (a : C.Hom (Shape.globe n) S) :
    (underlyingMap (X.tupleMap S t)).app n a = X.eval a t := rfl

theorem joined_of_parallel_expressions {C : GlobularTheory.{v}} (X : C.Model)
    (hC : C.IsCoherator) (S : Shape) (n : ℕ)
    (a b : (freeShape C S).underlying.Cell n)
    (hp : (freeShape C S).underlying.Parallel n a b)
    (t : X.presheaf.obj (op (⟨S⟩ : C.Obj))) :
    X.underlying.Joined n (X.eval a t) (X.eval b t) :=
  (underlyingMap (X.tupleMap S t)).map_joined (freeShape_joined C hC S n a b hp)

noncomputable def topCell (C : GlobularTheory.{v}) (n : ℕ) :
    (disk C n).underlying.Cell n := C.id (Shape.globe n)

@[simp] theorem tupleMap_topCell {C : GlobularTheory.{v}} (X : C.Model) (n : ℕ)
    (a : X.underlying.Cell n) :
    (underlyingMap (X.tupleMap (Shape.globe n) a)).app n (topCell C n) = a :=
  X.eval_id a

theorem compCell_left_unit {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a : X.underlying.Cell (n+1)) :
    X.underlying.Joined (n+1)
      (X.compCell hC n (X.unitCell hC n (X.underlying.source n a)) a
        (X.unitCell_target hC n _)) a := by
  let D := disk C (n+1)
  let c := topCell C (n+1)
  let f : D ⟶ X := X.tupleMap (Shape.globe (n+1)) a
  have hf : (underlyingMap f).app (n+1) c = a := X.tupleMap_topCell (n+1) a
  let u := D.compCell hC n (D.unitCell hC n (D.underlying.source n c)) c
    (D.unitCell_target hC n _)
  have hp : D.underlying.Parallel (n+1) u c := by
    constructor <;> dsimp [u] <;> simp only [compCell_source, compCell_target, unitCell_source]
  have h := (underlyingMap f).map_joined
    (freeShape_joined C hC (Shape.globe (n+1)) (n+1) u c hp)
  simpa only [u, map_compCell f, map_unitCell f,
    (underlyingMap f).source_app, hf] using h

theorem compCell_right_unit {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a : X.underlying.Cell (n+1)) :
    X.underlying.Joined (n+1)
      (X.compCell hC n a (X.unitCell hC n (X.underlying.target n a))
        (X.unitCell_source hC n _).symm) a := by
  let D := disk C (n+1)
  let c := topCell C (n+1)
  let f : D ⟶ X := X.tupleMap (Shape.globe (n+1)) a
  have hf : (underlyingMap f).app (n+1) c = a := X.tupleMap_topCell (n+1) a
  let u := D.compCell hC n c (D.unitCell hC n (D.underlying.target n c))
    (D.unitCell_source hC n _).symm
  have hp : D.underlying.Parallel (n+1) u c := by
    constructor <;> dsimp [u] <;> simp only [compCell_source, compCell_target, unitCell_target]
  have h := (underlyingMap f).map_joined
    (freeShape_joined C hC (Shape.globe (n+1)) (n+1) u c hp)
  simpa only [u, map_compCell f, map_unitCell f,
    (underlyingMap f).target_app, hf] using h

theorem compCell_inverse_right {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a : X.underlying.Cell (n+1)) :
    X.underlying.Joined (n+1)
      (X.compCell hC n a (X.inverseCell hC n a) (X.inverseCell_source hC n a).symm)
      (X.unitCell hC n (X.underlying.source n a)) := by
  let D := disk C (n+1)
  let c := topCell C (n+1)
  let f : D ⟶ X := X.tupleMap (Shape.globe (n+1)) a
  have hf : (underlyingMap f).app (n+1) c = a := X.tupleMap_topCell (n+1) a
  let u := D.compCell hC n c (D.inverseCell hC n c) (D.inverseCell_source hC n c).symm
  let z := D.unitCell hC n (D.underlying.source n c)
  have hp : D.underlying.Parallel (n+1) u z := by
    constructor <;> dsimp [u, z] <;>
      simp only [compCell_source, compCell_target, inverseCell_target, unitCell_source, unitCell_target]
  have h := (underlyingMap f).map_joined
    (freeShape_joined C hC (Shape.globe (n+1)) (n+1) u z hp)
  simpa only [u, z, map_compCell f, map_unitCell f, map_inverseCell f,
    (underlyingMap f).source_app, hf] using h

theorem compCell_inverse_left {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a : X.underlying.Cell (n+1)) :
    X.underlying.Joined (n+1)
      (X.compCell hC n (X.inverseCell hC n a) a (X.inverseCell_target hC n a))
      (X.unitCell hC n (X.underlying.target n a)) := by
  let D := disk C (n+1)
  let c := topCell C (n+1)
  let f : D ⟶ X := X.tupleMap (Shape.globe (n+1)) a
  have hf : (underlyingMap f).app (n+1) c = a := X.tupleMap_topCell (n+1) a
  let u := D.compCell hC n (D.inverseCell hC n c) c (D.inverseCell_target hC n c)
  let z := D.unitCell hC n (D.underlying.target n c)
  have hp : D.underlying.Parallel (n+1) u z := by
    constructor <;> dsimp [u, z] <;>
      simp only [compCell_source, compCell_target, inverseCell_source, unitCell_source, unitCell_target]
  have h := (underlyingMap f).map_joined
    (freeShape_joined C hC (Shape.globe (n+1)) (n+1) u z hp)
  simpa only [u, z, map_compCell f, map_unitCell f, map_inverseCell f,
    (underlyingMap f).target_app, hf] using h

end GlobularTheory.Model
end Grothendieck

namespace Grothendieck.GlobularSet

theorem Hom.boundaryMap_id (X : GlobularSet.{u}) (n : ℕ) (b : X.Boundary n) :
    (Hom.id X).boundaryMap n b = b := by
  cases n with
  | zero =>
    change (PUnit.unit : PUnit) = b
    exact Subsingleton.elim _ _
  | succ n => exact Subtype.ext rfl

theorem HasFillers.joined {X : GlobularSet.{u}} (hX : X.HasFillers)
    {n : ℕ} {a b : X.Cell n} (hp : X.Parallel n a b) : X.Joined n a b := by
  obtain ⟨z, hz⟩ := hX (n+1) ⟨(a,b), hp⟩
  exact ⟨z, congrArg (fun x => x.1.1) hz, congrArg (fun x => x.1.2) hz⟩

theorem HasFillers.retract {X Y : GlobularSet.{u}} (hY : Y.HasFillers)
    (i : Hom X Y) (r : Hom Y X) (hir : i.comp r = Hom.id X) : X.HasFillers := by
  intro n b
  obtain ⟨y, hy⟩ := hY n (i.boundaryMap n b)
  refine ⟨r.app n y, ?_⟩
  rw [← r.boundary_app, hy, ← Hom.boundaryMap_comp, hir, Hom.boundaryMap_id]

theorem hasFillers_of_endpoint_factorization {X Y P : GlobularSet.{u}}
    (hX : X.HasFillers) (i : Hom X Y) (r : Hom Y X) (h : Hom Y P)
    (p₀ p₁ : Hom P Y) (hh₀ : h.comp p₀ = Hom.id Y)
    (hh₁ : h.comp p₁ = r.comp i) (hp₁ : LiftsBoundaries p₁) : Y.HasFillers := by
  intro n b
  obtain ⟨x, hx⟩ := hX n (r.boundaryMap n b)
  have hb : Y.boundary n (i.app n x) = p₁.boundaryMap n (h.boundaryMap n b) := by
    rw [← i.boundary_app, hx, ← Hom.boundaryMap_comp, ← Hom.boundaryMap_comp, hh₁]
  obtain ⟨z, hz, _⟩ := hp₁ n (h.boundaryMap n b) (i.app n x) hb
  refine ⟨p₀.app n z, ?_⟩
  rw [← p₀.boundary_app, hz, ← Hom.boundaryMap_comp, hh₀, Hom.boundaryMap_id]

def LiftsSource {X Y : GlobularSet.{u}} (f : Hom X Y) (n : ℕ) : Prop :=
  ∀ (x : X.Cell n) (y : Y.Cell (n+1)), Y.source n y = f.app n x →
    ∃ z : X.Cell (n+1), X.source n z = x ∧ f.app (n+1) z = y

theorem liftsBoundary_of_contractible {X Y : GlobularSet.{u}} (f : Hom X Y)
    (hX : X.HasFillers) (hY : Y.HasFillers) (n : ℕ) (hf : LiftsSource f n)
    (b : X.Boundary n) (y : Y.Cell n) (hy : Y.boundary n y = f.boundaryMap n b) :
    ∃ x : X.Cell n, X.boundary n x = b ∧ f.app n x = y := by
  obtain ⟨x, hx⟩ := hX n b
  have hp : Y.Parallel n (f.app n x) y := by
    rw [parallel_iff_boundary_eq, ← f.boundary_app, hx, hy]
  obtain ⟨c, hc₀, hc₁⟩ := hY.joined hp
  obtain ⟨d, hd₀, hd⟩ := hf x c hc₀
  refine ⟨X.target n d, ?_, ?_⟩
  · have h := (parallel_iff_boundary_eq X n (X.source n d) (X.target n d)).1
      (Joined.parallel ⟨d, rfl, rfl⟩)
    rw [hd₀, hx] at h
    exact h.symm
  · rw [f.target_app, hd, hc₁]

end Grothendieck.GlobularSet

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite

namespace Shape

theorem attach_seam (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h)
    {k : ℕ} (hk : k < h) :
    (S.attach b h hl hr).seam hk = face hk true ≫ S.inr b h hl hr := rfl

end Shape

namespace GlobularTheory

def tripleShape (n : ℕ) : Shape :=
  (compositionShape n).attach n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def tripleFirst (n : ℕ) : Shape.globe (n+1) ⟶ tripleShape n :=
  compositionLeft n ≫ (compositionShape n).inl n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def tripleMiddle (n : ℕ) : Shape.globe (n+1) ⟶ tripleShape n :=
  compositionRight n ≫ (compositionShape n).inl n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def tripleLast (n : ℕ) : Shape.globe (n+1) ⟶ tripleShape n :=
  (compositionShape n).inr n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

theorem triple_first_middle (n : ℕ) :
    Shape.target n ≫ tripleFirst n = Shape.source n ≫ tripleMiddle n := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (compositionShape n).inl n (n+1)
      (Nat.lt_succ_self n) (Nat.lt_succ_self n)) (composition_seam n)).trans
        (Category.assoc _ _ _))

theorem triple_middle_last (n : ℕ) :
    Shape.target n ≫ tripleMiddle n = Shape.source n ≫ tripleLast n := by
  have h := Shape.seam_inl (compositionShape n) n (n+1)
    (Nat.lt_succ_self n) (Nat.lt_succ_self n)
  change (Shape.target n ≫ compositionRight n) ≫ _ = Shape.source n ≫ _ at h
  exact (Category.assoc _ _ _).symm.trans h

namespace Model

noncomputable def tripleTuple {C : GlobularTheory.{v}} (X : C.Model) (n : ℕ)
    (a b c : X.underlying.Cell (n+1))
    (hab : X.underlying.target n a = X.underlying.source n b)
    (hbc : X.underlying.target n b = X.underlying.source n c) :
    X.presheaf.obj (op (⟨tripleShape n⟩ : C.Obj)) :=
  X.sumTuple (compositionShape n) n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)
    (X.compositionTuple n a b hab) c (by
      change X.eval (C.base (Shape.target n ≫ compositionRight n)) _ = _
      rw [C.base_comp, eval_comp, compositionTuple_right]
      exact hbc)

@[simp] theorem tripleTuple_first {C : GlobularTheory.{v}} (X : C.Model) (n : ℕ)
    (a b c : X.underlying.Cell (n+1))
    (hab : X.underlying.target n a = X.underlying.source n b)
    (hbc : X.underlying.target n b = X.underlying.source n c) :
    X.eval (C.base (tripleFirst n)) (X.tripleTuple n a b c hab hbc) = a := by
  let j : compositionShape n ⟶ tripleShape n := (compositionShape n).inl n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)
  let t := X.tripleTuple n a b c hab hbc
  change X.eval (C.base (compositionLeft n ≫ j)) t = a
  rw [C.base_comp, eval_comp]
  have hj : X.eval (C.base j) t = X.compositionTuple n a b hab :=
    X.sumTuple_left _ _ _ _ _ _ _ _
  rw [hj, compositionTuple_left]

@[simp] theorem tripleTuple_middle {C : GlobularTheory.{v}} (X : C.Model) (n : ℕ)
    (a b c : X.underlying.Cell (n+1))
    (hab : X.underlying.target n a = X.underlying.source n b)
    (hbc : X.underlying.target n b = X.underlying.source n c) :
    X.eval (C.base (tripleMiddle n)) (X.tripleTuple n a b c hab hbc) = b := by
  let j : compositionShape n ⟶ tripleShape n := (compositionShape n).inl n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)
  let t := X.tripleTuple n a b c hab hbc
  change X.eval (C.base (compositionRight n ≫ j)) t = b
  rw [C.base_comp, eval_comp]
  have hj : X.eval (C.base j) t = X.compositionTuple n a b hab :=
    X.sumTuple_left _ _ _ _ _ _ _ _
  rw [hj, compositionTuple_right]

@[simp] theorem tripleTuple_last {C : GlobularTheory.{v}} (X : C.Model) (n : ℕ)
    (a b c : X.underlying.Cell (n+1))
    (hab : X.underlying.target n a = X.underlying.source n b)
    (hbc : X.underlying.target n b = X.underlying.source n c) :
    X.eval (C.base (tripleLast n)) (X.tripleTuple n a b c hab hbc) = c :=
  X.sumTuple_right _ _ _ _ _ _ _ _

theorem compCell_assoc {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a b c : X.underlying.Cell (n+1))
    (hab : X.underlying.target n a = X.underlying.source n b)
    (hbc : X.underlying.target n b = X.underlying.source n c) :
    X.underlying.Joined (n+1)
      (X.compCell hC n (X.compCell hC n a b hab) c (by rw [compCell_target, hbc]))
      (X.compCell hC n a (X.compCell hC n b c hbc) (by rw [compCell_source, hab])) := by
  let D := freeShape C (tripleShape n)
  let A : D.underlying.Cell (n+1) := C.base (tripleFirst n)
  let B : D.underlying.Cell (n+1) := C.base (tripleMiddle n)
  let E : D.underlying.Cell (n+1) := C.base (tripleLast n)
  have hAB : D.underlying.target n A = D.underlying.source n B := by
    change C.comp (C.base (Shape.target n)) (C.base (tripleFirst n)) =
      C.comp (C.base (Shape.source n)) (C.base (tripleMiddle n))
    rw [← C.base_comp, ← C.base_comp, triple_first_middle]
  have hBE : D.underlying.target n B = D.underlying.source n E := by
    change C.comp (C.base (Shape.target n)) (C.base (tripleMiddle n)) =
      C.comp (C.base (Shape.source n)) (C.base (tripleLast n))
    rw [← C.base_comp, ← C.base_comp, triple_middle_last]
  let f : D ⟶ X := X.tupleMap (tripleShape n) (X.tripleTuple n a b c hab hbc)
  have hfA : (underlyingMap f).app (n+1) A = a := X.tripleTuple_first n a b c hab hbc
  have hfB : (underlyingMap f).app (n+1) B = b := X.tripleTuple_middle n a b c hab hbc
  have hfE : (underlyingMap f).app (n+1) E = c := X.tripleTuple_last n a b c hab hbc
  let u := D.compCell hC n (D.compCell hC n A B hAB) E (by rw [compCell_target, hBE])
  let z := D.compCell hC n A (D.compCell hC n B E hBE) (by rw [compCell_source, hAB])
  have hp : D.underlying.Parallel (n+1) u z := by
    constructor <;> dsimp [u, z] <;> simp only [compCell_source, compCell_target]
  have h := (underlyingMap f).map_joined (freeShape_joined C hC (tripleShape n) (n+1) u z hp)
  simpa only [u, z, map_compCell f, hfA, hfB, hfE] using h

end Model
end GlobularTheory
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite

namespace Shape

theorem face_two_source (n : ℕ) (side : Bool) :
    face (show n < n+2 by omega) side =
      face (Nat.lt_succ_self n) side ≫ source (n+1) :=
  GlobularTheory.shapeGlobes.map_comp (Globe.face (Nat.lt_succ_self n) side) (Globe.source (n+1))

theorem globe_seam_general (n k : ℕ) (h : k < n) :
    (globe n).seam h = face h true := Category.comp_id _

end Shape

namespace GlobularTheory.Model

theorem compCell_congr_left {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a₀ a₁ b : X.underlying.Cell (n+1))
    (hab₀ : X.underlying.target n a₀ = X.underlying.source n b)
    (hab₁ : X.underlying.target n a₁ = X.underlying.source n b)
    (ha : X.underlying.Joined (n+1) a₀ a₁) :
    X.underlying.Joined (n+1) (X.compCell hC n a₀ b hab₀) (X.compCell hC n a₁ b hab₁) := by
  obtain ⟨h, hs, ht⟩ := ha
  let hn : n < n+2 := by omega
  let S := (Shape.globe (n+2)).attach n (n+1) hn (Nat.lt_succ_self n)
  let D := freeShape C S
  let l : Shape.globe (n+2) ⟶ S := (Shape.globe (n+2)).inl n (n+1) hn (Nat.lt_succ_self n)
  let r : Shape.globe (n+1) ⟶ S := (Shape.globe (n+2)).inr n (n+1) hn (Nat.lt_succ_self n)
  let H : D.underlying.Cell (n+2) := C.base l
  let B : D.underlying.Cell (n+1) := C.base r
  let A₀ := D.underlying.source (n+1) H
  let A₁ := D.underlying.target (n+1) H
  have hAB₀ : D.underlying.target n A₀ = D.underlying.source n B := by
    change C.comp (C.base (Shape.face (Nat.lt_succ_self n) true))
        (C.comp (C.base (Shape.source (n+1))) (C.base l)) =
      C.comp (C.base (Shape.source n)) (C.base r)
    rw [← C.assoc, ← C.base_comp, ← Shape.face_two_source, ← C.base_comp, ← C.base_comp]
    exact congrArg C.base (by
      simpa only [S, l, r, Shape.globe_seam_general, Shape.source] using
        Shape.seam_inl (Shape.globe (n+2)) n (n+1) hn (Nat.lt_succ_self n))
  have hAB₁ : D.underlying.target n A₁ = D.underlying.source n B :=
    (D.underlying.target_source n H).symm.trans hAB₀
  let t := X.sumTuple (Shape.globe (n+2)) n (n+1) hn (Nat.lt_succ_self n) h b (by
    change X.presheaf.obj (op (⟨Shape.globe (n+2)⟩ : C.Obj)) at h
    change X.presheaf.obj (op (⟨Shape.globe (n+1)⟩ : C.Obj)) at b
    rw [Shape.globe_seam_general, Shape.face_two_source, C.base_comp, eval_comp]
    change X.underlying.target n (X.underlying.source (n+1) h) = X.underlying.source n b
    rw [hs, hab₀])
  let f : D ⟶ X := X.tupleMap S t
  have hfH : (underlyingMap f).app (n+2) H = h := X.sumTuple_left _ _ _ _ _ _ _ _
  have hfB : (underlyingMap f).app (n+1) B = b := X.sumTuple_right _ _ _ _ _ _ _ _
  have hfA₀ : (underlyingMap f).app (n+1) A₀ = a₀ := by
    rw [(underlyingMap f).source_app, hfH, hs]
  have hfA₁ : (underlyingMap f).app (n+1) A₁ = a₁ := by
    rw [(underlyingMap f).target_app, hfH, ht]
  let u := D.compCell hC n A₀ B hAB₀
  let z := D.compCell hC n A₁ B hAB₁
  have hp : D.underlying.Parallel (n+1) u z := by
    constructor
    · dsimp [u, z]
      simp only [compCell_source]
      exact D.underlying.source_source n H
    · dsimp [u, z]
      simp only [compCell_target]
  have hz := (underlyingMap f).map_joined (freeShape_joined C hC S (n+1) u z hp)
  simpa only [u, z, map_compCell f, hfA₀, hfA₁, hfB] using hz

theorem compCell_congr_right {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a b₀ b₁ : X.underlying.Cell (n+1))
    (hab₀ : X.underlying.target n a = X.underlying.source n b₀)
    (hab₁ : X.underlying.target n a = X.underlying.source n b₁)
    (hb : X.underlying.Joined (n+1) b₀ b₁) :
    X.underlying.Joined (n+1) (X.compCell hC n a b₀ hab₀) (X.compCell hC n a b₁ hab₁) := by
  obtain ⟨h, hs, ht⟩ := hb
  let hn : n < n+2 := by omega
  let S := (Shape.globe (n+1)).attach n (n+2) (Nat.lt_succ_self n) hn
  let D := freeShape C S
  let l : Shape.globe (n+1) ⟶ S := (Shape.globe (n+1)).inl n (n+2) (Nat.lt_succ_self n) hn
  let r : Shape.globe (n+2) ⟶ S := (Shape.globe (n+1)).inr n (n+2) (Nat.lt_succ_self n) hn
  let A : D.underlying.Cell (n+1) := C.base l
  let H : D.underlying.Cell (n+2) := C.base r
  let B₀ := D.underlying.source (n+1) H
  let B₁ := D.underlying.target (n+1) H
  have hAB₀ : D.underlying.target n A = D.underlying.source n B₀ := by
    change C.comp (C.base (Shape.target n)) (C.base l) =
      C.comp (C.base (Shape.face (Nat.lt_succ_self n) false))
        (C.comp (C.base (Shape.source (n+1))) (C.base r))
    rw [← C.assoc]
    simp only [← C.base_comp]
    rw [← Shape.face_two_source]
    exact congrArg C.base (by
      simpa only [Shape.globe_seam] using
        Shape.seam_inl (Shape.globe (n+1)) n (n+2) (Nat.lt_succ_self n) hn)
  have hAB₁ : D.underlying.target n A = D.underlying.source n B₁ :=
    hAB₀.trans (D.underlying.source_source n H)
  let t := X.sumTuple (Shape.globe (n+1)) n (n+2) (Nat.lt_succ_self n) hn a h (by
    change X.presheaf.obj (op (⟨Shape.globe (n+2)⟩ : C.Obj)) at h
    change X.presheaf.obj (op (⟨Shape.globe (n+1)⟩ : C.Obj)) at a
    rw [Shape.globe_seam, Shape.face_two_source, C.base_comp, eval_comp]
    change X.underlying.target n a = X.underlying.source n (X.underlying.source (n+1) h)
    rw [hs, hab₀])
  let f : D ⟶ X := X.tupleMap S t
  have hfA : (underlyingMap f).app (n+1) A = a := X.sumTuple_left _ _ _ _ _ _ _ _
  have hfH : (underlyingMap f).app (n+2) H = h := X.sumTuple_right _ _ _ _ _ _ _ _
  have hfB₀ : (underlyingMap f).app (n+1) B₀ = b₀ := by
    rw [(underlyingMap f).source_app, hfH, hs]
  have hfB₁ : (underlyingMap f).app (n+1) B₁ = b₁ := by
    rw [(underlyingMap f).target_app, hfH, ht]
  let u := D.compCell hC n A B₀ hAB₀
  let z := D.compCell hC n A B₁ hAB₁
  have hp : D.underlying.Parallel (n+1) u z := by
    constructor
    · dsimp [u, z]
      simp only [compCell_source]
    · dsimp [u, z]
      simp only [compCell_target]
      exact D.underlying.target_source n H
  have hz := (underlyingMap f).map_joined (freeShape_joined C hC S (n+1) u z hp)
  simpa only [u, z, map_compCell f, hfA, hfB₀, hfB₁] using hz

end GlobularTheory.Model
end Grothendieck

namespace Grothendieck.GlobularTheory.Model
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable def targetDisk (C : GlobularTheory.{v}) (n : ℕ) :
    disk C n ⟶ disk C (n+1) :=
  show (disk C n).presheaf ⟶ (disk C (n+1)).presheaf from
    yoneda.map (show (⟨Shape.globe n⟩ : C.Obj) ⟶ ⟨Shape.globe (n+1)⟩ from
      C.base (Shape.target n))

@[simp] theorem cellEquiv_targetDisk {C : GlobularTheory.{v}} {X : C.Model}
    (n : ℕ) (a : disk C (n+1) ⟶ X) :
    cellEquiv X n (targetDisk C n ≫ a) = X.underlying.target n (cellEquiv X (n+1) a) :=
  (yonedaEquiv_naturality a
    (show (⟨Shape.globe n⟩ : C.Obj) ⟶ ⟨Shape.globe (n+1)⟩ from
      C.base (Shape.target n))).symm

structure BoundaryRepresentation (C : GlobularTheory.{v}) (n : ℕ) where
  obj : C.Model
  inclusion : obj ⟶ disk C n
  equiv : ∀ X : C.Model, (obj ⟶ X) ≃ X.underlying.Boundary n
  naturality : ∀ {X Y : C.Model} (f : obj ⟶ X) (g : X ⟶ Y),
    equiv Y (f ≫ g) = (underlyingMap g).boundaryMap n (equiv X f)
  inclusion_boundary : ∀ {X : C.Model} (f : disk C n ⟶ X),
    equiv X (inclusion ≫ f) = X.underlying.boundary n (cellEquiv X n f)

namespace BoundaryRepresentation

noncomputable def zero (C : GlobularTheory.{v}) : BoundaryRepresentation C 0 where
  obj := ⊥_ C.Model
  inclusion := initial.to _
  equiv X :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => initial.to X
      left_inv := fun _ => initial.hom_ext _ _
      right_inv := fun _ => by change (PUnit.unit : PUnit) = _; exact Subsingleton.elim _ _ }
  naturality _ _ := rfl
  inclusion_boundary _ := rfl

variable {C : GlobularTheory.{v}} {n : ℕ} (R : BoundaryRepresentation C n)

noncomputable abbrev nextObj : C.Model := pushout R.inclusion R.inclusion

noncomputable def nextValue (X : C.Model) (f : R.nextObj ⟶ X) :
    X.underlying.Boundary (n+1) :=
  ⟨(cellEquiv X n (pushout.inl _ _ ≫ f), cellEquiv X n (pushout.inr _ _ ≫ f)), by
    rw [GlobularSet.parallel_iff_boundary_eq,
      ← R.inclusion_boundary, ← R.inclusion_boundary, ← Category.assoc, ← Category.assoc,
      pushout.condition]⟩

theorem nextValue_bijective (X : C.Model) : Function.Bijective (R.nextValue X) := by
  constructor
  · intro f g h
    apply pushout.hom_ext
    · apply (cellEquiv X n).injective
      exact congrArg (fun b => b.1.1) h
    · apply (cellEquiv X n).injective
      exact congrArg (fun b => b.1.2) h
  · intro b
    let f := (cellEquiv X n).symm b.1.1
    let g := (cellEquiv X n).symm b.1.2
    have hfg : R.inclusion ≫ f = R.inclusion ≫ g := by
      apply (R.equiv X).injective
      simp only [R.inclusion_boundary, f, g, Equiv.apply_symm_apply]
      exact (GlobularSet.parallel_iff_boundary_eq _ _ _ _).1 b.2
    refine ⟨pushout.desc f g hfg, ?_⟩
    apply Subtype.ext
    change (cellEquiv X n (pushout.inl _ _ ≫ pushout.desc f g hfg),
      cellEquiv X n (pushout.inr _ _ ≫ pushout.desc f g hfg)) = b.1
    simp only [pushout.inl_desc, pushout.inr_desc, f, g, Equiv.apply_symm_apply]

theorem face_condition : R.inclusion ≫ J C n = R.inclusion ≫ targetDisk C n := by
  apply (R.equiv (disk C (n+1))).injective
  rw [R.inclusion_boundary, R.inclusion_boundary]
  have h := GlobularSet.Joined.parallel
    (⟨cellEquiv (disk C (n+1)) (n+1) (𝟙 _), rfl, rfl⟩ :
      (disk C (n+1)).underlying.Joined n
        ((disk C (n+1)).underlying.source n (cellEquiv _ (n+1) (𝟙 _)))
        ((disk C (n+1)).underlying.target n (cellEquiv _ (n+1) (𝟙 _))))
  have hs := cellEquiv_J (X := disk C (n+1)) n (𝟙 _)
  have ht := cellEquiv_targetDisk (X := disk C (n+1)) n (𝟙 _)
  rw [Category.comp_id] at hs ht
  rw [hs, ht]
  exact (GlobularSet.parallel_iff_boundary_eq _ _ _ _).1 h

noncomputable def succ : BoundaryRepresentation C (n+1) where
  obj := R.nextObj
  inclusion := pushout.desc (J C n) (targetDisk C n) R.face_condition
  equiv X := Equiv.ofBijective (R.nextValue X) (R.nextValue_bijective X)
  naturality f g := by
    apply Subtype.ext
    apply Prod.ext <;> change cellEquiv _ n (_ ≫ (f ≫ g)) = _
    · rw [← Category.assoc, cellEquiv_comp]; rfl
    · rw [← Category.assoc, cellEquiv_comp]; rfl
  inclusion_boundary f := by
    apply Subtype.ext
    change (cellEquiv _ n (pushout.inl _ _ ≫ (pushout.desc _ _ _ ≫ f)),
      cellEquiv _ n (pushout.inr _ _ ≫ (pushout.desc _ _ _ ≫ f))) =
      (_, _)
    simp only [← Category.assoc, pushout.inl_desc, pushout.inr_desc,
      cellEquiv_J, cellEquiv_targetDisk]

end BoundaryRepresentation

noncomputable def boundaryRepresentation (C : GlobularTheory.{v}) :
    (n : ℕ) → BoundaryRepresentation C n
  | 0 => BoundaryRepresentation.zero C
  | n+1 => (boundaryRepresentation C n).succ

noncomputable abbrev boundaryDisk (C : GlobularTheory.{v}) (n : ℕ) : C.Model :=
  (boundaryRepresentation C n).obj

noncomputable abbrev I (C : GlobularTheory.{v}) (n : ℕ) : boundaryDisk C n ⟶ disk C n :=
  (boundaryRepresentation C n).inclusion

open CategoryTheory CategoryTheory.Limits Opposite

theorem hasLiftingProperty_I_iff {C : GlobularTheory.{v}} {X Y : C.Model}
    (n : ℕ) (p : X ⟶ Y) :
    HasLiftingProperty (I C n) p ↔
      ∀ (b : X.underlying.Boundary n) (y : Y.underlying.Cell n),
        Y.underlying.boundary n y = (underlyingMap p).boundaryMap n b →
        ∃ x : X.underlying.Cell n,
          X.underlying.boundary n x = b ∧ (underlyingMap p).app n x = y := by
  let R := boundaryRepresentation C n
  constructor
  · intro hp b y hy
    let f : boundaryDisk C n ⟶ X := (R.equiv X).symm b
    let g : disk C n ⟶ Y := (cellEquiv Y n).symm y
    have sq : CommSq f (I C n) p g := by
      constructor
      apply (R.equiv Y).injective
      rw [R.naturality, R.inclusion_boundary]
      simpa only [f, g, Equiv.apply_symm_apply] using hy.symm
    let := hp
    refine ⟨cellEquiv X n sq.lift, ?_, ?_⟩
    · rw [← R.inclusion_boundary, sq.fac_left]
      exact (R.equiv X).apply_symm_apply b
    · rw [← cellEquiv_comp, sq.fac_right]
      exact (cellEquiv Y n).apply_symm_apply y
  · intro hp
    constructor
    intro f g sq
    have h : Y.underlying.boundary n (cellEquiv Y n g) =
        (underlyingMap p).boundaryMap n (R.equiv X f) := by
      rw [← R.inclusion_boundary, ← R.naturality, sq.w]
    obtain ⟨x, hx, hpx⟩ := hp (R.equiv X f) (cellEquiv Y n g) h
    let l : disk C n ⟶ X := (cellEquiv X n).symm x
    refine CommSq.HasLift.mk' { l := l, fac_left := ?_, fac_right := ?_ }
    · apply (R.equiv X).injective
      rw [R.inclusion_boundary]
      simpa only [l, Equiv.apply_symm_apply] using hx
    · apply (cellEquiv Y n).injective
      rw [cellEquiv_comp]
      simpa only [l, Equiv.apply_symm_apply] using hpx

theorem liftsBoundaries_iff {C : GlobularTheory.{v}} {X Y : C.Model} (p : X ⟶ Y) :
    GlobularSet.LiftsBoundaries (underlyingMap p) ↔ ∀ n, HasLiftingProperty (I C n) p := by
  simp only [hasLiftingProperty_I_iff, GlobularSet.LiftsBoundaries]

theorem hasLiftingProperty_J_iff {C : GlobularTheory.{v}} {X Y : C.Model}
    (n : ℕ) (p : X ⟶ Y) :
    HasLiftingProperty (J C n) p ↔
      ∀ (x : X.underlying.Cell n) (y : Y.underlying.Cell (n+1)),
        Y.underlying.source n y = (underlyingMap p).app n x →
        ∃ z : X.underlying.Cell (n+1),
          X.underlying.source n z = x ∧ (underlyingMap p).app (n+1) z = y := by
  constructor
  · intro hp x y hy
    let f : disk C n ⟶ X := (cellEquiv X n).symm x
    let g : disk C (n+1) ⟶ Y := (cellEquiv Y (n+1)).symm y
    have sq : CommSq f (J C n) p g := by
      constructor
      apply (cellEquiv Y n).injective
      rw [cellEquiv_comp, cellEquiv_J]
      simpa only [f, g, Equiv.apply_symm_apply] using hy.symm
    let := hp
    refine ⟨cellEquiv X (n+1) sq.lift, ?_, ?_⟩
    · rw [← cellEquiv_J, sq.fac_left]
      exact (cellEquiv X n).apply_symm_apply x
    · rw [← cellEquiv_comp, sq.fac_right]
      exact (cellEquiv Y (n+1)).apply_symm_apply y
  · intro hp
    constructor
    intro f g sq
    have h : Y.underlying.source n (cellEquiv Y (n+1) g) =
        (underlyingMap p).app n (cellEquiv X n f) := by
      rw [← cellEquiv_J, ← cellEquiv_comp, sq.w]
    obtain ⟨z, hz, hpz⟩ := hp (cellEquiv X n f) (cellEquiv Y (n+1) g) h
    let l : disk C (n+1) ⟶ X := (cellEquiv X (n+1)).symm z
    refine CommSq.HasLift.mk' { l := l, fac_left := ?_, fac_right := ?_ }
    · apply (cellEquiv X n).injective
      rw [cellEquiv_J]
      simpa only [l, Equiv.apply_symm_apply] using hz
    · apply (cellEquiv Y (n+1)).injective
      rw [cellEquiv_comp]
      simpa only [l, Equiv.apply_symm_apply] using hpz

end Grothendieck.GlobularTheory.Model

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck.GlobularTheory.Model
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] Cardinal.fact_isRegular_aleph0

instance presheafFunctor_finitelyAccessible (C : GlobularTheory.{v}) :
    (presheafFunctor C).IsCardinalAccessible Cardinal.aleph0.{v} := by
  let : C.sumComparisons.isLocal.ι.IsCardinalAccessible Cardinal.aleph0.{v} := by
    apply MorphismProperty.isCardinalAccessible_ι_isLocal _ Cardinal.aleph0.{v}
    rintro X Y f ⟨t⟩
    exact ⟨C.sumComparison_source_presentable t,
      C.shrinkYoneda_cardinalPresentable (C.sumCone t).pt.unop⟩
  let : (toLocal C).IsEquivalence := (localEquivalence C).isEquivalence_functor
  change ((toLocal C) ⋙ C.sumComparisons.isLocal.ι).IsCardinalAccessible Cardinal.aleph0.{v}
  infer_instance

instance freeShape_finitelyPresentable (C : GlobularTheory.{v}) (S : Shape) :
    IsCardinalPresentable (freeShape C S) Cardinal.aleph0.{v} := by
  let e : coyoneda.obj (op (freeShape C S)) ≅
      presheafFunctor C ⋙ (evaluation C.Objᵒᵖ (Type v)).obj (op (⟨S⟩ : C.Obj)) :=
    NatIso.ofComponents (fun X => Equiv.toIso yonedaEquiv)
  exact Functor.isCardinalAccessible_of_natIso e.symm Cardinal.aleph0.{v}

instance disk_finitelyPresentable (C : GlobularTheory.{v}) (n : ℕ) :
    IsCardinalPresentable (disk C n) Cardinal.aleph0.{v} :=
  freeShape_finitelyPresentable C (Shape.globe n)

instance boundaryDisk_finitelyPresentable (C : GlobularTheory.{v}) (n : ℕ) :
    IsCardinalPresentable (boundaryDisk C n) Cardinal.aleph0.{v} := by
  induction n with
  | zero =>
    change IsCardinalPresentable (⊥_ C.Model) Cardinal.aleph0.{v}
    let (k : Discrete PEmpty) : IsCardinalPresentable
        ((Functor.empty C.Model).obj k) Cardinal.aleph0.{v} := by cases k.as
    apply isCardinalPresentable_of_isColimit _ (initialIsInitial) Cardinal.aleph0.{v}
    exact hasCardinalLT_of_finite _ _ le_rfl
  | succ n ih =>
    let := ih
    change IsCardinalPresentable (pushout (I C n) (I C n)) Cardinal.aleph0.{v}
    let (k : WalkingSpan) : IsCardinalPresentable
        ((span (I C n) (I C n)).obj k) Cardinal.aleph0.{v} := by
      cases k with
      | none => exact ih
      | some k => cases k <;> exact disk_finitelyPresentable C n
    apply isCardinalPresentable_of_isColimit _ (colimit.isColimit _) Cardinal.aleph0.{v}
    exact hasCardinalLT_of_finite _ _ le_rfl

open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] Cardinal.fact_isRegular_aleph0

noncomputable def highBoundaries (C : GlobularTheory.{v}) (q : ℕ) :
    MorphismProperty C.Model :=
  MorphismProperty.ofHoms (fun n : {n : ℕ // q < n} => I C n.1)

theorem isCoskeletal_iff_local {C : GlobularTheory.{v}} (M : C.Model) (q : ℕ) :
    M.IsCoskeletal q ↔ (highBoundaries C q).isLocal M := by
  constructor
  · intro h A B i hi
    rcases hi with ⟨⟨n, hn⟩⟩
    let R := boundaryRepresentation C n
    constructor
    · intro f g hfg
      apply (cellEquiv M n).injective
      apply (h n hn).1
      rw [← R.inclusion_boundary, ← R.inclusion_boundary]
      exact congrArg (R.equiv M) hfg
    · intro f
      obtain ⟨x, hx⟩ := (h n hn).2 (R.equiv M f)
      refine ⟨(cellEquiv M n).symm x, ?_⟩
      apply (R.equiv M).injective
      rw [R.inclusion_boundary, Equiv.apply_symm_apply]
      exact hx
  · intro h n hn
    have hb := h (I C n) (MorphismProperty.ofHoms.mk (⟨n, hn⟩ : {n : ℕ // q < n}))
    let R := boundaryRepresentation C n
    change Function.Bijective (fun f : disk C n ⟶ M => R.inclusion ≫ f) at hb
    constructor
    · intro x y hxy
      apply (cellEquiv M n).symm.injective
      apply hb.1
      apply (R.equiv M).injective
      simpa only [R.inclusion_boundary, Equiv.apply_symm_apply] using hxy
    · intro b
      obtain ⟨f, hf⟩ := hb.2 ((R.equiv M).symm b)
      change R.inclusion ≫ f = (R.equiv M).symm b at hf
      refine ⟨cellEquiv M n f, ?_⟩
      rw [← R.inclusion_boundary, hf]
      exact (R.equiv M).apply_symm_apply b

theorem highBoundaries_local (C : GlobularTheory.{v}) (q : ℕ) :
    (highBoundaries C q).isLocal = (fun X : C.Model => X.IsCoskeletal q) := by
  funext X
  exact propext (isCoskeletal_iff_local X q).symm

instance cutoffInclusion_finitelyAccessible (C : GlobularTheory.{v}) (q : ℕ) :
    (ObjectProperty.ι (fun X : C.Model => X.IsCoskeletal q)).IsCardinalAccessible
      Cardinal.aleph0.{v} := by
  rw [← highBoundaries_local]
  apply MorphismProperty.isCardinalAccessible_ι_isLocal _ Cardinal.aleph0.{v}
  rintro A B i ⟨⟨n, hn⟩⟩
  exact ⟨boundaryDisk_finitelyPresentable C n, disk_finitelyPresentable C n⟩

theorem cutoff_finitelyPresentable {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : C.Model) [IsCardinalPresentable X Cardinal.aleph0.{v}] :
    IsCardinalPresentable ((cutoffFunctor hC q).obj X) Cardinal.aleph0.{v} :=
  (cutoffAdjunction hC q).isCardinalPresentable_leftAdjoint_obj Cardinal.aleph0.{v} X

open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] Cardinal.fact_isRegular_aleph0

noncomputable instance hasLimits (C : GlobularTheory.{v}) : HasLimitsOfSize.{v,v} C.Model := by
  let := presheafReflection C
  let : HasLimitsOfSize.{v,v} C.sumComparisons.isLocal.FullSubcategory :=
    hasLimits_of_reflective C.sumComparisons.isLocal.ι
  exact Adjunction.has_limits_of_equivalence (localEquivalence C).functor

theorem hasFillers_iff {C : GlobularTheory.{v}} (X : C.Model) :
    X.underlying.HasFillers ↔ ∀ n (f : boundaryDisk C n ⟶ X),
      ∃ g : disk C n ⟶ X, I C n ≫ g = f := by
  constructor
  · intro h n f
    let R := boundaryRepresentation C n
    obtain ⟨x, hx⟩ := h n (R.equiv X f)
    refine ⟨(cellEquiv X n).symm x, (R.equiv X).injective ?_⟩
    change R.equiv X (R.inclusion ≫ (cellEquiv X n).symm x) = R.equiv X f
    simpa only [R.inclusion_boundary, Equiv.apply_symm_apply] using hx
  · intro h n b
    let R := boundaryRepresentation C n
    obtain ⟨g, hg⟩ := h n ((R.equiv X).symm b)
    refine ⟨cellEquiv X n g, ?_⟩
    change R.inclusion ≫ g = (R.equiv X).symm b at hg
    rw [← R.inclusion_boundary, hg, Equiv.apply_symm_apply]

theorem hasFillers_of_filteredColimit {C : GlobularTheory.{v}}
    {K : Type v} [SmallCategory K] [IsFiltered K]
    {F : K ⥤ C.Model} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ k, (F.obj k).underlying.HasFillers) : c.pt.underlying.HasFillers := by
  rw [hasFillers_iff]
  intro n f
  obtain ⟨k, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc f
  obtain ⟨a, ha⟩ := (hasFillers_iff (F.obj k)).1 (hF k) n g
  exact ⟨a ≫ c.ι.app k, by rw [← Category.assoc, ha, hg]⟩

theorem hasFillers_of_cutoffFilteredColimit {C : GlobularTheory.{v}}
    (q : ℕ)
    {K : Type v} [SmallCategory K] [IsFiltered K]
    {F : K ⥤ CutoffModels C q} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ k, (F.obj k).obj.underlying.HasFillers) : c.pt.obj.underlying.HasFillers := by
  let ι := ObjectProperty.ι (fun X : C.Model => X.IsCoskeletal q)
  have : PreservesFilteredColimitsOfSize.{v,v} ι :=
    Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize.mp inferInstance
  exact hasFillers_of_filteredColimit (isColimitOfPreserves ι hc) hF

end Grothendieck.GlobularTheory.Model

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

theorem smallObjectArgument_of_finiteDomains {A : Type u} [Category.{v} A]
    [HasColimitsOfSize.{v,v} A] {ι : Type w} [Small.{v} ι]
    {U V : ι → A} (f : ∀ i, U i ⟶ V i)
    [∀ i, IsCardinalPresentable (U i) Cardinal.aleph0.{v}] :
    (MorphismProperty.ofHoms f).HasSmallObjectArgument.{v} := by
  refine ⟨Cardinal.aleph0.{v}, inferInstance, inferInstance, ?_⟩
  refine { preservesColimit := ?_ }
  rintro _ _ _ _ _ ⟨i⟩ g hg
  infer_instance

namespace GlobularTheory.Model

noncomputable abbrev cutoffDisk {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) : CutoffModels C q := (cutoffFunctor hC q).obj (disk C n)

noncomputable abbrev cutoffBoundary {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) : CutoffModels C q := (cutoffFunctor hC q).obj (boundaryDisk C n)

noncomputable abbrev cutoffI {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) : cutoffBoundary hC q n ⟶ cutoffDisk hC q n :=
  (cutoffFunctor hC q).map (I C n)

noncomputable abbrev cutoffJ {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) : cutoffDisk hC q n ⟶ cutoffDisk hC q (n+1) :=
  (cutoffFunctor hC q).map (J C n)

noncomputable def boundaryClass {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) : MorphismProperty (CutoffModels C q) :=
  MorphismProperty.ofHoms (fun n : {n : ℕ // r ≤ n} => cutoffI hC q n.1)

noncomputable def sourceClass {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) : MorphismProperty (CutoffModels C q) :=
  MorphismProperty.ofHoms (fun n : {n : ℕ // r ≤ n} => cutoffJ hC q n.1)

theorem boundaryClass_rlp_iff {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) {X Y : CutoffModels C q} (p : X ⟶ Y) :
    (boundaryClass hC q r).rlp p ↔
      ∀ n, r ≤ n → HasLiftingProperty (I C n) p.hom := by
  constructor
  · intro hp n hn
    exact ((cutoffAdjunction hC q).hasLiftingProperty_iff _ _).1
      (hp _ (MorphismProperty.ofHoms.mk (⟨n, hn⟩ : {n : ℕ // r ≤ n})))
  · intro hp _ _ i hi
    rcases hi with ⟨⟨n, hn⟩⟩
    exact ((cutoffAdjunction hC q).hasLiftingProperty_iff _ _).2 (hp n hn)

theorem sourceClass_rlp_iff {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) {X Y : CutoffModels C q} (p : X ⟶ Y) :
    (sourceClass hC q r).rlp p ↔
      ∀ n, r ≤ n → HasLiftingProperty (J C n) p.hom := by
  constructor
  · intro hp n hn
    exact ((cutoffAdjunction hC q).hasLiftingProperty_iff _ _).1
      (hp _ (MorphismProperty.ofHoms.mk (⟨n, hn⟩ : {n : ℕ // r ≤ n})))
  · intro hp _ _ i hi
    rcases hi with ⟨⟨n, hn⟩⟩
    exact ((cutoffAdjunction hC q).hasLiftingProperty_iff _ _).2 (hp n hn)

theorem boundaryClass_smallObject {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) : (boundaryClass hC q r).HasSmallObjectArgument.{v} := by
  let := cutoff_hasColimits hC q
  let (n : {n : ℕ // r ≤ n}) : IsCardinalPresentable
      (cutoffBoundary hC q n.1) Cardinal.aleph0.{v} :=
    cutoff_finitelyPresentable hC q (boundaryDisk C n.1)
  exact smallObjectArgument_of_finiteDomains _

theorem sourceClass_smallObject {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) : (sourceClass hC q r).HasSmallObjectArgument.{v} := by
  let := cutoff_hasColimits hC q
  let (n : {n : ℕ // r ≤ n}) : IsCardinalPresentable
      (cutoffDisk hC q n.1) Cardinal.aleph0.{v} :=
    cutoff_finitelyPresentable hC q (disk C n.1)
  exact smallObjectArgument_of_finiteDomains _

def Cofibrant {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q : ℕ)
    (X : CutoffModels C q) : Prop :=
  ∀ {P Q : CutoffModels C q} (p : P ⟶ Q), (boundaryClass hC q 0).rlp p →
    ∀ f : X ⟶ Q, ∃ g : X ⟶ P, g ≫ p = f

theorem Cofibrant.of_cofibration {C : GlobularTheory.{v}} {hC : C.IsCoherator}
    {q : ℕ} {X Y : CutoffModels C q} (hX : Cofibrant hC q X) (i : X ⟶ Y)
    (hi : (boundaryClass hC q 0).rlp.llp i) : Cofibrant hC q Y := by
  intro P Q p hp f
  obtain ⟨g, hg⟩ := hX p hp (i ≫ f)
  let := hi p hp
  have sq : CommSq g i p f := ⟨hg⟩
  exact ⟨sq.lift, sq.fac_right⟩

theorem Cofibrant.retract {C : GlobularTheory.{v}} {hC : C.IsCoherator}
    {q : ℕ} {X Y : CutoffModels C q} (hY : Cofibrant hC q Y)
    (i : X ⟶ Y) (r : Y ⟶ X) (hir : i ≫ r = 𝟙 X) : Cofibrant hC q X := by
  intro P Q p hp f
  obtain ⟨g, hg⟩ := hY p hp (r ≫ f)
  exact ⟨i ≫ g, by rw [Category.assoc, hg, ← Category.assoc, hir, Category.id_comp]⟩

theorem hasLiftingProperty_J_of_I {C : GlobularTheory.{v}} {X Y : C.Model}
    (n : ℕ) (p : X ⟶ Y) (hn : HasLiftingProperty (I C n) p)
    (hn₁ : HasLiftingProperty (I C (n+1)) p) : HasLiftingProperty (J C n) p := by
  rw [hasLiftingProperty_J_iff]
  intro x y hy
  have hb : Y.underlying.boundary n (Y.underlying.target n y) =
      (underlyingMap p).boundaryMap n (X.underlying.boundary n x) := by
    rw [(underlyingMap p).boundary_app]
    have hp := (GlobularSet.parallel_iff_boundary_eq Y.underlying n
      (Y.underlying.source n y) (Y.underlying.target n y)).1
        (GlobularSet.Joined.parallel ⟨y, rfl, rfl⟩)
    rw [hy] at hp
    exact hp.symm
  obtain ⟨z, hz, hpz⟩ := (hasLiftingProperty_I_iff n p).1 hn
    (X.underlying.boundary n x) (Y.underlying.target n y) hb
  let b : X.underlying.Boundary (n+1) := ⟨(x,z),
    (GlobularSet.parallel_iff_boundary_eq _ _ _ _).2 hz.symm⟩
  have hby : Y.underlying.boundary (n+1) y = (underlyingMap p).boundaryMap (n+1) b := by
    apply Subtype.ext
    exact Prod.ext hy hpz.symm
  obtain ⟨a, ha, hpa⟩ := (hasLiftingProperty_I_iff (n+1) p).1 hn₁ b y hby
  exact ⟨a, congrArg (fun v => v.1.1) ha, hpa⟩

theorem sourceClass_cofibration_le {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) : (sourceClass hC q r).rlp.llp ≤ (boundaryClass hC q r).rlp.llp := by
  apply MorphismProperty.antitone_llp
  intro X Y p hp
  rw [sourceClass_rlp_iff]
  have h := (boundaryClass_rlp_iff hC q r p).1 hp
  intro n hn
  exact hasLiftingProperty_J_of_I n p.hom (h n hn) (h (n+1) (by omega))

theorem boundaryClass_cofibration_le {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r s : ℕ) (hrs : r ≤ s) :
    (boundaryClass hC q s).rlp.llp ≤ (boundaryClass hC q r).rlp.llp := by
  apply MorphismProperty.antitone_llp
  intro X Y p hp
  rw [boundaryClass_rlp_iff] at hp ⊢
  exact fun n hn => hp n (hrs.trans hn)

end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck.GlobularTheory.Model
open CategoryTheory CategoryTheory.Limits Opposite

def ExpansionContraction {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) : Prop :=
  ∀ {X Y : CutoffModels C q} (i : X ⟶ Y),
    (sourceClass hC q r).rlp.llp i → Cofibrant hC q X →
      X.obj.underlying.HasFillers → Y.obj.underlying.HasFillers

theorem boundary_rlp_of_source_rlp {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) {X Y : CutoffModels C q} (p : X ⟶ Y)
    (hX : X.obj.underlying.HasFillers) (hY : Y.obj.underlying.HasFillers)
    (hp : (sourceClass hC q r).rlp p) : (boundaryClass hC q r).rlp p := by
  rw [boundaryClass_rlp_iff]
  intro n hn
  rw [hasLiftingProperty_I_iff]
  apply GlobularSet.liftsBoundary_of_contractible (underlyingMap p.hom) hX hY
  exact (hasLiftingProperty_J_iff n p.hom).1
    ((sourceClass_rlp_iff hC q r p).1 hp n hn)

theorem upper_boundary_is_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) (H : ExpansionContraction hC q r)
    {X Y : CutoffModels C q} (i : X ⟶ Y)
    (hi : (boundaryClass hC q r).rlp.llp i) (hX : Cofibrant hC q X)
    (hXF : X.obj.underlying.HasFillers) (hYF : Y.obj.underlying.HasFillers) :
    (sourceClass hC q r).rlp.llp i := by
  let := sourceClass_smallObject hC q r
  let W := sourceClass hC q r
  let F := MorphismProperty.factorizationData W.rlp.llp W.rlp i
  have hZF := H F.i F.hi hX hXF
  have hFp := boundary_rlp_of_source_rlp hC q r F.p hZF hYF F.hp
  let := hi F.p hFp
  have sq : CommSq F.i i F.p (𝟙 Y) := ⟨by rw [Category.comp_id, F.fac]⟩
  let s := sq.lift
  have hs : i ≫ s = F.i := sq.fac_left
  have hsp : s ≫ F.p = 𝟙 Y := sq.fac_right
  intro P Q p hp
  constructor
  intro a b ab
  let := F.hi p hp
  have sq' : CommSq a F.i p (F.p ≫ b) := by
    constructor
    rw [← Category.assoc, F.fac, ab.w]
  refine CommSq.HasLift.mk' ⟨s ≫ sq'.lift, ?_, ?_⟩
  · rw [← Category.assoc, hs, sq'.fac_left]
  · rw [Category.assoc, sq'.fac_right, ← Category.assoc, hsp, Category.id_comp]

theorem upper_pushout_hasFillers {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) (H : ExpansionContraction hC q r)
    {X Y X' Y' : CutoffModels C q} {i : X ⟶ Y} {a : X ⟶ X'}
    {i' : X' ⟶ Y'} {b : Y ⟶ Y'} (sq : IsPushout a i i' b)
    (hi : (boundaryClass hC q r).rlp.llp i) (hX : Cofibrant hC q X)
    (hXF : X.obj.underlying.HasFillers) (hYF : Y.obj.underlying.HasFillers)
    (hX' : Cofibrant hC q X') (hX'F : X'.obj.underlying.HasFillers) :
    Y'.obj.underlying.HasFillers := by
  apply H i' _ hX' hX'F
  exact MorphismProperty.of_isPushout sq
    (upper_boundary_is_source hC q r H i hi hX hXF hYF)

theorem hasLiftingProperty_I_of_unique {C : GlobularTheory.{v}} {X Y : C.Model}
    (p : X ⟶ Y) (n : ℕ) (hX : Function.Bijective (X.underlying.boundary n))
    (hY : Function.Bijective (Y.underlying.boundary n)) :
    HasLiftingProperty (I C n) p := by
  rw [hasLiftingProperty_I_iff]
  intro b y hy
  obtain ⟨x, hx⟩ := hX.2 b
  refine ⟨x, hx, hY.1 ?_⟩
  rw [← (underlyingMap p).boundary_app, hx, hy]

theorem upper_cofibration_low_bijective {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r k : ℕ) (hkq : k ≤ q) (hkr : k < r)
    {X Y : CutoffModels C q} (i : X ⟶ Y)
    (hi : (boundaryClass hC q r).rlp.llp i) :
    Function.Bijective ((underlyingMap i.hom).app k) := by
  let X' : CutoffModels C q := ⟨chosenCutoff hC k X.obj,
    fun j hj => chosenCutoff_coskeletal hC k X.obj j (by omega)⟩
  let Y' : CutoffModels C q := ⟨chosenCutoff hC k Y.obj,
    fun j hj => chosenCutoff_coskeletal hC k Y.obj j (by omega)⟩
  let p : X' ⟶ Y' := ObjectProperty.homMk (((cutoffFunctor hC k).map i.hom).hom)
  let a : X ⟶ X' := ObjectProperty.homMk (cutoffUnit hC k X.obj)
  let b : Y ⟶ Y' := ObjectProperty.homMk (cutoffUnit hC k Y.obj)
  have hp : (boundaryClass hC q r).rlp p := by
    rw [boundaryClass_rlp_iff]
    intro j hj
    exact hasLiftingProperty_I_of_unique p.hom j
      (chosenCutoff_coskeletal hC k X.obj j (by omega))
      (chosenCutoff_coskeletal hC k Y.obj j (by omega))
  let := hi p hp
  have sq : CommSq a i p b := by
    constructor
    apply ObjectProperty.hom_ext
    exact ((cutoffAdjunction hC k).unit.naturality i.hom).symm
  let l := sq.lift
  have ha : Function.Bijective ((underlyingMap a.hom).app k) :=
    cutoffUnit_low_bijective hC k X.obj k le_rfl
  have hb : Function.Bijective ((underlyingMap b.hom).app k) :=
    cutoffUnit_low_bijective hC k Y.obj k le_rfl
  have hil (x : X.obj.underlying.Cell k) :
      (underlyingMap l.hom).app k ((underlyingMap i.hom).app k x) =
        (underlyingMap a.hom).app k x :=
    congrFun (congrArg (fun f => (underlyingMap f.hom).app k) sq.fac_left) x
  have hlp (y : Y.obj.underlying.Cell k) :
      (underlyingMap p.hom).app k ((underlyingMap l.hom).app k y) =
        (underlyingMap b.hom).app k y :=
    congrFun (congrArg (fun f => (underlyingMap f.hom).app k) sq.fac_right) y
  constructor
  · intro x y hxy
    apply ha.1
    rw [← hil, ← hil, hxy]
  · intro y
    obtain ⟨x, hx⟩ := ha.2 ((underlyingMap l.hom).app k y)
    refine ⟨x, hb.1 ?_⟩
    rw [← hlp, hil, hx, hlp]

theorem expansionContraction_top {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) : ExpansionContraction hC q q := by
  intro X Y i hi _ hX
  have hib := sourceClass_cofibration_le hC q q i hi
  intro j b
  by_cases hj : q < j
  · exact (Y.property j hj).2 b
  · obtain ⟨b', hb'⟩ := ((underlyingMap i.hom).boundaryMap_bijective_of_low j
      (fun k hk => upper_cofibration_low_bijective hC q q k (by omega) (by omega) i hib)).2 b
    obtain ⟨x, hx⟩ := hX j b'
    exact ⟨(underlyingMap i.hom).app j x, by
      rw [← (underlyingMap i.hom).boundary_app, hx, hb']⟩

end Grothendieck.GlobularTheory.Model

namespace Grothendieck.GlobularSet

structure LiftStage {A X Y : GlobularSet.{v}} (p : Hom X Y) (f : Hom A Y) (n : ℕ) where
  app : ∀ k, k ≤ n → A.Cell k → X.Cell k
  source_app : ∀ k (h : k+1 ≤ n) x,
    app k (by omega) (A.source k x) = X.source k (app (k+1) h x)
  target_app : ∀ k (h : k+1 ≤ n) x,
    app k (by omega) (A.target k x) = X.target k (app (k+1) h x)
  fac : ∀ k (h : k ≤ n) x, p.app k (app k h x) = f.app k x

namespace LiftStage
variable {A X Y : GlobularSet.{v}} {p : Hom X Y} {f : Hom A Y}

noncomputable def zero (hp : LiftsBoundaries p) : LiftStage p f 0 := by
  have h x := hp 0 PUnit.unit (f.app 0 x) rfl
  choose z _ hz using h
  exact
    { app := fun k hk x => by
        have e : k = 0 := by omega
        subst k
        exact z x
      source_app := fun k hk => by omega
      target_app := fun k hk => by omega
      fac := fun k hk x => by
        have e : k = 0 := by omega
        subst k
        exact hz x }

def nextBoundary {n : ℕ} (a : LiftStage p f n) (x : A.Cell (n+1)) : X.Boundary (n+1) :=
  ⟨(a.app n le_rfl (A.source n x), a.app n le_rfl (A.target n x)), by
    cases n with
    | zero => trivial
    | succ n =>
      constructor
      · rw [← a.source_app n le_rfl, ← a.source_app n le_rfl, A.source_source]
      · rw [← a.target_app n le_rfl, ← a.target_app n le_rfl, A.target_source]⟩

noncomputable def succ {n : ℕ} (a : LiftStage p f n) (hp : LiftsBoundaries p) :
    LiftStage p f (n+1) := by
  have h x : ∃ z, X.boundary (n+1) z = a.nextBoundary x ∧
      p.app (n+1) z = f.app (n+1) x := by
    apply hp
    apply Subtype.ext
    exact Prod.ext ((f.source_app n x).symm.trans (a.fac n le_rfl _).symm)
      ((f.target_app n x).symm.trans (a.fac n le_rfl _).symm)
  choose z hz hzp using h
  have hs x := (congrArg (fun b => b.1.1) (hz x)).symm
  have ht x := (congrArg (fun b => b.1.2) (hz x)).symm
  exact
    { app := fun k hk x => if h : k ≤ n then a.app k h x else by
        have e : k = n+1 := by omega
        subst k
        exact z x
      source_app := fun k hk x => by
        dsimp only
        split_ifs with h h'
        · exact a.source_app k h' x
        · have e : k = n := by omega
          subst k
          exact hs x
        · omega
        · omega
      target_app := fun k hk x => by
        dsimp only
        split_ifs with h h'
        · exact a.target_app k h' x
        · have e : k = n := by omega
          subst k
          exact ht x
        · omega
        · omega
      fac := fun k hk x => by
        dsimp only
        split_ifs with h
        · exact a.fac k h x
        · have e : k = n+1 := by omega
          subst k
          exact hzp x }

@[simp] theorem succ_old {n : ℕ} (a : LiftStage p f n) (hp : LiftsBoundaries p)
    (k : ℕ) (hk : k ≤ n) (x : A.Cell k) :
    (a.succ hp).app k (by omega) x = a.app k hk x := by
  simp only [succ, dite_eq_left hk]

noncomputable def tower (hp : LiftsBoundaries p) : ∀ n, LiftStage p f n
  | 0 => zero hp
  | n+1 => (tower hp n).succ hp

end LiftStage

theorem LiftsBoundaries.lift {A X Y : GlobularSet.{v}} {p : Hom X Y}
    (hp : LiftsBoundaries p) (f : Hom A Y) : ∃ g : Hom A X, g.comp p = f := by
  let a (n : ℕ) := LiftStage.tower (f := f) hp n
  let g : Hom A X :=
    { app := fun n => (a n).app n le_rfl
      source_app := fun n x => by
        exact (LiftStage.succ_old (a n) hp n le_rfl _).symm.trans
          ((a (n+1)).source_app n le_rfl x)
      target_app := fun n x => by
        exact (LiftStage.succ_old (a n) hp n le_rfl _).symm.trans
          ((a (n+1)).target_app n le_rfl x) }
  exact ⟨g, by ext n x; exact (a n).fac n le_rfl x⟩

end Grothendieck.GlobularSet

namespace Grothendieck.GlobularTheory.Model
open CategoryTheory CategoryTheory.Limits Opposite

theorem isCellular_cutoff_cofibrant {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {X : C.Model} (hX : X.IsCellular) :
    Cofibrant hC q ((cutoffFunctor hC q).obj X) := by
  intro P Q p hp f
  have hp' : GlobularSet.LiftsBoundaries (underlyingMap p.hom) := by
    intro n
    exact (hasLiftingProperty_I_iff n p.hom).1
      ((boundaryClass_rlp_iff hC q 0 p).1 hp n (Nat.zero_le n))
  obtain ⟨A⟩ := hX
  let := A.linearOrder
  let := A.orderBot
  let := A.succOrder
  let := A.wellFoundedLT
  have : A.chain.F.IsWellOrderContinuous := A.chain.isWellOrderContinuous
  have : HasLiftingProperty (A.chain.incl.app ⊥) p.hom :=
    HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot
      (hc := A.chain.isColimit)
      (fun j hj => (A.attachment j hj).hasLiftingProperty p.hom hp')
  let a : X ⟶ Q.obj := (cutoffAdjunction hC q).homEquiv X Q f
  let b : A.chain.F.obj ⊥ ⟶ P.obj := A.chain.isoBot.hom ≫ A.isInitial.to P.obj
  have sq : CommSq b (A.chain.incl.app ⊥) p.hom a := by
    constructor
    dsimp [b]
    rw [Category.assoc]
    rw [A.isInitial.hom_ext (A.isInitial.to P.obj ≫ p.hom) (A.start ≫ a)]
    rw [← Category.assoc]
    have w : A.chain.isoBot.hom ≫ A.start = A.chain.incl.app ⊥ := by
      exact (congrArg (A.chain.isoBot.hom ≫ ·) A.chain.fac.symm).trans
        (by simp only [Iso.hom_inv_id_assoc])
    rw [w]
  refine ⟨((cutoffAdjunction hC q).homEquiv X P).symm sq.lift, ?_⟩
  apply ((cutoffAdjunction hC q).homEquiv X Q).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact sq.fac_right

end Grothendieck.GlobularTheory.Model

namespace Grothendieck.GlobularPresheaf
open CategoryTheory Opposite

theorem liftsBoundaries_lift {A X Y : GlobularPresheaf.{v}} {p : X ⟶ Y}
    (hp : GlobularSet.LiftsBoundaries (underlyingMap p)) (f : A ⟶ Y) :
    ∃ g : A ⟶ X, g ≫ p = f := by
  obtain ⟨g, hg⟩ := hp.lift (underlyingMap f)
  let l : A ⟶ X := A.underlyingPresheafIso.inv ≫ g.presheafMap ≫ X.underlyingPresheafIso.hom
  refine ⟨l, ?_⟩
  apply underlyingMap_injective
  exact hg

end Grothendieck.GlobularPresheaf

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck.GlobularTheory.Model
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable def cutoffFreeGlobular {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) : GlobularPresheaf.{v} ⥤ CutoffModels C q :=
  freeGlobular C ⋙ cutoffFunctor hC q

noncomputable def cutoffForgetGlobular (C : GlobularTheory.{v}) (q : ℕ) :
    CutoffModels C q ⥤ GlobularPresheaf.{v} :=
  (ObjectProperty.ι (fun X : C.Model => X.IsCoskeletal q)) ⋙ forgetGlobular C

noncomputable def cutoffGlobularAdjunction {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) : cutoffFreeGlobular hC q ⊣ cutoffForgetGlobular C q :=
  (globularAdjunction C).comp (cutoffAdjunction hC q)

instance cutoffFreeGlobular_preservesColimits {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) : PreservesColimitsOfSize.{v,v} (cutoffFreeGlobular hC q) :=
  (cutoffGlobularAdjunction hC q).leftAdjoint_preservesColimits

theorem cutoffFreeGlobular_cofibrant {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : GlobularPresheaf.{v}) :
    Cofibrant hC q ((cutoffFreeGlobular hC q).obj S) := by
  intro P Q p hp f
  have hp' : GlobularSet.LiftsBoundaries (underlyingMap p.hom) := by
    intro n
    exact (hasLiftingProperty_I_iff n p.hom).1
      ((boundaryClass_rlp_iff hC q 0 p).1 hp n (Nat.zero_le n))
  let A := cutoffGlobularAdjunction hC q
  obtain ⟨g, hg⟩ := GlobularPresheaf.liftsBoundaries_lift hp' (A.homEquiv S Q f)
  refine ⟨(A.homEquiv S P).symm g, ?_⟩
  apply (A.homEquiv S Q).injective
  rw [Adjunction.homEquiv_naturality_right]
  exact (congrArg (· ≫ (cutoffForgetGlobular C q).map p)
    ((A.homEquiv S P).apply_symm_apply g)).trans hg

noncomputable def shapeGlobularEquiv {C : GlobularTheory.{v}} (S : Shape) (X : C.Model) :
    (freeShape C S ⟶ X) ≃
      ((Shape.liftedRealization.{v}).obj S ⟶ (forgetGlobular C).obj X) :=
  yonedaEquiv.trans (Equiv.ofBijective (X.tuples.evaluation.app (op S))
    (X.tuples.evaluation_bijective S))

theorem shapeGlobularEquiv_natural {C : GlobularTheory.{v}} (S : Shape) {X Y : C.Model}
    (a : freeShape C S ⟶ X) (b : X ⟶ Y) :
    shapeGlobularEquiv S Y (a ≫ b) =
      shapeGlobularEquiv S X a ≫ (forgetGlobular C).map b := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  exact (ConcreteCategory.congr_hom (b.naturality
    (C.toTheoryData.arity.map (S.cellArrow k x.down)).op) (yonedaEquiv a)).symm

theorem cutoffFreeShape_cofibrant {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : Shape) : Cofibrant hC q ((cutoffFunctor hC q).obj (freeShape C S)) := by
  intro P Q p hp f
  have hp' : GlobularSet.LiftsBoundaries (underlyingMap p.hom) := by
    intro n
    exact (hasLiftingProperty_I_iff n p.hom).1
      ((boundaryClass_rlp_iff hC q 0 p).1 hp n (Nat.zero_le n))
  let A := cutoffAdjunction hC q
  let a := A.homEquiv (freeShape C S) Q f
  obtain ⟨g, hg⟩ := GlobularPresheaf.liftsBoundaries_lift hp' (shapeGlobularEquiv S Q.obj a)
  let l := (shapeGlobularEquiv S P.obj).symm g
  have hl : l ≫ p.hom = a := by
    apply (shapeGlobularEquiv S Q.obj).injective
    rw [shapeGlobularEquiv_natural]
    change shapeGlobularEquiv S P.obj ((shapeGlobularEquiv S P.obj).symm g) ≫ _ = _
    exact (congrArg (· ≫ (forgetGlobular C).map p.hom)
      ((shapeGlobularEquiv S P.obj).apply_symm_apply g)).trans hg
  refine ⟨(A.homEquiv (freeShape C S) P).symm l, ?_⟩
  apply (A.homEquiv (freeShape C S) Q).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact hl

open CategoryTheory CategoryTheory.Limits Opposite

structure CellGroupoid {C : GlobularTheory.{v}} (X : C.Model) (_hC : C.IsCoherator)
    (n : ℕ) where
  cell : X.underlying.Cell n

namespace CellGroupoid
variable {C : GlobularTheory.{v}} {X : C.Model} {hC : C.IsCoherator} {n : ℕ}

abbrev Edge (x y : CellGroupoid X hC n) :=
  {a : X.underlying.Cell (n+1) // X.underlying.source n a = x.cell ∧
    X.underlying.target n a = y.cell}

def edgeSetoid (x y : CellGroupoid X hC n) : Setoid (Edge x y) where
  r a b := X.underlying.Joined (n+1) a.1 b.1
  iseqv := ⟨fun a => X.joined_refl hC _ a.1,
    fun h => X.joined_symm hC h, fun h k => X.joined_trans hC h k⟩

noncomputable def edgeComp {x y z : CellGroupoid X hC n}
    (a : Edge x y) (b : Edge y z) : Edge x z :=
  ⟨X.compCell hC n a.1 b.1 (a.2.2.trans b.2.1.symm),
    (X.compCell_source hC n _ _ _).trans a.2.1,
    (X.compCell_target hC n _ _ _).trans b.2.2⟩

noncomputable instance : Category (CellGroupoid X hC n) where
  Hom x y := Quotient (edgeSetoid x y)
  id x := Quotient.mk _ ⟨X.unitCell hC n x.cell,
    X.unitCell_source hC n _, X.unitCell_target hC n _⟩
  comp a b := Quotient.map₂ edgeComp (fun {a a'} ha {b b'} hb =>
    X.joined_trans hC
      (X.compCell_congr_left hC n a.1 a'.1 b.1
        (a.2.2.trans b.2.1.symm) (a'.2.2.trans b.2.1.symm) ha)
      (X.compCell_congr_right hC n a'.1 b.1 b'.1
        (a'.2.2.trans b.2.1.symm) (a'.2.2.trans b'.2.1.symm) hb)) a b
  id_comp a := by
    induction a using Quotient.inductionOn with | h a =>
    apply Quotient.sound
    change X.underlying.Joined (n+1) (X.compCell hC n _ a.1 _) a.1
    simpa only [a.2.1] using X.compCell_left_unit hC n a.1
  comp_id a := by
    induction a using Quotient.inductionOn with | h a =>
    apply Quotient.sound
    change X.underlying.Joined (n+1) (X.compCell hC n a.1 _ _) a.1
    simpa only [a.2.2] using X.compCell_right_unit hC n a.1
  assoc a b c := by
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    induction c using Quotient.inductionOn with | h c =>
    exact Quotient.sound (X.compCell_assoc hC n a.1 b.1 c.1 _ _)

noncomputable def ofEdge {x y : CellGroupoid X hC n} (a : Edge x y) : x ⟶ y :=
  Quotient.mk _ a

theorem ofEdge_eq_iff {x y : CellGroupoid X hC n} (a b : Edge x y) :
    ofEdge a = ofEdge b ↔ X.underlying.Joined (n+1) a.1 b.1 :=
  Quotient.eq

noncomputable instance : Groupoid (CellGroupoid X hC n) := Groupoid.ofIsIso (by
  intro x y a
  induction a using Quotient.inductionOn with | h a =>
  refine ⟨ofEdge ⟨X.inverseCell hC n a.1,
    (X.inverseCell_source hC n _).trans a.2.2,
    (X.inverseCell_target hC n _).trans a.2.1⟩, ?_, ?_⟩
  · apply Quotient.sound
    change X.underlying.Joined (n+1) (X.compCell hC n a.1 (X.inverseCell hC n a.1) _) _
    simpa only [a.2.1] using X.compCell_inverse_right hC n a.1
  · apply Quotient.sound
    change X.underlying.Joined (n+1) (X.compCell hC n (X.inverseCell hC n a.1) a.1 _) _
    simpa only [a.2.2] using X.compCell_inverse_left hC n a.1)

noncomputable def map {Y : C.Model} (f : X ⟶ Y) :
    CellGroupoid X hC n ⥤ CellGroupoid Y hC n where
  obj x := ⟨(underlyingMap f).app n x.cell⟩
  map a := Quotient.map (fun a =>
    ⟨(underlyingMap f).app (n+1) a.1,
      ((underlyingMap f).source_app n a.1).symm.trans (congrArg _ a.2.1),
      ((underlyingMap f).target_app n a.1).symm.trans (congrArg _ a.2.2)⟩)
    (fun _ _ h => (underlyingMap f).map_joined h) a
  map_id x := by
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    exact map_unitCell f hC n x.cell
  map_comp a b := by
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    exact map_compCell f hC n a.1 b.1 _

end CellGroupoid
end Grothendieck.GlobularTheory.Model

namespace Grothendieck.GlobularSet

namespace LiftStage
variable {A X Y : GlobularSet.{v}} {p : Hom X Y} {f : Hom A Y}

noncomputable def extendTop {n : ℕ} (a : LiftStage p f n)
    (z : A.Cell (n+1) → X.Cell (n+1))
    (hs : ∀ x, X.source n (z x) = a.app n le_rfl (A.source n x))
    (ht : ∀ x, X.target n (z x) = a.app n le_rfl (A.target n x))
    (hzp : ∀ x, p.app (n+1) (z x) = f.app (n+1) x) : LiftStage p f (n+1) where
  app k hk x := if h : k ≤ n then a.app k h x else by
    have e : k = n+1 := by omega
    subst k
    exact z x
  source_app k hk x := by
    dsimp only
    split_ifs with h h'
    · exact a.source_app k h' x
    · have e : k = n := by omega
      subst k
      exact (hs x).symm
    · omega
    · omega
  target_app k hk x := by
    dsimp only
    split_ifs with h h'
    · exact a.target_app k h' x
    · have e : k = n := by omega
      subst k
      exact (ht x).symm
    · omega
    · omega
  fac k hk x := by
    dsimp only
    split_ifs with h
    · exact a.fac k h x
    · have e : k = n+1 := by omega
      subst k
      exact hzp x

noncomputable def ofBounded {n : ℕ} (a : LiftStage p f n)
    (hA : ∀ k, n < k → IsEmpty (A.Cell k)) : Hom A X where
  app k x := if hk : k ≤ n then a.app k hk x else (hA k (by omega)).false x |>.elim
  source_app k x := by
    have hk : k+1 ≤ n := by
      by_contra h
      exact (hA (k+1) (by omega)).false x
    simp only [dite_eq_left hk, dite_eq_left (show k ≤ n by omega)]
    exact a.source_app k hk x
  target_app k x := by
    have hk : k+1 ≤ n := by
      by_contra h
      exact (hA (k+1) (by omega)).false x
    simp only [dite_eq_left hk, dite_eq_left (show k ≤ n by omega)]
    exact a.target_app k hk x

theorem ofBounded_fac {n : ℕ} (a : LiftStage p f n)
    (hA : ∀ k, n < k → IsEmpty (A.Cell k)) : (a.ofBounded hA).comp p = f := by
  ext k x
  have hk : k ≤ n := by
    by_contra h
    exact (hA k (by omega)).false x
  simpa only [Hom.comp, ofBounded, dite_eq_left hk] using a.fac k hk x

end LiftStage

theorem lift_of_top_joined {A X Y : GlobularSet.{v}} {p : Hom X Y}
    (n : ℕ) (hp : LiftsSource p (n+1)) (f : Hom A Y) (a : Hom A X)
    (hA : ∀ k, n+1 < k → IsEmpty (A.Cell k))
    (ha : ∀ k, k ≤ n → ∀ x, p.app k (a.app k x) = f.app k x)
    (htop : ∀ x, Y.Joined (n+1) (p.app (n+1) (a.app (n+1) x)) (f.app (n+1) x)) :
    ∃ g : Hom A X, g.comp p = f := by
  let lo : LiftStage p f n :=
    { app := fun k _ => a.app k
      source_app := fun k _ => a.source_app k
      target_app := fun k _ => a.target_app k
      fac := ha }
  have h x : ∃ z : X.Cell (n+1),
      X.source n z = a.app n (A.source n x) ∧
      X.target n z = a.app n (A.target n x) ∧ p.app (n+1) z = f.app (n+1) x := by
    obtain ⟨c, hc₀, hc₁⟩ := htop x
    obtain ⟨d, hd₀, hd⟩ := hp (a.app (n+1) x) c hc₀
    refine ⟨X.target (n+1) d, ?_, ?_, ?_⟩
    · rw [← X.source_source, hd₀, ← a.source_app]
    · rw [← X.target_source, hd₀, ← a.target_app]
    · rw [p.target_app, hd, hc₁]
  choose z hs ht hz using h
  let b := lo.extendTop z hs ht hz
  exact ⟨b.ofBounded hA, b.ofBounded_fac hA⟩

end Grothendieck.GlobularSet

namespace Grothendieck.GlobularTheory.Model
open CategoryTheory CategoryTheory.Limits Opposite

theorem free_hasFillers_of_top_homotopy {C : GlobularTheory.{v}}
    (hC : C.IsCoherator) (q n : ℕ) (H : ExpansionContraction hC q (n+1))
    (S : GlobularPresheaf.{v})
    (hS : ∀ k, n+1 < k → IsEmpty (S.underlying.Cell k))
    (L : CutoffModels C q) (hL : Cofibrant hC q L)
    (hLF : L.obj.underlying.HasFillers)
    (f : (cutoffFreeGlobular hC q).obj S ⟶ L)
    (g : L ⟶ (cutoffFreeGlobular hC q).obj S)
    (hlo : ∀ k, k ≤ n → ∀ x,
      (underlyingMap (f ≫ g).hom).app k
        (GlobularPresheaf.underlyingMap ((cutoffGlobularAdjunction hC q).unit.app S) |>.app k x) =
      (GlobularPresheaf.underlyingMap ((cutoffGlobularAdjunction hC q).unit.app S)).app k x)
    (htop : ∀ x, ((cutoffFreeGlobular hC q).obj S).obj.underlying.Joined (n+1)
      ((underlyingMap (f ≫ g).hom).app (n+1)
        ((GlobularPresheaf.underlyingMap ((cutoffGlobularAdjunction hC q).unit.app S)).app (n+1) x))
      ((GlobularPresheaf.underlyingMap ((cutoffGlobularAdjunction hC q).unit.app S)).app (n+1) x)) :
    ((cutoffFreeGlobular hC q).obj S).obj.underlying.HasFillers := by
  let := sourceClass_smallObject hC q (n+1)
  let W := sourceClass hC q (n+1)
  let F := MorphismProperty.factorizationData W.rlp.llp W.rlp g
  have hQ := H F.i F.hi hL hLF
  let A := cutoffGlobularAdjunction hC q
  let U := cutoffForgetGlobular C q
  let eta := A.unit.app S
  let a := eta ≫ U.map f ≫ U.map F.i
  have hp : GlobularSet.LiftsSource (underlyingMap F.p.hom) (n+1) :=
    (hasLiftingProperty_J_iff (n+1) F.p.hom).1
      ((sourceClass_rlp_iff hC q (n+1) F.p).1 F.hp (n+1) le_rfl)
  have hap : a ≫ U.map F.p = eta ≫ U.map (f ≫ g) := by
    simp only [a, Category.assoc, ← Functor.map_comp, F.fac]
  have hap' := congrArg GlobularPresheaf.underlyingMap hap
  obtain ⟨b, hb⟩ := GlobularSet.lift_of_top_joined n hp
    (GlobularPresheaf.underlyingMap eta) (GlobularPresheaf.underlyingMap a) hS
    (by
      intro k hk x
      have e := congrFun (congrArg (fun z => z.app k) hap') x
      exact e.trans (hlo k hk x))
    (by
      intro x
      have e := congrFun (congrArg (fun z => z.app (n+1)) hap') x
      exact e ▸ htop x)
  let b' : S ⟶ U.obj F.Z := S.underlyingPresheafIso.inv ≫
    b.presheafMap ≫ (U.obj F.Z).underlyingPresheafIso.hom
  have hb' : b' ≫ U.map F.p = eta := by
    apply GlobularPresheaf.underlyingMap_injective
    exact hb
  let s := (A.homEquiv S F.Z).symm b'
  have hs : s ≫ F.p = 𝟙 _ := by
    apply (A.homEquiv S _).injective
    rw [Adjunction.homEquiv_naturality_right]
    change A.homEquiv S F.Z ((A.homEquiv S F.Z).symm b') ≫ U.map F.p = _
    rw [Equiv.apply_symm_apply, hb']
    exact (A.homEquiv_id S).symm
  apply hQ.retract (underlyingMap s.hom) (underlyingMap F.p.hom)
  exact congrArg (fun z => underlyingMap z.hom) hs

end Grothendieck.GlobularTheory.Model

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck.GlobularSet

def LiftsBoundary {X Y : GlobularSet.{v}} (p : Hom X Y) (k : ℕ) : Prop :=
  ∀ (bd : X.Boundary k) (y : Y.Cell k), Y.boundary k y = p.boundaryMap k bd →
    ∃ x : X.Cell k, X.boundary k x = bd ∧ p.app k x = y

structure RelativeLiftStage {A B X Y : GlobularSet.{v}}
    (i : Hom A B) (a : Hom A X) (p : Hom X Y) (b : Hom B Y) (n : ℕ)
    extends LiftStage p b n where
  on_domain : ∀ k (hk : k ≤ n) x, app k hk (i.app k x) = a.app k x

namespace RelativeLiftStage
variable {A B X Y : GlobularSet.{v}} {i : Hom A B} {a : Hom A X}
  {p : Hom X Y} {b : Hom B Y}

theorem exists_cell (r k : ℕ)
    (hi : Function.Injective (i.app k))
    (hlo : k < r → Function.Surjective (i.app k))
    (hp : r ≤ k → LiftsBoundary p k)
    (sq : a.comp p = i.comp b)
    (bd : B.Cell k → X.Boundary k)
    (hbd : ∀ x, X.boundary k (a.app k x) = bd (i.app k x))
    (hbp : ∀ y, Y.boundary k (b.app k y) = p.boundaryMap k (bd y)) :
    ∃ z : B.Cell k → X.Cell k,
      (∀ y, X.boundary k (z y) = bd y) ∧
      (∀ y, p.app k (z y) = b.app k y) ∧
      (∀ x, z (i.app k x) = a.app k x) := by
  classical
  have e x : p.app k (a.app k x) = b.app k (i.app k x) :=
    congrFun (congrArg (fun t => t.app k) sq) x
  have hz y : ∃ z : X.Cell k, X.boundary k z = bd y ∧ p.app k z = b.app k y ∧
      ∀ x, i.app k x = y → z = a.app k x := by
    by_cases hy : ∃ x, i.app k x = y
    · obtain ⟨x, rfl⟩ := hy
      exact ⟨a.app k x, hbd x, e x, fun x' hx' => congrArg (a.app k) (hi hx').symm⟩
    · have hk : r ≤ k := by
        by_contra hk
        exact hy (hlo (by omega) y)
      obtain ⟨z, hz, hzp⟩ := hp hk (bd y) (b.app k y) (hbp y)
      exact ⟨z, hz, hzp, fun x hx => (hy ⟨x,hx⟩).elim⟩
  choose z hb hf ho using hz
  exact ⟨z, hb, hf, fun x => ho _ x rfl⟩

noncomputable def zero (r : ℕ)
    (hi : ∀ k, Function.Injective (i.app k))
    (hlo : ∀ k, k < r → Function.Surjective (i.app k))
    (hp : ∀ k, r ≤ k → LiftsBoundary p k) (sq : a.comp p = i.comp b) :
    RelativeLiftStage i a p b 0 := by
  choose z _hb hf ho using exists_cell r 0 (hi 0) (hlo 0) (hp 0) sq
    (fun _ => PUnit.unit) (fun _ => rfl) (fun _ => rfl)
  exact
    { app := fun k hk x => by
        have e : k = 0 := by omega
        subst k
        exact z x
      source_app := fun k hk => by omega
      target_app := fun k hk => by omega
      fac := fun k hk x => by
        have e : k = 0 := by omega
        subst k
        exact hf x
      on_domain := fun k hk x => by
        have e : k = 0 := by omega
        subst k
        exact ho x }

noncomputable def succ (r : ℕ)
    (hi : ∀ k, Function.Injective (i.app k))
    (hlo : ∀ k, k < r → Function.Surjective (i.app k))
    (hp : ∀ k, r ≤ k → LiftsBoundary p k) (sq : a.comp p = i.comp b)
    {n : ℕ} (s : RelativeLiftStage i a p b n) : RelativeLiftStage i a p b (n+1) := by
  let bd := s.toLiftStage.nextBoundary
  have hbd x : X.boundary (n+1) (a.app (n+1) x) = bd (i.app (n+1) x) := by
    apply Subtype.ext
    apply Prod.ext
    · change X.source n (a.app (n+1) x) = s.app n le_rfl (B.source n (i.app (n+1) x))
      rw [← a.source_app, ← i.source_app, s.on_domain]
    · change X.target n (a.app (n+1) x) = s.app n le_rfl (B.target n (i.app (n+1) x))
      rw [← a.target_app, ← i.target_app, s.on_domain]
  have hbp y : Y.boundary (n+1) (b.app (n+1) y) = p.boundaryMap (n+1) (bd y) := by
    apply Subtype.ext
    apply Prod.ext
    · exact (b.source_app n y).symm.trans (s.fac n le_rfl _).symm
    · exact (b.target_app n y).symm.trans (s.fac n le_rfl _).symm
  choose z hb hf ho using exists_cell r (n+1) (hi _) (hlo _) (hp _) sq bd hbd hbp
  let t := s.toLiftStage.extendTop z
    (fun y => congrArg (fun c => c.1.1) (hb y))
    (fun y => congrArg (fun c => c.1.2) (hb y)) hf
  refine { toLiftStage := t, on_domain := ?_ }
  intro k hk x
  dsimp only [t, LiftStage.extendTop]
  split_ifs with h
  · exact s.on_domain k h x
  · have e : k = n+1 := by omega
    subst k
    exact ho x

theorem succ_old (r : ℕ)
    (hi : ∀ k, Function.Injective (i.app k))
    (hlo : ∀ k, k < r → Function.Surjective (i.app k))
    (hp : ∀ k, r ≤ k → LiftsBoundary p k) (sq : a.comp p = i.comp b)
    {n : ℕ} (s : RelativeLiftStage i a p b n) (k : ℕ) (hk : k ≤ n) (x : B.Cell k) :
    (s.succ r hi hlo hp sq).app k (by omega) x = s.app k hk x := by
  dsimp only [succ, LiftStage.extendTop]
  simp only [dite_eq_left hk]

end RelativeLiftStage

theorem relative_lift {A B X Y : GlobularSet.{v}} (i : Hom A B) (a : Hom A X)
    (p : Hom X Y) (b : Hom B Y) (r : ℕ)
    (hi : ∀ k, Function.Injective (i.app k))
    (hlo : ∀ k, k < r → Function.Surjective (i.app k))
    (hp : ∀ k, r ≤ k → LiftsBoundary p k) (sq : a.comp p = i.comp b) :
    ∃ l : Hom B X, i.comp l = a ∧ l.comp p = b := by
  let s : (n : ℕ) → RelativeLiftStage i a p b n :=
    Nat.rec (RelativeLiftStage.zero r hi hlo hp sq) (fun _ s => s.succ r hi hlo hp sq)
  let l : Hom B X :=
    { app := fun n => (s n).app n le_rfl
      source_app := fun n x =>
        ((s n).succ_old r hi hlo hp sq n le_rfl _).symm.trans
          ((s (n+1)).source_app n le_rfl x)
      target_app := fun n x =>
        ((s n).succ_old r hi hlo hp sq n le_rfl _).symm.trans
          ((s (n+1)).target_app n le_rfl x) }
  refine ⟨l, ?_, ?_⟩
  · ext n x
    exact (s n).on_domain n le_rfl x
  · ext n x
    exact (s n).fac n le_rfl x

end Grothendieck.GlobularSet

namespace Grothendieck.GlobularPresheaf
open CategoryTheory Opposite

theorem relative_lift {A B X Y : GlobularPresheaf.{v}}
    (i : A ⟶ B) (a : A ⟶ X) (p : X ⟶ Y) (b : B ⟶ Y) (r : ℕ)
    (hi : ∀ k, Function.Injective ((underlyingMap i).app k))
    (hlo : ∀ k, k < r → Function.Surjective ((underlyingMap i).app k))
    (hp : ∀ k, r ≤ k → GlobularSet.LiftsBoundary (underlyingMap p) k)
    (sq : a ≫ p = i ≫ b) : ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b := by
  obtain ⟨g, hg₀, hg₁⟩ := GlobularSet.relative_lift (underlyingMap i)
    (underlyingMap a) (underlyingMap p) (underlyingMap b) r hi hlo hp
      (congrArg underlyingMap sq)
  let l : B ⟶ X := B.underlyingPresheafIso.inv ≫ g.presheafMap ≫ X.underlyingPresheafIso.hom
  exact ⟨l, underlyingMap_injective hg₀, underlyingMap_injective hg₁⟩

end Grothendieck.GlobularPresheaf

namespace Grothendieck.GlobularTheory.Model
open CategoryTheory CategoryTheory.Limits Opposite

theorem cutoffFreeGlobular_map_cofibration {C : GlobularTheory.{v}}
    (hC : C.IsCoherator) (q r : ℕ) {S T : GlobularPresheaf.{v}} (i : S ⟶ T)
    (hi : ∀ k, Function.Injective ((GlobularPresheaf.underlyingMap i).app k))
    (hlo : ∀ k, k < r → Function.Surjective ((GlobularPresheaf.underlyingMap i).app k)) :
    (boundaryClass hC q r).rlp.llp ((cutoffFreeGlobular hC q).map i) := by
  intro P Q p hp
  constructor
  intro a b sq
  let A := cutoffGlobularAdjunction hC q
  let U := cutoffForgetGlobular C q
  let a' := A.homEquiv S P a
  let b' := A.homEquiv T Q b
  have hs : a' ≫ U.map p = i ≫ b' := by
    rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left]
    exact congrArg (A.homEquiv S Q) sq.w
  have hp' : ∀ k, r ≤ k → GlobularSet.LiftsBoundary
      (GlobularPresheaf.underlyingMap (U.map p)) k := by
    intro k hk
    exact (hasLiftingProperty_I_iff k p.hom).1
      ((boundaryClass_rlp_iff hC q r p).1 hp k hk)
  obtain ⟨l, hl₀, hl₁⟩ := GlobularPresheaf.relative_lift i a' (U.map p) b' r hi hlo hp' hs
  refine CommSq.HasLift.mk' ⟨(A.homEquiv T P).symm l, ?_, ?_⟩
  · apply (A.homEquiv S P).injective
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
    exact hl₀
  · apply (A.homEquiv T Q).injective
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    exact hl₁

theorem cutoff_hasLimits {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) : HasLimitsOfSize.{v,v} (CutoffModels C q) := by
  let := cutoffReflective hC q
  exact hasLimits_of_reflective (ObjectProperty.ι (fun X : C.Model => X.IsCoskeletal q))

theorem cutoff_hasFillers_iff {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (X : CutoffModels C q) :
    X.obj.underlying.HasFillers ↔ ∀ n (f : cutoffBoundary hC q n ⟶ X),
      ∃ g : cutoffDisk hC q n ⟶ X, cutoffI hC q n ≫ g = f := by
  rw [hasFillers_iff]
  let A := cutoffAdjunction hC q
  constructor
  · intro h n f
    obtain ⟨g, hg⟩ := h n (A.homEquiv _ X f)
    refine ⟨(A.homEquiv _ X).symm g, (A.homEquiv _ X).injective ?_⟩
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
    exact hg
  · intro h n f
    obtain ⟨g, hg⟩ := h n ((A.homEquiv _ X).symm f)
    refine ⟨A.homEquiv _ X g, ?_⟩
    have e := congrArg (A.homEquiv _ X) hg
    simpa only [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply] using e

end Grothendieck.GlobularTheory.Model

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits

theorem lifting_terminal_iff {K : Type u} [Category.{v} K] [HasTerminal K]
    {A B : K} (j : A ⟶ B) (X : K) :
    HasLiftingProperty j (terminal.from X) ↔ ∀ a : A ⟶ X, ∃ b : B ⟶ X, j ≫ b = a := by
  constructor
  · intro h a
    let := h
    have sq : CommSq a j (terminal.from X) (terminal.from B) := ⟨terminal.hom_ext _ _⟩
    exact ⟨sq.lift, sq.fac_left⟩
  · intro h
    constructor
    intro a b _sq
    obtain ⟨l, hl⟩ := h a
    exact CommSq.HasLift.mk' ⟨l, hl, terminal.hom_ext _ _⟩

namespace GlobularTheory.Model

structure CutoffPathData {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) (Y : CutoffModels C q) where
  P : CutoffModels C q
  p₀ : P ⟶ Y
  p₁ : P ⟶ Y
  lifts₀ : (boundaryClass hC q 0).rlp p₀
  lifts₁ : (boundaryClass hC q 0).rlp p₁
  joint : ∀ k, r ≤ k → ∀ (t : cutoffDisk hC q k ⟶ P)
    (u₀ u₁ : cutoffDisk hC q (k+1) ⟶ Y),
    t ≫ p₀ = cutoffJ hC q k ≫ u₀ → t ≫ p₁ = cutoffJ hC q k ≫ u₁ →
    ∃ l : cutoffDisk hC q (k+1) ⟶ P,
      cutoffJ hC q k ≫ l = t ∧ l ≫ p₀ = u₀ ∧ l ≫ p₁ = u₁

theorem CutoffPathData.joint_rlp {C : GlobularTheory.{v}} {hC : C.IsCoherator}
    {q r : ℕ} {Y : CutoffModels C q} (D : CutoffPathData hC q r Y)
    [HasBinaryProduct Y Y] : (sourceClass hC q r).rlp (prod.lift D.p₀ D.p₁) := by
  rintro _ _ j ⟨⟨k,hk⟩⟩
  constructor
  intro a b sq
  have hf : a ≫ D.p₀ = cutoffJ hC q k ≫ (b ≫ prod.fst) := by
    have e := congrArg (· ≫ prod.fst) sq.w
    simpa only [Category.assoc, prod.lift_fst] using e
  have hg : a ≫ D.p₁ = cutoffJ hC q k ≫ (b ≫ prod.snd) := by
    have e := congrArg (· ≫ prod.snd) sq.w
    simpa only [Category.assoc, prod.lift_snd] using e
  obtain ⟨l, hl, hl₀, hl₁⟩ := D.joint k hk a (b ≫ prod.fst) (b ≫ prod.snd) hf hg
  refine CommSq.HasLift.mk' ⟨l, hl, ?_⟩
  apply prod.hom_ext
  · simpa only [Category.assoc, prod.lift_fst] using hl₀
  · simpa only [Category.assoc, prod.lift_snd] using hl₁

theorem expansionContraction_of_paths {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) (D : ∀ Y, Nonempty (CutoffPathData hC q r Y)) :
    ExpansionContraction hC q r := by
  let := cutoff_hasLimits hC q
  intro X Y i hi hX hXF
  have hiI : (boundaryClass hC q 0).rlp.llp i :=
    boundaryClass_cofibration_le hC q 0 r (Nat.zero_le r) i
      (sourceClass_cofibration_le hC q r i hi)
  have ht : (boundaryClass hC q 0).rlp (terminal.from X) := by
    rintro A B j ⟨⟨k,_⟩⟩
    rw [lifting_terminal_iff]
    exact (cutoff_hasFillers_iff hC q _).1 hXF k
  let := hiI (terminal.from X) ht
  have retractSq : CommSq (𝟙 X) i (terminal.from X) (terminal.from Y) :=
    ⟨terminal.hom_ext _ _⟩
  let z : Y ⟶ X := retractSq.lift
  have hz : i ≫ z = 𝟙 X := retractSq.fac_left
  obtain ⟨P⟩ := D Y
  obtain ⟨a, ha⟩ := hX P.p₀ P.lifts₀ i
  let u : X ⟶ Y := a ≫ P.p₁
  let := hi (prod.lift P.p₀ P.p₁) P.joint_rlp
  have sq : CommSq a i (prod.lift P.p₀ P.p₁) (prod.lift (𝟙 Y) (z ≫ u)) := by
    constructor
    apply prod.hom_ext
    · simpa only [Category.assoc, prod.lift_fst, Category.comp_id] using ha
    · simp only [Category.assoc, prod.lift_snd]
      rw [← Category.assoc i, hz, Category.id_comp]
  have hf₀ : sq.lift ≫ P.p₀ = 𝟙 Y := by
    have e := congrArg (· ≫ prod.fst) sq.fac_right
    simpa only [Category.assoc, prod.lift_fst] using e
  have hf₁ : sq.lift ≫ P.p₁ = z ≫ u := by
    have e := congrArg (· ≫ prod.snd) sq.fac_right
    simpa only [Category.assoc, prod.lift_snd] using e
  refine GlobularSet.hasFillers_of_endpoint_factorization hXF
    (underlyingMap u.hom) (underlyingMap z.hom) (underlyingMap sq.lift.hom)
    (underlyingMap P.p₀.hom) (underlyingMap P.p₁.hom)
    (congrArg (fun t : Y ⟶ Y => underlyingMap t.hom) hf₀)
    (congrArg (fun t : Y ⟶ Y => underlyingMap t.hom) hf₁) ?_
  intro k
  exact (hasLiftingProperty_I_iff k P.p₁.hom).1
    ((boundaryClass_rlp_iff hC q 0 P.p₁).1 P.lifts₁ k (Nat.zero_le k))

end GlobularTheory.Model
end Grothendieck

namespace Grothendieck.GlobularSet

theorem ExactBoundaryTest.of_retract_factor {X Y : GlobularSet.{u}}
    (i : Hom X Y) (r : Hom Y X) (u : Hom X Y) (hir : i.comp r = Hom.id X)
    (hv : ExactBoundaryTest (r.comp u)) (units : ∀ k x, Y.Joined k x x) :
    ExactBoundaryTest i := by
  intro k bd y hy
  have hx : X.boundary k (r.app k y) = bd := by
    rw [← r.boundary_app, hy, ← Hom.boundaryMap_comp, hir, Hom.boundaryMap_id]
  refine ⟨r.app k y, hx, hv.reflects_joined ?_ ?_⟩
  · rw [parallel_iff_boundary_eq, ← i.boundary_app, hx, hy]
  · have e : r.app k (i.app k (r.app k y)) = r.app k y :=
      congrFun (congrArg (fun t => t.app k) hir) (r.app k y)
    change Y.Joined k (u.app k (r.app k (i.app k (r.app k y)))) (u.app k (r.app k y))
    rw [e]
    exact units k _

end Grothendieck.GlobularSet

namespace Grothendieck.GlobularTheory.Model
open CategoryTheory CategoryTheory.Limits

theorem weakEquivalence_of_cutoff_path {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) {X Y : CutoffModels C q} (i : X ⟶ Y)
    (hi : (sourceClass hC q r).rlp.llp i) (hX : Cofibrant hC q X)
    (z : Y ⟶ X) (hz : i ≫ z = 𝟙 X) (P : CutoffPathData hC q r Y) :
    WeakEquivalence hC i.hom := by
  let := cutoff_hasLimits hC q
  obtain ⟨a, ha⟩ := hX P.p₀ P.lifts₀ i
  let u : X ⟶ Y := a ≫ P.p₁
  let := hi (prod.lift P.p₀ P.p₁) P.joint_rlp
  have sq : CommSq a i (prod.lift P.p₀ P.p₁) (prod.lift (𝟙 Y) (z ≫ u)) := by
    constructor
    apply prod.hom_ext
    · simpa only [Category.assoc, prod.lift_fst, Category.comp_id] using ha
    · simp only [Category.assoc, prod.lift_snd]
      rw [← Category.assoc i, hz, Category.id_comp]
  have hf₀ : sq.lift ≫ P.p₀ = 𝟙 Y := by
    have e := congrArg (· ≫ prod.fst) sq.fac_right
    simpa only [Category.assoc, prod.lift_fst] using e
  have hf₁ : sq.lift ≫ P.p₁ = z ≫ u := by
    have e := congrArg (· ≫ prod.snd) sq.fac_right
    simpa only [Category.assoc, prod.lift_snd] using e
  have hp₀ : GlobularSet.LiftsBoundaries (underlyingMap P.p₀.hom) := by
    intro k
    exact (hasLiftingProperty_I_iff k P.p₀.hom).1
      ((boundaryClass_rlp_iff hC q 0 P.p₀).1 P.lifts₀ k (Nat.zero_le k))
  have hp₁ : GlobularSet.LiftsBoundaries (underlyingMap P.p₁.hom) := by
    intro k
    exact (hasLiftingProperty_I_iff k P.p₁.hom).1
      ((boundaryClass_rlp_iff hC q 0 P.p₁).1 P.lifts₁ k (Nat.zero_le k))
  apply weakEquivalence_of_exactBoundaryTest hC
  apply GlobularSet.ExactBoundaryTest.of_retract_factor
    (underlyingMap i.hom) (underlyingMap z.hom) (underlyingMap u.hom)
    (congrArg (fun t : X ⟶ X => underlyingMap t.hom) hz) _ (Y.obj.joined_refl hC)
  have hv := GlobularSet.exactBoundaryTest_endpoint_section
    (underlyingMap P.p₀.hom) (underlyingMap P.p₁.hom) (underlyingMap sq.lift.hom)
    hp₀ hp₁
    (fun k x => congrFun (congrArg (fun t => (underlyingMap t.hom).app k) hf₀) x)
    (Y.obj.joined_refl hC)
  have e := congrArg (fun t : Y ⟶ Y => underlyingMap t.hom) hf₁
  change GlobularSet.ExactBoundaryTest (underlyingMap (sq.lift ≫ P.p₁).hom) at hv
  rw [e] at hv
  exact hv

end Grothendieck.GlobularTheory.Model

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck.GlobularTheory
open CategoryTheory CategoryTheory.Limits Opposite

structure RepresentedHom {C : GlobularTheory.{v}} {K : Type u} [Category.{v} K]
    (F : C.Obj ⥤ K) (R : Shape ⥤ K)
    (e₀ e₁ : C.toTheoryData.arity ⋙ F ⟶ R) (S T : Shape) where
  original : C.Hom S T
  cylinder : R.obj S ⟶ R.obj T
  endpoint₀ : e₀.app S ≫ cylinder = F.map (show C.toTheoryData.arity.obj S ⟶ C.toTheoryData.arity.obj T from original) ≫ e₀.app T
  endpoint₁ : e₁.app S ≫ cylinder = F.map (show C.toTheoryData.arity.obj S ⟶ C.toTheoryData.arity.obj T from original) ≫ e₁.app T

@[ext] theorem RepresentedHom.ext {C : GlobularTheory.{v}} {K : Type u} [Category.{v} K]
    {F : C.Obj ⥤ K} {R : Shape ⥤ K} {e₀ e₁ : C.toTheoryData.arity ⋙ F ⟶ R}
    {S T : Shape} {a b : RepresentedHom F R e₀ e₁ S T}
    (h : a.original = b.original) (k : a.cylinder = b.cylinder) : a = b := by
  cases a
  cases b
  cases h
  cases k
  rfl

noncomputable def representedData {C : GlobularTheory.{v}} {K : Type u} [Category.{v} K]
    (F : C.Obj ⥤ K) (R : Shape ⥤ K)
    (e₀ e₁ : C.toTheoryData.arity ⋙ F ⟶ R) : TheoryData.{v} where
  Hom := RepresentedHom F R e₀ e₁
  id S := ⟨C.id S, 𝟙 _, by
    change e₀.app S ≫ 𝟙 _ = F.map (𝟙 _) ≫ e₀.app S
    simp, by
    change e₁.app S ≫ 𝟙 _ = F.map (𝟙 _) ≫ e₁.app S
    simp⟩
  comp a b :=
    { original := C.comp a.original b.original
      cylinder := a.cylinder ≫ b.cylinder
      endpoint₀ := by
        rw [← Category.assoc, a.endpoint₀, Category.assoc, b.endpoint₀, ← Category.assoc]
        exact congrArg (· ≫ e₀.app _) (F.map_comp a.original b.original).symm
      endpoint₁ := by
        rw [← Category.assoc, a.endpoint₁, Category.assoc, b.endpoint₁, ← Category.assoc]
        exact congrArg (· ≫ e₁.app _) (F.map_comp a.original b.original).symm }
  id_comp a := RepresentedHom.ext (C.id_comp _) (Category.id_comp _)
  comp_id a := RepresentedHom.ext (C.comp_id _) (Category.comp_id _)
  assoc a b c := RepresentedHom.ext (C.assoc _ _ _) (Category.assoc _ _ _)
  base f := ⟨C.base f, R.map f, (e₀.naturality f).symm, (e₁.naturality f).symm⟩
  base_id S := RepresentedHom.ext (C.base_id S) (R.map_id S)
  base_comp a b := RepresentedHom.ext (C.base_comp a b) (R.map_comp a b)

noncomputable def representedTheory {C : GlobularTheory.{v}} {K : Type u} [Category.{v} K]
    (F : C.Obj ⥤ K) (R : Shape ⥤ K)
    (e₀ e₁ : C.toTheoryData.arity ⋙ F ⟶ R)
    (hR : ∀ (S : Shape) b h hl hr, IsPushout
      (R.map (S.seam hl)) (R.map (Shape.face hr false))
      (R.map (S.inl b h hl hr)) (R.map (S.inr b h hl hr)))
    (hF : ∀ (S : Shape) b h hl hr, IsPushout
      (F.map (C.base (S.seam hl))) (F.map (C.base (Shape.face hr false)))
      (F.map (C.base (S.inl b h hl hr))) (F.map (C.base (S.inr b h hl hr)))) :
    GlobularTheory.{v} where
  toTheoryData := representedData F R e₀ e₁
  sums S b h hl hr := by
    apply IsPushout.mk'
    · exact RepresentedHom.ext (C.sums S b h hl hr).w (hR S b h hl hr).w
    · intro T a a' ha hb
      apply RepresentedHom.ext
      · exact (C.sums S b h hl hr).hom_ext (W := C.toTheoryData.arity.obj T.shape)
          (congrArg RepresentedHom.original ha) (congrArg RepresentedHom.original hb)
      · exact (hR S b h hl hr).hom_ext
          (congrArg RepresentedHom.cylinder ha) (congrArg RepresentedHom.cylinder hb)
    · intro T a b' hab
      change RepresentedHom F R e₀ e₁ S T.shape at a
      change RepresentedHom F R e₀ e₁ (Shape.globe h) T.shape at b'
      let d : C.Hom (S.attach b h hl hr) T.shape :=
        (C.sums S b h hl hr).desc (W := C.toTheoryData.arity.obj T.shape) a.original b'.original
          (congrArg RepresentedHom.original hab)
      let l : R.obj (S.attach b h hl hr) ⟶ R.obj T.shape :=
        (hR S b h hl hr).desc a.cylinder b'.cylinder
          (congrArg RepresentedHom.cylinder hab)
      have hd₀ : C.comp (C.base (S.inl b h hl hr)) d = a.original :=
        (C.sums S b h hl hr).inl_desc _ _ _
      have hd₁ : C.comp (C.base (S.inr b h hl hr)) d = b'.original :=
        (C.sums S b h hl hr).inr_desc _ _ _
      have hl₀ : R.map (S.inl b h hl hr) ≫ l = a.cylinder :=
        (hR S b h hl hr).inl_desc _ _ _
      have hl₁ : R.map (S.inr b h hl hr) ≫ l = b'.cylinder :=
        (hR S b h hl hr).inr_desc _ _ _
      have he (e : C.toTheoryData.arity ⋙ F ⟶ R)
          (ha : e.app S ≫ a.cylinder = F.map a.original ≫ e.app T.shape)
          (hb : e.app (Shape.globe h) ≫ b'.cylinder = F.map b'.original ≫ e.app T.shape) :
          e.app (S.attach b h hl hr) ≫ l = F.map d ≫ e.app T.shape := by
        apply (hF S b h hl hr).hom_ext
        · change (C.toTheoryData.arity ⋙ F).map (S.inl b h hl hr) ≫
            e.app (S.attach b h hl hr) ≫ l =
            F.map (C.base (S.inl b h hl hr)) ≫ F.map d ≫ e.app T.shape
          rw [← Category.assoc, e.naturality, Category.assoc, hl₀, ha]
          simpa only [Category.assoc, Functor.comp_obj, TheoryData.arity, Shape.globe] using congrArg (· ≫ e.app T.shape)
            ((F.map_comp (C.base (S.inl b h hl hr)) d).symm.trans
              (congrArg F.map hd₀)).symm
        · change (C.toTheoryData.arity ⋙ F).map (S.inr b h hl hr) ≫
            e.app (S.attach b h hl hr) ≫ l =
            F.map (C.base (S.inr b h hl hr)) ≫ F.map d ≫ e.app T.shape
          rw [← Category.assoc, e.naturality, Category.assoc, hl₁, hb]
          simpa only [Category.assoc, Functor.comp_obj, TheoryData.arity, Shape.globe] using congrArg (· ≫ e.app T.shape)
            ((F.map_comp (C.base (S.inr b h hl hr)) d).symm.trans
              (congrArg F.map hd₁)).symm
      let w : RepresentedHom F R e₀ e₁ (S.attach b h hl hr) T.shape :=
        ⟨d, l, he e₀ a.endpoint₀ b'.endpoint₀, he e₁ a.endpoint₁ b'.endpoint₁⟩
      exact ⟨w, RepresentedHom.ext hd₀ ((hR S b h hl hr).inl_desc _ _ _),
        RepresentedHom.ext hd₁ ((hR S b h hl hr).inr_desc _ _ _)⟩

noncomputable def representedProjection {C : GlobularTheory.{v}} {K : Type u} [Category.{v} K]
    (F : C.Obj ⥤ K) (R : Shape ⥤ K)
    (e₀ e₁ : C.toTheoryData.arity ⋙ F ⟶ R) (hR hF) :
    Morphism (representedTheory F R e₀ e₁ hR hF) C where
  map f := f.original
  map_id _ := rfl
  map_comp _ _ := rfl
  map_base _ := rfl

end Grothendieck.GlobularTheory

namespace Grothendieck.GlobularSet

inductive WhiskerCell (X : GlobularSet.{u}) (n : ℕ) : ℕ → Type u
  | base (k : ℕ) : X.Cell k → WhiskerCell X n k
  | tip : X.Cell n → WhiskerCell X n n
  | edge : X.Cell n → WhiskerCell X n (n+1)

namespace WhiskerCell

def source {X : GlobularSet.{u}} (n : ℕ) (ε : Bool) (k : ℕ)
    (x : WhiskerCell X n (k+1)) : WhiskerCell X n k := by
  cases x with
  | base _ x => exact .base _ (X.source k x)
  | tip x => exact .base _ (X.source k x)
  | edge x => exact if ε then .tip x else .base _ x

def target {X : GlobularSet.{u}} (n : ℕ) (ε : Bool) (k : ℕ)
    (x : WhiskerCell X n (k+1)) : WhiskerCell X n k := by
  cases x with
  | base _ x => exact .base _ (X.target k x)
  | tip x => exact .base _ (X.target k x)
  | edge x => exact if ε then .base _ x else .tip x

@[simp] theorem source_base {X : GlobularSet.{u}} (n : ℕ) (ε : Bool)
    (k : ℕ) (x : X.Cell (k+1)) :
    source n ε k (.base _ x) = .base _ (X.source k x) := rfl

@[simp] theorem target_base {X : GlobularSet.{u}} (n : ℕ) (ε : Bool)
    (k : ℕ) (x : X.Cell (k+1)) :
    target n ε k (.base _ x) = .base _ (X.target k x) := rfl

@[simp] theorem source_tip {X : GlobularSet.{u}} (ε : Bool)
    (k : ℕ) (x : X.Cell (k+1)) :
    source (k+1) ε k (.tip x) = .base _ (X.source k x) := rfl

@[simp] theorem target_tip {X : GlobularSet.{u}} (ε : Bool)
    (k : ℕ) (x : X.Cell (k+1)) :
    target (k+1) ε k (.tip x) = .base _ (X.target k x) := rfl

@[simp] theorem source_edge {X : GlobularSet.{u}} (n : ℕ) (ε : Bool)
    (x : X.Cell n) : source n ε n (.edge x) = if ε then .tip x else .base _ x := rfl

@[simp] theorem target_edge {X : GlobularSet.{u}} (n : ℕ) (ε : Bool)
    (x : X.Cell n) : target n ε n (.edge x) = if ε then .base _ x else .tip x := rfl

end WhiskerCell

def whisker (X : GlobularSet.{u}) (n : ℕ) (ε : Bool) : GlobularSet.{u} where
  Cell := WhiskerCell X n
  source := WhiskerCell.source n ε
  target := WhiskerCell.target n ε
  source_source k x := by
    cases x with
    | base _ x => simp only [WhiskerCell.source_base, WhiskerCell.target_base,
        X.source_source]
    | tip x => simp only [WhiskerCell.source_tip, WhiskerCell.target_tip,
        WhiskerCell.source_base, X.source_source]
    | edge x => cases ε <;> rfl
  target_source k x := by
    cases x with
    | base _ x => simp only [WhiskerCell.source_base, WhiskerCell.target_base,
        X.target_source]
    | tip x => simp only [WhiskerCell.source_tip, WhiskerCell.target_tip,
        WhiskerCell.target_base, X.target_source]
    | edge x => cases ε <;> rfl

def whiskerInclusion (X : GlobularSet.{u}) (n : ℕ) (ε : Bool) : Hom X (X.whisker n ε) where
  app := WhiskerCell.base
  source_app _ _ := rfl
  target_app _ _ := rfl

def whiskerMap {X Y : GlobularSet.{u}} (f : Hom X Y) (n : ℕ) (ε : Bool) :
    Hom (X.whisker n ε) (Y.whisker n ε) where
  app _ x := match x with
    | .base k x => .base k (f.app k x)
    | .tip x => .tip (f.app n x)
    | .edge x => .edge (f.app n x)
  source_app k x := by
    cases x with
    | base _ x => exact congrArg (WhiskerCell.base k) (f.source_app k x)
    | tip x => exact congrArg (WhiskerCell.base k) (f.source_app k x)
    | edge x => cases ε <;> rfl
  target_app k x := by
    cases x with
    | base _ x => exact congrArg (WhiskerCell.base k) (f.target_app k x)
    | tip x => exact congrArg (WhiskerCell.base k) (f.target_app k x)
    | edge x => cases ε <;> rfl

theorem whisker_bounded (X : GlobularSet.{u}) (n : ℕ) (ε : Bool)
    (hX : ∀ k, n+1 < k → IsEmpty (X.Cell k)) (k : ℕ) (hk : n+1 < k) :
    IsEmpty ((X.whisker n ε).Cell k) := by
  constructor
  intro x
  cases x with
  | base k x => exact (hX k hk).false x
  | tip x => omega
  | edge x => omega

theorem whiskerMap_injective {X Y : GlobularSet.{u}} (f : Hom X Y)
    (hf : ∀ k, Function.Injective (f.app k)) (n : ℕ) (ε : Bool) (k : ℕ) :
    Function.Injective ((whiskerMap f n ε).app k) := by
  intro x y h
  cases x <;> cases y <;>
    simp only [whiskerMap, reduceCtorEq] at h
  all_goals congr 1; apply hf; injection h


def toPresheafUnderlying (X : GlobularSet.{u}) : Hom X X.presheaf.underlying where
  app _ := _root_.id
  source_app n x := (X.presheafUnderlyingMap.source_app n x).symm
  target_app n x := (X.presheafUnderlyingMap.target_app n x).symm

def whiskerDesc {X Y : GlobularSet.{u}} (n : ℕ) (f : Hom X Y)
    (e : X.Cell n → Y.Cell (n+1)) (he : ∀ x, Y.source n (e x) = f.app n x) :
    Hom (X.whisker n false) Y where
  app _ x := match x with
    | .base k x => f.app k x
    | .tip x => Y.target n (e x)
    | .edge x => e x
  source_app k x := by
    cases x with
    | base _ x => exact f.source_app k x
    | tip x =>
      change f.app k (X.source k x) = Y.source k (Y.target (k+1) (e x))
      rw [f.source_app, ← he, Y.source_source]
    | edge x => exact (he x).symm
  target_app k x := by
    cases x with
    | base _ x => exact f.target_app k x
    | tip x =>
      change f.app k (X.target k x) = Y.target k (Y.target (k+1) (e x))
      rw [f.target_app, ← he, Y.target_source]
    | edge x => rfl

theorem whisker_hom_ext {X Y : GlobularSet.{u}} (n : ℕ) (ε : Bool)
    (f g : Hom (X.whisker n ε) Y)
    (hbase : ∀ k x, f.app k (.base k x) = g.app k (.base k x))
    (hedge : ∀ x, f.app (n+1) (.edge x) = g.app (n+1) (.edge x)) : f = g := by
  ext k x
  cases x with
  | base k x => exact hbase k x
  | edge x => exact hedge x
  | tip x =>
    cases ε with
    | false =>
      have hf := f.target_app n (.edge x)
      have hg := g.target_app n (.edge x)
      exact hf.trans ((congrArg (Y.target n) (hedge x)).trans hg.symm)
    | true =>
      have hf := f.source_app n (.edge x)
      have hg := g.source_app n (.edge x)
      exact hf.trans ((congrArg (Y.source n) (hedge x)).trans hg.symm)

end Grothendieck.GlobularSet

namespace Grothendieck.GlobularPresheaf
open CategoryTheory CategoryTheory.Limits Opposite

def whiskering (n : ℕ) (ε : Bool) : GlobularPresheaf.{u} ⥤ GlobularPresheaf.{u} where
  obj X := (X.underlying.whisker n ε).presheaf
  map f := (GlobularSet.whiskerMap (underlyingMap f) n ε).presheafMap
  map_id X := by
    ext ⟨⟨k⟩⟩ x
    cases x <;> rfl
  map_comp f g := by
    ext ⟨⟨k⟩⟩ x
    cases x <;> rfl

def whiskeringInclusion (n : ℕ) (ε : Bool) : 𝟭 GlobularPresheaf.{u} ⟶ whiskering n ε where
  app X := X.underlyingPresheafIso.inv ≫ (X.underlying.whiskerInclusion n ε).presheafMap
  naturality {X Y} f := by ext; rfl

def whiskeringDesc {X Y : GlobularPresheaf.{u}} (n : ℕ) (f : X ⟶ Y)
    (e : X.underlying.Cell n → Y.underlying.Cell (n+1))
    (he : ∀ x, Y.underlying.source n (e x) = (underlyingMap f).app n x) :
    (whiskering n false).obj X ⟶ Y :=
  (GlobularSet.whiskerDesc n (underlyingMap f) e he).presheafMap ≫ Y.underlyingPresheafIso.hom

theorem whiskering_hom_ext {X Y : GlobularPresheaf.{u}} (n : ℕ) (ε : Bool)
    (f g : (whiskering n ε).obj X ⟶ Y)
    (hbase : ∀ k x, f.app (op (Globe.mk k)) (.base k x) =
      g.app (op (Globe.mk k)) (.base k x))
    (hedge : ∀ x, f.app (op (Globe.mk (n+1))) (.edge x) =
      g.app (op (Globe.mk (n+1))) (.edge x)) : f = g := by
  apply underlyingMap_injective
  have h := GlobularSet.whisker_hom_ext n ε
    ((X.underlying.whisker n ε).toPresheafUnderlying.comp (underlyingMap f))
    ((X.underlying.whisker n ε).toPresheafUnderlying.comp (underlyingMap g)) hbase hedge
  ext k x
  exact congrFun (congrArg (fun z => z.app k) h) x

theorem whiskering_pushout {A B D E : GlobularPresheaf.{u}}
    {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ E} {j : D ⟶ E}
    (h : IsPushout f g i j) (n : ℕ) : IsPushout
      ((whiskering n false).map f) ((whiskering n false).map g)
      ((whiskering n false).map i) ((whiskering n false).map j) := by
  let W := whiskering n false
  let η := whiskeringInclusion n false
  let N := (evaluation Globeᵒᵖ (Type u)).obj (op (Globe.mk n))
  have hn := h.map N
  have ηi : i ≫ η.app E = η.app B ≫ W.map i := η.naturality i
  have ηj : j ≫ η.app E = η.app D ≫ W.map j := η.naturality j
  have ηf : f ≫ η.app B = η.app A ≫ W.map f := η.naturality f
  have ηg : g ≫ η.app D = η.app A ≫ W.map g := η.naturality g
  apply IsPushout.mk'
  · rw [← W.map_comp, ← W.map_comp, h.w]
  · intro T a b ha hb
    apply whiskering_hom_ext n false a b
    · have he : η.app E ≫ a = η.app E ≫ b := h.hom_ext
        (by rw [← Category.assoc, ηi, Category.assoc, ha,
          ← Category.assoc, ← ηi, Category.assoc])
        (by rw [← Category.assoc, ηj, Category.assoc, hb,
          ← Category.assoc, ← ηj, Category.assoc])
      intro k x
      exact congrFun (congrArg (fun z => z.app (op (Globe.mk k))) he) x
    · have he := hn.hom_ext (W := T.obj (op (Globe.mk (n+1))))
        (k := TypeCat.ofHom (fun x => a.app (op (Globe.mk (n+1))) (.edge x)))
        (l := TypeCat.ofHom (fun x => b.app (op (Globe.mk (n+1))) (.edge x)))
        (by ext x; exact congrFun (congrArg (fun z => z.app (op (Globe.mk (n+1)))) ha) (.edge x))
        (by ext x; exact congrFun (congrArg (fun z => z.app (op (Globe.mk (n+1)))) hb) (.edge x))
      exact fun x => ConcreteCategory.congr_hom he x
  · intro T a b hab
    have hf : f ≫ η.app B ≫ a = g ≫ η.app D ≫ b := by
      rw [← Category.assoc, ηf, Category.assoc, hab,
        ← Category.assoc, ← ηg, Category.assoc]
    let d : E ⟶ T := h.desc (η.app B ≫ a) (η.app D ≫ b) hf
    have hw : N.map f ≫ TypeCat.ofHom (fun x => a.app (op (Globe.mk (n+1))) (.edge x)) =
        N.map g ≫ TypeCat.ofHom (fun x => b.app (op (Globe.mk (n+1))) (.edge x)) := by
      ext x
      exact congrFun (congrArg (fun z => z.app (op (Globe.mk (n+1)))) hab) (.edge x)
    let t : E.obj (op (Globe.mk n)) ⟶ T.obj (op (Globe.mk (n+1))) :=
      hn.desc (TypeCat.ofHom (fun x => a.app (op (Globe.mk (n+1))) (.edge x)))
        (TypeCat.ofHom (fun x => b.app (op (Globe.mk (n+1))) (.edge x))) hw
    have ht : ∀ x, T.underlying.source n (t x) = (underlyingMap d).app n x := by
      have he : t ≫ T.map (Globe.source n).op = d.app (op (Globe.mk n)) := by
        apply hn.hom_ext
        · rw [← Category.assoc, hn.inl_desc]
          have hd := congrArg (fun z => z.app (op (Globe.mk n))) (h.inl_desc _ _ hf)
          change _ = (i ≫ d).app (op (Globe.mk n))
          rw [hd]
          ext x
          exact (((B.underlying.whisker n false).toPresheafUnderlying.comp
            (underlyingMap a)).source_app n (.edge x)).symm
        · rw [← Category.assoc, hn.inr_desc]
          have hd := congrArg (fun z => z.app (op (Globe.mk n))) (h.inr_desc _ _ hf)
          change _ = (j ≫ d).app (op (Globe.mk n))
          rw [hd]
          ext x
          exact (((D.underlying.whisker n false).toPresheafUnderlying.comp
            (underlyingMap b)).source_app n (.edge x)).symm
      exact fun x => ConcreteCategory.congr_hom he x
    let l := whiskeringDesc n d t ht
    refine ⟨l, ?_, ?_⟩
    · apply whiskering_hom_ext n false
      · intro k x
        exact congrFun (congrArg (fun z => z.app (op (Globe.mk k)))
          (h.inl_desc _ _ hf)) x
      · intro x
        exact ConcreteCategory.congr_hom (hn.inl_desc _ _ hw) x
    · apply whiskering_hom_ext n false
      · intro k x
        exact congrFun (congrArg (fun z => z.app (op (Globe.mk k)))
          (h.inr_desc _ _ hf)) x
      · intro x
        exact ConcreteCategory.congr_hom (hn.inr_desc _ _ hw) x

end Grothendieck.GlobularPresheaf

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite

structure CoGlobularObject (K : Type u) [Category.{v} K] where
  obj : ℕ → K
  source : ∀ n, obj n ⟶ obj (n+1)
  target : ∀ n, obj n ⟶ obj (n+1)
  source_source : ∀ n, source n ≫ source (n+1) = source n ≫ target (n+1)
  target_source : ∀ n, target n ≫ source (n+1) = target n ≫ target (n+1)

namespace CoGlobularObject
variable {K : Type u} [Category.{v} K]

def adjacent (B : CoGlobularObject K) (n : ℕ) (ε : Bool) : B.obj n ⟶ B.obj (n+1) :=
  if ε then B.target n else B.source n

theorem adjacent_pair (B : CoGlobularObject K) (n : ℕ) (ε δ : Bool) :
    B.adjacent n ε ≫ B.adjacent (n+1) δ = B.adjacent n ε ≫ B.source (n+1) := by
  cases ε <;> cases δ <;> simp only [adjacent, Bool.false_eq_true, ↓reduceIte]
  · exact (B.source_source n).symm
  · exact (B.target_source n).symm

def face (B : CoGlobularObject K) {m k : ℕ} (h : m < k) (ε : Bool) : B.obj m ⟶ B.obj k :=
  match k with
  | 0 => False.elim (by omega)
  | k+1 => if e : m = k then eqToHom (congrArg B.obj e) ≫ B.adjacent k ε
    else B.face (by omega : m < k) ε ≫ B.source k

@[simp] theorem face_succ (B : CoGlobularObject K) (n : ℕ) (ε : Bool) :
    B.face (Nat.lt_succ_self n) ε = B.adjacent n ε := by
  rw [face, dite_eq_left rfl]
  simp

theorem face_adjacent (B : CoGlobularObject K) {m k : ℕ} (h : m < k) (ε δ : Bool) :
    B.face h ε ≫ B.adjacent k δ = B.face (by omega : m < k+1) ε := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases e : m = k
    · subst m
      rw [face_succ, B.adjacent_pair]
      rw [face, dite_eq_right (by omega)]
      rw [face_succ]
    · have hm : m < k := by omega
      rw [face, dite_eq_right e, Category.assoc]
      change (B.face hm ε ≫ B.adjacent k false ≫ B.adjacent (k+1) δ) = _
      rw [B.adjacent_pair, ← Category.assoc]
      rw [face, dite_eq_right (by omega), face, dite_eq_right e]
      rfl

theorem face_comp (B : CoGlobularObject K) {m k l : ℕ} (h : m < k) (h' : k < l)
    (ε δ : Bool) : B.face h ε ≫ B.face h' δ = B.face (h.trans h') ε := by
  induction l with
  | zero => omega
  | succ l ih =>
    by_cases e : k = l
    · subst k
      rw [face_succ]
      exact B.face_adjacent h ε δ
    · have hkl : k < l := by omega
      rw [face, dite_eq_right e, ← Category.assoc, ih hkl]
      exact B.face_adjacent (h.trans hkl) ε false

def eval (B : CoGlobularObject K) {m n : ℕ} (f : Globe.Face m n) : B.obj m ⟶ B.obj n :=
  match f with
  | .id _ => 𝟙 _
  | .face h ε => B.face h ε

def functor (B : CoGlobularObject K) : Globe ⥤ K where
  obj k := B.obj k.dim
  map f := B.eval f
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    rcases X with ⟨x⟩
    rcases Y with ⟨y⟩
    rcases Z with ⟨z⟩
    change Globe.Face x y at f
    change Globe.Face y z at g
    cases f with
    | id => exact (Category.id_comp _).symm
    | face h ε =>
      cases g with
      | id => exact (Category.comp_id _).symm
      | face h' δ => exact (B.face_comp h h' ε δ).symm

noncomputable def realization (B : CoGlobularObject K) [HasColimitsOfSize.{0,max v w} K] :
    GlobularPresheaf.{max v w} ⥤ K := by
  let : (uliftYoneda.{max v w}).HasPointwiseLeftKanExtension B.functor := fun _ => by infer_instance
  exact uliftYoneda.{max v w}.leftKanExtension B.functor

noncomputable def globeIso (B : CoGlobularObject K) [HasColimitsOfSize.{0,max v w} K]
    (k : ℕ) : B.realization.obj (GlobularPresheaf.disk.{max v w} k) ≅ B.obj k := by
  let : (uliftYoneda.{max v w}).HasPointwiseLeftKanExtension B.functor := fun _ => by infer_instance
  exact (Presheaf.isExtensionAlongULiftYoneda B.functor).app (Globe.mk k)

instance preservesColimits_realization (B : CoGlobularObject K)
    [HasColimitsOfSize.{0,max v w} K] : PreservesColimits B.realization := by
  let : (uliftYoneda.{max v w}).HasPointwiseLeftKanExtension B.functor := fun _ => by infer_instance
  unfold realization
  infer_instance

@[reassoc] theorem globeIso_naturality (B : CoGlobularObject K)
    [HasColimitsOfSize.{0,max v w} K] {j k : ℕ} (f : Globe.Face j k) :
    B.realization.map (uliftYoneda.map f) ≫ (B.globeIso k).hom =
      (B.globeIso j).hom ≫ B.eval f := by
  let : (uliftYoneda.{max v w}).HasPointwiseLeftKanExtension B.functor := fun _ => by infer_instance
  exact (Presheaf.isExtensionAlongULiftYoneda B.functor).hom.naturality f

noncomputable def homEquiv (B : CoGlobularObject K) [HasColimitsOfSize.{0,max v w} K]
    (S : GlobularPresheaf.{max v w}) (Y : K) :
    (B.realization.obj S ⟶ Y) ≃ (S ⟶ (Presheaf.restrictedULiftYoneda.{w} B.functor).obj Y) := by
  let : (uliftYoneda.{max v w}).HasPointwiseLeftKanExtension B.functor := fun _ => by infer_instance
  exact (Presheaf.uliftYonedaAdjunction _ (uliftYoneda.leftKanExtensionUnit B.functor)).homEquiv S Y

noncomputable def cell (B : CoGlobularObject K) [HasColimitsOfSize.{0,max v w} K]
    (S : GlobularPresheaf.{max v w}) (k : ℕ) (x : S.obj (op (Globe.mk k))) :
    B.obj k ⟶ B.realization.obj S :=
  (B.globeIso k).inv ≫ B.realization.map (uliftYonedaEquiv.symm x)

@[simp] theorem homEquiv_app (B : CoGlobularObject K) [HasColimitsOfSize.{0,max v w} K]
    (S : GlobularPresheaf.{max v w}) (Y : K) (f : B.realization.obj S ⟶ Y)
    (k : ℕ) (x : S.obj (op (Globe.mk k))) :
    ((B.homEquiv S Y) f).app (op (Globe.mk k)) x = ULift.up (B.cell S k x ≫ f) := by
  let : (uliftYoneda.{max v w}).HasPointwiseLeftKanExtension B.functor := fun _ => by infer_instance
  change ((uliftYoneda.{max v w}).leftKanExtension B.functor).obj S ⟶ Y at f
  change ((Presheaf.uliftYonedaAdjunction _ (uliftYoneda.leftKanExtensionUnit B.functor)).homEquiv S Y f).app _ x = _
  rw [Presheaf.uliftYonedaAdjunction_homEquiv_app]
  congr 1
  exact (Category.assoc _ _ _).symm

theorem hom_ext (B : CoGlobularObject K) [HasColimitsOfSize.{0,max v w} K]
    {S : GlobularPresheaf.{max v w}} {Y : K} {f g : B.realization.obj S ⟶ Y}
    (h : ∀ k x, B.cell S k x ≫ f = B.cell S k x ≫ g) : f = g := by
  apply (B.homEquiv S Y).injective
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  rcases k with ⟨⟨k⟩⟩
  simp only [homEquiv_app]
  exact congrArg ULift.up (h k x)

end CoGlobularObject

structure FiniteCoGlobularObject (K : Type u) [Category.{v} K] (q : ℕ) where
  obj : ∀ k, k ≤ q → K
  source : ∀ k (hk : k+1 ≤ q), obj k (by omega) ⟶ obj (k+1) hk
  target : ∀ k (hk : k+1 ≤ q), obj k (by omega) ⟶ obj (k+1) hk
  source_source : ∀ k (hk : k+2 ≤ q),
    source k (by omega) ≫ source (k+1) hk = source k (by omega) ≫ target (k+1) hk
  target_source : ∀ k (hk : k+2 ≤ q),
    target k (by omega) ≫ source (k+1) hk = target k (by omega) ≫ target (k+1) hk

namespace FiniteCoGlobularObject
variable {K : Type u} [Category.{v} K] [HasTerminal K] {q : ℕ}

noncomputable def completedObj (B : FiniteCoGlobularObject K q) (k : ℕ) : K :=
  if h : k ≤ q then B.obj k h else ⊤_ K

theorem completedObj_eq (B : FiniteCoGlobularObject K q) (k : ℕ) (h : k ≤ q) :
    B.completedObj k = B.obj k h := dite_eq_left h

theorem completedObj_terminal (B : FiniteCoGlobularObject K q) (k : ℕ) (h : ¬ k ≤ q) :
    B.completedObj k = ⊤_ K := dite_eq_right h

noncomputable def completedArrow (B : FiniteCoGlobularObject K q) (k : ℕ) (ε : Bool) :
    B.completedObj k ⟶ B.completedObj (k+1) :=
  if h : k+1 ≤ q then
    eqToHom (B.completedObj_eq k (by omega)) ≫
      (if ε then B.target k h else B.source k h) ≫
      eqToHom (B.completedObj_eq (k+1) h).symm
  else terminal.from _ ≫ eqToHom (B.completedObj_terminal (k+1) h).symm

theorem completed_identity (B : FiniteCoGlobularObject K q) (k : ℕ) (ε : Bool) :
    B.completedArrow k ε ≫ B.completedArrow (k+1) false =
      B.completedArrow k ε ≫ B.completedArrow (k+1) true := by
  by_cases h : k+2 ≤ q
  · simp only [completedArrow, h, show k+1 ≤ q by omega, ↓reduceDIte]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    cases ε <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [← Category.assoc (B.source k _), B.source_source k h, Category.assoc]
    · rw [← Category.assoc (B.target k _), B.target_source k h, Category.assoc]
  · have ht : IsTerminal (B.completedObj (k+2)) := by
      simpa only [completedObj, dite_eq_right h] using (terminalIsTerminal (C := K))
    exact ht.hom_ext _ _

noncomputable abbrev complete (B : FiniteCoGlobularObject K q) : CoGlobularObject K where
  obj := B.completedObj
  source k := B.completedArrow k false
  target k := B.completedArrow k true
  source_source k := B.completed_identity k false
  target_source k := B.completed_identity k true

noncomputable def map {L : Type w} [Category.{v} L]
    (B : FiniteCoGlobularObject K q) (F : K ⥤ L) : FiniteCoGlobularObject L q where
  obj k hk := F.obj (B.obj k hk)
  source k hk := F.map (B.source k hk)
  target k hk := F.map (B.target k hk)
  source_source k hk := by rw [← F.map_comp, ← F.map_comp, B.source_source k hk]
  target_source k hk := by rw [← F.map_comp, ← F.map_comp, B.target_source k hk]

noncomputable def lowIso (B : FiniteCoGlobularObject K q) (k : ℕ) (hk : k ≤ q) :
    B.complete.obj k ≅ B.obj k hk := eqToIso (B.completedObj_eq k hk)

noncomputable def face (B : FiniteCoGlobularObject K q) {j k : ℕ}
    (h : j < k) (hk : k ≤ q) (ε : Bool) : B.obj j (by omega) ⟶ B.obj k hk :=
  (B.lowIso j (by omega)).inv ≫ B.complete.face h ε ≫ (B.lowIso k hk).hom

@[simp] theorem face_succ (B : FiniteCoGlobularObject K q) (k : ℕ)
    (hk : k+1 ≤ q) (ε : Bool) :
    B.face (Nat.lt_succ_self k) hk ε = if ε then B.target k hk else B.source k hk := by
  rw [face, CoGlobularObject.face_succ]
  have e : B.complete.adjacent k ε = B.completedArrow k ε := by cases ε <;> rfl
  rw [e]
  change eqToHom (B.completedObj_eq k (by omega)).symm ≫ B.completedArrow k ε ≫
    eqToHom (B.completedObj_eq (k+1) hk) = _
  rw [completedArrow, dite_eq_left hk]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id]

theorem face_comp (B : FiniteCoGlobularObject K q) {i j k : ℕ}
    (h : i < j) (h' : j < k) (hk : k ≤ q) (ε δ : Bool) :
    B.face h (by omega) ε ≫ B.face h' hk δ = B.face (h.trans h') hk ε := by
  simp only [face, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (B.complete.face h ε), B.complete.face_comp]

theorem face_adjacent (B : FiniteCoGlobularObject K q) {j k : ℕ}
    (h : j < k) (hk : k+1 ≤ q) (ε δ : Bool) :
    B.face h (by omega) ε ≫ (if δ then B.target k hk else B.source k hk) =
      B.face (by omega : j < k+1) hk ε := by
  rw [← B.face_succ k hk δ]
  exact B.face_comp h (Nat.lt_succ_self k) hk ε δ

noncomputable def realization (B : FiniteCoGlobularObject K q)
    [HasColimitsOfSize.{0,max v w} K] : GlobularPresheaf.{max v w} ⥤ K := B.complete.realization

noncomputable def globeIso (B : FiniteCoGlobularObject K q)
    [HasColimitsOfSize.{0,max v w} K] (k : ℕ) (hk : k ≤ q) :
    B.realization.obj (GlobularPresheaf.disk.{max v w} k) ≅ B.obj k hk :=
  (B.complete.globeIso k) ≪≫ B.lowIso k hk

@[reassoc] theorem globeIso_face (B : FiniteCoGlobularObject K q)
    [HasColimitsOfSize.{0,max v w} K] {j k : ℕ} (h : j < k) (hk : k ≤ q) (ε : Bool) :
    B.realization.map (GlobularPresheaf.face h ε) ≫ (B.globeIso k hk).hom =
      (B.globeIso j (by omega)).hom ≫ B.face h hk ε := by
  change B.complete.realization.map (GlobularPresheaf.face h ε) ≫
    ((B.complete.globeIso k).hom ≫ (B.lowIso k hk).hom) =
      ((B.complete.globeIso j).hom ≫ (B.lowIso j (by omega)).hom) ≫
        (B.lowIso j (by omega)).inv ≫ B.complete.face h ε ≫ (B.lowIso k hk).hom
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have e := B.complete.globeIso_naturality (Globe.face h ε)
  change B.complete.realization.map (GlobularPresheaf.face h ε) ≫
    (B.complete.globeIso k).hom = (B.complete.globeIso j).hom ≫ B.complete.face h ε at e
  rw [← Category.assoc, e, Category.assoc]

end FiniteCoGlobularObject

namespace Shape
open GlobularTheory

def linearBlock (n k : ℕ) : Shape :=
  if k < n then globe k else if k = n then globe (n+1) else tripleShape n

theorem linearBlock_low (n k : ℕ) (h : k < n) : linearBlock n k = globe k := by
  simp only [linearBlock, ite_eq_left h]

theorem linearBlock_center (n k : ℕ) (h : k = n) : linearBlock n k = globe (n+1) := by
  subst k
  simp only [linearBlock, lt_self_iff_false, ↓reduceIte]

theorem linearBlock_high (n k : ℕ) (h : n < k) : linearBlock n k = tripleShape n := by
  simp only [linearBlock, ite_eq_right (by omega : ¬ k < n), ite_eq_right (by omega : ¬ k = n)]

noncomputable def linearAdjacent (n k : ℕ) (hk : k ≤ n) (ε : Bool) :
    linearBlock n k ⟶ linearBlock n (k+1) :=
  if h : k < n then
    if h' : k+1 < n then
      eqToHom (linearBlock_low n k h) ≫ face (Nat.lt_succ_self k) ε ≫
        eqToHom (linearBlock_low n (k+1) h').symm
    else
      eqToHom (linearBlock_low n k h) ≫ face (by omega : k < n+1) ε ≫
        eqToHom (linearBlock_center n (k+1) (by omega)).symm
  else
    eqToHom (linearBlock_center n k (by omega)) ≫
      (if ε then tripleLast n else tripleFirst n) ≫
      eqToHom (linearBlock_high n (k+1) (by omega)).symm

theorem face_comp {a b c : ℕ} (h : a < b) (h' : b < c) (ε δ : Bool) :
    face h ε ≫ face h' δ = face (h.trans h') ε := by
  change uliftYoneda.map (Globe.face h ε) ≫ uliftYoneda.map (Globe.face h' δ) = _
  rw [← uliftYoneda.map_comp]
  rfl

theorem face_triple_first_last (n k : ℕ) (hk : k < n) (ε : Bool) :
    face (by omega : k < n+1) ε ≫ tripleFirst n =
      face (by omega : k < n+1) ε ≫ tripleLast n := by
  have h₀ := congrArg (fun f => face hk ε ≫ f) (triple_first_middle n)
  have h₁ := congrArg (fun f => face hk ε ≫ f) (triple_middle_last n)
  rw [← Category.assoc, ← Category.assoc] at h₀ h₁
  change (face hk ε ≫ face (Nat.lt_succ_self n) true) ≫ tripleFirst n =
    (face hk ε ≫ face (Nat.lt_succ_self n) false) ≫ tripleMiddle n at h₀
  change (face hk ε ≫ face (Nat.lt_succ_self n) true) ≫ tripleMiddle n =
    (face hk ε ≫ face (Nat.lt_succ_self n) false) ≫ tripleLast n at h₁
  rw [face_comp, face_comp] at h₀ h₁
  exact h₀.trans h₁

theorem linearAdjacent_identity (n k : ℕ) (hk : k+2 ≤ n+1) (ε : Bool) :
    linearAdjacent n k (by omega) ε ≫ linearAdjacent n (k+1) (by omega) false =
      linearAdjacent n k (by omega) ε ≫ linearAdjacent n (k+1) (by omega) true := by
  have h : k < n := by omega
  by_cases h' : k+1 < n
  · by_cases h'' : k+2 < n
    · simp only [linearAdjacent, dite_eq_left h, dite_eq_left h', dite_eq_left h'']
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Category.assoc (face _ ε), face_comp, ← Category.assoc (face _ ε), face_comp]
    · simp only [linearAdjacent, dite_eq_left h, dite_eq_left h', dite_eq_right h'']
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Category.assoc (face _ ε), face_comp, ← Category.assoc (face _ ε), face_comp]
  · simp only [linearAdjacent, dite_eq_left h, dite_eq_right h', Bool.false_eq_true, ↓reduceIte]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (face _ ε), face_triple_first_last n k h ε, Category.assoc]

noncomputable def linearDiagram (n : ℕ) : FiniteCoGlobularObject Shape (n+1) where
  obj k _ := linearBlock n k
  source k hk := linearAdjacent n k (by omega) false
  target k hk := linearAdjacent n k (by omega) true
  source_source k hk := linearAdjacent_identity n k hk false
  target_source k hk := linearAdjacent_identity n k hk true

noncomputable def linearGlobularDiagram (n : ℕ) : FiniteCoGlobularObject GlobularPresheaf.{0} (n+1) :=
  (linearDiagram n).map realization

noncomputable def linearization (n : ℕ) : GlobularPresheaf.{0} ⥤ GlobularPresheaf.{0} :=
  (linearGlobularDiagram n).realization

noncomputable def linearGlobeIso (n k : ℕ) (hk : k ≤ n+1) :
    (linearization n).obj (GlobularPresheaf.disk k) ≅ (linearBlock n k).realize :=
  (linearGlobularDiagram n).globeIso k hk

end Shape
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace Shape

def linearHeight (n k : ℕ) : ℕ := if k < n then k else n+1

theorem linearHeight_lt (n b k : ℕ) (hb : b < n) (hk : b < k) :
    b < linearHeight n k := by
  unfold linearHeight
  split_ifs <;> omega

theorem linear_adjacent_realization (n k : ℕ) (hk : k ≤ n) (ε : Bool) :
    (if ε then (linearGlobularDiagram n).target k (by omega)
       else (linearGlobularDiagram n).source k (by omega)) =
      realization.map (linearAdjacent n k hk ε) := by
  cases ε <;> rfl

theorem linear_face_low (n b k : ℕ) (h : b < k) (hk : k < n) (ε : Bool) :
    (linearGlobularDiagram n).face h (by omega) ε =
      realization.map (eqToHom (linearBlock_low n b (by omega)) ≫
        face h ε ≫ eqToHom (linearBlock_low n k hk).symm) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases eb : b = k
    · subst b
      rw [FiniteCoGlobularObject.face_succ, linear_adjacent_realization _ _ (by omega)]
      congr 1
      simp only [linearAdjacent, dite_eq_left (by omega : k < n), dite_eq_left hk]
    · have hb : b < k := by omega
      rw [← (linearGlobularDiagram n).face_adjacent hb (by omega) ε false,
        ih hb (by omega), linear_adjacent_realization _ _ (by omega)]
      change realization.map _ ≫ realization.map _ = realization.map _
      rw [← Functor.map_comp]
      congr 1
      simp only [linearAdjacent, dite_eq_left (by omega : k < n), dite_eq_left hk]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Category.assoc (face _ ε), face_comp]

theorem linear_face_center (n b : ℕ) (h : b < n) (ε : Bool) :
    (linearGlobularDiagram n).face h (by omega) ε =
      realization.map (eqToHom (linearBlock_low n b h) ≫
        face (by omega : b < n+1) ε ≫ eqToHom (linearBlock_center n n rfl).symm) := by
  cases n with
  | zero => omega
  | succ n =>
    by_cases eb : b = n
    · subst b
      rw [FiniteCoGlobularObject.face_succ, linear_adjacent_realization _ _ (by omega)]
      congr 1
      simp only [linearAdjacent, dite_eq_left (Nat.lt_succ_self n), dite_eq_right (lt_irrefl (n+1))]
    · have hb : b < n := by omega
      rw [← (linearGlobularDiagram (n+1)).face_adjacent hb (by omega) ε false,
        linear_face_low _ _ _ hb (by omega), linear_adjacent_realization _ _ (by omega)]
      change realization.map _ ≫ realization.map _ = realization.map _
      rw [← Functor.map_comp]
      congr 1
      simp only [linearAdjacent, dite_eq_left (Nat.lt_succ_self n), dite_eq_right (lt_irrefl (n+1))]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Category.assoc (face _ ε), face_comp]

theorem linear_face_top (n : ℕ) (ε : Bool) :
    (linearGlobularDiagram n).face (Nat.lt_succ_self n) le_rfl ε =
      realization.map (eqToHom (linearBlock_center n n rfl) ≫
        (if ε then GlobularTheory.tripleLast n else GlobularTheory.tripleFirst n) ≫
        eqToHom (linearBlock_high n (n+1) (Nat.lt_succ_self n)).symm) := by
  rw [FiniteCoGlobularObject.face_succ, linear_adjacent_realization _ _ (by omega)]
  congr 1
  simp only [linearAdjacent, dite_eq_right (lt_irrefl n)]

theorem linear_face_top_low (n b : ℕ) (h : b < n) (ε : Bool) :
    (linearGlobularDiagram n).face (by omega : b < n+1) le_rfl ε =
      realization.map (eqToHom (linearBlock_low n b h) ≫
        face (by omega : b < n+1) ε ≫ GlobularTheory.tripleLast n ≫
        eqToHom (linearBlock_high n (n+1) (Nat.lt_succ_self n)).symm) := by
  rw [← (linearGlobularDiagram n).face_adjacent h le_rfl ε true,
    linear_face_center, linear_adjacent_realization _ _ (by omega)]
  change realization.map _ ≫ realization.map _ = realization.map _
  rw [← Functor.map_comp]
  congr 1
  simp only [linearAdjacent, dite_eq_right (lt_irrefl n), ↓reduceIte]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

theorem isPushout_attach (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    IsPushout (S.seam hl) (face hr false) (S.inl b h hl hr) (S.inr b h hl hr) := by
  have H := realization_pushout S b h hl hr
  apply IsPushout.mk'
  · exact H.w
  · intro T f g hi hj
    exact H.hom_ext hi hj
  · intro T f g hw
    exact ⟨H.desc f g hw, H.inl_desc _ _ _, H.inr_desc _ _ _⟩

end Shape
namespace GlobularTheory

theorem composition_isPushout (n : ℕ) :
    IsPushout (Shape.target n) (Shape.source n) (compositionLeft n) (compositionRight n) := by
  have h := Shape.isPushout_attach (Shape.globe (n+1)) n (n+1)
    (Nat.lt_succ_self n) (Nat.lt_succ_self n)
  change IsPushout (Shape.target n ≫ 𝟙 _) (Shape.source n) (compositionLeft n) (compositionRight n) at h
  simpa only [Category.comp_id] using h

noncomputable def triplePrefix (n : ℕ) : compositionShape n ⟶ tripleShape n :=
  (compositionShape n).inl n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

theorem triple_isPushout (n : ℕ) :
    IsPushout (Shape.target n ≫ compositionRight n) (Shape.source n)
      (triplePrefix n) (tripleLast n) := Shape.isPushout_attach _ _ _ _ _

noncomputable def tripleDesc {S : Shape} (n : ℕ)
    (a b c : Shape.globe (n+1) ⟶ S)
    (hab : Shape.target n ≫ a = Shape.source n ≫ b)
    (hbc : Shape.target n ≫ b = Shape.source n ≫ c) : tripleShape n ⟶ S :=
  (triple_isPushout n).desc ((composition_isPushout n).desc a b hab) c (by
    rw [Category.assoc, IsPushout.inr_desc]
    exact hbc)

@[reassoc (attr := simp)] theorem tripleDesc_first {S : Shape} (n : ℕ)
    (a b c : Shape.globe (n+1) ⟶ S) (hab) (hbc) :
    tripleFirst n ≫ tripleDesc n a b c hab hbc = a := by
  change (compositionLeft n ≫ triplePrefix n) ≫ tripleDesc n a b c hab hbc = a
  rw [tripleDesc, Category.assoc, IsPushout.inl_desc, IsPushout.inl_desc]

@[reassoc (attr := simp)] theorem tripleDesc_middle {S : Shape} (n : ℕ)
    (a b c : Shape.globe (n+1) ⟶ S) (hab) (hbc) :
    tripleMiddle n ≫ tripleDesc n a b c hab hbc = b := by
  change (compositionRight n ≫ triplePrefix n) ≫ tripleDesc n a b c hab hbc = b
  rw [tripleDesc, Category.assoc, IsPushout.inl_desc, IsPushout.inr_desc]

@[reassoc (attr := simp)] theorem tripleDesc_last {S : Shape} (n : ℕ)
    (a b c : Shape.globe (n+1) ⟶ S) (hab) (hbc) :
    tripleLast n ≫ tripleDesc n a b c hab hbc = c := by
  exact (triple_isPushout n).inr_desc _ _ _

theorem triple_hom_ext {S : Shape} (n : ℕ) {f g : tripleShape n ⟶ S}
    (h₀ : tripleFirst n ≫ f = tripleFirst n ≫ g)
    (h₁ : tripleMiddle n ≫ f = tripleMiddle n ≫ g)
    (h₂ : tripleLast n ≫ f = tripleLast n ≫ g) : f = g := by
  apply (triple_isPushout n).hom_ext
  · apply (composition_isPushout n).hom_ext
    · exact (Category.assoc _ _ _).symm.trans (h₀.trans (Category.assoc _ _ _))
    · exact (Category.assoc _ _ _).symm.trans (h₁.trans (Category.assoc _ _ _))
  · exact h₂

end GlobularTheory
namespace Shape

open GlobularTheory

noncomputable def lastArrow (S : Shape) : globe S.1 ⟶ S := S.last

abbrev appendTwo (n : ℕ) (T : Table (n+1)) : Shape :=
  (attach ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)).attach
    n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def appendTwoOld (n : ℕ) (T : Table (n+1)) : ⟨n+1,T⟩ ⟶ appendTwo n T :=
  inl ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n) ≫
    (attach ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)).inl
      n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def appendTwoMiddle (n : ℕ) (T : Table (n+1)) : globe (n+1) ⟶ appendTwo n T :=
  inr ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n) ≫
    (attach ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)).inl
      n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def appendTwoLast (n : ℕ) (T : Table (n+1)) : globe (n+1) ⟶ appendTwo n T :=
  (attach ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)).inr
    n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def appendTwoTail (n : ℕ) (T : Table (n+1)) : tripleShape n ⟶ appendTwo n T :=
  tripleDesc n (lastArrow ⟨n+1,T⟩ ≫ appendTwoOld n T) (appendTwoMiddle n T) (appendTwoLast n T)
    (by
      have h := (isPushout_attach ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)).w
      change (target n ≫ lastArrow ⟨n+1,T⟩) ≫
        inl ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n) =
        source n ≫ inr ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n) at h
      simpa only [appendTwoOld, appendTwoMiddle, Category.assoc] using
        congrArg (fun f => f ≫ (attach ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n)
          (Nat.lt_succ_self n)).inl n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)) h)
    (by
      exact (Category.assoc _ _ _).symm.trans
        (isPushout_attach (attach ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n)
          (Nat.lt_succ_self n)) n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)).w)

@[reassoc (attr := simp)] theorem appendTwoTail_first (n : ℕ) (T : Table (n+1)) :
    tripleFirst n ≫ appendTwoTail n T = lastArrow ⟨n+1,T⟩ ≫ appendTwoOld n T :=
  tripleDesc_first _ _ _ _ _ _

@[reassoc (attr := simp)] theorem appendTwoTail_middle (n : ℕ) (T : Table (n+1)) :
    tripleMiddle n ≫ appendTwoTail n T = appendTwoMiddle n T :=
  tripleDesc_middle _ _ _ _ _ _

@[reassoc (attr := simp)] theorem appendTwoTail_last (n : ℕ) (T : Table (n+1)) :
    tripleLast n ≫ appendTwoTail n T = appendTwoLast n T :=
  tripleDesc_last _ _ _ _ _ _

theorem appendTwo_isPushout (n : ℕ) (T : Table (n+1)) :
    IsPushout (lastArrow ⟨n+1,T⟩) (tripleFirst n) (appendTwoOld n T) (appendTwoTail n T) := by
  let S : Shape := ⟨n+1,T⟩
  let S' := S.attach n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)
  let p := isPushout_attach S n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)
  let p' := isPushout_attach S' n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)
  apply IsPushout.mk'
  · exact (appendTwoTail_first n T).symm
  · intro R f g hf hg
    have hm := congrArg (tripleMiddle n ≫ ·) hg
    have hl := congrArg (tripleLast n ≫ ·) hg
    simp only [appendTwoTail_middle_assoc, appendTwoTail_last_assoc] at hm hl
    apply p'.hom_ext
    · apply p.hom_ext
      · exact (Category.assoc _ _ _).symm.trans (hf.trans (Category.assoc _ _ _))
      · exact (Category.assoc _ _ _).symm.trans (hm.trans (Category.assoc _ _ _))
    · exact hl
  · intro R f g hw
    have w₁ : S.seam (Nat.lt_succ_self n) ≫ f = source n ≫ (tripleMiddle n ≫ g) := by
      change (target n ≫ lastArrow S) ≫ f = _
      rw [Category.assoc, hw, ← Category.assoc]
      exact congrArg (· ≫ g) (triple_first_middle n)
    let d₁ : S' ⟶ R := p.desc f (tripleMiddle n ≫ g) w₁
    have w₂ : S'.seam (Nat.lt_succ_self n) ≫ d₁ = source n ≫ (tripleLast n ≫ g) := by
      change (target n ≫ S.inr n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)) ≫ d₁ = _
      erw [Category.assoc, IsPushout.inr_desc, ← Category.assoc]
      exact congrArg (· ≫ g) (triple_middle_last n)
    let d₂ : appendTwo n T ⟶ R := p'.desc d₁ (tripleLast n ≫ g) w₂
    have ho : appendTwoOld n T ≫ d₂ = f := by
      change (p.cocone.inl ≫ p'.cocone.inl) ≫ d₂ = _
      erw [Category.assoc, IsPushout.inl_desc, IsPushout.inl_desc]
    have hm : appendTwoMiddle n T ≫ d₂ = tripleMiddle n ≫ g := by
      change (p.cocone.inr ≫ p'.cocone.inl) ≫ d₂ = _
      erw [Category.assoc, IsPushout.inl_desc, IsPushout.inr_desc]
    have hl : appendTwoLast n T ≫ d₂ = tripleLast n ≫ g := p'.inr_desc _ _ _
    refine ⟨d₂, ho, ?_⟩
    apply triple_hom_ext n
    · rw [appendTwoTail_first_assoc, ho]
      exact hw
    · rw [appendTwoTail_middle_assoc, hm]
    · rw [appendTwoTail_last_assoc, hl]

end Shape

theorem threeChain_pushout {K : Type u} [Category.{v} K]
    {A D B V T B₁ B₂ : K} {s t : A ⟶ D} {a : D ⟶ B}
    {c₀ c₁ : D ⟶ V} {c : V ⟶ T} {c₂ : D ⟶ T}
    {i : B ⟶ B₁} {j : D ⟶ B₁} {i' : B₁ ⟶ B₂} {j' : D ⟶ B₂}
    (p₀ : IsPushout t s c₀ c₁) (p₁ : IsPushout (t ≫ c₁) s c c₂)
    (p : IsPushout (t ≫ a) s i j) (p' : IsPushout (t ≫ j) s i' j')
    (m : T ⟶ B₂) (hm₀ : (c₀ ≫ c) ≫ m = a ≫ i ≫ i')
    (hm₁ : (c₁ ≫ c) ≫ m = j ≫ i') (hm₂ : c₂ ≫ m = j') :
    IsPushout a (c₀ ≫ c) (i ≫ i') m := by
  apply IsPushout.mk'
  · exact hm₀.symm
  · intro R f g hf hg
    apply p'.hom_ext
    · apply p.hom_ext
      · simpa only [Category.assoc] using hf
      · have h := congrArg ((c₁ ≫ c) ≫ ·) hg
        simpa only [← Category.assoc, hm₁] using h
    · have h := congrArg (c₂ ≫ ·) hg
      simpa only [← Category.assoc, hm₂] using h
  · intro R f g hw
    have w₁ : (t ≫ a) ≫ f = s ≫ ((c₁ ≫ c) ≫ g) := by
      rw [Category.assoc, hw]
      simpa only [Category.assoc] using congrArg (fun z => z ≫ c ≫ g) p₀.w
    let d₁ := p.desc f ((c₁ ≫ c) ≫ g) w₁
    have w₂ : (t ≫ j) ≫ d₁ = s ≫ (c₂ ≫ g) := by
      rw [Category.assoc, p.inr_desc]
      simpa only [Category.assoc] using congrArg (· ≫ g) p₁.w
    let d₂ := p'.desc d₁ (c₂ ≫ g) w₂
    have ho : (i ≫ i') ≫ d₂ = f := by
      rw [Category.assoc, p'.inl_desc, p.inl_desc]
    have hm : (j ≫ i') ≫ d₂ = (c₁ ≫ c) ≫ g := by
      rw [Category.assoc, p'.inl_desc, p.inr_desc]
    have hl : j' ≫ d₂ = c₂ ≫ g := p'.inr_desc _ _ _
    refine ⟨d₂, ho, ?_⟩
    apply p₁.hom_ext
    · apply p₀.hom_ext
      · calc
          c₀ ≫ c ≫ m ≫ d₂ = a ≫ (i ≫ i') ≫ d₂ := by
            simpa only [Category.assoc] using congrArg (· ≫ d₂) hm₀
          _ = a ≫ f := by rw [ho]
          _ = c₀ ≫ c ≫ g := by simpa only [Category.assoc] using hw
      · simpa only [Category.assoc] using
          (congrArg (· ≫ d₂) hm₁).trans hm
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ d₂) hm₂).trans hl)

namespace Shape
open GlobularTheory

theorem composition_realization_isPushout (n : ℕ) :
    IsPushout (realization.map (target n)) (realization.map (source n))
      (realization.map (compositionLeft n)) (realization.map (compositionRight n)) := by
  have h := realization_pushout (globe (n+1)) n (n+1)
    (Nat.lt_succ_self n) (Nat.lt_succ_self n)
  change IsPushout (GlobularPresheaf.face (Nat.lt_succ_self n) true ≫ 𝟙 _)
    (realization.map (source n)) _ _ at h
  rw [Category.comp_id] at h
  exact h

theorem triple_realization_isPushout (n : ℕ) :
    IsPushout (realization.map (target n ≫ compositionRight n))
      (realization.map (source n)) (realization.map (triplePrefix n))
      (realization.map (tripleLast n)) := realization_pushout _ _ _ _ _

theorem appendTwo_realization_isPushout (n : ℕ) (T : Table (n+1)) :
    IsPushout (realization.map (lastArrow ⟨n+1,T⟩)) (realization.map (tripleFirst n))
      (realization.map (appendTwoOld n T)) (realization.map (appendTwoTail n T)) := by
  apply threeChain_pushout (composition_realization_isPushout n)
    (triple_realization_isPushout n)
    (realization_pushout ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n))
    (realization_pushout (attach ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n)
      (Nat.lt_succ_self n)) n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n))
  · exact congrArg realization.map (appendTwoTail_first n T)
  · exact congrArg realization.map (appendTwoTail_middle n T)
  · exact congrArg realization.map (appendTwoTail_last n T)

abbrev appendThree (S : Shape) (n b : ℕ) (hl : b < S.1) (hb : b < n) : Shape :=
  appendTwo n (Table.attach S.2 b (n+1) hl (by omega))

noncomputable def appendThreeOld (S : Shape) (n b : ℕ) (hl : b < S.1) (hb : b < n) :
    S ⟶ appendThree S n b hl hb :=
  S.inl b (n+1) hl (by omega) ≫ appendTwoOld n _

noncomputable def appendThreeTail (S : Shape) (n b : ℕ) (hl : b < S.1) (hb : b < n) :
    tripleShape n ⟶ appendThree S n b hl hb := appendTwoTail n _

theorem appendThree_realization_isPushout (S : Shape) (n b : ℕ)
    (hl : b < S.1) (hb : b < n) :
    IsPushout (realization.map (S.seam hl))
      (realization.map (face (by omega : b < n+1) false ≫ tripleFirst n))
      (realization.map (appendThreeOld S n b hl hb))
      (realization.map (appendThreeTail S n b hl hb)) := by
  have h₂ := appendTwo_realization_isPushout n (Table.attach S.2 b (n+1) hl (by omega))
  change IsPushout (realization.map (S.inr b (n+1) hl (by omega))) _ _ _ at h₂
  exact (realization_pushout S b (n+1) hl (by omega)).paste_vert h₂

theorem linearBlock_gt (n b k : ℕ) (hb : b < n) (hk : b < k) :
    b < (linearBlock n k).1 := by
  by_cases h : k < n
  · rw [linearBlock_low n k h]
    exact hk
  · by_cases h' : k = n
    · rw [linearBlock_center n k h']
      exact Nat.lt_trans hb (Nat.lt_succ_self n)
    · rw [linearBlock_high n k (by omega)]
      exact Nat.lt_trans hb (Nat.lt_succ_self n)

theorem face_lastArrow_transport {b : ℕ} {S T : Shape} (e : S = T)
    (hs : b < S.1) (ht : b < T.1) (ε : Bool) :
    face hs ε ≫ lastArrow S = face ht ε ≫ lastArrow T ≫ eqToHom e.symm := by
  subst T
  simp only [eqToHom_refl, Category.comp_id]

@[reassoc] theorem linear_face_below (n b k : ℕ) (h : b < k) (hb : b < n)
    (hk : k ≤ n+1) (ε : Bool) :
    realization.map (eqToHom (linearBlock_low n b hb).symm) ≫
      (linearGlobularDiagram n).face h hk ε =
    realization.map (face (linearBlock_gt n b k hb h) ε ≫ lastArrow (linearBlock n k)) := by
  by_cases hl : k < n
  · erw [linear_face_low n b k h hl, ← Functor.map_comp]
    congr 1
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [face_lastArrow_transport (linearBlock_low n k hl) _ h]
    rfl
  · by_cases hc : k = n
    · subst k
      erw [linear_face_center n b h, ← Functor.map_comp]
      congr 1
      simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [face_lastArrow_transport (linearBlock_center n n rfl) _ (by omega : b < n+1)]
      rfl
    · have he : k = n+1 := by omega
      subst k
      erw [linear_face_top_low n b hb, ← Functor.map_comp]
      congr 1
      simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [face_lastArrow_transport (linearBlock_high n (n+1) (by omega)) _
        (show b < (tripleShape n).1 by exact (by omega : b < n+1))]
      rfl

end Shape

noncomputable def pushoutSpanIso {K : Type u} [Category.{v} K]
    {A B D E A' B' D' E' : K} {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ E} {j : D ⟶ E}
    {f' : A' ⟶ B'} {g' : A' ⟶ D'} {i' : B' ⟶ E'} {j' : D' ⟶ E'}
    (p : IsPushout f g i j) (p' : IsPushout f' g' i' j')
    (a : A ≅ A') (b : B ≅ B') (d : D ≅ D')
    (hf : f ≫ b.hom = a.hom ≫ f') (hg : g ≫ d.hom = a.hom ≫ g') : E ≅ E' :=
  (p.of_iso (inl' := b.inv ≫ i) (inr' := d.inv ≫ j) a b d (Iso.refl E) hf hg (by simp) (by simp)).isoIsPushout _ _ p'

@[reassoc (attr := simp)] theorem pushoutSpanIso_inl {K : Type u} [Category.{v} K]
    {A B D E A' B' D' E' : K} {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ E} {j : D ⟶ E}
    {f' : A' ⟶ B'} {g' : A' ⟶ D'} {i' : B' ⟶ E'} {j' : D' ⟶ E'}
    (p : IsPushout f g i j) (p' : IsPushout f' g' i' j')
    (a : A ≅ A') (b : B ≅ B') (d : D ≅ D') (hf) (hg) :
    i ≫ (pushoutSpanIso p p' a b d hf hg).hom = b.hom ≫ i' := by
  have h := (p.of_iso (inl' := b.inv ≫ i) (inr' := d.inv ≫ j) a b d (Iso.refl E) hf hg (by simp) (by simp)).inl_isoIsPushout_hom _ _ p'
  have h' := congrArg (b.hom ≫ ·) h
  simpa only [pushoutSpanIso, ← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h'

@[reassoc (attr := simp)] theorem pushoutSpanIso_inr {K : Type u} [Category.{v} K]
    {A B D E A' B' D' E' : K} {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ E} {j : D ⟶ E}
    {f' : A' ⟶ B'} {g' : A' ⟶ D'} {i' : B' ⟶ E'} {j' : D' ⟶ E'}
    (p : IsPushout f g i j) (p' : IsPushout f' g' i' j')
    (a : A ≅ A') (b : B ≅ B') (d : D ≅ D') (hf) (hg) :
    j ≫ (pushoutSpanIso p p' a b d hf hg).hom = d.hom ≫ j' := by
  have h := (p.of_iso (inl' := b.inv ≫ i) (inr' := d.inv ≫ j) a b d (Iso.refl E) hf hg (by simp) (by simp)).inr_isoIsPushout_hom _ _ p'
  have h' := congrArg (d.hom ≫ ·) h
  simpa only [pushoutSpanIso, ← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h'

instance preservesColimits_linearization (n : ℕ) : PreservesColimits (Shape.linearization n) :=
  CoGlobularObject.preservesColimits_realization _

namespace Table
open Shape GlobularTheory

structure LinearData (n : ℕ) {k : ℕ} (T : Table k) (hk : k ≤ n+1) where
  table : Table (linearBlock n k).1
  iso : (linearization n).obj T.realize ≅ table.realize
  port : realization.map (lastArrow (linearBlock n k)) ≫
    (linearGlobeIso n k hk).inv ≫ (linearization n).map T.lastInclusion ≫ iso.hom =
      table.lastInclusion

namespace LinearData

noncomputable def globe (n k : ℕ) (hk : k ≤ n+1) : LinearData n (Table.globe k) hk where
  table := (linearBlock n k).2
  iso := linearGlobeIso n k hk
  port := by
    change _ ≫ (linearGlobeIso n k hk).inv ≫ (linearization n).map (𝟙 _) ≫
      (linearGlobeIso n k hk).hom = _
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
    rfl

noncomputable def extend {n k : ℕ} {T : Table k} {hk : k ≤ n+1}
    (d : LinearData n T hk) (b h : ℕ) (hl : b < k) (hr : b < h) (hh : h ≤ n+1)
    (R : Table (linearBlock n h).1)
    (i : d.table.realize ⟶ R.realize) (j : (linearBlock n h).realize ⟶ R.realize)
    (p : IsPushout
      ((linearGlobularDiagram n).face hl hk true ≫ (linearGlobeIso n k hk).inv ≫
        (linearization n).map T.lastInclusion ≫ d.iso.hom)
      ((linearGlobularDiagram n).face hr hh false) i j)
    (hj : realization.map (lastArrow (linearBlock n h)) ≫ j = R.lastInclusion) :
    LinearData n (T.attach b h hl hr) hh := by
  let P := (Shape.realization_pushout ⟨k,T⟩ b h hl hr).map (linearization n)
  have hf : (linearization n).map (realization.map (Shape.seam ⟨k,T⟩ hl)) ≫ d.iso.hom =
      (linearGlobeIso n b (by omega)).hom ≫
        (linearGlobularDiagram n).face hl hk true ≫ (linearGlobeIso n k hk).inv ≫
          (linearization n).map T.lastInclusion ≫ d.iso.hom := by
    change (linearization n).map (GlobularPresheaf.face hl true ≫ T.lastInclusion) ≫ _ = _
    rw [CategoryTheory.Functor.map_comp, Category.assoc]
    have e := (linearGlobularDiagram n).globeIso_face hl hk true
    have e' := congrArg (fun z => z ≫ (linearGlobeIso n k hk).inv ≫
      (linearization n).map T.lastInclusion ≫ d.iso.hom) e
    erw [Category.assoc, Iso.hom_inv_id_assoc, Category.assoc] at e'
    exact e'
  have hg : (linearization n).map (realization.map (Shape.face hr false)) ≫
      (linearGlobeIso n h hh).hom = (linearGlobeIso n b (by omega)).hom ≫
        (linearGlobularDiagram n).face hr hh false :=
    (linearGlobularDiagram n).globeIso_face hr hh false
  let e := pushoutSpanIso P p (linearGlobeIso n b (by omega)) d.iso
    (linearGlobeIso n h hh) hf hg
  refine ⟨R, e, ?_⟩
  change _ ≫ (linearGlobeIso n h hh).inv ≫
    (linearization n).map (realization.map (Shape.inr ⟨k,T⟩ b h hl hr)) ≫ e.hom = _
  erw [pushoutSpanIso_inr, Iso.inv_hom_id_assoc]
  exact hj

theorem seam_below {n k : ℕ} {T : Table k} {hk : k ≤ n+1}
    (d : LinearData n T hk) (b : ℕ) (hl : b < k) (hb : b < n) :
    realization.map (eqToHom (linearBlock_low n b hb).symm) ≫
      (linearGlobularDiagram n).face hl hk true ≫ (linearGlobeIso n k hk).inv ≫
        (linearization n).map T.lastInclusion ≫ d.iso.hom =
    realization.map (Shape.seam ⟨(linearBlock n k).1,d.table⟩ (linearBlock_gt n b k hb hl)) := by
  let f : (linearBlock n b).realize ⟶ (linearBlock n k).realize :=
    (linearGlobularDiagram n).face hl hk true
  let m : (linearBlock n k).realize ⟶ d.table.realize :=
    (linearGlobeIso n k hk).inv ≫ (linearization n).map T.lastInclusion ≫ d.iso.hom
  have e : realization.map (eqToHom (linearBlock_low n b hb).symm) ≫ f =
      realization.map (Shape.face (linearBlock_gt n b k hb hl) true) ≫
        realization.map (lastArrow (linearBlock n k)) :=
    (linear_face_below n b k hl hb hk true).trans (realization.map_comp _ _)
  have hp : realization.map (lastArrow (linearBlock n k)) ≫ m = d.table.lastInclusion := d.port
  change realization.map (eqToHom (linearBlock_low n b hb).symm) ≫ f ≫ m = _
  erw [← Category.assoc, e, Category.assoc, hp]
  rfl

end LinearData

private theorem lastArrow_isIso_globe {S : Shape} {k : ℕ} (e : S = Shape.globe k) :
    IsIso (lastArrow S) := by
  subst S
  change IsIso (𝟙 (Shape.globe k))
  infer_instance

theorem linearBlock_lastArrow_isIso (n h : ℕ) (hh : h ≤ n) :
    IsIso (lastArrow (linearBlock n h)) := by
  rcases lt_or_eq_of_le hh with hlt | he
  · exact lastArrow_isIso_globe (linearBlock_low n h hlt)
  · subst h
    exact lastArrow_isIso_globe (linearBlock_center n n rfl)

def reindex {k h : ℕ} (e : k = h) (T : Table k) : Table h := e ▸ T

noncomputable def reindexIso {k h : ℕ} (e : k = h) (T : Table k) :
    (T.reindex e).realize ≅ T.realize := by
  subst h
  exact Iso.refl _

@[reassoc] theorem reindexIso_last {k h : ℕ} (e : k = h) (T : Table k) :
    (T.reindex e).lastInclusion ≫ (T.reindexIso e).hom =
      realization.map (eqToHom (congrArg Shape.globe e.symm)) ≫ T.lastInclusion := by
  subst h
  simp only [reindex, reindexIso, Iso.refl_hom, Category.comp_id, eqToHom_refl,
    CategoryTheory.Functor.map_id]
  exact (Category.id_comp _).symm

@[reassoc] theorem lastArrow_transport {S R : Shape} (e : S = R) :
    realization.map (lastArrow S) ≫ realization.map (eqToHom e) =
      realization.map (eqToHom (congrArg Shape.globe (congrArg Sigma.fst e))) ≫
        realization.map (lastArrow R) := by
  subst R
  simp

namespace LinearData

noncomputable def attachLow {n k : ℕ} {T : Table k} {hk : k ≤ n+1}
    (d : LinearData n T hk) (b h : ℕ) (hl : b < k) (hr : b < h) (hh : h ≤ n) :
    LinearData n (T.attach b h hl hr) (by omega) := by
  let S : Shape := ⟨(linearBlock n k).1,d.table⟩
  have hb : b < n := by omega
  let hl' := linearBlock_gt n b k hb hl
  let hr' := linearBlock_gt n b h hb hr
  let R := Table.attach d.table b (linearBlock n h).1 hl' hr'
  let a := realization.mapIso (eqToIso (linearBlock_low n b hb).symm)
  letI := linearBlock_lastArrow_isIso n h hh
  let r := asIso (realization.map (lastArrow (linearBlock n h)))
  let i := realization.map (Shape.inl S b (linearBlock n h).1 hl' hr')
  let j := r.inv ≫ realization.map (Shape.inr S b (linearBlock n h).1 hl' hr')
  apply d.extend b h hl hr (by omega) R i j
  · apply (Shape.realization_pushout S b (linearBlock n h).1 hl' hr').of_iso
      a (Iso.refl _) r (Iso.refl _)
    · simp only [Iso.refl_hom, Category.comp_id]
      exact (d.seam_below b hl hb).symm
    · have h' := (linear_face_below n b h hr hb (by omega) false).symm
      change realization.map _ = _ at h'
      erw [CategoryTheory.Functor.map_comp] at h'
      exact h'
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · exact (r.hom_inv_id_assoc _).symm
  · change r.hom ≫ r.inv ≫ _ = _
    erw [r.hom_inv_id_assoc]
    rfl

noncomputable def attachHighBelow {n k : ℕ} {T : Table k} {hk : k ≤ n+1}
    (d : LinearData n T hk) (b : ℕ) (hl : b < k) (hb : b < n) :
    LinearData n (T.attach b (n+1) hl (by omega)) le_rfl := by
  let S : Shape := ⟨(linearBlock n k).1,d.table⟩
  let hl' := linearBlock_gt n b k hb hl
  let R := Shape.appendThree S n b hl' hb
  let e : (linearBlock n (n+1)).1 = n+1 :=
    congrArg Sigma.fst (linearBlock_high n (n+1) (by omega))
  let a := realization.mapIso (eqToIso (linearBlock_low n b hb).symm)
  let c := realization.mapIso (eqToIso (linearBlock_high n (n+1) (by omega)).symm)
  let r := R.2.reindexIso e.symm
  let i := realization.map (appendThreeOld S n b hl' hb) ≫ r.inv
  let j := c.inv ≫ realization.map (appendThreeTail S n b hl' hb) ≫ r.inv
  apply d.extend b (n+1) hl (by omega) le_rfl (R.2.reindex e.symm) i j
  · apply (appendThree_realization_isPushout S n b hl' hb).of_iso
      a (Iso.refl _) c r.symm
    · simp only [Iso.refl_hom, Category.comp_id]
      exact (d.seam_below b hl hb).symm
    · have hf := linear_face_top_low n b hb false
      rw [← Category.assoc (face _ false), ← face_triple_first_last n b hb false] at hf
      change _ = realization.map (_ ≫ _ ≫ _) at hf
      erw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hf
      change (linearGlobularDiagram n).face (by omega : b < n+1) le_rfl false =
        a.inv ≫ realization.map (face (by omega : b < n+1) false ≫ tripleFirst n) ≫ c.hom at hf
      erw [hf, Iso.hom_inv_id_assoc]
    · simp only [Iso.refl_hom, Category.id_comp]
      rfl
    · change _ ≫ r.inv = c.hom ≫ c.inv ≫ _ ≫ r.inv
      erw [Iso.hom_inv_id_assoc]
  · apply (cancel_mono r.hom).1
    change (realization.map (lastArrow (linearBlock n (n+1))) ≫ c.inv) ≫
      realization.map (appendThreeTail S n b hl' hb) ≫ r.inv ≫ r.hom = _
    erw [Iso.inv_hom_id, Category.comp_id, reindexIso_last]
    have ht := lastArrow_transport (linearBlock_high n (n+1) (by omega))
    have hz := congrArg (fun z => z ≫ realization.map (appendThreeTail S n b hl' hb)) ht
    change _ = realization.map (eqToHom (congrArg Shape.globe e)) ≫ R.2.lastInclusion
    erw [Category.assoc] at hz
    refine hz.trans ?_
    change (_ ≫ realization.map (tripleLast n)) ≫
      realization.map (appendTwoTail n _) = _
    erw [Category.assoc, ← CategoryTheory.Functor.map_comp, appendTwoTail_last]
    rfl

theorem face_top_normalized (n : ℕ) (ε : Bool) :
    realization.map (eqToHom (linearBlock_center n n rfl).symm) ≫
      (linearGlobularDiagram n).face (Nat.lt_succ_self n) le_rfl ε =
    realization.map (if ε then tripleLast n else tripleFirst n) ≫
      realization.map (eqToHom (linearBlock_high n (n+1) (by omega)).symm) := by
  erw [linear_face_top, ← CategoryTheory.Functor.map_comp]
  congr 1
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  rfl

noncomputable def attachHighCritical {n : ℕ} {T : Table (n+1)}
    (d : LinearData n T le_rfl) :
    LinearData n (T.attach n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)) le_rfl := by
  let eh := linearBlock_high n (n+1) (Nat.lt_succ_self n)
  let e : (linearBlock n (n+1)).1 = n+1 := congrArg Sigma.fst eh
  let U : Table (n+1) := d.table.reindex e
  let o := d.table.reindexIso e
  let R := Shape.appendTwo n U
  let a := realization.mapIso (eqToIso (linearBlock_center n n rfl).symm)
  let c := realization.mapIso (eqToIso eh.symm)
  let r := R.2.reindexIso e.symm
  let i := o.inv ≫ realization.map (appendTwoOld n U) ≫ r.inv
  let j := c.inv ≫ realization.map (appendTwoTail n U) ≫ r.inv
  let m : (linearBlock n (n+1)).realize ⟶ d.table.realize :=
    (linearGlobeIso n (n+1) le_rfl).inv ≫ (linearization n).map T.lastInclusion ≫ d.iso.hom
  apply d.extend n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n) le_rfl
    (R.2.reindex e.symm) i j
  · apply (appendTwo_realization_isPushout n U).of_iso a o c r.symm
    · have hface : a.hom ≫ (linearGlobularDiagram n).face (Nat.lt_succ_self n) le_rfl true =
          realization.map (tripleLast n) ≫ c.hom := face_top_normalized n true
      have ht := lastArrow_transport eh.symm
      have hp : realization.map (lastArrow (linearBlock n (n+1))) ≫ m = d.table.lastInclusion := d.port
      change U.lastInclusion ≫ o.hom = a.hom ≫
        (linearGlobularDiagram n).face (Nat.lt_succ_self n) le_rfl true ≫ m
      erw [← Category.assoc a.hom, hface, Category.assoc]
      have ht' := congrArg (· ≫ m) ht
      change (realization.map (tripleLast n) ≫ c.hom) ≫ m =
        (realization.map (eqToHom (congrArg Shape.globe e.symm)) ≫
          realization.map (lastArrow (linearBlock n (n+1)))) ≫ m at ht'
      erw [Category.assoc, Category.assoc, hp] at ht'
      exact (reindexIso_last e d.table).trans ht'.symm
    · exact (face_top_normalized n false).symm
    · change _ ≫ r.inv = o.hom ≫ o.inv ≫ _ ≫ r.inv
      erw [Iso.hom_inv_id_assoc]
    · change _ ≫ r.inv = c.hom ≫ c.inv ≫ _ ≫ r.inv
      erw [Iso.hom_inv_id_assoc]
  · apply (cancel_mono r.hom).1
    change (realization.map (lastArrow (linearBlock n (n+1))) ≫ c.inv) ≫
      realization.map (appendTwoTail n U) ≫ r.inv ≫ r.hom = _
    erw [Iso.inv_hom_id, Category.comp_id, reindexIso_last]
    have ht := lastArrow_transport eh
    have hz := congrArg (fun z => z ≫ realization.map (appendTwoTail n U)) ht
    change _ = realization.map (eqToHom (congrArg Shape.globe e)) ≫ R.2.lastInclusion
    erw [Category.assoc] at hz
    refine hz.trans ?_
    change (_ ≫ realization.map (tripleLast n)) ≫ realization.map (appendTwoTail n U) = _
    erw [Category.assoc, ← CategoryTheory.Functor.map_comp, appendTwoTail_last]
    rfl

end LinearData

theorem last_le_height {k : ℕ} (T : Table k) : k ≤ T.height := by
  cases T with
  | globe k => exact le_rfl
  | attach T b h hl hr => exact Nat.le_max_right _ _

noncomputable def linearData (n : ℕ) {k : ℕ} (T : Table k)
    (hT : T.height ≤ n+1) : LinearData n T (T.last_le_height.trans hT) := by
  induction T with
  | globe k => exact LinearData.globe n k hT
  | @attach k T b h hl hr ih =>
    have hprev : T.height ≤ n+1 := (Nat.le_max_left _ _).trans hT
    have hh : h ≤ n+1 := (Nat.le_max_right _ _).trans hT
    let d := ih hprev
    by_cases hlo : h ≤ n
    · exact d.attachLow b h hl hr hlo
    · have eh : h = n+1 := by omega
      subst h
      by_cases hb : b < n
      · exact d.attachHighBelow b hl hb
      · have eb : b = n := by omega
        have ek : k = n+1 := by have := T.last_le_height.trans hprev; omega
        subst b k
        exact d.attachHighCritical

end Table
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularPresheaf

noncomputable def densityDesc {K : Type u} [Category.{v} K]
    (F : GlobularPresheaf.{0} ⥤ K) [PreservesColimitsOfSize.{0,0} F]
    (S : GlobularPresheaf.{0}) (Y : K)
    (d : ∀ (k : Globe), S.obj (op k) → (F.obj (uliftYoneda.obj k) ⟶ Y))
    (hd : ∀ {k l : Globe} (f : k ⟶ l) x,
      F.map (uliftYoneda.map f) ≫ d l x = d k (S.map f.op x)) : F.obj S ⟶ Y :=
  (isColimitOfPreserves F (Presheaf.colimitOfRepresentable S)).desc
    { pt := Y
      ι :=
        { app x := d x.unop.1.unop x.unop.2
          naturality x y f := by
            dsimp
            erw [Category.comp_id]
            exact (hd f.unop.1.unop y.unop.2).trans (congrArg (d x.unop.1.unop) f.unop.2) } }

@[reassoc (attr := simp)] theorem densityDesc_cell {K : Type u} [Category.{v} K]
    (F : GlobularPresheaf.{0} ⥤ K) [PreservesColimitsOfSize.{0,0} F]
    (S : GlobularPresheaf.{0}) (Y : K) (d) (hd) (k : Globe) (x : S.obj (op k)) :
    F.map (uliftYonedaEquiv.symm x) ≫ densityDesc F S Y d hd = d k x := by
  exact (isColimitOfPreserves F (Presheaf.colimitOfRepresentable S)).fac _
    (op (Functor.elementsMk S (op k) x))

theorem density_hom_ext {K : Type u} [Category.{v} K]
    (F : GlobularPresheaf.{0} ⥤ K) [PreservesColimitsOfSize.{0,0} F]
    {S : GlobularPresheaf.{0}} {Y : K} {f g : F.obj S ⟶ Y}
    (h : ∀ (k : Globe) (x : S.obj (op k)),
      F.map (uliftYonedaEquiv.symm x) ≫ f = F.map (uliftYonedaEquiv.symm x) ≫ g) : f = g := by
  apply (isColimitOfPreserves F (Presheaf.colimitOfRepresentable S)).hom_ext
  intro x
  exact h x.unop.1.unop x.unop.2

noncomputable def liftSmall : GlobularPresheaf.{0} ⥤ GlobularPresheaf.{v} :=
  (Functor.whiskeringRight Globeᵒᵖ (Type) (Type v)).obj uliftFunctor.{v,0}

instance liftSmall_preservesColimits : PreservesColimitsOfSize.{0,0} (liftSmall.{v}) := by
  unfold liftSmall
  infer_instance

end GlobularPresheaf

namespace GlobularTheory.Model

noncomputable def smallFree {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q : ℕ) :
    GlobularPresheaf.{0} ⥤ CutoffModels C q :=
  GlobularPresheaf.liftSmall.{v} ⋙ cutoffFreeGlobular hC q

instance smallFree_preservesColimits {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q : ℕ) :
    PreservesColimitsOfSize.{0,0} (smallFree hC q) := by
  let : PreservesColimitsOfSize.{0,0} (cutoffFreeGlobular hC q) :=
    preservesColimitsOfSize_shrink _
  unfold smallFree
  infer_instance

noncomputable def cutoffShapeEquiv {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : Shape) (Y : CutoffModels C q) :
    ((cutoffFunctor hC q).obj (freeShape C S) ⟶ Y) ≃
      (GlobularPresheaf.liftSmall.obj S.realize ⟶ (cutoffForgetGlobular C q).obj Y) :=
  ((cutoffAdjunction hC q).homEquiv _ Y).trans (shapeGlobularEquiv S Y.obj)

@[reassoc] theorem cutoffShapeEquiv_naturality {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : Shape) {Y Z : CutoffModels C q}
    (a : (cutoffFunctor hC q).obj (freeShape C S) ⟶ Y) (b : Y ⟶ Z) :
    cutoffShapeEquiv hC q S Z (a ≫ b) =
      cutoffShapeEquiv hC q S Y a ≫ (cutoffForgetGlobular C q).map b := by
  change shapeGlobularEquiv S Z.obj
    ((cutoffAdjunction hC q).homEquiv _ Z (a ≫ b)) =
    shapeGlobularEquiv S Y.obj ((cutoffAdjunction hC q).homEquiv _ Y a) ≫ _
  erw [Adjunction.homEquiv_naturality_right, shapeGlobularEquiv_natural]
  rfl

noncomputable def smallFreeShapeIso {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : Shape) :
    (smallFree hC q).obj S.realize ≅ (cutoffFunctor hC q).obj (freeShape C S) := by
  let U := cutoffForgetGlobular C q
  let A := cutoffGlobularAdjunction hC q
  let P := (cutoffFunctor hC q).obj (freeShape C S)
  let X := GlobularPresheaf.liftSmall.obj S.realize
  let E (Y : CutoffModels C q) := cutoffShapeEquiv hC q S Y
  let f := (A.homEquiv X P).symm (E P (𝟙 P))
  let g := (E ((cutoffFreeGlobular hC q).obj X)).symm (A.unit.app X)
  have hf : A.homEquiv X P f = E P (𝟙 P) := (A.homEquiv X P).apply_symm_apply _
  have hg : E ((cutoffFreeGlobular hC q).obj X) g = A.unit.app X := (E _).apply_symm_apply _
  refine ⟨f, g, ?_, ?_⟩
  · apply (A.homEquiv X _).injective
    erw [Adjunction.homEquiv_naturality_right, hf, Adjunction.homEquiv_id]
    change E P (𝟙 P) ≫ U.map g = _
    erw [← cutoffShapeEquiv_naturality]
    erw [Category.id_comp]
    exact hg
  · apply (E P).injective
    change E P (g ≫ f) = E P (𝟙 P)
    erw [cutoffShapeEquiv_naturality, hg]
    exact hf

theorem smallFree_cofibrant {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : GlobularPresheaf.{0}) : Cofibrant hC q ((smallFree hC q).obj S) :=
  cutoffFreeGlobular_cofibrant hC q _

noncomputable def smallFreeGen {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell k) :
    ((smallFree hC q).obj S).obj.underlying.Cell k :=
  (GlobularPresheaf.underlyingMap
    ((cutoffGlobularAdjunction hC q).unit.app (GlobularPresheaf.liftSmall.obj S))).app k
      (ULift.up x)

noncomputable def smallFreeDesc {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : GlobularSet.Hom (GlobularPresheaf.liftSmall.obj S).underlying Y.obj.underlying) :
    (smallFree hC q).obj S ⟶ Y :=
  ((cutoffGlobularAdjunction hC q).homEquiv _ Y).symm
    ((GlobularPresheaf.liftSmall.obj S).underlyingPresheafIso.inv ≫
      f.presheafMap ≫ ((cutoffForgetGlobular C q).obj Y).underlyingPresheafIso.hom)

@[simp] theorem smallFreeDesc_gen {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : GlobularSet.Hom (GlobularPresheaf.liftSmall.obj S).underlying Y.obj.underlying)
    (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap (smallFreeDesc hC q f).hom).app k (smallFreeGen hC q S k x) =
      f.app k (ULift.up x) := by
  have h := ((cutoffGlobularAdjunction hC q).homEquiv _ Y).apply_symm_apply
    ((GlobularPresheaf.liftSmall.obj S).underlyingPresheafIso.inv ≫
      f.presheafMap ≫ ((cutoffForgetGlobular C q).obj Y).underlyingPresheafIso.hom)
  exact congrFun (congrArg (fun z => (GlobularPresheaf.underlyingMap z).app k) h) (ULift.up x)

@[simp] theorem smallFreeGen_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell (k+1)) :
    ((smallFree hC q).obj S).obj.underlying.source k (smallFreeGen hC q S (k+1) x) =
      smallFreeGen hC q S k (S.underlying.source k x) := by
  exact (GlobularPresheaf.underlyingMap
    ((cutoffGlobularAdjunction hC q).unit.app (GlobularPresheaf.liftSmall.obj S))).source_app k
      (ULift.up x) |>.symm

@[simp] theorem smallFreeGen_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell (k+1)) :
    ((smallFree hC q).obj S).obj.underlying.target k (smallFreeGen hC q S (k+1) x) =
      smallFreeGen hC q S k (S.underlying.target k x) := by
  exact (GlobularPresheaf.underlyingMap
    ((cutoffGlobularAdjunction hC q).unit.app (GlobularPresheaf.liftSmall.obj S))).target_app k
      (ULift.up x) |>.symm

@[simp] theorem smallFreeGen_map {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap ((smallFree hC q).map f).hom).app k (smallFreeGen hC q S k x) =
      smallFreeGen hC q T k ((GlobularPresheaf.underlyingMap f).app k x) := by
  have h := (cutoffGlobularAdjunction hC q).unit.naturality
    (GlobularPresheaf.liftSmall.map f)
  exact (congrFun (congrArg (fun z => (GlobularPresheaf.underlyingMap z).app k) h)
    (ULift.up x)).symm

end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model

theorem smallFree_hom_ext {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    {f g : (smallFree hC q).obj S ⟶ Y}
    (h : ∀ k x, (underlyingMap f.hom).app k (smallFreeGen hC q S k x) =
      (underlyingMap g.hom).app k (smallFreeGen hC q S k x)) : f = g := by
  apply ((cutoffGlobularAdjunction hC q).homEquiv _ Y).injective
  apply GlobularPresheaf.underlyingMap_injective
  ext k x
  exact h k x.down

noncomputable def smallShapeDesc {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : Shape) {Y : CutoffModels C q}
    (t : Y.obj.presheaf.obj (op (⟨S⟩ : C.Obj))) : (smallFree hC q).obj S.realize ⟶ Y :=
  ((cutoffGlobularAdjunction hC q).homEquiv _ Y).symm
    (shapeGlobularEquiv S Y.obj (Y.obj.tupleMap S t))

@[simp] theorem smallShapeDesc_gen {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : Shape) {Y : CutoffModels C q}
    (t : Y.obj.presheaf.obj (op (⟨S⟩ : C.Obj))) (k : ℕ) (x : S.realize.underlying.Cell k) :
    (underlyingMap (smallShapeDesc hC q S t).hom).app k (smallFreeGen hC q S.realize k x) =
      Y.obj.eval (C.base (S.cellArrow (op (Globe.mk k)) x)) t := by
  have h := ((cutoffGlobularAdjunction hC q).homEquiv _ Y).apply_symm_apply
    (shapeGlobularEquiv S Y.obj (Y.obj.tupleMap S t))
  have e := congrFun (congrArg (fun z => (GlobularPresheaf.underlyingMap z).app k) h) (ULift.up x)
  change (underlyingMap (smallShapeDesc hC q S t).hom).app k
    (smallFreeGen hC q S.realize k x) =
    ((Y.obj.tuples.evaluation.app (op S)) (yonedaEquiv (Y.obj.tupleMap S t))).app
      (op (Globe.mk k)) (ULift.up x) at e
  have ht : yonedaEquiv (Y.obj.tupleMap S t) = t := yonedaEquiv.apply_symm_apply t
  erw [ht] at e
  exact e

@[reassoc] theorem smallShapeDesc_naturality {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S T : Shape} (f : S ⟶ T) {Y : CutoffModels C q}
    (t : Y.obj.presheaf.obj (op (⟨T⟩ : C.Obj))) :
    (smallFree hC q).map (Shape.realization.map f) ≫ smallShapeDesc hC q T t =
      smallShapeDesc hC q S (Y.obj.eval (C.base f) t) := by
  apply smallFree_hom_ext hC q
  intro k x
  change (underlyingMap (smallShapeDesc hC q T t).hom).app k
    ((underlyingMap ((smallFree hC q).map (Shape.realization.map f)).hom).app k
      (smallFreeGen hC q S.realize k x)) = _
  erw [smallFreeGen_map, smallShapeDesc_gen, smallShapeDesc_gen]
  change Y.obj.eval (C.base (T.cellArrow _ (f.app _ x))) t = _
  erw [Shape.cellArrow_naturality, C.base_comp, eval_comp]

noncomputable def smallDiskDesc {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q k : ℕ) {Y : CutoffModels C q} (x : Y.obj.underlying.Cell k) :
    (smallFree hC q).obj (GlobularPresheaf.disk k) ⟶ Y :=
  smallShapeDesc hC q (Shape.globe k) x

@[simp] theorem smallDiskDesc_gen {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q k : ℕ) {Y : CutoffModels C q} (x : Y.obj.underlying.Cell k) :
    (underlyingMap (smallDiskDesc hC q k x).hom).app k
      (smallFreeGen hC q (GlobularPresheaf.disk k) k (ULift.up (𝟙 (Globe.mk k)))) = x := by
  unfold smallDiskDesc
  erw [smallShapeDesc_gen, Shape.cellArrow_identity, C.base_id, eval_id]

theorem smallShape_hasFillers {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : Shape) : ((smallFree hC q).obj S.realize).obj.underlying.HasFillers := by
  let e := smallFreeShapeIso hC q S
  apply (cutoff_freeShape_hasFillers C hC S q).retract
    (underlyingMap e.hom.hom) (underlyingMap e.inv.hom)
  exact congrArg (fun z => underlyingMap z.hom) e.hom_inv_id

theorem linearFree_hasFillers {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : Shape) (hS : S.2.height ≤ n+1) :
    ((smallFree hC q).obj ((Shape.linearization n).obj S.realize)).obj.underlying.HasFillers := by
  let d := S.2.linearData n hS
  let e := (smallFree hC q).mapIso d.iso
  apply (smallShape_hasFillers hC q ⟨_,d.table⟩).retract
    (underlyingMap e.hom.hom) (underlyingMap e.inv.hom)
  exact congrArg (fun z => underlyingMap z.hom) e.hom_inv_id

end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace FiniteCoGlobularObject
variable {K : Type u} [Category.{v} K] [HasTerminal K] {q : ℕ}

noncomputable def cell (B : FiniteCoGlobularObject K q)
    [HasColimitsOfSize.{0,max v w} K] (S : GlobularPresheaf.{max v w})
    (k : ℕ) (hk : k ≤ q) (x : S.underlying.Cell k) : B.obj k hk ⟶ B.realization.obj S :=
  (B.globeIso k hk).inv ≫ B.realization.map (uliftYonedaEquiv.symm x)

@[reassoc] theorem cell_face (B : FiniteCoGlobularObject K q)
    [HasColimitsOfSize.{0,max v w} K] (S : GlobularPresheaf.{max v w})
    {j k : ℕ} (h : j < k) (hk : k ≤ q) (ε : Bool) (x : S.underlying.Cell k) :
    B.face h hk ε ≫ B.cell S k hk x =
      B.cell S j (h.le.trans hk) (S.map (Globe.face h ε).op x) := by
  have e := B.globeIso_face h hk ε
  have e' : B.face h hk ε ≫ (B.globeIso k hk).inv =
      (B.globeIso j (h.le.trans hk)).inv ≫ B.realization.map (GlobularPresheaf.face h ε) := by
    rw [← Iso.inv_hom_id_assoc (B.globeIso j (h.le.trans hk)) (B.face h hk ε), ← e]
    rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold cell
  erw [← Category.assoc, e', Category.assoc, ← Functor.map_comp]
  congr 2
  exact (uliftYonedaEquiv_symm_map (Globe.face h ε).op x).symm

instance preservesColimits_realization (B : FiniteCoGlobularObject K q)
    [HasColimitsOfSize.{0,max v w} K] : PreservesColimits B.realization := by
  unfold realization
  infer_instance

end FiniteCoGlobularObject
namespace Shape

noncomputable def linearLow (n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ)
    (hk : k < n) (x : S.underlying.Cell k) : GlobularPresheaf.disk k ⟶ (linearization n).obj S :=
  realization.map (eqToHom (linearBlock_low n k hk).symm) ≫
    (linearGlobularDiagram n).cell S k (by omega) x

noncomputable def linearEdge (n : ℕ) (S : GlobularPresheaf.{0})
    (x : S.underlying.Cell n) : GlobularPresheaf.disk (n+1) ⟶ (linearization n).obj S :=
  realization.map (eqToHom (linearBlock_center n n rfl).symm) ≫
    (linearGlobularDiagram n).cell S n (by omega) x

noncomputable def linearTriple (n : ℕ) (S : GlobularPresheaf.{0})
    (x : S.underlying.Cell (n+1)) : (GlobularTheory.tripleShape n).realize ⟶ (linearization n).obj S :=
  realization.map (eqToHom (linearBlock_high n (n+1) (by omega)).symm) ≫
    (linearGlobularDiagram n).cell S (n+1) le_rfl x

@[reassoc] theorem linearLow_face (n : ℕ) (S : GlobularPresheaf.{0})
    {j k : ℕ} (h : j < k) (hk : k < n) (ε : Bool) (x : S.underlying.Cell k) :
    GlobularPresheaf.face h ε ≫ linearLow n S k hk x =
      linearLow n S j (by omega) (S.map (Globe.face h ε).op x) := by
  have e := (linearGlobularDiagram n).cell_face S h (by omega) ε x
  rw [linear_face_low n j k h hk ε] at e
  have e' := congrArg (realization.map (eqToHom (linearBlock_low n j (by omega)).symm) ≫ ·) e
  change _ = linearLow n S j (h.trans hk) _ at e'
  erw [← Category.assoc, ← Functor.map_comp] at e'
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at e'
  erw [Functor.map_comp, Category.assoc] at e'
  exact e'

@[reassoc] theorem linearEdge_face (n : ℕ) (S : GlobularPresheaf.{0})
    {j : ℕ} (h : j < n) (ε : Bool) (x : S.underlying.Cell n) :
    GlobularPresheaf.face (by omega : j < n+1) ε ≫ linearEdge n S x =
      linearLow n S j h (S.map (Globe.face h ε).op x) := by
  have e := (linearGlobularDiagram n).cell_face S h (by omega) ε x
  rw [linear_face_center n j h ε] at e
  have e' := congrArg (realization.map (eqToHom (linearBlock_low n j h).symm) ≫ ·) e
  change _ = linearLow n S j h _ at e'
  erw [← Category.assoc, ← Functor.map_comp] at e'
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at e'
  erw [Functor.map_comp, Category.assoc] at e'
  exact e'

@[reassoc] theorem linearTriple_face (n : ℕ) (S : GlobularPresheaf.{0})
    (ε : Bool) (x : S.underlying.Cell (n+1)) :
    realization.map (if ε then GlobularTheory.tripleLast n else GlobularTheory.tripleFirst n) ≫
      linearTriple n S x =
      linearEdge n S (S.map (Globe.face (Nat.lt_succ_self n) ε).op x) := by
  have e := (linearGlobularDiagram n).cell_face S (Nat.lt_succ_self n) le_rfl ε x
  rw [linear_face_top n ε] at e
  have e' := congrArg (realization.map (eqToHom (linearBlock_center n n rfl).symm) ≫ ·) e
  change _ = linearEdge n S _ at e'
  erw [← Category.assoc, ← Functor.map_comp] at e'
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at e'
  erw [Functor.map_comp, Category.assoc] at e'
  exact e'

end Shape
namespace GlobularTheory.Model

noncomputable def smallFreeCell {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} (k : ℕ) (f : GlobularPresheaf.disk k ⟶ S) :
    ((smallFree hC q).obj S).obj.underlying.Cell k :=
  smallFreeGen hC q S k (f.app (op (Globe.mk k)) (ULift.up (𝟙 (Globe.mk k))))

@[simp] theorem smallFreeCell_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} (k : ℕ) (f : GlobularPresheaf.disk (k+1) ⟶ S) :
    ((smallFree hC q).obj S).obj.underlying.source k (smallFreeCell hC q (k+1) f) =
      smallFreeCell hC q k (GlobularPresheaf.face (Nat.lt_succ_self k) false ≫ f) := by
  unfold smallFreeCell
  erw [smallFreeGen_source]
  exact congrArg (smallFreeGen hC q S k)
    ((GlobularPresheaf.underlyingMap f).source_app k (ULift.up (𝟙 (Globe.mk (k+1))))).symm

@[simp] theorem smallFreeCell_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} (k : ℕ) (f : GlobularPresheaf.disk (k+1) ⟶ S) :
    ((smallFree hC q).obj S).obj.underlying.target k (smallFreeCell hC q (k+1) f) =
      smallFreeCell hC q k (GlobularPresheaf.face (Nat.lt_succ_self k) true ≫ f) := by
  unfold smallFreeCell
  erw [smallFreeGen_target]
  exact congrArg (smallFreeGen hC q S k)
    ((GlobularPresheaf.underlyingMap f).target_app k (ULift.up (𝟙 (Globe.mk (k+1))))).symm

@[simp] theorem smallFreeCell_map {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) (k : ℕ)
    (a : GlobularPresheaf.disk k ⟶ S) :
    (underlyingMap ((smallFree hC q).map f).hom).app k (smallFreeCell hC q k a) =
      smallFreeCell hC q k (a ≫ f) :=
  smallFreeGen_map hC q f k _

@[simp] theorem smallShapeDesc_cell {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) (S : Shape) {Y : CutoffModels C q}
    (t : Y.obj.presheaf.obj (op (⟨S⟩ : C.Obj))) (k : ℕ) (f : Shape.globe k ⟶ S) :
    (underlyingMap (smallShapeDesc hC q S t).hom).app k
      (smallFreeCell hC q k (Shape.realization.map f)) = Y.obj.eval (C.base f) t := by
  unfold smallFreeCell
  erw [smallShapeDesc_gen]
  have e : S.cellArrow (op (Globe.mk k)) (f.app (op (Globe.mk k))
      (ULift.up (𝟙 (Globe.mk k)))) = f := uliftYonedaEquiv.symm_apply_apply f
  erw [e]

end GlobularTheory.Model

namespace GlobularPresheaf

noncomputable def finiteRealizationDesc {K : Type u} [Category.{v} K]
    (F : GlobularPresheaf.{0} ⥤ K) [PreservesColimitsOfSize.{0,0} F]
    {q : ℕ} (B : FiniteCoGlobularObject GlobularPresheaf.{0} q)
    (S : GlobularPresheaf.{0}) (hS : ∀ k, q < k → IsEmpty (S.underlying.Cell k)) (Y : K)
    (d : ∀ k (hk : k ≤ q), S.underlying.Cell k → (F.obj (B.obj k hk) ⟶ Y))
    (hd : ∀ {j k : ℕ} (h : j < k) (hk : k ≤ q) (ε : Bool) x,
      F.map (B.face h hk ε) ≫ d k hk x = d j (h.le.trans hk) (S.map (Globe.face h ε).op x)) :
    F.obj (B.realization.obj S) ⟶ Y := by
  let D (k : Globe) (x : S.obj (op k)) : (B.realization ⋙ F).obj (uliftYoneda.obj k) ⟶ Y :=
    if h : k.dim ≤ q then F.map (B.globeIso k.dim h).hom ≫ d k.dim h x
    else (hS k.dim (by omega)).false x |>.elim
  apply densityDesc (B.realization ⋙ F) S Y D
  intro k l f x
  rcases k with ⟨k⟩
  rcases l with ⟨l⟩
  have hl : l ≤ q := by
    by_contra hn
    exact (hS l (by omega)).false x
  change Globe.Face k l at f
  cases f with
  | id =>
    change (B.realization ⋙ F).map (uliftYoneda.map (𝟙 (Globe.mk k))) ≫ D _ x = _
    change _ = D _ (S.map (𝟙 (op (Globe.mk k))) x)
    erw [uliftYoneda.map_id, (B.realization ⋙ F).map_id, Category.id_comp, S.map_id]
    rfl
  | face h ε =>
    have hk := h.le.trans hl
    dsimp only [D]
    rw [dite_eq_left hl, dite_eq_left hk]
    change F.map (B.realization.map (GlobularPresheaf.face h ε)) ≫
      F.map (B.globeIso l hl).hom ≫ d l hl x = _
    erw [← Category.assoc, ← F.map_comp, B.globeIso_face, F.map_comp, Category.assoc, hd]
    rfl

@[reassoc] theorem finiteRealizationDesc_cell {K : Type u} [Category.{v} K]
    (F : GlobularPresheaf.{0} ⥤ K) [PreservesColimitsOfSize.{0,0} F]
    {q : ℕ} (B : FiniteCoGlobularObject GlobularPresheaf.{0} q)
    (S : GlobularPresheaf.{0}) (hS : ∀ k, q < k → IsEmpty (S.underlying.Cell k)) (Y : K)
    (d) (hd) (k : ℕ) (hk : k ≤ q) (x : S.underlying.Cell k) :
    F.map (B.cell S k hk x) ≫ finiteRealizationDesc F B S hS Y d hd = d k hk x := by
  unfold finiteRealizationDesc FiniteCoGlobularObject.cell
  rw [F.map_comp, Category.assoc]
  dsimp only
  erw [densityDesc_cell (B.realization ⋙ F)]
  dsimp only
  erw [dite_eq_left hk, ← Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.id_comp]

end GlobularPresheaf

namespace FiniteCoGlobularObject

theorem face_natural {K : Type u} [Category.{v} K]
    (F : GlobularPresheaf.{0} ⥤ K) {q : ℕ}
    (B : FiniteCoGlobularObject GlobularPresheaf.{0} q)
    (S : GlobularPresheaf.{0}) (Y : K)
    (d : ∀ k (hk : k ≤ q), S.underlying.Cell k → (F.obj (B.obj k hk) ⟶ Y))
    (hd : ∀ k (hk : k+1 ≤ q) (ε : Bool) x,
      F.map (if ε then B.target k hk else B.source k hk) ≫ d (k+1) hk x =
        d k (by omega) (S.map (Globe.face (Nat.lt_succ_self k) ε).op x)) :
    ∀ {j k : ℕ} (h : j < k) (hk : k ≤ q) (ε : Bool) x,
      F.map (B.face h hk ε) ≫ d k hk x =
        d j (h.le.trans hk) (S.map (Globe.face h ε).op x) := by
  intro j k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro h hk ε x
    by_cases e : j = k
    · subst j
      rw [B.face_succ]
      exact hd k hk ε x
    · have hj : j < k := by omega
      erw [← B.face_adjacent hj hk ε false, F.map_comp, Category.assoc, hd, ih hj]
      congr 1
      have e := S.map_comp (Globe.face (Nat.lt_succ_self k) false).op (Globe.face hj ε).op
      exact (ConcreteCategory.congr_hom e x).symm

end FiniteCoGlobularObject

end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model

noncomputable def smallFreeDescCells {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : ∀ k, S.underlying.Cell k → Y.obj.underlying.Cell k)
    (hs : ∀ k x, f k (S.underlying.source k x) = Y.obj.underlying.source k (f (k+1) x))
    (ht : ∀ k x, f k (S.underlying.target k x) = Y.obj.underlying.target k (f (k+1) x)) :
    (smallFree hC q).obj S ⟶ Y :=
  smallFreeDesc hC q
    { app := fun k x => f k x.down
      source_app := fun k x => hs k x.down
      target_app := fun k x => ht k x.down }

@[simp] theorem smallFreeDescCells_gen {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f) (hs) (ht) (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap (smallFreeDescCells hC q (Y := Y) f hs ht).hom).app k
      (smallFreeGen hC q S k x) = f k x := smallFreeDesc_gen hC q _ _ _

@[simp] theorem smallFreeCell_face {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} {j k : ℕ} (h : j < k) (ε : Bool)
    (f : GlobularPresheaf.disk k ⟶ S) :
    ((smallFree hC q).obj S).obj.eval (C.base (Shape.face h ε)) (smallFreeCell hC q k f) =
      smallFreeCell hC q j (GlobularPresheaf.face h ε ≫ f) := by
  unfold smallFreeCell smallFreeGen
  have e := ((cutoffGlobularAdjunction hC q).unit.app (GlobularPresheaf.liftSmall.obj S)).naturality
    (Globe.face h ε).op
  have e' := ConcreteCategory.congr_hom e
    (show (GlobularPresheaf.liftSmall.{v}.obj S).obj (op (Globe.mk k)) from
      ULift.up (f.app (op (Globe.mk k)) (ULift.up (𝟙 (Globe.mk k)))))
  change ((cutoffGlobularAdjunction hC q).unit.app (GlobularPresheaf.liftSmall.obj S)).app
    (op (Globe.mk j)) (ULift.up (S.map (Globe.face h ε).op
      (f.app (op (Globe.mk k)) (ULift.up (𝟙 (Globe.mk k)))))) =
      ((smallFree hC q).obj S).obj.eval (C.base (Shape.face h ε)) _ at e'
  apply e'.symm.trans
  apply congrArg (((cutoffGlobularAdjunction hC q).unit.app (GlobularPresheaf.liftSmall.obj S)).app
    (op (Globe.mk j)))
  apply congrArg ULift.up
  exact (ConcreteCategory.congr_hom (f.naturality (Globe.face h ε).op)
    (show (GlobularPresheaf.disk k).obj (op (Globe.mk k)) from
      ULift.up (𝟙 (Globe.mk k)))).symm

noncomputable abbrev linearFree {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) :=
  (smallFree hC q).obj ((Shape.linearization n).obj S)

noncomputable def linLow {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (hk : k < n) (x : S.underlying.Cell k) :
    (linearFree hC q n S).obj.underlying.Cell k :=
  smallFreeCell hC q k (Shape.linearLow n S k hk x)

noncomputable def linEdge {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell n) :
    (linearFree hC q n S).obj.underlying.Cell (n+1) :=
  smallFreeCell hC q (n+1) (Shape.linearEdge n S x)

noncomputable def linMiddle {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell (n+1)) :
    (linearFree hC q n S).obj.underlying.Cell (n+1) :=
  smallFreeCell hC q (n+1) (Shape.realization.map (tripleMiddle n) ≫ Shape.linearTriple n S x)

@[simp] theorem linMiddle_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell (n+1)) :
    (linearFree hC q n S).obj.underlying.source n (linMiddle hC q n S x) =
      (linearFree hC q n S).obj.underlying.target n (linEdge hC q n S (S.underlying.source n x)) := by
  unfold linMiddle linEdge
  erw [smallFreeCell_source, smallFreeCell_target]
  apply congrArg (smallFreeCell hC q n)
  have e : GlobularPresheaf.face (Nat.lt_succ_self n) true ≫ Shape.realization.map (tripleFirst n) =
    GlobularPresheaf.face (Nat.lt_succ_self n) false ≫ Shape.realization.map (tripleMiddle n) :=
    triple_first_middle n
  calc
    _ = (GlobularPresheaf.face (Nat.lt_succ_self n) false ≫
      Shape.realization.map (tripleMiddle n)) ≫ Shape.linearTriple n S x :=
        (Category.assoc _ _ _).symm
    _ = (GlobularPresheaf.face (Nat.lt_succ_self n) true ≫
      Shape.realization.map (tripleFirst n)) ≫ Shape.linearTriple n S x :=
        congrArg (· ≫ Shape.linearTriple n S x) e.symm
    _ = _ := by
      erw [Category.assoc, Shape.linearTriple_face n S false x]
      rfl

@[simp] theorem linMiddle_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell (n+1)) :
    (linearFree hC q n S).obj.underlying.target n (linMiddle hC q n S x) =
      (linearFree hC q n S).obj.underlying.source n (linEdge hC q n S (S.underlying.target n x)) := by
  unfold linMiddle linEdge
  erw [smallFreeCell_target, smallFreeCell_source]
  apply congrArg (smallFreeCell hC q n)
  have e : GlobularPresheaf.face (Nat.lt_succ_self n) true ≫ Shape.realization.map (tripleMiddle n) =
    GlobularPresheaf.face (Nat.lt_succ_self n) false ≫ Shape.realization.map (tripleLast n) :=
    triple_middle_last n
  calc
    _ = (GlobularPresheaf.face (Nat.lt_succ_self n) true ≫
      Shape.realization.map (tripleMiddle n)) ≫ Shape.linearTriple n S x :=
        (Category.assoc _ _ _).symm
    _ = (GlobularPresheaf.face (Nat.lt_succ_self n) false ≫
      Shape.realization.map (tripleLast n)) ≫ Shape.linearTriple n S x :=
        congrArg (· ≫ Shape.linearTriple n S x) e
    _ = _ := by
      erw [Category.assoc, Shape.linearTriple_face n S true x]
      rfl

@[simp] theorem linLow_face {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) {j k : ℕ} (h : j < k) (hk : k < n)
    (ε : Bool) (x : S.underlying.Cell k) :
    (linearFree hC q n S).obj.eval (C.base (Shape.face h ε)) (linLow hC q n S k hk x) =
      linLow hC q n S j (h.trans hk) (S.map (Globe.face h ε).op x) := by
  unfold linLow
  erw [smallFreeCell_face, Shape.linearLow_face]

@[simp] theorem linEdge_face {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) {j : ℕ} (h : j < n)
    (ε : Bool) (x : S.underlying.Cell n) :
    (linearFree hC q n S).obj.eval (C.base (Shape.face (by omega : j < n+1) ε))
      (linEdge hC q n S x) = linLow hC q n S j h (S.map (Globe.face h ε).op x) := by
  unfold linEdge linLow
  erw [smallFreeCell_face, Shape.linearEdge_face]

noncomputable def linOriginal {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0})
    (hS : ∀ k, n+1 < k → IsEmpty (S.underlying.Cell k))
    (k : ℕ) (x : S.underlying.Cell k) : (linearFree hC q n S).obj.underlying.Cell k := by
  by_cases h : k < n
  · exact linLow hC q n S k h x
  · by_cases e : k = n
    · subst k
      exact (linearFree hC q n S).obj.underlying.source n (linEdge hC q n S x)
    · have ek : k = n+1 := by
        by_contra hn
        exact (hS k (by omega)).false x
      subst k
      exact (linearFree hC q n S).obj.compCell hC n
        (linEdge hC q n S (S.underlying.source n x)) (linMiddle hC q n S x)
        (linMiddle_source hC q n S x).symm

@[simp] theorem linOriginal_low {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (k : ℕ) (hk : k < n)
    (x : S.underlying.Cell k) : linOriginal hC q n S hS k x = linLow hC q n S k hk x := by
  unfold linOriginal
  rw [dite_eq_left hk]

@[simp] theorem linOriginal_center {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (x : S.underlying.Cell n) :
    linOriginal hC q n S hS n x =
      (linearFree hC q n S).obj.underlying.source n (linEdge hC q n S x) := by
  unfold linOriginal
  rw [dite_eq_right (lt_irrefl n), dite_eq_left rfl]

@[simp] theorem linOriginal_high {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (x : S.underlying.Cell (n+1)) :
    linOriginal hC q n S hS (n+1) x =
      (linearFree hC q n S).obj.compCell hC n
        (linEdge hC q n S (S.underlying.source n x)) (linMiddle hC q n S x)
        (linMiddle_source hC q n S x).symm := by
  unfold linOriginal
  rw [dite_eq_right (by omega), dite_eq_right (by omega)]

theorem linOriginal_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (k : ℕ) (x : S.underlying.Cell (k+1)) :
    linOriginal hC q n S hS k (S.underlying.source k x) =
      (linearFree hC q n S).obj.underlying.source k (linOriginal hC q n S hS (k+1) x) := by
  have hk : k ≤ n := by
    by_contra h
    exact (hS (k+1) (by omega)).false x
  by_cases he : k = n
  · subst k
    erw [linOriginal_center, linOriginal_high, compCell_source]
  · have hkn : k < n := by omega
    erw [linOriginal_low _ _ _ _ _ _ hkn]
    by_cases e : k+1 = n
    · subst n
      erw [linOriginal_center]
      change _ = (linearFree hC q (k+1) S).obj.eval (C.base (Shape.source k))
        ((linearFree hC q (k+1) S).obj.eval (C.base (Shape.source (k+1))) _)
      erw [← eval_comp, ← C.base_comp]
      erw [← Shape.face_two_source]
      exact (linEdge_face hC q (k+1) S (Nat.lt_succ_self k) false x).symm
    · have h' : k+1 < n := by omega
      erw [linOriginal_low _ _ _ _ _ _ h']
      exact (linLow_face hC q n S (Nat.lt_succ_self k) h' false x).symm

theorem linOriginal_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (k : ℕ) (x : S.underlying.Cell (k+1)) :
    linOriginal hC q n S hS k (S.underlying.target k x) =
      (linearFree hC q n S).obj.underlying.target k (linOriginal hC q n S hS (k+1) x) := by
  have hk : k ≤ n := by
    by_contra h
    exact (hS (k+1) (by omega)).false x
  by_cases he : k = n
  · subst k
    erw [linOriginal_center, linOriginal_high, compCell_target, linMiddle_target]
  · have hkn : k < n := by omega
    erw [linOriginal_low _ _ _ _ _ _ hkn]
    by_cases e : k+1 = n
    · subst n
      erw [linOriginal_center]
      change _ = (linearFree hC q (k+1) S).obj.eval (C.base (Shape.target k))
        ((linearFree hC q (k+1) S).obj.eval (C.base (Shape.source (k+1))) _)
      erw [← eval_comp, ← C.base_comp]
      erw [← Shape.face_two_source]
      exact (linEdge_face hC q (k+1) S (Nat.lt_succ_self k) true x).symm
    · have h' : k+1 < n := by omega
      erw [linOriginal_low _ _ _ _ _ _ h']
      exact (linLow_face hC q n S (Nat.lt_succ_self k) h' true x).symm

noncomputable def whiskerToLinearCell {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0})
    (hS : ∀ k, n+1 < k → IsEmpty (S.underlying.Cell k))
    (k : ℕ) (x : (S.underlying.whisker n false).Cell k) :
    (linearFree hC q n S).obj.underlying.Cell k :=
  match x with
  | .base k x => linOriginal hC q n S hS k x
  | .tip x => (linearFree hC q n S).obj.underlying.target n (linEdge hC q n S x)
  | .edge x => linEdge hC q n S x

theorem whiskerToLinearCell_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (k : ℕ)
    (x : (S.underlying.whisker n false).Cell (k+1)) :
    whiskerToLinearCell hC q n S hS k ((S.underlying.whisker n false).source k x) =
      (linearFree hC q n S).obj.underlying.source k (whiskerToLinearCell hC q n S hS (k+1) x) := by
  cases x with
  | base k x => exact linOriginal_source hC q n S hS k x
  | tip x =>
    change linOriginal hC q (k+1) S hS k (S.underlying.source k x) = _
    rw [linOriginal_source, linOriginal_center]
    exact (linearFree hC q (k+1) S).obj.underlying.source_source k _
  | edge x => exact linOriginal_center hC q n S hS x

theorem whiskerToLinearCell_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (k : ℕ)
    (x : (S.underlying.whisker n false).Cell (k+1)) :
    whiskerToLinearCell hC q n S hS k ((S.underlying.whisker n false).target k x) =
      (linearFree hC q n S).obj.underlying.target k (whiskerToLinearCell hC q n S hS (k+1) x) := by
  cases x with
  | base k x => exact linOriginal_target hC q n S hS k x
  | tip x =>
    change linOriginal hC q (k+1) S hS k (S.underlying.target k x) = _
    rw [linOriginal_target, linOriginal_center]
    exact (linearFree hC q (k+1) S).obj.underlying.target_source k _
  | edge x => rfl

noncomputable abbrev whiskerFree {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) :=
  (smallFree hC q).obj ((GlobularPresheaf.whiskering n false).obj S)

noncomputable def whiskerToLinear {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0})
    (hS : ∀ k, n+1 < k → IsEmpty (S.underlying.Cell k)) : whiskerFree hC q n S ⟶ linearFree hC q n S :=
  smallFreeDescCells hC q (whiskerToLinearCell hC q n S hS)
    (fun k x => by
      have e := (S.underlying.whisker n false).presheafUnderlyingMap.source_app k x
      change ((GlobularPresheaf.whiskering n false).obj S).underlying.source k x =
        (S.underlying.whisker n false).source k x at e
      exact (congrArg (whiskerToLinearCell hC q n S hS k) e).trans
        (whiskerToLinearCell_source hC q n S hS k x))
    (fun k x => by
      have e := (S.underlying.whisker n false).presheafUnderlyingMap.target_app k x
      change ((GlobularPresheaf.whiskering n false).obj S).underlying.target k x =
        (S.underlying.whisker n false).target k x at e
      exact (congrArg (whiskerToLinearCell hC q n S hS k) e).trans
        (whiskerToLinearCell_target hC q n S hS k x))

noncomputable def wBase {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell k) :
    (whiskerFree hC q n S).obj.underlying.Cell k :=
  smallFreeGen hC q ((GlobularPresheaf.whiskering n false).obj S) k (.base k x)

noncomputable def wEdge {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell n) :
    (whiskerFree hC q n S).obj.underlying.Cell (n+1) :=
  smallFreeGen hC q ((GlobularPresheaf.whiskering n false).obj S) (n+1) (.edge x)

@[simp] theorem wBase_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell (k+1)) :
    (whiskerFree hC q n S).obj.underlying.source k (wBase hC q n S (k+1) x) =
      wBase hC q n S k (S.underlying.source k x) := by
  unfold wBase
  erw [smallFreeGen_source]
  congr 1
  exact (S.underlying.whisker n false).presheafUnderlyingMap.source_app _ _

@[simp] theorem wBase_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell (k+1)) :
    (whiskerFree hC q n S).obj.underlying.target k (wBase hC q n S (k+1) x) =
      wBase hC q n S k (S.underlying.target k x) := by
  unfold wBase
  erw [smallFreeGen_target]
  congr 1
  exact (S.underlying.whisker n false).presheafUnderlyingMap.target_app _ _

@[simp] theorem wEdge_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell n) :
    (whiskerFree hC q n S).obj.underlying.source n (wEdge hC q n S x) = wBase hC q n S n x := by
  unfold wEdge wBase
  erw [smallFreeGen_source]
  congr 1
  exact (S.underlying.whisker n false).presheafUnderlyingMap.source_app _ _

noncomputable def wMiddle {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell (n+1)) :
    (whiskerFree hC q n S).obj.underlying.Cell (n+1) :=
  (whiskerFree hC q n S).obj.compCell hC n
    ((whiskerFree hC q n S).obj.inverseCell hC n (wEdge hC q n S (S.underlying.source n x)))
    (wBase hC q n S (n+1) x) (by rw [inverseCell_target, wEdge_source, wBase_source])

@[simp] theorem wMiddle_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell (n+1)) :
    (whiskerFree hC q n S).obj.underlying.source n (wMiddle hC q n S x) =
      (whiskerFree hC q n S).obj.underlying.target n (wEdge hC q n S (S.underlying.source n x)) := by
  unfold wMiddle
  rw [compCell_source, inverseCell_source]

@[simp] theorem wMiddle_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell (n+1)) :
    (whiskerFree hC q n S).obj.underlying.target n (wMiddle hC q n S x) =
      (whiskerFree hC q n S).obj.underlying.source n (wEdge hC q n S (S.underlying.target n x)) := by
  unfold wMiddle
  rw [compCell_target, wBase_target, wEdge_source]

noncomputable def wTriple {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell (n+1)) :
    (whiskerFree hC q n S).obj.presheaf.obj (op (⟨tripleShape n⟩ : C.Obj)) :=
  (whiskerFree hC q n S).obj.tripleTuple n
    (wEdge hC q n S (S.underlying.source n x)) (wMiddle hC q n S x)
    (wEdge hC q n S (S.underlying.target n x))
    (wMiddle_source hC q n S x).symm (wMiddle_target hC q n S x)

noncomputable def linReverseBlock {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (hk : k ≤ n+1)
    (x : S.underlying.Cell k) :
    (smallFree hC q).obj ((Shape.linearGlobularDiagram n).obj k hk) ⟶ whiskerFree hC q n S := by
  by_cases h : k < n
  · exact (smallFree hC q).map (Shape.realization.map (eqToHom (Shape.linearBlock_low n k h))) ≫
      smallDiskDesc hC q k (wBase hC q n S k x)
  · by_cases e : k = n
    · subst k
      exact (smallFree hC q).map (Shape.realization.map (eqToHom (Shape.linearBlock_center n n rfl))) ≫
        smallDiskDesc hC q (n+1) (wEdge hC q n S x)
    · have ek : k = n+1 := by omega
      subst k
      exact (smallFree hC q).map (Shape.realization.map (eqToHom (Shape.linearBlock_high n (n+1) (by omega)))) ≫
        smallShapeDesc hC q (tripleShape n) (wTriple hC q n S x)

@[simp] theorem linReverseBlock_low {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (hk : k ≤ n+1) (h : k < n)
    (x : S.underlying.Cell k) : linReverseBlock hC q n S k hk x =
    (smallFree hC q).map (Shape.realization.map (eqToHom (Shape.linearBlock_low n k h))) ≫
      smallDiskDesc hC q k (wBase hC q n S k x) := by
  unfold linReverseBlock
  rw [dite_eq_left h]
  rfl

@[simp] theorem linReverseBlock_center {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hk : n ≤ n+1) (x : S.underlying.Cell n) :
    linReverseBlock hC q n S n hk x =
    (smallFree hC q).map (Shape.realization.map (eqToHom (Shape.linearBlock_center n n rfl))) ≫
      smallDiskDesc hC q (n+1) (wEdge hC q n S x) := by
  unfold linReverseBlock
  rw [dite_eq_right (lt_irrefl n), dite_eq_left rfl]
  rfl

@[simp] theorem linReverseBlock_high {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hk : n+1 ≤ n+1) (x : S.underlying.Cell (n+1)) :
    linReverseBlock hC q n S (n+1) hk x =
    (smallFree hC q).map (Shape.realization.map (eqToHom (Shape.linearBlock_high n (n+1) (by omega)))) ≫
      smallShapeDesc hC q (tripleShape n) (wTriple hC q n S x) := by
  unfold linReverseBlock
  rw [dite_eq_right (by omega), dite_eq_right (by omega)]
  rfl

theorem transportedShapeDesc {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {A B D E : Shape} (e : A = B) (f : B ⟶ D) (e' : E = D)
    {Y : CutoffModels C q} (t : Y.obj.presheaf.obj (op (⟨D⟩ : C.Obj))) :
    (smallFree hC q).map (Shape.realization.map (eqToHom e ≫ f ≫ eqToHom e'.symm)) ≫
      (smallFree hC q).map (Shape.realization.map (eqToHom e')) ≫ smallShapeDesc hC q D t =
    (smallFree hC q).map (Shape.realization.map (eqToHom e)) ≫
      smallShapeDesc hC q B (Y.obj.eval (C.base f) t) := by
  subst B
  subst E
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  erw [Shape.realization.map_id, (smallFree hC q).map_id, Category.id_comp,
    smallShapeDesc_naturality]
  erw [Shape.realization.map_id, (smallFree hC q).map_id, Category.id_comp]

theorem linReverseBlock_adjacent {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (hk : k+1 ≤ n+1)
    (ε : Bool) (x : S.underlying.Cell (k+1)) :
    (smallFree hC q).map ((Shape.linearGlobularDiagram n).face (Nat.lt_succ_self k) hk ε) ≫
      linReverseBlock hC q n S (k+1) hk x =
      linReverseBlock hC q n S k (by omega) (S.map (Globe.face (Nat.lt_succ_self k) ε).op x) := by
  by_cases e : k = n
  · subst k
    erw [Shape.linear_face_top, linReverseBlock_center, linReverseBlock_high]
    erw [transportedShapeDesc]
    unfold smallDiskDesc
    congr 2
    cases ε <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact tripleTuple_first _ _ _ _ _ _ _
    · exact tripleTuple_last _ _ _ _ _ _ _
  · have h : k < n := by omega
    by_cases e' : k+1 = n
    · subst n
      erw [Shape.linear_face_center, linReverseBlock_low _ _ _ _ _ _ h, linReverseBlock_center]
      unfold smallDiskDesc
      erw [transportedShapeDesc]
      congr 2
      erw [Shape.face_two_source, C.base_comp, eval_comp]
      cases ε
      · exact (congrArg ((whiskerFree hC q (k+1) S).obj.underlying.source k)
          (wEdge_source hC q (k+1) S x)).trans (wBase_source hC q (k+1) S k x)
      · exact (congrArg ((whiskerFree hC q (k+1) S).obj.underlying.target k)
          (wEdge_source hC q (k+1) S x)).trans (wBase_target hC q (k+1) S k x)
    · have h' : k+1 < n := by omega
      erw [Shape.linear_face_low _ _ _ _ h', linReverseBlock_low _ _ _ _ _ _ h',
        linReverseBlock_low _ _ _ _ _ _ h]
      unfold smallDiskDesc
      erw [transportedShapeDesc]
      congr 2
      cases ε
      · exact wBase_source hC q n S k x
      · exact wBase_target hC q n S k x

noncomputable def linearToWhisker {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0})
    (hS : ∀ k, n+1 < k → IsEmpty (S.underlying.Cell k)) : linearFree hC q n S ⟶ whiskerFree hC q n S :=
  GlobularPresheaf.finiteRealizationDesc (smallFree hC q) (Shape.linearGlobularDiagram n)
    S hS (whiskerFree hC q n S) (linReverseBlock hC q n S)
    ((Shape.linearGlobularDiagram n).face_natural (smallFree hC q) S (whiskerFree hC q n S)
      (linReverseBlock hC q n S) (fun k hk ε x => by
        rw [← FiniteCoGlobularObject.face_succ]
        exact linReverseBlock_adjacent hC q n S k hk ε x))

theorem cancelShapeTransport {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {A B : Shape} (e : A = B) {Y : CutoffModels C q}
    (f : (smallFree hC q).obj B.realize ⟶ Y) :
    (smallFree hC q).map (Shape.realization.map (eqToHom e.symm)) ≫
      (smallFree hC q).map (Shape.realization.map (eqToHom e)) ≫ f = f := by
  subst B
  erw [Shape.realization.map_id, (smallFree hC q).map_id, Category.id_comp, Category.id_comp]

@[reassoc] theorem linearToWhisker_lowHom {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (k : ℕ) (hk : k < n)
    (x : S.underlying.Cell k) :
    (smallFree hC q).map (Shape.linearLow n S k hk x) ≫ linearToWhisker hC q n S hS =
      smallDiskDesc hC q k (wBase hC q n S k x) := by
  unfold Shape.linearLow linearToWhisker
  erw [(smallFree hC q).map_comp, Category.assoc, GlobularPresheaf.finiteRealizationDesc_cell]
  erw [linReverseBlock_low _ _ _ _ _ _ hk, cancelShapeTransport]

@[reassoc] theorem linearToWhisker_edgeHom {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (x : S.underlying.Cell n) :
    (smallFree hC q).map (Shape.linearEdge n S x) ≫ linearToWhisker hC q n S hS =
      smallDiskDesc hC q (n+1) (wEdge hC q n S x) := by
  unfold Shape.linearEdge linearToWhisker
  erw [(smallFree hC q).map_comp, Category.assoc, GlobularPresheaf.finiteRealizationDesc_cell]
  erw [linReverseBlock_center, cancelShapeTransport]

@[reassoc] theorem linearToWhisker_tripleHom {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (x : S.underlying.Cell (n+1)) :
    (smallFree hC q).map (Shape.linearTriple n S x) ≫ linearToWhisker hC q n S hS =
      smallShapeDesc hC q (tripleShape n) (wTriple hC q n S x) := by
  unfold Shape.linearTriple linearToWhisker
  erw [(smallFree hC q).map_comp, Category.assoc, GlobularPresheaf.finiteRealizationDesc_cell]
  erw [linReverseBlock_high, cancelShapeTransport]

theorem smallFreeCell_image {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q} (k : ℕ)
    (a : GlobularPresheaf.disk k ⟶ S) (f : (smallFree hC q).obj S ⟶ Y)
    (x : Y.obj.underlying.Cell k) (h : (smallFree hC q).map a ≫ f = smallDiskDesc hC q k x) :
    (underlyingMap f.hom).app k (smallFreeCell hC q k a) = x := by
  have e := congrFun (congrArg (fun z => (underlyingMap z.hom).app k) h)
    (smallFreeGen hC q (GlobularPresheaf.disk k) k (ULift.up (𝟙 (Globe.mk k))))
  change (underlyingMap f.hom).app k
    ((underlyingMap ((smallFree hC q).map a).hom).app k _) = _ at e
  have hm : (underlyingMap ((smallFree hC q).map a).hom).app k
      (smallFreeGen hC q (GlobularPresheaf.disk k) k (ULift.up (𝟙 (Globe.mk k)))) =
      smallFreeCell hC q k a := smallFreeGen_map hC q a k _
  exact ((congrArg (underlyingMap f.hom |>.app k) hm).symm.trans e).trans
    (smallDiskDesc_gen hC q k x)

@[simp] theorem linearToWhisker_low {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (k : ℕ) (hk : k < n) (x : S.underlying.Cell k) :
    (underlyingMap (linearToWhisker hC q n S hS).hom).app k (linLow hC q n S k hk x) =
      wBase hC q n S k x :=
  smallFreeCell_image hC q k _ _ _ (linearToWhisker_lowHom hC q n S hS k hk x)

@[simp] theorem linearToWhisker_edge {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (x : S.underlying.Cell n) :
    (underlyingMap (linearToWhisker hC q n S hS).hom).app (n+1) (linEdge hC q n S x) =
      wEdge hC q n S x :=
  smallFreeCell_image hC q (n+1) _ _ _ (linearToWhisker_edgeHom hC q n S hS x)

@[simp] theorem linearToWhisker_middle {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (x : S.underlying.Cell (n+1)) :
    (underlyingMap (linearToWhisker hC q n S hS).hom).app (n+1) (linMiddle hC q n S x) =
      wMiddle hC q n S x := by
  let a : GlobularPresheaf.disk (n+1) ⟶ (tripleShape n).realize :=
    Shape.realization.map (tripleMiddle n)
  have he : (smallFree hC q).map a ≫ smallShapeDesc hC q (tripleShape n) (wTriple hC q n S x) =
      smallDiskDesc hC q (n+1) (wMiddle hC q n S x) := by
    have e := smallShapeDesc_naturality hC q (tripleMiddle n) (wTriple hC q n S x)
    have ht : (whiskerFree hC q n S).obj.eval (C.base (tripleMiddle n)) (wTriple hC q n S x) =
        wMiddle hC q n S x := tripleTuple_middle _ _ _ _ _ _ _
    exact e.trans (congrArg (smallShapeDesc hC q (Shape.globe (n+1))) ht)
  apply smallFreeCell_image hC q (n+1) (a ≫ Shape.linearTriple n S x)
  calc
    _ = (smallFree hC q).map a ≫
        ((smallFree hC q).map (Shape.linearTriple n S x) ≫ linearToWhisker hC q n S hS) := by
      rw [(smallFree hC q).map_comp, Category.assoc]
    _ = (smallFree hC q).map a ≫ smallShapeDesc hC q (tripleShape n) (wTriple hC q n S x) :=
      congrArg (_ ≫ ·) (linearToWhisker_tripleHom hC q n S hS x)
    _ = _ := he

theorem compCell_cancel_left {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a b : X.underlying.Cell (n+1))
    (h : X.underlying.source n a = X.underlying.source n b) :
    X.underlying.Joined (n+1)
      (X.compCell hC n a
        (X.compCell hC n (X.inverseCell hC n a) b (by rw [inverseCell_target, h]))
        (by rw [compCell_source, inverseCell_source])) b := by
  have hi := X.compCell_assoc hC n a (X.inverseCell hC n a) b
    (X.inverseCell_source hC n a).symm (by rw [inverseCell_target, h])
  apply X.joined_trans hC (X.joined_symm hC hi)
  apply X.joined_trans hC (X.compCell_congr_left hC n
    (X.compCell hC n a (X.inverseCell hC n a) (X.inverseCell_source hC n a).symm)
    (X.unitCell hC n (X.underlying.source n a)) b
    (by rw [compCell_target, inverseCell_target, h])
    (by rw [unitCell_target, h]) (X.compCell_inverse_right hC n a))
  simpa only [h] using X.compCell_left_unit hC n b

@[simp] theorem whiskerToLinear_gen {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (k : ℕ)
    (x : ((GlobularPresheaf.whiskering n false).obj S).underlying.Cell k) :
    (underlyingMap (whiskerToLinear hC q n S hS).hom).app k
      (smallFreeGen hC q ((GlobularPresheaf.whiskering n false).obj S) k x) =
    whiskerToLinearCell hC q n S hS k x := smallFreeDescCells_gen hC q _ _ _ k x

@[simp] theorem wEdge_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell n) :
    (whiskerFree hC q n S).obj.underlying.target n (wEdge hC q n S x) =
      smallFreeGen hC q ((GlobularPresheaf.whiskering n false).obj S) n (.tip x) := by
  unfold wEdge
  erw [smallFreeGen_target]
  congr 1
  exact (S.underlying.whisker n false).presheafUnderlyingMap.target_app _ _

theorem whiskerLinear_low {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (k : ℕ) (hk : k ≤ n)
    (x : ((GlobularPresheaf.whiskering n false).obj S).underlying.Cell k) :
    (underlyingMap (whiskerToLinear hC q n S hS ≫ linearToWhisker hC q n S hS).hom).app k
      (smallFreeGen hC q ((GlobularPresheaf.whiskering n false).obj S) k x) =
      smallFreeGen hC q ((GlobularPresheaf.whiskering n false).obj S) k x := by
  change (underlyingMap (linearToWhisker hC q n S hS).hom).app k
    ((underlyingMap (whiskerToLinear hC q n S hS).hom).app k _) = _
  apply (congrArg ((underlyingMap (linearToWhisker hC q n S hS).hom).app k)
    (whiskerToLinear_gen hC q n S hS k x)).trans
  cases x with
  | base k x =>
    change (underlyingMap (linearToWhisker hC q n S hS).hom).app k
      (linOriginal hC q n S hS k x) = wBase hC q n S k x
    by_cases e : k = n
    · subst k
      erw [linOriginal_center, (underlyingMap (linearToWhisker hC q n S hS).hom).source_app,
        linearToWhisker_edge, wEdge_source]
    · have h : k < n := by omega
      erw [linOriginal_low _ _ _ _ _ _ h, linearToWhisker_low]
  | tip x =>
    change (underlyingMap (linearToWhisker hC q k S hS).hom).app k
      ((linearFree hC q k S).obj.underlying.target k (linEdge hC q k S x)) = _
    erw [(underlyingMap (linearToWhisker hC q k S hS).hom).target_app,
      linearToWhisker_edge, wEdge_target]
  | edge x => exact (Nat.not_succ_le_self n hk).elim

theorem whiskerLinear_top {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS)
    (x : ((GlobularPresheaf.whiskering n false).obj S).underlying.Cell (n+1)) :
    (whiskerFree hC q n S).obj.underlying.Joined (n+1)
      ((underlyingMap (whiskerToLinear hC q n S hS ≫ linearToWhisker hC q n S hS).hom).app (n+1)
        (smallFreeGen hC q ((GlobularPresheaf.whiskering n false).obj S) (n+1) x))
      (smallFreeGen hC q ((GlobularPresheaf.whiskering n false).obj S) (n+1) x) := by
  change (whiskerFree hC q n S).obj.underlying.Joined (n+1)
    ((underlyingMap (linearToWhisker hC q n S hS).hom).app (n+1)
      ((underlyingMap (whiskerToLinear hC q n S hS).hom).app (n+1) _)) _
  have e := congrArg ((underlyingMap (linearToWhisker hC q n S hS).hom).app (n+1))
    (whiskerToLinear_gen hC q n S hS (n+1) x)
  apply (congrArg (fun z => (whiskerFree hC q n S).obj.underlying.Joined (n+1) z
    (smallFreeGen hC q ((GlobularPresheaf.whiskering n false).obj S) (n+1) x)) e).mpr
  cases x with
  | base k x =>
    change (whiskerFree hC q n S).obj.underlying.Joined (n+1)
      ((underlyingMap (linearToWhisker hC q n S hS).hom).app (n+1)
        (linOriginal hC q n S hS (n+1) x)) (wBase hC q n S (n+1) x)
    erw [linOriginal_high]
    simp only [map_compCell, linearToWhisker_edge, linearToWhisker_middle]
    exact (whiskerFree hC q n S).obj.compCell_cancel_left hC n
      (wEdge hC q n S (S.underlying.source n x)) (wBase hC q n S (n+1) x)
      (by rw [wEdge_source, wBase_source])
  | edge x =>
    change (whiskerFree hC q n S).obj.underlying.Joined (n+1)
      ((underlyingMap (linearToWhisker hC q n S hS).hom).app (n+1)
        (linEdge hC q n S x)) (wEdge hC q n S x)
    rw [linearToWhisker_edge]
    exact (whiskerFree hC q n S).obj.joined_refl hC _ _

end GlobularTheory.Model
namespace GlobularPresheaf

theorem disk_bounded (n k : ℕ) (h : n < k) : IsEmpty ((disk n).underlying.Cell k) := by
  constructor
  intro x
  change ULift (Globe.mk k ⟶ Globe.mk n) at x
  rcases x with ⟨x⟩
  change Globe.Face k n at x
  cases x with
  | id => omega
  | face h' ε => omega

end GlobularPresheaf
namespace Table

theorem bounded {l : ℕ} (T : Table l) (k : ℕ) (h : T.height < k) :
    IsEmpty (T.realize.underlying.Cell k) := by
  induction T with
  | globe n => exact GlobularPresheaf.disk_bounded n k h
  | @attach l T b j hl hr ih =>
    have hk : T.height < k := lt_of_le_of_lt (Nat.le_max_left _ _) h
    have hj : j < k := lt_of_le_of_lt (Nat.le_max_right _ _) h
    have H := (Shape.realization_pushout ⟨l,T⟩ b j hl hr).map
      ((evaluation Globeᵒᵖ (Type)).obj (op (Globe.mk k)))
    constructor
    intro x
    obtain ⟨y, _⟩ | ⟨y, _⟩ := Types.eq_or_eq_of_isPushout H x
    · exact (ih hk).false y
    · exact (GlobularPresheaf.disk_bounded j k hj).false y

end Table
namespace GlobularTheory.Model

theorem whiskerFree_bounded_hasFillers {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (H : ExpansionContraction hC q (n+1))
    (S : Shape) (hS : S.height ≤ n+1) : (whiskerFree hC q n S.realize).obj.underlying.HasFillers := by
  have hb (k : ℕ) (hk : n+1 < k) : IsEmpty (S.realize.underlying.Cell k) :=
    S.2.bounded k (lt_of_le_of_lt hS hk)
  apply free_hasFillers_of_top_homotopy hC q n H
    (GlobularPresheaf.liftSmall.obj ((GlobularPresheaf.whiskering n false).obj S.realize))
    (fun k hk => ⟨fun x => (S.realize.underlying.whisker_bounded n false hb k hk).false x.down⟩)
    (linearFree hC q n S.realize) (smallFree_cofibrant hC q _)
    (linearFree_hasFillers hC q n S hS)
    (whiskerToLinear hC q n S.realize hb) (linearToWhisker hC q n S.realize hb)
  · intro k hk x
    exact whiskerLinear_low hC q n S.realize hb k hk x.down
  · intro x
    exact whiskerLinear_top hC q n S.realize hb x.down

end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model

noncomputable def smallWhiskerCell {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y)
    (e : S.underlying.Cell n → Y.obj.underlying.Cell (n+1))
    (k : ℕ) (x : (S.underlying.whisker n false).Cell k) : Y.obj.underlying.Cell k :=
  match x with
  | .base k x => (underlyingMap f.hom).app k (smallFreeGen hC q S k x)
  | .tip x => Y.obj.underlying.target n (e x)
  | .edge x => e x

theorem smallWhiskerCell_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e : S.underlying.Cell n → Y.obj.underlying.Cell (n+1))
    (he : ∀ x, Y.obj.underlying.source n (e x) =
      (underlyingMap f.hom).app n (smallFreeGen hC q S n x))
    (k : ℕ) (x : (S.underlying.whisker n false).Cell (k+1)) :
    smallWhiskerCell hC q n f e k ((S.underlying.whisker n false).source k x) =
      Y.obj.underlying.source k (smallWhiskerCell hC q n f e (k+1) x) := by
  cases x with
  | base k x =>
    change (underlyingMap f.hom).app k (smallFreeGen hC q S k (S.underlying.source k x)) = _
    rw [← smallFreeGen_source, (underlyingMap f.hom).source_app]
    rfl
  | tip x =>
    change (underlyingMap f.hom).app k (smallFreeGen hC q S k (S.underlying.source k x)) = _
    rw [← smallFreeGen_source, (underlyingMap f.hom).source_app, ← he]
    exact Y.obj.underlying.source_source k _
  | edge x => exact (he x).symm

theorem smallWhiskerCell_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e : S.underlying.Cell n → Y.obj.underlying.Cell (n+1))
    (he : ∀ x, Y.obj.underlying.source n (e x) =
      (underlyingMap f.hom).app n (smallFreeGen hC q S n x))
    (k : ℕ) (x : (S.underlying.whisker n false).Cell (k+1)) :
    smallWhiskerCell hC q n f e k ((S.underlying.whisker n false).target k x) =
      Y.obj.underlying.target k (smallWhiskerCell hC q n f e (k+1) x) := by
  cases x with
  | base k x =>
    change (underlyingMap f.hom).app k (smallFreeGen hC q S k (S.underlying.target k x)) = _
    rw [← smallFreeGen_target, (underlyingMap f.hom).target_app]
    rfl
  | tip x =>
    change (underlyingMap f.hom).app k (smallFreeGen hC q S k (S.underlying.target k x)) = _
    rw [← smallFreeGen_target, (underlyingMap f.hom).target_app, ← he]
    exact Y.obj.underlying.target_source k _
  | edge x => rfl

noncomputable def smallWhiskerDesc {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e : S.underlying.Cell n → Y.obj.underlying.Cell (n+1))
    (he : ∀ x, Y.obj.underlying.source n (e x) =
      (underlyingMap f.hom).app n (smallFreeGen hC q S n x)) : whiskerFree hC q n S ⟶ Y :=
  smallFreeDescCells hC q (smallWhiskerCell hC q n f e)
    (fun k x => by
      have h := (S.underlying.whisker n false).presheafUnderlyingMap.source_app k x
      change (S.underlying.whisker n false).presheaf.underlying.source k x =
        (S.underlying.whisker n false).source k x at h
      exact (congrArg (smallWhiskerCell hC q n f e k) h).trans
        (smallWhiskerCell_source hC q n f e he k x))
    (fun k x => by
      have h := (S.underlying.whisker n false).presheafUnderlyingMap.target_app k x
      change (S.underlying.whisker n false).presheaf.underlying.target k x =
        (S.underlying.whisker n false).target k x at h
      exact (congrArg (smallWhiskerCell hC q n f e k) h).trans
        (smallWhiskerCell_target hC q n f e he k x))

@[simp] theorem smallWhiskerDesc_base {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e) (he) (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap (smallWhiskerDesc hC q n f e he).hom).app k (wBase hC q n S k x) =
      (underlyingMap f.hom).app k (smallFreeGen hC q S k x) :=
  smallFreeDescCells_gen hC q _ _ _ k _

@[simp] theorem smallWhiskerDesc_edge {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e) (he) (x : S.underlying.Cell n) :
    (underlyingMap (smallWhiskerDesc hC q n f e he).hom).app (n+1) (wEdge hC q n S x) = e x :=
  smallFreeDescCells_gen hC q _ _ _ (n+1) _

noncomputable def whiskerIn {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) : (smallFree hC q).obj S ⟶ whiskerFree hC q n S :=
  (smallFree hC q).map ((GlobularPresheaf.whiskeringInclusion n false).app S)

@[simp] theorem whiskerIn_gen {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap (whiskerIn hC q n S).hom).app k (smallFreeGen hC q S k x) =
      wBase hC q n S k x := smallFreeGen_map hC q _ k x

theorem smallFree_low_bijective {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) (hrq : r ≤ q) {S T : GlobularPresheaf.{0}} (f : S ⟶ T)
    (hf : ∀ k, k ≤ r → Function.Bijective ((GlobularPresheaf.underlyingMap f).app k)) :
    ∀ k, k ≤ r → Function.Bijective ((underlyingMap ((smallFree hC q).map f).hom).app k) := by
  apply (coskeletalLocalMap_iff hC r _).mp
  intro Z hZ g
  let Z' : CutoffModels C q := ⟨Z, fun j hj => hZ j (lt_of_le_of_lt hrq hj)⟩
  let A := cutoffGlobularAdjunction hC q
  let g' : (smallFree hC q).obj S ⟶ Z' := ObjectProperty.homMk g
  let f' := GlobularPresheaf.liftSmall.map f
  have hf' : ∀ k, k ≤ r → Function.Bijective (f'.app (op (Globe.mk k))) := by
    intro k hk
    exact ULift.map_bijective.mpr (hf k hk)
  have hb := GlobularPresheaf.precomp_bijective_low f' r hf' hZ
  obtain ⟨b, hb'⟩ := hb.2 (A.homEquiv _ Z' g')
  let a := (A.homEquiv _ Z').symm b
  have ha : (smallFree hC q).map f ≫ a = g' := by
    apply (A.homEquiv _ Z').injective
    erw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
    exact hb'
  refine ⟨a.hom, congrArg (fun t => t.hom) ha, ?_⟩
  intro a' ha'
  let a'' : (smallFree hC q).obj T ⟶ Z' := ObjectProperty.homMk a'
  have hh : (smallFree hC q).map f ≫ a'' = g' := by
    apply ObjectProperty.hom_ext
    exact ha'
  have hh' : a'' = a := by
    apply (A.homEquiv _ Z').injective
    apply hb.1
    change f' ≫ A.homEquiv _ Z' a'' = f' ≫ A.homEquiv _ Z' a
    erw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left, hh, ha]
  exact congrArg (fun t => t.hom) hh'

theorem liftsBoundary_of_bijective {X Y : GlobularSet.{u}} (p : GlobularSet.Hom X Y)
    (k : ℕ) (hp : ∀ j, j ≤ k → Function.Bijective (p.app j)) :
    GlobularSet.LiftsBoundary p k := by
  intro bd y hy
  obtain ⟨x, hx⟩ := (hp k le_rfl).2 y
  refine ⟨x, ?_, hx⟩
  apply (p.boundaryMap_bijective_of_low k (fun j hj => hp j hj.le)).1
  rw [p.boundary_app, hx, hy]

theorem exists_upper_resolution {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (hnq : n ≤ q) {X Y : CutoffModels C q} (f : X ⟶ Y)
    (hY : Cofibrant hC q Y) (hXF : X.obj.underlying.HasFillers)
    (hYF : Y.obj.underlying.HasFillers)
    (hf : ∀ k, k ≤ n → Function.Bijective ((underlyingMap f.hom).app k)) :
    ∃ (M : CutoffModels C q) (i : X ⟶ M) (p : M ⟶ Y) (s : Y ⟶ M),
      i ≫ p = f ∧ s ≫ p = 𝟙 Y ∧ (boundaryClass hC q (n+1)).rlp.llp i ∧
      M.obj.underlying.HasFillers ∧
      ∀ k, k ≤ n → Function.Injective ((underlyingMap p.hom).app k) := by
  let := boundaryClass_smallObject hC q (n+1)
  let W := boundaryClass hC q (n+1)
  let F := MorphismProperty.factorizationData W.rlp.llp W.rlp f
  have hi k (hk : k ≤ n) := upper_cofibration_low_bijective hC q (n+1) k
    (hk.trans hnq) (by omega) F.i F.hi
  have hp k (hk : k ≤ n) : Function.Bijective ((underlyingMap F.p.hom).app k) := by
    have fac (x : X.obj.underlying.Cell k) :
        (underlyingMap F.p.hom).app k ((underlyingMap F.i.hom).app k x) =
        (underlyingMap f.hom).app k x :=
      congrFun (congrArg (fun z => (underlyingMap z.hom).app k) F.fac) x
    constructor
    · intro a b hab
      obtain ⟨a', rfl⟩ := (hi k hk).2 a
      obtain ⟨b', rfl⟩ := (hi k hk).2 b
      exact congrArg ((underlyingMap F.i.hom).app k)
        ((hf k hk).1 ((fac a').symm.trans (hab.trans (fac b'))))
    · intro y
      obtain ⟨x, hx⟩ := (hf k hk).2 y
      exact ⟨(underlyingMap F.i.hom).app k x, (fac x).trans hx⟩
  have hMF : F.Z.obj.underlying.HasFillers := by
    apply hXF.of_low_bijective (underlyingMap F.i.hom) n hi
    intro k hk bd
    obtain ⟨y, hy⟩ := hYF k ((underlyingMap F.p.hom).boundaryMap k bd)
    obtain ⟨x, hx, _⟩ := (hasLiftingProperty_I_iff k F.p.hom).1
      ((boundaryClass_rlp_iff hC q (n+1) F.p).1 F.hp k (by omega)) bd y hy
    exact ⟨x, hx⟩
  have hpI : (boundaryClass hC q 0).rlp F.p := by
    rw [boundaryClass_rlp_iff]
    intro k _
    by_cases hk : k ≤ n
    · rw [hasLiftingProperty_I_iff]
      exact liftsBoundary_of_bijective (underlyingMap F.p.hom) k
        (fun j hj => hp j (hj.trans hk))
    · exact (boundaryClass_rlp_iff hC q (n+1) F.p).1 F.hp k (by omega)
  obtain ⟨s, hs⟩ := hY F.p hpI (𝟙 Y)
  exact ⟨F.Z, F.i, F.p, s, F.fac, hs, F.hi, hMF, fun k hk => (hp k hk).1⟩

theorem whiskerFree_hom_ext {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    {f g : whiskerFree hC q n S ⟶ Y}
    (hb : ∀ k x, (underlyingMap f.hom).app k (wBase hC q n S k x) =
      (underlyingMap g.hom).app k (wBase hC q n S k x))
    (he : ∀ x, (underlyingMap f.hom).app (n+1) (wEdge hC q n S x) =
      (underlyingMap g.hom).app (n+1) (wEdge hC q n S x)) : f = g := by
  apply smallFree_hom_ext hC q
  intro k x
  cases x with
  | base k x => exact hb k x
  | edge x => exact he x
  | tip x =>
    rw [← wEdge_target hC q k S x, (underlyingMap f.hom).target_app,
      (underlyingMap g.hom).target_app, he]

noncomputable def whiskerFreeMap {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) :
    whiskerFree hC q n S ⟶ whiskerFree hC q n T :=
  (smallFree hC q).map ((GlobularPresheaf.whiskering n false).map f)

@[simp] theorem whiskerFreeMap_base {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap (whiskerFreeMap hC q n f).hom).app k (wBase hC q n S k x) =
      wBase hC q n T k ((GlobularPresheaf.underlyingMap f).app k x) :=
  smallFreeGen_map hC q _ k _

@[simp] theorem whiskerFreeMap_edge {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) (x : S.underlying.Cell n) :
    (underlyingMap (whiskerFreeMap hC q n f).hom).app (n+1) (wEdge hC q n S x) =
      wEdge hC q n T ((GlobularPresheaf.underlyingMap f).app n x) :=
  smallFreeGen_map hC q _ (n+1) _

@[reassoc] theorem whiskerIn_naturality {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) :
    whiskerIn hC q n S ≫ whiskerFreeMap hC q n f =
      (smallFree hC q).map f ≫ whiskerIn hC q n T := by
  unfold whiskerIn whiskerFreeMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (smallFree hC q).map ((GlobularPresheaf.whiskeringInclusion n false).naturality f).symm

theorem whiskerFree_hasFillers_of_spine {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))
    {S T : GlobularPresheaf.{0}} (f : S ⟶ T)
    (hf : ∀ k, k ≤ n → Function.Bijective ((GlobularPresheaf.underlyingMap f).app k))
    (hS : ((smallFree hC q).obj S).obj.underlying.HasFillers)
    (hT : ((smallFree hC q).obj T).obj.underlying.HasFillers)
    (hW : (whiskerFree hC q n S).obj.underlying.HasFillers) :
    (whiskerFree hC q n T).obj.underlying.HasFillers := by
  let := cutoff_hasColimits hC q
  let F := smallFree hC q
  obtain ⟨M,i,p,s,hip,hsp,hi,hM,hp⟩ := exists_upper_resolution hC q n hnq
    (F.map f) (smallFree_cofibrant hC q T) hS hT
    (smallFree_low_bijective hC q n hnq f hf)
  let a := whiskerIn hC q n S
  let Q := pushout a i
  let j : whiskerFree hC q n S ⟶ Q := pushout.inl a i
  let k : M ⟶ Q := pushout.inr a i
  have hQ : Q.obj.underlying.HasFillers := upper_pushout_hasFillers hC q (n+1) H
    (IsPushout.of_hasPushout a i) hi (smallFree_cofibrant hC q S) hS hM
    (smallFree_cofibrant hC q _) hW
  let wm := whiskerFreeMap hC q n f
  let r : Q ⟶ whiskerFree hC q n T := pushout.desc wm (p ≫ whiskerIn hC q n T) (by
    rw [← Category.assoc, hip]
    exact whiskerIn_naturality hC q n f)
  have hjr : j ≫ r = wm := pushout.inl_desc _ _ _
  have hkr : k ≫ r = p ≫ whiskerIn hC q n T := pushout.inr_desc _ _ _
  let E := Equiv.ofBijective ((GlobularPresheaf.underlyingMap f).app n) (hf n le_rfl)
  have hsgen (x : T.underlying.Cell n) :
      (underlyingMap s.hom).app n (smallFreeGen hC q T n x) =
      (underlyingMap i.hom).app n (smallFreeGen hC q S n (E.symm x)) := by
    apply hp n le_rfl
    have hs := congrFun (congrArg (fun z => (underlyingMap z.hom).app n) hsp)
      (smallFreeGen hC q T n x)
    have hi' := congrFun (congrArg (fun z => (underlyingMap z.hom).app n) hip)
      (smallFreeGen hC q S n (E.symm x))
    exact hs.trans (((smallFreeGen_map hC q f n (E.symm x)).trans
      (congrArg (smallFreeGen hC q T n) (E.apply_symm_apply x))).symm.trans hi'.symm)
  let e (x : T.underlying.Cell n) := (underlyingMap j.hom).app (n+1) (wEdge hC q n S (E.symm x))
  have he (x : T.underlying.Cell n) : Q.obj.underlying.source n (e x) =
      (underlyingMap (s ≫ k).hom).app n (smallFreeGen hC q T n x) := by
    change Q.obj.underlying.source n ((underlyingMap j.hom).app (n+1) _) =
      (underlyingMap k.hom).app n ((underlyingMap s.hom).app n _)
    rw [← (underlyingMap j.hom).source_app, wEdge_source, hsgen]
    have hh := congrFun (congrArg (fun z => (underlyingMap z.hom).app n)
      (pushout.condition (f := a) (g := i))) (smallFreeGen hC q S n (E.symm x))
    exact (congrArg ((underlyingMap j.hom).app n)
      (whiskerIn_gen hC q n S n (E.symm x))).symm.trans hh
  let t := smallWhiskerDesc hC q n (s ≫ k) e he
  have htr : t ≫ r = 𝟙 _ := by
    apply whiskerFree_hom_ext hC q n
    · intro l x
      change (underlyingMap r.hom).app l ((underlyingMap t.hom).app l _) = wBase hC q n T l x
      have ht := smallWhiskerDesc_base hC q n (s ≫ k) e he l x
      apply (congrArg ((underlyingMap r.hom).app l) ht).trans
      have hcomp : (s ≫ k) ≫ r = whiskerIn hC q n T := by
        rw [Category.assoc, hkr, ← Category.assoc, hsp, Category.id_comp]
      exact (congrFun (congrArg (fun z => (underlyingMap z.hom).app l) hcomp)
        (smallFreeGen hC q T l x)).trans (whiskerIn_gen hC q n T l x)
    · intro x
      change (underlyingMap r.hom).app (n+1) ((underlyingMap t.hom).app (n+1) _) = wEdge hC q n T x
      have ht := smallWhiskerDesc_edge hC q n (s ≫ k) e he x
      apply (congrArg ((underlyingMap r.hom).app (n+1)) ht).trans
      have hh := congrFun (congrArg (fun z => (underlyingMap z.hom).app (n+1)) hjr)
        (wEdge hC q n S (E.symm x))
      exact hh.trans ((whiskerFreeMap_edge hC q n f (E.symm x)).trans
        (congrArg (wEdge hC q n T) (E.apply_symm_apply x)))
  exact hQ.retract (underlyingMap t.hom) (underlyingMap r.hom)
    (congrArg (fun z : whiskerFree hC q n T ⟶ whiskerFree hC q n T => underlyingMap z.hom) htr)

theorem whiskerFree_hasFillers {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1)) (S : Shape) :
    (whiskerFree hC q n S.realize).obj.underlying.HasFillers := by
  let P := S.2.spine n
  exact whiskerFree_hasFillers_of_spine hC q n hnq H P.map P.low_bijective
    (smallShape_hasFillers hC q P.S) (smallShape_hasFillers hC q S)
    (whiskerFree_bounded_hasFillers hC q n H P.S P.height_le)

end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model

noncomputable abbrev reverseWhiskerFree {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) :=
  (smallFree hC q).obj ((GlobularPresheaf.whiskering n true).obj S)

noncomputable def rwBase {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell k) :
    (reverseWhiskerFree hC q n S).obj.underlying.Cell k :=
  smallFreeGen hC q ((GlobularPresheaf.whiskering n true).obj S) k (.base k x)

noncomputable def rwEdge {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell n) :
    (reverseWhiskerFree hC q n S).obj.underlying.Cell (n+1) :=
  smallFreeGen hC q ((GlobularPresheaf.whiskering n true).obj S) (n+1) (.edge x)

@[simp] theorem rwBase_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell (k+1)) :
    (reverseWhiskerFree hC q n S).obj.underlying.source k (rwBase hC q n S (k+1) x) =
      rwBase hC q n S k (S.underlying.source k x) := by
  unfold rwBase
  erw [smallFreeGen_source]
  congr 1
  exact (S.underlying.whisker n true).presheafUnderlyingMap.source_app _ _

@[simp] theorem rwBase_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell (k+1)) :
    (reverseWhiskerFree hC q n S).obj.underlying.target k (rwBase hC q n S (k+1) x) =
      rwBase hC q n S k (S.underlying.target k x) := by
  unfold rwBase
  erw [smallFreeGen_target]
  congr 1
  exact (S.underlying.whisker n true).presheafUnderlyingMap.target_app _ _

@[simp] theorem rwEdge_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell n) :
    (reverseWhiskerFree hC q n S).obj.underlying.target n (rwEdge hC q n S x) = rwBase hC q n S n x := by
  unfold rwEdge rwBase
  erw [smallFreeGen_target]
  congr 1
  exact (S.underlying.whisker n true).presheafUnderlyingMap.target_app _ _

noncomputable def smallReverseWhiskerCell {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y)
    (e : S.underlying.Cell n → Y.obj.underlying.Cell (n+1))
    (k : ℕ) (x : (S.underlying.whisker n true).Cell k) : Y.obj.underlying.Cell k :=
  match x with
  | .base k x => (underlyingMap f.hom).app k (smallFreeGen hC q S k x)
  | .tip x => Y.obj.underlying.source n (e x)
  | .edge x => e x

theorem smallReverseWhiskerCell_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e : S.underlying.Cell n → Y.obj.underlying.Cell (n+1))
    (he : ∀ x, Y.obj.underlying.target n (e x) =
      (underlyingMap f.hom).app n (smallFreeGen hC q S n x))
    (k : ℕ) (x : (S.underlying.whisker n true).Cell (k+1)) :
    smallReverseWhiskerCell hC q n f e k ((S.underlying.whisker n true).source k x) =
      Y.obj.underlying.source k (smallReverseWhiskerCell hC q n f e (k+1) x) := by
  cases x with
  | base k x =>
    change (underlyingMap f.hom).app k (smallFreeGen hC q S k (S.underlying.source k x)) = _
    rw [← smallFreeGen_source, (underlyingMap f.hom).source_app]
    rfl
  | tip x =>
    change (underlyingMap f.hom).app k (smallFreeGen hC q S k (S.underlying.source k x)) = _
    rw [← smallFreeGen_source, (underlyingMap f.hom).source_app, ← he]
    exact (Y.obj.underlying.source_source k _).symm
  | edge x => rfl

theorem smallReverseWhiskerCell_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e : S.underlying.Cell n → Y.obj.underlying.Cell (n+1))
    (he : ∀ x, Y.obj.underlying.target n (e x) =
      (underlyingMap f.hom).app n (smallFreeGen hC q S n x))
    (k : ℕ) (x : (S.underlying.whisker n true).Cell (k+1)) :
    smallReverseWhiskerCell hC q n f e k ((S.underlying.whisker n true).target k x) =
      Y.obj.underlying.target k (smallReverseWhiskerCell hC q n f e (k+1) x) := by
  cases x with
  | base k x =>
    change (underlyingMap f.hom).app k (smallFreeGen hC q S k (S.underlying.target k x)) = _
    rw [← smallFreeGen_target, (underlyingMap f.hom).target_app]
    rfl
  | tip x =>
    change (underlyingMap f.hom).app k (smallFreeGen hC q S k (S.underlying.target k x)) = _
    rw [← smallFreeGen_target, (underlyingMap f.hom).target_app, ← he]
    exact (Y.obj.underlying.target_source k _).symm
  | edge x => exact (he x).symm

noncomputable def smallReverseWhiskerDesc {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e : S.underlying.Cell n → Y.obj.underlying.Cell (n+1))
    (he : ∀ x, Y.obj.underlying.target n (e x) =
      (underlyingMap f.hom).app n (smallFreeGen hC q S n x)) : reverseWhiskerFree hC q n S ⟶ Y :=
  smallFreeDescCells hC q (smallReverseWhiskerCell hC q n f e)
    (fun k x => by
      have h := (S.underlying.whisker n true).presheafUnderlyingMap.source_app k x
      change (S.underlying.whisker n true).presheaf.underlying.source k x =
        (S.underlying.whisker n true).source k x at h
      exact (congrArg (smallReverseWhiskerCell hC q n f e k) h).trans
        (smallReverseWhiskerCell_source hC q n f e he k x))
    (fun k x => by
      have h := (S.underlying.whisker n true).presheafUnderlyingMap.target_app k x
      change (S.underlying.whisker n true).presheaf.underlying.target k x =
        (S.underlying.whisker n true).target k x at h
      exact (congrArg (smallReverseWhiskerCell hC q n f e k) h).trans
        (smallReverseWhiskerCell_target hC q n f e he k x))

@[simp] theorem smallReverseWhiskerDesc_base {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e) (he) (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap (smallReverseWhiskerDesc hC q n f e he).hom).app k (rwBase hC q n S k x) =
      (underlyingMap f.hom).app k (smallFreeGen hC q S k x) :=
  smallFreeDescCells_gen hC q _ _ _ k _

@[simp] theorem smallReverseWhiskerDesc_edge {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : (smallFree hC q).obj S ⟶ Y) (e) (he) (x : S.underlying.Cell n) :
    (underlyingMap (smallReverseWhiskerDesc hC q n f e he).hom).app (n+1) (rwEdge hC q n S x) = e x :=
  smallFreeDescCells_gen hC q _ _ _ (n+1) _

noncomputable def reverseWhiskerIn {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) : (smallFree hC q).obj S ⟶ reverseWhiskerFree hC q n S :=
  (smallFree hC q).map ((GlobularPresheaf.whiskeringInclusion n true).app S)

@[simp] theorem reverseWhiskerIn_gen {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap (reverseWhiskerIn hC q n S).hom).app k (smallFreeGen hC q S k x) =
      rwBase hC q n S k x := smallFreeGen_map hC q _ k x

theorem inverseCell_inverse {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a : X.underlying.Cell (n+1)) :
    X.underlying.Joined (n+1) (X.inverseCell hC n (X.inverseCell hC n a)) a := by
  let D := disk C (n+1)
  let c := topCell C (n+1)
  let f : D ⟶ X := X.tupleMap (Shape.globe (n+1)) a
  have hf : (underlyingMap f).app (n+1) c = a := X.tupleMap_topCell (n+1) a
  let u := D.inverseCell hC n (D.inverseCell hC n c)
  have hp : D.underlying.Parallel (n+1) u c := by
    constructor <;> dsimp [u] <;> simp only [inverseCell_source, inverseCell_target]
  have h := (underlyingMap f).map_joined
    (freeShape_joined C hC (Shape.globe (n+1)) (n+1) u c hp)
  simpa only [u, map_inverseCell f, hf] using h

@[simp] theorem rwEdge_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell n) :
    (reverseWhiskerFree hC q n S).obj.underlying.source n (rwEdge hC q n S x) =
      smallFreeGen hC q ((GlobularPresheaf.whiskering n true).obj S) n (.tip x) := by
  unfold rwEdge
  erw [smallFreeGen_source]
  congr 1
  exact (S.underlying.whisker n true).presheafUnderlyingMap.source_app _ _

noncomputable def reverseWhiskerToWhisker {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) :
    reverseWhiskerFree hC q n S ⟶ whiskerFree hC q n S :=
  smallReverseWhiskerDesc hC q n (whiskerIn hC q n S)
    (fun x => (whiskerFree hC q n S).obj.inverseCell hC n (wEdge hC q n S x))
    (fun x => by rw [inverseCell_target, wEdge_source, whiskerIn_gen])

noncomputable def whiskerToReverseWhisker {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) :
    whiskerFree hC q n S ⟶ reverseWhiskerFree hC q n S :=
  smallWhiskerDesc hC q n (reverseWhiskerIn hC q n S)
    (fun x => (reverseWhiskerFree hC q n S).obj.inverseCell hC n (rwEdge hC q n S x))
    (fun x => by rw [inverseCell_source, rwEdge_target, reverseWhiskerIn_gen])

@[simp] theorem reverseWhiskerRound_base {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap ((reverseWhiskerToWhisker hC q n S) ≫
      (whiskerToReverseWhisker hC q n S)).hom).app k (rwBase hC q n S k x) =
      rwBase hC q n S k x := by
  change (underlyingMap (whiskerToReverseWhisker hC q n S).hom).app k
    ((underlyingMap (reverseWhiskerToWhisker hC q n S).hom).app k _) = _
  unfold reverseWhiskerToWhisker
  rw [smallReverseWhiskerDesc_base, whiskerIn_gen]
  unfold whiskerToReverseWhisker
  rw [smallWhiskerDesc_base, reverseWhiskerIn_gen]

@[simp] theorem reverseWhiskerRound_edge {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell n) :
    (underlyingMap ((reverseWhiskerToWhisker hC q n S) ≫
      (whiskerToReverseWhisker hC q n S)).hom).app (n+1) (rwEdge hC q n S x) =
      (reverseWhiskerFree hC q n S).obj.inverseCell hC n
        ((reverseWhiskerFree hC q n S).obj.inverseCell hC n (rwEdge hC q n S x)) := by
  change (underlyingMap (whiskerToReverseWhisker hC q n S).hom).app (n+1)
    ((underlyingMap (reverseWhiskerToWhisker hC q n S).hom).app (n+1) _) = _
  unfold reverseWhiskerToWhisker
  rw [smallReverseWhiskerDesc_edge, map_inverseCell]
  unfold whiskerToReverseWhisker
  rw [smallWhiskerDesc_edge]

theorem reverseWhiskerRound_low {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (hk : k ≤ n)
    (x : (S.underlying.whisker n true).Cell k) :
    (underlyingMap ((reverseWhiskerToWhisker hC q n S) ≫
      (whiskerToReverseWhisker hC q n S)).hom).app k
        (smallFreeGen hC q ((GlobularPresheaf.whiskering n true).obj S) k x) =
      smallFreeGen hC q ((GlobularPresheaf.whiskering n true).obj S) k x := by
  cases x with
  | base k x => exact reverseWhiskerRound_base hC q n S k x
  | edge x => omega
  | tip x =>
    rw [← rwEdge_source, (underlyingMap _).source_app, reverseWhiskerRound_edge,
      inverseCell_source, inverseCell_target, rwEdge_source]

theorem reverseWhiskerRound_top {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0})
    (x : (S.underlying.whisker n true).Cell (n+1)) :
    (reverseWhiskerFree hC q n S).obj.underlying.Joined (n+1)
      ((underlyingMap ((reverseWhiskerToWhisker hC q n S) ≫
        (whiskerToReverseWhisker hC q n S)).hom).app (n+1)
          (smallFreeGen hC q ((GlobularPresheaf.whiskering n true).obj S) (n+1) x))
      (smallFreeGen hC q ((GlobularPresheaf.whiskering n true).obj S) (n+1) x) := by
  cases x with
  | base k x =>
    change (reverseWhiskerFree hC q n S).obj.underlying.Joined (n+1)
      ((underlyingMap ((reverseWhiskerToWhisker hC q n S) ≫
        (whiskerToReverseWhisker hC q n S)).hom).app (n+1) (rwBase hC q n S (n+1) x)) _
    rw [reverseWhiskerRound_base]
    exact (reverseWhiskerFree hC q n S).obj.joined_refl hC _ _
  | edge x =>
    change (reverseWhiskerFree hC q n S).obj.underlying.Joined (n+1)
      ((underlyingMap ((reverseWhiskerToWhisker hC q n S) ≫
        (whiskerToReverseWhisker hC q n S)).hom).app (n+1) (rwEdge hC q n S x)) _
    rw [reverseWhiskerRound_edge]
    exact inverseCell_inverse _ hC n _

theorem reverseWhiskerFree_bounded_hasFillers {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (H : ExpansionContraction hC q (n+1)) (S : Shape) (hS : S.height ≤ n+1) :
    (reverseWhiskerFree hC q n S.realize).obj.underlying.HasFillers := by
  have hb (k : ℕ) (hk : n+1 < k) : IsEmpty (S.realize.underlying.Cell k) :=
    S.2.bounded k (lt_of_le_of_lt hS hk)
  apply free_hasFillers_of_top_homotopy hC q n H
    (GlobularPresheaf.liftSmall.obj ((GlobularPresheaf.whiskering n true).obj S.realize))
    (fun k hk => ⟨fun x => (S.realize.underlying.whisker_bounded n true hb k hk).false x.down⟩)
    (whiskerFree hC q n S.realize) (smallFree_cofibrant hC q _)
    (whiskerFree_bounded_hasFillers hC q n H S hS)
    (reverseWhiskerToWhisker hC q n S.realize) (whiskerToReverseWhisker hC q n S.realize)
  · intro k hk x
    exact reverseWhiskerRound_low hC q n S.realize k hk x.down
  · intro x
    exact reverseWhiskerRound_top hC q n S.realize x.down

theorem reverseWhiskerFree_hom_ext {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    {f g : reverseWhiskerFree hC q n S ⟶ Y}
    (hb : ∀ k x, (underlyingMap f.hom).app k (rwBase hC q n S k x) =
      (underlyingMap g.hom).app k (rwBase hC q n S k x))
    (he : ∀ x, (underlyingMap f.hom).app (n+1) (rwEdge hC q n S x) =
      (underlyingMap g.hom).app (n+1) (rwEdge hC q n S x)) : f = g := by
  apply smallFree_hom_ext hC q
  intro k x
  cases x with
  | base k x => exact hb k x
  | edge x => exact he x
  | tip x =>
    rw [← rwEdge_source hC q k S x, (underlyingMap f.hom).source_app,
      (underlyingMap g.hom).source_app, he]

noncomputable def reverseWhiskerFreeMap {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) :
    reverseWhiskerFree hC q n S ⟶ reverseWhiskerFree hC q n T :=
  (smallFree hC q).map ((GlobularPresheaf.whiskering n true).map f)

@[simp] theorem reverseWhiskerFreeMap_base {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap (reverseWhiskerFreeMap hC q n f).hom).app k (rwBase hC q n S k x) =
      rwBase hC q n T k ((GlobularPresheaf.underlyingMap f).app k x) :=
  smallFreeGen_map hC q _ k _

@[simp] theorem reverseWhiskerFreeMap_edge {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) (x : S.underlying.Cell n) :
    (underlyingMap (reverseWhiskerFreeMap hC q n f).hom).app (n+1) (rwEdge hC q n S x) =
      rwEdge hC q n T ((GlobularPresheaf.underlyingMap f).app n x) :=
  smallFreeGen_map hC q _ (n+1) _

@[reassoc] theorem reverseWhiskerIn_naturality {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) {S T : GlobularPresheaf.{0}} (f : S ⟶ T) :
    reverseWhiskerIn hC q n S ≫ reverseWhiskerFreeMap hC q n f =
      (smallFree hC q).map f ≫ reverseWhiskerIn hC q n T := by
  unfold reverseWhiskerIn reverseWhiskerFreeMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (smallFree hC q).map ((GlobularPresheaf.whiskeringInclusion n true).naturality f).symm

theorem reverseWhiskerFree_hasFillers_of_spine {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))
    {S T : GlobularPresheaf.{0}} (f : S ⟶ T)
    (hf : ∀ k, k ≤ n → Function.Bijective ((GlobularPresheaf.underlyingMap f).app k))
    (hS : ((smallFree hC q).obj S).obj.underlying.HasFillers)
    (hT : ((smallFree hC q).obj T).obj.underlying.HasFillers)
    (hW : (reverseWhiskerFree hC q n S).obj.underlying.HasFillers) :
    (reverseWhiskerFree hC q n T).obj.underlying.HasFillers := by
  let := cutoff_hasColimits hC q
  let F := smallFree hC q
  obtain ⟨M,i,p,s,hip,hsp,hi,hM,hp⟩ := exists_upper_resolution hC q n hnq
    (F.map f) (smallFree_cofibrant hC q T) hS hT
    (smallFree_low_bijective hC q n hnq f hf)
  let a := reverseWhiskerIn hC q n S
  let Q := pushout a i
  let j : reverseWhiskerFree hC q n S ⟶ Q := pushout.inl a i
  let k : M ⟶ Q := pushout.inr a i
  have hQ : Q.obj.underlying.HasFillers := upper_pushout_hasFillers hC q (n+1) H
    (IsPushout.of_hasPushout a i) hi (smallFree_cofibrant hC q S) hS hM
    (smallFree_cofibrant hC q _) hW
  let wm := reverseWhiskerFreeMap hC q n f
  let r : Q ⟶ reverseWhiskerFree hC q n T := pushout.desc wm (p ≫ reverseWhiskerIn hC q n T) (by
    rw [← Category.assoc, hip]
    exact reverseWhiskerIn_naturality hC q n f)
  have hjr : j ≫ r = wm := pushout.inl_desc _ _ _
  have hkr : k ≫ r = p ≫ reverseWhiskerIn hC q n T := pushout.inr_desc _ _ _
  let E := Equiv.ofBijective ((GlobularPresheaf.underlyingMap f).app n) (hf n le_rfl)
  have hsgen (x : T.underlying.Cell n) :
      (underlyingMap s.hom).app n (smallFreeGen hC q T n x) =
      (underlyingMap i.hom).app n (smallFreeGen hC q S n (E.symm x)) := by
    apply hp n le_rfl
    have hs := congrFun (congrArg (fun z => (underlyingMap z.hom).app n) hsp)
      (smallFreeGen hC q T n x)
    have hi' := congrFun (congrArg (fun z => (underlyingMap z.hom).app n) hip)
      (smallFreeGen hC q S n (E.symm x))
    exact hs.trans (((smallFreeGen_map hC q f n (E.symm x)).trans
      (congrArg (smallFreeGen hC q T n) (E.apply_symm_apply x))).symm.trans hi'.symm)
  let e (x : T.underlying.Cell n) := (underlyingMap j.hom).app (n+1) (rwEdge hC q n S (E.symm x))
  have he (x : T.underlying.Cell n) : Q.obj.underlying.target n (e x) =
      (underlyingMap (s ≫ k).hom).app n (smallFreeGen hC q T n x) := by
    change Q.obj.underlying.target n ((underlyingMap j.hom).app (n+1) _) =
      (underlyingMap k.hom).app n ((underlyingMap s.hom).app n _)
    rw [← (underlyingMap j.hom).target_app, rwEdge_target, hsgen]
    have hh := congrFun (congrArg (fun z => (underlyingMap z.hom).app n)
      (pushout.condition (f := a) (g := i))) (smallFreeGen hC q S n (E.symm x))
    exact (congrArg ((underlyingMap j.hom).app n)
      (reverseWhiskerIn_gen hC q n S n (E.symm x))).symm.trans hh
  let t := smallReverseWhiskerDesc hC q n (s ≫ k) e he
  have htr : t ≫ r = 𝟙 _ := by
    apply reverseWhiskerFree_hom_ext hC q n
    · intro l x
      change (underlyingMap r.hom).app l ((underlyingMap t.hom).app l _) = rwBase hC q n T l x
      have ht := smallReverseWhiskerDesc_base hC q n (s ≫ k) e he l x
      apply (congrArg ((underlyingMap r.hom).app l) ht).trans
      have hcomp : (s ≫ k) ≫ r = reverseWhiskerIn hC q n T := by
        rw [Category.assoc, hkr, ← Category.assoc, hsp, Category.id_comp]
      exact (congrFun (congrArg (fun z => (underlyingMap z.hom).app l) hcomp)
        (smallFreeGen hC q T l x)).trans (reverseWhiskerIn_gen hC q n T l x)
    · intro x
      change (underlyingMap r.hom).app (n+1) ((underlyingMap t.hom).app (n+1) _) = rwEdge hC q n T x
      have ht := smallReverseWhiskerDesc_edge hC q n (s ≫ k) e he x
      apply (congrArg ((underlyingMap r.hom).app (n+1)) ht).trans
      have hh := congrFun (congrArg (fun z => (underlyingMap z.hom).app (n+1)) hjr)
        (rwEdge hC q n S (E.symm x))
      exact hh.trans ((reverseWhiskerFreeMap_edge hC q n f (E.symm x)).trans
        (congrArg (rwEdge hC q n T) (E.apply_symm_apply x)))
  exact hQ.retract (underlyingMap t.hom) (underlyingMap r.hom)
    (congrArg (fun z : reverseWhiskerFree hC q n T ⟶ reverseWhiskerFree hC q n T => underlyingMap z.hom) htr)

theorem reverseWhiskerFree_hasFillers {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1)) (S : Shape) :
    (reverseWhiskerFree hC q n S.realize).obj.underlying.HasFillers := by
  let P := S.2.spine n
  exact reverseWhiskerFree_hasFillers_of_spine hC q n hnq H P.map P.low_bijective
    (smallShape_hasFillers hC q P.S) (smallShape_hasFillers hC q S)
    (reverseWhiskerFree_bounded_hasFillers hC q n H P.S P.height_le)

end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite

structure GlobularFrame (K : Type u) [Category.{v} K] where
  obj : ℕ → K
  bd : ℕ → K
  inc : ∀ j, bd j ⟶ obj j
  left : ∀ j, obj j ⟶ bd (j+1)
  right : ∀ j, obj j ⟶ bd (j+1)
  square : ∀ j, IsPushout (inc j) (inc j) (left j) (right j)
  initial : IsInitial (bd 0)

namespace GlobularFrame
variable {K : Type u} [Category.{v} K]

def diagram (B : GlobularFrame K) : CoGlobularObject K where
  obj := B.obj
  source j := B.left j ≫ B.inc (j+1)
  target j := B.right j ≫ B.inc (j+1)
  source_source j := by
    simp only [Category.assoc]
    rw [← Category.assoc (B.inc (j+1)), (B.square (j+1)).w, Category.assoc]
  target_source j := by
    simp only [Category.assoc]
    rw [← Category.assoc (B.inc (j+1)), (B.square (j+1)).w, Category.assoc]

def homGlob (B : GlobularFrame K) (Y : K) : GlobularSet.{v} where
  Cell j := B.obj j ⟶ Y
  source j f := B.diagram.source j ≫ f
  target j f := B.diagram.target j ≫ f
  source_source j f := by
    change B.diagram.source j ≫ B.diagram.source (j+1) ≫ f =
      B.diagram.source j ≫ B.diagram.target (j+1) ≫ f
    erw [← Category.assoc, B.diagram.source_source, Category.assoc]
  target_source j f := by
    change B.diagram.target j ≫ B.diagram.source (j+1) ≫ f =
      B.diagram.target j ≫ B.diagram.target (j+1) ≫ f
    erw [← Category.assoc, B.diagram.target_source, Category.assoc]

def post {B : GlobularFrame K} {X Y : K} (f : X ⟶ Y) :
    GlobularSet.Hom (B.homGlob X) (B.homGlob Y) where
  app _ a := a ≫ f
  source_app _ _ := Category.assoc _ _ _
  target_app _ _ := Category.assoc _ _ _

structure BoundaryEquiv (B : GlobularFrame K) (n : ℕ) where
  equiv : ∀ Y, (B.bd n ⟶ Y) ≃ (B.homGlob Y).Boundary n
  naturality : ∀ {X Y} (a : B.bd n ⟶ X) (f : X ⟶ Y),
    equiv Y (a ≫ f) = (post f).boundaryMap n (equiv X a)
  inc_boundary : ∀ {Y} (a : B.obj n ⟶ Y),
    equiv Y (B.inc n ≫ a) = (B.homGlob Y).boundary n a

namespace BoundaryEquiv
variable (B : GlobularFrame K)
noncomputable def zero : BoundaryEquiv B 0 where
  equiv Y :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => B.initial.to Y
      left_inv := fun _ => B.initial.hom_ext _ _
      right_inv := fun _ => by change (PUnit.unit : PUnit) = _; exact Subsingleton.elim _ _ }
  naturality _ _ := rfl
  inc_boundary _ := rfl

variable {B} {n : ℕ} (R : BoundaryEquiv B n)

def nextValue (Y : K) (f : B.bd (n+1) ⟶ Y) : (B.homGlob Y).Boundary (n+1) :=
  ⟨(B.left n ≫ f, B.right n ≫ f), by
    rw [GlobularSet.parallel_iff_boundary_eq, ← R.inc_boundary, ← R.inc_boundary,
      ← Category.assoc, ← Category.assoc, (B.square n).w]⟩

theorem nextValue_bijective (Y : K) : Function.Bijective (R.nextValue Y) := by
  constructor
  · intro f g h
    apply (B.square n).hom_ext
    · exact congrArg (fun b => b.1.1) h
    · exact congrArg (fun b => b.1.2) h
  · intro b
    have hb : B.inc n ≫ b.1.1 = B.inc n ≫ b.1.2 := by
      apply (R.equiv Y).injective
      erw [R.inc_boundary, R.inc_boundary]
      exact (GlobularSet.parallel_iff_boundary_eq _ _ _ _).1 b.2
    refine ⟨(B.square n).desc b.1.1 b.1.2 hb, ?_⟩
    apply Subtype.ext
    exact Prod.ext ((B.square n).inl_desc _ _ _) ((B.square n).inr_desc _ _ _)

noncomputable def succ : BoundaryEquiv B (n+1) where
  equiv Y := Equiv.ofBijective (R.nextValue Y) (R.nextValue_bijective Y)
  naturality a f := by
    apply Subtype.ext
    change (B.left n ≫ (a ≫ f), B.right n ≫ (a ≫ f)) =
      ((B.left n ≫ a) ≫ f, (B.right n ≫ a) ≫ f)
    exact Prod.ext (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm
  inc_boundary a := by
    apply Subtype.ext
    exact Prod.ext (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm

end BoundaryEquiv

noncomputable def boundaryEquiv (B : GlobularFrame K) : (n : ℕ) → BoundaryEquiv B n
  | 0 => BoundaryEquiv.zero B
  | n+1 => (boundaryEquiv B n).succ

structure Hom (D B : GlobularFrame K) where
  obj : ∀ j, D.obj j ⟶ B.obj j
  bd : ∀ j, D.bd j ⟶ B.bd j
  inc : ∀ j, bd j ≫ B.inc j = D.inc j ≫ obj j
  left : ∀ j, D.left j ≫ bd (j+1) = obj j ≫ B.left j
  right : ∀ j, D.right j ≫ bd (j+1) = obj j ≫ B.right j

namespace Hom
variable {D B : GlobularFrame K}
@[reassoc] theorem source_naturality (e : Hom D B) (j : ℕ) :
    D.diagram.source j ≫ e.obj (j+1) = e.obj j ≫ B.diagram.source j := by
  change (D.left j ≫ D.inc (j+1)) ≫ e.obj (j+1) = _
  rw [Category.assoc, ← e.inc, ← Category.assoc, e.left, Category.assoc]
  rfl
@[reassoc] theorem target_naturality (e : Hom D B) (j : ℕ) :
    D.diagram.target j ≫ e.obj (j+1) = e.obj j ≫ B.diagram.target j := by
  change (D.right j ≫ D.inc (j+1)) ≫ e.obj (j+1) = _
  rw [Category.assoc, ← e.inc, ← Category.assoc, e.right, Category.assoc]
  rfl

def pre (e : Hom D B) (Y : K) : GlobularSet.Hom (B.homGlob Y) (D.homGlob Y) where
  app j a := e.obj j ≫ a
  source_app j a := by
    change e.obj j ≫ B.diagram.source j ≫ a = D.diagram.source j ≫ e.obj (j+1) ≫ a
    erw [← Category.assoc, ← e.source_naturality, Category.assoc]
    rfl
  target_app j a := by
    change e.obj j ≫ B.diagram.target j ≫ a = D.diagram.target j ≫ e.obj (j+1) ≫ a
    erw [← Category.assoc, ← e.target_naturality, Category.assoc]
    rfl

theorem boundary_naturality (e : Hom D B) {Y : K} (j : ℕ) (a : B.bd j ⟶ Y) :
    (D.boundaryEquiv j).equiv Y (e.bd j ≫ a) =
      (e.pre Y).boundaryMap j ((B.boundaryEquiv j).equiv Y a) := by
  cases j with
  | zero => rfl
  | succ j =>
    apply Subtype.ext
    change (D.left j ≫ (e.bd (j+1) ≫ a), D.right j ≫ (e.bd (j+1) ≫ a)) =
      (e.obj j ≫ (B.left j ≫ a), e.obj j ≫ (B.right j ≫ a))
    simp only [← Category.assoc, e.left, e.right]

end Hom
end GlobularFrame

namespace GlobularSet

def fiberProd {X Y Z : GlobularSet.{v}} (f : Hom X Z) (g : Hom Y Z) : GlobularSet.{v} where
  Cell k := {xy : X.Cell k × Y.Cell k // f.app k xy.1 = g.app k xy.2}
  source k xy := ⟨(X.source k xy.1.1, Y.source k xy.1.2), by
    rw [f.source_app, g.source_app, xy.2]⟩
  target k xy := ⟨(X.target k xy.1.1, Y.target k xy.1.2), by
    rw [f.target_app, g.target_app, xy.2]⟩
  source_source k xy := Subtype.ext (Prod.ext (X.source_source k _) (Y.source_source k _))
  target_source k xy := Subtype.ext (Prod.ext (X.target_source k _) (Y.target_source k _))

namespace fiberProd
variable {X Y Z : GlobularSet.{v}} (f : Hom X Z) (g : Hom Y Z)
def fst : Hom (fiberProd f g) X where
  app _ xy := xy.1.1
  source_app _ _ := rfl
  target_app _ _ := rfl
def snd : Hom (fiberProd f g) Y where
  app _ xy := xy.1.2
  source_app _ _ := rfl
  target_app _ _ := rfl

variable {A : GlobularSet.{v}}
def lift (a : Hom A X) (b : Hom A Y) (h : a.comp f = b.comp g) : Hom A (fiberProd f g) where
  app k x := ⟨(a.app k x, b.app k x), congrFun (congrArg (fun t => t.app k) h) x⟩
  source_app k x := Subtype.ext (Prod.ext (a.source_app k x) (b.source_app k x))
  target_app k x := Subtype.ext (Prod.ext (a.target_app k x) (b.target_app k x))

@[simp] theorem lift_fst (a : Hom A X) (b : Hom A Y) (h : a.comp f = b.comp g) :
    (lift f g a b h).comp (fst f g) = a := rfl
@[simp] theorem lift_snd (a : Hom A X) (b : Hom A Y) (h : a.comp f = b.comp g) :
    (lift f g a b h).comp (snd f g) = b := rfl

end fiberProd
end GlobularSet

namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasPushouts K]
variable {D B : GlobularFrame K}

noncomputable abbrev oneSided (e : Hom D B) (j : ℕ) : K := pushout (e.bd j) (D.inc j)
noncomputable def oneSidedMap (e : Hom D B) (j : ℕ) : oneSided e j ⟶ B.obj j :=
  pushout.desc (B.inc j) (e.obj j) (e.inc j)

namespace Hom
variable (e : Hom D B) {X Y : K} (p : X ⟶ Y)

def relativeGlob : GlobularSet.{v} := GlobularSet.fiberProd (e.pre Y) (post p)

def relativeMap : GlobularSet.Hom (B.homGlob X) (e.relativeGlob p) :=
  GlobularSet.fiberProd.lift (e.pre Y) (post p) (post p) (e.pre X) (by
    ext k a
    exact (Category.assoc _ _ _).symm)

theorem relativeMap_liftsBoundary (j : ℕ) (hp : HasLiftingProperty (oneSidedMap e j) p) :
    GlobularSet.LiftsBoundary (e.relativeMap p) j := by
  intro bd z hz
  let a := (B.boundaryEquiv j).equiv X |>.symm bd
  have ha : (B.boundaryEquiv j).equiv X a = bd := Equiv.apply_symm_apply _ _
  have hz₁ := congrArg ((GlobularSet.fiberProd.fst (e.pre Y) (post p)).boundaryMap j) hz
  have hz₂ := congrArg ((GlobularSet.fiberProd.snd (e.pre Y) (post p)).boundaryMap j) hz
  have hab : e.bd j ≫ a = D.inc j ≫ z.1.2 := by
    apply ((D.boundaryEquiv j).equiv X).injective
    erw [e.boundary_naturality, ha, (D.boundaryEquiv j).inc_boundary]
    cases j with
    | zero => rfl
    | succ j => exact hz₂.symm
  have hap : a ≫ p = B.inc j ≫ z.1.1 := by
    apply ((B.boundaryEquiv j).equiv Y).injective
    erw [(B.boundaryEquiv j).naturality, ha, (B.boundaryEquiv j).inc_boundary]
    cases j with
    | zero => rfl
    | succ j => exact hz₁.symm
  let top : oneSided e j ⟶ X := pushout.desc a z.1.2 hab
  have sq : CommSq top (oneSidedMap e j) p z.1.1 := by
    constructor
    apply pushout.hom_ext
    · dsimp only [top, oneSidedMap]
      erw [pushout.inl_desc_assoc, pushout.inl_desc_assoc]
      exact hap
    · dsimp only [top, oneSidedMap]
      erw [pushout.inr_desc_assoc, pushout.inr_desc_assoc]
      exact z.2.symm
  let : sq.HasLift := hp.sq_hasLift sq
  let l := sq.lift
  refine ⟨l, ?_, ?_⟩
  · have hh : B.inc j ≫ l = a := by
      have h := congrArg (pushout.inl (e.bd j) (D.inc j) ≫ ·) sq.fac_left
      dsimp only [oneSidedMap, top] at h
      erw [pushout.inl_desc, pushout.inl_desc_assoc] at h
      exact h
    rw [← (B.boundaryEquiv j).inc_boundary, hh, ha]
  · apply Subtype.ext
    apply Prod.ext
    · exact sq.fac_right
    · have h := congrArg (pushout.inr (e.bd j) (D.inc j) ≫ ·) sq.fac_left
      dsimp only [oneSidedMap, top] at h
      erw [pushout.inr_desc, pushout.inr_desc_assoc] at h
      exact h

end Hom
end GlobularFrame

end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularFrame
variable {K : Type u} [Category.{v} K] {L : Type w} [Category.{v} L]

noncomputable def map (D : GlobularFrame K) (F : K ⥤ L) [PreservesColimitsOfShape WalkingSpan F]
    [PreservesColimitsOfShape (Discrete PEmpty) F] : GlobularFrame L where
  obj j := F.obj (D.obj j)
  bd j := F.obj (D.bd j)
  inc j := F.map (D.inc j)
  left j := F.map (D.left j)
  right j := F.map (D.right j)
  square j := (D.square j).map F
  initial := D.initial.isInitialObj F _

end GlobularFrame

namespace GlobularTheory.Model

noncomputable def diskFrame (C : GlobularTheory.{v}) : GlobularFrame C.Model where
  obj := disk C
  bd := boundaryDisk C
  inc := I C
  left j := pushout.inl (I C j) (I C j)
  right j := pushout.inr (I C j) (I C j)
  square _j := IsPushout.of_hasPushout _ _
  initial := initialIsInitial

@[simp] theorem diskFrame_source (C : GlobularTheory.{v}) (j : ℕ) :
    (diskFrame C).diagram.source j = J C j := by
  change pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  exact pushout.inl_desc _ _ _

@[simp] theorem diskFrame_target (C : GlobularTheory.{v}) (j : ℕ) :
    (diskFrame C).diagram.target j = targetDisk C j := by
  change pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  exact pushout.inr_desc _ _ _

noncomputable def cutoffDiskFrame {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q : ℕ) :
    GlobularFrame (CutoffModels C q) := by
  let : (cutoffFunctor hC q).IsLeftAdjoint := (cutoffAdjunction hC q).isLeftAdjoint
  exact (diskFrame C).map (cutoffFunctor hC q)

@[simp] theorem cutoffDiskFrame_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q j : ℕ) : (cutoffDiskFrame hC q).diagram.source j = cutoffJ hC q j := by
  change (cutoffFunctor hC q).map _ ≫ (cutoffFunctor hC q).map _ = _
  rw [← Functor.map_comp]
  exact congrArg (cutoffFunctor hC q).map (diskFrame_source C j)

end GlobularTheory.Model

structure CylinderNode {K : Type u} [Category.{v} K] (D : GlobularFrame K) (j : ℕ) where
  bd : K
  obj : K
  inc : bd ⟶ obj
  bdEnd : Bool → (D.bd j ⟶ bd)
  endpoint : Bool → (D.obj j ⟶ obj)
  comm : ∀ ε, bdEnd ε ≫ inc = D.inc j ≫ endpoint ε

namespace CylinderNode
variable {K : Type u} [Category.{v} K] {D : GlobularFrame K} {j : ℕ}

noncomputable def critical (D : GlobularFrame K) (n : ℕ) : CylinderNode D n where
  bd := D.bd n
  obj := D.obj (n+1)
  inc := D.inc n ≫ D.diagram.source n
  bdEnd _ := 𝟙 _
  endpoint ε := if ε then D.diagram.target n else D.diagram.source n
  comm ε := by
    cases ε
    · simp
    · simp only [↓reduceIte, Category.id_comp]
      change D.inc n ≫ D.left n ≫ D.inc (n+1) = D.inc n ≫ D.right n ≫ D.inc (n+1)
      rw [← Category.assoc, (D.square n).w, Category.assoc]

variable [HasPushouts K]

noncomputable abbrev nextBoundary (Z : CylinderNode D j) : K := pushout Z.inc Z.inc

noncomputable def nextBdEnd (Z : CylinderNode D j) (ε : Bool) :
    D.bd (j+1) ⟶ Z.nextBoundary :=
  (D.square j).desc (Z.endpoint ε ≫ pushout.inl _ _) (Z.endpoint ε ≫ pushout.inr _ _)
    (by rw [← Category.assoc, ← Z.comm, Category.assoc, pushout.condition,
      ← Category.assoc, Z.comm, Category.assoc])

@[reassoc (attr := simp)] theorem nextBdEnd_left (Z : CylinderNode D j) (ε : Bool) :
    D.left j ≫ Z.nextBdEnd ε = Z.endpoint ε ≫ pushout.inl _ _ :=
  (D.square j).inl_desc _ _ _

@[reassoc (attr := simp)] theorem nextBdEnd_right (Z : CylinderNode D j) (ε : Bool) :
    D.right j ≫ Z.nextBdEnd ε = Z.endpoint ε ≫ pushout.inr _ _ :=
  (D.square j).inr_desc _ _ _

end CylinderNode

namespace TwoEndpoints
variable {K : Type u} [Category.{v} K] [HasPushouts K]
variable {Bd Disk B : K} (i : Bd ⟶ Disk) (e : Bool → (Bd ⟶ B))

noncomputable abbrev first : K := pushout (e false) i
noncomputable abbrev obj : K := pushout (e true ≫ pushout.inl (e false) i) i
noncomputable def base : B ⟶ obj i e := pushout.inl _ _ ≫ pushout.inl _ _
noncomputable def endpoint (ε : Bool) : Disk ⟶ obj i e :=
  if ε then pushout.inr _ _ else pushout.inr _ _ ≫ pushout.inl _ _

theorem condition (ε : Bool) : e ε ≫ base i e = i ≫ endpoint i e ε := by
  cases ε
  · simp only [base, endpoint, Bool.false_eq_true, ↓reduceIte, ← Category.assoc]
    rw [pushout.condition]
  · simp only [base, endpoint, ↓reduceIte, ← Category.assoc]
    exact pushout.condition

variable {Y : K}
noncomputable def desc (b : B ⟶ Y) (d : Bool → (Disk ⟶ Y))
    (h : ∀ ε, e ε ≫ b = i ≫ d ε) : obj i e ⟶ Y :=
  pushout.desc (pushout.desc b (d false) (h false)) (d true)
    (by rw [Category.assoc, pushout.inl_desc]; exact h true)

@[reassoc (attr := simp)] theorem base_desc (b : B ⟶ Y) (d : Bool → (Disk ⟶ Y))
    (h : ∀ ε, e ε ≫ b = i ≫ d ε) : base i e ≫ desc i e b d h = b := by
  simp only [base, desc, Category.assoc, pushout.inl_desc]

@[reassoc (attr := simp)] theorem endpoint_desc (b : B ⟶ Y) (d : Bool → (Disk ⟶ Y))
    (h : ∀ ε, e ε ≫ b = i ≫ d ε) (ε : Bool) : endpoint i e ε ≫ desc i e b d h = d ε := by
  cases ε <;> simp only [endpoint, desc, Bool.false_eq_true,
    ↓reduceIte, Category.assoc, pushout.inl_desc, pushout.inr_desc]

theorem hom_ext {f g : obj i e ⟶ Y} (hb : base i e ≫ f = base i e ≫ g)
    (hd : ∀ ε, endpoint i e ε ≫ f = endpoint i e ε ≫ g) : f = g := by
  apply pushout.hom_ext
  · apply pushout.hom_ext
    · simpa only [base, Category.assoc] using hb
    · simpa only [endpoint, Bool.false_eq_true, ↓reduceIte, Category.assoc] using hd false
  · simpa only [endpoint, ↓reduceIte] using hd true

theorem oneSide_lifting {P X Y : K} (f : obj i e ⟶ P) (p : X ⟶ Y)
    (hi : HasLiftingProperty i p) (hf : HasLiftingProperty f p) (ε : Bool) :
    HasLiftingProperty (pushout.desc (base i e ≫ f) (endpoint i e ε ≫ f)
      (by rw [← Category.assoc, condition, Category.assoc])) p := by
  constructor
  intro a b sq
  let aB := pushout.inl (e ε) i ≫ a
  let aD := pushout.inr (e ε) i ≫ a
  have ha : e ε ≫ aB = i ≫ aD := by
    dsimp only [aB, aD]
    rw [← Category.assoc, pushout.condition, Category.assoc]
  have hB : aB ≫ p = base i e ≫ f ≫ b := by
    have h := congrArg (pushout.inl (e ε) i ≫ ·) sq.w
    simpa only [aB, Category.assoc, pushout.inl_desc_assoc] using h
  have hD : aD ≫ p = endpoint i e ε ≫ f ≫ b := by
    have h := congrArg (pushout.inr (e ε) i ≫ ·) sq.w
    simpa only [aD, Category.assoc, pushout.inr_desc_assoc] using h
  have otherSq : CommSq (e (!ε) ≫ aB) i p (endpoint i e (!ε) ≫ f ≫ b) := by
    constructor
    rw [Category.assoc, hB, ← Category.assoc (e (!ε)), condition, Category.assoc]
  let : otherSq.HasLift := hi.sq_hasLift otherSq
  let ds : Bool → (Disk ⟶ X) := fun δ => if δ = ε then aD else otherSq.lift
  have dsε : ds ε = aD := by simp [ds]
  have dsother : ds (!ε) = otherSq.lift := by cases ε <;> simp [ds]
  have hds : ∀ δ, e δ ≫ aB = i ≫ ds δ := by
    intro δ
    by_cases h : δ = ε
    · subst δ; rw [dsε]; exact ha
    · have he : δ = !ε := by cases δ <;> cases ε <;> simp_all
      subst δ; rw [dsother]; exact otherSq.fac_left.symm
  let a' := desc i e aB ds hds
  have sq' : CommSq a' f p b := by
    constructor
    apply hom_ext i e
    · simp only [← Category.assoc, base_desc, a']
      simpa only [Category.assoc] using hB
    · intro δ
      simp only [← Category.assoc, endpoint_desc, a']
      by_cases h : δ = ε
      · subst δ; rw [dsε]; simpa only [Category.assoc] using hD
      · have he : δ = !ε := by cases δ <;> cases ε <;> simp_all
        subst δ; rw [dsother]; simpa only [Category.assoc] using otherSq.fac_right
  let : sq'.HasLift := hf.sq_hasLift sq'
  refine CommSq.HasLift.mk' ⟨sq'.lift, ?_, sq'.fac_right⟩
  apply pushout.hom_ext
  · rw [pushout.inl_desc_assoc, Category.assoc, sq'.fac_left]
    exact base_desc i e aB ds hds
  · rw [pushout.inr_desc_assoc, Category.assoc, sq'.fac_left]
    exact (endpoint_desc i e aB ds hds ε).trans dsε

end TwoEndpoints
open CategoryTheory CategoryTheory.Limits Opposite
namespace CylinderNode
variable {K : Type u} [Category.{v} K] {D : GlobularFrame K} {j : ℕ}

def stationary (D : GlobularFrame K) (j : ℕ) : CylinderNode D j where
  bd := D.bd j
  obj := D.obj j
  inc := D.inc j
  bdEnd _ := 𝟙 _
  endpoint _ := 𝟙 _
  comm _ := by simp

structure Step (Z : CylinderNode D j) (W : CylinderNode D (j+1)) where
  left : Z.obj ⟶ W.bd
  right : Z.obj ⟶ W.bd
  square : IsPushout Z.inc Z.inc left right
  end_left : ∀ ε, D.left j ≫ W.bdEnd ε = Z.endpoint ε ≫ left
  end_right : ∀ ε, D.right j ≫ W.bdEnd ε = Z.endpoint ε ≫ right

def stationaryStep (D : GlobularFrame K) (j : ℕ) :
    Step (stationary D j) (stationary D (j+1)) where
  left := D.left j
  right := D.right j
  square := D.square j
  end_left _ := by simp [stationary]
  end_right _ := by simp [stationary]

noncomputable def criticalStep (D : GlobularFrame K) (j : ℕ) :
    Step (stationary D j) (critical D (j+1)) where
  left := D.left j
  right := D.right j
  square := D.square j
  end_left _ := by simp [stationary, critical]
  end_right _ := by simp [stationary, critical]

end CylinderNode

namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)

noncomputable def cylinderFactor (j : ℕ) (B : CutoffModels C q)
    (e : Bool → (cutoffBoundary hC q j ⟶ B)) := by
  let := cutoff_hasColimits hC q
  let := cutoff_hasLimits hC q
  let := boundaryClass_smallObject hC q (n+1)
  exact MorphismProperty.factorizationData (boundaryClass hC q (n+1)).rlp.llp
    (boundaryClass hC q (n+1)).rlp
    (terminal.from (TwoEndpoints.obj (cutoffI hC q j) e))

noncomputable def completedCylinder (j : ℕ) (B : CutoffModels C q)
    (e : Bool → (cutoffBoundary hC q j ⟶ B)) : CylinderNode (cutoffDiskFrame hC q) j := by
  let := cutoff_hasColimits hC q
  let F := cylinderFactor hC q n j B e
  exact
    { bd := B
      obj := F.Z
      inc := TwoEndpoints.base (cutoffI hC q j) e ≫ F.i
      bdEnd := e
      endpoint ε := TwoEndpoints.endpoint (cutoffI hC q j) e ε ≫ F.i
      comm ε := by erw [← Category.assoc, TwoEndpoints.condition, Category.assoc] }

noncomputable def cylinderNext {j : ℕ} (Z : CylinderNode (cutoffDiskFrame hC q) j) :
    CylinderNode (cutoffDiskFrame hC q) (j+1) := by
  let := cutoff_hasColimits hC q
  exact completedCylinder hC q n (j+1) Z.nextBoundary Z.nextBdEnd

noncomputable def cylinderNextStep {j : ℕ} (Z : CylinderNode (cutoffDiskFrame hC q) j) :
    CylinderNode.Step Z (cylinderNext hC q n Z) := by
  let := cutoff_hasColimits hC q
  exact
    { left := pushout.inl Z.inc Z.inc
      right := pushout.inr Z.inc Z.inc
      square := IsPushout.of_hasPushout _ _
      end_left := Z.nextBdEnd_left
      end_right := Z.nextBdEnd_right }

noncomputable def cylinderNode : (j : ℕ) → CylinderNode (cutoffDiskFrame hC q) j
  | 0 => if 0 < n then CylinderNode.stationary (cutoffDiskFrame hC q) 0
      else CylinderNode.critical (cutoffDiskFrame hC q) 0
  | j+1 => if j+1 < n then CylinderNode.stationary (cutoffDiskFrame hC q) (j+1)
      else if j+1 = n then CylinderNode.critical (cutoffDiskFrame hC q) (j+1)
      else cylinderNext hC q n (cylinderNode j)

theorem cylinderNode_low {j : ℕ} (h : j < n) :
    cylinderNode hC q n j = CylinderNode.stationary (cutoffDiskFrame hC q) j := by
  cases j <;> simp only [cylinderNode, ite_eq_left h]

theorem cylinderNode_critical : cylinderNode hC q n n =
    CylinderNode.critical (cutoffDiskFrame hC q) n := by
  cases n <;> simp only [cylinderNode, Nat.lt_irrefl, ite_false, ite_true]

theorem cylinderNode_high {j : ℕ} (h : n ≤ j) :
    cylinderNode hC q n (j+1) = cylinderNext hC q n (cylinderNode hC q n j) := by
  simp only [cylinderNode, ite_eq_right (show ¬ j+1 < n by omega),
    ite_eq_right (show ¬ j+1 = n by omega)]

noncomputable def cylinderStep (j : ℕ) :
    CylinderNode.Step (cylinderNode hC q n j) (cylinderNode hC q n (j+1)) := by
  by_cases h : j < n
  · by_cases h' : j+1 < n
    · rw [cylinderNode_low hC q n h, cylinderNode_low hC q n h']
      exact CylinderNode.stationaryStep _ _
    · have e : j+1 = n := by omega
      rw [cylinderNode_low hC q n h]
      have hc : cylinderNode hC q n (j+1) = CylinderNode.critical (cutoffDiskFrame hC q) (j+1) := by
        subst n; exact cylinderNode_critical hC q (j+1)
      rw [hc]
      exact CylinderNode.criticalStep _ _
  · rw [cylinderNode_high hC q n (by omega)]
    exact cylinderNextStep hC q n _

noncomputable def cylinderFrame : GlobularFrame (CutoffModels C q) where
  obj j := (cylinderNode hC q n j).obj
  bd j := (cylinderNode hC q n j).bd
  inc j := (cylinderNode hC q n j).inc
  left j := (cylinderStep hC q n j).left
  right j := (cylinderStep hC q n j).right
  square j := (cylinderStep hC q n j).square
  initial := by
    by_cases h : n = 0
    · subst n; rw [cylinderNode_critical]
      exact (cutoffDiskFrame hC q).initial
    · rw [cylinderNode_low hC q n (by omega)]
      exact (cutoffDiskFrame hC q).initial

noncomputable def cylinderEndpoint (ε : Bool) :
    GlobularFrame.Hom (cutoffDiskFrame hC q) (cylinderFrame hC q n) where
  obj j := (cylinderNode hC q n j).endpoint ε
  bd j := (cylinderNode hC q n j).bdEnd ε
  inc j := (cylinderNode hC q n j).comm ε
  left j := (cylinderStep hC q n j).end_left ε
  right j := (cylinderStep hC q n j).end_right ε

end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] (B : GlobularFrame K)

theorem homGlob_faceMap (Y : K) {j k : ℕ} (h : j < k) (ε : Bool)
    (a : B.obj k ⟶ Y) : (B.homGlob Y).faceMap h ε a = B.diagram.face h ε ≫ a := by
  induction k, h using Nat.le_induction with
  | base =>
    rw [GlobularSet.faceMap_succ, CoGlobularObject.face_succ]
    cases ε <;> rfl
  | succ k h ih =>
    erw [(B.homGlob Y).faceMap_source h ε, ih,
      ← B.diagram.face_adjacent h ε false]
    exact (Category.assoc _ _ _).symm

theorem homGlob_eval (Y : K) {j k : ℕ} (f : Globe.Face j k) (a : B.obj k ⟶ Y) :
    (B.homGlob Y).evalFace f a = B.diagram.eval f ≫ a := by
  cases f with
  | id => exact (Category.id_comp a).symm
  | face h ε => exact B.homGlob_faceMap Y h ε a

noncomputable def homGlobPresheafIso (Y : K) :
    (B.homGlob Y).presheaf ≅ (Presheaf.restrictedULiftYoneda.{v} B.diagram.functor).obj Y :=
  NatIso.ofComponents (fun _ => Equiv.toIso Equiv.ulift.symm) (by
    intro j k f
    apply ConcreteCategory.hom_ext
    intro a
    change ULift.up ((B.homGlob Y).evalFace f.unop a) = ULift.up (B.diagram.eval f.unop ≫ a)
    exact congrArg ULift.up (B.homGlob_eval Y f.unop a))

variable [HasColimitsOfSize.{0,v} K]
noncomputable abbrev realization : GlobularPresheaf.{v} ⥤ K := B.diagram.realization
noncomputable abbrev cell (S : GlobularPresheaf.{v}) (k : ℕ) (x : S.underlying.Cell k) :
    B.obj k ⟶ B.realization.obj S := B.diagram.cell S k x

noncomputable def desc {S : GlobularPresheaf.{v}} {Y : K}
    (f : GlobularSet.Hom S.underlying (B.homGlob Y)) : B.realization.obj S ⟶ Y :=
  (B.diagram.homEquiv S Y).symm
    (S.underlyingPresheafIso.inv ≫ f.presheafMap ≫ (B.homGlobPresheafIso Y).hom)

@[reassoc (attr := simp)] theorem cell_desc {S : GlobularPresheaf.{v}} {Y : K}
    (f : GlobularSet.Hom S.underlying (B.homGlob Y)) (k : ℕ) (x : S.underlying.Cell k) :
    B.cell S k x ≫ B.desc f = f.app k x := by
  have e := (B.diagram.homEquiv S Y).apply_symm_apply
    (S.underlyingPresheafIso.inv ≫ f.presheafMap ≫ (B.homGlobPresheafIso Y).hom)
  have h := congrArg (fun t : S ⟶ (Presheaf.restrictedULiftYoneda.{v} B.diagram.functor).obj Y =>
    t.app (op (Globe.mk k)) x) e
  erw [CoGlobularObject.homEquiv_app] at h
  exact congrArg ULift.down h

@[reassoc] theorem cell_face (S : GlobularPresheaf.{v}) {j k : ℕ} (f : Globe.Face j k)
    (x : S.underlying.Cell k) :
    B.diagram.eval f ≫ B.cell S k x = B.cell S j (S.map (show Globe.mk j ⟶ Globe.mk k from f).op x) := by
  have e := B.diagram.globeIso_naturality f
  have e' : B.diagram.eval f ≫ (B.diagram.globeIso k).inv =
      (B.diagram.globeIso j).inv ≫ B.realization.map (uliftYoneda.map f) := by
    rw [← Iso.inv_hom_id_assoc (B.diagram.globeIso j) (B.diagram.eval f), ← e]
    erw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  unfold cell CoGlobularObject.cell
  erw [← Category.assoc, e', Category.assoc, ← Functor.map_comp]
  congr 2
  exact (uliftYonedaEquiv_symm_map (show Globe.mk j ⟶ Globe.mk k from f).op x).symm

noncomputable def cellMap (S : GlobularPresheaf.{v}) :
    GlobularSet.Hom S.underlying (B.homGlob (B.realization.obj S)) where
  app := B.cell S
  source_app k x := by
    change B.cell S k (S.map (Globe.source k).op x) = B.diagram.source k ≫ B.cell S (k+1) x
    simpa only [CoGlobularObject.eval, Globe.source, Globe.face, CoGlobularObject.face_succ,
      CoGlobularObject.adjacent, Bool.false_eq_true, ite_false, diagram] using
      (B.cell_face S (Globe.source k) x).symm
  target_app k x := by
    change B.cell S k (S.map (Globe.target k).op x) = B.diagram.target k ≫ B.cell S (k+1) x
    simpa only [CoGlobularObject.eval, Globe.target, Globe.face, CoGlobularObject.face_succ,
      CoGlobularObject.adjacent, ite_true, diagram] using
      (B.cell_face S (Globe.target k) x).symm

noncomputable def realizeHom {S : GlobularPresheaf.{v}} {Y : K}
    (f : B.realization.obj S ⟶ Y) : GlobularSet.Hom S.underlying (B.homGlob Y) :=
  (B.cellMap S).comp (post f)

theorem hom_ext {S : GlobularPresheaf.{v}} {Y : K} {f g : B.realization.obj S ⟶ Y}
    (h : ∀ k x, B.cell S k x ≫ f = B.cell S k x ≫ g) : f = g := B.diagram.hom_ext h

@[simp] theorem realizeHom_desc {S : GlobularPresheaf.{v}} {Y : K}
    (f : GlobularSet.Hom S.underlying (B.homGlob Y)) : B.realizeHom (B.desc f) = f := by
  ext k x
  exact B.cell_desc f k x

@[simp] theorem desc_realizeHom {S : GlobularPresheaf.{v}} {Y : K}
    (f : B.realization.obj S ⟶ Y) : B.desc (B.realizeHom f) = f := by
  apply B.hom_ext
  intro k x
  exact B.cell_desc (B.realizeHom f) k x

end GlobularFrame
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularPresheaf

def homEquiv (S T : GlobularPresheaf.{v}) :
    (S ⟶ T) ≃ GlobularSet.Hom S.underlying T.underlying where
  toFun := underlyingMap
  invFun f := S.underlyingPresheafIso.inv ≫ f.presheafMap ≫ T.underlyingPresheafIso.hom
  left_inv f := by apply underlyingMap_injective; rfl
  right_inv f := by ext; rfl
end GlobularPresheaf
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasColimitsOfSize.{0,v} K]
noncomputable def realizationHomEquiv (B : GlobularFrame K) (S : GlobularPresheaf.{v}) (Y : K) :
    (B.realization.obj S ⟶ Y) ≃ GlobularSet.Hom S.underlying (B.homGlob Y) where
  toFun := B.realizeHom
  invFun := B.desc
  left_inv := B.desc_realizeHom
  right_inv := B.realizeHom_desc
end GlobularFrame
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q : ℕ)

noncomputable def cutoffCellEquiv (Y : CutoffModels C q) (j : ℕ) :
    (cutoffDisk hC q j ⟶ Y) ≃ Y.obj.underlying.Cell j :=
  ((cutoffAdjunction hC q).homEquiv (disk C j) Y).trans (cellEquiv Y.obj j)

@[simp] theorem cutoffCellEquiv_comp {Y Z : CutoffModels C q} (j : ℕ)
    (a : cutoffDisk hC q j ⟶ Y) (f : Y ⟶ Z) :
    cutoffCellEquiv hC q Z j (a ≫ f) =
      (underlyingMap f.hom).app j (cutoffCellEquiv hC q Y j a) := by
  unfold cutoffCellEquiv
  dsimp only [Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_right, cellEquiv_comp]
  rfl

@[simp] theorem cutoffDiskFrame_target (j : ℕ) :
    (cutoffDiskFrame hC q).diagram.target j = (cutoffFunctor hC q).map (targetDisk C j) := by
  change (cutoffFunctor hC q).map _ ≫ (cutoffFunctor hC q).map _ = _
  rw [← Functor.map_comp]
  exact congrArg (cutoffFunctor hC q).map (diskFrame_target C j)

@[simp] theorem cutoffCellEquiv_source {Y : CutoffModels C q} (j : ℕ)
    (a : cutoffDisk hC q (j+1) ⟶ Y) :
    cutoffCellEquiv hC q Y j ((cutoffDiskFrame hC q).diagram.source j ≫ a) =
      Y.obj.underlying.source j (cutoffCellEquiv hC q Y (j+1) a) := by
  rw [cutoffDiskFrame_source]
  unfold cutoffCellEquiv cutoffJ
  dsimp only [Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_left, cellEquiv_J]

@[simp] theorem cutoffCellEquiv_target {Y : CutoffModels C q} (j : ℕ)
    (a : cutoffDisk hC q (j+1) ⟶ Y) :
    cutoffCellEquiv hC q Y j ((cutoffDiskFrame hC q).diagram.target j ≫ a) =
      Y.obj.underlying.target j (cutoffCellEquiv hC q Y (j+1) a) := by
  rw [cutoffDiskFrame_target]
  unfold cutoffCellEquiv
  dsimp only [Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_left, cellEquiv_targetDisk]

noncomputable def cutoffDiskEvaluation (Y : CutoffModels C q) :
    GlobularSet.Hom ((cutoffDiskFrame hC q).homGlob Y) Y.obj.underlying where
  app j := cutoffCellEquiv hC q Y j
  source_app := cutoffCellEquiv_source hC q
  target_app := cutoffCellEquiv_target hC q

noncomputable def cutoffDiskCoevaluation (Y : CutoffModels C q) :
    GlobularSet.Hom Y.obj.underlying ((cutoffDiskFrame hC q).homGlob Y) where
  app j := (cutoffCellEquiv hC q Y j).symm
  source_app j x := by
    apply (cutoffCellEquiv hC q Y j).injective
    erw [Equiv.apply_symm_apply, cutoffCellEquiv_source, Equiv.apply_symm_apply]
  target_app j x := by
    apply (cutoffCellEquiv hC q Y j).injective
    erw [Equiv.apply_symm_apply, cutoffCellEquiv_target, Equiv.apply_symm_apply]

noncomputable def cutoffDiskHomEquiv (S : GlobularSet.{v}) (Y : CutoffModels C q) :
    GlobularSet.Hom S ((cutoffDiskFrame hC q).homGlob Y) ≃
      GlobularSet.Hom S Y.obj.underlying where
  toFun f := f.comp (cutoffDiskEvaluation hC q Y)
  invFun f := f.comp (cutoffDiskCoevaluation hC q Y)
  left_inv f := by ext j x; exact Equiv.symm_apply_apply _ _
  right_inv f := by ext j x; exact Equiv.apply_symm_apply _ _

variable [HasColimitsOfSize.{0,v} (CutoffModels C q)]
noncomputable def cutoffFrameHomEquiv (S : GlobularPresheaf.{v}) (Y : CutoffModels C q) :
    ((cutoffDiskFrame hC q).realization.obj S ⟶ Y) ≃
      (S ⟶ (cutoffForgetGlobular C q).obj Y) :=
  ((cutoffDiskFrame hC q).realizationHomEquiv S Y).trans
    ((cutoffDiskHomEquiv hC q S.underlying Y).trans
      (GlobularPresheaf.homEquiv S ((cutoffForgetGlobular C q).obj Y)).symm)

@[reassoc] theorem cutoffFrameHomEquiv_naturality (S : GlobularPresheaf.{v})
    {Y Z : CutoffModels C q} (a : (cutoffDiskFrame hC q).realization.obj S ⟶ Y) (b : Y ⟶ Z) :
    cutoffFrameHomEquiv hC q S Z (a ≫ b) =
      cutoffFrameHomEquiv hC q S Y a ≫ (cutoffForgetGlobular C q).map b := by
  apply GlobularPresheaf.underlyingMap_injective
  ext j x
  change cutoffCellEquiv hC q Z j ((cutoffDiskFrame hC q).cell S j x ≫ (a ≫ b)) =
    (underlyingMap b.hom).app j
      (cutoffCellEquiv hC q Y j ((cutoffDiskFrame hC q).cell S j x ≫ a))
  erw [← Category.assoc, cutoffCellEquiv_comp]

noncomputable def cutoffFrameFreeIso (S : GlobularPresheaf.{v}) :
    (cutoffFreeGlobular hC q).obj S ≅ (cutoffDiskFrame hC q).realization.obj S := by
  let U := cutoffForgetGlobular C q
  let A := cutoffGlobularAdjunction hC q
  let P := (cutoffDiskFrame hC q).realization.obj S
  let E (Y : CutoffModels C q) := cutoffFrameHomEquiv hC q S Y
  let f := (A.homEquiv S P).symm (E P (𝟙 P))
  let g := (E ((cutoffFreeGlobular hC q).obj S)).symm (A.unit.app S)
  have hf : A.homEquiv S P f = E P (𝟙 P) := (A.homEquiv S P).apply_symm_apply _
  have hg : E ((cutoffFreeGlobular hC q).obj S) g = A.unit.app S := (E _).apply_symm_apply _
  refine ⟨f, g, ?_, ?_⟩
  · apply (A.homEquiv S _).injective
    erw [Adjunction.homEquiv_naturality_right, hf, Adjunction.homEquiv_id]
    change E P (𝟙 P) ≫ U.map g = _
    erw [← cutoffFrameHomEquiv_naturality, Category.id_comp]
    exact hg
  · apply (E P).injective
    change E P (g ≫ f) = E P (𝟙 P)
    erw [cutoffFrameHomEquiv_naturality, hg]
    exact hf

theorem cutoffFrame_cofibrant (S : GlobularPresheaf.{v}) :
    Cofibrant hC q ((cutoffDiskFrame hC q).realization.obj S) := by
  let e := cutoffFrameFreeIso hC q S
  intro P Q p hp f
  exact Cofibrant.retract (cutoffFreeGlobular_cofibrant hC q S) e.inv e.hom e.inv_hom_id p hp f
end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularSet

def ulift (X : GlobularSet.{0}) : GlobularSet.{v} where
  Cell j := ULift.{v} (X.Cell j)
  source j x := ⟨X.source j x.down⟩
  target j x := ⟨X.target j x.down⟩
  source_source j x := congrArg ULift.up (X.source_source j x.down)
  target_source j x := congrArg ULift.up (X.target_source j x.down)

theorem ulift_faceMap (X : GlobularSet.{0}) {j k : ℕ} (h : j < k) (ε : Bool)
    (x : (X.ulift.{v}).Cell k) :
    (X.ulift.{v}).faceMap h ε x = ⟨X.faceMap h ε x.down⟩ := by
  induction k, h using Nat.le_induction with
  | base => rw [faceMap_succ, faceMap_succ]; cases ε <;> rfl
  | succ k h ih =>
    rw [(X.ulift.{v}).faceMap_source h ε, X.faceMap_source h ε]
    exact ih _

theorem ulift_evalFace (X : GlobularSet.{0}) {j k : ℕ} (f : Globe.Face j k)
    (x : (X.ulift.{v}).Cell k) :
    (X.ulift.{v}).evalFace f x = ⟨X.evalFace f x.down⟩ := by
  cases f with
  | id => rfl
  | face h ε => exact X.ulift_faceMap h ε x

noncomputable def uliftPresheafIso (X : GlobularSet.{0}) :
    (X.ulift.{v}).presheaf ≅ GlobularPresheaf.liftSmall.obj X.presheaf :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro j k f
    apply ConcreteCategory.hom_ext
    intro x
    exact X.ulift_evalFace f.unop x)

def uliftWhiskerTo (X : GlobularSet.{0}) (n : ℕ) (ε : Bool) :
    Hom ((X.whisker n ε).ulift.{v}) ((X.ulift.{v}).whisker n ε) where
  app _ x := match x.down with
    | .base j x => .base j ⟨x⟩
    | .tip x => .tip ⟨x⟩
    | .edge x => .edge ⟨x⟩
  source_app j x := by
    rcases x with ⟨x⟩
    cases x with
    | base _ x => rfl
    | tip x => rfl
    | edge x => cases ε <;> rfl
  target_app j x := by
    rcases x with ⟨x⟩
    cases x with
    | base _ x => rfl
    | tip x => rfl
    | edge x => cases ε <;> rfl

def uliftWhiskerFrom (X : GlobularSet.{0}) (n : ℕ) (ε : Bool) :
    Hom ((X.ulift.{v}).whisker n ε) ((X.whisker n ε).ulift.{v}) where
  app _ x := match x with
    | .base j x => ⟨.base j x.down⟩
    | .tip x => ⟨.tip x.down⟩
    | .edge x => ⟨.edge x.down⟩
  source_app j x := by
    cases x with
    | base _ x => rfl
    | tip x => rfl
    | edge x => cases ε <;> rfl
  target_app j x := by
    cases x with
    | base _ x => rfl
    | tip x => rfl
    | edge x => cases ε <;> rfl

def uliftWhiskerIso (X : GlobularSet.{0}) (n : ℕ) (ε : Bool) :
    ((X.whisker n ε).ulift.{v}).presheaf ≅ ((X.ulift.{v}).whisker n ε).presheaf where
  hom := (X.uliftWhiskerTo n ε).presheafMap
  inv := (X.uliftWhiskerFrom n ε).presheafMap
  hom_inv_id := by
    have h : (X.uliftWhiskerTo n ε).comp (X.uliftWhiskerFrom n ε) =
        Hom.id ((X.whisker n ε).ulift.{v}) := by
      ext j x
      rcases x with ⟨x⟩
      cases x <;> rfl
    exact congrArg Hom.presheafMap h
  inv_hom_id := by
    have h : (X.uliftWhiskerFrom n ε).comp (X.uliftWhiskerTo n ε) =
        Hom.id ((X.ulift.{v}).whisker n ε) := by
      ext j x
      cases x <;> rfl
    exact congrArg Hom.presheafMap h
end GlobularSet
namespace GlobularPresheaf

noncomputable def liftSmallWhiskerIso (S : GlobularPresheaf.{0}) (n : ℕ) (ε : Bool) :
    liftSmall.{v}.obj ((whiskering n ε).obj S) ≅
      (whiskering n ε).obj (liftSmall.{v}.obj S) :=
  (S.underlying.whisker n ε).uliftPresheafIso.symm ≪≫ S.underlying.uliftWhiskerIso n ε
end GlobularPresheaf
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{0,v} (CutoffModels C q)]

theorem cutoffFrame_whisker_hasFillers (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))
    (S : Shape) (ε : Bool) :
    ((cutoffDiskFrame hC q).realization.obj
      ((GlobularPresheaf.whiskering n ε).obj (GlobularPresheaf.liftSmall.obj S.realize))).obj.underlying.HasFillers := by
  let e := (cutoffFreeGlobular hC q).mapIso (GlobularPresheaf.liftSmallWhiskerIso S.realize n ε) ≪≫
    cutoffFrameFreeIso hC q _
  have h : ((smallFree hC q).obj ((GlobularPresheaf.whiskering n ε).obj S.realize)).obj.underlying.HasFillers := by
    cases ε
    · exact whiskerFree_hasFillers hC q n hnq H S
    · exact reverseWhiskerFree_hasFillers hC q n hnq H S
  exact h.retract (underlyingMap e.inv.hom) (underlyingMap e.hom.hom)
    (by
      have hh := congrArg (fun z : ((cutoffDiskFrame hC q).realization.obj
          ((GlobularPresheaf.whiskering n ε).obj (GlobularPresheaf.liftSmall.obj S.realize))) ⟶ _ =>
        underlyingMap z.hom) e.inv_hom_id
      exact hh)
end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace CylinderNode
variable {K : Type u} [Category.{v} K] [HasPushouts K]
variable {D : GlobularFrame K} {j : ℕ}
noncomputable def oneSideMap (Z : CylinderNode D j) (ε : Bool) :
    pushout (Z.bdEnd ε) (D.inc j) ⟶ Z.obj := pushout.desc Z.inc (Z.endpoint ε) (Z.comm ε)
end CylinderNode
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)]

omit [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
theorem completedCylinder_upper (j : ℕ) (hj : n < j)
    (B : CutoffModels C q) (e : Bool → (cutoffBoundary hC q j ⟶ B)) (ε : Bool) :
    (boundaryClass hC q (n+1)).rlp.llp
      ((completedCylinder hC q n j B e).oneSideMap ε) := by
  let := cutoff_hasColimits hC q
  intro X Y p hp
  exact TwoEndpoints.oneSide_lifting (cutoffI hC q j) e
    (cylinderFactor hC q n j B e).i p
    (hp _ (MorphismProperty.ofHoms.mk (⟨j,by omega⟩ : {j : ℕ // n+1 ≤ j})))
    ((cylinderFactor hC q n j B e).hi p hp) ε

omit [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
theorem cylinderNode_upper {j : ℕ} (hj : n < j) (ε : Bool) :
    (boundaryClass hC q (n+1)).rlp.llp ((cylinderNode hC q n j).oneSideMap ε) := by
  cases j with
  | zero => omega
  | succ j =>
    rw [cylinderNode_high hC q n (by omega)]
    exact completedCylinder_upper hC q n (j+1) hj _ _ ε

omit [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
theorem cylinderFrame_upper {j : ℕ} (hj : n < j) (ε : Bool) :
    (boundaryClass hC q (n+1)).rlp.llp
      (GlobularFrame.oneSidedMap (cylinderEndpoint hC q n ε) j) :=
  cylinderNode_upper hC q n hj ε

theorem cylinderNode_upper_fillers {j : ℕ} (hj : n < j) :
    (boundaryClass hC q (n+1)).rlp (terminal.from (cylinderNode hC q n j).obj) := by
  let := cutoff_hasLimits hC q
  cases j with
  | zero => omega
  | succ j =>
    rw [cylinderNode_high hC q n (by omega)]
    let F := cylinderFactor hC q n (j+1)
      (cylinderNode hC q n j).nextBoundary (cylinderNode hC q n j).nextBdEnd
    have e : terminal.from F.Z = F.p := terminal.hom_ext _ _
    exact e ▸ F.hp

end GlobularTheory.Model
namespace GlobularSet.LiftStage
variable {A : GlobularSet.{u}} {X Y : GlobularSet.{u}} {p : Hom X Y} {f : Hom A Y}

noncomputable def extendOne {n : ℕ} (a : LiftStage p f n) (hp : LiftsBoundary p (n+1)) :
    LiftStage p f (n+1) := by
  have h x : ∃ z, X.boundary (n+1) z = a.nextBoundary x ∧
      p.app (n+1) z = f.app (n+1) x := by
    apply hp
    apply Subtype.ext
    exact Prod.ext ((f.source_app n x).symm.trans (a.fac n le_rfl _).symm)
      ((f.target_app n x).symm.trans (a.fac n le_rfl _).symm)
  choose z hz hf using h
  exact a.extendTop z (fun x => congrArg (fun b => b.1.1) (hz x))
    (fun x => congrArg (fun b => b.1.2) (hz x)) hf

@[simp] theorem extendOne_old {n : ℕ} (a : LiftStage p f n) (hp : LiftsBoundary p (n+1))
    (k : ℕ) (hk : k ≤ n) (x : A.Cell k) :
    (a.extendOne hp).app k (by omega) x = a.app k hk x := by
  simp only [extendOne, extendTop, dite_eq_left hk]

noncomputable def extendBy {n : ℕ} (a : LiftStage p f n) :
    (d : ℕ) → (∀ j, n < j → j ≤ n+d → LiftsBoundary p j) → LiftStage p f (n+d)
  | 0, _ => a
  | d+1, h => (extendBy a d (fun j hj hj' => h j hj (by omega))).extendOne
      (h (n+d+1) (by omega) le_rfl)

theorem extendBy_old {n : ℕ} (a : LiftStage p f n) (d : ℕ)
    (h : ∀ j, n < j → j ≤ n+d → LiftsBoundary p j)
    (k : ℕ) (hk : k ≤ n) (x : A.Cell k) :
    (a.extendBy d h).app k (by omega) x = a.app k hk x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [extendBy, extendOne_old _ _ k (by omega)]
    exact ih _

end GlobularSet.LiftStage
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] {D B : GlobularFrame K}

structure CriticalData (e : Hom D B) (n : ℕ) (ε : Bool) where
  low : ∀ j, j < n → IsIso (e.obj j)
  iso : B.obj n ≅ D.obj (n+1)
  endpoint : e.obj n ≫ iso.hom = if ε then D.diagram.target n else D.diagram.source n

namespace CriticalData
variable {e : Hom D B} {n : ℕ} {ε : Bool} (c : CriticalData e n ε)
variable {S : GlobularSet.{v}} {Y : K}

noncomputable def stageOfFac (f : GlobularSet.Hom S (D.homGlob Y))
    (a : ∀ j, j ≤ n → S.Cell j → (B.obj j ⟶ Y))
    (ha : ∀ j hj x, e.obj j ≫ a j hj x = f.app j x) :
    GlobularSet.LiftStage (e.pre Y) f n where
  app := a
  fac := ha
  source_app j hj x := by
    let : IsIso (e.obj j) := c.low j (by omega)
    apply (cancel_epi (e.obj j)).1
    change e.obj j ≫ a j _ (S.source j x) = e.obj j ≫ B.diagram.source j ≫ a (j+1) hj x
    erw [ha, ← Category.assoc, ← e.source_naturality, Category.assoc, ha]
    exact f.source_app j x
  target_app j hj x := by
    let : IsIso (e.obj j) := c.low j (by omega)
    apply (cancel_epi (e.obj j)).1
    change e.obj j ≫ a j _ (S.target j x) = e.obj j ≫ B.diagram.target j ≫ a (j+1) hj x
    erw [ha, ← Category.assoc, ← e.target_naturality, Category.assoc, ha]
    exact f.target_app j x

noncomputable def initialCell
    (a : GlobularSet.Hom (S.whisker n ε) (D.homGlob Y))
    (j : ℕ) (hj : j ≤ n) (x : S.Cell j) : B.obj j ⟶ Y := by
  by_cases h : j < n
  · let : IsIso (e.obj j) := c.low j h
    exact inv (e.obj j) ≫ a.app j (.base j x)
  · have h' : j = n := by omega
    subst j
    exact c.iso.hom ≫ a.app (n+1) (.edge x)

theorem initialCell_low (a : GlobularSet.Hom (S.whisker n ε) (D.homGlob Y))
    (j : ℕ) (hj : j < n) (x : S.Cell j) :
    e.obj j ≫ c.initialCell a j (by omega) x = a.app j (.base j x) := by
  let : IsIso (e.obj j) := c.low j hj
  simp only [initialCell, dite_eq_left hj]
  erw [IsIso.hom_inv_id_assoc]

theorem initialCell_top (a : GlobularSet.Hom (S.whisker n ε) (D.homGlob Y))
    (x : S.Cell n) : c.initialCell a n le_rfl x = c.iso.hom ≫ a.app (n+1) (.edge x) := by
  simp only [initialCell, dite_eq_right (Nat.lt_irrefl n)]

theorem initialCell_fac (a : GlobularSet.Hom (S.whisker n ε) (D.homGlob Y))
    (j : ℕ) (hj : j ≤ n) (x : S.Cell j) :
    e.obj j ≫ c.initialCell a j hj x = a.app j (.base j x) := by
  by_cases h : j < n
  · exact c.initialCell_low a j h x
  · have hj' : j = n := by omega
    subst j
    erw [c.initialCell_top, ← Category.assoc, c.endpoint]
    cases ε with
    | false => exact (a.source_app n (.edge x)).symm
    | true => exact (a.target_app n (.edge x)).symm

noncomputable def initialStage (a : GlobularSet.Hom (S.whisker n ε) (D.homGlob Y)) :
    GlobularSet.LiftStage (e.pre Y) ((S.whiskerInclusion n ε).comp a) n :=
  c.stageOfFac _ (c.initialCell a) (c.initialCell_fac a)

end CriticalData

structure RelativeStage (e : Hom D B) {X Y : K} (p : X ⟶ Y)
    {S : GlobularSet.{v}} (f : GlobularSet.Hom S (D.homGlob X)) {m : ℕ}
    (b : GlobularSet.LiftStage (e.pre Y) (f.comp (post p)) m) (k : ℕ) (hk : k ≤ m) where
  stage : GlobularSet.LiftStage (e.pre X) f k
  fac_right : ∀ j (hj : j ≤ k) x, stage.app j hj x ≫ p = b.app j (hj.trans hk) x

namespace RelativeStage
variable [HasPushouts K] {e : Hom D B} {X Y : K} {p : X ⟶ Y}
variable {S : GlobularSet.{v}} {f : GlobularSet.Hom S (D.homGlob X)} {m k : ℕ}
variable {b : GlobularSet.LiftStage (e.pre Y) (f.comp (post p)) m} {hk : k ≤ m}

noncomputable def succ (a : RelativeStage e p f b k hk) (hk' : k+1 ≤ m)
    (hp : HasLiftingProperty (oneSidedMap e (k+1)) p) : RelativeStage e p f b (k+1) hk' := by
  let g := e.relativeMap p
  have H := e.relativeMap_liftsBoundary p (k+1) hp
  let z (x : S.Cell (k+1)) : (e.relativeGlob p).Cell (k+1) :=
    ⟨(b.app (k+1) hk' x, f.app (k+1) x), b.fac (k+1) hk' x⟩
  have hz (x : S.Cell (k+1)) :
      g.boundaryMap (k+1) (a.stage.nextBoundary x) = (e.relativeGlob p).boundary (k+1) (z x) := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · exact (a.fac_right k le_rfl (S.source k x)).trans (b.source_app k hk' x)
      · exact (a.stage.fac k le_rfl (S.source k x)).trans (f.source_app k x)
    · apply Subtype.ext
      apply Prod.ext
      · exact (a.fac_right k le_rfl (S.target k x)).trans (b.target_app k hk' x)
      · exact (a.stage.fac k le_rfl (S.target k x)).trans (f.target_app k x)
  choose l hlb hlg using fun x => H (a.stage.nextBoundary x) (z x) (hz x).symm
  let s := a.stage.extendTop l
    (fun x => congrArg (fun t => t.1.1) (hlb x))
    (fun x => congrArg (fun t => t.1.2) (hlb x))
    (fun x => congrArg (fun t => t.1.2) (hlg x))
  refine ⟨s, ?_⟩
  intro j hj x
  by_cases h : j ≤ k
  · simpa only [s, GlobularSet.LiftStage.extendTop, dite_eq_left h] using a.fac_right j h x
  · have hj' : j = k+1 := by omega
    subst j
    have hx : l x ≫ p = b.app (k+1) hk' x := congrArg (fun t => t.1.1) (hlg x)
    simpa only [s, GlobularSet.LiftStage.extendTop, dite_eq_right (by omega : ¬ k+1 ≤ k)] using hx

theorem succ_old (a : RelativeStage e p f b k hk) (hk' : k+1 ≤ m)
    (hp : HasLiftingProperty (oneSidedMap e (k+1)) p) (j : ℕ) (hj : j ≤ k) (x : S.Cell j) :
    (a.succ hk' hp).stage.app j (by omega) x = a.stage.app j hj x := by
  simp only [succ, GlobularSet.LiftStage.extendTop, dite_eq_left hj]

noncomputable def extendBy (a : RelativeStage e p f b k hk) :
    (d : ℕ) → (hd : k+d ≤ m) →
      (∀ j, k < j → j ≤ k+d → HasLiftingProperty (oneSidedMap e j) p) →
        RelativeStage e p f b (k+d) hd
  | 0, _, _ => a
  | d+1, hd, hp => (a.extendBy d (by omega) (fun j hj hj' => hp j hj (by omega))).succ hd
      (hp (k+d+1) (by omega) le_rfl)

theorem extendBy_old (a : RelativeStage e p f b k hk) (d : ℕ) (hd : k+d ≤ m)
    (hp : ∀ j, k < j → j ≤ k+d → HasLiftingProperty (oneSidedMap e j) p)
    (j : ℕ) (hj : j ≤ k) (x : S.Cell j) :
    (a.extendBy d hd hp).stage.app j (by omega) x = a.stage.app j hj x := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [extendBy, succ_old _ _ _ j (hj.trans (Nat.le_add_right k d))]
    exact ih _ _

end RelativeStage

end GlobularFrame
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularSet.LiftStage
variable {S A B : GlobularSet.{v}} {p : Hom A B} {f : Hom S B}
def restrict {n m : ℕ} (a : LiftStage p f m) (h : n ≤ m) : LiftStage p f n where
  app j hj := a.app j (hj.trans h)
  source_app j hj := a.source_app j (hj.trans h)
  target_app j hj := a.target_app j (hj.trans h)
  fac j hj := a.fac j (hj.trans h)
end GlobularSet.LiftStage
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] {D B : GlobularFrame K}
variable {e : Hom D B} {S : GlobularSet.{v}} {m : ℕ}

structure Presentation (e : Hom D B) (S : GlobularSet.{v}) (m : ℕ) where
  obj : K
  base : GlobularSet.Hom S (D.homGlob obj)
  stage : GlobularSet.LiftStage (e.pre obj) base m
  desc : ∀ {Y : K} (f : GlobularSet.Hom S (D.homGlob Y)),
    GlobularSet.LiftStage (e.pre Y) f m → (obj ⟶ Y)
  base_desc : ∀ {Y} f a j x, base.app j x ≫ desc (Y := Y) f a = f.app j x
  stage_desc : ∀ {Y} f a j hj x, stage.app j hj x ≫ desc (Y := Y) f a = a.app j hj x
  hom_ext : ∀ {Y} {f g : obj ⟶ Y},
    (∀ j x, base.app j x ≫ f = base.app j x ≫ g) →
    (∀ j hj x, stage.app j hj x ≫ f = stage.app j hj x ≫ g) → f = g

namespace Presentation
variable (V : Presentation e S m)
noncomputable def stageOn {Y : K} (f : GlobularSet.Hom S (D.homGlob Y))
    (b : V.obj ⟶ Y) (hb : ∀ j x, V.base.app j x ≫ b = f.app j x) :
    GlobularSet.LiftStage (e.pre Y) f m where
  app j hj x := V.stage.app j hj x ≫ b
  source_app j hj x := by
    change V.stage.app j _ (S.source j x) ≫ b = B.diagram.source j ≫ V.stage.app (j+1) hj x ≫ b
    erw [V.stage.source_app]
    exact Category.assoc _ _ _
  target_app j hj x := by
    change V.stage.app j _ (S.target j x) ≫ b = B.diagram.target j ≫ V.stage.app (j+1) hj x ≫ b
    erw [V.stage.target_app]
    exact Category.assoc _ _ _
  fac j hj x := by
    change e.obj j ≫ V.stage.app j hj x ≫ b = f.app j x
    have hv : e.obj j ≫ V.stage.app j hj x = V.base.app j x := V.stage.fac j hj x
    erw [← Category.assoc, hv, hb]

noncomputable def postStage {Y : K} (b : V.obj ⟶ Y) :
    GlobularSet.LiftStage (e.pre Y) (V.base.comp (post b)) m :=
  V.stageOn _ b (fun _ _ => rfl)

variable {n : ℕ} (U : Presentation e S n)
noncomputable def comparison (h : n ≤ m) : U.obj ⟶ V.obj :=
  U.desc V.base (V.stage.restrict h)

@[reassoc] theorem comparison_base (h : n ≤ m) (j : ℕ) (x : S.Cell j) :
    U.base.app j x ≫ V.comparison U h = V.base.app j x := U.base_desc _ _ j x
@[reassoc] theorem comparison_stage (h : n ≤ m) (j : ℕ) (hj : j ≤ n) (x : S.Cell j) :
    U.stage.app j hj x ≫ V.comparison U h = V.stage.app j (hj.trans h) x := U.stage_desc _ _ j hj x

variable [HasPushouts K]
theorem comparison_lifting (h : n ≤ m) {X Y : K} (p : X ⟶ Y)
    (hp : ∀ j, n < j → j ≤ m → HasLiftingProperty (oneSidedMap e j) p) :
    HasLiftingProperty (V.comparison U h) p := by
  constructor
  intro a b sq
  let f : GlobularSet.Hom S (D.homGlob X) := U.base.comp (post a)
  have hb : ∀ j x, V.base.app j x ≫ b = (f.comp (post p)).app j x := by
    intro j x
    change V.base.app j x ≫ b = (U.base.app j x ≫ a) ≫ p
    erw [Category.assoc, sq.w, ← Category.assoc, comparison_base]
  let t := V.stageOn (f.comp (post p)) b hb
  let s : RelativeStage e p f t n h :=
    ⟨U.postStage a, fun j hj x => by
      change (U.stage.app j hj x ≫ a) ≫ p = V.stage.app j (hj.trans h) x ≫ b
      erw [Category.assoc, sq.w, ← Category.assoc, comparison_stage]⟩
  let d := m-n
  have hd : n+d = m := Nat.add_sub_of_le h
  let z := s.extendBy d (by omega) (fun j hj hj' => hp j hj (by omega))
  let l := V.desc f (z.stage.restrict (by omega : m ≤ n+d))
  have hl₁ : V.comparison U h ≫ l = a := by
    apply U.hom_ext
    · intro j x
      erw [← Category.assoc, comparison_base, V.base_desc]
      rfl
    · intro j hj x
      erw [← Category.assoc, comparison_stage, V.stage_desc]
      change z.stage.app j _ x = U.stage.app j hj x ≫ a
      exact s.extendBy_old d _ _ j hj x
  have hl₂ : l ≫ p = b := by
    apply V.hom_ext
    · intro j x
      erw [← Category.assoc, V.base_desc]
      exact (hb j x).symm
    · intro j hj x
      erw [← Category.assoc, V.stage_desc]
      exact z.fac_right j (by omega) x
  exact CommSq.HasLift.mk' ⟨l, hl₁, hl₂⟩

end Presentation
end GlobularFrame
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularSet

def whiskerDescOriented {X Y : GlobularSet.{u}} (n : ℕ) (ε : Bool) (f : Hom X Y)
    (e : X.Cell n → Y.Cell (n+1))
    (he : ∀ x, (if ε then Y.target n else Y.source n) (e x) = f.app n x) :
    Hom (X.whisker n ε) Y where
  app _ x := match x with
    | .base k x => f.app k x
    | .tip x => (if ε then Y.source n else Y.target n) (e x)
    | .edge x => e x
  source_app k x := by
    cases x with
    | base _ x => exact f.source_app k x
    | tip x =>
      cases ε <;> simp only [Bool.false_eq_true, ↓reduceIte] at he
      · change f.app k (X.source k x) = Y.source k (Y.target (k+1) (e x))
        rw [f.source_app, ← he, Y.source_source]
      · change f.app k (X.source k x) = Y.source k (Y.source (k+1) (e x))
        rw [f.source_app, ← he, Y.source_source]
    | edge x => cases ε <;> first | exact (he x).symm | rfl
  target_app k x := by
    cases x with
    | base _ x => exact f.target_app k x
    | tip x =>
      cases ε <;> simp only [Bool.false_eq_true, ↓reduceIte] at he
      · change f.app k (X.target k x) = Y.target k (Y.target (k+1) (e x))
        rw [f.target_app, ← he, Y.target_source]
      · change f.app k (X.target k x) = Y.target k (Y.source (k+1) (e x))
        rw [f.target_app, ← he, Y.target_source]
    | edge x => cases ε <;> first | exact (he x).symm | rfl

end GlobularSet
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasColimitsOfSize.{0,v} K]
variable {D B : GlobularFrame K} {e : Hom D B}

namespace CriticalData
variable {n : ℕ} {ε : Bool} (c : CriticalData e n ε) {S : GlobularSet.{v}} {Y : K}

noncomputable def whiskerDiagram (f : GlobularSet.Hom S (D.homGlob Y))
    (a : GlobularSet.LiftStage (e.pre Y) f n) :
    GlobularSet.Hom (S.whisker n ε) (D.homGlob Y) :=
  GlobularSet.whiskerDescOriented n ε f (fun x => c.iso.inv ≫ a.app n le_rfl x) (by
    intro x
    have he := c.endpoint
    cases ε <;> simp only [Bool.false_eq_true, ↓reduceIte] at he ⊢
    all_goals
      change _ ≫ c.iso.inv ≫ a.app n le_rfl x = f.app n x
      erw [← he, Category.assoc, Iso.hom_inv_id_assoc]
      exact a.fac n le_rfl x)

noncomputable def whiskerPresentation (S : GlobularSet.{v}) : Presentation e S n where
  obj := D.realization.obj (S.whisker n ε).presheaf
  base := (S.whiskerInclusion n ε).comp
    ((S.whisker n ε).toPresheafUnderlying.comp (D.cellMap _))
  stage := c.initialStage ((S.whisker n ε).toPresheafUnderlying.comp (D.cellMap _))
  desc f a := D.desc ((S.whisker n ε).presheafUnderlyingMap.comp (c.whiskerDiagram f a))
  base_desc f a j x := D.cell_desc (S := (S.whisker n ε).presheaf) _ j (.base j x)
  stage_desc f a j hj x := by
    by_cases h : j < n
    · let : IsIso (e.obj j) := c.low j h
      apply (cancel_epi (e.obj j)).1
      change e.obj j ≫ c.initialCell _ j hj x ≫ _ = e.obj j ≫ a.app j hj x
      rw [← Category.assoc, c.initialCell_fac]
      erw [D.cell_desc]
      exact (a.fac j hj x).symm
    · have hj' : j = n := by omega
      subst j
      change c.initialCell _ n le_rfl x ≫ _ = a.app n le_rfl x
      rw [c.initialCell_top]
      change (c.iso.hom ≫ D.cell (S.whisker n ε).presheaf (n+1) (.edge x)) ≫ _ = _
      erw [Category.assoc, D.cell_desc]
      change c.iso.hom ≫ c.iso.inv ≫ a.app n le_rfl x = _
      exact c.iso.hom_inv_id_assoc _
  hom_ext := by
    intro Y f g hb hs
    have hd := GlobularSet.whisker_hom_ext n ε
      ((S.whisker n ε).toPresheafUnderlying.comp (D.realizeHom f))
      ((S.whisker n ε).toPresheafUnderlying.comp (D.realizeHom g)) hb (by
        intro x
        have h := hs n le_rfl x
        change c.initialCell _ n le_rfl x ≫ f = c.initialCell _ n le_rfl x ≫ g at h
        rw [c.initialCell_top] at h
        change (c.iso.hom ≫ D.cell (S.whisker n ε).presheaf (n+1) (.edge x)) ≫ f =
          (c.iso.hom ≫ D.cell (S.whisker n ε).presheaf (n+1) (.edge x)) ≫ g at h
        simp only [Category.assoc] at h
        exact (cancel_epi c.iso.hom).1 h)
    apply D.hom_ext
    intro j x
    exact congrFun (congrArg (fun z => z.app j) hd) x
end CriticalData

namespace Presentation
variable (e : Hom D B) (S : GlobularSet.{v}) (m : ℕ)
variable (hm : ∀ j, m < j → IsEmpty (S.Cell j))

noncomputable def fullStage (Y : K) (f : GlobularSet.Hom S (B.homGlob Y)) :
    GlobularSet.LiftStage (e.pre Y) (f.comp (e.pre Y)) m where
  app j _ := f.app j
  source_app j _ := f.source_app j
  target_app j _ := f.target_app j
  fac _ _ _ := rfl

noncomputable def full : Presentation e S m where
  obj := B.realization.obj S.presheaf
  base := (S.toPresheafUnderlying.comp (B.cellMap _)).comp (e.pre _)
  stage := fullStage e S m _ (S.toPresheafUnderlying.comp (B.cellMap _))
  desc f a := B.desc (S.presheafUnderlyingMap.comp
    { app := fun j x => if hj : j ≤ m then a.app j hj x else (hm j (by omega)).elim x
      source_app := by
        intro j x
        by_cases h : j+1 ≤ m
        · rw [dite_eq_left (by omega), dite_eq_left h]
          exact a.source_app j h x
        · exact (hm (j+1) (by omega)).elim x
      target_app := by
        intro j x
        by_cases h : j+1 ≤ m
        · rw [dite_eq_left (by omega), dite_eq_left h]
          exact a.target_app j h x
        · exact (hm (j+1) (by omega)).elim x })
  base_desc f a j x := by
    change (e.obj j ≫ B.cell S.presheaf j x) ≫ B.desc _ = f.app j x
    erw [Category.assoc, B.cell_desc]
    by_cases hj : j ≤ m
    · dsimp only [GlobularSet.Hom.comp, GlobularSet.presheafUnderlyingMap]
      rw [dite_eq_left hj]
      exact a.fac j hj x
    · exact (hm j (by omega)).elim x
  stage_desc f a j hj x := by
    change B.cell S.presheaf j x ≫ B.desc _ = _
    erw [B.cell_desc]
    dsimp only [GlobularSet.Hom.comp, GlobularSet.presheafUnderlyingMap]
    rw [dite_eq_left hj]
    rfl
  hom_ext := by
    intro Y f g _ hs
    apply B.hom_ext
    intro j x
    by_cases hj : j ≤ m
    · exact hs j hj x
    · exact (hm j (by omega)).elim x
end Presentation
end GlobularFrame
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularSet.LiftStage
variable {A X Y : GlobularSet.{v}} {p : Hom X Y} {f : Hom A Y} {m : ℕ}
theorem evalFace_app (s : LiftStage p f m) {k j : ℕ} (a : Globe.Face k j)
    (hj : j ≤ m) (hk : k ≤ m) (x : A.Cell j) :
    s.app k hk (A.evalFace a x) = X.evalFace a (s.app j hj x) := by
  cases a with
  | id => rfl
  | @face j h side =>
    change s.app k hk (A.faceMap h side x) = X.faceMap h side (s.app j hj x)
    induction j, h using Nat.le_induction with
    | base =>
      simp only [GlobularSet.faceMap_succ]
      cases side
      · exact s.source_app k hj x
      · exact s.target_app k hj x
    | succ j h ih =>
      rw [A.faceMap_source h side, X.faceMap_source h side, ← s.source_app j hj]
      exact ih (by omega) (A.source j x)
end GlobularSet.LiftStage
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] (B : GlobularFrame K)

def diskDiagram (j : ℕ) {Y : K} (a : B.obj j ⟶ Y) :
    GlobularSet.Hom (GlobularPresheaf.disk.{v} j).underlying (B.homGlob Y) where
  app k x := B.diagram.eval x.down ≫ a
  source_app k x := by
    change B.diagram.eval ((Globe.source k) ≫ x.down) ≫ a =
      B.diagram.source k ≫ B.diagram.eval x.down ≫ a
    have h := B.diagram.functor.map_comp (Globe.source k) x.down
    change B.diagram.eval _ = B.diagram.eval (Globe.source k) ≫ B.diagram.eval x.down at h
    erw [h, Category.assoc]
    congr 1
    exact CoGlobularObject.face_succ _ _ false
  target_app k x := by
    change B.diagram.eval ((Globe.target k) ≫ x.down) ≫ a =
      B.diagram.target k ≫ B.diagram.eval x.down ≫ a
    have h := B.diagram.functor.map_comp (Globe.target k) x.down
    change B.diagram.eval _ = B.diagram.eval (Globe.target k) ≫ B.diagram.eval x.down at h
    erw [h, Category.assoc]
    congr 1
    exact CoGlobularObject.face_succ _ _ true

theorem diskDiagram_cell {j : ℕ} {Y : K}
    (f : GlobularSet.Hom (GlobularPresheaf.disk.{v} j).underlying (B.homGlob Y))
    (k : ℕ) (x : (GlobularPresheaf.disk.{v} j).underlying.Cell k) :
    f.app k x = B.diagram.eval x.down ≫ f.app j ⟨𝟙 _⟩ := by
  have h := f.evalFace_app x.down ⟨𝟙 _⟩
  erw [GlobularPresheaf.underlying_evalFace] at h
  change f.app k ⟨x.down ≫ 𝟙 _⟩ = _ at h
  rw [Category.comp_id] at h
  exact h.trans (B.homGlob_eval _ _ _)

noncomputable def boundaryCell (j k : ℕ) (hk : k ≤ j) (ε : Bool) : B.obj k ⟶ B.bd (j+1) :=
  if h : k = j then eqToHom (congrArg B.obj h) ≫ (if ε then B.right j else B.left j)
  else B.diagram.face (by omega : k < j) ε ≫ B.left j

theorem boundaryCell_top (j : ℕ) (ε : Bool) :
    B.boundaryCell j j le_rfl ε = if ε then B.right j else B.left j := by
  simp only [boundaryCell, dite_eq_left rfl, eqToHom_refl, Category.id_comp]
theorem boundaryCell_low {j k : ℕ} (h : k < j) (ε : Bool) :
    B.boundaryCell j k (by omega) ε = B.diagram.face h ε ≫ B.left j := by
  simp only [boundaryCell, dite_eq_right (show k ≠ j by omega)]
  rfl

@[reassoc] theorem boundaryCell_inc (j k : ℕ) (hk : k ≤ j) (ε : Bool) :
    B.boundaryCell j k hk ε ≫ B.inc (j+1) = B.diagram.face (by omega : k < j+1) ε := by
  by_cases h : k = j
  · subst k
    rw [B.boundaryCell_top, CoGlobularObject.face_succ]
    cases ε <;> rfl
  · have hk' : k < j := by omega
    erw [B.boundaryCell_low hk', Category.assoc]
    exact B.diagram.face_adjacent hk' ε false

theorem boundaryCell_adjacent (j k : ℕ) (hk : k+1 ≤ j) (ε δ : Bool) :
    B.diagram.adjacent k δ ≫ B.boundaryCell j (k+1) hk ε =
      B.boundaryCell j k (by omega) δ := by
  by_cases h : k+1 = j
  · subst j
    rw [B.boundaryCell_top, B.boundaryCell_low (Nat.lt_succ_self k),
      CoGlobularObject.face_succ]
    cases ε with
    | false => rfl
    | true =>
      cases δ <;> change (_ ≫ B.inc (k+1)) ≫ B.right (k+1) =
        (_ ≫ B.inc (k+1)) ≫ B.left (k+1)
      all_goals
        exact (Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) (B.square (k+1)).w.symm).trans
            (Category.assoc _ _ _).symm)
  · have hk' : k+1 < j := by omega
    erw [B.boundaryCell_low hk', B.boundaryCell_low (by omega : k < j), ← Category.assoc]
    erw [← B.diagram.face_succ k δ, B.diagram.face_comp]

noncomputable def boundaryApp (j k : ℕ) (hk : k ≤ j)
    (x : (GlobularPresheaf.disk.{v} (j+1)).underlying.Cell k) : B.obj k ⟶ B.bd (j+1) := by
  change ULift.{v} (Globe.Face _ (j+1)) at x
  rcases x with ⟨x⟩
  cases x with
  | id => exfalso; change j+1 ≤ j at hk; omega
  | face _ ε => exact B.boundaryCell j k hk ε

@[simp] theorem boundaryApp_face (j k : ℕ) (hk : k ≤ j) (ε : Bool) :
    B.boundaryApp j k hk ⟨Globe.Face.face (by omega : k < j+1) ε⟩ = B.boundaryCell j k hk ε := rfl

theorem boundaryApp_source (j k : ℕ) (hk : k+1 ≤ j)
    (x : (GlobularPresheaf.disk.{v} (j+1)).underlying.Cell (k+1)) :
    B.boundaryApp j k (by omega) ((GlobularPresheaf.disk (j+1)).underlying.source k x) =
      B.diagram.source k ≫ B.boundaryApp j (k+1) hk x := by
  change ULift.{v} (Globe.Face _ (j+1)) at x
  rcases x with ⟨x⟩
  cases x with
  | id => exfalso; change j+1 ≤ j at hk; omega
  | face h ε => exact (B.boundaryCell_adjacent j k hk ε false).symm
theorem boundaryApp_target (j k : ℕ) (hk : k+1 ≤ j)
    (x : (GlobularPresheaf.disk.{v} (j+1)).underlying.Cell (k+1)) :
    B.boundaryApp j k (by omega) ((GlobularPresheaf.disk (j+1)).underlying.target k x) =
      B.diagram.target k ≫ B.boundaryApp j (k+1) hk x := by
  change ULift.{v} (Globe.Face _ (j+1)) at x
  rcases x with ⟨x⟩
  cases x with
  | id => exfalso; change j+1 ≤ j at hk; omega
  | face h ε => exact (B.boundaryCell_adjacent j k hk ε true).symm

@[reassoc] theorem boundaryApp_inc (j k : ℕ) (hk : k ≤ j)
    (x : (GlobularPresheaf.disk.{v} (j+1)).underlying.Cell k) :
    B.boundaryApp j k hk x ≫ B.inc (j+1) = B.diagram.eval x.down := by
  change ULift.{v} (Globe.Face _ (j+1)) at x
  rcases x with ⟨x⟩
  cases x with
  | id => exfalso; change j+1 ≤ j at hk; omega
  | face h ε => exact B.boundaryCell_inc j k hk ε

variable {D : GlobularFrame K}
namespace Hom
variable {B}
variable (e : Hom D B)
@[reassoc] theorem face_naturality {j k : ℕ} (h : j < k) (ε : Bool) :
    D.diagram.face h ε ≫ e.obj k = e.obj j ≫ B.diagram.face h ε := by
  induction k, h using Nat.le_induction with
  | base =>
    rw [CoGlobularObject.face_succ, CoGlobularObject.face_succ]
    cases ε
    · exact e.source_naturality j
    · exact e.target_naturality j
  | succ k h ih =>
    erw [← D.diagram.face_adjacent h ε false, Category.assoc, e.source_naturality,
      ← Category.assoc, ih, Category.assoc, B.diagram.face_adjacent h ε false]
    rfl

@[reassoc] theorem boundaryCell_naturality (j k : ℕ) (hk : k ≤ j) (ε : Bool) :
    D.boundaryCell j k hk ε ≫ e.bd (j+1) = e.obj k ≫ B.boundaryCell j k hk ε := by
  by_cases h : k = j
  · subst k
    rw [D.boundaryCell_top, B.boundaryCell_top]
    cases ε
    · exact e.left j
    · exact e.right j
  · have hk' : k < j := by omega
    erw [D.boundaryCell_low hk', B.boundaryCell_low hk', Category.assoc, e.left,
      ← Category.assoc, e.face_naturality, Category.assoc]
    rfl

@[reassoc] theorem boundaryApp_naturality (j k : ℕ) (hk : k ≤ j)
    (x : (GlobularPresheaf.disk.{v} (j+1)).underlying.Cell k) :
    D.boundaryApp j k hk x ≫ e.bd (j+1) = e.obj k ≫ B.boundaryApp j k hk x := by
  change ULift.{v} (Globe.Face _ (j+1)) at x
  rcases x with ⟨x⟩
  cases x with
  | id => exfalso; change j+1 ≤ j at hk; omega
  | face h ε => exact e.boundaryCell_naturality j k hk ε
end Hom
end GlobularFrame
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] {D B : GlobularFrame K}

namespace Presentation
variable {e : Hom D B} {j : ℕ} {Y : K}
variable (f : GlobularSet.Hom (GlobularPresheaf.disk.{v} (j+1)).underlying (D.homGlob Y))
variable (a : GlobularSet.LiftStage (e.pre Y) f j)

noncomputable def boundaryDesc : B.bd (j+1) ⟶ Y :=
  ((B.boundaryEquiv (j+1)).equiv Y).symm (a.nextBoundary ⟨𝟙 _⟩)

@[reassoc] theorem boundaryDesc_left :
    B.left j ≫ boundaryDesc f a = a.app j le_rfl ⟨Globe.source j⟩ := by
  have h := ((B.boundaryEquiv (j+1)).equiv Y).apply_symm_apply (a.nextBoundary ⟨𝟙 _⟩)
  exact congrArg (fun b => b.1.1) h
@[reassoc] theorem boundaryDesc_right :
    B.right j ≫ boundaryDesc f a = a.app j le_rfl ⟨Globe.target j⟩ := by
  have h := ((B.boundaryEquiv (j+1)).equiv Y).apply_symm_apply (a.nextBoundary ⟨𝟙 _⟩)
  exact congrArg (fun b => b.1.2) h

@[reassoc] theorem boundaryApp_desc (k : ℕ) (hk : k ≤ j)
    (x : (GlobularPresheaf.disk.{v} (j+1)).underlying.Cell k) :
    B.boundaryApp j k hk x ≫ boundaryDesc f a = a.app k hk x := by
  change ULift.{v} (Globe.Face k (j+1)) at x
  rcases x with ⟨x⟩
  cases x with
  | id => exfalso; change j+1 ≤ j at hk; omega
  | face h ε =>
    rw [B.boundaryApp_face]
    by_cases hk' : k = j
    · subst k
      rw [B.boundaryCell_top]
      cases ε
      · exact boundaryDesc_left f a
      · exact boundaryDesc_right f a
    · have hk' : k < j := by omega
      erw [B.boundaryCell_low hk', Category.assoc, boundaryDesc_left]
      have h := a.evalFace_app (Globe.Face.face hk' ε) le_rfl hk ⟨Globe.source j⟩
      erw [B.homGlob_eval, GlobularPresheaf.underlying_evalFace] at h
      exact h.symm

theorem boundaryDesc_comm :
    e.bd (j+1) ≫ boundaryDesc f a = D.inc (j+1) ≫ f.app (j+1) ⟨𝟙 _⟩ := by
  apply (D.square j).hom_ext
  · rw [← Category.assoc, e.left, Category.assoc, boundaryDesc_left]
    exact (a.fac j le_rfl ⟨Globe.source j⟩).trans
      ((D.diskDiagram_cell f j ⟨Globe.source j⟩).trans (by
        change D.diagram.face (Nat.lt_succ_self j) false ≫ _ = _
        rw [CoGlobularObject.face_succ]
        exact Category.assoc _ _ _))
  · rw [← Category.assoc, e.right, Category.assoc, boundaryDesc_right]
    exact (a.fac j le_rfl ⟨Globe.target j⟩).trans
      ((D.diskDiagram_cell f j ⟨Globe.target j⟩).trans (by
        change D.diagram.face (Nat.lt_succ_self j) true ≫ _ = _
        rw [CoGlobularObject.face_succ]
        exact Category.assoc _ _ _))

variable [HasPushouts K]
noncomputable def oneSidedStage (e : Hom D B) (j : ℕ) :
    GlobularSet.LiftStage (e.pre (oneSided e (j+1)))
      (D.diskDiagram (j+1) (pushout.inr (e.bd (j+1)) (D.inc (j+1)))) j where
  app k hk x := B.boundaryApp j k hk x ≫ pushout.inl _ _
  source_app k hk x := by
    change B.boundaryApp j k _ _ ≫ _ = B.diagram.source k ≫ B.boundaryApp j (k+1) hk x ≫ _
    erw [B.boundaryApp_source]
    exact Category.assoc _ _ _
  target_app k hk x := by
    change B.boundaryApp j k _ _ ≫ _ = B.diagram.target k ≫ B.boundaryApp j (k+1) hk x ≫ _
    erw [B.boundaryApp_target]
    exact Category.assoc _ _ _
  fac k hk x := by
    change e.obj k ≫ B.boundaryApp j k hk x ≫ _ = D.diagram.eval x.down ≫ _
    erw [← Category.assoc, ← e.boundaryApp_naturality, Category.assoc,
      pushout.condition, ← Category.assoc, D.boundaryApp_inc]
    rfl

noncomputable def oneSidedPresentation (e : Hom D B) (j : ℕ) :
    Presentation e (GlobularPresheaf.disk.{v} (j+1)).underlying j where
  obj := oneSided e (j+1)
  base := D.diskDiagram (j+1) (pushout.inr _ _)
  stage := oneSidedStage e j
  desc f a := pushout.desc (boundaryDesc f a) (f.app (j+1) ⟨𝟙 _⟩) (boundaryDesc_comm f a)
  base_desc f a k x := by
    change (D.diagram.eval x.down ≫ pushout.inr _ _) ≫ _ = _
    erw [Category.assoc, pushout.inr_desc]
    exact (D.diskDiagram_cell f k x).symm
  stage_desc f a k hk x := by
    change (B.boundaryApp j k hk x ≫ pushout.inl _ _) ≫ _ = _
    erw [Category.assoc, pushout.inl_desc]
    exact boundaryApp_desc f a k hk x
  hom_ext := by
    intro Y f g hb hs
    apply pushout.hom_ext
    · apply (B.square j).hom_ext
      · have h := hs j le_rfl ⟨Globe.source j⟩
        change (B.boundaryCell j j le_rfl false ≫ _) ≫ f = (B.boundaryCell j j le_rfl false ≫ _) ≫ g at h
        rw [B.boundaryCell_top] at h
        exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))
      · have h := hs j le_rfl ⟨Globe.target j⟩
        change (B.boundaryCell j j le_rfl true ≫ _) ≫ f = (B.boundaryCell j j le_rfl true ≫ _) ≫ g at h
        rw [B.boundaryCell_top] at h
        exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))
    · have h := hb (j+1) ⟨𝟙 _⟩
      change (𝟙 _ ≫ pushout.inr _ _) ≫ f = (𝟙 _ ≫ pushout.inr _ _) ≫ g at h
      simpa only [Category.id_comp] using h
end Presentation
end GlobularFrame
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularPresheaf
noncomputable def liftSmallDiskIso (j : ℕ) : liftSmall.{v}.obj (disk.{0} j) ≅ disk.{v} j :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun x => ⟨x.down.down⟩
      invFun := fun x => ⟨⟨x.down⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) (by intros; rfl)
end GlobularPresheaf
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)

theorem hasFillers_of_iso {X Y : CutoffModels C q} (e : X ≅ Y)
    (hX : X.obj.underlying.HasFillers) : Y.obj.underlying.HasFillers := by
  apply hX.retract (underlyingMap e.inv.hom) (underlyingMap e.hom.hom)
  exact congrArg (fun z : Y ⟶ Y => underlyingMap z.hom) e.inv_hom_id

noncomputable def cylinderCriticalData (ε : Bool) :
    GlobularFrame.CriticalData (cylinderEndpoint hC q n ε) n ε where
  low j hj := by
    change IsIso ((cylinderNode hC q n j).endpoint ε)
    rw [cylinderNode_low hC q n hj]
    change IsIso (𝟙 _)
    infer_instance
  iso := eqToIso (congrArg CylinderNode.obj (cylinderNode_critical hC q n))
  endpoint := by
    change (cylinderNode hC q n n).endpoint ε ≫
      eqToHom (congrArg CylinderNode.obj (cylinderNode_critical hC q n)) = _
    have h (Z : CylinderNode (cutoffDiskFrame hC q) n)
        (hz : Z = CylinderNode.critical (cutoffDiskFrame hC q) n) :
        Z.endpoint ε ≫ eqToHom (congrArg CylinderNode.obj hz) =
          if ε then (cutoffDiskFrame hC q).diagram.target n else (cutoffDiskFrame hC q).diagram.source n := by
      subst Z
      exact Category.comp_id _
    exact h _ (cylinderNode_critical hC q n)

theorem cutoff_boundary_surjective_iff (X : CutoffModels C q) (j : ℕ) :
    Function.Surjective (X.obj.underlying.boundary j) ↔
      ∀ a : cutoffBoundary hC q j ⟶ X, ∃ b : cutoffDisk hC q j ⟶ X, cutoffI hC q j ≫ b = a := by
  let A := cutoffAdjunction hC q
  let R := boundaryRepresentation C j
  constructor
  · intro h a
    obtain ⟨x, hx⟩ := h (R.equiv X.obj (A.homEquiv _ X a))
    refine ⟨(A.homEquiv _ X).symm ((cellEquiv X.obj j).symm x), ?_⟩
    apply (A.homEquiv _ X).injective
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
    apply (R.equiv X.obj).injective
    change R.equiv X.obj (R.inclusion ≫ (cellEquiv X.obj j).symm x) = _
    simpa only [R.inclusion_boundary, Equiv.apply_symm_apply] using hx
  · intro h a
    obtain ⟨g, hg⟩ := h ((A.homEquiv _ X).symm ((R.equiv X.obj).symm a))
    refine ⟨cellEquiv X.obj j (A.homEquiv _ X g), ?_⟩
    have e := congrArg (A.homEquiv _ X) hg
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply] at e
    change R.inclusion ≫ A.homEquiv _ X g = _ at e
    rw [← R.inclusion_boundary, e, Equiv.apply_symm_apply]

variable [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)]
local instance smallColimits : HasColimitsOfSize.{0,v} (CutoffModels C q) :=
  hasColimitsOfSizeShrink.{0,v} (CutoffModels C q)

omit [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
theorem cutoffFrame_diskWhisker_hasFillers (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))
    (j : ℕ) (ε : Bool) :
    ((cutoffDiskFrame hC q).realization.obj
      ((GlobularPresheaf.whiskering n ε).obj (GlobularPresheaf.disk.{v} j))).obj.underlying.HasFillers := by
  apply hasFillers_of_iso (q := q)
    ((cutoffDiskFrame hC q).realization.mapIso
      ((GlobularPresheaf.whiskering n ε).mapIso (GlobularPresheaf.liftSmallDiskIso j)))
  exact cutoffFrame_whisker_hasFillers hC q n hnq H (Shape.globe j) ε

theorem cylinderNode_high_hasFillers {j : ℕ} (hj : n < j) (hnq : n ≤ q)
    (ε : Bool)
    (hA : (GlobularFrame.oneSided (cylinderEndpoint hC q n ε) j).obj.underlying.HasFillers) :
    (cylinderNode hC q n j).obj.obj.underlying.HasFillers := by
  let i := GlobularFrame.oneSidedMap (cylinderEndpoint hC q n ε) j
  have hi := cylinderFrame_upper hC q n hj ε
  apply hA.of_low_bijective (underlyingMap i.hom) n
  · intro k hk
    exact upper_cofibration_low_bijective hC q (n+1) k (hk.trans hnq) (by omega) i hi
  · intro k hk
    rw [cutoff_boundary_surjective_iff hC q]
    apply (lifting_terminal_iff _ _).1
    exact cylinderNode_upper_fillers hC q n hj _
      (MorphismProperty.ofHoms.mk (⟨k,by omega⟩ : {k : ℕ // n+1 ≤ k}))

theorem cylinder_oneSided_contractible (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1)) :
    ∀ j, n < j → ∀ ε : Bool,
      Cofibrant hC q (GlobularFrame.oneSided (cylinderEndpoint hC q n ε) j) ∧
      (GlobularFrame.oneSided (cylinderEndpoint hC q n ε) j).obj.underlying.HasFillers ∧
      (sourceClass hC q (n+1)).rlp.llp (GlobularFrame.oneSidedMap (cylinderEndpoint hC q n ε) j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj ε
    cases j with
    | zero => omega
    | succ j =>
      let e := cylinderEndpoint hC q n ε
      let U := (cylinderCriticalData hC q n ε).whiskerPresentation (GlobularPresheaf.disk.{v} (j+1)).underlying
      let V := GlobularFrame.Presentation.oneSidedPresentation e j
      let f := V.comparison U (by omega)
      have hf : (sourceClass hC q (n+1)).rlp.llp f := by
        intro X Y p hp
        exact V.comparison_lifting U (by omega) p (fun k hk hk' =>
          (ih k (by omega) hk ε).2.2 p hp)
      have hU : Cofibrant hC q U.obj := cutoffFrame_cofibrant hC q _
      have hUF : U.obj.obj.underlying.HasFillers := cutoffFrame_diskWhisker_hasFillers hC q n hnq H (j+1) ε
      have hV : Cofibrant hC q V.obj := hU.of_cofibration f
        (boundaryClass_cofibration_le hC q 0 (n+1) (Nat.zero_le _) f
          (sourceClass_cofibration_le hC q (n+1) f hf))
      have hVF : V.obj.obj.underlying.HasFillers := H f hf hU hUF
      refine ⟨hV, hVF, ?_⟩
      exact upper_boundary_is_source hC q (n+1) H _
        (cylinderFrame_upper hC q n hj ε) hV hVF
        (cylinderNode_high_hasFillers hC q n hj hnq ε hVF)

end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)]
local instance smallColimitsShapes : HasColimitsOfSize.{0,v} (CutoffModels C q) :=
  hasColimitsOfSizeShrink.{0,v} (CutoffModels C q)

omit [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
theorem Cofibrant.of_iso {X Y : CutoffModels C q} (hX : Cofibrant hC q X) (e : X ≅ Y) :
    Cofibrant hC q Y := by
  intro P Q p hp f
  exact hX.retract e.inv e.hom e.inv_hom_id p hp f

noncomputable def cylinderShape (S : Shape) : CutoffModels C q :=
  (cylinderFrame hC q n).realization.obj (GlobularPresheaf.liftSmall.obj S.realize)

theorem cylinderShape_contractible (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1)) (S : Shape) :
    Cofibrant hC q (cylinderShape hC q n S) ∧ (cylinderShape hC q n S).obj.underlying.HasFillers := by
  let T := GlobularPresheaf.liftSmall.{v}.obj S.realize
  let e := cylinderEndpoint hC q n false
  let m := max n S.height
  have hm (j : ℕ) (hj : m < j) : IsEmpty (T.underlying.Cell j) := by
    constructor
    intro x
    exact (S.2.bounded j (lt_of_le_of_lt (Nat.le_max_right n S.height) hj)).false x.down
  let U := (cylinderCriticalData hC q n false).whiskerPresentation T.underlying
  let V := GlobularFrame.Presentation.full e T.underlying m hm
  let f := V.comparison U (Nat.le_max_left _ _)
  have hf : (sourceClass hC q (n+1)).rlp.llp f := by
    intro X Y p hp
    exact V.comparison_lifting U (Nat.le_max_left _ _) p (fun k hk _ =>
      (cylinder_oneSided_contractible hC q n hnq H k hk false).2.2 p hp)
  have hU : Cofibrant hC q U.obj := cutoffFrame_cofibrant hC q _
  have hUF : U.obj.obj.underlying.HasFillers := cutoffFrame_whisker_hasFillers hC q n hnq H S false
  have hV : Cofibrant hC q V.obj := hU.of_cofibration f
    (boundaryClass_cofibration_le hC q 0 (n+1) (Nat.zero_le _) f
      (sourceClass_cofibration_le hC q (n+1) f hf))
  have hVF : V.obj.obj.underlying.HasFillers := H f hf hU hUF
  let iso := (cylinderFrame hC q n).realization.mapIso T.underlyingPresheafIso
  exact ⟨Cofibrant.of_iso hC q hV iso, hasFillers_of_iso (q := q) iso hVF⟩

theorem cylinderNode_contractible (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1)) (j : ℕ) :
    Cofibrant hC q (cylinderNode hC q n j).obj ∧
      (cylinderNode hC q n j).obj.obj.underlying.HasFillers := by
  let iso := (cylinderFrame hC q n).realization.mapIso (GlobularPresheaf.liftSmallDiskIso j) ≪≫
    (cylinderFrame hC q n).diagram.globeIso j
  have h := cylinderShape_contractible hC q n hnq H (Shape.globe j)
  exact ⟨Cofibrant.of_iso hC q h.1 iso, hasFillers_of_iso (q := q) iso h.2⟩

omit [HasColimitsOfSize.{v,v} (CutoffModels C q)] in
theorem boundary_cofibration_split {r : ℕ} {X Y : CutoffModels C q} (i : X ⟶ Y)
    (hi : (boundaryClass hC q r).rlp.llp i) (hX : X.obj.underlying.HasFillers) :
    ∃ s : Y ⟶ X, i ≫ s = 𝟙 X := by
  have hp : (boundaryClass hC q r).rlp (terminal.from X) := by
    rintro A B f ⟨⟨k,hk⟩⟩
    exact (lifting_terminal_iff _ _).2 ((cutoff_hasFillers_iff hC q _).1 hX k)
  have sq : CommSq (𝟙 X) i (terminal.from X) (terminal.from Y) := ⟨terminal.hom_ext _ _⟩
  let : sq.HasLift := (hi _ hp).sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left⟩

theorem cylinder_oneSided_split_high (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))
    {j : ℕ} (hj : n < j) (ε : Bool) :
    ∃ s : (cylinderFrame hC q n).obj j ⟶ GlobularFrame.oneSided (cylinderEndpoint hC q n ε) j,
      GlobularFrame.oneSidedMap (cylinderEndpoint hC q n ε) j ≫ s = 𝟙 _ := by
  exact boundary_cofibration_split hC q _ (cylinderFrame_upper hC q n hj ε)
    (cylinder_oneSided_contractible hC q n hnq H j hj ε).2.1

end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasColimitsOfSize.{0,v} K]

@[reassoc] theorem cell_naturality (B : GlobularFrame K) {S T : GlobularPresheaf.{v}}
    (f : S ⟶ T) (k : ℕ) (x : S.underlying.Cell k) :
    B.cell S k x ≫ B.realization.map f = B.cell T k (f.app (op (Globe.mk k)) x) := by
  unfold cell CoGlobularObject.cell
  erw [Category.assoc, ← Functor.map_comp]
  congr 2
  apply uliftYonedaEquiv.injective
  erw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

namespace Hom
variable {D B : GlobularFrame K}
noncomputable def realization (e : Hom D B) : D.realization ⟶ B.realization where
  app S := D.desc ((B.cellMap S).comp (e.pre _))
  naturality S T f := by
    apply D.hom_ext
    intro k x
    erw [cell_naturality_assoc, D.cell_desc]
    erw [← Category.assoc, D.cell_desc]
    change e.obj k ≫ B.cell T k (f.app _ x) = (e.obj k ≫ B.cell S k x) ≫ B.realization.map f
    rw [Category.assoc, cell_naturality]

@[reassoc (attr := simp)] theorem cell_realization (e : Hom D B) (S : GlobularPresheaf.{v})
    (k : ℕ) (x : S.underlying.Cell k) :
    D.cell S k x ≫ e.realization.app S = e.obj k ≫ B.cell S k x := D.cell_desc _ _ _

end Hom

noncomputable abbrev shapeRealization (B : GlobularFrame K) : Shape ⥤ K :=
  Shape.liftedRealization ⋙ B.realization
noncomputable def shapeGlobeIso (B : GlobularFrame K) (j : ℕ) :
    B.shapeRealization.obj (Shape.globe j) ≅ B.obj j :=
  B.realization.mapIso (GlobularPresheaf.liftSmallDiskIso j) ≪≫ B.diagram.globeIso j

noncomputable abbrev Hom.shapeEndpoint {D B : GlobularFrame K} (e : Hom D B) :
    D.shapeRealization ⟶ B.shapeRealization := Functor.whiskerLeft Shape.liftedRealization e.realization

@[reassoc] theorem shapeGlobeIso_cell (B : GlobularFrame K) (j : ℕ) :
    B.cell (Shape.liftedRealization.obj (Shape.globe j)) j (ULift.up (ULift.up (𝟙 (Globe.mk j)))) ≫
      (B.shapeGlobeIso j).hom = 𝟙 _ := by
  dsimp only [shapeGlobeIso, Iso.trans_hom, Functor.mapIso_hom]
  erw [cell_naturality_assoc]
  change B.diagram.cell (GlobularPresheaf.disk j) j (ULift.up (𝟙 (Globe.mk j))) ≫ _ = _
  unfold CoGlobularObject.cell
  have h : (uliftYonedaEquiv.symm (ULift.up (𝟙 (Globe.mk j))) : GlobularPresheaf.disk.{v} j ⟶ _) = 𝟙 _ := by
    apply uliftYonedaEquiv.injective
    rfl
  erw [h]
  erw [B.diagram.realization.map_id (GlobularPresheaf.disk.{v} j), Category.comp_id, Iso.inv_hom_id]
  rfl

theorem shapeGlobeIso_inv_cell (B : GlobularFrame K) (j : ℕ) :
    (B.shapeGlobeIso j).inv = B.cell (Shape.liftedRealization.obj (Shape.globe j)) j
      (ULift.up (ULift.up (𝟙 (Globe.mk j)))) := by
  apply (cancel_mono (B.shapeGlobeIso j).hom).1
  rw [Iso.inv_hom_id, shapeGlobeIso_cell]

@[reassoc] theorem shapeEndpoint_globe {D B : GlobularFrame K} (e : Hom D B) (j : ℕ) :
    (D.shapeGlobeIso j).inv ≫ e.shapeEndpoint.app (Shape.globe j) ≫ (B.shapeGlobeIso j).hom = e.obj j := by
  rw [shapeGlobeIso_inv_cell]
  calc
    _ = (e.obj j ≫ B.cell (Shape.liftedRealization.obj (Shape.globe j)) j
        (ULift.up (ULift.up (𝟙 (Globe.mk j))))) ≫ (B.shapeGlobeIso j).hom := by
      erw [← Category.assoc, Hom.cell_realization]
    _ = e.obj j ≫ (B.cell (Shape.liftedRealization.obj (Shape.globe j)) j
        (ULift.up (ULift.up (𝟙 (Globe.mk j)))) ≫ (B.shapeGlobeIso j).hom) := Category.assoc _ _ _
    _ = e.obj j ≫ 𝟙 _ := congrArg (e.obj j ≫ ·) (B.shapeGlobeIso_cell j)
    _ = e.obj j := Category.comp_id _

@[reassoc] theorem shapeGlobeIso_face (B : GlobularFrame K) {j k : ℕ} (h : j < k) (ε : Bool) :
    B.shapeRealization.map (Shape.face h ε) ≫
      (B.shapeGlobeIso k).hom = (B.shapeGlobeIso j).hom ≫ B.diagram.face h ε := by
  apply (cancel_epi (B.shapeGlobeIso j).inv).1
  erw [Iso.inv_hom_id_assoc]
  rw [shapeGlobeIso_inv_cell]
  erw [cell_naturality_assoc]
  have h' := B.cell_face (Shape.liftedRealization.obj (Shape.globe k)) (Globe.face h ε)
      (ULift.up (ULift.up (𝟙 (Globe.mk k))))
  change B.diagram.face h ε ≫ B.cell (Shape.liftedRealization.obj (Shape.globe k)) k
      (ULift.up (ULift.up (𝟙 (Globe.mk k)))) =
    B.cell (Shape.liftedRealization.obj (Shape.globe k)) j
      (ULift.up (ULift.up (Globe.face h ε))) at h'
  change B.cell (Shape.liftedRealization.obj (Shape.globe k)) j
      (ULift.up (ULift.up (Globe.face h ε))) ≫ (B.shapeGlobeIso k).hom = _
  rw [← h']
  exact (Category.assoc _ _ _).trans ((congrArg (B.diagram.face h ε ≫ ·)
    (B.shapeGlobeIso_cell k)).trans (Category.comp_id _))

end GlobularFrame
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q : ℕ)

noncomputable def representables (C : GlobularTheory.{v}) : C.Obj ⥤ C.Model where
  obj S := freeShape C S.shape
  map f := yoneda.map f
  map_id S := yoneda.map_id S
  map_comp f g := yoneda.map_comp f g

noncomputable abbrev cutoffRepresentables : C.Obj ⥤ CutoffModels C q :=
  representables C ⋙ cutoffFunctor hC q

@[reassoc] theorem shapeGlobularEquiv_left {S T : Shape} (f : S ⟶ T)
    (X : C.Model) (a : freeShape C T ⟶ X) :
    shapeGlobularEquiv S X (yoneda.map (C.base f) ≫ a) =
      Shape.liftedRealization.map f ≫ shapeGlobularEquiv T X a := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  change X.eval (C.base (S.cellArrow k x.down)) (yonedaEquiv (yoneda.map (C.base f) ≫ a)) =
    X.eval (C.base (T.cellArrow k (f.app k x.down))) (yonedaEquiv a)
  erw [← yonedaEquiv_naturality, Shape.cellArrow_naturality, C.base_comp, eval_comp]
  rfl

@[reassoc] theorem cutoffShapeEquiv_left {S T : Shape} (f : S ⟶ T)
    (Y : CutoffModels C q) (a : (cutoffRepresentables hC q).obj ⟨T⟩ ⟶ Y) :
    cutoffShapeEquiv hC q S Y ((cutoffRepresentables hC q).map (C.base f) ≫ a) =
      Shape.liftedRealization.map f ≫ cutoffShapeEquiv hC q T Y a := by
  change shapeGlobularEquiv S Y.obj
      ((cutoffAdjunction hC q).homEquiv _ Y ((cutoffFunctor hC q).map (yoneda.map (C.base f)) ≫ a)) =
    Shape.liftedRealization.map f ≫ shapeGlobularEquiv T Y.obj
      ((cutoffAdjunction hC q).homEquiv _ Y a)
  erw [Adjunction.homEquiv_naturality_left]
  exact shapeGlobularEquiv_left f Y.obj _

variable [HasColimitsOfSize.{0,v} (CutoffModels C q)]

@[reassoc] theorem cutoffFrameHomEquiv_left {S T : GlobularPresheaf.{v}} (f : S ⟶ T)
    (Y : CutoffModels C q) (a : (cutoffDiskFrame hC q).realization.obj T ⟶ Y) :
    cutoffFrameHomEquiv hC q S Y ((cutoffDiskFrame hC q).realization.map f ≫ a) =
      f ≫ cutoffFrameHomEquiv hC q T Y a := by
  apply GlobularPresheaf.underlyingMap_injective
  ext j x
  change cutoffCellEquiv hC q Y j ((cutoffDiskFrame hC q).cell S j x ≫
      (cutoffDiskFrame hC q).realization.map f ≫ a) =
    cutoffCellEquiv hC q Y j ((cutoffDiskFrame hC q).cell T j (f.app _ x) ≫ a)
  erw [GlobularFrame.cell_naturality_assoc]
  rfl

noncomputable def shapeFrameIso (S : Shape) :
    (cutoffRepresentables hC q).obj ⟨S⟩ ≅ (cutoffDiskFrame hC q).shapeRealization.obj S := by
  let A := (cutoffRepresentables hC q).obj ⟨S⟩
  let B := (cutoffDiskFrame hC q).shapeRealization.obj S
  let E (Y) := cutoffShapeEquiv hC q S Y
  let G (Y) := cutoffFrameHomEquiv hC q (Shape.liftedRealization.obj S) Y
  let f : A ⟶ B := (E B).symm (G B (𝟙 B))
  let g : B ⟶ A := (G A).symm (E A (𝟙 A))
  have hf : E B f = G B (𝟙 B) := (E B).apply_symm_apply _
  have hg : G A g = E A (𝟙 A) := (G A).apply_symm_apply _
  refine ⟨f,g,?_,?_⟩
  · apply (E A).injective
    erw [cutoffShapeEquiv_naturality, hf, ← cutoffFrameHomEquiv_naturality, Category.id_comp]
    exact hg
  · apply (G B).injective
    erw [cutoffFrameHomEquiv_naturality, hg, ← cutoffShapeEquiv_naturality, Category.id_comp]
    exact hf

@[simp] theorem shapeFrameIso_equiv (S : Shape) {Y : CutoffModels C q}
    (a : (cutoffDiskFrame hC q).shapeRealization.obj S ⟶ Y) :
    cutoffShapeEquiv hC q S Y ((shapeFrameIso hC q S).hom ≫ a) =
      cutoffFrameHomEquiv hC q (Shape.liftedRealization.obj S) Y a := by
  change cutoffShapeEquiv hC q S Y
    ((cutoffShapeEquiv hC q S _).symm (cutoffFrameHomEquiv hC q _ _ (𝟙 _)) ≫ a) = _
  erw [cutoffShapeEquiv_naturality, Equiv.apply_symm_apply,
    ← cutoffFrameHomEquiv_naturality, Category.id_comp]
  rfl

@[reassoc] theorem shapeFrameIso_naturality {S T : Shape} (f : S ⟶ T) :
    (cutoffRepresentables hC q).map (C.base f) ≫ (shapeFrameIso hC q T).hom =
      (shapeFrameIso hC q S).hom ≫ (cutoffDiskFrame hC q).shapeRealization.map f := by
  let D := cutoffDiskFrame hC q
  let Y := D.shapeRealization.obj T
  apply (cutoffShapeEquiv hC q S Y).injective
  have hh : cutoffShapeEquiv hC q T Y (shapeFrameIso hC q T).hom =
      cutoffFrameHomEquiv hC q (Shape.liftedRealization.obj T) Y (𝟙 Y) := by
    have h := shapeFrameIso_equiv hC q T (𝟙 Y)
    erw [Category.comp_id] at h
    exact h
  have hl := cutoffFrameHomEquiv_left hC q (Shape.liftedRealization.map f) Y (𝟙 Y)
  erw [Category.comp_id] at hl
  exact (cutoffShapeEquiv_left hC q f Y _).trans
    ((congrArg (fun g : Shape.liftedRealization.obj T ⟶ (cutoffForgetGlobular C q).obj Y =>
      Shape.liftedRealization.map f ≫ g) hh).trans
        (hl.symm.trans (shapeFrameIso_equiv hC q S (D.shapeRealization.map f)).symm))

omit [HasColimitsOfSize.{0,v} (CutoffModels C q)] in
@[simp] theorem cutoffShapeEquiv_top (Y : CutoffModels C q) (j : ℕ)
    (a : cutoffDisk hC q j ⟶ Y) :
    (cutoffShapeEquiv hC q (Shape.globe j) Y a).app (op (Globe.mk j))
      (ULift.up (ULift.up (𝟙 (Globe.mk j)))) = cutoffCellEquiv hC q Y j a := by
  change Y.obj.eval (C.base ((Shape.globe j).cellArrow _ (ULift.up (𝟙 (Globe.mk j))))) _ = _
  erw [Shape.cellArrow_identity, C.base_id, eval_id]
  rfl

@[simp] theorem shapeFrameIso_globe (j : ℕ) :
    (shapeFrameIso hC q (Shape.globe j)).hom = ((cutoffDiskFrame hC q).shapeGlobeIso j).inv := by
  apply (cutoffCellEquiv hC q _ j).injective
  have hh := shapeFrameIso_equiv hC q (Shape.globe j) (𝟙 _)
  erw [Category.comp_id] at hh
  have e := congrArg (fun f => f.app (op (Globe.mk j))
      (ULift.up (ULift.up (𝟙 (Globe.mk j))))) hh
  erw [cutoffShapeEquiv_top] at e
  change cutoffCellEquiv hC q _ j _ = cutoffCellEquiv hC q _ j
    ((cutoffDiskFrame hC q).cell (Shape.liftedRealization.obj (Shape.globe j)) j
      (ULift.up (ULift.up (𝟙 (Globe.mk j)))) ≫ 𝟙 _) at e
  erw [Category.comp_id, ← GlobularFrame.shapeGlobeIso_inv_cell] at e
  exact e

end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasColimitsOfSize.{0,v} K]
theorem shapeRealization_sums (B : GlobularFrame K) (S : Shape) (b h : ℕ)
    (hl : b < S.1) (hr : b < h) :
    IsPushout (B.shapeRealization.map (S.seam hl))
      (B.shapeRealization.map (Shape.face hr false))
      (B.shapeRealization.map (S.inl b h hl hr))
      (B.shapeRealization.map (S.inr b h hl hr)) :=
  (Shape.liftedRealization_pushout S b h hl hr).map B.realization
end GlobularFrame
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)]
local instance smallColimitsTheory : HasColimitsOfSize.{0,v} (CutoffModels C q) :=
  hasColimitsOfSizeShrink.{0,v} (CutoffModels C q)

noncomputable def shapeFrameNatIso :
    C.toTheoryData.arity ⋙ cutoffRepresentables hC q ≅ (cutoffDiskFrame hC q).shapeRealization :=
  NatIso.ofComponents (shapeFrameIso hC q) (fun f => shapeFrameIso_naturality hC q f)

noncomputable def cylinderShapeEndpoint (ε : Bool) :
    C.toTheoryData.arity ⋙ cutoffRepresentables hC q ⟶ (cylinderFrame hC q n).shapeRealization :=
  (shapeFrameNatIso hC q).hom ≫ (cylinderEndpoint hC q n ε).shapeEndpoint

@[reassoc] theorem cylinderShapeEndpoint_globe (ε : Bool) (j : ℕ) :
    (cylinderShapeEndpoint hC q n ε).app (Shape.globe j) ≫
      ((cylinderFrame hC q n).shapeGlobeIso j).hom = (cylinderEndpoint hC q n ε).obj j := by
  change ((shapeFrameIso hC q (Shape.globe j)).hom ≫
    (cylinderEndpoint hC q n ε).shapeEndpoint.app _) ≫ _ = _
  erw [shapeFrameIso_globe, Category.assoc]
  exact GlobularFrame.shapeEndpoint_globe _ _

theorem cutoffRepresentables_sums (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    IsPushout ((cutoffRepresentables hC q).map (C.base (S.seam hl)))
      ((cutoffRepresentables hC q).map (C.base (Shape.face hr false)))
      ((cutoffRepresentables hC q).map (C.base (S.inl b h hl hr)))
      ((cutoffRepresentables hC q).map (C.base (S.inr b h hl hr))) := by
  exact ((cutoffDiskFrame hC q).shapeRealization_sums S b h hl hr).of_iso'
    (shapeFrameIso hC q (Shape.globe b)) (shapeFrameIso hC q S)
    (shapeFrameIso hC q (Shape.globe h)) (shapeFrameIso hC q (S.attach b h hl hr))
    (shapeFrameIso_naturality hC q _).symm (shapeFrameIso_naturality hC q _).symm
    (shapeFrameIso_naturality hC q _).symm (shapeFrameIso_naturality hC q _).symm

noncomputable abbrev cylinderTheory : GlobularTheory.{v} :=
  representedTheory (cutoffRepresentables hC q) (cylinderFrame hC q n).shapeRealization
    (cylinderShapeEndpoint hC q n false) (cylinderShapeEndpoint hC q n true)
    (cylinderFrame hC q n).shapeRealization_sums (cutoffRepresentables_sums hC q)
noncomputable abbrev cylinderProjection : Morphism (cylinderTheory hC q n) C :=
  representedProjection (cutoffRepresentables hC q) (cylinderFrame hC q n).shapeRealization
    (cylinderShapeEndpoint hC q n false) (cylinderShapeEndpoint hC q n true)
    (cylinderFrame hC q n).shapeRealization_sums (cutoffRepresentables_sums hC q)

end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)]
local instance smallColimitsExtension : HasColimitsOfSize.{0,v} (CutoffModels C q) :=
  hasColimitsOfSizeShrink.{0,v} (CutoffModels C q)

omit [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
theorem cylinderShapeEndpoint_low (S : Shape) (hS : S.height < n) :
    (cylinderShapeEndpoint hC q n false).app S = (cylinderShapeEndpoint hC q n true).app S := by
  change (shapeFrameIso hC q S).hom ≫ (cylinderEndpoint hC q n false).shapeEndpoint.app S =
    (shapeFrameIso hC q S).hom ≫ (cylinderEndpoint hC q n true).shapeEndpoint.app S
  apply congrArg ((shapeFrameIso hC q S).hom ≫ ·)
  apply (cutoffDiskFrame hC q).hom_ext
  intro j x
  erw [GlobularFrame.Hom.cell_realization, GlobularFrame.Hom.cell_realization]
  change S.2.height < n at hS
  have hj : j < n := by
    by_contra h
    exact (S.2.bounded j (by omega)).false x.down
  have he : (cylinderEndpoint hC q n false).obj j = (cylinderEndpoint hC q n true).obj j := by
    change (cylinderNode hC q n j).endpoint false = (cylinderNode hC q n j).endpoint true
    rw [cylinderNode_low hC q n hj]
    rfl
  exact congrArg (· ≫ _) he

theorem completedCylinder_extend (j : ℕ) (B : CutoffModels C q)
    (e : Bool → (cutoffBoundary hC q j ⟶ B)) {Y : CutoffModels C q}
    (hY : Y.obj.underlying.HasFillers) (b : B ⟶ Y)
    (d : Bool → (cutoffDisk hC q j ⟶ Y))
    (hd : ∀ ε, e ε ≫ b = cutoffI hC q j ≫ d ε) :
    ∃ l : (completedCylinder hC q n j B e).obj ⟶ Y,
      (completedCylinder hC q n j B e).inc ≫ l = b ∧
      ∀ ε, (completedCylinder hC q n j B e).endpoint ε ≫ l = d ε := by
  let F := cylinderFactor hC q n j B e
  have hp : (boundaryClass hC q (n+1)).rlp (terminal.from Y) := by
    rintro A B f ⟨⟨k,hk⟩⟩
    exact (lifting_terminal_iff _ _).2 ((cutoff_hasFillers_iff hC q _).1 hY k)
  let a := TwoEndpoints.desc (cutoffI hC q j) e b d hd
  obtain ⟨l,hl⟩ := (lifting_terminal_iff F.i Y).1 (F.hi _ hp) a
  refine ⟨l, ?_, ?_⟩
  · change (TwoEndpoints.base _ _ ≫ F.i) ≫ l = b
    erw [Category.assoc, hl]
    exact TwoEndpoints.base_desc _ _ _ _ _
  · intro ε
    change (TwoEndpoints.endpoint _ _ ε ≫ F.i) ≫ l = d ε
    erw [Category.assoc, hl]
    exact TwoEndpoints.endpoint_desc _ _ _ _ _ _

omit [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
theorem criticalCylinder_extend {Y : CutoffModels C q}
    (hY : Y.obj.underlying.HasFillers)
    (b : (cutoffDiskFrame hC q).bd n ⟶ Y)
    (d : Bool → ((cutoffDiskFrame hC q).obj n ⟶ Y))
    (hd : ∀ ε, b = (cutoffDiskFrame hC q).inc n ≫ d ε) :
    ∃ l : (CylinderNode.critical (cutoffDiskFrame hC q) n).obj ⟶ Y,
      (CylinderNode.critical (cutoffDiskFrame hC q) n).inc ≫ l = b ∧
      ∀ ε, (CylinderNode.critical (cutoffDiskFrame hC q) n).endpoint ε ≫ l = d ε := by
  let D := cutoffDiskFrame hC q
  let a := (D.square n).desc (d false) (d true) ((hd false).symm.trans (hd true))
  obtain ⟨l,hl⟩ := (cutoff_hasFillers_iff hC q Y).1 hY (n+1) a
  have hs : D.diagram.source n ≫ l = d false := by
    change (D.left n ≫ D.inc (n+1)) ≫ l = _
    erw [Category.assoc, hl]
    exact (D.square n).inl_desc _ _ _
  have ht : D.diagram.target n ≫ l = d true := by
    change (D.right n ≫ D.inc (n+1)) ≫ l = _
    erw [Category.assoc, hl]
    exact (D.square n).inr_desc _ _ _
  refine ⟨l, ?_, ?_⟩
  · change (D.inc n ≫ D.diagram.source n) ≫ l = b
    erw [Category.assoc, hs]
    exact (hd false).symm
  · intro ε
    cases ε
    · exact hs
    · exact ht

theorem cylinderNode_extend (j : ℕ) {Y : CutoffModels C q}
    (hY : Y.obj.underlying.HasFillers) (b : (cylinderNode hC q n j).bd ⟶ Y)
    (d : Bool → (cutoffDisk hC q j ⟶ Y))
    (hd : ∀ ε, (cylinderNode hC q n j).bdEnd ε ≫ b = cutoffI hC q j ≫ d ε)
    (hlow : j < n → d false = d true) :
    ∃ l : (cylinderNode hC q n j).obj ⟶ Y,
      (cylinderNode hC q n j).inc ≫ l = b ∧
      ∀ ε, (cylinderNode hC q n j).endpoint ε ≫ l = d ε := by
  revert b
  by_cases hj : j < n
  · erw [cylinderNode_low hC q n hj]
    intro b hd
    refine ⟨d false, ?_, ?_⟩
    · have h := hd false
      exact (Category.id_comp b).symm.trans h |>.symm
    · intro ε
      cases ε
      · exact Category.id_comp _
      · exact (Category.id_comp _).trans (hlow hj)
  · by_cases he : j = n
    · subst j
      erw [cylinderNode_critical]
      intro b hd
      exact criticalCylinder_extend hC q n hY b d (fun ε => (Category.id_comp b).symm.trans (hd ε))
    · cases j with
      | zero => omega
      | succ j =>
        erw [cylinderNode_high hC q n (by omega)]
        intro b hd
        exact completedCylinder_extend hC q n _ _ _ hY b d hd

end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasColimitsOfSize.{0,v} K]

@[reassoc] theorem shapeGlobeIso_source (B : GlobularFrame K) (j : ℕ) :
    B.shapeRealization.map (Shape.source j) ≫ (B.shapeGlobeIso (j+1)).hom =
      (B.shapeGlobeIso j).hom ≫ B.diagram.source j := by
  simpa only [Shape.source, CoGlobularObject.face_succ, CoGlobularObject.adjacent, Bool.false_eq_true, ↓reduceIte]
    using B.shapeGlobeIso_face (Nat.lt_succ_self j) false

@[reassoc] theorem shapeGlobeIso_target (B : GlobularFrame K) (j : ℕ) :
    B.shapeRealization.map (Shape.target j) ≫ (B.shapeGlobeIso (j+1)).hom =
      (B.shapeGlobeIso j).hom ≫ B.diagram.target j := by
  simpa only [Shape.target, CoGlobularObject.face_succ, CoGlobularObject.adjacent, ↓reduceIte]
    using B.shapeGlobeIso_face (Nat.lt_succ_self j) true

@[reassoc] theorem shapeGlobeIso_source_inv (B : GlobularFrame K) (j : ℕ) :
    B.diagram.source j ≫ (B.shapeGlobeIso (j+1)).inv =
      (B.shapeGlobeIso j).inv ≫ B.shapeRealization.map (Shape.source j) := by
  apply (cancel_mono (B.shapeGlobeIso (j+1)).hom).1
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    shapeGlobeIso_source, Iso.inv_hom_id_assoc]

@[reassoc] theorem shapeGlobeIso_target_inv (B : GlobularFrame K) (j : ℕ) :
    B.diagram.target j ≫ (B.shapeGlobeIso (j+1)).inv =
      (B.shapeGlobeIso j).inv ≫ B.shapeRealization.map (Shape.target j) := by
  apply (cancel_mono (B.shapeGlobeIso (j+1)).hom).1
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    shapeGlobeIso_target, Iso.inv_hom_id_assoc]

end GlobularFrame
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)]
local instance smallColimitsOperations : HasColimitsOfSize.{0,v} (CutoffModels C q) :=
  hasColimitsOfSizeShrink.{0,v} (CutoffModels C q)

@[reassoc] theorem cylinderShapeEndpoint_globe_inv (ε : Bool) (j : ℕ) :
    (cylinderEndpoint hC q n ε).obj j ≫ ((cylinderFrame hC q n).shapeGlobeIso j).inv =
      (cylinderShapeEndpoint hC q n ε).app (Shape.globe j) := by
  apply (cancel_mono ((cylinderFrame hC q n).shapeGlobeIso j).hom).1
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (cylinderShapeEndpoint_globe hC q n ε j).symm

omit [HasColimitsOfSize.{v,v} (CutoffModels C q)] in
@[simp] theorem cutoffRepresentables_source (j : ℕ) :
    (cutoffRepresentables hC q).map (C.base (Shape.source j)) =
      (cutoffDiskFrame hC q).diagram.source j := by
  rw [cutoffDiskFrame_source]
  rfl

omit [HasColimitsOfSize.{v,v} (CutoffModels C q)] in
@[simp] theorem cutoffRepresentables_target (j : ℕ) :
    (cutoffRepresentables hC q).map (C.base (Shape.target j)) =
      (cutoffDiskFrame hC q).diagram.target j := by
  rw [cutoffDiskFrame_target]
  rfl

end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)]
local instance smallColimitsInterpretation : HasColimitsOfSize.{0,v} (CutoffModels C q) :=
  hasColimitsOfSizeShrink.{0,v} (CutoffModels C q)

omit [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
theorem cylinderPair_parallel (a : (cylinderTheory hC q n).AdmissiblePair) :
    (cylinderFrame hC q n).inc a.n ≫ ((cylinderFrame hC q n).shapeGlobeIso a.n).inv ≫ a.source.cylinder =
      (cylinderFrame hC q n).inc a.n ≫ ((cylinderFrame hC q n).shapeGlobeIso a.n).inv ≫ a.target.cylinder := by
  rcases a with ⟨j,S,hS,s,t,hp⟩
  cases j with
  | zero => exact (cylinderFrame hC q n).initial.hom_ext _ _
  | succ j =>
    apply ((cylinderFrame hC q n).square j).hom_ext
    · change (((cylinderFrame hC q n).left j ≫ (cylinderFrame hC q n).inc (j+1))) ≫ _ ≫ s.cylinder =
        (((cylinderFrame hC q n).left j ≫ (cylinderFrame hC q n).inc (j+1))) ≫ _ ≫ t.cylinder
      change (cylinderFrame hC q n).diagram.source j ≫ _ ≫ s.cylinder =
        (cylinderFrame hC q n).diagram.source j ≫ _ ≫ t.cylinder
      have hh (f : (cylinderTheory hC q n).Hom (Shape.globe (j+1)) S) :
          (cylinderFrame hC q n).diagram.source j ≫
              ((cylinderFrame hC q n).shapeGlobeIso (j+1)).inv ≫ f.cylinder =
            ((cylinderFrame hC q n).shapeGlobeIso j).inv ≫
              (cylinderFrame hC q n).shapeRealization.map (Shape.source j) ≫ f.cylinder :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ f.cylinder) ((cylinderFrame hC q n).shapeGlobeIso_source_inv j)).trans
            (Category.assoc _ _ _))
      exact (hh s).trans ((congrArg (((cylinderFrame hC q n).shapeGlobeIso j).inv ≫ ·)
        (congrArg RepresentedHom.cylinder hp.1)).trans (hh t).symm)
    · change (((cylinderFrame hC q n).right j ≫ (cylinderFrame hC q n).inc (j+1))) ≫ _ ≫ s.cylinder =
        (((cylinderFrame hC q n).right j ≫ (cylinderFrame hC q n).inc (j+1))) ≫ _ ≫ t.cylinder
      change (cylinderFrame hC q n).diagram.target j ≫ _ ≫ s.cylinder =
        (cylinderFrame hC q n).diagram.target j ≫ _ ≫ t.cylinder
      have hh (f : (cylinderTheory hC q n).Hom (Shape.globe (j+1)) S) :
          (cylinderFrame hC q n).diagram.target j ≫
              ((cylinderFrame hC q n).shapeGlobeIso (j+1)).inv ≫ f.cylinder =
            ((cylinderFrame hC q n).shapeGlobeIso j).inv ≫
              (cylinderFrame hC q n).shapeRealization.map (Shape.target j) ≫ f.cylinder :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ f.cylinder) ((cylinderFrame hC q n).shapeGlobeIso_target_inv j)).trans
            (Category.assoc _ _ _))
      exact (hh s).trans ((congrArg (((cylinderFrame hC q n).shapeGlobeIso j).inv ≫ ·)
        (congrArg RepresentedHom.cylinder hp.2)).trans (hh t).symm)

noncomputable def cylinderPairBoundary (a : (cylinderTheory hC q n).AdmissiblePair) :
    (cylinderFrame hC q n).bd (a.n+1) ⟶ (cylinderFrame hC q n).shapeRealization.obj a.arity :=
  ((cylinderFrame hC q n).square a.n).desc
    (((cylinderFrame hC q n).shapeGlobeIso a.n).inv ≫ a.source.cylinder)
    (((cylinderFrame hC q n).shapeGlobeIso a.n).inv ≫ a.target.cylinder)
    (cylinderPair_parallel hC q n a)

omit [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
@[reassoc] theorem cylinderPairBoundary_left (a : (cylinderTheory hC q n).AdmissiblePair) :
    (cylinderFrame hC q n).left a.n ≫ cylinderPairBoundary hC q n a =
      ((cylinderFrame hC q n).shapeGlobeIso a.n).inv ≫ a.source.cylinder :=
  ((cylinderFrame hC q n).square a.n).inl_desc _ _ _
omit [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
@[reassoc] theorem cylinderPairBoundary_right (a : (cylinderTheory hC q n).AdmissiblePair) :
    (cylinderFrame hC q n).right a.n ≫ cylinderPairBoundary hC q n a =
      ((cylinderFrame hC q n).shapeGlobeIso a.n).inv ≫ a.target.cylinder :=
  ((cylinderFrame hC q n).square a.n).inr_desc _ _ _

omit [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
theorem cylinderPairBoundary_endpoint (a : (cylinderTheory hC q n).AdmissiblePair)
    (z : C.Hom (Shape.globe (a.n+1)) a.arity) (hz : Fills (cylinderProjection hC q n) a z) (ε : Bool) :
    (cylinderEndpoint hC q n ε).bd (a.n+1) ≫ cylinderPairBoundary hC q n a =
      (cutoffDiskFrame hC q).inc (a.n+1) ≫ (cutoffRepresentables hC q).map z ≫
        (cylinderShapeEndpoint hC q n ε).app a.arity := by
  let D := cutoffDiskFrame hC q
  let B := cylinderFrame hC q n
  let F := cutoffRepresentables hC q
  let e := cylinderEndpoint hC q n ε
  let E := cylinderShapeEndpoint hC q n ε
  have hs : E.app (Shape.globe a.n) ≫ a.source.cylinder = F.map (show C.toTheoryData.arity.obj (Shape.globe a.n) ⟶ C.toTheoryData.arity.obj a.arity from a.source.original) ≫ E.app a.arity := by
    cases ε
    · exact a.source.endpoint₀
    · exact a.source.endpoint₁
  have ht : E.app (Shape.globe a.n) ≫ a.target.cylinder = F.map (show C.toTheoryData.arity.obj (Shape.globe a.n) ⟶ C.toTheoryData.arity.obj a.arity from a.target.original) ≫ E.app a.arity := by
    cases ε
    · exact a.target.endpoint₀
    · exact a.target.endpoint₁
  apply (D.square a.n).hom_ext
  · change D.left a.n ≫ e.bd (a.n+1) ≫ cylinderPairBoundary hC q n a =
      D.left a.n ≫ D.inc (a.n+1) ≫ F.map (show C.toTheoryData.arity.obj (Shape.globe (a.n+1)) ⟶ C.toTheoryData.arity.obj a.arity from z) ≫ E.app a.arity
    erw [← Category.assoc, e.left, Category.assoc, cylinderPairBoundary_left]
    erw [← Category.assoc, cylinderShapeEndpoint_globe_inv hC q n ε a.n]
    change E.app (Shape.globe a.n) ≫ a.source.cylinder =
      D.diagram.source a.n ≫ F.map (show C.toTheoryData.arity.obj (Shape.globe (a.n+1)) ⟶ C.toTheoryData.arity.obj a.arity from z) ≫ E.app a.arity
    rw [hs]
    have hh : C.comp (C.base (Shape.source a.n)) z = a.source.original := hz.1
    have hz' := congrArg (fun f : C.toTheoryData.arity.obj (Shape.globe a.n) ⟶ C.toTheoryData.arity.obj a.arity => F.map f) hh
    erw [F.map_comp, cutoffRepresentables_source] at hz'
    exact congrArg (· ≫ E.app a.arity) hz'.symm
  · change D.right a.n ≫ e.bd (a.n+1) ≫ cylinderPairBoundary hC q n a =
      D.right a.n ≫ D.inc (a.n+1) ≫ F.map (show C.toTheoryData.arity.obj (Shape.globe (a.n+1)) ⟶ C.toTheoryData.arity.obj a.arity from z) ≫ E.app a.arity
    erw [← Category.assoc, e.right, Category.assoc, cylinderPairBoundary_right]
    erw [← Category.assoc, cylinderShapeEndpoint_globe_inv hC q n ε a.n]
    change E.app (Shape.globe a.n) ≫ a.target.cylinder =
      D.diagram.target a.n ≫ F.map (show C.toTheoryData.arity.obj (Shape.globe (a.n+1)) ⟶ C.toTheoryData.arity.obj a.arity from z) ≫ E.app a.arity
    rw [ht]
    have hh : C.comp (C.base (Shape.target a.n)) z = a.target.original := hz.2
    have hz' := congrArg (fun f : C.toTheoryData.arity.obj (Shape.globe a.n) ⟶ C.toTheoryData.arity.obj a.arity => F.map f) hh
    erw [F.map_comp, cutoffRepresentables_target] at hz'
    exact congrArg (· ≫ E.app a.arity) hz'.symm

theorem cylinderProjection_liftsFillers (hnq : n ≤ q)
    (H : ExpansionContraction hC q (n+1)) : LiftsFillers (cylinderProjection hC q n) := by
  intro a z hz
  let B := cylinderFrame hC q n
  let F := cutoffRepresentables hC q
  let Y := B.shapeRealization.obj a.arity
  let d (ε : Bool) : cutoffDisk hC q (a.n+1) ⟶ Y :=
    F.map (show C.toTheoryData.arity.obj (Shape.globe (a.n+1)) ⟶ C.toTheoryData.arity.obj a.arity from z) ≫ (cylinderShapeEndpoint hC q n ε).app a.arity
  have hd (ε : Bool) : (cylinderNode hC q n (a.n+1)).bdEnd ε ≫
      cylinderPairBoundary hC q n a = cutoffI hC q (a.n+1) ≫ d ε :=
    cylinderPairBoundary_endpoint hC q n a z hz ε
  have hlow (h : a.n+1 < n) : d false = d true := by
    have hh : a.arity.height < n := Nat.lt_of_le_of_lt a.height h
    have heq := cylinderShapeEndpoint_low hC q n a.arity hh
    exact congrArg (fun f : F.obj (C.toTheoryData.arity.obj a.arity) ⟶ Y => F.map (show C.toTheoryData.arity.obj (Shape.globe (a.n+1)) ⟶ C.toTheoryData.arity.obj a.arity from z) ≫ f) heq
  have hY : Y.obj.underlying.HasFillers :=
    (cylinderShape_contractible hC q n hnq H a.arity).2
  obtain ⟨l,hl,he⟩ := cylinderNode_extend hC q n (a.n+1) hY
    (cylinderPairBoundary hC q n a) d hd hlow
  let w : (cylinderTheory hC q n).Hom (Shape.globe (a.n+1)) a.arity :=
    { original := z
      cylinder := (B.shapeGlobeIso (a.n+1)).hom ≫ l
      endpoint₀ := by
        erw [← Category.assoc, cylinderShapeEndpoint_globe hC q n false (a.n+1)]
        exact he false
      endpoint₁ := by
        erw [← Category.assoc, cylinderShapeEndpoint_globe hC q n true (a.n+1)]
        exact he true }
  refine ⟨w, ⟨?_, ?_⟩, rfl⟩
  · apply RepresentedHom.ext hz.1
    change B.shapeRealization.map (Shape.source a.n) ≫ (B.shapeGlobeIso (a.n+1)).hom ≫ l =
      a.source.cylinder
    erw [← Category.assoc, GlobularFrame.shapeGlobeIso_source, Category.assoc]
    change (B.shapeGlobeIso a.n).hom ≫ (B.left a.n ≫ B.inc (a.n+1)) ≫ l = _
    have hh : (B.left a.n ≫ B.inc (a.n+1)) ≫ l =
        (B.shapeGlobeIso a.n).inv ≫ a.source.cylinder :=
      (Category.assoc _ _ _).trans ((congrArg (B.left a.n ≫ ·) hl).trans
        (cylinderPairBoundary_left hC q n a))
    exact (congrArg ((B.shapeGlobeIso a.n).hom ≫ ·) hh).trans
      ((B.shapeGlobeIso a.n).hom_inv_id_assoc _)
  · apply RepresentedHom.ext hz.2
    change B.shapeRealization.map (Shape.target a.n) ≫ (B.shapeGlobeIso (a.n+1)).hom ≫ l =
      a.target.cylinder
    erw [← Category.assoc, GlobularFrame.shapeGlobeIso_target, Category.assoc]
    change (B.shapeGlobeIso a.n).hom ≫ (B.right a.n ≫ B.inc (a.n+1)) ≫ l = _
    have hh : (B.right a.n ≫ B.inc (a.n+1)) ≫ l =
        (B.shapeGlobeIso a.n).inv ≫ a.target.cylinder :=
      (Category.assoc _ _ _).trans ((congrArg (B.right a.n ≫ ·) hl).trans
        (cylinderPairBoundary_right hC q n a))
    exact (congrArg ((B.shapeGlobeIso a.n).hom ≫ ·) hh).trans
      ((B.shapeGlobeIso a.n).hom_inv_id_assoc _)

noncomputable def cylinderInterpretation (hnq : n ≤ q)
    (H : ExpansionContraction hC q (n+1)) : Morphism C (cylinderTheory hC q n) :=
  Classical.choose (hC.1.some.lift (cylinderProjection hC q n)
    (cylinderProjection_liftsFillers hC q n hnq H) (Morphism.id C))

theorem cylinderInterpretation_projection (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1)) :
    (cylinderInterpretation hC q n hnq H).comp (cylinderProjection hC q n) = Morphism.id C :=
  Classical.choose_spec (hC.1.some.lift (cylinderProjection hC q n)
    (cylinderProjection_liftsFillers hC q n hnq H) (Morphism.id C))

end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)]
local instance smallColimitsFullCylinder : HasColimitsOfSize.{0,v} (CutoffModels C q) :=
  hasColimitsOfSizeShrink.{0,v} (CutoffModels C q)
variable (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))

noncomputable def cylinderRealization : C.Obj ⥤ CutoffModels C q where
  obj S := (cylinderFrame hC q n).shapeRealization.obj S.shape
  map f := ((cylinderInterpretation hC q n hnq H).map f).cylinder
  map_id S := congrArg RepresentedHom.cylinder ((cylinderInterpretation hC q n hnq H).map_id S.shape)
  map_comp f g := congrArg RepresentedHom.cylinder ((cylinderInterpretation hC q n hnq H).map_comp f g)

@[simp] theorem cylinderRealization_base {S T : Shape} (f : S ⟶ T) :
    (cylinderRealization hC q n hnq H).map (C.base f) =
      (cylinderFrame hC q n).shapeRealization.map f :=
  congrArg RepresentedHom.cylinder ((cylinderInterpretation hC q n hnq H).map_base f)

theorem cylinderInterpretation_original {S T : Shape} (f : C.Hom S T) :
    ((cylinderInterpretation hC q n hnq H).map f).original = f :=
  congrArg (fun z : Morphism C C => z.map f) (cylinderInterpretation_projection hC q n hnq H)

noncomputable def fullCylinder (Y : CutoffModels C q) : C.Model where
  presheaf := (cylinderRealization hC q n hnq H).op ⋙ yoneda.obj Y
  sums S b h hl hr := by
    simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, TheoryData.arity, cylinderRealization_base]
    exact (((cylinderFrame hC q n).shapeRealization_sums S b h hl hr).op.map (yoneda.obj Y)).flip

noncomputable def fullCylinderEndpoint (Y : CutoffModels C q) (ε : Bool) :
    fullCylinder hC q n hnq H Y ⟶ Y.obj where
  app S := ↾(fun a => yonedaEquiv ((cutoffAdjunction hC q).homEquiv _ Y
    ((cylinderShapeEndpoint hC q n ε).app S.unop.shape ≫ a)))
  naturality S T f := by
    apply ConcreteCategory.hom_ext
    intro a
    symm
    change Y.obj.presheaf.map f (yonedaEquiv ((cutoffAdjunction hC q).homEquiv _ Y
      ((cylinderShapeEndpoint hC q n ε).app S.unop.shape ≫ a))) =
      yonedaEquiv ((cutoffAdjunction hC q).homEquiv _ Y
        ((cylinderShapeEndpoint hC q n ε).app T.unop.shape ≫
          (cylinderRealization hC q n hnq H).map f.unop ≫ a))
    have he : (cylinderShapeEndpoint hC q n ε).app T.unop.shape ≫
        (cylinderRealization hC q n hnq H).map f.unop =
        (cutoffRepresentables hC q).map f.unop ≫
          (cylinderShapeEndpoint hC q n ε).app S.unop.shape := by
      let E := (cylinderInterpretation hC q n hnq H).map f.unop
      have ho : (show T.unop ⟶ S.unop from E.original) = f.unop :=
        cylinderInterpretation_original hC q n hnq H f.unop
      cases ε
      · exact E.endpoint₀.trans (congrArg (fun z : T.unop ⟶ S.unop =>
          (cutoffRepresentables hC q).map z ≫ (cylinderShapeEndpoint hC q n false).app S.unop.shape) ho)
      · exact E.endpoint₁.trans (congrArg (fun z : T.unop ⟶ S.unop =>
          (cutoffRepresentables hC q).map z ≫ (cylinderShapeEndpoint hC q n true).app S.unop.shape) ho)
    have ha : (cylinderShapeEndpoint hC q n ε).app T.unop.shape ≫
        (cylinderRealization hC q n hnq H).map f.unop ≫ a =
        (cutoffRepresentables hC q).map f.unop ≫
          ((cylinderShapeEndpoint hC q n ε).app S.unop.shape ≫ a) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ a) he).trans (Category.assoc _ _ _))
    have hadj := (cutoffAdjunction hC q).homEquiv_naturality_left
      (show freeShape C T.unop.shape ⟶ freeShape C S.unop.shape from yoneda.map f.unop)
      ((cylinderShapeEndpoint hC q n ε).app S.unop.shape ≫ a)
    exact (yonedaEquiv_naturality _ f.unop).trans
      ((congrArg yonedaEquiv hadj.symm).trans
        (congrArg (fun z => yonedaEquiv ((cutoffAdjunction hC q).homEquiv _ Y z)) ha.symm))

noncomputable def fullCylinderEvaluation (Y : CutoffModels C q) :
    GlobularSet.Hom (fullCylinder hC q n hnq H Y).underlying ((cylinderFrame hC q n).homGlob Y) where
  app j a := ((cylinderFrame hC q n).shapeGlobeIso j).inv ≫ a
  source_app j a := by
    change ((cylinderFrame hC q n).shapeGlobeIso j).inv ≫
      (cylinderRealization hC q n hnq H).map (C.base (Shape.source j)) ≫ a =
      (cylinderFrame hC q n).diagram.source j ≫ ((cylinderFrame hC q n).shapeGlobeIso (j+1)).inv ≫ a
    erw [cylinderRealization_base, ← Category.assoc,
      ← GlobularFrame.shapeGlobeIso_source_inv, Category.assoc]
  target_app j a := by
    change ((cylinderFrame hC q n).shapeGlobeIso j).inv ≫
      (cylinderRealization hC q n hnq H).map (C.base (Shape.target j)) ≫ a =
      (cylinderFrame hC q n).diagram.target j ≫ ((cylinderFrame hC q n).shapeGlobeIso (j+1)).inv ≫ a
    erw [cylinderRealization_base, ← Category.assoc,
      ← GlobularFrame.shapeGlobeIso_target_inv, Category.assoc]

noncomputable def fullCylinderCoevaluation (Y : CutoffModels C q) :
    GlobularSet.Hom ((cylinderFrame hC q n).homGlob Y) (fullCylinder hC q n hnq H Y).underlying where
  app j a := ((cylinderFrame hC q n).shapeGlobeIso j).hom ≫ a
  source_app j a := by
    change ((cylinderFrame hC q n).shapeGlobeIso j).hom ≫
      (cylinderFrame hC q n).diagram.source j ≫ a =
      (cylinderRealization hC q n hnq H).map (C.base (Shape.source j)) ≫
        ((cylinderFrame hC q n).shapeGlobeIso (j+1)).hom ≫ a
    erw [cylinderRealization_base]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ a)
      ((cylinderFrame hC q n).shapeGlobeIso_source j).symm).trans (Category.assoc _ _ _))
  target_app j a := by
    change ((cylinderFrame hC q n).shapeGlobeIso j).hom ≫
      (cylinderFrame hC q n).diagram.target j ≫ a =
      (cylinderRealization hC q n hnq H).map (C.base (Shape.target j)) ≫
        ((cylinderFrame hC q n).shapeGlobeIso (j+1)).hom ≫ a
    erw [cylinderRealization_base]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ a)
      ((cylinderFrame hC q n).shapeGlobeIso_target j).symm).trans (Category.assoc _ _ _))

@[simp] theorem fullCylinderEvaluation_coevaluation (Y : CutoffModels C q) :
    (fullCylinderEvaluation hC q n hnq H Y).comp (fullCylinderCoevaluation hC q n hnq H Y) =
      GlobularSet.Hom.id _ := by
  ext j a
  exact Iso.hom_inv_id_assoc _ _

@[simp] theorem fullCylinderCoevaluation_evaluation (Y : CutoffModels C q) :
    (fullCylinderCoevaluation hC q n hnq H Y).comp (fullCylinderEvaluation hC q n hnq H Y) =
      GlobularSet.Hom.id _ := by
  ext j a
  exact Iso.inv_hom_id_assoc _ _

@[simp] theorem fullCylinderEndpoint_evaluation (Y : CutoffModels C q) (ε : Bool) :
    underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε) =
      ((fullCylinderEvaluation hC q n hnq H Y).comp
        ((cylinderEndpoint hC q n ε).pre Y)).comp (cutoffDiskEvaluation hC q Y) := by
  ext j a
  change cutoffCellEquiv hC q Y j ((cylinderShapeEndpoint hC q n ε).app (Shape.globe j) ≫ a) =
    cutoffCellEquiv hC q Y j ((cylinderEndpoint hC q n ε).obj j ≫
      ((cylinderFrame hC q n).shapeGlobeIso j).inv ≫ a)
  erw [← Category.assoc, cylinderShapeEndpoint_globe_inv]
end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasPushouts K]
variable {D B : GlobularFrame K} (e : Bool → Hom D B)

noncomputable abbrev twoEnded (j : ℕ) := TwoEndpoints.obj (D.inc j) (fun ε => (e ε).bd j)
noncomputable def twoEndedMap (j : ℕ) : twoEnded e j ⟶ B.obj j :=
  TwoEndpoints.desc (D.inc j) (fun ε => (e ε).bd j) (B.inc j) (fun ε => (e ε).obj j)
    (fun ε => (e ε).inc j)

theorem twoEnded_lift {X Y : K} (p : X ⟶ Y) (j : ℕ)
    (h : HasLiftingProperty (twoEndedMap e j) p)
    (a : B.bd j ⟶ X) (d : Bool → (D.obj j ⟶ X))
    (hd : ∀ ε, (e ε).bd j ≫ a = D.inc j ≫ d ε)
    (y : B.obj j ⟶ Y) (ha : a ≫ p = B.inc j ≫ y)
    (hy : ∀ ε, d ε ≫ p = (e ε).obj j ≫ y) :
    ∃ l : B.obj j ⟶ X, B.inc j ≫ l = a ∧ (∀ ε, (e ε).obj j ≫ l = d ε) ∧ l ≫ p = y := by
  let t := TwoEndpoints.desc (D.inc j) (fun ε => (e ε).bd j) a d hd
  have sq : CommSq t (twoEndedMap e j) p y := by
    constructor
    apply TwoEndpoints.hom_ext
    · erw [← Category.assoc, TwoEndpoints.base_desc]
      erw [← Category.assoc, TwoEndpoints.base_desc]
      exact ha
    · intro ε
      erw [← Category.assoc, TwoEndpoints.endpoint_desc]
      erw [← Category.assoc, TwoEndpoints.endpoint_desc]
      exact hy ε
  let : sq.HasLift := h.sq_hasLift sq
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · have hh := congrArg (TwoEndpoints.base (D.inc j) (fun ε => (e ε).bd j) ≫ ·) sq.fac_left
    erw [← Category.assoc, TwoEndpoints.base_desc, TwoEndpoints.base_desc] at hh
    exact hh
  · intro ε
    have hh := congrArg (TwoEndpoints.endpoint (D.inc j) (fun ε => (e ε).bd j) ε ≫ ·) sq.fac_left
    erw [← Category.assoc, TwoEndpoints.endpoint_desc, TwoEndpoints.endpoint_desc] at hh
    exact hh

noncomputable abbrev jointSource (k : ℕ) :=
  TwoEndpoints.obj (D.diagram.source k) (fun ε => (e ε).obj k)
noncomputable def jointSourceMap (k : ℕ) : jointSource e k ⟶ B.obj (k+1) :=
  TwoEndpoints.desc (D.diagram.source k) (fun ε => (e ε).obj k)
    (B.diagram.source k) (fun ε => (e ε).obj (k+1))
    (fun ε => ((e ε).source_naturality k).symm)

omit [HasPushouts K] in
@[reassoc] theorem inc_source_eq_inc_target (B : GlobularFrame K) (k : ℕ) :
    B.inc k ≫ B.diagram.source k = B.inc k ≫ B.diagram.target k := by
  change B.inc k ≫ B.left k ≫ B.inc (k+1) = B.inc k ≫ B.right k ≫ B.inc (k+1)
  rw [← Category.assoc, (B.square k).w, Category.assoc]

theorem jointSource_lifting {X Y : K} (p : X ⟶ Y) (k : ℕ)
    (h₀ : HasLiftingProperty (twoEndedMap e k) p)
    (h₁ : HasLiftingProperty (twoEndedMap e (k+1)) p) :
    HasLiftingProperty (jointSourceMap e k) p := by
  constructor
  intro a y sq
  let u := TwoEndpoints.base (D.diagram.source k) (fun ε => (e ε).obj k) ≫ a
  let d (ε) := TwoEndpoints.endpoint (D.diagram.source k) (fun ε => (e ε).obj k) ε ≫ a
  have hd (ε) : (e ε).obj k ≫ u = D.diagram.source k ≫ d ε := by
    dsimp only [u,d]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ a) (TwoEndpoints.condition (D.diagram.source k)
        (fun ε => (e ε).obj k) ε)).trans (Category.assoc _ _ _))
  have hu : u ≫ p = B.diagram.source k ≫ y := by
    have h := congrArg (TwoEndpoints.base (D.diagram.source k) (fun ε => (e ε).obj k) ≫ ·) sq.w
    erw [← Category.assoc _ (jointSourceMap e k), TwoEndpoints.base_desc] at h
    exact (Category.assoc _ _ _).trans h
  have hyp (ε) : d ε ≫ p = (e ε).obj (k+1) ≫ y := by
    have h := congrArg (TwoEndpoints.endpoint (D.diagram.source k) (fun ε => (e ε).obj k) ε ≫ ·) sq.w
    erw [← Category.assoc _ (jointSourceMap e k), TwoEndpoints.endpoint_desc] at h
    exact (Category.assoc _ _ _).trans h
  have hbd (ε) : (e ε).bd k ≫ (B.inc k ≫ u) = D.inc k ≫ (D.diagram.target k ≫ d ε) := by
    erw [← Category.assoc, (e ε).inc, Category.assoc]
    exact (congrArg (D.inc k ≫ ·) (hd ε)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ d ε) (inc_source_eq_inc_target D k)).trans (Category.assoc _ _ _)))
  have hbyp : (B.inc k ≫ u) ≫ p = B.inc k ≫ B.diagram.target k ≫ y := by
    erw [Category.assoc, hu]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ y) (inc_source_eq_inc_target B k)).trans (Category.assoc _ _ _))
  have hdy (ε) : (D.diagram.target k ≫ d ε) ≫ p = (e ε).obj k ≫ B.diagram.target k ≫ y := by
    erw [Category.assoc, hyp]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ y) ((e ε).target_naturality k)).trans (Category.assoc _ _ _))
  obtain ⟨v,hv,he,hvp⟩ := twoEnded_lift e p k h₀ (B.inc k ≫ u)
    (fun ε => D.diagram.target k ≫ d ε) hbd (B.diagram.target k ≫ y) hbyp hdy
  let b := (B.square k).desc u v hv.symm
  have hbe (ε) : (e ε).bd (k+1) ≫ b = D.inc (k+1) ≫ d ε := by
    apply (D.square k).hom_ext
    · rw [← Category.assoc, (e ε).left, Category.assoc, IsPushout.inl_desc]
      exact (hd ε).trans (Category.assoc _ _ _)
    · rw [← Category.assoc, (e ε).right, Category.assoc, IsPushout.inr_desc]
      exact (he ε).trans (Category.assoc _ _ _)
  have hbp : b ≫ p = B.inc (k+1) ≫ y := by
    apply (B.square k).hom_ext
    · rw [← Category.assoc, IsPushout.inl_desc]
      exact hu.trans (Category.assoc _ _ _)
    · rw [← Category.assoc, IsPushout.inr_desc]
      exact hvp.trans (Category.assoc _ _ _)
  obtain ⟨l,hl,hel,hlp⟩ := twoEnded_lift e p (k+1) h₁ b d hbe y hbp hyp
  refine CommSq.HasLift.mk' ⟨l, ?_, hlp⟩
  apply TwoEndpoints.hom_ext
  · erw [← Category.assoc, TwoEndpoints.base_desc]
    change (B.left k ≫ B.inc (k+1)) ≫ l = u
    rw [Category.assoc, hl]
    exact (B.square k).inl_desc _ _ _
  · intro ε
    erw [← Category.assoc, TwoEndpoints.endpoint_desc]
    exact hel ε

end GlobularFrame
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace CylinderNode
variable {K : Type u} [Category.{v} K] [HasPushouts K]
variable {D : GlobularFrame K} {j : ℕ}
noncomputable def twoSideMap (Z : CylinderNode D j) :
    TwoEndpoints.obj (D.inc j) Z.bdEnd ⟶ Z.obj :=
  TwoEndpoints.desc (D.inc j) Z.bdEnd Z.inc Z.endpoint Z.comm

theorem critical_twoSide_lifting (D : GlobularFrame K) (n : ℕ)
    {X Y : K} (p : X ⟶ Y) (h : HasLiftingProperty (D.inc (n+1)) p) :
    HasLiftingProperty ((critical D n).twoSideMap) p := by
  constructor
  intro a y sq
  let e : Bool → (D.bd n ⟶ D.bd n) := fun _ => 𝟙 _
  let ds (ε) := TwoEndpoints.endpoint (D.inc n) e ε ≫ a
  have hd : D.inc n ≫ ds false = D.inc n ≫ ds true := by
    have hx (ε) : D.inc n ≫ ds ε = TwoEndpoints.base (D.inc n) e ≫ a := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ a) ((TwoEndpoints.condition (D.inc n) e ε).symm.trans
          (Category.id_comp _))))
    exact (hx false).trans (hx true).symm
  let b := (D.square n).desc (ds false) (ds true) hd
  have hdp (ε) : ds ε ≫ p = (if ε then D.diagram.target n else D.diagram.source n) ≫ y := by
    have hh := congrArg (TwoEndpoints.endpoint (D.inc n) e ε ≫ ·) sq.w
    erw [← Category.assoc _ ((critical D n).twoSideMap), TwoEndpoints.endpoint_desc] at hh
    exact (Category.assoc _ _ _).trans hh
  have sq' : CommSq b (D.inc (n+1)) p y := by
    constructor
    apply (D.square n).hom_ext
    · erw [← Category.assoc, IsPushout.inl_desc]
      exact (hdp false).trans (Category.assoc _ _ _)
    · erw [← Category.assoc, IsPushout.inr_desc]
      exact (hdp true).trans (Category.assoc _ _ _)
  let : sq'.HasLift := h.sq_hasLift sq'
  have hs : D.diagram.source n ≫ sq'.lift = ds false := by
    change (D.left n ≫ D.inc (n+1)) ≫ sq'.lift = _
    rw [Category.assoc, sq'.fac_left]
    exact (D.square n).inl_desc _ _ _
  have ht : D.diagram.target n ≫ sq'.lift = ds true := by
    change (D.right n ≫ D.inc (n+1)) ≫ sq'.lift = _
    rw [Category.assoc, sq'.fac_left]
    exact (D.square n).inr_desc _ _ _
  refine CommSq.HasLift.mk' ⟨sq'.lift, ?_, sq'.fac_right⟩
  apply TwoEndpoints.hom_ext
  · erw [← Category.assoc, TwoEndpoints.base_desc]
    change (D.inc n ≫ D.diagram.source n) ≫ sq'.lift = _
    erw [Category.assoc, hs]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ a) ((TwoEndpoints.condition (D.inc n) e false).symm.trans
        (Category.id_comp _))))
  · intro ε
    erw [← Category.assoc, TwoEndpoints.endpoint_desc]
    cases ε
    · exact hs
    · exact ht
end CylinderNode
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)]

theorem completedCylinder_twoSide_upper (j : ℕ) (B : CutoffModels C q)
    (e : Bool → (cutoffBoundary hC q j ⟶ B)) :
    (boundaryClass hC q (n+1)).rlp.llp ((completedCylinder hC q n j B e).twoSideMap) := by
  let F := cylinderFactor hC q n j B e
  have he : (completedCylinder hC q n j B e).twoSideMap = F.i := by
    apply TwoEndpoints.hom_ext
    · exact TwoEndpoints.base_desc _ _ _ _ _
    · intro ε
      exact TwoEndpoints.endpoint_desc _ _ _ _ _ ε
  rw [he]
  exact F.hi

theorem cylinderFrame_twoEnded_upper {j : ℕ} (hj : n ≤ j) :
    (boundaryClass hC q (n+1)).rlp.llp
      (GlobularFrame.twoEndedMap (cylinderEndpoint hC q n) j) := by
  change (boundaryClass hC q (n+1)).rlp.llp ((cylinderNode hC q n j).twoSideMap)
  by_cases he : j = n
  · subst j
    rw [cylinderNode_critical]
    intro X Y p hp
    exact CylinderNode.critical_twoSide_lifting (cutoffDiskFrame hC q) n p
      (hp _ (MorphismProperty.ofHoms.mk (⟨n+1,le_rfl⟩ : {j : ℕ // n+1 ≤ j})))
  · cases j with
    | zero => omega
    | succ j =>
      rw [cylinderNode_high hC q n (by omega)]
      exact completedCylinder_twoSide_upper hC q n _ _ _

theorem cylinderFrame_jointSource_upper (k : ℕ) (hk : n ≤ k) :
    (boundaryClass hC q (n+1)).rlp.llp
      (GlobularFrame.jointSourceMap (cylinderEndpoint hC q n) k) := by
  intro X Y p hp
  exact GlobularFrame.jointSource_lifting (cylinderEndpoint hC q n) p k
    (cylinderFrame_twoEnded_upper hC q n hk p hp)
    (cylinderFrame_twoEnded_upper hC q n (by omega) p hp)
end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasPushouts K]
variable {D B : GlobularFrame K}

theorem criticalJoint_retract (e : Bool → Hom D B) (n : ℕ)
    (i : B.obj n ≅ D.obj (n+1))
    (hs : (e false).obj n ≫ i.hom = D.diagram.source n)
    (ht : (e true).obj n ≫ i.hom = D.diagram.target n)
    (hb : (e false).bd n = (e true).bd n) [Epi ((e false).bd n)] :
    ∃ f : jointSource e n ⟶ oneSided (e false) (n+1),
      ∃ g : oneSided (e false) (n+1) ⟶ jointSource e n, f ≫ g = 𝟙 _ := by
  let aB := pushout.inl ((e false).bd (n+1)) (D.inc (n+1))
  let aD := pushout.inr ((e false).bd (n+1)) (D.inc (n+1))
  let c := TwoEndpoints.base (D.diagram.source n) (fun ε => (e ε).obj n)
  let d := TwoEndpoints.endpoint (D.diagram.source n) (fun ε => (e ε).obj n)
  let side (ε : Bool) := if ε then B.right n else B.left n
  have hc (ε) : D.diagram.source n ≫ d ε = (e ε).obj n ≫ c :=
    (TwoEndpoints.condition (D.diagram.source n) (fun ε => (e ε).obj n) ε).symm
  have hcommon : D.inc n ≫ (e false).obj n = D.inc n ≫ (e true).obj n := by
    rw [← (e false).inc, hb, (e true).inc]
  have hsi : D.diagram.source n ≫ i.inv = (e false).obj n := by
    apply (cancel_mono i.hom).1
    erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact hs.symm
  have hti : D.diagram.target n ≫ i.inv = (e true).obj n := by
    apply (cancel_mono i.hom).1
    erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact ht.symm
  have hpar : B.inc n ≫ i.hom ≫ d false = B.inc n ≫ i.hom ≫ d true := by
    apply (cancel_epi ((e false).bd n)).1
    have hx (ε) : (e false).bd n ≫ B.inc n ≫ i.hom ≫ d ε = D.inc n ≫ (e ε).obj n ≫ c := by
      erw [← Category.assoc, (e false).inc, Category.assoc]
      have hh : (e false).obj n ≫ i.hom ≫ d ε = (e ε).obj n ≫ c :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ d ε) hs).trans (hc ε))
      exact congrArg (D.inc n ≫ ·) hh
    exact (hx false).trans (((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ c) hcommon).trans (Category.assoc _ _ _))).trans (hx true).symm)
  let b := (B.square n).desc (i.hom ≫ d false) (i.hom ≫ d true) hpar
  have hbg : (e false).bd (n+1) ≫ b = D.inc (n+1) ≫ i.inv ≫ c := by
    apply (D.square n).hom_ext
    · erw [← Category.assoc, (e false).left, Category.assoc, IsPushout.inl_desc]
      erw [← Category.assoc, hs, hc false]
      have hh : D.diagram.source n ≫ i.inv ≫ c = (e false).obj n ≫ c :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ c) hsi)
      exact hh.symm.trans (Category.assoc _ _ _)
    · erw [← Category.assoc, (e false).right, Category.assoc, IsPushout.inr_desc]
      erw [← Category.assoc, hs, hc true]
      have hh : D.diagram.target n ≫ i.inv ≫ c = (e true).obj n ≫ c :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ c) hti)
      exact hh.symm.trans (Category.assoc _ _ _)
  let g := pushout.desc b (i.inv ≫ c) hbg
  have hgB : aB ≫ g = b := pushout.inl_desc _ _ _
  have hgD : aD ≫ g = i.inv ≫ c := pushout.inr_desc _ _ _
  have hfd (ε) : (e ε).obj n ≫ i.hom ≫ aD = D.diagram.source n ≫ i.inv ≫ side ε ≫ aB := by
    have hl : D.left n ≫ (e false).bd (n+1) ≫ aB = (e false).obj n ≫ B.left n ≫ aB := by
      erw [← Category.assoc, (e false).left, Category.assoc]
    have hr : D.right n ≫ (e false).bd (n+1) ≫ aB = (e false).obj n ≫ B.right n ≫ aB := by
      erw [← Category.assoc, (e false).right, Category.assoc]
    have hp : (e false).bd (n+1) ≫ aB = D.inc (n+1) ≫ aD := pushout.condition
    have hrhs (ε) : D.diagram.source n ≫ i.inv ≫ side ε ≫ aB = (e false).obj n ≫ side ε ≫ aB :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ side ε ≫ aB) hsi)
    cases ε
    · have hh : (e false).obj n ≫ i.hom ≫ aD = (e false).obj n ≫ B.left n ≫ aB :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ aD) hs).trans
          ((Category.assoc _ _ _).trans ((congrArg (D.left n ≫ ·) hp).symm.trans hl)))
      exact hh.trans (hrhs false).symm
    · have hh : (e true).obj n ≫ i.hom ≫ aD = (e false).obj n ≫ B.right n ≫ aB :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ aD) ht).trans
          ((Category.assoc _ _ _).trans ((congrArg (D.right n ≫ ·) hp).symm.trans hr)))
      exact hh.trans (hrhs true).symm
  let f := TwoEndpoints.desc (D.diagram.source n) (fun ε => (e ε).obj n)
    (i.hom ≫ aD) (fun ε => i.inv ≫ side ε ≫ aB) hfd
  refine ⟨f,g,?_⟩
  apply TwoEndpoints.hom_ext
  · erw [← Category.assoc, TwoEndpoints.base_desc, Category.assoc, hgD, Iso.hom_inv_id_assoc,
      Category.comp_id]
  · intro ε
    erw [← Category.assoc, TwoEndpoints.endpoint_desc, Category.assoc, Category.assoc, hgB]
    cases ε
    · change i.inv ≫ B.left n ≫ b = d false ≫ 𝟙 _
      erw [IsPushout.inl_desc, Iso.inv_hom_id_assoc, Category.comp_id]
    · change i.inv ≫ B.right n ≫ b = d true ≫ 𝟙 _
      erw [IsPushout.inr_desc, Iso.inv_hom_id_assoc, Category.comp_id]
end GlobularFrame
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace TwoEndpoints
variable {K : Type u} [Category.{v} K] [HasPushouts K]
theorem base_property (W : MorphismProperty K) [W.IsStableUnderCobaseChange]
    [W.IsStableUnderComposition] {Bd Disk B : K} (i : Bd ⟶ Disk)
    (e : Bool → (Bd ⟶ B)) (hi : W i) : W (base i e) :=
  W.comp_mem _ _ (MorphismProperty.of_isPushout (IsPushout.of_hasPushout (e false) i) hi)
    (MorphismProperty.of_isPushout (IsPushout.of_hasPushout (e true ≫ pushout.inl (e false) i) i) hi)
end TwoEndpoints
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasPushouts K] {D B : GlobularFrame K}
theorem oneSided_split_of_endpoint (e : Hom D B) (j : ℕ) [Epi (e.bd j)]
    (r : B.obj j ⟶ D.obj j) (hr : e.obj j ≫ r = 𝟙 _) :
    ∃ s : B.obj j ⟶ oneSided e j, oneSidedMap e j ≫ s = 𝟙 _ := by
  refine ⟨r ≫ pushout.inr (e.bd j) (D.inc j), ?_⟩
  apply pushout.hom_ext
  · apply (cancel_epi (e.bd j)).1
    erw [← Category.assoc _ (pushout.inl _ _), pushout.condition, Category.assoc,
      ← Category.assoc (pushout.inr _ _), pushout.inr_desc]
    erw [← Category.assoc (e.obj j) r, hr, Category.id_comp, Category.comp_id]
    exact pushout.condition.symm
  · erw [← Category.assoc, pushout.inr_desc, ← Category.assoc, hr, Category.id_comp,
      Category.comp_id]
end GlobularFrame
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)]

theorem cylinder_critical_joint_contractible (hnq : n ≤ q)
    (H : ExpansionContraction hC q (n+1)) :
    (GlobularFrame.jointSource (cylinderEndpoint hC q n) n).obj.underlying.HasFillers := by
  have hb : (cylinderEndpoint hC q n false).bd n = (cylinderEndpoint hC q n true).bd n := by
    change (cylinderNode hC q n n).bdEnd false = (cylinderNode hC q n n).bdEnd true
    rw [cylinderNode_critical]; rfl
  have : Epi ((cylinderEndpoint hC q n false).bd n) := by
    change Epi ((cylinderNode hC q n n).bdEnd false)
    rw [cylinderNode_critical]
    change Epi (𝟙 _); infer_instance
  obtain ⟨f,g,hfg⟩ := GlobularFrame.criticalJoint_retract (cylinderEndpoint hC q n) n
    (cylinderCriticalData hC q n false).iso
    (cylinderCriticalData hC q n false).endpoint
    (cylinderCriticalData hC q n true).endpoint hb
  exact ((cylinder_oneSided_contractible hC q n hnq H (n+1) (by omega) false).2.1).retract
    (underlyingMap f.hom) (underlyingMap g.hom)
    (congrArg (fun z : GlobularFrame.jointSource (cylinderEndpoint hC q n) n ⟶
      GlobularFrame.jointSource (cylinderEndpoint hC q n) n => underlyingMap z.hom) hfg)

theorem cylinder_joint_contractible (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))
    (k : ℕ) (hk : n ≤ k) :
    (GlobularFrame.jointSource (cylinderEndpoint hC q n) k).obj.underlying.HasFillers := by
  by_cases he : k = n
  · subst k; exact cylinder_critical_joint_contractible hC q n hnq H
  · let f := TwoEndpoints.base ((cutoffDiskFrame hC q).diagram.source k)
      (fun ε => (cylinderEndpoint hC q n ε).obj k)
    have hf : (sourceClass hC q (n+1)).rlp.llp f := by
      apply TwoEndpoints.base_property
      rw [cutoffDiskFrame_source]
      intro X Y p hp
      exact hp _ (MorphismProperty.ofHoms.mk (⟨k,by omega⟩ : {j : ℕ // n+1 ≤ j}))
    exact H f hf (cylinderNode_contractible hC q n hnq H k).1
      (cylinderNode_contractible hC q n hnq H k).2

theorem cylinder_joint_split (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))
    (k : ℕ) (hk : n ≤ k) :
    ∃ s : (cylinderFrame hC q n).obj (k+1) ⟶
        GlobularFrame.jointSource (cylinderEndpoint hC q n) k,
      GlobularFrame.jointSourceMap (cylinderEndpoint hC q n) k ≫ s = 𝟙 _ :=
  boundary_cofibration_split hC q _ (cylinderFrame_jointSource_upper hC q n k hk)
    (cylinder_joint_contractible hC q n hnq H k hk)

omit [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
@[simp] theorem target_comp_unitMap (j : ℕ) : targetDisk C j ≫ unitMap C hC j = 𝟙 _ := by
  apply NatTrans.ext
  funext S
  apply ConcreteCategory.hom_ext
  intro f
  change C.Hom S.unop.shape (Shape.globe j) at f
  change C.comp (C.comp f (C.base (Shape.target j))) (C.unit hC j) = f
  rw [C.assoc, C.unit_target, C.comp_id]

theorem cylinder_oneSided_split (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))
    (j : ℕ) (ε : Bool) :
    ∃ s : (cylinderFrame hC q n).obj j ⟶ GlobularFrame.oneSided (cylinderEndpoint hC q n ε) j,
      GlobularFrame.oneSidedMap (cylinderEndpoint hC q n ε) j ≫ s = 𝟙 _ := by
  by_cases hj : n < j
  · exact cylinder_oneSided_split_high hC q n hnq H hj ε
  · have hepi : Epi ((cylinderEndpoint hC q n ε).bd j) := by
      change Epi ((cylinderNode hC q n j).bdEnd ε)
      by_cases he : j = n
      · subst j; rw [cylinderNode_critical]; change Epi (𝟙 _); infer_instance
      · rw [cylinderNode_low hC q n (by omega)]; change Epi (𝟙 _); infer_instance
    suffices hr : ∃ r : (cylinderFrame hC q n).obj j ⟶ (cutoffDiskFrame hC q).obj j,
        (cylinderEndpoint hC q n ε).obj j ≫ r = 𝟙 _ by
      obtain ⟨r,hr⟩ := hr
      exact GlobularFrame.oneSided_split_of_endpoint (cylinderEndpoint hC q n ε) j r hr
    change ∃ r : (cylinderNode hC q n j).obj ⟶ (cutoffDiskFrame hC q).obj j,
      (cylinderNode hC q n j).endpoint ε ≫ r = 𝟙 _
    by_cases he : j = n
    · subst j
      rw [cylinderNode_critical]
      refine ⟨(cutoffFunctor hC q).map (unitMap C hC n), ?_⟩
      cases ε
      · change (cutoffDiskFrame hC q).diagram.source n ≫ _ = _
        rw [cutoffDiskFrame_source]
        change (cutoffFunctor hC q).map (J C n) ≫ _ = _
        erw [← Functor.map_comp, J_comp_unitMap]
        exact (cutoffFunctor hC q).map_id _
      · change (cutoffDiskFrame hC q).diagram.target n ≫ _ = _
        erw [cutoffDiskFrame_target, ← Functor.map_comp, target_comp_unitMap]
        exact (cutoffFunctor hC q).map_id _
    · rw [cylinderNode_low hC q n (by omega)]
      exact ⟨𝟙 _, Category.id_comp _⟩
end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularSet

theorem liftsBoundary_of_bijective {X Y : GlobularSet.{v}} (p : Hom X Y) (k : ℕ)
    (hp : ∀ j, j ≤ k → Function.Bijective (p.app j)) : LiftsBoundary p k := by
  intro bd y hy
  obtain ⟨x,hx⟩ := (hp k le_rfl).surjective y
  refine ⟨x, ?_, hx⟩
  apply (Hom.boundaryMap_bijective_of_low p k (fun j hj => hp j (by omega))).injective
  rw [p.boundary_app, hx, hy]

theorem LiftsBoundary.comp {X Y Z : GlobularSet.{v}} {f : Hom X Y} {g : Hom Y Z}
    {k : ℕ} (hf : LiftsBoundary f k) (hg : LiftsBoundary g k) : LiftsBoundary (f.comp g) k := by
  intro bd z hz
  obtain ⟨y,hy,hgz⟩ := hg (f.boundaryMap k bd) z
    (by simpa only [Hom.boundaryMap_comp] using hz)
  obtain ⟨x,hx,hfx⟩ := hf bd y hy
  exact ⟨x,hx,(congrArg (g.app k) hfx).trans hgz⟩

end GlobularSet
namespace GlobularFrame
variable {K : Type u} [Category.{v} K] [HasPushouts K] {B D : GlobularFrame K}

theorem Hom.pre_liftsBoundary (e : Hom D B) (Y : K) (j : ℕ)
    (s : B.obj j ⟶ oneSided e j) (hs : oneSidedMap e j ≫ s = 𝟙 _) :
    GlobularSet.LiftsBoundary (e.pre Y) j := by
  intro bd y hy
  let a := (B.boundaryEquiv j).equiv Y |>.symm bd
  have ha : (B.boundaryEquiv j).equiv Y a = bd := Equiv.apply_symm_apply _ _
  have hab : e.bd j ≫ a = D.inc j ≫ y := by
    apply ((D.boundaryEquiv j).equiv Y).injective
    erw [e.boundary_naturality, ha, (D.boundaryEquiv j).inc_boundary]
    exact hy.symm
  let top := pushout.desc a y hab
  have hh : oneSidedMap e j ≫ s ≫ top = top := by rw [← Category.assoc, hs, Category.id_comp]
  have hb : B.inc j ≫ s ≫ top = a := by
    have h := congrArg (pushout.inl (e.bd j) (D.inc j) ≫ ·) hh
    dsimp only [oneSidedMap,top] at h
    erw [pushout.inl_desc_assoc, pushout.inl_desc] at h
    exact h
  have he : e.obj j ≫ s ≫ top = y := by
    have h := congrArg (pushout.inr (e.bd j) (D.inc j) ≫ ·) hh
    dsimp only [oneSidedMap,top] at h
    erw [pushout.inr_desc_assoc, pushout.inr_desc] at h
    exact h
  exact ⟨s ≫ top, ((B.boundaryEquiv j).inc_boundary _).symm.trans
    ((congrArg ((B.boundaryEquiv j).equiv Y) hb).trans ha), he⟩

theorem jointSource_lift (e : Bool → Hom D B) (Y : K) (k : ℕ)
    (s : B.obj (k+1) ⟶ jointSource e k) (hs : jointSourceMap e k ≫ s = 𝟙 _)
    (t : B.obj k ⟶ Y) (u : Bool → (D.obj (k+1) ⟶ Y))
    (hu : ∀ ε, (e ε).obj k ≫ t = D.diagram.source k ≫ u ε) :
    ∃ l : B.obj (k+1) ⟶ Y, B.diagram.source k ≫ l = t ∧
      ∀ ε, (e ε).obj (k+1) ≫ l = u ε := by
  let top := TwoEndpoints.desc (D.diagram.source k) (fun ε => (e ε).obj k) t u hu
  have hh : jointSourceMap e k ≫ s ≫ top = top := by rw [← Category.assoc, hs, Category.id_comp]
  refine ⟨s ≫ top, ?_, ?_⟩
  · have h := congrArg (TwoEndpoints.base (D.diagram.source k) (fun ε => (e ε).obj k) ≫ ·) hh
    dsimp only [jointSourceMap,top] at h
    erw [TwoEndpoints.base_desc_assoc, TwoEndpoints.base_desc] at h
    exact h
  · intro ε
    have h := congrArg (TwoEndpoints.endpoint (D.diagram.source k) (fun ε => (e ε).obj k) ε ≫ ·) hh
    dsimp only [jointSourceMap,top] at h
    erw [TwoEndpoints.endpoint_desc_assoc, TwoEndpoints.endpoint_desc] at h
    exact h
end GlobularFrame
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)]
variable (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))

theorem fullCylinderEvaluation_bijective (Y : CutoffModels C q) (j : ℕ) :
    Function.Bijective ((fullCylinderEvaluation hC q n hnq H Y).app j) := by
  have h₁ : Function.LeftInverse ((fullCylinderCoevaluation hC q n hnq H Y).app j)
      ((fullCylinderEvaluation hC q n hnq H Y).app j) := by
    intro a
    exact congrFun (congrArg (fun f => f.app j) (fullCylinderEvaluation_coevaluation hC q n hnq H Y)) a
  have h₂ : Function.RightInverse ((fullCylinderCoevaluation hC q n hnq H Y).app j)
      ((fullCylinderEvaluation hC q n hnq H Y).app j) := by
    intro a
    exact congrFun (congrArg (fun f => f.app j) (fullCylinderCoevaluation_evaluation hC q n hnq H Y)) a
  exact ⟨h₁.injective,h₂.surjective⟩

theorem fullCylinderEndpoint_liftsBoundary (Y : CutoffModels C q) (ε : Bool) (j : ℕ) :
    GlobularSet.LiftsBoundary (underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε)) j := by
  rw [fullCylinderEndpoint_evaluation]
  obtain ⟨s,hs⟩ := cylinder_oneSided_split hC q n hnq H j ε
  exact ((GlobularSet.liftsBoundary_of_bijective _ j (fun k _ =>
    fullCylinderEvaluation_bijective hC q n hnq H Y k)).comp
      ((cylinderEndpoint hC q n ε).pre_liftsBoundary Y j s hs)).comp
    (GlobularSet.liftsBoundary_of_bijective _ j (fun k _ => (cutoffCellEquiv hC q Y k).bijective))

theorem fullCylinder_joint (Y : CutoffModels C q) (k : ℕ) (hk : n ≤ k)
    (t : (fullCylinder hC q n hnq H Y).underlying.Cell k)
    (u : Bool → Y.obj.underlying.Cell (k+1))
    (hu : ∀ ε, (underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε)).app k t =
      Y.obj.underlying.source k (u ε)) :
    ∃ l : (fullCylinder hC q n hnq H Y).underlying.Cell (k+1),
      (fullCylinder hC q n hnq H Y).underlying.source k l = t ∧
      ∀ ε, (underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε)).app (k+1) l = u ε := by
  let E := fullCylinderEvaluation hC q n hnq H Y
  let D := cutoffDiskCoevaluation hC q Y
  have hh ε : (cylinderEndpoint hC q n ε).obj k ≫ E.app k t =
      (cutoffDiskFrame hC q).diagram.source k ≫ D.app (k+1) (u ε) := by
    apply (cutoffCellEquiv hC q Y k).injective
    have he := congrFun (congrArg (fun f => f.app k)
      (fullCylinderEndpoint_evaluation hC q n hnq H Y ε)) t
    change (underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε)).app k t =
      cutoffCellEquiv hC q Y k ((cylinderEndpoint hC q n ε).obj k ≫ E.app k t) at he
    exact he.symm.trans ((hu ε).trans ((cutoffCellEquiv_source hC q k _).trans
      (congrArg (Y.obj.underlying.source k) (Equiv.apply_symm_apply _ _))).symm)
  obtain ⟨s,hs⟩ := cylinder_joint_split hC q n hnq H k hk
  obtain ⟨l,hl,he⟩ := GlobularFrame.jointSource_lift (cylinderEndpoint hC q n) Y k s hs
    (E.app k t) (fun ε => D.app (k+1) (u ε)) hh
  obtain ⟨z,hz⟩ := (fullCylinderEvaluation_bijective hC q n hnq H Y (k+1)).surjective l
  refine ⟨z, ?_, ?_⟩
  · apply (fullCylinderEvaluation_bijective hC q n hnq H Y k).injective
    rw [E.source_app, hz]
    exact hl
  · intro ε
    have h := congrFun (congrArg (fun f => f.app (k+1))
      (fullCylinderEndpoint_evaluation hC q n hnq H Y ε)) z
    change (underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε)).app (k+1) z =
      cutoffCellEquiv hC q Y (k+1) ((cylinderEndpoint hC q n ε).obj (k+1) ≫ E.app (k+1) z) at h
    rw [hz] at h
    exact h.trans ((congrArg (cutoffCellEquiv hC q Y (k+1)) (he ε)).trans
      (Equiv.apply_symm_apply _ _))
end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)]
variable (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))

noncomputable def reflectedCylinder (Y : CutoffModels C q) : CutoffModels C q :=
  cutoffObject hC q (fullCylinder hC q n hnq H Y)

noncomputable def reflectedCylinderEndpoint (Y : CutoffModels C q) (ε : Bool) :
    reflectedCylinder hC q n hnq H Y ⟶ Y :=
  (cutoffEquiv hC q (fullCylinder hC q n hnq H Y) Y).symm
    (fullCylinderEndpoint hC q n hnq H Y ε)

theorem reflectedCylinderEndpoint_factor (Y : CutoffModels C q) (ε : Bool) :
    cutoffUnit hC q (fullCylinder hC q n hnq H Y) ≫
      (reflectedCylinderEndpoint hC q n hnq H Y ε).hom =
        fullCylinderEndpoint hC q n hnq H Y ε :=
  (cutoffEquiv hC q (fullCylinder hC q n hnq H Y) Y).apply_symm_apply _

theorem reflectedCylinderEndpoint_app (Y : CutoffModels C q) (ε : Bool) (j : ℕ)
    (a : (fullCylinder hC q n hnq H Y).underlying.Cell j) :
    (underlyingMap (reflectedCylinderEndpoint hC q n hnq H Y ε).hom).app j
      ((underlyingMap (cutoffUnit hC q (fullCylinder hC q n hnq H Y))).app j a) =
        (underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε)).app j a :=
  congrFun (congrArg (fun z => (underlyingMap z).app j)
    (reflectedCylinderEndpoint_factor hC q n hnq H Y ε)) a

theorem reflectedCylinderEndpoint_lifts (Y : CutoffModels C q) (ε : Bool) :
    (boundaryClass hC q 0).rlp (reflectedCylinderEndpoint hC q n hnq H Y ε) := by
  rw [boundaryClass_rlp_iff]
  intro j _
  by_cases hj : j ≤ q
  · rw [hasLiftingProperty_I_iff]
    intro bd y hy
    let η := underlyingMap (cutoffUnit hC q (fullCylinder hC q n hnq H Y))
    let p := underlyingMap (reflectedCylinderEndpoint hC q n hnq H Y ε).hom
    have hη := GlobularSet.Hom.boundaryMap_bijective_of_low η j
      (fun k hk => cutoffUnit_low_bijective hC q _ k (by omega))
    obtain ⟨bd',hbd'⟩ := hη.surjective bd
    have hf : η.comp p = underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε) :=
      congrArg underlyingMap (reflectedCylinderEndpoint_factor hC q n hnq H Y ε)
    have hy' : Y.obj.underlying.boundary j y =
        (underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε)).boundaryMap j bd' := by
      exact hy.trans ((congrArg (p.boundaryMap j) hbd'.symm).trans
        ((GlobularSet.Hom.boundaryMap_comp η p j bd').symm.trans
          (congrArg (fun f => f.boundaryMap j bd') hf)))
    obtain ⟨a,ha,hpa⟩ := fullCylinderEndpoint_liftsBoundary hC q n hnq H Y ε j bd' y hy'
    refine ⟨η.app j a, ?_, ?_⟩
    · exact (η.boundary_app j a).symm.trans
        ((congrArg (η.boundaryMap j) ha).trans hbd')
    · exact (reflectedCylinderEndpoint_app hC q n hnq H Y ε j a).trans hpa
  · exact hasLiftingProperty_I_of_unique _ j
      ((reflectedCylinder hC q n hnq H Y).property j (by omega)) (Y.property j (by omega))

theorem reflectedCylinder_joint_cells (Y : CutoffModels C q) (k : ℕ) (hk : n ≤ k)
    (t : (reflectedCylinder hC q n hnq H Y).obj.underlying.Cell k)
    (u : Bool → Y.obj.underlying.Cell (k+1))
    (hu : ∀ ε, (underlyingMap (reflectedCylinderEndpoint hC q n hnq H Y ε).hom).app k t =
      Y.obj.underlying.source k (u ε)) :
    ∃ l : (reflectedCylinder hC q n hnq H Y).obj.underlying.Cell (k+1),
      (reflectedCylinder hC q n hnq H Y).obj.underlying.source k l = t ∧
      ∀ ε, (underlyingMap (reflectedCylinderEndpoint hC q n hnq H Y ε).hom).app (k+1) l = u ε := by
  by_cases hkq : k ≤ q
  · let η := underlyingMap (cutoffUnit hC q (fullCylinder hC q n hnq H Y))
    obtain ⟨t',ht'⟩ := (cutoffUnit_low_bijective hC q (fullCylinder hC q n hnq H Y) k hkq).surjective t
    have hu' ε : (underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε)).app k t' =
        Y.obj.underlying.source k (u ε) := by
      rw [← reflectedCylinderEndpoint_app, ht']
      exact hu ε
    obtain ⟨l,hl,hpl⟩ := fullCylinder_joint hC q n hnq H Y k hk t' u hu'
    refine ⟨η.app (k+1) l, ?_, ?_⟩
    · exact (η.source_app k l).symm.trans ((congrArg (η.app k) hl).trans ht')
    · intro ε
      exact (reflectedCylinderEndpoint_app hC q n hnq H Y ε (k+1) l).trans (hpl ε)
  · let R := reflectedCylinder hC q n hnq H Y
    refine ⟨R.obj.unitCell hC k t, R.obj.unitCell_source hC k t, ?_⟩
    intro ε
    apply (Y.obj.underlying.source_bijective_of_coskeletal q k Y.property (by omega)).injective
    rw [← (underlyingMap (reflectedCylinderEndpoint hC q n hnq H Y ε).hom).source_app,
      R.obj.unitCell_source]
    exact hu ε

noncomputable def cylinderPathData (Y : CutoffModels C q) : CutoffPathData hC q n Y where
  P := reflectedCylinder hC q n hnq H Y
  p₀ := reflectedCylinderEndpoint hC q n hnq H Y false
  p₁ := reflectedCylinderEndpoint hC q n hnq H Y true
  lifts₀ := reflectedCylinderEndpoint_lifts hC q n hnq H Y false
  lifts₁ := reflectedCylinderEndpoint_lifts hC q n hnq H Y true
  joint k hk t u₀ u₁ h₀ h₁ := by
    let R := reflectedCylinder hC q n hnq H Y
    let u : Bool → Y.obj.underlying.Cell (k+1) := fun ε =>
      if ε then cutoffCellEquiv hC q Y (k+1) u₁ else cutoffCellEquiv hC q Y (k+1) u₀
    have hu ε : (underlyingMap (reflectedCylinderEndpoint hC q n hnq H Y ε).hom).app k
        (cutoffCellEquiv hC q R k t) = Y.obj.underlying.source k (u ε) := by
      cases ε
      · have h := congrArg (cutoffCellEquiv hC q Y k) h₀
        erw [cutoffCellEquiv_comp, ← cutoffDiskFrame_source, cutoffCellEquiv_source] at h
        exact h
      · have h := congrArg (cutoffCellEquiv hC q Y k) h₁
        erw [cutoffCellEquiv_comp, ← cutoffDiskFrame_source, cutoffCellEquiv_source] at h
        exact h
    obtain ⟨l,hl,he⟩ := reflectedCylinder_joint_cells hC q n hnq H Y k hk
      (cutoffCellEquiv hC q R k t) u hu
    refine ⟨(cutoffCellEquiv hC q R (k+1)).symm l, ?_, ?_, ?_⟩
    · apply (cutoffCellEquiv hC q R k).injective
      erw [← cutoffDiskFrame_source,cutoffCellEquiv_source, Equiv.apply_symm_apply]
      exact hl
    · apply (cutoffCellEquiv hC q Y (k+1)).injective
      erw [cutoffCellEquiv_comp, Equiv.apply_symm_apply]
      exact he false
    · apply (cutoffCellEquiv hC q Y (k+1)).injective
      erw [cutoffCellEquiv_comp, Equiv.apply_symm_apply]
      exact he true

end GlobularTheory.Model
end Grothendieck

end OAI
end
end

section
section
namespace OAI


namespace Grothendieck.GlobularTheory.Model
open CategoryTheory CategoryTheory.Limits

theorem exactBoundaryTest_of_cutoff_path {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) {X Y : CutoffModels C q} (i : X ⟶ Y)
    (hi : (sourceClass hC q r).rlp.llp i) (hX : Cofibrant hC q X)
    (z : Y ⟶ X) (hz : i ≫ z = 𝟙 X) (P : CutoffPathData hC q r Y) :
    GlobularSet.ExactBoundaryTest (underlyingMap i.hom) := by
  let := cutoff_hasLimits hC q
  obtain ⟨a, ha⟩ := hX P.p₀ P.lifts₀ i
  let u : X ⟶ Y := a ≫ P.p₁
  let := hi (prod.lift P.p₀ P.p₁) P.joint_rlp
  have sq : CommSq a i (prod.lift P.p₀ P.p₁) (prod.lift (𝟙 Y) (z ≫ u)) := by
    constructor
    apply prod.hom_ext
    · simpa only [Category.assoc, prod.lift_fst, Category.comp_id] using ha
    · simp only [Category.assoc, prod.lift_snd]
      rw [← Category.assoc i, hz, Category.id_comp]
  have hf₀ : sq.lift ≫ P.p₀ = 𝟙 Y := by
    have e := congrArg (· ≫ prod.fst) sq.fac_right
    simpa only [Category.assoc, prod.lift_fst] using e
  have hf₁ : sq.lift ≫ P.p₁ = z ≫ u := by
    have e := congrArg (· ≫ prod.snd) sq.fac_right
    simpa only [Category.assoc, prod.lift_snd] using e
  have hp₀ : GlobularSet.LiftsBoundaries (underlyingMap P.p₀.hom) := by
    intro k
    exact (hasLiftingProperty_I_iff k P.p₀.hom).1
      ((boundaryClass_rlp_iff hC q 0 P.p₀).1 P.lifts₀ k (Nat.zero_le k))
  have hp₁ : GlobularSet.LiftsBoundaries (underlyingMap P.p₁.hom) := by
    intro k
    exact (hasLiftingProperty_I_iff k P.p₁.hom).1
      ((boundaryClass_rlp_iff hC q 0 P.p₁).1 P.lifts₁ k (Nat.zero_le k))
  apply GlobularSet.ExactBoundaryTest.of_retract_factor
    (underlyingMap i.hom) (underlyingMap z.hom) (underlyingMap u.hom)
    (congrArg (fun t : X ⟶ X => underlyingMap t.hom) hz) _ (Y.obj.joined_refl hC)
  have hv := GlobularSet.exactBoundaryTest_endpoint_section
    (underlyingMap P.p₀.hom) (underlyingMap P.p₁.hom) (underlyingMap sq.lift.hom)
    hp₀ hp₁
    (fun k x => congrFun (congrArg (fun t => (underlyingMap t.hom).app k) hf₀) x)
    (Y.obj.joined_refl hC)
  have e := congrArg (fun t : Y ⟶ Y => underlyingMap t.hom) hf₁
  change GlobularSet.ExactBoundaryTest (underlyingMap (sq.lift ≫ P.p₁).hom) at hv
  rw [e] at hv
  exact hv

theorem sourceClass_cofibration_mono {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {r s : ℕ} (hrs : r ≤ s) :
    (sourceClass hC q s).rlp.llp ≤ (sourceClass hC q r).rlp.llp := by
  intro X Y i hi P Q p hp
  apply hi p
  rw [sourceClass_rlp_iff] at hp ⊢
  exact fun k hk => hp k (hrs.trans hk)

theorem expansionContraction_mono {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {r s : ℕ} (hrs : r ≤ s) (H : ExpansionContraction hC q r) :
    ExpansionContraction hC q s := by
  intro X Y i hi hX hXF
  exact H i (sourceClass_cofibration_mono hC q hrs i hi) hX hXF

theorem expansionContraction_all {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q r : ℕ) : ExpansionContraction hC q r := by
  let := cutoff_hasColimits hC q
  let := cutoff_hasLimits hC q
  have hall : ∀ m r, q-r = m → ExpansionContraction hC q r := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro r hr
      by_cases hqr : q ≤ r
      · exact expansionContraction_mono hC q hqr (expansionContraction_top hC q)
      · have Hnext : ExpansionContraction hC q (r+1) := @ih (q-(r+1)) (by omega) (r+1) rfl
        exact expansionContraction_of_paths hC q r
          (fun Y => ⟨cylinderPathData hC q r (by omega) Hnext Y⟩)
  exact @hall (q-r) r rfl

theorem cutoff_elementary_exactBoundaryTest {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (hnq : n ≤ q) {X Y : C.Model} (hX : X.IsCellular)
    (a : disk C n ⟶ X) (i : X ⟶ Y) (b : disk C (n+1) ⟶ Y)
    (sq : IsPushout a (J C n) i b) :
    GlobularSet.ExactBoundaryTest (underlyingMap ((cutoffFunctor hC q).map i).hom) := by
  let := cutoff_hasColimits hC q
  let := cutoff_hasLimits hC q
  let F := cutoffFunctor hC q
  let : F.IsLeftAdjoint := (cutoffAdjunction hC q).isLeftAdjoint
  have hi : (sourceClass hC q n).rlp.llp (F.map i) := by
    apply MorphismProperty.of_isPushout (sq.map F)
    intro P Q p hp
    exact hp _ (MorphismProperty.ofHoms.mk (⟨n,le_rfl⟩ : {k : ℕ // n ≤ k}))
  obtain ⟨z,hz⟩ := elementary_pushout_retraction hC n a i b sq
  apply exactBoundaryTest_of_cutoff_path hC q n (F.map i) hi
    (isCellular_cutoff_cofibrant hC q hX) (F.map z)
  · exact (F.map_comp i z).symm.trans ((congrArg F.map hz).trans (F.map_id X))
  · exact cylinderPathData hC q n hnq (expansionContraction_all hC q (n+1)) (F.obj Y)

end Grothendieck.GlobularTheory.Model

end OAI
end
end

section
section
namespace OAI

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits
namespace GlobularSet

theorem exactBoundaryTest_at_of_low_square {X Y R S : GlobularSet.{v}}
    (i : Hom X Y) (j : Hom R S) (a : Hom X R) (b : Hom Y S)
    (sq : i.comp b = a.comp j) (hj : ExactBoundaryTest j) (d : ℕ)
    (ha : ∀ k, k ≤ d → Function.Bijective (a.app k))
    (hb : Function.Injective (b.app d)) (hb₁ : Function.Surjective (b.app (d+1)))
    (bd : X.Boundary d) (y : Y.Cell d) (hy : Y.boundary d y = i.boundaryMap d bd) :
    ∃ x : X.Cell d, X.boundary d x = bd ∧ Y.Joined d (i.app d x) y := by
  have hy' : S.boundary d (b.app d y) = j.boundaryMap d (a.boundaryMap d bd) := by
    rw [← b.boundary_app,hy, ← Hom.boundaryMap_comp, sq, Hom.boundaryMap_comp]
  obtain ⟨r,hr,z,zs,zt⟩ := hj d (a.boundaryMap d bd) (b.app d y) hy'
  obtain ⟨x,hx⟩ := (ha d le_rfl).surjective r
  have hxbd : X.boundary d x = bd := by
    apply (Hom.boundaryMap_bijective_of_low a d (fun k hk => ha k (by omega))).injective
    rw [a.boundary_app,hx,hr]
  obtain ⟨c,hc⟩ := hb₁ z
  have hsquare : b.app d (i.app d x) = j.app d (a.app d x) :=
    congrFun (congrArg (fun f => f.app d) sq) x
  refine ⟨x,hxbd,c, ?_, ?_⟩
  · apply hb
    rw [b.source_app,hc,zs,hsquare,hx]
  · apply hb
    rw [b.target_app,hc,zt]

end GlobularSet

theorem elementary_expansion_oai (C : GlobularTheory.{v}) (hC : C.IsCoherator)
    (X : C.Model) (hX : X.IsCellular) (n : ℕ)
    (a : GlobularTheory.Model.disk C n ⟶ X)
    (Y : C.Model) (i : X ⟶ Y)
    (b : GlobularTheory.Model.disk C (n + 1) ⟶ Y)
    (square : IsPushout a (GlobularTheory.Model.J C n) i b) :
    GlobularTheory.Model.WeakEquivalence hC i := by
  apply GlobularTheory.Model.weakEquivalence_of_exactBoundaryTest hC
  intro d bd y hy
  let q := max (n+1) (d+1)
  have hnq : n ≤ q := by dsimp [q]; omega
  have hdq : d ≤ q := by dsimp [q]; omega
  have hd₁q : d+1 ≤ q := Nat.le_max_right _ _
  let F := GlobularTheory.Model.cutoffFunctor hC q
  let ηX := GlobularTheory.Model.underlyingMap
    (GlobularTheory.Model.cutoffUnit hC q X)
  let ηY := GlobularTheory.Model.underlyingMap
    (GlobularTheory.Model.cutoffUnit hC q Y)
  have hs : (GlobularTheory.Model.underlyingMap i).comp ηY =
      ηX.comp (GlobularTheory.Model.underlyingMap (F.map i).hom) :=
    congrArg GlobularTheory.Model.underlyingMap
      ((GlobularTheory.Model.cutoffAdjunction hC q).unit.naturality i)
  exact GlobularSet.exactBoundaryTest_at_of_low_square
    (GlobularTheory.Model.underlyingMap i)
    (GlobularTheory.Model.underlyingMap (F.map i).hom) ηX ηY hs
    (GlobularTheory.Model.cutoff_elementary_exactBoundaryTest hC q n hnq hX a i b square)
    d (fun k hk => GlobularTheory.Model.cutoffUnit_low_bijective hC q X k (hk.trans hdq))
    (GlobularTheory.Model.cutoffUnit_low_bijective hC q Y d hdq).injective
    (GlobularTheory.Model.cutoffUnit_low_bijective hC q Y (d+1) hd₁q).surjective bd y hy

end Grothendieck

end OAI
end
end

section
section
namespace OAI

namespace Grothendieck.GlobularTheory.Model
open CategoryTheory

noncomputable instance homotopyGroupGroup {C : GlobularTheory.{v}} (X : C.Model)
    (hC : C.IsCoherator) (x : X.underlying.Cell 0) (n : ℕ) :
    Group (X.HomotopyGroup hC x n) :=
  show Group (End (⟨X.baseCell hC x n⟩ : CellGroupoid X hC n)) from inferInstance

noncomputable def homotopyMapHom {C : GlobularTheory.{v}} {X Y : C.Model}
    (f : X ⟶ Y) (hC : C.IsCoherator) (x : X.underlying.Cell 0) (n : ℕ) :
    X.HomotopyGroup hC x n →* Y.HomotopyGroup hC ((underlyingMap f).app 0 x) n where
  toFun := homotopyMap f hC x n
  map_one' := by
    apply congrArg (Quot.mk _)
    apply Subtype.ext
    exact (map_unitCell f hC n (X.baseCell hC x n)).trans
      (congrArg (Y.unitCell hC n) (map_baseCell f hC x n))
  map_mul' a b := by
    induction a using Quot.inductionOn with | h a =>
    induction b using Quot.inductionOn with | h b =>
    apply congrArg (Quot.mk _)
    apply Subtype.ext
    exact map_compCell f hC n b.1 a.1 _

noncomputable def homotopyGroupIsoOfWeakEquivalence {C : GlobularTheory.{v}}
    {X Y : C.Model} (f : X ⟶ Y) (hC : C.IsCoherator) (hf : WeakEquivalence hC f)
    (x : X.underlying.Cell 0) (n : ℕ) :
    X.HomotopyGroup hC x n ≃* Y.HomotopyGroup hC ((underlyingMap f).app 0 x) n :=
  MulEquiv.ofBijective (homotopyMapHom f hC x n) (hf.2 x n)

end Grothendieck.GlobularTheory.Model

end OAI
end
end

section
section

end
end

theorem solution : type_of% @OAI.Grothendieck.elementary_expansion_oai := @OAI.Grothendieck.elementary_expansion_oai
