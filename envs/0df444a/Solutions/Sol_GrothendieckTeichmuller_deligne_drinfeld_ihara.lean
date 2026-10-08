-- Prove2me | solution 1 for GrothendieckTeichmuller.deligne_drinfeld_ihara
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T13:55:17.781118+00:00
-- url     : https://prove2.me/submissions/c05b2881-9b18-42c7-97e9-fad12dcd11c6

import Definitions.Def_DeligneDrinfeld
import Definitions.Def_GT_grt1
import Theorems.Thm_GrothendieckTeichmuller_ihara_deriv_commutator
import Theorems.Thm_OAI_DeligneDrinfeld_main
import Theorems.Thm_GrothendieckTeichmuller_ihara_deriv_injOn_grt1
import Mathlib

universe u v

section
section
namespace OAI

noncomputable section
namespace DeligneDrinfeld

theorem freeLie_induction {R α : Type*} [CommRing R]
    {P : FreeLieAlgebra R α → Prop} (h0 : P 0)
    (hg : ∀ a, P (FreeLieAlgebra.of R a))
    (ha : ∀ a b, P a → P b → P (a+b))
    (hs : ∀ (r : R) a, P a → P (r • a))
    (hl : ∀ a b, P a → P b → P ⁅a,b⁆) (q : FreeLieAlgebra R α) : P q := by
  let K : LieSubalgebra R (FreeLieAlgebra R α) :=
    { carrier := {a | P a}
      zero_mem' := h0
      add_mem' := fun ha' hb' => ha _ _ ha' hb'
      smul_mem' := fun r a h => hs r a h
      lie_mem' := fun ha' hb' => hl _ _ ha' hb' }
  let f : FreeLieAlgebra R α →ₗ⁅R⁆ K :=
    FreeLieAlgebra.lift R (fun a => ⟨FreeLieAlgebra.of R a, hg a⟩)
  have hf : K.incl.comp f = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [f]
  have h := (f q).property
  change P ((K.incl.comp f) q) at h
  simpa only [hf, LieHom.id_apply] using h

@[ext] theorem Tangent.ext {a b : Tangent} (h : a.base = b.base)
    (k : a.velocity = b.velocity) : a = b := by cases a; cases b; simp_all

@[simp] theorem Tangent.base_zero : (0 : Tangent).base = 0 := rfl
@[simp] theorem Tangent.velocity_zero : (0 : Tangent).velocity = 0 := rfl
@[simp] theorem Tangent.base_add (a b : Tangent) : (a+b).base = a.base+b.base := rfl
@[simp] theorem Tangent.velocity_add (a b : Tangent) :
    (a+b).velocity = a.velocity+b.velocity := rfl
@[simp] theorem Tangent.base_smul (q : ℚ) (a : Tangent) : (q • a).base = q • a.base := rfl
@[simp] theorem Tangent.velocity_smul (q : ℚ) (a : Tangent) :
    (q • a).velocity = q • a.velocity := rfl
@[simp] theorem Tangent.base_lie (a b : Tangent) : ⁅a,b⁆.base = ⁅a.base,b.base⁆ := rfl
@[simp] theorem Tangent.velocity_lie (a b : Tangent) :
    ⁅a,b⁆.velocity = ⁅a.velocity,b.base⁆ + ⁅a.base,b.velocity⁆ := rfl

@[simp] theorem eval_x {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) :
    eval a b x = a := by simp [eval, x]
@[simp] theorem eval_y {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) :
    eval a b y = b := by simp [eval, y]

def Tangent.baseHom : Tangent →ₗ⁅ℚ⁆ L where
  toFun := Tangent.base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

@[simp] theorem tangentLift_base (p q : L) : (tangentLift p q).base = q := by
  have h : Tangent.baseHom.comp (tangentLift p) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [tangentLift, Tangent.baseHom, x, y] <;> rfl
  exact LieHom.congr_fun h q

@[simp] theorem D_x (p : L) : D p x = 0 := by simp [D, tangentLift, x]
@[simp] theorem D_y (p : L) : D p y = ⁅y,p⁆ := by simp [D, tangentLift, y]
@[simp] theorem D_zero (p : L) : D p 0 = 0 := by simp [D]
@[simp] theorem D_add (p q r : L) : D p (q+r) = D p q + D p r := by simp [D]
@[simp] theorem D_smul (p q : L) (a : ℚ) : D p (a • q) = a • D p q := by simp [D]
theorem D_lie (p q r : L) : D p ⁅q,r⁆ = ⁅D p q,r⁆ + ⁅q,D p r⁆ := by
  simp [D, LieHom.map_lie]

def derivation (p : L) : LieDerivation ℚ L L where
  toFun := D p
  map_add' := D_add p
  map_smul' a q := D_smul p q a
  leibniz' a b := by
    change D p ⁅a,b⁆ = ⁅a,D p b⁆ - ⁅b,D p a⁆
    rw [D_lie, sub_eq_add_neg, lie_skew, add_comm]

@[simp] theorem derivation_apply (p q : L) : derivation p q = D p q := rfl

theorem derivation_ext {d₁ d₂ : LieDerivation ℚ L L}
    (hx : d₁ x = d₂ x) (hy : d₁ y = d₂ y) : d₁ = d₂ := by
  ext q
  induction q using freeLie_induction with
  | h0 => simp
  | hg i => cases i; exact hx; exact hy
  | ha a b ha hb => simp [ha, hb]
  | hs r a ha => simp [ha]
  | hl a b ha hb => simp [ha, hb]

@[simp] theorem D_zero_left (q : L) : D 0 q = 0 := by
  have h : derivation 0 = 0 := by
    apply derivation_ext <;> simp
  exact LieDerivation.congr_fun h q

@[simp] theorem D_add_left (p q r : L) : D (p+q) r = D p r + D q r := by
  have h : derivation (p+q) = derivation p + derivation q := by
    apply derivation_ext <;> simp [lie_add]
  exact LieDerivation.congr_fun h r

@[simp] theorem D_smul_left (p q : L) (a : ℚ) : D (a • p) q = a • D p q := by
  have h : derivation (a • p) = a • derivation p := by
    apply derivation_ext <;> simp
  exact LieDerivation.congr_fun h q

namespace AssociativeModel

variable {α : Type*}
abbrev FL (α : Type*) := FreeLieAlgebra ℚ α
abbrev A (α : Type*) := MonoidAlgebra ℚ (FreeMonoid α)
attribute [local instance] LieRing.ofAssociativeRing

def atom (a : α) : A α := MonoidAlgebra.single (FreeMonoid.of a) 1

def embed : FL α →ₗ⁅ℚ⁆ A α := FreeLieAlgebra.lift ℚ atom

@[simp] theorem embed_of (a : α) : embed (FreeLieAlgebra.of ℚ a) = atom a := by
  simp [embed]

def wordLinear {M : Type*} [AddCommGroup M] [Module ℚ M]
    (f : FreeMonoid α → M) : A α →ₗ[ℚ] M :=
  (Finsupp.linearCombination ℚ f).comp (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

@[simp] theorem wordLinear_single {M : Type*} [AddCommGroup M] [Module ℚ M]
    (f : FreeMonoid α → M) (w : FreeMonoid α) (c : ℚ) :
    wordLinear f (MonoidAlgebra.single w c) = c • f w := by
  change Finsupp.linearCombination ℚ f (Finsupp.single w c) = _; simp

def wordAct : FreeMonoid α →* Module.End ℚ (FL α) :=
  FreeMonoid.lift (fun a => LieAlgebra.ad ℚ (FL α) (FreeLieAlgebra.of ℚ a))

def act : A α →ₐ[ℚ] Module.End ℚ (FL α) :=
  MonoidAlgebra.lift ℚ (Module.End ℚ (FL α)) (FreeMonoid α) wordAct

@[simp] theorem act_single (w : FreeMonoid α) (c : ℚ) :
    act (MonoidAlgebra.single w c) = c • wordAct w := by simp [act]

@[simp] theorem wordAct_of_apply (a : α) (q : FL α) :
    wordAct (FreeMonoid.of a) q = ⁅FreeLieAlgebra.of ℚ a,q⁆ := by
  simp [wordAct, LieAlgebra.ad_apply]

@[simp] theorem act_embed (p q : FL α) : act (embed p) q = ⁅p,q⁆ := by
  have h : act.toLieHom.comp embed = LieAlgebra.ad ℚ (FL α) := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [atom, wordAct]
  exact LinearMap.congr_fun (LieHom.congr_fun h p) q

end AssociativeModel

namespace FreeDerivations

variable {R : Type*} [CommRing R]
variable {M : Type*} [LieRing M] [LieAlgebra R M]

structure Jet (R M : Type*) [CommRing R] [LieRing M] [LieAlgebra R M] where
  base : M
  velocity : M

def Jet.equiv : Jet R M ≃ M × M where
  toFun z := (z.base, z.velocity)
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (Jet R M) := Jet.equiv.addCommGroup
instance : Module R (Jet R M) := Jet.equiv.addEquiv.module R
instance : Bracket (Jet R M) (Jet R M) :=
  ⟨fun a b => ⟨⁅a.base, b.base⁆,
    ⁅a.velocity, b.base⁆ + ⁅a.base, b.velocity⁆⟩⟩

@[ext] theorem Jet.ext {a b : Jet R M} (h : a.base = b.base)
    (k : a.velocity = b.velocity) : a = b := by cases a; cases b; simp_all

@[simp] theorem Jet.base_zero : (0 : Jet R M).base = 0 := rfl
@[simp] theorem Jet.velocity_zero : (0 : Jet R M).velocity = 0 := rfl
@[simp] theorem Jet.base_add (a b : Jet R M) : (a+b).base = a.base+b.base := rfl
@[simp] theorem Jet.velocity_add (a b : Jet R M) :
    (a+b).velocity = a.velocity+b.velocity := rfl
@[simp] theorem Jet.base_smul (q : R) (a : Jet R M) : (q • a).base = q • a.base := rfl
@[simp] theorem Jet.velocity_smul (q : R) (a : Jet R M) :
    (q • a).velocity = q • a.velocity := rfl
@[simp] theorem Jet.base_lie (a b : Jet R M) : ⁅a,b⁆.base = ⁅a.base,b.base⁆ := rfl
@[simp] theorem Jet.velocity_lie (a b : Jet R M) :
    ⁅a,b⁆.velocity = ⁅a.velocity,b.base⁆ + ⁅a.base,b.velocity⁆ := rfl

instance : LieRing (Jet R M) where
  add_lie a b c := by (ext <;> simp [add_lie]); abel
  lie_add a b c := by (ext <;> simp [lie_add]); abel
  lie_self a := by
    ext
    · simp
    · change ⁅a.velocity, a.base⁆ + ⁅a.base, a.velocity⁆ = 0
      rw [← lie_skew a.velocity a.base]
      exact neg_add_cancel _
  leibniz_lie a b c := by (ext <;> simp [lie_add, add_lie, lie_lie]); abel
instance : LieAlgebra R (Jet R M) where
  lie_smul q a b := by ext <;> simp [lie_smul, smul_add]

def Jet.baseHom : Jet R M →ₗ⁅R⁆ M where
  toFun := Jet.base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' {_ _} := rfl

variable {α : Type*}
local notation "F" => FreeLieAlgebra R α

def jetLift (f : α → F) : F →ₗ⁅R⁆ Jet R F :=
  FreeLieAlgebra.lift R (fun a => ⟨FreeLieAlgebra.of R a, f a⟩)

@[simp] theorem jetLift_base (f : α → F) (p : F) :
    (jetLift f p).base = p := by
  have h : Jet.baseHom.comp (jetLift f) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [jetLift, Jet.baseHom]
    rfl
  exact LieHom.congr_fun h p

def extend (f : α → F) : LieDerivation R F F where
  toFun q := (jetLift f q).velocity
  map_add' a b := by
    change (jetLift f (a+b)).velocity = _
    rw [map_add]
    rfl
  map_smul' r a := by
    change (jetLift f (r • a)).velocity = _
    rw [map_smul]
    rfl
  leibniz' a b := by
    change (jetLift f ⁅a,b⁆).velocity = ⁅a,(jetLift f b).velocity⁆ - ⁅b,(jetLift f a).velocity⁆
    rw [LieHom.map_lie, Jet.velocity_lie, jetLift_base, jetLift_base]
    rw [sub_eq_add_neg, lie_skew, add_comm]

@[simp] theorem extend_of (f : α → F) (a : α) :
    extend f (FreeLieAlgebra.of R a) = f a := by
  change (jetLift f (FreeLieAlgebra.of R a)).velocity = _
  simp [jetLift]

@[ext] theorem ext {d₁ d₂ : LieDerivation R F F}
    (h : ∀ a, d₁ (FreeLieAlgebra.of R a) = d₂ (FreeLieAlgebra.of R a)) : d₁ = d₂ := by
  ext q
  induction q using freeLie_induction with
  | h0 => simp
  | hg a => exact h a
  | ha a b ha hb => simp [ha, hb]
  | hs r a ha => simp [ha]
  | hl a b ha hb => simp [ha, hb]

variable [DecidableEq α]
def pair (i j : α) : LieDerivation R F F :=
  extend (fun k => if k = i then ⁅FreeLieAlgebra.of R i, FreeLieAlgebra.of R j⁆
    else if k = j then ⁅FreeLieAlgebra.of R j, FreeLieAlgebra.of R i⁆ else 0)

@[simp] theorem pair_of_left (i j : α) :
    pair (R := R) i j (FreeLieAlgebra.of R i) = ⁅FreeLieAlgebra.of R i,FreeLieAlgebra.of R j⁆ := by
  simp [pair]

@[simp] theorem pair_of_right (i j : α) :
    pair (R := R) i j (FreeLieAlgebra.of R j) = ⁅FreeLieAlgebra.of R j,FreeLieAlgebra.of R i⁆ := by
  by_cases h : j = i
  · subst j; simp
  · simp [pair, h]

@[simp] theorem pair_of_other (i j k : α) (hi : k ≠ i) (hj : k ≠ j) :
    pair (R := R) i j (FreeLieAlgebra.of R k) = 0 := by
  simp [pair, hi, hj]

theorem pair_comm (i j : α) : pair (R := R) i j = pair j i := by
  apply ext
  intro a
  by_cases hi : a=i
  · subst a; simp
  by_cases hj : a=j
  · subst a; simp
  simp [hi,hj]

theorem pair_self (i : α) : pair (R := R) i i = 0 := by
  apply ext
  intro a
  by_cases hi : a=i
  · subst a; simp
  simp [hi]

theorem pair_disjoint (i j k l : α)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    ⁅pair (R := R) i j,pair (R := R) k l⁆ = 0 := by
  apply ext
  intro a
  by_cases hai : a=i
  · subst a; simp [hik,hil,hjk,hjl]
  by_cases haj : a=j
  · subst a; simp [hik,hil,hjk,hjl]
  by_cases hak : a=k
  · subst a; simp [hik.symm,hjk.symm,hil.symm,hjl.symm]
  by_cases hal : a=l
  · subst a; simp [hik.symm,hjk.symm,hil.symm,hjl.symm]
  simp [hai,haj,hak,hal]

theorem pair_three (i j k : α) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅pair (R := R) i j, pair (R := R) i k + pair (R := R) j k⁆ = 0 := by
  apply ext
  intro a
  by_cases hai : a=i
  · subst a
    simp [hik,hij,hjk,hij.symm,hik.symm,hjk.symm]
    grind [lie_skew, lie_lie]
  by_cases haj : a=j
  · subst a
    simp [hik,hij,hjk,hij.symm,hik.symm,hjk.symm]
    grind [lie_skew, lie_lie]
  by_cases hak : a=k
  · subst a
    simp [hik.symm,hjk.symm]
    grind [lie_skew, lie_lie]
  simp [hai,haj,hak]

end FreeDerivations

namespace BraidRepresentation
open FreeDerivations LieAlgebra
variable {R α : Type*} [CommRing R] [DecidableEq α]
local notation "F" => FreeLieAlgebra R α
local notation "Der" => LieDerivation R F F
local notation "SD" => SemiDirectSum F Der (LieHom.id : Der →ₗ⁅R⁆ Der)

def fiber (i : α) : SD := SemiDirectSum.inl LieHom.id (FreeLieAlgebra.of R i)
def base (i j : α) : SD := SemiDirectSum.inr LieHom.id (pair i j)

def chord : Option α → Option α → SD
  | none, none => 0
  | none, some j => fiber j
  | some i, none => fiber i
  | some i, some j => base i j

@[simp] theorem chord_none_none : chord (R := R) (α := α) none none = 0 := rfl
@[simp] theorem chord_none_some (j : α) : chord (R := R) none (some j) = fiber j := rfl
@[simp] theorem chord_some_none (i : α) : chord (R := R) (some i) none = fiber i := rfl
@[simp] theorem chord_some_some (i j : α) : chord (R := R) (some i) (some j) = base i j := rfl

theorem chord_comm (i j : Option α) : chord (R := R) i j = chord j i := by
  cases i <;> cases j <;> simp [base, pair_comm]

@[simp] theorem chord_self (i : Option α) : chord (R := R) i i = 0 := by
  cases i <;> simp [base, pair_self]

theorem base_fiber (i j k : α) :
    ⁅base (R := R) i j, fiber k⁆ = SemiDirectSum.inl LieHom.id
      (pair (R := R) i j (FreeLieAlgebra.of R k)) := by
  simp [base, fiber]

theorem fiber_base (i j k : α) :
    ⁅fiber (R := R) k, base i j⁆ = - SemiDirectSum.inl LieHom.id
      (pair (R := R) i j (FreeLieAlgebra.of R k)) := by
  rw [← lie_skew, base_fiber]

theorem chord_disjoint (i j k l : Option α)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    ⁅chord (R := R) i j, chord (R := R) k l⁆ = 0 := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    simp_all [base, fiber, pair_disjoint]
  all_goals apply pair_of_other <;> intro h <;> subst_vars <;> contradiction

theorem chord_three (i j k : Option α)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅chord (R := R) i j, chord (R := R) i k + chord (R := R) j k⁆ = 0 := by
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      cases k with
      | none => exact (hik rfl).elim
      | some k =>
        rw [chord_none_some, chord_none_some, chord_some_some, lie_add, fiber_base]
        simp [fiber]
        grind [lie_skew]
  | some i =>
    cases j with
    | none =>
      cases k with
      | none => exact (hjk rfl).elim
      | some k =>
        rw [chord_some_none, chord_some_some, chord_none_some, lie_add, fiber_base]
        simp [fiber]
        grind [lie_skew]
    | some j =>
      cases k with
      | none =>
        rw [chord_some_some, chord_some_none, chord_some_none, lie_add,
          base_fiber, base_fiber]
        simp only [pair_of_left, pair_of_right, ← map_add]
        grind [lie_skew]
      | some k =>
        simp only [chord_some_some, base, ← map_add, ← LieHom.map_lie]
        rw [pair_three _ _ _ (fun h => hij (congrArg some h))
          (fun h => hik (congrArg some h)) (fun h => hjk (congrArg some h)), map_zero]

end BraidRepresentation

namespace BraidModel
open LieAlgebra
abbrev Fiber := FreeLieAlgebra ℚ (Fin 3)
abbrev Der := LieDerivation ℚ Fiber Fiber
abbrev Model := SemiDirectSum Fiber Der (LieHom.id : Der →ₗ⁅ℚ⁆ Der)
def chord (i j : Fin 4) : Model :=
  BraidRepresentation.chord (finSuccEquiv' (1 : Fin 4) i) (finSuccEquiv' (1 : Fin 4) j)

theorem chord_comm (i j : Fin 4) : chord i j = chord j i :=
  BraidRepresentation.chord_comm _ _

@[simp] theorem chord_self (i : Fin 4) : chord i i = 0 :=
  BraidRepresentation.chord_self _

def preMap : BraidFree →ₗ⁅ℚ⁆ Model := FreeLieAlgebra.lift ℚ (fun e => chord e.val.1 e.val.2)

@[simp] theorem preMap_chord (i j : Fin 4) : preMap (DeligneDrinfeld.chord i j) = chord i j := by
  unfold DeligneDrinfeld.chord
  split_ifs with hij hji
  · simp [preMap]
  · simp [preMap, chord_comm j i]
  · have h : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
    subst j
    simp

theorem ideal_le_ker : braidIdeal ≤ preMap.ker := by
  rw [braidIdeal, LieSubmodule.lieSpan_le]
  intro z hz
  change preMap z = 0
  rcases hz with ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩ | ⟨i,j,k,hij,hik,hjk,rfl⟩
  · rw [LieHom.map_lie, preMap_chord, preMap_chord]
    exact BraidRepresentation.chord_disjoint _ _ _ _
      ((finSuccEquiv' (1 : Fin 4)).injective.ne hik) ((finSuccEquiv' (1 : Fin 4)).injective.ne hil)
      ((finSuccEquiv' (1 : Fin 4)).injective.ne hjk) ((finSuccEquiv' (1 : Fin 4)).injective.ne hjl)
  · rw [LieHom.map_lie, map_add, preMap_chord, preMap_chord, preMap_chord]
    exact BraidRepresentation.chord_three _ _ _
      ((finSuccEquiv' (1 : Fin 4)).injective.ne hij) ((finSuccEquiv' (1 : Fin 4)).injective.ne hik)
      ((finSuccEquiv' (1 : Fin 4)).injective.ne hjk)

def map : T4 →ₗ⁅ℚ⁆ Model :=
  { braidIdeal.toSubmodule.liftQ preMap.toLinearMap ideal_le_ker with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact preMap.map_lie a b }

@[simp] theorem map_t (i j : Fin 4) : map (t i j) = chord i j := preMap_chord i j

end BraidModel

namespace AssociativeModel
attribute [local instance] LieRing.ofAssociativeRing
variable {α : Type*}

end AssociativeModel

theorem map_eval {M N : Type*} [LieRing M] [LieAlgebra ℚ M]
    [LieRing N] [LieAlgebra ℚ N] (f : M →ₗ⁅ℚ⁆ N) (a b : M) (p : L) :
    f (eval a b p) = eval (f a) (f b) p := by
  have h : f.comp (eval a b) = eval (f a) (f b) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [eval]
  exact LieHom.congr_fun h p

@[simp] theorem chord_comm (i j : Fin 4) : chord i j = chord j i := by
  unfold chord
  split_ifs <;> first | rfl | omega

@[simp] theorem t_comm (i j : Fin 4) : t i j = t j i := by
  unfold t
  rw [chord_comm]

theorem t_disjoint (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ⁅t i j,t k l⁆ = 0 := by
  rw [t, t, ← LieSubmodule.Quotient.mk_bracket, LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inl ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩)

theorem t_three (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅t i j,t i k + t j k⁆ = 0 := by
  change LieSubmodule.Quotient.mk (⁅chord i j, chord i k + chord j k⁆) = (0 : T4)
  rw [LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inr ⟨i,j,k,hij,hik,hjk,rfl⟩)

namespace BraidModel

end BraidModel

namespace T4Universal
variable {M : Type*} [LieRing M] [LieAlgebra ℚ M]

def pre (f : Fin 4 → Fin 4 → M) : BraidFree →ₗ⁅ℚ⁆ M :=
  FreeLieAlgebra.lift ℚ (fun e => f e.val.1 e.val.2)

theorem pre_chord (f : Fin 4 → Fin 4 → M)
    (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0) (i j : Fin 4) :
    pre f (chord i j) = f i j := by
  unfold chord
  split_ifs with hij hji
  · simp [pre]
  · simp [pre, hs j i]
  · have h : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
    subst j
    simp [hz]

def lift (f : Fin 4 → Fin 4 → M)
    (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0)
    (hd : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      ⁅f i j,f k l⁆ = 0)
    (ht : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ⁅f i j,f i k+f j k⁆ = 0) : T4 →ₗ⁅ℚ⁆ M := by
  have hker : braidIdeal ≤ (pre f).ker := by
    rw [braidIdeal, LieSubmodule.lieSpan_le]
    intro z hz'
    change pre f z = 0
    rcases hz' with ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩ | ⟨i,j,k,hij,hik,hjk,rfl⟩
    · simpa only [LieHom.map_lie, pre_chord f hs hz] using hd i j k l hij hik hil hjk hjl hkl
    · simpa only [LieHom.map_lie, map_add, pre_chord f hs hz] using ht i j k hij hik hjk
  exact { braidIdeal.toSubmodule.liftQ (pre f).toLinearMap hker with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact (pre f).map_lie a b }

@[simp] theorem lift_t (f : Fin 4 → Fin 4 → M) (hs hz hd ht) (i j : Fin 4) :
    lift f hs hz hd ht (t i j) = f i j := pre_chord f hs hz i j

end T4Universal

@[simp] theorem t_self (i : Fin 4) : t i i = 0 := by simp [t, chord]

def t4Rename (e : Equiv.Perm (Fin 4)) : T4 →ₗ⁅ℚ⁆ T4 :=
  T4Universal.lift (fun i j => t (e i) (e j))
    (fun _ _ => t_comm _ _) (fun _ => t_self _)
    (fun _ _ _ _ hij hik hil hjk hjl hkl => t_disjoint _ _ _ _
      (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hil)
      (e.injective.ne hjk) (e.injective.ne hjl) (e.injective.ne hkl))
    (fun _ _ _ hij hik hjk => t_three _ _ _
      (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hjk))

@[simp] theorem t4Rename_t (e : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    t4Rename e (t i j) = t (e i) (e j) := T4Universal.lift_t _ _ _ _ _ _ _

theorem free_action_inner {R α β Z : Type*} [CommRing R]
    [LieRing Z] [LieAlgebra R Z]
    (f : FreeLieAlgebra R α →ₗ⁅R⁆ Z) (g : FreeLieAlgebra R β →ₗ⁅R⁆ Z)
    (h : FreeLieAlgebra R β →ₗ⁅R⁆ LieDerivation R (FreeLieAlgebra R α) (FreeLieAlgebra R α))
    (hg : ∀ b a, f (h (FreeLieAlgebra.of R b) (FreeLieAlgebra.of R a)) =
      ⁅g (FreeLieAlgebra.of R b),f (FreeLieAlgebra.of R a)⁆)
    (q : FreeLieAlgebra R β) (p : FreeLieAlgebra R α) :
    f (h q p) = ⁅g q,f p⁆ := by
  have H : ∀ q : FreeLieAlgebra R β, ∀ p : FreeLieAlgebra R α,
      f (h q p) = ⁅g q,f p⁆ := by
    intro q
    induction q using freeLie_induction with
    | h0 => intro p; simp
    | hg b =>
      intro p
      induction p using freeLie_induction with
      | h0 => simp
      | hg a => exact hg b a
      | ha p r hp hr => simp [hp,hr]
      | hs c p hp => simp [hp]
      | hl p r hp hr =>
        simp [hp,hr,LieHom.map_lie]
        grind [lie_lie,lie_skew]
    | ha q r hq hr => intro p; simp [hq,hr]
    | hs c q hq => intro p; simp [hq]
    | hl q r hq hr => intro p; simp [LieHom.map_lie,hq,hr,lie_lie]
  exact H q p

namespace InnerSemiDirect
open LieAlgebra
variable {R K B Z : Type*} [CommRing R]
  [LieRing K] [LieAlgebra R K] [LieRing B] [LieAlgebra R B]
  [LieRing Z] [LieAlgebra R Z]
variable (action : B →ₗ⁅R⁆ LieDerivation R K K)
  (f : K →ₗ⁅R⁆ Z) (g : B →ₗ⁅R⁆ Z)
  (h : ∀ q p, f (action q p) = ⁅g q,f p⁆)

def lift : SemiDirectSum K B action →ₗ⁅R⁆ Z where
  toFun z := f z.left + g z.right
  map_add' z t := by simp; abel
  map_smul' c z := by simp [smul_add]
  map_lie' {z t} := by
    simp only [SemiDirectSum.lie_eq_mk, map_sub, map_add, LieHom.map_lie, h,
      add_lie, lie_add]
    rw [sub_eq_add_neg, lie_skew]
    abel

@[simp] theorem lift_inl (p : K) : lift action f g h (SemiDirectSum.inl action p) = f p := by
  simp [lift]
@[simp] theorem lift_inr (p : B) : lift action f g h (SemiDirectSum.inr action p) = g p := by
  simp [lift]
end InnerSemiDirect

namespace SpecialFiber
open LieAlgebra FreeDerivations
abbrev F := FreeLieAlgebra ℚ (Fin 3)
def fa : F := FreeLieAlgebra.of ℚ 0
def fb : F := FreeLieAlgebra.of ℚ 1
def fc : F := FreeLieAlgebra.of ℚ 2

def action : L →ₗ⁅ℚ⁆ LieDerivation ℚ F F := eval (pair 0 1) (pair 1 2)
abbrev M := SemiDirectSum F L action

def a : M := SemiDirectSum.inl action fa
def b : M := SemiDirectSum.inl action fb
def c : M := SemiDirectSum.inl action fc
def u : M := SemiDirectSum.inr action x
def v : M := SemiDirectSum.inr action y
def w : M := -a-b-c-u-v

theorem au : ⁅a,u⁆ = -⁅a,b⁆ := by
  simp only [a,u,b, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk, SemiDirectSum.neg_eq_mk]
  ext <;> simp [action,fa,fb]
theorem bu : ⁅b,u⁆ = ⁅a,b⁆ := by
  simp only [a,u,b, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fa,fb]
theorem cu : ⁅c,u⁆ = 0 := by
  simp only [c,u, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fc]
theorem av : ⁅a,v⁆ = 0 := by
  simp only [a,v, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fa]
theorem bv : ⁅b,v⁆ = -⁅b,c⁆ := by
  simp only [b,v,c, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk, SemiDirectSum.neg_eq_mk]
  ext <;> simp [action,fb,fc]
theorem cv : ⁅c,v⁆ = ⁅b,c⁆ := by
  simp only [b,v,c, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fb,fc]

def chord (i j : Fin 4) : M :=
  match i.val, j.val with
  | 0,1 | 1,0 => a
  | 0,2 | 2,0 => u
  | 0,3 | 3,0 => w
  | 1,2 | 2,1 => b
  | 1,3 | 3,1 => c
  | 2,3 | 3,2 => v
  | _,_ => 0

private theorem chord_symm (i j : Fin 4) : chord i j = chord j i := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem chord_zero (i : Fin 4) : chord i i = 0 := by fin_cases i <;> rfl

private theorem chord_disjoint (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) : ⁅chord i j,chord k l⁆ = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all only [ne_eq, not_true_eq_false]
  all_goals fin_cases k <;> simp_all only [not_true_eq_false]
  all_goals fin_cases l <;> simp_all only [not_true_eq_false]
  all_goals dsimp only [chord]
  all_goals simp only [w, lie_sub, sub_lie, lie_neg, neg_lie,
    bu,cu,av,bv,lie_self]
  all_goals grind [lie_skew, au,bu,cu,av,bv,cv]

private theorem chord_three (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅chord i j,chord i k+chord j k⁆ = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all only [ne_eq, not_true_eq_false]
  all_goals fin_cases k <;> simp_all only [not_true_eq_false]
  all_goals dsimp only [chord]
  all_goals simp only [w, lie_sub, sub_lie, lie_neg, neg_lie, lie_add,
    au,bu,cu,av,bv,cv,lie_self]
  all_goals grind [lie_skew, au,bu,cu,av,bv,cv]

def representation : T4 →ₗ⁅ℚ⁆ M :=
  T4Universal.lift chord chord_symm chord_zero chord_disjoint chord_three

@[simp] theorem representation_t (i j : Fin 4) : representation (t i j) = chord i j :=
  T4Universal.lift_t _ _ _ _ _ _ _

def fiberSpec : F →ₗ⁅ℚ⁆ L := FreeLieAlgebra.lift ℚ
  (fun i => if i = 0 then x else if i = 1 then y else -x-y)
def baseSpec : L →ₗ⁅ℚ⁆ L := eval (-x-y) x

@[simp] theorem fiberSpec_fa : fiberSpec fa = x := by simp [fiberSpec,fa]
@[simp] theorem fiberSpec_fb : fiberSpec fb = y := by simp [fiberSpec,fb]
@[simp] theorem fiberSpec_fc : fiberSpec fc = -x-y := by simp [fiberSpec,fc]
@[simp] theorem baseSpec_x : baseSpec x = -x-y := eval_x _ _
@[simp] theorem baseSpec_y : baseSpec y = x := eval_y _ _

theorem spec_equivariant (q : L) (p : F) :
    fiberSpec (action q p) = ⁅baseSpec q,fiberSpec p⁆ := by
  apply free_action_inner
  intro i j
  cases i <;> fin_cases j <;>
    simp [action, eval, baseSpec, fiberSpec, FreeDerivations.pair,
      x,y,sub_lie,neg_lie,lie_sub,lie_neg]

def specialize : M →ₗ⁅ℚ⁆ L := InnerSemiDirect.lift action fiberSpec baseSpec spec_equivariant

@[simp] theorem specialize_a : specialize a = x := by simp [specialize,a, InnerSemiDirect.lift]
@[simp] theorem specialize_b : specialize b = y := by simp [specialize,b, InnerSemiDirect.lift]
@[simp] theorem specialize_c : specialize c = -x-y := by simp [specialize,c, InnerSemiDirect.lift]
@[simp] theorem specialize_u : specialize u = -x-y := by simp [specialize,u, InnerSemiDirect.lift]
@[simp] theorem specialize_v : specialize v = x := by simp [specialize,v, InnerSemiDirect.lift]

@[simp] theorem eval_right (d e : M) (p : L) :
    (eval d e p).right = eval d.right e.right p :=
  map_eval (SemiDirectSum.projr action) d e p

end SpecialFiber

namespace Differentiation
open FreeDerivations

variable {M N : Type} [LieRing M] [LieAlgebra ℚ M] [LieRing N] [LieAlgebra ℚ N]

@[simp] theorem Jet.base_neg (p : Jet ℚ M) : (-p).base = -p.base := rfl
@[simp] theorem Jet.velocity_neg (p : Jet ℚ M) : (-p).velocity = -p.velocity := rfl
@[simp] theorem Jet.base_sub (p q : Jet ℚ M) : (p-q).base = p.base-q.base := rfl
@[simp] theorem Jet.velocity_sub (p q : Jet ℚ M) : (p-q).velocity = p.velocity-q.velocity := rfl

@[simp] theorem Jet.mk_add (a b da db : M) :
    (Jet.mk a da : Jet ℚ M) + Jet.mk b db = Jet.mk (a+b) (da+db) := rfl
@[simp] theorem Jet.mk_neg (a da : M) :
    -(Jet.mk a da : Jet ℚ M) = Jet.mk (-a) (-da) := rfl
@[simp] theorem Jet.mk_sub (a b da db : M) :
    (Jet.mk a da : Jet ℚ M) - Jet.mk b db = Jet.mk (a-b) (da-db) := rfl

@[simp] theorem eval_base (a b : Jet ℚ M) (p : L) :
    (eval a b p).base = eval a.base b.base p := map_eval Jet.baseHom a b p

def adPower (a : M) : ℕ → M → M
  | 0, t => t
  | n+1, t => ⁅a,adPower a n t⁆

omit [LieAlgebra ℚ M] in
@[simp] theorem adPower_zero (a t : M) : adPower a 0 t = t := rfl
omit [LieAlgebra ℚ M] in
@[simp] theorem adPower_succ (a t : M) (n : ℕ) : adPower a (n+1) t = ⁅a,adPower a n t⁆ := rfl
@[simp] theorem adPower_smul (a t : M) (n : ℕ) (r : ℚ) :
    adPower a n (r • t) = r • adPower a n t := by
  induction n <;> simp_all
omit [LieAlgebra ℚ M] in
@[simp] theorem adPower_zero_right (a : M) (n : ℕ) : adPower a n 0 = 0 := by
  induction n <;> simp_all
omit [LieAlgebra ℚ M] in
@[simp] theorem adPower_self (a : M) {n : ℕ} (hn : 0<n) : adPower a n a = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => simp
    | succ n ih => simp_all
omit [LieAlgebra ℚ M] in
@[simp] theorem adPower_zero_left (t : M) {n : ℕ} (hn : 0<n) : adPower (0:M) n t = 0 := by
  cases n <;> simp_all

def slope (p : L) (a b da db : M) : M :=
  (eval (Jet.mk a da : Jet ℚ M) (Jet.mk b db) p).velocity

@[simp] theorem slope_x (a b da db : M) : slope x a b da db = da := by simp [slope]
@[simp] theorem slope_y (a b da db : M) : slope y a b da db = db := by simp [slope]
@[simp] theorem slope_zero (a b da db : M) : slope 0 a b da db = 0 := by simp [slope]
@[simp] theorem slope_add (p q : L) (a b da db : M) :
    slope (p+q) a b da db = slope p a b da db + slope q a b da db := by simp [slope]
@[simp] theorem slope_smul (r : ℚ) (p : L) (a b da db : M) :
    slope (r • p) a b da db = r • slope p a b da db := by simp [slope]
@[simp] theorem slope_lie (p q : L) (a b da db : M) :
    slope ⁅p,q⁆ a b da db = ⁅slope p a b da db,eval a b q⁆ +
      ⁅eval a b p,slope q a b da db⁆ := by simp [slope,LieHom.map_lie]

@[simp] theorem slope_zero_direction (p : L) (a b : M) : slope p a b 0 0 = 0 := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [slope,eval]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq => simp [hp,hq]

 def fiberEval (a b c : M) : SpecialFiber.F →ₗ⁅ℚ⁆ M :=
  FreeLieAlgebra.lift ℚ (fun i => if i=0 then a else if i=1 then b else c)
@[simp] theorem fiberEval_fa (a b c : M) : fiberEval a b c SpecialFiber.fa = a := by
  simp [fiberEval,SpecialFiber.fa]
@[simp] theorem fiberEval_fb (a b c : M) : fiberEval a b c SpecialFiber.fb = b := by
  simp [fiberEval,SpecialFiber.fb]
@[simp] theorem fiberEval_fc (a b c : M) : fiberEval a b c SpecialFiber.fc = c := by
  simp [fiberEval,SpecialFiber.fc]

@[simp] theorem fiberEval_base (a b c : Jet ℚ M) (z : SpecialFiber.F) :
    (fiberEval a b c z).base = fiberEval a.base b.base c.base z := by
  have h : Jet.baseHom.comp (fiberEval a b c) = fiberEval a.base b.base c.base := by
    apply FreeLieAlgebra.hom_ext
    intro i
    fin_cases i <;> simp [fiberEval,Jet.baseHom] <;> rfl
  exact LieHom.congr_fun h z

@[simp] theorem adPower_base (a t : Jet ℚ M) (n : ℕ) :
    (adPower a n t).base = adPower a.base n t.base := by
  induction n <;> simp_all

end Differentiation

namespace Elimination
open LieAlgebra
variable {R α : Type*} [CommRing R]
attribute [local instance] LieRing.ofAssociativeRing
abbrev F (R α : Type*) [CommRing R] := FreeLieAlgebra R (ℕ × α)
abbrev G (R α : Type*) [CommRing R] := FreeLieAlgebra R (Option α)
def X : G R α := FreeLieAlgebra.of R none
def Y (a : α) : G R α := FreeLieAlgebra.of R (some a)
def E (n : ℕ) (a : α) : F R α := FreeLieAlgebra.of R (n,a)
def shift : LieDerivation R (F R α) (F R α) :=
  FreeDerivations.extend (fun (i,a) => E (i+1) a)
@[simp] theorem shift_E (n : ℕ) (a : α) : shift (E n a : F R α) = E (n+1) a := by
  simp [shift,E]
def action : R →ₗ⁅R⁆ LieDerivation R (F R α) (F R α) where
  toFun r := r • shift
  map_add' r s := add_smul r s shift
  map_smul' r s := mul_smul r s shift
  map_lie' {r s} := by simp [Ring.lie_def,mul_comm,smul_lie,lie_smul]
abbrev M (R α : Type*) [CommRing R] := SemiDirectSum (F R α) R action

def expand : G R α →ₗ⁅R⁆ M R α :=
  FreeLieAlgebra.lift R (fun a => match a with
    | none => SemiDirectSum.inr action 1
    | some a => SemiDirectSum.inl action (E 0 a))
@[simp] theorem expand_X : expand (X : G R α) = SemiDirectSum.inr action 1 := by
  simp [expand,X]
@[simp] theorem expand_Y (a : α) : expand (Y a : G R α) = SemiDirectSum.inl action (E 0 a) := by
  simp [expand,Y]

def adWord (n : ℕ) (a : α) : G R α :=
  (LieAlgebra.ad R (G R α) X)^[n] (Y a)
@[simp] theorem adWord_zero (a : α) : adWord 0 a = (Y a : G R α) := rfl
@[simp] theorem adWord_succ (n : ℕ) (a : α) :
    (adWord (n+1) a : G R α) = ⁅(X : G R α),adWord n a⁆ := by
  exact Function.iterate_succ_apply' _ n _
def collapseFiber : F R α →ₗ⁅R⁆ G R α := FreeLieAlgebra.lift R (fun (n,a) => adWord n a)
@[simp] theorem collapseFiber_E (n : ℕ) (a : α) :
    collapseFiber (E n a : F R α) = adWord n a := by simp [collapseFiber,E]

theorem collapse_shift (p : F R α) : collapseFiber (shift p) = ⁅(X : G R α),collapseFiber p⁆ := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => cases a; simp [shift,collapseFiber,E,adWord_succ]
  | ha p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hl p q hp hq =>
    simp only [LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,hp,hq]
    simpa only [add_comm] using (leibniz_lie (X : G R α) (collapseFiber p) (collapseFiber q)).symm

def scalarX : R →ₗ⁅R⁆ G R α where
  toFun r := r • X
  map_add' r s := add_smul r s X
  map_smul' r s := mul_smul r s X
  map_lie' {r s} := by simp [Ring.lie_def,mul_comm,smul_lie,lie_smul]

def collapse : M R α →ₗ⁅R⁆ G R α :=
  InnerSemiDirect.lift action collapseFiber scalarX (by
    intro r p
    change collapseFiber (r • shift p) = ⁅r • X,collapseFiber p⁆
    rw [map_smul,collapse_shift,smul_lie])

@[simp] theorem collapse_inl (p : F R α) :
    collapse (SemiDirectSum.inl action p) = collapseFiber p := by simp [collapse,InnerSemiDirect.lift]
@[simp] theorem collapse_inr (r : R) :
    collapse (SemiDirectSum.inr action r : M R α) = r • X := by simp [collapse,InnerSemiDirect.lift,scalarX]

end Elimination

namespace AssociativeElimination
open LieAlgebra
variable {R α β : Type*} [CommRing R]
attribute [local instance] LieRing.ofAssociativeRing
abbrev A (R α : Type*) [CommRing R] := MonoidAlgebra R (FreeMonoid α)
def atom (a : α) : A R α := MonoidAlgebra.single (FreeMonoid.of a) 1

def lift {B : Type*} [Ring B] [Algebra R B] (f : α → B) : A R α →ₐ[R] B :=
  MonoidAlgebra.lift R B (FreeMonoid α) (FreeMonoid.lift f)
@[simp] theorem lift_atom {B : Type*} [Ring B] [Algebra R B] (f : α → B) (a : α) :
    lift (R := R) f (atom a) = f a := by simp [lift,atom]

@[ext] theorem hom_ext {B : Type*} [Semiring B] [Algebra R B] {f g : A R α →ₐ[R] B}
    (h : ∀ a, f (atom a) = g (atom a)) : f=g := by
  apply (MonoidAlgebra.lift R B (FreeMonoid α)).symm.injective
  apply FreeMonoid.hom_eq
  intro a
  exact h a

def embed : FreeLieAlgebra R α →ₗ⁅R⁆ A R α := FreeLieAlgebra.lift R atom
@[simp] theorem embed_of (a : α) : embed (FreeLieAlgebra.of R a) = atom a := by simp [embed]

def dualLift (f : α → A R α) : A R α →ₐ[R] DualNumber (A R α) :=
  lift (fun a => TrivSqZeroExt.inl (atom a) + TrivSqZeroExt.inr (f a))
@[simp] theorem dualLift_base (f : α → A R α) (p : A R α) :
    (dualLift f p).fst = p := by
  have h : (TrivSqZeroExt.fstHom R (A R α) (A R α)).comp (dualLift f) = AlgHom.id R (A R α) := by
    apply hom_ext
    intro a
    simp [dualLift]
  exact AlgHom.congr_fun h p

def deriv (f : α → A R α) : A R α →ₗ[R] A R α :=
  ((TrivSqZeroExt.sndHom (A R α) (A R α)).restrictScalars R).comp (dualLift f).toLinearMap
@[simp] theorem deriv_atom (f : α → A R α) (a : α) : deriv f (atom a) = f a := by
  simp [deriv,dualLift]
@[simp] theorem deriv_one (f : α → A R α) : deriv f 1 = 0 := by simp [deriv]
theorem deriv_mul (f : α → A R α) (p q : A R α) :
    deriv f (p*q) = deriv f p*q + p*deriv f q := by
  change (dualLift f (p*q)).snd = _
  rw [map_mul,DualNumber.snd_mul,dualLift_base,dualLift_base]
  exact add_comm _ _
theorem deriv_lie (f : α → A R α) (p q : A R α) :
    deriv f ⁅p,q⁆ = ⁅deriv f p,q⁆ + ⁅p,deriv f q⁆ := by
  simp only [Ring.lie_def,map_sub,deriv_mul]
  abel

def shift : A R (ℕ×α) →ₗ[R] A R (ℕ×α) := deriv (fun (i,a) => atom (i+1,a))
@[simp] theorem shift_atom (i : ℕ) (a : α) : shift (atom (i,a) : A R (ℕ×α)) = atom (i+1,a) := by
  simp [shift]
@[simp] theorem shift_one : shift (1 : A R (ℕ×α)) = 0 := deriv_one _
theorem shift_mul (p q : A R (ℕ×α)) : shift (p*q) = shift p*q + p*shift q := deriv_mul _ _ _

theorem embed_shift (p : Elimination.F R α) : embed (Elimination.shift p) = shift (embed p) := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => cases a; simp [Elimination.shift,Elimination.E]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq =>
    simp only [LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,hp,hq]
    simpa only [shift,add_comm] using (deriv_lie (fun (i,a) => (atom (i+1,a) : A R (ℕ×α))) (embed p) (embed q)).symm

def leftMul : A R α →ₐ[R] Module.End R (A R α) := Algebra.lsmul R R (A R α)
@[simp] theorem leftMul_apply (p q : A R α) : leftMul p q = p*q := rfl
@[simp] theorem comm_shift_left (p : A R (ℕ×α)) :
    ⁅(shift : Module.End R (A R (ℕ×α))),leftMul p⁆ = leftMul (shift p) := by
  apply LinearMap.ext
  intro q
  change shift (p*q)-p*shift q = shift p*q
  rw [shift_mul,add_sub_cancel_right]

def scalarShift : R →ₗ⁅R⁆ Module.End R (A R (ℕ×α)) where
  toFun r := r • shift
  map_add' r s := add_smul r s shift
  map_smul' r s := mul_smul r s shift
  map_lie' {r s} := by simp [Ring.lie_def,smul_smul,mul_comm]

def representation : Elimination.M R α →ₗ⁅R⁆ Module.End R (A R (ℕ×α)) :=
  InnerSemiDirect.lift Elimination.action (leftMul.toLieHom.comp embed) scalarShift (by
    intro r p
    change leftMul (embed (r • Elimination.shift p)) = ⁅r • (shift : Module.End R (A R (ℕ×α))),leftMul (embed p)⁆
    rw [map_smul,map_smul,embed_shift]
    apply LinearMap.ext
    intro q
    change r • (shift (embed p)*q) = r • shift (embed p*q) - embed p*(r • shift q)
    rw [shift_mul,smul_add,mul_smul_comm,add_sub_cancel_right])

@[simp] theorem representation_inl (p : Elimination.F R α) :
    representation (SemiDirectSum.inl Elimination.action p) = leftMul (embed p) := by simp [representation,InnerSemiDirect.lift]
@[simp] theorem representation_inr (r : R) :
    representation (SemiDirectSum.inr Elimination.action r : Elimination.M R α) = r • shift := by
  simp [representation,InnerSemiDirect.lift,scalarShift]

end AssociativeElimination

namespace IntegralWords
open Classical
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {α β : Type*}
abbrev AQ (α : Type*) := A ℚ α

def word (w : List α) : AQ α := MonoidAlgebra.single (FreeMonoid.ofList w) 1
@[simp] theorem word_nil : word ([] : List α) = 1 := rfl
@[simp] theorem word_singleton (a : α) : word [a] = atom a := rfl

def rename (f : α → β) : AQ α →ₐ[ℚ] AQ β := lift (fun a => atom (f a))
@[simp] theorem rename_atom (f : α → β) (a : α) : rename f (atom a) = atom (f a) := by
  simp [rename]

end IntegralWords

namespace UniversalEmbedding
open Classical LieAlgebra AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α β : Type*} [CommRing R]
abbrev FL (R α : Type*) [CommRing R] := FreeLieAlgebra R α

inductive Tree (α : Type*)
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

def Tree.leaves : Tree α → List α
  | .leaf a => [a]
  | .node t u => t.leaves ++ u.leaves

def Tree.eval : Tree α → FL R α
  | .leaf a => FreeLieAlgebra.of R a
  | .node t u => ⁅t.eval,u.eval⁆

def Tree.map (f : α → β) : Tree α → Tree β
  | .leaf a => .leaf (f a)
  | .node t u => .node (t.map f) (u.map f)

@[simp] theorem Tree.leaves_map (f : α → β) (t : Tree α) :
    (t.map f).leaves = t.leaves.map f := by
  induction t <;> simp_all [Tree.map,Tree.leaves]

def rename (f : α → β) : FL R α →ₗ⁅R⁆ FL R β :=
  FreeLieAlgebra.lift R (fun a => FreeLieAlgebra.of R (f a))
@[simp] theorem rename_of (f : α → β) (a : α) :
    rename f (FreeLieAlgebra.of R a) = FreeLieAlgebra.of R (f a) := by simp [rename]
@[simp] theorem rename_eval (f : α → β) (t : Tree α) :
    rename f (t.eval : FL R α) = (t.map f).eval := by
  induction t <;> simp_all [Tree.eval,Tree.map,LieHom.map_lie]

def kill (a : α) : FL R α →ₗ⁅R⁆ FL R α :=
  FreeLieAlgebra.lift R (fun b => if b=a then 0 else FreeLieAlgebra.of R b)
@[simp] theorem kill_of (a b : α) : kill a (FreeLieAlgebra.of R b) =
    if b=a then 0 else FreeLieAlgebra.of R b := by simp [kill]

def fiber : Elimination.G R α →ₗ[R] Elimination.F R α :=
  { toFun := fun p => (Elimination.expand p).left
    map_add' := by intro p q; simp
    map_smul' := by intro r p; simp }

@[simp] theorem fiber_X : fiber (Elimination.X : Elimination.G R α) = 0 := by
  simp [fiber]
@[simp] theorem fiber_Y (a : α) : fiber (Elimination.Y a : Elimination.G R α) = Elimination.E 0 a := by
  simp [fiber]

end UniversalEmbedding

namespace QuadraticAlphabet
open AssociativeElimination LieAlgebra
attribute [local instance] LieRing.ofAssociativeRing
abbrev F := ZMod 2
inductive Letter | a | c | b deriving DecidableEq
instance (α : Type*) : CharP (A F α) 2 :=
  charP_of_injective_ringHom (algebraMap F (A F α)).injective 2
abbrev S := A F Letter
abbrev T := A F (Option Unit)
def a : S := atom Letter.a
def c : S := atom Letter.c
def b : S := atom Letter.b
def x : T := atom none
def y : T := atom (some ())

def delta : S →ₗ[F] S := deriv (fun | .a => 0 | .c => ⁅a,b⁆ | .b => c)
@[simp] theorem delta_a : delta a=0 := by simp [delta,a]
@[simp] theorem delta_b : delta b=c := by simp [delta,b]
@[simp] theorem delta_c : delta c=⁅a,b⁆ := by simp [delta,c]
@[simp] theorem delta_one : delta 1=0 := deriv_one _

theorem algebra_induction {R α : Type*} [CommRing R] {P : A R α → Prop}
    (p : A R α) (h1 : P 1) (ha : ∀ a, P (atom a))
    (hadd : ∀ p q, P p → P q → P (p+q))
    (hs : ∀ (r : R) p, P p → P (r • p))
    (hm : ∀ p q, P p → P q → P (p*q)) : P p := by
  apply MonoidAlgebra.induction_on p ?_ hadd hs
  intro w
  change P (MonoidAlgebra.single w 1)
  have hh : ∀ v : List α, P (MonoidAlgebra.single (FreeMonoid.ofList v) 1) := by
    intro v
    induction v with
    | nil => exact h1
    | cons a v ih =>
      convert hm (atom a) (MonoidAlgebra.single (FreeMonoid.ofList v) 1) (ha a) ih using 1
      simp only [atom,MonoidAlgebra.single_mul_single,one_mul,FreeMonoid.ofList_cons]
  simpa using hh w.toList

def left : S →ₐ[F] Module.End F (S×S) where
  toFun p :=
    { toFun := fun z => (p*z.1,p*z.2)
      map_add' := by intro z w; ext <;> simp [mul_add]
      map_smul' := by intro r z; ext <;> simp }
  map_one' := by ext z <;> simp
  map_mul' := by intro p q; ext z <;> simp [mul_assoc]
  map_zero' := by ext z <;> simp
  map_add' := by intro p q; ext z <;> simp [add_mul]
  commutes' := by intro r; ext z <;> simp [Algebra.algebraMap_eq_smul_one]

@[simp] theorem left_apply (p : S) (z : S×S) : left p z=(p*z.1,p*z.2) := rfl

def root : Module.End F (S×S) where
  toFun z := (delta z.1+z.2*a,z.1+delta z.2)
  map_add' := by intro z w; apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,map_add,add_mul] <;> abel
  map_smul' := by intro r z; ext <;> simp [smul_add]
@[simp] theorem root_apply (z : S×S) : root z=(delta z.1+z.2*a,z.1+delta z.2) := rfl

def substitution : S →ₐ[F] T := lift (fun | .a => x*x | .c => ⁅x,y⁆ | .b => y)
@[simp] theorem substitution_a : substitution a=x*x := by simp [substitution,a]
@[simp] theorem substitution_c : substitution c=⁅x,y⁆ := by simp [substitution,c]
@[simp] theorem substitution_b : substitution b=y := by simp [substitution,b]

def representation : T →ₐ[F] Module.End F (S×S) :=
  lift (fun | none => root | some _ => left b)
@[simp] theorem representation_x : representation x=root := by simp [representation,x]
@[simp] theorem representation_y : representation y=left b := by simp [representation,y]

abbrev LABC := FreeLieAlgebra F Letter
def la : LABC := FreeLieAlgebra.of F Letter.a
def lc : LABC := FreeLieAlgebra.of F Letter.c
def lb : LABC := FreeLieAlgebra.of F Letter.b
def under : LABC →ₗ⁅F⁆ T := substitution.toLieHom.comp embed
@[simp] theorem under_a : under la=x*x := by simp [under,la,substitution]
@[simp] theorem under_c : under lc=⁅x,y⁆ := by simp [under,lc,substitution]
@[simp] theorem under_b : under lb=y := by simp [under,lb,substitution]

def lieDelta : LieDerivation F LABC LABC :=
  FreeDerivations.extend (fun | .a => 0 | .c => ⁅la,lb⁆ | .b => lc)
@[simp] theorem lieDelta_a : lieDelta la=0 := by simp [lieDelta,la]
@[simp] theorem lieDelta_c : lieDelta lc=⁅la,lb⁆ := by simp [lieDelta,lc]
@[simp] theorem lieDelta_b : lieDelta lb=lc := by simp [lieDelta,lb]

def iter (i : ℕ) : LABC := lieDelta^[i] lb
@[simp] theorem iter_zero : iter 0=lb := rfl
@[simp] theorem iter_succ (i : ℕ) : iter (i+1)=lieDelta (iter i) :=
  Function.iterate_succ_apply' _ _ _

end QuadraticAlphabet

namespace AssociativeDerivations
open LieAlgebra AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]
local notation "FL" => FreeLieAlgebra R α

def extend (d : LieDerivation R FL FL) : Module.End R (A R α) :=
  deriv (fun a => embed (d (FreeLieAlgebra.of R a)))
@[simp] theorem extend_atom (d : LieDerivation R FL FL) (a : α) :
    extend d (atom a) = embed (d (FreeLieAlgebra.of R a)) := by simp [extend]
@[simp] theorem extend_one (d : LieDerivation R FL FL) :
    extend d 1=0 := deriv_one _
theorem extend_mul (d : LieDerivation R FL FL) (p q : A R α) :
    extend d (p*q)=extend d p*q+p*extend d q := deriv_mul _ p q

theorem extend_embed (d : LieDerivation R FL FL) (p : FL) :
    extend d (embed p)=embed (d p) := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq =>
    simp only [LieHom.map_lie,extend,deriv_lie] at *
    rw [hp,hq,LieDerivation.apply_lie_eq_add,map_add,LieHom.map_lie,LieHom.map_lie]
    exact add_comm _ _

theorem linear_ext {f g : Module.End R (A R α)}
    (h1 : f 1=g 1) (ha : ∀ a, f (atom a)=g (atom a))
    (hf : ∀ p q, f (p*q)=f p*q+p*f q)
    (hg : ∀ p q, g (p*q)=g p*q+p*g q) : f=g := by
  apply LinearMap.ext
  intro p
  induction p using QuadraticAlphabet.algebra_induction with
  | h1 => exact h1
  | ha a => exact ha a
  | hadd p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hm p q hp hq => rw [hf,hg,hp,hq]

theorem comm_mul (f g : Module.End R (A R α))
    (hf : ∀ p q, f (p*q)=f p*q+p*f q)
    (hg : ∀ p q, g (p*q)=g p*q+p*g q) (p q : A R α) :
    ⁅f,g⁆ (p*q)=⁅f,g⁆ p*q+p*⁅f,g⁆ q := by
  change f (g (p*q))-g (f (p*q))=(f (g p)-g (f p))*q+p*(f (g q)-g (f q))
  rw [hf,hg,map_add,map_add,hf,hf,hg,hg]
  noncomm_ring

def hom : LieDerivation R FL FL →ₗ⁅R⁆ Module.End R (A R α) where
  toFun := extend
  map_add' d e := by
    apply linear_ext
    · simp
    · intro a; simp [LieDerivation.add_apply]
    · exact extend_mul _
    · intro p q; simp only [LinearMap.add_apply,extend_mul]; noncomm_ring
  map_smul' r d := by
    apply linear_ext
    · simp
    · intro a; simp
    · exact extend_mul _
    · intro p q; simp [extend_mul,smul_add]
  map_lie' {d e} := by
    apply linear_ext
    · change extend ⁅d,e⁆ 1=extend d (extend e 1)-extend e (extend d 1)
      simp
    · intro a
      change extend ⁅d,e⁆ (atom a)=extend d (extend e (atom a))-extend e (extend d (atom a))
      simp [extend_embed]
    · exact extend_mul _
    · exact comm_mul _ _ (extend_mul d) (extend_mul e)

@[simp] theorem hom_apply (d : LieDerivation R FL FL) (p : A R α) :
    hom d p=extend d p := rfl

end AssociativeDerivations

namespace EnvelopingTools
open LieAlgebra
attribute [local instance] LieRing.ofAssociativeRing
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

end EnvelopingTools

namespace FiberPBW
open AssociativeElimination LieAlgebra
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {R α G : Type*} [CommRing R] [LieRing G] [LieAlgebra R G]
  (act : G →ₗ⁅R⁆ LieDerivation R (FreeLieAlgebra R α) (FreeLieAlgebra R α))
local notation "F" => FreeLieAlgebra R α
local notation "B" => UniversalEnvelopingAlgebra R G
abbrev M := SemiDirectSum (R:=R) F G act
local notation "V" => A R α ⊗[R] B

def onLeft (f : Module.End R (A R α)) : Module.End R V :=
  f.rTensor B

def onRight (f : Module.End R B) : Module.End R V :=
  f.lTensor (A R α)

@[simp] theorem onLeft_tmul (f : Module.End R (A R α)) (p : A R α) (b : B) :
    onLeft f (p⊗ₜ b)=f p⊗ₜ b := rfl
@[simp] theorem onRight_tmul (f : Module.End R B) (p : A R α) (b : B) :
    onRight f (p⊗ₜ b)=p⊗ₜ f b := rfl

theorem commute_tensor (f : Module.End R (A R α)) (g : Module.End R B) :
    ⁅onLeft (G:=G) f,onRight (α:=α) g⁆=0 := by
  apply TensorProduct.ext'
  intro p b
  simp

def fiber : F →ₗ⁅R⁆ Module.End R V :=
  (Module.End.rTensorAlgHom R (A R α) B).toLieHom.comp (leftMul.toLieHom.comp embed)

def action : G →ₗ⁅R⁆ Module.End R V :=
  (Module.End.rTensorAlgHom R (A R α) B).toLieHom.comp (AssociativeDerivations.hom.comp act)

def baseLeft : B →ₐ[R] Module.End R B := Algebra.lsmul R R B

def constant : G →ₗ⁅R⁆ Module.End R V :=
  (Module.End.lTensorAlgHom R B (A R α)).toLieHom.comp
    (baseLeft.toLieHom.comp (UniversalEnvelopingAlgebra.ι R))

def base : G →ₗ⁅R⁆ Module.End R V where
  toFun g := action act g+constant g
  map_add' g h := by simp only [map_add]; abel
  map_smul' r g := by simp only [map_smul,smul_add,RingHom.id_apply]
  map_lie' {g h} := by
    have h1 : ⁅action act g,constant h⁆=0 := commute_tensor _ _
    have h2 : ⁅action act h,constant g⁆=0 := commute_tensor _ _
    change action act ⁅g,h⁆+constant ⁅g,h⁆= _
    rw [LieHom.map_lie,LieHom.map_lie]
    change (action act g*action act h-action act h*action act g)+
      (constant g*constant h-constant h*constant g)=
      (action act g+constant g)*(action act h+constant h)-
      (action act h+constant h)*(action act g+constant g)
    change action act g*constant h-constant h*action act g=0 at h1
    change action act h*constant g-constant g*action act h=0 at h2
    have h1' : action act g*constant h=constant h*action act g := by
      exact (sub_eq_zero (a:=action act g*constant h) (b:=constant h*action act g)).mp h1
    have h2' : action act h*constant g=constant g*action act h := by
      exact (sub_eq_zero (a:=action act h*constant g) (b:=constant g*action act h)).mp h2
    simp only [add_mul,mul_add]
    rw [h1',h2']
    abel

@[simp] theorem fiber_tmul (p : F) (q : A R α) (b : B) :
    fiber p (q⊗ₜ b)=(embed p*q)⊗ₜ b := rfl
@[simp] theorem base_tmul (g : G) (q : A R α) (b : B) :
    base act g (q⊗ₜ b)=AssociativeDerivations.extend (act g) q⊗ₜ b+
      q⊗ₜ (UniversalEnvelopingAlgebra.ι R g*b) := rfl

def fiberIn : A R α →ₐ[R] UniversalEnvelopingAlgebra R (M act) :=
  lift (fun a => UniversalEnvelopingAlgebra.ι R (SemiDirectSum.inl act (FreeLieAlgebra.of R a)))
def baseIn : B →ₐ[R] UniversalEnvelopingAlgebra R (M act) :=
  UniversalEnvelopingAlgebra.lift R ((UniversalEnvelopingAlgebra.ι R).comp (SemiDirectSum.inr act))

def normal : V →ₗ[R] UniversalEnvelopingAlgebra R (M act) :=
  TensorProduct.lift
    { toFun := fun p =>
        { toFun := fun b => fiberIn act p*baseIn act b
          map_add' := by intro b c; simp [mul_add]
          map_smul' := by intro r b; simp }
      map_add' := by intro p q; ext b; simp [add_mul]
      map_smul' := by intro r p; ext b; simp }
@[simp] theorem normal_tmul (p : A R α) (b : B) :
    normal act (p⊗ₜ b)=fiberIn act p*baseIn act b := rfl

end FiberPBW

namespace GenericBraid
open LieAlgebra FreeDerivations
variable {R α : Type*} [CommRing R]
abbrev Free (R α : Type*) [CommRing R] := FreeLieAlgebra R (α×α)
def gen (i j : α) : Free R α := FreeLieAlgebra.of R (i,j)
def relations : Set (Free R α) := {q |
  (∃ i, q=gen (R:=R) i i) ∨ (∃ i j, q=gen (R:=R) i j-gen (R:=R) j i) ∨
  (∃ i j k l, i≠k ∧ i≠l ∧ j≠k ∧ j≠l ∧ q=⁅gen (R:=R) i j,gen (R:=R) k l⁆) ∨
  (∃ i j k, i≠j ∧ i≠k ∧ j≠k ∧ q=⁅gen (R:=R) i j,gen (R:=R) i k+gen (R:=R) j k⁆)}
def ideal : LieIdeal R (Free R α) := LieSubmodule.lieSpan R _ relations
abbrev T (R α : Type*) [CommRing R] := Free R α ⧸ (ideal (R:=R) (α:=α))
def t (i j : α) : T R α := (ideal (R:=R) (α:=α)).mkQ (gen i j)

theorem relation_zero {q : Free R α} (h : q∈relations) :
    (ideal (R:=R) (α:=α)).mkQ q=0 := by
  exact (LieSubmodule.Quotient.mk_eq_zero _).mpr (LieSubmodule.subset_lieSpan h)
@[simp] theorem t_self (i : α) : t (R:=R) i i=0 :=
  relation_zero (Or.inl ⟨i,rfl⟩)
theorem t_comm (i j : α) : t (R:=R) i j=t j i := by
  have h := relation_zero (R:=R) (Or.inr (Or.inl ⟨i,j,rfl⟩))
  simpa only [map_sub,sub_eq_zero,t] using h
theorem t_disjoint (i j k l : α) (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅t (R:=R) i j,t (R:=R) k l⁆=0 := by
  change (ideal (R:=R) (α:=α)).mkQ (⁅gen i j,gen k l⁆)=0
  exact relation_zero (Or.inr (Or.inr (Or.inl ⟨i,j,k,l,hik,hil,hjk,hjl,rfl⟩)))
theorem t_three (i j k : α) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ⁅t (R:=R) i j,t (R:=R) i k+t (R:=R) j k⁆=0 := by
  change (ideal (R:=R) (α:=α)).mkQ (⁅gen i j,gen i k+gen j k⁆)=0
  exact relation_zero (Or.inr (Or.inr (Or.inr ⟨i,j,k,hij,hik,hjk,rfl⟩)))

variable {E : Type*} [LieRing E] [LieAlgebra R E]
def lift (f : α → α → E) (hz : ∀ i, f i i=0) (hs : ∀ i j,f i j=f j i)
    (hd : ∀ i j k l,i≠k → i≠l → j≠k → j≠l → ⁅f i j,f k l⁆=0)
    (ht : ∀ i j k,i≠j → i≠k → j≠k → ⁅f i j,f i k+f j k⁆=0) : T R α →ₗ⁅R⁆ E := by
  let p := FreeLieAlgebra.lift R (fun ij : α×α => f ij.1 ij.2)
  have hker : ideal (R:=R) (α:=α) ≤ p.ker := by
    rw [ideal,LieSubmodule.lieSpan_le]
    intro q hq
    change p q=0
    rcases hq with ⟨i,rfl⟩ | ⟨i,j,rfl⟩ | ⟨i,j,k,l,hik,hil,hjk,hjl,rfl⟩ | ⟨i,j,k,hij,hik,hjk,rfl⟩
    · simpa only [p,gen,FreeLieAlgebra.lift_of_apply] using hz i
    · simpa only [map_sub,p,gen,FreeLieAlgebra.lift_of_apply,sub_eq_zero] using hs i j
    · simpa only [LieHom.map_lie,p,gen,FreeLieAlgebra.lift_of_apply] using hd i j k l hik hil hjk hjl
    · simpa only [LieHom.map_lie,map_add,p,gen,FreeLieAlgebra.lift_of_apply] using ht i j k hij hik hjk
  exact { (ideal (R:=R) (α:=α)).toSubmodule.liftQ p.toLinearMap hker with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact p.map_lie a b }
@[simp] theorem lift_t (f : α → α → E) (hz hs hd ht) (i j : α) :
    lift f hz hs hd ht (t (R:=R) i j)=f i j := by
  change FreeLieAlgebra.lift R (fun ij : α×α => f ij.1 ij.2) (FreeLieAlgebra.of R (i,j))=f i j
  simp only [FreeLieAlgebra.lift_of_apply]

variable [DecidableEq α]
def action : T R α →ₗ⁅R⁆ LieDerivation R (FreeLieAlgebra R α) (FreeLieAlgebra R α) :=
  lift pair pair_self pair_comm pair_disjoint pair_three
local notation "F" => FreeLieAlgebra R α
local notation "SD" => SemiDirectSum F (T R α) action
@[simp] theorem action_t (i j : α) : action (t (R:=R) i j)=pair i j := by simp [action]
def fiber (i : α) : SD := SemiDirectSum.inl action (FreeLieAlgebra.of R i)
def base (i j : α) : SD := SemiDirectSum.inr action (t i j)
def chord : Option α → Option α → SD
  | none, none => 0
  | none, some j => fiber j
  | some i, none => fiber i
  | some i, some j => base i j
@[simp] theorem chord_nn : chord (R:=R) (α:=α) none none=0 := rfl
@[simp] theorem chord_ns (i : α) : chord (R:=R) none (some i)=fiber i := rfl
@[simp] theorem chord_sn (i : α) : chord (R:=R) (some i) none=fiber i := rfl
@[simp] theorem chord_ss (i j : α) : chord (R:=R) (some i) (some j)=base i j := rfl
@[simp] theorem chord_self (i : Option α) : chord (R:=R) i i=0 := by
  cases i <;> simp [base]
theorem chord_comm (i j : Option α) : chord (R:=R) i j=chord j i := by
  cases i <;> cases j <;> simp [base,t_comm]
theorem base_fiber (i j k : α) : ⁅base (R:=R) i j,fiber k⁆=
    SemiDirectSum.inl action (pair (R:=R) i j (FreeLieAlgebra.of R k)) := by
  simp [base,fiber]
theorem fiber_base (i j k : α) : ⁅fiber (R:=R) k,base i j⁆=
    -SemiDirectSum.inl action (pair (R:=R) i j (FreeLieAlgebra.of R k)) := by
  rw [← lie_skew,base_fiber]
theorem chord_disjoint (i j k l : Option α)
    (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅chord (R:=R) i j,chord (R:=R) k l⁆=0 := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    simp_all [base,fiber,t_disjoint]
  all_goals apply pair_of_other <;> intro h <;> subst_vars <;> contradiction
theorem chord_three (i j k : Option α) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ⁅chord (R:=R) i j,chord (R:=R) i k+chord (R:=R) j k⁆=0 := by
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      cases k with
      | none => exact (hik rfl).elim
      | some k =>
        rw [chord_ns,chord_ns,chord_ss,lie_add,fiber_base]
        simp [fiber]
        grind [lie_skew]
  | some i =>
    cases j with
    | none =>
      cases k with
      | none => exact (hjk rfl).elim
      | some k =>
        rw [chord_sn,chord_ss,chord_ns,lie_add,fiber_base]
        simp [fiber]
        grind [lie_skew]
    | some j =>
      cases k with
      | none =>
        rw [chord_ss,chord_sn,chord_sn,lie_add,base_fiber,base_fiber]
        simp only [pair_of_left,pair_of_right,← map_add]
        grind [lie_skew]
      | some k =>
        simp only [chord_ss,base,← map_add,← LieHom.map_lie]
        rw [t_three _ _ _ (fun h => hij (congrArg some h))
          (fun h => hik (congrArg some h)) (fun h => hjk (congrArg some h)),map_zero]
def toSemidirect : T R (Option α) →ₗ⁅R⁆ SD :=
  lift chord chord_self chord_comm chord_disjoint chord_three
@[simp] theorem toSemidirect_t (i j : Option α) : toSemidirect (t (R:=R) i j)=chord i j := by
  simp [toSemidirect]
end GenericBraid

namespace RestrictedAlphabet
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
abbrev F := ZMod 2
inductive Letter (α : Type*) | a | c (i : α) | b (i : α)
variable {α : Type*}
abbrev S (α : Type*) := A F (Letter α)
abbrev T (α : Type*) := A F (Option α)
def a : S α := atom .a
def b (i : α) : S α := atom (.b i)
def c (i : α) : S α := atom (.c i)
def y (i : α) : T α := atom (some i)
def x : T α := atom none
def delta : Module.End F (S α) := deriv (fun (l : Letter α) => match l with | .a => 0 | .c i => ⁅(a : S α),b i⁆ | .b i => c i)
@[simp] theorem delta_a : delta (a : S α)=0 := by simp [delta,a]
@[simp] theorem delta_b (i : α) : delta (b i)=c i := by simp [delta,b]
@[simp] theorem delta_c (i : α) : delta (c i)=⁅(a : S α),b i⁆ := by simp [delta,c]
@[simp] theorem delta_one : delta (1 : S α)=0 := deriv_one _

def left : S α →ₐ[F] Module.End F (S α×S α) where
  toFun p :=
    { toFun := fun z => (p*z.1,p*z.2)
      map_add' := by intro z w; ext <;> simp [mul_add]
      map_smul' := by intro r z; ext <;> simp }
  map_one' := by ext z <;> simp
  map_mul' := by intro p q; ext z <;> simp [mul_assoc]
  map_zero' := by ext z <;> simp
  map_add' := by intro p q; ext z <;> simp [add_mul]
  commutes' := by intro r; ext z <;> simp [Algebra.algebraMap_eq_smul_one]
@[simp] theorem left_apply (p : S α) (z : S α×S α) : left p z=(p*z.1,p*z.2) := rfl

def root : Module.End F (S α×S α) where
  toFun z := (delta z.1+z.2*a,z.1+delta z.2)
  map_add' := by intro z w; apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,map_add,add_mul] <;> abel
  map_smul' := by intro r z; ext <;> simp [smul_add]
@[simp] theorem root_apply (z : S α×S α) : root z=(delta z.1+z.2*a,z.1+delta z.2) := rfl

def substitution : S α →ₐ[F] T α := lift (fun | .a => x*x | .c i => ⁅(x : T α),y i⁆ | .b i => y i)
@[simp] theorem substitution_a : substitution (a : S α)=x*x := by simp [substitution,a]
@[simp] theorem substitution_c (i : α) : substitution (c i)=⁅(x : T α),y i⁆ := by simp [substitution,c]
@[simp] theorem substitution_b (i : α) : substitution (b i)=y i := by simp [substitution,b]
def representation : T α →ₐ[F] Module.End F (S α×S α) :=
  lift (fun | none => root | some i => left (b i))
@[simp] theorem representation_x : representation (x : T α)=root := by simp [representation,x]
@[simp] theorem representation_y (i : α) : representation (y i)=left (b i) := by simp [representation,y]
end RestrictedAlphabet

namespace GenericBraid
open LieAlgebra AssociativeElimination
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R] [DecidableEq α]
abbrev Env (R α : Type*) [CommRing R] := UniversalEnvelopingAlgebra R (T R α)

def baseLie : T R α →ₗ⁅R⁆ T R (Option α) :=
  lift (fun i j => t (some i) (some j)) (fun i => t_self (some i))
    (fun i j => t_comm (some i) (some j)) (fun i j k l hik hil hjk hjl =>
      t_disjoint (some i) (some j) (some k) (some l) (fun h => hik (Option.some.inj h))
        (fun h => hil (Option.some.inj h)) (fun h => hjk (Option.some.inj h))
        (fun h => hjl (Option.some.inj h)))
    (fun i j k hij hik hjk => t_three (some i) (some j) (some k) (fun h => hij (Option.some.inj h))
      (fun h => hik (Option.some.inj h)) (fun h => hjk (Option.some.inj h)))
omit [DecidableEq α] in
@[simp] theorem baseLie_t (i j : α) : baseLie (t (R:=R) i j)=t (some i) (some j) := by
  simp [baseLie]

def fiberIn : A R α →ₐ[R] Env R (Option α) :=
  AssociativeElimination.lift (fun i => UniversalEnvelopingAlgebra.ι R (t none (some i)))
def baseIn : Env R α →ₐ[R] Env R (Option α) :=
  UniversalEnvelopingAlgebra.lift R ((UniversalEnvelopingAlgebra.ι R).comp baseLie)

def normal : A R α ⊗[R] Env R α →ₗ[R] Env R (Option α) :=
  TensorProduct.lift
    { toFun := fun p =>
        { toFun := fun b => fiberIn p*baseIn b
          map_add' := by intro b c; simp [mul_add]
          map_smul' := by intro r b; simp }
      map_add' := by intro p q; ext b; simp [add_mul]
      map_smul' := by intro r p; ext b; simp }
omit [DecidableEq α] in
@[simp] theorem normal_tmul (p : A R α) (b : Env R α) :
    normal (p⊗ₜ b)=fiberIn p*baseIn b := rfl

end GenericBraid

namespace RestrictedAlphabet
open LieAlgebra AssociativeElimination
open scoped TensorProduct
variable {α : Type*} [DecidableEq α]
local notation "U" => UniversalEnvelopingAlgebra F (GenericBraid.T F (Option α))

end RestrictedAlphabet

namespace Deletion

section
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {R α : Type*} [CommRing R]
def word (w : List α) : A R α := MonoidAlgebra.single (FreeMonoid.ofList w) 1
@[simp] theorem word_nil : word ([] : List α)=(1 : A R α) := rfl

def raw (ν : α → α → R) (l r : α) : List α → A R α
  | [] => 0
  | a::s => (ν a (s.headD r)-ν l a) • word s+atom a*raw ν a r s

def op (ν : α → α → R) (l r : α) : Module.End R (A R α) :=
  (Finsupp.linearCombination R (fun w : FreeMonoid α => raw ν l r w.toList)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap
@[simp] theorem op_word (ν : α → α → R) (l r : α) (s : List α) :
    op ν l r (word s)=raw ν l r s := by
  change Finsupp.linearCombination R (fun monoidWord : FreeMonoid α => raw ν l r monoidWord.toList) (Finsupp.single (FreeMonoid.ofList s) 1) = _; simp
@[simp] theorem op_one (ν : α → α → R) (l r : α) : op ν l r 1=0 := by
  exact op_word ν l r []
end

open AssociativeElimination
variable {R α : Type*} [CommRing R]
theorem linear_ext {M : Type*} [AddCommGroup M] [Module R M]
    {f g : A R α →ₗ[R] M} (h : ∀ s : List α,f (word s)=g (word s)) : f=g := by
  apply LinearMap.ext
  intro p
  induction p using MonoidAlgebra.induction_on with
  | of w => simpa only [word,FreeMonoid.ofList_toList,MonoidAlgebra.of_apply] using h w.toList
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]

theorem raw_add (ν μ : α → α → R) (l r : α) (s : List α) :
    raw (fun a b => ν a b+μ a b) l r s=raw ν l r s+raw μ l r s := by
  induction s generalizing l with
  | nil => simp [raw]
  | cons a s ih => simp only [raw,ih,mul_add]; module
@[simp] theorem op_add (ν μ : α → α → R) (l r : α) :
    op (fun a b => ν a b+μ a b) l r=op ν l r+op μ l r := by
  apply linear_ext
  intro s
  simp only [LinearMap.add_apply,op_word,raw_add]
@[simp] theorem op_zero (l r : α) : op (fun _ _ => (0 : R)) l r=0 := by
  apply linear_ext
  intro s
  simp only [LinearMap.zero_apply,op_word]
  induction s generalizing l with
  | nil => rfl
  | cons a s ih => simp [raw,ih]

end Deletion

namespace DeletionTable
open Deletion AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
inductive Letter | o | e | p | w deriving DecidableEq
instance : Fintype Letter := ⟨{.o,.e,.p,.w}, by intro x; cases x <;> simp⟩
inductive Hyperplane | a1 | a2 | a3 | p12 | m12 | p13 | m13 | p23 | m23 deriving DecidableEq
instance : Fintype Hyperplane := ⟨{.a1,.a2,.a3,.p12,.m12,.p13,.m13,.p23,.m23}, by intro x; cases x <;> simp⟩
open Letter Hyperplane

end DeletionTable

namespace GenericBraid
open LieAlgebra FreeDerivations
variable {R α : Type*} [CommRing R]

variable [DecidableEq α]
def fiberLie : FreeLieAlgebra R α →ₗ⁅R⁆ T R (Option α) :=
  FreeLieAlgebra.lift R (fun i => t none (some i))
omit [DecidableEq α] in
@[simp] theorem fiberLie_of (i : α) : fiberLie (FreeLieAlgebra.of R i)=t none (some i) := by
  simp [fiberLie]

end GenericBraid

attribute [local instance 2000] FreeLieAlgebra.instLieAlgebra

namespace IntegralBaseChange
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {S α : Type*} [CommRing S]
def words : A ℤ α →+* A S α := MonoidAlgebra.mapRingHom _ (Int.castRingHom S)
@[simp] theorem words_atom (a : α) : words (atom a : A ℤ α)=(atom a : A S α) := by
  simp [words,atom]
@[simp] theorem words_coeff (p : A ℤ α) (w : FreeMonoid α) :
    (words p : A S α).coeff w=(p.coeff w : S) := by simp [words]
def lie : FreeLieAlgebra ℤ α →ₗ⁅ℤ⁆ FreeLieAlgebra S α :=
  FreeLieAlgebra.lift ℤ (FreeLieAlgebra.of S)
@[simp] theorem lie_of (a : α) : lie (FreeLieAlgebra.of ℤ a)=FreeLieAlgebra.of S a := by exact FreeLieAlgebra.lift_of_apply (FreeLieAlgebra.of S) a
end IntegralBaseChange

namespace GenericBraid

section
variable {S α β : Type*} [CommRing S]
def cast : T ℤ α →ₗ⁅ℤ⁆ T S α :=
  lift (t (R:=S)) t_self t_comm t_disjoint t_three
@[simp] theorem cast_t (i j : α) : cast (t (R:=ℤ) i j)=t (R:=S) i j := by simp [cast]
def rename {R : Type*} [CommRing R] (e : α ≃ β) : T R α →ₗ⁅R⁆ T R β :=
  lift (fun i j => t (e i) (e j)) (fun i => t_self (e i)) (fun i j => t_comm (e i) (e j))
    (fun i j k l hik hil hjk hjl => t_disjoint (e i) (e j) (e k) (e l)
      (e.injective.ne hik) (e.injective.ne hil) (e.injective.ne hjk) (e.injective.ne hjl))
    (fun i j k hij hik hjk => t_three (e i) (e j) (e k) (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hjk))
@[simp] theorem rename_t {R : Type*} [CommRing R] (e : α ≃ β) (i j : α) :
    rename e (t (R:=R) i j)=t (e i) (e j) := by simp [rename]
variable [DecidableEq α]
end

variable {α : Type*}

def fromT4 : T4 →ₗ⁅ℚ⁆ T ℚ (Fin 4) :=
  T4Universal.lift (t (R:=ℚ)) t_comm t_self
    (fun i j k l _ hik hil hjk hjl _ => t_disjoint i j k l hik hil hjk hjl) t_three
@[simp] theorem fromT4_t (i j : Fin 4) : fromT4 (DeligneDrinfeld.t i j)=t i j := by
  simp [fromT4]
end GenericBraid

namespace BaseChangeEquations
variable {R : Type*} [CommRing R]
def x : FreeLieAlgebra R Bool := FreeLieAlgebra.of R false
def y : FreeLieAlgebra R Bool := FreeLieAlgebra.of R true
def eval {M : Type*} [LieRing M] [LieAlgebra R M] (a b : M) : FreeLieAlgebra R Bool →ₗ⁅R⁆ M :=
  FreeLieAlgebra.lift R (fun i => if i then b else a)
@[simp] theorem eval_x {M : Type*} [LieRing M] [LieAlgebra R M] (a b : M) : eval (R:=R) a b x=a := by simp [eval,x]
@[simp] theorem eval_y {M : Type*} [LieRing M] [LieAlgebra R M] (a b : M) : eval (R:=R) a b y=b := by simp [eval,y]

variable {S : Type*} [CommRing S]
@[simp] theorem cast_x : IntegralBaseChange.lie (x : FreeLieAlgebra ℤ Bool)=(x : FreeLieAlgebra S Bool) := by simp [x]
@[simp] theorem cast_y : IntegralBaseChange.lie (y : FreeLieAlgebra ℤ Bool)=(y : FreeLieAlgebra S Bool) := by simp [y]
end BaseChangeEquations

namespace PolynomialOrdering
open AssociativeElimination
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {R α β : Type*} [CommRing R]
abbrev V := A R α ⊗[R] A R β
variable (δ : β → α → A R α)
def fiberOp (a : α) : Module.End R (V (R:=R) (α:=α) (β:=β)) :=
  TensorProduct.map (leftMul (atom a)) LinearMap.id
def baseOp (b : β) : Module.End R (V (R:=R) (α:=α) (β:=β)) :=
  TensorProduct.map (deriv (δ b)) LinearMap.id+
    TensorProduct.map LinearMap.id (leftMul (atom b))
def op : Sum α β → Module.End R (V (R:=R) (α:=α) (β:=β)) :=
  Sum.elim fiberOp (baseOp δ)
@[simp] theorem fiberOp_tmul (a : α) (p : A R α) (q : A R β) :
    fiberOp a (p⊗ₜ q)=(atom a*p)⊗ₜ q := rfl
@[simp] theorem baseOp_tmul (b : β) (p : A R α) (q : A R β) :
    baseOp δ b (p⊗ₜ q)=deriv (δ b) p⊗ₜ q+p⊗ₜ (atom b*q) := rfl

def operators : A R (Sum α β) →ₐ[R] Module.End R (V (R:=R) (α:=α) (β:=β)) :=
  lift (op δ)
def normalize : A R (Sum α β) →ₗ[R] V (R:=R) (α:=α) (β:=β) :=
  (LinearMap.applyₗ ((1 : A R α)⊗ₜ (1 : A R β))).comp (operators δ).toLinearMap
@[simp] theorem normalize_one : normalize δ 1=1⊗ₜ 1 := by
  change operators δ 1 (1⊗ₜ 1)=_; simp
@[simp] theorem normalize_atom_mul (s : Sum α β) (p : A R (Sum α β)) :
    normalize δ (atom s*p)=op δ s (normalize δ p) := by
  change operators δ (atom s*p) (1⊗ₜ 1)=_
  rw [map_mul,Module.End.mul_apply]
  simp only [operators,lift_atom]
  rfl

variable {U : Type*} [Ring U] [Algebra R U]
def interpret (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U) : V (R:=R) (α:=α) (β:=β) →ₗ[R] U :=
  TensorProduct.lift
    { toFun := fun p =>
        { toFun := fun q => f p*g q
          map_add' := by intro q r; simp [mul_add]
          map_smul' := by intro c q; simp }
      map_add' := by intro p r; ext q; simp [add_mul]
      map_smul' := by intro c p; ext q; simp }
@[simp] theorem interpret_tmul (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U)
    (p : A R α) (q : A R β) : interpret f g (p⊗ₜ q)=f p*g q := rfl

variable (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U)
variable (hδ : ∀ b a,g (atom b)*f (atom a)-f (atom a)*g (atom b)=f (δ b a))
include hδ

omit hδ
end PolynomialOrdering

namespace WordGrading
open AssociativeElimination
variable {R α : Type*} [CommRing R]
def word (w : FreeMonoid α) : A R α := MonoidAlgebra.single w 1
@[simp] theorem word_one : word (1 : FreeMonoid α)=(1 : A R α) := rfl
@[simp] theorem word_of (a : α) : word (FreeMonoid.of a)=(atom a : A R α) := rfl
@[simp] theorem word_mul (u v : FreeMonoid α) : word (R:=R) (u*v)=word u*word v := by
  simp [word,MonoidAlgebra.single_mul_single]

def project (P : FreeMonoid α → Prop) [DecidablePred P] : A R α →ₗ[R] A R α :=
  (Finsupp.linearCombination R (fun w => if P w then word w else 0)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap
@[simp] theorem project_word (P : FreeMonoid α → Prop) [DecidablePred P] (w : FreeMonoid α) :
    project (R:=R) P (word w)=if P w then word w else 0 := by
  change Finsupp.linearCombination R (fun monoidWord => if P monoidWord then word monoidWord else 0) (Finsupp.single w 1) = _; simp

def degree (wt : α → ℕ) (w : FreeMonoid α) : ℕ := (w.toList.map wt).sum
@[simp] theorem degree_one (wt : α → ℕ) : degree wt 1=0 := rfl
@[simp] theorem degree_of (wt : α → ℕ) (a : α) : degree wt (FreeMonoid.of a)=wt a := by simp [degree]
@[simp] theorem degree_mul (wt : α → ℕ) (u v : FreeMonoid α) : degree wt (u*v)=degree wt u+degree wt v := by
  simp [degree]
end WordGrading

namespace TriangularWords
open AssociativeElimination WordGrading
variable {R α V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
def action (f : α → Module.End R V) : A R α →ₐ[R] Module.End R V := lift f
@[simp] theorem action_atom (f : α → Module.End R V) (a : α) : action f (atom a)=f a := lift_atom f a

def apply (f : α → Module.End R V) (v : V) : A R α →ₗ[R] V :=
  (LinearMap.applyₗ v).comp (action f).toLinearMap
@[simp] theorem apply_word_one (f : α → Module.End R V) (v : V) : apply f v (word 1)=v := by simp [apply]
@[simp] theorem apply_word_cons (f : α → Module.End R V) (v : V) (a : α) (w : FreeMonoid α) :
    apply f v (word (FreeMonoid.of a*w))=f a (apply f v (word w)) := by
  simp [apply,Module.End.mul_apply]

end TriangularWords
namespace WordGrading
open AssociativeElimination
variable {R α : Type*} [CommRing R]
end WordGrading
namespace TensorGrading
open AssociativeElimination WordGrading
open scoped TensorProduct
variable {R α β : Type*} [CommRing R]
abbrev V := A R α ⊗[R] A R β

variable {wa : α → ℕ} {wb : β → ℕ} {δ : β → α → A R α}

variable {δ₀ : β → α → A R α}
end TensorGrading
namespace CountTables

section
open AssociativeElimination
abbrev K := ZMod 2
abbrev F := Fin 5
abbrev B := Fin 4

def H : A K F := atom 0
def U (i : Fin 2) : A K F := atom ⟨i.val+1,by omega⟩
def V (i : Fin 2) : A K F := atom ⟨i.val+3,by omega⟩
def bracket {R α : Type*} [CommRing R] (p q : A R α) := p*q-q*p

open WordGrading

end

open AssociativeElimination
abbrev G := Fin 3
def X : A K G := atom 0
def Y (i : Fin 2) : A K G := atom ⟨i.val+1,by omega⟩
def C (i : Fin 2) := bracket X (Y i)
def realize : A K F →ₐ[K] A K G := lift (fun a => match a with
  | 0 => X*X | 1 => Y 0 | 2 => Y 1 | 3 => C 0 | _ => C 1)
def δ (i : Fin 2) : A K G →ₗ[K] A K G := deriv (fun a => if a=0 ∨ a.val=i.val+1 then C i else 0)
def ε : A K G →ₗ[K] A K G := deriv (fun a => if a=0 then 0 else bracket (Y 0) (Y 1))
def baseDeriv : B → A K G →ₗ[K] A K G
  | 0 => (δ 0).comp (δ 0)
  | 1 => (δ 1).comp (δ 1)
  | 2 => ε
  | _ => (δ 0).comp ε-ε.comp (δ 0)

@[simp] theorem realize_H : realize H=X*X := by simp [realize,H]
@[simp] theorem realize_U (i : Fin 2) : realize (U i)=Y i := by fin_cases i <;> simp [realize,U]
@[simp] theorem realize_V (i : Fin 2) : realize (V i)=C i := by fin_cases i <;> simp [realize,V]
@[simp] theorem realize_bracket (p q : A K F) : realize (bracket p q)=bracket (realize p) (realize q) := by simp [bracket]
@[simp] theorem deriv_bracket {R α : Type*} [CommRing R] (f : α → A R α) (p q : A R α) :
    deriv f (bracket p q)=bracket (deriv f p) q+bracket p (deriv f q) := by
  simp only [bracket,map_sub,AssociativeElimination.deriv_mul]; abel

@[simp] theorem bracket_add_left (p q r : A K G) : bracket (p+q) r=bracket p r+bracket q r := by simp [bracket,add_mul,mul_add]; abel
@[simp] theorem bracket_add_right (p q r : A K G) : bracket p (q+r)=bracket p q+bracket p r := by simp [bracket,add_mul,mul_add]; abel
@[simp] theorem bracket_sub_left (p q r : A K G) : bracket (p-q) r=bracket p r-bracket q r := by simp [bracket,sub_mul,mul_sub]; abel
@[simp] theorem bracket_sub_right (p q r : A K G) : bracket p (q-r)=bracket p q-bracket p r := by simp [bracket,sub_mul,mul_sub]; abel
@[simp] theorem bracket_zero_left (r : A K G) : bracket 0 r=0 := by simp [bracket]
@[simp] theorem bracket_zero_right (r : A K G) : bracket r 0=0 := by simp [bracket]
@[simp] theorem bracket_self (r : A K G) : bracket r r=0 := by simp [bracket]
theorem bracket_swap (p q : A K G) : bracket p q=bracket q p := by simp [bracket,CharTwo.sub_eq_add,add_comm]
theorem bracket_ad_square (u v : A K G) : bracket u (bracket u v)=bracket (u*u) v := by
  simp only [bracket,sub_eq_add_neg,CharTwo.neg_eq,mul_add,add_mul,mul_assoc]
  calc
    _ = u*(u*v)+v*(u*u)+(u*(v*u)+u*(v*u)) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]
theorem bracket_leibniz (p q r : A K G) : bracket p (bracket q r)=bracket (bracket p q) r+bracket q (bracket p r) := by
  simp only [bracket]; noncomm_ring
@[simp] theorem δ_X (i : Fin 2) : δ i X=C i := by simp [δ,X]
@[simp] theorem δ_Y_self (i : Fin 2) : δ i (Y i)=C i := by simp [δ,Y]
@[simp] theorem δ_Y_other (i j : Fin 2) (h : j≠i) : δ i (Y j)=0 := by
  have hv : j.val≠i.val := fun he => h (Fin.ext he)
  simp [δ,Y,hv]
theorem δ_mul (i : Fin 2) (p q : A K G) : δ i (p*q)=δ i p*q+p*δ i q := deriv_mul _ _ _
@[simp] theorem δ_bracket (i : Fin 2) (p q : A K G) : δ i (bracket p q)=bracket (δ i p) q+bracket p (δ i q) := deriv_bracket _ _ _
@[simp] theorem δ_H (i : Fin 2) : δ i (X*X)=bracket (X*X) (Y i) := by
  rw [δ_mul,δ_X,← bracket_ad_square]
  change C i*X+X*C i=bracket X (C i)
  simp [bracket,CharTwo.sub_eq_add,add_comm]
theorem bracket_X_Y (i : Fin 2) : bracket X (Y i)=C i := rfl
theorem bracket_X_C (i : Fin 2) : bracket X (C i)=bracket (X*X) (Y i) := bracket_ad_square _ _
@[simp] theorem δ_C_self (i : Fin 2) : δ i (C i)=bracket (X*X+C i) (Y i) := by
  change δ i (bracket X (Y i))=_
  rw [δ_bracket,δ_X,δ_Y_self,bracket_X_C,bracket_add_left]
  exact add_comm _ _
@[simp] theorem δ_C_other (i j : Fin 2) (h : j≠i) : δ i (C j)=bracket (C i) (Y j) := by
  rw [C,δ_bracket,δ_X,δ_Y_other i j h,bracket_zero_right,add_zero]
@[simp] theorem ε_X : ε X=0 := by simp [ε,X]
@[simp] theorem ε_Y (i : Fin 2) : ε (Y i)=bracket (Y 0) (Y 1) := by simp [ε,Y]
@[simp] theorem ε_bracket (p q : A K G) : ε (bracket p q)=bracket (ε p) q+bracket p (ε q) := deriv_bracket _ _ _
@[simp] theorem ε_H : ε (X*X)=0 := by simp [ε,AssociativeElimination.deriv_mul,X]
theorem ε_C (i : Fin 2) : ε (C i)=bracket (C 0) (Y 1)+bracket (Y 0) (C 1) := by
  rw [C,ε_bracket,ε_X,ε_Y,bracket_zero_left,zero_add,bracket_leibniz]
  rfl

def J := baseDeriv 3
@[simp] theorem J_X : J X=bracket (C 0) (Y 1)+bracket (Y 0) (C 1) := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε_X,map_zero,δ_X,ε_C]
  simp only [zero_sub,CharTwo.neg_eq]
@[simp] theorem J_Y_zero : J (Y 0)=bracket (Y 0) (C 1) := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε_Y,δ_bracket,δ_Y_self,
    δ_Y_other 0 1 (by decide),bracket_zero_right,add_zero,ε_C]
  simp only [sub_add_eq_sub_sub,sub_self,zero_sub,CharTwo.neg_eq]
@[simp] theorem J_Y_one : J (Y 1)=bracket (Y 1) (C 0) := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε_Y,δ_bracket,δ_Y_self,
    δ_Y_other 0 1 (by decide),bracket_zero_right,add_zero,map_zero,sub_zero]
  exact bracket_swap _ _
@[simp] theorem J_bracket (p q : A K G) : J (bracket p q)=bracket (J p) q+bracket p (J q) := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε_bracket,δ_bracket,map_add,
    bracket_sub_left,bracket_sub_right]
  abel
@[simp] theorem J_mul (p q : A K G) : J (p*q)=J p*q+p*J q := by
  simp only [J,baseDeriv,LinearMap.sub_apply,LinearMap.comp_apply,ε,δ,AssociativeElimination.deriv_mul,
    map_add,sub_mul,mul_sub]
  abel
@[simp] theorem J_H : J (X*X)=bracket (X*X) (bracket (Y 0) (Y 1)) := by
  rw [J_mul,J_X]
  have h : bracket (C 0) (Y 1)+bracket (Y 0) (C 1)=bracket X (bracket (Y 0) (Y 1)) :=
    (bracket_leibniz X (Y 0) (Y 1)).symm
  rw [h,← bracket_ad_square]
  simp only [bracket,CharTwo.sub_eq_add]
  exact add_comm _ _
@[simp] theorem J_C_zero : J (C 0)=bracket (C 0) (C 1)+
    bracket (bracket (C 0) (Y 1)+bracket (Y 0) (C 1)) (Y 0)+bracket (Y 0) (bracket (X*X) (Y 1)) := by
  change J (bracket X (Y 0))=_
  rw [J_bracket,J_X,J_Y_zero,bracket_leibniz,bracket_X_C]
  rw [bracket_X_Y 0,add_left_comm,← add_assoc]
@[simp] theorem J_C_one : J (C 1)=bracket (C 0) (C 1)+
    bracket (bracket (C 0) (Y 1)+bracket (Y 0) (C 1)) (Y 1)+bracket (Y 1) (bracket (X*X) (Y 0)) := by
  change J (bracket X (Y 1))=_
  rw [J_bracket,J_X,J_Y_one,bracket_leibniz,bracket_X_C]
  rw [bracket_X_Y 1,bracket_swap (C 1) (C 0),add_left_comm,← add_assoc]

@[simp] theorem δ_square_H (i : Fin 2) : δ i (δ i (X*X))=
    bracket (X*X) (C i)+bracket (bracket (X*X) (Y i)) (Y i) := by
  rw [δ_H,δ_bracket,δ_H,δ_Y_self]
  exact add_comm _ _
@[simp] theorem δ_H_add_C (i : Fin 2) : δ i (X*X+C i)=bracket (C i) (Y i) := by
  rw [map_add,δ_H,δ_C_self,bracket_add_left,CharTwo.add_cancel_left]
@[simp] theorem δ_square_C_self (i : Fin 2) : δ i (δ i (C i))=
    bracket (X*X) (C i)+bracket (bracket (C i) (Y i)) (Y i) := by
  rw [δ_C_self,δ_bracket,δ_H_add_C,δ_Y_self,bracket_add_left,bracket_self,add_zero]
  exact add_comm _ _
@[simp] theorem δ_square_C_other (i j : Fin 2) (h : j≠i) : δ i (δ i (C j))=
    bracket (bracket (X*X+C i) (Y i)) (Y j) := by
  rw [δ_C_other i j h,δ_bracket,δ_C_self,δ_Y_other i j h,bracket_zero_right,add_zero]

@[simp] theorem realize_atom_zero : realize (atom (0 : F))=X*X := realize_H
@[simp] theorem realize_atom_one : realize (atom (1 : F))=Y 0 := realize_U 0
@[simp] theorem realize_atom_two : realize (atom (2 : F))=Y 1 := realize_U 1
@[simp] theorem realize_atom_three : realize (atom (3 : F))=C 0 := realize_V 0
@[simp] theorem realize_atom_four : realize (atom (4 : F))=C 1 := realize_V 1

attribute [local irreducible] X Y C H U V
end CountTables
namespace WeightedDeletion
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]
def raw (κ : α → α → α → R) (l r : α) : List α → A R α
  | [] => 0
  | a::s => κ l a (s.headD r) • word (FreeMonoid.ofList s)+atom a*raw κ a r s

def op (κ : α → α → α → R) (l r : α) : Module.End R (A R α) :=
  (Finsupp.linearCombination R (fun w : FreeMonoid α => raw κ l r w.toList)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap
@[simp] theorem op_word (κ : α → α → α → R) (l r : α) (s : List α) :
    op κ l r (word (FreeMonoid.ofList s))=raw κ l r s := by change Finsupp.linearCombination R (fun monoidWord : FreeMonoid α => raw κ l r monoidWord.toList) (Finsupp.single (FreeMonoid.ofList s) 1) = _; simp

def count (wt : α → ℕ) (s : List α) : ℕ := (s.map wt).sum
@[simp] theorem count_nil (wt : α → ℕ) : count wt []=0 := rfl
@[simp] theorem count_cons (wt : α → ℕ) (a : α) (s : List α) : count wt (a::s)=wt a+count wt s := rfl

end WeightedDeletion

end DeligneDrinfeld

end

end OAI

end
end

section
section
/-! Transfer of OpenAI's Deligne–Drinfeld theorem (`OAI.DeligneDrinfeld.MainStatement`,
OpenAI Math Release, https://github.com/openai/math) to the published
`GrothendieckTeichmuller` statements about `grt1`. -/

namespace OAI.DeligneDrinfeld.GTBridge

open GrothendieckTeichmuller

noncomputable section

/-! ### The two free Lie algebras on two generators -/

/-- `Lxy → L`, `gx ↦ x`, `gy ↦ y`. -/
def φ : Lxy →ₗ⁅ℚ⁆ L := substXY x y

/-- `L → Lxy`, `x ↦ gx`, `y ↦ gy`. -/
def ψ : L →ₗ⁅ℚ⁆ Lxy := eval gx gy

theorem eval_comp_φ {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) (p : Lxy) :
    eval a b (φ p) = substXY a b p := by
  have h : (eval a b).comp φ = substXY a b := by
    apply FreeLieAlgebra.hom_ext
    intro i
    fin_cases i <;> simp [φ, substXY, eval, x, y]
  exact LieHom.congr_fun h p

theorem substXY_comp_ψ {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) (q : L) :
    substXY a b (ψ q) = eval a b q := by
  have h : (substXY a b).comp ψ = eval a b := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [ψ, eval, gx, gy, substXY]
  exact LieHom.congr_fun h q

@[simp] theorem ψ_φ (p : Lxy) : ψ (φ p) = p := by
  have h : ψ.comp φ = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro i
    fin_cases i <;> simp [φ, ψ, substXY, eval, x, y, gx, gy]
  exact LieHom.congr_fun h p

@[simp] theorem φ_ψ (q : L) : φ (ψ q) = q := by
  have h : φ.comp ψ = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [φ, ψ, substXY, eval, x, y, gx, gy]
  exact LieHom.congr_fun h q

theorem φ_injective : Function.Injective φ := fun a b h => by
  simpa using congrArg ψ h

@[simp] theorem φ_gx : φ gx = x := by simp [φ]
@[simp] theorem φ_gy : φ gy = y := by simp [φ]

/-- Naturality of substitution. -/
theorem map_substXY {M N : Type*} [LieRing M] [LieAlgebra ℚ M] [LieRing N] [LieAlgebra ℚ N]
    (f : M →ₗ⁅ℚ⁆ N) (a b : M) (p : Lxy) : f (substXY a b p) = substXY (f a) (f b) p := by
  have h : f.comp (substXY a b) = substXY (f a) (f b) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    fin_cases i <;> simp [substXY]
  exact LieHom.congr_fun h p

/-! ### The two presentations of `t₄` -/

/-- `t₄` (published) → `T4` (OpenAI), on the free Lie algebra level. -/
def αPre : FreeLieAlgebra ℚ (Fin 4 × Fin 4) →ₗ⁅ℚ⁆ T4 :=
  FreeLieAlgebra.lift ℚ (fun p => t p.1 p.2)

theorem dkIdeal_le : dkIdeal 4 ≤ αPre.ker := by
  rw [dkIdeal, LieSubmodule.lieSpan_le]
  intro z hz
  change αPre z = 0
  rcases hz with ⟨i, rfl⟩ | ⟨i, j, rfl⟩ | ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl, rfl⟩ |
      ⟨i, j, k, hij, hik, hjk, rfl⟩
  · simp [αPre]
  · simp only [αPre, map_sub, FreeLieAlgebra.lift_of_apply]
    rw [t_comm j i, sub_self]
  · simpa only [αPre, LieHom.map_lie, FreeLieAlgebra.lift_of_apply] using
      t_disjoint i j k l hij hik hil hjk hjl hkl
  · simpa only [αPre, LieHom.map_lie, map_add, FreeLieAlgebra.lift_of_apply] using
      t_three i j k hij hik hjk

/-- `t₄` (published) → `T4` (OpenAI), `t i j ↦ t i j`. -/
def α : DrinfeldKohno 4 →ₗ⁅ℚ⁆ T4 :=
  { (dkIdeal 4).toSubmodule.liftQ αPre.toLinearMap dkIdeal_le with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact αPre.map_lie a b }

@[simp] theorem α_dkGen (i j : Fin 4) : α (dkGen i j) = t i j := by
  change αPre (FreeLieAlgebra.of ℚ (i, j)) = t i j
  simp [αPre]

theorem dk_mk_eq_zero {r : FreeLieAlgebra ℚ (Fin 4 × Fin 4)} (hr : r ∈ dkRelations 4) :
    (LieSubmodule.Quotient.mk (N := dkIdeal 4) r : DrinfeldKohno 4) = 0 := by
  rw [LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan hr

theorem dkGen_symm (i j : Fin 4) : dkGen i j = dkGen j i := by
  have h := dk_mk_eq_zero (Or.inr (Or.inl ⟨i, j, rfl⟩))
  rw [← sub_eq_zero]
  change (LieSubmodule.Quotient.mk' (dkIdeal 4) (FreeLieAlgebra.of ℚ (i, j)) -
    LieSubmodule.Quotient.mk' (dkIdeal 4) (FreeLieAlgebra.of ℚ (j, i)) : DrinfeldKohno 4) = 0
  rw [← map_sub]
  exact h

theorem dkGen_self (i : Fin 4) : dkGen i i = 0 :=
  dk_mk_eq_zero (Or.inl ⟨i, rfl⟩)

/-- `T4` (OpenAI) → `t₄` (published), `t i j ↦ t i j`. -/
def β : T4 →ₗ⁅ℚ⁆ DrinfeldKohno 4 :=
  T4Universal.lift (fun i j => dkGen i j) dkGen_symm dkGen_self
    (fun i j k l hij hik hil hjk hjl hkl => by
      have h := dk_mk_eq_zero (Or.inr (Or.inr (Or.inl
        ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl, rfl⟩)))
      rw [LieSubmodule.Quotient.mk_bracket] at h
      exact h)
    (fun i j k hij hik hjk => by
      have h := dk_mk_eq_zero (Or.inr (Or.inr (Or.inr ⟨i, j, k, hij, hik, hjk, rfl⟩)))
      rw [LieSubmodule.Quotient.mk_bracket] at h
      have e : (LieSubmodule.Quotient.mk (N := dkIdeal 4)
          (FreeLieAlgebra.of ℚ (i, k) + FreeLieAlgebra.of ℚ (j, k)) : DrinfeldKohno 4) =
          dkGen i k + dkGen j k :=
        map_add (LieSubmodule.Quotient.mk' (dkIdeal 4)) _ _
      rw [e] at h
      exact h)

@[simp] theorem β_t (i j : Fin 4) : β (t i j) = dkGen i j := T4Universal.lift_t _ _ _ _ _ _ _

/-! ### `grt₁` (published) versus `W` (OpenAI) -/

theorem mem_W_of_mem_grt1 {p : Lxy} (hp : p ∈ grt1) : φ p ∈ W := by
  rw [mem_grt1_iff] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg φ h1
    rw [map_substXY, map_neg] at this
    simp only [φ_gx, φ_gy] at this
    rw [eval_comp_φ, this]
    exact add_neg_cancel _
  · have := congrArg φ h2
    simp only [map_add, map_substXY, map_sub, map_neg, φ_gx, φ_gy, map_zero] at this
    rw [eval_comp_φ, eval_comp_φ]
    have hs : substXY x y p = φ p := rfl
    rw [hs] at this
    exact this
  · have := congrArg α h3
    simp only [map_add, map_sub, map_substXY, α_dkGen, map_zero] at this
    simp only [eval_comp_φ]
    rw [← sub_eq_zero, ← neg_eq_zero, ← this]
    abel

theorem mem_grt1_of_mem_W {q : L} (hq : q ∈ W) : ψ q ∈ grt1 := by
  obtain ⟨h1, h2, h3⟩ := hq
  rw [mem_grt1_iff]
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg ψ h1
    rw [map_add, map_zero] at this
    rw [substXY_comp_ψ]
    have he : ψ (eval y x q) = eval gy gx q := by
      rw [ψ, ← LieHom.comp_apply]
      congr 1
      apply FreeLieAlgebra.hom_ext
      intro i
      cases i <;> simp [eval, x, y]
    rw [he] at this
    exact eq_neg_of_add_eq_zero_right this
  · have := congrArg ψ h2
    have he : ∀ a b : L, ψ (eval a b q) = eval (ψ a) (ψ b) q := fun a b => map_eval ψ a b q
    rw [map_add, map_add, he, he, map_zero] at this
    simp only [substXY_comp_ψ]
    have hx : ψ x = gx := by simp [ψ]
    have hy : ψ y = gy := by simp [ψ]
    have hq' : eval gx gy q = ψ q := rfl
    simpa only [map_sub, map_neg, hx, hy, hq'] using this
  · have := congrArg β h3
    simp only [map_add, map_eval, β_t] at this
    simp only [substXY_comp_ψ]
    rw [← neg_eq_zero, ← sub_eq_zero.mpr this]
    abel

/-! ### The Ihara derivations -/

/-- `φ` conjugates the published Ihara derivation to OpenAI's `D`. -/
def conjDeriv (f : Lxy) : LieDerivation ℚ L L where
  toFun q := φ (iharaDeriv f (ψ q))
  map_add' a b := by simp only [map_add]
  map_smul' c a := by simp only [map_smul, RingHom.id_apply]
  leibniz' a b := by
    change φ (iharaDeriv f (ψ ⁅a, b⁆)) =
      ⁅a, φ (iharaDeriv f (ψ b))⁆ - ⁅b, φ (iharaDeriv f (ψ a))⁆
    rw [LieHom.map_lie, LieDerivation.apply_lie_eq_sub, map_sub, LieHom.map_lie,
      LieHom.map_lie, φ_ψ, φ_ψ]

theorem φ_iharaDeriv (f u : Lxy) : φ (iharaDeriv f u) = D (φ f) (φ u) := by
  have h : conjDeriv f = derivation (φ f) := by
    apply derivation_ext
    · change φ (iharaDeriv f (ψ x)) = D (φ f) x
      have : ψ x = gx := by simp [ψ]
      rw [this, iharaDeriv_gx, D_x, map_zero]
    · change φ (iharaDeriv f (ψ y)) = D (φ f) y
      have : ψ y = gy := by simp [ψ]
      rw [this, iharaDeriv_gy, D_y, LieHom.map_lie, φ_gy]
  have := LieDerivation.congr_fun h (φ u)
  simpa [conjDeriv] using this

theorem φ_iharaBracket (f g : Lxy) : φ (iharaBracket f g) = ihara (φ f) (φ g) := by
  simp only [iharaBracket, ihara, map_add, map_sub, LieHom.map_lie, φ_iharaDeriv]
  abel

theorem ψ_ihara (p q : L) : ψ (ihara p q) = iharaBracket (ψ p) (ψ q) := by
  apply φ_injective
  rw [φ_iharaBracket, φ_ψ, φ_ψ, φ_ψ]

theorem iharaDeriv_add (f g : Lxy) : iharaDeriv (f + g) = iharaDeriv f + iharaDeriv g := by
  refine LieDerivation.ext fun u => φ_injective ?_
  rw [LieDerivation.add_apply, map_add, φ_iharaDeriv, φ_iharaDeriv, φ_iharaDeriv, map_add,
    D_add_left]

theorem iharaDeriv_smul (c : ℚ) (f : Lxy) : iharaDeriv (c • f) = c • iharaDeriv f := by
  refine LieDerivation.ext fun u => φ_injective ?_
  rw [LieDerivation.smul_apply, map_smul, φ_iharaDeriv, φ_iharaDeriv, map_smul, D_smul_left]

theorem iharaDeriv_sub (f g : Lxy) : iharaDeriv (f - g) = iharaDeriv f - iharaDeriv g := by
  have h := iharaDeriv_add (f - g) g
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem iharaDeriv_iharaBracket (f g : Lxy) :
    iharaDeriv (iharaBracket f g) = ⁅iharaDeriv f, iharaDeriv g⁆ := by
  rw [ihara_deriv_commutator, iharaBracket, iharaDeriv_sub, iharaDeriv_add]

/-! ### Injectivity of `f ↦ D_f` on `grt₁` -/

section
attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

end

/-! ### Homogeneity -/

theorem eval_smul_of_mem_Ln {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) (c : ℚ)
    {n : ℕ} {q : L} (hq : q ∈ Ln n) : eval (c • a) (c • b) q = c ^ n • eval a b q := by
  induction hq using Submodule.span_induction with
  | mem q hw =>
    induction hw with
    | generator i => cases i <;> simp [eval]
    | bracket _ _ iha ihb =>
      rw [LieHom.map_lie, LieHom.map_lie, iha, ihb, smul_lie, lie_smul, smul_smul, pow_add]
  | zero => simp
  | add u v _ _ hu hv => rw [map_add, map_add, hu, hv, smul_add]
  | smul r u _ hu => rw [map_smul, map_smul, hu, smul_comm]

theorem isHomogeneous_ψ {n : ℕ} {q : L} (hq : q ∈ Ln n) : IsHomogeneousOfDegree n (ψ q) := by
  intro c
  rw [substXY_comp_ψ, eval_smul_of_mem_Ln _ _ _ hq]
  rfl

/-! ### The bridge -/

theorem deligne_drinfeld_ihara_of_main (hmain : MainStatement)
    (hinj : Set.InjOn iharaDeriv (grt1 : Set Lxy)) :
    ∃ sigma : ℕ → Lxy,
      (∀ p, sigma p ∈ grt1 ∧ IsHomogeneousOfDegree (2 * p + 3) (sigma p)) ∧
      Function.Injective ⇑(FreeLieAlgebra.lift ℚ (fun p : ℕ => iharaDeriv (sigma p))) ∧
      Set.range ⇑(FreeLieAlgebra.lift ℚ (fun p : ℕ => iharaDeriv (sigma p))) =
        iharaDeriv '' (grt1 : Set Lxy) := by
  obtain ⟨e, hgr, hlie, -⟩ := hmain
  let sigma : ℕ → Lxy := fun p => ψ (e (FreeLieAlgebra.of ℚ p) : L)
  -- the composite `u ↦ D_{ψ (e u)}` is a morphism of Lie algebras
  let G : OddFree →ₗ⁅ℚ⁆ LieDerivation ℚ Lxy Lxy :=
    { toFun := fun u => iharaDeriv (ψ (e u : L))
      map_add' := fun u v => by simp [iharaDeriv_add]
      map_smul' := fun c u => by simp [iharaDeriv_smul]
      map_lie' := by
        intro u v
        simp only [hlie, ψ_ihara, iharaDeriv_iharaBracket] }
  have hG : FreeLieAlgebra.lift ℚ (fun p : ℕ => iharaDeriv (sigma p)) = G := by
    apply FreeLieAlgebra.hom_ext
    intro p
    simp [G, sigma]
  refine ⟨sigma, fun p => ⟨mem_grt1_of_mem_W (e _).2, ?_⟩, ?_, ?_⟩
  · apply isHomogeneous_ψ
    apply (hgr _ _).2
    exact Submodule.subset_span (WeightedWord.generator p)
  · rw [hG]
    intro u v huv
    have h := hinj (mem_grt1_of_mem_W (e u).2) (mem_grt1_of_mem_W (e v).2) huv
    have h' := congrArg φ h
    rw [φ_ψ, φ_ψ] at h'
    exact e.injective (Subtype.ext h')
  · rw [hG]
    ext d
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨ψ (e u : L), mem_grt1_of_mem_W (e u).2, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      refine ⟨e.symm ⟨φ f, mem_W_of_mem_grt1 hf⟩, ?_⟩
      change iharaDeriv (ψ (e (e.symm ⟨φ f, _⟩) : L)) = iharaDeriv f
      rw [LinearEquiv.apply_symm_apply]
      simp

end

end OAI.DeligneDrinfeld.GTBridge

end
end

section
section
namespace GrothendieckTeichmuller

theorem deligne_drinfeld_ihara_oai :
    ∃ sigma : ℕ → Lxy,
      (∀ p, sigma p ∈ grt1 ∧ IsHomogeneousOfDegree (2 * p + 3) (sigma p)) ∧
      Function.Injective ⇑(FreeLieAlgebra.lift ℚ (fun p : ℕ => iharaDeriv (sigma p))) ∧
      Set.range ⇑(FreeLieAlgebra.lift ℚ (fun p : ℕ => iharaDeriv (sigma p))) =
        iharaDeriv '' (grt1 : Set Lxy) :=
  OAI.DeligneDrinfeld.GTBridge.deligne_drinfeld_ihara_of_main OAI.DeligneDrinfeld.main
    ihara_deriv_injOn_grt1

end GrothendieckTeichmuller

end
end

section
open GrothendieckTeichmuller

theorem solution :
    ∃ sigma : ℕ → Lxy,
      (∀ p, sigma p ∈ grt1 ∧ IsHomogeneousOfDegree (2 * p + 3) (sigma p)) ∧
      Function.Injective ⇑(FreeLieAlgebra.lift ℚ (fun p : ℕ => iharaDeriv (sigma p))) ∧
      Set.range ⇑(FreeLieAlgebra.lift ℚ (fun p : ℕ => iharaDeriv (sigma p))) =
        iharaDeriv '' (grt1 : Set Lxy) := by
  apply GrothendieckTeichmuller.deligne_drinfeld_ihara_oai <;> assumption

end
