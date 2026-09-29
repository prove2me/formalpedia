-- Prove2me | solution 1 for IsLocalRing.exists_forall_algHom_bijective_of_forall_pullback_bijective_of_hull
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/44987644-9ac7-5490-8dd7-a2b09eed4088

import Mathlib
import Theorems.Thm_IsLocalRing_isLocalRing_and_isArtinianRing_equalizer_of_comp_algebraMap_eq_residue
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_hull

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

universe u

namespace P2mSchlessingerUniversal

open IsLocalRing

structure Hull (O : Type u) [CommRing O] [IsLocalRing O] (R : Type u) [CommRing R] [Algebra O R] where
  F : ∀ (A : Type u) [CommRing A] [Algebra O A], (A →+* ResidueField O) → Type u
  Frel : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O},
    F A resA → F A resA → Prop
  hrefl : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    (x : F A resA), Frel x x
  hsymm : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    (x y : F A resA), Frel x y → Frel y x
  htrans : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    (x y z : F A resA), Frel x y → Frel y z → Frel x z
  Fmap : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    (f : A →ₐ[O] A'), resA'.comp f.toRingHom = resA → F A resA → F A' resA'
  Fmap_rel : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA) (x y : F A resA),
    Frel x y → Frel (Fmap f hf x) (Fmap f hf y)
  Fmap_id : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    (h : resA.comp (AlgHom.id O A).toRingHom = resA) (x : F A resA), Frel (Fmap (AlgHom.id O A) h x) x
  Fmap_comp : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    {A'' : Type u} [CommRing A''] [Algebra O A''] {resA'' : A'' →+* ResidueField O}
    (f : A →ₐ[O] A') (g : A' →ₐ[O] A'') (hf : resA'.comp f.toRingHom = resA)
    (hg : resA''.comp g.toRingHom = resA') (hgf : resA''.comp (g.comp f).toRingHom = resA)
    (x : F A resA), Frel (Fmap (g.comp f) hgf x) (Fmap g hg (Fmap f hf x))

  x₀ : F (ResidueField O) (RingHom.id (ResidueField O))
  hx₀ : ∀ x : F (ResidueField O) (RingHom.id (ResidueField O)), Frel x x₀
  hglue : ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [Algebra O B]
      (resB : B →+* ResidueField O), Function.Surjective resB →
      resB.comp (algebraMap O B) = residue O →
    ∀ (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
      (resA' : A' →+* ResidueField O), Function.Surjective resA' →
      resA'.comp (algebraMap O A') = residue O →
    ∀ (A'' : Type u) [CommRing A''] [IsLocalRing A''] [IsArtinianRing A''] [Algebra O A'']
      (resA'' : A'' →+* ResidueField O), Function.Surjective resA'' →
      resA''.comp (algebraMap O A'') = residue O →
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
      (resA : A →+* ResidueField O), Function.Surjective resA →
      resA.comp (algebraMap O A) = residue O →
    ∀ (p' : B →ₐ[O] A') (hp' : resA'.comp p'.toRingHom = resB)
      (p'' : B →ₐ[O] A'') (hp'' : resA''.comp p''.toRingHom = resB)
      (q' : A' →ₐ[O] A) (hq' : resA.comp q'.toRingHom = resA')
      (q'' : A'' →ₐ[O] A) (hq'' : resA.comp q''.toRingHom = resA''),
      q'.comp p' = q''.comp p'' →
      (∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'') →
      Function.Surjective q'' →
      (∀ (x' : F A' resA') (x'' : F A'' resA''), Frel (Fmap q' hq' x') (Fmap q'' hq'' x'') →
          ∃ y : F B resB, Frel (Fmap p' hp' y) x' ∧ Frel (Fmap p'' hp'' y) x'') ∧
      (∀ (y₁ y₂ : F B resB), Frel (Fmap p' hp' y₁) (Fmap p' hp' y₂) →
          Frel (Fmap p'' hp'' y₁) (Fmap p'' hp'' y₂) → Frel y₁ y₂)
  resR : R →+* ResidueField O
  hresR : resR.comp (algebraMap O R) = residue O
  Ξ : ∀ (A : Type u) [CommRing A] [Algebra O A], IsLocalRing A → IsArtinianRing A →
    ∀ (resA : A →+* ResidueField O), Function.Surjective resA →
      resA.comp (algebraMap O A) = residue O →
    ∀ (u : R →ₐ[O] A), resA.comp u.toRingHom = resR → F A resA

  Ξ_nat : ∀ (A : Type u) [CommRing A] [Algebra O A] (hlA : IsLocalRing A) (haA : IsArtinianRing A)
      (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
      (hcA : resA.comp (algebraMap O A) = residue O)
      (A' : Type u) [CommRing A'] [Algebra O A'] (hlA' : IsLocalRing A') (haA' : IsArtinianRing A')
      (resA' : A' →+* ResidueField O) (hsA' : Function.Surjective resA')
      (hcA' : resA'.comp (algebraMap O A') = residue O)
      (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA)
      (u : R →ₐ[O] A) (hu : resA.comp u.toRingHom = resR)
      (hfu : resA'.comp (f.comp u).toRingHom = resR),
      Frel (Ξ A' hlA' haA' resA' hsA' hcA' (f.comp u) hfu) (Fmap f hf (Ξ A hlA haA resA hsA hcA u hu))

  Ξ_inj : ∀ (hl : IsLocalRing (DualNumber (ResidueField O)))
      (ha : IsArtinianRing (DualNumber (ResidueField O)))
      (hs : Function.Surjective (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom)
      (hc : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
        (algebraMap O (DualNumber (ResidueField O))) = residue O)
      (θ θ' : R →ₐ[O] DualNumber (ResidueField O))
      (hθ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ.toRingHom = resR)
      (hθ' : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ'.toRingHom =
        resR),
      Frel (Ξ _ hl ha _ hs hc θ hθ) (Ξ _ hl ha _ hs hc θ' hθ') → θ = θ'

  Ξ_surj : ∀ (hl : IsLocalRing (DualNumber (ResidueField O)))
      (ha : IsArtinianRing (DualNumber (ResidueField O)))
      (hs : Function.Surjective (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom)
      (hc : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
        (algebraMap O (DualNumber (ResidueField O))) = residue O)
      (x : F (DualNumber (ResidueField O))
        (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom),
      ∃ (θ : R →ₐ[O] DualNumber (ResidueField O))
        (hθ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ.toRingHom =
          resR), Frel (Ξ _ hl ha _ hs hc θ hθ) x

  Ξ_lift : ∀ (A' : Type u) [CommRing A'] [Algebra O A'] (hlA' : IsLocalRing A') (haA' : IsArtinianRing A')
      (resA' : A' →+* ResidueField O) (hsA' : Function.Surjective resA')
      (hcA' : resA'.comp (algebraMap O A') = residue O)
      (A : Type u) [CommRing A] [Algebra O A] (hlA : IsLocalRing A) (haA : IsArtinianRing A)
      (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
      (hcA : resA.comp (algebraMap O A) = residue O)
      (q : A' →ₐ[O] A) (hq : resA.comp q.toRingHom = resA'), Function.Surjective q →
      ∀ (t : A'), t ≠ 0 → t ∈ RingHom.ker resA' → (∀ m ∈ RingHom.ker resA', m * t = 0) →
      (∀ a : A', q a = 0 ↔ a ∈ Ideal.span {t}) →
      ∀ (u : R →ₐ[O] A) (hu : resA.comp u.toRingHom = resR) (η' : F A' resA'),
      Frel (Fmap q hq η') (Ξ A hlA haA resA hsA hcA u hu) → ∃ u' : R →ₐ[O] A', q.comp u' = u

variable {O : Type u} [CommRing O] [IsLocalRing O] {R : Type u} [CommRing R] [Algebra O R]
  (S : Hull O R)

namespace Hull

theorem Fmap_congr {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    (f f' : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA) (hf' : resA'.comp f'.toRingHom = resA)
    (h : f = f') (x : S.F A resA) : S.Fmap f hf x = S.Fmap f' hf' x := by
  subst h; rfl

theorem Ξ_congr {A : Type u} [CommRing A] [Algebra O A] (hlA : IsLocalRing A) (haA : IsArtinianRing A)
    (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
    (hcA : resA.comp (algebraMap O A) = residue O) (u u' : R →ₐ[O] A)
    (hu : resA.comp u.toRingHom = S.resR) (hu' : resA.comp u'.toRingHom = S.resR) (h : u = u') :
    S.Ξ A hlA haA resA hsA hcA u hu = S.Ξ A hlA haA resA hsA hcA u' hu' := by
  subst h; rfl

theorem ker_res_eq_maximalIdeal {B : Type u} [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    (res : B →+* ResidueField O) : RingHom.ker res = maximalIdeal B :=
  IsLocalRing.eq_maximalIdeal
    ((IsArtinianRing.isPrime_iff_isMaximal (RingHom.ker res)).1 (RingHom.ker_isPrime res))

theorem isUnit_iff_res_ne_zero {B : Type u} [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    (res : B →+* ResidueField O) (b : B) : IsUnit b ↔ res b ≠ 0 := by
  rw [ne_eq, ← RingHom.mem_ker, ker_res_eq_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    not_not]

def resAlgHom {A : Type u} [CommRing A] [Algebra O A] (resA : A →+* ResidueField O)
    (hcA : resA.comp (algebraMap O A) = residue O) : A →ₐ[O] ResidueField O :=
  { resA with
    commutes' := fun o => by
      change resA (algebraMap O A o) = residue O o
      rw [← RingHom.comp_apply, hcA] }

@[scoped simp] theorem resAlgHom_apply {A : Type u} [CommRing A] [Algebra O A] (resA : A →+* ResidueField O)
    (hcA : resA.comp (algebraMap O A) = residue O) (a : A) : resAlgHom resA hcA a = resA a := rfl

section dual

variable (O)

abbrev resD : DualNumber (ResidueField O) →+* ResidueField O :=
  (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom

theorem resD_apply (d : DualNumber (ResidueField O)) : resD O d = TrivSqZeroExt.fst d := rfl

theorem hlD : IsLocalRing (DualNumber (ResidueField O)) := inferInstance

theorem haD : IsArtinianRing (DualNumber (ResidueField O)) :=
  haveI : Module.Finite (ResidueField O) (DualNumber (ResidueField O)) :=
    inferInstanceAs (Module.Finite (ResidueField O) (ResidueField O × ResidueField O))
  IsArtinianRing.of_finite (ResidueField O) _

theorem hsD : Function.Surjective (resD O) := fun c => ⟨TrivSqZeroExt.inl c, rfl⟩

theorem hcD : (resD O).comp (algebraMap O (DualNumber (ResidueField O))) = residue O := rfl

end dual

section cartesian

variable {B : Type u} [CommRing B] [Algebra O B] {A' : Type u} [CommRing A'] [Algebra O A']
  {A'' : Type u} [CommRing A''] [Algebra O A''] {A : Type u} [CommRing A] [Algebra O A]
  (p' : B →ₐ[O] A') (p'' : B →ₐ[O] A'') (q' : A' →ₐ[O] A) (q'' : A'' →ₐ[O] A)
  (hcomm : q'.comp p' = q''.comp p'')
  (hcart : ∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'')

include hcomm hcart in
theorem cart_inj (b b' : B) (h1 : p' b = p' b') (h2 : p'' b = p'' b') : b = b' := by
  have hb : q' (p' b') = q'' (p'' b') := by
    change (q'.comp p') b' = (q''.comp p'') b'; rw [hcomm]
  exact (hcart _ _ hb).unique ⟨h1, h2⟩ ⟨rfl, rfl⟩

include hcomm hcart in

theorem exists_lift {T : Type u} [CommRing T] [Algebra O T] (v' : T →ₐ[O] A') (v'' : T →ₐ[O] A'')
    (hv : q'.comp v' = q''.comp v'') :
    ∃ w : T →ₐ[O] B, p'.comp w = v' ∧ p''.comp w = v'' := by
  classical
  have hx : ∀ x : T, q' (v' x) = q'' (v'' x) := fun x => by
    change (q'.comp v') x = (q''.comp v'') x; rw [hv]
  let f : T → B := fun x => (hcart (v' x) (v'' x) (hx x)).exists.choose
  have hf1 : ∀ x, p' (f x) = v' x := fun x => (hcart (v' x) (v'' x) (hx x)).exists.choose_spec.1
  have hf2 : ∀ x, p'' (f x) = v'' x := fun x => (hcart (v' x) (v'' x) (hx x)).exists.choose_spec.2
  have inj := cart_inj p' p'' q' q'' hcomm hcart
  let w : T →ₐ[O] B :=
    { toFun := f
      map_one' := inj _ _ (by rw [hf1, map_one, map_one]) (by rw [hf2, map_one, map_one])
      map_mul' := fun x y => inj _ _ (by rw [hf1, map_mul, map_mul, hf1, hf1])
        (by rw [hf2, map_mul, map_mul, hf2, hf2])
      map_zero' := inj _ _ (by rw [hf1, map_zero, map_zero]) (by rw [hf2, map_zero, map_zero])
      map_add' := fun x y => inj _ _ (by rw [hf1, map_add, map_add, hf1, hf1])
        (by rw [hf2, map_add, map_add, hf2, hf2])
      commutes' := fun o => inj _ _ (by rw [hf1, AlgHom.commutes, AlgHom.commutes])
        (by rw [hf2, AlgHom.commutes, AlgHom.commutes]) }
  exact ⟨w, AlgHom.ext hf1, AlgHom.ext hf2⟩

include hcomm hcart in
theorem lift_unique {T : Type u} [CommRing T] [Algebra O T] (w w' : T →ₐ[O] B)
    (h1 : p'.comp w = p'.comp w') (h2 : p''.comp w = p''.comp w') : w = w' :=
  AlgHom.ext fun x => cart_inj p' p'' q' q'' hcomm hcart _ _ (congr($h1 x)) (congr($h2 x))

end cartesian

section pullback

variable {A : Type u} [CommRing A] [Algebra O A]

abbrev It (t : A) : Ideal A := Ideal.span {t}

abbrev qt (t : A) : A →ₐ[O] A ⧸ It t := Ideal.Quotient.mkₐ O (It t)

theorem qt_apply (t a : A) : qt (O := O) t a = Ideal.Quotient.mk (It t) a := rfl

theorem qt_surjective (t : A) : Function.Surjective (qt (O := O) t) := Ideal.Quotient.mk_surjective

theorem qt_eq_zero_iff (t a : A) : qt (O := O) t a = 0 ↔ a ∈ Ideal.span {t} :=
  Ideal.Quotient.eq_zero_iff_mem

theorem qt_eq_iff (t a b : A) : qt (O := O) t a = qt (O := O) t b ↔ a - b ∈ Ideal.span {t} :=
  Ideal.Quotient.eq

theorem It_ne_top [IsLocalRing A] [IsArtinianRing A] (resA : A →+* ResidueField O) (t : A)
    (htm : t ∈ RingHom.ker resA) : It t ≠ ⊤ := by
  apply Ideal.span_singleton_ne_top
  rw [isUnit_iff_res_ne_zero resA, not_not]
  exact htm

theorem res_eq_zero_of_mem (resA : A →+* ResidueField O) (t : A) (htm : t ∈ RingHom.ker resA) (a : A)
    (ha : a ∈ It t) : resA a = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [map_mul, RingHom.mem_ker.1 htm, mul_zero]

theorem isLocalRing_quot [IsLocalRing A] [IsArtinianRing A] (resA : A →+* ResidueField O) (t : A)
    (htm : t ∈ RingHom.ker resA) : IsLocalRing (A ⧸ It t) :=
  haveI : Nontrivial (A ⧸ It t) := Ideal.Quotient.nontrivial_iff.2 (It_ne_top resA t htm)
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (It t)) Ideal.Quotient.mk_surjective

theorem isArtinianRing_quot [IsArtinianRing A] (t : A) : IsArtinianRing (A ⧸ It t) := inferInstance

def res₀ (resA : A →+* ResidueField O) (t : A) (htm : t ∈ RingHom.ker resA) :
    A ⧸ It t →+* ResidueField O :=
  Ideal.Quotient.lift (It t) resA (fun a ha => res_eq_zero_of_mem resA t htm a ha)

theorem res₀_comp (resA : A →+* ResidueField O) (t : A) (htm : t ∈ RingHom.ker resA) :
    (res₀ resA t htm).comp (qt (O := O) t).toRingHom = resA :=
  RingHom.ext fun _ => rfl

theorem res₀_qt (resA : A →+* ResidueField O) (t : A) (htm : t ∈ RingHom.ker resA) (a : A) :
    res₀ resA t htm (qt (O := O) t a) = resA a := rfl

theorem res₀_surjective (resA : A →+* ResidueField O) (hsA : Function.Surjective resA) (t : A)
    (htm : t ∈ RingHom.ker resA) : Function.Surjective (res₀ resA t htm) := fun c => by
  obtain ⟨a, rfl⟩ := hsA c
  exact ⟨qt (O := O) t a, rfl⟩

theorem res₀_compat (resA : A →+* ResidueField O) (hcA : resA.comp (algebraMap O A) = residue O) (t : A)
    (htm : t ∈ RingHom.ker resA) : (res₀ resA t htm).comp (algebraMap O (A ⧸ It t)) = residue O := by
  rw [← hcA]; rfl

abbrev Bt (t : A) : Subalgebra O (A × A) :=
  AlgHom.equalizer ((qt t).comp (AlgHom.fst O A A)) ((qt t).comp (AlgHom.snd O A A))

abbrev π₁ (t : A) : ↥(Bt (O := O) t) →ₐ[O] A := (AlgHom.fst O A A).comp (Bt t).val
abbrev π₂ (t : A) : ↥(Bt (O := O) t) →ₐ[O] A := (AlgHom.snd O A A).comp (Bt t).val

theorem π₁_apply (t : A) (b : ↥(Bt (O := O) t)) : π₁ t b = (b : A × A).1 := rfl

theorem π₂_apply (t : A) (b : ↥(Bt (O := O) t)) : π₂ t b = (b : A × A).2 := rfl

theorem mem_Bt (t : A) (x : A × A) : x ∈ Bt (O := O) t ↔ qt (O := O) t x.1 = qt (O := O) t x.2 :=
  Iff.rfl

theorem diff_mem (t : A) (b : ↥(Bt (O := O) t)) : (b : A × A).2 - (b : A × A).1 ∈ Ideal.span {t} :=
  (qt_eq_iff t _ _).1 ((mem_Bt t _).1 b.2).symm

abbrev resB (resA : A →+* ResidueField O) (t : A) : ↥(Bt (O := O) t) →+* ResidueField O :=
  resA.comp (π₁ t).toRingHom

theorem obj_Bt [IsLocalRing A] [IsArtinianRing A] (resA : A →+* ResidueField O)
    (hcA : resA.comp (algebraMap O A) = residue O) (t : A) (htm : t ∈ RingHom.ker resA) :
    IsLocalRing ↥(Bt (O := O) t) ∧ IsArtinianRing ↥(Bt (O := O) t) ∧
      Function.Surjective (resB (O := O) resA t) :=
  haveI := isLocalRing_quot resA t htm
  IsLocalRing.isLocalRing_and_isArtinianRing_equalizer_of_comp_algebraMap_eq_residue O A resA hcA A resA
    hcA (A ⧸ It t) (res₀ resA t htm) (qt t) (res₀_comp resA t htm) (qt t) (res₀_comp resA t htm)

theorem resB_compat (resA : A →+* ResidueField O) (hcA : resA.comp (algebraMap O A) = residue O)
    (t : A) : (resB (O := O) resA t).comp (algebraMap O ↥(Bt (O := O) t)) = residue O := by
  rw [← hcA]; rfl

theorem hπ₁ (resA : A →+* ResidueField O) (t : A) : resA.comp (π₁ (O := O) t).toRingHom = resB resA t :=
  rfl

theorem res_snd_eq (resA : A →+* ResidueField O) (t : A) (htm : t ∈ RingHom.ker resA)
    (b : ↥(Bt (O := O) t)) : resA (b : A × A).2 = resA (b : A × A).1 := by
  rw [← sub_eq_zero, ← map_sub]
  exact res_eq_zero_of_mem resA t htm _ (diff_mem t b)

theorem hπ₂ (resA : A →+* ResidueField O) (t : A) (htm : t ∈ RingHom.ker resA) :
    resA.comp (π₂ (O := O) t).toRingHom = resB resA t :=
  RingHom.ext fun b => res_snd_eq resA t htm b

theorem comm₁ (t : A) : (qt (O := O) t).comp (π₁ t) = (qt t).comp (π₂ t) :=
  AlgHom.ext fun b => (mem_Bt t _).1 b.2

theorem cart₁ (t : A) (a' a'' : A) (h : qt (O := O) t a' = qt (O := O) t a'') :
    ∃! b : ↥(Bt (O := O) t), π₁ t b = a' ∧ π₂ t b = a'' := by
  refine ⟨⟨(a', a''), h⟩, ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨⟨b₁, b₂⟩, hb⟩ ⟨rfl, rfl⟩
  rfl

def coef (t : A) (b : ↥(Bt (O := O) t)) : A :=
  (Ideal.mem_span_singleton'.1 (diff_mem t b)).choose

theorem coef_spec (t : A) (b : ↥(Bt (O := O) t)) : coef t b * t = (b : A × A).2 - (b : A × A).1 :=
  (Ideal.mem_span_singleton'.1 (diff_mem t b)).choose_spec

theorem res_eq_zero_of_mul_eq_zero [IsLocalRing A] [IsArtinianRing A] (resA : A →+* ResidueField O)
    (t : A) (ht0 : t ≠ 0) (c : A) (hc : c * t = 0) : resA c = 0 := by
  by_contra h
  have hu : IsUnit c := (isUnit_iff_res_ne_zero resA c).2 h
  apply ht0
  have h2 := congrArg (fun x => (↑hu.unit⁻¹ : A) * x) hc
  simp only [mul_zero] at h2
  rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at h2

def lam (resA : A →+* ResidueField O) (t : A) (b : ↥(Bt (O := O) t)) : ResidueField O :=
  resA (coef t b)

theorem lam_eq_of [IsLocalRing A] [IsArtinianRing A] (resA : A →+* ResidueField O) (t : A) (ht0 : t ≠ 0)
    (b : ↥(Bt (O := O) t)) (c : A) (hc : c * t = (b : A × A).2 - (b : A × A).1) :
    lam resA t b = resA c := by
  rw [lam, ← sub_eq_zero, ← map_sub]
  apply res_eq_zero_of_mul_eq_zero resA t ht0
  rw [sub_mul, hc, coef_spec, sub_self]

theorem mul_eq_of_lam_eq (resA : A →+* ResidueField O) (t : A) (hmt : ∀ m ∈ RingHom.ker resA, m * t = 0)
    (b : ↥(Bt (O := O) t)) (c : A) (hc : resA c = lam resA t b) :
    c * t = (b : A × A).2 - (b : A × A).1 := by
  rw [← coef_spec t b, ← sub_eq_zero, ← sub_mul]
  apply hmt
  rw [RingHom.mem_ker, map_sub, hc, lam, sub_self]

def τ [IsLocalRing A] [IsArtinianRing A] (resA : A →+* ResidueField O)
    (hcA : resA.comp (algebraMap O A) = residue O) (t : A) (ht0 : t ≠ 0) (htm : t ∈ RingHom.ker resA) :
    ↥(Bt (O := O) t) →ₐ[O] DualNumber (ResidueField O) where
  toFun b := ((resA (b : A × A).1, lam resA t b) : ResidueField O × ResidueField O)
  map_one' := by
    refine TrivSqZeroExt.ext (by simp) ?_
    change lam resA t 1 = 0
    rw [lam_eq_of resA t ht0 1 0 (by simp), map_zero]
  map_mul' b b' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · change resA ((b : A × A) * (b' : A × A)).1 = resA (b : A × A).1 * resA (b' : A × A).1
      rw [Prod.fst_mul, map_mul]
    · change lam resA t (b * b') = resA (b : A × A).1 • lam resA t b' +
        MulOpposite.op (resA (b' : A × A).1) • lam resA t b
      rw [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
        lam_eq_of resA t ht0 (b * b') ((b : A × A).1 * coef t b' + coef t b * (b' : A × A).2) ?_]
      · rw [map_add, map_mul, map_mul, res_snd_eq resA t htm b']
        rfl
      · change _ = ((b : A × A) * (b' : A × A)).2 - ((b : A × A) * (b' : A × A)).1
        rw [Prod.snd_mul, Prod.fst_mul, add_mul, mul_assoc, coef_spec, mul_assoc, mul_comm _ t,
          ← mul_assoc, coef_spec]
        ring
  map_zero' := by
    refine TrivSqZeroExt.ext (by simp) ?_
    change lam resA t 0 = 0
    rw [lam_eq_of resA t ht0 0 0 (by simp), map_zero]
  map_add' b b' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · change resA ((b : A × A) + (b' : A × A)).1 = resA (b : A × A).1 + resA (b' : A × A).1
      rw [Prod.fst_add, map_add]
    · change lam resA t (b + b') = lam resA t b + lam resA t b'
      rw [lam_eq_of resA t ht0 (b + b') (coef t b + coef t b') ?_, map_add]
      · rfl
      · change _ = ((b : A × A) + (b' : A × A)).2 - ((b : A × A) + (b' : A × A)).1
        rw [Prod.snd_add, Prod.fst_add, add_mul, coef_spec, coef_spec]
        ring
  commutes' o := by
    refine TrivSqZeroExt.ext ?_ ?_
    · change resA (algebraMap O (A × A) o).1 = TrivSqZeroExt.fst (algebraMap O (DualNumber _) o)
      rw [Prod.algebraMap_apply, ← RingHom.comp_apply, hcA]
      rfl
    · change lam resA t (algebraMap O _ o) = TrivSqZeroExt.snd (algebraMap O (DualNumber _) o)
      rw [lam_eq_of resA t ht0 _ 0 ?_, map_zero]
      · rfl
      · change (0 : A) * t = (algebraMap O (A × A) o).2 - (algebraMap O (A × A) o).1
        simp

theorem hτ [IsLocalRing A] [IsArtinianRing A] (resA : A →+* ResidueField O)
    (hcA : resA.comp (algebraMap O A) = residue O) (t : A) (ht0 : t ≠ 0) (htm : t ∈ RingHom.ker resA) :
    (resD O).comp (τ resA hcA t ht0 htm).toRingHom = resB resA t := rfl

theorem τ_fst [IsLocalRing A] [IsArtinianRing A] (resA : A →+* ResidueField O)
    (hcA : resA.comp (algebraMap O A) = residue O) (t : A) (ht0 : t ≠ 0) (htm : t ∈ RingHom.ker resA)
    (b : ↥(Bt (O := O) t)) : TrivSqZeroExt.fst (τ resA hcA t ht0 htm b) = resA (b : A × A).1 := rfl

theorem τ_snd [IsLocalRing A] [IsArtinianRing A] (resA : A →+* ResidueField O)
    (hcA : resA.comp (algebraMap O A) = residue O) (t : A) (ht0 : t ≠ 0) (htm : t ∈ RingHom.ker resA)
    (b : ↥(Bt (O := O) t)) : TrivSqZeroExt.snd (τ resA hcA t ht0 htm b) = lam resA t b := rfl

theorem comm₂ [IsLocalRing A] [IsArtinianRing A] (resA : A →+* ResidueField O)
    (hcA : resA.comp (algebraMap O A) = residue O) (t : A) (ht0 : t ≠ 0) (htm : t ∈ RingHom.ker resA) :
    (resAlgHom resA hcA).comp (π₁ t) =
      (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).comp (τ resA hcA t ht0 htm) :=
  AlgHom.ext fun _ => rfl

theorem cart₂ [IsLocalRing A] [IsArtinianRing A] (resA : A →+* ResidueField O)
    (hsA : Function.Surjective resA) (hcA : resA.comp (algebraMap O A) = residue O) (t : A) (ht0 : t ≠ 0)
    (htm : t ∈ RingHom.ker resA) (hmt : ∀ m ∈ RingHom.ker resA, m * t = 0)
    (a : A) (d : DualNumber (ResidueField O))
    (h : resAlgHom resA hcA a = TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O) d) :
    ∃! b : ↥(Bt (O := O) t), π₁ t b = a ∧ τ resA hcA t ht0 htm b = d := by
  obtain ⟨c, hc⟩ := hsA (TrivSqZeroExt.snd d)
  have hmem : (a, a + c * t) ∈ Bt (O := O) t := by
    rw [mem_Bt, qt_eq_iff]
    exact Ideal.mem_span_singleton'.2 ⟨-c, by ring⟩
  have hlam : lam resA t ⟨(a, a + c * t), hmem⟩ = TrivSqZeroExt.snd d := by
    rw [lam_eq_of resA t ht0 _ c (by simp), hc]
  refine ⟨⟨(a, a + c * t), hmem⟩, ⟨rfl, TrivSqZeroExt.ext h hlam⟩, ?_⟩
  rintro ⟨⟨b₁, b₂⟩, hb⟩ ⟨hb₁, hb₂⟩
  change b₁ = a at hb₁
  subst hb₁
  have h2 : c * t = b₂ - b₁ := by
    apply mul_eq_of_lam_eq resA t hmt ⟨(b₁, b₂), hb⟩ c
    rw [hc, ← hb₂]; rfl
  apply Subtype.ext
  change (b₁, b₂) = (b₁, b₁ + c * t)
  rw [h2]; ext <;> simp

end pullback

theorem comp_compat {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA) (u : R →ₐ[O] A)
    (hu : resA.comp u.toRingHom = S.resR) : resA'.comp (f.comp u).toRingHom = S.resR := by
  rw [← hu, ← hf]; rfl

theorem Fmap_gf_id {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
    {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
    (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA) (g : A' →ₐ[O] A)
    (hg : resA.comp g.toRingHom = resA') (hgf : g.comp f = AlgHom.id O A) (z : S.F A resA) :
    S.Frel (S.Fmap g hg (S.Fmap f hf z)) z := by
  have hc : resA.comp (g.comp f).toRingHom = resA := by rw [hgf]; rfl
  have h1 := S.Fmap_comp f g hf hg hc z
  have h2 : S.Frel (S.Fmap (g.comp f) hc z) z := by
    rw [S.Fmap_congr (g.comp f) (AlgHom.id O A) hc rfl hgf z]
    exact S.Fmap_id rfl z
  exact S.htrans _ _ _ (S.hsymm _ _ h1) h2

structure SmallExt (O : Type u) [CommRing O] [IsLocalRing O] (A : Type u) [CommRing A] [Algebra O A]
    where
  resA : A →+* ResidueField O
  hsA : Function.Surjective resA
  hcA : resA.comp (algebraMap O A) = residue O
  t : A
  ht0 : t ≠ 0
  htm : t ∈ RingHom.ker resA
  hmt : ∀ m ∈ RingHom.ker resA, m * t = 0

section step

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A] (E : SmallExt O A)

abbrev ΞA (u : R →ₐ[O] A) (hu : E.resA.comp u.toRingHom = S.resR) : S.F A E.resA :=
  S.Ξ A ‹_› ‹_› E.resA E.hsA E.hcA u hu

abbrev Ξ₀ (u : R →ₐ[O] A ⧸ It E.t) (hu : (res₀ E.resA E.t E.htm).comp u.toRingHom = S.resR) :
    S.F (A ⧸ It E.t) (res₀ E.resA E.t E.htm) :=
  S.Ξ (A ⧸ It E.t) (isLocalRing_quot E.resA E.t E.htm) (isArtinianRing_quot E.t) (res₀ E.resA E.t E.htm)
    (res₀_surjective E.resA E.hsA E.t E.htm) (res₀_compat E.resA E.hcA E.t E.htm) u hu

abbrev ΞB (w : R →ₐ[O] ↥(Bt (O := O) E.t)) (hw : (resB E.resA E.t).comp w.toRingHom = S.resR) :
    S.F ↥(Bt (O := O) E.t) (resB E.resA E.t) :=
  S.Ξ ↥(Bt (O := O) E.t) (obj_Bt E.resA E.hcA E.t E.htm).1 (obj_Bt E.resA E.hcA E.t E.htm).2.1
    (resB E.resA E.t) (obj_Bt E.resA E.hcA E.t E.htm).2.2 (resB_compat E.resA E.hcA E.t) w hw

abbrev ΞD (θ : R →ₐ[O] DualNumber (ResidueField O)) (hθ : (resD O).comp θ.toRingHom = S.resR) :
    S.F (DualNumber (ResidueField O)) (resD O) :=
  S.Ξ (DualNumber (ResidueField O)) (hlD O) (haD O) (resD O) (hsD O) (hcD O) θ hθ

abbrev τE : ↥(Bt (O := O) E.t) →ₐ[O] DualNumber (ResidueField O) := τ E.resA E.hcA E.t E.ht0 E.htm

theorem hτE : (resD O).comp (τE E).toRingHom = resB E.resA E.t := rfl

def Inj : Prop :=
  ∀ (u u' : R →ₐ[O] A) (hu : E.resA.comp u.toRingHom = S.resR) (hu' : E.resA.comp u'.toRingHom = S.resR),
    S.Frel (ΞA S E u hu) (ΞA S E u' hu') → u = u'

def Surj : Prop :=
  ∀ x : S.F A E.resA, ∃ (u : R →ₐ[O] A) (hu : E.resA.comp u.toRingHom = S.resR), S.Frel (ΞA S E u hu) x

def Inj₀ : Prop :=
  ∀ (u u' : R →ₐ[O] A ⧸ It E.t) (hu : (res₀ E.resA E.t E.htm).comp u.toRingHom = S.resR)
    (hu' : (res₀ E.resA E.t E.htm).comp u'.toRingHom = S.resR),
    S.Frel (Ξ₀ S E u hu) (Ξ₀ S E u' hu') → u = u'

def Surj₀ : Prop :=
  ∀ x : S.F (A ⧸ It E.t) (res₀ E.resA E.t E.htm), ∃ (u : R →ₐ[O] A ⧸ It E.t)
    (hu : (res₀ E.resA E.t E.htm).comp u.toRingHom = S.resR), S.Frel (Ξ₀ S E u hu) x

theorem nat_qt (u : R →ₐ[O] A) (hu : E.resA.comp u.toRingHom = S.resR) :
    S.Frel (Ξ₀ S E ((qt E.t).comp u) (comp_compat S (qt E.t) (res₀_comp E.resA E.t E.htm) u hu))
      (S.Fmap (qt E.t) (res₀_comp E.resA E.t E.htm) (ΞA S E u hu)) :=
  S.Ξ_nat A ‹_› ‹_› E.resA E.hsA E.hcA (A ⧸ It E.t) (isLocalRing_quot E.resA E.t E.htm)
    (isArtinianRing_quot E.t) (res₀ E.resA E.t E.htm) (res₀_surjective E.resA E.hsA E.t E.htm)
    (res₀_compat E.resA E.hcA E.t E.htm) (qt E.t) (res₀_comp E.resA E.t E.htm) u hu _

theorem nat_π₁ (w : R →ₐ[O] ↥(Bt (O := O) E.t)) (hw : (resB E.resA E.t).comp w.toRingHom = S.resR) :
    S.Frel (ΞA S E ((π₁ E.t).comp w) (comp_compat S (π₁ E.t) (hπ₁ E.resA E.t) w hw))
      (S.Fmap (π₁ E.t) (hπ₁ E.resA E.t) (ΞB S E w hw)) :=
  S.Ξ_nat ↥(Bt (O := O) E.t) (obj_Bt E.resA E.hcA E.t E.htm).1 (obj_Bt E.resA E.hcA E.t E.htm).2.1
    (resB E.resA E.t) (obj_Bt E.resA E.hcA E.t E.htm).2.2 (resB_compat E.resA E.hcA E.t) A ‹_› ‹_› E.resA
    E.hsA E.hcA (π₁ E.t) (hπ₁ E.resA E.t) w hw _

theorem nat_π₂ (w : R →ₐ[O] ↥(Bt (O := O) E.t)) (hw : (resB E.resA E.t).comp w.toRingHom = S.resR) :
    S.Frel (ΞA S E ((π₂ E.t).comp w) (comp_compat S (π₂ E.t) (hπ₂ E.resA E.t E.htm) w hw))
      (S.Fmap (π₂ E.t) (hπ₂ E.resA E.t E.htm) (ΞB S E w hw)) :=
  S.Ξ_nat ↥(Bt (O := O) E.t) (obj_Bt E.resA E.hcA E.t E.htm).1 (obj_Bt E.resA E.hcA E.t E.htm).2.1
    (resB E.resA E.t) (obj_Bt E.resA E.hcA E.t E.htm).2.2 (resB_compat E.resA E.hcA E.t) A ‹_› ‹_› E.resA
    E.hsA E.hcA (π₂ E.t) (hπ₂ E.resA E.t E.htm) w hw _

theorem nat_τ (w : R →ₐ[O] ↥(Bt (O := O) E.t)) (hw : (resB E.resA E.t).comp w.toRingHom = S.resR) :
    S.Frel (ΞD S ((τE E).comp w) (comp_compat S (τE E) (hτE E) w hw))
      (S.Fmap (τE E) (hτE E) (ΞB S E w hw)) :=
  S.Ξ_nat ↥(Bt (O := O) E.t) (obj_Bt E.resA E.hcA E.t E.htm).1 (obj_Bt E.resA E.hcA E.t E.htm).2.1
    (resB E.resA E.t) (obj_Bt E.resA E.hcA E.t E.htm).2.2 (resB_compat E.resA E.hcA E.t)
    (DualNumber (ResidueField O)) (hlD O) (haD O) (resD O) (hsD O) (hcD O) (τE E) (hτE E) w hw _

theorem nat_qt' (u : R →ₐ[O] A) (hu : E.resA.comp u.toRingHom = S.resR) (v : R →ₐ[O] A ⧸ It E.t)
    (hv : (res₀ E.resA E.t E.htm).comp v.toRingHom = S.resR) (h : (qt E.t).comp u = v) :
    S.Frel (Ξ₀ S E v hv) (S.Fmap (qt E.t) (res₀_comp E.resA E.t E.htm) (ΞA S E u hu)) := by
  subst h; exact nat_qt S E u hu

theorem nat_π₁' (w : R →ₐ[O] ↥(Bt (O := O) E.t)) (hw : (resB E.resA E.t).comp w.toRingHom = S.resR)
    (u : R →ₐ[O] A) (hu : E.resA.comp u.toRingHom = S.resR) (h : (π₁ E.t).comp w = u) :
    S.Frel (ΞA S E u hu) (S.Fmap (π₁ E.t) (hπ₁ E.resA E.t) (ΞB S E w hw)) := by
  subst h; exact nat_π₁ S E w hw

theorem nat_π₂' (w : R →ₐ[O] ↥(Bt (O := O) E.t)) (hw : (resB E.resA E.t).comp w.toRingHom = S.resR)
    (u : R →ₐ[O] A) (hu : E.resA.comp u.toRingHom = S.resR) (h : (π₂ E.t).comp w = u) :
    S.Frel (ΞA S E u hu) (S.Fmap (π₂ E.t) (hπ₂ E.resA E.t E.htm) (ΞB S E w hw)) := by
  subst h; exact nat_π₂ S E w hw

theorem nat_τ' (w : R →ₐ[O] ↥(Bt (O := O) E.t)) (hw : (resB E.resA E.t).comp w.toRingHom = S.resR)
    (θ : R →ₐ[O] DualNumber (ResidueField O)) (hθ : (resD O).comp θ.toRingHom = S.resR)
    (h : (τE E).comp w = θ) :
    S.Frel (ΞD S θ hθ) (S.Fmap (τE E) (hτE E) (ΞB S E w hw)) := by
  subst h; exact nat_τ S E w hw

theorem glue₁ :
    (∀ (x' : S.F A E.resA) (x'' : S.F A E.resA),
        S.Frel (S.Fmap (qt E.t) (res₀_comp E.resA E.t E.htm) x')
          (S.Fmap (qt E.t) (res₀_comp E.resA E.t E.htm) x'') →
        ∃ y : S.F ↥(Bt (O := O) E.t) (resB E.resA E.t),
          S.Frel (S.Fmap (π₁ E.t) (hπ₁ E.resA E.t) y) x' ∧
            S.Frel (S.Fmap (π₂ E.t) (hπ₂ E.resA E.t E.htm) y) x'') ∧
    (∀ (y₁ y₂ : S.F ↥(Bt (O := O) E.t) (resB E.resA E.t)),
        S.Frel (S.Fmap (π₁ E.t) (hπ₁ E.resA E.t) y₁) (S.Fmap (π₁ E.t) (hπ₁ E.resA E.t) y₂) →
        S.Frel (S.Fmap (π₂ E.t) (hπ₂ E.resA E.t E.htm) y₁) (S.Fmap (π₂ E.t) (hπ₂ E.resA E.t E.htm) y₂) →
        S.Frel y₁ y₂) := by
  haveI := (obj_Bt (O := O) E.resA E.hcA E.t E.htm).1
  haveI := (obj_Bt (O := O) E.resA E.hcA E.t E.htm).2.1
  haveI := isLocalRing_quot (O := O) E.resA E.t E.htm
  exact S.hglue ↥(Bt (O := O) E.t) (resB E.resA E.t) (obj_Bt E.resA E.hcA E.t E.htm).2.2
    (resB_compat E.resA E.hcA E.t) A E.resA E.hsA E.hcA A E.resA E.hsA E.hcA (A ⧸ It E.t)
    (res₀ E.resA E.t E.htm) (res₀_surjective E.resA E.hsA E.t E.htm) (res₀_compat E.resA E.hcA E.t E.htm)
    (π₁ E.t) (hπ₁ E.resA E.t) (π₂ E.t) (hπ₂ E.resA E.t E.htm) (qt E.t) (res₀_comp E.resA E.t E.htm)
    (qt E.t) (res₀_comp E.resA E.t E.htm) (comm₁ E.t) (cart₁ E.t) (qt_surjective E.t)

theorem glue₂ :
    ∀ (y₁ y₂ : S.F ↥(Bt (O := O) E.t) (resB E.resA E.t)),
      S.Frel (S.Fmap (π₁ E.t) (hπ₁ E.resA E.t) y₁) (S.Fmap (π₁ E.t) (hπ₁ E.resA E.t) y₂) →
      S.Frel (S.Fmap (τE E) (hτE E) y₁) (S.Fmap (τE E) (hτE E) y₂) → S.Frel y₁ y₂ := by
  haveI := (obj_Bt (O := O) E.resA E.hcA E.t E.htm).1
  haveI := (obj_Bt (O := O) E.resA E.hcA E.t E.htm).2.1
  haveI := haD O
  exact (S.hglue ↥(Bt (O := O) E.t) (resB E.resA E.t) (obj_Bt E.resA E.hcA E.t E.htm).2.2
    (resB_compat E.resA E.hcA E.t) A E.resA E.hsA E.hcA (DualNumber (ResidueField O)) (resD O) (hsD O)
    (hcD O) (ResidueField O) (RingHom.id _) Function.surjective_id rfl
    (π₁ E.t) (hπ₁ E.resA E.t) (τE E) (hτE E)
    (resAlgHom E.resA E.hcA) rfl (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)) rfl
    (comm₂ E.resA E.hcA E.t E.ht0 E.htm) (cart₂ E.resA E.hsA E.hcA E.t E.ht0 E.htm E.hmt) (hsD O)).2

theorem inj_step (ih : Inj₀ S E) : Inj S E := by
  intro u₁ u₂ hu₁ hu₂ hrel

  have hq₁ := comp_compat S (qt E.t) (res₀_comp E.resA E.t E.htm) u₁ hu₁
  have hq₂ := comp_compat S (qt E.t) (res₀_comp E.resA E.t E.htm) u₂ hu₂
  have h1 : (qt E.t).comp u₁ = (qt E.t).comp u₂ := by
    refine ih _ _ hq₁ hq₂ ?_
    have n1 := nat_qt S E u₁ hu₁
    have n2 := nat_qt S E u₂ hu₂
    have m := S.Fmap_rel (qt E.t) (res₀_comp E.resA E.t E.htm) _ _ hrel
    exact S.htrans _ _ _ n1 (S.htrans _ _ _ m (S.hsymm _ _ n2))

  obtain ⟨w, hw1, hw2⟩ := exists_lift (π₁ E.t) (π₂ E.t) (qt E.t) (qt E.t) (comm₁ E.t) (cart₁ E.t) u₁ u₂ h1
  obtain ⟨w₀, hw01, hw02⟩ :=
    exists_lift (π₁ E.t) (π₂ E.t) (qt E.t) (qt E.t) (comm₁ E.t) (cart₁ E.t) u₁ u₁ rfl
  have hw : (resB E.resA E.t).comp w.toRingHom = S.resR := by
    change E.resA.comp ((π₁ E.t).comp w).toRingHom = S.resR; rw [hw1]; exact hu₁
  have hw₀ : (resB E.resA E.t).comp w₀.toRingHom = S.resR := by
    change E.resA.comp ((π₁ E.t).comp w₀).toRingHom = S.resR; rw [hw01]; exact hu₁

  have key : S.Frel (ΞB S E w hw) (ΞB S E w₀ hw₀) := by
    refine (glue₁ S E).2 _ _ ?_ ?_
    · have a1 := nat_π₁' S E w hw u₁ hu₁ hw1
      have a2 := nat_π₁' S E w₀ hw₀ u₁ hu₁ hw01
      exact S.htrans _ _ _ (S.hsymm _ _ a1) a2
    · have a1 := nat_π₂' S E w hw u₂ hu₂ hw2
      have a2 := nat_π₂' S E w₀ hw₀ u₁ hu₁ hw02
      exact S.htrans _ _ _ (S.hsymm _ _ a1) (S.htrans _ _ _ (S.hsymm _ _ hrel) a2)

  have hτw := comp_compat S (τE E) (hτE E) w hw
  have hτw₀ := comp_compat S (τE E) (hτE E) w₀ hw₀
  have h4 : (τE E).comp w = (τE E).comp w₀ := by
    refine S.Ξ_inj (hlD O) (haD O) (hsD O) (hcD O) _ _ hτw hτw₀ ?_
    have b1 := nat_τ S E w hw
    have b2 := nat_τ S E w₀ hw₀
    have m := S.Fmap_rel (τE E) (hτE E) _ _ key
    exact S.htrans _ _ _ b1 (S.htrans _ _ _ m (S.hsymm _ _ b2))

  have h5 : w = w₀ :=
    lift_unique (π₁ E.t) (τE E) (resAlgHom E.resA E.hcA)
      (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)) (comm₂ E.resA E.hcA E.t E.ht0 E.htm)
      (cart₂ E.resA E.hsA E.hcA E.t E.ht0 E.htm E.hmt) w w₀ (by rw [hw1, hw01]) h4
  rw [← hw2, h5, hw02]

theorem surj_step (ih : Surj₀ S E) : Surj S E := by
  intro x'

  obtain ⟨u, hu, hux⟩ := ih (S.Fmap (qt E.t) (res₀_comp E.resA E.t E.htm) x')
  obtain ⟨u', hu'⟩ := S.Ξ_lift A ‹_› ‹_› E.resA E.hsA E.hcA (A ⧸ It E.t)
    (isLocalRing_quot E.resA E.t E.htm) (isArtinianRing_quot E.t) (res₀ E.resA E.t E.htm)
    (res₀_surjective E.resA E.hsA E.t E.htm) (res₀_compat E.resA E.hcA E.t E.htm) (qt E.t)
    (res₀_comp E.resA E.t E.htm) (qt_surjective E.t) E.t E.ht0 E.htm E.hmt (qt_eq_zero_iff E.t) u hu x'
    (S.hsymm _ _ hux)
  have hcu' : E.resA.comp u'.toRingHom = S.resR := by
    rw [← res₀_comp (O := O) E.resA E.t E.htm]
    change (res₀ E.resA E.t E.htm).comp ((qt E.t).comp u').toRingHom = S.resR
    rw [hu']; exact hu

  have hglue : S.Frel (S.Fmap (qt E.t) (res₀_comp E.resA E.t E.htm) (ΞA S E u' hcu'))
      (S.Fmap (qt E.t) (res₀_comp E.resA E.t E.htm) x') := by
    have n := nat_qt' S E u' hcu' u hu hu'
    exact S.htrans _ _ _ (S.hsymm _ _ n) hux
  obtain ⟨ζ, hζ₁, hζ₂⟩ := (glue₁ S E).1 _ _ hglue

  obtain ⟨θ, hθ, hθζ⟩ := S.Ξ_surj (hlD O) (haD O) (hsD O) (hcD O) (S.Fmap (τE E) (hτE E) ζ)

  have hcomp : (resAlgHom E.resA E.hcA).comp u' =
      (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).comp θ := by
    apply AlgHom.ext; intro x
    change (E.resA.comp u'.toRingHom) x = ((resD O).comp θ.toRingHom) x
    rw [hcu', hθ]
  obtain ⟨w, hw1, hw2⟩ := exists_lift (π₁ E.t) (τE E) (resAlgHom E.resA E.hcA)
    (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)) (comm₂ E.resA E.hcA E.t E.ht0 E.htm)
    (cart₂ E.resA E.hsA E.hcA E.t E.ht0 E.htm E.hmt) u' θ hcomp
  have hw : (resB E.resA E.t).comp w.toRingHom = S.resR := by
    change E.resA.comp ((π₁ E.t).comp w).toRingHom = S.resR; rw [hw1]; exact hcu'

  have key : S.Frel (ΞB S E w hw) ζ := by
    refine glue₂ S E _ _ ?_ ?_
    · have a1 := nat_π₁' S E w hw u' hcu' hw1
      exact S.htrans _ _ _ (S.hsymm _ _ a1) (S.hsymm _ _ hζ₁)
    · have b1 := nat_τ' S E w hw θ hθ hw2
      exact S.htrans _ _ _ (S.hsymm _ _ b1) hθζ

  refine ⟨(π₂ E.t).comp w, comp_compat S (π₂ E.t) (hπ₂ E.resA E.t E.htm) w hw, ?_⟩
  have c1 := nat_π₂ S E w hw
  exact S.htrans _ _ _ c1 (S.htrans _ _ _ (S.Fmap_rel (π₂ E.t) (hπ₂ E.resA E.t E.htm) _ _ key) hζ₂)

end step

section base

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
  (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
  (hcA : resA.comp (algebraMap O A) = residue O)

include hsA in
theorem base_case (hm : maximalIdeal A = ⊥) :
    (∀ (u u' : R →ₐ[O] A) (hu : resA.comp u.toRingHom = S.resR) (hu' : resA.comp u'.toRingHom = S.resR),
        S.Frel (S.Ξ A ‹_› ‹_› resA hsA hcA u hu) (S.Ξ A ‹_› ‹_› resA hsA hcA u' hu') → u = u') ∧
    (∀ x : S.F A resA, ∃ (u : R →ₐ[O] A) (hu : resA.comp u.toRingHom = S.resR),
        S.Frel (S.Ξ A ‹_› ‹_› resA hsA hcA u hu) x) := by
  have hinj : Function.Injective resA := by
    rw [RingHom.injective_iff_ker_eq_bot, ker_res_eq_maximalIdeal, hm]
  refine ⟨fun u u' hu hu' _ => ?_, fun x => ?_⟩
  · apply AlgHom.ext; intro r
    apply hinj
    change (resA.comp u.toRingHom) r = (resA.comp u'.toRingHom) r
    rw [hu, hu']
  ·
    let e : A ≃+* ResidueField O := RingEquiv.ofBijective resA ⟨hinj, hsA⟩
    have he : ∀ a, e a = resA a := fun _ => rfl
    let g : ResidueField O →ₐ[O] A :=
      { e.symm.toRingHom with
        commutes' := fun o => by
          change e.symm (algebraMap O (ResidueField O) o) = algebraMap O A o
          apply e.injective
          rw [e.apply_symm_apply, he, ← RingHom.comp_apply, hcA]
          rfl }
    have hg : resA.comp g.toRingHom = RingHom.id _ := by
      ext c; change resA (e.symm c) = c; rw [← he, e.apply_symm_apply]
    let ρ : R →ₐ[O] ResidueField O :=
      { S.resR with
        commutes' := fun o => by
          change S.resR (algebraMap O R o) = _
          rw [← RingHom.comp_apply, S.hresR]; rfl }
    let u : R →ₐ[O] A := g.comp ρ
    have hu : resA.comp u.toRingHom = S.resR := by
      ext r; change resA (e.symm (S.resR r)) = S.resR r; rw [← he, e.apply_symm_apply]
    refine ⟨u, hu, ?_⟩

    let f : A →ₐ[O] ResidueField O := resAlgHom resA hcA
    have hf : (RingHom.id _).comp f.toRingHom = resA := rfl
    have hgf : g.comp f = AlgHom.id O A := by
      apply AlgHom.ext; intro a
      change e.symm (resA a) = a
      rw [← he, e.symm_apply_apply]
    have h1 : S.Frel (S.Fmap f hf (S.Ξ A ‹_› ‹_› resA hsA hcA u hu)) (S.Fmap f hf x) :=
      S.htrans _ _ _ (S.hx₀ _) (S.hsymm _ _ (S.hx₀ _))
    have h2 := S.Fmap_rel g hg _ _ h1
    exact S.htrans _ _ _ (S.hsymm _ _ (Fmap_gf_id S f hf g hg hgf _))
      (S.htrans _ _ _ h2 (Fmap_gf_id S f hf g hg hgf x))

end base

theorem exists_small (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (hm : maximalIdeal A ≠ ⊥) :
    ∃ t : A, t ≠ 0 ∧ t ∈ maximalIdeal A ∧ ∀ a ∈ maximalIdeal A, a * t = 0 := by
  classical
  have hex : ∃ N, maximalIdeal A ^ N = ⊥ := by
    obtain ⟨N, hN⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).1 ‹_›
    exact ⟨N, hN⟩
  have hM : maximalIdeal A ^ Nat.find hex = ⊥ := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, maximalIdeal A ^ j ≠ ⊥ := fun j hj => Nat.find_min hex hj
  have hM0 : Nat.find hex ≠ 0 := fun h => by
    rw [h, pow_zero, Ideal.one_eq_top] at hM; exact top_ne_bot hM
  have hM1 : Nat.find hex ≠ 1 := fun h => by rw [h, pow_one] at hM; exact hm hM
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 2 := ⟨Nat.find hex - 2, by omega⟩
  have hne : maximalIdeal A ^ (j + 1) ≠ ⊥ := hmin _ (by omega)
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨t, ht0, Ideal.pow_le_self (Nat.succ_ne_zero j) ht, fun a ha => ?_⟩
  have hat : a * t ∈ maximalIdeal A ^ (j + 2) := by
    rw [pow_succ']; exact Ideal.mul_mem_mul ha ht
  rw [← hj, hM] at hat
  exact hat

theorem bij_of_length (n : ℕ) :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
      (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
      (hcA : resA.comp (algebraMap O A) = residue O), Module.length A A = n →
    (∀ (u u' : R →ₐ[O] A) (hu : resA.comp u.toRingHom = S.resR) (hu' : resA.comp u'.toRingHom = S.resR),
        S.Frel (S.Ξ A ‹_› ‹_› resA hsA hcA u hu) (S.Ξ A ‹_› ‹_› resA hsA hcA u' hu') → u = u') ∧
    (∀ x : S.F A resA, ∃ (u : R →ₐ[O] A) (hu : resA.comp u.toRingHom = S.resR),
        S.Frel (S.Ξ A ‹_› ‹_› resA hsA hcA u hu) x) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ _ _ resA hsA hcA hn
  by_cases hm : maximalIdeal A = ⊥
  · exact base_case S resA hsA hcA hm
  obtain ⟨t, ht0, htm', hmt'⟩ := exists_small A hm
  have htm : t ∈ RingHom.ker resA := by rw [ker_res_eq_maximalIdeal]; exact htm'
  have hmt : ∀ a ∈ RingHom.ker resA, a * t = 0 := by rw [ker_res_eq_maximalIdeal]; exact hmt'
  let E : SmallExt O A := ⟨resA, hsA, hcA, t, ht0, htm, hmt⟩

  haveI := isLocalRing_quot (O := O) resA t htm
  have hI : (It t : Ideal A) ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]; exact ht0
  have hlt : Module.length A (A ⧸ It t) < Module.length A A := Submodule.length_quotient_lt _ hI
  have heq : Module.length A (A ⧸ It t) = Module.length (A ⧸ It t) (A ⧸ It t) :=
    Module.length_eq_of_surjective (S := A) (R := A ⧸ It t) Ideal.Quotient.mk_surjective
  obtain ⟨n₀, hn₀⟩ := ENat.ne_top_iff_exists.1 (Module.length_ne_top (R := A ⧸ It t) (M := A ⧸ It t))
  have hlt' : n₀ < n := by
    rw [heq, ← hn₀, hn] at hlt
    exact_mod_cast hlt
  have ih₀ := ih n₀ hlt' (A ⧸ It t) (res₀ resA t htm) (res₀_surjective resA hsA t htm)
    (res₀_compat resA hcA t htm) hn₀.symm
  exact ⟨inj_step S E ih₀.1, surj_step S E ih₀.2⟩

theorem bij (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
    (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
    (hcA : resA.comp (algebraMap O A) = residue O) :
    (∀ (u u' : R →ₐ[O] A) (hu : resA.comp u.toRingHom = S.resR) (hu' : resA.comp u'.toRingHom = S.resR),
        S.Frel (S.Ξ A ‹_› ‹_› resA hsA hcA u hu) (S.Ξ A ‹_› ‹_› resA hsA hcA u' hu') → u = u') ∧
    (∀ x : S.F A resA, ∃ (u : R →ₐ[O] A) (hu : resA.comp u.toRingHom = S.resR),
        S.Frel (S.Ξ A ‹_› ‹_› resA hsA hcA u hu) x) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (Module.length_ne_top (R := A) (M := A))
  exact bij_of_length S n A resA hsA hcA hn.symm

def β (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
    (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
    (hcA : resA.comp (algebraMap O A) = residue O) (x : S.F A resA) : R →ₐ[O] A :=
  ((bij S A resA hsA hcA).2 x).choose

theorem β_compat (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
    (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
    (hcA : resA.comp (algebraMap O A) = residue O) (x : S.F A resA) :
    resA.comp (β S A resA hsA hcA x).toRingHom = S.resR :=
  ((bij S A resA hsA hcA).2 x).choose_spec.choose

theorem β_spec (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
    (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
    (hcA : resA.comp (algebraMap O A) = residue O) (x : S.F A resA) :
    S.Frel (S.Ξ A ‹_› ‹_› resA hsA hcA (β S A resA hsA hcA x) (β_compat S A resA hsA hcA x)) x :=
  ((bij S A resA hsA hcA).2 x).choose_spec.choose_spec

theorem β_unique (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
    (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
    (hcA : resA.comp (algebraMap O A) = residue O) (x : S.F A resA) (u : R →ₐ[O] A)
    (hu : resA.comp u.toRingHom = S.resR) (h : S.Frel (S.Ξ A ‹_› ‹_› resA hsA hcA u hu) x) :
    β S A resA hsA hcA x = u :=
  (bij S A resA hsA hcA).1 _ _ _ _ (S.htrans _ _ _ (β_spec S A resA hsA hcA x) (S.hsymm _ _ h))

end Hull
p2m_reactivate "P2MW.S_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_hull.P2mSchlessingerUniversal.Hull"

end P2mSchlessingerUniversal
p2m_reactivate "P2MW.S_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_hull.P2mSchlessingerUniversal.Hull P2MW.S_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_hull.P2mSchlessingerUniversal"

open IsLocalRing in
theorem solution
    (O : Type u) [CommRing O] [IsLocalRing O]
    (F : ∀ (A : Type u) [CommRing A] [Algebra O A], (A →+* ResidueField O) → Type u)
    (Frel : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O},
      F A resA → F A resA → Prop)
    (hrefl : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (x : F A resA), Frel x x)
    (hsymm : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (x y : F A resA), Frel x y → Frel y x)
    (htrans : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (x y z : F A resA), Frel x y → Frel y z → Frel x z)
    (Fmap : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
      (f : A →ₐ[O] A'), resA'.comp f.toRingHom = resA → F A resA → F A' resA')
    (Fmap_rel : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
      (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA) (x y : F A resA),
      Frel x y → Frel (Fmap f hf x) (Fmap f hf y))
    (Fmap_id : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      (h : resA.comp (AlgHom.id O A).toRingHom = resA) (x : F A resA), Frel (Fmap (AlgHom.id O A) h x) x)
    (Fmap_comp : ∀ {A : Type u} [CommRing A] [Algebra O A] {resA : A →+* ResidueField O}
      {A' : Type u} [CommRing A'] [Algebra O A'] {resA' : A' →+* ResidueField O}
      {A'' : Type u} [CommRing A''] [Algebra O A''] {resA'' : A'' →+* ResidueField O}
      (f : A →ₐ[O] A') (g : A' →ₐ[O] A'') (hf : resA'.comp f.toRingHom = resA)
      (hg : resA''.comp g.toRingHom = resA') (hgf : resA''.comp (g.comp f).toRingHom = resA)
      (x : F A resA), Frel (Fmap (g.comp f) hgf x) (Fmap g hg (Fmap f hf x)))

    (x₀ : F (ResidueField O) (RingHom.id (ResidueField O)))
    (hx₀ : ∀ x : F (ResidueField O) (RingHom.id (ResidueField O)), Frel x x₀)

    (hglue : ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [Algebra O B]
        (resB : B →+* ResidueField O), Function.Surjective resB →
        resB.comp (algebraMap O B) = residue O →
      ∀ (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
        (resA' : A' →+* ResidueField O), Function.Surjective resA' →
        resA'.comp (algebraMap O A') = residue O →
      ∀ (A'' : Type u) [CommRing A''] [IsLocalRing A''] [IsArtinianRing A''] [Algebra O A'']
        (resA'' : A'' →+* ResidueField O), Function.Surjective resA'' →
        resA''.comp (algebraMap O A'') = residue O →
      ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O →
      ∀ (p' : B →ₐ[O] A') (hp' : resA'.comp p'.toRingHom = resB)
        (p'' : B →ₐ[O] A'') (hp'' : resA''.comp p''.toRingHom = resB)
        (q' : A' →ₐ[O] A) (hq' : resA.comp q'.toRingHom = resA')
        (q'' : A'' →ₐ[O] A) (hq'' : resA.comp q''.toRingHom = resA''),
        q'.comp p' = q''.comp p'' →
        (∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'') →
        Function.Surjective q'' →
        (∀ (x' : F A' resA') (x'' : F A'' resA''), Frel (Fmap q' hq' x') (Fmap q'' hq'' x'') →
            ∃ y : F B resB, Frel (Fmap p' hp' y) x' ∧ Frel (Fmap p'' hp'' y) x'') ∧
        (∀ (y₁ y₂ : F B resB), Frel (Fmap p' hp' y₁) (Fmap p' hp' y₂) →
            Frel (Fmap p'' hp'' y₁) (Fmap p'' hp'' y₂) → Frel y₁ y₂))

    (R : Type u) [CommRing R] [Algebra O R] (resR : R →+* ResidueField O)
    (hresR : resR.comp (algebraMap O R) = residue O)
    (Ξ : ∀ (A : Type u) [CommRing A] [Algebra O A], IsLocalRing A → IsArtinianRing A →
      ∀ (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O →
      ∀ (u : R →ₐ[O] A), resA.comp u.toRingHom = resR → F A resA)

    (Ξ_nat : ∀ (A : Type u) [CommRing A] [Algebra O A] (hlA : IsLocalRing A) (haA : IsArtinianRing A)
        (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
        (hcA : resA.comp (algebraMap O A) = residue O)
        (A' : Type u) [CommRing A'] [Algebra O A'] (hlA' : IsLocalRing A') (haA' : IsArtinianRing A')
        (resA' : A' →+* ResidueField O) (hsA' : Function.Surjective resA')
        (hcA' : resA'.comp (algebraMap O A') = residue O)
        (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA)
        (u : R →ₐ[O] A) (hu : resA.comp u.toRingHom = resR)
        (hfu : resA'.comp (f.comp u).toRingHom = resR),
        Frel (Ξ A' hlA' haA' resA' hsA' hcA' (f.comp u) hfu) (Fmap f hf (Ξ A hlA haA resA hsA hcA u hu)))

    (Ξ_inj : ∀ (hl : IsLocalRing (DualNumber (ResidueField O)))
        (ha : IsArtinianRing (DualNumber (ResidueField O)))
        (hs : Function.Surjective (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom)
        (hc : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
          (algebraMap O (DualNumber (ResidueField O))) = residue O)
        (θ θ' : R →ₐ[O] DualNumber (ResidueField O))
        (hθ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ.toRingHom = resR)
        (hθ' : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ'.toRingHom =
          resR),
        Frel (Ξ _ hl ha _ hs hc θ hθ) (Ξ _ hl ha _ hs hc θ' hθ') → θ = θ')

    (Ξ_surj : ∀ (hl : IsLocalRing (DualNumber (ResidueField O)))
        (ha : IsArtinianRing (DualNumber (ResidueField O)))
        (hs : Function.Surjective (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom)
        (hc : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp
          (algebraMap O (DualNumber (ResidueField O))) = residue O)
        (x : F (DualNumber (ResidueField O))
          (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom),
        ∃ (θ : R →ₐ[O] DualNumber (ResidueField O))
          (hθ : (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).toRingHom.comp θ.toRingHom =
            resR), Frel (Ξ _ hl ha _ hs hc θ hθ) x)

    (Ξ_lift : ∀ (A' : Type u) [CommRing A'] [Algebra O A'] (hlA' : IsLocalRing A') (haA' : IsArtinianRing A')
        (resA' : A' →+* ResidueField O) (hsA' : Function.Surjective resA')
        (hcA' : resA'.comp (algebraMap O A') = residue O)
        (A : Type u) [CommRing A] [Algebra O A] (hlA : IsLocalRing A) (haA : IsArtinianRing A)
        (resA : A →+* ResidueField O) (hsA : Function.Surjective resA)
        (hcA : resA.comp (algebraMap O A) = residue O)
        (q : A' →ₐ[O] A) (hq : resA.comp q.toRingHom = resA'), Function.Surjective q →
        ∀ (t : A'), t ≠ 0 → t ∈ RingHom.ker resA' → (∀ m ∈ RingHom.ker resA', m * t = 0) →
        (∀ a : A', q a = 0 ↔ a ∈ Ideal.span {t}) →
        ∀ (u : R →ₐ[O] A) (hu : resA.comp u.toRingHom = resR) (η' : F A' resA'),
        Frel (Fmap q hq η') (Ξ A hlA haA resA hsA hcA u hu) → ∃ u' : R →ₐ[O] A', q.comp u' = u) :
    ∃
      (β : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O → F A resA → (R →ₐ[O] A)),
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O) (x : F A resA),
        resA.comp (β A resA hs hc x).toRingHom = resR) ∧
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O) (x y : F A resA),
        Frel x y → β A resA hs hc x = β A resA hs hc y) ∧
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O)
          (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
          (resA' : A' →+* ResidueField O) (hs' : Function.Surjective resA')
          (hc' : resA'.comp (algebraMap O A') = residue O)
          (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA) (x : F A resA),
        β A' resA' hs' hc' (Fmap f hf x) = f.comp (β A resA hs hc x)) ∧
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O) (x y : F A resA),
        β A resA hs hc x = β A resA hs hc y → Frel x y) ∧
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O) (χ : R →ₐ[O] A),
        resA.comp χ.toRingHom = resR → ∃ x : F A resA, β A resA hs hc x = χ) := by
  let S : P2mSchlessingerUniversal.Hull O R :=
    { F := F, Frel := Frel, hrefl := hrefl, hsymm := hsymm, htrans := htrans, Fmap := Fmap,
      Fmap_rel := Fmap_rel, Fmap_id := Fmap_id, Fmap_comp := Fmap_comp, x₀ := x₀, hx₀ := hx₀,
      hglue := hglue, resR := resR, hresR := hresR, Ξ := Ξ, Ξ_nat := Ξ_nat, Ξ_inj := Ξ_inj,
      Ξ_surj := Ξ_surj, Ξ_lift := Ξ_lift }
  refine ⟨fun A _ _ _ _ resA hs hc x => S.β A resA hs hc x, ?_, ?_, ?_, ?_, ?_⟩
  · intro A _ _ _ _ resA hs hc x
    exact S.β_compat A resA hs hc x
  · intro A _ _ _ _ resA hs hc x y hxy
    exact S.β_unique A resA hs hc x (S.β A resA hs hc y) (S.β_compat A resA hs hc y)
      (htrans _ _ _ (S.β_spec A resA hs hc y) (hsymm _ _ hxy))
  · intro A _ _ _ _ resA hs hc A' _ _ _ _ resA' hs' hc' f hf x
    refine S.β_unique A' resA' hs' hc' (Fmap f hf x) (f.comp (S.β A resA hs hc x))
      (S.comp_compat f hf _ (S.β_compat A resA hs hc x)) ?_
    exact htrans _ _ _ (Ξ_nat A ‹_› ‹_› resA hs hc A' ‹_› ‹_› resA' hs' hc' f hf (S.β A resA hs hc x)
      (S.β_compat A resA hs hc x) _) (Fmap_rel f hf _ _ (S.β_spec A resA hs hc x))
  · intro A _ _ _ _ resA hs hc x y h
    have h1 := S.β_spec A resA hs hc x
    have h2 := S.β_spec A resA hs hc y
    rw [S.Ξ_congr ‹_› ‹_› resA hs hc _ _ (S.β_compat A resA hs hc x) (S.β_compat A resA hs hc y) h]
      at h1
    exact htrans _ _ _ (hsymm _ _ h1) h2
  · intro A _ _ _ _ resA hs hc χ hχ
    exact ⟨S.Ξ A ‹_› ‹_› resA hs hc χ hχ, S.β_unique A resA hs hc _ χ hχ (hrefl _)⟩

end
end S_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_hull
end P2MW
export P2MW.S_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_hull (solution)
