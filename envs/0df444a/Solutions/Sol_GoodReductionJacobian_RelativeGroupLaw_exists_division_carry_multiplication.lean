-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_division_carry_multiplication
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:46.959805+00:00
-- url     : https://prove2.me/submissions/4aff54f0-8d01-4128-92a2-1d441af830b7

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_sigma_binary_operation
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_division_carry_lift

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

private theorem nsmul_eq_point_pow
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) :
    letI := L.pointCommGroup hc t
    L.nsmul t n x = x ^ n := by
  letI := L.pointCommGroup hc t
  induction n with
  | zero => rfl
  | succ n ih =>
      change L.nsmul t n x * x = x ^ (n + 1)
      rw [ih, pow_succ]

private theorem division_fibre_fst_over
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    pullback.fst (L.schemeNsmul n) S.1 ≫ f = pullback.snd (L.schemeNsmul n) S.1 := by
  calc
    pullback.fst (L.schemeNsmul n) S.1 ≫ f =
        pullback.fst (L.schemeNsmul n) S.1 ≫ L.schemeNsmul n ≫ f := by
          rw [L.schemeNsmul_over]
    _ = pullback.snd (L.schemeNsmul n) S.1 ≫ S.1 ≫ f := by
          rw [pullback.condition_assoc]
    _ = pullback.snd (L.schemeNsmul n) S.1 := by rw [S.2]; simp

private theorem division_fibre_point_pow
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n a : ℕ)
    (u : T ⟶ pullback (L.schemeNsmul n) (L.nsmul (𝟙 _) a S).1)
    (hu : u ≫ pullback.snd (L.schemeNsmul n) (L.nsmul (𝟙 _) a S).1 = t)
    (x : SchemeHomOver t f)
    (hx : x.1 = u ≫ pullback.fst (L.schemeNsmul n) (L.nsmul (𝟙 _) a S).1) :
    letI := L.pointCommGroup hc t
    x ^ n = (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S) ^ a := by
  letI := L.pointCommGroup hc t
  apply Subtype.ext
  rw [← nsmul_eq_point_pow L hc t n,
    L.coe_nsmul_eq_comp_schemeNsmul, hx, Category.assoc, pullback.condition,
    ← Category.assoc, hu]
  have h := congrArg Subtype.val
    (L.nsmul_natural (𝟙 _) t t (by simp) a S)
  rw [nsmul_eq_point_pow L hc t] at h
  exact h

/-- Multiplication with the integral carry is an actual morphism on the
finite coproduct of the 71 division fibres. Its component equations retain
the supplied relative group law. Group identities are a separate obligation. -/
theorem _root_.solution
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    let X : ZMod 71 → Scheme.{0} := fun a =>
      pullback (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    let g : ∀ a, X a ⟶ Spec (CommRingCat.of R) := fun a =>
      pullback.snd (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    ∃ μ : SchemeHomOver
        (pullback.fst (Sigma.desc g) (Sigma.desc g) ≫ Sigma.desc g) (Sigma.desc g),
      ∀ a b : ZMod 71,
        let t := pullback.fst (g a) (g b) ≫ g a
        letI := L.pointCommGroup hc t
        ∃ (x y : SchemeHomOver t f) (z : SchemeHomOver t (g (a + b))),
          x.1 = pullback.fst (g a) (g b) ≫
            pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1 ∧
          y.1 = pullback.snd (g a) (g b) ≫
            pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) b.val S).1 ∧
          pullback.map (g a) (g b) (Sigma.desc g) (Sigma.desc g)
              (Sigma.ι X a) (Sigma.ι X b) (𝟙 _) (by simp) (by simp) ≫ μ.1 =
            z.1 ≫ Sigma.ι X (a + b) ∧
          z.1 ≫ pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) (a + b).val S).1 =
            (x * y / (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S) ^
              ((a.val + b.val) / 71)).1 := by
  classical
  let X : ZMod 71 → Scheme.{0} := fun a =>
    pullback (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
  let g : ∀ a, X a ⟶ Spec (CommRingCat.of R) := fun a =>
    pullback.snd (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
  let t (a b : ZMod 71) := pullback.fst (g a) (g b) ≫ g a
  let x (a b : ZMod 71) : SchemeHomOver (t a b) f :=
    ⟨pullback.fst (g a) (g b) ≫
      pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1,
      by rw [Category.assoc, division_fibre_fst_over]⟩
  let y (a b : ZMod 71) : SchemeHomOver (t a b) f :=
    ⟨pullback.snd (g a) (g b) ≫
      pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) b.val S).1,
      by rw [Category.assoc, division_fibre_fst_over]; exact (pullback.condition (f := g a) (g := g b)).symm⟩
  have hxy (a b : ZMod 71) :
      letI := L.pointCommGroup hc (t a b)
      ∃ z : SchemeHomOver (t a b) (g (a + b)),
        z.1 ≫ pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) (a + b).val S).1 =
          (x a b * y a b /
            (GoodReductionJacobian.schemeHomOverComp (t a b) (Category.comp_id (t a b)) S) ^
              ((a.val + b.val) / 71)).1 := by
    letI := L.pointCommGroup hc (t a b)
    have hx := division_fibre_point_pow L hc S (t a b) 71 a.val
      (pullback.fst (g a) (g b)) rfl (x a b) rfl
    have hy := division_fibre_point_pow L hc S (t a b) 71 b.val
      (pullback.snd (g a) (g b)) (pullback.condition (f := g a) (g := g b)).symm (y a b) rfl
    dsimp only [g, X]
    rw [ZMod.val_add]
    exact L.division_carry_lift hc S (t a b) 71 a.val b.val (x a b) (y a b) hx hy
  choose z hz using hxy
  obtain ⟨μ, hμ⟩ := AlgebraicGeometry.Scheme.exists_sigma_binary_operation X g
    (fun a b => a + b) (fun a b => (z a b).1) (fun a b => (z a b).2)
  refine ⟨μ, fun a b => ⟨x a b, y a b, z a b, rfl, rfl, hμ a b, hz a b⟩⟩

end GoodReductionJacobian.RelativeGroupLaw
