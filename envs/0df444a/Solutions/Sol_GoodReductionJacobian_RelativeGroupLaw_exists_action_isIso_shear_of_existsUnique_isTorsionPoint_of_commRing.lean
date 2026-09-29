-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_action_isIso_shear_of_existsUnique_isTorsionPoint_of_commRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/b8144a81-8b46-53e1-b3ba-3c5fcbe47242

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_action_isIso_shear_of_existsUnique_isTorsionPoint_of_commRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace C6TorsorR

variable {K : Type u} [CommRing K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
  (L : RelativeGroupLaw K f)

theorem inv_natural {T T' : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (s' : T' ⟶ Spec (CommRingCat.of K))
    (ψ : T' ⟶ T) (hψ : ψ ≫ s = s') (x : SchemeHomOver s f) :
    schemeHomOverComp ψ hψ (L.inv s x) = L.inv s' (schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup s'
  apply eq_inv_of_mul_eq_one_left
  change L.mul s' (schemeHomOverComp ψ hψ (L.inv s x)) (schemeHomOverComp ψ hψ x) = L.one s'
  rw [← L.mul_natural s s' ψ hψ, L.inv_mul_cancel, L.one_natural s s' ψ hψ]

theorem nsmul_eq_pow {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : SchemeHomOver t f) :
    L.nsmul t n x = (letI := L.pointGroup t; x ^ n) := by
  letI := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [L.nsmul_succ, ih, pow_succ]; rfl

theorem nsmul_val {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : SchemeHomOver t f) :
    (L.nsmul t n x).1 = x.1 ≫ L.schemeNsmul n := by
  have h := L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x := Subtype.ext (Category.comp_id _)
  rw [hx] at h
  rw [← h]
  rfl

set_option maxHeartbeats 3200000 in
theorem main (hc : L.IsCommutative) (n : ℕ)
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (u : SchemeHomOver s f) (hu : L.IsTorsionPoint s n u)
    (huniv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (z : SchemeHomOver t f),
      L.IsTorsionPoint t n z → ∃! g : T ⟶ S, g ≫ u.1 = z.1) :
    ∃ (act : pullback f s ⟶ A),
      act ≫ f = pullback.fst f s ≫ f ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f) (g : T ⟶ S)
          (hx : x.1 ≫ f = g ≫ s),
        pullback.lift x.1 g hx ≫ act =
          (L.mul t x ⟨g ≫ u.1, by rw [Category.assoc, u.2, ← hx, x.2]⟩).1) ∧
      ∃ (hsh : pullback.fst f s ≫ L.schemeNsmul n = act ≫ L.schemeNsmul n),
        IsIso (pullback.lift (f := L.schemeNsmul n) (g := L.schemeNsmul n) (pullback.fst f s) act hsh) := by

  let tP : pullback f s ⟶ Spec (CommRingCat.of K) := pullback.fst f s ≫ f
  let U₁ : SchemeHomOver tP f := ⟨pullback.fst f s, rfl⟩
  let U₂ : SchemeHomOver tP f := ⟨pullback.snd f s ≫ u.1, by
    change (pullback.snd f s ≫ u.1) ≫ f = pullback.fst f s ≫ f
    rw [Category.assoc, u.2, pullback.condition]⟩
  have hU₂tors : L.IsTorsionPoint tP n U₂ :=
    L.isTorsionPoint_schemeHomOverComp s tP (pullback.snd f s) pullback.condition.symm n hu
  let act : pullback f s ⟶ A := (L.mul tP U₁ U₂).1

  have hpts : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f) (g : T ⟶ S)
      (hx : x.1 ≫ f = g ≫ s),
      pullback.lift x.1 g hx ≫ act = (L.mul t x ⟨g ≫ u.1, by rw [Category.assoc, u.2, ← hx, x.2]⟩).1 := by
    intro T t x g hx
    have hψ : pullback.lift x.1 g hx ≫ tP = t := by
      change pullback.lift x.1 g hx ≫ pullback.fst f s ≫ f = t
      rw [← Category.assoc, pullback.lift_fst, x.2]
    have h := congrArg Subtype.val (L.mul_natural tP t (pullback.lift x.1 g hx) hψ U₁ U₂)
    have h1 : schemeHomOverComp (pullback.lift x.1 g hx) hψ U₁ = x := Subtype.ext (pullback.lift_fst _ _ _)
    have h2 : schemeHomOverComp (pullback.lift x.1 g hx) hψ U₂ =
        ⟨g ≫ u.1, by rw [Category.assoc, u.2, ← hx, x.2]⟩ := by
      apply Subtype.ext
      change pullback.lift x.1 g hx ≫ pullback.snd f s ≫ u.1 = g ≫ u.1
      rw [← Category.assoc, pullback.lift_snd]
    rw [h1, h2] at h
    exact h

  have hpow : L.nsmul tP n (L.mul tP U₁ U₂) = L.nsmul tP n U₁ := by
    letI : CommGroup (SchemeHomOver tP f) := { L.pointGroup tP with mul_comm := hc tP }
    have e1 : L.nsmul tP n (L.mul tP U₁ U₂) = (L.mul tP U₁ U₂) ^ n := nsmul_eq_pow L tP n _
    have e2 : L.nsmul tP n U₁ = U₁ ^ n := nsmul_eq_pow L tP n _
    have e3 : L.nsmul tP n U₂ = U₂ ^ n := nsmul_eq_pow L tP n _
    have hU₂' : U₂ ^ n = 1 := by rw [← e3]; exact hU₂tors
    rw [e1, e2]
    change (U₁ * U₂) ^ n = U₁ ^ n
    rw [mul_pow, hU₂', mul_one]
  have hsh : pullback.fst f s ≫ L.schemeNsmul n = act ≫ L.schemeNsmul n := by
    change U₁.1 ≫ L.schemeNsmul n = (L.mul tP U₁ U₂).1 ≫ L.schemeNsmul n
    rw [← nsmul_val L, ← nsmul_val L, hpow]
  refine ⟨act, (L.mul tP U₁ U₂).2, hpts, hsh, ?_⟩

  let Q := pullback (L.schemeNsmul n) (L.schemeNsmul n)
  let tQ : Q ⟶ Spec (CommRingCat.of K) := pullback.fst (L.schemeNsmul n) (L.schemeNsmul n) ≫ f
  let V₁ : SchemeHomOver tQ f := ⟨pullback.fst _ _, rfl⟩
  have hV₂ : pullback.snd (L.schemeNsmul n) (L.schemeNsmul n) ≫ f = tQ := by
    calc pullback.snd (L.schemeNsmul n) (L.schemeNsmul n) ≫ f
        = pullback.snd (L.schemeNsmul n) (L.schemeNsmul n) ≫ (L.schemeNsmul n ≫ f) := by rw [L.schemeNsmul_over]
      _ = (pullback.snd (L.schemeNsmul n) (L.schemeNsmul n) ≫ L.schemeNsmul n) ≫ f := (Category.assoc _ _ _).symm
      _ = (pullback.fst (L.schemeNsmul n) (L.schemeNsmul n) ≫ L.schemeNsmul n) ≫ f := by rw [pullback.condition]
      _ = pullback.fst (L.schemeNsmul n) (L.schemeNsmul n) ≫ f := by rw [Category.assoc, L.schemeNsmul_over]
  let V₂ : SchemeHomOver tQ f := ⟨pullback.snd _ _, hV₂⟩
  let z : SchemeHomOver tQ f := L.mul tQ (L.inv tQ V₁) V₂
  have hz : L.IsTorsionPoint tQ n z := by
    letI : CommGroup (SchemeHomOver tQ f) := { L.pointGroup tQ with mul_comm := hc tQ }
    have hV : L.nsmul tQ n V₁ = L.nsmul tQ n V₂ := by
      apply Subtype.ext
      rw [nsmul_val L, nsmul_val L]
      exact pullback.condition
    change L.nsmul tQ n z = L.one tQ
    rw [nsmul_eq_pow L]
    change (V₁⁻¹ * V₂) ^ n = 1
    rw [mul_pow, inv_pow, ← nsmul_eq_pow L, ← nsmul_eq_pow L, hV]
    exact inv_mul_cancel _
  obtain ⟨g, hg, hguniq⟩ := huniv tQ z hz
  have hgs : g ≫ s = tQ := by rw [← u.2, ← Category.assoc, hg, z.2]
  let ι : Q ⟶ pullback f s := pullback.lift V₁.1 g (by rw [hgs])
  let sh := pullback.lift (f := L.schemeNsmul n) (g := L.schemeNsmul n) (pullback.fst f s) act hsh

  have hιtP : ι ≫ tP = tQ := by
    change ι ≫ pullback.fst f s ≫ f = pullback.fst _ _ ≫ f
    rw [← Category.assoc, pullback.lift_fst]
  have hι1 : schemeHomOverComp ι hιtP U₁ = V₁ := Subtype.ext (pullback.lift_fst _ _ _)
  have hι2 : schemeHomOverComp ι hιtP U₂ = z := by
    apply Subtype.ext
    change ι ≫ pullback.snd f s ≫ u.1 = z.1
    rw [← Category.assoc, pullback.lift_snd, hg]
  have hιact : ι ≫ act = V₂.1 := by
    have h := congrArg Subtype.val (L.mul_natural tP tQ ι hιtP U₁ U₂)
    rw [hι1, hι2] at h
    change ι ≫ act = (L.mul tQ V₁ (L.mul tQ (L.inv tQ V₁) V₂)).1 at h
    rw [h, ← L.mul_assoc, L.mul_inv_cancel, L.one_mul]
  have hιsh : ι ≫ sh = 𝟙 Q := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]; exact pullback.lift_fst _ _ _
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]; exact hιact

  have hshtQ : sh ≫ tQ = tP := by
    change sh ≫ pullback.fst _ _ ≫ f = pullback.fst f s ≫ f
    rw [← Category.assoc, pullback.lift_fst]
  have hsh1 : schemeHomOverComp sh hshtQ V₁ = U₁ := Subtype.ext (pullback.lift_fst _ _ _)
  have hsh2 : schemeHomOverComp sh hshtQ V₂ = L.mul tP U₁ U₂ := Subtype.ext (pullback.lift_snd _ _ _)
  have hshz : schemeHomOverComp sh hshtQ z = U₂ := by
    change schemeHomOverComp sh hshtQ (L.mul tQ (L.inv tQ V₁) V₂) = U₂
    rw [L.mul_natural, inv_natural L, hsh1, hsh2, ← L.mul_assoc, L.inv_mul_cancel, L.one_mul]
  have hshg : sh ≫ g = pullback.snd f s := by
    obtain ⟨g₀, -, huq⟩ := huniv tP U₂ hU₂tors
    have e1 : sh ≫ g = g₀ := huq _ (by
      show (sh ≫ g) ≫ u.1 = U₂.1
      rw [Category.assoc, hg]; exact congrArg Subtype.val hshz)
    have e2 : pullback.snd f s = g₀ := huq _ (show pullback.snd f s ≫ u.1 = U₂.1 from rfl)
    rw [e1, e2]
  have hshι : sh ≫ ι = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]; exact pullback.lift_fst _ _ _
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]; exact hshg
  exact ⟨ι, hshι, hιsh⟩

end C6TorsorR

theorem solution
    (R : Type u) [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (n : ℕ)
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver s f) (hu : L.IsTorsionPoint s n u)
    (huniv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (z : SchemeHomOver t f),
      L.IsTorsionPoint t n z → ∃! g : T ⟶ S, g ≫ u.1 = z.1) :
    ∃ (act : pullback f s ⟶ A),
      act ≫ f = pullback.fst f s ≫ f ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (g : T ⟶ S)
          (hx : x.1 ≫ f = g ≫ s),
        pullback.lift x.1 g hx ≫ act =
          (L.mul t x ⟨g ≫ u.1, by rw [Category.assoc, u.2, ← hx, x.2]⟩).1) ∧
      ∃ (hsh : pullback.fst f s ≫ L.schemeNsmul n = act ≫ L.schemeNsmul n),
        IsIso (pullback.lift (f := L.schemeNsmul n) (g := L.schemeNsmul n) (pullback.fst f s) act hsh) :=
  C6TorsorR.main L hc n s u hu huniv

end S_GoodReductionJacobian_RelativeGroupLaw_exists_action_isIso_shear_of_existsUnique_isTorsionPoint_of_commRing
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_action_isIso_shear_of_existsUnique_isTorsionPoint_of_commRing (solution)
