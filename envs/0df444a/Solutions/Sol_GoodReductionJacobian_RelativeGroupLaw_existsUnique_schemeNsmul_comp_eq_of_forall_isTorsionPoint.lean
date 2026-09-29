-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.existsUnique_schemeNsmul_comp_eq_of_forall_isTorsionPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/11f80dbe-c9b8-53f4-a319-37f866b2775d

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_JacJ1Iface
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_schemeNsmul_comp_eq_of_forall_isTorsionPoint

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace K4Sol

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem nsmul_eq_pow {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (x : SchemeHomOver t f) :
    letI := L.pointGroup t
    L.nsmul t n x = x ^ n := by
  letI := L.pointGroup t
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, L.nsmul_succ, ih]; rfl

theorem comp_schemeNsmul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (x : SchemeHomOver t f) :
    x.1 ≫ L.schemeNsmul n = (L.nsmul t n x).1 := by
  have h := L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint) = x := by
    apply Subtype.ext; rw [schemeHomOverComp_coe]; exact Category.comp_id _
  rw [hx] at h
  have := congrArg Subtype.val h
  rw [schemeHomOverComp_coe] at this
  exact this

end K4Sol

open K4Sol in

theorem K4_core
    (S : Type) [CommRing S]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative)
    (n : ℕ)
    [Flat (L.schemeNsmul n)] [Surjective (L.schemeNsmul n)] [QuasiCompact (L.schemeNsmul n)]
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of S)) (L' : RelativeGroupLaw S f')
    (F : A ⟶ A') (hF : F ≫ f' = f)
    (hFhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ F =
        (L'.mul t ⟨P.1 ≫ F, by rw [Category.assoc, hF]; exact P.2⟩
          ⟨Q.1 ≫ F, by rw [Category.assoc, hF]; exact Q.2⟩).1)
    (hFker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      L.IsTorsionPoint t n P → P.1 ≫ F = (L'.one t).1) :
    ∃ w : A ⟶ A', (L.schemeNsmul n ≫ w = F) ∧
      (∀ w' : A ⟶ A', L.schemeNsmul n ≫ w' = F → w' = w) ∧ w ≫ f' = f := by

  have key : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ A), g₁ ≫ L.schemeNsmul n = g₂ ≫ L.schemeNsmul n → g₁ ≫ F = g₂ ≫ F := by
    intro Z g₁ g₂ hg
    let t : Z ⟶ Spec (CommRingCat.of S) := g₁ ≫ f
    have ht2 : g₂ ≫ f = t := by
      show g₂ ≫ f = g₁ ≫ f
      rw [← L.schemeNsmul_over n, ← Category.assoc, ← hg, Category.assoc]
    let P : SchemeHomOver t f := ⟨g₁, rfl⟩
    let Q : SchemeHomOver t f := ⟨g₂, ht2⟩
    letI grp : CommGroup (SchemeHomOver t f) := { L.pointGroup t with mul_comm := fun a b => hc t a b }
    letI grp' := L'.pointGroup t

    let Φ : SchemeHomOver t f → SchemeHomOver t f' := fun R => ⟨R.1 ≫ F, by rw [Category.assoc, hF]; exact R.2⟩
    have hΦmul : ∀ R R' : SchemeHomOver t f, Φ (R * R') = Φ R * Φ R' := fun R R' => by
      apply Subtype.ext; exact hFhom t R R'
    let Φh : SchemeHomOver t f →* SchemeHomOver t f' := MonoidHom.mk' Φ hΦmul

    have hPQ : P ^ n = Q ^ n := by
      rw [← nsmul_eq_pow L t n P, ← nsmul_eq_pow L t n Q]
      apply Subtype.ext
      rw [← comp_schemeNsmul L t n P, ← comp_schemeNsmul L t n Q]
      exact hg

    have hD : L.IsTorsionPoint t n (P / Q) := by
      show L.nsmul t n (P / Q) = L.one t
      rw [nsmul_eq_pow L t n, div_pow, hPQ, div_self']
      rfl
    have hΦD : Φh (P / Q) = 1 := by
      apply Subtype.ext
      exact hFker t (P / Q) hD
    have : Φh P = Φh Q := by
      rw [← div_eq_one, ← map_div, hΦD]
    exact congrArg Subtype.val this
  refine ⟨EffectiveEpi.desc (L.schemeNsmul n) F key, EffectiveEpi.fac (L.schemeNsmul n) F key, ?_, ?_⟩
  · intro w' hw'
    exact EffectiveEpi.uniq (L.schemeNsmul n) F key w' hw'
  · rw [← cancel_epi (L.schemeNsmul n), ← Category.assoc, EffectiveEpi.fac, hF, L.schemeNsmul_over]

open K4Sol in

theorem K4_full
    (S : Type) [CommRing S]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative)
    (n : ℕ)
    [Flat (L.schemeNsmul n)] [Surjective (L.schemeNsmul n)] [QuasiCompact (L.schemeNsmul n)]
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of S)) (L' : RelativeGroupLaw S f')
    (F : A ⟶ A') (hF : F ≫ f' = f)
    (hFhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ F =
        (L'.mul t ⟨P.1 ≫ F, by rw [Category.assoc, hF]; exact P.2⟩
          ⟨Q.1 ≫ F, by rw [Category.assoc, hF]; exact Q.2⟩).1)
    (hFker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      L.IsTorsionPoint t n P → P.1 ≫ F = (L'.one t).1) :
    ∃ w : A ⟶ A', (L.schemeNsmul n ≫ w = F) ∧
      (∀ w' : A ⟶ A', L.schemeNsmul n ≫ w' = F → w' = w) ∧
      ∃ hw : w ≫ f' = f,
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
          (L.mul t P Q).1 ≫ w =
            (L'.mul t ⟨P.1 ≫ w, by rw [Category.assoc, hw]; exact P.2⟩
              ⟨Q.1 ≫ w, by rw [Category.assoc, hw]; exact Q.2⟩).1 := by
  obtain ⟨w, hwF, huniq, hw⟩ := K4_core S f L hc n f' L' F hF hFhom hFker
  refine ⟨w, hwF, huniq, hw, ?_⟩

  let π : pullback f f ⟶ Spec (CommRingCat.of S) := pullback.fst f f ≫ f
  let a : SchemeHomOver π f := ⟨pullback.fst f f, rfl⟩
  let b : SchemeHomOver π f := ⟨pullback.snd f f, pullback.condition.symm⟩
  letI grp : CommGroup (SchemeHomOver π f) := { L.pointGroup π with mul_comm := fun x y => hc π x y }
  letI grp' := L'.pointGroup π
  let Φ : SchemeHomOver π f → SchemeHomOver π f' := fun R => ⟨R.1 ≫ w, by rw [Category.assoc, hw]; exact R.2⟩

  let ν : pullback f f ⟶ pullback f f :=
    pullback.map f f f f (L.schemeNsmul n) (L.schemeNsmul n) (𝟙 _)
      ((Category.comp_id _).trans (L.schemeNsmul_over n).symm) ((Category.comp_id _).trans (L.schemeNsmul_over n).symm)
  have hν1 : ν ≫ pullback.fst f f = pullback.fst f f ≫ L.schemeNsmul n := pullback.lift_fst _ _ _
  have hν2 : ν ≫ pullback.snd f f = pullback.snd f f ≫ L.schemeNsmul n := pullback.lift_snd _ _ _
  have hνπ : ν ≫ π = π := by
    show ν ≫ (pullback.fst f f ≫ f) = pullback.fst f f ≫ f
    rw [← Category.assoc, hν1, Category.assoc, L.schemeNsmul_over]
  haveI : Flat ν := MorphismProperty.pullbackMap (P := @Flat) (inferInstance : Flat (L.schemeNsmul n))
    (inferInstance : Flat (L.schemeNsmul n)) (L.schemeNsmul_over n).symm (L.schemeNsmul_over n).symm
  haveI : Surjective ν := MorphismProperty.pullbackMap (P := @Surjective) (inferInstance : Surjective (L.schemeNsmul n))
    (inferInstance : Surjective (L.schemeNsmul n)) (L.schemeNsmul_over n).symm (L.schemeNsmul_over n).symm
  haveI : Epi ν := Flat.epi_of_flat_of_surjective ν

  have hca : schemeHomOverComp ν hνπ a = a ^ n := by
    apply Subtype.ext
    rw [schemeHomOverComp_coe, ← nsmul_eq_pow L π n a, ← comp_schemeNsmul L π n a]
    exact hν1
  have hcb : schemeHomOverComp ν hνπ b = b ^ n := by
    apply Subtype.ext
    rw [schemeHomOverComp_coe, ← nsmul_eq_pow L π n b, ← comp_schemeNsmul L π n b]
    exact hν2

  have m_eq : (L.mul π a b).1 ≫ w = (L'.mul π (Φ a) (Φ b)).1 := by
    rw [← cancel_epi ν]

    have l1 : ν ≫ (L.mul π a b).1 = ((a * b) ^ n : SchemeHomOver π f).1 := by
      have := congrArg Subtype.val (L.mul_natural π π ν hνπ a b)
      rw [schemeHomOverComp_coe, hca, hcb] at this
      rw [this, mul_pow]
      rfl
    have l2 : ((a * b) ^ n : SchemeHomOver π f).1 = (a * b : SchemeHomOver π f).1 ≫ L.schemeNsmul n := by
      rw [← nsmul_eq_pow L π n, comp_schemeNsmul L π n]

    have hΦa : schemeHomOverComp ν hνπ (Φ a) = ⟨(a : SchemeHomOver π f).1 ≫ F, by rw [Category.assoc, hF]⟩ := by
      apply Subtype.ext
      rw [schemeHomOverComp_coe]
      show ν ≫ pullback.fst f f ≫ w = pullback.fst f f ≫ F
      rw [← Category.assoc, hν1, Category.assoc, hwF]
    have hΦb : schemeHomOverComp ν hνπ (Φ b) = ⟨(b : SchemeHomOver π f).1 ≫ F, by rw [Category.assoc, hF]; exact b.2⟩ := by
      apply Subtype.ext
      rw [schemeHomOverComp_coe]
      show ν ≫ pullback.snd f f ≫ w = pullback.snd f f ≫ F
      rw [← Category.assoc, hν2, Category.assoc, hwF]
    have r1 := congrArg Subtype.val (L'.mul_natural π π ν hνπ (Φ a) (Φ b))
    rw [schemeHomOverComp_coe, hΦa, hΦb] at r1
    rw [← Category.assoc, l1, l2, Category.assoc, hwF, r1]
    exact hFhom π a b

  intro T t P Q
  let s : T ⟶ pullback f f := pullback.lift P.1 Q.1 (P.2.trans Q.2.symm)
  have hs : s ≫ π = t := by
    show s ≫ (pullback.fst f f ≫ f) = t
    rw [← Category.assoc, pullback.lift_fst]; exact P.2
  have hPa : schemeHomOverComp s hs a = P := by
    apply Subtype.ext; rw [schemeHomOverComp_coe]; exact pullback.lift_fst _ _ _
  have hQb : schemeHomOverComp s hs b = Q := by
    apply Subtype.ext; rw [schemeHomOverComp_coe]; exact pullback.lift_snd _ _ _
  have e1 := congrArg Subtype.val (L.mul_natural π t s hs a b)
  rw [schemeHomOverComp_coe, hPa, hQb] at e1
  have hPa' : schemeHomOverComp s hs (Φ a) = ⟨P.1 ≫ w, by rw [Category.assoc, hw]; exact P.2⟩ := by
    apply Subtype.ext; rw [schemeHomOverComp_coe]
    show s ≫ pullback.fst f f ≫ w = P.1 ≫ w
    rw [← Category.assoc, pullback.lift_fst]
  have hQb' : schemeHomOverComp s hs (Φ b) = ⟨Q.1 ≫ w, by rw [Category.assoc, hw]; exact Q.2⟩ := by
    apply Subtype.ext; rw [schemeHomOverComp_coe]
    show s ≫ pullback.snd f f ≫ w = Q.1 ≫ w
    rw [← Category.assoc, pullback.lift_snd]
  have e2 := congrArg Subtype.val (L'.mul_natural π t s hs (Φ a) (Φ b))
  rw [schemeHomOverComp_coe, hPa', hQb'] at e2
  rw [← e1, ← e2, Category.assoc, m_eq]

theorem solution
    (S : Type) [CommRing S]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative)
    (n : ℕ)
    [Flat (L.schemeNsmul n)] [Surjective (L.schemeNsmul n)] [QuasiCompact (L.schemeNsmul n)]
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of S)) (L' : RelativeGroupLaw S f')
    (F : A ⟶ A') (hF : F ≫ f' = f)
    (hFhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ F =
        (L'.mul t ⟨P.1 ≫ F, by rw [Category.assoc, hF]; exact P.2⟩
          ⟨Q.1 ≫ F, by rw [Category.assoc, hF]; exact Q.2⟩).1)
    (hFker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      L.IsTorsionPoint t n P → P.1 ≫ F = (L'.one t).1) :
    ∃ w : A ⟶ A', (L.schemeNsmul n ≫ w = F) ∧
      (∀ w' : A ⟶ A', L.schemeNsmul n ≫ w' = F → w' = w) ∧
      ∃ hw : w ≫ f' = f,
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
          (L.mul t P Q).1 ≫ w =
            (L'.mul t ⟨P.1 ≫ w, by rw [Category.assoc, hw]; exact P.2⟩
              ⟨Q.1 ≫ w, by rw [Category.assoc, hw]; exact Q.2⟩).1 :=
  K4_full S f L hc n f' L' F hF hFhom hFker

end S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_schemeNsmul_comp_eq_of_forall_isTorsionPoint
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_schemeNsmul_comp_eq_of_forall_isTorsionPoint (solution)
