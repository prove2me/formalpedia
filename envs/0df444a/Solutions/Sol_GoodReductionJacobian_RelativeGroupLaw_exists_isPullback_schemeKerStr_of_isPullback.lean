-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isPullback_schemeKerStr_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/eef86e23-20a8-51cd-8e9a-17ac3486e328

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isPullback_schemeKerStr_of_isPullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace KerBC

section Points

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem nsmul_val {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    (L.nsmul t n P).1 = P.1 ≫ L.schemeNsmul n := by
  have h := L.nsmul_natural f t P.1 P.2 n RelativeGroupLaw.idPoint
  have hP : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P := by
    apply Subtype.ext
    rw [schemeHomOverComp_coe]
    exact Category.comp_id _
  rw [hP] at h
  rw [← h, schemeHomOverComp_coe]
  rfl

theorem one_val {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h := L.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t)
  rw [← h, schemeHomOverComp_coe]

theorem fst_comp_f (n : ℕ) : pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f = L.schemeKerStr n := by
  have h1 : pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f =
      pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ (L.schemeNsmul n ≫ f) := by rw [L.schemeNsmul_over]
  rw [h1, ← Category.assoc, pullback.condition, Category.assoc, (L.one (𝟙 _)).2]
  exact Category.comp_id _

end Points

section Cartesian

variable {R R' : Type u} [CommRing R] [CommRing R'] {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  {f' : A' ⟶ Spec (CommRingCat.of R')} (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R' f')
  (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (g : A' ⟶ A) (hg : IsPullback g f' f ι)
  (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' f'),
    (L'.mul t' P Q).1 ≫ g =
      (L.mul (t' ≫ ι) ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)

def pushAlong {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' f') :
    SchemeHomOver (t' ≫ ι) f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩

include hmul in
theorem one_g {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    (L'.one t').1 ≫ g = (L.one (t' ≫ ι)).1 := by
  letI := L.pointGroup (t' ≫ ι)
  let x : SchemeHomOver (t' ≫ ι) f := pushAlong ι g hg t' (L'.one t')
  have h := hmul t' (L'.one t') (L'.one t')
  rw [L'.one_mul] at h
  have hx : x = x * x := Subtype.ext h
  have : x = 1 := by
    have h2 : x * x = x * 1 := by rw [mul_one]; exact hx.symm
    exact mul_left_cancel h2
  exact congrArg Subtype.val this

include hmul in
theorem nsmul_g {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ) (P : SchemeHomOver t' f') :
    (L'.nsmul t' n P).1 ≫ g = (L.nsmul (t' ≫ ι) n (pushAlong ι g hg t' P)).1 := by
  induction n with
  | zero => exact one_g L L' ι g hg hmul t'
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, hmul]
      congr 2
      exact Subtype.ext ih

include hmul in
theorem schemeNsmul_g (n : ℕ) : L'.schemeNsmul n ≫ g = g ≫ L.schemeNsmul n := by
  have h := nsmul_g L L' ι g hg hmul f' n RelativeGroupLaw.idPoint
  rw [nsmul_val, nsmul_val] at h
  change (𝟙 A' ≫ L'.schemeNsmul n) ≫ g = (𝟙 A' ≫ g) ≫ L.schemeNsmul n at h
  rw [Category.id_comp, Category.id_comp] at h
  exact h

include hmul in
theorem unit_g : (L'.one (𝟙 _)).1 ≫ g = ι ≫ (L.one (𝟙 _)).1 := by
  rw [one_g L L' ι g hg hmul, one_val, Category.id_comp]

include hmul in

theorem exists_isPullback_schemeKerStr (n : ℕ) :
    ∃ π : L'.schemeKer n ⟶ L.schemeKer n, IsPullback π (L'.schemeKerStr n) (L.schemeKerStr n) ι ∧
      π ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 = pullback.fst (L'.schemeNsmul n) (L'.one (𝟙 _)).1 ≫ g := by
  let e : Spec (CommRingCat.of R) ⟶ A := (L.one (𝟙 _)).1
  let e' : Spec (CommRingCat.of R') ⟶ A' := (L'.one (𝟙 _)).1
  have hN := schemeNsmul_g L L' ι g hg hmul n
  have hU : e' ≫ g = ι ≫ e := unit_g L L' ι g hg hmul
  have w : (pullback.fst (L'.schemeNsmul n) e' ≫ g) ≫ L.schemeNsmul n = (pullback.snd (L'.schemeNsmul n) e' ≫ ι) ≫ e := by
    rw [Category.assoc, ← hN, ← Category.assoc, pullback.condition, Category.assoc, hU, Category.assoc]
  let π : L'.schemeKer n ⟶ L.schemeKer n := pullback.lift _ _ w
  have hπ1 : π ≫ pullback.fst _ _ = pullback.fst _ _ ≫ g := pullback.lift_fst _ _ _
  have hπ2 : π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ ι := pullback.lift_snd _ _ _
  refine ⟨π, IsPullback.of_isLimit' ⟨hπ2⟩ ?_, hπ1⟩
  refine PullbackCone.IsLimit.mk _ (fun c => ?_) (fun c => ?_) (fun c => ?_) (fun c m hm1 hm2 => ?_)
  · refine pullback.lift (hg.lift (c.fst ≫ pullback.fst _ _) c.snd ?_) c.snd ?_
    · rw [Category.assoc, fst_comp_f]; exact c.condition
    · apply hg.hom_ext
      · rw [Category.assoc, hN, ← Category.assoc, IsPullback.lift_fst, Category.assoc, pullback.condition,
          ← Category.assoc, Category.assoc c.snd, hU, ← Category.assoc]
        congr 1
        exact c.condition
      · rw [Category.assoc, L'.schemeNsmul_over, IsPullback.lift_snd, Category.assoc, (L'.one (𝟙 _)).2]
        exact (Category.comp_id _).symm
  · apply pullback.hom_ext
    · rw [Category.assoc, hπ1, ← Category.assoc, pullback.lift_fst, IsPullback.lift_fst]
    · rw [Category.assoc, hπ2, ← Category.assoc, pullback.lift_snd]
      exact c.condition.symm
  · exact pullback.lift_snd _ _ _
  · apply pullback.hom_ext
    · rw [pullback.lift_fst]
      apply hg.hom_ext
      · rw [IsPullback.lift_fst, Category.assoc, ← hπ1, ← Category.assoc, hm1]
      · rw [IsPullback.lift_snd, Category.assoc, fst_comp_f]
        exact hm2
    · rw [pullback.lift_snd]; exact hm2

end Cartesian

end KerBC

open KerBC in
theorem solution
    {R R' : Type u} [CommRing R] [CommRing R'] (φ : R →+* R')
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')} (L' : RelativeGroupLaw R' f')
    (g : A' ⟶ A) (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (n : ℕ) :
    ∃ gn : L'.schemeKer n ⟶ L.schemeKer n,
      IsPullback gn (L'.schemeKerStr n) (L.schemeKerStr n) (Spec.map (CommRingCat.ofHom φ)) ∧
      gn ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 =
        pullback.fst (L'.schemeNsmul n) (L'.one (𝟙 (Spec (CommRingCat.of R')))).1 ≫ g :=
  exists_isPullback_schemeKerStr L L' (Spec.map (CommRingCat.ofHom φ)) g hg hmul n

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isPullback_schemeKerStr_of_isPullback
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isPullback_schemeKerStr_of_isPullback (solution)
