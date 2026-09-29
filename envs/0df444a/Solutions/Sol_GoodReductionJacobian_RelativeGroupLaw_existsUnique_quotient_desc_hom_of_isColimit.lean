-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.existsUnique_quotient_desc_hom_of_isColimit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/7e4d440d-b18d-5b48-8863-fe9bcd8acbeb

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_quotient_desc_hom_of_isColimit

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_quotient_desc_hom_of_isColimit.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.actionSource"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "one mul_natural one_mul mul actionSource actionFstPoint actionSndPoint action"
namespace QuotientUMP
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {E : Scheme.{u}} (ι : E ⟶ J)
  {P : Scheme.{u}} (p : J ⟶ P) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)
  [Flat p] [Surjective p]
  (hcoeq : IsColimit (Cofork.ofπ p w))
  {g : P ⟶ Spec (CommRingCat.of R)} (hg : p ≫ g = f) (LP : RelativeGroupLaw R g)
  (hp : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
    (⟨(L.mul t x y).1 ≫ p, by rw [Category.assoc, hg, (L.mul t x y).2]⟩ : SchemeHomOver t g) =
      LP.mul t ⟨x.1 ≫ p, by rw [Category.assoc, hg, x.2]⟩ ⟨y.1 ≫ p, by rw [Category.assoc, hg, y.2]⟩)
  {X : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of R)} (LX : RelativeGroupLaw R gX)
  (φ : SchemeHomOver f gX)
  (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
    (⟨(L.mul t x y).1 ≫ φ.1, by rw [Category.assoc, φ.2, (L.mul t x y).2]⟩ : SchemeHomOver t gX) =
      LX.mul t ⟨x.1 ≫ φ.1, by rw [Category.assoc, φ.2, x.2]⟩ ⟨y.1 ≫ φ.1, by rw [Category.assoc, φ.2, y.2]⟩)
  (hφE : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (e : T ⟶ E) (he : e ≫ ι ≫ f = t),
    (⟨(e ≫ ι) ≫ φ.1, by rw [Category.assoc, φ.2, Category.assoc, he]⟩ : SchemeHomOver t gX) = LX.one t)

include hφ hφE in

theorem cond : pullback.snd (ι ≫ f) f ≫ φ.1 = L.action ι ≫ φ.1 := by
  let t := RelativeGroupLaw.actionSource f ι
  have he : (pullback.fst (ι ≫ f) f) ≫ ι ≫ f = t := by rw [pullback.condition]
  have h := hφ t (L.actionFstPoint ι) (L.actionSndPoint ι)
  have hE : (⟨(L.actionFstPoint ι).1 ≫ φ.1, by rw [Category.assoc, φ.2, (L.actionFstPoint ι).2]⟩ : SchemeHomOver t gX) = LX.one t :=
    hφE t (pullback.fst (ι ≫ f) f) he
  rw [hE, LX.one_mul] at h
  have h' := congrArg Subtype.val h
  exact h'.symm

noncomputable def ψm : P ⟶ X := Cofork.IsColimit.desc hcoeq φ.1 (cond L ι LX φ hφ hφE)

theorem p_ψm : p ≫ ψm L ι p w hcoeq LX φ hφ hφE = φ.1 := by
  have h := Cofork.IsColimit.π_desc' hcoeq φ.1 (cond L ι LX φ hφ hφE)
  rwa [Cofork.π_ofπ] at h

theorem epi_p : Epi p := Flat.epi_of_flat_of_surjective p

include hg in
theorem ψm_over : ψm L ι p w hcoeq LX φ hφ hφE ≫ gX = g := by
  haveI := epi_p p
  rw [← cancel_epi p, ← Category.assoc, p_ψm, hg]; exact φ.2

noncomputable def ψ : SchemeHomOver g gX := ⟨ψm L ι p w hcoeq LX φ hφ hφE, ψm_over L ι p w hcoeq hg LX φ hφ hφE⟩

noncomputable def pp : pullback f f ⟶ pullback g g :=
  pullback.map f f g g p p (𝟙 _) (by rw [Category.comp_id, hg]) (by rw [Category.comp_id, hg])

theorem epi_pp : Epi (pp p hg) := by
  haveI : Flat (pp p hg) := MorphismProperty.pullbackMap (P := @Flat) (inferInstance : Flat p) (inferInstance : Flat p) hg.symm hg.symm
  haveI : Surjective (pp p hg) :=
    MorphismProperty.pullbackMap (P := @Surjective) (inferInstance : Surjective p) (inferInstance : Surjective p) hg.symm hg.symm
  exact Flat.epi_of_flat_of_surjective _

noncomputable def mP : pullback g g ⟶ P := (LP.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩ ⟨pullback.snd g g, pullback.condition.symm⟩).1

noncomputable def mX : pullback gX gX ⟶ X := (LX.mul (pullback.fst gX gX ≫ gX) ⟨pullback.fst gX gX, rfl⟩ ⟨pullback.snd gX gX, pullback.condition.symm⟩).1

theorem comp_m {Y : Scheme.{u}} {gY : Y ⟶ Spec (CommRingCat.of R)} (LY : RelativeGroupLaw R gY)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (θ : T ⟶ pullback gY gY) (ht : θ ≫ pullback.fst gY gY ≫ gY = t) :
    θ ≫ (LY.mul (pullback.fst gY gY ≫ gY) ⟨pullback.fst gY gY, rfl⟩ ⟨pullback.snd gY gY, pullback.condition.symm⟩).1 =
      (LY.mul t ⟨θ ≫ pullback.fst gY gY, ht⟩ ⟨θ ≫ pullback.snd gY gY, by rw [← ht, Category.assoc, pullback.condition]⟩).1 := by
  subst ht
  have h := congrArg Subtype.val (LY.mul_natural _ _ θ rfl (⟨pullback.fst gY gY, rfl⟩ : SchemeHomOver (pullback.fst gY gY ≫ gY) gY)
    (⟨pullback.snd gY gY, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst gY gY ≫ gY) gY))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  rw [h]
  rfl

include hp in

theorem pp_mP : pp p hg ≫ mP LP = (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 ≫ p := by
  rw [mP, comp_m LP (pullback.fst f f ≫ f) (pp p hg) (by rw [pp, pullback.lift_fst_assoc, Category.assoc, hg])]
  have h := hp (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩
  have h' := congrArg Subtype.val h
  refine Eq.trans ?_ h'.symm
  congr 2
  · exact Subtype.ext (by show pp p hg ≫ pullback.fst g g = pullback.fst f f ≫ p; rw [pp, pullback.lift_fst])
  · exact Subtype.ext (by show pp p hg ≫ pullback.snd g g = pullback.snd f f ≫ p; rw [pp, pullback.lift_snd])

noncomputable def ψψ : pullback g g ⟶ pullback gX gX :=
  pullback.map g g gX gX (ψm L ι p w hcoeq LX φ hφ hφE) (ψm L ι p w hcoeq LX φ hφ hφE) (𝟙 _)
    (by rw [Category.comp_id, ψm_over L ι p w hcoeq hg]) (by rw [Category.comp_id, ψm_over L ι p w hcoeq hg])

include hp in

theorem mP_ψ : mP LP ≫ ψm L ι p w hcoeq LX φ hφ hφE = ψψ L ι p w hcoeq hg LX φ hφ hφE ≫ mX LX := by
  haveI := epi_pp p hg
  rw [← cancel_epi (pp p hg), ← Category.assoc, pp_mP L p hg LP hp, Category.assoc, p_ψm]

  have hL : (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 ≫ φ.1 = _ :=
    congrArg Subtype.val (hφ (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩)
  rw [← Category.assoc (pp p hg), mX, comp_m LX (pullback.fst f f ≫ f) (pp p hg ≫ ψψ L ι p w hcoeq hg LX φ hφ hφE) (by
    rw [Category.assoc, ψψ, pullback.lift_fst_assoc, Category.assoc, pp, pullback.lift_fst_assoc, Category.assoc,
      ψm_over L ι p w hcoeq hg, hg])]
  rw [hL]
  congr 2
  · exact Subtype.ext (by
      show pullback.fst f f ≫ φ.1 = (pp p hg ≫ ψψ L ι p w hcoeq hg LX φ hφ hφE) ≫ pullback.fst gX gX
      rw [Category.assoc, ψψ, pullback.lift_fst, pp, pullback.lift_fst_assoc, Category.assoc, p_ψm])
  · exact Subtype.ext (by
      show pullback.snd f f ≫ φ.1 = (pp p hg ≫ ψψ L ι p w hcoeq hg LX φ hφ hφE) ≫ pullback.snd gX gX
      rw [Category.assoc, ψψ, pullback.lift_snd, pp, pullback.lift_snd_assoc, Category.assoc, p_ψm])

include hp in

theorem ψ_hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t g) :
    (⟨(LP.mul t u v).1 ≫ (ψ L ι p w hcoeq hg LX φ hφ hφE).1, by rw [Category.assoc, (ψ L ι p w hcoeq hg LX φ hφ hφE).2, (LP.mul t u v).2]⟩ : SchemeHomOver t gX) =
      LX.mul t ⟨u.1 ≫ (ψ L ι p w hcoeq hg LX φ hφ hφE).1, by rw [Category.assoc, (ψ L ι p w hcoeq hg LX φ hφ hφE).2, u.2]⟩
        ⟨v.1 ≫ (ψ L ι p w hcoeq hg LX φ hφ hφE).1, by rw [Category.assoc, (ψ L ι p w hcoeq hg LX φ hφ hφE).2, v.2]⟩ := by
  apply Subtype.ext
  show (LP.mul t u v).1 ≫ ψm L ι p w hcoeq LX φ hφ hφE = _

  have hu : (LP.mul t u v).1 = pullback.lift u.1 v.1 (u.2.trans v.2.symm) ≫ mP LP := by
    rw [mP, comp_m LP t _ (by rw [pullback.lift_fst_assoc]; exact u.2)]
    congr 2 <;> exact Subtype.ext (by simp only [pullback.lift_fst, pullback.lift_snd])
  have hx : (LX.mul t ⟨u.1 ≫ (ψ L ι p w hcoeq hg LX φ hφ hφE).1, by rw [Category.assoc, (ψ L ι p w hcoeq hg LX φ hφ hφE).2, u.2]⟩
        ⟨v.1 ≫ (ψ L ι p w hcoeq hg LX φ hφ hφE).1, by rw [Category.assoc, (ψ L ι p w hcoeq hg LX φ hφ hφE).2, v.2]⟩).1 =
      (pullback.lift u.1 v.1 (u.2.trans v.2.symm) ≫ ψψ L ι p w hcoeq hg LX φ hφ hφE) ≫ mX LX := by
    rw [mX, comp_m LX t _ (by
      rw [Category.assoc, ψψ, pullback.lift_fst_assoc, Category.assoc, pullback.lift_fst_assoc, ψm_over L ι p w hcoeq hg]
      exact u.2)]
    congr 2
    all_goals apply Subtype.ext
    all_goals first
      | (show u.1 ≫ ψm L ι p w hcoeq LX φ hφ hφE = (pullback.lift u.1 v.1 _ ≫ ψψ L ι p w hcoeq hg LX φ hφ hφE) ≫ pullback.fst gX gX
         rw [Category.assoc, ψψ, pullback.lift_fst, pullback.lift_fst_assoc])
      | (show v.1 ≫ ψm L ι p w hcoeq LX φ hφ hφE = (pullback.lift u.1 v.1 _ ≫ ψψ L ι p w hcoeq hg LX φ hφ hφE) ≫ pullback.snd gX gX
         rw [Category.assoc, ψψ, pullback.lift_snd, pullback.lift_snd_assoc])
  rw [hu, hx, Category.assoc, Category.assoc, mP_ψ L ι p w hcoeq hg LP hp LX φ hφ hφE]

end GoodReductionJacobian.RelativeGroupLaw.QuotientUMP

open GoodReductionJacobian.RelativeGroupLaw.QuotientUMP in
theorem solution
    {R : Type u} [CommRing R]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {E : Scheme.{u}} (ι : E ⟶ J)
    {P : Scheme.{u}} (p : J ⟶ P) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)
    [Flat p] [Surjective p]
    (hcoeq : IsColimit (Cofork.ofπ p w))
    {g : P ⟶ Spec (CommRingCat.of R)} (hg : p ≫ g = f) (LP : RelativeGroupLaw R g)
    (hp : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (⟨(L.mul t x y).1 ≫ p, by rw [Category.assoc, hg, (L.mul t x y).2]⟩ : SchemeHomOver t g) =
        LP.mul t ⟨x.1 ≫ p, by rw [Category.assoc, hg, x.2]⟩ ⟨y.1 ≫ p, by rw [Category.assoc, hg, y.2]⟩)
    {X : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of R)} (LX : RelativeGroupLaw R gX)
    (φ : SchemeHomOver f gX)
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (⟨(L.mul t x y).1 ≫ φ.1, by rw [Category.assoc, φ.2, (L.mul t x y).2]⟩ : SchemeHomOver t gX) =
        LX.mul t ⟨x.1 ≫ φ.1, by rw [Category.assoc, φ.2, x.2]⟩ ⟨y.1 ≫ φ.1, by rw [Category.assoc, φ.2, y.2]⟩)
    (hφE : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (e : T ⟶ E) (he : e ≫ ι ≫ f = t),
      (⟨(e ≫ ι) ≫ φ.1, by simp only [Category.assoc, φ.2, he]⟩ : SchemeHomOver t gX) = LX.one t) :
    ∃! ψ : SchemeHomOver g gX, p ≫ ψ.1 = φ.1 ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t g),
        (⟨(LP.mul t u v).1 ≫ ψ.1, by rw [Category.assoc, ψ.2, (LP.mul t u v).2]⟩ : SchemeHomOver t gX) =
          LX.mul t ⟨u.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, u.2]⟩ ⟨v.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, v.2]⟩ := by
  refine ⟨ψ L ι p w hcoeq hg LX φ hφ hφE, ⟨p_ψm L ι p w hcoeq LX φ hφ hφE, fun t u v => ψ_hom L ι p w hcoeq hg LP hp LX φ hφ hφE t u v⟩, ?_⟩
  rintro ψ' ⟨h1, -⟩
  apply Subtype.ext
  haveI := epi_p p
  rw [← cancel_epi p, h1]
  exact (p_ψm L ι p w hcoeq LX φ hφ hφE).symm

end S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_quotient_desc_hom_of_isColimit
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_quotient_desc_hom_of_isColimit (solution)
