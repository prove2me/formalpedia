-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_schemeHomOver_baseChange_baseChange_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/48f8c29f-c604-523a-82cf-e7948a86decc

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOver_baseChange_baseChange_iso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] {R'' : Type u} [CommRing R'']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    (j : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R'))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    ∃ (u : SchemeHomOver (RelativeGroupLaw.baseChangeStr j (RelativeGroupLaw.baseChangeStr ι f))
          (RelativeGroupLaw.baseChangeStr (j ≫ ι) f))
      (v : SchemeHomOver (RelativeGroupLaw.baseChangeStr (j ≫ ι) f)
          (RelativeGroupLaw.baseChangeStr j (RelativeGroupLaw.baseChangeStr ι f))),
      u.1 ≫ v.1 = 𝟙 _ ∧ v.1 ≫ u.1 = 𝟙 _ ∧
      u.1 ≫ pullback.fst f (j ≫ ι) = pullback.fst (pullback.snd f ι) j ≫ pullback.fst f ι ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R''))
        (x y : SchemeHomOver t (RelativeGroupLaw.baseChangeStr j (RelativeGroupLaw.baseChangeStr ι f))),
        NeronModelInfra.schemeHomOverComp (((G.baseChange ι).baseChange j).mul t x y) u =
          (G.baseChange (j ≫ ι)).mul t (NeronModelInfra.schemeHomOverComp x u)
            (NeronModelInfra.schemeHomOverComp y u) := by
  classical
  let e := pullbackLeftPullbackSndIso f ι j
  have he_snd : e.hom ≫ pullback.snd f (j ≫ ι) = pullback.snd (pullback.snd f ι) j :=
    pullbackLeftPullbackSndIso_hom_snd f ι j
  have he_fst : e.hom ≫ pullback.fst f (j ≫ ι) = pullback.fst (pullback.snd f ι) j ≫ pullback.fst f ι :=
    pullbackLeftPullbackSndIso_hom_fst f ι j
  have hv_snd : e.inv ≫ pullback.snd (pullback.snd f ι) j = pullback.snd f (j ≫ ι) := by
    rw [← he_snd, Iso.inv_hom_id_assoc]
  let u : SchemeHomOver (RelativeGroupLaw.baseChangeStr j (RelativeGroupLaw.baseChangeStr ι f))
      (RelativeGroupLaw.baseChangeStr (j ≫ ι) f) := ⟨e.hom, he_snd⟩
  let v : SchemeHomOver (RelativeGroupLaw.baseChangeStr (j ≫ ι) f)
      (RelativeGroupLaw.baseChangeStr j (RelativeGroupLaw.baseChangeStr ι f)) := ⟨e.inv, hv_snd⟩

  have mul_val_congr : ∀ {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
      (X Y : SchemeHomOver t₁ f) (X' Y' : SchemeHomOver t₂ f), X.1 = X'.1 → Y.1 = Y'.1 →
      (G.mul t₁ X Y).1 = (G.mul t₂ X' Y').1 := by
    intro T t₁ t₂ h X Y X' Y' hX hY
    subst h
    rw [show X = X' from Subtype.ext hX, show Y = Y' from Subtype.ext hY]
  refine ⟨u, v, e.hom_inv_id, e.inv_hom_id, he_fst, ?_⟩
  intro T t x y
  apply Subtype.ext
  apply pullback.hom_ext
  ·
    rw [NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
    show (((G.baseChange ι).baseChange j).mul t x y).1 ≫ e.hom ≫ pullback.fst f (j ≫ ι) = _
    rw [he_fst, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, ← Category.assoc,
      pullback.lift_fst, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe,
      pullback.lift_fst]
    rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
    apply mul_val_congr (Category.assoc t j ι)
    · rw [RelativeGroupLaw.baseChangePointToBase_coe, RelativeGroupLaw.baseChangePointToBase_coe,
        RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc,
        Category.assoc, he_fst]
    · rw [RelativeGroupLaw.baseChangePointToBase_coe, RelativeGroupLaw.baseChangePointToBase_coe,
        RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc,
        Category.assoc, he_fst]
  ·
    have h1 := (NeronModelInfra.schemeHomOverComp (((G.baseChange ι).baseChange j).mul t x y) u).2
    have h2 := ((G.baseChange (j ≫ ι)).mul t (NeronModelInfra.schemeHomOverComp x u)
      (NeronModelInfra.schemeHomOverComp y u)).2
    exact h1.trans h2.symm

end S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOver_baseChange_baseChange_iso
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOver_baseChange_baseChange_iso (solution)
