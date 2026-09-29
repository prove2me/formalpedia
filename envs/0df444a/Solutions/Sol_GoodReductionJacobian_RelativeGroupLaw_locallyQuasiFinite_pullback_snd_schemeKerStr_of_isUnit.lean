-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_pullback_snd_schemeKerStr_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/84ff3182-f6ef-5114-9ce6-340f7263dd60

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_baseChange_schemeNsmul_comp_fst_and_eq_pullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_pullback_snd_schemeKerStr_of_isUnit

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {R : Type u} [CommRing R] {K : Type u} [Field K]
    (ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} [LocallyOfFiniteType f]
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : K)) :
    LocallyQuasiFinite (pullback.snd (G.schemeKerStr n) ι) := by

  have hc : G.IsCommutative := fun t x y => hcomm t x y
  have hlqf : LocallyQuasiFinite ((G.baseChange ι).schemeNsmul n) :=
    (G.baseChange ι).locallyQuasiFinite_schemeNsmul_of_isUnit (fun t x y => (hc.baseChange ι) t x y) n hn
  obtain ⟨h₁, h₂, -⟩ := G.baseChange_schemeNsmul_comp_fst_and_eq_pullback_map ι n

  have hover : G.schemeNsmul n ≫ f = f := G.schemeNsmul_over n
  have he : (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f = 𝟙 _ := (G.one (𝟙 _)).2
  have hcondK := pullback.condition (f := G.schemeNsmul n) (g := (G.one (𝟙 (Spec (CommRingCat.of R)))).1)

  have hR : IsPullback (pullback.fst f ι) ((G.baseChange ι).schemeNsmul n) (G.schemeNsmul n)
      (pullback.fst f ι) := by
    refine IsPullback.of_iso_pullback ⟨h₁.symm⟩ ?_ ?_ ?_
    · refine ⟨pullback.lift (pullback.fst f ι) ((G.baseChange ι).schemeNsmul n) h₁.symm,
        pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd f ι) ?_, ?_, ?_⟩
      · rw [Category.assoc, ← pullback.condition, ← Category.assoc, ← pullback.condition, Category.assoc,
          hover]
      · apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
        · simp only [Category.assoc, pullback.lift_snd, Category.id_comp, pullback.lift_snd_assoc, h₂]
      · apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
        · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
          apply pullback.hom_ext
          · rw [Category.assoc, h₁, pullback.lift_fst_assoc, pullback.condition]
          · rw [Category.assoc, h₂, pullback.lift_snd]
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _

  have hout : IsPullback (pullback.fst (G.schemeKerStr n) ι ≫ pullback.fst (G.schemeNsmul n) (G.one (𝟙 _)).1)
      (pullback.snd (G.schemeKerStr n) ι) (G.schemeNsmul n) (ι ≫ (G.one (𝟙 _)).1) :=
    (IsPullback.of_hasPullback (G.schemeKerStr n) ι).paste_horiz
      (IsPullback.of_hasPullback (G.schemeNsmul n) (G.one (𝟙 _)).1)

  let eK : Spec (CommRingCat.of K) ⟶ pullback f ι :=
    pullback.lift (ι ≫ (G.one (𝟙 _)).1) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have heK : eK ≫ pullback.fst f ι = ι ≫ (G.one (𝟙 _)).1 := pullback.lift_fst _ _ _
  have hkf : pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f = G.schemeKerStr n := by
    calc _ = pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫
          G.schemeNsmul n ≫ f := by rw [hover]
      _ = (pullback.snd (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫
          (G.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫ f := by rw [← Category.assoc, hcondK]
      _ = G.schemeKerStr n := by rw [Category.assoc, he, Category.comp_id]
  let j : pullback (G.schemeKerStr n) ι ⟶ pullback f ι :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst (G.schemeNsmul n) (G.one (𝟙 _)).1) (pullback.snd _ _)
      (by rw [Category.assoc, hkf, pullback.condition])
  have hj : j ≫ pullback.fst f ι = pullback.fst _ _ ≫ pullback.fst (G.schemeNsmul n) (G.one (𝟙 _)).1 :=
    pullback.lift_fst _ _ _
  rw [← hj, ← heK] at hout

  have hsq : IsPullback j (pullback.snd (G.schemeKerStr n) ι) ((G.baseChange ι).schemeNsmul n) eK := by
    refine hout.of_right ?_ hR
    apply pullback.hom_ext
    · rw [Category.assoc, h₁, ← Category.assoc, hj, Category.assoc, hcondK, Category.assoc, heK,
        pullback.condition_assoc]
    · rw [Category.assoc, h₂, Category.assoc]
      simp only [j, eK, pullback.lift_snd, Category.comp_id]
  exact MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) hsq hlqf

end S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_pullback_snd_schemeKerStr_of_isUnit
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_pullback_snd_schemeKerStr_of_isUnit (solution)
