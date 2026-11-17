-- Prove2me | solution 1 for N25.LocalFive.exists_integralPointCover
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:23.641785+00:00
-- url     : https://prove2.me/submissions/64554ad1-d38a-4d17-aedf-cbfaaa614444

import Mathlib
import Definitions.Def_N25_LocalFiveIntegralPoints
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_N25_LocalFive_henselian_R5
import Definitions.Def_N25_LocalFiveArithmetic
import Theorems.Thm_HenselianLocalRing_of_isAdicComplete_maximalIdeal
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open GoodReductionJacobian NeronModelInfra

open GoodReductionJacobian.RelativeGroupLaw

noncomputable section

local instance instL_N25_LocalFive_exists_integralPointCover_bfd51b_s984cbe : Fact (Nat.Prime 5) := ⟨by decide⟩

namespace N25.LocalFive

private theorem mul_changeSource
    {R : Type} [CommRing R] {A T : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t')
    (x y : SchemeHomOver t f) :
    (G.mul t' ⟨x.1, x.2.trans h⟩ ⟨y.1, y.2.trans h⟩).1 = (G.mul t x y).1 := by
  subst t'
  rfl

/-- Néron integral sections cover local points with the group law inherited from `L`. -/
theorem _root_.solution
    {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of ℚ)}
    (L : RelativeGroupLaw ℚ f)
    (hB : AbelianSchemePropertyBundle ℚ f)
    (hc : L.IsCommutative) : Nonempty (IntegralPointCover L hc) := by
  letI : HenselianLocalRing R5 := henselian_R5
  let ι := Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ_[5]))
  let j := specGenericFibreInclusion R5 ℚ_[5]
  let LK := L.baseChange ι
  have hBK : AbelianSchemePropertyBundle ℚ_[5] (baseChangeStr ι f) :=
    hB.of_isPullback (IsPullback.of_hasPullback f ι)
  obtain ⟨N, g, G, e, hmodel, hcomm, he, hmul⟩ :=
    LK.exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
      (R := R5) ℚ_[5] hBK
  letI : IsIso e.1 := he
  have hGc : G.IsCommutative := hcomm
  have hm (x y : SchemeHomOver ((𝟙 (Spec (CommRingCat.of ℚ_[5]))) ≫ j) g) :
      baseChangePointToBase ι (NeronModelInfra.schemeHomOverComp
        (baseChangePointOfBase j (G.mul _ x y)) e) =
      L.mul _
        (baseChangePointToBase ι (NeronModelInfra.schemeHomOverComp (baseChangePointOfBase j x) e))
        (baseChangePointToBase ι (NeronModelInfra.schemeHomOverComp (baseChangePointOfBase j y) e)) := by
    rw [← baseChangePointToBase_mul]
    congr 1
    rw [← hmul]
    congr 1
    apply (baseChangePointEquiv j (𝟙 _)).injective
    simp only [baseChangePointEquiv, Equiv.coe_fn_mk, baseChangePointToBase_ofBase]
    change G.mul _ x y = baseChangePointToBase j
      ((G.baseChange j).mul _ (baseChangePointOfBase j x) (baseChangePointOfBase j y))
    rw [baseChangePointToBase_mul, baseChangePointToBase_ofBase, baseChangePointToBase_ofBase]
  have hj : Spec.map (CommRingCat.ofHom (algebraMap R5 ℚ_[5])) =
      (𝟙 (Spec (CommRingCat.of ℚ_[5]))) ≫ j := by simp [j]
  have hi : (𝟙 (Spec (CommRingCat.of ℚ_[5]))) ≫ ι =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ_[5])) := by simp [ι]
  let v (x : G.AlgPoints hGc ℚ_[5]) : SchemeHomOver ((𝟙 _) ≫ j) g :=
    ⟨(AlgPoints.toPoint x).1, (AlgPoints.toPoint x).2.trans hj⟩
  let w (x : G.AlgPoints hGc ℚ_[5]) :=
    baseChangePointToBase ι (NeronModelInfra.schemeHomOverComp (baseChangePointOfBase j (v x)) e)
  let p (x : G.AlgPoints hGc ℚ_[5]) : L.AlgPoints hc ℚ_[5] :=
    AlgPoints.ofPoint ⟨(w x).1, (w x).2.trans hi⟩
  have hp : ∀ x y, p (x + y) = p x + p y := by
    intro x y
    have hv : v (x + y) = G.mul _ (v x) (v y) := by
      apply Subtype.ext
      exact (mul_changeSource G hj (AlgPoints.toPoint x) (AlgPoints.toPoint y)).symm
    have hw : w (x + y) = L.mul _ (w x) (w y) := by
      dsimp only [w]
      rw [hv]
      exact hm _ _
    apply AlgPoints.toPoint_injective
    apply Subtype.ext
    change (w (x + y)).1 = (L.mul _ ⟨(w x).1, (w x).2.trans hi⟩
      ⟨(w y).1, (w y).2.trans hi⟩).1
    rw [hw]
    exact (mul_changeSource L hi (w x) (w y)).symm
  let q : G.AlgPoints hGc ℚ_[5] →+ L.AlgPoints hc ℚ_[5] :=
    AddMonoidHom.mk' p hp
  let a : G.AlgPoints hGc R5 →+ G.AlgPoints hGc ℚ_[5] :=
    AlgPoints.map (IsScalarTower.toAlgHom R5 R5 ℚ_[5])
  refine ⟨⟨N, g, G, hGc, hmodel, q.comp a, ?_⟩⟩
  intro x
  let xK : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ_[5]))) (baseChangeStr ι f) :=
    baseChangePointOfBase ι ⟨(AlgPoints.toPoint x).1, (AlgPoints.toPoint x).2.trans hi.symm⟩
  let yK : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℚ_[5]))) (genericFibreStr ℚ_[5] g) :=
    ⟨xK.1 ≫ inv e.1, by
      rw [Category.assoc, show inv e.1 ≫ genericFibreStr ℚ_[5] g =
        baseChangeStr ι f from (IsIso.inv_comp_eq e.1).2 e.2.symm, xK.2]⟩
  let y := baseChangePointToBase j yK
  -- This is the canonical identification of the raw generic source with Spec Q5.
  let c := asIso (pullback.snd (𝟙 (Spec (CommRingCat.of R5))) j)
  have hcj : c.inv ≫ pullback.fst (𝟙 (Spec (CommRingCat.of R5))) j = j := by
    have h := congrArg (fun v => c.inv ≫ v)
      (pullback.condition (f := 𝟙 (Spec (CommRingCat.of R5))) (g := j))
    change c.inv ≫ pullback.fst (𝟙 (Spec (CommRingCat.of R5))) j ≫ 𝟙 _ =
      c.inv ≫ c.hom ≫ j at h
    simpa only [Category.comp_id, Iso.inv_hom_id_assoc] using h
  obtain ⟨s, hsraw⟩ := hmodel.integralPoints_bijective.surjective
    (⟨c.hom ≫ yK.1, by rw [Category.assoc, yK.2, Category.comp_id]; rfl⟩)
  have hs : j ≫ s.1 = y.1 := by
    have h := congrArg (fun v => c.inv ≫ v.1 ≫ pullback.fst g j) hsraw
    change c.inv ≫ (pullback.lift
      (pullback.fst (𝟙 (Spec (CommRingCat.of R5))) j ≫ s.1)
      (pullback.snd (𝟙 (Spec (CommRingCat.of R5))) j) _) ≫ pullback.fst g j =
      c.inv ≫ (c.hom ≫ yK.1) ≫ pullback.fst g j at h
    simp only [Category.assoc, pullback.lift_fst] at h
    rw [← Category.assoc c.inv (pullback.fst (𝟙 _) j), hcj] at h
    simpa only [Category.assoc,
      ← Category.assoc c.inv (pullback.fst (𝟙 _) j), hcj,
      Iso.inv_hom_id_assoc, y, baseChangePointToBase_coe] using h
  have hself : (𝟙 (Spec (CommRingCat.of R5))) =
      Spec.map (CommRingCat.ofHom (algebraMap R5 R5)) := by
    simp only [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  let z : G.AlgPoints hGc R5 := AlgPoints.ofPoint ⟨s.1, s.2.trans hself⟩
  refine ⟨z, ?_⟩
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  change ((w (a z)).1) = (AlgPoints.toPoint x).1
  have hz : baseChangePointOfBase j (v (a z)) = yK := by
    apply (baseChangePointEquiv j (𝟙 _)).injective
    simp only [baseChangePointEquiv, Equiv.coe_fn_mk, baseChangePointToBase_ofBase]
    apply Subtype.ext
    change (AlgPoints.toPoint (a z)).1 = y.1
    change j ≫ s.1 = y.1
    exact hs
  dsimp only [w]
  rw [hz]
  dsimp only [baseChangePointToBase, NeronModelInfra.schemeHomOverComp, yK, xK]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, baseChangePointOfBase_coe, pullback.lift_fst]

end N25.LocalFive
