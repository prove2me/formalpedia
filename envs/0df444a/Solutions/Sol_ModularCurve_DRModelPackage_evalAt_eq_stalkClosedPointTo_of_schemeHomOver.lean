-- Prove2me | solution 1 for ModularCurve.DRModelPackage.evalAt_eq_stalkClosedPointTo_of_schemeHomOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d4f238da-b173-5862-b25a-d12d6c410849

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
import Theorems.Thm_AlgebraicGeometry_exists_isUnit_mul_eq_mem_closure_of_stalk_pullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_evalAt_eq_stalkClosedPointTo_of_schemeHomOver
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace EvalMatch

universe u

theorem stalkClosedPointTo_germ_const {O : Type u} [CommRing O] [IsLocalRing O]
    {Y : Scheme.{u}} (u : Y ⟶ Spec (CommRingCat.of O)) (t : Spec (CommRingCat.of O) ⟶ Y) (ht : t ≫ u = 𝟙 _) (a : O) :
    (Scheme.stalkClosedPointTo t).hom ((Y.presheaf.germ ⊤ (t.base (IsLocalRing.closedPoint O)) trivial).hom
      (u.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a))) = a := by
  have hsec : ∀ y : Γ(Spec (CommRingCat.of O), ⊤), (t.app ⊤).hom (u.appTop.hom y) = y := by
    intro y
    have h := Scheme.Hom.comp_appTop t u
    rw [ht] at h
    have h2 := congrArg (fun φ : Γ(Spec (CommRingCat.of O), ⊤) ⟶ Γ(Spec (CommRingCat.of O), ⊤) => φ.hom y) h
    simp at h2
    exact h2.symm
  show ((Y.presheaf.germ ⊤ (t.base (IsLocalRing.closedPoint O)) trivial) ≫
    Scheme.stalkClosedPointTo t).hom (u.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)) = a
  rw [Scheme.germ_stalkClosedPointTo t ⊤ trivial]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, Iso.trans_hom, Functor.mapIso_hom,
    Iso.op_hom, eqToIso.hom, hsec]
  try simp only [RingHom.id_apply]
  change ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom).hom a = a
  rw [Iso.inv_hom_id]
  rfl

theorem stalkClosedPointTo_comp_germ {R : CommRingCat.{u}} [IsLocalRing R] {X Y : Scheme.{u}}
    (q : Spec R ⟶ X) (g : X ⟶ Y) (U : Y.Opens) (hU : (q ≫ g).base (IsLocalRing.closedPoint R) ∈ U) (f : Γ(Y, U)) :
    (Scheme.stalkClosedPointTo (q ≫ g)).hom ((Y.presheaf.germ U _ hU).hom f) =
      (Scheme.stalkClosedPointTo q).hom ((X.presheaf.germ (g ⁻¹ᵁ U) (q.base (IsLocalRing.closedPoint R)) hU).hom
        ((g.app U).hom f)) := by
  rw [Scheme.stalkClosedPointTo_comp]
  show ((Y.presheaf.germ U _ hU ≫ g.stalkMap _) ≫ Scheme.stalkClosedPointTo q).hom f = _
  erw [Scheme.Hom.germ_stalkMap g U (q.base (IsLocalRing.closedPoint R)) hU]
  rfl

theorem map_stalkClosedPointTo_germ {O K' : Type u} [CommRing O] [IsLocalRing O] [CommRing K'] [IsLocalRing K']
    (φ : CommRingCat.of O ⟶ CommRingCat.of K') {Y : Scheme.{u}} (t : Spec (CommRingCat.of O) ⟶ Y) (U : Y.Opens)
    (hU : t.base (IsLocalRing.closedPoint O) ∈ U)
    (hU' : (Spec.map φ ≫ t).base (IsLocalRing.closedPoint K') ∈ U) (f : Γ(Y, U)) :
    φ.hom ((Scheme.stalkClosedPointTo t).hom ((Y.presheaf.germ U _ hU).hom f)) =
      (Scheme.stalkClosedPointTo (Spec.map φ ≫ t)).hom ((Y.presheaf.germ U _ hU').hom f) := by

  have key : ∀ {S : Type u} [CommRing S] [IsLocalRing S] (r : Spec (CommRingCat.of S) ⟶ Y)
      (hr : r.base (IsLocalRing.closedPoint S) ∈ U),
      (Scheme.stalkClosedPointTo r).hom ((Y.presheaf.germ U _ hr).hom f) =
        (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((r.appLE U ⊤
          (by rw [Scheme.preimage_eq_top_of_closedPoint_mem r hr])).hom f) := by
    intro S _ _ r hr
    have h := congrArg (fun ψ => ψ.hom f) (Scheme.germ_stalkClosedPointTo r U hr)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
    rw [h]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply]
    congr 1
  rw [key t hU, key (Spec.map φ ≫ t) hU']
  have hcomp : (Spec.map φ ≫ t).appLE U ⊤ (by rw [Scheme.preimage_eq_top_of_closedPoint_mem _ hU']) =
      t.appLE U ⊤ (by rw [Scheme.preimage_eq_top_of_closedPoint_mem t hU]) ≫ (Spec.map φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [hcomp]
  have hnat := congrArg (fun ψ => ψ.hom ((t.appLE U ⊤ (by rw [Scheme.preimage_eq_top_of_closedPoint_mem t hU])).hom f))
    (Scheme.ΓSpecIso_naturality φ)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hnat
  simpa using hnat.symm

theorem algebraMap_germ_eq_germToFunctionField {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) (x : X) (hx : x ∈ U)
    [Nonempty U] (f : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.germ U x hx).hom f) = (X.germToFunctionField U).hom f := by
  change ((X.presheaf.germ U x hx) ≫ X.presheaf.stalkSpecializes _).hom f = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]

theorem isUnit_valuationSubring_mk_iff {F : Type*} [Field F] (A : ValuationSubring F) (g : F) (hg : g ∈ A) :
    IsUnit (⟨g, hg⟩ : A) ↔ g ≠ 0 ∧ g⁻¹ ∈ A := by
  constructor
  · rintro ⟨u, hu⟩
    have hmul : g * ((u⁻¹ : Aˣ) : A).1 = 1 := by
      have := congrArg (fun w : A => (w : F)) u.mul_inv
      simpa [hu] using this
    have hg0 : g ≠ 0 := fun h => by simp [h] at hmul
    refine ⟨hg0, ?_⟩
    have : g⁻¹ = ((u⁻¹ : Aˣ) : A).1 := by
      rw [inv_eq_of_mul_eq_one_right hmul]
    rw [this]; exact ((u⁻¹ : Aˣ) : A).2
  · rintro ⟨hg0, hinv⟩
    exact ⟨⟨⟨g, hg⟩, ⟨g⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hg0), Subtype.ext (inv_mul_cancel₀ hg0)⟩, rfl⟩

theorem residue_eq_algebraMap_iff {K S : Type*} [Field K] [CommRing S] [IsLocalRing S] [Algebra K S] (x : S) (c : K) :
    IsLocalRing.residue S x = algebraMap K (IsLocalRing.ResidueField S) c ↔ ¬ IsUnit (x - algebraMap K S c) := by
  rw [show algebraMap K (IsLocalRing.ResidueField S) c = IsLocalRing.residue S (algebraMap K S c) from rfl,
    ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

end EvalMatch

set_option maxHeartbeats 16000000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

    [hneη : Nonempty (Scheme.Opens.toScheme
      ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hMη : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((𝔛.Mη.ffEquiv.symm
          (𝔛.Mη.C.germToFunctionField
            ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
            (((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).app
                ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
              (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of
                  ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))
          : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)

    (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hePl : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
        (f : ↥(modularFunctionFieldBar (1 * p))) (f' : ↥(modularFunctionFieldBar p)),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (f' : LaurentSeries (AlgebraicClosure ℚ)) →
          (f ∈ V.toValuationSubring ↔ f' ∈ (ePl V).toValuationSubring) ∧ V.evalAt f = (ePl V).evalAt f')

    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
    (t : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of O)))
      (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (ht : Spec.map (CommRingCat.ofHom (ιK.comp (algebraMap O K))) ≫ t.1 ≫
        pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      (𝔛.Mη.pointEquivPlace.symm (ePl V)).1 ≫ 𝔛.eη ≫
        pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))))
    (hx : t.1.base (IsLocalRing.closedPoint O) = x)
    (hfin : x ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
    (s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
      (t.1.base (IsLocalRing.closedPoint O))) :
    φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr
          (.of_eq hx) |>.hom.hom s)) ∈ V.toValuationSubring ∧
    V.evalAt (φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr
          (.of_eq hx) |>.hom.hom s))) =
      ιK (algebraMap O K (Scheme.stalkClosedPointTo t.1 s)) := by
  classical
  subst hx
  have hsc : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr (Inseparable.of_eq (rfl : t.1.base (IsLocalRing.closedPoint O) =
      t.1.base (IsLocalRing.closedPoint O)))).hom.hom s = s := by simp
  rw [hsc]

  set y := 𝔛.Mη.pointEquivPlace.symm (ePl V) with hy
  have hyV : 𝔛.Mη.pointEquivPlace y = ePl V := Equiv.apply_symm_apply _ _
  set jK : CommRingCat.of O ⟶ CommRingCat.of (AlgebraicClosure ℚ) := CommRingCat.ofHom (ιK.comp (algebraMap O K)) with hjK
  set z : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) := Spec.map jK ≫ t.1 with hz
  have hzt : z ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) = y.1 ≫ 𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) := by rw [hz, Category.assoc]; exact ht

  have hgenU : z.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := by
    have hsp : (Spec.map jK).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ⤳ IsLocalRing.closedPoint O :=
      IsLocalRing.specializes_closedPoint _
    have hsp' : z.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ⤳ t.1.base (IsLocalRing.closedPoint O) := by
      rw [hz, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
      exact hsp.map t.1.base.hom.continuous
    exact hsp'.mem_open ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).isOpen hfin
  have hgenU' : (z ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := hgenU
  have hyU' : (y.1 ≫ 𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))))).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := by
    rw [← hzt]; exact hgenU'
  have hyU : y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ (𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := hyU'

  let val : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (t.1.base (IsLocalRing.closedPoint O)) →+* AlgebraicClosure ℚ :=
    (ιK.comp (algebraMap O K)).comp (Scheme.stalkClosedPointTo t.1).hom
  have hval : ∀ r, val r = ιK (algebraMap O K ((Scheme.stalkClosedPointTo t.1).hom r)) := fun r => rfl
  let rd : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (t.1.base (IsLocalRing.closedPoint O)) →+* ↥(modularFunctionFieldBar (1 * p)) :=
    φ.comp (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)
  have hrd : ∀ r, rd r = φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField r) := fun r => rfl
  let Pr : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (t.1.base (IsLocalRing.closedPoint O)) → Prop := fun r =>
    ∃ h : rd r ∈ V.toValuationSubring,
      IsLocalRing.residue V.toValuationSubring ⟨rd r, h⟩ = algebraMap (AlgebraicClosure ℚ) V.ResidueField (val r)

  have hconst : ∀ c : AlgebraicClosure ℚ, ∃ h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) c ∈
      V.toValuationSubring, IsLocalRing.residue V.toValuationSubring ⟨_, h⟩ =
        algebraMap (AlgebraicClosure ℚ) V.ResidueField c := by
    intro c
    refine ⟨V.algebraMap_mem' c, ?_⟩
    have : (⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) c, V.algebraMap_mem' c⟩ :
        V.toValuationSubring) = algebraMap (AlgebraicClosure ℚ) V.toValuationSubring c := Subtype.ext rfl
    rw [this]
    rfl

  have Padd : ∀ r₁ r₂, Pr r₁ → Pr r₂ → Pr (r₁ + r₂) := by
    rintro r₁ r₂ ⟨h₁, e₁⟩ ⟨h₂, e₂⟩
    refine ⟨by rw [map_add]; exact add_mem h₁ h₂, ?_⟩
    have : (⟨rd (r₁ + r₂), by rw [map_add]; exact add_mem h₁ h₂⟩ : V.toValuationSubring) = ⟨rd r₁, h₁⟩ + ⟨rd r₂, h₂⟩ :=
      Subtype.ext (map_add rd r₁ r₂)
    rw [this, map_add, e₁, e₂, map_add, map_add]
  have Pmul : ∀ r₁ r₂, Pr r₁ → Pr r₂ → Pr (r₁ * r₂) := by
    rintro r₁ r₂ ⟨h₁, e₁⟩ ⟨h₂, e₂⟩
    refine ⟨by rw [map_mul]; exact mul_mem h₁ h₂, ?_⟩
    have : (⟨rd (r₁ * r₂), by rw [map_mul]; exact mul_mem h₁ h₂⟩ : V.toValuationSubring) = ⟨rd r₁, h₁⟩ * ⟨rd r₂, h₂⟩ :=
      Subtype.ext (map_mul rd r₁ r₂)
    rw [this, map_mul, e₁, e₂, map_mul, map_mul]
  have Pneg : ∀ r, Pr r → Pr (-r) := by
    rintro r ⟨h, e⟩
    refine ⟨by rw [map_neg]; exact neg_mem h, ?_⟩
    have : (⟨rd (-r), by rw [map_neg]; exact neg_mem h⟩ : V.toValuationSubring) = -⟨rd r, h⟩ :=
      Subtype.ext (map_neg rd r)
    rw [this, map_neg, e, map_neg, map_neg]
  have Pone : Pr 1 := by
    refine ⟨by rw [map_one]; exact one_mem _, ?_⟩
    have : (⟨rd 1, by rw [map_one]; exact one_mem _⟩ : V.toValuationSubring) = 1 := Subtype.ext (map_one rd)
    rw [this, map_one, map_one, map_one]
  have Pzero : Pr 0 := by
    refine ⟨by rw [map_zero]; exact zero_mem _, ?_⟩
    have : (⟨rd 0, by rw [map_zero]; exact zero_mem _⟩ : V.toValuationSubring) = 0 := Subtype.ext (map_zero rd)
    rw [this, map_zero, map_zero, map_zero]

  have Pconst : ∀ o : O, Pr (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ (t.1.base (IsLocalRing.closedPoint O)) trivial).hom
      (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))) := by
    intro o
    obtain ⟨h, e⟩ := hconst (ιK (algebraMap O K o))
    have hv : val (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ (t.1.base (IsLocalRing.closedPoint O)) trivial).hom
        (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))) = ιK (algebraMap O K o) := by
      rw [hval, EvalMatch.stalkClosedPointTo_germ_const (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) t.1 t.2 o]
    have hr : rd (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ (t.1.base (IsLocalRing.closedPoint O)) trivial).hom
        (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K o)) := hφO o
    refine ⟨hr ▸ h, ?_⟩
    rw [hv, ← e]
    congr 1
    exact Subtype.ext hr

  have htransfer : ∀ (f : ↥(modularFunctionFieldBar (1 * p))) (f' : ↥(modularFunctionFieldBar p))
      (hff : (f : LaurentSeries (AlgebraicClosure ℚ)) = (f' : LaurentSeries (AlgebraicClosure ℚ)))
      (c : AlgebraicClosure ℚ) (h' : f' ∈ (ePl V).toValuationSubring)
      (e' : IsLocalRing.residue (ePl V).toValuationSubring ⟨f', h'⟩ = algebraMap (AlgebraicClosure ℚ) _ c),
      ∃ h : f ∈ V.toValuationSubring,
        IsLocalRing.residue V.toValuationSubring ⟨f, h⟩ = algebraMap (AlgebraicClosure ℚ) V.ResidueField c := by
    intro f f' hff c h' e'
    have hmem : f ∈ V.toValuationSubring := ((hePl V f f' hff).1).mpr h'
    refine ⟨hmem, ?_⟩

    rw [EvalMatch.residue_eq_algebraMap_iff] at e' ⊢
    intro hu
    apply e'
    have hg : (⟨f, hmem⟩ - algebraMap (AlgebraicClosure ℚ) V.toValuationSubring c : V.toValuationSubring) =
        ⟨f - algebraMap (AlgebraicClosure ℚ) _ c, sub_mem hmem (V.algebraMap_mem' c)⟩ := Subtype.ext rfl
    have hg' : (⟨f', h'⟩ - algebraMap (AlgebraicClosure ℚ) (ePl V).toValuationSubring c : (ePl V).toValuationSubring) =
        ⟨f' - algebraMap (AlgebraicClosure ℚ) _ c, sub_mem h' ((ePl V).algebraMap_mem' c)⟩ := Subtype.ext rfl
    rw [hg, EvalMatch.isUnit_valuationSubring_mk_iff] at hu
    rw [hg', EvalMatch.isUnit_valuationSubring_mk_iff]
    have hLS : ((f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) c : ↥(modularFunctionFieldBar (1 * p))) :
        LaurentSeries (AlgebraicClosure ℚ)) = ((f' - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) c :
          ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) := by
      push_cast
      rw [hff]
    obtain ⟨h0, hinv⟩ := hu
    refine ⟨fun h => h0 ?_, ?_⟩
    · apply Subtype.ext
      rw [hLS]
      simp [h]
    · refine ((hePl V _ _ ?_).1).mp hinv
      push_cast
      rw [hff]

  have Pchart : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), Pr (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (t.1.base (IsLocalRing.closedPoint O)) hfin).hom
      (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) := by
    intro a

    have hread : rd (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (t.1.base (IsLocalRing.closedPoint O)) hfin).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) = φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) := by
      rw [hrd, EvalMatch.algebraMap_germ_eq_germToFunctionField]
    have hff : ((rd (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (t.1.base (IsLocalRing.closedPoint O)) hfin).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ((⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull p)).2⟩ : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [hread]
      exact hφj a

    have hMηa : (⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull p)).2⟩ : ↥(modularFunctionFieldBar p)) = 𝔛.Mη.ffEquiv.symm (algebraMap _ 𝔛.Mη.C.functionField
        ((𝔛.Mη.C.presheaf.germ ((𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hyU).hom (((𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))) := by
      rw [EvalMatch.algebraMap_germ_eq_germToFunctionField]
      apply Subtype.ext
      exact (hMη a).symm

    have hL1 := AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
      𝔛.Mη y ((𝔛.Mη.C.presheaf.germ ((𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hyU).hom (((𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))
    rw [← hMηa, hyV] at hL1
    obtain ⟨h1, hres1, -⟩ := hL1

    have hv1 : (Scheme.stalkClosedPointTo y.1).hom ((𝔛.Mη.C.presheaf.germ ((𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
        (y.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hyU).hom (((𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) =
        (Scheme.stalkClosedPointTo (y.1 ≫ 𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))))).hom (((DRModel p).presheaf.germ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) _ hyU').hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) :=
      (EvalMatch.stalkClosedPointTo_comp_germ y.1 (𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))))) ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) hyU' (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))).symm
    have hv2 : (Scheme.stalkClosedPointTo (y.1 ≫ 𝔛.eη ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))))).hom (((DRModel p).presheaf.germ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) _ hyU').hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) =
        (Scheme.stalkClosedPointTo (z ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))).hom (((DRModel p).presheaf.germ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) _ hgenU').hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) := by
      have key : ∀ (q₁ q₂ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ DRModel p) (e : q₁ = q₂)
          (h₁ : q₁.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (h₂ : q₂.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)),
          (Scheme.stalkClosedPointTo q₁).hom (((DRModel p).presheaf.germ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) _ h₁).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) =
            (Scheme.stalkClosedPointTo q₂).hom (((DRModel p).presheaf.germ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) _ h₂).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) := by
        rintro q₁ q₂ rfl h₁ h₂; rfl
      exact key _ _ hzt.symm hyU' hgenU'
    have hv3 : (Scheme.stalkClosedPointTo (z ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))).hom (((DRModel p).presheaf.germ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) _ hgenU').hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) =
        (Scheme.stalkClosedPointTo z).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (z.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hgenU).hom
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :=
      EvalMatch.stalkClosedPointTo_comp_germ z (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) hgenU' (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))
    have hv4 : val (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (t.1.base (IsLocalRing.closedPoint O)) hfin).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) = (Scheme.stalkClosedPointTo z).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
        (z.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hgenU).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) := by
      rw [hval]
      exact EvalMatch.map_stalkClosedPointTo_germ jK t.1 ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) hfin (by rw [← hz]; exact hgenU)
        (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))

    exact htransfer (rd (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (t.1.base (IsLocalRing.closedPoint O)) hfin).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))) (⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull p)).2⟩ : ↥(modularFunctionFieldBar p)) hff (val (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (t.1.base (IsLocalRing.closedPoint O)) hfin).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))) h1 (by rw [hres1, hv1, hv2, hv3, ← hv4])

  have Pclosure : ∀ r ∈ Subring.closure
      (Set.range (fun a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) => ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (t.1.base (IsLocalRing.closedPoint O)) hfin).hom
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) ∪
       Set.range (fun o : O => ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ (t.1.base (IsLocalRing.closedPoint O)) trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o)))), Pr r := by
    intro r hr
    induction hr using Subring.closure_induction with
    | mem r hr =>
      rcases hr with ⟨a, rfl⟩ | ⟨o, rfl⟩
      · exact Pchart a
      · exact Pconst o
    | zero => exact Pzero
    | one => exact Pone
    | add _ _ _ _ h₁ h₂ => exact Padd _ _ h₁ h₂
    | neg _ _ h => exact Pneg _ h
    | mul _ _ _ _ h₁ h₂ => exact Pmul _ _ h₁ h₂

  obtain ⟨u, w, hwu, hsw, hu, hw⟩ := AlgebraicGeometry.exists_isUnit_mul_eq_mem_closure_of_stalk_pullback
    (DRModel.toBase p) (TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) (TwoChartIntegralModel.ιFin_toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))
    (t.1.base (IsLocalRing.closedPoint O)) hfin s
  obtain ⟨hu1, eu⟩ := Pclosure u hu
  obtain ⟨hw1, ew⟩ := Pclosure w hw

  have hvw : val w ≠ 0 := by
    intro h0
    have hU : IsUnit (val w) := hwu.map val
    rw [h0] at hU
    exact not_isUnit_zero hU
  have hwunit : IsUnit (⟨rd w, hw1⟩ : V.toValuationSubring) := by
    by_contra hnu
    have hm : (⟨rd w, hw1⟩ : V.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [← IsLocalRing.residue_eq_zero_iff, ew] at hm
    exact hvw ((map_eq_zero_iff _ (algebraMap (AlgebraicClosure ℚ) V.ResidueField).injective).mp hm)
  obtain ⟨hw0, hwinv⟩ := (EvalMatch.isUnit_valuationSubring_mk_iff _ _ hw1).mp hwunit

  have hsw' : rd s * rd w = rd u := by rw [← map_mul, hsw]
  have hrds : rd s = rd u * (rd w)⁻¹ := by rw [← hsw', mul_inv_cancel_right₀ hw0]
  have hmemS : rd s ∈ V.toValuationSubring := by rw [hrds]; exact mul_mem hu1 hwinv
  have hresS : IsLocalRing.residue V.toValuationSubring ⟨rd s, hmemS⟩ =
      algebraMap (AlgebraicClosure ℚ) V.ResidueField (val s) := by
    have hprod : (⟨rd s, hmemS⟩ : V.toValuationSubring) * ⟨rd w, hw1⟩ = ⟨rd u, hu1⟩ := Subtype.ext hsw'
    have e := congrArg (IsLocalRing.residue V.toValuationSubring) hprod
    rw [map_mul, ew, eu] at e
    have hvals : val s * val w = val u := by rw [← map_mul, hsw]
    rw [← hvals, map_mul] at e
    exact mul_right_cancel₀ ((map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) V.ResidueField).injective).mpr hvw) e
  refine ⟨hmemS, ?_⟩
  show V.evalAt (rd s) = val s
  rw [Place.evalAt_of_mem _ hmemS, hresS]
  exact Place.residueInv_algebraMap _ _

end S_ModularCurve_DRModelPackage_evalAt_eq_stalkClosedPointTo_of_schemeHomOver
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_evalAt_eq_stalkClosedPointTo_of_schemeHomOver (solution)
