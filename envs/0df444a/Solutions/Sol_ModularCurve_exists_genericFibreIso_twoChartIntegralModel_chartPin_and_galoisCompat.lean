-- Prove2me | solution 1 for ModularCurve.exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/066ee1f9-57cc-5f2f-8be9-32e20cb8f478

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

open scoped TensorProduct

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace TwoChartGlueGal
namespace B

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve AlgebraicCurve AlgebraicCurve.CurveModel

section Emb

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) [Fact (j ≠ 0)]

private def emb : ↥F₀ →+* ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) :=
  ((coeffEmb (AlgebraicClosure ℚ)).comp (SubringClass.subtype F₀)).codRestrict
    (laurentBaseChange (AlgebraicClosure ℚ) F₀)
    fun x => coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2

private theorem emb_apply (x : ↥F₀) :
    emb F₀ x = ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩ := rfl

private theorem emb_jFull_inv : emb F₀ j⁻¹ = (emb F₀ j)⁻¹ := map_inv₀ _ _

private theorem jBar_ne_zero : (emb F₀ j) ≠ 0 := (map_ne_zero (emb F₀)).mpr Fact.out

private scoped instance factJBarNeZero : Fact ((emb F₀ j) ≠ 0) := ⟨jBar_ne_zero F₀ j⟩

end Emb

private theorem ringHom_apply_eq_ratCast {S : Subring ℚ} {R : Type*} [DivisionRing R] [Algebra ℚ R]
    (f : ↥S →+* R) (q : ↥S) : f q = ((q : ℚ) : R) := by
  have hd : (((q : ℚ).den : ℕ) : R) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ R)]
    exact (map_ne_zero (algebraMap ℚ R)).mpr (Nat.cast_ne_zero.mpr (q : ℚ).den_ne_zero)
  have hmul : f q * (((q : ℚ).den : ℕ) : R) = (((q : ℚ).num : ℤ) : R) := by
    rw [← map_natCast f, ← map_intCast f, ← map_mul]
    congr 1
    apply Subtype.ext
    push_cast
    exact Rat.mul_den_eq_num (q : ℚ)
  rw [Rat.cast_def, eq_div_iff hd, hmul]

section Charts

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) [Fact (j ≠ 0)] (p : ℕ)

private theorem emb_mem_adjoin {S : Set ↥F₀} {T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))}
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) {x : ↥F₀}
    (hx : x ∈ Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) S) :
    emb F₀ x ∈ Algebra.adjoin (AlgebraicClosure ℚ) T := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (hST x hx)
  | algebraMap r =>
      have h : emb F₀ (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀ r) =
          ((r : ℚ) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) :=
        ringHom_apply_eq_ratCast ((emb F₀).comp
          (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀)) r
      rw [h, ← map_ratCast (algebraMap (AlgebraicClosure ℚ) (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))]
      exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

private theorem emb_mem_chartRing {S : Set ↥F₀} {T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))}
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) {b : ↥F₀} (hb : b ∈ TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S) :
    emb F₀ b ∈ chartRing (AlgebraicClosure ℚ) T := by
  have hint : IsIntegral (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) S) b :=
    hb
  let ψ : ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) S) →+* ↥(Algebra.adjoin (AlgebraicClosure ℚ) T) :=
    ((emb F₀).comp (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) S).val.toRingHom).codRestrict
      (Algebra.adjoin (AlgebraicClosure ℚ) T).toSubring fun x => emb_mem_adjoin F₀ p hST x.2
  exact IsIntegral.map_of_comp_eq ψ (emb F₀) (RingHom.ext fun _ => rfl) hint

private def ρ (S : Set ↥F₀) (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) :
    ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S) →+* ↥(chartRing (AlgebraicClosure ℚ) T) where
  toFun b := ⟨emb F₀ b, emb_mem_chartRing F₀ p hST b.2⟩
  map_one' := Subtype.ext (by simp only [Subalgebra.coe_one, map_one])
  map_mul' a b := Subtype.ext (by simp only [Subalgebra.coe_mul, map_mul])
  map_zero' := Subtype.ext (by simp only [Subalgebra.coe_zero, map_zero])
  map_add' a b := Subtype.ext (by simp only [Subalgebra.coe_add, map_add])

private theorem coe_ρ_apply (S : Set ↥F₀) (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) (b : ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) :
    (ρ F₀ p S T hST b : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) = emb F₀ b := rfl

private theorem ρ_comp_algebraMap (S : Set ↥F₀) (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) :
    (ρ F₀ p S T hST).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) =
      (algebraMap (AlgebraicClosure ℚ) ↥(chartRing (AlgebraicClosure ℚ) T)).comp
        (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) := by
  refine RingHom.ext fun q => Subtype.ext ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, coe_ρ_apply]
  have h1 : emb F₀ (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀ q) =
      ((q : ℚ) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) :=
    ringHom_apply_eq_ratCast ((emb F₀).comp
      (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀)) q
  have h2 : algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) q =
      ((q : ℚ) : AlgebraicClosure ℚ) :=
    ringHom_apply_eq_ratCast (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) q
  rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, h1, h2, map_ratCast]

private theorem fin_sub : ∀ s ∈ ({j} : Set ↥F₀),
    emb F₀ s ∈ ({(emb F₀ j)} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) := by
  intro s hs
  rw [Set.mem_singleton_iff] at hs ⊢
  rw [hs]

private theorem inf_sub : ∀ s ∈ ({j⁻¹} : Set ↥F₀),
    emb F₀ s ∈ ({(emb F₀ j)⁻¹} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) := by
  intro s hs
  rw [Set.mem_singleton_iff] at hs ⊢
  rw [hs, emb_jFull_inv]

private theorem mid_sub : ∀ s ∈ ({j, j⁻¹} : Set ↥F₀),
    emb F₀ s ∈ ({(emb F₀ j), (emb F₀ j)⁻¹} :
      Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) := by
  intro s hs
  rcases hs with rfl | hs
  · exact Set.mem_insert _ _
  · rw [Set.mem_singleton_iff] at hs
    rw [hs, emb_jFull_inv]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

private abbrev ρFin : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) →+*
    ↥(chartRing (AlgebraicClosure ℚ) ({(emb F₀ j)} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) :=
  ρ F₀ p _ _ (fin_sub F₀ j)

private abbrev ρInf : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) →+*
    ↥(chartRing (AlgebraicClosure ℚ) ({(emb F₀ j)⁻¹} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) :=
  ρ F₀ p _ _ (inf_sub F₀ j)

private abbrev ρMid : ↥(TwoChartIntegralModel.chartAlgMid ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) →+*
    ↥(chartRing (AlgebraicClosure ℚ) ({(emb F₀ j),
      (emb F₀ j)⁻¹} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) :=
  ρ F₀ p _ _ (mid_sub F₀ j)

private theorem jb_subset_pair : ({(emb F₀ j)} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ⊆
    {(emb F₀ j), (emb F₀ j)⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert _ _)

private theorem jb_inv_subset_pair :
    ({(emb F₀ j)⁻¹} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ⊆
      {(emb F₀ j), (emb F₀ j)⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ (Set.mem_singleton _))

private theorem square_fin :
    (AlgebraicCurve.CurveModel.chartIncl (AlgebraicClosure ℚ) (jb_subset_pair F₀ j)).toRingHom.comp (ρFin F₀ j p) =
      (ρMid F₀ j p).comp (TwoChartIntegralModel.inclFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).toRingHom := by
  refine RingHom.ext fun b => Subtype.ext ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [AlgebraicCurve.CurveModel.coe_chartIncl, coe_ρ_apply, coe_ρ_apply,
    TwoChartIntegralModel.coe_chartIncl]

private theorem square_inf :
    (AlgebraicCurve.CurveModel.chartIncl (AlgebraicClosure ℚ) (jb_inv_subset_pair F₀ j)).toRingHom.comp (ρInf F₀ j p) =
      (ρMid F₀ j p).comp (TwoChartIntegralModel.inclInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).toRingHom := by
  refine RingHom.ext fun b => Subtype.ext ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [AlgebraicCurve.CurveModel.coe_chartIncl, coe_ρ_apply, coe_ρ_apply,
    TwoChartIntegralModel.coe_chartIncl]

end Charts

section Schemes

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) [Fact (j ≠ 0)] (p : ℕ)

local notation "Qb" => AlgebraicClosure ℚ
local notation "jb" => (emb F₀ j)

private abbrev uFin : X₀ Qb jb ⟶ TwoChartIntegralModel.XFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j := Spec.map (CommRingCat.ofHom (ρFin F₀ j p))

private abbrev uInf : CurveModel.XInf Qb jb ⟶ TwoChartIntegralModel.XInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j :=
  Spec.map (CommRingCat.ofHom (ρInf F₀ j p))

private abbrev uMid : XOverlap Qb jb ⟶ TwoChartIntegralModel.XMid ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j := Spec.map (CommRingCat.ofHom (ρMid F₀ j p))

private theorem f₀_uFin : f₀ Qb jb ≫ uFin F₀ j p = uMid F₀ j p ≫ TwoChartIntegralModel.fFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j := by
  simp only [f₀, uFin, uMid, TwoChartIntegralModel.fFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (square_fin F₀ j p)

private theorem fInf_uInf : CurveModel.fInf Qb jb ≫ uInf F₀ j p = uMid F₀ j p ≫ TwoChartIntegralModel.fInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j := by
  simp only [CurveModel.fInf, uInf, uMid, TwoChartIntegralModel.fInf, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (square_inf F₀ j p)

private theorem glue_compat :
    f₀ Qb jb ≫ (uFin F₀ j p ≫ TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) =
      CurveModel.fInf Qb jb ≫ (uInf F₀ j p ≫ TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) := by
  rw [← Category.assoc, f₀_uFin, ← Category.assoc, fInf_uInf, Category.assoc, Category.assoc,
    TwoChartIntegralModel.glue_condition]

private def u : glued Qb jb ⟶ TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j :=
  pushout.desc (uFin F₀ j p ≫ TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (uInf F₀ j p ≫ TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
    (glue_compat F₀ j p)

@[reassoc]
private theorem ι₀_u : ι₀ Qb jb ≫ u F₀ j p = uFin F₀ j p ≫ TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j :=
  pushout.inl_desc _ _ _

@[reassoc]
private theorem ιInf_u : CurveModel.ιInf Qb jb ≫ u F₀ j p = uInf F₀ j p ≫ TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j :=
  pushout.inr_desc _ _ _

private abbrev baseMap : Spec (CommRingCat.of Qb) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)) :=
  Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) Qb))

private theorem uFin_base :
    uFin F₀ j p ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j))) =
      Spec.map (CommRingCat.ofHom (algebraMap Qb ↥(chartRing Qb ({jb} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))))) ≫
        baseMap p := by
  simp only [uFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (ρ_comp_algebraMap F₀ p _ _ (fin_sub F₀ j))

private theorem uInf_base :
    uInf F₀ j p ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j))) =
      Spec.map (CommRingCat.ofHom (algebraMap Qb ↥(chartRing Qb ({jb⁻¹} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))))) ≫
        baseMap p := by
  simp only [uInf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (ρ_comp_algebraMap F₀ p _ _ (inf_sub F₀ j))

private theorem u_igusaTo : u F₀ j p ≫ TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j = gluedToBase Qb jb ≫ baseMap p := by
  refine pushout.hom_ext (f := f₀ Qb jb) (g := CurveModel.fInf Qb jb) ?_ ?_
  · change ι₀ Qb jb ≫ u F₀ j p ≫ TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j = ι₀ Qb jb ≫ gluedToBase Qb jb ≫ baseMap p
    rw [ι₀_u_assoc, TwoChartIntegralModel.ιFin_toBase, uFin_base, ι₀_gluedToBase_assoc]
  · change CurveModel.ιInf Qb jb ≫ u F₀ j p ≫ TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j =
      CurveModel.ιInf Qb jb ≫ gluedToBase Qb jb ≫ baseMap p
    rw [ιInf_u_assoc, TwoChartIntegralModel.ιInf_toBase, uInf_base, ιInf_gluedToBase_assoc]

private def eη : glued Qb jb ⟶ pullback (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p) :=
  pullback.lift (u F₀ j p) (gluedToBase Qb jb) (u_igusaTo F₀ j p)

@[reassoc (attr := simp)]
private theorem eη_fst : eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p) = u F₀ j p := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem eη_snd : eη F₀ j p ≫ pullback.snd (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p) = gluedToBase Qb jb :=
  pullback.lift_snd _ _ _

private theorem ι₀_eη_fst :
    ι₀ Qb jb ≫ eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p) =
      uFin F₀ j p ≫ TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j := by
  rw [eη_fst, ι₀_u]

private theorem ιInf_eη_fst :
    CurveModel.ιInf Qb jb ≫ eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p) =
      uInf F₀ j p ≫ TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j := by
  rw [eη_fst, ιInf_u]

end Schemes

section ChartMatch

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) [Fact (j ≠ 0)] (p : ℕ)

local notation "Qb" => AlgebraicClosure ℚ
local notation "jb" => (emb F₀ j)

private theorem ig_ιFin_eq_ιInf_iff (x₀ : TwoChartIntegralModel.XFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (xi : TwoChartIntegralModel.XInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) :
    (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).base x₀ = (TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).base xi ↔
      ∃ w : TwoChartIntegralModel.XMid ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j,
        (TwoChartIntegralModel.fFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).base w = x₀ ∧ (TwoChartIntegralModel.fInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (F := span (TwoChartIntegralModel.fFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (TwoChartIntegralModel.fInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · exact match fi, fj, h₁, h₂ with
        | .init _, .init _, h₁, h₂ => ⟨w, h₁, h₂⟩
    · exact nomatch fj
    · exact nomatch fi
  · rintro ⟨w, rfl, rfl⟩
    change (TwoChartIntegralModel.fFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j ≫ TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).base w =
      (TwoChartIntegralModel.fInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j ≫ TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).base w
    rw [TwoChartIntegralModel.glue_condition]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem ig_range_fInf : Set.range (TwoChartIntegralModel.fInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).base =
    ((PrimeSpectrum.basicOpen (TwoChartIntegralModel.jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j))) : Set (PrimeSpectrum ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j))) := by
  letI := (TwoChartIntegralModel.inclInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).toRingHom.toAlgebra
  haveI := TwoChartIntegralModel.isLocalization_away_inclInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j
  exact PrimeSpectrum.localization_away_comap_range ↥(TwoChartIntegralModel.chartAlgMid ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (TwoChartIntegralModel.jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)

private theorem ig_ιInf_mem_range_ιFin_iff (xi : TwoChartIntegralModel.XInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) :
    (TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).base xi ∈ Set.range (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).base ↔
      TwoChartIntegralModel.jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← ig_range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (ig_ιFin_eq_ιInf_iff F₀ j p x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(TwoChartIntegralModel.fFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).base w, (ig_ιFin_eq_ιInf_iff F₀ j p _ _).mpr ⟨w, rfl, rfl⟩⟩

private theorem ρInf_jInvChartInf : ρInf F₀ j p (TwoChartIntegralModel.jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) = tInvChart Qb jb := by
  apply Subtype.ext
  rw [coe_ρ_apply, TwoChartIntegralModel.coe_jInvChartInf, emb_jFull_inv, coe_tInvChart]

private theorem uInf_asIdeal (z : CurveModel.XInf Qb jb) :
    ((uInf F₀ j p).base z).asIdeal = z.asIdeal.comap (ρInf F₀ j p) := rfl

private theorem u_mem_range_ιFin_iff (y : glued Qb jb) :
    (u F₀ j p).base y ∈ Set.range (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).base ↔ y ∈ Set.range (ι₀ Qb jb).base := by
  rcases mem_range_ι₀_or_mem_range_ιInf Qb jb y with ⟨x₀, rfl⟩ | ⟨z, rfl⟩
  · refine ⟨fun _ => ⟨x₀, rfl⟩, fun _ => ⟨(uFin F₀ j p).base x₀, ?_⟩⟩
    change (uFin F₀ j p ≫ TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).base x₀ = (ι₀ Qb jb ≫ u F₀ j p).base x₀
    rw [ι₀_u]
  · have hz : (u F₀ j p).base ((CurveModel.ιInf Qb jb).base z) =
        (TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).base ((uInf F₀ j p).base z) := by
      change (CurveModel.ιInf Qb jb ≫ u F₀ j p).base z = (uInf F₀ j p ≫ TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).base z
      rw [ιInf_u]
    rw [hz, ig_ιInf_mem_range_ιFin_iff, ιInf_mem_range_ι₀_iff, uInf_asIdeal, Ideal.mem_comap,
      ρInf_jInvChartInf]

end ChartMatch

section Model

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) [Fact (j ≠ 0)]

private def Mη (htrans : Transcendental (AlgebraicClosure ℚ) (emb F₀ j))
    (hfd : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(emb F₀ j)} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (hfd_inv : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(emb F₀ j)⁻¹} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) :
    CurveModel (AlgebraicClosure ℚ) (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) :=
  haveI := hfd
  haveI := hfd_inv
  CurveModel.ofGenerator (AlgebraicClosure ℚ) (emb F₀ j) htrans

end Model

section Tensor

open scoped TensorProduct

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) [Fact (j ≠ 0)] (p : ℕ)

private local instance instAlgebraRatLocalizedChartRing (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) :
    Algebra ↥(GaloisRep.ratLocalizedAt p) ↥(chartRing (AlgebraicClosure ℚ) T) :=
  ((algebraMap (AlgebraicClosure ℚ) ↥(chartRing (AlgebraicClosure ℚ) T)).comp
    (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))).toAlgebra

set_option synthInstance.maxHeartbeats 1600000 in

private def ρAlg (S : Set ↥F₀) (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) :
    ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S) →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartRing (AlgebraicClosure ℚ) T) :=
  { ρ F₀ p S T hST with
    commutes' := fun q => RingHom.congr_fun (ρ_comp_algebraMap F₀ p S T hST) q }

set_option synthInstance.maxHeartbeats 1600000 in

private def incAlg (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) :
    AlgebraicClosure ℚ →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartRing (AlgebraicClosure ℚ) T) :=
  { algebraMap (AlgebraicClosure ℚ) ↥(chartRing (AlgebraicClosure ℚ) T) with
    commutes' := fun _ => rfl }

set_option synthInstance.maxHeartbeats 1600000 in

private def θ (S : Set ↥F₀) (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) :
    (↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S) ⊗[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ) →+*
      ↥(chartRing (AlgebraicClosure ℚ) T) :=
  (Algebra.TensorProduct.lift (ρAlg F₀ p S T hST) (incAlg F₀ p T) fun _ _ => Commute.all _ _).toRingHom

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θ_tmul (S : Set ↥F₀) (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) (b : ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) (c : AlgebraicClosure ℚ) :
    θ F₀ p S T hST (b ⊗ₜ c) = ρ F₀ p S T hST b * algebraMap (AlgebraicClosure ℚ) _ c :=
  Algebra.TensorProduct.lift_tmul (ρAlg F₀ p S T hST) (incAlg F₀ p T) _ b c

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θ_comp_includeLeft (S : Set ↥F₀) (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) :
    (θ F₀ p S T hST).comp Algebra.TensorProduct.includeLeftRingHom = ρ F₀ p S T hST := by
  refine RingHom.ext fun b => ?_
  rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, θ_tmul, map_one, mul_one]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem θ_comp_includeRight (S : Set ↥F₀) (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) :
    (θ F₀ p S T hST).comp
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
          AlgebraicClosure ℚ →ₐ[↥(GaloisRep.ratLocalizedAt p)]
            ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S) ⊗[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ)) =
      algebraMap (AlgebraicClosure ℚ) ↥(chartRing (AlgebraicClosure ℚ) T) := by
  refine RingHom.ext fun c => ?_
  simpa using θ_tmul F₀ p S T hST 1 c

set_option synthInstance.maxHeartbeats 1600000 in

private abbrev θFin := θ F₀ p _ _ (fin_sub F₀ j)

set_option synthInstance.maxHeartbeats 1600000 in

private abbrev θInf := θ F₀ p _ _ (inf_sub F₀ j)

end Tensor

section TensorLeft

open scoped TensorProduct

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ)

private abbrev cm (S : Set ↥F₀) :=
  Algebra.TensorProduct.comm ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private def θL (S : Set ↥F₀) (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) :
    (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →ₐ[AlgebraicClosure ℚ] ↥(chartRing (AlgebraicClosure ℚ) T) where
  toRingHom := (θ F₀ p S T hST).comp (cm F₀ p S : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) ≃+* _).toRingHom
  commutes' c := by
    show θ F₀ p S T hST ((1 : ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) ⊗ₜ c) = algebraMap (AlgebraicClosure ℚ) _ c
    rw [θ_tmul, map_one, one_mul]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_apply (S : Set ↥F₀) (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) (x : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S))) :
    θL F₀ p S T hST x = θ F₀ p S T hST (cm F₀ p S x) := rfl

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_tmul (S : Set ↥F₀) (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) (c : AlgebraicClosure ℚ) (b : ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) :
    θL F₀ p S T hST (c ⊗ₜ b) = ρ F₀ p S T hST b * algebraMap (AlgebraicClosure ℚ) _ c :=
  θ_tmul F₀ p S T hST b c

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_one_tmul (S : Set ↥F₀) (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) (b : ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) :
    θL F₀ p S T hST (1 ⊗ₜ b) = ρ F₀ p S T hST b := by
  rw [θL_tmul, map_one, mul_one]

end TensorLeft

section Consumption

open scoped TensorProduct

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem ringHom_eq_θL (S : Set ↥F₀) (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T)
    (e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →ₐ[AlgebraicClosure ℚ] ↥(chartRing (AlgebraicClosure ℚ) T))
    (he : ∀ b : ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S),
      ((e (1 ⊗ₜ b) : ↥(chartRing (AlgebraicClosure ℚ) T)) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) = emb F₀ b)
    (y : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S))) :
    (e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) y = (θL F₀ p S T hST : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ((e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)).map_zero).trans ((θL F₀ p S T hST : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)).map_zero).symm
  | tmul c b =>
    have hA : (e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) (algebraMap (AlgebraicClosure ℚ) _ c) =
        (θL F₀ p S T hST : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) (algebraMap (AlgebraicClosure ℚ) _ c) :=
      (e.commutes c).trans ((θL F₀ p S T hST).commutes c).symm
    have hB : (e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) (1 ⊗ₜ b) = (θL F₀ p S T hST : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) (1 ⊗ₜ b) :=
      (Subtype.ext ((he b).trans (coe_ρ_apply F₀ p S T hST b).symm)).trans (θL_one_tmul F₀ p S T hST b).symm
    have hc : (c ⊗ₜ b : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S))) = algebraMap (AlgebraicClosure ℚ) _ c * (1 ⊗ₜ b) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    exact (congrArg (e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) hc).trans (((e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)).map_mul _ _).trans
      ((congr (congrArg (@HMul.hMul _ _ _ _) hA) hB).trans (((θL F₀ p S T hST : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)).map_mul _ _).symm.trans
        (congrArg (θL F₀ p S T hST : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) hc.symm))))
  | add x y hx hy =>
    exact ((e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)).map_add x y).trans
      ((congr (congrArg (@HAdd.hAdd _ _ _ _) hx) hy).trans ((θL F₀ p S T hST : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)).map_add x y).symm)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem algHom_apply_eq_θL (S : Set ↥F₀) (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T)
    (e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →ₐ[AlgebraicClosure ℚ] ↥(chartRing (AlgebraicClosure ℚ) T))
    (he : ∀ b : ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S),
      ((e (1 ⊗ₜ b) : ↥(chartRing (AlgebraicClosure ℚ) T)) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) = emb F₀ b)
    (x : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S))) : e x = θL F₀ p S T hST x :=
  ringHom_eq_θL F₀ p S T hST e he x

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem θ_bijective_of_algEquiv (S : Set ↥F₀) (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T)
    (e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) ≃ₐ[AlgebraicClosure ℚ] ↥(chartRing (AlgebraicClosure ℚ) T))
    (he : ∀ b : ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S),
      ((e (1 ⊗ₜ b) : ↥(chartRing (AlgebraicClosure ℚ) T)) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) = emb F₀ b) :
    Function.Bijective (θ F₀ p S T hST) := by
  have hL : ∀ x, θL F₀ p S T hST x = e x := fun x =>
    (algHom_apply_eq_θL F₀ p S T hST (e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) →ₐ[AlgebraicClosure ℚ] ↥(chartRing (AlgebraicClosure ℚ) T)) he x).symm
  have hcm : ∀ x, θL F₀ p S T hST ((cm F₀ p S).symm x) = θ F₀ p S T hST x := fun x =>
    (θL_apply F₀ p S T hST _).trans (congrArg (θ F₀ p S T hST) ((cm F₀ p S).apply_symm_apply x))
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · have h' : e ((cm F₀ p S).symm x) = e ((cm F₀ p S).symm y) :=
      ((hL _).symm.trans ((hcm x).trans (hxy.trans ((hcm y).symm.trans (hL _)))))
    exact (cm F₀ p S).symm.injective (e.injective h')
  · obtain ⟨w, hw⟩ := e.surjective z
    exact ⟨cm F₀ p S w, (θL_apply F₀ p S T hST w).symm.trans ((hL w).trans hw)⟩

end Consumption

section Iso

open scoped TensorProduct

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) [Fact (j ≠ 0)] (p : ℕ)

local notation "Qb" => AlgebraicClosure ℚ
local notation "jb" => (emb F₀ j)

private abbrev PFin := pullback (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p))

private abbrev PInf := pullback (TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p))

private def φFin : X₀ Qb jb ⟶ PFin F₀ j p :=
  pullback.lift (uFin F₀ j p) (ι₀ Qb jb ≫ eη F₀ j p) (by rw [Category.assoc, ι₀_eη_fst])

private def φInf : CurveModel.XInf Qb jb ⟶ PInf F₀ j p :=
  pullback.lift (uInf F₀ j p) (CurveModel.ιInf Qb jb ≫ eη F₀ j p) (by rw [Category.assoc, ιInf_eη_fst])

@[reassoc (attr := simp)]
private theorem φFin_fst : φFin F₀ j p ≫ pullback.fst _ _ = uFin F₀ j p := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem φFin_snd : φFin F₀ j p ≫ pullback.snd _ _ = ι₀ Qb jb ≫ eη F₀ j p := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
private theorem φInf_fst : φInf F₀ j p ≫ pullback.fst _ _ = uInf F₀ j p := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem φInf_snd : φInf F₀ j p ≫ pullback.snd _ _ = CurveModel.ιInf Qb jb ≫ eη F₀ j p := pullback.lift_snd _ _ _

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem SpecMap_θFin_eq :
    Spec.map (CommRingCat.ofHom (θFin F₀ j p)) ≫
        (pullbackSpecIso ↥(GaloisRep.ratLocalizedAt p) ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) Qb).inv =
      φFin F₀ j p ≫ (pullbackRightPullbackFstIso (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p) (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)).hom ≫
        (pullback.congrHom (TwoChartIntegralModel.ιFin_toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      θ_comp_includeLeft]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, φFin_fst]
    try rfl
  · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [θ_comp_includeRight F₀ p _ _ (fin_sub F₀ j)]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd, φFin_snd_assoc, eη_snd, ι₀_gluedToBase]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem SpecMap_θInf_eq :
    Spec.map (CommRingCat.ofHom (θInf F₀ j p)) ≫
        (pullbackSpecIso ↥(GaloisRep.ratLocalizedAt p) ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) Qb).inv =
      φInf F₀ j p ≫ (pullbackRightPullbackFstIso (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p) (TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)).hom ≫
        (pullback.congrHom (TwoChartIntegralModel.ιInf_toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      θ_comp_includeLeft]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, φInf_fst]
    try rfl
  · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [θ_comp_includeRight F₀ p _ _ (inf_sub F₀ j)]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd, φInf_snd_assoc, eη_snd, ιInf_gluedToBase]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isIso_φFin (hfin : Function.Bijective (θFin F₀ j p)) : IsIso (φFin F₀ j p) := by
  haveI : IsIso (Spec.map (CommRingCat.ofHom
      (R := ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ {j}) ⊗[↥(GaloisRep.ratLocalizedAt p)] Qb)
      (θFin F₀ j p))) :=
    isIso_SpecMap_iff.mpr (by rwa [CommRingCat.hom_ofHom])
  haveI : IsIso (φFin F₀ j p ≫
      (pullbackRightPullbackFstIso (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p) (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)).hom ≫
        (pullback.congrHom (TwoChartIntegralModel.ιFin_toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) rfl).hom) := by
    rw [← SpecMap_θFin_eq]
    infer_instance
  exact IsIso.of_isIso_comp_right (φFin F₀ j p)
    ((pullbackRightPullbackFstIso (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p) (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)).hom ≫
      (pullback.congrHom (TwoChartIntegralModel.ιFin_toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) rfl).hom)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isIso_φInf (hinf : Function.Bijective (θInf F₀ j p)) : IsIso (φInf F₀ j p) := by
  haveI : IsIso (Spec.map (CommRingCat.ofHom
      (R := ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ {j⁻¹}) ⊗[↥(GaloisRep.ratLocalizedAt p)] Qb)
      (θInf F₀ j p))) :=
    isIso_SpecMap_iff.mpr (by rwa [CommRingCat.hom_ofHom])
  haveI : IsIso (φInf F₀ j p ≫
      (pullbackRightPullbackFstIso (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p) (TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)).hom ≫
        (pullback.congrHom (TwoChartIntegralModel.ιInf_toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) rfl).hom) := by
    rw [← SpecMap_θInf_eq]
    infer_instance
  exact IsIso.of_isIso_comp_right (φInf F₀ j p)
    ((pullbackRightPullbackFstIso (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p) (TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)).hom ≫
      (pullback.congrHom (TwoChartIntegralModel.ιInf_toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) rfl).hom)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isOpenImmersion_ι₀_eη (hfin : Function.Bijective (θFin F₀ j p)) :
    IsOpenImmersion (ι₀ Qb jb ≫ eη F₀ j p) := by
  haveI := isIso_φFin F₀ j p hfin
  rw [← φFin_snd]
  infer_instance

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isOpenImmersion_ιInf_eη (hinf : Function.Bijective (θInf F₀ j p)) :
    IsOpenImmersion (CurveModel.ιInf Qb jb ≫ eη F₀ j p) := by
  haveI := isIso_φInf F₀ j p hinf
  rw [← φInf_snd]
  infer_instance

set_option synthInstance.maxHeartbeats 1600000 in

private theorem u_eq_of_eη_eq {y y' : glued Qb jb} (h : eη F₀ j p y = eη F₀ j p y') : u F₀ j p y = u F₀ j p y' := by
  have h1 := congrArg (pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p)) h
  rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, eη_fst] at h1

set_option synthInstance.maxHeartbeats 1600000 in
private theorem injective_eη (hfin : Function.Bijective (θFin F₀ j p)) (hinf : Function.Bijective (θInf F₀ j p)) :
    Function.Injective (eη F₀ j p) := by
  intro y y' h
  have hu := u_eq_of_eη_eq F₀ j p h

  have hu' : (u F₀ j p).base y = (u F₀ j p).base y' := hu
  have hsame : y ∈ Set.range (ι₀ Qb jb).base ↔ y' ∈ Set.range (ι₀ Qb jb).base := by
    rw [← u_mem_range_ιFin_iff F₀ j p y, ← u_mem_range_ιFin_iff F₀ j p y', hu']
  by_cases hy : y ∈ Set.range (ι₀ Qb jb).base
  · obtain ⟨a, rfl⟩ := hy
    obtain ⟨a', rfl⟩ := hsame.mp ⟨a, rfl⟩
    haveI := isOpenImmersion_ι₀_eη F₀ j p hfin
    have : (ι₀ Qb jb ≫ eη F₀ j p) a = (ι₀ Qb jb ≫ eη F₀ j p) a' := h
    rw [(ι₀ Qb jb ≫ eη F₀ j p).isOpenEmbedding.injective this]
  · have hy' : y' ∉ Set.range (ι₀ Qb jb).base := fun h' => hy (hsame.mpr h')
    obtain ⟨a, rfl⟩ := (mem_range_ι₀_or_mem_range_ιInf Qb jb y).resolve_left hy
    obtain ⟨a', rfl⟩ := (mem_range_ι₀_or_mem_range_ιInf Qb jb y').resolve_left hy'
    haveI := isOpenImmersion_ιInf_eη F₀ j p hinf
    have : (CurveModel.ιInf Qb jb ≫ eη F₀ j p) a = (CurveModel.ιInf Qb jb ≫ eη F₀ j p) a' := h
    rw [(CurveModel.ιInf Qb jb ≫ eη F₀ j p).isOpenEmbedding.injective this]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem surjective_eη (hfin : Function.Bijective (θFin F₀ j p)) (hinf : Function.Bijective (θInf F₀ j p)) :
    Function.Surjective (eη F₀ j p) := by
  intro pt
  rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j (pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p) pt) with hp | hp
  ·
    have hp' : pt ∈ Set.range (pullback.snd (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
        (pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p))) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact hp
    obtain ⟨r, rfl⟩ := hp'
    haveI := isIso_φFin F₀ j p hfin
    obtain ⟨a, rfl⟩ := (φFin F₀ j p).homeomorph.surjective r
    exact ⟨ι₀ Qb jb a, by
      show (ι₀ Qb jb ≫ eη F₀ j p) a = (φFin F₀ j p ≫ pullback.snd _ _) a
      rw [φFin_snd]⟩
  · have hp' : pt ∈ Set.range (pullback.snd (TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
        (pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p))) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact hp
    obtain ⟨r, rfl⟩ := hp'
    haveI := isIso_φInf F₀ j p hinf
    obtain ⟨a, rfl⟩ := (φInf F₀ j p).homeomorph.surjective r
    exact ⟨CurveModel.ιInf Qb jb a, by
      show (CurveModel.ιInf Qb jb ≫ eη F₀ j p) a = (φInf F₀ j p ≫ pullback.snd _ _) a
      rw [φInf_snd]⟩

set_option synthInstance.maxHeartbeats 1600000 in

private theorem isIso_eη_of_bijective (hfin : Function.Bijective (θFin F₀ j p)) (hinf : Function.Bijective (θInf F₀ j p)) :
    IsIso (eη F₀ j p) := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨?_, ⟨surjective_eη F₀ j p hfin hinf⟩⟩
  refine IsOpenImmersion.of_forall_source_exists _ (injective_eη F₀ j p hfin hinf) fun y => ?_
  rcases mem_range_ι₀_or_mem_range_ιInf Qb jb y with hy | hy
  · exact ⟨_, ι₀ Qb jb, inferInstance, hy, isOpenImmersion_ι₀_eη F₀ j p hfin⟩
  · exact ⟨_, CurveModel.ιInf Qb jb, inferInstance, hy, isOpenImmersion_ιInf_eη F₀ j p hinf⟩

end Iso

end TwoChartGlueGal.B
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B"
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B"

noncomputable section

open ModularCurve AlgebraicCurve AlgebraicCurve.CurveModel

namespace TwoChartGlueGal
namespace H

open TwoChartGlueGal.B
open scoped TensorProduct

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem adjoin_range_ρ_eq_top (S : Set ↥F₀) (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (hST : ∀ s ∈ S, emb F₀ s ∈ T) (hθ : Function.Surjective (θ F₀ p S T hST)) :
    Algebra.adjoin (AlgebraicClosure ℚ) (Set.range (ρ F₀ p S T hST)) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨t, rfl⟩ := hθ y
  induction t using TensorProduct.induction_on with
  | zero => rw [(θ F₀ p S T hST).map_zero]; exact zero_mem _
  | tmul b c =>
      rw [θ_tmul]
      exact mul_mem (Algebra.subset_adjoin ⟨b, rfl⟩) (Subalgebra.algebraMap_mem _ c)
  | add x y hx hy => rw [(θ F₀ p S T hST).map_add]; exact add_mem hx hy

end TwoChartGlueGal.H
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B"
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B"

set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve AlgebraicCurve.CurveModel IsDedekindDomain IntermediateField

open scoped Pointwise

universe u

namespace TwoChartGlueGal
namespace C

variable {L : Type u} [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
variable (g : L ≃ₐ[ℚ] L)

private theorem arithmeticRingAut_symm_apply (x : ↥(laurentBaseChange L F₀)) :
    (arithmeticRingAut F₀ g).symm x = arithmeticRingAut F₀ g.symm x :=
  rfl

private theorem galois_smul_eq (x : ↥(laurentBaseChange L F₀)) :
    arithmeticGalois F₀ g • x = arithmeticRingAut F₀ g x :=
  rfl

private theorem galois_inv_smul_eq (x : ↥(laurentBaseChange L F₀)) :
    (arithmeticGalois F₀ g)⁻¹ • x = (arithmeticRingAut F₀ g).symm x :=
  rfl

variable {F₀ g} in
private theorem symm_fix {s : ↥(laurentBaseChange L F₀)} (hs : arithmeticRingAut F₀ g s = s) :
    (arithmeticRingAut F₀ g).symm s = s :=
  (arithmeticRingAut F₀ g).symm_apply_eq.mpr hs.symm

variable {F₀ g} in
private theorem arithmeticRingAut_mem_adjoin {s : ↥(laurentBaseChange L F₀)}
    (hs : arithmeticRingAut F₀ g s = s) {x : ↥(laurentBaseChange L F₀)}
    (hx : x ∈ Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀))) :
    arithmeticRingAut F₀ g x ∈ Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀)) := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    rw [hx, hs]
    exact Algebra.subset_adjoin rfl
  | algebraMap a =>
    rw [arithmeticRingAut_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact mul_mem hx hy

variable {F₀ g} in

private theorem arithmeticRingAut_mem_chartRing {s : ↥(laurentBaseChange L F₀)}
    (hs : arithmeticRingAut F₀ g s = s) {x : ↥(laurentBaseChange L F₀)}
    (hx : x ∈ chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) :
    arithmeticRingAut F₀ g x ∈ chartRing L ({s} : Set ↥(laurentBaseChange L F₀)) := by
  obtain ⟨p, hp, hx0⟩ :=
    (id hx : IsIntegral ↥(Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀))) x)
  let ψ : ↥(Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀))) →+*
      ↥(Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀))) :=
    ((arithmeticRingAut F₀ g).toRingHom.comp
      (Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀))).val.toRingHom).codRestrict
      (Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀)))
      fun a => arithmeticRingAut_mem_adjoin hs a.2
  have hψ : (algebraMap ↥(Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀)))
      ↥(laurentBaseChange L F₀)).comp ψ =
      (arithmeticRingAut F₀ g).toRingHom.comp
        (algebraMap ↥(Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀)))
          ↥(laurentBaseChange L F₀)) :=
    RingHom.ext fun _ => rfl
  refine ⟨p.map ψ, hp.map ψ, ?_⟩
  rw [Polynomial.eval₂_map, hψ]
  have key := Polynomial.hom_eval₂ p
    (algebraMap ↥(Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀))) ↥(laurentBaseChange L F₀))
    (arithmeticRingAut F₀ g).toRingHom x
  rw [hx0, map_zero] at key
  exact key.symm

variable {F₀ g} in

private def chartAut {s : ↥(laurentBaseChange L F₀)} (hs : arithmeticRingAut F₀ g s = s) :
    ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) ≃+*
      ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) where
  toFun a := ⟨arithmeticRingAut F₀ g a, arithmeticRingAut_mem_chartRing hs a.2⟩
  invFun a := ⟨(arithmeticRingAut F₀ g).symm a,
    arithmeticRingAut_mem_chartRing (g := g.symm)
      (show arithmeticRingAut F₀ g.symm s = s from symm_fix hs) a.2⟩
  left_inv a := Subtype.ext
    ((arithmeticRingAut F₀ g).symm_apply_apply (a : ↥(laurentBaseChange L F₀)))
  right_inv a := Subtype.ext
    ((arithmeticRingAut F₀ g).apply_symm_apply (a : ↥(laurentBaseChange L F₀)))
  map_mul' a b := Subtype.ext
    (map_mul (arithmeticRingAut F₀ g) (a : ↥(laurentBaseChange L F₀)) (b : ↥(laurentBaseChange L F₀)))
  map_add' a b := Subtype.ext
    (map_add (arithmeticRingAut F₀ g) (a : ↥(laurentBaseChange L F₀)) (b : ↥(laurentBaseChange L F₀)))

variable {F₀ g} in
@[scoped simp]
private theorem coe_chartAut {s : ↥(laurentBaseChange L F₀)} (hs : arithmeticRingAut F₀ g s = s)
    (a : ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀)))) :
    (chartAut hs a : ↥(laurentBaseChange L F₀)) = arithmeticRingAut F₀ g a :=
  rfl

variable {F₀ g} in
@[scoped simp]
private theorem coe_chartAut_symm {s : ↥(laurentBaseChange L F₀)} (hs : arithmeticRingAut F₀ g s = s)
    (a : ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀)))) :
    ((chartAut hs).symm a : ↥(laurentBaseChange L F₀)) = (arithmeticRingAut F₀ g).symm a :=
  rfl

variable {F₀ g} in
private theorem chartAut_symm_algebraMap {s : ↥(laurentBaseChange L F₀)}
    (hs : arithmeticRingAut F₀ g s = s) (c : L) :
    (chartAut hs).symm (algebraMap L ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) c) =
      algebraMap L ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) (g.symm c) := by
  apply Subtype.ext
  show (arithmeticRingAut F₀ g).symm (algebraMap L ↥(laurentBaseChange L F₀) c) =
    algebraMap L ↥(laurentBaseChange L F₀) (g.symm c)
  exact arithmeticRingAut_algebraMap F₀ g.symm c

private theorem mem_nonunits_smul_iff (h : SemilinearAut L ↥(laurentBaseChange L F₀))
    (O : ValuationSubring ↥(laurentBaseChange L F₀)) (x : ↥(laurentBaseChange L F₀)) :
    x ∈ (h • O).nonunits ↔ h⁻¹ • x ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, smul_inv'', smul_eq_zero_iff_eq]

variable {F₀ g} in

private theorem smul_mem_chartPlaces {s : ↥(laurentBaseChange L F₀)} (hs : arithmeticRingAut F₀ g s = s)
    {v : Place L ↥(laurentBaseChange L F₀)} (hv : v ∈ chartPlaces L s) :
    arithmeticGalois F₀ g • v ∈ chartPlaces L s := by
  show s ∈ (arithmeticGalois F₀ g • v).toValuationSubring
  rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    galois_inv_smul_eq, symm_fix hs]
  exact hv

set_option synthInstance.maxHeartbeats 1600000 in

private scoped instance (priority := high) isScalarTower_chartRing (S : Set ↥(laurentBaseChange L F₀)) :
    IsScalarTower L ↥(chartRing L S) ↥(laurentBaseChange L F₀) :=
  ⟨fun a b c => by
    show a • (b : ↥(laurentBaseChange L F₀)) * c = a • ((b : ↥(laurentBaseChange L F₀)) * c)
    rw [Algebra.smul_def, Algebra.smul_def, mul_assoc]⟩

section Dictionary

variable [CharZero L] (s : ↥(laurentBaseChange L F₀))
  [FiniteDimensional L⟮s⟯ ↥(laurentBaseChange L F₀)]

private theorem mem_prime_iff_nonunits {v : Place L ↥(laurentBaseChange L F₀)} (hv : v ∈ chartPlaces L s)
    (a : ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀)))) :
    a ∈ ((primeEquivChartPlaces L s).symm ⟨v, hv⟩).asIdeal ↔
      (a : ↥(laurentBaseChange L F₀)) ∈ v.toValuationSubring.nonunits := by
  have hv𝔭 : Place.ofHeightOneSpectrum (K := L) ((primeEquivChartPlaces L s).symm ⟨v, hv⟩) = v :=
    congrArg Subtype.val ((primeEquivChartPlaces L s).apply_symm_apply ⟨v, hv⟩)
  have hO : v.toValuationSubring =
      (((primeEquivChartPlaces L s).symm ⟨v, hv⟩).valuation ↥(laurentBaseChange L F₀)).valuationSubring :=
    (congrArg Place.toValuationSubring hv𝔭).symm
  rw [hO, ValuationSubring.mem_nonunits_iff,
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := ↥(laurentBaseChange L F₀))]
  exact (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one

variable {s} in

private theorem prime_smul (hs : arithmeticRingAut F₀ g s = s)
    {v : Place L ↥(laurentBaseChange L F₀)} (hv : v ∈ chartPlaces L s) :
    ((primeEquivChartPlaces L s).symm ⟨arithmeticGalois F₀ g • v, smul_mem_chartPlaces hs hv⟩).asIdeal =
      Ideal.map (chartAut hs) ((primeEquivChartPlaces L s).symm ⟨v, hv⟩).asIdeal := by
  ext a
  rw [mem_prime_iff_nonunits F₀ s, ← Ideal.comap_symm, Ideal.mem_comap, mem_prime_iff_nonunits F₀ s,
    SemilinearAut.smul_toValuationSubring, mem_nonunits_smul_iff]
  rfl

variable {s} in

private theorem ofHeightOneSpectrum_eq_smul (hs : arithmeticRingAut F₀ g s = s)
    (𝔭 𝔭' : HeightOneSpectrum ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))))
    (h : 𝔭'.asIdeal = Ideal.map (chartAut hs) 𝔭.asIdeal) :
    Place.ofHeightOneSpectrum (K := L) (F := ↥(laurentBaseChange L F₀)) 𝔭' =
      arithmeticGalois F₀ g •
        Place.ofHeightOneSpectrum (K := L) (F := ↥(laurentBaseChange L F₀)) 𝔭 := by
  have h𝔭 : (primeEquivChartPlaces L s).symm ⟨Place.ofHeightOneSpectrum (K := L) 𝔭,
      mem_ofHeightOneSpectrum L s 𝔭⟩ = 𝔭 :=
    (primeEquivChartPlaces L s).symm_apply_apply 𝔭
  have key := prime_smul F₀ g hs (mem_ofHeightOneSpectrum L s 𝔭)
  rw [h𝔭, ← h] at key
  have h𝔭' : (primeEquivChartPlaces L s).symm
      ⟨arithmeticGalois F₀ g • Place.ofHeightOneSpectrum (K := L) 𝔭,
        smul_mem_chartPlaces hs (mem_ofHeightOneSpectrum L s 𝔭)⟩ = 𝔭' :=
    HeightOneSpectrum.ext key
  have := congrArg Subtype.val ((primeEquivChartPlaces L s).apply_symm_apply
    ⟨arithmeticGalois F₀ g • Place.ofHeightOneSpectrum (K := L) 𝔭,
      smul_mem_chartPlaces hs (mem_ofHeightOneSpectrum L s 𝔭)⟩)
  rw [h𝔭'] at this
  exact this

end Dictionary
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B"

variable {F₀ g} in

private def conjAlgHom {s : ↥(laurentBaseChange L F₀)} (hs : arithmeticRingAut F₀ g s = s)
    (φ : ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) →ₐ[L] L) :
    ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) →ₐ[L] L :=
  { (g : L →+* L).comp (φ.toRingHom.comp (chartAut hs).symm.toRingHom) with
    commutes' := fun c => by
      show g (φ ((chartAut hs).symm
        (algebraMap L ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) c))) = algebraMap L L c
      rw [chartAut_symm_algebraMap, AlgHom.commutes, Algebra.algebraMap_self_apply,
        Algebra.algebraMap_self_apply]
      exact g.apply_symm_apply c }

variable {F₀ g} in
private theorem conjAlgHom_apply {s : ↥(laurentBaseChange L F₀)} (hs : arithmeticRingAut F₀ g s = s)
    (φ : ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) →ₐ[L] L)
    (a : ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀)))) :
    conjAlgHom hs φ a = g (φ ((chartAut hs).symm a)) :=
  rfl

variable {F₀ g} in

private theorem ker_conjAlgHom {s : ↥(laurentBaseChange L F₀)} (hs : arithmeticRingAut F₀ g s = s)
    (φ : ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) →ₐ[L] L) :
    RingHom.ker (conjAlgHom hs φ) = Ideal.map (chartAut hs) (RingHom.ker φ) := by
  ext a
  rw [RingHom.mem_ker, conjAlgHom_apply, map_eq_zero_iff g g.injective, ← Ideal.comap_symm,
    Ideal.mem_comap, RingHom.mem_ker]

variable {F₀ g} in

private theorem eq_conjAlgHom_of_eqOn {s : ↥(laurentBaseChange L F₀)} (hs : arithmeticRingAut F₀ g s = s)
    {T : Set ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀)))}
    (hT : Algebra.adjoin L T = ⊤) (hfix : ∀ t ∈ T, chartAut hs t = t)
    (φ φ' : ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) →ₐ[L] L)
    (hconj : ∀ t ∈ T, φ' t = g (φ t)) :
    φ' = conjAlgHom hs φ := by
  refine AlgHom.ext_of_adjoin_eq_top hT fun t ht => ?_
  show φ' t = g (φ ((chartAut hs).symm t))
  rw [hconj t ht, (chartAut hs).symm_apply_eq.mpr (hfix t ht).symm]

variable {F₀ g} in

private theorem ofHeightOneSpectrum_ker_eq_smul [CharZero L] {s : ↥(laurentBaseChange L F₀)}
    [FiniteDimensional L⟮s⟯ ↥(laurentBaseChange L F₀)]
    (hs : arithmeticRingAut F₀ g s = s)
    {T : Set ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀)))}
    (hT : Algebra.adjoin L T = ⊤) (hfix : ∀ t ∈ T, chartAut hs t = t)
    (φ φ' : ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) →ₐ[L] L)
    (hconj : ∀ t ∈ T, φ' t = g (φ t))
    (𝔭 𝔭' : HeightOneSpectrum ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))))
    (h𝔭 : 𝔭.asIdeal = RingHom.ker φ) (h𝔭' : 𝔭'.asIdeal = RingHom.ker φ') :
    Place.ofHeightOneSpectrum (K := L) (F := ↥(laurentBaseChange L F₀)) 𝔭' =
      arithmeticGalois F₀ g •
        Place.ofHeightOneSpectrum (K := L) (F := ↥(laurentBaseChange L F₀)) 𝔭 := by
  refine ofHeightOneSpectrum_eq_smul F₀ g hs 𝔭 𝔭' ?_
  rw [h𝔭', h𝔭, eq_conjAlgHom_of_eqOn hs hT hfix φ φ' hconj, ker_conjAlgHom]

end TwoChartGlueGal.C
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.C"
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.C"

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicCurve.CurveModel IsDedekindDomain IntermediateField

universe u

namespace TwoChartGlueGal
namespace P

section Cancel

variable {A B : Type u} [CommRing A] [CommRing B] {X : Scheme.{u}}

private theorem ringHom_eq_of_SpecMap_comp_eq (ι : Spec (CommRingCat.of A) ⟶ X) [Mono ι] (ψ ψ' : A →+* B)
    (h : Spec.map (CommRingCat.ofHom ψ') ≫ ι = Spec.map (CommRingCat.ofHom ψ) ≫ ι) : ψ' = ψ := by
  have h1 : Spec.map (CommRingCat.ofHom ψ') = Spec.map (CommRingCat.ofHom ψ) := (cancel_mono ι).mp h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

private theorem ringHom_eq_comp_of_SpecMap_comp (ι : Spec (CommRingCat.of A) ⟶ X) [Mono ι]
    (ψ ψ' : A →+* B) (g : B →+* B)
    (h : Spec.map (CommRingCat.ofHom ψ') ≫ ι =
      Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ ι) :
    ψ' = g.comp ψ := by
  apply ringHom_eq_of_SpecMap_comp_eq ι
  rw [h, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

end Cancel
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.C"

section AlgHom

variable (K : Type u) [Field K]

private def _root_.TwoChartGlueGal.P.toAlgHom {R : Type u} [CommRing R] [Algebra K R] (φ : R →+* K)
    (hφ : φ.comp (algebraMap K R) = RingHom.id K) : R →ₐ[K] K :=
  { φ with commutes' := fun c => RingHom.congr_fun hφ c }

p2m_export "TwoChartGlueGal.P" "toAlgHom"
@[scoped simp]
private theorem toAlgHom_toRingHom {R : Type u} [CommRing R] [Algebra K R] (φ : R →+* K)
    (hφ : φ.comp (algebraMap K R) = RingHom.id K) : (toAlgHom K φ hφ).toRingHom = φ :=
  rfl

end AlgHom
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.C"

section Points

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
  [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

private theorem exists_algHom_eq_SpecMap_comp_ι₀ (ht : Transcendental K t)
    (x : {p : Spec (CommRingCat.of K) ⟶ (ofGenerator K t ht).C // p ≫ (ofGenerator K t ht).toBase = 𝟙 _})
    (hx : x.1 (IsLocalRing.closedPoint K) ∈ Set.range (ι₀ K t)) :
    ∃ φ : ↥(chartRing K ({t} : Set L)) →ₐ[K] K,
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ι₀ K t = x.1 := by
  have hrange : Set.range x.1 ⊆ Set.range (ι₀ K t) := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [hp]
    exact hx
  have hfac := IsOpenImmersion.lift_fac (ι₀ K t) x.1 hrange
  have h1 : IsOpenImmersion.lift (ι₀ K t) x.1 hrange ≫ (ι₀ K t ≫ gluedToBase K t) = 𝟙 _ := by
    rw [← Category.assoc, hfac]
    exact x.2
  rw [ι₀_gluedToBase, ← Spec.map_preimage (IsOpenImmersion.lift (ι₀ K t) x.1 hrange),
    ← Spec.map_comp] at h1
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective (h1.trans (Spec.map_id _).symm))
  refine ⟨toAlgHom K (Spec.preimage (IsOpenImmersion.lift (ι₀ K t) x.1 hrange)).hom h2, ?_⟩
  rw [toAlgHom_toRingHom, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

private theorem pointEquivPlace_of_eq_SpecMap_comp_ι₀ [IsAlgClosed K] (ht : Transcendental K t)
    (x : {p : Spec (CommRingCat.of K) ⟶ (ofGenerator K t ht).C // p ≫ (ofGenerator K t ht).toBase = 𝟙 _})
    (φ : ↥(chartRing K ({t} : Set L)) →ₐ[K] K)
    (hx : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ι₀ K t = x.1) :
    ∃ 𝔭 : HeightOneSpectrum ↥(chartRing K ({t} : Set L)),
      𝔭.asIdeal = RingHom.ker φ.toRingHom ∧
      (ofGenerator K t ht).pointEquivPlace x = Place.ofHeightOneSpectrum (K := K) (F := L) 𝔭 := by
  have hpt : x.1 (IsLocalRing.closedPoint K) =
      ι₀ K t (Spec.map (CommRingCat.ofHom φ.toRingHom) (IsLocalRing.closedPoint K)) := by
    rw [← hx]
    rfl
  have hx₀ : (Spec.map (CommRingCat.ofHom φ.toRingHom) (IsLocalRing.closedPoint K)).asIdeal =
      RingHom.ker φ.toRingHom := by
    show Ideal.comap φ.toRingHom (IsLocalRing.maximalIdeal K) = RingHom.ker φ.toRingHom
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  have hc : ι₀ K t (Spec.map (CommRingCat.ofHom φ.toRingHom) (IsLocalRing.closedPoint K)) ∈
      closedPoints (glued K t) := by
    have h2 := (pointEquivClosedPoint (ofGenerator K t ht).toBase x).2
    have h3 : ((pointEquivClosedPoint (ofGenerator K t ht).toBase x : (ofGenerator K t ht).C)) =
        ι₀ K t (Spec.map (CommRingCat.ofHom φ.toRingHom) (IsLocalRing.closedPoint K)) := hpt
    rw [h3] at h2
    exact h2
  refine ⟨primeOfι₀ K t ht _ hc, hx₀, ?_⟩
  rw [pointEquivPlace_apply]
  have h4 : pointEquivClosedPoint (ofGenerator K t ht).toBase x =
      (⟨ι₀ K t (Spec.map (CommRingCat.ofHom φ.toRingHom) (IsLocalRing.closedPoint K)), hc⟩ :
        closedPoints (glued K t)) :=
    Subtype.ext hpt
  rw [h4]
  exact gluedPlaceOfPoint_ι₀ K t ht _ hc

private theorem exists_algHom_eq_SpecMap_comp_ιInf (ht : Transcendental K t)
    (x : {p : Spec (CommRingCat.of K) ⟶ (ofGenerator K t ht).C // p ≫ (ofGenerator K t ht).toBase = 𝟙 _})
    (hx : x.1 (IsLocalRing.closedPoint K) ∈ Set.range (ιInf K t)) :
    ∃ φ : ↥(chartRing K ({t⁻¹} : Set L)) →ₐ[K] K,
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ιInf K t = x.1 := by
  have hrange : Set.range x.1 ⊆ Set.range (ιInf K t) := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [hp]
    exact hx
  have hfac := IsOpenImmersion.lift_fac (ιInf K t) x.1 hrange
  have h1 : IsOpenImmersion.lift (ιInf K t) x.1 hrange ≫ (ιInf K t ≫ gluedToBase K t) = 𝟙 _ := by
    rw [← Category.assoc, hfac]
    exact x.2
  rw [ιInf_gluedToBase, ← Spec.map_preimage (IsOpenImmersion.lift (ιInf K t) x.1 hrange),
    ← Spec.map_comp] at h1
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective (h1.trans (Spec.map_id _).symm))
  refine ⟨toAlgHom K (Spec.preimage (IsOpenImmersion.lift (ιInf K t) x.1 hrange)).hom h2, ?_⟩
  rw [toAlgHom_toRingHom, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

private theorem pointEquivPlace_of_eq_SpecMap_comp_ιInf [IsAlgClosed K] (ht : Transcendental K t)
    (x : {p : Spec (CommRingCat.of K) ⟶ (ofGenerator K t ht).C // p ≫ (ofGenerator K t ht).toBase = 𝟙 _})
    (φ : ↥(chartRing K ({t⁻¹} : Set L)) →ₐ[K] K)
    (hx : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ιInf K t = x.1)
    (h₀ : x.1 (IsLocalRing.closedPoint K) ∉ Set.range (ι₀ K t)) :
    ∃ 𝔭 : HeightOneSpectrum ↥(chartRing K ({t⁻¹} : Set L)),
      𝔭.asIdeal = RingHom.ker φ.toRingHom ∧
      (ofGenerator K t ht).pointEquivPlace x = Place.ofHeightOneSpectrum (K := K) (F := L) 𝔭 := by
  have hpt : x.1 (IsLocalRing.closedPoint K) =
      ιInf K t (Spec.map (CommRingCat.ofHom φ.toRingHom) (IsLocalRing.closedPoint K)) := by
    rw [← hx]
    rfl
  have hx₀ : (Spec.map (CommRingCat.ofHom φ.toRingHom) (IsLocalRing.closedPoint K)).asIdeal =
      RingHom.ker φ.toRingHom := by
    show Ideal.comap φ.toRingHom (IsLocalRing.maximalIdeal K) = RingHom.ker φ.toRingHom
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  have hc : x.1 (IsLocalRing.closedPoint K) ∈ closedPoints (glued K t) :=
    (pointEquivClosedPoint (ofGenerator K t ht).toBase x).2
  refine ⟨primeOfιInf K t ht (Spec.map (CommRingCat.ofHom φ.toRingHom) (IsLocalRing.closedPoint K))
    (by rw [← hpt]; exact hc), hx₀, ?_⟩
  rw [pointEquivPlace_apply]
  exact gluedPlaceOfPoint_of_not_mem K t ht ⟨x.1 (IsLocalRing.closedPoint K), hc⟩ h₀ _ hpt.symm

end Points
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.C"

end TwoChartGlueGal.P
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.C P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.P"
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.C"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.C P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.P"

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve AlgebraicCurve AlgebraicCurve.CurveModel

namespace TwoChartGlueGal
namespace G

open TwoChartGlueGal.B TwoChartGlueGal.C TwoChartGlueGal.P

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) [Fact (j ≠ 0)] (p : ℕ)

local notation "Qb" => AlgebraicClosure ℚ
local notation "jb" => (emb F₀ j)

private theorem arithmeticRingAut_jBar (g : Qb ≃ₐ[ℚ] Qb) :
    arithmeticRingAut F₀ g jb = jb :=
  Subtype.ext (coeffMap_coeffEmb g _)

private theorem arithmeticRingAut_jBar_inv (g : Qb ≃ₐ[ℚ] Qb) :
    arithmeticRingAut F₀ g jb⁻¹ = jb⁻¹ := by
  rw [map_inv₀, arithmeticRingAut_jBar]

private theorem chartAut_ρFin (g : Qb ≃ₐ[ℚ] Qb)
    (hs : arithmeticRingAut F₀ g jb = jb) :
    ∀ t ∈ Set.range (ρFin F₀ j p), chartAut hs t = t := by
  rintro _ ⟨b, rfl⟩
  exact Subtype.ext (Subtype.ext (coeffMap_coeffEmb g _))

private theorem chartAut_ρInf (g : Qb ≃ₐ[ℚ] Qb)
    (hs : arithmeticRingAut F₀ g jb⁻¹ = jb⁻¹) :
    ∀ t ∈ Set.range (ρInf F₀ j p), chartAut hs t = t := by
  rintro _ ⟨b, rfl⟩
  exact Subtype.ext (Subtype.ext (coeffMap_coeffEmb g _))

private theorem eη_fst_closedPoint (q : Spec (CommRingCat.of Qb) ⟶ CurveModel.glued Qb jb) :
    (q ≫ eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p)) (IsLocalRing.closedPoint Qb) =
      (u F₀ j p) (q (IsLocalRing.closedPoint Qb)) := by
  rw [eη_fst]
  rfl

private theorem SpecMap_ι₀_eη_fst
    (ψ : ↥(chartRing Qb ({jb} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) →+* Qb) :
    Spec.map (CommRingCat.ofHom ψ) ≫ ι₀ Qb jb ≫ eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p) =
      Spec.map (CommRingCat.ofHom (ψ.comp (ρFin F₀ j p))) ≫ TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j := by
  rw [ι₀_eη_fst, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

private theorem SpecMap_ιInf_eη_fst
    (ψ : ↥(chartRing Qb ({jb⁻¹} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) →+* Qb) :
    Spec.map (CommRingCat.ofHom ψ) ≫ CurveModel.ιInf Qb jb ≫ eη F₀ j p ≫
        pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p) =
      Spec.map (CommRingCat.ofHom (ψ.comp (ρInf F₀ j p))) ≫ TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j := by
  rw [ιInf_eη_fst, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

variable (htrans : Transcendental (AlgebraicClosure ℚ) (emb F₀ j))
    (hfd : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(emb F₀ j)} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (hfd_inv : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(emb F₀ j)⁻¹} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))

private theorem u_closedPoint_eq (g : Qb ≃ₐ[ℚ] Qb)
    (x x' : {q : Spec (CommRingCat.of Qb) ⟶ (Mη F₀ j htrans hfd hfd_inv).C // q ≫ (Mη F₀ j htrans hfd hfd_inv).toBase = 𝟙 _})
    (h : x'.1 ≫ eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ =
      Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ x.1 ≫ eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _) :
    (u F₀ j p) (x'.1 (IsLocalRing.closedPoint Qb)) = (u F₀ j p) (x.1 (IsLocalRing.closedPoint Qb)) :=
  calc (u F₀ j p) (x'.1 (IsLocalRing.closedPoint Qb))
      = (x'.1 ≫ eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _) (IsLocalRing.closedPoint Qb) :=
        (eη_fst_closedPoint F₀ j p x'.1).symm
    _ = (Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ x.1 ≫ eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _)
          (IsLocalRing.closedPoint Qb) := by rw [h]
    _ = (x.1 ≫ eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _)
          (Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) (IsLocalRing.closedPoint Qb)) := rfl
    _ = (x.1 ≫ eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _) (IsLocalRing.closedPoint Qb) := by
        rw [Subsingleton.elim (α := PrimeSpectrum Qb)
          (Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) (IsLocalRing.closedPoint Qb))
          (IsLocalRing.closedPoint Qb)]
    _ = (u F₀ j p) (x.1 (IsLocalRing.closedPoint Qb)) := eη_fst_closedPoint F₀ j p x.1

private theorem hgal_fin (g : Qb ≃ₐ[ℚ] Qb)
    (hAfin : Algebra.adjoin Qb (Set.range (ρFin F₀ j p)) = ⊤)
    (x x' : {q : Spec (CommRingCat.of Qb) ⟶ (Mη F₀ j htrans hfd hfd_inv).C // q ≫ (Mη F₀ j htrans hfd hfd_inv).toBase = 𝟙 _})
    (h : x'.1 ≫ eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ =
      Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ x.1 ≫ eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _)
    (hx : x.1 (IsLocalRing.closedPoint Qb) ∈ Set.range (ι₀ Qb jb))
    (hx' : x'.1 (IsLocalRing.closedPoint Qb) ∈ Set.range (ι₀ Qb jb)) :
    (Mη F₀ j htrans hfd hfd_inv).pointEquivPlace x' =
      arithmeticGalois (L := Qb) F₀ g • (Mη F₀ j htrans hfd hfd_inv).pointEquivPlace x := by
  haveI := hfd
  haveI := hfd_inv
  obtain ⟨φ, hφ⟩ := exists_algHom_eq_SpecMap_comp_ι₀ Qb jb htrans x hx
  obtain ⟨φ', hφ'⟩ := exists_algHom_eq_SpecMap_comp_ι₀ Qb jb htrans x' hx'
  obtain ⟨𝔭, h𝔭, hx𝔭⟩ := pointEquivPlace_of_eq_SpecMap_comp_ι₀ Qb jb htrans x φ hφ
  obtain ⟨𝔭', h𝔭', hx𝔭'⟩ := pointEquivPlace_of_eq_SpecMap_comp_ι₀ Qb jb htrans x' φ' hφ'
  have h1 : (Spec.map (CommRingCat.ofHom φ'.toRingHom) ≫ ι₀ Qb jb) ≫ eη F₀ j p ≫
      pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p) =
      Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        ι₀ Qb jb) ≫ eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p) := by
    rw [hφ, hφ']
    exact h
  simp only [Category.assoc] at h1
  rw [SpecMap_ι₀_eη_fst, SpecMap_ι₀_eη_fst] at h1
  have hP2 := ringHom_eq_comp_of_SpecMap_comp (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ _ _ h1
  have hconj : ∀ t ∈ Set.range (ρFin F₀ j p), φ' t = g (φ t) := by
    rintro _ ⟨b, rfl⟩
    exact RingHom.congr_fun hP2 b
  refine hx𝔭'.trans (Eq.trans ?_
    (congrArg (arithmeticGalois (L := Qb) F₀ g • ·) hx𝔭).symm)
  exact ofHeightOneSpectrum_ker_eq_smul (arithmeticRingAut_jBar F₀ j g) hAfin
    (chartAut_ρFin F₀ j p g (arithmeticRingAut_jBar F₀ j g)) φ φ' hconj 𝔭 𝔭' h𝔭 h𝔭'

private theorem hgal_inf (g : Qb ≃ₐ[ℚ] Qb)
    (hAinf : Algebra.adjoin Qb (Set.range (ρInf F₀ j p)) = ⊤)
    (x x' : {q : Spec (CommRingCat.of Qb) ⟶ (Mη F₀ j htrans hfd hfd_inv).C // q ≫ (Mη F₀ j htrans hfd hfd_inv).toBase = 𝟙 _})
    (h : x'.1 ≫ eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ =
      Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ x.1 ≫ eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _)
    (hx : x.1 (IsLocalRing.closedPoint Qb) ∉ Set.range (ι₀ Qb jb))
    (hx' : x'.1 (IsLocalRing.closedPoint Qb) ∉ Set.range (ι₀ Qb jb)) :
    (Mη F₀ j htrans hfd hfd_inv).pointEquivPlace x' =
      arithmeticGalois (L := Qb) F₀ g • (Mη F₀ j htrans hfd hfd_inv).pointEquivPlace x := by
  haveI := hfd
  haveI := hfd_inv
  obtain ⟨φ, hφ⟩ := exists_algHom_eq_SpecMap_comp_ιInf Qb jb htrans x
    (mem_range_ιInf_of_not_mem_range_ι₀ Qb jb hx)
  obtain ⟨φ', hφ'⟩ := exists_algHom_eq_SpecMap_comp_ιInf Qb jb htrans x'
    (mem_range_ιInf_of_not_mem_range_ι₀ Qb jb hx')
  obtain ⟨𝔭, h𝔭, hx𝔭⟩ :=
    pointEquivPlace_of_eq_SpecMap_comp_ιInf Qb jb htrans x φ hφ hx
  obtain ⟨𝔭', h𝔭', hx𝔭'⟩ :=
    pointEquivPlace_of_eq_SpecMap_comp_ιInf Qb jb htrans x' φ' hφ' hx'
  have h1 : (Spec.map (CommRingCat.ofHom φ'.toRingHom) ≫ CurveModel.ιInf Qb jb) ≫ eη F₀ j p ≫
      pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p) =
      Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        CurveModel.ιInf Qb jb) ≫ eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (baseMap p) := by
    rw [hφ, hφ']
    exact h
  simp only [Category.assoc] at h1
  rw [SpecMap_ιInf_eη_fst, SpecMap_ιInf_eη_fst] at h1
  have hP2 := ringHom_eq_comp_of_SpecMap_comp (TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ _ _ h1
  have hconj : ∀ t ∈ Set.range (ρInf F₀ j p), φ' t = g (φ t) := by
    rintro _ ⟨b, rfl⟩
    exact RingHom.congr_fun hP2 b
  refine hx𝔭'.trans (Eq.trans ?_
    (congrArg (arithmeticGalois (L := Qb) F₀ g • ·) hx𝔭).symm)
  exact ofHeightOneSpectrum_ker_eq_smul (arithmeticRingAut_jBar_inv F₀ j g) hAinf
    (chartAut_ρInf F₀ j p g (arithmeticRingAut_jBar_inv F₀ j g)) φ φ' hconj 𝔭 𝔭' h𝔭 h𝔭'

private theorem hgal
    (hAfin : Algebra.adjoin Qb (Set.range (ρFin F₀ j p)) = ⊤)
    (hAinf : Algebra.adjoin Qb (Set.range (ρInf F₀ j p)) = ⊤)
    (hP3 : ∀ y : CurveModel.glued Qb jb,
      (u F₀ j p) y ∈ Set.range (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) ↔ y ∈ Set.range (ι₀ Qb jb)) :
    ∀ (g : Qb ≃ₐ[ℚ] Qb)
      (x x' : {q : Spec (CommRingCat.of Qb) ⟶ (Mη F₀ j htrans hfd hfd_inv).C // q ≫ (Mη F₀ j htrans hfd hfd_inv).toBase = 𝟙 _}),
      x'.1 ≫ eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ =
        Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ x.1 ≫ eη F₀ j p ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ →
      (Mη F₀ j htrans hfd hfd_inv).pointEquivPlace x' =
        arithmeticGalois (L := Qb) F₀ g • (Mη F₀ j htrans hfd hfd_inv).pointEquivPlace x := by
  intro g x x' h
  have hsame : x.1 (IsLocalRing.closedPoint Qb) ∈ Set.range (ι₀ Qb jb) ↔
      x'.1 (IsLocalRing.closedPoint Qb) ∈ Set.range (ι₀ Qb jb) := by

    have h2 := hP3 (x'.1 (IsLocalRing.closedPoint Qb))
    rw [u_closedPoint_eq F₀ j p htrans hfd hfd_inv g x x' h] at h2
    exact (hP3 (x.1 (IsLocalRing.closedPoint Qb))).symm.trans h2
  by_cases hx : x.1 (IsLocalRing.closedPoint Qb) ∈ Set.range (ι₀ Qb jb)
  · exact hgal_fin F₀ j p htrans hfd hfd_inv g hAfin x x' h hx (hsame.mp hx)
  · exact hgal_inf F₀ j p htrans hfd hfd_inv g hAinf x x' h hx (fun hx' => hx (hsame.mpr hx'))
end TwoChartGlueGal.G
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.C P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.P"
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.C P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.P"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.C P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.P"

namespace TwoChartGlueGal
namespace Pin

private theorem algEquiv_comp_includeRight_eq_ρ (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ) (S : Set ↥F₀)
    (T : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) (hST : ∀ s ∈ S, TwoChartGlueGal.B.emb F₀ s ∈ T)
    (e : ((AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S)) ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) T))
    (he : ∀ b : ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S),
      ((e (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) T)) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) = TwoChartGlueGal.B.emb F₀ b) :
    e.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt p)) (A := AlgebraicClosure ℚ)
          (B := ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ S))).toRingHom =
      TwoChartGlueGal.B.ρ F₀ p S T hST :=
  RingHom.ext fun b => Subtype.ext ((he b).trans (TwoChartGlueGal.B.coe_ρ_apply F₀ p S T hST b).symm)

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) [Fact (j ≠ 0)] (p : ℕ)

private theorem ι₀_pin
    (e : ((AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({(TwoChartGlueGal.B.emb F₀ j)} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))))))
    (he : (∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j), ((e (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({(TwoChartGlueGal.B.emb F₀ j)} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))))) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))
      = TwoChartGlueGal.B.emb F₀ b)) :
    AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) (TwoChartGlueGal.B.emb F₀ j) ≫ TwoChartGlueGal.B.eη F₀ j p ≫
      pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ =
    Spec.map (CommRingCat.ofHom (e.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight
        (R := ↥(GaloisRep.ratLocalizedAt p)) (A := AlgebraicClosure ℚ)
        (B := ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j))).toRingHom)) ≫ TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j :=
  (TwoChartGlueGal.B.ι₀_eη_fst F₀ j p).trans
    (congrArg (fun h => Spec.map (CommRingCat.ofHom h) ≫ TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
      (algEquiv_comp_includeRight_eq_ρ F₀ p _ _ (TwoChartGlueGal.B.fin_sub F₀ j) e he).symm)

private theorem ιInf_pin
    (e : ((AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({(TwoChartGlueGal.B.emb F₀ j)⁻¹} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))))))
    (he : (∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j), ((e (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({(TwoChartGlueGal.B.emb F₀ j)⁻¹} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))))) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))
      = TwoChartGlueGal.B.emb F₀ b)) :
    AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ) (TwoChartGlueGal.B.emb F₀ j) ≫ TwoChartGlueGal.B.eη F₀ j p ≫
      pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ =
    Spec.map (CommRingCat.ofHom (e.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight
        (R := ↥(GaloisRep.ratLocalizedAt p)) (A := AlgebraicClosure ℚ)
        (B := ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j))).toRingHom)) ≫ TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j :=
  (TwoChartGlueGal.B.ιInf_eη_fst F₀ j p).trans
    (congrArg (fun h => Spec.map (CommRingCat.ofHom h) ≫ TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
      (algEquiv_comp_includeRight_eq_ρ F₀ p _ _ (TwoChartGlueGal.B.inf_sub F₀ j) e he).symm)

end TwoChartGlueGal.Pin
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.C P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.P"
p2m_reactivate "P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.B P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.C P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat.TwoChartGlueGal.P"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ) [Fact p.Prime] (j : ↥F₀) [Fact (j ≠ 0)]
    (jb : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hjb : (jb : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((j : ↥F₀) : LaurentSeries ℚ))
    (htrans : Transcendental (AlgebraicClosure ℚ) jb)
    [hne : Fact (jb ≠ 0)]
    [hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    [hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    (eFin : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
        ≃ₐ[AlgebraicClosure ℚ] ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))))
    (hFin : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j),
        ((eFin (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) =
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥F₀).2⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
    (eInf : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
        ≃ₐ[AlgebraicClosure ℚ] ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))))
    (hInf : ∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j),
        ((eInf (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) =
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥F₀).2⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) :
    let Mη : CurveModel (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) :=
      CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans
    ∃ (eη : Mη.C ⟶ pullback (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) (_ : IsIso eη),
      eη ≫ pullback.snd (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ = Mη.toBase ∧
      (AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) jb ≫ eη ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ =
        Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt p)) (A := AlgebraicClosure ℚ) (B := ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j))).toRingHom)) ≫
          TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) ∧
      (AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ) jb ≫ eη ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ =
        Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt p)) (A := AlgebraicClosure ℚ) (B := ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j))).toRingHom)) ≫
          TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
        x'.1 ≫ eη ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ eη ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _ →
        Mη.pointEquivPlace x' =
          arithmeticGalois (L := AlgebraicClosure ℚ) F₀ σ • Mη.pointEquivPlace x := by
  obtain rfl : jb = TwoChartGlueGal.B.emb F₀ j := Subtype.ext hjb
  intro Mη
  have hbF : Function.Bijective (TwoChartGlueGal.B.θFin F₀ j p) :=
    TwoChartGlueGal.B.θ_bijective_of_algEquiv F₀ p _ _ (TwoChartGlueGal.B.fin_sub F₀ j) eFin hFin
  have hbI : Function.Bijective (TwoChartGlueGal.B.θInf F₀ j p) :=
    TwoChartGlueGal.B.θ_bijective_of_algEquiv F₀ p _ _ (TwoChartGlueGal.B.inf_sub F₀ j) eInf hInf
  exact ⟨TwoChartGlueGal.B.eη F₀ j p, TwoChartGlueGal.B.isIso_eη_of_bijective F₀ j p hbF hbI, TwoChartGlueGal.B.eη_snd F₀ j p,
    TwoChartGlueGal.Pin.ι₀_pin F₀ j p eFin hFin, TwoChartGlueGal.Pin.ιInf_pin F₀ j p eInf hInf,
    TwoChartGlueGal.G.hgal F₀ j p htrans hfd hfd_inv
      (TwoChartGlueGal.H.adjoin_range_ρ_eq_top F₀ p _ _ (TwoChartGlueGal.B.fin_sub F₀ j) hbF.2)
      (TwoChartGlueGal.H.adjoin_range_ρ_eq_top F₀ p _ _ (TwoChartGlueGal.B.inf_sub F₀ j) hbI.2)
      (fun y => TwoChartGlueGal.B.u_mem_range_ιFin_iff F₀ j p y)⟩

end
end S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat
end P2MW
export P2MW.S_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat (solution)
