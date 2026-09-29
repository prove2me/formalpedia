-- Prove2me | solution 1 for ModularCurve.exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/843172bb-eaa2-564f-97c8-68415980a794

import Theorems.Thm_AlgebraicCurve_CurveModel_placeOfPoint_ofGenerator_iota0_comap
import Theorems.Thm_AlgebraicCurve_CurveModel_placeOfPoint_ofGenerator_iotaInf_comap
import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve ModularCurve.CharPModel ModularCurve.IgusaScheme AlgebraicCurve
open scoped TensorProduct

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace BCQ

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve ModularCurve.CharPModel ModularCurve.IgusaScheme AlgebraicCurve AlgebraicCurve.CurveModel

section Emb

variable (N : ℕ) [NeZero N]

private def emb : ↥(modularFunctionFieldFull N) →+* modularFunctionFieldBar N :=
  ((coeffEmb (AlgebraicClosure ℚ)).comp (SubringClass.subtype (modularFunctionFieldFull N))).codRestrict
    (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))
    fun x => coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2

omit [NeZero N] in
private theorem emb_apply (x : ↥(modularFunctionFieldFull N)) :
    emb N x = ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩ := rfl

private theorem emb_jFull : emb N (jFull N) = (jBar N : modularFunctionFieldBar N) := Subtype.ext rfl

private theorem emb_jFull_inv : emb N (jFull N)⁻¹ = (jBar N : modularFunctionFieldBar N)⁻¹ := by
  rw [map_inv₀, emb_jFull]

private theorem jBar_ne_zero : (jBar N : modularFunctionFieldBar N) ≠ 0 := fun h =>
  jFull_ne_zero N ((emb N).injective ((emb_jFull N).trans (h.trans (map_zero (emb N)).symm)))

private scoped instance factJBarNeZero : Fact ((jBar N : modularFunctionFieldBar N) ≠ 0) := ⟨jBar_ne_zero N⟩

end Emb

section Charts

variable (N : ℕ) [NeZero N]

omit [NeZero N] in

private theorem emb_mem_adjoin {S : Set ↥(modularFunctionFieldFull N)} {T : Set (modularFunctionFieldBar N)}
    (hST : ∀ s ∈ S, emb N s ∈ T) {x : ↥(modularFunctionFieldFull N)}
    (hx : x ∈ Algebra.adjoin ℚ S) :
    emb N x ∈ Algebra.adjoin (AlgebraicClosure ℚ) T := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (hST x hx)
  | algebraMap r =>
      have h : emb N (algebraMap ℚ ↥(modularFunctionFieldFull N) r) = ((r : ℚ) : modularFunctionFieldBar N) :=
        eq_ratCast ((emb N).comp (algebraMap ℚ ↥(modularFunctionFieldFull N))) r
      rw [h, ← map_ratCast (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N))]
      exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

omit [NeZero N] in

private theorem emb_mem_chartRing {S : Set ↥(modularFunctionFieldFull N)} {T : Set (modularFunctionFieldBar N)}
    (hST : ∀ s ∈ S, emb N s ∈ T) {b : ↥(modularFunctionFieldFull N)} (hb : b ∈ chartRing ℚ S) :
    emb N b ∈ chartRing (AlgebraicClosure ℚ) T := by
  have hint : IsIntegral (Algebra.adjoin ℚ S) b := hb
  let ψ : ↥(Algebra.adjoin ℚ S) →+* ↥(Algebra.adjoin (AlgebraicClosure ℚ) T) :=
    ((emb N).comp (Algebra.adjoin ℚ S).val.toRingHom).codRestrict
      (Algebra.adjoin (AlgebraicClosure ℚ) T).toSubring fun x => emb_mem_adjoin N hST x.2
  exact IsIntegral.map_of_comp_eq ψ (emb N) (RingHom.ext fun _ => rfl) hint

private def ρ (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N)) (hST : ∀ s ∈ S, emb N s ∈ T) :
    ↥(chartRing ℚ S) →+* ↥(chartRing (AlgebraicClosure ℚ) T) where
  toFun b := ⟨emb N b, emb_mem_chartRing N hST b.2⟩
  map_one' := Subtype.ext (by simp only [Subalgebra.coe_one, map_one])
  map_mul' a b := Subtype.ext (by simp only [Subalgebra.coe_mul, map_mul])
  map_zero' := Subtype.ext (by simp only [Subalgebra.coe_zero, map_zero])
  map_add' a b := Subtype.ext (by simp only [Subalgebra.coe_add, map_add])

omit [NeZero N] in

private theorem coe_ρ_apply (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N)) (hST : ∀ s ∈ S, emb N s ∈ T)
    (b : ↥(chartRing ℚ S)) :
    (ρ N S T hST b : modularFunctionFieldBar N) = emb N b := rfl

omit [NeZero N] in

private theorem ρ_comp_algebraMap (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N)) (hST : ∀ s ∈ S, emb N s ∈ T) :
    (ρ N S T hST).comp (algebraMap ℚ ↥(chartRing ℚ S)) =
      (algebraMap (AlgebraicClosure ℚ) ↥(chartRing (AlgebraicClosure ℚ) T)).comp (algebraMap ℚ (AlgebraicClosure ℚ)) := by
  refine RingHom.ext fun q => Subtype.ext ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, coe_ρ_apply]
  have h1 : emb N (algebraMap ℚ ↥(modularFunctionFieldFull N) q) = ((q : ℚ) : modularFunctionFieldBar N) :=
    eq_ratCast ((emb N).comp (algebraMap ℚ ↥(modularFunctionFieldFull N))) q
  have h2 : algebraMap ℚ (AlgebraicClosure ℚ) q = ((q : ℚ) : AlgebraicClosure ℚ) := eq_ratCast _ q
  rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, h1, h2, map_ratCast]

private theorem fin_sub : ∀ s ∈ ({jFull N} : Set ↥(modularFunctionFieldFull N)), emb N s ∈ ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)) := by
  intro s hs
  rw [Set.mem_singleton_iff] at hs ⊢
  rw [hs, emb_jFull]

private theorem inf_sub : ∀ s ∈ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)), emb N s ∈ ({(jBar N : modularFunctionFieldBar N)⁻¹} : Set (modularFunctionFieldBar N)) := by
  intro s hs
  rw [Set.mem_singleton_iff] at hs ⊢
  rw [hs, emb_jFull_inv]

private theorem mid_sub : ∀ s ∈ ({jFull N, (jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)),
    emb N s ∈ ({(jBar N : modularFunctionFieldBar N), (jBar N : modularFunctionFieldBar N)⁻¹} : Set (modularFunctionFieldBar N)) := by
  intro s hs
  rcases hs with rfl | hs
  · rw [emb_jFull]; exact Set.mem_insert _ _
  · rw [Set.mem_singleton_iff] at hs
    rw [hs, emb_jFull_inv]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

private abbrev ρFin : ↥(chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))) →+*
    ↥(chartRing (AlgebraicClosure ℚ) ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) :=
  ρ N _ _ (fin_sub N)

private abbrev ρInf : ↥(chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) →+*
    ↥(chartRing (AlgebraicClosure ℚ) ({(jBar N : modularFunctionFieldBar N)⁻¹} : Set (modularFunctionFieldBar N))) :=
  ρ N _ _ (inf_sub N)

private abbrev ρMid : ↥(chartRing ℚ ({jFull N, (jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) →+*
    ↥(chartRing (AlgebraicClosure ℚ) ({(jBar N : modularFunctionFieldBar N), (jBar N : modularFunctionFieldBar N)⁻¹} : Set (modularFunctionFieldBar N))) :=
  ρ N _ _ (mid_sub N)

private theorem j_subset_pair : ({jFull N} : Set ↥(modularFunctionFieldFull N)) ⊆ {jFull N, (jFull N)⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert _ _)

private theorem j_inv_subset_pair : ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)) ⊆ {jFull N, (jFull N)⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ (Set.mem_singleton _))

private theorem jb_subset_pair : ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)) ⊆ {(jBar N : modularFunctionFieldBar N), (jBar N : modularFunctionFieldBar N)⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert _ _)

private theorem jb_inv_subset_pair : ({(jBar N : modularFunctionFieldBar N)⁻¹} : Set (modularFunctionFieldBar N)) ⊆ {(jBar N : modularFunctionFieldBar N), (jBar N : modularFunctionFieldBar N)⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ (Set.mem_singleton _))

private theorem square_fin :
    (AlgebraicCurve.CurveModel.chartIncl (AlgebraicClosure ℚ) (jb_subset_pair N)).toRingHom.comp (ρFin N) =
      (ρMid N).comp (AlgebraicCurve.CurveModel.chartIncl ℚ (j_subset_pair N)).toRingHom := by
  refine RingHom.ext fun b => Subtype.ext ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [AlgebraicCurve.CurveModel.coe_chartIncl, coe_ρ_apply, coe_ρ_apply,
    AlgebraicCurve.CurveModel.coe_chartIncl]

private theorem square_inf :
    (AlgebraicCurve.CurveModel.chartIncl (AlgebraicClosure ℚ) (jb_inv_subset_pair N)).toRingHom.comp (ρInf N) =
      (ρMid N).comp (AlgebraicCurve.CurveModel.chartIncl ℚ (j_inv_subset_pair N)).toRingHom := by
  refine RingHom.ext fun b => Subtype.ext ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [AlgebraicCurve.CurveModel.coe_chartIncl, coe_ρ_apply, coe_ρ_apply,
    AlgebraicCurve.CurveModel.coe_chartIncl]

end Charts

section Schemes

variable (N : ℕ) [NeZero N]

local notation "Qb" => AlgebraicClosure ℚ
local notation "jb" => (jBar N : modularFunctionFieldBar N)

private abbrev uFin : X₀ Qb jb ⟶ X₀ ℚ (jFull N) := Spec.map (CommRingCat.ofHom (ρFin N))

private abbrev uInf : CurveModel.XInf Qb jb ⟶ CurveModel.XInf ℚ (jFull N) :=
  Spec.map (CommRingCat.ofHom (ρInf N))

private abbrev uMid : XOverlap Qb jb ⟶ XOverlap ℚ (jFull N) := Spec.map (CommRingCat.ofHom (ρMid N))

private theorem f₀_uFin : f₀ Qb jb ≫ uFin N = uMid N ≫ f₀ ℚ (jFull N) := by
  simp only [f₀, uFin, uMid, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (square_fin N)

private theorem fInf_uInf : CurveModel.fInf Qb jb ≫ uInf N = uMid N ≫ CurveModel.fInf ℚ (jFull N) := by
  simp only [CurveModel.fInf, uInf, uMid, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (square_inf N)

private theorem glue_compat :
    f₀ Qb jb ≫ (uFin N ≫ ι₀ ℚ (jFull N)) =
      CurveModel.fInf Qb jb ≫ (uInf N ≫ CurveModel.ιInf ℚ (jFull N)) := by
  rw [← Category.assoc, f₀_uFin, ← Category.assoc, fInf_uInf, Category.assoc, Category.assoc,
    CurveModel.glue_condition]

private def u : glued Qb jb ⟶ glued ℚ (jFull N) :=
  pushout.desc (uFin N ≫ ι₀ ℚ (jFull N)) (uInf N ≫ CurveModel.ιInf ℚ (jFull N)) (glue_compat N)

@[reassoc]
private theorem ι₀_u : ι₀ Qb jb ≫ u N = uFin N ≫ ι₀ ℚ (jFull N) := pushout.inl_desc _ _ _

@[reassoc]
private theorem ιInf_u : CurveModel.ιInf Qb jb ≫ u N = uInf N ≫ CurveModel.ιInf ℚ (jFull N) :=
  pushout.inr_desc _ _ _

private abbrev baseMap : Spec (CommRingCat.of Qb) ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ Qb))

private theorem uFin_base :
    uFin N ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ ↥(chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))))) =
      Spec.map (CommRingCat.ofHom (algebraMap Qb ↥(chartRing Qb ({jb} : Set (modularFunctionFieldBar N))))) ≫ baseMap := by
  simp only [uFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (ρ_comp_algebraMap N _ _ (fin_sub N))

private theorem uInf_base :
    uInf N ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ ↥(chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))))) =
      Spec.map (CommRingCat.ofHom (algebraMap Qb ↥(chartRing Qb ({jb⁻¹} : Set (modularFunctionFieldBar N))))) ≫ baseMap := by
  simp only [uInf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (ρ_comp_algebraMap N _ _ (inf_sub N))

private theorem u_toBase : u N ≫ gluedToBase ℚ (jFull N) = gluedToBase Qb jb ≫ baseMap := by
  refine pushout.hom_ext (f := f₀ Qb jb) (g := CurveModel.fInf Qb jb) ?_ ?_
  · change ι₀ Qb jb ≫ u N ≫ gluedToBase ℚ (jFull N) = ι₀ Qb jb ≫ gluedToBase Qb jb ≫ baseMap
    rw [ι₀_u_assoc, ι₀_gluedToBase, uFin_base, ι₀_gluedToBase_assoc]
  · change CurveModel.ιInf Qb jb ≫ u N ≫ gluedToBase ℚ (jFull N) =
      CurveModel.ιInf Qb jb ≫ gluedToBase Qb jb ≫ baseMap
    rw [ιInf_u_assoc, ιInf_gluedToBase, uInf_base, ιInf_gluedToBase_assoc]

private def eη : glued Qb jb ⟶ pullback (gluedToBase ℚ (jFull N)) baseMap :=
  pullback.lift (u N) (gluedToBase Qb jb) (u_toBase N)

@[reassoc (attr := simp)]
private theorem eη_fst : eη N ≫ pullback.fst (gluedToBase ℚ (jFull N)) baseMap = u N := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem eη_snd : eη N ≫ pullback.snd (gluedToBase ℚ (jFull N)) baseMap = gluedToBase Qb jb :=
  pullback.lift_snd _ _ _

private theorem ι₀_eη_fst :
    ι₀ Qb jb ≫ eη N ≫ pullback.fst (gluedToBase ℚ (jFull N)) baseMap = uFin N ≫ ι₀ ℚ (jFull N) := by
  rw [eη_fst, ι₀_u]

private theorem ιInf_eη_fst :
    CurveModel.ιInf Qb jb ≫ eη N ≫ pullback.fst (gluedToBase ℚ (jFull N)) baseMap =
      uInf N ≫ CurveModel.ιInf ℚ (jFull N) := by
  rw [eη_fst, ιInf_u]

private theorem eη_fst_closedPoint (q : Spec (CommRingCat.of Qb) ⟶ CurveModel.glued Qb jb) :
    (q ≫ eη N ≫ pullback.fst (gluedToBase ℚ (jFull N)) baseMap).base (IsLocalRing.closedPoint Qb) =
      (u N).base (q.base (IsLocalRing.closedPoint Qb)) := by
  rw [eη_fst]
  rfl

end Schemes

section ChartMatch

variable (N : ℕ) [NeZero N]

local notation "Qb" => AlgebraicClosure ℚ
local notation "jb" => (jBar N : modularFunctionFieldBar N)

private theorem ρInf_tInvChart : ρInf N (tInvChart ℚ (jFull N)) = tInvChart Qb jb := by
  apply Subtype.ext
  rw [coe_ρ_apply, coe_tInvChart, coe_tInvChart, emb_jFull_inv]

private theorem uInf_asIdeal (z : CurveModel.XInf Qb jb) :
    ((uInf N).base z).asIdeal = z.asIdeal.comap (ρInf N) := rfl

private theorem u_mem_range_ι₀_iff (y : glued Qb jb) :
    (u N).base y ∈ Set.range (ι₀ ℚ (jFull N)).base ↔ y ∈ Set.range (ι₀ Qb jb).base := by
  rcases mem_range_ι₀_or_mem_range_ιInf Qb jb y with ⟨x₀, rfl⟩ | ⟨z, rfl⟩
  · refine ⟨fun _ => ⟨x₀, rfl⟩, fun _ => ⟨(uFin N).base x₀, ?_⟩⟩
    change (uFin N ≫ ι₀ ℚ (jFull N)).base x₀ = (ι₀ Qb jb ≫ u N).base x₀
    rw [ι₀_u]
  · have hz : (u N).base ((CurveModel.ιInf Qb jb).base z) =
        (CurveModel.ιInf ℚ (jFull N)).base ((uInf N).base z) := by
      change (CurveModel.ιInf Qb jb ≫ u N).base z = (uInf N ≫ CurveModel.ιInf ℚ (jFull N)).base z
      rw [ιInf_u]
    rw [hz, ιInf_mem_range_ι₀_iff, ιInf_mem_range_ι₀_iff, uInf_asIdeal, Ideal.mem_comap, ρInf_tInvChart]

end ChartMatch

section Tensor

open scoped TensorProduct

variable (N : ℕ) [NeZero N]

private local instance instAlgebraRatChartRing (T : Set (modularFunctionFieldBar N)) :
    Algebra ℚ ↥(chartRing (AlgebraicClosure ℚ) T) :=
  ((algebraMap (AlgebraicClosure ℚ) ↥(chartRing (AlgebraicClosure ℚ) T)).comp (algebraMap ℚ (AlgebraicClosure ℚ))).toAlgebra

set_option synthInstance.maxHeartbeats 1600000 in

private def ρAlg (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N)) (hST : ∀ s ∈ S, emb N s ∈ T) :
    ↥(chartRing ℚ S) →ₐ[ℚ] ↥(chartRing (AlgebraicClosure ℚ) T) :=
  { ρ N S T hST with
    commutes' := fun q => RingHom.congr_fun (ρ_comp_algebraMap N S T hST) q }

set_option synthInstance.maxHeartbeats 1600000 in

private def incAlg (T : Set (modularFunctionFieldBar N)) :
    AlgebraicClosure ℚ →ₐ[ℚ] ↥(chartRing (AlgebraicClosure ℚ) T) :=
  { algebraMap (AlgebraicClosure ℚ) ↥(chartRing (AlgebraicClosure ℚ) T) with
    commutes' := fun _ => rfl }

set_option synthInstance.maxHeartbeats 1600000 in

private def θ (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N)) (hST : ∀ s ∈ S, emb N s ∈ T) :
    (↥(chartRing ℚ S) ⊗[ℚ] AlgebraicClosure ℚ) →+* ↥(chartRing (AlgebraicClosure ℚ) T) :=
  (Algebra.TensorProduct.lift (ρAlg N S T hST) (incAlg N T) fun _ _ => Commute.all _ _).toRingHom

omit [NeZero N] in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem θ_tmul (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N)) (hST : ∀ s ∈ S, emb N s ∈ T)
    (b : ↥(chartRing ℚ S)) (c : AlgebraicClosure ℚ) :
    θ N S T hST (b ⊗ₜ c) = ρ N S T hST b * algebraMap (AlgebraicClosure ℚ) _ c :=
  Algebra.TensorProduct.lift_tmul (ρAlg N S T hST) (incAlg N T) _ b c

omit [NeZero N] in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem θ_comp_includeLeft (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N)) (hST : ∀ s ∈ S, emb N s ∈ T) :
    (θ N S T hST).comp Algebra.TensorProduct.includeLeftRingHom = ρ N S T hST := by
  refine RingHom.ext fun b => ?_
  rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, θ_tmul, map_one, mul_one]

omit [NeZero N] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem θ_comp_includeRight (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N)) (hST : ∀ s ∈ S, emb N s ∈ T) :
    (θ N S T hST).comp
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
          AlgebraicClosure ℚ →ₐ[ℚ] ↥(chartRing ℚ S) ⊗[ℚ] AlgebraicClosure ℚ)) =
      algebraMap (AlgebraicClosure ℚ) ↥(chartRing (AlgebraicClosure ℚ) T) := by
  refine RingHom.ext fun c => ?_
  simpa using θ_tmul N S T hST 1 c

set_option synthInstance.maxHeartbeats 1600000 in

private abbrev θFin := θ N _ _ (fin_sub N)

set_option synthInstance.maxHeartbeats 1600000 in

private abbrev θInf := θ N _ _ (inf_sub N)

end Tensor

section TensorLeft

open scoped TensorProduct

variable (N : ℕ)

private abbrev cm (S : Set ↥(modularFunctionFieldFull N)) :=
  Algebra.TensorProduct.comm ℚ (AlgebraicClosure ℚ) ↥(chartRing ℚ S)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private def θL (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N)) (hST : ∀ s ∈ S, emb N s ∈ T) :
    ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) →ₐ[AlgebraicClosure ℚ] ↥(chartRing (AlgebraicClosure ℚ) T) where
  toRingHom := (θ N S T hST).comp (cm N S : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) ≃+* _).toRingHom
  commutes' c := by
    show θ N S T hST ((1 : ↥(chartRing ℚ S)) ⊗ₜ c) = algebraMap (AlgebraicClosure ℚ) _ c
    rw [θ_tmul, map_one, one_mul]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_apply (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N)) (hST : ∀ s ∈ S, emb N s ∈ T) (x : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S))) :
    θL N S T hST x = θ N S T hST (cm N S x) := rfl

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_tmul (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N)) (hST : ∀ s ∈ S, emb N s ∈ T)
    (c : AlgebraicClosure ℚ) (b : ↥(chartRing ℚ S)) :
    θL N S T hST (c ⊗ₜ b) = ρ N S T hST b * algebraMap (AlgebraicClosure ℚ) _ c :=
  θ_tmul N S T hST b c

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_one_tmul (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N)) (hST : ∀ s ∈ S, emb N s ∈ T)
    (b : ↥(chartRing ℚ S)) :
    θL N S T hST (1 ⊗ₜ b) = ρ N S T hST b := by
  rw [θL_tmul, map_one, mul_one]

end TensorLeft

section Consumption

open scoped TensorProduct

variable (N : ℕ)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem ringHom_eq_θL (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N)) (hST : ∀ s ∈ S, emb N s ∈ T)
    (e : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) →ₐ[AlgebraicClosure ℚ] ↥(chartRing (AlgebraicClosure ℚ) T))
    (he : ∀ b : ↥(chartRing ℚ S),
      ((e (1 ⊗ₜ b) : ↥(chartRing (AlgebraicClosure ℚ) T)) : modularFunctionFieldBar N) = emb N b)
    (y : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S))) :
    (e : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) y = (θL N S T hST : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ((e : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)).map_zero).trans ((θL N S T hST : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)).map_zero).symm
  | tmul c b =>
    have hA : (e : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) (algebraMap (AlgebraicClosure ℚ) _ c) = (θL N S T hST : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) (algebraMap (AlgebraicClosure ℚ) _ c) :=
      (e.commutes c).trans ((θL N S T hST).commutes c).symm
    have hB : (e : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) (1 ⊗ₜ b) = (θL N S T hST : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) (1 ⊗ₜ b) :=
      (Subtype.ext ((he b).trans (coe_ρ_apply N S T hST b).symm)).trans (θL_one_tmul N S T hST b).symm
    have hc : (c ⊗ₜ b : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S))) = algebraMap (AlgebraicClosure ℚ) _ c * (1 ⊗ₜ b) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    exact (congrArg (e : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) hc).trans (((e : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)).map_mul _ _).trans
      ((congr (congrArg (@HMul.hMul _ _ _ _) hA) hB).trans (((θL N S T hST : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)).map_mul _ _).symm.trans
        (congrArg (θL N S T hST : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) hc.symm))))
  | add x y hx hy =>
    exact ((e : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)).map_add x y).trans
      ((congr (congrArg (@HAdd.hAdd _ _ _ _) hx) hy).trans ((θL N S T hST : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)).map_add x y).symm)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem algHom_apply_eq_θL (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N)) (hST : ∀ s ∈ S, emb N s ∈ T)
    (e : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) →ₐ[AlgebraicClosure ℚ] ↥(chartRing (AlgebraicClosure ℚ) T))
    (he : ∀ b : ↥(chartRing ℚ S),
      ((e (1 ⊗ₜ b) : ↥(chartRing (AlgebraicClosure ℚ) T)) : modularFunctionFieldBar N) = emb N b)
    (x : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S))) : e x = θL N S T hST x :=
  ringHom_eq_θL N S T hST e he x

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem θ_bijective_of_algEquiv (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N)) (hST : ∀ s ∈ S, emb N s ∈ T)
    (e : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) ≃ₐ[AlgebraicClosure ℚ] ↥(chartRing (AlgebraicClosure ℚ) T))
    (he : ∀ b : ↥(chartRing ℚ S),
      ((e (1 ⊗ₜ b) : ↥(chartRing (AlgebraicClosure ℚ) T)) : modularFunctionFieldBar N) = emb N b) :
    Function.Bijective (θ N S T hST) := by
  have hL : ∀ x, θL N S T hST x = e x := fun x =>
    (algHom_apply_eq_θL N S T hST (e : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) →ₐ[AlgebraicClosure ℚ] ↥(chartRing (AlgebraicClosure ℚ) T)) he x).symm
  have hcm : ∀ x, θL N S T hST ((cm N S).symm x) = θ N S T hST x := fun x =>
    (θL_apply N S T hST _).trans (congrArg (θ N S T hST) ((cm N S).apply_symm_apply x))
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · have h' : e ((cm N S).symm x) = e ((cm N S).symm y) :=
      ((hL _).symm.trans ((hcm x).trans (hxy.trans ((hcm y).symm.trans (hL _)))))
    exact (cm N S).symm.injective (e.injective h')
  · obtain ⟨w, hw⟩ := e.surjective z
    exact ⟨cm N S w, (θL_apply N S T hST w).symm.trans ((hL w).trans hw)⟩

end Consumption

section Iso

open scoped TensorProduct

variable (N : ℕ) [NeZero N]

local notation "Qb" => AlgebraicClosure ℚ
local notation "jb" => (jBar N : modularFunctionFieldBar N)

private abbrev PFin := pullback (ι₀ ℚ (jFull N)) (pullback.fst (gluedToBase ℚ (jFull N)) baseMap)

private abbrev PInf :=
  pullback (CurveModel.ιInf ℚ (jFull N)) (pullback.fst (gluedToBase ℚ (jFull N)) baseMap)

private def φFin : X₀ Qb jb ⟶ PFin N :=
  pullback.lift (uFin N) (ι₀ Qb jb ≫ eη N) (by rw [Category.assoc, ι₀_eη_fst])

private def φInf : CurveModel.XInf Qb jb ⟶ PInf N :=
  pullback.lift (uInf N) (CurveModel.ιInf Qb jb ≫ eη N) (by rw [Category.assoc, ιInf_eη_fst])

@[reassoc (attr := simp)]
private theorem φFin_fst : φFin N ≫ pullback.fst _ _ = uFin N := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem φFin_snd : φFin N ≫ pullback.snd _ _ = ι₀ Qb jb ≫ eη N := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
private theorem φInf_fst : φInf N ≫ pullback.fst _ _ = uInf N := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem φInf_snd : φInf N ≫ pullback.snd _ _ = CurveModel.ιInf Qb jb ≫ eη N := pullback.lift_snd _ _ _

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem SpecMap_θFin_eq :
    Spec.map (CommRingCat.ofHom (θFin N)) ≫
        (pullbackSpecIso ℚ ↥(chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))) Qb).inv =
      φFin N ≫ (pullbackRightPullbackFstIso (gluedToBase ℚ (jFull N)) baseMap (ι₀ ℚ (jFull N))).hom ≫
        (pullback.congrHom (ι₀_gluedToBase ℚ (jFull N)) rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      θ_comp_includeLeft]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, φFin_fst]
    try rfl
  · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [θ_comp_includeRight N _ _ (fin_sub N)]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd, φFin_snd_assoc, eη_snd, ι₀_gluedToBase]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem SpecMap_θInf_eq :
    Spec.map (CommRingCat.ofHom (θInf N)) ≫
        (pullbackSpecIso ℚ ↥(chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) Qb).inv =
      φInf N ≫ (pullbackRightPullbackFstIso (gluedToBase ℚ (jFull N)) baseMap (CurveModel.ιInf ℚ (jFull N))).hom ≫
        (pullback.congrHom (ιInf_gluedToBase ℚ (jFull N)) rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      θ_comp_includeLeft]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, φInf_fst]
    try rfl
  · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [θ_comp_includeRight N _ _ (inf_sub N)]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd, φInf_snd_assoc, eη_snd, ιInf_gluedToBase]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isIso_φFin (hfin : Function.Bijective (θFin N)) : IsIso (φFin N) := by
  haveI : IsIso (Spec.map (CommRingCat.ofHom (θFin N))) := isIso_SpecMap_iff.mpr hfin
  haveI : IsIso (φFin N ≫
      (pullbackRightPullbackFstIso (gluedToBase ℚ (jFull N)) baseMap (ι₀ ℚ (jFull N))).hom ≫
        (pullback.congrHom (ι₀_gluedToBase ℚ (jFull N)) rfl).hom) := by
    rw [← SpecMap_θFin_eq]
    infer_instance
  exact IsIso.of_isIso_comp_right (φFin N)
    ((pullbackRightPullbackFstIso (gluedToBase ℚ (jFull N)) baseMap (ι₀ ℚ (jFull N))).hom ≫
      (pullback.congrHom (ι₀_gluedToBase ℚ (jFull N)) rfl).hom)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isIso_φInf (hinf : Function.Bijective (θInf N)) : IsIso (φInf N) := by
  haveI : IsIso (Spec.map (CommRingCat.ofHom (θInf N))) := isIso_SpecMap_iff.mpr hinf
  haveI : IsIso (φInf N ≫
      (pullbackRightPullbackFstIso (gluedToBase ℚ (jFull N)) baseMap (CurveModel.ιInf ℚ (jFull N))).hom ≫
        (pullback.congrHom (ιInf_gluedToBase ℚ (jFull N)) rfl).hom) := by
    rw [← SpecMap_θInf_eq]
    infer_instance
  exact IsIso.of_isIso_comp_right (φInf N)
    ((pullbackRightPullbackFstIso (gluedToBase ℚ (jFull N)) baseMap (CurveModel.ιInf ℚ (jFull N))).hom ≫
      (pullback.congrHom (ιInf_gluedToBase ℚ (jFull N)) rfl).hom)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isOpenImmersion_ι₀_eη (hfin : Function.Bijective (θFin N)) :
    IsOpenImmersion (ι₀ Qb jb ≫ eη N) := by
  haveI := isIso_φFin N hfin
  rw [← φFin_snd]
  infer_instance

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isOpenImmersion_ιInf_eη (hinf : Function.Bijective (θInf N)) :
    IsOpenImmersion (CurveModel.ιInf Qb jb ≫ eη N) := by
  haveI := isIso_φInf N hinf
  rw [← φInf_snd]
  infer_instance

set_option synthInstance.maxHeartbeats 1600000 in

private theorem u_eq_of_eη_eq {y y' : glued Qb jb} (h : eη N y = eη N y') : u N y = u N y' := by
  have h1 := congrArg (pullback.fst (gluedToBase ℚ (jFull N)) baseMap) h
  rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, eη_fst] at h1

set_option synthInstance.maxHeartbeats 1600000 in
private theorem injective_eη (hfin : Function.Bijective (θFin N)) (hinf : Function.Bijective (θInf N)) :
    Function.Injective (eη N) := by
  intro y y' h
  have hu := u_eq_of_eη_eq N h
  have hu' : (u N).base y = (u N).base y' := hu
  have hsame : y ∈ Set.range (ι₀ Qb jb).base ↔ y' ∈ Set.range (ι₀ Qb jb).base := by
    rw [← u_mem_range_ι₀_iff N y, ← u_mem_range_ι₀_iff N y', hu']
  by_cases hy : y ∈ Set.range (ι₀ Qb jb).base
  · obtain ⟨a, rfl⟩ := hy
    obtain ⟨a', rfl⟩ := hsame.mp ⟨a, rfl⟩
    haveI := isOpenImmersion_ι₀_eη N hfin
    have : (ι₀ Qb jb ≫ eη N) a = (ι₀ Qb jb ≫ eη N) a' := h
    rw [(ι₀ Qb jb ≫ eη N).isOpenEmbedding.injective this]
  · have hy' : y' ∉ Set.range (ι₀ Qb jb).base := fun h' => hy (hsame.mpr h')
    obtain ⟨a, rfl⟩ := (mem_range_ι₀_or_mem_range_ιInf Qb jb y).resolve_left hy
    obtain ⟨a', rfl⟩ := (mem_range_ι₀_or_mem_range_ιInf Qb jb y').resolve_left hy'
    haveI := isOpenImmersion_ιInf_eη N hinf
    have : (CurveModel.ιInf Qb jb ≫ eη N) a = (CurveModel.ιInf Qb jb ≫ eη N) a' := h
    rw [(CurveModel.ιInf Qb jb ≫ eη N).isOpenEmbedding.injective this]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem surjective_eη (hfin : Function.Bijective (θFin N)) (hinf : Function.Bijective (θInf N)) :
    Function.Surjective (eη N) := by
  intro p
  rcases mem_range_ι₀_or_mem_range_ιInf ℚ (jFull N) (pullback.fst (gluedToBase ℚ (jFull N)) baseMap p) with hp | hp
  · have hp' : p ∈ Set.range (pullback.snd (ι₀ ℚ (jFull N))
        (pullback.fst (gluedToBase ℚ (jFull N)) baseMap)) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact hp
    obtain ⟨r, rfl⟩ := hp'
    haveI := isIso_φFin N hfin
    obtain ⟨a, rfl⟩ := (φFin N).homeomorph.surjective r
    exact ⟨ι₀ Qb jb a, by
      show (ι₀ Qb jb ≫ eη N) a = (φFin N ≫ pullback.snd _ _) a
      rw [φFin_snd]⟩
  · have hp' : p ∈ Set.range (pullback.snd (CurveModel.ιInf ℚ (jFull N))
        (pullback.fst (gluedToBase ℚ (jFull N)) baseMap)) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact hp
    obtain ⟨r, rfl⟩ := hp'
    haveI := isIso_φInf N hinf
    obtain ⟨a, rfl⟩ := (φInf N).homeomorph.surjective r
    exact ⟨CurveModel.ιInf Qb jb a, by
      show (CurveModel.ιInf Qb jb ≫ eη N) a = (φInf N ≫ pullback.snd _ _) a
      rw [φInf_snd]⟩

set_option synthInstance.maxHeartbeats 1600000 in

private theorem isIso_eη_of_bijective (hfin : Function.Bijective (θFin N))
    (hinf : Function.Bijective (θInf N)) : IsIso (eη N) := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨?_, ⟨surjective_eη N hfin hinf⟩⟩
  refine IsOpenImmersion.of_forall_source_exists _ (injective_eη N hfin hinf) fun y => ?_
  rcases mem_range_ι₀_or_mem_range_ιInf Qb jb y with hy | hy
  · exact ⟨_, ι₀ Qb jb, inferInstance, hy, isOpenImmersion_ι₀_eη N hfin⟩
  · exact ⟨_, CurveModel.ιInf Qb jb, inferInstance, hy, isOpenImmersion_ιInf_eη N hinf⟩

end Iso

section Pin

open scoped TensorProduct

private theorem algEquiv_comp_includeRight_eq_ρ (N : ℕ) (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T)
    (e : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ S)) ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) T))
    (he : ∀ b : ↥(chartRing ℚ S),
      ((e (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) T)) : modularFunctionFieldBar N) = emb N b) :
    e.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
          (B := ↥(chartRing ℚ S))).toRingHom =
      ρ N S T hST :=
  RingHom.ext fun b => Subtype.ext ((he b).trans (coe_ρ_apply N S T hST b).symm)

variable (N : ℕ) [NeZero N]

private theorem ι₀_pin
    (e : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))) ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N))))
    (he : ∀ b : ↥(chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))), ((e (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N)
      = emb N b) :
    AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) (jBar N) ≫ eη N ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (e.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
        (B := ↥(chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))))).toRingHom)) ≫
      AlgebraicCurve.CurveModel.ι₀ ℚ (jFull N) :=
  (ι₀_eη_fst N).trans
    (congrArg (fun h => Spec.map (CommRingCat.ofHom h) ≫ AlgebraicCurve.CurveModel.ι₀ ℚ (jFull N))
      (algEquiv_comp_includeRight_eq_ρ N _ _ (fin_sub N) e he).symm)

private theorem ιInf_pin
    (e : ((AlgebraicClosure ℚ) ⊗[ℚ] ↥(chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))) ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N))))
    (he : ∀ b : ↥(chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))), ((e (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N)
      = emb N b) :
    AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ) (jBar N) ≫ eη N ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom (e.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
        (B := ↥(chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))))).toRingHom)) ≫
      AlgebraicCurve.CurveModel.ιInf ℚ (jFull N) :=
  (ιInf_eη_fst N).trans
    (congrArg (fun h => Spec.map (CommRingCat.ofHom h) ≫ AlgebraicCurve.CurveModel.ιInf ℚ (jFull N))
      (algEquiv_comp_includeRight_eq_ρ N _ _ (inf_sub N) e he).symm)

end Pin

section Model

variable (N : ℕ) [NeZero N]

private def Mη (htrans : Transcendental (AlgebraicClosure ℚ) (jBar N : modularFunctionFieldBar N))
    (hfd : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N))
    (hfd_inv : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(jBar N : modularFunctionFieldBar N)⁻¹} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)) :
    CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  haveI := hfd
  haveI := hfd_inv
  CurveModel.ofGenerator (AlgebraicClosure ℚ) (jBar N : modularFunctionFieldBar N) htrans

private def M₀ (htrans₀ : Transcendental ℚ (jFull N))
    (hfd₀ : FiniteDimensional (IntermediateField.adjoin ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))) ↥(modularFunctionFieldFull N))
    (hfd_inv₀ : FiniteDimensional (IntermediateField.adjoin ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) ↥(modularFunctionFieldFull N)) :
    CurveModel ℚ ↥(modularFunctionFieldFull N) :=
  haveI := hfd₀
  haveI := hfd_inv₀
  CurveModel.ofGenerator ℚ (jFull N) htrans₀

end Model

section Compat

open scoped TensorProduct

variable (N : ℕ) [NeZero N]

local notation "Qb" => AlgebraicClosure ℚ
local notation "jb" => (jBar N : modularFunctionFieldBar N)

private theorem φ_coe_eq_coe_ρ (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N)) (hST : ∀ s ∈ S, emb N s ∈ T)
    (a : ↥(chartRing ℚ S)) :
    ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
          (B := ↥(modularFunctionFieldFull N))).toRingHom) (a : ↥(modularFunctionFieldFull N)) =
      (ρ N S T hST a : modularFunctionFieldBar N) := by
  rw [coe_ρ_apply, emb_apply, RingHom.comp_apply]
  exact baseChangeEquiv_one_tmul (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (a : ↥(modularFunctionFieldFull N))

set_option synthInstance.maxHeartbeats 1600000 in

private theorem hcompat
    (htrans : Transcendental (AlgebraicClosure ℚ) (jBar N : modularFunctionFieldBar N))
    (hfd : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N))
    (hfd_inv : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(jBar N : modularFunctionFieldBar N)⁻¹} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N))
    (htrans₀ : Transcendental ℚ (jFull N))
    (hfd₀ : FiniteDimensional (IntermediateField.adjoin ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))) ↥(modularFunctionFieldFull N))
    (hfd_inv₀ : FiniteDimensional (IntermediateField.adjoin ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) ↥(modularFunctionFieldFull N))
    (x : {q : Spec (CommRingCat.of Qb) ⟶ (Mη N htrans hfd hfd_inv).C //
      q ≫ (Mη N htrans hfd hfd_inv).toBase = 𝟙 _})
    (x₀ : closedPoints (M₀ N htrans₀ hfd₀ hfd_inv₀).C)
    (hpt : (x.1 ≫ eη N ≫ pullback.fst _ _).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1) :
    ((Mη N htrans hfd hfd_inv).pointEquivPlace x).toValuationSubring.toSubring.comap
        ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
          (B := ↥(modularFunctionFieldFull N))).toRingHom) =
      ((M₀ N htrans₀ hfd₀ hfd_inv₀).placeOfPoint x₀).toValuationSubring.toSubring := by
  haveI := hfd
  haveI := hfd_inv
  haveI := hfd₀
  haveI := hfd_inv₀
  rw [CurveModel.pointEquivPlace_apply]

  have hc : x.1.base (IsLocalRing.closedPoint Qb) ∈ closedPoints (glued Qb jb) :=
    (pointEquivClosedPoint (Mη N htrans hfd hfd_inv).toBase x).2
  have hu : (u N).base (x.1.base (IsLocalRing.closedPoint Qb)) = x₀.1 := by
    rw [← hpt]
    exact (eη_fst_closedPoint N x.1).symm
  by_cases hx : x.1.base (IsLocalRing.closedPoint Qb) ∈ Set.range (ι₀ Qb jb).base
  ·
    obtain ⟨xb, hxb⟩ := hx
    have hyb : (ι₀ ℚ (jFull N)).base ((uFin N).base xb) = x₀.1 := by
      rw [← hu, ← hxb]
      change (uFin N ≫ ι₀ ℚ (jFull N)).base xb = (ι₀ Qb jb ≫ u N).base xb
      rw [ι₀_u]
    have hxb' : (ι₀ Qb jb).base xb ∈ closedPoints (glued Qb jb) := by
      rw [hxb]
      exact hc
    have hyb' : (ι₀ ℚ (jFull N)).base ((uFin N).base xb) ∈ closedPoints (glued ℚ (jFull N)) := by
      rw [hyb]
      exact x₀.2
    have e1 : pointEquivClosedPoint (Mη N htrans hfd hfd_inv).toBase x =
        (⟨(ι₀ Qb jb).base xb, hxb'⟩ : closedPoints (glued Qb jb)) :=
      Subtype.ext hxb.symm
    have e2 : x₀ = (⟨(ι₀ ℚ (jFull N)).base ((uFin N).base xb), hyb'⟩ : closedPoints (glued ℚ (jFull N))) :=
      Subtype.ext hyb.symm
    rw [e1, e2]
    exact placeOfPoint_ofGenerator_iota0_comap ℚ (jFull N) (AlgebraicClosure ℚ) jb htrans₀ htrans
      ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
          (B := ↥(modularFunctionFieldFull N))).toRingHom)
      (ρFin N) (φ_coe_eq_coe_ρ N _ _ (fin_sub N)) xb hxb' ((uFin N).base xb) hyb' rfl
  ·
    obtain ⟨xb, hxb⟩ :=
      (mem_range_ι₀_or_mem_range_ιInf Qb jb (x.1.base (IsLocalRing.closedPoint Qb))).resolve_left hx
    have hy : x₀.1 ∉ Set.range (ι₀ ℚ (jFull N)).base := by

      rw [← hu]
      exact fun h => hx ((u_mem_range_ι₀_iff N (x.1.base (IsLocalRing.closedPoint Qb))).mp h)
    have hyb : (CurveModel.ιInf ℚ (jFull N)).base ((uInf N).base xb) = x₀.1 := by
      rw [← hu, ← hxb]
      change (uInf N ≫ CurveModel.ιInf ℚ (jFull N)).base xb = (CurveModel.ιInf Qb jb ≫ u N).base xb
      rw [ιInf_u]
    exact placeOfPoint_ofGenerator_iotaInf_comap ℚ (jFull N) (AlgebraicClosure ℚ) jb htrans₀ htrans
      ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
          (B := ↥(modularFunctionFieldFull N))).toRingHom)
      (ρInf N) (φ_coe_eq_coe_ρ N _ _ (inf_sub N))
      (pointEquivClosedPoint (Mη N htrans hfd hfd_inv).toBase x) hx xb hxb x₀ hy ((uInf N).base xb) hyb rfl

end Compat

end BCQ
p2m_reactivate "P2MW.S_ModularCurve_exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat.BCQ"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (N : ℕ) [NeZero N]

    (htrans : Transcendental (AlgebraicClosure ℚ) (jBar N))
    [hne : Fact (jBar N ≠ 0)]
    [hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)]
    [hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)]

    (htrans₀ : Transcendental ℚ (jFull N))
    [hne₀ : Fact (jFull N ≠ 0)]
    [hfd₀ : FiniteDimensional
      ↥(IntermediateField.adjoin ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))) ↥(modularFunctionFieldFull N)]
    [hfd_inv₀ : FiniteDimensional
      ↥(IntermediateField.adjoin ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) ↥(modularFunctionFieldFull N)]

    (cFin : (AlgebraicClosure ℚ) ⊗[ℚ] ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))) ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N))))
    (hcFin : ∀ b : AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)),
      ((cFin (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N)))) : (modularFunctionFieldBar N)) =
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(modularFunctionFieldFull N)).2⟩ : (modularFunctionFieldBar N)))
    (cInf : (AlgebraicClosure ℚ) ⊗[ℚ] ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N))))
    (hcInf : ∀ b : AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)),
      ((cInf (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))) : (modularFunctionFieldBar N)) =
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(modularFunctionFieldFull N)).2⟩ : (modularFunctionFieldBar N))) :
    let Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := CurveModel.ofGenerator (AlgebraicClosure ℚ) (jBar N) htrans
    let M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N) := CurveModel.ofGenerator ℚ (jFull N) htrans₀
    ∃ (eη : Mη.C ⟶ pullback M₀.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))))
      (_ : IsIso eη),
      eη ≫ pullback.snd _ _ = Mη.toBase ∧
      (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y₀ : closedPoints M₀.C),
      (y.1 ≫ eη ≫ pullback.fst _ _).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = y₀.1 →
      ((Mη.pointEquivPlace y).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ) (B := ↥(modularFunctionFieldFull N))).toRingHom) =
        (M₀.placeOfPoint y₀).toValuationSubring.toSubring)) ∧
      (AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) (jBar N) ≫ eη ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (cFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
            (B := ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))))).toRingHom)) ≫
          AlgebraicCurve.CurveModel.ι₀ ℚ (jFull N)) ∧
      (AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ) (jBar N) ≫ eη ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (cInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
            (B := ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))))).toRingHom)) ≫
          AlgebraicCurve.CurveModel.ιInf ℚ (jFull N)) := by
  intro Mη M₀
  have hbF : Function.Bijective (BCQ.θFin N) :=
    BCQ.θ_bijective_of_algEquiv N _ _ (BCQ.fin_sub N) cFin hcFin
  have hbI : Function.Bijective (BCQ.θInf N) :=
    BCQ.θ_bijective_of_algEquiv N _ _ (BCQ.inf_sub N) cInf hcInf
  exact ⟨BCQ.eη N, BCQ.isIso_eη_of_bijective N hbF hbI, BCQ.eη_snd N,
    fun y y₀ h => BCQ.hcompat N htrans hfd hfd_inv htrans₀ hfd₀ hfd_inv₀ y y₀ h,
    BCQ.ι₀_pin N cFin hcFin, BCQ.ιInf_pin N cInf hcInf⟩

end
p2m_reactivate "P2MW.S_ModularCurve_exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat.BCQ"

end S_ModularCurve_exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat
end P2MW
export P2MW.S_ModularCurve_exists_ofGenerator_baseChangeIso_chartPin_and_placeCompat (solution)
