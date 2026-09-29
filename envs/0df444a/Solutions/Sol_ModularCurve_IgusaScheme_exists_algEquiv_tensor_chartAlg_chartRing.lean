-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_algEquiv_tensor_chartAlg_chartRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/7a74c56b-e735-52de-955e-e49fd0e06cfc

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Theorems.Thm_ModularCurve_IgusaScheme_chartRing_le_span_coeffEmb_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlg_chartRing
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve ModularCurve.IgusaScheme ModularCurve.CharPModel

open scoped TensorProduct

noncomputable section
set_option autoImplicit false

namespace S7B

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

private theorem jBar_ne_zero : (jBar N : modularFunctionFieldBar N) ≠ 0 := fun h => by

  have h' := congrArg (fun z : modularFunctionFieldBar N => (z : LaurentSeries (AlgebraicClosure ℚ))) h
  have e : (jBar N : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) :=
    map_jqModC (K := ℚ) (algebraMap ℚ (AlgebraicClosure ℚ))
  simp only [e] at h'
  have hc : (jqModC (AlgebraicClosure ℚ)).coeff (-1 : ℤ) = (1 : AlgebraicClosure ℚ) := by
    rw [← map_jqModC (K := ℚ) (algebraMap ℚ (AlgebraicClosure ℚ)), jqModC_rat]
    simp [HahnSeries.map_coeff]
  rw [h'] at hc
  simp at hc

private scoped instance factJBarNeZero : Fact ((jBar N : modularFunctionFieldBar N) ≠ 0) := ⟨jBar_ne_zero N⟩

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

variable (N : ℕ) [NeZero N] (ℓ : ℕ)

omit [NeZero N] in

private theorem emb_mem_adjoin {S : Set ↥(modularFunctionFieldFull N)} {T : Set (modularFunctionFieldBar N)}
    (hST : ∀ s ∈ S, emb N s ∈ T) {x : ↥(modularFunctionFieldFull N)}
    (hx : x ∈ Algebra.adjoin ↥(GaloisRep.ratLocalizedAt ℓ) S) :
    emb N x ∈ Algebra.adjoin (AlgebraicClosure ℚ) T := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (hST x hx)
  | algebraMap r =>
      have h : emb N (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) r) =
          ((r : ℚ) : modularFunctionFieldBar N) :=
        ringHom_apply_eq_ratCast ((emb N).comp
          (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N))) r
      rw [h, ← map_ratCast (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N))]
      exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

omit [NeZero N] in

private theorem emb_mem_chartRing {S : Set ↥(modularFunctionFieldFull N)} {T : Set (modularFunctionFieldBar N)}
    (hST : ∀ s ∈ S, emb N s ∈ T) {b : ↥(modularFunctionFieldFull N)} (hb : b ∈ chartAlg N ℓ S) :
    emb N b ∈ chartRing (AlgebraicClosure ℚ) T := by
  have hint : IsIntegral (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt ℓ) S) b :=
    hb
  let ψ : ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt ℓ) S) →+* ↥(Algebra.adjoin (AlgebraicClosure ℚ) T) :=
    ((emb N).comp (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt ℓ) S).val.toRingHom).codRestrict
      (Algebra.adjoin (AlgebraicClosure ℚ) T).toSubring fun x => emb_mem_adjoin N ℓ hST x.2
  exact IsIntegral.map_of_comp_eq ψ (emb N) (RingHom.ext fun _ => rfl) hint

private def ρ (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) :
    ↥(chartAlg N ℓ S) →+* ↥(chartRing (AlgebraicClosure ℚ) T) where
  toFun b := ⟨emb N b, emb_mem_chartRing N ℓ hST b.2⟩
  map_one' := Subtype.ext (by simp only [Subalgebra.coe_one, map_one])
  map_mul' a b := Subtype.ext (by simp only [Subalgebra.coe_mul, map_mul])
  map_zero' := Subtype.ext (by simp only [Subalgebra.coe_zero, map_zero])
  map_add' a b := Subtype.ext (by simp only [Subalgebra.coe_add, map_add])

omit [NeZero N] in
private theorem coe_ρ_apply (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) (b : ↥(chartAlg N ℓ S)) :
    (ρ N ℓ S T hST b : modularFunctionFieldBar N) = emb N b := rfl

omit [NeZero N] in

private theorem ρ_comp_algebraMap (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) :
    (ρ N ℓ S T hST).comp (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlg N ℓ S)) =
      (algebraMap (AlgebraicClosure ℚ) ↥(chartRing (AlgebraicClosure ℚ) T)).comp
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)) := by
  refine RingHom.ext fun q => Subtype.ext ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, coe_ρ_apply]
  have h1 : emb N (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N) q) =
      ((q : ℚ) : modularFunctionFieldBar N) :=
    ringHom_apply_eq_ratCast ((emb N).comp
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N))) q
  have h2 : algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) q =
      ((q : ℚ) : AlgebraicClosure ℚ) :=
    ringHom_apply_eq_ratCast (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)) q
  rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, h1, h2, map_ratCast]

private theorem fin_sub : ∀ s ∈ ({jFull N} : Set ↥(modularFunctionFieldFull N)),
    emb N s ∈ ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)) := by
  intro s hs
  rw [Set.mem_singleton_iff] at hs ⊢
  rw [hs, emb_jFull]

private theorem inf_sub : ∀ s ∈ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)),
    emb N s ∈ ({(jBar N : modularFunctionFieldBar N)⁻¹} : Set (modularFunctionFieldBar N)) := by
  intro s hs
  rw [Set.mem_singleton_iff] at hs ⊢
  rw [hs, emb_jFull_inv]

private theorem mid_sub : ∀ s ∈ ({jFull N, (jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)),
    emb N s ∈ ({(jBar N : modularFunctionFieldBar N), (jBar N : modularFunctionFieldBar N)⁻¹} :
      Set (modularFunctionFieldBar N)) := by
  intro s hs
  rcases hs with rfl | hs
  · rw [emb_jFull]; exact Set.mem_insert _ _
  · rw [Set.mem_singleton_iff] at hs
    rw [hs, emb_jFull_inv]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

private abbrev ρFin : ↥(chartAlgFin N ℓ) →+*
    ↥(chartRing (AlgebraicClosure ℚ) ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) :=
  ρ N ℓ _ _ (fin_sub N)

private abbrev ρInf : ↥(chartAlgInf N ℓ) →+*
    ↥(chartRing (AlgebraicClosure ℚ) ({(jBar N : modularFunctionFieldBar N)⁻¹} : Set (modularFunctionFieldBar N))) :=
  ρ N ℓ _ _ (inf_sub N)

private abbrev ρMid : ↥(chartAlgMid N ℓ) →+*
    ↥(chartRing (AlgebraicClosure ℚ) ({(jBar N : modularFunctionFieldBar N),
      (jBar N : modularFunctionFieldBar N)⁻¹} : Set (modularFunctionFieldBar N))) :=
  ρ N ℓ _ _ (mid_sub N)

private theorem jb_subset_pair : ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)) ⊆
    {(jBar N : modularFunctionFieldBar N), (jBar N : modularFunctionFieldBar N)⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert _ _)

private theorem jb_inv_subset_pair :
    ({(jBar N : modularFunctionFieldBar N)⁻¹} : Set (modularFunctionFieldBar N)) ⊆
      {(jBar N : modularFunctionFieldBar N), (jBar N : modularFunctionFieldBar N)⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ (Set.mem_singleton _))

variable [Fact ℓ.Prime]

private theorem square_fin :
    (AlgebraicCurve.CurveModel.chartIncl (AlgebraicClosure ℚ) (jb_subset_pair N)).toRingHom.comp (ρFin N ℓ) =
      (ρMid N ℓ).comp (ModularCurve.IgusaScheme.inclFin N ℓ).toRingHom := by
  refine RingHom.ext fun b => Subtype.ext ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [AlgebraicCurve.CurveModel.coe_chartIncl, coe_ρ_apply, coe_ρ_apply,
    ModularCurve.IgusaScheme.coe_chartIncl]

private theorem square_inf :
    (AlgebraicCurve.CurveModel.chartIncl (AlgebraicClosure ℚ) (jb_inv_subset_pair N)).toRingHom.comp (ρInf N ℓ) =
      (ρMid N ℓ).comp (ModularCurve.IgusaScheme.inclInf N ℓ).toRingHom := by
  refine RingHom.ext fun b => Subtype.ext ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [AlgebraicCurve.CurveModel.coe_chartIncl, coe_ρ_apply, coe_ρ_apply,
    ModularCurve.IgusaScheme.coe_chartIncl]

end Charts

section Schemes

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

local notation "Qb" => AlgebraicClosure ℚ
local notation "jb" => (jBar N : modularFunctionFieldBar N)

private abbrev uFin : X₀ Qb jb ⟶ ModularCurve.IgusaScheme.XFin N ℓ := Spec.map (CommRingCat.ofHom (ρFin N ℓ))

private abbrev uInf : CurveModel.XInf Qb jb ⟶ ModularCurve.IgusaScheme.XInf N ℓ :=
  Spec.map (CommRingCat.ofHom (ρInf N ℓ))

private abbrev uMid : XOverlap Qb jb ⟶ ModularCurve.IgusaScheme.XMid N ℓ := Spec.map (CommRingCat.ofHom (ρMid N ℓ))

private theorem f₀_uFin : f₀ Qb jb ≫ uFin N ℓ = uMid N ℓ ≫ ModularCurve.IgusaScheme.fFin N ℓ := by
  simp only [f₀, uFin, uMid, ModularCurve.IgusaScheme.fFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (square_fin N ℓ)

private theorem fInf_uInf : CurveModel.fInf Qb jb ≫ uInf N ℓ = uMid N ℓ ≫ ModularCurve.IgusaScheme.fInf N ℓ := by
  simp only [CurveModel.fInf, uInf, uMid, ModularCurve.IgusaScheme.fInf, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (square_inf N ℓ)

private theorem glue_compat :
    f₀ Qb jb ≫ (uFin N ℓ ≫ ModularCurve.IgusaScheme.ιFin N ℓ) =
      CurveModel.fInf Qb jb ≫ (uInf N ℓ ≫ ModularCurve.IgusaScheme.ιInf N ℓ) := by
  rw [← Category.assoc, f₀_uFin, ← Category.assoc, fInf_uInf, Category.assoc, Category.assoc,
    ModularCurve.IgusaScheme.glue_condition]

private def u : glued Qb jb ⟶ ModularCurve.IgusaScheme N ℓ :=
  pushout.desc (uFin N ℓ ≫ ModularCurve.IgusaScheme.ιFin N ℓ) (uInf N ℓ ≫ ModularCurve.IgusaScheme.ιInf N ℓ)
    (glue_compat N ℓ)

@[reassoc]
private theorem ι₀_u : ι₀ Qb jb ≫ u N ℓ = uFin N ℓ ≫ ModularCurve.IgusaScheme.ιFin N ℓ :=
  pushout.inl_desc _ _ _

@[reassoc]
private theorem ιInf_u : CurveModel.ιInf Qb jb ≫ u N ℓ = uInf N ℓ ≫ ModularCurve.IgusaScheme.ιInf N ℓ :=
  pushout.inr_desc _ _ _

private abbrev baseMap : Spec (CommRingCat.of Qb) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)) :=
  Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) Qb))

omit [Fact ℓ.Prime] in
private theorem uFin_base :
    uFin N ℓ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ))) =
      Spec.map (CommRingCat.ofHom (algebraMap Qb ↥(chartRing Qb ({jb} : Set (modularFunctionFieldBar N))))) ≫
        baseMap ℓ := by
  simp only [uFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (ρ_comp_algebraMap N ℓ _ _ (fin_sub N))

omit [Fact ℓ.Prime] in
private theorem uInf_base :
    uInf N ℓ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ))) =
      Spec.map (CommRingCat.ofHom (algebraMap Qb ↥(chartRing Qb ({jb⁻¹} : Set (modularFunctionFieldBar N))))) ≫
        baseMap ℓ := by
  simp only [uInf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (ρ_comp_algebraMap N ℓ _ _ (inf_sub N))

private theorem u_igusaTo : u N ℓ ≫ igusaTo N ℓ = gluedToBase Qb jb ≫ baseMap ℓ := by
  refine pushout.hom_ext (f := f₀ Qb jb) (g := CurveModel.fInf Qb jb) ?_ ?_
  · change ι₀ Qb jb ≫ u N ℓ ≫ igusaTo N ℓ = ι₀ Qb jb ≫ gluedToBase Qb jb ≫ baseMap ℓ
    rw [ι₀_u_assoc, ModularCurve.IgusaScheme.ιFin_igusaTo, uFin_base, ι₀_gluedToBase_assoc]
  · change CurveModel.ιInf Qb jb ≫ u N ℓ ≫ igusaTo N ℓ =
      CurveModel.ιInf Qb jb ≫ gluedToBase Qb jb ≫ baseMap ℓ
    rw [ιInf_u_assoc, ModularCurve.IgusaScheme.ιInf_igusaTo, uInf_base, ιInf_gluedToBase_assoc]

private def eη : glued Qb jb ⟶ pullback (igusaTo N ℓ) (baseMap ℓ) :=
  pullback.lift (u N ℓ) (gluedToBase Qb jb) (u_igusaTo N ℓ)

@[reassoc (attr := simp)]
private theorem eη_fst : eη N ℓ ≫ pullback.fst (igusaTo N ℓ) (baseMap ℓ) = u N ℓ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem eη_snd : eη N ℓ ≫ pullback.snd (igusaTo N ℓ) (baseMap ℓ) = gluedToBase Qb jb :=
  pullback.lift_snd _ _ _

private theorem ι₀_eη_fst :
    ι₀ Qb jb ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) (baseMap ℓ) =
      uFin N ℓ ≫ ModularCurve.IgusaScheme.ιFin N ℓ := by
  rw [eη_fst, ι₀_u]

private theorem ιInf_eη_fst :
    CurveModel.ιInf Qb jb ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) (baseMap ℓ) =
      uInf N ℓ ≫ ModularCurve.IgusaScheme.ιInf N ℓ := by
  rw [eη_fst, ιInf_u]

end Schemes

section ChartMatch

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

local notation "Qb" => AlgebraicClosure ℚ
local notation "jb" => (jBar N : modularFunctionFieldBar N)

private theorem ig_ιFin_eq_ιInf_iff (x₀ : ModularCurve.IgusaScheme.XFin N ℓ) (xi : ModularCurve.IgusaScheme.XInf N ℓ) :
    (ModularCurve.IgusaScheme.ιFin N ℓ).base x₀ = (ModularCurve.IgusaScheme.ιInf N ℓ).base xi ↔
      ∃ w : ModularCurve.IgusaScheme.XMid N ℓ,
        (ModularCurve.IgusaScheme.fFin N ℓ).base w = x₀ ∧ (ModularCurve.IgusaScheme.fInf N ℓ).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (F := span (ModularCurve.IgusaScheme.fFin N ℓ) (ModularCurve.IgusaScheme.fInf N ℓ))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · exact match fi, fj, h₁, h₂ with
        | .init _, .init _, h₁, h₂ => ⟨w, h₁, h₂⟩
    · exact nomatch fj
    · exact nomatch fi
  · rintro ⟨w, rfl, rfl⟩
    change (ModularCurve.IgusaScheme.fFin N ℓ ≫ ModularCurve.IgusaScheme.ιFin N ℓ).base w =
      (ModularCurve.IgusaScheme.fInf N ℓ ≫ ModularCurve.IgusaScheme.ιInf N ℓ).base w
    rw [ModularCurve.IgusaScheme.glue_condition]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem ig_range_fInf : Set.range (ModularCurve.IgusaScheme.fInf N ℓ).base =
    ((PrimeSpectrum.basicOpen (jInvChartInf N ℓ) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(chartAlgInf N ℓ))) : Set (PrimeSpectrum ↥(chartAlgInf N ℓ))) := by
  letI := (ModularCurve.IgusaScheme.inclInf N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf N ℓ
  exact PrimeSpectrum.localization_away_comap_range ↥(chartAlgMid N ℓ) (jInvChartInf N ℓ)

private theorem ig_ιInf_mem_range_ιFin_iff (xi : ModularCurve.IgusaScheme.XInf N ℓ) :
    (ModularCurve.IgusaScheme.ιInf N ℓ).base xi ∈ Set.range (ModularCurve.IgusaScheme.ιFin N ℓ).base ↔
      jInvChartInf N ℓ ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← ig_range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (ig_ιFin_eq_ιInf_iff N ℓ x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(ModularCurve.IgusaScheme.fFin N ℓ).base w, (ig_ιFin_eq_ιInf_iff N ℓ _ _).mpr ⟨w, rfl, rfl⟩⟩

private theorem ρInf_jInvChartInf : ρInf N ℓ (jInvChartInf N ℓ) = tInvChart Qb jb := by
  apply Subtype.ext
  rw [coe_ρ_apply, coe_jInvChartInf, emb_jFull_inv, coe_tInvChart]

omit [Fact ℓ.Prime] in
private theorem uInf_asIdeal (z : CurveModel.XInf Qb jb) :
    ((uInf N ℓ).base z).asIdeal = z.asIdeal.comap (ρInf N ℓ) := rfl

private theorem u_mem_range_ιFin_iff (y : glued Qb jb) :
    (u N ℓ).base y ∈ Set.range (ModularCurve.IgusaScheme.ιFin N ℓ).base ↔ y ∈ Set.range (ι₀ Qb jb).base := by
  rcases mem_range_ι₀_or_mem_range_ιInf Qb jb y with ⟨x₀, rfl⟩ | ⟨z, rfl⟩
  · refine ⟨fun _ => ⟨x₀, rfl⟩, fun _ => ⟨(uFin N ℓ).base x₀, ?_⟩⟩
    change (uFin N ℓ ≫ ModularCurve.IgusaScheme.ιFin N ℓ).base x₀ = (ι₀ Qb jb ≫ u N ℓ).base x₀
    rw [ι₀_u]
  · have hz : (u N ℓ).base ((CurveModel.ιInf Qb jb).base z) =
        (ModularCurve.IgusaScheme.ιInf N ℓ).base ((uInf N ℓ).base z) := by
      change (CurveModel.ιInf Qb jb ≫ u N ℓ).base z = (uInf N ℓ ≫ ModularCurve.IgusaScheme.ιInf N ℓ).base z
      rw [ιInf_u]
    rw [hz, ig_ιInf_mem_range_ιFin_iff, ιInf_mem_range_ι₀_iff, uInf_asIdeal, Ideal.mem_comap,
      ρInf_jInvChartInf]

end ChartMatch

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

private theorem Mη_C (htrans : Transcendental (AlgebraicClosure ℚ) (jBar N : modularFunctionFieldBar N))
    (hfd : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N))
    (hfd_inv : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(jBar N : modularFunctionFieldBar N)⁻¹} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)) :
    (Mη N htrans hfd hfd_inv).C =
      CurveModel.glued (AlgebraicClosure ℚ) (jBar N : modularFunctionFieldBar N) :=
  rfl

end Model

section Tensor

open scoped TensorProduct

variable (N : ℕ) [NeZero N] (ℓ : ℕ)

local instance instAlgebraRatLocalizedChartRing (T : Set (modularFunctionFieldBar N)) :
    Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartRing (AlgebraicClosure ℚ) T) :=
  ((algebraMap (AlgebraicClosure ℚ) ↥(chartRing (AlgebraicClosure ℚ) T)).comp
    (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))).toAlgebra

set_option synthInstance.maxHeartbeats 1600000 in

private def ρAlg (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) :
    ↥(chartAlg N ℓ S) →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartRing (AlgebraicClosure ℚ) T) :=
  { ρ N ℓ S T hST with
    commutes' := fun q => RingHom.congr_fun (ρ_comp_algebraMap N ℓ S T hST) q }

set_option synthInstance.maxHeartbeats 1600000 in

private def incAlg (T : Set (modularFunctionFieldBar N)) :
    AlgebraicClosure ℚ →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartRing (AlgebraicClosure ℚ) T) :=
  { algebraMap (AlgebraicClosure ℚ) ↥(chartRing (AlgebraicClosure ℚ) T) with
    commutes' := fun _ => rfl }

set_option synthInstance.maxHeartbeats 1600000 in

private def θ (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) :
    (↥(chartAlg N ℓ S) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] AlgebraicClosure ℚ) →+*
      ↥(chartRing (AlgebraicClosure ℚ) T) :=
  (Algebra.TensorProduct.lift (ρAlg N ℓ S T hST) (incAlg N ℓ T) fun _ _ => Commute.all _ _).toRingHom

omit [NeZero N] in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem θ_tmul (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) (b : ↥(chartAlg N ℓ S)) (c : AlgebraicClosure ℚ) :
    θ N ℓ S T hST (b ⊗ₜ c) = ρ N ℓ S T hST b * algebraMap (AlgebraicClosure ℚ) _ c :=
  Algebra.TensorProduct.lift_tmul (ρAlg N ℓ S T hST) (incAlg N ℓ T) _ b c

omit [NeZero N] in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem coe_θ_tmul (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) (b : ↥(chartAlg N ℓ S)) (c : AlgebraicClosure ℚ) :
    ((θ N ℓ S T hST (b ⊗ₜ c) : ↥(chartRing (AlgebraicClosure ℚ) T)) : modularFunctionFieldBar N) =
      c • emb N b := by
  rw [θ_tmul, Subalgebra.coe_mul, coe_ρ_apply, Algebra.smul_def, mul_comm]
  rfl

omit [NeZero N] in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem θ_comp_includeLeft (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) :
    (θ N ℓ S T hST).comp Algebra.TensorProduct.includeLeftRingHom = ρ N ℓ S T hST := by
  refine RingHom.ext fun b => ?_
  rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, θ_tmul, map_one, mul_one]

omit [NeZero N] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem θ_comp_includeRight (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) :
    (θ N ℓ S T hST).comp
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
          AlgebraicClosure ℚ →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)]
            ↥(chartAlg N ℓ S) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] AlgebraicClosure ℚ)) =
      algebraMap (AlgebraicClosure ℚ) ↥(chartRing (AlgebraicClosure ℚ) T) := by
  refine RingHom.ext fun c => ?_
  simpa using θ_tmul N ℓ S T hST 1 c

set_option synthInstance.maxHeartbeats 1600000 in

private abbrev θFin := θ N ℓ _ _ (fin_sub N)

set_option synthInstance.maxHeartbeats 1600000 in

private abbrev θInf := θ N ℓ _ _ (inf_sub N)

end Tensor

section TensorLeft

open scoped TensorProduct

variable (N : ℕ) (ℓ : ℕ)

private abbrev cm (S : Set ↥(modularFunctionFieldFull N)) :=
  Algebra.TensorProduct.comm ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) ↥(chartAlg N ℓ S)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private def θL (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) :
    (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →ₐ[AlgebraicClosure ℚ] ↥(chartRing (AlgebraicClosure ℚ) T) where
  toRingHom := (θ N ℓ S T hST).comp (cm N ℓ S : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) ≃+* _).toRingHom
  commutes' c := by
    show θ N ℓ S T hST ((1 : ↥(chartAlg N ℓ S)) ⊗ₜ c) = algebraMap (AlgebraicClosure ℚ) _ c
    rw [θ_tmul, map_one, one_mul]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_apply (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) (x : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S))) :
    θL N ℓ S T hST x = θ N ℓ S T hST (cm N ℓ S x) := rfl

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_tmul (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) (c : AlgebraicClosure ℚ) (b : ↥(chartAlg N ℓ S)) :
    θL N ℓ S T hST (c ⊗ₜ b) = ρ N ℓ S T hST b * algebraMap (AlgebraicClosure ℚ) _ c :=
  θ_tmul N ℓ S T hST b c

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_one_tmul (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) (b : ↥(chartAlg N ℓ S)) :
    θL N ℓ S T hST (1 ⊗ₜ b) = ρ N ℓ S T hST b := by
  rw [θL_tmul, map_one, mul_one]

set_option synthInstance.maxHeartbeats 1600000 in

private theorem coe_θL_one_tmul (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) (b : ↥(chartAlg N ℓ S)) :
    ((θL N ℓ S T hST (1 ⊗ₜ b) : ↥(chartRing (AlgebraicClosure ℚ) T)) : modularFunctionFieldBar N) = emb N b := by
  rw [θL_one_tmul, coe_ρ_apply]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_injective (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) (h : Function.Injective (θ N ℓ S T hST)) :
    Function.Injective (θL N ℓ S T hST) := fun x y hxy =>
  (cm N ℓ S).injective (h (by rwa [θL_apply, θL_apply] at hxy))

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_surjective (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) (h : Function.Surjective (θ N ℓ S T hST)) :
    Function.Surjective (θL N ℓ S T hST) := fun z => by
  obtain ⟨w, hw⟩ := h z
  exact ⟨(cm N ℓ S).symm w, by rw [θL_apply, (cm N ℓ S).apply_symm_apply, hw]⟩

set_option synthInstance.maxHeartbeats 1600000 in

private def chartEquivL (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) (hinj : Function.Injective (θ N ℓ S T hST))
    (hsurj : Function.Surjective (θ N ℓ S T hST)) :
    (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) ≃ₐ[AlgebraicClosure ℚ] ↥(chartRing (AlgebraicClosure ℚ) T) :=
  AlgEquiv.ofBijective (θL N ℓ S T hST) ⟨θL_injective N ℓ S T hST hinj, θL_surjective N ℓ S T hST hsurj⟩

set_option synthInstance.maxHeartbeats 1600000 in
private theorem coe_chartEquivL_one_tmul (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) (hinj : Function.Injective (θ N ℓ S T hST))
    (hsurj : Function.Surjective (θ N ℓ S T hST)) (b : ↥(chartAlg N ℓ S)) :
    ((chartEquivL N ℓ S T hST hinj hsurj (1 ⊗ₜ b) : ↥(chartRing (AlgebraicClosure ℚ) T)) : modularFunctionFieldBar N) = emb N b :=
  coe_θL_one_tmul N ℓ S T hST b

end TensorLeft

section Iso

open scoped TensorProduct

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

local notation "Qb" => AlgebraicClosure ℚ
local notation "jb" => (jBar N : modularFunctionFieldBar N)

private abbrev PFin := pullback (ModularCurve.IgusaScheme.ιFin N ℓ) (pullback.fst (igusaTo N ℓ) (baseMap ℓ))

private abbrev PInf := pullback (ModularCurve.IgusaScheme.ιInf N ℓ) (pullback.fst (igusaTo N ℓ) (baseMap ℓ))

private def φFin : X₀ Qb jb ⟶ PFin N ℓ :=
  pullback.lift (uFin N ℓ) (ι₀ Qb jb ≫ eη N ℓ) (by rw [Category.assoc, ι₀_eη_fst])

private def φInf : CurveModel.XInf Qb jb ⟶ PInf N ℓ :=
  pullback.lift (uInf N ℓ) (CurveModel.ιInf Qb jb ≫ eη N ℓ) (by rw [Category.assoc, ιInf_eη_fst])

@[reassoc (attr := simp)]
private theorem φFin_fst : φFin N ℓ ≫ pullback.fst _ _ = uFin N ℓ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem φFin_snd : φFin N ℓ ≫ pullback.snd _ _ = ι₀ Qb jb ≫ eη N ℓ := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
private theorem φInf_fst : φInf N ℓ ≫ pullback.fst _ _ = uInf N ℓ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem φInf_snd : φInf N ℓ ≫ pullback.snd _ _ = CurveModel.ιInf Qb jb ≫ eη N ℓ := pullback.lift_snd _ _ _

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem SpecMap_θFin_eq :
    Spec.map (CommRingCat.ofHom (θFin N ℓ)) ≫
        (pullbackSpecIso ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ) Qb).inv =
      φFin N ℓ ≫ (pullbackRightPullbackFstIso (igusaTo N ℓ) (baseMap ℓ) (ModularCurve.IgusaScheme.ιFin N ℓ)).hom ≫
        (pullback.congrHom (ModularCurve.IgusaScheme.ιFin_igusaTo N ℓ) rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      θ_comp_includeLeft]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, φFin_fst]
    try rfl
  · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [θ_comp_includeRight N ℓ _ _ (fin_sub N)]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd, φFin_snd_assoc, eη_snd, ι₀_gluedToBase]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem SpecMap_θInf_eq :
    Spec.map (CommRingCat.ofHom (θInf N ℓ)) ≫
        (pullbackSpecIso ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ) Qb).inv =
      φInf N ℓ ≫ (pullbackRightPullbackFstIso (igusaTo N ℓ) (baseMap ℓ) (ModularCurve.IgusaScheme.ιInf N ℓ)).hom ≫
        (pullback.congrHom (ModularCurve.IgusaScheme.ιInf_igusaTo N ℓ) rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      θ_comp_includeLeft]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, φInf_fst]
    try rfl
  · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [θ_comp_includeRight N ℓ _ _ (inf_sub N)]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd, φInf_snd_assoc, eη_snd, ιInf_gluedToBase]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isIso_φFin (hfin : Function.Bijective (θFin N ℓ)) : IsIso (φFin N ℓ) := by
  haveI : IsIso (CommRingCat.ofHom (R := ↥(chartAlg N ℓ ({jFull N} : Set ↥(modularFunctionFieldFull N))) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] AlgebraicClosure ℚ)
      (S := ↥(chartRing (AlgebraicClosure ℚ) ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))) (θFin N ℓ)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (by simpa using hfin)
  haveI : IsIso (Spec.map (CommRingCat.ofHom (R := ↥(chartAlg N ℓ ({jFull N} : Set ↥(modularFunctionFieldFull N))) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] AlgebraicClosure ℚ)
      (S := ↥(chartRing (AlgebraicClosure ℚ) ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))) (θFin N ℓ))) := inferInstance
  haveI : IsIso (φFin N ℓ ≫
      (pullbackRightPullbackFstIso (igusaTo N ℓ) (baseMap ℓ) (ModularCurve.IgusaScheme.ιFin N ℓ)).hom ≫
        (pullback.congrHom (ModularCurve.IgusaScheme.ιFin_igusaTo N ℓ) rfl).hom) := by
    rw [← SpecMap_θFin_eq]
    infer_instance
  exact IsIso.of_isIso_comp_right (φFin N ℓ)
    ((pullbackRightPullbackFstIso (igusaTo N ℓ) (baseMap ℓ) (ModularCurve.IgusaScheme.ιFin N ℓ)).hom ≫
      (pullback.congrHom (ModularCurve.IgusaScheme.ιFin_igusaTo N ℓ) rfl).hom)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isIso_φInf (hinf : Function.Bijective (θInf N ℓ)) : IsIso (φInf N ℓ) := by
  haveI : IsIso (CommRingCat.ofHom (R := ↥(chartAlg N ℓ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] AlgebraicClosure ℚ)
      (S := ↥(chartRing (AlgebraicClosure ℚ) ({(jBar N : modularFunctionFieldBar N)⁻¹} : Set (modularFunctionFieldBar N)))) (θInf N ℓ)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (by simpa using hinf)
  haveI : IsIso (Spec.map (CommRingCat.ofHom (R := ↥(chartAlg N ℓ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] AlgebraicClosure ℚ)
      (S := ↥(chartRing (AlgebraicClosure ℚ) ({(jBar N : modularFunctionFieldBar N)⁻¹} : Set (modularFunctionFieldBar N)))) (θInf N ℓ))) := inferInstance
  haveI : IsIso (φInf N ℓ ≫
      (pullbackRightPullbackFstIso (igusaTo N ℓ) (baseMap ℓ) (ModularCurve.IgusaScheme.ιInf N ℓ)).hom ≫
        (pullback.congrHom (ModularCurve.IgusaScheme.ιInf_igusaTo N ℓ) rfl).hom) := by
    rw [← SpecMap_θInf_eq]
    infer_instance
  exact IsIso.of_isIso_comp_right (φInf N ℓ)
    ((pullbackRightPullbackFstIso (igusaTo N ℓ) (baseMap ℓ) (ModularCurve.IgusaScheme.ιInf N ℓ)).hom ≫
      (pullback.congrHom (ModularCurve.IgusaScheme.ιInf_igusaTo N ℓ) rfl).hom)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isOpenImmersion_ι₀_eη (hfin : Function.Bijective (θFin N ℓ)) :
    IsOpenImmersion (ι₀ Qb jb ≫ eη N ℓ) := by
  haveI := isIso_φFin N ℓ hfin
  rw [← φFin_snd]
  infer_instance

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isOpenImmersion_ιInf_eη (hinf : Function.Bijective (θInf N ℓ)) :
    IsOpenImmersion (CurveModel.ιInf Qb jb ≫ eη N ℓ) := by
  haveI := isIso_φInf N ℓ hinf
  rw [← φInf_snd]
  infer_instance

set_option synthInstance.maxHeartbeats 1600000 in

private theorem u_eq_of_eη_eq {y y' : glued Qb jb} (h : eη N ℓ y = eη N ℓ y') : u N ℓ y = u N ℓ y' := by
  have h1 := congrArg (pullback.fst (igusaTo N ℓ) (baseMap ℓ)) h
  rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, eη_fst] at h1

set_option synthInstance.maxHeartbeats 1600000 in
private theorem injective_eη (hfin : Function.Bijective (θFin N ℓ)) (hinf : Function.Bijective (θInf N ℓ)) :
    Function.Injective (eη N ℓ) := by
  intro y y' h
  have hu := u_eq_of_eη_eq N ℓ h

  have hu' : (u N ℓ).base y = (u N ℓ).base y' := hu
  have hsame : y ∈ Set.range (ι₀ Qb jb).base ↔ y' ∈ Set.range (ι₀ Qb jb).base := by
    rw [← u_mem_range_ιFin_iff N ℓ y, ← u_mem_range_ιFin_iff N ℓ y', hu']
  by_cases hy : y ∈ Set.range (ι₀ Qb jb).base
  · obtain ⟨a, rfl⟩ := hy
    obtain ⟨a', rfl⟩ := hsame.mp ⟨a, rfl⟩
    haveI := isOpenImmersion_ι₀_eη N ℓ hfin
    have : (ι₀ Qb jb ≫ eη N ℓ) a = (ι₀ Qb jb ≫ eη N ℓ) a' := h
    rw [(ι₀ Qb jb ≫ eη N ℓ).isOpenEmbedding.injective this]
  · have hy' : y' ∉ Set.range (ι₀ Qb jb).base := fun h' => hy (hsame.mpr h')
    obtain ⟨a, rfl⟩ := (mem_range_ι₀_or_mem_range_ιInf Qb jb y).resolve_left hy
    obtain ⟨a', rfl⟩ := (mem_range_ι₀_or_mem_range_ιInf Qb jb y').resolve_left hy'
    haveI := isOpenImmersion_ιInf_eη N ℓ hinf
    have : (CurveModel.ιInf Qb jb ≫ eη N ℓ) a = (CurveModel.ιInf Qb jb ≫ eη N ℓ) a' := h
    rw [(CurveModel.ιInf Qb jb ≫ eη N ℓ).isOpenEmbedding.injective this]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem surjective_eη (hfin : Function.Bijective (θFin N ℓ)) (hinf : Function.Bijective (θInf N ℓ)) :
    Function.Surjective (eη N ℓ) := by
  intro p
  rcases mem_range_ιFin_or_mem_range_ιInf N ℓ (pullback.fst (igusaTo N ℓ) (baseMap ℓ) p) with hp | hp
  ·
    have hp' : p ∈ Set.range (pullback.snd (ModularCurve.IgusaScheme.ιFin N ℓ)
        (pullback.fst (igusaTo N ℓ) (baseMap ℓ))) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact hp
    obtain ⟨r, rfl⟩ := hp'
    haveI := isIso_φFin N ℓ hfin
    obtain ⟨a, rfl⟩ := (φFin N ℓ).homeomorph.surjective r
    exact ⟨ι₀ Qb jb a, by
      show (ι₀ Qb jb ≫ eη N ℓ) a = (φFin N ℓ ≫ pullback.snd _ _) a
      rw [φFin_snd]⟩
  · have hp' : p ∈ Set.range (pullback.snd (ModularCurve.IgusaScheme.ιInf N ℓ)
        (pullback.fst (igusaTo N ℓ) (baseMap ℓ))) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact hp
    obtain ⟨r, rfl⟩ := hp'
    haveI := isIso_φInf N ℓ hinf
    obtain ⟨a, rfl⟩ := (φInf N ℓ).homeomorph.surjective r
    exact ⟨CurveModel.ιInf Qb jb a, by
      show (CurveModel.ιInf Qb jb ≫ eη N ℓ) a = (φInf N ℓ ≫ pullback.snd _ _) a
      rw [φInf_snd]⟩

set_option synthInstance.maxHeartbeats 1600000 in

private theorem isIso_eη_of_bijective (hfin : Function.Bijective (θFin N ℓ)) (hinf : Function.Bijective (θInf N ℓ)) :
    IsIso (eη N ℓ) := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨?_, ⟨surjective_eη N ℓ hfin hinf⟩⟩
  refine IsOpenImmersion.of_forall_source_exists _ (injective_eη N ℓ hfin hinf) fun y => ?_
  rcases mem_range_ι₀_or_mem_range_ιInf Qb jb y with hy | hy
  · exact ⟨_, ι₀ Qb jb, inferInstance, hy, isOpenImmersion_ι₀_eη N ℓ hfin⟩
  · exact ⟨_, CurveModel.ιInf Qb jb, inferInstance, hy, isOpenImmersion_ιInf_eη N ℓ hinf⟩

end Iso

end S7B
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlg_chartRing.S7B"

section

open TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve ModularCurve.CharPModel ModularCurve.IgusaScheme AlgebraicCurve AlgebraicCurve.CurveModel
open scoped TensorProduct
open S7B

namespace S7j

open TensorProduct

variable {R : Type*} [CommRing R] {A : Type*} [AddCommGroup A] [Module R A]
  {L : Type*} [Field L] [Algebra ℚ L] [Module R L]

private theorem linearIndependent_rat_of_basis {V : Submodule ℤ L} {ι : Type*} (b : Module.Basis ι ℤ V) :
    LinearIndependent ℚ (fun k => (b k : L)) := by
  have h : LinearIndependent ℤ (fun k => (b k : L)) :=
    b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp h

private theorem injective_of_coeff (v : A →+ LaurentSeries ℚ) (hv : Function.Injective v)
    (Φ : A ⊗[R] L →+ LaurentSeries L)
    (hΦ : ∀ (a : A) (c : L) (n : ℤ),
      (Φ (a ⊗ₜ[R] c)).coeff n = c * algebraMap ℚ L ((v a).coeff n)) :
    Function.Injective Φ := by
  classical
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  refine (injective_iff_map_eq_zero Φ).mpr fun t ht => ?_
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t

  let V : Submodule ℤ L := Submodule.span ℤ (↑(s.image Prod.snd) : Set L)
  haveI : Module.Finite ℤ V := Module.Finite.span_of_finite ℤ (s.image Prod.snd).finite_toSet
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := V)
  have hli : LinearIndependent ℚ (fun k => (b k : L)) := linearIndependent_rat_of_basis b
  have hmem : ∀ i ∈ s, i.2 ∈ V := fun i hi =>
    Submodule.subset_span (by
      rw [Finset.coe_image]
      exact Set.mem_image_of_mem _ hi)

  let c' : s → V := fun i => ⟨i.1.2, hmem i.1 i.2⟩
  let a' : Fin n → A := fun k => ∑ i : s, (b.repr (c' i) k) • i.1.1
  have key : ∑ i ∈ s, i.1 ⊗ₜ[R] i.2 = ∑ k : Fin n, a' k ⊗ₜ[R] (b k : L) := by
    calc ∑ i ∈ s, i.1 ⊗ₜ[R] i.2
        = ∑ i : s, i.1.1 ⊗ₜ[R] ((c' i : V) : L) :=
          (Finset.sum_coe_sort s (fun i => i.1 ⊗ₜ[R] i.2)).symm
      _ = ∑ i : s, ∑ k : Fin n, ((b.repr (c' i) k) • i.1.1) ⊗ₜ[R] (b k : L) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          conv_lhs => rw [← b.sum_repr (c' i)]
          rw [Submodule.coe_sum, tmul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Submodule.coe_smul, smul_tmul]
      _ = ∑ k : Fin n, ∑ i : s, ((b.repr (c' i) k) • i.1.1) ⊗ₜ[R] (b k : L) :=
          Finset.sum_comm
      _ = ∑ k : Fin n, a' k ⊗ₜ[R] (b k : L) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [sum_tmul]
  rw [key, map_sum] at ht

  have hcoeff : ∀ (k : Fin n) (m : ℤ), (v (a' k)).coeff m = 0 := by
    intro k m
    have h0 : ∑ j : Fin n, ((v (a' j)).coeff m) • (b j : L) = 0 := by
      have h1 := congrArg (fun x : LaurentSeries L => x.coeff m) ht
      simp only [HahnSeries.coeff_sum, hΦ, HahnSeries.coeff_zero] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    exact Fintype.linearIndependent_iff.mp hli _ h0 k
  have ha' : ∀ k : Fin n, a' k = 0 := fun k =>
    hv (by
      rw [map_zero]
      exact HahnSeries.coeff_inj.mp (funext fun m => by rw [hcoeff k m, HahnSeries.coeff_zero]))
  rw [key]
  exact Finset.sum_eq_zero fun k _ => by rw [ha' k, zero_tmul]

end S7j
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlg_chartRing.S7B"

namespace S7j

open S7B
open scoped TensorProduct

variable (N : ℕ) [NeZero N] (ℓ : ℕ)

local notation "Qb" => AlgebraicClosure ℚ

omit [NeZero N] in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem coeff_coe_θ_tmul (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) (b : ↥(chartAlg N ℓ S)) (c : Qb) (n : ℤ) :
    (((θ N ℓ S T hST (b ⊗ₜ c) : ↥(chartRing (AlgebraicClosure ℚ) T)) : modularFunctionFieldBar N) :
        LaurentSeries Qb).coeff n =
      c * algebraMap ℚ Qb (((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ).coeff n) := by
  rw [coe_θ_tmul, Algebra.smul_def, MulMemClass.coe_mul,
    show ((algebraMap Qb (modularFunctionFieldBar N) c : modularFunctionFieldBar N) : LaurentSeries Qb) =
      HahnSeries.single 0 c from algebraMap_laurentSeries_eq_single Qb c,
    HahnSeries.coeff_single_zero_mul]
  rfl

private def coeLS (S : Set ↥(modularFunctionFieldFull N)) : ↥(chartAlg N ℓ S) →+ LaurentSeries ℚ :=
  AddMonoidHom.mk' (fun b => ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ)) fun _ _ => rfl

omit [NeZero N] in
private theorem coeLS_injective (S : Set ↥(modularFunctionFieldFull N)) :
    Function.Injective (coeLS N ℓ S) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

set_option synthInstance.maxHeartbeats 1600000 in

private def θLS (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) :
    (↥(chartAlg N ℓ S) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] AlgebraicClosure ℚ) →+ LaurentSeries Qb :=
  AddMonoidHom.mk'
    (fun t => (((θ N ℓ S T hST t : ↥(chartRing (AlgebraicClosure ℚ) T)) : modularFunctionFieldBar N) :
      LaurentSeries Qb))
    fun x y => by simp only [(θ N ℓ S T hST).map_add]; rfl

omit [NeZero N] in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem θ_injective (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) : Function.Injective (θ N ℓ S T hST) := by
  have h : Function.Injective (θLS N ℓ S T hST) :=
    injective_of_coeff (coeLS N ℓ S) (coeLS_injective N ℓ S) (θLS N ℓ S T hST)
      fun b c n => coeff_coe_θ_tmul N ℓ S T hST b c n
  intro x y hxy
  exact h (congrArg (fun z : ↥(chartRing (AlgebraicClosure ℚ) T) =>
    ((z : modularFunctionFieldBar N) : LaurentSeries Qb)) hxy)

set_option synthInstance.maxHeartbeats 1600000 in

private theorem θFin_injective : Function.Injective (θFin N ℓ) := θ_injective N ℓ _ _ (fin_sub N)

set_option synthInstance.maxHeartbeats 1600000 in

private theorem θInf_injective : Function.Injective (θInf N ℓ) := θ_injective N ℓ _ _ (inf_sub N)

end S7j
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlg_chartRing.S7B"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlg_chartRing.S7B"

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve ModularCurve.CharPModel ModularCurve.IgusaScheme AlgebraicCurve AlgebraicCurve.CurveModel
open scoped TensorProduct
open ModularCurve ModularCurve.CharPModel ModularCurve.IgusaScheme AlgebraicCurve.CurveModel

namespace S7s

open scoped TensorProduct
open ModularCurve ModularCurve.CharPModel ModularCurve.IgusaScheme AlgebraicCurve.CurveModel

variable (N : ℕ) [NeZero N] (ℓ : ℕ)

omit [NeZero N] in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem surjective_θ_of_le_span
    (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, S7B.emb N s ∈ T)
    (hS7A : (chartRing (AlgebraicClosure ℚ) T).toSubmodule ≤
      Submodule.span (AlgebraicClosure ℚ)
        (Set.range fun b : ↥(chartAlg N ℓ S) => S7B.emb N (b : ↥(modularFunctionFieldFull N)))) :
    Function.Surjective (S7B.θ N ℓ S T hST) := by
  intro y

  have hrange :
      (Set.range fun b : ↥(chartAlg N ℓ S) => S7B.emb N (b : ↥(modularFunctionFieldFull N))) =
        ⇑(chartRing (AlgebraicClosure ℚ) T).val.toLinearMap ''
          Set.range ⇑(S7B.ρ N ℓ S T hST) := by
    rw [← Set.range_comp]; rfl
  have hy₀ : (y : modularFunctionFieldBar N) ∈
      Submodule.map (chartRing (AlgebraicClosure ℚ) T).val.toLinearMap
        (Submodule.span (AlgebraicClosure ℚ) (Set.range (S7B.ρ N ℓ S T hST))) := by
    rw [Submodule.map_span, ← hrange]
    exact hS7A y.2
  obtain ⟨y', hy', hyy'⟩ := Submodule.mem_map.mp hy₀
  obtain rfl : y' = y := Subtype.ext hyy'
  clear hy₀ hyy' hS7A hrange

  refine Submodule.span_induction ?mem ?zero ?add ?smul hy'
  case mem =>
    rintro _ ⟨b, rfl⟩
    exact ⟨b ⊗ₜ (1 : AlgebraicClosure ℚ), by rw [S7B.θ_tmul, map_one, mul_one]⟩
  case zero =>
    exact ⟨0, (S7B.θ N ℓ S T hST).map_zero⟩
  case add =>
    rintro x₁ x₂ _ _ ⟨z₁, h₁⟩ ⟨z₂, h₂⟩
    exact ⟨z₁ + z₂, ((S7B.θ N ℓ S T hST).map_add z₁ z₂).trans (by rw [h₁, h₂])⟩
  case smul =>
    rintro c x _ ⟨z, hz⟩
    refine ⟨((1 : ↥(chartAlg N ℓ S)) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] c) * z, ?_⟩
    rw [(S7B.θ N ℓ S T hST).map_mul, hz, S7B.θ_tmul, map_one, one_mul]
    exact (Algebra.smul_def c x).symm

private theorem range_emb_eq_fin :
    (Set.range fun b : chartAlgFin N ℓ =>
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N)) =
      Set.range fun b : ↥(chartAlg N ℓ {jFull N}) => S7B.emb N (b : ↥(modularFunctionFieldFull N)) :=
  rfl

private theorem range_emb_eq_inf :
    (Set.range fun b : chartAlgInf N ℓ =>
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N)) =
      Set.range fun b : ↥(chartAlg N ℓ {(jFull N)⁻¹}) => S7B.emb N (b : ↥(modularFunctionFieldFull N)) :=
  rfl

set_option synthInstance.maxHeartbeats 1600000 in

private theorem surjective_θFin
    (hS7A : (chartRing (AlgebraicClosure ℚ)
        ({jBar N} : Set (modularFunctionFieldBar N))).toSubmodule ≤
      Submodule.span (AlgebraicClosure ℚ) (Set.range fun b : chartAlgFin N ℓ =>
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N))) :
    Function.Surjective (S7B.θFin N ℓ) :=
  surjective_θ_of_le_span N ℓ _ _ (S7B.fin_sub N) (range_emb_eq_fin N ℓ ▸ hS7A)

set_option synthInstance.maxHeartbeats 1600000 in

private theorem surjective_θInf
    (hS7A : (chartRing (AlgebraicClosure ℚ)
        ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N))).toSubmodule ≤
      Submodule.span (AlgebraicClosure ℚ) (Set.range fun b : chartAlgInf N ℓ =>
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N))) :
    Function.Surjective (S7B.θInf N ℓ) :=
  surjective_θ_of_le_span N ℓ _ _ (S7B.inf_sub N) (range_emb_eq_inf N ℓ ▸ hS7A)

end S7s
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlg_chartRing.S7B"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlg_chartRing.S7B"

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) :
    (∃ eFin : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({jBar N} : Set (modularFunctionFieldBar N))),
      ∀ b : chartAlgFin N ℓ, ((eFin (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
          ({jBar N} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N)
        = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N)) ∧
    (∃ eInf : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N))),
      ∀ b : chartAlgInf N ℓ, ((eInf (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
          ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N)
        = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N)) := by
  have hA := ModularCurve.IgusaScheme.chartRing_le_span_coeffEmb_chartAlg N ℓ
  exact ⟨⟨S7B.chartEquivL N ℓ _ _ (S7B.fin_sub N) (S7j.θFin_injective N ℓ)
      (S7s.surjective_θFin N ℓ hA.1),
    fun b => S7B.coe_chartEquivL_one_tmul N ℓ _ _ (S7B.fin_sub N) _ _ b⟩,
  ⟨S7B.chartEquivL N ℓ _ _ (S7B.inf_sub N) (S7j.θInf_injective N ℓ)
      (S7s.surjective_θInf N ℓ hA.2),
    fun b => S7B.coe_chartEquivL_one_tmul N ℓ _ _ (S7B.inf_sub N) _ _ b⟩⟩

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlg_chartRing.S7B"

end S_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlg_chartRing
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlg_chartRing (solution)
