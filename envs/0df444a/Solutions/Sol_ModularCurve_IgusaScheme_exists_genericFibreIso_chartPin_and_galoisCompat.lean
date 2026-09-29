-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_genericFibreIso_chartPin_and_galoisCompat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/502adbfd-e3a8-5b57-b3f3-f3b6c49ec662

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve ModularCurve.IgusaScheme ModularCurve.CharPModel

open scoped TensorProduct

noncomputable section
set_option autoImplicit false
set_option Elab.async false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve ModularCurve.IgusaScheme ModularCurve.CharPModel

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

end Model

section Tensor

open scoped TensorProduct

variable (N : ℕ) [NeZero N] (ℓ : ℕ)

private local instance instAlgebraRatLocalizedChartRing (T : Set (modularFunctionFieldBar N)) :
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

end TensorLeft

section Consumption

open scoped TensorProduct

variable (N : ℕ) (ℓ : ℕ)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem ringHom_eq_θL (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T)
    (e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →ₐ[AlgebraicClosure ℚ] ↥(chartRing (AlgebraicClosure ℚ) T))
    (he : ∀ b : ↥(chartAlg N ℓ S),
      ((e (1 ⊗ₜ b) : ↥(chartRing (AlgebraicClosure ℚ) T)) : modularFunctionFieldBar N) = emb N b)
    (y : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S))) :
    (e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) y = (θL N ℓ S T hST : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ((e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)).map_zero).trans ((θL N ℓ S T hST : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)).map_zero).symm
  | tmul c b =>
    have hA : (e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) (algebraMap (AlgebraicClosure ℚ) _ c) =
        (θL N ℓ S T hST : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) (algebraMap (AlgebraicClosure ℚ) _ c) :=
      (e.commutes c).trans ((θL N ℓ S T hST).commutes c).symm
    have hB : (e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) (1 ⊗ₜ b) = (θL N ℓ S T hST : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) (1 ⊗ₜ b) :=
      (Subtype.ext ((he b).trans (coe_ρ_apply N ℓ S T hST b).symm)).trans (θL_one_tmul N ℓ S T hST b).symm
    have hc : (c ⊗ₜ b : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S))) = algebraMap (AlgebraicClosure ℚ) _ c * (1 ⊗ₜ b) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    exact (congrArg (e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) hc).trans (((e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)).map_mul _ _).trans
      ((congr (congrArg (@HMul.hMul _ _ _ _) hA) hB).trans (((θL N ℓ S T hST : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)).map_mul _ _).symm.trans
        (congrArg (θL N ℓ S T hST : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)) hc.symm))))
  | add x y hx hy =>
    exact ((e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)).map_add x y).trans
      ((congr (congrArg (@HAdd.hAdd _ _ _ _) hx) hy).trans ((θL N ℓ S T hST : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing (AlgebraicClosure ℚ) T)).map_add x y).symm)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem algHom_apply_eq_θL (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T)
    (e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →ₐ[AlgebraicClosure ℚ] ↥(chartRing (AlgebraicClosure ℚ) T))
    (he : ∀ b : ↥(chartAlg N ℓ S),
      ((e (1 ⊗ₜ b) : ↥(chartRing (AlgebraicClosure ℚ) T)) : modularFunctionFieldBar N) = emb N b)
    (x : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S))) : e x = θL N ℓ S T hST x :=
  ringHom_eq_θL N ℓ S T hST e he x

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem θ_bijective_of_algEquiv (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T)
    (e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) ≃ₐ[AlgebraicClosure ℚ] ↥(chartRing (AlgebraicClosure ℚ) T))
    (he : ∀ b : ↥(chartAlg N ℓ S),
      ((e (1 ⊗ₜ b) : ↥(chartRing (AlgebraicClosure ℚ) T)) : modularFunctionFieldBar N) = emb N b) :
    Function.Bijective (θ N ℓ S T hST) := by
  have hL : ∀ x, θL N ℓ S T hST x = e x := fun x =>
    (algHom_apply_eq_θL N ℓ S T hST (e : (AlgebraicClosure ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →ₐ[AlgebraicClosure ℚ] ↥(chartRing (AlgebraicClosure ℚ) T)) he x).symm
  have hcm : ∀ x, θL N ℓ S T hST ((cm N ℓ S).symm x) = θ N ℓ S T hST x := fun x =>
    (θL_apply N ℓ S T hST _).trans (congrArg (θ N ℓ S T hST) ((cm N ℓ S).apply_symm_apply x))
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · have h' : e ((cm N ℓ S).symm x) = e ((cm N ℓ S).symm y) :=
      ((hL _).symm.trans ((hcm x).trans (hxy.trans ((hcm y).symm.trans (hL _)))))
    exact (cm N ℓ S).symm.injective (e.injective h')
  · obtain ⟨w, hw⟩ := e.surjective z
    exact ⟨cm N ℓ S w, (θL_apply N ℓ S T hST w).symm.trans ((hL w).trans hw)⟩

end Consumption

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
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7B"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7B"

noncomputable section

open ModularCurve ModularCurve.IgusaScheme AlgebraicCurve AlgebraicCurve.CurveModel

namespace S7H

open S7B
open scoped TensorProduct

variable (N : ℕ) (ℓ : ℕ)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem adjoin_range_ρ_eq_top (S : Set ↥(modularFunctionFieldFull N)) (T : Set (modularFunctionFieldBar N))
    (hST : ∀ s ∈ S, emb N s ∈ T) (hθ : Function.Surjective (θ N ℓ S T hST)) :
    Algebra.adjoin (AlgebraicClosure ℚ) (Set.range (ρ N ℓ S T hST)) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨t, rfl⟩ := hθ y
  induction t using TensorProduct.induction_on with
  | zero => rw [(θ N ℓ S T hST).map_zero]; exact zero_mem _
  | tmul b c =>
      rw [θ_tmul]
      exact mul_mem (Algebra.subset_adjoin ⟨b, rfl⟩) (Subalgebra.algebraMap_mem _ c)
  | add x y hx hy => rw [(θ N ℓ S T hST).map_add]; exact add_mem hx hy

end S7H
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7B"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7B"

set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve AlgebraicCurve.CurveModel IsDedekindDomain IntermediateField

open scoped Pointwise

universe u

namespace S7c

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
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7B"

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

end S7c
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7B P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7c"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7B P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7c"

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicCurve.CurveModel IsDedekindDomain IntermediateField

universe u

namespace S7p

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
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7B P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7c"

section AlgHom

variable (K : Type u) [Field K]

private def _root_.S7p.toAlgHom {R : Type u} [CommRing R] [Algebra K R] (φ : R →+* K)
    (hφ : φ.comp (algebraMap K R) = RingHom.id K) : R →ₐ[K] K :=
  { φ with commutes' := fun c => RingHom.congr_fun hφ c }

p2m_export "S7p" "toAlgHom"
@[scoped simp]
private theorem toAlgHom_toRingHom {R : Type u} [CommRing R] [Algebra K R] (φ : R →+* K)
    (hφ : φ.comp (algebraMap K R) = RingHom.id K) : (toAlgHom K φ hφ).toRingHom = φ :=
  rfl

end AlgHom
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7B P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7c"

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
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7B P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7c"

end S7p
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7B P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7c P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7p"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7B P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7c P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7p"

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve ModularCurve.CharPModel ModularCurve.IgusaScheme AlgebraicCurve AlgebraicCurve.CurveModel

namespace S7G

open S7B S7c S7p

variable (N : ℕ) [NeZero N] (ℓ : ℕ)

local notation "Qb" => AlgebraicClosure ℚ
local notation "jb" => (jBar N : modularFunctionFieldBar N)

private theorem arithmeticRingAut_jBar (g : Qb ≃ₐ[ℚ] Qb) :
    arithmeticRingAut (modularFunctionFieldFull N) g jb = jb :=
  Subtype.ext (coeffMap_coeffEmb g _)

private theorem arithmeticRingAut_jBar_inv (g : Qb ≃ₐ[ℚ] Qb) :
    arithmeticRingAut (modularFunctionFieldFull N) g jb⁻¹ = jb⁻¹ := by
  rw [map_inv₀, arithmeticRingAut_jBar]

private theorem chartAut_ρFin (g : Qb ≃ₐ[ℚ] Qb)
    (hs : arithmeticRingAut (modularFunctionFieldFull N) g jb = jb) :
    ∀ t ∈ Set.range (ρFin N ℓ), chartAut hs t = t := by
  rintro _ ⟨b, rfl⟩
  exact Subtype.ext (Subtype.ext (coeffMap_coeffEmb g _))

private theorem chartAut_ρInf (g : Qb ≃ₐ[ℚ] Qb)
    (hs : arithmeticRingAut (modularFunctionFieldFull N) g jb⁻¹ = jb⁻¹) :
    ∀ t ∈ Set.range (ρInf N ℓ), chartAut hs t = t := by
  rintro _ ⟨b, rfl⟩
  exact Subtype.ext (Subtype.ext (coeffMap_coeffEmb g _))

variable [Fact ℓ.Prime]

private theorem eη_fst_closedPoint (q : Spec (CommRingCat.of Qb) ⟶ CurveModel.glued Qb jb) :
    (q ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) (baseMap ℓ)) (IsLocalRing.closedPoint Qb) =
      (u N ℓ) (q (IsLocalRing.closedPoint Qb)) := by
  rw [eη_fst]
  rfl

private theorem SpecMap_ι₀_eη_fst
    (ψ : ↥(chartRing Qb ({jb} : Set (modularFunctionFieldBar N))) →+* Qb) :
    Spec.map (CommRingCat.ofHom ψ) ≫ ι₀ Qb jb ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) (baseMap ℓ) =
      Spec.map (CommRingCat.ofHom (ψ.comp (ρFin N ℓ))) ≫ ModularCurve.IgusaScheme.ιFin N ℓ := by
  rw [ι₀_eη_fst, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

private theorem SpecMap_ιInf_eη_fst
    (ψ : ↥(chartRing Qb ({jb⁻¹} : Set (modularFunctionFieldBar N))) →+* Qb) :
    Spec.map (CommRingCat.ofHom ψ) ≫ CurveModel.ιInf Qb jb ≫ eη N ℓ ≫
        pullback.fst (igusaTo N ℓ) (baseMap ℓ) =
      Spec.map (CommRingCat.ofHom (ψ.comp (ρInf N ℓ))) ≫ ModularCurve.IgusaScheme.ιInf N ℓ := by
  rw [ιInf_eη_fst, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

variable (htrans : Transcendental (AlgebraicClosure ℚ) (jBar N : modularFunctionFieldBar N))
    (hfd : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N))
    (hfd_inv : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(jBar N : modularFunctionFieldBar N)⁻¹} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N))

private theorem u_closedPoint_eq (g : Qb ≃ₐ[ℚ] Qb)
    (x x' : {q : Spec (CommRingCat.of Qb) ⟶ (Mη N htrans hfd hfd_inv).C // q ≫ (Mη N htrans hfd hfd_inv).toBase = 𝟙 _})
    (h : x'.1 ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) _ =
      Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ x.1 ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) _) :
    (u N ℓ) (x'.1 (IsLocalRing.closedPoint Qb)) = (u N ℓ) (x.1 (IsLocalRing.closedPoint Qb)) :=
  calc (u N ℓ) (x'.1 (IsLocalRing.closedPoint Qb))
      = (x'.1 ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) _) (IsLocalRing.closedPoint Qb) :=
        (eη_fst_closedPoint N ℓ x'.1).symm
    _ = (Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ x.1 ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) _)
          (IsLocalRing.closedPoint Qb) := by rw [h]
    _ = (x.1 ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) _)
          (Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) (IsLocalRing.closedPoint Qb)) := rfl
    _ = (x.1 ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) _) (IsLocalRing.closedPoint Qb) := by
        rw [Subsingleton.elim (α := PrimeSpectrum Qb)
          (Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) (IsLocalRing.closedPoint Qb))
          (IsLocalRing.closedPoint Qb)]
    _ = (u N ℓ) (x.1 (IsLocalRing.closedPoint Qb)) := eη_fst_closedPoint N ℓ x.1

private theorem hgal_fin (g : Qb ≃ₐ[ℚ] Qb)
    (hAfin : Algebra.adjoin Qb (Set.range (ρFin N ℓ)) = ⊤)
    (x x' : {q : Spec (CommRingCat.of Qb) ⟶ (Mη N htrans hfd hfd_inv).C // q ≫ (Mη N htrans hfd hfd_inv).toBase = 𝟙 _})
    (h : x'.1 ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) _ =
      Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ x.1 ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) _)
    (hx : x.1 (IsLocalRing.closedPoint Qb) ∈ Set.range (ι₀ Qb jb))
    (hx' : x'.1 (IsLocalRing.closedPoint Qb) ∈ Set.range (ι₀ Qb jb)) :
    (Mη N htrans hfd hfd_inv).pointEquivPlace x' =
      arithmeticGalois (L := Qb) (modularFunctionFieldFull N) g • (Mη N htrans hfd hfd_inv).pointEquivPlace x := by
  haveI := hfd
  haveI := hfd_inv
  obtain ⟨φ, hφ⟩ := exists_algHom_eq_SpecMap_comp_ι₀ Qb jb htrans x hx
  obtain ⟨φ', hφ'⟩ := exists_algHom_eq_SpecMap_comp_ι₀ Qb jb htrans x' hx'
  obtain ⟨𝔭, h𝔭, hx𝔭⟩ := pointEquivPlace_of_eq_SpecMap_comp_ι₀ Qb jb htrans x φ hφ
  obtain ⟨𝔭', h𝔭', hx𝔭'⟩ := pointEquivPlace_of_eq_SpecMap_comp_ι₀ Qb jb htrans x' φ' hφ'
  have h1 : (Spec.map (CommRingCat.ofHom φ'.toRingHom) ≫ ι₀ Qb jb) ≫ eη N ℓ ≫
      pullback.fst (igusaTo N ℓ) (baseMap ℓ) =
      Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        ι₀ Qb jb) ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) (baseMap ℓ) := by
    rw [hφ, hφ']
    exact h
  simp only [Category.assoc] at h1
  rw [SpecMap_ι₀_eη_fst, SpecMap_ι₀_eη_fst] at h1
  have hP2 := ringHom_eq_comp_of_SpecMap_comp (ModularCurve.IgusaScheme.ιFin N ℓ) _ _ _ h1
  have hconj : ∀ t ∈ Set.range (ρFin N ℓ), φ' t = g (φ t) := by
    rintro _ ⟨b, rfl⟩
    exact RingHom.congr_fun hP2 b
  refine hx𝔭'.trans (Eq.trans ?_
    (congrArg (arithmeticGalois (L := Qb) (modularFunctionFieldFull N) g • ·) hx𝔭).symm)
  exact ofHeightOneSpectrum_ker_eq_smul (arithmeticRingAut_jBar N g) hAfin
    (chartAut_ρFin N ℓ g (arithmeticRingAut_jBar N g)) φ φ' hconj 𝔭 𝔭' h𝔭 h𝔭'

private theorem hgal_inf (g : Qb ≃ₐ[ℚ] Qb)
    (hAinf : Algebra.adjoin Qb (Set.range (ρInf N ℓ)) = ⊤)
    (x x' : {q : Spec (CommRingCat.of Qb) ⟶ (Mη N htrans hfd hfd_inv).C // q ≫ (Mη N htrans hfd hfd_inv).toBase = 𝟙 _})
    (h : x'.1 ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) _ =
      Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ x.1 ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) _)
    (hx : x.1 (IsLocalRing.closedPoint Qb) ∉ Set.range (ι₀ Qb jb))
    (hx' : x'.1 (IsLocalRing.closedPoint Qb) ∉ Set.range (ι₀ Qb jb)) :
    (Mη N htrans hfd hfd_inv).pointEquivPlace x' =
      arithmeticGalois (L := Qb) (modularFunctionFieldFull N) g • (Mη N htrans hfd hfd_inv).pointEquivPlace x := by
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
  have h1 : (Spec.map (CommRingCat.ofHom φ'.toRingHom) ≫ CurveModel.ιInf Qb jb) ≫ eη N ℓ ≫
      pullback.fst (igusaTo N ℓ) (baseMap ℓ) =
      Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        CurveModel.ιInf Qb jb) ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) (baseMap ℓ) := by
    rw [hφ, hφ']
    exact h
  simp only [Category.assoc] at h1
  rw [SpecMap_ιInf_eη_fst, SpecMap_ιInf_eη_fst] at h1
  have hP2 := ringHom_eq_comp_of_SpecMap_comp (ModularCurve.IgusaScheme.ιInf N ℓ) _ _ _ h1
  have hconj : ∀ t ∈ Set.range (ρInf N ℓ), φ' t = g (φ t) := by
    rintro _ ⟨b, rfl⟩
    exact RingHom.congr_fun hP2 b
  refine hx𝔭'.trans (Eq.trans ?_
    (congrArg (arithmeticGalois (L := Qb) (modularFunctionFieldFull N) g • ·) hx𝔭).symm)
  exact ofHeightOneSpectrum_ker_eq_smul (arithmeticRingAut_jBar_inv N g) hAinf
    (chartAut_ρInf N ℓ g (arithmeticRingAut_jBar_inv N g)) φ φ' hconj 𝔭 𝔭' h𝔭 h𝔭'

private theorem hgal
    (hAfin : Algebra.adjoin Qb (Set.range (ρFin N ℓ)) = ⊤)
    (hAinf : Algebra.adjoin Qb (Set.range (ρInf N ℓ)) = ⊤)
    (hP3 : ∀ y : CurveModel.glued Qb jb,
      (u N ℓ) y ∈ Set.range (ModularCurve.IgusaScheme.ιFin N ℓ) ↔ y ∈ Set.range (ι₀ Qb jb)) :
    ∀ (g : Qb ≃ₐ[ℚ] Qb)
      (x x' : {q : Spec (CommRingCat.of Qb) ⟶ (Mη N htrans hfd hfd_inv).C // q ≫ (Mη N htrans hfd hfd_inv).toBase = 𝟙 _}),
      x'.1 ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) _ =
        Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ x.1 ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) _ →
      (Mη N htrans hfd hfd_inv).pointEquivPlace x' =
        arithmeticGalois (L := Qb) (modularFunctionFieldFull N) g • (Mη N htrans hfd hfd_inv).pointEquivPlace x := by
  intro g x x' h
  have hsame : x.1 (IsLocalRing.closedPoint Qb) ∈ Set.range (ι₀ Qb jb) ↔
      x'.1 (IsLocalRing.closedPoint Qb) ∈ Set.range (ι₀ Qb jb) := by

    have h2 := hP3 (x'.1 (IsLocalRing.closedPoint Qb))
    rw [u_closedPoint_eq N ℓ htrans hfd hfd_inv g x x' h] at h2
    exact (hP3 (x.1 (IsLocalRing.closedPoint Qb))).symm.trans h2
  by_cases hx : x.1 (IsLocalRing.closedPoint Qb) ∈ Set.range (ι₀ Qb jb)
  · exact hgal_fin N ℓ htrans hfd hfd_inv g hAfin x x' h hx (hsame.mp hx)
  · exact hgal_inf N ℓ htrans hfd hfd_inv g hAinf x x' h hx (fun hx' => hx (hsame.mpr hx'))
end S7G
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7B P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7c P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7p"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7B P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7c P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7p"

namespace S7Pin

private theorem algEquiv_comp_includeRight_eq_ρ (N : ℕ) [NeZero N] (ℓ : ℕ) (S : Set ↥(modularFunctionFieldFull N))
    (T : Set (modularFunctionFieldBar N)) (hST : ∀ s ∈ S, S7B.emb N s ∈ T)
    (e : ((AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) T))
    (he : ∀ b : ↥(chartAlg N ℓ S),
      ((e (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) T)) : modularFunctionFieldBar N) = S7B.emb N b) :
    e.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
          (B := ↥(chartAlg N ℓ S))).toRingHom =
      S7B.ρ N ℓ S T hST :=
  RingHom.ext fun b => Subtype.ext ((he b).trans (S7B.coe_ρ_apply N ℓ S T hST b).symm)

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

private theorem ι₀_pin
    (e : ((AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N)))))
    (he : (∀ b : ↥(chartAlgFin N ℓ), ((e (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jBar N} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N)
      = S7B.emb N b)) :
    AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) (jBar N) ≫ S7B.eη N ℓ ≫
      pullback.fst (igusaTo N ℓ) _ =
    Spec.map (CommRingCat.ofHom (e.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight
        (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
        (B := ↥(chartAlgFin N ℓ))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιFin N ℓ :=
  (S7B.ι₀_eη_fst N ℓ).trans
    (congrArg (fun h => Spec.map (CommRingCat.ofHom h) ≫ ModularCurve.IgusaScheme.ιFin N ℓ)
      (algEquiv_comp_includeRight_eq_ρ N ℓ _ _ (S7B.fin_sub N) e he).symm)

private theorem ιInf_pin
    (e : ((AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))))
    (he : (∀ b : ↥(chartAlgInf N ℓ), ((e (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N)
      = S7B.emb N b)) :
    AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ) (jBar N) ≫ S7B.eη N ℓ ≫
      pullback.fst (igusaTo N ℓ) _ =
    Spec.map (CommRingCat.ofHom (e.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight
        (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
        (B := ↥(chartAlgInf N ℓ))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιInf N ℓ :=
  (S7B.ιInf_eη_fst N ℓ).trans
    (congrArg (fun h => Spec.map (CommRingCat.ofHom h) ≫ ModularCurve.IgusaScheme.ιInf N ℓ)
      (algEquiv_comp_includeRight_eq_ρ N ℓ _ _ (S7B.inf_sub N) e he).symm)

end S7Pin
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7B P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7c P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat.S7p"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (htrans : Transcendental (AlgebraicClosure ℚ) (jBar N))
    [hne : Fact (jBar N ≠ 0)]
    [hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jBar N} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N)]
    [hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N)]
    (eFin : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({jBar N} : Set (modularFunctionFieldBar N))))
    (hFin : ∀ b : chartAlgFin N ℓ, ((eFin (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({jBar N} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N))
    (eInf : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N))))
    (hInf : ∀ b : chartAlgInf N ℓ, ((eInf (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({(jBar N)⁻¹} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N)).2⟩ : modularFunctionFieldBar N)) :
    let Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
      CurveModel.ofGenerator (AlgebraicClosure ℚ) (jBar N) htrans
    ∃ (eη : Mη.C ⟶ pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) (_ : IsIso eη),
      eη ≫ pullback.snd (igusaTo N ℓ) _ = Mη.toBase ∧
      (AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) (jBar N) ≫ eη ≫
        pullback.fst (igusaTo N ℓ) _ =
      Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
          (B := ↥(chartAlgFin N ℓ))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιFin N ℓ) ∧
      (AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ) (jBar N) ≫ eη ≫
        pullback.fst (igusaTo N ℓ) _ =
      Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
          (B := ↥(chartAlgInf N ℓ))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιInf N ℓ) ∧
      ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
        x'.1 ≫ eη ≫ pullback.fst (igusaTo N ℓ) _ =
          Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
            x.1 ≫ eη ≫ pullback.fst (igusaTo N ℓ) _ →
        Mη.pointEquivPlace x' =
          arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) g •
            Mη.pointEquivPlace x := by
  have _ := hℓN
  intro Mη
  have hbF : Function.Bijective (S7B.θFin N ℓ) :=
    S7B.θ_bijective_of_algEquiv N ℓ _ _ (S7B.fin_sub N) eFin hFin
  have hbI : Function.Bijective (S7B.θInf N ℓ) :=
    S7B.θ_bijective_of_algEquiv N ℓ _ _ (S7B.inf_sub N) eInf hInf
  exact ⟨S7B.eη N ℓ, S7B.isIso_eη_of_bijective N ℓ hbF hbI, S7B.eη_snd N ℓ,
    S7Pin.ι₀_pin N ℓ eFin hFin, S7Pin.ιInf_pin N ℓ eInf hInf,
    S7G.hgal N ℓ htrans hfd hfd_inv
      (S7H.adjoin_range_ρ_eq_top N ℓ _ _ (S7B.fin_sub N) hbF.2)
      (S7H.adjoin_range_ρ_eq_top N ℓ _ _ (S7B.inf_sub N) hbI.2)
      (fun y => S7B.u_mem_range_ιFin_iff N ℓ y)⟩

end
end S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat (solution)
