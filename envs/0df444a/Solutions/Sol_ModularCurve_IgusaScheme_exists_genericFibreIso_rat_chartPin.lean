-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_genericFibreIso_rat_chartPin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/f9e6cc65-809a-5d0b-b194-334fa98cb10a

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_rat_chartPin
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve ModularCurve.IgusaScheme AlgebraicCurve

open scoped TensorProduct

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace S7Q

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve ModularCurve.IgusaScheme AlgebraicCurve AlgebraicCurve.CurveModel

section Charts

variable (N : ℕ) [NeZero N] (ℓ : ℕ)

omit [NeZero N] in

private theorem mem_adjoin_rat_of_mem_adjoin {S : Set ↥(modularFunctionFieldFull N)}
    {x : ↥(modularFunctionFieldFull N)}
    (hx : x ∈ Algebra.adjoin ↥(GaloisRep.ratLocalizedAt ℓ) S) :
    x ∈ Algebra.adjoin ℚ S := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
      rw [IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt ℓ) ℚ ↥(modularFunctionFieldFull N)]
      exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

omit [NeZero N] in

private theorem mem_chartRing_of_mem_chartAlg {S : Set ↥(modularFunctionFieldFull N)}
    {b : ↥(modularFunctionFieldFull N)} (hb : b ∈ chartAlg N ℓ S) :
    b ∈ chartRing ℚ S := by
  have hint : IsIntegral (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt ℓ) S) b := hb
  let ψ : ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt ℓ) S) →+* ↥(Algebra.adjoin ℚ S) :=
    (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt ℓ) S).val.toRingHom.codRestrict
      (Algebra.adjoin ℚ S).toSubring fun x => mem_adjoin_rat_of_mem_adjoin N ℓ x.2
  exact IsIntegral.map_of_comp_eq ψ (RingHom.id ↥(modularFunctionFieldFull N))
    (RingHom.ext fun _ => rfl) hint

private def ρ (S : Set ↥(modularFunctionFieldFull N)) :
    ↥(chartAlg N ℓ S) →+* ↥(chartRing ℚ S) :=
  (chartAlg N ℓ S).val.toRingHom.codRestrict (chartRing ℚ S)
    fun b => mem_chartRing_of_mem_chartAlg N ℓ b.2

omit [NeZero N] in
private theorem coe_ρ_apply (S : Set ↥(modularFunctionFieldFull N)) (b : ↥(chartAlg N ℓ S)) :
    (ρ N ℓ S b : ↥(modularFunctionFieldFull N)) = b :=
  RingHom.codRestrict_apply ((chartAlg N ℓ S).val.toRingHom) (chartRing ℚ S)
    (fun b => mem_chartRing_of_mem_chartAlg N ℓ b.2) b

omit [NeZero N] in

private theorem ρ_comp_algebraMap (S : Set ↥(modularFunctionFieldFull N)) :
    (ρ N ℓ S).comp (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlg N ℓ S)) =
      (algebraMap ℚ ↥(chartRing ℚ S)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) := by
  refine RingHom.ext fun q => Subtype.ext ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, coe_ρ_apply, Subalgebra.coe_algebraMap,
    Subalgebra.coe_algebraMap]
  exact IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt ℓ) ℚ ↥(modularFunctionFieldFull N) q

private abbrev ρFin : ↥(chartAlgFin N ℓ) →+*
    ↥(chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))) :=
  ρ N ℓ _

private abbrev ρInf : ↥(chartAlgInf N ℓ) →+*
    ↥(chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) :=
  ρ N ℓ _

private abbrev ρMid : ↥(chartAlgMid N ℓ) →+*
    ↥(chartRing ℚ ({jFull N, (jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) :=
  ρ N ℓ _

private theorem j_subset_pair :
    ({jFull N} : Set ↥(modularFunctionFieldFull N)) ⊆ {jFull N, (jFull N)⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert _ _)

private theorem j_inv_subset_pair :
    ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)) ⊆ {jFull N, (jFull N)⁻¹} :=
  Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ (Set.mem_singleton _))

variable [Fact ℓ.Prime]

private theorem square_fin :
    (AlgebraicCurve.CurveModel.chartIncl ℚ (j_subset_pair N)).toRingHom.comp (ρFin N ℓ) =
      (ρMid N ℓ).comp (ModularCurve.IgusaScheme.inclFin N ℓ).toRingHom := by
  refine RingHom.ext fun b => Subtype.ext ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [AlgebraicCurve.CurveModel.coe_chartIncl, coe_ρ_apply, coe_ρ_apply,
    ModularCurve.IgusaScheme.coe_chartIncl]

private theorem square_inf :
    (AlgebraicCurve.CurveModel.chartIncl ℚ (j_inv_subset_pair N)).toRingHom.comp (ρInf N ℓ) =
      (ρMid N ℓ).comp (ModularCurve.IgusaScheme.inclInf N ℓ).toRingHom := by
  refine RingHom.ext fun b => Subtype.ext ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [AlgebraicCurve.CurveModel.coe_chartIncl, coe_ρ_apply, coe_ρ_apply,
    ModularCurve.IgusaScheme.coe_chartIncl]

end Charts

section Schemes

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev uFin : X₀ ℚ (jFull N) ⟶ ModularCurve.IgusaScheme.XFin N ℓ :=
  Spec.map (CommRingCat.ofHom (ρFin N ℓ))

private abbrev uInf : CurveModel.XInf ℚ (jFull N) ⟶ ModularCurve.IgusaScheme.XInf N ℓ :=
  Spec.map (CommRingCat.ofHom (ρInf N ℓ))

private abbrev uMid : XOverlap ℚ (jFull N) ⟶ ModularCurve.IgusaScheme.XMid N ℓ :=
  Spec.map (CommRingCat.ofHom (ρMid N ℓ))

private theorem f₀_uFin :
    f₀ ℚ (jFull N) ≫ uFin N ℓ = uMid N ℓ ≫ ModularCurve.IgusaScheme.fFin N ℓ := by
  simp only [f₀, uFin, uMid, ModularCurve.IgusaScheme.fFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (square_fin N ℓ)

private theorem fInf_uInf :
    CurveModel.fInf ℚ (jFull N) ≫ uInf N ℓ = uMid N ℓ ≫ ModularCurve.IgusaScheme.fInf N ℓ := by
  simp only [CurveModel.fInf, uInf, uMid, ModularCurve.IgusaScheme.fInf, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (square_inf N ℓ)

private theorem glue_compat :
    f₀ ℚ (jFull N) ≫ (uFin N ℓ ≫ ModularCurve.IgusaScheme.ιFin N ℓ) =
      CurveModel.fInf ℚ (jFull N) ≫ (uInf N ℓ ≫ ModularCurve.IgusaScheme.ιInf N ℓ) := by
  rw [← Category.assoc, f₀_uFin, ← Category.assoc, fInf_uInf, Category.assoc, Category.assoc,
    ModularCurve.IgusaScheme.glue_condition]

private def u : glued ℚ (jFull N) ⟶ ModularCurve.IgusaScheme N ℓ :=
  pushout.desc (uFin N ℓ ≫ ModularCurve.IgusaScheme.ιFin N ℓ) (uInf N ℓ ≫ ModularCurve.IgusaScheme.ιInf N ℓ)
    (glue_compat N ℓ)

@[reassoc]
private theorem ι₀_u : ι₀ ℚ (jFull N) ≫ u N ℓ = uFin N ℓ ≫ ModularCurve.IgusaScheme.ιFin N ℓ :=
  pushout.inl_desc _ _ _

@[reassoc]
private theorem ιInf_u :
    CurveModel.ιInf ℚ (jFull N) ≫ u N ℓ = uInf N ℓ ≫ ModularCurve.IgusaScheme.ιInf N ℓ :=
  pushout.inr_desc _ _ _

private abbrev baseMap : Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)) :=
  Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))

omit [Fact ℓ.Prime] in
private theorem uFin_base :
    uFin N ℓ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ
        ↥(chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))))) ≫ baseMap ℓ := by
  simp only [uFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (ρ_comp_algebraMap N ℓ _)

omit [Fact ℓ.Prime] in
private theorem uInf_base :
    uInf N ℓ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ))) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ
        ↥(chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))))) ≫ baseMap ℓ := by
  simp only [uInf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h => Spec.map (CommRingCat.ofHom h)) (ρ_comp_algebraMap N ℓ _)

private theorem u_igusaTo : u N ℓ ≫ igusaTo N ℓ = gluedToBase ℚ (jFull N) ≫ baseMap ℓ := by
  refine pushout.hom_ext (f := f₀ ℚ (jFull N)) (g := CurveModel.fInf ℚ (jFull N)) ?_ ?_
  · change ι₀ ℚ (jFull N) ≫ u N ℓ ≫ igusaTo N ℓ = ι₀ ℚ (jFull N) ≫ gluedToBase ℚ (jFull N) ≫ baseMap ℓ
    rw [ι₀_u_assoc, ModularCurve.IgusaScheme.ιFin_igusaTo, uFin_base, ι₀_gluedToBase_assoc]
  · change CurveModel.ιInf ℚ (jFull N) ≫ u N ℓ ≫ igusaTo N ℓ =
      CurveModel.ιInf ℚ (jFull N) ≫ gluedToBase ℚ (jFull N) ≫ baseMap ℓ
    rw [ιInf_u_assoc, ModularCurve.IgusaScheme.ιInf_igusaTo, uInf_base, ιInf_gluedToBase_assoc]

private def eη : glued ℚ (jFull N) ⟶ pullback (igusaTo N ℓ) (baseMap ℓ) :=
  pullback.lift (u N ℓ) (gluedToBase ℚ (jFull N)) (u_igusaTo N ℓ)

@[reassoc (attr := simp)]
private theorem eη_fst : eη N ℓ ≫ pullback.fst (igusaTo N ℓ) (baseMap ℓ) = u N ℓ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem eη_snd : eη N ℓ ≫ pullback.snd (igusaTo N ℓ) (baseMap ℓ) = gluedToBase ℚ (jFull N) :=
  pullback.lift_snd _ _ _

private theorem ι₀_eη_fst :
    ι₀ ℚ (jFull N) ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) (baseMap ℓ) =
      uFin N ℓ ≫ ModularCurve.IgusaScheme.ιFin N ℓ := by
  rw [eη_fst, ι₀_u]

private theorem ιInf_eη_fst :
    CurveModel.ιInf ℚ (jFull N) ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) (baseMap ℓ) =
      uInf N ℓ ≫ ModularCurve.IgusaScheme.ιInf N ℓ := by
  rw [eη_fst, ιInf_u]

end Schemes

section ChartMatch

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

private theorem ig_ιFin_eq_ιInf_iff (x₀ : ModularCurve.IgusaScheme.XFin N ℓ)
    (xi : ModularCurve.IgusaScheme.XInf N ℓ) :
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

private theorem ρInf_jInvChartInf : ρInf N ℓ (jInvChartInf N ℓ) = tInvChart ℚ (jFull N) := by
  apply Subtype.ext
  rw [coe_ρ_apply, coe_jInvChartInf, coe_tInvChart]

omit [Fact ℓ.Prime] in
private theorem uInf_asIdeal (z : CurveModel.XInf ℚ (jFull N)) :
    ((uInf N ℓ).base z).asIdeal = z.asIdeal.comap (ρInf N ℓ) := rfl

private theorem u_mem_range_ιFin_iff (y : glued ℚ (jFull N)) :
    (u N ℓ).base y ∈ Set.range (ModularCurve.IgusaScheme.ιFin N ℓ).base ↔
      y ∈ Set.range (ι₀ ℚ (jFull N)).base := by
  rcases mem_range_ι₀_or_mem_range_ιInf ℚ (jFull N) y with ⟨x₀, rfl⟩ | ⟨z, rfl⟩
  · refine ⟨fun _ => ⟨x₀, rfl⟩, fun _ => ⟨(uFin N ℓ).base x₀, ?_⟩⟩
    change (uFin N ℓ ≫ ModularCurve.IgusaScheme.ιFin N ℓ).base x₀ = (ι₀ ℚ (jFull N) ≫ u N ℓ).base x₀
    rw [ι₀_u]
  · have hz : (u N ℓ).base ((CurveModel.ιInf ℚ (jFull N)).base z) =
        (ModularCurve.IgusaScheme.ιInf N ℓ).base ((uInf N ℓ).base z) := by
      change (CurveModel.ιInf ℚ (jFull N) ≫ u N ℓ).base z =
        (uInf N ℓ ≫ ModularCurve.IgusaScheme.ιInf N ℓ).base z
      rw [ιInf_u]
    rw [hz, ig_ιInf_mem_range_ιFin_iff, ιInf_mem_range_ι₀_iff, uInf_asIdeal, Ideal.mem_comap,
      ρInf_jInvChartInf]

end ChartMatch

section Tensor

open scoped TensorProduct

variable (N : ℕ) [NeZero N] (ℓ : ℕ)

private local instance instAlgebraRatLocalizedChartRing (S : Set ↥(modularFunctionFieldFull N)) :
    Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartRing ℚ S) :=
  ((algebraMap ℚ ↥(chartRing ℚ S)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)).toAlgebra

set_option synthInstance.maxHeartbeats 1600000 in

private def ρAlg (S : Set ↥(modularFunctionFieldFull N)) :
    ↥(chartAlg N ℓ S) →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartRing ℚ S) :=
  { ρ N ℓ S with
    commutes' := fun q => RingHom.congr_fun (ρ_comp_algebraMap N ℓ S) q }

set_option synthInstance.maxHeartbeats 1600000 in

private def incAlg (S : Set ↥(modularFunctionFieldFull N)) :
    ℚ →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartRing ℚ S) :=
  { algebraMap ℚ ↥(chartRing ℚ S) with
    commutes' := fun _ => rfl }

set_option synthInstance.maxHeartbeats 1600000 in

private def θ (S : Set ↥(modularFunctionFieldFull N)) :
    (↥(chartAlg N ℓ S) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ℚ) →+* ↥(chartRing ℚ S) :=
  (Algebra.TensorProduct.lift (ρAlg N ℓ S) (incAlg N ℓ S) fun _ _ => Commute.all _ _).toRingHom

omit [NeZero N] in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem θ_tmul (S : Set ↥(modularFunctionFieldFull N)) (b : ↥(chartAlg N ℓ S)) (c : ℚ) :
    θ N ℓ S (b ⊗ₜ c) = ρ N ℓ S b * algebraMap ℚ _ c :=
  Algebra.TensorProduct.lift_tmul (ρAlg N ℓ S) (incAlg N ℓ S) _ b c

omit [NeZero N] in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem θ_comp_includeLeft (S : Set ↥(modularFunctionFieldFull N)) :
    (θ N ℓ S).comp Algebra.TensorProduct.includeLeftRingHom = ρ N ℓ S := by
  refine RingHom.ext fun b => ?_
  rw [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply, θ_tmul, map_one, mul_one]

omit [NeZero N] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem θ_comp_includeRight (S : Set ↥(modularFunctionFieldFull N)) :
    (θ N ℓ S).comp
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
          ℚ →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ℚ)) =
      algebraMap ℚ ↥(chartRing ℚ S) := by
  refine RingHom.ext fun c => ?_
  simpa using θ_tmul N ℓ S 1 c

set_option synthInstance.maxHeartbeats 1600000 in

private abbrev θFin := θ N ℓ ({jFull N} : Set ↥(modularFunctionFieldFull N))

set_option synthInstance.maxHeartbeats 1600000 in

private abbrev θInf := θ N ℓ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))

end Tensor

section TensorLeft

open scoped TensorProduct

variable (N : ℕ) (ℓ : ℕ)

private abbrev cm (S : Set ↥(modularFunctionFieldFull N)) :=
  Algebra.TensorProduct.comm ↥(GaloisRep.ratLocalizedAt ℓ) ℚ ↥(chartAlg N ℓ S)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private def θL (S : Set ↥(modularFunctionFieldFull N)) :
    (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →ₐ[ℚ] ↥(chartRing ℚ S) where
  toRingHom := (θ N ℓ S).comp (cm N ℓ S : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) ≃+* _).toRingHom
  commutes' c := by
    show θ N ℓ S ((1 : ↥(chartAlg N ℓ S)) ⊗ₜ c) = algebraMap ℚ _ c
    rw [θ_tmul, map_one, one_mul]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_apply (S : Set ↥(modularFunctionFieldFull N)) (x : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S))) :
    θL N ℓ S x = θ N ℓ S (cm N ℓ S x) := rfl

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_tmul (S : Set ↥(modularFunctionFieldFull N)) (c : ℚ) (b : ↥(chartAlg N ℓ S)) :
    θL N ℓ S (c ⊗ₜ b) = ρ N ℓ S b * algebraMap ℚ _ c :=
  θ_tmul N ℓ S b c

set_option synthInstance.maxHeartbeats 1600000 in
private theorem θL_one_tmul (S : Set ↥(modularFunctionFieldFull N)) (b : ↥(chartAlg N ℓ S)) :
    θL N ℓ S (1 ⊗ₜ b) = ρ N ℓ S b := by
  rw [θL_tmul, map_one, mul_one]

end TensorLeft

section Consumption

open scoped TensorProduct

variable (N : ℕ) (ℓ : ℕ)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem ringHom_eq_θL (S : Set ↥(modularFunctionFieldFull N))
    (e : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →ₐ[ℚ] ↥(chartRing ℚ S))
    (he : ∀ b : ↥(chartAlg N ℓ S),
      ((e (1 ⊗ₜ b) : ↥(chartRing ℚ S)) : ↥(modularFunctionFieldFull N)) = b)
    (y : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S))) :
    (e : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing ℚ S)) y = (θL N ℓ S : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing ℚ S)) y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ((e : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing ℚ S)).map_zero).trans ((θL N ℓ S : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing ℚ S)).map_zero).symm
  | tmul c b =>
    have hA : (e : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing ℚ S)) (algebraMap ℚ _ c) = (θL N ℓ S : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing ℚ S)) (algebraMap ℚ _ c) :=
      (e.commutes c).trans ((θL N ℓ S).commutes c).symm
    have hB : (e : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing ℚ S)) (1 ⊗ₜ b) = (θL N ℓ S : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing ℚ S)) (1 ⊗ₜ b) :=
      (Subtype.ext ((he b).trans (coe_ρ_apply N ℓ S b).symm)).trans (θL_one_tmul N ℓ S b).symm
    have hc : (c ⊗ₜ b : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S))) = algebraMap ℚ _ c * (1 ⊗ₜ b) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    exact (congrArg (e : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing ℚ S)) hc).trans (((e : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing ℚ S)).map_mul _ _).trans
      ((congr (congrArg (@HMul.hMul _ _ _ _) hA) hB).trans (((θL N ℓ S : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing ℚ S)).map_mul _ _).symm.trans
        (congrArg (θL N ℓ S : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing ℚ S)) hc.symm))))
  | add x y hx hy =>
    exact ((e : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing ℚ S)).map_add x y).trans
      ((congr (congrArg (@HAdd.hAdd _ _ _ _) hx) hy).trans ((θL N ℓ S : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →+* ↥(chartRing ℚ S)).map_add x y).symm)

set_option synthInstance.maxHeartbeats 1600000 in
private theorem algHom_apply_eq_θL (S : Set ↥(modularFunctionFieldFull N))
    (e : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →ₐ[ℚ] ↥(chartRing ℚ S))
    (he : ∀ b : ↥(chartAlg N ℓ S),
      ((e (1 ⊗ₜ b) : ↥(chartRing ℚ S)) : ↥(modularFunctionFieldFull N)) = b)
    (x : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S))) : e x = θL N ℓ S x :=
  ringHom_eq_θL N ℓ S e he x

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem θ_bijective_of_algEquiv (S : Set ↥(modularFunctionFieldFull N))
    (e : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) ≃ₐ[ℚ] ↥(chartRing ℚ S))
    (he : ∀ b : ↥(chartAlg N ℓ S),
      ((e (1 ⊗ₜ b) : ↥(chartRing ℚ S)) : ↥(modularFunctionFieldFull N)) = b) :
    Function.Bijective (θ N ℓ S) := by
  have hL : ∀ x, θL N ℓ S x = e x := fun x =>
    (algHom_apply_eq_θL N ℓ S (e : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) →ₐ[ℚ] ↥(chartRing ℚ S)) he x).symm
  have hcm : ∀ x, θL N ℓ S ((cm N ℓ S).symm x) = θ N ℓ S x := fun x =>
    (θL_apply N ℓ S _).trans (congrArg (θ N ℓ S) ((cm N ℓ S).apply_symm_apply x))
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · have h' : e ((cm N ℓ S).symm x) = e ((cm N ℓ S).symm y) :=
      ((hL _).symm.trans ((hcm x).trans (hxy.trans ((hcm y).symm.trans (hL _)))))
    exact (cm N ℓ S).symm.injective (e.injective h')
  · obtain ⟨w, hw⟩ := e.surjective z
    exact ⟨cm N ℓ S w, (θL_apply N ℓ S w).symm.trans ((hL w).trans hw)⟩

end Consumption

section Iso

open scoped TensorProduct

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev PFin := pullback (ModularCurve.IgusaScheme.ιFin N ℓ) (pullback.fst (igusaTo N ℓ) (baseMap ℓ))

private abbrev PInf := pullback (ModularCurve.IgusaScheme.ιInf N ℓ) (pullback.fst (igusaTo N ℓ) (baseMap ℓ))

private def φFin : X₀ ℚ (jFull N) ⟶ PFin N ℓ :=
  pullback.lift (uFin N ℓ) (ι₀ ℚ (jFull N) ≫ eη N ℓ) (by rw [Category.assoc, ι₀_eη_fst])

private def φInf : CurveModel.XInf ℚ (jFull N) ⟶ PInf N ℓ :=
  pullback.lift (uInf N ℓ) (CurveModel.ιInf ℚ (jFull N) ≫ eη N ℓ) (by rw [Category.assoc, ιInf_eη_fst])

@[reassoc (attr := simp)]
private theorem φFin_fst : φFin N ℓ ≫ pullback.fst _ _ = uFin N ℓ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem φFin_snd : φFin N ℓ ≫ pullback.snd _ _ = ι₀ ℚ (jFull N) ≫ eη N ℓ := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
private theorem φInf_fst : φInf N ℓ ≫ pullback.fst _ _ = uInf N ℓ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem φInf_snd : φInf N ℓ ≫ pullback.snd _ _ = CurveModel.ιInf ℚ (jFull N) ≫ eη N ℓ :=
  pullback.lift_snd _ _ _

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem SpecMap_θFin_eq :
    Spec.map (CommRingCat.ofHom (θFin N ℓ)) ≫
        (pullbackSpecIso ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ) ℚ).inv =
      φFin N ℓ ≫ (pullbackRightPullbackFstIso (igusaTo N ℓ) (baseMap ℓ) (ModularCurve.IgusaScheme.ιFin N ℓ)).hom ≫
        (pullback.congrHom (ModularCurve.IgusaScheme.ιFin_igusaTo N ℓ) rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      θ_comp_includeLeft]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, φFin_fst]
    try rfl
  · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [θ_comp_includeRight N ℓ _]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd, φFin_snd_assoc, eη_snd, ι₀_gluedToBase]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem SpecMap_θInf_eq :
    Spec.map (CommRingCat.ofHom (θInf N ℓ)) ≫
        (pullbackSpecIso ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ) ℚ).inv =
      φInf N ℓ ≫ (pullbackRightPullbackFstIso (igusaTo N ℓ) (baseMap ℓ) (ModularCurve.IgusaScheme.ιInf N ℓ)).hom ≫
        (pullback.congrHom (ModularCurve.IgusaScheme.ιInf_igusaTo N ℓ) rfl).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      θ_comp_includeLeft]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
      pullbackRightPullbackFstIso_hom_fst, φInf_fst]
    try rfl
  · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [θ_comp_includeRight N ℓ _]
    simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd, φInf_snd_assoc, eη_snd, ιInf_gluedToBase]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isIso_φFin (hfin : Function.Bijective (θFin N ℓ)) : IsIso (φFin N ℓ) := by
  haveI : IsIso (CommRingCat.ofHom (R := ↥(chartAlg N ℓ ({jFull N} : Set ↥(modularFunctionFieldFull N))) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ℚ)
      (S := ↥(chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))) (θFin N ℓ)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (by simpa using hfin)
  haveI : IsIso (Spec.map (CommRingCat.ofHom (R := ↥(chartAlg N ℓ ({jFull N} : Set ↥(modularFunctionFieldFull N))) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ℚ)
      (S := ↥(chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))) (θFin N ℓ))) := inferInstance
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
  haveI : IsIso (CommRingCat.ofHom (R := ↥(chartAlg N ℓ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ℚ)
      (S := ↥(chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))) (θInf N ℓ)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (by simpa using hinf)
  haveI : IsIso (Spec.map (CommRingCat.ofHom (R := ↥(chartAlg N ℓ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))) ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ℚ)
      (S := ↥(chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))) (θInf N ℓ))) := inferInstance
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
    IsOpenImmersion (ι₀ ℚ (jFull N) ≫ eη N ℓ) := by
  haveI := isIso_φFin N ℓ hfin
  rw [← φFin_snd]
  infer_instance

set_option synthInstance.maxHeartbeats 1600000 in
private theorem isOpenImmersion_ιInf_eη (hinf : Function.Bijective (θInf N ℓ)) :
    IsOpenImmersion (CurveModel.ιInf ℚ (jFull N) ≫ eη N ℓ) := by
  haveI := isIso_φInf N ℓ hinf
  rw [← φInf_snd]
  infer_instance

set_option synthInstance.maxHeartbeats 1600000 in

private theorem u_eq_of_eη_eq {y y' : glued ℚ (jFull N)} (h : eη N ℓ y = eη N ℓ y') : u N ℓ y = u N ℓ y' := by
  have h1 := congrArg (pullback.fst (igusaTo N ℓ) (baseMap ℓ)) h
  rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, eη_fst] at h1

set_option synthInstance.maxHeartbeats 1600000 in
private theorem injective_eη (hfin : Function.Bijective (θFin N ℓ)) (hinf : Function.Bijective (θInf N ℓ)) :
    Function.Injective (eη N ℓ) := by
  intro y y' h
  have hu := u_eq_of_eη_eq N ℓ h

  have hu' : (u N ℓ).base y = (u N ℓ).base y' := hu
  have hsame : y ∈ Set.range (ι₀ ℚ (jFull N)).base ↔ y' ∈ Set.range (ι₀ ℚ (jFull N)).base := by
    rw [← u_mem_range_ιFin_iff N ℓ y, ← u_mem_range_ιFin_iff N ℓ y', hu']
  by_cases hy : y ∈ Set.range (ι₀ ℚ (jFull N)).base
  · obtain ⟨a, rfl⟩ := hy
    obtain ⟨a', rfl⟩ := hsame.mp ⟨a, rfl⟩
    haveI := isOpenImmersion_ι₀_eη N ℓ hfin
    have : (ι₀ ℚ (jFull N) ≫ eη N ℓ) a = (ι₀ ℚ (jFull N) ≫ eη N ℓ) a' := h
    rw [(ι₀ ℚ (jFull N) ≫ eη N ℓ).isOpenEmbedding.injective this]
  · have hy' : y' ∉ Set.range (ι₀ ℚ (jFull N)).base := fun h' => hy (hsame.mpr h')
    obtain ⟨a, rfl⟩ := (mem_range_ι₀_or_mem_range_ιInf ℚ (jFull N) y).resolve_left hy
    obtain ⟨a', rfl⟩ := (mem_range_ι₀_or_mem_range_ιInf ℚ (jFull N) y').resolve_left hy'
    haveI := isOpenImmersion_ιInf_eη N ℓ hinf
    have : (CurveModel.ιInf ℚ (jFull N) ≫ eη N ℓ) a = (CurveModel.ιInf ℚ (jFull N) ≫ eη N ℓ) a' := h
    rw [(CurveModel.ιInf ℚ (jFull N) ≫ eη N ℓ).isOpenEmbedding.injective this]

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
    exact ⟨ι₀ ℚ (jFull N) a, by
      show (ι₀ ℚ (jFull N) ≫ eη N ℓ) a = (φFin N ℓ ≫ pullback.snd _ _) a
      rw [φFin_snd]⟩
  · have hp' : p ∈ Set.range (pullback.snd (ModularCurve.IgusaScheme.ιInf N ℓ)
        (pullback.fst (igusaTo N ℓ) (baseMap ℓ))) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      exact hp
    obtain ⟨r, rfl⟩ := hp'
    haveI := isIso_φInf N ℓ hinf
    obtain ⟨a, rfl⟩ := (φInf N ℓ).homeomorph.surjective r
    exact ⟨CurveModel.ιInf ℚ (jFull N) a, by
      show (CurveModel.ιInf ℚ (jFull N) ≫ eη N ℓ) a = (φInf N ℓ ≫ pullback.snd _ _) a
      rw [φInf_snd]⟩

set_option synthInstance.maxHeartbeats 1600000 in

private theorem isIso_eη_of_bijective (hfin : Function.Bijective (θFin N ℓ))
    (hinf : Function.Bijective (θInf N ℓ)) : IsIso (eη N ℓ) := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨?_, ⟨surjective_eη N ℓ hfin hinf⟩⟩
  refine IsOpenImmersion.of_forall_source_exists _ (injective_eη N ℓ hfin hinf) fun y => ?_
  rcases mem_range_ι₀_or_mem_range_ιInf ℚ (jFull N) y with hy | hy
  · exact ⟨_, ι₀ ℚ (jFull N), inferInstance, hy, isOpenImmersion_ι₀_eη N ℓ hfin⟩
  · exact ⟨_, CurveModel.ιInf ℚ (jFull N), inferInstance, hy, isOpenImmersion_ιInf_eη N ℓ hinf⟩

end Iso

section Pin

open scoped TensorProduct

private theorem algEquiv_comp_includeRight_eq_ρ (N : ℕ) (ℓ : ℕ) (S : Set ↥(modularFunctionFieldFull N))
    (e : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlg N ℓ S)) ≃ₐ[ℚ] ↥(AlgebraicCurve.CurveModel.chartRing ℚ S))
    (he : ∀ b : ↥(chartAlg N ℓ S),
      ((e (1 ⊗ₜ b) : ↥(AlgebraicCurve.CurveModel.chartRing ℚ S)) : ↥(modularFunctionFieldFull N)) = b) :
    e.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ℚ)
          (B := ↥(chartAlg N ℓ S))).toRingHom =
      ρ N ℓ S :=
  RingHom.ext fun b => Subtype.ext ((he b).trans (coe_ρ_apply N ℓ S b).symm)

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

private theorem ι₀_pin
    (e : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ)) ≃ₐ[ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))))
    (he : ∀ b : ↥(chartAlgFin N ℓ), ((e (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))) : ↥(modularFunctionFieldFull N)) = b) :
    AlgebraicCurve.CurveModel.ι₀ ℚ (jFull N) ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) _ =
    Spec.map (CommRingCat.ofHom (e.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight
        (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ℚ) (B := ↥(chartAlgFin N ℓ))).toRingHom)) ≫
      ModularCurve.IgusaScheme.ιFin N ℓ :=
  (ι₀_eη_fst N ℓ).trans
    (congrArg (fun h => Spec.map (CommRingCat.ofHom h) ≫ ModularCurve.IgusaScheme.ιFin N ℓ)
      (algEquiv_comp_includeRight_eq_ρ N ℓ ({jFull N} : Set ↥(modularFunctionFieldFull N)) e he).symm)

private theorem ιInf_pin
    (e : (ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ)) ≃ₐ[ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))))
    (he : ∀ b : ↥(chartAlgInf N ℓ), ((e (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))) : ↥(modularFunctionFieldFull N)) = b) :
    AlgebraicCurve.CurveModel.ιInf ℚ (jFull N) ≫ eη N ℓ ≫ pullback.fst (igusaTo N ℓ) _ =
    Spec.map (CommRingCat.ofHom (e.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight
        (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ℚ) (B := ↥(chartAlgInf N ℓ))).toRingHom)) ≫
      ModularCurve.IgusaScheme.ιInf N ℓ :=
  (ιInf_eη_fst N ℓ).trans
    (congrArg (fun h => Spec.map (CommRingCat.ofHom h) ≫ ModularCurve.IgusaScheme.ιInf N ℓ)
      (algEquiv_comp_includeRight_eq_ρ N ℓ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)) e he).symm)

end Pin

end S7Q

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (htrans : Transcendental ℚ (jFull N))
    [hne : Fact (jFull N ≠ 0)]
    [hfd : FiniteDimensional
      ↥(IntermediateField.adjoin ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))
      ↥(modularFunctionFieldFull N)]
    [hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))
      ↥(modularFunctionFieldFull N)]
    (eFin : ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) ≃ₐ[ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N))))
    (hFin : ∀ b : chartAlgFin N ℓ,
      ((eFin (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({jFull N} : Set ↥(modularFunctionFieldFull N)))) :
          ↥(modularFunctionFieldFull N)) = (b : ↥(modularFunctionFieldFull N)))
    (eInf : ℚ ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) ≃ₐ[ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N))))
    (hInf : ∀ b : chartAlgInf N ℓ,
      ((eInf (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing ℚ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)))) :
          ↥(modularFunctionFieldFull N)) = (b : ↥(modularFunctionFieldFull N))) :
    let M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N) :=
      CurveModel.ofGenerator ℚ (jFull N) htrans
    ∃ (e₀ : M₀.C ⟶ pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)))) (_ : IsIso e₀),
      e₀ ≫ pullback.snd (igusaTo N ℓ) _ = M₀.toBase ∧
      (AlgebraicCurve.CurveModel.ι₀ ℚ (jFull N) ≫ e₀ ≫ pullback.fst (igusaTo N ℓ) _ =
        Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ℚ) (B := ↥(chartAlgFin N ℓ))).toRingHom)) ≫
          ModularCurve.IgusaScheme.ιFin N ℓ) ∧
      (AlgebraicCurve.CurveModel.ιInf ℚ (jFull N) ≫ e₀ ≫ pullback.fst (igusaTo N ℓ) _ =
        Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := ℚ) (B := ↥(chartAlgInf N ℓ))).toRingHom)) ≫
          ModularCurve.IgusaScheme.ιInf N ℓ) := by
  intro M₀
  have hbF : Function.Bijective (S7Q.θFin N ℓ) :=
    S7Q.θ_bijective_of_algEquiv N ℓ ({jFull N} : Set ↥(modularFunctionFieldFull N)) eFin hFin
  have hbI : Function.Bijective (S7Q.θInf N ℓ) :=
    S7Q.θ_bijective_of_algEquiv N ℓ ({(jFull N)⁻¹} : Set ↥(modularFunctionFieldFull N)) eInf hInf
  exact ⟨S7Q.eη N ℓ, S7Q.isIso_eη_of_bijective N ℓ hbF hbI, S7Q.eη_snd N ℓ,
    S7Q.ι₀_pin N ℓ eFin hFin, S7Q.ιInf_pin N ℓ eInf hInf⟩

end

end S_ModularCurve_IgusaScheme_exists_genericFibreIso_rat_chartPin
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_genericFibreIso_rat_chartPin (solution)
