-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.iotaInf_comp_dia_hom_eq_spec_map_comp_iotaInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/4d2456be-9a20-5494-a240-62a5659c8aee

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_AlgebraicGeometry_eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
import Theorems.Thm_ModularCurve_XHDRModelAtP_coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_iotaInf_comp_dia_hom_eq_spec_map_comp_iotaInf

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_iotaInf_comp_dia_hom_eq_spec_map_comp_iotaInf.ModularCurve ModularCurve.XHDRLevel"
open scoped MatrixGroups TensorProduct

noncomputable section

namespace DiaChart

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
  (𝔓 : XHDRModelAtP p M H hpM hj) (d : (ZMod M)ˣ)

local notation "𝕂" => AlgebraicClosure ℚ

abbrev Xbar : Scheme.{0} :=
  pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) 𝕂)))

def diaBar : Xbar (p := p) (M := M) (H := H) (hj := hj) ⟶ Xbar (p := p) (M := M) (H := H) (hj := hj) :=
  pullback.map _ _ _ _ (𝔓.dia d).hom (𝟙 _) (𝟙 _)
    (by rw [𝔓.dia_over d, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])

scoped instance isIso_diaBar : IsIso (diaBar 𝔓 d) := by
  unfold diaBar; infer_instance

@[reassoc] theorem diaBar_fst : diaBar 𝔓 d ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (𝔓.dia d).hom := by
  unfold diaBar; exact pullback.lift_fst _ _ _

@[reassoc] theorem diaBar_snd : diaBar 𝔓 d ≫ pullback.snd _ _ = pullback.snd _ _ := by
  unfold diaBar; rw [pullback.lift_snd, Category.comp_id]

def delta : 𝔓.Meta.C ⟶ 𝔓.Meta.C :=
  haveI := 𝔓.eeta_iso
  𝔓.eeta ≫ diaBar 𝔓 d ≫ inv 𝔓.eeta

scoped instance isIso_delta : IsIso (delta 𝔓 d) := by
  haveI := 𝔓.eeta_iso
  unfold delta; infer_instance

theorem delta_eeta : delta 𝔓 d ≫ 𝔓.eeta = 𝔓.eeta ≫ diaBar 𝔓 d := by
  haveI := 𝔓.eeta_iso
  simp [delta]

theorem delta_e : delta 𝔓 d ≫ 𝔓.eeta ≫ pullback.fst _ _ = (𝔓.eeta ≫ pullback.fst _ _) ≫ (𝔓.dia d).hom := by
  rw [← Category.assoc, delta_eeta, Category.assoc, diaBar_fst, Category.assoc]

theorem delta_toBase : delta 𝔓 d ≫ 𝔓.Meta.toBase = 𝔓.Meta.toBase := by
  rw [← 𝔓.heeta, ← Category.assoc, delta_eeta, Category.assoc, diaBar_snd]

def translate (x : {s : Spec (CommRingCat.of 𝕂) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _}) :
    {s : Spec (CommRingCat.of 𝕂) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _} :=
  ⟨x.1 ≫ delta 𝔓 d, by rw [Category.assoc, delta_toBase]; exact x.2⟩

theorem pointEquivPlace_translate (x : {s : Spec (CommRingCat.of 𝕂) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _}) :
    𝔓.Meta.pointEquivPlace (translate 𝔓 d x) =
      SemilinearAut.ofAlgAut (diamondAutHBar M H d) • 𝔓.Meta.pointEquivPlace x := by
  refine 𝔓.dia_generic d x (translate 𝔓 d x) ?_
  show (x.1 ≫ delta 𝔓 d) ≫ 𝔓.eeta ≫ pullback.fst _ _ = x.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ ≫ (𝔓.dia d).hom
  rw [Category.assoc, delta_e, Category.assoc]

variable (ρ : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] 𝕂)

def liftBar : Spec (CommRingCat.of 𝕂) ⟶ Xbar (p := p) (M := M) (H := H) (hj := hj) :=
  pullback.lift (Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ ιInf p (ΓM M H) hj) (𝟙 _) (by
    rw [Category.assoc, TwoChartIntegralModel.ιInf_toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Category.id_comp]
    congr 2
    exact RingHom.ext fun r => ρ.commutes r)

@[reassoc (attr := simp)] theorem liftBar_fst : liftBar ρ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ ιInf p (ΓM M H) hj :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem liftBar_snd : liftBar (p := p) (M := M) (H := H) (hj := hj) ρ ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

private def _root_.DiaChart.lift : {s : Spec (CommRingCat.of 𝕂) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _} :=
  haveI := 𝔓.eeta_iso
  ⟨liftBar ρ ≫ inv 𝔓.eeta, by rw [← 𝔓.heeta, Category.assoc, IsIso.inv_hom_id_assoc, liftBar_snd]⟩

p2m_export "DiaChart" "lift"
theorem lift_eeta : (lift 𝔓 ρ).1 ≫ 𝔓.eeta = liftBar ρ := by
  haveI := 𝔓.eeta_iso
  show (liftBar ρ ≫ inv 𝔓.eeta) ≫ 𝔓.eeta = liftBar ρ
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

abbrev precomp (σ : ↥(chartAlgInf p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj)) :
    ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] 𝕂 :=
  ρ.comp (σ : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj))

theorem translate_lift_eeta : (translate 𝔓 d (lift 𝔓 ρ)).1 ≫ 𝔓.eeta = liftBar ρ ≫ diaBar 𝔓 d := by
  show ((lift 𝔓 ρ).1 ≫ delta 𝔓 d) ≫ 𝔓.eeta = liftBar ρ ≫ diaBar 𝔓 d
  rw [Category.assoc, delta_eeta, ← Category.assoc, lift_eeta]

end DiaChart
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_iotaInf_comp_dia_hom_eq_spec_map_comp_iotaInf.DiaChart"

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_iotaInf_comp_dia_hom_eq_spec_map_comp_iotaInf.DiaChart"

noncomputable section

namespace DiaChart

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
  (𝔓 : XHDRModelAtP p M H hpM hj)

local notation "𝕂" => AlgebraicClosure ℚ

def bhat (b : ↥(chartAlgInf p (ΓM M H) hj)) : ↥(xHFunctionFieldBar M H) :=
  ⟨coeffEmb 𝕂 ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
    coeffEmb_mem_laurentBaseChange 𝕂 (b : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩

def ahat (a : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(xHFunctionFieldBar M H) :=
  ⟨coeffEmb 𝕂 ((a : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
    coeffEmb_mem_laurentBaseChange 𝕂 (a : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩

theorem ahat_jChartFin_mul_bhat_jInvChartInf :
    ahat (p := p) (M := M) (H := H) (hj := hj) (TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)) * bhat (p := p) (M := M) (H := H) (hj := hj) (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)) = 1 := by
  apply Subtype.ext
  show coeffEmb 𝕂 ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) *
      coeffEmb 𝕂 (((jAt (ΓM M H) hj)⁻¹ : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = 1
  have hne : (jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) ≠ 0 := Fact.out
  have h1 : ((jAt (ΓM M H) hj * (jAt (ΓM M H) hj)⁻¹ : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((jAt (ΓM M H) hj : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) *
        (((jAt (ΓM M H) hj)⁻¹ : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) := rfl
  rw [← map_mul, ← h1, mul_inv_cancel₀ hne]
  show coeffEmb 𝕂 (1 : LaurentSeries ℚ) = 1
  exact map_one _

variable (P : {s : Spec (CommRingCat.of 𝕂) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _})

theorem val_eeta_fst_toBase :
    (P.1 ≫ 𝔓.eeta ≫ pullback.fst _ _) ≫ toBase p (ΓM M H) hj =
      Spec.map (CommRingCat.ofHom (algebraMap (R p) 𝕂)) := by
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔓.eeta, 𝔓.heeta, ← Category.assoc, P.2,
    Category.id_comp]

theorem exists_eq_lift_of_comp_eq (z : Spec (CommRingCat.of 𝕂) ⟶ TwoChartIntegralModel.XInf (R p) _ (jAt (ΓM M H) hj))
    (hz : P.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ = z ≫ ιInf p (ΓM M H) hj) :
    ∃ χ : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] 𝕂, P = DiaChart.lift 𝔓 χ := by
  haveI := 𝔓.eeta_iso

  set r : ↥(chartAlgInf p (ΓM M H) hj) →+* 𝕂 := (Spec.preimage z).hom with hr
  have hzr : z = Spec.map (CommRingCat.ofHom r) := by
    rw [hr, CommRingCat.ofHom_hom, Spec.map_preimage]

  have hcomm : r.comp (algebraMap (R p) ↥(chartAlgInf p (ΓM M H) hj)) = algebraMap (R p) 𝕂 := by
    have h1 := val_eeta_fst_toBase 𝔓 P
    rw [hz, Category.assoc, hzr] at h1
    erw [TwoChartIntegralModel.ιInf_toBase] at h1
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at h1
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  let χ : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] 𝕂 :=
    { toRingHom := r, commutes' := fun c => RingHom.congr_fun hcomm c }
  refine ⟨χ, ?_⟩
  apply Subtype.ext

  have key : P.1 ≫ 𝔓.eeta = (DiaChart.lift 𝔓 χ).1 ≫ 𝔓.eeta := by
    rw [DiaChart.lift_eeta]
    apply pullback.hom_ext
    · rw [Category.assoc, hz, DiaChart.liftBar_fst, hzr]
    · rw [Category.assoc, 𝔓.heeta, P.2, DiaChart.liftBar_snd]
  exact (cancel_mono 𝔓.eeta).mp key

theorem place_eq_pointEquivPlace_lift_of_forall_hasValue
    (hread : ∀ (χ : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] 𝕂) (b : ↥(chartAlgInf p (ΓM M H) hj)),
      (𝔓.Meta.pointEquivPlace (DiaChart.lift 𝔓 χ)).HasValue (bhat b) (χ b))
    (hreadFin : ∀ (Q : {s : Spec (CommRingCat.of 𝕂) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _})
      (r' : ↥(chartAlgFin p (ΓM M H) hj) →+* 𝕂),
      Q.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom r') ≫ ιFin p (ΓM M H) hj →
        (𝔓.Meta.pointEquivPlace Q).HasValue (ahat (p := p) (M := M) (H := H) (hj := hj) (TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))) (r' (TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))))
    (χ : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] 𝕂) (w : Place 𝕂 ↥(xHFunctionFieldBar M H))
    (hw : ∀ b : ↥(chartAlgInf p (ΓM M H) hj), w.HasValue (bhat b) (χ b)) :
    w = 𝔓.Meta.pointEquivPlace (DiaChart.lift 𝔓 χ) := by
  haveI := 𝔓.eeta_iso

  set P := 𝔓.Meta.pointEquivPlace.symm w with hP
  have hwP : w = 𝔓.Meta.pointEquivPlace P := by rw [hP, Equiv.apply_symm_apply]

  suffices hfac : ∃ z : Spec (CommRingCat.of 𝕂) ⟶ TwoChartIntegralModel.XInf (R p) _ (jAt (ΓM M H) hj),
      P.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ = z ≫ ιInf p (ΓM M H) hj by
    obtain ⟨z, hz⟩ := hfac
    obtain ⟨χ', hχ'⟩ := exists_eq_lift_of_comp_eq 𝔓 P z hz
    have hw' : w = 𝔓.Meta.pointEquivPlace (DiaChart.lift 𝔓 χ') := by rw [hwP, hχ']

    have hχ : χ' = χ := by
      refine AlgHom.ext fun b => ?_
      exact Place.HasValue.unique (hread χ' b) (hw' ▸ hw b)
    rw [hw', hχ]

  set Qm := P.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ with hQm
  rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf (R p) _ (jAt (ΓM M H) hj)
    (Qm.base (IsLocalRing.closedPoint 𝕂)) with hfin | hinf
  ·
    have hsub : Set.range Qm.base ⊆ Set.range (ιFin p (ΓM M H) hj).base := by
      rintro _ ⟨y, rfl⟩
      rw [Subsingleton.elim y (IsLocalRing.closedPoint 𝕂)]
      exact hfin
    set z' := IsOpenImmersion.lift (ιFin p (ΓM M H) hj) Qm hsub with hz'
    have hz'fac : z' ≫ ιFin p (ΓM M H) hj = Qm := IsOpenImmersion.lift_fac _ _ _
    set r' : ↥(chartAlgFin p (ΓM M H) hj) →+* 𝕂 := (Spec.preimage z').hom with hr'
    have hz'r : z' = Spec.map (CommRingCat.ofHom r') := by
      rw [hr', CommRingCat.ofHom_hom, Spec.map_preimage]

    have hval := hreadFin P r' (by rw [← hQm, ← hz'fac, hz'r])
    have hval' := hw (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))
    have hprod := Place.HasValue.mul hval (hwP ▸ hval')
    rw [ahat_jChartFin_mul_bhat_jInvChartInf] at hprod
    have h1 : (𝔓.Meta.pointEquivPlace P).HasValue 1 (1 : 𝕂) := by
      simpa using Place.hasValue_algebraMap (𝔓.Meta.pointEquivPlace P) (1 : 𝕂)
    have hunit : IsUnit (r' (TwoChartIntegralModel.jChartFin _ _ _)) :=
      IsUnit.of_mul_eq_one _ (Place.HasValue.unique hprod h1)

    letI := (TwoChartIntegralModel.inclFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)).toRingHom.toAlgebra
    haveI := TwoChartIntegralModel.isLocalization_away_inclFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
    set r'' := IsLocalization.Away.lift (TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))
      (S := ↥(TwoChartIntegralModel.chartAlgMid (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))) hunit with hr''
    have hr''comp : r''.comp (TwoChartIntegralModel.inclFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)).toRingHom = r' :=
      IsLocalization.Away.lift_comp _ hunit
    refine ⟨Spec.map (CommRingCat.ofHom r'') ≫ TwoChartIntegralModel.fInf (R p) _ (jAt (ΓM M H) hj), ?_⟩
    rw [Category.assoc, ← TwoChartIntegralModel.glue_condition, ← Category.assoc,
      TwoChartIntegralModel.fFin, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hr''comp, ← hz'r, hz'fac]
  ·
    have hsub : Set.range Qm.base ⊆ Set.range (ιInf p (ΓM M H) hj).base := by
      rintro _ ⟨y, rfl⟩
      rw [Subsingleton.elim y (IsLocalRing.closedPoint 𝕂)]
      exact hinf
    exact ⟨IsOpenImmersion.lift (ιInf p (ΓM M H) hj) Qm hsub, (IsOpenImmersion.lift_fac _ _ _).symm⟩

theorem hasValue_smul {L F : Type*} [Field L] [Field F] [Algebra L F] (g : SemilinearAut L F) (v : Place L F)
    {x : F} {a : L} (h : v.HasValue x a) : (g • v).HasValue (g • x) (SemilinearAut.baseAut g a) := by
  obtain ⟨hx, hres⟩ := h
  have hmem : g • x ∈ (g • v).toValuationSubring := by
    rw [SemilinearAut.smul_toValuationSubring]
    exact ValuationSubring.smul_mem_pointwise_smul g x v.toValuationSubring hx
  refine ⟨hmem, ?_⟩
  have key : IsLocalRing.residue (g • v).toValuationSubring
      (SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨x, hx⟩) =
      SemilinearAut.smulResidueRingEquiv g v (IsLocalRing.residue v.toValuationSubring ⟨x, hx⟩) := by
    rw [SemilinearAut.smulResidueRingEquiv, IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue]
    rfl
  have hx' : (⟨g • x, hmem⟩ : (g • v).toValuationSubring) =
      SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨x, hx⟩ := rfl
  rw [hx', key, hres, SemilinearAut.smulResidueRingEquiv_algebraMap]

theorem hasValue_ofAlgAut_smul {L F : Type*} [Field L] [Field F] [Algebra L F] (φ : F ≃ₐ[L] F) (v : Place L F)
    {x : F} {a : L} (h : v.HasValue x a) : (SemilinearAut.ofAlgAut φ • v).HasValue (φ x) a := by
  have := hasValue_smul (SemilinearAut.ofAlgAut φ) v h
  rwa [SemilinearAut.ofAlgAut_smul, SemilinearAut.baseAut_ofAlgAut] at this

theorem pointEquivPlace_lift_precomp (d : (ZMod M)ˣ)
    (hread : ∀ (χ : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] 𝕂) (b : ↥(chartAlgInf p (ΓM M H) hj)),
      (𝔓.Meta.pointEquivPlace (DiaChart.lift 𝔓 χ)).HasValue (bhat b) (χ b))
    (hreadFin : ∀ (Q : {s : Spec (CommRingCat.of 𝕂) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _})
      (r' : ↥(chartAlgFin p (ΓM M H) hj) →+* 𝕂),
      Q.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom r') ≫ ιFin p (ΓM M H) hj →
        (𝔓.Meta.pointEquivPlace Q).HasValue (ahat (p := p) (M := M) (H := H) (hj := hj) (TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))) (r' (TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))))
    (σ : ↥(chartAlgInf p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj))
    (hσ : ∀ b : ↥(chartAlgInf p (ΓM M H) hj),
      coeffEmb (AlgebraicClosure ℚ) (((σ b : ↥(chartAlgInf p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        (((diamondAutHBar M H d).symm
            ⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩
          : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)))
    (ρ : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] 𝕂) :
    𝔓.Meta.pointEquivPlace (DiaChart.lift 𝔓 (DiaChart.precomp ρ σ)) =
      SemilinearAut.ofAlgAut (diamondAutHBar M H d) • 𝔓.Meta.pointEquivPlace (DiaChart.lift 𝔓 ρ) := by
  symm
  refine place_eq_pointEquivPlace_lift_of_forall_hasValue 𝔓 hread hreadFin (DiaChart.precomp ρ σ) _ fun b => ?_

  have hσb : bhat (σ b) = (diamondAutHBar M H d).symm (bhat b) := Subtype.ext (hσ b)

  have h1 := hread ρ (σ b)
  have h2 := hasValue_ofAlgAut_smul (diamondAutHBar M H d) _ h1
  rw [hσb, AlgEquiv.apply_symm_apply] at h2
  exact h2

end DiaChart
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_iotaInf_comp_dia_hom_eq_spec_map_comp_iotaInf.DiaChart"

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_iotaInf_comp_dia_hom_eq_spec_map_comp_iotaInf.DiaChart"

universe u

namespace FinRead

section Value

variable {R : CommRingCat.{u}} [IsLocalRing R] {X Y : Scheme.{u}}

theorem stalkClosedPointTo_germ_appIso_inv (ι : Y ⟶ X) [IsOpenImmersion ι] (l : Spec R ⟶ Y)
    (w : Γ(Y, ⊤)) (h : (l ≫ ι).base (IsLocalRing.closedPoint R) ∈ ι ''ᵁ ⊤) :
    Scheme.stalkClosedPointTo (l ≫ ι) (X.presheaf.germ (ι ''ᵁ ⊤) _ h ((ι.appIso ⊤).inv w)) =
      Scheme.stalkClosedPointTo l (Y.presheaf.germ ⊤ _ trivial w) := by
  rw [Scheme.stalkClosedPointTo_comp]
  show Scheme.stalkClosedPointTo l (ι.stalkMap (l.base (IsLocalRing.closedPoint R))
    (X.presheaf.germ (ι ''ᵁ ⊤) (ι.base (l.base (IsLocalRing.closedPoint R))) h ((ι.appIso ⊤).inv w))) = _
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply, TopCat.Presheaf.germ_res_apply]

theorem stalkClosedPointTo_SpecMap_germ {A : CommRingCat.{u}} (φ : A ⟶ R) (b : A) :
    Scheme.stalkClosedPointTo (Spec.map φ) ((Spec A).presheaf.germ ⊤ _ trivial ((Scheme.ΓSpecIso A).inv b)) =
      φ b := by
  rw [← CommRingCat.comp_apply, Scheme.germ_stalkClosedPointTo_Spec, CommRingCat.comp_apply,
    Iso.inv_hom_id_apply]

theorem stalkClosedPointTo_congr {g g' : Spec R ⟶ X} (hg : g = g') (U : X.Opens)
    (h : g.base (IsLocalRing.closedPoint R) ∈ U) (h' : g'.base (IsLocalRing.closedPoint R) ∈ U) (s : Γ(X, U)) :
    Scheme.stalkClosedPointTo g (X.presheaf.germ U _ h s) = Scheme.stalkClosedPointTo g' (X.presheaf.germ U _ h' s) := by
  subst hg; rfl

theorem stalkClosedPointTo_germ_app (y : Spec R ⟶ Y) (f : Y ⟶ X) (U : X.Opens)
    (h : (y ≫ f).base (IsLocalRing.closedPoint R) ∈ U) :
    ∀ s : Γ(X, U), Scheme.stalkClosedPointTo y (Y.presheaf.germ (f ⁻¹ᵁ U) (y.base (IsLocalRing.closedPoint R)) h (f.app U s)) =
      Scheme.stalkClosedPointTo (y ≫ f) (X.presheaf.germ U _ h s) := by
  intro s
  rw [Scheme.stalkClosedPointTo_comp]
  show _ = Scheme.stalkClosedPointTo y (f.stalkMap (y.base (IsLocalRing.closedPoint R))
    (X.presheaf.germ U (f.base (y.base (IsLocalRing.closedPoint R))) h s))
  rw [Scheme.Hom.germ_stalkMap_apply]

end Value
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_iotaInf_comp_dia_hom_eq_spec_map_comp_iotaInf.DiaChart"

theorem algebraMap_germ_eq_germToFunctionField {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) (x : X) (hx : x ∈ U)
    (s : Γ(X, U)) :
    haveI : Nonempty U := ⟨⟨x, hx⟩⟩
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx s) = X.germToFunctionField U s := by
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  show (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom (X.presheaf.germ U x hx s) = _
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]

end FinRead
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_iotaInf_comp_dia_hom_eq_spec_map_comp_iotaInf.DiaChart"

namespace ModularCurve p2m_export "ModularCurve" "XHDRModelAtP xHFunctionFieldBar qExpFunctionFieldC coeffEmb coeffEmb_mem_laurentBaseChange jqModC diamondAutHBar XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb" namespace XHDRModelAtP p2m_export "ModularCurve.XHDRModelAtP" "eeta Meta_chart_nonempty w Meta dia_generic dia_over lfp dia Meta_pin heeta isProper eeta_iso flat comp w_sq coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb" end ModularCurve.XHDRModelAtP
p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in
open FinRead in

theorem ModularCurve.XHDRModelAtP.hasValue_pointEquivPlace_coeffEmb_of_comp_eq_ιInf_of_pin
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (𝔓 : XHDRModelAtP p M H hpM hj)
    [hne : Nonempty (Scheme.Opens.toScheme ((𝔓.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)))]
    (hpin : ∀ b : ↥(chartAlgInf p (ΓM M H) hj),
      ((𝔓.Meta.ffEquiv.symm
          (𝔓.Meta.C.germToFunctionField
            ((𝔓.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
              ((ιInf p (ΓM M H) hj) ''ᵁ ⊤))
            (((𝔓.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app
                ((ιInf p (ΓM M H) hj) ''ᵁ ⊤)).hom
              (((ιInf p (ΓM M H) hj).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv b))))
          : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ))
    (Q : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _})
    (χ : ↥(chartAlgInf p (ΓM M H) hj) →+* AlgebraicClosure ℚ)
    (hQ : Q.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) =
      Spec.map (CommRingCat.ofHom χ) ≫ ιInf p (ΓM M H) hj)
    (b : ↥(chartAlgInf p (ΓM M H) hj)) :
    (𝔓.Meta.pointEquivPlace Q).HasValue
      ⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ (χ b) := by

  set f := 𝔓.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
    (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) with hf
  set U : (X p (ΓM M H) hj).Opens := (ιInf p (ΓM M H) hj) ''ᵁ ⊤ with hU
  set sec : Γ(X p (ΓM M H) hj, U) :=
    ((ιInf p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓM M H) hj))).inv b)
    with hsec
  have hQf : Q.1 ≫ f = Spec.map (CommRingCat.ofHom χ) ≫ ιInf p (ΓM M H) hj := by rw [hf]; exact hQ
  have hmemU : (Q.1 ≫ f).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ U := by
    rw [hQf]
    exact ⟨(Spec.map (CommRingCat.ofHom χ)).base (IsLocalRing.closedPoint _), trivial, rfl⟩
  have hmemU' : (Spec.map (CommRingCat.ofHom χ) ≫ ιInf p (ΓM M H) hj).base
      (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ U := hQf ▸ hmemU
  set s := 𝔓.Meta.C.presheaf.germ (f ⁻¹ᵁ U) (Q.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hmemU
    (f.app U sec) with hs
  obtain ⟨hmem, hres, -⟩ :=
    AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo 𝔓.Meta Q s
  have helt : 𝔓.Meta.ffEquiv.symm (algebraMap _ 𝔓.Meta.C.functionField s) =
      ⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ := by
    apply Subtype.ext
    rw [hs, algebraMap_germ_eq_germToFunctionField]
    exact hpin b
  have hval : (Scheme.stalkClosedPointTo Q.1).hom s = χ b := by
    show Scheme.stalkClosedPointTo Q.1 s = χ b
    rw [hs, stalkClosedPointTo_germ_app Q.1 f U hmemU sec, stalkClosedPointTo_congr hQf U hmemU hmemU' sec, hsec,
      stalkClosedPointTo_germ_appIso_inv, stalkClosedPointTo_SpecMap_germ]
    rfl
  have H' : ∃ h : 𝔓.Meta.ffEquiv.symm (algebraMap _ 𝔓.Meta.C.functionField s) ∈
      (𝔓.Meta.pointEquivPlace Q).toValuationSubring,
      IsLocalRing.residue (𝔓.Meta.pointEquivPlace Q).toValuationSubring ⟨_, h⟩ =
        algebraMap (AlgebraicClosure ℚ) (𝔓.Meta.pointEquivPlace Q).ResidueField (χ b) :=
    ⟨hmem, by rw [hres, hval]⟩
  rw [helt] at H'
  exact H'

p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in

theorem ModularCurve.XHDRModelAtP.hasValue_pointEquivPlace_coeffEmb_of_comp_eq_ιInf
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (Q : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _})
    (χ : ↥(chartAlgInf p (ΓM M H) hj) →+* AlgebraicClosure ℚ)
    (hQ : Q.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) =
      Spec.map (CommRingCat.ofHom χ) ≫ ιInf p (ΓM M H) hj)
    (b : ↥(chartAlgInf p (ΓM M H) hj)) :
    (𝔓.Meta.pointEquivPlace Q).HasValue
      ⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ (χ b) := by
  obtain ⟨hne, _⟩ := ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb
    p M H hpM hj 𝔓 b
  haveI := hne
  refine ModularCurve.XHDRModelAtP.hasValue_pointEquivPlace_coeffEmb_of_comp_eq_ιInf_of_pin 𝔓 (fun b' => ?_) Q χ hQ b
  obtain ⟨_, h⟩ := ModularCurve.XHDRModelAtP.coe_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_coeffEmb
    p M H hpM hj 𝔓 b'
  exact h

p2m_open_scoped "ModularCurve ModularCurve.XHDRModelAtP" in
open FinRead in

theorem ModularCurve.XHDRModelAtP.hasValue_pointEquivPlace_coeffEmb_of_comp_eq_ιFin
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (Q : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _})
    (r' : ↥(chartAlgFin p (ΓM M H) hj) →+* AlgebraicClosure ℚ)
    (hQ : Q.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) =
      Spec.map (CommRingCat.ofHom r') ≫ ιFin p (ΓM M H) hj)
    (a : ↥(chartAlgFin p (ΓM M H) hj)) :
    (𝔓.Meta.pointEquivPlace Q).HasValue
      ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ (r' a) := by
  haveI := 𝔓.Meta_chart_nonempty

  set f := 𝔓.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
    (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) with hf
  set U : (X p (ΓM M H) hj).Opens := (ιFin p (ΓM M H) hj) ''ᵁ ⊤ with hU
  set sec : Γ(X p (ΓM M H) hj, U) :=
    ((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv a)
    with hsec

  have hQf : Q.1 ≫ f = Spec.map (CommRingCat.ofHom r') ≫ ιFin p (ΓM M H) hj := by rw [hf]; exact hQ
  have hmemU : (Q.1 ≫ f).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ U := by
    rw [hQf]
    exact ⟨(Spec.map (CommRingCat.ofHom r')).base (IsLocalRing.closedPoint _), trivial, rfl⟩
  have hmemU' : (Spec.map (CommRingCat.ofHom r') ≫ ιFin p (ΓM M H) hj).base
      (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) ∈ U := hQf ▸ hmemU

  set s := 𝔓.Meta.C.presheaf.germ (f ⁻¹ᵁ U) (Q.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hmemU
    (f.app U sec) with hs
  obtain ⟨hmem, hres, -⟩ :=
    AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo 𝔓.Meta Q s

  have helt : 𝔓.Meta.ffEquiv.symm (algebraMap _ 𝔓.Meta.C.functionField s) =
      ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩ := by
    apply Subtype.ext
    rw [hs, algebraMap_germ_eq_germToFunctionField]
    exact 𝔓.Meta_pin a

  have hval : (Scheme.stalkClosedPointTo Q.1).hom s = r' a := by
    show Scheme.stalkClosedPointTo Q.1 s = r' a
    rw [hs, stalkClosedPointTo_germ_app Q.1 f U hmemU sec, stalkClosedPointTo_congr hQf U hmemU hmemU' sec, hsec,
      stalkClosedPointTo_germ_appIso_inv, stalkClosedPointTo_SpecMap_germ]
    rfl
  have H' : ∃ h : 𝔓.Meta.ffEquiv.symm (algebraMap _ 𝔓.Meta.C.functionField s) ∈
      (𝔓.Meta.pointEquivPlace Q).toValuationSubring,
      IsLocalRing.residue (𝔓.Meta.pointEquivPlace Q).toValuationSubring ⟨_, h⟩ =
        algebraMap (AlgebraicClosure ℚ) (𝔓.Meta.pointEquivPlace Q).ResidueField (r' a) :=
    ⟨hmem, by rw [hres, hval]⟩
  rw [helt] at H'
  exact H'

theorem solution
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (𝔓 : XHDRModelAtP p M H hpM hj) (d : (ZMod M)ˣ)
    (σ : ↥(chartAlgInf p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj))
    (hσ : ∀ b : ↥(chartAlgInf p (ΓM M H) hj),
      coeffEmb (AlgebraicClosure ℚ) (((σ b : ↥(chartAlgInf p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        (((diamondAutHBar M H d).symm
            ⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(qExpFunctionFieldC ℚ (ΓM M H))).2⟩
          : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))) :
    ιInf p (ΓM M H) hj ≫ (𝔓.dia d).hom =
      Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫ ιInf p (ΓM M H) hj := by
  haveI := 𝔓.isProper
  haveI : IsFractionRing (R p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  haveI := 𝔓.flat
  haveI := 𝔓.lfp

  have hf : ιInf p (ΓM M H) hj ≫ toBase p (ΓM M H) hj =
      Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥(chartAlgInf p (ΓM M H) hj))) :=
    TwoChartIntegralModel.ιInf_toBase _ _ _
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥(chartAlgInf p (ΓM M H) hj)))) := by
    rw [← hf]; infer_instance
  haveI : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥(chartAlgInf p (ΓM M H) hj)))) := by
    rw [← hf]; infer_instance
  refine AlgebraicGeometry.eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated
    (R := R p) ℚ (AlgebraicClosure ℚ)
    (Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥(chartAlgInf p (ΓM M H) hj))))
    (toBase p (ΓM M H) hj) _ _ ?_ ?_ ?_
  · rw [Category.assoc, 𝔓.dia_over d, hf]
  · rw [Category.assoc, hf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun r => σ.commutes r
  · intro x hx

    have hread : ∀ (χ : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] AlgebraicClosure ℚ) (b : ↥(chartAlgInf p (ΓM M H) hj)),
        (𝔓.Meta.pointEquivPlace (DiaChart.lift 𝔓 χ)).HasValue (DiaChart.bhat b) (χ b) := fun χ b =>
      ModularCurve.XHDRModelAtP.hasValue_pointEquivPlace_coeffEmb_of_comp_eq_ιInf 𝔓 (DiaChart.lift 𝔓 χ) χ.toRingHom
        (by rw [← Category.assoc, DiaChart.lift_eeta, DiaChart.liftBar_fst]) b
    have hreadFin : ∀ (Q : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _})
        (r' : ↥(chartAlgFin p (ΓM M H) hj) →+* AlgebraicClosure ℚ),
        Q.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom r') ≫ ιFin p (ΓM M H) hj →
        (𝔓.Meta.pointEquivPlace Q).HasValue
          (DiaChart.ahat (TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)))
          (r' (TwoChartIntegralModel.jChartFin (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))) :=
      fun Q r' h => ModularCurve.XHDRModelAtP.hasValue_pointEquivPlace_coeffEmb_of_comp_eq_ιFin 𝔓 Q r' h _
    have hRHS : ∀ ρ : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] AlgebraicClosure ℚ,
        𝔓.Meta.pointEquivPlace (DiaChart.lift 𝔓 (DiaChart.precomp ρ σ)) =
          SemilinearAut.ofAlgAut (diamondAutHBar M H d) • 𝔓.Meta.pointEquivPlace (DiaChart.lift 𝔓 ρ) :=
      fun ρ => DiaChart.pointEquivPlace_lift_precomp 𝔓 d hread hreadFin σ hσ ρ

    obtain ⟨ρ, hxρ⟩ : ∃ ρ : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] AlgebraicClosure ℚ,
        x = Spec.map (CommRingCat.ofHom ρ.toRingHom) := by
      have hxf : Spec.map (Spec.preimage x) = x := Spec.map_preimage x
      have hcomm : (Spec.preimage x).hom.comp (algebraMap (R p) ↥(chartAlgInf p (ΓM M H) hj)) =
          algebraMap (R p) (AlgebraicClosure ℚ) := by
        have h1 : Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥(chartAlgInf p (ΓM M H) hj)) ≫ Spec.preimage x) =
            Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
          rw [Spec.map_comp, hxf]; exact hx
        exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
      refine ⟨{ (Spec.preimage x).hom with commutes' := fun r => ?_ }, ?_⟩
      · exact congrArg (fun g => g r) hcomm
      · calc x = Spec.map (Spec.preimage x) := hxf.symm
          _ = _ := rfl
    subst hxρ

    have hpl : 𝔓.Meta.pointEquivPlace (DiaChart.lift 𝔓 (DiaChart.precomp ρ σ)) =
        𝔓.Meta.pointEquivPlace (DiaChart.translate 𝔓 d (DiaChart.lift 𝔓 ρ)) := by
      rw [hRHS ρ, DiaChart.pointEquivPlace_translate]
    have hsec : DiaChart.lift 𝔓 (DiaChart.precomp ρ σ) = DiaChart.translate 𝔓 d (DiaChart.lift 𝔓 ρ) :=
      𝔓.Meta.pointEquivPlace.injective hpl
    have hbar : DiaChart.liftBar (DiaChart.precomp ρ σ) = DiaChart.liftBar ρ ≫ DiaChart.diaBar 𝔓 d := by
      rw [← DiaChart.lift_eeta 𝔓, hsec, DiaChart.translate_lift_eeta]
    have hfst := congrArg (fun g => g ≫ pullback.fst _ _) hbar
    simp only [Category.assoc, DiaChart.liftBar_fst, DiaChart.diaBar_fst, DiaChart.liftBar_fst_assoc] at hfst

    have hsplit : Spec.map (CommRingCat.ofHom (DiaChart.precomp ρ σ).toRingHom) =
        Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
    rw [← hfst, hsplit, Category.assoc]

end S_ModularCurve_XHDRModelAtP_iotaInf_comp_dia_hom_eq_spec_map_comp_iotaInf
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_iotaInf_comp_dia_hom_eq_spec_map_comp_iotaInf (solution)
