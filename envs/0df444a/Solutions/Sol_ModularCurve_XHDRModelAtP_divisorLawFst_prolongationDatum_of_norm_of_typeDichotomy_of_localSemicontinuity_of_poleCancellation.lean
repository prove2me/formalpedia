-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.divisorLawFst_prolongationDatum_of_norm_of_typeDichotomy_of_localSemicontinuity_of_poleCancellation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ae82dab6-247f-57a5-afbe-cfe3e64d259e

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardNormFormula_of_finiteDimensional
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_divisorLawFst_prolongationDatum_of_norm_of_typeDichotomy_of_localSemicontinuity_of_poleCancellation
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_divisorLawFst_prolongationDatum_of_norm_of_typeDichotomy_of_localSemicontinuity_of_poleCancellation.ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP"

open scoped MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "XHDRModelAtP diamondActionModL infSubgroup translation_mem_GammaH xHFunctionField xHFunctionFieldBar qExpFunctionFieldC qExpFunctionFieldC_mono jq coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange qExpFrobeniusPlaceModL jqModC JHNeronObjectAtP.ΓN JHNeronObjectAtP.Fbar JHNeronObjectAtP JZeroNeronObjectAtP JHPlaceSpecialization.Fixed JHPlaceSpecialization JHPlaceSpecialization.fstDiv JHPlaceSpecialization.sndDiv JHPlaceSpecialization.ProlongationDatum qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul JOneES.exists_transcendental_finiteDimensional_laurentBaseChange finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange qExpFrobeniusPlaceModL_bijective qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul"
namespace DivisorLawFstEngine
p2m_open "ModularCurve"

section FinsuppSums

variable {ι τ : Type*}

open Classical in
theorem mapDomain_apply_eq_sum (r : ι → τ) (D : ι →₀ ℤ) (b : τ) :
    Finsupp.mapDomain r D b = ∑ a ∈ D.support, if r a = b then D a else 0 := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.single_apply]

open Classical in
theorem mapDomain_filter_apply_eq_sum (r : ι → τ) (P : ι → Prop) (D : ι →₀ ℤ) (b : τ) :
    Finsupp.mapDomain r (D.filter P) b = ∑ a ∈ D.support, if P a ∧ r a = b then D a else 0 := by
  rw [mapDomain_apply_eq_sum, Finsupp.support_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.filter_apply]
  by_cases hP : P a <;> by_cases hr : r a = b <;> simp [hP, hr]

end FinsuppSums

theorem qExpFrobeniusPlaceModL_injective (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]
    [PerfectField K] (Γ : Subgroup SL(2, ℤ)) :
    Function.Injective (qExpFrobeniusPlaceModL K Γ p) := by
  intro v w h
  rw [qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul, qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul] at h
  exact MulAction.injective _ h

section NormFormula

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem inertiaDegAlong_eq_one_of_deg_eq_one (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (W : Place K F') (hW : W.deg = 1) : W.inertiaDegAlong φ hφ = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  have h := W.deg_restrict_mul_inertiaDeg (F := F)
  rw [hW] at h
  exact Nat.eq_one_of_mul_eq_one_left h

theorem mapDomain_restrictAlong_eq_pushforwardAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hdeg : ∀ W : Place K F', W.deg = 1) (D : Divisor K F') :
    Finsupp.mapDomain (Place.restrictAlong φ hφ) D = Divisor.pushforwardAlong φ hφ D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D₁ D₂ h₁ h₂ => rw [Finsupp.mapDomain_add, map_add, h₁, h₂]
  | single W n =>
    rw [Finsupp.mapDomain_single, Divisor.pushforwardAlong_single,
      inertiaDegAlong_eq_one_of_deg_eq_one φ hφ W (hdeg W), Nat.cast_one, mul_one]

theorem mapDomain_restrictAlong_apply_eq_ord_norm (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    [CharZero F] (hfin : FiniteAlong K φ) (hdeg : ∀ W : Place K F', W.deg = 1)
    (f : F') (hf : f ≠ 0) (D : Divisor K F') (hD : ∀ W, D W = W.ord f) (V : Place K F) :
    Finsupp.mapDomain (Place.restrictAlong φ hφ) D V = V.ord (letI := algebraAlong φ; Algebra.norm F f) := by
  rw [mapDomain_restrictAlong_eq_pushforwardAlong φ hφ hdeg]
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : Module.Finite F F' := hfin
  haveI : Algebra.IsSeparable F F' := inferInstance
  have hN : Divisor.PushforwardNormFormula K F F' := Divisor.pushforwardNormFormula_of_finiteDimensional
  exact hN f hf D hD V

end NormFormula

section LevelFields

theorem deg_eq_one_laurentBaseChange (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (W : Place (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) :
    W.deg = 1 := by
  obtain ⟨x, hx, hfd⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ) Γ hT
  haveI := hfd
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) :=
    AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx
  haveI := IsCurveOver.finiteResidue (K := AlgebraicClosure ℚ) W
  have hpos : 0 < W.deg := Module.finrank_pos
  exact Place.deg_eq_one_of_isAlgClosed W hpos.ne'

theorem isCurveOver_laurentBaseChange (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) :
    IsCurveOver (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) := by
  obtain ⟨x, hx, hfd⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ) Γ hT
  haveI := hfd
  exact AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx

theorem deg_eq_one_xHFunctionFieldBar (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : W.deg = 1 :=
  deg_eq_one_laurentBaseChange (CohCarrier.GammaH M H) (translation_mem_GammaH M H) W

set_option synthInstance.maxHeartbeats 1600000 in

theorem finiteAlong_of_coe_eq (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (u : LaurentSeries (AlgebraicClosure ℚ))) :
    FiniteAlong (AlgebraicClosure ℚ) α := by
  have hjM : jq ∈ xHFunctionField M H := qExpFunctionFieldC_mono ℚ le_top hj
  have hjMp : jq ∈ xHFunctionField (M / p) (infSubgroup p M H hpM) := qExpFunctionFieldC_mono ℚ le_top hj
  let jM : ↥(xHFunctionFieldBar M H) :=
    ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hjM⟩
  let jMp : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hjMp⟩
  have hαj : α jMp = jM := Subtype.ext (by rw [hα_coe])
  have hfd : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jM} : Set ↥(xHFunctionFieldBar M H)))
      ↥(xHFunctionFieldBar M H) :=
    finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange (CohCarrier.GammaH M H)
      (translation_mem_GammaH M H) (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) rfl jM rfl

  have hle : IntermediateField.adjoin (AlgebraicClosure ℚ) ({jM} : Set ↥(xHFunctionFieldBar M H)) ≤ α.fieldRange := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact (AlgHom.mem_fieldRange (f := α)).mpr ⟨jMp, hαj⟩
  letI : Algebra ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) := algebraAlong α
  letI : Module ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) := Algebra.toModule
  show Module.Finite ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H)
  obtain ⟨S, hS⟩ := hfd.fg_top
  refine Module.finite_def.mpr ⟨S, ?_⟩
  rw [eq_top_iff]
  rintro x -
  have hx : x ∈ Submodule.span
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jM} : Set ↥(xHFunctionFieldBar M H)))
      (S : Set ↥(xHFunctionFieldBar M H)) := by
    rw [hS]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul c y _ hy =>
    obtain ⟨c', hc'⟩ := (AlgHom.mem_fieldRange (f := α)).mp (hle c.2)
    have h1 : c • y = (c : ↥(xHFunctionFieldBar M H)) * y := rfl
    have h2 : c' • y = α c' * y := Algebra.smul_def c' y
    rw [h1, ← hc', ← h2]
    exact Submodule.smul_mem _ c' hy

end LevelFields

section Main

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
variable (A : ValuationSubring (AlgebraicClosure ℚ))
variable [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

set_option quotPrecheck false
local notation "κ" => ResidueField ↥A
local notation "FM" => ↥(xHFunctionFieldBar M H)
local notation "FMp" => ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))
local notation "Fb" => JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)
local notation "Γ′" => ModularCurve.JHNeronObjectAtP.ΓN p M H hpM
local notation "φ" => qExpFrobeniusPlaceModL (ResidueField ↥A) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM) p

theorem mapDomain_reduceFst_eq_ord_add_ord
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (θ : FM ≃ₐ[AlgebraicClosure ℚ] FM)
    (α : FMp →ₐ[AlgebraicClosure ℚ] FM)
    (hα_coe : ∀ u, ((α u : FM) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hN : ∀ (f : FM) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
        Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
        letI := algebraAlong α
        ∃ g : Fb, g ≠ 0 ∧
          (∀ D : Divisor (AlgebraicClosure ℚ) FMp,
            (∀ V, D V = V.ord (Algebra.norm FMp f)) →
            ∀ v', Finsupp.mapDomain Psp.sp D v' = v'.ord g) ∧
          ∀ u : Place κ Fb, (φ u).ord g = (φ u).ord (Rpd.R₁.residue ⟨f, h₁⟩) + u.ord (Rpd.R₂.residue ⟨f, h₂⟩))
    (u : Place κ Fb) (g : FM) (hg₁ : g ∈ Rpd.R₁.integers) (hg₂ : g ∈ Rpd.R₂.integers)
    (hrg₁ : Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0) (hrg₂ : Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0)
    (E : Divisor (AlgebraicClosure ℚ) FM) (hE : ∀ W, E W = W.ord g) :
    Finsupp.mapDomain (Psp.reduceFst α hα) E (φ u) =
      (φ u).ord (Rpd.R₁.residue ⟨g, hg₁⟩) + u.ord (Rpd.R₂.residue ⟨g, hg₂⟩) := by
  have hg0 : g ≠ 0 := by
    intro hz
    apply hrg₁
    have h0 : (⟨g, hg₁⟩ : ↥Rpd.R₁.integers) = 0 := Subtype.ext hz
    rw [h0, map_zero]
  obtain ⟨gb, -, hgD, hgφ⟩ := hN g hg₁ hg₂ hrg₁ hrg₂
  have hE' : ∀ V, Finsupp.mapDomain (Place.restrictAlong α hα) E V =
      V.ord (letI := algebraAlong α; Algebra.norm FMp g) := fun V =>
    mapDomain_restrictAlong_apply_eq_ord_norm α hα (finiteAlong_of_coe_eq p M H hpM hj α hα_coe)
      (deg_eq_one_xHFunctionFieldBar M H) g hg0 E hE V
  have hcomp : Psp.reduceFst α hα = Psp.sp ∘ Place.restrictAlong α hα := rfl
  rw [hcomp, Finsupp.mapDomain_comp, hgD _ hE' _]
  exact hgφ u

theorem mapDomain_reduceFst_eq_fstMass_add_sndMass
    (δ : Place κ Fb → Place κ Fb)
    (θ : FM ≃ₐ[AlgebraicClosure ℚ] FM)
    (α : FMp →ₐ[AlgebraicClosure ℚ] FM)
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A)
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hφinj : Function.Injective φ)
    (u : Place κ Fb)
    (hu : ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ u)
    (hv : ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (φ u))
    (E : Divisor (AlgebraicClosure ℚ) FM) :
    Finsupp.mapDomain (Psp.reduceFst α hα) E (φ u) =
      Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ E) (φ u) +
        Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ)
          (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ E) u := by
  classical
  have hdisj : ∀ W, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W →
      Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → False := by
    intro W hF hS
    apply hF.2
    unfold JHPlaceSpecialization.Fixed
    rw [hF.1, ← hS.1]
  unfold JHPlaceSpecialization.fstDiv JHPlaceSpecialization.sndDiv
  rw [mapDomain_apply_eq_sum, mapDomain_filter_apply_eq_sum, mapDomain_filter_apply_eq_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun W _ => ?_
  rcases hTD W with hA | hB
  ·
    by_cases hr : Psp.reduceFst α hα W = φ u
    · have hr2 : Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = u := hφinj (hA.symm.trans hr)
      have hSS : Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W := ⟨hA, hr2.symm ▸ hu⟩
      have hnSF : ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W := fun hSF => hdisj W hSF hSS
      simp [hr, hr2, hSS, hnSF]
    · have hr2 : ¬ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = u := fun h => hr (by rw [hA, h])
      simp [hr, hr2]
  ·
    by_cases hr : Psp.reduceFst α hα W = φ u
    · have hSF : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W := ⟨hB, hr.symm ▸ hv⟩
      have hnSS : ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W := fun hSS => hdisj W hSF hSS
      simp [hr, hSF, hnSS]
    · have hn : ¬ (Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W ∧
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = u) := fun ⟨hS, h⟩ => hr (by rw [hS.1, h])
      simp [hr, hn]

set_option maxHeartbeats 1600000 in

theorem divisorLawFst_of_norm_of_typeDichotomy_of_localSemicontinuity_of_poleCancellation
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (δ : Place κ Fb → Place κ Fb)
    (θ : FM ≃ₐ[AlgebraicClosure ℚ] FM)
    (α : FMp →ₐ[AlgebraicClosure ℚ] FM)
    (hα_coe : ∀ u, ((α u : FM) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hN : ∀ (f : FM) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
        Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
        letI := algebraAlong α
        ∃ g : Fb, g ≠ 0 ∧
          (∀ D : Divisor (AlgebraicClosure ℚ) FMp,
            (∀ V, D V = V.ord (Algebra.norm FMp f)) →
            ∀ v', Finsupp.mapDomain Psp.sp D v' = v'.ord g) ∧
          ∀ u : Place κ Fb, (φ u).ord g = (φ u).ord (Rpd.R₁.residue ⟨f, h₁⟩) + u.ord (Rpd.R₂.residue ⟨f, h₂⟩))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hL : ((∀ (f : FM) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) FM, (∀ W, D W = W.ord f) →
        ∀ v : Place κ Fb, ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          (∀ W, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = v → 0 ≤ D W) →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D) v ≤ v.ord (Rpd.R₁.residue ⟨f, h₁⟩)) ∧
     (∀ (f : FM) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) FM, (∀ W, D W = W.ord f) →
        ∀ u : Place κ Fb, ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ u →
          (∀ W, Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = u → 0 ≤ D W) →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D) u ≤
            u.ord (Rpd.R₂.residue ⟨f, h₂⟩))))
    (hpc : (∀ (f : FM) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ u : Place κ Fb,
        ∃ (h : FM) (hh₁ : h ∈ Rpd.R₁.integers) (hh₂ : h ∈ Rpd.R₂.integers),
          Rpd.R₁.residue ⟨h, hh₁⟩ ≠ 0 ∧ Rpd.R₂.residue ⟨h, hh₂⟩ ≠ 0 ∧
          (∀ W, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = φ u → 0 ≤ W.ord h) ∧
          (∀ W, Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = u → 0 ≤ W.ord h) ∧
          (∀ W, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = φ u → 0 ≤ W.ord (f * h)) ∧
          (∀ W, Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = u → 0 ≤ W.ord (f * h))))
    (hcomm : ∀ v, δ (φ v) = φ (δ v)) :
    Rpd.DivisorLawFst α (θ.toAlgHom.comp α) hα hβ δ := by
  classical
  intro f h₁ h₂ hres₁ hres₂ D hD v hv

  have hφinj : Function.Injective φ := qExpFrobeniusPlaceModL_injective p κ Γ′
  have hφsurj : Function.Surjective φ := (qExpFrobeniusPlaceModL_bijective κ p Γ′).2
  obtain ⟨u, rfl⟩ := hφsurj v

  have hu : ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ u := by
    intro hfix
    apply hv
    unfold JHPlaceSpecialization.Fixed at hfix ⊢
    rw [hcomm (φ u), hfix]

  haveI : IsCurveOver (AlgebraicClosure ℚ) FM :=
    isCurveOver_laurentBaseChange (CohCarrier.GammaH M H) (translation_mem_GammaH M H)

  have hall := mapDomain_reduceFst_eq_ord_add_ord p M H hpM A hj θ α hα_coe hα Psp Rpd hN u
  have hpart := mapDomain_reduceFst_eq_fstMass_add_sndMass p M H hpM A δ θ α hα hβ Psp hTD hφinj u hu hv

  have hpf : ∀ (g : FM) (hg₁ : g ∈ Rpd.R₁.integers) (hg₂ : g ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 → Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) FM, (∀ W, E W = W.ord g) →
        (∀ W, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = φ u → 0 ≤ E W) →
        (∀ W, Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = u → 0 ≤ E W) →
        Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ E) (φ u) =
          (φ u).ord (Rpd.R₁.residue ⟨g, hg₁⟩) := by
    intro g hg₁ hg₂ hrg₁ hrg₂ E hE hp₁ hp₂
    have ha := hall g hg₁ hg₂ hrg₁ hrg₂ E hE
    have hb := hpart E
    have hl₁ := hL.1 g hg₁ hg₂ hrg₁ hrg₂ E hE (φ u) hv hp₁
    have hl₂ := hL.2 g hg₁ hg₂ hrg₁ hrg₂ E hE u hu hp₂
    omega

  obtain ⟨h, hh₁, hh₂, hs₁, hs₂, hph₁, hph₂, hpfh₁, hpfh₂⟩ := hpc f h₁ h₂ hres₁ hres₂ u
  have hf0 : f ≠ 0 := by
    intro hz
    apply hres₁
    have h0 : (⟨f, h₁⟩ : ↥Rpd.R₁.integers) = 0 := Subtype.ext hz
    rw [h0, map_zero]
  have hh0 : h ≠ 0 := by
    intro hz
    apply hs₁
    have h0 : (⟨h, hh₁⟩ : ↥Rpd.R₁.integers) = 0 := Subtype.ext hz
    rw [h0, map_zero]
  obtain ⟨E, hE, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) h hh0
  have hDE : ∀ W, (D + E) W = W.ord (f * h) := by
    intro W
    rw [Finsupp.add_apply, hD W, hE W, W.ord_mul hf0 hh0]
  have hfh₁ : f * h ∈ Rpd.R₁.integers := mul_mem h₁ hh₁
  have hfh₂ : f * h ∈ Rpd.R₂.integers := mul_mem h₂ hh₂
  have hmul₁ : (⟨f * h, hfh₁⟩ : ↥Rpd.R₁.integers) = ⟨f, h₁⟩ * ⟨h, hh₁⟩ := rfl
  have hmul₂ : (⟨f * h, hfh₂⟩ : ↥Rpd.R₂.integers) = ⟨f, h₂⟩ * ⟨h, hh₂⟩ := rfl
  have hrfh₁ : Rpd.R₁.residue ⟨f * h, hfh₁⟩ ≠ 0 := by
    rw [hmul₁, map_mul]; exact mul_ne_zero hres₁ hs₁
  have hrfh₂ : Rpd.R₂.residue ⟨f * h, hfh₂⟩ ≠ 0 := by
    rw [hmul₂, map_mul]; exact mul_ne_zero hres₂ hs₂

  have hA := hpf (f * h) hfh₁ hfh₂ hrfh₁ hrfh₂ (D + E) hDE
    (fun W hW hWu => by rw [hDE W]; exact hpfh₁ W hW hWu)
    (fun W hW hWu => by rw [hDE W]; exact hpfh₂ W hW hWu)
  have hB := hpf h hh₁ hh₂ hs₁ hs₂ E hE
    (fun W hW hWu => by rw [hE W]; exact hph₁ W hW hWu)
    (fun W hW hWu => by rw [hE W]; exact hph₂ W hW hWu)

  have hadd : Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ (D + E)) (φ u) =
      Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D) (φ u) +
        Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ E) (φ u) := by
    unfold JHPlaceSpecialization.fstDiv
    rw [Finsupp.filter_add, Finsupp.mapDomain_add, Finsupp.add_apply]
  have hres : Rpd.R₁.residue ⟨f * h, hfh₁⟩ = Rpd.R₁.residue ⟨f, h₁⟩ * Rpd.R₁.residue ⟨h, hh₁⟩ := by
    rw [hmul₁, map_mul]
  rw [hadd, hB, hres, (φ u).ord_mul hres₁ hs₁] at hA
  omega

end Main

end ModularCurve.DivisorLawFstEngine

end

open ModularCurve.DivisorLawFstEngine in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hN : ∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
        Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
        letI := algebraAlong α
        ∃ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), g ≠ 0 ∧
          (∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
            (∀ V, D V = V.ord (Algebra.norm ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) f)) →
            ∀ v', Finsupp.mapDomain Psp.sp D v' = v'.ord g) ∧
          ∀ u : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
            (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u).ord g =
              (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u).ord (Rpd.R₁.residue ⟨f, h₁⟩) +
                u.ord (Rpd.R₂.residue ⟨f, h₂⟩))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hL : ((∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, D W = W.ord f) →
        ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          (∀ W, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = v → 0 ≤ D W) →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D) v ≤ v.ord (Rpd.R₁.residue ⟨f, h₁⟩)) ∧
     (∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, D W = W.ord f) →
        ∀ u : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ u →
          (∀ W, Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = u → 0 ≤ D W) →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D) u ≤
            u.ord (Rpd.R₂.residue ⟨f, h₂⟩))))
    (hpc : (∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ u : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
        ∃ (h : ↥(xHFunctionFieldBar M H)) (hh₁ : h ∈ Rpd.R₁.integers) (hh₂ : h ∈ Rpd.R₂.integers),
          Rpd.R₁.residue ⟨h, hh₁⟩ ≠ 0 ∧ Rpd.R₂.residue ⟨h, hh₂⟩ ≠ 0 ∧
          (∀ W, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u → 0 ≤ W.ord h) ∧
          (∀ W, Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = u → 0 ≤ W.ord h) ∧
          (∀ W, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u → 0 ≤ W.ord (f * h)) ∧
          (∀ W, Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = u → 0 ≤ W.ord (f * h)))) :
    Rpd.DivisorLawFst α (θ.toAlgHom.comp α) hα hβ δ := by

  have hpMp : ¬ p ∣ M / p := by
    intro hd
    apply hpM2
    obtain ⟨c, hc⟩ := hd
    refine ⟨c, ?_⟩
    have hM : M = M / p * p := (Nat.div_mul_cancel hpM).symm
    rw [hM, hc]
    ring
  have hcomm : ∀ v, δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v) =
      qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (δ v) := by
    intro v
    rw [hδ, hδ]
    exact (ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpMp
      (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) v).symm
  exact divisorLawFst_of_norm_of_typeDichotomy_of_localSemicontinuity_of_poleCancellation p M H hpM A hj δ θ α
    hα_coe hα hβ Psp Rpd hN hTD hL hpc hcomm

end S_ModularCurve_XHDRModelAtP_divisorLawFst_prolongationDatum_of_norm_of_typeDichotomy_of_localSemicontinuity_of_poleCancellation
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_divisorLawFst_prolongationDatum_of_norm_of_typeDichotomy_of_localSemicontinuity_of_poleCancellation (solution)
