-- Prove2me | solution 1 for ModularCurve.exists_frickeAlgEquiv_triple_x1_xH_galois_smul_and_apply_inclusion_eq_and_forall_apply_degeneracy_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/49851c55-4659-582e-8216-5afd2a5bf765

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_CohCarrier_Fricke
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_heckePic0HBarTranspose_smul_diamondHBar_smul_smul_of_qExpansion_slash_fricke
import Theorems.Thm_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_heckeDiamondInputsAll
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_frickeAlgEquiv_triple_x1_xH_galois_smul_and_apply_inclusion_eq_and_forall_apply_degeneracy_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open ModularCurve AlgebraicCurve IntermediateField HahnSeries CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

local notation "Qbar" => AlgebraicClosure ℚ

namespace FrTriple

section Defs

variable (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (ℓ : ℕ) [NeZero ℓ]

abbrev F0 : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ Γ

abbrev E0 : IntermediateField ℚ (LaurentSeries ℚ) := qExpFunctionFieldC ℚ (Γ ⊓ Gamma0 (M * ℓ))

abbrev FB : IntermediateField Qbar (LaurentSeries Qbar) := laurentBaseChange Qbar (F0 Γ)

abbrev JG : Type _ := Pic0 Qbar (FB Γ)

theorem coeffMap_qExpandG {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

variable {L} in
theorem laurentBaseChange_monoG {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

variable {L} in
theorem qExpand_mem_laurentBaseChangeG {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (n : ℕ)
    [NeZero n] {F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (hF : ∀ y ∈ F₀, qExpand ℚ n y ∈ F₁)
    {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) :
    qExpand L n x ∈ laurentBaseChange L F₁ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero,
          ← algebraMap_laurentSeries_eq_single]
        exact (laurentBaseChange L F₁).algebraMap_mem _
      · rw [coeffEmb, ← coeffMap_qExpandG]
        exact coeffEmb_mem_laurentBaseChange L (hF z hz)
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

def alphaG : laurentBaseChange L (F0 Γ) →ₐ[L] laurentBaseChange L (E0 M Γ ℓ) :=
  IntermediateField.inclusion (laurentBaseChange_monoG (qExpFunctionFieldC_mono ℚ inf_le_left))

def BetaDefG : Prop := ∀ y ∈ F0 Γ, qExpand ℚ ℓ y ∈ E0 M Γ ℓ

def betaRingHomOfG (h : BetaDefG M Γ ℓ) :
    laurentBaseChange L (F0 Γ) →+* laurentBaseChange L (E0 M Γ ℓ) where
  toFun x := ⟨qExpand L ℓ (x : LaurentSeries L), qExpand_mem_laurentBaseChangeG ℓ h x.2⟩
  map_one' := Subtype.ext (map_one (qExpand L ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand L ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand L ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand L ℓ) _ _)

def betaOfG (h : BetaDefG M Γ ℓ) :
    laurentBaseChange L (F0 Γ) →ₐ[L] laurentBaseChange L (E0 M Γ ℓ) :=
  { betaRingHomOfG L M Γ ℓ h with
    commutes' := fun a => Subtype.ext <| by
      show qExpand L ℓ (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

open Classical in

def betaG : laurentBaseChange L (F0 Γ) →ₐ[L] laurentBaseChange L (E0 M Γ ℓ) :=
  if h : BetaDefG M Γ ℓ then betaOfG L M Γ ℓ h else alphaG L M Γ ℓ

def IsDiaG (d : (ZMod M)ˣ) (σ : FB Γ ≃ₐ[Qbar] FB Γ) : Prop :=
  ∀ (k : ℤ) (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) (γ : SL(2, ℤ)), γ ∈ Gamma0 M → ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
      ∃ y : LaurentSeries ℚ, y ∈ F0 Γ ∧
        ((σ ⟨coeffEmb Qbar (intSeriesC ℚ pf / intSeriesC ℚ pg),
              coeffEmb_mem_laurentBaseChange Qbar (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
            FB Γ) : LaurentSeries Qbar) = coeffEmb Qbar y ∧
        coeffMap (algebraMap ℚ ℂ) y *
            HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
          HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ)))

def diaAutG (d : (ZMod M)ˣ) : FB Γ ≃ₐ[Qbar] FB Γ :=
  haveI := Classical.dec (∃ σ : FB Γ ≃ₐ[Qbar] FB Γ, IsDiaG M Γ d σ)
  if h : ∃ σ : FB Γ ≃ₐ[Qbar] FB Γ, IsDiaG M Γ d σ then h.choose else AlgEquiv.refl

def diaG (d : (ZMod M)ˣ) : JG Γ →+ JG Γ :=
  DistribSMul.toAddMonoidHom _ (SemilinearAut.ofAlgAut (diaAutG M Γ d))

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

def SpecG (W : GL (Fin 2) ℝ) (ι : Qbar →+* ℂ) (w : FB Γ → FB Γ) : Prop :=
  ∀ (x : FB Γ) (k : ℤ) (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
    coeffMap ι (x : LaurentSeries Qbar) * HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑g) =
        HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑f) →
      coeffMap ι ((w x : FB Γ) : LaurentSeries Qbar) *
          HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] W)) =
        HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] W))

variable {M Γ}

theorem isDiaG_diaAutG {d : (ZMod M)ˣ} (h : ∃ σ : FB Γ ≃ₐ[Qbar] FB Γ, IsDiaG M Γ d σ) :
    IsDiaG M Γ d (diaAutG M Γ d) := by
  rw [diaAutG, dif_pos h]
  exact h.choose_spec

theorem diaG_apply (d : (ZMod M)ˣ) (x : JG Γ) :
    diaG M Γ d x = SemilinearAut.ofAlgAut (diaAutG M Γ d) • x := rfl

end Defs

section Transport

variable (M : ℕ) [NeZero M]

def frickeGL : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

@[scoped simp]
theorem val_frickeGL : ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

def FrLawsG (Γ : Subgroup SL(2, ℤ)) (w : FB Γ ≃ₐ[Qbar] FB Γ) : Prop :=
  (∀ (ℓ : ℕ) [Fact ℓ.Prime]
      (hα : (alphaG Qbar M Γ ℓ).toRingHom.IsIntegral)
      (hβ : (betaG Qbar M Γ ℓ).toRingHom.IsIntegral)
      [HasPrincipalDivisors Qbar (laurentBaseChange Qbar (E0 M Γ ℓ))]
      (hFIβ : FundamentalIdentityAlong Qbar (betaG Qbar M Γ ℓ) hβ)
      (hfinα : FiniteAlong Qbar (alphaG Qbar M Γ ℓ))
      (hNα : NormFormulaAlong Qbar (alphaG Qbar M Γ ℓ) hfinα)
      (hFIα : FundamentalIdentityAlong Qbar (alphaG Qbar M Γ ℓ) hα)
      (hfinβ : FiniteAlong Qbar (betaG Qbar M Γ ℓ))
      (hNβ : NormFormulaAlong Qbar (betaG Qbar M Γ ℓ) hfinβ)
      (x : JG Γ),
    Pic0.correspondence (alphaG Qbar M Γ ℓ) (betaG Qbar M Γ ℓ) hα hβ hFIα hfinβ hNβ
        (SemilinearAut.ofAlgAut w • x)
      = SemilinearAut.ofAlgAut w •
          Pic0.correspondence (betaG Qbar M Γ ℓ) (alphaG Qbar M Γ ℓ) hβ hα hFIβ hfinα hNα x) ∧
  (∀ (d : (ZMod M)ˣ) (x : JG Γ),
    diaG M Γ d (SemilinearAut.ofAlgAut w • diaG M Γ d x) = SemilinearAut.ofAlgAut w • x) ∧
  (∀ x : JG Γ, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x) ∧
  (∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (c : ℕ) (hc : c.Coprime M), (∀ ζ : Qbar, ζ ^ M = 1 → σ ζ = ζ ^ c) →
    ∀ x : JG Γ,
      SemilinearAut.ofAlgAut w • (arithmeticGalois (F0 Γ) σ • x)
        = arithmeticGalois (F0 Γ) σ • diaG M Γ (ZMod.unitOfCoprime c hc)
            (SemilinearAut.ofAlgAut w • x))

variable {M} in

theorem lawFourH {H : Subgroup (ZMod M)ˣ}
    {w : xHFunctionFieldBar M H ≃ₐ[Qbar] xHFunctionFieldBar M H}
    (hgal : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (c : ℕ) (hc : c.Coprime M), (∀ ζ : Qbar, ζ ^ M = 1 → σ ζ = ζ ^ c) →
      ∀ x : xHFunctionFieldBar M H,
        w (arithmeticGalois (xHFunctionField M H) σ • x) =
          arithmeticGalois (xHFunctionField M H) σ • diamondAutHBar M H (ZMod.unitOfCoprime c hc) (w x))
    (σ : Qbar ≃ₐ[ℚ] Qbar) (c : ℕ) (hc : c.Coprime M) (hζ : ∀ ζ : Qbar, ζ ^ M = 1 → σ ζ = ζ ^ c)
    (x : JH M H) :
    SemilinearAut.ofAlgAut w • (σ • x)
      = σ • diamondHBar M H (ZMod.unitOfCoprime c hc) (SemilinearAut.ofAlgAut w • x) := by
  have key : SemilinearAut.ofAlgAut w * arithmeticGalois (xHFunctionField M H) σ =
      arithmeticGalois (xHFunctionField M H) σ *
        SemilinearAut.ofAlgAut (diamondAutHBar M H (ZMod.unitOfCoprime c hc)) *
          SemilinearAut.ofAlgAut w := by
    refine Subtype.ext (Prod.ext (RingEquiv.ext fun y => ?_) ?_)
    · exact hgal σ c hc hζ y
    · change (1 : Qbar ≃+* Qbar) * σ.toRingEquiv = σ.toRingEquiv * 1 * 1
      rw [one_mul, mul_one, mul_one]
  have := congrArg (fun g => g • x) key
  simp only [mul_smul] at this
  rw [galois_smul_pic0_def, galois_smul_pic0_def, diamondHBar_apply]
  exact this

theorem exists_laws_specH (ι : Qbar →+* ℂ) (H : Subgroup (ZMod M)ˣ) :
    ∃ w : xHFunctionFieldBar M H ≃ₐ[Qbar] xHFunctionFieldBar M H,
      ((∀ (ℓ : ℕ) [Fact ℓ.Prime]
          (hα : HeckeAlphaHBarIntegral Qbar M H ℓ)
          (hβ : HeckeBetaHBarIntegral Qbar M H ℓ)
          [HasPrincipalDivisors Qbar (laurentBaseChange Qbar (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
          (hFIβ : FundamentalIdentityAlong Qbar (heckeBetaHBar Qbar M H ℓ) hβ)
          (hfinα : FiniteAlong Qbar (heckeAlphaHBar Qbar M H ℓ))
          (hNα : NormFormulaAlong Qbar (heckeAlphaHBar Qbar M H ℓ) hfinα)
          (hFIα : FundamentalIdentityAlong Qbar (heckeAlphaHBar Qbar M H ℓ) hα)
          (hfinβ : FiniteAlong Qbar (heckeBetaHBar Qbar M H ℓ))
          (hNβ : NormFormulaAlong Qbar (heckeBetaHBar Qbar M H ℓ) hfinβ)
          (x : JH M H),
        heckePic0HBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w • x)
          = SemilinearAut.ofAlgAut w • heckePic0HBar hα hβ hFIβ hfinα hNα x) ∧
      (∀ (d : (ZMod M)ˣ) (x : JH M H),
        diamondHBar M H d (SemilinearAut.ofAlgAut w • diamondHBar M H d x)
          = SemilinearAut.ofAlgAut w • x) ∧
      (∀ x : JH M H, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x) ∧
      (∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (c : ℕ) (hc : c.Coprime M),
        (∀ ζ : Qbar, ζ ^ M = 1 → σ ζ = ζ ^ c) →
          ∀ x : JH M H,
            SemilinearAut.ofAlgAut w • (σ • x)
              = σ • diamondHBar M H (ZMod.unitOfCoprime c hc) (SemilinearAut.ofAlgAut w • x))) ∧
      SpecG (CohCarrier.GammaH M H) (frickeGL M) ι w := by
  obtain ⟨w, spec, hgal⟩ :=
    ModularCurve.exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul M H
      (ModularCurve.heckeDiamondInputsHAll M H).2 ι (frickeGL M) rfl
  obtain ⟨h1, h2, h3⟩ :=
    ModularCurve.heckePic0HBarTranspose_smul_diamondHBar_smul_smul_of_qExpansion_slash_fricke M H ι
      (frickeGL M) rfl w spec
  exact ⟨w, ⟨h1, h2, h3, fun σ c hc hζ x => lawFourH hgal σ c hc hζ x⟩,
    fun x k f g h => spec x k f g h⟩

theorem exists_frLaws_spec_bot (ι : Qbar →+* ℂ) :
    ∃ w, FrLawsG M (CohCarrier.GammaH M ⊥) w ∧ SpecG (CohCarrier.GammaH M ⊥) (frickeGL M) ι w :=
  exists_laws_specH M ι ⊥

theorem exists_frLaws_spec_one (ι : Qbar →+* ℂ) :
    ∃ w, FrLawsG M (Gamma1 M) w ∧ SpecG (Gamma1 M) (frickeGL M) ι w := by
  have key : ∀ Γ : Subgroup SL(2, ℤ), Γ = CohCarrier.GammaH M ⊥ →
      ∃ w, FrLawsG M Γ w ∧ SpecG Γ (frickeGL M) ι w := by
    rintro Γ rfl
    exact exists_frLaws_spec_bot M ι
  exact key _ (GammaH_bot M).symm

theorem exists_isDiaG_one (d : (ZMod M)ˣ) : ∃ σ, IsDiaG M (Gamma1 M) d σ := by
  have key : ∀ Γ : Subgroup SL(2, ℤ), Γ = CohCarrier.GammaH M ⊥ → ∃ σ, IsDiaG M Γ d σ := by
    rintro Γ rfl
    exact (ModularCurve.heckeDiamondInputsHAll M ⊥).2 d
  exact key _ (GammaH_bot M).symm

end Transport

section Slash

variable {M : ℕ}

abbrev Γ1 (M : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ Gamma1 M := by
  rw [← GammaH_bot]; exact translation_mem_GammaH M ⊥

theorem one_mem_strictPeriods_of_T_mem {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ ((Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ1 M).strictPeriods :=
  one_mem_strictPeriods_of_T_mem (T_mem_Gamma1 M)

theorem conj_mem_Gamma1 {γ δ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hδ : δ ∈ Gamma1 M) :
    γ * δ * γ⁻¹ ∈ Gamma1 M := by
  rw [← GammaH_bot] at hδ ⊢
  exact CohCarrier.conj_mem_GammaH M ⊥ ⟨γ, hγ⟩ ⟨δ, hδ⟩

theorem le_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    Γ1 M ≤ ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹ • Γ1 M := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨γ * δ * γ⁻¹, conj_mem_Gamma1 hγ hδ, by simp; rfl⟩

def slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (Γ1 M) k) :
    ModularForm (Γ1 M) k :=
  restrictForm (le_conj hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))

@[scoped simp]
theorem coe_slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (Γ1 M) k) :
    ⇑(slashForm γ hγ f) = ⇑f ∣[k] (γ : GL (Fin 2) ℝ) := rfl

theorem qC_eq_zero_iff_of_T_mem {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (f : ModularForm ((Γ : Subgroup (GL (Fin 2) ℝ))) k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods_of_T_mem hT) f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (Γ1 M) k) : qC f = 0 ↔ f = 0 :=
  qC_eq_zero_iff_of_T_mem (T_mem_Gamma1 M) f

abbrev ιC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

theorem ιC_injective : Function.Injective ιC := RingHom.injective _

theorem ιC_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    ιC (intSeriesC ℚ p) = qC F := by
  rw [qC, ← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem ne_zero_of_intSeriesC_ne_zero {k : ℤ} {g : ModularForm (Γ1 M) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : g ≠ 0 := by
  intro h
  have h1 : qC g = 0 := (qC_eq_zero_iff g).mpr h
  rw [← ιC_intSeriesC hg] at h1
  exact hg0 ((map_eq_zero_iff _ ιC_injective).mp h1)

theorem slashForm_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {f : ModularForm (Γ1 M) k}
    (hf : f ≠ 0) : slashForm γ hγ f ≠ 0 := by
  intro h
  apply hf
  have h2 : slashForm γ⁻¹ (inv_mem hγ) (slashForm γ hγ f) = f := by
    ext τ
    simp only [coe_slashForm, map_inv, ← SlashAction.slash_mul, mul_inv_cancel,
      SlashAction.slash_one]
  rw [← h2, h]
  ext τ
  simp [coe_slashForm]

theorem qC_slash_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {g : ModularForm (Γ1 M) k}
    {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    qC (⇑g ∣[k] (γ : GL (Fin 2) ℝ)) ≠ 0 := fun h =>
  slashForm_ne_zero γ hγ (ne_zero_of_intSeriesC_ne_zero hg hg0)
    ((qC_eq_zero_iff (slashForm γ hγ g)).mp h)

end Slash

section Unique

variable (Γ : Subgroup SL(2, ℤ))

abbrev genB : Set (LaurentSeries Qbar) := ⇑(coeffEmb Qbar) '' intFormRatiosC ℚ Γ

theorem FB_eq_adjoin : FB Γ = IntermediateField.adjoin Qbar (genB Γ) := by
  apply le_antisymm
  · rw [FB, laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ (qExpFunctionFieldC ℚ Γ).toSubfield := hz
    rw [qExpFunctionFieldC, IntermediateField.adjoin_toSubfield] at hz'
    have key : (Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ Γ)).map
        (coeffEmb Qbar) ≤ (IntermediateField.adjoin Qbar (genB Γ)).toSubfield := by
      rw [RingHom.map_field_closure, Subfield.closure_le]
      rintro _ ⟨y, hy, rfl⟩
      rcases hy with ⟨c, rfl⟩ | hyS
      · have hcomp : (coeffEmb Qbar).comp (algebraMap ℚ (LaurentSeries ℚ))
            = (algebraMap Qbar (LaurentSeries Qbar)).comp (algebraMap ℚ Qbar) := Subsingleton.elim _ _
        change coeffEmb Qbar (algebraMap ℚ _ c) ∈ IntermediateField.adjoin Qbar (genB Γ)
        rw [← RingHom.comp_apply, hcomp, RingHom.comp_apply]
        exact IntermediateField.algebraMap_mem _ _
      · exact IntermediateField.subset_adjoin Qbar _ ⟨y, hyS, rfl⟩
    exact key ⟨z, hz', rfl⟩
  · exact IntermediateField.adjoin.mono Qbar _ _ (Set.image_mono (intFormRatiosC_subset ℚ Γ))

variable {Γ}

theorem algHom_ext_gen {R : Type*} [Semiring R] [Algebra Qbar R] (φ ψ : FB Γ →ₐ[Qbar] R)
    (h : ∀ (k : ℤ) (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ)
      (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0),
      φ ⟨coeffEmb Qbar (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange Qbar (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ =
        ψ ⟨coeffEmb Qbar (intSeriesC ℚ pf / intSeriesC ℚ pg),
          coeffEmb_mem_laurentBaseChange Qbar (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩) :
    φ = ψ := by
  refine IntermediateField.algHom_ext_of_eq_adjoin Qbar (FB_eq_adjoin Γ) ?_
  rintro _ ⟨x, ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
  exact h k f g pf pg hf hg hg0

theorem baseChangeAut_refl : baseChangeAut Qbar (AlgEquiv.refl : F0 Γ ≃ₐ[ℚ] F0 Γ) = AlgEquiv.refl := by
  have hex : ∃ σ : FB Γ ≃ₐ[Qbar] FB Γ, IsBaseChangeAutOf Qbar (AlgEquiv.refl : F0 Γ ≃ₐ[ℚ] F0 Γ) σ :=
    ⟨AlgEquiv.refl, fun _ => rfl⟩
  have hB := isBaseChangeAutOf_baseChangeAut (L := Qbar) hex
  apply AlgEquiv.ext
  intro x
  have key : ((baseChangeAut Qbar (AlgEquiv.refl : F0 Γ ≃ₐ[ℚ] F0 Γ)).toAlgHom : FB Γ →ₐ[Qbar] FB Γ)
      = (AlgEquiv.refl : FB Γ ≃ₐ[Qbar] FB Γ).toAlgHom := by
    refine algHom_ext_gen _ _ fun k f g pf pg hf hg hg0 => Subtype.ext ?_
    exact hB ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩
  exact AlgHom.congr_fun key x

end Unique

section Dictionary

variable {M : ℕ} [NeZero M]

theorem exists_gamma0_of_coprime {d : ℕ} (hd : d.Coprime M) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M ∧ ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
  have hb : ((1 : ℕ) : ℤ) = (d : ℤ) * Nat.gcdA d M + (M : ℤ) * Nat.gcdB d M := by
    rw [← hd]; exact Nat.gcd_eq_gcd_ab d M
  set a := Nat.gcdA d M
  set b := Nat.gcdB d M
  refine ⟨⟨!![(d : ℤ), -b; (M : ℤ), a], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    push_cast at hb
    linear_combination -hb
  · rw [Gamma0_mem]
    show (((!![(d : ℤ), -b; (M : ℤ), a] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M) = 0
    simp
  · show (((!![(d : ℤ), -b; (M : ℤ), a] : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod M) = (d : ZMod M)
    simp

theorem diaAutG_one_eq {d : ℕ} (hd : d.Coprime M) :
    diaAutG M (Gamma1 M) (ZMod.unitOfCoprime d hd) = diamondAutBar M d := by
  set u := ZMod.unitOfCoprime d hd with hu
  have huc : (u : ZMod M) = (d : ZMod M) := ZMod.coe_unitOfCoprime d hd

  have hAll := ModularCurve.heckeDiamondInputsAll M
  obtain ⟨hex0, hexB⟩ := hAll.2 d hd
  have hD : IsDiamondAut M d (diamondAut M d) := isDiamondAut_diamondAut hex0
  have hB : IsBaseChangeAutOf Qbar (diamondAut M d) (diamondAutBar M d) :=
    isBaseChangeAutOf_baseChangeAut (L := Qbar) hexB
  have hH : IsDiaG M (Gamma1 M) u (diaAutG M (Gamma1 M) u) := isDiaG_diaAutG (exists_isDiaG_one M u)
  obtain ⟨γ, hγ, hγd⟩ := exists_gamma0_of_coprime hd
  apply AlgEquiv.ext
  intro x
  have key : ((diaAutG M (Gamma1 M) u).toAlgHom : FB (Gamma1 M) →ₐ[Qbar] FB (Gamma1 M))
      = (diamondAutBar M d).toAlgHom := by
    refine algHom_ext_gen _ _ fun k f g pf pg hf hg hg0 => Subtype.ext ?_

    obtain ⟨z₂, -, hz₂, hz₂'⟩ := hH k f g pf pg hf hg hg0 γ hγ (hγd.trans huc.symm)
    have hz₁ := hB ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩
    have hz₁' := hD.2 k f g pf pg hf hg hg0 γ hγ hγd
    set z₁ : LaurentSeries ℚ := ((diamondAut M d ⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
      div_mem_qExpFunctionFieldC f g hf hg hg0⟩ : x1FunctionField M) : LaurentSeries ℚ) with hz₁def
    have hne : qC (⇑g ∣[k] (γ : GL (Fin 2) ℝ)) ≠ 0 := qC_slash_ne_zero γ hγ hg hg0
    have heq : ιC z₂ = ιC z₁ := by
      apply mul_right_cancel₀ hne
      change coeffMap (algebraMap ℚ ℂ) z₂ * ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ)))
        = coeffMap (algebraMap ℚ ℂ) z₁ * ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ)))
      rw [hz₂']
      exact hz₁'.symm
    have hzz : z₂ = z₁ := ιC_injective heq
    change ((diaAutG M (Gamma1 M) u _ : FB (Gamma1 M)) : LaurentSeries Qbar) = ((diamondAutBar M d _ : FB (Gamma1 M)) : LaurentSeries Qbar)
    rw [hz₂, hzz]
    exact hz₁.symm
  exact AlgHom.congr_fun key x

theorem diaG_one_apply {d : ℕ} (hd : d.Coprime M) (x : JOne M) :
    diaG M (Gamma1 M) (ZMod.unitOfCoprime d hd) x = diamondOneBar M d x := by
  rw [diaG_apply, diaAutG_one_eq hd]
  rfl

theorem diamondOneBar_of_not_coprime {d : ℕ} (hd : ¬ d.Coprime M) (x : JOne M) :
    diamondOneBar M d x = x := by
  rw [diamondOneBar_apply, diamondAutBar, diamondAut_of_not_coprime hd]
  have h : baseChangeAut Qbar (AlgEquiv.refl : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M) = AlgEquiv.refl :=
    baseChangeAut_refl (Γ := Gamma1 M)
  rw [h]
  have h1 : SemilinearAut.ofAlgAut (AlgEquiv.refl : x1FunctionFieldBar M ≃ₐ[Qbar] x1FunctionFieldBar M) = 1 :=
    map_one _
  rw [h1, one_smul]

end Dictionary

section FrickeForm

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

abbrev ΓGL (Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ) :=
  ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem mapGL_eq_coe (γ : SL(2, ℤ)) : Matrix.SpecialLinearGroup.mapGL ℝ γ = (γ : GL (Fin 2) ℝ) := rfl

theorem frickeGL_mul_mul_inv (γ : SL(2, ℤ)) (h : (M : ℤ) ∣ γ 1 0) :
    frickeGL M * Matrix.SpecialLinearGroup.mapGL ℝ γ * (frickeGL M)⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ (CohCarrier.frickeMat M γ h) := by
  rw [mul_inv_eq_iff_eq_mul, mapGL_eq_coe, mapGL_eq_coe]
  ext i j
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  obtain ⟨c, hc⟩ := h
  have hc' : (γ 1 0 / M : ℤ) = c := by rw [hc, Int.mul_ediv_cancel_left _ (by exact_mod_cast NeZero.ne M)]
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_two, CohCarrier.frickeMat, hc]; try ring)

theorem le_conj_frickeGL :
    ΓGL (CohCarrier.GammaH M H) ≤ ConjAct.toConjAct (frickeGL M)⁻¹ • ΓGL (CohCarrier.GammaH M H) := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  have h10 := CohCarrier.N_dvd_of_mem_GammaH M H ⟨δ, hδ⟩
  exact ⟨CohCarrier.frickeMat M δ h10, CohCarrier.frickeMat_mem M H ⟨δ, hδ⟩,
    (frickeGL_mul_mul_inv δ h10).symm⟩

def frickeForm {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ModularForm (ΓGL (CohCarrier.GammaH M H)) k :=
  restrictForm le_conj_frickeGL (ModularForm.translate f (frickeGL M))

@[scoped simp]
theorem coe_frickeForm {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(frickeForm f) = ⇑f ∣[k] frickeGL M := rfl

theorem frickeForm_ne_zero {k : ℤ} {g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k} (hg : g ≠ 0) :
    frickeForm g ≠ 0 := by
  intro h
  apply hg
  have h' : ⇑g ∣[k] frickeGL M = 0 := by rw [← coe_frickeForm, h, ModularForm.coe_zero]
  have : (⇑g : ℍ → ℂ) = 0 := by
    have := congrArg (fun F : ℍ → ℂ => F ∣[k] (frickeGL M)⁻¹) h'
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one,
      SlashAction.zero_slash] using this
  exact DFunLike.ext' (by rw [this, ModularForm.coe_zero])

theorem qC_frickeForm_ne_zero {k : ℤ} {g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k}
    (hg : qC g ≠ 0) : qC (⇑g ∣[k] frickeGL M) ≠ 0 := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H
  rw [← coe_frickeForm]
  exact fun h0 => frickeForm_ne_zero (fun h => hg ((qC_eq_zero_iff_of_T_mem hT g).mpr h))
    ((qC_eq_zero_iff_of_T_mem hT _).mp h0)

end FrickeForm

section Square

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem xHBar_le_x1Bar : xHFunctionFieldBar M H ≤ x1FunctionFieldBar M :=
  laurentBaseChange_monoG (xHFunctionFieldC_le_x1 ℚ M H)

def incl : xHFunctionFieldBar M H →ₐ[Qbar] x1FunctionFieldBar M :=
  IntermediateField.inclusion xHBar_le_x1Bar

theorem coe_incl (x : xHFunctionFieldBar M H) :
    ((incl x : x1FunctionFieldBar M) : LaurentSeries Qbar) = (x : LaurentSeries Qbar) :=
  IntermediateField.coe_inclusion _ x

theorem coeffMap_injective (ι : Qbar →+* ℂ) : Function.Injective (coeffMap ι) := fun x y h => by
  ext k
  exact ι.injective (by simpa using congrArg (fun z => z.coeff k) h)

theorem coeffMap_coeffEmb (ι : Qbar →+* ℂ) (y : LaurentSeries ℚ) :
    coeffMap ι (coeffEmb Qbar y) = coeffMap (algebraMap ℚ ℂ) y := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) y

theorem Γ1_le_ΓH : Γ1 M ≤ ΓGL (CohCarrier.GammaH M H) :=
  Subgroup.map_mono (Gamma1_le_GammaH M H)

theorem coe_wH_eq_coe_w1 (ι : Qbar →+* ℂ)
    {wH : xHFunctionFieldBar M H ≃ₐ[Qbar] xHFunctionFieldBar M H}
    {w₁ : x1FunctionFieldBar M ≃ₐ[Qbar] x1FunctionFieldBar M}
    (specH : SpecG (CohCarrier.GammaH M H) (frickeGL M) ι wH)
    (spec₁ : SpecG (Gamma1 M) (frickeGL M) ι w₁) (u : xHFunctionFieldBar M H) :
    ((wH u : xHFunctionFieldBar M H) : LaurentSeries Qbar) =
      ((w₁ (incl u) : x1FunctionFieldBar M) : LaurentSeries Qbar) := by

  let φ₁ : xHFunctionFieldBar M H →ₐ[Qbar] LaurentSeries Qbar :=
    (IntermediateField.val _).comp (wH : xHFunctionFieldBar M H →ₐ[Qbar] xHFunctionFieldBar M H)
  let φ₂ : xHFunctionFieldBar M H →ₐ[Qbar] LaurentSeries Qbar :=
    (IntermediateField.val _).comp
      ((w₁ : x1FunctionFieldBar M →ₐ[Qbar] x1FunctionFieldBar M).comp incl)
  suffices h : φ₁ = φ₂ from AlgHom.congr_fun h u
  refine algHom_ext_gen (Γ := CohCarrier.GammaH M H) φ₁ φ₂ fun k f g pf pg hf hg hg0 => ?_
  set x₀ : xHFunctionFieldBar M H := ⟨coeffEmb Qbar (intSeriesC ℚ pf / intSeriesC ℚ pg),
    coeffEmb_mem_laurentBaseChange Qbar (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ with hx₀
  change ((wH x₀ : xHFunctionFieldBar M H) : LaurentSeries Qbar) =
    ((w₁ (incl x₀) : x1FunctionFieldBar M) : LaurentSeries Qbar)
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H

  have hqg : qC g ≠ 0 := by
    rw [← ιC_intSeriesC hg]
    exact (map_ne_zero_iff _ ιC_injective).mpr hg0
  have h0 : coeffMap ι (x₀ : LaurentSeries Qbar) * qC g = qC f := by
    change coeffMap ι (coeffEmb Qbar (intSeriesC ℚ pf / intSeriesC ℚ pg)) * qC g = qC f
    rw [coeffMap_coeffEmb, map_div₀, ιC_intSeriesC hf, ιC_intSeriesC hg, div_mul_cancel₀ _ hqg]

  have hH := specH x₀ k f g h0

  have h0' : coeffMap ι ((incl x₀ : x1FunctionFieldBar M) : LaurentSeries Qbar) *
      qC (restrictForm Γ1_le_ΓH g) = qC (restrictForm Γ1_le_ΓH f) := by
    rw [coe_incl, coe_restrictForm, coe_restrictForm]; exact h0
  have h1 := spec₁ (incl x₀) k (restrictForm Γ1_le_ΓH f) (restrictForm Γ1_le_ΓH g) h0'
  rw [coe_restrictForm, coe_restrictForm] at h1

  change coeffMap ι _ * qC (⇑g ∣[k] frickeGL M) = qC (⇑f ∣[k] frickeGL M) at hH
  change coeffMap ι _ * qC (⇑g ∣[k] frickeGL M) = qC (⇑f ∣[k] frickeGL M) at h1
  rw [← h1] at hH
  exact coeffMap_injective ι (mul_right_cancel₀ (qC_frickeForm_ne_zero hqg) hH)

theorem eq_incl (ι' : xHFunctionFieldBar M H →ₐ[Qbar] x1FunctionFieldBar M)
    (hι' : ∀ x : xHFunctionFieldBar M H,
      ((ι' x : x1FunctionFieldBar M) : LaurentSeries Qbar) = (x : LaurentSeries Qbar)) :
    ι' = incl :=
  AlgHom.ext fun x => Subtype.ext (by rw [hι' x, coe_incl])

end Square

section Involution

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

def scalarGL (a : ℝ) (ha : a ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, a]
    (by rw [Matrix.det_fin_two_of]; simpa using ha)

@[scoped simp]
theorem val_scalarGL (a : ℝ) (ha : a ≠ 0) :
    ((scalarGL a ha : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, 0; 0, a] := rfl

theorem det_scalarGL (a : ℝ) (ha : a ≠ 0) : ((scalarGL a ha).det : ℝ) = a * a := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_scalarGL, Matrix.det_fin_two_of]; ring

theorem scalarGL_smul (a : ℝ) (ha : a ≠ 0) (τ : ℍ) : scalarGL a ha • τ = τ := by
  have hdet : 0 < ((scalarGL a ha).det : ℝ) := by rw [det_scalarGL]; exact mul_self_pos.mpr ha
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos hdet]
  simp only [num, denom, val_scalarGL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_zero, zero_mul, add_zero, zero_add]
  rw [mul_div_assoc, mul_div_cancel₀ _ (by exact_mod_cast ha)]

theorem slash_scalarGL (k : ℤ) (a : ℝ) (ha : a ≠ 0) (φ : ℍ → ℂ) :
    φ ∣[k] scalarGL a ha = (fun _ => ((|a * a| : ℝ) : ℂ) ^ (k - 1) * (a : ℂ) ^ (-k)) * φ := by
  have hdet : 0 < ((scalarGL a ha).det : ℝ) := by rw [det_scalarGL]; exact mul_self_pos.mpr ha
  funext τ
  rw [ModularForm.slash_apply, scalarGL_smul, Pi.mul_apply]
  have hσ : σ (scalarGL a ha) = ContinuousAlgEquiv.refl ℝ ℂ := by
    rw [σ, if_pos hdet]
  rw [hσ, ContinuousAlgEquiv.refl_apply, det_scalarGL]
  simp only [denom, val_scalarGL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_zero, zero_mul, zero_add]
  ring

theorem frickeGL_mul_frickeGL :
    frickeGL M * frickeGL M = scalarGL (-(M : ℝ)) (neg_ne_zero.mpr (by exact_mod_cast NeZero.ne M)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def frickeSqConst (M : ℕ) (k : ℤ) : ℂ :=
  ((|(-(M : ℝ)) * (-(M : ℝ))| : ℝ) : ℂ) ^ (k - 1) * ((-(M : ℝ) : ℝ) : ℂ) ^ (-k)

theorem frickeSqConst_ne_zero (k : ℤ) : frickeSqConst M k ≠ 0 := by
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  refine mul_ne_zero (zpow_ne_zero _ ?_) (zpow_ne_zero _ ?_)
  · exact_mod_cast (abs_ne_zero.mpr (mul_ne_zero (neg_ne_zero.mpr hM) (neg_ne_zero.mpr hM)))
  · exact_mod_cast neg_ne_zero.mpr hM

theorem slash_frickeGL_frickeGL (k : ℤ) (φ : ℍ → ℂ) :
    (φ ∣[k] frickeGL M) ∣[k] frickeGL M = (fun _ => frickeSqConst M k) * φ := by
  rw [← SlashAction.slash_mul, frickeGL_mul_frickeGL, slash_scalarGL]
  rfl

omit [NeZero M] in
theorem qC_smul_of_T_mem {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) {k : ℤ} (c : ℂ)
    (f : ModularForm (ΓGL Γ) k) : qC (c • ⇑f) = HahnSeries.C c * qC f := by
  rw [qC, qC, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_of_T_mem hT) c f,
    ← HahnSeries.ofPowerSeries_C, ← map_mul, PowerSeries.smul_eq_C_mul]

omit [NeZero M] in

theorem coe_smul_form {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (c : ℂ) (f : ModularForm (ΓGL Γ) k) :
    ⇑(c • f) = c • ⇑f :=
  FunLike.coe_smul c f

omit [NeZero M] in
theorem qC_const_mul_of_T_mem {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) {k : ℤ} (c : ℂ)
    (f : ModularForm (ΓGL Γ) k) : qC ((fun _ => c) * ⇑f) = HahnSeries.C c * qC f := by
  rw [show ((fun _ => c) * ⇑f : ℍ → ℂ) = c • ⇑f from rfl, qC_smul_of_T_mem hT]

theorem apply_apply_of_specG (ι : Qbar →+* ℂ)
    {w : FB (CohCarrier.GammaH M H) ≃ₐ[Qbar] FB (CohCarrier.GammaH M H)}
    (spec : SpecG (CohCarrier.GammaH M H) (frickeGL M) ι w) (x : FB (CohCarrier.GammaH M H)) :
    w (w x) = x := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H
  suffices h : ((w.trans w : FB (CohCarrier.GammaH M H) ≃ₐ[Qbar] FB (CohCarrier.GammaH M H)) :
      FB (CohCarrier.GammaH M H) →ₐ[Qbar] FB (CohCarrier.GammaH M H)) = AlgHom.id Qbar _ from
    AlgHom.congr_fun h x
  refine algHom_ext_gen _ _ fun k f g pf pg hf hg hg0 => ?_
  set x₀ : FB (CohCarrier.GammaH M H) := ⟨coeffEmb Qbar (intSeriesC ℚ pf / intSeriesC ℚ pg),
    coeffEmb_mem_laurentBaseChange Qbar (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ with hx₀
  change w (w x₀) = x₀
  have hqg : qC g ≠ 0 := by
    rw [← ιC_intSeriesC hg]
    exact (map_ne_zero_iff _ ιC_injective).mpr hg0
  have h0 : coeffMap ι (x₀ : LaurentSeries Qbar) * qC g = qC f := by
    change coeffMap ι (coeffEmb Qbar (intSeriesC ℚ pf / intSeriesC ℚ pg)) * qC g = qC f
    rw [coeffMap_coeffEmb, map_div₀, ιC_intSeriesC hf, ιC_intSeriesC hg, div_mul_cancel₀ _ hqg]
  have h1 := spec x₀ k f g h0
  change coeffMap ι _ * qC (⇑g ∣[k] frickeGL M) = qC (⇑f ∣[k] frickeGL M) at h1
  rw [← coe_frickeForm, ← coe_frickeForm] at h1
  have h2 := spec (w x₀) k (frickeForm f) (frickeForm g) h1
  change coeffMap ι _ * qC (⇑(frickeForm g) ∣[k] frickeGL M) =
    qC (⇑(frickeForm f) ∣[k] frickeGL M) at h2
  rw [coe_frickeForm, coe_frickeForm, slash_frickeGL_frickeGL, slash_frickeGL_frickeGL,
    qC_const_mul_of_T_mem hT, qC_const_mul_of_T_mem hT, ← mul_assoc, mul_comm (coeffMap ι _),
    mul_assoc] at h2
  have h3 := mul_left_cancel₀ ((map_ne_zero_iff _ HahnSeries.C_injective).mpr
    (frickeSqConst_ne_zero (M := M) k)) h2
  rw [← h0] at h3
  exact Subtype.ext (coeffMap_injective ι (mul_right_cancel₀ hqg h3))

end Involution

section LevelChange

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} (hpM : p ∣ M)

omit [Fact p.Prime] [NeZero M] in
include hpM in

theorem GammaH_le_GammaH_div :
    CohCarrier.GammaH M H ≤ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) := by
  intro A hA
  obtain ⟨hA0, hAH⟩ := CohCarrier.mem_GammaH_iff.mp hA
  have hA0' : A ∈ Gamma0 (M / p) := by
    rw [Gamma0_mem] at hA0 ⊢
    have : ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod (M / p))
        (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M)
        = (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod (M / p)) := map_intCast _ _
    rw [← this, hA0, map_zero]
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨hA0', ?_⟩
  rw [mem_infSubgroup_iff]
  refine ⟨CohCarrier.gamma0Units M ⟨A, hA0⟩, hAH, ?_⟩
  ext
  rw [ZMod.unitsMap_val, CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
  show ((((A 1 1 : ℤ) : ZMod M)).cast : ZMod (M / p)) = ((A 1 1 : ℤ) : ZMod (M / p))
  rw [ZMod.cast_intCast (Nat.div_dvd_of_dvd hpM)]

omit [Fact p.Prime] [NeZero M] in

theorem ΓGL_le_div :
    ΓGL (CohCarrier.GammaH M H) ≤ ΓGL (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) :=
  Subgroup.map_mono (GammaH_le_GammaH_div hpM)

variable [NeZero (M / p)]

include hpM in

theorem frickeGL_div_mul_heckeDiag :
    frickeGL (M / p) * ModularForm.heckeDiagMatrix p = frickeGL M := by
  have hMp : ((M / p : ℕ) : ℝ) * (p : ℝ) = (M : ℝ) := by exact_mod_cast Nat.div_mul_cancel hpM
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix (NeZero.ne p),
    val_frickeGL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hMp]

include hpM in

theorem slash_frickeGL_level (k : ℤ) (φ : ℍ → ℂ) :
    φ ∣[k] frickeGL M =
      (fun _ => ((p : ℂ) ^ (k - 1))) *
        fun τ => (φ ∣[k] frickeGL (M / p)) (ModularForm.heckeDiagMatrix p • τ) := by
  rw [← frickeGL_div_mul_heckeDiag hpM, SlashAction.slash_mul]
  funext τ
  rw [ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne p)]
  rfl

omit [Fact p.Prime] [NeZero M] [NeZero (M / p)] in

theorem ofPowerSeries_eq_qExpand {ℓ : ℕ} [NeZero ℓ] (P P' : PowerSeries ℂ)
    (h : ∀ n, PowerSeries.coeff n P' = if ℓ ∣ n then PowerSeries.coeff (n / ℓ) P else 0) :
    ofPowerSeries ℤ ℂ P' = qExpand ℂ ℓ (ofPowerSeries ℤ ℂ P) := by
  ext m
  by_cases hdvd : (ℓ : ℤ) ∣ m
  · obtain ⟨j, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    have hℓ0 : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
    by_cases hj : j < 0
    · rw [if_pos hj, if_pos (mul_neg_of_pos_of_neg hℓ0 hj)]
    · rw [if_neg hj, if_neg (by push Not at hj ⊢; positivity), h]
      have h1 : ((ℓ : ℤ) * j).natAbs = ℓ * j.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [h1, if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne ℓ))]
  · rw [qExpand_coeff_of_not_dvd ℓ _ hdvd, PowerSeries.coeff_coe]
    split_ifs with hm
    · rfl
    · rw [h, if_neg]
      rintro ⟨c, hc⟩
      apply hdvd
      refine ⟨c, ?_⟩
      have : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_not_gt hm)
      rw [← this, hc]; push_cast; ring

omit [Fact p.Prime] [NeZero M] [NeZero (M / p)] in

theorem qC_comp_heckeDiag {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (F : ModularForm (ΓGL Γ) k) (ℓ : ℕ) [NeZero ℓ] :
    qC (fun τ => F (ModularForm.heckeDiagMatrix ℓ • τ)) = qExpand ℂ ℓ (qC F) :=
  ofPowerSeries_eq_qExpand _ _ fun n =>
    ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul F (one_mem_strictPeriods_of_T_mem hT)
      (NeZero.ne ℓ) n

include hpM in

theorem qC_slash_frickeGL_level {k : ℤ}
    (f : ModularForm (ΓGL (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) k) :
    qC (⇑f ∣[k] frickeGL M) =
      qExpand ℂ p (HahnSeries.C ((p : ℂ) ^ (k - 1)) * qC (⇑f ∣[k] frickeGL (M / p))) := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) :=
    translation_mem_GammaH _ _
  rw [slash_frickeGL_level hpM, ← coe_frickeForm, ← qC_smul_of_T_mem hT, ← coe_smul_form,
    ← qC_comp_heckeDiag hT ((((p : ℂ) ^ (k - 1))) • frickeForm f) p]
  congr 1

end LevelChange

section Exchange

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} (hpM : p ∣ M) [NeZero (M / p)]
  (ι : Qbar →+* ℂ)
  {w : xHFunctionFieldBar M H ≃ₐ[Qbar] xHFunctionFieldBar M H}
  {w' : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) ≃ₐ[Qbar]
    xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)}
  {αH βH : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) →ₐ[Qbar] xHFunctionFieldBar M H}

theorem apply_alpha_eq
    (specH : SpecG (CohCarrier.GammaH M H) (frickeGL M) ι w)
    (spec' : SpecG (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) (frickeGL (M / p)) ι w')
    (hα : ∀ u : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM),
      ((αH u : xHFunctionFieldBar M H) : LaurentSeries Qbar) = (u : LaurentSeries Qbar))
    (hβ : ∀ u : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM),
      ((βH u : xHFunctionFieldBar M H) : LaurentSeries Qbar) = qExpand Qbar p (u : LaurentSeries Qbar))
    (u : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :
    w (αH u) = βH (w' u) := by
  suffices h : (w : xHFunctionFieldBar M H →ₐ[Qbar] xHFunctionFieldBar M H).comp αH =
      βH.comp (w' : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) →ₐ[Qbar]
        xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) from AlgHom.congr_fun h u
  refine algHom_ext_gen (Γ := CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) _ _
    fun k f g pf pg hf hg hg0 => Subtype.ext ?_
  set x₀ : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) :=
    ⟨coeffEmb Qbar (intSeriesC ℚ pf / intSeriesC ℚ pg),
      coeffEmb_mem_laurentBaseChange Qbar (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ with hx₀
  change ((w (αH x₀) : xHFunctionFieldBar M H) : LaurentSeries Qbar) =
    ((βH (w' x₀) : xHFunctionFieldBar M H) : LaurentSeries Qbar)
  have hqg : qC g ≠ 0 := by
    rw [← ιC_intSeriesC hg]
    exact (map_ne_zero_iff _ ιC_injective).mpr hg0
  have h0 : coeffMap ι (x₀ : LaurentSeries Qbar) * qC g = qC f := by
    change coeffMap ι (coeffEmb Qbar (intSeriesC ℚ pf / intSeriesC ℚ pg)) * qC g = qC f
    rw [coeffMap_coeffEmb, map_div₀, ιC_intSeriesC hf, ιC_intSeriesC hg, div_mul_cancel₀ _ hqg]

  have h4 := spec' x₀ k f g h0
  change coeffMap ι _ * qC (⇑g ∣[k] frickeGL (M / p)) = qC (⇑f ∣[k] frickeGL (M / p)) at h4

  have h0' : coeffMap ι ((αH x₀ : xHFunctionFieldBar M H) : LaurentSeries Qbar) *
      qC (restrictForm (ΓGL_le_div hpM) g) = qC (restrictForm (ΓGL_le_div hpM) f) := by
    rw [hα, coe_restrictForm, coe_restrictForm]; exact h0
  have h5 := specH (αH x₀) k (restrictForm (ΓGL_le_div hpM) f) (restrictForm (ΓGL_le_div hpM) g) h0'
  change coeffMap ι _ * qC (⇑(restrictForm (ΓGL_le_div hpM) g) ∣[k] frickeGL M) =
    qC (⇑(restrictForm (ΓGL_le_div hpM) f) ∣[k] frickeGL M) at h5
  rw [coe_restrictForm, coe_restrictForm, qC_slash_frickeGL_level hpM,
    qC_slash_frickeGL_level hpM] at h5

  apply coeffMap_injective ι
  rw [hβ, coeffMap_qExpandG]
  have hne : qExpand ℂ p (HahnSeries.C ((p : ℂ) ^ (k - 1)) * qC (⇑g ∣[k] frickeGL (M / p))) ≠ 0 := by
    refine (map_ne_zero_iff (qExpand ℂ p) (qExpand_injective p)).mpr
      (mul_ne_zero ?_ (qC_frickeForm_ne_zero hqg))
    exact (map_ne_zero_iff _ HahnSeries.C_injective).mpr
      (zpow_ne_zero _ (by exact_mod_cast NeZero.ne p))
  apply mul_right_cancel₀ hne
  rw [h5, ← map_mul, mul_left_comm, h4]

theorem apply_beta_eq
    (specH : SpecG (CohCarrier.GammaH M H) (frickeGL M) ι w)
    (spec' : SpecG (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) (frickeGL (M / p)) ι w')
    (hα : ∀ u : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM),
      ((αH u : xHFunctionFieldBar M H) : LaurentSeries Qbar) = (u : LaurentSeries Qbar))
    (hβ : ∀ u : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM),
      ((βH u : xHFunctionFieldBar M H) : LaurentSeries Qbar) = qExpand Qbar p (u : LaurentSeries Qbar))
    (u : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :
    w (βH u) = αH (w' u) := by
  have h := apply_alpha_eq hpM ι specH spec' hα hβ (w' u)
  have e1 : w' (w' u) = u := apply_apply_of_specG ι spec' u
  rw [e1] at h
  rw [← h]
  exact apply_apply_of_specG ι specH (αH (w' u))

end Exchange

section CrossPush

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable {g : SemilinearAut K F} {g' : SemilinearAut K F'}
variable {φ ψ : F →ₐ[K] F'}

def CrossIntertwines (φ ψ : F →ₐ[K] F') (g : SemilinearAut K F) (g' : SemilinearAut K F') :
    Prop :=
  ∀ x : F, g' • (φ x) = ψ (g • x)

theorem CrossIntertwines.inv (h : CrossIntertwines φ ψ g g') :
    CrossIntertwines ψ φ g⁻¹ g'⁻¹ := by
  intro x
  have hx := h (g⁻¹ • x)
  rw [smul_inv_smul] at hx
  rw [← hx, inv_smul_smul]

theorem restrictAlong_smul (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h : CrossIntertwines φ ψ g g') (v : Place K F') :
    (g' • v).restrictAlong ψ hψ = g • v.restrictAlong φ hφ := by
  apply Place.toValuationSubring_injective
  ext x
  change ψ x ∈ (g' • v).toValuationSubring ↔
    x ∈ (g • v.restrictAlong φ hφ).toValuationSubring
  rw [SemilinearAut.smul_toValuationSubring, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, h.inv x]
  rfl

def restrictEquiv (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h : CrossIntertwines φ ψ g g') (v : Place K F') :
    (v.restrictAlong φ hφ).toValuationSubring ≃+*
      ((g' • v).restrictAlong ψ hψ).toValuationSubring where
  toFun x := ⟨g • (x : F), by
    have hx : φ (x : F) ∈ v.toValuationSubring := x.2
    show ψ (g • (x : F)) ∈ (g' • v).toValuationSubring
    rw [SemilinearAut.smul_toValuationSubring, ← h (x : F)]
    exact ValuationSubring.smul_mem_pointwise_smul g' _ _ hx⟩
  invFun y := ⟨g⁻¹ • (y : F), by
    have hy : ψ (y : F) ∈ (g' • v).toValuationSubring := y.2
    show φ (g⁻¹ • (y : F)) ∈ v.toValuationSubring
    rw [SemilinearAut.smul_toValuationSubring,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hy
    rw [← h.inv (y : F)]
    exact hy⟩
  left_inv x := by ext; exact inv_smul_smul g (x : F)
  right_inv y := by ext; exact smul_inv_smul g (y : F)
  map_mul' x y := by ext; exact smul_mul' g (x : F) (y : F)
  map_add' x y := by ext; exact smul_add g (x : F) (y : F)

theorem inertiaDegAlong_smul (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h : CrossIntertwines φ ψ g g') (v : Place K F') :
    (g' • v).inertiaDegAlong ψ hψ = v.inertiaDegAlong φ hφ := by
  letI iφ : Algebra (v.restrictAlong φ hφ).ResidueField v.ResidueField :=
    (letI := algebraAlong φ; haveI := isScalarTower_along φ; haveI := isIntegral_along φ hφ
     (Place.restrictResidueMap F v).toAlgebra)
  letI iψ : Algebra ((g' • v).restrictAlong ψ hψ).ResidueField (g' • v).ResidueField :=
    (letI := algebraAlong ψ; haveI := isScalarTower_along ψ; haveI := isIntegral_along ψ hψ
     (Place.restrictResidueMap F (g' • v)).toAlgebra)
  change Module.finrank ((g' • v).restrictAlong ψ hψ).ResidueField (g' • v).ResidueField
    = Module.finrank (v.restrictAlong φ hφ).ResidueField v.ResidueField
  refine (Algebra.finrank_eq_of_equiv_equiv
    (IsLocalRing.ResidueField.mapEquiv (restrictEquiv hφ hψ h v))
    (SemilinearAut.smulResidueRingEquiv g' v) ?_).symm
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change IsLocalRing.residue (g' • v).toValuationSubring
      (⟨ψ (g • (a : F)), _⟩ : (g' • v).toValuationSubring)
    = IsLocalRing.residue (g' • v).toValuationSubring
      (⟨g' • φ (a : F), _⟩ : (g' • v).toValuationSubring)
  exact congrArg (IsLocalRing.residue _) (Subtype.ext (h (a : F)).symm)

theorem pushforwardAlong_smul (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h : CrossIntertwines φ ψ g g') (E : Divisor K F') :
    Divisor.pushforwardAlong ψ hψ (g' • E) = g • Divisor.pushforwardAlong φ hφ E := by
  induction E using Finsupp.induction with
  | zero => rw [smul_zero, map_zero, map_zero, smul_zero]
  | single_add v n D _ _ ih =>
    rw [smul_add, map_add, map_add, smul_add, ih]
    congr 1
    rw [SemilinearAut.smul_single, Divisor.pushforwardAlong_single,
      Divisor.pushforwardAlong_single, SemilinearAut.smul_single,
      restrictAlong_smul hφ hψ h v, inertiaDegAlong_smul hφ hψ h v]

theorem pushforwardAlongHom_cross (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfinφ : FiniteAlong K φ) (hNφ : NormFormulaAlong K φ hfinφ)
    (hfinψ : FiniteAlong K ψ) (hNψ : NormFormulaAlong K ψ hfinψ)
    (h : CrossIntertwines φ ψ g g') (x : Pic0 K F') :
    Pic0.pushforwardAlongHom ψ hψ hfinψ hNψ (g' • x) =
      g • Pic0.pushforwardAlongHom φ hφ hfinφ hNφ x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [SemilinearAut.pic0_smul_mk, Pic0.pushforwardAlongHom_mk, Pic0.pushforwardAlongHom_mk,
    SemilinearAut.pic0_smul_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  rw [Pic0.coe_pushforwardAlongDegZero, SemilinearAut.coe_degZeroSMulHom,
    SemilinearAut.coe_degZeroSMulHom, Pic0.coe_pushforwardAlongDegZero]
  exact pushforwardAlong_smul hφ hψ h (D : Divisor K F')

end CrossPush

end FrTriple
p2m_reactivate "P2MW.S_ModularCurve_exists_frickeAlgEquiv_triple_x1_xH_galois_smul_and_apply_inclusion_eq_and_forall_apply_degeneracy_eq.FrTriple"

open FrTriple in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]

    (ι : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(x1FunctionFieldBar M))
    (hι : ∀ x : ↥(xHFunctionFieldBar M H), ((ι x : ↥(x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ))) :
    ∃ (w₁ : ↥(x1FunctionFieldBar M) ≃ₐ[AlgebraicClosure ℚ] ↥(x1FunctionFieldBar M))
      (w : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (w' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),

      ((∀ (ℓ : ℕ) [Fact ℓ.Prime]
          (hα : HeckeAlphaOneBarIntegral (AlgebraicClosure ℚ) M ℓ)
          (hβ : HeckeBetaOneBarIntegral (AlgebraicClosure ℚ) M ℓ)
          [HasPrincipalDivisors (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ M (M * ℓ)))]
          (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ) hβ)
          (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ))
          (hNα : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hfinα)
          (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hα)
          (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ))
          (hNβ : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ) hfinβ)
          (x : JOne M),
        heckePic0OneBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w₁ • x)
          = SemilinearAut.ofAlgAut w₁ • heckePic0OneBar hα hβ hFIβ hfinα hNα x) ∧
      (∀ (d : ℕ) (x : JOne M),
        diamondOneBar M d (SemilinearAut.ofAlgAut w₁ • diamondOneBar M d x)
          = SemilinearAut.ofAlgAut w₁ • x) ∧
      (∀ x : JOne M, SemilinearAut.ofAlgAut w₁ • (SemilinearAut.ofAlgAut w₁ • x) = x) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ), c.Coprime M →
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) → ∀ x : JOne M,
          SemilinearAut.ofAlgAut w₁ • (σ • x)
            = σ • diamondOneBar M c (SemilinearAut.ofAlgAut w₁ • x))) ∧

      ((∀ (ℓ : ℕ) [Fact ℓ.Prime]
          (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
          (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
          [HasPrincipalDivisors (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
          (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hβ)
          (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ))
          (hNα : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hfinα)
          (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hα)
          (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ))
          (hNβ : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hfinβ)
          (x : JH M H),
        heckePic0HBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w • x)
          = SemilinearAut.ofAlgAut w • heckePic0HBar hα hβ hFIβ hfinα hNα x) ∧
      (∀ (d : (ZMod M)ˣ) (x : JH M H),
        diamondHBar M H d (SemilinearAut.ofAlgAut w • diamondHBar M H d x)
          = SemilinearAut.ofAlgAut w • x) ∧
      (∀ x : JH M H, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
          ∀ x : JH M H,
            SemilinearAut.ofAlgAut w • (σ • x)
              = σ • diamondHBar M H (ZMod.unitOfCoprime c hc) (SemilinearAut.ofAlgAut w • x))) ∧
      ((∀ (ℓ : ℕ) [Fact ℓ.Prime]
          (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ)
          (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ)
          [HasPrincipalDivisors (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * ℓ)))]
          (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ) hβ)
          (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ))
          (hNα : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ) hfinα)
          (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ) hα)
          (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ))
          (hNβ : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ) hfinβ)
          (x : JH (M / p) (infSubgroup p M H hpM)),
        heckePic0HBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w' • x)
          = SemilinearAut.ofAlgAut w' • heckePic0HBar hα hβ hFIβ hfinα hNα x) ∧
      (∀ (d : (ZMod (M / p))ˣ) (x : JH (M / p) (infSubgroup p M H hpM)),
        diamondHBar (M / p) (infSubgroup p M H hpM) d (SemilinearAut.ofAlgAut w' • diamondHBar (M / p) (infSubgroup p M H hpM) d x)
          = SemilinearAut.ofAlgAut w' • x) ∧
      (∀ x : JH (M / p) (infSubgroup p M H hpM), SemilinearAut.ofAlgAut w' • (SemilinearAut.ofAlgAut w' • x) = x) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime (M / p)),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ (M / p) = 1 → σ ζ = ζ ^ c) →
          ∀ x : JH (M / p) (infSubgroup p M H hpM),
            SemilinearAut.ofAlgAut w' • (σ • x)
              = σ • diamondHBar (M / p) (infSubgroup p M H hpM) (ZMod.unitOfCoprime c hc) (SemilinearAut.ofAlgAut w' • x))) ∧

      (∀ u : ↥(xHFunctionFieldBar M H), ι (w u) = w₁ (ι u)) ∧

      (∀ (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
          (hα : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
          (hβ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
            ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((βH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
          (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
          (hαfin : FiniteAlong (AlgebraicClosure ℚ) αH) (hβfin : FiniteAlong (AlgebraicClosure ℚ) βH)
          (hαN : NormFormulaAlong (AlgebraicClosure ℚ) αH hαfin) (hβN : NormFormulaAlong (AlgebraicClosure ℚ) βH hβfin),
        (∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), αH (w' u) = w (βH u)) ∧
          (∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), βH (w' u) = w (αH u)) ∧

          (∀ x : JH M H,
        Pic0.pushforwardAlongHom βH hβint hβfin hβN (SemilinearAut.ofAlgAut w • x)
          = SemilinearAut.ofAlgAut w' • Pic0.pushforwardAlongHom αH hαint hαfin hαN x) ∧
          (∀ x : JH M H,
        Pic0.pushforwardAlongHom αH hαint hαfin hαN (SemilinearAut.ofAlgAut w • x)
          = SemilinearAut.ofAlgAut w' • Pic0.pushforwardAlongHom βH hβint hβfin hβN x)) := by

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let ι₀ : AlgebraicClosure ℚ →+* ℂ :=
    ((IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ) : AlgebraicClosure ℚ →+* ℂ)

  obtain ⟨wH, ⟨hH1, hH2, hH3, hH4⟩, specH⟩ := exists_laws_specH M ι₀ H
  obtain ⟨w', ⟨hP1, hP2, hP3, hP4⟩, spec'⟩ := exists_laws_specH (M / p) ι₀ (infSubgroup p M H hpM)
  obtain ⟨w₁, ⟨h1, h2, h3, h4⟩, spec₁⟩ := exists_frLaws_spec_one M ι₀

  have hsq : ∀ u : xHFunctionFieldBar M H,
      ((wH u : xHFunctionFieldBar M H) : LaurentSeries Qbar) =
        ((w₁ (incl u) : x1FunctionFieldBar M) : LaurentSeries Qbar) :=
    fun u => coe_wH_eq_coe_w1 ι₀ specH spec₁ u
  refine ⟨w₁, wH, w', ⟨?_, ?_, h3, ?_⟩, ⟨hH1, hH2, hH3, hH4⟩, ⟨hP1, hP2, hP3, hP4⟩, ?_, ?_⟩
  ·
    intro ℓ _ hα hβ hPD hFIβ hfinα hNα hFIα hfinβ hNβ x
    haveI : HasPrincipalDivisors Qbar (laurentBaseChange Qbar (E0 M (Gamma1 M) ℓ)) := hPD
    exact h1 ℓ hα hβ hFIβ hfinα hNα hFIα hfinβ hNβ x
  ·
    intro d x
    by_cases hd : d.Coprime M
    · have := h2 (ZMod.unitOfCoprime d hd) x
      rwa [diaG_one_apply hd, diaG_one_apply hd] at this
    · rw [diamondOneBar_of_not_coprime hd, diamondOneBar_of_not_coprime hd]
  ·
    intro σ c hc hζ x
    have e := h4 σ c hc hζ x
    rw [diaG_one_apply hc] at e
    exact e
  ·
    have hιeq : ι = incl := eq_incl ι hι
    subst hιeq
    intro u
    exact Subtype.ext (by rw [coe_incl]; exact hsq u)
  ·
    intro αH βH hα hβ hαint hβint hαfin hβfin hαN hβN
    have hA : ∀ u, wH (αH u) = βH (w' u) := fun u => apply_alpha_eq hpM ι₀ specH spec' hα hβ u
    have hB : ∀ u, wH (βH u) = αH (w' u) := fun u => apply_beta_eq hpM ι₀ specH spec' hα hβ u
    refine ⟨fun u => (hB u).symm, fun u => (hA u).symm, fun x => ?_, fun x => ?_⟩
    ·
      have hI : CrossIntertwines αH βH (SemilinearAut.ofAlgAut w') (SemilinearAut.ofAlgAut wH) :=
        fun u => by rw [SemilinearAut.ofAlgAut_smul, SemilinearAut.ofAlgAut_smul]; exact hA u
      exact pushforwardAlongHom_cross hαint hβint hαfin hαN hβfin hβN hI x
    ·
      have hI : CrossIntertwines βH αH (SemilinearAut.ofAlgAut w') (SemilinearAut.ofAlgAut wH) :=
        fun u => by rw [SemilinearAut.ofAlgAut_smul, SemilinearAut.ofAlgAut_smul]; exact hB u
      exact pushforwardAlongHom_cross hβint hαint hβfin hβN hαfin hαN hI x

end
end S_ModularCurve_exists_frickeAlgEquiv_triple_x1_xH_galois_smul_and_apply_inclusion_eq_and_forall_apply_degeneracy_eq
end P2MW
export P2MW.S_ModularCurve_exists_frickeAlgEquiv_triple_x1_xH_galois_smul_and_apply_inclusion_eq_and_forall_apply_degeneracy_eq (solution)
