-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.whittakerCoefficient_mul_whittakerCoefficient_inv_unipotent_mul_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/10663de8-9b99-5ed4-bd2b-30b9a6cdb106

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_NumberField_IdeleProductMeasure
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_whittakerCoefficient_mul_whittakerCoefficient_inv_unipotent_mul_rat

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

noncomputable section

namespace Ws46
namespace CONVH

open NumberField.StandardAddChar NumberField.AdelicBox
open scoped Pointwise

theorem map_unipotentGL2 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x : A) :
    Matrix.GeneralLinearGroup.map f (unipotentGL2 x) = unipotentGL2 (f x) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem unipotentGL2_algebraMap (a : ℚ) :
    (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a) : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
      = globalPoints (𝓞 ℚ) ℚ (unipotentGL2 a) :=
  (map_unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) a).symm

section BoxMeasure

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

def boxMeasure : Measure (AdeleRing (𝓞 ℚ) ℚ) :=
  ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (adelicBox ℚ)

scoped instance isProbabilityMeasure_boxMeasure : IsProbabilityMeasure boxMeasure :=
  isProbabilityMeasure_cond_adelicBox ℚ

theorem productionPinsOf_ν_eq_boxMeasure (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ) :
    (productionPinsOf ℚ D U gen (adelicBox ℚ)).ν = boxMeasure := rfl

scoped instance countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
  have : (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ : Set (AdeleRing (𝓞 ℚ) ℚ))
      = Set.range (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)) := by
    ext x; exact ⟨fun ⟨a, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, ha⟩⟩
  rw [show (Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ))
      = Countable ((AdeleRing.principalSubgroup (𝓞 ℚ) ℚ : Set (AdeleRing (𝓞 ℚ) ℚ))) from rfl, this]
  exact (Set.countable_range _).to_subtype

theorem integral_boxMeasure_eq_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AdeleRing (𝓞 ℚ) ℚ → E) :
    ∫ u, f u ∂boxMeasure
      = ((NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (adelicBox ℚ))⁻¹).toReal •
          ∫ u in adelicBox ℚ, f u ∂(NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) := by
  rw [boxMeasure, ProbabilityTheory.cond, integral_smul_measure]

theorem ae_mem_adelicBox_boxMeasure : ∀ᵐ u ∂boxMeasure, u ∈ adelicBox ℚ := by
  rw [boxMeasure, ProbabilityTheory.cond]
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_adelicBox ℚ)) _

theorem integral_boxMeasure_comp_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : AdeleRing (𝓞 ℚ) ℚ → E)
    (hH : ∀ (a : ℚ) (u : AdeleRing (𝓞 ℚ) ℚ), H (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a + u) = H u)
    (w : AdeleRing (𝓞 ℚ) ℚ) :
    ∫ u, H (u + w) ∂boxMeasure = ∫ u, H u ∂boxMeasure := by
  rw [integral_boxMeasure_eq_smul, integral_boxMeasure_eq_smul]
  congr 1
  set μ := NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ with hμ
  have hmeas : MeasurableSet (adelicBox ℚ) := measurableSet_adelicBox ℚ
  have hmeas' : MeasurableSet (w +ᵥ adelicBox ℚ) := hmeas.const_vadd w
  have hind : ∀ u, (adelicBox ℚ).indicator (fun u => H (u + w)) u = (w +ᵥ adelicBox ℚ).indicator H (u + w) := by
    intro u
    by_cases hu : u ∈ adelicBox ℚ
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem]
      rw [add_comm]; exact Set.vadd_mem_vadd_set_iff.mpr hu
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem]
      rw [add_comm]; exact fun h => hu (Set.vadd_mem_vadd_set_iff.mp h)
  have hFD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (adelicBox ℚ) μ :=
    isAddFundamentalDomain_adelicBox ℚ μ
  have hFD' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (w +ᵥ adelicBox ℚ) μ :=
    hFD.vadd_of_comm w
  calc ∫ u in adelicBox ℚ, H (u + w) ∂μ
      = ∫ u, (adelicBox ℚ).indicator (fun u => H (u + w)) u ∂μ := (integral_indicator hmeas).symm
    _ = ∫ u, (w +ᵥ adelicBox ℚ).indicator H (u + w) ∂μ := by simp_rw [hind]
    _ = ∫ u, (w +ᵥ adelicBox ℚ).indicator H u ∂μ :=
        integral_add_right_eq_self (fun u => (w +ᵥ adelicBox ℚ).indicator H u) w
    _ = ∫ u in w +ᵥ adelicBox ℚ, H u ∂μ := integral_indicator hmeas'
    _ = ∫ u in adelicBox ℚ, H u ∂μ := by
        refine hFD'.setIntegral_eq hFD fun g u => ?_
        obtain ⟨_, a, rfl⟩ := g
        exact hH a u

end BoxMeasure

theorem whittakerCoefficient_unipotentGL2_mul' (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : ∀ q : ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q) = 1)
    (Φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hleft : ∀ (γ : GL (Fin 2) ℚ) (y : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ), Φ (globalPoints (𝓞 ℚ) ℚ γ * y) = Φ y)
    (α : ℚ) (w : AdeleRing (𝓞 ℚ) ℚ) (x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ Φ α (unipotentGL2 w * x)
      = ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * w)
          * whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ Φ α x := by
  set H : AdeleRing (𝓞 ℚ) ℚ → ℂ := fun u => Φ (unipotentGL2 u * x) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * u))
    with hH_def
  have hH : ∀ (a : ℚ) (u : AdeleRing (𝓞 ℚ) ℚ), H (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a + u) = H u := by
    intro a u
    rw [hH_def]
    dsimp only
    have e : -(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a)
        = algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (-(α * a)) := by rw [map_neg, map_mul]
    rw [unipotentGL2_add, unipotentGL2_algebraMap, mul_assoc, hleft, mul_add, neg_add, AddChar.map_add_eq_mul,
      e, hψ, one_mul]
  show ∫ u, Φ (unipotentGL2 u * (unipotentGL2 w * x)) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * u)) ∂boxMeasure
    = ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * w) * ∫ u, H u ∂boxMeasure
  have hpt : ∀ u, Φ (unipotentGL2 u * (unipotentGL2 w * x)) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * u))
      = H (u + w) * ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * w) := by
    intro u
    rw [hH_def]
    dsimp only
    rw [← mul_assoc, ← unipotentGL2_add, mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [hpt]
  rw [integral_mul_const, integral_boxMeasure_comp_add H hH w, mul_comm]

end Ws46.CONVH
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_whittakerCoefficient_mul_whittakerCoefficient_inv_unipotent_mul_rat.Ws46 P2MW.S_LanglandsTunnell_RankinSelberg_whittakerCoefficient_mul_whittakerCoefficient_inv_unipotent_mul_rat.Ws46.CONVH"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_whittakerCoefficient_mul_whittakerCoefficient_inv_unipotent_mul_rat.Ws46"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_whittakerCoefficient_mul_whittakerCoefficient_inv_unipotent_mul_rat.Ws46 P2MW.S_LanglandsTunnell_RankinSelberg_whittakerCoefficient_mul_whittakerCoefficient_inv_unipotent_mul_rat.Ws46.CONVH"

open Ws46.CONVH in
theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (φ φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (WA WA' FA : GL (Fin 2) ℝ → ℂ) (Wf Wf' Ff : finiteAdelicGL2Subgroup ℚ → ℂ)
    (Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (P : ℝ → ℝ) (x₀ : ℝ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (e₁ e₂ cS uS : ℝ) (tS : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (_hφc : Continuous φ) (_hφ'c : Continuous φ')
    (_hφd : IsRapidlyDecreasingOnSiegelSets ℚ φ) (_hφ'd : IsRapidlyDecreasingOnSiegelSets ℚ φ')
    (_hφG : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
    (_hφ'G : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ' (globalPoints (𝓞 ℚ) ℚ γ * g) = φ' g)
    (_hΦ : Φ ∈ schwartzBruhat2 ℚ)
    (_he₁ : 0 < e₁) (_he : e₁ < e₂) (_hcS : 0 < cS) (_hDm : MeasurableSet D)
    (_hDμ : adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ D < ⊤)
    (_hDs : D ⊆ {g | TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (_hDS : D ⊆ ⋃ t ∈ tS, (· * t) '' integralWindowedSiegelSet ℚ cS uS)
    (_hW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 g = WA (ratArchGL2 g) * Wf (finFactor g))
    (_hW' : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 g = WA' (ratArchGL2 g) * Wf' (finFactor g))
    (_hΦsplit : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Φ (bottomRowVec ℚ g 1) = FA (ratArchGL2 g) * Ff (finFactor g))
    (_hFA : ∀ g : GL (Fin 2) ℝ, FA g = Complex.exp (-(Real.pi *
        (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ)))
    (_hT : ∀ (a₁ a₂ : ℝ) (h₁ : a₁ ≠ 0) (h₂ : 0 < a₂),
      WA (upperUnit a₁ 0 a₂ h₁ h₂.ne') * WA' (upperUnit a₁ 0 a₂ h₁ h₂.ne') = ((P (a₁ / a₂) : ℝ) : ℂ))
    (_hP0 : ∀ y : ℝ, 0 ≤ P y)
    (_hPint : ∀ σ' : ℝ, x₀ < σ' → Integrable (fun y : ℝ => P y * |y| ^ (σ' - 2)))
    (_hWfm : Measurable Wf) (_hWf'm : Measurable Wf') (_hFfm : Measurable Ff)
    (_harch : @Measurable (GL (Fin 2) ℝ) ℂ (borel _) _ WA ∧ @Measurable (GL (Fin 2) ℝ) ℂ (borel _) _ WA' ∧ Measurable P ∧
      (∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, WA (n * g) * WA' (n * g) = WA g * WA' g) ∧
      (∀ κ' ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det κ' = 1 →
        ∀ g : GL (Fin 2) ℝ, WA (g * κ') * WA' (g * κ') = WA g * WA' g))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (lam om lam' om' : HeightOneSpectrum (𝓞 ℚ) → ℂ) (κ : ℝ)
    (_hfin :
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ‖lam v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖lam' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ) ∧
      (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
        Wf ((n : finiteAdelicGL2Subgroup ℚ) * g) * (Wf' ((n : finiteAdelicGL2Subgroup ℚ) * g) * Ff ((n : finiteAdelicGL2Subgroup ℚ) * g)) =
          Wf g * (Wf' g * Ff g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
        (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
        (∃ r : v.adicCompletionIntegers ℚ,
          ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
            algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
        ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → Wf (finFactor (g * placeEmbed ℚ v x)) = Wf (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ →
          Wf' (finFactor (g * placeEmbed ℚ v x)) * Ff (finFactor (g * placeEmbed ℚ v x)) = Wf' (finFactor g) * Ff (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∀ hv : v ∉ S, ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m n : ℤ), localAt ℚ v g = 1 →
        Wf (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n))) *
          (Wf' (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n))) *
            Ff (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n)))) =
        (if 0 ≤ m ∧ 0 ≤ n then
          (om v * om' v) ^ n.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam v) (om v) m.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam' v) (om' v) m.toNat
         else 0) * (Wf (finFactor g) * (Wf' (finFactor g) * Ff (finFactor g)))))
    (_hsupp :
      (∃ (Cpt : Set (finiteAdelicGL2Subgroup ℚ)) (B₀ : ℝ), IsCompact Cpt ∧
        (∀ g : finiteAdelicGL2Subgroup ℚ, ‖Wf g * (Wf' g * Ff g)‖ ≤ B₀) ∧
        ∀ g : finiteAdelicGL2Subgroup ℚ,
          (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
          Wf g * (Wf' g * Ff g) ≠ 0 →
            ∃ (n : RSCarrier.finUnipotent) (h : finiteAdelicGL2Subgroup ℚ), h ∈ Cpt ∧
              ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S →
                localAt ℚ v ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
                  localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ)))
    :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    (∀ (n : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) *
          whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) =
        whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 g *
          whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 g) := by
  intro n g
  obtain ⟨w, hw⟩ := n.2
  have hn : (n : AdelicGL2 (𝓞 ℚ) ℚ) = unipotentGL2 (Multiplicative.toAdd w) := by rw [← hw]; rfl
  rw [hn]
  have h1 := whittakerCoefficient_unipotentGL2_mul' (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
    NumberField.StandardAddChar.psiQ NumberField.StandardAddChar.psiQ_algebraMap φ _hφG 1 (Multiplicative.toAdd w) g
  have h2 := whittakerCoefficient_unipotentGL2_mul' (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
    NumberField.StandardAddChar.psiQ⁻¹ (fun q => by rw [AddChar.inv_apply, ← map_neg, NumberField.StandardAddChar.psiQ_algebraMap]) φ' _hφ'G 1
    (Multiplicative.toAdd w) g
  rw [h1, h2, map_one, one_mul, AddChar.inv_apply]
  have : NumberField.StandardAddChar.psiQ (Multiplicative.toAdd w) * NumberField.StandardAddChar.psiQ (-Multiplicative.toAdd w) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  calc NumberField.StandardAddChar.psiQ (Multiplicative.toAdd w) * whittakerCoefficient ℚ _ NumberField.StandardAddChar.psiQ φ 1 g *
        (NumberField.StandardAddChar.psiQ (-Multiplicative.toAdd w) * whittakerCoefficient ℚ _ NumberField.StandardAddChar.psiQ⁻¹ φ' 1 g)
      = (NumberField.StandardAddChar.psiQ (Multiplicative.toAdd w) * NumberField.StandardAddChar.psiQ (-Multiplicative.toAdd w)) *
        (whittakerCoefficient ℚ _ NumberField.StandardAddChar.psiQ φ 1 g * whittakerCoefficient ℚ _ NumberField.StandardAddChar.psiQ⁻¹ φ' 1 g) := by ring
    _ = _ := by rw [this, one_mul]

end S_LanglandsTunnell_RankinSelberg_whittakerCoefficient_mul_whittakerCoefficient_inv_unipotent_mul_rat
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_whittakerCoefficient_mul_whittakerCoefficient_inv_unipotent_mul_rat (solution)
