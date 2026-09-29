-- Prove2me | solution 1 for LanglandsTunnell.exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e618f6a3-03f4-5526-94eb-8973b675faf1

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_finprod_eq_finprod_prod_extension
import Theorems.Thm_LanglandsTunnell_Converse_conductorExponentAt_localChar_eq_zero_of_isUnramifiedCharAt
import Theorems.Thm_LanglandsTunnell_Converse_finite_setOf_pinnedExp_ne_zero_of_continuous
import Theorems.Thm_LanglandsTunnell_Converse_hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt
import Theorems.Thm_LanglandsTunnell_HeckeTate_exists_archRootNumber_induced_of_finrank_eq_two
import Theorems.Thm_LanglandsTunnell_HeckeTate_finite_setOf_stdRootNumberAt_ne_one_and_finite_setOf_pinnedExp_ne_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_TateLocal_hasConductorExponentAt_comp_norm_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_hasConductorExponentAt_mul_of_hasConductorExponentAt_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_two
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_hasConductorExponentAt_zero
import Theorems.Thm_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
import Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
import Theorems.Thm_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
import Theorems.Thm_NumberField_TateGlobal_continuous_localChar
import Theorems.Thm_NumberField_TateGlobal_localChar_mul_comp_idelicNorm_genuineBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers"

set_option autoImplicit false

p2m_open "NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter LanglandsTunnell P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.HeckeTate M4aHerbrand.GenuineDescent"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.finiteConductor Converse.pinnedRootNumber TateLocal.addCharLevel TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt TateLocal.conductorExponentAt_one signEpsilon RealArchParam ComplexArchParam RealArchParam.oddArtin ComplexArchParam.trivialArtin HeckeTate.heckeRootNumber HeckeTate.heckeConductor Converse.finite_setOf_pinnedExp_ne_zero_of_continuous Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt HeckeTate.exists_archRootNumber_induced_of_finrank_eq_two HeckeTate.finite_setOf_stdRootNumberAt_ne_one_and_finite_setOf_pinnedExp_ne_zero TateLocal.addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one TateLocal.exists_hasConductorExponentAt_of_continuous TateLocal.hasConductorExponentAt_comp_norm_zero TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_zero TateLocal.psiLocal_ne_one TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_two TateLocal.stdRootNumberAt_mul_of_hasConductorExponentAt_zero"
namespace P2ind
p2m_open "LanglandsTunnell"

variable (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]

noncomputable def kOf (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 E))) : ↥S → ℤ := fun v =>
  letI := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 E) E M (𝓞 M) v.1
  ∑ w : v.1.Extension (𝓞 M),
    (v.1.asIdeal.inertiaDeg' w.1.asIdeal : ℤ) *
      ((LanglandsTunnell.TateLocal.conductorExponentAt M w.1 (localChar ξ w.1) : ℤ) +
        LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal M w.1))

noncomputable def cS (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 E))) : ℂ :=
  ∏ v : ↥S,
    letI := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 E) E M (𝓞 M) v.1
    ∏ w : v.1.Extension (𝓞 M), LanglandsTunnell.TateLocal.stdRootNumberAt M w.1 (localChar ξ w.1)

open scoped Classical in

noncomputable def cI (S : Finset (HeightOneSpectrum (𝓞 E))) : ℂ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 E),
    if v ∈ S then 1 else
      if (∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) = v ∧ v.asIdeal.inertiaDeg' w.asIdeal = 2)
      then (-1 : ℂ) ^ (LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal E v)).natAbs else 1

end LanglandsTunnell.P2ind

set_option autoImplicit false

p2m_open "NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter LanglandsTunnell P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.HeckeTate M4aHerbrand.GenuineDescent"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.finiteConductor Converse.pinnedRootNumber TateLocal.addCharLevel TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt TateLocal.conductorExponentAt_one signEpsilon RealArchParam ComplexArchParam RealArchParam.oddArtin ComplexArchParam.trivialArtin HeckeTate.heckeRootNumber HeckeTate.heckeConductor Converse.finite_setOf_pinnedExp_ne_zero_of_continuous Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt HeckeTate.exists_archRootNumber_induced_of_finrank_eq_two HeckeTate.finite_setOf_stdRootNumberAt_ne_one_and_finite_setOf_pinnedExp_ne_zero TateLocal.addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one TateLocal.exists_hasConductorExponentAt_of_continuous TateLocal.hasConductorExponentAt_comp_norm_zero TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_zero TateLocal.psiLocal_ne_one TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_two TateLocal.stdRootNumberAt_mul_of_hasConductorExponentAt_zero"
namespace P2ind
namespace CondAux
p2m_open "LanglandsTunnell"

open IsDedekindDomain.HeightOneSpectrum LanglandsTunnell.TateLocal NumberField.StandardAddChar

variable (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]

theorem prod_zpow_eq_zpow_sum {ι : Type} (s : Finset ι) (a : ℝ) (ha : a ≠ 0) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ ha]

scoped instance liesOver_extension (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M)) : w.1.asIdeal.LiesOver v.asIdeal := by
  constructor
  have h := congrArg (fun x : HeightOneSpectrum (𝓞 E) => x.asIdeal) w.2
  exact h.symm

theorem absNorm_eq_pow_inertiaDeg_extension (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M)) :
    (Ideal.absNorm w.1.asIdeal : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ v.asIdeal.inertiaDeg' w.1.asIdeal := by
  have h := Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver w.1.asIdeal v.asIdeal v.isPrime v.ne_bot
  exact_mod_cast h

theorem absNorm_ne_zero (v : HeightOneSpectrum (𝓞 E)) : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast this

theorem exists_hasConductorExponentAt_localChar (K : Type) [Field K] [NumberField K] (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχ : Continuous χ) (v : HeightOneSpectrum (𝓞 K)) : ∃ c : ℕ, HasConductorExponentAt K v (localChar χ v) c :=
  LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous K v (localChar χ v)
    (NumberField.TateGlobal.continuous_localChar χ hχ v)

theorem sum_inertiaDeg_eq_two (h2 : Module.finrank E M = 2) (v : HeightOneSpectrum (𝓞 E))
    (hram : ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = v → v.asIdeal.ramificationIdx' w'.asIdeal = 1) :
    (letI := Extension.fintype (𝓞 E) E M (𝓞 M) v; ∑ w : v.Extension (𝓞 M), (v.asIdeal.inertiaDeg' w.1.asIdeal : ℤ)) = 2 := by
  letI := Extension.fintype (𝓞 E) E M (𝓞 M) v
  have h := Ideal.sum_ramification_inertia_extensions (𝓞 E) E M (𝓞 M) v
  rw [h2] at h
  have h' : ∑ w : v.Extension (𝓞 M), v.asIdeal.inertiaDeg' w.1.asIdeal = 2 := by
    rw [← h]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [hram w.1 w.2, one_mul]
  exact_mod_cast h'

theorem inertiaDeg_eq_one_or_two (h2 : Module.finrank E M = 2) (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) :
    v.asIdeal.inertiaDeg' w.1.asIdeal = 1 ∨ v.asIdeal.inertiaDeg' w.1.asIdeal = 2 := by
  letI := Extension.fintype (𝓞 E) E M (𝓞 M) v
  have h := Ideal.sum_ramification_inertia_extensions (𝓞 E) E M (𝓞 M) v
  rw [h2] at h
  have hle : v.asIdeal.ramificationIdx' w.1.asIdeal * v.asIdeal.inertiaDeg' w.1.asIdeal ≤ 2 := by
    rw [← h]
    exact Finset.single_le_sum (f := fun w : v.Extension (𝓞 M) => v.asIdeal.ramificationIdx' w.1.asIdeal * v.asIdeal.inertiaDeg' w.1.asIdeal)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
  rw [he, one_mul] at hle
  haveI := v.isMaximal
  have hf : 0 < v.asIdeal.inertiaDeg' w.1.asIdeal := Ideal.inertiaDeg'_pos v.asIdeal w.1.asIdeal
  omega

end LanglandsTunnell.P2ind.CondAux
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell.P2ind P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell.P2ind.CondAux"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell.P2ind"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell"

namespace LanglandsTunnell p2m_export "LanglandsTunnell" "Converse.finiteConductor Converse.pinnedRootNumber TateLocal.addCharLevel TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt TateLocal.conductorExponentAt_one signEpsilon RealArchParam ComplexArchParam RealArchParam.oddArtin ComplexArchParam.trivialArtin HeckeTate.heckeRootNumber HeckeTate.heckeConductor Converse.finite_setOf_pinnedExp_ne_zero_of_continuous Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt HeckeTate.exists_archRootNumber_induced_of_finrank_eq_two HeckeTate.finite_setOf_stdRootNumberAt_ne_one_and_finite_setOf_pinnedExp_ne_zero TateLocal.addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one TateLocal.exists_hasConductorExponentAt_of_continuous TateLocal.hasConductorExponentAt_comp_norm_zero TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_zero TateLocal.psiLocal_ne_one TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_two TateLocal.stdRootNumberAt_mul_of_hasConductorExponentAt_zero" namespace P2ind end LanglandsTunnell.P2ind
p2m_open_scoped "LanglandsTunnell" in
open LanglandsTunnell.P2ind LanglandsTunnell.P2ind.CondAux IsDedekindDomain.HeightOneSpectrum LanglandsTunnell.TateLocal NumberField.StandardAddChar in
theorem LanglandsTunnell.P2ind.heckeConductor_eq
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    (Pi : HeckeEigensystem E ℂ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS₀ : ∀ w' ∈ S₀, w'.under (𝓞 E) ∈ S)
    (hram : ∀ v ∉ S, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = v →
      v.asIdeal.ramificationIdx' w'.asIdeal = 1)
    (hPi : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ S →
      (∀ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' → w'.under (𝓞 E) = w → w''.under (𝓞 E) = w →
        Pi.a w = (ξ (uniformizerIdele M w') : ℂ) + ξ (uniformizerIdele M w'') ∧
        Pi.b w = (ξ (uniformizerIdele M w') : ℂ) * ξ (uniformizerIdele M w'')) ∧
      (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → w.asIdeal.inertiaDeg' w'.asIdeal = 2 →
        Pi.a w = 0 ∧ Pi.b w = -(ξ (uniformizerIdele M w') : ℂ)))
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist E μ) (hμS : ∀ v ∈ S, IsUnramifiedCharAt μ v) :
    heckeConductor M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) =
      finiteConductor E μ S * ∏ v : ↥S, (Ideal.absNorm v.1.asIdeal : ℝ) ^ (kOf E M ξ S v) := by
  classical
  set N := (genuineBaseChange E M).idelicNorm with hN
  set lam : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ := ξ * μ.comp N with hlam
  have hcontN : Continuous N := by
    rw [hN]
    exact Continuous.units_map _ (M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange E M)
  have hcont : Continuous lam := by
    rw [hlam]
    show Continuous (fun x => ξ x * μ (N x))
    exact hξ.continuous.mul (hμ.2.1.comp hcontN)
  set q : HeightOneSpectrum (𝓞 E) → ℝ := fun v => (Ideal.absNorm v.asIdeal : ℝ) with hq
  set P : HeightOneSpectrum (𝓞 M) → ℤ := fun w => pinnedExp M lam w with hP

  have hP_out : ∀ v ∉ S, ∀ w : v.Extension (𝓞 M), P w.1 = pinnedExp E μ v := by
    intro v hv w
    have hG1 : localChar lam w.1 = localChar ξ w.1 * (localChar μ v).comp (Units.map (Algebra.norm (v.adicCompletion E))) := by
      rw [hlam, hN]
      exact NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange E M ξ μ v w

    have hw0 : w.1 ∉ S₀ := fun h => hv (w.2 ▸ hS₀ w.1 h)
    have hξ0 : HasConductorExponentAt M w.1 (localChar ξ w.1) 0 :=
      LanglandsTunnell.Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt M ξ w.1 (hunr w.1 hw0)

    obtain ⟨a, ha⟩ := exists_hasConductorExponentAt_localChar E μ hμ.2.1 v
    have he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1 := hram v hv w.1 w.2
    have hunit : ‖((localChar μ v (NumberField.AdelicLevel.uniformizerUnit E v) : ℂˣ) : ℂ)‖ = 1 := hμ.2.2 _
    have hχ : HasConductorExponentAt M w.1 ((localChar μ v).comp (Units.map (Algebra.norm (v.adicCompletion E)))) a := by
      rcases inertiaDeg_eq_one_or_two E M h2 v w he with hf | hf
      · exact (LanglandsTunnell.TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one E M v w he hf (localChar μ v) a ha hunit).1
      · exact (LanglandsTunnell.TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_two E M v w he hf (localChar μ v) a ha hunit).1
    have hlamw : HasConductorExponentAt M w.1 (localChar lam w.1) a := by
      have hcomm : localChar ξ w.1 * (localChar μ v).comp (Units.map (Algebra.norm (v.adicCompletion E))) =
          (localChar μ v).comp (Units.map (Algebra.norm (v.adicCompletion E))) * localChar ξ w.1 :=
        MonoidHom.ext (fun x => mul_comm _ _)
      rw [hG1, hcomm]
      exact LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_zero M w.1 _ _ a hχ hξ0
    have hlev : addCharLevel (psiLocal M w.1) = addCharLevel (psiLocal E v) :=
      LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one E M v w he
    simp only [hP, pinnedExp]
    rw [conductorExponentAt_eq_of_hasConductorExponentAt M w.1 hlamw, conductorExponentAt_eq_of_hasConductorExponentAt E v ha, hlev]
  have hP_in : ∀ v ∈ S, ∀ w : v.Extension (𝓞 M), P w.1 =
      (conductorExponentAt M w.1 (localChar ξ w.1) : ℤ) + addCharLevel (psiLocal M w.1) := by
    intro v hv w

    have hG1 : localChar lam w.1 = localChar ξ w.1 * (localChar μ v).comp (Units.map (Algebra.norm (v.adicCompletion E))) := by
      rw [hlam, hN]
      exact NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange E M ξ μ v w
    obtain ⟨a, ha⟩ := exists_hasConductorExponentAt_localChar M ξ hξ.continuous w.1
    have hω : HasConductorExponentAt M w.1 ((localChar μ v).comp (Units.map (Algebra.norm (v.adicCompletion E)))) 0 :=
      LanglandsTunnell.TateLocal.hasConductorExponentAt_comp_norm_zero E M v w (localChar μ v)
        (LanglandsTunnell.Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt E μ v (hμS v hv))
    have hlamw : HasConductorExponentAt M w.1 (localChar lam w.1) a := by
      rw [hG1]
      exact LanglandsTunnell.TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_zero M w.1 _ _ a ha hω
    simp only [hP, pinnedExp]
    rw [conductorExponentAt_eq_of_hasConductorExponentAt M w.1 hlamw, conductorExponentAt_eq_of_hasConductorExponentAt M w.1 ha]

  have hfinM : (Function.mulSupport fun w : HeightOneSpectrum (𝓞 M) => (Ideal.absNorm w.asIdeal : ℝ) ^ P w).Finite := by
    refine (LanglandsTunnell.Converse.finite_setOf_pinnedExp_ne_zero_of_continuous M lam hcont).subset ?_
    intro w hw
    simp only [Function.mem_mulSupport] at hw
    simp only [Set.mem_setOf_eq]
    intro h0; apply hw; simp [hP, h0]
  have hL : heckeConductor M lam = ∏ᶠ v : HeightOneSpectrum (𝓞 E),
      (letI := Extension.fintype (𝓞 E) E M (𝓞 M) v; ∏ w : v.Extension (𝓞 M), (Ideal.absNorm w.1.asIdeal : ℝ) ^ P w.1) := by
    unfold heckeConductor
    exact IsDedekindDomain.HeightOneSpectrum.finprod_eq_finprod_prod_extension E M (fun w => (Ideal.absNorm w.asIdeal : ℝ) ^ P w) hfinM

  set F : HeightOneSpectrum (𝓞 E) → ℝ := fun v =>
    if h : v ∈ S then q v ^ (kOf E M ξ S ⟨v, h⟩) else q v ^ (2 * pinnedExp E μ v) with hF
  have hfib : ∀ v : HeightOneSpectrum (𝓞 E),
      (letI := Extension.fintype (𝓞 E) E M (𝓞 M) v; ∏ w : v.Extension (𝓞 M), (Ideal.absNorm w.1.asIdeal : ℝ) ^ P w.1) = F v := by
    intro v
    letI := Extension.fintype (𝓞 E) E M (𝓞 M) v

    have hstep : ∀ w : v.Extension (𝓞 M), (Ideal.absNorm w.1.asIdeal : ℝ) ^ P w.1 = q v ^ ((v.asIdeal.inertiaDeg' w.1.asIdeal : ℤ) * P w.1) := by
      intro w
      rw [absNorm_eq_pow_inertiaDeg_extension E M v w, ← zpow_natCast, ← zpow_mul]
    rw [Finset.prod_congr rfl (fun w _ => hstep w), prod_zpow_eq_zpow_sum _ _ (absNorm_ne_zero E v)]
    by_cases hv : v ∈ S
    · simp only [hF, dif_pos hv]
      congr 1
      simp only [kOf]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [hP_in v hv w]
    · simp only [hF, dif_neg hv]
      congr 1
      rw [Finset.sum_congr rfl (fun w _ => by rw [hP_out v hv w]), ← Finset.sum_mul,
        sum_inertiaDeg_eq_two E M h2 v (hram v hv)]

  have hR : finiteConductor E μ S * ∏ v : ↥S, (Ideal.absNorm v.1.asIdeal : ℝ) ^ (kOf E M ξ S v) = ∏ᶠ v, F v := by
    set A : HeightOneSpectrum (𝓞 E) → ℝ := fun v => if v ∈ S then 1 else q v ^ (2 * pinnedExp E μ v) with hA
    set B : HeightOneSpectrum (𝓞 E) → ℝ := fun v => if h : v ∈ S then q v ^ (kOf E M ξ S ⟨v, h⟩) else 1 with hB
    have hfinA : (Function.mulSupport A).Finite := by
      refine (LanglandsTunnell.Converse.finite_setOf_pinnedExp_ne_zero_of_continuous E μ hμ.2.1).subset ?_
      intro v hv
      simp only [Function.mem_mulSupport, hA] at hv
      simp only [Set.mem_setOf_eq]
      intro h0; apply hv
      by_cases hvS : v ∈ S
      · simp [hvS]
      · simp [hvS, h0]
    have hfinB : (Function.mulSupport B).Finite := by
      refine (S.finite_toSet).subset ?_
      intro v hv
      simp only [Function.mem_mulSupport, hB] at hv
      by_contra hvS
      exact hv (by simp [Finset.mem_coe.not.mp hvS])
    have h1 : finiteConductor E μ S = ∏ᶠ v, A v := by
      unfold finiteConductor
      refine finprod_congr (fun v => ?_)
      by_cases hvS : v ∈ S <;> simp [hA, hvS, hq]
    have h2' : ∏ v : ↥S, (Ideal.absNorm v.1.asIdeal : ℝ) ^ (kOf E M ξ S v) = ∏ᶠ v, B v := by
      rw [finprod_eq_prod_of_mulSupport_subset B (s := S) (by
        intro v hv
        simp only [Function.mem_mulSupport, hB] at hv
        by_contra hvS
        exact hv (by simp [Finset.mem_coe.not.mp hvS]))]
      rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl (fun v _ => ?_)
      simp [hB, hq, dif_pos v.2]
    rw [h1, h2', ← finprod_mul_distrib hfinA hfinB]
    refine finprod_congr (fun v => ?_)
    by_cases hvS : v ∈ S <;> simp [hA, hB, hF, hvS]
  rw [hL, hR]
  exact finprod_congr hfib

set_option autoImplicit false

p2m_open "NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter LanglandsTunnell P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.HeckeTate M4aHerbrand.GenuineDescent"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.finiteConductor Converse.pinnedRootNumber TateLocal.addCharLevel TateLocal.stdRootNumberAt TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt TateLocal.conductorExponentAt_one signEpsilon RealArchParam ComplexArchParam RealArchParam.oddArtin ComplexArchParam.trivialArtin HeckeTate.heckeRootNumber HeckeTate.heckeConductor Converse.finite_setOf_pinnedExp_ne_zero_of_continuous Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt HeckeTate.exists_archRootNumber_induced_of_finrank_eq_two HeckeTate.finite_setOf_stdRootNumberAt_ne_one_and_finite_setOf_pinnedExp_ne_zero TateLocal.addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one TateLocal.exists_hasConductorExponentAt_of_continuous TateLocal.hasConductorExponentAt_comp_norm_zero TateLocal.hasConductorExponentAt_mul_of_hasConductorExponentAt_zero TateLocal.psiLocal_ne_one TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_two TateLocal.stdRootNumberAt_mul_of_hasConductorExponentAt_zero"
namespace P2ind
namespace OffSAux
p2m_open "LanglandsTunnell"

open IsDedekindDomain.HeightOneSpectrum LanglandsTunnell.TateLocal NumberField.StandardAddChar

variable (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]

scoped instance liesOver_extension' (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M)) : w.1.asIdeal.LiesOver v.asIdeal := by
  constructor
  have h := congrArg (fun x : HeightOneSpectrum (𝓞 E) => x.asIdeal) w.2
  exact h.symm

theorem inertiaDeg_pos_ext (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M)) : 0 < v.asIdeal.inertiaDeg' w.1.asIdeal := by
  haveI := v.isMaximal
  exact Ideal.inertiaDeg'_pos v.asIdeal w.1.asIdeal

theorem inertiaDeg_eq_one_or_two' (h2 : Module.finrank E M = 2) (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1) :
    v.asIdeal.inertiaDeg' w.1.asIdeal = 1 ∨ v.asIdeal.inertiaDeg' w.1.asIdeal = 2 := by
  letI := Extension.fintype (𝓞 E) E M (𝓞 M) v
  have h := Ideal.sum_ramification_inertia_extensions (𝓞 E) E M (𝓞 M) v
  rw [h2] at h
  have hle : v.asIdeal.ramificationIdx' w.1.asIdeal * v.asIdeal.inertiaDeg' w.1.asIdeal ≤ 2 := by
    rw [← h]
    exact Finset.single_le_sum (f := fun w : v.Extension (𝓞 M) => v.asIdeal.ramificationIdx' w.1.asIdeal * v.asIdeal.inertiaDeg' w.1.asIdeal)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
  rw [he, one_mul] at hle
  have hf := inertiaDeg_pos_ext E M v w
  omega

open scoped Classical in

theorem fibre_split_or_inert (h2 : Module.finrank E M = 2) (v : HeightOneSpectrum (𝓞 E))
    (hram : ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = v → v.asIdeal.ramificationIdx' w'.asIdeal = 1) :
    letI := Extension.fintype (𝓞 E) E M (𝓞 M) v
    (∃ w₁ w₂ : v.Extension (𝓞 M), w₁ ≠ w₂ ∧ (∀ w : v.Extension (𝓞 M), w = w₁ ∨ w = w₂) ∧
        v.asIdeal.inertiaDeg' w₁.1.asIdeal = 1 ∧ v.asIdeal.inertiaDeg' w₂.1.asIdeal = 1) ∨
    (∃ w₀ : v.Extension (𝓞 M), (∀ w : v.Extension (𝓞 M), w = w₀) ∧ v.asIdeal.inertiaDeg' w₀.1.asIdeal = 2) := by
  classical
  letI := Extension.fintype (𝓞 E) E M (𝓞 M) v
  have h := Ideal.sum_ramification_inertia_extensions (𝓞 E) E M (𝓞 M) v
  rw [h2] at h
  have hsum : ∑ w : v.Extension (𝓞 M), v.asIdeal.inertiaDeg' w.1.asIdeal = 2 := by
    rw [← h]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [hram w.1 w.2, one_mul]
  by_cases hex : ∃ w₀ : v.Extension (𝓞 M), v.asIdeal.inertiaDeg' w₀.1.asIdeal = 2
  · obtain ⟨w₀, hw₀⟩ := hex
    refine Or.inr ⟨w₀, fun w => ?_, hw₀⟩
    by_contra hne
    have hpair : ∑ x ∈ ({w₀, w} : Finset (v.Extension (𝓞 M))), v.asIdeal.inertiaDeg' x.1.asIdeal ≤ 2 := by
      rw [← hsum]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [Finset.sum_pair (Ne.symm hne)] at hpair
    have := inertiaDeg_pos_ext E M v w
    omega
  · push Not at hex
    have hall : ∀ w : v.Extension (𝓞 M), v.asIdeal.inertiaDeg' w.1.asIdeal = 1 := fun w =>
      (inertiaDeg_eq_one_or_two' E M h2 v w (hram w.1 w.2)).resolve_right (hex w)
    have hcard : (Finset.univ : Finset (v.Extension (𝓞 M))).card = 2 := by
      have : ∑ w : v.Extension (𝓞 M), (1 : ℕ) = 2 := by
        rw [← hsum]; exact Finset.sum_congr rfl (fun w _ => (hall w).symm)
      simpa using this
    obtain ⟨w₁, w₂, hne, huniv⟩ := Finset.card_eq_two.mp hcard
    refine Or.inl ⟨w₁, w₂, hne, fun w => ?_, hall w₁, hall w₂⟩
    have hm : w ∈ (Finset.univ : Finset (v.Extension (𝓞 M))) := Finset.mem_univ _
    rw [huniv] at hm
    rcases Finset.mem_insert.mp hm with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)

private theorem _root_.LanglandsTunnell.P2ind.OffSAux.norm_apply_eq_one_of_isOfFinOrder {G : Type} [Group G] (χ : G →* ℂˣ) (hχ : IsOfFinOrder χ) (x : G) :
    ‖((χ x : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hχn⟩ := hχ.exists_pow_eq_one
  have h1 : ((χ x : ℂˣ) : ℂ) ^ n = 1 := by
    have := congrArg (fun f : G →* ℂˣ => ((f x : ℂˣ) : ℂ)) hχn
    simpa using this
  have h2 : ‖((χ x : ℂˣ) : ℂ)‖ ^ n = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h2

p2m_export "LanglandsTunnell.P2ind.OffSAux" "norm_apply_eq_one_of_isOfFinOrder"
theorem neg_one_pow_natAbs (n : ℤ) : ((-1 : ℂ)) ^ n.natAbs = (-1 : ℂ) ^ n := by
  rcases Int.natAbs_eq n with h | h
  · conv_rhs => rw [h]
    rw [zpow_natCast]
  · conv_rhs => rw [h]
    rw [zpow_neg, zpow_natCast]
    rcases neg_one_pow_eq_or ℂ n.natAbs with h' | h' <;> simp [h']

end LanglandsTunnell.P2ind.OffSAux
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell.P2ind P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell.P2ind.CondAux P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell.P2ind.OffSAux"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell.P2ind P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell.P2ind.CondAux"
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell.P2ind P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell.P2ind.CondAux"

p2m_open_scoped "LanglandsTunnell" in
open LanglandsTunnell.P2ind LanglandsTunnell.P2ind.OffSAux IsDedekindDomain.HeightOneSpectrum LanglandsTunnell.TateLocal NumberField.StandardAddChar in
open scoped Classical in

theorem LanglandsTunnell.P2ind.prod_extension_stdRootNumberAt_off_S
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    (Pi : HeckeEigensystem E ℂ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS₀ : ∀ w' ∈ S₀, w'.under (𝓞 E) ∈ S)
    (hram : ∀ v ∉ S, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = v →
      v.asIdeal.ramificationIdx' w'.asIdeal = 1)
    (hPi : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ S →
      (∀ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' → w'.under (𝓞 E) = w → w''.under (𝓞 E) = w →
        Pi.a w = (ξ (uniformizerIdele M w') : ℂ) + ξ (uniformizerIdele M w'') ∧
        Pi.b w = (ξ (uniformizerIdele M w') : ℂ) * ξ (uniformizerIdele M w'')) ∧
      (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → w.asIdeal.inertiaDeg' w'.asIdeal = 2 →
        Pi.a w = 0 ∧ Pi.b w = -(ξ (uniformizerIdele M w') : ℂ)))
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist E μ)
    (v : HeightOneSpectrum (𝓞 E)) (hv : v ∉ S) :
    (letI := Extension.fintype (𝓞 E) E M (𝓞 M) v;
      ∏ w : v.Extension (𝓞 M), stdRootNumberAt M w.1 (localChar (ξ * μ.comp (genuineBaseChange E M).idelicNorm) w.1)) =
    (if (∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) = v ∧ v.asIdeal.inertiaDeg' w.asIdeal = 2)
      then (-1 : ℂ) ^ (addCharLevel (psiLocal E v)).natAbs else 1) * goodPlaceRootNumber E Pi μ v := by
  classical
  letI := Extension.fintype (𝓞 E) E M (𝓞 M) v
  set lam := ξ * μ.comp (genuineBaseChange E M).idelicNorm with hlam

  set χw : ∀ w : v.Extension (𝓞 M), (w.1.adicCompletion M)ˣ →* ℂˣ :=
    fun w => (localChar μ v).comp (Units.map (Algebra.norm (v.adicCompletion E))) with hχw
  have hG1 : ∀ w : v.Extension (𝓞 M), localChar lam w.1 = χw w * localChar ξ w.1 := by
    intro w
    rw [hlam, NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange E M ξ μ v w]
    exact MonoidHom.ext (fun x => mul_comm _ _)

  obtain ⟨a, ha⟩ : ∃ a : ℕ, HasConductorExponentAt E v (localChar μ v) a :=
    LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous E v (localChar μ v)
      (NumberField.TateGlobal.continuous_localChar μ hμ.2.1 v)
  have hpe : pinnedExp E μ v = (a : ℤ) + addCharLevel (psiLocal E v) := by
    simp only [pinnedExp, conductorExponentAt_eq_of_hasConductorExponentAt E v ha]
  have hunitμ : ‖((localChar μ v (NumberField.AdelicLevel.uniformizerUnit E v) : ℂˣ) : ℂ)‖ = 1 := hμ.2.2 _

  have he : ∀ w : v.Extension (𝓞 M), v.asIdeal.ramificationIdx' w.1.asIdeal = 1 := fun w => hram v hv w.1 w.2
  have hξ0 : ∀ w : v.Extension (𝓞 M), HasConductorExponentAt M w.1 (localChar ξ w.1) 0 := fun w =>
    LanglandsTunnell.Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt M ξ w.1
      (hunr w.1 (fun h => hv (w.2 ▸ hS₀ w.1 h)))
  have hunitχ : ∀ w : v.Extension (𝓞 M), ‖((χw w (NumberField.AdelicLevel.uniformizerUnit M w.1) : ℂˣ) : ℂ)‖ = 1 :=
    fun w => hμ.2.2 _
  have hunitξ : ∀ w : v.Extension (𝓞 M), ‖((localChar ξ w.1 (NumberField.AdelicLevel.uniformizerUnit M w.1) : ℂˣ) : ℂ)‖ = 1 :=
    fun w => norm_apply_eq_one_of_isOfFinOrder ξ hξ.isOfFinOrder _
  have hlev : ∀ w : v.Extension (𝓞 M), addCharLevel (psiLocal M w.1) = addCharLevel (psiLocal E v) := fun w =>
    LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_of_ramificationIdx_eq_one E M v w (he w)
  have hϖ : ∀ w : v.Extension (𝓞 M), ((localChar ξ w.1 (NumberField.AdelicLevel.uniformizerUnit M w.1) : ℂˣ) : ℂ) =
      (ξ (uniformizerIdele M w.1) : ℂ) := fun w => rfl

  have htwist : ∀ w : v.Extension (𝓞 M), HasConductorExponentAt M w.1 (χw w) a →
      stdRootNumberAt M w.1 (localChar lam w.1) =
        (ξ (uniformizerIdele M w.1) : ℂ) ^ ((a : ℤ) + addCharLevel (psiLocal E v)) * stdRootNumberAt M w.1 (χw w) := by
    intro w hχ
    rw [hG1 w, LanglandsTunnell.TateLocal.stdRootNumberAt_mul_of_hasConductorExponentAt_zero M w.1 (χw w) (localChar ξ w.1) a
      hχ (hξ0 w) (hunitχ w) (hunitξ w) (LanglandsTunnell.TateLocal.psiLocal_ne_one M w.1), hϖ w, hlev w]

  rcases fibre_split_or_inert E M h2 v (hram v hv) with ⟨w₁, w₂, hne, hall, hf₁, hf₂⟩ | ⟨w₀, hall, hf₀⟩
  ·
    have huniv : (Finset.univ : Finset (v.Extension (𝓞 M))) = {w₁, w₂} := by
      ext w
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      exact hall w
    have hn1 := LanglandsTunnell.TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one E M v w₁ (he w₁) hf₁ (localChar μ v) a ha hunitμ
    have hn2 := LanglandsTunnell.TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_one E M v w₂ (he w₂) hf₂ (localChar μ v) a ha hunitμ
    have hno2 : ¬ (∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) = v ∧ v.asIdeal.inertiaDeg' w.asIdeal = 2) := by
      rintro ⟨w, hw, hf⟩
      rcases hall ⟨w, hw⟩ with h | h
      · have h1 : v.asIdeal.inertiaDeg' w.asIdeal = v.asIdeal.inertiaDeg' w₁.1.asIdeal := by rw [← h]
        omega
      · have h1 : v.asIdeal.inertiaDeg' w.asIdeal = v.asIdeal.inertiaDeg' w₂.1.asIdeal := by rw [← h]
        omega
    rw [if_neg hno2, one_mul, huniv, Finset.prod_pair hne, htwist w₁ hn1.1, htwist w₂ hn2.1, hn1.2, hn2.2]

    have hne' : w₁.1 ≠ w₂.1 := fun h => hne (Subtype.ext h)
    have hb : (Pi.b v : ℂ) = (ξ (uniformizerIdele M w₁.1) : ℂ) * ξ (uniformizerIdele M w₂.1) :=
      ((hPi v hv).1 w₁.1 w₂.1 hne' w₁.2 w₂.2).2
    simp only [goodPlaceRootNumber, hpe, hb]
    rw [mul_zpow]
    ring
  ·
    have huniv : (Finset.univ : Finset (v.Extension (𝓞 M))) = {w₀} := by
      ext w
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact hall w
    have hn := LanglandsTunnell.TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_two E M v w₀ (he w₀) hf₀ (localChar μ v) a ha hunitμ
    have hyes : (∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) = v ∧ v.asIdeal.inertiaDeg' w.asIdeal = 2) := ⟨w₀.1, w₀.2, hf₀⟩
    rw [if_pos hyes, huniv, Finset.prod_singleton, htwist w₀ hn.1, hn.2]
    have hb : (Pi.b v : ℂ) = -(ξ (uniformizerIdele M w₀.1) : ℂ) := ((hPi v hv).2 w₀.1 w₀.2 hf₀).2
    simp only [goodPlaceRootNumber, hpe, hb]
    have h10 : (-1 : ℂ) ≠ 0 := by norm_num
    have hneg : (-(ξ (uniformizerIdele M w₀.1) : ℂ)) ^ ((a : ℤ) + addCharLevel (psiLocal E v)) =
        (-1 : ℂ) ^ ((a : ℤ) + addCharLevel (psiLocal E v)) * (ξ (uniformizerIdele M w₀.1) : ℂ) ^ ((a : ℤ) + addCharLevel (psiLocal E v)) := by
      rw [← mul_zpow, neg_one_mul]
    rw [hneg, neg_one_pow_natAbs, zpow_add₀ h10, zpow_natCast]

    have hsq : ((-1 : ℂ) ^ addCharLevel (psiLocal E v)) * ((-1 : ℂ) ^ addCharLevel (psiLocal E v)) = 1 := by
      rw [← zpow_add₀ h10, ← two_mul, zpow_mul, show ((-1 : ℂ)) ^ (2 : ℤ) = 1 by norm_num, one_zpow]
    linear_combination (-(((ξ (uniformizerIdele M w₀.1) : ℂ)) ^ ((a : ℤ) + addCharLevel (psiLocal E v)) * (-1 : ℂ) ^ a *
      stdRootNumberAt E v (localChar μ v) ^ 2)) * hsq

set_option autoImplicit false

p2m_open "NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter LanglandsTunnell P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.HeckeTate M4aHerbrand.GenuineDescent"

p2m_open_scoped "LanglandsTunnell" in
set_option maxHeartbeats 3200000 in
theorem LanglandsTunnell.P2ind.localChar_comp_norm_uniformizerUnit
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M)) (hμv : IsUnramifiedCharAt μ v) :
    ((localChar μ v).comp (Units.map (Algebra.norm (v.adicCompletion E)))
        (NumberField.AdelicLevel.uniformizerUnit M w.1) : ℂˣ) =
      μ (uniformizerIdele E v) ^ (v.asIdeal.inertiaDeg' w.1.asIdeal) := by

  have h1 := NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange E M 1 μ v w
  have h2 : ∀ x, ((localChar μ v).comp (Units.map (Algebra.norm (v.adicCompletion E)))) x =
      μ ((genuineBaseChange E M).idelicNorm (Units.map (NumberField.AdelicLevel.finIncl (𝓞 M) M) (NumberField.AdelicLevel.localUnit (𝓞 M) M w.1 x))) := fun x => by
    have hx := congrArg (fun φ : (w.1.adicCompletion M)ˣ →* ℂˣ => φ x) h1
    simp only [MonoidHom.mul_apply, localChar_apply, MonoidHom.one_apply, one_mul, MonoidHom.comp_apply] at hx
    simp only [MonoidHom.comp_apply]
    exact hx.symm
  rw [h2]

  obtain ⟨t, ht, hN⟩ := M4aHerbrand.exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit E M w.1
  have hμv' : IsUnramifiedCharAt μ (w.1.under (𝓞 E)) := by rw [w.2]; exact hμv
  have hint : (t : (w.1.under (𝓞 E)).adicCompletion E) ∈ (w.1.under (𝓞 E)).adicCompletionIntegers E := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ht]
  have hint' : ((t⁻¹ : ((w.1.under (𝓞 E)).adicCompletion E)ˣ) : (w.1.under (𝓞 E)).adicCompletion E) ∈
      (w.1.under (𝓞 E)).adicCompletionIntegers E := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, ht, inv_one]
  have hkill : μ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 E) E) (NumberField.AdelicLevel.localUnit (𝓞 E) E (w.1.under (𝓞 E)) t)) = 1 := by
    have := hμv' t hint hint'
    rwa [localChar_apply] at this
  have hN' : μ ((genuineBaseChange E M).idelicNorm (uniformizerIdele M w.1)) =
      μ (uniformizerIdele E (w.1.under (𝓞 E))) ^ ((w.1.under (𝓞 E)).asIdeal.inertiaDeg' w.1.asIdeal) := by
    rw [hN, map_mul, map_pow, hkill, mul_one]
  rw [w.2] at hN'

  exact hN'

p2m_open_scoped "LanglandsTunnell" in

theorem LanglandsTunnell.P2ind.norm_apply_eq_one_of_isOfFinOrder {G : Type} [Group G] (χ : G →* ℂˣ) (hχ : IsOfFinOrder χ) (g : G) :
    ‖((χ g : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hχn⟩ := hχ.exists_pow_eq_one
  have h1 : ((χ g : ℂˣ) : ℂ) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hχn, MonoidHom.one_apply, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h1 hn.ne'

p2m_open_scoped "LanglandsTunnell" in

theorem LanglandsTunnell.P2ind.prod_zpow_eq_zpow_sum' {ι : Type} (s : Finset ι) (b : ℂ) (hb : b ≠ 0) (e : ι → ℤ) :
    ∏ i ∈ s, b ^ e i = b ^ ∑ i ∈ s, e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hb]

p2m_open_scoped "LanglandsTunnell" in
set_option maxHeartbeats 3200000 in
theorem LanglandsTunnell.P2ind.prod_extension_stdRootNumberAt_on_S
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist E μ)
    (v : HeightOneSpectrum (𝓞 E)) (hμv : IsUnramifiedCharAt μ v) :
    (letI := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 E) E M (𝓞 M) v
      ∏ w : v.Extension (𝓞 M),
        LanglandsTunnell.TateLocal.stdRootNumberAt M w.1 (localChar (ξ * μ.comp (genuineBaseChange E M).idelicNorm) w.1)) =
    (letI := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 E) E M (𝓞 M) v
      ∏ w : v.Extension (𝓞 M), LanglandsTunnell.TateLocal.stdRootNumberAt M w.1 (localChar ξ w.1)) *
      ((μ (uniformizerIdele E v) : ℂˣ) : ℂ) ^
        (letI := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 E) E M (𝓞 M) v
          ∑ w : v.Extension (𝓞 M),
            (v.asIdeal.inertiaDeg' w.1.asIdeal : ℤ) *
              ((LanglandsTunnell.TateLocal.conductorExponentAt M w.1 (localChar ξ w.1) : ℤ) +
                LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal M w.1))) := by
  letI := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 E) E M (𝓞 M) v
  set b : ℂ := ((μ (uniformizerIdele E v) : ℂˣ) : ℂ) with hb
  have hb0 : b ≠ 0 := Units.ne_zero _
  have hb1 : ‖b‖ = 1 := hμ.2.2 _
  rw [← LanglandsTunnell.P2ind.prod_zpow_eq_zpow_sum' _ b hb0, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_

  rw [NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange E M ξ μ v w]
  set ω : (w.1.adicCompletion M)ˣ →* ℂˣ := (localChar μ v).comp (Units.map (Algebra.norm (v.adicCompletion E))) with hω

  obtain ⟨a, ha⟩ := LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous M w.1 (localChar ξ w.1)
    (NumberField.TateGlobal.continuous_localChar ξ hξ.continuous w.1)
  have ha' : LanglandsTunnell.TateLocal.conductorExponentAt M w.1 (localChar ξ w.1) = a :=
    LanglandsTunnell.TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt M w.1 ha

  have hω0 : LanglandsTunnell.TateLocal.HasConductorExponentAt M w.1 ω 0 :=
    LanglandsTunnell.TateLocal.hasConductorExponentAt_comp_norm_zero E M v w (localChar μ v)
      (LanglandsTunnell.Converse.hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt E μ v hμv)

  have hωϖ : ((ω (NumberField.AdelicLevel.uniformizerUnit M w.1) : ℂˣ) : ℂ) = b ^ (v.asIdeal.inertiaDeg' w.1.asIdeal) := by
    rw [hω, LanglandsTunnell.P2ind.localChar_comp_norm_uniformizerUnit E M μ v w hμv, Units.val_pow_eq_pow_val]
  have hu : ‖((localChar ξ w.1 (NumberField.AdelicLevel.uniformizerUnit M w.1) : ℂˣ) : ℂ)‖ = 1 := by
    rw [localChar_apply]; exact LanglandsTunnell.P2ind.norm_apply_eq_one_of_isOfFinOrder ξ hξ.isOfFinOrder _
  have huω : ‖((ω (NumberField.AdelicLevel.uniformizerUnit M w.1) : ℂˣ) : ℂ)‖ = 1 := by
    rw [hωϖ, norm_pow, hb1, one_pow]

  rw [LanglandsTunnell.TateLocal.stdRootNumberAt_mul_of_hasConductorExponentAt_zero M w.1 (localChar ξ w.1) ω a ha hω0 hu huω
    (LanglandsTunnell.TateLocal.psiLocal_ne_one M w.1), hωϖ, ha', mul_comm]
  congr 1
  rw [← zpow_natCast, ← zpow_mul]

p2m_open_scoped "LanglandsTunnell" in
open scoped Classical in
open LanglandsTunnell.P2ind in
theorem LanglandsTunnell.P2ind.heckeRootNumber_eq
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    (Pi : HeckeEigensystem E ℂ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS₀ : ∀ w' ∈ S₀, w'.under (𝓞 E) ∈ S)
    (hram : ∀ v ∉ S, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = v →
      v.asIdeal.ramificationIdx' w'.asIdeal = 1)
    (hPi : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ S →
      (∀ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' → w'.under (𝓞 E) = w → w''.under (𝓞 E) = w →
        Pi.a w = (ξ (uniformizerIdele M w') : ℂ) + ξ (uniformizerIdele M w'') ∧
        Pi.b w = (ξ (uniformizerIdele M w') : ℂ) * ξ (uniformizerIdele M w'')) ∧
      (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → w.asIdeal.inertiaDeg' w'.asIdeal = 2 →
        Pi.a w = 0 ∧ Pi.b w = -(ξ (uniformizerIdele M w') : ℂ)))
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist E μ) (hμS : ∀ v ∈ S, IsUnramifiedCharAt μ v)
    (hsign : ∀ w w' : InfinitePlace M, w ≠ w' → w.IsReal → w'.IsReal →
      w.comap (algebraMap E M) = w'.comap (algebraMap E M) →
      ((archLocalChar ξ w (-1) : ℂˣ) : ℂ) * archLocalChar ξ w' (-1) = -1)
    (c₀ : ℂ)
    (harch : ∀ (aR : ∀ w : InfinitePlace E, w.IsReal → ZMod 2) (kC : ∀ w : InfinitePlace E, w.IsComplex → ℤ)
        (aR' : ∀ w' : InfinitePlace M, w'.IsReal → ZMod 2)
        (kC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℤ),
        (∀ w', ∀ hw' : w'.IsReal,
          ((archLocalChar ξ w' (-1) : ℂˣ) : ℂ) =
            (-1) ^ (aR' w' hw' - aR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M))).val) →
        (∀ w', ∀ hw' : w'.IsComplex,
          (kC' w' hw').natAbs = if h : (w'.comap (algebraMap E M)).IsReal then 0
            else (kC _ (InfinitePlace.not_isReal_iff_isComplex.mp h)).natAbs) →
        ∀ (uR : ∀ w : InfinitePlace E, w.IsReal → ℂ) (uC : ∀ w : InfinitePlace E, w.IsComplex → ℂ),
          ((Finset.univ : Finset {w' : InfinitePlace M // w'.IsReal}).prod
              fun w' => signEpsilon (aR' w'.1 w'.2)) *
            ((Finset.univ : Finset {w' : InfinitePlace M // w'.IsComplex}).prod
              fun w' => Complex.I ^ (kC' w'.1 w'.2).natAbs) =
          c₀ * archRootNumber E (fun _ _ => RealArchParam.oddArtin) (fun _ _ => ComplexArchParam.trivialArtin)
                uR aR uC kC)
    (aR : ∀ w : InfinitePlace E, w.IsReal → ZMod 2) (kC : ∀ w : InfinitePlace E, w.IsComplex → ℤ)
    (aR' : ∀ w' : InfinitePlace M, w'.IsReal → ZMod 2)
    (kC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℤ)
    (haR' : ∀ w', ∀ hw' : w'.IsReal,
      ((archLocalChar ξ w' (-1) : ℂˣ) : ℂ) =
        (-1) ^ (aR' w' hw' - aR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M))).val)
    (hkC' : ∀ w', ∀ hw' : w'.IsComplex,
      (kC' w' hw').natAbs = if h : (w'.comap (algebraMap E M)).IsReal then 0
        else (kC _ (InfinitePlace.not_isReal_iff_isComplex.mp h)).natAbs)
    (uR : ∀ w : InfinitePlace E, w.IsReal → ℂ) (uC : ∀ w : InfinitePlace E, w.IsComplex → ℂ) :
    heckeRootNumber M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) aR' kC' =
      c₀ * cI E M S * cS E M ξ S * (∏ v : ↥S, ((μ (uniformizerIdele E v.1) : ℂˣ) : ℂ) ^ (kOf E M ξ S v)) *
        pinnedRootNumber E Pi μ S (fun _ _ => RealArchParam.oddArtin)
          (fun _ _ => ComplexArchParam.trivialArtin) uR aR uC kC := by

  have hfin : (∏ᶠ w : HeightOneSpectrum (𝓞 M),
      LanglandsTunnell.TateLocal.stdRootNumberAt M w (localChar (ξ * μ.comp (genuineBaseChange E M).idelicNorm) w)) =
      cI E M S * cS E M ξ S * (∏ v : ↥S, ((μ (uniformizerIdele E v.1) : ℂˣ) : ℂ) ^ (kOf E M ξ S v)) *
        finiteRootNumber E Pi μ S := by

    set lam := ξ * μ.comp (genuineBaseChange E M).idelicNorm with hlam
    set F : HeightOneSpectrum (𝓞 M) → ℂ := fun w => LanglandsTunnell.TateLocal.stdRootNumberAt M w (localChar lam w) with hF

    have hlamw : ∀ (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M)),
        localChar lam w.1 = localChar ξ w.1 * (localChar μ v).comp (Units.map (Algebra.norm (v.adicCompletion E))) :=
      fun v w => NumberField.TateGlobal.localChar_mul_comp_idelicNorm_genuineBaseChange E M ξ μ v w

    have hsupp : (Function.mulSupport F).Finite := by

      have hADM : IsAdmissibleTwist M lam := by
        refine ⟨fun u => ?_, ?_, fun x => ?_⟩
        ·
          have hN : (genuineBaseChange E M).idelicNorm (Units.map (algebraMap M (AdeleRing (𝓞 M) M) : M →* AdeleRing (𝓞 M) M) u) =
              Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* AdeleRing (𝓞 E) E) (Units.map (Algebra.norm E : M →* E) u) := by
            apply Units.ext
            exact M4aHerbrand.GenuineDescent.adelicNorm_genuineBaseChange_algebraMap E M (u : M)
          rw [hlam, MonoidHom.mul_apply, hξ.isIdeleClassChar u, one_mul, MonoidHom.comp_apply, hN]
          exact hμ.1 _
        ·
          rw [hlam]
          have hc : Continuous (μ.comp (genuineBaseChange E M).idelicNorm) :=
            hμ.2.1.comp (Continuous.units_map _ (M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange E M))
          exact hξ.continuous.mul hc
        ·
          rw [hlam, MonoidHom.mul_apply, Units.val_mul, norm_mul, MonoidHom.comp_apply, hμ.2.2, mul_one]
          exact LanglandsTunnell.P2ind.norm_apply_eq_one_of_isOfFinOrder ξ hξ.isOfFinOrder x
      exact (LanglandsTunnell.HeckeTate.finite_setOf_stdRootNumberAt_ne_one_and_finite_setOf_pinnedExp_ne_zero M lam hADM).1

    have hG2 : (∏ᶠ w, F w) = ∏ᶠ v : HeightOneSpectrum (𝓞 E),
        (letI := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 E) E M (𝓞 M) v; ∏ w : v.Extension (𝓞 M), F w.1) :=
      IsDedekindDomain.HeightOneSpectrum.finprod_eq_finprod_prod_extension E M F hsupp

    have hS : ∀ v : ↥S,
        (letI := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 E) E M (𝓞 M) v.1; ∏ w : v.1.Extension (𝓞 M), F w.1) =
        (letI := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 E) E M (𝓞 M) v.1;
          ∏ w : v.1.Extension (𝓞 M), LanglandsTunnell.TateLocal.stdRootNumberAt M w.1 (localChar ξ w.1)) *
          ((μ (uniformizerIdele E v.1) : ℂˣ) : ℂ) ^ (kOf E M ξ S v) := by
      intro v
      have h := LanglandsTunnell.P2ind.prod_extension_stdRootNumberAt_on_S E M ξ hξ μ hμ v.1 (hμS v.1 v.2)
      simp only [hF]
      rw [h]
      rfl

    have hgood : ∀ v : HeightOneSpectrum (𝓞 E), v ∉ S →
        (letI := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 E) E M (𝓞 M) v; ∏ w : v.Extension (𝓞 M), F w.1) =
        (if (∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) = v ∧ v.asIdeal.inertiaDeg' w.asIdeal = 2)
          then (-1 : ℂ) ^ (LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal E v)).natAbs else 1) *
          goodPlaceRootNumber E Pi μ v := fun v hv => by
      simp only [hF]
      exact LanglandsTunnell.P2ind.prod_extension_stdRootNumberAt_off_S E M h2 ξ hξ S₀ hunr Pi S hS₀ hram hPi μ hμ v hv

    rw [hG2]
    set G : HeightOneSpectrum (𝓞 E) → ℂ := fun v =>
      (letI := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 E) E M (𝓞 M) v; ∏ w : v.Extension (𝓞 M), F w.1) with hG
    set Iv : HeightOneSpectrum (𝓞 E) → ℂ := fun v =>
      (if (∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) = v ∧ v.asIdeal.inertiaDeg' w.asIdeal = 2)
        then (-1 : ℂ) ^ (LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal E v)).natAbs else 1) with hIv

    have hGsupp : (Function.mulSupport G).Finite := by
      refine (hsupp.image fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 E)).subset ?_
      intro v hv
      rw [Function.mem_mulSupport] at hv
      by_contra hv'
      apply hv
      simp only [hG]
      refine Finset.prod_eq_one fun w _ => ?_
      by_contra hw
      exact hv' ⟨w.1, hw, w.2⟩

    have hsplit : (∏ᶠ v, G v) = (∏ v ∈ S, G v) * ∏ᶠ v, (if v ∈ S then 1 else G v) := by
      have hpt : ∀ v, G v = (if v ∈ S then G v else 1) * (if v ∈ S then 1 else G v) := by
        intro v; split_ifs <;> simp
      have hf1 : (Function.mulSupport fun v => if v ∈ S then G v else 1).Finite :=
        (S.finite_toSet).subset fun v hv => by
          rw [Function.mem_mulSupport] at hv; by_contra h; exact hv (if_neg h)
      have hf2 : (Function.mulSupport fun v => if v ∈ S then 1 else G v).Finite :=
        hGsupp.subset fun v hv => by
          rw [Function.mem_mulSupport] at hv ⊢; intro h; apply hv; simp [h]
      rw [finprod_congr hpt, finprod_mul_distrib hf1 hf2]
      congr 1
      rw [finprod_eq_prod_of_mulSupport_subset _ (show (Function.mulSupport fun v => if v ∈ S then G v else 1) ⊆ (S : Set _) from
        fun v hv => by rw [Function.mem_mulSupport] at hv; by_contra h; exact hv (if_neg h))]
      exact Finset.prod_congr rfl fun v hv => if_pos hv

    have hSpart : (∏ v ∈ S, G v) = cS E M ξ S * ∏ v : ↥S, ((μ (uniformizerIdele E v.1) : ℂˣ) : ℂ) ^ (kOf E M ξ S v) := by
      rw [← Finset.prod_coe_sort S, show (fun v : ↥S => G v.1) = fun v : ↥S =>
          (letI := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 E) E M (𝓞 M) v.1;
            ∏ w : v.1.Extension (𝓞 M), LanglandsTunnell.TateLocal.stdRootNumberAt M w.1 (localChar ξ w.1)) *
          ((μ (uniformizerIdele E v.1) : ℂˣ) : ℂ) ^ (kOf E M ξ S v) from funext fun v => by simp only [hG]; exact hS v,
        Finset.prod_mul_distrib]
      rfl

    have hoff : (∏ᶠ v, (if v ∈ S then 1 else G v)) = cI E M S * finiteRootNumber E Pi μ S := by
      have hcongr : ∀ v, (if v ∈ S then (1 : ℂ) else G v) =
          (if v ∈ S then (1 : ℂ) else Iv v) * (if v ∈ S then (1 : ℂ) else goodPlaceRootNumber E Pi μ v) := by
        intro v
        split_ifs with hv
        · simp
        · simp only [hG, hIv]; exact hgood v hv

      have hlev : {v : HeightOneSpectrum (𝓞 E) | LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal E v) ≠ 0}.Finite := by
        have h := LanglandsTunnell.Converse.finite_setOf_pinnedExp_ne_zero_of_continuous E 1 continuous_const
        refine h.subset fun v hv => ?_
        simp only [Set.mem_setOf_eq] at hv ⊢
        unfold pinnedExp
        have h1 : localChar (1 : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) v = 1 := rfl
        rw [h1, LanglandsTunnell.TateLocal.conductorExponentAt_one]
        simpa using hv
      have hfI : (Function.mulSupport fun v => if v ∈ S then (1 : ℂ) else Iv v).Finite := by
        refine hlev.subset fun v hv => ?_
        rw [Function.mem_mulSupport] at hv
        simp only [Set.mem_setOf_eq]
        intro h0
        apply hv
        simp only [hIv, h0, Int.natAbs_zero, pow_zero, ite_self, ite_self]
      have hεfin := (LanglandsTunnell.HeckeTate.finite_setOf_stdRootNumberAt_ne_one_and_finite_setOf_pinnedExp_ne_zero E μ hμ)
      have hfg : (Function.mulSupport fun v => if v ∈ S then (1 : ℂ) else goodPlaceRootNumber E Pi μ v).Finite := by
        refine (hεfin.1.union hεfin.2).subset fun v hv => ?_
        rw [Function.mem_mulSupport] at hv
        by_contra h
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
        apply hv
        have : goodPlaceRootNumber E Pi μ v = 1 := by
          unfold goodPlaceRootNumber; rw [h.1, h.2]; simp
        simp [this]
      rw [finprod_congr hcongr, finprod_mul_distrib hfI hfg]
      rfl
    rw [hsplit, hSpart, hoff]
    ring

  have ha := harch aR kC aR' kC' haR' hkC' uR uC
  unfold heckeRootNumber pinnedRootNumber
  rw [hfin, ha]
  ring

set_option autoImplicit false

p2m_open "NumberField NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter LanglandsTunnell P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two.LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.HeckeTate M4aHerbrand.GenuineDescent"

open LanglandsTunnell.P2ind in
open scoped Classical in

theorem solution
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    (hsign : ∀ w w' : InfinitePlace M, w ≠ w' → w.IsReal → w'.IsReal →
      w.comap (algebraMap E M) = w'.comap (algebraMap E M) →
      ((archLocalChar ξ w (-1) : ℂˣ) : ℂ) * archLocalChar ξ w' (-1) = -1)
    (Pi : HeckeEigensystem E ℂ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS₀ : ∀ w' ∈ S₀, w'.under (𝓞 E) ∈ S)
    (hram : ∀ v ∉ S, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = v →
      v.asIdeal.ramificationIdx' w'.asIdeal = 1)
    (hPi : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ S →
      (∀ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' → w'.under (𝓞 E) = w → w''.under (𝓞 E) = w →
        Pi.a w = (ξ (uniformizerIdele M w') : ℂ) + ξ (uniformizerIdele M w'') ∧
        Pi.b w = (ξ (uniformizerIdele M w') : ℂ) * ξ (uniformizerIdele M w'')) ∧
      (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → w.asIdeal.inertiaDeg' w'.asIdeal = 2 →
        Pi.a w = 0 ∧ Pi.b w = -(ξ (uniformizerIdele M w') : ℂ))) :
    ∃ (c : ℂ) (k : ↥S → ℤ), ∀ (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ), IsAdmissibleTwist E μ →
      (∀ v ∈ S, IsUnramifiedCharAt μ v) →
      heckeConductor M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) =
        finiteConductor E μ S * ∏ v : ↥S, (Ideal.absNorm v.1.asIdeal : ℝ) ^ (k v) ∧
      ∀ (aR : ∀ w : InfinitePlace E, w.IsReal → ZMod 2) (kC : ∀ w : InfinitePlace E, w.IsComplex → ℤ)
        (aR' : ∀ w' : InfinitePlace M, w'.IsReal → ZMod 2)
        (kC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℤ),
        (∀ w', ∀ hw' : w'.IsReal,
          ((archLocalChar ξ w' (-1) : ℂˣ) : ℂ) =
            (-1) ^ (aR' w' hw' - aR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M))).val) →
        (∀ w', ∀ hw' : w'.IsComplex,
          (kC' w' hw').natAbs = if h : (w'.comap (algebraMap E M)).IsReal then 0
            else (kC _ (InfinitePlace.not_isReal_iff_isComplex.mp h)).natAbs) →
        ∀ (uR : ∀ w : InfinitePlace E, w.IsReal → ℂ) (uC : ∀ w : InfinitePlace E, w.IsComplex → ℂ),
          heckeRootNumber M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) aR' kC' =
            c * (∏ v : ↥S, ((μ (uniformizerIdele E v.1) : ℂˣ) : ℂ) ^ (k v)) *
              pinnedRootNumber E Pi μ S (fun _ _ => RealArchParam.oddArtin)
                (fun _ _ => ComplexArchParam.trivialArtin) uR aR uC kC := by
  obtain ⟨c₀, -, harch⟩ := LanglandsTunnell.HeckeTate.exists_archRootNumber_induced_of_finrank_eq_two E M h2 ξ hsign
  refine ⟨c₀ * cI E M S * cS E M ξ S, kOf E M ξ S, fun μ hμ hμS => ⟨?_, ?_⟩⟩
  · exact heckeConductor_eq E M h2 ξ hξ S₀ hunr Pi S hS₀ hram hPi μ hμ hμS
  · intro aR kC aR' kC' haR' hkC' uR uC
    exact heckeRootNumber_eq E M h2 ξ hξ S₀ hunr Pi S hS₀ hram hPi μ hμ hμS hsign c₀ harch aR kC aR' kC' haR' hkC' uR uC

end S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two
end P2MW
export P2MW.S_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two (solution)
