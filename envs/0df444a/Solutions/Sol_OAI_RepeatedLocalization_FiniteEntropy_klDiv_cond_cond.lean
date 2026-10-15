-- Prove2me | solution 1 for OAI.RepeatedLocalization.FiniteEntropy.klDiv_cond_cond
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:29:04.675757+00:00
-- url     : https://prove2.me/submissions/12141afe-9fc1-4c70-ba87-2c71f2f41b90

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/EntropyChain.lean:L84-L113
-- (upload_full_project.md Phase 4): solution for node OAI.RepeatedLocalization.FiniteEntropy.klDiv_cond_cond. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards

-- ---- from OAI.Probability.Localization.EntropyChain ----
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma llr_restrict_left {α : Type*} [MeasurableSpace α] (P ν : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure ν] (hac : P ≪ ν) {E : Set α} (hE : MeasurableSet E) :
    llr (P.restrict E) ν =ᵐ[P.restrict E] llr P ν := by
  have ha : P.restrict E ≪ ν := Measure.absolutelyContinuous_restrict.trans hac
  filter_upwards [ha.ae_le (Measure.rnDeriv_restrict P ν hE),ae_restrict_mem hE] with x hx hxE
  simp only [llr,Set.indicator_of_mem hxE] at hx ⊢
  rw [hx]

lemma llr_chain {α : Type*} [MeasurableSpace α] (P ν ρ : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    (hPν : P ≪ ν) (hνρ : ν ≪ ρ) :
    llr P ρ =ᵐ[P] fun x => llr P ν x + llr ν ρ x := by
  filter_upwards [(hPν.trans hνρ).ae_le (Measure.rnDeriv_mul_rnDeriv hPν),
    Measure.rnDeriv_pos hPν,hPν.ae_le (Measure.rnDeriv_lt_top P ν),
    hPν.ae_le (Measure.rnDeriv_pos hνρ),(hPν.trans hνρ).ae_le (Measure.rnDeriv_lt_top ν ρ)]
    with x hx hp hp' hν hν'
  simp only [llr,Pi.mul_apply] at hx ⊢
  rw [← hx,ENNReal.toReal_mul,Real.log_mul]
  · exact ENNReal.toReal_ne_zero.mpr ⟨hp.ne',hp'.ne⟩
  · exact ENNReal.toReal_ne_zero.mpr ⟨hν.ne',hν'.ne⟩

lemma llr_cond_left {α : Type*} [MeasurableSpace α] (P ν : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure ν] (hac : P ≪ ν)
    {E : Set α} (hE : MeasurableSet E) (hp : P E ≠ 0) :
    llr (ProbabilityTheory.cond P E) ν =ᵐ[ProbabilityTheory.cond P E]
      fun x => llr P ν x - Real.log (P E).toReal := by
  have ha : P.restrict E ≪ ν := Measure.absolutelyContinuous_restrict.trans hac
  have hleft := llr_smul_left ha (P E)⁻¹ (ENNReal.inv_ne_zero.mpr (measure_ne_top P E))
    (ENNReal.inv_ne_top.mpr hp)
  have hrestrict := llr_restrict_left P ν hac hE
  have hcond : ProbabilityTheory.cond P E ≪ P.restrict E := Measure.smul_absolutelyContinuous
  filter_upwards [hcond.ae_le hleft,hcond.ae_le hrestrict] with x hx hy
  change llr ((P E)⁻¹ • P.restrict E) ν x = _
  rw [hx,hy,ENNReal.toReal_inv,Real.log_inv]
  ring

lemma cond_ac_cond {α : Type*} [MeasurableSpace α] (P ν : Measure α)
    [IsFiniteMeasure ν] (hac : P ≪ ν) {E R : Set α} (hER : E ⊆ R) (hνR : ν R ≠ 0) :
    ProbabilityTheory.cond P E ≪ ProbabilityTheory.cond ν R := by
  have normalize : ν R • ProbabilityTheory.cond ν R = ν.restrict R := by
    rw [ProbabilityTheory.cond, smul_smul,
      ENNReal.mul_inv_cancel hνR (measure_ne_top ν R), one_smul]
  have restrict_ac : ν.restrict R ≪ ProbabilityTheory.cond ν R := by
    rw [← normalize]
    exact Measure.smul_absolutelyContinuous
  exact (Measure.smul_absolutelyContinuous.trans
    ((Measure.absolutelyContinuous_of_le (Measure.restrict_mono hER le_rfl)).trans (hac.restrict R))).trans
      restrict_ac

lemma llr_cond_cond {α : Type*} [MeasurableSpace α] (P ν : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure ν] (hac : P ≪ ν)
    {E R : Set α} (hE : MeasurableSet E) (hR : MeasurableSet R) (hER : E ⊆ R)
    (hp : P E ≠ 0) (hνR : ν R ≠ 0) :
    llr (ProbabilityTheory.cond P E) (ProbabilityTheory.cond ν R) =ᵐ[ProbabilityTheory.cond P E]
      fun x => llr P ν x - Real.log (P E).toReal + Real.log (ν R).toReal := by
  let := ProbabilityTheory.cond_isProbabilityMeasure (μ := P) hp
  let := ProbabilityTheory.cond_isProbabilityMeasure (μ := ν) hνR
  have ha := cond_ac_cond P ν hac hER hνR
  have he := llr_chain (ProbabilityTheory.cond P E) (ProbabilityTheory.cond ν R) ν ha
    ProbabilityTheory.cond_absolutelyContinuous
  have hpν := llr_cond_left P ν hac hE hp
  have hνν := llr_cond_left ν ν Measure.AbsolutelyContinuous.rfl hR hνR
  have hs := (ProbabilityTheory.cond_absolutelyContinuous (μ := ν) (s := R)).ae_le (llr_self ν)
  filter_upwards [he,hpν,ha.ae_le hνν,ha.ae_le hs] with x he hpν hνν hs
  simp only [Pi.zero_apply] at hs
  rw [hs] at hνν
  linarith

lemma integral_cond {α : Type*} [MeasurableSpace α] (P : Measure α) (E : Set α) (f : α → ℝ) :
    (∫ x,f x ∂ProbabilityTheory.cond P E) = (P E).toReal⁻¹ * ∫ x in E,f x ∂P := by
  rw [ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]

lemma klDiv_cond_cond {α : Type*} [MeasurableSpace α] (P ν : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure ν] (hac : P ≪ ν)
    (hK : InformationTheory.klDiv P ν ≠ ∞) {E R : Set α}
    (hE : MeasurableSet E) (hR : MeasurableSet R) (hER : E ⊆ R)
    (hp : P E ≠ 0) (hνR : ν R ≠ 0) :
    InformationTheory.klDiv (ProbabilityTheory.cond P E) (ProbabilityTheory.cond ν R) ≠ ∞ ∧
    (P E).toReal * (InformationTheory.klDiv (ProbabilityTheory.cond P E) (ProbabilityTheory.cond ν R)).toReal =
      (∫ x in E,llr P ν x ∂P) - (P E).toReal * Real.log (P E).toReal +
        (P E).toReal * Real.log (ν R).toReal := by
  let := ProbabilityTheory.cond_isProbabilityMeasure (μ := P) hp
  let := ProbabilityTheory.cond_isProbabilityMeasure (μ := ν) hνR
  have ha := cond_ac_cond P ν hac hER hνR
  have hint := (InformationTheory.klDiv_ne_top_iff.mp hK).2
  have hint' : Integrable (llr P ν) (ProbabilityTheory.cond P E) :=
    hint.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr hp)
  have he := llr_cond_cond P ν hac hE hR hER hp hνR
  have hi : Integrable (llr (ProbabilityTheory.cond P E) (ProbabilityTheory.cond ν R))
      (ProbabilityTheory.cond P E) :=
    ((hint'.sub (integrable_const _)).add (integrable_const _)).congr he.symm
  refine ⟨InformationTheory.klDiv_ne_top ha hi,?_⟩
  rw [InformationTheory.toReal_klDiv_of_measure_eq ha (by simp),integral_congr_ae he]
  have hsub := integral_sub hint' (integrable_const (Real.log (P E).toReal))
  have hadd := integral_add (hint'.sub (integrable_const (Real.log (P E).toReal)))
    (integrable_const (Real.log (ν R).toReal))
  simp only [Pi.sub_apply] at hsub hadd
  rw [hadd,hsub]
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
  rw [integral_cond]
  have hp' : (P E).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp,measure_ne_top _ _⟩
  field_simp

end FiniteEntropy

end RepeatedLocalization

end OAI

-- ---- platform node ----
open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem solution {α : Type*} [MeasurableSpace α] (P ν : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure ν] (hac : P ≪ ν)
    (hK : InformationTheory.klDiv P ν ≠ ∞) {E R : Set α}
    (hE : MeasurableSet E) (hR : MeasurableSet R) (hER : E ⊆ R)
    (hp : P E ≠ 0) (hνR : ν R ≠ 0) :
    InformationTheory.klDiv (ProbabilityTheory.cond P E) (ProbabilityTheory.cond ν R) ≠ ∞ ∧
    (P E).toReal * (InformationTheory.klDiv (ProbabilityTheory.cond P E) (ProbabilityTheory.cond ν R)).toReal =
      (∫ x in E,llr P ν x ∂P) - (P E).toReal * Real.log (P E).toReal +
        (P E).toReal * Real.log (ν R).toReal := by
  first
    | exact OAI.RepeatedLocalization.FiniteEntropy.klDiv_cond_cond P ν hac hK hE hR hER hp hνR
    | exact OAI.RepeatedLocalization.FiniteEntropy.klDiv_cond_cond
    | (apply OAI.RepeatedLocalization.FiniteEntropy.klDiv_cond_cond <;> assumption)
    | (intros; apply OAI.RepeatedLocalization.FiniteEntropy.klDiv_cond_cond <;> assumption)
