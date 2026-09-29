-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b3cf2374-e3ce-5fa1-89c3-d742092add27

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection

import Theorems.Thm_LanglandsTunnell_CubicInduction_integral_godementSection_upperUnipotent3_eq_godementWhittaker3_of_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_cellSectionOf_antidiagonal3_mul_mul_eq_integral_godementDatum
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetWhittaker3_diagonal3_mul_eq_mul_integral_psiLocal_cellSectionOf
import Theorems.Thm_LanglandsTunnell_CubicInduction_godementDatum_mem_principalSeries2_and_support
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_finset_pureTensor_godementDatum
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
import Theorems.Thm_AutomorphicForm_secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom
import Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_apply_antidiagonal_mul_unipotentGL2_mul_addChar_of_mem_principalSeries2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace B1Glue

variable (p : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel

scoped instance instBorelGL2 : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p

theorem continuous_det_units : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin 2) (p.adicCompletion ℚ) → (p.adicCompletion ℚ)ˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · simpa [Function.comp_def, Matrix.GeneralLinearGroup.val_det_apply] using (Units.continuous_val.matrix_det : Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) => (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det)
  · have : Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((g⁻¹ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)).det :=
      (Units.continuous_val.comp continuous_inv).matrix_det
    simpa [Matrix.GeneralLinearGroup.val_det_apply, map_inv] using this

theorem continuous_lam_det (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) :=
  Units.continuous_val.comp (hχ.continuous.comp (continuous_det_units p))

theorem modulus_cast_eq_norm (x : p.adicCompletion ℚ) : ((modulus x : ℝ) : ℂ) = ((‖x‖ : ℝ) : ℂ) := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem continuous_modulus_det : Continuous fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) := by
  simp_rw [modulus_cast_eq_norm]
  exact Complex.continuous_ofReal.comp ((Units.continuous_val.comp (continuous_det_units p)).norm)

theorem measurable_cpow_modulus_det (c : ℂ) :
    Measurable fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ c :=
  (continuous_modulus_det p).measurable.pow_const c

def rowpad (h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) :=
  Matrix.of fun i k => Fin.lastCases (0 : p.adicCompletion ℚ)
    (fun k' : Fin 2 => ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i k') k

theorem continuous_rowpad : Continuous (rowpad p) := by
  refine continuous_pi fun i => continuous_pi fun k => ?_
  induction k using Fin.lastCases with
  | last => simp only [rowpad, Matrix.of_apply, Fin.lastCases_last]; exact continuous_const
  | cast k' =>
    simp only [rowpad, Matrix.of_apply, Fin.lastCases_castSucc]
    exact (Units.continuous_val.matrix_elem i k')

theorem continuous_upperUnipotent3_val :
    Continuous fun q : p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ =>
      ((upperUnipotent3 q.1 q.2.1 q.2.2 : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) := by
  simp only [upperUnipotent3_coe]
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_argMap (g : LocalGL3 p) :
    Continuous fun r : (p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
      (rowpad p r.2 * ((upperUnipotent3 r.1.1 r.1.2.1 r.1.2.2 * g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)),
        antidiagonal2 p * r.2⁻¹) := by
  refine Continuous.prodMk ?_ ?_
  · refine ((continuous_rowpad p).comp continuous_snd).matrix_mul ?_
    have : Continuous fun r : (p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
        ((upperUnipotent3 r.1.1 r.1.2.1 r.1.2.2 : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) *
          (g : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) :=
      ((continuous_upperUnipotent3_val p).comp continuous_fst).matrix_mul continuous_const
    simpa only [Units.val_mul] using this
  · exact (continuous_const.mul (continuous_inv.comp continuous_snd))

open NumberField.StandardAddChar

theorem norm_psiPadicFun' {q : ℕ} [Fact q.Prime] (y : ℚ_[q]) : ‖psiPadicFun y‖ = 1 := by
  obtain ⟨a, k, hk⟩ := exists_pPow_approx y
  rw [psiPadicFun_eq hk]
  have hcast : -(2 * (Real.pi : ℂ) * Complex.I) * ((a : ℂ) / (q : ℂ) ^ k)
      = ((-(2 * Real.pi * ((a : ℝ) / (q : ℝ) ^ k)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hcast, Complex.norm_exp_ofReal_mul_I]

theorem norm_psiLocal (x : p.adicCompletion ℚ) : ‖psiLocal ℚ p x‖ = 1 := by
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv p : ℕ)) := ⟨(Rat.HeightOneSpectrum.primesEquiv p).2⟩
  rw [psiLocal_rat_eq_psiV, psiV_apply, psiPadic_apply]
  exact norm_psiPadicFun' _

theorem psiLocal_inv_inv_apply (x : p.adicCompletion ℚ) :
    (psiLocal ℚ p)⁻¹⁻¹ x = psiLocal ℚ p x := by
  rw [AddChar.inv_apply, AddChar.inv_apply, neg_neg]

theorem norm_psiLocal_inv_inv (x : p.adicCompletion ℚ) : ‖(psiLocal ℚ p)⁻¹⁻¹ x‖ = 1 := by
  rw [psiLocal_inv_inv_apply]; exact norm_psiLocal p x

theorem continuous_psiLocal_inv : Continuous ((psiLocal ℚ p)⁻¹ : AddChar (p.adicCompletion ℚ) ℂ) := by
  have : (((psiLocal ℚ p)⁻¹ : AddChar (p.adicCompletion ℚ) ℂ) : (p.adicCompletion ℚ) → ℂ) =
      fun x => psiLocal ℚ p (-x) := funext fun x => AddChar.inv_apply _ x
  rw [this]
  exact (continuous_psiLocal ℚ p).comp continuous_neg

theorem isAddHaarMeasure_selfDualHaarAt :
    (selfDualHaarAt ℚ p : Measure (p.adicCompletion ℚ)).IsAddHaarMeasure := by
  have hq : (Ideal.absNorm p.asIdeal : NNReal) ≠ 0 := by
    have h : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
    exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)
  have hc : ((Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (psiLocal ℚ p) : ℝ) / 2)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne'
  show ((((Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (psiLocal ℚ p) : ℝ) / 2))
      • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) : Measure (p.adicCompletion ℚ))).IsAddHaarMeasure
  rw [ENNReal.smul_def]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc) ENNReal.coe_ne_top

theorem upperUnipotent2_eq_unipotentGL2 (x : p.adicCompletion ℚ) : upperUnipotent2 p x = unipotentGL2 x :=
  Units.ext rfl

theorem det_upperUnipotent3_mul (x y z : p.adicCompletion ℚ) (g : LocalGL3 p) :
    Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z * g) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul]
  have : Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z : LocalGL3 p) = 1 := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, upperUnipotent3_coe, Matrix.det_fin_three]
    simp
  rw [this, one_mul]

theorem exists_higherUnitsAt_eq_one (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ n : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p n, χ u = 1 := by
  obtain ⟨V, hV, hVF⟩ := Units.isEmbedding_val₀.toIsInducing.isOpen_iff.mp (hχ.isOpen_fiber (χ 1))
  have h1V : (1 : p.adicCompletion ℚ) ∈ V := by
    have : (1 : (p.adicCompletion ℚ)ˣ) ∈ (Units.val ⁻¹' V : Set (p.adicCompletion ℚ)ˣ) := by rw [hVF]; exact rfl
    simpa using this
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h1V)
  have hq1 : 1 < ((Ideal.absNorm p.asIdeal : NNReal) : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  have hq0 : 0 < ((Ideal.absNorm p.asIdeal : NNReal) : ℝ) := lt_trans one_pos hq1
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (((Ideal.absNorm p.asIdeal : NNReal) : ℝ)⁻¹) ^ n < ε :=
    exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hq1)
  refine ⟨n + 1, fun u hu => ?_⟩
  rcases hu with ⟨-, h0 | hle⟩
  · omega
  · have hmono := (WithZeroMulInt.toNNReal_strictMono hq1).monotone hle
    have hnorm : ‖(u : p.adicCompletion ℚ) - 1‖ < ε := by
      rw [NumberField.FinitePlace.norm_def]
      refine lt_of_le_of_lt (NNReal.coe_le_coe.mpr hmono) ?_
      rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
      refine lt_of_le_of_lt ?_ hn
      have : Multiplicative.toAdd (WithZero.unzero (WithZero.exp_ne_zero (a := (-((n + 1 : ℕ) : ℤ))))) = -((n + 1 : ℕ) : ℤ) := rfl
      rw [this]
      push_cast
      rw [zpow_neg, ← inv_zpow, ← zpow_natCast]
      exact zpow_le_zpow_right_of_le_one₀ (inv_pos.mpr hq0) (inv_le_one_of_one_le₀ hq1.le) (by omega)
    have hmem : (u : p.adicCompletion ℚ) ∈ V := hball (by simpa [Metric.mem_ball, dist_eq_norm] using hnorm)
    have : u ∈ (Units.val ⁻¹' V : Set (p.adicCompletion ℚ)ˣ) := hmem
    rw [hVF] at this
    have h := this
    simp only [Set.mem_setOf_eq, map_one] at h
    exact h

theorem norm_uniformizerUnit_lt_one :
    ‖((NumberField.AdelicLevel.uniformizerUnit ℚ p : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)‖ < 1 := by
  have hq1 : 1 < ((Ideal.absNorm p.asIdeal : NNReal) : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  rw [NumberField.FinitePlace.norm_def, NumberField.AdelicLevel.valued_uniformizerUnit,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have : Multiplicative.toAdd (WithZero.unzero (WithZero.exp_ne_zero (a := (-1 : ℤ)))) = -1 := rfl
  rw [this]
  push_cast
  rw [zpow_neg_one]
  exact inv_lt_one_of_one_lt₀ hq1

theorem hdom_of_chamber (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (σ : Fin 3 → ℝ)
    (hσ : ∀ (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ), ‖((lam i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h12 : σ 2 < σ 1) :
    ‖(((![lam 1, lam 2] : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) 0) (NumberField.AdelicLevel.uniformizerUnit ℚ p) : ℂ)‖ <
      ‖(((![lam 1, lam 2] : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) 1) (NumberField.AdelicLevel.uniformizerUnit ℚ p) : ℂ)‖ := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hσ 1, hσ 2]
  exact Real.rpow_lt_rpow_of_exponent_gt (norm_pos_iff.mpr (Units.ne_zero _)) (norm_uniformizerUnit_lt_one p) h12

theorem continuous_leftBlockOf : Continuous fun X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) =>
    (Matrix.of fun a b => X a (Fin.castSucc b) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :=
  continuous_pi fun a => continuous_pi fun b => (continuous_apply_apply a (Fin.castSucc b))

theorem continuous_lastColOf : Continuous fun X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) => (X 0 2, X 1 2) :=
  (continuous_apply_apply 0 2).prodMk (continuous_apply_apply 1 2)

theorem continuous_argMap' (g : LocalGL3 p) :
    Continuous fun r : (p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
      (rowpad p r.2 * ((upperUnipotent3 r.1.1 r.1.2.1 r.1.2.2 * g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)),
        r.2⁻¹) :=
  (continuous_argMap p g).fst.prodMk (continuous_inv.comp continuous_snd)

end B1Glue
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber.B1Glue"

open B1Glue NumberField.StandardAddChar in
set_option maxHeartbeats 4000000 in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))
    (σ : Fin 3 → ℝ)
    (hσ : ∀ (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ), ‖((lam i a : ℂˣ) : ℂ)‖ = ‖(a : p.adicCompletion ℚ)‖ ^ (σ i))
    (h01 : σ 1 < σ 0) (h12 : σ 2 < σ 1)
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (T : LocalGL3 p) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p

    ∃ (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) (R : ℝ), IsOpen U ∧ (1 : GL (Fin 2) (p.adicCompletion ℚ)) ∈ U ∧
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) → IsCompact (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →

    ∀ (φsec : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (φsec = fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)) =>
        let Z : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) := X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))
        let s : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) := Matrix.of fun i j => Z i (Fin.castSucc j)
        let N : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) := (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) * Z
        ((μ₂ (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ)⁻¹ *
          (((lam 0 (Matrix.GeneralLinearGroup.det T) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det T : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)) *
          (Units.val '' (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))).indicator (fun _ => (1 : ℂ)) s *
          (charExt (lam 0) s.det)⁻¹ * ((‖s.det‖⁻¹ : ℝ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
              ^ (1 / 2 : ℂ) *
          charExt (lam 1) (((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * s.det / N 1 0) *
          charExt (lam 2) (N 1 0) * ((‖N 1 0‖⁻¹ : ℝ) : ℂ) *
          Φ ![N 1 1 / N 1 0, N 1 2 / N 1 0, (Z 0 0 * Z 1 2 - Z 0 2 * Z 1 0) / s.det]) →

    ∀ (𝔇 : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) → GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (𝔇 = fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
        ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
          φsec X (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p)) →

    (∀ g : LocalGL3 p,
      Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          rowFourier23 p (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹⁻¹
              (fun X => 𝔇 (X * ((g : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) h⁻¹)
              (godementArg p h) *
            ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
              ^ (1 / 2 : ℂ)) μ₂ ∧
      jacquetWhittaker3 p lam Φ (diagonal3 p ![1, -1, 1] * g * T) =
        ((lam 1 (-1) : ℂˣ) : ℂ) *
          godementWhittaker3 p (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ μ₂ (lam 0) 𝔇 g) ∧

    HasCompactSupport 𝔇 ∧
    (∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)), 𝔇 X k ≠ 0 →
      (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j)) ∈
        Units.val '' (K : Set (GL (Fin 2) (p.adicCompletion ℚ)))) ∧

    (∀ X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ),
      φsec X ∈ principalSeries2 p ![lam 1, lam 2] ∧
      ∀ g : GL (Fin 2) (p.adicCompletion ℚ), φsec X g ≠ 0 →
        ((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
          (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j))) 1 0 ≠ 0 ∧
        ‖((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j))) 1 1‖ ≤
          R * ‖((g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) *
            (Matrix.of fun i j => (X * (T : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) i (Fin.castSucc j))) 1 0‖) ∧

    ((K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ⊆ U →
      ∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), φsec X g ≠ 0 →
        (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 ≠ 0 ∧
          ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖ ≤
            R * ‖(g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖) ∧

    (∃ (m : ℕ) (φ₁ : Fin m → Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ)
        (φ₂ : Fin m → (p.adicCompletion ℚ) × (p.adicCompletion ℚ) → ℂ)
        (φ : Fin m → GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ i, IsLocallyConstant (φ₁ i) ∧ HasCompactSupport (φ₁ i)) ∧
      (∀ i, IsLocallyConstant (φ₂ i) ∧ HasCompactSupport (φ₂ i)) ∧
      (∀ i, φ i ∈ principalSeries2 p ![lam 1, lam 2] ∧
        ∃ s ∈ K, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), φ i g ≠ 0 →
          ((g * s : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 ≠ 0) ∧
      (∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)),
        𝔇 X k = ∑ i, φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) *
          ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
            φ i (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p)) ∧

      ∀ g : LocalGL3 p,
        (∀ i, Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
            rowFourier23 p (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹⁻¹
                (fun X => (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
              φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) *
                ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                  φ i (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p))
                  (X * ((g : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) h⁻¹)
                (godementArg p h) *
              ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ)
                ^ (1 / 2 : ℂ)) μ₂) ∧
        jacquetWhittaker3 p lam Φ (diagonal3 p ![1, -1, 1] * g * T) =
          ((lam 1 (-1) : ℂˣ) : ℂ) *
            ∑ i, godementWhittaker3 p (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ μ₂ (lam 0)
              (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
              φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) *
                ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                  φ i (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p)) g) := by
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ p
  letI : MeasurableSpace (Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) := borel _
  haveI : BorelSpace (Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) := ⟨rfl⟩
  obtain ⟨hsc, hlcG, -, -⟩ :=
    AutomorphicForm.secondCountableTopology_and_locallyCompactSpace_gl_two_and_isClosed_range_unipotentGL2Hom ℚ p
  haveI := hsc
  haveI := hlcG
  haveI : (selfDualHaarAt ℚ p : Measure (p.adicCompletion ℚ)).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt p
  obtain ⟨U, R, hUo, h1U, hD⟩ := godementDatum_mem_principalSeries2_and_support p lam hlam Φ hΦ T
  refine ⟨U, R, hUo, h1U, ?_⟩
  intro μ₂ hμ K hKo hKc φsec hφ 𝔇 h𝔇
  obtain ⟨hmeas, hlc, hcs, hsupp, hps, hsmall⟩ := hD μ₂ K hKo hKc φsec hφ
  have hB := cellSectionOf_antidiagonal3_mul_mul_eq_integral_godementDatum p lam Φ T μ₂ K hKo hKc φsec hφ
  have hCc := jacquetWhittaker3_diagonal3_mul_eq_mul_integral_psiLocal_cellSectionOf p lam hlam σ hσ h01 h12 Φ hΦ
  obtain ⟨m, φ₁, φ₂, φ, hφ₁, hφ₂, hφm, hsum, hdom⟩ :=
    exists_finset_pureTensor_godementDatum p lam hlam Φ hΦ T μ₂ K hKo hKc φsec hφ

  have hmeasD : Measurable (fun P : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
      (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k' : GL (Fin 2) (p.adicCompletion ℚ)) =>
        φsec X (antidiagonal2 p * k')) P.1 P.2) :=
    hmeas.comp (measurable_fst.prodMk ((continuous_const.mul continuous_snd).measurable))
  have hF : ∀ Y : LocalGL3 p, (fun Y : LocalGL3 p => cellSectionOf p lam Φ (antidiagonal3 p * Y * T)) Y =
      ((lam 0 (Matrix.GeneralLinearGroup.det Y) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det Y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
        ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
          (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k' : GL (Fin 2) (p.adicCompletion ℚ)) =>
              φsec X (antidiagonal2 p * k'))
            (rowpad p h * ((Y : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) h⁻¹ *
            ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ) ∂μ₂ :=
    fun Y => (hB Y).2.1

  have hH1 : ∀ g : LocalGL3 p,
      Integrable (fun r : (p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
          φsec (rowpad p r.2 * ((upperUnipotent3 r.1.1 r.1.2.1 r.1.2.2 * g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)))
              (antidiagonal2 p * r.2⁻¹) *
            ((lam 0 (Matrix.GeneralLinearGroup.det r.2) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det r.2 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ))
        ((jacquetHaar3 p).prod μ₂) := by
    intro g
    have hmint : Measurable (fun r : (p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
          φsec (rowpad p r.2 * ((upperUnipotent3 r.1.1 r.1.2.1 r.1.2.2 * g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)))
              (antidiagonal2 p * r.2⁻¹) *
            ((lam 0 (Matrix.GeneralLinearGroup.det r.2) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det r.2 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ)) :=
      ((hmeas.comp (continuous_argMap p g).measurable).mul
        ((continuous_lam_det p (lam 0) (hlam 0)).measurable.comp measurable_snd)).mul
        ((measurable_cpow_modulus_det p (3 / 2 : ℂ)).comp measurable_snd)
    rw [integrable_prod_iff hmint.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun q => (hB (upperUnipotent3 q.1 q.2.1 q.2.2 * g)).1, ?_⟩
    have heq : (fun q : p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ =>
        ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
          ‖φsec (rowpad p h * ((upperUnipotent3 q.1 q.2.1 q.2.2 * g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)))
              (antidiagonal2 p * h⁻¹) *
            ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ)‖ ∂μ₂) =
        fun q => ‖cellSectionOf p lam Φ (antidiagonal3 p * upperUnipotent3 q.1 q.2.1 q.2.2 * (g * T))‖ *
          (‖((lam 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)))⁻¹ := by
      funext q
      have h22 := (hB (upperUnipotent3 q.1 q.2.1 q.2.2 * g)).2.2
      simp only [rowpad] at h22 ⊢
      rw [h22, det_upperUnipotent3_mul]
      simp only [mul_assoc]
    rw [heq]
    exact (hCc (g * T)).1.norm.mul_const _

  have hA := fun g : LocalGL3 p =>
    integral_godementSection_upperUnipotent3_eq_godementWhittaker3_of_continuous p ((psiLocal ℚ p)⁻¹)
      (continuous_psiLocal_inv p) (lam 0)
      (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k' : GL (Fin 2) (p.adicCompletion ℚ)) => φsec X (antidiagonal2 p * k'))
      (fun Y : LocalGL3 p => cellSectionOf p lam Φ (antidiagonal3 p * Y * T)) μ₂ hF hmeasD g (hH1 g)
  have hDW : ∀ (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)),
      ∫ x : p.adicCompletion ℚ, (psiLocal ℚ p)⁻¹⁻¹ x * φsec X (antidiagonal2 p * (upperUnipotent2 p x * k))
        ∂(selfDualHaarAt ℚ p) = 𝔇 X k := by
    intro X k
    rw [h𝔇]
    congr 1
    funext x
    rw [psiLocal_inv_inv_apply, mul_assoc]
  refine ⟨fun g => ?_, ?_, ?_, hps, hsmall, ⟨m, φ₁, φ₂, φ, hφ₁, hφ₂, hφm, ?_, ?_⟩⟩
  ·
    have h := hA g
    simp only [hDW] at h
    refine ⟨h.1, ?_⟩
    rw [mul_assoc (diagonal3 p ![1, -1, 1]) g T, (hCc (g * T)).2, ← h.2]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun q => ?_)
    simp only [psiLocal_inv_inv_apply, mul_assoc]
  ·
    refine hcs.mono ?_
    intro X hX
    rw [Function.mem_support] at hX ⊢
    intro h0
    apply hX
    funext k
    rw [h𝔇]
    simp [h0]
  ·
    intro X k hk
    by_contra hnot
    apply hk
    have h0 : ∀ g, φsec X g = 0 := fun g => by
      by_contra hg
      exact hnot (hsupp X g hg)
    rw [h𝔇]
    simp [h0]
  ·
    obtain ⟨n1, hn1⟩ := exists_higherUnitsAt_eq_one p (lam 1) (hlam 1)
    obtain ⟨n2, hn2⟩ := exists_higherUnitsAt_eq_one p (lam 2) (hlam 2)
    have hcχ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p ((![n1, n2] : Fin 2 → ℕ) i),
        ((![lam 1, lam 2] : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) i) u = 1 := by
      intro i u hu
      fin_cases i
      · simpa using hn1 u (by simpa using hu)
      · simpa using hn2 u (by simpa using hu)
    have hint : ∀ (i : Fin m) (k : GL (Fin 2) (p.adicCompletion ℚ)),
        Integrable (fun x : p.adicCompletion ℚ => psiLocal ℚ p x * φ i (antidiagonal2 p * upperUnipotent2 p x * k))
          (selfDualHaarAt ℚ p) := by
      intro i k
      have hI := integrable_apply_antidiagonal_mul_unipotentGL2_mul_addChar_of_mem_principalSeries2 p ![lam 1, lam 2]
        ![n1, n2] hcχ (NumberField.AdelicLevel.uniformizerUnit ℚ p) (NumberField.AdelicLevel.valued_uniformizerUnit ℚ p)
        (hdom_of_chamber p lam σ hσ h12) (φ i) (hφm i).1 (antidiagonal2 p) (antidiagonal2_coe p) (psiLocal ℚ p)
        (continuous_psiLocal ℚ p) k (selfDualHaarAt ℚ p)
      refine hI.congr (ae_of_all _ fun x => ?_)
      dsimp only
      rw [mul_comm, upperUnipotent2_eq_unipotentGL2]
    intro X k
    rw [h𝔇]
    calc ∫ x : p.adicCompletion ℚ, psiLocal ℚ p x * φsec X (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p)
        = ∫ x : p.adicCompletion ℚ, ∑ i, (φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2)) *
            (psiLocal ℚ p x * φ i (antidiagonal2 p * upperUnipotent2 p x * k)) ∂(selfDualHaarAt ℚ p) := by
          congr 1
          funext x
          rw [hsum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = ∑ i, ∫ x : p.adicCompletion ℚ, (φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2)) *
            (psiLocal ℚ p x * φ i (antidiagonal2 p * upperUnipotent2 p x * k)) ∂(selfDualHaarAt ℚ p) :=
          integral_finset_sum _ (fun i _ => (hint i k).const_mul _)
      _ = ∑ i, φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) *
            ∫ x : p.adicCompletion ℚ, psiLocal ℚ p x * φ i (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_const_mul]
  ·
    intro g

    have hDim : ∀ i : Fin m, Measurable (fun P : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
        (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k' : GL (Fin 2) (p.adicCompletion ℚ)) =>
          φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) * φ i (antidiagonal2 p * k')) P.1 P.2) := by
      intro i
      exact (((((hφ₁ i).1.continuous.comp (continuous_leftBlockOf p)).measurable.comp measurable_fst)).mul
        (((hφ₂ i).1.continuous.comp (continuous_lastColOf p)).measurable.comp measurable_fst)).mul
        ((mem_principalSeries2_iff.mp (hφm i).1).1.continuous.measurable.comp
          ((continuous_const.mul continuous_snd).measurable))

    have hdomr : ∀ (i : Fin m) (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (h : GL (Fin 2) (p.adicCompletion ℚ)) (a b : ℂ),
        ‖φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) * φ i (antidiagonal2 p * h⁻¹) * a * b‖ ≤
          ‖φsec X (antidiagonal2 p * h⁻¹) * a * b‖ := by
      intro i X h a b
      simp only [norm_mul]
      have h1 := hdom i X (antidiagonal2 p * h⁻¹)
      simp only [norm_mul] at h1
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) (norm_nonneg _)
    have hH1i : ∀ i : Fin m,
        Integrable (fun r : (p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ) × GL (Fin 2) (p.adicCompletion ℚ) =>
          (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k' : GL (Fin 2) (p.adicCompletion ℚ)) =>
              φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) * φ i (antidiagonal2 p * k'))
            (rowpad p r.2 * ((upperUnipotent3 r.1.1 r.1.2.1 r.1.2.2 * g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)))
            r.2⁻¹ *
          ((lam 0 (Matrix.GeneralLinearGroup.det r.2) : ℂˣ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det r.2 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ))
        ((jacquetHaar3 p).prod μ₂) := by
      intro i
      beta_reduce
      refine (hH1 g).mono ?_ (ae_of_all _ fun r => ?_)
      · exact ((((hDim i).comp ((continuous_argMap' p g).measurable)).mul
          ((continuous_lam_det p (lam 0) (hlam 0)).measurable.comp measurable_snd)).mul
          ((measurable_cpow_modulus_det p (3 / 2 : ℂ)).comp measurable_snd)).aestronglyMeasurable
      · exact hdomr i (rowpad p r.2 * ((upperUnipotent3 r.1.1 r.1.2.1 r.1.2.2 * g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) r.2
          ((lam 0 (Matrix.GeneralLinearGroup.det r.2) : ℂˣ) : ℂ)
          (((modulus ((Matrix.GeneralLinearGroup.det r.2 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ))

    have hAi := fun i : Fin m =>
      integral_godementSection_upperUnipotent3_eq_godementWhittaker3_of_continuous p ((psiLocal ℚ p)⁻¹)
        (continuous_psiLocal_inv p) (lam 0)
        (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k' : GL (Fin 2) (p.adicCompletion ℚ)) =>
          φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) * φ i (antidiagonal2 p * k'))
        _ μ₂ (fun Y => rfl) (hDim i) g (hH1i i)
    have hDWi : ∀ (i : Fin m) (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)),
        ∫ x : p.adicCompletion ℚ, (psiLocal ℚ p)⁻¹⁻¹ x *
            (φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) *
              φ i (antidiagonal2 p * (upperUnipotent2 p x * k))) ∂(selfDualHaarAt ℚ p) =
          φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) *
            ∫ x : p.adicCompletion ℚ, psiLocal ℚ p x * φ i (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p) := by
      intro i X k
      have hfun : (fun x : p.adicCompletion ℚ => (psiLocal ℚ p)⁻¹⁻¹ x *
            (φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) *
              φ i (antidiagonal2 p * (upperUnipotent2 p x * k)))) =
          fun x : p.adicCompletion ℚ => (φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2)) *
            (psiLocal ℚ p x * φ i (antidiagonal2 p * upperUnipotent2 p x * k)) := by
        funext x
        rw [psiLocal_inv_inv_apply, ← mul_assoc (antidiagonal2 p) (upperUnipotent2 p x) k]
        ring
      rw [hfun, integral_const_mul]
    refine ⟨fun i => ?_, ?_⟩
    · have h := hAi i
      simp only [hDWi] at h
      exact h.1
    ·

      have step : ∀ i : Fin m,
          godementWhittaker3 p (psiLocal ℚ p)⁻¹ μ₂ (lam 0)
              (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k : GL (Fin 2) (p.adicCompletion ℚ)) =>
                φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) *
                  ∫ x : p.adicCompletion ℚ, NumberField.StandardAddChar.psiLocal ℚ p x *
                    φ i (antidiagonal2 p * upperUnipotent2 p x * k) ∂(selfDualHaarAt ℚ p)) g =
            ∫ q : p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ,
              (psiLocal ℚ p)⁻¹⁻¹ (q.1 + q.2.1) *
                (((lam 0 (Matrix.GeneralLinearGroup.det (upperUnipotent3 q.1 q.2.1 q.2.2 * g)) : ℂˣ) : ℂ) *
                  ((modulus ((Matrix.GeneralLinearGroup.det (upperUnipotent3 q.1 q.2.1 q.2.2 * g) : (p.adicCompletion ℚ)ˣ) :
                    p.adicCompletion ℚ) : ℝ) : ℂ) *
                  ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
                    (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k' : GL (Fin 2) (p.adicCompletion ℚ)) =>
                        φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) * φ i (antidiagonal2 p * k'))
                      (rowpad p h * ((upperUnipotent3 q.1 q.2.1 q.2.2 * g : GL (Fin 3) (p.adicCompletion ℚ)) :
                        Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) h⁻¹ *
                    ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
                    ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
                      (3 / 2 : ℂ) ∂μ₂) ∂(jacquetHaar3 p) := by
        intro i
        have h := hAi i
        simp only [hDWi] at h
        exact h.2.symm

      have hpieceY : ∀ (i : Fin m) (Y : LocalGL3 p),
          Integrable (fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
            (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k' : GL (Fin 2) (p.adicCompletion ℚ)) =>
                φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) * φ i (antidiagonal2 p * k'))
              (rowpad p h * ((Y : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) h⁻¹ *
            ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (3 / 2 : ℂ)) μ₂ := by
        intro i Y
        beta_reduce
        have hBY := (hB Y).1
        simp only [rowpad] at hBY ⊢
        refine hBY.mono ?_ (ae_of_all _ fun h => ?_)
        · have hc : Continuous fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
              (rowpad p h * ((Y : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)), h⁻¹) :=
            ((continuous_rowpad p).matrix_mul continuous_const).prodMk continuous_inv
          exact ((((hDim i).comp hc.measurable)).mul (continuous_lam_det p (lam 0) (hlam 0)).measurable).mul
            (measurable_cpow_modulus_det p (3 / 2 : ℂ)) |>.aestronglyMeasurable
        · exact hdomr i _ h _ _

      have hψq : Continuous fun q : p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ =>
          (psiLocal ℚ p)⁻¹⁻¹ (q.1 + q.2.1) := by
        have : (fun q : p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ => (psiLocal ℚ p)⁻¹⁻¹ (q.1 + q.2.1)) =
            fun q => psiLocal ℚ p (q.1 + q.2.1) := funext fun q => psiLocal_inv_inv_apply p _
        rw [this]
        exact (continuous_psiLocal ℚ p).comp (continuous_fst.add (continuous_fst.comp continuous_snd))
      have hGi : ∀ i : Fin m, Integrable (fun q : p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ =>
          (psiLocal ℚ p)⁻¹⁻¹ (q.1 + q.2.1) *
            (((lam 0 (Matrix.GeneralLinearGroup.det (upperUnipotent3 q.1 q.2.1 q.2.2 * g)) : ℂˣ) : ℂ) *
              ((modulus ((Matrix.GeneralLinearGroup.det (upperUnipotent3 q.1 q.2.1 q.2.2 * g) : (p.adicCompletion ℚ)ˣ) :
                p.adicCompletion ℚ) : ℝ) : ℂ) *
              ∫ h : GL (Fin 2) (p.adicCompletion ℚ),
                (fun (X : Matrix (Fin 2) (Fin 3) (p.adicCompletion ℚ)) (k' : GL (Fin 2) (p.adicCompletion ℚ)) =>
                    φ₁ i (Matrix.of fun a b => X a (Fin.castSucc b)) * φ₂ i (X 0 2, X 1 2) * φ i (antidiagonal2 p * k'))
                  (rowpad p h * ((upperUnipotent3 q.1 q.2.1 q.2.2 * g : GL (Fin 3) (p.adicCompletion ℚ)) :
                    Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) h⁻¹ *
                ((lam 0 (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
                ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^
                  (3 / 2 : ℂ) ∂μ₂)) (jacquetHaar3 p) := by
        intro i
        have hI := ((hH1i i).integral_prod_left).const_mul
          (((lam 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ))
        have hI2 := hI.bdd_mul (c := 1) hψq.measurable.aestronglyMeasurable
          (ae_of_all _ fun q => le_of_eq (norm_psiLocal_inv_inv p _))
        refine hI2.congr (ae_of_all _ fun q => ?_)
        simp only [det_upperUnipotent3_mul]
      rw [mul_assoc (diagonal3 p ![1, -1, 1]) g T, (hCc (g * T)).2]
      congr 1
      simp only [step]
      rw [← integral_finset_sum _ fun i _ => hGi i]
      refine integral_congr_ae (ae_of_all _ fun q => ?_)
      dsimp only
      rw [← Finset.mul_sum, ← Finset.mul_sum, psiLocal_inv_inv_apply]
      congr 1
      rw [← integral_finset_sum _ fun i _ => hpieceY i _]
      have hfull := (hB (upperUnipotent3 q.1 q.2.1 q.2.2 * g)).2.1
      rw [show antidiagonal3 p * upperUnipotent3 q.1 q.2.1 q.2.2 * (g * T) =
          antidiagonal3 p * (upperUnipotent3 q.1 q.2.1 q.2.2 * g) * T by simp only [mul_assoc], hfull]
      simp only [rowpad]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun h => ?_)
      dsimp only
      rw [hsum, Finset.sum_mul, Finset.sum_mul]

end
end S_LanglandsTunnell_CubicInduction_jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_jacquetWhittaker3_diagonal3_mul_eq_mul_godementWhittaker3_of_chamber (solution)
