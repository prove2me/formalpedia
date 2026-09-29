-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_inv_mul_indicator_shell_of_cuspidal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/2a589eaa-15e5-5026-afb1-c9c3a75d4d1e

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
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_AutomorphicForm_WhittakerModel_eq_zero_of_forall_apply_diagOne_eq_zero_of_mem_span_of_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_isSchwartzBruhat_tateFourier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_inv_mul_indicator_shell_of_cuspidal

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors ENNReal NNReal
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

namespace E3cH

variable (p : HeightOneSpectrum (𝓞 ℚ))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → p.adicCompletion ℚ))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem secondCountableTopology_units : SecondCountableTopology (p.adicCompletion ℚ)ˣ :=
  (Units.isEmbedding_val₀ (G₀ := p.adicCompletion ℚ)).secondCountableTopology

theorem borelSpace_units [MeasurableSpace (p.adicCompletion ℚ)] [BorelSpace (p.adicCompletion ℚ)] :
    BorelSpace (p.adicCompletion ℚ)ˣ :=
  ⟨by
    rw [(Units.isEmbedding_val₀ (G₀ := p.adicCompletion ℚ)).isInducing.eq_induced, borel_comap,
      ← BorelSpace.measurable_eq (α := p.adicCompletion ℚ)]
    rfl⟩

theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ p
    (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  set c : NNReal := (Ideal.absNorm p.asIdeal : NNReal) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ p) : ℝ) / 2)
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))).ne'
  have hdef : selfDualHaarAt ℚ p = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := rfl
  rw [hdef]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc0) ENNReal.coe_ne_top

end E3cH
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_inv_mul_indicator_shell_of_cuspidal.E3cH"

namespace GJJLGlueAlg

theorem natCast_zpow_cpow (N : ℕ) (hN : 0 < N) (k : ℤ) (z : ℂ) :
    (((N : ℂ)) ^ k) ^ z = (N : ℂ) ^ ((k : ℂ) * z) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : ((N : ℂ) ^ k) = (((N : ℝ) ^ k : ℝ) : ℂ) := by push_cast; rfl
  have hpos : (0 : ℝ) < (N : ℝ) ^ k := zpow_pos hNr k
  rw [h1, Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le, Real.log_zpow,
    Complex.cpow_def_of_ne_zero hNc, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

end GJJLGlueAlg
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_inv_mul_indicator_shell_of_cuspidal.E3cH"

namespace OSW

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G2" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem diagUnitGL2_eq_diagOne (a : (F)ˣ) : (diagUnitGL2 a : G2) = diagOne a := by
  apply Units.ext
  ext i j
  rw [NumberField.AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [diagUnitGL2]

theorem coe_diagOne (a : (F)ˣ) : ((diagOne a : G2) : Mat) = !![(a : F), 0; 0, 1] := by
  ext i j
  rw [NumberField.AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem diagOne_mul_weylJ (wJ : G2) (hwJ : (wJ : Mat) = !![0, 1; -1, 0]) (u : (F)ˣ) :
    diagOne u * wJ = wJ * Matrix.GeneralLinearGroup.scalar (Fin 2) u * diagOne u⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_diagOne, coe_diagOne, hwJ]
  have hsc : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : G2) : Mat) = Matrix.diagonal (fun _ => (u : F)) := rfl
  rw [hsc]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.vecHead, Matrix.vecTail]

theorem scalar_comm (z : (F)ˣ) (g : G2) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g := by
  apply Units.ext
  have hsc : ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G2) : Mat) = Matrix.diagonal (fun _ => (z : F)) := rfl
  rw [Units.val_mul, Units.val_mul, hsc, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]

theorem central_of_mem_span (θ₀ : (F)ˣ →* ℂˣ) (w₂base : G2 → ℂ)
    (hcentral : ∀ (z : (F)ˣ) (g : G2), w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (w : G2 → ℂ) (hw : w ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂base (g * h))) :
    ∀ (z : (F)ˣ) (g : G2), w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    intro z g
    show w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g * h) = ((θ₀ z : ℂˣ) : ℂ) * w₂base (g * h)
    rw [mul_assoc, hcentral]
  | zero => intro z g; simp
  | add x y _ _ hx hy => intro z g; simp only [Pi.add_apply, hx, hy, mul_add]
  | smul c x _ hx => intro z g; simp only [Pi.smul_apply, smul_eq_mul, hx]; ring

theorem comp_mul_mem_span (w₀ : G2 → ℂ)
    {w : G2 → ℂ} (hw : w ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₀ (g * h))) (h : G2) :
    (fun x => w (x * h)) ∈ Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₀ (g * h)) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h', rfl⟩ := hx
    refine Submodule.subset_span ⟨h * h', ?_⟩
    funext g; simp [mul_assoc]
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (fun g => (x + y) (g * h)) = (fun g => x (g * h)) + fun g => y (g * h) := rfl
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : (fun g => (a • x) (g * h)) = a • fun g => x (g * h) := rfl
    rw [this]; exact Submodule.smul_mem _ a hx

end OSW
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_inv_mul_indicator_shell_of_cuspidal.E3cH"

namespace OSW

theorem poly_eq_zero_of_eval_cpow (Nn : ℕ) (hN : 1 < Nn) (R : Polynomial ℂ) (σ : ℝ) (upper : Bool)
    (h : ∀ s : ℂ, (if upper then σ < s.re else s.re < σ) → R.eval ((Nn : ℂ) ^ (-s)) = 0) : R = 0 := by
  have hNr : (1 : ℝ) < Nn := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < Nn := zero_lt_one.trans hNr

  set t : ℕ → ℝ := fun n => if upper then σ + 1 + n else σ - 1 - n with ht
  have htcond : ∀ n : ℕ, (if upper then σ < ((t n : ℝ) : ℂ).re else ((t n : ℝ) : ℂ).re < σ) := by
    intro n
    rw [ht]
    cases upper <;> simp <;> linarith
  have hreal : ∀ n : ℕ, ((Nn : ℂ)) ^ (-((t n : ℝ) : ℂ)) = (((Nn : ℝ) ^ (-(t n)) : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_cpow hNpos.le]
    push_cast
    rfl
  have hinj : Function.Injective fun n : ℕ => ((Nn : ℂ)) ^ (-((t n : ℝ) : ℂ)) := by
    intro n₁ n₂ hn
    simp only [hreal] at hn
    have hn' : (Nn : ℝ) ^ (-(t n₁)) = (Nn : ℝ) ^ (-(t n₂)) := by exact_mod_cast hn
    have hlog := congrArg Real.log hn'
    rw [Real.log_rpow hNpos, Real.log_rpow hNpos] at hlog
    have hlogN : Real.log (Nn : ℝ) ≠ 0 := (Real.log_pos hNr).ne'
    have : t n₁ = t n₂ := by
      have := mul_right_cancel₀ hlogN hlog
      linarith
    rw [ht] at this
    cases upper <;> simp at this <;> exact_mod_cast this
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine Set.infinite_of_injective_forall_mem hinj fun n => ?_
  exact h _ (htcond n)

theorem laurent_eq_monomial_of_eqOn (Nn : ℕ) (hN : 1 < Nn) (P : Polynomial ℂ) (a k : ℤ) (c : ℂ) (σ : ℝ)
    (upper : Bool)
    (h : ∀ s : ℂ, (if upper then σ < s.re else s.re < σ) →
      (Nn : ℂ) ^ ((a : ℂ) * s) * P.eval ((Nn : ℂ) ^ (-s)) = c * (Nn : ℂ) ^ ((k : ℂ) * s)) :
    ∀ s : ℂ, (Nn : ℂ) ^ ((a : ℂ) * s) * P.eval ((Nn : ℂ) ^ (-s)) = c * (Nn : ℂ) ^ ((k : ℂ) * s) := by
  classical
  have hN0 : (Nn : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hN).ne'
  set K : ℤ := |a| + |k| with hK
  have hKa : 0 ≤ K - a := by have := le_abs_self a; have := abs_nonneg k; omega
  have hKk : 0 ≤ K - k := by have := le_abs_self k; have := abs_nonneg a; omega
  set R : Polynomial ℂ := Polynomial.X ^ (K - a).toNat * P - Polynomial.C c * Polynomial.X ^ (K - k).toNat with hR
  have hev : ∀ s : ℂ, R.eval ((Nn : ℂ) ^ (-s)) =
      (Nn : ℂ) ^ ((K : ℂ) * (-s)) * ((Nn : ℂ) ^ ((a : ℂ) * s) * P.eval ((Nn : ℂ) ^ (-s)) - c * (Nn : ℂ) ^ ((k : ℂ) * s)) := by
    intro s
    rw [hR, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← Complex.cpow_nat_mul, ← Complex.cpow_nat_mul]
    have e1 : (((K - a).toNat : ℕ) : ℂ) = (K : ℂ) - (a : ℂ) := by
      have := Int.toNat_of_nonneg hKa; exact_mod_cast this
    have e2 : (((K - k).toNat : ℕ) : ℂ) = (K : ℂ) - (k : ℂ) := by
      have := Int.toNat_of_nonneg hKk; exact_mod_cast this
    rw [e1, e2, show ((K : ℂ) - (a : ℂ)) * (-s) = (K : ℂ) * (-s) + (a : ℂ) * s by ring,
      show ((K : ℂ) - (k : ℂ)) * (-s) = (K : ℂ) * (-s) + (k : ℂ) * s by ring, Complex.cpow_add _ _ hN0, Complex.cpow_add _ _ hN0]
    ring
  have hR0 : R = 0 := by
    refine poly_eq_zero_of_eval_cpow Nn hN R σ upper fun s hs => ?_
    rw [hev s, h s hs, sub_self, mul_zero]
  intro s
  have := hev s
  rw [hR0, Polynomial.eval_zero] at this
  have hne : (Nn : ℂ) ^ ((K : ℂ) * (-s)) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hN0]; exact Complex.exp_ne_zero _
  have := (mul_eq_zero.1 this.symm).resolve_left hne
  exact sub_eq_zero.1 this

end OSW
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_inv_mul_indicator_shell_of_cuspidal.E3cH"

namespace OSW

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem exists_uniformizer : ∃ ϖ : p.adicCompletionIntegers ℚ,
    algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0 ∧
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := p.intValuation_exists_uniformizer
  have hv : Valued.v ((π : 𝓞 ℚ) : p.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) p π
    have h2 : p.valuation ℚ (π : ℚ) = WithZero.exp (-1 : ℤ) := by
      rw [show (π : ℚ) = algebraMap (𝓞 ℚ) ℚ π from rfl, HeightOneSpectrum.valuation_of_algebraMap]; exact hπ
    first
      | (rw [h1]; exact h2)
      | (simp only [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuedAdicCompletion_eq_valuation,
           Valued.valuedCompletion_apply, HeightOneSpectrum.adicValued_apply] at h1 ⊢
         first | exact h2 | (rw [h1]; exact h2) | simpa using h2)
  have hmem : ((π : 𝓞 ℚ) : p.adicCompletion ℚ) ∈ p.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hv, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.2 (by norm_num)
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · intro h0
    have : Valued.v ((π : 𝓞 ℚ) : p.adicCompletion ℚ) = 0 := by
      rw [show ((π : 𝓞 ℚ) : p.adicCompletion ℚ) = 0 from h0, map_zero]
    rw [hv] at this
    exact WithZero.coe_ne_zero this
  · exact hv

end OSW
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_inv_mul_indicator_shell_of_cuspidal.E3cH"

open OSW in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (wJ : GL (Fin 2) (p.adicCompletion ℚ)) (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0])

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)

    (E₀ : ℂ) (e₀ : ℤ)
    (hfe : letI := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e₀ : ℂ) * s)) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))))

    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0)
    :
    ∀ (m : ℤ),
    ∀ w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      (∀ y : (p.adicCompletion ℚ)ˣ,
        w₂ (diagOne y) = (((χ y : ℂˣ) : ℂ))⁻¹ * (if Valued.v (y : (p.adicCompletion ℚ)) = WithZero.exp (-m) then (1 : ℂ) else 0)) →
      ∀ y : (p.adicCompletion ℚ)ˣ,
        w₂ (diagOne y * wJ) =
          E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ (((e₀ : ℤ) : ℂ) / 2) * ((χ y : ℂˣ) : ℂ) * ((θ₀ y : ℂˣ) : ℂ) *
            (if Valued.v (y : (p.adicCompletion ℚ)) = WithZero.exp (-(e₀ - m)) then (1 : ℂ) else 0) := by
  intro m w₂ hw₂ hK y0
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  classical
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ)ˣ := E3cH.borelSpace_units p
  haveI hν : (selfDualHaarAt ℚ p).IsAddHaarMeasure := E3cH.isAddHaarMeasure_selfDualHaarAt p
  set τ : Measure (p.adicCompletion ℚ)ˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) with hτ
  haveI hτH : τ.IsHaarMeasure := by
    rw [hτ]; exact LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)
  obtain ⟨ϖ, hπ, hϖ⟩ := exists_uniformizer p

  set πu : (p.adicCompletion ℚ)ˣ := Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ with hπu
  have hvπ : ∀ k : ℤ, Valued.v (((πu ^ k : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) = WithZero.exp (-k) := by
    intro k
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπu, Units.val_mk0, hϖ, ← WithZero.exp_zsmul, smul_neg, zsmul_one, Int.cast_id]
  set f : (p.adicCompletion ℚ)ˣ → ℂ := fun y => w₂ (diagOne y * wJ) with hf
  have hcw := central_of_mem_span p θ₀ w₂base hcentral w₂ hw₂

  obtain ⟨hSm, huniq, hmass, hmod, -⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p

  have hA : ∀ u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 →
      ∀ x : GL (Fin 2) (p.adicCompletion ℚ), w₂ (x * diagOne u⁻¹) = ((χ u : ℂˣ) : ℂ) * w₂ x := by
    intro u hu x
    have hmem : (fun x => w₂ (x * diagOne u⁻¹)) - ((χ u : ℂˣ) : ℂ) • w₂ ∈
        Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) :=
      Submodule.sub_mem _ (comp_mul_mem_span p w₂base hw₂ _) (Submodule.smul_mem _ _ hw₂)
    have hvu : Valued.v ((u⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
    have hzero := AutomorphicForm.WhittakerModel.eq_zero_of_forall_apply_diagOne_eq_zero_of_mem_span_of_localLevelOne p N hN
      w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm _ hmem (fun y => by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [← map_mul, hK, hK, Units.val_mul, Valuation.map_mul, hvu, mul_one, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
        have hχu : ((χ u : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
        field_simp
        ring)
    have := congrFun hzero x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    linear_combination this

  have hunit : ∀ u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 → ∀ y : (p.adicCompletion ℚ)ˣ,
      f (u * y) = ((θ₀ u : ℂˣ) : ℂ) * ((χ u : ℂˣ) : ℂ) * f y := by
    intro u hu y
    rw [hf]
    simp only
    rw [mul_comm u y, map_mul, mul_assoc, diagOne_mul_weylJ p wJ hwJ u, ← mul_assoc, ← mul_assoc, scalar_comm p u (diagOne y * wJ),
      mul_assoc, hcw, hA u hu, mul_assoc]

  set U1 : Set (p.adicCompletion ℚ)ˣ := {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1} with hU1
  have hU1eq : U1 = {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-((0 : ℤ)))} := by
    rw [hU1, neg_zero, WithZero.exp_zero]
  have hU1m : MeasurableSet U1 := by rw [hU1eq]; exact hSm 0
  obtain ⟨-, hU1pos, hU1top⟩ := hmass 0
  rw [← hU1eq] at hU1pos hU1top
  set τ₁ : ℝ := (τ U1).toReal with hτ₁
  have hτ₁pos : 0 < τ₁ := by rw [hτ₁]; exact ENNReal.toReal_pos hU1pos.ne' hU1top.ne
  have hτ₁ne : (τ₁ : ℂ) ≠ 0 := by exact_mod_cast hτ₁pos.ne'
  have hsetconst : ∀ c : ℂ, ∫ u in U1, (fun _ => c) u ∂τ = (τ₁ : ℂ) * c := by
    intro c
    rw [setIntegral_const, Complex.real_smul, hτ₁, Measure.real]

  obtain ⟨cχ, hcχ⟩ := LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous ℚ p χ hχ.continuous
  obtain ⟨Eχ, eχ, hEχ, hKW⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_units_apply_diagUnitGL2_mul_weylJ_eq_mul_setIntegral_of_cuspidal p hπ hϖ
      θ₀ N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ hcusp χ cχ hcχ τ
  set cof : ℤ → ℂ := fun n => f (πu ^ n) with hcof
  have hshape : ∀ n : ℤ, cof n =
      Eχ * (((θ₀ πu : ℂˣ) : ℂ)) ^ n * (((χ (πu ^ (eχ - n)) : ℂˣ) : ℂ))⁻¹ * (if eχ - n = m then (1 : ℂ) else 0) := by
    intro n
    have h := hKW w₂ hw₂ n

    have hL : ∫ u in U1, w₂ (diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n * u) * wJ) *
          ((((χ u : ℂˣ) : ℂ))⁻¹ * (((θ₀ u : ℂˣ) : ℂ))⁻¹) ∂τ = (τ₁ : ℂ) * cof n := by
      rw [← hsetconst]
      refine setIntegral_congr_fun hU1m fun u hu => ?_
      have hu' : Valued.v (u : p.adicCompletion ℚ) = 1 := hu
      rw [diagUnitGL2_eq_diagOne, ← hπu, mul_comm (πu ^ n) u]
      have := hunit u hu' (πu ^ n)
      rw [hf] at this
      simp only at this
      rw [this, hcof]
      have h1 : ((χ u : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      have h2 : ((θ₀ u : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      field_simp
      rfl

    have hR : ∫ u in U1, w₂ (diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ (eχ - n) * u)) * ((χ u : ℂˣ) : ℂ) ∂τ =
        (τ₁ : ℂ) * ((((χ (πu ^ (eχ - n)) : ℂˣ) : ℂ))⁻¹ * (if eχ - n = m then (1 : ℂ) else 0)) := by
      rw [← hsetconst]
      refine setIntegral_congr_fun hU1m fun u hu => ?_
      have hu' : Valued.v (u : p.adicCompletion ℚ) = 1 := hu
      rw [diagUnitGL2_eq_diagOne, ← hπu, hK, Units.val_mul, Valuation.map_mul, hu', mul_one, hvπ, map_mul, Units.val_mul, mul_inv]
      have h1 : ((χ u : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      by_cases hnm : eχ - n = m
      · have hv' : (WithZero.exp (-(eχ - n)) : WithZero (Multiplicative ℤ)) = WithZero.exp (-m) := by rw [hnm]
        rw [if_pos hv', if_pos hnm]; field_simp
      · have hv' : (WithZero.exp (-(eχ - n)) : WithZero (Multiplicative ℤ)) ≠ WithZero.exp (-m) :=
          fun h' => hnm (neg_injective (WithZero.exp_injective h'))
        rw [if_neg hv', if_neg hnm]; ring
    rw [hU1] at hL hR
    rw [hL, hR, ← hπu] at h
    have h' : (τ₁ : ℂ) * cof n = (τ₁ : ℂ) * (Eχ * (((θ₀ πu : ℂˣ) : ℂ)) ^ n * (((χ (πu ^ (eχ - n)) : ℂˣ) : ℂ))⁻¹ *
        (if eχ - n = m then (1 : ℂ) else 0)) := by rw [h]; ring
    exact mul_left_cancel₀ hτ₁ne h'

  have hdecomp : ∀ y : (p.adicCompletion ℚ)ˣ, ∃ (n : ℤ) (u : (p.adicCompletion ℚ)ˣ),
      Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-n) ∧ Valued.v (u : p.adicCompletion ℚ) = 1 ∧ y = u * πu ^ n := by
    intro y
    obtain ⟨n, hn, -⟩ := huniq y
    refine ⟨n, y * πu ^ (-n), hn, ?_, ?_⟩
    · rw [Units.val_mul, Valuation.map_mul, hvπ, hn, ← WithZero.exp_add]; simp
    · rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  set n₀ : ℤ := eχ - m with hn₀
  have hcof0 : ∀ n : ℤ, n ≠ n₀ → cof n = 0 := by
    intro n hn
    rw [hshape, if_neg (by omega), mul_zero]
  have hcofn₀ : cof n₀ = Eχ * (((θ₀ πu : ℂˣ) : ℂ)) ^ n₀ * (((χ (πu ^ m) : ℂˣ) : ℂ))⁻¹ := by
    rw [hshape, if_pos (by omega), mul_one, show eχ - n₀ = m by omega]
  have hcofn₀ne : cof n₀ ≠ 0 := by
    rw [hcofn₀]
    exact mul_ne_zero (mul_ne_zero hEχ (zpow_ne_zero _ (Units.ne_zero _))) (inv_ne_zero (Units.ne_zero _))

  have hN1 : 1 < Ideal.absNorm p.asIdeal := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p
    exact_mod_cast this
  have hNpos : 0 < Ideal.absNorm p.asIdeal := zero_lt_one.trans hN1
  have hNc : (Ideal.absNorm p.asIdeal : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hmodC : ∀ (n : ℤ) (y : (p.adicCompletion ℚ)ˣ), Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-n) → ∀ z : ℂ,
      ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ z = (Ideal.absNorm p.asIdeal : ℂ) ^ (((-n : ℤ) : ℂ) * z) := by
    intro n y hy z
    rw [hmod n y hy]
    have := GJJLGlueAlg.natCast_zpow_cpow (Ideal.absNorm p.asIdeal) hNpos (-n) z
    push_cast at this ⊢
    exact this

  obtain ⟨P, Pd, mm, md, σ₀, σ₁, -, h2, -, h4, h5⟩ := hfe w₂ hw₂

  set A' : ℂ := cof n₀ * ((((θ₀ (πu ^ n₀) : ℂˣ) : ℂ)) * (((χ (πu ^ n₀) : ℂˣ) : ℂ)))⁻¹ with hA'
  have hprimal : ∀ s : ℂ, σ₀ < s.re →
      (Ideal.absNorm p.asIdeal : ℂ) ^ ((mm : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
        ((τ₁ : ℂ) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((((-m : ℤ)) : ℂ) * (-(1 / 2 : ℂ)))) * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-m : ℤ) : ℂ) * s) := by
    intro s hs
    rw [← h2 s hs]
    have hfun : (fun y : (p.adicCompletion ℚ)ˣ =>
        w₂ (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) =
        Set.indicator {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(m))}
          (fun _ => (Ideal.absNorm p.asIdeal : ℂ) ^ (((-m : ℤ) : ℂ) * (s - 1 / 2))) := by
      funext y
      rw [hK y]
      by_cases hy : Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-m)
      · rw [if_pos hy, Set.indicator_of_mem (show y ∈ {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(m))} from hy),
          hmodC m y hy]
        have : ((χ y : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
        field_simp
      · rw [if_neg hy, Set.indicator_of_notMem (show y ∉ {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(m))} from hy)]
        simp
    have hrm : τ.real {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(m))} = τ₁ := by
      rw [measureReal_def, (hmass m).1, ← hU1eq]
    rw [hfun, integral_indicator (hSm m), setIntegral_const, Complex.real_smul, hrm]
    rw [show ((-m : ℤ) : ℂ) * (s - 1 / 2) = ((-m : ℤ) : ℂ) * (-(1 / 2 : ℂ)) + ((-m : ℤ) : ℂ) * s by ring, Complex.cpow_add _ _ hNc]
    ring

  have hdual : ∀ s : ℂ, s.re < σ₁ →
      (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
        ((τ₁ : ℂ) * A' * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-n₀ : ℤ) : ℂ) * (1 / 2 : ℂ))) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n₀ : ℂ) * s) := by
    intro s hs
    rw [← h4 s hs]
    have hfun : (fun y : (p.adicCompletion ℚ)ˣ =>
        w₂ (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((θ₀ y : ℂˣ) : ℂ))⁻¹ * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)) =
        Set.indicator {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n₀))}
          (fun _ => A' * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-n₀ : ℤ) : ℂ) * (1 / 2 - s))) := by
      funext y
      obtain ⟨n, u, hyn, hu, hyu⟩ := hdecomp y
      have hfy : w₂ (diagOne y * wJ) = ((θ₀ u : ℂˣ) : ℂ) * ((χ u : ℂˣ) : ℂ) * cof n := by
        have := hunit u hu (πu ^ n)
        rw [hf] at this
        simp only at this
        rw [hyu, this, hcof]
      by_cases hn : n = n₀
      · subst hn
        rw [Set.indicator_of_mem (show y ∈ {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n₀))} from hyn),
          hmodC n₀ y hyn, hfy, hA']
        rw [hyu, map_mul, map_mul, Units.val_mul, Units.val_mul]
        have h1 : ((χ u : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
        have h2 : ((θ₀ u : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
        have h3 : ((χ (πu ^ n₀) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
        have h4' : ((θ₀ (πu ^ n₀) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
        field_simp
      · have hne : y ∉ {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n₀))} := by
          intro hy'
          exact hn (neg_injective (WithZero.exp_injective (hyn.symm.trans hy')))
        rw [Set.indicator_of_notMem hne, hfy, hcof0 n hn]
        simp
    have hrn : τ.real {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(n₀))} = τ₁ := by
      rw [measureReal_def, (hmass n₀).1, ← hU1eq]
    rw [hfun, integral_indicator (hSm n₀), setIntegral_const, Complex.real_smul, hrn]
    rw [show ((-n₀ : ℤ) : ℂ) * (1 / 2 - s) = ((-n₀ : ℤ) : ℂ) * (1 / 2 : ℂ) + ((n₀ : ℤ) : ℂ) * s by push_cast; ring,
      Complex.cpow_add _ _ hNc]
    push_cast
    ring

  set c₁ : ℂ := (τ₁ : ℂ) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((((-m : ℤ)) : ℂ) * (-(1 / 2 : ℂ))) with hc₁
  set c₂ : ℂ := (τ₁ : ℂ) * A' * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-n₀ : ℤ) : ℂ) * (1 / 2 : ℂ)) with hc₂
  have hP := laurent_eq_monomial_of_eqOn (Ideal.absNorm p.asIdeal) hN1 P mm (-m) c₁ σ₀ true
    (fun s hs => by rw [hc₁]; exact hprimal s (by simpa using hs))
  have hPd := laurent_eq_monomial_of_eqOn (Ideal.absNorm p.asIdeal) hN1 Pd md n₀ c₂ σ₁ false
    (fun s hs => by rw [hc₂]; exact hdual s (by simpa using hs))
  have hFE : ∀ s : ℂ, c₂ * (Ideal.absNorm p.asIdeal : ℂ) ^ (((n₀ : ℤ) : ℂ) * s) =
      E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e₀ : ℂ) * s) * (c₁ * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-m : ℤ) : ℂ) * s)) := by
    intro s
    rw [← hPd s, ← hP s, h5 s]
  have hc₁ne : c₁ ≠ 0 := by
    rw [hc₁]; exact mul_ne_zero hτ₁ne (by rw [Complex.cpow_def_of_ne_zero hNc]; exact Complex.exp_ne_zero _)
  have hA'ne : A' ≠ 0 := by
    rw [hA']; exact mul_ne_zero hcofn₀ne (inv_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)))
  have hc₂ne : c₂ ≠ 0 := by
    rw [hc₂]; exact mul_ne_zero (mul_ne_zero hτ₁ne hA'ne) (by rw [Complex.cpow_def_of_ne_zero hNc]; exact Complex.exp_ne_zero _)

  have h0 : c₂ = E₀ * c₁ := by
    have := hFE 0
    simp only [mul_zero, Complex.cpow_zero, mul_one] at this
    exact this
  have hE₀ : E₀ ≠ 0 := by
    intro hE; rw [hE, zero_mul] at h0; exact hc₂ne h0
  have h1 : (Ideal.absNorm p.asIdeal : ℂ) ^ (((n₀ : ℤ) : ℂ)) = (Ideal.absNorm p.asIdeal : ℂ) ^ (((e₀ - m : ℤ) : ℂ)) := by
    have h10 := hFE 1
    simp only [mul_one] at h10
    have h11 : E₀ * c₁ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((n₀ : ℤ) : ℂ) =
        E₀ * c₁ * ((Ideal.absNorm p.asIdeal : ℂ) ^ (e₀ : ℂ) * (Ideal.absNorm p.asIdeal : ℂ) ^ ((-m : ℤ) : ℂ)) := by
      linear_combination h10 - (Ideal.absNorm p.asIdeal : ℂ) ^ ((n₀ : ℤ) : ℂ) * h0
    have h12 := mul_left_cancel₀ (mul_ne_zero hE₀ hc₁ne) h11
    rw [h12, ← Complex.cpow_add _ _ hNc]
    congr 1
    push_cast
    ring
  have hn₀e : n₀ = e₀ - m := by
    have hNr : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := by exact_mod_cast hNpos
    have hNr1 : (Ideal.absNorm p.asIdeal : ℝ) ≠ 1 := by exact_mod_cast hN1.ne'
    rw [Complex.cpow_intCast, Complex.cpow_intCast] at h1
    have h1' := congrArg norm h1
    rw [norm_zpow, norm_zpow, Complex.norm_natCast] at h1'
    exact zpow_right_injective₀ hNr hNr1 h1'

  have hA'val : A' = E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ (((e₀ : ℤ) : ℂ) / 2) := by
    have h := h0
    rw [hc₂, hc₁] at h

    have h' : A' * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-n₀ : ℤ) : ℂ) * (1 / 2 : ℂ)) =
        E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((((-m : ℤ)) : ℂ) * (-(1 / 2 : ℂ))) := by
      have := mul_left_cancel₀ hτ₁ne (show (τ₁ : ℂ) * (A' * (Ideal.absNorm p.asIdeal : ℂ) ^ (((-n₀ : ℤ) : ℂ) * (1 / 2 : ℂ))) =
        (τ₁ : ℂ) * (E₀ * (Ideal.absNorm p.asIdeal : ℂ) ^ ((((-m : ℤ)) : ℂ) * (-(1 / 2 : ℂ)))) by rw [← mul_assoc, h]; ring)
      exact this
    have hpow : (Ideal.absNorm p.asIdeal : ℂ) ^ (((-n₀ : ℤ) : ℂ) * (1 / 2 : ℂ)) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hNc]; exact Complex.exp_ne_zero _
    rw [← eq_div_iff hpow] at h'
    rw [h', div_eq_iff hpow, mul_assoc, ← Complex.cpow_add _ _ hNc]
    congr 2
    rw [hn₀e]
    push_cast
    ring

  obtain ⟨n, u, hyn, hu, hyu⟩ := hdecomp y0
  have hfy : w₂ (diagOne y0 * wJ) = ((θ₀ u : ℂˣ) : ℂ) * ((χ u : ℂˣ) : ℂ) * cof n := by
    have := hunit u hu (πu ^ n)
    rw [hf] at this
    simp only at this
    rw [hyu, this, hcof]
  rw [hfy]
  by_cases hn : n = n₀
  · subst hn
    have hcofv : cof n₀ = A' * ((((θ₀ (πu ^ n₀) : ℂˣ) : ℂ)) * (((χ (πu ^ n₀) : ℂˣ) : ℂ))) := by
      rw [hA', mul_assoc, inv_mul_cancel₀ (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)), mul_one]
    rw [if_pos (by rw [hyn, hn₀e]), hcofv, hA'val, hyu, map_mul, map_mul, Units.val_mul, Units.val_mul]
    ring
  · have hne : Valued.v ((y0 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) ≠ WithZero.exp (-(e₀ - m)) := by
      rw [hyn]
      intro h'
      exact hn ((neg_injective (WithZero.exp_injective h')).trans hn₀e.symm)
    rw [if_neg hne, hcof0 n hn]
    simp

end
end S_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_inv_mul_indicator_shell_of_cuspidal
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_inv_mul_indicator_shell_of_cuspidal (solution)
