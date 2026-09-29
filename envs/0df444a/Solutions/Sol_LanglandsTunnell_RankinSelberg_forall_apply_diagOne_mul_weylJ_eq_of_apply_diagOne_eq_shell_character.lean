-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_shell_character
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/1bf03606-49b5-5474-927e-6225800b53b6

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
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
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

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_shell_character

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_shell_character.E3cH"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_shell_character.E3cH"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_shell_character.E3cH"

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
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (η lam : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hlam : ∀ u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 → lam u = (η u)⁻¹)
    (E : ℂ) (e : ℤ)
    (hKW : letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ n : ℤ,
          ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              w (diagUnitGL2 ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n * u) * wJ) * ((((lam u : ℂˣ) : ℂ))⁻¹ * (((θ₀ u : ℂˣ) : ℂ))⁻¹) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) =
            E * (((θ₀ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)) ^ n *
              ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
                w (diagUnitGL2 ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ (e - n) * u)) * ((lam u : ℂˣ) : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))
    (m : ℤ) (v : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hv : v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)))
    (hvK : ∀ y : (p.adicCompletion ℚ)ˣ, v (diagOne y) =
      if Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-m) then ((η (y * (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ (-m)) : ℂˣ) : ℂ) else 0) :
    ∀ y : (p.adicCompletion ℚ)ˣ, v (diagOne y * wJ) =
      E * (((θ₀ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)) ^ (e - m) *
        (if Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(e - m)) then
          (((θ₀ * η⁻¹) (y * (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ (-(e - m))) : ℂˣ) : ℂ) else 0) := by
  intro y0
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  classical
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ)ˣ := E3cH.borelSpace_units p
  haveI hν : (selfDualHaarAt ℚ p).IsAddHaarMeasure := E3cH.isAddHaarMeasure_selfDualHaarAt p
  set τ : Measure (p.adicCompletion ℚ)ˣ := Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) with hτ
  haveI hτH : τ.IsHaarMeasure := by
    rw [hτ]; exact LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)
  set πu : (p.adicCompletion ℚ)ˣ := Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ with hπu
  have hvπ : ∀ k : ℤ, Valued.v (((πu ^ k : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) = WithZero.exp (-k) := by
    intro k
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπu, Units.val_mk0, hϖ, ← WithZero.exp_zsmul, smul_neg, zsmul_one, Int.cast_id]
  set f : (p.adicCompletion ℚ)ˣ → ℂ := fun y => v (diagOne y * wJ) with hf
  have hcw := central_of_mem_span p θ₀ w₂base hcentral v hv
  obtain ⟨hSm, huniq, hmass, hmod, -⟩ :=
    LanglandsTunnell.TateLocal.hasSum_setIntegral_shell_comap_val_mulMeasure_and_modulus_eq_of_valued_eq p

  have hA : ∀ u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 →
      ∀ x : GL (Fin 2) (p.adicCompletion ℚ), v (x * diagOne u⁻¹) = (((η u : ℂˣ) : ℂ))⁻¹ * v x := by
    intro u hu x
    have hmem : (fun x => v (x * diagOne u⁻¹)) - (((η u : ℂˣ) : ℂ))⁻¹ • v ∈
        Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) :=
      Submodule.sub_mem _ (comp_mul_mem_span p w₂base hv _) (Submodule.smul_mem _ _ hv)
    have hvu : Valued.v ((u⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
    have hzero := AutomorphicForm.WhittakerModel.eq_zero_of_forall_apply_diagOne_eq_zero_of_mem_span_of_localLevelOne p N hN
      w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm _ hmem (fun y => by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [← map_mul, hvK, hvK, Units.val_mul, Valuation.map_mul, hvu, mul_one]
        by_cases hy : Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-m)
        · rw [if_pos hy, if_pos hy, show y * u⁻¹ * πu ^ (-m) = y * πu ^ (-m) * u⁻¹ by rw [mul_right_comm], map_mul, map_inv,
            Units.val_mul, Units.val_inv_eq_inv_val]
          ring
        · rw [if_neg hy, if_neg hy]; ring)
    have := congrFun hzero x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    linear_combination this

  have hunit : ∀ u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 → ∀ y : (p.adicCompletion ℚ)ˣ,
      f (u * y) = ((θ₀ u : ℂˣ) : ℂ) * (((η u : ℂˣ) : ℂ))⁻¹ * f y := by
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

  set cof : ℤ → ℂ := fun n => f (πu ^ n) with hcof
  have hshape : ∀ n : ℤ, cof n = E * (((θ₀ πu : ℂˣ) : ℂ)) ^ n * (if e - n = m then (1 : ℂ) else 0) := by
    intro n
    have h := hKW v hv n
    have hL : ∫ u in U1, v (diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n * u) * wJ) *
          ((((lam u : ℂˣ) : ℂ))⁻¹ * (((θ₀ u : ℂˣ) : ℂ))⁻¹) ∂τ = (τ₁ : ℂ) * cof n := by
      rw [← hsetconst]
      refine setIntegral_congr_fun hU1m fun u hu => ?_
      have hu' : Valued.v (u : p.adicCompletion ℚ) = 1 := hu
      rw [diagUnitGL2_eq_diagOne, ← hπu, mul_comm (πu ^ n) u]
      have := hunit u hu' (πu ^ n)
      rw [hf] at this
      simp only at this
      rw [this, hcof, hlam u hu', Units.val_inv_eq_inv_val]
      have h1 : ((η u : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      have h2 : ((θ₀ u : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      field_simp
      rfl
    have hR : ∫ u in U1, v (diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ (e - n) * u)) * ((lam u : ℂˣ) : ℂ) ∂τ =
        (τ₁ : ℂ) * (if e - n = m then (1 : ℂ) else 0) := by
      rw [← hsetconst]
      refine setIntegral_congr_fun hU1m fun u hu => ?_
      have hu' : Valued.v (u : p.adicCompletion ℚ) = 1 := hu
      rw [diagUnitGL2_eq_diagOne, ← hπu, hvK, Units.val_mul, Valuation.map_mul, hu', mul_one, hvπ, hlam u hu']
      by_cases hnm : e - n = m
      · have hv' : (WithZero.exp (-(e - n)) : WithZero (Multiplicative ℤ)) = WithZero.exp (-m) := by rw [hnm]
        rw [if_pos hv', if_pos hnm, show πu ^ (e - n) * u * πu ^ (-m) = u by
          rw [hnm, mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul], Units.val_inv_eq_inv_val]
        have h1 : ((η u : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
        field_simp
      · have hv' : (WithZero.exp (-(e - n)) : WithZero (Multiplicative ℤ)) ≠ WithZero.exp (-m) :=
          fun h' => hnm (neg_injective (WithZero.exp_injective h'))
        rw [if_neg hv', if_neg hnm]; ring
    rw [hU1] at hL hR
    rw [hL, hR] at h
    have h' : (τ₁ : ℂ) * cof n = (τ₁ : ℂ) * (E * (((θ₀ πu : ℂˣ) : ℂ)) ^ n * (if e - n = m then (1 : ℂ) else 0)) := by
      rw [h]; ring
    exact mul_left_cancel₀ hτ₁ne h'

  obtain ⟨n, hn, -⟩ := huniq y0
  set u : (p.adicCompletion ℚ)ˣ := y0 * πu ^ (-n) with hu
  have hvu : Valued.v (u : p.adicCompletion ℚ) = 1 := by
    rw [hu, Units.val_mul, Valuation.map_mul, hvπ, hn, ← WithZero.exp_add]; simp
  have hyu : y0 = u * πu ^ n := by rw [hu, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have hfy : v (diagOne y0 * wJ) = ((θ₀ u : ℂˣ) : ℂ) * (((η u : ℂˣ) : ℂ))⁻¹ * cof n := by
    have := hunit u hvu (πu ^ n)
    rw [hf] at this
    simp only at this
    rw [hyu, this, hcof]
  rw [hfy, hshape]
  by_cases hnm : n = e - m
  · rw [if_pos (by omega), if_pos (by rw [hn, hnm]), show y0 * πu ^ (-(e - m)) = u by rw [hu, hnm], MonoidHom.mul_apply,
      MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, hnm]
    ring
  · have hne : Valued.v ((y0 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) ≠ WithZero.exp (-(e - m)) := by
      rw [hn]; intro h'; exact hnm (neg_injective (WithZero.exp_injective h'))
    rw [if_neg (by omega), if_neg hne]
    ring

end
end S_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_shell_character
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_shell_character (solution)
