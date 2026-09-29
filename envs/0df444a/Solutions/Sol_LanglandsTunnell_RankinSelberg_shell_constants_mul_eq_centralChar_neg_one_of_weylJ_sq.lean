-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.shell_constants_mul_eq_centralChar_neg_one_of_weylJ_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/53c5e004-fb8c-531f-9a08-9989fa86dbaa

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
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_mem_span_forall_diagOne_eq_of_shell_window_of_localLevelOne
import Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_shell_character
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_shell_constants_mul_eq_centralChar_neg_one_of_weylJ_sq

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors ENNReal NNReal
open NumberField.AdelicLevel (diagOne)

open scoped Classical

noncomputable section

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
    (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ) (hη : HasConductorExponentAt ℚ p η cη)
    (lam₁ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hlam₁ : ∀ u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 → lam₁ u = (η u)⁻¹)
    (E₁ : ℂ) (e₁ : ℤ)
    (hKW₁ : letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ n : ℤ,
          ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              w (diagUnitGL2 ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n * u) * wJ) * ((((lam₁ u : ℂˣ) : ℂ))⁻¹ * (((θ₀ u : ℂˣ) : ℂ))⁻¹) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) =
            E₁ * (((θ₀ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)) ^ n *
              ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
                w (diagUnitGL2 ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ (e₁ - n) * u)) * ((lam₁ u : ℂˣ) : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))
    (lam₂ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hlam₂ : ∀ u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 → lam₂ u = (θ₀ u)⁻¹ * η u)
    (E₂ : ℂ) (e₂ : ℤ)
    (hKW₂ : letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)), ∀ n : ℤ,
          ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
              w (diagUnitGL2 ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ n * u) * wJ) * ((((lam₂ u : ℂˣ) : ℂ))⁻¹ * (((θ₀ u : ℂˣ) : ℂ))⁻¹) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) =
            E₂ * (((θ₀ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)) ^ n *
              ∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
                w (diagUnitGL2 ((Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) ^ (e₂ - n) * u)) * ((lam₂ u : ℂˣ) : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))))
    :
    e₂ = e₁ ∧ E₁ * E₂ * (((θ₀ (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ) : ℂˣ) : ℂ)) ^ e₁ = ((θ₀ (-1) : ℂˣ) : ℂ) := by
  letI iF : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  classical
  set πu : (p.adicCompletion ℚ)ˣ := Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ with hπu
  have hvπ : ∀ k : ℤ, Valued.v (((πu ^ k : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ) = WithZero.exp (-k) := by
    intro k
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπu, Units.val_mk0, hϖ, ← WithZero.exp_zsmul, smul_neg, zsmul_one, Int.cast_id]

  obtain ⟨v₀, hv₀, hv₀K⟩ := AutomorphicForm.WhittakerModel.exists_mem_span_forall_diagOne_eq_of_shell_window_of_localLevelOne p N hN
    w₂base hw₂law hw₂K hw₂ne hw₂irr
    (fun y : (p.adicCompletion ℚ)ˣ => if Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-(0 : ℤ)) then ((η (y * πu ^ (-(0 : ℤ))) : ℂˣ) : ℂ) else 0)
    0 0 cη
    (fun y hy => by
      beta_reduce
      rw [if_neg (by rcases hy with hy | hy <;> [exact ne_of_gt hy; exact ne_of_lt hy])])
    (fun y u hu hu1 => by
      beta_reduce
      rw [Units.val_mul, Valuation.map_mul, hu, mul_one, show y * u * πu ^ (-(0 : ℤ)) = y * πu ^ (-(0 : ℤ)) * u by rw [mul_right_comm],
        map_mul, hη.1 u ⟨hu, ?_⟩, mul_one]
      rcases Nat.eq_zero_or_pos cη with h0 | hpos
      · exact Or.inl h0
      · exact Or.inr hu1)

  have h1 := LanglandsTunnell.RankinSelberg.forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_shell_character p θ₀ N hN w₂base
    hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ hπ hϖ η lam₁ hlam₁ E₁ e₁ hKW₁ 0 v₀ hv₀ hv₀K
  simp only [sub_zero] at h1

  have hwJ2 : wJ * wJ = Matrix.GeneralLinearGroup.scalar (Fin 2) (-1) := by
    apply Units.ext
    rw [Units.val_mul, hwJ]
    show !![(0 : p.adicCompletion ℚ), 1; -1, 0] * !![0, 1; -1, 0] = Matrix.diagonal (fun _ => (((-1 : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ))
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
  have hcw := central_of_mem_span p θ₀ w₂base hcentral v₀ hv₀
  have hv₀1 : v₀ (diagOne 1) = 1 := by
    rw [hv₀K]; simp
  have hback : ∀ y : (p.adicCompletion ℚ)ˣ, v₀ (diagOne y * wJ * wJ) = ((θ₀ (-1) : ℂˣ) : ℂ) * v₀ (diagOne y) := by
    intro y
    rw [mul_assoc, hwJ2, scalar_comm p, hcw]
  set c : ℂ := E₁ * (((θ₀ πu : ℂˣ) : ℂ)) ^ e₁ with hc
  have hc0 : c ≠ 0 := by
    intro hc0
    have hzero : ∀ y : (p.adicCompletion ℚ)ˣ, v₀ (diagOne y * wJ) = 0 := fun y => by rw [h1 y, hc0, zero_mul]
    have : v₀ (diagOne 1 * wJ * wJ) = 0 := by

      have hmem : (fun x => v₀ (x * wJ)) ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) := comp_mul_mem_span p w₂base hv₀ wJ
      have hz : (fun x => v₀ (x * wJ)) = 0 := AutomorphicForm.WhittakerModel.eq_zero_of_forall_apply_diagOne_eq_zero_of_mem_span_of_localLevelOne
        p N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm _ hmem (fun y => hzero y)
      have := congrFun hz (diagOne 1 * wJ)
      simpa using this
    rw [hback, hv₀1, mul_one] at this
    exact (Units.ne_zero _) this

  set v₁ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ := fun x => c⁻¹ * v₀ (x * wJ) with hv₁
  have hv₁V : v₁ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)) := by
    have : v₁ = c⁻¹ • fun x => v₀ (x * wJ) := by funext x; simp [hv₁]
    rw [this]; exact Submodule.smul_mem _ _ (comp_mul_mem_span p w₂base hv₀ wJ)
  have hv₁K : ∀ y : (p.adicCompletion ℚ)ˣ, v₁ (diagOne y) =
      if Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (-e₁) then (((θ₀ * η⁻¹) (y * πu ^ (-e₁)) : ℂˣ) : ℂ) else 0 := by
    intro y
    rw [hv₁]
    simp only
    rw [h1 y, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hlam₂' : ∀ u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 → lam₂ u = ((θ₀ * η⁻¹) u)⁻¹ := by
    intro u hu
    rw [hlam₂ u hu, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv]
  have h2 := LanglandsTunnell.RankinSelberg.forall_apply_diagOne_mul_weylJ_eq_of_apply_diagOne_eq_shell_character p θ₀ N hN w₂base
    hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcentral wJ hwJ hπ hϖ (θ₀ * η⁻¹) lam₂ hlam₂' E₂ e₂ hKW₂ e₁ v₁ hv₁V hv₁K

  have hlhs : v₁ (diagOne 1 * wJ) = c⁻¹ * ((θ₀ (-1) : ℂˣ) : ℂ) := by
    rw [hv₁]
    simp only
    rw [hback, hv₀1, mul_one]
  have hrhs := h2 1
  rw [hlhs, Units.val_one, Valuation.map_one, one_mul] at hrhs
  have hθη : θ₀ * (θ₀ * η⁻¹)⁻¹ = η := by
    ext u
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_rev, inv_inv]
    rw [mul_comm (η u), ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hθη] at hrhs
  by_cases he : e₂ = e₁
  · refine ⟨he, ?_⟩
    have hr := hrhs
    rw [he] at hr
    simp only [sub_self, neg_zero, zpow_zero, WithZero.exp_zero, if_true, eq_self_iff_true, one_mul, mul_one, map_one,
      Units.val_one] at hr
    have h3 := congrArg (fun z => c * z) hr
    simp only [← mul_assoc, mul_inv_cancel₀ hc0, one_mul] at h3
    rw [h3, hc]
    ring
  · exfalso
    rw [if_neg (by rw [← WithZero.exp_zero]; intro h'; exact he (by have := WithZero.exp_injective h'; omega)), mul_zero] at hrhs
    exact (mul_ne_zero (inv_ne_zero hc0) (Units.ne_zero _)) hrhs

end
end S_LanglandsTunnell_RankinSelberg_shell_constants_mul_eq_centralChar_neg_one_of_weylJ_sq
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_shell_constants_mul_eq_centralChar_neg_one_of_weylJ_sq (solution)
