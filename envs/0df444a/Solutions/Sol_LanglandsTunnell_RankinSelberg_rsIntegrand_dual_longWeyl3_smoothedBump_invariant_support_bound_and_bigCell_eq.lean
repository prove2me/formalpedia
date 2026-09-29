-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.rsIntegrand_dual_longWeyl3_smoothedBump_invariant_support_bound_and_bigCell_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/bcaff2c1-4c3f-5b3f-8b6f-fd021a6933c8

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_rsIntegrand_dual_longWeyl3_smoothedBump_invariant_support_bound_and_bigCell_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section AlgebraEngine

open Matrix AutomorphicForm LanglandsTunnell.CubicInduction UnramifiedWhittaker

namespace JUnfoldAlg

variable {F : Type*} [Field F]

local notation "G" => (GL (Fin 2) F)
local notation "G₃" => (GL (Fin 3) F)
local notation "Mat" => (Matrix (Fin 2) (Fin 2) F)

theorem inv_mul_entries (g : G) :
    (g : Mat)⁻¹ 0 0 * (g : Mat) 0 0 + (g : Mat)⁻¹ 0 1 * (g : Mat) 1 0 = 1 ∧
    (g : Mat)⁻¹ 0 0 * (g : Mat) 0 1 + (g : Mat)⁻¹ 0 1 * (g : Mat) 1 1 = 0 ∧
    (g : Mat)⁻¹ 1 0 * (g : Mat) 0 0 + (g : Mat)⁻¹ 1 1 * (g : Mat) 1 0 = 0 ∧
    (g : Mat)⁻¹ 1 0 * (g : Mat) 0 1 + (g : Mat)⁻¹ 1 1 * (g : Mat) 1 1 = 1 := by
  have h : (g : Mat)⁻¹ * (g : Mat) = 1 := by
    rw [← Matrix.coe_units_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e := fun i j => congrFun (congrFun h i) j
  have e00 := e 0 0; have e01 := e 0 1; have e10 := e 1 0; have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at e00 e01 e10 e11
  exact ⟨e00, e01, e10, e11⟩

theorem longWeyl3_mul_longWeyl3 : (longWeyl3 : G₃) * longWeyl3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_mul, longWeyl3_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem transposeInv3_iotaGL (g : G) : transposeInv3 (iotaGL g) = iotaGL (transposeInvN (Fin 2) g) := by
  refine Units.ext ?_
  change (((iotaGL g)⁻¹ : G₃) : Matrix (Fin 3) (Fin 3) F)ᵀ = embedMat2 ((transposeInvN (Fin 2) g : G) : Mat)
  rw [← map_inv, coe_iotaGL, coe_transposeInvN]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.transpose_apply]

def dMat (m : G) : G₃ := longWeyl3 * iotaGL m * longWeyl3

theorem coe_dMat (m : G) :
    ((dMat m : G₃) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, (m : Mat) 1 1, (m : Mat) 1 0; 0, (m : Mat) 0 1, (m : Mat) 0 0] := by
  simp only [dMat, Units.val_mul, longWeyl3_coe, coe_iotaGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three]

theorem longWeyl3_mul_transposeInv3_iotaGL (g : G) :
    (longWeyl3 : G₃) * transposeInv3 (iotaGL g) = dMat (transposeInvN (Fin 2) g) * longWeyl3 := by
  rw [transposeInv3_iotaGL, dMat, mul_assoc, mul_assoc, longWeyl3_mul_longWeyl3, mul_one]

theorem dMat_mul_upperUnipotent3 (m : G) (u y : F) :
    dMat m * upperUnipotent3 u 0 y =
      upperUnipotent3 (u * (m : Mat)⁻¹ 1 1 + y * (m : Mat)⁻¹ 0 1) 0
        (u * (m : Mat)⁻¹ 1 0 + y * (m : Mat)⁻¹ 0 0) * dMat m := by
  obtain ⟨h1, h2, h3, h4⟩ := inv_mul_entries m
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_dMat, upperUnipotent3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  all_goals first
    | linear_combination u * h4 + y * h2
    | linear_combination u * h3 + y * h1
    | linear_combination (-u) * h4 + (-y) * h2
    | linear_combination (-u) * h3 + (-y) * h1

theorem dMat_transposeInvN_mul_upperUnipotent3 (g : G) (u y : F) :
    dMat (transposeInvN (Fin 2) g) * upperUnipotent3 u 0 y =
      upperUnipotent3 (u * (g : Mat) 1 1 + y * (g : Mat) 1 0) 0 (u * (g : Mat) 0 1 + y * (g : Mat) 0 0) *
        dMat (transposeInvN (Fin 2) g) := by
  have h := dMat_mul_upperUnipotent3 (transposeInvN (Fin 2) g) u y
  have hinv : ((transposeInvN (Fin 2) g : G) : Mat)⁻¹ = ((g : Mat))ᵀ := by
    rw [← Matrix.coe_units_inv, coe_inv_transposeInvN]
  simp only [hinv, Matrix.transpose_apply] at h
  exact h

theorem dMat_transposeInvN_unipotent (x : F) :
    dMat (transposeInvN (Fin 2) (unipotent x : G)) = upperUnipotent3 0 (-x) 0 := by
  refine Units.ext ?_
  have hu : (unipotent x : G) = unipotentGL2 x := Units.ext rfl
  rw [coe_dMat, upperUnipotent3_coe, coe_transposeInvN, hu]
  have hinv : (((unipotentGL2 x : G)⁻¹ : G) : Mat) = !![1, -x; 0, 1] := rfl
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

theorem dMat_mul (m n : G) : dMat (m * n) = dMat m * dMat n := by
  simp only [dMat, map_mul, mul_assoc]
  rw [← mul_assoc longWeyl3 longWeyl3, longWeyl3_mul_longWeyl3, one_mul]

theorem unipotent_mul_apply_one (x : F) (g : G) (j : Fin 2) :
    (((unipotent x * g : G)) : Mat) 1 j = (g : Mat) 1 j := by
  rw [Units.val_mul]
  change ((!![1, x; 0, 1] : Mat) * (g : Mat)) 1 j = (g : Mat) 1 j
  simp [Matrix.mul_apply, Fin.sum_univ_two]

section Weyl2

theorem w0_mul_transposeInvN_unipotent (w₀p : G) (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (x : F) :
    w₀p * transposeInvN (Fin 2) (unipotent x : G) = unipotent (-x) * w₀p := by
  have hu : ∀ t : F, (unipotent t : G) = unipotentGL2 t := fun t => Units.ext (α := Mat) rfl
  rw [hu, hu]
  refine Units.ext (α := Mat) ?_
  rw [Units.val_mul, Units.val_mul, coe_transposeInvN, hw₀p]
  have hinv : (((unipotentGL2 x : G)⁻¹ : G) : Mat) = !![1, -x; 0, 1] := rfl
  rw [hinv, unipotentGL2_coe]
  change !![(0 : F), 1; 1, 0] * (!![1, -x; 0, 1] : Mat)ᵀ = !![1, -x; 0, 1] * !![0, 1; 1, 0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

theorem w0_mul_transposeInvN_unipotent_mul (w₀p : G) (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (x : F) (g : G) :
    w₀p * transposeInvN (Fin 2) (unipotent x * g) = unipotent (-x) * (w₀p * transposeInvN (Fin 2) g) := by
  rw [transposeInvN_mul, ← mul_assoc, w0_mul_transposeInvN_unipotent w₀p hw₀p, mul_assoc]

theorem w0_mul_diagUnits2_inv (w₀p : G) (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (d a : Fˣ) :
    w₀p * diagUnits2 d⁻¹ a⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ * (w₀p * diagUnitGL2 (a * d⁻¹)) := by
  refine Units.ext (α := Mat) ?_
  simp only [Units.val_mul, hw₀p]
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  change !![(0 : F), 1; 1, 0] * !![(((d⁻¹ : Fˣ)) : F), 0; 0, (((a⁻¹ : Fˣ)) : F)] =
    Matrix.diagonal (fun _ => (((a⁻¹ : Fˣ)) : F)) * (!![(0 : F), 1; 1, 0] * !![(((a * d⁻¹ : Fˣ)) : F), 0; 0, 1])
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val]

end Weyl2

theorem transposeInvN_diagUnits2_mul_lowerUnipotentGL2 (d a : Fˣ) (x : F) :
    transposeInvN (Fin 2) (diagUnits2 d a * lowerUnipotentGL2 x : G) = diagUnits2 d⁻¹ a⁻¹ * unipotentGL2 (-x) := by
  refine Units.ext ?_
  rw [coe_transposeInvN, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  have h1 : (((lowerUnipotentGL2 x : G)⁻¹ : G) : Mat) = !![1, 0; -x, 1] := rfl
  have h2 : (((diagUnits2 d a : G)⁻¹ : G) : Mat) = !![(((d⁻¹ : Fˣ)) : F), 0; 0, (((a⁻¹ : Fˣ)) : F)] := rfl
  rw [h1, h2]
  change ((!![1, 0; -x, 1] : Mat) * !![(((d⁻¹ : Fˣ)) : F), 0; 0, (((a⁻¹ : Fˣ)) : F)])ᵀ =
    !![(((d⁻¹ : Fˣ)) : F), 0; 0, (((a⁻¹ : Fˣ)) : F)] * !![1, -x; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, mul_comm]

theorem dMat_diagUnits2_inv (d a : Fˣ) :
    dMat (diagUnits2 d⁻¹ a⁻¹ : G) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) d⁻¹ * iotaGL (diagUnits2 d (d * a⁻¹)) := by
  refine Units.ext ?_
  rw [coe_dMat, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_iotaGL]
  change !![(1 : F), 0, 0; 0, (((a⁻¹ : Fˣ)) : F), 0; 0, 0, (((d⁻¹ : Fˣ)) : F)] =
    Matrix.diagonal (fun _ => (((d⁻¹ : Fˣ)) : F)) * embedMat2 !![((d : Fˣ) : F), 0; 0, (((d * a⁻¹ : Fˣ)) : F)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.mul_apply, Fin.sum_univ_three, Units.val_inv_eq_inv_val]

theorem coe_dMat_unipotentGL2 (t : F) :
    ((dMat (unipotentGL2 t : G) : G₃) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 1, 0; 0, t, 1] := by
  rw [coe_dMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe]

theorem coe_inv_dMat_unipotentGL2 (t : F) :
    (((dMat (unipotentGL2 t : G))⁻¹ : G₃) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 1, 0; 0, -t, 1] := by
  have h : (dMat (unipotentGL2 t : G))⁻¹ = dMat (unipotentGL2 (-t) : G) := by
    rw [← mul_eq_one_iff_inv_eq, ← dMat_mul, ← unipotentGL2_add, add_neg_cancel]
    have : (unipotentGL2 (0 : F) : G) = 1 := Units.ext (by rw [unipotentGL2_coe]; ext i j; fin_cases i <;> fin_cases j <;> simp)
    rw [this, dMat, map_one, mul_one, longWeyl3_mul_longWeyl3]
  rw [h, coe_dMat_unipotentGL2]

theorem diagUnits2_split (d a : Fˣ) :
    (diagUnits2 d (d * a⁻¹) : G) = diagUnits2 d d * diagUnits2 1 a⁻¹ := by
  refine Units.ext ?_
  rw [Units.val_mul]
  change (!![((d : Fˣ) : F), 0; 0, (((d * a⁻¹ : Fˣ)) : F)] : Mat) =
    !![((d : Fˣ) : F), 0; 0, ((d : Fˣ) : F)] * !![(((1 : Fˣ)) : F), 0; 0, (((a⁻¹ : Fˣ)) : F)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem eq_unipotent_mul_diagUnits2_mul_lowerUnipotentGL2 (g : G) (h : (g : Mat) 1 1 ≠ 0) :
    g = unipotent ((g : Mat) 0 1 * ((g : Mat) 1 1)⁻¹) *
      (diagUnits2 (Units.mk0 ((g : Mat).det * ((g : Mat) 1 1)⁻¹)
          (mul_ne_zero (Matrix.GeneralLinearGroup.det g).ne_zero (inv_ne_zero h)))
        (Units.mk0 ((g : Mat) 1 1) h) *
        lowerUnipotentGL2 ((g : Mat) 1 0 * ((g : Mat) 1 1)⁻¹)) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  change (g : Mat) = !![1, (g : Mat) 0 1 * ((g : Mat) 1 1)⁻¹; 0, 1] *
    (!![(g : Mat).det * ((g : Mat) 1 1)⁻¹, 0; 0, (g : Mat) 1 1] * !![1, 0; (g : Mat) 1 0 * ((g : Mat) 1 1)⁻¹, 1])
  rw [Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

end JUnfoldAlg

end AlgebraEngine

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction NumberField.StandardAddChar UnramifiedWhittaker Topology

open scoped ENNReal NNReal

noncomputable section

namespace JUnfoldMain

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "K₂" => (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion ℚ p))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_localGL : SecondCountableTopology G :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance locallyCompactSpace_localGL' : LocallyCompactSpace G := locallyCompactSpace_localGL ℚ p

theorem coe_modulus_eq_norm (x : F) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem norm_psiPadicFun {q : ℕ} [Fact q.Prime] (y : ℚ_[q]) : ‖psiPadicFun y‖ = 1 := by
  obtain ⟨a, k, hk⟩ := exists_pPow_approx y
  rw [psiPadicFun_eq hk]
  have hcast : -(2 * (Real.pi : ℂ) * Complex.I) * ((a : ℂ) / (q : ℂ) ^ k)
      = ((-(2 * Real.pi * ((a : ℝ) / (q : ℝ) ^ k)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hcast, Complex.norm_exp_ofReal_mul_I]

theorem norm_psiLocal (x : F) : ‖psiLocal ℚ p x‖ = 1 := by
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv p : ℕ)) := ⟨(Rat.HeightOneSpectrum.primesEquiv p).2⟩
  rw [psiLocal_rat_eq_psiV, psiV_apply, psiPadic_apply]
  exact norm_psiPadicFun _

theorem norm_psiInv (x : F) : ‖(psiLocal ℚ p)⁻¹ x‖ = 1 := by
  rw [AddChar.inv_apply]
  exact norm_psiLocal p _

theorem continuous_psiInv : Continuous fun x : F => (psiLocal ℚ p)⁻¹ x := by
  have h : (fun x : F => (psiLocal ℚ p)⁻¹ x) = fun x => psiLocal ℚ p (-x) := funext fun x => AddChar.inv_apply _ _
  rw [h]
  exact (continuous_psiLocal ℚ p).comp continuous_neg

theorem psiInv_add (a b : F) : (psiLocal ℚ p)⁻¹ (a + b) = (psiLocal ℚ p)⁻¹ a * (psiLocal ℚ p)⁻¹ b :=
  AddChar.map_add_eq_mul _ _ _

theorem continuous_of_rightInvariant {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (f : Γ → ℂ) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ)) (hf : ∀ k ∈ U, ∀ g : Γ, f (g * k) = f g) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hopen : IsOpen ((fun k : Γ => g * k) '' (U : Set Γ)) := (Homeomorph.mulLeft g).isOpenMap _ hU
  have hmem : g ∈ (fun k : Γ => g * k) '' (U : Set Γ) := ⟨1, U.one_mem, mul_one g⟩
  have hev : (fun _ : Γ => f g) =ᶠ[𝓝 g] f := by
    filter_upwards [hopen.mem_nhds hmem] with h hh
    obtain ⟨k, hk, rfl⟩ := hh
    exact (hf k hk g).symm
  exact continuousAt_const.congr hev

theorem continuous_transposeInvN : Continuous fun g : G => transposeInvN (Fin 2) g := by
  rw [Units.continuous_iff]
  exact ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem continuous_transposeInv3 : Continuous fun g : G₃ => transposeInv3 g := by
  rw [Units.continuous_iff]
  exact ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem continuous_entry (i j : Fin 2) : Continuous fun g : G => (g : Mat) i j :=
  (Units.continuous_val).matrix_elem i j

theorem continuous_iotaGL : Continuous fun g : G => (iotaGL g : G₃) := by
  rw [Units.continuous_iff]
  have hc : ∀ i j : Fin 2, Continuous fun g : G => (g : Mat) i j := continuous_entry p
  have hci : ∀ i j : Fin 2, Continuous fun g : G => ((g⁻¹ : G) : Mat) i j := fun i j =>
    (Units.continuous_coe_inv).matrix_elem i j
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [Function.comp_apply, coe_iotaGL, embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
        Matrix.cons_val_fin_one] <;>
      first | exact continuous_const | exact hc _ _
  · have h : ∀ g : G, ((((iotaGL g : G₃)⁻¹ : G₃)) : Matrix (Fin 3) (Fin 3) F) = embedMat2 ((g⁻¹ : G) : Mat) :=
      fun g => by rw [← map_inv, coe_iotaGL]
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      first | exact continuous_const | exact hci _ _

theorem continuous_dMat_transposeInvN : Continuous fun g : G => (JUnfoldAlg.dMat (transposeInvN (Fin 2) g) : G₃) := by
  unfold JUnfoldAlg.dMat
  exact (continuous_const.mul ((continuous_iotaGL p).comp (continuous_transposeInvN p))).mul continuous_const

theorem continuous_modulus_det :
    Continuous fun g : G =>
      ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ) : ℂ) := by
  have : (fun g : G => ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) :
      ℝ) : ℂ)) = fun g : G => ((‖(g : Mat).det‖ : ℝ) : ℂ) := by
    funext g
    rw [coe_modulus_eq_norm, Matrix.GeneralLinearGroup.val_det_apply]
  rw [this]
  exact Complex.continuous_ofReal.comp (continuous_norm.comp (Units.continuous_val.matrix_det))

def phiHat (φ : F → ℂ) : F → ℂ := tateFourier (psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ

theorem phiHat_apply (φ : F → ℂ) (y : F) :
    phiHat p φ y = ∫ x, φ x * (psiLocal ℚ p)⁻¹ (x * y) ∂(selfDualHaarAt ℚ p) := rfl

theorem isAddHaarMeasure_selfDual : (selfDualHaarAt ℚ p : Measure F).IsAddHaarMeasure := by
  have hq : (Ideal.absNorm p.asIdeal : ℝ≥0) ≠ 0 := by
    have h : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p
    exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)
  have hc : ((Ideal.absNorm p.asIdeal : ℝ≥0) ^ (-(addCharLevel (psiLocal ℚ p) : ℝ) / 2)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne'
  change (((Ideal.absNorm p.asIdeal : ℝ≥0) ^ (-(addCharLevel (psiLocal ℚ p) : ℝ) / 2))
      • Measure.addHaarMeasure (integersPositiveCompacts ℚ p) : Measure F).IsAddHaarMeasure
  rw [ENNReal.smul_def]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc) ENNReal.coe_ne_top

theorem measurable_phiHat {φ : F → ℂ} (hφ : IsSchwartzBruhat φ) : Measurable (phiHat p φ) := by
  haveI := isAddHaarMeasure_selfDual p
  have hcont : Continuous (Function.uncurry fun (x y : F) => φ x * (psiLocal ℚ p)⁻¹ (x * y)) :=
    (hφ.1.continuous.comp continuous_fst).mul ((continuous_psiInv p).comp (continuous_fst.mul continuous_snd))
  have h := MeasureTheory.StronglyMeasurable.integral_prod_left (μ := (selfDualHaarAt ℚ p : Measure F))
    (f := fun (x y : F) => φ x * (psiLocal ℚ p)⁻¹ (x * y)) hcont.stronglyMeasurable
  exact h.measurable

theorem norm_phiHat_le {φ : F → ℂ} (hφ : IsSchwartzBruhat φ) (y : F) :
    ‖phiHat p φ y‖ ≤ ∫ x, ‖φ x‖ ∂(selfDualHaarAt ℚ p) := by
  rw [phiHat_apply]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [norm_mul, norm_psiInv, mul_one]

section ClosedForm

def Wsm (W₀ : G₃ → ℂ) (φ φ₁ : F → ℂ) : G₃ → ℂ :=
  fun X => ∫ u, ∫ y, W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p)

theorem dual_Wsm_iotaGL (W₀ : G₃ → ℂ) (hW₀law : IsGL3PsiWhittakerFn (psiLocal ℚ p)⁻¹ W₀) (φ φ₁ : F → ℂ) (g : G) :
    dualWhittakerFn3 (Wsm p W₀ φ φ₁) (iotaGL g) =
      W₀ (JUnfoldAlg.dMat (transposeInvN (Fin 2) g)) * (phiHat p φ ((g : Mat) 1 1) * phiHat p φ₁ ((g : Mat) 1 0)) := by
  rw [dualWhittakerFn3_apply]
  simp only [Wsm]
  set D : G₃ := JUnfoldAlg.dMat (transposeInvN (Fin 2) g) with hD
  have harg : ∀ u y : F, (longWeyl3 : G₃) * transposeInv3 (iotaGL g) * longWeyl3 * upperUnipotent3 u 0 y =
      upperUnipotent3 (u * (g : Mat) 1 1 + y * (g : Mat) 1 0) 0 (u * (g : Mat) 0 1 + y * (g : Mat) 0 0) * D := by
    intro u y
    rw [JUnfoldAlg.longWeyl3_mul_transposeInv3_iotaGL, mul_assoc (JUnfoldAlg.dMat _), JUnfoldAlg.longWeyl3_mul_longWeyl3,
      mul_one, JUnfoldAlg.dMat_transposeInvN_mul_upperUnipotent3]
  have hpt : ∀ u y : F, W₀ ((longWeyl3 : G₃) * transposeInv3 (iotaGL g) * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) =
      (W₀ D * (φ u * (psiLocal ℚ p)⁻¹ (u * (g : Mat) 1 1))) * (φ₁ y * (psiLocal ℚ p)⁻¹ (y * (g : Mat) 1 0)) := by
    intro u y
    rw [harg, hW₀law, add_zero, psiInv_add]
    ring
  simp_rw [hpt]
  have hin : ∀ u : F, ∫ y, (W₀ D * (φ u * (psiLocal ℚ p)⁻¹ (u * (g : Mat) 1 1))) * (φ₁ y * (psiLocal ℚ p)⁻¹ (y * (g : Mat) 1 0))
      ∂(selfDualHaarAt ℚ p) = (W₀ D * (φ u * (psiLocal ℚ p)⁻¹ (u * (g : Mat) 1 1))) * phiHat p φ₁ ((g : Mat) 1 0) := by
    intro u
    rw [integral_const_mul, phiHat_apply]
  simp_rw [hin]
  rw [integral_mul_const, integral_const_mul, ← phiHat_apply]
  ring

end ClosedForm

section KTwo

theorem isCompact_K2 : IsCompact ((K₂ : Subgroup G) : Set G) :=
  (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ top_ne_bot).1

theorem isOpen_K2 : IsOpen ((K₂ : Subgroup G) : Set G) :=
  (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ top_ne_bot).2

theorem mem_K2_iff (k : G) :
    k ∈ K₂ ↔ (∀ i j, Valued.v ((k : Mat) i j) ≤ 1) ∧ (∀ i j, Valued.v (((k⁻¹ : G) : Mat) i j) ≤ 1) := by
  rw [AdelicDock.mem_localLevelOne_iff]
  have key : ∀ m : Mat, AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m ↔ ∀ i j, Valued.v (m i j) ≤ 1 := by
    intro m
    constructor
    · intro h i j
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mp (h.integral i j)
    · intro h
      refine ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mpr (h i j), ?_, ?_⟩
      · rw [AdelicLevel.idealBound_top]; exact h 1 0
      · rw [AdelicLevel.idealBound_top]
        refine le_trans (Valuation.map_sub _ _ _) (max_le (h 1 1) ?_)
        rw [Valuation.map_one]
  rw [key, key]

private theorem toAdd_unzero_exp (n : ℤ) (h : (WithZero.exp n : WithZero (Multiplicative ℤ)) ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero h) = n :=
  rfl

theorem norm_eq_zpow {x : F} {n : ℤ} (h : Valued.v x = WithZero.exp n) :
    ‖x‖ = (Ideal.absNorm p.asIdeal : ℝ) ^ n := by
  rw [NumberField.FinitePlace.norm_def, h,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, toAdd_unzero_exp]
  push_cast
  rfl

theorem norm_eq_one_of_v_eq_one {x : F} (h : Valued.v x = 1) : ‖x‖ = 1 := by
  rw [← WithZero.exp_zero] at h
  rw [norm_eq_zpow p h, zpow_zero]

theorem modulus_eq_one_of_v_eq_one {x : F} (h : Valued.v x = 1) : modulus x = 1 := by
  have h1 : ((modulus x : ℝ≥0) : ℝ) = 1 := by rw [coe_modulus_eq_norm, norm_eq_one_of_v_eq_one p h]
  exact_mod_cast h1

theorem v_det_le_one {m : Mat} (h : ∀ i j, Valued.v (m i j) ≤ 1) : Valued.v m.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
  · rw [Valuation.map_mul]
    exact mul_le_one' (h 0 0) (h 1 1)
  · rw [Valuation.map_mul]
    exact mul_le_one' (h 0 1) (h 1 0)

theorem v_det_eq_one_of_mem_K2 {k : G} (hk : k ∈ K₂) :
    Valued.v ((Matrix.GeneralLinearGroup.det k : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) = 1 := by
  rw [mem_K2_iff] at hk
  have h1 : Valued.v ((Matrix.GeneralLinearGroup.det k : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) ≤ 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]; exact v_det_le_one p hk.1
  have h2 : Valued.v ((Matrix.GeneralLinearGroup.det k⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) ≤ 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]; exact v_det_le_one p hk.2
  have hprod : Valued.v ((Matrix.GeneralLinearGroup.det k : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) *
      Valued.v ((Matrix.GeneralLinearGroup.det k⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) = 1 := by
    rw [← Valuation.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Valuation.map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ))
      = Valued.v ((Matrix.GeneralLinearGroup.det k : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) *
          Valued.v ((Matrix.GeneralLinearGroup.det k⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) := hprod.symm
    _ ≤ Valued.v ((Matrix.GeneralLinearGroup.det k : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) * 1 :=
          mul_le_mul_right h2 _
    _ = _ := mul_one _

theorem modulus_det_eq_one_of_mem_K2 {k : G} (hk : k ∈ K₂) :
    modulus ((Matrix.GeneralLinearGroup.det k : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) = 1 :=
  modulus_eq_one_of_v_eq_one p (v_det_eq_one_of_mem_K2 p hk)

theorem diagUnits2_mem_K2 {x y : (HeightOneSpectrum.adicCompletion ℚ p)ˣ}
    (hx : Valued.v (x : F) = 1) (hy : Valued.v (y : F) = 1) : (diagUnits2 x y : G) ∈ K₂ := by
  rw [mem_K2_iff]
  have hxi : Valued.v (((x⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  have hyi : Valued.v (((y⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hy, inv_one]
  have hval : ((diagUnits2 x y : G) : Mat) = !![(x : F), 0; 0, (y : F)] := rfl
  have hinv : (((diagUnits2 x y : G)⁻¹ : G) : Mat) =
      !![(((x⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)) : F), 0; 0, (((y⁻¹ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ)) : F)] := rfl
  constructor
  · intro i j
    rw [hval]
    fin_cases i <;> fin_cases j <;> simp [hx, hy]
  · intro i j
    rw [hinv]
    fin_cases i <;> fin_cases j <;> simp [hx, hy, hxi, hyi]

end KTwo

end JUnfoldMain
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_rsIntegrand_dual_longWeyl3_smoothedBump_invariant_support_bound_and_bigCell_eq.JUnfoldMain"

namespace JUnfoldMain

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "G₃" => (GL (Fin 3) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "K₂" => (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤)
local notation "Fˣ" => ((HeightOneSpectrum.adicCompletion ℚ p)ˣ)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

def Wfun (W₀ : G₃ → ℂ) (φ φ₁ : F → ℂ) : G → ℂ := fun g => dualWhittakerFn3 (Wsm p W₀ φ φ₁) (iotaGL g)

def Ffun (w : G → ℂ) (w₀p : G) : G → ℂ := fun g =>
  ((modulus ((Matrix.GeneralLinearGroup.det g : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F) : ℝ) : ℂ) *
    w (w₀p * transposeInvN (Fin 2) g)

def Dg (g : G) : G₃ := JUnfoldAlg.dMat (transposeInvN (Fin 2) g)

theorem Wfun_eq (W₀ : G₃ → ℂ) (hW₀law : IsGL3PsiWhittakerFn (psiLocal ℚ p)⁻¹ W₀) (φ φ₁ : F → ℂ) (g : G) :
    Wfun p W₀ φ φ₁ g = W₀ (Dg p g) * (phiHat p φ ((g : Mat) 1 1) * phiHat p φ₁ ((g : Mat) 1 0)) :=
  dual_Wsm_iotaGL p W₀ hW₀law φ φ₁ g

theorem det_unipotent (x : F) : Matrix.GeneralLinearGroup.det (unipotent x : G) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change Matrix.det (!![1, x; 0, 1] : Mat) = ((1 : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : F)
  rw [Matrix.det_fin_two_of]
  simp

theorem W₀_Dg_unipotent_mul (W₀ : G₃ → ℂ) (hW₀law : IsGL3PsiWhittakerFn (psiLocal ℚ p)⁻¹ W₀) (x : F) (g : G) :
    W₀ (Dg p (unipotent x * g)) = psiLocal ℚ p x * W₀ (Dg p g) := by
  unfold Dg
  rw [transposeInvN_mul, JUnfoldAlg.dMat_mul, JUnfoldAlg.dMat_transposeInvN_unipotent, hW₀law, AddChar.inv_apply]
  congr 2
  abel

theorem Wfun_unipotent_mul (W₀ : G₃ → ℂ) (hW₀law : IsGL3PsiWhittakerFn (psiLocal ℚ p)⁻¹ W₀) (φ φ₁ : F → ℂ)
    (x : F) (g : G) :
    Wfun p W₀ φ φ₁ (unipotent x * g) = psiLocal ℚ p x * Wfun p W₀ φ φ₁ g := by
  rw [Wfun_eq p W₀ hW₀law, Wfun_eq p W₀ hW₀law, W₀_Dg_unipotent_mul p W₀ hW₀law, JUnfoldAlg.unipotent_mul_apply_one,
    JUnfoldAlg.unipotent_mul_apply_one, mul_assoc]

theorem Ffun_unipotent_mul (w : G → ℂ) (hwlaw : ∀ (x : F) (g : G), w (unipotent x * g) = psiLocal ℚ p x * w g)
    (w₀p : G) (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (x : F) (g : G) :
    Ffun p w w₀p (unipotent x * g) = psiLocal ℚ p (-x) * Ffun p w w₀p g := by
  unfold Ffun
  rw [map_mul, det_unipotent p, one_mul, JUnfoldAlg.w0_mul_transposeInvN_unipotent_mul w₀p hw₀p, hwlaw]
  ring

theorem prod_unipotent_mul (W₀ : G₃ → ℂ) (hW₀law : IsGL3PsiWhittakerFn (psiLocal ℚ p)⁻¹ W₀) (φ φ₁ : F → ℂ)
    (w : G → ℂ) (hwlaw : ∀ (x : F) (g : G), w (unipotent x * g) = psiLocal ℚ p x * w g)
    (w₀p : G) (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (x : F) (g : G) :
    Wfun p W₀ φ φ₁ (unipotent x * g) * Ffun p w w₀p (unipotent x * g) = Wfun p W₀ φ φ₁ g * Ffun p w w₀p g := by
  rw [Wfun_unipotent_mul p W₀ hW₀law, Ffun_unipotent_mul p w hwlaw w₀p hw₀p]
  have h1 : psiLocal ℚ p x * psiLocal ℚ p (-x) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  calc psiLocal ℚ p x * Wfun p W₀ φ φ₁ g * (psiLocal ℚ p (-x) * Ffun p w w₀p g)
      = (psiLocal ℚ p x * psiLocal ℚ p (-x)) * (Wfun p W₀ φ φ₁ g * Ffun p w w₀p g) := by ring
    _ = _ := by rw [h1, one_mul]

theorem dMat_unipotentGL2_mem_congruenceK1 (f : ℕ) {t : F} (ht : Valued.v t ≤ WithZero.exp (-(f : ℤ))) :
    (JUnfoldAlg.dMat (unipotentGL2 t : G) : G₃) ∈ congruenceK1 (𝓞 ℚ) ℚ p f := by
  have ht1 : Valued.v t ≤ 1 := by
    refine ht.trans ?_
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hneg : Valued.v (-t) ≤ 1 := by rwa [Valuation.map_neg]
  rw [mem_congruenceK1_iff, mem_localMaximalCompact3_iff, JUnfoldAlg.coe_dMat_unipotentGL2,
    JUnfoldAlg.coe_inv_dMat_unipotentGL2]
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, ?_, ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [ht1]
  · fin_cases i <;> fin_cases j <;> simp [ht1, hneg]
  · simp
  · simpa using ht
  · simp

theorem lowerUnipotentGL2_mem_K2 {x : F} (hx : Valued.v x ≤ 1) : (lowerUnipotentGL2 x : G) ∈ K₂ := by
  rw [mem_K2_iff]
  have hval : ((lowerUnipotentGL2 x : G) : Mat) = !![1, 0; x, 1] := rfl
  have hinv : (((lowerUnipotentGL2 x : G)⁻¹ : G) : Mat) = !![1, 0; -x, 1] := rfl
  have hneg : Valued.v (-x) ≤ 1 := by rwa [Valuation.map_neg]
  constructor
  · intro i j; rw [hval]; fin_cases i <;> fin_cases j <;> simp [hx]
  · intro i j; rw [hinv]; fin_cases i <;> fin_cases j <;> simp [hx, hneg]

theorem v_eq_one_of_bump_diag_ne_zero (W₀ : G₃ → ℂ)
    (hbumpS : ∀ h : G, W₀ (iotaGL h) ≠ 0 → ∃ x : F, ∃ k ∈ K₂, h = unipotentGL2 x * k)
    (d : Fˣ) (h : W₀ (iotaGL (diagUnits2 d d : G)) ≠ 0) :
    Valued.v (d : F) = 1 := by
  obtain ⟨x, k, hk, hdk⟩ := hbumpS _ h
  have hk' : k = (unipotentGL2 x : G)⁻¹ * diagUnits2 d d := by rw [hdk, inv_mul_cancel_left]
  rw [mem_K2_iff] at hk
  have h11 : ((k : G) : Mat) 1 1 = (d : F) := by
    rw [hk', Units.val_mul]
    change ((!![1, -x; 0, 1] : Mat) * !![((d : Fˣ) : F), 0; 0, (d : F)]) 1 1 = (d : F)
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hi11 : (((k⁻¹ : G)) : Mat) 1 1 = (((d⁻¹ : Fˣ)) : F) := by
    rw [hk', mul_inv_rev, inv_inv, Units.val_mul]
    change ((!![(((d⁻¹ : Fˣ)) : F), 0; 0, (((d⁻¹ : Fˣ)) : F)] : Mat) * !![1, x; 0, 1]) 1 1 = _
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hle : Valued.v (d : F) ≤ 1 := by simpa [h11] using hk.1 1 1
  have hge : Valued.v (((d⁻¹ : Fˣ)) : F) ≤ 1 := by simpa [hi11] using hk.2 1 1
  rw [Units.val_inv_eq_inv_val, map_inv₀] at hge
  have hne : Valued.v (d : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr d.ne_zero
  have := (inv_le_one₀ ((zero_lt_iff).mpr hne)).mp hge
  exact le_antisymm hle this

theorem W₀_Dg_torus (ω : Fˣ →* ℂˣ) (f : ℕ) (W₀ : G₃ → ℂ)
    (hcentral : ∀ (t : Fˣ) (h : G₃),
      W₀ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W₀ h)
    (hK1 : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : G₃, W₀ (g * k) = W₀ g)
    (hbumpK : ∀ k ∈ K₂, ∀ h : G, W₀ (iotaGL (h * k)) = W₀ (iotaGL h))
    (d a : Fˣ) (x : F) (ha : Valued.v (a : F) = 1) (hx : Valued.v x ≤ WithZero.exp (-(f : ℤ))) :
    W₀ (JUnfoldAlg.dMat (diagUnits2 d⁻¹ a⁻¹ * unipotentGL2 (-x) : G)) =
      ((ω d⁻¹ : ℂˣ) : ℂ) * W₀ (iotaGL (diagUnits2 d d : G)) := by
  have hnegx : Valued.v (-x) ≤ WithZero.exp (-(f : ℤ)) := by rwa [Valuation.map_neg]
  rw [JUnfoldAlg.dMat_mul, hK1 _ (dMat_unipotentGL2_mem_congruenceK1 p f hnegx), JUnfoldAlg.dMat_diagUnits2_inv,
    hcentral, JUnfoldAlg.diagUnits2_split]
  have hainv : Valued.v (((a⁻¹ : Fˣ)) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one]
  have hk : (diagUnits2 1 a⁻¹ : G) ∈ K₂ := diagUnits2_mem_K2 p (by simp) hainv
  rw [hbumpK _ hk]

theorem W₀_iotaGL_diag (W₀ : G₃ → ℂ)
    (hbumpK : ∀ k ∈ K₂, ∀ h : G, W₀ (iotaGL (h * k)) = W₀ (iotaGL h))
    (hbumpS : ∀ h : G, W₀ (iotaGL h) ≠ 0 → ∃ x : F, ∃ k ∈ K₂, h = unipotentGL2 x * k)
    (hbump1 : W₀ (iotaGL 1) = 1) (d : Fˣ) :
    W₀ (iotaGL (diagUnits2 d d : G)) = if Valued.v (d : F) = 1 then 1 else 0 := by
  split_ifs with hd
  · have hk : (diagUnits2 d d : G) ∈ K₂ := diagUnits2_mem_K2 p hd hd
    have := hbumpK _ hk 1
    rw [one_mul] at this
    rw [this, hbump1]
  · by_contra hne
    exact hd (v_eq_one_of_bump_diag_ne_zero p W₀ hbumpS d hne)

theorem support_prod (ω : Fˣ →* ℂˣ) (f : ℕ) (W₀ : G₃ → ℂ)
    (hW₀law : IsGL3PsiWhittakerFn (psiLocal ℚ p)⁻¹ W₀)
    (hcentral : ∀ (t : Fˣ) (h : G₃),
      W₀ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W₀ h)
    (hK1 : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : G₃, W₀ (g * k) = W₀ g)
    (hbumpK : ∀ k ∈ K₂, ∀ h : G, W₀ (iotaGL (h * k)) = W₀ (iotaGL h))
    (hbumpS : ∀ h : G, W₀ (iotaGL h) ≠ 0 → ∃ x : F, ∃ k ∈ K₂, h = unipotentGL2 x * k)
    (φ φ₁ : F → ℂ)
    (hat2 : ∀ y : F, Valued.v y ≠ 1 → phiHat p φ y = 0)
    (hat4 : ∀ y : F, phiHat p φ₁ y ≠ 0 → Valued.v y ≤ WithZero.exp (-(f : ℤ)))
    (w : G → ℂ) (w₀p : G) (g : G)
    (hg : Wfun p W₀ φ φ₁ g * Ffun p w w₀p g ≠ 0) :
    ∃ (x : F) (u : G), u ∈ K₂ ∧ g = unipotent x * u := by
  have hW : Wfun p W₀ φ φ₁ g ≠ 0 := left_ne_zero_of_mul hg
  rw [Wfun_eq p W₀ hW₀law] at hW
  have hD : W₀ (Dg p g) ≠ 0 := left_ne_zero_of_mul hW
  have hφ0 : phiHat p φ ((g : Mat) 1 1) ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hW)
  have hφ10 : phiHat p φ₁ ((g : Mat) 1 0) ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul hW)
  have h11 : Valued.v ((g : Mat) 1 1) = 1 := by
    by_contra hne
    exact hφ0 (hat2 _ hne)
  have h11ne : (g : Mat) 1 1 ≠ 0 := fun h0 => by
    rw [h0, Valuation.map_zero] at h11
    exact zero_ne_one h11
  have h10 : Valued.v ((g : Mat) 1 0) ≤ WithZero.exp (-(f : ℤ)) := hat4 _ hφ10

  set A : Fˣ := Units.mk0 ((g : Mat) 1 1) h11ne with hA
  set Dd : Fˣ := Units.mk0 ((g : Mat).det * ((g : Mat) 1 1)⁻¹)
    (mul_ne_zero (Matrix.GeneralLinearGroup.det g).ne_zero (inv_ne_zero h11ne)) with hDd
  set xr : F := (g : Mat) 1 0 * ((g : Mat) 1 1)⁻¹ with hxr
  set x₀ : F := (g : Mat) 0 1 * ((g : Mat) 1 1)⁻¹ with hx₀
  set g' : G := diagUnits2 Dd A * lowerUnipotentGL2 xr with hg'
  have hdec : g = unipotent x₀ * g' := JUnfoldAlg.eq_unipotent_mul_diagUnits2_mul_lowerUnipotentGL2 g h11ne
  have hxrv : Valued.v xr ≤ WithZero.exp (-(f : ℤ)) := by
    rw [hxr, Valuation.map_mul, map_inv₀, h11, inv_one, mul_one]
    exact h10
  have hxr1 : Valued.v xr ≤ 1 := by
    refine hxrv.trans ?_
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hAv : Valued.v (A : F) = 1 := h11

  have hDg' : W₀ (Dg p g') ≠ 0 := by
    have h := W₀_Dg_unipotent_mul p W₀ hW₀law x₀ g'
    rw [← hdec] at h
    intro h0
    rw [h0, mul_zero] at h
    exact hD h
  have hDv : Valued.v (Dd : F) = 1 := by
    unfold Dg at hDg'
    rw [hg', JUnfoldAlg.transposeInvN_diagUnits2_mul_lowerUnipotentGL2,
      W₀_Dg_torus p ω f W₀ hcentral hK1 hbumpK Dd A xr hAv hxrv] at hDg'
    have hb : W₀ (iotaGL (diagUnits2 Dd Dd : G)) ≠ 0 := right_ne_zero_of_mul hDg'
    exact v_eq_one_of_bump_diag_ne_zero p W₀ hbumpS Dd hb
  refine ⟨x₀, g', ?_, hdec⟩
  rw [hg']
  exact (K₂).mul_mem (diagUnits2_mem_K2 p hDv hAv) (lowerUnipotentGL2_mem_K2 p hxr1)

theorem measurable_prod (W₀ : G₃ → ℂ) (hW₀law : IsGL3PsiWhittakerFn (psiLocal ℚ p)⁻¹ W₀)
    (hW₀sm : ∃ Uv : Subgroup G₃, IsOpen (Uv : Set G₃) ∧ ∀ k ∈ Uv, ∀ g : G₃, W₀ (g * k) = W₀ g)
    (φ φ₁ : F → ℂ) (hφ : IsSchwartzBruhat φ) (hφ₁ : IsSchwartzBruhat φ₁)
    (w : G → ℂ) (hwsm : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, w (g * k) = w g)
    (w₀p : G) :
    Measurable (fun g : G => Wfun p W₀ φ φ₁ g * Ffun p w w₀p g) := by
  obtain ⟨Uv, hUv, hUvinv⟩ := hW₀sm
  obtain ⟨U, hU, hUinv⟩ := hwsm
  have hW₀c : Continuous W₀ := continuous_of_rightInvariant W₀ Uv hUv hUvinv
  have hwc : Continuous w := continuous_of_rightInvariant w U hU hUinv
  have h1 : (Wfun p W₀ φ φ₁) = fun g => W₀ (Dg p g) * (phiHat p φ ((g : Mat) 1 1) * phiHat p φ₁ ((g : Mat) 1 0)) :=
    funext (Wfun_eq p W₀ hW₀law φ φ₁)
  rw [h1]
  refine Measurable.mul (Measurable.mul ?_ (Measurable.mul ?_ ?_)) ?_
  · exact (hW₀c.comp (continuous_dMat_transposeInvN p)).measurable
  · exact (measurable_phiHat p hφ).comp (continuous_entry p 1 1).measurable
  · exact (measurable_phiHat p hφ₁).comp (continuous_entry p 1 0).measurable
  · unfold Ffun
    exact ((continuous_modulus_det p).mul (hwc.comp (continuous_const.mul (continuous_transposeInvN p)))).measurable

theorem exists_bound_prod (W₀ : G₃ → ℂ) (hW₀law : IsGL3PsiWhittakerFn (psiLocal ℚ p)⁻¹ W₀)
    (hW₀sm : ∃ Uv : Subgroup G₃, IsOpen (Uv : Set G₃) ∧ ∀ k ∈ Uv, ∀ g : G₃, W₀ (g * k) = W₀ g)
    (φ φ₁ : F → ℂ) (hφ : IsSchwartzBruhat φ) (hφ₁ : IsSchwartzBruhat φ₁)
    (w : G → ℂ) (hwsm : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, w (g * k) = w g)
    (w₀p : G) :
    ∃ C : ℝ, ∀ g ∈ (K₂ : Subgroup G), ‖Wfun p W₀ φ φ₁ g * Ffun p w w₀p g‖ ≤ C := by
  obtain ⟨Uv, hUv, hUvinv⟩ := hW₀sm
  obtain ⟨U, hU, hUinv⟩ := hwsm
  have hW₀c : Continuous W₀ := continuous_of_rightInvariant W₀ Uv hUv hUvinv
  have hwc : Continuous w := continuous_of_rightInvariant w U hU hUinv
  obtain ⟨C₁, hC₁⟩ := (isCompact_K2 p).exists_bound_of_continuousOn
    ((hW₀c.comp (continuous_dMat_transposeInvN p)).continuousOn (s := ((K₂ : Subgroup G) : Set G)))
  have hFc : Continuous (Ffun p w w₀p) := by
    unfold Ffun
    exact (continuous_modulus_det p).mul (hwc.comp (continuous_const.mul (continuous_transposeInvN p)))
  obtain ⟨C₄, hC₄⟩ := (isCompact_K2 p).exists_bound_of_continuousOn (hFc.continuousOn (s := ((K₂ : Subgroup G) : Set G)))
  set C₂ : ℝ := ∫ x, ‖φ x‖ ∂(selfDualHaarAt ℚ p)
  set C₃ : ℝ := ∫ x, ‖φ₁ x‖ ∂(selfDualHaarAt ℚ p)
  refine ⟨max C₁ 0 * (C₂ * C₃) * max C₄ 0, fun g hg => ?_⟩
  rw [Wfun_eq p W₀ hW₀law, norm_mul, norm_mul, norm_mul]
  have h1 : ‖W₀ (Dg p g)‖ ≤ max C₁ 0 := (hC₁ g hg).trans (le_max_left _ _)
  have h2 : ‖phiHat p φ ((g : Mat) 1 1)‖ ≤ C₂ := norm_phiHat_le p hφ _
  have h3 : ‖phiHat p φ₁ ((g : Mat) 1 0)‖ ≤ C₃ := norm_phiHat_le p hφ₁ _
  have h4 : ‖Ffun p w w₀p g‖ ≤ max C₄ 0 := (hC₄ g hg).trans (le_max_left _ _)
  have h23 : ‖phiHat p φ ((g : Mat) 1 1)‖ * ‖phiHat p φ₁ ((g : Mat) 1 0)‖ ≤ C₂ * C₃ :=
    mul_le_mul h2 h3 (norm_nonneg _) ((norm_nonneg _).trans h2)
  refine mul_le_mul (mul_le_mul h1 h23 (by positivity) (le_max_right _ _)) h4 (norm_nonneg _) ?_
  exact mul_nonneg (le_max_right _ _) ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans h23)

theorem unipotentGL2_mem_K2 {y : F} (hy : Valued.v y ≤ 1) : (unipotentGL2 y : G) ∈ K₂ := by
  rw [mem_K2_iff]
  have hval : ((unipotentGL2 y : G) : Mat) = !![1, y; 0, 1] := rfl
  have hinv : (((unipotentGL2 y : G)⁻¹ : G) : Mat) = !![1, -y; 0, 1] := rfl
  have hneg : Valued.v (-y) ≤ 1 := by rwa [Valuation.map_neg]
  constructor
  · intro i j; rw [hval]; fin_cases i <;> fin_cases j <;> simp [hy]
  · intro i j; rw [hinv]; fin_cases i <;> fin_cases j <;> simp [hy, hneg]

theorem v_le_one_of_unipotentGL2_mem_K2 {y : F} (h : (unipotentGL2 y : G) ∈ K₂) : Valued.v y ≤ 1 := by
  rw [mem_K2_iff] at h
  have := h.1 0 1
  simpa [unipotentGL2_coe] using this

theorem coe_diagUnits2_mul_lowerUnipotentGL2 (d a : Fˣ) (x : F) :
    ((diagUnits2 d a * lowerUnipotentGL2 x : G) : Mat) = !![(d : F), 0; (a : F) * x, (a : F)] := by
  rw [Units.val_mul]
  change (!![((d : Fˣ) : F), 0; 0, ((a : Fˣ) : F)] : Mat) * !![1, 0; x, 1] = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem det_diagUnits2_mul_lowerUnipotentGL2 (d a : Fˣ) (x : F) :
    Matrix.GeneralLinearGroup.det (diagUnits2 d a * lowerUnipotentGL2 x : G) = d * a := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagUnits2_mul_lowerUnipotentGL2, Matrix.det_fin_two_of, Units.val_mul]
  ring

theorem cell_value (ω θ : Fˣ →* ℂˣ) (f : ℕ) (W₀ : G₃ → ℂ)
    (hW₀law : IsGL3PsiWhittakerFn (psiLocal ℚ p)⁻¹ W₀)
    (hcentral : ∀ (t : Fˣ) (h : G₃),
      W₀ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W₀ h)
    (hK1 : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : G₃, W₀ (g * k) = W₀ g)
    (hbumpK : ∀ k ∈ K₂, ∀ h : G, W₀ (iotaGL (h * k)) = W₀ (iotaGL h))
    (hbumpS : ∀ h : G, W₀ (iotaGL h) ≠ 0 → ∃ x : F, ∃ k ∈ K₂, h = unipotentGL2 x * k)
    (hbump1 : W₀ (iotaGL 1) = 1)
    (w : G → ℂ) (hwlaw : ∀ (x : F) (g : G), w (unipotent x * g) = psiLocal ℚ p x * w g)
    (hwcentral : ∀ (z : Fˣ) (g : G), w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ z : ℂˣ) : ℂ) * w g)
    (φ φ₁ : F → ℂ)
    (hat1 : ∀ t : Fˣ, Valued.v (t : F) = 1 → phiHat p φ (t : F) = ((θ t : ℂˣ) : ℂ))
    (hat2 : ∀ y : F, Valued.v y ≠ 1 → phiHat p φ y = 0)
    (hat3 : ∀ t : Fˣ, Valued.v (t : F) = 1 → ∀ y : F, phiHat p φ₁ ((t : F) * y) = ((ω t : ℂˣ) : ℂ) * phiHat p φ₁ y)
    (hat4 : ∀ y : F, phiHat p φ₁ y ≠ 0 → Valued.v y ≤ WithZero.exp (-(f : ℤ)))
    (w₀p : G) (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0])
    (y x : F) (a d : Fˣ) :
    ((K₂ : Subgroup G) : Set G).indicator (fun g : G => Wfun p W₀ φ φ₁ g * Ffun p w w₀p g)
        (unipotentGL2 y * diagUnits2 d a * lowerUnipotentGL2 x) =
      (if Valued.v y ≤ 1 then (1 : ℂ) else 0) *
        (if Valued.v (a : F) = 1 ∧ Valued.v (d : F) = 1 then
          ((ω (a * d⁻¹) : ℂˣ) : ℂ) * phiHat p φ₁ x * w (w₀p * diagUnitGL2 (a * d⁻¹) * unipotent (-x))
        else 0) := by
  set g' : G := diagUnits2 d a * lowerUnipotentGL2 x with hg'
  have hu : (unipotentGL2 y : G) = unipotent y := (Units.ext rfl : (unipotent y : G) = unipotentGL2 y).symm
  have hz : (unipotentGL2 y * diagUnits2 d a * lowerUnipotentGL2 x : G) = unipotent y * g' := by
    rw [hu, hg', mul_assoc]
  rw [hz]
  have hprod : Wfun p W₀ φ φ₁ (unipotent y * g') * Ffun p w w₀p (unipotent y * g') =
      Wfun p W₀ φ φ₁ g' * Ffun p w w₀p g' := prod_unipotent_mul p W₀ hW₀law φ φ₁ w hwlaw w₀p hw₀p y g'
  have h11 : ((g' : G) : Mat) 1 1 = (a : F) := by rw [hg', coe_diagUnits2_mul_lowerUnipotentGL2]; rfl
  have h10 : ((g' : G) : Mat) 1 0 = (a : F) * x := by rw [hg', coe_diagUnits2_mul_lowerUnipotentGL2]; rfl
  have hWfun : Wfun p W₀ φ φ₁ g' =
      W₀ (JUnfoldAlg.dMat (diagUnits2 d⁻¹ a⁻¹ * unipotentGL2 (-x) : G)) * (phiHat p φ (a : F) * phiHat p φ₁ ((a : F) * x)) := by
    rw [Wfun_eq p W₀ hW₀law, h11, h10, Dg, hg', JUnfoldAlg.transposeInvN_diagUnits2_mul_lowerUnipotentGL2]
  have hun : (unipotentGL2 (-x) : G) = unipotent (-x) := (Units.ext rfl : (unipotent (-x) : G) = unipotentGL2 (-x)).symm
  have hFfun : Ffun p w w₀p g' =
      ((modulus (((d * a : Fˣ)) : F) : ℝ) : ℂ) *
        (((θ a⁻¹ : ℂˣ) : ℂ) * w (w₀p * diagUnitGL2 (a * d⁻¹) * unipotent (-x))) := by
    unfold Ffun
    rw [hg', det_diagUnits2_mul_lowerUnipotentGL2, JUnfoldAlg.transposeInvN_diagUnits2_mul_lowerUnipotentGL2, ← mul_assoc,
      JUnfoldAlg.w0_mul_diagUnits2_inv w₀p hw₀p, mul_assoc, mul_assoc, hwcentral, hun]
    simp only [mul_assoc]

  have hzero : Wfun p W₀ φ φ₁ g' * Ffun p w w₀p g' = 0 →
      ((K₂ : Subgroup G) : Set G).indicator (fun g : G => Wfun p W₀ φ φ₁ g * Ffun p w w₀p g) (unipotent y * g') = 0 := by
    intro h0
    by_cases hmem : (unipotent y * g' : G) ∈ ((K₂ : Subgroup G) : Set G)
    · rw [Set.indicator_of_mem hmem, hprod, h0]
    · rw [Set.indicator_of_notMem hmem]
  by_cases ha : Valued.v (a : F) = 1
  · have hφa : phiHat p φ (a : F) = ((θ a : ℂˣ) : ℂ) := hat1 a ha
    have hφ1ax : phiHat p φ₁ ((a : F) * x) = ((ω a : ℂˣ) : ℂ) * phiHat p φ₁ x := hat3 a ha x
    by_cases hx0 : phiHat p φ₁ x = 0
    · have hval : Wfun p W₀ φ φ₁ g' * Ffun p w w₀p g' = 0 := by
        rw [hWfun, hφ1ax, hx0]; ring
      rw [hzero hval, hx0]
      split_ifs <;> simp
    · have hxv : Valued.v x ≤ WithZero.exp (-(f : ℤ)) := hat4 x hx0
      have hx1 : Valued.v x ≤ 1 := by
        refine hxv.trans ?_
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]
        omega
      have hWD : W₀ (JUnfoldAlg.dMat (diagUnits2 d⁻¹ a⁻¹ * unipotentGL2 (-x) : G)) =
          ((ω d⁻¹ : ℂˣ) : ℂ) * (if Valued.v (d : F) = 1 then 1 else 0) := by
        rw [W₀_Dg_torus p ω f W₀ hcentral hK1 hbumpK d a x ha hxv, W₀_iotaGL_diag p W₀ hbumpK hbumpS hbump1]
      by_cases hd : Valued.v (d : F) = 1
      ·
        have hg'K : g' ∈ K₂ := by
          rw [hg']; exact (K₂).mul_mem (diagUnits2_mem_K2 p hd ha) (lowerUnipotentGL2_mem_K2 p hx1)
        have hmemiff : (unipotent y * g' : G) ∈ ((K₂ : Subgroup G) : Set G) ↔ Valued.v y ≤ 1 := by
          rw [← hu, SetLike.mem_coe]
          constructor
          · intro h
            have h' : (unipotentGL2 y : G) ∈ K₂ := by
              have := (K₂).mul_mem h ((K₂).inv_mem hg'K)
              rwa [mul_inv_cancel_right] at this
            exact v_le_one_of_unipotentGL2_mem_K2 p h'
          · intro hy1
            exact (K₂).mul_mem (unipotentGL2_mem_K2 p hy1) hg'K
        have hmod : modulus (((d * a : Fˣ)) : F) = 1 := by
          refine modulus_eq_one_of_v_eq_one p ?_
          rw [Units.val_mul, Valuation.map_mul, hd, ha, mul_one]
        have hθ : ((θ a : ℂˣ) : ℂ) * ((θ a⁻¹ : ℂˣ) : ℂ) = 1 := by
          rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
        have hω : ((ω d⁻¹ : ℂˣ) : ℂ) * ((ω a : ℂˣ) : ℂ) = ((ω (a * d⁻¹) : ℂˣ) : ℂ) := by
          rw [← Units.val_mul, ← map_mul, mul_comm]
        have hval : Wfun p W₀ φ φ₁ g' * Ffun p w w₀p g' =
            ((ω (a * d⁻¹) : ℂˣ) : ℂ) * phiHat p φ₁ x * w (w₀p * diagUnitGL2 (a * d⁻¹) * unipotent (-x)) := by
          rw [hWfun, hFfun, hWD, hφa, hφ1ax, hmod, if_pos hd]
          calc ((ω d⁻¹ : ℂˣ) : ℂ) * 1 * (((θ a : ℂˣ) : ℂ) * (((ω a : ℂˣ) : ℂ) * phiHat p φ₁ x)) *
                (((((1 : ℝ≥0) : ℝ)) : ℂ) * (((θ a⁻¹ : ℂˣ) : ℂ) * w (w₀p * diagUnitGL2 (a * d⁻¹) * unipotent (-x))))
              = (((ω d⁻¹ : ℂˣ) : ℂ) * ((ω a : ℂˣ) : ℂ)) * (((θ a : ℂˣ) : ℂ) * ((θ a⁻¹ : ℂˣ) : ℂ)) *
                  (phiHat p φ₁ x * w (w₀p * diagUnitGL2 (a * d⁻¹) * unipotent (-x))) := by push_cast; ring
            _ = _ := by rw [hω, hθ]; ring
        by_cases hmem : (unipotent y * g' : G) ∈ ((K₂ : Subgroup G) : Set G)
        · rw [Set.indicator_of_mem hmem, hprod, hval, if_pos (hmemiff.mp hmem), if_pos ⟨ha, hd⟩, one_mul]
        · rw [Set.indicator_of_notMem hmem, if_neg (fun h => hmem (hmemiff.mpr h)), zero_mul]
      · have hval : Wfun p W₀ φ φ₁ g' * Ffun p w w₀p g' = 0 := by
          rw [hWfun, hWD, if_neg hd]; ring
        rw [hzero hval]
        have hn : ¬ (Valued.v (a : F) = 1 ∧ Valued.v (d : F) = 1) := fun h => hd h.2
        rw [if_neg hn, mul_zero]
  · have hφa : phiHat p φ (a : F) = 0 := hat2 _ ha
    have hval : Wfun p W₀ φ φ₁ g' * Ffun p w w₀p g' = 0 := by
      rw [hWfun, hφa]; ring
    rw [hzero hval]
    have hn : ¬ (Valued.v (a : F) = 1 ∧ Valued.v (d : F) = 1) := fun h => ha h.1
    rw [if_neg hn, mul_zero]

end JUnfoldMain
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_rsIntegrand_dual_longWeyl3_smoothedBump_invariant_support_bound_and_bigCell_eq.JUnfoldMain"

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (ω θ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (f : ℕ)
    (W₀ : LocalGL3 p → ℂ)
    (hW₀law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₀)
    (hW₀sm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧ ∀ k ∈ Uv, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g)
    (hω : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₀ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W₀ h)
    (hK1 : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g)
    (hbumpK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL (h * k)) = W₀ (iotaGL h))
    (hbumpS : ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₀ (iotaGL h) ≠ 0 →
      ∃ x : p.adicCompletion ℚ, ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, h = unipotentGL2 x * k)
    (hbump1 : W₀ (iotaGL 1) = 1)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (hwsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hθ : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ z : ℂˣ) : ℂ) * w g)
    (φ φ₁ : p.adicCompletion ℚ → ℂ) (hφ : IsSchwartzBruhat φ) (hφ₁ : IsSchwartzBruhat φ₁) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    letI := localBorel ℚ p

    (∀ t : (p.adicCompletion ℚ)ˣ, Valued.v (t : p.adicCompletion ℚ) = 1 → tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ (t : p.adicCompletion ℚ) = ((θ t : ℂˣ) : ℂ)) →
    (∀ y : p.adicCompletion ℚ, Valued.v y ≠ 1 → tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ y = 0) →
    (∀ t : (p.adicCompletion ℚ)ˣ, Valued.v (t : p.adicCompletion ℚ) = 1 → ∀ y : p.adicCompletion ℚ,
      tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ ((t : p.adicCompletion ℚ) * y) = ((ω t : ℂˣ) : ℂ) * tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ y) →
    (∀ y : p.adicCompletion ℚ, tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ y ≠ 0 → Valued.v y ≤ WithZero.exp (-(f : ℤ))) →

    Measurable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          dualWhittakerFn3
            (fun X : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
              W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
            (iotaGL g) *
          (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w (w₀p * transposeInvN (Fin 2) g))) ∧

    (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        dualWhittakerFn3
            (fun X : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
              W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
            (iotaGL (unipotent x * g)) *
          (((modulus ((Matrix.GeneralLinearGroup.det (unipotent x * g) : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w (w₀p * transposeInvN (Fin 2) (unipotent x * g))) =
        dualWhittakerFn3
            (fun X : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
              W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
            (iotaGL g) *
          (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w (w₀p * transposeInvN (Fin 2) g))) ∧

    (∀ g : GL (Fin 2) (p.adicCompletion ℚ),
        dualWhittakerFn3
            (fun X : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
              W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
            (iotaGL g) *
          (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w (w₀p * transposeInvN (Fin 2) g)) ≠ 0 →
        ∃ (x : p.adicCompletion ℚ) (u : GL (Fin 2) (p.adicCompletion ℚ)),
          u ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ ∧ g = unipotent x * u) ∧

    (∃ C : ℝ, ∀ g ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
        ‖dualWhittakerFn3
            (fun X : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
              W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
            (iotaGL g) *
          (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w (w₀p * transposeInvN (Fin 2) g))‖ ≤ C) ∧

    (∀ (y x : p.adicCompletion ℚ) (a d : (p.adicCompletion ℚ)ˣ),
        (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set (GL (Fin 2) (p.adicCompletion ℚ))).indicator
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          dualWhittakerFn3
            (fun X : LocalGL3 p => ∫ u : p.adicCompletion ℚ, ∫ y : p.adicCompletion ℚ,
              W₀ (X * longWeyl3 * upperUnipotent3 u 0 y) * (φ u * φ₁ y) ∂(selfDualHaarAt ℚ p) ∂(selfDualHaarAt ℚ p))
            (iotaGL g) *
          (((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            w (w₀p * transposeInvN (Fin 2) g)))
          (unipotentGL2 y * diagUnits2 d a * lowerUnipotentGL2 x) =
        (if Valued.v y ≤ 1 then (1 : ℂ) else 0) *
          (if Valued.v (a : p.adicCompletion ℚ) = 1 ∧ Valued.v (d : p.adicCompletion ℚ) = 1 then
            ((ω (a * d⁻¹) : ℂˣ) : ℂ) * tateFourier (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (selfDualHaarAt ℚ p) φ₁ x *
              w (w₀p * diagUnitGL2 (a * d⁻¹) * unipotent (-x))
          else 0)) := by
  intro hat1 hat2 hat3 hat4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact JUnfoldMain.measurable_prod p W₀ hW₀law hW₀sm φ φ₁ hφ hφ₁ w hwsm w₀p
  · exact JUnfoldMain.prod_unipotent_mul p W₀ hW₀law φ φ₁ w hwlaw w₀p hw₀p
  · exact JUnfoldMain.support_prod p ω f W₀ hW₀law hω hK1 hbumpK hbumpS φ φ₁ hat2 hat4 w w₀p
  · exact JUnfoldMain.exists_bound_prod p W₀ hW₀law hW₀sm φ φ₁ hφ hφ₁ w hwsm w₀p
  · intro y x a d
    exact JUnfoldMain.cell_value p ω θ f W₀ hW₀law hω hK1 hbumpK hbumpS hbump1 w hwlaw hθ φ φ₁ hat1 hat2 hat3 hat4
      w₀p hw₀p y x a d

end
end S_LanglandsTunnell_RankinSelberg_rsIntegrand_dual_longWeyl3_smoothedBump_invariant_support_bound_and_bigCell_eq
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_rsIntegrand_dual_longWeyl3_smoothedBump_invariant_support_bound_and_bigCell_eq (solution)
