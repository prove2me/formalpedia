-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_cleared_rsLocalIntegral_fe_of_forall_lt_cleared_fe_finsum_cpow_of_isGL3PsiWhittakerFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/9946b3c7-4387-50c8-be19-caed7f642016

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
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_finset_forall_rsLocalIntegral_finsum_mul_eq_sum_cpow_of_forall_lt_cleared_laurent_of_torusShell
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_cleared_rsLocalIntegral_fe_of_forall_lt_cleared_fe_finsum_cpow_of_isGL3PsiWhittakerFn
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

open scoped Classical

set_option autoImplicit false

open scoped Classical

namespace LFEjf

theorem laurent_eq_zero_of_infinite {ι : Type*} (T : Finset ι) (a : ι → ℂ) (k : ι → ℤ) (S : Set ℂ)
    (hS : S.Infinite) (h0 : ∀ z ∈ S, z ≠ 0) (h : ∀ z ∈ S, ∑ t ∈ T, a t * z ^ (k t) = 0) :
    ∀ z : ℂ, z ≠ 0 → ∑ t ∈ T, a t * z ^ (k t) = 0 := by
  classical
  set K : ℕ := T.sup fun t => (k t).natAbs with hK
  have hKt : ∀ t ∈ T, 0 ≤ k t + K := by
    intro t ht
    have : (k t).natAbs ≤ K := Finset.le_sup (f := fun t => (k t).natAbs) ht
    omega
  set Q : Polynomial ℂ := ∑ t ∈ T, Polynomial.C (a t) * Polynomial.X ^ (k t + K).toNat with hQ
  have hQeval : ∀ z : ℂ, z ≠ 0 → Q.eval z = (∑ t ∈ T, a t * z ^ (k t)) * z ^ (K : ℤ) := by
    intro z hz
    rw [hQ, Polynomial.eval_finsetSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_assoc]
    congr 1
    rw [← zpow_natCast, Int.toNat_of_nonneg (hKt t ht), zpow_add₀ hz]
  have hroots : Set.Infinite {z : ℂ | Q.IsRoot z} := by
    refine hS.mono fun z hz => ?_
    show Q.IsRoot z
    rw [Polynomial.IsRoot.def, hQeval z (h0 z hz), h z hz, zero_mul]
  have hQ0 : Q = 0 := Polynomial.eq_zero_of_infinite_isRoot Q hroots
  intro z hz
  have h1 : (∑ t ∈ T, a t * z ^ (k t)) * z ^ (K : ℤ) = 0 := by rw [← hQeval z hz, hQ0, Polynomial.eval_zero]
  rcases mul_eq_zero.mp h1 with h1 | h1
  · exact h1
  · exact absurd h1 (zpow_ne_zero _ hz)

theorem infinite_image_cpow_neg (N : ℕ) (hN : 1 < N) (Sr : Set ℝ) (hSr : Sr.Infinite) :
    Set.Infinite ((fun t : ℝ => (N : ℂ) ^ (-(t : ℂ))) '' Sr) ∧
      ∀ z ∈ (fun t : ℝ => (N : ℂ) ^ (-(t : ℂ))) '' Sr, z ≠ 0 := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  refine ⟨hSr.image fun t₁ _ t₂ _ ht => ?_, ?_⟩
  · have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
    have h1 : ((N : ℝ) ^ (-(t₁ : ℝ)) : ℝ) = (N : ℝ) ^ (-(t₂ : ℝ)) := by
      have := congrArg Complex.re ht
      rwa [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_cast, show (-((t₁ : ℝ) : ℂ)) = ((-(t₁ : ℝ) : ℝ) : ℂ) by push_cast; ring,
        show (-((t₂ : ℝ) : ℂ)) = ((-(t₂ : ℝ) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_cpow (by positivity),
        Complex.ofReal_re, Complex.ofReal_re] at this
    have h2 : -(t₁ : ℝ) = -(t₂ : ℝ) := by
      rcases lt_trichotomy (-(t₁ : ℝ)) (-(t₂ : ℝ)) with hlt | heq | hgt
      · exact absurd h1 (ne_of_lt ((Real.rpow_lt_rpow_left_iff hN1).mpr hlt))
      · exact heq
      · exact absurd h1 (ne_of_gt ((Real.rpow_lt_rpow_left_iff hN1).mpr hgt))
    exact neg_injective h2
  · rintro z ⟨t, -, rfl⟩
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hN0)

theorem cpow_neg_int_mul (N : ℕ) (i : ℤ) (u : ℂ) :
    (N : ℂ) ^ (-(i : ℂ) * u) = ((N : ℂ) ^ (-u)) ^ i := by
  rw [← Complex.cpow_int_mul]
  congr 1
  ring

theorem sum_mul_zpow_eq_zero_of_forall_lt {ι : Type*} (N : ℕ) (hN : 1 < N) (T : Finset ι) (c : ι → ℂ) (k : ι → ℤ)
    (u₀ : ℝ) (h : ∀ u : ℝ, u₀ < u → ∑ t ∈ T, c t * (N : ℂ) ^ (-(k t : ℂ) * (u : ℂ)) = 0) :
    (∀ z : ℂ, z ≠ 0 → ∑ t ∈ T, c t * z ^ (k t) = 0) ∧ ∑ t ∈ T, c t = 0 := by
  have hSr : (Set.Ioi u₀).Infinite := Set.Ioi_infinite u₀
  obtain ⟨hS, hS0⟩ := infinite_image_cpow_neg N hN (Set.Ioi u₀) hSr
  have hmain := laurent_eq_zero_of_infinite T c k _ hS hS0 (by
    rintro z ⟨u, hu, rfl⟩
    have := h u hu
    simpa only [cpow_neg_int_mul] using this)
  refine ⟨hmain, ?_⟩
  simpa using hmain 1 one_ne_zero

theorem sum_eq_sum_of_forall_lt {ι : Type*} (N : ℕ) (hN : 1 < N) (T : Finset ι) (a b : ι → ℂ) (k : ι → ℤ)
    (u₀ : ℝ) (h : ∀ u : ℝ, u₀ < u →
      ∑ t ∈ T, a t * (N : ℂ) ^ (-(k t : ℂ) * (u : ℂ)) = ∑ t ∈ T, b t * (N : ℂ) ^ (-(k t : ℂ) * (u : ℂ))) :
    ∑ t ∈ T, a t = ∑ t ∈ T, b t := by
  have h' : ∀ u : ℝ, u₀ < u → ∑ t ∈ T, (a t - b t) * (N : ℂ) ^ (-(k t : ℂ) * (u : ℂ)) = 0 := by
    intro u hu
    simp only [sub_mul, Finset.sum_sub_distrib, h u hu, sub_self]
  have := (sum_mul_zpow_eq_zero_of_forall_lt N hN T _ k u₀ h').2
  simp only [Finset.sum_sub_distrib] at this
  exact sub_eq_zero.mp this

theorem exists_polynomial_eq_sum_cpow (N : ℕ) (hN : 1 < N) (M : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) :
    ∃ (P : Polynomial ℂ) (m₀ : ℤ), ∀ s : ℂ,
      ∑ mi ∈ M, c mi * (N : ℂ) ^ (-(mi.1 : ℂ) * s) = (N : ℂ) ^ ((m₀ : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)

  set K : ℕ := M.sup fun mi => (mi.1).natAbs with hK
  have hKm : ∀ mi ∈ M, 0 ≤ mi.1 + K := by
    intro mi hmi
    have : (mi.1).natAbs ≤ K := Finset.le_sup (f := fun mi : ℤ × ℤ => (mi.1).natAbs) hmi
    omega
  refine ⟨∑ mi ∈ M, Polynomial.C (c mi) * Polynomial.X ^ (mi.1 + K).toNat, K, fun s => ?_⟩
  rw [Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun mi hmi => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hX : (N : ℂ) ^ (-s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hN0)
  have e1 : ((N : ℂ) ^ (-s)) ^ (mi.1 + K).toNat = ((N : ℂ) ^ (-s)) ^ (mi.1 + (K : ℤ)) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (hKm mi hmi)]
  have e2 : ((N : ℂ) ^ (-s)) ^ (mi.1 + (K : ℤ)) = (N : ℂ) ^ (-(mi.1 : ℂ) * s) * (N : ℂ) ^ (-((K : ℕ) : ℂ) * s) := by
    rw [zpow_add₀ hX, ← Complex.cpow_int_mul, ← Complex.cpow_int_mul]
    congr 2 <;> push_cast <;> ring
  have e3 : (N : ℂ) ^ (((K : ℕ) : ℂ) * s) * (N : ℂ) ^ (-((K : ℕ) : ℂ) * s) = 1 := by
    rw [← Complex.cpow_add _ _ hN0]; ring_nf; simp
  rw [e1, e2]
  push_cast
  linear_combination (-(c mi * (N : ℂ) ^ (-(mi.1 : ℂ) * s))) * e3

section Inputs

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction UnramifiedWhittaker LanglandsTunnell.TateLocal

variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => HeightOneSpectrum.adicCompletion ℚ p

theorem iotaGL_unipotent (x : F) : (iotaGL (unipotent x) : LocalGL3 p) = upperUnipotent3 x 0 0 := by
  apply Units.ext
  change embedMat2 ((unipotent x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = _
  rw [upperUnipotent3_coe]
  have : ((unipotent x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] := rfl
  rw [this]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

theorem transposeInv3_mul (g h : LocalGL3 p) : transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  apply Units.ext
  change Matrix.transpose (((g * h)⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F) =
    Matrix.transpose ((g⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F) * Matrix.transpose ((h⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F)
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem longWeyl3_mul_transposeInv3_upperUnipotent3 (x : F) :
    (longWeyl3 : LocalGL3 p) * transposeInv3 (upperUnipotent3 x 0 0) = upperUnipotent3 0 (-x) 0 * longWeyl3 := by
  apply Units.ext
  change ((longWeyl3 : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F) * Matrix.transpose (((upperUnipotent3 x 0 0)⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F) =
    ((upperUnipotent3 0 (-x) 0 : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F) * ((longWeyl3 : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F)
  rw [upperUnipotent3_inv_eq]
  simp only [upperUnipotent3_coe, show ((longWeyl3 : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F) = !![0, 0, 1; 0, 1, 0; 1, 0, 0] from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]

theorem w0_mul_transposeInvN_unipotent (w₀p : GL (Fin 2) F) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) (x : F) :
    w₀p * transposeInvN (Fin 2) (unipotent x) = unipotent (-x) * w₀p := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_transposeInvN, hw₀p]
  have h1 : (((unipotent x : GL (Fin 2) F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, -x; 0, 1] := by
    rw [Matrix.coe_units_inv]
    have : ((unipotent x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] := rfl
    rw [this, Matrix.inv_def]
    simp [Matrix.det_fin_two_of, Matrix.adjugate_fin_two_of]
  have h2 : ((unipotent (-x) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, -x; 0, 1] := rfl
  rw [h1, h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

theorem det_unipotent_mul (x : F) (g : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.det (unipotent x * g) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul]
  have : Matrix.GeneralLinearGroup.det (unipotent x : GL (Fin 2) F) = 1 := by
    apply Units.ext
    change Matrix.det ((unipotent x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    have : ((unipotent x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] := rfl
    rw [this, Matrix.det_fin_two_of]; ring
  rw [this, one_mul]

variable (E : ℤ → LocalGL3 p → ℂ)
  (hElaw : ∀ i : ℤ, IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (E i))
  (w : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ)
  (hwlaw : ∀ (x : HeightOneSpectrum.adicCompletion ℚ p) (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)

include hElaw hwlaw in

theorem primal_unipotent_invariant (i : ℤ) (x : F) (g : GL (Fin 2) F) :
    E i (iotaGL (unipotent x * g)) * w (unipotent x * g) = E i (iotaGL g) * w g := by
  rw [map_mul, iotaGL_unipotent, hElaw i x 0 0, hwlaw, add_zero]
  have h1 : (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ x * NumberField.StandardAddChar.psiLocal ℚ p x = 1 := by
    rw [AddChar.inv_apply, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  linear_combination (E i (iotaGL g) * w g) * h1

include hElaw hwlaw in

theorem dual_unipotent_invariant (w₀p : GL (Fin 2) F) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0])
    (i : ℤ) (x : F) (g : GL (Fin 2) F) :
    dualWhittakerFn3 (E i) (iotaGL (unipotent x * g)) *
        (((modulus ((Matrix.GeneralLinearGroup.det (unipotent x * g) : Fˣ) : F) : ℝ) : ℂ) *
          w (w₀p * transposeInvN (Fin 2) (unipotent x * g))) =
      dualWhittakerFn3 (E i) (iotaGL g) *
        (((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) := by
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, map_mul, iotaGL_unipotent, transposeInv3_mul,
    show (longWeyl3 : LocalGL3 p) * (transposeInv3 (upperUnipotent3 x 0 0) * transposeInv3 (iotaGL g)) =
      upperUnipotent3 0 (-x) 0 * (longWeyl3 * transposeInv3 (iotaGL g)) from by
        rw [← mul_assoc, longWeyl3_mul_transposeInv3_upperUnipotent3, mul_assoc],
    hElaw i 0 (-x) 0, zero_add, det_unipotent_mul, transposeInvN_mul,
    show w₀p * (transposeInvN (Fin 2) (unipotent x) * transposeInvN (Fin 2) g) = unipotent (-x) * (w₀p * transposeInvN (Fin 2) g) from by
        rw [← mul_assoc, w0_mul_transposeInvN_unipotent p w₀p hw₀p, mul_assoc],
    hwlaw]
  have h1 : (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (-x) * NumberField.StandardAddChar.psiLocal ℚ p (-x) = 1 := by
    rw [AddChar.inv_apply, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  linear_combination (E i (longWeyl3 * transposeInv3 (iotaGL g)) *
    ((((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ)) * w (w₀p * transposeInvN (Fin 2) g))) * h1

end Inputs

section Finiteness

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction UnramifiedWhittaker

variable (p : HeightOneSpectrum (𝓞 ℚ))
local notation "F" => HeightOneSpectrum.adicCompletion ℚ p

theorem continuous_iotaGL : Continuous (iotaGL : GL (Fin 2) F → LocalGL3 p) := by
  have key : ∀ (M : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F), Continuous M →
      Continuous fun k => embedMat2 (M k) := by
    intro M hM
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [embedMat2] <;> first
      | exact (Continuous.matrix_elem hM _ _) | exact continuous_const
  rw [Units.continuous_iff]
  exact ⟨key _ Units.continuous_val, key _ Units.continuous_coe_inv⟩

theorem continuous_transposeInv3 : Continuous (transposeInv3 : LocalGL3 p → LocalGL3 p) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun g : LocalGL3 p => Matrix.transpose ((g⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F)
    exact Units.continuous_coe_inv.matrix_transpose
  · change Continuous fun g : LocalGL3 p => Matrix.transpose ((g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F)
    exact Units.continuous_val.matrix_transpose

variable (E : ℤ → LocalGL3 p → ℂ)
  (hEfin : ∀ C : Set (LocalGL3 p), IsCompact C → {i : ℤ | ∃ g ∈ C, E i g ≠ 0}.Finite)

include hEfin in

theorem finite_primal (C : Set (GL (Fin 2) F)) (hC : IsCompact C) :
    {i : ℤ | ∃ g ∈ C, E i (iotaGL g) ≠ 0}.Finite :=
  (hEfin _ (hC.image (continuous_iotaGL p))).subset fun i ⟨g, hg, hne⟩ => ⟨iotaGL g, ⟨g, hg, rfl⟩, hne⟩

include hEfin in

theorem finite_dual (C : Set (GL (Fin 2) F)) (hC : IsCompact C) :
    {i : ℤ | ∃ g ∈ C, dualWhittakerFn3 (E i) (iotaGL g) ≠ 0}.Finite :=
  (hEfin _ (hC.image ((continuous_const.mul ((continuous_transposeInv3 p).comp (continuous_iotaGL p)))))).subset
    fun i ⟨g, hg, hne⟩ => ⟨longWeyl3 * transposeInv3 (iotaGL g), ⟨g, hg, rfl⟩, hne⟩

end Finiteness

end LFEjf

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

open scoped Classical

noncomputable section

namespace FlatCutjf

theorem laurent_eq_zero_of_infinite {ι : Type*} (T : Finset ι) (a : ι → ℂ) (k : ι → ℤ) (S : Set ℂ)
    (hS : S.Infinite) (h0 : ∀ z ∈ S, z ≠ 0) (h : ∀ z ∈ S, ∑ t ∈ T, a t * z ^ (k t) = 0) :
    ∀ z : ℂ, z ≠ 0 → ∑ t ∈ T, a t * z ^ (k t) = 0 := by
  classical
  set K : ℕ := T.sup fun t => (k t).natAbs with hK
  have hKt : ∀ t ∈ T, 0 ≤ k t + K := by
    intro t ht
    have : (k t).natAbs ≤ K := Finset.le_sup (f := fun t => (k t).natAbs) ht
    omega
  set Q : Polynomial ℂ := ∑ t ∈ T, Polynomial.C (a t) * Polynomial.X ^ (k t + K).toNat with hQ
  have hQeval : ∀ z : ℂ, z ≠ 0 → Q.eval z = (∑ t ∈ T, a t * z ^ (k t)) * z ^ (K : ℤ) := by
    intro z hz
    rw [hQ, Polynomial.eval_finsetSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_assoc]
    congr 1
    rw [← zpow_natCast, Int.toNat_of_nonneg (hKt t ht), zpow_add₀ hz]
  have hroots : Set.Infinite {z : ℂ | Q.IsRoot z} := by
    refine hS.mono fun z hz => ?_
    show Q.IsRoot z
    rw [Polynomial.IsRoot.def, hQeval z (h0 z hz), h z hz, zero_mul]
  have hQ0 : Q = 0 := Polynomial.eq_zero_of_infinite_isRoot Q hroots
  intro z hz
  have h1 : (∑ t ∈ T, a t * z ^ (k t)) * z ^ (K : ℤ) = 0 := by rw [← hQeval z hz, hQ0, Polynomial.eval_zero]
  rcases mul_eq_zero.mp h1 with h1 | h1
  · exact h1
  · exact absurd h1 (zpow_ne_zero _ hz)

theorem infinite_image_cpow_neg (N : ℕ) (hN : 1 < N) (Sr : Set ℝ) (hSr : Sr.Infinite) :
    Set.Infinite ((fun t : ℝ => (N : ℂ) ^ (-(t : ℂ))) '' Sr) ∧
      ∀ z ∈ (fun t : ℝ => (N : ℂ) ^ (-(t : ℂ))) '' Sr, z ≠ 0 := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  refine ⟨hSr.image fun t₁ _ t₂ _ ht => ?_, ?_⟩
  · have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
    have h1 : ((N : ℝ) ^ (-(t₁ : ℝ)) : ℝ) = (N : ℝ) ^ (-(t₂ : ℝ)) := by
      have := congrArg Complex.re ht
      rwa [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_cast, show (-((t₁ : ℝ) : ℂ)) = ((-(t₁ : ℝ) : ℝ) : ℂ) by push_cast; ring,
        show (-((t₂ : ℝ) : ℂ)) = ((-(t₂ : ℝ) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_cpow (by positivity),
        Complex.ofReal_re, Complex.ofReal_re] at this
    have h2 : -(t₁ : ℝ) = -(t₂ : ℝ) := by
      rcases lt_trichotomy (-(t₁ : ℝ)) (-(t₂ : ℝ)) with hlt | heq | hgt
      · exact absurd h1 (ne_of_lt ((Real.rpow_lt_rpow_left_iff hN1).mpr hlt))
      · exact heq
      · exact absurd h1 (ne_of_gt ((Real.rpow_lt_rpow_left_iff hN1).mpr hgt))
    exact neg_injective h2
  · rintro z ⟨t, -, rfl⟩
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hN0)

private theorem _root_.FlatCutjf.cpow_neg_int_mul (N : ℕ) (i : ℤ) (u : ℂ) :
    (N : ℂ) ^ (-(i : ℂ) * u) = ((N : ℂ) ^ (-u)) ^ i := by
  rw [← Complex.cpow_int_mul]
  congr 1
  ring

p2m_export "FlatCutjf" "cpow_neg_int_mul"

theorem coeff_eq_zero_of_forall_mem (N : ℕ) (hN : 1 < N) (T : Finset ℤ) (a : ℤ → ℂ) (Sr : Set ℝ) (hSr : Sr.Infinite)
    (h : ∀ u ∈ Sr, ∑ i ∈ T, a i * (N : ℂ) ^ (-(i : ℂ) * (u : ℂ)) = 0) : ∀ i ∈ T, a i = 0 := by
  classical
  obtain ⟨hS, hS0⟩ := infinite_image_cpow_neg N hN Sr hSr
  have hz : ∀ z : ℂ, z ≠ 0 → ∑ i ∈ T, a i * z ^ (i : ℤ) = 0 :=
    laurent_eq_zero_of_infinite T a (fun i => i) _ hS hS0 (by
      rintro z ⟨u, hu, rfl⟩
      have := h u hu
      simpa only [cpow_neg_int_mul] using this)
  set K : ℕ := T.sup fun i => (i : ℤ).natAbs with hK
  have hKt : ∀ i ∈ T, 0 ≤ i + K := by
    intro i hi
    have : (i : ℤ).natAbs ≤ K := Finset.le_sup (f := fun i : ℤ => (i : ℤ).natAbs) hi
    omega
  set Q : Polynomial ℂ := ∑ i ∈ T, Polynomial.C (a i) * Polynomial.X ^ (i + K).toNat with hQ
  have hQeval : ∀ z : ℂ, z ≠ 0 → Q.eval z = (∑ i ∈ T, a i * z ^ (i : ℤ)) * z ^ (K : ℤ) := by
    intro z hz0
    rw [hQ, Polynomial.eval_finsetSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_assoc]
    congr 1
    rw [← zpow_natCast, Int.toNat_of_nonneg (hKt i hi), zpow_add₀ hz0]
  have hroots : Set.Infinite {z : ℂ | Q.IsRoot z} := by
    have hinf : Set.Infinite {z : ℂ | z ≠ 0} := by
      have : {z : ℂ | z ≠ 0} = Set.univ \ {0} := by ext z; simp
      rw [this]; exact Set.infinite_univ.diff (Set.finite_singleton 0)
    refine hinf.mono fun z hz0 => ?_
    show Q.IsRoot z
    rw [Polynomial.IsRoot.def, hQeval z hz0, hz z hz0, zero_mul]
  have hQ0 : Q = 0 := Polynomial.eq_zero_of_infinite_isRoot Q hroots
  intro i hi
  have hc : Q.coeff (i + K).toNat = a i := by
    rw [hQ, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single i]
    · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    · intro j hj hji
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
      intro hEq
      apply hji
      have h1 := hKt j hj
      have h2 := hKt i hi
      have : ((j + K).toNat : ℤ) = ((i + K).toNat : ℤ) := by rw [hEq]
      rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at this
      omega
    · intro hni; exact absurd hi hni
  rw [← hc, hQ0, Polynomial.coeff_zero]

theorem exists_infinite_fiber (f : ℝ → ℕ) : ∃ L : ℕ, {u : ℝ | f u = L}.Infinite := by
  by_contra h
  push Not at h
  have hcount : (Set.univ : Set ℝ).Countable := by
    have : (Set.univ : Set ℝ) = ⋃ L : ℕ, {u : ℝ | f u = L} := by
      ext u; simp
    rw [this]
    exact Set.countable_iUnion fun L => (h L).countable
  exact Cardinal.not_countable_real hcount

section Family

variable (p : HeightOneSpectrum (𝓞 ℚ))
  (E : ℤ → LocalGL3 p → ℂ) (U : Subgroup (LocalGL3 p))
  (hElaw : ∀ i : ℤ, IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (E i))
  (hEU : ∀ (i : ℤ), ∀ k ∈ U, ∀ g : LocalGL3 p, E i (g * k) = E i g)
  (hEfin : ∀ C : Set (LocalGL3 p), IsCompact C → {i : ℤ | ∃ g ∈ C, E i g ≠ 0}.Finite)

def WY (Y : ℤ → ℂ) (g : LocalGL3 p) : ℂ := ∑ᶠ i : ℤ, Y i * E i g

def Tpt (g : LocalGL3 p) : Finset ℤ := (hEfin {g} isCompact_singleton).toFinset

include hEfin in
theorem eq_zero_of_not_mem_Tpt {g : LocalGL3 p} {i : ℤ} (hi : i ∉ Tpt p E hEfin g) : E i g = 0 := by
  by_contra hne
  apply hi
  simp only [Tpt, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact ⟨g, rfl, hne⟩

include hEfin in
theorem WY_eq_sum (Y : ℤ → ℂ) (g : LocalGL3 p) : WY p E Y g = ∑ i ∈ Tpt p E hEfin g, Y i * E i g := by
  unfold WY
  apply finsum_eq_sum_of_support_subset
  intro i hi
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hi
  simp only [Finset.mem_coe, Tpt, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact ⟨g, rfl, hi.2⟩

include hEfin in

theorem WY_eq_sum_of_subset (Y : ℤ → ℂ) (g : LocalGL3 p) (T : Finset ℤ) (hT : Tpt p E hEfin g ⊆ T) :
    WY p E Y g = ∑ i ∈ T, Y i * E i g := by
  rw [WY_eq_sum p E hEfin Y g]
  apply Finset.sum_subset hT
  intro i _ hi
  rw [eq_zero_of_not_mem_Tpt p E hEfin hi, mul_zero]

include hElaw hEfin in
theorem isGL3PsiWhittakerFn_WY (Y : ℤ → ℂ) :
    IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (WY p E Y) := by
  intro x y z g

  set T := Tpt p E hEfin g ∪ Tpt p E hEfin (upperUnipotent3 x y z * g) with hT
  rw [WY_eq_sum_of_subset p E hEfin Y _ T Finset.subset_union_right,
    WY_eq_sum_of_subset p E hEfin Y _ T Finset.subset_union_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hElaw i x y z g]; ring

include hEU hEfin in
theorem WY_mul_right (Y : ℤ → ℂ) (k : LocalGL3 p) (hk : k ∈ U) (g : LocalGL3 p) : WY p E Y (g * k) = WY p E Y g := by
  unfold WY
  exact finsum_congr fun i => by rw [hEU i k hk g]

end Family

theorem exists_open_subgroup_conj_subset {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (C : Set G) (hC : IsCompact C) :
    ∃ U' : Subgroup G, IsOpen (U' : Set G) ∧ ∀ y ∈ C, ∀ k ∈ U', y⁻¹ * k * y ∈ U := by
  set φ : G × G → G := fun q => q.1⁻¹ * q.2 * q.1 with hφ
  have hφc : Continuous φ := by
    simp only [hφ]; fun_prop
  have hS : IsOpen (φ ⁻¹' (U : Set G)) := hU.preimage hφc
  have hsub : C ×ˢ ({1} : Set G) ⊆ φ ⁻¹' (U : Set G) := by
    rintro ⟨y, k⟩ ⟨-, hk⟩
    simp only [Set.mem_singleton_iff] at hk
    simp only [Set.mem_preimage, hφ, hk, mul_one, inv_mul_cancel, SetLike.mem_coe]
    exact U.one_mem
  obtain ⟨u, v, hu, hv, hCu, h1v, huv⟩ := generalized_tube_lemma hC isCompact_singleton hS hsub
  let U' : Subgroup G :=
    { carrier := {k | ∀ y ∈ C, y⁻¹ * k * y ∈ U}
      mul_mem' := fun {a b} ha hb y hy => by
        have := U.mul_mem (ha y hy) (hb y hy)
        simpa [mul_assoc] using this
      one_mem' := fun y hy => by simp [U.one_mem]
      inv_mem' := fun {a} ha y hy => by
        have := U.inv_mem (ha y hy)
        simpa [mul_assoc] using this }
  refine ⟨U', ?_, fun y hy k hk => hk y hy⟩
  apply Subgroup.isOpen_of_mem_nhds U' (g := 1)
  refine Filter.mem_of_superset (hv.mem_nhds (h1v (Set.mem_singleton 1))) fun k hk y hy => ?_
  have := huv (Set.mk_mem_prod (hCu hy) hk)
  simpa [hφ] using this

section Main

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => HeightOneSpectrum.adicCompletion ℚ p

private theorem _root_.FlatCutjf.continuous_iotaGL : Continuous (iotaGL : GL (Fin 2) F → LocalGL3 p) := by
  have key : ∀ (M : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F), Continuous M →
      Continuous fun k => embedMat2 (M k) := by
    intro M hM
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [embedMat2] <;> first
      | exact (Continuous.matrix_elem hM _ _) | exact continuous_const
  rw [Units.continuous_iff]
  exact ⟨key _ Units.continuous_val, key _ Units.continuous_coe_inv⟩

p2m_export "FlatCutjf" "continuous_iotaGL"
private theorem _root_.FlatCutjf.continuous_transposeInv3 : Continuous (transposeInv3 : LocalGL3 p → LocalGL3 p) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun g : LocalGL3 p => Matrix.transpose ((g⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F)
    exact Units.continuous_coe_inv.matrix_transpose
  · change Continuous fun g : LocalGL3 p => Matrix.transpose ((g : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F)
    exact Units.continuous_val.matrix_transpose

p2m_export "FlatCutjf" "continuous_transposeInv3"
theorem transposeInv3_mul (g h : LocalGL3 p) : transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  apply Units.ext
  change Matrix.transpose (((g * h)⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F) =
    Matrix.transpose ((g⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F) * Matrix.transpose ((h⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) F)
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem diagUnitGL2_mk0_zpow (π : p.adicCompletion ℚ) (hπ : π ≠ 0) (m : ℤ) :
    diagUnitGL2 (Units.mk0 π hπ ^ m * 1) = diagZ π hπ m := by
  apply Units.ext
  rw [mul_one]
  change (!![(((Units.mk0 π hπ ^ m : (p.adicCompletion ℚ)ˣ)) : p.adicCompletion ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) _) = !![π ^ m, 0; 0, 1]
  congr
  rw [Units.val_zpow_eq_zpow_val]; rfl

theorem flatCut
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (E : ℤ → LocalGL3 p → ℂ) (U : Subgroup (LocalGL3 p)) (hU : IsOpen (U : Set (LocalGL3 p)))
    (hElaw : ∀ i : ℤ, IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (E i))
    (hEU : ∀ (i : ℤ), ∀ k ∈ U, ∀ g : LocalGL3 p, E i (g * k) = E i g)
    (hEfin : ∀ C : Set (LocalGL3 p), IsCompact C → {i : ℤ | ∃ g ∈ C, E i g ≠ 0}.Finite) :
    ∃ L : ℕ, ∀ (i : ℤ), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ n : ℤ × ℤ,
      (n.1 < -(L : ℤ) ∨ n.2 < -(L : ℤ)) →
        E i (iotaGL (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n.1 * k)) = 0 ∧
        dualWhittakerFn3 (E i) (iotaGL (scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ n.1 * k)) = 0 := by
  classical
  set π := algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ with hπdef
  set N : ℕ := Ideal.absNorm p.asIdeal with hNdef
  have hN : 1 < N := by
    have h0 : Ideal.absNorm p.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact p.ne_bot
    have h1 : Ideal.absNorm p.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact p.isPrime.ne_top
    omega
  set K₀ : Set (GL (Fin 2) (p.adicCompletion ℚ)) :=
    ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))) with hK₀
  have hK₀c : IsCompact K₀ := (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ top_ne_bot).1

  set C : Set (LocalGL3 p) := (fun k => (iotaGL k : LocalGL3 p)) '' K₀ ∪ (fun k => transposeInv3 (iotaGL k : LocalGL3 p)) '' K₀ with hC
  have hCc : IsCompact C :=
    (hK₀c.image (continuous_iotaGL p)).union (hK₀c.image ((continuous_transposeInv3 p).comp (continuous_iotaGL p)))
  obtain ⟨U', hU'o, hU'⟩ := exists_open_subgroup_conj_subset U hU C hCc

  let Y : ℝ → ℤ → ℂ := fun u i => (N : ℂ) ^ (-(i : ℂ) * (u : ℂ))

  have hlev : ∀ u : ℝ, ∃ L : ℕ, ∀ y ∈ C, ∀ n : ℤ × ℤ, (n.1 < -(L : ℤ) ∨ n.2 < -(L : ℤ)) →
      WY p E (Y u) (iotaGL (scalarPi π hπ ^ n.2 * diagUnitGL2 (Units.mk0 π hπ ^ n.1 * 1)) * y) = 0 ∧
      WY p E (Y u) (longWeyl3 * transposeInv3 (iotaGL (scalarPi π hπ ^ n.2 * diagUnitGL2 (Units.mk0 π hπ ^ n.1 * 1))) * y) = 0 := by
    intro u
    have hfix : ∀ y ∈ C, ∀ k' ∈ U', ∀ x : LocalGL3 p, WY p E (Y u) (x * k' * y) = WY p E (Y u) (x * y) := by
      intro y hy k' hk' x
      rw [show x * k' * y = x * y * (y⁻¹ * k' * y) by group]
      exact WY_mul_right p E U hEU hEfin (Y u) _ (hU' y hy k' hk') _
    obtain ⟨L, hL⟩ := LanglandsTunnell.CubicInduction.exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg p
      (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ rfl (WY p E (Y u)) (isGL3PsiWhittakerFn_WY p E hElaw hEfin (Y u))
      hπ hϖ C U' hU'o hfix
    exact ⟨L, fun y hy n hn => hL y hy n hn 1 (by simp)⟩
  choose Lf hLf using hlev
  obtain ⟨L₀, hS⟩ := exists_infinite_fiber Lf
  refine ⟨L₀, fun i k hk n hn => ?_⟩
  have hshape : scalarPi π hπ ^ n.2 * diagUnitGL2 (Units.mk0 π hπ ^ n.1 * 1) = scalarPi π hπ ^ n.2 * diagZ π hπ n.1 := by
    rw [diagUnitGL2_mk0_zpow]

  have key : ∀ pt : LocalGL3 p, (∀ u ∈ {u : ℝ | Lf u = L₀}, WY p E (Y u) pt = 0) → E i pt = 0 := by
    intro pt hpt
    by_cases hi : i ∈ Tpt p E hEfin pt
    · refine coeff_eq_zero_of_forall_mem N hN (Tpt p E hEfin pt) (fun j => E j pt) _ hS ?_ i hi
      intro u hu
      have h1 := hpt u hu
      rw [WY_eq_sum p E hEfin] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    · exact eq_zero_of_not_mem_Tpt p E hEfin hi
  have hk1 : (iotaGL k : LocalGL3 p) ∈ C := Or.inl ⟨k, hk, rfl⟩
  have hk2 : transposeInv3 (iotaGL k : LocalGL3 p) ∈ C := Or.inr ⟨k, hk, rfl⟩
  constructor
  · apply key
    intro u hu
    have hn' : n.1 < -(Lf u : ℤ) ∨ n.2 < -(Lf u : ℤ) := by rw [Set.mem_setOf_eq.mp hu]; exact hn
    have := (hLf u _ hk1 n hn').1
    rwa [hshape, ← map_mul] at this
  · rw [dualWhittakerFn3_apply]
    apply key
    intro u hu
    have hn' : n.1 < -(Lf u : ℤ) ∨ n.2 < -(Lf u : ℤ) := by rw [Set.mem_setOf_eq.mp hu]; exact hn
    have := (hLf u _ hk2 n hn').2
    rwa [hshape, mul_assoc, ← transposeInv3_mul, ← map_mul] at this

end Main

end FlatCutjf

end

namespace FlatCleared48

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction UnramifiedWhittaker Filter Topology

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

theorem isLocallyConstant_of_mul_right_invariant {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    {Y : Type*} (f : G → Y) (U : Subgroup G) (hU : IsOpen (U : Set G)) (hf : ∀ k ∈ U, ∀ g : G, f (g * k) = f g) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun h => g⁻¹ * h) ⁻¹' (U : Set G), hU.preimage (continuous_const.mul continuous_id), ?_, fun h hh => ?_⟩
  · show g⁻¹ * g ∈ (U : Set G)
    rw [inv_mul_cancel]; exact U.one_mem
  · have := hf (g⁻¹ * h) hh g
    rwa [mul_inv_cancel_left] at this

theorem continuous_transposeInvN2 : Continuous (fun h : GL (Fin 2) F => transposeInvN (Fin 2) h) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · show Continuous fun h : GL (Fin 2) F => ((transposeInvN (Fin 2) h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    simp only [coe_transposeInvN]
    exact (Units.continuous_coe_inv).matrix_transpose
  · show Continuous fun h : GL (Fin 2) F => (((transposeInvN (Fin 2) h)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    simp only [coe_inv_transposeInvN]
    exact Units.continuous_val.matrix_transpose

theorem isLocallyConstant_modulus_det :
    IsLocallyConstant (fun g : GL (Fin 2) F =>
      (((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ))) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hdet : Continuous fun h : GL (Fin 2) F => ((Matrix.GeneralLinearGroup.det h : Fˣ) : F) := by
    have : (fun h : GL (Fin 2) F => ((Matrix.GeneralLinearGroup.det h : Fˣ) : F)) =
        fun h : GL (Fin 2) F => ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det := by
      funext h; rw [Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]
    exact Units.continuous_val.matrix_det
  have hne : ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ≠ 0 := (Matrix.GeneralLinearGroup.det g).ne_zero
  have hev := (hdet.tendsto g).eventually (eventually_norm_eq p hne)
  filter_upwards [hev] with h hh
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm,
    coe_nnnorm, coe_nnnorm, hh]

end FlatCleared48

namespace FlatCleared

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction UnramifiedWhittaker

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem mul_eq_of_unipotent_primal
    (E : ℤ → LocalGL3 p → ℂ)
    (hElaw : ∀ i : ℤ, IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (E i))
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g) :
    ∀ (i : ℤ) (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      (fun g => E i (iotaGL g)) (unipotent x * g) * w (unipotent x * g) = (fun g => E i (iotaGL g)) g * w g :=
  fun i x g => LFEjf.primal_unipotent_invariant p E hElaw w hwlaw i x g

theorem mul_eq_of_unipotent_dual
    (E : ℤ → LocalGL3 p → ℂ)
    (hElaw : ∀ i : ℤ, IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (E i))
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    ∀ (i : ℤ) (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      (fun g => dualWhittakerFn3 (E i) (iotaGL g)) (unipotent x * g) *
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) (unipotent x * g) =
        (fun g => dualWhittakerFn3 (E i) (iotaGL g)) g *
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) g :=
  fun i x g => LFEjf.dual_unipotent_invariant p E hElaw w hwlaw w₀p hw₀p i x g

theorem isLocallyConstant_primal_and_dual
    (E : ℤ → LocalGL3 p → ℂ) (U : Subgroup (LocalGL3 p)) (hU : IsOpen (U : Set (LocalGL3 p)))
    (hEU : ∀ (i : ℤ), ∀ k ∈ U, ∀ g : LocalGL3 p, E i (g * k) = E i g) :
    ∀ i : ℤ, IsLocallyConstant (fun g : GL (Fin 2) (p.adicCompletion ℚ) => E i (iotaGL g)) ∧
      IsLocallyConstant (fun g : GL (Fin 2) (p.adicCompletion ℚ) => dualWhittakerFn3 (E i) (iotaGL g)) := by
  intro i
  have hlc : IsLocallyConstant (E i) := FlatCleared48.isLocallyConstant_of_mul_right_invariant (E i) U hU (hEU i)
  refine ⟨hlc.comp_continuous (LFEjf.continuous_iotaGL p), ?_⟩
  simp only [dualWhittakerFn3_apply]
  exact hlc.comp_continuous (continuous_const.mul ((LFEjf.continuous_transposeInv3 p).comp (LFEjf.continuous_iotaGL p)))

theorem finite_primal_and_dual
    (E : ℤ → LocalGL3 p → ℂ)
    (hEfin : ∀ C : Set (LocalGL3 p), IsCompact C → {i : ℤ | ∃ g ∈ C, E i g ≠ 0}.Finite) :
    ∀ C : Set (GL (Fin 2) (p.adicCompletion ℚ)), IsCompact C →
      {i : ℤ | ∃ g ∈ C, (fun g => E i (iotaGL g)) g ≠ 0}.Finite ∧
      {i : ℤ | ∃ g ∈ C, (fun g => dualWhittakerFn3 (E i) (iotaGL g)) g ≠ 0}.Finite :=
  fun C hC => ⟨LFEjf.finite_primal p E hEfin C hC, LFEjf.finite_dual p E hEfin C hC⟩

theorem isLocallyConstant_dualPartner
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwsm : ∃ U₂ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U₂ : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U₂, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) :
    IsLocallyConstant w ∧
      IsLocallyConstant (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) := by
  obtain ⟨U₂, hU₂, hwU⟩ := hwsm
  have hlc : IsLocallyConstant w := FlatCleared48.isLocallyConstant_of_mul_right_invariant w U₂ hU₂ hwU
  refine ⟨hlc, ?_⟩
  exact FlatCleared48.isLocallyConstant_modulus_det.mul
    (hlc.comp_continuous (continuous_const.mul FlatCleared48.continuous_transposeInvN2))

theorem dual_finsum
    (E : ℤ → LocalGL3 p → ℂ)
    (hEfin : ∀ C : Set (LocalGL3 p), IsCompact C → {i : ℤ | ∃ g ∈ C, E i g ≠ 0}.Finite)
    (W : ℂ → LocalGL3 p → ℂ) (Wc : LocalGL3 p → ℂ)
    (hW : ∀ (u : ℂ) (g : LocalGL3 p), W u g = ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * E i g)
    (hWc : ∀ g : LocalGL3 p, Wc g = ∑ᶠ i : ℤ, E i g) :
    (∀ (u : ℂ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        dualWhittakerFn3 (W u) (iotaGL g) =
          ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * dualWhittakerFn3 (E i) (iotaGL g)) ∧
      (∀ g : GL (Fin 2) (p.adicCompletion ℚ), dualWhittakerFn3 Wc (iotaGL g) = ∑ᶠ i : ℤ, dualWhittakerFn3 (E i) (iotaGL g)) := by
  refine ⟨fun u g => ?_, fun g => ?_⟩
  · simp only [dualWhittakerFn3_apply, hW]
  · simp only [dualWhittakerFn3_apply, hWc]

end FlatCleared

namespace Asm491

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction UnramifiedWhittaker

variable {p : HeightOneSpectrum (𝓞 ℚ)}

theorem expsum_eq_at_one {ι κ : Type*} (N : ℕ) (hN : 1 < N) (T : Finset ι) (T' : Finset κ)
    (a : ι → ℂ) (k : ι → ℤ) (b : κ → ℂ) (k' : κ → ℤ) (u₀ : ℝ)
    (h : ∀ u : ℝ, u₀ < u →
      ∑ t ∈ T, a t * (N : ℂ) ^ (-(k t : ℂ) * (u : ℂ)) = ∑ t ∈ T', b t * (N : ℂ) ^ (-(k' t : ℂ) * (u : ℂ))) :
    ∑ t ∈ T, a t = ∑ t ∈ T', b t := by
  classical
  have h' : ∀ u : ℝ, u₀ < u →
      ∑ t ∈ T.disjSum T', (Sum.elim a (fun t => -b t) t) * (N : ℂ) ^ (-((Sum.elim k k' t : ℤ) : ℂ) * (u : ℂ)) = 0 := by
    intro u hu
    have e1 : ∑ t ∈ T', (-b t) * (N : ℂ) ^ (-(k' t : ℂ) * (u : ℂ)) = -∑ t ∈ T', b t * (N : ℂ) ^ (-(k' t : ℂ) * (u : ℂ)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun t _ => neg_mul _ _)
    rw [Finset.sum_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [e1, h u hu, add_neg_cancel]
  have := (LFEjf.sum_mul_zpow_eq_zero_of_forall_lt N hN (T.disjSum T') _ _ u₀ h').2
  rw [Finset.sum_disjSum] at this
  simp only [Sum.elim_inl, Sum.elim_inr] at this
  have e2 : ∑ t ∈ T', (-b t) = -∑ t ∈ T', b t := by simp
  rw [e2] at this
  linear_combination this

theorem expsum_eq_zero_of_forall_re {ι : Type*} (N : ℕ) (hN : 1 < N) (T : Finset ι) (a : ι → ℂ) (k : ι → ℤ) (σ : ℝ)
    (h : ∀ s : ℂ, σ < s.re → ∑ t ∈ T, a t * (N : ℂ) ^ (-(k t : ℂ) * s) = 0) :
    ∀ s : ℂ, ∑ t ∈ T, a t * (N : ℂ) ^ (-(k t : ℂ) * s) = 0 := by

  have hreal : ∀ u : ℝ, σ < u → ∑ t ∈ T, a t * (N : ℂ) ^ (-(k t : ℂ) * (u : ℂ)) = 0 :=
    fun u hu => h u (by simpa using hu)
  have hz := (LFEjf.sum_mul_zpow_eq_zero_of_forall_lt N hN T a k σ hreal).1
  intro s
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have := hz ((N : ℂ) ^ (-s)) (Complex.cpow_ne_zero_iff.mpr (Or.inl hN0))
  simpa only [LFEjf.cpow_neg_int_mul] using this

end Asm491

namespace Asm491

theorem expsum_ext {ι κ : Type*} (N : ℕ) (hN : 1 < N) (T : Finset ι) (T' : Finset κ)
    (a : ι → ℂ) (k : ι → ℤ) (b : κ → ℂ) (k' : κ → ℤ) (σ : ℝ)
    (h : ∀ s : ℂ, σ < s.re →
      ∑ t ∈ T, a t * (N : ℂ) ^ (-(k t : ℂ) * s) = ∑ t ∈ T', b t * (N : ℂ) ^ (-(k' t : ℂ) * s)) :
    ∀ s : ℂ, ∑ t ∈ T, a t * (N : ℂ) ^ (-(k t : ℂ) * s) = ∑ t ∈ T', b t * (N : ℂ) ^ (-(k' t : ℂ) * s) := by
  classical
  have h' : ∀ s : ℂ, σ < s.re →
      ∑ t ∈ T.disjSum T', (Sum.elim a (fun t => -b t) t) * (N : ℂ) ^ (-((Sum.elim k k' t : ℤ) : ℂ) * s) = 0 := by
    intro s hs
    have e1 : ∑ t ∈ T', (-b t) * (N : ℂ) ^ (-(k' t : ℂ) * s) = -∑ t ∈ T', b t * (N : ℂ) ^ (-(k' t : ℂ) * s) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun t _ => neg_mul _ _)
    rw [Finset.sum_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [e1, h s hs, add_neg_cancel]
  intro s
  have := expsum_eq_zero_of_forall_re N hN (T.disjSum T') _ _ σ h' s
  rw [Finset.sum_disjSum] at this
  simp only [Sum.elim_inl, Sum.elim_inr] at this
  have e2 : ∑ t ∈ T', (-b t) * (N : ℂ) ^ (-(k' t : ℂ) * s) = -∑ t ∈ T', b t * (N : ℂ) ^ (-(k' t : ℂ) * s) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun t _ => neg_mul _ _)
  rw [e2] at this
  linear_combination this

theorem laurentForm (N : ℕ) (hN : 1 < N) (P : Polynomial ℂ) (m : ℤ) (s : ℂ) :
    (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s)) =
      ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (N : ℂ) ^ (-(((i : ℤ) - m : ℤ) : ℂ) * s) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : ((N : ℂ) ^ (-s)) ^ i = (N : ℂ) ^ (-(i : ℂ) * s) := by
    rw [← Complex.cpow_nat_mul]; congr 1; ring
  have e2 : (N : ℂ) ^ (-(((i : ℤ) - m : ℤ) : ℂ) * s) = (N : ℂ) ^ ((m : ℂ) * s) * (N : ℂ) ^ (-(i : ℂ) * s) := by
    rw [← Complex.cpow_add _ _ hN0]; congr 1; push_cast; ring
  rw [e1, e2]; ring

theorem cpow_mulY (N : ℕ) (hN : 1 < N) (i b : ℤ) (u : ℂ) :
    (N : ℂ) ^ (-(i : ℂ) * u) * (N : ℂ) ^ (-(b : ℂ) * u) = (N : ℂ) ^ (-((i + b : ℤ) : ℂ) * u) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [← Complex.cpow_add _ _ hN0]; congr 1; push_cast; ring

theorem prodForm (N : ℕ) (hN : 1 < N) (M SQ : Finset (ℤ × ℤ)) (c q : ℤ × ℤ → ℂ) (u s s₂ : ℂ) :
    (∑ mi ∈ M, c mi * (N : ℂ) ^ (-(mi.2 : ℂ) * u) * (N : ℂ) ^ (-(mi.1 : ℂ) * s)) *
        (∑ ab ∈ SQ, q ab * (N : ℂ) ^ (-(ab.1 : ℂ) * s₂) * (N : ℂ) ^ (-(ab.2 : ℂ) * u)) =
      ∑ x ∈ M ×ˢ SQ, (c x.1 * (N : ℂ) ^ (-(x.1.1 : ℂ) * s) * (q x.2 * (N : ℂ) ^ (-(x.2.1 : ℂ) * s₂))) *
        (N : ℂ) ^ (-((x.1.2 + x.2.2 : ℤ) : ℂ) * u) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← cpow_mulY N hN]; ring

theorem prodForm0 (N : ℕ) (M SQ : Finset (ℤ × ℤ)) (c q : ℤ × ℤ → ℂ) (s s₂ : ℂ) :
    (∑ mi ∈ M, c mi * (N : ℂ) ^ (-(mi.1 : ℂ) * s)) * (∑ ab ∈ SQ, q ab * (N : ℂ) ^ (-(ab.1 : ℂ) * s₂)) =
      ∑ x ∈ M ×ˢ SQ, (c x.1 * (N : ℂ) ^ (-(x.1.1 : ℂ) * s) * (q x.2 * (N : ℂ) ^ (-(x.2.1 : ℂ) * s₂))) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']

end Asm491

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (E : ℤ → LocalGL3 p → ℂ) (U : Subgroup (LocalGL3 p)) (hU : IsOpen (U : Set (LocalGL3 p)))
    (hElaw : ∀ i : ℤ, IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ (E i))
    (hEU : ∀ (i : ℤ), ∀ k ∈ U, ∀ g : LocalGL3 p, E i (g * k) = E i g)
    (hEfin : ∀ C : Set (LocalGL3 p), IsCompact C → {i : ℤ | ∃ g ∈ C, E i g ≠ 0}.Finite)

    (W : ℂ → LocalGL3 p → ℂ) (Wc : LocalGL3 p → ℂ)
    (hW : ∀ (u : ℂ) (g : LocalGL3 p), W u g = ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * E i g)
    (hWc : ∀ g : LocalGL3 p, Wc g = ∑ᶠ i : ℤ, E i g)

    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (hwsm : ∃ U₂ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U₂ : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      ∀ k ∈ U₂, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])

    (γ : ℂ → ℂ) (e : ℤ)

    (SQ SQd : Finset (ℤ × ℤ)) (q qd : ℤ × ℤ → ℂ) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],

      (∃ u₀ : ℝ, ∀ u : ℝ, u₀ < u →
        ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
          (∀ s : ℂ, σ₂ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (W u (iotaGL g) * w g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              (dualWhittakerFn3 (W u) (iotaGL g) *
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) g) *
                ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
              (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
          (∀ s : ℂ, σ₂ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => W u (iotaGL g)) w *
                (∑ ab ∈ SQ, q ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.2 : ℂ) * (u : ℂ))) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ, σ₃ < s.re →
            RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                  (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
                s (fun g => dualWhittakerFn3 (W u) (iotaGL g))
                (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) *
                (∑ ab ∈ SQd, qd ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.2 : ℂ) * (u : ℂ))) =
              (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
          (∀ s : ℂ,
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) *
                (∑ ab ∈ SQ, q ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.2 : ℂ) * (u : ℂ))) =
              (γ s * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e : ℂ) * (u : ℂ))) *
                ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
                (∑ ab ∈ SQd, qd ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.2 : ℂ) * (u : ℂ))))) →

      (∃ σc : ℝ, ∀ s : ℂ, σc < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (Wc (iotaGL g) * w g) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →
      (∃ σd : ℝ, ∀ s : ℂ, σd < s.re →
        Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          (dualWhittakerFn3 Wc (iotaGL g) *
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) g) *
            ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) →

      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ),
        (∀ s : ℂ, σ₂ < s.re →
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (Wc (iotaGL g) * w g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
        (∀ s : ℂ, σ₃ < s.re →
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            (dualWhittakerFn3 Wc (iotaGL g) *
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ∧
        (∀ s : ℂ, σ₂ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
              s (fun g => Wc (iotaGL g)) w *
              (∑ ab ∈ SQ, q ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s)) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ, σ₃ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
                (modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))
              s (fun g => dualWhittakerFn3 Wc (iotaGL g))
              (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g)) *
              (∑ ab ∈ SQd, qd ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s)) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧
        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) *
              (∑ ab ∈ SQ, q ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * (-s))) =
            γ s * ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ s)) *
              (∑ ab ∈ SQd, qd ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s))) := by
  intro μ₂ _ μN₂ _ hI hIIc hIIId
  classical

  have hϖv := NumberField.AdelicLevel.valued_uniformizerUnit ℚ p
  have hmem : ((NumberField.AdelicLevel.uniformizerUnit ℚ p : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) ∈
      p.adicCompletionIntegers ℚ := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hϖv, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  set ϖ : p.adicCompletionIntegers ℚ := ⟨_, hmem⟩ with hϖdef
  have hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0 :=
    (NumberField.AdelicLevel.uniformizerUnit ℚ p).ne_zero
  have hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) := hϖv
  have hN : 1 < Ideal.absNorm p.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm p

  have hlc := FlatCleared.isLocallyConstant_primal_and_dual p E U hU hEU
  obtain ⟨hlcw, hlcBd⟩ := FlatCleared.isLocallyConstant_dualPartner p w hwsm w₀p
  have hfin := FlatCleared.finite_primal_and_dual p E hEfin
  have hFBp := FlatCleared.mul_eq_of_unipotent_primal p E hElaw w hwlaw
  have hFBd := FlatCleared.mul_eq_of_unipotent_dual p E hElaw w hwlaw w₀p hw₀p
  obtain ⟨L, hL⟩ := FlatCutjf.flatCut p hπ hϖ E U hU hElaw hEU hEfin
  obtain ⟨hGd, hGdc⟩ := FlatCleared.dual_finsum p E hEfin W Wc hW hWc
  obtain ⟨u₀, hu⟩ := hI

  obtain ⟨M, c, hMu, hMc⟩ :=
    LanglandsTunnell.RankinSelberg.exists_finset_forall_rsLocalIntegral_finsum_mul_eq_sum_cpow_of_forall_lt_cleared_laurent_of_torusShell
      p hπ hϖ (fun i g => E i (iotaGL g)) w (fun i => (hlc i).1) hlcw hFBp (fun C hC => (hfin C hC).1)
      ⟨L, fun i k hk n hn => (hL i k hk n hn).1⟩
      (fun u g => W u (iotaGL g)) (fun g => Wc (iotaGL g)) (fun u g => hW u (iotaGL g)) (fun g => hWc (iotaGL g)) SQ q μ₂ μN₂
      ⟨u₀, fun u hu' => by
        obtain ⟨P, Pd, m, md, σ₂, σ₃, h1, h2, h3, h4, h5⟩ := hu u hu'
        exact ⟨P, m, σ₂, h1, h3⟩⟩

  obtain ⟨Md, cd, hMdu, hMdc⟩ :=
    LanglandsTunnell.RankinSelberg.exists_finset_forall_rsLocalIntegral_finsum_mul_eq_sum_cpow_of_forall_lt_cleared_laurent_of_torusShell
      p hπ hϖ (fun i g => dualWhittakerFn3 (E i) (iotaGL g))
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w (w₀p * transposeInvN (Fin 2) g))
      (fun i => (hlc i).2) hlcBd hFBd (fun C hC => (hfin C hC).2)
      ⟨L, fun i k hk n hn => (hL i k hk n hn).2⟩
      (fun u g => dualWhittakerFn3 (W u) (iotaGL g)) (fun g => dualWhittakerFn3 Wc (iotaGL g)) hGd hGdc SQd qd μ₂ μN₂
      ⟨u₀, fun u hu' => by
        obtain ⟨P, Pd, m, md, σ₂, σ₃, h1, h2, h3, h4, h5⟩ := hu u hu'
        exact ⟨Pd, md, σ₃, h2, h4⟩⟩

  have KEY : ∀ s : ℂ,
      (∑ mi ∈ Md, cd mi * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.1 : ℂ) * s)) *
          (∑ ab ∈ SQ, q ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * (-s))) =
        γ s * (∑ mi ∈ M, c mi * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.1 : ℂ) * (-s))) *
          (∑ ab ∈ SQd, qd ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s)) := by

    intro s
    have hN0 : ((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show Ideal.absNorm p.asIdeal ≠ 0 by omega)

    have main : ∀ u : ℝ, u₀ < u →
        (∑ mi ∈ Md, cd mi * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.2 : ℂ) * (u : ℂ)) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.1 : ℂ) * s)) *
            (∑ ab ∈ SQ, q ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * (-s)) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.2 : ℂ) * (u : ℂ))) =
          (γ s * (Ideal.absNorm p.asIdeal : ℂ) ^ ((e : ℂ) * (u : ℂ))) *
            (∑ mi ∈ M, c mi * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.2 : ℂ) * (u : ℂ)) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.1 : ℂ) * (-s))) *
            (∑ ab ∈ SQd, qd ab * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.1 : ℂ) * s) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(ab.2 : ℂ) * (u : ℂ))) := by
      intro u hu'
      obtain ⟨P, Pd, m, md, σ₂, σ₃, h1, h2, h3, h4, h5⟩ := hu u hu'

      have hA : ∀ s' : ℂ, (∑ mi ∈ M, c mi * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.2 : ℂ) * (u : ℂ)) *
            (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.1 : ℂ) * s')) =
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s') * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s')) := by
        have hhalf : ∀ s' : ℂ, σ₂ < s'.re →
            (∑ mi ∈ M, (c mi * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.2 : ℂ) * (u : ℂ))) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.1 : ℂ) * s')) =
              ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(((i : ℤ) - m : ℤ) : ℂ) * s') := by
          intro s' hs'
          rw [← Asm491.laurentForm _ hN, ← h3 s' hs', ← hMu (u : ℂ) s' (h1 s' hs')]
        intro s'
        rw [Asm491.laurentForm _ hN]
        have := Asm491.expsum_ext _ hN M (Finset.range (P.natDegree + 1))
          (fun mi => c mi * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.2 : ℂ) * (u : ℂ))) (fun mi => mi.1)
          (fun i => P.coeff i) (fun i => (i : ℤ) - m) σ₂ hhalf s'
        simpa only [mul_assoc] using this
      have hB : ∀ s' : ℂ, (∑ mi ∈ Md, cd mi * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.2 : ℂ) * (u : ℂ)) *
            (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.1 : ℂ) * s')) =
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s') * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s')) := by
        have hhalf : ∀ s' : ℂ, σ₃ < s'.re →
            (∑ mi ∈ Md, (cd mi * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.2 : ℂ) * (u : ℂ))) * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.1 : ℂ) * s')) =
              ∑ i ∈ Finset.range (Pd.natDegree + 1), Pd.coeff i * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(((i : ℤ) - md : ℤ) : ℂ) * s') := by
          intro s' hs'
          rw [← Asm491.laurentForm _ hN, ← h4 s' hs', ← hMdu (u : ℂ) s' (h2 s' hs')]
        intro s'
        rw [Asm491.laurentForm _ hN]
        have := Asm491.expsum_ext _ hN Md (Finset.range (Pd.natDegree + 1))
          (fun mi => cd mi * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(mi.2 : ℂ) * (u : ℂ))) (fun mi => mi.1)
          (fun i => Pd.coeff i) (fun i => (i : ℤ) - md) σ₃ hhalf s'
        simpa only [mul_assoc] using this
      have hA' := hA (-s)
      rw [neg_neg] at hA'
      rw [hB s, hA']
      exact h5 s

    have main' : ∀ u : ℝ, u₀ < u →
        ∑ x ∈ Md ×ˢ SQ, (cd x.1 * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(x.1.1 : ℂ) * s) *
            (q x.2 * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(x.2.1 : ℂ) * (-s)))) *
            (Ideal.absNorm p.asIdeal : ℂ) ^ (-((x.1.2 + x.2.2 : ℤ) : ℂ) * (u : ℂ)) =
        ∑ x ∈ M ×ˢ SQd, (γ s * (c x.1 * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(x.1.1 : ℂ) * (-s)) *
            (qd x.2 * (Ideal.absNorm p.asIdeal : ℂ) ^ (-(x.2.1 : ℂ) * s)))) *
            (Ideal.absNorm p.asIdeal : ℂ) ^ (-((x.1.2 + x.2.2 + -e : ℤ) : ℂ) * (u : ℂ)) := by
      intro u hu'
      have h := main u hu'
      rw [Asm491.prodForm _ hN, mul_assoc (γ s * _), Asm491.prodForm _ hN, Finset.mul_sum] at h
      rw [h]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [show (Ideal.absNorm p.asIdeal : ℂ) ^ ((e : ℂ) * (u : ℂ)) = (Ideal.absNorm p.asIdeal : ℂ) ^ (-((-e : ℤ) : ℂ) * (u : ℂ)) by
        congr 1; push_cast; ring]
      rw [← Asm491.cpow_mulY _ hN (x.1.2 + x.2.2) (-e)]
      ring
    have hone := Asm491.expsum_eq_at_one _ hN (Md ×ˢ SQ) (M ×ˢ SQd) _ _ _ _ u₀ main'
    rw [Asm491.prodForm0, mul_assoc (γ s), Asm491.prodForm0, Finset.mul_sum]
    exact hone

  obtain ⟨P, m₀, hP⟩ := LFEjf.exists_polynomial_eq_sum_cpow (Ideal.absNorm p.asIdeal) hN M c
  obtain ⟨Pd, md₀, hPd⟩ := LFEjf.exists_polynomial_eq_sum_cpow (Ideal.absNorm p.asIdeal) hN Md cd
  obtain ⟨σc, hσc⟩ := hIIc
  obtain ⟨σd, hσd⟩ := hIIId
  refine ⟨P, Pd, m₀, md₀, σc, σd, hσc, hσd, fun s hs => ?_, fun s hs => ?_, fun s => ?_⟩
  · rw [hMc s (hσc s hs), hP s]
  · rw [hMdc s (hσd s hs), hPd s]
  · have hPs := hP (-s)
    rw [neg_neg] at hPs
    rw [← hPd s, ← hPs]
    exact KEY s

end S_LanglandsTunnell_RankinSelberg_exists_cleared_rsLocalIntegral_fe_of_forall_lt_cleared_fe_finsum_cpow_of_isGL3PsiWhittakerFn
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_cleared_rsLocalIntegral_fe_of_forall_lt_cleared_fe_finsum_cpow_of_isGL3PsiWhittakerFn (solution)
