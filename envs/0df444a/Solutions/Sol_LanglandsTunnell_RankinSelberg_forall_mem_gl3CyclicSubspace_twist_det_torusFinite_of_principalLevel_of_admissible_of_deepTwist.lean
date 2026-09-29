-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6743d278-78be-5d68-b201-826b5b130761

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
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction"

open scoped nonZeroDivisors

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.HasConductorExponentAt CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd TateLocal.exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt CubicInduction.exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg TateLocal.isHaarMeasure_comap_val_mulMeasure"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply gl3CyclicSubspace transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL localMaximalCompact3 LocalGL3 diagUnitGL2 coe_diagUnitGL2 diagHom diagUnits2 coe_diagUnits2 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply diagonal3 diagonal3_mul diagonal3_coe exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg"
namespace CritGenGlue
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open Matrix Topology Filter
open scoped NNReal ENNReal

variable {v : HeightOneSpectrum (𝓞 ℚ)}

section Torus

variable (v)

noncomputable def d3 : (Fin 3 → (v.adicCompletion ℚ)ˣ) →* LocalGL3 v where
  toFun := diagonal3 v
  map_one' := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    simp only [diagonal3_coe, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp
  map_mul' := diagonal3_mul v

@[scoped simp] theorem d3_apply (a : Fin 3 → (v.adicCompletion ℚ)ˣ) : d3 v a = diagonal3 v a := rfl

noncomputable def e1 : (v.adicCompletion ℚ)ˣ →* (Fin 3 → (v.adicCompletion ℚ)ˣ) where
  toFun u := ![u, 1, 1]
  map_one' := by funext i; fin_cases i <;> rfl
  map_mul' x y := by funext i; fin_cases i <;> simp

noncomputable def e3inv : (v.adicCompletion ℚ)ˣ →* (Fin 3 → (v.adicCompletion ℚ)ˣ) where
  toFun u := ![1, 1, u⁻¹]
  map_one' := by funext i; fin_cases i <;> simp
  map_mul' x y := by funext i; fin_cases i <;> simp [mul_comm]

@[scoped simp] theorem e1_apply (u : (v.adicCompletion ℚ)ˣ) : e1 v u = ![u, 1, 1] := rfl
@[scoped simp] theorem e3inv_apply (u : (v.adicCompletion ℚ)ˣ) : e3inv v u = ![1, 1, u⁻¹] := rfl

noncomputable def D2 : (v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ)ˣ →* GL (Fin 2) (v.adicCompletion ℚ) where
  toFun p := diagUnits2 p.1 p.2
  map_one' := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp
  map_mul' p q := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    simp only [Units.val_mul, coe_diagUnits2]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem D2_apply (x y : (v.adicCompletion ℚ)ˣ) : D2 v (x, y) = diagUnits2 x y := rfl

theorem scalarPi_eq (ϖ : v.adicCompletion ℚ) (hπ : ϖ ≠ 0) :
    UnramifiedWhittaker.scalarPi ϖ hπ = D2 v (Units.mk0 ϖ hπ, Units.mk0 ϖ hπ) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [D2_apply, coe_diagUnits2, UnramifiedWhittaker.scalarPi, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  fin_cases i <;> fin_cases j <;> simp

theorem diagUnitGL2_eq (x : (v.adicCompletion ℚ)ˣ) : diagUnitGL2 x = D2 v (x, 1) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [D2_apply, coe_diagUnits2, coe_diagUnitGL2]
  fin_cases i <;> fin_cases j <;> simp

theorem iotaGL_D2 (x y : (v.adicCompletion ℚ)ˣ) : iotaGL (D2 v (x, y)) = d3 v ![x, y, 1] := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [coe_iotaGL, D2_apply, coe_diagUnits2, d3_apply, diagonal3_coe]
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

theorem transposeInvN_D2 (x y : (v.adicCompletion ℚ)ˣ) : transposeInvN (Fin 2) (D2 v (x, y)) = D2 v (x⁻¹, y⁻¹) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [coe_transposeInvN, D2_apply, D2_apply, coe_diagUnits2]
  have : (((diagUnits2 x y)⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
      !![((x⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ), 0; 0, ((y⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)] := rfl
  rw [this]
  fin_cases i <;> fin_cases j <;> simp

theorem transposeInv3_iotaGL (m : GL (Fin 2) (v.adicCompletion ℚ)) :
    transposeInv3 (iotaGL m : LocalGL3 v) = iotaGL (transposeInvN (Fin 2) m) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h1 : ((transposeInv3 (iotaGL m : LocalGL3 v) : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      (((iotaGL m : LocalGL3 v)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ := rfl
  rw [h1, ← map_inv, coe_iotaGL, coe_iotaGL, coe_transposeInvN, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp [embedMat2]

theorem longWeyl3_mul_d3 (a b c : (v.adicCompletion ℚ)ˣ) :
    (longWeyl3 : LocalGL3 v) * d3 v ![a, b, c] = d3 v ![c, b, a] * longWeyl3 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  simp only [Units.val_mul, longWeyl3_coe, d3_apply, diagonal3_coe, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp

variable {v}

theorem arg_fst (ϖ : v.adicCompletion ℚ) (hπ : ϖ ≠ 0) (n : ℤ × ℤ) (u : (v.adicCompletion ℚ)ˣ)
    (m : GL (Fin 2) (v.adicCompletion ℚ)) (g : LocalGL3 v) :
    iotaGL (UnramifiedWhittaker.scalarPi ϖ hπ ^ n.2 * diagUnitGL2 (Units.mk0 ϖ hπ ^ n.1 * u) * m) * g =
      d3 v (![Units.mk0 ϖ hπ, Units.mk0 ϖ hπ, 1] ^ n.2 * ![Units.mk0 ϖ hπ, 1, 1] ^ n.1) * d3 v (e1 v u) * (iotaGL m * g) := by
  have h1 : iotaGL (UnramifiedWhittaker.scalarPi ϖ hπ ^ n.2) = d3 v (![Units.mk0 ϖ hπ, Units.mk0 ϖ hπ, 1] ^ n.2) := by
    rw [map_zpow, scalarPi_eq, iotaGL_D2, ← map_zpow]
  have h2 : iotaGL (diagUnitGL2 (Units.mk0 ϖ hπ ^ n.1 * u)) = d3 v (![Units.mk0 ϖ hπ, 1, 1] ^ n.1) * d3 v (e1 v u) := by
    rw [show diagUnitGL2 (Units.mk0 ϖ hπ ^ n.1 * u) = diagHom (Units.mk0 ϖ hπ ^ n.1 * u) from rfl, map_mul, map_mul,
      map_zpow, map_zpow, show diagHom (Units.mk0 ϖ hπ) = diagUnitGL2 (Units.mk0 ϖ hπ) from rfl,
      show diagHom u = diagUnitGL2 u from rfl, diagUnitGL2_eq, diagUnitGL2_eq, iotaGL_D2, iotaGL_D2, ← map_zpow]
    rfl
  rw [map_mul, map_mul, h1, h2, map_mul]
  simp only [mul_assoc]

theorem arg_snd (ϖ : v.adicCompletion ℚ) (hπ : ϖ ≠ 0) (n : ℤ × ℤ) (u : (v.adicCompletion ℚ)ˣ)
    (m : GL (Fin 2) (v.adicCompletion ℚ)) (g : LocalGL3 v) :
    longWeyl3 * transposeInv3 (iotaGL (UnramifiedWhittaker.scalarPi ϖ hπ ^ n.2 *
      diagUnitGL2 (Units.mk0 ϖ hπ ^ n.1 * u) * transposeInvN (Fin 2) m)) * g =
      d3 v ![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] * d3 v (e3inv v u) *
        (longWeyl3 * iotaGL m * g) := by
  set P := Units.mk0 ϖ hπ with hP

  let τ : GL (Fin 2) (v.adicCompletion ℚ) →* GL (Fin 2) (v.adicCompletion ℚ) :=
    { toFun := transposeInvN (Fin 2)
      map_one' := by
        have h := transposeInvN_mul (Fin 2) (1 : GL (Fin 2) (v.adicCompletion ℚ)) 1
        rw [one_mul] at h
        exact mul_left_cancel (a := transposeInvN (Fin 2) (1 : GL (Fin 2) (v.adicCompletion ℚ))) (by rw [← h, mul_one])
      map_mul' := transposeInvN_mul (Fin 2) }
  have hτ : ∀ x, transposeInvN (Fin 2) x = τ x := fun x => rfl
  have ht : transposeInvN (Fin 2) (UnramifiedWhittaker.scalarPi ϖ hπ ^ n.2 * diagUnitGL2 (P ^ n.1 * u)) =
      D2 v ((P ^ n.2 * P ^ n.1 * u)⁻¹, (P ^ n.2)⁻¹) := by
    rw [hτ, map_mul, map_zpow, ← hτ, ← hτ, scalarPi_eq, transposeInvN_D2, diagUnitGL2_eq, transposeInvN_D2,
      ← map_zpow, ← map_mul]
    congr 1
    ext <;> simp [hP, mul_comm, mul_assoc]
  rw [transposeInv3_iotaGL, transposeInvN_mul, transposeInvN_transposeInvN, ht, map_mul, iotaGL_D2]
  have hsplit : (![(P ^ n.2 * P ^ n.1 * u)⁻¹, (P ^ n.2)⁻¹, 1] : Fin 3 → (v.adicCompletion ℚ)ˣ) =
      ![(P ^ n.2 * P ^ n.1)⁻¹ * u⁻¹, (P ^ n.2)⁻¹, 1] := by
    funext i; fin_cases i <;> simp [mul_comm]
  rw [hsplit, ← mul_assoc, ← mul_assoc, longWeyl3_mul_d3]
  have hfac : (![1, (P ^ n.2)⁻¹, (P ^ n.2 * P ^ n.1)⁻¹ * u⁻¹] : Fin 3 → (v.adicCompletion ℚ)ˣ) =
      ![1, (P ^ n.2)⁻¹, (P ^ n.2 * P ^ n.1)⁻¹] * e3inv v u := by
    funext i; fin_cases i <;> simp
  rw [hfac, map_mul]
  simp only [mul_assoc]

theorem valued_mk0_zpow {ϖ : v.adicCompletion ℚ} (hπ : ϖ ≠ 0) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (n : ℤ) :
    Valued.v (((Units.mk0 ϖ hπ ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) = WithZero.exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0, hϖ, ← WithZero.exp_zsmul]
  congr 1; ring

theorem cond_fst {ϖ : v.adicCompletion ℚ} (hπ : ϖ ≠ 0) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {N : ℤ} {n : ℤ × ℤ}
    (hn : N ≤ n.1) :
    Valued.v ((((![Units.mk0 ϖ hπ, Units.mk0 ϖ hπ, 1] ^ n.2 * ![Units.mk0 ϖ hπ, 1, 1] ^ n.1 :
        Fin 3 → (v.adicCompletion ℚ)ˣ) 0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) ≤
      WithZero.exp (-N) * Valued.v ((((![Units.mk0 ϖ hπ, Units.mk0 ϖ hπ, 1] ^ n.2 * ![Units.mk0 ϖ hπ, 1, 1] ^ n.1 :
        Fin 3 → (v.adicCompletion ℚ)ˣ) 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) := by
  simp only [Pi.mul_apply, Pi.pow_apply, Matrix.cons_val_zero, Matrix.cons_val_one, _root_.one_zpow,
    Units.val_mul, map_mul, valued_mk0_zpow hπ hϖ, mul_one, ← WithZero.exp_add, WithZero.exp_le_exp]
  omega

theorem cond_snd {ϖ : v.adicCompletion ℚ} (hπ : ϖ ≠ 0) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {N : ℤ} {n : ℤ × ℤ}
    (hn : N ≤ n.1) :
    Valued.v ((((![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] :
        Fin 3 → (v.adicCompletion ℚ)ˣ) 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) ≤
      WithZero.exp (-N) * Valued.v ((((![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] :
        Fin 3 → (v.adicCompletion ℚ)ˣ) 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) := by
  have h1 : ((![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] :
      Fin 3 → (v.adicCompletion ℚ)ˣ) 1) = (Units.mk0 ϖ hπ ^ n.2)⁻¹ := rfl
  have h2 : ((![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] :
      Fin 3 → (v.adicCompletion ℚ)ˣ) 2) = (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹ := rfl
  rw [h1, h2]
  simp only [Units.val_inv_eq_inv_val, map_inv₀, Units.val_mul, map_mul, valued_mk0_zpow hπ hϖ, ← WithZero.exp_add,
    ← WithZero.exp_neg, WithZero.exp_le_exp]
  omega

end Torus

section Sphere

variable (v)

def sphere : Subgroup (v.adicCompletion ℚ)ˣ where
  carrier := {u | Valued.v (u : v.adicCompletion ℚ) = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at *
    rw [ha, hb, one_mul]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val, map_inv₀] at *
    rw [ha, inv_one]

theorem mem_sphere_iff {u : (v.adicCompletion ℚ)ˣ} : u ∈ sphere v ↔ Valued.v (u : v.adicCompletion ℚ) = 1 := Iff.rfl

theorem coe_sphere : (sphere v : Set (v.adicCompletion ℚ)ˣ) =
    {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1} := rfl

section WithZeroTop

open WithZeroTopology

theorem continuous_valuation : Continuous (Valued.v : v.adicCompletion ℚ → WithZero (Multiplicative ℤ)) :=
  Valued.continuous_valuation_of_surjective (HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v)

theorem isOpen_sphereK : IsOpen {x : v.adicCompletion ℚ | Valued.v x = 1} := by
  have h : IsOpen ({1} : Set (WithZero (Multiplicative ℤ))) := WithZeroTopology.isOpen_iff.2 (Or.inl (by simp))
  exact h.preimage (continuous_valuation v)

theorem isClosed_sphereK : IsClosed {x : v.adicCompletion ℚ | Valued.v x = 1} := by
  have h : IsClosed ({1} : Set (WithZero (Multiplicative ℤ))) :=
    WithZeroTopology.isClosed_iff.2 (Or.inr ⟨1, one_ne_zero, by simp⟩)
  exact h.preimage (continuous_valuation v)

theorem isOpen_closedBallK (c : ℕ) :
    IsOpen {x : v.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-(c : ℤ))} := by
  have h : IsOpen (Set.Iic (WithZero.exp (-(c : ℤ))) : Set (WithZero (Multiplicative ℤ))) :=
    WithZeroTopology.isOpen_iff.2 (Or.inr ⟨WithZero.exp (-(c : ℤ)), WithZero.exp_ne_zero, Set.Iio_subset_Iic_self⟩)
  exact h.preimage (continuous_valuation v)

end WithZeroTop

theorem isOpen_sphere : IsOpen (sphere v : Set (v.adicCompletion ℚ)ˣ) :=
  (isOpen_sphereK v).preimage Units.continuous_val

theorem isCompact_sphere : IsCompact (sphere v : Set (v.adicCompletion ℚ)ˣ) := by
  have hK : IsCompact {x : v.adicCompletion ℚ | Valued.v x = 1} := by
    refine IsCompact.of_isClosed_subset
      (isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers ℚ) from inferInstance))
      (isClosed_sphereK v) ?_
    intro x hx
    show x ∈ v.adicCompletionIntegers ℚ
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact le_of_eq hx
  have hsub : {x : v.adicCompletion ℚ | Valued.v x = 1} ⊆ Set.range (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) := by
    intro x hx
    have hx1 : Valued.v x = 1 := hx
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, map_zero] at hx1
      exact zero_ne_one hx1
    exact ⟨Units.mk0 x hx0, rfl⟩
  exact Units.isEmbedding_val₀.isInducing.isCompact_preimage' hK hsub

scoped instance compactSpace_sphere : CompactSpace (sphere v) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere v)

def smallUnits (c : ℕ) : Set (v.adicCompletion ℚ)ˣ :=
  {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1 ∧
    Valued.v ((u : v.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(c : ℤ))}

theorem isOpen_smallUnits (c : ℕ) : IsOpen (smallUnits v c) :=
  (isOpen_sphere v).inter ((isOpen_closedBallK v c).preimage (Units.continuous_val.sub continuous_const))

theorem one_mem_smallUnits (c : ℕ) : (1 : (v.adicCompletion ℚ)ˣ) ∈ smallUnits v c := by
  refine ⟨by simp, ?_⟩
  simp only [Units.val_one, sub_self, map_zero]
  exact zero_le'

theorem smallUnits_subset_higherUnitsAt (c : ℕ) : smallUnits v c ⊆ higherUnitsAt ℚ v c :=
  fun _ hu => ⟨hu.1, Or.inr hu.2⟩

theorem isOpen_ker_of_hasConductorExponentAt {η : (v.adicCompletion ℚ)ˣ →* ℂˣ} {c : ℕ}
    (hη : HasConductorExponentAt ℚ v η c) : IsOpen (η.ker : Set (v.adicCompletion ℚ)ˣ) := by
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset ((isOpen_smallUnits v c).mem_nhds (one_mem_smallUnits v c)) ?_)
  intro u hu
  exact hη.1 u (smallUnits_subset_higherUnitsAt v c hu)

end Sphere

section Engine

attribute [local instance] LanglandsTunnell.TateLocal.localBorel AutomorphicForm.localGLBorel

variable (v)

theorem borelSpace_loc : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v

attribute [local instance] borelSpace_loc

theorem borelSpace_locUnits : BorelSpace (v.adicCompletion ℚ)ˣ := by
  refine ⟨?_⟩
  have h : (inferInstance : TopologicalSpace (v.adicCompletion ℚ)ˣ) =
      TopologicalSpace.induced (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) inferInstance :=
    Units.isEmbedding_val₀.eq_induced
  show MeasurableSpace.comap Units.val (borel (v.adicCompletion ℚ)) = borel (v.adicCompletion ℚ)ˣ
  exact ((congrArg (fun t => @borel (v.adicCompletion ℚ)ˣ t) h).trans borel_comap).symm

attribute [local instance] borelSpace_locUnits

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  have hq : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := by
    have h : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)
  have hc : ((Ideal.absNorm v.asIdeal : ℝ≥0) ^
      (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2)) ≠ 0 :=
    (NNReal.rpow_pos (pos_iff_ne_zero.mpr hq)).ne'
  show ((((Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2))
    • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) : Measure (v.adicCompletion ℚ))).IsAddHaarMeasure
  rw [ENNReal.smul_def]
  exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc) ENNReal.coe_ne_top

attribute [local instance] isAddHaarMeasure_selfDualHaarAt

theorem isHaarMeasure_locMul :
    (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)) : Measure (v.adicCompletion ℚ)ˣ).IsHaarMeasure :=
  LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ v (selfDualHaarAt ℚ v)

theorem borelSpace_locGL : BorelSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ v

attribute [local instance] borelSpace_locGL

theorem setIntegral_subgroup_mul_left {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (H : Subgroup G) (hH : MeasurableSet (H : Set G))
    (f : G → ℂ) {k : G} (hk : k ∈ H) :
    ∫ x in (H : Set G), f (k * x) ∂μ = ∫ x in (H : Set G), f x ∂μ := by
  rw [← integral_indicator hH, ← integral_indicator hH]
  have hind : (H : Set G).indicator (fun x => f (k * x)) = fun x => (H : Set G).indicator f (k * x) := by
    funext x
    by_cases hx : x ∈ (H : Set G)
    · have hkx : k * x ∈ (H : Set G) := H.mul_mem hk hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hkx]
    · have hkx : k * x ∉ (H : Set G) := fun h =>
        hx (by simpa only [SetLike.mem_coe, inv_mul_cancel_left] using H.mul_mem (H.inv_mem hk) h)
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hkx]
  rw [hind]
  exact integral_mul_left_eq_self _ k

end Engine

section Data

variable (v)

theorem continuous_iotaGL : Continuous (iotaGL : GL (Fin 2) (v.adicCompletion ℚ) → LocalGL3 v) := by
  have hc : ∀ a b : Fin 2, Continuous fun h : GL (Fin 2) (v.adicCompletion ℚ) =>
      ((h : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) a b :=
    fun a b => Units.continuous_val.matrix_elem a b
  have hc' : ∀ a b : Fin 2, Continuous fun h : GL (Fin 2) (v.adicCompletion ℚ) =>
      ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) a b :=
    fun a b => Units.continuous_coe_inv.matrix_elem a b
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun h : GL (Fin 2) (v.adicCompletion ℚ) =>
      embedMat2 ((h : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j
    fin_cases i <;> fin_cases j <;> simp [embedMat2, hc, continuous_const]
  · refine continuous_matrix fun i j => ?_
    show Continuous fun h : GL (Fin 2) (v.adicCompletion ℚ) =>
      embedMat2 ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j
    fin_cases i <;> fin_cases j <;> simp [embedMat2, hc', continuous_const, -Matrix.coe_units_inv]

theorem continuous_coe_inv' : Continuous fun u : (v.adicCompletion ℚ)ˣ => ((u : v.adicCompletion ℚ))⁻¹ := by
  simpa only [Units.val_inv_eq_inv_val] using
    (Units.continuous_coe_inv : Continuous fun u : (v.adicCompletion ℚ)ˣ => ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ))

theorem continuous_d3_e1 : Continuous ((d3 v).comp (e1 v)) := by
  have hci := continuous_coe_inv' v
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun u : (v.adicCompletion ℚ)ˣ =>
      (Matrix.diagonal fun i => (((![u, 1, 1] : Fin 3 → (v.adicCompletion ℚ)ˣ) i : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Units.continuous_val, continuous_const]
  · refine continuous_matrix fun i j => ?_
    show Continuous fun u : (v.adicCompletion ℚ)ˣ =>
      (Matrix.diagonal fun i => ((((![u, 1, 1] : Fin 3 → (v.adicCompletion ℚ)ˣ) i)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, continuous_const, hci]

theorem continuous_d3_e3inv : Continuous ((d3 v).comp (e3inv v)) := by
  have hci := continuous_coe_inv' v
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun u : (v.adicCompletion ℚ)ˣ =>
      (Matrix.diagonal fun i => (((![1, 1, u⁻¹] : Fin 3 → (v.adicCompletion ℚ)ˣ) i : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, continuous_const, hci]
  · refine continuous_matrix fun i j => ?_
    show Continuous fun u : (v.adicCompletion ℚ)ˣ =>
      (Matrix.diagonal fun i => ((((![1, 1, u⁻¹] : Fin 3 → (v.adicCompletion ℚ)ˣ) i)⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Units.continuous_val, continuous_const]

end Data

section Congruence

variable (v)

theorem valued_mul_le_of_right_integral {a b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {C : WithZero (Multiplicative ℤ)}
    (ha : ∀ i l, Valued.v (a i l) ≤ C) (hb : ∀ l j, Valued.v (b l j) ≤ 1) (i j : Fin 3) :
    Valued.v ((a * b) i j) ≤ C := by
  have hterm : ∀ l, Valued.v (a i l * b l j) ≤ C := fun l => by
    rw [map_mul]
    calc Valued.v (a i l) * Valued.v (b l j) ≤ Valued.v (a i l) * 1 := mul_le_mul_right (hb l j) _
      _ = Valued.v (a i l) := mul_one _
      _ ≤ C := ha i l
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

theorem valued_mul_le_of_left_integral {a b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {C : WithZero (Multiplicative ℤ)}
    (ha : ∀ i l, Valued.v (a i l) ≤ 1) (hb : ∀ l j, Valued.v (b l j) ≤ C) (i j : Fin 3) :
    Valued.v ((a * b) i j) ≤ C := by
  have hterm : ∀ l, Valued.v (a i l * b l j) ≤ C := fun l => by
    rw [map_mul]
    calc Valued.v (a i l) * Valued.v (b l j) ≤ 1 * Valued.v (b l j) := mul_le_mul_left (ha i l) _
      _ = Valued.v (b l j) := one_mul _
      _ ≤ C := hb l j
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

theorem valued_mul_le_mul {a b : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)} {C D : WithZero (Multiplicative ℤ)}
    (ha : ∀ i l, Valued.v (a i l) ≤ C) (hb : ∀ l j, Valued.v (b l j) ≤ D) (i j : Fin 3) :
    Valued.v ((a * b) i j) ≤ C * D := by
  have hterm : ∀ l, Valued.v (a i l * b l j) ≤ C * D := fun l => by
    rw [map_mul]; exact mul_le_mul' (ha i l) (hb l j)
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

def congr3 (m : ℕ) : Subgroup (LocalGL3 v) where
  carrier := {k | (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) ∧
    (∀ i j, Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ)))}
  one_mem' := by
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [Units.val_one, sub_self, Valuation.map_zero]; exact zero_le'
    · rw [inv_one, Units.val_one, sub_self, Valuation.map_zero]; exact zero_le'
  mul_mem' := by
    intro a b ha hb
    have key : ∀ (x y : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)),
        (∀ i j, Valued.v (x i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) →
        (∀ i j, Valued.v (y i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) →
        ∀ i j, Valued.v ((x * y) i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ)) := by
      intro x y hx hy i j
      have hx1 : ∀ i l, Valued.v (x i l) ≤ 1 := fun i l => by
        have h := hx i l
        have : x i l = (x i l - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i l) + (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i l := by ring
        rw [this]
        refine le_trans (Valuation.map_add _ _ _) (max_le (h.trans ?_) ?_)
        · rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
        · rw [Matrix.one_apply]; split_ifs <;> simp
      have hdecomp : (x * y) i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j =
          (x * (y - 1)) i j + (x - 1) i j := by
        simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply]; ring
      rw [hdecomp]
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
      · exact valued_mul_le_of_left_integral v hx1 (fun l j => by rw [Matrix.sub_apply]; exact hy l j) i j
      · rw [Matrix.sub_apply]; exact hx i j
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact key _ _ ha.1 hb.1
    · rw [_root_.mul_inv_rev, Units.val_mul]; exact key _ _ hb.2 ha.2
  inv_mem' := by
    intro a ha
    exact ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem mem_congr3_iff {m : ℕ} {k : LocalGL3 v} : k ∈ congr3 v m ↔
    (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) ∧
    (∀ i j, Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) := Iff.rfl

theorem isOpen_congr3 (m : ℕ) : IsOpen (congr3 v m : Set (LocalGL3 v)) := by
  have hball := isOpen_closedBallK v m
  have hc1 : ∀ i j : Fin 3, Continuous fun k : LocalGL3 v =>
      (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j :=
    fun i j => (Units.continuous_val.matrix_elem i j).sub continuous_const
  have hc2 : ∀ i j : Fin 3, Continuous fun k : LocalGL3 v =>
      ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j :=
    fun i j => ((Units.continuous_val.matrix_elem i j).comp continuous_inv).sub continuous_const
  have h : (congr3 v m : Set (LocalGL3 v)) =
      (⋂ i : Fin 3, ⋂ j : Fin 3, (fun k : LocalGL3 v => (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ⁻¹' {x | Valued.v x ≤ WithZero.exp (-(m : ℤ))}) ∩
      (⋂ i : Fin 3, ⋂ j : Fin 3, (fun k : LocalGL3 v => ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ⁻¹' {x | Valued.v x ≤ WithZero.exp (-(m : ℤ))}) := by
    ext k
    simp only [SetLike.mem_coe, mem_congr3_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
  rw [h]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hball.preimage (hc1 i j)).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hball.preimage (hc2 i j))

theorem conj_mem_of_mem_congr3 {M d m : ℕ} (hm : d + 2 * M ≤ m) {g : LocalGL3 v}
    (hg : ∀ i j, Valued.v ((g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (M : ℤ) ∧
      Valued.v (((g⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (M : ℤ))
    {k : LocalGL3 v} (hk : k ∈ congr3 v m) :
    g⁻¹ * k * g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧
    ∀ i j, Valued.v (((g⁻¹ * k * g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ)) := by

  have est : ∀ x : LocalGL3 v,
      (∀ i j, Valued.v ((x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) →
      ∀ i j, Valued.v (((g⁻¹ * x * g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ)) := by
    intro x hx i j
    have hmat : ((g⁻¹ * x * g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 =
        ((g⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
          ((x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) * ((g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one]
    have h := congrFun (congrFun hmat i) j
    rw [Matrix.sub_apply] at h
    rw [h]
    have hx' : ∀ l j, Valued.v ((((x : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1) l j) ≤
        WithZero.exp (-(m : ℤ)) := fun l j => by rw [Matrix.sub_apply]; exact hx l j
    have h1 : ∀ i j, Valued.v ((((g⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) *
        (((x : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1)) i j) ≤
        WithZero.exp (M : ℤ) * WithZero.exp (-(m : ℤ)) :=
      fun i j => valued_mul_le_mul v (fun i l => (hg i l).2) hx' i j
    have h2 := valued_mul_le_mul v h1 (fun l j => (hg l j).1) i j
    refine h2.trans ?_
    rw [← WithZero.exp_add, ← WithZero.exp_add, WithZero.exp_le_exp]
    omega
  have hk1 := est k hk.1
  have hk2 : ∀ i j, Valued.v ((((g⁻¹ * k * g)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ)) := by
    have : (g⁻¹ * k * g)⁻¹ = g⁻¹ * k⁻¹ * g := by
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [this]
    exact est k⁻¹ hk.2
  have hint : ∀ (x : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)),
      (∀ i j, Valued.v (x i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
      ∀ i j, Valued.v (x i j) ≤ 1 := by
    intro x hx i j
    have : x i j = (x i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) + (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j := by ring
    rw [this]
    refine le_trans (Valuation.map_add _ _ _) (max_le ((hx i j).trans ?_) ?_)
    · rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    · rw [Matrix.one_apply]; split_ifs <;> simp
  exact ⟨⟨hint _ hk1, hint _ hk2⟩, hk1⟩

end Congruence

end LanglandsTunnell.CubicInduction.CritGenGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.HasConductorExponentAt CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd TateLocal.exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt CubicInduction.exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg TateLocal.isHaarMeasure_comap_val_mulMeasure"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply gl3CyclicSubspace transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL localMaximalCompact3 LocalGL3 diagUnitGL2 coe_diagUnitGL2 diagHom diagUnits2 coe_diagUnits2 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply diagonal3 diagonal3_mul diagonal3_coe exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg"
namespace CritGenGlue
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open Matrix Topology Filter

section Members

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => v.adicCompletion ℚ
local notation "Mat3" => Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)

theorem exists_valued_entry_le_of_isCompact (C : Set (LocalGL3 v)) (hC : IsCompact C) :
    ∃ M : ℕ, ∀ X ∈ C, ∀ i j,
      Valued.v ((X : Mat3) i j) ≤ WithZero.exp (M : ℤ) ∧
      Valued.v (((X⁻¹ : LocalGL3 v) : Mat3) i j) ≤ WithZero.exp (M : ℤ) := by
  classical
  set π : 𝕂 := algebraMap ℚ (v.adicCompletion ℚ) ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℚ) with hπ
  have hvπ : Valued.v π = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans (RatIdele.valuation_natGenerator v)
  have hπ0 : π ≠ 0 := fun h => by rw [h, map_zero] at hvπ; exact WithZero.exp_ne_zero hvπ.symm
  have hnormπ : ‖π‖ < 1 := (Valued.toNormedField.norm_lt_one_iff).mpr (by rw [hvπ, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num))
  have hnormπinv : 1 < ‖π⁻¹‖ := by
    rw [norm_inv]; exact (one_lt_inv₀ (norm_pos_iff.mpr hπ0)).mpr hnormπ
  have hb : ∀ i j : Fin 3, ∃ R : ℝ, ∀ X ∈ C,
      ‖(X : Mat3) i j‖ ≤ R ∧ ‖(((X⁻¹ : LocalGL3 v)) : Mat3) i j‖ ≤ R := by
    intro i j
    have hc1 : Continuous fun X : LocalGL3 v => (X : Mat3) i j := (Units.continuous_val.matrix_elem i j)
    have hc2 : Continuous fun X : LocalGL3 v => (((X⁻¹ : LocalGL3 v)) : Mat3) i j :=
      (Units.continuous_val.matrix_elem i j).comp continuous_inv
    obtain ⟨R₁, hR₁⟩ := hC.exists_bound_of_continuousOn hc1.continuousOn
    obtain ⟨R₂, hR₂⟩ := hC.exists_bound_of_continuousOn hc2.continuousOn
    exact ⟨max R₁ R₂, fun X hX => ⟨(hR₁ X hX).trans (le_max_left _ _), (hR₂ X hX).trans (le_max_right _ _)⟩⟩
  choose R hR using hb
  set R₀ : ℝ := Finset.univ.sum fun ij : Fin 3 × Fin 3 => |R ij.1 ij.2| with hR₀
  have hRle : ∀ i j, R i j ≤ R₀ := fun i j => by
    have := Finset.single_le_sum (f := fun ij : Fin 3 × Fin 3 => |R ij.1 ij.2|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ (i, j))
    exact (le_abs_self _).trans this
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt R₀ hnormπinv
  refine ⟨M, fun X hX i j => ?_⟩
  have hcmp : ∀ y : 𝕂, ‖y‖ ≤ R₀ → Valued.v y ≤ WithZero.exp (M : ℤ) := by
    intro y hy
    have h1 : ‖y‖ ≤ ‖(π⁻¹) ^ M‖ := by rw [norm_pow]; exact hy.trans hM.le
    have h2 := (Valued.toNormedField.norm_le_iff).mp h1
    rw [map_pow, map_inv₀, hvπ, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_nsmul] at h2
    simpa using h2
  exact ⟨hcmp _ ((hR i j X hX).1.trans (hRle i j)), hcmp _ ((hR i j X hX).2.trans (hRle i j))⟩

theorem det_diagonal3 (c : Fin 3 → (𝕂)ˣ) : Matrix.GeneralLinearGroup.det (diagonal3 v c) = c 0 * c 1 * c 2 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, diagonal3_coe, Matrix.det_diagonal, Fin.prod_univ_three]
  simp

theorem det_upperUnipotent3 (x y z : 𝕂) : Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z : LocalGL3 v) = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, upperUnipotent3_coe, Matrix.det_fin_three]
  simp

theorem continuous_det3 : Continuous (Matrix.GeneralLinearGroup.det : LocalGL3 v → (𝕂)ˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (Units.val ∘ (Matrix.GeneralLinearGroup.det : LocalGL3 v → (𝕂)ˣ)) =
        fun g : LocalGL3 v => ((g : LocalGL3 v) : Mat3).det := by
      funext g; exact Matrix.GeneralLinearGroup.val_det_apply g
    rw [this]; exact Units.continuous_val.matrix_det
  · have : (fun g : LocalGL3 v => ((↑((Matrix.GeneralLinearGroup.det g)⁻¹) : 𝕂))) =
        fun g : LocalGL3 v => (((g⁻¹ : LocalGL3 v)) : Mat3).det := by
      funext g; rw [← map_inv]; exact Matrix.GeneralLinearGroup.val_det_apply g⁻¹
    refine (continuous_congr (fun g => ?_)).mpr ((Units.continuous_val.comp continuous_inv).matrix_det)
    show ((↑((Matrix.GeneralLinearGroup.det g)⁻¹) : 𝕂)) = (((g⁻¹ : LocalGL3 v)) : Mat3).det
    rw [← map_inv]; exact Matrix.GeneralLinearGroup.val_det_apply g⁻¹

variable (W₀ : LocalGL3 v → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (d : ℕ)

def P12 (W : LocalGL3 v → ℂ) : Prop :=
  ∀ C : Set (LocalGL3 v), IsCompact C → ∃ N : ℕ, ∀ X ∈ C, ∀ a : Fin 3 → (𝕂)ˣ,
    Valued.v (((a 0 : (𝕂)ˣ) : 𝕂) / ((a 1 : (𝕂)ˣ) : 𝕂)) ≤ WithZero.exp (-(N : ℤ)) →
    ∀ s t : (𝕂)ˣ, s ∈ higherUnitsAt ℚ v d → t ∈ higherUnitsAt ℚ v d →
      W (diagonal3 v a * diagonal3 v ![s, t, t] * X) =
        ((χ s : ℂˣ) : ℂ) * ((χ t : ℂˣ) : ℂ) ^ 2 * W (diagonal3 v a * X)

def P23 (W : LocalGL3 v → ℂ) : Prop :=
  ∀ C : Set (LocalGL3 v), IsCompact C → ∃ N : ℕ, ∀ X ∈ C, ∀ a : Fin 3 → (𝕂)ˣ,
    Valued.v (((a 1 : (𝕂)ˣ) : 𝕂) / ((a 2 : (𝕂)ˣ) : 𝕂)) ≤ WithZero.exp (-(N : ℤ)) →
    ∀ s t : (𝕂)ˣ, s ∈ higherUnitsAt ℚ v d → t ∈ higherUnitsAt ℚ v d →
      W (diagonal3 v a * diagonal3 v ![t, t, s] * X) =
        ((χ s : ℂˣ) : ℂ) * ((χ t : ℂˣ) : ℂ) ^ 2 * W (diagonal3 v a * X)

variable {ϖ : v.adicCompletionIntegers ℚ}
  (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)

def PNEG (W : LocalGL3 v → ℂ) : Prop :=
  ∀ C : Set (LocalGL3 v), IsCompact C → ∃ L : ℕ, ∀ y ∈ C, ∀ n : ℤ × ℤ, (n.1 < -(L : ℤ) ∨ n.2 < -(L : ℤ)) →
    ∀ u : (𝕂)ˣ, Valued.v (u : 𝕂) = 1 →
      W (iotaGL (UnramifiedWhittaker.scalarPi
            (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
            ^ n.1 * u)) * y) = 0 ∧
      W (longWeyl3 * transposeInv3 (iotaGL (UnramifiedWhittaker.scalarPi
            (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
          diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
            ^ n.1 * u))) * y) = 0

variable {W₀ χ d}

theorem P12.zero : P12 v χ d 0 := fun C _ => ⟨0, fun X _ a _ s t _ _ => by simp⟩
theorem P23.zero : P23 v χ d 0 := fun C _ => ⟨0, fun X _ a _ s t _ _ => by simp⟩
theorem PNEG.zero : PNEG v hπ 0 := fun C _ => ⟨0, fun y _ n _ u _ => by simp⟩

theorem P12.add {W₁ W₂ : LocalGL3 v → ℂ} (h₁ : P12 v χ d W₁) (h₂ : P12 v χ d W₂) : P12 v χ d (W₁ + W₂) := by
  intro C hC
  obtain ⟨N₁, hN₁⟩ := h₁ C hC
  obtain ⟨N₂, hN₂⟩ := h₂ C hC
  refine ⟨max N₁ N₂, fun X hX a ha s t hs ht => ?_⟩
  have ha₁ : Valued.v (((a 0 : (𝕂)ˣ) : 𝕂) / ((a 1 : (𝕂)ˣ) : 𝕂)) ≤ WithZero.exp (-(N₁ : ℤ)) :=
    ha.trans (WithZero.exp_le_exp.mpr (by omega))
  have ha₂ : Valued.v (((a 0 : (𝕂)ˣ) : 𝕂) / ((a 1 : (𝕂)ˣ) : 𝕂)) ≤ WithZero.exp (-(N₂ : ℤ)) :=
    ha.trans (WithZero.exp_le_exp.mpr (by omega))
  simp only [Pi.add_apply, hN₁ X hX a ha₁ s t hs ht, hN₂ X hX a ha₂ s t hs ht]
  ring

theorem P23.add {W₁ W₂ : LocalGL3 v → ℂ} (h₁ : P23 v χ d W₁) (h₂ : P23 v χ d W₂) : P23 v χ d (W₁ + W₂) := by
  intro C hC
  obtain ⟨N₁, hN₁⟩ := h₁ C hC
  obtain ⟨N₂, hN₂⟩ := h₂ C hC
  refine ⟨max N₁ N₂, fun X hX a ha s t hs ht => ?_⟩
  have ha₁ : Valued.v (((a 1 : (𝕂)ˣ) : 𝕂) / ((a 2 : (𝕂)ˣ) : 𝕂)) ≤ WithZero.exp (-(N₁ : ℤ)) :=
    ha.trans (WithZero.exp_le_exp.mpr (by omega))
  have ha₂ : Valued.v (((a 1 : (𝕂)ˣ) : 𝕂) / ((a 2 : (𝕂)ˣ) : 𝕂)) ≤ WithZero.exp (-(N₂ : ℤ)) :=
    ha.trans (WithZero.exp_le_exp.mpr (by omega))
  simp only [Pi.add_apply, hN₁ X hX a ha₁ s t hs ht, hN₂ X hX a ha₂ s t hs ht]
  ring

theorem PNEG.add {W₁ W₂ : LocalGL3 v → ℂ} (h₁ : PNEG v hπ W₁) (h₂ : PNEG v hπ W₂) : PNEG v hπ (W₁ + W₂) := by
  intro C hC
  obtain ⟨L₁, hL₁⟩ := h₁ C hC
  obtain ⟨L₂, hL₂⟩ := h₂ C hC
  refine ⟨max L₁ L₂, fun y hy n hn u hu => ?_⟩
  have hn₁ : n.1 < -(L₁ : ℤ) ∨ n.2 < -(L₁ : ℤ) := by rcases hn with h | h <;> [left; right] <;> omega
  have hn₂ : n.1 < -(L₂ : ℤ) ∨ n.2 < -(L₂ : ℤ) := by rcases hn with h | h <;> [left; right] <;> omega
  obtain ⟨a₁, b₁⟩ := hL₁ y hy n hn₁ u hu
  obtain ⟨a₂, b₂⟩ := hL₂ y hy n hn₂ u hu
  simp only [Pi.add_apply, a₁, b₁, a₂, b₂, add_zero, and_self]

theorem P12.smul {W : LocalGL3 v → ℂ} (c : ℂ) (h : P12 v χ d W) : P12 v χ d (c • W) := by
  intro C hC
  obtain ⟨N, hN⟩ := h C hC
  refine ⟨N, fun X hX a ha s t hs ht => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, hN X hX a ha s t hs ht]
  ring

theorem P23.smul {W : LocalGL3 v → ℂ} (c : ℂ) (h : P23 v χ d W) : P23 v χ d (c • W) := by
  intro C hC
  obtain ⟨N, hN⟩ := h C hC
  refine ⟨N, fun X hX a ha s t hs ht => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, hN X hX a ha s t hs ht]
  ring

theorem PNEG.smul {W : LocalGL3 v → ℂ} (c : ℂ) (h : PNEG v hπ W) : PNEG v hπ (c • W) := by
  intro C hC
  obtain ⟨L, hL⟩ := h C hC
  refine ⟨L, fun y hy n hn u hu => ?_⟩
  obtain ⟨a₁, b₁⟩ := hL y hy n hn u hu
  simp only [Pi.smul_apply, smul_eq_mul, a₁, b₁, mul_zero, and_self]

end Members
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"

end LanglandsTunnell.CubicInduction.CritGenGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.HasConductorExponentAt CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd TateLocal.exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt CubicInduction.exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg TateLocal.isHaarMeasure_comap_val_mulMeasure"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply gl3CyclicSubspace transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL localMaximalCompact3 LocalGL3 diagUnitGL2 coe_diagUnitGL2 diagHom diagUnits2 coe_diagUnits2 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply diagonal3 diagonal3_mul diagonal3_coe exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg"
namespace CritGenGlue
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open Matrix Topology Filter

section Generators

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => v.adicCompletion ℚ
local notation "Mat3" => Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)

variable (W₀ : LocalGL3 v → ℂ)
  (hW₀law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W₀)
  (d : ℕ)
  (hW₀lev : ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
    (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
    ∀ g : LocalGL3 v, W₀ (g * k) = W₀ g)
  (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (kp : ℕ) (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v χ kp)

include hW₀law in

theorem isGL3PsiWhittakerFn_translate_twist (h : LocalGL3 v) :
    IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹
      (gl3AmbientRightTranslate (R := ℂ) h
        (fun g : LocalGL3 v => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W₀ g)) := by
  intro x y z g
  show ((χ (Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z * g * h)) : ℂˣ) : ℂ) * W₀ (upperUnipotent3 x y z * g * h) =
    (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ (x + y) *
      (((χ (Matrix.GeneralLinearGroup.det (g * h)) : ℂˣ) : ℂ) * W₀ (g * h))
  rw [mul_assoc, map_mul, det_upperUnipotent3, one_mul, hW₀law x y z (g * h)]
  ring

include hW₀law hW₀lev in
theorem gen_P12 (h : LocalGL3 v) :
    P12 v χ d (gl3AmbientRightTranslate (R := ℂ) h
      (fun g : LocalGL3 v => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W₀ g)) := by
  intro C hC
  have hCh : IsCompact ((fun X : LocalGL3 v => X * h) '' C) := hC.image (continuous_mul_const h)
  obtain ⟨N, hN⟩ :=
    LanglandsTunnell.CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst
      v W₀ hW₀law d hW₀lev _ hCh
  refine ⟨N, fun X hX a ha s t hs ht => ?_⟩
  have key := hN (X * h) ⟨X, hX, rfl⟩ a ha s t hs ht
  simp only [gl3AmbientRightTranslate_apply]
  rw [show diagonal3 v a * diagonal3 v ![s, t, t] * X * h = diagonal3 v a * diagonal3 v ![s, t, t] * (X * h) by
      simp only [mul_assoc],
    show diagonal3 v a * X * h = diagonal3 v a * (X * h) by simp only [mul_assoc], key]
  simp only [map_mul, det_diagonal3, Units.val_mul]
  have e0 : ((![s, t, t] : Fin 3 → (𝕂)ˣ) 0) = s := rfl
  have e1 : ((![s, t, t] : Fin 3 → (𝕂)ˣ) 1) = t := rfl
  have e2 : ((![s, t, t] : Fin 3 → (𝕂)ˣ) 2) = t := rfl
  rw [e0, e1, e2]
  ring

include hW₀law hW₀lev in
theorem gen_P23 (h : LocalGL3 v) :
    P23 v χ d (gl3AmbientRightTranslate (R := ℂ) h
      (fun g : LocalGL3 v => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W₀ g)) := by
  intro C hC
  have hCh : IsCompact ((fun X : LocalGL3 v => X * h) '' C) := hC.image (continuous_mul_const h)
  obtain ⟨N, hN⟩ :=
    LanglandsTunnell.CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd
      v W₀ hW₀law d hW₀lev _ hCh
  refine ⟨N, fun X hX a ha s t hs ht => ?_⟩
  have key := hN (X * h) ⟨X, hX, rfl⟩ a ha s t hs ht
  simp only [gl3AmbientRightTranslate_apply]
  rw [show diagonal3 v a * diagonal3 v ![t, t, s] * X * h = diagonal3 v a * diagonal3 v ![t, t, s] * (X * h) by
      simp only [mul_assoc],
    show diagonal3 v a * X * h = diagonal3 v a * (X * h) by simp only [mul_assoc], key]
  simp only [map_mul, det_diagonal3, Units.val_mul]
  have e0 : ((![t, t, s] : Fin 3 → (𝕂)ˣ) 0) = t := rfl
  have e1 : ((![t, t, s] : Fin 3 → (𝕂)ˣ) 1) = t := rfl
  have e2 : ((![t, t, s] : Fin 3 → (𝕂)ˣ) 2) = s := rfl
  rw [e0, e1, e2]
  ring

variable {ϖ : v.adicCompletionIntegers ℚ}
  (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
  (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))

include hW₀law hW₀lev hkp hϖ in
theorem gen_PNEG (h : LocalGL3 v) :
    PNEG v hπ (gl3AmbientRightTranslate (R := ℂ) h
      (fun g : LocalGL3 v => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W₀ g)) := by
  intro C hC
  have hCh : IsCompact ((fun X : LocalGL3 v => X * h) '' C) := hC.image (continuous_mul_const h)
  obtain ⟨M, hM⟩ := exists_valued_entry_le_of_isCompact v _ hCh

  set U : Subgroup (LocalGL3 v) := congr3 v (d + 2 * M) ⊓ (χ.comp (Matrix.GeneralLinearGroup.det : LocalGL3 v →* (𝕂)ˣ)).ker with hU
  have hUo : IsOpen (U : Set (LocalGL3 v)) := by
    have h1 := isOpen_congr3 v (d + 2 * M)
    have h2 : IsOpen ((χ.comp (Matrix.GeneralLinearGroup.det : LocalGL3 v →* (𝕂)ˣ)).ker : Set (LocalGL3 v)) := by
      have hker : ((χ.comp (Matrix.GeneralLinearGroup.det : LocalGL3 v →* (𝕂)ˣ)).ker : Set (LocalGL3 v)) =
          (Matrix.GeneralLinearGroup.det : LocalGL3 v → (𝕂)ˣ) ⁻¹' (χ.ker : Set (𝕂)ˣ) := by
        ext g; simp [MonoidHom.mem_ker]
      rw [hker]
      exact (isOpen_ker_of_hasConductorExponentAt v hkp).preimage (continuous_det3 v)
    rw [hU, Subgroup.coe_inf]
    exact h1.inter h2
  have hfix : ∀ y ∈ C, ∀ k' ∈ U, ∀ x : LocalGL3 v,
      gl3AmbientRightTranslate (R := ℂ) h
          (fun g : LocalGL3 v => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W₀ g) (x * k' * y) =
        gl3AmbientRightTranslate (R := ℂ) h
          (fun g : LocalGL3 v => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W₀ g) (x * y) := by
    intro y hy k' hk' x
    rw [hU, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.comp_apply] at hk'
    obtain ⟨hkc, hkχ⟩ := hk'
    obtain ⟨hmem, hcong⟩ := conj_mem_of_mem_congr3 v (le_refl (d + 2 * M)) (hM (y * h) ⟨y, hy, rfl⟩) hkc
    simp only [gl3AmbientRightTranslate_apply]
    have hgrp : x * k' * y * h = x * y * h * ((y * h)⁻¹ * k' * (y * h)) := by group
    rw [hgrp, hW₀lev _ hmem hcong, ← hgrp]
    congr 1
    simp only [map_mul, hkχ, mul_one]
  exact LanglandsTunnell.CubicInduction.exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg v _ rfl _
    (isGL3PsiWhittakerFn_translate_twist v W₀ hW₀law χ h) hπ hϖ C U hUo hfix

variable {W : LocalGL3 v → ℂ}

include hW₀law hW₀lev in
theorem P12_of_mem
    (hW : W ∈ gl3CyclicSubspace (fun g : LocalGL3 v => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W₀ g)) :
    P12 v χ d W := by
  refine Submodule.span_induction (p := fun W _ => P12 v χ d W) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩; exact gen_P12 v W₀ hW₀law d hW₀lev χ h
  · exact P12.zero v
  · intro x y _ _ hx hy; exact P12.add v hx hy
  · intro c x _ hx; exact P12.smul v c hx

include hW₀law hW₀lev in
theorem P23_of_mem
    (hW : W ∈ gl3CyclicSubspace (fun g : LocalGL3 v => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W₀ g)) :
    P23 v χ d W := by
  refine Submodule.span_induction (p := fun W _ => P23 v χ d W) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩; exact gen_P23 v W₀ hW₀law d hW₀lev χ h
  · exact P23.zero v
  · intro x y _ _ hx hy; exact P23.add v hx hy
  · intro c x _ hx; exact P23.smul v c hx

include hW₀law hW₀lev hkp hϖ in
theorem PNEG_of_mem
    (hW : W ∈ gl3CyclicSubspace (fun g : LocalGL3 v => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W₀ g)) :
    PNEG v hπ W := by
  refine Submodule.span_induction (p := fun W _ => PNEG v hπ W) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨h, rfl⟩; exact gen_PNEG v W₀ hW₀law d hW₀lev χ kp hkp hπ hϖ h
  · exact PNEG.zero v hπ
  · intro x y _ _ hx hy; exact PNEG.add v hπ hx hy
  · intro c x _ hx; exact PNEG.smul v hπ c hx

end Generators
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"

end LanglandsTunnell.CubicInduction.CritGenGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.HasConductorExponentAt CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd TateLocal.exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt CubicInduction.exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg TateLocal.isHaarMeasure_comap_val_mulMeasure"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply gl3CyclicSubspace transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL localMaximalCompact3 LocalGL3 diagUnitGL2 coe_diagUnitGL2 diagHom diagUnits2 coe_diagUnits2 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply diagonal3 diagonal3_mul diagonal3_coe exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg"
namespace CritGenGlue
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open Matrix Topology Filter

section Helpers

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => v.adicCompletion ℚ

theorem d3_comm (x y : Fin 3 → (𝕂)ˣ) : d3 v x * d3 v y = d3 v y * d3 v x := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem D2_scalar_comm (s : (𝕂)ˣ) (m : GL (Fin 2) 𝕂) : D2 v (s, s) * m = m * D2 v (s, s) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Units.val_mul, Units.val_mul, D2_apply, coe_diagUnits2]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem D2_scalar_left_comm (s : (𝕂)ˣ) (a m : GL (Fin 2) 𝕂) :
    a * (D2 v (s, s) * m) = D2 v (s, s) * (a * m) := by
  rw [← mul_assoc, ← D2_scalar_comm v s a, mul_assoc]

theorem transposeInv3_mul' (g h : LocalGL3 v) : transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  show (((g * h)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂)ᵀ =
    ((g⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂)ᵀ * ((h⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂)ᵀ
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem idealBound_pow (b : ℕ) :
    NumberField.AdelicLevel.idealBound (𝓞 ℚ) (v.asIdeal ^ b) v = WithZero.exp (-(b : ℤ)) := by
  rw [NumberField.AdelicLevel.idealBound_of_ne_bot (pow_ne_zero _ v.ne_bot), Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr v.ne_bot) (Associates.irreducible_mk.mpr v.irreducible),
    Associates.count_self (Associates.irreducible_mk.mpr v.irreducible), mul_one]

theorem isLocalLevelOne_of (b : ℕ) (m : Matrix (Fin 2) (Fin 2) 𝕂)
    (hint : ∀ i j, Valued.v (m i j) ≤ 1) (h10 : Valued.v (m 1 0) ≤ WithZero.exp (-(b : ℤ)))
    (h11 : Valued.v (m 1 1 - 1) ≤ WithZero.exp (-(b : ℤ))) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) m := by
  refine ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr (hint i j), ?_, ?_⟩
  · rw [idealBound_pow]; exact h10
  · rw [idealBound_pow]; exact h11

theorem D2_scalar_mem_localLevelOne (b : ℕ) (s : (𝕂)ˣ) (hs1 : Valued.v (s : 𝕂) = 1)
    (hsb : Valued.v ((s : 𝕂) - 1) ≤ WithZero.exp (-(b : ℤ))) :
    D2 v (s, s) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) := by
  have hs' : Valued.v (((s⁻¹ : (𝕂)ˣ)) : 𝕂) = 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, hs1, inv_one]
  have hsb' : Valued.v ((((s⁻¹ : (𝕂)ˣ)) : 𝕂) - 1) ≤ WithZero.exp (-(b : ℤ)) := by
    have : (((s⁻¹ : (𝕂)ˣ)) : 𝕂) - 1 = -((((s⁻¹ : (𝕂)ˣ)) : 𝕂) * ((s : 𝕂) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one]; ring
    rw [this, Valuation.map_neg, map_mul, hs', one_mul]; exact hsb
  have hval : ((D2 v (s, s) : GL (Fin 2) 𝕂) : Matrix (Fin 2) (Fin 2) 𝕂) = !![(s : 𝕂), 0; 0, (s : 𝕂)] := by
    rw [D2_apply, coe_diagUnits2]
  have hinv : (((D2 v (s, s))⁻¹ : GL (Fin 2) 𝕂) : Matrix (Fin 2) (Fin 2) 𝕂) =
      !![(((s⁻¹ : (𝕂)ˣ)) : 𝕂), 0; 0, (((s⁻¹ : (𝕂)ˣ)) : 𝕂)] := by
    rw [← map_inv, Prod.inv_mk, D2_apply, coe_diagUnits2]
  rw [AdelicDock.mem_localLevelOne_iff, hval, hinv]
  refine ⟨isLocalLevelOne_of v b _ ?_ ?_ ?_, isLocalLevelOne_of v b _ ?_ ?_ ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hs1.le]
  · simp
  · simpa using hsb
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hs1]
  · simp
  · simpa using hsb'

end Helpers
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"

section Engine2

attribute [local instance] LanglandsTunnell.TateLocal.localBorel AutomorphicForm.localGLBorel

variable (v : HeightOneSpectrum (𝓞 ℚ))

attribute [local instance] borelSpace_loc borelSpace_locUnits isAddHaarMeasure_selfDualHaarAt borelSpace_locGL

theorem setIntegral_sphere_eq_zero_of_mul_eq (φ : (v.adicCompletion ℚ)ˣ → ℂ) (c : ℂ) (hc : c ≠ 1)
    (s : (v.adicCompletion ℚ)ˣ) (hs : Valued.v (s : v.adicCompletion ℚ) = 1)
    (hφ : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 → φ (s * u) = c * φ u) :
    ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}, φ u
      ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) = 0 := by
  haveI := isHaarMeasure_locMul v
  have hleft := setIntegral_subgroup_mul_left (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
    (sphere v) (isOpen_sphere v).measurableSet φ (show s ∈ sphere v from hs)
  rw [coe_sphere] at hleft
  have hmul : ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}, φ (s * u)
      ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      c * ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}, φ u
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun ((isOpen_sphere v).measurableSet) fun u hu => hφ u hu
  rw [hmul] at hleft
  rcases mul_left_eq_self₀.mp hleft with h | h
  · exact absurd h hc
  · exact h

theorem setIntegral_levelOne_mul_left (b : ℕ) (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
    (G : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) {z : GL (Fin 2) (v.adicCompletion ℚ)}
    (hz : z ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b)) :
    ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
        Set (GL (Fin 2) (v.adicCompletion ℚ))), G (z * k) ∂μ₂ =
    ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
        Set (GL (Fin 2) (v.adicCompletion ℚ))), G k ∂μ₂ :=
  setIntegral_subgroup_mul_left μ₂ _
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ v (v.asIdeal ^ b) (pow_ne_zero _ v.ne_bot)).2.measurableSet G hz

theorem setIntegral_levelOne_eq_zero_of_mul_eq (b : ℕ) (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ)))
    [μ₂.IsHaarMeasure] (G : GL (Fin 2) (v.adicCompletion ℚ) → ℂ) (c : ℂ) (hc : c ≠ 1)
    {z : GL (Fin 2) (v.adicCompletion ℚ)} (hz : z ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b))
    (hG : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b), G (z * k) = c * G k) :
    ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
        Set (GL (Fin 2) (v.adicCompletion ℚ))), G k ∂μ₂ = 0 := by
  have hleft := setIntegral_levelOne_mul_left v b μ₂ G hz
  have hmul : ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
        Set (GL (Fin 2) (v.adicCompletion ℚ))), G (z * k) ∂μ₂ =
      c * ∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
        Set (GL (Fin 2) (v.adicCompletion ℚ))), G k ∂μ₂ := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun
      ((AdelicDock.isCompact_and_isOpen_localLevelOne ℚ v (v.asIdeal ^ b) (pow_ne_zero _ v.ne_bot)).2.measurableSet)
      fun k hk => hG k hk
  rw [hmul] at hleft
  rcases mul_left_eq_self₀.mp hleft with h | h
  · exact absurd h hc
  · exact h

end Engine2
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"

end LanglandsTunnell.CubicInduction.CritGenGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.HasConductorExponentAt CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd TateLocal.exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt CubicInduction.exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg TateLocal.isHaarMeasure_comap_val_mulMeasure"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply gl3CyclicSubspace transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL localMaximalCompact3 LocalGL3 diagUnitGL2 coe_diagUnitGL2 diagHom diagUnits2 coe_diagUnits2 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply diagonal3 diagonal3_mul diagonal3_coe exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg"
namespace CritGenGlue
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Ratios

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "𝕂" => v.adicCompletion ℚ

theorem exp_neg_le_exp_neg {a b : ℤ} (h : b ≤ a) : WithZero.exp (-a) ≤ WithZero.exp (-b) :=
  WithZero.exp_le_exp.mpr (by omega)

theorem ratio1 {ϖ : 𝕂} (hπ : ϖ ≠ 0) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {N' : ℤ} {n : ℤ × ℤ}
    (hn : N' ≤ n.1) (u : (𝕂)ˣ) (hu : Valued.v (u : 𝕂) = 1) :
    Valued.v (((((![Units.mk0 ϖ hπ, Units.mk0 ϖ hπ, 1] ^ n.2 * ![Units.mk0 ϖ hπ, 1, 1] ^ n.1) * e1 v u :
        Fin 3 → (𝕂)ˣ) 0 : (𝕂)ˣ) : 𝕂) /
      ((((![Units.mk0 ϖ hπ, Units.mk0 ϖ hπ, 1] ^ n.2 * ![Units.mk0 ϖ hπ, 1, 1] ^ n.1) * e1 v u :
        Fin 3 → (𝕂)ˣ) 1 : (𝕂)ˣ) : 𝕂)) ≤ WithZero.exp (-N') := by
  simp only [Pi.mul_apply, Pi.pow_apply, e1_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    _root_.one_zpow, mul_one, Units.val_mul, map_mul, map_div₀, valued_mk0_zpow hπ hϖ, hu]
  rw [← WithZero.exp_add, ← WithZero.exp_sub, WithZero.exp_le_exp]
  omega

theorem ratio3 {ϖ : 𝕂} (hπ : ϖ ≠ 0) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {N' : ℤ} {n : ℤ × ℤ}
    (hn : N' ≤ n.2) (u : (𝕂)ˣ) :
    Valued.v (((((![Units.mk0 ϖ hπ, Units.mk0 ϖ hπ, 1] ^ n.2 * ![Units.mk0 ϖ hπ, 1, 1] ^ n.1) * e1 v u :
        Fin 3 → (𝕂)ˣ) 1 : (𝕂)ˣ) : 𝕂) /
      ((((![Units.mk0 ϖ hπ, Units.mk0 ϖ hπ, 1] ^ n.2 * ![Units.mk0 ϖ hπ, 1, 1] ^ n.1) * e1 v u :
        Fin 3 → (𝕂)ˣ) 2 : (𝕂)ˣ) : 𝕂)) ≤ WithZero.exp (-N') := by
  have h2 : ((((![Units.mk0 ϖ hπ, Units.mk0 ϖ hπ, 1] ^ n.2 * ![Units.mk0 ϖ hπ, 1, 1] ^ n.1) * e1 v u :
        Fin 3 → (𝕂)ˣ) 2 : (𝕂)ˣ) : 𝕂) = 1 := by
    simp [Pi.mul_apply, Pi.pow_apply, e1_apply]
  have h1 : ((((![Units.mk0 ϖ hπ, Units.mk0 ϖ hπ, 1] ^ n.2 * ![Units.mk0 ϖ hπ, 1, 1] ^ n.1) * e1 v u :
        Fin 3 → (𝕂)ˣ) 1 : (𝕂)ˣ) : 𝕂) = ((Units.mk0 ϖ hπ ^ n.2 : (𝕂)ˣ) : 𝕂) := by
    simp [Pi.mul_apply, Pi.pow_apply, e1_apply]
  rw [h1, h2, div_one, valued_mk0_zpow hπ hϖ, WithZero.exp_le_exp]
  omega

theorem ratio2 {ϖ : 𝕂} (hπ : ϖ ≠ 0) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {N' : ℤ} {n : ℤ × ℤ}
    (hn : N' ≤ n.1) (u : (𝕂)ˣ) (hu : Valued.v (u : 𝕂) = 1) :
    Valued.v ((((![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] * e3inv v u :
        Fin 3 → (𝕂)ˣ) 1 : (𝕂)ˣ) : 𝕂) /
      (((![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] * e3inv v u :
        Fin 3 → (𝕂)ˣ) 2 : (𝕂)ˣ) : 𝕂)) ≤ WithZero.exp (-N') := by
  have h1 : (((![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] * e3inv v u :
        Fin 3 → (𝕂)ˣ) 1 : (𝕂)ˣ) : 𝕂) = ((Units.mk0 ϖ hπ ^ n.2 : (𝕂)ˣ) : 𝕂)⁻¹ := by
    simp [Pi.mul_apply, e3inv_apply]
  have h2 : (((![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] * e3inv v u :
        Fin 3 → (𝕂)ˣ) 2 : (𝕂)ˣ) : 𝕂) =
        (((Units.mk0 ϖ hπ ^ n.2 : (𝕂)ˣ) : 𝕂) * ((Units.mk0 ϖ hπ ^ n.1 : (𝕂)ˣ) : 𝕂))⁻¹ * (u : 𝕂)⁻¹ := by
    simp [Pi.mul_apply, e3inv_apply]
  rw [h1, h2, map_div₀, map_mul, map_inv₀, map_inv₀, map_inv₀, map_mul, valued_mk0_zpow hπ hϖ, valued_mk0_zpow hπ hϖ,
    hu, inv_one, mul_one, ← WithZero.exp_add, ← WithZero.exp_neg, ← WithZero.exp_neg, ← WithZero.exp_sub,
    WithZero.exp_le_exp]
  omega

theorem ratio4 {ϖ : 𝕂} (hπ : ϖ ≠ 0) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {N' : ℤ} {n : ℤ × ℤ}
    (hn : N' ≤ n.2) (u : (𝕂)ˣ) :
    Valued.v ((((![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] * e3inv v u :
        Fin 3 → (𝕂)ˣ) 0 : (𝕂)ˣ) : 𝕂) /
      (((![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] * e3inv v u :
        Fin 3 → (𝕂)ˣ) 1 : (𝕂)ˣ) : 𝕂)) ≤ WithZero.exp (-N') := by
  have h0 : (((![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] * e3inv v u :
        Fin 3 → (𝕂)ˣ) 0 : (𝕂)ˣ) : 𝕂) = 1 := by
    simp [Pi.mul_apply, e3inv_apply]
  have h1 : (((![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] * e3inv v u :
        Fin 3 → (𝕂)ˣ) 1 : (𝕂)ˣ) : 𝕂) = ((Units.mk0 ϖ hπ ^ n.2 : (𝕂)ˣ) : 𝕂)⁻¹ := by
    simp [Pi.mul_apply, e3inv_apply]
  rw [h0, h1, one_div, inv_inv, valued_mk0_zpow hπ hϖ, WithZero.exp_le_exp]
  omega

end Ratios
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"

end LanglandsTunnell.CubicInduction.CritGenGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.HasConductorExponentAt CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst CubicInduction.exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd TateLocal.exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt CubicInduction.exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg TateLocal.isHaarMeasure_comap_val_mulMeasure"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply gl3CyclicSubspace transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL coe_iotaGL localMaximalCompact3 LocalGL3 diagUnitGL2 coe_diagUnitGL2 diagHom diagUnits2 coe_diagUnits2 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply diagonal3 diagonal3_mul diagonal3_coe exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_fst exists_forall_apply_diagonal3_mul_diagonal3_mul_eq_of_isCompact_of_valued_le_snd exists_forall_apply_iotaGL_mul_eq_zero_of_lt_neg"
namespace CritGenGlue
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Invariances

variable (v : HeightOneSpectrum (𝓞 ℚ)) {χ : (v.adicCompletion ℚ)ˣ →* ℂˣ} {d : ℕ} {W : LocalGL3 v → ℂ}
  {ϖ : v.adicCompletion ℚ} (hπ : ϖ ≠ 0) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
  (g₃ : LocalGL3 v) (k₀ : GL (Fin 2) (v.adicCompletion ℚ)) (b : ℕ)

include hϖ in

theorem inv_fst_primal (hW : P12 v χ d W) :
    ∃ N : ℕ, ∀ n : ℤ × ℤ, (N : ℤ) ≤ n.1 → ∀ s : ((v.adicCompletion ℚ))ˣ, s ∈ higherUnitsAt ℚ v d →
      ∀ u : ((v.adicCompletion ℚ))ˣ, Valued.v (u : (v.adicCompletion ℚ)) = 1 →
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b),
        W (iotaGL ((UnramifiedWhittaker.scalarPi ϖ hπ ^ n.2 * diagUnitGL2 (Units.mk0 ϖ hπ ^ n.1 * (s * u))) * (k₀ * k)) * g₃) = ((χ s : ℂˣ) : ℂ) * W (iotaGL ((UnramifiedWhittaker.scalarPi ϖ hπ ^ n.2 * diagUnitGL2 (Units.mk0 ϖ hπ ^ n.1 * u)) * (k₀ * k)) * g₃) := by
  have hC : IsCompact ((fun k : GL (Fin 2) (v.adicCompletion ℚ) => iotaGL (k₀ * k) * g₃) ''
      (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) : Set (GL (Fin 2) (v.adicCompletion ℚ)))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ v (v.asIdeal ^ b) (pow_ne_zero _ v.ne_bot)).1.image
      (((continuous_iotaGL v).comp (continuous_const.mul continuous_id)).mul continuous_const)
  obtain ⟨N, hN⟩ := hW _ hC
  have hone : (1 : ((v.adicCompletion ℚ))ˣ) ∈ higherUnitsAt ℚ v d := by
    rw [mem_higherUnitsAt_iff]
    refine ⟨by simp, Or.inr ?_⟩
    simp only [Units.val_one, sub_self, map_zero]
    exact zero_le'
  refine ⟨N, fun n hn s hs u hu k hk => ?_⟩
  have eA : ((![Units.mk0 ϖ hπ, Units.mk0 ϖ hπ, 1] ^ n.2 * ![Units.mk0 ϖ hπ, 1, 1] ^ n.1 : Fin 3 → ((v.adicCompletion ℚ))ˣ)) * e1 v (s * u) = ((![Units.mk0 ϖ hπ, Units.mk0 ϖ hπ, 1] ^ n.2 * ![Units.mk0 ϖ hπ, 1, 1] ^ n.1 : Fin 3 → ((v.adicCompletion ℚ))ˣ)) * e1 v u * ![s, 1, 1] := by
    rw [map_mul, mul_comm (e1 v s) (e1 v u), ← mul_assoc]
    rfl
  have key := hN _ ⟨k, hk, rfl⟩ (((![Units.mk0 ϖ hπ, Units.mk0 ϖ hπ, 1] ^ n.2 * ![Units.mk0 ϖ hπ, 1, 1] ^ n.1 : Fin 3 → ((v.adicCompletion ℚ))ˣ)) * e1 v u) (ratio1 hπ hϖ hn u hu) s 1 hs hone
  rw [arg_fst, arg_fst, d3_apply, d3_apply, d3_apply, ← diagonal3_mul, ← diagonal3_mul, eA,
    diagonal3_mul v (_ * e1 v u) ![s, 1, 1], key]
  simp only [map_one, Units.val_one, one_pow, mul_one]

include hϖ in

theorem inv_fst_dual (hW : P23 v χ d W) :
    ∃ N : ℕ, ∀ n : ℤ × ℤ, (N : ℤ) ≤ n.1 → ∀ s : ((v.adicCompletion ℚ))ˣ, s⁻¹ ∈ higherUnitsAt ℚ v d →
      ∀ u : ((v.adicCompletion ℚ))ˣ, Valued.v (u : (v.adicCompletion ℚ)) = 1 →
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b),
        dualWhittakerFn3 (fun x => W (x * g₃)) (iotaGL ((UnramifiedWhittaker.scalarPi ϖ hπ ^ n.2 * diagUnitGL2 (Units.mk0 ϖ hπ ^ n.1 * (s * u))) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) =
        (((χ s)⁻¹ : ℂˣ) : ℂ) *
          dualWhittakerFn3 (fun x => W (x * g₃)) (iotaGL ((UnramifiedWhittaker.scalarPi ϖ hπ ^ n.2 * diagUnitGL2 (Units.mk0 ϖ hπ ^ n.1 * u)) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) := by
  have hC : IsCompact ((fun k : GL (Fin 2) (v.adicCompletion ℚ) => longWeyl3 * iotaGL (AutomorphicForm.transposeInvN (Fin 2) k₀ * k) * g₃) ''
      (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) : Set (GL (Fin 2) (v.adicCompletion ℚ)))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ v (v.asIdeal ^ b) (pow_ne_zero _ v.ne_bot)).1.image
      ((continuous_const.mul ((continuous_iotaGL v).comp (continuous_const.mul continuous_id))).mul continuous_const)
  obtain ⟨N, hN⟩ := hW _ hC
  have hone : (1 : ((v.adicCompletion ℚ))ˣ) ∈ higherUnitsAt ℚ v d := by
    rw [mem_higherUnitsAt_iff]
    refine ⟨by simp, Or.inr ?_⟩
    simp only [Units.val_one, sub_self, map_zero]
    exact zero_le'
  have hkτ : ∀ k : GL (Fin 2) (v.adicCompletion ℚ),
      k₀ * AutomorphicForm.transposeInvN (Fin 2) k =
        AutomorphicForm.transposeInvN (Fin 2) (AutomorphicForm.transposeInvN (Fin 2) k₀ * k) := by
    intro k
    rw [transposeInvN_mul, transposeInvN_transposeInvN]
  refine ⟨N, fun n hn s hs u hu k hk => ?_⟩
  have eA : ((![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] : Fin 3 → ((v.adicCompletion ℚ))ˣ)) * e3inv v (s * u) = ((![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] : Fin 3 → ((v.adicCompletion ℚ))ˣ)) * e3inv v u * ![1, 1, s⁻¹] := by
    rw [map_mul, mul_comm (e3inv v s) (e3inv v u), ← mul_assoc]
    rfl
  have key := hN _ ⟨k, hk, rfl⟩ (((![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] : Fin 3 → ((v.adicCompletion ℚ))ˣ)) * e3inv v u) (ratio2 hπ hϖ hn u hu) s⁻¹ 1 hs hone
  simp only [dualWhittakerFn3_apply]
  rw [hkτ, arg_snd, arg_snd, d3_apply, d3_apply, d3_apply, ← diagonal3_mul, ← diagonal3_mul, eA,
    diagonal3_mul v (_ * e3inv v u) ![1, 1, s⁻¹], key]
  simp only [map_one, Units.val_one, one_pow, mul_one, map_inv]

include hϖ in

theorem inv_snd_primal (hW : P23 v χ d W) :
    ∃ N : ℕ, ∀ n : ℤ × ℤ, (N : ℤ) ≤ n.2 → ∀ s : ((v.adicCompletion ℚ))ˣ, s ∈ higherUnitsAt ℚ v d →
      ∀ u : ((v.adicCompletion ℚ))ˣ, ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b),
        W (iotaGL ((UnramifiedWhittaker.scalarPi ϖ hπ ^ n.2 * diagUnitGL2 (Units.mk0 ϖ hπ ^ n.1 * u)) * (k₀ * (D2 v (s, s) * k))) * g₃) =
        ((χ s : ℂˣ) : ℂ) ^ 2 * W (iotaGL ((UnramifiedWhittaker.scalarPi ϖ hπ ^ n.2 * diagUnitGL2 (Units.mk0 ϖ hπ ^ n.1 * u)) * (k₀ * k)) * g₃) := by
  have hC : IsCompact ((fun k : GL (Fin 2) (v.adicCompletion ℚ) => iotaGL (k₀ * k) * g₃) ''
      (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) : Set (GL (Fin 2) (v.adicCompletion ℚ)))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ v (v.asIdeal ^ b) (pow_ne_zero _ v.ne_bot)).1.image
      (((continuous_iotaGL v).comp (continuous_const.mul continuous_id)).mul continuous_const)
  obtain ⟨N, hN⟩ := hW _ hC
  have hone : (1 : ((v.adicCompletion ℚ))ˣ) ∈ higherUnitsAt ℚ v d := by
    rw [mem_higherUnitsAt_iff]
    refine ⟨by simp, Or.inr ?_⟩
    simp only [Units.val_one, sub_self, map_zero]
    exact zero_le'
  have ez := D2_scalar_left_comm v
  refine ⟨N, fun n hn s hs u k hk => ?_⟩
  have key := hN _ ⟨k, hk, rfl⟩ (((![Units.mk0 ϖ hπ, Units.mk0 ϖ hπ, 1] ^ n.2 * ![Units.mk0 ϖ hπ, 1, 1] ^ n.1 : Fin 3 → ((v.adicCompletion ℚ))ˣ)) * e1 v u) (ratio3 hπ hϖ hn u) 1 s hone hs
  have eL : iotaGL ((UnramifiedWhittaker.scalarPi ϖ hπ ^ n.2 * diagUnitGL2 (Units.mk0 ϖ hπ ^ n.1 * u)) * (k₀ * (D2 v (s, s) * k))) * g₃ =
      diagonal3 v (((![Units.mk0 ϖ hπ, Units.mk0 ϖ hπ, 1] ^ n.2 * ![Units.mk0 ϖ hπ, 1, 1] ^ n.1 : Fin 3 → ((v.adicCompletion ℚ))ˣ)) * e1 v u) * diagonal3 v ![s, s, 1] * (iotaGL (k₀ * k) * g₃) := by
    rw [ez s k₀ k, ez s, map_mul iotaGL (D2 v (s, s)), iotaGL_D2, mul_assoc, arg_fst, d3_apply, d3_apply, d3_apply,
      ← diagonal3_mul, ← mul_assoc, ← diagonal3_mul, ← diagonal3_mul, mul_comm (![s, s, 1] : Fin 3 → ((v.adicCompletion ℚ))ˣ)]
  have eR : iotaGL ((UnramifiedWhittaker.scalarPi ϖ hπ ^ n.2 * diagUnitGL2 (Units.mk0 ϖ hπ ^ n.1 * u)) * (k₀ * k)) * g₃ = diagonal3 v (((![Units.mk0 ϖ hπ, Units.mk0 ϖ hπ, 1] ^ n.2 * ![Units.mk0 ϖ hπ, 1, 1] ^ n.1 : Fin 3 → ((v.adicCompletion ℚ))ˣ)) * e1 v u) * (iotaGL (k₀ * k) * g₃) := by
    rw [arg_fst, d3_apply, d3_apply, ← diagonal3_mul]
  rw [eL, eR, key]
  simp only [map_one, Units.val_one, one_mul]

include hϖ in

theorem inv_snd_dual (hW : P12 v χ d W) :
    ∃ N : ℕ, ∀ n : ℤ × ℤ, (N : ℤ) ≤ n.2 → ∀ s : ((v.adicCompletion ℚ))ˣ, s ∈ higherUnitsAt ℚ v d →
      ∀ u : ((v.adicCompletion ℚ))ˣ, ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b),
        dualWhittakerFn3 (fun x => W (x * g₃)) (iotaGL ((UnramifiedWhittaker.scalarPi ϖ hπ ^ n.2 * diagUnitGL2 (Units.mk0 ϖ hπ ^ n.1 * u)) *
            (k₀ * AutomorphicForm.transposeInvN (Fin 2) (D2 v (s, s) * k)))) =
        ((χ s : ℂˣ) : ℂ) ^ 2 *
          dualWhittakerFn3 (fun x => W (x * g₃)) (iotaGL ((UnramifiedWhittaker.scalarPi ϖ hπ ^ n.2 * diagUnitGL2 (Units.mk0 ϖ hπ ^ n.1 * u)) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) := by
  have hC : IsCompact ((fun k : GL (Fin 2) (v.adicCompletion ℚ) => longWeyl3 * iotaGL (AutomorphicForm.transposeInvN (Fin 2) k₀ * k) * g₃) ''
      (AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) : Set (GL (Fin 2) (v.adicCompletion ℚ)))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ v (v.asIdeal ^ b) (pow_ne_zero _ v.ne_bot)).1.image
      ((continuous_const.mul ((continuous_iotaGL v).comp (continuous_const.mul continuous_id))).mul continuous_const)
  obtain ⟨N, hN⟩ := hW _ hC
  have hone : (1 : ((v.adicCompletion ℚ))ˣ) ∈ higherUnitsAt ℚ v d := by
    rw [mem_higherUnitsAt_iff]
    refine ⟨by simp, Or.inr ?_⟩
    simp only [Units.val_one, sub_self, map_zero]
    exact zero_le'
  have hkτ : ∀ k : GL (Fin 2) (v.adicCompletion ℚ),
      k₀ * AutomorphicForm.transposeInvN (Fin 2) k =
        AutomorphicForm.transposeInvN (Fin 2) (AutomorphicForm.transposeInvN (Fin 2) k₀ * k) := by
    intro k
    rw [transposeInvN_mul, transposeInvN_transposeInvN]
  have ez' := D2_scalar_left_comm v
  refine ⟨N, fun n hn s hs u k hk => ?_⟩
  have key := hN _ ⟨k, hk, rfl⟩ (((![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] : Fin 3 → ((v.adicCompletion ℚ))ˣ)) * e3inv v u) (ratio4 hπ hϖ hn u) 1 s hone hs
  simp only [dualWhittakerFn3_apply]
  have eL : longWeyl3 * transposeInv3 (iotaGL ((UnramifiedWhittaker.scalarPi ϖ hπ ^ n.2 * diagUnitGL2 (Units.mk0 ϖ hπ ^ n.1 * u)) *
        (k₀ * AutomorphicForm.transposeInvN (Fin 2) (D2 v (s, s) * k)))) * g₃ =
      diagonal3 v (((![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] : Fin 3 → ((v.adicCompletion ℚ))ˣ)) * e3inv v u) * diagonal3 v ![1, s, s] *
        (longWeyl3 * iotaGL (AutomorphicForm.transposeInvN (Fin 2) k₀ * k) * g₃) := by
    rw [transposeInvN_mul, transposeInvN_D2, ez' s⁻¹ k₀, ez' s⁻¹, map_mul iotaGL (D2 v (s⁻¹, s⁻¹)), transposeInv3_mul',
      transposeInv3_iotaGL, transposeInvN_D2, inv_inv, iotaGL_D2, ← mul_assoc longWeyl3,
      longWeyl3_mul_d3, d3_apply, mul_assoc (diagonal3 v _) longWeyl3, mul_assoc (diagonal3 v _) (longWeyl3 * _) g₃,
      hkτ, arg_snd, d3_apply, d3_apply, ← diagonal3_mul, ← mul_assoc, ← diagonal3_mul, ← diagonal3_mul,
      mul_comm (![1, s, s] : Fin 3 → ((v.adicCompletion ℚ))ˣ)]
  have eR : longWeyl3 * transposeInv3 (iotaGL ((UnramifiedWhittaker.scalarPi ϖ hπ ^ n.2 * diagUnitGL2 (Units.mk0 ϖ hπ ^ n.1 * u)) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) * g₃ =
      diagonal3 v (((![1, (Units.mk0 ϖ hπ ^ n.2)⁻¹, (Units.mk0 ϖ hπ ^ n.2 * Units.mk0 ϖ hπ ^ n.1)⁻¹] : Fin 3 → ((v.adicCompletion ℚ))ˣ)) * e3inv v u) * (longWeyl3 * iotaGL (AutomorphicForm.transposeInvN (Fin 2) k₀ * k) * g₃) := by
    rw [hkτ, arg_snd, d3_apply, d3_apply, ← diagonal3_mul]
  rw [eL, eR, key]
  simp only [map_one, Units.val_one, one_mul]

end Invariances
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"

end LanglandsTunnell.CubicInduction.CritGenGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction.CritGenGlue"

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.CritGenGlue in
open scoped Classical in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))

    (W₀ : LocalGL3 p → ℂ)
    (hW₀law : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₀)
    (d : ℕ)
    (hW₀lev : ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
      (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
          (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
      ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g)
    (ω₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω₀ : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₀ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω₀ t : ℂˣ) : ℂ) * W₀ h)

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1)
    (kp : ℕ) (hkp : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ kp)

    (hW₃adm : ∀ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) →
      ∃ B : Finset (LocalGL3 p → ℂ), ∀ W ∈ gl3CyclicSubspace
        (fun g : LocalGL3 p => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W₀ g),
        (∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (LocalGL3 p → ℂ)))

    (b : ℕ)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (hkβ : 6 * (b + 3 * d + 3) + 7 ≤ kp) :
    ∀ W ∈ gl3CyclicSubspace (fun g : LocalGL3 p => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W₀ g),
    ∀ (g₃ : LocalGL3 p) (k₀ : GL (Fin 2) (p.adicCompletion ℚ)) (η : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (c : ℕ),
    LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p η c → c ≤ b →
    letI := localBorel ℚ p
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∃ T : Finset (ℤ × ℤ), ∀ n : ℤ × ℤ, n ∉ T →
        (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
            (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                  Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                W (iotaGL (UnramifiedWhittaker.scalarPi
                      (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                      ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0 ∧
        (∫ u in {u : (p.adicCompletion ℚ)ˣ | Valued.v (u : p.adicCompletion ℚ) = 1},
            (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
                  Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
                dualWhittakerFn3 (fun x => W (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                      (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ
                      ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) = 0 := by
  intro W hW g₃ k₀ η c hη hcb μ₂ hμ₂
  letI : MeasurableSpace (p.adicCompletion ℚ) := localBorel ℚ p
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  have hK₁ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p (p.asIdeal ^ b) (pow_ne_zero _ p.ne_bot)

  have hcι := continuous_iotaGL p
  have hC₁ : IsCompact ((fun k : GL (Fin 2) (p.adicCompletion ℚ) => iotaGL (k₀ * k) * g₃) ''
      (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) : Set (GL (Fin 2) (p.adicCompletion ℚ)))) :=
    hK₁.1.image ((hcι.comp (continuous_const.mul continuous_id)).mul continuous_const)
  have hC₃ : IsCompact ((fun k : GL (Fin 2) (p.adicCompletion ℚ) => iotaGL (transposeInvN (Fin 2) k₀ * k) * g₃) ''
      (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) : Set (GL (Fin 2) (p.adicCompletion ℚ)))) :=
    hK₁.1.image ((hcι.comp (continuous_const.mul continuous_id)).mul continuous_const)

  obtain ⟨L, hL⟩ := PNEG_of_mem p W₀ hW₀law d hW₀lev χ kp hkp hπ hϖ hW _ (hC₁.union hC₃)
  obtain ⟨N₁, hN₁⟩ := inv_fst_primal p hπ hϖ g₃ k₀ b (P12_of_mem p W₀ hW₀law d hW₀lev χ hW)
  obtain ⟨N₂, hN₂⟩ := inv_fst_dual p hπ hϖ g₃ k₀ b (P23_of_mem p W₀ hW₀law d hW₀lev χ hW)
  obtain ⟨N₃, hN₃⟩ := inv_snd_primal p hπ hϖ g₃ k₀ b (P23_of_mem p W₀ hW₀law d hW₀lev χ hW)
  obtain ⟨N₄, hN₄⟩ := inv_snd_dual p hπ hϖ g₃ k₀ b (P12_of_mem p W₀ hW₀law d hW₀lev χ hW)

  have hm4 : max b d + 4 ≤ kp := by omega
  obtain ⟨s₁, hs₁m, hs₁χ⟩ := hkp.2 (max b d) (by omega)
  obtain ⟨⟨s₂, hs₂m, hs₂χ⟩, -⟩ :=
    LanglandsTunnell.TateLocal.exists_mem_higherUnitsAt_pow_two_ne_one_and_pow_three_ne_one_of_hasConductorExponentAt
      p χ kp hkp (max b d) hm4
  have hUd : higherUnitsAt ℚ p (max b d) ≤ higherUnitsAt ℚ p d := higherUnitsAt_antitone ℚ p (le_max_right b d)
  have hUb : higherUnitsAt ℚ p (max b d) ≤ higherUnitsAt ℚ p b := higherUnitsAt_antitone ℚ p (le_max_left b d)
  have hUc : higherUnitsAt ℚ p b ≤ higherUnitsAt ℚ p c := higherUnitsAt_antitone ℚ p hcb
  have hs₁d : s₁ ∈ higherUnitsAt ℚ p d := hUd hs₁m
  have hs₂d : s₂ ∈ higherUnitsAt ℚ p d := hUd hs₂m
  have hs₁1 : Valued.v (s₁ : (p.adicCompletion ℚ)) = 1 := ((mem_higherUnitsAt_iff ℚ p).mp hs₁m).1
  have hs₂1 : Valued.v (s₂ : (p.adicCompletion ℚ)) = 1 := ((mem_higherUnitsAt_iff ℚ p).mp hs₂m).1
  have hη₁ : η s₁ = 1 := hη.1 s₁ (hUc (hUb hs₁m))
  have hs₁inv : s₁⁻¹ ∈ higherUnitsAt ℚ p d := by
    obtain ⟨h1, h2⟩ := (mem_higherUnitsAt_iff ℚ p).mp hs₁d
    have h1' : Valued.v (((s₁⁻¹ : ((p.adicCompletion ℚ))ˣ)) : (p.adicCompletion ℚ)) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, h1, inv_one]
    rw [mem_higherUnitsAt_iff]
    refine ⟨h1', ?_⟩
    rcases h2 with h0 | h2
    · exact Or.inl h0
    · right
      have : (((s₁⁻¹ : ((p.adicCompletion ℚ))ˣ)) : (p.adicCompletion ℚ)) - 1 = -((((s₁⁻¹ : ((p.adicCompletion ℚ))ˣ)) : (p.adicCompletion ℚ)) * ((s₁ : (p.adicCompletion ℚ)) - 1)) := by
        rw [mul_sub, Units.inv_mul, mul_one]; ring
      rw [this, Valuation.map_neg, map_mul, h1', one_mul]; exact h2
  have hs₂b : Valued.v ((s₂ : (p.adicCompletion ℚ)) - 1) ≤ WithZero.exp (-(b : ℤ)) := by
    obtain ⟨-, h⟩ := (mem_higherUnitsAt_iff ℚ p).mp (hUb hs₂m)
    rcases h with h0 | h
    · rw [h0, Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact le_trans (Valuation.map_sub _ _ _) (max_le hs₂1.le (by rw [Valuation.map_one]))
    · exact h
  have hz : D2 p (s₂, s₂) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :=
    D2_scalar_mem_localLevelOne p b s₂ hs₂1 hs₂b
  have hχ₁ : ((χ s₁ : ℂˣ) : ℂ) ≠ 1 := fun h => hs₁χ (Units.val_eq_one.mp h)
  have hχ₁' : (((χ s₁)⁻¹ : ℂˣ) : ℂ) ≠ 1 := fun h => hs₁χ (inv_eq_one.mp (Units.val_eq_one.mp h))
  have hχ₂ : ((χ s₂ : ℂˣ) : ℂ) ^ 2 ≠ 1 := fun h => hs₂χ (Units.val_eq_one.mp (by rw [Units.val_pow_eq_pow_val]; exact h))

  set N : ℕ := max (max N₁ N₂) (max N₃ N₄) with hN
  refine ⟨(Finset.Icc (-(L : ℤ)) (N : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (N : ℤ)), fun n hn => ?_⟩
  have hcase : (n.1 < -(L : ℤ) ∨ n.2 < -(L : ℤ)) ∨ ((N : ℤ) < n.1 ∨ (N : ℤ) < n.2) := by
    simp only [Finset.mem_product, Finset.mem_Icc, not_and_or, not_le] at hn
    omega
  rcases hcase with hneg | hpos
  ·
    refine ⟨?_, ?_⟩
    · refine setIntegral_sphere_eq_zero_of_mul_eq p _ 0 zero_ne_one 1 (by simp) fun u hu => ?_
      rw [one_mul, zero_mul]
      rw [setIntegral_levelOne_eq_zero_of_mul_eq p b μ₂ _ 0 zero_ne_one (Subgroup.one_mem _) fun k hk => ?_, zero_mul]
      rw [one_mul, zero_mul]
      have h0 := (hL _ (Or.inl ⟨k, hk, rfl⟩) n hneg u hu).1
      simpa only [map_mul, mul_assoc] using h0
    · refine setIntegral_sphere_eq_zero_of_mul_eq p _ 0 zero_ne_one 1 (by simp) fun u hu => ?_
      rw [one_mul, zero_mul]
      rw [setIntegral_levelOne_eq_zero_of_mul_eq p b μ₂ _ 0 zero_ne_one (Subgroup.one_mem _) fun k hk => ?_, zero_mul]
      rw [one_mul, zero_mul]
      have h0 := (hL _ (Or.inr ⟨k, hk, rfl⟩) n hneg u hu).2
      simpa only [dualWhittakerFn3_apply, map_mul, transposeInv3_mul', transposeInv3_iotaGL, transposeInvN_mul,
        transposeInvN_transposeInvN, mul_assoc] using h0
  rcases hpos with h1 | h2
  ·
    have hN₁le : (N₁ : ℤ) ≤ n.1 := by omega
    have hN₂le : (N₂ : ℤ) ≤ n.1 := by omega
    refine ⟨?_, ?_⟩
    · refine setIntegral_sphere_eq_zero_of_mul_eq p _ ((χ s₁ : ℂˣ) : ℂ) hχ₁ s₁ hs₁1 fun u hu => ?_
      rw [map_mul, Units.val_mul, hη₁, Units.val_one, one_mul,
        setIntegral_congr_fun hK₁.2.measurableSet (hN₁ n hN₁le s₁ hs₁d u hu), integral_const_mul, mul_assoc]
    · refine setIntegral_sphere_eq_zero_of_mul_eq p _ (((χ s₁)⁻¹ : ℂˣ) : ℂ) hχ₁' s₁ hs₁1 fun u hu => ?_
      rw [map_mul, Units.val_mul, hη₁, Units.val_one, one_mul,
        setIntegral_congr_fun hK₁.2.measurableSet (hN₂ n hN₂le s₁ hs₁inv u hu), integral_const_mul, mul_assoc]
  ·
    have hN₃le : (N₃ : ℤ) ≤ n.2 := by omega
    have hN₄le : (N₄ : ℤ) ≤ n.2 := by omega
    refine ⟨?_, ?_⟩
    · refine setIntegral_sphere_eq_zero_of_mul_eq p _ 0 zero_ne_one 1 (by simp) fun u hu => ?_
      rw [one_mul, zero_mul]
      have hI : (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
          Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
          W (iotaGL ((UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
          diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.1 * u)) * (k₀ * k)) * g₃) ∂μ₂) = 0 :=
        setIntegral_levelOne_eq_zero_of_mul_eq p b μ₂
          (fun k => W (iotaGL ((UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
          diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.1 * u)) * (k₀ * k)) * g₃)) (((χ s₂ : ℂˣ) : ℂ) ^ 2) hχ₂ hz (hN₃ n hN₃le s₂ hs₂d u)
      rw [hI, zero_mul]
    · refine setIntegral_sphere_eq_zero_of_mul_eq p _ 0 zero_ne_one 1 (by simp) fun u hu => ?_
      rw [one_mul, zero_mul]
      have hI : (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) :
          Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) : Set (GL (Fin 2) (p.adicCompletion ℚ))),
          dualWhittakerFn3 (fun x => W (x * g₃)) (iotaGL ((UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
          diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.1 * u)) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) = 0 :=
        setIntegral_levelOne_eq_zero_of_mul_eq p b μ₂
          (fun k => dualWhittakerFn3 (fun x => W (x * g₃)) (iotaGL ((UnramifiedWhittaker.scalarPi (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.2 *
          diagUnitGL2 (Units.mk0 (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ ^ n.1 * u)) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))))
          (((χ s₂ : ℂˣ) : ℂ) ^ 2) hχ₂ hz (hN₄ n hN₄le s₂ hs₂d u)
      rw [hI, zero_mul]

end S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_gl3CyclicSubspace_twist_det_torusFinite_of_principalLevel_of_admissible_of_deepTwist (solution)
