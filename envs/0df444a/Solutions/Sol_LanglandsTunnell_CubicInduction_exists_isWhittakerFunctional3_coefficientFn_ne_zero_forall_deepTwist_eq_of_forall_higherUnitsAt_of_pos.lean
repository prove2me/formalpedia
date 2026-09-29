-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/6233108d-d9f9-547d-b86d-056fddad164d

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
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors

open scoped Classical

namespace Ws46
namespace LV

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal Filter Topology MeasureTheory

variable (p : HeightOneSpectrum (𝓞 ℚ))

noncomputable def tw (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 p) : ℂ :=
  ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)

theorem tw_mul (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (g h : LocalGL3 p) : tw p χ (g * h) = tw p χ g * tw p χ h := by
  simp only [tw, map_mul, Units.val_mul]

theorem tw_ne_zero (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 p) : tw p χ g ≠ 0 := Units.ne_zero _

theorem tw_inv_char (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 p) : tw p χ⁻¹ g = (tw p χ g)⁻¹ := by
  simp only [tw, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]

theorem det_upperUnipotent3 (x y z : p.adicCompletion ℚ) :
    Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z : LocalGL3 p) = 1 := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_three]

theorem det_diagonal3 (a : Fin 3 → (p.adicCompletion ℚ)ˣ) :
    Matrix.GeneralLinearGroup.det (diagonal3 p a) = a 0 * a 1 * a 2 := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_diagonal, Fin.prod_univ_three]

theorem tw_upperUnipotent3 (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (x y z : p.adicCompletion ℚ) :
    tw p χ (upperUnipotent3 x y z) = 1 := by
  simp only [tw, det_upperUnipotent3, map_one, Units.val_one]

theorem tw_diagonal3 (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (a : Fin 3 → (p.adicCompletion ℚ)ˣ) :
    tw p χ (diagonal3 p a) = ((χ (a 0) : ℂˣ) : ℂ) * ((χ (a 1) : ℂˣ) : ℂ) * ((χ (a 2) : ℂˣ) : ℂ) := by
  simp only [tw, det_diagonal3, map_mul, Units.val_mul]

theorem continuous_det3 : Continuous (Matrix.GeneralLinearGroup.det : LocalGL3 p → (p.adicCompletion ℚ)ˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : (Units.val ∘ (Matrix.GeneralLinearGroup.det : LocalGL3 p → (p.adicCompletion ℚ)ˣ)) =
        fun g : LocalGL3 p => ((g : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))).det := by
      funext g; simp [Matrix.GeneralLinearGroup.val_det_apply]
    rw [this]; exact Units.continuous_val.matrix_det
  · have : (fun g : LocalGL3 p => (((Matrix.GeneralLinearGroup.det g)⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) =
        fun g : LocalGL3 p => (((g⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))).det := by
      funext g; rw [← map_inv]; simp [Matrix.GeneralLinearGroup.val_det_apply]
    refine (continuous_congr (fun g => congrFun this g)).2 ?_
    exact Units.continuous_coe_inv.matrix_det

theorem isLocallyConstant_tw (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) : IsLocallyConstant (tw p χ) :=
  ((hχ.comp_continuous (continuous_det3 p)).comp (fun u : ℂˣ => (u : ℂ)))

theorem torusChar3_twist (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (a : Fin 3 → (p.adicCompletion ℚ)ˣ) :
    torusChar3 p lam a = torusChar3 p (fun i => lam i * χ⁻¹) a * tw p χ (diagonal3 p a) := by
  simp only [torusChar3, tw_diagonal3, Fin.prod_univ_three, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul,
    Units.val_inv_eq_inv_val]
  field_simp

theorem twist_mem (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    {f₀ : LocalGL3 p → ℂ} (hf₀ : f₀ ∈ principalSeries3 p (fun i => lam i * χ⁻¹)) :
    (fun g => tw p χ g * f₀ g) ∈ principalSeries3 p lam := by
  obtain ⟨hlc, hn, ht⟩ := mem_principalSeries3_iff.mp hf₀
  refine mem_principalSeries3_iff.mpr ⟨(isLocallyConstant_tw p χ hχ).comp₂ hlc (· * ·), fun x y z g => ?_, fun a g => ?_⟩
  · show tw p χ _ * f₀ _ = tw p χ g * f₀ g
    rw [tw_mul, tw_upperUnipotent3, one_mul, hn]
  · show tw p χ _ * f₀ _ = _ * (tw p χ g * f₀ g)
    rw [tw_mul, ht, torusChar3_twist p lam χ a]
    ring

theorem untwist_mem (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    {f : LocalGL3 p → ℂ} (hf : f ∈ principalSeries3 p lam) :
    (fun g => (tw p χ g)⁻¹ * f g) ∈ principalSeries3 p (fun i => lam i * χ⁻¹) := by
  obtain ⟨hlc, hn, ht⟩ := mem_principalSeries3_iff.mp hf
  refine mem_principalSeries3_iff.mpr
    ⟨((isLocallyConstant_tw p χ hχ).comp (fun c : ℂ => c⁻¹)).comp₂ hlc (· * ·), fun x y z g => ?_, fun a g => ?_⟩
  · show (tw p χ _)⁻¹ * f _ = (tw p χ g)⁻¹ * f g
    rw [tw_mul, tw_upperUnipotent3, one_mul, hn]
  · show (tw p χ _)⁻¹ * f _ = _ * ((tw p χ g)⁻¹ * f g)
    rw [tw_mul, ht, torusChar3_twist p lam χ a]
    have h1 := tw_ne_zero p χ (diagonal3 p a)
    have h2 := tw_ne_zero p χ g
    field_simp

noncomputable def untwistLM (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ↥(principalSeries3 p lam) →ₗ[ℂ] ↥(principalSeries3 p (fun i => lam i * χ⁻¹)) where
  toFun f := ⟨fun g => (tw p χ g)⁻¹ * (f : LocalGL3 p → ℂ) g, untwist_mem p lam χ hχ f.2⟩
  map_add' f g := by
    apply Subtype.ext; funext k
    show (tw p χ k)⁻¹ * ((f : LocalGL3 p → ℂ) k + (g : LocalGL3 p → ℂ) k) = (tw p χ k)⁻¹ * (f : LocalGL3 p → ℂ) k + (tw p χ k)⁻¹ * (g : LocalGL3 p → ℂ) k
    ring
  map_smul' c f := by
    apply Subtype.ext; funext k
    show (tw p χ k)⁻¹ * (c * (f : LocalGL3 p → ℂ) k) = c * ((tw p χ k)⁻¹ * (f : LocalGL3 p → ℂ) k)
    ring

theorem untwistLM_apply (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (f : ↥(principalSeries3 p lam)) (g : LocalGL3 p) :
    ((untwistLM p lam χ hχ f : ↥(principalSeries3 p (fun i => lam i * χ⁻¹))) : LocalGL3 p → ℂ) g =
      (tw p χ g)⁻¹ * (f : LocalGL3 p → ℂ) g := rfl

theorem isWhittakerFunctional3_comp_untwist (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχ : IsLocallyConstant χ) (ψ : AddChar (p.adicCompletion ℚ) ℂ)
    (Λ' : ↥(principalSeries3 p (fun i => lam i * χ⁻¹)) →ₗ[ℂ] ℂ) (hΛ' : IsWhittakerFunctional3 ψ Λ') :
    IsWhittakerFunctional3 ψ (Λ'.comp (untwistLM p lam χ hχ)) := by
  intro x y z f
  show Λ' (untwistLM p lam χ hχ _) = ψ (x + y) * Λ' (untwistLM p lam χ hχ f)
  rw [← hΛ' x y z (untwistLM p lam χ hχ f)]
  congr 1
  apply Subtype.ext; funext k
  show (tw p χ k)⁻¹ * (f : LocalGL3 p → ℂ) (k * upperUnipotent3 x y z) =
    (tw p χ (k * upperUnipotent3 x y z))⁻¹ * (f : LocalGL3 p → ℂ) (k * upperUnipotent3 x y z)
  rw [tw_mul, tw_upperUnipotent3, mul_one]

theorem coefficientFn_twist (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ)
    (Λ' : ↥(principalSeries3 p (fun i => lam i * χ⁻¹)) →ₗ[ℂ] ℂ)
    (f₀ : ↥(principalSeries3 p (fun i => lam i * χ⁻¹))) (g : LocalGL3 p) :
    coefficientFn (Λ'.comp (untwistLM p lam χ hχ))
        ⟨fun k => tw p χ k * (f₀ : LocalGL3 p → ℂ) k, twist_mem p lam χ hχ f₀.2⟩ g =
      tw p χ g * coefficientFn Λ' f₀ g := by
  simp only [coefficientFn]
  show Λ' (untwistLM p lam χ hχ _) = tw p χ g * Λ' _
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  apply Subtype.ext; funext k
  show (tw p χ k)⁻¹ * (tw p χ (k * g) * (f₀ : LocalGL3 p → ℂ) (k * g)) = tw p χ g * (f₀ : LocalGL3 p → ℂ) (k * g)
  rw [tw_mul]
  have := tw_ne_zero p χ k
  field_simp

end Ws46.LV

namespace Ws46
namespace LV

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal Filter Topology MeasureTheory

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem gl3Entry_mul_upperUnipotent3 (g : LocalGL3 p) (x y z : p.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry p (g * upperUnipotent3 x y z) i 0 = gl3Entry p g i 0 ∧
    gl3Entry p (g * upperUnipotent3 x y z) i 1 = gl3Entry p g i 0 * x + gl3Entry p g i 1 ∧
    gl3Entry p (g * upperUnipotent3 x y z) i 2 = gl3Entry p g i 0 * z + gl3Entry p g i 1 * y + gl3Entry p g i 2 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

theorem cornerEntry_mul_upperUnipotent3 (g : LocalGL3 p) (x y z : p.adicCompletion ℚ) :
    cornerEntry p (g * upperUnipotent3 x y z) = cornerEntry p g :=
  (gl3Entry_mul_upperUnipotent3 p g x y z 2).1

theorem lowerMinor_mul_upperUnipotent3 (g : LocalGL3 p) (x y z : p.adicCompletion ℚ) :
    lowerMinor p (g * upperUnipotent3 x y z) = lowerMinor p g := by
  obtain ⟨h10, h11, -⟩ := gl3Entry_mul_upperUnipotent3 p g x y z 1
  obtain ⟨h20, h21, -⟩ := gl3Entry_mul_upperUnipotent3 p g x y z 2
  simp only [lowerMinor, h10, h11, h20, h21]; ring

theorem outerMinor_mul_upperUnipotent3 (g : LocalGL3 p) (x y z : p.adicCompletion ℚ) :
    outerMinor p (g * upperUnipotent3 x y z) = y * lowerMinor p g + outerMinor p g := by
  obtain ⟨h10, -, h12⟩ := gl3Entry_mul_upperUnipotent3 p g x y z 1
  obtain ⟨h20, -, h22⟩ := gl3Entry_mul_upperUnipotent3 p g x y z 2
  simp only [outerMinor, lowerMinor, h10, h12, h20, h22]; ring

theorem gl3Det_mul_upperUnipotent3 (g : LocalGL3 p) (x y z : p.adicCompletion ℚ) :
    gl3Det p (g * upperUnipotent3 x y z) = gl3Det p g := by
  have h1 : Matrix.det !![(1 : p.adicCompletion ℚ), x, z; 0, 1, y; 0, 0, 1] = 1 := by
    simp [Matrix.det_fin_three]
  rw [gl3Det, gl3Det, Units.val_mul, Matrix.det_mul, upperUnipotent3_coe, h1, mul_one]

theorem cellValue_mul_upperUnipotent3 (χ : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (g : LocalGL3 p) (x y z : p.adicCompletion ℚ) :
    cellValue p χ (g * upperUnipotent3 x y z) = cellValue p χ g := by
  simp only [cellValue, gl3Det_mul_upperUnipotent3, lowerMinor_mul_upperUnipotent3, cornerEntry_mul_upperUnipotent3]

theorem antidiagonal3_mul_upperUnipotent3_mem_bigCell3 (x y z : p.adicCompletion ℚ) :
    antidiagonal3 p * upperUnipotent3 x y z ∈ bigCell3 p := by
  rw [mem_bigCell3_iff, cornerEntry_mul_upperUnipotent3, lowerMinor_mul_upperUnipotent3, cornerEntry_antidiagonal3,
    lowerMinor_antidiagonal3]
  exact ⟨one_ne_zero, neg_ne_zero.2 one_ne_zero⟩

theorem cellRatio_antidiagonal3_mul_upperUnipotent3 (x y z : p.adicCompletion ℚ) :
    cellRatio p (antidiagonal3 p * upperUnipotent3 x y z) = ![x, z, y] := by
  obtain ⟨h20, h21, h22⟩ := gl3Entry_mul_upperUnipotent3 p (antidiagonal3 p) x y z 2
  have e20 : gl3Entry p (antidiagonal3 p) 2 0 = 1 := by simp [gl3Entry, antidiagonal3_coe]
  have e21 : gl3Entry p (antidiagonal3 p) 2 1 = 0 := by simp [gl3Entry, antidiagonal3_coe]
  have e22 : gl3Entry p (antidiagonal3 p) 2 2 = 0 := by simp [gl3Entry, antidiagonal3_coe]
  have hc : cornerEntry p (antidiagonal3 p * upperUnipotent3 x y z) = 1 := by
    rw [cornerEntry_mul_upperUnipotent3, cornerEntry_antidiagonal3]
  have v21 : gl3Entry p (antidiagonal3 p * upperUnipotent3 x y z) 2 1 = x := by rw [h21, e20, e21]; ring
  have v22 : gl3Entry p (antidiagonal3 p * upperUnipotent3 x y z) 2 2 = z := by rw [h22, e20, e21, e22]; ring
  have v3 : outerMinor p (antidiagonal3 p * upperUnipotent3 x y z) / lowerMinor p (antidiagonal3 p * upperUnipotent3 x y z) = y := by
    rw [outerMinor_mul_upperUnipotent3, lowerMinor_mul_upperUnipotent3, lowerMinor_antidiagonal3, outerMinor_antidiagonal3]
    field_simp; ring
  show ![_ / _, _ / _, _ / _] = ![x, z, y]
  rw [v3, hc, v21, v22, div_one, div_one]

theorem cellSectionOf_antidiagonal3_mul_upperUnipotent3 (χ : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (x y z : p.adicCompletion ℚ) :
    cellSectionOf p χ Φ (antidiagonal3 p * upperUnipotent3 x y z) = cellValue p χ (antidiagonal3 p) * Φ ![x, z, y] := by
  rw [cellSectionOf_apply_of_mem p χ Φ (antidiagonal3_mul_upperUnipotent3_mem_bigCell3 p x y z),
    cellValue_mul_upperUnipotent3, cellRatio_antidiagonal3_mul_upperUnipotent3]

theorem cellValue_antidiagonal3_ne_zero (χ : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) : cellValue p χ (antidiagonal3 p) ≠ 0 := by
  rw [cellValue_antidiagonal3]
  exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (Units.ne_zero _)

def sball (d : ℕ) : Set (p.adicCompletion ℚ) := {x | Valued.v x ≤ WithZero.exp (-(d : ℤ))}

theorem mem_sball {d : ℕ} {x : p.adicCompletion ℚ} : x ∈ sball p d ↔ Valued.v x ≤ WithZero.exp (-(d : ℤ)) := Iff.rfl

theorem zero_mem_sball (d : ℕ) : (0 : p.adicCompletion ℚ) ∈ sball p d := by
  rw [mem_sball, map_zero]; exact zero_le'

theorem sball_subset_integers (d : ℕ) : sball p d ⊆ (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) := by
  intro x hx
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  refine hx.trans ?_
  rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.2 (by omega)

theorem isClopen_sball (d : ℕ) : IsClopen (sball p d) := by
  let π : p.adicCompletion ℚ := ((NumberField.AdelicLevel.uniformizerUnit ℚ p)⁻¹ : (p.adicCompletion ℚ)ˣ) ^ d
  have hπ : Valued.v π = WithZero.exp (d : ℤ) := by
    rw [map_pow, Units.val_inv_eq_inv_val, map_inv₀, NumberField.AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_neg,
      neg_neg, ← WithZero.exp_nsmul]
    congr 1; simp
  have : sball p d = (fun x => x * π) ⁻¹' {y : p.adicCompletion ℚ | Valued.v y ≤ 1} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, mem_sball, map_mul, hπ]
    rw [WithZero.exp_neg, ← one_mul ((WithZero.exp (d : ℤ))⁻¹), le_mul_inv_iff₀ WithZero.exp_pos]
  rw [this]
  exact (isClopen_valued_le_one p).preimage (continuous_mul_const π)

theorem isCompact_sball (d : ℕ) : IsCompact (sball p d) :=
  (integersPositiveCompacts ℚ p).isCompact.of_isClosed_subset (isClopen_sball p d).isClosed
    (by rw [coe_integersPositiveCompacts]; exact sball_subset_integers p d)

noncomputable def cubeFun (d : ℕ) : (Fin 3 → p.adicCompletion ℚ) → ℂ :=
  Set.indicator {r | ∀ i, r i ∈ sball p d} 1

theorem cubeFun_apply (d : ℕ) (r : Fin 3 → p.adicCompletion ℚ) :
    cubeFun p d r = if ∀ i, r i ∈ sball p d then 1 else 0 := by
  simp only [cubeFun, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]

theorem cube_eq_pi (d : ℕ) : {r : Fin 3 → p.adicCompletion ℚ | ∀ i, r i ∈ sball p d} = Set.pi Set.univ (fun _ => sball p d) := by
  ext r; simp [Set.mem_pi]

theorem isClopen_cube (d : ℕ) : IsClopen {r : Fin 3 → p.adicCompletion ℚ | ∀ i, r i ∈ sball p d} := by
  have : {r : Fin 3 → p.adicCompletion ℚ | ∀ i, r i ∈ sball p d} = ⋂ i, (fun r => r i) ⁻¹' sball p d := by
    ext r; simp
  rw [this]
  exact isClopen_iInter_of_finite fun i => (isClopen_sball p d).preimage (continuous_apply i)

theorem cubeFun_isLocallyConstant (d : ℕ) : IsLocallyConstant (cubeFun p d) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro r
  by_cases hr : r ∈ {r : Fin 3 → p.adicCompletion ℚ | ∀ i, r i ∈ sball p d}
  · refine ⟨_, (isClopen_cube p d).isOpen, hr, fun r' hr' => ?_⟩
    rw [cubeFun, Set.indicator_of_mem hr', Set.indicator_of_mem hr]; rfl
  · refine ⟨_, (isClopen_cube p d).compl.isOpen, hr, fun r' hr' => ?_⟩
    rw [cubeFun, Set.indicator_of_notMem hr', Set.indicator_of_notMem hr]

theorem cubeFun_hasCompactSupport (d : ℕ) : HasCompactSupport (cubeFun p d) := by
  have hK : IsCompact {r : Fin 3 → p.adicCompletion ℚ | ∀ i, r i ∈ sball p d} := by
    rw [cube_eq_pi]; exact isCompact_univ_pi fun _ => isCompact_sball p d
  exact HasCompactSupport.intro' hK (isClopen_cube p d).isClosed fun r hr => by
    rw [cubeFun, Set.indicator_of_notMem hr]

end Ws46.LV

namespace Ws46
namespace LV

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal Filter Topology MeasureTheory

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem absNorm_rpow_ne_zero (r : ℝ) : ((Ideal.absNorm p.asIdeal : NNReal) ^ r) ≠ 0 := by
  have h : (0 : NNReal) < (Ideal.absNorm p.asIdeal : NNReal) := by
    exact_mod_cast lt_trans zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm p)
  exact (NNReal.rpow_pos h).ne'

theorem selfDualHaarAt_sball_ne_zero (d : ℕ) : selfDualHaarAt ℚ p (sball p d) ≠ 0 := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  simp only [selfDualHaarAt, Measure.smul_apply, ne_eq, smul_eq_zero, not_or]
  exact ⟨absNorm_rpow_ne_zero p _, ((isClopen_sball p d).isOpen.measure_pos _ ⟨0, zero_mem_sball p d⟩).ne'⟩

theorem selfDualHaarAt_sball_ne_top (d : ℕ) : selfDualHaarAt ℚ p (sball p d) ≠ ⊤ := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  refine ne_top_of_le_ne_top ?_ (measure_mono (sball_subset_integers p d))
  simp only [selfDualHaarAt, Measure.smul_apply]
  rw [← coe_integersPositiveCompacts, Measure.addHaarMeasure_self]
  simp [ENNReal.smul_def]

theorem selfDualHaarAt_sball_toReal_pos (d : ℕ) : 0 < (selfDualHaarAt ℚ p (sball p d)).toReal :=
  ENNReal.toReal_pos (selfDualHaarAt_sball_ne_zero p d) (selfDualHaarAt_sball_ne_top p d)

theorem measurableSet_sball (d : ℕ) : @MeasurableSet _ (localBorel ℚ p) (sball p d) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  exact (isClopen_sball p d).isClosed.measurableSet

scoped instance sFinite_selfDualHaarAt : @SFinite _ (localBorel ℚ p) (selfDualHaarAt ℚ p) := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  unfold selfDualHaarAt
  infer_instance

theorem jacquetTruncated3_cellSectionOf_cubeFun (χ : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (d : ℕ) (c : ℤ) (hc : 0 ≤ c) :
    jacquetTruncated3 p c (cellSectionOf p χ (cubeFun p d)) =
      cellValue p χ (antidiagonal3 p) * ((selfDualHaarAt ℚ p (sball p d)).toReal) ^ 3 := by
  letI := localBorel ℚ p
  haveI : BorelSpace (p.adicCompletion ℚ) := borelSpace_localBorel ℚ p
  set T : Set (p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ) := sball p d ×ˢ (sball p d ×ˢ sball p d) with hT
  have hTm : MeasurableSet T := (measurableSet_sball p d).prod ((measurableSet_sball p d).prod (measurableSet_sball p d))
  have hint : (fun q : p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ =>
      NumberField.StandardAddChar.psiLocal ℚ p (-(q.1 + q.2.1)) * cellSectionOf p χ (cubeFun p d) (antidiagonal3 p * upperUnipotent3 q.1 q.2.1 q.2.2)) =
      fun q => cellValue p χ (antidiagonal3 p) * T.indicator 1 q := by
    funext q
    rw [cellSectionOf_antidiagonal3_mul_upperUnipotent3, cubeFun_apply]
    by_cases hq : q ∈ T
    · obtain ⟨h1, h23⟩ := Set.mem_prod.1 hq
      obtain ⟨h2, h3⟩ := Set.mem_prod.1 h23
      have hall : ∀ i, ![q.1, q.2.2, q.2.1] i ∈ sball p d := by
        intro i; fin_cases i
        · exact h1
        · exact h3
        · exact h2
      have hmem : -(q.1 + q.2.1) ∈ p.adicCompletionIntegers ℚ :=
        neg_mem (add_mem (sball_subset_integers p d h1) (sball_subset_integers p d h2))
      rw [if_pos hall, Set.indicator_of_mem hq, Pi.one_apply, psiLocal_eq_one_of_mem_integers ℚ p _ hmem]; ring
    · have hnall : ¬ ∀ i, ![q.1, q.2.2, q.2.1] i ∈ sball p d := by
        intro h; apply hq
        exact Set.mem_prod.2 ⟨by simpa using h 0, Set.mem_prod.2 ⟨by simpa using h 2, by simpa using h 1⟩⟩
      rw [if_neg hnall, Set.indicator_of_notMem hq]; ring
  have hsub : T ⊆ unipotentBall3 p c := by
    rintro q hq
    obtain ⟨h1, h23⟩ := Set.mem_prod.1 hq
    obtain ⟨h2, h3⟩ := Set.mem_prod.1 h23
    have hle : WithZero.exp (-(d : ℤ)) ≤ WithZero.exp c := WithZero.exp_le_exp.2 (by omega)
    have hle2 : WithZero.exp (-(d : ℤ)) ≤ WithZero.exp (2 * c) := WithZero.exp_le_exp.2 (by omega)
    exact ⟨h1.trans hle, h2.trans hle, h3.trans hle2⟩
  show (∫ q in unipotentBall3 p c, NumberField.StandardAddChar.psiLocal ℚ p (-(q.1 + q.2.1)) *
      cellSectionOf p χ (cubeFun p d) (antidiagonal3 p * upperUnipotent3 q.1 q.2.1 q.2.2) ∂(jacquetHaar3 p)) = _
  rw [hint, integral_const_mul, show T.indicator (1 : (p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ) → ℂ) = T.indicator (fun _ => (1 : ℂ)) from rfl,
    integral_indicator_const (1 : ℂ) hTm, Measure.real, Measure.restrict_apply hTm, Set.inter_eq_left.2 hsub,
    Complex.real_smul, mul_one]
  congr 1
  rw [show jacquetHaar3 p = (selfDualHaarAt ℚ p).prod ((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p)) from rfl,
    hT, Measure.prod_prod, Measure.prod_prod, ENNReal.toReal_mul, ENNReal.toReal_mul]
  push_cast; ring

theorem jacquetValue_cellSectionOf_cubeFun_ne_zero (χ : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (d : ℕ) :
    jacquetValue p (cellSectionOf p χ (cubeFun p d)) ≠ 0 := by
  set u := cellSectionOf p χ (cubeFun p d) with hu
  have hconst : ∀ c : ℤ, ((0 : ℕ) : ℤ) ≤ c → jacquetTruncated3 p c u = jacquetTruncated3 p (0 : ℕ) u := by
    intro c hc
    rw [jacquetTruncated3_cellSectionOf_cubeFun p χ d c (by exact_mod_cast hc), Nat.cast_zero,
      jacquetTruncated3_cellSectionOf_cubeFun p χ d 0 le_rfl]
  have hlev : jacquetLevel p u = 0 := Nat.le_zero.1 (jacquetLevel_le p u hconst)
  rw [jacquetValue, hlev, Nat.cast_zero, jacquetTruncated3_cellSectionOf_cubeFun p χ d 0 le_rfl]
  refine mul_ne_zero (cellValue_antidiagonal3_ne_zero p χ) (pow_ne_zero _ ?_)
  exact_mod_cast (selfDualHaarAt_sball_toReal_pos p d).ne'

end Ws46.LV
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46.LV"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46"

namespace Ws46
namespace LV

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal Filter Topology MeasureTheory

variable (p : HeightOneSpectrum (𝓞 ℚ))

section Kit
variable {e : WithZero (Multiplicative ℤ)}

theorem v_add_le {x y : p.adicCompletion ℚ} (hx : Valued.v x ≤ e) (hy : Valued.v y ≤ e) : Valued.v (x + y) ≤ e :=
  (Valuation.map_add _ _ _).trans (max_le hx hy)

theorem v_sub_le {x y : p.adicCompletion ℚ} (hx : Valued.v x ≤ e) (hy : Valued.v y ≤ e) : Valued.v (x - y) ≤ e :=
  (Valuation.map_sub _ _ _).trans (max_le hx hy)

theorem v_mul_le {x y : p.adicCompletion ℚ} (hx : Valued.v x ≤ e) (hy : Valued.v y ≤ 1) : Valued.v (x * y) ≤ e := by
  rw [map_mul]; calc Valued.v x * Valued.v y ≤ e * 1 := mul_le_mul' hx hy
    _ = e := mul_one e

theorem v_mul_le' {x y : p.adicCompletion ℚ} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ e) : Valued.v (x * y) ≤ e := by
  rw [mul_comm]; exact v_mul_le p hy hx

theorem v_eq_one_of_near (he : e < 1) {x : p.adicCompletion ℚ} (hx : Valued.v (x - 1) ≤ e) : Valued.v x = 1 := by
  have := Valuation.map_one_add_of_lt Valued.v (lt_of_le_of_lt hx he)
  rwa [add_sub_cancel] at this

theorem ne_zero_of_near (he : e < 1) {x : p.adicCompletion ℚ} (hx : Valued.v (x - 1) ≤ e) : x ≠ 0 := by
  intro h; have := v_eq_one_of_near p he hx; rw [h, map_zero] at this; exact zero_ne_one this

theorem near_mul (he : e < 1) {x y : p.adicCompletion ℚ} (hx : Valued.v (x - 1) ≤ e) (hy : Valued.v (y - 1) ≤ e) :
    Valued.v (x * y - 1) ≤ e := by
  rw [show x * y - 1 = (x - 1) * y + (y - 1) by ring]
  exact v_add_le p (v_mul_le p hx (v_eq_one_of_near p he hy).le) hy

theorem near_inv (he : e < 1) {x : p.adicCompletion ℚ} (hx : Valued.v (x - 1) ≤ e) : Valued.v (x⁻¹ - 1) ≤ e := by
  have hx0 := ne_zero_of_near p he hx
  rw [show x⁻¹ - 1 = -(x⁻¹ * (x - 1)) by field_simp; ring, Valuation.map_neg, map_mul, map_inv₀, v_eq_one_of_near p he hx,
    inv_one, one_mul]
  exact hx

theorem near_div (he : e < 1) {x y : p.adicCompletion ℚ} (hx : Valued.v (x - 1) ≤ e) (hy : Valued.v (y - 1) ≤ e) :
    Valued.v (x / y - 1) ≤ e := by
  rw [div_eq_mul_inv]; exact near_mul p he hx (near_inv p he hy)

theorem v_div_le_of_near (he : e < 1) {x y : p.adicCompletion ℚ} (hx : Valued.v x ≤ e) (hy : Valued.v (y - 1) ≤ e) :
    Valued.v (x / y) ≤ e := by
  rw [map_div₀, v_eq_one_of_near p he hy, div_one]; exact hx

theorem norm_eq_one_of_near (he : e < 1) {x : p.adicCompletion ℚ} (hx : Valued.v (x - 1) ≤ e) : ‖x‖ = 1 := by
  have h1 := v_eq_one_of_near p he hx
  have hle : ‖x‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).2 h1.le
  have hge : ¬ ‖x‖ < 1 := fun h => by
    have := (Valued.toNormedField.norm_lt_one_iff).1 h; rw [h1] at this; exact lt_irrefl _ this
  exact le_antisymm hle (not_lt.1 hge)

end Kit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46.LV"

theorem mk0_mem_higherUnitsAt {d : ℕ} (hd : 0 < d) {x : p.adicCompletion ℚ}
    (hx : Valued.v (x - 1) ≤ WithZero.exp (-(d : ℤ))) (hx0 : x ≠ 0) :
    Units.mk0 x hx0 ∈ higherUnitsAt ℚ p d := by
  have he : WithZero.exp (-(d : ℤ)) < 1 := by rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)
  exact ⟨by rw [Units.val_mk0]; exact v_eq_one_of_near p he hx, Or.inr (by rw [Units.val_mk0]; exact hx)⟩

theorem charExt_mul_near {d : ℕ} (hd : 0 < d) (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : ∀ u ∈ higherUnitsAt ℚ p d, χ u = 1)
    (x : p.adicCompletion ℚ) {w : p.adicCompletion ℚ} (hw : Valued.v (w - 1) ≤ WithZero.exp (-(d : ℤ))) :
    charExt χ (x * w) = charExt χ x := by
  have he : WithZero.exp (-(d : ℤ)) < 1 := by rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)
  have hw0 := ne_zero_of_near p he hw
  rw [mul_comm, show w = ((Units.mk0 w hw0 : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) from (Units.val_mk0 hw0).symm, charExt_units_mul,
    hχ _ (mk0_mem_higherUnitsAt p hd hw hw0), Units.val_one, one_mul]

noncomputable def innerMinor (g : LocalGL3 p) : p.adicCompletion ℚ := gl3Entry p g 1 1 * gl3Entry p g 2 2 - gl3Entry p g 1 2 * gl3Entry p g 2 1

theorem plucker (g : LocalGL3 p) :
    cornerEntry p g * innerMinor p g - gl3Entry p g 2 1 * outerMinor p g + gl3Entry p g 2 2 * lowerMinor p g = 0 := by
  simp only [cornerEntry, innerMinor, outerMinor, lowerMinor]; ring

theorem bottom_mul (g k : LocalGL3 p) (j : Fin 3) :
    gl3Entry p (g * k) 2 j = gl3Entry p g 2 0 * gl3Entry p k 0 j + gl3Entry p g 2 1 * gl3Entry p k 1 j +
      gl3Entry p g 2 2 * gl3Entry p k 2 j := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

noncomputable def kMinor (k : LocalGL3 p) (l l' a b : Fin 3) : p.adicCompletion ℚ :=
  gl3Entry p k l a * gl3Entry p k l' b - gl3Entry p k l' a * gl3Entry p k l b

theorem lowerMinor_mul (g k : LocalGL3 p) :
    lowerMinor p (g * k) = lowerMinor p g * kMinor p k 0 1 0 1 + outerMinor p g * kMinor p k 0 2 0 1 +
      innerMinor p g * kMinor p k 1 2 0 1 := by
  simp only [lowerMinor, outerMinor, innerMinor, kMinor, gl3Entry, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem outerMinor_mul (g k : LocalGL3 p) :
    outerMinor p (g * k) = lowerMinor p g * kMinor p k 0 1 0 2 + outerMinor p g * kMinor p k 0 2 0 2 +
      innerMinor p g * kMinor p k 1 2 0 2 := by
  simp only [lowerMinor, outerMinor, innerMinor, kMinor, gl3Entry, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem gl3Det_mul (g k : LocalGL3 p) : gl3Det p (g * k) = gl3Det p g * gl3Det p k := by
  simp only [gl3Det, Units.val_mul, Matrix.det_mul]

theorem gl3Det_eq (k : LocalGL3 p) : gl3Det p k =
    gl3Entry p k 0 0 * kMinor p k 1 2 1 2 - gl3Entry p k 0 1 * kMinor p k 1 2 0 2 + gl3Entry p k 0 2 * kMinor p k 1 2 0 1 := by
  simp only [gl3Det, Matrix.det_fin_three, kMinor, gl3Entry]; ring

end Ws46.LV
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46.LV"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46.LV"

namespace Ws46
namespace LV

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal Filter Topology MeasureTheory

variable (p : HeightOneSpectrum (𝓞 ℚ))

section Near
variable {d : ℕ}

theorem k_diag (k : LocalGL3 p)
    (hk : ∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) (i : Fin 3) : Valued.v (gl3Entry p k i i - 1) ≤ WithZero.exp (-(d : ℤ)) := by
  have := hk i i; rwa [Matrix.one_apply_eq] at this

theorem k_off (k : LocalGL3 p)
    (hk : ∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) {i j : Fin 3} (h : i ≠ j) : Valued.v (gl3Entry p k i j) ≤ WithZero.exp (-(d : ℤ)) := by
  have := hk i j; rwa [Matrix.one_apply_ne h, sub_zero] at this

theorem k_le_one (k : LocalGL3 p)
    (hk : ∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) (i j : Fin 3) : Valued.v (gl3Entry p k i j) ≤ 1 := by
  have h := hk i j
  have h1 : Valued.v ((1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1 := by
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne hij, map_zero]; exact zero_le'
  have he : WithZero.exp (-(d : ℤ)) ≤ 1 := by rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.2 (by omega)
  have := v_add_le p (h.trans he) h1
  rwa [sub_add_cancel] at this

end Near
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46.LV"

set_option maxHeartbeats 6400000 in

theorem small_mul (χ : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) {d : ℕ} (hd : 0 < d)
    (hχ : ∀ i : Fin 3, ∀ u ∈ higherUnitsAt ℚ p d, χ i u = 1)
    (k : LocalGL3 p)
    (hk : ∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ)))
    (g : LocalGL3 p) (hg : g ∈ bigCell3 p) (hr : ∀ i, cellRatio p g i ∈ sball p d) :
    (g * k ∈ bigCell3 p ∧ ∀ i, cellRatio p (g * k) i ∈ sball p d) ∧ cellValue p χ (g * k) = cellValue p χ g := by
  have he : WithZero.exp (-(d : ℤ)) < 1 := by rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)

  obtain ⟨hc, hm⟩ := (mem_bigCell3_iff p g).1 hg
  set c := cornerEntry p g with hcdef
  set m := lowerMinor p g with hmdef
  set o := outerMinor p g with hodef
  set n := innerMinor p g with hndef
  set b₁ := gl3Entry p g 2 1 with hb₁
  set b₂ := gl3Entry p g 2 2 with hb₂
  have hc' : gl3Entry p g 2 0 = c := rfl
  have hr₁ : Valued.v (b₁ / c) ≤ WithZero.exp (-(d : ℤ)) := hr 0
  have hr₂ : Valued.v (b₂ / c) ≤ WithZero.exp (-(d : ℤ)) := hr 1
  have hr₃ : Valued.v (o / m) ≤ WithZero.exp (-(d : ℤ)) := hr 2
  have hnm : Valued.v (n / m) ≤ WithZero.exp (-(d : ℤ)) := by
    have hpl := plucker p g
    have : n / m = b₁ / c * (o / m) - b₂ / c := by
      field_simp
      simp only [← hcdef, ← hndef, ← hodef, ← hmdef, ← hb₁, ← hb₂] at hpl ⊢
      linear_combination hpl
    rw [this]
    exact v_sub_le p (v_mul_le p hr₁ (hr₃.trans he.le)) hr₂

  have kd := k_diag p k hk
  have ko := fun {i j : Fin 3} (h : i ≠ j) => k_off p k hk h
  have k1 := k_le_one p k hk

  set u₀ := gl3Entry p k 0 0 + b₁ / c * gl3Entry p k 1 0 + b₂ / c * gl3Entry p k 2 0 with hu₀
  set w₁ := gl3Entry p k 0 1 + b₁ / c * gl3Entry p k 1 1 + b₂ / c * gl3Entry p k 2 1 with hw₁
  set w₂ := gl3Entry p k 0 2 + b₁ / c * gl3Entry p k 1 2 + b₂ / c * gl3Entry p k 2 2 with hw₂
  have hu₀n : Valued.v (u₀ - 1) ≤ WithZero.exp (-(d : ℤ)) := by
    rw [show u₀ - 1 = (gl3Entry p k 0 0 - 1) + (b₁ / c * gl3Entry p k 1 0 + b₂ / c * gl3Entry p k 2 0) by rw [hu₀]; ring]
    exact v_add_le p (kd 0) (v_add_le p (v_mul_le p hr₁ (k1 1 0)) (v_mul_le p hr₂ (k1 2 0)))
  have hw₁s : Valued.v w₁ ≤ WithZero.exp (-(d : ℤ)) :=
    v_add_le p (v_add_le p (ko (by decide)) (v_mul_le p hr₁ (k1 1 1))) (v_mul_le p hr₂ (k1 2 1))
  have hw₂s : Valued.v w₂ ≤ WithZero.exp (-(d : ℤ)) :=
    v_add_le p (v_add_le p (ko (by decide)) (v_mul_le p hr₁ (k1 1 2))) (v_mul_le p hr₂ (k1 2 2))
  have hcorner' : cornerEntry p (g * k) = c * u₀ := by
    show gl3Entry p (g * k) 2 0 = c * u₀
    rw [bottom_mul, hu₀, hc', ← hb₁, ← hb₂]; field_simp
  have hb₁' : gl3Entry p (g * k) 2 1 = c * w₁ := by rw [bottom_mul, hw₁, hc', ← hb₁, ← hb₂]; field_simp
  have hb₂' : gl3Entry p (g * k) 2 2 = c * w₂ := by rw [bottom_mul, hw₂, hc', ← hb₁, ← hb₂]; field_simp

  have hK0101 : Valued.v (kMinor p k 0 1 0 1 - 1) ≤ WithZero.exp (-(d : ℤ)) := by
    rw [show kMinor p k 0 1 0 1 - 1 = (gl3Entry p k 0 0 * gl3Entry p k 1 1 - 1) - gl3Entry p k 1 0 * gl3Entry p k 0 1 by
      simp only [kMinor]; ring]
    exact v_sub_le p (near_mul p he (kd 0) (kd 1)) (v_mul_le p (ko (by decide)) (k1 0 1))
  have hK0202 : Valued.v (kMinor p k 0 2 0 2 - 1) ≤ WithZero.exp (-(d : ℤ)) := by
    rw [show kMinor p k 0 2 0 2 - 1 = (gl3Entry p k 0 0 * gl3Entry p k 2 2 - 1) - gl3Entry p k 2 0 * gl3Entry p k 0 2 by
      simp only [kMinor]; ring]
    exact v_sub_le p (near_mul p he (kd 0) (kd 2)) (v_mul_le p (ko (by decide)) (k1 0 2))
  have hK1212 : Valued.v (kMinor p k 1 2 1 2 - 1) ≤ WithZero.exp (-(d : ℤ)) := by
    rw [show kMinor p k 1 2 1 2 - 1 = (gl3Entry p k 1 1 * gl3Entry p k 2 2 - 1) - gl3Entry p k 2 1 * gl3Entry p k 1 2 by
      simp only [kMinor]; ring]
    exact v_sub_le p (near_mul p he (kd 1) (kd 2)) (v_mul_le p (ko (by decide)) (k1 1 2))
  have hKs : ∀ {l l' a b : Fin 3}, l ≠ a ∨ l' ≠ b → l' ≠ a ∨ l ≠ b →
      (l ≠ a → Valued.v (gl3Entry p k l a) ≤ WithZero.exp (-(d : ℤ))) →
      (l' ≠ b → Valued.v (gl3Entry p k l' b) ≤ WithZero.exp (-(d : ℤ))) →
      (l' ≠ a → Valued.v (gl3Entry p k l' a) ≤ WithZero.exp (-(d : ℤ))) →
      (l ≠ b → Valued.v (gl3Entry p k l b) ≤ WithZero.exp (-(d : ℤ))) →
      Valued.v (kMinor p k l l' a b) ≤ WithZero.exp (-(d : ℤ)) := by
    intro l l' a b h1 h2 f1 f2 f3 f4
    simp only [kMinor]
    refine v_sub_le p ?_ ?_
    · rcases h1 with h | h
      · exact v_mul_le p (f1 h) (k1 _ _)
      · exact v_mul_le' p (k1 _ _) (f2 h)
    · rcases h2 with h | h
      · exact v_mul_le p (f3 h) (k1 _ _)
      · exact v_mul_le' p (k1 _ _) (f4 h)
  have hK0201 : Valued.v (kMinor p k 0 2 0 1) ≤ WithZero.exp (-(d : ℤ)) :=
    hKs (Or.inr (by decide)) (Or.inl (by decide)) (fun h => absurd rfl h) (fun h => ko h) (fun h => ko h) (fun h => ko h)
  have hK1201 : Valued.v (kMinor p k 1 2 0 1) ≤ WithZero.exp (-(d : ℤ)) :=
    hKs (Or.inl (by decide)) (Or.inl (by decide)) (fun h => ko h) (fun h => ko h) (fun h => ko h) (fun h => ko h)
  have hK0102 : Valued.v (kMinor p k 0 1 0 2) ≤ WithZero.exp (-(d : ℤ)) :=
    hKs (Or.inr (by decide)) (Or.inl (by decide)) (fun h => absurd rfl h) (fun h => ko h) (fun h => ko h) (fun h => ko h)
  have hK1202 : Valued.v (kMinor p k 1 2 0 2) ≤ WithZero.exp (-(d : ℤ)) :=
    hKs (Or.inl (by decide)) (Or.inl (by decide)) (fun h => ko h) (fun h => ko h) (fun h => ko h) (fun h => ko h)
  set u₁ := kMinor p k 0 1 0 1 + o / m * kMinor p k 0 2 0 1 + n / m * kMinor p k 1 2 0 1 with hu₁
  set w₃ := kMinor p k 0 1 0 2 + o / m * kMinor p k 0 2 0 2 + n / m * kMinor p k 1 2 0 2 with hw₃
  have hu₁n : Valued.v (u₁ - 1) ≤ WithZero.exp (-(d : ℤ)) := by
    rw [show u₁ - 1 = (kMinor p k 0 1 0 1 - 1) + (o / m * kMinor p k 0 2 0 1 + n / m * kMinor p k 1 2 0 1) by rw [hu₁]; ring]
    exact v_add_le p hK0101 (v_add_le p (v_mul_le p hr₃ (hK0201.trans he.le)) (v_mul_le p hnm (hK1201.trans he.le)))
  have hw₃s : Valued.v w₃ ≤ WithZero.exp (-(d : ℤ)) :=
    v_add_le p (v_add_le p hK0102 (v_mul_le p hr₃ ((v_eq_one_of_near p he hK0202).le)))
      (v_mul_le p hnm (hK1202.trans he.le))
  have hm' : lowerMinor p (g * k) = m * u₁ := by rw [lowerMinor_mul, hu₁, ← hmdef, ← hodef, ← hndef]; field_simp
  have ho' : outerMinor p (g * k) = m * w₃ := by rw [outerMinor_mul, hw₃, ← hmdef, ← hodef, ← hndef]; field_simp

  have hdetk : Valued.v (gl3Det p k - 1) ≤ WithZero.exp (-(d : ℤ)) := by
    rw [gl3Det_eq, show gl3Entry p k 0 0 * kMinor p k 1 2 1 2 - gl3Entry p k 0 1 * kMinor p k 1 2 0 2 +
        gl3Entry p k 0 2 * kMinor p k 1 2 0 1 - 1 = (gl3Entry p k 0 0 * kMinor p k 1 2 1 2 - 1) -
        gl3Entry p k 0 1 * kMinor p k 1 2 0 2 + gl3Entry p k 0 2 * kMinor p k 1 2 0 1 by ring]
    exact v_add_le p (v_sub_le p (near_mul p he (kd 0) hK1212) (v_mul_le p (ko (by decide)) (hK1202.trans he.le)))
      (v_mul_le p (ko (by decide)) (hK1201.trans he.le))

  have hu₀0 := ne_zero_of_near p he hu₀n
  have hu₁0 := ne_zero_of_near p he hu₁n
  refine ⟨⟨(mem_bigCell3_iff p _).2 ⟨by rw [hcorner']; exact mul_ne_zero hc hu₀0, by rw [hm']; exact mul_ne_zero hm hu₁0⟩,
    fun i => ?_⟩, ?_⟩
  · fin_cases i
    · show Valued.v (gl3Entry p (g * k) 2 1 / cornerEntry p (g * k)) ≤ _
      rw [hb₁', hcorner', mul_div_mul_left _ _ hc]; exact v_div_le_of_near p he hw₁s hu₀n
    · show Valued.v (gl3Entry p (g * k) 2 2 / cornerEntry p (g * k)) ≤ _
      rw [hb₂', hcorner', mul_div_mul_left _ _ hc]; exact v_div_le_of_near p he hw₂s hu₀n
    · show Valued.v (outerMinor p (g * k) / lowerMinor p (g * k)) ≤ _
      rw [ho', hm', mul_div_mul_left _ _ hm]; exact v_div_le_of_near p he hw₃s hu₁n
  · have h1 : gl3Det p (g * k) / lowerMinor p (g * k) = gl3Det p g / m * (gl3Det p k / u₁) := by
      rw [gl3Det_mul, hm']; field_simp
    have h2 : lowerMinor p (g * k) / cornerEntry p (g * k) = m / c * (u₁ / u₀) := by
      rw [hm', hcorner']; field_simp
    rw [cellValue, cellValue, h1, h2, hcorner', charExt_mul_near p hd (χ 0) (hχ 0) _ (near_div p he hdetk hu₁n),
      charExt_mul_near p hd (χ 1) (hχ 1) _ (near_div p he hu₁n hu₀n), charExt_mul_near p hd (χ 2) (hχ 2) _ hu₀n,
      norm_mul, norm_mul, norm_eq_one_of_near p he (near_div p he hdetk hu₁n), norm_eq_one_of_near p he hu₀n,
      mul_one, mul_one]

end Ws46.LV
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46.LV"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46.LV"

namespace Ws46
namespace LV

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal Filter Topology MeasureTheory

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem inv_near {d : ℕ} (k : LocalGL3 p) (hkK : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (hk : ∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) :
    ∀ i j : Fin 3, Valued.v (((k⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ)) := by
  intro i j
  have hmat : ((k⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) - 1 =
      ((k⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) * (1 - (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) := by
    rw [mul_sub, mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have := congrFun (congrFun hmat i) j
  rw [Matrix.sub_apply] at this
  rw [this, Matrix.mul_apply, Fin.sum_univ_three]
  have hb : ∀ m : Fin 3, Valued.v (((k⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i m *
      ((1 - (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) m j)) ≤ WithZero.exp (-(d : ℤ)) := by
    intro m
    refine v_mul_le' p (hkK.2 i m) ?_
    rw [Matrix.sub_apply, ← Valuation.map_neg, neg_sub]; exact hk m j
  exact v_add_le p (v_add_le p (hb 0) (hb 1)) (hb 2)

theorem cellSectionOf_cubeFun_eq (χ : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (d : ℕ) (g : LocalGL3 p) :
    cellSectionOf p χ (cubeFun p d) g =
      if g ∈ bigCell3 p ∧ ∀ i, cellRatio p g i ∈ sball p d then cellValue p χ g else 0 := by
  by_cases hg : g ∈ bigCell3 p
  · rw [cellSectionOf_apply_of_mem p χ _ hg, cubeFun_apply]
    by_cases hr : ∀ i, cellRatio p g i ∈ sball p d
    · rw [if_pos hr, if_pos ⟨hg, hr⟩, mul_one]
    · rw [if_neg hr, if_neg (fun h => hr h.2), mul_zero]
  · rw [cellSectionOf_apply_of_notMem p χ _ hg, if_neg (fun h => hg h.1)]

theorem cellSectionOf_cubeFun_mul (χ : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) {d : ℕ} (hd : 0 < d)
    (hχ : ∀ i : Fin 3, ∀ u ∈ higherUnitsAt ℚ p d, χ i u = 1)
    (k : LocalGL3 p) (hkK : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (hk : ∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ)))
    (g : LocalGL3 p) :
    cellSectionOf p χ (cubeFun p d) (g * k) = cellSectionOf p χ (cubeFun p d) g := by
  rw [cellSectionOf_cubeFun_eq, cellSectionOf_cubeFun_eq]
  by_cases hP : g ∈ bigCell3 p ∧ ∀ i, cellRatio p g i ∈ sball p d
  · obtain ⟨hP', hval⟩ := small_mul p χ hd hχ k hk g hP.1 hP.2
    rw [if_pos hP', if_pos hP, hval]
  · have hP' : ¬ (g * k ∈ bigCell3 p ∧ ∀ i, cellRatio p (g * k) i ∈ sball p d) := by
      intro h
      have := (small_mul p χ hd hχ k⁻¹ (inv_near p k hkK hk) (g * k) h.1 h.2).1
      rw [mul_inv_cancel_right] at this
      exact hP this
    rw [if_neg hP', if_neg hP]

set_option maxHeartbeats 6400000 in
theorem main
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i : Fin 3, IsLocallyConstant (lam i))
    (hu : ∀ (i : Fin 3) (x : (p.adicCompletion ℚ)ˣ), ‖((lam i x : ℂˣ) : ℂ)‖ = 1)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (hχu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1)
    (d : ℕ) (hd : 0 < d)
    (hlev : ∀ i : Fin 3, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p d, (lam i * χ⁻¹) u = 1) :
    ∃ (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 p lam)),
      IsWhittakerFunctional3 (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ Λ ∧
      coefficientFn Λ f ≠ 0 ∧
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
        (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
            (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
        ∀ g : LocalGL3 p,
          ((χ (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ)⁻¹ * coefficientFn Λ f (g * k) =
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * coefficientFn Λ f g := by
  classical
  set lam' : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ) := fun i => lam i * χ⁻¹ with hlam'
  have hlam'lc : ∀ i, IsLocallyConstant (lam' i) := by
    intro i
    have : (⇑(lam' i) : (p.adicCompletion ℚ)ˣ → ℂˣ) = fun x => lam i x * (χ x)⁻¹ := by
      funext x; simp only [hlam', MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [this]
    exact (hlam i).comp₂ (hχ.comp fun u : ℂˣ => u⁻¹) (· * ·)
  obtain ⟨Λ₀, Λ₁, -, -, -, -, hΛ₁, hΛ₁val, hΛ₁cell⟩ :=
    LanglandsTunnell.CubicInduction.exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum p lam' hlam'lc
  obtain ⟨hmem, hcoef⟩ := hΛ₁cell (cubeFun p d) ⟨cubeFun_isLocallyConstant p d, cubeFun_hasCompactSupport p d⟩
  set f₀ : ↥(principalSeries3 p lam') := ⟨cellSectionOf p lam' (cubeFun p d), hmem⟩ with hf₀
  let Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ := Λ₁.comp (untwistLM p lam χ hχ)
  let f : ↥(principalSeries3 p lam) := ⟨fun g => tw p χ g * (f₀ : LocalGL3 p → ℂ) g, twist_mem p lam χ hχ f₀.2⟩
  have hcoefg : ∀ g, coefficientFn Λ f g = tw p χ g * coefficientFn Λ₁ f₀ g := fun g =>
    coefficientFn_twist p lam χ hχ Λ₁ f₀ g
  have hcoef₀ : ∀ g, coefficientFn Λ₁ f₀ g = jacquetWhittaker3 p lam' (cubeFun p d) (diagonal3 p ![1, -1, 1] * g) :=
    fun g => (congrFun hcoef g).symm
  refine ⟨Λ, f, isWhittakerFunctional3_comp_untwist p lam χ hχ _ Λ₁ hΛ₁, ?_, ?_⟩
  ·
    intro h0
    have h1 := congrFun h0 (diagonal3 p ![1, -1, 1])⁻¹
    rw [Pi.zero_apply, hcoefg, hcoef₀, mul_inv_cancel, jacquetWhittaker3_apply] at h1
    have h2 : gl3AmbientRightTranslate (R := ℂ) (1 : LocalGL3 p) (cellSectionOf p lam' (cubeFun p d)) =
        cellSectionOf p lam' (cubeFun p d) := by
      funext x; simp [gl3AmbientRightTranslate]
    rw [h2] at h1
    exact (mul_ne_zero (tw_ne_zero p χ _) (jacquetValue_cellSectionOf_cubeFun_ne_zero p lam' d)) h1
  ·
    intro k hkK hk g
    have hinv : ∀ h : LocalGL3 p, coefficientFn Λ₁ f₀ (h * k) = coefficientFn Λ₁ f₀ h := by
      intro h
      simp only [coefficientFn]
      congr 1
      apply Subtype.ext
      funext x
      show cellSectionOf p lam' (cubeFun p d) (x * (h * k)) = cellSectionOf p lam' (cubeFun p d) (x * h)
      rw [← mul_assoc]
      exact cellSectionOf_cubeFun_mul p lam' hd hlev k hkK hk (x * h)
    show (tw p χ (g * k))⁻¹ * coefficientFn Λ f (g * k) = (tw p χ g)⁻¹ * coefficientFn Λ f g
    rw [hcoefg, hcoefg, hinv, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (tw_ne_zero p χ _),
      inv_mul_cancel₀ (tw_ne_zero p χ _)]

end Ws46.LV
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46.LV"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46 P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos.Ws46.LV"

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i : Fin 3, IsLocallyConstant (lam i))
    (hu : ∀ (i : Fin 3) (x : (p.adicCompletion ℚ)ˣ), ‖((lam i x : ℂˣ) : ℂ)‖ = 1)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) (hχu : ∀ x : (p.adicCompletion ℚ)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1)
    (d : ℕ) (hd : 0 < d)
    (hlev : ∀ i : Fin 3, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p d, (lam i * χ⁻¹) u = 1) :
    ∃ (Λ : ↥(principalSeries3 p lam) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 p lam)),
      IsWhittakerFunctional3 (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ Λ ∧
      coefficientFn Λ f ≠ 0 ∧
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p,
        (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j -
            (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(d : ℤ))) →
        ∀ g : LocalGL3 p,
          ((χ (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ)⁻¹ * coefficientFn Λ f (g * k) =
            ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * coefficientFn Λ f g :=
  Ws46.LV.main p lam hlam hu χ hχ hχu d hd hlev

end S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_coefficientFn_ne_zero_forall_deepTwist_eq_of_forall_higherUnitsAt_of_pos (solution)
