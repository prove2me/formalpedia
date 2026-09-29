-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_typeIntegral_eq_zero_of_le_fst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/6cf4b716-866f-510f-beb3-1ef2f06d0d0d

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Theorems.Thm_LanglandsTunnell_CubicInduction_mem_span_rightTranslate_radicalP12_sub_of_forall_apply_mul_diagonal3
import Theorems.Thm_LanglandsTunnell_CubicInduction_mem_span_rightTranslate_radicalP21_sub_of_forall_apply_mul_diagonal3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isOpen_forall_apply_mul_iotaGL_mul_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_fst

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix Topology Filter
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_fst.LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal AutomorphicForm"

open scoped NNReal ENNReal

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.localBorel TateLocal.HasConductorExponentAt CubicInduction.mem_span_rightTranslate_radicalP12_sub_of_forall_apply_mul_diagonal3 CubicInduction.mem_span_rightTranslate_radicalP21_sub_of_forall_apply_mul_diagonal3 CubicInduction.exists_isOpen_forall_apply_mul_iotaGL_mul_eq TateLocal.isHaarMeasure_comap_val_mulMeasure TateLocal.psiLocal_eq_one_of_mem_integers"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 diagonal3_mul diagonal3_coe principalSeries3 rightTranslate_mem_principalSeries3 coefficientFn IsWhittakerFunctional3 gl3AmbientRightTranslate transposeInv3 upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 embedMat2 iotaGL coe_iotaGL LocalGL3 diagUnitGL2 coe_diagUnitGL2 diagHom diagUnits2 coe_diagUnits2 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply mem_span_rightTranslate_radicalP12_sub_of_forall_apply_mul_diagonal3 mem_span_rightTranslate_radicalP21_sub_of_forall_apply_mul_diagonal3 exists_isOpen_forall_apply_mul_iotaGL_mul_eq"
namespace TypeIntegralFst
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable {v : HeightOneSpectrum (𝓞 ℚ)} {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}

def Rπ (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (g : LocalGL3 v) :
    ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ) :=
  (gl3AmbientRightTranslate (R := ℂ) g).restrict fun _ h => rightTranslate_mem_principalSeries3 h g

@[scoped simp] theorem Rπ_apply_coe (g : LocalGL3 v) (F : ↥(principalSeries3 v χ)) (x : LocalGL3 v) :
    ((Rπ χ g F : ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ) x = (F : LocalGL3 v → ℂ) (x * g) := rfl

theorem Rπ_mul (g h : LocalGL3 v) (F : ↥(principalSeries3 v χ)) : Rπ χ (g * h) F = Rπ χ g (Rπ χ h F) := by
  refine Subtype.ext (funext fun x => ?_)
  simp only [Rπ_apply_coe, mul_assoc]

theorem Rπ_one (F : ↥(principalSeries3 v χ)) : Rπ χ 1 F = F := by
  refine Subtype.ext (funext fun x => ?_)
  simp only [Rπ_apply_coe, mul_one]

theorem coefficientFn_eq (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ)) (g : LocalGL3 v) :
    coefficientFn Λ f g = Λ (Rπ χ g f) := rfl

theorem whittaker_apply {ψ : AddChar (v.adicCompletion ℚ) ℂ} {Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ}
    (hΛ : IsWhittakerFunctional3 ψ Λ) (x y z : v.adicCompletion ℚ) (F : ↥(principalSeries3 v χ)) :
    Λ (Rπ χ (upperUnipotent3 x y z) F) = ψ (x + y) * Λ F :=
  hΛ x y z F

theorem diagonal3_mul_upperUnipotent3 (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (x y z : v.adicCompletion ℚ) :
    diagonal3 v a * upperUnipotent3 x y z =
      upperUnipotent3 ((a 0 : v.adicCompletion ℚ) * ((a 1)⁻¹ : (v.adicCompletion ℚ)ˣ) * x)
        ((a 1 : v.adicCompletion ℚ) * ((a 2)⁻¹ : (v.adicCompletion ℚ)ˣ) * y)
        ((a 0 : v.adicCompletion ℚ) * ((a 2)⁻¹ : (v.adicCompletion ℚ)ˣ) * z) * diagonal3 v a := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  simp only [Units.val_mul, diagonal3_coe, upperUnipotent3_coe, Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [mul_comm, mul_left_comm, (a 2).ne_zero]
  left
  rw [mul_left_comm, mul_inv_cancel₀ (a 1).ne_zero, mul_one]

section Whittaker

variable {ψ : AddChar (v.adicCompletion ℚ) ℂ} {Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ}

theorem exists_int_valued_le (x : v.adicCompletion ℚ) : ∃ m : ℤ, Valued.v x ≤ WithZero.exp m := by
  by_cases hx : Valued.v x = 0
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · exact ⟨WithZero.log (Valued.v x), by rw [WithZero.exp_log hx]⟩

theorem exists_forall_apply_Rπ_diagonal3_eq_zero_of_mem_span12
    (hψ : ∃ ℓ : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp ℓ → ψ x = 1)
    (hΛ : IsWhittakerFunctional3 ψ Λ) (F : ↥(principalSeries3 v χ))
    (hF : (F : LocalGL3 v → ℂ) ∈ Submodule.span ℂ {h : LocalGL3 v → ℂ | ∃ (w : Fin 2 → v.adicCompletion ℚ)
      (G : LocalGL3 v → ℂ), G ∈ principalSeries3 v χ ∧ h = gl3AmbientRightTranslate (R := ℂ) (radicalP12 w) G - G}) :
    ∃ N : ℤ, ∀ a : Fin 3 → (v.adicCompletion ℚ)ˣ,
      Valued.v ((a 0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤
        WithZero.exp (-N) * Valued.v ((a 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) →
      Λ (Rπ χ (diagonal3 v a) F) = 0 := by
  obtain ⟨ℓ, hℓ⟩ := hψ
  suffices key : ∀ (H : LocalGL3 v → ℂ) (hHs : H ∈ Submodule.span ℂ {h : LocalGL3 v → ℂ |
      ∃ (w : Fin 2 → v.adicCompletion ℚ) (G : LocalGL3 v → ℂ), G ∈ principalSeries3 v χ ∧
        h = gl3AmbientRightTranslate (R := ℂ) (radicalP12 w) G - G}),
      ∃ N : ℤ, ∀ (hH : H ∈ principalSeries3 v χ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ),
        Valued.v ((a 0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤
          WithZero.exp (-N) * Valued.v ((a 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) →
        Λ (Rπ χ (diagonal3 v a) ⟨H, hH⟩) = 0 by
    obtain ⟨N, hN⟩ := key F hF
    exact ⟨N, fun a ha => hN F.2 a ha⟩
  intro H hHs
  induction hHs using Submodule.span_induction with
  | mem H hH =>
    obtain ⟨w, G, hG, rfl⟩ := hH
    obtain ⟨m, hm⟩ := exists_int_valued_le (w 0)
    refine ⟨m - ℓ, fun hH a ha => ?_⟩
    have h1 : (⟨gl3AmbientRightTranslate (R := ℂ) (radicalP12 w) G - G, hH⟩ : ↥(principalSeries3 v χ)) =
        Rπ χ (radicalP12 w) ⟨G, hG⟩ - ⟨G, hG⟩ := rfl
    rw [h1, map_sub, ← Rπ_mul, show (radicalP12 w : LocalGL3 v) = upperUnipotent3 (w 0) 0 (w 1) from rfl,
      diagonal3_mul_upperUnipotent3, Rπ_mul, map_sub, whittaker_apply hΛ]
    have hval : Valued.v ((a 0 : v.adicCompletion ℚ) * ((a 1)⁻¹ : (v.adicCompletion ℚ)ˣ) * w 0) ≤ WithZero.exp ℓ := by
      have h1v : Valued.v (((a 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr (a 1).ne_zero
      rw [map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      have h2 : Valued.v ((a 0 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) *
          (Valued.v ((a 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ))⁻¹ ≤ WithZero.exp (-(m - ℓ)) := by
        rw [mul_inv_le_iff₀ (lt_of_le_of_ne zero_le' h1v.symm)]
        exact ha
      calc _ ≤ WithZero.exp (-(m - ℓ)) * WithZero.exp m := mul_le_mul' h2 hm
        _ = WithZero.exp ℓ := by rw [← WithZero.exp_add]; ring_nf
    rw [mul_zero, add_zero, hℓ _ hval, one_mul, sub_self]
  | zero =>
    refine ⟨0, fun hH a _ => ?_⟩
    have : (⟨0, hH⟩ : ↥(principalSeries3 v χ)) = 0 := rfl
    rw [this, map_zero, map_zero]
  | add H₁ H₂ hH₁ hH₂ ih₁ ih₂ =>
    obtain ⟨N₁, hN₁⟩ := ih₁
    obtain ⟨N₂, hN₂⟩ := ih₂
    have hle : Submodule.span ℂ {h : LocalGL3 v → ℂ | ∃ (w : Fin 2 → v.adicCompletion ℚ) (G : LocalGL3 v → ℂ),
        G ∈ principalSeries3 v χ ∧ h = gl3AmbientRightTranslate (R := ℂ) (radicalP12 w) G - G} ≤ principalSeries3 v χ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨w, G, hG, rfl⟩
      exact Submodule.sub_mem _ (rightTranslate_mem_principalSeries3 hG _) hG
    refine ⟨max N₁ N₂, fun hH a ha => ?_⟩
    have h1 : (⟨H₁ + H₂, hH⟩ : ↥(principalSeries3 v χ)) = ⟨H₁, hle hH₁⟩ + ⟨H₂, hle hH₂⟩ := rfl
    rw [h1, map_add, map_add, hN₁ (hle hH₁) a (le_trans ha (mul_le_mul_left ?_ _)),
      hN₂ (hle hH₂) a (le_trans ha (mul_le_mul_left ?_ _)), add_zero]
    · exact WithZero.exp_le_exp.mpr (neg_le_neg (le_max_right _ _))
    · exact WithZero.exp_le_exp.mpr (neg_le_neg (le_max_left _ _))
  | smul c H hH ih =>
    obtain ⟨N, hN⟩ := ih
    have hle : Submodule.span ℂ {h : LocalGL3 v → ℂ | ∃ (w : Fin 2 → v.adicCompletion ℚ) (G : LocalGL3 v → ℂ),
        G ∈ principalSeries3 v χ ∧ h = gl3AmbientRightTranslate (R := ℂ) (radicalP12 w) G - G} ≤ principalSeries3 v χ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨w, G, hG, rfl⟩
      exact Submodule.sub_mem _ (rightTranslate_mem_principalSeries3 hG _) hG
    refine ⟨N, fun hHπ a ha => ?_⟩
    have h1 : (⟨c • H, hHπ⟩ : ↥(principalSeries3 v χ)) = c • ⟨H, hle hH⟩ := rfl
    rw [h1, map_smul, map_smul, hN (hle hH) a ha, smul_zero]

theorem exists_forall_apply_Rπ_diagonal3_eq_zero_of_mem_span21
    (hψ : ∃ ℓ : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp ℓ → ψ x = 1)
    (hΛ : IsWhittakerFunctional3 ψ Λ) (F : ↥(principalSeries3 v χ))
    (hF : (F : LocalGL3 v → ℂ) ∈ Submodule.span ℂ {h : LocalGL3 v → ℂ | ∃ (w : Fin 2 → v.adicCompletion ℚ)
      (G : LocalGL3 v → ℂ), G ∈ principalSeries3 v χ ∧ h = gl3AmbientRightTranslate (R := ℂ) (radicalP21 w) G - G}) :
    ∃ N : ℤ, ∀ a : Fin 3 → (v.adicCompletion ℚ)ˣ,
      Valued.v ((a 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤
        WithZero.exp (-N) * Valued.v ((a 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) →
      Λ (Rπ χ (diagonal3 v a) F) = 0 := by
  obtain ⟨ℓ, hℓ⟩ := hψ
  suffices key : ∀ (H : LocalGL3 v → ℂ) (hHs : H ∈ Submodule.span ℂ {h : LocalGL3 v → ℂ |
      ∃ (w : Fin 2 → v.adicCompletion ℚ) (G : LocalGL3 v → ℂ), G ∈ principalSeries3 v χ ∧
        h = gl3AmbientRightTranslate (R := ℂ) (radicalP21 w) G - G}),
      ∃ N : ℤ, ∀ (hH : H ∈ principalSeries3 v χ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ),
        Valued.v ((a 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤
          WithZero.exp (-N) * Valued.v ((a 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) →
        Λ (Rπ χ (diagonal3 v a) ⟨H, hH⟩) = 0 by
    obtain ⟨N, hN⟩ := key F hF
    exact ⟨N, fun a ha => hN F.2 a ha⟩
  intro H hHs
  induction hHs using Submodule.span_induction with
  | mem H hH =>
    obtain ⟨w, G, hG, rfl⟩ := hH
    obtain ⟨m, hm⟩ := exists_int_valued_le (w 1)
    refine ⟨m - ℓ, fun hH a ha => ?_⟩
    have h1 : (⟨gl3AmbientRightTranslate (R := ℂ) (radicalP21 w) G - G, hH⟩ : ↥(principalSeries3 v χ)) =
        Rπ χ (radicalP21 w) ⟨G, hG⟩ - ⟨G, hG⟩ := rfl
    rw [h1, map_sub, ← Rπ_mul, show (radicalP21 w : LocalGL3 v) = upperUnipotent3 0 (w 1) (w 0) from rfl,
      diagonal3_mul_upperUnipotent3, Rπ_mul, map_sub, whittaker_apply hΛ]
    have hval : Valued.v ((a 1 : v.adicCompletion ℚ) * ((a 2)⁻¹ : (v.adicCompletion ℚ)ˣ) * w 1) ≤ WithZero.exp ℓ := by
      have h1v : Valued.v (((a 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr (a 2).ne_zero
      rw [map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      have h2 : Valued.v ((a 1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) *
          (Valued.v ((a 2 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ))⁻¹ ≤ WithZero.exp (-(m - ℓ)) := by
        rw [mul_inv_le_iff₀ (lt_of_le_of_ne zero_le' h1v.symm)]
        exact ha
      calc _ ≤ WithZero.exp (-(m - ℓ)) * WithZero.exp m := mul_le_mul' h2 hm
        _ = WithZero.exp ℓ := by rw [← WithZero.exp_add]; ring_nf
    rw [mul_zero, zero_add, hℓ _ hval, one_mul, sub_self]
  | zero =>
    refine ⟨0, fun hH a _ => ?_⟩
    have : (⟨0, hH⟩ : ↥(principalSeries3 v χ)) = 0 := rfl
    rw [this, map_zero, map_zero]
  | add H₁ H₂ hH₁ hH₂ ih₁ ih₂ =>
    obtain ⟨N₁, hN₁⟩ := ih₁
    obtain ⟨N₂, hN₂⟩ := ih₂
    have hle : Submodule.span ℂ {h : LocalGL3 v → ℂ | ∃ (w : Fin 2 → v.adicCompletion ℚ) (G : LocalGL3 v → ℂ),
        G ∈ principalSeries3 v χ ∧ h = gl3AmbientRightTranslate (R := ℂ) (radicalP21 w) G - G} ≤ principalSeries3 v χ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨w, G, hG, rfl⟩
      exact Submodule.sub_mem _ (rightTranslate_mem_principalSeries3 hG _) hG
    refine ⟨max N₁ N₂, fun hH a ha => ?_⟩
    have h1 : (⟨H₁ + H₂, hH⟩ : ↥(principalSeries3 v χ)) = ⟨H₁, hle hH₁⟩ + ⟨H₂, hle hH₂⟩ := rfl
    rw [h1, map_add, map_add, hN₁ (hle hH₁) a (le_trans ha (mul_le_mul_left ?_ _)),
      hN₂ (hle hH₂) a (le_trans ha (mul_le_mul_left ?_ _)), add_zero]
    · exact WithZero.exp_le_exp.mpr (neg_le_neg (le_max_right _ _))
    · exact WithZero.exp_le_exp.mpr (neg_le_neg (le_max_left _ _))
  | smul c H hH ih =>
    obtain ⟨N, hN⟩ := ih
    have hle : Submodule.span ℂ {h : LocalGL3 v → ℂ | ∃ (w : Fin 2 → v.adicCompletion ℚ) (G : LocalGL3 v → ℂ),
        G ∈ principalSeries3 v χ ∧ h = gl3AmbientRightTranslate (R := ℂ) (radicalP21 w) G - G} ≤ principalSeries3 v χ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨w, G, hG, rfl⟩
      exact Submodule.sub_mem _ (rightTranslate_mem_principalSeries3 hG _) hG
    refine ⟨N, fun hHπ a ha => ?_⟩
    have h1 : (⟨c • H, hHπ⟩ : ↥(principalSeries3 v χ)) = c • ⟨H, hle hH⟩ := rfl
    rw [h1, map_smul, map_smul, hN (hle hH) a ha, smul_zero]

end Whittaker

section Torus

variable (v)

def d3 : (Fin 3 → (v.adicCompletion ℚ)ˣ) →* LocalGL3 v where
  toFun := diagonal3 v
  map_one' := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    simp only [diagonal3_coe, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp
  map_mul' := diagonal3_mul v

@[scoped simp] theorem d3_apply (a : Fin 3 → (v.adicCompletion ℚ)ˣ) : d3 v a = diagonal3 v a := rfl

def e1 : (v.adicCompletion ℚ)ˣ →* (Fin 3 → (v.adicCompletion ℚ)ˣ) where
  toFun u := ![u, 1, 1]
  map_one' := by funext i; fin_cases i <;> rfl
  map_mul' x y := by funext i; fin_cases i <;> simp

def e3inv : (v.adicCompletion ℚ)ˣ →* (Fin 3 → (v.adicCompletion ℚ)ˣ) where
  toFun u := ![1, 1, u⁻¹]
  map_one' := by funext i; fin_cases i <;> simp
  map_mul' x y := by funext i; fin_cases i <;> simp [mul_comm]

@[scoped simp] theorem e1_apply (u : (v.adicCompletion ℚ)ˣ) : e1 v u = ![u, 1, 1] := rfl
@[scoped simp] theorem e3inv_apply (u : (v.adicCompletion ℚ)ˣ) : e3inv v u = ![1, 1, u⁻¹] := rfl

def D2 : (v.adicCompletion ℚ)ˣ × (v.adicCompletion ℚ)ˣ →* GL (Fin 2) (v.adicCompletion ℚ) where
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

variable {v}

theorem sum_eq_sum_of_injective_sphere {V : Subgroup (v.adicCompletion ℚ)ˣ} [Fintype (↥(sphere v) ⧸ V.subgroupOf (sphere v))]
    {M : Type*} [AddCommMonoid M] {φ : (v.adicCompletion ℚ)ˣ → M}
    (hφ : ∀ s ∈ sphere v, ∀ w ∈ V, φ (s * w) = φ s)
    (ρ : ↥(sphere v) ⧸ V.subgroupOf (sphere v) → ↥(sphere v))
    (hinj : Function.Injective fun q => (QuotientGroup.mk (ρ q) : ↥(sphere v) ⧸ V.subgroupOf (sphere v))) :
    ∑ q, φ (ρ q) = ∑ q : ↥(sphere v) ⧸ V.subgroupOf (sphere v), φ ((Quotient.out q : ↥(sphere v)) : (v.adicCompletion ℚ)ˣ) := by
  have hbij : Function.Bijective fun q => (QuotientGroup.mk (ρ q) : ↥(sphere v) ⧸ V.subgroupOf (sphere v)) :=
    Finite.injective_iff_bijective.mp hinj
  have hrep : ∀ t : ↥(sphere v), φ ((Quotient.out (QuotientGroup.mk t : ↥(sphere v) ⧸ V.subgroupOf (sphere v)) :
      ↥(sphere v)) : (v.adicCompletion ℚ)ˣ) = φ t := by
    intro t
    have h : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk t : ↥(sphere v) ⧸ V.subgroupOf (sphere v))) :
        ↥(sphere v) ⧸ V.subgroupOf (sphere v)) = QuotientGroup.mk t := QuotientGroup.out_eq' _
    rw [QuotientGroup.eq] at h
    have h' : (((Quotient.out (QuotientGroup.mk t : ↥(sphere v) ⧸ V.subgroupOf (sphere v)))⁻¹ * t : ↥(sphere v)) :
        (v.adicCompletion ℚ)ˣ) ∈ V := Subgroup.mem_subgroupOf.mp h
    have := hφ _ (Quotient.out (QuotientGroup.mk t : ↥(sphere v) ⧸ V.subgroupOf (sphere v))).2 _ h'
    rw [← this]
    congr 1
    simp
  calc ∑ q, φ (ρ q) = ∑ q, φ ((Quotient.out (QuotientGroup.mk (ρ q) : ↥(sphere v) ⧸ V.subgroupOf (sphere v)) :
        ↥(sphere v)) : (v.adicCompletion ℚ)ˣ) := Finset.sum_congr rfl fun q _ => (hrep (ρ q)).symm
    _ = _ := hbij.sum_comp (fun q : ↥(sphere v) ⧸ V.subgroupOf (sphere v) =>
        φ ((Quotient.out q : ↥(sphere v)) : (v.adicCompletion ℚ)ˣ))

theorem sum_mul_out {V : Subgroup (v.adicCompletion ℚ)ˣ} [Fintype (↥(sphere v) ⧸ V.subgroupOf (sphere v))]
    {M : Type*} [AddCommMonoid M] {φ : (v.adicCompletion ℚ)ˣ → M}
    (hφ : ∀ s ∈ sphere v, ∀ w ∈ V, φ (s * w) = φ s) {u : (v.adicCompletion ℚ)ˣ} (hu : u ∈ sphere v) :
    ∑ q : ↥(sphere v) ⧸ V.subgroupOf (sphere v), φ (u * ((Quotient.out q : ↥(sphere v)) : (v.adicCompletion ℚ)ˣ)) =
      ∑ q : ↥(sphere v) ⧸ V.subgroupOf (sphere v), φ ((Quotient.out q : ↥(sphere v)) : (v.adicCompletion ℚ)ˣ) := by
  let ρ : ↥(sphere v) ⧸ V.subgroupOf (sphere v) → ↥(sphere v) := fun q => ⟨u, hu⟩ * Quotient.out q
  have hinj : Function.Injective fun q => (QuotientGroup.mk (ρ q) : ↥(sphere v) ⧸ V.subgroupOf (sphere v)) := by
    intro q₁ q₂ h12
    have h12' := QuotientGroup.eq.mp h12
    have hmem : ((ρ q₁)⁻¹ * ρ q₂ : ↥(sphere v)) ∈ V.subgroupOf (sphere v) := h12'
    have heq : ((ρ q₁)⁻¹ * ρ q₂ : ↥(sphere v)) = (Quotient.out q₁)⁻¹ * Quotient.out q₂ := by
      simp only [ρ, _root_.mul_inv_rev]
      group
    rw [heq] at hmem
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂]
    exact QuotientGroup.eq.mpr hmem
  have h := sum_eq_sum_of_injective_sphere hφ ρ hinj
  simpa [ρ] using h

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

variable {v}

theorem isLocallyConstant_of_forall_mul_eq {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] {M : Type*}
    {φ : G → M} (V : Subgroup G) (hV : IsOpen (V : Set G)) (hφ : ∀ u, ∀ w ∈ V, φ (u * w) = φ u) :
    IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_exists_open]
  intro u
  refine ⟨(fun y => u⁻¹ * y) ⁻¹' (V : Set G), hV.preimage (continuous_const.mul continuous_id), by simp [V.one_mem], ?_⟩
  intro y hy
  have : y = u * (u⁻¹ * y) := by group
  rw [this]
  exact hφ u _ hy

theorem exists_forall_setIntegral_eq_zero (f : ↥(principalSeries3 v χ)) (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)
    (A : ℤ × ℤ → LocalGL3 v) (d : (v.adicCompletion ℚ)ˣ →* LocalGL3 v) (hd : Continuous d)
    (y : GL (Fin 2) (v.adicCompletion ℚ) → LocalGL3 v)
    (H : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) (hHc : IsCompact (H : Set (GL (Fin 2) (v.adicCompletion ℚ))))
    (hHo : IsOpen (H : Set (GL (Fin 2) (v.adicCompletion ℚ))))
    (hyU : ∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧
      ∀ k ∈ H, ∀ k' ∈ U, ∀ x : LocalGL3 v, (f : LocalGL3 v → ℂ) (x * k' * y k) = (f : LocalGL3 v → ℂ) (x * y k))
    (hyloc : IsLocallyConstant fun k : GL (Fin 2) (v.adicCompletion ℚ) => fun x : LocalGL3 v => (f : LocalGL3 v → ℂ) (x * y k))
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hηo : IsOpen (η.ker : Set (v.adicCompletion ℚ)ˣ))
    (hcor : ∀ F : ↥(principalSeries3 v χ),
      (∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧
        ∀ k ∈ U, ∀ g : LocalGL3 v, (F : LocalGL3 v → ℂ) (g * k) = (F : LocalGL3 v → ℂ) g) →
      (∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
        ∀ g : LocalGL3 v, (F : LocalGL3 v → ℂ) (g * d u) = (((η u)⁻¹ : ℂˣ) : ℂ) * (F : LocalGL3 v → ℂ) g) →
      ∃ N : ℤ, ∀ n : ℤ × ℤ, N ≤ n.1 → Λ (Rπ χ (A n) F) = 0)
    (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure] :
    ∃ N : ℤ, ∀ n : ℤ × ℤ, N ≤ n.1 →
      (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
        (∫ k in (H : Set (GL (Fin 2) (v.adicCompletion ℚ))), coefficientFn Λ f (A n * d u * y k) ∂μ₂) * ((η u : ℂˣ) : ℂ)
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) = 0 := by
  haveI := isHaarMeasure_locMul v
  obtain ⟨U, hUo, hUy⟩ := hyU

  let V : Subgroup (v.adicCompletion ℚ)ˣ := sphere v ⊓ U.comap d ⊓ η.ker
  have hVo : IsOpen (V : Set (v.adicCompletion ℚ)ˣ) :=
    ((isOpen_sphere v).inter (hUo.preimage hd)).inter hηo
  have hVS : ∀ w ∈ V, w ∈ sphere v := fun w hw => hw.1.1
  have hVU : ∀ w ∈ V, d w ∈ U := fun w hw => hw.1.2
  have hVη : ∀ w ∈ V, η w = 1 := fun w hw => hw.2
  haveI : Finite (↥(sphere v) ⧸ V.subgroupOf (sphere v)) :=
    Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen _ _ hVo)
  letI : Fintype (↥(sphere v) ⧸ V.subgroupOf (sphere v)) := Fintype.ofFinite _

  set sq : ↥(sphere v) ⧸ V.subgroupOf (sphere v) → (v.adicCompletion ℚ)ˣ :=
    fun q => ((Quotient.out q : ↥(sphere v)) : (v.adicCompletion ℚ)ˣ) with hsq
  have hsqS : ∀ q, sq q ∈ sphere v := fun q => (Quotient.out q : ↥(sphere v)).2

  have hinv : ∀ k ∈ H, ∀ s : (v.adicCompletion ℚ)ˣ, ∀ w ∈ V, ∀ B : LocalGL3 v,
      Rπ χ (B * d (s * w) * y k) f = Rπ χ (B * d s * y k) f := by
    intro k hk s w hw B
    refine Subtype.ext (funext fun x => ?_)
    simp only [Rπ_apply_coe, map_mul]
    have := hUy k hk (d w) (hVU w hw) (x * (B * d s))
    simp only [mul_assoc] at this ⊢
    exact this

  let Fv : GL (Fin 2) (v.adicCompletion ℚ) → ↥(principalSeries3 v χ) :=
    fun k => ∑ q, ((η (sq q) : ℂˣ) : ℂ) • Rπ χ (d (sq q) * y k) f
  have hFv_apply : ∀ k (g : LocalGL3 v), (Fv k : LocalGL3 v → ℂ) g =
      ∑ q, ((η (sq q) : ℂˣ) : ℂ) * (f : LocalGL3 v → ℂ) (g * (d (sq q) * y k)) := by
    intro k g
    simp only [Fv, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Rπ_apply_coe]

  have hF1 : ∀ k ∈ H, ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
      ∀ g : LocalGL3 v, (Fv k : LocalGL3 v → ℂ) (g * d u) = (((η u)⁻¹ : ℂˣ) : ℂ) * (Fv k : LocalGL3 v → ℂ) g := by
    intro k hk u hu g
    let φ : (v.adicCompletion ℚ)ˣ → ℂ := fun s => ((η s : ℂˣ) : ℂ) * (f : LocalGL3 v → ℂ) (g * (d s * y k))
    have hφ : ∀ s ∈ sphere v, ∀ w ∈ V, φ (s * w) = φ s := by
      intro s _ w hw
      simp only [φ, map_mul, hVη w hw, mul_one]
      congr 1
      have := congrArg (fun F : ↥(principalSeries3 v χ) => (F : LocalGL3 v → ℂ) g) (hinv k hk s w hw 1)
      simpa only [Rπ_apply_coe, one_mul, map_mul] using this
    have hsum := sum_mul_out hφ hu
    have hlhs : ∑ q, φ (u * sq q) = ((η u : ℂˣ) : ℂ) * (Fv k : LocalGL3 v → ℂ) (g * d u) := by
      rw [hFv_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [φ, map_mul, Units.val_mul, mul_assoc]
    rw [hlhs, ← hFv_apply] at hsum
    rw [← hsum, ← mul_assoc, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

  have hbase : IsOpen {k' : LocalGL3 v | ∀ x : LocalGL3 v, (f : LocalGL3 v → ℂ) (x * k') = (f : LocalGL3 v → ℂ) x} := by

    let St : Subgroup (LocalGL3 v) :=
      { carrier := {k' | ∀ x : LocalGL3 v, (f : LocalGL3 v → ℂ) (x * k') = (f : LocalGL3 v → ℂ) x}
        mul_mem' := fun {a b} ha hb x => by rw [← mul_assoc, hb, ha]
        one_mem' := fun x => by rw [mul_one]
        inv_mem' := fun {a} ha x => by rw [← ha (x * a⁻¹), inv_mul_cancel_right] }
    have hcont : Continuous fun k' : LocalGL3 v => y 1 * k' * (y 1)⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    have hsub : (fun k' : LocalGL3 v => y 1 * k' * (y 1)⁻¹) ⁻¹' (U : Set (LocalGL3 v)) ⊆ St := by
      intro k' hk' x
      have := hUy 1 H.one_mem _ hk' (x * (y 1)⁻¹)
      simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel, mul_one] using this
    show IsOpen (St : Set (LocalGL3 v))
    have h1 : (1 : LocalGL3 v) ∈ (fun k' : LocalGL3 v => y 1 * k' * (y 1)⁻¹) ⁻¹' (U : Set (LocalGL3 v)) := by
      show y 1 * 1 * (y 1)⁻¹ ∈ (U : Set (LocalGL3 v))
      rw [mul_one, mul_inv_cancel]; exact U.one_mem
    exact Subgroup.isOpen_of_mem_nhds St (Filter.mem_of_superset ((hUo.preimage hcont).mem_nhds h1) hsub)
  have hSt : ∀ z : LocalGL3 v, IsOpen {k' : LocalGL3 v | ∀ x : LocalGL3 v,
      (f : LocalGL3 v → ℂ) (x * k' * z) = (f : LocalGL3 v → ℂ) (x * z)} := by
    intro z
    have heq : {k' : LocalGL3 v | ∀ x : LocalGL3 v, (f : LocalGL3 v → ℂ) (x * k' * z) = (f : LocalGL3 v → ℂ) (x * z)} =
        (fun k' => z⁻¹ * k' * z) ⁻¹' {k' : LocalGL3 v | ∀ x : LocalGL3 v, (f : LocalGL3 v → ℂ) (x * k') = (f : LocalGL3 v → ℂ) x} := by
      ext k'
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      constructor
      · intro h x
        have := h (x * z⁻¹)
        simpa only [mul_assoc, inv_mul_cancel_right, mul_inv_cancel_left, inv_mul_cancel, mul_one] using this
      · intro h x
        have := h (x * z)
        simpa only [mul_assoc, mul_inv_cancel_left] using this
    rw [heq]
    exact hbase.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hF2 : ∀ k, ∃ U₀ : Subgroup (LocalGL3 v), IsOpen (U₀ : Set (LocalGL3 v)) ∧
      ∀ k' ∈ U₀, ∀ g : LocalGL3 v, (Fv k : LocalGL3 v → ℂ) (g * k') = (Fv k : LocalGL3 v → ℂ) g := by
    intro k
    let Sz : (↥(sphere v) ⧸ V.subgroupOf (sphere v)) → Subgroup (LocalGL3 v) := fun q =>
      { carrier := {k' | ∀ x : LocalGL3 v, (f : LocalGL3 v → ℂ) (x * k' * (d (sq q) * y k)) =
          (f : LocalGL3 v → ℂ) (x * (d (sq q) * y k))}
        mul_mem' := fun {a b} ha hb x => by
          have h1 := hb (x * a)
          have h2 := ha x
          simp only [mul_assoc] at h1 h2 ⊢
          rw [h1, h2]
        one_mem' := fun x => by rw [mul_one]
        inv_mem' := fun {a} ha x => by
          have := ha (x * a⁻¹)
          simp only [mul_assoc, inv_mul_cancel_left] at this ⊢
          exact this.symm }
    refine ⟨⨅ q, Sz q, ?_, fun k' hk' g => ?_⟩
    · rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite fun q => hSt (d (sq q) * y k)
    · rw [hFv_apply, hFv_apply]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hq : k' ∈ Sz q := (Subgroup.mem_iInf.mp hk') q
      rw [hq g]

  have hF3 : ∀ k (B : LocalGL3 v), Λ (Rπ χ B (Fv k)) =
      ∑ q, ((η (sq q) : ℂˣ) : ℂ) * coefficientFn Λ f (B * d (sq q) * y k) := by
    intro k B
    simp only [Fv, map_sum, map_smul, smul_eq_mul, coefficientFn_eq, ← Rπ_mul, mul_assoc]

  have hFvloc : IsLocallyConstant Fv := by
    rw [IsLocallyConstant.iff_exists_open]
    intro k
    refine ⟨{k'' | (fun x : LocalGL3 v => (f : LocalGL3 v → ℂ) (x * y k'')) = fun x => (f : LocalGL3 v → ℂ) (x * y k)},
      hyloc.isOpen_fiber _, rfl, fun k'' hk'' => ?_⟩
    simp only [Fv]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    refine Subtype.ext (funext fun x => ?_)
    simp only [Rπ_apply_coe]
    have := congrFun hk'' (x * d (sq q))
    simpa only [mul_assoc] using this

  have hWloc : ∀ B : LocalGL3 v, IsLocallyConstant fun k => coefficientFn Λ f (B * y k) := by
    intro B
    rw [IsLocallyConstant.iff_exists_open]
    intro k
    refine ⟨{k'' | (fun x : LocalGL3 v => (f : LocalGL3 v → ℂ) (x * y k'')) = fun x => (f : LocalGL3 v → ℂ) (x * y k)},
      hyloc.isOpen_fiber _, rfl, fun k'' hk'' => ?_⟩
    simp only [coefficientFn_eq]
    congr 1
    refine Subtype.ext (funext fun x => ?_)
    simp only [Rπ_apply_coe]
    have := congrFun hk'' (x * B)
    simpa only [mul_assoc] using this

  have hN : ∀ k ∈ H, ∃ N : ℤ, ∀ n : ℤ × ℤ, N ≤ n.1 → Λ (Rπ χ (A n) (Fv k)) = 0 :=
    fun k hk => hcor (Fv k) (hF2 k) (hF1 k hk)
  choose! Nf hNf using hN
  obtain ⟨t, ht⟩ := hHc.elim_finite_subcover (fun i : ↥H => {k'' | Fv k'' = Fv (i : GL (Fin 2) (v.adicCompletion ℚ))})
    (fun i => hFvloc.isOpen_fiber _) (fun k hk => Set.mem_iUnion.mpr ⟨⟨k, hk⟩, rfl⟩)
  refine ⟨((t.sup fun i => (Nf (i : GL (Fin 2) (v.adicCompletion ℚ))).toNat : ℕ) : ℤ), fun n hn => ?_⟩
  have hvan : ∀ k ∈ H, Λ (Rπ χ (A n) (Fv k)) = 0 := by
    intro k hk
    have hk' := ht hk
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hk'
    obtain ⟨i, hi, hki⟩ := hk'
    rw [hki]
    refine hNf i i.2 n (le_trans ?_ hn)
    calc Nf (i : GL (Fin 2) (v.adicCompletion ℚ)) ≤ ((Nf (i : GL (Fin 2) (v.adicCompletion ℚ))).toNat : ℤ) := Int.self_le_toNat _
      _ ≤ _ := by
        exact_mod_cast Finset.le_sup (f := fun i : ↥H => (Nf (i : GL (Fin 2) (v.adicCompletion ℚ))).toNat) hi

  set φ : (v.adicCompletion ℚ)ˣ → ℂ := fun u =>
    (∫ k in (H : Set (GL (Fin 2) (v.adicCompletion ℚ))), coefficientFn Λ f (A n * d u * y k) ∂μ₂) * ((η u : ℂˣ) : ℂ) with hφdef
  have hφV : ∀ u, ∀ w ∈ V, φ (u * w) = φ u := by
    intro u w hw
    have hη1 : ((η (u * w) : ℂˣ) : ℂ) = ((η u : ℂˣ) : ℂ) := by rw [map_mul, hVη w hw, mul_one]
    simp only [hφdef, hη1]
    congr 1
    refine setIntegral_congr_fun hHo.measurableSet fun k hk => ?_
    show coefficientFn Λ f (A n * d (u * w) * y k) = coefficientFn Λ f (A n * d u * y k)
    rw [coefficientFn_eq, coefficientFn_eq, hinv k hk u w hw (A n)]
  have hφc : Continuous φ := (isLocallyConstant_of_forall_mul_eq V hVo hφV).continuous
  have hint : ∀ s : (v.adicCompletion ℚ)ˣ, IntegrableOn (fun u => φ (s * u))
      {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1} (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) :=
    fun s => (hφc.comp (continuous_const.mul continuous_id)).continuousOn.integrableOn_compact (isCompact_sphere v)
  have hleft : ∀ s ∈ sphere v,
      ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}, φ (s * u) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) =
      ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}, φ u ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) :=
    fun s hs => setIntegral_subgroup_mul_left _ (sphere v) (isOpen_sphere v).measurableSet φ hs

  have hkint : ∀ B : LocalGL3 v, IntegrableOn (fun k => coefficientFn Λ f (B * y k))
      (H : Set (GL (Fin 2) (v.adicCompletion ℚ))) μ₂ :=
    fun B => (hWloc B).continuous.continuousOn.integrableOn_compact hHc
  have hsum0 : ∀ u ∈ sphere v, ∑ q, φ (sq q * u) = 0 := by
    intro u hu
    have hu1 : Valued.v (u : v.adicCompletion ℚ) = 1 := hu
    have hstep : ∀ q, φ (sq q * u) = ∫ k in (H : Set (GL (Fin 2) (v.adicCompletion ℚ))),
        ((η (u * sq q) : ℂˣ) : ℂ) * coefficientFn Λ f (A n * d u * d (sq q) * y k) ∂μ₂ := by
      intro q
      simp only [hφdef]
      rw [mul_comm (sq q) u, mul_comm, ← integral_const_mul]
      refine setIntegral_congr_fun hHo.measurableSet fun k _ => ?_
      simp only [map_mul, mul_assoc]
    simp_rw [hstep]
    rw [← integral_finsetSum _ (fun q _ => ((hkint (A n * d u * d (sq q))).integrable.const_mul _))]
    have hzero : ∀ k ∈ (H : Set (GL (Fin 2) (v.adicCompletion ℚ))),
        ∑ q, ((η (u * sq q) : ℂˣ) : ℂ) * coefficientFn Λ f (A n * d u * d (sq q) * y k) = 0 := by
      intro k hk
      have h1 : ∑ q, ((η (u * sq q) : ℂˣ) : ℂ) * coefficientFn Λ f (A n * d u * d (sq q) * y k) =
          ((η u : ℂˣ) : ℂ) * Λ (Rπ χ (A n * d u) (Fv k)) := by
        rw [hF3, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [map_mul, Units.val_mul, mul_assoc]
      have h2 : Rπ χ (d u) (Fv k) = (((η u)⁻¹ : ℂˣ) : ℂ) • Fv k := by
        refine Subtype.ext (funext fun g => ?_)
        rw [Rπ_apply_coe, hF1 k hk u hu1 g, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [h1, Rπ_mul, h2, map_smul, map_smul, hvan k hk, smul_zero, mul_zero]
    rw [setIntegral_congr_fun hHo.measurableSet hzero]
    simp

  have hcard : (Fintype.card (↥(sphere v) ⧸ V.subgroupOf (sphere v)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have key : (Fintype.card (↥(sphere v) ⧸ V.subgroupOf (sphere v)) : ℂ) *
      ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}, φ u
        ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) = 0 := by
    calc _ = ∑ q : ↥(sphere v) ⧸ V.subgroupOf (sphere v),
          ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}, φ u
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ q : ↥(sphere v) ⧸ V.subgroupOf (sphere v),
          ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}, φ (sq q * u)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) :=
          Finset.sum_congr rfl fun q _ => (hleft (sq q) (hsqS q)).symm
      _ = ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}, ∑ q, φ (sq q * u)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) :=
          (integral_finsetSum _ fun q _ => hint (sq q)).symm
      _ = ∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1}, (0 : ℂ)
            ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) :=
          setIntegral_congr_fun (isOpen_sphere v).measurableSet fun u hu => hsum0 u hu
      _ = 0 := by simp
  exact (mul_eq_zero.mp key).resolve_left hcard

end Engine

section Data

variable (v)

def ev1 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ :=
  (LinearMap.proj (1 : LocalGL3 v) : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ).comp (principalSeries3 v χ).subtype

theorem coefficientFn_ev1 (f : ↥(principalSeries3 v χ)) : coefficientFn (ev1 v χ) f = (f : LocalGL3 v → ℂ) := by
  funext g
  show (f : LocalGL3 v → ℂ) (1 * g) = _
  rw [one_mul]

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

end LanglandsTunnell.CubicInduction.TypeIntegralFst
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_fst.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_fst.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_fst.LanglandsTunnell.CubicInduction.TypeIntegralFst"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_fst.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_fst.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_fst.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_fst.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_fst.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_fst.LanglandsTunnell.CubicInduction.TypeIntegralFst"

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse

open scoped nonZeroDivisors

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_fst.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.TypeIntegralFst in
open scoped Classical in

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψinv : ψv = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 3 → ℕ)
    (ha : ∀ i, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (χ i) (a i))
    (W : LocalGL3 v → ℂ)
    (hmem : ∃ (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ)),
      IsWhittakerFunctional3 ψv Λ ∧ W = coefficientFn Λ f)
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (b : ℕ)
    (hfloorb : ∀ i, 2 * b + 1 ≤ a i) :
    ∀ (g₃ : LocalGL3 v) (k₀ : GL (Fin 2) (v.adicCompletion ℚ)) (η : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (c : ℕ),
    LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v η c → c ≤ b →
    letI := localBorel ℚ v
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      ∃ N : ℤ, ∀ n : ℤ × ℤ, N ≤ n.1 →
        (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
            (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) :
                  Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                W (iotaGL (UnramifiedWhittaker.scalarPi
                      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
                      ^ n.1 * u) * (k₀ * k)) * g₃) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) = 0 ∧
        (∫ u in {u : (v.adicCompletion ℚ)ˣ | Valued.v (u : v.adicCompletion ℚ) = 1},
            (∫ k in ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) :
                  Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) : Set (GL (Fin 2) (v.adicCompletion ℚ))),
                dualWhittakerFn3 (fun x => W (x * g₃)) (iotaGL (UnramifiedWhittaker.scalarPi
                      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 *
                    diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ
                      ^ n.1 * u) * (k₀ * AutomorphicForm.transposeInvN (Fin 2) k))) ∂μ₂) * ((η u : ℂˣ) : ℂ)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))) = 0 := by
  intro g₃ k₀ η c hη hcb μ₂ hμ₂
  obtain ⟨Λ, f, hΛ, rfl⟩ := hmem
  have hK₁ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ v (v.asIdeal ^ b) (pow_ne_zero _ v.ne_bot)
  set K₁ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ)) := AdelicDock.localLevelOne (𝓞 ℚ) ℚ v (v.asIdeal ^ b) with hK₁def

  have hψ : ∃ ℓ : ℤ, ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp ℓ → ψv x = 1 := by
    refine ⟨0, fun x hx => ?_⟩
    rw [hψinv, AddChar.inv_apply]
    refine LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ v (-x) ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_neg]
    simpa using hx

  obtain ⟨U₁, hU₁o, hU₁⟩ := LanglandsTunnell.CubicInduction.exists_isOpen_forall_apply_mul_iotaGL_mul_eq v χ
    (f : LocalGL3 v → ℂ) ⟨ev1 v χ, f, (coefficientFn_ev1 v f).symm⟩ b g₃ k₀
  obtain ⟨U₃, hU₃o, hU₃⟩ := LanglandsTunnell.CubicInduction.exists_isOpen_forall_apply_mul_iotaGL_mul_eq v χ
    (f : LocalGL3 v → ℂ) ⟨ev1 v χ, f, (coefficientFn_ev1 v f).symm⟩ b g₃ 1
  have hU₃' : ∀ k' ∈ U₃, ∀ x : LocalGL3 v, (f : LocalGL3 v → ℂ) (x * k' * g₃) = (f : LocalGL3 v → ℂ) (x * g₃) := by
    intro k' hk' x
    have h := (hU₃ 1 K₁.one_mem k' hk' x).1
    simpa only [mul_one, map_one, one_mul] using h

  have hne : ∀ i : Fin 3, ∃ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 ∧ η u = 1 ∧ χ i u ≠ 1 := by
    intro i
    have hlt : c < a i := by have := hfloorb i; omega
    obtain ⟨u, hu, hne⟩ := (ha i).2 c hlt
    exact ⟨u, hu.1, hη.1 u hu, hne⟩
  have hηo := isOpen_ker_of_hasConductorExponentAt v hη

  set y₁ : GL (Fin 2) (v.adicCompletion ℚ) → LocalGL3 v := fun k => iotaGL (k₀ * k) * g₃ with hy₁
  set y₂ : GL (Fin 2) (v.adicCompletion ℚ) → LocalGL3 v :=
    fun k => longWeyl3 * iotaGL (transposeInvN (Fin 2) k₀ * k) * g₃ with hy₂
  have hyU₁ : ∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧
      ∀ k ∈ K₁, ∀ k' ∈ U, ∀ x : LocalGL3 v, (f : LocalGL3 v → ℂ) (x * k' * y₁ k) = (f : LocalGL3 v → ℂ) (x * y₁ k) :=
    ⟨U₁, hU₁o, fun k hk k' hk' x => (hU₁ k hk k' hk' x).1⟩
  have hyU₂ : ∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧
      ∀ k ∈ K₁, ∀ k' ∈ U, ∀ x : LocalGL3 v, (f : LocalGL3 v → ℂ) (x * k' * y₂ k) = (f : LocalGL3 v → ℂ) (x * y₂ k) := by
    let U₂ : Subgroup (LocalGL3 v) :=
      { carrier := {k'' | (longWeyl3 : LocalGL3 v)⁻¹ * k'' * longWeyl3 ∈ U₁}
        mul_mem' := fun {p q} hp hq => by
          have : (longWeyl3 : LocalGL3 v)⁻¹ * (p * q) * longWeyl3 =
              ((longWeyl3 : LocalGL3 v)⁻¹ * p * longWeyl3) * ((longWeyl3 : LocalGL3 v)⁻¹ * q * longWeyl3) := by group
          show (longWeyl3 : LocalGL3 v)⁻¹ * (p * q) * longWeyl3 ∈ U₁
          rw [this]; exact U₁.mul_mem hp hq
        one_mem' := by
          show (longWeyl3 : LocalGL3 v)⁻¹ * 1 * longWeyl3 ∈ U₁
          rw [mul_one, inv_mul_cancel]; exact U₁.one_mem
        inv_mem' := fun {p} hp => by
          have : (longWeyl3 : LocalGL3 v)⁻¹ * p⁻¹ * longWeyl3 = ((longWeyl3 : LocalGL3 v)⁻¹ * p * longWeyl3)⁻¹ := by group
          show (longWeyl3 : LocalGL3 v)⁻¹ * p⁻¹ * longWeyl3 ∈ U₁
          rw [this]; exact U₁.inv_mem hp }
    refine ⟨U₂, hU₁o.preimage ((continuous_const.mul continuous_id).mul continuous_const), fun k hk k' hk' x => ?_⟩
    have h := (hU₁ k hk _ hk' (x * longWeyl3)).2
    have e1 : x * longWeyl3 * ((longWeyl3 : LocalGL3 v)⁻¹ * k' * longWeyl3) * (iotaGL (transposeInvN (Fin 2) k₀ * k) * g₃) =
        x * k' * y₂ k := by simp only [hy₂]; group
    have e2 : x * longWeyl3 * (iotaGL (transposeInvN (Fin 2) k₀ * k) * g₃) = x * y₂ k := by simp only [hy₂]; group
    rw [e1, e2] at h
    exact h
  have hyloc : ∀ (z : LocalGL3 v) (m : GL (Fin 2) (v.adicCompletion ℚ)),
      IsLocallyConstant fun k : GL (Fin 2) (v.adicCompletion ℚ) =>
        fun x : LocalGL3 v => (f : LocalGL3 v → ℂ) (x * (z * iotaGL (m * k) * g₃)) := by
    intro z m
    rw [IsLocallyConstant.iff_exists_open]
    intro k
    refine ⟨(fun k'' => iotaGL (k⁻¹ * k'')) ⁻¹' (U₃ : Set (LocalGL3 v)),
      hU₃o.preimage ((continuous_iotaGL v).comp (continuous_const.mul continuous_id)), ?_, fun k'' hk'' => ?_⟩
    · show iotaGL (k⁻¹ * k) ∈ (U₃ : Set (LocalGL3 v))
      rw [inv_mul_cancel, map_one]; exact U₃.one_mem
    · funext x
      have h := hU₃' _ hk'' (x * z * iotaGL (m * k))
      have e : (iotaGL (m * k'') : LocalGL3 v) = iotaGL (m * k) * iotaGL (k⁻¹ * k'') := by
        rw [← map_mul]; congr 1; group
      rw [e]
      simpa only [mul_assoc] using h
  have hyloc₁ : IsLocallyConstant fun k : GL (Fin 2) (v.adicCompletion ℚ) =>
      fun x : LocalGL3 v => (f : LocalGL3 v → ℂ) (x * y₁ k) := by
    simpa only [hy₁, one_mul] using hyloc 1 k₀
  have hyloc₂ : IsLocallyConstant fun k : GL (Fin 2) (v.adicCompletion ℚ) =>
      fun x : LocalGL3 v => (f : LocalGL3 v → ℂ) (x * y₂ k) := by
    simpa only [hy₂] using hyloc longWeyl3 (transposeInvN (Fin 2) k₀)

  have hcor₁ : ∀ F : ↥(principalSeries3 v χ),
      (∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧
        ∀ k ∈ U, ∀ g : LocalGL3 v, (F : LocalGL3 v → ℂ) (g * k) = (F : LocalGL3 v → ℂ) g) →
      (∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
        ∀ g : LocalGL3 v, (F : LocalGL3 v → ℂ) (g * ((d3 v).comp (e1 v)) u) = (((η u)⁻¹ : ℂˣ) : ℂ) * (F : LocalGL3 v → ℂ) g) →
      ∃ N : ℤ, ∀ n : ℤ × ℤ, N ≤ n.1 →
        Λ (Rπ χ (d3 v (![Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ, Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ, 1] ^ n.2 * ![Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ, 1, 1] ^ n.1)) F) = 0 := by
    intro F hFsm hFiso
    have hθ : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
        ∀ g : LocalGL3 v, (F : LocalGL3 v → ℂ) (g * diagonal3 v ![u, 1, 1]) = ((η⁻¹ u : ℂˣ) : ℂ) * (F : LocalGL3 v → ℂ) g := by
      intro u hu g
      rw [MonoidHom.inv_apply]
      exact hFiso u hu g
    have hne' : ∀ i : Fin 3, ∃ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 ∧ η⁻¹ u ≠ χ i u := by
      intro i
      obtain ⟨u, hu, hη1, hχ1⟩ := hne i
      exact ⟨u, hu, by rw [MonoidHom.inv_apply, hη1, inv_one]; exact fun h => hχ1 h.symm⟩
    have hspan := LanglandsTunnell.CubicInduction.mem_span_rightTranslate_radicalP12_sub_of_forall_apply_mul_diagonal3
      v χ (F : LocalGL3 v → ℂ) F.2 hFsm η⁻¹ hθ hne'
    obtain ⟨N, hN⟩ := exists_forall_apply_Rπ_diagonal3_eq_zero_of_mem_span12 hψ hΛ F hspan
    exact ⟨N, fun n hn => hN _ (cond_fst hπ hϖ hn)⟩
  have hcor₂ : ∀ F : ↥(principalSeries3 v χ),
      (∃ U : Subgroup (LocalGL3 v), IsOpen (U : Set (LocalGL3 v)) ∧
        ∀ k ∈ U, ∀ g : LocalGL3 v, (F : LocalGL3 v → ℂ) (g * k) = (F : LocalGL3 v → ℂ) g) →
      (∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
        ∀ g : LocalGL3 v, (F : LocalGL3 v → ℂ) (g * ((d3 v).comp (e3inv v)) u) = (((η u)⁻¹ : ℂˣ) : ℂ) * (F : LocalGL3 v → ℂ) g) →
      ∃ N : ℤ, ∀ n : ℤ × ℤ, N ≤ n.1 →
        Λ (Rπ χ (d3 v ![1, (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2)⁻¹, (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 * Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1)⁻¹]) F) = 0 := by
    intro F hFsm hFiso
    have hθ : ∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
        ∀ g : LocalGL3 v, (F : LocalGL3 v → ℂ) (g * diagonal3 v ![1, 1, u]) = ((η u : ℂˣ) : ℂ) * (F : LocalGL3 v → ℂ) g := by
      intro u hu g
      have hu' : Valued.v ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
        rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
      have h := hFiso u⁻¹ hu' g
      have e : ((d3 v).comp (e3inv v)) u⁻¹ = diagonal3 v ![1, 1, u] := by
        show diagonal3 v ![1, 1, u⁻¹⁻¹] = _
        rw [inv_inv]
      rw [e, map_inv, inv_inv] at h
      exact h
    have hne' : ∀ i : Fin 3, ∃ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 ∧ η u ≠ χ i u := by
      intro i
      obtain ⟨u, hu, hη1, hχ1⟩ := hne i
      exact ⟨u, hu, by rw [hη1]; exact fun h => hχ1 h.symm⟩
    have hspan := LanglandsTunnell.CubicInduction.mem_span_rightTranslate_radicalP21_sub_of_forall_apply_mul_diagonal3
      v χ (F : LocalGL3 v → ℂ) F.2 hFsm η hθ hne'
    obtain ⟨N, hN⟩ := exists_forall_apply_Rπ_diagonal3_eq_zero_of_mem_span21 hψ hΛ F hspan
    exact ⟨N, fun n hn => hN _ (cond_snd hπ hϖ hn)⟩

  obtain ⟨N₁, hN₁⟩ := exists_forall_setIntegral_eq_zero f Λ (fun n => d3 v (![Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ, Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ, 1] ^ n.2 * ![Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ, 1, 1] ^ n.1))
    ((d3 v).comp (e1 v)) (continuous_d3_e1 v) y₁ K₁ hK₁.1 hK₁.2 hyU₁ hyloc₁ η hηo hcor₁ μ₂
  obtain ⟨N₂, hN₂⟩ := exists_forall_setIntegral_eq_zero f Λ (fun n => d3 v ![1, (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2)⁻¹, (Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.2 * Units.mk0 (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n.1)⁻¹])
    ((d3 v).comp (e3inv v)) (continuous_d3_e3inv v) y₂ K₁ hK₁.1 hK₁.2 hyU₂ hyloc₂ η hηo hcor₂ μ₂
  refine ⟨max N₁ N₂, fun n hn => ⟨?_, ?_⟩⟩
  · have h := hN₁ n (le_trans (le_max_left _ _) hn)
    simp_rw [arg_fst]
    exact h
  · have h := hN₂ n (le_trans (le_max_right _ _) hn)
    have hkτ : ∀ k : GL (Fin 2) (v.adicCompletion ℚ),
        k₀ * transposeInvN (Fin 2) k = transposeInvN (Fin 2) (transposeInvN (Fin 2) k₀ * k) := by
      intro k
      rw [transposeInvN_mul, transposeInvN_transposeInvN]
    simp_rw [dualWhittakerFn3_apply, hkτ, arg_snd]
    exact h

end S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_fst
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_typeIntegral_eq_zero_of_le_fst (solution)
