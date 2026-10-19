-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Auxiliary.energy_increment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:05:35.268869+00:00
-- url     : https://prove2.me/submissions/cf6d7bb1-1611-4145-ae37-f849290a85d5

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/BinaryPacket.lean:L180-L192
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Auxiliary.energy_increment. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket

-- ---- from OAI.Analysis.Littlewood.BinaryPacket ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uX

namespace AsymptoticallyMinimalLittlewood
namespace Auxiliary
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ComplexConjugate ENNReal
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instMeasureSpaceUnitAddCircle_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsAddHaarMeasureUnitAddCircleVolume_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsProbabilityMeasureUnitAddCircleVolume_oAI
lemma integral_circle_fourier (n : ℤ) :
    (∫ x : UnitAddCircle, fourier n x) = if n=0 then 1 else 0 := by
  have hh := congrFun (fourierCoeff_fourier (T := (1:ℝ)) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using! hh

lemma cosine_cast (x : UnitAddCircle) :
    (cosine x : ℂ) = (fourier 1 x + fourier (-1) x)/2 := by
  rw [fourier_neg]
  apply Complex.ext <;> simp [cosine]

lemma integral_cosine : (∫ x : UnitAddCircle, cosine x) = 0 := by
  have hi : Integrable (fun x : UnitAddCircle ↦ fourier 1 x) := (fourier 1).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ x : UnitAddCircle, (fourier 1 x).re) = 0
  have hr : (∫ x : UnitAddCircle, (fourier 1 x).re) = (∫ x : UnitAddCircle, fourier 1 x).re := by
    simpa using! integral_re hi
  rw [hr, integral_circle_fourier]
  norm_num

lemma integral_cosine_sq : (∫ x : UnitAddCircle, cosine x ^ 2) = 1/2 := by
  have hp (x : UnitAddCircle) : ((cosine x ^ 2 : ℝ) : ℂ) =
      (fourier 2 x + 2 + fourier (-2) x)/4 := by
    rw [Complex.ofReal_pow, cosine_cast, div_pow, add_sq]
    have h1 : fourier (1:ℤ) x * fourier 1 x = fourier 2 x := by
      rw [← fourier_add]; norm_num
    have h2 : fourier (-1:ℤ) x * fourier (-1) x = fourier (-2) x := by
      rw [← fourier_add]; norm_num
    have h3 : fourier (1:ℤ) x * fourier (-1) x = 1 := by rw [← fourier_add]; norm_num
    rw [pow_two, pow_two, h1, h2]
    calc
      _ = (fourier 2 x + 2*(fourier 1 x*fourier (-1) x) + fourier (-2) x)/4 := by ring
      _ = _ := by rw [h3]; ring
  have hh : ((∫ x : UnitAddCircle, cosine x ^ 2 : ℝ) : ℂ) = (1/2:ℂ) := by
    have hr : (∫ x : UnitAddCircle, ((cosine x ^ 2 : ℝ) : ℂ)) =
        ((∫ x : UnitAddCircle, cosine x^2 : ℝ) : ℂ) := by
      simpa using! (integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure UnitAddCircle)) (f := fun x : UnitAddCircle ↦ cosine x^(2:ℕ)))
    rw [← hr]
    simp_rw [hp]
    rw [integral_div, integral_add, integral_add, integral_circle_fourier,
      integral_circle_fourier, integral_const]
    · norm_num
    all_goals apply Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)
  have hr := congrArg Complex.re hh
  simpa using hr

lemma integral_pi_cons {n : ℕ} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin (n+1) → UnitAddCircle) → E) (hf : Integrable f) :
    (∫ x, f x) = ∫ u : UnitAddCircle, ∫ y : Fin n → UnitAddCircle, f (Fin.cons u y) := by
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ UnitAddCircle) 0).symm
  have hi := he.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) |>.mpr hf
  rw [← he.integral_comp' f]
  change (∫ z, f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ UnitAddCircle) 0).symm z) ∂(volume.prod volume)) = _
  have hp := integral_prod _ hi
  dsimp only [Function.comp_def] at hp
  rw [hp]
  congr 1
  ext u
  congr 1
  ext y
  congr 1
  ext i
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    ]

lemma binary_cons (n : ℕ) (u : UnitAddCircle) (y : Fin n → UnitAddCircle) :
    binary (n+1) (Fin.cons u y) = binary n y+(1-binary n y^2)/2*cosine u := by
  simp [binary]

lemma integrable_cont {X : Type uX} {E : Type uE} [TopologicalSpace X] [MeasurableSpace X]
    [CompactSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {f : X → E} (h : Continuous f) :
    Integrable f μ := h.integrable_of_hasCompactSupport (.of_compactSpace _)

lemma integral_pi_cons_rev {n : ℕ} {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : (Fin (n+1) → UnitAddCircle) → E) (hf : Continuous f) :
    (∫ x, f x) = ∫ y : Fin n → UnitAddCircle, ∫ u : UnitAddCircle, f (Fin.cons u y) := by
  rw [integral_pi_cons f (integrable_cont hf)]
  apply integral_integral_swap
  apply integrable_cont
  exact hf.comp (by fun_prop)

lemma integral_cosine_square (a b : ℝ) :
    (∫ u : UnitAddCircle, (a+b*cosine u)^2) = a^2+b^2/2 := by
  have h (u : UnitAddCircle) : (a+b*cosine u)^2 = a^2+2*a*b*cosine u+b^2*cosine u^2 := by ring
  simp_rw [h]
  rw [integral_add, integral_add, integral_const_mul, integral_const_mul,
    integral_cosine, integral_cosine_sq]
  · simp; ring
  all_goals apply integrable_cont; fun_prop

lemma energy_succ (n : ℕ) : energy (n+1) = energy n +
    (1/8)*∫ y : Fin n → UnitAddCircle, (1-binary n y^2)^2 := by
  unfold energy
  rw [integral_pi_cons_rev (fun x : Fin (n+1) → UnitAddCircle ↦ binary (n+1) x^2) (by fun_prop)]
  simp_rw [binary_cons, integral_cosine_square]
  have h (y : Fin n → UnitAddCircle) : binary n y^2+((1-binary n y^2)/2)^2/2 =
      binary n y^2+(1/8)*(1-binary n y^2)^2 := by ring
  simp_rw [h]
  rw [integral_add (integrable_cont (by fun_prop)) (integrable_cont (by fun_prop)), integral_const_mul]

lemma energy_increment (n : ℕ) : energy n+(1-energy n)^2/8 ≤ energy (n+1) := by
  have h0 : (0:ℝ) ≤ ∫ y : Fin n → UnitAddCircle, (energy n-binary n y^2)^2 :=
    integral_nonneg (fun y ↦ sq_nonneg (energy n-binary n y^2))
  have hpoint (y : Fin n → UnitAddCircle) : (energy n-binary n y^2)^2 =
      (1-binary n y^2)^2 + 2*(1-energy n)*binary n y^2 + (energy n^2-1) := by ring
  simp_rw [hpoint] at h0
  rw [integral_add, integral_add, integral_const_mul, integral_const] at h0
  · simp only [probReal_univ, smul_eq_mul, one_mul] at h0
    change 0 ≤ (∫ y : Fin n → UnitAddCircle, (1-binary n y^2)^2) +
      2*(1-energy n)*energy n+(energy n^2-1) at h0
    rw [energy_succ]
    nlinarith
  all_goals apply integrable_cont; fun_prop

open UnitAddTorus

end
end Auxiliary
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Auxiliary
open MeasureTheory Filter Topology Complex
open scoped BigOperators ComplexConjugate ENNReal
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instMeasureSpaceUnitAddCircle_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsAddHaarMeasureUnitAddCircleVolume_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsProbabilityMeasureUnitAddCircleVolume_oAI


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Auxiliary.energy_increment := @_root_.OAI.AsymptoticallyMinimalLittlewood.Auxiliary.energy_increment
