-- Prove2me | solution 1 for OAI.Erdos3.physicalL1Source_error_le_exp_of_precision_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:12:49.12298+00:00
-- url     : https://prove2.me/submissions/3eff3261-2ebb-4ca1-8bb9-a71b3574b6e8

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B162

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedSmoothSelectedMarginal
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem smoothProbabilityProfile_inner_lower (x : ℝ) (hx : |x| ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ smoothProbabilityProfile x := by
  have hx' : probabilityProfileBump x = 1 := probabilityProfileBump.one_of_mem_closedBall
    (by simpa [probabilityProfileBump, Real.dist_eq] using hx)
  have hi := probabilityProfileBump.integral_le_measure_closedBall volume
  norm_num [probabilityProfileBump] at hi
  change (∫ y, probabilityProfileBump y) ≤ 3 / 2 at hi
  change (1 / 2 : ℝ) ≤ probabilityProfileBump x / ∫ y, probabilityProfileBump y
  rw [hx']
  apply (le_div_iff₀ probabilityProfileBump.integral_pos).mpr
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientSquareSpatialBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators

theorem referenceErrorVolumeFactor_exp_bound (q : ℕ) (X : Type*) [Fintype X]
    {P D W L : ℝ} (hP : 0 ≤ P) (hq : ((q + 1 : ℕ) : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L) :
    (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
        (((1 + W) / L) ^ q) ^ Fintype.card X ≤ Real.exp (coefficientErrorVolumeLog P) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hq' : (q : ℝ) + 1 ≤ P := by simpa only [Nat.cast_add, Nat.cast_one] using hq
  have hcount : (Fintype.card (Option (Fin q) × X) : ℝ) ≤ P ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact (mul_le_mul hq' hX (Nat.cast_nonneg _) hP).trans_eq (pow_two P).symm
  have hprofile0 := smoothProbabilityProfile_pos_zero
  have hprofile : 30 / smoothProbabilityProfile 0 ≤ Real.exp 60 := by
    have hi := smoothProbabilityProfile_inner_lower 0 (by norm_num)
    apply le_trans (show 30 / smoothProbabilityProfile 0 ≤ 60 from
      (div_le_iff₀ hprofile0).mpr (by linarith))
    linarith [Real.add_one_le_exp (60 : ℝ)]
  have hprofilePower := pow_le_exp_mul_of_le_exp (by positivity) hprofile
    (by norm_num : (0 : ℝ) ≤ 60) _ hcount
  have hratio0 : 0 ≤ (1 + W) / L := by positivity
  have hratio : (1 + W) / L ≤ Real.exp (P + 1) := by
    apply (show (1 + W) / L ≤ 1 + D from (div_le_iff₀ hL0).mpr (by nlinarith)).trans
    exact one_add_le_exp_succ hP hD
  have hqPower := pow_le_exp_mul_of_le_exp hratio0 hratio (by positivity : 0 ≤ P + 1)
    q (by linarith : (q : ℝ) ≤ P)
  have hXPower := pow_le_exp_mul_of_le_exp (pow_nonneg hratio0 q) hqPower
    (by positivity : 0 ≤ P * (P + 1)) _ hX
  calc
    _ ≤ Real.exp (P ^ 2 * 60) * Real.exp (P * (P * (P + 1))) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; unfold coefficientErrorVolumeLog; ring

theorem coefficientErrorSpatialFactor_exp_bound {G : Type*} [Fintype G] (q : ℕ)
    (X : Type*) [Fintype X] (selection : Fin q ↪ G) {M period : ℕ} {P D W L : ℝ}
    (hP : 0 ≤ P) (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp P)
    (hperiod : (period : ℝ) ≤ Real.exp (P ^ 2))
    (hq : ((q + 1 : ℕ) : ℝ) ≤ P) (hG : (Fintype.card G : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L) :
    let Cψ := ((period : ℝ) ^ Fintype.card (Unit ⊕ Fin q) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let Vsp := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
      (((1 + W) / L) ^ q) ^ Fintype.card X
    0 ≤ Cψ * Vsp ∧ Cψ * Vsp ≤ Real.exp (coefficientErrorSpatialLog P) := by
  intro Cψ Vsp
  have hj : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ P := by
    simpa [Nat.add_comm] using hq
  have hc := anisotropicSpatialDensityCap_exp_bound selection hP hM hMP hj hG
  have hc0 := anisotropicSpatialDensityCap_nonneg selection (by positivity : 0 ≤ 1 / (M : ℝ))
  have hh : (period : ℝ) ^ Fintype.card (Unit ⊕ Fin q) ≤ Real.exp (P ^ 3) :=
    (pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _) hperiod (sq_nonneg P) _ hj).trans_eq
      (congrArg Real.exp (by ring))
  have hb : (period : ℝ) ^ Fintype.card (Unit ⊕ Fin q) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ)) ≤
      Real.exp (P ^ 3 + anisotropicSpatialCapLog P) := by
    calc
      _ ≤ Real.exp (P ^ 3) * Real.exp (anisotropicSpatialCapLog P) := by gcongr
      _ = _ := (Real.exp_add _ _).symm
  have hcapLog := anisotropicSpatialCapLog_nonneg hP
  have hψ : Cψ ≤ Real.exp (P * (P ^ 3 + anisotropicSpatialCapLog P)) :=
    pow_le_exp_mul_of_le_exp (by positivity) hb (by positivity) _ hX
  have hvol : Vsp ≤ Real.exp (coefficientErrorVolumeLog P) :=
    referenceErrorVolumeFactor_exp_bound q X hP hq hX hL hW hD hWL
  have hprofile0 := smoothProbabilityProfile_pos_zero
  refine ⟨by dsimp [Cψ, Vsp]; positivity, ?_⟩
  calc
    _ ≤ Real.exp (P * (P ^ 3 + anisotropicSpatialCapLog P)) *
        Real.exp (coefficientErrorVolumeLog P) := by gcongr
    _ = _ := by rw [← Real.exp_add]; rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalL1SourceAccuracy
namespace OAI

section

namespace Erdos3

theorem l1SourceAccuracy_pos (target spatialCap spatialVolume : ℝ) :
    0 < l1SourceAccuracy target spatialCap spatialVolume := Real.exp_pos _

theorem l1Source_error_le_exp_of_joint_bound
    {target budget Cψ factor window E δ η ε εtrunc : ℝ}
    (hC0 : 0 ≤ Cψ) (hf0 : 0 ≤ factor) (hw0 : 0 ≤ window)
    (hf : Cψ * factor ≤ Real.exp budget) (hw : Cψ * window ≤ Real.exp budget)
    (hE : E ≤ l1SourceAccuracy target budget 0)
    (hδ : δ ≤ l1SourceAccuracy target budget 0)
    (hη : η ≤ l1SourceAccuracy target budget 0)
    (hε : ε ≤ l1SourceAccuracy target budget 0)
    (ht : εtrunc ≤ l1SourceAccuracy target budget 0) :
    Cψ * (factor * (E + 2 * δ + (2 * η + ε)) + window * εtrunc) ≤ Real.exp (-target) := by
  let e := l1SourceAccuracy target budget 0
  have he : 0 ≤ e := (l1SourceAccuracy_pos _ _ _).le
  have hsum : E + 2 * δ + (2 * η + ε) ≤ 6 * e := by dsimp only [e]; linarith
  have hfirst : (Cψ * factor) * (E + 2 * δ + (2 * η + ε)) ≤ Real.exp budget * (6 * e) :=
    (mul_le_mul_of_nonneg_left hsum (mul_nonneg hC0 hf0)).trans
      (mul_le_mul_of_nonneg_right hf (by positivity))
  have hsecond : (Cψ * window) * εtrunc ≤ Real.exp budget * e :=
    (mul_le_mul_of_nonneg_left ht (mul_nonneg hC0 hw0)).trans (mul_le_mul_of_nonneg_right hw he)
  have h7 : (7 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  calc
    _ ≤ 7 * Real.exp budget * e := by nlinarith only [hfirst, hsecond]
    _ ≤ Real.exp 8 * Real.exp budget * e := by gcongr
    _ = _ := by
      dsimp only [e, l1SourceAccuracy]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators

theorem physicalWindowFactor_le_referenceFactor (dim : ℕ) (X : Type*) [Fintype X]
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L) :
    (9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X ≤
    (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X := by
  have hc : Fintype.card (X × (Unit ⊕ Fin dim)) = Fintype.card (Option (Fin dim) × X) := by
    simp [Nat.add_comm, Nat.mul_comm]
  rw [hc]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9)
  apply (le_div_iff₀ smoothProbabilityProfile_pos_zero).mpr
  linarith [(smoothProbabilityProfile_range 0).2]

theorem physicalL1Source_error_le_exp {G : Type*} [Fintype G] (dim : ℕ)
    (X : Type*) [Fintype X] (selection : Fin dim ↪ G) {M period : ℕ} {P D W L target : ℝ}
    (hP : 0 ≤ P) (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp P)
    (hperiod : (period : ℝ) ≤ Real.exp (P ^ 2))
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ P) (hG : (Fintype.card G : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L)
    {E δ η ε εtrunc : ℝ}
    (hE : E ≤ l1SourceAccuracy target (coefficientErrorSpatialLog P) 0)
    (hδ : δ ≤ l1SourceAccuracy target (coefficientErrorSpatialLog P) 0)
    (hη : η ≤ l1SourceAccuracy target (coefficientErrorSpatialLog P) 0)
    (hε : ε ≤ l1SourceAccuracy target (coefficientErrorSpatialLog P) 0)
    (ht : εtrunc ≤ l1SourceAccuracy target (coefficientErrorSpatialLog P) 0) :
    let Cψ := ((period : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    let window := (9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    Cψ * (factor * (E + 2 * δ + (2 * η + ε)) + window * εtrunc) ≤ Real.exp (-target) := by
  intro Cψ factor window
  have hC : 0 ≤ Cψ := pow_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (anisotropicSpatialDensityCap_nonneg selection (one_div_nonneg.mpr (Nat.cast_nonneg _)))) _
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hratio : 0 ≤ (1 + W) / L := div_nonneg (by linarith) hL0.le
  have hf0 : 0 ≤ factor := mul_nonneg (pow_nonneg (div_nonneg (by norm_num)
    smoothProbabilityProfile_pos_zero.le) _) (pow_nonneg (pow_nonneg hratio _) _)
  have hw0 : 0 ≤ window := mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (pow_nonneg hratio _) _)
  have hf := (coefficientErrorSpatialFactor_exp_bound dim X selection hP hM hMP hperiod
    hdim hG hX hL hW hD hWL).2
  have hw : Cψ * window ≤ Real.exp (coefficientErrorSpatialLog P) :=
    (mul_le_mul_of_nonneg_left (physicalWindowFactor_le_referenceFactor dim X hW hL0) hC).trans hf
  exact l1Source_error_le_exp_of_joint_bound hC hf0 hw0 hf hw hE hδ hη hε ht

theorem physicalL1Source_error_le_exp_of_precision_s2_oai {G : Type*} [Fintype G] (dim : ℕ)
    (X : Type*) [Fintype X] (selection : Fin dim ↪ G) {M period : ℕ} {P D W L target precision : ℝ}
    (hP : 0 ≤ P) (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp P)
    (hperiod : (period : ℝ) ≤ Real.exp (P ^ 2))
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ P) (hG : (Fintype.card G : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) (hL : 1 ≤ L) (hW : 0 ≤ W)
    (hD : D ≤ Real.exp P) (hWL : W ≤ D * L)
    (hprecision : target + coefficientErrorSpatialLog P + 8 ≤ precision)
    {η ε εtrunc : ℝ}
    (hη : η ≤ Real.exp (-precision)) (hε : ε ≤ Real.exp (-precision))
    (ht : εtrunc ≤ Real.exp (-precision)) :
    let Cψ := ((period : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    let window := (9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    Cψ * (factor * (Real.exp (-precision) + 2 * Real.exp (-precision) + (2 * η + ε)) +
      window * εtrunc) ≤ Real.exp (-target) := by
  have ha : Real.exp (-precision) ≤ l1SourceAccuracy target (coefficientErrorSpatialLog P) 0 := by
    unfold l1SourceAccuracy
    apply Real.exp_le_exp.mpr
    linarith
  exact physicalL1Source_error_le_exp dim X selection hP hM hMP hperiod hdim hG hX hL hW hD hWL
    ha ha (hη.trans ha) (hε.trans ha) (ht.trans ha)

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.physicalL1Source_error_le_exp_of_precision_s2_oai.{u_1, u_2} := @OAI.Erdos3.physicalL1Source_error_le_exp_of_precision_s2_oai.{u_1, u_2}
