-- Prove2me | solution 1 for OAI.Erdos3.exists_weighted_affine_plateau_site_approximation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:46:15.918273+00:00
-- url     : https://prove2.me/submissions/2706a5e1-5443-4030-ab57-fe9f5dcf877d

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B111

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_map {α R S : Type*} [DecidableEq α] [CommRing R] [CommRing S]
    (φ : R →+* S) (f : Finset α → R) (s : Finset α) :
    φ (booleanCoefficient f s) = booleanCoefficient (fun t => φ (f t)) s := by
  simp only [booleanCoefficient, map_sum, map_mul, map_pow, map_neg, map_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_div {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) (a : ℝ) :
    booleanCoefficient (fun t => f t / a) s = booleanCoefficient f s / a := by
  simp only [booleanCoefficient, ← mul_div_assoc, Finset.sum_div]

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem booleanCoefficient_sub_bound {α : Type*} [DecidableEq α]
    (f g : Finset α → ℝ) (s : Finset α) {H : ℝ}
    (h : ∀ t ∈ s.powerset, |f t-g t| ≤ H) :
    |booleanCoefficient f s-booleanCoefficient g s| ≤ (2 : ℝ)^s.card*H := by
  unfold booleanCoefficient
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ t ∈ s.powerset, |(-1 : ℝ)^(s\t).card*f t-(-1 : ℝ)^(s\t).card*g t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ t ∈ s.powerset, |f t-g t| := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← mul_sub, abs_mul, abs_pow]
      norm_num
    _ ≤ ∑ _t ∈ s.powerset, H := Finset.sum_le_sum h
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped Classical

variable {α β R V : Type*} [Fintype α] [DecidableEq α] [CommRing R]
  [AddCommGroup V] [Module R V]

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RectangularGridCharacter
namespace OAI

section

open scoped BigOperators ComplexConjugate ENNReal Real

open _root_.Finset Function MeasureTheory _root_.Set

namespace Erdos3.CircleFourier

noncomputable section

end
end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open scoped Real NNReal

end Erdos3.CircleFourier

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem cyclicIntegerCharacter_intCast (M : ℕ) [NeZero M] (r z : ℤ) :
    cyclicIntegerCharacter M z (r : ZMod M) =
      character (((r : ℝ) * (z : ℝ) / M : ℝ) : CircleFourier.Circle) := by
  change character (ZMod.toAddCircle ((r : ZMod M) * (z : ZMod M))) = _
  rw [← Int.cast_mul, ZMod.toAddCircle_intCast]
  simp only [Int.cast_mul]

theorem integerGridCharacter_eq (M : ℕ) [NeZero M] (k : Fin M) (z : ℤ) :
    integerGridCharacter M k z =
      character ((((k.val : ℝ) / M) * z : ℝ) : CircleFourier.Circle) := by
  have h := cyclicIntegerCharacter_intCast M (k.val : ℤ) z
  simpa only [integerGridCharacter, gridResidueEquiv, Equiv.coe_fn_mk,
    Int.cast_natCast, div_mul_eq_mul_div] using h

end Erdos3

end

section

namespace Erdos3

open CircleFourier

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open Module
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem circle_coe_fintype_sum {J : Type*} [Fintype J] (f : J → ℝ) :
    ((∑ j, f j : ℝ) : CircleFourier.Circle) = ∑ j, (f j : CircleFourier.Circle) :=
  map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) f Finset.univ

theorem rectangularGridCharacter_eq {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y : J → ℤ) :
    rectangularGridCharacter M k y =
      character ((∑ j, (((k j).val : ℝ) / M) * (y j : ℝ) : ℝ) : CircleFourier.Circle) := by
  simp only [rectangularGridCharacter, integerGridCharacter_eq, circle_coe_fintype_sum, character_fintype_sum]

theorem rectangularGridCharacter_sub {J : Type*} [Fintype J]
    (M : ℕ) [NeZero M] (k : J → Fin M) (y z : J → ℤ) :
    rectangularGridCharacter M k (y - z) =
      rectangularGridCharacter M k y * star (rectangularGridCharacter M k z) := by
  simp only [rectangularGridCharacter_eq, Pi.sub_apply, Int.cast_sub, mul_sub, Finset.sum_sub_distrib]
  rw [AddCircle.coe_sub, sub_eq_add_neg, character_add, character_neg]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.NativeModelingNumerics

end Erdos3.NativeModelingNumerics

end

section

namespace Erdos3

theorem regularizationRadius_spec {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    0 < regularizationRadius L ε ∧ regularizationRadius L ε ≤ 1 ∧
      L*regularizationRadius L ε ≤ ε/2 := by
  have hp : 0 < regularizationRadius L ε := by unfold regularizationRadius; positivity
  refine ⟨hp, min_le_left _ _, ?_⟩
  have hs := (le_div_iff₀ (show 0 < 2*(1+L) by positivity)).mp
    (show regularizationRadius L ε ≤ ε/(2*(1+L)) from min_le_right _ _)
  nlinarith

theorem regularizationRadius_inverse_le_exp {L ε P : ℝ}
    (hL : 0 ≤ L) (hε : 0 < ε) (hP : 0 ≤ P)
    (hLP : L ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    (regularizationRadius L ε)⁻¹ ≤ Real.exp (2*P+2) := by
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using Real.one_le_exp_iff.mpr (by positivity : 0 ≤ 2*P+2)
  · have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      (ε/(2*(1+L)))⁻¹ = 2*(1+L)*ε⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 1*Real.exp (P+1)*Real.exp P := by
        gcongr
        exact one_add_le_exp_succ hP hLP
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem intervalSiteWeight_sum {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : ℝ) (hx : |x| ≤ B) :
    ∑ i, intervalSiteWeight B r i x = 1 := by
  apply regularizedTentPartition_sum _ hr
  obtain ⟨i, hi⟩ := exists_uniformIntervalGrid_approx hB (boxCoverMeshCount_pos B 1 r) x hx
  refine ⟨i, ?_⟩
  have he := boxCoverMeshCount_error (1 : ℝ≥0) hr (B := B)
  simp only [NNReal.coe_one, one_mul] at he
  exact (show dist x (intervalSiteCenter B r i) ≤ 2 * B / boxCoverMeshCount B 1 r from hi).trans he

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {X I : Type*} [PseudoMetricSpace X] [Fintype I]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped NNReal

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

namespace RepresentativeWindow

end RepresentativeWindow
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PMFLipschitzAverage
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {T X : Type*} [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

theorem pmf_integrable_of_norm_le (p : PMF T) (f : T → ℂ) {B : ℝ}
    (hf : ∀ t, ‖f t‖ ≤ B) : Integrable f p.toMeasure :=
  Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable B (ae_of_all _ hf)

theorem pmf_integral_lipschitz [PseudoMetricSpace X]
    (p : PMF T) (F : T → X → ℂ) (L : ℝ≥0) {B : ℝ}
    (hB : ∀ t x, ‖F t x‖ ≤ B) (hL : ∀ t, LipschitzWith L (F t)) :
    LipschitzWith L (fun x => ∫ t, F t x ∂p.toMeasure) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← integral_sub
    (pmf_integrable_of_norm_le p _ (fun t => hB t x))
    (pmf_integrable_of_norm_le p _ (fun t => hB t y))]
  have h := norm_integral_le_of_norm_le_const
    (ae_of_all p.toMeasure (fun t => by
      simpa only [dist_eq_norm] using (hL t).dist_le_mul x y))
  simpa only [probReal_univ, mul_one] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedSupportPlateau
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {J : Type*} [Fintype J]

theorem normalizedSupportPlateau_range (H : ℝ) (x : J → ℝ) :
    0 ≤ normalizedSupportPlateau H x ∧ normalizedSupportPlateau H x ≤ 1 :=
  linearCutoff_range _ _ _

theorem normalizedSupportPlateau_lipschitz (H : ℝ) :
    LipschitzWith 4 (normalizedSupportPlateau (J := J) H) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (linearCutoff_lipschitz H (1 / 4) (by norm_num)).dist_le_mul ‖x‖ ‖y‖
  norm_num only [NNReal.coe_inv, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    one_div, inv_inv] at h
  exact h.trans (mul_le_mul_of_nonneg_left (dist_norm_norm_le x y) (by norm_num))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PlateauFourierMode
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {J : Type*} [Fintype J]

theorem realLinearCharacter_norm (ω x : J → ℝ) : ‖realLinearCharacter ω x‖ = 1 :=
  CircleFourier.norm_character _

theorem realLinearCharacter_lipschitz (ω : J → ℝ) (W : ℝ≥0)
    (hW : ∀ j, |ω j| ≤ W) :
    LipschitzWith (CircleFourier.characterLipConstant * (Fintype.card J * W))
      (realLinearCharacter ω) := by
  have hlin : LipschitzWith (Fintype.card J * W) (fun x : J → ℝ => ∑ j, ω j * x j) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j, |ω j * x j - ω j * y j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : J, (W : ℝ) * dist x y := by
        apply Finset.sum_le_sum
        intro j _
        rw [← mul_sub, abs_mul]
        exact mul_le_mul (hW j) (by simpa only [Real.dist_eq] using dist_le_pi_dist x y j)
          (abs_nonneg _) W.coe_nonneg
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        NNReal.coe_mul, NNReal.coe_natCast]; ring
  have hquot : LipschitzWith 1 (fun x : ℝ => (x : CircleFourier.Circle)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← AddCircle.coe_sub, NNReal.coe_one, one_mul, dist_eq_norm]
    exact QuotientAddGroup.norm_mk_le_norm
  have hc := CircleFourier.character_lipschitz.comp (hquot.comp hlin)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [one_mul, Function.comp_def, realLinearCharacter] using hc.dist_le_mul x y

theorem plateauFourierMode_norm (H : ℝ) (ω x : J → ℝ) : ‖plateauFourierMode H ω x‖ ≤ 1 := by
  rw [plateauFourierMode, norm_mul, realLinearCharacter_norm, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (normalizedSupportPlateau_range H x).1]
  exact (normalizedSupportPlateau_range H x).2

theorem plateauFourierMode_lipschitz (H : ℝ) (ω : J → ℝ) (W : ℝ≥0)
    (hW : ∀ j, |ω j| ≤ W) :
    LipschitzWith (CircleFourier.characterLipConstant * (Fintype.card J * W) + 4)
      (plateauFourierMode H ω) := by
  have hp : LipschitzWith 4 (fun x : J → ℝ => (normalizedSupportPlateau H x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real] using
      (normalizedSupportPlateau_lipschitz (J := J) H).dist_le_mul x y
  have hc := lipschitz_mul_of_bounds (fun x : J → ℝ => (normalizedSupportPlateau H x : ℂ))
      (realLinearCharacter ω) hp (realLinearCharacter_lipschitz ω W hW)
      (Bf := 1) (Bg := 1)
      (fun x => by
        rw [Complex.norm_real, Real.norm_of_nonneg (normalizedSupportPlateau_range H x).1]
        exact (normalizedSupportPlateau_range H x).2)
      (fun x => (realLinearCharacter_norm ω x).le)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [one_mul, plateauFourierMode] using hc.dist_le_mul x y

theorem rationalGridPhase_norm (D : ℕ) [NeZero D] (a : J → ℤ) (r : J → ZMod D) :
    ‖rationalGridPhase D a r‖ = 1 := CircleFourier.norm_character _

theorem rationalGridPhase_intCast (D : ℕ) [NeZero D] (a z : J → ℤ) :
    rationalGridPhase D a (integerGridResidue D z) =
      realLinearCharacter (fun j => (a j : ℝ) / D) (fun j => (z j : ℝ)) := by
  have he : (∑ j, (a j : ZMod D) * (z j : ZMod D)) = ((∑ j, a j * z j : ℤ) : ZMod D) := by
    simp only [Int.cast_sum, Int.cast_mul]
  unfold rationalGridPhase integerGridResidue realLinearCharacter
  rw [he, ZMod.toAddCircle_intCast]
  congr 2
  simp only [Int.cast_sum, Int.cast_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem plateau_grid_character_split (H : ℝ) {K M D : ℕ} [NeZero M] [NeZero D]
    (hK : 0 < K) (k : J → Fin M) (a : J → ℤ) (ω : J → ℝ)
    (hfreq : ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / D + ω j / K)
    (shift z : J → ℤ) :
    (normalizedSupportPlateau H (fun j => ((z j : ℝ) - shift j) / K) : ℂ) *
        (rectangularGridCharacter M k shift * star (rectangularGridCharacter M k z)) =
      rationalGridPhase D a (integerGridResidue D (shift - z)) *
        plateauFourierMode H (fun j => -ω j) (fun j => ((z j : ℝ) - shift j) / K) := by
  have hK0 : (K : ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
  have hphase : (∑ j, ((k j).val : ℝ) / M * ((shift j : ℝ) - z j)) =
      (∑ j, (a j : ℝ) / D * ((shift j : ℝ) - z j)) +
        ∑ j, -ω j * (((z j : ℝ) - shift j) / K) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hfreq j]
    field_simp [hK0]
    ring
  rw [← rectangularGridCharacter_sub, rectangularGridCharacter_eq,
    rationalGridPhase_intCast, plateauFourierMode]
  simp only [realLinearCharacter, Pi.sub_apply, Int.cast_sub]
  rw [hphase, AddCircle.coe_add, CircleFourier.character_add]
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedPlateauMixture
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {T J : Type*} [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable [Fintype J]

theorem rationalGridPhase_sub (D : ℕ) [NeZero D] (a u v : J → ℤ) :
    rationalGridPhase D a (integerGridResidue D (u - v)) =
      rationalGridPhase D a (integerGridResidue D u) *
        star (rationalGridPhase D a (integerGridResidue D v)) := by
  unfold rationalGridPhase integerGridResidue
  simp only [Pi.sub_apply, Int.cast_sub, mul_sub, Finset.sum_sub_distrib, map_sub]
  rw [sub_eq_add_neg, CircleFourier.character_add, CircleFourier.character_neg]

omit [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T] in
theorem plateauModeMixture_integrand_norm (H : ℝ) (D K : ℕ) [NeZero D]
    (a : J → ℤ) (ω : J → ℝ) (shift : T → J → ℤ) (x : J → ℝ) (t : T) :
    ‖rationalGridPhase D a (integerGridResidue D (shift t)) *
      plateauFourierMode H (fun j => -ω j) (x - fun j => (shift t j : ℝ) / K)‖ ≤ 1 := by
  rw [norm_mul, rationalGridPhase_norm, one_mul]
  exact plateauFourierMode_norm _ _ _

omit [Countable T] [MeasurableSingletonClass T] in
theorem plateauModeMixture_norm (p : PMF T) (H : ℝ) (D K : ℕ) [NeZero D]
    (a : J → ℤ) (ω : J → ℝ) (shift : T → J → ℤ) (x : J → ℝ) :
    ‖plateauModeMixture p H D K a ω shift x‖ ≤ 1 := by
  simpa only [plateauModeMixture, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const
      (ae_of_all p.toMeasure (plateauModeMixture_integrand_norm H D K a ω shift x))

theorem plateauModeMixture_lipschitz (p : PMF T) (H : ℝ) (D K : ℕ) [NeZero D]
    (a : J → ℤ) (ω : J → ℝ) (shift : T → J → ℤ) (W : ℝ≥0)
    (hW : ∀ j, |ω j| ≤ W) :
    LipschitzWith (CircleFourier.characterLipConstant * (Fintype.card J * W) + 4)
      (plateauModeMixture p H D K a ω shift) := by
  apply pmf_integral_lipschitz p _ _
    (fun t x => plateauModeMixture_integrand_norm H D K a ω shift x t)
  intro t
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← mul_sub, norm_mul, rationalGridPhase_norm, one_mul]
  have h := (plateauFourierMode_lipschitz H (fun j => -ω j) W
    (fun j => by simpa only [abs_neg] using hW j)).dist_le_mul
      (x - fun j => (shift t j : ℝ) / K) (y - fun j => (shift t j : ℝ) / K)
  have he : (x - fun j => (shift t j : ℝ) / K) -
      (y - fun j => (shift t j : ℝ) / K) = x - y := by abel
  simpa only [dist_eq_norm, he] using h

omit [Countable T] [MeasurableSingletonClass T] in
theorem plateauModeMixture_grid_factor (p : PMF T) (H : ℝ) (D K : ℕ) [NeZero D]
    (a : J → ℤ) (ω : J → ℝ) (shift : T → J → ℤ) (z : J → ℤ) :
    (∫ t, rationalGridPhase D a (integerGridResidue D (shift t - z)) *
      plateauFourierMode H (fun j => -ω j)
        (fun j => ((z j : ℝ) - shift t j) / K) ∂p.toMeasure) =
      star (rationalGridPhase D a (integerGridResidue D z)) *
        plateauModeMixture p H D K a ω shift (fun j => (z j : ℝ) / K) := by
  unfold plateauModeMixture
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    have he : (fun j => ((z j : ℝ) - shift t j) / K) =
        (fun j => (z j : ℝ) / K) - (fun j => (shift t j : ℝ) / K) := by
      funext j
      exact sub_div _ _ _
    dsimp only
    rw [rationalGridPhase_sub, he]
    ring)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable {n K M : ℕ} [NeZero M]
variable (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
variable (offset : B → ℤ)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {B I T : Type*} [Fintype B] [Fintype I] [DecidableEq I]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable {n K M : ℕ} [NeZero M]
variable (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
variable (offset : B → ℤ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBoundedVariablePatchExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {α : Type*} [Fintype α] {κ X : α → Type*}
  (ψ : ∀ a, κ a → X a → ℝ)

variable [DecidableEq α] [∀ a, Fintype (κ a)]

variable [∀ a, PseudoMetricSpace (X a)]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

theorem intervalTensorWeight_nonneg {S : Type*} [Fintype S] (B : ℝ) {r : ℝ} (hr : 0 < r)
    (k : S → Fin (intervalSiteCount B r)) (x : S → ℝ) : 0 ≤ intervalTensorWeight B r k x :=
  Finset.prod_nonneg (fun i _ => (intervalSiteWeight_range B hr (k i) (x i)).1)

theorem intervalTensorWeight_sum {S : Type*} [Fintype S] [DecidableEq S]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : S → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ∑ k : S → Fin (intervalSiteCount B r), intervalTensorWeight B r k x = 1 := by
  unfold intervalTensorWeight
  rw [← Fintype.prod_sum (fun i k => intervalSiteWeight B r k (x i))]
  simp only [intervalSiteWeight_sum hB hr _ (hx _), Finset.prod_const_one]

theorem intervalTensorWeight_near {S : Type*} [Fintype S] {B r : ℝ} (hr : 0 < r)
    (k : S → Fin (intervalSiteCount B r)) (x : S → ℝ) (hx : 0 < intervalTensorWeight B r k x) :
    dist x (fun i => intervalSiteCenter B r (k i)) ≤ 2 * r := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  have hp := productPartitionWeight_pos_coordinate (fun _ : S => intervalSiteWeight B r)
    (fun _ j x => (intervalSiteWeight_range B hr j x).1) k x hx i
  exact (intervalSiteWeight_near B r (k i) (x i) hp).le

theorem intervalTensorApprox_error {S : Type*} [Fintype S] [DecidableEq S]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (F : (S → ℝ) → ℂ) {K : ℝ≥0}
    (hF : LipschitzWith K F) (x : S → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ‖F x - intervalTensorApprox B r F x‖ ≤ 2 * K * r := by
  apply norm_sub_positive_sum_le (fun k => intervalTensorWeight B r k x)
    (fun k => F (fun i => intervalSiteCenter B r (k i))) (F x) _
    (fun k => intervalTensorWeight_nonneg B hr k x) (intervalTensorWeight_sum hB hr x hx)
  intro k hk
  have h := hF.dist_le_mul x (fun i => intervalSiteCenter B r (k i))
  rw [dist_eq_norm] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (intervalTensorWeight_near hr k x hk) K.coe_nonneg).trans_eq (by ring))

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal BigOperators

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GroupedSiteTensor
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {S D : Type*} [Fintype S] [Fintype D]

theorem siteCurry_lipschitz :
    LipschitzWith 1 (fun x : S × D → ℝ => fun s d => x (s, d)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro s
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro d
  exact dist_le_pi_dist x y (s, d)

theorem groupedSiteApprox_eq_interval [DecidableEq S] [DecidableEq D]
    (B r : ℝ) (F : (S → D → ℝ) → ℂ) (x : S → D → ℝ) :
    groupedSiteApprox B r F x =
      intervalTensorApprox B r (fun y : S × D → ℝ => F (fun s d => y (s, d)))
        (fun p => x p.1 p.2) := by
  unfold groupedSiteApprox intervalTensorApprox groupedSiteCoefficient
  apply Finset.sum_congr rfl
  intro k _
  simp only [groupedSiteFactor, vectorIntervalSiteWeight, intervalTensorWeight,
    Complex.ofReal_prod, Fintype.prod_prod_type]
  ring

theorem groupedSiteApprox_error [DecidableEq S] [DecidableEq D]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (F : (S → D → ℝ) → ℂ)
    {K : ℝ≥0} (hF : LipschitzWith K F) (x : S → D → ℝ)
    (hx : ∀ s d, |x s d| ≤ B) :
    ‖F x-groupedSiteApprox B r F x‖ ≤ 2*K*r := by
  rw [groupedSiteApprox_eq_interval]
  exact intervalTensorApprox_error hB hr _
    (by simpa only [mul_one] using hF.comp (siteCurry_lipschitz (S := S) (D := D)))
    (fun p : S × D => x p.1 p.2) (fun p : S × D => hx p.1 p.2)

theorem groupedSiteCoefficient_sum [DecidableEq S] [DecidableEq D]
    (B r : ℝ) (F : (S → D → ℝ) → ℂ)
    {A : ℝ} (hF : ∀ x, ‖F x‖ ≤ A) :
    (∑ k : S × D → Fin (intervalSiteCount B r), ‖groupedSiteCoefficient B r F k‖) ≤
      (intervalSiteCount B r : ℝ)^(Fintype.card S*Fintype.card D)*A := by
  calc
    _ ≤ ∑ _k : S × D → Fin (intervalSiteCount B r), A := Finset.sum_le_sum (fun k _ => hF _)
    _ = _ := by simp [Fintype.card_prod]

omit [Fintype S] in
theorem groupedSiteFactor_bound (B : ℝ) {r : ℝ} (hr : 0 < r)
    (k : S × D → Fin (intervalSiteCount B r)) (s : S) (x : D → ℝ) :
    ‖groupedSiteFactor B r k s x‖ ≤ 1 :=
  vectorIntervalSiteWeight_bound B hr _ _

omit [Fintype S] in
theorem groupedSiteFactor_lipschitz (B : ℝ) {r : ℝ≥0} (hr : 0 < r)
    (k : S × D → Fin (intervalSiteCount B r)) (s : S) :
    LipschitzWith (Fintype.card D*((2*intervalSiteCount B r+1)/r))
      (groupedSiteFactor B r k s) :=
  vectorIntervalSiteWeight_lipschitz B hr _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.VectorSiteBudget
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_grouped_site_approximation {S D : Type*} [Fintype S] [Fintype D]
    [DecidableEq S] [DecidableEq D]
    (F : (S → D → ℝ) → ℂ) (A K : ℝ≥0) (hA : ∀ x, ‖F x‖ ≤ A)
    (hK : LipschitzWith K F) {B ε P : ℝ} (hB : 0 < B) (hε : 0 < ε) (hP : 0 ≤ P)
    (hBP : B ≤ Real.exp P) (hAP : (A : ℝ) ≤ Real.exp P) (hKP : (K : ℝ) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4*P+8) ∧
      ∃ (c : (S × D → Fin n) → ℂ) (f : (S × D → Fin n) → S → (D → ℝ) → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp ((Fintype.card S*Fintype.card D : ℕ)*(4*P+8)+P) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith ⟨Real.exp (Fintype.card D+6*P+12), Real.exp_nonneg _⟩ (f k s)) ∧
        ∀ x : S → D → ℝ, (∀ s d, |x s d| ≤ B) →
          ‖F x-∑ k, c k*∏ s, f k s (x s)‖ ≤ ε := by
  let r := regularizationRadius K ε
  have hs := regularizationRadius_spec K.coe_nonneg hε
  have hr : 0 < r := hs.1
  have hi : r⁻¹ ≤ Real.exp (2*P+2) :=
    regularizationRadius_inverse_le_exp K.coe_nonneg hε hP hKP hεP
  have hP' : 0 ≤ 2*P+2 := by positivity
  have hPP' : P ≤ 2*P+2 := by linarith
  have hB' : B ≤ Real.exp (2*P+2) := hBP.trans (Real.exp_le_exp.mpr hPP')
  have hn : (intervalSiteCount B r : ℝ) ≤ Real.exp (4*P+8) := by
    have hb := intervalSiteCount_le_exp hB.le hr hP' hB' (by simpa only [one_div] using hi)
    have he : 2*(2*P+2)+4 = 4*P+8 := by ring
    simpa only [he] using hb
  have hf : (Fintype.card D : ℝ)*((2*(intervalSiteCount B r : ℝ)+1)/r) ≤
      Real.exp (Fintype.card D+6*P+12) := by
    have hb := intervalSiteLipschitz_le_exp hB.le hr hP' hB' (by simpa only [one_div] using hi)
    have hd : (Fintype.card D : ℝ) ≤ Real.exp (Fintype.card D : ℝ) := by
      linarith [Real.add_one_le_exp (Fintype.card D : ℝ)]
    calc
      _ ≤ Real.exp (Fintype.card D : ℝ)*Real.exp (3*(2*P+2)+6) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨intervalSiteCount B r, hn, groupedSiteCoefficient B r F, groupedSiteFactor B r, ?_,
    (fun k s x => groupedSiteFactor_bound B hr k s x), ?_, ?_⟩
  · apply (groupedSiteCoefficient_sum B r F hA).trans
    calc
      _ ≤ (Real.exp (4*P+8))^(Fintype.card S*Fintype.card D)*Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]
  · intro k s
    have hl := groupedSiteFactor_lipschitz B (r := ⟨r, hr.le⟩) hr k s
    apply hl.weaken
    exact_mod_cast hf
  · intro x hx
    apply (groupedSiteApprox_error hB hr F hK x hx).trans
    have hs' : (K : ℝ)*r ≤ ε/2 := hs.2.2
    nlinarith

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineModeratePlateauModel
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {A J : Type*} [Fintype A] [Fintype J]
variable (D : A → ℕ) [∀ a, NeZero (D a)] (frequency : A → J → ℤ)
variable (coefficient : A → ℂ) (mode : A → (J → ℝ) → ℂ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open CircleFourier

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {B : Type*} [Fintype B] [DecidableEq B]
variable {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
variable (c : B → NormalizedScalarCubeSource Empty)
variable (s : B → Fin n → NormalizedScalarCubeSource I)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B I T : Type*} [Fintype B] [Fintype I] [DecidableEq I]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable {n K M : ℕ} [NeZero M]
variable (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
variable (u : B → Fin n → Option I → ℤ) (v : B → Fin n → Option I → ℕ)
variable (offset : B → ℤ)

theorem weightedAffineModeratePlateauApproximation_split_periods
    (hK : 0 < K) (H : ℝ) (rows : Finset (Finset I)) (shift z : rows → ℤ)
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K) :
    weightedAffineModeratePlateauApproximation c s u v offset K H rows shift z F =
      ((K : ℂ) / M) ^ rows.card * ∑ k ∈ F,
        (∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M rows k) *
          (rationalGridPhase (D k) (a k) (integerGridResidue (D k) (shift - z)) *
            plateauFourierMode H (fun t => -ω k t) (fun t => ((z t : ℝ) - shift t) / K)) := by
  unfold weightedAffineModeratePlateauApproximation weightedAffineModerateGridApproximation
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← plateau_grid_character_split H hK k (a k) (ω k) (hfreq k hk) shift z]
  ring

theorem weightedAffineModeratePlateauMixture_expansion
    (p : PMF T) (hK : 0 < K) (H : ℝ) (rows : Finset (Finset I))
    (shift : T → rows → ℤ) (z : rows → ℤ)
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K) :
    (∫ zeta, weightedAffineModeratePlateauApproximation c s u v offset K H rows (shift zeta) z F ∂p.toMeasure) =
      ((K : ℂ) / M) ^ rows.card * ∑ k ∈ F,
        (∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M rows k) *
          (star (rationalGridPhase (D k) (a k) (integerGridResidue (D k) z)) *
            plateauModeMixture p H (D k) K (a k) (ω k) shift (fun t => (z t : ℝ) / K)) := by
  simp_rw [weightedAffineModeratePlateauApproximation_split_periods c s u v offset hK H rows _ z F D a ω hfreq]
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul, plateauModeMixture_grid_factor]
  · intro k _
    apply Integrable.const_mul
    apply pmf_integrable_of_norm_le p _ (B := 1)
    intro zeta
    rw [norm_mul, rationalGridPhase_norm, one_mul]
    exact plateauFourierMode_norm _ _ _

omit [NeZero M] in
theorem weightedAffinePlateauModeCoefficient_sum_le (rows : Finset (Finset I))
    (F : Finset (rows → Fin M)) (hscale : ((K : ℝ) / M) ^ rows.card ≤ 1) {C : ℝ}
    (hcap : (∑ k, ‖∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M rows k‖) ≤ C) :
    (∑ k : F, ‖weightedAffinePlateauModeCoefficient c s u v offset K M rows k‖) ≤ C := by
  rw [← Finset.sum_subtype F (fun _ => Iff.rfl)
    (fun k => ‖weightedAffinePlateauModeCoefficient c s u v offset K M rows k‖)]
  simp only [weightedAffinePlateauModeCoefficient, norm_mul, norm_pow, norm_div,
    Complex.norm_natCast, ← Finset.mul_sum]
  have hC : 0 ≤ C := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hcap
  apply (mul_le_mul_of_nonneg_left
    ((Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)).trans hcap) (by positivity)).trans
  exact mul_le_of_le_one_left hC hscale

theorem weightedAffinePlateauModeModel_grid_value (p : PMF T) (hK : 0 < K) (H : ℝ)
    (rows : Finset (Finset I)) (F : Finset (rows → Fin M))
    (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K)
    (shift : T → rows → ℤ) (z : rows → ℤ) :
    (∫ zeta, weightedAffineModeratePlateauApproximation c s u v offset K H rows (shift zeta) z F ∂p.toMeasure) =
      weightedAffinePlateauModeModel c s u v offset p H K rows F D a ω shift
        (fun k => integerGridResidue (D k) z) (fun t => (z t : ℝ) / K) := by
  rw [weightedAffineModeratePlateauMixture_expansion c s u v offset p hK H rows shift z F D a ω hfreq]
  let term (k : rows → Fin M) := weightedAffinePlateauModeCoefficient c s u v offset K M rows k *
    (star (rationalGridPhase (D k) (a k) (integerGridResidue (D k) z)) *
      plateauModeMixture p H (D k) K (a k) (ω k) shift (fun t => (z t : ℝ) / K))
  calc
    _ = ∑ k ∈ F, term k := by
      simp only [term, weightedAffinePlateauModeCoefficient, Finset.mul_sum, mul_assoc]
    _ = ∑ k : F, term k := Finset.sum_subtype F (fun _ => Iff.rfl) term
    _ = _ := rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPlateauSiteApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {A : Type*} [Fintype A] {I : A → Type*} [∀ a, Fintype (I a)]

theorem sigma_sum_coefficient_norm_le (w : A → ℂ) (c : ∀ a, I a → ℂ)
    {C B : ℝ} (hB : 0 ≤ B) (hw : (∑ a, ‖w a‖) ≤ C)
    (hc : ∀ a, (∑ i, ‖c a i‖) ≤ B) :
    (∑ p : Σ a, I a, ‖w p.1 * c p.1 p.2‖) ≤ C * B := by
  rw [Fintype.sum_sigma]
  simp only [norm_mul, ← Finset.mul_sum]
  calc
    _ ≤ ∑ a, ‖w a‖ * B :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hc a) (norm_nonneg _))
    _ = (∑ a, ‖w a‖) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ C * B := mul_le_mul_of_nonneg_right hw hB

theorem sigma_sum_approximation_error (w g : A → ℂ) (c v : ∀ a, I a → ℂ)
    {C ε : ℝ} (hε : 0 ≤ ε) (hw : (∑ a, ‖w a‖) ≤ C)
    (he : ∀ a, ‖g a - ∑ i, c a i * v a i‖ ≤ ε) :
    ‖(∑ a, w a * g a) -
      ∑ p : Σ a, I a, (w p.1 * c p.1 p.2) * v p.1 p.2‖ ≤ C * ε := by
  rw [Fintype.sum_sigma]
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a, ‖w a * g a - w a * ∑ i, c a i * v a i‖ := norm_sum_le _ _
    _ ≤ ∑ a, ‖w a‖ * ε := by
      apply Finset.sum_le_sum
      intro a _
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left (he a) (norm_nonneg _)
    _ = (∑ a, ‖w a‖) * ε := (Finset.sum_mul _ _ _).symm
    _ ≤ C * ε := mul_le_mul_of_nonneg_right hw hε

theorem sigma_partition_card_le {S : Type*} [Fintype S] [DecidableEq S]
    (n : A → ℕ) {B : ℝ} (hn : ∀ a, (n a : ℝ) ≤ B) :
    (Fintype.card (Σ a, S → Fin (n a)) : ℝ) ≤ Fintype.card A * B ^ Fintype.card S := by
  simp only [Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin, Nat.cast_sum, Nat.cast_pow]
  calc
    _ ≤ ∑ _a : A, B ^ Fintype.card S := by
      apply Finset.sum_le_sum
      intro a _
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hn a) _
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {T K L S U : Type*} [Fintype T] [Fintype K] [Fintype L] [Fintype S]
variable (c : T → ℂ) (a : K → L → ℂ)
variable (g : T → S → U → ℂ) (f : K → L → S → U → ℂ) (v : S → U)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B I T : Type*} [Fintype B] [Fintype I] [DecidableEq I]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable {n K M : ℕ} [NeZero M]
variable (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
variable (offset : B → ℤ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {α A T : Type*} [Fintype α] [DecidableEq α] [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
theorem selectedBooleanSiteRows_lipschitz (axis : A) (rows : Finset (Finset α)) :
    LipschitzWith ((2 : ℝ≥0) ^ Fintype.card α) (selectedBooleanSiteRows axis rows) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (by positivity)).mpr
  intro t
  change |booleanCoefficient (fun s => x s axis) t - booleanCoefficient (fun s => y s axis) t| ≤ _
  apply (booleanCoefficient_sub_bound _ _ _ (H := dist x y) ?_).trans
  · simp only [NNReal.coe_pow, NNReal.coe_ofNat]
    gcongr
    · norm_num
    · exact Finset.card_le_univ _
  · intro s _
    exact (show |x s axis - y s axis| ≤ dist (x s) (y s) from
      dist_le_pi_dist (x s) (y s) axis).trans (dist_le_pi_dist x y s)

omit [Fintype α] in
theorem rationalBooleanSitePhase_norm (D : ℕ) [NeZero D]
    (rows : Finset (Finset α)) (a : rows → ℤ) (s : Finset α) (v : ZMod D) :
    ‖rationalBooleanSitePhase D rows a s v‖ = 1 := rationalGridPhase_norm _ _ _

theorem rationalBooleanSitePhase_prod (D : ℕ) [NeZero D]
    (rows : Finset (Finset α)) (a : rows → ℤ) (r : Finset α → ZMod D) :
    rationalGridPhase D a (fun t => booleanCoefficient r t) =
      ∏ s, rationalBooleanSitePhase D rows a s (r s) := by
  have hsum (t : rows) : booleanCoefficient r t =
      ∑ s : Finset α, booleanCoefficient (Pi.single s (r s)) t := by
    rw [← booleanCoefficient_sum]
    congr 1
    funext u
    simp [Pi.single_apply]
  unfold rationalBooleanSitePhase rationalGridPhase
  simp_rw [hsum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, map_sum, CircleFourier.character_fintype_sum]

variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

theorem exists_plateau_mode_site_approximation (p : PMF T) (H : ℝ) (D K : ℕ) [NeZero D]
    (axis : A) (rows : Finset (Finset α)) (a : rows → ℤ) (ω : rows → ℝ)
    (shift : T → rows → ℤ) (W : ℝ≥0) (hW : ∀ t, |ω t| ≤ W)
    {R ε P : ℝ} (hR : 0 < R) (hε : 0 < ε) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4 * P + 8) ∧
      ∃ (c : (Finset α × A → Fin n) → ℂ)
        (f : (Finset α × A → Fin n) → Finset α → (A → ℝ) → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp ((Fintype.card (Finset α) * Fintype.card A : ℕ) * (4 * P + 8) + P) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith ⟨Real.exp (Fintype.card A + 6 * P + 12), Real.exp_nonneg _⟩ (f k s)) ∧
        ∀ x : Finset α → A → ℝ, (∀ s d, |x s d| ≤ R) →
          ‖plateauModeMixture p H D K a ω shift (selectedBooleanSiteRows axis rows x) -
            ∑ k, c k * ∏ s, f k s (x s)‖ ≤ ε := by
  apply exists_grouped_site_approximation _ 1
    ((CircleFourier.characterLipConstant * (rows.card * W) + 4) * (2 : ℝ≥0) ^ Fintype.card α)
    (fun x => plateauModeMixture_norm p H D K a ω shift _) _ hR hε hP hRP
    (by simpa only [NNReal.coe_one] using Real.one_le_exp hP) hLP hεP
  have h := (plateauModeMixture_lipschitz p H D K a ω shift W hW).comp
    (selectedBooleanSiteRows_lipschitz axis rows)
  simpa only [Fintype.card_coe, Function.comp_def] using h

theorem exists_residue_plateau_site_approximation (p : PMF T) (H : ℝ) (D K : ℕ) [NeZero D]
    (axis : A) (rows : Finset (Finset α)) (a : rows → ℤ) (ω : rows → ℝ)
    (shift : T → rows → ℤ) (W : ℝ≥0) (hW : ∀ t, |ω t| ≤ W)
    {R ε P : ℝ} (hR : 0 < R) (hε : 0 < ε) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4 * P + 8) ∧
      ∃ (c : (Finset α × A → Fin n) → ℂ)
        (f : (Finset α × A → Fin n) → Finset α → ZMod D → (A → ℝ) → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp ((Fintype.card (Finset α) * Fintype.card A : ℕ) * (4 * P + 8) + P) ∧
        (∀ k s r x, ‖f k s r x‖ ≤ 1) ∧
        (∀ k s r, LipschitzWith ⟨Real.exp (Fintype.card A + 6 * P + 12), Real.exp_nonneg _⟩ (f k s r)) ∧
        ∀ (r : Finset α → ZMod D) (x : Finset α → A → ℝ), (∀ s d, |x s d| ≤ R) →
          ‖star (rationalGridPhase D a (fun t => booleanCoefficient r t)) *
              plateauModeMixture p H D K a ω shift (selectedBooleanSiteRows axis rows x) -
            ∑ k, c k * ∏ s, f k s (r s) (x s)‖ ≤ ε := by
  obtain ⟨n, hn, c, f, hc, hf, hLf, he⟩ :=
    exists_plateau_mode_site_approximation p H D K axis rows a ω shift W hW hR hε hP hRP hεP hLP
  refine ⟨n, hn, c, (fun k s r x => star (rationalBooleanSitePhase D rows a s r) * f k s x),
    hc, ?_, ?_, ?_⟩
  · intro k s r x
    rw [norm_mul, norm_star, rationalBooleanSitePhase_norm, one_mul]
    exact hf k s x
  · intro k s r
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← mul_sub, norm_mul, norm_star, rationalBooleanSitePhase_norm, one_mul]
    simpa only [dist_eq_norm] using (hLf k s).dist_le_mul x y
  · intro r x hx
    have hp : (∏ s, star (rationalBooleanSitePhase D rows a s (r s))) =
        star (rationalGridPhase D a (fun t => booleanCoefficient r t)) := by
      rw [← star_prod, ← rationalBooleanSitePhase_prod]
    have hs : (∑ k, c k * ∏ s, star (rationalBooleanSitePhase D rows a s (r s)) * f k s (x s)) =
        star (rationalGridPhase D a (fun t => booleanCoefficient r t)) *
          ∑ k, c k * ∏ s, f k s (x s) := by
      simp only [Finset.prod_mul_distrib, hp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hs, ← mul_sub, norm_mul, norm_star, rationalGridPhase_norm, one_mul]
    exact he x hx

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {α T : Type*} [Fintype α] [DecidableEq α]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

theorem exists_scalar_residue_plateau_site_approximation
    (p : PMF T) (H : ℝ) (D K : ℕ) [NeZero D]
    (rows : Finset (Finset α)) (a : rows → ℤ) (ω : rows → ℝ)
    (shift : T → rows → ℤ) (W : ℝ≥0) (hW : ∀ t, |ω t| ≤ W)
    {R ε P : ℝ} (hR : 0 < R) (hε : 0 < ε) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4 * P + 8) ∧
      ∃ (c : (Finset α × Unit → Fin n) → ℂ)
        (f : (Finset α × Unit → Fin n) → Finset α → ZMod D → ℝ → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P) ∧
        (∀ k s r x, ‖f k s r x‖ ≤ 1) ∧
        (∀ k s r, LipschitzWith ⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ (f k s r)) ∧
        ∀ (r : Finset α → ZMod D) (x : Finset α → ℝ), (∀ s, |x s| ≤ R) →
          ‖star (rationalGridPhase D a (fun t => booleanCoefficient r t)) *
              plateauModeMixture p H D K a ω shift (fun t => booleanCoefficient x t) -
            ∑ k, c k * ∏ s, f k s (r s) (x s)‖ ≤ ε := by
  obtain ⟨n, hn, c, f, hc, hf, hLf, he⟩ :=
    exists_residue_plateau_site_approximation p H D K () rows a ω shift W hW hR hε hP hRP hεP hLP
  refine ⟨n, hn, c, (fun k s r x => f k s r (fun _ => x)), ?_, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_unit, mul_one] using hc
  · intro k s r x
    exact hf k s r _
  · intro k s r
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Fintype.card_unit, Nat.cast_one, dist_pi_const] using
      (hLf k s r).dist_le_mul (fun _ => x) (fun _ => y)
  · intro r x hx
    exact he r (fun s _ => x s) (fun s _ => hx s)

theorem exists_scalar_integer_plateau_site_approximation
    (p : PMF T) (H : ℝ) (D K : ℕ) [NeZero D]
    (rows : Finset (Finset α)) (a : rows → ℤ) (ω : rows → ℝ)
    (shift : T → rows → ℤ) (W : ℝ≥0) (hW : ∀ t, |ω t| ≤ W)
    {R ε P : ℝ} (hR : 0 < R) (hε : 0 < ε) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4 * P + 8) ∧
      ∃ (c : (Finset α × Unit → Fin n) → ℂ)
        (f : (Finset α × Unit → Fin n) → Finset α → ZMod D → ℝ → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P) ∧
        (∀ k s r x, ‖f k s r x‖ ≤ 1) ∧
        (∀ k s r, LipschitzWith ⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ (f k s r)) ∧
        ∀ y : Finset α → ℤ, (∀ s, |(y s : ℝ) / K| ≤ R) →
          ‖star (rationalGridPhase D a (integerGridResidue D
                (fun t => booleanCoefficient y t))) *
              plateauModeMixture p H D K a ω shift
                (fun t => ((booleanCoefficient y t : ℤ) : ℝ) / K) -
            ∑ k, c k * ∏ s, f k s (y s : ZMod D) ((y s : ℝ) / K)‖ ≤ ε := by
  obtain ⟨n, hn, c, f, hc, hf, hLf, he⟩ := exists_scalar_residue_plateau_site_approximation
    p H D K rows a ω shift W hW hR hε hP hRP hεP hLP
  refine ⟨n, hn, c, f, hc, hf, hLf, ?_⟩
  intro y hy
  have h := he (fun s => (y s : ZMod D)) (fun s => (y s : ℝ) / K) hy
  have hr : (fun t : rows => booleanCoefficient (fun s => (y s : ZMod D)) t) =
      integerGridResidue D (fun t : rows => booleanCoefficient y t) := by
    funext t
    exact (booleanCoefficient_map (Int.castRingHom (ZMod D)) y t).symm
  have hx : (fun t : rows => booleanCoefficient (fun s => (y s : ℝ) / K) t) =
      (fun t : rows => ((booleanCoefficient y t : ℤ) : ℝ) / K) := by
    funext t
    rw [booleanCoefficient_div]
    congr 1
    exact (booleanCoefficient_map (Int.castRingHom ℝ) y t).symm
  rwa [hr, hx] at h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {α A T : Type*} [Fintype α] [DecidableEq α] [Fintype A]

theorem plateauSiteIndex_card_le (n : A → ℕ) {P : ℝ}
    (hn : ∀ m, (n m : ℝ) ≤ Real.exp (4 * P + 8)) :
    (Fintype.card (PlateauSiteIndex α A n) : ℝ) ≤
      Fintype.card A * Real.exp (Fintype.card (Finset α) * (4 * P + 8)) := by
  have hb := sigma_partition_card_le (A := A) (S := Finset α × Unit) n hn
  rw [Fintype.card_prod, Fintype.card_unit, mul_one, ← Real.exp_nat_mul] at hb
  exact hb

variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

theorem exists_integer_plateau_sum_site_approximation
    (p : PMF T) (H : ℝ) (K : ℕ) (rows : Finset (Finset α))
    (D : A → ℕ) [∀ a, NeZero (D a)]
    (a : A → rows → ℤ) (ω : A → rows → ℝ) (shift : T → rows → ℤ)
    (coefficient : A → ℂ) {C : ℝ} (hcap : (∑ m, ‖coefficient m‖) ≤ C)
    (W : ℝ≥0) (hW : ∀ m t, |ω m t| ≤ W)
    {R ε P : ℝ} (hR : 0 < R) (hε : 0 < ε) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P) :
    ∃ n : A → ℕ, (∀ m, (n m : ℝ) ≤ Real.exp (4 * P + 8)) ∧
      (Fintype.card (PlateauSiteIndex α A n) : ℝ) ≤
        Fintype.card A * Real.exp (Fintype.card (Finset α) * (4 * P + 8)) ∧
      ∃ (c : PlateauSiteIndex α A n → ℂ)
        (f : (k : PlateauSiteIndex α A n) → Finset α → ZMod (D k.1) → ℝ → ℂ),
        (∑ k, ‖c k‖) ≤ C * Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P) ∧
        (∀ k s r x, ‖f k s r x‖ ≤ 1) ∧
        (∀ k s r, LipschitzWith ⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ (f k s r)) ∧
        ∀ y : Finset α → ℤ, (∀ s, |(y s : ℝ) / K| ≤ R) →
          ‖finiteResidueModeModel D a coefficient
              (fun m => plateauModeMixture p H (D m) K (a m) (ω m) shift)
              (fun m => integerGridResidue (D m) (fun t => booleanCoefficient y t))
              (fun t => ((booleanCoefficient y t : ℤ) : ℝ) / K) -
            ∑ k, c k * ∏ s, f k s (y s : ZMod (D k.1)) ((y s : ℝ) / K)‖ ≤ C * ε := by
  have hex (m : A) := exists_scalar_integer_plateau_site_approximation
    p H (D m) K rows (a m) (ω m) shift W (hW m) hR hε hP hRP hεP hLP
  choose n hn c f hc hf hLf he using hex
  refine ⟨n, hn, ?_, (fun k => coefficient k.1 * c k.1 k.2), (fun k => f k.1 k.2),
    ?_, ?_, ?_, ?_⟩
  · exact plateauSiteIndex_card_le (α := α) n hn
  · exact sigma_sum_coefficient_norm_le coefficient c (Real.exp_nonneg _) hcap hc
  · intro k s r x
    exact hf k.1 k.2 s r x
  · intro k s r
    exact hLf k.1 k.2 s r
  · intro y hy
    exact sigma_sum_approximation_error coefficient _ c
      (fun m k => ∏ s, f m k s (y s : ZMod (D m)) ((y s : ℝ) / K))
      hε.le hcap (fun m => he m y hy)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B α T : Type*} [Fintype B] [Fintype α] [DecidableEq α]
variable {n K M : ℕ} [NeZero M]
variable (s : B → Fin (n + 1) → NormalizedScalarCubeSource α)

variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B α T : Type*} [Fintype B] [Fintype α] [DecidableEq α]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable {b K M : ℕ} [NeZero M]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineModeratePlateauSite
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B α T : Type*} [Fintype B] [Fintype α] [DecidableEq α]
variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]
variable {b K M : ℕ} [NeZero M]

theorem exists_weighted_affine_plateau_site_approximation
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin b → NormalizedScalarCubeSource α)
    (u : B → Fin b → Option α → ℤ) (v : B → Fin b → Option α → ℕ)
    (offset : B → ℤ) (p : PMF T) (hK : 0 < K) (H : ℝ)
    (rows : Finset (Finset α)) (F : Finset (rows → Fin M))
    (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K)
    (shift : T → rows → ℤ) (hscale : ((K : ℝ) / M) ^ rows.card ≤ 1) {C : ℝ}
    (hcap : (∑ k, ‖∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (fun j i => (u b j i : ℝ)) (v b) (offset b : ℝ) M rows k‖) ≤ C)
    (W : ℝ≥0) (hW : ∀ k ∈ F, ∀ t, |ω k t| ≤ W)
    {R δ P : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hδP : (δ / (C + 1))⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P) :
    ∃ n : F → ℕ, (∀ k, (n k : ℝ) ≤ Real.exp (4 * P + 8)) ∧
      (Fintype.card (PlateauSiteIndex α F n) : ℝ) ≤
        F.card * Real.exp (Fintype.card (Finset α) * (4 * P + 8)) ∧
      ∃ (β : PlateauSiteIndex α F n → ℂ)
        (f : (k : PlateauSiteIndex α F n) → Finset α → ZMod (D k.1) → ℝ → ℂ),
        (∑ k, ‖β k‖) ≤ C * Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P) ∧
        (∀ k u r x, ‖f k u r x‖ ≤ 1) ∧
        (∀ k u r, LipschitzWith ⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ (f k u r)) ∧
        ∀ y : Finset α → ℤ, (∀ u, |(y u : ℝ) / K| ≤ R) →
          ‖(∫ zeta, weightedAffineModeratePlateauApproximation c s u v offset K H rows (shift zeta)
                (fun t => booleanCoefficient y t) F ∂p.toMeasure) -
            ∑ k, β k * ∏ u, f k u (y u : ZMod (D k.1)) ((y u : ℝ) / K)‖ ≤ δ := by
  have hC : 0 ≤ C := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hcap
  have htol : 0 < δ / (C + 1) := div_pos hδ (by positivity)
  obtain ⟨n, hn, hcard, β, f, hβ, hf, hLf, he⟩ :=
    exists_integer_plateau_sum_site_approximation p H K rows (fun k : F => D k)
      (fun k => a k) (fun k => ω k) shift
      (fun k => weightedAffinePlateauModeCoefficient c s u v offset K M rows k)
      (weightedAffinePlateauModeCoefficient_sum_le c s u v offset rows F hscale hcap)
      W (fun k => hW k k.property) hR htol hP hRP hδP hLP
  refine ⟨n, hn, ?_, β, f, hβ, hf, hLf, ?_⟩
  · simpa only [Fintype.card_coe] using hcard
  · intro y hy
    rw [weightedAffinePlateauModeModel_grid_value c s u v offset p hK H rows F D a ω hfreq shift]
    apply (he y hy).trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < C + 1)).mpr
    nlinarith

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.exists_weighted_affine_plateau_site_approximation.{u_1, u_2, u_3} := @OAI.Erdos3.exists_weighted_affine_plateau_site_approximation.{u_1, u_2, u_3}
