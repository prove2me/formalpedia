-- Prove2me | solution 2 for OAI.GrahamSpherical.full_main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T10:21:59.78326+00:00
-- url     : https://prove2.me/submissions/136eab47-b5d7-4afe-a19f-be6d6c2eaa19

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SphericalRamsey/Main.lean:L21-L27
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.GrahamSpherical.full_main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_GrahamSpherical_full_main) verbatim and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_GrahamSpherical
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_Model
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_MonochromaticObstruction
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_BasisDerivation
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_AlgebraicExtension
import Theorems.Thm_OAI_GrahamSpherical_exists_real_derivation
import Theorems.Thm_OAI_GrahamSpherical_rounding_obstruction
import Theorems.Thm_OAI_GrahamSpherical_weighted_copy_derivation_energy

-- ---- from OAI.Combinatorics.SphericalRamsey.Ramsey ----
namespace OAI

namespace GrahamSpherical

/-- Fixed fifty-color avoidance in every positive dimension contradicts the
ordinary Ramsey quantifier, without assuming any copy exists. -/
theorem not_euclideanRamsey_of_fifty_colorings
    (havoid : ∀ n : ℕ, 0 < n →
      ∃ color : Point n → Fin 50, AvoidsCopy witness color) :
    ¬ EuclideanRamsey witness := by
  intro hRamsey
  obtain ⟨n, hn, hall⟩ := hRamsey 50 (by decide)
  obtain ⟨color, hc⟩ := havoid n hn
  exact hc (hall color)

/-- The geometric and coloring properties jointly imply the spherical
non-Ramsey conclusion. -/
theorem assemble_full_result
    (hcard : witness.ncard = 12)
    (hsphere : witness ⊆ Metric.sphere (0 : Point 2) 1)
    (havoid : ∀ n : ℕ, 0 < n →
      ∃ color : Point n → Fin 50, AvoidsCopy witness color) :
    Specification.FullAuthoredResult :=
  ⟨hcard, hsphere, havoid, not_euclideanRamsey_of_fifty_colorings havoid⟩

end GrahamSpherical

end OAI

-- ---- from OAI.Combinatorics.SphericalRamsey.MonochromaticObstruction ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace GrahamSpherical

theorem energyColor_eq_implies_residue_eq {n : ℕ} (e : Point n → ℝ)
    (x y : Point n) (h : energyColor e x = energyColor e y) :
    (Int.floor (3 * e x)) % 50 = (Int.floor (3 * e y)) % 50 := by
  have he := congrArg Fin.val h
  change ((Int.floor (3 * e x)) % 50).toNat =
    ((Int.floor (3 * e y)) % 50).toNat at he
  have hx := Int.emod_nonneg (Int.floor (3 * e x)) (by norm_num : (50 : ℤ) ≠ 0)
  have hy := Int.emod_nonneg (Int.floor (3 * e y)) (by norm_num : (50 : ℤ) ≠ 0)
  omega

/-- Every copy here is an actual isometry of the literal witness subtype.
The energy identity is an explicit intermediate premise, discharged separately. -/
theorem energyColor_avoids_of_invariant {n : ℕ} (e : Point n → ℝ)
    (hinvariant : ∀ (f : witness → Point n), Isometry f →
      ∑ i : Label, (weight i : ℝ) * e (f ⟨vertex i, ⟨i, rfl⟩⟩) = 8) :
    AvoidsCopy witness (energyColor e) := by
  rintro ⟨f, hf, c, hc⟩
  have hi := hinvariant f hf
  obtain ⟨i, j, hij⟩ := rounding_obstruction
    (fun i : Label => e (f ⟨vertex i, ⟨i, rfl⟩⟩)) (by
      simpa [weight] using hi)
  apply hij
  apply energyColor_eq_implies_residue_eq e
  exact (hc ⟨vertex i, ⟨i, rfl⟩⟩).trans (hc ⟨vertex j, ⟨j, rfl⟩⟩).symm

end GrahamSpherical

end

end OAI

-- ---- from OAI.Combinatorics.SphericalRamsey.CopyInvariant ----
namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace GrahamSpherical

theorem derivationColor_avoids {n : ℕ}
    (D : Derivation ℤ ℝ ℝ)
    (hD : D parameter = (1 + parameter ^ 2) / 2) :
    AvoidsCopy witness (energyColor (derivationEnergy (n := n) D)) :=
  energyColor_avoids_of_invariant _ (weighted_copy_derivation_energy D hD)

end GrahamSpherical

end

end OAI

-- ---- from OAI.Combinatorics.SphericalRamsey.Parameter ----
namespace OAI

noncomputable section

namespace GrahamSpherical

/-- The native series includes the additional factorial-zero term. -/
theorem parameter_add_tenth :
    (1 : ℝ) / 10 + parameter = liouvilleNumber 10 := by
  simpa [LiouvilleNumber.partialSum, LiouvilleNumber.remainder, parameter] using
    (LiouvilleNumber.partialSum_add_remainder (m := (10 : ℝ)) (by norm_num) 0)

/-- Transcendence of the factorial-series parameter, over the rational field. -/
theorem parameter_transcendental : Transcendental ℚ parameter := by
  intro hp
  have hrat : IsAlgebraic ℚ ((1 : ℝ) / 10) := by
    simpa using (isAlgebraic_ratCast ℚ (1 / 10 : ℚ) :
      IsAlgebraic ℚ ((1 / 10 : ℚ) : ℝ))
  have hsum : IsAlgebraic ℚ (liouvilleNumber 10) := by
    rw [← parameter_add_tenth]
    exact hrat.add hp
  have hint : IsAlgebraic ℤ (liouvilleNumber 10) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr hsum
  exact (transcendental_liouvilleNumber (m := 10) (by norm_num)) hint

/-- The strict rational bounds stated for the literal factorial series. -/
theorem parameter_bounds :
    (11 : ℝ) / 100 < parameter ∧ parameter < 12 / 100 := by
  have hsplit := LiouvilleNumber.partialSum_add_remainder
    (m := (10 : ℝ)) (by norm_num) 2
  have hpos := LiouvilleNumber.remainder_pos (m := (10 : ℝ)) (by norm_num) 2
  have hupp := LiouvilleNumber.remainder_lt (m := (10 : ℝ)) 2 (by norm_num)
  norm_num [LiouvilleNumber.partialSum, Finset.sum_range_succ, Nat.factorial] at hsplit hupp
  constructor <;> linarith [parameter_add_tenth]

end GrahamSpherical

end

end OAI

-- ---- from OAI.Combinatorics.SphericalRamsey.WitnessScalars ----
namespace OAI

noncomputable section
namespace GrahamSpherical

theorem parameter_den_pos : 0 < 1 + parameter ^ 2 := by positivity

theorem u_sq_add_v_sq : u ^ 2 + v ^ 2 = 1 := by
  unfold u v
  field_simp [ne_of_gt parameter_den_pos]
  ring

theorem v_pos : 0 < v := by
  have ht : 0 < parameter := by linarith [parameter_bounds.1]
  exact div_pos (mul_pos (by norm_num) ht) parameter_den_pos

theorem v_lt_u : v < u := by
  apply (div_lt_div_iff_of_pos_right parameter_den_pos).2
  have ht := parameter_bounds
  have hprod : 0 ≤ (12 / 100 - parameter) * (12 / 100 + parameter) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem u_lt_one : u < 1 := by
  change (1 - parameter ^ 2) / (1 + parameter ^ 2) < 1
  apply (div_lt_one parameter_den_pos).2
  have ht : 0 < parameter := by linarith [parameter_bounds.1]
  nlinarith [sq_pos_of_pos ht]

theorem u_pos : 0 < u := lt_trans v_pos v_lt_u

end GrahamSpherical

end

end OAI

-- ---- from OAI.Combinatorics.SphericalRamsey.WitnessCoordinates ----
namespace OAI

noncomputable section
namespace GrahamSpherical

theorem vertex_injective : Function.Injective vertex := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h0 := congrArg (fun x : Point 2 => x 0) h
  have h1 := congrArg (fun x : Point 2 => x 1) h
  have hp := v_pos
  have hpu := u_pos
  have hlt := v_lt_u
  have hu := u_lt_one
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals norm_num [vertex, coordinates, squareCoordinate, Fin.ext_iff] at h0
  all_goals norm_num [vertex, coordinates, squareCoordinate, Fin.ext_iff] at h1
  all_goals first | rfl | linarith

theorem vertex_norm (i : Label) : ‖vertex i‖ = 1 := by
  have hs : ‖vertex i‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rcases i with ⟨a,b⟩
    fin_cases a <;> fin_cases b <;>
      simp [vertex, coordinates, squareCoordinate, Fin.ext_iff, Fin.sum_univ_two, u_sq_add_v_sq,
        add_comm (v ^ 2) (u ^ 2)]
  nlinarith [norm_nonneg (vertex i)]

theorem witness_subset_sphere : witness ⊆ Metric.sphere (0 : Point 2) 1 := by
  rintro x ⟨i, rfl⟩
  simpa [Metric.mem_sphere, dist_zero_right] using vertex_norm i

theorem witness_ncard : witness.ncard = 12 := by
  rw [witness, Set.ncard_range_of_injective vertex_injective]
  norm_num [Label]

end GrahamSpherical

end

end OAI

-- ---- from OAI.Combinatorics.SphericalRamsey.Main ----
namespace OAI

noncomputable section
namespace GrahamSpherical

/-- A single actual real derivation defines avoiding colorings in all dimensions. -/
theorem exists_common_derivation_colorings :
    ∃ D : Derivation ℤ ℝ ℝ,
      D parameter = (1 + parameter ^ 2) / 2 ∧
      ∀ n : ℕ, AvoidsCopy witness (energyColor (derivationEnergy (n := n) D)) := by
  obtain ⟨D, hD⟩ := exists_real_derivation parameter
    ((1 + parameter ^ 2) / 2) parameter_transcendental
  exact ⟨D, hD, fun _ => derivationColor_avoids D hD⟩

/-- The literal twelve-point spherical witness defeats fifty colors in every
positive dimension, hence is not Euclidean Ramsey. No auxiliary premise remains. -/
theorem full_main : Specification.FullAuthoredResult := by
  obtain ⟨D, _hD, hcolors⟩ := exists_common_derivation_colorings
  apply assemble_full_result witness_ncard witness_subset_sphere
  intro n _hn
  exact ⟨energyColor (derivationEnergy (n := n) D), hcolors n⟩

end GrahamSpherical

end

end OAI

-- ---- mission target ----
open OAI OAI.GrahamSpherical

namespace OAI
namespace GrahamSpherical
theorem _root_.solution : Specification.FullAuthoredResult := by
  first
    | exact OAI.GrahamSpherical.full_main
    | (apply OAI.GrahamSpherical.full_main <;> assumption)
    | (intros; apply OAI.GrahamSpherical.full_main <;> assumption)
end GrahamSpherical
end OAI
