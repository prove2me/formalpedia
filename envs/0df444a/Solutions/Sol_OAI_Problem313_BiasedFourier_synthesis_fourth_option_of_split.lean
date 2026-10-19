-- Prove2me | solution 1 for OAI.Problem313.BiasedFourier.synthesis_fourth_option_of_split
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:31:24.20906+00:00
-- url     : https://prove2.me/submissions/5ac375ef-e589-4f27-90c1-75c0ebb3d879

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/FourierHypercontractive.lean:L35-L83
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.BiasedFourier.synthesis_fourth_option_of_split. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype
import Definitions.Def_OAI_Combinatorics_SharpThreshold_ProjectionIdentities
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierProjection
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOptionExpectation
import Theorems.Thm_OAI_Problem313_biased_two_point_fourth_moment
import Theorems.Thm_OAI_Problem313_weighted_fourth_moment_add_sq

-- ---- from OAI.Combinatorics.SharpThreshold.FourierOption ----
namespace OAI

universe u

noncomputable section

open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι]

theorem sum_option_finset (F : Finset (Option ι) → ℝ) :
    (∑ S, F S) =
      (∑ S : Finset ι, F (S.map Function.Embedding.some)) +
      ∑ S : Finset ι, F (Finset.insertNone S) := by
  classical
  rw [← optionFinsetEquiv.symm.sum_comp F]
  simp [Fintype.sum_sum_type, optionFinsetEquiv]

/-- A noise-weighted Fourier polynomial separates into its two first-coordinate pieces. -/
theorem synthesis_option (p ρ : ℝ) (c : Finset (Option ι) → ℝ)
    (x : Option ι → Bool) :
    (∑ S, ρ ^ S.card * c S * char p S x) =
      (∑ S : Finset ι, ρ ^ S.card * c (S.map Function.Embedding.some) *
        char p S (fun i => x (some i))) +
      ρ * chi p (x none) *
        ∑ S : Finset ι, ρ ^ S.card * c (Finset.insertNone S) *
          char p S (fun i => x (some i)) := by
  classical
  rw [sum_option_finset]
  simp only [Finset.card_map, char_map_some, Finset.card_insertNone, char_insertNone,
    pow_succ]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem coefficient_energy_option (c : Finset (Option ι) → ℝ) :
    (∑ S, c S ^ 2) =
      (∑ S : Finset ι, c (S.map Function.Embedding.some) ^ 2) +
        ∑ S : Finset ι, c (Finset.insertNone S) ^ 2 :=
  sum_option_finset _

end Problem313.BiasedFourier

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.FourierHypercontractive ----
namespace OAI

universe u

noncomputable section

namespace Problem313.BiasedFourier

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- The scalar hypercontractive estimate in normalized character notation. -/
theorem scalar_synthesis_fourth {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (a b : ℝ) :
    (1 - p) * (a + (Real.sqrt (p * (1-p)) / 4) * chi p false * b) ^ 4 +
      p * (a + (Real.sqrt (p * (1-p)) / 4) * chi p true * b) ^ 4 ≤
      (a ^ 2 + b ^ 2) ^ 2 := by
  have hs : Real.sqrt (p * (1 - p)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (mul_pos hp (sub_pos.mpr hp1)))
  have hfalse : (Real.sqrt (p * (1-p)) / 4) * chi p false = -p / 4 := by
    rw [chi_false]
    field_simp
  have htrue : (Real.sqrt (p * (1-p)) / 4) * chi p true = (1-p) / 4 := by
    rw [chi_true]
    field_simp
  rw [hfalse, htrue]
  convert Problem313.biased_two_point_fourth_moment p a b hp.le hp1.le using 1; ring

/-- Tensorization step for an additional Boolean coordinate, in spectral form. -/
theorem synthesis_fourth_option_of_split {ι : Type u} [Fintype ι]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hsplit : ∀ g : (Option ι → Bool) → ℝ,
      (∑ x, weight p x * g x) =
        (1-p) * (∑ y : ι → Bool, weight p y * g (fun t => Option.elim t false y)) +
        p * (∑ y : ι → Bool, weight p y * g (fun t => Option.elim t true y)))
    (ih : ∀ c : Finset ι → ℝ,
      (∑ x, weight p x * (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card *
        c S * char p S x) ^ 4) ≤ (∑ S, c S ^ 2) ^ 2)
    (c : Finset (Option ι) → ℝ) :
    (∑ x, weight p x * (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card *
      c S * char p S x) ^ 4) ≤ (∑ S, c S ^ 2) ^ 2 := by
  classical
  let ρ := Real.sqrt (p*(1-p))/4
  let c₀ : Finset ι → ℝ := fun S => c (S.map Function.Embedding.some)
  let c₁ : Finset ι → ℝ := fun S => c (Finset.insertNone S)
  let A : (ι → Bool) → ℝ := fun x => ∑ S, ρ ^ S.card * c₀ S * char p S x
  let B : (ι → Bool) → ℝ := fun x => ∑ S, ρ ^ S.card * c₁ S * char p S x
  have hw : ∀ x : ι → Bool, 0 ≤ weight p x := by
    intro x
    apply Finset.prod_nonneg
    intro i hi
    cases x i <;> simp [scalarWeight] <;> linarith
  have hA : (∑ x, weight p x * (A x) ^ 4) ≤ (∑ S, c₀ S ^ 2) ^ 2 := ih c₀
  have hB : (∑ x, weight p x * (B x) ^ 4) ≤ (∑ S, c₁ S ^ 2) ^ 2 := ih c₁
  have hbound := Problem313.weighted_fourth_moment_add_sq Finset.univ
    (weight p) A B (∑ S, c₀ S ^ 2) (∑ S, c₁ S ^ 2)
    (fun x _ => hw x) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hA hB
  rw [coefficient_energy_option]
  change _ ≤ ((∑ S, c₀ S ^ 2) + ∑ S, c₁ S ^ 2) ^ 2
  calc
    _ = (1-p) * (∑ x, weight p x * (A x + ρ * chi p false * B x) ^ 4) +
        p * (∑ x, weight p x * (A x + ρ * chi p true * B x) ^ 4) := by
      rw [hsplit]
      simp only [synthesis_option]
      rfl
    _ = ∑ x, weight p x * ((1-p) * (A x + ρ * chi p false * B x) ^ 4 +
        p * (A x + ρ * chi p true * B x) ^ 4) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ ≤ ∑ x, weight p x * ((A x) ^ 2 + (B x) ^ 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (scalar_synthesis_fourth hp hp1 (A x) (B x)) (hw x)
    _ ≤ _ := hbound

end Problem313.BiasedFourier

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


theorem solution.{u} : type_of% @_root_.OAI.Problem313.BiasedFourier.synthesis_fourth_option_of_split.{u} := @_root_.OAI.Problem313.BiasedFourier.synthesis_fourth_option_of_split.{u}
