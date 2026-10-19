-- Prove2me | solution 1 for OAI.Problem313.BiasedFourier.synthesis_contraction_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:51:53.483116+00:00
-- url     : https://prove2.me/submissions/44e99c68-11e8-45ee-ae57-a508c4f637fe

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/FourierReindex.lean:L123-L144
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.BiasedFourier.synthesis_contraction_reindex. The node keeps its source
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

-- ---- from OAI.Combinatorics.SharpThreshold.FourierReindex ----
namespace OAI

universe u v

noncomputable section

open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Product Bernoulli weight is unchanged by renaming its coordinates. -/
theorem weight_reindex (e : ι ≃ κ) (p : ℝ) (x : ι → Bool) :
    weight p (Reindex.config e x) = weight p x := by
  unfold weight
  exact (Fintype.prod_equiv e _ _ (fun i => by simp)).symm

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- Fourier characters are natural under a bijection of coordinate sets. -/
theorem char_reindex (e : ι ≃ κ) (p : ℝ) (S : Finset ι) (x : ι → Bool) :
    char p (S.map e.toEmbedding) (Reindex.config e x) = char p S x := by
  simp [char, Finset.prod_map]

/-- Every weighted finite expectation is unchanged by coordinate transport. -/
theorem expectation_reindex (e : ι ≃ κ) (p : ℝ)
    (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ)
    (hfg : ∀ x, g (Reindex.config e x) = f x) :
    (∑ y, weight p y * g y) = ∑ x, weight p x * f x := by
  classical
  symm
  apply Fintype.sum_equiv (Reindex.configEquiv e)
  intro x
  simp only [Reindex.configEquiv_apply, weight_reindex, hfg]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Coordinate transport of spectral synthesis, including a degree-dependent multiplier. -/
theorem spectral_sum_reindex (e : ι ≃ κ) (p : ℝ) (M : ℕ → ℝ)
    (c : Finset ι → ℝ) (d : Finset κ → ℝ)
    (hcd : ∀ S, d (S.map e.toEmbedding) = c S) (x : ι → Bool) :
    (∑ T : Finset κ, M T.card * d T * char p T (Reindex.config e x)) =
      ∑ S : Finset ι, M S.card * c S * char p S x := by
  classical
  symm
  apply Fintype.sum_equiv e.finsetCongr
  intro S
  simp only [Equiv.finsetCongr_apply, Finset.card_map, hcd, char_reindex]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Every degree-weighted squared coefficient sum is invariant under coordinate transport. -/
theorem coefficient_energy_reindex (e : ι ≃ κ) (M : ℕ → ℝ)
    (c : Finset ι → ℝ) (d : Finset κ → ℝ)
    (hcd : ∀ S, d (S.map e.toEmbedding) = c S) :
    (∑ T : Finset κ, M T.card * (d T) ^ 2) =
      ∑ S : Finset ι, M S.card * (c S) ^ 2 := by
  classical
  symm
  apply Fintype.sum_equiv e.finsetCongr
  intro S
  simp only [Equiv.finsetCongr_apply, Finset.card_map, hcd]

/-- The universal coefficient form of hypercontractivity transports along coordinate
bijections. It is the equivalence branch of finite-type induction. -/
theorem synthesis_contraction_reindex (e : ι ≃ κ) (p ρ : ℝ)
    (hι : ∀ c : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S : Finset ι, ρ ^ S.card * c S * char p S x) ^ 4) ≤
        (∑ S : Finset ι, (c S) ^ 2) ^ 2)
    (d : Finset κ → ℝ) :
    (∑ y, weight p y *
        (∑ T : Finset κ, ρ ^ T.card * d T * char p T y) ^ 4) ≤
        (∑ T : Finset κ, (d T) ^ 2) ^ 2 := by
  classical
  let c : Finset ι → ℝ := fun S => d (S.map e.toEmbedding)
  have he := spectral_sum_reindex e p (fun k => ρ ^ k) c d (fun _ => rfl)
  rw [expectation_reindex e p
    (fun x => (∑ S : Finset ι, ρ ^ S.card * c S * char p S x) ^ 4)
    (fun y => (∑ T : Finset κ, ρ ^ T.card * d T * char p T y) ^ 4)
    (fun x => congrArg (fun z : ℝ => z ^ 4) (he x))]
  have hc : (∑ T : Finset κ, (d T) ^ 2) = ∑ S : Finset ι, (c S) ^ 2 := by
    simpa using coefficient_energy_reindex e (fun _ => 1) c d (fun _ => rfl)
  rw [hc]
  exact hι c

end Problem313.BiasedFourier

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
open scoped BigOperators


theorem solution.{u,v} : type_of% @_root_.OAI.Problem313.BiasedFourier.synthesis_contraction_reindex.{u,v} := @_root_.OAI.Problem313.BiasedFourier.synthesis_contraction_reindex.{u,v}
