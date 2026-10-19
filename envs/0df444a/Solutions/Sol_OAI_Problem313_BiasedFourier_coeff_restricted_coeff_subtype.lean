-- Prove2me | solution 1 for OAI.Problem313.BiasedFourier.coeff_restricted_coeff_subtype
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:55:05.489441+00:00
-- url     : https://prove2.me/submissions/ebef8817-576b-4a53-ad68-96e91b2260e0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/RestrictionMassSubtype.lean:L31-L49
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.BiasedFourier.coeff_restricted_coeff_subtype. The node keeps its source
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
import Theorems.Thm_OAI_Problem313_BiasedFourier_coeff_restricted_coeff

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

omit [DecidableEq ι] [DecidableEq κ] in
/-- Transport of Fourier coefficients, with the support transported by `Finset.map`. -/
theorem coeff_reindex (e : ι ≃ κ) (p : ℝ)
    (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ)
    (hfg : ∀ x, g (Reindex.config e x) = f x) (S : Finset ι) :
    coeff p g (S.map e.toEmbedding) = coeff p f S := by
  classical
  unfold coeff
  symm
  apply Fintype.sum_equiv (Reindex.configEquiv e)
  intro x
  simp only [Reindex.configEquiv_apply, weight_reindex, hfg, char_reindex]

end Problem313.BiasedFourier

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.RestrictionMassSubtype ----
namespace OAI

universe u

noncomputable section

open scoped BigOperators

namespace Problem313

variable {ι : Type u} [Fintype ι] (P : ι → Prop) [DecidablePred P]

omit [Fintype ι] in
/-- The coordinate equivalence from a predicate and its complement is ordinary pasting. -/
theorem config_sumCompl_eq_pasteCube
    (x : {i // P i} → Bool) (y : {i // ¬P i} → Bool) :
    Reindex.config (Equiv.sumCompl P) (Sum.elim x y) = pasteCube P x y := by
  funext i
  by_cases hi : P i <;> simp [Reindex.config, pasteCube, hi]

namespace BiasedFourier

/-- Conditional Fourier coefficients on arbitrary coordinate subtypes agree with
full coefficients after Fourier transformation in the exterior coordinates. -/
theorem coeff_restricted_coeff_subtype (p : ℝ) (f : (ι → Bool) → ℝ)
    (A : Finset {i // P i}) (D : Finset {i // ¬P i}) :
    coeff p (fun y => coeff p (restrictCube P f y) A) D =
      coeff p f (subtypeSupport P A D) := by
  classical
  let F : ({i // P i} ⊕ {i // ¬P i} → Bool) → ℝ :=
    fun z => f (Reindex.config (Equiv.sumCompl P) z)
  have hsplit : ∀ x y, F (Sum.elim x y) = restrictCube P f y x := by
    intro x y
    simp [F, config_sumCompl_eq_pasteCube, restrictCube]
  calc
    coeff p (fun y => coeff p (restrictCube P f y) A) D =
        coeff p (fun y => coeff p (fun x => F (Sum.elim x y)) A) D := by
      simp only [hsplit]
    _ = coeff p F (A.disjSum D) := coeff_restricted_coeff p F A D
    _ = coeff p f (subtypeSupport P A D) :=
      (coeff_reindex (Equiv.sumCompl P) p F f (fun _ => rfl) (A.disjSum D)).symm

end BiasedFourier
end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.Problem313.BiasedFourier.coeff_restricted_coeff_subtype.{u} := @_root_.OAI.Problem313.BiasedFourier.coeff_restricted_coeff_subtype.{u}
