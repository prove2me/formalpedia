-- Prove2me | solution 1 for OAI.Problem313.BiasedFourier.synthesis_fourth_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:33:03.711865+00:00
-- url     : https://prove2.me/submissions/27eb461d-5f1d-463e-9376-aeaf6ff56ca3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/FourierHypercontractive.lean:L96-L114
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.BiasedFourier.synthesis_fourth_bound. The node keeps its source
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
import Theorems.Thm_OAI_Problem313_BiasedFourier_synthesis_contraction_reindex
import Theorems.Thm_OAI_Problem313_BiasedFourier_synthesis_fourth_option_of_split

-- ---- from OAI.Combinatorics.SharpThreshold.FourierOptionExpectation ----
namespace OAI

universe u

noncomputable section

open scoped BigOperators
open Classical

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι]

/-- Exact expectation splitting at the distinguished `none` coordinate.
This identity is polynomial and requires no restriction on the bias. -/
theorem weighted_sum_option (p : ℝ) (g : (Option ι → Bool) → ℝ) :
    (∑ x, weight p x * g x) =
      (1 - p) * (∑ y, weight p y * g ((fun i : Option ι => Option.elim i false y))) +
        p * (∑ y, weight p y * g ((fun i : Option ι => Option.elim i true y))) := by
  let e : (Option ι → Bool) ≃ Bool × (ι → Bool) := Equiv.piOptionEquivProd
  rw [← e.symm.sum_comp (fun x => weight p x * g x), Fintype.sum_prod_type,
    Fintype.sum_bool]
  have he (b : Bool) (y : ι → Bool) : e.symm (b, y) = (fun i : Option ι => Option.elim i b y) := by
    funext i
    cases i <;> rfl
  simp_rw [he, weight_option_elim, scalarWeight_true, scalarWeight_false,
    mul_assoc, ← Finset.mul_sum]
  ring

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

/-- Initial case of the finite-coordinate tensorization induction. -/
theorem synthesis_fourth_empty {ι : Type u} [Fintype ι] [IsEmpty ι]
    (p : ℝ) (c : Finset ι → ℝ) :
    (∑ x : ι → Bool, weight p x *
      (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card * c S * char p S x) ^ 4) ≤
      (∑ S, c S ^ 2) ^ 2 := by
  have he : (default : Finset ι) = ∅ := Subsingleton.elim _ _
  simp [weight, char, he]
  ring_nf
  exact le_rfl

/-- Biased product hypercontractivity in its root-free, arbitrary-coefficient form. -/
theorem synthesis_fourth_bound {ι : Type u} [Fintype ι]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (c : Finset ι → ℝ) :
    (∑ x, weight p x * (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card *
      c S * char p S x) ^ 4) ≤ (∑ S, c S ^ 2) ^ 2 := by
  classical
  refine Fintype.induction_empty_option
    (P := fun α _ => ∀ c : Finset α → ℝ,
      (∑ x, weight p x * (∑ S, (Real.sqrt (p*(1-p))/4) ^ S.card *
        c S * char p S x) ^ 4) ≤ (∑ S, c S ^ 2) ^ 2) ?_ ?_ ?_ ι c
  · intro α β _ e h d
    let : Fintype α := Fintype.ofEquiv β e.symm
    exact synthesis_contraction_reindex e p (Real.sqrt (p*(1-p))/4) h d
  · exact synthesis_fourth_empty p
  · intro α _ h d
    convert! synthesis_fourth_option_of_split hp hp1 (weighted_sum_option p) h d using 1
    apply Finset.sum_congr (by ext x; simp)
    intro x hx
    rfl

end Problem313.BiasedFourier

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq


theorem solution.{u} : type_of% @_root_.OAI.Problem313.BiasedFourier.synthesis_fourth_bound.{u} := @_root_.OAI.Problem313.BiasedFourier.synthesis_fourth_bound.{u}
