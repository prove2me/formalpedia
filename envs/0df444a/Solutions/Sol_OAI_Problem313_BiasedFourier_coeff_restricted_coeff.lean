-- Prove2me | solution 1 for OAI.Problem313.BiasedFourier.coeff_restricted_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:00:22.319545+00:00
-- url     : https://prove2.me/submissions/ef5dd029-3aa5-4593-bc83-9ec63a76432a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/FourierRestriction.lean:L15-L54
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.BiasedFourier.coeff_restricted_coeff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption

-- ---- from OAI.Combinatorics.SharpThreshold.FourierRestriction ----
namespace OAI

universe u v

noncomputable section

open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]

/-- Fourier transformation in the exterior variables of a conditional Fourier
coefficient recovers the full Fourier coefficient on the disjoint support. -/
theorem coeff_restricted_coeff (p : ℝ) (f : (ι ⊕ κ → Bool) → ℝ)
    (A : Finset ι) (D : Finset κ) :
    coeff p (fun y => coeff p (fun x => f (Sum.elim x y)) A) D =
      coeff p f (A.disjSum D) := by
  classical
  let : DecidableEq ι := Classical.decEq _
  let : DecidableEq κ := Classical.decEq _
  let : DecidableEq (ι ⊕ κ) := Classical.decEq _
  unfold coeff
  symm
  calc
    (∑ z, weight p z * f z * char p (A.disjSum D) z) =
        ∑ x : ι → Bool, ∑ y : κ → Bool,
          weight p (Sum.elim x y) * f (Sum.elim x y) *
            char p (A.disjSum D) (Sum.elim x y) := by
      calc
        _ = ∑ xy : (ι → Bool) × (κ → Bool),
            weight p (Sum.elim xy.1 xy.2) * f (Sum.elim xy.1 xy.2) *
              char p (A.disjSum D) (Sum.elim xy.1 xy.2) := by
          apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow ι κ Bool)
          intro z
          have hz : Sum.elim (fun i => z (Sum.inl i)) (fun j => z (Sum.inr j)) = z := by
            funext i
            cases i <;> rfl
          simpa only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_mk, Function.comp_def] using
            congrArg (fun z => weight p z * f z * char p (A.disjSum D) z) hz.symm
        _ = _ := Fintype.sum_prod_type _
    _ = ∑ y, weight p y * (∑ x, weight p x * f (Sum.elim x y) * char p A x) *
        char p D y := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro x hx
      simp only [weight, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
        char, Finset.prod_disjSum]
      ring

end Problem313.BiasedFourier

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
open scoped BigOperators


theorem solution.{u,v} : type_of% @_root_.OAI.Problem313.BiasedFourier.coeff_restricted_coeff.{u,v} := @_root_.OAI.Problem313.BiasedFourier.coeff_restricted_coeff.{u,v}
