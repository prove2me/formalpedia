-- Prove2me | solution 1 for OAI.Problem313.BiasedFourier.restriction_mass_subtype
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:59:22.207424+00:00
-- url     : https://prove2.me/submissions/00eb7087-7079-4014-a049-80336e8b1769

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/RestrictionMassSubtype.lean:L104-L130
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.BiasedFourier.restriction_mass_subtype. The node keeps its source
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
import Theorems.Thm_OAI_Problem313_BiasedFourier_coeff_restricted_coeff_subtype
import Theorems.Thm_OAI_Problem313_BiasedFourier_parseval

-- ---- from OAI.Combinatorics.SharpThreshold.RestrictionMassSubtype ----
namespace OAI

universe u

noncomputable section

open scoped BigOperators

namespace Problem313

variable {ι : Type u} [Fintype ι] (P : ι → Prop) [DecidablePred P]

namespace BiasedFourier

/-- Exact squared-coefficient averaging over arbitrary exterior coordinate subtypes. -/
theorem restricted_coeff_sq_average_subtype [DecidableEq ι] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (A : Finset {i // P i}) :
    (∑ y : {i // ¬P i} → Bool, weight p y *
      (coeff p (restrictCube P f y) A) ^ 2) =
      ∑ D : Finset {i // ¬P i}, (coeff p f (subtypeSupport P A D)) ^ 2 := by
  classical
  symm
  simpa only [coeff_restricted_coeff_subtype] using
    parseval hp hp1 (fun y => coeff p (restrictCube P f y) A)

/-- Sum over each ambient support by its free and exterior pieces. -/
theorem sum_subtypeSupport [DecidableEq ι] (h : Finset ι → ℝ) :
    (∑ A : Finset {i // P i}, ∑ D : Finset {i // ¬P i}, h (subtypeSupport P A D)) =
      ∑ S : Finset ι, h S := by
  classical
  calc
    _ = ∑ AD : Finset {i // P i} × Finset {i // ¬P i},
        h (subtypeSupport P AD.1 AD.2) :=
      (Fintype.sum_prod_type (fun AD : Finset {i // P i} × Finset {i // ¬P i} =>
        h (subtypeSupport P AD.1 AD.2))).symm
    _ = _ := by
      apply Fintype.sum_equiv (subtypeSupportEquiv P)
      rintro ⟨A,D⟩
      rfl

/-- Exact restriction-mass transport for any statistic of the free support.
There is deliberately no restriction on exterior Fourier degree. -/
theorem restriction_mass_subtype [DecidableEq ι] {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : (ι → Bool) → ℝ)
    (L : Finset {i // P i} → ℝ) :
    (∑ y : {i // ¬P i} → Bool, weight p y *
      ∑ A : Finset {i // P i}, L A * coeff p (restrictCube P f y) A ^ 2) =
      ∑ S : Finset ι, L (S.subtype P) * coeff p f S ^ 2 := by
  classical
  calc
    (∑ y : {i // ¬P i} → Bool, weight p y *
        ∑ A : Finset {i // P i}, L A * coeff p (restrictCube P f y) A ^ 2) =
      ∑ A : Finset {i // P i}, L A *
        ∑ y : {i // ¬P i} → Bool, weight p y * coeff p (restrictCube P f y) A ^ 2 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = ∑ A : Finset {i // P i}, ∑ D : Finset {i // ¬P i},
        L A * coeff p f (subtypeSupport P A D) ^ 2 := by
      simp_rw [restricted_coeff_sq_average_subtype P hp hp1, Finset.mul_sum]
    _ = ∑ S : Finset ι, L (S.subtype P) * coeff p f S ^ 2 := by
      simpa only [subtype_subtypeSupport] using
        sum_subtypeSupport P (fun S => L (S.subtype P) * coeff p f S ^ 2)

end BiasedFourier
end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.Problem313.BiasedFourier.restriction_mass_subtype.{u} := @_root_.OAI.Problem313.BiasedFourier.restriction_mass_subtype.{u}
