-- Prove2me | solution 1 for GlobalTheory.SimMult.exists_bar_sub_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:48:09.66916+00:00
-- url     : https://prove2.me/submissions/64490a9f-078a-40f0-81e2-d7199eae0922

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSimTrivialOfMult

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SimMult
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
namespace GlobalTheory.SimMult
theorem _root_.solution (P : Ideal (𝓞 E)) (hP : P.IsMaximal) : ∃ t, H.bar t - t ∉ P := by
  by_contra hcon
  push Not at hcon
  have := H.unram
  let g : 𝓞 E →ₐ[𝓞 (maximalRealSubfield E)] 𝓞 E :=
    { (H.bar : 𝓞 E →+* 𝓞 E) with
      commutes' := fun r => by
        apply RingOfIntegers.ext
        change ((H.bar (algebraMap _ _ r) : 𝓞 E) : E) = _
        rw [H.bar_eq]
        exact (IsCMField.complexConj E).commutes (r : maximalRealSubfield E) }
  have hg : g = AlgHom.id _ _ :=
    Algebra.FormallyUnramified.ext_of_iInf P (Ideal.iInf_pow_eq_bot_of_isDomain P hP.ne_top)
      fun x => Ideal.Quotient.eq.2 (hcon x)
  have h1 : H.bar H.rt = H.rt := congrArg (fun f => f H.rt) hg
  rw [HostModel.bar_rt] at h1
  have h2 : H.rt = 0 := by
    apply mul_left_cancel₀ (two_ne_zero : (2 : 𝓞 E) ≠ 0)
    linear_combination -h1
  have h3 := H.rt_sq
  rw [h2] at h3
  have h4 : (H.d : 𝓞 E) = 0 := by linear_combination h3
  exact H.d_prime.ne_zero (by exact_mod_cast h4)
end GlobalTheory.SimMult
