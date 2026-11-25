-- Prove2me | solution 1 for GlobalTheory.ZetaPole.norm_le_idealZetaR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:25:52.345235+00:00
-- url     : https://prove2.me/submissions/3f23e45e-259e-4679-a73a-43b19b167d33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialZetaTotallyRealAtMostSimplePole
import Theorems.Thm_ReciprocityTheory_Cheb_sum_le_idealZetaR


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex Filter Topology
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.ZetaPole
namespace GlobalTheory.ZetaPole
theorem _root_.solution (F : Type) [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ)
    (hZ : IsPartialZeta C Z) {x : ℝ} (hx : 1 < x) : ‖Z x‖ ≤ ReciprocityTheory.Cheb.idealZetaR F x := by
  have hs := hZ.2 x (by simpa using hx)
  set r : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} → ℝ :=
    fun J => ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℝ) ^ (-x) with hr
  have hterm : (fun J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} =>
      ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-(x : ℂ))) = fun J => ((r J : ℝ) : ℂ) := by
    funext J
    rw [hr, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.ofReal_natCast]
  rw [hterm] at hs
  have hre := (Complex.hasSum_re hs)
  have him := (Complex.hasSum_im hs)
  simp only [Complex.ofReal_re, Complex.ofReal_im] at hre him
  have him0 : (Z x).im = 0 := (hasSum_zero.unique him).symm
  have hnn : 0 ≤ (Z x).re := hre.nonneg fun J => by positivity
  have hZx : Z x = ((Z x).re : ℂ) := Complex.ext (by simp) (by simp [him0])
  rw [hZx, norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  refine hasSum_le_of_sum_le hre fun T => ?_
  classical
  have hinj : Function.Injective (fun J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} => (J.1 : Ideal (𝓞 F))) := by
    intro a b h
    exact Subtype.ext (Subtype.ext h)
  have := ReciprocityTheory.Cheb.sum_le_idealZetaR F hx (T.image fun J => (J.1 : Ideal (𝓞 F)))
  rw [Finset.sum_image fun a _ b _ h => hinj h] at this
  exact this
end GlobalTheory.ZetaPole
