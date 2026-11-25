-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.APart.summable_norm_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:41:40.346096+00:00
-- url     : https://prove2.me/submissions/092c2688-a5c4-4703-bc3d-c439de7246fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Theorems.Thm_GlobalTheory_HeckeTwo_APart_exists_den
import Theorems.Thm_ReciprocityTheory_Cheb_summable_absNorm_rpow_ideal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.APart
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwo.APart
theorem _root_.solution (I : FractionalIdeal (𝓞 F)⁰ F) {s : ℝ} (hs : 1 < s) :
    Summable (fun c : Quotient (unitRel I) => |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| ^ (-s)) := by
  obtain ⟨d, hd, hdI⟩ := exists_den I
  choose g hg using fun c : Quotient (unitRel I) => hdI c.out.1 c.out.2.1
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd
  have hinj : Function.Injective (fun c : Quotient (unitRel I) => Ideal.span ({g c} : Set (𝓞 F))) := by
    intro c c' h
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 h
    have h2 := congrArg (fun x : 𝓞 F => (x : F)) hu
    push_cast at h2
    refine Quotient.out_equiv_out.1 ⟨u, ?_⟩
    apply mul_left_cancel₀ hd'
    linear_combination ((u : 𝓞 F) : F) * hg c - hg c' - h2
  have hS := (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).comp_injective hinj
  have hNd : 0 < |((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| := by
    simp [Algebra.norm_eq_zero_iff, hd']
  refine (hS.mul_left (|((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| ^ s)).congr fun c => ?_
  have e1 : ((Algebra.norm ℤ (g c) : ℤ) : ℚ) = Algebra.norm ℚ (d : F) * Algebra.norm ℚ c.out.1 := by
    rw [Algebra.coe_norm_int, hg, map_mul]
  have e2 : ((Algebra.norm ℤ (g c) : ℤ) : ℝ) =
      ((Algebra.norm ℚ (d : F) : ℚ) : ℝ) * ((Algebra.norm ℚ c.out.1 : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) e1
  have hN : ((Ideal.absNorm (Ideal.span ({g c} : Set (𝓞 F))) : ℕ) : ℝ) =
      |((Algebra.norm ℚ (d : F) : ℚ) : ℝ)| * |((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, e2, abs_mul]
  simp only [Function.comp_apply]
  rw [hN, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hNd, add_neg_cancel,
    Real.rpow_zero, one_mul]
end GlobalTheory.HeckeTwo.APart
