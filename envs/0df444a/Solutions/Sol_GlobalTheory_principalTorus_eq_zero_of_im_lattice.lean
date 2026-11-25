-- Prove2me | solution 1 for GlobalTheory.principalTorus_eq_zero_of_im_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:56:16.717474+00:00
-- url     : https://prove2.me/submissions/58b08bce-35ee-473f-952f-164304bcc335

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_PrincipalTorusEqZeroOfImLattice
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_eq__c00dd98ec76c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_span_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace
open GlobalTheory
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory
theorem _root_.solution (X : PT E) {a : Vsp X.dim} (h : ∀ y ∈ X.L, (Hf y a).im = 0) : a = 0 := by
  have hspan : ∀ v, (Hf v a).im = 0 := by
    intro v
    have hv : v ∈ Submodule.span ℝ (X.L : Set (Vsp X.dim)) := by
      have h1 : Submodule.span ℝ (Set.range X.b) ≤ Submodule.span ℝ (X.L : Set (Vsp X.dim)) :=
        Submodule.span_mono (fun z hz => Submodule.subset_span hz)
      rw [X.b.span_eq] at h1
      exact h1 Submodule.mem_top
    exact Hf_im_span_left _ a h v hv
  have h1 := hspan (Complex.I • a)
  have e : -(Complex.I • (Complex.I • a)) = a := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]
  rw [Hf_im_eq', e] at h1
  exact inner_self_eq_zero.1 h1
end GlobalTheory
