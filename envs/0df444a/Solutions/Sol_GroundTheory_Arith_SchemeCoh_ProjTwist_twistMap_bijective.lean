-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ProjTwist.twistMap_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:32:50.101852+00:00
-- url     : https://prove2.me/submissions/f3640f06-0f3a-4e64-a016-67783c02ac59

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechModel
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistLeray
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_twistFrac_mul_twistFrac_neg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_twistMap_apply
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_exists_section_of_isLocallyFraction_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_ext
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_isLocallyFraction_mul
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
universe w w' u
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjTwist
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]
namespace GroundTheory.Arith.SchemeCoh.ProjTwist
theorem _root_.solution {u : A} (hu : u ∈ 𝒜 1) (k : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒜)}
    (hW : ∀ x : W, u ∉ x.1.asHomogeneousIdeal) : Function.Bijective (twistMap hu k hW) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    apply Subtype.ext
    funext x
    apply HomogeneousLocalization.val_injective
    have h1 : twistFrac u k x.1 (hW x) * (t.1 x).val = 0 := congrFun (congrArg Subtype.val ht) x
    have h2 := twistFrac_mul_twistFrac_neg u k x.1 (hW x)
    refine (show (t.1 x).val = 0 from ?_).trans HomogeneousLocalization.val_zero.symm
    calc (t.1 x).val = twistFrac u (-k) x.1 (hW x) * (twistFrac u k x.1 (hW x) * (t.1 x).val) := by
          linear_combination (-(t.1 x).val) * h2
      _ = 0 := by rw [h1, mul_zero]
  · intro s
    have hf := isLocallyFraction_mul (neg_add_cancel k) (isLocallyFraction_twistFrac hu (-k) hW) s.2
    obtain ⟨t, ht⟩ := exists_section_of_isLocallyFraction_zero _ hf
    refine ⟨t, Subtype.ext (funext fun x => ?_)⟩
    rw [twistMap_apply, ht x]
    change twistFrac u k x.1 (hW x) * (twistFrac u (-k) x.1 (hW x) * s.1 x) = s.1 x
    linear_combination (s.1 x) * twistFrac_mul_twistFrac_neg u k x.1 (hW x)
end GroundTheory.Arith.SchemeCoh.ProjTwist
