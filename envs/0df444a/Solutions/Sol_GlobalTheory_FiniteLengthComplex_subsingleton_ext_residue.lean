-- Prove2me | solution 1 for GlobalTheory.FiniteLengthComplex.subsingleton_ext_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:17.065802+00:00
-- url     : https://prove2.me/submissions/157c0afa-ed72-43c9-9315-24b3b4ad7585

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing
open GlobalTheory
open GlobalTheory.FiniteLengthComplex
variable {R : Type} [CommRing R]
namespace GlobalTheory.FiniteLengthComplex
theorem _root_.solution [IsRegularLocalRing R] (g : ℕ) (hg : ringKrullDim R = g)
    (n : ℕ) (hn : n ≠ g) :
    Subsingleton
      (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) n) := by
  obtain ⟨xs, h, hd⟩ := exists_ofList_eq_maximalIdeal_length_eq R
  have hreg := isRegular_of_ofList_eq_maximalIdeal h hd.le
  have hlen : xs.length = g := by
    rw [hg] at hd
    exact_mod_cast hd
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · refine ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) _ ?_ _ ?_ xs ?_ hreg n
      (hlen ▸ hlt)
    · rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    · rw [smul_eq_mul, Ideal.mul_top]
      exact (maximalIdeal.isMaximal R).ne_top.lt_top
    · intro r hr
      rw [← h]
      exact Ideal.subset_span hr
  · have key := ModuleCat.projectiveDimension_quotient_eq_length.{0} xs hreg
    rw [projectiveDimension_eq_of_iso (Shrink.linearEquiv R _).toModuleIso, h, hlen] at key
    have : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ maximalIdeal R)) g :=
      (projectiveDimension_le_iff _ g).mp key.le
    exact HasProjectiveDimensionLT.subsingleton _ (g + 1) n hgt _
end GlobalTheory.FiniteLengthComplex
