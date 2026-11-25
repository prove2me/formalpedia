-- Prove2me | solution 1 for GlobalTheory.SW.NbAvg.ncard_carry_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:02:44.777227+00:00
-- url     : https://prove2.me/submissions/d51fe0eb-2bbb-4cd9-854d-c1d11210fb58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ClassSumNb
import Theorems.Thm_GlobalTheory_SW_NbAvg_ccT_mem_carry
import Theorems.Thm_GlobalTheory_SW_Nbr_cc_cc
import Theorems.Thm_GlobalTheory_SW_Nbr_conjI_conjI
import Theorems.Thm_GlobalTheory_SW_Nbr_good_conj
import Theorems.Thm_GlobalTheory_TraceDualMin_cc_cc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW
open GlobalTheory.SW.NbAvg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.SW.NbAvg
theorem _root_.solution {M q : ℕ} {P : Ideal (𝓞 E)} (hM : 0 < M) (hP : GoodPrime M q P)
    {A B : Lt E n} (hA : A ∈ Vset E n M) (hB : B ∈ Vset E n M) :
    (carry M (conjI P) B A).ncard = (carry M P A B).ncard := by
  have hcc : ∀ k : Matrix (Fin n) (Fin n) E, ccT (ccT k) = k := by
    intro k
    ext i j
    simp [ccT, Nbr.cc_cc]
  have hgc : GoodPrime M q (conjI P) := Nbr.good_conj hP
  have himg : (ccT : Matrix (Fin n) (Fin n) E → Matrix (Fin n) (Fin n) E) '' carry M P A B =
      carry M (conjI P) B A := by
    ext k
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ccT_mem_carry hM hP hA hB hh
    · intro hk
      refine ⟨ccT k, ?_, hcc k⟩
      have key := ccT_mem_carry hM hgc hB hA hk
      rwa [Nbr.conjI_conjI] at key
  rw [← himg, Set.ncard_image_of_injective _ (Function.LeftInverse.injective hcc)]
end GlobalTheory.SW.NbAvg
