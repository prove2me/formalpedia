-- Prove2me | solution 1 for GlobalTheory.SW.NbAvg.wt_mul_nbIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:20:46.429926+00:00
-- url     : https://prove2.me/submissions/ca9a1127-309a-401f-b6cc-bb4ccc09a336

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ClassSumNb
import Theorems.Thm_GlobalTheory_SW_NbAvg_ncard_carry
import Theorems.Thm_GlobalTheory_SW_NbAvg_ncard_carry_symm
import Theorems.Thm_GlobalTheory_SW_finite_cls_and_stab
import Theorems.Thm_GlobalTheory_SW_neighbours


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
    (wt M A : ℂ) * (nbIn M P A B).ncard = (wt M B : ℂ) * (nbIn M (conjI P) B A).ncard := by
  obtain ⟨-, -, hstab, -, -⟩ := finite_cls_and_stab E n M hM
  obtain ⟨hgc, -, hnb⟩ := neighbours E n M q P hM hP
  have hnb' := (neighbours E n M q (conjI P) hM hgc).2.2
  have h1 := ncard_carry (P := P) (A := A) (B := B) (hnb A hA).1 (hstab B hB).1
  have h2 := ncard_carry (P := conjI P) (A := B) (B := A) (hnb' B hB).1 (hstab A hA).1
  have h3 := ncard_carry_symm hM hP hA hB
  have key : (nbIn M P A B).ncard * {h ∈ DH E n M | Moves h B B}.ncard =
      (nbIn M (conjI P) B A).ncard * {h ∈ DH E n M | Moves h A A}.ncard := by
    rw [← h1, ← h2, h3]
  have hne : ∀ Λ ∈ Vset E n M, (({h ∈ DH E n M | Moves h Λ Λ}.ncard : ℕ) : ℂ) ≠ 0 := by
    intro Λ hΛ h0
    have hw := (hstab Λ hΛ).2
    norm_cast at h0
    simp only [wt, h0] at hw
    simp at hw
  simp only [wt]
  push_cast
  rw [inv_mul_eq_div, inv_mul_eq_div, div_eq_div_iff (hne A hA) (hne B hB)]
  exact_mod_cast key
end GlobalTheory.SW.NbAvg
