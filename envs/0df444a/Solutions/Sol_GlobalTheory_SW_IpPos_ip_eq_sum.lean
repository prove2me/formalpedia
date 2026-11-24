-- Prove2me | solution 1 for GlobalTheory.SW.IpPos.ip_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:23:24.695428+00:00
-- url     : https://prove2.me/submissions/4ed21095-2392-4749-9101-c995938b57cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBounds
import Theorems.Thm_GlobalTheory_SW_haar_eq_haarAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.IpPos
open NumberField
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]
open Matrix Complex
open scoped ComplexConjugate Real
open NumberField
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.IpPos
namespace _root_.GlobalTheory.SW.IpPos
theorem _root_.solution {R : ℕ} (hR : 0 < R) {φ ψ : Matrix κ ι K → ℂ}
    (hφ : _root_.GlobalTheory.SW.HasLevel R φ) (hψ : _root_.GlobalTheory.SW.HasLevel R ψ) :
    _root_.GlobalTheory.SW.ip φ ψ =
      ((R : ℂ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)))⁻¹ *
      ∑ q ∈ (_root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hR).1.toFinset,
        φ q.out * conj (ψ q.out) := by
  have hlev : _root_.GlobalTheory.SW.HasLevel R (fun x => φ x * conj (ψ x)) := by
    refine ⟨fun x hx => hφ.1 x (left_ne_zero_of_mul hx), fun x y hy => ?_⟩
    simp only [hφ.2 x y hy, hψ.2 x y hy]
  unfold _root_.GlobalTheory.SW.ip
  rw [(_root_.GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hlev).1]
  unfold _root_.GlobalTheory.SW.haarAt
  congr 1
  refine finsum_eq_sum_of_support_subset _ ?_
  intro q hq
  rw [Set.Finite.coe_toFinset]
  exact hφ.1 _ (left_ne_zero_of_mul hq)
end _root_.GlobalTheory.SW.IpPos
end GlobalTheory.SW.IpPos
