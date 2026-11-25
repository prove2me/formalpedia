-- Prove2me | solution 1 for GlobalTheory.SublatCount.encard_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:32:50.964266+00:00
-- url     : https://prove2.me/submissions/066a4057-4888-4bad-b2f1-3ba6fb688da0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSublatticesQuotientProdDegreeOnePrimes
import Theorems.Thm_GlobalTheory_SW_Hyper_count
import Theorems.Thm_GlobalTheory_SW_Hyper_surj_of_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.SublatCount
variable {O N : Type} [CommRing O] [AddCommGroup N] [Module O N]
namespace GlobalTheory.SublatCount
theorem _root_.solution [IsDomain O] [Module.Finite O N] [Module.Projective O N] (P : Ideal O)
    [hP : P.IsMaximal] [Finite (O ⧸ P)] :
    (Ker P N).encard =
      ((∑ i ∈ Finset.range (Module.finrank O N), Nat.card (O ⧸ P) ^ i : ℕ) : ℕ∞) := by
  have : Nontrivial (O ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
  have he : Ker P N = {L : Submodule O N | ∃ f : N →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = L} := by
    ext L
    refine exists_congr fun f => and_congr_left fun _ => ⟨fun hf h0 => ?_, fun hf y => ?_⟩
    · obtain ⟨v, hv⟩ := hf 1
      rw [h0] at hv
      exact zero_ne_one hv
    · obtain ⟨v, hv⟩ := GlobalTheory.SW.Hyper.surj_of_ne P f hf
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨c • v, by rw [map_smul, hv, Algebra.smul_def, mul_one]; rfl⟩
  obtain ⟨hf, hc⟩ := GlobalTheory.SW.Hyper.count (M := N) P
  rw [he, ← hf.cast_ncard_eq]
  congr 1
  have h1 : 1 < Nat.card (O ⧸ P) := Finite.one_lt_card
  refine Nat.eq_of_mul_eq_mul_right (m := Nat.card (O ⧸ P) - 1) (by omega) ?_
  rw [hc, geom_sum_mul_of_one_le h1.le]
end GlobalTheory.SublatCount
