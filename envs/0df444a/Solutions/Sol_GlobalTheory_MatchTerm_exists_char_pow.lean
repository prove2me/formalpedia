-- Prove2me | solution 1 for GlobalTheory.MatchTerm.exists_char_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:36.93189+00:00
-- url     : https://prove2.me/submissions/eabca4a7-69b5-46be-87da-e17f9d22b8b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Module Filter
open scoped BigOperators Topology
open GlobalTheory GlobalTheory.MatchTerm
namespace GlobalTheory.MatchTerm
theorem _root_.solution {K X : Type} [Field K] [IsAlgClosed K] [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] {k : ℕ} (hk : k ≠ 0) (t : Multiplicative X →* Kˣ) :
    ∃ s : Multiplicative X →* Kˣ, s ^ k = t := by
  have h : ∀ u : Kˣ, ∃ v : Kˣ, v ^ k = u := fun u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : K) (Nat.pos_of_ne_zero hk)
    have : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hk] at hz
      exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z this, Units.ext (by simpa using hz)⟩
  choose v hv using h
  let b := Module.finBasis ℤ X
  refine ⟨TorsionFourier.charOfValues b fun i => v (t (Multiplicative.ofAdd (b i))), MonoidHom.ext fun x => ?_⟩
  change (∏ i, v (t (Multiplicative.ofAdd (b i))) ^ (b.repr x.toAdd i)) ^ k = t (Multiplicative.ofAdd x.toAdd)
  rw [TorsionFourier.char_apply_eq_prod b t, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hv]
end GlobalTheory.MatchTerm
