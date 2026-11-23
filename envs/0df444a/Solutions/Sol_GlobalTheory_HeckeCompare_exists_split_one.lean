-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.exists_split_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:18.672953+00:00
-- url     : https://prove2.me/submissions/02b3f3a4-5a57-4563-8c89-91514c195a25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HeckeCompare
namespace GlobalTheory.HeckeCompare
theorem _root_.solution {O : Type} [CommRing O] [IsDedekindDomain O] {p : O} (hp : p ≠ 0) (P : Ideal O)
    [P.IsMaximal] : ∃ (n : ℕ) (π j : O), π ∈ P ∧ π + j = 1 ∧ ∀ a ∈ P ^ (n + 1), j * a ∈ Ideal.span {p} * P := by
  obtain ⟨J, hJ, e⟩ := Ideal.eq_prime_pow_mul_coprime (I := Ideal.span {p}) (by simpa using hp) P
  obtain ⟨π, hπ, j, hj, h⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hJ)
  generalize Multiset.count P _ = n at e
  refine ⟨n, π, j, hπ, h, fun a ha => ?_⟩
  rw [e, mul_right_comm, ← pow_succ, mul_comm j]
  exact Ideal.mul_mem_mul ha hj
end GlobalTheory.HeckeCompare
