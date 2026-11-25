-- Prove2me | solution 1 for GlobalTheory.AbCoh.LowBaseChange.krullDimLE_isLocalRing_quot_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:53:01.514295+00:00
-- url     : https://prove2.me/submissions/4a5d4bdd-a934-4bbc-8659-ffc5924f5db8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrullDimLEIsLocalRingQuotPow
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.LowBaseChange
namespace GlobalTheory.AbCoh.LowBaseChange
theorem _root_.solution {R : Type} [CommRing R] (m : Ideal R)
    [hm : m.IsMaximal] (n : ℕ) :
    Ring.KrullDimLE 0 (R ⧸ m ^ (n + 1)) ∧ IsLocalRing (R ⧸ m ^ (n + 1)) := by
  have hJt : m ^ (n + 1) ≠ ⊤ := fun h => hm.ne_top
    (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))
  have : Nontrivial (R ⧸ m ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.2 hJt
  have key : ∀ P : Ideal (R ⧸ m ^ (n + 1)), P.IsPrime →
      P = m.map (Ideal.Quotient.mk (m ^ (n + 1))) := by
    intro P hP
    have hc : (P.comap (Ideal.Quotient.mk (m ^ (n + 1)))).IsPrime := Ideal.comap_isPrime _ _
    have h1 : m ≤ P.comap (Ideal.Quotient.mk (m ^ (n + 1))) := by
      refine Ideal.IsPrime.le_of_pow_le (n := n + 1) fun a ha => ?_
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
      exact P.zero_mem
    exact (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P).symm.trans
      (congrArg _ (hm.eq_of_le hc.ne_top h1).symm)
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (R ⧸ m ^ (n + 1))
  exact ((Ring.krullDimLE_zero_and_isLocalRing_tfae (R ⧸ m ^ (n + 1))).out 1 0 rfl rfl).mp
    ⟨P, hP.isPrime, fun Q hQ => (key Q hQ).trans (key P hP.isPrime).symm⟩
end GlobalTheory.AbCoh.LowBaseChange
