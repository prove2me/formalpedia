-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosJ.near_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:01:16.06907+00:00
-- url     : https://prove2.me/submissions/49c7cebb-6671-4485-911a-73fc254e9299

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliser

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosJ
open GlobalTheory.HL
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [NumberField K] [StarRing K]
namespace GlobalTheory.DegCnt.PosJ
theorem _root_.solution {j m : ℕ} (e : Fin j → V) (X : Submodule K V) (L P : Submodule (𝓞 K) V)
    (𝔞 : Fin j → Submodule (𝓞 K) K) (u : Matrix (Fin j) (Fin j) K) (hu : IsUni u) (𝔮 : Ideal (𝓞 K))
    (hq : ∀ x ∈ 𝔮, ∀ a b, ∀ t ∈ 𝔞 a, (x : K) * (t * u b a) ∈ 𝔞 b)
    (h1 : ∀ a, ∀ t ∈ 𝔞 a, t • vec e u a ∈ L)
    (h2 : ∀ y ∈ L, y ∈ X → ∃ c : Fin j → K, (∀ a, c a ∈ 𝔞 a) ∧ y = ∑ a, c a • vec e u a)
    (hP1 : ∀ a, ∀ t ∈ 𝔞 a, t • e a ∈ P)
    (hP2 : ∀ y ∈ P, y ∈ X → ∃ c : Fin j → K, (∀ a, c a ∈ 𝔞 a) ∧ y = ∑ a, c a • e a)
    (hm : j ≤ m) (hm1 : 1 ≤ m) :
    𝔮 ^ m • (P ⊓ rs (𝓞 K) X) ≤ L ∧ 𝔮 ^ m • (L ⊓ rs (𝓞 K) X) ≤ P := by
  have hs : ∀ (x : 𝓞 K) (y : V), x • y = (x : K) • y := fun x y => (algebraMap_smul K x y).symm
  have key : ∀ a : Fin j, ∀ x ∈ 𝔮 ^ (a : ℕ), ∀ t ∈ 𝔞 a, ((x : K) * t) • e a ∈ L := by
    intro a
    induction a using WellFoundedLT.induction with
    | ind a ih =>
      intro x hx t ht
      have h3 : ((x : K) * t) • vec e u a ∈ L := by
        rw [mul_smul, ← hs]; exact L.smul_mem _ (h1 a t ht)
      rw [vec, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), hu.2, one_smul, smul_add] at h3
      refine (L.add_mem_iff_left ?_).1 h3
      rw [Finset.smul_sum]
      refine L.sum_mem fun b hb => ?_
      rcases lt_or_gt_of_ne (Finset.mem_erase.1 hb).1 with h4 | h4
      · have h5 : x ∈ 𝔮 ^ (b : ℕ) * 𝔮 := by
          rw [← pow_succ]; exact Ideal.pow_le_pow_right (by exact h4) hx
        rw [smul_smul]
        refine Submodule.mul_induction_on (C := fun x : 𝓞 K => ((x : K) * t * u b a) • e b ∈ L) h5
          (fun p hp q hq' => ?_) (fun p q hp hq' => ?_)
        · have := ih b h4 p hp _ (hq q hq' a b t ht)
          convert this using 2
          push_cast; ring
        · have := L.add_mem hp hq'
          rw [← add_smul] at this
          convert this using 2
          push_cast; ring
      · rw [hu.1 _ _ h4, zero_smul, smul_zero]; exact L.zero_mem
  constructor
  · refine Submodule.smul_le.2 fun x hx y hy => ?_
    obtain ⟨c, hc, rfl⟩ := hP2 y hy.1 hy.2
    rw [hs, Finset.smul_sum]
    refine L.sum_mem fun a _ => ?_
    rw [smul_smul]
    exact key a x (Ideal.pow_le_pow_right (a.2.le.trans hm) hx) _ (hc a)
  · refine Submodule.smul_le.2 fun x hx y hy => ?_
    obtain ⟨c, hc, rfl⟩ := h2 y hy.1 hy.2
    rw [hs, Finset.smul_sum]
    refine P.sum_mem fun a _ => ?_
    rw [vec, Finset.smul_sum, Finset.smul_sum]
    refine P.sum_mem fun b _ => ?_
    rw [smul_smul, smul_smul, mul_assoc]
    exact hP1 b _ (hq x (Ideal.pow_le_self (by omega) hx) a b _ (hc a))
end GlobalTheory.DegCnt.PosJ
