-- Prove2me | solution 1 for GlobalTheory.DegCnt.LiftS.pow_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:33:09.263492+00:00
-- url     : https://prove2.me/submissions/a0f7ad28-af62-4fcb-9eeb-ed79f49683a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
import Theorems.Thm_GlobalTheory_DegCnt_LiftS_star_one_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
namespace GlobalTheory.DegCnt.LiftS
section Ideals
variable {K : Type} [Field K] [NumberField K] [StarRing K]
private theorem star_mem_mul_of_star_mem {M N : Submodule (𝓞 K) K} (hM : ∀ x ∈ M, star x ∈ M)
    (hN : ∀ x ∈ N, star x ∈ N) : ∀ x ∈ M * N, star x ∈ M * N := by
  intro x hx
  refine Submodule.mul_induction_on hx (C := fun x => star x ∈ M * N) ?_ ?_
  · intro m hm n hn
    have hmn := Submodule.mul_mem_mul (hM m hm) (hN n hn)
    rw [star_mul, mul_comm (star n) (star m)]
    exact hmn
  · intro a b ha hb
    rw [star_add]
    exact Submodule.add_mem _ ha hb
end Ideals
section Abstract
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
end Abstract
section Flag
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
end Flag
section Conc
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)
end Conc
section Lat
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)
end Lat
section Main
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
end Main
end GlobalTheory.DegCnt.LiftS
end

set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.LiftS
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace GlobalTheory.DegCnt.LiftS
theorem _root_.solution (𝔡 : Ideal (𝓞 K)) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℕ) :
    ∀ x ∈ (((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ n : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K),
      star x ∈ (((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ n : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  rw [FractionalIdeal.coe_pow, FractionalIdeal.coe_coeIdeal]
  have base : ∀ x ∈ IsLocalization.coeSubmodule K 𝔡, star x ∈ IsLocalization.coeSubmodule K 𝔡 := by
    intro x hx
    rw [IsLocalization.mem_coeSubmodule] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, hz'⟩ := hs y hy
    exact ⟨z, hz, hz'⟩
  induction n with
  | zero => intro x hx; rw [pow_zero] at hx ⊢; exact star_one_mem hx
  | succ m ih => rw [pow_succ]; exact star_mem_mul_of_star_mem ih base
end GlobalTheory.DegCnt.LiftS
