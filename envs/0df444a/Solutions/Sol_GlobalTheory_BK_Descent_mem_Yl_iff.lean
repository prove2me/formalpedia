-- Prove2me | solution 1 for GlobalTheory.BK.Descent.mem_Yl_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:33:13.555154+00:00
-- url     : https://prove2.me/submissions/8f948ad3-4909-413a-b522-00e9fca60602

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
import Theorems.Thm_GlobalTheory_BK_Hom_onPol_cls
import Theorems.Thm_GlobalTheory_BK_Raises_pow_mem
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
import Theorems.Thm_GlobalTheory_BK_mem_tot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BK.Hom.onPol_cls
attribute [local simp] GlobalTheory.BK.coe_Eunit
attribute [local simp] GlobalTheory.BK.hat_coe



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a]
open GlobalTheory.BK.Descent
variable {P : PhiMod O K l e a ι} (Δ : Descent P)
omit [NeZero e]
namespace GlobalTheory.BK.Descent
theorem _root_.solution {η : ℕ} {y : Vec K a ι} : y ∈ Δ.Yl η ↔ ∃ n : ℕ, (l : K) ^ n • y ∈ Δ.Y η := by
  have hl (n : ℕ) (f : K⟦X⟧) : (l : K) ^ n • f = ((l : A O K) : K⟦X⟧) ^ n * f := by
    simp [smul_eq_C_mul]
  constructor
  · rintro ⟨h1, h2⟩
    choose n hn using fun p : ZMod a × ι => mem_tot.1 h1 p.1 p.2
    refine ⟨Finset.univ.sup n, mem_tot.2 fun τ i => ?_, Δ.inv.smul_mem _ h2⟩
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i)))
    rw [smul_comm, Pi.smul_apply, Pi.smul_apply, hl, hc, pow_add, mul_assoc]
    exact mul_mem (pow_mem (l : A O K).2 c) (hn (τ, i))
  · rintro ⟨n, h1, h2⟩
    refine ⟨mem_tot.2 fun τ i => ⟨n, ?_⟩, fun g => ?_⟩
    · have := mem_tot.1 h1 τ i
      rwa [smul_comm, Pi.smul_apply, Pi.smul_apply, hl] at this
    · exact smul_right_injective _ (pow_ne_zero n (l_ne_zero l)) ((map_smul _ _ _).symm.trans (h2 g))
end GlobalTheory.BK.Descent
