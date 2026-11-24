-- Prove2me | solution 1 for GlobalTheory.BK.Descent.map_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:00:10.122942+00:00
-- url     : https://prove2.me/submissions/2c7c7b30-abea-4e8f-b33f-6e3aab047bbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqMulAddOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsAlgebraMapEqRoot
import Theorems.Thm_GlobalTheory_BK_Descent_norm_card
import Theorems.Thm_GlobalTheory_BK_Hom_onPol_cls
import Theorems.Thm_GlobalTheory_BK_coe_Eunit
import Theorems.Thm_GlobalTheory_BK_hat_coe
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
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
variable {O K l e a ι} {κ : Type} [Fintype κ] [DecidableEq κ] {η H η' H' : ℕ}
open GlobalTheory.BK.Descent
variable {P : PhiMod O K l e a ι} (Δ : Descent P)
namespace GlobalTheory.BK.Descent
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] (f : Vec K a ι →ₗ[K] V) {v : Vec K a ι}
    (h : ∀ g, f (Δ.act g v) = f v) : f (Δ.avg v) = f v := by
  let _ := Fintype.ofFinite (TameGal K l e a)
  have h0 : (Nat.card (TameGal K l e a) : K) ≠ 0 := norm_ne_zero_iff.1 (by rw [norm_card]; simp)
  simp only [avg, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, h, Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul K, inv_smul_smul₀ h0]
end GlobalTheory.BK.Descent
