-- Prove2me | solution 1 for GlobalTheory.TorsionCoset.exists_isReps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:15:27.12578+00:00
-- url     : https://prove2.me/submissions/e7b87bbd-b767-4ab7-9e13-a4721a265c74

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TBNFinal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroOnCoset
import Theorems.Thm_GlobalTheory_TorsionCoset_natCast_smul_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.TorsionCoset
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.TorsionCoset
theorem _root_.solution (X : PT E) (n : ℕ) (hn : n ≠ 0) :
    ∃ K, IsReps X (n ^ 2) 1 ((n : ℂ) • LinearMap.id) K := by
  classical
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hsq : ∀ x : Vsp X.dim, ((n ^ 2 : ℕ) : ℂ) • x = (n : ℂ) • (n : ℂ) • x := fun x => by
    rw [smul_smul]; push_cast; rw [sq]
  let S : Set (Fin 1 → Vsp X.dim) :=
    {b | (n : ℂ) • (n : ℂ) • b 0 ∈ X.L ∧ (n : ℂ) • b 0 ∈ ZSpan.fundamentalDomain X.b}
  have hS : S.Finite := by
    have hb := ZSpan.setFinite_inter X.b
      ((ZSpan.fundamentalDomain_isBounded X.b).smul₀ (n : ℂ))
    refine Set.Finite.of_injOn (f := fun b => (n : ℂ) • (n : ℂ) • b 0) ?_ ?_ hb
    · intro b hb
      exact ⟨Set.smul_mem_smul_set hb.2, hb.1⟩
    · intro b _ c _ h
      funext k
      rw [Subsingleton.elim k 0]
      exact smul_right_injective _ hn' (smul_right_injective _ hn' h)
  refine ⟨hS.toFinset, fun b hb k => ?_, fun b hb => ?_⟩
  · rw [Subsingleton.elim k 0, hsq]
    exact (hS.mem_toFinset.1 hb).1
  · have hb0 := hb 0
    rw [hsq] at hb0
    have hfl : (n : ℂ) • b 0 - ZSpan.fract X.b ((n : ℂ) • b 0) ∈ X.L := by
      rw [ZSpan.fract_apply, sub_sub_cancel]
      exact (ZSpan.floor X.b _).2
    refine ⟨fun _ => (n : ℂ)⁻¹ • ZSpan.fract X.b ((n : ℂ) • b 0), ⟨hS.mem_toFinset.2 ⟨?_, ?_⟩,
      fun k => ?_⟩, ?_⟩
    · simp only [smul_inv_smul₀ hn']
      have := sub_mem hb0 (natCast_smul_mem X hfl n)
      rwa [smul_sub, sub_sub_cancel] at this
    · simp only [smul_inv_smul₀ hn']
      exact ZSpan.fract_mem_fundamentalDomain X.b _
    · rw [Subsingleton.elim k 0]
      simpa only [LinearMap.smul_apply, LinearMap.id_apply, smul_sub, smul_inv_smul₀ hn'] using hfl
    · rintro c ⟨hc, hc'⟩
      have h1 := (hS.mem_toFinset.1 hc).2
      have h2 := hc' 0
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_sub] at h2
      funext k
      rw [Subsingleton.elim k 0, eq_inv_smul_iff₀ hn', ← (ZSpan.fract_eq_self.2 h1),
        ZSpan.fract_eq_fract, neg_add_eq_sub]
      exact h2
end GlobalTheory.TorsionCoset
