-- Prove2me | solution 1 for GlobalTheory.HL.CongFin.mem_stab_of_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:33:13.06341+00:00
-- url     : https://prove2.me/submissions/a527ba41-dde6-4a6c-bc0d-30e72b007b60

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPowSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruenceSubgroupLatticeStabilizer
import Theorems.Thm_GlobalTheory_HL_CongFin_smul_mem_of
import Theorems.Thm_GlobalTheory_HL_CongFin_exists_pow_smul_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_PowSmulMem_exists_pow_smul_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CongFin
variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] {O : Subring E}
namespace GlobalTheory.HL.CongFin
theorem _root_.solution {p : E} (hp : p ∈ O) (hdiv : ∀ e : E, ∃ a : ℕ, p ^ a * e ∈ O)
    (Λ : Submodule O V) (hΛ : Λ.FG) (hΛ' : Submodule.span E (Λ : Set V) = ⊤) {N : ℕ} (hN : 1 ≤ N)
    (g : V ≃ₗ[E] V) (hg : ∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = p ^ N • w) :
    g ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ := by
  have hg1 : ∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = p • w := by
    intro v hv
    obtain ⟨w, hw, h⟩ := hg v hv
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
    exact ⟨p ^ M • w, smul_mem_of Λ (O.pow_mem hp M) hw, by rw [h, pow_add, pow_one, mul_smul]⟩
  have hle : ∀ v ∈ Λ, g v ∈ Λ := by
    intro v hv
    obtain ⟨w, hw, h⟩ := hg1 v hv
    rw [eq_add_of_sub_eq h]
    exact Λ.add_mem (smul_mem_of Λ hp hw) hv
  have hit : ∀ k : ℕ, ∀ v ∈ Λ, ∃ u ∈ Λ, ∃ w ∈ Λ, v = g u + p ^ k • w := by
    intro k v hv
    induction k with
    | zero => exact ⟨0, Λ.zero_mem, v, hv, by simp⟩
    | succ k ih =>
      obtain ⟨u, hu, w, hw, e⟩ := ih
      obtain ⟨w', hw', e'⟩ := hg1 w hw
      refine ⟨u + p ^ k • w, Λ.add_mem hu (smul_mem_of Λ (O.pow_mem hp k) hw), -w',
        Λ.neg_mem hw', ?_⟩
      rw [e, map_add, map_smul, eq_add_of_sub_eq e', pow_succ, mul_smul]
      simp only [smul_add, smul_neg]
      abel
  let Λ1 : Submodule O V := Λ.map (g.symm.toLinearMap.restrictScalars O)
  obtain ⟨a, ha⟩ := exists_pow_smul_mem hp hdiv Λ1 Λ (hΛ.map _) hΛ'
  rw [mem_stab_iff]
  refine fun v => ⟨fun hv => ?_, hle v⟩
  obtain ⟨u, hu, w, hw, e⟩ := hit a _ hv
  have : v = u + p ^ a • g.symm w := g.injective (by rw [e]; simp)
  rw [this]
  exact Λ.add_mem hu (ha _ ⟨w, hw, rfl⟩)
end GlobalTheory.HL.CongFin
