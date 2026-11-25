-- Prove2me | solution 1 for GlobalTheory.BrauerZero.central_case
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:01:57.523697+00:00
-- url     : https://prove2.me/submissions/03734f0f-697f-4e9c-bd00-70aac7a218db

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__BrauerDegreeZero_fefd58e19a2fa426
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInductionIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersIffSubCharacters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleCharacterLinearOrInducedAbelianByPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IndMulClassFunEqIndMulRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemClosureInducedCentralByPrimePower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndApplyOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionFromSubgroupTransStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionMemInducedDegreeOneCharDiffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedOneSubIndexMemDegreeOneCharacterDiffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLtCommutatorMemOfNeTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BrauerDegreeZero
import Theorems.Thm_GlobalTheory_BrauerZero_inducedClassFunction_mem_degreeOneCharacterDiff
import Theorems.Thm_GlobalTheory_BrauerZero_ind_one_sub_index_mem_degreeOneDiff_nilpotent
import Theorems.Thm_GlobalTheory_BI_irrChar_linear_or_induced
import Theorems.Thm_GlobalTheory_BI_isChar_induction
import Theorems.Thm_GlobalTheory_BI_isChar_mem_virt_complex
import Theorems.Thm_GlobalTheory_BI_isChar_one
import Theorems.Thm_GlobalTheory_BI_mem_virt_iff_sub
import Theorems.Thm_GlobalTheory_BrauerZero_ind_apply_one
import Theorems.Thm_GlobalTheory_BrauerZero_ind_const
import Theorems.Thm_GlobalTheory_BrauerZero_ind_sub
import Theorems.Thm_GlobalTheory_BrauerZero_ind_top
import Theorems.Thm_GlobalTheory_isChar_restrict_conj_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BrauerZero
namespace GlobalTheory.BrauerZero
theorem _root_.solution (G : Type) [Group G] [Finite G]
    (hG : ∃ l : ℕ, l.Prime ∧ ∀ y : G, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center G)
    (IH : ∀ T : Subgroup G, T ≠ ⊤ → ∀ f ∈ Virt ℂ ℂ T, f 1 = 0 → f ∈ D0 T) :
    ∀ f ∈ Virt ℂ ℂ G, f 1 = 0 → f ∈ D0 G := by
  classical
  obtain ⟨l, hl, hc⟩ := hG
  have : Fact l.Prime := ⟨hl⟩
  have hq : IsPGroup l (G ⧸ Subgroup.center G) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨j, hj⟩ := hc y
    exact ⟨j, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hj⟩
  have := hq.isNilpotent
  haveI : Group.IsNilpotent G :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (Subgroup.center G)) (by simp)
  have hab : AbByP G := ⟨l, hl, Subgroup.center G, inferInstance,
    fun a _ b hb => Subgroup.mem_center_iff.1 hb a, fun g => hc g⟩
  have C : ∀ χ : G → ℂ, IsChar ℂ ℂ χ → χ - (fun _ => χ 1) ∈ D0 G := by
    refine isChar_induction ℂ ℂ G (fun χ => χ - (fun _ => χ 1) ∈ D0 G) ?_ ?_
    · have e : (0 : G → ℂ) - (fun _ => (0 : G → ℂ) 1) = 0 := by funext g; simp
      rw [e]; exact zero_mem _
    · intro φ c hφ _ hQ
      have e : (φ + c) - (fun _ => (φ + c) 1) = (φ - fun _ => φ 1) + (c - fun _ => c 1) := by
        funext g; simp only [Pi.add_apply, Pi.sub_apply]; ring
      rw [e]
      refine add_mem ?_ hQ
      rcases irrChar_linear_or_induced ℂ G φ hab hφ with ⟨lam, hlam⟩ | ⟨T, hT, ψ, hψ, rfl⟩
      · have hφc : IsChar ℂ ℂ φ := by obtain ⟨n, ρ, -, h⟩ := hφ; exact ⟨n, ρ, h⟩
        have hcl := (isChar_restrict_conj_one ℂ ℂ G φ hφc).2.1
        refine AddSubgroup.subset_closure ⟨⊤, lam.comp (⊤ : Subgroup G).subtype, ?_⟩
        have e1 : (fun h : (⊤ : Subgroup G) => ((lam.comp (⊤ : Subgroup G).subtype h : ℂˣ) : ℂ)) =
            fun h : (⊤ : Subgroup G) => φ (h : G) := by
          funext h; simp [hlam]
        rw [e1, ind_top φ hcl, ind_top (fun _ : G => (1 : ℂ)) (fun _ _ => rfl)]
        funext g; simp [hlam]
      · obtain ⟨n, hn, -⟩ := (isChar_restrict_conj_one ℂ ℂ T ψ hψ).2.2
        have hψV : ψ - (fun _ => ψ 1) ∈ Virt ℂ ℂ T := by
          refine sub_mem (isChar_mem_virt_complex hψ) ?_
          have e2 : (fun _ : T => ψ 1) = n • (fun _ : T => (1 : ℂ)) := by funext; simp [hn]
          rw [e2]; exact nsmul_mem (isChar_mem_virt_complex (isChar_one ℂ ℂ T)) n
        have h1 := inducedClassFunction_mem_degreeOneCharacterDiff T _ (IH T hT _ hψV (by simp))
        have h2 := ind_one_sub_index_mem_degreeOneDiff_nilpotent T.index T le_rfl
        have key : ind T ψ - (fun _ => ind T ψ 1) = ind T (ψ - fun _ => ψ 1) +
            (n : ℤ) • (ind T (fun _ => (1 : ℂ)) - fun _ => (T.index : ℂ)) := by
          rw [ind_sub]; funext g
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, ind_apply_one, hn, ind_const T (n : ℂ) g,
            zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply, Pi.natCast_apply]
          push_cast; ring
        rw [key]; exact add_mem h1 (zsmul_mem h2 _)
  intro f hf hf1
  obtain ⟨a, b, ha, hb, rfl⟩ := (mem_virt_iff_sub ℂ ℂ G f).1 hf
  have hab1 : a 1 = b 1 := by simpa [sub_eq_zero] using hf1
  have e : a - b = (a - fun _ => a 1) - (b - fun _ => b 1) := by funext g; simp [hab1]
  rw [e]; exact sub_mem (C a ha) (C b hb)
end GlobalTheory.BrauerZero
