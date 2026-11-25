-- Prove2me | solution 1 for GlobalTheory.DegCnt.Unimod.invVol_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:16:30.75873+00:00
-- url     : https://prove2.me/submissions/2484b8b7-f1f0-4e63-8c87-1ac356d7c821

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntSmulLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexNeZero
import Theorems.Thm_GlobalTheory_DegCnt_Unimod_finite_between
import Theorems.Thm_GlobalTheory_DegCnt_Unimod_mem_smul_iff
import Theorems.Thm_GlobalTheory_DegCnt_Unimod_isLattice_smul
import Theorems.Thm_GlobalTheory_DegCnt_Unimod_relIndex_ne_zero
import Theorems.Thm_GlobalTheory_DegCnt_Unimod_exists_den
import Theorems.Thm_GlobalTheory_DegCnt_Unimod_inf_stab_smul
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_invVol_mul_pos_le_conj
import Theorems.Thm_GlobalTheory_IntMulIntegral_main
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Unimod
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.Unimod
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (G : Subgroup (V ≃ₗ[K] V)) (n : ℕ), (∀ s ∈ G, ((s : V →ₗ[K] V) - 1) ^ n = 0) → ∀ Λ Λ' : Submodule (𝓞 K) V, Submodule.IsLattice K Λ → Submodule.IsLattice K Λ' → (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ).relIndex (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ') ≠ 0 ∧ ∀ s ∈ G, GlobalTheory.HL.invVol (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ') (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) (s • Λ)) = GlobalTheory.HL.invVol (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ') (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ) := by
  intro K V _ _ _ _ _ _ _ G n hG Λ Λ' hΛ hΛ'
  refine ⟨relIndex_ne_zero G hΛ hΛ', fun s hs => ?_⟩
  let S : Submodule (𝓞 K) V → Subgroup (V ≃ₗ[K] V) := fun M =>
    G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) M
  have main : ∀ A B C : Submodule (𝓞 K) V, Submodule.IsLattice K A → Submodule.IsLattice K B →
      Submodule.IsLattice K C → _ := fun A B C hA hB hC =>
    GlobalTheory.HL.invVol_mul_pos_le_conj (S A) (S B) (S C) (relIndex_ne_zero G hA hB)
      (relIndex_ne_zero G hB hA) (relIndex_ne_zero G hA hC) (relIndex_ne_zero G hC hA)
  set d : ℝ := GlobalTheory.HL.invVol (S Λ) (S (s • Λ)) with hd
  have hdpos : 0 < d := (main Λ Λ (s • Λ) hΛ hΛ (isLattice_smul s hΛ)).2.1
  have hpow : ∀ m : ℕ, GlobalTheory.HL.invVol (S Λ) (S (s ^ m • Λ)) = d ^ m := by
    intro m
    induction m with
    | zero => simp [GlobalTheory.HL.invVol]
    | succ m ih =>
      have h1 := (main Λ (s • Λ) (s ^ (m + 1) • Λ) hΛ (isLattice_smul _ hΛ) (isLattice_smul _ hΛ)).1
      have h2 := (main Λ Λ (s ^ m • Λ) hΛ hΛ (isLattice_smul _ hΛ)).2.2.2 s
      have e1 : MulAut.conj s • S Λ = S (s • Λ) := (inf_stab_smul G hs Λ).symm
      have e2 : MulAut.conj s • S (s ^ m • Λ) = S (s ^ (m + 1) • Λ) := by
        rw [pow_succ', mul_smul]
        exact (inf_stab_smul G hs _).symm
      rw [e1, e2, ih] at h2
      rw [h1, h2, pow_succ']
  obtain ⟨b, hb, h₂⟩ := exists_den (hG s hs) hΛ
  obtain ⟨a, ha, h₁⟩ := exists_den (hG s⁻¹ (G.inv_mem hs)) hΛ
  have hfin := finite_between hΛ.fg ha hb
  have hmaps : ∀ m : ℕ, s ^ m • Λ ∈
      {M : Submodule (𝓞 K) V | (∀ x ∈ Λ, a • x ∈ M) ∧ ∀ x ∈ M, b • x ∈ Λ} := by
    intro m
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [mem_smul_iff, map_zsmul, ← inv_pow]
      exact h₁ m x hx
    · rw [mem_smul_iff] at hx
      simpa using h₂ m _ hx
  obtain ⟨i, j, hij, e⟩ := hfin.exists_lt_map_eq_of_forall_mem hmaps
  have hd1 : d = 1 := by
    have h : d ^ i = d ^ j := by rw [← hpow, ← hpow, e]
    by_contra hne
    exact hij.ne (pow_right_injective₀ hdpos hne h)
  have h := (main Λ' Λ (s • Λ) hΛ' hΛ (isLattice_smul s hΛ)).1
  rw [← hd, hd1, mul_one] at h
  exact h
end GlobalTheory.DegCnt.Unimod
