-- Prove2me | solution 1 for GlobalTheory.RankStrata.exists_fullRank_sub_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:49.487202+00:00
-- url     : https://prove2.me/submissions/cf734c58-dcba-449f-b69b-f0b2466cd760

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNonzeroMinorOfRankStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatPartitionOfUnityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatReindexRowsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatMinorSupportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzBruhatFullRankModuloTranslates
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RankStrata_Nsp_le_SB
import Theorems.Thm_GlobalTheory_T_exists_nonzero_minor_of_rank
import Theorems.Thm_GlobalTheory_T_schwartzBruhat_minor_support
import Theorems.Thm_GlobalTheory_T_schwartzBruhat_partition_of_unity
import Theorems.Thm_GlobalTheory_T_schwartzBruhat_reindex_rows
import Theorems.Thm_P2M_GlobalTheory_RankChart_toRows__dil_a78c4f6a5c7f
import Theorems.Thm_P2M_GlobalTheory_RankChart_toRows__shear_d5dffcf9ff0a
import Theorems.Thm_P2M_GlobalTheory_RankChart_toRows__stack_b71dac95216e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] P2M_GlobalTheory_RankChart_toRows__dil_a78c4f6a5c7f
attribute [local simp] P2M_GlobalTheory_RankChart_toRows__shear_d5dffcf9ff0a
attribute [local simp] P2M_GlobalTheory_RankChart_toRows__stack_b71dac95216e



set_option autoImplicit false
open GlobalTheory.WeilM Matrix
noncomputable section
open GlobalTheory GlobalTheory.RankStrata
namespace GlobalTheory.RankStrata
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) →
    ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ Ψ₀ ∈ SB (Matrix (Fin n) (Fin d) k), (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≠ n → Ψ₀ Y = 0) ∧
      Ψ - Ψ₀ ∈ Submodule.span ℂ {Z | ∃ g : GL (Fin n) k, ∃ Ψ' ∈ SB (Matrix (Fin n) (Fin d) k), Z = GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ'} := by
  intro k _ _ _ _ n d ν ϖ hϖ hν Ψ hΨ
  classical
  have piece : ∀ ρ < n, ∀ f : Matrix (Fin n) (Fin d) k → ℂ, f ∈ SB (Matrix (Fin n) (Fin d) k) →
      ∀ (S : Fin ρ → Fin n) (τ : Fin ρ → Fin d), (∀ Y, f Y ≠ 0 → (Y.submatrix S τ).det ≠ 0) →
      ∃ Φ ∈ Nsp k (Fin n) (Fin d) ν, ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≤ ρ → Φ Y = f Y := by
    intro ρ hρ f hf S τ hS
    by_cases h0 : ∀ Y, f Y = 0
    · exact ⟨0, Submodule.zero_mem _, fun Y _ => by simp [h0 Y]⟩
    push_neg at h0
    obtain ⟨Y0, hY0⟩ := h0
    have hinj : Function.Injective S := by
      intro i j hij
      by_contra hne
      exact hS Y0 hY0 (Matrix.det_zero_of_row_eq hne (by ext l; simp [hij]))
    let e' : Fin ρ ⊕ ↥(Set.range S)ᶜ ≃ Fin n :=
      (Equiv.sumCongr (Equiv.ofInjective S hinj) (Equiv.refl _)).trans (Equiv.Set.sumCompl _)
    have he' : ∀ i, e'.symm (S i) = Sum.inl i := fun i => by
      rw [Equiv.symm_apply_eq]; simp [e']
    haveI : Nonempty ↥(Set.range S)ᶜ := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have := Fintype.card_congr e'
      simp at this
      omega
    have hT := GlobalTheory.T.schwartzBruhat_reindex_rows k (Fin ρ ⊕ ↥(Set.range S)ᶜ) (Fin n) (Fin d) ν e'
    obtain ⟨Φ', hΦ', hΦ'f⟩ := GlobalTheory.T.schwartzBruhat_minor_support k (Fin ρ) (↥(Set.range S)ᶜ) (Fin d) ν ϖ hϖ hν τ
      (fun Z => f (Z.submatrix e'.symm id)) (hT.1 f hf) (fun Z hZ => by
        have := hS _ hZ
        rwa [Matrix.submatrix_submatrix, show (e'.symm ∘ S) = Sum.inl from funext he'] at this)
    have hT2 := GlobalTheory.T.schwartzBruhat_reindex_rows k (Fin n) (Fin ρ ⊕ ↥(Set.range S)ᶜ) (Fin d) ν e'.symm
    refine ⟨_, hT2.2 Φ' hΦ', fun Y hY => ?_⟩
    simp only [Equiv.symm_symm]
    rw [hΦ'f _ (by rw [show (id : Fin d → Fin d) = ⇑(Equiv.refl (Fin d)) from rfl, Matrix.rank_submatrix]; simpa using hY)]
    simp [Matrix.submatrix_submatrix]
  have step : ∀ ρ < n, ∀ g ∈ SB (Matrix (Fin n) (Fin d) k),
      (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank < ρ → g Y = 0) →
      ∃ Φ ∈ Nsp k (Fin n) (Fin d) ν, ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≤ ρ → Φ Y = g Y := by
    intro ρ hρ g hg hg0
    haveI : T2Space k := by
      letI := IsTopologicalAddGroup.rightUniformSpace k
      haveI := isUniformAddGroup_of_addCommGroup (G := k)
      infer_instance
    have hsp := GlobalTheory.T.schwartzBruhat_partition_of_unity k (Fin n) (Fin d) ((Fin ρ → Fin n) × (Fin ρ → Fin d))
      (fun i => {Y : Matrix (Fin n) (Fin d) k | (Y.submatrix i.1 i.2).det ≠ 0})
      (fun i => isOpen_ne_fun ((continuous_id.matrix_submatrix i.1 i.2).matrix_det) continuous_const) g hg
      (fun Y hY => by
        have : ρ ≤ Y.rank := by
          by_contra h
          exact hY (hg0 Y (by omega))
        obtain ⟨S, τ, h⟩ := GlobalTheory.T.exists_nonzero_minor_of_rank k _ _ ρ Y this
        exact ⟨(S, τ), h⟩)
    refine Submodule.span_induction
      (p := fun g _ => ∃ Φ ∈ Nsp k (Fin n) (Fin d) ν, ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≤ ρ → Φ Y = g Y)
      ?_ ?_ ?_ ?_ hsp
    · rintro f ⟨hf, i, hi⟩
      exact piece ρ hρ f hf i.1 i.2 hi
    · exact ⟨0, Submodule.zero_mem _, fun _ _ => rfl⟩
    · rintro x y _ _ ⟨Φ, hΦ, h⟩ ⟨Φ', hΦ', h'⟩
      exact ⟨Φ + Φ', Submodule.add_mem _ hΦ hΦ', fun Y hY => by simp [h Y hY, h' Y hY]⟩
    · rintro c x _ ⟨Φ, hΦ, h⟩
      exact ⟨c • Φ, Submodule.smul_mem _ c hΦ, fun Y hY => by simp [h Y hY]⟩
  have ind : ∀ ρ ≤ n, ∃ Ψρ ∈ SB (Matrix (Fin n) (Fin d) k),
      (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank < ρ → Ψρ Y = 0) ∧ Ψ - Ψρ ∈ Nsp k (Fin n) (Fin d) ν := by
    intro ρ
    induction ρ with
    | zero => intro _; exact ⟨Ψ, hΨ, fun Y h => absurd h (Nat.not_lt_zero _), by simp⟩
    | succ ρ ih =>
      intro hρ
      obtain ⟨Ψρ, hSB, h0, hN⟩ := ih (by omega)
      obtain ⟨Φ, hΦ, hΦe⟩ := step ρ (by omega) Ψρ hSB h0
      refine ⟨Ψρ - Φ, Submodule.sub_mem _ hSB (Nsp_le_SB _ _ ν hΦ), fun Y hY => ?_, ?_⟩
      · simp [hΦe Y (by omega)]
      · have : Ψ - (Ψρ - Φ) = (Ψ - Ψρ) + Φ := by abel
        rw [this]; exact Submodule.add_mem _ hN hΦ
  obtain ⟨Ψ₀, h1, h2, h3⟩ := ind n le_rfl
  refine ⟨Ψ₀, h1, fun Y hY => h2 Y (lt_of_le_of_ne ?_ hY), h3⟩
  simpa using Matrix.rank_le_card_height Y
end GlobalTheory.RankStrata
