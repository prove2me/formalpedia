-- Prove2me | solution 1 for GlobalTheory.FlatFactor.flCol_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:03:43.836122+00:00
-- url     : https://prove2.me/submissions/b3facb5b-9870-4aff-8d28-53bfb3b61593

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegratedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelAllNonFreeUnreadEntriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelIntegratesFreeEntriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqZeroOfFlatMapColumnZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFactorThroughFlatMapFourierJacobiColumnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapFourierJacobiFactorsLocalFlat
import Theorems.Thm_GlobalTheory_FlatFactor_ch_add_mat
import Theorems.Thm_GlobalTheory_FlatFactor_continuous_ch
import Theorems.Thm_GlobalTheory_FlatFactor_kerRed_empty
import Theorems.Thm_GlobalTheory_FlatFactor_mem_SB_addChar_mul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_StepData_IntM_neg
import Theorems.Thm_GlobalTheory_StepData_MaxM_neg
import Theorems.Thm_GlobalTheory_T_exists_factor_through_flatMapFourierJacobiColumn
import Theorems.Thm_GlobalTheory_T_flatFactorReduction_kernel_all_nonFreeUnread_entries
import Theorems.Thm_GlobalTheory_T_flatFactorReduction_kernel_integrates_free_entries
import Theorems.Thm_GlobalTheory_T_kernelReduction_extend_evaluated_integrated
import Theorems.Thm_GlobalTheory_T_partialReduction_eq_zero_of_flatMapColumn_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory.FlatFactor
namespace GlobalTheory.FlatFactor
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val < ρ ∧ ¬ Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l, r = Sum.inr l ∧ ρ ≤ l.val ∧ ∀ i, q = Sum.inr i → i.val = ρ) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ ≤ i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → L Φ' = (ψ (ch (Matrix.single r q a)) : ℂ) • L Φ) → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → (∀ l l' : Fin c, l.val < ρ → ρ ≤ l'.val → u.val l l' = 0) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∃ L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ.1 → L Φ = L₀ Ψ := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν n n' _ _ _ _ c ρ M _ _ L hc H1 H2 H3 H4
  set Mt := Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k
  set β : Mt := basePt c (0 : Matrix n n' k)
  have tw : ∀ (f : Mt → k), Continuous f → ∀ Θ : SB Mt, (fun t => (ψ (f t) : ℂ) * Θ.1 t) ∈ SB Mt :=
    fun f hf Θ => mem_SB_addChar_mul ψ hψc f hf Θ.1 Θ.2
  let T : SB Mt → SB Mt := fun Θ => ⟨fun t => (ψ (ch t) : ℂ) * Θ.1 t, tw _ continuous_ch Θ⟩
  let L' : SB Mt →ₗ[ℂ] M :=
    { toFun := fun Θ => L (T Θ)
      map_add' := fun Θ₁ Θ₂ => by
        show L (T (Θ₁ + Θ₂)) = L (T Θ₁) + L (T Θ₂)
        rw [← map_add]; congr 1; apply Subtype.ext; funext t
        show (ψ (ch t) : ℂ) * (Θ₁.1 t + Θ₂.1 t) = (ψ (ch t) : ℂ) * Θ₁.1 t + (ψ (ch t) : ℂ) * Θ₂.1 t
        ring
      map_smul' := fun a Θ => by
        show L (T (a • Θ)) = a • L (T Θ)
        rw [← map_smul]; congr 1; apply Subtype.ext; funext t
        show (ψ (ch t) : ℂ) * (a * Θ.1 t) = a * ((ψ (ch t) : ℂ) * Θ.1 t)
        ring }
  have hL' : ∀ Θ, L' Θ = L (T Θ) := fun _ => rfl

  have hTw : TwLaw ρ ψ L' := by
    intro u hN hblk Θ Θ' Θ'' h' h''
    rw [hL', hL']
    have := H4 u hN hblk (T Θ'') (T Θ') (fun t => by
      simp only [T, h', h'']
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
      rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 3; ring)
    exact this

  have hS1 : KerRed ν (evC n n' c ρ) (itB n n' c ρ) β L' := by
    refine GlobalTheory.T.kernelReduction_extend_evaluated_integrated k ψ ν hψc hψ1 hν _ _ M L' β ∅ ∅ _ _ (Finset.empty_subset _) (Finset.empty_subset _) ?_
      (kerRed_empty ν β L') ?_ ?_
    · rw [Finset.disjoint_left]
      rintro ⟨r, q⟩ h1 h2
      simp only [evC, itB, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rcases h1 with ⟨i, hq, -, hfr⟩ | ⟨l, hr, hl, hq⟩
      · exact hfr h2.1
      · subst hr
        rcases q with q | q
        · simp [Free] at h2; omega
        · have := hq q rfl; simp [Free] at h2; omega
    · rintro ⟨r, q⟩ he - b Θ Θ' hΘ
      simp only [evC, Finset.mem_filter, Finset.mem_univ, true_and] at he
      rw [hL', hL']
      rcases he with he | he
      · exact H1 r q he b (T Θ) (T Θ') (fun t => by simp only [T, hΘ]; ring)
      · exact H2 r q he b (T Θ) (T Θ') (fun t => by simp only [T, hΘ]; ring)
    · rintro ⟨r, q⟩ he - a Θ Θ' hΘ
      simp only [itB, Finset.mem_filter, Finset.mem_univ, true_and] at he
      rw [hL', hL']
      set E : Mt := Matrix.single r q a
      let Φ' : SB Mt := ⟨fun t => (ψ (ch (t + E)) : ℂ) * Θ'.1 t, tw _ (continuous_ch.comp (continuous_add_right E)) Θ'⟩
      have h3 := H3 r q he.1 he.2 a (T Θ) Φ' (fun t => by
        show (ψ (ch (t + E)) : ℂ) * Θ'.1 t = (ψ (ch (t + E)) : ℂ) * Θ.1 (t + E)
        rw [hΘ])
      have hT : T Θ' = (ψ (-ch E) : ℂ) • Φ' := by
        ext t
        show (ψ (ch t) : ℂ) * Θ'.1 t = (ψ (-ch E) : ℂ) * ((ψ (ch (t + E)) : ℂ) * Θ'.1 t)
        have hm : ∀ x y : k, (ψ x : ℂ) * ψ y = ψ (x + y) := by
          intro x y; rw [AddChar.map_add_eq_mul, Circle.coe_mul]
        rw [← mul_assoc, hm, ch_add_mat, show -ch E + (ch t + ch E) = ch t by ring]
      rw [hT, map_smul, h3, smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel,
        AddChar.map_zero_eq_one, Circle.coe_one, one_smul]
  have hS2 := GlobalTheory.T.flatFactorReduction_kernel_all_nonFreeUnread_entries k ψ ν hψc hψ1 hν n n' c ρ M L' hc hTw hS1
  have hS3 := GlobalTheory.T.flatFactorReduction_kernel_integrates_free_entries k ψ ν hψc hψ1 hν n n' c ρ M L' hc hTw hS2
  refine GlobalTheory.T.exists_factor_through_flatMapFourierJacobiColumn k ψ ν hψc hν n n' c (ρ + 1) (by omega) (by omega) M L ?_
  intro Φ hΦ
  let Θ : SB Mt := ⟨fun t => (ψ (-ch t) : ℂ) * Φ.1 t, tw _ continuous_ch.neg Φ⟩
  have hΘ : T Θ = Φ := by
    ext t
    simp only [T, Θ]
    rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one,
      Circle.coe_one, one_mul]
  have := hS3 Θ (GlobalTheory.T.partialReduction_eq_zero_of_flatMapColumn_zero k ψ ν n n' c ρ hc Φ.1 hΦ)
  rw [hL', hΘ] at this
  exact this
end GlobalTheory.FlatFactor
