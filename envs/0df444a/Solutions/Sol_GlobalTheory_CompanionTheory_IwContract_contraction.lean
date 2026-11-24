-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwContract.contraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:12:14.774255+00:00
-- url     : https://prove2.me/submissions/41369623-c01e-4cb5-9aec-5892b3a31598

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriContraction
import Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_mem_iwahori_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_val_entry_le_one
import Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_isClosed_val_le_pow
import Theorems.Thm_GlobalTheory_CompanionTheory_IwContract_step
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_isCompact_iwahori
import Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_isOpen_iwahori


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix Topology MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwContract
open PositivityTheory.Rg.Tf.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
namespace GlobalTheory.CompanionTheory.IwContract
theorem _root_.solution {ϖ : Fˣ} (hϖ : IsUniformiser (ϖ : F)) {a : Fin n → ℤ} (ha : StrictlyDominant a)
    (γ : GL (Fin n) F) (hγ : γ ∈ iwDouble F (diagPow ϖ a)) :
    ∃ m ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F, ∃ t ∈ torusO F, m⁻¹ * γ * m = diagPow ϖ a * t := by
  obtain ⟨x, hx⟩ : ∃ x, x = diagPow ϖ a := ⟨_, rfl⟩
  rw [← hx] at hγ ⊢
  obtain ⟨u, hu, w, hw, hγe⟩ := hγ
  have hu' := mem_iwahori_iff.1 hu
  have hw' := mem_iwahori_iff.1 hw
  have hq : valuation F (ϖ : F) < 1 := hϖ.1
  obtain ⟨φ, hφ⟩ : ∃ φ : GL (Fin n) F → GL (Fin n) F, φ = fun m => x⁻¹ * (m⁻¹ * γ * m) := ⟨_, rfl⟩
  have hφc : Continuous φ := by
    rw [hφ]
    fun_prop
  let S : ℕ → Set (GL (Fin n) F) := fun k =>
    {m | m ∈ GlobalTheory.SmGL.iwahori F (Fin n) ∧ Near (valuation F (ϖ : F) ^ k) (φ m)}
  have hdec : ∀ k, S (k + 1) ⊆ S k := fun k m hm =>
    ⟨hm.1, hm.2.1, fun i j hij => (hm.2.2 i j hij).trans (pow_le_pow_right_of_le_one' hq.le (Nat.le_succ k))⟩
  have hne : ∀ k, (S k).Nonempty := by
    intro k
    induction k with
    | zero =>
      have e : φ u = w * u := by
        rw [hφ, hγe]
        group
      refine ⟨u, hu', ?_, fun i j _ => ?_⟩
      · rw [e]
        exact mul_mem hw' hu'
      · rw [e, pow_zero]
        exact val_entry_le_one (mul_mem hw' hu') i j
    | succ k ih =>
      obtain ⟨m, hm, hN⟩ := ih
      obtain ⟨m₁, hm₁, c', hc', he⟩ := step hϖ ha hN
      rw [← hx] at he
      have h0 : x * φ m = m⁻¹ * γ * m := by
        rw [hφ]
        group
      have e : φ (m * m₁) = c' := by
        have h1 : (m * m₁)⁻¹ * γ * (m * m₁) = m₁⁻¹ * ((x * φ m) * m₁) := by
          rw [h0]
          group
        rw [hφ]
        show x⁻¹ * ((m * m₁)⁻¹ * γ * (m * m₁)) = c'
        rw [h1, he]
        group
      refine ⟨m * m₁, mul_mem hm hm₁, ?_⟩
      rw [e, pow_succ]
      exact hc'
  have hIcl : IsClosed (GlobalTheory.SmGL.iwahori F (Fin n) : Set (GL (Fin n) F)) :=
    Subgroup.isClosed_of_isOpen _ (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori F (Fin n))
  have hcl : ∀ k, IsClosed (S k) := by
    intro k
    have e : S k = (GlobalTheory.SmGL.iwahori F (Fin n) : Set (GL (Fin n) F)) ∩
        (φ ⁻¹' (GlobalTheory.SmGL.iwahori F (Fin n) : Set (GL (Fin n) F)) ∩
          ⋂ i, ⋂ j, ⋂ _ : i ≠ j, (fun m => (φ m).val i j) ⁻¹'
            {y : F | valuation F y ≤ valuation F (ϖ : F) ^ k}) := by
      ext m
      simp only [S, Near, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter,
        SetLike.mem_coe]
    rw [e]
    refine hIcl.inter ((hIcl.preimage hφc).inter (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun _ => (isClosed_val_le_pow ϖ k).preimage ?_))
    exact (Units.continuous_val.matrix_elem i j).comp hφc
  have hcomp : IsCompact (S 0) :=
    (GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori F (Fin n)).of_isClosed_subset (hcl 0) fun m hm => hm.1
  obtain ⟨m, hm⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hdec hne hcomp hcl
  have hm' : ∀ k, m ∈ S k := Set.mem_iInter.1 hm
  have hoff : ∀ i j, i ≠ j → (φ m).val i j = 0 := by
    intro i j hij
    by_contra hne0
    have hv : valuation F ((φ m).val i j) ≠ 0 := (Valuation.ne_zero_iff _).2 hne0
    have : MulArchimedean (ValueGroupWithZero F) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    obtain ⟨k, hk⟩ := exists_pow_lt₀ hq (Units.mk0 _ hv)
    exact absurd ((hm' k).2.2 i j hij) (not_le.2 hk)
  refine ⟨m, mem_iwahori_iff.2 (hm' 0).1, φ m, ⟨(mem_iwahori_iff.2 (hm' 0).2.1).1, hoff⟩, ?_⟩
  rw [hφ]
  group
end GlobalTheory.CompanionTheory.IwContract
