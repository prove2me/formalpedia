-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnnihOpen.isOpen_annihilator_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:26.832378+00:00
-- url     : https://prove2.me/submissions/fc68d621-cba2-4fe6-bfcb-4868c9044c3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenCharacterAnnihilator
import Theorems.Thm_GlobalTheory_CharDualMat_circle_eq_one_of_pow_near


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnnihOpen
namespace GlobalTheory.CompanionTheory.AnnihOpen
theorem _root_.solution :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)),
      IsCompact (A : Set (Fin n → k)) → IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} := by
  intro k _ _ _ _ ψ hψ n A hA
  let H : AddSubgroup (Fin n → k) :=
    { carrier := {ξ | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1}
      zero_mem' := by
        intro a _
        simp
      add_mem' := by
        intro x y hx hy a ha
        rw [add_dotProduct, AddChar.map_add_eq_mul, hx a ha, hy a ha, one_mul]
      neg_mem' := by
        intro x hx a ha
        rw [neg_dotProduct, AddChar.map_neg_eq_inv, hx a ha, inv_one] }
  have hdot : Continuous fun p : (Fin n → k) × (Fin n → k) => p.1 ⬝ᵥ p.2 :=
    continuous_fst.dotProduct continuous_snd
  have hcoe : Continuous fun z : Circle => (z : ℂ) := continuous_iff_le_induced.mpr fun U a ↦ a
  have hcont : Continuous fun p : (Fin n → k) × (Fin n → k) =>
      ‖((ψ (p.1 ⬝ᵥ p.2) : Circle) : ℂ) - 1‖ :=
    ((hcoe.comp (hψ.comp hdot)).sub continuous_const).norm
  have hU : IsOpen {p : (Fin n → k) × (Fin n → k) | ‖((ψ (p.1 ⬝ᵥ p.2) : Circle) : ℂ) - 1‖ < 1} :=
    isOpen_lt hcont continuous_const
  have hsub : ({0} : Set (Fin n → k)) ×ˢ (A : Set (Fin n → k)) ⊆
      {p : (Fin n → k) × (Fin n → k) | ‖((ψ (p.1 ⬝ᵥ p.2) : Circle) : ℂ) - 1‖ < 1} := by
    rintro ⟨x, a⟩ ⟨hx, -⟩
    have hx0 : x = 0 := hx
    subst hx0
    simp
  obtain ⟨V, W, hV, -, h0V, hAW, hVW⟩ := generalized_tube_lemma isCompact_singleton hA hU hsub
  have hmem : (H : Set (Fin n → k)) ∈ 𝓝 (0 : Fin n → k) := by
    refine Filter.mem_of_superset (hV.mem_nhds (h0V rfl)) ?_
    intro ξ hξ a ha
    apply GlobalTheory.CharDualMat.circle_eq_one_of_pow_near
    intro m
    have hma : m • a ∈ (A : Set (Fin n → k)) := SetLike.mem_coe.mpr (A.nsmul_mem ha m)
    have h1 := hVW (Set.mk_mem_prod hξ (hAW hma))
    rw [Set.mem_setOf_eq, dotProduct_smul, AddChar.map_nsmul_eq_pow, Circle.coe_pow] at h1
    exact h1
  exact AddSubgroup.isOpen_of_mem_nhds H hmem
end GlobalTheory.CompanionTheory.AnnihOpen
