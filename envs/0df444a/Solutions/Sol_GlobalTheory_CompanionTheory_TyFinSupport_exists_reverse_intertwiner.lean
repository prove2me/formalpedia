-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinSupport.exists_reverse_intertwiner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:28:16.836842+00:00
-- url     : https://prove2.me/submissions/117369ff-9690-4913-83ee-e8e7a5d1e51a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalSupportExists
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSupport_exists_generalizedInverse
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_Formalism_L2_NT_IsTeich_map_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinSupport
namespace GlobalTheory.CompanionTheory.TyFinSupport
theorem _root_.solution {G V W : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (Φ : V →ₗ[ℂ] W) (hΦ : Φ ≠ 0) (h : ∀ p, Φ ∘ₗ ρ p = σ p ∘ₗ Φ) :
    ∃ ψ : W →ₗ[ℂ] V, ψ ≠ 0 ∧ ∀ p, ψ ∘ₗ σ p = ρ p ∘ₗ ψ := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨g, hg⟩ := exists_generalizedInverse Φ
  let ψ : W →ₗ[ℂ] V := ∑ p : G, ρ p ∘ₗ g ∘ₗ σ p⁻¹
  have hinv : ∀ (p : G) (x : V), Φ (ρ p x) = σ p (Φ x) := fun p x => LinearMap.congr_fun (h p) x
  have hσ : ∀ (p : G) (w : W), σ p (σ p⁻¹ w) = w := fun p w => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hρ : ∀ (p : G) (v : V), ρ p⁻¹ (ρ p v) = v := fun p v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hgx : ∀ x, Φ (g (Φ x)) = Φ x := fun x => LinearMap.congr_fun hg x
  have hterm : ∀ (p : G) (x : V), Φ (ρ p (g (σ p⁻¹ (Φ x)))) = Φ x := by
    intro p x
    have e : σ p⁻¹ (Φ x) = Φ (ρ p⁻¹ x) := (hinv p⁻¹ x).symm
    rw [hinv, e, hgx, hinv, hσ]
  have hψ : ∀ x, Φ (ψ (Φ x)) = (Fintype.card G : ℂ) • Φ x := by
    intro x
    simp only [ψ, LinearMap.sum_apply, LinearMap.comp_apply, map_sum, hterm, Finset.sum_const,
      Finset.card_univ, Nat.cast_smul_eq_nsmul]
  refine ⟨ψ, ?_, ?_⟩
  · intro h0
    apply hΦ
    ext x
    have h1 := hψ x
    rw [h0] at h1
    simp only [LinearMap.zero_apply, map_zero] at h1
    have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simpa [hc] using h1.symm
  · intro q
    ext w
    simp only [ψ, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft q⁻¹) _ _ fun p => ?_
    simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]
    rw [← Module.End.mul_apply (ρ q), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
end GlobalTheory.CompanionTheory.TyFinSupport
