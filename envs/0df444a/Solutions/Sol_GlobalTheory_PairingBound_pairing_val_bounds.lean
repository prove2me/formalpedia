-- Prove2me | solution 1 for GlobalTheory.PairingBound.pairing_val_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:59:39.594269+00:00
-- url     : https://prove2.me/submissions/a37d00c1-32b3-49a3-9b20-d98822a453a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodDenominatorBound
import Theorems.Thm_GlobalTheory_PairingBound_val_nonneg
import Theorems.Thm_GlobalTheory_PairingBound_val_le_of_dvd
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.PairingBound
namespace GlobalTheory.PairingBound
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ i, 0 ≤ val_vp O l (algebraMap O K (B (e i) (f i))) ∧ val_vp O l (algebraMap O K (B (e i) (f i))) ≤ val_vp O l (algebraMap O K D) := by
  intro E _ _ _ c _ l hl O _ _ _ _ K _ _ _ hlm _ D hD _ I _ φ _ H _ _ ρ Fil B hLat hEig e f hGen i
  obtain ⟨hfree, -, -, -, -, -, hbij, halt, -⟩ := hLat
  obtain ⟨-, hsat, ⟨-, hsum⟩, -, horth⟩ := hEig
  obtain ⟨he, hf⟩ := hGen i
  haveI := hfree
  obtain ⟨-, ⟨g, hg0, hgs⟩, -, -, C, hC⟩ := hsat (φ i)
  have he0 : e i ≠ 0 := by
    intro h0
    rw [he, h0, Submodule.span_singleton_eq_bot.2 rfl] at hgs
    exact hg0 (Submodule.span_singleton_eq_bot.1 hgs.symm)
  have heL : e i ∈ eigLat ρ (φ i) := by rw [he]; exact Submodule.mem_span_singleton_self _
  rw [he] at hC
  let lam : H →ₗ[O] O := ((LinearEquiv.toSpanNonzeroSingleton O H (e i) he0).symm.toLinearMap).comp
    (Submodule.linearProjOfIsCompl _ C hC)
  have hlam : lam (e i) = 1 := by
    simp only [lam, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have hp : (Submodule.linearProjOfIsCompl _ C hC) (e i) = ⟨e i, Submodule.mem_span_singleton_self _⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨e i, Submodule.mem_span_singleton_self _⟩
    rw [hp, LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  obtain ⟨h, hh⟩ := hbij.2 lam
  have hBeh : B (e i) h = -1 := by
    rw [← LinearMap.IsAlt.neg halt h (e i), hh, hlam]
  have hle : (⨆ σ : E →+* K, eigLat ρ σ) ≤ LinearMap.ker (B (e i)) ⊔ (O ∙ f i) := by
    refine iSup_le fun σ => ?_
    by_cases hσ : σ = bar (φ i)
    · subst hσ; rw [hf]; exact le_sup_right
    · refine le_sup_of_le_left fun y hy => ?_
      rw [LinearMap.mem_ker]
      have h0 := horth (φ i) σ hσ _ heL _ hy
      simp only [inK, TensorProduct.mk_apply, LinearMap.BilinForm.baseChange_tmul, mul_one, Algebra.smul_def]
        at h0
      exact (IsFractionRing.injective O K) (by rw [h0, map_zero])
  obtain ⟨k, hk, y, hy, hky⟩ := Submodule.mem_sup.1 (hle (hsum h))
  obtain ⟨u, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hdiv : B (e i) (f i) ∣ D := by
    have h1 := congrArg (B (e i)) hky
    rw [map_add, LinearMap.mem_ker.1 hk, zero_add, map_smul, map_smul, hBeh, smul_eq_mul, smul_eq_mul] at h1
    exact ⟨-u, by linear_combination h1⟩
  exact ⟨val_nonneg O l hl.ne_zero hlm _, val_le_of_dvd O l hl.ne_zero hlm hD hdiv⟩
end GlobalTheory.PairingBound
