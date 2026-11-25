-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.exists_span_of_derivations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:34:16.583196+00:00
-- url     : https://prove2.me/submissions/fe38a98e-571f-43e9-bda5-06724f1856d3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
theorem _root_.solution (S : Type) [CommRing S] [Algebra ℚ S] (σ : Type) (u : σ → S) (e : ℕ)
    (z : Fin e → S)
    (hz : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤) (ψ : S →ₐ[ℚ] ℂ) :
    ∃ b : Fin e → σ → ℂ, ∀ Φ : S →ₐ[ℚ] TrivSqZeroExt ℂ ℂ,
      (TrivSqZeroExt.fstHom ℚ ℂ ℂ).comp Φ = ψ →
      (fun q => (Φ (u q)).snd) ∈ Submodule.span ℂ (Set.range b) := by
  classical
  have hmem : ∀ q, ∃ c : Fin e → S, ∑ i, c i • KaehlerDifferential.D ℚ S (z i) =
      KaehlerDifferential.D ℚ S (u q) := by
    intro q
    have h : KaehlerDifferential.D ℚ S (u q) ∈
        Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) := hz ▸ Submodule.mem_top
    exact (Submodule.mem_span_range_iff_exists_fun S).1 h
  choose c hc using hmem
  refine ⟨fun i q => ψ (c q i), fun Φ hΦ => ?_⟩
  have hfst : ∀ s, (Φ s).fst = ψ s := fun s => DFunLike.congr_fun hΦ s
  let _ : Module S ℂ := Module.compHom ℂ (ψ : S →+* ℂ)
  have hsm : ∀ (s : S) (x : ℂ), s • x = ψ s * x := fun _ _ => rfl
  have : IsScalarTower ℚ S ℂ := ⟨fun r s x => by
    rw [hsm, hsm, map_smul, smul_mul_assoc]⟩
  let d : Derivation ℚ S ℂ := Derivation.mk'
    (((TrivSqZeroExt.sndHom ℂ ℂ).restrictScalars ℚ).comp Φ.toLinearMap) (fun a b => by
      show (Φ (a * b)).snd = a • (Φ b).snd + b • (Φ a).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, hsm, hsm]
      simp [mul_comm])
  have hd : ∀ s, d s = (Φ s).snd := fun _ => rfl
  have key : ∀ q, (Φ (u q)).snd = ∑ i, ψ (c q i) * (Φ (z i)).snd := by
    intro q
    have h := congrArg d.liftKaehlerDifferential (hc q)
    rw [Derivation.liftKaehlerDifferential_comp_D, map_sum] at h
    rw [← hd, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, hsm, hd]
  have he : (fun q => (Φ (u q)).snd) = ∑ i, (Φ (z i)).snd • (fun q => ψ (c q i)) := by
    funext q
    rw [key, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  rw [he]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
