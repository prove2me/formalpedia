-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.card_le_of_kaehler
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:25:14.454013+00:00
-- url     : https://prove2.me/submissions/80dde543-aeb6-48df-b24a-daadfec3111f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRing
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Reg_exists_unique_lift
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Reg_exists_span_of_derivations
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Reg_aeval_dual
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Reg_card_le_finrank_add

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
theorem _root_.solution (σ : Type) [Fintype σ] (Ω : Type) [Field Ω] [CharZero Ω] (u : σ → Ω)
    (V : Submodule ℂ (σ → ℂ)) (w : σ → ℂ) (F : MvPolynomial σ ℚ) (hF : aeval u F ≠ 0)
    (hFw : eval w (map (algebraMap ℚ ℂ) F) ≠ 0)
    (hker : ∀ g : MvPolynomial σ ℚ, aeval u g = 0 → eval w (map (algebraMap ℚ ℂ) g) = 0)
    (hV : ∀ g : MvPolynomial σ ℚ, aeval u g = 0 →
      (fun q => eval w (pderiv q (map (algebraMap ℚ ℂ) g))) ∈ V)
    (S : Subalgebra ℚ Ω) (hS : S = Algebra.adjoin ℚ (insert (aeval u F)⁻¹ (Set.range u)))
    (e : ℕ) (z : Fin e → S)
    (hz : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤) :
    Fintype.card σ ≤ Module.finrank ℂ V + e := by
  have huS : ∀ q, u q ∈ S := fun q => hS ▸ Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨q, rfl⟩)
  have haw : ∀ g : MvPolynomial σ ℚ, (aeval w g : ℂ) = eval w (map (algebraMap ℚ ℂ) g) := fun g => by
    rw [eval_map, aeval_def]
  obtain ⟨ψ, hψ, hψu⟩ := exists_unique_lift σ Ω ℂ u w
    (fun g hg => by rw [haw]; exact hker g hg) F hF
    (by rw [haw]; exact isUnit_iff_ne_zero.2 hFw) S hS huS
  obtain ⟨b, hb⟩ := exists_span_of_derivations S σ (fun q => ⟨u q, huS q⟩) e z hz ψ
  refine card_le_finrank_add _ _ e b fun v hv => ?_
  let t : σ → TrivSqZeroExt ℂ ℂ := fun q => TrivSqZeroExt.inl (w q) + TrivSqZeroExt.inr (v q)
  obtain ⟨Φ, hΦ, -⟩ := exists_unique_lift σ Ω (TrivSqZeroExt ℂ ℂ) u t
    (fun g hg => by
      obtain ⟨h1, h2⟩ := aeval_dual σ w v g
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [h1, hker g hg]; rfl
      · rw [h2]
        have := hv _ (hV g hg)
        exact this)
    F hF
    (by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, (aeval_dual σ w v F).1]
      exact isUnit_iff_ne_zero.2 hFw) S hS huS
  have hfst : (TrivSqZeroExt.fstHom ℚ ℂ ℂ).comp Φ = ψ := hψu _ fun q => by
    simp [hΦ, t]
  have := hb Φ hfst
  have hv' : (fun q => (Φ ⟨u q, huS q⟩).snd) = v := by
    funext q
    simp [hΦ, t]
  rwa [hv'] at this
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
