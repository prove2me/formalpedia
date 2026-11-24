-- Prove2me | solution 1 for GlobalTheory.Relab.relab_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:26:03.570159+00:00
-- url     : https://prove2.me/submissions/9d9d27aa-d3fd-45e1-97ed-c333c0795ac8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RelabelEmbeddingsGoodBijectiveConjCompat
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.Relab
namespace GlobalTheory.Relab
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ → Function.Bijective (relab c σ) ∧ (∀ τ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0) ∧ (∀ τ, relab c σ (conjEmb τ) = conjEmb (relab c σ τ)) ∧ ∀ (Dw : Datum H) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) := by
  intro E _ _ _ H l c σ hσ
  classical
  have hinj : Function.Injective (relab c σ) := by
    intro τ₁ τ₂ h
    ext a
    have := congrArg (fun f : E →+* ℂ => f a) h
    exact congrArg Subtype.val (σ.injective this)
  have h0 : H.rt0 ≠ 0 := by
    intro h
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    have hd : (H.d : ℂ) = 0 := by linear_combination this
    exact H.d_prime.ne_zero (by exact_mod_cast hd)
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hrel : ∀ τ' : E →+* ℂ, (relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0) := by
    intro τ'
    have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
      simpa using this
    have hsq : (τ' (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      rw [H.sqrt_neg_disc_sq, ← map_pow, hE, map_neg, map_natCast]
    have hval : relab c σ τ' (H.rt : E) = σ ⟨τ' (H.rt : E), c.conj τ' _⟩ := rfl
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hx | hx
    · refine ⟨fun _ => hx, fun _ => ?_⟩
      rw [hval, ← hσ0]
      exact congrArg σ (Subtype.ext hx)
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · exfalso
        have h1 : σ ⟨τ' (H.rt : E), c.conj τ' _⟩ = -σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ := by
          rw [← map_neg]
          exact congrArg σ (Subtype.ext hx)
        rw [← hval, h, hσ0] at h1
        exact h0 (by linear_combination h1 / 2)
      · exfalso
        exact h0 (by linear_combination (h.symm.trans hx) / 2)
  have hsurj := Finite.injective_iff_surjective.1 hinj
  refine ⟨⟨hinj, hsurj⟩, hrel, ?_, ?_⟩
  · intro τ
    ext a
    have key : ∀ (ρ : E →+* ℂ) (x : E), conjEmb ρ x = ρ (IsCMField.complexConj E x) := fun ρ x =>
      (IsCMField.complexEmbedding_complexConj E ρ x).symm
    rw [key]
    exact congrArg σ (Subtype.ext (key τ a))
  · intro Dw g e τ
    obtain ⟨τ₀, rfl⟩ := hsurj τ
    have hcard : Nat.card {i // relab c σ (e i).1 = relab c σ τ₀} = Dw.mult τ₀ := by
      have e1 : {i // relab c σ (e i).1 = relab c σ τ₀} ≃ {i // (e i).1 = τ₀} :=
        Equiv.subtypeEquivRight (fun i => hinj.eq_iff)
      have e2 : {i // (e i).1 = τ₀} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀} :=
        e.subtypeEquiv (fun _ => Iff.rfl)
      have e3 : {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀} ≃ Fin (Dw.mult τ₀) := Equiv.sigmaSubtype τ₀
      rw [Nat.card_congr (e1.trans (e2.trans e3)), Nat.card_eq_fintype_card, Fintype.card_fin]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hcard]
      unfold Datum.mult
      rw [if_pos ((hrel τ₀).1 h)]
    · rw [hcard]
      unfold Datum.mult
      rw [if_neg (fun h' => h ((hrel τ₀).2 h'))]
end GlobalTheory.Relab
