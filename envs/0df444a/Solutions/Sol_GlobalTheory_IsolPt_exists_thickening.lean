-- Prove2me | solution 1 for GlobalTheory.IsolPt.exists_thickening
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:12:42.07382+00:00
-- url     : https://prove2.me/submissions/933cdc42-464a-402e-becd-499984339e31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasChartsOfForallIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniversalThickening
import Theorems.Thm_GlobalTheory_IsolPt_exists_pow_stable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.IsolPt
namespace GlobalTheory.IsolPt
theorem _root_.solution {k B : Type} [Field k] [CommRing B] [Algebra k B] [IsArtinianRing B]
    (e : B →ₐ[k] k) : ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (aug : A →ₐ[k] k) (M : ℕ)
      (π : B →ₐ[k] A), RingHom.ker aug ^ (M + 1) = ⊥ ∧ aug.comp π = e ∧
      ∀ (Q : Type) [CommRing Q] [Algebra k Q] (augQ : Q →ₐ[k] k) (j : ℕ),
        RingHom.ker augQ ^ (j + 1) = ⊥ → ∀ z : B →ₐ[k] Q, augQ.comp z = e →
        ∃ a : A →ₐ[k] Q, augQ.comp a = aug ∧ z = a.comp π := by
  obtain ⟨M, hM⟩ := exists_pow_stable (RingHom.ker e)
  set I : Ideal B := RingHom.ker e ^ (M + 1) with hI
  have hIe : ∀ b ∈ I, e b = 0 := fun b hb => Ideal.pow_le_self (Nat.succ_ne_zero M) hb
  refine ⟨B ⧸ I, inferInstance, inferInstance, Ideal.Quotient.liftₐ I e hIe, M, Ideal.Quotient.mkₐ k I,
    ?_, ?_, ?_⟩
  · have h : RingHom.ker (Ideal.Quotient.liftₐ I e hIe) ≤ (RingHom.ker e).map (Ideal.Quotient.mk I) := by
      intro x hx
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact Ideal.mem_map_of_mem _ hx
    refine le_bot_iff.1 ((Ideal.pow_right_mono h _).trans ?_)
    rw [← Ideal.map_pow, ← hI, Ideal.map_quotient_self]
  · ext b
    rfl
  · intro Q _ _ augQ j hj z hz
    have hzI : ∀ b ∈ I, z b = 0 := by
      intro b hb
      have h : (RingHom.ker e).map z ≤ RingHom.ker augQ := by
        rw [Ideal.map_le_iff_le_comap]
        intro c hc
        change augQ (z c) = 0
        rw [← AlgHom.comp_apply, hz]
        exact hc
      have h2 := Ideal.mem_map_of_mem z (hM j hb)
      rw [Ideal.map_pow] at h2
      have h3 := Ideal.pow_right_mono h _ h2
      rwa [hj] at h3
    refine ⟨Ideal.Quotient.liftₐ I z hzI, ?_, ?_⟩
    · apply Ideal.Quotient.algHom_ext
      ext b
      exact DFunLike.congr_fun hz b
    · ext b
      rfl
end GlobalTheory.IsolPt
