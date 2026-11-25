-- Prove2me | solution 1 for GlobalTheory.PowGerm.univPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:37:48.855394+00:00
-- url     : https://prove2.me/submissions/80ca1853-f0c7-4035-9e1d-03cc90dc2a75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalJetsPowerProduct
import Theorems.Thm_GlobalTheory_PowGerm_UnivPow_homAt_comp
import Theorems.Thm_GlobalTheory_PowGerm_UnivPow_jet_ext
import Theorems.Thm_GlobalTheory_PowGerm_UnivPow_jetCopy_X
import Theorems.Thm_GlobalTheory_PowGerm_UnivPow_jetAug_X
import Theorems.Thm_GlobalTheory_PowGerm_UnivPow_jetTrunc_mk
import Theorems.Thm_GlobalTheory_PowGerm_UnivPow_zV_pr
import Theorems.Thm_GlobalTheory_PowGerm_UnivPow_pow_ext
import Theorems.Thm_GlobalTheory_PowGerm_UnivPow_one_pr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PowGerm
open UnivPow
namespace GlobalTheory.PowGerm
theorem _root_.solution : UnivPowSt := by
  intro V _ G G' _ _ n d pG xT ⟨hT, hA, hU⟩
  refine ⟨fun m => pow_ext pG _ _ fun i => ?_, fun m => pow_ext pG _ _ fun i => ?_, ?_⟩
  · rw [Category.assoc, zV_pr, zV_pr, ← hT m, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp]
    congr 2
    apply jet_ext
    intro p
    rw [AlgHom.comp_apply, AlgHom.comp_apply, jetCopy_X, jetTrunc_mk, jetTrunc_mk, jetCopy_X]
  · rw [Category.assoc, zV_pr, one_pr, ← hA m, ← Category.assoc, homAt_comp]
    congr 2
    apply jet_ext
    intro p
    rw [AlgHom.comp_apply, jetCopy_X, jetAug_X, jetAug_X]
  · intro A _ _ aug m hm y hy
    have hi : ∀ i : Fin n, ∃! ψ : Jet V (Fin 1 × Fin d) m →ₐ[V] A,
        aug.comp ψ = jetAug ∧ y ≫ pG.pr i = Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ xT m := fun i =>
      hU A aug m hm (y ≫ pG.pr i) (by rw [← Category.assoc, hy, one_pr])
    choose ψ hψ hψu using hi
    let a : Fin n × Fin d → A := fun p => ψ p.1 (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), p.2)))
    have ha : ∀ p, aug (a p) = 0 := fun p => by
      have := congrArg (fun f : Jet V (Fin 1 × Fin d) m →ₐ[V] V =>
        f (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), p.2)))) (hψ p.1).1
      simp only [AlgHom.comp_apply, jetAug_X] at this
      exact this
    have hsp : Ideal.span (Set.range fun p => (MvPolynomial.aeval a : MvPolynomial (Fin n × Fin d) V →ₐ[V] A)
        (MvPolynomial.X p)) ^ (m + 1) = ⊥ := by
      apply le_bot_iff.1
      rw [← hm]
      apply Ideal.pow_right_mono
      rw [Ideal.span_le]
      rintro _ ⟨p, rfl⟩
      simp only [MvPolynomial.aeval_X]
      exact ha p
    let Ψ : Jet V (Fin n × Fin d) m →ₐ[V] A := liftJet (MvPolynomial.aeval a) hsp
    have hΨ : ∀ p, Ψ (Ideal.Quotient.mk _ (MvPolynomial.X p)) = a p := fun p => by
      show (MvPolynomial.aeval a : MvPolynomial (Fin n × Fin d) V →ₐ[V] A) (MvPolynomial.X p) = a p
      rw [MvPolynomial.aeval_X]
    have hc : ∀ i, Ψ.comp (jetCopy d m i) = ψ i := fun i => by
      apply jet_ext
      rintro ⟨u, j⟩
      obtain rfl : u = 0 := Subsingleton.elim _ _
      rw [AlgHom.comp_apply, jetCopy_X, hΨ]
    refine ⟨Ψ, ⟨?_, pow_ext pG _ _ fun i => ?_⟩, ?_⟩
    · apply jet_ext
      intro p
      rw [AlgHom.comp_apply, hΨ, ha, jetAug_X]
    · rw [Category.assoc, zV_pr, ← Category.assoc, homAt_comp, hc]
      exact (hψ i).2
    · rintro Φ ⟨h1, h2⟩
      have hd : ∀ i, Φ.comp (jetCopy d m i) = ψ i := fun i => by
        apply hψu i
        refine ⟨?_, ?_⟩
        · rw [← AlgHom.comp_assoc, h1]
          apply jet_ext
          intro p
          rw [AlgHom.comp_apply, jetCopy_X, jetAug_X, jetAug_X]
        · rw [h2, Category.assoc, zV_pr, ← Category.assoc, homAt_comp]
      apply jet_ext
      rintro ⟨i, j⟩
      rw [hΨ]
      show _ = ψ i _
      rw [← hd i, AlgHom.comp_apply, jetCopy_X]
end GlobalTheory.PowGerm
