-- Prove2me | solution 1 for GlobalTheory.AnVal.JetAlg.origin_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:40:38.30762+00:00
-- url     : https://prove2.me/submissions/4f587b32-1db8-4047-997e-e171dc083df0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_mk_trunc_coe
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psTrunc_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_mD_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_taylor_multiplication
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_coeff_tay
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isLocalHom_jetMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetAug_mk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_precomp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetZero_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetAlg
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
  {n m : ℕ}
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.AnVal.JetAlg
theorem _root_.solution {ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left} {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (hψ : Φ.JetMap m ψ Λ) {U : A.left.Opens} (hU : ⊤ ≤ ψ ⁻¹ᵁ U) :
    ⊤ ≤ (Φ.e (Λ (colsOf n g 0))).left ⁻¹ᵁ U := by
  obtain ⟨hol, rfl⟩ := hψ
  have hz : IsLocalHom (jetZero (g := n * g) m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) := by
    unfold jetZero
    exact isLocalHom_jetMap _ _
  have hr : IsLocalHom (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) := by
    unfold renN
    exact isLocalHom_jetMap _ _
  have hc : ∀ F : (Fin (n * g) → ℂ) → ℂ, jetAug (jetOf m F) = F 0 := by
    intro F
    unfold jetOf psJet
    rw [jetAug_mk, FBIdJet.psTrunc_eq]
    show MvPolynomial.coeff 0 _ = _
    rw [MvPowerSeries.coeff_truncTotal _ (by simp), coeff_tay]
    simp [dirs, fct, TM.mD_zero]
  have hk : ∀ c : ℂ, jetOf m (fun _ : Fin (n * g) → ℂ => c) = algebraMap ℂ _ c := by
    intro c
    unfold jetOf psJet
    rw [TM.taylor_multiplication.2.1, ← MvPolynomial.coe_C, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]
    rfl
  have key := jetPt_precomp _ (fun _ => (Φ.e (Λ (colsOf n g 0))).left) hol (isHolFam_const _) rfl m
    (jetZero (g := n * g) m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) (fun U _ f => by
      rw [AlgHom.coe_toRingHom, jetZero_eq, hc, hk])
  rw [← jetPt_const] at key
  intro p _
  have h1 := hU (show IsLocalRing.closedPoint (Jet ℂ (Fin n × Fin g) m) ∈ (⊤ : (Sp (Jet ℂ (Fin n × Fin g) m)).Opens) from trivial)
  have h2 := congrArg (fun φ => φ (IsLocalRing.closedPoint (Jet ℂ (Fin 1 × Fin (n * g)) m))) key
  unfold spMap at h1 h2
  simp only [Scheme.Hom.comp_apply] at h1 h2
  have hz' : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom
      (jetZero (g := n * g) m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m))) := hz
  have hr' : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom
      (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m))) := hr
  have q1 : (Spec.map (CommRingCat.ofHom (jetZero (g := n * g) m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m)))
      (IsLocalRing.closedPoint (Jet ℂ (Fin 1 × Fin (n * g)) m)) = IsLocalRing.closedPoint _ :=
    AlgebraicGeometry.Spec_closedPoint
  have q2 : (Spec.map (CommRingCat.ofHom (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m)))
      (IsLocalRing.closedPoint (Jet ℂ (Fin n × Fin g) m)) = IsLocalRing.closedPoint _ :=
    AlgebraicGeometry.Spec_closedPoint
  have hp : ∀ q r : PrimeSpectrum ℂ, q = r := fun q r =>
    PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm)
  show (Over.Hom.left (Φ.e (Λ (colsOf n g 0)))) p ∈ U
  rw [hp p ((Spec.map (CommRingCat.ofHom (algebraMap ℂ (Jet ℂ (Fin 1 × Fin (n * g)) m))))
    (IsLocalRing.closedPoint (Jet ℂ (Fin 1 × Fin (n * g)) m)))]
  refine (congrArg (fun z => z ∈ U) h2).mp ?_
  exact (congrArg (fun z => (jetPt (fun v => Over.Hom.left (Φ.e (Λ (colsOf n g v)))) hol m) z ∈ U)
    (q1.trans q2.symm)).mpr h1
end GlobalTheory.AnVal.JetAlg
