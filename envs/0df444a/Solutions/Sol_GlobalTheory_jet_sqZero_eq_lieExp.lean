-- Prove2me | solution 1 for GlobalTheory.jet_sqZero_eq_lieExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:10.725867+00:00
-- url     : https://prove2.me/submissions/af6192f6-d467-4181-b44e-27766814bf61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FirstJetEqProdTangent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangent
import Theorems.Thm_GlobalTheory_firstJet_eq_prod_tangent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open SqZero
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (hG : Smooth G.hom) {d : ℕ} {v : Fin d → (epsR R ⟶ G)}
    (hv : IsLieBasis v) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G)
    (hxt : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
    (hx0 : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
    (hx1 : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)
    {A : Type} [CommRing A] [Algebra R A] {J : Ideal A} (hJ : J ^ 2 = ⊥) (δ : Fin d → A)
    (hδ : ∀ j, δ j ∈ J) (hδ' : ∀ j, δ j * δ j = 0) (m : ℕ) (φ : JetR R (Fin d) m →ₐ[R] A)
    (hφ : ∀ j, φ (zR m j) = δ j) : spMap φ ≫ x m = lieExp v δ hδ' := by
  have key : ∀ (k : ℕ) (φ : JetR R (Fin d) (k + 1) →ₐ[R] A), (∀ j, φ (zR (k + 1) j) = δ j) →
      spMap φ ≫ x (k + 1) = lieExp v δ hδ' := by
    intro k
    induction k with
    | zero =>
      intro φ hφ
      exact firstJet_eq_prod_tangent R G hG d v hv x hx0 hx1 A φ _
        fun j => (epsTo_eps _ _).trans (hφ j).symm
    | succ k ih =>
      intro φ hφ
      have hk : J ^ (k + 1 + 1) = ⊥ :=
        le_bot_iff.1 ((Ideal.pow_le_pow_right (by omega)).trans hJ.le)
      have e : φ = (jetLift R J hk δ hδ).comp (jetTruncR R (Fin d) (k + 1)) :=
        jet_ext fun j => (hφ j).trans (jetLift_zR J hk δ hδ j).symm
      rw [e, ← spMap_comp, Category.assoc, hxt]
      exact ih _ (jetLift_zR J hk δ hδ)
  rw [← hxt m, ← Category.assoc, spMap_comp]
  exact key m _ hφ
end GlobalTheory
