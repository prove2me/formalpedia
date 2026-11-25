-- Prove2me | solution 1 for GlobalTheory.TorsionCompare.law_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:43:36.096181+00:00
-- url     : https://prove2.me/submissions/835abb3a-75f8-4919-bd4d-44a976382e7a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_OriginChartMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NotIsUnitNatCastOfIsLocalHom
import Theorems.Thm_GlobalTheory_TorsionCompare_jetPt_zR
import Theorems.Thm_P2M_GlobalTheory_TorsionCompare_substJ_zR__6c798f86c20b

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
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCompare
variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G]
variable {d : ℕ}
namespace GlobalTheory.TorsionCompare
theorem _root_.solution (F : FGLaw R d) (x : ∀ m : ℕ, algOver R (JetR R (Fin 1 × Fin d) m) ⟶ G) (m : ℕ) :
    (algOverHom (substJ m F.F F.const) ≫ x m =
      (algOverHom (jetPt (d := d) (0 : Fin 2) m) ≫ x m) *
        (algOverHom (jetPt (d := d) (1 : Fin 2) m) ≫ x m)) ↔
    ∃ ψ₀ ψ₁ ψ : JetR R (Fin d) m →ₐ[R] JetR R (Fin 2 × Fin d) m,
      (∀ j, ψ₀ (zR m j) = zR m ((0 : Fin 2), j)) ∧ (∀ j, ψ₁ (zR m j) = zR m ((1 : Fin 2), j)) ∧
      (∀ j, ψ (zR m j) = jetOfSeries m (F.F j)) ∧
      lift (algOverHom ψ₀ ≫ chartEquiv G d x m) (algOverHom ψ₁ ≫ chartEquiv G d x m) ≫ μ[G] =
        algOverHom ψ ≫ chartEquiv G d x m := by
  have hc : ∀ ψ : JetR R (Fin d) m →ₐ[R] JetR R (Fin 2 × Fin d) m,
      algOverHom ψ ≫ chartEquiv G d x m = algOverHom (ψ.comp (jetRename Prod.snd m)) ≫ x m :=
    fun ψ => by rw [algOverHom_comp, Category.assoc]; rfl
  have hi : ∀ χ : JetR R (Fin 1 × Fin d) m →ₐ[R] JetR R (Fin 2 × Fin d) m,
      (χ.comp (jetRename toOne m)).comp (jetRename Prod.snd m) = χ := fun χ => by
    rw [AlgHom.comp_assoc, jetRename_comp_of_inverse Prod.snd toOne toOne_snd, AlgHom.comp_id]
  constructor
  · intro h
    refine ⟨(jetPt 0 m).comp (jetRename toOne m), (jetPt 1 m).comp (jetRename toOne m),
      (substJ m F.F F.const).comp (jetRename toOne m), fun j => ?_, fun j => ?_, fun j => ?_, ?_⟩
    · rw [AlgHom.comp_apply, jetRename_zR, jetPt_zR]; rfl
    · rw [AlgHom.comp_apply, jetRename_zR, jetPt_zR]; rfl
    · rw [AlgHom.comp_apply, jetRename_zR, substJ_zR']; rfl
    · rw [hc, hc, hc, hi, hi, hi, h]; rfl
  · rintro ⟨ψ₀, ψ₁, ψ, h0, h1, h2, h⟩
    have e0 : ψ₀.comp (jetRename Prod.snd m) = jetPt 0 m := jet_ext fun q => by
      rw [AlgHom.comp_apply, jetRename_zR, h0, jetPt_zR]
    have e1 : ψ₁.comp (jetRename Prod.snd m) = jetPt 1 m := jet_ext fun q => by
      rw [AlgHom.comp_apply, jetRename_zR, h1, jetPt_zR]
    have e2 : ψ.comp (jetRename Prod.snd m) = substJ m F.F F.const := jet_ext fun q => by
      rw [AlgHom.comp_apply, jetRename_zR, h2, substJ_zR']
    rw [hc, hc, hc, e0, e1, e2] at h
    rw [← h]; rfl
end GlobalTheory.TorsionCompare
