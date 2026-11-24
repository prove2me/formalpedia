-- Prove2me | solution 1 for GlobalTheory.LamBiext.val_nest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:36:23.671808+00:00
-- url     : https://prove2.me/submissions/a8652a3f-b0cb-485a-af8f-28dabf5b303e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_MulGenNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLaws
import Theorems.Thm_GlobalTheory_LamBiext_trF_flat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LamBiext
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
variable {X W Y Z : Scheme.{0}} (L : LB X) {I K : Type} [Fintype I] [Fintype K]
  (φ : I → (W ⟶ X)) (δ : I → ℤ) (ψ : K → (Y ⟶ W)) (ε : K → ℤ)
variable {L φ δ ψ ε}
namespace GlobalTheory.LamBiext
theorem _root_.solution {t : LB.Gen (LB.LinComb L (flatφ φ ψ) (flatε δ ε))} (ht : t.IsGen) (r : Z ⟶ Y) {z : Z}
    {JP : (Z ⟶ W) → I → L.ι} (hJP : Good (LB.LinComb L φ δ) z JP) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (L := LB.LinComb L φ δ) (nest L φ δ ψ ε t) r z JP =
      (∏ k, adj φ δ z JP J (r ≫ ψ k) ^ ε k) * val (L := L) t r z J := by
  have hm := hJP.mem ψ r
  have e₁ : val (L := LB.LinComb L φ δ) (nest L φ δ ψ ε t) r z JP =
      gm r z (LB.wchart L (flatφ φ ψ) fun p => JP (r ≫ ψ p.1) p.2) (t.s fun p => JP (r ≫ ψ p.1) p.2) :=
    gm_res r z _ hm _
  have e₂ := val_of t r z J (fun p => J ((r ≫ ψ p.1) ≫ φ p.2)) (fun p => by rw [Category.assoc])
  have m₂ : r z ∈ LB.wchart L (flatφ φ ψ) (fun p => J ((r ≫ ψ p.1) ≫ φ p.2)) := by
    have := hJ.mem (flatφ φ ψ) r
    simpa only [Category.assoc] using this
  rw [e₂]
  refine e₁.trans ((gen_trans ht r z (nest_le L φ δ ψ _ hm) m₂).trans ?_)
  exact congrArg (· * _) (trF_flat L φ δ ψ ε r z (fun k => JP (r ≫ ψ k)) (fun k i => J ((r ≫ ψ k) ≫ φ i)))
end GlobalTheory.LamBiext
