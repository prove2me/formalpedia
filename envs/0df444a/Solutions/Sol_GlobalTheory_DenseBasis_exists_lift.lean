-- Prove2me | solution 1 for GlobalTheory.DenseBasis.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:07:13.330809+00:00
-- url     : https://prove2.me/submissions/a0995d38-2c9b-46e3-9e6b-b6d42cc408b7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteEtaleLatticeTorsionHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfDense
import Theorems.Thm_GlobalTheory_FinEt_exists_iso_sigma_of_isSepClosed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.DenseBasis
variable {Z S : Scheme.{0}}
namespace GlobalTheory.DenseBasis
theorem _root_.solution (p : Z ⟶ S) [IsFinite p] [Etale p] {K : Type} [Field K] [IsAlgClosed K]
    (x : Spec (.of K) ⟶ S) (w : Spec (.of K)) (z : Z) (hz : p z = x w) :
    ∃ y : Spec (.of K) ⟶ Z, y ≫ p = x ∧ y w = z := by
  obtain ⟨q, hq₁, hq₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := x) z w hz
  obtain ⟨n, e, he⟩ := GlobalTheory.FinEt.exists_iso_sigma_of_isSepClosed (pullback.snd p x)
  obtain ⟨⟨j, v⟩, hv⟩ : ∃ a, AlgebraicGeometry.sigmaMk _ a = e.inv q :=
    ⟨(AlgebraicGeometry.sigmaMk _).symm (e.inv q), by simp⟩
  rw [AlgebraicGeometry.sigmaMk_mk] at hv
  refine ⟨Sigma.ι (fun _ : Fin n => Spec (.of K)) j ≫ e.hom ≫ pullback.fst p x, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% he]
    simp
  · rw [Subsingleton.elim w v, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hv, ← Scheme.Hom.comp_apply]
    simpa using hq₁
end GlobalTheory.DenseBasis
