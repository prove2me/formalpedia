-- Prove2me | solution 1 for GlobalTheory.MulFinite.isFinite_of_relAmple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:52:55.832778+00:00
-- url     : https://prove2.me/submissions/e4752495-ba63-4664-b8cd-92660b40fc12

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Theorems.Thm_GlobalTheory_MulFinite_locallyQuasiFinite_of_cover
import Theorems.Thm_GlobalTheory_MulFinite_isAffineHom_fromSpecResidueField
import Theorems.Thm_GlobalTheory_MulFinite_exists_fn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.MulFinite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace Polynomial
namespace GlobalTheory.MulFinite
theorem _root_.solution {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsProper A.hom] (L : LB A.left)
    (hL : L.IsLB) (hA : RelAmple A L) (m : A ⟶ A) (e : ℕ) (he : e ≠ 0)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, m.left] ![(e : ℤ), -1])) (hα : α.IsGen) :
    IsFinite m.left := by
  have hm : m.left ≫ A.hom = A.hom := Over.w m
  have : IsProper (m.left ≫ A.hom) := by rw [hm]; infer_instance
  have : IsProper m.left := .of_comp _ A.hom
  suffices LocallyQuasiFinite m.left from .of_isProper_of_locallyQuasiFinite _
  refine .of_fiberToSpecResidueField _ fun y => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (A.hom y)) isOpen_univ
  obtain ⟨N, -, M, s, hcov, hs⟩ := hA U hU
  have hy : ∀ z, m.left (m.left.fiberι y z) = y := fun z =>
    (m.left.range_fiberι y).le ⟨z, rfl⟩
  let r : m.left.fiber y ⟶ (A.hom ⁻¹ᵁ U).toScheme :=
    IsOpenImmersion.lift (A.hom ⁻¹ᵁ U).ι (m.left.fiberι y) (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      change A.hom (m.left.fiberι y z) ∈ U
      rw [← hm, Scheme.Hom.comp_apply, hy]
      exact hyU)
  have hr : r ≫ (A.hom ⁻¹ᵁ U).ι = m.left.fiberι y := IsOpenImmersion.lift_fac _ _ _
  have := isAffineHom_fromSpecResidueField A.left y
  have : IsAffineHom (r ≫ (A.hom ⁻¹ᵁ U).ι) := by
    rw [hr]; exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
      (IsPullback.of_hasPullback m.left (A.left.fromSpecResidueField y)).flip this
  have : IsAffineHom r := .of_comp r (A.hom ⁻¹ᵁ U).ι
  obtain ⟨j₀, hj₀⟩ := exists_chart hL y
  have key := fun i => exists_fn L hL (A.hom ⁻¹ᵁ U).ι N (s i) m.left e he α hα r j₀ (fun z => by
    rw [← Scheme.Hom.comp_apply r, hr, hy]; exact hj₀)
  choose a ha using key
  have : IsProper (m.left.fiberToSpecResidueField y) :=
    inferInstanceAs (IsProper (pullback.snd m.left (A.left.fromSpecResidueField y)))
  refine locallyQuasiFinite_of_cover (K := A.left.residueField y) (m.left.fiberToSpecResidueField y) a ?_ fun i => ?_
  · simp only [ha]
    rw [← Scheme.Hom.preimage_iSup]
    exact (congrArg (fun V => r ⁻¹ᵁ V) hcov).trans rfl
  · rw [ha]
    exact (hs i).1.preimage r
end GlobalTheory.MulFinite
