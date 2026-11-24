-- Prove2me | solution 1 for GlobalTheory.exists_grpObj_of_flat_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:14:39.008711+00:00
-- url     : https://prove2.me/submissions/ccdc83bf-3cbf-497a-9535-e05a7b22d3c2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsGrpObjOfFlatClosed
import Theorems.Thm_GlobalTheory_exists_grpObj_of_mono
import Theorems.Thm_GlobalTheory_isMonHom_of_comp_mono
import Theorems.Thm_GlobalTheory_isCommMonObj_of_mono
import Theorems.Thm_GlobalTheory_existsUnique_lift_of_flat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S S' : Scheme.{0}} (f : S' ⟶ S)
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] (P Ga : Over S) [GrpObj P] (io : Ga ⟶ P)
    (Z : Over S') [GrpObj Z] (i : Z ⟶ (Over.pullback f).obj P) (e : (Over.pullback f).obj Ga ≅ Z)
    [IsClosedImmersion io.left] [Flat Ga.hom] [hi : IsMonHom i]
    (h : e.hom ≫ i = (Over.pullback f).map io) :
    ∃ _ : GrpObj Ga, IsMonHom io ∧ IsMonHom e.hom ∧ (IsCommMonObj P → IsCommMonObj Ga) := by
  have h1 : Flat (𝟙_ (Over S)).hom := inferInstanceAs (Flat (𝟙 S))
  have h2 : Flat (Ga ⊗ Ga).hom := inferInstanceAs (Flat (pullback.fst Ga.hom Ga.hom ≫ Ga.hom))
  have hm : Mono io := (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono io.left))
  have hm' : Mono ((Over.pullback f).map io) := inferInstance
  have h' : e.inv ≫ (Over.pullback f).map io = i := by rw [← h, e.inv_hom_id_assoc]
  have hmi : Mono i := by rw [← h']; infer_instance
  obtain ⟨o, ⟨ho, -⟩, -⟩ := existsUnique_lift_of_flat f io η[P]
    (Functor.OplaxMonoidal.η (Over.pullback f) ≫ η[Z] ≫ e.inv) (by
      rw [Category.assoc, Category.assoc, h', hi.one_hom, Functor.obj.η_def,
        Functor.Monoidal.η_ε_assoc])
  obtain ⟨m, ⟨hm, -⟩, -⟩ := existsUnique_lift_of_flat f io ((io ⊗ₘ io) ≫ μ[P])
    (Functor.OplaxMonoidal.δ (Over.pullback f) Ga Ga ≫ (e.hom ⊗ₘ e.hom) ≫ μ[Z] ≫ e.inv) (by
      simp only [Category.assoc]
      rw [h', hi.mul_hom, tensorHom_comp_tensorHom_assoc, h, Functor.obj.μ_def,
        Functor.LaxMonoidal.μ_natural_assoc, Functor.Monoidal.δ_μ_assoc, Functor.map_comp])
  obtain ⟨n, ⟨hn, -⟩, -⟩ := existsUnique_lift_of_flat f io (io ≫ GrpObj.inv)
    (e.hom ≫ GrpObj.inv ≫ e.inv) (by
      simp only [Category.assoc]
      rw [h', GrpObj.inv_hom, ← Category.assoc, h, Functor.obj.ι_def, Functor.map_comp])
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono io o m n ho hm hn
  refine ⟨G, hG, ?_, fun _ => isCommMonObj_of_mono io⟩
  have : IsMonHom (e.hom ≫ i) := by rw [h]; infer_instance
  exact isMonHom_of_comp_mono e.hom i
end GlobalTheory
