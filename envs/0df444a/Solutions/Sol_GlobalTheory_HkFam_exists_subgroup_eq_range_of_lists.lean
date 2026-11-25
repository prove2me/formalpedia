-- Prove2me | solution 1 for GlobalTheory.HkFam.exists_subgroup_eq_range_of_lists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:51:16.169984+00:00
-- url     : https://prove2.me/submissions/eb7aeb78-0142-42a7-8413-7fc25bf1ffd3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_KerScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteEtaleLatticeTorsionHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSubgroupEqRangeOfLists
import Theorems.Thm_GlobalTheory_HkFam_ListedSubgroup_eq_comp_section
import Theorems.Thm_GlobalTheory_HkFam_ListedSubgroup_section_eq

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
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
open GlobalTheory GlobalTheory.HkFam
open ListedSubgroup
namespace GlobalTheory.HkFam
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) [ConnectedSpace S] (t : SAB H S) (σ : Fin n → (𝟙_ (Over S) ⟶ t.G)) (K : Set t.G.left), IsProper t.G.hom → IsUnit (p : Γ(S, ⊤)) → Lists (p ^ 2) σ K → HeckeSet D t 𝔓 p i K → ∃ C : Subgroup (𝟙_ (Over S) ⟶ t.G), (C : Set _) = Set.range σ := by
  intro E _ _ _ H D 𝔓 p i n S _ t σ K hpr hp ⟨hσ, hK, _⟩ hH
  have hab : IsAbelianScheme t.G := ⟨t.comm, t.semi.smooth, hpr, t.semi.geomConnected⟩
  have hN : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤)) := by
    rw [Nat.cast_pow]
    exact hp.pow 2
  obtain ⟨s₀⟩ : Nonempty S := inferInstance
  let k : Type := AlgebraicClosure (S.residueField s₀)
  let x : Sp k ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s₀) k)) ≫ S.fromSpecResidueField s₀
  obtain ⟨C, hC, -⟩ := hH k x
  obtain ⟨q⟩ : Nonempty (Sp k) := inferInstance
  have hmem : ∀ j, toUnit (Over.mk x) ≫ σ j ∈ C := fun j => by
    rw [hC, hK]
    rintro _ ⟨y, rfl⟩
    exact Set.mem_iUnion.2 ⟨j, x y, (Scheme.Hom.comp_apply x (σ j).left y).symm⟩
  have key : ∀ a : 𝟙_ (Over S) ⟶ t.G, a ^ (p ^ 2) = 1 → toUnit (Over.mk x) ≫ a ∈ C → a ∈ Set.range σ := by
    intro a ha h
    rw [hC, hK] at h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (h ⟨q, rfl⟩)
    have h1 := eq_comp_section t.G.hom (σ j).left (Over.w (σ j)) _ q hj
    rw [Over.w (toUnit (Over.mk x) ≫ a)] at h1
    exact ⟨j, (section_eq t.G hN ha (hσ j) x h1).symm⟩
  refine ⟨{ carrier := Set.range σ, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩
  · rintro _ _ ⟨j, rfl⟩ ⟨j', rfl⟩
    refine key _ (by rw [mul_pow, hσ, hσ, _root_.one_mul]) ?_
    rw [MonObj.comp_mul]
    exact C.mul_mem (hmem j) (hmem j')
  · refine key _ (one_pow _) ?_
    rw [MonObj.comp_one]
    exact C.one_mem
  · rintro _ ⟨j, rfl⟩
    refine key _ (by rw [inv_pow, hσ, inv_one]) ?_
    rw [GrpObj.comp_inv]
    exact C.inv_mem (hmem j)
end GlobalTheory.HkFam
