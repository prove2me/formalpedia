-- Prove2me | solution 1 for GlobalTheory.SmoothLocusAdd.exists_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:58:35.024626+00:00
-- url     : https://prove2.me/submissions/b5c3ea63-ea4a-4fa9-9ff9-d52317f649fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfLocallyRel
import Theorems.Thm_GlobalTheory_SmoothLocusAdd_exists_hom_of_locally_rel
import Theorems.Thm_GlobalTheory_SmoothLocusAdd_IsSumAt_unique
import Theorems.Thm_GlobalTheory_SmoothLocusAdd_exists_sum_near_prime
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_symm_zeroOver
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_some
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_toAffineLift
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_zero
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_symm_zeroOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_symm_zeroOver
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_some
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_toAffineLift
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_zero
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_symm_zeroOver



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
  AlgebraicGeometry
noncomputable section
open GlobalTheory GlobalTheory.SmoothLocusAdd
open GlobalTheory.WeierstrassCurve
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
namespace GlobalTheory.SmoothLocusAdd
theorem _root_.solution {T : Scheme.{0}} [IsReduced T] (p q : T ⟶ scheme W)
    (hpq : p ≫ toSpec W = q ≫ toSpec W)
    (np : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), IsNonsingularAt W (x ≫ p))
    (nq : ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), IsNonsingularAt W (x ≫ q)) :
    ∃ s : T ⟶ scheme W, s ≫ toSpec W = p ≫ toSpec W ∧
      ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ T), IsSumAt W (x ≫ p) (x ≫ q) (x ≫ s) := by
  refine exists_hom_of_locally_rel (p ≫ toSpec W) (toSpec W)
    (fun k _ x y => IsSumAt W (x ≫ p) (x ≫ q) y)
    (fun k _ x y y' h h' => h.unique W (by simp only [Category.assoc, hpq]) h') fun z => ?_
  have hc : ∀ e : scheme W, ∃ i, e ∈ coordOpen W i := fun e => by
    rcases (coordOpen_one_sup_coordOpen_two W).ge (Set.mem_univ e) with h | h
    exacts [⟨_, h⟩, ⟨_, h⟩]
  obtain ⟨a, ha⟩ := hc (p z)
  obtain ⟨b, hb⟩ := hc (q z)
  obtain ⟨C, ι, _, ⟨z', rfl⟩, hr⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := z) (U := p ⁻¹ᵁ coordOpen W a ⊓ q ⁻¹ᵁ coordOpen W b) ⟨ha, hb⟩
  have : _root_.IsReduced C := (affine_isReduced_iff C).mp (isReduced_of_isOpenImmersion ι)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (ι ≫ p ≫ toSpec W)
  obtain ⟨P, hP, -, eP⟩ := exists_eq_ptHom_of_preimage_eq_top W (A := C) φ.hom (ι ≫ p)
    (by rw [Category.assoc]; exact hφ.symm) a (top_le_iff.mp fun y _ => (hr ⟨y, rfl⟩).1)
  obtain ⟨Q, hQ, -, eQ⟩ := exists_eq_ptHom_of_preimage_eq_top W (A := C) φ.hom (ι ≫ q)
    (by rw [Category.assoc, ← hpq]; exact hφ.symm) b (top_le_iff.mp fun y _ => (hr ⟨y, rfl⟩).2)
  obtain ⟨V, j, _, f, ⟨v, rfl⟩, hf, hsum⟩ := exists_sum_near_prime W (C := C) φ.hom hP hQ
    (fun k _ ψ => np k (Spec.map (CommRingCat.ofHom ψ) ≫ ι) _ _ (hP.map_comp ψ) (by
      rw [Category.assoc, ← SpecMap_ptHom W _ _ hP, ← eP]))
    (fun k _ ψ => nq k (Spec.map (CommRingCat.ofHom ψ) ≫ ι) _ _ (hQ.map_comp ψ) (by
      rw [Category.assoc, ← SpecMap_ptHom W _ _ hQ, ← eQ])) z'
  refine ⟨V, j ≫ ι, inferInstance, f, ⟨v, by simp⟩, ?_, fun k _ x => ?_⟩
  · rw [hf, Category.assoc, ← hφ]; rfl
  · have := hsum k x
    rw [← eP, ← eQ] at this
    simpa only [Category.assoc] using this
end GlobalTheory.SmoothLocusAdd
