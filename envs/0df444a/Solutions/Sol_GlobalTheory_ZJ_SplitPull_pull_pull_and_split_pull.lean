-- Prove2me | solution 1 for GlobalTheory.ZJ.SplitPull.pull_pull_and_split_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:44:45.630054+00:00
-- url     : https://prove2.me/submissions/e41886ce-e698-4c0d-80c8-8b0c5cece79c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PullPullAndSplitPull
import Theorems.Thm_GlobalTheory_ZJ_SplitPull_exists_basis_sections
import Theorems.Thm_GlobalTheory_ZJ_SplitPull_stable_pull
import Theorems.Thm_GlobalTheory_ZJ_SplitPull_hasWt_pull
import Theorems.Thm_GlobalTheory_ZJ_SplitPull_hasWt_coeff
import Theorems.Thm_GlobalTheory_UU_TorusCompat_isMonHom
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_UU_existsUnique_torusCompat


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
noncomputable section
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.SplitPull
open GlobalTheory.UU
namespace GlobalTheory.ZJ.SplitPull
theorem _root_.solution : (∀ (X Y Y' : Scheme.{0}) (C : Charts X) (φ : Y ⟶ X) (ψ : Y' ⟶ Y) [IsAffineHom φ] [IsAffineHom ψ], (C.pull φ).pull ψ = C.pull (ψ ≫ φ)) ∧ ∀ (K K' : Type) [Field K] [Field K'] (H : Over (Sp K)) [GrpObj H] (H' : Over (Sp K')) [GrpObj H'] (f : Sp K' ⟶ Sp K) (φ : H'.left ⟶ H.left) [IsAffineHom φ], IsGrpPullback H' H f φ → ∀ (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl), C.Split c → Charts.Split (C.pull φ) c := by
  refine ⟨fun X Y Y' C φ ψ _ _ => rfl, ?_⟩
  rintro K K' _ _ H _ H' _ f φ _ hφ C d c ⟨hc, i, hT⟩
  obtain ⟨i', hi, -⟩ := existsUnique_torusCompat hφ.1 i
  have := hT.hom
  refine ⟨MorphismProperty.of_isPullback (P := @GeometricallyConnected) hφ.1 hc, i', hi.isMonHom hφ,
    fun a => stable_pull hφ hi (hT.stable a), fun a j hj => hasWt_pull hφ hi (hT.inv a j hj),
    fun a j k hj => hasWt_pull hφ hi (hT.wt a j k hj), fun k x => ?_, fun a u hu => ?_⟩
  · obtain ⟨a, j, hj, hx⟩ := hT.bpf k (φ x)
    refine ⟨a, j, hj, ?_⟩
    change x ∈ H'.left.basicOpen ((φ.app (C.W a)).hom (C.r a j))
    rw [← Scheme.preimage_basicOpen]
    exact hx
  · obtain ⟨J, e, he⟩ := exists_basis_sections f
    obtain ⟨s, x, rfl⟩ := (he _ _ φ _ _ hφ.1).1 (C.W a) (C.aff a) u
    have hx := hasWt_coeff hφ hi e (fun Y => (he _ _ _ _ _ (IsPullback.of_hasPullback Y.hom f)).2) s x hu
    refine Subring.sum_mem _ fun l hl => Subring.mul_mem _ ?_ (Subring.subset_closure (Or.inl ⟨e l, rfl⟩))
    have h1 := hT.gen a (x l) (hx l hl)
    refine Subring.mem_comap.1 (Subring.closure_le.2 ?_ h1)
    rintro v (⟨w, rfl⟩ | ⟨j, hj, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨f.appTop.hom w, ?_⟩)
      have e₁ := Scheme.Hom.appLE_comp_appLE φ H.hom ⊤ (C.W a) (φ ⁻¹ᵁ C.W a) le_top le_rfl
      have e₂ := Scheme.Hom.appLE_comp_appLE H'.hom f ⊤ ⊤ (φ ⁻¹ᵁ C.W a) le_top le_top
      simp only [hφ.1.w] at e₁
      rw [φ.appLE_eq_app] at e₁
      erw [f.appLE_eq_app] at e₂
      exact congrArg (fun q => q.hom w) (e₂.trans e₁.symm)
    · exact Subring.subset_closure (Or.inr ⟨j, hj, rfl⟩)
end GlobalTheory.ZJ.SplitPull
