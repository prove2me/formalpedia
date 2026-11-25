-- Prove2me | solution 1 for GlobalTheory.nonempty_baseChange_grCube_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:13:34.741802+00:00
-- url     : https://prove2.me/submissions/013ccd32-c211-41c3-99a2-400ad5a431e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsBaseChangeAwayOfIntertwine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsBaseChangeGradedPiece
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBaseChangeGrCubeIso
import Theorems.Thm_GlobalTheory_map_xProd_pow_smul_of_X
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_exists_isBaseChange_away_xProd
import Theorems.Thm_GlobalTheory_isBaseChange_gradedPiece
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (N₀ : Type) [AddCommGroup N₀] [Module R₀ N₀] [Module (MvPolynomial ι R₀) N₀] [IsScalarTower R₀ (MvPolynomial ι R₀) N₀] (𝒩₀ : ℤ → Submodule R₀ N₀) [PolyGradedSMul ι 𝒩₀] [Decomposition 𝒩₀] (N : Type) [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N] [IsScalarTower R (MvPolynomial ι R) N] (𝒩 : ℤ → Submodule R N) [PolyGradedSMul ι 𝒩] [Decomposition 𝒩] [Module R₀ N] [IsScalarTower R₀ R N] [IsScalarTower R₀ (MvPolynomial ι R) N] (ψ : N₀ →ₗ[R₀] N) (n : ℤ), IsBaseChange R ψ → (∀ (i : ι) y, ψ ((X i : MvPolynomial ι R₀) • y) = (X i : MvPolynomial ι R) • ψ y) → (∀ j, ∀ y ∈ 𝒩₀ j, ψ y ∈ 𝒩 j) → Nonempty (Cube.baseChange R (grCube ι 𝒩₀ n) ≅ grCube ι 𝒩 n) := by
  intro ι _ _ R₀ R _ _ _ N₀ _ _ _ _ 𝒩₀ _ _ N _ _ _ _ 𝒩 _ _ _ _ _ ψ n hψ hX hgr
  choose θ hθ hθe using fun s : Finset ι => GlobalTheory.exists_isBaseChange_away_xProd ι R₀ R N₀ N ψ s hψ hX
  have hg : ∀ s j, ∀ y ∈ homLoc 𝒩₀ s j, θ s y ∈ homLoc 𝒩 s j := by
    rintro s j _ ⟨k, m, hm, rfl⟩
    rw [hθe]
    exact awayFrac_mem_homLoc (hgr _ _ hm) rfl
  let η : ∀ s, homLoc 𝒩₀ s n →ₗ[R₀] homLoc 𝒩 s n := fun s =>
    { toFun := fun y => ⟨θ s y, hg s n _ y.2⟩
      map_add' := fun a b => Subtype.ext (map_add (θ s) a.1 b.1)
      map_smul' := fun r a => Subtype.ext (map_smul (θ s) r a.1) }
  have hη : ∀ s, IsBaseChange R (η s) := fun s =>
    GlobalTheory.isBaseChange_gradedPiece R₀ R _ _ (homLoc 𝒩₀ s) (homLoc 𝒩 s) (θ s) n (η s) (hθ s) (hg s) fun _ => rfl
  have hres : ∀ {s t : Finset ι} (h : s ⊆ t) (z : homLoc 𝒩₀ s n),
      η t (homLocRes 𝒩₀ h n z) = homLocRes 𝒩 h n (η s z) := by
    rintro s t h ⟨_, k, m, hm, rfl⟩
    apply Subtype.ext
    change θ t (locRes X N₀ h (awayFrac N₀ _ k m)) = locRes X N h (θ s (awayFrac N₀ _ k m))
    rw [hθe, locRes_awayFrac X h (Finset.prod_sdiff h).symm,
      locRes_awayFrac X h (Finset.prod_sdiff h).symm, hθe]
    exact congrArg _ (map_xProd_pow_smul_of_X ψ hX (t \ s) k m)
  have key : ∀ {s t : Finset ι} (h : s ⊆ t) (x : R ⊗[R₀] homLoc 𝒩₀ s n),
      (hη t).equiv ((homLocRes 𝒩₀ h n).baseChange R x) = homLocRes 𝒩 h n ((hη s).equiv x) := by
    intro s t h x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul r z =>
      rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul, map_smul,
        hres]
  exact ⟨Cube.isoMk (fun s => (hη s).equiv) fun h x => key h x⟩
end GlobalTheory
