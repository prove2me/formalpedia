-- Prove2me | solution 1 for GlobalTheory.KS.Kunneth.kunneth_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:18:46.672717+00:00
-- url     : https://prove2.me/submissions/38d6f2d8-0d12-4d1e-8fa9-cad8fd7aa9d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDualFamilyModSubspace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCovers
import Theorems.Thm_GlobalTheory_KS_Kunneth_rsT_of_le
import Theorems.Thm_GlobalTheory_KS_Kunneth_cstHom_apply
import Theorems.Thm_GlobalTheory_KS_Kunneth_res_constFn
import Theorems.Thm_GlobalTheory_KS_Kunneth_pair_symm
import Theorems.Thm_GlobalTheory_KS_exists_symm_matrix_mod_subspace


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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Kunneth
namespace GlobalTheory.KS.Kunneth
theorem _root_.solution : ∀ (K : Type) [Field K] (Y Z : Scheme.{0}) (q : Y ⟶ Sp K) (p₁ p₂ : Z ⟶ Y) (I : Type) [Finite I] (U : I → Y.Opens) (g : ℕ) (θ φ : Fin g → C1 U), IsSeparated q → IsPullback p₁ p₂ q q → (∀ i, IsAffineOpen (U i)) → (∀ c, IsCob U (lc q c φ) → c = 0) → ∀ (u : ∀ i i' j, Γ(Z, p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j)) (u' : ∀ i j j', Γ(Z, p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))), (∀ i i' j j', ∑ a, (pbT p₁ (θ a i i') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) * pbT p₂ (φ a j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - pbT p₁ (φ a i i') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) * pbT p₂ (θ a j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) = (rsT (u i i' j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - rsT (u i i' j) (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j'))) + (rsT (u' i' j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) - rsT (u' i j j') (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')))) → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob U (θ b - lc q (Θ b) φ) := by
  intro K _ Y Z q p₁ p₂ I _ U g θ φ hq H hU hind u u' hu
  letI : ∀ i j : I, Module K Γ(Y, U i ⊓ U j) := fun i j => (cstHom q (U i ⊓ U j)).hom.toModule
  have hsmul : ∀ (c : K) (x : C1 U), c • x = fun i j => constFn q (U i ⊓ U j) c * x i j := by
    intro c x
    funext i j
    rw [← cstHom_apply]
    rfl
  have hrs_add : ∀ {O₀ O : Y.Opens} (s t : Γ(Y, O₀)), rsT (s + t) O = rsT s O + rsT t O := by
    intro O₀ O s t
    unfold rsT
    split_ifs <;> simp
  have hrs_cmul : ∀ {O₀ O : Y.Opens} (c : K) (s : Γ(Y, O₀)), O ≤ O₀ →
      rsT (constFn q O₀ c * s) O = constFn q O c * rsT s O := by
    intro O₀ O c s h
    rw [rsT_of_le _ h, rsT_of_le _ h, map_mul, res_constFn]
  let B : Submodule K (C1 U) :=
    { carrier := {c | IsCob U c}
      add_mem' := by
        rintro x y ⟨b, hb⟩ ⟨b', hb'⟩
        refine ⟨b + b', fun i j => ?_⟩
        show x i j + y i j = _
        rw [hb, hb', Pi.add_apply, Pi.add_apply, hrs_add, hrs_add]
        abel
      zero_mem' := ⟨0, fun i j => by simp [rsT]⟩
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨fun i => constFn q (U i) c * b i, fun i j => ?_⟩
        rw [hsmul]
        show constFn q _ c * x i j = _
        rw [hb, hrs_cmul c _ inf_le_right, hrs_cmul c _ inf_le_left, mul_sub] }
  have hlc : ∀ c : Fin g → K, lc q c φ = ∑ a, c a • φ a := by
    intro c
    funext i j
    simp only [lc, Finset.sum_apply, hsmul]
  have hind' : ∀ c : Fin g → K, ∑ a, c a • φ a ∈ B → c = 0 := by
    intro c hc
    apply hind c
    rw [hlc]
    exact hc
  obtain ⟨Θ, hΘ, hmem⟩ := exists_symm_matrix_mod_subspace K (C1 U) B g θ φ hind'
    (fun α β hα hβ => pair_symm θ φ hq H hU u u' hu α.toAddMonoidHom β.toAddMonoidHom
      (fun c x => by
        have e := hsmul c x
        rw [← e]
        show α (c • x) = c * α x
        rw [map_smul, smul_eq_mul])
      (fun c x => by
        have e := hsmul c x
        rw [← e]
        show β (c • x) = c * β x
        rw [map_smul, smul_eq_mul])
      (fun c hc => LinearMap.mem_ker.mp (hα hc))
      (fun c hc => LinearMap.mem_ker.mp (hβ hc)))
  refine ⟨Θ, hΘ, fun b => ?_⟩
  rw [hlc]
  exact hmem b
end GlobalTheory.KS.Kunneth
