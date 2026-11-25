-- Prove2me | solution 1 for GlobalTheory.KS.exists_isSymm_of_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:55:25.598251+00:00
-- url     : https://prove2.me/submissions/c4095d69-78f0-4617-bec7-edfe8eeac0cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCobOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCoversStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsSymmOfSquare
import Theorems.Thm_GlobalTheory_KS_Square_rsT_add
import Theorems.Thm_GlobalTheory_KS_Square_rsT_sub
import Theorems.Thm_GlobalTheory_KS_Square_rsT_neg
import Theorems.Thm_GlobalTheory_KS_Square_rsT_mul
import Theorems.Thm_GlobalTheory_KS_Square_rsT_sum
import Theorems.Thm_GlobalTheory_KS_Square_rsT_rsT
import Theorems.Thm_GlobalTheory_KS_Square_rsT_pbT
import Theorems.Thm_GlobalTheory_KS_Square_ext_cover
import Theorems.Thm_GlobalTheory_KS_Square_isAffineOpen_prod
import Theorems.Thm_GlobalTheory_KS_Square_exists_split
import Theorems.Thm_GlobalTheory_KS_Square_exists_compare
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_kerEquiv_val
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_T_kunneth_symm_product_affine_covers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AbLaw.CechOne.kerEquiv_val
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS
open Square
namespace GlobalTheory.KS
theorem _root_.solution : ∀ (K : Type) [Field K] (Y Z : Scheme.{0}) (q : Y ⟶ Sp K) (p₁ p₂ : Z ⟶ Y) (I : Type) [Finite I] (U : I → Y.Opens) (g : ℕ) (θ φ : Fin g → C1 U), IsSeparated q → IsPullback p₁ p₂ q q → (∀ i, IsAffineOpen (U i)) → (∀ c, IsCob U (lc q c φ) → c = 0) → ∀ (J : Type) (V : J → Z.Opens) (k : ∀ i j, C1 (fun α => p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j ⊓ V α)) (e : Fin g → ∀ j α, Γ(Z, p₂ ⁻¹ᵁ U j ⊓ V α)) (e' : Fin g → ∀ i α, Γ(Z, p₁ ⁻¹ᵁ U i ⊓ V α)), ⨆ α, V α = ⊤ → (∀ i j, IsCoc _ (k i j)) → (∀ a j j' α O, O ≤ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α → rsT (e a j' α) O - rsT (e a j α) O = pbT p₂ (φ a j j') O) → (∀ a i i' α O, O ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ V α → rsT (e' a i' α) O - rsT (e' a i α) O = pbT p₁ (φ a i i') O) → (∀ i i' j α β O, O ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j ⊓ V α ⊓ V β → rsT (k i' j α β) O - rsT (k i j α β) O = ∑ a, pbT p₁ (θ a i i') O * (rsT (e a j α) O - rsT (e a j β) O)) → (∀ i j j' α β O, O ≤ p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α ⊓ V β → rsT (k i j' α β) O - rsT (k i j α β) O = ∑ a, pbT p₂ (θ a j j') O * (rsT (e' a i α) O - rsT (e' a i β) O)) → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob U (θ b - lc q (Θ b) φ) := by
  intro K _ Y Z q p₁ p₂ I _ U g θ φ hq H hU hφ J V k e e' hV hk he he' hk₁ hk₂
  have hA : ∀ i j, IsAffineOpen (p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j) := fun i j =>
    isAffineOpen_prod H (hU i) (hU j)
  choose c hc using fun i j => exists_split hV (hA i j) (k i j) (hk i j)
  choose u hu using fun i i' j => exists_compare hV p₁ (T := U i ⊓ U i')
    (W := p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j) (A := p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j)
    (B := p₁ ⁻¹ᵁ U i' ⊓ p₂ ⁻¹ᵁ U j) (E := p₂ ⁻¹ᵁ U j)
    (inf_le_inf_right _ (p₁.preimage_mono inf_le_left)) (inf_le_inf_right _ (p₁.preimage_mono inf_le_right))
    inf_le_right inf_le_left (fun a => θ a i i') (fun a => e a j) (k i j) (k i' j) (c i j) (c i' j)
    (hc i j) (hc i' j) (hk₁ i i' j)
  choose v hv using fun i j j' => exists_compare hV p₂ (T := U j ⊓ U j')
    (W := p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j')) (A := p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j)
    (B := p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j') (E := p₁ ⁻¹ᵁ U i)
    (inf_le_inf_left _ (p₂.preimage_mono inf_le_left)) (inf_le_inf_left _ (p₂.preimage_mono inf_le_right))
    inf_le_left inf_le_right (fun a => θ a j j') (fun a => e' a i) (k i j) (k i j') (c i j) (c i j')
    (hc i j) (hc i j') (hk₂ i j j')
  refine GlobalTheory.T.kunneth_symm_product_affine_covers K Y Z q p₁ p₂ I U g θ φ hq H hU hφ u (fun i j j' => -v i j j') ?_
  intro i i' j j'
  apply ext_cover hV
  intro α
  have hQ1 : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j' :=
    inf_le_inf_left _ (p₂.preimage_mono inf_le_right)
  have hQ2 : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j :=
    inf_le_inf_left _ (p₂.preimage_mono inf_le_left)
  have hQ3 : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ≤ p₁ ⁻¹ᵁ U i' ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') :=
    inf_le_inf_right _ (p₁.preimage_mono inf_le_right)
  have hQ4 : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ≤ p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') :=
    inf_le_inf_right _ (p₁.preimage_mono inf_le_left)
  have hu₁ := hu i i' j' α _ (inf_le_inf_right (V α) hQ1)
  have hu₂ := hu i i' j α _ (inf_le_inf_right (V α) hQ2)
  have hv₁ := hv i' j j' α _ (inf_le_inf_right (V α) hQ3)
  have hv₂ := hv i j j' α _ (inf_le_inf_right (V α) hQ4)
  have hφ₂ := fun a => he a j j' α (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α) (inf_le_inf_right (V α) inf_le_right)
  have hφ₁ := fun a => he' a i i' α (p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α) (inf_le_inf_right (V α) inf_le_left)
  have hO : p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α ≤
      p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') := inf_le_left
  simp only [rsT_add, rsT_sub, rsT_neg, rsT_sum, rsT_mul, rsT_rsT hO hQ1, rsT_rsT hO hQ2,
    rsT_rsT hO hQ3, rsT_rsT hO hQ4, rsT_pbT p₁ hO inf_le_left, rsT_pbT p₂ hO inf_le_right]
  rw [hu₁, hu₂, hv₁, hv₂]
  simp only [← hφ₁, ← hφ₂, mul_sub, sub_mul, Finset.sum_sub_distrib]
  simp only [mul_comm (rsT (e' _ _ α) _)]
  ring
end GlobalTheory.KS
