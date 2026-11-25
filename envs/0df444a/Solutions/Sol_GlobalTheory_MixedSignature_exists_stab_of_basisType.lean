-- Prove2me | solution 1 for GlobalTheory.MixedSignature.exists_stab_of_basisType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:17:27.632995+00:00
-- url     : https://prove2.me/submissions/439611b6-2079-4428-b444-a28a2193aa64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeightedSupDriftOnOrthonormalFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsBoundOrthonormalFrame
import Theorems.Thm_GlobalTheory_MixedSignature_transfer_herm
import Theorems.Thm_GlobalTheory_FlagMahler_Qy_smul_le
import Theorems.Thm_GlobalTheory_FlagMahler_col_map_eq
import Theorems.Thm_GlobalTheory_FlagMahler_comb_bound
import Theorems.Thm_GlobalTheory_FlagMahler_comp_le_Qy
import Theorems.Thm_GlobalTheory_FlagMahler_finite_int_sq
import Theorems.Thm_GlobalTheory_FlagMahler_inv_lact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianLatticeMaps_phi_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianLatticeMaps_phi_phi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_Am_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_Ly_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_Ly_surjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_ipB_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_quad_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealPlaceEmbeddings_qb_apply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MixedSignature
open ReciprocityTheory.ChartRestriction.G.FD NumberField Module Complex
open Matrix hiding col gram
open scoped ComplexConjugate
open QuadraticLatticeForms (ip ipB ipB_apply Ly Am Qy Ly_injective Ly_surjective quad_int Am_posDef)
open HermitianLatticeMaps (phi phi_f phi_zsum phi_mem phi_phi smul_coe coe_expand mulQ mulQ_apply)
open GlobalTheory.FlagMahler (col_map_eq inv_lact comp_le_Qy comb_bound Qy_smul_le finite_int_sq)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {f f' : Basis ι ℤ X.Λ}
namespace GlobalTheory.MixedSignature
theorem _root_.solution (h : basisType X G f = basisType X G f') :
    ∃ γ : GL (Fin r) E, IsUStab G X.Λ γ ∧
      (∀ i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (f i : Fin r → E) = f' i) ∧
      ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v =
        ∑ i, (RealPlaceEmbeddings.qb X f').repr v i • (f i : Fin r → E) := by
  have h' : basisType X G f' = basisType X G f := h.symm
  set A := LinearMap.toMatrix' (transferE X h) with hA
  set B := LinearMap.toMatrix' (transferE X h') with hB
  have hAB : A * B = 1 := by
    rw [hA, hB, ← LinearMap.toMatrix'_comp]
    have : (transferE X h).comp (transferE X h') = LinearMap.id :=
      LinearMap.ext fun x => phi_phi X f' f x
    rw [this, LinearMap.toMatrix'_id]
  have hBA : B * A = 1 := by
    rw [hA, hB, ← LinearMap.toMatrix'_comp]
    have : (transferE X h').comp (transferE X h) = LinearMap.id :=
      LinearMap.ext fun x => phi_phi X f f' x
    rw [this, LinearMap.toMatrix'_id]
  have hAv : ∀ v, A *ᵥ v = phi X f f' v := fun v => by
    rw [hA, LinearMap.toMatrix'_mulVec]; rfl
  have hBv : ∀ v, B *ᵥ v = phi X f' f v := fun v => by
    rw [hB, LinearMap.toMatrix'_mulVec]; rfl
  refine ⟨⟨A, B, hAB, hBA⟩, ⟨fun x y => ?_, fun x => ?_⟩, fun i => ?_, fun v => ?_⟩
  · change herm G (A *ᵥ x) (A *ᵥ y) = herm G x y
    rw [hAv, hAv, transfer_herm X h]
  · change x ∈ X.Λ ↔ A *ᵥ x ∈ X.Λ
    rw [hAv]
    refine ⟨fun hx => phi_mem X f f' hx, fun hx => ?_⟩
    have := phi_mem X f' f hx
    rwa [phi_phi] at this
  · change A *ᵥ (f i : Fin r → E) = f' i
    rw [hAv, phi_f]
  · change B *ᵥ v = _
    rw [hBv]
    conv_lhs => rw [← (RealPlaceEmbeddings.qb X f').sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, RealPlaceEmbeddings.qb_apply, phi_f]
end GlobalTheory.MixedSignature
