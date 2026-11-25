-- Prove2me | solution 1 for GlobalTheory.AbCoh.exteriorSquare_equiv_of_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:20:12.496538+00:00
-- url     : https://prove2.me/submissions/6729bd1b-ecb6-4e2f-a669-1eb36db01577

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorSquareEquivOfBaseChangeField
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (M N M' N' : Type) [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] [AddCommGroup M'] [Module L M'] [AddCommGroup N'] [Module L N'] (c : M →ₗ[K] M →ₗ[K] N) (c' : M' →ₗ[L] M' →ₗ[L] N') (e₁ : L ⊗[K] M ≃ₗ[L] M') (e₂ : L ⊗[K] N ≃ₗ[L] N'), (∀ a b, e₂ (1 ⊗ₜ c a b) = c' (e₁ (1 ⊗ₜ a)) (e₁ (1 ⊗ₜ b))) → (∃ e : ⋀[L]^2 M' ≃ₗ[L] N', ∀ a b, e (exteriorPower.ιMulti L 2 ![a, b]) = c' a b) → ∃ e : ⋀[K]^2 M ≃ₗ[K] N, ∀ a b, e (exteriorPower.ιMulti K 2 ![a, b]) = c a b := by
  intro K L _ _ _ M N M' N' _ _ _ _ _ _ _ _ c c' e₁ e₂ hcomp hex
  classical
  obtain ⟨eL, heL⟩ := hex

  have hinj : Function.Injective (TensorProduct.mk K L N 1) := by
    have h1 : Function.Injective ((Algebra.linearMap K L).rTensor N) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K L).injective
    intro x y hxy
    apply (TensorProduct.lid K N).symm.injective
    apply h1
    simpa [TensorProduct.lid_symm_apply] using hxy

  have hc : ∀ a, c a a = 0 := by
    intro a
    apply hinj
    apply e₂.injective
    have h0 : exteriorPower.ιMulti L 2 ![e₁ (1 ⊗ₜ a), e₁ (1 ⊗ₜ a)] = 0 :=
      AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := 1) rfl (by decide)
    simp only [TensorProduct.mk_apply, hcomp, TensorProduct.tmul_zero, map_zero, ← heL, h0]
  let f : M [⋀^Fin 2]→ₗ[K] N :=
    { toFun := fun w => c (w 0) (w 1)
      map_update_add' := by
        intro _ w i x y
        fin_cases i <;> simp
      map_update_smul' := by
        intro _ w i r x
        fin_cases i <;> simp
      map_eq_zero_of_eq' := by
        intro w i j hij hne
        fin_cases i <;> fin_cases j <;> simp_all [hc] }
  let φ := exteriorPower.alternatingMapLinearEquiv f
  have hφ : ∀ w : Fin 2 → M, φ (exteriorPower.ιMulti K 2 w) = c (w 0) (w 1) := fun w =>
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti f w
  let b := Module.Basis.ofVectorSpace K M
  letI : LinearOrder (Module.Basis.ofVectorSpaceIndex K M) := linearOrderOfSTO WellOrderingRel
  let B := b.exteriorPower 2
  let b' := (Algebra.TensorProduct.basis L b).map e₁
  have hb' : ∀ i, b' i = e₁ (1 ⊗ₜ b i) := fun i => by
    simp [b', Algebra.TensorProduct.basis_apply]
  let B' := b'.exteriorPower 2
  have key : ∀ s, e₂ (1 ⊗ₜ φ (B s)) = eL (B' s) := by
    intro s
    rw [exteriorPower.basis_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
      exteriorPower.ιMulti_family, hφ, hcomp, ← heL]
    congr 2
    funext i
    fin_cases i <;> simp [hb']
  let V' := B'.map (eL.trans e₂.symm)
  have hV' : ∀ s, V' s = (1 : L) ⊗ₜ[K] φ (B s) := fun s => by
    simp only [V', Module.Basis.map_apply, LinearEquiv.trans_apply]
    rw [← key, LinearEquiv.symm_apply_apply]
  have h1 : LinearIndependent L (fun s => (1 : L) ⊗ₜ[K] φ (B s)) := by
    have h := V'.linearIndependent
    rwa [show (⇑V') = fun s => (1 : L) ⊗ₜ[K] φ (B s) from funext hV'] at h
  have h2 : LinearIndependent K (fun s => (1 : L) ⊗ₜ[K] φ (B s)) := h1.restrict_scalars' K
  have h3 : LinearIndependent K (φ ∘ B) := LinearIndependent.of_comp (TensorProduct.mk K L N 1) h2
  let W := Submodule.span K (Set.range (φ ∘ B))
  have hs : Function.Surjective (W.subtype.lTensor L) := by
    have hr : LinearMap.range (W.subtype.baseChange L) = ⊤ := by
      rw [eq_top_iff, ← V'.span_eq, Submodule.span_le]
      rintro _ ⟨s, rfl⟩
      rw [hV']
      exact ⟨1 ⊗ₜ ⟨φ (B s), Submodule.subset_span ⟨s, rfl⟩⟩, rfl⟩
    intro x
    obtain ⟨y, hy⟩ := LinearMap.range_eq_top.mp hr x
    exact ⟨y, by rw [← LinearMap.baseChange_eq_ltensor]; exact hy⟩
  have hW : Function.Surjective W.subtype :=
    (Module.FaithfullyFlat.lTensor_surjective_iff_surjective K L W.subtype).mp hs
  have hspan : ⊤ ≤ W := fun x _ => by
    obtain ⟨y, rfl⟩ := hW x
    exact y.2
  let V := Module.Basis.mk h3 hspan
  refine ⟨B.equiv V (Equiv.refl _), fun a b => ?_⟩
  have hEq : (B.equiv V (Equiv.refl _)).toLinearMap = φ :=
    B.ext fun s => by simp [V, Module.Basis.mk_apply]
  rw [← LinearEquiv.coe_coe, hEq, hφ]
  rfl
end GlobalTheory.AbCoh
