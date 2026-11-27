-- Prove2me | solution 1 for GlobalTheory.TorusTransfer.torus_algebraic_of_siegel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:35:00.739487+00:00
-- url     : https://prove2.me/submissions/99a93c4b-c26a-4ed1-a095-5b897ec4bfee

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FderivEqZeroOfAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_PolarisedTorusAlgebraicOfParts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqZeroOfFderivEqZero
import Theorems.Thm_GlobalTheory_TorusTransfer_tangent_bijective
import Theorems.Thm_GlobalTheory_TorusTransfer_frame_law
import Theorems.Thm_GlobalTheory_TorusTransfer_exists_siegel_coordinates
import Theorems.Thm_GlobalTheory_TorusTransfer_autFactor_mul_exp
import Theorems.Thm_GlobalTheory_SiegelNormalForm_quad_differentiable
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_thetaChar_ofRealVec_eq_theta
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_PTheta_thetaQuasiPeriod_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real CategoryTheory.Obj
open GlobalTheory GlobalTheory.TorusTransfer
namespace GlobalTheory.TorusTransfer
theorem _root_.solution :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∃ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L g) (th : P.L.Sec), P.g = g ∧ (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧ u.IsFn th (thetaChar τ a b) ∧ ∀ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ l ∈ u.Λ, F l ∈ u.Λ) → ∃ f : P.A ⟶ P.A, IsMonHom f ∧ ∀ z, u.ex (F z) = u.ex z ≫ f) →
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) → Function.Bijective Ef → ∃ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L g) (χ : u.Λ → ℂ), P.g = g ∧ u.Λ = Λ ∧ u.IsAH Hm χ ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) := by
  intro H g Λ Hm Ef hd hf hH hpos hE hbij
  obtain ⟨φ, τ, Y, hs, hp, hΛ, hY, hYτ, hform⟩ := exists_siegel_coordinates Λ hd hf Hm Ef hH hpos hE hbij
  have h0 : ∀ i : Fin g, ofRealVec (0 : Fin g → ℝ) i = 0 ∨ ofRealVec (0 : Fin g → ℝ) i = 1 / 2 :=
    fun i => Or.inl (by simp [ofRealVec])
  obtain ⟨P, u, th, hg, hu, hth, -⟩ := H g τ _ _ hs hp h0 h0
  rw [thetaChar_ofRealVec_eq_theta] at hth
  have hψ : ∀ z, φ.symm z ∈ u.Λ ↔ z ∈ Λ := fun z => by
    rw [hu, ← hΛ, LinearEquiv.apply_symm_apply]
  have hmn : ∀ l : Λ, ∃ m n : Fin g → ℤ, φ.symm l = τ *ᵥ ofIntVec n + ofIntVec m := fun l => by
    obtain ⟨m, n, h⟩ := (hu _).1 ((hψ _).2 l.2)
    exact ⟨m, n, h.trans (add_comm _ _)⟩
  choose m n hmn using hmn
  have hform' : ∀ z w, z ⬝ᵥ Hm *ᵥ star w = φ.symm z ⬝ᵥ Y.map (↑) *ᵥ star (φ.symm w) := fun z w => by
    rw [← hform, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hsm : SmoothOfRelativeDimension g P.A.hom := hg ▸ P.smoothDim
  refine ⟨P, reparam u φ.symm (fun z => -SiegelNormalForm.quad (Y.map (↑)) 0 z)
    (SiegelNormalForm.quad_differentiable _ _).neg Λ hd hf hψ,
    fun l => cexp (((Real.pi * ((n l ⬝ᵥ m l : ℤ) : ℝ) : ℝ) : ℂ) * I), hg, rfl,
    ⟨hH, hpos, fun l => Complex.norm_exp_ofReal_mul_I _, fun l i z hz => ?_⟩, tangent_bijective _ hsm⟩
  have h1 := frame_law u th _ (autFactor 0 0 τ (n l) (m l)) (differentiable_theta ⟨hs, hp⟩ 0 0)
    (theta_ne_zero ⟨hs, hp⟩ 0 0) (by unfold autFactor eC; simp only [dotProduct]; fun_prop) hth (φ.symm l)
    ((hψ _).2 l.2) (fun z => by rw [hmn l, ← add_assoc]; exact thetaQuasiPeriod_holds _ _ _ _ _ _ _ hs) i
    (φ.symm z) hz
  have h2 := autFactor_mul_exp hY hYτ (n l) (m l) (φ.symm z) (φ.symm l) (hmn l)
  change u.fr i (φ.symm z) * cexp (-SiegelNormalForm.quad (Y.map (↑)) 0 (φ.symm z)) =
    _ * (u.fr i (φ.symm (z + l)) * cexp (-SiegelNormalForm.quad (Y.map (↑)) 0 (φ.symm (z + l))))
  rw [hform', hform', map_add, h1]
  linear_combination u.fr i (φ.symm z + φ.symm l) * h2
end GlobalTheory.TorusTransfer
