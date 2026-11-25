-- Prove2me | solution 1 for GlobalTheory.TorusTransfer.exists_siegel_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:13:51.781735+00:00
-- url     : https://prove2.me/submissions/72193ca8-5463-48e9-8b46-26c0d50f5bf5

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
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_right
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_right
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_left_right
import Theorems.Thm_GlobalTheory_SiegelNormalForm_form_conj
import Theorems.Thm_GlobalTheory_SiegelNormalForm_form_pull
import Theorems.Thm_GlobalTheory_SiegelNormalForm_form_single
import Theorems.Thm_GlobalTheory_SiegelNormalForm_isUnit_of_lagrangian
import Theorems.Thm_GlobalTheory_SiegelNormalForm_siegel_of_relations
import Theorems.Thm_GlobalTheory_bijective_neg_bilinForm
import Theorems.Thm_GlobalTheory_exists_isSymplecticBasis_of_finrank
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
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
open SiegelNormalForm
variable {g : ℕ}
namespace GlobalTheory.TorusTransfer
theorem _root_.solution (Λ : Submodule ℤ (Fin g → ℂ)) (hdisc : DiscreteTopology Λ)
    (hspan : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (Ef : LinearMap.BilinForm ℤ Λ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hE : ∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)
    (hbij : Function.Bijective Ef) :
    ∃ (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ) (Y : Matrix (Fin g) (Fin g) ℝ),
      τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧
      (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
      (Y.map (↑) : Matrix _ _ ℂ).IsSymm ∧ Y * τ.map Complex.im = 1 ∧
      ∀ z w, φ z ⬝ᵥ Hm *ᵥ star (φ w) = z ⬝ᵥ Y.map (↑) *ᵥ star w := by
  have : IsZLattice ℝ Λ := ⟨hspan⟩
  have halt : Ef.IsAlt := fun l => by
    have h1 := congrArg Complex.im (form_conj hH (l : Fin g → ℂ) l)
    have h2 := hE l l
    simp only [Complex.star_def, Complex.conj_im] at h1
    have : (Ef l l : ℝ) = 0 := by linarith
    exact_mod_cast this
  have hrank : Module.finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
    simp [mul_comm]
  obtain ⟨bs, hbs⟩ := GlobalTheory.exists_isSymplecticBasis_of_finrank (B := -Ef) halt.neg
    (GlobalTheory.bijective_neg_bilinForm hbij) hrank
  set e : Fin g → Λ := fun i => bs (Sum.inl i) with he
  set f : Fin g → Λ := fun i => bs (Sum.inr i) with hf
  have hee : ∀ i j, ((e i : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (e j : Fin g → ℂ)).im = 0 := fun i j => by
    have := hbs.left_left i j
    simp only [LinearMap.neg_apply, neg_eq_zero] at this
    rw [← hE, this]; simp
  have hff : ∀ i j, ((f i : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (f j : Fin g → ℂ)).im = 0 := fun i j => by
    have := hbs.right_right i j
    simp only [LinearMap.neg_apply, neg_eq_zero] at this
    rw [← hE, this]; simp
  have hef : ∀ i j, ((e i : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (f j : Fin g → ℂ)).im =
      if i = j then -1 else 0 := fun i j => by
    have := hbs.left_right i j
    simp only [LinearMap.neg_apply, neg_eq_iff_eq_neg] at this
    rw [← hE, this]; split_ifs <;> simp
  let P : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k i => (e i : Fin g → ℂ) k
  have hP : ∀ i, P *ᵥ Pi.single i 1 = e i := fun i => by
    ext k; simp [P]
  let Y : Matrix (Fin g) (Fin g) ℝ := (Pᵀ * Hm * P.map star).map Complex.re
  have hYe : ∀ i j, (Pᵀ * Hm * P.map star) i j =
      (e i : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (e j : Fin g → ℂ) := fun i j => by
    rw [← form_single (Pᵀ * Hm * P.map star), ← form_pull, hP, hP]
  have hY : Pᵀ * Hm * P.map star = Y.map (↑) := by
    ext i j
    apply Complex.ext
    · simp [Y]
    · rw [hYe, hee]; simp
  have hPu : IsUnit P := isUnit_of_lagrangian P Hm (fun j => f j) hpos Y hY
    (fun i j => by rw [hP, hef])
  have hPi : Function.Injective P.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hPu
  have hPs : Function.Surjective P.mulVec := Matrix.mulVec_surjective_iff_isUnit.2 hPu
  let φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofBijective P.mulVecLin ⟨hPi, hPs⟩
  have hφ : ∀ z, φ z = P *ᵥ z := fun z => rfl
  let τ : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k j => φ.symm (f j) k
  have hτ : ∀ j, P *ᵥ (τ *ᵥ Pi.single j 1) = f j := fun j => by
    rw [← hφ, ← LinearEquiv.eq_symm_apply]
    ext k; simp [τ]
  have hform : ∀ z w, (P *ᵥ z) ⬝ᵥ Hm *ᵥ star (P *ᵥ w) = z ⬝ᵥ Y.map (↑) *ᵥ star w :=
    fun z w => by rw [form_pull, hY]
  have hYs : Yᵀ = Y := by
    ext i j
    have := congrArg Complex.re (form_conj hH (e i : Fin g → ℂ) (e j))
    simp only [Complex.star_def, Complex.conj_re] at this
    simp only [Y, Matrix.transpose_apply, Matrix.map_apply, hYe, this]
  have hYp : Y.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa [Matrix.IsHermitian] using hYs) ?_
    intro a ha
    have hne : P *ᵥ (fun i => (a i : ℂ)) ≠ 0 := by
      intro h0
      have := hPi (h0.trans (Matrix.mulVec_zero P).symm)
      exact ha (funext fun i => by simpa using congrFun this i)
    have := hpos _ hne
    rw [hform] at this
    simpa [Matrix.mulVec, dotProduct] using this
  obtain ⟨hτs, hτp, hYτ⟩ := siegel_of_relations Y hYp τ
    (fun i j => by rw [← hform, hP, hτ, hef]) (fun i j => by rw [← hform, hτ, hτ, hff])
  have hYs' : (Y.map (↑) : Matrix _ _ ℂ).IsSymm := by
    ext i j
    simpa using congrFun (congrFun hYs i) j
  have hcomb : ∀ m n : Fin g → ℤ, φ ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) =
      ((∑ i, m i • e i + ∑ i, n i • f i : Λ) : Fin g → ℂ) := fun m n => by
    have h1 : ∀ m : Fin g → ℤ, (fun i => (m i : ℂ)) = ∑ i, m i • (Pi.single i 1 : Fin g → ℂ) := by
      intro m; ext k; simp [Finset.sum_apply, Pi.single_apply]
    rw [h1 m, h1 n, hφ]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, hP, hτ]
    simp
  refine ⟨φ, τ, Y, hτs, hτp, fun z => ⟨fun hz => ?_, ?_⟩, hYs', hYτ, hform⟩
  · refine ⟨fun i => bs.repr ⟨_, hz⟩ (Sum.inl i), fun i => bs.repr ⟨_, hz⟩ (Sum.inr i),
      φ.injective ?_⟩
    rw [hcomb]
    have := bs.sum_repr ⟨_, hz⟩
    rw [Fintype.sum_sum_type] at this
    rw [this]
  · rintro ⟨m, n, rfl⟩
    rw [hcomb]
    exact Subtype.coe_prop _
end GlobalTheory.TorusTransfer
