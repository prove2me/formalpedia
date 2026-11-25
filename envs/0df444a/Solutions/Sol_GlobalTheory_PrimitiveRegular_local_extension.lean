-- Prove2me | solution 1 for GlobalTheory.PrimitiveRegular.local_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:19:10.504453+00:00
-- url     : https://prove2.me/submissions/eccb2efc-7338-45b5-8ac2-9bced7cc14a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowThetaFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowEqThetaLevelChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfLocallyRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PrimitiveRegularOnSectionNonzeroLocus
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_pow
import Theorems.Thm_GlobalTheory_ThetaBundleSym_HasFactor_mul
import Theorems.Thm_GlobalTheory_ThetaBundleSym_HasFactor_pow
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply


section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.PrimitiveRegular
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}
private theorem valAt'_eq_ΓSpecIso_appLE {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {W : Y.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W) (f : Γ(Y, W)) :
    valAt' y W f = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((y.appLE W ⊤ hW).hom f) := by
  unfold valAt' valAt
  rw [dif_pos hW]
private theorem valAt'_presheaf_map_of_le_of_whole_le_preimage {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {V W : Y.Opens} (hVW : V ≤ W)
    (hV : ⊤ ≤ y ⁻¹ᵁ V) (f : Γ(Y, W)) :
    valAt' y V ((Y.presheaf.map (homOfLE hVW).op).hom f) = valAt' y W f := by
  rw [valAt'_eq_ΓSpecIso_appLE y hV, valAt'_eq_ΓSpecIso_appLE y (hV.trans fun q hq => hVW hq)]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
private theorem valAt'_mul_of_whole_le_preimage {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {W : Y.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f f' : Γ(Y, W)) : valAt' y W (f * f') = valAt' y W f * valAt' y W f' := by
  simp only [valAt'_eq_ΓSpecIso_appLE y hW, map_mul]
private theorem valAt'_pow_of_whole_le_preimage {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {W : Y.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f : Γ(Y, W)) (m : ℕ) : valAt' y W (f ^ m) = valAt' y W f ^ m := by
  simp only [valAt'_eq_ΓSpecIso_appLE y hW, map_pow]
private theorem top_le_comap_basicOpen_of_valAt'_ne_zero {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {W : Y.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f : Γ(Y, W)) (hf : valAt' y W f ≠ 0) : ⊤ ≤ y ⁻¹ᵁ Y.basicOpen f := by
  rw [valAt'_eq_ΓSpecIso_appLE y hW] at hf
  have hu : IsUnit ((y.appLE W ⊤ hW).hom f) := by
    have h2 := (IsUnit.mk0 _ hf).map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    simpa using h2
  have h3 : (Sp ℂ).basicOpen ((y.appLE W ⊤ hW).hom f) = ⊤ := Scheme.basicOpen_of_isUnit _ hu
  have h4 : (Sp ℂ).basicOpen ((y.appLE W ⊤ hW).hom f) ≤ y ⁻¹ᵁ Y.basicOpen f := by
    rw [Scheme.preimage_basicOpen]
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res]
    exact inf_le_right
  exact h3.symm.le.trans h4
end GlobalTheory.PrimitiveRegular
namespace GlobalTheory
open PrimitiveRegular
end GlobalTheory
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.PrimitiveRegular
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}
namespace GlobalTheory.PrimitiveRegular
theorem _root_.solution (u : HolUnif A L g) (hL : L.IsLB) {I : Type} (O : I → A.left.Opens)
    (c : ∀ i i', Γ(A.left, O i ⊓ O i')) (h : I → (Fin g → ℂ) → ℂ) (hO : ⨆ i, O i = ⊤)
    (hh : ∀ i, DifferentiableOn ℂ (h i) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i})
    (hc : ∀ i i' z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (O i ⊓ O i') →
      valAt' (u.ex z).left (O i ⊓ O i') (c i i') = h i' z - h i z)
    (i : I) {n : ℕ} (σ : (lbPow L n).Sec) (hσ : Out.nonzeroLocus σ ≤ O i) {θ : (Fin g → ℂ) → ℂ}
    (hd : Differentiable ℂ θ) (hθ : u.IsFnPow n σ θ) (x : A.left) :
    ∃ (Q : A.left.Opens) (N : ℕ) (F : (Fin g → ℂ) → ℂ), x ∈ Q ∧
      DifferentiableOn ℂ F {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ Q} ∧
      ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Q → θ z ≠ 0 → θ z ^ N * h i z = F z := by
  obtain ⟨i', hxi'⟩ := TopologicalSpace.Opens.mem_iSup.mp (show x ∈ ⨆ i, O i from hO ▸ trivial)
  obtain ⟨j, hxj⟩ := TopologicalSpace.Opens.mem_iSup.mp (show x ∈ ⨆ j, L.U j from hL.1 ▸ trivial)
  let k : (lbPow L n).ι := fun _ => j
  have hUk : (lbPow L n).U k ≤ L.U j := fun p hp => by simpa using Set.mem_iInter.mp hp PUnit.unit
  have hxk : x ∈ (lbPow L n).U k := Set.mem_iInter.mpr fun _ => by simpa using hxj
  have hB : TopologicalSpace.Opens.IsBasis A.left.affineOpens := by
    first
      | exact AlgebraicGeometry.isBasis_affineOpens A.left
      | exact AlgebraicGeometry.Scheme.isBasis_affineOpens A.left
  obtain ⟨V, hVa, hxV, hVle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp hB) (show x ∈ O i' ⊓ (lbPow L n).U k from ⟨hxi', hxk⟩)
  have hV1 : V ≤ O i' := hVle.trans inf_le_left
  have hV2 : V ≤ (lbPow L n).U k := hVle.trans inf_le_right
  set sV := (A.left.presheaf.map (homOfLE hV2).op).hom (σ.f k) with hsV
  have hD : A.left.basicOpen sV ≤ O i ⊓ O i' := by
    refine le_inf ?_ ((A.left.basicOpen_le sV).trans hV1)
    refine le_trans ?_ hσ
    rw [hsV, Scheme.basicOpen_res]
    refine inf_le_right.trans ?_
    unfold ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus
    exact le_iSup (fun k => A.left.basicOpen (σ.f k)) k
  obtain ⟨N, a, ha⟩ := exists_eq_pow_mul_of_isAffineOpen A.left V hVa sV
    ((A.left.presheaf.map (homOfLE hD).op).hom (c i i'))
  have hS1 : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ V} ⊆ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i'} :=
    fun z hz q hq => hV1 (hz hq)
  have hS2 : {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ V} ⊆ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j} :=
    fun z hz q hq => hUk (hV2 (hz hq))
  refine ⟨V, N, fun z => θ z ^ N * h i' z - valAt' (u.ex z).left V a * (u.fr j z ^ (n * N))⁻¹, hxV, ?_, ?_⟩
  · have hfrd : DifferentiableOn ℂ (fun z => u.fr j z ^ (n * N)) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ V} :=
      ((u.10 j).mono hS2).pow _
    exact ((hd.pow N).differentiableOn.mul ((hh i').mono hS1)).sub
      ((u.8 V a).2.mul (hfrd.inv fun z hz => pow_ne_zero _ (u.11 j z (hS2 hz))))
  · intro z hz hz0
    have hzk : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U k := hz.trans fun q hq => hV2 hq
    have hfr : u.fr j z ≠ 0 := u.11 j z (hS2 hz)
    have hs : valAt' (u.ex z).left V sV = θ z * u.fr j z ^ n := by
      rw [hsV, valAt'_presheaf_map_of_le_of_whole_le_preimage _ hV2 hz]
      exact hθ k z hzk
    have hzD : ⊤ ≤ (u.ex z).left ⁻¹ᵁ A.left.basicOpen sV :=
      top_le_comap_basicOpen_of_valAt'_ne_zero _ hz sV (by rw [hs]; exact mul_ne_zero hz0 (pow_ne_zero _ hfr))
    have hc' := hc i i' z (hzD.trans fun q hq => hD hq)
    have key := congrArg (valAt' (u.ex z).left (A.left.basicOpen sV)) ha
    rw [valAt'_mul_of_whole_le_preimage _ hzD, valAt'_pow_of_whole_le_preimage _ hzD] at key
    simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict] at key
    rw [valAt'_presheaf_map_of_le_of_whole_le_preimage _ _ hzD, valAt'_presheaf_map_of_le_of_whole_le_preimage _ _ hzD, valAt'_presheaf_map_of_le_of_whole_le_preimage _ _ hzD, hs, hc'] at key
    beta_reduce
    rw [key]
    field_simp
    ring
end GlobalTheory.PrimitiveRegular
