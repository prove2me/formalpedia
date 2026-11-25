-- Prove2me | solution 1 for GlobalTheory.primitive_regular_on_nonzeroLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:40:08.194888+00:00
-- url     : https://prove2.me/submissions/246ec612-8be3-4f60-bedb-5414c94a4360

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
import Theorems.Thm_GlobalTheory_PrimitiveRegular_top_le_preimage_iSup
import Theorems.Thm_GlobalTheory_PrimitiveRegular_mem_basicOpen
import Theorems.Thm_GlobalTheory_PrimitiveRegular_local_extension
import Theorems.Thm_GlobalTheory_PrimitiveRegular_entire_extension
import Theorems.Thm_GlobalTheory_SectionTheta_ex_add_lattice
import Theorems.Thm_GlobalTheory_ThetaBundleSec_exists_fn
import Theorems.Thm_GlobalTheory_existsUnique_section_of_locally_regular
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
private theorem valAt'_eq_ΓSpecIso_appLE_of_whole_le_preimage {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {W : Y.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W) (f : Γ(Y, W)) :
    valAt' y W f = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((y.appLE W ⊤ hW).hom f) := by
  unfold valAt' valAt
  rw [dif_pos hW]
private theorem valAt'_presheaf_map_of_le_of_whole_le_preimage' {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {V W : Y.Opens} (hVW : V ≤ W)
    (hV : ⊤ ≤ y ⁻¹ᵁ V) (f : Γ(Y, W)) :
    valAt' y V ((Y.presheaf.map (homOfLE hVW).op).hom f) = valAt' y W f := by
  rw [valAt'_eq_ΓSpecIso_appLE_of_whole_le_preimage y hV, valAt'_eq_ΓSpecIso_appLE_of_whole_le_preimage y (hV.trans fun q hq => hVW hq)]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
private theorem valAt'_mul_of_top_le_preimage_open {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {W : Y.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f f' : Γ(Y, W)) : valAt' y W (f * f') = valAt' y W f * valAt' y W f' := by
  simp only [valAt'_eq_ΓSpecIso_appLE_of_whole_le_preimage y hW, map_mul]
private theorem valAt'_pow_of_whole_le_preimage' {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {W : Y.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f : Γ(Y, W)) (m : ℕ) : valAt' y W (f ^ m) = valAt' y W f ^ m := by
  simp only [valAt'_eq_ΓSpecIso_appLE_of_whole_le_preimage y hW, map_pow]
private theorem point_mem_basicOpen_of_valAt'_ne_zero {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {W : Y.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W)
    (f : Γ(Y, W)) (hf : valAt' y W f ≠ 0) : ⊤ ≤ y ⁻¹ᵁ Y.basicOpen f := by
  rw [valAt'_eq_ΓSpecIso_appLE_of_whole_le_preimage y hW] at hf
  have hu : IsUnit ((y.appLE W ⊤ hW).hom f) := by
    have h2 := (IsUnit.mk0 _ hf).map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    simpa using h2
  have h3 : (Sp ℂ).basicOpen ((y.appLE W ⊤ hW).hom f) = ⊤ := Scheme.basicOpen_of_isUnit _ hu
  have h4 : (Sp ℂ).basicOpen ((y.appLE W ⊤ hW).hom f) ≤ y ⁻¹ᵁ Y.basicOpen f := by
    rw [Scheme.preimage_basicOpen]
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res]
    exact inf_le_right
  exact h3.symm.le.trans h4
private theorem valAt'_one_of_whole_le_preimage {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) {W : Y.Opens} (hW : ⊤ ≤ y ⁻¹ᵁ W) :
    valAt' y W 1 = 1 := by
  simp only [valAt'_eq_ΓSpecIso_appLE_of_whole_le_preimage y hW, map_one]
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
open GlobalTheory
open PrimitiveRegular
namespace GlobalTheory
theorem _root_.solution : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (I : Type) (O : I → P₀.A.left.Opens) (c : ∀ i i', Γ(P₀.A.left, O i ⊓ O i')) (h : I → (Fin P₀.g → ℂ) → ℂ), ⨆ i, O i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i} ∧ ∀ (l : u.Λ) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i → h i (z + l) = h i z) → (∀ i i' z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (O i ⊓ O i') → valAt' (u.ex z).left (O i ⊓ O i') (c i i') = h i' z - h i z) → ∀ i (n : ℕ) (σ : (lbPow P₀.L n).Sec), Out.nonzeroLocus σ ≤ O i → ∃ a : Γ(P₀.A.left, Out.nonzeroLocus σ), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Out.nonzeroLocus σ → valAt' (u.ex z).left (Out.nonzeroLocus σ) a = h i z := by
  intro P₀ u Hm χ hG I O c h hO hh hc i n σ hσ
  have hL : P₀.L.IsLB := P₀.7
  have : CompactSpace P₀.A.left := by
    have : IsProper P₀.A.hom := by
      exact P₀.3.3
    have hc0 := QuasiCompact.isCompact_preimage (f := P₀.A.hom) Set.univ isOpen_univ isCompact_univ
    exact ⟨by simpa using hc0⟩
  obtain ⟨θ, hθd, hθ, -, hθper⟩ := GlobalTheory.ThetaBundleSec.exists_fn u hL n σ
  have hOi : ∀ z, θ z ≠ 0 → ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i := by
    intro z hz
    obtain ⟨j, hj⟩ := (PrimitiveRegular.top_le_preimage_iSup (u.ex z).left P₀.L.U).mp
      (by rw [hL.1]; exact fun q _ => trivial)
    let k : (lbPow P₀.L n).ι := fun _ => j
    have hk : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P₀.L n).U k :=
      fun q hq => Set.mem_iInter.mpr fun _ => by simpa using hj hq
    have hb := point_mem_basicOpen_of_valAt'_ne_zero _ hk (σ.f k) (PrimitiveRegular.mem_basicOpen u hθ k z hk hz)
    refine hb.trans fun q hq => hσ ?_
    unfold ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus
    exact (le_iSup (fun k => P₀.A.left.basicOpen (σ.f k)) k) hq
  obtain ⟨M, hM, hdiff⟩ := PrimitiveRegular.entire_extension u (h i) θ hθd
    (PrimitiveRegular.local_extension u hL O c h hO (fun i => (hh i).1) hc i σ hσ hθd hθ)
  have hTh : u.IsThetaFn Hm χ (n * M) (fun z => θ z ^ M * h i z) := by
    refine ⟨hdiff, fun l z => ?_⟩
    beta_reduce
    have hw := hθper z (z + l)
      (χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l))
      (GlobalTheory.SectionTheta.ex_add_lattice u z l) (fun j hj => hG.ah.2.2.2 l j z hj)
    by_cases h0 : θ z = 0
    · have h0' : θ (z + l) = 0 := by rw [hw, h0, mul_zero]
      simp only [h0, h0', zero_pow hM.ne', zero_mul, mul_zero]
    · rw [hw, (hh i).2 l z (hOi z h0), pow_mul, mul_pow]
      ring
  obtain ⟨s, hs⟩ := hG.sec (n * M) _ hTh
  refine (existsUnique_section_of_locally_regular P₀ u Hm χ hG (Out.nonzeroLocus σ) (h i) ?_).exists
  intro z hz
  have hz' := hz
  unfold ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus at hz'
  obtain ⟨k, hk⟩ := (PrimitiveRegular.top_le_preimage_iSup (u.ex z).left _).mp hz'
  have hle : P₀.A.left.basicOpen (σ.f k) ≤ Out.nonzeroLocus σ := by
    unfold ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus
    exact le_iSup (fun k => P₀.A.left.basicOpen (σ.f k)) k
  have hUk := P₀.A.left.basicOpen_le (σ.f k)
  have hu : IsUnit ((P₀.A.left.presheaf.map (homOfLE hUk).op).hom (σ.f k)) := by
    exact RingedSpace.isUnit_res_basicOpen _ (σ.f k)
  refine ⟨P₀.A.left.basicOpen (σ.f k),
    (P₀.A.left.presheaf.map (homOfLE hUk).op).hom (s.f k) * ((hu.unit⁻¹ : _ˣ) : Γ(P₀.A.left, P₀.A.left.basicOpen (σ.f k))) ^ M,
    hle, hk, fun z' hz'' => ?_⟩
  have hzk : ⊤ ≤ (u.ex z').left ⁻¹ᵁ (lbPow P₀.L n).U k := hz''.trans fun q hq => hUk hq
  have hr : valAt' (u.ex z').left _ (hu.unit : Γ(P₀.A.left, P₀.A.left.basicOpen (σ.f k))) = θ z' * u.fr (k PUnit.unit) z' ^ n := by
    rw [IsUnit.unit_spec, valAt'_presheaf_map_of_le_of_whole_le_preimage' _ _ hz'']
    exact hθ k z' hzk
  have hinv : valAt' (u.ex z').left _ (hu.unit : Γ(P₀.A.left, P₀.A.left.basicOpen (σ.f k))) *
      valAt' (u.ex z').left _ ((hu.unit⁻¹ : _ˣ) : Γ(P₀.A.left, P₀.A.left.basicOpen (σ.f k))) = 1 := by
    rw [← valAt'_mul_of_top_le_preimage_open _ hz'', Units.mul_inv, valAt'_one_of_whole_le_preimage _ hz'']
  have hne : θ z' * u.fr (k PUnit.unit) z' ^ n ≠ 0 := by
    rw [← hr]; exact left_ne_zero_of_mul_eq_one hinv
  have hθ0 : θ z' ≠ 0 := left_ne_zero_of_mul hne
  have hfr0 : u.fr (k PUnit.unit) z' ^ n ≠ 0 := right_ne_zero_of_mul hne
  rw [hr] at hinv
  rw [valAt'_mul_of_top_le_preimage_open _ hz'', valAt'_pow_of_whole_le_preimage' _ hz'']
  erw [valAt'_presheaf_map_of_le_of_whole_le_preimage' (W := (lbPow P₀.L (n * M)).U k) _ hUk hz'']
  rw [eq_inv_of_mul_eq_one_right hinv, hs k z' (show ⊤ ≤ (u.ex z').left ⁻¹ᵁ (lbPow P₀.L (n * M)).U k from hzk)]
  have hθM : θ z' ^ M ≠ 0 := pow_ne_zero _ hθ0
  have hfrM : u.fr (k PUnit.unit) z' ^ (n * M) ≠ 0 := by
    rw [pow_mul]
    exact pow_ne_zero _ hfr0
  beta_reduce
  rw [inv_pow, mul_pow, ← pow_mul]
  calc _ = (θ z' ^ M * u.fr (k PUnit.unit) z' ^ (n * M)) *
        (θ z' ^ M * u.fr (k PUnit.unit) z' ^ (n * M))⁻¹ * h i z' := by ring
    _ = h i z' := by rw [mul_inv_cancel₀ (mul_ne_zero hθM hfrM), _root_.one_mul]
end GlobalTheory
