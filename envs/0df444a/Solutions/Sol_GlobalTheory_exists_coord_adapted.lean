-- Prove2me | solution 1 for GlobalTheory.exists_coord_adapted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:09:24.51035+00:00
-- url     : https://prove2.me/submissions/3eef994f-9e46-4cef-b280-4afb4519993d

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FderivEqZeroOfAffine
import Theorems.Thm_GlobalTheory_AdaptedCoord_ex_comp
import Theorems.Thm_GlobalTheory_AdaptedCoord_eventually_le
import Theorems.Thm_GlobalTheory_AdaptedCoord_dirDeriv_apply
import Theorems.Thm_GlobalTheory_AdaptedCoord_dirDeriv_constFn
import Theorems.Thm_GlobalTheory_AdaptedCoord_dirDeriv_mul
import Theorems.Thm_GlobalTheory_AdaptedCoord_fderiv_eq_zero_of_affine
import Theorems.Thm_GlobalTheory_AdaptedCoord_apply_eq_sum
import Theorems.Thm_P2M_GlobalTheory_valAt__add_b0728a15060b
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
namespace GlobalTheory
namespace AdaptedCoord
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
private theorem valAt'_constFn_of_comp_eq_id {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (p : X ⟶ Sp ℂ) (hp : x ≫ p = 𝟙 _)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : ℂ) : valAt' x U (constFn p U a) = a := by
  have key : ∀ (q : Sp ℂ ⟶ Sp ℂ) (e : ⊤ ≤ q ⁻¹ᵁ ⊤), q = 𝟙 _ →
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ q.appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom =
        𝟙 _ := by
    rintro q e rfl
    simp [Scheme.Hom.appLE]
    erw [CategoryTheory.Functor.map_id]
    simp
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ p.appLE ⊤ U (show U ≤ p ⁻¹ᵁ ⊤ from fun _ _ => trivial) ≫
      x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = 𝟙 _ := by
    rw [Scheme.Hom.appLE_comp_appLE_assoc]
    exact key _ _ hp
  rw [valAt', dif_pos h]
  exact congrArg (fun φ => φ.hom a) hcomp
private theorem valAt'_zero_toric_geometry {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) :
    valAt' x U 0 = 0 := by
  unfold valAt'
  split_ifs <;> simp [valAt]
private theorem valAt'_finset_sum' {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) {J : Type} (s : Finset J)
    (F : J → Γ(X, U)) : valAt' x U (∑ j ∈ s, F j) = ∑ j ∈ s, valAt' x U (F j) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, valAt'_zero_toric_geometry]
  · intro j s hj ih
    rw [Finset.sum_insert hj, Finset.sum_insert hj, valAt'_add, ih]
end AdaptedCoord
end GlobalTheory
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open AdaptedCoord
namespace GlobalTheory
theorem _root_.solution : (∀ (X : Over (Sp ℂ)) (g : ℕ), SmoothOfRelativeDimension g X.hom → ∀ e : (𝟙_ (Over (Sp ℂ)) ⟶ X), ∃ (W : Set (Fin g → ℂ)) (σ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (U : X.left.Opens) (t : Fin g → Γ(X.left, U)), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ IsAffineOpen U ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (σ w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (σ w).left U f) {w | w ∈ W ∧ ⊤ ≤ (σ w).left ⁻¹ᵁ U}) ∧ (∀ w ∈ W, ⊤ ≤ (σ w).left ⁻¹ᵁ U ∧ ∀ i, valAt' (σ w).left U (t i) = w i) ∧ IsOpen[(TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ X) | ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}})] (σ '' W) ∧ (∀ D : Γ(X.left, U) →+ ℂ, (∀ a, D (constFn X.hom U a) = 0) → (∀ f f', D (f * f') = valAt' e.left U f * D f' + valAt' e.left U f' * D f) → (∀ i, D (t i) = 0) → D = 0)) → (∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), SmoothOfRelativeDimension g A.hom → (∀ w : Fin g → ℂ, (∀ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U → fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0) → w = 0) → ∃ (U : A.left.Opens) (t : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) := by
  intro H A _ L g u hsm hinj
  obtain ⟨W, σ, U, t, -, hW0, hσ0, hU, -, hσW, -, hD⟩ := H A g hsm (u.ex 0)
  have h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := hσ0 ▸ (hσW 0 hW0).1
  have hφd : DifferentiableAt ℂ (fun z i => valAt' (u.ex z).left U (t i)) 0 :=
    differentiableAt_pi.2 fun i => differentiableAt_val u h (t i)

  obtain ⟨M, hMdef⟩ : ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      ∀ v, M v = fderiv ℂ (fun z i => valAt' (u.ex z).left U (t i)) 0 v :=
    ⟨(fderiv ℂ (fun z i => valAt' (u.ex z).left U (t i)) 0 : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)),
      fun _ => rfl⟩
  have hM : ∀ v i, M v i = dirDeriv u h v (t i) := by
    intro v i
    rw [hMdef, dirDeriv_apply, (hasFDerivAt_pi'.1 hφd.hasFDerivAt i).fderiv]
    rfl

  have hMinj : Function.Injective M := by
    intro v v' hvv
    have hv0 : v - v' = 0 := by
      apply hinj
      intro V f hV
      refine fderiv_eq_zero_of_affine u hU h (v - v') ?_ V f hV
      refine hD _ (fun a => dirDeriv_constFn u h _ a) (fun f f' => dirDeriv_mul u h _ f f') fun i => ?_
      rw [← hM, map_sub, hvv, sub_self]
      rfl
    exact sub_eq_zero.1 hv0
  obtain ⟨Sinv, hSM, hSinj⟩ : ∃ S : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ v, S (M v) = v) ∧ Function.Injective S := by
    let N := LinearEquiv.ofInjectiveEndo M hMinj
    refine ⟨N.symm.toLinearMap, fun v => ?_, N.symm.injective⟩
    have hN : N v = M v := by simp [N, LinearEquiv.coe_ofInjectiveEndo]
    rw [LinearEquiv.coe_coe, ← hN, LinearEquiv.symm_apply_apply]

  obtain ⟨t', ht'⟩ : ∃ t' : Fin g → Γ(A.left, U),
      ∀ i, t' i = ∑ j, constFn A.hom U (Sinv (Pi.single j 1) i) * t j :=
    ⟨fun i => ∑ j, constFn A.hom U (Sinv (Pi.single j 1) i) * t j, fun _ => rfl⟩
  have hc0 : ∀ c : ℂ, valAt' (u.ex 0).left U (constFn A.hom U c) = c :=
    fun c => valAt'_constFn_of_comp_eq_id _ _ (ex_comp u 0) U h c
  refine ⟨U, t', hU, h, ?_, ?_⟩
  · intro D hc hl hD'
    apply hD D hc hl
    have hS : Sinv (fun j => D (t j)) = 0 := by
      funext i
      have e : D (t' i) = ∑ j, Sinv (Pi.single j 1) i * D (t j) := by
        rw [ht', map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hl, hc, hc0, mul_zero, add_zero]
      rw [apply_eq_sum]
      simp only [Pi.zero_apply]
      rw [← e, hD' i]
    have h0 : (fun j => D (t j)) = 0 := hSinj (hS.trans (map_zero Sinv).symm)
    exact fun j => congrFun h0 j
  · have hev : (fun w i => valAt' (u.ex w).left U (t' i)) =ᶠ[𝓝 0]
        fun w => Sinv (fun i => valAt' (u.ex w).left U (t i)) := by
      filter_upwards [eventually_le u h] with z hz
      funext i
      rw [ht', valAt'_finset_sum', apply_eq_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [valAt'_mul, valAt'_constFn_of_comp_eq_id _ _ (ex_comp u z) U hz]
    have hcomp : HasFDerivAt (fun w => Sinv (fun i => valAt' (u.ex w).left U (t i)))
        ((LinearMap.toContinuousLinearMap Sinv).comp
          (fderiv ℂ (fun z i => valAt' (u.ex z).left U (t i)) 0)) 0 :=
      (LinearMap.toContinuousLinearMap Sinv).hasFDerivAt.comp 0 hφd.hasFDerivAt
    have hid : (LinearMap.toContinuousLinearMap Sinv).comp
        (fderiv ℂ (fun z i => valAt' (u.ex z).left U (t i)) 0) = ContinuousLinearMap.id ℂ (Fin g → ℂ) := by
      refine ContinuousLinearMap.ext fun v => ?_
      rw [ContinuousLinearMap.comp_apply, ← hMdef, LinearMap.coe_toContinuousLinearMap', hSM]
      rfl
    rw [hid] at hcomp
    exact hcomp.congr_of_eventuallyEq hev
end GlobalTheory
