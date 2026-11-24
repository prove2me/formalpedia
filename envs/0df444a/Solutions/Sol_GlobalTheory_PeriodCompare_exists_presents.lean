-- Prove2me | solution 1 for GlobalTheory.PeriodCompare.exists_presents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:57:47.314223+00:00
-- url     : https://prove2.me/submissions/aaa09b50-49ec-490f-84e0-d6303a584f1e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong
import Theorems.Thm_GlobalTheory_PeriodCompare_finiteDimensional
import Theorems.Thm_GlobalTheory_PeriodCompare_mem_domain
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PeriodMapPresentation_IsPeriodMap_map_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PeriodCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open scoped TensorProduct Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.PeriodCompare
theorem _root_.solution {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (h : IsPeriod D ty P) : ∃ J ∈ domain D, Presents D ty P J := by
  obtain ⟨_, _⟩ := finiteDimensional D
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, -, hpos, hE⟩ := h
  let ψ : ℝ ⊗[ℤ] D.La →ₗ[ℝ] (Fin g → ℂ) := P.toIntLinearMap.liftBaseChange ℝ
  have hψ : ∀ (r : ℝ) x, ψ (r ⊗ₜ x) = r • P x := fun r x => by simp [ψ]
  have hsurj : Function.Surjective ψ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp [hψ]⟩
  have hrk : Module.finrank ℝ (ℝ ⊗[ℤ] D.La) = Module.finrank ℝ (Fin g → ℂ) := by
    haveI : DiscreteTopology (LinearMap.range P.toIntLinearMap) := hdisc
    haveI : IsZLattice ℝ (LinearMap.range P.toIntLinearMap) := ⟨hspan⟩
    rw [Module.finrank_baseChange, (LinearEquiv.ofInjective P.toIntLinearMap hinj).finrank_eq, ZLattice.rank ℝ]
  let φ := LinearEquiv.ofBijective ψ ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).2 hsurj, hsurj⟩
  have hφ : ∀ (r : ℝ) x, φ (r ⊗ₜ x) = r • P x := hψ
  let J : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
    φ.symm.conj ((Complex.I • (LinearMap.id : Module.End ℂ (Fin g → ℂ))).restrictScalars ℝ)
  have hJ : ∀ v, φ (J v) = Complex.I • φ v := fun v => by simp [J, LinearEquiv.conj_apply_apply]
  have hact : ∀ (a : 𝓞 E) v, φ (actR D a v) = tyAct ty a (φ v) := fun a v => by
    induction v using TensorProduct.induction_on with
    | zero => funext i; simp [tyAct]
    | add u v hu hv => funext i; simp [tyAct, hu, hv, mul_add]
    | tmul r x =>
      funext i
      have : actR D a (r ⊗ₜ x) = r ⊗ₜ (a • x) := rfl
      simp [this, hφ, tyAct, hlin, mul_left_comm]
  have hB : ∀ x y, D.EF.baseChange ℝ x y = imForm Hm (φ x) (φ y) := fun x y => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | tmul r x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' h h' => simp only [map_add, h, h']
      | tmul r' y =>
        have : imForm Hm (P x) (P y) = D.EF x y := hE x y
        simp only [hφ, map_smul, LinearMap.smul_apply, this, LinearMap.BilinForm.baseChange_tmul, smul_eq_mul,
          zsmul_eq_mul]
        ring
  refine ⟨J, mem_domain D (fun x => φ.injective ?_) (fun a => LinearMap.ext fun v => φ.injective ?_)
    (fun x y => ?_) (fun x hx => ?_), φ, fun x => by simp [hφ], hJ, hact⟩
  · rw [hJ, hJ, smul_smul, Complex.I_mul_I, map_neg, neg_smul, one_smul]
  · simp only [LinearMap.comp_apply, hJ, hact]
    funext i; simp [tyAct, mul_left_comm]
  · rw [hB, hB, hJ, hJ]
    change (hermForm _ _ _).im = (hermForm _ _ _).im
    simp [hermForm, star_smul, Matrix.mulVec_smul, Matrix.mulVec_neg, ← mul_assoc]
  · rw [hB, hJ]
    have := hpos (φ x) (by simpa using hx)
    change 0 < (hermForm _ _ _).im
    simpa [hermForm, smul_dotProduct] using this
end GlobalTheory.PeriodCompare
