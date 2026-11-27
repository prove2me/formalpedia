-- Prove2me | solution 1 for GlobalTheory.ThetaValueCont.exists_coordinates_of_relations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:35:00.744288+00:00
-- url     : https://prove2.me/submissions/4813ce0e-f39c-444b-94c5-a365a29ee566

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfFiniteOfClosedFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsCoordinatesOfRelations
import Theorems.Thm_GlobalTheory_SiegelNormalForm_form_conj
import Theorems.Thm_GlobalTheory_SiegelNormalForm_form_pull
import Theorems.Thm_GlobalTheory_SiegelNormalForm_form_single
import Theorems.Thm_GlobalTheory_SiegelNormalForm_isUnit_of_lagrangian
import Theorems.Thm_GlobalTheory_SiegelNormalForm_siegel_of_relations
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Filter Set
open scoped Topology
open GlobalTheory GlobalTheory.ThetaValueCont
open GlobalTheory.ThetaFamily
open Filter Set
open scoped Topology
open Complex Matrix
namespace GlobalTheory.ThetaValueCont
namespace _root_.GlobalTheory.ThetaValueCont
theorem _root_.solution {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) (e f : Fin g → Fin g → ℂ)
    (hee : ∀ i j, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (e i) (e j)).im = 0) (hff : ∀ i j, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (f i) (f j)).im = 0)
    (hef : ∀ i j, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (e i) (f j)).im = if i = j then -1 else 0) :
    ∃ (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ),
      τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ k, φ (Pi.single k 1) = e k ∧ φ (τ *ᵥ Pi.single k 1) = f k) ∧
      ∀ z w, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (φ z) (φ w) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm ((τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)) z w := by
  classical
  set P : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun a k ↦ e k a with hPdef
  set F : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun a k ↦ f k a with hFdef
  have hPe : ∀ k, P *ᵥ Pi.single k 1 = e k := fun k ↦ by
    rw [Matrix.mulVec_single_one]; rfl
  have hFf : ∀ k, F *ᵥ Pi.single k 1 = f k := fun k ↦ by
    rw [Matrix.mulVec_single_one]; rfl
  set YC : Matrix (Fin g) (Fin g) ℂ := P.transpose * Hm * P.map star with hYCdef
  have hYC : ∀ z w, z ⬝ᵥ YC.mulVec (star w) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (P *ᵥ z) (P *ᵥ w) := fun z w ↦ by
    rw [hYCdef, ← _root_.GlobalTheory.SiegelNormalForm.form_pull]; rfl
  have hYCe : ∀ i j, YC i j = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (e i) (e j) := fun i j ↦ by
    rw [← _root_.GlobalTheory.SiegelNormalForm.form_single YC i j, hYC, hPe, hPe]
  set Y : Matrix (Fin g) (Fin g) ℝ := YC.map Complex.re with hYdef
  have hYre : Y.map Complex.ofReal = YC := by
    ext i j
    refine Complex.ext (by simp [hYdef]) ?_
    simp only [hYdef, Matrix.map_apply, Complex.ofReal_im]
    rw [hYCe, hee]
  have hPu : IsUnit P := _root_.GlobalTheory.SiegelNormalForm.isUnit_of_lagrangian P Hm f hpos Y hYre.symm
    (fun i j ↦ by rw [hPe]; exact hef i j)
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have hPinj : ∀ z, P *ᵥ z = 0 → z = 0 := fun z hz ↦ by
    rw [← Matrix.one_mulVec z, ← Matrix.nonsing_inv_mul P hdet, ← Matrix.mulVec_mulVec, hz,
      Matrix.mulVec_zero]
  have hYpos : Y.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · ext i j
      simp only [Matrix.conjTranspose_apply, star_trivial, hYdef, Matrix.map_apply, hYCe]
      rw [show _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (e j) (e i) = star (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (e i) (e j)) from
        (_root_.GlobalTheory.SiegelNormalForm.form_conj hH _ _).symm]
      simp
    · intro x hx
      set z : Fin g → ℂ := fun i ↦ (x i : ℂ) with hzdef
      have hz : z ≠ 0 := fun h ↦ hx (funext fun i ↦ by
        simpa [hzdef] using congrFun h i)
      have key : ((star x ⬝ᵥ Y *ᵥ x : ℝ) : ℂ) = z ⬝ᵥ YC.mulVec (star z) := by
        rw [← hYre]
        simp [hzdef, dotProduct, Matrix.mulVec, Complex.ofReal_sum, Complex.ofReal_mul]
      have h2 := hpos (P *ᵥ z) (fun h ↦ hz (hPinj z h))
      rw [← Complex.ofReal_re (star x ⬝ᵥ Y *ᵥ x), key, hYC]
      exact h2
  set τ : Matrix (Fin g) (Fin g) ℂ := P⁻¹ * F with hτdef
  have hPτ : ∀ k, P *ᵥ (τ *ᵥ Pi.single k 1) = f k := fun k ↦ by
    rw [Matrix.mulVec_mulVec, hτdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv P hdet,
      Matrix.one_mul, hFf]
  obtain ⟨hsymm, hpd, hYI⟩ := _root_.GlobalTheory.SiegelNormalForm.siegel_of_relations Y hYpos τ
    (fun i j ↦ by rw [hYre, hYC, hPe, hPτ]; exact hef i j)
    (fun i j ↦ by rw [hYre, hYC, hPτ, hPτ]; exact hff i j)
  letI : Invertible P := P.invertibleOfIsUnitDet hdet
  refine ⟨Matrix.toLinearEquiv' P this, τ, hsymm, hpd, fun k ↦ ⟨?_, ?_⟩, fun z w ↦ ?_⟩
  · change P *ᵥ Pi.single k 1 = e k
    exact hPe k
  · change P *ᵥ (τ *ᵥ Pi.single k 1) = f k
    exact hPτ k
  · change _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (P *ᵥ z) (P *ᵥ w) = _
    rw [Matrix.inv_eq_left_inv hYI, hYre, ← hYC]
    rfl
end _root_.GlobalTheory.ThetaValueCont
end GlobalTheory.ThetaValueCont
