-- Prove2me | solution 1 for GlobalTheory.PeriodConn.isPeriod_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:22:57.45465+00:00
-- url     : https://prove2.me/submissions/ccf4da4e-a54f-46da-8d99-b18eae24b4d8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsPreconnectedBlockUnits
import Theorems.Thm_GlobalTheory_PeriodConn_hermForm_conj_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Matrix
open GlobalTheory GlobalTheory.PeriodConn
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
open NumberField Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
namespace GlobalTheory.PeriodConn
namespace _root_.GlobalTheory.PeriodConn
theorem _root_.solution {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P) {A : Matrix (Fin g) (Fin g) ℂ} (hA : A.det ≠ 0)
    (hty : ∀ i j, ty i ≠ ty j → A i j = 0) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty ((A.mulVecLin).toAddMonoidHom.comp P) := by
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hHm, hpos, him⟩ := hP
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hcancel : ∀ v, A⁻¹ *ᵥ (A *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hu, Matrix.one_mulVec]
  have hcancel' : ∀ v, A *ᵥ (A⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hu, Matrix.one_mulVec]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a x i
    simp only [AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe, Function.comp_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hlin, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : ty i = ty j
    · rw [h]; ring
    · rw [hty i j h]; simp
  · intro x y hxy
    apply hinj
    have := congrArg (fun v => A⁻¹ *ᵥ v) hxy
    simpa [hcancel] using this
  · let f : (A.mulVecLin.toAddMonoidHom.comp P).range → P.range := fun v =>
      ⟨A⁻¹ *ᵥ (v : Fin g → ℂ), by
        obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp v.2
        refine AddMonoidHom.mem_range.mpr ⟨x, ?_⟩
        rw [← hx]
        exact (hcancel (P x)).symm⟩
    refine DiscreteTopology.of_continuous_injective (f := f) ?_ ?_
    · exact (continuous_const.matrix_mulVec continuous_subtype_val).subtype_mk _
    · intro v w hvw
      apply Subtype.ext
      have := congrArg (fun u : P.range => A *ᵥ (u : Fin g → ℂ)) hvw
      simpa [f, hcancel'] using this
  · have hr : Set.range ⇑(A.mulVecLin.toAddMonoidHom.comp P) =
        ((A.mulVecLin).restrictScalars ℝ) '' Set.range ⇑P := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact fun v => ⟨A⁻¹ *ᵥ v, hcancel' v⟩
  · have hct : ∀ N : Matrix (Fin g) (Fin g) ℂ, (N.map star)ᴴ = Nᵀ := fun N => by
      ext i j; simp
    have hct' : ∀ N : Matrix (Fin g) (Fin g) ℂ, (Nᵀ)ᴴ = N.map star := fun N => by
      ext i j; simp
    refine ⟨(A⁻¹)ᵀ * Hm * (A⁻¹).map star, ?_, ?_, ?_⟩
    · unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hHm.eq, hct, hct',
        Matrix.mul_assoc]
    · intro z hz
      rw [_root_.GlobalTheory.PeriodConn.hermForm_conj_mul]
      refine hpos _ fun h => hz ?_
      simpa [hcancel'] using congrArg (fun v => A *ᵥ v) h
    · intro x y
      change (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm _ (A *ᵥ P x) (A *ᵥ P y)).im = _
      rw [_root_.GlobalTheory.PeriodConn.hermForm_conj_mul, hcancel, hcancel]
      exact him x y
end _root_.GlobalTheory.PeriodConn
end GlobalTheory.PeriodConn
