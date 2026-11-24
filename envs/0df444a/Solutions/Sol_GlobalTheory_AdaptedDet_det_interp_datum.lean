-- Prove2me | solution 1 for GlobalTheory.AdaptedDet.det_interp_datum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:04:30.573836+00:00
-- url     : https://prove2.me/submissions/fd2408aa-429d-41fb-a2c3-66b696de56ce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmUnitPowFourIdempotentModEight
import Theorems.Thm_GlobalTheory_AdaptedDet_det_interp
import Theorems.Thm_GlobalTheory_AdaptedDet_norm_one_add
import Theorems.Thm_GlobalTheory_AdaptedDet_cmUnit_pow_four_idempotent_mod_eight
import Theorems.Thm_GlobalTheory_AdaptedDet_exists_gl
import Theorems.Thm_GlobalTheory_AdaptedDet_det_eq_norm
import Theorems.Thm_GlobalTheory_CongruenceDet_det_eq_one
import Theorems.Thm_GlobalTheory_DatumCoord_eq_of_trace_int
import Theorems.Thm_GlobalTheory_HermModel_herm_add_right
import Theorems.Thm_GlobalTheory_HermModel_herm_smul_left
import Theorems.Thm_GlobalTheory_HermModel_herm_smul_right
import Theorems.Thm_GlobalTheory_HermModel_herm_zero_right
import Theorems.Thm_GlobalTheory_HermModel_rank_integral_selfDual
import Theorems.Thm_GlobalTheory_exists_herm_coord_of_datum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AdaptedDet
namespace GlobalTheory.AdaptedDet
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (D : Datum H) {M : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ D.La)
    (gam : D.La ≃ₗ[𝓞 E] D.La) (hM : 3 ≤ M) (hiso : ∀ a b, D.EF (gam a) (gam b) = D.EF a b)
    (hlev : ∀ a, ∃ e, gam a = a + M • e) (T : D.La →ₗ[ℤ] D.La)
    (hT : ∀ x, T x = H.w0 ^ 4 • gam x + (x - H.w0 ^ 4 • x)) :
    (((LinearMap.toMatrix b b T).det : ℤ) : ZMod 8) = 1 := by
  have hrt : FD.cc (H.rt : E) = -(H.rt : E) ∧ (H.rt : E) ≠ 0 := by
    have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
      simpa using this
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have hne : FD.cc (H.rt : E) ≠ (H.rt : E) := by
      intro h
      obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have h2 := IsCMField.complexEmbedding_complexConj E σ (H.rt : E)
      rw [show IsCMField.complexConj E (H.rt : E) = H.rt from h] at h2
      have h3 : (σ H.rt).im = 0 := Complex.conj_eq_iff_im.mp h2.symm
      have h4 := congrArg (fun x => (σ x).re) h1
      simp only [map_pow, map_neg, map_natCast, sq, map_mul, Complex.mul_re, h3, Complex.neg_re,
        Complex.natCast_re] at h4
      nlinarith [mul_self_nonneg (σ H.rt).re]
    constructor
    · have h2 : FD.cc (H.rt : E) ^ 2 = (H.rt : E) ^ 2 := by
        rw [FD.cc, ← map_pow, h1, map_neg, map_natCast]
      exact (sq_eq_sq_iff_eq_or_eq_neg.mp h2).resolve_left hne
    · intro h
      apply hne
      rw [h, FD.cc, map_zero]
  obtain ⟨Gm, φ, hinj, hspan, hherm, hdet, hEF⟩ :=
    exists_herm_coord_of_datum E H D H.rt hrt.1 hrt.2 _ rfl
  have hfg := (HermModel.rank_integral_selfDual E H D _ _ Gm φ hrt.1
    ⟨hinj, hspan, hherm, hdet, hEF⟩).2.1
  obtain ⟨γ, hγ⟩ := exists_gl φ hinj hspan gam
  have hsm : ∀ (a : 𝓞 E) (x : D.La), φ (a • x) = (a : E) • φ x := fun a x => by
    rw [map_smul]; rfl
  have hh : ∀ x y, FD.herm Gm (φ (gam x)) (φ (gam y)) = FD.herm Gm (φ x) (φ y) := by
    intro x y
    apply mul_left_cancel₀ hrt.2
    apply DatumCoord.eq_of_trace_int
    intro a
    have := hiso (a • x) y
    have h2 := hEF (a • x) y
    rw [← this, hEF, map_smul, hsm, hsm, HermModel.herm_smul_left, HermModel.herm_smul_left] at h2
    rw [mul_left_comm, h2, mul_left_comm]
  have hadd : ∀ x x' y, FD.herm Gm (x + x') y = FD.herm Gm x y + FD.herm Gm x' y := by
    intro x x' y
    simp [FD.herm, add_mul, Finset.sum_add_distrib]
  have hU : FD.IsUStab Gm (LinearMap.range φ) γ := by
    constructor
    · intro x y
      have hx : x ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
      have hy : y ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨x, rfl⟩ := hx
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨y, rfl⟩ := hy
          rw [hγ, hγ, hh]
        | zero => simp [HermModel.herm_zero_right]
        | add y z _ _ hy hz =>
          rw [Matrix.mulVec_add, HermModel.herm_add_right, HermModel.herm_add_right, hy, hz]
        | smul c y _ hy =>
          rw [Matrix.mulVec_smul, HermModel.herm_smul_right, HermModel.herm_smul_right, hy]
      | zero => simp [FD.herm]
      | add x z _ _ hx hz => rw [Matrix.mulVec_add, hadd, hadd, hx, hz]
      | smul c x _ hx =>
        rw [Matrix.mulVec_smul, HermModel.herm_smul_left, HermModel.herm_smul_left, hx]
    · intro x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨gam y, (hγ y).symm⟩
      · rintro ⟨y, hy⟩
        refine ⟨gam.symm y, ?_⟩
        apply Matrix.mulVec_injective_of_isUnit γ.isUnit
        change _ *ᵥ _ = _ *ᵥ _
        rw [hγ, LinearEquiv.apply_symm_apply, hy]
  have hdet1 := CongruenceDet.det_eq_one E _ M Gm (LinearMap.range φ) γ hdet hfg hspan hM hU (by
    rintro _ ⟨x, rfl⟩
    obtain ⟨e, he⟩ := hlev x
    exact ⟨φ e, ⟨e, rfl⟩, by rw [hγ, he, map_add, map_nsmul]⟩)
  obtain ⟨he0, t, ht⟩ := cmUnit_pow_four_idempotent_mod_eight H
  obtain ⟨y, hy⟩ := det_interp 8 (by norm_num) _ t he0 ht (LinearMap.range φ) γ hfg hspan
    (fun v hv => (hU.2 v).1 hv) hdet1
  have h := det_eq_norm b φ hinj hspan T
    (((H.w0 ^ 4 : 𝓞 E) : E) • (γ : Matrix _ _ E) + (1 - ((H.w0 ^ 4 : 𝓞 E) : E)) • 1) (by
      intro x
      rw [hT, map_add, map_sub, hsm, hsm, Matrix.add_mulVec, Matrix.smul_mulVec,
        Matrix.smul_mulVec, hγ, Matrix.one_mulVec, sub_smul, one_smul])
  rw [hy, ← Algebra.coe_norm_int] at h
  rw [Int.cast_injective h]
  exact norm_one_add 8 y
end GlobalTheory.AdaptedDet
