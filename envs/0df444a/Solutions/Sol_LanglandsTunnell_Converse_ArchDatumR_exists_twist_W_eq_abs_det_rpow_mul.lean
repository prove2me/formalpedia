-- Prove2me | solution 1 for LanglandsTunnell.Converse.ArchDatumR.exists_twist_W_eq_abs_det_rpow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/37300472-3ca6-5605-83d8-d2c37dcf2867

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_twist_W_eq_abs_det_rpow_mul

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse AutomorphicForm

namespace Ws47
namespace TWD

open LanglandsTunnell.Converse.ArchR LanglandsTunnell.Converse.ArchCasimir MeasureTheory

variable {P : RealArchParam}

noncomputable def twistW (D : ArchDatumR P) (t : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := (((|g.det| ^ t : ℝ)) : ℂ) * D.W g

end Ws47.TWD

open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse AutomorphicForm

namespace Ws47
namespace TWD

theorem isOpen_glSet : IsOpen ArchR.glSet := by
  have hc : Continuous fun M : Fin 2 → Fin 2 → ℝ => M 0 0 * M 1 1 - M 0 1 * M 1 0 := by fun_prop
  have : ArchR.glSet = {M : Fin 2 → Fin 2 → ℝ | M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0} := by
    ext M
    simp only [ArchR.glSet, Set.mem_setOf_eq, Matrix.det_fin_two, Matrix.of_apply]
  rw [this]
  exact isOpen_ne_fun hc continuous_const

theorem uniqueDiffOn_glSet : UniqueDiffOn ℝ ArchR.glSet := isOpen_glSet.uniqueDiffOn

theorem det_ne_zero_of_isK {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) : k.det ≠ 0 := by
  have h := (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).1 hk
  have h' := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h'
  exact left_ne_zero_of_mul_eq_one h'

theorem abs_det_of_isK {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) : |k.det| = 1 := by
  have h := (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).1 hk
  have h' := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h'
  have : |k.det| ^ 2 = 1 := by rw [sq_abs, sq, h']
  nlinarith [abs_nonneg k.det]

theorem abs_entry_le_one_of_isK {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : ArchR.IsK k) (i j : Fin 2) : |k i j| ≤ 1 := by
  have h := (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).1 hk
  have hrow : k i 0 * k i 0 + k i 1 * k i 1 = 1 := by
    have := congrFun (congrFun h i) i
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply] using this
  rw [abs_le_one_iff_mul_self_le_one]
  fin_cases j
  · show k i 0 * k i 0 ≤ 1
    nlinarith [sq_nonneg (k i 1)]
  · show k i 1 * k i 1 ≤ 1
    nlinarith [sq_nonneg (k i 0)]

theorem isCompact_Kcoords : IsCompact {q : Fin 2 → Fin 2 → ℝ | ArchR.IsK (Matrix.of q)} := by
  have hclosed : IsClosed {q : Fin 2 → Fin 2 → ℝ | ArchR.IsK (Matrix.of q)} := by
    have hc : Continuous fun q : Fin 2 → Fin 2 → ℝ => Matrix.of q * Matrix.transpose (Matrix.of q) := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Fin.sum_univ_two]
      fun_prop
    have : {q : Fin 2 → Fin 2 → ℝ | ArchR.IsK (Matrix.of q)} =
        (fun q : Fin 2 → Fin 2 → ℝ => Matrix.of q * Matrix.transpose (Matrix.of q)) ⁻¹' {1} := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      exact Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ
    rw [this]
    exact isClosed_singleton.preimage hc
  refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → Fin 2 → ℝ)) (r := 1)).subset fun q hq => ?_
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  rw [Real.norm_eq_abs]
  exact abs_entry_le_one_of_isK hq i j

noncomputable def twistFactor (t : ℝ) (p : Fin 2 → Fin 2 → ℝ) : ℂ := (((|(Matrix.of p).det| ^ t : ℝ)) : ℂ)

theorem contDiff_det_of : ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 2 → Fin 2 → ℝ => (Matrix.of p).det) := by
  have : (fun p : Fin 2 → Fin 2 → ℝ => (Matrix.of p).det) = fun p => p 0 0 * p 1 1 - p 0 1 * p 1 0 := by
    funext p; simp [Matrix.det_fin_two]
  rw [this]
  fun_prop

theorem contDiffOn_twistFactor (t : ℝ) : ContDiffOn ℝ (⊤ : ℕ∞) (twistFactor t) ArchR.glSet := by
  intro p hp
  have hdet : (Matrix.of p).det ≠ 0 := hp
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Fin 2 → Fin 2 → ℝ => (Matrix.of q).det ^ 2) p :=
    (contDiff_det_of.pow 2).contDiffAt
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => x ^ (t / 2)) ((Matrix.of p).det ^ 2) :=
    Real.contDiffAt_rpow_const_of_ne (pow_ne_zero 2 hdet)
  have h3 := h2.comp p h1

  have hR : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Fin 2 → Fin 2 → ℝ => |(Matrix.of q).det| ^ t) p := by
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    show |(Matrix.of q).det| ^ t = ((Matrix.of q).det ^ 2) ^ (t / 2)
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    push_cast
    ring
  have hC := Complex.ofRealCLM.contDiff.contDiffAt.comp p hR
  have hC' : ContDiffAt ℝ (⊤ : ℕ∞) (twistFactor t) p := by
    refine hC.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    simp [twistFactor, Function.comp_apply]
  exact hC'.contDiffWithinAt

theorem exists_bound_twistFactor (t : ℝ) (i : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : Matrix (Fin 2) (Fin 2) ℝ, ArchR.IsK k →
      ‖iteratedFDerivWithin ℝ i (twistFactor t) ArchR.glSet (Matrix.of.symm k)‖ ≤ B := by
  have hcont : ContinuousOn (iteratedFDerivWithin ℝ i (twistFactor t) ArchR.glSet) ArchR.glSet :=
    (contDiffOn_twistFactor t).continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) uniqueDiffOn_glSet
  have hsub : {q : Fin 2 → Fin 2 → ℝ | ArchR.IsK (Matrix.of q)} ⊆ ArchR.glSet := fun q hq =>
    det_ne_zero_of_isK hq
  obtain ⟨B, hB⟩ := isCompact_Kcoords.exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨max B 0, le_max_right _ _, fun k hk => (hB (Matrix.of.symm k) ?_).trans (le_max_left _ _)⟩
  show ArchR.IsK (Matrix.of (Matrix.of.symm k))
  rwa [Equiv.apply_symm_apply]

noncomputable def Dlin (y : ℝ) : (Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → Fin 2 → ℝ) where
  toFun M := Matrix.of.symm (ArchR.diagOne y * Matrix.of M)
  map_add' M N := by
    ext i j
    simp only [Matrix.of_symm_apply, Pi.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
    ring
  map_smul' c M := by
    ext i j
    simp only [Matrix.of_symm_apply, Pi.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul,
      Matrix.of_apply, RingHom.id_apply]
    ring

theorem Dlin_apply (y : ℝ) (M : Fin 2 → Fin 2 → ℝ) : Dlin y M = Matrix.of.symm (ArchR.diagOne y * Matrix.of M) := rfl

theorem Dlin_apply_zero (y : ℝ) (M : Fin 2 → Fin 2 → ℝ) (j : Fin 2) : Dlin y M 0 j = y * M 0 j := by
  simp only [Dlin_apply, Matrix.of_symm_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  simp [ArchR.diagOne]

theorem Dlin_apply_one (y : ℝ) (M : Fin 2 → Fin 2 → ℝ) (j : Fin 2) : Dlin y M 1 j = M 1 j := by
  simp only [Dlin_apply, Matrix.of_symm_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  simp [ArchR.diagOne]

noncomputable def Dclm (y : ℝ) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap (Dlin y)

theorem Dclm_apply (y : ℝ) (M : Fin 2 → Fin 2 → ℝ) : Dclm y M = Matrix.of.symm (ArchR.diagOne y * Matrix.of M) := rfl

theorem Dclm_cancel (y : ℝ) (hy : y ≠ 0) (M : Fin 2 → Fin 2 → ℝ) : Dclm y⁻¹ (Dclm y M) = M := by
  ext i j
  fin_cases i
  · show Dlin y⁻¹ (Dlin y M) 0 j = M 0 j
    rw [Dlin_apply_zero, Dlin_apply_zero, ← mul_assoc, inv_mul_cancel₀ hy, one_mul]
  · show Dlin y⁻¹ (Dlin y M) 1 j = M 1 j
    rw [Dlin_apply_one, Dlin_apply_one]

noncomputable def Dcle (y : ℝ) (hy : y ≠ 0) : (Fin 2 → Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → Fin 2 → ℝ) :=
  ContinuousLinearEquiv.equivOfInverse (Dclm y) (Dclm y⁻¹) (fun M => Dclm_cancel y hy M)
    (fun M => by simpa only [inv_inv] using Dclm_cancel y⁻¹ (inv_ne_zero hy) M)

theorem Dcle_apply (y : ℝ) (hy : y ≠ 0) (M : Fin 2 → Fin 2 → ℝ) :
    Dcle y hy M = Matrix.of.symm (ArchR.diagOne y * Matrix.of M) := rfl

theorem Dcle_coe (y : ℝ) (hy : y ≠ 0) : (Dcle y hy : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ)) = Dclm y := rfl

theorem Dcle_symm_coe (y : ℝ) (hy : y ≠ 0) :
    ((Dcle y hy).symm : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ)) = Dclm y⁻¹ := rfl

theorem norm_Dclm_le (y : ℝ) : ‖Dclm y‖ ≤ max |y| 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun M => ?_
  have h1 : ∀ i' j', ‖M i' j'‖ ≤ ‖M‖ := fun i' j' => (norm_le_pi_norm (M i') j').trans (norm_le_pi_norm M i')
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro j
  fin_cases i
  · show ‖Dlin y M 0 j‖ ≤ _
    rw [Dlin_apply_zero, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul (le_max_left _ _) (h1 0 j) (norm_nonneg _) (by positivity)
  · show ‖Dlin y M 1 j‖ ≤ _
    rw [Dlin_apply_one, ← one_mul ‖M 1 j‖]
    exact mul_le_mul (le_max_right _ _) (h1 1 j) (norm_nonneg _) (by positivity)

theorem det_of_Dclm (y : ℝ) (M : Fin 2 → Fin 2 → ℝ) : (Matrix.of (Dclm y M)).det = y * (Matrix.of M).det := by
  have h0 : ∀ j, Dclm y M 0 j = y * M 0 j := Dlin_apply_zero y M
  have h1 : ∀ j, Dclm y M 1 j = M 1 j := Dlin_apply_one y M
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [Matrix.of_apply, h0, h1]
  ring

theorem det_of_Dcle (y : ℝ) (hy : y ≠ 0) (M : Fin 2 → Fin 2 → ℝ) :
    (Matrix.of (Dcle y hy M)).det = y * (Matrix.of M).det := det_of_Dclm y M

theorem mem_glSet_Dclm_iff (y : ℝ) (hy : y ≠ 0) (M : Fin 2 → Fin 2 → ℝ) :
    Dclm y M ∈ ArchR.glSet ↔ M ∈ ArchR.glSet := by
  simp only [ArchR.glSet, Set.mem_setOf_eq, det_of_Dclm]
  exact mul_ne_zero_iff.trans (and_iff_right hy)

theorem preimage_glSet_Dcle (y : ℝ) (hy : y ≠ 0) : (Dcle y hy) ⁻¹' ArchR.glSet = ArchR.glSet := by
  ext M; exact mem_glSet_Dclm_iff y hy M

theorem preimage_glSet_Dcle_symm (y : ℝ) (hy : y ≠ 0) : (Dcle y hy).symm ⁻¹' ArchR.glSet = ArchR.glSet := by
  ext M; exact mem_glSet_Dclm_iff y⁻¹ (inv_ne_zero hy) M

theorem Dcle_of_symm (y : ℝ) (hy : y ≠ 0) (k : Matrix (Fin 2) (Fin 2) ℝ) :
    Dcle y hy (Matrix.of.symm k) = ArchR.diagOneMulCoords y k := by
  rw [Dcle_apply, Equiv.apply_symm_apply]; rfl

variable {P : RealArchParam}

theorem asPi_twist (D : ArchDatumR P) (t : ℝ) :
    ArchR.asPi (fun g : Matrix (Fin 2) (Fin 2) ℝ => (((|g.det| ^ t : ℝ)) : ℂ) * D.W g)
      = fun p => twistFactor t p * ArchR.asPi D.W p := by
  funext p; rfl

theorem twist_comp_Dcle (D : ArchDatumR P) (t y : ℝ) (hy : y ≠ 0) :
    (fun p => twistFactor t p * ArchR.asPi D.W p) ∘ (Dcle y hy)
      = fun q => ((((|y| ^ t : ℝ)) : ℂ) * twistFactor t q) * (ArchR.asPi D.W ∘ Dcle y hy) q := by
  funext q
  simp only [Function.comp_apply, twistFactor]
  rw [det_of_Dcle, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  push_cast
  ring

theorem smooth_twist (D : ArchDatumR P) (t : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi (fun g : Matrix (Fin 2) (Fin 2) ℝ => (((|g.det| ^ t : ℝ)) : ℂ) * D.W g))
      ArchR.glSet := by
  rw [asPi_twist]
  exact (contDiffOn_twistFactor t).mul D.smooth

theorem contDiffOn_comp_Dcle (D : ArchDatumR P) (y : ℝ) (hy : y ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi D.W ∘ Dcle y hy) ArchR.glSet := by
  refine D.smooth.comp (Dcle y hy).contDiff.contDiffOn fun M hM => ?_
  exact (mem_glSet_Dclm_iff y hy M).2 hM

theorem norm_iteratedFDerivWithin_twist_le (D : ArchDatumR P) (t : ℝ) (j : ℕ) (B : ℕ → ℝ) (hB0 : ∀ i, 0 ≤ B i)
    (hB : ∀ i k, ArchR.IsK k → ‖iteratedFDerivWithin ℝ i (twistFactor t) ArchR.glSet (Matrix.of.symm k)‖ ≤ B i)
    (y : ℝ) (hy : y ≠ 0) (k : Matrix (Fin 2) (Fin 2) ℝ) (hk : ArchR.IsK k) :
    ‖iteratedFDerivWithin ℝ j (ArchR.asPi (fun g : Matrix (Fin 2) (Fin 2) ℝ => (((|g.det| ^ t : ℝ)) : ℂ) * D.W g))
        ArchR.glSet (ArchR.diagOneMulCoords y k)‖
      ≤ (max |y|⁻¹ 1) ^ j * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (|y| ^ t * B i) *
          ((max |y| 1) ^ (j - i) * ‖iteratedFDerivWithin ℝ (j - i) (ArchR.asPi D.W) ArchR.glSet
            (ArchR.diagOneMulCoords y k)‖) := by
  set F : (Fin 2 → Fin 2 → ℝ) → ℂ := fun p => twistFactor t p * ArchR.asPi D.W p with hF
  set L := Dcle y hy with hL
  set k₀ : Fin 2 → Fin 2 → ℝ := Matrix.of.symm k with hk₀
  have hk₀mem : k₀ ∈ ArchR.glSet := by
    show (Matrix.of (Matrix.of.symm k)).det ≠ 0
    rw [Equiv.apply_symm_apply]; exact det_ne_zero_of_isK hk
  have hLk₀ : L k₀ = ArchR.diagOneMulCoords y k := Dcle_of_symm y hy k
  have hLk₀mem : L k₀ ∈ ArchR.glSet := (mem_glSet_Dclm_iff y hy k₀).2 hk₀mem
  rw [asPi_twist, ← hF, ← hLk₀]

  have hFeq : F = (F ∘ L) ∘ L.symm := by funext p; simp
  have keyA := L.symm.iteratedFDerivWithin_comp_right (F ∘ L) uniqueDiffOn_glSet
    (show L.symm (L k₀) ∈ ArchR.glSet by rw [L.symm_apply_apply]; exact hk₀mem) j
  rw [preimage_glSet_Dcle_symm, ← hFeq, L.symm_apply_apply] at keyA
  have stepA : ‖iteratedFDerivWithin ℝ j F ArchR.glSet (L k₀)‖
      ≤ ‖iteratedFDerivWithin ℝ j (F ∘ L) ArchR.glSet k₀‖ * (max |y|⁻¹ 1) ^ j := by
    rw [keyA]
    calc ‖(iteratedFDerivWithin ℝ j (F ∘ ⇑L) ArchR.glSet k₀).compContinuousLinearMap fun _ =>
            ((L.symm : (Fin 2 → Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → Fin 2 → ℝ)) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ))‖
          ≤ ‖iteratedFDerivWithin ℝ j (F ∘ ⇑L) ArchR.glSet k₀‖ * ∏ _i : Fin j,
              ‖((L.symm : (Fin 2 → Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → Fin 2 → ℝ)) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ))‖ :=
            ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDerivWithin ℝ j (F ∘ ⇑L) ArchR.glSet k₀‖ * ‖Dclm y⁻¹‖ ^ j := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hL, Dcle_symm_coe]
      _ ≤ ‖iteratedFDerivWithin ℝ j (F ∘ ⇑L) ArchR.glSet k₀‖ * (max |y|⁻¹ 1) ^ j := by
            gcongr
            simpa only [abs_inv] using norm_Dclm_le y⁻¹

  have hcomp : F ∘ L = fun q => ((((|y| ^ t : ℝ)) : ℂ) * twistFactor t q) * (ArchR.asPi D.W ∘ L) q :=
    twist_comp_Dcle D t y hy
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (fun q => (((|y| ^ t : ℝ)) : ℂ) * twistFactor t q) ArchR.glSet :=
    contDiffOn_const.mul (contDiffOn_twistFactor t)
  have hψ : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi D.W ∘ L) ArchR.glSet := contDiffOn_comp_Dcle D y hy
  have stepB : ‖iteratedFDerivWithin ℝ j (F ∘ L) ArchR.glSet k₀‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (fun q => (((|y| ^ t : ℝ)) : ℂ) * twistFactor t q) ArchR.glSet k₀‖ *
          ‖iteratedFDerivWithin ℝ (j - i) (ArchR.asPi D.W ∘ L) ArchR.glSet k₀‖ := by
    rw [hcomp]
    exact norm_iteratedFDerivWithin_mul_le hφ hψ uniqueDiffOn_glSet hk₀mem (n := j) (by exact_mod_cast le_top)

  have hfac1 : ∀ i, ‖iteratedFDerivWithin ℝ i (fun q => (((|y| ^ t : ℝ)) : ℂ) * twistFactor t q) ArchR.glSet k₀‖
      ≤ |y| ^ t * B i := by
    intro i
    have hcd : ContDiffWithinAt ℝ (i : ℕ∞) (twistFactor t) ArchR.glSet k₀ :=
      ((contDiffOn_twistFactor t) k₀ hk₀mem).of_le (by exact_mod_cast le_top)
    have := iteratedFDerivWithin_const_smul_apply (a := (((|y| ^ t : ℝ)) : ℂ)) hcd uniqueDiffOn_glSet hk₀mem
    rw [show (fun q => (((|y| ^ t : ℝ)) : ℂ) * twistFactor t q) = ((((|y| ^ t : ℝ)) : ℂ) • twistFactor t) from rfl,
      this, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) t)]
    exact mul_le_mul_of_nonneg_left (hB i k hk) (Real.rpow_nonneg (abs_nonneg y) t)
  have hfac2 : ∀ i, ‖iteratedFDerivWithin ℝ i (ArchR.asPi D.W ∘ L) ArchR.glSet k₀‖
      ≤ (max |y| 1) ^ i * ‖iteratedFDerivWithin ℝ i (ArchR.asPi D.W) ArchR.glSet (L k₀)‖ := by
    intro i
    have keyB := L.iteratedFDerivWithin_comp_right (ArchR.asPi D.W) uniqueDiffOn_glSet hLk₀mem i
    rw [preimage_glSet_Dcle] at keyB
    rw [keyB]
    calc ‖(iteratedFDerivWithin ℝ i (ArchR.asPi D.W) ArchR.glSet (L k₀)).compContinuousLinearMap fun _ =>
            ((L : (Fin 2 → Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → Fin 2 → ℝ)) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ))‖
          ≤ ‖iteratedFDerivWithin ℝ i (ArchR.asPi D.W) ArchR.glSet (L k₀)‖ * ∏ _i : Fin i,
              ‖((L : (Fin 2 → Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → Fin 2 → ℝ)) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ))‖ :=
            ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDerivWithin ℝ i (ArchR.asPi D.W) ArchR.glSet (L k₀)‖ * ‖Dclm y‖ ^ i := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hL, Dcle_coe]
      _ ≤ ‖iteratedFDerivWithin ℝ i (ArchR.asPi D.W) ArchR.glSet (L k₀)‖ * (max |y| 1) ^ i := by
            gcongr; exact norm_Dclm_le y
      _ = _ := mul_comm _ _

  have hterm : ∀ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (fun q => (((|y| ^ t : ℝ)) : ℂ) * twistFactor t q) ArchR.glSet k₀‖ *
          ‖iteratedFDerivWithin ℝ (j - i) (ArchR.asPi D.W ∘ L) ArchR.glSet k₀‖
        ≤ (j.choose i : ℝ) * (|y| ^ t * B i) *
          ((max |y| 1) ^ (j - i) * ‖iteratedFDerivWithin ℝ (j - i) (ArchR.asPi D.W) ArchR.glSet (L k₀)‖) := by
    intro i _
    have hnn : 0 ≤ (j.choose i : ℝ) * (|y| ^ t * B i) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.rpow_nonneg (abs_nonneg y) t) (hB0 i))
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hfac1 i) (Nat.cast_nonneg _)) (hfac2 (j - i))
      (norm_nonneg _) hnn
  have hm : 0 ≤ (max |y|⁻¹ 1) ^ j := by positivity
  calc ‖iteratedFDerivWithin ℝ j F ArchR.glSet (L k₀)‖
      ≤ ‖iteratedFDerivWithin ℝ j (F ∘ L) ArchR.glSet k₀‖ * (max |y|⁻¹ 1) ^ j := stepA
    _ ≤ (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (fun q => (((|y| ^ t : ℝ)) : ℂ) * twistFactor t q) ArchR.glSet k₀‖ *
          ‖iteratedFDerivWithin ℝ (j - i) (ArchR.asPi D.W ∘ L) ArchR.glSet k₀‖) * (max |y|⁻¹ 1) ^ j :=
        mul_le_mul_of_nonneg_right stepB hm
    _ ≤ (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (|y| ^ t * B i) *
          ((max |y| 1) ^ (j - i) * ‖iteratedFDerivWithin ℝ (j - i) (ArchR.asPi D.W) ArchR.glSet (L k₀)‖)) *
          (max |y|⁻¹ 1) ^ j := mul_le_mul_of_nonneg_right (Finset.sum_le_sum hterm) hm
    _ = _ := mul_comm _ _

end Ws47.TWD

namespace Ws47
namespace TWD

variable {P : RealArchParam}

theorem rpow_mul_pow_mul_rpow_le_of_one_le {y t : ℝ} (hy : 1 ≤ |y|) (m : ℕ) (N N' : ℝ)
    (hexp : t + m - N' ≤ -N) : |y| ^ t * ((|y| : ℝ) ^ m * |y| ^ (-N')) ≤ |y| ^ (-N) := by
  have hpos : 0 < |y| := lt_of_lt_of_le one_pos hy
  rw [← Real.rpow_natCast, ← Real.rpow_add hpos, ← Real.rpow_add hpos]
  exact Real.rpow_le_rpow_of_exponent_le hy (by linarith)

theorem rpow_mul_rpow_le_of_le_one {y t σ S : ℝ} (hy0 : y ≠ 0) (hy : |y| ≤ 1) (hσ : σ ≤ S) :
    |y| ^ t * |y| ^ (-σ) ≤ |y| ^ (-|t|) * |y| ^ (-S) := by
  have hpos : 0 < |y| := abs_pos.2 hy0
  refine mul_le_mul ?_ ?_ (Real.rpow_nonneg (abs_nonneg y) _) (Real.rpow_nonneg (abs_nonneg y) _)
  · exact Real.rpow_le_rpow_of_exponent_ge hpos hy (by linarith [neg_abs_le t])
  · exact Real.rpow_le_rpow_of_exponent_ge hpos hy (by linarith)

theorem decay_top_twist (D : ArchDatumR P) (t : ℝ) (j N : ℕ) :
    ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → 1 ≤ |y| →
      ‖iteratedFDerivWithin ℝ j (ArchR.asPi (fun g : Matrix (Fin 2) (Fin 2) ℝ => (((|g.det| ^ t : ℝ)) : ℂ) * D.W g))
        ArchR.glSet (ArchR.diagOneMulCoords y k)‖ ≤ C * |y| ^ (-(N : ℝ)) := by

  have hBex : ∀ i : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ k : Matrix (Fin 2) (Fin 2) ℝ, ArchR.IsK k →
      ‖iteratedFDerivWithin ℝ i (twistFactor t) ArchR.glSet (Matrix.of.symm k)‖ ≤ B := exists_bound_twistFactor t
  choose B hB0 hB using hBex

  set N' : ℕ := N + j + ⌈|t|⌉₊ with hN'
  have hDex : ∀ i : ℕ, ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → 1 ≤ |y| →
      ‖iteratedFDerivWithin ℝ (j - i) (ArchR.asPi D.W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖
        ≤ C * |y| ^ (-(N' : ℝ)) := fun i => D.decay_top (j - i) N'
  choose Cd hCd using hDex
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * |Cd i|, fun y k hk hy => ?_⟩
  have hy0 : y ≠ 0 := fun h => by rw [h, abs_zero] at hy; exact absurd hy (by norm_num)
  have hypos : 0 < |y| := abs_pos.2 hy0
  have key := norm_iteratedFDerivWithin_twist_le D t j B hB0 hB y hy0 k hk
  have hmax1 : max |y|⁻¹ 1 = 1 := max_eq_right (inv_le_one_of_one_le₀ hy)
  have hmax2 : max |y| 1 = |y| := max_eq_left hy
  rw [hmax1, hmax2, one_pow, one_mul] at key
  refine key.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : j - i ≤ j := Nat.sub_le j i

  have h1 : |y| ^ (j - i) * ‖iteratedFDerivWithin ℝ (j - i) (ArchR.asPi D.W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖
      ≤ |y| ^ (j - i) * (|Cd i| * |y| ^ (-(N' : ℝ))) := by
    refine mul_le_mul_of_nonneg_left ((hCd i y k hk hy).trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (abs_nonneg y) _)
  have hexp : t + ((j - i : ℕ) : ℝ) - (N' : ℝ) ≤ -(N : ℝ) := by
    have h2 : ((j - i : ℕ) : ℝ) ≤ j := by exact_mod_cast hi'
    have h3 : |t| ≤ ⌈|t|⌉₊ := Nat.le_ceil _
    have h4 : (N' : ℝ) = N + j + ⌈|t|⌉₊ := by rw [hN']; push_cast; ring
    linarith [le_abs_self t]
  have h5 := rpow_mul_pow_mul_rpow_le_of_one_le (t := t) hy (j - i) (N : ℝ) (N' : ℝ) hexp
  calc (j.choose i : ℝ) * (|y| ^ t * B i) *
        (|y| ^ (j - i) * ‖iteratedFDerivWithin ℝ (j - i) (ArchR.asPi D.W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖)
      ≤ (j.choose i : ℝ) * (|y| ^ t * B i) * (|y| ^ (j - i) * (|Cd i| * |y| ^ (-(N' : ℝ)))) := by
        refine mul_le_mul_of_nonneg_left h1 ?_
        exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.rpow_nonneg (abs_nonneg y) t) (hB0 i))
    _ = (j.choose i : ℝ) * B i * |Cd i| * (|y| ^ t * ((|y| : ℝ) ^ (j - i) * |y| ^ (-(N' : ℝ)))) := by ring
    _ ≤ (j.choose i : ℝ) * B i * |Cd i| * |y| ^ (-(N : ℝ)) := by
        refine mul_le_mul_of_nonneg_left h5 ?_
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB0 i)) (abs_nonneg _)

theorem decay_zero_twist (D : ArchDatumR P) (t : ℝ) (j : ℕ) :
    ∃ (C σ : ℝ), ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 → |y| ≤ 1 →
      ‖iteratedFDerivWithin ℝ j (ArchR.asPi (fun g : Matrix (Fin 2) (Fin 2) ℝ => (((|g.det| ^ t : ℝ)) : ℂ) * D.W g))
        ArchR.glSet (ArchR.diagOneMulCoords y k)‖ ≤ C * |y| ^ (-σ) := by
  have hBex : ∀ i : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ k : Matrix (Fin 2) (Fin 2) ℝ, ArchR.IsK k →
      ‖iteratedFDerivWithin ℝ i (twistFactor t) ArchR.glSet (Matrix.of.symm k)‖ ≤ B := exists_bound_twistFactor t
  choose B hB0 hB using hBex
  have hDex : ∀ i : ℕ, ∃ (C σ : ℝ), ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 → |y| ≤ 1 →
      ‖iteratedFDerivWithin ℝ (j - i) (ArchR.asPi D.W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖
        ≤ C * |y| ^ (-σ) := fun i => D.decay_zero (j - i)
  choose Cd σd hCd using hDex
  set S : ℝ := ∑ i ∈ Finset.range (j + 1), |σd i| with hS
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * |Cd i|, (j : ℝ) + |t| + S, fun y k hk hy0 hy => ?_⟩
  have hypos : 0 < |y| := abs_pos.2 hy0
  have key := norm_iteratedFDerivWithin_twist_le D t j B hB0 hB y hy0 k hk
  have hmax1 : max |y|⁻¹ 1 = |y|⁻¹ := max_eq_left (one_le_inv_iff₀.mpr ⟨hypos, hy⟩)
  have hmax2 : max |y| 1 = 1 := max_eq_right hy
  rw [hmax1, hmax2] at key
  simp only [one_pow, one_mul] at key
  refine key.trans ?_

  have hinv : (|y|⁻¹ : ℝ) ^ j = |y| ^ (-(j : ℝ)) := by
    rw [Real.rpow_neg (abs_nonneg y), Real.rpow_natCast, inv_pow]
  have hsplit : |y| ^ (-((j : ℝ) + |t| + S)) = |y| ^ (-(j : ℝ)) * (|y| ^ (-|t|) * |y| ^ (-S)) := by
    rw [← Real.rpow_add hypos, ← Real.rpow_add hypos]; congr 1; ring
  rw [hinv, hsplit, ← mul_assoc, mul_comm (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * |Cd i|),
    mul_assoc, Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (Real.rpow_nonneg (abs_nonneg y) _)
  have hσS : σd i ≤ S := by
    rw [hS]
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |σd i|) (fun _ _ => abs_nonneg _) hi)
  have h1 : ‖iteratedFDerivWithin ℝ (j - i) (ArchR.asPi D.W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖
      ≤ |Cd i| * |y| ^ (-σd i) :=
    (hCd i y k hk hy0 hy).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (abs_nonneg y) _))
  have h5 := rpow_mul_rpow_le_of_le_one (t := t) hy0 hy hσS
  calc (j.choose i : ℝ) * (|y| ^ t * B i) *
        ‖iteratedFDerivWithin ℝ (j - i) (ArchR.asPi D.W) ArchR.glSet (ArchR.diagOneMulCoords y k)‖
      ≤ (j.choose i : ℝ) * (|y| ^ t * B i) * (|Cd i| * |y| ^ (-σd i)) := by
        refine mul_le_mul_of_nonneg_left h1 ?_
        exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.rpow_nonneg (abs_nonneg y) t) (hB0 i))
    _ = (j.choose i : ℝ) * B i * |Cd i| * (|y| ^ t * |y| ^ (-σd i)) := by ring
    _ ≤ (j.choose i : ℝ) * B i * |Cd i| * (|y| ^ (-|t|) * |y| ^ (-S)) := by
        refine mul_le_mul_of_nonneg_left h5 ?_
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB0 i)) (abs_nonneg _)

end Ws47.TWD

namespace Ws47
namespace TWD

variable {P : RealArchParam}

theorem smooth' (D : ArchDatumR P) (t : ℝ) : ContDiffOn ℝ (⊤ : ℕ∞) (ArchR.asPi (twistW D t)) ArchR.glSet :=
  smooth_twist D t

theorem decay_top' (D : ArchDatumR P) (t : ℝ) (j N : ℕ) :
    ∃ C : ℝ, ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → 1 ≤ |y| →
      ‖iteratedFDerivWithin ℝ j (ArchR.asPi (twistW D t)) ArchR.glSet (ArchR.diagOneMulCoords y k)‖
        ≤ C * |y| ^ (-(N : ℝ)) :=
  decay_top_twist D t j N

theorem decay_zero' (D : ArchDatumR P) (t : ℝ) (j : ℕ) :
    ∃ (C σ : ℝ), ∀ (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ), ArchR.IsK k → y ≠ 0 → |y| ≤ 1 →
      ‖iteratedFDerivWithin ℝ j (ArchR.asPi (twistW D t)) ArchR.glSet (ArchR.diagOneMulCoords y k)‖
        ≤ C * |y| ^ (-σ) :=
  decay_zero_twist D t j

end Ws47.TWD

namespace Ws47
namespace TWD

open LanglandsTunnell.Converse.ArchR LanglandsTunnell.Converse.ArchCasimir MeasureTheory

variable {P : RealArchParam}

theorem centralExponent_twist (P : RealArchParam) (u : ℂ) (a : ZMod 2) :
    (P.twist u a).centralExponent = P.centralExponent + 2 * u := by
  cases P <;> simp [RealArchParam.twist, RealArchParam.centralExponent] <;> ring

theorem centralSign_twist (P : RealArchParam) (u : ℂ) (a : ZMod 2) :
    (P.twist u a).centralSign = P.centralSign := by
  have h2 : ∀ b : ZMod 2, b + b = 0 := by decide
  cases P with
  | principal u₁ a₁ u₂ a₂ =>
    simp only [RealArchParam.twist, RealArchParam.centralSign]
    linear_combination h2 a
  | discrete u₀ k hk => simp [RealArchParam.twist, RealArchParam.centralSign]

theorem archFactor_twist_zero (P : RealArchParam) (u s : ℂ) :
    (P.twist u 0).archFactor s = P.archFactor (s + u) := by
  simp only [RealArchParam.archFactor, RealArchParam.gammaR_twist_zero, RealArchParam.gammaC_twist,
    Multiset.map_map, Function.comp_def]
  congr 3 <;> (funext μ; congr 1; ring)

theorem laplaceEigenvalue_twist_zero (P : RealArchParam) (u : ℂ) :
    (P.twist u 0).laplaceEigenvalue = P.laplaceEigenvalue := by
  cases P <;> simp [RealArchParam.twist, RealArchParam.laplaceEigenvalue]

theorem unip_law' (D : ArchDatumR P) (t : ℝ) (x : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) :
    twistW D t (unip x * g) = psi x * twistW D t g := by
  unfold twistW
  have hdet : (unip x * g).det = g.det := by
    rw [Matrix.det_mul]; simp [unip, Matrix.det_fin_two]
  rw [hdet, D.unip_law]; ring

theorem central_law' (D : ArchDatumR P) (t : ℝ) (z : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) (hz : z ≠ 0) :
    twistW D t (z • g) = centralChar (P.twist (t : ℂ) 0) z * ((|z| : ℝ) : ℂ) * twistW D t g := by
  unfold twistW
  have hdet : (z • g).det = z ^ 2 * g.det := by
    rw [Matrix.det_smul, Fintype.card_fin]
  have habs : |(z • g).det| = |z| ^ (2 : ℕ) * |g.det| := by rw [hdet, abs_mul, abs_pow]
  have hrpow : |(z • g).det| ^ t = |z| ^ (2 * t) * |g.det| ^ t := by
    rw [habs, Real.mul_rpow (pow_nonneg (abs_nonneg z) 2) (abs_nonneg _), ← Real.rpow_natCast,
      ← Real.rpow_mul (abs_nonneg z)]
    norm_num
  rw [hrpow, D.central_law z g hz]

  have hz' : ((|z| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr hz).ne'
  have hcc : centralChar (P.twist (t : ℂ) 0) z = centralChar P z * (((|z| ^ (2 * t) : ℝ)) : ℂ) := by
    simp only [centralChar, quasiChar, centralExponent_twist, centralSign_twist]
    rw [Complex.cpow_add _ _ hz', Complex.ofReal_cpow (abs_nonneg z)]
    push_cast; ring
  rw [hcc]; push_cast; ring

noncomputable def zetaEntire' (D : ArchDatumR P) (t : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) (s : ℂ) : ℂ :=
  (((|g.det| ^ t : ℝ)) : ℂ) * D.zetaEntire g (u + t) a s

theorem zetaEntire'_differentiable (D : ArchDatumR P) (t : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) :
    Differentiable ℂ (zetaEntire' D t g u a) := by
  show Differentiable ℂ fun s => (((|g.det| ^ t : ℝ)) : ℂ) * D.zetaEntire g (u + t) a s
  exact (D.zetaEntire_differentiable g (u + t) a).const_mul _

theorem zetaIntegrand_twistW (D : ArchDatumR P) (t : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) (s : ℂ) :
    zetaIntegrand (twistW D t) g u a s = fun y => (((|g.det| ^ t : ℝ)) : ℂ) * zetaIntegrand D.W g (u + t) a s y := by
  funext y
  simp only [zetaIntegrand, twistW]
  by_cases hy : y = 0
  · subst hy; simp
  have hy' : ((|y| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_pos.mpr hy).ne'
  have hdet : (diagOne y * g).det = y * g.det := by
    rw [Matrix.det_mul]; simp [diagOne, Matrix.det_fin_two]
  have hrpow : (((|(diagOne y * g).det| ^ t : ℝ)) : ℂ) = ((|y| : ℝ) : ℂ) ^ (t : ℂ) * (((|g.det| ^ t : ℝ)) : ℂ) := by
    rw [hdet, abs_mul, Real.mul_rpow (abs_nonneg y) (abs_nonneg _)]
    push_cast
    rw [Complex.ofReal_cpow (abs_nonneg y)]
    try push_cast
    try ring
  have hq : quasiChar (u + (t : ℂ)) a y = quasiChar u a y * ((|y| : ℝ) : ℂ) ^ (t : ℂ) := by
    simp only [quasiChar]; rw [Complex.cpow_add _ _ hy']; ring
  rw [hrpow, hq]; ring

theorem zeta_integrable' (D : ArchDatumR P) (t : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) (s : ℂ)
    (hg : g.det ≠ 0) (hs : D.zeta_abscissa - t < s.re + u.re) :
    Integrable (zetaIntegrand (twistW D t) g u a s) := by
  rw [zetaIntegrand_twistW]
  refine (D.zeta_integrable g (u + t) a s hg ?_).const_mul _
  simp only [Complex.add_re, Complex.ofReal_re]; linarith

theorem zeta_eq' (D : ArchDatumR P) (t : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) (s : ℂ)
    (hg : g.det ≠ 0) (hs : D.zeta_abscissa - t < s.re + u.re) :
    ∫ y : ℝ, zetaIntegrand (twistW D t) g u a s y = ((P.twist (t : ℂ) 0).twist u a).archFactor s * zetaEntire' D t g u a s := by
  have h : D.zeta_abscissa < s.re + (u + (t : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]; linarith
  rw [zetaIntegrand_twistW, MeasureTheory.integral_const_mul, D.zeta_eq g (u + t) a s hg h, RealArchParam.twist_twist,
    add_comm (t : ℂ) u, zero_add]
  simp only [zetaEntire']; ring

theorem functional_equation' (D : ArchDatumR P) (t : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) (s : ℂ)
    (hg : g.det ≠ 0) :
    zetaEntire' D t (weyl * g) (-(u + (P.twist (t : ℂ) 0).centralExponent)) (a + (P.twist (t : ℂ) 0).centralSign) (1 - s)
      = ((P.twist (t : ℂ) 0).twist u a).epsilonFactor * zetaEntire' D t g u a s := by
  simp only [zetaEntire']
  have hdet : (weyl * g).det = g.det := by rw [Matrix.det_mul]; simp [weyl, Matrix.det_fin_two]
  rw [hdet, centralExponent_twist, centralSign_twist,
    show -(u + (P.centralExponent + 2 * (t : ℂ))) + (t : ℂ) = -((u + t) + P.centralExponent) by ring,
    D.functional_equation g (u + t) a s hg, RealArchParam.twist_twist, add_comm (t : ℂ) u, zero_add]
  ring

theorem zetaEntire'_finiteOrder (D : ArchDatumR P) (t : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ) (a : ZMod 2) (A B : ℝ) :
    ∃ C D' : ℝ, ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖zetaEntire' D t g u a s‖ ≤ C * Real.exp (D' * |s.im|) := by
  obtain ⟨C, D', h⟩ := D.zetaEntire_finiteOrder g (u + t) a A B
  refine ⟨‖(((|g.det| ^ t : ℝ)) : ℂ)‖ * C, D', fun s hA hB => ?_⟩
  simp only [zetaEntire', norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h s hA hB) (norm_nonneg _)

noncomputable def twistDatum (D : ArchDatumR P) (t : ℝ) : ArchDatumR (P.twist (t : ℂ) 0) where
  W := twistW D t
  smooth := smooth' D t
  unip_law := unip_law' D t
  central_law := central_law' D t
  zetaEntire := zetaEntire' D t
  zetaEntire_differentiable := zetaEntire'_differentiable D t
  zeta_abscissa := D.zeta_abscissa - t
  zeta_integrable := fun g u a s hg hs => zeta_integrable' D t g u a s hg hs
  zeta_eq := fun g u a s hg hs => zeta_eq' D t g u a s hg hs
  functional_equation := fun g u a s hg => functional_equation' D t g u a s hg
  zetaEntire_finiteOrder := zetaEntire'_finiteOrder D t
  decay_top := decay_top' D t
  decay_zero := decay_zero' D t

theorem isCasimirEigen_twist (D : ArchDatumR P) (t : ℝ) (hD : IsCasimirEigen D) : IsCasimirEigen (twistDatum D t) := by

  have hflow : ∀ (d : AutomorphicForm.ArchDir) (s : ℝ),
      ((AutomorphicForm.archFlowMatrix d s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    intro d s
    cases d <;> simp [AutomorphicForm.archFlowMatrix, AutomorphicForm.splitTorusGL2_coe, AutomorphicForm.unipotentGL2_coe,
      AutomorphicForm.lowerUnipotentGL2_coe, Matrix.det_fin_two, ← Real.exp_add]
  have key : ∀ (d : AutomorphicForm.ArchDir) (F : Matrix (Fin 2) (Fin 2) ℝ → ℂ),
      matrixFlowDeriv d (fun x => (((|x.det| ^ t : ℝ)) : ℂ) * F x) = fun x => (((|x.det| ^ t : ℝ)) : ℂ) * matrixFlowDeriv d F x := by
    intro d F; funext x
    simp only [matrixFlowDeriv]
    have e : (fun s : ℝ => (((|(x * (AutomorphicForm.archFlowMatrix d s : Matrix (Fin 2) (Fin 2) ℝ)).det| ^ t : ℝ)) : ℂ) *
        F (x * (AutomorphicForm.archFlowMatrix d s : Matrix (Fin 2) (Fin 2) ℝ))) =
        fun s : ℝ => (((|x.det| ^ t : ℝ)) : ℂ) * F (x * (AutomorphicForm.archFlowMatrix d s : Matrix (Fin 2) (Fin 2) ℝ)) := by
      funext s; rw [Matrix.det_mul, hflow, mul_one]
    rw [e, deriv_const_mul_field']
  intro x hx
  have hW : (twistDatum D t).W = fun x => (((|x.det| ^ t : ℝ)) : ℂ) * D.W x := rfl
  have hC : matrixCasimir (twistDatum D t).W x = (((|x.det| ^ t : ℝ)) : ℂ) * matrixCasimir D.W x := by
    rw [hW]; simp only [matrixCasimir, key, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [hC, hD x hx, laplaceEigenvalue_twist_zero, hW]; ring

theorem weightLaw_twist (D : ArchDatumR P) (t : ℝ) (k : ℤ)
    (hk : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ) :
    (twistDatum D t).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (archWeightCharℝ k r : ℂ) * (twistDatum D t).W (x : Matrix (Fin 2) (Fin 2) ℝ) := by
  show twistW D t _ = _ * twistW D t _
  unfold twistW
  have hr : ((r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := ((mem_rowIsometrySubgroup₀_iff ℝ).mp r.2).1
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, hr, mul_one, ← Matrix.GeneralLinearGroup.coe_mul, hk r x]
  ring

theorem ne_zero_twist (D : ArchDatumR P) (t : ℝ) (h : ∃ g : GL (Fin 2) ℝ, D.W g ≠ 0) :
    ∃ g : GL (Fin 2) ℝ, (twistDatum D t).W g ≠ 0 := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, ?_⟩
  show twistW D t _ ≠ 0
  unfold twistW
  refine mul_ne_zero ?_ hg
  have hd : ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det g).ne_zero
  exact_mod_cast (Real.rpow_pos_of_pos (abs_pos.mpr hd) t).ne'

end Ws47.TWD

theorem solution
    (P : RealArchParam) (D : ArchDatumR P) (t : ℝ) :
    ∃ D' : ArchDatumR (P.twist (t : ℂ) 0),
      (∀ g : Matrix (Fin 2) (Fin 2) ℝ, D'.W g = (((|g.det| ^ t : ℝ)) : ℂ) * D.W g) ∧
      (ArchCasimir.IsCasimirEigen D → ArchCasimir.IsCasimirEigen D') ∧
      (∀ k : ℤ, (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
          D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
            (archWeightCharℝ k r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ)) →
        (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
          D'.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
            (archWeightCharℝ k r : ℂ) * D'.W (x : Matrix (Fin 2) (Fin 2) ℝ))) ∧
      ((∃ g : GL (Fin 2) ℝ, D.W g ≠ 0) → ∃ g : GL (Fin 2) ℝ, D'.W g ≠ 0) := by
  refine ⟨Ws47.TWD.twistDatum D t, fun g => rfl, Ws47.TWD.isCasimirEigen_twist D t, fun k hk => Ws47.TWD.weightLaw_twist D t k hk, Ws47.TWD.ne_zero_twist D t⟩

end S_LanglandsTunnell_Converse_ArchDatumR_exists_twist_W_eq_abs_det_rpow_mul
end P2MW
export P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_twist_W_eq_abs_det_rpow_mul (solution)
