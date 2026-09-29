-- Prove2me | solution 1 for LanglandsTunnell.Converse.ArchDatumR.exists_sgnTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/54f8e0cb-c785-51c8-be18-8047ff662d9f

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_sgnTwist

set_option autoImplicit false

p2m_open "LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_sgnTwist.LanglandsTunnell.Converse"

noncomputable section

open Complex MeasureTheory

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.ArchDatumR RealArchParam RealArchParam.twist RealArchParam.centralSign RealArchParam.principal"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "ArchDatumR"
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

p2m_open "LanglandsTunnell.Converse.ArchR"

private theorem isK_det_ne_zero {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : IsK k) : k.det ≠ 0 := by
  have h := congrArg Matrix.det ((Matrix.mem_orthogonalGroup_iff _ _).mp hk)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact left_ne_zero_of_mul_eq_one h

namespace DetSign

private def posSet : Set (Fin 2 → Fin 2 → ℝ) := {m | 0 < (Matrix.of m).det}

private def negSet : Set (Fin 2 → Fin 2 → ℝ) := {m | (Matrix.of m).det < 0}

private theorem contDiff_coord (i j : Fin 2) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun m : Fin 2 → Fin 2 → ℝ => m i j) :=
  (contDiff_apply ℝ ℝ j).comp (contDiff_apply ℝ (Fin 2 → ℝ) i)

private theorem contDiff_detCoord {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun m : Fin 2 → Fin 2 → ℝ => (Matrix.of m).det) := by
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  exact ((contDiff_coord 0 0).mul (contDiff_coord 1 1)).sub ((contDiff_coord 0 1).mul (contDiff_coord 1 0))

private theorem isOpen_posSet : IsOpen posSet := isOpen_lt continuous_const (contDiff_detCoord (n := 1)).continuous

private theorem isOpen_negSet : IsOpen negSet := isOpen_lt (contDiff_detCoord (n := 1)).continuous continuous_const

private theorem glSet_eq : glSet = posSet ∪ negSet := by
  ext m
  simp only [glSet, posSet, negSet, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro h
    rcases lt_or_gt_of_ne h with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact h.ne'
    · exact h.ne

private theorem isOpen_glSet : IsOpen glSet := by
  rw [glSet_eq]
  exact isOpen_posSet.union isOpen_negSet

private theorem det_of_diagOneMulCoords (y : ℝ) (k : Matrix (Fin 2) (Fin 2) ℝ) :
    (Matrix.of (diagOneMulCoords y k)).det = y * k.det := by
  have h : Matrix.of (diagOneMulCoords y k) = diagOne y * k := Matrix.of.apply_symm_apply _
  rw [h, Matrix.det_mul]
  simp [diagOne, Matrix.det_fin_two_of]

private theorem diagOneMulCoords_mem_glSet {y : ℝ} (hy : y ≠ 0) {k : Matrix (Fin 2) (Fin 2) ℝ} (hk : IsK k) :
    diagOneMulCoords y k ∈ glSet := by
  show (Matrix.of (diagOneMulCoords y k)).det ≠ 0
  rw [det_of_diagOneMulCoords]
  exact mul_ne_zero hy (isK_det_ne_zero hk)

private theorem mem_posSet_or_mem_negSet {q : Fin 2 → Fin 2 → ℝ} (hq : q ∈ glSet) : q ∈ posSet ∨ q ∈ negSet := by
  rw [glSet_eq] at hq
  exact hq

end DetSign

p2m_open "LanglandsTunnell.Converse.ArchR P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_sgnTwist.LanglandsTunnell.Converse.DetSign"

private def sgnC (t : ℝ) : ℂ := ((SignType.sign t : ℝ) : ℂ)

private theorem sgnC_mul (t₁ t₂ : ℝ) : sgnC (t₁ * t₂) = sgnC t₁ * sgnC t₂ := by
  simp [sgnC, sign_mul]

private theorem sgnC_of_pos {t : ℝ} (ht : 0 < t) : sgnC t = 1 := by
  simp [sgnC, sign_pos ht]

private theorem sgnC_of_neg {t : ℝ} (ht : t < 0) : sgnC t = -1 := by
  simp [sgnC, sign_neg ht]

private theorem sgnC_mul_self {t : ℝ} (ht : t ≠ 0) : sgnC t * sgnC t = 1 := by
  rcases lt_or_gt_of_ne ht with h | h
  · rw [sgnC_of_neg h]
    norm_num
  · rw [sgnC_of_pos h]
    norm_num

private theorem norm_sgnC_le (t : ℝ) : ‖sgnC t‖ ≤ 1 := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · rw [sgnC_of_neg h]
    simp
  · simp [sgnC]
  · rw [sgnC_of_pos h]
    simp

private theorem sgnC_sq_mul {z : ℝ} (hz : z ≠ 0) (t : ℝ) : sgnC (z ^ 2 * t) = sgnC t := by
  rw [sgnC_mul, sgnC_of_pos (by positivity), one_mul]

private theorem zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

private theorem zmod_two_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

private theorem quasiChar_add_one (u : ℂ) (a : ZMod 2) {y : ℝ} (hy : y ≠ 0) :
    quasiChar u (a + 1) y = quasiChar u a y * sgnC y := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl
  · simp [quasiChar, sgnC]
  · rw [zmod_two_one_add_one]
    simp only [quasiChar, if_true, if_neg one_ne_zero]
    rw [mul_assoc, show (((SignType.sign y : ℝ)) : ℂ) = sgnC y from rfl, sgnC_mul_self hy, mul_one]

private theorem det_diagOne_mul (y : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) : (diagOne y * g).det = y * g.det := by
  rw [Matrix.det_mul]
  simp [diagOne, Matrix.det_fin_two_of]

private theorem det_unip_mul (x : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) : (unip x * g).det = g.det := by
  rw [Matrix.det_mul]
  simp [unip, Matrix.det_fin_two_of]

private theorem det_weyl_mul (g : Matrix (Fin 2) (Fin 2) ℝ) : (weyl * g).det = g.det := by
  rw [Matrix.det_mul]
  simp [weyl, Matrix.det_fin_two_of]

namespace SignTwistParam

private theorem twist_flip (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (u : ℂ) (a : ZMod 2) :
    (RealArchParam.principal u₁ (a₁ + 1) u₂ (a₂ + 1)).twist u a
      = (RealArchParam.principal u₁ a₁ u₂ a₂).twist u (a + 1) := by
  simp only [RealArchParam.twist]
  congr 1 <;> ring

private theorem centralSign_flip (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) :
    (RealArchParam.principal u₁ (a₁ + 1) u₂ (a₂ + 1)).centralSign
      = (RealArchParam.principal u₁ a₁ u₂ a₂).centralSign := by
  simp only [RealArchParam.centralSign]
  linear_combination zmod_two_one_add_one

private theorem centralExponent_flip (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) :
    (RealArchParam.principal u₁ (a₁ + 1) u₂ (a₂ + 1)).centralExponent
      = (RealArchParam.principal u₁ a₁ u₂ a₂).centralExponent := rfl

end SignTwistParam

private theorem centralChar_flip (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (z : ℝ) :
    centralChar (RealArchParam.principal u₁ (a₁ + 1) u₂ (a₂ + 1)) z
      = centralChar (RealArchParam.principal u₁ a₁ u₂ a₂) z := by
  unfold centralChar
  rw [SignTwistParam.centralSign_flip, SignTwistParam.centralExponent_flip]

namespace SignTwistDatum

private theorem zetaIntegrand_sgnTwist_apply (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ)
    (a : ZMod 2) (s : ℂ) (y : ℝ) :
    zetaIntegrand (fun g => sgnC g.det * W g) g u a s y = sgnC g.det * zetaIntegrand W g u (a + 1) s y := by
  simp only [zetaIntegrand]
  by_cases hy : y = 0
  · subst hy
    simp
  · rw [det_diagOne_mul, sgnC_mul, quasiChar_add_one u a hy]
    ring

private theorem zetaIntegrand_sgnTwist (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ) (u : ℂ)
    (a : ZMod 2) (s : ℂ) :
    zetaIntegrand (fun g => sgnC g.det * W g) g u a s = fun y => sgnC g.det * zetaIntegrand W g u (a + 1) s y :=
  funext (zetaIntegrand_sgnTwist_apply W g u a s)

private theorem norm_iteratedFDerivWithin_sgnTwist (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (j : ℕ) {q : Fin 2 → Fin 2 → ℝ}
    (hq : q ∈ glSet) :
    ‖iteratedFDerivWithin ℝ j (asPi fun g => sgnC g.det * W g) glSet q‖
      = ‖iteratedFDerivWithin ℝ j (asPi W) glSet q‖ := by
  rcases mem_posSet_or_mem_negSet hq with h | h
  · have e : Set.EqOn (asPi fun g => sgnC g.det * W g) (asPi W) posSet := fun m hm => by
      simp only [asPi]
      rw [sgnC_of_pos (show 0 < (Matrix.of m).det from hm), one_mul]
    rw [iteratedFDerivWithin_of_isOpen j isOpen_glSet hq, ← iteratedFDerivWithin_of_isOpen j isOpen_posSet h,
      iteratedFDerivWithin_congr e h, iteratedFDerivWithin_of_isOpen j isOpen_posSet h,
      ← iteratedFDerivWithin_of_isOpen j isOpen_glSet hq]
  · have e : Set.EqOn (asPi fun g => sgnC g.det * W g) (-asPi W) negSet := fun m hm => by
      simp only [asPi, Pi.neg_apply]
      rw [sgnC_of_neg (show (Matrix.of m).det < 0 from hm)]
      ring
    rw [iteratedFDerivWithin_of_isOpen j isOpen_glSet hq, ← iteratedFDerivWithin_of_isOpen j isOpen_negSet h,
      iteratedFDerivWithin_congr e h, iteratedFDerivWithin_neg_apply isOpen_negSet.uniqueDiffOn h, norm_neg,
      iteratedFDerivWithin_of_isOpen j isOpen_negSet h, ← iteratedFDerivWithin_of_isOpen j isOpen_glSet hq]

variable {u₁ u₂ : ℂ} {a₁ a₂ : ZMod 2}

private def sgnTwist (D : ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂)) :
    ArchDatumR (RealArchParam.principal u₁ (a₁ + 1) u₂ (a₂ + 1)) where
  W g := sgnC g.det * D.W g
  smooth := by
    refine contDiffOn_of_locally_contDiffOn fun q hq => ?_
    rcases mem_posSet_or_mem_negSet hq with h | h
    · refine ⟨posSet, isOpen_posSet, h, (D.smooth.mono Set.inter_subset_left).congr fun m hm => ?_⟩
      simp only [asPi]
      rw [sgnC_of_pos (show 0 < (Matrix.of m).det from hm.2), one_mul]
    · refine ⟨negSet, isOpen_negSet, h, (D.smooth.mono Set.inter_subset_left).neg.congr fun m hm => ?_⟩
      simp only [asPi]
      rw [sgnC_of_neg (show (Matrix.of m).det < 0 from hm.2)]
      ring
  unip_law x g := by
    rw [D.unip_law, det_unip_mul]
    ring
  central_law z g hz := by
    rw [D.central_law z g hz, Matrix.det_smul, Fintype.card_fin, sgnC_sq_mul hz, centralChar_flip]
    ring
  zetaEntire g u a s := sgnC g.det * D.zetaEntire g u (a + 1) s
  zetaEntire_differentiable g u a := (D.zetaEntire_differentiable g u (a + 1)).const_mul _
  zeta_abscissa := D.zeta_abscissa
  zeta_integrable g u a s hg hs := by
    rw [zetaIntegrand_sgnTwist]
    exact (D.zeta_integrable g u (a + 1) s hg hs).const_mul _
  zeta_eq g u a s hg hs := by
    simp only [zetaIntegrand_sgnTwist_apply]
    rw [integral_const_mul, D.zeta_eq g u (a + 1) s hg hs, SignTwistParam.twist_flip]
    ring
  functional_equation g u a s hg := by
    have hidx : a + (RealArchParam.principal u₁ (a₁ + 1) u₂ (a₂ + 1)).centralSign + 1
        = (a + 1) + (RealArchParam.principal u₁ a₁ u₂ a₂).centralSign := by
      simp only [RealArchParam.centralSign]
      linear_combination zmod_two_one_add_one
    rw [det_weyl_mul, SignTwistParam.centralExponent_flip, hidx, D.functional_equation g u (a + 1) s hg,
      SignTwistParam.twist_flip]
    ring
  zetaEntire_finiteOrder g u a A B := by
    obtain ⟨C, E, h⟩ := D.zetaEntire_finiteOrder g u (a + 1) A B
    refine ⟨C, E, fun s hA hB => ?_⟩
    calc ‖sgnC g.det * D.zetaEntire g u (a + 1) s‖ = ‖sgnC g.det‖ * ‖D.zetaEntire g u (a + 1) s‖ := norm_mul _ _
      _ ≤ 1 * ‖D.zetaEntire g u (a + 1) s‖ := mul_le_mul_of_nonneg_right (norm_sgnC_le _) (norm_nonneg _)
      _ = ‖D.zetaEntire g u (a + 1) s‖ := one_mul _
      _ ≤ C * Real.exp (E * |s.im|) := h s hA hB
  decay_top j N := by
    obtain ⟨C, h⟩ := D.decay_top j N
    refine ⟨C, fun y k hk hy => ?_⟩
    have hy0 : y ≠ 0 := fun h0 => by rw [h0, abs_zero] at hy; exact absurd hy (by norm_num)
    rw [norm_iteratedFDerivWithin_sgnTwist D.W j (diagOneMulCoords_mem_glSet hy0 hk)]
    exact h y k hk hy
  decay_zero j := by
    obtain ⟨C, σ, h⟩ := D.decay_zero j
    refine ⟨C, σ, fun y k hk hy hy1 => ?_⟩
    rw [norm_iteratedFDerivWithin_sgnTwist D.W j (diagOneMulCoords_mem_glSet hy hk)]
    exact h y k hk hy hy1

@[scoped simp] private theorem sgnTwist_W (D : ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂))
    (g : Matrix (Fin 2) (Fin 2) ℝ) :
    (sgnTwist D).W g = sgnC g.det * D.W g := rfl

end SignTwistDatum
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_sgnTwist.LanglandsTunnell.Converse.SignTwistDatum"

end LanglandsTunnell.Converse
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_sgnTwist.LanglandsTunnell.Converse.SignTwistDatum P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_sgnTwist.LanglandsTunnell P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_sgnTwist.LanglandsTunnell.Converse"
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_sgnTwist.LanglandsTunnell.Converse.SignTwistDatum P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_sgnTwist.LanglandsTunnell"

p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_sgnTwist.LanglandsTunnell LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_sgnTwist.LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchDatumR"

theorem solution (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2)
    (D : ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂)) :
    ∃ D' : ArchDatumR (RealArchParam.principal u₁ (a₁ + 1) u₂ (a₂ + 1)),
      D'.W = fun g => ((SignType.sign g.det : ℝ) : ℂ) * D.W g :=
  ⟨SignTwistDatum.sgnTwist D, rfl⟩

end
end S_LanglandsTunnell_Converse_ArchDatumR_exists_sgnTwist
end P2MW
export P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_sgnTwist (solution)
