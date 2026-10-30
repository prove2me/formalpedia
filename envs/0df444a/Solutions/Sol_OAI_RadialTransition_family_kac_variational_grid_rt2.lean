-- Prove2me | solution 1 for OAI.RadialTransition.family_kac_variational_grid_rt2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:52:22.193993+00:00
-- url     : https://prove2.me/submissions/04aefe3e-6258-43a5-9031-2b05bda61e0f

import Mathlib
import Definitions.Def_RadialTransition
import Definitions.Def_OAIQ112R000
import Theorems.Thm_OAI_RadialTransition_family_ideal_exists_active_rt2
import Theorems.Thm_OAI_RadialTransition_family_kac_lower_limit_rt2
import Theorems.Thm_OAI_RadialTransition_family_kac_upper_limit_rt2
import Theorems.Thm_OAI_RadialTransition_finiteGrandPressure_family_box_error_rt2

section
-- module Solutions.OAIQ112_RT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_IdealAttraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem idealAttraction_eq_of_active {Q : Pressure} {a β h u : ℝ}
    (hu : ActiveShift Q a β h u) :
    idealAttraction Q a β h = attractionBranch Q a u β h := by
  apply IsGreatest.csSup_eq
  exact ⟨⟨u, rfl⟩, by rintro _ ⟨v, rfl⟩; exact hu v⟩

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ShellGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uIndex uV

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

section Shell

theorem independent_of_simplex_gram
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type uIndex} [Fintype ι] [DecidableEq ι] (v : ι → E) {ε : ℝ}
    (hε : 0 ≤ ε) (hsmall : (Fintype.card ι : ℝ) * ε < 1 / 2)
    (hgram : ∀ i j,
      |inner ℝ (v i) (v j) - ((1 : ℝ) / 2 + if i = j then 1 / 2 else 0)| ≤ ε) :
    LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let S : ℝ := ∑ j, c j ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg (c j)
  have hCS : (∑ j, |c j|) ^ 2 ≤ (Fintype.card ι : ℝ) * S := by
    simpa only [Finset.card_univ, sq_abs] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => |c j|))
  have hterm (j k : ι) :
      c j * c k * ((1 : ℝ) / 2 + if j = k then 1 / 2 else 0) -
        ε * |c j| * |c k| ≤ c j * c k * inner ℝ (v j) (v k) := by
    have hh : |c j * c k * (inner ℝ (v j) (v k) -
        ((1 : ℝ) / 2 + if j = k then 1 / 2 else 0))| ≤ ε * |c j| * |c k| := by
      rw [abs_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hgram j k)
        (mul_nonneg (abs_nonneg (c j)) (abs_nonneg (c k)))]
    have hh' := (abs_le.mp hh).1
    nlinarith [hh']
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun j _ =>
    Finset.sum_le_sum (s := Finset.univ) fun k _ => hterm j k
  have hlin : (∑ j, ∑ k, c j * c k * inner ℝ (v j) (v k)) = 0 := by
    have hh : inner ℝ (∑ j, c j • v j) (∑ j, c j • v j) = 0 := by rw [hc]; simp
    simpa only [sum_inner, inner_sum, real_inner_smul_left,
      real_inner_smul_right, mul_assoc, mul_left_comm, mul_comm, real_inner_comm] using hh
  have href : (∑ j, ∑ k,
      c j * c k * ((1 : ℝ) / 2 + if j = k then 1 / 2 else 0)) =
      (1 / 2 : ℝ) * (∑ j, c j) ^ 2 + (1 / 2 : ℝ) * S := by
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
    simp only [S, sq, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  have herr : (∑ j, ∑ k, ε * |c j| * |c k|) = ε * (∑ j, |c j|) ^ 2 := by
    simp only [sq, Finset.mul_sum, Finset.sum_mul]
    congr 1
    ext j
    congr 1
    ext k
    ring
  simp only [Finset.sum_sub_distrib] at hsum
  rw [hlin, href, herr] at hsum
  have hSzero : S = 0 := by
    have he := mul_le_mul_of_nonneg_left hCS hε
    nlinarith [sq_nonneg (∑ j, c j)]
  have hci : c i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j))).mp hSzero i
      (Finset.mem_univ i)
  nlinarith [hci]

theorem no_five_unit_shell (x : Fin 5 → Position)
    (hx : ∀ i j, i ≠ j → 1 ≤ dist (x i) (x j) ∧
      dist (x i) (x j) ≤ 1 + (1 : ℝ) / 1000) : False := by
  let v : Fin 4 → Position := fun i => x i.succ - x 0
  have hsq (i j : Fin 5) (hij : i ≠ j) :
      1 ≤ ‖x i - x j‖ ^ 2 ∧ ‖x i - x j‖ ^ 2 ≤ (1001 / 1000 : ℝ) ^ 2 := by
    have h := hx i j hij
    rw [dist_eq_norm] at h
    constructor <;> nlinarith [h.1, h.2]
  have hnorm (i : Fin 4) :
      1 ≤ ‖v i‖ ^ 2 ∧ ‖v i‖ ^ 2 ≤ (1001 / 1000 : ℝ) ^ 2 :=
    hsq i.succ 0 (Fin.succ_ne_zero i)
  have hgram (i j : Fin 4) :
      |inner ℝ (v i) (v j) - ((1 : ℝ) / 2 + if i = j then 1 / 2 else 0)| ≤
      (2001 / 1000000 : ℝ) := by
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl, real_inner_self_eq_norm_sq]
      have h := hnorm i
      rw [abs_le]
      constructor <;> nlinarith [h.1, h.2]
    · rw [ite_eq_right hij, add_zero, abs_le]
      have hi := hnorm i
      have hj := hnorm j
      have hd := hsq i.succ j.succ (by simpa using hij)
      have heq : v i - v j = x i.succ - x j.succ := by simp [v]
      have hp := norm_sub_sq_real (v i) (v j)
      rw [heq] at hp
      constructor <;> nlinarith [hi.1, hi.2, hj.1, hj.2, hd.1, hd.2, hp]
  have hind := independent_of_simplex_gram v (by norm_num : (0 : ℝ) ≤ 2001 / 1000000)
    (by norm_num : (Fintype.card (Fin 4) : ℝ) * (2001 / 1000000) < 1 / 2) hgram
  have hdim := hind.fintype_card_le_finrank
  norm_num [Position, finrank_euclideanSpace] at hdim

theorem no_five_shell (x : Fin 5 → Position) {l : ℝ} (hl : 0 < l)
    (hx : ∀ i j, i ≠ j → l ≤ dist (x i) (x j) ∧
      dist (x i) (x j) ≤ (1 + (1 : ℝ) / 1000) * l) : False := by
  apply no_five_unit_shell (fun i => l⁻¹ • x i)
  intro i j hij
  have h := hx i j hij
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hl)]
  constructor
  · have hh := mul_le_mul_of_nonneg_left h.1 (inv_nonneg.mpr hl.le)
    simpa [ne_of_gt hl] using hh
  · have hh := mul_le_mul_of_nonneg_left h.2 (inv_nonneg.mpr hl.le)
    calc
      l⁻¹ * dist (x i) (x j) ≤ l⁻¹ * ((1 + (1 : ℝ) / 1000) * l) := hh
      _ = 1 + (1 : ℝ) / 1000 := by field_simp

theorem shell_edge_bound {V : Type uV} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.CliqueFree 5) :
    8 * G.edgeFinset.card ≤ 3 * (Fintype.card V) ^ 2 := by
  obtain ⟨H, hdec, hmax⟩ := SimpleGraph.exists_isTuranMaximal (V := V) (r := 4) (by norm_num)
  let _ : DecidableRel H.Adj := hdec
  have hle := hmax.2 hG
  obtain ⟨e⟩ := (SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph
    (G := H) (by norm_num : 0 < 4)).mp hmax
  have heq := e.card_edgeFinset_eq
  have hb := SimpleGraph.mul_card_edgeFinset_turanGraph_le (n := Fintype.card V) (r := 4)
  rw [← heq] at hb
  norm_num at hb
  omega

theorem shellGraph_cliqueFree {V : Type uV} (x : V → Position) {l : ℝ} (hl : 0 < l) :
    (shellGraph x l).CliqueFree 5 := by
  classical
  intro s hs
  let e : Fin 5 ≃ s := (Finset.equivFinOfCardEq hs.card_eq).symm
  apply no_five_shell (fun i => x (e i)) hl
  intro i j hij
  have hne : (e i : V) ≠ (e j : V) := fun h => hij (e.injective (Subtype.ext h))
  have hh := hs.isClique (e i).property (e j).property hne
  exact hh.2

end Shell

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_BoundedCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem clamp01_nonneg (x : ℝ) : 0 ≤ clamp01 x := le_max_left _ _
theorem clamp01_le_one (x : ℝ) : clamp01 x ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)
theorem clamp01_eq_zero {x : ℝ} (hx : x ≤ 0) : clamp01 x = 0 := by
  exact max_eq_left (le_trans (min_le_right _ _) hx)
theorem clamp01_eq_one {x : ℝ} (hx : 1 ≤ x) : clamp01 x = 1 := by
  simp [clamp01, min_eq_left hx]
theorem continuous_clamp01 : Continuous clamp01 := by
  unfold clamp01
  fun_prop

theorem shellStep_pos (t : ℝ) : 0 < shellStep t := div_pos (microLength_pos t) (by norm_num)

theorem coreReal_nonneg (t r : ℝ) : 0 ≤ coreReal t r := by
  apply mul_nonneg (sq_nonneg t)
  apply le_min
  · linarith [clamp01_le_one ((r - microLength t) / shellStep t),
      clamp01_nonneg ((r - microLength t - 2 * shellStep t) / shellStep t)]
  · exact clamp01_nonneg _

theorem coreReal_le (t r : ℝ) : coreReal t r ≤ t ^ 2 := by
  have hh : min
      (1 - clamp01 ((r - microLength t) / shellStep t) +
        clamp01 ((r - microLength t - 2 * shellStep t) / shellStep t))
      (clamp01 (1 + t * (1 - r))) ≤ 1 :=
    (min_le_right _ _).trans (clamp01_le_one _)
  simpa only [coreReal, mul_one] using mul_le_mul_of_nonneg_left hh (sq_nonneg t)

theorem continuous_coreReal (t : ℝ) : Continuous (coreReal t) := by
  unfold coreReal
  exact continuous_const.mul
    (((continuous_const.sub (continuous_clamp01.comp
      ((continuous_id.sub continuous_const).div_const _))).add
      (continuous_clamp01.comp
        (((continuous_id.sub continuous_const).sub continuous_const).div_const _))).min
      (continuous_clamp01.comp
        (continuous_const.add (continuous_const.mul (continuous_const.sub continuous_id)))))

theorem coreReal_zero_outer {t r : ℝ} (ht : 0 < t) (hr : 1 + 1 / t ≤ r) :
    coreReal t r = 0 := by
  have hc : clamp01 (1 + t * (1 - r)) = 0 := by
    apply clamp01_eq_zero
    have hm := mul_le_mul_of_nonneg_left hr ht.le
    have hd := div_mul_cancel₀ (1 : ℝ) (ne_of_gt ht)
    nlinarith [hm, hd]
  have hs : 0 ≤ 1 - clamp01 ((r - microLength t) / shellStep t) +
      clamp01 ((r - microLength t - 2 * shellStep t) / shellStep t) := by
    linarith [clamp01_le_one ((r - microLength t) / shellStep t),
      clamp01_nonneg ((r - microLength t - 2 * shellStep t) / shellStep t)]
  simp only [coreReal, hc, min_eq_right hs, mul_zero]

theorem coreReal_full_left {t r : ℝ} (ht : 0 ≤ t)
    (hl : r ≤ microLength t) (hr : r ≤ 1) : coreReal t r = t ^ 2 := by
  have hd := shellStep_pos t
  have hdown : clamp01 ((r - microLength t) / shellStep t) = 0 :=
    clamp01_eq_zero (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)
  have hup : clamp01 ((r - microLength t - 2 * shellStep t) / shellStep t) = 0 :=
    clamp01_eq_zero (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)
  have hc : clamp01 (1 + t * (1 - r)) = 1 :=
    clamp01_eq_one (by nlinarith [mul_nonneg ht (sub_nonneg.mpr hr)])
  simp [coreReal, hdown, hup, hc]

theorem coreReal_full_right {t r : ℝ} (ht : 0 ≤ t)
    (hl : microLength t + 3 * shellStep t ≤ r) (hr : r ≤ 1) :
    coreReal t r = t ^ 2 := by
  have hd := shellStep_pos t
  have hdown : clamp01 ((r - microLength t) / shellStep t) = 1 :=
    clamp01_eq_one ((le_div_iff₀ hd).mpr (by linarith))
  have hup : clamp01 ((r - microLength t - 2 * shellStep t) / shellStep t) = 1 :=
    clamp01_eq_one ((le_div_iff₀ hd).mpr (by linarith))
  have hc : clamp01 (1 + t * (1 - r)) = 1 :=
    clamp01_eq_one (by nlinarith [mul_nonneg ht (sub_nonneg.mpr hr)])
  simp [coreReal, hdown, hup, hc]

theorem coreReal_full_of_not_shell {t r : ℝ} (ht : 0 ≤ t) (hr : r ≤ 1)
    (hs : ¬(microLength t ≤ r ∧ r ≤ (1 + (1 : ℝ) / 1000) * microLength t)) :
    coreReal t r = t ^ 2 := by
  by_cases hlo : microLength t ≤ r
  · apply coreReal_full_right ht ?_ hr
    have hhi : (1 + (1 : ℝ) / 1000) * microLength t < r :=
      lt_of_not_ge (fun hh => hs ⟨hlo, hh⟩)
    dsimp [shellStep]
    linarith [hhi]
  · exact coreReal_full_left ht (le_of_not_ge hlo) hr

theorem twice_pair_sum {N : ℕ} (F : Fin N → Fin N → ℝ)
    (hF : ∀ i j, F i j = F j i) :
    2 * (∑ i, ∑ j with i < j, F i j) =
      ∑ i, ∑ j, if i ≠ j then F i j else 0 := by
  classical
  simp only [Finset.sum_filter]
  have hswap : (∑ i, ∑ j, if j < i then F i j else 0) =
      ∑ i, ∑ j, if i < j then F i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hF j i]
  calc
    2 * (∑ i, ∑ j, if i < j then F i j else 0) =
      (∑ i, ∑ j, if i < j then F i j else 0) +
      (∑ i, ∑ j, if j < i then F i j else 0) := by rw [hswap]; ring
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rcases lt_trichotomy i j with h | h | h
      · simp [h, ne_of_lt h, not_lt_of_ge h.le]
      · simp [h]
      · simp [h, ne_of_gt h, not_lt_of_ge h.le]

theorem sum_adj_indicator {V : Type uV} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    (∑ i, ∑ j, if G.Adj i j then (1 : ℝ) else 0) = 2 * G.edgeFinset.card := by
  classical
  have hi (i : V) : (∑ j, if G.Adj i j then (1 : ℝ) else 0) = G.degree i := by
    rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
    simp
  simp_rw [hi]
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_RadialKernel
attribute [-instance] _root_.OAI.RadialTransition.instMeasurableSpaceParticleState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem rawBumpProfile_nonneg (r : ℝ) : 0 ≤ rawBumpProfile r :=
  Real.smoothTransition.nonneg _

theorem rawBumpProfile_le_one (r : ℝ) : rawBumpProfile r ≤ 1 :=
  Real.smoothTransition.le_one _

theorem continuous_rawBumpProfile : Continuous rawBumpProfile := by
  exact Real.smoothTransition.continuous.comp (by fun_prop)

theorem bumpIntegral_pos : 0 < bumpIntegral := by
  apply contDiff_rawBump.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    compactSupport_rawBump (fun x => rawBumpProfile_nonneg ‖x‖) (x := 0)
  simp [rawBump, rawBumpProfile, Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2)]

theorem bumpProfile_nonneg (r : ℝ) : 0 ≤ bumpProfile r :=
  div_nonneg (rawBumpProfile_nonneg r) bumpIntegral_pos.le

theorem bumpProfile_bound (r : ℝ) : |bumpProfile r| ≤ bumpIntegral⁻¹ := by
  rw [abs_of_nonneg (bumpProfile_nonneg r)]
  simpa [bumpProfile, one_div] using
    div_le_div_of_nonneg_right (rawBumpProfile_le_one r) bumpIntegral_pos.le

theorem bumpProfile_zero {r : ℝ} (hr : 1 ≤ r) : bumpProfile r = 0 := by
  rw [bumpProfile, rawBumpProfile_zero hr, zero_div]

theorem continuous_bumpProfile : Continuous bumpProfile :=
  continuous_rawBumpProfile.div_const _

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CellStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uV

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem symmetric_row_quadratic {I : Type uI} [Fintype I] (J : I → I → ℝ) (n : I → ℝ) (M : ℝ)
    (hJ : ∀ i j, 0 ≤ J i j) (hsymm : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ M) :
    ∑ i, ∑ j, J i j * n i * n j ≤ M * ∑ i, (n i) ^ 2 := by
  have ht (i j : I) : 2 * (J i j * n i * n j) ≤
      J i j * (n i ^ 2 + n j ^ 2) := by
    nlinarith [mul_nonneg (hJ i j) (sq_nonneg (n i - n j))]
  have hl := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => ht i j
  have hs : (∑ i, ∑ j, J i j * n j ^ 2) = ∑ i, ∑ j, J i j * n i ^ 2 := by
    rw [Finset.sum_comm]
    congr 1
    funext i
    congr 1
    funext j
    rw [hsymm]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hl
  rw [hs] at hl
  have hb : (∑ i, ∑ j, J i j * n i ^ 2) ≤ M * ∑ i, n i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
  linarith

theorem core_ordered_lower_small_diameter {V : Type uV} [Fintype V] [DecidableEq V] {t : ℝ} (ht : 0 ≤ t)
    (x : V → Position) (hx : ∀ i j, dist (x i) (x j) ≤ 1) :
    t ^ 2 / 4 * (Fintype.card V : ℝ) ^ 2 - t ^ 2 * Fintype.card V ≤
      ∑ i, ∑ j, if i ≠ j then coreReal t (dist (x i) (x j)) else 0 := by
  classical
  let G := shellGraph x (microLength t)
  have hG : G.CliqueFree 5 := shellGraph_cliqueFree x (microLength_pos t)
  have hbound : (8 : ℝ) * G.edgeFinset.card ≤ 3 * (Fintype.card V : ℝ) ^ 2 := by
    have hh : 8 * G.edgeFinset.card ≤ 3 * Fintype.card V ^ 2 := by
      simpa using shell_edge_bound G hG
    exact_mod_cast hh
  have hterm (i j : V) :
      t ^ 2 * ((if i ≠ j then (1 : ℝ) else 0) - (if G.Adj i j then 1 else 0)) ≤
      (if i ≠ j then coreReal t (dist (x i) (x j)) else 0) := by
    by_cases hij : i = j
    · subst j
      simp
    · simp only [ite_eq_left hij]
      by_cases hA : G.Adj i j
      · simp only [hA, ite_true, if_true, sub_self, mul_zero]
        exact coreReal_nonneg _ _
      · simp only [hA, ite_false, if_false, sub_zero, mul_one]
        rw [coreReal_full_of_not_shell ht (hx i j)]
        intro h
        exact hA ⟨hij, h⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hterm i j
  have hcount : (∑ i : V, ∑ j : V, if i ≠ j then (1 : ℝ) else 0) =
      (Fintype.card V : ℝ) ^ 2 - Fintype.card V := by
    have hite (i j : V) : (if i ≠ j then (1 : ℝ) else 0) =
        1 - (if i = j then 1 else 0) := by by_cases h : i = j <;> simp [h]
    simp_rw [hite]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, if_true]
    ring
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  rw [hcount, sum_adj_indicator G] at hsum
  have hb := mul_le_mul_of_nonneg_left hbound (sq_nonneg t)
  nlinarith [hsum, hb]

theorem sum_occupation {V : Type uV} {I : Type uI} [Fintype V] [Fintype I] (q : V → I) :
    ∑ i, occupation q i = Fintype.card V := by
  classical
  simpa [occupation] using Fintype.sum_fiberwise q (fun _ => (1 : ℝ))

theorem sum_subtype_le_of_nonneg {V : Type uV} [Fintype V] (p : V → Prop)
    (f : V → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (by classical exact ∑ a : {a // p a}, f a) ≤ ∑ a, f a := by
  classical
  have hh := Fintype.sum_subtype_add_sum_subtype p f
  have hz : 0 ≤ ∑ a : {a // ¬p a}, f a := Finset.sum_nonneg (fun a _ => hf a)
  linarith

theorem core_ordered_cells {V : Type uV} {I : Type uI} [Fintype V] [Fintype I] [DecidableEq V]
    {t : ℝ} (ht : 0 ≤ t) (q : V → I) (x : V → Position)
    (c : V → V → ℝ) (hc : ∀ a b, 0 ≤ c a b)
    (hsame : ∀ a b, q a = q b → c a b = 1)
    (hdiam : ∀ a b, q a = q b → dist (x a) (x b) ≤ 1) :
    t ^ 2 / 4 * (∑ i, occupation q i ^ 2) - t ^ 2 * Fintype.card V ≤
      ∑ a, ∑ b, if a ≠ b then c a b * coreReal t (dist (x a) (x b)) else 0 := by
  classical
  let F (a b : V) := if a ≠ b then c a b * coreReal t (dist (x a) (x b)) else 0
  have hF (a b : V) : 0 ≤ F a b := by
    exact ite_nonneg (mul_nonneg (hc a b) (coreReal_nonneg _ _)) le_rfl
  have hlocal (i : I) : t ^ 2 / 4 * occupation q i ^ 2 - t ^ 2 * occupation q i ≤
      ∑ a : {a // q a = i}, ∑ b, F a b := by
    have hl := core_ordered_lower_small_diameter ht (fun a : {a // q a = i} => x a)
      (fun a b => hdiam a b (a.property.trans b.property.symm))
    change t ^ 2 / 4 * occupation q i ^ 2 - t ^ 2 * occupation q i ≤ _ at hl
    apply hl.trans
    apply Finset.sum_le_sum
    intro a _
    have heq : (∑ b : {b // q b = i},
        if a ≠ b then coreReal t (dist (x a) (x b)) else 0) =
        ∑ b : {b // q b = i}, F a b := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : a = b
      · subst b; simp [F]
      · have hab' : (a : V) ≠ (b : V) := fun hh => hab (Subtype.ext hh)
        simp [F, hab, hab', hsame a b (a.property.trans b.property.symm)]
    rw [heq]
    exact sum_subtype_le_of_nonneg (fun b => q b = i) (F a) (hF a)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlocal i)
  rw [Fintype.sum_fiberwise q (fun a => ∑ b, F a b)] at hs
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_occupation] using hs

theorem sum_by_occupation {V : Type uV} {I : Type uI} [Fintype V] [Fintype I]
    (q : V → I) (f : I → ℝ) :
    (∑ a, f (q a)) = ∑ i, occupation q i * f i := by
  classical
  rw [← Fintype.sum_fiberwise q (fun a => f (q a))]
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun a : {a // q a = i} => f (q a)) = (fun _ => f i) := by
    funext a
    rw [a.property]
  rw [heq]
  simp [occupation]

theorem lifted_row_quadratic {V : Type uV} {I : Type uI} [Fintype V] [Fintype I]
    (q : V → I) (J : I → I → ℝ) {M : ℝ}
    (hJ : ∀ i j, 0 ≤ J i j) (hJsy : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ M) :
    (∑ a, ∑ b, J (q a) (q b)) ≤ M * ∑ i, occupation q i ^ 2 := by
  classical
  have heq : (∑ a, ∑ b, J (q a) (q b)) =
      ∑ i, ∑ j, J i j * occupation q i * occupation q j := by
    calc
      _ = ∑ a, ∑ j, occupation q j * J (q a) j := by
        apply Finset.sum_congr rfl
        intro a _
        exact sum_by_occupation q (J (q a))
      _ = ∑ i, occupation q i * ∑ j, occupation q j * J i j :=
        sum_by_occupation q (fun i => ∑ j, occupation q j * J i j)
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [heq]
  exact symmetric_row_quadratic J (occupation q) M hJ hJsy hrow

theorem modified_energy_cell_bound {N : ℕ} {I : Type uI} [Fintype I]
    {t M : ℝ} (ht : 0 ≤ t) (q : Fin N → I) (x : Fin N → Position)
    (c K : Fin N → Fin N → ℝ) (J : I → I → ℝ)
    (hc : ∀ a b, 0 ≤ c a b) (hcsy : ∀ a b, c a b = c b a)
    (hsame : ∀ a b, q a = q b → c a b = 1)
    (hdiam : ∀ a b, q a = q b → dist (x a) (x b) ≤ 1)
    (hK : ∀ a b, 0 ≤ K a b) (hKsy : ∀ a b, K a b = K b a)
    (hKJ : ∀ a b, K a b ≤ J (q a) (q b))
    (hJ : ∀ i j, 0 ≤ J i j) (hJsy : ∀ i j, J i j = J j i)
    (hrow : ∀ i, ∑ j, J i j ≤ M) :
    (t ^ 2 / 8 - M / 2) * (∑ i, occupation q i ^ 2) - t ^ 2 / 2 * N ≤
      ∑ a, ∑ b with a < b, (c a b * coreReal t (dist (x a) (x b)) - K a b) := by
  classical
  have hcore := core_ordered_cells ht q x c hc hsame hdiam
  have hrow' := lifted_row_quadratic q J hJ hJsy hrow
  have hatt : (∑ a, ∑ b, if a ≠ b then K a b else 0) ≤
      M * ∑ i, occupation q i ^ 2 := by
    apply le_trans ?_ hrow'
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    apply le_trans ?_ (hKJ a b)
    split_ifs
    · exact le_rfl
    · exact hK a b
  have hpair := twice_pair_sum
    (fun a b => c a b * coreReal t (dist (x a) (x b)) - K a b)
    (fun a b => by rw [hcsy a b, dist_comm (x a), hKsy a b])
  have heq : (∑ a, ∑ b, if a ≠ b then
      c a b * coreReal t (dist (x a) (x b)) - K a b else 0) =
      (∑ a, ∑ b, if a ≠ b then c a b * coreReal t (dist (x a) (x b)) else 0) -
      (∑ a, ∑ b, if a ≠ b then K a b else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a = b <;> simp [hab]
  rw [heq] at hpair
  simp only [Fintype.card_fin] at hcore
  nlinarith

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ScaledKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem scaledBumpProfile_nonneg {R : ℝ} (hR : 0 < R) (r : ℝ) :
    0 ≤ scaledBumpProfile R r :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hR.le 3)) (bumpProfile_nonneg _)

theorem scaledBumpProfile_bound {R : ℝ} (hR : 1 ≤ R) (r : ℝ) :
    |scaledBumpProfile R r| ≤ bumpIntegral⁻¹ := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  rw [abs_of_nonneg (scaledBumpProfile_nonneg hR0 r)]
  unfold scaledBumpProfile
  apply le_trans (mul_le_mul_of_nonneg_left
    ((le_abs_self _).trans (bumpProfile_bound (r / R)))
    (inv_nonneg.mpr (pow_nonneg hR0.le 3)))
  exact mul_le_of_le_one_left (inv_nonneg.mpr bumpIntegral_pos.le)
    (inv_le_one_of_one_le₀ (one_le_pow₀ hR))

theorem scaledBumpProfile_zero {R r : ℝ} (hR : 0 < R) (hr : R ≤ r) :
    scaledBumpProfile R r = 0 := by
  rw [scaledBumpProfile, bumpProfile_zero ((le_div_iff₀ hR).mpr (by simpa using hr)),
    mul_zero]

theorem continuous_scaledBumpProfile (R : ℝ) : Continuous (scaledBumpProfile R) :=
  continuous_const.mul (continuous_bumpProfile.comp (continuous_id.div_const _))

theorem attractionProfile_nonneg {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (r : ℝ) :
    0 ≤ attractionProfile a R r := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (ha n) (scaledBumpProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR n)) r)

theorem summable_attractionProfile {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (r : ℝ) :
    Summable (fun n => a n * scaledBumpProfile (R n) r) := by
  apply (hs.mul_right bumpIntegral⁻¹).of_nonneg_of_le
  · intro n
    exact mul_nonneg (ha n) (scaledBumpProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR n)) r)
  · intro n
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (scaledBumpProfile_bound (hR n) r)) (ha n)

theorem attractionProfile_bound {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (r : ℝ) :
    |attractionProfile a R r| ≤ (∑' n, a n) * bumpIntegral⁻¹ := by
  rw [abs_of_nonneg (attractionProfile_nonneg ha hR r)]
  unfold attractionProfile
  rw [← tsum_mul_right]
  exact Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (scaledBumpProfile_bound (hR n) r)) (ha n))
    (summable_attractionProfile ha hR hs r) (hs.mul_right _)

theorem continuous_attractionProfile {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) :
    Continuous (attractionProfile a R) := by
  apply continuous_tsum (fun n => continuous_const.mul (continuous_scaledBumpProfile (R n)))
    (hs.mul_right bumpIntegral⁻¹)
  intro n r
  change |a n * scaledBumpProfile (R n) r| ≤ a n * bumpIntegral⁻¹
  rw [abs_mul, abs_of_nonneg (ha n)]
  exact mul_le_mul_of_nonneg_left (scaledBumpProfile_bound (hR n) r) (ha n)

theorem continuous_familyPotential {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (t : ℝ) :
    Continuous (familyPotential t a R) := by
  exact ((continuous_coreReal t).sub (continuous_const.mul
    (continuous_attractionProfile ha hR hs))).comp NNReal.continuous_coe

theorem bounded_familyPotential {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (t : ℝ) :
    IsBoundedPotential (familyPotential t a R) := by
  refine ⟨t ^ 2 + |t| * ((∑' n, a n) * bumpIntegral⁻¹), ?_, ?_⟩
  · exact add_nonneg (sq_nonneg _) (mul_nonneg (abs_nonneg _)
      (mul_nonneg (tsum_nonneg ha) (inv_nonneg.mpr bumpIntegral_pos.le)))
  · intro r
    apply le_trans (abs_sub _ _)
    rw [abs_of_nonneg (coreReal_nonneg t r), abs_mul]
    exact add_le_add (coreReal_le t r)
      (mul_le_mul_of_nonneg_left (attractionProfile_bound ha hR hs r) (abs_nonneg t))

theorem familyPotential_nonpos_outer {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) {t : ℝ} (ht : 1 ≤ t)
    {r : ℝ≥0} (hr : 2 ≤ (r : ℝ)) : familyPotential t a R r ≤ 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hinv : 1 / t ≤ 1 := by simpa using inv_le_one_of_one_le₀ ht
  have hz := coreReal_zero_outer ht0 (show 1 + 1 / t ≤ (r : ℝ) by linarith)
  dsimp [familyPotential]
  rw [hz, zero_sub]
  exact neg_nonpos.mpr (mul_nonneg ht0.le (attractionProfile_nonneg ha hR r))

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_LatticeStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uV

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem mem_rangeCells (R : ℝ) (i j : Cell) : j ∈ rangeCells R i ↔ CellReach R i j := by
  simp only [rangeCells, Fintype.mem_piFinset, Finset.mem_Icc, CellReach, abs_le]
  constructor <;> intro h k <;> have hh := h k <;> constructor <;> omega

theorem cellReach_symm {R : ℝ} {i j : Cell} (h : CellReach R i j) : CellReach R j i := by
  intro k
  simpa only [abs_sub_comm] using h k

theorem cellMargin_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ cellMargin R := by
  have hh := Int.le_ceil (4 * R)
  have : (0 : ℝ) ≤ (cellMargin R : ℝ) := by dsimp [cellMargin]; push_cast; linarith
  exact_mod_cast this

theorem card_rangeCells {R : ℝ} (hR : 1 ≤ R) (i : Cell) :
    ((rangeCells R i).card : ℝ) ≤ 2197 * R ^ 3 := by
  have hm := cellMargin_nonneg (le_trans zero_le_one hR)
  have hm1 : 0 ≤ 2 * cellMargin R + 1 := by omega
  have heq : (rangeCells R i).card = (2 * cellMargin R + 1).toNat ^ 3 := by
    simp only [rangeCells, Fintype.card_piFinset, Int.card_Icc]
    simp_rw [show ∀ k, i k + cellMargin R + 1 - (i k - cellMargin R) =
        2 * cellMargin R + 1 by intro k; ring]
    simp
  rw [heq]
  have hcast : (((2 * cellMargin R + 1).toNat : ℕ) : ℝ) = 2 * (cellMargin R : ℝ) + 1 := by
    have hh := Int.toNat_of_nonneg hm1
    exact_mod_cast hh
  push_cast
  rw [hcast]
  have hb : 2 * (cellMargin R : ℝ) + 1 ≤ 13 * R := by
    have hc := Int.ceil_lt_add_one (4 * R)
    dsimp [cellMargin]
    push_cast
    linarith
  calc
    _ ≤ (13 * R) ^ 3 := pow_le_pow_left₀ (by exact_mod_cast hm1) hb 3
    _ = _ := by ring

theorem cellReach_of_dist {x y : Position} {R : ℝ} (hxy : dist x y ≤ R) :
    CellReach R (cellOf x) (cellOf y) := by
  intro k
  have hc : |x k - y k| ≤ R := by
    simpa only [Real.dist_eq] using (PiLp.dist_apply_le x y k).trans hxy
  have hxl := Int.floor_le (4 * x k)
  have hyl := Int.floor_le (4 * y k)
  have hxu := Int.lt_floor_add_one (4 * x k)
  have hyu := Int.lt_floor_add_one (4 * y k)
  have hceil := Int.le_ceil (4 * R)
  have hb : |((⌊4 * y k⌋ : ℤ) : ℝ) - (⌊4 * x k⌋ : ℤ)| ≤ (⌈4 * R⌉ : ℤ) + (1 : ℝ) := by
    rcases abs_le.mp hc with ⟨hc1, hc2⟩
    apply abs_le.mpr
    constructor <;> linarith
  dsimp [cellOf, cellMargin]
  exact_mod_cast hb

theorem cellMajorant_nonneg {R W : ℝ} (hR : 0 ≤ R) (hW : 0 ≤ W) (i j : Cell) :
    0 ≤ cellMajorant R W i j :=
  ite_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg hR _)) hW) le_rfl

theorem cellMajorant_symm (R W : ℝ) (i j : Cell) :
    cellMajorant R W i j = cellMajorant R W j i := by
  unfold cellMajorant
  have hh : CellReach R i j ↔ CellReach R j i := ⟨cellReach_symm, cellReach_symm⟩
  by_cases h : CellReach R i j
  · simp [h, hh.mp h]
  · simp [h, show ¬ CellReach R j i from fun hji => h (hh.mpr hji)]

theorem cellMajorant_row {I : Type uI} [Fintype I]
    (e : I → Cell) (he : Function.Injective e) {R W : ℝ} (hR : 1 ≤ R) (hW : 0 ≤ W)
    (i : Cell) : ∑ j, cellMajorant R W i (e j) ≤ 2197 * W := by
  classical
  let s := Finset.univ.filter (fun j => CellReach R i (e j))
  have hcard : s.card ≤ (rangeCells R i).card := by
    apply Finset.card_le_card_of_injOn e
    · intro j hj
      exact (mem_rangeCells R i (e j)).mpr (Finset.mem_filter.mp hj).2
    · exact he.injOn
  have hsum : (∑ j, cellMajorant R W i (e j)) = (s.card : ℝ) * ((R ^ 3)⁻¹ * W) := by
    simp [cellMajorant, s, ← Finset.sum_filter]
  rw [hsum]
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hc : (s.card : ℝ) ≤ 2197 * R ^ 3 :=
    (by exact_mod_cast hcard : (s.card : ℝ) ≤ (rangeCells R i).card).trans (card_rangeCells hR i)
  calc
    _ ≤ (2197 * R ^ 3) * ((R ^ 3)⁻¹ * W) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg (inv_nonneg.mpr (pow_nonneg hR0.le _)) hW)
    _ = _ := by field_simp

theorem same_cell_diameter {x y : Position} (h : cellOf x = cellOf y) :
    dist x y ≤ 1 := by
  have hc (k : Fin 3) : |x k - y k| ≤ 1 / 4 := by
    have hh : ⌊4 * x k⌋ = ⌊4 * y k⌋ := congrFun h k
    have hxl := Int.floor_le (4 * x k)
    have hxu := Int.lt_floor_add_one (4 * x k)
    have hyl := Int.floor_le (4 * y k)
    have hyu := Int.lt_floor_add_one (4 * y k)
    rw [← hh] at hyl hyu
    apply abs_le.mpr
    constructor <;> linarith
  have hs : dist x y ^ 2 ≤ 3 * (1 / 4 : ℝ) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    calc
      _ ≤ ∑ k : Fin 3, (1 / 4 : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        simpa only [Real.dist_eq] using pow_le_pow_left₀ (abs_nonneg _) (hc k) 2
      _ = _ := by simp
  nlinarith [dist_nonneg (x := x) (y := y)]

theorem scaledBumpProfile_le_cellMajorant {R : ℝ} (hR : 1 ≤ R) (x y : Position) :
    scaledBumpProfile R (dist x y) ≤ cellMajorant R bumpIntegral⁻¹ (cellOf x) (cellOf y) := by
  have hR0 := lt_of_lt_of_le zero_lt_one hR
  by_cases h : CellReach R (cellOf x) (cellOf y)
  · simp only [cellMajorant, ite_eq_left h, scaledBumpProfile]
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (bumpProfile_bound _))
      (inv_nonneg.mpr (pow_nonneg hR0.le _))
  · have hd : R ≤ dist x y := le_of_not_ge (fun hh => h (cellReach_of_dist hh))
    simp [cellMajorant, h, scaledBumpProfile_zero hR0 hd]

theorem summable_cellMajorant {a R : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (i j : Cell) :
    Summable (fun n => a n * cellMajorant (R n) bumpIntegral⁻¹ i j) := by
  apply (hs.mul_right bumpIntegral⁻¹).of_nonneg_of_le
  · intro n
    exact mul_nonneg (ha n) (cellMajorant_nonneg (zero_le_one.trans (hR n))
      (inv_nonneg.mpr bumpIntegral_pos.le) i j)
  · intro n
    apply mul_le_mul_of_nonneg_left ?_ (ha n)
    unfold cellMajorant
    split_ifs
    · exact mul_le_of_le_one_left (inv_nonneg.mpr bumpIntegral_pos.le)
        (inv_le_one_of_one_le₀ (one_le_pow₀ (hR n)))
    · exact inv_nonneg.mpr bumpIntegral_pos.le

theorem familyCellMajorant_nonneg {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (i j : Cell) :
    0 ≤ familyCellMajorant t a R i j := by
  apply mul_nonneg ht (tsum_nonneg _)
  intro n
  exact mul_nonneg (ha n) (cellMajorant_nonneg (zero_le_one.trans (hR n))
    (inv_nonneg.mpr bumpIntegral_pos.le) i j)

theorem familyCellMajorant_symm (t : ℝ) (a R : ℕ → ℝ) (i j : Cell) :
    familyCellMajorant t a R i j = familyCellMajorant t a R j i := by
  unfold familyCellMajorant
  congr 1
  apply tsum_congr
  intro n
  rw [cellMajorant_symm]

theorem familyCellMajorant_row {I : Type uI} [Fintype I] (e : I → Cell)
    (he : Function.Injective e) {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (i : Cell) :
    ∑ j, familyCellMajorant t a R i (e j) ≤ 2197 * t * bumpIntegral⁻¹ * ∑' n, a n := by
  simp only [familyCellMajorant, ← Finset.mul_sum]
  have hswap : (∑ j, ∑' n, a n * cellMajorant (R n) bumpIntegral⁻¹ i (e j)) =
      ∑' n, a n * ∑ j, cellMajorant (R n) bumpIntegral⁻¹ i (e j) := by
    rw [← Summable.tsum_finsetSum (fun j _ => summable_cellMajorant ha hR hs i (e j))]
    simp_rw [Finset.mul_sum]
  rw [hswap]
  calc
    _ ≤ t * ∑' n, a n * (2197 * bumpIntegral⁻¹) := by
      apply mul_le_mul_of_nonneg_left ?_ ht
      apply Summable.tsum_le_tsum
      · intro n
        exact mul_le_mul_of_nonneg_left
          (cellMajorant_row e he (hR n) (inv_nonneg.mpr bumpIntegral_pos.le) i) (ha n)
      · simpa only [Finset.mul_sum] using
          summable_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
            summable_cellMajorant ha hR hs i (e j))
      · exact hs.mul_right _
    _ = _ := by rw [tsum_mul_right]; ring

theorem attraction_le_familyCellMajorant {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) (x y : Position) :
    t * attractionProfile a R (dist x y) ≤ familyCellMajorant t a R (cellOf x) (cellOf y) := by
  apply mul_le_mul_of_nonneg_left ?_ ht
  exact Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (scaledBumpProfile_le_cellMajorant (hR n) x y) (ha n))
    (summable_attractionProfile ha hR hs _) (summable_cellMajorant ha hR hs _ _)

theorem family_energy_cell_bound {I : Type uI} [Fintype I] {N : ℕ}
    (e : I → Cell) (he : Function.Injective e) (q : Fin N → I) (x : Fin N → Position)
    (hq : ∀ j, e (q j) = cellOf (x j)) {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a) :
    (t ^ 2 / 8 - (2197 * t * bumpIntegral⁻¹ * ∑' n, a n) / 2) *
        (∑ i, occupation q i ^ 2) - t ^ 2 / 2 * N ≤ energy (familyPotential t a R) x := by
  have hh := modified_energy_cell_bound ht q x (fun _ _ => 1)
    (fun i j => t * attractionProfile a R (dist (x i) (x j)))
    (fun i j => familyCellMajorant t a R (e i) (e j))
    (fun _ _ => zero_le_one) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun i j hij => same_cell_diameter (by rw [← hq i, ← hq j, hij]))
    (fun i j => mul_nonneg ht (attractionProfile_nonneg ha hR _))
    (fun i j => by rw [dist_comm (x i) (x j)])
    (fun i j => by simpa only [hq] using attraction_le_familyCellMajorant ht ha hR hs (x i) (x j))
    (fun i j => familyCellMajorant_nonneg ht ha hR (e i) (e j))
    (fun i j => familyCellMajorant_symm t a R (e i) (e j))
    (fun i => familyCellMajorant_row e he ht ha hR hs (e i))
  simpa only [one_mul, energy, familyPotential, coe_nndist] using hh

theorem stable_familyPotential {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a)
    (hcoerc : 2197 * t * bumpIntegral⁻¹ * (∑' n, a n) / 2 ≤ t ^ 2 / 8) :
    StableWith (familyPotential t a R) (t ^ 2 / 2) := by
  classical
  intro N x
  let S : Finset Cell := Finset.univ.image (fun j => cellOf (x j))
  let q : Fin N → S := fun j => ⟨cellOf (x j), Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  have hh := family_energy_cell_bound (fun i : S => (i : Cell)) Subtype.val_injective q x
    (fun _ => rfl) ht ha hR hs
  have hn : 0 ≤ (t ^ 2 / 8 - (2197 * t * bumpIntegral⁻¹ * ∑' n, a n) / 2) *
      (∑ i, occupation q i ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hcoerc) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  change -(t ^ 2 / 2 * (N : ℝ)) ≤ _
  linarith

theorem cellOf_mem_cubeCells {L : ℝ} {x : Position} (hx : x ∈ cube L) :
    cellOf x ∈ cubeCells L := by
  simp only [cubeCells, Fintype.mem_piFinset, Finset.mem_Icc, cellOf]
  intro k
  exact ⟨Int.floor_nonneg.mpr (by linarith [(hx k).1]), Int.floor_mono (by linarith [(hx k).2])⟩

theorem card_cubeCells {L : ℝ} (hL : 1 ≤ L) :
    ((cubeCells L).card : ℝ) ≤ 216 * L ^ 3 := by
  have hf : 0 ≤ ⌊4 * L⌋ := Int.floor_nonneg.mpr (by linarith)
  have heq : (cubeCells L).card = (⌊4 * L⌋ + 1).toNat ^ 3 := by
    simp [cubeCells, Fintype.card_piFinset, Int.card_Icc]
  rw [heq]
  have hc : (((⌊4 * L⌋ + 1).toNat : ℕ) : ℝ) = (⌊4 * L⌋ : ℝ) + 1 := by
    exact_mod_cast (Int.toNat_of_nonneg (show 0 ≤ ⌊4 * L⌋ + 1 by omega))
  push_cast
  rw [hc]
  have hb : (⌊4 * L⌋ : ℝ) + 1 ≤ 6 * L := by
    have hh := Int.floor_le (4 * L)
    linarith
  calc
    _ ≤ (6 * L) ^ 3 := pow_le_pow_left₀ (by exact_mod_cast (show 0 ≤ ⌊4 * L⌋ + 1 by omega)) hb 3
    _ = _ := by ring

theorem square_count_le_card_occupation {V : Type uV} {I : Type uI} [Fintype V] [Fintype I]
    (q : V → I) : (Fintype.card V : ℝ) ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, occupation q i ^ 2 := by
  rw [← sum_occupation q]
  simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := occupation q)

theorem family_density_stability {t L : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t) (hL : 1 ≤ L)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a)
    (hcoerc : 2197 * t * bumpIntegral⁻¹ * (∑' n, a n) / 2 ≤ t ^ 2 / 16)
    {N : ℕ} (x : Fin N → Position) (hx : x ∈ configurationCube L N) :
    t ^ 2 / 3456 * (N : ℝ) ^ 2 / L ^ 3 - t ^ 2 / 2 * N ≤ energy (familyPotential t a R) x := by
  classical
  let S := cubeCells L
  let q : Fin N → S := fun j => ⟨cellOf (x j), cellOf_mem_cubeCells (hx j)⟩
  have hh := family_energy_cell_bound (fun i : S => (i : Cell)) Subtype.val_injective q x
    (fun _ => rfl) ht ha hR hs
  have hsum : 0 ≤ ∑ i, occupation q i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hn := square_count_le_card_occupation q
  have hcard : (Fintype.card S : ℝ) ≤ 216 * L ^ 3 := by
    simpa using card_cubeCells hL
  have hn' := hn.trans (mul_le_mul_of_nonneg_right hcard hsum)
  have hL0 : 0 < L ^ 3 := pow_pos (lt_of_lt_of_le zero_lt_one hL) _
  have hocc : (N : ℝ) ^ 2 / (216 * L ^ 3) ≤ ∑ i, occupation q i ^ 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hL0)).mpr
    simpa only [Fintype.card_fin, mul_comm] using hn'
  have hocc' := mul_le_mul_of_nonneg_left hocc (show 0 ≤ t ^ 2 / 16 by positivity)
  have heq : t ^ 2 / 16 * ((N : ℝ) ^ 2 / (216 * L ^ 3)) =
      t ^ 2 / 3456 * (N : ℝ) ^ 2 / L ^ 3 := by ring
  rw [heq] at hocc'
  nlinarith [mul_nonneg (show 0 ≤ t ^ 2 / 16 - 2197 * t * bumpIntegral⁻¹ * (∑' n, a n) / 2 by linarith) hsum]

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_FinitePartition
attribute [-instance] _root_.OAI.RadialTransition.instMeasurableSpaceParticleState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uIndex

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem isClosed_cube (L : ℝ) : IsClosed (cube L) := by
  have heq : cube L = ⋂ k : Fin 3, {x : Position | x k ∈ Icc 0 L} := by
    ext x
    simp only [cube, mem_ofPred_eq, mem_iInter, mem_Icc]
  rw [heq]
  exact isClosed_iInter (fun k : Fin 3 =>
    isClosed_Icc.preimage (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k))

theorem measurableSet_cube (L : ℝ) : MeasurableSet (cube L) :=
  (isClosed_cube L).measurableSet

theorem volume_cube (L : ℝ) : volume (cube L) = ENNReal.ofReal L ^ 3 := by
  have heq : cube L = WithLp.ofLp ⁻¹' (Set.univ.pi fun _ : Fin 3 => Icc (0 : ℝ) L) := by
    ext x
    simp only [cube, mem_ofPred_eq, mem_preimage, Set.mem_pi, mem_univ, true_implies, mem_Icc]
  rw [heq, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (MeasurableSet.univ_pi (fun _ : Fin 3 => measurableSet_Icc)).nullMeasurableSet]
  rw [volume_pi, Measure.pi_pi]
  simp only [Real.volume_Icc, sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem measurableSet_configurationCube (L : ℝ) (N : ℕ) :
    MeasurableSet (configurationCube L N) := by
  have heq : configurationCube L N = Set.univ.pi (fun _ : Fin N => cube L) := by
    ext x
    simp only [configurationCube, mem_ofPred_eq, Set.mem_pi, mem_univ, true_implies]
  rw [heq]
  exact MeasurableSet.univ_pi (fun _ : Fin N => measurableSet_cube L)

theorem volume_configurationCube (L : ℝ) (N : ℕ) :
    volume (configurationCube L N) = ENNReal.ofReal L ^ (3 * N) := by
  have heq : configurationCube L N = Set.univ.pi (fun _ : Fin N => cube L) := by
    ext x
    simp only [configurationCube, mem_ofPred_eq, Set.mem_pi, mem_univ, true_implies]
  rw [heq, volume_pi]
  rw [Measure.pi_pi]
  simp [volume_cube, ← pow_mul]

theorem continuous_energy {φ : Potential} (hφ : Continuous φ) (N : ℕ) :
    Continuous (energy φ (N := N)) := by
  unfold energy
  exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _
    (fun j _ => hφ.comp ((continuous_apply i).nndist (continuous_apply j))))

theorem energy_abs_bound {φ : Potential} {M : ℝ} (hM : 0 ≤ M)
    (hφ : ∀ r : ℝ≥0, |φ r| ≤ M) {N : ℕ} (x : Fin N → Position) :
    |energy φ x| ≤ (N : ℝ) ^ 2 * M := by
  calc
    _ ≤ ∑ i : Fin N, ∑ j : Fin N with i < j, |φ (nndist (x i) (x j))| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, M := by
      apply Finset.sum_le_sum
      intro i _
      apply le_trans (Finset.sum_le_sum (fun j _ => hφ _))
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => hM)
    _ = _ := by simp; ring

theorem integrableOn_boltzmann {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) (L : ℝ) (N : ℕ) (β : ℝ) :
    IntegrableOn (fun x : Fin N → Position => Real.exp (-β * energy φ x))
      (configurationCube L N) := by
  obtain ⟨M, hM, hφM⟩ := hb
  have hfinite : volume (configurationCube L N) < ⊤ := by
    rw [volume_configurationCube]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  apply IntegrableOn.of_bound hfinite ((Real.continuous_exp.comp
    (continuous_const.mul (continuous_energy hφ N))).stronglyMeasurable.aestronglyMeasurable) (Real.exp (|β| * ((N : ℝ) ^ 2 * M)))
  filter_upwards [] with x
  change |Real.exp (-β * energy φ x)| ≤ _
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    -β * energy φ x ≤ |-β * energy φ x| := le_abs_self _
    _ = |β| * |energy φ x| := by rw [abs_mul, abs_neg]
    _ ≤ _ := mul_le_mul_of_nonneg_left (energy_abs_bound hM hφM x) (abs_nonneg _)

theorem partition_pos {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {L : ℝ} (hL : 0 < L) (N : ℕ) (β : ℝ) : 0 < partition φ L N β := by
  unfold partition
  apply mul_pos (inv_pos.mpr (by exact_mod_cast Nat.factorial_pos N))
  apply (integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos (-β * energy φ x)).le))
    (integrableOn_boltzmann hφ hb L N β)).mpr
  have heq : Function.support (fun x : Fin N → Position => Real.exp (-β * energy φ x)) = univ := by
    ext x
    simp [Function.mem_support]
  rw [heq, Measure.restrict_apply_univ]
  rw [volume_configurationCube]
  exact pos_iff_ne_zero.mpr (pow_ne_zero _ ((ENNReal.ofReal_pos.mpr hL).ne'))

theorem log_integral_exp_convex_mix {X : Type uX} [MeasurableSpace X] {μ : Measure X}
    {F G : X → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hF : Integrable (fun x => Real.exp (F x)) μ)
    (hG : Integrable (fun x => Real.exp (G x)) μ)
    (hH : Integrable (fun x => Real.exp (a * F x + b * G x)) μ)
    (hZF : 0 < ∫ x, Real.exp (F x) ∂μ) (hZG : 0 < ∫ x, Real.exp (G x) ∂μ)
    (hZH : 0 < ∫ x, Real.exp (a * F x + b * G x) ∂μ) :
    Real.log (∫ x, Real.exp (a * F x + b * G x) ∂μ) ≤
      a * Real.log (∫ x, Real.exp (F x) ∂μ) + b * Real.log (∫ x, Real.exp (G x) ∂μ) := by
  let c := a * Real.log (∫ x, Real.exp (F x) ∂μ) + b * Real.log (∫ x, Real.exp (G x) ∂μ)
  have hpoint (x : X) : Real.exp (-c) * Real.exp (a * F x + b * G x) ≤
      a * ((∫ x, Real.exp (F x) ∂μ)⁻¹ * Real.exp (F x)) +
      b * ((∫ x, Real.exp (G x) ∂μ)⁻¹ * Real.exp (G x)) := by
    have hh := convexOn_exp.2 (mem_univ (F x - Real.log (∫ x, Real.exp (F x) ∂μ)))
      (mem_univ (G x - Real.log (∫ x, Real.exp (G x) ∂μ))) ha hb hab
    simp only [smul_eq_mul] at hh
    have heq : a * (F x - Real.log (∫ x, Real.exp (F x) ∂μ)) +
        b * (G x - Real.log (∫ x, Real.exp (G x) ∂μ)) = -c + (a * F x + b * G x) := by
      dsimp [c]; ring
    rw [heq, Real.exp_add, Real.exp_sub, Real.exp_sub, Real.exp_log hZF, Real.exp_log hZG] at hh
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have hi := integral_mono (hH.const_mul _) ((hF.const_mul _).const_mul a |>.add
      ((hG.const_mul _).const_mul b)) hpoint
  simp only [Pi.add_apply, integral_add ((hF.const_mul _).const_mul a) ((hG.const_mul _).const_mul b),
    integral_const_mul, inv_mul_cancel₀ hZF.ne', inv_mul_cancel₀ hZG.ne', mul_one, hab] at hi
  have hexp := Real.log_le_log (mul_pos (Real.exp_pos (-c)) hZH) hi
  rw [Real.log_mul (Real.exp_ne_zero _) hZH.ne', Real.log_exp, Real.log_one] at hexp
  change _ ≤ c
  linarith

theorem integral_const_configurationCube {L : ℝ} (hL : 0 ≤ L) (N : ℕ) (c : ℝ) :
    (∫ _x : Fin N → Position in configurationCube L N, c) = L ^ (3 * N) * c := by
  rw [setIntegral_const, Measure.real, volume_configurationCube, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hL]
  rfl

theorem partition_zero (φ : Potential) (L β : ℝ) : partition φ L 0 β = 1 := by
  have heq : (fun x : Fin 0 → Position => Real.exp (-β * energy φ x)) = fun _ => (1 : ℝ) := by
    funext x
    simp [energy]
  unfold partition
  rw [heq, setIntegral_const, Measure.real, volume_configurationCube]
  simp

theorem partition_nonneg {φ : Potential} (L : ℝ) (N : ℕ) (β : ℝ) :
    0 ≤ partition φ L N β := by
  exact mul_nonneg (by positivity) (integral_nonneg fun x => (Real.exp_pos _).le)

theorem partition_upper_of_energy_lower {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {L β E : ℝ} (hL : 0 ≤ L) (hβ : 0 ≤ β) (N : ℕ)
    (hE : ∀ x ∈ configurationCube L N, E ≤ energy φ x) :
    partition φ L N β ≤ (N.factorial : ℝ)⁻¹ * L ^ (3 * N) * Real.exp (-β * E) := by
  have hfinite : volume (configurationCube L N) ≠ ⊤ := by
    simp [volume_configurationCube]
  have hconst : IntegrableOn (fun _ : Fin N → Position => Real.exp (-β * E))
      (configurationCube L N) := integrableOn_const hfinite
  have hc := setIntegral_mono_on (integrableOn_boltzmann hφ hb L N β) hconst
    (measurableSet_configurationCube L N) (fun x hx =>
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hE x hx) (neg_nonpos.mpr hβ)))
  rw [integral_const_configurationCube hL] at hc
  exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (mul_assoc _ _ _).symm

theorem partition_stability_upper {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B L β : ℝ} (hstable : StableWith φ B)
    (hL : 0 ≤ L) (hβ : 0 ≤ β) (N : ℕ) :
    partition φ L N β ≤ (L ^ 3 * Real.exp (β * B)) ^ N / N.factorial := by
  have hh := partition_upper_of_energy_lower hφ hb hL hβ N (fun x _ => hstable N x)
  have heq : (N.factorial : ℝ)⁻¹ * L ^ (3 * N) * Real.exp (-β * (-(B * N))) =
      (L ^ 3 * Real.exp (β * B)) ^ N / N.factorial := by
    rw [mul_pow, ← pow_mul, ← Real.exp_nat_mul]
    have he : -β * -(B * (N : ℝ)) = (N : ℝ) * (β * B) := by ring
    rw [he]
    ring
  exact hh.trans_eq heq

theorem log_partition_upper_of_energy_lower {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {L β E : ℝ} (hL : 0 < L) (hβ : 0 ≤ β) (N : ℕ)
    (hE : ∀ x ∈ configurationCube L N, E ≤ energy φ x) :
    Real.log (partition φ L N β) ≤
      (N : ℝ) * Real.log (L ^ 3) - Real.log (N.factorial : ℝ) - β * E := by
  have hh := Real.log_le_log (partition_pos hφ hb hL N β)
    (partition_upper_of_energy_lower hφ hb hL.le hβ N hE)
  have hfac : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  rw [Real.log_mul (mul_ne_zero (inv_ne_zero hfac) (pow_ne_zero _ hL.ne')) (Real.exp_ne_zero _),
    Real.log_mul (inv_ne_zero hfac) (pow_ne_zero _ hL.ne'), Real.log_inv,
    Real.log_pow, Real.log_exp] at hh
  rw [Real.log_pow]

  push_cast at hh
  norm_num only [Nat.cast_ofNat] at *
  nlinarith

theorem boltzmannIntegral_pos {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {L : ℝ} (hL : 0 < L) (N : ℕ) (β : ℝ) :
    0 < ∫ x in configurationCube L N, Real.exp (-β * energy φ x) := by
  have hp := partition_pos hφ hb hL N β
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr (by exact_mod_cast Nat.factorial_pos N))).mp hp

theorem log_partition_convex_mix {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {L a b : ℝ} (hL : 0 < L) (N : ℕ) (β γ : ℝ)
    (ha : 0 ≤ a) (hbb : 0 ≤ b) (hab : a + b = 1) :
    Real.log (partition φ L N (a * β + b * γ)) ≤
      a * Real.log (partition φ L N β) + b * Real.log (partition φ L N γ) := by
  have heq (x : Fin N → Position) : a * (-β * energy φ x) + b * (-γ * energy φ x) =
      -(a * β + b * γ) * energy φ x := by ring
  have hc := log_integral_exp_convex_mix (F := fun x : Fin N → Position => -β * energy φ x)
    (G := fun x => -γ * energy φ x) (μ := volume.restrict (configurationCube L N)) ha hbb hab
    (integrableOn_boltzmann hφ hb L N β) (integrableOn_boltzmann hφ hb L N γ)
    (by simp_rw [heq]; exact integrableOn_boltzmann hφ hb L N _) (boltzmannIntegral_pos hφ hb hL N β)
    (boltzmannIntegral_pos hφ hb hL N γ) (by simp_rw [heq]; exact boltzmannIntegral_pos hφ hb hL N _)
  simp_rw [heq] at hc
  have hfac : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  simp only [partition, Real.log_mul (inv_ne_zero hfac)
    (boltzmannIntegral_pos hφ hb hL N _).ne']
  have haff := congrArg (fun z : ℝ => z * Real.log (N.factorial : ℝ)⁻¹) hab
  nlinarith [haff]

theorem grandTerm_stability_upper {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B L β : ℝ} (hstable : StableWith φ B)
    (hL : 0 ≤ L) (hβ : 0 ≤ β) (t h : ℝ) (N : ℕ) :
    Real.exp (t * h * N) * partition φ L N β ≤
      (L ^ 3 * Real.exp (β * B + t * h)) ^ N / N.factorial := by
  have hh := mul_le_mul_of_nonneg_left (partition_stability_upper hφ hb hstable hL hβ N)
    (Real.exp_pos (t * h * N)).le
  apply hh.trans_eq
  rw [Real.exp_add, mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul (β * B) N,
    ← Real.exp_nat_mul (t * h) N]
  have he : t * h * (N : ℝ) = (N : ℝ) * (t * h) := by ring
  rw [he]
  ring

theorem grandPartition_summable {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B L β : ℝ} (hstable : StableWith φ B)
    (hL : 0 ≤ L) (hβ : 0 ≤ β) (t h : ℝ) :
    Summable (fun N : ℕ => Real.exp (t * h * N) * partition φ L N β) :=
  Summable.of_nonneg_of_le
    (fun N => mul_nonneg (Real.exp_pos _).le (partition_nonneg L N β))
    (grandTerm_stability_upper hφ hb hstable hL hβ t h)
    (Real.summable_pow_div_factorial _)

theorem grandPartition_bounds {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B L β : ℝ} (hstable : StableWith φ B)
    (hL : 0 ≤ L) (hβ : 0 ≤ β) (t h : ℝ) :
    1 ≤ grandPartition φ t L β h ∧
      grandPartition φ t L β h ≤ Real.exp (L ^ 3 * Real.exp (β * B + t * h)) := by
  have hs := grandPartition_summable hφ hb hstable hL hβ t h
  constructor
  · have hh := hs.le_tsum 0 (fun N _ => mul_nonneg (Real.exp_pos _).le (partition_nonneg L N β))
    convert hh using 1 <;> first | rfl | norm_num [partition_zero]
  · have hh := hs.tsum_le_tsum (grandTerm_stability_upper hφ hb hstable hL hβ t h)
      (Real.summable_pow_div_factorial _)
    have he : (∑' N : ℕ, (L ^ 3 * Real.exp (β * B + t * h)) ^ N / N.factorial) =
        Real.exp (L ^ 3 * Real.exp (β * B + t * h)) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    exact hh.trans_eq he

theorem log_tsum_convex_mix {T U V : ℕ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hT : Summable T) (hU : Summable U) (hV : Summable V)
    (hpT : ∀ n, 0 < T n) (hpU : ∀ n, 0 < U n) (hpV : ∀ n, 0 < V n)
    (hlog : ∀ n, Real.log (T n) ≤ a * Real.log (U n) + b * Real.log (V n)) :
    Real.log (∑' n, T n) ≤ a * Real.log (∑' n, U n) + b * Real.log (∑' n, V n) := by
  have hsT : 0 < ∑' n, T n := lt_of_lt_of_le (hpT 0) (hT.le_tsum 0 (fun n _ => (hpT n).le))
  have hsU : 0 < ∑' n, U n := lt_of_lt_of_le (hpU 0) (hU.le_tsum 0 (fun n _ => (hpU n).le))
  have hsV : 0 < ∑' n, V n := lt_of_lt_of_le (hpV 0) (hV.le_tsum 0 (fun n _ => (hpV n).le))
  let c := a * Real.log (∑' n, U n) + b * Real.log (∑' n, V n)
  have hpoint (n : ℕ) : Real.exp (-c) * T n ≤
      a * ((∑' n, U n)⁻¹ * U n) + b * ((∑' n, V n)⁻¹ * V n) := by
    have hcv := convexOn_exp.2 (mem_univ (Real.log (U n) - Real.log (∑' n, U n)))
      (mem_univ (Real.log (V n) - Real.log (∑' n, V n))) ha hb hab
    simp only [smul_eq_mul] at hcv
    have he : a * (Real.log (U n) - Real.log (∑' n, U n)) +
        b * (Real.log (V n) - Real.log (∑' n, V n)) =
        -c + (a * Real.log (U n) + b * Real.log (V n)) := by dsimp [c]; ring
    rw [he, Real.exp_add, Real.exp_sub, Real.exp_sub, Real.exp_log (hpU n),
      Real.exp_log (hpV n), Real.exp_log hsU, Real.exp_log hsV] at hcv
    have hh := Real.exp_le_exp.mpr (hlog n)
    rw [Real.exp_log (hpT n)] at hh
    apply (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le).trans
    simpa only [div_eq_mul_inv, mul_comm] using hcv
  have hh := (hT.mul_left (Real.exp (-c))).tsum_le_tsum hpoint
    ((hU.mul_left _).mul_left a |>.add ((hV.mul_left _).mul_left b))
  rw [Summable.tsum_add ((hU.mul_left _).mul_left a) ((hV.mul_left _).mul_left b)] at hh
  simp only [tsum_mul_left, inv_mul_cancel₀ hsU.ne', inv_mul_cancel₀ hsV.ne', mul_one, hab] at hh
  have hh' := Real.log_le_log (mul_pos (Real.exp_pos (-c)) hsT) hh
  rw [Real.log_mul (Real.exp_ne_zero _) hsT.ne', Real.log_exp, Real.log_one] at hh'
  change _ ≤ c
  linarith

theorem cubeProbability_isProbability {L : ℝ} (hL : 0 < L) :
    IsProbabilityMeasure (cubeProbability L) := by
  constructor
  simp only [cubeProbability, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
    volume_cube, ENNReal.ofReal_pow hL.le]
  exact ENNReal.inv_mul_cancel (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hL).ne')
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

theorem measure_pi_smul {ι : Type uIndex} [Fintype ι] {X : ι → Type uX}
    [∀ i, MeasurableSpace (X i)] (μ : (i : ι) → Measure (X i))
    [∀ i, SigmaFinite (μ i)] (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  have : ∀ i, SigmaFinite (c i • μ i) := by
    intro i
    rw [← ENNReal.coe_toNNReal (hc i)]
    change SigmaFinite ((c i).toNNReal • μ i)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_mul_distrib]

theorem cubeProbability_pi {L : ℝ} (hL : 0 < L) (N : ℕ) :
    Measure.pi (fun _ : Fin N => cubeProbability L) =
      (ENNReal.ofReal (L ^ (3 * N)))⁻¹ • volume.restrict (configurationCube L N) := by
  have heq : configurationCube L N = Set.univ.pi (fun _ : Fin N => cube L) := by
    ext x
    simp [configurationCube, Set.mem_pi]
  rw [heq, volume_pi, Measure.restrict_pi_pi]
  unfold cubeProbability
  rw [measure_pi_smul _ _ (fun _ => ENNReal.inv_ne_top.mpr
    (ENNReal.ofReal_pos.mpr (pow_pos hL _)).ne')]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.inv_pow, ← ENNReal.ofReal_pow (pow_nonneg hL.le 3),
    ← pow_mul]

theorem measurePreserving_pair_eval {ι : Type uIndex} {X : Type uX} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {i j : ι} (hij : i ≠ j) :
    MeasurePreserving (fun x : ι → X => (x i, x j))
      (Measure.pi (fun _ : ι => μ)) (μ.prod μ) := by
  have hind := ProbabilityTheory.iIndepFun_pi (μ := fun _ : ι => μ)
    (X := fun _ => id) (fun _ => aemeasurable_id)
  refine ⟨(measurable_pi_apply _).prodMk (measurable_pi_apply _), ?_⟩
  have hp := (hind.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply _).aemeasurable (measurable_pi_apply _).aemeasurable
  simpa only [id_eq, (measurePreserving_eval (fun _ : ι => μ) i).map_eq,
    (measurePreserving_eval (fun _ : ι => μ) j).map_eq] using hp

theorem probability_pair_kernel_bound {L M : ℝ} (hL : 0 < L) {K : Position → ℝ}
    (hK : Continuous K) (hKM : ∀ z, |K z| ≤ M) (hKi : Integrable K)
    (hK0 : ∀ z, 0 ≤ K z) :
    (∫ z : Position × Position, K (z.1 - z.2) ∂(cubeProbability L).prod (cubeProbability L)) ≤
      (L ^ 3)⁻¹ * ∫ z, K z := by
  let := cubeProbability_isProbability hL
  have hi : Integrable (fun z : Position × Position => K (z.1 - z.2))
      ((cubeProbability L).prod (cubeProbability L)) :=
    Integrable.of_bound (hK.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable M
      (Eventually.of_forall (fun z => hKM (z.1 - z.2)))
  rw [integral_prod _ hi]
  have hh (x : Position) : (∫ y, K (x - y) ∂cubeProbability L) ≤ (L ^ 3)⁻¹ * ∫ z, K z := by
    simp only [cubeProbability, integral_smul_measure, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (pow_nonneg hL.le 3), smul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg hL.le _))
    exact (setIntegral_le_integral (hKi.comp_sub_left x)
      (Eventually.of_forall (fun y => hK0 (x - y)))).trans_eq (integral_sub_left_eq_self K volume x)
  have hh' := integral_mono hi.integral_prod_left (integrable_const _) hh
  simpa [integral_const, Measure.real] using hh'

theorem probability_energy_upper {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {L M : ℝ} (hL : 0 < L) (N : ℕ) {K : Position → ℝ}
    (hK : Continuous K) (hKM : ∀ z, |K z| ≤ M) (hKi : Integrable K)
    (hK0 : ∀ z, 0 ≤ K z) (hφK : ∀ x y, φ (nndist x y) ≤ K (x - y)) :
    (∫ x : Fin N → Position, energy φ x ∂Measure.pi (fun _ : Fin N => cubeProbability L)) ≤
      (N : ℝ) ^ 2 * ((L ^ 3)⁻¹ * ∫ z, K z) := by
  classical
  let := cubeProbability_isProbability hL
  obtain ⟨Mφ, hMφ, hφM⟩ := hb
  have hipair (i j : Fin N) : Integrable
      (fun x : Fin N → Position => φ (nndist (x i) (x j)))
      (Measure.pi (fun _ : Fin N => cubeProbability L)) :=
    Integrable.of_bound (hφ.comp ((continuous_apply i).nndist (continuous_apply j))).aestronglyMeasurable
      Mφ (Eventually.of_forall (fun x => hφM _))
  have hik (i j : Fin N) : Integrable
      (fun x : Fin N → Position => K (x i - x j))
      (Measure.pi (fun _ : Fin N => cubeProbability L)) :=
    Integrable.of_bound (hK.comp ((continuous_apply i).sub (continuous_apply j))).aestronglyMeasurable
      M (Eventually.of_forall (fun x => hKM _))
  simp only [energy, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hipair i j))]
  have hbound (i j : Fin N) (hij : i < j) :
      (∫ x : Fin N → Position, φ (nndist (x i) (x j))
        ∂Measure.pi (fun _ : Fin N => cubeProbability L)) ≤ (L ^ 3)⁻¹ * ∫ z, K z := by
    apply (integral_mono (hipair i j) (hik i j) (fun x => hφK (x i) (x j))).trans
    have hp := measurePreserving_pair_eval (cubeProbability L) hij.ne
    have hmap := integral_map (μ := Measure.pi (fun _ : Fin N => cubeProbability L)) hp.measurable.aemeasurable
      (hK.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
    rw [hp.map_eq] at hmap
    simp only [Function.comp_apply, Pi.sub_apply] at hmap
    rw [← hmap]
    exact probability_pair_kernel_bound hL hK hKM hKi hK0
  have hconst : 0 ≤ (L ^ 3)⁻¹ * ∫ z, K z :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg hL.le _)) (integral_nonneg hK0)
  calc
    _ = ∑ i : Fin N, ∑ j : Fin N with i < j,
        ∫ x : Fin N → Position, φ (nndist (x i) (x j))
          ∂Measure.pi (fun _ : Fin N => cubeProbability L) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hipair i j)]
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, (L ^ 3)⁻¹ * ∫ z, K z := by
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.sum_le_sum (fun j hj => hbound i j (Finset.mem_filter.mp hj).2)).trans
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => hconst)
    _ = _ := by simp; ring

theorem integral_cubeProbability_pi {L : ℝ} (hL : 0 < L) (N : ℕ)
    (F : (Fin N → Position) → ℝ) :
    (∫ x, F x ∂Measure.pi (fun _ : Fin N => cubeProbability L)) =
      (L ^ (3 * N))⁻¹ * ∫ x in configurationCube L N, F x := by
  rw [cubeProbability_pi hL N, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (pow_nonneg hL.le _), smul_eq_mul]

theorem log_partition_lower_of_energy_mean {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {L β E : ℝ} (hL : 0 < L) (hβ : 0 ≤ β) (N : ℕ)
    (hE : (∫ x : Fin N → Position, energy φ x
      ∂Measure.pi (fun _ : Fin N => cubeProbability L)) ≤ E) :
    (3 * N : ℝ) * Real.log L - Real.log (N.factorial : ℝ) - β * E ≤
      Real.log (partition φ L N β) := by
  let := cubeProbability_isProbability hL
  let μ := Measure.pi (fun _ : Fin N => cubeProbability L)
  obtain ⟨M, hM, hφM⟩ := hb
  have hi : Integrable (fun x : Fin N → Position => energy φ x) μ :=
    Integrable.of_bound (continuous_energy hφ N).aestronglyMeasurable
      ((N : ℝ)^2 * M) (Eventually.of_forall (energy_abs_bound hM hφM))
  have he : Integrable (fun x : Fin N → Position => Real.exp (-β * energy φ x)) μ := by
    apply Integrable.of_bound ((Real.continuous_exp.comp
      (continuous_const.mul (continuous_energy hφ N))).aestronglyMeasurable)
      (Real.exp (|β| * ((N : ℝ)^2 * M)))
    filter_upwards [] with x
    change |Real.exp _| ≤ _
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      -β * energy φ x ≤ |-β * energy φ x| := le_abs_self _
      _ = |β| * |energy φ x| := by rw [abs_mul, abs_neg]
      _ ≤ _ := mul_le_mul_of_nonneg_left (energy_abs_bound hM hφM x) (abs_nonneg β)
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall (fun x : Fin N → Position => mem_univ (-β * energy φ x)))
    (hi.const_mul (-β)) he
  rw [integral_const_mul] at hj
  have hlow := (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hE (neg_nonpos.mpr hβ))).trans hj
  have hp : 0 < ∫ x : Fin N → Position, Real.exp (-β * energy φ x) ∂μ :=
    lt_of_lt_of_le (Real.exp_pos _) hlow
  have hl := Real.log_le_log (Real.exp_pos (-β * E)) hlow
  rw [Real.log_exp] at hl
  have hpint : 0 < ∫ x in configurationCube L N, Real.exp (-β * energy φ x) := by
    have h := partition_pos hφ ⟨M, hM, hφM⟩ hL N β
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr (by exact_mod_cast Nat.factorial_pos N))).mp h
  change -β * E ≤ Real.log (∫ x, Real.exp (-β * energy φ x)
    ∂Measure.pi (fun _ : Fin N => cubeProbability L)) at hl
  rw [integral_cubeProbability_pi hL N, Real.log_mul (inv_ne_zero (pow_ne_zero _ hL.ne')) hpint.ne',
    Real.log_inv, Real.log_pow] at hl
  rw [partition, Real.log_mul (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero N)) hpint.ne',
    Real.log_inv]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hl
  linarith

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CanonicalCosts
attribute [-instance] _root_.OAI.RadialTransition.instMeasurableSpaceParticleState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem continuous_coreLift (t : ℝ) : Continuous (coreLift t) :=
  (continuous_coreReal t).comp continuous_norm

theorem coreLift_nonneg (t : ℝ) (x : Position) : 0 ≤ coreLift t x := coreReal_nonneg t ‖x‖

theorem coreLift_bound (t : ℝ) (x : Position) : |coreLift t x| ≤ t ^ 2 := by
  rw [abs_of_nonneg (coreLift_nonneg t x)]
  exact coreReal_le t ‖x‖

theorem coreLift_compactSupport {t : ℝ} (ht : 1 ≤ t) : HasCompactSupport (coreLift t) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Position) 2)
  intro x hx
  by_contra h
  have hn : 2 < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using h
  apply hx
  exact coreReal_zero_outer (by linarith) (le_trans
    (by have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) ht; norm_num at hh; simp only [one_div]; linarith)
    hn.le)

theorem integrable_coreLift {t : ℝ} (ht : 1 ≤ t) : Integrable (coreLift t) :=
  (continuous_coreLift t).integrable_of_hasCompactSupport (coreLift_compactSupport ht)

theorem familyPotential_le_core {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (r : ℝ≥0) :
    familyPotential t a R r ≤ corePotential t r := by
  exact sub_le_self _ (mul_nonneg ht (attractionProfile_nonneg ha hR r))

theorem probability_energy_family_upper {t L : ℝ} {a R : ℕ → ℝ} (ht : 1 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a)
    (hL : 0 < L) (N : ℕ) :
    (∫ x : Fin N → Position, energy (familyPotential t a R) x
      ∂Measure.pi (fun _ : Fin N => cubeProbability L)) ≤
      coreIntegral t * (N : ℝ)^2 / L^3 := by
  have hh := probability_energy_upper (continuous_familyPotential ha hR hs t)
    (bounded_familyPotential ha hR hs t) hL N (continuous_coreLift t)
    (coreLift_bound t) (integrable_coreLift ht) (coreLift_nonneg t)
    (fun x y => (familyPotential_le_core (by linarith) ha hR _).trans_eq (by
      simp only [corePotential, coreLift, coe_nndist, dist_eq_norm]))
  simpa only [coreIntegral, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv] using hh

theorem log_factorial_bounds (N : ℕ) :
    (N : ℝ) * Real.log N - N ≤ Real.log (N.factorial : ℝ) ∧
      Real.log (N.factorial : ℝ) ≤ (N : ℝ) * Real.log N := by
  by_cases hN : N = 0
  · simp [hN]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  constructor
  · have hh := Stirling.le_log_factorial_stirling hN
    have hnlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
    have hpilog : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  · have hf : (N.factorial : ℝ) ≤ (N : ℝ)^N := by exact_mod_cast Nat.factorial_le_pow N
    have hh := Real.log_le_log (by exact_mod_cast Nat.factorial_pos N) hf
    simpa only [Real.log_pow] using hh

theorem finiteCanonical_bounds {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {L t β c B K : ℝ} (hL : 0 < L) (ht : 0 < t) (hβ : 0 ≤ β) (N : ℕ)
    (hlow : ∀ x ∈ configurationCube L N, c * (N : ℝ)^2 / L^3 - B * N ≤ energy φ x)
    (hmean : (∫ x : Fin N → Position, energy φ x
      ∂Measure.pi (fun _ : Fin N => cubeProbability L)) ≤ K * (N : ℝ)^2 / L^3) :
    β / t * (c * densityAt L N ^ 2 - B * densityAt L N) +
        (densityAt L N * Real.log (densityAt L N) - densityAt L N) / t ≤
      finiteCanonical φ t L N β ∧
    finiteCanonical φ t L N β ≤
      β / t * K * densityAt L N ^ 2 + densityAt L N * Real.log (densityAt L N) / t := by
  have hden : 0 < t * L^3 := mul_pos ht (pow_pos hL 3)
  have hlog := log_factorial_bounds N
  have hl := log_partition_upper_of_energy_lower hφ hb hL hβ N hlow
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hu := log_partition_lower_of_energy_mean hφ hb hL hβ N hmean
  by_cases hN : N = 0
  · subst N
    simp [densityAt, finiteCanonical, partition_zero]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hdlog : Real.log (densityAt L N) = Real.log (N : ℝ) - 3 * Real.log L := by
    rw [densityAt, Real.log_div hNr (pow_ne_zero 3 hL.ne'), Real.log_pow]
    norm_num
  constructor
  · rw [finiteCanonical, le_div_iff₀ hden]
    rw [hdlog]
    dsimp only [densityAt]
    have halg : (β / t * (c * ((N : ℝ) / L^3)^2 - B * ((N : ℝ) / L^3)) +
        (((N : ℝ) / L^3) * (Real.log N - 3 * Real.log L) - ((N : ℝ) / L^3)) / t) *
        (t * L^3) = β * (c * (N : ℝ)^2 / L^3 - B * N) +
          (N : ℝ) * Real.log N - (3 * N : ℝ) * Real.log L - N := by field_simp; ring
    rw [halg]
    linarith
  · rw [finiteCanonical, div_le_iff₀ hden]
    rw [hdlog]
    dsimp only [densityAt]
    have halg : (β / t * K * ((N : ℝ) / L^3)^2 +
        ((N : ℝ) / L^3) * (Real.log N - 3 * Real.log L) / t) * (t * L^3) =
        β * (K * (N : ℝ)^2 / L^3) + (N : ℝ) * Real.log N - (3 * N : ℝ) * Real.log L := by
      field_simp
      ring
    rw [halg]
    linarith

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_SpatialProducts
attribute [-instance] _root_.OAI.RadialTransition.instMeasurableSpaceParticleState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uIndex uOtherIndex uX

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem orderedEnergy_fin (φ : Potential) {N : ℕ} (x : Fin N → Position) :
    orderedEnergy φ x = energy φ x := by
  have h := twice_pair_sum (fun i j => φ (nndist (x i) (x j)))
    (fun i j => by rw [nndist_comm])
  have hh : (∑ i : Fin N, ∑ j : Fin N,
      if i ≠ j then φ (nndist (x i) (x j)) else 0) = 2 * energy φ x := h.symm
  have he : orderedEnergy φ x = (∑ i : Fin N, ∑ j : Fin N,
      if i ≠ j then φ (nndist (x i) (x j)) else 0) / 2 := by
    unfold orderedEnergy
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j <;> simp [hij]
  rw [he, hh]
  ring

theorem orderedEnergy_equiv {ι : Type uIndex} {κ : Type uOtherIndex} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (φ : Potential) (x : κ → Position) :
    orderedEnergy φ (x ∘ e) = orderedEnergy φ x := by
  classical
  unfold orderedEnergy
  congr 1
  have hi (i : ι) : (∑ j : ι, if i ≠ j then φ (nndist (x (e i)) (x (e j))) else 0) =
      ∑ j : κ, if e i ≠ j then φ (nndist (x (e i)) (x j)) else 0 := by
    convert e.sum_comp (fun j => if e i ≠ j then φ (nndist (x (e i)) (x j)) else 0) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [ne_eq, e.injective.eq_iff]
  simpa only [Function.comp_apply, hi] using
    e.sum_comp (fun i => ∑ j, if i ≠ j then φ (nndist (x i) (x j)) else 0)

theorem continuous_orderedEnergy {ι : Type uIndex} [Fintype ι] {φ : Potential}
    (hφ : Continuous φ) : Continuous (fun x : ι → Position => orderedEnergy φ x) := by
  classical
  unfold orderedEnergy
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  split_ifs
  · exact hφ.comp ((continuous_apply i).nndist (continuous_apply j))
  · exact continuous_const

theorem orderedEnergy_abs_bound {ι : Type uIndex} [Fintype ι] {φ : Potential} {M : ℝ}
    (hM : 0 ≤ M) (hφM : ∀ r, |φ r| ≤ M) (x : ι → Position) :
    |orderedEnergy φ x| ≤ (Fintype.card ι : ℝ)^2 * M := by
  classical
  have hh : |∑ i : ι, ∑ j : ι, if i ≠ j then φ (nndist (x i) (x j)) else 0| ≤
      ∑ i : ι, ∑ j : ι, M := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · exact hφM _
    · simpa using hM
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  unfold orderedEnergy
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [mul_nonneg (sq_nonneg (Fintype.card ι : ℝ)) hM]

theorem integrable_orderedBoltzmann {ι : Type uIndex} [Fintype ι] {φ : Potential}
    (hφ : Continuous φ) (hb : IsBoundedPotential φ) (β : ℝ)
    (μ : Measure (ι → Position)) [IsFiniteMeasure μ] :
    Integrable (fun x : ι → Position => Real.exp (-β * orderedEnergy φ x)) μ := by
  obtain ⟨M, hM, hφM⟩ := hb
  apply Integrable.of_bound ((Real.continuous_exp.comp
    (continuous_const.mul (continuous_orderedEnergy hφ))).aestronglyMeasurable)
    (Real.exp (|β| * ((Fintype.card ι : ℝ)^2 * M)))
  filter_upwards [] with x
  change |Real.exp _| ≤ _
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    -β * orderedEnergy φ x ≤ |-β * orderedEnergy φ x| := le_abs_self _
    _ = |β| * |orderedEnergy φ x| := by rw [abs_mul, abs_neg]
    _ ≤ _ := mul_le_mul_of_nonneg_left (orderedEnergy_abs_bound hM hφM x) (abs_nonneg β)

theorem rawPartition_nonneg (φ : Potential) (A : Set Position) (ι : Type uIndex) [Fintype ι] (β : ℝ) :
    0 ≤ rawPartition φ A ι β := integral_nonneg (fun _ => (Real.exp_pos _).le)

theorem rawPartition_equiv {ι : Type uIndex} {κ : Type uOtherIndex} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (φ : Potential) (A : Set Position) (β : ℝ) :
    rawPartition φ A ι β = rawPartition φ A κ β := by
  have hp := measurePreserving_piCongrLeft (fun _ : κ => volume.restrict A) e
  have hh := hp.integral_comp' (fun x => Real.exp (-β * orderedEnergy φ x))
  have he (x : ι → Position) : orderedEnergy φ ((MeasurableEquiv.piCongrLeft (fun _ : κ => Position) e) x) =
      orderedEnergy φ x := by
    have ht := orderedEnergy_equiv e φ ((MeasurableEquiv.piCongrLeft (fun _ : κ => Position) e) x)
    simpa only [Function.comp_def, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_apply] using ht.symm
  simpa only [rawPartition, he] using hh

theorem measure_pi_add {ι : Type uIndex} [Fintype ι] [DecidableEq ι] {X : ι → Type uX}
    [∀ i, MeasurableSpace (X i)] (μ ν : (i : ι) → Measure (X i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    Measure.pi (fun i => μ i + ν i) =
      ∑ T : Finset ι, Measure.pi (fun i => if i ∈ T then μ i else ν i) := by
  classical
  have hσ (T : Finset ι) : ∀ i, SigmaFinite (if i ∈ T then μ i else ν i) := by
    intro i
    split_ifs <;> infer_instance
  refine Measure.pi_eq (μ := fun i => μ i + ν i) (fun s hs => ?_)
  simp only [Measure.finsetSum_apply, Measure.pi_pi, Measure.add_apply]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro T _
  have he (i : ι) : (if i ∈ T then μ i else ν i) (s i) =
      if i ∈ T then μ i (s i) else ν i (s i) := by split_ifs <;> rfl
  simp_rw [he]
  rw [Finset.prod_ite]
  congr 1 <;> congr 1 <;> ext i <;> simp

theorem sum_split_four {ι : Type uIndex} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (F : ι → ι → ℝ) :
    (∑ i, ∑ j, F i j) =
      (∑ i : Subtype p, ∑ j : Subtype p, F i j) +
      (∑ i : Subtype p, ∑ j : {j // ¬p j}, F i j) +
      (∑ i : {i // ¬p i}, ∑ j : Subtype p, F i j) +
      (∑ i : {i // ¬p i}, ∑ j : {j // ¬p j}, F i j) := by
  rw [← Fintype.sum_subtype_add_sum_subtype p (fun i => ∑ j, F i j)]
  simp_rw [← Fintype.sum_subtype_add_sum_subtype p (fun j => F _ j)]
  simp only [Finset.sum_add_distrib]
  ring

theorem orderedEnergy_split {ι : Type uIndex} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (φ : Potential) (x : ι → Position) :
    orderedEnergy φ x = orderedEnergy φ (fun i : Subtype p => x i) +
      orderedEnergy φ (fun i : {i // ¬p i} => x i) +
      ∑ i : Subtype p, ∑ j : {j // ¬p j}, φ (nndist (x i) (x j)) := by
  classical
  have hn (i : Subtype p) (j : {i // ¬p i}) : (i : ι) ≠ j := by
    intro h
    exact j.property (h ▸ i.property)
  unfold orderedEnergy
  rw [sum_split_four p]
  dsimp only
  have hpp (i j : Subtype p) : (if (i : ι) ≠ (j : ι) then φ (nndist (x i) (x j)) else 0) =
      if i ≠ j then φ (nndist (x i) (x j)) else 0 := by
    by_cases h : i = j
    · simp [h]
    · simp [h, Subtype.coe_ne_coe.mpr h]
  have hmm (i j : {i // ¬p i}) : (if (i : ι) ≠ (j : ι) then φ (nndist (x i) (x j)) else 0) =
      if i ≠ j then φ (nndist (x i) (x j)) else 0 := by
    by_cases h : i = j
    · simp [h]
    · simp [h, Subtype.coe_ne_coe.mpr h]
  have hpm (i : Subtype p) (j : {i // ¬p i}) :
      (if (i : ι) ≠ (j : ι) then φ (nndist (x i) (x j)) else 0) = φ (nndist (x i) (x j)) := by
    rw [ite_eq_left (hn i j)]
  have hmp (i : {i // ¬p i}) (j : Subtype p) :
      (if (i : ι) ≠ (j : ι) then φ (nndist (x i) (x j)) else 0) = φ (nndist (x i) (x j)) := by
    rw [ite_eq_left (hn j i).symm]
  simp_rw [hpp, hmm, hpm, hmp]
  have hs : (∑ i : {i // ¬p i}, ∑ j : Subtype p, φ (nndist (x i) (x j))) =
      ∑ i : Subtype p, ∑ j : {j // ¬p j}, φ (nndist (x i) (x j)) := by
    rw [Finset.sum_comm]
    simp_rw [nndist_comm]
  rw [hs]
  ring_nf

theorem orderedEnergy_split_le {ι : Type uIndex} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (φ : Potential) (x : ι → Position)
    (hc : ∀ i j, p i → ¬p j → φ (nndist (x i) (x j)) ≤ 0) :
    orderedEnergy φ x ≤ orderedEnergy φ (fun i : Subtype p => x i) +
      orderedEnergy φ (fun i : {i // ¬p i} => x i) := by
  rw [orderedEnergy_split p]
  have hh : (∑ i : Subtype p, ∑ j : {j // ¬p j}, φ (nndist (x i) (x j))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    apply Finset.sum_nonpos
    intro j _
    exact hc i j i.property j.property
  linarith

theorem sector_product_integral {ι : Type uIndex} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (F : (Subtype p → Position) → ℝ) (G : ({i // ¬p i} → Position) → ℝ)
    (μ ν : Measure Position) [SigmaFinite μ] [SigmaFinite ν] :
    (∫ x : ι → Position, F (fun i => x i) * G (fun i => x i)
      ∂Measure.pi (fun i => if p i then μ else ν)) =
      (∫ x : Subtype p → Position, F x ∂Measure.pi (fun _ => μ)) *
        ∫ x : {i // ¬p i} → Position, G x ∂Measure.pi (fun _ => ν) := by
  have : ∀ i : ι, SigmaFinite (if p i then μ else ν) := by
    intro i
    split_ifs <;> infer_instance
  have hp := measurePreserving_piEquivPiSubtypeProd (fun i => if p i then μ else ν) p
  have hh := hp.integral_comp' (fun z => F z.1 * G z.2)
  simp only [MeasurableEquiv.piEquivPiSubtypeProd_apply,
    Subtype.prop, ite_true, if_true, (fun i : {i // ¬p i} => i.property), ite_false, if_false] at hh
  exact hh.trans (integral_prod_mul F G)

theorem sector_raw_lower {ι : Type uIndex} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ) {β : ℝ} (hβ : 0 ≤ β)
    {A B : Set Position} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAfin : volume A ≠ ⊤) (hBfin : volume B ≠ ⊤)
    (hc : ∀ x ∈ A, ∀ y ∈ B, φ (nndist x y) ≤ 0) :
    rawPartition φ A (Subtype p) β * rawPartition φ B {i // ¬p i} β ≤
      ∫ x : ι → Position, Real.exp (-β * orderedEnergy φ x)
        ∂Measure.pi (fun i => if p i then volume.restrict A else volume.restrict B) := by
  let μ := fun i : ι => if p i then volume.restrict A else volume.restrict B
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAfin
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBfin
  have : ∀ i, IsFiniteMeasure (μ i) := by
    intro i
    dsimp [μ]
    split_ifs <;> infer_instance
  have hiA := integrable_orderedBoltzmann hφ hb β (Measure.pi (fun _ : Subtype p => volume.restrict A))
  have hiB := integrable_orderedBoltzmann hφ hb β (Measure.pi (fun _ : {i // ¬p i} => volume.restrict B))
  have hp := measurePreserving_piEquivPiSubtypeProd μ p
  have hip : Integrable (fun z : (Subtype p → Position) × ({i // ¬p i} → Position) =>
      Real.exp (-β * orderedEnergy φ z.1) * Real.exp (-β * orderedEnergy φ z.2))
      ((Measure.pi (fun i : Subtype p => μ i)).prod (Measure.pi (fun i : {i // ¬p i} => μ i))) := by
    simpa only [μ, Subtype.prop, ite_true, if_true, (fun i : {i // ¬p i} => i.property), ite_false, if_false] using hiA.mul_prod hiB
  have his := hp.integrable_comp_of_integrable hip
  have hiQ := integrable_orderedBoltzmann hφ hb β (Measure.pi μ)
  have hae : ∀ᵐ x : ι → Position ∂Measure.pi μ, ∀ i, x i ∈ (if p i then A else B) := by
    apply ae_all_iff.mpr
    intro i
    apply (Measure.tendsto_eval_ae_ae (μ := μ)).eventually
    dsimp [μ]
    split_ifs <;> exact ae_restrict_mem (by assumption)
  have hh := integral_mono_ae his hiQ (hae.mono (fun x hx => ?_))
  · simp only [MeasurableEquiv.piEquivPiSubtypeProd_apply, Function.comp_apply] at hh
    change (∫ x : ι → Position, Real.exp (-β * orderedEnergy φ (fun i : Subtype p => x i)) *
      Real.exp (-β * orderedEnergy φ (fun i : {i // ¬p i} => x i))
      ∂Measure.pi (fun i => if p i then volume.restrict A else volume.restrict B)) ≤ _ at hh
    have hprod := sector_product_integral p
      (fun x : Subtype p → Position => Real.exp (-β * orderedEnergy φ x))
      (fun x : {i // ¬p i} → Position => Real.exp (-β * orderedEnergy φ x))
      (volume.restrict A) (volume.restrict B)
    exact hprod.symm.trans_le hh
  · change Real.exp (-β * orderedEnergy φ (fun i : Subtype p => x i)) *
        Real.exp (-β * orderedEnergy φ (fun i : {i // ¬p i} => x i)) ≤ _
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he := orderedEnergy_split_le p φ x (fun i j hi hj => hc (x i)
      (by simpa [hi] using hx i) (x j) (by simpa [hj] using hx j))
    nlinarith

theorem rawPartition_union_sum {ι : Type uIndex} [Fintype ι] [DecidableEq ι]
    {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ) (β : ℝ)
    {A B : Set Position} (hB : MeasurableSet B) (hab : Disjoint A B)
    (hAfin : volume A ≠ ⊤) (hBfin : volume B ≠ ⊤) :
    rawPartition φ (A ∪ B) ι β =
      ∑ T : Finset ι, ∫ x : ι → Position, Real.exp (-β * orderedEnergy φ x)
        ∂Measure.pi (fun i => if i ∈ T then volume.restrict A else volume.restrict B) := by
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAfin
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBfin
  unfold rawPartition
  simp_rw [Measure.restrict_union hab hB]
  rw [measure_pi_add]
  apply integral_finsetSum_measure
  intro T _
  have : ∀ i : ι, IsFiniteMeasure (if i ∈ T then volume.restrict A else volume.restrict B) := by
    intro i
    split_ifs <;> infer_instance
  exact integrable_orderedBoltzmann hφ hb β _

theorem rawPartition_union_lower {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {β : ℝ} (hβ : 0 ≤ β)
    {A B : Set Position} (hA : MeasurableSet A) (hB : MeasurableSet B) (hab : Disjoint A B)
    (hAfin : volume A ≠ ⊤) (hBfin : volume B ≠ ⊤)
    (hc : ∀ x ∈ A, ∀ y ∈ B, φ (nndist x y) ≤ 0) (m n : ℕ) :
    ((m + n).choose m : ℝ) * rawPartition φ A (Fin m) β * rawPartition φ B (Fin n) β ≤
      rawPartition φ (A ∪ B) (Fin (m + n)) β := by
  classical
  let S : Finset (Finset (Fin (m + n))) := Finset.univ.powersetCard m
  let I (T : Finset (Fin (m + n))) := ∫ x : Fin (m + n) → Position, Real.exp (-β * orderedEnergy φ x)
    ∂Measure.pi (fun i => if i ∈ T then volume.restrict A else volume.restrict B)
  have hterm (T : Finset (Fin (m + n))) (hT : T ∈ S) :
      rawPartition φ A (Fin m) β * rawPartition φ B (Fin n) β ≤ I T := by
    have hcard : T.card = m := (Finset.mem_powersetCard.mp hT).2
    have hcardA : Fintype.card {i : Fin (m + n) // i ∈ T} = m := by
      simpa only [Fintype.card_coe] using hcard
    have hcardB : Fintype.card {i : Fin (m + n) // i ∉ T} = n := by
      rw [Fintype.card_subtype_compl, hcardA, Fintype.card_fin]
      omega
    have hh := sector_raw_lower (fun i => i ∈ T) hφ hb hβ hA hB hAfin hBfin hc
    have heA := rawPartition_equiv (Fintype.equivFinOfCardEq hcardA) φ A β
    have heB := rawPartition_equiv (Fintype.equivFinOfCardEq hcardB) φ B β
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    · convert heA.symm using 1
      all_goals try with_reducible_and_instances rfl
      congr!
    · exact heB.symm
  have hs := Finset.sum_le_sum hterm
  have hnn (T : Finset (Fin (m + n))) : 0 ≤ I T := integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hsubset : S ⊆ Finset.univ := Finset.subset_univ _
  have hh := hs.trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun T _ _ => hnn T))
  have hcardS : S.card = (m + n).choose m := by
    simp only [S, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_const, hcardS, nsmul_eq_mul] at hh
  rw [rawPartition_union_sum hφ hb β hB hab hAfin hBfin]
  simpa only [mul_assoc, I] using hh

theorem partitionOn_union_lower {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {β : ℝ} (hβ : 0 ≤ β)
    {A B : Set Position} (hA : MeasurableSet A) (hB : MeasurableSet B) (hab : Disjoint A B)
    (hAfin : volume A ≠ ⊤) (hBfin : volume B ≠ ⊤)
    (hc : ∀ x ∈ A, ∀ y ∈ B, φ (nndist x y) ≤ 0) (m n : ℕ) :
    partitionOn φ A m β * partitionOn φ B n β ≤ partitionOn φ (A ∪ B) (m + n) β := by
  have hh := rawPartition_union_lower hφ hb hβ hA hB hab hAfin hBfin hc m n
  have hm : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hmn : ((m + n).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m + n)
  have hfac : ((m + n).choose m : ℝ) * m.factorial * n.factorial = (m + n).factorial := by
    exact_mod_cast (by simpa using Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right m n))
  have hcancel : ((m + n).factorial : ℝ)⁻¹ * ((m + n).choose m : ℝ) =
      (m.factorial : ℝ)⁻¹ * (n.factorial : ℝ)⁻¹ := by
    field_simp
    nlinarith [hfac]
  have hh' := mul_le_mul_of_nonneg_left hh
    (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ (m + n).factorial))
  unfold partitionOn
  have he : (m.factorial : ℝ)⁻¹ * rawPartition φ A (Fin m) β *
      ((n.factorial : ℝ)⁻¹ * rawPartition φ B (Fin n) β) =
      ((m + n).factorial : ℝ)⁻¹ *
        (((m + n).choose m : ℝ) * rawPartition φ A (Fin m) β * rawPartition φ B (Fin n) β) := by
    calc
      _ = ((m.factorial : ℝ)⁻¹ * (n.factorial : ℝ)⁻¹) *
          (rawPartition φ A (Fin m) β * rawPartition φ B (Fin n) β) := by ring
      _ = _ := by rw [← hcancel]; ring
  rw [he]
  exact hh'

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_PartitionReplication
attribute [-instance] _root_.OAI.RadialTransition.instMeasurableSpaceParticleState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uIndex uI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem rawPartition_setIntegral {ι : Type uIndex} [Fintype ι] (φ : Potential) (A : Set Position) (β : ℝ) :
    rawPartition φ A ι β = ∫ x in Set.univ.pi (fun _ : ι => A), Real.exp (-β * orderedEnergy φ x) := by
  rw [rawPartition, volume_pi, Measure.restrict_pi_pi]

theorem partitionOn_cube (φ : Potential) (L : ℝ) (N : ℕ) (β : ℝ) :
    partitionOn φ (cube L) N β = partition φ L N β := by
  rw [partitionOn, rawPartition_setIntegral]
  simp_rw [orderedEnergy_fin]
  have he : (Set.univ.pi (fun _ : Fin N => cube L)) = configurationCube L N := by
    ext x
    simp [configurationCube, Set.mem_pi]
  rw [he]
  rfl

theorem partitionOn_nonneg (φ : Potential) (A : Set Position) (N : ℕ) (β : ℝ) :
    0 ≤ partitionOn φ A N β := mul_nonneg (by positivity) (rawPartition_nonneg φ A _ β)

theorem partitionOn_zero (φ : Potential) (A : Set Position) (β : ℝ) :
    partitionOn φ A 0 β = 1 := by
  simp [partitionOn, rawPartition, orderedEnergy, Measure.real]

theorem rawPartition_mono {ι : Type uIndex} [Fintype ι] {φ : Potential}
    (hφ : Continuous φ) (hb : IsBoundedPotential φ) (β : ℝ)
    {A B : Set Position} (hAB : A ⊆ B) (hBfin : volume B ≠ ⊤) :
    rawPartition φ A ι β ≤ rawPartition φ B ι β := by
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBfin
  have hi : Integrable (fun x : ι → Position => Real.exp (-β * orderedEnergy φ x))
      (volume.restrict (Set.univ.pi (fun _ : ι => B))) := by
    rw [volume_pi, Measure.restrict_pi_pi]
    exact integrable_orderedBoltzmann hφ hb β _
  rw [rawPartition_setIntegral, rawPartition_setIntegral]
  exact integral_mono_measure (Measure.restrict_mono (Set.pi_mono (fun _ _ => hAB)) le_rfl)
    (Eventually.of_forall (fun _ => (Real.exp_pos _).le)) hi

theorem partitionOn_mono {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    (β : ℝ) (N : ℕ) {A B : Set Position} (hAB : A ⊆ B) (hBfin : volume B ≠ ⊤) :
    partitionOn φ A N β ≤ partitionOn φ B N β :=
  mul_le_mul_of_nonneg_left (rawPartition_mono hφ hb β hAB hBfin) (by positivity)

theorem measurableSet_translate {a : Position} {A : Set Position} (hA : MeasurableSet A) :
    MeasurableSet (translateSet a A) := hA.preimage (measurable_id.sub_const a)

theorem orderedEnergy_add {ι : Type uIndex} [Fintype ι] (φ : Potential) (x : ι → Position) (a : Position) :
    orderedEnergy φ (fun i => a + x i) = orderedEnergy φ x := by
  simp only [orderedEnergy, nndist_add_left]

theorem rawPartition_translate {ι : Type uIndex} [Fintype ι] (φ : Potential)
    (A : Set Position) (a : Position) (β : ℝ) :
    rawPartition φ (translateSet a A) ι β = rawPartition φ A ι β := by
  let τ : (ι → Position) ≃ᵐ (ι → Position) := (Homeomorph.addLeft (fun _ : ι => a)).toMeasurableEquiv
  have hp : MeasurePreserving τ volume volume := measurePreserving_add_left volume _
  have hpre : τ ⁻¹' (Set.univ.pi (fun _ : ι => translateSet a A)) = Set.univ.pi (fun _ : ι => A) := by
    ext x
    simp [τ, translateSet, add_sub_cancel_left]
  have he (x : ι → Position) : orderedEnergy φ (τ x) = orderedEnergy φ x := orderedEnergy_add φ x a
  have hh := hp.setIntegral_preimage_emb τ.measurableEmbedding
    (fun x => Real.exp (-β * orderedEnergy φ x)) (Set.univ.pi (fun _ : ι => translateSet a A))
  rw [hpre] at hh
  simpa only [rawPartition_setIntegral, he] using hh.symm

theorem partitionOn_translate (φ : Potential) (A : Set Position) (a : Position) (N : ℕ) (β : ℝ) :
    partitionOn φ (translateSet a A) N β = partitionOn φ A N β := by
  simp only [partitionOn, rawPartition_translate]

theorem partitionOn_biUnion_lower {I : Type uI} (S : Finset I) (A : I → Set Position)
    {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ) {β : ℝ} (hβ : 0 ≤ β)
    (hA : ∀ i ∈ S, MeasurableSet (A i)) (hAfin : ∀ i ∈ S, volume (A i) ≠ ⊤)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (A i) (A j))
    (hc : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, φ (nndist x y) ≤ 0)
    (n : I → ℕ) :
    ∏ i ∈ S, partitionOn φ (A i) (n i) β ≤
      partitionOn φ (⋃ i ∈ S, A i) (∑ i ∈ S, n i) β := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [partitionOn_zero]
  | @insert i S hi ih =>
    have hAs (j) (hj : j ∈ S) := hA j (Finset.mem_insert_of_mem hj)
    have hfins (j) (hj : j ∈ S) := hAfin j (Finset.mem_insert_of_mem hj)
    have hU : MeasurableSet (⋃ j ∈ S, A j) := S.measurableSet_biUnion hAs
    have hUfin : volume (⋃ j ∈ S, A j) ≠ ⊤ := by
      apply ne_top_of_le_ne_top _ (measure_biUnion_finset_le S A)
      exact ENNReal.sum_ne_top.mpr hfins
    have hdU : Disjoint (A i) (⋃ j ∈ S, A j) := by
      simp only [Set.disjoint_iUnion_right]
      intro j hj
      exact hdisj i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (by rintro rfl; exact hi hj)
    have hcU : ∀ x ∈ A i, ∀ y ∈ ⋃ j ∈ S, A j, φ (nndist x y) ≤ 0 := by
      intro x hx y hy
      obtain ⟨j, hj, hy⟩ := Set.mem_iUnion₂.mp hy
      exact hc i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (by rintro rfl; exact hi hj) x hx y hy
    have hi' := ih hAs hfins
      (fun j hj k hk hne => hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne)
      (fun j hj k hk hne => hc j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne)
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have hprod := mul_le_mul_of_nonneg_left hi' (partitionOn_nonneg φ (A i) (n i) β)
    refine hprod.trans ?_
    have hu : (⋃ j ∈ insert i S, A j) = A i ∪ ⋃ j ∈ S, A j := by
      ext x
      simp
    rw [hu]
    exact partitionOn_union_lower hφ hb hβ
      (hA i (Finset.mem_insert_self _ _)) hU hdU (hAfin i (Finset.mem_insert_self _ _)) hUfin hcU
      (n i) (∑ j ∈ S, n j)

theorem sum_all_subsets_card (N : ℕ) (F : ℕ → ℝ) :
    (∑ T : Finset (Fin N), F T.card) = ∑ m ∈ Finset.range (N + 1), (N.choose m : ℝ) * F m := by
  have hh := Finset.sum_powerset (Finset.univ : Finset (Fin N)) (fun T => F T.card)
  simpa only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin,
    Finset.sum_powersetCard, nsmul_eq_mul] using hh

theorem factorial_choose_cancel {N m : ℕ} (hm : m ≤ N) :
    (N.factorial : ℝ)⁻¹ * (N.choose m : ℝ) =
      (m.factorial : ℝ)⁻¹ * ((N - m).factorial : ℝ)⁻¹ := by
  have hfac : (N.choose m : ℝ) * m.factorial * (N - m).factorial = N.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hm
  have hN : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  have hm' : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hnm : ((N - m).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (N - m)
  field_simp
  nlinarith [hfac]

theorem partitionOn_union_convolution {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {β : ℝ} (hβ : 0 ≤ β)
    {A B : Set Position} (hA : MeasurableSet A) (hB : MeasurableSet B) (hab : Disjoint A B)
    (hAfin : volume A ≠ ⊤) (hBfin : volume B ≠ ⊤)
    (hc : ∀ x ∈ A, ∀ y ∈ B, φ (nndist x y) ≤ 0) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), partitionOn φ A m β * partitionOn φ B (N - m) β) ≤
      partitionOn φ (A ∪ B) N β := by
  classical
  have hterm (T : Finset (Fin N)) :
      rawPartition φ A (Fin T.card) β * rawPartition φ B (Fin (N - T.card)) β ≤
      ∫ x : Fin N → Position, Real.exp (-β * orderedEnergy φ x)
        ∂Measure.pi (fun i => if i ∈ T then volume.restrict A else volume.restrict B) := by
    have hcardA : Fintype.card {i : Fin N // i ∈ T} = T.card := Fintype.card_coe T
    have hcardB : Fintype.card {i : Fin N // i ∉ T} = N - T.card := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, hcardA]
    have hh := sector_raw_lower (fun i => i ∈ T) hφ hb hβ hA hB hAfin hBfin hc
    have heA := rawPartition_equiv (Fintype.equivFinOfCardEq hcardA) φ A β
    have heB := rawPartition_equiv (Fintype.equivFinOfCardEq hcardB) φ B β
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    · convert heA.symm using 1
      all_goals try with_reducible_and_instances rfl
      congr!
    · exact heB.symm
  have hh := Finset.sum_le_sum (fun T (_ : T ∈ (Finset.univ : Finset (Finset (Fin N)))) => hterm T)
  rw [← rawPartition_union_sum hφ hb β hB hab hAfin hBfin] at hh
  rw [sum_all_subsets_card N (fun m =>
    rawPartition φ A (Fin m) β * rawPartition φ B (Fin (N - m)) β)] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (show (0 : ℝ) ≤ N.factorial by positivity))
  change _ ≤ (N.factorial : ℝ)⁻¹ * rawPartition φ (A ∪ B) (Fin N) β
  refine le_trans (le_of_eq ?_) hh'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hcancel := factorial_choose_cancel (Nat.le_of_lt_succ (Finset.mem_range.mp hm))
  unfold partitionOn
  calc
    _ = ((m.factorial : ℝ)⁻¹ * ((N - m).factorial : ℝ)⁻¹) *
        (rawPartition φ A (Fin m) β * rawPartition φ B (Fin (N - m)) β) := by ring
    _ = _ := by rw [← hcancel]; ring

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_GrandPartition
attribute [-instance] _root_.OAI.RadialTransition.instMeasurableSpaceParticleState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem partitionOn_stability_upper {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B β : ℝ} (hstable : StableWith φ B)
    (hβ : 0 ≤ β) {A : Set Position} (hAfin : volume A ≠ ⊤) (N : ℕ) :
    partitionOn φ A N β ≤ (volume.real A) ^ N * Real.exp (β * B * N) / N.factorial := by
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAfin
  have hh : rawPartition φ A (Fin N) β ≤ (volume.real A) ^ N * Real.exp (β * B * N) := by
    calc
      _ ≤ ∫ _ : Fin N → Position, Real.exp (β * B * N)
          ∂Measure.pi (fun _ : Fin N => volume.restrict A) := by
        apply integral_mono (integrable_orderedBoltzmann hφ hb β _) (integrable_const _)
        intro x
        apply Real.exp_le_exp.mpr
        rw [orderedEnergy_fin]
        nlinarith [mul_le_mul_of_nonneg_left (hstable N x) hβ]
      _ = _ := by
        simp [integral_const, measureReal_def, Measure.pi_univ]
  have hh' := mul_le_mul_of_nonneg_left hh
    (show (0 : ℝ) ≤ (N.factorial : ℝ)⁻¹ by positivity)
  simpa only [partitionOn, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh'

theorem grandOn_term_upper {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B β : ℝ} (hstable : StableWith φ B)
    (hβ : 0 ≤ β) {A : Set Position} (hAfin : volume A ≠ ⊤) (z : ℝ) (N : ℕ) :
    Real.exp (z * N) * partitionOn φ A N β ≤
      (volume.real A * Real.exp (β * B + z)) ^ N / N.factorial := by
  have hh := mul_le_mul_of_nonneg_left (partitionOn_stability_upper hφ hb hstable hβ hAfin N)
    (Real.exp_pos (z * N)).le
  apply hh.trans_eq
  rw [Real.exp_add, mul_pow, mul_pow, ← Real.exp_nat_mul (β * B) N,
    ← Real.exp_nat_mul z N]
  have he₁ : β * B * (N : ℝ) = (N : ℝ) * (β * B) := by ring
  have he₂ : z * (N : ℝ) = (N : ℝ) * z := by ring
  rw [he₁, he₂]
  ring

theorem grandOn_summable {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B β : ℝ} (hstable : StableWith φ B)
    (hβ : 0 ≤ β) {A : Set Position} (hAfin : volume A ≠ ⊤) (z : ℝ) :
    Summable (fun N : ℕ => Real.exp (z * N) * partitionOn φ A N β) :=
  Summable.of_nonneg_of_le
    (fun N => mul_nonneg (Real.exp_pos _).le (partitionOn_nonneg φ A N β))
    (grandOn_term_upper hφ hb hstable hβ hAfin z)
    (Real.summable_pow_div_factorial _)

theorem grandOn_bounds {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B β : ℝ} (hstable : StableWith φ B)
    (hβ : 0 ≤ β) {A : Set Position} (hAfin : volume A ≠ ⊤) (z : ℝ) :
    1 ≤ grandOn φ A β z ∧ grandOn φ A β z ≤ Real.exp (volume.real A * Real.exp (β * B + z)) := by
  have hs := grandOn_summable hφ hb hstable hβ hAfin z
  constructor
  · have hh := hs.le_tsum 0 (fun N _ => mul_nonneg (Real.exp_pos _).le (partitionOn_nonneg φ A N β))
    convert hh using 1 <;> first | rfl | norm_num [partitionOn_zero]
  · have hh := hs.tsum_le_tsum (grandOn_term_upper hφ hb hstable hβ hAfin z)
      (Real.summable_pow_div_factorial _)
    have he : (∑' N : ℕ, (volume.real A * Real.exp (β * B + z)) ^ N / N.factorial) =
        Real.exp (volume.real A * Real.exp (β * B + z)) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    exact hh.trans_eq he

theorem grandOn_union_lower {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {B β : ℝ} (hstable : StableWith φ B) (hβ : 0 ≤ β)
    {A D : Set Position} (hA : MeasurableSet A) (hD : MeasurableSet D) (had : Disjoint A D)
    (hAfin : volume A ≠ ⊤) (hDfin : volume D ≠ ⊤)
    (hc : ∀ x ∈ A, ∀ y ∈ D, φ (nndist x y) ≤ 0) (z : ℝ) :
    grandOn φ A β z * grandOn φ D β z ≤ grandOn φ (A ∪ D) β z := by
  have hUfin : volume (A ∪ D) ≠ ⊤ := (measure_union_le A D).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hAfin.lt_top, hDfin.lt_top⟩) |>.ne
  have hsA := grandOn_summable hφ hb hstable hβ hAfin z
  have hsD := grandOn_summable hφ hb hstable hβ hDfin z
  have hsU := grandOn_summable hφ hb hstable hβ hUfin z
  have hcov (N : ℕ) :
      (∑ m ∈ Finset.range (N + 1), (Real.exp (z * m) * partitionOn φ A m β) *
        (Real.exp (z * ((N - m : ℕ) : ℝ)) * partitionOn φ D (N - m) β)) ≤
          Real.exp (z * N) * partitionOn φ (A ∪ D) N β := by
    have he : (∑ m ∈ Finset.range (N + 1), (Real.exp (z * m) * partitionOn φ A m β) *
        (Real.exp (z * ((N - m : ℕ) : ℝ)) * partitionOn φ D (N - m) β)) =
        Real.exp (z * N) * ∑ m ∈ Finset.range (N + 1),
          partitionOn φ A m β * partitionOn φ D (N - m) β := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hmN : m ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      have he : z * (m : ℝ) + z * (N - m : ℕ) = z * N := by
        rw [Nat.cast_sub hmN]; ring
      calc
        _ = (Real.exp (z * m) * Real.exp (z * ((N - m : ℕ) : ℝ))) *
            (partitionOn φ A m β * partitionOn φ D (N - m) β) := by ring
        _ = _ := by rw [← Real.exp_add, he]
    rw [he]
    exact mul_le_mul_of_nonneg_left (partitionOn_union_convolution hφ hb hβ hA hD had hAfin hDfin hc N)
      (Real.exp_pos _).le
  have hnn (N : ℕ) : 0 ≤ ∑ m ∈ Finset.range (N + 1),
      (Real.exp (z * m) * partitionOn φ A m β) *
        (Real.exp (z * ((N - m : ℕ) : ℝ)) * partitionOn φ D (N - m) β) := by
    apply Finset.sum_nonneg
    intro m _
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (partitionOn_nonneg φ A m β))
      (mul_nonneg (Real.exp_pos _).le (partitionOn_nonneg φ D (N - m) β))
  rw [grandOn, grandOn,
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hsA.norm hsD.norm]
  exact (Summable.of_nonneg_of_le hnn hcov hsU).tsum_le_tsum hcov hsU

theorem grandOn_mono {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B β : ℝ} (hstable : StableWith φ B) (hβ : 0 ≤ β) {A D : Set Position}
    (hsub : A ⊆ D) (hDfin : volume D ≠ ⊤) (z : ℝ) : grandOn φ A β z ≤ grandOn φ D β z := by
  have hAfin : volume A ≠ ⊤ := (measure_mono hsub).trans_lt hDfin.lt_top |>.ne
  exact (grandOn_summable hφ hb hstable hβ hAfin z).tsum_le_tsum
    (fun N => mul_le_mul_of_nonneg_left (partitionOn_mono hφ hb β N hsub hDfin) (Real.exp_pos _).le)
    (grandOn_summable hφ hb hstable hβ hDfin z)

theorem grandOn_translate (φ : Potential) (A : Set Position) (a : Position) (β z : ℝ) :
    grandOn φ (translateSet a A) β z = grandOn φ A β z := by
  simp only [grandOn, partitionOn_translate]

theorem grandOn_cube (φ : Potential) (L t β h : ℝ) :
    grandOn φ (cube L) β (t * h) = grandPartition φ t L β h := by
  simp only [grandOn, grandPartition, partitionOn_cube]

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_SpatialReplication
attribute [-instance] _root_.OAI.RadialTransition.instMeasurableSpaceParticleState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uIndex

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem volume_translateSet (A : Set Position) (a : Position) (hA : MeasurableSet A) :
    volume (translateSet a A) = volume A := by
  exact (measurePreserving_sub_right volume a).measure_preimage hA.nullMeasurableSet

theorem measurableSet_boxRegion {n : ℕ} (s : ℝ) (j : Fin 3 → Fin n) :
    MeasurableSet (boxRegion s j) := measurableSet_translate (measurableSet_cube s)

theorem volume_boxRegion {n : ℕ} (s : ℝ) (j : Fin 3 → Fin n) :
    volume (boxRegion s j) = ENNReal.ofReal s ^ 3 := by
  rw [boxRegion, volume_translateSet _ _ (measurableSet_cube s), volume_cube]

theorem boxRegion_subset_cube {n : ℕ} {s L : ℝ} (hs : 0 ≤ s)
    (hn : (n : ℝ) * (s + 2) ≤ L) (j : Fin 3 → Fin n) : boxRegion s j ⊆ cube L := by
  intro x hx k
  have hxx : ∀ k, 0 ≤ x k - (j k : ℝ) * (s + 2) ∧
      x k - (j k : ℝ) * (s + 2) ≤ s := hx
  have hj : (j k : ℝ) + 1 ≤ n := by exact_mod_cast (j k).isLt
  have hj0 : 0 ≤ (j k : ℝ) := by positivity
  have hp := mul_le_mul_of_nonneg_right hj (show 0 ≤ s + 2 by linarith)
  have hp0 : 0 ≤ (j k : ℝ) * (s + 2) := mul_nonneg hj0 (by linarith)
  exact ⟨by linarith [(hxx k).1], by linarith [(hxx k).2]⟩

theorem boxRegion_dist {n : ℕ} {s : ℝ} (hs : 0 ≤ s) {j k : Fin 3 → Fin n}
    (hjk : j ≠ k) {x y : Position} (hx : x ∈ boxRegion s j) (hy : y ∈ boxRegion s k) :
    2 ≤ dist x y := by
  have hc {j k : Fin 3 → Fin n} {x y : Position} (q : Fin 3) (hq : j q < k q)
      (hx : x ∈ boxRegion s j) (hy : y ∈ boxRegion s k) : 2 ≤ dist x y := by
    have hq' : (j q : ℝ) + 1 ≤ (k q : ℝ) := by exact_mod_cast hq
    have hp := mul_le_mul_of_nonneg_right hq' (show 0 ≤ s + 2 by linarith)
    have hx' : x q - (j q : ℝ) * (s + 2) ≤ s := (hx q).2
    have hy' : 0 ≤ y q - (k q : ℝ) * (s + 2) := (hy q).1
    have hh : 2 ≤ y q - x q := by linarith
    calc
      2 ≤ y q - x q := hh
      _ ≤ |y q - x q| := le_abs_self _
      _ ≤ ‖y - x‖ := by simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (y - x) q
      _ = dist x y := by rw [← dist_eq_norm, dist_comm]
  obtain ⟨q, hq⟩ := Function.ne_iff.mp hjk
  rcases lt_or_gt_of_ne hq with h | h
  · exact hc q h hx hy
  · simpa only [dist_comm] using hc q h hy hx

theorem boxRegion_disjoint {n : ℕ} {s : ℝ} (hs : 0 ≤ s) {j k : Fin 3 → Fin n}
    (hjk : j ≠ k) : Disjoint (boxRegion s j) (boxRegion s k) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hh := boxRegion_dist hs hjk hx hy
  norm_num at hh

theorem grandOn_biUnion_lower {ι : Type uIndex} [DecidableEq ι]
    {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B β : ℝ} (hstable : StableWith φ B) (hβ : 0 ≤ β)
    (S : Finset ι) (A : ι → Set Position) (z : ℝ)
    (hA : ∀ i ∈ S, MeasurableSet (A i)) (hAfin : ∀ i ∈ S, volume (A i) ≠ ⊤)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (A i) (A j))
    (hc : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, φ (nndist x y) ≤ 0) :
    (∏ i ∈ S, grandOn φ (A i) β z) ≤ grandOn φ (⋃ i ∈ S, A i) β z := by
  induction S using Finset.induction_on with
  | empty =>
    simpa using (grandOn_bounds hφ hb hstable hβ (by simp : volume (∅ : Set Position) ≠ ⊤) z).1
  | @insert i S hi ih =>
    have hAs : ∀ j ∈ S, MeasurableSet (A j) := fun j hj => hA j (Finset.mem_insert_of_mem hj)
    have hfins : ∀ j ∈ S, volume (A j) ≠ ⊤ := fun j hj => hAfin j (Finset.mem_insert_of_mem hj)
    have hU : MeasurableSet (⋃ j ∈ S, A j) := Finset.measurableSet_biUnion S hAs
    have hUfin : volume (⋃ j ∈ S, A j) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr hfins) (measure_biUnion_finset_le S A)
    have hdU : Disjoint (A i) (⋃ j ∈ S, A j) := by
      simp only [Set.disjoint_iUnion_right]
      intro j hj
      exact hdisj i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (by rintro rfl; exact hi hj)
    have hcU : ∀ x ∈ A i, ∀ y ∈ ⋃ j ∈ S, A j, φ (nndist x y) ≤ 0 := by
      intro x hx y hy
      obtain ⟨j, hj, hy⟩ := Set.mem_iUnion₂.mp hy
      exact hc i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (by rintro rfl; exact hi hj) x hx y hy
    have hi' := ih hAs hfins
      (fun j hj k hk hne => hdisj j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne)
      (fun j hj k hk hne => hc j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne)
    rw [Finset.prod_insert hi]
    have hnn := (grandOn_bounds hφ hb hstable hβ (hAfin i (Finset.mem_insert_self _ _)) z).1
    have hprod := mul_le_mul_of_nonneg_left hi' (show 0 ≤ grandOn φ (A i) β z by linarith)
    refine hprod.trans ?_
    have hu : (⋃ j ∈ insert i S, A j) = A i ∪ ⋃ j ∈ S, A j := by ext x; simp
    rw [hu]
    exact grandOn_union_lower hφ hb hstable hβ
      (hA i (Finset.mem_insert_self _ _)) hU hdU (hAfin i (Finset.mem_insert_self _ _)) hUfin hcU z

theorem partition_replication {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {β s L : ℝ} (hβ : 0 ≤ β) (hs : 0 ≤ s)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0) (n : ℕ)
    (hn : (n : ℝ) * (s + 2) ≤ L) (m : (Fin 3 → Fin n) → ℕ) :
    (∏ j, partition φ s (m j) β) ≤ partition φ L (∑ j, m j) β := by
  classical
  have hh := partitionOn_biUnion_lower Finset.univ (boxRegion s) hφ hb hβ
    (fun j _ => measurableSet_boxRegion s j)
    (fun j _ => by rw [volume_boxRegion]; finiteness)
    (fun _ _ _ _ hne => boxRegion_disjoint hs hne)
    (fun _ _ _ _ hne _ hx _ hy => hc _ (boxRegion_dist hs hne hx hy)) m
  have hsub : (⋃ j ∈ (Finset.univ : Finset (Fin 3 → Fin n)), boxRegion s j) ⊆ cube L := by
    intro x hx
    obtain ⟨j, _, hx⟩ := Set.mem_iUnion₂.mp hx
    exact boxRegion_subset_cube hs hn j hx
  have hh' := hh.trans (partitionOn_mono hφ hb β _ hsub (by rw [volume_cube]; finiteness))
  simpa only [boxRegion, partitionOn_translate, partitionOn_cube] using hh'

theorem grandPartition_replication {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B β s L : ℝ} (hstable : StableWith φ B) (hβ : 0 ≤ β) (hs : 0 ≤ s)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0) (n : ℕ)
    (hn : (n : ℝ) * (s + 2) ≤ L) (t h : ℝ) :
    grandPartition φ t s β h ^ (n ^ 3) ≤ grandPartition φ t L β h := by
  classical
  have hh := grandOn_biUnion_lower hφ hb hstable hβ Finset.univ (boxRegion s) (t * h)
    (fun j _ => measurableSet_boxRegion s j)
    (fun j _ => by rw [volume_boxRegion]; finiteness)
    (fun _ _ _ _ hne => boxRegion_disjoint hs hne)
    (fun _ _ _ _ hne _ hx _ hy => hc _ (boxRegion_dist hs hne hx hy))
  have hsub : (⋃ j ∈ (Finset.univ : Finset (Fin 3 → Fin n)), boxRegion s j) ⊆ cube L := by
    intro x hx
    obtain ⟨j, _, hx⟩ := Set.mem_iUnion₂.mp hx
    exact boxRegion_subset_cube hs hn j hx
  have hh' := hh.trans (grandOn_mono hφ hb hstable hβ hsub (by rw [volume_cube]; finiteness) (t * h))
  simpa only [boxRegion, grandOn_translate, grandOn_cube, Finset.prod_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using hh'

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_ThermodynamicLimit
attribute [-instance] _root_.OAI.RadialTransition.instIsCountablyGeneratedProdRealNatThermodynamicFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uIndex

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem separated_box_limit {F : ℝ → ℝ} {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hF0 : ∀ s, 0 ≤ s → 0 ≤ F s)
    (hFC : ∀ s, 0 ≤ s → F s ≤ C * s ^ 3)
    (hrep : ∀ (s L : ℝ) (n : ℕ), 0 ≤ s → (n : ℝ) * (s + δ) ≤ L →
      (n : ℝ) ^ 3 * F s ≤ F L) :
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ C ∧
      Tendsto (fun L : ℝ => F L / L ^ 3) atTop (nhds p) ∧
      ∀ s, 0 ≤ s → F s / (s + δ) ^ 3 ≤ p := by
  let S : Set ℝ := {r | ∃ s : ℝ, 0 ≤ s ∧ r = F s / (s + δ) ^ 3}
  have hnon : S.Nonempty := ⟨_, 0, le_rfl, rfl⟩
  have hbound : ∀ s, 0 ≤ s → F s / (s + δ) ^ 3 ≤ C := by
    intro s hs
    apply (div_le_iff₀ (by positivity : 0 < (s + δ) ^ 3)).mpr
    calc
      F s ≤ C * s ^ 3 := hFC s hs
      _ ≤ C * (s + δ) ^ 3 := by gcongr; linarith
  have hbd : BddAbove S := ⟨C, by rintro r ⟨s, hs, rfl⟩; exact hbound s hs⟩
  let p : ℝ := sSup S
  have hpC : p ≤ C := csSup_le hnon (by rintro r ⟨s, hs, rfl⟩; exact hbound s hs)
  have hsp (s : ℝ) (hs : 0 ≤ s) : F s / (s + δ) ^ 3 ≤ p := le_csSup hbd ⟨s, hs, rfl⟩
  have hp0 : 0 ≤ p := (div_nonneg (hF0 0 le_rfl) (by positivity)).trans (hsp 0 le_rfl)
  refine ⟨p, hp0, hpC, ?_, hsp⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨r, ⟨s, hs, rfl⟩, har⟩ := (lt_csSup_iff hbd hnon).mp ha
    have hlim : Tendsto (fun L : ℝ => ((⌊L / (s + δ)⌋₊ : ℝ) / L) ^ 3 * F s)
        atTop (nhds (F s / (s + δ) ^ 3)) := by
      have hh := ((tendsto_nat_floor_mul_div_atTop (show 0 ≤ (s + δ)⁻¹ by positivity)).pow 3).mul_const (F s)
      simpa only [div_eq_mul_inv, inv_pow, mul_comm] using hh
    filter_upwards [hlim.eventually_const_lt har, eventually_gt_atTop (0 : ℝ)] with L hlo hL
    have hn : (⌊L / (s + δ)⌋₊ : ℝ) * (s + δ) ≤ L :=
      (le_div_iff₀ (by positivity : 0 < s + δ)).mp (Nat.floor_le (by positivity))
    have hh := div_le_div_of_nonneg_right (hrep s L ⌊L / (s + δ)⌋₊ hs hn)
      (show 0 ≤ L ^ 3 by positivity)
    have heq : ((⌊L / (s + δ)⌋₊ : ℝ) / L) ^ 3 * F s =
        ((⌊L / (s + δ)⌋₊ : ℝ) ^ 3 * F s) / L ^ 3 := by ring
    exact hlo.trans_le (heq ▸ hh)
  · intro a ha
    have hlim : Tendsto (fun L : ℝ => p * (1 + δ * L⁻¹) ^ 3) atTop (nhds p) := by
      have hh := ((tendsto_const_nhds (x := (1 : ℝ))).add
        (tendsto_inv_atTop_zero.const_mul δ)).pow 3
      simpa using hh.const_mul p
    filter_upwards [hlim.eventually_lt_const ha, eventually_gt_atTop (0 : ℝ)] with L hhi hL
    apply lt_of_le_of_lt _ hhi
    apply (div_le_iff₀ (by positivity : 0 < L ^ 3)).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < (L + δ) ^ 3)).mp (hsp L hL.le)
    calc
      F L ≤ p * (L + δ) ^ 3 := hh
      _ = p * (1 + δ * L⁻¹) ^ 3 * L ^ 3 := by field_simp

theorem grandPressure_exists {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t β : ℝ} (hstable : StableWith φ B) (ht : 0 < t) (hβ : 0 ≤ β)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0) (h : ℝ) :
    ∃ p : ℝ, 0 ≤ p ∧ p ≤ Real.exp (β * B + t * h) / t ∧
      Tendsto (fun L : ℝ => Real.log (grandPartition φ t L β h) / (t * L ^ 3))
        atTop (nhds p) := by
  have hbnd (s : ℝ) (hs : 0 ≤ s) := grandPartition_bounds hφ hb hstable hs hβ t h
  obtain ⟨p, hp0, hpC, hlim, _⟩ := separated_box_limit
    (F := fun L => Real.log (grandPartition φ t L β h))
    (C := Real.exp (β * B + t * h)) (δ := 2) (Real.exp_pos _).le (by norm_num)
    (fun s hs => Real.log_nonneg (hbnd s hs).1)
    (fun s hs => by
      have hh := Real.log_le_log (show 0 < grandPartition φ t s β h by linarith [(hbnd s hs).1])
        (hbnd s hs).2
      simpa only [Real.log_exp, mul_comm] using hh)
    (fun s L n hs hn => by
      have hh := Real.log_le_log
        (pow_pos (show 0 < grandPartition φ t s β h by linarith [(hbnd s hs).1]) _)
        (grandPartition_replication hφ hb hstable hβ hs hc n hn t h)
      simpa only [Real.log_pow, Nat.cast_pow] using hh)
  refine ⟨p / t, div_nonneg hp0 ht.le, (div_le_div_of_nonneg_right hpC ht.le), ?_⟩
  simpa only [div_div, mul_comm] using hlim.div_const t

theorem exists_bounded_fill (k c E : ℕ) (hc : 0 < c) (hE : E ≤ k * c) :
    ∃ v : Fin k → ℕ, (∀ i, v i ≤ c) ∧ (∑ i, v i) = E ∧
      (Finset.univ.filter (fun i => v i ≠ 0)).card ≤ E / c + 1 := by
  classical
  let r := E / c
  let a := E % c
  have ha : a < c := Nat.mod_lt _ hc
  have hdecomp : r * c + a = E := by
    dsimp [r, a]
    simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div E c
  have hr : r ≤ k := by
    have hh : r * c ≤ k * c := by omega
    exact (mul_le_mul_iff_left₀ hc).mp (by simpa [Nat.mul_comm] using hh)
  let v : Fin k → ℕ := fun i => (if (i : ℕ) < r then c else 0) +
    (if (i : ℕ) = r then a else 0)
  have hv (i : Fin k) : v i ≤ c := by
    dsimp [v]
    split_ifs <;> omega
  have hsum1 : (∑ i : Fin k, if (i : ℕ) < r then c else 0) = r * c := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, Fin.card_filter_val_lt, min_eq_right hr, nsmul_eq_mul, Nat.cast_id]
  have hsum2 : (∑ i : Fin k, if (i : ℕ) = r then a else 0) = a := by
    by_cases hr' : r < k
    · let j : Fin k := ⟨r, hr'⟩
      have hiff (i : Fin k) : (i : ℕ) = r ↔ i = j := by
        exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      simp_rw [hiff]
      simp
    · have he : r = k := by omega
      have ha0 : a = 0 := by rw [he] at hdecomp; omega
      simp [ha0]
  have hcard : (Finset.univ.filter (fun i => v i ≠ 0)).card ≤ r + 1 := by
    have hsub : Finset.univ.filter (fun i => v i ≠ 0) ⊆
        Finset.univ.filter (fun i : Fin k => (i : ℕ) < r + 1) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      by_contra hh
      have hge : r + 1 ≤ (i : ℕ) := by omega
      simp [v, show ¬(i : ℕ) < r by omega, show (i : ℕ) ≠ r by omega] at hi
    exact (Finset.card_le_card hsub).trans (by rw [Fin.card_filter_val_lt]; exact min_le_right _ _)
  refine ⟨v, hv, ?_, hcard⟩
  simp only [v, Finset.sum_add_distrib, hsum1, hsum2]
  exact hdecomp

theorem exists_integer_adjustment (k m q n : ℕ) (hm : 0 < m) (hmq : m < q)
    (hn : n ≤ k * q) {c : ℝ} (hc : 0 < c) (hcm : c ≤ (m : ℝ))
    (hcq : c ≤ ((q - m : ℕ) : ℝ)) :
    ∃ f : Fin k → ℕ, (∑ i, f i) = n ∧ (∀ i, f i ≤ q) ∧
      ((Finset.univ.filter (fun i => f i ≠ m)).card : ℝ) ≤
        |(n : ℝ) - (k : ℝ) * m| / c + 1 := by
  classical
  by_cases hmn : k * m ≤ n
  · have hE : n - k * m ≤ k * (q - m) := by
      rw [Nat.mul_sub_left_distrib]
      exact Nat.sub_le_sub_right hn _
    obtain ⟨v, hv, hsv, hcv⟩ := exists_bounded_fill k (q - m) (n - k * m)
      (Nat.sub_pos_of_lt hmq) hE
    let f : Fin k → ℕ := fun i => m + v i
    have hs : (∑ i, f i) = n := by
      simp only [f, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, hsv]
      omega
    have he : (Finset.univ.filter (fun i => f i ≠ m)) =
        Finset.univ.filter (fun i => v i ≠ 0) := by
      ext i
      simp [f]
    refine ⟨f, hs, (fun i => by dsimp [f]; have := hv i; omega), ?_⟩
    rw [he]
    have hvreal : ((Finset.univ.filter (fun i => v i ≠ 0)).card : ℝ) ≤
        ((n - k * m) / (q - m) : ℕ) + 1 := by exact_mod_cast hcv
    have hdiv : (((n - k * m) / (q - m) : ℕ) : ℝ) ≤
        ((n - k * m : ℕ) : ℝ) / c := by
      apply Nat.cast_div_le.trans
      exact div_le_div_of_nonneg_left (by positivity) hc hcq
    have hdiff : ((n - k * m : ℕ) : ℝ) = |(n : ℝ) - (k : ℝ) * m| := by
      rw [Nat.cast_sub hmn, Nat.cast_mul, abs_of_nonneg]
      exact sub_nonneg.mpr (by exact_mod_cast hmn)
    rw [hdiff] at hdiv
    linarith
  · have hnkm : n ≤ k * m := by omega
    obtain ⟨v, hv, hsv, hcv⟩ := exists_bounded_fill k m (k * m - n) hm (Nat.sub_le _ _)
    let f : Fin k → ℕ := fun i => m - v i
    have hs : (∑ i, f i) = n := by
      dsimp [f]
      rw [Finset.sum_tsub_distrib _ (fun i _ => hv i), Finset.sum_const, hsv]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      omega
    have he : (Finset.univ.filter (fun i => f i ≠ m)) =
        Finset.univ.filter (fun i => v i ≠ 0) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, f]
      have hvi := hv i
      omega
    refine ⟨f, hs, (fun i => (Nat.sub_le _ _).trans hmq.le), ?_⟩
    rw [he]
    have hvreal : ((Finset.univ.filter (fun i => v i ≠ 0)).card : ℝ) ≤
        ((k * m - n) / m : ℕ) + 1 := by exact_mod_cast hcv
    have hdiv : (((k * m - n) / m : ℕ) : ℝ) ≤
        ((k * m - n : ℕ) : ℝ) / c := by
      apply Nat.cast_div_le.trans
      exact div_le_div_of_nonneg_left (by positivity) hc hcm
    have hdiff : ((k * m - n : ℕ) : ℝ) = |(n : ℝ) - (k : ℝ) * m| := by
      rw [Nat.cast_sub hnkm, Nat.cast_mul, abs_of_nonpos]
      · ring
      · exact sub_nonpos.mpr (by exact_mod_cast hnkm)
    rw [hdiff] at hdiv
    linarith

theorem sum_changed_cost {ι : Type uIndex} [Fintype ι] (f : ι → ℕ) (m : ℕ)
    (H : ℕ → ℝ) {K : ℝ} (hm : |H m| ≤ K) (hf : ∀ i, |H (f i)| ≤ K) :
    (∑ i, H (f i)) ≤ Fintype.card ι * H m +
      2 * K * (Finset.univ.filter (fun i => f i ≠ m)).card := by
  classical
  have hh : ∀ i, H (f i) ≤ H m + if f i ≠ m then 2 * K else 0 := by
    intro i
    split_ifs with hi
    · linarith [(abs_le.mp (hf i)).2, (abs_le.mp hm).1]
    · simp only [not_not] at hi
      simp [hi]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hs
  have he : (∑ i, if f i ≠ m then 2 * K else 0) =
      2 * K * (Finset.univ.filter (fun i => f i ≠ m)).card := by
    rw [← Finset.sum_filter, Finset.sum_const]
    simp only [nsmul_eq_mul]
    ring
  rwa [he] at hs

theorem finiteCanonical_replication {φ : Potential} (hφ : Continuous φ)
    (hb : IsBoundedPotential φ) {β t s L : ℝ} (hβ : 0 ≤ β) (ht : 0 < t)
    (hs : 0 < s) (hL : 0 < L)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0) (n : ℕ)
    (hn : (n : ℝ) * (s + 2) ≤ L) (m : Fin (n ^ 3) → ℕ) :
    finiteCanonical φ t L (∑ j, m j) β ≤
      s ^ 3 / L ^ 3 * ∑ j, finiteCanonical φ t s (m j) β := by
  classical
  let e : (Fin 3 → Fin n) ≃ Fin (n ^ 3) := Fintype.equivFinOfCardEq (by simp)
  have hp := partition_replication hφ hb hβ hs.le hc n hn (m ∘ e)
  have hsum : (∑ j, (m ∘ e) j) = ∑ j, m j := e.sum_comp m
  have hprod : (∏ j, partition φ s ((m ∘ e) j) β) =
      ∏ j, partition φ s (m j) β := e.prod_comp (fun j => partition φ s (m j) β)
  rw [hsum, hprod] at hp
  have hpos : ∀ j ∈ (Finset.univ : Finset (Fin (n ^ 3))), 0 < partition φ s (m j) β :=
    fun j _ => partition_pos hφ hb hs _ _
  have hlog := Real.log_le_log (Finset.prod_pos hpos) hp
  rw [Real.log_prod (fun j hj => (hpos j hj).ne')] at hlog
  have hpoint (j : Fin (n ^ 3)) : Real.log (partition φ s (m j) β) =
      -(t * s ^ 3) * finiteCanonical φ t s (m j) β := by
    dsimp only [finiteCanonical]
    field_simp
  simp_rw [hpoint] at hlog
  rw [← Finset.mul_sum] at hlog
  change -Real.log (partition φ L (∑ j, m j) β) / (t * L ^ 3) ≤ _
  rw [div_le_iff₀ (mul_pos ht (pow_pos hL 3))]
  have he : (s ^ 3 / L ^ 3 * ∑ j, finiteCanonical φ t s (m j) β) * (t * L ^ 3) =
      t * s ^ 3 * ∑ j, finiteCanonical φ t s (m j) β := by field_simp
  rw [he]
  linarith

theorem thermodynamicFilter_side (d : ℝ) :
    Tendsto Prod.fst (thermodynamicFilter d) atTop := by
  exact tendsto_comap.mono_left inf_le_left

theorem thermodynamicFilter_density (d : ℝ) :
    Tendsto (fun z : ℝ × ℕ => (z.2 : ℝ) / z.1 ^ 3)
      (thermodynamicFilter d) (nhds d) := by
  exact tendsto_comap.mono_left inf_le_right

theorem floor_density_tendsto {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun L : ℝ => (⌊d * L ^ 3⌋₊ : ℝ) / L ^ 3) atTop (nhds d) := by
  have hh := (tendsto_nat_floor_mul_div_atTop hd).comp (tendsto_pow_atTop (by norm_num : 3 ≠ 0))
  simpa only [Function.comp_def, mul_comm] using hh

theorem floor_tendsto_thermodynamicFilter {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun L : ℝ => (L, ⌊d * L ^ 3⌋₊)) atTop (thermodynamicFilter d) := by
  apply tendsto_inf.mpr
  constructor
  · exact tendsto_comap_iff.mpr tendsto_id
  · exact tendsto_comap_iff.mpr (floor_density_tendsto hd)

theorem thermodynamicFilter_neBot {d : ℝ} (hd : 0 ≤ d) : NeBot (thermodynamicFilter d) :=
  (floor_tendsto_thermodynamicFilter hd).neBot

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CanonicalLimit
attribute [-instance] _root_.OAI.RadialTransition.instMeasurableSpaceParticleState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem boxCost_adjustment {H : ℝ → ℕ → ℝ} (hrep : HasBoxReplication H)
    {s L : ℝ} (hs : 0 < s) (hL : 0 < L) (b m q N : ℕ)
    (hbL : (b : ℝ) * (s + 2) ≤ L) (hm : 0 < m) (hmq : m < q)
    (hN : N ≤ b ^ 3 * q) {c K : ℝ} (hc0 : 0 < c) (hcm : c ≤ (m : ℝ))
    (hcq : c ≤ ((q - m : ℕ) : ℝ)) (hK : 0 ≤ K)
    (hcost : ∀ j ≤ q, |H s j| ≤ K) :
    H L N ≤ s ^ 3 / L ^ 3 *
      ((b : ℝ) ^ 3 * H s m + 2 * K * (|(N : ℝ) - (b : ℝ) ^ 3 * m| / c + 1)) := by
  obtain ⟨f, hfN, hfq, hfc⟩ := exists_integer_adjustment (b ^ 3) m q N hm hmq hN hc0 hcm hcq
  have hr := hrep s L b hs hL hbL f
  rw [hfN] at hr
  have hsum := sum_changed_cost f m (H s) (hcost m hmq.le) (fun i => hcost (f i) (hfq i))
  simp only [Fintype.card_fin, Nat.cast_pow] at hsum hfc
  apply hr.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact hsum.trans (by gcongr)

theorem boxCost_limsup_bound {H : ℝ → ℕ → ℝ} (hrep : HasBoxReplication H)
    {d s c K : ℝ} (hd : 0 < d) (hs : 0 < s) (hc : 0 < c) (hK : 0 ≤ K)
    (m q : ℕ) (hm : 0 < m) (hmq : m < q)
    (hcm : c * s ^ 3 ≤ (m : ℝ)) (hcq : c * s ^ 3 ≤ ((q - m : ℕ) : ℝ))
    (hcap : d < (q : ℝ) / (s + 2) ^ 3) (hcost : ∀ j ≤ q, |H s j| ≤ K)
    (hbelow : IsBoundedUnder (· ≥ ·) (thermodynamicFilter d) (fun z => H z.1 z.2)) :
    limsup (fun z => H z.1 z.2) (thermodynamicFilter d) ≤
      (s / (s + 2)) ^ 3 * H s m +
        2 * K / c * |d - (s / (s + 2)) ^ 3 * ((m : ℝ) / s ^ 3)| := by
  let _ := thermodynamicFilter_neBot hd.le
  let F := thermodynamicFilter d
  let b (z : ℝ × ℕ) : ℕ := ⌊z.1 / (s + 2)⌋₊
  let r (z : ℝ × ℕ) : ℝ := ((b z : ℝ) / z.1) ^ 3
  have hr : Tendsto r F (nhds ((s + 2)⁻¹ ^ 3)) := by
    have hh := ((tendsto_nat_floor_mul_div_atTop
      (show 0 ≤ (s + 2)⁻¹ by positivity)).pow 3).comp (thermodynamicFilter_side d)
    simpa only [r, b, Function.comp_def, div_eq_mul_inv, mul_comm] using hh
  have hden : Tendsto (fun z : ℝ × ℕ => (z.1 ^ 3)⁻¹) F (nhds 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp
      (thermodynamicFilter_side d))
  let G (z : ℝ × ℕ) : ℝ := s ^ 3 * (r z * H s m +
    2 * K * (|(z.2 : ℝ) / z.1 ^ 3 - r z * m| / (c * s ^ 3) + (z.1 ^ 3)⁻¹))
  have hG : Tendsto G F (nhds (s ^ 3 * ((s + 2)⁻¹ ^ 3 * H s m +
      2 * K * (|d - (s + 2)⁻¹ ^ 3 * m| / (c * s ^ 3))))) := by
    have hh := ((hr.mul_const (H s m)).add
      (((((thermodynamicFilter_density d).sub (hr.mul_const (m : ℝ))).abs.div_const
        (c * s ^ 3)).add hden).const_mul (2 * K))).const_mul (s ^ 3)
    simpa only [add_zero] using hh
  have hcaplimit : Tendsto (fun z => r z * q) F (nhds ((q : ℝ) / (s + 2) ^ 3)) := by
    simpa only [inv_pow, div_eq_mul_inv, mul_comm] using hr.mul_const (q : ℝ)
  obtain ⟨a, hda, haq⟩ := exists_between hcap
  have hN : ∀ᶠ z in F, (z.2 : ℝ) / z.1 ^ 3 < r z * q := by
    filter_upwards [(thermodynamicFilter_density d).eventually_lt_const hda,
      hcaplimit.eventually_const_lt haq] with z hz hq
    exact hz.trans hq
  have hle : ∀ᶠ z in F, H z.1 z.2 ≤ G z := by
    filter_upwards [hN, (thermodynamicFilter_side d).eventually (eventually_gt_atTop (0 : ℝ))]
      with z hNz hL
    have hbL : (b z : ℝ) * (s + 2) ≤ z.1 :=
      (le_div_iff₀ (by positivity : 0 < s + 2)).mp (Nat.floor_le (by positivity))
    have hNe : z.2 ≤ b z ^ 3 * q := by
      have he : r z * q = ((b z : ℝ) ^ 3 * q) / z.1 ^ 3 := by dsimp [r]; ring
      rw [he] at hNz
      have hh := (div_lt_div_iff_of_pos_right (pow_pos hL 3)).mp hNz
      exact_mod_cast hh.le
    have hh := boxCost_adjustment hrep hs hL (b z) m q z.2 hbL hm hmq hNe
      (mul_pos hc (pow_pos hs 3)) hcm hcq hK hcost
    apply hh.trans_eq
    have habs : |(z.2 : ℝ) / z.1 ^ 3 - r z * m| =
        |(z.2 : ℝ) - (b z : ℝ) ^ 3 * m| / z.1 ^ 3 := by
      dsimp only [r]
      rw [div_pow, div_mul_eq_mul_div, ← sub_div, abs_div, abs_of_pos (pow_pos hL 3)]
    dsimp only [G]
    rw [habs]
    dsimp only [r]
    ring
  have hh := limsup_le_limsup hle hbelow.isCobounded_le hG.isBoundedUnder_le
  rw [hG.limsup_eq] at hh
  apply hh.trans_eq
  field_simp

theorem tendsto_side_ratio :
    Tendsto (fun s : ℝ => s / (s + 2)) atTop (nhds 1) := by
  have hh := ((tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_id)).const_mul 2).const_sub 1
  simp only [mul_zero, sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  simp only [Function.comp_def, id_eq]
  field_simp
  ring

theorem boxCost_limit {H : ℝ → ℕ → ℝ} (hrep : HasBoxReplication H)
    (hbnd : ∀ D : ℝ, 0 < D → ∃ K : ℝ, 0 ≤ K ∧
      ∀ s : ℝ, 1 ≤ s → ∀ n : ℕ, (n : ℝ) / s ^ 3 ≤ D → |H s n| ≤ K)
    {d : ℝ} (hd : 0 < d) :
    ∃ A : ℝ, Tendsto (fun z : ℝ × ℕ => H z.1 z.2) (thermodynamicFilter d) (nhds A) := by
  let _ := thermodynamicFilter_neBot hd.le
  obtain ⟨K, hK, hbound⟩ := hbnd (2 * d) (by positivity)
  have hevent : ∀ᶠ z in thermodynamicFilter d, |H z.1 z.2| ≤ K := by
    filter_upwards [(thermodynamicFilter_side d).eventually (eventually_ge_atTop (1 : ℝ)),
      (thermodynamicFilter_density d).eventually_lt_const (show d < 2 * d by linarith)]
      with z hz hdens
    exact hbound z.1 hz z.2 hdens.le
  have hbelow : IsBoundedUnder (· ≥ ·) (thermodynamicFilter d) (fun z => H z.1 z.2) :=
    ⟨-K, hevent.mono (fun z hz => (abs_le.mp hz).1)⟩
  have habove : IsBoundedUnder (· ≤ ·) (thermodynamicFilter d) (fun z => H z.1 z.2) :=
    ⟨K, hevent.mono (fun z hz => (abs_le.mp hz).2)⟩
  let A := liminf (fun z => H z.1 z.2) (thermodynamicFilter d)
  obtain ⟨x, hxH, hx⟩ := exists_seq_tendsto_liminf habove.isCobounded_ge hbelow
  let s (j : ℕ) := (x j).1
  let m (j : ℕ) := (x j).2
  let q (j : ℕ) : ℕ := ⌊2 * d * s j ^ 3⌋₊
  have hs : Tendsto s atTop atTop := (thermodynamicFilter_side d).comp hx
  have hm : Tendsto (fun j => (m j : ℝ) / s j ^ 3) atTop (nhds d) :=
    (thermodynamicFilter_density d).comp hx
  have hq : Tendsto (fun j => (q j : ℝ) / s j ^ 3) atTop (nhds (2 * d)) :=
    (floor_density_tendsto (show 0 ≤ 2 * d by positivity)).comp hs
  have hratio := tendsto_side_ratio.comp hs
  have hcap : Tendsto (fun j => (q j : ℝ) / (s j + 2) ^ 3) atTop (nhds (2 * d)) := by
    have hh := hq.mul (hratio.pow 3)
    simp only [one_pow, mul_one] at hh
    apply hh.congr'
    filter_upwards [hs.eventually (eventually_gt_atTop (0 : ℝ))] with j hj
    simp only [Function.comp_def]
    field_simp
  have hdiff : Tendsto (fun j => ((q j : ℝ) - m j) / s j ^ 3) atTop (nhds d) := by
    have hh := hq.sub hm
    simp only [← sub_div] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have href : ∀ᶠ j in atTop,
      limsup (fun z => H z.1 z.2) (thermodynamicFilter d) ≤
        (s j / (s j + 2)) ^ 3 * H (s j) (m j) +
          2 * K / (d / 2) * |d - (s j / (s j + 2)) ^ 3 * ((m j : ℝ) / s j ^ 3)| := by
    filter_upwards [hs.eventually (eventually_ge_atTop (1 : ℝ)),
      hm.eventually_const_lt (show d / 2 < d by linarith),
      hdiff.eventually_const_lt (show d / 2 < d by linarith),
      hcap.eventually_const_lt (show d < 2 * d by linarith)] with j hsj hmj hdiffj hcapj
    have hsj0 : 0 < s j := by linarith
    have hcm : d / 2 * s j ^ 3 < (m j : ℝ) :=
      (lt_div_iff₀ (pow_pos hsj0 3)).mp hmj
    have hcq : d / 2 * s j ^ 3 < (q j : ℝ) - m j :=
      (lt_div_iff₀ (pow_pos hsj0 3)).mp hdiffj
    have hm0 : 0 < m j := by
      have hh : (0 : ℝ) < m j := (by positivity : (0 : ℝ) < d / 2 * s j ^ 3).trans hcm
      exact_mod_cast hh
    have hmq : m j < q j := by
      have hh : (m j : ℝ) < q j := by linarith [show 0 < d / 2 * s j ^ 3 by positivity]
      exact_mod_cast hh
    apply boxCost_limsup_bound hrep hd hsj0 (show 0 < d / 2 by positivity) hK (m j) (q j)
      hm0 hmq hcm.le
    · rw [Nat.cast_sub hmq.le]
      exact hcq.le
    · exact hcapj
    · intro n hn
      apply hbound (s j) hsj n
      apply (div_le_iff₀ (pow_pos hsj0 3)).mpr
      exact (show (n : ℝ) ≤ q j by exact_mod_cast hn).trans (Nat.floor_le (by positivity))
    · exact hbelow
  have hlim : Tendsto (fun j => (s j / (s j + 2)) ^ 3 * H (s j) (m j) +
      2 * K / (d / 2) * |d - (s j / (s j + 2)) ^ 3 * ((m j : ℝ) / s j ^ 3)|)
      atTop (nhds A) := by
    have hh := ((hratio.pow 3).mul hxH).add
      ((((hratio.pow 3).mul hm).const_sub d).abs.const_mul (2 * K / (d / 2)))
    simpa only [one_pow, one_mul, sub_self, abs_zero, mul_zero, add_zero, Function.comp_def, s, m, A] using hh
  refine ⟨A, tendsto_of_le_liminf_of_limsup_le le_rfl ?_ habove hbelow⟩
  exact ge_of_tendsto hlim href

theorem boxCost_limit_with_bounds {H : ℝ → ℕ → ℝ} (hrep : HasBoxReplication H)
    {l u : ℝ → ℝ} (hl : Continuous l) (hu : Continuous u) (hzero : l 0 = u 0)
    (hb : ∀ s : ℝ, 1 ≤ s → ∀ n : ℕ,
      l ((n : ℝ) / s ^ 3) ≤ H s n ∧ H s n ≤ u ((n : ℝ) / s ^ 3))
    {d : ℝ} (hd : 0 ≤ d) :
    ∃ A : ℝ, Tendsto (fun z : ℝ × ℕ => H z.1 z.2) (thermodynamicFilter d) (nhds A) ∧
      l d ≤ A ∧ A ≤ u d := by
  let _ := thermodynamicFilter_neBot hd
  have hlo : Tendsto (fun z : ℝ × ℕ => l ((z.2 : ℝ) / z.1 ^ 3))
      (thermodynamicFilter d) (nhds (l d)) := hl.continuousAt.tendsto.comp (thermodynamicFilter_density d)
  have hup : Tendsto (fun z : ℝ × ℕ => u ((z.2 : ℝ) / z.1 ^ 3))
      (thermodynamicFilter d) (nhds (u d)) := hu.continuousAt.tendsto.comp (thermodynamicFilter_density d)
  have hevent : ∀ᶠ z in thermodynamicFilter d,
      l ((z.2 : ℝ) / z.1 ^ 3) ≤ H z.1 z.2 ∧ H z.1 z.2 ≤ u ((z.2 : ℝ) / z.1 ^ 3) := by
    filter_upwards [(thermodynamicFilter_side d).eventually (eventually_ge_atTop (1 : ℝ))] with z hz
    exact hb z.1 hz z.2
  obtain rfl | hdpos := hd.eq_or_lt
  · refine ⟨l 0, ?_, le_rfl, hzero.le⟩
    rw [← hzero] at hup
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
      (hevent.mono (fun _ hz => hz.1)) (hevent.mono (fun _ hz => hz.2))
  · have hlocal : ∀ D : ℝ, 0 < D → ∃ K : ℝ, 0 ≤ K ∧
        ∀ s : ℝ, 1 ≤ s → ∀ n : ℕ, (n : ℝ) / s ^ 3 ≤ D → |H s n| ≤ K := by
      intro D _
      obtain ⟨Cl, hCl⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) D) hl.continuousOn
      obtain ⟨Cu, hCu⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) D) hu.continuousOn
      refine ⟨max 0 (max Cl Cu), le_max_left _ _, ?_⟩
      intro s hs n hn
      have hds : (n : ℝ) / s ^ 3 ∈ Icc (0 : ℝ) D := ⟨by positivity, hn⟩
      have hll : |l ((n : ℝ) / s ^ 3)| ≤ max 0 (max Cl Cu) := by
        have hh := hCl _ hds
        rw [Real.norm_eq_abs] at hh
        exact hh.trans ((le_max_left _ _).trans (le_max_right _ _))
      have huu : |u ((n : ℝ) / s ^ 3)| ≤ max 0 (max Cl Cu) := by
        have hh := hCu _ hds
        rw [Real.norm_eq_abs] at hh
        exact hh.trans ((le_max_right _ _).trans (le_max_right _ _))
      exact abs_le.mpr ⟨(abs_le.mp hll).1.trans (hb s hs n).1,
        (hb s hs n).2.trans (abs_le.mp huu).2⟩
    obtain ⟨A, hA⟩ := boxCost_limit hrep hlocal hdpos
    exact ⟨A, hA, le_of_tendsto_of_tendsto hlo hA (hevent.mono (fun _ hz => hz.1)),
      le_of_tendsto_of_tendsto hA hup (hevent.mono (fun _ hz => hz.2))⟩

theorem finiteCanonical_limit {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {t β c B K : ℝ} (ht : 0 < t) (hβ : 0 ≤ β)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0)
    (hlow : ∀ L : ℝ, 1 ≤ L → ∀ (N : ℕ) (x : Fin N → Position),
      x ∈ configurationCube L N → c * (N : ℝ)^2 / L^3 - B * N ≤ energy φ x)
    (hmean : ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ,
      (∫ x : Fin N → Position, energy φ x
        ∂MeasureTheory.Measure.pi (fun _ : Fin N => cubeProbability L)) ≤ K * (N : ℝ)^2 / L^3)
    {d : ℝ} (hd : 0 ≤ d) :
    ∃ A : ℝ, Tendsto (fun z : ℝ × ℕ => finiteCanonical φ t z.1 z.2 β)
        (thermodynamicFilter d) (nhds A) ∧
      β / t * (c * d ^ 2 - B * d) + (d * Real.log d - d) / t ≤ A ∧
      A ≤ β / t * K * d ^ 2 + d * Real.log d / t := by
  apply boxCost_limit_with_bounds (H := fun L N => finiteCanonical φ t L N β) (d := d)
    (fun s L b hs hL hbL m => finiteCanonical_replication hφ hb hβ ht hs hL hc b hbL m)
    (l := fun d => β / t * (c * d ^ 2 - B * d) + (d * Real.log d - d) / t)
    (u := fun d => β / t * K * d ^ 2 + d * Real.log d / t)
  · fun_prop (disch := exact Real.continuous_mul_log)
  · fun_prop (disch := exact Real.continuous_mul_log)
  · simp
  · intro L hL N
    exact finiteCanonical_bounds hφ hb (by linarith) ht hβ N (hlow L hL N) (hmean L hL N)
  · exact hd

theorem canonicalThermo_spec {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {t β c B K : ℝ} (ht : 0 < t) (hβ : 0 ≤ β)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0)
    (hlow : ∀ L : ℝ, 1 ≤ L → ∀ (N : ℕ) (x : Fin N → Position),
      x ∈ configurationCube L N → c * (N : ℝ)^2 / L^3 - B * N ≤ energy φ x)
    (hmean : ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ,
      (∫ x : Fin N → Position, energy φ x
        ∂MeasureTheory.Measure.pi (fun _ : Fin N => cubeProbability L)) ≤ K * (N : ℝ)^2 / L^3)
    {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun z : ℝ × ℕ => finiteCanonical φ t z.1 z.2 β)
        (thermodynamicFilter d) (nhds (canonicalThermo φ t β d)) ∧
      β / t * (c * d ^ 2 - B * d) + (d * Real.log d - d) / t ≤ canonicalThermo φ t β d ∧
      canonicalThermo φ t β d ≤ β / t * K * d ^ 2 + d * Real.log d / t := by
  let _ := thermodynamicFilter_neBot hd
  obtain ⟨A, hA, hlo, hhi⟩ := finiteCanonical_limit hφ hb ht hβ hc hlow hmean hd
  have he : canonicalThermo φ t β d = A := hA.liminf_eq
  rw [he]
  exact ⟨hA, hlo, hhi⟩

theorem familyCanonicalThermo_spec {t β d : ℝ} {a R : ℕ → ℝ} (ht : 1 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a)
    (hcoerc : 2197 * t * bumpIntegral⁻¹ * (∑' n, a n) / 2 ≤ t ^ 2 / 16)
    (hβ : 0 ≤ β) (hd : 0 ≤ d) :
    Tendsto (fun z : ℝ × ℕ => finiteCanonical (familyPotential t a R) t z.1 z.2 β)
        (thermodynamicFilter d) (nhds (canonicalThermo (familyPotential t a R) t β d)) ∧
      β / t * (t ^ 2 / 3456 * d ^ 2 - t ^ 2 / 2 * d) +
        (d * Real.log d - d) / t ≤ canonicalThermo (familyPotential t a R) t β d ∧
      canonicalThermo (familyPotential t a R) t β d ≤
        β / t * coreIntegral t * d ^ 2 + d * Real.log d / t := by
  apply canonicalThermo_spec (continuous_familyPotential ha hR hs t)
    (bounded_familyPotential ha hR hs t) (by linarith) hβ
    (fun _ hr => familyPotential_nonpos_outer ha hR ht hr)
  · intro L hL N x hx
    exact family_density_stability (by linarith) hL ha hR hs hcoerc x hx
  · intro L hL N
    exact probability_energy_family_upper ht ha hR hs (by linarith) N
  · exact hd

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_DensityMixtures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem grandPressure_spec {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t β : ℝ} (hstable : StableWith φ B) (ht : 0 < t) (hβ : 0 ≤ β)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0) (h : ℝ) :
    Tendsto (fun L : ℝ => finiteGrandPressure φ t L β h) atTop (nhds (grandPressure φ t β h)) ∧
      0 ≤ grandPressure φ t β h ∧ grandPressure φ t β h ≤ Real.exp (β * B + t * h) / t := by
  obtain ⟨p, hp0, hpB, hlim⟩ := grandPressure_exists hφ hb hstable ht hβ hc h
  have he : grandPressure φ t β h = p := hlim.limsup_eq
  rw [he]
  exact ⟨hlim, hp0, hpB⟩

theorem finiteGrandPressure_convex_mix {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t L β γ a b : ℝ} (hstable : StableWith φ B) (ht : 0 < t) (hL : 0 < L)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (h j : ℝ) (ha : 0 ≤ a) (hbb : 0 ≤ b) (hab : a + b = 1) :
    finiteGrandPressure φ t L (a * β + b * γ) (a * h + b * j) ≤
      a * finiteGrandPressure φ t L β h + b * finiteGrandPressure φ t L γ j := by
  have hmix : 0 ≤ a * β + b * γ := by positivity
  have hh := log_tsum_convex_mix ha hbb hab
    (grandPartition_summable hφ hb hstable hL.le hmix t (a * h + b * j))
    (grandPartition_summable hφ hb hstable hL.le hβ t h)
    (grandPartition_summable hφ hb hstable hL.le hγ t j)
    (fun n => mul_pos (Real.exp_pos _) (partition_pos hφ hb hL n _))
    (fun n => mul_pos (Real.exp_pos _) (partition_pos hφ hb hL n _))
    (fun n => mul_pos (Real.exp_pos _) (partition_pos hφ hb hL n _))
    (fun n => by
      simp only [Real.log_mul (Real.exp_ne_zero _) (partition_pos hφ hb hL n _).ne', Real.log_exp]
      have hh := log_partition_convex_mix hφ hb hL n β γ ha hbb hab
      nlinarith)
  dsimp only [finiteGrandPressure]
  have hh' := div_le_div_of_nonneg_right hh (show 0 ≤ t * L ^ 3 by positivity)
  simpa only [grandPartition, add_div, mul_div_assoc] using hh'

theorem grandPressure_convex_mix {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t β γ a b : ℝ} (hstable : StableWith φ B) (ht : 0 < t)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (h j : ℝ) (ha : 0 ≤ a) (hbb : 0 ≤ b) (hab : a + b = 1) :
    grandPressure φ t (a * β + b * γ) (a * h + b * j) ≤
      a * grandPressure φ t β h + b * grandPressure φ t γ j := by
  have hl := (grandPressure_spec hφ hb hstable ht (β := a * β + b * γ) (by positivity) hc (a * h + b * j)).1
  have hr := ((grandPressure_spec hφ hb hstable ht hβ hc h).1.const_mul a).add
    ((grandPressure_spec hφ hb hstable ht hγ hc j).1.const_mul b)
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  exact finiteGrandPressure_convex_mix hφ hb hstable ht hL hβ hγ h j ha hbb hab

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_CanonicalDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem canonical_le_grand_dual {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t β d : ℝ} (hstable : StableWith φ B) (ht : 0 < t) (hβ : 0 ≤ β) (hd : 0 ≤ d)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0)
    (hlim : Tendsto (fun z : ℝ × ℕ => finiteCanonical φ t z.1 z.2 β)
      (thermodynamicFilter d) (nhds (canonicalThermo φ t β d))) (h : ℝ) :
    h * d - canonicalThermo φ t β d ≤ grandPressure φ t β h := by
  have hH := hlim.comp (floor_tendsto_thermodynamicFilter hd)
  have hlo := ((floor_density_tendsto hd).const_mul h).sub hH
  have hhi := (grandPressure_spec hφ hb hstable ht hβ hc h).1
  apply le_of_tendsto_of_tendsto hlo hhi
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  let n : ℕ := ⌊d * L ^ 3⌋₊
  have hterm := (grandPartition_summable hφ hb hstable hL.le hβ t h).le_tsum n
    (fun N _ => mul_nonneg (Real.exp_pos _).le (partition_nonneg L N β))
  have hh := Real.log_le_log (mul_pos (Real.exp_pos _) (partition_pos hφ hb hL n β)) hterm
  rw [Real.log_mul (Real.exp_ne_zero _) (partition_pos hφ hb hL n β).ne', Real.log_exp] at hh
  have hden : 0 < t * L ^ 3 := by positivity
  change h * ((n : ℝ) / L ^ 3) - finiteCanonical φ t L n β ≤ finiteGrandPressure φ t L β h
  dsimp only [finiteGrandPressure, finiteCanonical]
  apply (le_div_iff₀ hden).mpr
  have he : (h * ((n : ℝ) / L ^ 3) - -Real.log (partition φ L n β) / (t * L ^ 3)) *
      (t * L ^ 3) = t * h * n + Real.log (partition φ L n β) := by field_simp; ring
  rw [he]
  exact hh

theorem grandPartition_tail_le_one {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t L β h D : ℝ} (hstable : StableWith φ B) (ht : 0 < t) (hL : 0 ≤ L)
    (hβ : 0 ≤ β) (hD : Real.exp (β * B + t * h + 1) ≤ D) :
    (∑' n : {n : ℕ // ⌊D * L ^ 3⌋₊ < n},
      Real.exp (t * h * (n : ℕ)) * partition φ L n β) ≤ 1 := by
  have hD0 : 0 < D := (Real.exp_pos _).trans_le hD
  let m := ⌊D * L ^ 3⌋₊
  let h' := h + t⁻¹
  have hs := grandPartition_summable hφ hb hstable hL hβ t h'
  have hfac : Summable (fun n : ℕ => Real.exp (-D * L ^ 3) *
      (Real.exp (t * h' * n) * partition φ L n β)) := hs.mul_left _
  have hsub := (grandPartition_summable hφ hb hstable hL hβ t h).subtype (fun n => m < n)
  have hh (n : {n : ℕ // m < n}) :
      Real.exp (t * h * (n : ℕ)) * partition φ L n β ≤
      Real.exp (-D * L ^ 3) * (Real.exp (t * h' * (n : ℕ)) * partition φ L n β) := by
    have hn : D * L ^ 3 < (n : ℕ) := (Nat.floor_lt (by positivity)).mp n.property
    have hfield : t * h' = t * h + 1 := by dsimp [h']; field_simp
    rw [← mul_assoc, ← Real.exp_add, hfield]
    apply mul_le_mul_of_nonneg_right _ (partition_nonneg L n β)
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsum := hsub.tsum_le_tsum hh (hfac.subtype (fun n => m < n))
  have hsuble := Summable.tsum_subtype_le _ {n : ℕ | m < n}
    (fun n => mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.exp_pos _).le (partition_nonneg L n β))) hfac
  have hh' := hsum.trans hsuble
  rw [tsum_mul_left] at hh'
  have hbound := mul_le_mul_of_nonneg_left
    (grandPartition_bounds hφ hb hstable hL hβ t h').2 (Real.exp_pos (-D * L ^ 3)).le
  have heq : β * B + t * h' = β * B + t * h + 1 := by dsimp [h']; field_simp; ring
  rw [heq, ← Real.exp_add] at hbound
  apply hh'.trans (hbound.trans _)
  apply Real.exp_le_one_iff.mpr
  nlinarith [pow_nonneg hL (3 : ℕ)]

theorem finiteGrandPressure_max_term {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t L β h D : ℝ} (hstable : StableWith φ B) (ht : 0 < t) (hL : 1 ≤ L)
    (hβ : 0 ≤ β) (hD : Real.exp (β * B + t * h + 1) ≤ D) :
    ∃ n : ℕ, (n : ℝ) / L ^ 3 ∈ Icc 0 D ∧
      finiteGrandPressure φ t L β h ≤
        h * ((n : ℝ) / L ^ 3) - finiteCanonical φ t L n β +
          Real.log ((D + 2) * L ^ 3) / (t * L ^ 3) := by
  classical
  have hL0 : 0 < L := by linarith
  have hD0 : 0 < D := (Real.exp_pos _).trans_le hD
  let m := ⌊D * L ^ 3⌋₊
  let F (n : ℕ) := Real.exp (t * h * n) * partition φ L n β
  have hs : Summable F := grandPartition_summable hφ hb hstable hL0.le hβ t h
  obtain ⟨n, hn, hnmax⟩ := (Finset.range (m+1)).exists_max_image F (by simp)
  have hnle : n ≤ m := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
  have hnD : (n : ℝ) ≤ D * L ^ 3 :=
    (by exact_mod_cast hnle : (n : ℝ) ≤ m).trans (Nat.floor_le (by positivity))
  have hge1 : 1 ≤ F n := by
    have hh := hnmax 0 (by simp)
    simpa [F, partition_zero] using hh
  have htail : (∑' k : {k : ℕ // k ∉ Finset.range (m+1)}, F k) ≤ 1 := by
    let e : {k : ℕ // k ∉ Finset.range (m+1)} ≃ {k : ℕ // m < k} :=
      Equiv.subtypeEquivProp (by funext k; apply propext; simp)
    have he := e.tsum_eq (fun k => F k)
    change (∑' k : {k : ℕ // k ∉ Finset.range (m+1)}, F k) =
      (∑' k : {k : ℕ // m < k}, F k) at he
    rw [he]
    exact grandPartition_tail_le_one hφ hb hstable ht hL0.le hβ hD
  have hgrand : grandPartition φ t L β h ≤ ((m : ℝ) + 2) * F n := by
    rw [grandPartition, ← hs.sum_add_tsum_compl (s := Finset.range (m+1))]
    have hsum := Finset.sum_le_card_nsmul (Finset.range (m+1)) F (F n) hnmax
    simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hsum
    change (∑ k ∈ Finset.range (m+1), F k) + (∑' k : {k : ℕ // k ∉ Finset.range (m+1)}, F k) ≤ _
    nlinarith
  have hV : 1 ≤ L ^ 3 := one_le_pow₀ hL
  have hmD : (m : ℝ) + 2 ≤ (D + 2) * L ^ 3 := by
    have hm := Nat.floor_le (show 0 ≤ D * L ^ 3 by positivity)
    dsimp only [m]
    nlinarith
  have hgrand' := hgrand.trans (mul_le_mul_of_nonneg_right hmD (by linarith : 0 ≤ F n))
  have hlog := Real.log_le_log (show 0 < grandPartition φ t L β h by
    linarith [(grandPartition_bounds hφ hb hstable hL0.le hβ t h).1]) hgrand'
  have hFp : 0 < F n := by linarith
  rw [Real.log_mul (by positivity) hFp.ne'] at hlog
  have hFlog : Real.log (F n) = t * h * n + Real.log (partition φ L n β) := by
    simp only [F, Real.log_mul (Real.exp_ne_zero _) (partition_pos hφ hb hL0 n β).ne', Real.log_exp]
  rw [hFlog] at hlog
  refine ⟨n, ⟨by positivity, (div_le_iff₀ (by positivity : 0 < L ^ 3)).mpr hnD⟩, ?_⟩
  have hden : 0 < t * L ^ 3 := by positivity
  change Real.log (grandPartition φ t L β h) / (t * L ^ 3) ≤ _
  apply (div_le_iff₀ hden).mpr
  have he : (h * ((n : ℝ) / L ^ 3) - finiteCanonical φ t L n β +
      Real.log ((D + 2) * L ^ 3) / (t * L ^ 3)) * (t * L ^ 3) =
      Real.log ((D + 2) * L ^ 3) + (t * h * n + Real.log (partition φ L n β)) := by
    dsimp only [finiteCanonical]
    field_simp
    ring
  rw [he]
  exact hlog

theorem tendsto_log_volume_error {C t : ℝ} (hC : 0 < C) (ht : 0 < t) :
    Tendsto (fun L : ℝ => Real.log (C * L ^ 3) / (t * L ^ 3)) atTop (nhds 0) := by
  have hx : Tendsto (fun L : ℝ => C * L ^ 3) atTop atTop :=
    Tendsto.const_mul_atTop hC (tendsto_pow_atTop (by norm_num : 3 ≠ 0))
  have hh := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hx
  simp only [one_mul, add_zero, pow_one, Function.comp_def] at hh
  have hh' := hh.const_mul (C / t)
  simp only [mul_zero] at hh'
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  field_simp

theorem grandPressure_exists_maximizing_density {φ : Potential}
    (hφ : Continuous φ) (hb : IsBoundedPotential φ) {B t β : ℝ}
    (hstable : StableWith φ B) (ht : 0 < t) (hβ : 0 ≤ β)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0)
    (hlim : ∀ d : ℝ, 0 ≤ d → Tendsto (fun z : ℝ × ℕ => finiteCanonical φ t z.1 z.2 β)
      (thermodynamicFilter d) (nhds (canonicalThermo φ t β d))) (h : ℝ) :
    ∃ d : ℝ, 0 ≤ d ∧ grandPressure φ t β h = h * d - canonicalThermo φ t β d := by
  let D := Real.exp (β * B + t * h + 1)
  have hD : 0 < D := Real.exp_pos _
  let L (j : ℕ) : ℝ := j + 1
  have hLs (j : ℕ) : 1 ≤ L j := by dsimp [L]; linarith [Nat.cast_nonneg (α := ℝ) j]
  have hL : Tendsto L atTop atTop := by
    exact tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  choose N hNd hNmax using fun j : ℕ =>
    finiteGrandPressure_max_term hφ hb hstable ht (hLs j) hβ (le_refl D)
  obtain ⟨d, hd, σ, hσ, hden⟩ := isCompact_Icc.tendsto_subseq hNd
  have hside : Tendsto (L ∘ σ) atTop atTop := hL.comp hσ.tendsto_atTop
  have hconfig : Tendsto (fun j => (L (σ j), N (σ j))) atTop (thermodynamicFilter d) := by
    apply tendsto_inf.mpr
    exact ⟨tendsto_comap_iff.mpr hside, tendsto_comap_iff.mpr hden⟩
  have hcost := (hlim d hd.1).comp hconfig
  have hp := (grandPressure_spec hφ hb hstable ht hβ hc h).1.comp hside
  have hu := ((hden.const_mul h).sub hcost).add
    ((tendsto_log_volume_error (show 0 < D + 2 by linarith) ht).comp hside)
  simp only [add_zero, Function.comp_def] at hp hu
  have hle := le_of_tendsto_of_tendsto hp hu (Eventually.of_forall (fun j => hNmax (σ j)))
  exact ⟨d, hd.1, le_antisymm hle
    (canonical_le_grand_dual hφ hb hstable ht hβ hd.1 hc (hlim d hd.1) h)⟩

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_PressureContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

lemma localMomentBound_nonneg {t β : ℝ} (hβ : 0 ≤ β) (z : ℝ) :
    0 ≤ localMomentBound t β z := by unfold localMomentBound; positivity

lemma stable_family_of_master {t : ℝ} {a m R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hsa : Summable a) (hsm : Summable m)
    (ham : ∀ n, a n ≤ m n)
    (hrow : 2197*t*bumpIntegral⁻¹*(∑' n, m n) ≤ (t^2/8)/8) :
    StableWith (familyPotential t a R) (t^2/2) := by
  apply stable_familyPotential ht ha hR hsa
  have hcoeff : 0 ≤ 2197*t*bumpIntegral⁻¹ := mul_nonneg (by positivity) (inv_nonneg.mpr bumpIntegral_pos.le)
  have hh := (mul_le_mul_of_nonneg_left (hsa.tsum_le_tsum ham hsm) hcoeff).trans hrow
  nlinarith [sq_nonneg t]

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_RangeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

lemma referenceRowBound_nonneg {t A : ℝ} (ht : 0 ≤ t) (hA : 0 ≤ A) :
    0 ≤ referenceRowBound t A := by
  unfold referenceRowBound
  have hb := bumpIntegral_pos.le
  positivity

lemma boxPressureConstant_nonneg {t β h A : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β) (hA : 0 ≤ A) :
    0 ≤ boxPressureConstant t β h A := by
  unfold boxPressureConstant
  exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (localMomentBound_nonneg hβ _))
    (referenceRowBound_nonneg ht hA)) ht

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_InteriorGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped BigOperators ENNReal NNReal ContDiff

namespace RadialTransition

lemma kernelRowError_nonneg (q : ℕ) {R : ℝ} (hR : 0 ≤ R) : 0 ≤ kernelRowError q R := by
  unfold kernelRowError
  have := bumpIntegral_pos
  positivity

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_MixtureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff BigOperators ENNReal NNReal

namespace RadialTransition

lemma quadraticTerm_pos {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {L : ℝ} (hL : 0 < L) (β z b : ℝ) (n : ℕ) : 0 < quadraticTerm φ L β z b n := by
  exact mul_pos (mul_pos (Real.exp_pos _) (partition_pos hφ hb hL n β)) (Real.exp_pos _)

lemma quadraticTerm_tail_bound {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {L β z b c B κ D : ℝ} (hL : 0 < L) (hβ : 0 ≤ β) (hκ : 0 < κ)
    (hc : κ ≤ β*c-b) (hD : 1 ≤ D) (hcut : z+β*B+2 ≤ κ*D)
    (hE : ∀ n x, x ∈ configurationCube L n → c*(n:ℝ)^2/L^3-B*n ≤ energy φ x)
    {n : ℕ} (hn : D*L^3 < n) : quadraticTerm φ L β z b n ≤ Real.exp (-(n:ℝ)) := by
  have hV : 0 < L^3 := by positivity
  have hn0 : 0 < (n:ℝ) := lt_trans (by positivity : 0 < D*L^3) hn
  have hp := quadraticTerm_pos hφ hb hL β z b n
  have hl := log_partition_upper_of_energy_lower hφ hb hL hβ n (hE n)
  have hf := (log_factorial_bounds n).1
  have hlog : Real.log (L^3) ≤ Real.log (n:ℝ) := Real.log_le_log hV (by nlinarith)
  have hentropy : (n:ℝ)*Real.log (L^3)-Real.log (n.factorial:ℝ) ≤ n := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hn0.le]
  have hquad : κ*D*(n:ℝ) ≤ (β*c-b)*(n:ℝ)^2/L^3 := by
    apply (le_div_iff₀ hV).mpr
    have hh : D*L^3 ≤ (n:ℝ) := hn.le
    nlinarith [mul_le_mul_of_nonneg_left hh (mul_nonneg hκ.le hn0.le),
      mul_le_mul_of_nonneg_right hc (sq_nonneg (n:ℝ))]
  have hlg : Real.log (quadraticTerm φ L β z b n) ≤ -(n:ℝ) := by
    rw [quadraticTerm, Real.log_mul (mul_ne_zero (Real.exp_ne_zero _) (partition_pos hφ hb hL n β).ne') (Real.exp_ne_zero _),
      Real.log_mul (Real.exp_ne_zero _) (partition_pos hφ hb hL n β).ne', Real.log_exp, Real.log_exp]
    have he : z*(n:ℝ)-β*(c*(n:ℝ)^2/L^3-B*n)+b*(n:ℝ)^2/L^3 =
        (z+β*B)*(n:ℝ)-(β*c-b)*(n:ℝ)^2/L^3 := by ring
    have hh := mul_le_mul_of_nonneg_right hcut hn0.le
    linarith
  exact (Real.exp_log hp).symm.le.trans (Real.exp_le_exp.mpr hlg)

lemma exp_neg_nat_summable : Summable (fun n : ℕ => Real.exp (-(n:ℝ))) := by
  have he (n : ℕ) : Real.exp (-(n:ℝ)) = (Real.exp (-1))^n := by rw [← Real.exp_nat_mul]; congr 1; ring
  simpa only [he] using summable_geometric_of_lt_one (Real.exp_pos (-1)).le (Real.exp_lt_one_iff.mpr (by norm_num))

lemma exp_neg_positive_tail : (∑' n : {n : ℕ // 0 < n}, Real.exp (-(n:ℝ))) ≤ 1 := by
  have hs := exp_neg_nat_summable
  have he : (∑' n : ℕ, Real.exp (-(n:ℝ))) = (1-Real.exp (-1))⁻¹ := by
    have hh := tsum_geometric_of_lt_one (Real.exp_pos (-1)).le (Real.exp_lt_one_iff.mpr (by norm_num))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    apply tsum_congr; intro n
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hx : Real.exp (-1) ≤ (1/2:ℝ) := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos 1)]
    have hh := Real.add_one_le_exp (1:ℝ)
    linarith
  have hpos : 0 < 1-Real.exp (-1) := by linarith
  have hsum : (∑' n : ℕ, Real.exp (-(n:ℝ))) ≤ 2 := by
    rw [he, inv_le_iff_one_le_mul₀ hpos]
    linarith
  have ht := hs.sum_add_tsum_compl (s := {0})
  simp only [Finset.sum_singleton, Nat.cast_zero, neg_zero, Real.exp_zero] at ht
  have heq : (∑' n : {n : ℕ // n ∉ ({0}:Finset ℕ)}, Real.exp (-(n:ℝ))) =
      ∑' n : {n : ℕ // 0 < n}, Real.exp (-(n:ℝ)) := by
    let e : {n : ℕ // n ∉ ({0}:Finset ℕ)} ≃ {n : ℕ // 0 < n} :=
      Equiv.subtypeEquivProp (by funext n; apply propext; simp [Nat.pos_iff_ne_zero])
    exact e.tsum_eq (fun n => Real.exp (-(n:ℝ)))
  change 1 + (∑' n : {n : ℕ // n ∉ ({0}:Finset ℕ)}, Real.exp (-(n:ℝ))) = _ at ht
  rw [heq] at ht
  linarith

lemma summable_of_tail_exp {F : ℕ → ℝ} (hF : ∀ n, 0 ≤ F n) (N : ℕ)
    (htail : ∀ n, N < n → F n ≤ Real.exp (-(n:ℝ))) : Summable F := by
  apply Summable.of_nonneg_of_le (fun n => hF n) (f := fun n => if n ≤ N then F n else Real.exp (-(n:ℝ)))
  · intro n
    split_ifs with hn
    · rfl
    · exact htail n (by omega)
  · have he : (fun n => if n ≤ N then F n else Real.exp (-(n:ℝ))) =
        (fun n : ℕ => Real.exp (-(n:ℝ)) + if n ≤ N then F n-Real.exp (-(n:ℝ)) else 0) := by
      funext n; split_ifs <;> ring
    rw [he]
    exact exp_neg_nat_summable.add (summable_of_ne_finset_zero (s := Finset.range (N+1)) (by intro n hn; simp only [Finset.mem_range, not_lt] at hn; simp [show ¬n ≤ N by omega]))

lemma tail_le_one_of_exp {F : ℕ → ℝ} (hF : ∀ n, 0 ≤ F n) (N : ℕ)
    (htail : ∀ n, N < n → F n ≤ Real.exp (-(n:ℝ))) :
    (∑' n : {n : ℕ // N < n}, F n) ≤ 1 := by
  have hs := summable_of_tail_exp hF N htail
  have hh := (hs.subtype (fun n => N < n)).tsum_le_tsum (fun (n : {n : ℕ // N < n}) => htail n n.property)
    (exp_neg_nat_summable.subtype (fun n => N < n))
  apply hh.trans
  apply le_trans _ exp_neg_positive_tail
  let j : {n : ℕ // N < n} → {n : ℕ // 0 < n} := fun n => ⟨n, lt_of_le_of_lt (Nat.zero_le N) n.property⟩
  exact tsum_comp_le_tsum_of_inj (i := j) (exp_neg_nat_summable.subtype (fun n => 0 < n))
    (fun _ => (Real.exp_pos _).le) (by intro a b h; apply Subtype.ext; exact congrArg (fun x : {n : ℕ // 0 < n} => (x:ℕ)) h)

lemma truncated_sum_bound {F : ℕ → ℝ} (hF : Summable F) {N : ℕ} {M : ℝ}
    (hM : 1 ≤ M) (htail : (∑' n : {n : ℕ // N < n}, F n) ≤ 1)
    (hsmall : ∀ n, n ≤ N → F n ≤ M) : (∑' n, F n) ≤ ((N:ℝ)+2)*M := by
  have ht := hF.sum_add_tsum_compl (s := Finset.range (N+1))
  have he := (Equiv.subtypeEquivProp (by funext n; apply propext; simp) :
    {n : ℕ // n ∉ Finset.range (N+1)} ≃ {n : ℕ // N < n}).tsum_eq (fun n => F n)
  change (∑' n : {n : ℕ // n ∉ Finset.range (N+1)}, F n) =
    (∑' n : {n : ℕ // N < n}, F n) at he
  change (∑ n ∈ Finset.range (N+1), F n) + (∑' n : {n : ℕ // n ∉ Finset.range (N+1)}, F n) = _ at ht
  rw [he] at ht
  have hs := Finset.sum_le_card_nsmul (Finset.range (N+1)) F M (by intro n hn; exact hsmall n (by simpa using hn))
  simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hs
  linarith

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_GrandBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff BigOperators ENNReal NNReal

namespace RadialTransition

lemma finite_term_le_grand {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t L β : ℝ} (hst : StableWith φ B) (ht : 0 < t) (hL : 0 < L) (hβ : 0 ≤ β) (h : ℝ) (n : ℕ) :
    h*((n:ℝ)/L^3)-finiteCanonical φ t L n β ≤ finiteGrandPressure φ t L β h := by
  have hterm := (grandPartition_summable hφ hb hst hL.le hβ t h).le_tsum n
    (fun N _ => mul_nonneg (Real.exp_pos _).le (partition_nonneg L N β))
  have hh := Real.log_le_log (mul_pos (Real.exp_pos _) (partition_pos hφ hb hL n β)) hterm
  rw [Real.log_mul (Real.exp_ne_zero _) (partition_pos hφ hb hL n β).ne', Real.log_exp] at hh
  dsimp only [finiteGrandPressure, finiteCanonical]
  apply (le_div_iff₀ (by positivity : 0 < t*L^3)).mpr
  convert hh using 1 <;> first | rfl | (try field_simp [ht.ne', hL.ne']; ring)

lemma log_quadraticTerm_eq {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {t L : ℝ} (ht : 0 < t) (hL : 0 < L) (β h a eta : ℝ) (n : ℕ) :
    Real.log (quadraticTerm φ L β (t*h) (β*t*a*(1+eta)/2) n)/(t*L^3) =
      (h+β*a*((n:ℝ)/L^3))*((n:ℝ)/L^3)-finiteCanonical φ t L n β -
      β*a/2*((n:ℝ)/L^3)^2+β*a*eta/2*((n:ℝ)/L^3)^2 := by
  rw [quadraticTerm, Real.log_mul (mul_ne_zero (Real.exp_ne_zero _) (partition_pos hφ hb hL n β).ne') (Real.exp_ne_zero _),
    Real.log_mul (Real.exp_ne_zero _) (partition_pos hφ hb hL n β).ne', Real.log_exp, Real.log_exp]
  unfold finiteCanonical
  field_simp
  ring

lemma log_quadraticTerm_bound {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t L β : ℝ} (hst : StableWith φ B) (ht : 0 < t) (hL : 0 < L) (hβ : 0 ≤ β)
    (h a eta : ℝ) (n : ℕ) :
    Real.log (quadraticTerm φ L β (t*h) (β*t*a*(1+eta)/2) n)/(t*L^3) ≤
      finiteGrandPressure φ t L β (h+β*a*((n:ℝ)/L^3)) -
      β*a/2*((n:ℝ)/L^3)^2+β*a*eta/2*((n:ℝ)/L^3)^2 := by
  rw [log_quadraticTerm_eq hφ hb ht hL]
  linarith [finite_term_le_grand hφ hb hst ht hL hβ (h+β*a*((n:ℝ)/L^3)) n]

lemma quadratic_sum_pressure_bound {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t L β h a eta c B₀ κ D P : ℝ} (hst : StableWith φ B) (ht : 0 < t) (hL : 1 ≤ L)
    (hβ : 0 ≤ β) (ha : 0 ≤ a) (heta : 0 ≤ eta) (hκ : 0 < κ)
    (hc : κ ≤ β*c-β*t*a*(1+eta)/2) (hD : 1 ≤ D) (hcut : t*h+β*B₀+2 ≤ κ*D)
    (hE : ∀ n x, x ∈ configurationCube L n → c*(n:ℝ)^2/L^3-B₀*n ≤ energy φ x)
    (hP : 0 ≤ P) (hbound : ∀ d ∈ Icc (0:ℝ) D, finiteGrandPressure φ t L β (h+β*a*d)-β*a/2*d^2 ≤ P) :
    Summable (quadraticTerm φ L β (t*h) (β*t*a*(1+eta)/2)) ∧
    Real.log (∑' n, quadraticTerm φ L β (t*h) (β*t*a*(1+eta)/2) n)/(t*L^3) ≤
      P+β*a*eta/2*D^2+Real.log ((D+2)*L^3)/(t*L^3) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hV : 0 < t*L^3 := by positivity
  let N := ⌊D*L^3⌋₊
  let F := quadraticTerm φ L β (t*h) (β*t*a*(1+eta)/2)
  have hFp (n : ℕ) : 0 < F n := quadraticTerm_pos hφ hb hL0 _ _ _ n
  have htail (n : ℕ) (hn : N < n) : F n ≤ Real.exp (-(n:ℝ)) := by
    apply quadraticTerm_tail_bound hφ hb hL0 hβ hκ hc hD hcut hE
    exact (Nat.floor_lt (by positivity : 0 ≤ D*L^3)).mp hn
  have hs : Summable F := summable_of_tail_exp (fun n => (hFp n).le) N htail
  let M := Real.exp (t*L^3*(P+β*a*eta/2*D^2))
  have hM : 1 ≤ M := Real.one_le_exp_iff.mpr (by positivity)
  have hsmall (n : ℕ) (hn : n ≤ N) : F n ≤ M := by
    have hnD : (n:ℝ)/L^3 ≤ D := by
      apply (div_le_iff₀ (by positivity : 0 < L^3)).mpr
      exact (by exact_mod_cast hn : (n:ℝ) ≤ N).trans (Nat.floor_le (by positivity))
    have hd0 : 0 ≤ (n:ℝ)/L^3 := by positivity
    have hbnd := hbound ((n:ℝ)/L^3) ⟨hd0, hnD⟩
    have hh := log_quadraticTerm_bound hφ hb hst ht hL0 hβ h a eta n
    have he : β*a*eta/2*((n:ℝ)/L^3)^2 ≤ β*a*eta/2*D^2 := by
      apply mul_le_mul_of_nonneg_left (sq_le_sq₀ hd0 (by positivity) |>.mpr hnD)
      positivity
    have hl : Real.log (F n)/(t*L^3) ≤ P+β*a*eta/2*D^2 := by linarith
    have hl' := (div_le_iff₀ hV).mp hl
    calc
      _ = Real.exp (Real.log (F n)) := (Real.exp_log (hFp n)).symm
      _ ≤ M := Real.exp_le_exp.mpr (by nlinarith)
  have hsum := truncated_sum_bound hs hM (tail_le_one_of_exp (fun n => (hFp n).le) N htail) hsmall
  have hnV : (N:ℝ)+2 ≤ (D+2)*L^3 := by
    have hfloor := Nat.floor_le (show 0 ≤ D*L^3 by positivity)
    have hV1 : 1 ≤ L^3 := one_le_pow₀ hL
    dsimp only [N]
    nlinarith
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_right hnV (by positivity : 0 ≤ M))
  have hpos : 0 < ∑' n, F n := lt_of_lt_of_le (hFp 0) (hs.le_tsum 0 (fun n _ => (hFp n).le))
  have hl := Real.log_le_log hpos hsum'
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at hl
  refine ⟨hs, ?_⟩
  apply (div_le_iff₀ hV).mpr
  convert hl using 1 <;> first | rfl | (try field_simp [ht.ne', hL0.ne']; ring)

end RadialTransition

end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_IdealAttainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma entropy_lower {d : ℝ} (hd : 0 ≤ d) : -1 ≤ d*Real.log d-d := by
  rcases eq_or_lt_of_le hd with rfl | hd
  · norm_num
  have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hd)
  rw [Real.log_inv] at hh
  have hm := mul_le_mul_of_nonneg_left hh hd.le
  rw [mul_sub, mul_inv_cancel₀ hd.ne', mul_one] at hm
  nlinarith

lemma grandPressure_continuous_h {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t β : ℝ} (hst : StableWith φ B) (ht : 0 < t) (hβ : 0 ≤ β)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r:ℝ) → φ r ≤ 0) : Continuous (grandPressure φ t β) := by
  have hconv : ConvexOn ℝ univ (grandPressure φ t β) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hbb hab
    have hh := grandPressure_convex_mix hφ hb hst ht hc hβ hβ x y ha hbb hab
    have he : a*β+b*β = β := by nlinarith
    simpa only [he, smul_eq_mul] using hh
  exact continuousOn_univ.mp (hconv.continuousOn isOpen_univ)

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_KacComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma family_row_mono_mass {t a : ℝ} {b : ℕ → ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8) :
    2197*t*bumpIntegral⁻¹*(∑' n, b n) ≤ (t^2/8)/8 := by
  have hc : 0 ≤ 2197*t*bumpIntegral⁻¹ := by have := bumpIntegral_pos; positivity
  exact (mul_le_mul_of_nonneg_left (by linarith : (∑' n, b n) ≤ a+∑' n, b n) hc).trans hrow

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_FamilyIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma family_pressure_data {t β : ℝ} {b S : ℕ → ℝ} (ht : 1 ≤ t) (hβ : 0 < β)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hrow : 2197*t*bumpIntegral⁻¹*(∑' n, b n) ≤ (t^2/8)/8) :
    Continuous (grandPressure (familyPotential t b S) t β) ∧
    (∀ h, 0 ≤ grandPressure (familyPotential t b S) t β h) ∧
    (∀ h, ∃ d ≥ 0, grandPressure (familyPotential t b S) t β h = h*d-canonicalThermo (familyPotential t b S) t β d) ∧
    (∀ h d, 0 ≤ d → h*d-canonicalThermo (familyPotential t b S) t β d ≤ grandPressure (familyPotential t b S) t β h) ∧
    (∀ d, 0 ≤ d → β*t/3456*d^2-β*t/2*d-1/t ≤ canonicalThermo (familyPotential t b S) t β d) := by
  have ht0 : 0 < t := by linarith
  have hst := stable_family_of_master ht0.le hb hS hs hs (fun _ => le_rfl) hrow
  have hφ := continuous_familyPotential hb hS hs t
  have hbd := bounded_familyPotential hb hS hs t
  have hc := fun r hr => familyPotential_nonpos_outer hb hS ht (r := r) hr
  have hcoerc : 2197*t*bumpIntegral⁻¹*(∑' n, b n)/2 ≤ t^2/16 := by nlinarith [sq_nonneg t]
  have hl := fun d hd => (familyCanonicalThermo_spec ht hb hS hs hcoerc hβ.le (d := d) hd).1
  refine ⟨grandPressure_continuous_h hφ hbd hst ht0 hβ.le hc,
    fun h => (grandPressure_spec hφ hbd hst ht0 hβ.le hc h).2.1,
    grandPressure_exists_maximizing_density hφ hbd hst ht0 hβ.le hc hl, ?_, ?_⟩
  · intro h d hd
    exact canonical_le_grand_dual hφ hbd hst ht0 hβ.le hd hc (hl d hd) h
  · intro d hd
    have hh := (familyCanonicalThermo_spec ht hb hS hs hcoerc hβ.le hd).2.1
    have he := div_le_div_of_nonneg_right (entropy_lower hd) ht0.le
    have halg : β/t*(t^2/3456*d^2-t^2/2*d) = β*t/3456*d^2-β*t/2*d := by field_simp
    rw [halg] at hh
    simp only [neg_div] at he
    linarith

lemma ideal_bddAbove_of_active {Q : Pressure} {a β h u : ℝ} (hu : ActiveShift Q a β h u) :
    BddAbove (range fun v => attractionBranch Q a v β h) :=
  ⟨attractionBranch Q a u β h, fun _ ⟨v, hv⟩ => hv ▸ hu v⟩

lemma ideal_nonneg_of_active {Q : Pressure} {a β h u : ℝ} (hu : ActiveShift Q a β h u)
    (hQ : 0 ≤ Q β h) : 0 ≤ idealAttraction Q a β h := by
  rw [idealAttraction_eq_of_active hu]
  have hh := hu 0
  simp only [attractionBranch, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] at hh
  exact hQ.trans hh

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_UniformConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma kernelUpperError_le_row {q : ℕ} {R : ℝ} (hR : 0 ≤ R) :
    kernelUpperError q R ≤ kernelRowError q R := by
  unfold kernelUpperError kernelRowError
  apply div_le_div_of_nonneg_right _ hR
  have hh := mul_nonneg (inv_nonneg.mpr bumpIntegral_pos.le) (Nat.cast_nonneg (α := ℝ) q)
  nlinarith

lemma kernelUpperError_nonneg (q : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ kernelUpperError q R := by unfold kernelUpperError; positivity

end RadialTransition
end

end OAI
end

section
-- module Solutions.OAIQ112_RT.RadialTransition_KacVariational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma family_kac_variational_grid_rt2_oai {q : ℕ} (hq : 0 < q)
    {t β h R₀ a R κ D F C : ℝ} {b S : ℕ → ℝ}
    (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 ≤ a) (hR : (q:ℝ)/4 ≤ R) (hq1 : 1 ≤ (q:ℝ)/4)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hR₀ : 2 ≤ R₀) (hrange : ∀ n, S n ≤ R₀)
    (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8)
    (hκ : 0 < κ) (hc : κ ≤ β*(t^2/3456)-β*t*a*(1+kernelUpperError q R)/2)
    (hD : 1 ≤ D) (hcut : t*h+β*(t^2/2)+t+1 ≤ κ*D)
    (hDF : D ≤ F) (hF : Real.exp (β*(t^2/2)+t*(h+β*a*D)+1) ≤ F)
    (hC : ∀ v ∈ Icc (0:ℝ) D, boxPressureConstant t β (h+β*a*v) (∑' n, b n) ≤ C) :
    |grandPressure (familyPotential t (prepend a b) (prepend R S)) t β h-
      idealAttraction (grandPressure (familyPotential t b S) t) a β h| ≤
      2*C*R₀/((q:ℝ)/4)+β*a/2*kernelRowError q R*F^2+
        Real.log ((F+2)*((q:ℝ)/4)^3)/(t*((q:ℝ)/4)^3) := by
  let φ := familyPotential t b S
  let Q := grandPressure φ t
  let s := (q:ℝ)/4
  have hs1 : 1 ≤ s := hq1
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hR1 : 1 ≤ R := hq1.trans hR
  have hrowb := family_row_mono_mass ht0.le ha hrow
  have hst := stable_family_of_master ht0.le hb hS hs hs (fun _ => le_rfl) hrowb
  have hφ := continuous_familyPotential hb hS hs t
  have hbd := bounded_familyPotential hb hS hs t
  have heta := kernelUpperError_nonneg q hR0
  have hcoerc : 2197*t*bumpIntegral⁻¹*(∑' n, b n)/2 ≤ t^2/16 := by nlinarith [sq_nonneg t]
  have hca : κ/t ≤ β*t/3456-β*a/2 := by
    apply (div_le_iff₀ ht0).mpr
    nlinarith [mul_nonneg (show 0 ≤ β*t*a by positivity) heta]
  have hcuta : h+β*t/2+1/t+1 ≤ κ/t*D := by
    apply (mul_le_mul_iff_left₀ ht0).mp
    have he1 : t*(h+β*t/2+1/t+1) = t*h+β*(t^2/2)+t+1 := by field_simp; ring
    have he2 : t*(κ/t*D) = κ*D := by field_simp
    rw [mul_comm _ t, mul_comm (κ/t*D) t, he1, he2]
    exact hcut
  obtain ⟨u, hu, hactive⟩ := family_ideal_exists_active_rt2 ht hβ ha hb hS hs hrowb
    (div_pos hκ ht0) hca hD hcuta
  have hfinite := ideal_bddAbove_of_active hactive
  have hnonneg := ideal_nonneg_of_active hactive ((family_pressure_data ht hβ hb hS hs hrowb).2.1 h)
  have hC0 : boxPressureConstant t β h (∑' n, b n) ≤ C := by
    simpa only [mul_zero, add_zero] using hC 0 ⟨le_rfl, by linarith⟩
  have hCpos : 0 ≤ C := (boxPressureConstant_nonneg ht0.le hβ.le (tsum_nonneg hb)).trans hC0
  have hbox (v : ℝ) (hv : v ∈ Icc (0:ℝ) D) :
      |finiteGrandPressure φ t s β (h+β*a*v)-Q β (h+β*a*v)| ≤ C*R₀/s := by
    apply (finiteGrandPressure_family_box_error_rt2 hq ht hβ hb hS hs hR₀ hrange hrowb).trans
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hC v hv) (by linarith)) hs0.le
  have hbound (d : ℝ) (hd : d ∈ Icc (0:ℝ) D) :
      finiteGrandPressure φ t s β (h+β*a*d)-β*a/2*d^2 ≤ idealAttraction Q a β h+C*R₀/s := by
    have hsum := le_csSup hfinite (mem_range_self d)
    have hh := (abs_le.mp (hbox d hd)).2
    change attractionBranch Q a d β h ≤ idealAttraction Q a β h at hsum
    dsimp only [attractionBranch] at hsum
    linarith
  have hquad := quadratic_sum_pressure_bound hφ hbd hst ht0 hs1 hβ.le ha heta hκ hc hD
    (show t*h+β*(t^2/2)+2 ≤ κ*D by linarith)
    (fun n x hx => family_density_stability ht0.le hs1 hb hS hs hcoerc x hx)
    (show 0 ≤ idealAttraction Q a β h+C*R₀/s by positivity) hbound
  have hks : Summable (kacSeries φ q R t a β h) := by
    simpa only [kacSeries, φ, s, ← mul_assoc] using hquad.1
  have hup := family_kac_upper_limit_rt2 hq ht hβ ha hR hq1 hb hS hs hR₀ hrange hrow hks
    (show Real.log (∑' n, kacSeries φ q R t a β h n)/(t*s^3) ≤
      idealAttraction Q a β h+C*R₀/s+β*a*kernelUpperError q R/2*D^2+
        Real.log ((D+2)*s^3)/(t*s^3) by
      simpa only [kacSeries, φ, s, ← mul_assoc] using hquad.2)
  have hFu : Real.exp (β*(t^2/2)+t*(h+β*a*u)+1) ≤ F := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hF
    gcongr
    exact hu.2
  have hlo := family_kac_lower_limit_rt2 hq ht hβ ha hR hq1 hb hS hs hR₀ hrange hrow hks hFu
  have hboxu := (abs_le.mp (hbox u hu)).1
  have heq := idealAttraction_eq_of_active hactive
  change idealAttraction Q a β h = Q β (h+β*a*u)-β*a/2*u^2 at heq
  have hdel : boxPressureConstant t β h (∑' n, b n)*R₀/s ≤ C*R₀/s :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC0 (by linarith)) hs0.le
  have hDF0 : 0 ≤ D := by linarith
  have hF0 : 0 ≤ F := hDF0.trans hDF
  have herr : β*a*kernelUpperError q R/2*D^2 ≤ β*a/2*kernelRowError q R*F^2 := by
    have hh := mul_le_mul (kernelUpperError_le_row hR0) ((sq_le_sq₀ hDF0 hF0).mpr hDF)
      (sq_nonneg D) (kernelRowError_nonneg q hR0)
    nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ β*a/2 by positivity)]
  have hlog : Real.log ((D+2)*s^3)/(t*s^3) ≤ Real.log ((F+2)*s^3)/(t*s^3) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  apply abs_le.mpr
  dsimp only [φ, Q, s] at hboxu hdel heq herr hlog hup hlo ⊢
  rw [show 2*C*R₀/((q:ℝ)/4) = 2*(C*R₀/((q:ℝ)/4)) by ring]
  constructor <;> linarith only [hboxu, hdel, heq, herr, hlog, hup, hlo]

end RadialTransition
end

end OAI
end

theorem solution : type_of% @OAI.RadialTransition.family_kac_variational_grid_rt2_oai := @OAI.RadialTransition.family_kac_variational_grid_rt2_oai
