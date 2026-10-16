-- Prove2me | solution 1 for OAI.Erdos3.exists_crt_counting_contradiction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T03:27:34.067251+00:00
-- url     : https://prove2.me/submissions/ca973c3b-422e-41fa-9554-d1f0ac515c7d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1325
import Theorems.Thm_OAI_Erdos3_exists_character_centered_counting

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
namespace OAI

section

open scoped BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators


end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators




end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem complex_ofReal_expect {X : Type*} [Fintype X] (f : X → ℝ) :
    (((𝔼 x, f x) : ℝ) : ℂ) = 𝔼 x, (f x : ℂ) := by
  simp only [Fintype.expect_eq_sum_div_card, Complex.ofReal_div, Complex.ofReal_sum,
    Complex.ofReal_natCast]

theorem real_mean_le_of_complex_mean_close {X : Type*} [Fintype X]
    (f : X → ℝ) {epsilon : ℝ} (h : ‖(𝔼 x, (f x : ℂ)) - 1‖ ≤ epsilon) :
    (𝔼 x, f x) ≤ 1 + epsilon := by
  rw [← complex_ofReal_expect, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at h
  linarith [(abs_le.mp h).2]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

theorem abs_sub_le_of_circle_dist_from_interior_center {x c δ : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 1) (hc : δ < c ∧ c < 1 - δ)
    (hdist : dist (x : UnitAddCircle) (c : UnitAddCircle) ≤ δ) :
    |x - c| ≤ δ := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, UnitAddCircle.norm_eq] at hdist
  have hxc : |x - c| < 1 - δ := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hz : |(round (x - c) : ℝ)| ≤ |x - c - (round (x - c) : ℝ)| + |x - c| := by
    calc
      _ = |((round (x - c) : ℝ) - (x - c)) + (x - c)| := by ring_nf
      _ ≤ |(round (x - c) : ℝ) - (x - c)| + |x - c| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm (round (x - c) : ℝ) (x - c)]
  have hzlt : |(round (x - c) : ℝ)| < 1 := by linarith
  have hzlo : (-1 : ℤ) < round (x - c) := by exact_mod_cast (abs_lt.mp hzlt).1
  have hzhi : round (x - c) < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hzlt).2
  have hz0 : round (x - c) = 0 := by omega
  simpa only [hz0, Int.cast_zero, sub_zero] using hdist

theorem residue_fraction_mem_unit_interval {N : ℕ} [NeZero N] (x : ZMod N) :
    0 ≤ (x.val : ℝ) / N ∧ (x.val : ℝ) / N ≤ 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  exact ⟨by positivity, (div_le_one hN).mpr (by exact_mod_cast x.val_lt.le)⟩

theorem residue_fraction_close_to_interior_center {N : ℕ} [NeZero N]
    (x : ZMod N) {c δ : ℝ} (hc : δ < c ∧ c < 1 - δ)
    (hdist : dist (ZMod.toAddCircle x) (c : UnitAddCircle) ≤ δ) :
    |(x.val : ℝ) / N - c| ≤ δ := by
  rw [ZMod.toAddCircle_apply] at hdist
  exact abs_sub_le_of_circle_dist_from_interior_center (residue_fraction_mem_unit_interval x) hc hdist

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CRTConfigurationTorus
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem crt_configuration_expect {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
    [∀ j, NeZero (N j)] [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))
    (f : ((t : J × Bool) → ZMod (N t.1)) → ℝ) :
    (𝔼 z : ZMod (∏ j, N j) × ZMod (∏ j, N j), f (crtConfigurationEquiv N hN z)) = 𝔼 w, f w :=
  Fintype.expect_equiv (crtConfigurationEquiv N hN).toEquiv _ _ (fun _ => rfl)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.TorusCellBudget
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open CircleFourier

theorem circle_grid_cover {q : ℕ} (hq : 0 < q) (x : UnitAddCircle) :
    ∃ a : Fin q, dist x (((a.val : ℝ) / q : ℝ) : UnitAddCircle) ≤ 1 / (q : ℝ) := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℝ)) x
  refine ⟨fractionalPartBin q hq r, ?_⟩
  calc
    _ = ‖((Int.fract r - (fractionalPartBin q hq r).val / (q : ℝ) : ℝ) : UnitAddCircle)‖ := by
      rw [dist_eq_norm, AddCircle.coe_sub, AddCircle.coe_fract]
      rfl
    _ ≤ |Int.fract r - (fractionalPartBin q hq r).val / (q : ℝ)| := by
      exact QuotientAddGroup.norm_mk_le_norm
    _ ≤ 1 / (q : ℝ) := by
      simpa only [abs_sub_comm] using fractionalPartBin_center_error hq r

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped NNReal

theorem ambientTorusTent_range {J : Type*} [Fintype J] (q : ℕ) (x : J → UnitAddCircle) :
    0 ≤ ambientTorusTent q x ∧ ambientTorusTent q x ≤ 1 := by
  refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
  have h : 0 ≤ (q : ℝ) / 4 * ‖x‖ := by positivity
  linarith

theorem ambientTorusTent_ge_half {J : Type*} [Fintype J] {q : ℕ} (hq : 0 < q)
    (x : J → UnitAddCircle) (hx : ‖x‖ ≤ 2 / (q : ℝ)) : 1 / 2 ≤ ambientTorusTent q x := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have he := (le_div_iff₀ hq').mp hx
  apply le_trans _ (le_max_right _ _)
  nlinarith

theorem ambientTorusTent_support {J : Type*} [Fintype J] {q : ℕ} (hq : 0 < q)
    (x : J → UnitAddCircle) (hx : ambientTorusTent q x ≠ 0) : ‖x‖ < 4 / (q : ℝ) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have he : 0 < 1 - (q : ℝ) / 4 * ‖x‖ := by
    by_contra h
    exact hx (max_eq_left (by linarith))
  apply (lt_div_iff₀ hq').mpr
  nlinarith

theorem ambientTorusTent_lipschitz {J : Type*} [Fintype J] (q : ℕ) :
    LipschitzWith ((q : ℝ≥0) / 4) (ambientTorusTent (J := J) q) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |max 0 (1 - (q : ℝ) / 4 * ‖x‖) - max 0 (1 - (q : ℝ) / 4 * ‖y‖)| ≤ _
  calc
    _ ≤ |(1 - (q : ℝ) / 4 * ‖x‖) - (1 - (q : ℝ) / 4 * ‖y‖)| := by
      rw [max_comm 0 _, max_comm 0 _]
      exact abs_max_sub_max_le_abs _ _ _
    _ = (q : ℝ) / 4 * |‖x‖ - ‖y‖| := by
      rw [show (1 - (q : ℝ) / 4 * ‖x‖) - (1 - (q : ℝ) / 4 * ‖y‖) =
        -((q : ℝ) / 4) * (‖x‖ - ‖y‖) by ring, abs_mul, abs_neg,
        abs_of_nonneg (by positivity : 0 ≤ (q : ℝ) / 4)]
    _ ≤ _ := by
      simpa only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat, dist_eq_norm] using
        mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (by positivity : 0 ≤ (q : ℝ) / 4)

end Erdos3

end

section

namespace Erdos3

theorem residue_quotient_double_bound {N q : ℕ} (hq : 0 < q) (hN : q ≤ N) :
    N ≤ 2 * q * (N / q) := by
  have hpos : 1 ≤ N / q := Nat.le_div_iff_mul_le hq |>.mpr (by simpa using hN)
  have hlt := Nat.lt_mul_div_succ N hq
  nlinarith

theorem exists_residue_circle_neighborhood_embedding {N q : ℕ} [NeZero N]
    (hq : 0 < q) (hN : q ≤ N) (c : UnitAddCircle) :
    ∃ e : Fin (N / q) ↪ ZMod N,
      ∀ a, dist (ZMod.toAddCircle (e a)) c ≤ 2 / (q : ℝ) := by
  obtain ⟨b, hb⟩ := circle_grid_cover (NeZero.pos N) c
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hNR : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hqN : (q : ℝ) ≤ N := by exact_mod_cast hN
  have hdiv : N / q ≤ N := Nat.div_le_self N q
  let e : Fin (N / q) ↪ ZMod N :=
    ⟨fun a => (b.val : ZMod N) + a.val, by
      intro a a' h
      have hh : (a.val : ZMod N) = a'.val := add_left_cancel h
      have ha : a.val < N := a.isLt.trans_le hdiv
      have ha' : a'.val < N := a'.isLt.trans_le hdiv
      have hv := congrArg ZMod.val hh
      rw [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt ha'] at hv
      exact Fin.ext hv⟩
  refine ⟨e, fun a => ?_⟩
  have haq : (a.val : ℝ) * q ≤ N := by
    exact_mod_cast (Nat.mul_le_mul_right q a.isLt.le).trans (Nat.div_mul_le_self N q)
  have ha : (a.val : ℝ) / N ≤ 1 / q := by
    apply (div_le_div_iff₀ hNR hqR).mpr
    simpa only [one_mul] using haq
  have hd : dist (ZMod.toAddCircle (e a)) (ZMod.toAddCircle (b.val : ZMod N)) ≤
      (a.val : ℝ) / N := by
    change dist (ZMod.toAddCircle ((b.val : ZMod N) + (a.val : ZMod N))) _ ≤ _
    rw [map_add, dist_eq_norm, add_sub_cancel_left, ZMod.toAddCircle_natCast]
    calc
      _ ≤ ‖(a.val : ℝ) / N‖ := QuotientAddGroup.norm_mk_le_norm
      _ = _ := Real.norm_of_nonneg (by positivity)
  have hb' : dist (ZMod.toAddCircle (b.val : ZMod N)) c ≤ 1 / (N : ℝ) := by
    simpa only [ZMod.toAddCircle_natCast, dist_comm] using hb
  have hi : 1 / (N : ℝ) ≤ 1 / q := one_div_le_one_div_of_le hqR hqN
  exact (dist_triangle _ _ _).trans ((add_le_add (hd.trans ha) (hb'.trans hi)).trans
    (by ring_nf; exact le_rfl))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem centeredTorusTent_range {J : Type*} [Fintype J] (q : ℕ)
    (c x : J → UnitAddCircle) : 0 ≤ centeredTorusTent q c x ∧ centeredTorusTent q c x ≤ 1 :=
  ambientTorusTent_range q (x - c)

theorem centeredTorusTent_lipschitz {J : Type*} [Fintype J] (q : ℕ)
    (c : J → UnitAddCircle) : LipschitzWith ((q : ℝ≥0) / 4) (centeredTorusTent q c) := by
  unfold centeredTorusTent
  simpa only [mul_one, Function.comp_def, sub_eq_add_neg] using
    (ambientTorusTent_lipschitz (J := J) q).comp (isometry_add_right (-c)).lipschitz

theorem centeredTorusTent_coordinate_support {J : Type*} [Fintype J] {q : ℕ}
    (hq : 0 < q) (c x : J → UnitAddCircle) (h : centeredTorusTent q c x ≠ 0) (j : J) :
    dist (x j) (c j) < 4 / (q : ℝ) := by
  have hnorm := ambientTorusTent_support hq (x - c) h
  calc
    dist (x j) (c j) = ‖(x - c) j‖ := dist_eq_norm _ _
    _ ≤ ‖x - c‖ := norm_le_pi_norm (x - c) j
    _ < _ := hnorm

theorem centeredTorusTent_residue_mean {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
    [∀ j, NeZero (N j)] {q : ℕ} (hq : 0 < q) (hN : ∀ j, q ≤ N j)
    (c : J → UnitAddCircle) :
    1 / (2 * (2 * (q : ℝ)) ^ Fintype.card J) ≤
      𝔼 u : (j : J) → ZMod (N j), centeredTorusTent q c (fun j => ZMod.toAddCircle (u j)) := by
  classical
  choose e he using fun j => exists_residue_circle_neighborhood_embedding hq (hN j) (c j)
  let E : ((j : J) → Fin (N j / q)) → ((j : J) → ZMod (N j)) := fun a j => e j (a j)
  have hinj : Function.Injective E := by
    intro a b h
    funext j
    exact (e j).injective (congrFun h j)
  let W : ((j : J) → ZMod (N j)) → ℝ :=
    fun u => centeredTorusTent q c (fun j => ZMod.toAddCircle (u j))
  have hhalf (a : (j : J) → Fin (N j / q)) : 1 / 2 ≤ W (E a) := by
    apply ambientTorusTent_ge_half hq
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    simpa only [Pi.sub_apply, ← dist_eq_norm] using he j (a j)
  have hsum : (Fintype.card ((j : J) → Fin (N j / q)) : ℝ) / 2 ≤ ∑ u, W u := by
    classical
    have h : ∑ _a : (j : J) → Fin (N j / q), (1 / 2 : ℝ) ≤ ∑ u, W u := by
      calc ∑ _a : (j : J) → Fin (N j / q), (1 / 2 : ℝ) ≤ ∑ a, W (E a) :=
            Finset.sum_le_sum (fun a _ => hhalf a)
        _ = ∑ u ∈ Finset.univ.image E, W u :=
            (Finset.sum_image (fun x _ y _ hxy => hinj hxy)).symm
        _ ≤ ∑ u, W u := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun u _ _ => (centeredTorusTent_range q c _).1)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div] using h
  have hcard : (Fintype.card ((j : J) → ZMod (N j)) : ℝ) ≤
      (2 * (q : ℝ)) ^ Fintype.card J * (Fintype.card ((j : J) → Fin (N j / q)) : ℝ) := by
    simp only [Fintype.card_pi, ZMod.card, Fintype.card_fin, Nat.cast_prod]
    calc
      (∏ j, (N j : ℝ)) ≤ ∏ j, 2 * (q : ℝ) * (N j / q : ℕ) := by
        apply Finset.prod_le_prod
        · intro j _; positivity
        · intro j _; exact_mod_cast residue_quotient_double_bound hq (hN j)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hd : (0 : ℝ) < Fintype.card ((j : J) → ZMod (N j)) := by
    exact_mod_cast Fintype.card_pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Fintype.expect_eq_sum_div_card]
  change 1 / (2 * (2 * (q : ℝ)) ^ Fintype.card J) ≤ (∑ u, W u) / _
  apply (le_div_iff₀ hd).mpr
  calc
    _ = (Fintype.card ((j : J) → ZMod (N j)) : ℝ) /
        (2 * (2 * (q : ℝ)) ^ Fintype.card J) := by ring
    _ ≤ _ := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * (2 * (q : ℝ)) ^ Fintype.card J)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hsum
        (by positivity : 0 ≤ 2 * (2 * (q : ℝ)) ^ Fintype.card J)]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators NNReal

namespace PolynomialPatch

end PolynomialPatch


end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

namespace PatchKernel


end PatchKernel

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CRTProgressionVanishing
namespace OAI

section

namespace Erdos3

theorem progression_window_radius_bounds {k : ℕ} (hk : 1 ≤ k) :
    0 < 1 / (16 * (k : ℝ)) ∧ 1 / (16 * (k : ℝ)) ≤ 1 / 16 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact ⟨by positivity, one_div_le_one_div_of_le (by norm_num) (by linarith)⟩

theorem residue_base_window_bound {N k : ℕ} [NeZero N] (hk : 1 ≤ k)
    (x : ZMod N)
    (hx : dist (ZMod.toAddCircle x) ((1 / 4 : ℝ) : UnitAddCircle) ≤ 1 / (16 * (k : ℝ))) :
    2 * x.val < N := by
  obtain ⟨_, hr⟩ := progression_window_radius_bounds hk
  have hc : 1 / (16 * (k : ℝ)) < 1 / 4 ∧ (1 / 4 : ℝ) < 1 - 1 / (16 * (k : ℝ)) := by
    constructor <;> linarith
  have he := residue_fraction_close_to_interior_center x hc hx
  have hfrac : (x.val : ℝ) / N < 1 / 2 := by linarith [(abs_le.mp he).2]
  have hNR : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hmul : 2 * (x.val : ℝ) < N := by linarith [(div_lt_iff₀ hNR).mp hfrac]
  exact_mod_cast hmul

theorem residue_step_window_bounds {N k : ℕ} [NeZero N] (hk : 1 ≤ k)
    (d : ZMod N)
    (hd : dist (ZMod.toAddCircle d) ((1 / (4 * (k : ℝ)) : ℝ) : UnitAddCircle) ≤
      1 / (16 * (k : ℝ))) :
    0 < d.val ∧ 2 * k * d.val < N := by
  obtain ⟨hr0, hr⟩ := progression_window_radius_bounds hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have heq : 1 / (4 * (k : ℝ)) = 4 * (1 / (16 * (k : ℝ))) := by ring
  have hc : 1 / (16 * (k : ℝ)) < 1 / (4 * (k : ℝ)) ∧
      1 / (4 * (k : ℝ)) < 1 - 1 / (16 * (k : ℝ)) := by
    rw [heq]
    constructor <;> linarith
  have he := residue_fraction_close_to_interior_center d hc hd
  have hf0 : 0 < (d.val : ℝ) / N := by rw [heq] at he; linarith [(abs_le.mp he).1]
  have heq' : 1 / (2 * (k : ℝ)) = 8 * (1 / (16 * (k : ℝ))) := by ring
  have hf1 : (d.val : ℝ) / N < 1 / (2 * (k : ℝ)) := by
    rw [heq] at he
    rw [heq']
    linarith [(abs_le.mp he).2]
  have hNR : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  constructor
  · have h := (lt_div_iff₀ hNR).mp hf0
    simpa only [zero_mul, Nat.cast_pos] using h
  · have h := (div_lt_div_iff₀ hNR (by positivity : 0 < 2 * (k : ℝ))).mp hf1
    have hh : 2 * (k : ℝ) * d.val < N := by nlinarith
    exact_mod_cast hh

theorem residue_progression_val_of_windows {N k : ℕ} [NeZero N]
    (x d : ZMod N) (hx : 2 * x.val < N) (hd : 2 * k * d.val < N)
    {i : ℕ} (hi : i < k) :
    (x + (i : ZMod N) * d).val = x.val + i * d.val := by
  have hid : i * d.val ≤ k * d.val := Nat.mul_le_mul_right _ hi.le
  have hsum : x.val + i * d.val < N := by nlinarith
  have he : x + (i : ZMod N) * d = ((x.val + i * d.val : ℕ) : ZMod N) := by simp
  rw [he, ZMod.val_natCast_of_lt hsum]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem progressionTorusCutoff_range {J : Type*} [Fintype J] (k : ℕ)
    (w : J × Bool → UnitAddCircle) :
    0 ≤ progressionTorusCutoff k w ∧ progressionTorusCutoff k w ≤ 1 :=
  centeredTorusTent_range _ _ _

theorem progressionTorusCutoff_lipschitz {J : Type*} [Fintype J] (k : ℕ) :
    LipschitzWith (((64 * k : ℕ) : ℝ≥0) / 4) (progressionTorusCutoff (J := J) k) :=
  centeredTorusTent_lipschitz _ _

theorem progressionTorusCutoff_residue_support {J : Type*} [Fintype J] (N : J → ℕ)
    [∀ j, NeZero (N j)] {k : ℕ} (hk : 1 ≤ k)
    (u : (t : J × Bool) → ZMod (N t.1))
    (hu : progressionTorusCutoff k (fun t => ZMod.toAddCircle (u t)) ≠ 0) (j : J) :
    2 * (u (j, false)).val < N j ∧
      0 < (u (j, true)).val ∧ 2 * k * (u (j, true)).val < N j := by
  have hk0 : 0 < 64 * k := by omega
  have hr : 4 / ((64 * k : ℕ) : ℝ) = 1 / (16 * (k : ℝ)) := by push_cast; ring
  have hx := centeredTorusTent_coordinate_support hk0 (progressionTorusCenter k)
    (fun t => ZMod.toAddCircle (u t)) hu (j, false)
  have hd := centeredTorusTent_coordinate_support hk0 (progressionTorusCenter k)
    (fun t => ZMod.toAddCircle (u t)) hu (j, true)
  rw [hr] at hx hd
  simp only [progressionTorusCenter, Bool.false_eq_true, ↓reduceIte] at hx
  simp only [progressionTorusCenter, ↓reduceIte] at hd
  exact ⟨residue_base_window_bound hk _ hx.le, residue_step_window_bounds hk _ hd.le⟩

theorem progressionTorusCutoff_residue_mean {J : Type*} [Fintype J] [DecidableEq J]
    (N : J → ℕ) [∀ j, NeZero (N j)] {k : ℕ} (hk : 1 ≤ k) (hN : ∀ j, 64 * k ≤ N j) :
    1 / (2 * (128 * (k : ℝ)) ^ (Fintype.card J * 2)) ≤
      𝔼 u : (t : J × Bool) → ZMod (N t.1),
        progressionTorusCutoff k (fun t => ZMod.toAddCircle (u t)) := by
  have h := centeredTorusTent_residue_mean (fun t : J × Bool => N t.1)
    (show 0 < 64 * k by omega) (fun t => hN t.1) (progressionTorusCenter k)
  simpa only [progressionTorusCutoff, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul,
    Nat.cast_ofNat, show (2 : ℝ) * (64 * (k : ℝ)) = 128 * k by ring] using h

theorem crtProgressionWeight_mean {J : Type*} [Fintype J] (N : J → ℕ)
    [∀ j, NeZero (N j)] [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))
    {k : ℕ} (hk : 1 ≤ k) (hsize : ∀ j, 64 * k ≤ N j) :
    1 / (2 * (128 * (k : ℝ)) ^ (Fintype.card J * 2)) ≤
      𝔼 z, crtProgressionWeight N hN k z := by
  classical
  have he := crt_configuration_expect N hN
    (fun u => progressionTorusCutoff k (fun t => ZMod.toAddCircle (u t)))
  change (𝔼 z, crtProgressionWeight N hN k z) = _ at he
  rw [he]
  exact progressionTorusCutoff_residue_mean N hk hsize

theorem crtProgressionWeight_support {J : Type*} [Fintype J] (N : J → ℕ)
    [∀ j, NeZero (N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) {k : ℕ} (hk : 1 ≤ k)
    (x d : ZMod (∏ j, N j)) (h : crtProgressionWeight N hN k (x, d) ≠ 0) :
    (∀ j, 0 < (ZMod.prodEquivPi N hN d j).val) ∧
    ∀ i : ℕ, i < k → ∀ j,
      (ZMod.prodEquivPi N hN (x + (i : ZMod (∏ j, N j)) * d) j).val =
        (ZMod.prodEquivPi N hN x j).val + i * (ZMod.prodEquivPi N hN d j).val := by
  have hb (j : J) := progressionTorusCutoff_residue_support N hk
    (crtConfigurationEquiv N hN (x, d)) h j
  change ∀ j, 2 * (ZMod.prodEquivPi N hN x j).val < N j ∧
    0 < (ZMod.prodEquivPi N hN d j).val ∧
      2 * k * (ZMod.prodEquivPi N hN d j).val < N j at hb
  refine ⟨fun j => (hb j).2.1, fun i hi j => ?_⟩
  have hv := residue_progression_val_of_windows (ZMod.prodEquivPi N hN x j)
    (ZMod.prodEquivPi N hN d j) (hb j).1 (hb j).2.2 hi
  simpa only [map_add, map_mul, map_natCast, Pi.add_apply, Pi.mul_apply, Pi.natCast_apply] using hv

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem crtProgressionWeight_mul_prod_eq_zero {J : Type*} [Fintype J] [Nonempty J]
    (N : J → ℕ) [∀ j, NeZero (N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))
    {k : ℕ} (hk : 1 ≤ k) (f : ((j : J) → ZMod (N j)) → ℝ)
    (hfree : IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k)
    (x d : ZMod (∏ j, N j)) :
    crtProgressionWeight N hN k (x, d) *
      (∏ i : Fin k, f (ZMod.prodEquivPi N hN (x + (i.val : ZMod (∏ j, N j)) * d))) = 0 := by
  classical
  by_cases hw : crtProgressionWeight N hN k (x, d) = 0
  · rw [hw, zero_mul]
  obtain ⟨hstep, hval⟩ := crtProgressionWeight_support N hN hk x d hw
  let a := residueBoxIntegerPoint N (ZMod.prodEquivPi N hN x)
  let b := residueBoxIntegerPoint N (ZMod.prodEquivPi N hN d)
  have hb : b ≠ 0 := by
    intro h
    let j : J := Classical.choice inferInstance
    have hj : b j = 0 := congrFun h j
    have hpos : (0 : ℤ) < b j := by
      dsimp [b, residueBoxIntegerPoint]
      exact_mod_cast hstep j
    omega
  obtain ⟨i, hi⟩ := hfree a b hb
  have hzero : f (ZMod.prodEquivPi N hN (x + (i.val : ZMod (∏ j, N j)) * d)) = 0 := by
    by_contra h
    apply hi
    refine ⟨ZMod.prodEquivPi N hN (x + (i.val : ZMod (∏ j, N j)) * d), h, ?_⟩
    funext j
    change ((ZMod.prodEquivPi N hN (x + (i.val : ZMod (∏ j, N j)) * d) j).val : ℤ) =
      ((ZMod.prodEquivPi N hN x j).val : ℤ) + (i.val : ℤ) * (ZMod.prodEquivPi N hN d j).val
    exact_mod_cast hval i.val i.isLt j
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero, mul_zero]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CanonicalDensityFourier
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_crtProgressionWeight_fourier {J : Type*} [Fintype J]
    (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → J × Bool → ℤ) (c : F → ℂ),
      ∀ (N : J → ℕ) [∀ j, NeZero (N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))
        (z : ZMod (∏ j, N j) × ZMod (∏ j, N j)),
        ‖(crtProgressionWeight N hN k z : ℂ) -
          ∑ a, c a * crtConfigurationCharacter N hN (frequency a) z‖ ≤ δ := by
  let L : ℝ≥0 := ((64 * k : ℕ) : ℝ≥0) / 4
  let f : ((J × Bool) → UnitAddCircle) → ℂ := fun w => (progressionTorusCutoff k w : ℂ)
  have hf : LipschitzWith L f := by
    simpa only [one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitz.comp (progressionTorusCutoff_lipschitz (J := J) k)
  have hB : ∀ w, ‖f w‖ ≤ (1 : ℝ≥0) := by
    intro w
    simpa only [f, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (progressionTorusCutoff_range k w).1, NNReal.coe_one] using
      (progressionTorusCutoff_range k w).2
  let P : ℝ := Fintype.card (J × Bool) + L + δ⁻¹
  have hi : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  have hc : (0 : ℝ) ≤ Fintype.card (J × Bool) := Nat.cast_nonneg _
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hJ : (Fintype.card (J × Bool) : ℝ) ≤ P := by dsimp [P]; linarith [L.coe_nonneg]
  have hL : (L : ℝ) ≤ Real.exp P := by
    have he := Real.add_one_le_exp P
    dsimp [P] at he
    linarith
  have hδP : δ⁻¹ ≤ Real.exp P := by
    have he := Real.add_one_le_exp P
    dsimp [P] at he
    linarith [L.coe_nonneg]
  obtain ⟨F, inst, frequency, c, _, _, _, happ⟩ :=
    exists_ambient_torus_fourier_approximation f L 1 hf hB hδ hP hJ hL hδP
  refine ⟨F, inst, frequency, c, ?_⟩
  intro N _ hN z
  exact happ (crtConfigurationTorus N hN z)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal


end Erdos3

end

section

namespace Erdos3
open scoped Classical


end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped NNReal



end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators NNReal


end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PivotStageBoundary
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem twoSlopeMap_bijective {R : Type*} [CommRing R] (a b : R) (hab : IsUnit (b - a)) :
    Function.Bijective (fun z : R × R => (z.1 + a * z.2, z.1 + b * z.2)) := by
  obtain ⟨u, hu⟩ := hab
  constructor
  · intro x y h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    have hd : (u : R) * x.2 = (u : R) * y.2 := by
      rw [hu]
      dsimp at h1 h2
      linear_combination h2 - h1
    have hxy : x.2 = y.2 := u.isUnit.mul_left_cancel hd
    apply Prod.ext
    · dsimp at h1
      rw [hxy] at h1
      exact add_right_cancel h1
    · exact hxy
  · rintro ⟨y, z⟩
    let d := (↑(u⁻¹) : R) * (z - y)
    refine ⟨(y - a * d, d), ?_⟩
    apply Prod.ext
    · dsimp
      ring
    · change y - a * d + b * d = z
      have hd : (b - a) * d = z - y := by
        rw [← hu]
        dsimp [d]
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
      linear_combination hd

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MaskedCenteredCounting
namespace OAI

universe u

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem consecutive_slopes_unit {N k : ℕ}
    (hunit : ∀ m : ℕ, 1 ≤ m → m < k → IsUnit (m : ZMod N))
    (i j : Fin k) (hij : i ≠ j) : IsUnit ((i.val : ZMod N) - (j.val : ZMod N)) := by
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hij' with hlt | hgt
  · have h := (hunit (j.val - i.val) (by omega) (by omega)).neg
    simpa only [Nat.cast_sub (Nat.le_of_lt hlt), neg_sub] using h
  · simpa only [Nat.cast_sub (Nat.le_of_lt hgt)] using
      hunit (i.val - j.val) (by omega) (by omega)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ConfigurationCharacters
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_two_slope_characters {R : Type*} [CommRing R]
    (a b : R) (hab : IsUnit (b - a)) (Psi : AddChar (R × R) ℂ) :
    ∃ chi rho : AddChar R ℂ, ∀ x d, Psi (x, d) = chi (x + a * d) * rho (x + b * d) := by
  let e : (R × R) ≃+ (R × R) := AddEquiv.ofBijective (twoSlopeAddHom a b)
    (twoSlopeMap_bijective a b hab)
  let L : R →+ (R × R) := { toFun := fun x => (x, 0), map_zero' := rfl, map_add' := by intros; simp }
  let M : R →+ (R × R) := { toFun := fun y => (0, y), map_zero' := rfl, map_add' := by intros; simp }
  refine ⟨Psi.compAddMonoidHom (e.symm.toAddMonoidHom.comp L),
    Psi.compAddMonoidHom (e.symm.toAddMonoidHom.comp M), ?_⟩
  intro x d
  change Psi (x, d) = Psi (e.symm (x + a * d, 0)) * Psi (e.symm (0, x + b * d))
  have hpair : (x + a * d, 0) + (0, x + b * d) = e (x, d) := by
    change (x + a * d, 0) + (0, x + b * d) = (x + a * d, x + b * d)
    simp
  rw [← AddChar.map_add_eq_mul, ← map_add, hpair, e.symm_apply_apply]

theorem exists_single_slope_characters {R : Type*} [CommRing R]
    (a : R) (Psi : AddChar (R × R) ℂ) :
    ∃ chi rho : AddChar R ℂ, ∀ u d, Psi (u - a * d, d) = chi u * rho d := by
  let L : R →+ (R × R) := { toFun := fun u => (u, 0), map_zero' := rfl, map_add' := by intros; simp }
  let M : R →+ (R × R) := {
    toFun := fun d => (-a * d, d)
    map_zero' := by simp
    map_add' := by intro x y; ext <;> simp [mul_add] }
  refine ⟨Psi.compAddMonoidHom L, Psi.compAddMonoidHom M, ?_⟩
  intro u d
  change Psi (u - a * d, d) = Psi (u, 0) * Psi (-a * d, d)
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ext <;> simp [sub_eq_add_neg]

theorem complex_expect_pivot_change {R : Type*} [Ring R] [Fintype R]
    (a : R) (F : R → R → ℂ) :
    (𝔼 x, 𝔼 d, F x d) = 𝔼 u, 𝔼 d, F (u - a * d) d := by
  rw [Finset.expect_comm, Finset.expect_comm (Finset.univ : Finset R) (Finset.univ : Finset R)
    (fun u d => F (u - a * d) d)]
  apply Finset.expect_congr rfl
  intro d _
  symm
  apply Fintype.expect_equiv (Equiv.addRight (-(a * d)))
  intro u
  change F (u - a * d) d = F (u + -(a * d)) d
  rw [sub_eq_add_neg]

theorem exists_single_slope_character_bound {R : Type*} [CommRing R] [Fintype R]
    (a : R) (Psi : AddChar (R × R) ℂ) (f : R → ℂ) :
    ∃ chi : AddChar R ℂ,
      ‖𝔼 x, 𝔼 d, Psi (x, d) * f (x + a * d)‖ ≤ ‖𝔼 u, chi u * f u‖ := by
  obtain ⟨chi, rho, hfactor⟩ := exists_single_slope_characters a Psi
  refine ⟨chi, ?_⟩
  rw [complex_expect_pivot_change a]
  simp only [sub_add_cancel, hfactor]
  have he : (𝔼 u, 𝔼 d, chi u * rho d * f u) =
      (𝔼 u, chi u * f u) * (𝔼 d, rho d) := by
    have hpoint (u d : R) : chi u * rho d * f u = (chi u * f u) * rho d := by ring
    simp only [hpoint, ← Finset.mul_expect, ← Finset.expect_mul]
  rw [he, norm_mul]
  have hrho : ‖𝔼 d, rho d‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    simp only [AddChar.norm_apply, Fintype.expect_const]
    exact le_rfl
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hrho (norm_nonneg _)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ConfigurationCenteredCounting
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_configuration_centered_counting (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ mu : ZMod N → ℝ, (∀ x, 0 ≤ mu x ∧ mu x ≤ Real.exp p) → (𝔼 x, mu x) = 1 →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) mu (fun _ => 1 + xi) →
      ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I], Fintype.card I ≤ s + 2 →
      ∀ (slopes : I → ZMod N), (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      ∀ Psi : AddChar (ZMod N × ZMod N) ℂ,
      ‖𝔼 x, 𝔼 d, Psi (x, d) * (∏ i, ((mu (x + slopes i * d) - 1 : ℝ) : ℂ))‖ ≤ epsilon := by
  classical
  obtain ⟨C, hC, xi, hxi, hcount⟩ := exists_character_centered_counting s hs hepsilon
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro N _ p hp hodd hN mu hmu hmean hcompare I _ _ _ hI slopes hsep Psi
  by_cases hsmall : Fintype.card I ≤ 1
  · let : Subsingleton I := Fintype.card_le_one_iff_subsingleton.mp hsmall
    let i : I := Classical.arbitrary I
    obtain ⟨chi, hchi⟩ := exists_single_slope_character_bound (slopes i) Psi
      (fun u => ((mu u - 1 : ℝ) : ℂ))
    have hsingle := hcount hp hodd hN mu hmu hmean hcompare (I := Unit)
      (by simp) (fun _ => (0 : ZMod N)) (fun _ => chi)
      (fun i j hij => (hij (Subsingleton.elim i j)).elim)
    have hsingle' : ‖𝔼 u, chi u * ((mu u - 1 : ℝ) : ℂ)‖ ≤ epsilon := by
      simpa using hsingle
    have hprod (x d : ZMod N) :
        (∏ j : I, ((mu (x + slopes j * d) - 1 : ℝ) : ℂ)) =
          ((mu (x + slopes i * d) - 1 : ℝ) : ℂ) := Fintype.prod_subsingleton _ i
    simp only [hprod]
    exact hchi.trans hsingle'
  obtain ⟨i, _, j, _, hij⟩ := Finset.one_lt_card.mp
    (show 1 < (Finset.univ : Finset I).card by simpa using (show 1 < Fintype.card I by omega))
  obtain ⟨chi, rho, hfactor⟩ := exists_two_slope_characters (slopes i) (slopes j)
    (hsep j i (Ne.symm hij)) Psi
  let theta : I → AddChar (ZMod N) ℂ := fun k => if k = i then chi else if k = j then rho else 0
  have htheta (x d : ZMod N) :
      (∏ k : I, theta k (x + slopes k * d)) = Psi (x, d) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k => theta k (x + slopes k * d)) (Finset.mem_univ i)]
    have hi : theta i (x + slopes i * d) = chi (x + slopes i * d) := by simp [theta]
    have hj : (∏ k ∈ (Finset.univ : Finset I).erase i, theta k (x + slopes k * d)) =
        rho (x + slopes j * d) := by
      rw [Finset.prod_eq_single_of_mem j (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
      · simp [theta, Ne.symm hij]
      · intro k hk hkj
        simp [theta, Finset.ne_of_mem_erase hk, hkj]
    rw [hi, hj, ← hfactor]
  have h := hcount hp hodd hN mu hmu hmean hcompare hI slopes theta hsep
  simpa only [Finset.prod_mul_distrib, htheta] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveWeightContradiction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem weighted_comparison_of_uniform_approx {X : Type*} [Fintype X] [Nonempty X]
    (W H : X → ℂ) (F : X → ℝ) {eta B error : ℝ} (heta : 0 ≤ eta)
    (hF : ∀ x, 0 ≤ F x) (hmean : (𝔼 x, F x) ≤ B)
    (happrox : ∀ x, ‖W x - H x‖ ≤ eta)
    (hH : ‖(𝔼 x, H x * (F x : ℂ)) - (𝔼 x, H x)‖ ≤ error) :
    ‖(𝔼 x, W x * (F x : ℂ)) - (𝔼 x, W x)‖ ≤ error + eta * (B + 1) := by
  have herror : ‖𝔼 x, (W x - H x) * ((F x : ℂ) - 1)‖ ≤ eta * (B + 1) := by
    calc
      _ ≤ 𝔼 x, ‖(W x - H x) * ((F x : ℂ) - 1)‖ := RCLike.norm_expect_le (K := ℂ)
      _ ≤ 𝔼 x, eta * (F x + 1) := by
        apply Finset.expect_le_expect
        intro x _
        have habs : |F x - 1| ≤ F x + 1 := abs_le.mpr ⟨by linarith [hF x], by linarith⟩
        have he : (F x : ℂ) - 1 = ((F x - 1 : ℝ) : ℂ) := by simp
        rw [norm_mul, he, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (happrox x) habs (abs_nonneg _) heta
      _ = eta * ((𝔼 x, F x) + 1) := by
        rw [← Finset.mul_expect, Finset.expect_add_distrib, Fintype.expect_const]
      _ ≤ eta * (B + 1) := mul_le_mul_of_nonneg_left (add_le_add hmean le_rfl) heta
  have heq : (𝔼 x, W x * (F x : ℂ)) - (𝔼 x, W x) =
      ((𝔼 x, H x * (F x : ℂ)) - (𝔼 x, H x)) +
        (𝔼 x, (W x - H x) * ((F x : ℂ) - 1)) := by
    calc
      _ = 𝔼 x, (W x * (F x : ℂ) - W x) := (Finset.expect_sub_distrib ..).symm
      _ = 𝔼 x, ((H x * (F x : ℂ) - H x) + (W x - H x) * ((F x : ℂ) - 1)) := by
        apply Finset.expect_congr rfl
        intro x _
        ring
      _ = _ := by rw [Finset.expect_add_distrib, Finset.expect_sub_distrib]
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hH herror)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem positive_weight_counting_contradiction {X : Type*} [Fintype X] [Nonempty X]
    (W F : X → ℝ) (H : X → ℂ) {beta eta B error : ℝ}
    (hbeta : 0 < beta) (hW : beta ≤ 𝔼 x, W x) (hF : ∀ x, 0 ≤ F x)
    (hmean : (𝔼 x, F x) ≤ B) (hvanish : ∀ x, W x * F x = 0)
    (heta : 0 ≤ eta) (happrox : ∀ x, ‖(W x : ℂ) - H x‖ ≤ eta)
    (hcount : ‖(𝔼 x, H x * (F x : ℂ)) - (𝔼 x, H x)‖ ≤ error)
    (hsmall : error + eta * (B + 1) < beta) : False := by
  have h := weighted_comparison_of_uniform_approx (fun x => (W x : ℂ)) H F
    heta hF hmean happrox hcount
  have hv (x : X) : (W x : ℂ) * (F x : ℂ) = 0 := by
    rw [← Complex.ofReal_mul, hvanish, Complex.ofReal_zero]
  simp only [hv, Fintype.expect_const, zero_sub, norm_neg, ← complex_ofReal_expect,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hbeta.le.trans hW)] at h
  linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedCenteredExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem weighted_product_count_of_centered {I X : Type*} [DecidableEq I] [Fintype X]
    (S : Finset I) (F : I → X → ℂ) (W : X → ℂ) {error : ℝ} (herror : 0 ≤ error)
    (hcentered : ∀ U ⊆ S, U.Nonempty →
      ‖𝔼 x, W x * (∏ i ∈ U, (F i x - 1))‖ ≤ error) :
    ‖(𝔼 x, W x * (∏ i ∈ S, F i x)) - (𝔼 x, W x)‖ ≤ (2 : ℝ) ^ S.card * error := by
  have hp (x : X) : (∏ i ∈ S, F i x) =
      ∑ U ∈ S.powerset, ∏ i ∈ U, (F i x - 1) := by
    simpa only [sub_add_cancel] using (Finset.prod_add_one (f := fun i => F i x - 1) S)
  have he : (𝔼 x, W x * (∏ i ∈ S, F i x)) - (𝔼 x, W x) =
      ∑ U ∈ S.powerset.erase ∅, 𝔼 x, W x * (∏ i ∈ U, (F i x - 1)) := by
    simp only [hp, Finset.mul_sum, Finset.expect_sum_comm]
    rw [← Finset.sum_erase_add _ _ (show ∅ ∈ S.powerset by simp)]
    simp
  rw [he]
  calc
    _ ≤ ∑ U ∈ S.powerset.erase ∅, ‖𝔼 x, W x * (∏ i ∈ U, (F i x - 1))‖ := norm_sum_le _ _
    _ ≤ ∑ _U ∈ S.powerset.erase ∅, error := by
      apply Finset.sum_le_sum
      intro U hU
      exact hcentered U (Finset.mem_powerset.mp (Finset.mem_of_mem_erase hU))
        (Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hU))
    _ = ((S.powerset.erase ∅).card : ℝ) * error := by simp
    _ ≤ (S.powerset.card : ℝ) * error := mul_le_mul_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card (Finset.erase_subset ∅ S.powerset)) herror
    _ = _ := by simp

theorem norm_expect_finite_weighted_sum_le {J X : Type*} [Fintype J] [Fintype X]
    (c : J → ℂ) (H : J → X → ℂ) (f : X → ℂ) {error : ℝ}
    (h : ∀ j, ‖𝔼 x, H j x * f x‖ ≤ error) :
    ‖𝔼 x, (∑ j, c j * H j x) * f x‖ ≤ (∑ j, ‖c j‖) * error := by
  have he : (𝔼 x, (∑ j, c j * H j x) * f x) = ∑ j, c j * (𝔼 x, H j x * f x) := by
    simp only [Finset.sum_mul, Finset.expect_sum_comm, mul_assoc, ← Finset.mul_expect]
  rw [he]
  calc
    _ ≤ ∑ j, ‖c j * (𝔼 x, H j x * f x)‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖c j‖ * error := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (h j) (norm_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FourierWeightedCounting
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_fourier_weighted_counting (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ mu : ZMod N → ℝ, (∀ x, 0 ≤ mu x ∧ mu x ≤ Real.exp p) → (𝔼 x, mu x) = 1 →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) mu (fun _ => 1 + xi) →
      ∀ {I : Type} [DecidableEq I] (slopes : I → ZMod N),
      (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      ∀ S : Finset I, S.card ≤ s + 2 →
      ∀ {J : Type} [Fintype J] (c : J → ℂ) (Psi : J → AddChar (ZMod N × ZMod N) ℂ),
        ‖(𝔼 x, 𝔼 d, configurationFourierWeight c Psi (x, d) *
            (∏ i ∈ S, (mu (x + slopes i * d) : ℂ))) -
          (𝔼 x, 𝔼 d, configurationFourierWeight c Psi (x, d))‖ ≤ (∑ j, ‖c j‖) * epsilon := by
  let delta := epsilon / (2 : ℝ) ^ (s + 2)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨C, hC, xi, hxi, hcount⟩ := exists_configuration_centered_counting s hs hdelta
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro N _ p hp hodd hN mu hmu hmean hcompare I _ slopes hsep S hS J _ c Psi
  let F : I → (ZMod N × ZMod N) → ℂ := fun i z => (mu (z.1 + slopes i * z.2) : ℂ)
  let W := configurationFourierWeight c Psi
  let L : ℝ := ∑ j, ‖c j‖
  have hL : 0 ≤ L := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hcenter (U : Finset I) (hUS : U ⊆ S) (hU : U.Nonempty) :
      ‖𝔼 z, W z * (∏ i ∈ U, (F i z - 1))‖ ≤ L * delta := by
    let : Nonempty U := ⟨⟨hU.choose, hU.choose_spec⟩⟩
    apply norm_expect_finite_weighted_sum_le c (fun j z => Psi j z) (fun z => ∏ i ∈ U, (F i z - 1))
    intro j
    have hcard : Fintype.card U ≤ s + 2 := by
      simpa only [Fintype.card_coe] using (Finset.card_le_card hUS).trans hS
    have h := hcount hp hodd hN mu hmu hmean hcompare (I := U) hcard
      (fun i => slopes i.val)
      (fun i k hik => hsep i.val k.val (fun h => hik (Subtype.ext h))) (Psi j)
    have hprod (x d : ZMod N) :
        (∏ i : U, ((mu (x + slopes i.val * d) - 1 : ℝ) : ℂ)) =
          ∏ i ∈ U, ((mu (x + slopes i * d) - 1 : ℝ) : ℂ) :=
      Finset.prod_coe_sort (s := U) (f := fun i : I => ((mu (x + slopes i * d) - 1 : ℝ) : ℂ))
    simp only [hprod] at h
    rw [expect_prod_split]
    simpa only [F, Complex.ofReal_sub, Complex.ofReal_one] using h
  have h := weighted_product_count_of_centered S F W (mul_nonneg hL hdelta.le) hcenter
  have hbound : (2 : ℝ) ^ S.card * (L * delta) ≤ L * epsilon := by
    calc
      _ = L * ((2 : ℝ) ^ S.card * delta) := by ring
      _ ≤ L * ((2 : ℝ) ^ (s + 2) * delta) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hS) hdelta.le) hL
      _ = L * epsilon := by congr 1; dsimp [delta]; field_simp
  simpa only [expect_prod_split, F, W, L] using h.trans hbound

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AbsoluteCRTWindow
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_crt_counting_contradiction_oai {J : Type*} [Fintype J] [Nonempty J]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
    ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
      (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) {p : ℝ},
      2 ≤ p → Odd (∏ j, N j) → Real.exp ((p + 2) ^ C) ≤ (∏ j, N j) →
      (∀ j, 64 * k ≤ N j) →
      (∀ m : ℕ, 1 ≤ m → m < k → IsUnit (m : ZMod (∏ j, N j))) →
      ∀ f : ((j : J) → ZMod (N j)) → ℝ,
      (∀ u, 0 ≤ f u ∧ f u ≤ Real.exp p) →
      (𝔼 x : ZMod (∏ j, N j), f (ZMod.prodEquivPi N hN x)) = 1 →
      IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k →
      ¬ CyclicNiltestUpperComparison.{0} (k - 2) (∏ j, N j) ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (fun x => f (ZMod.prodEquivPi N hN x)) (fun _ => 1 + xi) := by
  classical
  let beta : ℝ := min 1 (1 / (2 * (128 * (k : ℝ)) ^ (Fintype.card J * 2)))
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hbeta : 0 < beta := lt_min (by norm_num) (by positivity)
  have hbeta1 : beta ≤ 1 := min_le_left _ _
  let eta := beta / 8
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨F, inst, frequency, c, happ⟩ := exists_crtProgressionWeight_fourier (J := J) k heta
  let _ := inst
  let L : ℝ := ∑ a, ‖c a‖
  have hL : 0 ≤ L := Finset.sum_nonneg (fun a _ => norm_nonneg _)
  let epsilon := beta / (8 * (L + 1))
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hL1 : L + 1 ≠ 0 := by linarith
  have heq : (L + 1) * epsilon = beta / 8 := by dsimp [epsilon]; field_simp [hL1]
  have hepsilon1 : epsilon ≤ 1 := by nlinarith [mul_nonneg hL hepsilon.le]
  have hsmall : L * epsilon + eta * ((2 : ℝ) + 1) < beta := by dsimp [eta]; nlinarith
  obtain ⟨C, hC, xi, hxi, hcount⟩ := exists_fourier_weighted_counting (k - 2) (by omega) hepsilon
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro N _ _ hN p hp hodd hlarge hsize hunit f hf hmean hfree hcompare
  let mu : ZMod (∏ j, N j) → ℝ := fun x => f (ZMod.prodEquivPi N hN x)
  let slopes : Fin k → ZMod (∏ j, N j) := fun i => i.val
  have hsep (i j : Fin k) (hij : i ≠ j) : IsUnit (slopes i - slopes j) :=
    consecutive_slopes_unit hunit i j hij
  have hcard : (Finset.univ : Finset (Fin k)).card ≤ k - 2 + 2 := by simp; omega
  let G : (ZMod (∏ j, N j) × ZMod (∏ j, N j)) → ℝ :=
    fun z => ∏ i : Fin k, mu (z.1 + slopes i * z.2)
  have hG0 (z) : 0 ≤ G z := Finset.prod_nonneg (fun i _ => (hf _).1)
  have hconst := hcount hp hodd hlarge mu (fun x => hf _) hmean hcompare
    slopes hsep Finset.univ hcard (fun _ : Unit => (1 : ℂ)) (fun _ => 1)
  have hGclose : ‖(𝔼 z, (G z : ℂ)) - 1‖ ≤ epsilon := by
    simpa [configurationFourierWeight, expect_prod_split, G, Complex.ofReal_prod] using hconst
  have hGmean : (𝔼 z, G z) ≤ 2 :=
    (real_mean_le_of_complex_mean_close G hGclose).trans (by linarith)
  let Psi : F → AddChar (ZMod (∏ j, N j) × ZMod (∏ j, N j)) ℂ :=
    fun a => crtConfigurationCharacter N hN (frequency a)
  let H := configurationFourierWeight c Psi
  have hH : ‖(𝔼 z, H z * (G z : ℂ)) - (𝔼 z, H z)‖ ≤ L * epsilon := by
    have h := hcount hp hodd hlarge mu (fun x => hf _) hmean hcompare
      slopes hsep Finset.univ hcard c Psi
    simpa only [expect_prod_split, G, Complex.ofReal_prod, H, L] using h
  apply positive_weight_counting_contradiction (crtProgressionWeight N hN k) G H hbeta
    ((min_le_right _ _).trans (crtProgressionWeight_mean N hN (by omega) hsize))
    hG0 hGmean _ heta.le (happ N hN) hH hsmall
  intro z
  exact crtProgressionWeight_mul_prod_eq_zero N hN (by omega) f hfree z.1 z.2

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.exists_crt_counting_contradiction_oai.{u_1} := @OAI.Erdos3.exists_crt_counting_contradiction_oai.{u_1}
