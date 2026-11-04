-- Prove2me | solution 1 for OAI.FreeGroupFactorMain.FiniteActive.extension_at_time
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T03:53:27.001556+00:00
-- url     : https://prove2.me/submissions/24910fb8-1860-496a-93b0-cf0dcc68edc1

import Mathlib
import Definitions.Def_FreeGroupFactorProof18
import Theorems.Thm_OAI_FreeGroupFactorMain_FiniteActive_moments

set_option linter.all false

section
namespace OAI

noncomputable section

universe uA uE uι

open Set Metric
open scoped NNReal Topology

open Set Metric
open scoped NNReal Topology
namespace FreeGroupFactorMain

theorem global_solution_of_bounded_lipschitz
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (K L : ℝ≥0) (hf : LipschitzWith K f)
    (hbound : ∀ x, ‖f x‖ ≤ L) (x₀ : E) :
    ∃ X : ℝ → E, X 0 = x₀ ∧ ∀ t, HasDerivAt X (f (X t)) t := by
  have hlocal (R : ℝ) (hR : 0 < R) :
      ∃ X : ℝ → E, X 0 = x₀ ∧
        ∀ t ∈ Ioo (-R) R, HasDerivAt X (f (X t)) t := by
    let r : ℝ≥0 := NNReal.mk R hR.le
    have hp : IsPicardLindelof (fun _ : ℝ => f)
        (⟨0, by constructor <;> linarith⟩ : Icc (-R) R)
        x₀ (L * r) 0 L K := by
      constructor
      · intro t ht
        exact hf.lipschitzOnWith
      · intro x hx
        exact continuousOn_const
      · intro t ht x hx
        exact hbound x
      · simp [r, NNReal.coe_mul]
    obtain ⟨X, hX₀, hX⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨X, hX₀, fun t ht => ?_⟩
    exact (hX t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  choose sol init deriv using hlocal
  have agree (R Q : ℝ) (hR : 0 < R) (hQ : 0 < Q) (t : ℝ)
      (htR : t ∈ Ioo (-R) R) (htQ : t ∈ Ioo (-Q) Q) :
      sol R hR t = sol Q hQ t := by
    have hm : 0 < min R Q := lt_min hR hQ
    have heq : EqOn (sol R hR) (sol Q hQ) (Ioo (-min R Q) (min R Q)) := by
      apply ODE_solution_unique_of_mem_Ioo
        (v := fun _ : ℝ => f) (s := fun _ => univ) (t₀ := 0)
        (fun _ _ => hf.lipschitzOnWith)
        (by constructor <;> linarith) _ _ (by rw [init, init])
      · intro u hu
        refine ⟨deriv R hR u ?_, mem_univ _⟩
        constructor <;> have := min_le_left R Q <;> linarith [hu.1, hu.2]
      · intro u hu
        refine ⟨deriv Q hQ u ?_, mem_univ _⟩
        constructor <;> have := min_le_right R Q <;> linarith [hu.1, hu.2]
    apply heq
    constructor
    · have hh : -t < min R Q := lt_min (by linarith [htR.1]) (by linarith [htQ.1])
      linarith
    · exact lt_min htR.2 htQ.2
  let X : ℝ → E := fun t => sol (|t| + 1) (by positivity) t
  have hEq (R : ℝ) (hR : 0 < R) : EqOn X (sol R hR) (Ioo (-R) R) := by
    intro t ht
    apply agree
    · constructor <;> linarith [neg_abs_le t, le_abs_self t]
    · exact ht
  refine ⟨X, ?_, fun t => ?_⟩
  · exact init _ _
  · let R := |t| + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have ht : t ∈ Ioo (-R) R := by
      dsimp [R]
      constructor <;> linarith [neg_abs_le t, le_abs_self t]
    have hh : X =ᶠ[nhds t] sol R hR :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) (hEq R hR)
    rw [hEq R hR ht]
    exact (deriv R hR t ht).congr_of_eventuallyEq hh

end FreeGroupFactorMain

open scoped NNReal
namespace FreeGroupFactorMain

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialClip (x : E) : E := (max 1 ‖x‖)⁻¹ • x

theorem radialClip_eq {x : E} (hx : ‖x‖ ≤ 1) : radialClip x = x := by
  simp [radialClip, max_eq_left hx]

theorem norm_radialClip_le (x : E) : ‖radialClip x‖ ≤ 1 := by
  have ha : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [radialClip, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ha]
  simpa only [div_eq_mul_inv, mul_comm] using (div_le_one ha).mpr (le_max_right 1 ‖x‖)

theorem radialClip_lipschitz : LipschitzWith 2 (radialClip : E → E) := by
  have hle (x y : E) (hxy : max 1 ‖y‖ ≤ max 1 ‖x‖) :
      ‖radialClip x - radialClip y‖ ≤ 2 * ‖x - y‖ := by
    let a := max 1 ‖x‖
    let b := max 1 ‖y‖
    have ha1 : 1 ≤ a := le_max_left _ _
    have hb1 : 1 ≤ b := le_max_left _ _
    have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
    have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
    have hba : b ≤ a := hxy
    have hiny : ‖y‖ ≤ b := le_max_right _ _
    have hdiff : a - b ≤ ‖x - y‖ := by
      have := (lipschitzWith_one_norm.const_max 1).dist_le_mul x y
      exact (le_abs_self (a - b)).trans (by simpa [a, b, Real.dist_eq, dist_eq_norm] using this)
    have hinv : a⁻¹ ≤ b⁻¹ := inv_anti₀ hb hba
    have hterm : (b⁻¹ - a⁻¹) * ‖y‖ ≤ a - b := by
      calc
        (b⁻¹ - a⁻¹) * ‖y‖ = (a - b) * (‖y‖ / (a * b)) := by
          field_simp
        _ ≤ (a - b) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hba)
          apply (div_le_one (mul_pos ha hb)).mpr
          exact hiny.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hb.le])
        _ = a - b := mul_one _
    have hfirst : a⁻¹ * ‖x - y‖ ≤ ‖x - y‖ :=
      mul_le_of_le_one_left (norm_nonneg _) ((inv_le_one₀ ha).mpr ha1)
    have hid : radialClip x - radialClip y =
        a⁻¹ • (x - y) + (a⁻¹ - b⁻¹) • y := by
      dsimp [radialClip, a, b]
      module
    rw [hid]
    calc
      ‖a⁻¹ • (x - y) + (a⁻¹ - b⁻¹) • y‖ ≤
          ‖a⁻¹ • (x - y)‖ + ‖(a⁻¹ - b⁻¹) • y‖ := norm_add_le _ _
      _ = a⁻¹ * ‖x - y‖ + (b⁻¹ - a⁻¹) * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr ha), abs_of_nonpos (sub_nonpos.mpr hinv)]
        ring
      _ ≤ 2 * ‖x - y‖ := by linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_ofNat, dist_eq_norm]
  rcases le_total (max 1 ‖y‖) (max 1 ‖x‖) with h | h
  · exact hle x y h
  · simpa only [norm_sub_rev (radialClip y), norm_sub_rev y] using hle y x h

end FreeGroupFactorMain

open scoped NNReal BigOperators
namespace FreeGroupFactorMain

variable {E : Type uE} {A : Type uA} [NormedAddCommGroup E] [NormedRing A]

def BoundedLip (f : E → A) : Prop :=
  ∃ M K : ℝ, 0 ≤ M ∧ 0 ≤ K ∧ (∀ x, ‖f x‖ ≤ M) ∧
    ∀ x y, ‖f x - f y‖ ≤ K * ‖x - y‖

namespace BoundedLip

theorem const (c : A) : BoundedLip (fun _ : E => c) := by
  refine ⟨‖c‖, 0, norm_nonneg _, le_rfl, fun _ => le_rfl, ?_⟩
  intro x y
  simp

theorem add {f g : E → A} (hf : BoundedLip f) (hg : BoundedLip g) :
    BoundedLip (fun x => f x + g x) := by
  obtain ⟨M, K, hM, hK, hfb, hfl⟩ := hf
  obtain ⟨N, L, hN, hL, hgb, hgl⟩ := hg
  refine ⟨M + N, K + L, add_nonneg hM hN, add_nonneg hK hL, ?_, ?_⟩
  · intro x
    exact (norm_add_le _ _).trans (add_le_add (hfb x) (hgb x))
  · intro x y
    rw [show f x + g x - (f y + g y) = (f x - f y) + (g x - g y) by abel]
    exact (norm_add_le _ _).trans (by nlinarith only [hfl x y, hgl x y])

theorem mul {f g : E → A} (hf : BoundedLip f) (hg : BoundedLip g) :
    BoundedLip (fun x => f x * g x) := by
  obtain ⟨M, K, hM, hK, hfb, hfl⟩ := hf
  obtain ⟨N, L, hN, hL, hgb, hgl⟩ := hg
  refine ⟨M * N, M * L + K * N, mul_nonneg hM hN,
    add_nonneg (mul_nonneg hM hL) (mul_nonneg hK hN), ?_, ?_⟩
  · intro x
    exact (norm_mul_le _ _).trans (mul_le_mul (hfb x) (hgb x) (norm_nonneg _) hM)
  · intro x y
    calc
      ‖f x * g x - f y * g y‖ =
          ‖f x * (g x - g y) + (f x - f y) * g y‖ := by
        congr 1
        noncomm_ring
      _ ≤ ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ M * (L * ‖x - y‖) + (K * ‖x - y‖) * N := by
        exact add_le_add
          (mul_le_mul (hfb x) (hgl x y) (norm_nonneg _) hM)
          (mul_le_mul (hfl x y) (hgb y) (norm_nonneg _)
            (mul_nonneg hK (norm_nonneg _)))
      _ = (M * L + K * N) * ‖x - y‖ := by ring

theorem star [StarRing A] [NormedStarGroup A] {f : E → A} (hf : BoundedLip f) :
    BoundedLip (fun x => star (f x)) := by
  obtain ⟨M, K, hM, hK, hfb, hfl⟩ := hf
  refine ⟨M, K, hM, hK, ?_, ?_⟩
  · simpa only [norm_star] using hfb
  · simpa only [← star_sub, norm_star] using hfl

theorem sum {ι : Type uι} (s : Finset ι) (f : ι → E → A)
    (hf : ∀ i ∈ s, BoundedLip (f i)) : BoundedLip (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (E := E) (0 : A))
  | @insert i s hi ih =>
    simpa [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem smul [NormedAlgebra ℂ A] (c : ℂ) {f : E → A} (hf : BoundedLip f) :
    BoundedLip (fun x => c • f x) := by
  simpa only [Algebra.smul_def] using (const (E := E) (algebraMap ℂ A c)).mul hf

theorem pi {ι : Type uι} [Fintype ι] {f : E → ι → A}
    (hf : ∀ i, BoundedLip (fun x => f x i)) : BoundedLip f := by
  classical
  choose M K hM hK hb hl using hf
  have hMs (i : ι) : M i ≤ ∑ j, M j :=
    Finset.single_le_sum (fun j _ => hM j) (Finset.mem_univ i)
  have hKs (i : ι) : K i ≤ ∑ j, K j :=
    Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ i)
  have hMsum : 0 ≤ ∑ j, M j := Finset.sum_nonneg fun j _ => hM j
  have hKsum : 0 ≤ ∑ j, K j := Finset.sum_nonneg fun j _ => hK j
  refine ⟨∑ j, M j, ∑ j, K j, hMsum, hKsum, ?_, ?_⟩
  · intro x
    exact (pi_norm_le_iff_of_nonneg hMsum).mpr fun i => (hb i x).trans (hMs i)
  · intro x y
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hKsum (norm_nonneg _))).mpr
    intro i
    exact (hl i x y).trans (mul_le_mul_of_nonneg_right (hKs i) (norm_nonneg _))

theorem to_bounds {f : E → A} (hf : BoundedLip f) :
    ∃ M K : ℝ≥0, (∀ x, ‖f x‖ ≤ M) ∧ LipschitzWith K f := by
  obtain ⟨M, K, hM, hK, hb, hl⟩ := hf
  refine ⟨NNReal.mk M hM, NNReal.mk K hK, hb, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_mk] using hl x y

end BoundedLip
end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uι

open Set Metric
open scoped NNReal Topology BigOperators

open scoped BigOperators ContDiff
namespace FreeGroupFactorMain
namespace PolynomialFlow

section

variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

 omit [Fintype ι] in
 theorem selfAdjoint_hamiltonian (S : A) (hS : IsSelfAdjoint S)
    (h : FreeGroup ι →₀ ℝ) (X : ι → A) : IsSelfAdjoint (hamiltonian S h X) := by
  classical
  unfold hamiltonian Finsupp.sum
  change star (∑ g ∈ h.support, (h g : ℂ) • (word g X * S * star (word g X))) = _
  simp only [star_sum, star_smul, Complex.star_def, Complex.conj_ofReal, star_mul, star_star, hS.star_eq, mul_assoc]

end

section
open scoped NNReal BigOperators
variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem boundedLip_clip_coordinate (j : ι) :
    BoundedLip (fun X : ι → A => radialClip X j) := by
  refine ⟨1, 2, by positivity, by positivity, ?_, ?_⟩
  · intro X
    exact (norm_le_pi_norm (radialClip X) j).trans (norm_radialClip_le X)
  · intro X Y
    exact (norm_le_pi_norm (radialClip X - radialClip Y) j).trans
      (by simpa only [dist_eq_norm, NNReal.coe_ofNat] using radialClip_lipschitz.dist_le_mul X Y)

omit [DecidableEq ι] in
theorem boundedLip_clip_wordList (w : List (ι × Bool)) :
    BoundedLip (fun X : ι → A => wordList w (radialClip X)) := by
  induction w with
  | nil => exact BoundedLip.const 1
  | cons a w ih =>
    rcases a with ⟨i, b⟩
    cases b
    · exact (boundedLip_clip_coordinate i).star.mul ih
    · exact (boundedLip_clip_coordinate i).mul ih

theorem boundedLip_clip_word (g : FreeGroup ι) :
    BoundedLip (fun X : ι → A => word g (radialClip X)) :=
  boundedLip_clip_wordList _

theorem boundedLip_clip_hamiltonian (S : A) (h : FreeGroup ι →₀ ℝ) :
    BoundedLip (fun X : ι → A => hamiltonian S h (radialClip X)) := by
  classical
  unfold hamiltonian Finsupp.sum
  apply BoundedLip.sum
  intro g hg
  exact ((boundedLip_clip_word g).mul (BoundedLip.const S) |>.mul
    (boundedLip_clip_word g).star).smul (h g : ℂ)

theorem boundedLip_clip_field (S : A) (h : ι → FreeGroup ι →₀ ℝ) :
    BoundedLip (fun X => field S h (radialClip X)) := by
  apply BoundedLip.pi
  intro j
  exact ((boundedLip_clip_hamiltonian S (h j)).mul
    (boundedLip_clip_coordinate j)).smul Complex.I

theorem tangent_clipped (S : A) (hS : IsSelfAdjoint S)
    (h : ι → FreeGroup ι →₀ ℝ) (X : ι → A) (j : ι) :
    star (field S h (radialClip X) j) * X j +
      star (X j) * field S h (radialClip X) j = 0 := by
  let r : ℝ := (max 1 ‖X‖)⁻¹
  have he : radialClip X j = r • X j := rfl
  simp only [field, he, mul_smul_comm, smul_comm Complex.I r, star_smul,
    star_trivial, star_mul, (selfAdjoint_hamiltonian S hS (h j) (radialClip X)).star_eq,
    Complex.star_def, Complex.conj_I, neg_smul, neg_mul, smul_mul_assoc,
    mul_assoc]
  module

theorem global_unitary_solution [Nontrivial A]
    (S : A) (hS : IsSelfAdjoint S) (h : ι → FreeGroup ι →₀ ℝ)
    (V : ι → A) (hV : ∀ j, V j ∈ unitary A) :
    ∃ X : ℝ → ι → A, X 0 = V ∧
      (∀ t, HasDerivAt X (field S h (X t)) t) ∧
      ∀ t j, X t j ∈ unitary A := by
  obtain ⟨M, K, hb, hl⟩ := (boundedLip_clip_field S h).to_bounds
  obtain ⟨X, hX₀, hX⟩ := global_solution_of_bounded_lipschitz
    (fun X => field S h (radialClip X)) K M hl hb V
  have hd (j : ι) (t : ℝ) :
      HasDerivAt (fun u => star (X u j) * X u j) 0 t := by
    have hj := hasDerivAt_pi.mp (hX t) j
    convert! hj.star.mul hj using 1
    exact (tangent_clipped S hS h (X t) j).symm
  have hisom (t : ℝ) (j : ι) : star (X t j) * X t j = 1 := by
    have he := is_const_of_deriv_eq_zero (fun u => (hd j u).differentiableAt)
      (fun u => (hd j u).deriv) t 0
    rw [he, hX₀]
    exact (Unitary.mem_iff.mp (hV j)).1
  have hn (t : ℝ) : ‖X t‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    have he := congrArg norm (hisom t j)
    rw [CStarRing.norm_star_mul_self, norm_one] at he
    nlinarith [norm_nonneg (X t j)]
  have hder (t : ℝ) : HasDerivAt X (field S h (X t)) t := by
    simpa only [radialClip_eq (hn t)] using hX t
  refine ⟨X, hX₀, hder, ?_⟩
  intro t j
  have hc : Continuous (fun u => X u j) :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_pi.mp (hder u) j).continuousAt
  have hset : {u | X u j ∈ unitary A} = {u | IsUnit (X u j)} := by
    ext u
    constructor
    · intro hu
      exact Unitary.isUnit_coe (U := ⟨X u j, hu⟩)
    · exact fun hu => hu.mem_unitary_of_star_mul_self (hisom u j)
  have hcl : IsClosed {u | X u j ∈ unitary A} := isClosed_unitary.preimage hc
  have hop : IsOpen {u | X u j ∈ unitary A} := by
    rw [hset]
    exact Units.isOpen.preimage hc
  have hall := (IsClopen.eq_univ ⟨hcl, hop⟩ ⟨0, by change X 0 j ∈ unitary A; rw [hX₀]; exact hV j⟩)
  exact (show t ∈ {u | X u j ∈ unitary A} from by rw [hall]; trivial)

end

variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem norm_unitary_tuple_le [Nontrivial A] (V : ι → A)
    (hV : ∀ j, V j ∈ unitary A) : ‖V‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  exact (CStarRing.norm_of_mem_unitary (hV j)).le

theorem unitary_solutions_unique [Nontrivial A]
    (S : A) (h : ι → FreeGroup ι →₀ ℝ) (X Y : ℝ → ι → A)
    (hX : ∀ t, HasDerivAt X (field S h (X t)) t)
    (hY : ∀ t, HasDerivAt Y (field S h (Y t)) t)
    (hUX : ∀ t j, X t j ∈ unitary A) (hUY : ∀ t j, Y t j ∈ unitary A)
    (t₀ : ℝ) (hinit : X t₀ = Y t₀) : X = Y := by
  obtain ⟨M, K, _hb, hl⟩ := (boundedLip_clip_field S h).to_bounds
  funext t
  let R := |t| + |t₀| + 1
  have ht : t ∈ Set.Ioo (-R) R := by
    dsimp [R]
    constructor <;> linarith [neg_abs_le t, le_abs_self t, abs_nonneg t₀]
  have ht₀ : t₀ ∈ Set.Ioo (-R) R := by
    dsimp [R]
    constructor <;> linarith [neg_abs_le t₀, le_abs_self t₀, abs_nonneg t]
  have heq : Set.EqOn X Y (Set.Ioo (-R) R) := by
    apply ODE_solution_unique_of_mem_Ioo
      (v := fun _ Z => field S h (radialClip Z)) (s := fun _ => Set.univ) (t₀ := t₀)
      (fun _ _ => hl.lipschitzOnWith) ht₀ _ _ hinit
    · intro u _
      rw [radialClip_eq (norm_unitary_tuple_le _ (hUX u))]
      exact ⟨hX u, Set.mem_univ _⟩
    · intro u _
      rw [radialClip_eq (norm_unitary_tuple_le _ (hUY u))]
      exact ⟨hY u, Set.mem_univ _⟩
  exact heq ht

end PolynomialFlow
end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

open scoped ENNReal

def rightRegular {G : Type uG} [Group G] (g : G) : GroupOperator G :=
  (hilbertReindex (Equiv.mulRight g⁻¹)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem rightRegular_apply {G : Type uG} [Group G] (g : G)
    (ξ : GroupHilbert G) (h : G) : rightRegular g ξ h = ξ (h * g) := by
  simp [rightRegular]

@[simp] theorem rightRegular_star {G : Type uG} [Group G] (g : G) :
    star (rightRegular g) = rightRegular g⁻¹ := by
  change star ((hilbertReindex (Equiv.mulRight g⁻¹)) : GroupOperator G) = _
  rw [LinearIsometryEquiv.star_eq_symm]
  ext ξ b
  change ξ (b * g⁻¹) = rightRegular g⁻¹ ξ b
  rw [rightRegular_apply]

theorem left_right_commute {G : Type uG} [Group G] (g h : G) :
    leftRegular g * rightRegular h = rightRegular h * leftRegular g := by
  ext ξ b
  simp [mul_assoc]

theorem rightRegular_mem_commutant {G : Type uG} [Group G] (g : G) :
    rightRegular g ∈ StarSubalgebra.centralizer ℂ (leftTranslations G) := by
  rw [StarSubalgebra.mem_centralizer_iff, leftTranslations_eq_range]
  rintro _ ⟨h, rfl⟩
  exact ⟨left_right_commute h g, by simp only [leftRegular_star]; exact left_right_commute _ _⟩

theorem groupVN_commute_right {G : Type uG} [Group G] (T : groupVonNeumann G) (g : G) :
    rightRegular g * (T : GroupOperator G) = (T : GroupOperator G) * rightRegular g :=
  ((StarSubalgebra.mem_centralizer_iff ℂ).mp T.property _ (rightRegular_mem_commutant g)).1

theorem canonicalTrace_eq_inner {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) :
    canonicalTrace T = inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
      ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))) := by
  classical
  simp only [canonicalTrace, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
  apply congrArg (fun v : GroupHilbert G => ((T : GroupOperator G) v) 1)
  ext b
  simp [lp.single_apply, Pi.single_apply]

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

 def groupUnitaryHom (G : Type uG) [Group G] : G →* groupVonNeumann G where
  toFun := groupUnitary
  map_one' := Subtype.ext (leftRegular_one)
  map_mul' g b := Subtype.ext (leftRegular_mul g b)

end FreeGroupFactorMain

namespace FreeGroupFactorMain.UnitaryEvaluation
open scoped ContDiff
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain
open scoped ContDiff

 theorem wordHom_generatorUnitary {ι : Type uι} (g : FreeGroup ι) :
    UnitaryEvaluation.wordHom generatorUnitary g = groupUnitary g := by
  have he : UnitaryEvaluation.wordHom (generatorUnitary (ι := ι)) =
      groupUnitaryHom (FreeGroup ι) := by
    apply FreeGroup.ext_hom
    intro i
    rfl
  exact DFunLike.congr_fun he g

end FreeGroupFactorMain

namespace FreeGroupFactorMain.PolynomialFlow
variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [Nontrivial A] [Fintype ι] [DecidableEq ι] in
theorem coe_wordList (E : StarSubalgebra ℂ A) [IsClosed (E : Set A)] (w : List (ι × Bool)) (X : ι → E) :
    ((wordList w X : E) : A) = wordList w (fun i => (X i : A)) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨i, b⟩
    cases b <;> simpa [wordList] using
      congrArg (fun z : A => _ * z) ih

omit [Nontrivial A] [Fintype ι] in
theorem coe_field (E : StarSubalgebra ℂ A) [IsClosed (E : Set A)] (S : E)
    (h : ι → FreeGroup ι →₀ ℝ) (X : ι → E) (j : ι) :
    ((field S h X j : E) : A) = field (S : A) h (fun i => (X i : A)) j := by
  classical
  simp [field, hamiltonian, Finsupp.sum, word, coe_wordList]

theorem solution_mem_subalgebra (E : StarSubalgebra ℂ A) (hE : IsClosed (E : Set A))
    (S : A) (hS : IsSelfAdjoint S) (hSE : S ∈ E) (h : ι → FreeGroup ι →₀ ℝ)
    (X : ℝ → ι → A) (hX : ∀ t, HasDerivAt X (field S h (X t)) t)
    (hU : ∀ t j, X t j ∈ unitary A) (t₀ : ℝ) (h₀ : ∀ j, X t₀ j ∈ E) :
    ∀ t j, X t j ∈ E := by
  let : IsClosed (E : Set A) := hE
  let S' : E := ⟨S, hSE⟩
  let V : ι → E := fun j => ⟨X t₀ j, h₀ j⟩
  have hS' : IsSelfAdjoint S' := Subtype.ext hS
  have hV : ∀ j, V j ∈ unitary E := by
    intro j
    rw [Unitary.mem_iff]
    exact ⟨Subtype.ext (hU t₀ j).1, Subtype.ext (hU t₀ j).2⟩
  obtain ⟨Y, hY₀, hY, hUY⟩ := global_unitary_solution S' hS' h V hV
  let L : (ι → E) →L[ℝ] (ι → A) :=
    ContinuousLinearMap.pi fun j =>
      (E.toSubalgebra.toSubmodule.subtypeL.restrictScalars ℝ).comp
        (ContinuousLinearMap.proj j)
  let Z : ℝ → ι → A := fun t => L (Y (t - t₀))
  have hZ : ∀ t, HasDerivAt Z (field S h (Z t)) t := by
    intro t
    have hd := (hY (t - t₀)).scomp t ((hasDerivAt_id t).sub_const t₀)
    have hm := L.hasFDerivAt.comp_hasDerivAt t hd
    have hm' : HasDerivAt Z (L (field S' h (Y (t - t₀)))) t := by
      simpa only [Function.comp_def, id_eq, one_smul, Z] using hm
    have hf : L (field S' h (Y (t - t₀))) = field S h (Z t) := by
      ext j
      exact coe_field E S' h (Y (t - t₀)) j
    rw [hf] at hm'
    exact hm'
  have hUZ : ∀ t j, Z t j ∈ unitary A := by
    intro t j
    exact ⟨congrArg Subtype.val (hUY (t - t₀) j).1,
      congrArg Subtype.val (hUY (t - t₀) j).2⟩
  have heq : X = Z := unitary_solutions_unique S h X Z hX hZ hU hUZ t₀ (by
    ext j
    change X t₀ j = ((Y (t₀ - t₀) j : E) : A)
    rw [sub_self, hY₀])
  intro t j
  rw [heq]
  exact (Y (t - t₀) j).property

end FreeGroupFactorMain.PolynomialFlow

end

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

open scoped ComplexConjugate

theorem deltaOne_eq {G : Type uG} [Group G] [DecidableEq G] :
    (deltaOne : GroupHilbert G) = lp.single 2 1 1 := by
  ext x
  simp [deltaOne, lp.single_apply, Pi.single_apply]

theorem groupVN_matrix {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) (x y : G) :
    ((T : GroupOperator G) (lp.single 2 y 1)) x =
      ((T : GroupOperator G) deltaOne) (x * y⁻¹) := by
  have hr : rightRegular y⁻¹ deltaOne = lp.single 2 y 1 := by
    ext b
    simp [deltaOne, lp.single_apply, Pi.single_apply, mul_inv_eq_one]
  rw [← hr]
  have hc := congrArg (fun f : GroupOperator G => f deltaOne)
    (groupVN_commute_right T y⁻¹)
  simpa only [mul_apply_eq_comp, rightRegular_apply] using
    congrArg (fun v : GroupHilbert G => v x) hc.symm

theorem groupVN_star_coefficient {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) (x : G) :
    ((star T : GroupOperator G) deltaOne) x =
      conj (((T : GroupOperator G) deltaOne) x⁻¹) := by
  calc
    ((star T : GroupOperator G) deltaOne) x =
        inner ℂ (lp.single 2 x (1 : ℂ)) ((star T : GroupOperator G) deltaOne) := by
      simp only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
    _ = inner ℂ ((T : GroupOperator G) (lp.single 2 x 1)) deltaOne := by
      exact ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = conj (((T : GroupOperator G) (lp.single 2 x 1)) 1) := by
      simp only [deltaOne, lp.inner_single_right, RCLike.inner_apply, one_mul]
    _ = _ := by rw [groupVN_matrix]; simp

theorem canonicalTrace_star_mul_inner {G : Type uG} [Group G] [DecidableEq G]
    (T U : groupVonNeumann G) :
    canonicalTrace (star T * U) = inner ℂ
      ((T : GroupOperator G) deltaOne) ((U : GroupOperator G) deltaOne) := by
  classical
  rw [canonicalTrace_eq_inner, ← deltaOne_eq]
  change inner ℂ deltaOne (star (T : GroupOperator G) ((U : GroupOperator G) deltaOne)) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

theorem canonicalTrace_mul {G : Type uG} [Group G] [DecidableEq G]
    (T U : groupVonNeumann G) : canonicalTrace (T * U) = canonicalTrace (U * T) := by
  have he (T U : groupVonNeumann G) :
      canonicalTrace (T * U) = ∑' x : G,
        ((T : GroupOperator G) deltaOne) x⁻¹ * ((U : GroupOperator G) deltaOne) x := by
    rw [← star_star T, canonicalTrace_star_mul_inner]
    change (∑' x, inner ℂ (((star T : GroupOperator G) deltaOne) x)
      (((U : GroupOperator G) deltaOne) x)) = _
    apply tsum_congr
    intro x
    rw [groupVN_star_coefficient]
    simp [RCLike.inner_apply, mul_comm]
  rw [he, he]
  simpa only [Equiv.inv_apply, inv_inv, mul_comm] using
    ((Equiv.inv G).tsum_eq (fun x =>
      ((T : GroupOperator G) deltaOne) x⁻¹ * ((U : GroupOperator G) deltaOne) x)).symm

def hilbertSequenceMap {G : Type uG} {H : Type uH} (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (ξ : lp (fun _ : ℕ => GroupHilbert G) 2) :
    lp (fun _ : ℕ => GroupHilbert H) 2 :=
  ⟨fun n => e (ξ n), Memℓp.of_norm (by simpa only [e.norm_map] using (lp.memℓp ξ).norm)⟩

theorem spatial_ultraweak_continuous {G : Type uG} {H : Type uH}
    (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H) :
    @Continuous _ _ (ultraweakOperatorTopology G) (ultraweakOperatorTopology H)
      e.conjStarAlgEquiv := by
  apply continuous_iInf_rng.mpr
  intro ξ
  apply continuous_iInf_rng.mpr
  intro η
  apply continuous_induced_rng.mpr
  have heq :
      (fun T : GroupOperator G => ∑' k : ℕ, inner ℂ (η k) (e.conjStarAlgEquiv T (ξ k))) =
      (fun T : GroupOperator G => ∑' k : ℕ,
        inner ℂ (hilbertSequenceMap e.symm η k) (T (hilbertSequenceMap e.symm ξ k))) := by
    funext T
    apply tsum_congr
    intro k
    change inner ℂ (η k) (e (T (e.symm (ξ k)))) =
      inner ℂ (e.symm (η k)) (T (e.symm (ξ k)))
    rw [← e.inner_map_map]
    simp
  change @Continuous _ _ (ultraweakOperatorTopology G) _
    (fun T : GroupOperator G => ∑' k : ℕ, inner ℂ (η k) (e.conjStarAlgEquiv T (ξ k)))
  rw [heq]
  exact continuous_iInf_dom (i := hilbertSequenceMap e.symm ξ)
    (continuous_iInf_dom (i := hilbertSequenceMap e.symm η) continuous_induced_dom)

def spatialGroupIso {G : Type uG} {H : Type uH} [Group G] [Group H]
    (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (hVN : ∀ T : GroupOperator G,
      T ∈ groupVonNeumann G ↔ e.conjStarAlgEquiv T ∈ groupVonNeumann H) :
    groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann H where
  toFun T := ⟨e.conjStarAlgEquiv T, (hVN T).mp T.property⟩
  invFun T := ⟨e.conjStarAlgEquiv.symm T, (hVN _).mpr (by rw [e.conjStarAlgEquiv.apply_symm_apply]; exact T.property)⟩
  left_inv T := Subtype.ext (e.conjStarAlgEquiv.symm_apply_apply T)
  right_inv T := Subtype.ext (e.conjStarAlgEquiv.apply_symm_apply T)
  map_mul' T U := Subtype.ext (map_mul e.conjStarAlgEquiv (T : GroupOperator G) (U : GroupOperator G))
  map_add' T U := Subtype.ext (map_add e.conjStarAlgEquiv (T : GroupOperator G) (U : GroupOperator G))
  map_star' T := Subtype.ext (map_star e.conjStarAlgEquiv (T : GroupOperator G))
  map_smul' c T := Subtype.ext (map_smul e.conjStarAlgEquiv c (T : GroupOperator G))

theorem spatialGroupIso_normal {G : Type uG} {H : Type uH} [Group G] [Group H]
    (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (hVN : ∀ T : GroupOperator G,
      T ∈ groupVonNeumann G ↔ e.conjStarAlgEquiv T ∈ groupVonNeumann H) :
    @Continuous _ _ (groupUltraweakTopology G) (groupUltraweakTopology H)
      (spatialGroupIso e hVN) := by
  let : TopologicalSpace (GroupOperator G) := ultraweakOperatorTopology G
  let : TopologicalSpace (GroupOperator H) := ultraweakOperatorTopology H
  let : TopologicalSpace (groupVonNeumann G) := groupUltraweakTopology G
  let : TopologicalSpace (groupVonNeumann H) := groupUltraweakTopology H
  apply continuous_induced_rng.mpr
  have hinc : Continuous (fun T : groupVonNeumann G => (T : GroupOperator G)) :=
    continuous_induced_dom
  exact (spatial_ultraweak_continuous e).comp hinc

open scoped ComplexConjugate ENNReal

 theorem operator_matrix_ext {G : Type uG} [DecidableEq G] (T U : GroupOperator G)
    (h : ∀ g, T (lp.single 2 g 1) = U (lp.single 2 g 1)) : T = U := by
  classical
  apply ContinuousLinearMap.ext
  intro ξ
  have hT := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ).mapL T
  have hU := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ).mapL U
  have he (g : G) : T (lp.single 2 g (ξ g)) = U (lp.single 2 g (ξ g)) := by
    have hc : lp.single (E := fun _ : G => ℂ) 2 g (ξ g) =
        (ξ g) • lp.single (E := fun _ : G => ℂ) 2 g 1 := by
      ext b
      simp [lp.single_apply, Pi.single_apply]
    rw [hc, map_smul, map_smul, h]
  simp only [he] at hT
  exact hT.unique hU

 theorem operator_coeff_tsum {G : Type uG} [DecidableEq G] (T : GroupOperator G)
    (ξ : GroupHilbert G) (x : G) :
    (T ξ) x = ∑' y : G, (T (lp.single 2 y 1)) x * ξ y := by
  calc
    (T ξ) x = inner ℂ (lp.single 2 x 1) (T ξ) := by simp [lp.inner_single_left]
    _ = inner ℂ (star T (lp.single 2 x 1)) ξ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    _ = ∑' y : G, (T (lp.single 2 y 1)) x * ξ y := by
      rw [lp.inner_eq_tsum]
      apply tsum_congr
      intro y
      have he : conj ((star T (lp.single 2 x 1)) y) = (T (lp.single 2 y 1)) x := by
        calc
          _ = inner ℂ (star T (lp.single 2 x 1)) (lp.single 2 y 1) := by
            simp [lp.inner_single_right]
          _ = inner ℂ (lp.single 2 x 1) (T (lp.single 2 y 1)) := by
            rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
          _ = _ := by simp [lp.inner_single_left]
      simp only [RCLike.inner_apply, he, mul_comm]

 theorem matrix_of_commute_right {G : Type uG} [Group G] [DecidableEq G]
    (T : GroupOperator G) (hT : ∀ g, rightRegular g * T = T * rightRegular g)
    (x y : G) :
    (T (lp.single 2 y 1)) x = (T deltaOne) (x * y⁻¹) := by
  have hr : rightRegular y⁻¹ deltaOne = lp.single 2 y 1 := by
    ext b
    simp [deltaOne, lp.single_apply, Pi.single_apply, mul_inv_eq_one]
  rw [← hr]
  have hc := congrArg (fun f : GroupOperator G => f deltaOne) (hT y⁻¹)
  simpa only [mul_apply_eq_comp, rightRegular_apply] using
    congrArg (fun v : GroupHilbert G => v x) hc.symm

 theorem matrix_of_commute_left {G : Type uG} [Group G] [DecidableEq G]
    (T : GroupOperator G) (hT : ∀ g, leftRegular g * T = T * leftRegular g)
    (x y : G) :
    (T (lp.single 2 y 1)) x = (T deltaOne) (y⁻¹ * x) := by
  have hl : leftRegular y deltaOne = lp.single 2 y 1 := by
    ext b
    simp [deltaOne, lp.single_apply, Pi.single_apply, inv_mul_eq_one, eq_comm]
  rw [← hl]
  have hc := congrArg (fun f : GroupOperator G => f deltaOne) (hT y)
  simpa only [mul_apply_eq_comp, leftRegular_apply] using
    congrArg (fun v : GroupHilbert G => v x) hc.symm

 theorem mem_groupVN_iff_commute_right {G : Type uG} [Group G]
    (T : GroupOperator G) : T ∈ groupVonNeumann G ↔
      ∀ g, rightRegular g * T = T * rightRegular g := by
  classical
  refine ⟨fun h g => groupVN_commute_right ⟨T,h⟩ g, ?_⟩
  intro hT
  have hc (U : GroupOperator G) (hU : ∀ g, leftRegular g * U = U * leftRegular g) :
      U * T = T * U := by
    apply operator_matrix_ext
    intro k
    ext x
    have hleft : ((U * T) (lp.single 2 k 1)) x =
        ∑' y : G, (U deltaOne) (y⁻¹ * x) * (T deltaOne) (y * k⁻¹) := by
      change (U (T (lp.single 2 k 1))) x = _
      rw [operator_coeff_tsum U]
      apply tsum_congr
      intro y
      rw [matrix_of_commute_left U hU x y, matrix_of_commute_right T hT y k]
    have hright : ((T * U) (lp.single 2 k 1)) x =
        ∑' y : G, (T deltaOne) (x * y⁻¹) * (U deltaOne) (k⁻¹ * y) := by
      change (T (U (lp.single 2 k 1))) x = _
      rw [operator_coeff_tsum T]
      apply tsum_congr
      intro y
      rw [matrix_of_commute_right T hT x y, matrix_of_commute_left U hU y k]
    rw [hleft, hright]
    let e : G ≃ G := ((Equiv.inv G).trans (Equiv.mulLeft x)).trans (Equiv.mulRight k)
    have hs := e.tsum_eq (fun y => (U deltaOne) (y⁻¹ * x) * (T deltaOne) (y * k⁻¹))
    change (∑' c : G, (U deltaOne) ((x * c⁻¹ * k)⁻¹ * x) *
      (T deltaOne) (x * c⁻¹ * k * k⁻¹)) = _ at hs
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel,
      mul_inv_cancel, mul_one, mul_comm] using hs.symm
  rw [groupVonNeumann, StarSubalgebra.mem_centralizer_iff]
  intro U hU
  have hu : ∀ g, leftRegular g * U = U * leftRegular g := by
    intro g
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp hU _
      (leftRegular_mem_leftTranslations g)).1
  refine ⟨hc U hu, hc (star U) ?_⟩
  intro g
  have hh := congrArg star (hu g⁻¹)
  simpa only [star_mul, leftRegular_star, inv_inv] using hh.symm

open scoped ComplexConjugate

 theorem rightRegular_single {G : Type uG} [Group G] [DecidableEq G] (g y : G) :
    rightRegular g (lp.single 2 y (1 : ℂ)) = lp.single 2 (y * g⁻¹) 1 := by
  ext x
  simp only [rightRegular_apply, lp.single_apply, Pi.single_apply]
  congr 1
  exact propext (eq_mul_inv_iff_mul_eq.symm)

 theorem mem_groupVN_of_matrix_invariant {G : Type uG} [Group G] [DecidableEq G]
    (T : GroupOperator G)
    (hT : ∀ x y g : G, (T (lp.single 2 (y*g) 1)) (x*g) =
      (T (lp.single 2 y 1)) x) : T ∈ groupVonNeumann G := by
  rw [mem_groupVN_iff_commute_right]
  intro g
  apply operator_matrix_ext
  intro y
  ext x
  simp only [mul_apply_eq_comp, rightRegular_apply]
  change (T (lp.single 2 y 1)) (x*g) = (T (rightRegular g (lp.single 2 y 1))) x
  rw [rightRegular_single]
  simpa only [mul_inv_cancel_right] using (hT (x*g) y g⁻¹).symm

 theorem haar_orbit_orthonormal {G : Type uG} {H : Type uH} [Group G] [Group H] [DecidableEq G]
    (ρ : G →* groupVonNeumann H)
    (hstar : ∀ g, star (ρ g) = ρ g⁻¹)
    (htrace : ∀ g, canonicalTrace (ρ g) = if g = 1 then 1 else 0) :
    Orthonormal ℂ (fun g => ((ρ g : groupVonNeumann H) : GroupOperator H) deltaOne) := by
  classical
  rw [orthonormal_iff_ite]
  intro x y
  rw [← canonicalTrace_star_mul_inner, hstar, ← map_mul, htrace]
  simp only [inv_mul_eq_one]

 theorem spatial_of_haar_total {G : Type uG} {H : Type uH} [Group G] [Group H] [DecidableEq G]
    (ρ : G →* groupVonNeumann H)
    (hstar : ∀ g, star (ρ g) = ρ g⁻¹)
    (htrace : ∀ g, canonicalTrace (ρ g) = if g = 1 then 1 else 0)
    (htotal : ⊤ ≤ (Submodule.span ℂ (Set.range
      (fun g => ((ρ g : groupVonNeumann H) : GroupOperator H) deltaOne))).topologicalClosure) :
    ∃ e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H,
      e deltaOne = deltaOne ∧
      (∀ g, e.conjStarAlgEquiv (leftRegular g) = (ρ g : GroupOperator H)) ∧
      ∀ T : GroupOperator G, T ∈ groupVonNeumann G ↔
        e.conjStarAlgEquiv T ∈ groupVonNeumann H := by
  classical
  let v : G → GroupHilbert H := fun g => ((ρ g : groupVonNeumann H) : GroupOperator H) deltaOne
  have hon : Orthonormal ℂ v := haar_orbit_orthonormal ρ hstar htrace
  let e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H :=
    (hon.isHilbertSum htotal).linearIsometryEquiv.symm
  have he (g : G) : e (lp.single 2 g 1) = v g :=
    hon.linearIsometryEquiv_symm_apply_single_one htotal g
  have hδ : e deltaOne = deltaOne := by
    rw [deltaOne_eq, he]
    simp [v]
  have hleft (g : G) : e.conjStarAlgEquiv (leftRegular g) = (ρ g : GroupOperator H) := by
    apply e.conjStarAlgEquiv.symm.injective
    change e.conjStarAlgEquiv.symm (e.conjStarAlgEquiv (leftRegular g)) =
      e.conjStarAlgEquiv.symm (ρ g : GroupOperator H)
    rw [e.conjStarAlgEquiv.symm_apply_apply]
    apply operator_matrix_ext
    intro y
    apply e.injective
    change e (leftRegular g (lp.single 2 y 1)) =
      e (e.symm ((ρ g : GroupOperator H) (e (lp.single 2 y 1))))
    rw [e.apply_symm_apply, he]
    have hl : leftRegular g (lp.single 2 y (1 : ℂ)) = lp.single 2 (g*y) 1 := by
      ext x
      simp only [leftRegular_apply, lp.single_apply, Pi.single_apply]
      congr 1
      exact propext (inv_mul_eq_iff_eq_mul)
    rw [hl, he]
    change ((ρ (g*y) : groupVonNeumann H) : GroupOperator H) deltaOne = _
    rw [map_mul]
    rfl
  refine ⟨e, hδ, hleft, ?_⟩
  intro T
  constructor
  · intro hT
    rw [mem_groupVN_iff_commute_right]
    intro g
    apply e.conjStarAlgEquiv.symm.injective
    change e.conjStarAlgEquiv.symm (rightRegular g * e.conjStarAlgEquiv T) =
      e.conjStarAlgEquiv.symm (e.conjStarAlgEquiv T * rightRegular g)
    rw [map_mul, map_mul, e.conjStarAlgEquiv.symm_apply_apply]
    have hc : e.conjStarAlgEquiv.symm (rightRegular g) ∈
        StarSubalgebra.centralizer ℂ (leftTranslations G) := by
      rw [StarSubalgebra.mem_centralizer_iff, leftTranslations_eq_range]
      rintro _ ⟨x,rfl⟩
      constructor
      · apply e.conjStarAlgEquiv.injective
        change e.conjStarAlgEquiv (leftRegular _ * e.conjStarAlgEquiv.symm (rightRegular g)) =
          e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm (rightRegular g) * leftRegular _)
        rw [map_mul, map_mul, e.conjStarAlgEquiv.apply_symm_apply, hleft]
        exact (groupVN_commute_right (ρ x) g).symm
      · rw [leftRegular_star]
        apply e.conjStarAlgEquiv.injective
        change e.conjStarAlgEquiv (leftRegular _ * e.conjStarAlgEquiv.symm (rightRegular g)) =
          e.conjStarAlgEquiv (e.conjStarAlgEquiv.symm (rightRegular g) * leftRegular _)
        rw [map_mul, map_mul, e.conjStarAlgEquiv.apply_symm_apply, hleft]
        exact (groupVN_commute_right (ρ x⁻¹) g).symm
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp hT _ hc).1
  · intro hT
    let U : groupVonNeumann H := ⟨e.conjStarAlgEquiv T, hT⟩
    have hm (x y : G) : (T (lp.single 2 y 1)) x =
        canonicalTrace (star (ρ x) * U * ρ y) := by
      calc
        (T (lp.single 2 y 1)) x = inner ℂ (lp.single 2 x 1) (T (lp.single 2 y 1)) := by
          simp [lp.inner_single_left]
        _ = inner ℂ (v x) ((U : GroupOperator H) (v y)) := by
          rw [← he x, ← he y, ← e.inner_map_map]
          change inner ℂ (e (lp.single 2 x 1)) (e (T (lp.single 2 y 1))) =
            inner ℂ (e (lp.single 2 x 1)) (e (T (e.symm (e (lp.single 2 y 1)))))
          rw [e.symm_apply_apply]
        _ = canonicalTrace (star (ρ x) * U * ρ y) := by
          rw [mul_assoc, canonicalTrace_star_mul_inner]
          rfl
    apply mem_groupVN_of_matrix_invariant T
    intro x y g
    rw [hm, hm, map_mul, map_mul, star_mul]
    have hc := canonicalTrace_mul (star (ρ g) * star (ρ x) * U * ρ y) (ρ g)
    simp only [← mul_assoc]
    rw [hc]
    simp only [hstar, ← mul_assoc, ← map_mul, mul_inv_cancel, one_mul]

 theorem iso_extension_of_haar_total {G : Type uG} {H : Type uH} [Group G] [Group H] [DecidableEq G]
    (ρ : G →* groupVonNeumann H)
    (hstar : ∀ g, star (ρ g) = ρ g⁻¹)
    (htrace : ∀ g, canonicalTrace (ρ g) = if g = 1 then 1 else 0)
    (htotal : ⊤ ≤ (Submodule.span ℂ (Set.range
      (fun g => ((ρ g : groupVonNeumann H) : GroupOperator H) deltaOne))).topologicalClosure) :
    ∃ Φ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann H,
      (∀ T, canonicalTrace (Φ T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology G) (groupUltraweakTopology H) Φ ∧
      ∀ g, Φ (groupUnitary g) = ρ g := by
  classical
  obtain ⟨e,hδ,hρ,hVN⟩ := spatial_of_haar_total ρ hstar htrace htotal
  refine ⟨spatialGroupIso e hVN, ?_, spatialGroupIso_normal e hVN, ?_⟩
  · intro T
    rw [canonicalTrace_eq_inner, canonicalTrace_eq_inner, ← deltaOne_eq, ← deltaOne_eq]
    change inner ℂ deltaOne (e ((T : GroupOperator G) (e.symm deltaOne))) =
      inner ℂ deltaOne ((T : GroupOperator G) deltaOne)
    rw [← hδ, e.symm_apply_apply, e.inner_map_map]
  · intro g
    apply Subtype.ext
    exact hρ g

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uA uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

section
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def reducingAlgebra (K : Submodule ℂ H) : StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {T | (∀ x ∈ K, T x ∈ K) ∧ ∀ x ∈ K, (star T) x ∈ K}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    rintro T U ⟨hT,hT'⟩ ⟨hU,hU'⟩
    constructor
    · intro x hx; exact K.add_mem (hT x hx) (hU x hx)
    · intro x hx; simpa using K.add_mem (hT' x hx) (hU' x hx)
  mul_mem' := by
    rintro T U ⟨hT,hT'⟩ ⟨hU,hU'⟩
    constructor
    · intro x hx; exact hT _ (hU x hx)
    · intro x hx; simpa using hU' _ (hT' x hx)
  algebraMap_mem' := by
    intro c
    constructor
    · intro x hx; simpa using K.smul_mem c hx
    · intro x hx; simpa only [← algebraMap_star_comm, ContinuousLinearMap.algebraMap_apply] using K.smul_mem (star c) hx
  star_mem' := by
    rintro T ⟨hT,hT'⟩
    exact ⟨hT', by simpa using hT⟩

theorem reducingAlgebra_isClosed (K : Submodule ℂ H) (hK : IsClosed (K : Set H)) :
    IsClosed (reducingAlgebra K : Set (H →L[ℂ] H)) := by
  change IsClosed {T : H →L[ℂ] H | _ ∧ _}
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _hx
    exact hK.preimage (ContinuousLinearMap.apply ℂ H x).continuous
  · apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _hx
    exact hK.preimage ((ContinuousLinearMap.apply ℂ H x).continuous.comp continuous_star)

omit [CompleteSpace H] in

theorem closedSpan_invariant {G : Type uG} [Group G]
    (ρ : G →* (H →L[ℂ] H)) (ξ : H) (g : G) :
    ∀ x ∈ (Submodule.span ℂ (Set.range (fun a => ρ a ξ))).topologicalClosure,
      ρ g x ∈ (Submodule.span ℂ (Set.range (fun a => ρ a ξ))).topologicalClosure := by
  let K := (Submodule.span ℂ (Set.range (fun a => ρ a ξ))).topologicalClosure
  change K ≤ K.comap (ρ g).toLinearMap
  apply Submodule.topologicalClosure_minimal
  · rw [Submodule.span_le]
    rintro _ ⟨a,rfl⟩
    change ρ g (ρ a ξ) ∈ K
    have he : ρ g (ρ a ξ) = ρ (g*a) ξ := by rw [map_mul]; rfl
    rw [he]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g*a, rfl⟩)
  · exact (Submodule.isClosed_topologicalClosure _).preimage (ρ g).continuous

end

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}
 theorem wordHom_mem (E : StarSubalgebra ℂ A) (U : ι → unitary A)
    (hU : ∀ i, (U i : A) ∈ E) (g : FreeGroup ι) : wordHom U g ∈ E := by
  induction g using FreeGroup.induction_on with
  | C1 => rw [map_one]; exact one_mem E
  | of i => simpa only [wordHom_of] using hU i
  | inv_of i hi => rw [wordHom_inv]; exact star_mem hi
  | mul x y hx hy => rw [map_mul]; exact mul_mem hx hy

 theorem laurentValue_mem (E : StarSubalgebra ℂ A) (C : unitary A)
    (hC : (C : A) ∈ E) (l : ℤ →₀ ℂ) : laurentValue C l ∈ E := by
  have hp (k : ℤ) : ((C ^ k : unitary A) : A) ∈ E := by
    cases k with
    | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast]
      exact pow_mem hC n
    | negSucc n =>
      rw [zpow_negSucc]
      change star ((C : A) ^ (n+1)) ∈ E
      exact star_mem (pow_mem hC (n+1))
  classical
  change (∑ k ∈ l.support, l k • ((C ^ k : unitary A) : A)) ∈ E
  exact sum_mem fun k _ => E.smul_mem (hp k) _
end UnitaryEvaluation

open UnitaryEvaluation
open scoped ENNReal

open UnitaryEvaluation

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

noncomputable section

universe uA uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

open scoped ContDiff BigOperators ENNReal
namespace FreeGroupFactorMain

end FreeGroupFactorMain
namespace FreeGroupFactorMain.UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain
open scoped ContDiff
open UnitaryEvaluation

end FreeGroupFactorMain

namespace FreeGroupFactorMain.UnitaryEvaluation
open scoped ContDiff
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} {κ : Type uκ}

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain.FiniteActive
open UnitaryEvaluation
open scoped ContDiff
variable {ι : Type uι} {κ : Type uκ}

end FreeGroupFactorMain.FiniteActive

namespace FreeGroupFactorMain
open UnitaryEvaluation
open scoped ENNReal
 theorem canonical_total_of_reducing {ι : Type uι}
    (K : Submodule ℂ (GroupHilbert (FreeGroup ι)))
    (hK : IsClosed (K : Set (GroupHilbert (FreeGroup ι)))) (hδ : deltaOne ∈ K)
    (hgen : ∀ i : ι, (generatorUnitary i : groupVonNeumann (FreeGroup ι)) ∈
      (reducingAlgebra K).comap (groupVonNeumann (FreeGroup ι)).subtype) : ⊤ ≤ K := by
  classical
  let E := (reducingAlgebra K).comap (groupVonNeumann (FreeGroup ι)).subtype
  have hgroup (g : FreeGroup ι) : groupUnitary g ∈ E := by
    rw [← wordHom_generatorUnitary]
    exact wordHom_mem E generatorUnitary hgen g
  have hsingle (g : FreeGroup ι) : lp.single 2 g (1 : ℂ) ∈ K := by
    have hh := (hgroup g).1 deltaOne hδ
    have he : (leftRegular g) deltaOne = lp.single 2 g 1 := by
      ext x
      simp [deltaOne, lp.single_apply, Pi.single_apply, inv_mul_eq_one, eq_comm]
    change (leftRegular g) deltaOne ∈ K at hh
    rwa [he] at hh
  intro ξ _hξ
  have hs := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ
  apply hK.mem_of_tendsto hs
  filter_upwards [] with s
  apply K.sum_mem
  intro g _hg
  have he : lp.single 2 g (ξ g) = (ξ g) • (lp.single 2 g (1 : ℂ) : GroupHilbert (FreeGroup ι)) := by
    ext x
    simp [lp.single_apply, Pi.single_apply]
  rw [he]
  exact K.smul_mem _ (hsingle g)

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

namespace FreeGroupFactorMain.FiniteActive

section
open UnitaryEvaluation
open scoped ENNReal
 theorem original_generators_mem {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (X : ℝ → ι → Ambient ι κ) (hU : ∀ t i, X t i ∈ unitary (Ambient ι κ))
    (hX₀ : X 0 = fun i => groupUnitary (FreeGroup.of (some (Sum.inl i))))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t)
    (E : StarSubalgebra ℂ (Ambient ι κ)) (hE : IsClosed (E : Set (Ambient ι κ)))
    (hC : (generatorUnitary (none : Option (ι ⊕ κ)) : Ambient ι κ) ∈ E)
    (t₀ : ℝ) (hXt : ∀ i, X t₀ i ∈ E)
    (hpass : ∀ k : κ, (generatorUnitary (some (Sum.inr k) : Option (ι ⊕ κ)) : Ambient ι κ) ∈ E) :
    ∀ i : Option (ι ⊕ κ), (generatorUnitary i : Ambient ι κ) ∈ E := by
  have hXS := PolynomialFlow.solution_mem_subalgebra E hE
    (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) hS
    (laurentValue_mem E _ hC l) h X hX hU t₀ hXt
  intro i
  cases i with
  | none => exact hC
  | some j =>
    cases j with
    | inl i =>
      change groupUnitary (FreeGroup.of (some (Sum.inl i))) ∈ E
      simpa only [hX₀] using hXS 0 i
    | inr k => exact hpass k

 theorem orbit_total {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (X : ℝ → ι → groupVonNeumann (FreeGroup (Option (ι ⊕ κ))))
    (hU : ∀ t j, X t j ∈ unitary (groupVonNeumann (FreeGroup (Option (ι ⊕ κ)))))
    (hX₀ : X 0 = fun j => groupUnitary (FreeGroup.of (some (Sum.inl j))))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t) (t₀ : ℝ) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (fun g : FreeGroup (Option (ι ⊕ κ)) =>
      ((wordHom (extendUnitary (fun j => ⟨tuple (X t₀) j,tuple_unitary (X t₀) (hU t₀) j⟩)
        (generatorUnitary none)) g : groupVonNeumann (FreeGroup (Option (ι ⊕ κ)))) :
          GroupOperator (FreeGroup (Option (ι ⊕ κ)))) deltaOne))).topologicalClosure := by
  classical
  let U := extendUnitary (fun j => ⟨tuple (X t₀) j,tuple_unitary (X t₀) (hU t₀) j⟩) (generatorUnitary none)
  let ρ : FreeGroup (Option (ι ⊕ κ)) →* GroupOperator (FreeGroup (Option (ι ⊕ κ))) :=
    (groupVonNeumann _).subtype.toMonoidHom.comp (wordHom U)
  let K := (Submodule.span ℂ (Set.range (fun g => ρ g deltaOne))).topologicalClosure
  let E := (reducingAlgebra K).comap (groupVonNeumann _).subtype
  have hK : IsClosed (K : Set (GroupHilbert (FreeGroup (Option (ι ⊕ κ))))) :=
    Submodule.isClosed_topologicalClosure _
  have hE : IsClosed (E : Set (groupVonNeumann (FreeGroup (Option (ι ⊕ κ))))) :=
    (reducingAlgebra_isClosed K hK).preimage continuous_subtype_val
  have hρ (g) : wordHom U g ∈ E := by
    constructor
    · exact closedSpan_invariant ρ deltaOne g
    · have he : star (ρ g) = ρ g⁻¹ := by
        change ((star (wordHom U g) : groupVonNeumann (FreeGroup (Option (ι ⊕ κ)))) :
          GroupOperator (FreeGroup (Option (ι ⊕ κ)))) = _
        rw [← wordHom_inv]
        rfl
      change ∀ x ∈ K, (star (ρ g)) x ∈ K
      rw [he]
      exact closedSpan_invariant ρ deltaOne g⁻¹
  have hC : (generatorUnitary (none : Option (ι ⊕ κ)) : groupVonNeumann _) ∈ E := by
    simpa only [wordHom_of, U, extendUnitary, Option.elim_none] using hρ (FreeGroup.of none)
  have hXt : ∀ j, X t₀ j ∈ E := by
    intro j
    simpa only [wordHom_of, U, extendUnitary, Option.elim_some,tuple,Sum.elim_inl] using hρ (FreeGroup.of (some (Sum.inl j)))
  have hpass (k : κ) : (generatorUnitary (some (Sum.inr k) : Option (ι ⊕ κ)) : Ambient ι κ) ∈ E := by
    change groupUnitary (FreeGroup.of (some (Sum.inr k))) ∈ E
    simpa only [wordHom_of,U,extendUnitary,Option.elim_some,tuple,Sum.elim_inr]
      using hρ (FreeGroup.of (some (Sum.inr k)))
  have hgen := original_generators_mem h l hS X hU hX₀ hX E hE hC t₀ hXt hpass
  change ⊤ ≤ K
  apply canonical_total_of_reducing K hK _ hgen
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

end
open UnitaryEvaluation

theorem extension_at_time {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (X : ℝ → ι → Ambient ι κ) (hU : ∀ t i, X t i ∈ unitary (Ambient ι κ))
    (hX₀ : X 0 = fun i => groupUnitary (FreeGroup.of (some (Sum.inl i))))
    (hX : ∀ t, HasDerivAt X (PolynomialFlow.field
      (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) h (X t)) t) (t : ℝ) :
    ∃ Φ : Ambient ι κ ≃⋆ₐ[ℂ] Ambient ι κ,
        (∀ T, canonicalTrace (Φ T) = canonicalTrace T) ∧
        @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ))))
          (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ)))) Φ ∧
        ∀ g, Φ (groupUnitary g) = wordHom
          (extendUnitary (fun j => ⟨tuple (X t) j,tuple_unitary (X t) (hU t) j⟩)
            (generatorUnitary none)) g := by
  exact iso_extension_of_haar_total
    (wordHom (extendUnitary (fun j => ⟨tuple (X t) j,tuple_unitary (X t) (hU t) j⟩)
      (generatorUnitary none)))
    (fun g => (wordHom_inv _ g).symm)
    (moments h l hS X hU hX₀ hX t)
    (orbit_total h l hS X hU hX₀ hX t)

end FreeGroupFactorMain.FiniteActive

namespace FreeGroupFactorMain.UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} {κ : Type uκ}

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain.FiniteActive

section
open UnitaryEvaluation
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

end

open UnitaryEvaluation

end FreeGroupFactorMain.FiniteActive

end

end OAI
end

theorem solution.{v_1,v_2} : type_of% @OAI.FreeGroupFactorMain.FiniteActive.extension_at_time.{v_1,v_2} := @OAI.FreeGroupFactorMain.FiniteActive.extension_at_time.{v_1,v_2}
