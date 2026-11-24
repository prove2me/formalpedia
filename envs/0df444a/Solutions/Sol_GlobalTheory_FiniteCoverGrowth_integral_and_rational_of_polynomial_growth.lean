-- Prove2me | solution 1 for GlobalTheory.FiniteCoverGrowth.integral_and_rational_of_polynomial_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:03:14.098002+00:00
-- url     : https://prove2.me/submissions/4394e771-4071-43a9-a337-c07583371454

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IntegralAndRationalOfPolynomialGrowth
import Theorems.Thm_GlobalTheory_FiniteCoverGrowth_exists_norm_root_le
import Theorems.Thm_GlobalTheory_FiniteCoverGrowth_exists_map_eq_of_eval
import Theorems.Thm_GlobalTheory_FiniteCoverGrowth_separable_map
import Theorems.Thm_GlobalTheory_FiniteCoverGrowth_eq_nodal
import Theorems.Thm_GlobalTheory_FiniteCoverGrowth_card_roots
import Theorems.Thm_GlobalTheory_FiniteCoverGrowth_exists_local_roots
import Theorems.Thm_GlobalTheory_FiniteCoverGrowth_norm_prod_le_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.FiniteCoverGrowth
namespace GlobalTheory.FiniteCoverGrowth
theorem _root_.solution :
    (∀ (d : ℕ) (q : MvPolynomial (Fin d) ℂ), q ≠ 0 → IsConnected {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} ∧ Dense {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0}) → (∀ (d m : ℕ) (q : MvPolynomial (Fin d) ℂ) (f : (Fin d → ℂ) → ℂ) (C : ℝ), q ≠ 0 → DifferentiableOn ℂ f {x | MvPolynomial.eval x q ≠ 0} → (∀ x, MvPolynomial.eval x q ≠ 0 → ‖f x‖ ≤ C * (1 + ‖x‖) ^ m) → ∃ p : MvPolynomial (Fin d) ℂ, ∀ x, MvPolynomial.eval x q ≠ 0 → f x = MvPolynomial.eval x p) → (∀ (d m : ℕ) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ) (φ : (Fin d → ℂ) × ℂ → ℂ) (C : ℝ), p.Monic → q ≠ 0 → Polynomial.C q ∈ Ideal.span {p, p.derivative} → (∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, ∃ F : (Fin d → ℂ) × ℂ → ℂ, AnalyticAt ℂ F z ∧ ∀ᶠ w in 𝓝[{z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}] z, φ w = F w) → (∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, ‖φ z‖ ≤ C * (1 + ‖z.1‖) ^ m) → (∃ s : Polynomial (MvPolynomial (Fin d) ℂ), s.Monic ∧ ∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, (s.map (MvPolynomial.eval z.1)).eval (φ z) = 0) ∧ ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), ∀ z ∈ {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}, (p.derivative.map (MvPolynomial.eval z.1)).eval z.2 * φ z = (r.map (MvPolynomial.eval z.1)).eval z.2) := by
  classical
  intro _ hpoly d m p q φ C hp hq0 hq hφ hb
  set U : Set (Fin d → ℂ) := {x | MvPolynomial.eval x q ≠ 0} with hU
  set Z : Set ((Fin d → ℂ) × ℂ) := {z | MvPolynomial.eval z.1 q ≠ 0 ∧
    (p.map (MvPolynomial.eval z.1)).eval z.2 = 0} with hZ
  set n := p.natDegree with hn
  let T : (Fin d → ℂ) → Finset ℂ := fun x => (p.map (MvPolynomial.eval x)).roots.toFinset
  have hT : ∀ x y, y ∈ T x ↔ (p.map (MvPolynomial.eval x)).eval y = 0 := fun x y => by
    simp only [T, Multiset.mem_toFinset]
    exact Polynomial.mem_roots (hp.map _).ne_zero
  have hsep : ∀ x ∈ U, (p.map (MvPolynomial.eval x)).Separable :=
    fun x hx => separable_map p q hq x hx
  have hcard : ∀ x ∈ U, (T x).card = n := fun x hx => by
    rw [hn, ← hp.natDegree_map (MvPolynomial.eval x)]
    exact card_roots (hp.map _) (hsep x hx)
  have hUo : IsOpen U := isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const

  have hloc : ∀ x₀ ∈ U, ∃ y ψ : Fin n → (Fin d → ℂ) → ℂ, (∀ i, DifferentiableAt ℂ (y i) x₀) ∧
      (∀ i, DifferentiableAt ℂ (ψ i) x₀) ∧
      ∀ᶠ x in 𝓝 x₀, Function.Injective (fun i => y i x) ∧
        T x = Finset.univ.image (fun i => y i x) ∧ ∀ i, φ (x, y i x) = ψ i x := by
    intro x₀ hx₀
    obtain ⟨y, hyd, hy⟩ := exists_local_roots p hp x₀ (hsep x₀ hx₀)
    have hmem : ∀ᶠ x in 𝓝 x₀, ∀ i, (x, y i x) ∈ Z := by
      filter_upwards [hy, hUo.mem_nhds hx₀] with x h1 h2 i
      refine ⟨h2, (hT x _).1 ?_⟩
      change _ ∈ (p.map (MvPolynomial.eval x)).roots.toFinset
      rw [h1.2]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    choose F hF hF' using fun i => hφ _ (hmem.self_of_nhds i)
    refine ⟨y, fun i x => F i (x, y i x), hyd, fun i => ?_, ?_⟩
    · exact (hF i).differentiableAt.comp x₀ (differentiableAt_id.prodMk (hyd i))
    · have : ∀ i, ∀ᶠ x in 𝓝 x₀, φ (x, y i x) = F i (x, y i x) := fun i => by
        have ht : Tendsto (fun x => (x, y i x)) (𝓝 x₀) (𝓝[Z] (x₀, y i x₀)) :=
          tendsto_nhdsWithin_iff.2 ⟨(continuousAt_id.prodMk (hyd i).continuousAt).tendsto,
            hmem.mono fun x h => h i⟩
        exact ht.eventually (hF' i)
      filter_upwards [hy, eventually_all.2 this] with x h1 h2
      exact ⟨h1.1, h1.2, h2⟩

  have hgrow : ∀ t : ℂ, ∃ (K : ℝ) (M : ℕ), ∀ x ∈ U, 1 ≤ K * (1 + ‖x‖) ^ M ∧ ∀ y ∈ T x,
      ‖φ (x, y)‖ ≤ K * (1 + ‖x‖) ^ M ∧ ‖t - φ (x, y)‖ ≤ K * (1 + ‖x‖) ^ M ∧
        ‖t - y‖ ≤ K * (1 + ‖x‖) ^ M := by
    intro t
    obtain ⟨K, M, hK, h⟩ := exists_norm_root_le p hp
    refine ⟨1 + ‖t‖ + |C| + K, m + M, fun x hx => ?_⟩
    have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have h2 : (1 + ‖x‖) ^ m ≤ (1 + ‖x‖) ^ (m + M) := pow_le_pow_right₀ h1 (by omega)
    have h3 : (1 + ‖x‖) ^ M ≤ (1 + ‖x‖) ^ (m + M) := pow_le_pow_right₀ h1 (by omega)
    have h4 : 1 ≤ (1 + ‖x‖) ^ (m + M) := one_le_pow₀ h1
    have h5 : ‖t‖ ≤ ‖t‖ * (1 + ‖x‖) ^ (m + M) := le_mul_of_one_le_right (norm_nonneg _) h4
    have h6 : 0 ≤ |C| * (1 + ‖x‖) ^ (m + M) := by positivity
    have h7 : 0 ≤ K * (1 + ‖x‖) ^ (m + M) := by positivity
    have h8 := norm_nonneg t
    simp only [add_mul, one_mul]
    refine ⟨by linarith, fun y hy => ?_⟩
    have h9 : ‖φ (x, y)‖ ≤ |C| * (1 + ‖x‖) ^ (m + M) :=
      (hb (x, y) ⟨hx, (hT x y).1 hy⟩).trans
        (mul_le_mul (le_abs_self C) h2 (by positivity) (abs_nonneg C))
    have h10 : ‖y‖ ≤ K * (1 + ‖x‖) ^ (m + M) :=
      (h x y ((hT x y).1 hy)).trans (mul_le_mul_of_nonneg_left h3 hK)
    refine ⟨by linarith, ?_, ?_⟩
    · linarith [norm_sub_le t (φ (x, y))]
    · linarith [norm_sub_le t y]
  constructor
  · refine Exists.elim (exists_map_eq_of_eval (N := n) U
      (fun x => Lagrange.nodal (T x) (fun y => φ (x, y)) - Polynomial.X ^ n) ?_ ?_) ?_
    rotate_right
    · rintro s ⟨hs, hs'⟩
      refine ⟨Polynomial.X ^ n + s, Polynomial.monic_X_pow_add hs, fun z hz => ?_⟩
      rw [Polynomial.map_add, hs' z.1 hz.1, Polynomial.map_pow, Polynomial.map_X, add_sub_cancel]
      exact Lagrange.eval_nodal_at_node (v := fun y => φ (z.1, y)) ((hT _ _).2 hz.2)
    · intro x hx
      have h1 : (Lagrange.nodal (T x) (fun y => φ (x, y))).degree = n := by
        rw [Lagrange.degree_nodal, hcard x hx]
      rw [← h1]
      refine Polynomial.degree_sub_lt (by rw [h1, Polynomial.degree_X_pow])
        Lagrange.nodal_monic.ne_zero ?_
      rw [Lagrange.nodal_monic.leadingCoeff, (Polynomial.monic_X_pow n).leadingCoeff]
    · intro t
      obtain ⟨K, M, hK⟩ := hgrow t
      refine Exists.elim (hpoly d (M * n) q (fun x => ∏ y ∈ T x, (t - φ (x, y))) (K ^ n) hq0 ?_ ?_) ?_
      rotate_right
      · rintro g hg
        refine ⟨g - MvPolynomial.C (t ^ n), fun x hx => ?_⟩
        simp [Lagrange.eval_nodal, ← hg x hx]
      · intro x₀ hx₀
        obtain ⟨y, ψ, hy, hψ, h⟩ := hloc x₀ hx₀
        have : DifferentiableAt ℂ (fun x => ∏ i, (t - ψ i x)) x₀ := by fun_prop
        refine (this.congr_of_eventuallyEq ?_).differentiableWithinAt
        filter_upwards [h] with x hx
        rw [hx.2.1, Finset.prod_image fun i _ j _ h => hx.1 h]
        simp only [hx.2.2]
      · intro x hx
        rw [pow_mul, ← mul_pow]
        exact norm_prod_le_pow _ _ _ _ (hK x hx).1 (hcard x hx).le
          fun y hy => ((hK x hx).2 y hy).2.1
  · refine Exists.elim (exists_map_eq_of_eval (N := n + 1) U
      (fun x => ∑ y ∈ T x, Polynomial.C (φ (x, y)) * Lagrange.nodal ((T x).erase y) id) ?_ ?_) ?_
    rotate_right
    · rintro r ⟨-, hr⟩
      refine ⟨r, fun z hz => ?_⟩
      have hz' : z.2 ∈ T z.1 := (hT _ _).2 hz.2
      rw [hr z.1 hz.1, ← Polynomial.derivative_map, eq_nodal (hp.map _) (hsep z.1 hz.1),
        Polynomial.eval_finset_sum, Finset.sum_eq_single z.2]
      · rw [Polynomial.eval_mul, Polynomial.eval_C, mul_comm]
        congr 1
        exact Lagrange.eval_nodal_derivative_eval_node_eq (v := id) hz'
      · intro y _ hy
        rw [Polynomial.eval_mul]
        exact mul_eq_zero_of_right _ (Lagrange.eval_nodal_at_node (v := id)
          (Finset.mem_erase.2 ⟨hy.symm, hz'⟩))
      · exact fun h => absurd hz' h
    · intro x hx
      refine (Polynomial.degree_sum_le _ _).trans_lt ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro y hy
      rw [← Polynomial.smul_eq_C_mul]
      refine (Polynomial.degree_smul_le _ _).trans_lt ?_
      rw [Lagrange.degree_nodal]
      have : ((T x).erase y).card < n + 1 :=
        Nat.lt_succ_of_le (Finset.card_erase_le.trans (hcard x hx).le)
      exact_mod_cast this
    · intro t
      obtain ⟨K, M, hK⟩ := hgrow t
      refine Exists.elim (hpoly d (M * (n + 1)) q
        (fun x => ∑ y ∈ T x, φ (x, y) * ∏ y' ∈ (T x).erase y, (t - y')) (n * K ^ (n + 1)) hq0 ?_ ?_) ?_
      rotate_right
      · rintro g hg
        refine ⟨g, fun x hx => ?_⟩
        simp [Lagrange.eval_nodal, ← hg x hx, Polynomial.eval_finset_sum]
      · intro x₀ hx₀
        obtain ⟨y, ψ, hy, hψ, h⟩ := hloc x₀ hx₀
        have : DifferentiableAt ℂ
          (fun x => ∑ i, ψ i x * ∏ j ∈ Finset.univ.erase i, (t - y j x)) x₀ := by fun_prop
        refine (this.congr_of_eventuallyEq ?_).differentiableWithinAt
        filter_upwards [h] with x hx
        rw [hx.2.1, Finset.sum_image fun i _ j _ h => hx.1 h]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hx.2.2, ← Finset.image_erase hx.1, Finset.prod_image fun i _ j _ h => hx.1 h]
      · intro x hx
        rw [pow_mul, mul_assoc, ← mul_pow]
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_card_nsmul _ _ ((K * (1 + ‖x‖) ^ M) ^ (n + 1)) fun y hy => ?_).trans
          (by rw [hcard x hx, nsmul_eq_mul])
        rw [norm_mul, pow_succ']
        refine mul_le_mul ((hK x hx).2 y hy).1 (norm_prod_le_pow _ _ _ _ (hK x hx).1
          (Finset.card_erase_le.trans (hcard x hx).le)
          fun y' hy' => ((hK x hx).2 y' (Finset.mem_of_mem_erase hy')).2.2) (norm_nonneg _)
          (zero_le_one.trans (hK x hx).1)
end GlobalTheory.FiniteCoverGrowth
