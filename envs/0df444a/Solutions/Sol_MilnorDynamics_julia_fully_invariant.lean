-- Prove2me | solution 1 for MilnorDynamics.julia_fully_invariant
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:58:55.343178+00:00
-- url     : https://prove2.me/submissions/98baad9c-c394-4d11-a288-bfd2ab5cff3d

import Mathlib
import Definitions.Def_MilnorDynamics_RationalMaps

open scoped OnePoint Topology
open Filter Set

namespace MilnorDynamics

lemma aux_jfi_coclosed : coclosedCompact ℂ = Bornology.cobounded ℂ := by
  rw [Filter.coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact]

lemma aux_jfi_invChart_ne {w : ℂ} (hw : w ≠ 0) : invChart w = ((w⁻¹ : ℂ) : OnePoint ℂ) := by
  simp [invChart, hw]

lemma aux_jfi_invChart_zero : invChart 0 = ∞ := by simp [invChart]

lemma aux_jfi_chartInf_invChart (w : ℂ) : chartInfinite (invChart w) = w := by
  by_cases hw : w = 0
  · subst hw; simp [invChart, chartInfinite]
  · simp [invChart, hw, chartInfinite]

lemma aux_jfi_invChart_chartInf (p : OnePoint ℂ) (hp : p ≠ ((0:ℂ) : OnePoint ℂ)) :
    invChart (chartInfinite p) = p := by
  induction p using OnePoint.rec with
  | infty => simp [invChart, chartInfinite]
  | coe z =>
    have hz : z ≠ 0 := fun h => hp (by rw [h])
    simp [chartInfinite, invChart, hz]

lemma aux_jfi_invChart_ne_zero (w : ℂ) : invChart w ≠ ((0:ℂ) : OnePoint ℂ) := by
  by_cases hw : w = 0
  · simp [invChart, hw]
  · simp [invChart, hw]

lemma aux_jfi_invChart_continuous : Continuous invChart := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 0
  · subst hw
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, aux_jfi_invChart_zero]
    have h2 : Tendsto (fun x : ℂ => x⁻¹) (𝓝[≠] 0) (coclosedCompact ℂ) := by
      rw [aux_jfi_coclosed]; exact tendsto_inv₀_nhdsNE_zero
    have h1 : Tendsto (fun x : ℂ => ((x⁻¹ : ℂ) : OnePoint ℂ)) (𝓝[≠] 0) (𝓝 ∞) :=
      OnePoint.tendsto_coe_infty.comp h2
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [aux_jfi_invChart_ne hx]
  · have : (fun x : ℂ => ((x⁻¹ : ℂ) : OnePoint ℂ)) =ᶠ[𝓝 w] invChart := by
      filter_upwards [isOpen_ne.mem_nhds hw] with x hx
      rw [aux_jfi_invChart_ne hx]
    refine ContinuousAt.congr ?_ this
    exact (OnePoint.continuous_coe.continuousAt).comp (continuousAt_inv₀ hw)

lemma aux_jfi_chartInf_contAt (p : OnePoint ℂ) (hp : p ≠ ((0:ℂ) : OnePoint ℂ)) :
    ContinuousAt chartInfinite p := by
  induction p using OnePoint.rec with
  | infty =>
    rw [ContinuousAt, OnePoint.nhds_infty_eq, tendsto_sup]
    constructor
    · rw [tendsto_map'_iff]
      have : chartInfinite ∘ ((↑) : ℂ → OnePoint ℂ) = fun x => x⁻¹ := by
        funext x; rfl
      rw [this, aux_jfi_coclosed]
      simpa [chartInfinite] using (tendsto_inv₀_cobounded (α := ℂ))
    · exact tendsto_pure_nhds _ _
  | coe z =>
    have hz : z ≠ 0 := fun h => hp (by rw [h])
    rw [← OnePoint.isOpenEmbedding_coe.continuousAt_iff]
    exact continuousAt_inv₀ hz

lemma aux_jfi_invChart_openEmb : Topology.IsOpenEmbedding invChart := by
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    aux_jfi_invChart_continuous ?_ ?_
  · intro a b h; rw [← aux_jfi_chartInf_invChart a, h, aux_jfi_chartInf_invChart]
  · intro U hU
    have hO : IsOpen {p : OnePoint ℂ | p ≠ ((0:ℂ) : OnePoint ℂ)} := isOpen_ne
    have : invChart '' U = {p : OnePoint ℂ | p ≠ ((0:ℂ) : OnePoint ℂ)} ∩ chartInfinite ⁻¹' U := by
      ext p; constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨aux_jfi_invChart_ne_zero w, by simpa [aux_jfi_chartInf_invChart] using hw⟩
      · rintro ⟨hp, hpU⟩; exact ⟨chartInfinite p, hpU, aux_jfi_invChart_chartInf p hp⟩
    rw [this]
    exact ContinuousOn.isOpen_inter_preimage
      (fun p hp => (aux_jfi_chartInf_contAt p hp).continuousWithinAt) hO hU

noncomputable def aux_jfi_rf (P Q : Polynomial ℂ) (t : ℂ) : OnePoint ℂ :=
  if Q.eval t = 0 then ∞ else ((P.eval t / Q.eval t : ℂ) : OnePoint ℂ)

lemma aux_jfi_rf_eq_coe (P Q : Polynomial ℂ) {t : ℂ} (h : Q.eval t ≠ 0) :
    aux_jfi_rf P Q t = ((P.eval t / Q.eval t : ℂ) : OnePoint ℂ) := by
  simp [aux_jfi_rf, h]

lemma aux_jfi_rf_eq_inv (P Q : Polynomial ℂ) {t : ℂ} (h : P.eval t ≠ 0) :
    aux_jfi_rf P Q t = invChart (Q.eval t / P.eval t) := by
  by_cases hQ : Q.eval t = 0
  · simp [aux_jfi_rf, invChart, hQ]
  · have : Q.eval t / P.eval t ≠ 0 := div_ne_zero hQ h
    rw [aux_jfi_invChart_ne this, aux_jfi_rf_eq_coe P Q hQ, inv_div]

lemma aux_jfi_rf_ev_coe (P Q : Polynomial ℂ) {t : ℂ} (h : Q.eval t ≠ 0) :
    aux_jfi_rf P Q =ᶠ[𝓝 t] fun s => ((P.eval s / Q.eval s : ℂ) : OnePoint ℂ) := by
  filter_upwards [Q.continuous.continuousAt.eventually_ne h] with s hs
  exact aux_jfi_rf_eq_coe P Q hs

lemma aux_jfi_rf_ev_inv (P Q : Polynomial ℂ) {t : ℂ} (h : P.eval t ≠ 0) :
    aux_jfi_rf P Q =ᶠ[𝓝 t] fun s => invChart (Q.eval s / P.eval s) := by
  filter_upwards [P.continuous.continuousAt.eventually_ne h] with s hs
  exact aux_jfi_rf_eq_inv P Q hs

lemma aux_jfi_rf_contAt (P Q : Polynomial ℂ) (hPQ : ∀ t, P.eval t = 0 → Q.eval t ≠ 0)
    (t : ℂ) : ContinuousAt (aux_jfi_rf P Q) t := by
  by_cases hQ : Q.eval t = 0
  · have hP : P.eval t ≠ 0 := fun h => hPQ t h hQ
    refine ContinuousAt.congr ?_ (aux_jfi_rf_ev_inv P Q hP).symm
    exact aux_jfi_invChart_continuous.continuousAt.comp
      (Q.continuous.continuousAt.div P.continuous.continuousAt hP)
  · refine ContinuousAt.congr ?_ (aux_jfi_rf_ev_coe P Q hQ).symm
    exact OnePoint.continuous_coe.continuousAt.comp
      (P.continuous.continuousAt.div Q.continuous.continuousAt hQ)

lemma aux_jfi_analytic_div (P Q : Polynomial ℂ) {t : ℂ} (h : Q.eval t ≠ 0) :
    AnalyticAt ℂ (fun s => P.eval s / Q.eval s) t := by
  have hd : DifferentiableOn ℂ (fun s => P.eval s / Q.eval s) {s | Q.eval s ≠ 0} :=
    fun s hs => (P.differentiable s |>.div (Q.differentiable s) hs).differentiableWithinAt
  exact hd.analyticAt ((isOpen_ne.preimage Q.continuous).mem_nhds h)

lemma aux_jfi_poly_eq_of_ev (P Q : Polynomial ℂ) {t c : ℂ} (hQ : Q.eval t ≠ 0)
    (hc : ∀ᶠ s in 𝓝 t, P.eval s / Q.eval s = c) : P = Polynomial.C c * Q := by
  have hzero : P - Polynomial.C c * Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply infinite_of_mem_nhds t
    filter_upwards [hc, Q.continuous.continuousAt.eventually_ne hQ] with s hs hs'
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C]
    rw [← hs]; field_simp; ring
  exact sub_eq_zero.mp hzero

lemma aux_jfi_rf_nhds_le (P Q : Polynomial ℂ) (hPQ : ∀ t, P.eval t = 0 → Q.eval t ≠ 0)
    (hnc : ∀ c : ℂ, P ≠ Polynomial.C c * Q ∧ Q ≠ Polynomial.C c * P) (t : ℂ) :
    𝓝 (aux_jfi_rf P Q t) ≤ map (aux_jfi_rf P Q) (𝓝 t) := by
  by_cases hQ : Q.eval t = 0
  · have hP : P.eval t ≠ 0 := fun h => hPQ t h hQ
    rcases (aux_jfi_analytic_div Q P hP).eventually_constant_or_nhds_le_map_nhds with hc | hle
    · exact absurd (aux_jfi_poly_eq_of_ev Q P hP hc) (hnc _).2
    · rw [map_congr (aux_jfi_rf_ev_inv P Q hP), aux_jfi_rf_eq_inv P Q hP,
        ← aux_jfi_invChart_openEmb.map_nhds_eq]
      calc map invChart (𝓝 (Q.eval t / P.eval t))
          ≤ map invChart (map (fun s => Q.eval s / P.eval s) (𝓝 t)) := map_mono hle
        _ = map (fun s => invChart (Q.eval s / P.eval s)) (𝓝 t) := map_map
  · rcases (aux_jfi_analytic_div P Q hQ).eventually_constant_or_nhds_le_map_nhds with hc | hle
    · exact absurd (aux_jfi_poly_eq_of_ev P Q hQ hc) (hnc _).1
    · rw [map_congr (aux_jfi_rf_ev_coe P Q hQ), aux_jfi_rf_eq_coe P Q hQ,
        ← OnePoint.isOpenEmbedding_coe.map_nhds_eq]
      calc map ((↑) : ℂ → OnePoint ℂ) (𝓝 (P.eval t / Q.eval t))
          ≤ map ((↑) : ℂ → OnePoint ℂ) (map (fun s => P.eval s / Q.eval s) (𝓝 t)) := map_mono hle
        _ = map (fun s => ((P.eval s / Q.eval s : ℂ) : OnePoint ℂ)) (𝓝 t) := map_map


lemma aux_jfi_reflect_eval (p : Polynomial ℂ) (N : ℕ) (hp : p.natDegree ≤ N) {t : ℂ}
    (ht : t ≠ 0) : (p.reflect N).eval t = t ^ N * p.eval t⁻¹ := by
  let _ : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht)
  have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) t⁻¹ N p hp
  rw [invOf_eq_inv, inv_inv] at h
  change Polynomial.eval t _ * _ = Polynomial.eval t⁻¹ p at h
  rw [← h, inv_pow]; field_simp

lemma aux_jfi_toFun_coe (f : RationalMap) (t : ℂ) :
    f.toFun (t : OnePoint ℂ) = aux_jfi_rf f.num f.den t := rfl

lemma aux_jfi_toFun_invChart (f : RationalMap) (t : ℂ) :
    f.toFun (invChart t) = aux_jfi_rf (f.num.reflect f.degree) (f.den.reflect f.degree) t := by
  by_cases ht : t = 0
  · subst ht
    rw [aux_jfi_invChart_zero]
    simp only [aux_jfi_rf, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect,
      Polynomial.revAt_le (Nat.zero_le _), Nat.sub_zero, RationalMap.degree]
    by_cases hd : f.den.natDegree < f.num.natDegree
    · have hm : max f.num.natDegree f.den.natDegree = f.num.natDegree := max_eq_left hd.le
      rw [hm, Polynomial.coeff_eq_zero_of_natDegree_lt hd]
      simp [RationalMap.toFun, hd]
    · have hm : max f.num.natDegree f.den.natDegree = f.den.natDegree :=
        max_eq_right (not_lt.mp hd)
      rw [hm]
      have hl : f.den.coeff f.den.natDegree ≠ 0 := by
        rw [← Polynomial.leadingCoeff]; exact Polynomial.leadingCoeff_ne_zero.mpr f.den_ne_zero
      simp only [RationalMap.toFun, hd, if_false, hl]
      rfl
  · rw [aux_jfi_invChart_ne ht]
    have h1 := aux_jfi_reflect_eval f.num f.degree (le_max_left _ _) ht
    have h2 := aux_jfi_reflect_eval f.den f.degree (le_max_right _ _) ht
    have htN : t ^ f.degree ≠ 0 := pow_ne_zero _ ht
    rw [aux_jfi_toFun_coe]
    simp only [aux_jfi_rf, h1, h2, mul_eq_zero, htN, false_or]
    split_ifs with h
    · rfl
    · congr 1
      rw [mul_div_mul_left _ _ htN]

lemma aux_jfi_nocommon (f : RationalMap) (t : ℂ) (h : f.num.eval t = 0) : f.den.eval t ≠ 0 := by
  intro h'
  obtain ⟨a, b, hab⟩ := f.coprime
  have := congrArg (Polynomial.eval t) hab
  simp [h, h'] at this

lemma aux_jfi_R_nocommon (f : RationalMap) (t : ℂ)
    (h : (f.num.reflect f.degree).eval t = 0) : (f.den.reflect f.degree).eval t ≠ 0 := by
  by_cases ht : t = 0
  · subst ht
    simp only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_reflect,
      Polynomial.revAt_le (Nat.zero_le _), Nat.sub_zero, RationalMap.degree] at h ⊢
    by_cases hd : f.den.natDegree < f.num.natDegree
    · exfalso
      have hm : max f.num.natDegree f.den.natDegree = f.num.natDegree := max_eq_left hd.le
      rw [hm] at h
      have hn : f.num ≠ 0 := by
        intro h0; rw [h0] at hd; simp at hd
      exact (Polynomial.leadingCoeff_ne_zero.mpr hn) h
    · have hm : max f.num.natDegree f.den.natDegree = f.den.natDegree :=
        max_eq_right (not_lt.mp hd)
      rw [hm]
      exact Polynomial.leadingCoeff_ne_zero.mpr f.den_ne_zero
  · rw [aux_jfi_reflect_eval f.den f.degree (le_max_right _ _) ht]
    rw [aux_jfi_reflect_eval f.num f.degree (le_max_left _ _) ht] at h
    have htN : t ^ f.degree ≠ 0 := pow_ne_zero _ ht
    rw [mul_eq_zero] at h
    exact mul_ne_zero htN (aux_jfi_nocommon f _ (h.resolve_left htN))

lemma aux_jfi_nc (f : RationalMap) (hf : ¬(f.num.natDegree = 0 ∧ f.den.natDegree = 0)) (c : ℂ) :
    f.num ≠ Polynomial.C c * f.den ∧ f.den ≠ Polynomial.C c * f.num := by
  constructor
  · intro h
    apply hf
    have hc := f.coprime
    rw [h] at hc
    have hu : IsUnit f.den := isCoprime_self.mp (IsCoprime.of_mul_left_right hc)
    have h0 : f.den.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    refine ⟨?_, h0⟩
    rw [h]; exact Nat.le_zero.mp ((Polynomial.natDegree_C_mul_le c f.den).trans h0.le)
  · intro h
    apply hf
    have hc := f.coprime
    rw [h] at hc
    have hu : IsUnit f.num := isCoprime_self.mp (IsCoprime.of_mul_right_right hc)
    have h0 : f.num.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    refine ⟨h0, ?_⟩
    rw [h]; exact Nat.le_zero.mp ((Polynomial.natDegree_C_mul_le c f.num).trans h0.le)

lemma aux_jfi_R_nc (f : RationalMap) (hf : ¬(f.num.natDegree = 0 ∧ f.den.natDegree = 0))
    (c : ℂ) : f.num.reflect f.degree ≠ Polynomial.C c * f.den.reflect f.degree ∧
      f.den.reflect f.degree ≠ Polynomial.C c * f.num.reflect f.degree := by
  obtain ⟨h1, h2⟩ := aux_jfi_nc f hf c
  constructor
  · intro h; apply h1
    have := congrArg (Polynomial.reflect f.degree) h
    rwa [Polynomial.reflect_reflect, Polynomial.reflect_C_mul, Polynomial.reflect_reflect] at this
  · intro h; apply h2
    have := congrArg (Polynomial.reflect f.degree) h
    rwa [Polynomial.reflect_reflect, Polynomial.reflect_C_mul, Polynomial.reflect_reflect] at this

lemma aux_jfi_toFun_cont (f : RationalMap) : Continuous f.toFun := by
  rw [continuous_iff_continuousAt]
  intro p
  induction p using OnePoint.rec with
  | infty =>
    rw [← aux_jfi_invChart_zero, ← aux_jfi_invChart_openEmb.continuousAt_iff]
    have : f.toFun ∘ invChart = aux_jfi_rf _ _ := funext (aux_jfi_toFun_invChart f)
    rw [this]; exact aux_jfi_rf_contAt _ _ (aux_jfi_R_nocommon f) 0
  | coe t =>
    rw [← OnePoint.isOpenEmbedding_coe.continuousAt_iff]
    exact aux_jfi_rf_contAt _ _ (aux_jfi_nocommon f) t

lemma aux_jfi_toFun_open (f : RationalMap) (hf : ¬(f.num.natDegree = 0 ∧ f.den.natDegree = 0)) :
    IsOpenMap f.toFun := by
  rw [isOpenMap_iff_nhds_le]
  intro p
  induction p using OnePoint.rec with
  | infty =>
    rw [← aux_jfi_invChart_zero, ← aux_jfi_invChart_openEmb.map_nhds_eq, map_map,
      aux_jfi_toFun_invChart]
    have : f.toFun ∘ invChart = aux_jfi_rf _ _ := funext (aux_jfi_toFun_invChart f)
    rw [this]
    exact aux_jfi_rf_nhds_le _ _ (aux_jfi_R_nocommon f) (aux_jfi_R_nc f hf) 0
  | coe t =>
    rw [← OnePoint.isOpenEmbedding_coe.map_nhds_eq, map_map, aux_jfi_toFun_coe]
    have : f.toFun ∘ ((↑) : ℂ → OnePoint ℂ) = aux_jfi_rf _ _ := funext (aux_jfi_toFun_coe f)
    rw [this]
    exact aux_jfi_rf_nhds_le _ _ (aux_jfi_nocommon f) (aux_jfi_nc f hf) t

lemma aux_jfi_toFun_const (f : RationalMap) (hf : f.num.natDegree = 0 ∧ f.den.natDegree = 0)
    (p q : OnePoint ℂ) : f.toFun p = f.toFun q := by
  have key : ∀ p, f.toFun p = ((f.num.coeff 0 / f.den.coeff 0 : ℂ) : OnePoint ℂ) := by
    intro p
    have hd0 : f.den.coeff 0 ≠ 0 := by
      have := Polynomial.leadingCoeff_ne_zero.mpr f.den_ne_zero
      rwa [Polynomial.leadingCoeff, hf.2] at this
    induction p using OnePoint.rec with
    | infty =>
      simp only [RationalMap.toFun, hf.1, hf.2, lt_irrefl, if_false, Polynomial.leadingCoeff]
    | coe t =>
      rw [aux_jfi_toFun_coe, Polynomial.eq_C_of_natDegree_eq_zero hf.1,
        Polynomial.eq_C_of_natDegree_eq_zero hf.2]
      simp [aux_jfi_rf, hd0]
  rw [key p, key q]

noncomputable def aux_jfi_S : OnePoint ℂ → EuclideanSpace ℝ (Fin 3)
  | some z => !₂[2 * z.re / (1 + ‖z‖ ^ 2), 2 * z.im / (1 + ‖z‖ ^ 2),
      (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2)]
  | none => !₂[0, 0, 1]

lemma aux_jfi_normsq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

lemma aux_jfi_chordal_nonneg (a b : OnePoint ℂ) : 0 ≤ chordalDist a b := by
  induction a using OnePoint.rec <;> induction b using OnePoint.rec <;>
    simp only [chordalDist] <;> first | rfl | positivity

lemma aux_jfi_chordal_sq (a b : OnePoint ℂ) :
    chordalDist a b ^ 2 = ∑ i, dist (aux_jfi_S a i) (aux_jfi_S b i) ^ 2 := by
  simp only [Fin.sum_univ_three, Real.dist_eq, sq_abs]
  induction a using OnePoint.rec with
  | infty =>
    induction b using OnePoint.rec with
    | infty => simp [chordalDist, aux_jfi_S]
    | coe w =>
      simp [chordalDist, aux_jfi_S, div_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1 + ‖w‖ ^ 2)]
      simp only [aux_jfi_normsq]
      field_simp
      ring
  | coe z =>
    induction b using OnePoint.rec with
    | infty =>
      simp [chordalDist, aux_jfi_S, div_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1 + ‖z‖ ^ 2)]
      simp only [aux_jfi_normsq]
      field_simp
      ring
    | coe w =>
      simp [chordalDist, aux_jfi_S, div_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1 + ‖z‖ ^ 2), Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1 + ‖w‖ ^ 2)]
      simp only [aux_jfi_normsq, Complex.sub_re, Complex.sub_im]
      field_simp
      ring


lemma aux_jfi_chordal_eq (a b : OnePoint ℂ) :
    chordalDist a b = dist (aux_jfi_S a) (aux_jfi_S b) := by
  rw [EuclideanSpace.dist_eq, ← aux_jfi_chordal_sq, Real.sqrt_sq (aux_jfi_chordal_nonneg a b)]

lemma aux_jfi_chordal_self (x : OnePoint ℂ) : chordalDist x x = 0 := by
  rw [aux_jfi_chordal_eq, dist_self]

lemma aux_jfi_chordal_eq_zero {a b : OnePoint ℂ} (h : chordalDist a b = 0) : a = b := by
  induction a using OnePoint.rec with
  | infty =>
    induction b using OnePoint.rec with
    | infty => rfl
    | coe w =>
      exfalso; simp only [chordalDist] at h
      have : (0:ℝ) < 2 / √(1 + ‖w‖ ^ 2) := by positivity
      linarith
  | coe z =>
    induction b using OnePoint.rec with
    | infty =>
      exfalso; simp only [chordalDist] at h
      have : (0:ℝ) < 2 / √(1 + ‖z‖ ^ 2) := by positivity
      linarith
    | coe w =>
      simp only [chordalDist] at h
      have h1 : 0 < √(1 + ‖z‖ ^ 2) * √(1 + ‖w‖ ^ 2) := by positivity
      rw [div_eq_zero_iff] at h
      rcases h with h | h
      · have : ‖z - w‖ = 0 := by linarith
        rw [norm_eq_zero, sub_eq_zero] at this; rw [this]
      · linarith

lemma aux_jfi_unique (a : ℕ → OnePoint ℂ) (b c : OnePoint ℂ)
    (hb : ∀ ε > 0, ∀ᶠ k in atTop, chordalDist (a k) b < ε)
    (hc : ∀ ε > 0, ∀ᶠ k in atTop, chordalDist (a k) c < ε) : b = c := by
  apply aux_jfi_chordal_eq_zero
  rw [aux_jfi_chordal_eq]
  by_contra hne
  have hpos : 0 < dist (aux_jfi_S b) (aux_jfi_S c) := lt_of_le_of_ne dist_nonneg (Ne.symm hne)
  obtain ⟨k, hk1, hk2⟩ := ((hb _ (half_pos hpos)).and (hc _ (half_pos hpos))).exists
  rw [aux_jfi_chordal_eq] at hk1 hk2
  have := dist_triangle (aux_jfi_S b) (aux_jfi_S (a k)) (aux_jfi_S c)
  rw [dist_comm (aux_jfi_S b) (aux_jfi_S (a k))] at this
  linarith

def aux_jfi_SNI (f : OnePoint ℂ → OnePoint ℂ) (N : Set (OnePoint ℂ)) : Prop :=
  ∀ n : ℕ → ℕ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : OnePoint ℂ → OnePoint ℂ, ContinuousOn g N ∧
    ∀ K ⊆ N, IsCompact K → ∀ ε > 0, ∀ᶠ k in atTop, ∀ x ∈ K,
      chordalDist (f^[n (φ k)] x) (g x) < ε

lemma aux_jfi_chart (f : OnePoint ℂ → OnePoint ℂ) (e : ℂ → OnePoint ℂ)
    (he : Topology.IsOpenEmbedding e) (w₀ : ℂ) :
    (∃ V : Set ℂ, IsOpen V ∧ w₀ ∈ V ∧ IsNormalFamily V
      ((fun g : OnePoint ℂ → OnePoint ℂ => fun w : ℂ => g (e w)) '' Set.range fun n : ℕ => f^[n]))
    ↔ ∃ N : Set (OnePoint ℂ), IsOpen N ∧ e w₀ ∈ N ∧ aux_jfi_SNI f N := by
  constructor
  · rintro ⟨V, hV, hw₀, hnorm⟩
    refine ⟨e '' V, he.isOpenMap V hV, mem_image_of_mem e hw₀, ?_⟩
    intro n
    obtain ⟨φ, hφ, g', hg', hconv⟩ := hnorm (fun k => fun w => f^[n k] (e w))
      (fun k => ⟨f^[n k], ⟨n k, rfl⟩, rfl⟩)
    refine ⟨φ, hφ, fun p => g' (Function.invFun e p), ?_, ?_⟩
    · rw [he.isInducing.continuousOn_image_iff]
      have : (fun p => g' (Function.invFun e p)) ∘ e = g' := by
        funext w; simp [Function.leftInverse_invFun he.injective w]
      rw [this]; exact hg'
    · intro K hKN hK ε hε
      have hKr : K ⊆ range e := hKN.trans (image_subset_range e V)
      have hK' : IsCompact (e ⁻¹' K) := by
        rw [he.isInducing.isCompact_iff, image_preimage_eq_of_subset hKr]; exact hK
      have hK'V : e ⁻¹' K ⊆ V := by
        intro w hw
        obtain ⟨v, hv, hve⟩ := hKN hw
        rw [← he.injective hve]; exact hv
      filter_upwards [hconv (e ⁻¹' K) hK'V hK' ε hε] with k hk
      intro x hx
      obtain ⟨w, rfl⟩ := hKr hx
      have := hk w hx
      simpa [Function.leftInverse_invFun he.injective w] using this
  · rintro ⟨N, hN, hw₀, hSNI⟩
    refine ⟨e ⁻¹' N, hN.preimage he.continuous, hw₀, ?_⟩
    intro F hF
    choose G hG hGF using hF
    choose m hm using hG
    obtain ⟨φ, hφ, g, hg, hconv⟩ := hSNI m
    refine ⟨φ, hφ, g ∘ e, hg.comp he.continuous.continuousOn (mapsTo_preimage e N), ?_⟩
    intro K hKV hK ε hε
    have hKN : e '' K ⊆ N := by rintro _ ⟨w, hw, rfl⟩; exact hKV hw
    filter_upwards [hconv (e '' K) hKN (hK.image he.continuous) ε hε] with k hk
    intro w hw
    have h1 := hk (e w) (mem_image_of_mem e hw)
    have h2 : F (φ k) w = f^[m (φ k)] (e w) := by
      rw [← hGF (φ k), ← hm (φ k)]
    rw [h2]; exact h1

lemma aux_jfi_fatou_iff (f : OnePoint ℂ → OnePoint ℂ) (p : OnePoint ℂ) :
    p ∈ fatouSet f ↔ ∃ N : Set (OnePoint ℂ), IsOpen N ∧ p ∈ N ∧ aux_jfi_SNI f N := by
  induction p using OnePoint.rec with
  | infty =>
    have := aux_jfi_chart f invChart aux_jfi_invChart_openEmb 0
    rw [aux_jfi_invChart_zero] at this
    rw [← this]; rfl
  | coe z =>
    exact aux_jfi_chart f (↑) OnePoint.isOpenEmbedding_coe z

lemma aux_jfi_split (n : ℕ → ℕ) : (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, n (φ k) = 0) ∨
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, n (φ k) ≠ 0) := by
  by_cases h : ∃ᶠ k in atTop, n k = 0
  · exact Or.inl (extraction_of_frequently_atTop h)
  · rw [not_frequently] at h
    exact Or.inr (extraction_of_frequently_atTop h.frequently)

lemma aux_jfi_iter (f : OnePoint ℂ → OnePoint ℂ) (m : ℕ) (x : OnePoint ℂ) :
    f^[m + 1] x = f^[m] (f x) := by
  rw [Function.iterate_add_apply, Function.iterate_one]

lemma aux_jfi_dirA (f : OnePoint ℂ → OnePoint ℂ) (hf : Continuous f) (N : Set (OnePoint ℂ))
    (h : aux_jfi_SNI f N) : aux_jfi_SNI f (f ⁻¹' N) := by
  intro n
  rcases aux_jfi_split n with ⟨φ, hφ, h0⟩ | ⟨φ₁, hφ₁, h1⟩
  · refine ⟨φ, hφ, id, continuousOn_id, ?_⟩
    intro K _ _ ε hε
    exact Eventually.of_forall fun k x _ => by simp [h0 k, aux_jfi_chordal_self, hε]
  · obtain ⟨φ₂, hφ₂, g, hg, hconv⟩ := h (fun k => n (φ₁ k) - 1)
    refine ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, g ∘ f, hg.comp hf.continuousOn (mapsTo_preimage f N), ?_⟩
    intro K hKN hK ε hε
    have hfK : f '' K ⊆ N := by rintro _ ⟨x, hx, rfl⟩; exact hKN hx
    filter_upwards [hconv (f '' K) hfK (hK.image hf) ε hε] with k hk
    intro x hx
    have := hk (f x) (mem_image_of_mem f hx)
    have he : n (φ₁ (φ₂ k)) = (n (φ₁ (φ₂ k)) - 1) + 1 :=
      (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (h1 _))).symm
    simp only [Function.comp_apply]
    rw [he, aux_jfi_iter]
    exact this

lemma aux_jfi_dirB (f : OnePoint ℂ → OnePoint ℂ) (ho : IsOpenMap f)
    (N : Set (OnePoint ℂ)) (hN : IsOpen N) (z : OnePoint ℂ) (hz : z ∈ N) (h : aux_jfi_SNI f N) :
    ∃ N' : Set (OnePoint ℂ), IsOpen N' ∧ f z ∈ N' ∧ aux_jfi_SNI f N' := by
  obtain ⟨L, hLc, hzL, hLN⟩ := exists_compact_subset hN hz
  refine ⟨f '' interior L, ho _ isOpen_interior, mem_image_of_mem f hzL, ?_⟩
  intro n
  obtain ⟨φ, hφ, g, hg, hconv⟩ := h (fun k => n k + 1)
  have hcons : ∀ x ∈ N, ∀ x' ∈ N, f x = f x' → g x = g x' := by
    intro x hx x' hx' hxx'
    apply aux_jfi_unique (fun k => f^[n (φ k) + 1] x)
    · intro ε hε
      filter_upwards [hconv {x} (singleton_subset_iff.mpr hx) isCompact_singleton ε hε] with k hk
      exact hk x rfl
    · intro ε hε
      filter_upwards [hconv {x'} (singleton_subset_iff.mpr hx') isCompact_singleton ε hε] with k hk
      have := hk x' rfl
      simp only [aux_jfi_iter] at this ⊢
      rw [hxx']; exact this
  have hex : ∀ y, ∃ x, y ∈ f '' interior L → x ∈ interior L ∧ f x = y := by
    intro y
    by_cases hy : y ∈ f '' interior L
    · obtain ⟨x, hx, rfl⟩ := hy; exact ⟨x, fun _ => ⟨hx, rfl⟩⟩
    · exact ⟨y, fun h => absurd h hy⟩
  choose xOf hxOf using hex
  refine ⟨φ, hφ, fun y => g (xOf y), ?_, ?_⟩
  · rw [continuousOn_open_iff (ho _ isOpen_interior)]
    intro W hW
    have hgW : IsOpen (interior L ∩ g ⁻¹' W) :=
      (hg.mono (interior_subset.trans hLN)).isOpen_inter_preimage isOpen_interior hW
    have : f '' interior L ∩ (fun y => g (xOf y)) ⁻¹' W = f '' (interior L ∩ g ⁻¹' W) := by
      ext y; constructor
      · rintro ⟨hy, hyW⟩
        obtain ⟨h1, h2⟩ := hxOf y hy
        exact ⟨xOf y, ⟨h1, hyW⟩, h2⟩
      · rintro ⟨x, ⟨hx, hxW⟩, rfl⟩
        have hy : f x ∈ f '' interior L := mem_image_of_mem f hx
        obtain ⟨h1, h2⟩ := hxOf (f x) hy
        refine ⟨hy, ?_⟩
        show g (xOf (f x)) ∈ W
        rw [hcons (xOf (f x)) (hLN (interior_subset h1)) x (hLN (interior_subset hx)) h2]
        exact hxW
    rw [this]; exact ho _ hgW
  · intro K hK _ ε hε
    filter_upwards [hconv L hLN hLc ε hε] with k hk
    intro y hy
    obtain ⟨h1, h2⟩ := hxOf y (hK hy)
    have := hk (xOf y) (interior_subset h1)
    simp only [aux_jfi_iter, h2] at this
    exact this

lemma aux_jfi_const_SNI (f : OnePoint ℂ → OnePoint ℂ) (hf : ∀ p q, f p = f q) :
    aux_jfi_SNI f univ := by
  intro n
  rcases aux_jfi_split n with ⟨φ, hφ, h0⟩ | ⟨φ, hφ, h1⟩
  · refine ⟨φ, hφ, id, continuousOn_id, ?_⟩
    intro K _ _ ε hε
    exact Eventually.of_forall fun k x _ => by simp [h0 k, aux_jfi_chordal_self, hε]
  · refine ⟨φ, hφ, fun _ => f ∞, continuousOn_const, ?_⟩
    intro K _ _ ε hε
    refine Eventually.of_forall fun k x _ => ?_
    have he : n (φ k) = (n (φ k) - 1) + 1 :=
      (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (h1 _))).symm
    rw [he, Function.iterate_succ_apply', hf _ ∞, aux_jfi_chordal_self]
    exact hε

end MilnorDynamics

open MilnorDynamics

theorem solution (f : RationalMap) (z : OnePoint ℂ) :
    z ∈ juliaSet f.toFun ↔ f.toFun z ∈ juliaSet f.toFun := by
  simp only [juliaSet, mem_compl_iff]
  rw [not_iff_not]
  constructor
  · intro hz
    by_cases hc : f.num.natDegree = 0 ∧ f.den.natDegree = 0
    · rw [aux_jfi_fatou_iff]
      exact ⟨univ, isOpen_univ, mem_univ _, aux_jfi_const_SNI f.toFun (aux_jfi_toFun_const f hc)⟩
    · rw [aux_jfi_fatou_iff] at hz ⊢
      obtain ⟨N, hN, hzN, hS⟩ := hz
      exact aux_jfi_dirB f.toFun (aux_jfi_toFun_open f hc) N hN z hzN hS
  · intro hfz
    rw [aux_jfi_fatou_iff] at hfz ⊢
    obtain ⟨N, hN, hzN, hS⟩ := hfz
    exact ⟨f.toFun ⁻¹' N, hN.preimage (aux_jfi_toFun_cont f), hzN,
      aux_jfi_dirA f.toFun (aux_jfi_toFun_cont f) N hS⟩
