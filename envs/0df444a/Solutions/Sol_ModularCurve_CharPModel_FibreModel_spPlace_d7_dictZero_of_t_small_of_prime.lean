-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.spPlace_d7_dictZero_of_t_small_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c760f568-7250-513d-9fad-b55d2fc5f52d

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Theorems.Thm_ModularCurve_forall_ord_jBar_sub_le_zero_or_exists_ord_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero_of_t_small_of_prime
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option maxHeartbeats 6400000

p2m_open "AlgebraicCurve ModularCurve~dedekindPsi_prime ModularCurve.CharPModel Polynomial"

set_option autoImplicit false

noncomputable section

namespace SpPlaceD7Prime

structure PreShape (Φ : ℤ[X][X]) (N : ℕ) : Prop where
  deg : ∀ k, N + 1 < k → Φ.coeff k = 0
  degX : ∀ k i, N + 1 < i → (Φ.coeff k).coeff i = 0
  top : ∀ i, (Φ.coeff (N + 1)).coeff i = if i = 0 then 1 else 0
  right : ∀ k, (Φ.coeff k).coeff (N + 1) = if k = 0 then 1 else 0

structure Shape (Φ : ℤ[X][X]) (N : ℕ) : Prop extends PreShape Φ N where
  corner : (Φ.coeff N).coeff N = -1

namespace PreShape

variable {Φ : ℤ[X][X]} {N : ℕ}

theorem natDegree_lt (hS : PreShape Φ N) : Φ.natDegree < N + 2 := by
  rw [Nat.lt_succ_iff, natDegree_le_iff_coeff_eq_zero]
  intro k hk
  exact hS.deg k (by exact_mod_cast hk)

theorem natDegree_coeff_lt (hS : PreShape Φ N) (k : ℕ) : (Φ.coeff k).natDegree < N + 2 := by
  rw [Nat.lt_succ_iff, natDegree_le_iff_coeff_eq_zero]
  intro i hi
  exact hS.degX k i (by exact_mod_cast hi)

theorem coeff_eq_zero_of_lt (hS : PreShape Φ N) (hN : 1 ≤ N) {i k : ℕ} (hi : i < N + 2)
    (hk : k < N + 2) (h : N * (N + 1) < i + N * k) : (Φ.coeff k).coeff i = 0 := by
  rcases Nat.lt_or_ge k N with hkN | hkN
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkN
    have h1 : (k + d + 1) * (k + d + 1 + 1) < i + (k + d + 1) * k := h
    nlinarith
  · rcases Nat.lt_or_ge k (N + 1) with hk1 | hk1
    · obtain rfl : k = N := by omega
      have hi' : i = k + 1 := by
        rcases Nat.lt_or_ge i (k + 1) with h2 | h2
        · exfalso
          nlinarith
        · omega
      subst hi'
      rw [hS.right]
      simp [show k ≠ 0 by omega]
    · obtain rfl : k = N + 1 := by omega
      rw [hS.top]
      have : i ≠ 0 := by
        rintro rfl
        simp at h
      simp [this]

theorem eval₂_eq_sum (hP : PreShape Φ N) {L : Type*} [CommRing L] [Algebra ℤ L] (x y : L) :
    Φ.eval₂ (aeval (R := ℤ) x).toRingHom y
      = ∑ p ∈ Finset.range (N + 2) ×ˢ Finset.range (N + 2),
          (((Φ.coeff p.1).coeff p.2 : ℤ) : L) * (x ^ p.2 * y ^ p.1) := by
  rw [eval₂_eq_sum_range' _ hP.natDegree_lt, Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_def,
    eval₂_eq_sum_range' _ (hP.natDegree_coeff_lt k), Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [eq_intCast]
  ring

end PreShape

theorem order_eq_of_coeff {x : LaurentSeries ℚ} {m : ℤ} (h1 : x.coeff m ≠ 0)
    (h2 : ∀ m' < m, x.coeff m' = 0) : x.order = m := by
  have hx : x ≠ 0 := fun h => h1 (by rw [h]; rfl)
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra hlt
  push Not at hlt
  exact hx (HahnSeries.coeff_order_eq_zero.mp (h2 _ hlt))

def Monic1 (x : LaurentSeries ℚ) (e : ℤ) : Prop :=
  x ≠ 0 ∧ x.order = e ∧ x.leadingCoeff = 1

namespace Monic1

theorem of_coeff {x : LaurentSeries ℚ} {e : ℤ} (h1 : x.coeff e = 1)
    (h2 : ∀ m < e, x.coeff m = 0) : Monic1 x e := by
  have hne : x.coeff e ≠ 0 := by rw [h1]; exact one_ne_zero
  have hx : x ≠ 0 := fun h => hne (by rw [h]; rfl)
  have ho : x.order = e := order_eq_of_coeff hne h2
  exact ⟨hx, ho, by rw [HahnSeries.leadingCoeff_eq, ho, h1]⟩

variable {x y : LaurentSeries ℚ} {e ex ey : ℤ}

theorem coeff_self (h : Monic1 x e) : x.coeff e = 1 := by
  rw [← h.2.1, ← HahnSeries.leadingCoeff_eq]; exact h.2.2

theorem coeff_of_lt (h : Monic1 x e) {m : ℤ} (hm : m < e) : x.coeff m = 0 :=
  HahnSeries.coeff_eq_zero_of_lt_order (by rw [h.2.1]; exact hm)

theorem mul (hx : Monic1 x ex) (hy : Monic1 y ey) : Monic1 (x * y) (ex + ey) := by
  have ho : (x * y).order = ex + ey := by rw [HahnSeries.order_mul hx.1 hy.1, hx.2.1, hy.2.1]
  refine ⟨mul_ne_zero hx.1 hy.1, ho, ?_⟩
  rw [HahnSeries.leadingCoeff_eq, ho, ← hx.2.1, ← hy.2.1, HahnSeries.coeff_mul_order_add_order,
    hx.2.2, hy.2.2, mul_one]

theorem one : Monic1 1 0 :=
  of_coeff (by simp) fun m hm => by
    rw [← HahnSeries.single_zero_one, HahnSeries.coeff_single_of_ne hm.ne]

theorem congr {e' : ℤ} (h : Monic1 x e) (h' : e = e') : Monic1 x e' := h' ▸ h

theorem pow (hx : Monic1 x e) : ∀ n : ℕ, Monic1 (x ^ n) (n * e)
  | 0 => by simpa using one
  | n + 1 => by
    rw [pow_succ]
    exact ((pow hx n).mul hx).congr (by push_cast; ring)

end Monic1

theorem monic1_jq : Monic1 jq (-1) :=
  Monic1.of_coeff coeff_jq_neg_one fun _ hm => coeff_jq_of_lt hm

theorem monic1_qExpand {x : LaurentSeries ℚ} {e : ℤ} (hx : Monic1 x e) (N : ℕ) [NeZero N] :
    Monic1 (qExpand ℚ N x) (N * e) := by
  refine Monic1.of_coeff (by rw [qExpand_coeff_mul, hx.coeff_self]) fun m hm => ?_
  by_cases hd : (N : ℤ) ∣ m
  · obtain ⟨m', rfl⟩ := hd
    rw [qExpand_coeff_mul]
    apply hx.coeff_of_lt
    have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    exact lt_of_mul_lt_mul_left hm hN.le
  · exact qExpand_coeff_of_not_dvd N _ hd

theorem monic1_term (N : ℕ) [NeZero N] (i k : ℕ) :
    Monic1 (jq ^ i * qExpand ℚ N jq ^ k) (-((i + N * k : ℕ) : ℤ)) := by
  exact ((monic1_jq.pow i).mul ((monic1_qExpand monic1_jq N).pow k)).congr (by push_cast; ring)

theorem intCast_mul_coeff (c : ℤ) (x : LaurentSeries ℚ) (m : ℤ) :
    (((c : ℤ) : LaurentSeries ℚ) * x).coeff m = (c : ℚ) * x.coeff m := by
  rw [← HahnSeries.single_zero_intCast, HahnSeries.coeff_single_zero_mul]

theorem corner_of_eval {Φ : ℤ[X][X]} {N : ℕ} [NeZero N] (hP : PreShape Φ N) (hN : 2 ≤ N)
    (heval : Φ.eval₂ (aeval (R := ℤ) jq).toRingHom (qExpand ℚ N jq) = 0) :
    (Φ.coeff N).coeff N = -1 := by
  set S := Finset.range (N + 2) ×ˢ Finset.range (N + 2) with hS
  set m₀ : ℤ := -((N * (N + 1) : ℕ) : ℤ) with hm₀
  have key : ∀ p ∈ S, p ≠ (N + 1, 0) ∧ p ≠ (N, N) →
      ((((Φ.coeff p.1).coeff p.2 : ℤ) : LaurentSeries ℚ)
        * (jq ^ p.2 * qExpand ℚ N jq ^ p.1)).coeff m₀ = 0 := by
    rintro ⟨k, i⟩ hp hne
    simp only [hS, Finset.mem_product, Finset.mem_range] at hp
    simp only [ne_eq, Prod.mk.injEq, not_and] at hne
    rw [intCast_mul_coeff]
    rcases Nat.lt_trichotomy (i + N * k) (N * (N + 1)) with h | h | h
    · rw [(monic1_term N i k).coeff_of_lt, mul_zero]
      rw [hm₀, neg_lt_neg_iff, Nat.cast_lt]
      exact h
    · exfalso
      rcases Nat.lt_or_ge k N with hkN | hkN
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkN
        nlinarith [hp.1, hp.2]
      · rcases Nat.lt_or_ge k (N + 1) with h1 | h1
        · obtain rfl : k = N := by omega
          have hi : i = k := by nlinarith
          exact hne.2 rfl hi
        · obtain rfl : k = N + 1 := by omega
          have hi : i = 0 := by nlinarith
          exact hne.1 rfl hi
    · rw [hP.coeff_eq_zero_of_lt (by omega) hp.2 hp.1 h]
      simp
  have hc : (Φ.eval₂ (aeval (R := ℤ) jq).toRingHom (qExpand ℚ N jq)).coeff m₀ = 0 := by
    rw [heval]; rfl
  have hne : ((N + 1, 0) : ℕ × ℕ) ≠ (N, N) := by
    simp
  rw [hP.eval₂_eq_sum jq (qExpand ℚ N jq), HahnSeries.coeff_sum,
    Finset.sum_eq_add (N + 1, 0) (N, N) hne key
    (fun h => absurd (by simp [hS]) h) (fun h => absurd (by simp [hS]) h)] at hc
  rw [intCast_mul_coeff, intCast_mul_coeff, hP.top, if_pos rfl] at hc
  have ha1 : (jq ^ 0 * qExpand ℚ N jq ^ (N + 1)).coeff m₀ = 1 := by
    convert (monic1_term N 0 (N + 1)).coeff_self using 2
    rw [hm₀]; push_cast; ring
  have hb1 : (jq ^ N * qExpand ℚ N jq ^ N).coeff m₀ = 1 := by
    convert (monic1_term N N N).coeff_self using 2
    rw [hm₀]; push_cast; ring
  simp only [ha1, hb1, mul_one, Int.cast_one] at hc
  have : ((Φ.coeff N).coeff N : ℚ) = -1 := by linarith
  exact_mod_cast this

theorem aeval_jq_injective :
    Function.Injective (aeval (R := ℤ) (A := LaurentSeries ℚ) jq) := by
  intro p q hpq
  by_contra hne
  have hr : p - q ≠ 0 := sub_ne_zero.mpr hne
  have h0 : aeval (R := ℤ) jq (p - q) = 0 := by rw [map_sub, hpq, sub_self]
  set r := p - q with hr_def
  have hcoeff : (aeval (R := ℤ) jq r).coeff (-(r.natDegree : ℤ)) = (r.leadingCoeff : ℚ) := by
    rw [aeval_def, eval₂_eq_sum_range, HahnSeries.coeff_sum]
    rw [Finset.sum_eq_single r.natDegree]
    · rw [eq_intCast, intCast_mul_coeff, coeff_jq_pow_self, mul_one,
        leadingCoeff]
    · intro b hb hbne
      have hb' : b < r.natDegree := lt_of_le_of_ne (Finset.mem_range_succ_iff.mp hb) hbne
      rw [eq_intCast, intCast_mul_coeff, coeff_jq_pow_of_lt (by omega),
        mul_zero]
    · intro h; exact absurd (Finset.self_mem_range_succ r.natDegree) h
  rw [h0] at hcoeff
  have : r = 0 := by simpa using hcoeff.symm
  exact hr this

theorem coeff_symm {Φ : ℤ[X][X]} (hsym : EvalSymm Φ) (k i : ℕ) :
    (Φ.coeff k).coeff i = (Φ.coeff i).coeff k := by
  have hpoly : ∀ b : ℤ, Φ.eval (C b) = Φ.map (evalRingHom b) := by
    intro b
    apply aeval_jq_injective
    have h := hsym jq (algebraMap ℤ (LaurentSeries ℚ) b)
    have hL : Φ.eval₂ (aeval (R := ℤ) jq).toRingHom (algebraMap ℤ (LaurentSeries ℚ) b)
        = aeval (R := ℤ) jq (Φ.eval (C b)) := by
      rw [show algebraMap ℤ (LaurentSeries ℚ) b = (aeval (R := ℤ) jq).toRingHom (C b) by simp,
        eval₂_at_apply]
      rfl
    have hcomp : (aeval (R := ℤ) (algebraMap ℤ (LaurentSeries ℚ) b)).toRingHom
        = (algebraMap ℤ (LaurentSeries ℚ)).comp (evalRingHom b) := by
      apply Polynomial.ringHom_ext
      · intro a; simp
      · simp
    have hR : Φ.eval₂ (aeval (R := ℤ) (algebraMap ℤ (LaurentSeries ℚ) b)).toRingHom jq
        = aeval (R := ℤ) jq (Φ.map (evalRingHom b)) := by
      rw [hcomp, ← eval₂_map, aeval_def]
    rw [← hL, ← hR]
    exact h
  set R : ℤ[X] := ∑ k ∈ Finset.range (Φ.natDegree + 1), C ((Φ.coeff k).coeff i) * X ^ k
    with hRdef
  have hReq : R = Φ.coeff i := by
    apply Polynomial.funext
    intro b
    have h := congrArg (fun P : ℤ[X] => P.coeff i) (hpoly b)
    simp only [coeff_map, coe_evalRingHom] at h
    rw [← h, hRdef, eval_finsetSum, eval_eq_sum_range, finsetSum_coeff]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X, ← C_pow, coeff_mul_C]
  have h := congrArg (fun P : ℤ[X] => P.coeff k) hReq
  simp only [hRdef, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq,
    Finset.mem_range] at h
  split_ifs at h with hk
  · exact h
  · have : Φ.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [this, coeff_zero]
    exact h

theorem dedekindPsi_prime {N : ℕ} (hp : N.Prime) : dedekindPsi N = N + 1 := by
  rw [dedekindPsi, hp.divisors, Finset.filter_true_of_mem, Finset.sum_pair hp.one_lt.ne,
    Nat.div_one, Nat.div_self hp.pos]
  intro d hd
  rw [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl
  exacts [squarefree_one, hp.prime.squarefree]

theorem preShape_of_prime {N : ℕ} [NeZero N] (hp : N.Prime) (data : ModularPolynomialData N)
    (hsym : EvalSymm data.Φ) : PreShape data.Φ N := by
  have hdeg : data.Φ.natDegree = N + 1 := by rw [data.natDegree_eq, dedekindPsi_prime hp]
  have htopc : data.Φ.coeff (N + 1) = 1 := by
    have := data.monic.coeff_natDegree; rwa [hdeg] at this
  have hdeg' : ∀ k, N + 1 < k → data.Φ.coeff k = 0 := fun k hk =>
    coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hk)
  have htop : ∀ i, (data.Φ.coeff (N + 1)).coeff i = if i = 0 then 1 else 0 := by
    intro i
    rw [htopc, coeff_one]
  refine ⟨hdeg', ?_, htop, ?_⟩
  · intro k i hi
    rw [coeff_symm hsym, hdeg' i hi, coeff_zero]
  · intro k
    rw [coeff_symm hsym, htop]

theorem shape_of_prime {N : ℕ} [NeZero N] (hp : N.Prime) (data : ModularPolynomialData N)
    (hsym : EvalSymm data.Φ) : Shape data.Φ N := by
  have hP := preShape_of_prime hp data hsym
  refine ⟨hP, corner_of_eval hP hp.two_le ?_⟩
  have h := data.eval_eq_zero
  rwa [show evalAtJ = (aeval (R := ℤ) jq).toRingHom from rfl,
    show jqN N = qExpand ℚ N jq from rfl] at h

def G (Φ : ℤ[X][X]) (N : ℕ) {L : Type*} [CommRing L] (σ θ : L) : L :=
  ∑ k ∈ Finset.range (N + 2), ∑ i ∈ Finset.range (N + 2),
    (((Φ.coeff k).coeff i : ℤ) : L) * σ ^ (N * (N + 1) - (i + N * k)) * θ ^ k

theorem map_G (Φ : ℤ[X][X]) (N : ℕ) {L L' : Type*} [CommRing L] [CommRing L']
    (f : L →+* L') (σ θ : L) : f (G Φ N σ θ) = G Φ N (f σ) (f θ) := by
  simp only [G, map_sum, map_mul, map_pow, map_intCast]

theorem subtype_G (Φ : ℤ[X][X]) (N : ℕ) {L : Type*} [CommRing L] (S : Subring L) (σ θ : S) :
    ((G Φ N σ θ : S) : L) = G Φ N (σ : L) (θ : L) :=
  map_G Φ N S.subtype σ θ

theorem clear {Φ : ℤ[X][X]} {N : ℕ} (hS : PreShape Φ N) (hN : 1 ≤ N) {L : Type*} [Field L]
    [Algebra ℤ L] {σ : L} (hσ : σ ≠ 0) (θ : L) :
    σ ^ (N * (N + 1)) * Φ.eval₂ (aeval (R := ℤ) σ⁻¹).toRingHom (θ * σ⁻¹ ^ N) = G Φ N σ θ := by
  rw [eval₂_eq_sum_range' _ hS.natDegree_lt, Finset.mul_sum]
  unfold G
  refine Finset.sum_congr rfl fun k hk => ?_
  have hinner : (aeval (R := ℤ) σ⁻¹).toRingHom (Φ.coeff k)
      = ∑ i ∈ Finset.range (N + 2), (((Φ.coeff k).coeff i : ℤ) : L) * σ⁻¹ ^ i := by
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_def,
      eval₂_eq_sum_range' _ (hS.natDegree_coeff_lt k)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [eq_intCast]
  rw [hinner, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  by_cases hz : (Φ.coeff k).coeff i = 0
  · simp [hz]
  · have hadm : i + N * k ≤ N * (N + 1) := by
      by_contra h
      exact hz (hS.coeff_eq_zero_of_lt hN (Finset.mem_range.mp hi) (Finset.mem_range.mp hk)
        (not_le.mp h))
    obtain ⟨e, he⟩ : ∃ e, N * (N + 1) = e + (i + N * k) := ⟨_, (Nat.sub_add_cancel hadm).symm⟩
    rw [he, Nat.add_sub_cancel]
    simp only [inv_pow, mul_pow, ← pow_mul]
    field_simp
    ring

section Newton

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

private theorem lt_of_pow_le {x m : Γ₀} {n a : ℕ} (hm0 : 0 < m) (hm1 : m < 1) (hna : n < a)
    (h : x ^ n ≤ m ^ a) : x < m := by
  by_contra hle
  push Not at hle
  have h1 : m ^ n ≤ x ^ n := pow_le_pow_left₀ zero_le' hle n
  have h2 : m ^ a < m ^ n := pow_lt_pow_right_of_lt_one₀ hm0 hm1 hna
  exact lt_irrefl _ (lt_of_lt_of_le h2 (h1.trans h))

end Newton

theorem newton {Φ : ℤ[X][X]} {N : ℕ} (hS : Shape Φ N) (hN : 2 ≤ N) {L : Type*} [Field L]
    (O : ValuationSubring L) {σ θ : L} (hθ0 : θ ≠ 0)
    (hσ : O.valuation σ < 1) (hθ : O.valuation θ < 1) (hG : G Φ N σ θ = 0) :
    O.valuation (σ ^ (N ^ 2 - 1) - θ ^ N) < O.valuation (θ ^ N) := by
  set v := O.valuation with hv
  have hN1 : 1 ≤ N := by omega
  have hsq : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ hN1
  set M := N ^ 2 - 1 with hM
  have hMN : M + 1 = N ^ 2 := Nat.sub_add_cancel hsq
  have hMNz : (M : ℤ) + 1 = (N : ℤ) ^ 2 := by exact_mod_cast hMN
  have hM1 : 1 ≤ M := by
    have : 2 ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hN 2
    omega

  let g : ℕ × ℕ → L := fun p =>
    (((Φ.coeff p.2).coeff p.1 : ℤ) : L) * σ ^ (N * (N + 1) - (p.1 + N * p.2)) * θ ^ p.2
  set S := Finset.range (N + 2) ×ˢ Finset.range (N + 2) with hSdef
  have hGsum : G Φ N σ θ = ∑ p ∈ S, g p := by
    rw [G, Finset.sum_product_right]
  have hc1 : ((N + 1, 0) : ℕ × ℕ) ∈ S := by
    simp [S]
  have hc2 : ((N, N) : ℕ × ℕ) ∈ S.erase (N + 1, 0) := by
    simp [S]
  set S' := (S.erase (N + 1, 0)).erase (N, N) with hS'def
  have hsplit : ∑ p ∈ S, g p = g (N + 1, 0) + (g (N, N) + ∑ p ∈ S', g p) := by
    rw [Finset.add_sum_erase _ _ hc2, Finset.add_sum_erase _ _ hc1]
  have hex1 : N * (N + 1) - (N + 1 + N * 0) = M := by
    have h1 : N + 1 + N * 0 ≤ N * (N + 1) := by nlinarith
    zify [h1, hsq]
    linear_combination (-1 : ℤ) * hMNz
  have hex2 : N * (N + 1) - (N + N * N) = 0 := by
    apply Nat.sub_eq_zero_of_le
    nlinarith
  have hg1 : g (N + 1, 0) = σ ^ M := by
    simp only [g]
    rw [hS.right 0, hex1]
    simp
  have hg2 : g (N, N) = -θ ^ N := by
    simp only [g]
    rw [hS.corner, hex2]
    simp
  have hrest : σ ^ M - θ ^ N = -∑ p ∈ S', g p := by
    have h := hG
    rw [hGsum, hsplit, hg1, hg2] at h
    linear_combination h

  have hvθ0 : v θ ≠ 0 := (Valuation.ne_zero_iff v).mpr hθ0
  have hvθpos : 0 < v θ := zero_lt_iff.mpr hvθ0
  set Mx := max (v σ ^ M) (v θ ^ N) with hMx
  have hMxpos : 0 < Mx := lt_max_of_lt_right (pow_pos hvθpos N)
  have hMx0 : Mx ≠ 0 := hMxpos.ne'
  have hMx1 : Mx < 1 :=
    max_lt (pow_lt_one₀ zero_le' hσ (by omega)) (pow_lt_one₀ zero_le' hθ (by omega))
  have hσM : v σ ^ M ≤ Mx := le_max_left _ _
  have hθN : v θ ^ N ≤ Mx := le_max_right _ _
  have hvσ1 : v σ ≤ 1 := hσ.le
  have hvθ1 : v θ ≤ 1 := hθ.le

  have hterm : ∀ p ∈ S', v (g p) < Mx := by
    rintro ⟨i, k⟩ hp
    simp only [S', S, Finset.mem_erase, Finset.mem_product, Finset.mem_range, Prod.mk.injEq,
      ne_eq] at hp
    obtain ⟨hpNN, hpN1, hi, hk⟩ := hp
    by_cases hz : (Φ.coeff k).coeff i = 0
    · simp only [g, hz, Int.cast_zero, zero_mul, map_zero]
      exact hMxpos
    have hφ : v (((Φ.coeff k).coeff i : ℤ) : L) ≤ 1 :=
      (O.valuation_le_one_iff _).mpr (intCast_mem O _)

    have hvg : ∀ e : ℕ, v ((((Φ.coeff k).coeff i : ℤ) : L) * σ ^ e * θ ^ k)
        ≤ v σ ^ e * v θ ^ k := by
      intro e
      rw [map_mul, map_mul, map_pow, map_pow]
      calc v (((Φ.coeff k).coeff i : ℤ) : L) * v σ ^ e * v θ ^ k
          ≤ 1 * v σ ^ e * v θ ^ k := by gcongr
        _ = v σ ^ e * v θ ^ k := by rw [one_mul]
    rcases Nat.lt_or_ge k N with hkN | hkN
    · rcases Nat.eq_zero_or_pos k with rfl | hk0
      ·
        have hiN : i ≤ N := by
          by_contra h
          exact hpN1 ⟨by omega, rfl⟩
        have hex : N * (N + 1) - (i + N * 0) = M + (N + 1 - i) := by
          have h1 : i + N * 0 ≤ N * (N + 1) := by nlinarith
          have h2 : i ≤ N + 1 := by omega
          zify [h1, h2, hsq]
          linear_combination (-1 : ℤ) * hMNz
        simp only [g]
        rw [hex]
        rcases eq_or_ne (v σ) 0 with hσz | hσz
        · refine lt_of_le_of_lt (hvg _) ?_
          rw [hσz, zero_pow (by omega), zero_mul]
          exact hMxpos
        · have hvσpos : 0 < v σ := zero_lt_iff.mpr hσz
          have hlt : v σ ^ (M + (N + 1 - i)) * v θ ^ 0 < Mx := by
            rw [pow_zero, mul_one, pow_add]
            calc v σ ^ M * v σ ^ (N + 1 - i) < v σ ^ M * 1 := by
                  gcongr
                  · exact pow_pos hvσpos _
                  · exact pow_lt_one₀ zero_le' hσ (by omega)
              _ ≤ Mx := by rw [mul_one]; exact hσM
          exact lt_of_le_of_lt (hvg _) hlt
      ·
        have hiN : i ≤ N := by
          by_contra h
          obtain rfl : i = N + 1 := by omega
          rw [hS.right] at hz
          simp [hk0.ne'] at hz
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hkN
        set D := d + 1 with hD
        have hND : N = k + D := by omega
        have hex : N * (N + 1) - (i + N * k) = N * D + (N - i) := by
          have h1 : i + N * k ≤ N * (N + 1) := by nlinarith
          zify [h1, hiN]
          have : (N : ℤ) = k + D := by exact_mod_cast hND
          linear_combination (N : ℤ) * this

        have ht : v σ ^ (N * D) * v θ ^ k < Mx := by
          have hpow : (v σ ^ (N * D) * v θ ^ k) ^ (N * M) ≤ Mx ^ (N * M + D) := by
            have e1 : (v σ ^ (N * D)) ^ (N * M) = (v σ ^ M) ^ (N * D * N) := by
              rw [← pow_mul, ← pow_mul]
              congr 1
              ring
            have e2 : (v θ ^ k) ^ (N * M) = (v θ ^ N) ^ (k * M) := by
              rw [← pow_mul, ← pow_mul]
              congr 1
              ring
            have hexp : N * D * N + k * M = N * M + D := by
              zify
              have : (N : ℤ) = k + D := by exact_mod_cast hND
              linear_combination ((k : ℤ) - N) * hMNz + (1 - (N : ℤ) ^ 2) * this
            rw [mul_pow, e1, e2, ← hexp, pow_add]
            exact mul_le_mul' (pow_le_pow_left₀ zero_le' hσM _) (pow_le_pow_left₀ zero_le' hθN _)
          exact lt_of_pow_le hMxpos hMx1 (by omega) hpow
        have hle : v σ ^ (N * D + (N - i)) * v θ ^ k ≤ v σ ^ (N * D) * v θ ^ k := by
          rw [pow_add]
          calc v σ ^ (N * D) * v σ ^ (N - i) * v θ ^ k
              ≤ v σ ^ (N * D) * 1 * v θ ^ k := by
                gcongr
                exact pow_le_one₀ zero_le' hvσ1
            _ = v σ ^ (N * D) * v θ ^ k := by rw [mul_one]
        simp only [g]
        rw [hex]
        exact lt_of_le_of_lt ((hvg _).trans hle) ht
    · rcases Nat.lt_or_ge k (N + 1) with hk1 | hk1
      ·
        obtain rfl : k = N := by omega
        have hiN : i < k := by
          rcases Nat.lt_or_ge i k with h | h
          · exact h
          · exfalso
            rcases Nat.lt_or_ge i (k + 1) with h' | h'
            · exact hpNN ⟨by omega, rfl⟩
            · obtain rfl : i = k + 1 := by omega
              rw [hS.right] at hz
              simp [show k ≠ 0 by omega] at hz
        have hex : k * (k + 1) - (i + k * k) = k - i := by
          have h1 : i + k * k ≤ k * (k + 1) := by nlinarith
          zify [h1, hiN.le]
          ring
        have hlt : v σ ^ (k - i) * v θ ^ k < Mx := by
          calc v σ ^ (k - i) * v θ ^ k < 1 * v θ ^ k := by
                gcongr
                · exact pow_pos hvθpos _
                · exact pow_lt_one₀ zero_le' hσ (by omega)
            _ ≤ Mx := by rw [one_mul]; exact hθN
        simp only [g]
        rw [hex]
        exact lt_of_le_of_lt (hvg _) hlt
      ·
        obtain rfl : k = N + 1 := by omega
        have hi0 : i = 0 := by
          by_contra h
          rw [hS.top] at hz
          simp [h] at hz
        subst hi0
        have hex : N * (N + 1) - (0 + N * (N + 1)) = 0 := by simp
        have hlt : v σ ^ 0 * v θ ^ (N + 1) < Mx := by
          rw [pow_zero, one_mul, pow_succ]
          calc v θ ^ N * v θ < v θ ^ N * 1 := by
                gcongr
                exact pow_pos hvθpos _
            _ ≤ Mx := by rw [mul_one]; exact hθN
        simp only [g]
        rw [hex]
        exact lt_of_le_of_lt (hvg _) hlt
  have hvrest : v (σ ^ M - θ ^ N) < Mx := by
    rw [hrest, Valuation.map_neg]
    exact v.map_sum_lt hMx0 hterm
  rcases le_or_gt (v σ ^ M) (v θ ^ N) with h | h
  · rw [hMx, max_eq_right h] at hvrest
    rwa [map_pow]
  · exfalso
    have h' : v (θ ^ N) < v (σ ^ M) := by rwa [map_pow, map_pow]
    rw [hMx, max_eq_left h.le, Valuation.map_sub_eq_of_lt_left v h', map_pow] at hvrest
    exact lt_irrefl _ hvrest

theorem newton_nonunits {Φ : ℤ[X][X]} {N : ℕ} (hS : Shape Φ N) (hN : 2 ≤ N) {L : Type*}
    [Field L] (O : ValuationSubring L) {σ θ : L} (hθ0 : θ ≠ 0)
    (hσ : σ ∈ O.nonunits) (hθ : θ ∈ O.nonunits) (hG : G Φ N σ θ = 0) :
    σ ^ (N ^ 2 - 1) / θ ^ N - 1 ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hσ hθ ⊢
  have h := newton hS hN O hθ0 hσ hθ hG
  have hθN : θ ^ N ≠ 0 := pow_ne_zero _ hθ0
  have hvθN : O.valuation (θ ^ N) ≠ 0 := (Valuation.ne_zero_iff _).mpr hθN
  rw [show σ ^ (N ^ 2 - 1) / θ ^ N - 1 = (σ ^ (N ^ 2 - 1) - θ ^ N) / θ ^ N by
    field_simp, map_div₀, div_lt_one₀ (zero_lt_iff.mpr hvθN)]
  exact h

theorem key_id₁ {L : Type*} [Field L] {j jN : L} (hj : j ≠ 0) (hjN : jN ≠ 0) {N M : ℕ}
    (hNN : N * N = M + 1) : j / jN ^ N * (jN * j⁻¹ ^ N) ^ N = j⁻¹ ^ M := by
  rw [mul_pow, ← pow_mul, hNN, pow_succ]
  field_simp

theorem key_id₂ {L : Type*} [Field L] {j jN : L} (hj : j ≠ 0) (hjN : jN ≠ 0) {N M : ℕ}
    (hNN : N * N = M + 1) : j⁻¹ ^ M / (jN * j⁻¹ ^ N) ^ N = j / jN ^ N := by
  rw [← key_id₁ hj hjN hNN, mul_div_cancel_right₀]
  exact pow_ne_zero _ (mul_ne_zero hjN (pow_ne_zero _ (inv_ne_zero hj)))

section PlaceAux

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def HV (w : Place K F) (f : F) (a : K) : Prop :=
  f - algebraMap K F a ∈ w.toValuationSubring.nonunits

variable (w : Place K F)

theorem alg_mem (a : K) : algebraMap K F a ∈ w.toValuationSubring := w.algebraMap_mem' a

theorem alg_mem_nonunits_iff (a : K) :
    algebraMap K F a ∈ w.toValuationSubring.nonunits ↔ a = 0 := by
  constructor
  · intro h
    rcases (ValuationSubring.mem_nonunits_iff_or _).mp h with h0 | hinv
    · exact (map_eq_zero _).mp h0
    · exact absurd (by simpa using alg_mem w a⁻¹) hinv
  · rintro rfl
    simp [ZeroMemClass.zero_mem]

theorem mul_mem_nonunits {x y : F} (hx : x ∈ w.toValuationSubring.nonunits)
    (hy : y ∈ w.toValuationSubring) : x * y ∈ w.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  rw [← ValuationSubring.valuation_le_one_iff] at hy
  calc w.toValuationSubring.valuation (x * y)
      = w.toValuationSubring.valuation x * w.toValuationSubring.valuation y := map_mul _ _ _
    _ ≤ w.toValuationSubring.valuation x * 1 := by gcongr
    _ = w.toValuationSubring.valuation x := mul_one _
    _ < 1 := hx

theorem mem_of_ord_pos {f : F} (h : 0 < w.ord f) : f ∈ w.toValuationSubring := by
  have hf : f ≠ 0 := by rintro rfl; simp at h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf hπ
  rw [hu, show w.ord f = (((w.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h.le).symm,
    zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem (π : w.toValuationSubring).2 _)

theorem mem_nonunits_iff_ord_pos {f : F} (hf : f ≠ 0) :
    f ∈ w.toValuationSubring.nonunits ↔ 0 < w.ord f := by
  constructor
  · intro h
    have hmem : f ∈ w.toValuationSubring := w.toValuationSubring.nonunits_subset h
    have h' : ((⟨f, hmem⟩ : w.toValuationSubring) : F) ∈ w.toValuationSubring.nonunits := h
    rw [ValuationSubring.coe_mem_nonunits_iff] at h'
    exact (w.mem_maximalIdeal_iff_ord_pos hf hmem).mp h'
  · intro h
    have hmem : f ∈ w.toValuationSubring := mem_of_ord_pos w h
    have h' := (w.mem_maximalIdeal_iff_ord_pos hf hmem).mpr h
    rw [← ValuationSubring.coe_mem_nonunits_iff] at h'
    exact h'

theorem HV_algebraMap (a : K) : HV w (algebraMap K F a) a := by
  simp [HV, ZeroMemClass.zero_mem]

theorem HV_intCast (n : ℤ) : HV w (n : F) (n : K) := by
  simpa using HV_algebraMap w (n : K)

variable {w}

theorem HV.mem {f : F} {a : K} (h : HV w f a) : f ∈ w.toValuationSubring := by
  have h1 : f - algebraMap K F a ∈ w.toValuationSubring := w.toValuationSubring.nonunits_subset h
  simpa using add_mem h1 (alg_mem w a)

theorem HV.unique {f : F} {a b : K} (ha : HV w f a) (hb : HV w f b) : a = b := by
  have h : algebraMap K F (a - b) ∈ w.toValuationSubring.nonunits := by
    have := sub_mem hb ha
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  exact sub_eq_zero.mp ((alg_mem_nonunits_iff w _).mp h)

theorem HV.add {f g : F} {a b : K} (hf : HV w f a) (hg : HV w g b) :
    HV w (f + g) (a + b) := by
  have := add_mem hf hg
  rw [HV, map_add]
  convert this using 1
  ring

theorem HV.mul {f g : F} {a b : K} (hf : HV w f a) (hg : HV w g b) :
    HV w (f * g) (a * b) := by
  have h1 : (f - algebraMap K F a) * g ∈ w.toValuationSubring.nonunits :=
    mul_mem_nonunits w hf hg.mem
  have h2 : (g - algebraMap K F b) * algebraMap K F a ∈ w.toValuationSubring.nonunits :=
    mul_mem_nonunits w hg (alg_mem w a)
  have := add_mem h1 h2
  rw [HV, map_mul]
  convert this using 1
  ring

theorem HV.pow {f : F} {a : K} (h : HV w f a) : ∀ n : ℕ, HV w (f ^ n) (a ^ n)
  | 0 => by simpa using HV_algebraMap w 1
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact (HV.pow h n).mul h

theorem HV.sum {ι : Type*} (S : Finset ι) {f : ι → F} {g : ι → K}
    (h : ∀ i ∈ S, HV w (f i) (g i)) : HV w (∑ i ∈ S, f i) (∑ i ∈ S, g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using HV_algebraMap w 0
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a S)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem HV.G_val (Φ : ℤ[X][X]) (N : ℕ) {s T : F} {c a : K} (hs : HV w s c) (hT : HV w T a) :
    HV w (G Φ N s T) (G Φ N c a) := by
  unfold G
  refine HV.sum _ fun k _ => HV.sum _ fun i _ => ?_
  exact ((HV_intCast w _).mul (hs.pow _)).mul (hT.pow _)

theorem mem_of_pow_mem (O : ValuationSubring F) {s : F} {M : ℕ} (h : s ^ M ∈ O) (hM : M ≠ 0) :
    s ∈ O := by
  rw [← O.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  by_contra hlt
  push Not at hlt
  exact absurd h (not_le.mpr (one_lt_pow₀ hlt hM))

variable (w)

theorem HV_iff_residue (y : w.toValuationSubring) (b : K) :
    HV w (y : F) b ↔
      IsLocalRing.residue w.toValuationSubring y = algebraMap K w.ResidueField b := by
  rw [show algebraMap K w.ResidueField b
      = IsLocalRing.residue w.toValuationSubring (algebraMap K w.toValuationSubring b) from rfl,
    ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

theorem exists_HV_of_pow [IsAlgClosed K] {x : F} (hx : x ∈ w.toValuationSubring)
    {M : ℕ} (hM : M ≠ 0) {β : K} (h : HV w (x ^ M) β) : ∃ c : K, HV w x c := by
  set xb := IsLocalRing.residue w.toValuationSubring ⟨x, hx⟩ with hxb_def
  have hxb : xb ^ M = algebraMap K w.ResidueField β := by
    rw [hxb_def, ← map_pow]
    exact (HV_iff_residue w _ _).mp (by simpa using h)
  have hint : IsIntegral K xb := ⟨X ^ M - C β, monic_X_pow_sub_C β hM, by simp [hxb]⟩
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one K xb
    (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint))
  exact ⟨c, (HV_iff_residue w _ _).mpr (by rw [← hxb_def]; exact hc.symm)⟩

theorem char0 [IsAlgClosed K] (A : ValuationSubring K) {Φ : ℤ[X][X]} {N : ℕ} (hS : Shape Φ N)
    (hN : 2 ≤ N) {s T T' : F} (hT0 : T ≠ 0) (hG : G Φ N s T = 0)
    (hkey : T' * T ^ N = s ^ (N ^ 2 - 1)) {a τ : A} (ha : a ∈ IsLocalRing.maximalIdeal A)
    (hTa : HV w T (a : K)) (hT'τ : HV w T' (τ : K)) :
    τ - 1 ∈ IsLocalRing.maximalIdeal A ∧
      ∃ c : A, c ∈ IsLocalRing.maximalIdeal A ∧ HV w s (c : K) := by
  set O := w.toValuationSubring with hO
  set M := N ^ 2 - 1 with hM
  have hM0 : M ≠ 0 := by
    have : 2 ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hN 2
    omega
  have hsM : HV w (s ^ M) ((τ : K) * (a : K) ^ N) := by
    rw [← hkey]; exact hT'τ.mul (hTa.pow N)
  have hsmem : s ∈ O := mem_of_pow_mem O hsM.mem hM0
  obtain ⟨c, hc⟩ := exists_HV_of_pow w hsmem hM0 hsM
  have hcM : c ^ M = (τ : K) * (a : K) ^ N := (hc.pow M).unique hsM

  have hGca : G Φ N c (a : K) = 0 := by
    have h1 : HV w (G Φ N s T) (G Φ N c (a : K)) := HV.G_val Φ N hc hTa
    have h2 : HV w (G Φ N s T) 0 := by
      rw [hG]; simpa using HV_algebraMap w 0
    exact h1.unique h2
  have hva : A.valuation (a : K) < 1 := (A.valuation_lt_one_iff a).mp ha
  by_cases ha0 : (a : K) = 0
  ·
    have hc0 : c = 0 := by
      have : c ^ M = 0 := by rw [hcM, ha0, zero_pow (by omega), mul_zero]
      exact pow_eq_zero_iff hM0 |>.mp this
    have hs0 : s ∈ O.nonunits := by simpa [HV, hc0] using hc
    have hT0' : T ∈ O.nonunits := by simpa [HV, ha0] using hTa
    have hnew := newton_nonunits hS hN O hT0 hs0 hT0' hG
    have hT'eq : s ^ (N ^ 2 - 1) / T ^ N = T' := by
      rw [← hM, ← hkey, mul_div_cancel_right₀ _ (pow_ne_zero _ hT0)]
    rw [hT'eq] at hnew
    have h1 : HV w T' 1 := by simpa [HV] using hnew
    have hτ1 : (τ : K) = 1 := hT'τ.unique h1
    have hτ : τ = 1 := Subtype.ext (by simpa using hτ1)
    refine ⟨by rw [hτ, sub_self]; exact zero_mem _, 0, zero_mem _, ?_⟩
    simpa [hc0] using hc
  ·
    have hva0 : A.valuation (a : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr ha0
    have hvcM : A.valuation c ^ M < 1 := by
      rw [← map_pow, hcM, map_mul, map_pow]
      calc A.valuation (τ : K) * A.valuation (a : K) ^ N
          ≤ 1 * A.valuation (a : K) ^ N := by
            gcongr
            exact (A.valuation_le_one_iff _).mpr τ.2
        _ < 1 := by rw [one_mul]; exact pow_lt_one₀ zero_le' hva (by omega)
    have hvc : A.valuation c < 1 := by
      by_contra hge
      push Not at hge
      exact absurd hvcM (not_lt.mpr (one_le_pow₀ hge))
    have hcA : c ∈ A := (A.valuation_le_one_iff c).mp hvc.le
    have hcm : (⟨c, hcA⟩ : A) ∈ IsLocalRing.maximalIdeal A := (A.valuation_lt_one_iff _).mpr hvc
    refine ⟨?_, ⟨c, hcA⟩, hcm, hc⟩
    have hnew := newton hS hN A (σ := c) (θ := (a : K)) ha0 hvc hva hGca
    have heq : c ^ (N ^ 2 - 1) - (a : K) ^ N = ((τ : K) - 1) * (a : K) ^ N := by
      rw [← hM, hcM]; ring
    rw [heq, map_mul, map_pow] at hnew
    have hlt : A.valuation ((τ : K) - 1) < 1 := by
      by_contra hge
      push Not at hge
      have := mul_le_mul_left hge (A.valuation (a : K) ^ N)
      rw [one_mul] at this
      exact absurd (lt_of_le_of_lt this hnew) (lt_irrefl _)
    rw [A.valuation_lt_one_iff]
    push_cast
    exact hlt

end PlaceAux

section Modular

theorem jBar_ne_zero (N : ℕ) [NeZero N] : jBar N ≠ 0 := by
  intro h
  have h1 : ((jBar N : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      LaurentSeries (AlgebraicClosure ℚ)).coeff (-1) = 1 := by
    show (coeffEmb (AlgebraicClosure ℚ) jq).coeff (-1) = 1
    rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]
  rw [h] at h1
  simp at h1

theorem jNBar_ne_zero (N : ℕ) [NeZero N] : jNBar N ≠ 0 := by
  intro h
  have h1 : ((jNBar N : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) :
      LaurentSeries (AlgebraicClosure ℚ)).coeff ((N : ℤ) * (-1)) = 1 := by
    show (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq)).coeff ((N : ℤ) * (-1)) = 1
    rw [coeffEmb_coeff, qExpand_coeff_mul, coeff_jq_neg_one, map_one]
  rw [h] at h1
  simp at h1

theorem coeff_jqModC_neg_one' (K : Type*) [CommRing K] : (jqModC K).coeff (-1 : ℤ) = 1 := by
  rw [jqModC, HahnSeries.coeff_single_mul, one_mul, sub_self,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jNum,
    map_one]

theorem jqModC_ne_zero' (K : Type*) [CommRing K] [Nontrivial K] : jqModC K ≠ 0 := by
  intro h
  have := coeff_jqModC_neg_one' K
  rw [h] at this
  simp at this

theorem jqNModC_ne_zero' (K : Type*) [CommRing K] [Nontrivial K] (N : ℕ) [NeZero N] :
    jqNModC K N ≠ 0 := by
  intro h
  have h1 : (jqNModC K N).coeff ((N : ℤ) * (-1)) = 1 := by
    rw [show jqNModC K N = qExpand K N (jqModC K) from rfl, qExpand_coeff_mul,
      coeff_jqModC_neg_one']
  rw [h] at h1
  simp at h1

theorem barEval_laurent' (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ)
        (coeffEmb (AlgebraicClosure ℚ) jq)).toRingHom
      (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq)) = 0 := by
  have hcomp : ((coeffEmb (AlgebraicClosure ℚ)).comp
      (Polynomial.aeval (R := ℤ) jq).toRingHom)
      = (Polynomial.aeval (R := ℤ) (coeffEmb (AlgebraicClosure ℚ) jq)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [eq_intCast, map_intCast]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Polynomial.aeval_X]
  have h := Polynomial.hom_eval₂ data.Φ (Polynomial.aeval (R := ℤ) jq).toRingHom
    (coeffEmb (AlgebraicClosure ℚ)) (qExpand ℚ N jq)
  have h0 := data.eval_eq_zero
  rw [show evalAtJ = (Polynomial.aeval (R := ℤ) jq).toRingHom from rfl,
    show jqN N = qExpand ℚ N jq from rfl] at h0
  rw [h0, map_zero, hcomp] at h
  exact h.symm

theorem barEval' (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jBar N)).toRingHom (jNBar N) = 0 := by
  have hcomp : (((laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionFieldFull N)).val.toRingHom).comp
      (Polynomial.aeval (R := ℤ) (jBar N)).toRingHom)
      = (Polynomial.aeval (R := ℤ)
          (coeffEmb (AlgebraicClosure ℚ) jq)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [eq_intCast, map_intCast]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Polynomial.aeval_X]
      rfl
  have h := Polynomial.hom_eval₂ data.Φ
    (Polynomial.aeval (R := ℤ) (jBar N)).toRingHom
    ((laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)).val.toRingHom)
    (jNBar N)
  apply Subtype.val_injective
  have h0 : (laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionFieldFull N)).val.toRingHom
      (data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jBar N)).toRingHom (jNBar N)) = 0 := by
    rw [h, hcomp]
    exact barEval_laurent' N data
  simpa using h0

theorem G_jBar_eq_zero {N : ℕ} [NeZero N] (hp : N.Prime) (data : ModularPolynomialData N)
    (hsym : EvalSymm data.Φ) :
    G data.Φ N (jBar N)⁻¹ (jNBar N * (jBar N)⁻¹ ^ N) = 0 := by
  have hS := shape_of_prime hp data hsym
  have hj := jBar_ne_zero N
  have h := clear hS.toPreShape hp.one_lt.le (inv_ne_zero hj) (jNBar N * (jBar N)⁻¹ ^ N)
  have hT : jNBar N * (jBar N)⁻¹ ^ N * (jBar N)⁻¹⁻¹ ^ N = jNBar N := by
    rw [inv_inv, mul_assoc, ← mul_pow, inv_mul_cancel₀ hj, one_pow, mul_one]
  rw [hT, inv_inv, barEval' N data, mul_zero] at h
  exact h.symm

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ : ℕ} [Fact ℓ.Prime] {k : Type*} [Field k]
  [CharP k ℓ] {red : A →+* k} {N : ℕ} [NeZero N]

theorem red_eq_zero_of_mem (fm : FibreModel N A ℓ k red) {a : A}
    (ha : a ∈ IsLocalRing.maximalIdeal A) : red a = 0 := by
  have hker : (⟨constantsHom N A a, fm.constInf_mem a⟩ : fm.BInf) ∈ RingHom.ker fm.piInf := by
    rw [fm.ker_piInf]
    exact Ideal.subset_span ⟨a, ha, rfl⟩
  rw [RingHom.mem_ker, fm.piInf_const] at hker
  exact (map_eq_zero_iff _ (algebraMap k (modularFunctionFieldC k N)).injective).mp hker

end Modular

open IsLocalRing in
set_option synthInstance.maxHeartbeats 1600000 in

theorem mainPrime
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hN : N.Prime)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsym : EvalSymm (dataAll N (dvd_refl N)).Φ)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (fm : FibreModel N A ℓ k red) (cc : fm.CuspChart)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (τ : A)
    (ht : jBar N / jNBar N ^ N ∈ w.toValuationSubring)
    (hpole : ∀ a : A, w.ord (jNBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      (a : AlgebraicClosure ℚ)) ≤ 0)
    (hres : IsLocalRing.residue w.toValuationSubring ⟨_, ht⟩
        = algebraMap (AlgebraicClosure ℚ) w.ResidueField (τ : AlgebraicClosure ℚ))
    (hsmall : ∃ a : A, a ∈ IsLocalRing.maximalIdeal A ∧
      (jNBar N / jBar N ^ N
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
          ∈ w.toValuationSubring.nonunits) :
    ⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
        - algebraMap k (modularFunctionFieldC k N) (red τ) = 0 ∨
    0 < ((fm.spPlace hred dataAll hsep) w).ord
      (⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^
          N
        - algebraMap k (modularFunctionFieldC k N) (red τ)) := by
  set K := AlgebraicClosure ℚ with hKdef
  set Φ := (dataAll N (dvd_refl N)).Φ with hΦ
  have hS : Shape Φ N := shape_of_prime hN _ hsym
  have hN2 : 2 ≤ N := hN.two_le
  have hsq1 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ hN.pos
  have hNN : N * N = (N ^ 2 - 1) + 1 := by rw [Nat.sub_add_cancel hsq1, sq]
  have hj := jBar_ne_zero N
  have hjN := jNBar_ne_zero N

  set s := (jBar N)⁻¹ with hs
  set T := jNBar N * (jBar N)⁻¹ ^ N with hT
  have hTdiv : jNBar N / jBar N ^ N = T := by rw [hT, div_eq_mul_inv, inv_pow]
  have hT0 : T ≠ 0 := mul_ne_zero hjN (pow_ne_zero _ (inv_ne_zero hj))
  have hkey : jBar N / jNBar N ^ N * T ^ N = s ^ (N ^ 2 - 1) := key_id₁ hj hjN hNN
  have hG : G Φ N s T = 0 := G_jBar_eq_zero hN _ hsym

  obtain ⟨a, ha, hTa⟩ := hsmall
  rw [hTdiv] at hTa
  have hT'τ : HV w (jBar N / jNBar N ^ N) (τ : K) := by
    have e : algebraMap K w.ResidueField (τ : K)
        = residue w.toValuationSubring (algebraMap K w.toValuationSubring (τ : K)) := rfl
    rw [e, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
      ← ValuationSubring.coe_mem_nonunits_iff] at hres
    exact hres

  obtain ⟨hτ1, c, hc, hsc⟩ := char0 w A hS hN2 hT0 hG hkey ha hTa hT'τ
  have hredτ : red τ = 1 := by
    have h := red_eq_zero_of_mem fm hτ1
    rwa [map_sub, map_one, sub_eq_zero] at h

  have hpoleJ : ∀ b : A, w.ord (jBar N - algebraMap K (modularFunctionFieldBar N) (b : K)) ≤ 0 := by
    rcases forall_ord_jBar_sub_le_zero_or_exists_ord_pos A N (dataAll N (dvd_refl N)) w with
      h | ⟨_, aN, _, haN⟩
    · exact h
    · exact absurd haN (not_lt.mpr (hpole aN))
  set v' := fm.spPlace hred dataAll hsep w with hv'
  have hsv : (fm.piInf ⟨(jBar N)⁻¹, fm.jInvBar_mem⟩ : modularFunctionFieldC k N)
      ∈ v'.toValuationSubring.nonunits :=
    (fm.piInf_mem_spPlace_nonunits_iff hred dataAll hsep w hpoleJ _).mpr ⟨c, hc, hsc⟩
  have hTv : (fm.piInf ⟨jNBar N * (jBar N)⁻¹ ^ N, cc.tBar_mem⟩ : modularFunctionFieldC k N)
      ∈ v'.toValuationSubring.nonunits :=
    (fm.piInf_mem_spPlace_nonunits_iff hred dataAll hsep w hpoleJ _).mpr ⟨a, ha, hTa⟩
  rw [fm.piInf_jInv] at hsv
  rw [cc.piInf_t] at hTv

  set jt : modularFunctionFieldC k N := ⟨jqModC k, jqModC_mem k N⟩ with hjt
  set jNt : modularFunctionFieldC k N := ⟨jqNModC k N, jqNModC_mem k N⟩ with hjNt
  have hjt0 : jt ≠ 0 := fun h => jqModC_ne_zero' k (congrArg Subtype.val h)
  have hjNt0 : jNt ≠ 0 := fun h => jqNModC_ne_zero' k N (congrArg Subtype.val h)
  have hGt : G Φ N jt⁻¹ (jNt * jt⁻¹ ^ N) = 0 := by
    have h1 : G Φ N (⟨(jBar N)⁻¹, fm.jInvBar_mem⟩ : fm.BInf)
        ⟨jNBar N * (jBar N)⁻¹ ^ N, cc.tBar_mem⟩ = 0 := by
      apply Subtype.val_injective
      rw [subtype_G]
      exact hG
    have h2 := congrArg fm.piInf h1
    rw [map_G, map_zero, fm.piInf_jInv, cc.piInf_t] at h2
    exact h2
  have hTt0 : jNt * jt⁻¹ ^ N ≠ 0 := mul_ne_zero hjNt0 (pow_ne_zero _ (inv_ne_zero hjt0))
  have hnew := newton_nonunits hS hN2 v'.toValuationSubring hTt0 hsv hTv hGt
  rw [key_id₂ hjt0 hjNt0 hNN] at hnew
  rw [hredτ, map_one]
  rcases eq_or_ne (jt / jNt ^ N - 1) 0 with h0 | hne
  · exact Or.inl h0
  · exact Or.inr ((mem_nonunits_iff_ord_pos v' hne).mp hnew)

end SpPlaceD7Prime

open SpPlaceD7Prime in

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hN : N.Prime)
    (hsq : Squarefree N) (hlN : ¬ ℓ ∣ N)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (halpha : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hbeta : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsym : EvalSymm (dataAll N (dvd_refl N)).Φ)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (fm : FibreModel N A ℓ k red) (cc : fm.CuspChart) :
    ∀ (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (τ : A)
      (ht : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          / (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N) ^ N ∈
                  w.toValuationSubring),
    (∀ a : A,
      w.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) →
    IsLocalRing.residue w.toValuationSubring ⟨_, ht⟩
        = algebraMap (AlgebraicClosure ℚ) w.ResidueField (τ : AlgebraicClosure ℚ) →
    (∃ a : A, a ∈ IsLocalRing.maximalIdeal A ∧
      ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N)
          / (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) ^ N
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
          ∈ w.toValuationSubring.nonunits) →
      ⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^ N
          - algebraMap k (modularFunctionFieldC k N) (red τ) = 0 ∨
      0 < ((fm.spPlace hred dataAll hsep) w).ord
        (⟨jqModC k, jqModC_mem k N⟩ / (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) ^
            N
          - algebraMap k (modularFunctionFieldC k N) (red τ)) := by
  intro w τ ht hpole hres hsmall
  exact mainPrime A ℓ N hN k red hred dataAll hsym hsep fm cc w τ ht hpole hres hsmall

end

end S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero_of_t_small_of_prime
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero_of_t_small_of_prime (solution)
