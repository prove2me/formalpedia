-- Prove2me | solution 1 for MvPolynomial.relation_mem_span_of_linear_of_forall_relation_modulo_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/81665342-1384-5e09-a6f6-ae57d5732726

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_relation_mem_span_of_linear_of_forall_relation_modulo_mem_span

set_option autoImplicit false

namespace GotzRegC

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {n : ℕ}

theorem decompose_eq (q : MvPolynomial (Fin (n + 1)) K) (d : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) K) q d : MvPolynomial (Fin (n + 1)) K) =
      homogeneousComponent d q :=
  MvPolynomial.decomposition.decompose'_apply q d

theorem homogeneousComponent_mul_add {G : MvPolynomial (Fin (n + 1)) K} {m : ℕ} (hG : G.IsHomogeneous m)
    (a : MvPolynomial (Fin (n + 1)) K) (d : ℕ) :
    homogeneousComponent (m + d) (a * G) = homogeneousComponent d a * G := by
  have := DirectSum.coe_decompose_mul_of_right_mem_of_le (𝒜 := homogeneousSubmodule (Fin (n + 1)) K)
    (a := a) (show G ∈ homogeneousSubmodule (Fin (n + 1)) K m from hG) (Nat.le_add_right m d)
  rw [decompose_eq, decompose_eq, Nat.add_sub_cancel_left] at this
  exact this

theorem homogeneousComponent_mul_of_lt {G : MvPolynomial (Fin (n + 1)) K} {m : ℕ} (hG : G.IsHomogeneous m)
    (a : MvPolynomial (Fin (n + 1)) K) {d : ℕ} (hd : d < m) :
    homogeneousComponent d (a * G) = 0 := by
  have := DirectSum.coe_decompose_mul_of_right_mem_of_not_le (𝒜 := homogeneousSubmodule (Fin (n + 1)) K)
    (a := a) (show G ∈ homogeneousSubmodule (Fin (n + 1)) K m from hG) (Nat.not_le.mpr hd)
  rw [decompose_eq] at this
  exact this

theorem isHomogeneous_of_linear_mul {ℓ w : MvPolynomial (Fin (n + 1)) K} (hℓ : ℓ.IsHomogeneous 1)
    (hℓ0 : ℓ ≠ 0) {N : ℕ} (h : (ℓ * w).IsHomogeneous (N + 1)) : w.IsHomogeneous N := by
  intro μ hμ
  by_contra hne

  set e := μ.degree with he
  have hcomp : homogeneousComponent e w ≠ 0 := by
    intro h0
    have := congrArg (coeff μ) h0
    rw [coeff_homogeneousComponent, if_pos rfl, coeff_zero] at this
    exact hμ this
  have h1 : homogeneousComponent (1 + e) (w * ℓ) = homogeneousComponent e w * ℓ :=
    homogeneousComponent_mul_add hℓ w e
  have h2 : homogeneousComponent (1 + e) (w * ℓ) = 0 := by
    rw [mul_comm w ℓ, homogeneousComponent_of_mem (show ℓ * w ∈ homogeneousSubmodule (Fin (n + 1)) K (N + 1)
      from h), if_neg]
    intro h12
    apply hne
    change (Finsupp.weight 1) μ = N
    have : μ.degree = N := by omega
    rw [← this, Finsupp.degree_eq_weight_one]; rfl
  rw [h2] at h1
  exact hcomp ((mul_eq_zero.mp h1.symm).resolve_right hℓ0)

theorem eq_zero_of_linear_mul {ℓ w : MvPolynomial (Fin (n + 1)) K} (hℓ : ℓ.IsHomogeneous 1)
    (hℓ0 : ℓ ≠ 0) (h : (ℓ * w).IsHomogeneous 0) : w = 0 := by
  have h0 : homogeneousComponent 0 (w * ℓ) = 0 := homogeneousComponent_mul_of_lt hℓ w Nat.zero_lt_one
  have h1 : homogeneousComponent 0 (w * ℓ) = w * ℓ := by
    rw [homogeneousComponent_of_mem (show w * ℓ ∈ homogeneousSubmodule (Fin (n + 1)) K 0 by
      rw [mul_comm]; exact h), if_pos rfl]
  rw [h1] at h0
  exact (mul_eq_zero.mp h0).resolve_right hℓ0

theorem exists_hom_coeffs {g : ℕ} (F : Fin g → MvPolynomial (Fin (n + 1)) K) {m : ℕ}
    (hF : ∀ i, (F i).IsHomogeneous m) {p : MvPolynomial (Fin (n + 1)) K} {k : ℕ}
    (hp : p.IsHomogeneous (m + k)) (h : p ∈ Ideal.span (Set.range F)) :
    ∃ c : Fin g → MvPolynomial (Fin (n + 1)) K, (∀ i, (c i).IsHomogeneous k) ∧ ∑ i, c i * F i = p := by
  obtain ⟨c₀, hc₀⟩ := Ideal.mem_span_range_iff_exists_fun.mp h
  refine ⟨fun i => homogeneousComponent k (c₀ i), fun i => homogeneousComponent_isHomogeneous _ _, ?_⟩
  calc ∑ i, homogeneousComponent k (c₀ i) * F i = ∑ i, homogeneousComponent (m + k) (c₀ i * F i) :=
        Finset.sum_congr rfl fun i _ => (homogeneousComponent_mul_add (hF i) (c₀ i) k).symm
    _ = homogeneousComponent (m + k) p := by rw [← map_sum, hc₀]
    _ = p := by
        rw [homogeneousComponent_of_mem (show p ∈ homogeneousSubmodule (Fin (n + 1)) K (m + k) from hp), if_pos rfl]

theorem exists_hom_coeffs_span {g : ℕ} {T : Set (Fin g → MvPolynomial (Fin (n + 1)) K)}
    (deg : (Fin g → MvPolynomial (Fin (n + 1)) K) → ℕ) (hT : ∀ τ ∈ T, ∀ i, (τ i).IsHomogeneous (deg τ))
    {c : Fin g → MvPolynomial (Fin (n + 1)) K} {d : ℕ} (hc : ∀ i, (c i).IsHomogeneous d)
    (h : c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K) T) :
    ∃ (N : ℕ) (τ : Fin N → (Fin g → MvPolynomial (Fin (n + 1)) K)) (a : Fin N → MvPolynomial (Fin (n + 1)) K),
      (∀ j, τ j ∈ T) ∧ (∀ j, deg (τ j) ≤ d → (a j).IsHomogeneous (d - deg (τ j))) ∧
      (∀ j, d < deg (τ j) → a j = 0) ∧ c = ∑ j, a j • τ j := by
  classical
  obtain ⟨N, f, gs, hsum⟩ := Submodule.mem_span_set'.mp h
  refine ⟨N, fun j => (gs j : Fin g → MvPolynomial (Fin (n + 1)) K),
    fun j => if deg (gs j : Fin g → MvPolynomial (Fin (n + 1)) K) ≤ d then
      homogeneousComponent (d - deg (gs j : Fin g → MvPolynomial (Fin (n + 1)) K)) (f j) else 0,
    fun j => (gs j).2, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · simp only [if_pos hj]; exact homogeneousComponent_isHomogeneous _ _
  · simp only [if_neg (Nat.not_le.mpr hj)]
  · funext i
    have hci : c i = homogeneousComponent d (c i) := by
      rw [homogeneousComponent_of_mem (show c i ∈ homogeneousSubmodule (Fin (n + 1)) K d from hc i), if_pos rfl]
    rw [hci, ← hsum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : deg (gs j : Fin g → MvPolynomial (Fin (n + 1)) K) ≤ d
    · rw [if_pos hj]
      have := homogeneousComponent_mul_add (hT _ (gs j).2 i) (f j) (d - deg (gs j : Fin g → _))
      rw [Nat.add_sub_cancel' hj] at this
      exact this
    · rw [if_neg hj, zero_mul]
      exact homogeneousComponent_mul_of_lt (hT _ (gs j).2 i) (f j) (Nat.not_le.mp hj)

theorem exists_eq_sum_X_mul (k : ℕ) (g : MvPolynomial (Fin (n + 1)) K) (hg : g.IsHomogeneous (k + 1)) :
    ∃ q : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K, (∀ i, (q i).IsHomogeneous k) ∧ g = ∑ i, X i * q i := by
  classical
  have hg' : g ∈ (Submodule.span K ((fun μ : Fin (n + 1) →₀ ℕ => monomial μ (1 : K)) ''
      {μ : Fin (n + 1) →₀ ℕ | μ.degree = k + 1}) : Submodule K (MvPolynomial (Fin (n + 1)) K)) := by
    have : g ∈ homogeneousSubmodule (Fin (n + 1)) K (k + 1) := hg
    rw [homogeneousSubmodule_eq_finsupp_supported, AddMonoidAlgebra.supported_eq_span_single] at this
    exact this
  clear hg
  induction hg' using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨μ, hμ, rfl⟩ := hx
      have hμ' : μ.degree = k + 1 := hμ
      have hne : μ ≠ 0 := by rintro rfl; simp at hμ'
      obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
        by_contra h; push Not at h; exact hne (Finsupp.ext h)
      have hle : Finsupp.single i 1 ≤ μ := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
      have hdeg : (μ - Finsupp.single i 1).degree = k := by
        have h1 : μ - Finsupp.single i 1 + Finsupp.single i 1 = μ := tsub_add_cancel_of_le hle
        have h2 := congrArg Finsupp.degree h1
        rw [map_add, Finsupp.degree_single, hμ'] at h2
        omega
      refine ⟨Pi.single i (monomial (μ - Finsupp.single i 1) 1), fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj; rw [Pi.single_eq_same]; exact isHomogeneous_monomial _ hdeg
        · rw [Pi.single_eq_of_ne hj]; exact isHomogeneous_zero _ _ _
      · rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
          (fun h => (h (Finset.mem_univ i)).elim), Pi.single_eq_same]
        show (monomial μ (1 : K)) = monomial (Finsupp.single i 1) 1 * monomial (μ - Finsupp.single i 1) 1
        rw [monomial_mul, one_mul, add_tsub_cancel_of_le hle]
  | zero => exact ⟨0, fun _ => isHomogeneous_zero _ _ _, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨q₁, hq₁, rfl⟩ := hx
      obtain ⟨q₂, hq₂, rfl⟩ := hy
      exact ⟨q₁ + q₂, fun i => (hq₁ i).add (hq₂ i), by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, mul_add]⟩
  | smul c x _ hx =>
      obtain ⟨q, hq, rfl⟩ := hx
      refine ⟨fun i => C c * q i, fun i => (hq i).C_mul c, ?_⟩
      rw [smul_eq_C_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_left_comm]

theorem mem_of_forall_mem (I : Ideal (MvPolynomial (Fin (n + 1)) K)) {m : ℕ}
    (h : ∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous m → f ∈ I) :
    ∀ (j : ℕ) (f : MvPolynomial (Fin (n + 1)) K), f.IsHomogeneous (m + j) → f ∈ I
  | 0, f, hf => h f hf
  | j + 1, f, hf => by
      obtain ⟨q, hq, rfl⟩ := exists_eq_sum_X_mul (m + j) f hf
      exact I.sum_mem fun i _ => I.mul_mem_left _ (mem_of_forall_mem I h j (q i) (hq i))

theorem sum_mul_mem_span {g : ℕ} (F : Fin g → MvPolynomial (Fin (n + 1)) K)
    (c : Fin g → MvPolynomial (Fin (n + 1)) K) : ∑ i, c i * F i ∈ Ideal.span (Set.range F) :=
  Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

noncomputable def ev {g : ℕ} (F : Fin g → MvPolynomial (Fin (n + 1)) K) :
    (Fin g → MvPolynomial (Fin (n + 1)) K) →ₗ[MvPolynomial (Fin (n + 1)) K] MvPolynomial (Fin (n + 1)) K where
  toFun v := ∑ i, v i * F i
  map_add' v w := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, add_mul]
  map_smul' r v := by
    rw [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem ev_apply {g : ℕ} (F : Fin g → MvPolynomial (Fin (n + 1)) K) (v : Fin g → MvPolynomial (Fin (n + 1)) K) :
    ev F v = ∑ i, v i * F i := rfl

theorem ev_eq_zero_of_mem_span {g : ℕ} (F : Fin g → MvPolynomial (Fin (n + 1)) K)
    {v : Fin g → MvPolynomial (Fin (n + 1)) K}
    (hv : v ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
      {l : Fin g → MvPolynomial (Fin (n + 1)) K | (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i = 0}) :
    ∑ i, v i * F i = 0 := by
  have hle : Submodule.span (MvPolynomial (Fin (n + 1)) K)
      {l : Fin g → MvPolynomial (Fin (n + 1)) K | (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i = 0} ≤
      LinearMap.ker (ev F) := Submodule.span_le.mpr fun l hl => hl.2
  exact hle hv

theorem main (m g : ℕ) (F : Fin g → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous m) (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    (hcol : ∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous m →
      ℓ * f ∈ Ideal.span (Set.range F) → f ∈ Ideal.span (Set.range F))
    (hrel : ∀ (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K), (∀ i, (c i).IsHomogeneous d) →
      ∑ i, c i * F i ∈ Ideal.span {ℓ} →
      c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
        {l : Fin g → MvPolynomial (Fin (n + 1)) K |
          (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i ∈ Ideal.span {ℓ}}) :
    ∀ (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K), (∀ i, (c i).IsHomogeneous d) →
      ∑ i, c i * F i = 0 →
      c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
        {l : Fin g → MvPolynomial (Fin (n + 1)) K | (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i = 0} := by
  classical
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro c hc hcF

  by_cases hd : d ≤ 1
  · exact Submodule.subset_span ⟨⟨d, hd, hc⟩, hcF⟩
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩

  by_cases hℓ0 : ℓ = 0
  · have hbot : Ideal.span ({ℓ} : Set (MvPolynomial (Fin (n + 1)) K)) = ⊥ := Ideal.span_singleton_eq_bot.mpr hℓ0
    have hset : {l : Fin g → MvPolynomial (Fin (n + 1)) K |
        (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i ∈ Ideal.span {ℓ}} =
        {l : Fin g → MvPolynomial (Fin (n + 1)) K | (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i = 0} := by
      ext l; simp only [Set.mem_setOf_eq, hbot, Ideal.mem_bot]
    have := hrel (e + 2) c hc (by rw [hcF]; exact Ideal.zero_mem _)
    rwa [hset] at this

  have hcT := hrel (e + 2) c hc (by rw [hcF]; exact Ideal.zero_mem _)
  let deg : (Fin g → MvPolynomial (Fin (n + 1)) K) → ℕ := fun l => if ∀ i, (l i).IsHomogeneous 0 then 0 else 1
  have hT : ∀ τ ∈ {l : Fin g → MvPolynomial (Fin (n + 1)) K |
      (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i ∈ Ideal.span {ℓ}}, ∀ i, (τ i).IsHomogeneous (deg τ) := by
    rintro τ ⟨⟨d', hd', hτ⟩, -⟩
    by_cases h0 : ∀ i, (τ i).IsHomogeneous 0
    · simp only [deg, if_pos h0]; exact h0
    · simp only [deg, if_neg h0]
      interval_cases d'
      · exact absurd hτ h0
      · exact hτ
  obtain ⟨N, τ, a, hτT, ha, -, hcsum⟩ := exists_hom_coeffs_span deg hT hc hcT
  have hw : ∀ jj : Fin N, ∃ w, w * ℓ = ∑ i, τ jj i * F i := fun jj => Ideal.mem_span_singleton'.mp (hτT jj).2
  choose w hw using hw
  have hwI : ∀ jj, ℓ * w jj ∈ Ideal.span (Set.range F) := fun jj => by
    rw [mul_comm, hw]; exact sum_mul_mem_span F _

  set L := Submodule.span (MvPolynomial (Fin (n + 1)) K)
    {l : Fin g → MvPolynomial (Fin (n + 1)) K | (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i = 0}
    with hLdef

  have step : ∀ jj, ∃ v : Fin g → MvPolynomial (Fin (n + 1)) K,
      (∀ i, (v i).IsHomogeneous (e + 1)) ∧ a jj • τ jj - ℓ • v ∈ L := by
    intro jj
    by_cases h0 : ∀ i, (τ jj i).IsHomogeneous 0
    ·
      have hdeg : deg (τ jj) = 0 := by simp only [deg, if_pos h0]
      have haj : (a jj).IsHomogeneous (e + 1 + 1) := by
        have := ha jj (by rw [hdeg]; exact Nat.zero_le _); rwa [hdeg, Nat.sub_zero] at this
      have hsum : (ℓ * w jj).IsHomogeneous m := by
        rw [mul_comm, hw]
        exact IsHomogeneous.sum Finset.univ (fun i => τ jj i * F i) m fun i _ => by
          have := (h0 i).mul (hF i); rwa [Nat.zero_add] at this
      rcases Nat.eq_zero_or_eq_succ_pred m with hm | hm
      ·
        rw [hm] at hsum
        have hw0 : w jj = 0 := eq_zero_of_linear_mul hℓ hℓ0 hsum
        refine ⟨0, fun _ => isHomogeneous_zero _ _ _, ?_⟩
        rw [smul_zero, sub_zero]
        refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨0, Nat.zero_le _, h0⟩, ?_⟩)
        rw [← hw, hw0, zero_mul]
      · rw [hm] at hsum
        have hwh : (w jj).IsHomogeneous m.pred := isHomogeneous_of_linear_mul hℓ hℓ0 hsum

        have hXw : ∀ ν, ∃ κ : Fin g → MvPolynomial (Fin (n + 1)) K,
            (∀ i, (κ i).IsHomogeneous 0) ∧ ∑ i, κ i * F i = X ν * w jj := by
          intro ν
          have hXh : (X ν * w jj).IsHomogeneous (m + 0) := by
            have := (isHomogeneous_X K ν).mul hwh; rwa [show 1 + m.pred = m + 0 by omega] at this
          refine exists_hom_coeffs F hF hXh (hcol _ ?_ ?_)
          · exact hXh
          · rw [mul_left_comm]; exact Ideal.mul_mem_left _ _ (hwI jj)
        choose κ hκ hκF using hXw
        obtain ⟨b, hb, hab⟩ := exists_eq_sum_X_mul (e + 1) (a jj) haj
        refine ⟨∑ ν, b ν • κ ν, fun i => ?_, ?_⟩
        · rw [Finset.sum_apply]
          exact IsHomogeneous.sum Finset.univ (fun ν => (b ν • κ ν) i) (e + 1) fun ν _ => by
            simp only [Pi.smul_apply, smul_eq_mul]
            exact (hb ν).mul (hκ ν i)
        ·
          have hid : a jj • τ jj - ℓ • ∑ ν, b ν • κ ν =
              ∑ ν, b ν • ((X ν : MvPolynomial (Fin (n + 1)) K) • τ jj - ℓ • κ ν) := by
            rw [hab, Finset.sum_smul, Finset.smul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun ν _ => ?_
            rw [smul_sub, mul_comm (X ν) (b ν), mul_smul, smul_comm (b ν) ℓ]
          rw [hid]
          refine Submodule.sum_mem _ fun ν _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨1, le_rfl, ?_⟩, ?_⟩)
          · intro i
            rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
            refine ((isHomogeneous_X K ν).mul (h0 i)).sub ?_
            have := hℓ.mul (hκ ν i); exact this
          · calc ∑ i, (X ν • τ jj - ℓ • κ ν) i * F i = X ν * ∑ i, τ jj i * F i - ℓ * ∑ i, κ ν i * F i := by
                  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, sub_mul,
                    mul_assoc, mul_assoc]
              _ = 0 := by rw [← hw, hκF]; ring
    ·
      have hdeg : deg (τ jj) = 1 := by simp only [deg, if_neg h0]
      have h1 : ∀ i, (τ jj i).IsHomogeneous 1 := by have := hT _ (hτT jj); rwa [hdeg] at this
      have haj : (a jj).IsHomogeneous (e + 1) := by
        have := ha jj (by rw [hdeg]; omega); rwa [hdeg, show e + 2 - 1 = e + 1 by omega] at this
      have hsum : (ℓ * w jj).IsHomogeneous (m + 1) := by
        rw [mul_comm, hw]
        exact IsHomogeneous.sum Finset.univ (fun i => τ jj i * F i) (m + 1) fun i _ => by
          have := (h1 i).mul (hF i); rwa [show 1 + m = m + 1 by omega] at this
      have hwh : (w jj).IsHomogeneous (m + 0) := by
        exact isHomogeneous_of_linear_mul hℓ hℓ0 hsum
      obtain ⟨κ, hκ, hκF⟩ := exists_hom_coeffs F hF hwh (hcol _ hwh (hwI jj))
      refine ⟨a jj • κ, fun i => ?_, ?_⟩
      · rw [Pi.smul_apply, smul_eq_mul]
        exact haj.mul (hκ i)
      · have hid : a jj • τ jj - ℓ • (a jj • κ) = a jj • (τ jj - ℓ • κ) := by
          rw [smul_sub, smul_comm ℓ (a jj)]
        rw [hid]
        refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨1, le_rfl, fun i => ?_⟩, ?_⟩)
        · rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          refine (h1 i).sub ?_
          have := hℓ.mul (hκ i); exact this
        · calc ∑ i, (τ jj - ℓ • κ) i * F i = ∑ i, τ jj i * F i - ℓ * ∑ i, κ i * F i := by
                rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, mul_assoc]
            _ = 0 := by rw [← hw, hκF, mul_comm (w jj) ℓ, sub_self]
  choose v hv hvL using step

  set V := ∑ jj, v jj with hVdef
  have hcV : c - ℓ • V ∈ L := by
    have : c - ℓ • V = ∑ jj, (a jj • τ jj - ℓ • v jj) := by
      rw [hcsum, hVdef, Finset.smul_sum, ← Finset.sum_sub_distrib]
    rw [this]; exact Submodule.sum_mem _ fun jj _ => hvL jj
  have hVh : ∀ i, (V i).IsHomogeneous (e + 1) := fun i => by
    rw [hVdef, Finset.sum_apply]; exact IsHomogeneous.sum Finset.univ (fun jj => v jj i) (e + 1) fun jj _ => hv jj i
  have hVrel : ∑ i, V i * F i = 0 := by
    have h1 : ∑ i, (c - ℓ • V) i * F i = 0 := ev_eq_zero_of_mem_span F hcV
    have h2 : ∑ i, (c - ℓ • V) i * F i = ∑ i, c i * F i - ℓ * ∑ i, V i * F i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, mul_assoc]
    rw [h2, hcF, zero_sub, neg_eq_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left hℓ0
  have hVL : V ∈ L := ih (e + 1) (by omega) V hVh hVrel
  have : c = (c - ℓ • V) + ℓ • V := by rw [sub_add_cancel]
  rw [this]
  exact L.add_mem hcV (L.smul_mem ℓ hVL)

end GotzRegC

open MvPolynomial in
theorem solution
    (n m g : ℕ) (K : Type) [Field K] (F : Fin g → MvPolynomial (Fin (n + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous m) (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    (hcol : ∀ f : MvPolynomial (Fin (n + 1)) K, f.IsHomogeneous m →
      ℓ * f ∈ Ideal.span (Set.range F) → f ∈ Ideal.span (Set.range F))
    (hrel : ∀ (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K), (∀ i, (c i).IsHomogeneous d) →
      ∑ i, c i * F i ∈ Ideal.span {ℓ} →
      c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
        {l : Fin g → MvPolynomial (Fin (n + 1)) K |
          (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i ∈ Ideal.span {ℓ}})
    (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K) (hc : ∀ i, (c i).IsHomogeneous d)
    (hcF : ∑ i, c i * F i = 0) :
    c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
      {l : Fin g → MvPolynomial (Fin (n + 1)) K |
        (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧ ∑ i, l i * F i = 0} :=
  GotzRegC.main m g F hF ℓ hℓ hcol hrel d c hc hcF

end S_MvPolynomial_relation_mem_span_of_linear_of_forall_relation_modulo_mem_span
end P2MW
export P2MW.S_MvPolynomial_relation_mem_span_of_linear_of_forall_relation_modulo_mem_span (solution)
