-- Prove2me | solution 1 for MasulloGRH.correspondence_growth_bound
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T17:38:34.117846+00:00
-- url     : https://prove2.me/submissions/c3696679-bffa-4c11-8b1b-ada8f5b28474

import Definitions.Def_MasulloGRH_SchwartzBruhat
import Theorems.Thm_MasulloGRH_isCompact_preimage_of_isOpenMap_of_isCompact_ker
import Theorems.Thm_MasulloGRH_intSubgroup_exists_rounding

set_option autoImplicit false

open Topology Filter

namespace MasulloGRHGrowthAux

open MasulloGRH

section basic
variable {m n r s : ℕ} {d : Fin s → ℕ}

/-- the size of an element of an elementary group -/
def N (e : ElemGroup m n r s d) : ℝ := ‖e.1‖ + ‖e.2.2.1‖

lemma N_nonneg (e : ElemGroup m n r s d) : 0 ≤ N e := by unfold N; positivity

lemma N_add (e f : ElemGroup m n r s d) : N (e + f) ≤ N e + N f := by
  unfold N
  simp only [Prod.fst_add, Prod.snd_add]
  linarith [norm_add_le e.1 f.1, norm_add_le e.2.2.1 f.2.2.1]

lemma N_neg (e : ElemGroup m n r s d) : N (-e) = N e := by
  unfold N; simp

lemma N_sub (e f : ElemGroup m n r s d) : N (e - f) ≤ N e + N f := by
  rw [sub_eq_add_neg]; exact (N_add _ _).trans (by rw [N_neg])

lemma N_zsmul (k : ℤ) (e : ElemGroup m n r s d) : N (k • e) ≤ |(k : ℝ)| * N e := by
  unfold N
  simp only [Prod.smul_fst, Prod.smul_snd]
  have h1 := norm_zsmul_le k e.1
  have h2 := norm_zsmul_le k e.2.2.1
  rw [Int.norm_eq_abs] at h1 h2
  nlinarith

lemma N_sum {ι : Type*} (t : Finset ι) (f : ι → ElemGroup m n r s d) :
    N (∑ i ∈ t, f i) ≤ ∑ i ∈ t, N (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [N]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (N_add _ _).trans (by linarith)

lemma continuous_N : Continuous (N : ElemGroup m n r s d → ℝ) := by
  unfold N; fun_prop

lemma isCompact_ball (hd : ∀ i, d i ≠ 0) (R : ℝ) :
    IsCompact {e : ElemGroup m n r s d | N e ≤ R} := by
  haveI : ∀ i, NeZero (d i) := fun i => ⟨hd i⟩
  have hK : IsCompact (Metric.closedBall (0 : Fin m → ℝ) R ×ˢ
      ((Set.univ : Set (Fin n → UnitAddCircle)) ×ˢ (Metric.closedBall (0 : Fin r → ℤ) R ×ˢ
        (Set.univ : Set ((i : Fin s) → ZMod (d i)))))) :=
    (isCompact_closedBall _ _).prod (isCompact_univ.prod ((isCompact_closedBall _ _).prod
      isCompact_univ))
  refine hK.of_isClosed_subset (isClosed_le continuous_N continuous_const) fun e he => ?_
  have h := N_nonneg e
  simp only [Set.mem_setOf_eq, N] at he
  refine ⟨?_, trivial, ?_, trivial⟩
  · rw [mem_closedBall_zero_iff]; linarith [norm_nonneg e.2.2.1]
  · rw [mem_closedBall_zero_iff]; linarith [norm_nonneg e.1]

end basic

/-- the covering of the identity component -/
def ℒ {m n r s : ℕ} {d : Fin s → ℕ} (y : (Fin m → ℝ) × (Fin n → ℝ)) : ElemGroup m n r s d :=
  (y.1, fun j => ((y.2 j : ℝ) : UnitAddCircle), 0, 0)

section
variable {m n r s : ℕ} {d : Fin s → ℕ}

lemma ℒ_zero : (ℒ (0 : (Fin m → ℝ) × (Fin n → ℝ)) : ElemGroup m n r s d) = 0 := by
  ext <;> simp [ℒ]

lemma ℒ_add (y z : (Fin m → ℝ) × (Fin n → ℝ)) :
    (ℒ (y + z) : ElemGroup m n r s d) = ℒ y + ℒ z := by
  ext <;> simp [ℒ, AddCircle.coe_add]

lemma ℒ_neg (y : (Fin m → ℝ) × (Fin n → ℝ)) :
    (ℒ (-y) : ElemGroup m n r s d) = -ℒ y := by
  ext <;> simp [ℒ, AddCircle.coe_neg]

lemma continuous_ℒ : Continuous (ℒ : (Fin m → ℝ) × (Fin n → ℝ) → ElemGroup m n r s d) := by
  have h : Continuous (fun x : ℝ => (x : UnitAddCircle)) := AddCircle.continuous_mk' 1
  unfold ℒ
  fun_prop

/-- an open subgroup contains the identity component -/
lemma mem_of_isOpen (H : Subgroup (Multiplicative (ElemGroup m n r s d)))
    (hH : IsOpen (H : Set (Multiplicative (ElemGroup m n r s d))))
    (y : (Fin m → ℝ) × (Fin n → ℝ)) : Multiplicative.ofAdd (ℒ y) ∈ H := by
  let S : AddSubgroup ((Fin m → ℝ) × (Fin n → ℝ)) :=
    { carrier := {y | Multiplicative.ofAdd (ℒ y : ElemGroup m n r s d) ∈ H}
      zero_mem' := by simp only [Set.mem_ofPred_eq, ℒ_zero, ofAdd_zero]; exact H.one_mem
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, ℒ_add, ofAdd_add] at *; exact H.mul_mem ha hb
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, ℒ_neg, ofAdd_neg] at *; exact H.inv_mem ha }
  have hSo : IsOpen (S : Set ((Fin m → ℝ) × (Fin n → ℝ))) :=
    hH.preimage (continuous_ofAdd.comp continuous_ℒ)
  have hSc := AddSubgroup.isClosed_of_isOpen S hSo
  have := (convex_univ (𝕜 := ℝ)).isPreconnected.subset_isClopen ⟨hSc, hSo⟩
    ⟨0, Set.mem_univ _, S.zero_mem⟩ (Set.mem_univ y)
  exact this

end


section main

variable (P : Type*) [CommGroup P] [TopologicalSpace P] [IsTopologicalGroup P] [T2Space P]
    [LocallyCompactSpace P] (P₀ : Subgroup P) (hP₀ : IsOpen (P₀ : Set P))
    (m n r s : ℕ) (d : Fin s → ℕ) (hd : ∀ i, d i ≠ 0)
    (α : ↥P₀ →* Multiplicative (ElemGroup m n r s d)) (hαc : Continuous α) (hαo : IsOpenMap α)
    (hαk : IsCompact {x : ↥P₀ | α x = 1})
    (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
    (β : P →* Multiplicative (ElemGroup m' n' r' s' d')) (hβc : Continuous β)

include hP₀ hd hαc hαo hαk hβc in
lemma bound_of_le (R : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ p : P₀,
    N (Multiplicative.toAdd (α p)) ≤ R → N (Multiplicative.toAdd (β p)) ≤ M := by
  haveI : T2Space (Multiplicative (ElemGroup m n r s d)) :=
    inferInstanceAs (T2Space (ElemGroup m n r s d))
  haveI : LocallyCompactSpace P₀ := hP₀.locallyCompactSpace
  have hK := isCompact_preimage_of_isOpenMap_of_isCompact_ker α hαc hαo hαk
    ((isCompact_ball hd R).image continuous_ofAdd)
  obtain ⟨M, hM⟩ := hK.bddAbove_image (f := fun p : P₀ => N (Multiplicative.toAdd (β p)))
    ((continuous_N.comp (continuous_toAdd.comp (hβc.comp continuous_subtype_val))).continuousOn)
  refine ⟨max M 0, le_max_right _ _, fun p hp => le_max_of_le_left (hM ⟨p, ?_, rfl⟩)⟩
  exact ⟨Multiplicative.toAdd (α p), hp, rfl⟩

include hαo in
lemma exists_of_ℒ (y : (Fin m → ℝ) × (Fin n → ℝ)) :
    ∃ p : P₀, α p = Multiplicative.ofAdd (ℒ y) := by
  have := mem_of_isOpen α.range (by rw [MonoidHom.coe_range]; exact hαo.isOpen_range) y
  exact this

include hP₀ hd hαc hαo hαk hβc in
lemma real_step : ∃ M₁ : ℝ, 0 ≤ M₁ ∧ ∀ x : Fin m → ℝ, ∃ p : P₀,
    α p = Multiplicative.ofAdd (x, 0, 0, 0) ∧
      N (Multiplicative.toAdd (β p)) ≤ M₁ * (‖x‖ + 1) := by
  obtain ⟨M₁, hM₁0, hM₁⟩ := bound_of_le P P₀ hP₀ m n r s d hd α hαc hαo hαk m' n' r' s' d' β hβc 1
  refine ⟨M₁, hM₁0, fun x => ?_⟩
  set k := ⌈‖x‖⌉₊ with hk
  have hxk : ‖x‖ ≤ k := Nat.le_ceil _
  have hk1 : (k : ℝ) < ‖x‖ + 1 := Nat.ceil_lt_add_one (norm_nonneg x)
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · have hx : x = 0 := by
      rw [h0, Nat.cast_zero] at hxk; exact norm_le_zero_iff.1 hxk
    refine ⟨1, ?_, ?_⟩
    · rw [map_one, hx]; rfl
    · rw [OneMemClass.coe_one, map_one, toAdd_one]
      simp only [N, Prod.fst_zero, Prod.snd_zero, norm_zero, add_zero]
      positivity
  · have hkpos : (0 : ℝ) < k := by exact_mod_cast hpos
    obtain ⟨p₁, hp₁⟩ := exists_of_ℒ P P₀ m n r s d α hαo (((k : ℝ)⁻¹ • x, 0) :
      (Fin m → ℝ) × (Fin n → ℝ))
    have hN1 : N (Multiplicative.toAdd (α p₁)) ≤ 1 := by
      rw [hp₁, toAdd_ofAdd]
      simp only [N, ℒ, norm_zero, add_zero, norm_smul, norm_inv, Real.norm_natCast]
      rw [inv_mul_le_iff₀ hkpos, mul_one]; exact hxk
    have hb := hM₁ p₁ hN1
    refine ⟨p₁ ^ k, ?_, ?_⟩
    · rw [map_pow, hp₁]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_ofAdd, toAdd_ofAdd]
      ext
      · simp only [ℒ, Prod.smul_fst, Pi.smul_apply, nsmul_eq_mul, smul_eq_mul]
        field_simp
      · simp [ℒ]
      · simp [ℒ]
      · simp [ℒ]
    · rw [SubmonoidClass.coe_pow, map_pow, toAdd_pow, ← natCast_zsmul]
      calc N ((k : ℤ) • Multiplicative.toAdd (β p₁)) ≤ |((k : ℤ) : ℝ)| * N (Multiplicative.toAdd (β p₁)) :=
            N_zsmul _ _
        _ = k * N (Multiplicative.toAdd (β p₁)) := by
            rw [Int.cast_natCast, abs_of_nonneg hkpos.le]
        _ ≤ (‖x‖ + 1) * M₁ := mul_le_mul hk1.le hb (N_nonneg _) (by positivity)
        _ = M₁ * (‖x‖ + 1) := mul_comm _ _

include hP₀ hd hαc hαo hαk hβc in
lemma torus_step : ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ z : Fin n → UnitAddCircle, ∃ p : P₀,
    α p = Multiplicative.ofAdd (0, z, 0, 0) ∧ N (Multiplicative.toAdd (β p)) ≤ M₀ := by
  obtain ⟨M₀, hM₀0, hM₀⟩ := bound_of_le P P₀ hP₀ m n r s d hd α hαc hαo hαk m' n' r' s' d' β hβc 0
  refine ⟨M₀, hM₀0, fun z => ?_⟩
  obtain ⟨p, hp⟩ := exists_of_ℒ P P₀ m n r s d α hαo ((0, fun j => (z j).out) :
      (Fin m → ℝ) × (Fin n → ℝ))
  have he : (ℒ ((0, fun j => (z j).out) : (Fin m → ℝ) × (Fin n → ℝ)) : ElemGroup m n r s d) =
      (0, z, 0, 0) := by
    ext
    · rfl
    · simp only [ℒ]; exact QuotientAddGroup.out_eq' _
    · rfl
    · rfl
  rw [he] at hp
  refine ⟨p, hp, hM₀ p ?_⟩
  rw [hp, toAdd_ofAdd]
  simp [N]

include hP₀ hd hαc hαo hαk hβc in
lemma discrete_step : ∃ A B : ℝ, ∀ (p : P₀) (a : Fin r → ℤ) (f : (i : Fin s) → ZMod (d i)),
    α p = Multiplicative.ofAdd (0, 0, a, f) →
      N (Multiplicative.toAdd (β p)) ≤ A * ‖a‖ + B := by
  let L : AddSubgroup (Fin r → ℤ) :=
    { carrier := {a | ∃ p : P₀, ∃ f, α p = Multiplicative.ofAdd (0, 0, a, f)}
      zero_mem' := ⟨1, 0, by rw [map_one]; rfl⟩
      add_mem' := fun {a b} ⟨p, f, hp⟩ ⟨q, g, hq⟩ => ⟨p * q, f + g, by
        rw [map_mul, hp, hq, ← ofAdd_add]; congr 1; ext <;> simp⟩
      neg_mem' := fun {a} ⟨p, f, hp⟩ => ⟨p⁻¹, -f, by
        rw [map_inv, hp, ← ofAdd_neg]; congr 1; ext <;> simp⟩ }
  obtain ⟨ι, _, b, K, R₀, hbL, hround⟩ := intSubgroup_exists_rounding L
  choose pb fb hpb using hbL
  obtain ⟨M₂, hM₂0, hM₂⟩ := bound_of_le P P₀ hP₀ m n r s d hd α hαc hαo hαk m' n' r' s' d' β hβc R₀
  obtain ⟨S, hSdef⟩ : ∃ S, S = ∑ i, N (Multiplicative.toAdd (β (pb i))) := ⟨_, rfl⟩
  have hS : 0 ≤ S := hSdef ▸ Finset.sum_nonneg fun i _ => N_nonneg _
  refine ⟨K * S, M₂ + S, fun p a f hp => ?_⟩
  obtain ⟨k, hk, hkr⟩ := hround a ⟨p, f, hp⟩
  obtain ⟨q, hq⟩ : ∃ q, q = p * (∏ i, pb i ^ k i)⁻¹ := ⟨_, rfl⟩
  have hαq : Multiplicative.toAdd (α q) =
      (0, 0, a - ∑ i, k i • b i, f - ∑ i, k i • fb i) := by
    rw [hq, map_mul, map_inv, map_prod, toAdd_mul, toAdd_inv, toAdd_prod, hp, toAdd_ofAdd]
    simp only [map_zpow, toAdd_zpow, hpb, toAdd_ofAdd]
    have e : ∀ x, k x • ((0, 0, b x, fb x) : ElemGroup m n r s d) = (0, 0, k x • b x, k x • fb x) :=
      fun x => by simp only [Prod.smul_mk, smul_zero]
    rw [Finset.sum_congr rfl fun x _ => e x]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · simp only [Prod.fst_add, Prod.fst_neg, Prod.fst_sum]; simp
    · simp only [Prod.snd_add, Prod.fst_add, Prod.snd_neg, Prod.fst_neg, Prod.snd_sum, Prod.fst_sum]
      simp
    · simp only [Prod.snd_add, Prod.fst_add, Prod.snd_neg, Prod.fst_neg, Prod.snd_sum, Prod.fst_sum]
      abel
    · simp only [Prod.snd_add, Prod.snd_neg, Prod.snd_sum]
      abel
  have hNq : N (Multiplicative.toAdd (α q)) ≤ R₀ := by
    rw [hαq]; simpa [N] using hkr
  have hbq := hM₂ q hNq
  have hpq : p = q * ∏ i, pb i ^ k i := by rw [hq, inv_mul_cancel_right]
  let βs := β.comp P₀.subtype
  have hβp : Multiplicative.toAdd (βs p) =
      Multiplicative.toAdd (βs q) + ∑ i, k i • Multiplicative.toAdd (βs (pb i)) := by
    conv_lhs => rw [hpq]
    rw [map_mul, toAdd_mul, map_prod, toAdd_prod]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zpow, toAdd_zpow]
  show N (Multiplicative.toAdd (βs p)) ≤ _
  rw [hβp]
  calc N (Multiplicative.toAdd (βs q) + ∑ i, k i • Multiplicative.toAdd (βs (pb i)))
      ≤ N (Multiplicative.toAdd (βs q)) + ∑ i, N (k i • Multiplicative.toAdd (βs (pb i))) :=
        (N_add _ _).trans (add_le_add le_rfl (N_sum _ _))
    _ ≤ M₂ + ∑ i, (K * ‖a‖ + 1) * N (Multiplicative.toAdd (β (pb i))) := by
        refine add_le_add hbq (Finset.sum_le_sum fun i _ => (N_zsmul _ _).trans ?_)
        exact mul_le_mul_of_nonneg_right (hk i) (N_nonneg _)
    _ = K * S * ‖a‖ + (M₂ + S) := by
        rw [← Finset.mul_sum, ← hSdef]; ring

include hP₀ hd hαc hαo hαk hβc in
theorem main : ∃ A B : ℝ, ∀ p : P₀,
    N (Multiplicative.toAdd (β p)) ≤ A * N (Multiplicative.toAdd (α p)) + B := by
  obtain ⟨M₁, hM₁0, hreal⟩ := real_step P P₀ hP₀ m n r s d hd α hαc hαo hαk m' n' r' s' d' β hβc
  obtain ⟨M₀, hM₀0, htor⟩ := torus_step P P₀ hP₀ m n r s d hd α hαc hαo hαk m' n' r' s' d' β hβc
  obtain ⟨A, B, hdisc⟩ := discrete_step P P₀ hP₀ m n r s d hd α hαc hαo hαk m' n' r' s' d' β hβc
  refine ⟨M₁ + |A|, B + M₁ + M₀, fun p => ?_⟩
  rcases he : Multiplicative.toAdd (α p) with ⟨x, z, a, f⟩
  obtain ⟨pr, hpr, hbr⟩ := hreal x
  obtain ⟨pt, hpt, hbt⟩ := htor z
  have hd' : α (p * (pr * pt)⁻¹) = Multiplicative.ofAdd (0, 0, a, f) := by
    rw [map_mul, map_inv, map_mul, hpr, hpt]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_mul, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd, he]
    ext <;> simp
  have hbd := hdisc _ a f hd'
  let βs := β.comp P₀.subtype
  have hsplit : Multiplicative.toAdd (βs p) = Multiplicative.toAdd (βs (p * (pr * pt)⁻¹)) +
      Multiplicative.toAdd (βs pr) + Multiplicative.toAdd (βs pt) := by
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]; abel
  show N (Multiplicative.toAdd (βs p)) ≤ _
  rw [hsplit]
  have hNa : N (x, z, a, f) = ‖x‖ + ‖a‖ := rfl
  rw [hNa]
  have h1 := N_add (Multiplicative.toAdd (βs (p * (pr * pt)⁻¹)) + Multiplicative.toAdd (βs pr))
    (Multiplicative.toAdd (βs pt))
  have h2 := N_add (Multiplicative.toAdd (βs (p * (pr * pt)⁻¹))) (Multiplicative.toAdd (βs pr))
  have hbd' : N (Multiplicative.toAdd (βs (p * (pr * pt)⁻¹))) ≤ A * ‖a‖ + B := hbd
  have hbr' : N (Multiplicative.toAdd (βs pr)) ≤ M₁ * (‖x‖ + 1) := hbr
  have hbt' : N (Multiplicative.toAdd (βs pt)) ≤ M₀ := hbt
  have hA : A * ‖a‖ ≤ |A| * ‖a‖ := mul_le_mul_of_nonneg_right (le_abs_self A) (norm_nonneg a)
  nlinarith [norm_nonneg x, norm_nonneg a, abs_nonneg A]

end main

end MasulloGRHGrowthAux

open MasulloGRH in
theorem solution
    (P : Type*) [CommGroup P] [TopologicalSpace P] [IsTopologicalGroup P] [T2Space P]
    [LocallyCompactSpace P] (P₀ : Subgroup P) (hP₀ : IsOpen (P₀ : Set P))
    (m n r s : ℕ) (d : Fin s → ℕ) (hd : ∀ i, d i ≠ 0)
    (α : ↥P₀ →* Multiplicative (ElemGroup m n r s d)) (hαc : Continuous α) (hαo : IsOpenMap α)
    (hαk : IsCompact {x : ↥P₀ | α x = 1})
    (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
    (β : P →* Multiplicative (ElemGroup m' n' r' s' d')) (hβc : Continuous β) :
    ∃ A B : ℝ, ∀ p : P₀,
      ‖(Multiplicative.toAdd (β p)).1‖ + ‖(Multiplicative.toAdd (β p)).2.2.1‖ ≤
        A * (‖(Multiplicative.toAdd (α p)).1‖ + ‖(Multiplicative.toAdd (α p)).2.2.1‖) + B :=
  MasulloGRHGrowthAux.main P P₀ hP₀ m n r s d hd α hαc hαo hαk m' n' r' s' d' β hβc
