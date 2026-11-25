-- Prove2me | solution 1 for GlobalTheory.blockValue_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:06:13.483446+00:00
-- url     : https://prove2.me/submissions/daf138bc-6b33-48d6-a403-ff8f397c94f3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEq
import Theorems.Thm_GlobalTheory_DetPowPairing_main
import Theorems.Thm_GlobalTheory_DiagBlock_main
import Theorems.Thm_GlobalTheory_UnitCase_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open scoped BigOperators
namespace GlobalTheory.BlockValue
variable {C : Type} [Field C] {σ κ : Type}
end GlobalTheory.BlockValue
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma coeff_mvExp_eq_sum_range_degree_succ (f : MvPowerSeries σ C) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m (_root_.Formalism.IncomingBounds.mvExp f) =
      ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (f ^ k) / (k.factorial : C) :=
  rfl
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma mvExp_zero_unramified_depth : _root_.Formalism.IncomingBounds.mvExp (0 : MvPowerSeries σ C) = 1 := by
  ext m
  rw [coeff_mvExp_eq_sum_range_degree_succ, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [zero_pow hk]
  · intro h
    simp at h
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma coeff_pow_eq_zero_of_degree_lt_unramified_depth (f : MvPowerSeries σ C)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    ∀ (k : ℕ) (m : σ →₀ ℕ), m.degree < k → MvPowerSeries.coeff m (f ^ k) = 0
  | 0, m, h => absurd h (Nat.not_lt_zero _)
  | k + 1, m, h => by
    classical
    rw [pow_succ', MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases hp1 : p.1 = 0
    · rw [hp1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_mul]
    · have h1 : 0 < p.1.degree := Nat.pos_of_ne_zero ((Finsupp.degree_eq_zero_iff _).not.mpr hp1)
      have h2 : m.degree = p.1.degree + p.2.degree := by rw [← hp, map_add]
      rw [coeff_pow_eq_zero_of_degree_lt_unramified_depth f hf k p.2 (by omega), mul_zero]
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma coeff_mvExp_eq_sum_range_of_degree_lt (f : MvPowerSeries σ C)
    (hf : MvPowerSeries.constantCoeff f = 0) (m : σ →₀ ℕ) (N : ℕ) (hN : m.degree < N) :
    MvPowerSeries.coeff m (_root_.Formalism.IncomingBounds.mvExp f) =
      ∑ k ∈ Finset.range N, MvPowerSeries.coeff m (f ^ k) / (k.factorial : C) := by
  rw [coeff_mvExp_eq_sum_range_degree_succ]
  refine Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega) fun k _ hk => ?_
  rw [Finset.mem_range, not_lt] at hk
  rw [coeff_pow_eq_zero_of_degree_lt_unramified_depth f hf k m (by omega), zero_div]
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma coeff_pow_mul_pow_eq_zero_of_degree_lt {f g : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) (hg : MvPowerSeries.constantCoeff g = 0)
    {i j : ℕ} {m : σ →₀ ℕ} (h : m.degree < i + j) :
    MvPowerSeries.coeff m (f ^ i * g ^ j) = 0 := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hd : m.degree = p.1.degree + p.2.degree := by rw [← hp, map_add]
  by_cases h1 : p.1.degree < i
  · rw [coeff_pow_eq_zero_of_degree_lt_unramified_depth f hf i _ h1, zero_mul]
  · rw [coeff_pow_eq_zero_of_degree_lt_unramified_depth g hg j _ (by omega), mul_zero]
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma mvExp_add_unramified_depth [CharZero C] {a b : MvPowerSeries σ C}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    _root_.Formalism.IncomingBounds.mvExp (a + b) = _root_.Formalism.IncomingBounds.mvExp a * _root_.Formalism.IncomingBounds.mvExp b := by
  classical
  ext m
  obtain ⟨N, hN⟩ : ∃ N, N = m.degree + 1 := ⟨_, rfl⟩
  have hfac : ∀ k : ℕ, (k.factorial : C) ≠ 0 := fun k => Nat.cast_ne_zero.2 k.factorial_ne_zero
  have hab : MvPowerSeries.constantCoeff (a + b) = 0 := by rw [map_add, ha, hb, add_zero]
  have hprod : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal m,
      MvPowerSeries.coeff p.1 (_root_.Formalism.IncomingBounds.mvExp a) * MvPowerSeries.coeff p.2 (_root_.Formalism.IncomingBounds.mvExp b) =
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          MvPowerSeries.coeff p.1 (a ^ i) * MvPowerSeries.coeff p.2 (b ^ j) /
            ((i.factorial : C) * (j.factorial : C)) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hd : m.degree = p.1.degree + p.2.degree := by rw [← hp, map_add]
    rw [coeff_mvExp_eq_sum_range_of_degree_lt a ha p.1 N (by omega),
      coeff_mvExp_eq_sum_range_of_degree_lt b hb p.2 N (by omega), Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => div_mul_div_comm _ _ _ _
  rw [MvPowerSeries.coeff_mul, coeff_mvExp_eq_sum_range_of_degree_lt (a + b) hab m N (by omega)]
  calc ∑ k ∈ Finset.range N, MvPowerSeries.coeff m ((a + b) ^ k) / (k.factorial : C)
      = ∑ k ∈ Finset.range N, ∑ i ∈ Finset.range (k + 1),
          MvPowerSeries.coeff m (a ^ i * b ^ (k - i)) /
            ((i.factorial : C) * ((k - i).factorial : C)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [add_pow, map_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have hch : ((k.choose i : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hik).ne'
        rw [← nsmul_eq_mul', map_nsmul, nsmul_eq_mul,
          ← Nat.choose_mul_factorial_mul_factorial hik]
        push_cast
        field_simp [hfac]
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range (N - i),
          MvPowerSeries.coeff m (a ^ i * b ^ j) / ((i.factorial : C) * (j.factorial : C)) :=
        Finset.sum_range_diag_flip N
          (fun i j => MvPowerSeries.coeff m (a ^ i * b ^ j) /
            ((i.factorial : C) * (j.factorial : C)))
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          MvPowerSeries.coeff m (a ^ i * b ^ j) / ((i.factorial : C) * (j.factorial : C)) := by
        refine Finset.sum_congr rfl fun i hi => Finset.sum_subset
          (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega) fun j _ hj => ?_
        rw [Finset.mem_range] at hi
        rw [Finset.mem_range, not_lt] at hj
        rw [coeff_pow_mul_pow_eq_zero_of_degree_lt ha hb (by omega), zero_div]
    _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
          MvPowerSeries.coeff p.1 (_root_.Formalism.IncomingBounds.mvExp a) * MvPowerSeries.coeff p.2 (_root_.Formalism.IncomingBounds.mvExp b) := by
        rw [Finset.sum_congr rfl hprod,
          Finset.sum_comm (s := Finset.HasAntidiagonal.antidiagonal m)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm (s := Finset.HasAntidiagonal.antidiagonal m)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_div, ← MvPowerSeries.coeff_mul]
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma mvExp_sum' [CharZero C] {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ C)
    (h : ∀ i ∈ s, MvPowerSeries.constantCoeff (f i) = 0) :
    _root_.Formalism.IncomingBounds.mvExp (∑ i ∈ s, f i) = ∏ i ∈ s, _root_.Formalism.IncomingBounds.mvExp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvExp_zero_unramified_depth]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      mvExp_add_unramified_depth (h a (Finset.mem_insert_self a s)), ih fun i hi => h i (Finset.mem_insert_of_mem hi)]
    rw [map_sum]
    exact Finset.sum_eq_zero fun i hi => h i (Finset.mem_insert_of_mem hi)
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma onlyIn_one (S : σ → Prop) : _root_.GlobalTheory.BlockValue.OnlyIn S (1 : MvPowerSeries σ C) := by
  classical
  intro m hm x hx
  have h0 : m = 0 := by
    by_contra h
    exact hm (by simp [MvPowerSeries.coeff_one, h])
  subst h0
  simp at hx
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma onlyIn_mul {S : σ → Prop} {f g : MvPowerSeries σ C} (hf : _root_.GlobalTheory.BlockValue.OnlyIn S f)
    (hg : _root_.GlobalTheory.BlockValue.OnlyIn S g) : _root_.GlobalTheory.BlockValue.OnlyIn S (f * g) := by
  classical
  intro m hm x hx
  rw [MvPowerSeries.coeff_mul] at hm
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  subst hp
  rcases Finset.mem_union.1 (Finsupp.support_add hx) with h | h
  · exact hf _ (left_ne_zero_of_mul hne) x h
  · exact hg _ (right_ne_zero_of_mul hne) x h
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma onlyIn_pow {S : σ → Prop} {f : MvPowerSeries σ C} (hf : _root_.GlobalTheory.BlockValue.OnlyIn S f)
    (k : ℕ) : _root_.GlobalTheory.BlockValue.OnlyIn S (f ^ k) := by
  induction k with
  | zero => simpa using onlyIn_one S
  | succ k ih => rw [pow_succ]; exact onlyIn_mul ih hf
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma onlyIn_mvExp {S : σ → Prop} {f : MvPowerSeries σ C}
    (hf : _root_.GlobalTheory.BlockValue.OnlyIn S f) : _root_.GlobalTheory.BlockValue.OnlyIn S (_root_.Formalism.IncomingBounds.mvExp f) := by
  intro m hm
  rw [coeff_mvExp_eq_sum_range_degree_succ] at hm
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  exact onlyIn_pow hf k m fun h => hk (by rw [h, zero_div])
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma onlyIn_sum {S : σ → Prop} {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ C)
    (h : ∀ i ∈ s, _root_.GlobalTheory.BlockValue.OnlyIn S (f i)) :
    _root_.GlobalTheory.BlockValue.OnlyIn S (∑ i ∈ s, f i) := by
  intro m hm
  rw [map_sum] at hm
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  exact h i hi m hne
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma onlyIn_prod {S : σ → Prop} {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ C)
    (h : ∀ i ∈ s, _root_.GlobalTheory.BlockValue.OnlyIn S (f i)) :
    _root_.GlobalTheory.BlockValue.OnlyIn S (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using onlyIn_one S
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact onlyIn_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma lead_zero_one (π : σ → κ) :
    _root_.GlobalTheory.BlockValue.Lead π 0 (1 : MvPowerSeries σ C) := by
  classical
  refine ⟨fun m hm => ?_, by simp⟩
  have h0 : m = 0 := by
    by_contra h
    exact hm (by simp [MvPowerSeries.coeff_one, h])
  subst h0
  simp
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma lead_mapDomain_le_and_eq_of_coeff_ne_zero {π : σ → κ} {d e p q : σ →₀ ℕ} {f g : MvPowerSeries σ C}
    (hf : _root_.GlobalTheory.BlockValue.Lead π d f)
    (hg : _root_.GlobalTheory.BlockValue.Lead π e g)
    (hp : MvPowerSeries.coeff p f ≠ 0) (hq : MvPowerSeries.coeff q g ≠ 0) :
    (d + e).mapDomain π ≤ (p + q).mapDomain π ∧
      ((p + q).mapDomain π ≤ (d + e).mapDomain π → p = d ∧ q = e) := by
  obtain ⟨h1, h2⟩ := hf.1 p hp
  obtain ⟨h3, h4⟩ := hg.1 q hq
  simp only [Finsupp.mapDomain_add]
  refine ⟨add_le_add h1 h3, fun h => ⟨h2 ?_, h4 ?_⟩⟩
  · exact le_of_add_le_add_right (h.trans (add_le_add le_rfl h3))
  · exact le_of_add_le_add_left (h.trans (add_le_add h1 le_rfl))
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma lead_mul' {π : σ → κ} {d e : σ →₀ ℕ} {f g : MvPowerSeries σ C}
    (hf : _root_.GlobalTheory.BlockValue.Lead π d f)
    (hg : _root_.GlobalTheory.BlockValue.Lead π e g) :
    _root_.GlobalTheory.BlockValue.Lead π (d + e) (f * g) := by
  classical
  refine ⟨fun m hm => ?_, ?_⟩
  · rw [MvPowerSeries.coeff_mul] at hm
    obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    subst hp
    obtain ⟨h1, h2⟩ := lead_mapDomain_le_and_eq_of_coeff_ne_zero hf hg (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne)
    refine ⟨h1, fun h => ?_⟩
    obtain ⟨h3, h4⟩ := h2 h
    rw [h3, h4]
  · rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (d, e)]
    · simp [hf.2, hg.2]
    · intro p hp hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_contra H
      obtain ⟨-, h2⟩ := lead_mapDomain_le_and_eq_of_coeff_ne_zero hf hg (left_ne_zero_of_mul H) (right_ne_zero_of_mul H)
      obtain ⟨h3, h4⟩ := h2 (by rw [hp])
      exact hne (Prod.ext h3 h4)
    · intro h
      exfalso
      apply h
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma lead_prod' {π : σ → κ} {ι : Type} (s : Finset ι) (d : ι → σ →₀ ℕ)
    (f : ι → MvPowerSeries σ C) (h : ∀ i ∈ s, _root_.GlobalTheory.BlockValue.Lead π (d i) (f i)) :
    _root_.GlobalTheory.BlockValue.Lead π (∑ i ∈ s, d i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lead_zero_one π
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact lead_mul' (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma lead_pow' {π : σ → κ} {d : σ →₀ ℕ} {f : MvPowerSeries σ C}
    (hf : _root_.GlobalTheory.BlockValue.Lead π d f) (k : ℕ) :
    _root_.GlobalTheory.BlockValue.Lead π (k • d) (f ^ k) := by
  induction k with
  | zero => simpa using lead_zero_one π
  | succ k ih => rw [pow_succ, succ_nsmul]; exact lead_mul' ih hf
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma mapDomain_eq_single_degree_of_const {π : σ → κ} {z : κ} {m : σ →₀ ℕ}
    (h : ∀ x ∈ m.support, π x = z) : m.mapDomain π = Finsupp.single z m.degree := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum,
    Finset.sum_congr rfl (fun x hx => congrArg (fun w => Finsupp.single w (m x)) (h x hx)),
    ← Finsupp.single_finset_sum] <;> rfl
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma lead_single_of_linear_coeff_eq_X {ι : Type} {π : σ → κ} {v : ι → σ} {z : κ}
    (hv : ∀ c, π (v c) = z) {c₀ : ι} {f : MvPowerSeries σ C}
    (hsupp : ∀ m : σ →₀ ℕ, MvPowerSeries.coeff m f ≠ 0 → ∀ x ∈ m.support, ∃ c, x = v c)
    (hlin : ∀ m : σ →₀ ℕ, m.degree ≤ 1 →
      MvPowerSeries.coeff m f = MvPowerSeries.coeff m (MvPowerSeries.X (v c₀))) :
    _root_.GlobalTheory.BlockValue.Lead π (Finsupp.single (v c₀) 1) f := by
  classical
  have hone : MvPowerSeries.coeff (Finsupp.single (v c₀) 1) f = 1 := by
    rw [hlin _ (by simp [Finsupp.degree_single])]
    simp [MvPowerSeries.coeff_X]
  refine ⟨fun m hm => ?_, hone⟩
  have hmap : m.mapDomain π = Finsupp.single z m.degree :=
    mapDomain_eq_single_degree_of_const fun x hx => by
      obtain ⟨c, rfl⟩ := hsupp m hm x hx
      exact hv c
  have hd : (Finsupp.single (v c₀) 1 : σ →₀ ℕ).mapDomain π = Finsupp.single z 1 := by
    rw [Finsupp.mapDomain_single, hv]
  have hpos : m ≠ 0 := by
    rintro rfl
    apply hm
    rw [hlin 0 (by simp)]
    simp [MvPowerSeries.coeff_X]
    exact (Finsupp.single_ne_zero.2 one_ne_zero).symm
  have hdeg : 1 ≤ m.degree := Nat.one_le_iff_ne_zero.2 ((Finsupp.degree_eq_zero_iff m).not.2 hpos)
  rw [hmap, hd]
  refine ⟨by rw [Finsupp.single_le_iff]; simpa using hdeg, fun h => ?_⟩
  rw [Finsupp.single_le_iff, Finsupp.single_eq_same] at h
  rw [hlin m h, MvPowerSeries.coeff_X] at hm
  split_ifs at hm with heq
  · exact heq
  · exact absurd rfl hm
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma lead_zero_mvExp (π : σ → κ) (f : MvPowerSeries σ C) :
    _root_.GlobalTheory.BlockValue.Lead π 0 (_root_.Formalism.IncomingBounds.mvExp f) := by
  refine ⟨fun m _ => ⟨by simp, fun h => ?_⟩, ?_⟩
  · have h0 : m.mapDomain π = 0 := nonpos_iff_eq_zero.mp (by simpa using h)
    have hdeg : (m.mapDomain π).degree = 0 := by rw [h0, map_zero]
    rw [Finsupp.degree_mapDomain] at hdeg
    exact (Finsupp.degree_eq_zero_iff m).1 hdeg
  · rw [coeff_mvExp_eq_sum_range_degree_succ]
    simp
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma mapDomain_sideRow_inl {n : ℕ} (m : _root_.Formalism.IncomingBounds.PVar n →₀ ℕ) (ρ : Fin n) :
    (m.mapDomain (_root_.GlobalTheory.BlockValue.sideRow n)) (Sum.inl ρ) = ∑ c : Fin n, m (Sum.inl (ρ, c)) := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp), Finsupp.finset_sum_apply]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, _root_.GlobalTheory.BlockValue.sideRow, Finsupp.single_apply]
  rw [Finset.sum_eq_single ρ (fun b _ hb => by simp [hb]) (by simp)]
  simp
open scoped BigOperators in
variable {C : Type} [Field C] {σ κ : Type} in
private lemma mapDomain_sideRow_inr {n : ℕ} (m : _root_.Formalism.IncomingBounds.PVar n →₀ ℕ) (ρ : Fin n) :
    (m.mapDomain (_root_.GlobalTheory.BlockValue.sideRow n)) (Sum.inr ρ) = ∑ c : Fin n, m (Sum.inr (ρ, c)) := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_fintype _ _ (by simp), Finsupp.finset_sum_apply]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, _root_.GlobalTheory.BlockValue.sideRow, Finsupp.single_apply]
  rw [Finset.sum_eq_single ρ (fun b _ hb => by simp [hb]) (by simp)]
  simp
end

set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open scoped BigOperators
open scoped BigOperators
variable {C : Type} [Field C] {σ κ : Type}
namespace _root_.GlobalTheory
theorem _root_.solution : _root_.Formalism.L2.FormalSeriesBounds.BiValue := by
  unfold _root_.Formalism.L2.FormalSeriesBounds.BiValue
  intro C _ _ l i n0 n hn hr t t' h1 hB y
  classical
  obtain ⟨-, hR, -, hU⟩ := _root_.GlobalTheory.DiagBlock.main
  unfold _root_.Formalism.UnitaryBoundIntegral.BlockJet at hR
  unfold _root_.Formalism.UnitaryBoundIntegral.RestrictExp at hU
  have hsplit : _root_.Formalism.L2.FormalSeriesBounds.BiF l i n0 n y hr t t' =
      _root_.Formalism.IncomingBounds.mvExp (∑ ρ : Fin n with ρ.val < n0, hr ρ) *
        ∏ ρ : Fin n, (if (ρ : ℕ) < n0 then 1 else t ρ ^ (l ^ i * y) * t' ρ ^ y * _root_.Formalism.IncomingBounds.mvExp (hr ρ)) := by
    unfold _root_.Formalism.L2.FormalSeriesBounds.BiF
    rw [mvExp_sum' _ _ (fun ρ _ => hB.constantCoeff_biadditive_zero ρ), Finset.prod_filter, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    split_ifs <;> ring
  have hres : _root_.Formalism.UnitaryBoundIntegral.restr hn (_root_.Formalism.IncomingBounds.mvExp (∑ ρ : Fin n with ρ.val < n0, hr ρ)) = _root_.Formalism.IncomingBounds.mvExp (_root_.Formalism.IncomingBounds.hP C l i n0 h1) := by
    rw [hU, hB.R3]
  have hG : _root_.GlobalTheory.BlockValue.OnlyIn (fun x => (_root_.Formalism.UnitaryBoundIntegral.rowOf x : ℕ) < n0)
      (_root_.Formalism.IncomingBounds.mvExp (∑ ρ : Fin n with ρ.val < n0, hr ρ)) := by
    refine onlyIn_mvExp (onlyIn_sum _ _ fun ρ hρ => ?_)
    have hrow := hB.biadditive_in_single_variables ρ
    unfold _root_.Formalism.L2.FormalSeriesBounds.InRow at hrow
    intro m hm x hx
    rw [hrow m hm x hx]
    exact (Finset.mem_filter.1 hρ).2
  have hH : _root_.GlobalTheory.BlockValue.OnlyIn (fun x => n0 ≤ (_root_.Formalism.UnitaryBoundIntegral.rowOf x : ℕ))
      (∏ ρ : Fin n, (if (ρ : ℕ) < n0 then 1 else t ρ ^ (l ^ i * y) * t' ρ ^ y * _root_.Formalism.IncomingBounds.mvExp (hr ρ))) := by
    refine onlyIn_prod _ _ fun ρ _ => ?_
    split_ifs with hρ
    · exact onlyIn_one _
    · have hρ' : n0 ≤ (ρ : ℕ) := not_lt.1 hρ
      have ht := hB.diagonal_coordinate_left ρ hρ'
      have ht' := hB.diagonal_coordinate_right ρ hρ'
      have hrow := hB.biadditive_in_single_variables ρ
      unfold _root_.Formalism.L2.FormalSeriesBounds.DiagCoord at ht ht'
      unfold _root_.Formalism.L2.FormalSeriesBounds.InRow at hrow
      refine onlyIn_mul (onlyIn_mul (onlyIn_pow ?_ _) (onlyIn_pow ?_ _)) (onlyIn_mvExp ?_)
      · intro m hm x hx
        obtain ⟨c, rfl⟩ := ht.1 m hm x hx
        exact hρ'
      · intro m hm x hx
        obtain ⟨c, rfl⟩ := ht'.1 m hm x hx
        exact hρ'
      · intro m hm x hx
        rw [hrow m hm x hx]
        exact hρ'
  have hL : _root_.GlobalTheory.BlockValue.Lead (_root_.GlobalTheory.BlockValue.sideRow n) (_root_.Formalism.UnitaryBoundIntegral.diagMon n0 n (l ^ i) y)
      (∏ ρ : Fin n, (if (ρ : ℕ) < n0 then 1 else t ρ ^ (l ^ i * y) * t' ρ ^ y * _root_.Formalism.IncomingBounds.mvExp (hr ρ))) := by
    have hX : _root_.Formalism.UnitaryBoundIntegral.diagMon n0 n (l ^ i) y = ∑ ρ : Fin n, (if (ρ : ℕ) < n0 then 0 else
        Finsupp.single (Sum.inl (ρ, ρ) : _root_.Formalism.IncomingBounds.PVar n) (l ^ i * y) +
          Finsupp.single (Sum.inr (ρ, ρ) : _root_.Formalism.IncomingBounds.PVar n) y) := by
      unfold _root_.Formalism.UnitaryBoundIntegral.diagMon
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      split_ifs <;> first | omega | rfl
    rw [hX]
    refine lead_prod' _ _ _ fun ρ _ => ?_
    split_ifs with hρ
    · exact lead_zero_one _
    · have hρ' : n0 ≤ (ρ : ℕ) := not_lt.1 hρ
      have ht := hB.diagonal_coordinate_left ρ hρ'
      have ht' := hB.diagonal_coordinate_right ρ hρ'
      unfold _root_.Formalism.L2.FormalSeriesBounds.DiagCoord at ht ht'
      have h1 := lead_pow' (lead_single_of_linear_coeff_eq_X (π := _root_.GlobalTheory.BlockValue.sideRow n)
        (z := Sum.inl ρ) (fun c => rfl) ht.1 ht.2) (l ^ i * y)
      have h2 := lead_pow' (lead_single_of_linear_coeff_eq_X (π := _root_.GlobalTheory.BlockValue.sideRow n)
        (z := Sum.inr ρ) (fun c => rfl) ht'.1 ht'.2) y
      rw [Finsupp.smul_single_one] at h1 h2
      have h3 := lead_mul' (lead_mul' h1 h2) (lead_zero_mvExp (_root_.GlobalTheory.BlockValue.sideRow n) (hr ρ))
      rwa [add_zero] at h3
  have hHc : ∀ m : _root_.Formalism.IncomingBounds.PVar n →₀ ℕ, (∀ x ∈ m.support, n0 ≤ (_root_.Formalism.UnitaryBoundIntegral.rowOf x : ℕ)) →
      (∀ ρ : Fin n, n0 ≤ (ρ : ℕ) → _root_.Formalism.UnitaryBoundIntegral.rowDegZ m ρ ≤ l ^ i * y ∧ _root_.Formalism.UnitaryBoundIntegral.rowDegZ' m ρ ≤ y) →
      MvPowerSeries.coeff m
        (∏ ρ : Fin n, (if (ρ : ℕ) < n0 then 1 else t ρ ^ (l ^ i * y) * t' ρ ^ y * _root_.Formalism.IncomingBounds.mvExp (hr ρ))) =
        if m = _root_.Formalism.UnitaryBoundIntegral.diagMon n0 n (l ^ i) y then 1 else 0 := by
    intro m hsupp hbd
    split_ifs with hm
    · rw [hm]
      exact hL.2
    · by_contra hne
      refine hm ((hL.1 m hne).2 ?_)
      have hzero : ∀ ρ : Fin n, ¬ n0 ≤ (ρ : ℕ) → ∀ c : Fin n,
          m (Sum.inl (ρ, c)) = 0 ∧ m (Sum.inr (ρ, c)) = 0 := by
        intro ρ hρ c
        constructor
        · by_contra hc
          exact hρ (hsupp _ (Finsupp.mem_support_iff.2 hc))
        · by_contra hc
          exact hρ (hsupp _ (Finsupp.mem_support_iff.2 hc))
      rw [Finsupp.le_def]
      rintro (ρ | ρ)
      · rw [mapDomain_sideRow_inl, mapDomain_sideRow_inl]
        by_cases hρ : n0 ≤ (ρ : ℕ)
        · have hX : ∑ c : Fin n, (_root_.Formalism.UnitaryBoundIntegral.diagMon n0 n (l ^ i) y) (Sum.inl (ρ, c)) = l ^ i * y := by
            unfold _root_.Formalism.UnitaryBoundIntegral.diagMon
            simp only [Finsupp.finset_sum_apply, Finsupp.add_apply, Finsupp.single_apply,
              Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq, if_false, add_zero]
            rw [Finset.sum_comm, Finset.sum_eq_single_of_mem ρ (by simpa using hρ)]
            · simp
            · intro b _ hb
              simp [hb]
          rw [hX]
          exact (hbd ρ hρ).1
        · rw [Finset.sum_eq_zero fun c _ => (hzero ρ hρ c).1]
          exact Nat.zero_le _
      · rw [mapDomain_sideRow_inr, mapDomain_sideRow_inr]
        by_cases hρ : n0 ≤ (ρ : ℕ)
        · have hX : ∑ c : Fin n, (_root_.Formalism.UnitaryBoundIntegral.diagMon n0 n (l ^ i) y) (Sum.inr (ρ, c)) = y := by
            unfold _root_.Formalism.UnitaryBoundIntegral.diagMon
            simp only [Finsupp.finset_sum_apply, Finsupp.add_apply, Finsupp.single_apply,
              Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq, if_false, zero_add]
            rw [Finset.sum_comm, Finset.sum_eq_single_of_mem ρ (by simpa using hρ)]
            · simp
            · intro b _ hb
              simp [hb]
          rw [hX]
          exact (hbd ρ hρ).2
        · rw [Finset.sum_eq_zero fun c _ => (hzero ρ hρ c).2]
          exact Nat.zero_le _
  unfold _root_.Formalism.IncomingBounds.LamP
  rw [hsplit, hR C n0 n hn (l ^ i) y _ _ hG hH hHc, hres]
end _root_.GlobalTheory
