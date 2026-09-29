-- Prove2me | solution 1 for MvFormalGroup.exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/52d9f69a-0d40-5e7a-bd12-a8a59cb9dae0

import Mathlib
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Theorems.Thm_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

universe u

noncomputable section

open MvPowerSeries

namespace P2mPiDescent72

local instance (priority := high) instModuleCoeff {k : Type u} [Field k] {n : ℕ}
    (I : Ideal (MvPowerSeries (Fin n) k)) :
    Module (MvPowerSeries (Fin n) k) (MvPowerSeries (Fin n) (MvPowerSeries (Fin n) k ⧸ I)) :=
  Algebra.toModule

section PowerSeries

variable {σ R : Type*} [CommRing R]

theorem exists_eq_sum_X_mul [DecidableEq σ] (T : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ d : σ →₀ ℕ, (∀ s ∈ T, d s = 0) → coeff d f = 0) →
      ∃ q : σ → MvPowerSeries σ R, f = ∑ s ∈ T, X s * q s := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    refine ⟨fun _ => 0, ?_⟩
    rw [Finset.sum_empty]
    ext d
    rw [map_zero]
    exact hf d (fun s hs => absurd hs (Finset.notMem_empty s))
  | @insert s T hs ih =>
    intro f hf
    let f₀ : MvPowerSeries σ R := fun d => if d s = 0 then coeff d f else 0
    have hf₀ : ∀ d, coeff d f₀ = if d s = 0 then coeff d f else 0 := fun d => rfl
    have hdvd : (X s : MvPowerSeries σ R) ∣ f - f₀ := by
      rw [X_dvd_iff]
      intro d hd
      rw [map_sub, hf₀, if_pos hd, sub_self]
    obtain ⟨q', hq'⟩ := hdvd
    obtain ⟨q, hq⟩ := ih f₀ (by
      intro d hd
      rw [hf₀]
      split_ifs with hds
      · exact hf d (fun t ht => by
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact hds
          · exact hd t ht)
      · rfl)
    refine ⟨Function.update q s q', ?_⟩
    rw [Finset.sum_insert hs, Function.update_self]
    have hrest : ∑ t ∈ T, X t * Function.update q s q' t = ∑ t ∈ T, X t * q t := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Function.update_of_ne (ne_of_mem_of_not_mem ht hs)]
    rw [hrest, ← hq, ← hq']
    ring

theorem exists_eq_sum_X_mul_of_constantCoeff [Fintype σ] (f : MvPowerSeries σ R)
    (hf : constantCoeff f = 0) : ∃ q : σ → MvPowerSeries σ R, f = ∑ s, X s * q s := by
  classical
  obtain ⟨q, hq⟩ := exists_eq_sum_X_mul (Finset.univ : Finset σ) f (fun d hd => by
    have hd0 : d = 0 := Finsupp.ext fun s => hd s (Finset.mem_univ s)
    rw [hd0, coeff_zero_eq_constantCoeff_apply, hf])
  exact ⟨q, hq⟩

theorem exists_le_degree_eq (d : σ →₀ ℕ) : ∀ N : ℕ, N ≤ d.degree → ∃ e ≤ d, e.degree = N := by
  classical
  intro N
  induction N with
  | zero => intro _; exact ⟨0, bot_le, map_zero _⟩
  | succ N ih =>
    intro hN
    obtain ⟨e, hed, he⟩ := ih (Nat.le_of_succ_le hN)
    have hne : e ≠ d := by
      rintro rfl
      omega
    have hlt : ∃ s, e s < d s := by
      by_contra hcon
      push Not at hcon
      exact hne (le_antisymm hed (Finsupp.le_def.mpr hcon))
    obtain ⟨s, hs⟩ := hlt
    refine ⟨e + Finsupp.single s 1, ?_, ?_⟩
    · rw [Finsupp.le_def]
      intro i
      by_cases his : i = s
      · subst his
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
        omega
      · have h0 : (Finsupp.single s 1 : σ →₀ ℕ) i = 0 := by
          rw [Finsupp.single_apply, if_neg (Ne.symm his)]
        simp only [Finsupp.coe_add, Pi.add_apply, h0, add_zero]
        exact Finsupp.le_def.mp hed i
    · rw [map_add, he, Finsupp.degree_single]

theorem exists_eq_sum_monomial_mul [Finite σ] (N : ℕ) (f : MvPowerSeries σ R)
    (hf : ∀ d : σ →₀ ℕ, d.degree < N → coeff d f = 0) :
    ∃ (S : Finset (σ →₀ ℕ)) (h : (σ →₀ ℕ) → MvPowerSeries σ R),
      (∀ e ∈ S, e.degree = N) ∧ f = ∑ e ∈ S, monomial e (1 : R) * h e := by
  classical
  let S : Finset (σ →₀ ℕ) := ((Finsupp.finite_of_degree_le N).subset
    (fun e (he : e.degree = N) => (le_of_eq he : e.degree ≤ N))).toFinset
  have hS : ∀ e, e ∈ S ↔ e.degree = N := fun e => by
    simp only [S, Set.Finite.mem_toFinset]
    exact Iff.rfl

  have hchoice : ∀ d : σ →₀ ℕ, ∃ e : σ →₀ ℕ, N ≤ d.degree → e ≤ d ∧ e.degree = N := by
    intro d
    by_cases hd : N ≤ d.degree
    · obtain ⟨e, he, he'⟩ := exists_le_degree_eq d N hd
      exact ⟨e, fun _ => ⟨he, he'⟩⟩
    · exact ⟨0, fun h => absurd h hd⟩
  choose c hc using hchoice
  let h : (σ →₀ ℕ) → MvPowerSeries σ R := fun e d' =>
    if N ≤ (d' + e).degree ∧ c (d' + e) = e then coeff (d' + e) f else 0
  have hh : ∀ e d', coeff d' (h e) = if N ≤ (d' + e).degree ∧ c (d' + e) = e then coeff (d' + e) f else 0 :=
    fun e d' => rfl
  refine ⟨S, h, fun e he => (hS e).mp he, ?_⟩
  ext d
  rw [map_sum]
  simp only [coeff_monomial_mul, one_mul]
  by_cases hd : N ≤ d.degree
  · obtain ⟨hcd, hcdeg⟩ := hc d hd
    rw [Finset.sum_eq_single (c d)]
    · rw [if_pos hcd, hh, tsub_add_cancel_of_le hcd, if_pos ⟨hd, rfl⟩]
    · intro e _ hne
      split_ifs with hed
      · rw [hh, tsub_add_cancel_of_le hed, if_neg (fun h' => hne h'.2.symm)]
      · rfl
    · intro hcS
      exact absurd ((hS _).mpr hcdeg) hcS
  · rw [hf d (not_le.mp hd)]
    symm
    refine Finset.sum_eq_zero fun e he => ?_
    split_ifs with hed
    · rw [hh, tsub_add_cancel_of_le hed, if_neg (fun h' => hd h'.1)]
    · rfl

theorem subst_C' {τ : Type*} {S : Type*} [CommRing S] [Algebra R S] {a : σ → MvPowerSeries τ S}
    (ha : HasSubst a) (r : R) : subst a (C r : MvPowerSeries σ R) = C (algebraMap R S r) := by
  rw [← monomial_zero_eq_C_apply, subst_monomial ha, Finsupp.prod_zero_index, mul_one,
    MvPowerSeries.algebraMap_apply]

theorem constantCoeff_subst_of_constantCoeff_zero [Finite σ] {τ : Type*} {S : Type*} [CommRing S]
    [Algebra R S] {a : σ → MvPowerSeries τ S} (ha : ∀ i, (a i).constantCoeff = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = algebraMap R S (constantCoeff f) := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hsplit : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  have hz : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  rw [hsplit, subst_add hsa, subst_C' hsa, map_add, constantCoeff_C, constantCoeff_subst_eq_zero hsa ha hz,
    add_zero, map_add, constantCoeff_C, hz, add_zero]

theorem subst_map_algebraMap {τ : Type*} {S : Type*} [CommRing S] [Algebra R S]
    {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (f : MvPowerSeries σ R) :
    subst a (map (algebraMap R S) f) = subst a f := by
  ext e
  rw [coeff_subst ha, coeff_subst ha]
  apply finsum_congr
  intro d
  rw [coeff_map, algebraMap_smul]

theorem subst_mem_span [Fintype σ] {τ : Type*} {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) {f : MvPowerSeries σ R} (hf : constantCoeff f = 0) :
    subst a f ∈ Ideal.span (Set.range a) := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha
  obtain ⟨q, hq⟩ := exists_eq_sum_X_mul_of_constantCoeff f hf
  rw [hq, ← coe_substAlgHom hsa, map_sum]
  refine Ideal.sum_mem _ fun s _ => ?_
  rw [map_mul, coe_substAlgHom hsa, subst_X hsa]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s, rfl⟩)

theorem injective_of_existsUnique_expansion {A : Type*} [CommRing A] [NoZeroDivisors A]
    [Nontrivial A] (φ : A →+* A) {ι : Type*} [Fintype ι] (b : ι → A)
    (hb : ∀ x : A, ∃! c : ι → A, x = ∑ i, φ (c i) * b i) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨c₁, hc₁, huniq⟩ := hb 1
  have hc₁' : (1 : A) = ∑ i, φ (c₁ i + c * c₁ i) * b i := by
    refine hc₁.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_add, map_mul, hc, zero_mul, add_zero]
  have hcc : (fun i => c₁ i + c * c₁ i) = c₁ := huniq _ hc₁'
  by_contra hne
  have hzero : ∀ i, c₁ i = 0 := fun i => by
    have hi := congrFun hcc i
    have hmul : c * c₁ i = 0 := by
      have := congrArg (fun t => t - c₁ i) hi
      simpa using this
    exact (mul_eq_zero.mp hmul).resolve_left hne
  have : (1 : A) = 0 := by
    rw [hc₁]
    exact Finset.sum_eq_zero fun i _ => by rw [hzero i, map_zero, zero_mul]
  exact one_ne_zero this

end PowerSeries

section Quotient

variable {k : Type u} [Field k] {n : ℕ} (I : Ideal (MvPowerSeries (Fin n) k))

local notation "A" => MvPowerSeries (Fin n) k

theorem exists_pow_mk_X_eq_zero [Module.Finite k (A ⧸ I)] :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ l : Fin n, (Ideal.Quotient.mk I (X l)) ^ N₀ = 0 := by
  haveI : IsArtinianRing (A ⧸ I) := IsArtinianRing.of_finite k (A ⧸ I)
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A ⧸ I)
  refine ⟨N + 1, Nat.succ_pos N, fun l => ?_⟩
  have hmem : Ideal.Quotient.mk I (X l) ∈ Ideal.jacobson (⊥ : Ideal (A ⧸ I)) := by
    rw [Ideal.mem_jacobson_bot]
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), ← map_add]
    refine IsUnit.map _ ?_
    rw [isUnit_iff_constantCoeff]
    simp
  have hpow : (Ideal.Quotient.mk I (X l)) ^ N ∈ (Ideal.jacobson (⊥ : Ideal (A ⧸ I))) ^ N :=
    Ideal.pow_mem_pow hmem N
  rw [hN] at hpow
  rw [pow_succ, Ideal.mem_bot.mp hpow, zero_mul]

variable {I}

theorem exists_degree_bound [Module.Finite k (A ⧸ I)] :
    ∃ N : ℕ, ∀ e : Fin n →₀ ℕ, N ≤ e.degree →
      (∏ l, (Ideal.Quotient.mk I (X l)) ^ e l = 0) ∧ monomial e (1 : k) ∈ I := by
  obtain ⟨N₀, hN₀, hnil⟩ := exists_pow_mk_X_eq_zero I
  refine ⟨n * N₀ + 1, fun e he => ?_⟩

  have hbig : ∃ l, N₀ ≤ e l := by
    by_contra hcon
    push Not at hcon
    have : e.degree ≤ n * N₀ := by
      rw [Finsupp.degree_eq_sum]
      calc ∑ i, e i ≤ ∑ _i : Fin n, N₀ := Finset.sum_le_sum fun i _ => (hcon i).le
        _ = n * N₀ := by simp
    omega
  obtain ⟨l, hl⟩ := hbig
  have hXl : (X l : A) ^ e l ∈ I := by
    have h1 : Ideal.Quotient.mk I ((X l : A) ^ e l) = 0 := by
      rw [map_pow, ← Nat.sub_add_cancel hl, pow_add, hnil l, mul_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  constructor
  · apply Finset.prod_eq_zero (Finset.mem_univ l)
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr hXl]
  · classical
    rw [monomial_one_eq, Finsupp.prod]
    by_cases hls : l ∈ e.support
    · rw [← Finset.mul_prod_erase _ _ hls]
      exact Ideal.mul_mem_right _ _ hXl
    · exfalso
      rw [Finsupp.mem_support_iff, not_not] at hls
      omega

def tbar (I : Ideal (MvPowerSeries (Fin n) k)) : Fin n → A ⧸ I := fun l => Ideal.Quotient.mk I (X l)

theorem isNilpotent_tbar [Module.Finite k (A ⧸ I)] (l : Fin n) : IsNilpotent (tbar I l) := by
  obtain ⟨N₀, -, h⟩ := exists_pow_mk_X_eq_zero I
  exact ⟨N₀, h l⟩

theorem hasSubst_C_tbar [Module.Finite k (A ⧸ I)] {τ : Type*} :
    HasSubst (fun l => (C (tbar I l) : MvPowerSeries τ (A ⧸ I))) :=
  hasSubst_of_constantCoeff_nilpotent (fun l => by simpa using isNilpotent_tbar l)

theorem algebraMap_quot (x : k) : algebraMap k (A ⧸ I) x = Ideal.Quotient.mk I (C x) := by
  rw [← Ideal.Quotient.mk_algebraMap, MvPowerSeries.algebraMap_apply]
  rfl

theorem subst_C_tbar [Module.Finite k (A ⧸ I)] {τ : Type*} (g : A) :
    subst (fun l => (C (tbar I l) : MvPowerSeries τ (A ⧸ I))) g = C (Ideal.Quotient.mk I g) := by
  classical
  have ha : HasSubst (fun l => (C (tbar I l) : MvPowerSeries τ (A ⧸ I))) := hasSubst_C_tbar
  obtain ⟨N, hN⟩ := exists_degree_bound (I := I)

  set p : MvPolynomial (Fin n) k := truncTotal N g with hp
  have htail : ∀ d : Fin n →₀ ℕ, d.degree < N → coeff d (g - (p : A)) = 0 := by
    intro d hd
    rw [map_sub, MvPolynomial.coeff_coe, hp, coeff_truncTotal _ hd, sub_self]
  obtain ⟨S, h, hS, hdec⟩ := exists_eq_sum_monomial_mul N (g - (p : A)) htail
  have hg : g = (p : A) + (g - (p : A)) := by ring

  have hpoly : subst (fun l => (C (tbar I l) : MvPowerSeries τ (A ⧸ I))) (p : A) =
      C (Ideal.Quotient.mk I (p : A)) := by
    rw [subst_coe]
    have h1 : (MvPolynomial.aeval fun l => (C (tbar I l) : MvPowerSeries τ (A ⧸ I))) =
        (IsScalarTower.toAlgHom k (A ⧸ I) (MvPowerSeries τ (A ⧸ I))).comp
          (MvPolynomial.aeval (tbar I)) := by
      apply MvPolynomial.algHom_ext
      intro s
      simp [MvPowerSeries.algebraMap_apply]
    have h2 : ((Ideal.Quotient.mkₐ k I).comp (MvPolynomial.coeToMvPowerSeries.algHom k) :
        MvPolynomial (Fin n) k →ₐ[k] A ⧸ I) = MvPolynomial.aeval (tbar I) := by
      apply MvPolynomial.algHom_ext
      intro s
      simp [tbar, MvPolynomial.coeToMvPowerSeries.algHom_apply]
    rw [h1, AlgHom.comp_apply, ← h2]
    simp [MvPowerSeries.algebraMap_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply]

  have htail1 : subst (fun l => (C (tbar I l) : MvPowerSeries τ (A ⧸ I))) (g - (p : A)) = 0 := by
    rw [hdec, ← coe_substAlgHom ha, map_sum]
    refine Finset.sum_eq_zero fun e he => ?_
    rw [map_mul, coe_substAlgHom ha, subst_monomial ha, map_one, one_mul]
    have hprod : (e.prod fun s m => (C (tbar I s) : MvPowerSeries τ (A ⧸ I)) ^ m) = 0 := by
      rw [Finsupp.prod_fintype _ _ (fun s => pow_zero _)]
      simp only [← map_pow]
      rw [← map_prod]
      show C (∏ l, (Ideal.Quotient.mk I (X l)) ^ e l) = 0
      rw [(hN e (le_of_eq (hS e he).symm)).1, map_zero]
    rw [hprod, zero_mul]
  have htail2 : Ideal.Quotient.mk I (g - (p : A)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, hdec]
    exact Ideal.sum_mem _ fun e he => Ideal.mul_mem_right _ _ (hN e (le_of_eq (hS e he).symm)).2
  rw [hg, subst_add ha, hpoly, htail1, add_zero, map_add, htail2, add_zero]

theorem mk_subst_eq_of_constantCoeff {a : Fin n → A} (ha : ∀ i, constantCoeff (a i) = 0)
    (haI : ∀ i, a i ∈ I) (c : A) :
    Ideal.Quotient.mk I (subst a c) = algebraMap k (A ⧸ I) (constantCoeff c) := by
  rw [algebraMap_quot, Ideal.Quotient.eq]
  have h2 : subst a c - C (constantCoeff c) = subst a (c - C (constantCoeff c)) := by
    rw [subst_sub (hasSubst_of_constantCoeff_zero ha), subst_C' (hasSubst_of_constantCoeff_zero ha)]
    rfl
  rw [h2]
  refine (Ideal.span_le.mpr ?_) (subst_mem_span ha (by simp))
  rintro _ ⟨i, rfl⟩
  exact haI i

end Quotient

section Torsor

variable {k : Type u} [Field k] {n : ℕ} (F : MvFormalGroup n k)
  (I : Ideal (MvPowerSeries (Fin n) k)) [Module.Finite k (MvPowerSeries (Fin n) k ⧸ I)]

local notation "A" => MvPowerSeries (Fin n) k
local notation "B" => MvPowerSeries (Fin n) (MvPowerSeries (Fin n) k ⧸ I)

def evFam : Fin n ⊕ Fin n → B :=
  Sum.elim (fun l => X l) (fun l => C (tbar I l))

theorem hasSubst_evFam : HasSubst (evFam I) :=
  hasSubst_of_constantCoeff_nilpotent (by
    rintro (l | l)
    · simp [evFam]
    · simpa [evFam] using isNilpotent_tbar l)

def torsorFam : Fin n → B :=
  fun i => substAlgHom (hasSubst_evFam I) (F.toPowerSeries i)

theorem hasSubst_torsorFam : HasSubst (torsorFam F I) :=
  HasSubst.comp F.hasSubst_toPowerSeries (hasSubst_evFam I)

omit [Module.Finite k (MvPowerSeries (Fin n) k ⧸ I)] in
theorem algebraMap_eq (a : A) : algebraMap A B a = map (algebraMap k (A ⧸ I)) a := rfl

omit [Module.Finite k (MvPowerSeries (Fin n) k ⧸ I)] in
theorem smul_def' (a : A) (G : B) : a • G = map (algebraMap k (A ⧸ I)) a * G := Algebra.smul_def a G

theorem subst_evFam_subst_inl (f : A) :
    subst (evFam I) (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) f) =
      map (algebraMap k (A ⧸ I)) f := by
  have hXl : HasSubst (fun l : Fin n => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  rw [subst_comp_subst_apply hXl (hasSubst_evFam I), map_algebraMap_eq_subst_X]
  congr 1
  funext l
  rw [subst_X (hasSubst_evFam I)]
  rfl

theorem subst_evFam_subst_inr (f : A) :
    subst (evFam I) (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) f) =
      C (Ideal.Quotient.mk I f) := by
  have hXr : HasSubst (fun l : Fin n => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  rw [subst_comp_subst_apply hXr (hasSubst_evFam I)]
  have hfam : (fun l => subst (evFam I) ((X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k))) =
      fun l => (C (tbar I l) : B) := by
    funext l
    rw [subst_X (hasSubst_evFam I)]
    rfl
  rw [hfam, subst_C_tbar]

theorem subst_evFam_subst_F (f : A) :
    subst (evFam I) (subst F.toPowerSeries f) = subst (torsorFam F I) f := by
  rw [subst_comp_subst_apply F.hasSubst_toPowerSeries (hasSubst_evFam I)]
  show _ = subst (fun i => substAlgHom (hasSubst_evFam I) (F.toPowerSeries i)) f
  congr 1
  funext s
  rw [coe_substAlgHom]

theorem subst_torsorFam_subst_nth [F.IsComm] {φ : Fin n → MvPowerSeries (Fin n) k}
    (hφ0 : ∀ i, constantCoeff (φ i) = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) =
      subst (Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
        (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j)))
        (F.toPowerSeries i))
    (hmI : ∀ i, φ i ∈ I) (c : A) :
    subst (torsorFam F I) (subst (φ) c) = map (algebraMap k (A ⧸ I)) (subst (φ) c) := by
  have hnat : HasSubst φ := hasSubst_of_constantCoeff_zero hφ0
  have hXl : HasSubst (fun l : Fin n => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hXr : HasSubst (fun l : Fin n => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _

  have hcomp : ∀ i, subst (torsorFam F I) (φ i) = map (algebraMap k (A ⧸ I)) (φ i) := by
    intro i
    rw [← subst_evFam_subst_F]
    have key := hφF i
    rw [key, subst_comp_subst_apply (MvFormalGroup.hasSubst_elim
      (fun j => constantCoeff_subst_eq_zero hXl (fun l => constantCoeff_X _)
        (hφ0 j))
      (fun j => constantCoeff_subst_eq_zero hXr (fun l => constantCoeff_X _)
        (hφ0 j))) (hasSubst_evFam I)]
    have hfam : (fun s => subst (evFam I) (Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
        (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j)) s))
        = Sum.elim (fun j => map (algebraMap k (A ⧸ I)) (φ j)) (fun _ => (0 : B)) := by
      funext s
      rcases s with j | j
      · exact subst_evFam_subst_inl I (φ j)
      · show subst (evFam I) (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k))
          (φ j)) = 0
        rw [subst_evFam_subst_inr, Ideal.Quotient.eq_zero_iff_mem.mpr (hmI j), map_zero]
    rw [hfam, ← subst_map_algebraMap (MvFormalGroup.hasSubst_elim
      (fun j => by rw [constantCoeff_map, hφ0, map_zero])
      (fun _ => map_zero _))]
    exact MvFormalGroup.subst_elim_zero_right (F.map (algebraMap k (A ⧸ I)))
      (a := fun j => map (algebraMap k (A ⧸ I)) (φ j))
      (fun j => by rw [constantCoeff_map, hφ0, map_zero]) i
  rw [subst_comp_subst_apply hnat (hasSubst_torsorFam F I), map_algebraMap_eq_subst_X,
    subst_comp_subst_apply hnat HasSubst.X]
  congr 1
  funext i
  rw [hcomp, map_algebraMap_eq_subst_X]

theorem constantCoeff_torsorFam (i : Fin n) : constantCoeff (torsorFam F I i) = tbar I i := by
  classical
  show constantCoeff (substAlgHom (hasSubst_evFam I) (F.toPowerSeries i)) = _
  rw [coe_substAlgHom]
  have hC : HasSubst (fun s => (C (constantCoeff (evFam I s)) : B)) :=
    hasSubst_of_constantCoeff_nilpotent (fun s => by
      simpa using (hasSubst_evFam I).const_coeff s)
  have h1 : constantCoeff (subst (evFam I) (F.toPowerSeries i)) =
      constantCoeff (subst (fun s => (C (constantCoeff (evFam I s)) : B)) (F.toPowerSeries i)) := by
    rw [constantCoeff_subst (hasSubst_evFam I), constantCoeff_subst hC]
    apply finsum_congr
    intro d
    congr 1
    simp only [map_finsuppProd, map_pow, constantCoeff_C]
  have h2 : (fun s => (C (constantCoeff (evFam I s)) : B)) =
      Sum.elim (fun _ : Fin n => (0 : B)) (fun l => C (tbar I l)) := by
    funext s
    rcases s with l | l
    · simp [evFam]
    · simp [evFam]
  rw [h1, h2]
  have h0X : HasSubst (Sum.elim (fun _ : Fin n => (0 : A)) fun j => (X j : A)) :=
    MvFormalGroup.hasSubst_elim (fun _ => map_zero _) fun j => constantCoeff_X j
  have hCt : HasSubst (fun l => (C (tbar I l) : B)) := hasSubst_C_tbar
  have h3 : (Sum.elim (fun _ : Fin n => (0 : B)) (fun l => C (tbar I l))) =
      fun s : Fin n ⊕ Fin n => subst (fun l => (C (tbar I l) : B))
        (Sum.elim (fun _ : Fin n => (0 : A)) (fun j => (X j : A)) s) := by
    funext s
    rcases s with l | l
    · show (0 : B) = subst _ (0 : A)
      rw [← coe_substAlgHom hCt, map_zero]
    · show C (tbar I l) = subst _ (X l)
      rw [subst_X hCt]
  rw [h3, ← subst_comp_subst_apply h0X hCt, MvFormalGroup.subst_elim_zero_X F i, subst_C_tbar,
    constantCoeff_C]
  rfl

theorem constantCoeff_subst_torsorFam (b : A) :
    constantCoeff (subst (torsorFam F I) b) = Ideal.Quotient.mk I b := by
  classical
  have hC : HasSubst (fun i => (C (tbar I i) : B)) := hasSubst_C_tbar
  have h1 : constantCoeff (subst (torsorFam F I) b) =
      constantCoeff (subst (fun i => (C (tbar I i) : B)) b) := by
    rw [constantCoeff_subst (hasSubst_torsorFam F I), constantCoeff_subst hC]
    apply finsum_congr
    intro d
    congr 1
    simp only [map_finsuppProd, map_pow, constantCoeff_C, constantCoeff_torsorFam]
  rw [h1, subst_C_tbar, constantCoeff_C]

def coordFun {r : ℕ} (β : Module.Basis (Fin r) k (A ⧸ I)) (G : B) (j : Fin r) : A :=
  fun d => β.equivFun (coeff d G) j

def ofCoord {r : ℕ} (β : Module.Basis (Fin r) k (A ⧸ I)) (H : Fin r → A) : B :=
  fun d => β.equivFun.symm fun j => coeff d (H j)

omit [Module.Finite k (MvPowerSeries (Fin n) k ⧸ I)] in
theorem coeff_coordFun {r : ℕ} (β : Module.Basis (Fin r) k (A ⧸ I)) (G : B) (j : Fin r) (d : Fin n →₀ ℕ) :
    coeff d (coordFun I β G j) = β.equivFun (coeff d G) j := rfl

omit [Module.Finite k (MvPowerSeries (Fin n) k ⧸ I)] in
theorem coeff_ofCoord {r : ℕ} (β : Module.Basis (Fin r) k (A ⧸ I)) (H : Fin r → A) (d : Fin n →₀ ℕ) :
    coeff d (ofCoord I β H) = β.equivFun.symm fun j => coeff d (H j) := rfl

def coordEquiv {r : ℕ} (β : Module.Basis (Fin r) k (A ⧸ I)) : B ≃ₗ[A] (Fin r → A) where
  toFun G := fun j => coordFun I β G j
  invFun H := ofCoord I β H
  map_add' G₁ G₂ := by
    funext j
    ext d
    rw [Pi.add_apply, map_add, coeff_coordFun, coeff_coordFun, coeff_coordFun, map_add, map_add,
      Pi.add_apply]
  map_smul' a G := by
    funext j
    ext d
    show β.equivFun (coeff d (map (algebraMap k (A ⧸ I)) a * G)) j = coeff d (a * coordFun I β G j)
    rw [coeff_mul, coeff_mul, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [coeff_map, ← Algebra.smul_def, map_smul, Pi.smul_apply, smul_eq_mul, coeff_coordFun]
  left_inv G := by
    ext d
    rw [coeff_ofCoord]
    exact β.equivFun.symm_apply_apply (coeff d G)
  right_inv H := by
    funext j
    ext d
    rw [coeff_coordFun, coeff_ofCoord, LinearEquiv.apply_symm_apply]

scoped instance moduleFinite_B : Module.Finite A B :=
  Module.Finite.equiv (coordEquiv I (Module.finBasis k (A ⧸ I))).symm

def combo {r : ℕ} (Ψ : Fin r → B) : (Fin r → A) →ₗ[A] B :=
  ∑ j, (LinearMap.proj j : (Fin r → A) →ₗ[A] A).smulRight (Ψ j)

omit [Module.Finite k (MvPowerSeries (Fin n) k ⧸ I)] in
theorem combo_apply {r : ℕ} (Ψ : Fin r → B) (c : Fin r → A) :
    combo I Ψ c = ∑ j, map (algebraMap k (A ⧸ I)) (c j) * Ψ j := by
  simp only [combo, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply]
  rfl

theorem combo_surjective {r : ℕ} (Ψ : Fin r → B)
    (hspan : ∀ y : A ⧸ I, ∃ μ : Fin r → k, y = ∑ j, algebraMap k (A ⧸ I) (μ j) * constantCoeff (Ψ j)) :
    Function.Surjective (combo I Ψ) := by
  classical
  set N' : Submodule A B := LinearMap.range (combo I Ψ) with hN'
  let 𝔪 : Ideal A := Ideal.span (Set.range (X : Fin n → A))
  have hjac : 𝔪 ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨l, rfl⟩
    rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff]
    simp

  have hstep : ∀ G : B, ∃ H : B, N'.mkQ G = N'.mkQ H ∧ H ∈ 𝔪 • (⊤ : Submodule A B) := by
    intro G
    obtain ⟨μ, hμ⟩ := hspan (constantCoeff G)
    refine ⟨G - ∑ j, (C (algebraMap k (A ⧸ I) (μ j)) : B) * Ψ j, ?_, ?_⟩
    · rw [map_sub, eq_comm, sub_eq_self, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hN']
      refine ⟨fun j => C (μ j), ?_⟩
      rw [combo_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_C]
    · have hH0 : constantCoeff (G - ∑ j, (C (algebraMap k (A ⧸ I) (μ j)) : B) * Ψ j) = 0 := by
        rw [map_sub, map_sum, hμ, sub_eq_zero]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, constantCoeff_C]
      obtain ⟨q, hq⟩ := exists_eq_sum_X_mul_of_constantCoeff _ hH0
      rw [hq]
      refine Submodule.sum_mem _ fun l _ => ?_
      have hXl : (X l : B) * q l = (X l : A) • q l := by
        show _ = map (algebraMap k (A ⧸ I)) (X l) * q l
        rw [map_X]
      rw [hXl]
      exact Submodule.smul_mem_smul (Ideal.subset_span ⟨l, rfl⟩) Submodule.mem_top

  have htop : (⊤ : Submodule A (B ⧸ N')) = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot 𝔪 ⊤ Module.Finite.fg_top ?_ hjac
    rintro x -
    obtain ⟨G, rfl⟩ := Submodule.mkQ_surjective N' x
    obtain ⟨H, hGH, hH⟩ := hstep G
    rw [hGH]
    have hmem : N'.mkQ H ∈ (𝔪 • (⊤ : Submodule A B)).map N'.mkQ := Submodule.mem_map_of_mem hH
    rw [Submodule.map_smul''] at hmem
    exact Submodule.smul_mono le_rfl le_top hmem
  intro G
  have hG : N'.mkQ G ∈ (⊤ : Submodule A (B ⧸ N')) := Submodule.mem_top
  rw [htop, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hN'] at hG
  exact hG

theorem combo_injective (Ψ : Fin (Module.finrank k (A ⧸ I)) → B) (hsurj : Function.Surjective (combo I Ψ)) :
    Function.Injective (combo I Ψ) := by
  let Ξ := coordEquiv I (Module.finBasis k (A ⧸ I))
  let T : (Fin (Module.finrank k (A ⧸ I)) → A) →ₗ[A] (Fin (Module.finrank k (A ⧸ I)) → A) :=
    Ξ.toLinearMap ∘ₗ combo I Ψ
  have hT : Function.Surjective T := Ξ.surjective.comp hsurj
  have hTinj : Function.Injective T := OrzechProperty.injective_of_surjective_endomorphism T hT
  intro x y hxy
  exact hTinj (show Ξ (combo I Ψ x) = Ξ (combo I Ψ y) by rw [hxy])

end Torsor

end P2mPiDescent72
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.P2mPiDescent72"

attribute [local instance 10000] P2mPiDescent72.instModuleCoeff

open P2mPiDescent72 in
theorem descent72
    {k : Type u} [Field k] {n : ℕ} (F : MvFormalGroup n k) [F.IsComm]
    (φ : Fin n → MvPowerSeries (Fin n) k) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφF : ∀ i, MvPowerSeries.subst F.toPowerSeries (φ i) =
      MvPowerSeries.subst (Sum.elim
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j)))
        (F.toPowerSeries i))
    (hfin : Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range φ)))
    (f : MvPowerSeries (Fin n) k)
    (hf : MvPowerSeries.subst F.toPowerSeries f -
        MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) f ∈
      Ideal.span (Set.range fun i => MvPowerSeries.subst
        (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ i))) :
    ∃! G : MvPowerSeries (Fin n) k, f = MvPowerSeries.subst (φ) G := by
  classical

  set I : Ideal (MvPowerSeries (Fin n) k) := Ideal.span (Set.range (φ)) with hI
  haveI : Module.Finite k (MvPowerSeries (Fin n) k ⧸ I) := hfin
  have hmI : ∀ i, φ i ∈ I := fun i => Ideal.subset_span ⟨i, rfl⟩
  have hnat0 : ∀ i, constantCoeff (φ i) = 0 := hφ0
  have hnat : HasSubst (φ) := hasSubst_of_constantCoeff_zero hnat0
  let θ : MvPowerSeries (Fin n) k →ₐ[k] MvPowerSeries (Fin n) k := substAlgHom hnat
  have hθ : ∀ c, θ c = subst φ c := fun c => congrFun (coe_substAlgHom hnat) c

  obtain ⟨-, -, b, hb⟩ :=
    MvPowerSeries.finite_flat_exists_basis_substAlgHom_of_finite_quotient (φ) hnat0 hfin
  have hinj : Function.Injective θ :=
    injective_of_existsUnique_expansion θ.toRingHom b (fun x => by simpa [hθ] using hb x)

  refine existsUnique_of_exists_of_unique ?_ (fun G₁ G₂ h₁ h₂ => hinj (by rw [hθ, hθ, ← h₁, ← h₂]))

  let ρ : MvPowerSeries (Fin n) k →ₐ[k] MvPowerSeries (Fin n) (MvPowerSeries (Fin n) k ⧸ I) :=
    substAlgHom (hasSubst_torsorFam F I)
  have hρ : ∀ x, ρ x = subst (torsorFam F I) x := fun x => congrFun (coe_substAlgHom (hasSubst_torsorFam F I)) x
  let Ψ : Fin (Module.finrank k (MvPowerSeries (Fin n) k ⧸ I)) →
      MvPowerSeries (Fin n) (MvPowerSeries (Fin n) k ⧸ I) := fun j => ρ (b j)

  have hspan : ∀ y : MvPowerSeries (Fin n) k ⧸ I,
      ∃ μ : Fin _ → k, y = ∑ j, algebraMap k _ (μ j) * constantCoeff (Ψ j) := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc, -⟩ := hb x
    refine ⟨fun j => constantCoeff (c j), ?_⟩
    conv_lhs => rw [hc]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, mk_subst_eq_of_constantCoeff hnat0 hmI]
    congr 1
    show _ = constantCoeff (ρ (b j))
    rw [hρ, constantCoeff_subst_torsorFam]
  have hsurj := combo_surjective I Ψ hspan
  have hinjΨ := combo_injective I Ψ hsurj

  have hev : ρ f = algebraMap _ _ f := by
    have hzero : subst (evFam I) (MvPowerSeries.subst F.toPowerSeries f -
        MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) f) = 0 := by
      have hle : Ideal.span (Set.range fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ i)) ≤
          RingHom.ker (substAlgHom (hasSubst_evFam I)).toRingHom := by
        refine Ideal.span_le.mpr ?_
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom,
          subst_evFam_subst_inr, Ideal.Quotient.eq_zero_iff_mem.mpr (hmI i), map_zero]
      have := hle hf
      rwa [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom] at this
    rw [subst_sub (hasSubst_evFam I), subst_evFam_subst_F, subst_evFam_subst_inl, sub_eq_zero] at hzero
    rw [hρ, hzero]
    rfl

  obtain ⟨c, hc, -⟩ := hb f
  obtain ⟨e, he, -⟩ := hb 1
  have hterm : ∀ (u : MvPowerSeries (Fin n) k) (j),
      ρ (subst (φ) u * b j) = map (algebraMap k _) (θ u) * Ψ j := by
    intro u j
    rw [map_mul, hθ]
    congr 1
    rw [hρ, subst_torsorFam_subst_nth F I hφ0 hφF hmI]
  have hρf : ρ f = combo I Ψ (fun j => θ (c j)) := by
    rw [combo_apply]
    conv_lhs => rw [hc]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => hterm (c j) j
  have hρ1 : (1 : MvPowerSeries (Fin n) (MvPowerSeries (Fin n) k ⧸ I)) = combo I Ψ (fun j => θ (e j)) := by
    rw [← map_one ρ, combo_apply]
    conv_lhs => rw [he]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => hterm (e j) j
  have hf1 : algebraMap (MvPowerSeries (Fin n) k) _ f = combo I Ψ (fun j => f * θ (e j)) := by
    have h2 : (fun j => f * θ (e j)) = f • (fun j => θ (e j)) := by
      funext j
      rfl
    rw [h2, LinearMap.map_smul, ← hρ1, Algebra.smul_def, mul_one]
  have hcoord : (fun j => θ (c j)) = fun j => f * θ (e j) :=
    hinjΨ (by rw [← hρf, ← hf1, hev])

  have hunit : ∃ j, IsUnit (e j) := by
    by_contra hcon
    push Not at hcon
    have h0 : ∀ j, constantCoeff (e j) = 0 := fun j => by
      have := hcon j
      rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not] at this
      exact this
    have h1 : constantCoeff (1 : MvPowerSeries (Fin n) k) = 0 := by
      conv_lhs => rw [he]
      rw [map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_mul, constantCoeff_subst_of_constantCoeff_zero hnat0, h0 j]
      simp
    simp at h1
  obtain ⟨j, hj⟩ := hunit
  refine ⟨c j * ↑(hj.unit⁻¹), ?_⟩
  have hcj : θ (c j) = f * θ (e j) := congrFun hcoord j
  rw [← hθ, map_mul, hcj, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]

end
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.P2mPiDescent72"

noncomputable section

open MvPowerSeries

namespace P2mPiDescent85

section PowerSeries

variable {σ R : Type*} [CommRing R]

theorem exists_eq_sum_X_mul [DecidableEq σ] (T : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ d : σ →₀ ℕ, (∀ s ∈ T, d s = 0) → coeff d f = 0) →
      ∃ q : σ → MvPowerSeries σ R, f = ∑ s ∈ T, X s * q s := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    refine ⟨fun _ => 0, ?_⟩
    rw [Finset.sum_empty]
    ext d
    rw [map_zero]
    exact hf d (fun s hs => absurd hs (Finset.notMem_empty s))
  | @insert s T hs ih =>
    intro f hf
    let f₀ : MvPowerSeries σ R := fun d => if d s = 0 then coeff d f else 0
    have hf₀ : ∀ d, coeff d f₀ = if d s = 0 then coeff d f else 0 := fun d => rfl
    have hdvd : (X s : MvPowerSeries σ R) ∣ f - f₀ := by
      rw [X_dvd_iff]
      intro d hd
      rw [map_sub, hf₀, if_pos hd, sub_self]
    obtain ⟨q', hq'⟩ := hdvd
    obtain ⟨q, hq⟩ := ih f₀ (by
      intro d hd
      rw [hf₀]
      split_ifs with hds
      · exact hf d (fun t ht => by
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact hds
          · exact hd t ht)
      · rfl)
    refine ⟨Function.update q s q', ?_⟩
    rw [Finset.sum_insert hs, Function.update_self]
    have hrest : ∑ t ∈ T, X t * Function.update q s q' t = ∑ t ∈ T, X t * q t := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Function.update_of_ne (ne_of_mem_of_not_mem ht hs)]
    rw [hrest, ← hq, ← hq']
    ring

private theorem _root_.P2mPiDescent85.constantCoeff_subst_of_constantCoeff_zero [Finite σ] {τ : Type*}
    {a : σ → MvPowerSeries τ R} (ha : ∀ i, (a i).constantCoeff = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hsa : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hsplit : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  have hz : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  rw [hsplit, subst_add hsa, subst_C, map_add, constantCoeff_C, constantCoeff_subst_eq_zero hsa ha hz,
    add_zero, map_add, constantCoeff_C, hz, add_zero]

p2m_export "P2mPiDescent85" "constantCoeff_subst_of_constantCoeff_zero"

theorem injective_of_existsUnique_expansion {A : Type*} [CommRing A] [NoZeroDivisors A]
    [Nontrivial A] (φ : A →+* A) {ι : Type*} [Fintype ι] (b : ι → A)
    (hb : ∀ x : A, ∃! c : ι → A, x = ∑ i, φ (c i) * b i) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨c₁, hc₁, huniq⟩ := hb 1
  have hc₁' : (1 : A) = ∑ i, φ (c₁ i + c * c₁ i) * b i := by
    refine hc₁.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_add, map_mul, hc, zero_mul, add_zero]
  have hcc : (fun i => c₁ i + c * c₁ i) = c₁ := huniq _ hc₁'
  by_contra hne
  have hzero : ∀ i, c₁ i = 0 := fun i => by
    have hi := congrFun hcc i
    have hmul : c * c₁ i = 0 := by
      have := congrArg (fun t => t - c₁ i) hi
      simpa using this
    exact (mul_eq_zero.mp hmul).resolve_left hne
  have : (1 : A) = 0 := by
    rw [hc₁]
    exact Finset.sum_eq_zero fun i _ => by rw [hzero i, map_zero, zero_mul]
  exact one_ne_zero this

theorem subst_injective_of_finite_quotient {k : Type u} [Field k] {σ : Type} [Fintype σ]
    [DecidableEq σ] (g : σ → MvPowerSeries σ k) (hg : ∀ i, constantCoeff (g i) = 0)
    (hfin : Module.Finite k (MvPowerSeries σ k ⧸ Ideal.span (Set.range g))) :
    Function.Injective (subst g : MvPowerSeries σ k → MvPowerSeries σ k) := by

  let d := Fintype.card σ
  let e : σ ≃ Fin d := Fintype.equivFin σ
  let ρ : MvPowerSeries σ k ≃ₐ[k] MvPowerSeries (Fin d) k := renameEquiv k e
  have hρ : ∀ f : MvPowerSeries σ k, ρ f = rename e f := fun f => rfl
  let g' : Fin d → MvPowerSeries (Fin d) k := fun i => ρ (g (e.symm i))
  have hg' : ∀ i, constantCoeff (g' i) = 0 := fun i => by
    show constantCoeff (rename e (g (e.symm i))) = 0
    rw [constantCoeff_rename, hg]
  have hsg : HasSubst g := hasSubst_of_constantCoeff_zero hg
  have hsg' : HasSubst g' := hasSubst_of_constantCoeff_zero hg'

  have hcomm : ∀ f : MvPowerSeries σ k, subst g' (ρ f) = ρ (subst g f) := by
    intro f
    rw [hρ, hρ, rename_eq_subst, rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp e) hsg',
      subst_comp_subst_apply hsg (HasSubst.X_comp e)]
    congr 1
    funext s
    show subst g' (X (e s)) = subst (X ∘ e) (g s)
    rw [subst_X hsg']
    show ρ (g (e.symm (e s))) = _
    rw [Equiv.symm_apply_apply, hρ, rename_eq_subst]

  have hIJ : Ideal.span (Set.range g') = (Ideal.span (Set.range g)).map (ρ : MvPowerSeries σ k →+* _) := by
    rw [Ideal.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨g (e.symm i), ⟨e.symm i, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨s, rfl⟩, rfl⟩
      exact ⟨e s, by simp [g']⟩
  have hfin' : Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g')) :=
    Module.Finite.equiv (Ideal.quotientEquivAlg (Ideal.span (Set.range g)) (Ideal.span (Set.range g'))
      ρ hIJ).toLinearEquiv
  obtain ⟨-, -, b, hb⟩ :=
    MvPowerSeries.finite_flat_exists_basis_substAlgHom_of_finite_quotient g' hg' hfin'
  have hinj := injective_of_existsUnique_expansion (substAlgHom (R := k) hsg').toRingHom b (fun x => by
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom] using hb x)
  intro x y hxy
  apply ρ.injective
  apply hinj
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom]
  rw [hcomm, hcomm, hxy]

end PowerSeries
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.P2mPiDescent72"

section Universal

variable {k : Type u} [CommRing k] {n : ℕ}

def Xl : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k := fun l => X (Sum.inl l)

def Xr : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k := fun l => X (Sum.inr l)

theorem constantCoeff_Xl : ∀ i, (Xl (n := n) (k := k) i).constantCoeff = 0 :=
  fun _ => constantCoeff_X _

theorem constantCoeff_Xr : ∀ i, (Xr (n := n) (k := k) i).constantCoeff = 0 :=
  fun _ => constantCoeff_X _

end Universal
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.P2mPiDescent72"

section Coefficients

variable {k : Type u} [CommRing k] {n : ℕ}

theorem coeff_subst_elim_Xl_zero (G : MvPowerSeries (Fin n ⊕ Fin n) k) (d : Fin n ⊕ Fin n →₀ ℕ)
    (hd : ∀ j, d (Sum.inr j) = 0) :
    coeff d (subst (Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) G)
      = coeff d G := by
  classical
  have hθ : HasSubst (Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
    MvFormalGroup.hasSubst_elim constantCoeff_Xl (fun _ => map_zero _)
  rw [coeff_subst hθ]

  have hprod : ∀ e : Fin n ⊕ Fin n →₀ ℕ,
      (e.prod fun s m => (Sum.elim (Xl (n := n) (k := k))
        (fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) s) ^ m) =
        if ∀ j, e (Sum.inr j) = 0 then monomial e 1 else 0 := by
    intro e
    split_ifs with he
    · rw [monomial_one_eq]
      apply Finset.prod_congr rfl
      intro s hs
      rcases s with l | j
      · rfl
      · exact absurd (he j) (Finsupp.mem_support_iff.mp hs)
    · push Not at he
      obtain ⟨j, hj⟩ := he
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hj)
      show (0 : MvPowerSeries (Fin n ⊕ Fin n) k) ^ e (Sum.inr j) = 0
      exact zero_pow hj
  simp only [hprod]
  rw [finsum_eq_single _ d]
  · rw [if_pos hd, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
  · intro e hed
    split_ifs with he
    · rw [coeff_monomial, if_neg (Ne.symm hed), smul_zero]
    · rw [map_zero, smul_zero]

theorem exists_eq_sum_Xr_mul (G : MvPowerSeries (Fin n ⊕ Fin n) k)
    (hG : subst (Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) G = 0) :
    ∃ q : Fin n → MvPowerSeries (Fin n ⊕ Fin n) k, G = ∑ j, X (Sum.inr j) * q j := by
  classical
  let T : Finset (Fin n ⊕ Fin n) := Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩
  obtain ⟨q, hq⟩ := exists_eq_sum_X_mul T G (by
    intro d hd
    have hd' : ∀ j, d (Sum.inr j) = 0 := fun j => hd (Sum.inr j) (by simp [T])
    rw [← coeff_subst_elim_Xl_zero G d hd', hG, map_zero])
  refine ⟨fun j => q (Sum.inr j), ?_⟩
  rw [hq, Finset.sum_map]
  rfl

end Coefficients
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.P2mPiDescent72"

section Injectivity

variable {k : Type u} [Field k] {n : ℕ} (F : MvFormalGroup n k)

theorem subst_elim_nth_Xr_injective {φ : Fin n → MvPowerSeries (Fin n) k} (hφ0 : ∀ i, constantCoeff (φ i) = 0)
    (hfin : Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range φ))) :
    Function.Injective (subst (Sum.elim ((fun i => subst (Xl (n := n) (k := k)) (φ i))) Xr) :
      MvPowerSeries (Fin n ⊕ Fin n) k → MvPowerSeries (Fin n ⊕ Fin n) k) := by
  classical
  set s₁ : Fin n ⊕ Fin n → MvPowerSeries (Fin n ⊕ Fin n) k := Sum.elim ((fun i => subst Xl (φ i))) Xr with hs₁
  have hs₁0 : ∀ t, constantCoeff (s₁ t) = 0 := by
    rintro (i | i)
    · exact (fun i => constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero constantCoeff_Xl) constantCoeff_Xl (hφ0 i)) i
    · exact constantCoeff_X _

  let J₁ : Ideal (MvPowerSeries (Fin n ⊕ Fin n) k) := Ideal.span (Set.range s₁)
  have hXl : HasSubst (Xl (n := n) (k := k)) := hasSubst_of_constantCoeff_zero constantCoeff_Xl
  let φ₁ : MvPowerSeries (Fin n) k →ₐ[k] MvPowerSeries (Fin n ⊕ Fin n) k ⧸ J₁ :=
    (Ideal.Quotient.mkₐ k J₁).comp (substAlgHom hXl)
  have hφ₁ : ∀ f, φ₁ f = Ideal.Quotient.mk J₁ (subst Xl f) := fun f => by
    simp [φ₁, coe_substAlgHom]
  have hsurj : Function.Surjective φ₁ := by
    intro y
    obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨subst (Sum.elim X fun _ => (0 : MvPowerSeries (Fin n) k)) G, ?_⟩
    rw [hφ₁, Ideal.Quotient.eq]

    have hX0 : HasSubst (Sum.elim X fun _ => (0 : MvPowerSeries (Fin n) k)) :=
      MvFormalGroup.hasSubst_elim (fun j => constantCoeff_X j) (fun _ => map_zero _)
    have hcomp : subst Xl (subst (Sum.elim X fun _ => (0 : MvPowerSeries (Fin n) k)) G) =
        subst (Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) G := by
      rw [subst_comp_subst_apply hX0 hXl]
      congr 1
      funext t
      rcases t with j | j
      · exact subst_X hXl j
      · show subst Xl (0 : MvPowerSeries (Fin n) k) = 0
        rw [← coe_substAlgHom hXl, map_zero]
    have hkill : subst (Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k))
        (subst (Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) G - G)
        = 0 := by
      have hθ : HasSubst (Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
        MvFormalGroup.hasSubst_elim constantCoeff_Xl (fun _ => map_zero _)
      rw [subst_sub hθ, subst_comp_subst_apply hθ hθ]
      have hfam : (fun t : Fin n ⊕ Fin n => subst (Sum.elim (Xl (n := n) (k := k))
          fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) (Sum.elim (Xl (n := n) (k := k))
            (fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) t)) =
          Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k) := by
        funext t
        rcases t with j | j
        · exact subst_X hθ (Sum.inl j)
        · show subst _ (0 : MvPowerSeries (Fin n ⊕ Fin n) k) = 0
          rw [← coe_substAlgHom hθ, map_zero]
      rw [hfam, sub_self]
    obtain ⟨q, hq⟩ := exists_eq_sum_Xr_mul _ hkill
    rw [hcomp, hq]
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨Sum.inr j, ?_⟩)
    rfl
  have hker : ∀ f ∈ Ideal.span (Set.range (φ)), φ₁ f = 0 := by
    have hle : Ideal.span (Set.range (φ)) ≤ RingHom.ker φ₁.toRingHom := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hφ₁,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨Sum.inl i, rfl⟩
    intro f hf
    have := hle hf
    rwa [RingHom.mem_ker] at this
  haveI := hfin
  have hfin₁ : Module.Finite k (MvPowerSeries (Fin n ⊕ Fin n) k ⧸ J₁) := by
    refine Module.Finite.of_surjective
      (Ideal.Quotient.liftₐ (Ideal.span (Set.range (φ))) φ₁ hker).toLinearMap ?_
    intro y
    obtain ⟨f, rfl⟩ := hsurj y
    exact ⟨Ideal.Quotient.mk _ f, rfl⟩
  exact subst_injective_of_finite_quotient s₁ hs₁0 hfin₁

theorem subst_elim_nth_nth_injective {φ : Fin n → MvPowerSeries (Fin n) k} (hφ0 : ∀ i, constantCoeff (φ i) = 0)
    (hfin : Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range φ))) :
    Function.Injective (subst (Sum.elim ((fun i => subst (Xl (n := n) (k := k)) (φ i))) ((fun i => subst Xr (φ i)))) :
      MvPowerSeries (Fin n ⊕ Fin n) k → MvPowerSeries (Fin n ⊕ Fin n) k) := by
  have h₁ := subst_elim_nth_Xr_injective hφ0 hfin
  have hs₁ : HasSubst (Sum.elim ((fun i => subst (Xl (n := n) (k := k)) (φ i))) Xr) :=
    MvFormalGroup.hasSubst_elim ((fun i => constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero constantCoeff_Xl) constantCoeff_Xl (hφ0 i))) constantCoeff_Xr
  have hs₂ : HasSubst (Sum.elim (Xl (n := n) (k := k)) ((fun i => subst Xr (φ i)))) :=
    MvFormalGroup.hasSubst_elim constantCoeff_Xl ((fun i => constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero constantCoeff_Xr) constantCoeff_Xr (hφ0 i)))
  have hXl : HasSubst (Xl (n := n) (k := k)) := hasSubst_of_constantCoeff_zero constantCoeff_Xl
  have hXr : HasSubst (Xr (n := n) (k := k)) := hasSubst_of_constantCoeff_zero constantCoeff_Xr

  let sw : MvPowerSeries (Fin n ⊕ Fin n) k ≃ₐ[k] MvPowerSeries (Fin n ⊕ Fin n) k :=
    renameEquiv k (Equiv.sumComm (Fin n) (Fin n))
  have hsw : ∀ f, sw f = subst (Sum.elim (Xr (n := n) (k := k)) Xl) f := by
    intro f
    show rename (Equiv.sumComm (Fin n) (Fin n)) f = _
    rw [rename_eq_subst]
    congr 1
    funext t; rcases t with j | j <;> rfl
  have hswap : HasSubst (Sum.elim (Xr (n := n) (k := k)) Xl) := MvFormalGroup.hasSubst_elim constantCoeff_Xr constantCoeff_Xl

  have hu : (fun t => subst (Sum.elim ((fun i => subst (Xl (n := n) (k := k)) (φ i))) Xr)
      (Sum.elim (Xr (n := n) (k := k)) Xl t)) = Sum.elim Xr ((fun i => subst Xl (φ i))) := by
    funext t
    rcases t with j | j
    · show subst (Sum.elim ((fun i => subst Xl (φ i))) Xr) (X (Sum.inr j)) = _
      rw [subst_X hs₁]
      rfl
    · show subst (Sum.elim ((fun i => subst Xl (φ i))) Xr) (X (Sum.inl j)) = _
      rw [subst_X hs₁]
      rfl
  have hu' : HasSubst (Sum.elim (Xr (n := n) (k := k)) ((fun i => subst Xl (φ i)))) :=
    MvFormalGroup.hasSubst_elim constantCoeff_Xr ((fun i => constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero constantCoeff_Xl) constantCoeff_Xl (hφ0 i)))
  have hv : (fun t => subst (Sum.elim (Xr (n := n) (k := k)) Xl)
      (Sum.elim (Xr (n := n) (k := k)) ((fun i => subst Xl (φ i))) t)) = Sum.elim Xl ((fun i => subst Xr (φ i))) := by
    funext t
    rcases t with j | j
    · show subst (Sum.elim Xr Xl) (X (Sum.inr j)) = _
      rw [subst_X hswap]
      rfl
    · show subst (Sum.elim Xr Xl) (subst Xl (φ j)) = subst Xr (φ j)
      rw [subst_comp_subst_apply hXl hswap]
      congr 1
      funext l
      show subst (Sum.elim Xr Xl) (X (Sum.inl l)) = _
      rw [subst_X hswap]
      rfl
  have hconj : ∀ f : MvPowerSeries (Fin n ⊕ Fin n) k, subst (Sum.elim (Xl (n := n) (k := k)) ((fun i => subst Xr (φ i)))) f =
      sw (subst (Sum.elim ((fun i => subst (Xl (n := n) (k := k)) (φ i))) Xr) (sw f)) := by
    intro f
    rw [hsw, hsw, subst_comp_subst_apply hswap hs₁, hu, subst_comp_subst_apply hu' hswap, hv]
  have h₂ : Function.Injective (subst (Sum.elim (Xl (n := n) (k := k)) ((fun i => subst Xr (φ i)))) :
      MvPowerSeries (Fin n ⊕ Fin n) k → MvPowerSeries (Fin n ⊕ Fin n) k) := by
    intro x y hxy
    rw [hconj, hconj] at hxy
    exact sw.injective (h₁ (sw.injective hxy))

  have hcomp : ∀ f : MvPowerSeries (Fin n ⊕ Fin n) k, subst (Sum.elim ((fun i => subst (Xl (n := n) (k := k)) (φ i))) ((fun i => subst Xr (φ i)))) f =
      subst (Sum.elim (Xl (n := n) (k := k)) ((fun i => subst Xr (φ i))))
        (subst (Sum.elim ((fun i => subst (Xl (n := n) (k := k)) (φ i))) Xr) f) := by
    intro f
    rw [subst_comp_subst_apply hs₁ hs₂]
    congr 1
    funext t
    rcases t with j | j
    · show subst Xl (φ j) = subst (Sum.elim Xl ((fun i => subst Xr (φ i)))) (subst Xl (φ j))
      rw [subst_comp_subst_apply hXl hs₂]
      congr 1
      funext l
      show Xl l = subst (Sum.elim Xl ((fun i => subst Xr (φ i)))) (X (Sum.inl l))
      rw [subst_X hs₂, Sum.elim_inl]
    · show subst Xr (φ j) = subst (Sum.elim Xl ((fun i => subst Xr (φ i)))) (X (Sum.inr j))
      rw [subst_X hs₂, Sum.elim_inr]
  intro x y hxy
  rw [hcomp, hcomp] at hxy
  exact h₁ (h₂ hxy)

end Injectivity
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.P2mPiDescent72"

end P2mPiDescent85
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.P2mPiDescent72"

namespace MvFormalGroup
p2m_export "MvFormalGroup" "subst_zero_of_constantCoeff_eq_zero hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm subst_elim_zero_X IsComm hasSubst_toPowerSeries map mk toPowerSeries constantCoeff_eq_zero subst_elim_zero_right addCoboundary IsSymmTwoCocycle"
p2m_open "MvFormalGroup"

variable {g : ℕ} {R : Type*} [CommRing R]

namespace C1Kit

variable {τ : Type*} (F : MvFormalGroup g R) {Γ : MvPowerSeries (Fin g ⊕ Fin g) R}

theorem constantCoeff_XL (l : Fin g) :
    constantCoeff ((fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) l) = 0 :=
  constantCoeff_X _

theorem constantCoeff_XR (l : Fin g) :
    constantCoeff ((fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) l) = 0 :=
  constantCoeff_X _

theorem symm_elim (hΓ : F.IsSymmTwoCocycle Γ) {a b : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) :
    subst (Sum.elim b a) Γ = subst (Sum.elim a b) Γ := by
  have hT : HasSubst (Sum.elim a b) := hasSubst_elim ha hb
  have hswap : HasSubst (Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [constantCoeff_X])
  have key := congrArg (subst (R := R) (Sum.elim a b)) hΓ.symm
  rw [subst_comp_subst_apply hswap hT] at key
  have hfam : (fun s => subst (Sum.elim a b) ((Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) s)) = Sum.elim b a := by
    funext s
    rcases s with j | j <;> simp [subst_X hT]
  rw [hfam] at key
  exact key

theorem cocycle_elim (hΓ : F.IsSymmTwoCocycle Γ) {a b c : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0)
    (hc : ∀ i, (c i).constantCoeff = 0) :
    subst (Sum.elim (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) c) Γ
        + subst (Sum.elim a b) Γ
      = subst (Sum.elim a fun j => subst (Sum.elim b c) (F.toPowerSeries j)) Γ
        + subst (Sum.elim b c) Γ := by
  have hT0 : ∀ s : Fin g ⊕ (Fin g ⊕ Fin g),
      ((Sum.elim a (Sum.elim b c)) s).constantCoeff = 0 := by
    rintro (j | j | j)
    exacts [ha j, hb j, hc j]
  have hT : HasSubst (Sum.elim a (Sum.elim b c)) := hasSubst_of_constantCoeff_zero hT0
  have hzB : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
      (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun l => X (Sum.inr (Sum.inl l))) s).constantCoeff = 0 := by
    rintro (l | l) <;> simp [constantCoeff_X]
  have hzC : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
      (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun l => X (Sum.inr (Sum.inr l))) s).constantCoeff = 0 := by
    rintro (l | l) <;> simp [constantCoeff_X]
  have hB := hasSubst_of_constantCoeff_zero hzB
  have hC := hasSubst_of_constantCoeff_zero hzC
  have hA : HasSubst (Sum.elim
      (fun j => subst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
      fun j => X (Sum.inr (Sum.inr j))) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero hB hzB (F.constantCoeff_eq_zero j)
    · exact constantCoeff_X _
  have hA' : HasSubst (Sum.elim
      (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun j => subst (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact constantCoeff_X _
    · exact constantCoeff_subst_eq_zero hC hzC (F.constantCoeff_eq_zero j)
  have key := congrArg (subst (R := R) (Sum.elim a (Sum.elim b c))) hΓ.cocycle
  rw [subst_add hT, subst_add hT, subst_comp_subst_apply hA hT, subst_comp_subst_apply hA' hT,
    subst_comp_subst_apply hB hT, subst_comp_subst_apply hC hT] at key
  have hBfam : (fun t => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun l => X (Sum.inr (Sum.inl l))) t)) = Sum.elim a b := by
    funext t
    rcases t with l | l <;> simp [subst_X hT]
  have hCfam : (fun t => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun l => X (Sum.inr (Sum.inr l))) t)) = Sum.elim b c := by
    funext t
    rcases t with l | l <;> simp [subst_X hT]
  have hAfam : (fun s => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun j => subst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
      fun j => X (Sum.inr (Sum.inr j))) s))
      = Sum.elim (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) c := by
    funext s
    rcases s with j | j
    · show subst (Sum.elim a (Sum.elim b c)) (subst (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
        = subst (Sum.elim a b) (F.toPowerSeries j)
      rw [subst_comp_subst_apply hB hT, hBfam]
    · simp [subst_X hT]
  have hA'fam : (fun s => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun j => subst (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j)) s))
      = Sum.elim a fun j => subst (Sum.elim b c) (F.toPowerSeries j) := by
    funext s
    rcases s with j | j
    · simp [subst_X hT]
    · show subst (Sum.elim a (Sum.elim b c)) (subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j))
        = subst (Sum.elim b c) (F.toPowerSeries j)
      rw [subst_comp_subst_apply hC hT, hCfam]
  rw [hAfam, hA'fam, hBfam, hCfam] at key
  exact key

theorem four_term [IsComm F] (hΓ : F.IsSymmTwoCocycle Γ) {a b c d : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0)
    (hc : ∀ i, (c i).constantCoeff = 0) (hd : ∀ i, (d i).constantCoeff = 0) :
    subst (Sum.elim (fun j => subst (Sum.elim a b) (F.toPowerSeries j))
        fun j => subst (Sum.elim c d) (F.toPowerSeries j)) Γ
        + subst (Sum.elim a b) Γ + subst (Sum.elim c d) Γ
      = subst (Sum.elim (fun j => subst (Sum.elim a c) (F.toPowerSeries j))
        fun j => subst (Sum.elim b d) (F.toPowerSeries j)) Γ
        + subst (Sum.elim a c) Γ + subst (Sum.elim b d) Γ := by
  have hab := constantCoeff_subst_elim F ha hb
  have hac := constantCoeff_subst_elim F ha hc
  have e1 := cocycle_elim F hΓ hab hc hd
  have e2 := cocycle_elim F hΓ hac hb hd
  have e3 := cocycle_elim F hΓ ha hb hc
  have e4 := cocycle_elim F hΓ ha hc hb
  have hcb : (fun j => subst (Sum.elim c b) (F.toPowerSeries j))
      = fun j => subst (Sum.elim b c) (F.toPowerSeries j) :=
    funext fun j => subst_elim_comm F hc hb j
  rw [hcb, symm_elim F hΓ hb hc] at e4
  have h6 : (fun j => subst (Sum.elim (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) c)
        (F.toPowerSeries j))
      = fun j => subst (Sum.elim (fun j => subst (Sum.elim a c) (F.toPowerSeries j)) b)
        (F.toPowerSeries j) := by
    funext j
    rw [subst_elim_assoc F ha hb hc j, ← hcb, ← subst_elim_assoc F ha hc hb j]
  rw [h6] at e1
  linear_combination e2 - e1 + e3 - e4

end C1Kit
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.P2mPiDescent72"

end MvFormalGroup
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.P2mPiDescent72"

namespace MvFormalGroup
p2m_export "MvFormalGroup" "subst_zero_of_constantCoeff_eq_zero hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm subst_elim_zero_X IsComm hasSubst_toPowerSeries map mk toPowerSeries constantCoeff_eq_zero subst_elim_zero_right addCoboundary IsSymmTwoCocycle"
namespace C1Kit
p2m_open "MvFormalGroup"

variable {g : ℕ} {R : Type*} [CommRing R] (F : MvFormalGroup g R) {Γ : MvPowerSeries (Fin g ⊕ Fin g) R}

noncomputable abbrev inL (φ : Fin g → MvPowerSeries (Fin g) R) : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R :=
  fun i => subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin g ⊕ Fin g) R)) (φ i)

noncomputable abbrev inR (φ : Fin g → MvPowerSeries (Fin g) R) : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R :=
  fun i => subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin g ⊕ Fin g) R)) (φ i)

theorem hasSubst_XL : HasSubst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_XR : HasSubst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

variable {φ ψ : Fin g → MvPowerSeries (Fin g) R}

theorem constantCoeff_inL (hφ : ∀ i, (φ i).constantCoeff = 0) (i : Fin g) :
    (inL φ i).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero hasSubst_XL (fun _ => constantCoeff_X _) (hφ i)

theorem constantCoeff_inR (hφ : ∀ i, (φ i).constantCoeff = 0) (i : Fin g) :
    (inR φ i).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero hasSubst_XR (fun _ => constantCoeff_X _) (hφ i)

theorem inL_addVia (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0) :
    inL (fun i => subst (Sum.elim φ ψ) (F.toPowerSeries i))
      = fun i => subst (Sum.elim (inL φ) (inL ψ)) (F.toPowerSeries i) := by
  funext i
  show subst _ (subst (Sum.elim φ ψ) (F.toPowerSeries i)) = _
  rw [subst_comp_subst_apply (hasSubst_elim hφ hψ) hasSubst_XL]
  congr 1
  funext s; rcases s with j | j <;> rfl

theorem inR_addVia (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0) :
    inR (fun i => subst (Sum.elim φ ψ) (F.toPowerSeries i))
      = fun i => subst (Sum.elim (inR φ) (inR ψ)) (F.toPowerSeries i) := by
  funext i
  show subst _ (subst (Sum.elim φ ψ) (F.toPowerSeries i)) = _
  rw [subst_comp_subst_apply (hasSubst_elim hφ hψ) hasSubst_XR]
  congr 1
  funext s; rcases s with j | j <;> rfl

theorem subst_XL_subst_elim (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0)
    (f : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (fun m => (X (Sum.inl m) : MvPowerSeries (Fin g ⊕ Fin g) R)) (subst (Sum.elim φ ψ) f)
      = subst (Sum.elim (inL φ) (inL ψ)) f := by
  rw [subst_comp_subst_apply (hasSubst_elim hφ hψ) hasSubst_XL]
  congr 1
  funext s; rcases s with j | j <;> rfl

theorem subst_XR_subst_elim (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0)
    (f : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (fun m => (X (Sum.inr m) : MvPowerSeries (Fin g ⊕ Fin g) R)) (subst (Sum.elim φ ψ) f)
      = subst (Sum.elim (inR φ) (inR ψ)) f := by
  rw [subst_comp_subst_apply (hasSubst_elim hφ hψ) hasSubst_XR]
  congr 1
  funext s; rcases s with j | j <;> rfl

theorem subst_law_subst_elim (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i))
    (hψF : ∀ i, subst F.toPowerSeries (ψ i) = subst (Sum.elim (inL ψ) (inR ψ)) (F.toPowerSeries i))
    (f : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst F.toPowerSeries (subst (Sum.elim φ ψ) f)
      = subst (Sum.elim (fun i => subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i))
          fun i => subst (Sum.elim (inL ψ) (inR ψ)) (F.toPowerSeries i)) f := by
  rw [subst_comp_subst_apply (hasSubst_elim hφ hψ) F.hasSubst_toPowerSeries]
  congr 1
  funext s; rcases s with j | j
  · exact hφF j
  · exact hψF j

theorem pull_addVia [IsComm F] (hΓ : F.IsSymmTwoCocycle Γ)
    (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i))
    (hψF : ∀ i, subst F.toPowerSeries (ψ i) = subst (Sum.elim (inL ψ) (inR ψ)) (F.toPowerSeries i)) :
    subst (Sum.elim (inL fun i => subst (Sum.elim φ ψ) (F.toPowerSeries i))
        (inR fun i => subst (Sum.elim φ ψ) (F.toPowerSeries i))) Γ
      = subst (Sum.elim (inL φ) (inR φ)) Γ + subst (Sum.elim (inL ψ) (inR ψ)) Γ
        + F.addCoboundary (subst (Sum.elim φ ψ) Γ) := by
  rw [inL_addVia F hφ hψ, inR_addVia F hφ hψ, addCoboundary, subst_law_subst_elim F hφ hψ hφF hψF,
    subst_XL_subst_elim hφ hψ, subst_XR_subst_elim hφ hψ]
  have h4 := four_term F hΓ (constantCoeff_inL hφ) (constantCoeff_inL hψ) (constantCoeff_inR hφ)
    (constantCoeff_inR hψ)
  linear_combination h4

theorem constantCoeff_subst_elim_cocycle (hΓ : F.IsSymmTwoCocycle Γ) {τ : Type*}
    {a b : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) :
    (subst (Sum.elim a b) Γ).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_elim ha hb) (by rintro (s | s); exacts [ha s, hb s])
    hΓ.constantCoeff_eq_zero

end MvFormalGroup.C1Kit
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.P2mPiDescent72"
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.P2mPiDescent72"

namespace MvFormalGroup
p2m_export "MvFormalGroup" "subst_zero_of_constantCoeff_eq_zero hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm subst_elim_zero_X IsComm hasSubst_toPowerSeries map mk toPowerSeries constantCoeff_eq_zero subst_elim_zero_right addCoboundary IsSymmTwoCocycle"
namespace C1Kit
p2m_open "MvFormalGroup"

variable {g : ℕ} {R : Type*} [CommRing R] (F : MvFormalGroup g R) {Γ : MvPowerSeries (Fin g ⊕ Fin g) R}
variable {φ ψ : Fin g → MvPowerSeries (Fin g) R}

theorem subst_subst_pull {τ : Type*} {T : Fin g ⊕ Fin g → MvPowerSeries τ R} (hT : HasSubst T)
    (hφ : ∀ i, (φ i).constantCoeff = 0) (f : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst T (subst (Sum.elim (inL φ) (inR φ)) f)
      = subst (Sum.elim (fun i => subst (fun m => T (Sum.inl m)) (φ i))
          fun i => subst (fun m => T (Sum.inr m)) (φ i)) f := by
  rw [subst_comp_subst_apply (hasSubst_elim (constantCoeff_inL hφ) (constantCoeff_inR hφ)) hT]
  congr 1
  funext s; rcases s with j | j
  · show subst T (subst _ (φ j)) = _
    rw [subst_comp_subst_apply hasSubst_XL hT]
    congr 1; funext m; exact subst_X hT _
  · show subst T (subst _ (φ j)) = _
    rw [subst_comp_subst_apply hasSubst_XR hT]
    congr 1; funext m; exact subst_X hT _

theorem pull_comp (hφ : ∀ i, (φ i).constantCoeff = 0) (hψ : ∀ i, (ψ i).constantCoeff = 0)
    (f : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (Sum.elim (inL fun i => subst ψ (φ i)) (inR fun i => subst ψ (φ i))) f
      = subst (Sum.elim (inL ψ) (inR ψ)) (subst (Sum.elim (inL φ) (inR φ)) f) := by
  rw [subst_subst_pull (hasSubst_elim (constantCoeff_inL hψ) (constantCoeff_inR hψ)) hφ]
  congr 1
  funext s; rcases s with j | j
  · show subst _ (subst ψ (φ j)) = _
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hψ) hasSubst_XL]
    rfl
  · show subst _ (subst ψ (φ j)) = _
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hψ) hasSubst_XR]
    rfl

theorem pull_X (f : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (Sum.elim (inL fun i => (X i : MvPowerSeries (Fin g) R)) (inR fun i => X i)) f = f := by
  have h : Sum.elim (inL fun i => (X i : MvPowerSeries (Fin g) R)) (inR fun i => X i)
      = (X : Fin g ⊕ Fin g → MvPowerSeries (Fin g ⊕ Fin g) R) := by
    funext s; rcases s with j | j
    · exact subst_X hasSubst_XL j
    · exact subst_X hasSubst_XR j
  rw [h, subst_self]; rfl

theorem symm_pull (hΓ : F.IsSymmTwoCocycle Γ) (hφ : ∀ i, (φ i).constantCoeff = 0) :
    subst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R)) fun j => X (Sum.inl j))
        (subst (Sum.elim (inL φ) (inR φ)) Γ)
      = subst (Sum.elim (inL φ) (inR φ)) Γ := by
  have hswap : HasSubst (Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R)) fun j => X (Sum.inl j)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [constantCoeff_X])
  rw [subst_subst_pull hswap hφ]
  exact symm_elim F hΓ (constantCoeff_inL hφ) (constantCoeff_inR hφ)

section ThreeBlocks

noncomputable abbrev B1 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R := fun l => X (Sum.inl l)
noncomputable abbrev B2 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R := fun l => X (Sum.inr (Sum.inl l))
noncomputable abbrev B3 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R := fun l => X (Sum.inr (Sum.inr l))

theorem cB1 (l : Fin g) : ((B1 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R) l).constantCoeff = 0 :=
  constantCoeff_X _
theorem cB2 (l : Fin g) : ((B2 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R) l).constantCoeff = 0 :=
  constantCoeff_X _
theorem cB3 (l : Fin g) : ((B3 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R) l).constantCoeff = 0 :=
  constantCoeff_X _

noncomputable abbrev atB (B : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R)
    (φ : Fin g → MvPowerSeries (Fin g) R) : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R :=
  fun i => subst B (φ i)

theorem constantCoeff_atB {B : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R}
    (hB : ∀ l, (B l).constantCoeff = 0) (hφ : ∀ i, (φ i).constantCoeff = 0) (i : Fin g) :
    (atB B φ i).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hB) hB (hφ i)

theorem subst_lawpair (hφ : ∀ i, (φ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i))
    {Bi Bj : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R}
    (hBi : ∀ l, (Bi l).constantCoeff = 0) (hBj : ∀ l, (Bj l).constantCoeff = 0) (i : Fin g) :
    subst (fun m => subst (Sum.elim Bi Bj) (F.toPowerSeries m)) (φ i)
      = subst (Sum.elim (atB Bi φ) (atB Bj φ)) (F.toPowerSeries i) := by
  rw [← subst_comp_subst_apply F.hasSubst_toPowerSeries (hasSubst_elim hBi hBj), hφF i,
    subst_subst_pull (hasSubst_elim hBi hBj) hφ]
  rfl

theorem cocycle_pull (hΓ : F.IsSymmTwoCocycle Γ) (hφ : ∀ i, (φ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i)) :
    subst
        (Sum.elim
          (fun j => subst
            (Sum.elim
              (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
              fun l => X (Sum.inr (Sum.inl l)))
            (F.toPowerSeries j))
          fun j => X (Sum.inr (Sum.inr j)))
        (subst (Sum.elim (inL φ) (inR φ)) Γ)
      + subst
        (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inl l)))
        (subst (Sum.elim (inL φ) (inR φ)) Γ)
      =
    subst
        (Sum.elim
          (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun j => subst
            (Sum.elim
              (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
              fun l => X (Sum.inr (Sum.inr l)))
            (F.toPowerSeries j))
        (subst (Sum.elim (inL φ) (inR φ)) Γ)
      + subst
        (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inr l)))
        (subst (Sum.elim (inL φ) (inR φ)) Γ) := by
  have hB12 : HasSubst (Sum.elim (B1 (g := g) (R := R)) B2) := hasSubst_elim cB1 cB2
  have hB23 : HasSubst (Sum.elim (B2 (g := g) (R := R)) B3) := hasSubst_elim cB2 cB3
  have hA : HasSubst (Sum.elim (fun j => subst (Sum.elim (B1 (g := g) (R := R)) B2) (F.toPowerSeries j)) B3) :=
    hasSubst_elim (constantCoeff_subst_elim F cB1 cB2) cB3
  have hA' : HasSubst (Sum.elim B1 fun j => subst (Sum.elim (B2 (g := g) (R := R)) B3) (F.toPowerSeries j)) :=
    hasSubst_elim cB1 (constantCoeff_subst_elim F cB2 cB3)
  show subst (Sum.elim (fun j => subst (Sum.elim B1 B2) (F.toPowerSeries j)) B3) _
      + subst (Sum.elim B1 B2) _
      = subst (Sum.elim B1 fun j => subst (Sum.elim B2 B3) (F.toPowerSeries j)) _ + subst (Sum.elim B2 B3) _
  rw [subst_subst_pull hA hφ, subst_subst_pull hB12 hφ, subst_subst_pull hA' hφ, subst_subst_pull hB23 hφ]
  have k := cocycle_elim F hΓ (constantCoeff_atB cB1 hφ) (constantCoeff_atB cB2 hφ) (constantCoeff_atB cB3 hφ)
  have h1 : (fun i => subst (fun m => Sum.elim (fun j => subst (Sum.elim B1 B2) (F.toPowerSeries j)) B3 (Sum.inl m))
      (φ i)) = fun i => subst (Sum.elim (atB B1 φ) (atB B2 φ)) (F.toPowerSeries i) :=
    funext fun i => subst_lawpair F hφ hφF cB1 cB2 i
  have h2 : (fun i => subst (fun m => Sum.elim B1 (fun j => subst (Sum.elim B2 B3) (F.toPowerSeries j)) (Sum.inr m))
      (φ i)) = fun i => subst (Sum.elim (atB B2 φ) (atB B3 φ)) (F.toPowerSeries i) :=
    funext fun i => subst_lawpair F hφ hφF cB2 cB3 i
  simp only [Sum.elim_inl, Sum.elim_inr] at h1 h2 ⊢
  rw [h1, h2]
  exact k

end ThreeBlocks
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.P2mPiDescent72"

theorem isSymmTwoCocycle_pull (hΓ : F.IsSymmTwoCocycle Γ) (hφ : ∀ i, (φ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i)) :
    F.IsSymmTwoCocycle (subst (Sum.elim (inL φ) (inR φ)) Γ) where
  constantCoeff_eq_zero := constantCoeff_subst_elim_cocycle F hΓ (constantCoeff_inL hφ) (constantCoeff_inR hφ)
  symm := symm_pull F hΓ hφ
  cocycle := cocycle_pull F hΓ hφ hφF

theorem pull_addCoboundary (hφ : ∀ i, (φ i).constantCoeff = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) = subst (Sum.elim (inL φ) (inR φ)) (F.toPowerSeries i))
    (g₁ : MvPowerSeries (Fin g) R) :
    subst (Sum.elim (inL φ) (inR φ)) (F.addCoboundary g₁) = F.addCoboundary (subst φ g₁) := by
  have hP : HasSubst (Sum.elim (inL φ) (inR φ)) := hasSubst_elim (constantCoeff_inL hφ) (constantCoeff_inR hφ)
  have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ
  rw [addCoboundary, addCoboundary, subst_sub hP, subst_sub hP,
    subst_comp_subst_apply F.hasSubst_toPowerSeries hP, subst_comp_subst_apply hasSubst_XL hP,
    subst_comp_subst_apply hasSubst_XR hP, subst_comp_subst_apply hφs F.hasSubst_toPowerSeries,
    subst_comp_subst_apply hφs hasSubst_XL, subst_comp_subst_apply hφs hasSubst_XR]
  congr 2
  · congr 1; funext i; exact (hφF i).symm
  · congr 1; funext m; exact subst_X hP _
  · congr 1; funext m; exact subst_X hP _

end MvFormalGroup.C1Kit
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.P2mPiDescent72"
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.P2mPiDescent72"

namespace MvFormalGroup
p2m_export "MvFormalGroup" "subst_zero_of_constantCoeff_eq_zero hasSubst_elim constantCoeff_subst_elim subst_elim_assoc subst_elim_comm subst_elim_zero_X IsComm hasSubst_toPowerSeries map mk toPowerSeries constantCoeff_eq_zero subst_elim_zero_right addCoboundary IsSymmTwoCocycle"
namespace C1Kit
p2m_open "MvFormalGroup"

variable {g : ℕ} {R : Type*} [CommRing R] {φ : Fin g → MvPowerSeries (Fin g) R}

theorem hasSubst_pull (hφ : ∀ i, (φ i).constantCoeff = 0) : HasSubst (Sum.elim (inL φ) (inR φ)) :=
  hasSubst_elim (constantCoeff_inL hφ) (constantCoeff_inR hφ)

theorem pull_smul_add (hφ : ∀ i, (φ i).constantCoeff = 0) (c : R) (Γ Γ' : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (Sum.elim (inL φ) (inR φ)) (c • Γ + Γ')
      = c • subst (Sum.elim (inL φ) (inR φ)) Γ + subst (Sum.elim (inL φ) (inR φ)) Γ' := by
  rw [← coe_substAlgHom (hasSubst_pull hφ), map_add, map_smul]

theorem pull_add (hφ : ∀ i, (φ i).constantCoeff = 0) (Γ Γ' : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (Sum.elim (inL φ) (inR φ)) (Γ + Γ') = subst (Sum.elim (inL φ) (inR φ)) Γ + subst (Sum.elim (inL φ) (inR φ)) Γ' :=
  subst_add (hasSubst_pull hφ) Γ Γ'

theorem pull_smul (hφ : ∀ i, (φ i).constantCoeff = 0) (c : R) (Γ : MvPowerSeries (Fin g ⊕ Fin g) R) :
    subst (Sum.elim (inL φ) (inR φ)) (c • Γ) = c • subst (Sum.elim (inL φ) (inR φ)) Γ := by
  rw [← coe_substAlgHom (hasSubst_pull hφ), map_smul]

theorem pull_zero (hφ : ∀ i, (φ i).constantCoeff = 0) :
    subst (Sum.elim (inL φ) (inR φ)) (0 : MvPowerSeries (Fin g ⊕ Fin g) R) = 0 := by
  rw [← coe_substAlgHom (hasSubst_pull hφ), map_zero]

end MvFormalGroup.C1Kit
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.P2mPiDescent72"
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.P2mPiDescent72"

open MvPowerSeries _root_.MvFormalGroup _root_.P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.MvFormalGroup MvFormalGroup.C1Kit in
open P2mPiDescent85 in

theorem solution
    {k : Type u} [Field k] {n : ℕ} (F : MvFormalGroup n k) [F.IsComm]
    (φ : Fin n → MvPowerSeries (Fin n) k) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφF : ∀ i, MvPowerSeries.subst F.toPowerSeries (φ i) =
      MvPowerSeries.subst
        (Sum.elim
          (fun j => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
          fun j => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
        (F.toPowerSeries i))
    (hfin : Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range φ)))
    (Γ : MvPowerSeries (Fin n ⊕ Fin n) k) (hΓ : F.IsSymmTwoCocycle Γ)
    (g : MvPowerSeries (Fin n) k) (hg0 : MvPowerSeries.constantCoeff g = 0)
    (hg : MvPowerSeries.subst
        (Sum.elim
          (fun j => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
          fun j => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
        Γ = F.addCoboundary g)
    (hgI : g ∈ Ideal.span (Set.range φ)) :
    ∃ G : MvPowerSeries (Fin n) k, MvPowerSeries.constantCoeff G = 0 ∧
      g = MvPowerSeries.subst φ G ∧ Γ = F.addCoboundary G := by
  classical
  have hXr : HasSubst (fun l : Fin n => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hP : HasSubst (Sum.elim (inL φ) (inR φ)) := hasSubst_pull hφ0

  have hzero : ∀ j : Fin n, ((fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) j).constantCoeff = 0 :=
    fun _ => map_zero _
  have h10 : subst (Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) Γ = 0 := by
    have hc := cocycle_elim F hΓ (a := Xl (n := n) (k := k)) (b := fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k))
      (c := fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) constantCoeff_Xl hzero hzero
    have hF0 : (fun j => subst (Sum.elim (Xl (n := n) (k := k)) fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k))
        (F.toPowerSeries j)) = Xl := funext fun j => subst_elim_zero_right F constantCoeff_Xl j
    have hzz : (Sum.elim (fun _ : Fin n => (0 : MvPowerSeries (Fin n ⊕ Fin n) k))
        fun _ : Fin n => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) = fun _ => 0 := by
      funext s; rcases s with j | j <;> rfl
    have h00 : (fun j => subst (Sum.elim (fun _ : Fin n => (0 : MvPowerSeries (Fin n ⊕ Fin n) k))
        fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) (F.toPowerSeries j))
        = fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k) := by
      funext j; rw [hzz]; exact subst_zero_of_constantCoeff_eq_zero (F.constantCoeff_eq_zero j)
    have hΓ00 : subst (Sum.elim (fun _ : Fin n => (0 : MvPowerSeries (Fin n ⊕ Fin n) k))
        fun _ => (0 : MvPowerSeries (Fin n ⊕ Fin n) k)) Γ = 0 := by
      rw [hzz]; exact subst_zero_of_constantCoeff_eq_zero hΓ.constantCoeff_eq_zero
    rw [hF0, h00, hΓ00] at hc
    linear_combination hc

  obtain ⟨qv, hq⟩ := exists_eq_sum_Xr_mul Γ h10

  have hf : subst F.toPowerSeries g -
      subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) g ∈
      Ideal.span (Set.range fun i => subst
        (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ i)) := by
    have e : subst F.toPowerSeries g - subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) g
        = F.addCoboundary g + subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) g := by
      rw [addCoboundary]; ring
    rw [e]
    refine Ideal.add_mem _ ?_ ?_
    · rw [← hg, hq, ← coe_substAlgHom hP, map_sum]
      refine Ideal.sum_mem _ fun j _ => ?_
      rw [map_mul]
      refine Ideal.mul_mem_right _ _ ?_
      rw [coe_substAlgHom, subst_X hP]
      exact Ideal.subset_span ⟨j, rfl⟩
    · obtain ⟨r, hr⟩ := Ideal.mem_span_range_iff_exists_fun.mp hgI
      rw [← hr, ← coe_substAlgHom hXr, map_sum]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [map_mul, coe_substAlgHom]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

  obtain ⟨G, hG, -⟩ := descent72 F φ hφ0 hφF hfin g hf

  have hG0 : constantCoeff G = 0 := by
    have h := congrArg constantCoeff hG
    rw [hg0, P2mPiDescent72.constantCoeff_subst_of_constantCoeff_zero hφ0] at h
    simpa using h.symm

  have hinj := subst_elim_nth_nth_injective hφ0 hfin
  refine ⟨G, hG0, hG, hinj ?_⟩
  show subst (Sum.elim (inL φ) (inR φ)) Γ = subst (Sum.elim (inL φ) (inR φ)) (F.addCoboundary G)
  rw [pull_addCoboundary F hφ0 hφF G, ← hG]
  exact hg

end
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.P2mPiDescent72"

end S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span
end P2MW
export P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span (solution)
