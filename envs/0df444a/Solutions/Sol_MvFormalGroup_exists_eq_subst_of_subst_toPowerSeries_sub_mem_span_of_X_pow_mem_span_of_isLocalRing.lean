-- Prove2me | solution 1 for MvFormalGroup.exists_eq_subst_of_subst_toPowerSeries_sub_mem_span_of_X_pow_mem_span_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c56782ac-cc44-5a31-84b4-3046b103b999

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvPowerSeries_existsUnique_eq_sum_subst_mul_of_basis_residueField_tensor_quotient
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_finite_and_finrank_kerAlgebra_varpi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_eq_subst_of_subst_toPowerSeries_sub_mem_span_of_X_pow_mem_span_of_isLocalRing
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace O4DescT72

local instance (priority := high) instModuleCoeff {k : Type} [CommRing k] [IsLocalRing k] {n : ℕ}
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

variable {k : Type} [CommRing k] [IsLocalRing k] {n : ℕ} (I : Ideal (MvPowerSeries (Fin n) k))

local notation "A" => MvPowerSeries (Fin n) k

theorem exists_pow_mk_X_eq_zero [Fact (∀ l : Fin n, IsNilpotent (Ideal.Quotient.mk I (X l : A)))] :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ l : Fin n, (Ideal.Quotient.mk I (X l)) ^ N₀ = 0 := by
  classical
  have h := (Fact.out : ∀ l : Fin n, IsNilpotent (Ideal.Quotient.mk I (X l : A)))
  choose N hN using h
  refine ⟨(∑ l, N l) + 1, Nat.succ_pos _, fun l => ?_⟩
  have hle : N l ≤ (∑ l, N l) + 1 :=
    (Finset.single_le_sum (fun i _ => Nat.zero_le (N i)) (Finset.mem_univ l)).trans (Nat.le_succ _)
  exact pow_eq_zero_of_le hle (hN l)

variable {I}

theorem exists_degree_bound [Fact (∀ l : Fin n, IsNilpotent (Ideal.Quotient.mk I (X l : A)))] :
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

theorem isNilpotent_tbar [Fact (∀ l : Fin n, IsNilpotent (Ideal.Quotient.mk I (X l : A)))] (l : Fin n) : IsNilpotent (tbar I l) := by
  obtain ⟨N₀, -, h⟩ := exists_pow_mk_X_eq_zero I
  exact ⟨N₀, h l⟩

theorem hasSubst_C_tbar [Fact (∀ l : Fin n, IsNilpotent (Ideal.Quotient.mk I (X l : A)))] {τ : Type*} :
    HasSubst (fun l => (C (tbar I l) : MvPowerSeries τ (A ⧸ I))) :=
  hasSubst_of_constantCoeff_nilpotent (fun l => by simpa using isNilpotent_tbar l)

theorem algebraMap_quot (x : k) : algebraMap k (A ⧸ I) x = Ideal.Quotient.mk I (C x) := by
  rw [← Ideal.Quotient.mk_algebraMap, MvPowerSeries.algebraMap_apply]
  rfl

theorem subst_C_tbar [Fact (∀ l : Fin n, IsNilpotent (Ideal.Quotient.mk I (X l : A)))] {τ : Type*} (g : A) :
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

variable {k : Type} [CommRing k] [IsLocalRing k] {n : ℕ} (F : MvFormalGroup n k)
  (I : Ideal (MvPowerSeries (Fin n) k)) [Module.Finite k (MvPowerSeries (Fin n) k ⧸ I)]
  [Module.Free k (MvPowerSeries (Fin n) k ⧸ I)]
  [Fact (∀ l : Fin n, IsNilpotent (Ideal.Quotient.mk I (X l : MvPowerSeries (Fin n) k)))]

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

omit [Module.Finite k (MvPowerSeries (Fin n) k ⧸ I)] [Module.Free k (MvPowerSeries (Fin n) k ⧸ I)]
  [Fact (∀ l : Fin n, IsNilpotent (Ideal.Quotient.mk I (X l : MvPowerSeries (Fin n) k)))] in
theorem algebraMap_eq (a : A) : algebraMap A B a = map (algebraMap k (A ⧸ I)) a := rfl

omit [Module.Finite k (MvPowerSeries (Fin n) k ⧸ I)] [Module.Free k (MvPowerSeries (Fin n) k ⧸ I)]
  [Fact (∀ l : Fin n, IsNilpotent (Ideal.Quotient.mk I (X l : MvPowerSeries (Fin n) k)))] in
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

theorem subst_torsorFam_subst_nth [F.IsComm] (F' : MvFormalGroup n k) {φ : Fin n → MvPowerSeries (Fin n) k}
    (hφ0 : ∀ i, constantCoeff (φ i) = 0)
    (hφF : ∀ i, subst F.toPowerSeries (φ i) =
      subst (Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
        (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j)))
        (F'.toPowerSeries i))
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
    exact MvFormalGroup.subst_elim_zero_right (F'.map (algebraMap k (A ⧸ I)))
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

omit [Module.Finite k (MvPowerSeries (Fin n) k ⧸ I)] [Module.Free k (MvPowerSeries (Fin n) k ⧸ I)]
  [Fact (∀ l : Fin n, IsNilpotent (Ideal.Quotient.mk I (X l : MvPowerSeries (Fin n) k)))] in
theorem coeff_coordFun {r : ℕ} (β : Module.Basis (Fin r) k (A ⧸ I)) (G : B) (j : Fin r) (d : Fin n →₀ ℕ) :
    coeff d (coordFun I β G j) = β.equivFun (coeff d G) j := rfl

omit [Module.Finite k (MvPowerSeries (Fin n) k ⧸ I)] [Module.Free k (MvPowerSeries (Fin n) k ⧸ I)]
  [Fact (∀ l : Fin n, IsNilpotent (Ideal.Quotient.mk I (X l : MvPowerSeries (Fin n) k)))] in
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

omit [Module.Finite k (MvPowerSeries (Fin n) k ⧸ I)] [Module.Free k (MvPowerSeries (Fin n) k ⧸ I)]
  [Fact (∀ l : Fin n, IsNilpotent (Ideal.Quotient.mk I (X l : MvPowerSeries (Fin n) k)))] in
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

end O4DescT72
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_of_subst_toPowerSeries_sub_mem_span_of_X_pow_mem_span_of_isLocalRing.O4DescT72"

end
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_of_subst_toPowerSeries_sub_mem_span_of_X_pow_mem_span_of_isLocalRing.O4DescT72"

attribute [local instance 10000] O4DescT72.instModuleCoeff

noncomputable section

open MvPowerSeries

namespace O4Desc

open O4DescT72

theorem hasSubst_Xl (n : ℕ) (k : Type) [CommRing k] [IsLocalRing k] :
    HasSubst (fun l : Fin n => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
  hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _

theorem hasSubst_Xr (n : ℕ) (k : Type) [CommRing k] [IsLocalRing k] :
    HasSubst (fun l : Fin n => (X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) :=
  hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _

abbrev inlAlgHom (n : ℕ) (k : Type) [CommRing k] [IsLocalRing k] :
    MvPowerSeries (Fin n) k →ₐ[k] MvPowerSeries (Fin n ⊕ Fin n) k :=
  substAlgHom (hasSubst_Xl n k)

abbrev inrAlgHom (n : ℕ) (k : Type) [CommRing k] [IsLocalRing k] :
    MvPowerSeries (Fin n) k →ₐ[k] MvPowerSeries (Fin n ⊕ Fin n) k :=
  substAlgHom (hasSubst_Xr n k)

theorem apply_mem_of_mem_smul_top {A : Type*} [CommRing A] {r : ℕ} (I : Ideal A)
    {x : Fin r → A} (hx : x ∈ I • (⊤ : Submodule A (Fin r → A))) (j : Fin r) : x j ∈ I := by
  refine Submodule.smul_induction_on (p := fun y => y j ∈ I) hx ?_ ?_
  · intro a ha m _
    show (a • m) j ∈ I
    rw [Pi.smul_apply, smul_eq_mul]
    exact I.mul_mem_right _ ha
  · intro y z hy hz
    show (y + z) j ∈ I
    rw [Pi.add_apply]
    exact I.add_mem hy hz

theorem torsor_descent_mod
    {k : Type} [CommRing k] [IsLocalRing k] [IsNoetherianRing k] {n : ℕ} (F : MvFormalGroup n k) [F.IsComm] (F' : MvFormalGroup n k)
    (φ : Fin n → MvPowerSeries (Fin n) k) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφF : ∀ i, MvPowerSeries.subst F.toPowerSeries (φ i) =
      MvPowerSeries.subst (Sum.elim
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
        (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j)))
        (F'.toPowerSeries i))
    (hNφ : ∃ N : ℕ, ∀ i : Fin n, (MvPowerSeries.X i : MvPowerSeries (Fin n) k) ^ N ∈ Ideal.span (Set.range φ))
    (hfin : Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range φ)))
    (hfree : Module.Free k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range φ)))
    (I : Ideal (MvPowerSeries (Fin n) k))
    (f : MvPowerSeries (Fin n) k)
    (hf : MvPowerSeries.subst F.toPowerSeries f -
        MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) f ∈
      Ideal.span (Set.range fun i => MvPowerSeries.subst
        (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ i)) ⊔
      I.map (inlAlgHom n k).toRingHom) :
    ∃ G : MvPowerSeries (Fin n) k, f - MvPowerSeries.subst φ G ∈ I := by
  classical

  set J : Ideal (MvPowerSeries (Fin n) k) := Ideal.span (Set.range (φ)) with hJ
  haveI : Module.Finite k (MvPowerSeries (Fin n) k ⧸ J) := hfin
  haveI : Module.Free k (MvPowerSeries (Fin n) k ⧸ J) := hfree
  haveI : Fact (∀ l : Fin n, IsNilpotent (Ideal.Quotient.mk J (X l : MvPowerSeries (Fin n) k))) := ⟨fun l => by
    obtain ⟨N, hN⟩ := hNφ
    exact ⟨N, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hN l⟩⟩
  have hmJ : ∀ i, φ i ∈ J := fun i => Ideal.subset_span ⟨i, rfl⟩
  have hnat0 : ∀ i, constantCoeff (φ i) = 0 := hφ0
  have hnat : HasSubst (φ) := hasSubst_of_constantCoeff_zero hnat0
  let θ : MvPowerSeries (Fin n) k →ₐ[k] MvPowerSeries (Fin n) k := substAlgHom hnat
  have hθ : ∀ c, θ c = subst φ c := fun c => congrFun (coe_substAlgHom hnat) c

  let βA := Module.finBasis k (MvPowerSeries (Fin n) k ⧸ J)
  choose b hbmk using fun j => Ideal.Quotient.mk_surjective (βA j)
  let β' := Algebra.TensorProduct.basis (IsLocalRing.ResidueField k) βA
  have hb : ∀ x : MvPowerSeries (Fin n) k, ∃! c : Fin (Module.finrank k (MvPowerSeries (Fin n) k ⧸ J)) → MvPowerSeries (Fin n) k,
      x = ∑ j, MvPowerSeries.subst φ (c j) * b j := fun x =>
    MvPowerSeries.existsUnique_eq_sum_subst_mul_of_basis_residueField_tensor_quotient (B := k) φ hφ0 hNφ hfin b β'
      (fun j => by
        show Algebra.TensorProduct.basis (IsLocalRing.ResidueField k) βA j = _
        rw [Algebra.TensorProduct.basis_apply, hbmk j]) x

  let ρ : MvPowerSeries (Fin n) k →ₐ[k] MvPowerSeries (Fin n) (MvPowerSeries (Fin n) k ⧸ J) :=
    substAlgHom (hasSubst_torsorFam F J)
  have hρ : ∀ x, ρ x = subst (torsorFam F J) x := fun x => congrFun (coe_substAlgHom (hasSubst_torsorFam F J)) x
  let Ψ : Fin (Module.finrank k (MvPowerSeries (Fin n) k ⧸ J)) →
      MvPowerSeries (Fin n) (MvPowerSeries (Fin n) k ⧸ J) := fun j => ρ (b j)

  have hspan : ∀ y : MvPowerSeries (Fin n) k ⧸ J,
      ∃ μ : Fin _ → k, y = ∑ j, algebraMap k _ (μ j) * constantCoeff (Ψ j) := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc, -⟩ := hb x
    refine ⟨fun j => constantCoeff (c j), ?_⟩
    conv_lhs => rw [hc]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, mk_subst_eq_of_constantCoeff hnat0 hmJ]
    congr 1
    show _ = constantCoeff (ρ (b j))
    rw [hρ, constantCoeff_subst_torsorFam]
  have hsurj := combo_surjective J Ψ hspan
  have hinjΨ := combo_injective J Ψ hsurj

  have hev : ρ f - algebraMap (MvPowerSeries (Fin n) k) _ f ∈
      I.map (algebraMap (MvPowerSeries (Fin n) k) (MvPowerSeries (Fin n) (MvPowerSeries (Fin n) k ⧸ J))) := by
    have hle : Ideal.span (Set.range fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ i)) ⊔
        I.map (inlAlgHom n k).toRingHom ≤
        (I.map (algebraMap (MvPowerSeries (Fin n) k)
          (MvPowerSeries (Fin n) (MvPowerSeries (Fin n) k ⧸ J)))).comap
          (substAlgHom (hasSubst_evFam J)).toRingHom := by
      refine sup_le ?_ ?_
      · refine Ideal.span_le.mpr ?_
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom,
          subst_evFam_subst_inr, Ideal.Quotient.eq_zero_iff_mem.mpr (hmJ i), map_zero]
        exact Ideal.zero_mem _
      · rw [Ideal.map_le_iff_le_comap]
        intro u hu
        rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom, subst_evFam_subst_inl, ← algebraMap_eq]
        exact Ideal.mem_map_of_mem _ hu
    have := hle hf
    rwa [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_substAlgHom,
      subst_sub (hasSubst_evFam J), subst_evFam_subst_F, subst_evFam_subst_inl, ← algebraMap_eq, ← hρ] at this
  have hsmul : ρ f - algebraMap (MvPowerSeries (Fin n) k) _ f ∈
      I • (⊤ : Submodule (MvPowerSeries (Fin n) k) (MvPowerSeries (Fin n) (MvPowerSeries (Fin n) k ⧸ J))) := by
    rw [Ideal.smul_top_eq_map]
    exact hev

  obtain ⟨c, hc, -⟩ := hb f
  obtain ⟨e, he, -⟩ := hb 1
  have hterm : ∀ (u : MvPowerSeries (Fin n) k) (j),
      ρ (subst (φ) u * b j) = map (algebraMap k _) (θ u) * Ψ j := by
    intro u j
    rw [map_mul, hθ]
    congr 1
    rw [hρ, subst_torsorFam_subst_nth F J F' hφ0 hφF hmJ]
  have hρf : ρ f = combo J Ψ (fun j => θ (c j)) := by
    rw [combo_apply]
    conv_lhs => rw [hc]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => hterm (c j) j
  have hρ1 : (1 : MvPowerSeries (Fin n) (MvPowerSeries (Fin n) k ⧸ J)) = combo J Ψ (fun j => θ (e j)) := by
    rw [← map_one ρ, combo_apply]
    conv_lhs => rw [he]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => hterm (e j) j
  have hf1 : algebraMap (MvPowerSeries (Fin n) k) _ f = combo J Ψ (fun j => f * θ (e j)) := by
    have h2 : (fun j => f * θ (e j)) = f • (fun j => θ (e j)) := by
      funext j
      rfl
    rw [h2, LinearMap.map_smul, ← hρ1, Algebra.smul_def, mul_one]

  have hdiff : ((fun j => θ (c j)) - fun j => f * θ (e j)) ∈
      I • (⊤ : Submodule (MvPowerSeries (Fin n) k) (Fin (Module.finrank k (MvPowerSeries (Fin n) k ⧸ J)) →
        MvPowerSeries (Fin n) k)) := by
    have h1 : combo J Ψ ((fun j => θ (c j)) - fun j => f * θ (e j)) ∈
        I • (⊤ : Submodule (MvPowerSeries (Fin n) k) (MvPowerSeries (Fin n) (MvPowerSeries (Fin n) k ⧸ J))) := by
      rw [map_sub, ← hρf, ← hf1]
      exact hsmul
    have h2 : I • (⊤ : Submodule (MvPowerSeries (Fin n) k) (MvPowerSeries (Fin n) (MvPowerSeries (Fin n) k ⧸ J))) =
        (I • (⊤ : Submodule (MvPowerSeries (Fin n) k) (Fin (Module.finrank k (MvPowerSeries (Fin n) k ⧸ J)) →
          MvPowerSeries (Fin n) k))).map (combo J Ψ) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
    rw [h2] at h1
    obtain ⟨y, hy, hyeq⟩ := h1
    rw [← hinjΨ hyeq]
    exact hy
  have hcoord : ∀ j, θ (c j) - f * θ (e j) ∈ I := fun j => by
    have := apply_mem_of_mem_smul_top I hdiff j
    simpa only [Pi.sub_apply] using this

  have hunit : ∃ j, IsUnit (e j) := by
    by_contra hcon
    push Not at hcon
    have h0 : ∀ j, constantCoeff (e j) ∈ IsLocalRing.maximalIdeal k := fun j => by
      have := hcon j
      rw [isUnit_iff_constantCoeff] at this
      exact (IsLocalRing.mem_maximalIdeal _).mpr this
    have h1 : constantCoeff (∑ j, subst φ (e j) * b j) ∈ IsLocalRing.maximalIdeal k := by
      rw [map_sum]
      refine Ideal.sum_mem _ fun j _ => ?_
      rw [map_mul, constantCoeff_subst_of_constantCoeff_zero hnat0, Algebra.algebraMap_self, RingHom.id_apply]
      exact Ideal.mul_mem_right _ _ (h0 j)
    rw [← he, map_one] at h1
    exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal k).ne_top h1
  obtain ⟨j, hj⟩ := hunit
  refine ⟨c j * ↑(hj.unit⁻¹), ?_⟩
  set v : MvPowerSeries (Fin n) k := ↑(hj.unit⁻¹) with hv
  have hinv : θ (e j) * θ v = 1 := by rw [← map_mul, hv, IsUnit.mul_val_inv, map_one]
  have key : f - subst φ (c j * v) = -((θ (c j) - f * θ (e j)) * θ v) := by
    rw [← hθ, map_mul]
    linear_combination (-f) * hinv
  rw [key]
  exact I.neg_mem (I.mul_mem_right _ (hcoord j))

end O4Desc
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_of_subst_toPowerSeries_sub_mem_span_of_X_pow_mem_span_of_isLocalRing.O4DescT72"

end
p2m_reactivate "P2MW.S_MvFormalGroup_exists_eq_subst_of_subst_toPowerSeries_sub_mem_span_of_X_pow_mem_span_of_isLocalRing.O4DescT72"

open MvPowerSeries in
theorem solution
    {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] {n : ℕ} (F F' : MvFormalGroup n B) [F.IsComm] [F'.IsComm]
    (ρ : Fin n → MvPowerSeries (Fin n) B) (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (hρF : ∀ i, MvPowerSeries.subst F.toPowerSeries (ρ i) =
      MvPowerSeries.subst (Sum.elim
          (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) B)) (ρ j))
          (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) B)) (ρ j)))
        (F'.toPowerSeries i))
    (hN : ∃ N : ℕ, ∀ i : Fin n, (MvPowerSeries.X i : MvPowerSeries (Fin n) B) ^ N ∈ Ideal.span (Set.range ρ))
    (hfin : Module.Finite B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)))
    (hproj : Module.Projective B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ))) :
(∀ G : MvPowerSeries (Fin n) B,
      MvPowerSeries.subst F.toPowerSeries G -
          MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) B)) G ∈
        Ideal.span (Set.range fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) B)) (ρ i)) →
      ∃ H : MvPowerSeries (Fin n) B, G = MvPowerSeries.subst ρ H ∧
        MvPowerSeries.constantCoeff H = MvPowerSeries.constantCoeff G) := by
  intro G hG
  haveI : Module.Flat B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)) := Module.Flat.of_projective
  have hfree : Module.Free B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)) := Module.free_of_flat_of_isLocalRing
  have hf : MvPowerSeries.subst F.toPowerSeries G -
        MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) B)) G ∈
      Ideal.span (Set.range fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) B)) (ρ i)) ⊔
        (⊥ : Ideal (MvPowerSeries (Fin n) B)).map (O4Desc.inlAlgHom n B).toRingHom := by
    rw [Ideal.map_bot, sup_bot_eq]
    exact hG
  obtain ⟨H, hH⟩ := O4Desc.torsor_descent_mod F F' ρ hρ0 hρF hN hfin hfree ⊥ G hf
  rw [Ideal.mem_bot, sub_eq_zero] at hH
  refine ⟨H, hH, ?_⟩
  rw [hH, O4DescT72.constantCoeff_subst_of_constantCoeff_zero hρ0 H, Algebra.algebraMap_self, RingHom.id_apply]

end S_MvFormalGroup_exists_eq_subst_of_subst_toPowerSeries_sub_mem_span_of_X_pow_mem_span_of_isLocalRing
end P2MW
export P2MW.S_MvFormalGroup_exists_eq_subst_of_subst_toPowerSeries_sub_mem_span_of_X_pow_mem_span_of_isLocalRing (solution)
