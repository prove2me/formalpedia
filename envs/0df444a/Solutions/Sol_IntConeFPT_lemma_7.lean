-- Prove2me | solution 1 for IntConeFPT.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-24T15:03:58.87071+00:00
-- url     : https://prove2.me/submissions/4c87239d-feb6-46f4-abc9-3d40194a12d4

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Problem

set_option autoImplicit false

open OnlineCRS.Combine
open IntConeFPT

namespace IntConeFPT.Lemma7Proof

open scoped Classical

private noncomputable def pot {d k : ℕ} (ν : Gen d k →₀ ℕ) : ℕ :=
  ν.sum fun g n => n * ∑ i : Fin d, (g.1 i).natAbs ^ 2

private lemma pot_add {d k : ℕ} (ν₁ ν₂ : Gen d k →₀ ℕ) :
    pot (ν₁ + ν₂) = pot ν₁ + pot ν₂ := by
  unfold pot
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

private lemma pot_sum {d k : ℕ} {ι : Type*} (s : Finset ι) (h : ι → Gen d k →₀ ℕ) :
    pot (∑ i ∈ s, h i) = ∑ i ∈ s, pot (h i) := by
  induction s using Finset.induction_on with
  | empty => simp [pot]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pot_add, ih]

private lemma pot_single {d k : ℕ} (g : Gen d k) (n : ℕ) :
    pot (Finsupp.single g n) = n * ∑ i : Fin d, (g.1 i).natAbs ^ 2 := by
  unfold pot
  exact Finsupp.sum_single_index (by simp)

private lemma aggr_add {d k : ℕ} (ν₁ ν₂ : Gen d k →₀ ℕ) :
    aggr (ν₁ + ν₂) = aggr ν₁ + aggr ν₂ := by
  unfold aggr
  exact Finsupp.sum_add_index' (fun _ => by simp)
    (fun _ _ _ => by simp only [Nat.cast_add, add_smul])

private lemma aggr_sum {d k : ℕ} {ι : Type*} (s : Finset ι) (h : ι → Gen d k →₀ ℕ) :
    aggr (∑ i ∈ s, h i) = ∑ i ∈ s, aggr (h i) := by
  induction s using Finset.induction_on with
  | empty => simp [aggr]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, aggr_add, ih]

private lemma aggr_single {d k : ℕ} (g : Gen d k) (n : ℕ) :
    aggr (Finsupp.single g n) = (n : ℝ) • g.toReal := by
  unfold aggr
  exact Finsupp.sum_single_index (by simp)

private lemma count_add {d k : ℕ} (ν₁ ν₂ : Gen d k →₀ ℕ) :
    count (ν₁ + ν₂) = count ν₁ + count ν₂ := by
  unfold count
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

private lemma count_sum {d k : ℕ} {ι : Type*} (s : Finset ι) (h : ι → Gen d k →₀ ℕ) :
    count (∑ i ∈ s, h i) = ∑ i ∈ s, count (h i) := by
  induction s using Finset.induction_on with
  | empty => simp [count]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, count_add, ih]

private lemma count_single {d k : ℕ} (g : Gen d k) (n : ℕ) :
    count (Finsupp.single g n) = n := by
  unfold count
  exact Finsupp.sum_single_index rfl

private lemma costOf_add {d k : ℕ} (f : (Fin d → ℝ) → ℝ) (ν₁ ν₂ : Gen d k →₀ ℕ) :
    costOf f (ν₁ + ν₂) = costOf f ν₁ + costOf f ν₂ := by
  unfold costOf
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)

private lemma costOf_sum {d k : ℕ} (f : (Fin d → ℝ) → ℝ) {ι : Type*} (s : Finset ι)
    (h : ι → Gen d k →₀ ℕ) :
    costOf f (∑ i ∈ s, h i) = ∑ i ∈ s, costOf f (h i) := by
  induction s using Finset.induction_on with
  | empty => simp [costOf]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, costOf_add, ih]

private lemma costOf_single {d k : ℕ} (f : (Fin d → ℝ) → ℝ) (g : Gen d k) (n : ℕ) :
    costOf f (Finsupp.single g n) = (n : ℝ) * f (fun i => (g.1 i : ℝ)) := by
  unfold costOf
  exact Finsupp.sum_single_index (by simp)

private def Admissible {d k : ℕ} (P : Set ((Fin d → ℝ) × (Fin k → ℝ)))
    (f : (Fin d → ℝ) → ℝ) (μ ν : Gen d k →₀ ℕ) : Prop :=
  (↑ν.support : Set (Gen d k)) ⊆ genSet P ∧
  aggr ν = aggr μ ∧
  count ν = count μ ∧
  costOf f ν ≤ costOf f μ

private noncomputable def collapseCount {d k : ℕ} (ν : Gen d k →₀ ℕ) (x : Fin d → ℤ) : ℕ :=
  ∑ g ∈ ν.support.filter (fun g => g.1 = x), ν g

private noncomputable def collapseCont {d k : ℕ} (ν : Gen d k →₀ ℕ) (x : Fin d → ℤ) :
    Fin k → ℝ :=
  ((collapseCount ν x : ℝ)⁻¹) •
    ∑ g ∈ ν.support.filter (fun g => g.1 = x), (ν g : ℝ) • g.2

private noncomputable def collapseGen {d k : ℕ} (ν : Gen d k →₀ ℕ) (x : Fin d → ℤ) : Gen d k :=
  (x, collapseCont ν x)

private noncomputable def collapse {d k : ℕ} (ν : Gen d k →₀ ℕ) : Gen d k →₀ ℕ :=
  ∑ x ∈ ν.support.image Prod.fst, Finsupp.single (collapseGen ν x) (collapseCount ν x)

private lemma collapseCount_pos_of_mem {d k : ℕ} (ν : Gen d k →₀ ℕ) {x : Fin d → ℤ}
    (hx : x ∈ ν.support.image Prod.fst) : 0 < collapseCount ν x := by
  rw [Finset.mem_image] at hx
  obtain ⟨g, hg, hgx⟩ := hx
  have hg_mem : g ∈ ν.support.filter (fun g => g.1 = x) :=
    Finset.mem_filter.mpr ⟨hg, hgx⟩
  have hpos : 0 < ν g := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hg)
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hg_mem)

private lemma collapseGen_mem_genSet {d k : ℕ} {P : Set ((Fin d → ℝ) × (Fin k → ℝ))}
    (hconv : Convex ℝ P) {ν : Gen d k →₀ ℕ} (hν : (↑ν.support : Set (Gen d k)) ⊆ genSet P)
    {x : Fin d → ℤ} (hx : x ∈ ν.support.image Prod.fst) :
    collapseGen ν x ∈ genSet P := by
  let Sx := ν.support.filter (fun g => g.1 = x)
  have hnpos : 0 < (collapseCount ν x : ℝ) :=
    Nat.cast_pos.mpr (collapseCount_pos_of_mem ν hx)
  have hw0 : ∀ g ∈ Sx, (0 : ℝ) ≤ (ν g : ℝ) := fun _ _ => Nat.cast_nonneg _
  have hwsum : 0 < ∑ g ∈ Sx, (ν g : ℝ) := by
    have heq : (∑ g ∈ Sx, (ν g : ℝ)) = (collapseCount ν x : ℝ) := by
      simp [collapseCount, Sx]
    rw [heq]
    exact hnpos
  have hmemP : ∀ g ∈ Sx, g.toReal ∈ P := fun g hg => hν (Finset.mem_filter.mp hg).1
  have hcm := hconv.centerMass_mem hw0 hwsum hmemP
  have hcm_eq : Sx.centerMass (fun g => (ν g : ℝ)) Gen.toReal = (collapseGen ν x).toReal := by
    have hsum_eq : (∑ g ∈ Sx, (ν g : ℝ)) = (collapseCount ν x : ℝ) := by
      simp [collapseCount, Sx]
    simp only [Finset.centerMass, hsum_eq]
    ext j
    · simp only [Prod.smul_fst, Prod.fst_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Gen.toReal, collapseGen]
      have hid : (∑ g ∈ Sx, (ν g : ℝ) * (g.1 j : ℝ)) =
          (∑ g ∈ Sx, (ν g : ℝ)) * (x j : ℝ) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun g hg => ?_
        rw [(Finset.mem_filter.mp hg).2]
      rw [hid, hsum_eq, inv_mul_cancel_left₀ hnpos.ne']
    · simp only [Prod.smul_snd, Prod.snd_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Gen.toReal, collapseGen, collapseCont, Sx]
  change (collapseGen ν x).toReal ∈ P
  rw [← hcm_eq]
  exact hcm

private lemma collapse_properties {d k : ℕ} {P : Set ((Fin d → ℝ) × (Fin k → ℝ))}
    (hconv : Convex ℝ P) {f : (Fin d → ℝ) → ℝ} {μ ν : Gen d k →₀ ℕ}
    (hAdm : Admissible P f μ ν) :
    Admissible P f μ (collapse ν) ∧
    pot (collapse ν) = pot ν ∧
    ∀ g₁ ∈ (collapse ν).support, ∀ g₂ ∈ (collapse ν).support, g₁ ≠ g₂ → g₁.1 ≠ g₂.1 := by
  rcases hAdm with ⟨hsupp, haggr, hcount, hcost⟩
  let Xsupp := ν.support.image Prod.fst
  have hterm_aggr : ∀ x ∈ Xsupp,
      aggr (Finsupp.single (collapseGen ν x) (collapseCount ν x)) =
        ∑ g ∈ ν.support.filter (fun g => g.1 = x), (ν g : ℝ) • g.toReal := by
    intro x hx
    rw [aggr_single]
    have hnpos : (collapseCount ν x : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (collapseCount_pos_of_mem ν hx)).ne'
    ext j
    · simp only [Gen.toReal, collapseGen, Prod.smul_fst, Pi.smul_apply, smul_eq_mul,
        Prod.fst_sum, Finset.sum_apply]
      have : (collapseCount ν x : ℝ) * (x j : ℝ) =
          ∑ g ∈ ν.support.filter (fun g => g.1 = x), (ν g : ℝ) * (x j : ℝ) := by
        simp [collapseCount, Finset.sum_mul]
      rw [this]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [(Finset.mem_filter.mp hg).2]
    · simp only [Gen.toReal, collapseGen, collapseCont, Prod.smul_snd, Prod.snd_sum,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_inv_cancel_left₀ hnpos]
  have hfiber_sum : ∀ {M : Type} [AddCommMonoid M] (F : Gen d k → M),
      ∑ x ∈ Xsupp, ∑ g ∈ ν.support.filter (fun g => g.1 = x), F g = ∑ g ∈ ν.support, F g := by
    intro M _ F
    exact Finset.sum_fiberwise_of_maps_to (s := ν.support) (t := Xsupp) (g := Prod.fst)
      (fun g hg => Finset.mem_image_of_mem _ hg) F
  have hc_supp : (↑(collapse ν).support : Set (Gen d k)) ⊆ genSet P := by
    intro g hg
    have hg' := Finsupp.support_finsetSum (Finset.mem_coe.mp hg)
    rw [Finset.mem_biUnion] at hg'
    obtain ⟨x, hx, hgx⟩ := hg'
    have hgeq : g = collapseGen ν x := Finset.mem_singleton.mp (Finsupp.support_single_subset hgx)
    rw [hgeq]
    exact collapseGen_mem_genSet hconv hsupp hx
  have hc_aggr : aggr (collapse ν) = aggr μ := by
    rw [← haggr]
    unfold collapse
    rw [aggr_sum]
    have hcongr : ∑ x ∈ Xsupp, aggr (Finsupp.single (collapseGen ν x) (collapseCount ν x)) =
        ∑ x ∈ Xsupp, ∑ g ∈ ν.support.filter (fun g => g.1 = x), (ν g : ℝ) • g.toReal :=
      Finset.sum_congr rfl fun x hx => hterm_aggr x hx
    rw [hcongr]
    exact hfiber_sum (fun g => (ν g : ℝ) • g.toReal)
  have hc_count : count (collapse ν) = count μ := by
    rw [← hcount]
    unfold collapse
    rw [count_sum]
    simp_rw [count_single, collapseCount]
    exact hfiber_sum (fun g => ν g)
  have hc_cost : costOf f (collapse ν) ≤ costOf f μ := by
    refine le_trans ?_ hcost
    unfold collapse
    rw [costOf_sum]
    have hcongr : ∑ x ∈ Xsupp, costOf f (Finsupp.single (collapseGen ν x) (collapseCount ν x)) =
        ∑ x ∈ Xsupp, ∑ g ∈ ν.support.filter (fun g => g.1 = x),
          (ν g : ℝ) * f (fun i => (g.1 i : ℝ)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [costOf_single]
      simp only [collapseGen, collapseCount, Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [(Finset.mem_filter.mp hg).2]
    rw [hcongr]
    exact (hfiber_sum (fun g => (ν g : ℝ) * f (fun i => (g.1 i : ℝ)))).le
  have hc_pot : pot (collapse ν) = pot ν := by
    unfold collapse
    rw [pot_sum]
    have hcongr : ∑ x ∈ Xsupp, pot (Finsupp.single (collapseGen ν x) (collapseCount ν x)) =
        ∑ x ∈ Xsupp, ∑ g ∈ ν.support.filter (fun g => g.1 = x),
          ν g * ∑ i : Fin d, (g.1 i).natAbs ^ 2 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [pot_single]
      simp only [collapseGen, collapseCount, Finset.sum_mul]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [(Finset.mem_filter.mp hg).2]
    rw [hcongr]
    exact hfiber_sum (fun g => ν g * ∑ i, (g.1 i).natAbs ^ 2)
  have hc_inj : ∀ g₁ ∈ (collapse ν).support, ∀ g₂ ∈ (collapse ν).support, g₁ ≠ g₂ → g₁.1 ≠ g₂.1 := by
    intro g₁ hg₁ g₂ hg₂ hne heq1
    have h1 := Finsupp.support_finsetSum hg₁
    have h2 := Finsupp.support_finsetSum hg₂
    rw [Finset.mem_biUnion] at h1 h2
    obtain ⟨x₁, _, hgx₁⟩ := h1
    obtain ⟨x₂, _, hgx₂⟩ := h2
    have hge1 : g₁ = collapseGen ν x₁ := Finset.mem_singleton.mp (Finsupp.support_single_subset hgx₁)
    have hge2 : g₂ = collapseGen ν x₂ := Finset.mem_singleton.mp (Finsupp.support_single_subset hgx₂)
    have hxeq : x₁ = x₂ := by
      have h1' : g₁.1 = x₁ := by rw [hge1]; rfl
      have h2' : g₂.1 = x₂ := by rw [hge2]; rfl
      rw [← h1', ← h2', heq1]
    apply hne
    rw [hge1, hge2, hxeq]
  exact ⟨⟨hc_supp, hc_aggr, hc_count, hc_cost⟩, hc_pot, hc_inj⟩

private lemma int_midpoint_sq {a b : ℤ} (hdiv : 2 ∣ a + b) :
    4 * (((a + b) / 2).natAbs ^ 2 : ℤ) + ((a - b).natAbs ^ 2 : ℤ) =
      2 * ((a.natAbs ^ 2 : ℤ) + (b.natAbs ^ 2 : ℤ)) := by
  have hc : 2 * ((a + b) / 2) = a + b := Int.mul_ediv_cancel' hdiv
  have h1 : (((a + b) / 2).natAbs : ℤ) ^ 2 = ((a + b) / 2) ^ 2 := Int.natAbs_sq _
  have h2 : ((a - b).natAbs : ℤ) ^ 2 = (a - b) ^ 2 := Int.natAbs_sq _
  have h3 : (a.natAbs : ℤ) ^ 2 = a ^ 2 := Int.natAbs_sq _
  have h4 : (b.natAbs : ℤ) ^ 2 = b ^ 2 := Int.natAbs_sq _
  rw [h1, h2, h3, h4]
  have hpow : 4 * ((a + b) / 2) ^ 2 = (2 * ((a + b) / 2)) ^ 2 := by ring
  rw [hpow, hc]
  ring

private lemma nat_midpoint_pot_ineq {a b : ℤ} (hmod : a % 2 = 0 ↔ b % 2 = 0) :
    2 * ((a + b) / 2).natAbs ^ 2 ≤ a.natAbs ^ 2 + b.natAbs ^ 2 ∧
    (a ≠ b → 2 * ((a + b) / 2).natAbs ^ 2 < a.natAbs ^ 2 + b.natAbs ^ 2) := by
  have hdiv : 2 ∣ a + b := by omega
  have hidN : 4 * ((a + b) / 2).natAbs ^ 2 + (a - b).natAbs ^ 2 =
      2 * (a.natAbs ^ 2 + b.natAbs ^ 2) := by exact_mod_cast int_midpoint_sq hdiv
  refine ⟨by omega, fun hne => ?_⟩
  have hpos : 0 < (a - b).natAbs ^ 2 := by
    have hnz : (a - b).natAbs ≠ 0 := by omega
    exact Nat.pow_pos (Nat.pos_of_ne_zero hnz)
  omega

lemma lemma_7_single {d k : ℕ} (P : Set ((Fin d → ℝ) × (Fin k → ℝ)))
    (hconv : Convex ℝ P) (f : (Fin d → ℝ) → ℝ)
    (hf : DiscreteJensen {x : Fin d → ℤ | (fun i => (x i : ℝ)) ∈ Prod.fst '' P}
      (fun x => f (fun i => (x i : ℝ))))
    (μ : Gen d k →₀ ℕ) (hμ : (↑μ.support : Set (Gen d k)) ⊆ genSet P) :
    ∃ μ' : Gen d k →₀ ℕ,
      (↑μ'.support : Set (Gen d k)) ⊆ genSet P ∧
      aggr μ' = aggr μ ∧ count μ' = count μ ∧
      costOf f μ' ≤ costOf f μ ∧
      μ'.support.card ≤ 2 ^ d := by
  let S : ℕ → Prop := fun m => ∃ ν : Gen d k →₀ ℕ, Admissible P f μ ν ∧ pot ν = m
  have hex : ∃ m, S m := ⟨pot μ, μ, ⟨hμ, rfl, rfl, le_rfl⟩, rfl⟩
  let m₀ := Nat.find hex
  obtain ⟨ν₀, hAdm₀, hpot₀⟩ := Nat.find_spec hex
  have hmin : ∀ ν, Admissible P f μ ν → m₀ ≤ pot ν := fun ν hAdm =>
    Nat.find_min' hex ⟨ν, hAdm, rfl⟩
  obtain ⟨hAdm', hpot', hinj'⟩ := collapse_properties hconv hAdm₀
  let ν' := collapse ν₀
  have hpot_eq : pot ν' = m₀ := by rw [hpot', hpot₀]
  refine ⟨ν', hAdm'.1, hAdm'.2.1, hAdm'.2.2.1, hAdm'.2.2.2, ?_⟩
  by_contra hcard
  have hlt : (Finset.univ : Finset (Fin d → Bool)).card < ν'.support.card := by
    simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using Nat.lt_of_not_ge hcard
  let parity : Gen d k → (Fin d → Bool) := fun g i => decide (g.1 i % 2 = 0)
  have hmaps : Set.MapsTo parity (ν'.support : Set (Gen d k))
      ((Finset.univ : Finset (Fin d → Bool)) : Set (Fin d → Bool)) :=
    fun _ _ => Finset.mem_univ _
  obtain ⟨ga, hga, gb, hgb, hne, hpar⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  have hxne : ga.1 ≠ gb.1 := hinj' ga hga gb hgb hne
  have hmod : ∀ i : Fin d, ga.1 i % 2 = 0 ↔ gb.1 i % 2 = 0 := by
    intro i
    have hi := congrFun hpar i
    exact decide_eq_decide.mp hi
  have hdiv : ∀ i : Fin d, 2 ∣ ga.1 i + gb.1 i := by
    intro i
    have := hmod i
    omega
  let xc : Fin d → ℤ := fun i => (ga.1 i + gb.1 i) / 2
  let uc : Fin k → ℝ := (2⁻¹ : ℝ) • (ga.2 + gb.2)
  let gc : Gen d k := (xc, uc)
  have hxc_mul : ∀ i : Fin d, 2 * xc i = ga.1 i + gb.1 i :=
    fun i => Int.mul_ediv_cancel' (hdiv i)
  have hgc_mem : gc ∈ genSet P := by
    have haP : ga.toReal ∈ P := hAdm'.1 hga
    have hbP : gb.toReal ∈ P := hAdm'.1 hgb
    have hmid := hconv haP hbP (by positivity : (0 : ℝ) ≤ 2⁻¹)
      (by positivity : (0 : ℝ) ≤ 2⁻¹) (by norm_num)
    have hmid_eq : (2⁻¹ : ℝ) • ga.toReal + (2⁻¹ : ℝ) • gb.toReal = gc.toReal := by
      ext j
      · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Gen.toReal, gc]
        have h2 : (2 : ℝ) * (xc j : ℝ) = (ga.1 j : ℝ) + (gb.1 j : ℝ) := by
          exact_mod_cast hxc_mul j
        linarith
      · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Gen.toReal, gc, uc]
        ring
    change gc.toReal ∈ P
    rw [← hmid_eq]
    exact hmid
  let ν_rem : Gen d k →₀ ℕ := (ν' - Finsupp.single ga 1) - Finsupp.single gb 1
  have hga_pos : 1 ≤ ν' ga := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hga)
  have hgb_pos : 1 ≤ ν' gb := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hgb)
  have hsplit : ν' = ν_rem + Finsupp.single ga 1 + Finsupp.single gb 1 := by
    ext g
    simp only [Finsupp.add_apply, Finsupp.tsub_apply, ν_rem, Finsupp.single_apply]
    by_cases ha : ga = g <;> by_cases hb : gb = g
    · subst ha; exact absurd hb.symm hne
    · subst ha; simp [hb]; omega
    · subst hb; simp [ha]; omega
    · simp only [if_neg ha, if_neg hb]; omega
  let ν'' : Gen d k →₀ ℕ := ν_rem + Finsupp.single gc 2
  have hAdm'' : Admissible P f μ ν'' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g hg
      have hg' := Finsupp.support_add (Finset.mem_coe.mp hg)
      rcases Finset.mem_union.mp hg' with hrem | hsingle
      · have hg1 : g ∈ (ν' - Finsupp.single ga 1).support :=
          Finsupp.support_tsub (f2 := Finsupp.single gb 1) hrem
        have hg2 : g ∈ ν'.support := Finsupp.support_tsub (f2 := Finsupp.single ga 1) hg1
        exact hAdm'.1 hg2
      · have hgeq : g = gc := Finset.mem_singleton.mp (Finsupp.support_single_subset hsingle)
        rw [hgeq]
        exact hgc_mem
    · rw [← hAdm'.2.1]
      have h1 : aggr ν' = aggr ν_rem + ga.toReal + gb.toReal := by
        conv_lhs => rw [hsplit]
        simp only [aggr_add, aggr_single, Nat.cast_one, one_smul]
      have h2 : aggr ν'' = aggr ν_rem + (2 : ℝ) • gc.toReal := by
        simp only [ν'', aggr_add, aggr_single, Nat.cast_ofNat]
      have hmid2 : (2 : ℝ) • gc.toReal = ga.toReal + gb.toReal := by
        ext j
        · simp only [Prod.smul_fst, Prod.fst_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
            Gen.toReal, gc]
          have h2' : (2 : ℝ) * (xc j : ℝ) = (ga.1 j : ℝ) + (gb.1 j : ℝ) := by
            exact_mod_cast hxc_mul j
          exact h2'
        · simp only [Prod.smul_snd, Prod.snd_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
            Gen.toReal, gc, uc]
          ring
      rw [h1, h2, hmid2, add_assoc]
    · rw [← hAdm'.2.2.1]
      have h1 : count ν' = count ν_rem + 1 + 1 := by
        conv_lhs => rw [hsplit]
        rw [count_add, count_add, count_single, count_single]
      have h2 : count ν'' = count ν_rem + 2 := by
        simp only [ν'', count_add, count_single]
      change count ν'' = count ν'
      omega
    · refine le_trans ?_ hAdm'.2.2.2
      have h1 : costOf f ν' =
          costOf f ν_rem + f (fun i => (ga.1 i : ℝ)) + f (fun i => (gb.1 i : ℝ)) := by
        conv_lhs => rw [hsplit]
        rw [costOf_add, costOf_add, costOf_single, costOf_single, Nat.cast_one, one_mul, one_mul]
      have h2 : costOf f ν'' = costOf f ν_rem + 2 * f (fun i => (gc.1 i : ℝ)) := by
        simp only [ν'', costOf_add, costOf_single, Nat.cast_ofNat]
      have hxc_in : xc ∈ {x : Fin d → ℤ | (fun i => (x i : ℝ)) ∈ Prod.fst '' P} :=
        ⟨gc.toReal, hgc_mem, rfl⟩
      have hga_in : ga.1 ∈ {x : Fin d → ℤ | (fun i => (x i : ℝ)) ∈ Prod.fst '' P} :=
        ⟨ga.toReal, hAdm'.1 hga, rfl⟩
      have hgb_in : gb.1 ∈ {x : Fin d → ℤ | (fun i => (x i : ℝ)) ∈ Prod.fst '' P} :=
        ⟨gb.toReal, hAdm'.1 hgb, rfl⟩
      let θ : Fin 2 → ℝ := fun _ => (2⁻¹ : ℝ)
      let xs : Fin 2 → Fin d → ℤ := ![ga.1, gb.1]
      have hjens : f (fun i => (xc i : ℝ)) ≤
          ∑ r : Fin 2, θ r * f (fun i => (xs r i : ℝ)) := by
        refine hf xc hxc_in 2 θ xs ?_ (fun _ => by positivity) (by simp [θ]) ?_
        · intro r
          fin_cases r
          · exact hga_in
          · exact hgb_in
        · ext i
          simp only [Fin.sum_univ_two, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, θ, xs,
            Matrix.cons_val_zero, Matrix.cons_val_one]
          have h2' : (2 : ℝ) * (xc i : ℝ) = (ga.1 i : ℝ) + (gb.1 i : ℝ) := by
            exact_mod_cast hxc_mul i
          linarith
      simp only [Fin.sum_univ_two, θ, xs, Matrix.cons_val_zero, Matrix.cons_val_one] at hjens
      have h2f : 2 * f (fun i => (gc.1 i : ℝ)) ≤
          f (fun i => (ga.1 i : ℝ)) + f (fun i => (gb.1 i : ℝ)) := by
        change 2 * f (fun i => (xc i : ℝ)) ≤ _
        linarith
      rw [h1, h2]
      linarith
  have hpot_lt : pot ν'' < pot ν' := by
    have h1 : pot ν' = pot ν_rem +
        ((∑ i : Fin d, (ga.1 i).natAbs ^ 2) + (∑ i : Fin d, (gb.1 i).natAbs ^ 2)) := by
      conv_lhs => rw [hsplit]
      rw [pot_add, pot_add, pot_single, pot_single, one_mul, one_mul, add_assoc]
    have h2 : pot ν'' = pot ν_rem + 2 * ∑ i : Fin d, (xc i).natAbs ^ 2 := by
      simp only [ν'', pot_add, pot_single, gc]
    have hne_coord : ∃ i₀ : Fin d, ga.1 i₀ ≠ gb.1 i₀ := by
      by_contra hnone
      push Not at hnone
      exact hxne (funext hnone)
    obtain ⟨i₀, hi₀⟩ := hne_coord
    have hsum_lt : 2 * ∑ i : Fin d, (xc i).natAbs ^ 2 <
        (∑ i : Fin d, (ga.1 i).natAbs ^ 2) + (∑ i : Fin d, (gb.1 i).natAbs ^ 2) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_lt_sum (fun i _ => (nat_midpoint_pot_ineq (hmod i)).1)
        ⟨i₀, Finset.mem_univ i₀, (nat_midpoint_pot_ineq (hmod i₀)).2 hi₀⟩
    rw [h1, h2]
    omega
  have hm₀_le : m₀ ≤ pot ν'' := hmin ν'' hAdm''
  omega

end IntConeFPT.Lemma7Proof

open IntConeFPT
open IntConeFPT.Lemma7Proof

theorem solution {d k τ : ℕ} (hd : 1 ≤ d) (P : Fin τ → Set ((Fin d → ℝ) × (Fin k → ℝ)))
    (hconv : ∀ t, Convex ℝ (P t)) (hbdd : ∀ t, Bornology.IsBounded (P t))
    (f : Fin τ → (Fin d → ℝ) → ℝ)
    (hf : ∀ t, DiscreteJensen {x : Fin d → ℤ | (fun i => (x i : ℝ)) ∈ Prod.fst '' P t}
      (fun x => f t (fun i => (x i : ℝ))))
    (μ : (t : Fin τ) → Gen d k →₀ ℕ)
    (hμ : ∀ t, (↑(μ t).support : Set (Gen d k)) ⊆ genSet (P t)) :
    ∃ μ' : (t : Fin τ) → Gen d k →₀ ℕ,
      (∀ t, (↑(μ' t).support : Set (Gen d k)) ⊆ genSet (P t)) ∧
      (∀ t, aggr (μ' t) = aggr (μ t) ∧ count (μ' t) = count (μ t)) ∧
      (∀ t, costOf (f t) (μ' t) ≤ costOf (f t) (μ t)) ∧
      (∀ t, (μ' t).support.card ≤ 2 ^ d) ∧
      ∑ t, (μ' t).support.card ≤ τ * 2 ^ d := by
  have hsingle : ∀ t : Fin τ, ∃ ν : Gen d k →₀ ℕ,
      (↑ν.support : Set (Gen d k)) ⊆ genSet (P t) ∧
      aggr ν = aggr (μ t) ∧ count ν = count (μ t) ∧
      costOf (f t) ν ≤ costOf (f t) (μ t) ∧
      ν.support.card ≤ 2 ^ d :=
    fun t => lemma_7_single (P t) (hconv t) (f t) (hf t) (μ t) (hμ t)
  choose μ' hμ'_spec using hsingle
  refine ⟨μ', fun t => (hμ'_spec t).1,
    fun t => ⟨(hμ'_spec t).2.1, (hμ'_spec t).2.2.1⟩,
    fun t => (hμ'_spec t).2.2.2.1,
    fun t => (hμ'_spec t).2.2.2.2, ?_⟩
  calc ∑ t : Fin τ, (μ' t).support.card
    _ ≤ ∑ _t : Fin τ, 2 ^ d := Finset.sum_le_sum fun t _ => (hμ'_spec t).2.2.2.2
    _ = τ * 2 ^ d := by simp
