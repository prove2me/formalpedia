-- Prove2me | solution 1 for Manifold.exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c559b8fe-f775-52e9-acdb-0ea52681257f

import Mathlib
import Theorems.Thm_Manifold_exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Manifold_exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card

set_option autoImplicit false

noncomputable section

open Filter Topology Set
p2m_open_scoped "Manifold P2MW.S_Manifold_exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card.Manifold ContDiff Topology"

namespace Manifold
p2m_export "Manifold" "exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg"
namespace MeromorphicDimensionBoundProof
p2m_open "Manifold"

section Germs

variable {f f₁ f₂ G G₁ G₂ : ℂ → ℂ} {c : ℂ}

theorem exists_analyticAt_eventuallyEq (hf : MeromorphicAt f c) (h0 : 0 ≤ meromorphicOrderAt f c) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G c ∧ f =ᶠ[𝓝[≠] c] G := by
  by_cases htop : meromorphicOrderAt f c = ⊤
  · refine ⟨0, analyticAt_const, ?_⟩
    exact meromorphicOrderAt_eq_top_iff.1 htop
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
    have hn0 : 0 ≤ n := by
      rw [← hn] at h0
      exact_mod_cast h0
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
    obtain ⟨G, hG, -, hev⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn.symm
    refine ⟨fun z => (z - c) ^ (k : ℤ) • G z, ?_, hev⟩
    have h1 : AnalyticAt ℂ (fun z : ℂ => (z - c) ^ (k : ℤ)) c := by
      simp_rw [zpow_natCast]
      exact (analyticAt_id.sub analyticAt_const).pow k
    exact h1.smul hG

theorem apply_eq_of_eventuallyEq (h₁ : AnalyticAt ℂ G₁ c) (h₂ : AnalyticAt ℂ G₂ c)
    (h : G₁ =ᶠ[𝓝[≠] c] G₂) : G₁ c = G₂ c :=
  tendsto_nhds_unique_of_eventuallyEq (h₁.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (h₂.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) h

abbrev wt (k : ℕ) (c : ℂ) (f : ℂ → ℂ) : ℂ → ℂ := fun z => (z - c) ^ k * f z

theorem meromorphicAt_pow_sub (k : ℕ) (c : ℂ) : MeromorphicAt (fun z : ℂ => (z - c) ^ k) c :=
  ((analyticAt_id.sub analyticAt_const).pow k).meromorphicAt

theorem meromorphicOrderAt_pow_sub (k : ℕ) (c : ℂ) :
    meromorphicOrderAt (fun z : ℂ => (z - c) ^ k) c = (k : ℤ) := by
  refine (meromorphicOrderAt_eq_int_iff (meromorphicAt_pow_sub k c)).2 ⟨1, analyticAt_const,
    one_ne_zero, Eventually.of_forall fun z => ?_⟩
  simp [zpow_natCast]

theorem meromorphicAt_wt (k : ℕ) (hf : MeromorphicAt f c) : MeromorphicAt (wt k c f) c :=
  (meromorphicAt_pow_sub k c).mul hf

theorem meromorphicOrderAt_wt (k : ℕ) (hf : MeromorphicAt f c) :
    meromorphicOrderAt (wt k c f) c = (k : ℤ) + meromorphicOrderAt f c := by
  rw [show wt k c f = (fun z : ℂ => (z - c) ^ k) * f from rfl,
    meromorphicOrderAt_mul (meromorphicAt_pow_sub k c) hf, meromorphicOrderAt_pow_sub]

theorem le_order_iff (k : ℕ) (hf : MeromorphicAt f c) :
    ((-(k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f c ↔ 0 ≤ meromorphicOrderAt (wt k c f) c := by
  rw [meromorphicOrderAt_wt k hf]
  generalize meromorphicOrderAt f c = o
  induction o using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    norm_cast
    omega

theorem exists_rep (k : ℕ) (hf : MeromorphicAt f c)
    (hk : ((-(k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f c) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G c ∧ wt k c f =ᶠ[𝓝[≠] c] G :=
  exists_analyticAt_eventuallyEq (meromorphicAt_wt k hf) ((le_order_iff k hf).1 hk)

open Classical in

def lead (k : ℕ) (f : ℂ → ℂ) (c : ℂ) : ℂ :=
  if h : ∃ G : ℂ → ℂ, AnalyticAt ℂ G c ∧ wt k c f =ᶠ[𝓝[≠] c] G then h.choose c else 0

theorem lead_eq {k : ℕ} (hG : AnalyticAt ℂ G c) (heq : wt k c f =ᶠ[𝓝[≠] c] G) :
    lead k f c = G c := by
  have h : ∃ G : ℂ → ℂ, AnalyticAt ℂ G c ∧ wt k c f =ᶠ[𝓝[≠] c] G := ⟨G, hG, heq⟩
  rw [lead, dif_pos h]
  exact apply_eq_of_eventuallyEq h.choose_spec.1 hG (h.choose_spec.2.symm.trans heq)

theorem lead_add {k : ℕ} (h₁ : MeromorphicAt f₁ c) (hk₁ : ((-(k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f₁ c)
    (h₂ : MeromorphicAt f₂ c) (hk₂ : ((-(k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f₂ c) :
    lead k (f₁ + f₂) c = lead k f₁ c + lead k f₂ c := by
  obtain ⟨G₁, hG₁, he₁⟩ := exists_rep k h₁ hk₁
  obtain ⟨G₂, hG₂, he₂⟩ := exists_rep k h₂ hk₂
  have he : wt k c (f₁ + f₂) =ᶠ[𝓝[≠] c] (G₁ + G₂) := by
    filter_upwards [he₁, he₂] with z h1 h2
    simp only [wt, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  rw [lead_eq (hG₁.add hG₂) he, lead_eq hG₁ he₁, lead_eq hG₂ he₂, Pi.add_apply]

theorem lead_smul {k : ℕ} (a : ℂ) (h₁ : MeromorphicAt f c)
    (hk₁ : ((-(k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f c) :
    lead k (a • f) c = a * lead k f c := by
  obtain ⟨G, hG, he⟩ := exists_rep k h₁ hk₁
  have he' : wt k c (a • f) =ᶠ[𝓝[≠] c] (a • G) := by
    filter_upwards [he] with z h1
    simp only [wt, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [← h1]; ring
  rw [lead_eq (hG.const_smul (c := a)) he', lead_eq hG he, Pi.smul_apply, smul_eq_mul]

theorem le_order_of_lead_eq_zero {k : ℕ} (hf : MeromorphicAt f c)
    (hk : ((-((k + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f c)
    (h0 : lead (k + 1) f c = 0) : ((-(k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f c := by
  obtain ⟨G, hG, he⟩ := exists_rep (k + 1) hf hk
  have hGc : G c = 0 := by rw [← lead_eq hG he, h0]

  have hG₁ : AnalyticAt ℂ (dslope G c) c := by
    obtain ⟨p, hp⟩ := hG
    exact ⟨_, hp.has_fpower_series_dslope_fslope⟩
  have hfac : ∀ z, G z = (z - c) * dslope G c z := fun z => by
    have := sub_smul_dslope G c z
    rw [smul_eq_mul, hGc, sub_zero] at this
    exact this.symm

  have he' : wt k c f =ᶠ[𝓝[≠] c] dslope G c := by
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff] at he ⊢
    filter_upwards [he] with z hz hne
    have hz' := hz hne
    simp only [wt] at hz' ⊢
    rw [hfac z, pow_succ] at hz'
    have hzc : z - c ≠ 0 := sub_ne_zero.2 hne
    have : (z - c) * ((z - c) ^ k * f z) = (z - c) * dslope G c z := by
      rw [← hz']; ring
    exact mul_left_cancel₀ hzc this
  rw [le_order_iff k hf, meromorphicOrderAt_congr he']
  exact hG₁.meromorphicOrderAt_nonneg

end Germs

section Bounded

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

abbrev φ (x : M) : PartialEquiv M ℂ := extChartAt 𝓘(ℂ, ℂ) x

abbrev ctr (x : M) : ℂ := extChartAt 𝓘(ℂ, ℂ) x x

abbrev rd (ψ : M → ℂ) (x : M) : ℂ → ℂ := fun z => ψ ((φ x).symm z)

def Bdd (D : M →₀ ℕ) (ψ : M → ℂ) : Prop :=
  ∀ x : M, MeromorphicAt (rd ψ x) (ctr x) ∧
    ((-(D x : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (rd ψ x) (ctr x)

variable {D : M →₀ ℕ}

theorem Bdd.zero : Bdd D (0 : M → ℂ) := fun x => by
  refine ⟨MeromorphicAt.const 0 (ctr x), ?_⟩
  have : rd (0 : M → ℂ) x = fun _ => (0 : ℂ) := rfl
  rw [this, meromorphicOrderAt_const]
  simp

theorem Bdd.add {ψ₁ ψ₂ : M → ℂ} (h₁ : Bdd D ψ₁) (h₂ : Bdd D ψ₂) : Bdd D (ψ₁ + ψ₂) := fun x => by
  have e : rd (ψ₁ + ψ₂) x = rd ψ₁ x + rd ψ₂ x := rfl
  refine ⟨by rw [e]; exact (h₁ x).1.add (h₂ x).1, ?_⟩
  rw [e]
  exact (le_min (h₁ x).2 (h₂ x).2).trans (meromorphicOrderAt_add (h₁ x).1 (h₂ x).1)

theorem Bdd.smul {ψ : M → ℂ} (a : ℂ) (h : Bdd D ψ) : Bdd D (a • ψ) := fun x => by
  by_cases ha : a = 0
  · rw [ha, zero_smul]; exact Bdd.zero x
  have e : rd (a • ψ) x = (fun _ => a) * rd ψ x := by
    funext z; simp [rd, smul_eq_mul]
  have hc : MeromorphicAt (fun _ : ℂ => a) (ctr x) := MeromorphicAt.const a _
  refine ⟨by rw [e]; exact hc.mul (h x).1, ?_⟩
  rw [e, meromorphicOrderAt_mul hc (h x).1, meromorphicOrderAt_const, if_neg ha, zero_add]
  exact (h x).2

theorem Bdd.sub {ψ₁ ψ₂ : M → ℂ} (h₁ : Bdd D ψ₁) (h₂ : Bdd D ψ₂) : Bdd D (ψ₁ - ψ₂) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ ψ₂]
  exact h₁.add (h₂.smul (-1))

theorem Bdd.sum {ι : Type*} (s : Finset ι) {ψ : ι → M → ℂ} (c : ι → ℂ) (h : ∀ i, Bdd D (ψ i)) :
    Bdd D (∑ i ∈ s, c i • ψ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Bdd.zero
  | insert i s hi ih => rw [Finset.sum_insert hi]; exact ((h i).smul (c i)).add ih

theorem Bdd.of_lead_eq_zero {ψ : M → ℂ} (h : Bdd D ψ) {x₀ : M} (hx₀ : 1 ≤ D x₀)
    (h0 : lead (D x₀) (rd ψ x₀) (ctr x₀) = 0) : Bdd (D - Finsupp.single x₀ 1) ψ := by
  classical
  intro x
  refine ⟨(h x).1, ?_⟩
  rw [Finsupp.tsub_apply]
  by_cases hx : x₀ = x
  · subst hx
    rw [Finsupp.single_eq_same]
    obtain ⟨k, hk⟩ : ∃ k, D x₀ = k + 1 := ⟨D x₀ - 1, by omega⟩
    rw [hk] at h0 ⊢
    rw [Nat.add_sub_cancel]
    exact le_order_of_lead_eq_zero (h x₀).1 (by rw [← hk]; exact (h x₀).2) h0
  · rw [Finsupp.single_apply, if_neg hx, Nat.sub_zero]
    exact (h x).2

end Bounded

section Bound

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
variable [CompactSpace M] [ConnectedSpace M]

abbrev degN (D : M →₀ ℕ) : ℕ := D.sum fun _ n => n

omit [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M] [CompactSpace M]
  [ConnectedSpace M] in
theorem degN_eq_zero_iff (D : M →₀ ℕ) : degN D = 0 ↔ D = 0 := by
  constructor
  · intro h
    rw [degN, Finsupp.sum, Finset.sum_eq_zero_iff] at h
    ext x
    by_cases hx : x ∈ D.support
    · exact h x hx
    · exact Finsupp.notMem_support_iff.1 hx
  · rintro rfl; rfl

omit [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M] [CompactSpace M]
  [ConnectedSpace M] in
theorem degN_sub_single {D : M →₀ ℕ} {x₀ : M} (hx₀ : 1 ≤ D x₀) :
    degN (D - Finsupp.single x₀ 1) + 1 = degN D := by
  classical
  have hle : Finsupp.single x₀ 1 ≤ D := by
    intro x
    simp only [Finsupp.single_apply]
    split_ifs with h
    · subst h; exact hx₀
    · exact Nat.zero_le _
  have hD : D = (D - Finsupp.single x₀ 1) + Finsupp.single x₀ 1 := (tsub_add_cancel_of_le hle).symm
  conv_rhs => rw [hD]
  rw [degN, degN, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]

theorem base {ι : Type*} [Fintype ι] (ψ : ι → M → ℂ) (hψ : ∀ i, Bdd 0 (ψ i))
    (hcard : 1 < Fintype.card ι) :
    ∃ c : ι → ℂ, c ≠ 0 ∧ ∀ x, rd (∑ i, c i • ψ i) x =ᶠ[𝓝[≠] (ctr x)] 0 := by
  classical
  have hconst : ∀ i, ∃ C : ℂ, ∀ x, rd (ψ i) x =ᶠ[𝓝[≠] (ctr x)] fun _ => C := fun i =>
    Manifold.exists_forall_eventuallyEq_const_of_meromorphicOrderAt_nonneg (ψ i)
      (fun x => (hψ i x).1) (fun x => by have h__af := (hψ i x).2; simp at h__af; exact h__af)
  choose C hC using hconst
  obtain ⟨i₁, i₂, hne⟩ := Fintype.exists_pair_of_one_lt_card hcard
  by_cases h1 : C i₁ = 0
  · refine ⟨Pi.single i₁ (1 : ℂ), fun h => one_ne_zero (α := ℂ) (by simpa using congrFun h i₁),
      fun x => ?_⟩
    have : rd (∑ i, (Pi.single i₁ (1 : ℂ) : ι → ℂ) i • ψ i) x = rd (ψ i₁) x := by
      funext z
      simp only [rd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, ite_mul,
        one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [this]
    filter_upwards [hC i₁ x] with z hz
    rw [hz, h1, Pi.zero_apply]
  · refine ⟨Pi.single i₁ (C i₂) - Pi.single i₂ (C i₁), fun h => h1 ?_, fun x => ?_⟩
    · have := congrFun h i₂
      simp only [Pi.sub_apply, Pi.single_apply, if_neg hne.symm, zero_sub,
        Pi.zero_apply, neg_eq_zero] at this
      exact this
    · have : rd (∑ i, (Pi.single i₁ (C i₂) - Pi.single i₂ (C i₁) : ι → ℂ) i • ψ i) x =
          C i₂ • rd (ψ i₁) x - C i₁ • rd (ψ i₂) x := by
        funext z
        simp only [rd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
          Pi.single_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [this]
      filter_upwards [hC i₁ x, hC i₂ x] with z h₁ h₂
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h₁, h₂, Pi.zero_apply]
      ring

theorem bound (n : ℕ) : ∀ (D : M →₀ ℕ), degN D = n → ∀ {ι : Type*} [Fintype ι] (ψ : ι → M → ℂ),
    (∀ i, Bdd D (ψ i)) → n + 1 < Fintype.card ι →
    ∃ c : ι → ℂ, c ≠ 0 ∧ ∀ x, rd (∑ i, c i • ψ i) x =ᶠ[𝓝[≠] (ctr x)] 0 := by
  classical
  induction n with
  | zero =>
    intro D hD ι _ ψ hψ hcard
    rw [degN_eq_zero_iff] at hD
    subst hD
    exact base ψ hψ hcard
  | succ n ih =>
    intro D hD ι _ ψ hψ hcard

    obtain ⟨x₀, hx₀⟩ : ∃ x₀, 1 ≤ D x₀ := by
      by_contra hcon
      push Not at hcon
      have : D = 0 := by ext x; have := hcon x; simpa using Nat.lt_one_iff.1 this
      rw [this] at hD; simp [degN] at hD
    have hdeg' : degN (D - Finsupp.single x₀ 1) = n := by
      have := degN_sub_single hx₀
      rw [hD] at this
      omega
    let lam : ι → ℂ := fun i => lead (D x₀) (rd (ψ i) x₀) (ctr x₀)
    by_cases hall : ∀ i, lam i = 0
    ·
      exact ih _ hdeg' ψ (fun i => (hψ i).of_lead_eq_zero hx₀ (hall i)) (by omega)
    · push Not at hall
      obtain ⟨i₀, hi₀⟩ := hall

      let ι' := {i : ι // i ≠ i₀}
      let ψ' : ι' → M → ℂ := fun i => ψ i - (lam i / lam i₀) • ψ i₀
      have hψ' : ∀ i : ι', Bdd (D - Finsupp.single x₀ 1) (ψ' i) := by
        intro i
        have hB : Bdd D (ψ' i) := (hψ i).sub ((hψ i₀).smul _)
        refine hB.of_lead_eq_zero hx₀ ?_
        set a : ℂ := -(lam i / lam i₀) with ha
        have hm : MeromorphicAt (a • rd (ψ i₀) x₀) (ctr x₀) := (((hψ i₀).smul a) x₀).1
        have ho : ((-(D x₀ : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (a • rd (ψ i₀) x₀) (ctr x₀) :=
          (((hψ i₀).smul a) x₀).2
        have e : rd (ψ' i) x₀ = rd (ψ i) x₀ + a • rd (ψ i₀) x₀ := by
          funext z; simp [ψ', rd, smul_eq_mul, ha]; ring
        rw [e, lead_add (hψ i x₀).1 (hψ i x₀).2 hm ho, lead_smul a (hψ i₀ x₀).1 (hψ i₀ x₀).2]
        show lam i + -(lam i / lam i₀) * lam i₀ = 0
        field_simp
        ring
      have hcard' : n + 1 < Fintype.card ι' := by
        have : Fintype.card ι' = Fintype.card ι - 1 := by
          simp [ι', Fintype.card_subtype_compl]
        omega
      obtain ⟨c', hc'0, hc'⟩ := ih _ hdeg' ψ' hψ' hcard'

      let c : ι → ℂ := fun i =>
        if h : i = i₀ then -(∑ j : ι', c' j * (lam j / lam i₀)) else c' ⟨i, h⟩
      have hsum : ∑ i, c i • ψ i = ∑ j : ι', c' j • ψ' j := by

        have hL : ∑ i, c i • ψ i = c i₀ • ψ i₀ + ∑ j : ι', c' j • ψ (j : ι) := by
          rw [← Finset.add_sum_erase Finset.univ (fun i => c i • ψ i) (Finset.mem_univ i₀)]
          congr 1
          rw [Finset.sum_subtype (Finset.univ.erase i₀) (p := fun i => i ≠ i₀)
            (fun i => by simp)]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [c, dif_neg j.2]
        have hR : ∑ j : ι', c' j • ψ' j =
            ∑ j : ι', c' j • ψ (j : ι) + (-(∑ j : ι', c' j * (lam j / lam i₀))) • ψ i₀ := by
          simp only [ψ', smul_sub, Finset.sum_sub_distrib, smul_smul, neg_smul, Finset.sum_smul]
          abel
        rw [hL, hR, add_comm]
        simp only [c, dif_pos rfl]
      refine ⟨c, ?_, fun x => by rw [hsum]; exact hc' x⟩
      intro hc0
      apply hc'0
      funext j
      have := congrFun hc0 (j : ι)
      simp only [c, dif_neg j.2, Pi.zero_apply] at this
      exact this

end Bound

end Manifold.MeromorphicDimensionBoundProof

open Manifold.MeromorphicDimensionBoundProof in

theorem solution
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]
    [CompactSpace M] [ConnectedSpace M]
    (D : M →₀ ℕ) {ι : Type*} [Fintype ι] (ψ : ι → M → ℂ)
    (hψ : ∀ i x, MeromorphicAt (fun z : ℂ => ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      (extChartAt 𝓘(ℂ, ℂ) x x))
    (hord : ∀ i x, ((-(D x : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z : ℂ => ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) (extChartAt 𝓘(ℂ, ℂ) x x))
    (hcard : (D.sum fun _ n => n) + 1 < Fintype.card ι) :
    ∃ c : ι → ℂ, c ≠ 0 ∧ ∀ x : M, (fun z : ℂ => ∑ i, c i * ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      =ᶠ[𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) x x)] 0 := by
  obtain ⟨c, hc0, hc⟩ := bound (degN D) D rfl ψ (fun i x => ⟨hψ i x, hord i x⟩) hcard
  refine ⟨c, hc0, fun x => ?_⟩
  have : (fun z : ℂ => ∑ i, c i * ψ i ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) = rd (∑ i, c i • ψ i) x := by
    funext z
    simp [rd, Finset.sum_apply, smul_eq_mul]
  rw [this]
  exact hc x

end

end S_Manifold_exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card
end P2MW
export P2MW.S_Manifold_exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card (solution)
