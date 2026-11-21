-- Prove2me | solution 1 for MinSharing.corollary_2_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T23:17:54.682396+00:00
-- url     : https://prove2.me/submissions/5d2ff548-37f2-4d9d-bc08-781442720cce

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting

set_option autoImplicit false

namespace Aux_MS_S3

open CompetitiveChores.RichFamily

section Cone

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

def LI (g : ι → (Fin N → ℝ)) (T : Finset ι) : Prop :=
  ∀ f : ι → ℝ, ∑ i ∈ T, f i • g i = 0 → ∀ i ∈ T, f i = 0

theorem carath (g : ι → (Fin N → ℝ)) : ∀ (K : ℕ) (lam : ι → ℝ), (∀ i, 0 ≤ lam i) →
    (Finset.univ.filter (fun i => lam i ≠ 0)).card ≤ K →
    ∃ T : Finset ι, LI g T ∧ ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i, i ∉ T → μ i = 0) ∧
      ∑ i, μ i • g i = ∑ i, lam i • g i := by
  intro K
  induction K with
  | zero =>
    intro lam hlam hcard
    refine ⟨∅, fun f _ i hi => absurd hi (Finset.notMem_empty i), lam, hlam, ?_, rfl⟩
    intro i _
    by_contra h
    have hi : i ∈ Finset.univ.filter (fun i => lam i ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    have := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  | succ K ih =>
    intro lam hlam hcard
    obtain ⟨S, hS⟩ : ∃ S : Finset ι, S = Finset.univ.filter (fun i => lam i ≠ 0) := ⟨_, rfl⟩
    have memS : ∀ i, i ∈ S ↔ lam i ≠ 0 := by intro i; rw [hS]; simp
    rw [← hS] at hcard
    by_cases hLI : LI g S
    · refine ⟨S, hLI, lam, hlam, fun i hi => ?_, rfl⟩
      by_contra h
      exact hi ((memS i).mpr h)
    · unfold LI at hLI
      push_neg at hLI
      obtain ⟨f, hf, i₀, hi₀S, hfi₀⟩ := hLI
      have hc : ∑ i, (if i ∈ S then f i else 0) • g i = 0 := by
        calc ∑ i, (if i ∈ S then f i else 0) • g i
            = ∑ i ∈ S, (if i ∈ S then f i else 0) • g i :=
              Eq.symm (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [hi]))
          _ = ∑ i ∈ S, f i • g i := Finset.sum_congr rfl (fun i hi => by simp [hi])
          _ = 0 := hf
      obtain ⟨d, hd0, hdS, hdi₀⟩ : ∃ d : ι → ℝ, ∑ i, d i • g i = 0 ∧
          (∀ i, i ∉ S → d i = 0) ∧ 0 < d i₀ := by
        rcases lt_or_gt_of_ne hfi₀ with hneg | hpos
        · refine ⟨fun i => -(if i ∈ S then f i else 0), ?_, ?_, ?_⟩
          · simp only [neg_smul, Finset.sum_neg_distrib, hc, neg_zero]
          · intro i hi; simp [hi]
          · simp only [if_pos hi₀S]; linarith
        · refine ⟨fun i => if i ∈ S then f i else 0, hc, ?_, ?_⟩
          · intro i hi; simp [hi]
          · simp only [if_pos hi₀S]; exact hpos
      have hdpos : ∀ i, 0 < d i → i ∈ S := by
        intro i hi
        by_contra h
        rw [hdS i h] at hi
        exact lt_irrefl _ hi
      obtain ⟨P, hP⟩ : ∃ P : Finset ι, P = Finset.univ.filter (fun i => 0 < d i) := ⟨_, rfl⟩
      have memP : ∀ i, i ∈ P ↔ 0 < d i := by intro i; rw [hP]; simp
      have hPne : P.Nonempty := ⟨i₀, (memP i₀).mpr hdi₀⟩
      obtain ⟨i₁, hi₁P, hmin⟩ := Finset.exists_min_image P (fun i => lam i / d i) hPne
      have hd1 : 0 < d i₁ := (memP i₁).mp hi₁P
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = lam i₁ / d i₁ := ⟨_, rfl⟩
      have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (hlam i₁) hd1.le
      have hlam' : ∀ i, 0 ≤ lam i - t * d i := by
        intro i
        by_cases hdi : 0 < d i
        · have h1 : t ≤ lam i / d i := by rw [ht]; exact hmin i ((memP i).mpr hdi)
          rw [le_div_iff₀ hdi] at h1
          linarith
        · push_neg at hdi
          nlinarith [hlam i, ht0, hdi]
      have hzero : lam i₁ - t * d i₁ = 0 := by
        rw [ht, div_mul_cancel₀ _ hd1.ne', sub_self]
      have hsupp : Finset.univ.filter (fun i => lam i - t * d i ≠ 0) ⊆ S.erase i₁ := by
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [Finset.mem_erase]
        refine ⟨fun h => hi.2 (by rw [h]; exact hzero), ?_⟩
        by_contra hiS
        apply hi.2
        rw [hdS i hiS]
        have : lam i = 0 := by
          by_contra h'
          exact hiS ((memS i).mpr h')
        rw [this]
        ring
      have hcard' : (Finset.univ.filter (fun i => lam i - t * d i ≠ 0)).card ≤ K := by
        have h1 := Finset.card_le_card hsupp
        have h2 := Finset.card_erase_of_mem (hdpos i₁ hd1)
        omega
      obtain ⟨T, hT, μ, hμ0, hμT, hμsum⟩ := ih (fun i => lam i - t * d i) hlam' hcard'
      refine ⟨T, hT, μ, hμ0, hμT, ?_⟩
      have hsplit : ∑ i, (lam i - t * d i) • g i = ∑ i, lam i • g i - t • ∑ i, d i • g i := by
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [sub_smul, mul_smul]
      rw [hμsum, hsplit, hd0, smul_zero, sub_zero]

def coneOf (g : ι → (Fin N → ℝ)) : Set (Fin N → ℝ) :=
  {x | ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i • g i = x}

theorem mem_coneOf (g : ι → (Fin N → ℝ)) (x : Fin N → ℝ) :
    x ∈ coneOf g ↔ ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i • g i = x := Iff.rfl

def coneT (g : ι → (Fin N → ℝ)) (T : Finset ι) : Set (Fin N → ℝ) :=
  {x | ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i, i ∉ T → μ i = 0) ∧ ∑ i, μ i • g i = x}

theorem mem_coneT (g : ι → (Fin N → ℝ)) (T : Finset ι) (x : Fin N → ℝ) :
    x ∈ coneT g T ↔
      ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i, i ∉ T → μ i = 0) ∧ ∑ i, μ i • g i = x := Iff.rfl

theorem sum_ext_T (g : ι → (Fin N → ℝ)) (T : Finset ι) (μ : T → ℝ) :
    ∑ i, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i = ∑ i : T, μ i • g i := by
  have h1 : ∑ i ∈ T, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i =
      ∑ i, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i :=
    Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by rw [dif_neg hi, zero_smul])
  rw [← h1, ← Finset.sum_coe_sort T]
  apply Finset.sum_congr rfl
  intro i _
  rw [dif_pos i.2]

theorem sum_restrict_T (g : ι → (Fin N → ℝ)) (T : Finset ι) (μ : ι → ℝ)
    (hμT : ∀ i, i ∉ T → μ i = 0) :
    ∑ i : T, μ i • g i = ∑ i, μ i • g i := by
  have h1 : ∑ i : T, μ i • g i = ∑ i ∈ T, μ i • g i := Finset.sum_coe_sort T (fun i => μ i • g i)
  rw [h1]
  exact Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by rw [hμT i hi, zero_smul])

theorem coneT_closed (g : ι → (Fin N → ℝ)) (T : Finset ι) (hT : LI g T) :
    IsClosed (coneT g T) := by
  let L : (T → ℝ) →ₗ[ℝ] (Fin N → ℝ) := Fintype.linearCombination ℝ (fun i : T => g i)
  have hL : ∀ μ : T → ℝ, L μ = ∑ i : T, μ i • g i := fun μ => rfl
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro μ hμ
    rw [hL] at hμ
    have h1 : ∑ i ∈ T, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i = 0 := by
      have h3 : ∑ i ∈ T, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i =
          ∑ i, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i :=
        Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by rw [dif_neg hi, zero_smul])
      rw [h3, sum_ext_T]
      exact hμ
    have h2 := hT _ h1
    funext i
    have := h2 i i.2
    rw [dif_pos i.2] at this
    exact this
  have hA : IsClosed {μ : T → ℝ | ∀ i, 0 ≤ μ i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  have heq : coneT g T = L '' {μ : T → ℝ | ∀ i, 0 ≤ μ i} := by
    ext x
    rw [mem_coneT]
    constructor
    · rintro ⟨μ, hμ0, hμT, rfl⟩
      refine ⟨fun i => μ i, fun i => hμ0 i, ?_⟩
      rw [hL]
      exact sum_restrict_T g T μ hμT
    · rintro ⟨μ, hμ0, rfl⟩
      refine ⟨fun i => if h : i ∈ T then μ ⟨i, h⟩ else 0, ?_, ?_, ?_⟩
      · intro i
        show 0 ≤ (if h : i ∈ T then μ ⟨i, h⟩ else 0)
        by_cases h : i ∈ T
        · rw [dif_pos h]; exact hμ0 _
        · rw [dif_neg h]
      · intro i hi
        show (if h : i ∈ T then μ ⟨i, h⟩ else 0) = 0
        rw [dif_neg hi]
      · rw [hL]
        exact sum_ext_T g T μ
  rw [heq]
  exact (LinearMap.isClosedEmbedding_of_injective hker).isClosedMap _ hA

theorem cone_closed (g : ι → (Fin N → ℝ)) : IsClosed (coneOf g) := by
  have heq : coneOf g = ⋃ (T : Finset ι), ⋃ (_ : LI g T), coneT g T := by
    ext x
    rw [mem_coneOf, Set.mem_iUnion₂]
    constructor
    · rintro ⟨lam, hlam, rfl⟩
      obtain ⟨T, hT, μ, hμ0, hμT, hμ⟩ :=
        carath g (Finset.univ.filter (fun i => lam i ≠ 0)).card lam hlam le_rfl
      exact ⟨T, hT, (mem_coneT g T _).mpr ⟨μ, hμ0, hμT, hμ⟩⟩
    · rintro ⟨T, _, hx⟩
      obtain ⟨μ, hμ0, _, hμ⟩ := (mem_coneT g T x).mp hx
      exact ⟨μ, hμ0, hμ⟩
  rw [heq]
  exact isClosed_iUnion_of_finite (fun T => isClosed_iUnion_of_finite (fun hT => coneT_closed g T hT))

theorem stiemke (g : ι → (Fin N → ℝ))
    (h : ∀ lam : ι → ℝ, (∀ i, 0 ≤ lam i) → (∀ k, 0 ≤ (∑ i, lam i • g i) k) →
      ∑ i, lam i • g i = 0) :
    ∃ w : Fin N → ℝ, (∀ k, 0 < w k) ∧ ∀ i, ∑ k, w k * g i k ≤ 0 := by
  have hconv : Convex ℝ (coneOf g) := by
    intro x hx y hy a b ha hb _
    obtain ⟨l1, hl1, rfl⟩ := (mem_coneOf g x).mp hx
    obtain ⟨l2, hl2, rfl⟩ := (mem_coneOf g y).mp hy
    refine (mem_coneOf g _).mpr ⟨fun i => a * l1 i + b * l2 i,
      fun i => add_nonneg (mul_nonneg ha (hl1 i)) (mul_nonneg hb (hl2 i)), ?_⟩
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [add_smul, mul_smul, mul_smul]
  have hclosed : IsClosed (coneOf g) := cone_closed g
  have hdisj : Disjoint (stdSimplex ℝ (Fin N)) (coneOf g) := by
    rw [Set.disjoint_left]
    intro y hy hyc
    obtain ⟨lam, hlam, rfl⟩ := (mem_coneOf g y).mp hyc
    have h0 := h lam hlam hy.1
    have h1 := hy.2
    rw [h0] at h1
    simp at h1
  obtain ⟨f, u, v, hfu, huv, hfv⟩ := geometric_hahn_banach_compact_closed
    (convex_stdSimplex ℝ (Fin N)) (isCompact_stdSimplex ℝ (Fin N)) hconv hclosed hdisj
  have h0mem : (0 : Fin N → ℝ) ∈ coneOf g := (mem_coneOf g 0).mpr ⟨0, fun _ => le_rfl, by simp⟩
  have hv : v < 0 := by
    have := hfv 0 h0mem
    simpa using this
  have hgi : ∀ i, 0 ≤ f (g i) := by
    intro i
    by_contra hneg
    push_neg at hneg
    have hmem : (v / f (g i)) • g i ∈ coneOf g := by
      refine (mem_coneOf g _).mpr ⟨fun j => if j = i then v / f (g i) else 0, fun j => ?_, ?_⟩
      · show 0 ≤ (if j = i then v / f (g i) else 0)
        by_cases hj : j = i
        · rw [if_pos hj]; exact le_of_lt (div_pos_of_neg_of_neg hv hneg)
        · rw [if_neg hj]
      · simp [ite_smul]
    have := hfv _ hmem
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
    exact lt_irrefl _ this
  have he : ∀ k : Fin N, f (fun j => if k = j then (1 : ℝ) else 0) < 0 :=
    fun k => lt_trans (hfu _ (ite_eq_mem_stdSimplex ℝ k)) (lt_trans huv hv)
  have hfx : ∀ x : Fin N → ℝ, f x = ∑ k, x k * f (fun j => if k = j then (1 : ℝ) else 0) := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul, smul_eq_mul]
  refine ⟨fun k => - f (fun j => if k = j then (1 : ℝ) else 0), fun k => neg_pos.mpr (he k),
    fun i => ?_⟩
  show ∑ k, -f (fun j => if k = j then (1 : ℝ) else 0) * g i k ≤ 0
  have h1 := hgi i
  rw [hfx] at h1
  have h2 : ∑ k, -f (fun j => if k = j then (1 : ℝ) else 0) * g i k =
      - ∑ k, g i k * f (fun j => if k = j then (1 : ℝ) else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h2]
  linarith

end Cone

section Weights

variable {n m : ℕ}

def Dv (p : Fin m × Fin n × Fin n) (k : Fin n) : ℝ :=
  (if k = p.2.2 then 1 else 0) - (if k = p.2.1 then 1 else 0)

theorem sum_Dv (p : Fin m × Fin n × Fin n) : ∑ k, Dv p k = 0 := by
  simp [Dv, Finset.sum_sub_distrib]

noncomputable def gen (v z : Fin n → Fin m → ℝ) (p : Fin m × Fin n × Fin n) : Fin n → ℝ :=
  fun k => if 0 < z p.2.1 p.1 then v k p.1 * Dv p k else 0

theorem po_weights (v z : Fin n → Fin m → ℝ) (hPO : IsParetoOptimal v z) :
    ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧
      ∀ (i j : Fin n) (o : Fin m), 0 < z i o → w j * v j o ≤ w i * v i o := by
  have hz := hPO.1
  have hstiem : ∀ lam : Fin m × Fin n × Fin n → ℝ, (∀ p, 0 ≤ lam p) →
      (∀ k, 0 ≤ (∑ p, lam p • gen v z p) k) → ∑ p, lam p • gen v z p = 0 := by
    intro lam hlam hy
    by_contra hne
    obtain ⟨k₀, hk₀⟩ := Function.ne_iff.mp hne
    have hk₀pos : 0 < (∑ p, lam p • gen v z p) k₀ := lt_of_le_of_ne (hy k₀) (Ne.symm hk₀)
    -- flows
    let c : Fin m × Fin n × Fin n → ℝ := fun p => if 0 < z p.2.1 p.1 then lam p else 0
    have hc0 : ∀ p, 0 ≤ c p := by
      intro p; show 0 ≤ (if 0 < z p.2.1 p.1 then lam p else 0); split_ifs
      · exact hlam p
      · exact le_rfl
    let Dl : Fin n → Fin m → ℝ := fun k o => ∑ p, if p.1 = o then c p * Dv p k else 0
    have hyk : ∀ k, (∑ p, lam p • gen v z p) k = ∑ o, v k o * Dl k o := by
      intro k
      rw [Finset.sum_apply]
      have e1 : ∀ p : Fin m × Fin n × Fin n, (lam p • gen v z p) k = v k p.1 * (c p * Dv p k) := by
        intro p
        show lam p * (if 0 < z p.2.1 p.1 then v k p.1 * Dv p k else 0) =
          v k p.1 * ((if 0 < z p.2.1 p.1 then lam p else 0) * Dv p k)
        split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun p _ => e1 p)]
      show ∑ p, v k p.1 * (c p * Dv p k) = ∑ o, v k o * ∑ p, (if p.1 = o then c p * Dv p k else 0)
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      simp
    have hDlsum : ∀ o, ∑ k, Dl k o = 0 := by
      intro o
      show ∑ k, ∑ p, (if p.1 = o then c p * Dv p k else 0) = 0
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro p _
      by_cases hpo : p.1 = o
      · simp only [if_pos hpo]
        rw [← Finset.mul_sum, sum_Dv, mul_zero]
      · simp [hpo]
    obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ p, lam p := ⟨_, rfl⟩
    have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg (fun p _ => hlam p)
    have hDllow : ∀ k o, -S ≤ Dl k o := by
      intro k o
      show -S ≤ ∑ p, (if p.1 = o then c p * Dv p k else 0)
      rw [hS, ← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro p _
      have hl := hlam p
      show -lam p ≤ if p.1 = o then (if 0 < z p.2.1 p.1 then lam p else 0) * Dv p k else 0
      unfold Dv
      split_ifs <;> linarith
    have hDlnn : ∀ k o, ¬ 0 < z k o → 0 ≤ Dl k o := by
      intro k o hko
      show 0 ≤ ∑ p, (if p.1 = o then c p * Dv p k else 0)
      apply Finset.sum_nonneg
      intro p _
      have hl := hlam p
      show 0 ≤ if p.1 = o then (if 0 < z p.2.1 p.1 then lam p else 0) * Dv p k else 0
      by_cases hpo : p.1 = o
      · rw [if_pos hpo]
        by_cases hz' : 0 < z p.2.1 p.1
        · rw [if_pos hz']
          have hne : k ≠ p.2.1 := by
            intro e
            apply hko
            rw [e, ← hpo]
            exact hz'
          unfold Dv
          rw [if_neg hne]
          split_ifs <;> linarith
        · rw [if_neg hz', zero_mul]
      · rw [if_neg hpo]
    -- step size
    obtain ⟨δ₀, hδ₀, hδ₀le⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ k o, 0 < z k o → δ₀ ≤ z k o := by
      by_cases hne' : (Finset.univ.filter (fun q : Fin n × Fin m => 0 < z q.1 q.2)).Nonempty
      · refine ⟨(Finset.univ.filter (fun q : Fin n × Fin m => 0 < z q.1 q.2)).inf' hne'
          (fun q => z q.1 q.2), ?_, ?_⟩
        · rw [Finset.lt_inf'_iff]
          intro q hq
          exact (Finset.mem_filter.mp hq).2
        · intro k o hko
          exact Finset.inf'_le (fun q : Fin n × Fin m => z q.1 q.2)
            (Finset.mem_filter.mpr ⟨Finset.mem_univ (k, o), hko⟩)
      · refine ⟨1, one_pos, fun k o hko => ?_⟩
        exact (hne' ⟨(k, o), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hko⟩⟩).elim
    obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = δ₀ / (1 + S) := ⟨_, rfl⟩
    have hS1 : (1 + S) ≠ 0 := ne_of_gt (by linarith)
    have hε0 : 0 ≤ ε := by rw [hε]; exact div_nonneg hδ₀.le (by linarith)
    have hεS : ε * (1 + S) = δ₀ := by
      rw [hε, div_mul_cancel₀ _ hS1]
    rw [mul_add, mul_one] at hεS
    let z' : Fin n → Fin m → ℝ := fun k o => z k o + ε * Dl k o
    have hz'feas : IsFeasible z' := by
      refine ⟨fun k o => ?_, fun o => ?_⟩
      · show 0 ≤ z k o + ε * Dl k o
        by_cases hko : 0 < z k o
        · have h1 := hδ₀le k o hko
          have h2 := hDllow k o
          have h3 : 0 ≤ ε * (Dl k o + S) := mul_nonneg hε0 (by linarith)
          rw [mul_add] at h3
          linarith
        · have h1 := hDlnn k o hko
          have h2 := hz.1 k o
          have h3 : 0 ≤ ε * Dl k o := mul_nonneg hε0 h1
          linarith
      · show ∑ k, (z k o + ε * Dl k o) = 1
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hDlsum o, mul_zero, add_zero]
        exact hz.2 o
    have hu : ∀ k, utilityProfile v z' k =
        utilityProfile v z k + ε * (∑ p, lam p • gen v z p) k := by
      intro k
      rw [hyk k]
      show ∑ o, v k o * (z k o + ε * Dl k o) = ∑ o, v k o * z k o + ε * ∑ o, v k o * Dl k o
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro o _
      ring
    have hεpos : 0 < ε := by rw [hε]; exact div_pos hδ₀ (by linarith)
    apply hPO.2
    refine ⟨z', hz'feas, fun k => ?_, ⟨k₀, ?_⟩⟩
    · rw [hu k]
      have := hy k
      have := mul_nonneg hε0 this
      linarith
    · rw [hu k₀]
      have := mul_pos hεpos hk₀pos
      linarith
  obtain ⟨w, hw, hwg⟩ := stiemke (gen v z) hstiem
  refine ⟨w, hw, fun i j o hio => ?_⟩
  have h1 := hwg (o, i, j)
  have h2 : ∑ k, w k * gen v z (o, i, j) k = w j * v j o - w i * v i o := by
    have e : ∀ k, w k * gen v z (o, i, j) k =
        (if k = j then w k * v k o else 0) - (if k = i then w k * v k o else 0) := by
      intro k
      show w k * (if 0 < z i o then v k o * Dv (o, i, j) k else 0) = _
      rw [if_pos hio]
      dsimp only [Dv]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_sub_distrib]
    simp
  linarith

theorem weights_po (v z : Fin n → Fin m → ℝ) (hz : IsFeasible z) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i)
    (hmax : ∀ (i j : Fin n) (o : Fin m), 0 < z i o → w j * v j o ≤ w i * v i o) :
    IsParetoOptimal v z := by
  refine ⟨hz, ?_⟩
  rintro ⟨z', hz', hle, ⟨i₀, hlt⟩⟩
  have e : ∀ zz : Fin n → Fin m → ℝ,
      ∑ i, w i * utilityProfile v zz i = ∑ o, ∑ i, w i * (v i o * zz i o) := by
    intro zz
    simp only [utilityProfile, bundleUtility, Finset.mul_sum]
    exact Finset.sum_comm
  have hW : ∑ i, w i * utilityProfile v z' i ≤ ∑ i, w i * utilityProfile v z i := by
    rw [e z', e z]
    apply Finset.sum_le_sum
    intro o _
    obtain ⟨i₁, hi₁⟩ : ∃ i, 0 < z i o := by
      by_contra hcon
      push_neg at hcon
      have := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => hcon i)
      rw [hz.2 o] at this
      linarith
    have hc : ∀ i, 0 < z i o → w i * v i o = w i₁ * v i₁ o :=
      fun i hi => le_antisymm (hmax i₁ i o hi₁) (hmax i i₁ o hi)
    calc ∑ i, w i * (v i o * z' i o) ≤ ∑ i, (w i₁ * v i₁ o) * z' i o := by
          apply Finset.sum_le_sum
          intro i _
          have h1 := hmax i₁ i o hi₁
          have h2 := hz'.1 i o
          nlinarith
      _ = w i₁ * v i₁ o := by rw [← Finset.mul_sum, hz'.2 o, mul_one]
      _ = ∑ i, (w i₁ * v i₁ o) * z i o := by rw [← Finset.mul_sum, hz.2 o, mul_one]
      _ = ∑ i, w i * (v i o * z i o) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : 0 < z i o
          · rw [← hc i hi]; ring
          · have : z i o = 0 := le_antisymm (not_lt.mp hi) (hz.1 i o)
            rw [this]; ring
  have hW' : ∑ i, w i * utilityProfile v z i < ∑ i, w i * utilityProfile v z' i := by
    apply Finset.sum_lt_sum
    · intro i _
      exact mul_le_mul_of_nonneg_left (hle i) (hw i).le
    · exact ⟨i₀, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt (hw i₀)⟩
  linarith

end Weights

end Aux_MS_S3

open CompetitiveChores.RichFamily in
theorem solution {n m : ℕ} (v z : Fin n → Fin m → ℝ) (hz : IsParetoOptimal v z) :
    ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧
      ∀ i j : Fin n, i ≠ j → 0 < w j / w i ∧ ∀ o : Fin m,
        (0 < v i o * v j o →
          (w j / w i < |v i o| / |v j o| → (0 < v i o → z j o = 0) ∧ (v i o < 0 → z i o = 0)) ∧
          (|v i o| / |v j o| < w j / w i → (0 < v i o → z i o = 0) ∧ (v i o < 0 → z j o = 0))) ∧
        (v i o * v j o < 0 → (v i o < 0 → z i o = 0) ∧ (v j o < 0 → z j o = 0)) ∧
        (v i o = 0 → v j o ≠ 0 → (v j o < 0 → z j o = 0) ∧ (0 < v j o → z i o = 0)) ∧
        (0 < z i o → 0 < z j o →
          (v j o ≠ 0 ∧ v i o / v j o = w j / w i) ∨ (v i o = 0 ∧ v j o = 0)) := by
  obtain ⟨w, hw, hmax⟩ := Aux_MS_S3.po_weights v z hz
  have hzero : ∀ a b o, w a * v a o < w b * v b o → z a o = 0 := by
    intro a b o h
    by_contra hne
    have hpos : 0 < z a o := lt_of_le_of_ne (hz.1.1 a o) (Ne.symm hne)
    have := hmax a b o hpos
    linarith
  refine ⟨w, hw, fun i j _ => ⟨div_pos (hw j) (hw i), fun o => ⟨?_, ?_, ?_, ?_⟩⟩⟩
  · intro hprod
    have hwi := hw i
    have hwj := hw j
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hprod with ⟨hvi, hvj⟩ | ⟨hvi, hvj⟩
    · rw [abs_of_pos hvi, abs_of_pos hvj]
      refine ⟨fun hlt => ⟨fun _ => ?_, fun h => absurd h (not_lt.mpr hvi.le)⟩,
              fun hlt => ⟨fun _ => ?_, fun h => absurd h (not_lt.mpr hvi.le)⟩⟩
      · rw [div_lt_div_iff₀ hwi hvj] at hlt
        exact hzero j i o (by nlinarith [mul_comm (v i o) (w i)])
      · rw [div_lt_div_iff₀ hvj hwi] at hlt
        exact hzero i j o (by nlinarith [mul_comm (v i o) (w i), mul_comm (w j) (v j o)])
    · rw [abs_of_neg hvi, abs_of_neg hvj]
      have hvj' : 0 < -v j o := neg_pos.mpr hvj
      refine ⟨fun hlt => ⟨fun h => absurd h (not_lt.mpr hvi.le), fun _ => ?_⟩,
              fun hlt => ⟨fun h => absurd h (not_lt.mpr hvi.le), fun _ => ?_⟩⟩
      · rw [div_lt_div_iff₀ hwi hvj'] at hlt
        exact hzero i j o (by nlinarith)
      · rw [div_lt_div_iff₀ hvj' hwi] at hlt
        exact hzero j i o (by nlinarith)
  · intro hprod
    rcases mul_neg_iff.mp hprod with ⟨hvi, hvj⟩ | ⟨hvi, hvj⟩
    · refine ⟨fun h => absurd h (not_lt.mpr hvi.le), fun _ => hzero j i o ?_⟩
      have h1 : w j * v j o < 0 := mul_neg_of_pos_of_neg (hw j) hvj
      have h2 : 0 < w i * v i o := mul_pos (hw i) hvi
      linarith
    · refine ⟨fun _ => hzero i j o ?_, fun h => absurd h (not_lt.mpr hvj.le)⟩
      have h1 : w i * v i o < 0 := mul_neg_of_pos_of_neg (hw i) hvi
      have h2 : 0 < w j * v j o := mul_pos (hw j) hvj
      linarith
  · intro hvi _
    refine ⟨fun hneg => hzero j i o ?_, fun hpos => hzero i j o ?_⟩
    · rw [hvi, mul_zero]; exact mul_neg_of_pos_of_neg (hw j) hneg
    · rw [hvi, mul_zero]; exact mul_pos (hw j) hpos
  · intro hi hj
    have e : w i * v i o = w j * v j o := le_antisymm (hmax j i o hj) (hmax i j o hi)
    by_cases hvj : v j o = 0
    · right
      refine ⟨?_, hvj⟩
      rw [hvj, mul_zero] at e
      rcases mul_eq_zero.mp e with h | h
      · exact absurd h (hw i).ne'
      · exact h
    · left
      refine ⟨hvj, ?_⟩
      rw [div_eq_div_iff hvj (hw i).ne']
      linarith [mul_comm (v i o) (w i)]
