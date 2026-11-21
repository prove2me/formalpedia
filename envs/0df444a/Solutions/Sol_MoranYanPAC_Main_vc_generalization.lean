-- Prove2me | solution 1 for MoranYanPAC.Main.vc_generalization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:56:11.910805+00:00
-- url     : https://prove2.me/submissions/7c78f307-a35b-4d21-a560-36f38bde5104

import Mathlib
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_MoranYanPAC_Main_EmpiricalLoss
import Definitions.Def_MoranYanPAC_Main_PACExperiment

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.Sauer

theorem sum_choose_le (n d : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n) :
    (∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ)) ≤ (Real.exp 1 * n / d) ^ d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hd hdn)
  have hr : (1 : ℝ) ≤ n / d := by rw [le_div_iff₀ hdpos]; simp only [one_mul]; exact_mod_cast hdn
  have step1 : (∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ)) ≤
      ∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ) * (n / d) ^ (d - k) := by
    refine Finset.sum_le_sum fun k _ => ?_
    have : (1 : ℝ) ≤ (n / d) ^ (d - k) := one_le_pow₀ hr
    nlinarith [(Nat.cast_nonneg (n.choose k) : (0 : ℝ) ≤ n.choose k)]
  have step2 : ∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ) * (n / d) ^ (d - k) =
      (n / d : ℝ) ^ d * ∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ) * (d / n : ℝ) ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have : (n / d : ℝ) ^ d = (n / d) ^ (d - k) * (n / d) ^ k := by rw [← pow_add]; congr 1; omega
    rw [this]
    have h2 : (n / d : ℝ) ^ k * (d / n : ℝ) ^ k = 1 := by
      rw [← mul_pow]; rw [div_mul_div_comm, mul_comm (n : ℝ) d, div_self (by positivity)]; simp
    calc (n.choose k : ℝ) * (n / d) ^ (d - k) = (n.choose k : ℝ) * (n / d) ^ (d - k) * ((n / d : ℝ) ^ k * (d / n : ℝ) ^ k) := by rw [h2]; ring
      _ = _ := by ring
  have step3 : ∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ) * (d / n : ℝ) ^ k ≤
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (d / n : ℝ) ^ k := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega)) ?_
    intro k _ _; positivity
  have step4 : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (d / n : ℝ) ^ k = (1 + d / n : ℝ) ^ n := by
    rw [show (1 + (d : ℝ) / n) = d / n + 1 by ring, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [one_pow]
    ring
  have step5 : (1 + d / n : ℝ) ^ n ≤ Real.exp 1 ^ d := by
    have h1 : (1 + d / n : ℝ) ≤ Real.exp (d / n) := by linarith [Real.add_one_le_exp (d / n : ℝ)]
    calc (1 + d / n : ℝ) ^ n ≤ Real.exp (d / n) ^ n := pow_le_pow_left₀ (by positivity) h1 n
      _ = Real.exp ((d / n) * n) := by rw [← Real.exp_nat_mul]; ring_nf
      _ = Real.exp d := by rw [div_mul_cancel₀ _ hnpos.ne']
      _ = Real.exp 1 ^ d := by rw [← Real.exp_nat_mul]; ring_nf
  calc (∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ)) ≤ _ := step1
    _ = _ := step2
    _ ≤ (n / d : ℝ) ^ d * (1 + d / n : ℝ) ^ n := by
        rw [← step4]; exact mul_le_mul_of_nonneg_left step3 (by positivity)
    _ ≤ (n / d : ℝ) ^ d * Real.exp 1 ^ d := mul_le_mul_of_nonneg_left step5 (by positivity)
    _ = (Real.exp 1 * n / d) ^ d := by rw [← mul_pow]; congr 1; ring

end MoranYanPAC.Dev.Sauer
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.VC

open Finset

theorem rademacher_tail (n : ℕ) (c : Fin n → ℝ) (t V : ℝ) (ht : 0 < t) (hVpos : 0 < V)
    (hV : ∑ i, c i ^ 2 ≤ V) :
    (((Finset.univ : Finset (Fin n → Bool)).filter
      (fun σ => t ≤ ∑ i, (if σ i then c i else -c i))).card : ℝ) ≤
      2 ^ n * Real.exp (-(t ^ 2) / (2 * V)) := by
  classical
  · set l := t / V with hl
    have hl0 : 0 < l := by positivity
    have step1 : (((Finset.univ : Finset (Fin n → Bool)).filter
        (fun σ => t ≤ ∑ i, (if σ i then c i else -c i))).card : ℝ) ≤
        ∑ σ : Fin n → Bool, Real.exp (l * (∑ i, (if σ i then c i else -c i)) - l * t) := by
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_le_sum fun σ _ => ?_
      split_ifs with h
      · have : 1 ≤ Real.exp (l * (∑ i, (if σ i then c i else -c i)) - l * t) := by
          apply Real.one_le_exp
          nlinarith
        exact this
      · exact (Real.exp_pos _).le
    refine step1.trans ?_
    have step2 : ∑ σ : Fin n → Bool, Real.exp (l * (∑ i, (if σ i then c i else -c i)) - l * t) =
        Real.exp (-(l * t)) * ∏ i : Fin n, (Real.exp (l * c i) + Real.exp (-(l * c i))) := by
      have : ∀ σ : Fin n → Bool, Real.exp (l * (∑ i, (if σ i then c i else -c i)) - l * t) =
          Real.exp (-(l * t)) * ∏ i, Real.exp (l * (if σ i then c i else -c i)) := by
        intro σ
        rw [← Real.exp_sum, ← Real.exp_add, ← Finset.mul_sum]; congr 1; ring
      simp_rw [this]
      rw [← Finset.mul_sum]
      congr 1
      have := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Bool))
        (fun i (b : Bool) => Real.exp (l * (if b then c i else -c i)))
      rw [Fintype.piFinset_univ] at this
      rw [← this]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [add_comm]
    rw [step2]
    have step3 : ∏ i : Fin n, (Real.exp (l * c i) + Real.exp (-(l * c i))) ≤
        2 ^ n * Real.exp (l ^ 2 * (∑ i, c i ^ 2) / 2) := by
      have : ∀ i : Fin n, Real.exp (l * c i) + Real.exp (-(l * c i)) ≤ 2 * Real.exp ((l * c i) ^ 2 / 2) := by
        intro i
        have := Real.cosh_le_exp_half_sq (l * c i)
        rw [Real.cosh_eq] at this
        linarith
      calc ∏ i : Fin n, (Real.exp (l * c i) + Real.exp (-(l * c i)))
          ≤ ∏ i : Fin n, (2 * Real.exp ((l * c i) ^ 2 / 2)) :=
            Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => this i)
        _ = 2 ^ n * Real.exp (l ^ 2 * (∑ i, c i ^ 2) / 2) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
              ← Real.exp_sum, Finset.mul_sum, ← Finset.sum_div]
            congr 3
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
    calc Real.exp (-(l * t)) * ∏ i : Fin n, (Real.exp (l * c i) + Real.exp (-(l * c i)))
        ≤ Real.exp (-(l * t)) * (2 ^ n * Real.exp (l ^ 2 * V / 2)) := by
          refine mul_le_mul_of_nonneg_left (step3.trans ?_) (Real.exp_pos _).le
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
          have : l ^ 2 * (∑ i, c i ^ 2) ≤ l ^ 2 * V := mul_le_mul_of_nonneg_left hV (sq_nonneg _)
          linarith
      _ = 2 ^ n * Real.exp (-(t ^ 2) / (2 * V)) := by
          rw [← mul_assoc, mul_comm (Real.exp _) ((2:ℝ)^n), mul_assoc, ← Real.exp_add]
          congr 2
          rw [hl]; field_simp; ring

end MoranYanPAC.Dev.VC
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.VC

open Finset

theorem restr_card_le {X : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Set (X → Bool))
    (d : ℕ) (hvc : UnderstandingML.vcDim G ≤ d) (pts : ι → X) :
    ∃ 𝒜 : Finset (Finset ι), (∀ h ∈ G, (Finset.univ.filter (fun j => h (pts j) = true)) ∈ 𝒜) ∧
      𝒜.card ≤ ∑ k ∈ Finset.range (d + 1), (Fintype.card ι).choose k := by
  classical
  let 𝒜 : Finset (Finset ι) :=
    (Finset.univ : Finset (Finset ι)).filter (fun J => ∃ h ∈ G, ∀ j, (j ∈ J ↔ h (pts j) = true))
  refine ⟨𝒜, fun h hh => ?_, ?_⟩
  · simp only [𝒜, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h, hh, fun j => by simp⟩
  · have h1 := Finset.card_le_card_shatterer 𝒜
    have h3 := Finset.card_shatterer_le_sum_vcDim (𝒜 := 𝒜)
    have h4 : 𝒜.vcDim ≤ d := by
      unfold Finset.vcDim
      refine Finset.sup_le fun J hJ => ?_
      have hsh := Finset.mem_shatterer.1 hJ
      -- pts injective on J
      have hinj : Set.InjOn pts (J : Set ι) := by
        intro j1 hj1 j2 hj2 heq
        by_contra hne
        obtain ⟨u, hu, hJu⟩ := hsh (t := {j1}) (by simpa using hj1)
        obtain ⟨h, hh, hpat⟩ := (Finset.mem_filter.1 hu).2
        have h1 : j1 ∈ J ∩ u := by rw [hJu]; simp
        have h2 : j2 ∉ J ∩ u := by
          rw [hJu]; simp; exact fun h => hne h.symm
        have a1 := (hpat j1).1 (Finset.mem_inter.1 h1).2
        have a2 : ¬ (j2 ∈ u) := fun hm => h2 (Finset.mem_inter.2 ⟨hj2, hm⟩)
        have a3 := mt (hpat j2).2 a2
        rw [← heq] at a3
        exact a3 a1
      have hC : UnderstandingML.Shatters G (J.image pts) := by
        intro g
        obtain ⟨u, hu, hJu⟩ := hsh (t := J.filter (fun j => ∃ c : J.image pts, c.val = pts j ∧ g c = true))
          (Finset.filter_subset _ _)
        obtain ⟨h, hh, hpat⟩ := (Finset.mem_filter.1 hu).2
        refine ⟨h, hh, fun c => ?_⟩
        obtain ⟨j, hjJ, hjc⟩ := Finset.mem_image.1 c.2
        have hmem : (j ∈ J ∩ u) ↔ j ∈ J.filter (fun j => ∃ c : J.image pts, c.val = pts j ∧ g c = true) := by
          rw [hJu]
        simp only [Finset.mem_inter, Finset.mem_filter] at hmem
        have e1 : h c.val = true ↔ g c = true := by
          rw [← hjc, ← hpat j]
          constructor
          · intro hu'
            obtain ⟨_, c', hc', hg'⟩ := hmem.1 ⟨hjJ, hu'⟩
            have : c' = c := Subtype.ext (by rw [hc', hjc])
            rwa [← this]
          · intro hg
            exact (hmem.2 ⟨hjJ, c, hjc.symm, hg⟩).2
        cases hh1 : h c.val <;> cases hg1 : g c <;> simp_all
      have hcard : (J.image pts).card = J.card := Finset.card_image_of_injOn hinj
      have : ((J.image pts).card : ℕ∞) ≤ UnderstandingML.vcDim G :=
        le_iSup₂ (f := fun (C : Finset X) (_ : UnderstandingML.Shatters G C) => (C.card : ℕ∞)) _ hC
      rw [hcard] at this
      exact_mod_cast this.trans hvc
    have h5 : ∑ k ∈ Finset.Iic 𝒜.vcDim, (Fintype.card ι).choose k ≤
        ∑ k ∈ Finset.range (d + 1), (Fintype.card ι).choose k := by
      refine Finset.sum_le_sum_of_subset ?_
      intro k hk
      simp only [Finset.mem_Iic, Finset.mem_range] at hk ⊢
      omega
    omega

end MoranYanPAC.Dev.VC
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.VC

open Finset

theorem bad_count (n : ℕ) (α : ℝ) (hα : 0 < α) (Lf : Fin n → Bool → ℝ)
    (h01 : ∀ i b, Lf i b = 0 ∨ Lf i b = 1) :
    (((Finset.univ : Finset (Fin n → Bool)).filter (fun σ =>
      ∑ i, Lf i (σ i) ≤ α * n / 2 ∧ 3 * α * n / 4 < ∑ i, Lf i (!σ i))).card : ℝ) ≤
      2 ^ n * Real.exp (-(α * n / 40)) := by
  classical
  by_cases hemp : (Finset.univ.filter (fun σ : Fin n → Bool =>
      ∑ i, Lf i (σ i) ≤ α * n / 2 ∧ 3 * α * n / 4 < ∑ i, Lf i (!σ i))) = ∅
  · rw [hemp]; simp; positivity
  obtain ⟨σ0, hσ0⟩ := Finset.nonempty_iff_ne_empty.2 hemp
  have hσ0' := (Finset.mem_filter.1 hσ0).2
  set M : ℝ := ∑ i, (Lf i false + Lf i true) with hM
  have hsum : ∀ σ : Fin n → Bool, ∑ i, Lf i (σ i) + ∑ i, Lf i (!σ i) = M := by
    intro σ
    rw [hM, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases σ i <;> simp [add_comm]
  have hLnn : ∀ i b, 0 ≤ Lf i b := fun i b => by rcases h01 i b with h | h <;> rw [h] <;> norm_num
  have hm1nn : 0 ≤ ∑ i, Lf i (σ0 i) := Finset.sum_nonneg fun i _ => hLnn _ _
  have hn : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hσ0'
    · exact_mod_cast h
  have hu : 0 < α * n := by positivity
  set u := α * n with hudef
  have hMpos : 3 * u / 4 < M := by
    have := hsum σ0
    have h2 := hσ0'.2
    have : 3 * α * n / 4 = 3 * u / 4 := by rw [hudef]; ring
    linarith
  set c : Fin n → ℝ := fun i => Lf i false - Lf i true with hc
  have hS : ∀ σ : Fin n → Bool, ∑ i, (if σ i then c i else -c i) =
      ∑ i, Lf i (!σ i) - ∑ i, Lf i (σ i) := by
    intro σ
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases σ i <;> simp [hc]
  have hV : ∑ i, c i ^ 2 ≤ M := by
    rw [hM]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [hc]
    rcases h01 i false with h | h <;> rcases h01 i true with h' | h' <;> simp [h, h']
  set t : ℝ := max (M - u) (3 * u / 2 - M) with ht
  have htpos : u / 4 ≤ t := by
    rw [ht]; rcases le_total (M - u) (3 * u / 2 - M) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hsub : (Finset.univ.filter (fun σ : Fin n → Bool =>
      ∑ i, Lf i (σ i) ≤ α * n / 2 ∧ 3 * α * n / 4 < ∑ i, Lf i (!σ i))) ⊆
      Finset.univ.filter (fun σ : Fin n → Bool => t ≤ ∑ i, (if σ i then c i else -c i)) := by
    intro σ hσ
    have h1 := (Finset.mem_filter.1 hσ).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [hS]
    have hs := hsum σ
    have e1 : 3 * α * n / 4 = 3 * u / 4 := by rw [hudef]; ring
    have e2 : α * n / 2 = u / 2 := by rw [hudef]
    rw [ht]
    refine max_le ?_ ?_ <;> linarith [h1.1, h1.2]
  have hbound := rademacher_tail n c t M (by linarith) (by linarith) hV
  have hcard := Finset.card_le_card hsub
  have key : u / 40 ≤ t ^ 2 / (2 * M) := by
    have hMp : 0 < M := by linarith
    rw [le_div_iff₀ (by positivity)]
    rw [ht]
    rcases le_total (M - u) (3 * u / 2 - M) with h | h
    · rw [max_eq_right h]
      have h' : 0 ≤ 3 * u / 2 - M := by linarith
      nlinarith [sq_nonneg (M - 5 * u / 4), mul_nonneg hu.le h']
    · rw [max_eq_left h]
      have h' : 0 ≤ M - u := by linarith
      nlinarith [sq_nonneg (M - 5 * u / 4), mul_nonneg hu.le h']
  calc _ ≤ ((Finset.univ.filter (fun σ : Fin n → Bool => t ≤ ∑ i, (if σ i then c i else -c i))).card : ℝ) :=
        by exact_mod_cast hcard
    _ ≤ 2 ^ n * Real.exp (-(t ^ 2) / (2 * M)) := hbound
    _ ≤ 2 ^ n * Real.exp (-(α * n / 40)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
        have : -(t ^ 2) / (2 * M) = -(t ^ 2 / (2 * M)) := by ring
        rw [this]
        have : α * n / 40 = u / 40 := by rw [hudef]
        linarith

end MoranYanPAC.Dev.VC
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.VC

open Finset MoranYanPAC.Main

variable {X : Type*}

theorem cnt_eq {Z : Type*} (p : Z → Prop) [DecidablePred p] : ∀ (n : ℕ) (s : Fin n → Z),
    ((List.ofFn s).filter (fun z => decide (p z))).length =
      ∑ i : Fin n, (if p (s i) then 1 else 0) := by
  intro n
  induction n with
  | zero => intro s; simp
  | succ n ih =>
    intro s
    rw [List.ofFn_succ, Fin.sum_univ_succ, List.filter_cons]
    have := ih (fun i => s i.succ)
    by_cases h : p (s 0) <;> simp [h, this] <;> omega

theorem emp_eq (n : ℕ) (s : Fin n → X × Bool) (h : X → Bool) :
    empiricalRate (List.ofFn s) h = (∑ i : Fin n, if h (s i).1 ≠ (s i).2 then (1 : ℝ) else 0) / n := by
  unfold empiricalRate empiricalLoss
  rw [List.length_ofFn]
  congr 1
  have := cnt_eq (fun z : X × Bool => h z.1 ≠ z.2) n s
  rw [this]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp


open Classical in
theorem swap_count (G : Set (X → Bool)) (d : ℕ) (hvc : UnderstandingML.vcDim G ≤ d) (n : ℕ)
    (hn : 0 < n) (α : ℝ) (hα : 0 < α) (z z' : Fin n → X × Bool) :
    (((Finset.univ : Finset (Fin n → Bool)).filter (fun σ : Fin n → Bool => ∃ h ∈ G,
      empiricalRate (List.ofFn (fun i => if σ i then z' i else z i)) h ≤ α / 2 ∧
      3 * α / 4 < empiricalRate (List.ofFn (fun i => if σ i then z i else z' i)) h)).card : ℝ) ≤
    (∑ k ∈ Finset.range (d + 1), (2 * n).choose k) * (2 ^ n * Real.exp (-(α * n / 40))) := by
  classical
  let pts : Fin n × Bool → X := fun j => if j.2 then (z' j.1).1 else (z j.1).1
  let lab : Fin n × Bool → Bool := fun j => if j.2 then (z' j.1).2 else (z j.1).2
  obtain ⟨𝒜, hmem, hcard⟩ := restr_card_le G d hvc pts
  have hιcard : Fintype.card (Fin n × Bool) = 2 * n := by simp [Fintype.card_prod]; ring
  rw [hιcard] at hcard
  let Lf : Finset (Fin n × Bool) → Fin n → Bool → ℝ := fun J i b =>
    if (decide ((i, b) ∈ J)) ≠ lab (i, b) then 1 else 0
  have hLf01 : ∀ J i b, Lf J i b = 0 ∨ Lf J i b = 1 := by
    intro J i b; simp only [Lf]; split_ifs <;> simp
  have hcover : (Finset.univ.filter (fun σ : Fin n → Bool => ∃ h ∈ G,
      empiricalRate (List.ofFn (fun i => if σ i then z' i else z i)) h ≤ α / 2 ∧
      3 * α / 4 < empiricalRate (List.ofFn (fun i => if σ i then z i else z' i)) h)) ⊆
      𝒜.biUnion (fun J => Finset.univ.filter (fun σ : Fin n → Bool =>
        ∑ i, Lf J i (σ i) ≤ α * n / 2 ∧ 3 * α * n / 4 < ∑ i, Lf J i (!σ i))) := by
    intro σ hσ
    obtain ⟨h, hh, e1, e2⟩ := (Finset.mem_filter.1 hσ).2
    refine Finset.mem_biUnion.2 ⟨Finset.univ.filter (fun j => h (pts j) = true), hmem h hh, ?_⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    rw [emp_eq, div_le_iff₀ hnr] at e1
    rw [emp_eq, lt_div_iff₀ hnr] at e2
    have key1 : ∀ (b : Fin n → Bool) (σ' : Fin n → Bool),
        (∀ i, b i = σ' i) →
        ∑ i, Lf (Finset.univ.filter (fun j => h (pts j) = true)) i (b i) =
          ∑ i : Fin n, (if h ((if σ' i then z' i else z i)).1 ≠ ((if σ' i then z' i else z i)).2
            then (1 : ℝ) else 0) := by
      intro b σ' hb
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Lf, hb i, pts, lab]
      cases σ' i <;> simp
    have key2 : ∀ i, Lf (Finset.univ.filter (fun j => h (pts j) = true)) i (!σ i) =
        (if h ((if σ i then z i else z' i)).1 ≠ ((if σ i then z i else z' i)).2 then (1 : ℝ) else 0) := by
      intro i
      simp only [Lf, pts, lab]
      cases σ i <;> simp
    refine ⟨?_, ?_⟩
    · rw [key1 σ σ (fun _ => rfl)]; linarith
    · simp_rw [key2]; linarith
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_biUnion_le (s := 𝒜) (t := fun J => Finset.univ.filter (fun σ : Fin n → Bool =>
        ∑ i, Lf J i (σ i) ≤ α * n / 2 ∧ 3 * α * n / 4 < ∑ i, Lf J i (!σ i)))
  have h3 : ∀ J ∈ 𝒜, ((Finset.univ.filter (fun σ : Fin n → Bool =>
        ∑ i, Lf J i (σ i) ≤ α * n / 2 ∧ 3 * α * n / 4 < ∑ i, Lf J i (!σ i))).card : ℝ) ≤
      2 ^ n * Real.exp (-(α * n / 40)) := fun J _ => bad_count n α hα (Lf J) (hLf01 J)
  calc (_ : ℝ) ≤ ((𝒜.biUnion (fun J => Finset.univ.filter (fun σ : Fin n → Bool =>
        ∑ i, Lf J i (σ i) ≤ α * n / 2 ∧ 3 * α * n / 4 < ∑ i, Lf J i (!σ i)))).card : ℝ) := by
        exact_mod_cast h1
    _ ≤ ∑ J ∈ 𝒜, ((Finset.univ.filter (fun σ : Fin n → Bool =>
        ∑ i, Lf J i (σ i) ≤ α * n / 2 ∧ 3 * α * n / 4 < ∑ i, Lf J i (!σ i))).card : ℝ) := by
        exact_mod_cast h2
    _ ≤ ∑ J ∈ 𝒜, (2 ^ n * Real.exp (-(α * n / 40))) := Finset.sum_le_sum h3
    _ = (𝒜.card : ℝ) * (2 ^ n * Real.exp (-(α * n / 40))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∑ k ∈ Finset.range (d + 1), (2 * n).choose k : ℕ) * (2 ^ n * Real.exp (-(α * n / 40))) := by
        refine mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by push_cast; ring

end MoranYanPAC.Dev.VC
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.VC

open MeasureTheory Finset
open scoped ENNReal

variable {Z : Type*} [MeasurableSpace Z]

def swapT (n : ℕ) (σ : Fin n → Bool) (p : (Fin n → Z) × (Fin n → Z)) :
    (Fin n → Z) × (Fin n → Z) :=
  (fun i => if σ i then p.2 i else p.1 i, fun i => if σ i then p.1 i else p.2 i)

theorem swapT_mp (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (σ : Fin n → Bool) :
    MeasurePreserving (swapT (Z := Z) n σ) ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ))
      ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)) := by
  have hE := measurePreserving_arrowProdEquivProdArrow Z Z (Fin n) (fun _ => μ) (fun _ => μ)
  have hF : MeasurePreserving (fun (a : Fin n → Z × Z) i => (if σ i then Prod.swap else id) (a i))
      (Measure.pi fun _ : Fin n => μ.prod μ) (Measure.pi fun _ : Fin n => μ.prod μ) := by
    refine measurePreserving_pi _ _ (fun i => ?_)
    cases σ i
    · simpa using MeasurePreserving.id _
    · simpa using Measure.measurePreserving_swap (μ := μ) (ν := μ)
  have hcomp := hE.comp (hF.comp (hE.symm (MeasurableEquiv.arrowProdEquivProdArrow Z Z (Fin n))))
  convert hcomp using 1
  ext p i <;> simp [swapT, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow] <;>
    cases σ i <;> simp


open Classical in
theorem avg_bound (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ)
    (B : Set ((Fin n → Z) × (Fin n → Z))) (hB : MeasurableSet B) (q : ℝ) (hq0 : 0 ≤ q)
    (hq : ∀ p, ((Finset.univ.filter (fun σ : Fin n → Bool => swapT n σ p ∈ B)).card : ℝ) ≤ 2 ^ n * q) :
    ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)) B ≤ ENNReal.ofReal q := by
  set μ2 := ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ)) with hμ2
  have : IsProbabilityMeasure μ2 := by rw [hμ2]; infer_instance
  have h1 : ∀ σ : Fin n → Bool, μ2 (swapT n σ ⁻¹' B) = μ2 B := fun σ =>
    (swapT_mp μ n σ).measure_preimage hB.nullMeasurableSet
  have hmeas : ∀ σ : Fin n → Bool, MeasurableSet (swapT n σ ⁻¹' B) := fun σ =>
    (swapT_mp μ n σ).measurable hB
  have h2 : ∑ σ : Fin n → Bool, μ2 (swapT n σ ⁻¹' B) = (2 : ℝ≥0∞) ^ n * μ2 B := by
    simp_rw [h1]
    rw [Finset.sum_const, Finset.card_univ]
    simp [nsmul_eq_mul]
  have h3 : ∑ σ : Fin n → Bool, μ2 (swapT n σ ⁻¹' B) =
      ∫⁻ p, ∑ σ : Fin n → Bool, (swapT n σ ⁻¹' B).indicator (1 : ((Fin n → Z) × (Fin n → Z)) → ℝ≥0∞) p ∂μ2 := by
    rw [lintegral_finsetSum _ (fun σ _ => (measurable_one.indicator (hmeas σ)))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [lintegral_indicator_one (hmeas σ)]
  have h4 : ∀ p, ∑ σ : Fin n → Bool, (swapT n σ ⁻¹' B).indicator (1 : ((Fin n → Z) × (Fin n → Z)) → ℝ≥0∞) p ≤
      ENNReal.ofReal (2 ^ n * q) := by
    intro p
    have : ∑ σ : Fin n → Bool, (swapT n σ ⁻¹' B).indicator (1 : ((Fin n → Z) × (Fin n → Z)) → ℝ≥0∞) p =
        ((Finset.univ.filter (fun σ : Fin n → Bool => swapT n σ p ∈ B)).card : ℝ≥0∞) := by
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl fun σ _ => ?_
      by_cases h : swapT n σ p ∈ B <;> simp [Set.indicator, h]
    rw [this, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hq p)
  have h5 : (2 : ℝ≥0∞) ^ n * μ2 B ≤ (2 : ℝ≥0∞) ^ n * ENNReal.ofReal q := by
    rw [← h2, h3]
    calc ∫⁻ p, ∑ σ : Fin n → Bool, (swapT n σ ⁻¹' B).indicator (1 : ((Fin n → Z) × (Fin n → Z)) → ℝ≥0∞) p ∂μ2
        ≤ ∫⁻ _, ENNReal.ofReal (2 ^ n * q) ∂μ2 := lintegral_mono h4
      _ = ENNReal.ofReal (2 ^ n * q) := by simp
      _ = (2 : ℝ≥0∞) ^ n * ENNReal.ofReal q := by
          rw [ENNReal.ofReal_mul (by positivity)]
          simp [ENNReal.ofReal_pow]
  exact (ENNReal.mul_le_mul_iff_right (by positivity) (by simp)).1 h5

end MoranYanPAC.Dev.VC
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.VC

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {Z : Type*} [MeasurableSpace Z]

open Classical in
theorem ghost_chebyshev (μ : Measure Z) [IsProbabilityMeasure μ] (E : Set Z)
    (hE : MeasurableSet E) (n : ℕ) (α : ℝ) (hα : 0 < α) (hp : α < (μ E).toReal)
    (hn : 32 ≤ α * n) :
    (Measure.pi (fun _ : Fin n => μ))
      {s | (∑ i : Fin n, if s i ∈ E then (1 : ℝ) else 0) ≤ 3 * α * n / 4} ≤ ENNReal.ofReal (1 / 2) := by
  classical
  set p : ℝ := (μ E).toReal with hpdef
  set f : Z → ℝ := fun z => if z ∈ E then 1 else 0 with hf
  have hfmeas : Measurable f := Measurable.ite hE measurable_const measurable_const
  have hfb : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z; simp only [hf]; split_ifs <;> simp
  have hMemLp : MemLp f 2 μ := memLp_of_bounded (a := 0) (b := 1) (Filter.Eventually.of_forall hfb)
    hfmeas.aestronglyMeasurable 2
  have hEf : μ[f] = p := by
    have : f = E.indicator (fun _ => (1 : ℝ)) := by
      ext z; simp [hf, Set.indicator]
    rw [this, integral_indicator hE]
    simp [hpdef, Measure.real]
  have hvar : Var[f; μ] ≤ p * (1 - p) := by
    have := variance_le_sub_mul_sub (μ := μ) (a := 0) (b := 1) (X := f)
      (Filter.Eventually.of_forall hfb) hfmeas.aemeasurable
    rw [hEf] at this; linarith
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 := by
    rw [hpdef]; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  set π := Measure.pi (fun _ : Fin n => μ) with hπ
  have hS : Var[∑ i : Fin n, fun s : Fin n → Z => f (s i); π] ≤ n * (p * (1 - p)) := by
    rw [hπ, variance_sum_pi (fun _ => hMemLp)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left hvar (Nat.cast_nonneg _)
  have hmean : π[∑ i : Fin n, fun s : Fin n → Z => f (s i)] = n * p := by
    have hint : ∀ i : Fin n, Integrable (fun s : Fin n → Z => f (s i)) π := by
      intro i
      refine Integrable.of_bound (C := 1) (hfmeas.comp (measurable_pi_apply i)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun s => ?_)
      have := hfb (s i)
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
    have hsum : (∑ i : Fin n, fun s : Fin n → Z => f (s i)) = fun s => ∑ i, f (s i) := by
      ext s; simp
    rw [hsum, integral_finset_sum _ (fun i _ => hint i)]
    have : ∀ i : Fin n, ∫ s : Fin n → Z, f (s i) ∂π = p := by
      intro i
      rw [hπ, integral_comp_eval hfmeas.aestronglyMeasurable, hEf]
    simp [this]
  have hnpos : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hn; linarith
    · exact_mod_cast h
  have hpα : α < p := hp
  have hppos : 0 < p := by linarith
  have hc : 0 < (n : ℝ) * p / 4 := div_pos (mul_pos hnpos hppos) (by norm_num)
  have hmem : MemLp (∑ i : Fin n, fun s : Fin n → Z => f (s i)) 2 π := by
    refine memLp_finset_sum' _ (fun i _ => ?_)
    exact hMemLp.comp_measurePreserving (measurePreserving_eval _ i)
  have hcheb := meas_ge_le_variance_div_sq hmem hc
  rw [hmean] at hcheb
  refine le_trans (measure_mono ?_) (hcheb.trans (ENNReal.ofReal_le_ofReal ?_))
  · intro s hs
    simp only [Set.mem_setOf_eq] at hs ⊢
    have hS : (∑ i : Fin n, fun s : Fin n → Z => f (s i)) s = ∑ i : Fin n, if s i ∈ E then (1 : ℝ) else 0 := by
      simp [hf]
    rw [hS]
    have : (n : ℝ) * p ≤ n * p := le_rfl
    rw [le_abs]
    right
    nlinarith [mul_pos hnpos (sub_pos.2 hpα)]
  · have h1 : Var[∑ i : Fin n, fun s : Fin n → Z => f (s i); π] / ((n : ℝ) * p / 4) ^ 2 ≤
        (n * (p * (1 - p))) / ((n : ℝ) * p / 4) ^ 2 := by
      exact div_le_div_of_nonneg_right hS (pow_pos hc 2).le
    refine h1.trans ?_
    have hnp : 32 ≤ (n : ℝ) * p := by nlinarith
    rw [div_le_iff₀ (pow_pos hc 2)]
    have : (n : ℝ) * (p * (1 - p)) ≤ n * p := by nlinarith [mul_nonneg hnpos.le (mul_nonneg hp0 hp0)]
    nlinarith [mul_pos hnpos (by linarith : (0 : ℝ) < p)]

end MoranYanPAC.Dev.VC
end

section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace MoranYanPAC.Dev.VC

open MoranYanPAC.Main Finset

variable {X : Type*} [MeasurableSpace X]

open Classical in
theorem vc_main (G : Set (X → Bool)) (d : ℕ) (hvc : UnderstandingML.vcDim G ≤ d)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (hm : VCEventsMeasurable G P) (n : ℕ) (hn1 : 32 ≤ α * n)
    (hn2 : 2 * ((∑ k ∈ Finset.range (d + 1), (2 * n).choose k : ℕ) * Real.exp (-(α * n / 40))) ≤ β) :
    ENNReal.ofReal (1 - β) ≤ sampleLaw P n (vcSuccessEvent G P α n) := by
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hn1; linarith
    · exact h
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  set π := sampleLaw P n with hπ
  have hπdef : π = Measure.pi (fun _ : Fin n => P) := rfl
  haveI : IsProbabilityMeasure π := by rw [hπdef]; infer_instance
  set A : Set (Fin n → X × Bool) := {s | ∃ h ∈ G, empiricalRate (List.ofFn s) h ≤ α / 2 ∧ α < populationLoss P h} with hA
  set B : Set ((Fin n → X × Bool) × (Fin n → X × Bool)) :=
    {p | ∃ h ∈ G, empiricalRate (List.ofFn p.1) h ≤ α / 2 ∧ 3 * α / 4 < empiricalRate (List.ofFn p.2) h} with hB
  have hAm : MeasurableSet A := hm.2.1 n (α / 2) α
  have hBm : MeasurableSet B := hm.2.2 n n (α / 2) (3 * α / 4)
  have hcompl : vcSuccessEvent G P α n = Aᶜ := by
    ext s
    simp only [vcSuccessEvent, hA, Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_and, not_lt]
  set μ2 := π.prod π with hμ2
  -- step 2: μ2 B small
  have hB2 : μ2 B ≤ ENNReal.ofReal ((∑ k ∈ Finset.range (d + 1), (2 * n).choose k : ℕ) * Real.exp (-(α * n / 40))) := by
    rw [hμ2, hπdef]
    refine avg_bound P n B hBm _ (by positivity) (fun p => ?_)
    have := swap_count G d hvc n hnpos α hα p.1 p.2
    have hcardeq : (Finset.univ.filter (fun σ : Fin n → Bool => swapT n σ p ∈ B)).card =
        (Finset.univ.filter (fun σ : Fin n → Bool => ∃ h ∈ G,
          empiricalRate (List.ofFn (fun i => if σ i then p.2 i else p.1 i)) h ≤ α / 2 ∧
          3 * α / 4 < empiricalRate (List.ofFn (fun i => if σ i then p.1 i else p.2 i)) h)).card := by
      congr 1 <;> try exact Finset.filter_congr (fun σ _ => Iff.rfl)
    rw [hcardeq]
    refine this.trans (le_of_eq ?_)
    push_cast
    try ring
  -- step 1: ghost
  have hghost : ENNReal.ofReal (1 / 2) * π A ≤ μ2 B := by
    rw [hμ2, Measure.prod_apply hBm]
    calc ENNReal.ofReal (1 / 2) * π A = ∫⁻ s in A, ENNReal.ofReal (1 / 2) ∂π := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ s in A, π (Prod.mk s ⁻¹' B) ∂π := by
          refine setLIntegral_mono' hAm (fun s hs => ?_)
          obtain ⟨h, hh, e1, e2⟩ := hs
          set E : Set (X × Bool) := {z | h z.1 ≠ z.2} with hE
          have hEm : MeasurableSet E := hm.1 h hh
          have hch := ghost_chebyshev P E hEm n α hα (by simpa [populationLoss, hE] using e2) hn1
          rw [← hπdef] at hch
          have hsub : {s' : Fin n → X × Bool | 3 * α * n / 4 < ∑ i : Fin n, if s' i ∈ E then (1 : ℝ) else 0} ⊆
              Prod.mk s ⁻¹' B := by
            intro s' hs'
            refine ⟨h, hh, e1, ?_⟩
            rw [emp_eq, lt_div_iff₀ hnr]
            have : (∑ i : Fin n, if s' i ∈ E then (1 : ℝ) else 0) =
                ∑ i : Fin n, if h (s' i).1 ≠ (s' i).2 then (1 : ℝ) else 0 := by
              refine Finset.sum_congr rfl fun i _ => ?_
              simp [hE]
            rw [← this]
            have h3 : 3 * α * n / 4 = 3 * α / 4 * n := by ring
            have hs'' : 3 * α * n / 4 < ∑ i : Fin n, if s' i ∈ E then (1 : ℝ) else 0 := hs'
            linarith
          have hTm : MeasurableSet {s' : Fin n → X × Bool | (∑ i : Fin n, if s' i ∈ E then (1 : ℝ) else 0) ≤ 3 * α * n / 4} := by
            refine measurableSet_le (Finset.measurable_sum _ (fun i _ => ?_)) measurable_const
            exact Measurable.ite (hEm.preimage (measurable_pi_apply i)) measurable_const measurable_const
          have hcomp : {s' : Fin n → X × Bool | 3 * α * n / 4 < ∑ i : Fin n, if s' i ∈ E then (1 : ℝ) else 0} =
              {s' : Fin n → X × Bool | (∑ i : Fin n, if s' i ∈ E then (1 : ℝ) else 0) ≤ 3 * α * n / 4}ᶜ := by
            ext s'; simp
          have h1 : ENNReal.ofReal (1 / 2) ≤ π {s' : Fin n → X × Bool | 3 * α * n / 4 < ∑ i : Fin n, if s' i ∈ E then (1 : ℝ) else 0} := by
            rw [hcomp, prob_compl_eq_one_sub hTm]
            have : ENNReal.ofReal (1 / 2) = 1 - ENNReal.ofReal (1 / 2) := by
              rw [show ENNReal.ofReal (1 / 2) = 2⁻¹ by
                rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp]
              exact (ENNReal.one_sub_inv_two).symm
            rw [this]
            convert tsub_le_tsub_left hch 1 using 3
            all_goals first | rfl | (ext s'; simp only [Set.mem_setOf_eq]; congr!)
          exact h1.trans (measure_mono hsub)
      _ ≤ ∫⁻ s, π (Prod.mk s ⁻¹' B) ∂π := setLIntegral_le_lintegral _ _
  -- conclude
  have hπA : π A ≤ ENNReal.ofReal β := by
    have h2 : ENNReal.ofReal (1 / 2) * π A ≤ ENNReal.ofReal ((∑ k ∈ Finset.range (d + 1), (2 * n).choose k : ℕ) * Real.exp (-(α * n / 40))) :=
      hghost.trans hB2
    have h3 : π A ≤ 2 * ENNReal.ofReal ((∑ k ∈ Finset.range (d + 1), (2 * n).choose k : ℕ) * Real.exp (-(α * n / 40))) := by
      have : π A = 2 * (ENNReal.ofReal (1 / 2) * π A) := by
        rw [← mul_assoc, show (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 1 by
          rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp [ENNReal.mul_inv_cancel]]
        simp
      rw [this]
      gcongr
    refine h3.trans ?_
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hn2
  rw [hcompl, prob_compl_eq_one_sub hAm]
  calc ENNReal.ofReal (1 - β) = 1 - ENNReal.ofReal β := by
        rw [ENNReal.ofReal_sub _ hβ.le]; simp
    _ ≤ 1 - π A := tsub_le_tsub_left hπA 1

end MoranYanPAC.Dev.VC
end

section
set_option autoImplicit false

namespace MoranYanPAC.Dev.VC

theorem arith (d : ℕ) (hd : 1 ≤ d) (α β : ℝ) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (n : ℕ) (hn : 640 * ((d : ℝ) * Real.log (Real.exp 1 / α) + Real.log (1 / β)) / α ≤ n) :
    32 ≤ α * n ∧ (d : ℝ) ≤ 2 * n ∧ 2 * ((Real.exp 1 * (2 * n) / d) ^ d * Real.exp (-(α * n / 40))) ≤ β := by
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set u : ℝ := Real.log (Real.exp 1 / α) with hu
  have hu1 : 1 ≤ u := by
    rw [hu, Real.log_div (Real.exp_pos 1).ne' hα.ne', Real.log_exp]
    have := Real.log_neg hα hα1
    linarith
  have hlogβ : 0 < Real.log (1 / β) := Real.log_pos (by rw [lt_div_iff₀ hβ]; linarith)
  set L : ℝ := d * u + Real.log (1 / β) with hL
  have hL1 : (d : ℝ) ≤ L := by nlinarith
  have hαn : 640 * L ≤ α * n := by
    rw [div_le_iff₀ hα] at hn; linarith
  have hnr : (0 : ℝ) < n := by
    have : 0 < α * n := by linarith
    exact (pos_iff_pos_of_mul_pos this).1 hα
  refine ⟨by linarith, by nlinarith, ?_⟩
  set y : ℝ := α * n / d with hy
  have hdpos : (0 : ℝ) < d := by linarith
  have hypos : 0 < y := by positivity
  -- y ≤ 80 exp(y/80 - 1)
  have hy1 : y / 80 ≤ Real.exp (y / 80 - 1) := by
    have := Real.add_one_le_exp (y / 80 - 1); linarith
  have hy2 : Real.exp 1 * (2 * n) / d ≤ 160 / α * Real.exp (y / 80) := by
    have h1 : Real.exp 1 * (2 * n) / d = 2 * Real.exp 1 * y / α := by
      rw [hy]; field_simp
    rw [h1]
    have h2 : Real.exp (y / 80) = Real.exp 1 * Real.exp (y / 80 - 1) := by
      rw [← Real.exp_add]; ring_nf
    rw [h2, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hα]
    nlinarith [Real.exp_pos 1, Real.exp_pos (y / 80 - 1), mul_le_mul_of_nonneg_left hy1 (Real.exp_pos 1).le]
  have hpow : (Real.exp 1 * (2 * n) / d) ^ d ≤ (160 / α) ^ d * Real.exp (α * n / 80) := by
    calc (Real.exp 1 * (2 * n) / d) ^ d ≤ (160 / α * Real.exp (y / 80)) ^ d :=
          pow_le_pow_left₀ (by positivity) hy2 d
      _ = (160 / α) ^ d * Real.exp (α * n / 80) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 2
          rw [hy]; field_simp
  have h3 : 2 * (160 / α) ^ d ≤ β * Real.exp (α * n / 80) := by
    have hexp : Real.exp (8 * L) ≤ Real.exp (α * n / 80) := Real.exp_le_exp.2 (by linarith)
    have hE : Real.exp (8 * L) = (Real.exp 1 / α) ^ (8 * d) * (1 / β) ^ 8 := by
      rw [hL, mul_add, Real.exp_add]
      congr 1
      · rw [show 8 * ((d : ℝ) * u) = ((8 * d : ℕ) : ℝ) * u by push_cast; ring, Real.exp_nat_mul, hu,
          Real.exp_log (by positivity)]
      · rw [show (8 : ℝ) * Real.log (1 / β) = ((8 : ℕ) : ℝ) * Real.log (1 / β) by norm_num, Real.exp_nat_mul,
          Real.exp_log (by positivity)]
    have hb8 : 1 ≤ (1 / β) ^ 7 := one_le_pow₀ (by rw [le_div_iff₀ hβ]; linarith)
    have hα8 : (1 / α) ^ d ≤ (1 / α) ^ (8 * d) := pow_le_pow_right₀ (by rw [le_div_iff₀ hα]; linarith) (by omega)
    have he8 : (320 : ℝ) ≤ Real.exp 1 ^ 8 := by
      have := Real.exp_one_gt_d9
      have h27 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith
      calc (320 : ℝ) ≤ 2.7 ^ 8 := by norm_num
        _ ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) h27 8
    have h160 : 2 * (160 : ℝ) ^ d ≤ (Real.exp 1 ^ 8) ^ d := by
      have h1 : (2 : ℝ) * 160 ^ d ≤ 160 ^ d * 2 := by ring_nf; exact le_refl _
      have : (160 : ℝ) ^ d * 2 ≤ 160 ^ d * (Real.exp 1 ^ 8 / 160) ^ d := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (2 : ℝ) ≤ Real.exp 1 ^ 8 / 160 := by rw [le_div_iff₀ (by norm_num)]; linarith
          _ = (Real.exp 1 ^ 8 / 160) ^ 1 := by ring
          _ ≤ (Real.exp 1 ^ 8 / 160) ^ d :=
            pow_le_pow_right₀ (by rw [le_div_iff₀ (by norm_num)]; linarith) hd
      calc 2 * (160 : ℝ) ^ d ≤ 160 ^ d * 2 := h1
        _ ≤ _ := this
        _ = (Real.exp 1 ^ 8) ^ d := by rw [← mul_pow]; congr 1; ring
    calc 2 * (160 / α) ^ d = 2 * 160 ^ d * (1 / α) ^ d := by rw [div_eq_mul_one_div, mul_pow]; ring
      _ ≤ (Real.exp 1 ^ 8) ^ d * (1 / α) ^ (8 * d) := by
          exact mul_le_mul h160 hα8 (by positivity) (by positivity)
      _ = (Real.exp 1 / α) ^ (8 * d) := by
          rw [← pow_mul, div_eq_mul_one_div (Real.exp 1) α, mul_pow]
      _ ≤ (Real.exp 1 / α) ^ (8 * d) * (1 / β) ^ 7 := by
          have : 0 ≤ (Real.exp 1 / α) ^ (8 * d) := by positivity
          nlinarith
      _ = β * ((Real.exp 1 / α) ^ (8 * d) * (1 / β) ^ 8) := by
          field_simp
      _ = β * Real.exp (8 * L) := by rw [hE]
      _ ≤ β * Real.exp (α * n / 80) := mul_le_mul_of_nonneg_left hexp hβ.le
  calc 2 * ((Real.exp 1 * (2 * n) / d) ^ d * Real.exp (-(α * n / 40)))
      ≤ 2 * ((160 / α) ^ d * Real.exp (α * n / 80) * Real.exp (-(α * n / 40))) := by
        gcongr
    _ = 2 * (160 / α) ^ d * Real.exp (-(α * n / 80)) := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ β * Real.exp (α * n / 80) * Real.exp (-(α * n / 80)) := by
        gcongr
    _ = β := by rw [mul_assoc, ← Real.exp_add]; simp

end MoranYanPAC.Dev.VC
end

section
set_option autoImplicit false

open MeasureTheory

namespace MoranYanPAC.Main

theorem chk_vc_generalization :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Type) [MeasurableSpace X]
      (G : Set (X → Bool)) (d : ℕ), 1 ≤ d → UnderstandingML.vcDim G ≤ d →
      ∀ (α β : ℝ), 0 < α → α < 1 → 0 < β → β < 1 →
      ∀ (P : Measure (X × Bool)), IsProbabilityMeasure P → VCEventsMeasurable G P →
      ∀ n : ℕ,
        C * ((d : ℝ) * Real.log (Real.exp 1 / α) + Real.log (1 / β)) / α ≤ n →
        ENNReal.ofReal (1 - β) ≤ sampleLaw P n (vcSuccessEvent G P α n) := by
  refine ⟨640, by norm_num, ?_⟩
  intro X _ G d hd1 hvc α β hα hα1 hβ hβ1 P hP hm n hn
  haveI := hP
  obtain ⟨h1, h2, h3⟩ := Dev.VC.arith d hd1 α β hα hα1 hβ hβ1 n hn
  refine Dev.VC.vc_main G d hvc α β hα hβ P hm n h1 ?_
  have hS : ((∑ k ∈ Finset.range (d + 1), (2 * n).choose k : ℕ) : ℝ) ≤
      (Real.exp 1 * ((2 * n : ℕ) : ℝ) / d) ^ d := by
    push_cast
    have := Dev.Sauer.sum_choose_le (2 * n) d hd1 (by exact_mod_cast h2)
    push_cast at this
    exact this
  refine le_trans ?_ h3
  have : 0 ≤ Real.exp (-(α * n / 40)) := (Real.exp_pos _).le
  push_cast at hS ⊢
  nlinarith
end MoranYanPAC.Main
end

theorem solution : type_of% @MoranYanPAC.Main.chk_vc_generalization := @MoranYanPAC.Main.chk_vc_generalization
