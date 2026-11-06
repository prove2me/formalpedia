-- Prove2me | solution 1 for MPECRelax.ScholtesConv.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T19:45:54.625247+00:00
-- url     : https://prove2.me/submissions/ab152b77-4b95-43f8-881e-c51f0379cd83

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC
import Definitions.Def_MPECRelax_ScholtesConv_Scholtes
import Theorems.Thm_MPECRelax_ScholtesConv_mpec_mfcq_posLinIndep

open Filter Topology

namespace ScholtesHelp
open MPECRelax.ScholtesConv

lemma grad_neg {n : ℕ} (f : E n → ℝ) (x : E n) :
    gradient (fun y => -f y) x = -gradient f x := by
  simp only [gradient]
  rw [fderiv_fun_neg]; simp

lemma grad_mul_sub {n : ℕ} (f g : E n → ℝ) (t : ℝ) (x : E n)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y * g y - t) x = g x • gradient f x + f x • gradient g x := by
  simp only [gradient]
  rw [fderiv_sub_const, fderiv_fun_mul hf hg]
  simp [add_comm]

lemma grad_cont {n : ℕ} (f : E n → ℝ) (hf : ContDiff ℝ 1 f) : Continuous (gradient f) := by
  have : gradient f = fun x => (InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ f x) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (E n)).symm.continuous.comp
    (hf.continuous_fderiv (by norm_num))

lemma closed_ge {X : Type*} [TopologicalSpace X] {φ : X → ℝ} (hφ : Continuous φ)
    {z : ℕ → X} {z0 : X} (hz : Tendsto z atTop (𝓝 z0)) (h : ∀ k, 0 ≤ φ (z k)) : 0 ≤ φ z0 :=
  ge_of_tendsto' ((hφ.tendsto z0).comp hz) h

lemma closed_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [Zero Y]
    {φ : X → Y} (hφ : Continuous φ)
    {z : ℕ → X} {z0 : X} (hz : Tendsto z atTop (𝓝 z0)) (h : ∀ k, φ (z k) = 0) : φ z0 = 0 := by
  have H := (hφ.tendsto z0).comp hz
  have : φ ∘ z = fun _ => 0 := funext h
  rw [this] at H
  exact tendsto_nhds_unique H tendsto_const_nhds

abbrev V (m p l : ℕ) := (Fin m → ℝ) × (Fin p → ℝ) × (Fin l → ℝ) × (Fin l → ℝ) × (Fin l → ℝ) ×
  (Fin l → ℝ)

variable {n m p l : ℕ}

/-- The rewritten KKT combination. -/
noncomputable def F (P : MPEC n m p l) (x : E n) (v : V m p l) : E n :=
  ∑ i, v.1 i • gradient (P.g i) x + ∑ i, v.2.1 i • gradient (P.h i) x
    - ∑ i, v.2.2.1 i • gradient (P.G i) x - ∑ i, v.2.2.2.1 i • gradient (P.H i) x
    + ∑ i, (v.2.2.2.2.1 i * P.H i x) • gradient (P.G i) x
    + ∑ i, (v.2.2.2.2.2 i * P.G i x) • gradient (P.H i) x

def Facts (P : MPEC n m p l) (xs : E n) (x : E n) (v : V m p l) : Prop :=
  (∀ i, 0 ≤ v.1 i) ∧ (∀ i, v.1 i * P.g i x = 0) ∧
  (∀ i ∈ P.Ip0 xs, v.2.2.1 i * P.G i x = 0) ∧ (∀ i ∈ P.I0p xs, v.2.2.2.1 i * P.H i x = 0) ∧
  (∀ i, 0 ≤ v.2.2.2.2.1 i) ∧ (∀ i, 0 ≤ v.2.2.2.2.2 i) ∧
  (∀ i ∉ P.Ip0 xs, v.2.2.2.2.1 i = 0) ∧ (∀ i ∉ P.I0p xs, v.2.2.2.2.2 i = 0) ∧
  (∀ i ∈ P.Ip0 xs, v.2.2.2.2.1 i * P.G i x ≤ |v.2.2.2.1 i|) ∧
  (∀ i ∈ P.I0p xs, v.2.2.2.2.2 i * P.H i x ≤ |v.2.2.1 i|) ∧
  (∀ i ∈ P.I00 xs, 0 ≤ v.2.2.1 i * v.2.2.2.1 i)

lemma F_smul (P : MPEC n m p l) (x : E n) (v : V m p l) (c : ℝ) :
    F P x (c • v) = c • F P x v := by
  simp only [F, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, smul_add, smul_sub,
    Finset.smul_sum, smul_smul, mul_assoc]

lemma F_cont (P : MPEC n m p l) (hP : P.IsC1) : Continuous (fun q : E n × V m p l => F P q.1 q.2) := by
  obtain ⟨hf1, hg1, hh1, hG1, hH1⟩ := hP
  have a1 := fun i => grad_cont _ (hg1 i)
  have a2 := fun i => grad_cont _ (hh1 i)
  have a3 := fun i => grad_cont _ (hG1 i)
  have a4 := fun i => grad_cont _ (hH1 i)
  have a5 := fun i => (hG1 i).continuous
  have a6 := fun i => (hH1 i).continuous
  unfold F
  fun_prop

lemma Facts_smul (P : MPEC n m p l) (xs x : E n) (v : V m p l) (c : ℝ) (hc : 0 ≤ c)
    (h : Facts P xs x v) : Facts P xs x (c • v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  simp only [Facts, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  refine ⟨fun i => mul_nonneg hc (h1 i), fun i => by rw [mul_assoc, h2 i, mul_zero],
    fun i hi => by rw [mul_assoc, h3 i hi, mul_zero], fun i hi => by rw [mul_assoc, h4 i hi, mul_zero],
    fun i => mul_nonneg hc (h5 i), fun i => mul_nonneg hc (h6 i),
    fun i hi => by rw [h7 i hi, mul_zero], fun i hi => by rw [h8 i hi, mul_zero],
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [abs_mul, abs_of_nonneg hc, mul_assoc]; exact mul_le_mul_of_nonneg_left (h9 i hi) hc
  · rw [abs_mul, abs_of_nonneg hc, mul_assoc]; exact mul_le_mul_of_nonneg_left (h10 i hi) hc
  · have := h11 i hi
    have : c * v.2.2.1 i * (c * v.2.2.2.1 i) = (c * c) * (v.2.2.1 i * v.2.2.2.1 i) := by ring
    rw [this]; exact mul_nonneg (mul_self_nonneg c) (h11 i hi)

lemma Facts_limit (P : MPEC n m p l) (hP : P.IsC1) (xs : E n) (z : ℕ → E n × V m p l)
    (x0 : E n) (w : V m p l) (hz : Tendsto z atTop (𝓝 (x0, w)))
    (h : ∀ k, Facts P xs (z k).1 (z k).2) : Facts P xs x0 w := by
  obtain ⟨hf1, hg1, hh1, hG1, hH1⟩ := hP
  have cg := fun i => (hg1 i).continuous
  have cG := fun i => (hG1 i).continuous
  have cH := fun i => (hH1 i).continuous
  refine ⟨fun i => ?_, fun i => ?_, fun i hi => ?_, fun i hi => ?_, fun i => ?_, fun i => ?_,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · exact closed_ge (φ := fun q : E n × V m p l => q.2.1 i) (by fun_prop) hz
      (fun k => (h k).1 i)
  · exact closed_eq (φ := fun q : E n × V m p l => q.2.1 i * P.g i q.1)
      (by have := cg i; fun_prop) hz (fun k => (h k).2.1 i)
  · exact closed_eq (φ := fun q : E n × V m p l => q.2.2.2.1 i * P.G i q.1)
      (by have := cG i; fun_prop) hz (fun k => (h k).2.2.1 i hi)
  · exact closed_eq (φ := fun q : E n × V m p l => q.2.2.2.2.1 i * P.H i q.1)
      (by have := cH i; fun_prop) hz (fun k => (h k).2.2.2.1 i hi)
  · exact closed_ge (φ := fun q : E n × V m p l => q.2.2.2.2.2.1 i) (by fun_prop) hz
      (fun k => (h k).2.2.2.2.1 i)
  · exact closed_ge (φ := fun q : E n × V m p l => q.2.2.2.2.2.2 i) (by fun_prop) hz
      (fun k => (h k).2.2.2.2.2.1 i)
  · exact closed_eq (φ := fun q : E n × V m p l => q.2.2.2.2.2.1 i) (by fun_prop) hz
      (fun k => (h k).2.2.2.2.2.2.1 i hi)
  · exact closed_eq (φ := fun q : E n × V m p l => q.2.2.2.2.2.2 i) (by fun_prop) hz
      (fun k => (h k).2.2.2.2.2.2.2.1 i hi)
  · have := closed_ge (φ := fun q : E n × V m p l =>
        |q.2.2.2.2.1 i| - q.2.2.2.2.2.1 i * P.G i q.1)
      (by have := cG i; fun_prop) hz (fun k => sub_nonneg.mpr ((h k).2.2.2.2.2.2.2.2.1 i hi))
    simpa using this
  · have := closed_ge (φ := fun q : E n × V m p l =>
        |q.2.2.2.1 i| - q.2.2.2.2.2.2 i * P.H i q.1)
      (by have := cH i; fun_prop) hz (fun k => sub_nonneg.mpr ((h k).2.2.2.2.2.2.2.2.2.1 i hi))
    simpa using this
  · exact closed_ge (φ := fun q : E n × V m p l => q.2.2.2.1 i * q.2.2.2.2.1 i)
      (by fun_prop) hz (fun k => (h k).2.2.2.2.2.2.2.2.2.2 i hi)

lemma F_at (P : MPEC n m p l) (xs : E n) (v : V m p l) (h : Facts P xs xs v) :
    F P xs v = ∑ i, v.1 i • gradient (P.g i) xs + ∑ i, v.2.1 i • gradient (P.h i) xs
    - ∑ i, v.2.2.1 i • gradient (P.G i) xs - ∑ i, v.2.2.2.1 i • gradient (P.H i) xs := by
  obtain ⟨-, -, -, -, -, -, h7, h8, -⟩ := h
  have e1 : ∑ i, (v.2.2.2.2.1 i * P.H i xs) • gradient (P.G i) xs = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ P.Ip0 xs
    · rw [hi.2, mul_zero, zero_smul]
    · rw [h7 i hi, zero_mul, zero_smul]
  have e2 : ∑ i, (v.2.2.2.2.2 i * P.G i xs) • gradient (P.H i) xs = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ P.I0p xs
    · rw [hi.1, mul_zero, zero_smul]
    · rw [h8 i hi, zero_mul, zero_smul]
  rw [F, e1, e2, add_zero, add_zero]

lemma kkt_step (P : MPEC n m p l) (hP : P.IsC1) (t : ℝ) (ht : 0 < t) (xs x : E n)
    (hx : (P.RS t).IsKKTPoint x) : ∃ v, Facts P xs x v ∧ gradient P.f x + F P x v = 0 := by
  classical
  obtain ⟨hf1, hg1, hh1, hG1, hH1⟩ := hP
  obtain ⟨⟨hfg, hfh⟩, lam, mu, hnn, hcs, heq⟩ := hx
  set la : Fin m → ℝ := fun i => lam (Sum.inl i)
  set γ : Fin l → ℝ := fun i => lam (Sum.inr (Sum.inl i))
  set ν : Fin l → ℝ := fun i => lam (Sum.inr (Sum.inr (Sum.inl i)))
  set δ : Fin l → ℝ := fun i => lam (Sum.inr (Sum.inr (Sum.inr i)))
  set a : Fin l → ℝ := fun i => if i ∈ P.Ip0 xs then 1 else 0
  set b : Fin l → ℝ := fun i => if i ∈ P.I0p xs then 1 else 0
  -- basic facts
  have hgk : ∀ i, P.g i x ≤ 0 := fun i => by simpa [MPEC.RS] using hfg (Sum.inl i)
  have hGk : ∀ i, 0 ≤ P.G i x := fun i => by simpa [MPEC.RS] using hfg (Sum.inr (Sum.inl i))
  have hHk : ∀ i, 0 ≤ P.H i x := fun i => by
    simpa [MPEC.RS] using hfg (Sum.inr (Sum.inr (Sum.inl i)))
  have hla0 : ∀ i, 0 ≤ la i := fun i => hnn _
  have hγ0 : ∀ i, 0 ≤ γ i := fun i => hnn _
  have hν0 : ∀ i, 0 ≤ ν i := fun i => hnn _
  have hδ0 : ∀ i, 0 ≤ δ i := fun i => hnn _
  have hlac : ∀ i, la i * P.g i x = 0 := fun i => by simpa [MPEC.RS] using hcs (Sum.inl i)
  have hγc : ∀ i, γ i * P.G i x = 0 := fun i => by
    have := hcs (Sum.inr (Sum.inl i)); simp [MPEC.RS] at this; simp [γ, this]
  have hνc : ∀ i, ν i * P.H i x = 0 := fun i => by
    have := hcs (Sum.inr (Sum.inr (Sum.inl i))); simp [MPEC.RS] at this; simp [ν, this]
  have hδc : ∀ i, δ i * (P.G i x * P.H i x - t) = 0 := fun i => by
    simpa [MPEC.RS] using hcs (Sum.inr (Sum.inr (Sum.inr i)))
  have hγδ : ∀ i, γ i * δ i = 0 := fun i => by
    rcases mul_eq_zero.mp (hγc i) with h | h
    · rw [h, zero_mul]
    · have := hδc i; rw [h, zero_mul, zero_sub, mul_neg, neg_eq_zero] at this
      rcases mul_eq_zero.mp this with h' | h'
      · rw [h', mul_zero]
      · exact absurd h' ht.ne'
  have hνδ : ∀ i, ν i * δ i = 0 := fun i => by
    rcases mul_eq_zero.mp (hνc i) with h | h
    · rw [h, zero_mul]
    · have := hδc i; rw [h, mul_zero, zero_sub, mul_neg, neg_eq_zero] at this
      rcases mul_eq_zero.mp this with h' | h'
      · rw [h', mul_zero]
      · exact absurd h' ht.ne'
  have disj : ∀ i ∈ P.Ip0 xs, i ∉ P.I0p xs := fun i h1 h2 => by
    have := h1.1; rw [h2.1] at this; exact lt_irrefl _ this
  refine ⟨(la, mu, fun i => γ i - (1 - a i) * δ i * P.H i x,
    fun i => ν i - (1 - b i) * δ i * P.G i x, fun i => a i * δ i, fun i => b i * δ i), ?_, ?_⟩
  · refine ⟨hla0, hlac, fun i hi => ?_, fun i hi => ?_, fun i => ?_, fun i => ?_,
      fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · simp only [a, if_pos hi]; rw [sub_self, zero_mul, zero_mul, sub_zero, hγc]
    · simp only [b, if_pos hi]; rw [sub_self, zero_mul, zero_mul, sub_zero, hνc]
    · simp only [a]; split_ifs <;> simp [hδ0 i]
    · simp only [b]; split_ifs <;> simp [hδ0 i]
    · simp only [a, if_neg hi, zero_mul]
    · simp only [b, if_neg hi, zero_mul]
    · simp only [a, b, if_pos hi, if_neg (disj i hi), one_mul, sub_zero]
      rcases mul_eq_zero.mp (hνδ i) with h | h
      · rw [h, zero_sub, abs_neg, abs_of_nonneg (mul_nonneg (hδ0 i) (hGk i))]
      · rw [h]; simp
    · have hi' : i ∉ P.Ip0 xs := fun h => disj i h hi
      simp only [a, b, if_pos hi, if_neg hi', one_mul, sub_zero]
      rcases mul_eq_zero.mp (hγδ i) with h | h
      · rw [h, zero_sub, abs_neg, abs_of_nonneg (mul_nonneg (hδ0 i) (hHk i))]
      · rw [h]; simp
    · have h1 : i ∉ P.Ip0 xs := fun h => by have := h.1; rw [hi.1] at this; exact lt_irrefl _ this
      have h2 : i ∉ P.I0p xs := fun h => by have := h.2; rw [hi.2] at this; exact lt_irrefl _ this
      simp only [a, b, if_neg h1, if_neg h2, sub_zero, one_mul]
      have : (γ i - δ i * P.H i x) * (ν i - δ i * P.G i x) =
          γ i * ν i + δ i * δ i * (P.H i x * P.G i x) - (γ i * δ i) * P.G i x
            - (ν i * δ i) * P.H i x := by ring
      rw [this, hγδ, hνδ]
      have := mul_nonneg (hγ0 i) (hν0 i)
      have := mul_nonneg (mul_self_nonneg (δ i)) (mul_nonneg (hHk i) (hGk i))
      linarith
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at heq
    have hgm : ∀ i, gradient (fun y => P.G i y * P.H i y - t) x =
        P.H i x • gradient (P.G i) x + P.G i x • gradient (P.H i) x := fun i =>
      grad_mul_sub _ _ _ _ ((hG1 i).differentiable (by norm_num) x)
        ((hH1 i).differentiable (by norm_num) x)
    simp only [MPEC.RS, Sum.elim_inl, Sum.elim_inr, grad_neg, hgm] at heq
    rw [← heq]
    have key : ∀ i, γ i • -gradient (P.G i) x + (ν i • -gradient (P.H i) x +
        δ i • (P.H i x • gradient (P.G i) x + P.G i x • gradient (P.H i) x)) =
        -((γ i - (1 - a i) * δ i * P.H i x) • gradient (P.G i) x)
        - (ν i - (1 - b i) * δ i * P.G i x) • gradient (P.H i) x
        + (a i * δ i * P.H i x) • gradient (P.G i) x
        + (b i * δ i * P.G i x) • gradient (P.H i) x := fun i => by module
    have hs := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => key i)
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hs
    simp only [F, la, γ, ν, δ] at hs ⊢
    linear_combination (norm := module) -hs

end ScholtesHelp

open MPECRelax.ScholtesConv ScholtesHelp in
theorem solution {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1)
    (t : ℕ → ℝ) (ht_pos : ∀ k, 0 < t k) (_ht_anti : Antitone t)
    (ht_lim : Tendsto t atTop (𝓝 0))
    (x : ℕ → E n) (hx : ∀ k, (P.RS (t k)).IsKKTPoint (x k))
    (xs : E n) (hxs : Tendsto x atTop (𝓝 xs)) (hCQ : P.MPEC_MFCQ xs) :
    P.IsCStationary xs := by
  classical
  have hP' := hP
  obtain ⟨hf1, hg1, hh1, hG1, hH1⟩ := hP'
  have cg := fun i => (hg1 i).continuous
  have ch := fun i => (hh1 i).continuous
  have cG := fun i => (hG1 i).continuous
  have cH := fun i => (hH1 i).continuous
  -- Step 1: feasibility of the limit point
  have hfe : ∀ k, (P.RS (t k)).Feasible (x k) := fun k => (hx k).1
  have hgk : ∀ k i, P.g i (x k) ≤ 0 := fun k i => by
    simpa [MPEC.RS] using (hfe k).1 (Sum.inl i)
  have hhk : ∀ k i, P.h i (x k) = 0 := fun k i => (hfe k).2 i
  have hGk : ∀ k i, 0 ≤ P.G i (x k) := fun k i => by
    simpa [MPEC.RS] using (hfe k).1 (Sum.inr (Sum.inl i))
  have hHk : ∀ k i, 0 ≤ P.H i (x k) := fun k i => by
    simpa [MPEC.RS] using (hfe k).1 (Sum.inr (Sum.inr (Sum.inl i)))
  have hGHk : ∀ k i, P.G i (x k) * P.H i (x k) ≤ t k := fun k i => by
    have := (hfe k).1 (Sum.inr (Sum.inr (Sum.inr i)))
    simp [MPEC.RS] at this; linarith
  have hfeas : P.Feasible xs := by
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
    · exact le_of_tendsto' (((cg i).tendsto xs).comp hxs) (fun k => hgk k i)
    · exact closed_eq (ch i) hxs (fun k => hhk k i)
    · have h1 : 0 ≤ P.G i xs := ge_of_tendsto' (((cG i).tendsto xs).comp hxs) (fun k => hGk k i)
      have h2 : 0 ≤ P.H i xs := ge_of_tendsto' (((cH i).tendsto xs).comp hxs) (fun k => hHk k i)
      have h3 : P.G i xs * P.H i xs ≤ 0 :=
        le_of_tendsto_of_tendsto' ((((cG i).mul (cH i)).tendsto xs).comp hxs) ht_lim
          (fun k => hGHk k i)
      exact ⟨h1, h2, le_antisymm h3 (mul_nonneg h1 h2)⟩
  have hIp0 : ∀ i, P.G i xs ≠ 0 → i ∈ P.Ip0 xs := fun i hi =>
    ⟨lt_of_le_of_ne (hfeas.2.2 i).1 (Ne.symm hi),
      (mul_eq_zero.mp (hfeas.2.2 i).2.2).resolve_left hi⟩
  have hI0p : ∀ i, P.H i xs ≠ 0 → i ∈ P.I0p xs := fun i hi =>
    ⟨(mul_eq_zero.mp (hfeas.2.2 i).2.2).resolve_right hi,
      lt_of_le_of_ne (hfeas.2.2 i).2.1 (Ne.symm hi)⟩
  -- Step 2: MPEC-MFCQ forces any multiplier vector of the limiting system to vanish
  have zero_of : ∀ v' : V m p l, Facts P xs xs v' → F P xs v' = 0 → v' = 0 := by
    intro v' hF hE
    rw [F_at P xs v' hF] at hE
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hF
    obtain ⟨hL, hM, hGt, hNt⟩ := mpec_mfcq_posLinIndep P xs hfeas hCQ v'.1 v'.2.1 v'.2.2.1
      v'.2.2.2.1 h1
      (fun i hi => (mul_eq_zero.mp (h2 i)).resolve_right hi)
      (fun i hi => by
        by_cases hG : P.G i xs = 0
        · exfalso; apply hi
          rcases (hfeas.2.2 i).2.1.eq_or_lt with h | h
          · exact Or.inl ⟨hG, h.symm⟩
          · exact Or.inr ⟨hG, h⟩
        · exact (mul_eq_zero.mp (h3 i (hIp0 i hG))).resolve_right hG)
      (fun i hi => by
        by_cases hH : P.H i xs = 0
        · exfalso; apply hi
          rcases (hfeas.2.2 i).1.eq_or_lt with h | h
          · exact Or.inl ⟨h.symm, hH⟩
          · exact Or.inr ⟨h, hH⟩
        · exact (mul_eq_zero.mp (h4 i (hI0p i hH))).resolve_right hH)
      hE
    have hD1 : v'.2.2.2.2.1 = 0 := funext fun i => by
      by_cases hi : i ∈ P.Ip0 xs
      · have := h9 i hi
        rw [congrFun hNt i, Pi.zero_apply, abs_zero] at this
        refine le_antisymm ?_ (h5 i)
        by_contra hc; replace hc := not_le.mp hc
        have := mul_pos hc hi.1; linarith
      · exact h7 i hi
    have hD2 : v'.2.2.2.2.2 = 0 := funext fun i => by
      by_cases hi : i ∈ P.I0p xs
      · have := h10 i hi
        rw [congrFun hGt i, Pi.zero_apply, abs_zero] at this
        refine le_antisymm ?_ (h6 i)
        by_contra hc; replace hc := not_le.mp hc
        have := mul_pos hc hi.2; linarith
      · exact h8 i hi
    exact Prod.ext hL (Prod.ext hM (Prod.ext hGt (Prod.ext hNt (Prod.ext hD1 hD2))))
  -- Step 3: multipliers of the relaxed problems, normalized
  choose v hvF hvE using fun k => kkt_step P hP (t k) (ht_pos k) xs (x k) (hx k)
  set c : ℕ → ℝ := fun k => (1 + ‖v k‖)⁻¹ with hc_def
  set u : ℕ → V m p l := fun k => c k • v k with hu_def
  have hc_pos : ∀ k, 0 < c k := fun k => inv_pos.mpr (by positivity)
  have hu_norm : ∀ k, ‖u k‖ = 1 - c k := fun k => by
    have hpos : (0 : ℝ) < 1 + ‖v k‖ := by positivity
    simp only [u, c, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
    field_simp; ring
  have hbd : ∀ k, (u k, c k) ∈ Metric.closedBall (0 : V m p l × ℝ) 1 := fun k => by
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, hu_norm, Real.norm_eq_abs,
      abs_of_pos (hc_pos k)]
    have := hc_pos k
    exact max_le (by linarith) (by
      simp only [c]; exact inv_le_one_of_one_le₀ (by linarith [norm_nonneg (v k)]))
  obtain ⟨⟨w, c0⟩, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbd
  have hw : Tendsto (fun k => u (φ k)) atTop (𝓝 w) := (continuous_fst.tendsto _).comp hlim
  have hc : Tendsto (fun k => c (φ k)) atTop (𝓝 c0) := (continuous_snd.tendsto _).comp hlim
  have hxφ : Tendsto (fun k => x (φ k)) atTop (𝓝 xs) := hxs.comp hφ.tendsto_atTop
  have hz : Tendsto (fun k => (x (φ k), u (φ k))) atTop (𝓝 (xs, w)) := hxφ.prodMk_nhds hw
  have hFw : Facts P xs xs w :=
    Facts_limit P hP xs _ xs w hz (fun k => Facts_smul P xs _ _ _ (hc_pos _).le (hvF (φ k)))
  have hEw : c0 • gradient P.f xs + F P xs w = 0 := by
    have hcont : Continuous (fun q : (E n × V m p l) × ℝ =>
        q.2 • gradient P.f q.1.1 + F P q.1.1 q.1.2) :=
      (continuous_snd.smul ((grad_cont _ hf1).comp (continuous_fst.comp continuous_fst))).add
        ((F_cont P hP).comp continuous_fst)
    exact closed_eq hcont (hz.prodMk_nhds hc) (fun k => by
      simp only [u]; rw [F_smul, ← smul_add, hvE, smul_zero])
  have hwnorm : ‖w‖ = 1 - c0 := by
    have h1 : Tendsto (fun k => ‖u (φ k)‖) atTop (𝓝 ‖w‖) := (continuous_norm.tendsto w).comp hw
    have h2 : Tendsto (fun k => ‖u (φ k)‖) atTop (𝓝 (1 - c0)) := by
      simp only [hu_norm]; exact tendsto_const_nhds.sub hc
    exact tendsto_nhds_unique h1 h2
  have hc0 : 0 ≤ c0 := ge_of_tendsto' hc (fun k => (hc_pos _).le)
  rcases hc0.eq_or_lt with h0 | hpos
  · -- unbounded multipliers: contradiction with MPEC-MFCQ
    exfalso
    rw [← h0, zero_smul, zero_add] at hEw
    have := zero_of w hFw hEw
    rw [this, norm_zero, ← h0] at hwnorm
    norm_num at hwnorm
  · -- bounded multipliers: the limit gives C-stationarity multipliers
    set vs : V m p l := c0⁻¹ • w
    have hFs : Facts P xs xs vs := Facts_smul P xs xs w _ (inv_nonneg.mpr hc0) hFw
    have hEs : gradient P.f xs + F P xs vs = 0 := by
      have := congrArg (fun y => c0⁻¹ • y) hEw
      simp only [smul_add, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul, smul_zero] at this
      rw [F_smul]; exact this
    rw [F_at P xs vs hFs] at hEs
    obtain ⟨h1, h2, h3, h4, -, -, -, -, -, -, h11⟩ := hFs
    refine ⟨hfeas, vs.1, vs.2.1, vs.2.2.1, vs.2.2.2.1, ⟨?_, h1, h2, ?_, ?_⟩, h11⟩
    · rw [← hEs]; abel
    · intro i hi
      exact (mul_eq_zero.mp (h3 i hi)).resolve_right hi.1.ne'
    · intro i hi
      exact (mul_eq_zero.mp (h4 i hi)).resolve_right hi.2.ne'
