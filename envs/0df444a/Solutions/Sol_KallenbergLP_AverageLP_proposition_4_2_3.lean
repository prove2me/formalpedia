-- Prove2me | solution 1 for KallenbergLP.AverageLP.proposition_4_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:37:06.689252+00:00
-- url     : https://prove2.me/submissions/96f2aed5-ab55-4647-a47b-719064675d0f

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model

set_option autoImplicit false

open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter
open scoped Topology

namespace KallenbergLP.AverageLP.P423Aux

open KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- Reindex a sum over admissible pairs supported on the graph of `f`. -/
lemma sum_pair_graph (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i)
    (G : Pair M → ℝ) (h0 : ∀ p : Pair M, p.1.2 ≠ f p.1.1 → G p = 0) :
    ∑ p : Pair M, G p = ∑ i : S, G ⟨(i, f i), hf i⟩ := by
  symm
  refine Fintype.sum_of_injective (fun i : S => (⟨(i, f i), hf i⟩ : Pair M)) ?_ _ _ ?_ ?_
  · intro i k h
    have := congrArg (fun p : Pair M => p.1.1) h
    simpa using this
  · intro p hp
    apply h0
    intro hpf
    apply hp
    refine ⟨p.1.1, ?_⟩
    rcases p with ⟨⟨i, a⟩, ha⟩
    simp only at hpf ⊢
    subst hpf
    rfl
  · intro i; rfl

/-- `E_x` is closed under the actions selected on it. -/
lemma ex_closed (M : StationaryMDP S A) (β : S → ℝ)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hfeas : z ∈ dualFeasible M β)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (hsel : IsSelection M z.1 z.2 f hf)
    (i k : S) (hi : i ∈ Ex M z.1) (hik : 0 < M.trans i (f i) k) : k ∈ Ex M z.1 := by
  have h1 := hfeas.1 k
  have hx := (hsel i).1 hi
  show 0 < stateSum M z.1 k
  have hss : stateSum M z.1 k =
      ∑ p : Pair M, (if p.1.1 = k then (1 : ℝ) else 0) * z.1 p := by
    unfold stateSum
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs <;> simp
  have e : ∑ p : Pair M, ((if p.1.1 = k then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 k) * z.1 p
      = ∑ p : Pair M, (if p.1.1 = k then (1 : ℝ) else 0) * z.1 p
        - ∑ p : Pair M, M.trans p.1.1 p.1.2 k * z.1 p := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have hsplit : ∑ p : Pair M, (if p.1.1 = k then (1 : ℝ) else 0) * z.1 p
      = ∑ p : Pair M, M.trans p.1.1 p.1.2 k * z.1 p := by
    linarith
  rw [hss, hsplit]
  have hle : M.trans i (f i) k * z.1 ⟨(i, f i), hf i⟩ ≤
      ∑ p : Pair M, M.trans p.1.1 p.1.2 k * z.1 p := by
    refine Finset.single_le_sum (f := fun p : Pair M => M.trans p.1.1 p.1.2 k * z.1 p)
      (fun p _ => mul_nonneg (M.trans_nonneg _ _ _) (hfeas.2.2 p).1)
      (Finset.mem_univ (⟨(i, f i), hf i⟩ : Pair M))
  exact lt_of_lt_of_le (mul_pos hik hx) hle

lemma ex_reach (M : StationaryMDP S A) (β : S → ℝ)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hfeas : z ∈ dualFeasible M β)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (hsel : IsSelection M z.1 z.2 f hf)
    (a b : S) (hab : Accessible (Pf M f) a b) (ha : a ∈ Ex M z.1) : b ∈ Ex M z.1 := by
  induction hab with
  | refl => exact ha
  | tail _ hbc ih =>
    exact ex_closed M β z hfeas f hf hsel _ _ ih (by simpa [Pf] using hbc)

end KallenbergLP.AverageLP.P423Aux

open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter KallenbergLP.AverageLP in
theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (M : StationaryMDP S A)
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hext : z ∈ Set.extremePoints ℝ (dualFeasible M β))
    (hopt : IsDualOptimal M β z)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (hsel : IsSelection M z.1 z.2 f hf) :
    ∀ j ∉ Ex M z.1, ¬ IsRecurrent (Pf M f) j := by
  classical
  intro j₀ hj₀ hrec
  have hfeas : z ∈ dualFeasible M β := hext.1
  -- the closed class `C` of `j₀`
  set C : Set S := {ℓ | Accessible (Pf M f) j₀ ℓ} with hCdef
  have hj₀C : j₀ ∈ C := Relation.ReflTransGen.refl
  have hCclosed : ∀ ℓ ∈ C, ∀ m, 0 < M.trans ℓ (f ℓ) m → m ∈ C := by
    intro ℓ hℓ m hm
    exact Relation.ReflTransGen.tail hℓ (by simpa [Pf] using hm)
  have hCzero : ∀ ℓ ∈ C, ∀ m, m ∉ C → M.trans ℓ (f ℓ) m = 0 := by
    intro ℓ hℓ m hm
    exact le_antisymm (not_lt.1 fun h => hm (hCclosed ℓ hℓ m h)) (M.trans_nonneg _ _ _)
  -- `C` avoids `E_x`
  have hCT : ∀ ℓ ∈ C, ℓ ∉ Ex M z.1 := by
    intro ℓ hℓ hℓE
    have hback : Accessible (Pf M f) ℓ j₀ := hrec ℓ hℓ
    exact hj₀ (P423Aux.ex_reach M β z hfeas f hf hsel ℓ j₀ hback hℓE)
  have hypos : ∀ ℓ ∈ C, 0 < z.2 ⟨(ℓ, f ℓ), hf ℓ⟩ := fun ℓ hℓ => (hsel ℓ).2 (hCT ℓ hℓ)
  -- a nonzero left fixed vector supported on `C`
  let δ : S → S → ℝ := fun i k => if i = k then 1 else 0
  let N : Matrix S S ℝ := Matrix.of fun i k =>
    if i ∈ C then M.trans i (f i) k - δ i k else δ i k
  let u : S → ℝ := fun k => if k ∈ C then 1 else 0
  have hNu : N *ᵥ u = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, N, Matrix.of_apply, Pi.zero_apply]
    by_cases hi : i ∈ C
    · simp only [hi, if_true]
      have hterm : ∀ k, (M.trans i (f i) k - δ i k) * u k = M.trans i (f i) k - δ i k := by
        intro k
        by_cases hk : k ∈ C
        · simp [u, hk]
        · have hik : i ≠ k := fun h => hk (h ▸ hi)
          simp [u, hk, δ, hik, hCzero i hi k hk]
      simp only [hterm, Finset.sum_sub_distrib, M.trans_sum, δ, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, sub_self]
    · simp only [hi, if_false]
      have hterm : ∀ k, δ i k * u k = 0 := by
        intro k
        by_cases hik : i = k
        · subst hik; simp [u, hi]
        · simp [δ, hik]
      simp [hterm]
  have hdet : N.det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨u, ?_, hNu⟩
    intro hu
    have := congrFun hu j₀
    simp [u, hj₀C] at this
  obtain ⟨v, hv0, hvN⟩ := (Matrix.exists_vecMul_eq_zero_iff (M := N)).2 hdet
  have hvN' : ∀ k, ∑ i, v i * N i k = 0 := by
    intro k
    have := congrFun hvN k
    simpa [Matrix.vecMul, dotProduct] using this
  have hvC : ∀ k, k ∉ C → v k = 0 := by
    intro k hk
    have h := hvN' k
    have hterm : ∀ i, v i * N i k = if i = k then v k else 0 := by
      intro i
      by_cases hi : i ∈ C
      · have hik : i ≠ k := fun h => hk (h ▸ hi)
        simp [N, hi, hCzero i hi k hk, δ, hik]
      · by_cases hik : i = k
        · subst hik; simp [N, hi, δ]
        · simp [N, hi, δ, hik]
    simpa [hterm] using h
  have hfix : ∀ k, ∑ i, v i * M.trans i (f i) k = v k := by
    intro k
    have h := hvN' k
    have hterm : ∀ i, v i * N i k = v i * M.trans i (f i) k - v i * δ i k := by
      intro i
      by_cases hi : i ∈ C
      · simp [N, hi]; ring
      · simp [hvC i hi]
    simp only [hterm, Finset.sum_sub_distrib] at h
    have hd : ∑ i, v i * δ i k = v k := by simp [δ]
    linarith
  -- the perturbation direction
  let w : Pair M → ℝ := fun p => if p.1.2 = f p.1.1 then v p.1.1 else 0
  have hw : ∀ j, ∑ p : Pair M,
      ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * w p = 0 := by
    intro j
    rw [P423Aux.sum_pair_graph M f hf]
    · simp only [w, if_true]
      have : ∑ i, ((if i = j then (1 : ℝ) else 0) - M.trans i (f i) j) * v i
          = v j - ∑ i, v i * M.trans i (f i) j := by
        simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        congr 1
        exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      rw [this, hfix]; ring
    · intro p hp
      simp [w, hp]
  -- a small step size
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, i ∈ C → ε * |v i| < z.2 ⟨(i, f i), hf i⟩ := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i ∈ C
    · have ht : Tendsto (fun ε : ℝ => ε * |v i|) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun ε : ℝ => ε * |v i|) (𝓝 0) (𝓝 (0 * |v i|)) :=
          (continuous_id.mul continuous_const).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      exact (ht.eventually (gt_mem_nhds (hypos i hi))).mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => absurd h hi)
  obtain ⟨ε, hε, hεpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hεpos' : (0 : ℝ) < ε := hεpos
  have hbound : ∀ p : Pair M, |ε * w p| ≤ z.2 p := by
    rintro ⟨⟨i, a⟩, ha⟩
    by_cases hia : a = f i
    · subst hia
      by_cases hi : i ∈ C
      · have := hε i hi
        simp only [w, if_true]
        rw [abs_mul, abs_of_pos hεpos']
        exact this.le
      · simp only [w, if_true, hvC i hi, mul_zero, abs_zero]
        exact (hfeas.2.2 _).2
    · simp only [w, hia, if_false, mul_zero, abs_zero]
      exact (hfeas.2.2 _).2
  let z₁ : (Pair M → ℝ) × (Pair M → ℝ) := (z.1, fun p => z.2 p + ε * w p)
  let z₂ : (Pair M → ℝ) × (Pair M → ℝ) := (z.1, fun p => z.2 p - ε * w p)
  have hfeas_sign : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      ((z.1, fun p => z.2 p + s * (ε * w p)) : (Pair M → ℝ) × (Pair M → ℝ))
        ∈ dualFeasible M β := by
    intro s hs
    refine ⟨fun j => hfeas.1 j, fun j => ?_, fun p => ⟨(hfeas.2.2 p).1, ?_⟩⟩
    · have h2 := hfeas.2.1 j
      have hsum : ∑ p : Pair M,
          ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * (z.2 p + s * (ε * w p))
          = ∑ p : Pair M,
              ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * z.2 p
            + (s * ε) * ∑ p : Pair M,
              ((if p.1.1 = j then (1 : ℝ) else 0) - M.trans p.1.1 p.1.2 j) * w p := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        ring
      simp only
      rw [hsum, hw j, mul_zero, add_zero]
      exact h2
    · have hb := abs_le.1 (hbound p)
      rcases hs with rfl | rfl
      · simp only; linarith [hb.1]
      · simp only; linarith [hb.2]
  have h₁ : z₁ ∈ dualFeasible M β := by
    have := hfeas_sign 1 (Or.inl rfl)
    simpa [z₁] using this
  have h₂ : z₂ ∈ dualFeasible M β := by
    have := hfeas_sign (-1) (Or.inr rfl)
    have heq : ((z.1, fun p => z.2 p + (-1) * (ε * w p)) : (Pair M → ℝ) × (Pair M → ℝ)) = z₂ := by
      refine Prod.ext rfl ?_
      funext p
      simp only [z₂]
      ring
    rw [heq] at this
    exact this
  have hseg : z ∈ openSegment ℝ z₁ z₂ := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    refine Prod.ext ?_ ?_
    · funext p
      simp only [z₁, z₂, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · funext p
      simp only [z₁, z₂, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have hz₁ : z₁ = z := ((mem_extremePoints.1 hext).2 z₁ h₁ z₂ h₂ hseg).1
  apply hv0
  funext i
  have := congrFun (congrArg Prod.snd hz₁) ⟨(i, f i), hf i⟩
  simp only [z₁, w, if_true] at this
  have hm : ε * v i = 0 := by linarith
  simpa [hεpos'.ne'] using hm
