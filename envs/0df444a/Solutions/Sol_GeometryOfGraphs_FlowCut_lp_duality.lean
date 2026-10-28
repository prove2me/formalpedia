-- Prove2me | solution 1 for GeometryOfGraphs.FlowCut.lp_duality
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T10:20:57.250597+00:00
-- url     : https://prove2.me/submissions/d4cb06a8-7ec4-4065-be2c-9eafb8c7a685

import Definitions.Def_GeometryOfGraphs_FlowCut_Pseudometric
import Definitions.Def_GeometryOfGraphs_FlowCut_Network
import Definitions.Def_GeometryOfGraphs_FlowCut_Maxflow

set_option autoImplicit false

open GeometryOfGraphs.FlowCut
open Matrix
open scoped Classical

/-! ### Section 1: Fourier–Motzkin Elimination and Farkas' Lemma over `ℝ` -/

private lemma fm_between_real {ι : Type*} [Fintype ι] (α l u : ι → ℝ)
    (h : ∀ p q, 0 < α p → α q < 0 → l q ≤ u p) :
    ∃ t : ℝ, (∀ q, α q < 0 → l q ≤ t) ∧ ∀ p, 0 < α p → t ≤ u p := by
  by_cases hN : (Finset.univ.filter (fun q => α q < 0)).Nonempty
  · obtain ⟨q0, hq0, hmax⟩ := Finset.exists_max_image _ l hN
    refine ⟨l q0, fun q hq => hmax q (by simpa using hq),
      fun p hp => h p q0 hp (by simpa using hq0)⟩
  · by_cases hP : (Finset.univ.filter (fun p => 0 < α p)).Nonempty
    · obtain ⟨p0, hp0, hmin⟩ := Finset.exists_min_image _ u hP
      refine ⟨u p0, fun q hq => ?_, fun p hp => hmin p (by simpa using hp)⟩
      exact absurd ⟨q, by simpa using hq⟩ hN
    · refine ⟨0, fun q hq => ?_, fun p hp => ?_⟩
      · exact absurd ⟨q, by simpa using hq⟩ hN
      · exact absurd ⟨p, by simpa using hp⟩ hP

private theorem farkas_real : ∀ (n : ℕ) {ι : Type*} [Fintype ι] (a : ι → Fin n → ℝ) (b : ι → ℝ),
    (¬ ∃ x : Fin n → ℝ, ∀ i, a i ⬝ᵥ x ≤ b i) →
    ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i • a i = 0) ∧ ∑ i, μ i * b i < 0 := by
  intro n
  induction n with
  | zero =>
    intro ι _ a b h
    have : ∃ i, b i < 0 := by
      by_contra hc
      push Not at hc
      exact h ⟨0, fun i => by simpa using hc i⟩
    obtain ⟨i0, hi0⟩ := this
    refine ⟨fun i => if i = i0 then 1 else 0,
      fun i => by dsimp only; split_ifs <;> norm_num, ?_, ?_⟩
    · funext j; exact j.elim0
    · simpa using hi0
  | succ n ih =>
    intro ι _ a b h
    set α : ι → ℝ := fun i => a i 0 with hα
    set a' : ι → Fin n → ℝ := fun i j => a i j.succ with ha'
    have hdot : ∀ i (t : ℝ) (x' : Fin n → ℝ),
        a i ⬝ᵥ (vecCons t x') = α i * t + a' i ⬝ᵥ x' := by
      intro i t x'
      simp only [dotProduct, Fin.sum_univ_succ, hα, ha']
      simp
    let W : ι × ι → ι → ℝ := fun pq l =>
      (if α pq.1 = 0 ∧ pq.1 = pq.2 ∧ l = pq.1 then 1 else 0) +
      (if 0 < α pq.1 ∧ α pq.2 < 0 then
        ((if l = pq.1 then -α pq.2 else 0) + (if l = pq.2 then α pq.1 else 0)) else 0)
    have hW0 : ∀ pq l, 0 ≤ W pq l := by
      intro pq l
      simp only [W]
      split_ifs <;> linarith
    have hW1 : ∀ i, α i = 0 → ∀ v : ι → ℝ, ∑ l, W (i, i) l * v l = v i := by
      intro i hi v
      have : ∀ l, W (i, i) l = if l = i then 1 else 0 := by
        intro l; simp [W, hi]
      simp [this]
    have hW2 : ∀ p q, 0 < α p → α q < 0 → ∀ v : ι → ℝ,
        ∑ l, W (p, q) l * v l = -α q * v p + α p * v q := by
      intro p q hp hq v
      have hpq : p ≠ q := fun e => by subst e; linarith
      have : ∀ l, W (p, q) l = (if l = p then -α q else 0) + (if l = q then α p else 0) := by
        intro l; simp [W, hp, hq, hp.ne', hpq]
      simp [this, add_mul, Finset.sum_add_distrib]
    have hW3 : ∀ p q, ¬ (α p = 0 ∧ p = q) → ¬ (0 < α p ∧ α q < 0) → ∀ v : ι → ℝ,
        ∑ l, W (p, q) l * v l = 0 := by
      intro p q h1 h2 v
      have : ∀ l, W (p, q) l = 0 := by
        intro l
        have h1' : ¬ (α p = 0 ∧ p = q ∧ l = p) := fun h => h1 ⟨h.1, h.2.1⟩
        simp only [W]; rw [if_neg h1', if_neg h2]; simp
      simp [this]
    have hWα : ∀ pq, ∑ l, W pq l * α l = 0 := by
      intro pq
      obtain ⟨p, q⟩ := pq
      by_cases h1 : α p = 0 ∧ p = q
      · obtain ⟨h1a, rfl⟩ := h1
        rw [hW1 p h1a]; exact h1a
      · by_cases h2 : 0 < α p ∧ α q < 0
        · rw [hW2 p q h2.1 h2.2]; ring
        · exact hW3 p q h1 h2 _
    let a'' : ι × ι → Fin n → ℝ := fun pq => ∑ l, W pq l • a' l
    let b'' : ι × ι → ℝ := fun pq => ∑ l, W pq l * b l
    have hinf : ¬ ∃ x' : Fin n → ℝ, ∀ pq, a'' pq ⬝ᵥ x' ≤ b'' pq := by
      rintro ⟨x', hx'⟩
      have hex := fm_between_real α (fun q => (b q - a' q ⬝ᵥ x') / α q)
        (fun p => (b p - a' p ⬝ᵥ x') / α p) (by
          intro p q hp hq
          have := hx' (p, q)
          have e1 : a'' (p, q) ⬝ᵥ x' = ∑ l, W (p, q) l * (a' l ⬝ᵥ x') := by
            simp only [a'', sum_dotProduct, smul_dotProduct, smul_eq_mul]
          rw [e1] at this
          have hsum : ∑ l, W (p, q) l * (a' l ⬝ᵥ x') = -α q * (a' p ⬝ᵥ x') + α p * (a' q ⬝ᵥ x') :=
            hW2 p q hp hq _
          have hb : b'' (p, q) = -α q * b p + α p * b q := hW2 p q hp hq _
          rw [hsum, hb] at this
          rw [div_le_iff_of_neg hq, div_mul_eq_mul_div, div_le_iff₀ hp]
          nlinarith)
      obtain ⟨t, htl, htu⟩ := hex
      apply h
      refine ⟨vecCons t x', fun i => ?_⟩
      rw [hdot]
      rcases lt_trichotomy (α i) 0 with hi | hi | hi
      · have := htl i hi
        rw [div_le_iff_of_neg hi] at this
        linarith
      · have := hx' (i, i)
        have e1 : a'' (i, i) ⬝ᵥ x' = a' i ⬝ᵥ x' := by
          simp only [a'', sum_dotProduct, smul_dotProduct, smul_eq_mul]
          exact hW1 i hi (fun l => a' l ⬝ᵥ x')
        have e2 : b'' (i, i) = b i := hW1 i hi b
        rw [e1, e2] at this
        rw [hi]; linarith
      · have := htu i hi
        rw [le_div_iff₀ hi] at this
        linarith
    obtain ⟨μ'', hμ0, hμa, hμb⟩ := ih a'' b'' hinf
    refine ⟨fun l => ∑ pq, μ'' pq * W pq l,
      fun l => Finset.sum_nonneg (fun pq _ => mul_nonneg (hμ0 pq) (hW0 pq l)), ?_, ?_⟩
    · funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        have : ∀ l, a l 0 = α l := fun l => rfl
        simp only [this]
        calc ∑ l, (∑ pq, μ'' pq * W pq l) * α l
            = ∑ pq, μ'' pq * ∑ l, W pq l * α l := by
              simp only [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          _ = 0 := by simp [hWα]
      · have := congrFun hμa j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, a''] at this ⊢
        have e : ∀ l, a l j.succ = a' l j := fun l => rfl
        simp only [e]
        calc ∑ l, (∑ pq, μ'' pq * W pq l) * a' l j
            = ∑ pq, μ'' pq * ∑ l, W pq l * a' l j := by
              simp only [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          _ = 0 := by rw [← this]
    · calc ∑ l, (∑ pq, μ'' pq * W pq l) * b l
          = ∑ pq, μ'' pq * b'' pq := by
            simp only [b'', Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ < 0 := hμb

/-- Coordinate-free Farkas' lemma over `ℝ` for finite variable type `α` and constraint type `ι`. -/
private theorem farkas_fintype {α ι : Type*} [Fintype α] [Fintype ι]
    (a : ι → α → ℝ) (b : ι → ℝ)
    (h : ¬ ∃ x : α → ℝ, ∀ i, (∑ v : α, a i v * x v) ≤ b i) :
    ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ v : α, ∑ i, μ i * a i v = 0) ∧ ∑ i, μ i * b i < 0 := by
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let a' : ι → Fin (Fintype.card α) → ℝ := fun i j => a i (e.symm j)
  have h' : ¬ ∃ x : Fin (Fintype.card α) → ℝ, ∀ i, a' i ⬝ᵥ x ≤ b i := by
    rintro ⟨x, hx⟩
    apply h
    refine ⟨fun v => x (e v), fun i => ?_⟩
    have := hx i
    have hsum : (∑ v : α, a i v * x (e v)) = a' i ⬝ᵥ x := by
      simp only [dotProduct, a']
      simpa using e.sum_comp (fun j => a i (e.symm j) * x j)
    linarith
  obtain ⟨μ, hμ0, hμa, hμb⟩ := farkas_real (Fintype.card α) a' b h'
  refine ⟨μ, hμ0, fun v => ?_, hμb⟩
  have hv := congrFun hμa (e v)
  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, a'] using hv

/-! ### Section 2: Weak Duality for Concurrent Flow and Pseudometrics -/

private lemma flow_weak_duality {V : Type*} [Fintype V] [DecidableEq V] (N : Network V)
    (f : Fin N.k → V → V → ℝ) (lam : ℝ) (hf : N.IsFeasibleFlow f lam)
    (d : V → V → ℝ) (hd : IsPseudometric d) :
    lam * ∑ μ, N.D μ * d (N.s μ) (N.t μ) ≤ (1 / 2) * ∑ i, ∑ j, N.C i j * d i j := by
  obtain ⟨hd_self, hd_nonneg, hd_symm, hd_tri⟩ := hd
  obtain ⟨hf_nonneg, hf_cons, hf_cap⟩ := hf
  have h_commodity : ∀ μ : Fin N.k,
      lam * N.D μ * d (N.s μ) (N.t μ) ≤ ∑ i, ∑ j, f μ i j * d i j := by
    intro μ
    have h_sum_v : ∑ v : V, (∑ j : V, f μ v j - ∑ j : V, f μ j v) * d v (N.t μ) =
        lam * N.D μ * d (N.s μ) (N.t μ) := by
      calc
        ∑ v : V, (∑ j : V, f μ v j - ∑ j : V, f μ j v) * d v (N.t μ)
          = ∑ v : V, (lam * N.D μ *
              ((if v = N.s μ then 1 else 0) - (if v = N.t μ then 1 else 0))) * d v (N.t μ) := by
            refine Finset.sum_congr rfl fun v _ => by rw [hf_cons μ v]
        _ = lam * N.D μ * (d (N.s μ) (N.t μ) - d (N.t μ) (N.t μ)) := by
            have h1 : ∀ v : V,
                (lam * N.D μ *
                  ((if v = N.s μ then 1 else 0) - (if v = N.t μ then 1 else 0))) * d v (N.t μ) =
                (if v = N.s μ then lam * N.D μ * d v (N.t μ) else 0) -
                (if v = N.t μ then lam * N.D μ * d v (N.t μ) else 0) := by
              intro v; split_ifs <;> ring
            simp only [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
            ring
        _ = lam * N.D μ * d (N.s μ) (N.t μ) := by
            rw [hd_self (N.t μ), sub_zero]
    have h_rearrange : ∑ v : V, (∑ j : V, f μ v j - ∑ j : V, f μ j v) * d v (N.t μ) =
        ∑ i : V, ∑ j : V, f μ i j * (d i (N.t μ) - d j (N.t μ)) := by
      simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
      have h_swap : (∑ v : V, ∑ j : V, f μ j v * d v (N.t μ)) =
          ∑ i : V, ∑ j : V, f μ i j * d j (N.t μ) := Finset.sum_comm
      rw [h_swap]
      simp only [← Finset.sum_sub_distrib, ← mul_sub]
    rw [← h_sum_v, h_rearrange]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (hf_nonneg μ i j)
    linarith [hd_tri i j (N.t μ)]
  have h_sum_μ : lam * ∑ μ, N.D μ * d (N.s μ) (N.t μ) ≤
      ∑ μ, ∑ i, ∑ j, f μ i j * d i j := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun μ _ => ?_)
    rw [← mul_assoc]
    exact h_commodity μ
  have h_symm_f : (∑ μ, ∑ i, ∑ j, f μ i j * d i j) =
      (1 / 2) * ∑ i, ∑ j, (∑ μ, (f μ i j + f μ j i)) * d i j := by
    have h1 : (∑ μ, ∑ i, ∑ j, f μ i j * d i j) = ∑ i, ∑ j, (∑ μ, f μ i j) * d i j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
    have h2 : (∑ i, ∑ j, (∑ μ, f μ j i) * d i j) = ∑ i, ∑ j, (∑ μ, f μ i j) * d i j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hd_symm j i]
    have h3 : ∑ i, ∑ j, (∑ μ, (f μ i j + f μ j i)) * d i j =
        (∑ i, ∑ j, (∑ μ, f μ i j) * d i j) + (∑ i, ∑ j, (∑ μ, f μ j i) * d i j) := by
      simp only [Finset.sum_add_distrib, add_mul]
    linarith
  refine h_sum_μ.trans ?_
  rw [h_symm_f]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  exact mul_le_mul_of_nonneg_right (hf_cap i j) (hd_nonneg i j)

private lemma zero_mem_feasibleFlow {V : Type*} [Fintype V] [DecidableEq V] (N : Network V) :
    (0 : ℝ) ∈ {lam : ℝ | 0 ≤ lam ∧ ∃ f : Fin N.k → V → V → ℝ, N.IsFeasibleFlow f lam} := by
  refine ⟨le_rfl, fun _ _ _ => 0, ?_, ?_, ?_⟩
  · intro _ _ _; exact le_rfl
  · intro _ _; simp
  · intro i j; simp [N.C_nonneg i j]

private lemma discrete_isPseudometric {V : Type*} [DecidableEq V] :
    IsPseudometric (fun x y : V => if x = y then (0 : ℝ) else 1) := by
  refine ⟨fun x => by simp, fun x y => by dsimp only; split_ifs <;> norm_num,
    fun x y => by dsimp only; by_cases h : x = y <;> simp [h, eq_comm],
    fun x y z => ?_⟩
  dsimp only
  by_cases hxy : x = y <;> by_cases hyz : y = z
  · subst hxy hyz; simp
  · subst hxy; simp [hyz]
  · subst hyz; simp [hxy]
  · simp only [if_neg hxy, if_neg hyz]
    split_ifs <;> norm_num

private lemma bddAbove_feasibleFlow {V : Type*} [Fintype V] [DecidableEq V] (N : Network V)
    (hN : ∃ μ, 0 < N.D μ ∧ N.s μ ≠ N.t μ) :
    BddAbove {lam : ℝ | 0 ≤ lam ∧ ∃ f : Fin N.k → V → V → ℝ, N.IsFeasibleFlow f lam} := by
  obtain ⟨μ0, hD0, hst0⟩ := hN
  let d0 : V → V → ℝ := fun x y => if x = y then 0 else 1
  have hd0 : IsPseudometric d0 := discrete_isPseudometric
  have hD_pos : 0 < ∑ μ, N.D μ * d0 (N.s μ) (N.t μ) := by
    have h_nonneg : ∀ μ ∈ Finset.univ, 0 ≤ N.D μ * d0 (N.s μ) (N.t μ) := by
      intro μ _
      exact mul_nonneg (N.D_nonneg μ) (hd0.2.1 _ _)
    have h_pos0 : 0 < N.D μ0 * d0 (N.s μ0) (N.t μ0) := by
      simp [d0, hst0, hD0]
    exact lt_of_lt_of_le h_pos0 (Finset.single_le_sum h_nonneg (Finset.mem_univ μ0))
  refine ⟨((1 / 2) * ∑ i, ∑ j, N.C i j * d0 i j) / (∑ μ, N.D μ * d0 (N.s μ) (N.t μ)), ?_⟩
  rintro lam ⟨_, f, hf⟩
  rw [le_div_iff₀ hD_pos]
  exact flow_weak_duality N f lam hf d0 hd0

private lemma maxflow_nonneg {V : Type*} [Fintype V] [DecidableEq V] (N : Network V)
    (hN : ∃ μ, 0 < N.D μ ∧ N.s μ ≠ N.t μ) : 0 ≤ N.maxflow :=
  le_csSup (bddAbove_feasibleFlow N hN) (zero_mem_feasibleFlow N)

private theorem weak_duality_part1 {V : Type*} [Fintype V] [DecidableEq V] (N : Network V) :
    ∀ d : V → V → ℝ, IsPseudometric d →
      N.maxflow * ∑ μ, N.D μ * d (N.s μ) (N.t μ) ≤ (1 / 2) * ∑ i, ∑ j, N.C i j * d i j := by
  intro d hd
  set D_sum := ∑ μ, N.D μ * d (N.s μ) (N.t μ)
  set C_sum := (1 / 2) * ∑ i, ∑ j, N.C i j * d i j
  have hD_nonneg : 0 ≤ D_sum :=
    Finset.sum_nonneg fun μ _ => mul_nonneg (N.D_nonneg μ) (hd.2.1 _ _)
  have hC_nonneg : 0 ≤ C_sum := by
    refine mul_nonneg (by norm_num) ?_
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (N.C_nonneg i j) (hd.2.1 i j)
  rcases hD_nonneg.lt_or_eq with hD_pos | hD_zero
  · rw [← le_div_iff₀ hD_pos]
    refine csSup_le ⟨0, zero_mem_feasibleFlow N⟩ ?_
    rintro lam ⟨_, f, hf⟩
    rw [le_div_iff₀ hD_pos]
    exact flow_weak_duality N f lam hf d hd
  · rw [← hD_zero, mul_zero]
    exact hC_nonneg

/-! ### Section 3: Lipschitz Envelope Pseudometric and Farkas Dual of Infeasible Flow -/

private def LipSet {V : Type*} (ℓ : V → V → ℝ) : Set (V → ℝ) :=
  {q | ∀ i j : V, q i - q j ≤ ℓ i j}

private noncomputable def lipDist {V : Type*} (ℓ : V → V → ℝ) (x y : V) : ℝ :=
  sSup ((fun q : V → ℝ => q x - q y) '' LipSet ℓ)

private lemma lipDist_props {V : Type*} (ℓ : V → V → ℝ)
    (hℓ_nonneg : ∀ i j, 0 ≤ ℓ i j) (hℓ_symm : ∀ i j, ℓ i j = ℓ j i) :
    IsPseudometric (lipDist ℓ) ∧
    (∀ i j, lipDist ℓ i j ≤ ℓ i j) ∧
    (∀ q ∈ LipSet ℓ, ∀ x y, q x - q y ≤ lipDist ℓ x y) := by
  have h0_mem : (0 : V → ℝ) ∈ LipSet ℓ := by
    intro i j; simp [hℓ_nonneg i j]
  have h_ne : ∀ x y : V, ((fun q : V → ℝ => q x - q y) '' LipSet ℓ).Nonempty :=
    fun x y => ⟨0, 0, h0_mem, by simp⟩
  have h_bdd : ∀ x y : V, BddAbove ((fun q : V → ℝ => q x - q y) '' LipSet ℓ) := by
    intro x y
    refine ⟨ℓ x y, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact hq x y
  have h_le_ℓ : ∀ i j : V, lipDist ℓ i j ≤ ℓ i j := by
    intro i j
    refine csSup_le (h_ne i j) ?_
    rintro _ ⟨q, hq, rfl⟩
    exact hq i j
  have h_q_le : ∀ q ∈ LipSet ℓ, ∀ x y : V, q x - q y ≤ lipDist ℓ x y :=
    fun q hq x y => le_csSup (h_bdd x y) ⟨q, hq, rfl⟩
  have h_nonneg : ∀ x y : V, 0 ≤ lipDist ℓ x y := by
    intro x y
    have := h_q_le 0 h0_mem x y
    simpa using this
  have h_self : ∀ x : V, lipDist ℓ x x = 0 := by
    intro x
    refine le_antisymm ?_ (h_nonneg x x)
    refine csSup_le (h_ne x x) ?_
    rintro _ ⟨q, _, rfl⟩
    simp
  have h_symm_le : ∀ x y : V, lipDist ℓ x y ≤ lipDist ℓ y x := by
    intro x y
    refine csSup_le (h_ne x y) ?_
    rintro _ ⟨q, hq, rfl⟩
    have hnq : -q ∈ LipSet ℓ := by
      intro i j
      simp only [Pi.neg_apply, neg_sub_neg]
      exact (hq j i).trans_eq (hℓ_symm j i)
    have := h_q_le (-q) hnq y x
    dsimp only [Pi.neg_apply] at this
    linarith
  have h_symm : ∀ x y : V, lipDist ℓ x y = lipDist ℓ y x :=
    fun x y => le_antisymm (h_symm_le x y) (h_symm_le y x)
  have h_tri : ∀ x y z : V, lipDist ℓ x z ≤ lipDist ℓ x y + lipDist ℓ y z := by
    intro x y z
    refine csSup_le (h_ne x z) ?_
    rintro _ ⟨q, hq, rfl⟩
    have h1 := h_q_le q hq x y
    have h2 := h_q_le q hq y z
    linarith
  exact ⟨⟨h_self, h_nonneg, h_symm, h_tri⟩, h_le_ℓ, h_q_le⟩

/-- For any infeasible flow value `lam > 0`, Farkas' lemma produces a pseudometric `d` with
positive demand sum and `(1/2) * ∑ C_{ij} d_{ij} < lam * ∑ D_μ d(s_μ, t_μ)`. -/
private lemma exists_pseudometric_lt_of_infeasible {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (lam : ℝ) (hlam_pos : 0 < lam)
    (hinf : ¬ ∃ f : Fin N.k → V → V → ℝ, N.IsFeasibleFlow f lam) :
    ∃ d : V → V → ℝ, IsPseudometric d ∧
      0 < ∑ μ, N.D μ * d (N.s μ) (N.t μ) ∧
      (1 / 2) * ∑ i, ∑ j, N.C i j * d i j < lam * ∑ μ, N.D μ * d (N.s μ) (N.t μ) := by
  let rhs_cons : Fin N.k → V → ℝ := fun μ v =>
    lam * N.D μ * ((if v = N.s μ then 1 else 0) - (if v = N.t μ then 1 else 0))
  let A_sys : ((Fin N.k × V × V) ⊕ (Fin N.k × V) ⊕ (V × V)) → (Fin N.k × V × V) → ℝ := fun c x =>
    match c with
    | Sum.inl (μ, i, j) => if x = (μ, i, j) then -1 else 0
    | Sum.inr (Sum.inl (μ, v)) =>
        if x.1 = μ then
          (if x.2.2 = v then 1 else 0) - (if x.2.1 = v then 1 else 0)
        else 0
    | Sum.inr (Sum.inr (i, j)) =>
        (if x.2 = (i, j) then 1 else 0) + (if x.2 = (j, i) then 1 else 0)
  let b_sys : ((Fin N.k × V × V) ⊕ (Fin N.k × V) ⊕ (V × V)) → ℝ := fun c =>
    match c with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl (μ, v)) => -rhs_cons μ v
    | Sum.inr (Sum.inr (i, j)) => N.C i j
  have hA_inl : ∀ (μ : Fin N.k) (i j : V) (x : Fin N.k × V × V → ℝ),
      (∑ v : Fin N.k × V × V, A_sys (Sum.inl (μ, i, j)) v * x v) = -x (μ, i, j) := by
    intro μ i j x
    have : ∀ v : Fin N.k × V × V,
        A_sys (Sum.inl (μ, i, j)) v * x v = if v = (μ, i, j) then -x v else 0 := by
      intro v; dsimp only [A_sys]; split_ifs <;> ring
    simp [this]
  have hA_cons : ∀ (μ : Fin N.k) (v : V) (x : Fin N.k × V × V → ℝ),
      (∑ y : Fin N.k × V × V, A_sys (Sum.inr (Sum.inl (μ, v))) y * x y) =
        (∑ j : V, x (μ, j, v)) - (∑ j : V, x (μ, v, j)) := by
    intro μ v x
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single μ (by
      intro μ' _ hμ'
      refine Finset.sum_eq_zero fun yz _ => ?_
      dsimp only [A_sys]
      rw [if_neg hμ', zero_mul]) (by simp)]
    rw [Fintype.sum_prod_type]
    have h_inner : ∀ i j : V,
        A_sys (Sum.inr (Sum.inl (μ, v))) (μ, i, j) * x (μ, i, j) =
        (if j = v then x (μ, i, j) else 0) - (if i = v then x (μ, i, j) else 0) := by
      intro i j; simp only [A_sys, ↓reduceIte]; split_ifs <;> ring
    simp only [h_inner, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_comm]
      simp
    · simp
  have hA_cap : ∀ (i j : V) (x : Fin N.k × V × V → ℝ),
      (∑ y : Fin N.k × V × V, A_sys (Sum.inr (Sum.inr (i, j))) y * x y) =
        ∑ μ : Fin N.k, (x (μ, i, j) + x (μ, j, i)) := by
    intro i j x
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have h_inner : ∀ uv : V × V,
        A_sys (Sum.inr (Sum.inr (i, j))) (μ, uv) * x (μ, uv) =
        (if uv = (i, j) then x (μ, uv) else 0) +
        (if uv = (j, i) then x (μ, uv) else 0) := by
      intro uv; dsimp only [A_sys]; split_ifs <;> ring
    simp [h_inner, Finset.sum_add_distrib]
  have h_sys_inf : ¬ ∃ x : Fin N.k × V × V → ℝ,
      ∀ c : (Fin N.k × V × V) ⊕ (Fin N.k × V) ⊕ (V × V),
        (∑ y : Fin N.k × V × V, A_sys c y * x y) ≤ b_sys c := by
    rintro ⟨x, hx⟩
    apply hinf
    let f : Fin N.k → V → V → ℝ := fun μ i j => x (μ, i, j)
    refine ⟨f, ?_, ?_, ?_⟩
    · intro μ i j
      have h := hx (Sum.inl (μ, i, j))
      rw [hA_inl] at h
      dsimp only [b_sys, f] at h ⊢
      linarith
    · intro μ v
      have h_le : ∀ w : V, (∑ j : V, f μ j w) - (∑ j : V, f μ w j) ≤ -rhs_cons μ w := by
        intro w
        have hw := hx (Sum.inr (Sum.inl (μ, w)))
        rwa [hA_cons] at hw
      have h_nonneg : ∀ w : V,
          0 ≤ (∑ j : V, f μ w j - ∑ j : V, f μ j w) - rhs_cons μ w := by
        intro w; linarith [h_le w]
      have h_sum_zero : ∑ w : V,
          ((∑ j : V, f μ w j - ∑ j : V, f μ j w) - rhs_cons μ w) = 0 := by
        simp only [Finset.sum_sub_distrib, rhs_cons]
        have h1 : (∑ w : V, ∑ j : V, f μ w j) - (∑ w : V, ∑ j : V, f μ j w) = 0 := by
          rw [Finset.sum_comm]; ring
        have h2 : ∑ w : V, lam * N.D μ *
            ((if w = N.s μ then 1 else 0) - (if w = N.t μ then 1 else 0)) = 0 := by
          have : ∀ w : V,
              lam * N.D μ * ((if w = N.s μ then 1 else 0) - (if w = N.t μ then 1 else 0)) =
              (if w = N.s μ then lam * N.D μ else 0) - (if w = N.t μ then lam * N.D μ else 0) := by
            intro w; split_ifs <;> ring
          simp [this, Finset.sum_sub_distrib]
        linarith
      have h_eq_zero :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => h_nonneg w)).mp h_sum_zero v (Finset.mem_univ v)
      linarith
    · intro i j
      have h := hx (Sum.inr (Sum.inr (i, j)))
      rwa [hA_cap] at h
  obtain ⟨μ_dual, hμ0, hμA, hμb⟩ := farkas_fintype A_sys b_sys h_sys_inf
  let p : Fin N.k → V → ℝ := fun μ v => μ_dual (Sum.inr (Sum.inl (μ, v)))
  let w : V → V → ℝ := fun i j => μ_dual (Sum.inr (Sum.inr (i, j)))
  let ℓ : V → V → ℝ := fun i j => w i j + w j i
  have hℓ_nonneg : ∀ i j, 0 ≤ ℓ i j :=
    fun i j => add_nonneg (hμ0 (Sum.inr (Sum.inr (i, j)))) (hμ0 (Sum.inr (Sum.inr (j, i))))
  have hℓ_symm : ∀ i j, ℓ i j = ℓ j i := fun i j => add_comm (w i j) (w j i)
  have hp_lip : ∀ μ : Fin N.k, p μ ∈ LipSet ℓ := by
    intro μ i j
    have h_var := hμA (μ, i, j)
    simp only [Fintype.sum_sum_type] at h_var
    have h_s1 : (∑ z : Fin N.k × V × V,
          μ_dual (Sum.inl z) * A_sys (Sum.inl z) (μ, i, j)) =
        -μ_dual (Sum.inl (μ, i, j)) := by
      have : ∀ z : Fin N.k × V × V,
          μ_dual (Sum.inl z) * A_sys (Sum.inl z) (μ, i, j) =
          if (μ, i, j) = z then -μ_dual (Sum.inl z) else 0 := by
        intro z; dsimp only [A_sys]; split_ifs <;> ring
      simp [this]
    have h_s2 : (∑ μv : Fin N.k × V, μ_dual (Sum.inr (Sum.inl μv)) *
          A_sys (Sum.inr (Sum.inl μv)) (μ, i, j)) = p μ j - p μ i := by
      rw [Fintype.sum_prod_type]
      have : ∀ (μ' : Fin N.k) (v : V),
          μ_dual (Sum.inr (Sum.inl (μ', v))) * A_sys (Sum.inr (Sum.inl (μ', v))) (μ, i, j) =
          if μ = μ' then
            (if j = v then p μ' v else 0) - (if i = v then p μ' v else 0)
          else 0 := by
        intro μ' v; dsimp only [A_sys, p]; split_ifs <;> ring
      simp [this, Finset.sum_sub_distrib]
    have h_s3 : (∑ uv : V × V, μ_dual (Sum.inr (Sum.inr uv)) *
          A_sys (Sum.inr (Sum.inr uv)) (μ, i, j)) = ℓ i j := by
      rw [Fintype.sum_prod_type]
      simp only [A_sys, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Prod.mk.injEq,
        ite_and]
      simp [ℓ, w]
    rw [h_s1, h_s2, h_s3] at h_var
    have h_α_nonneg : 0 ≤ μ_dual (Sum.inl (μ, i, j)) := hμ0 (Sum.inl (μ, i, j))
    linarith
  have h_b_ineq : (1 / 2) * ∑ i, ∑ j, N.C i j * ℓ i j <
      lam * ∑ μ, N.D μ * (p μ (N.s μ) - p μ (N.t μ)) := by
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, b_sys, mul_zero,
      Finset.sum_const_zero, zero_add] at hμb
    have h_cons_sum : (∑ x : Fin N.k, ∑ v : V,
        μ_dual (Sum.inr (Sum.inl (x, v))) * -rhs_cons x v) =
        -(lam * ∑ μ : Fin N.k, N.D μ * (p μ (N.s μ) - p μ (N.t μ))) := by
      simp only [rhs_cons, p, mul_neg, Finset.sum_neg_distrib, neg_inj, Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      have : ∀ v : V,
          μ_dual (Sum.inr (Sum.inl (μ, v))) *
            (lam * N.D μ * ((if v = N.s μ then 1 else 0) - (if v = N.t μ then 1 else 0))) =
          (if v = N.s μ then lam * N.D μ * μ_dual (Sum.inr (Sum.inl (μ, v))) else 0) -
          (if v = N.t μ then lam * N.D μ * μ_dual (Sum.inr (Sum.inl (μ, v))) else 0) := by
        intro v; split_ifs <;> ring
      simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      ring
    have h_cap_sum : (∑ i : V, ∑ j : V, μ_dual (Sum.inr (Sum.inr (i, j))) * N.C i j) =
        (1 / 2) * ∑ i : V, ∑ j : V, N.C i j * ℓ i j := by
      have h_symm_w : (∑ i : V, ∑ j : V, w j i * N.C i j) =
          ∑ i : V, ∑ j : V, w i j * N.C i j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [N.C_symm j i]
      have h_expand : ∑ i : V, ∑ j : V, N.C i j * ℓ i j =
          (∑ i : V, ∑ j : V, w i j * N.C i j) + (∑ i : V, ∑ j : V, w j i * N.C i j) := by
        have : ∀ i j : V, N.C i j * ℓ i j = w i j * N.C i j + w j i * N.C i j := by
          intro i j; dsimp only [ℓ]; ring
        simp only [this, Finset.sum_add_distrib]
      dsimp only [w] at h_expand h_symm_w
      linarith
    linarith
  obtain ⟨hd_pseudo, hd_le_ℓ, hq_le_d⟩ := lipDist_props ℓ hℓ_nonneg hℓ_symm
  let d := lipDist ℓ
  have hC_le : (1 / 2) * ∑ i, ∑ j, N.C i j * d i j ≤ (1 / 2) * ∑ i, ∑ j, N.C i j * ℓ i j := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_left (hd_le_ℓ i j) (N.C_nonneg i j)
  have hD_le : lam * ∑ μ, N.D μ * (p μ (N.s μ) - p μ (N.t μ)) ≤
      lam * ∑ μ, N.D μ * d (N.s μ) (N.t μ) := by
    refine mul_le_mul_of_nonneg_left ?_ hlam_pos.le
    refine Finset.sum_le_sum fun μ _ => ?_
    exact mul_le_mul_of_nonneg_left (hq_le_d (p μ) (hp_lip μ) (N.s μ) (N.t μ)) (N.D_nonneg μ)
  have h_strict : (1 / 2) * ∑ i, ∑ j, N.C i j * d i j <
      lam * ∑ μ, N.D μ * d (N.s μ) (N.t μ) :=
    (hC_le.trans_lt h_b_ineq).trans_le hD_le
  have hC_nonneg : 0 ≤ (1 / 2) * ∑ i, ∑ j, N.C i j * d i j := by
    refine mul_nonneg (by norm_num) ?_
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (N.C_nonneg i j) (hd_pseudo.2.1 i j)
  have hD_pos : 0 < ∑ μ, N.D μ * d (N.s μ) (N.t μ) := by
    have : 0 < lam * ∑ μ, N.D μ * d (N.s μ) (N.t μ) := hC_nonneg.trans_lt h_strict
    exact pos_of_mul_pos_right this hlam_pos.le
  exact ⟨d, hd_pseudo, hD_pos, h_strict⟩

/-! ### Section 4: Truncation and Compactness of Normalized Pseudometrics -/

private lemma isPseudometric_scale {V : Type*} {d : V → V → ℝ} (hd : IsPseudometric d)
    {c : ℝ} (hc : 0 ≤ c) : IsPseudometric (fun x y => c * d x y) := by
  obtain ⟨h_self, h_nonneg, h_symm, h_tri⟩ := hd
  refine ⟨fun x => by simp [h_self x],
    fun x y => mul_nonneg hc (h_nonneg x y),
    fun x y => by dsimp only; rw [h_symm x y],
    fun x y z => by dsimp only; nlinarith [h_tri x y z]⟩

private lemma isPseudometric_min_const {V : Type*} {d : V → V → ℝ} (hd : IsPseudometric d)
    {B : ℝ} (hB : 0 ≤ B) : IsPseudometric (fun x y => min (d x y) B) := by
  obtain ⟨h_self, h_nonneg, h_symm, h_tri⟩ := hd
  refine ⟨fun x => by dsimp only; rw [h_self x, min_eq_left hB],
    fun x y => le_min (h_nonneg x y) hB,
    fun x y => by dsimp only; rw [h_symm x y],
    fun x y z => ?_⟩
  dsimp only
  rcases le_total (d x y) B with hxy | hxy <;> rcases le_total (d y z) B with hyz | hyz
  · rw [min_eq_left hxy, min_eq_left hyz]
    exact (min_le_left (d x z) B).trans (h_tri x y z)
  · rw [min_eq_left hxy, min_eq_right hyz]
    linarith [min_le_right (d x z) B, h_nonneg x y]
  · rw [min_eq_right hxy, min_eq_left hyz]
    linarith [min_le_right (d x z) B, h_nonneg y z]
  · rw [min_eq_right hxy, min_eq_right hyz]
    linarith [min_le_right (d x z) B]

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (N : Network V)
    (hN : ∃ μ, 0 < N.D μ ∧ N.s μ ≠ N.t μ) :
    (∀ d : V → V → ℝ, IsPseudometric d →
      N.maxflow * ∑ μ, N.D μ * d (N.s μ) (N.t μ) ≤ (1 / 2) * ∑ i, ∑ j, N.C i j * d i j) ∧
    ∃ d : V → V → ℝ, IsPseudometric d ∧ 0 < ∑ μ, N.D μ * d (N.s μ) (N.t μ) ∧
      N.maxflow * ∑ μ, N.D μ * d (N.s μ) (N.t μ) = (1 / 2) * ∑ i, ∑ j, N.C i j * d i j := by
  refine ⟨weak_duality_part1 N, ?_⟩
  let B : ℝ := (∑ μ : Fin N.k, if 0 < N.D μ then 1 / N.D μ else 0) + 1
  have hB_pos : 0 < B := by
    refine add_pos_of_nonneg_of_pos ?_ zero_lt_one
    refine Finset.sum_nonneg fun μ _ => ?_
    split_ifs with h
    · exact div_nonneg zero_le_one h.le
    · exact le_rfl
  -- Any pseudometric `d` with positive demand sum can be normalized and truncated at `B`.
  have h_norm_trunc : ∀ d : V → V → ℝ, IsPseudometric d →
      0 < ∑ μ, N.D μ * d (N.s μ) (N.t μ) →
      ∃ d' : V → V → ℝ, IsPseudometric d' ∧
        (∀ x y, d' x y ≤ B) ∧
        (∑ μ, N.D μ * d' (N.s μ) (N.t μ) = 1) ∧
        (1 / 2) * ∑ i, ∑ j, N.C i j * d' i j ≤
          ((1 / 2) * ∑ i, ∑ j, N.C i j * d i j) / (∑ μ, N.D μ * d (N.s μ) (N.t μ)) := by
    intro d hd hD_pos
    set D_sum := ∑ μ, N.D μ * d (N.s μ) (N.t μ)
    let d1 : V → V → ℝ := fun x y => D_sum⁻¹ * d x y
    have hd1 : IsPseudometric d1 := isPseudometric_scale hd (inv_nonneg.mpr hD_pos.le)
    have hd1_sum : ∑ μ, N.D μ * d1 (N.s μ) (N.t μ) = 1 := by
      have : (∑ μ, N.D μ * (D_sum⁻¹ * d (N.s μ) (N.t μ))) = D_sum⁻¹ * D_sum := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun μ _ => by ring
      dsimp only [d1]
      rw [this, inv_mul_cancel₀ hD_pos.ne']
    have hd1_le_B : ∀ μ : Fin N.k, 0 < N.D μ → d1 (N.s μ) (N.t μ) ≤ B := by
      intro μ hμ
      have h_single : N.D μ * d1 (N.s μ) (N.t μ) ≤ 1 := by
        rw [← hd1_sum]
        exact Finset.single_le_sum
          (fun ν _ => mul_nonneg (N.D_nonneg ν) (hd1.2.1 _ _)) (Finset.mem_univ μ)
      have hd1_le_inv : d1 (N.s μ) (N.t μ) ≤ 1 / N.D μ :=
        (le_div_iff₀ hμ).mpr (by linarith [mul_comm (N.D μ) (d1 (N.s μ) (N.t μ))])
      have h_inv_le_B : 1 / N.D μ ≤ B := by
        dsimp only [B]
        have h_nonneg : ∀ ν ∈ Finset.univ, (0 : ℝ) ≤ (if 0 < N.D ν then 1 / N.D ν else 0) := by
          intro ν _; split_ifs with h; exact div_nonneg zero_le_one h.le; exact le_rfl
        have h_le := Finset.single_le_sum h_nonneg (Finset.mem_univ μ)
        rw [if_pos hμ] at h_le
        linarith
      exact hd1_le_inv.trans h_inv_le_B
    let d' : V → V → ℝ := fun x y => min (d1 x y) B
    refine ⟨d', isPseudometric_min_const hd1 hB_pos.le, fun x y => min_le_right _ _, ?_, ?_⟩
    · rw [← hd1_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rcases (N.D_nonneg μ).lt_or_eq with hμ_pos | hμ_zero
      · dsimp only [d']
        rw [min_eq_left (hd1_le_B μ hμ_pos)]
      · rw [← hμ_zero, zero_mul, zero_mul]
    · have h_rhs : ((1 / 2) * ∑ i, ∑ j, N.C i j * d i j) / D_sum =
          (1 / 2) * ∑ i, ∑ j, N.C i j * d1 i j := by
        dsimp only [d1]
        rw [div_eq_mul_inv, mul_comm _ D_sum⁻¹, ← mul_assoc, mul_comm D_sum⁻¹, mul_assoc,
          Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [h_rhs]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) (N.C_nonneg i j)
  -- Define the compact set `K` of normalized `B`-bounded pseudometrics.
  let K : Set (V → V → ℝ) :=
    {d | IsPseudometric d ∧ (∀ x y, d x y ≤ B) ∧ (∑ μ, N.D μ * d (N.s μ) (N.t μ) = 1)}
  have hK_nonempty : K.Nonempty := by
    obtain ⟨μ0, hD0, hst0⟩ := hN
    let d0 : V → V → ℝ := fun x y => if x = y then 0 else 1
    have hd0 : IsPseudometric d0 := discrete_isPseudometric
    have hD_pos : 0 < ∑ μ, N.D μ * d0 (N.s μ) (N.t μ) := by
      have h_nonneg : ∀ μ ∈ Finset.univ, 0 ≤ N.D μ * d0 (N.s μ) (N.t μ) :=
        fun μ _ => mul_nonneg (N.D_nonneg μ) (hd0.2.1 _ _)
      have h_pos0 : 0 < N.D μ0 * d0 (N.s μ0) (N.t μ0) := by simp [d0, hst0, hD0]
      exact lt_of_lt_of_le h_pos0 (Finset.single_le_sum h_nonneg (Finset.mem_univ μ0))
    obtain ⟨d', hd', hd'B, hd'1, _⟩ := h_norm_trunc d0 hd0 hD_pos
    exact ⟨d', hd', hd'B, hd'1⟩
  have hK_closed : IsClosed K := by
    have h_ev : ∀ x y : V, Continuous (fun d : V → V → ℝ => d x y) :=
      fun x y => (continuous_apply y).comp (continuous_apply x)
    have h1 : IsClosed {d : V → V → ℝ | ∀ x, d x x = 0} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun x => isClosed_eq (h_ev x x) continuous_const
    have h2 : IsClosed {d : V → V → ℝ | ∀ x y, 0 ≤ d x y} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun x => isClosed_iInter fun y =>
        isClosed_le continuous_const (h_ev x y)
    have h3 : IsClosed {d : V → V → ℝ | ∀ x y, d x y = d y x} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun x => isClosed_iInter fun y =>
        isClosed_eq (h_ev x y) (h_ev y x)
    have h4 : IsClosed {d : V → V → ℝ | ∀ x y z, d x z ≤ d x y + d y z} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
        isClosed_le (h_ev x z) ((h_ev x y).add (h_ev y z))
    have h5 : IsClosed {d : V → V → ℝ | ∀ x y, d x y ≤ B} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun x => isClosed_iInter fun y =>
        isClosed_le (h_ev x y) continuous_const
    have h6 : IsClosed {d : V → V → ℝ | ∑ μ, N.D μ * d (N.s μ) (N.t μ) = 1} := by
      refine isClosed_eq ?_ continuous_const
      exact continuous_finsetSum _ fun μ _ =>
        continuous_const.mul (h_ev (N.s μ) (N.t μ))
    have hK_eq : K =
        (({d | ∀ x, d x x = 0} ∩ ({d | ∀ x y, 0 ≤ d x y} ∩
          ({d | ∀ x y, d x y = d y x} ∩ {d | ∀ x y z, d x z ≤ d x y + d y z}))) ∩
          ({d | ∀ x y, d x y ≤ B} ∩ {d | ∑ μ, N.D μ * d (N.s μ) (N.t μ) = 1})) := by
      ext d; rfl
    rw [hK_eq]
    exact ((h1.inter (h2.inter (h3.inter h4))).inter (h5.inter h6))
  have hK_compact : IsCompact K := by
    have hIcc : IsCompact (Set.Icc (0 : V → V → ℝ) (fun _ _ => B)) := isCompact_Icc
    refine hIcc.of_isClosed_subset hK_closed ?_
    rintro d ⟨hd, hdB, _⟩
    exact ⟨fun x y => hd.2.1 x y, fun x y => hdB x y⟩
  let obj : (V → V → ℝ) → ℝ := fun d => (1 / 2) * ∑ i, ∑ j, N.C i j * d i j
  have hobj_cont : Continuous obj := by
    refine continuous_const.mul ?_
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact continuous_const.mul ((continuous_apply j).comp (continuous_apply i))
  obtain ⟨d_star, hd_star_K, hd_star_min⟩ :=
    hK_compact.exists_isMinOn hK_nonempty hobj_cont.continuousOn
  obtain ⟨hd_star_pseudo, _, hd_star_sum⟩ := hd_star_K
  refine ⟨d_star, hd_star_pseudo, by rw [hd_star_sum]; exact zero_lt_one, ?_⟩
  rw [hd_star_sum, mul_one]
  apply le_antisymm
  · have hw := weak_duality_part1 N d_star hd_star_pseudo
    rwa [hd_star_sum, mul_one] at hw
  · -- Show `obj d_star ≤ N.maxflow` by contradiction: if `N.maxflow < obj d_star`,
    -- take `lam = (N.maxflow + obj d_star) / 2 > N.maxflow`.
    by_contra hgt
    push Not at hgt
    let lam : ℝ := (N.maxflow + obj d_star) / 2
    have h_mf_lt_lam : N.maxflow < lam := by dsimp only [lam, obj] at *; linarith
    have h_lam_lt_obj : lam < obj d_star := by dsimp only [lam, obj] at *; linarith
    have h_mf_nonneg : 0 ≤ N.maxflow := maxflow_nonneg N hN
    have h_lam_pos : 0 < lam := lt_of_le_of_lt h_mf_nonneg h_mf_lt_lam
    have h_lam_inf : ¬ ∃ f : Fin N.k → V → V → ℝ, N.IsFeasibleFlow f lam := by
      intro hf
      have h_mem : lam ∈ {l : ℝ | 0 ≤ l ∧ ∃ f : Fin N.k → V → V → ℝ, N.IsFeasibleFlow f l} :=
        ⟨h_lam_pos.le, hf⟩
      have h_le : lam ≤ N.maxflow := le_csSup (bddAbove_feasibleFlow N hN) h_mem
      linarith
    obtain ⟨d_farkas, hd_farkas, hD_farkas_pos, h_farkas_lt⟩ :=
      exists_pseudometric_lt_of_infeasible N lam h_lam_pos h_lam_inf
    obtain ⟨d', hd'_pseudo, hd'_B, hd'_sum, hd'_le⟩ :=
      h_norm_trunc d_farkas hd_farkas hD_farkas_pos
    have hd'_mem : d' ∈ K := ⟨hd'_pseudo, hd'_B, hd'_sum⟩
    have h_star_le_d' : obj d_star ≤ obj d' := hd_star_min hd'_mem
    have h_div_lt_lam :
        ((1 / 2) * ∑ i, ∑ j, N.C i j * d_farkas i j) /
          (∑ μ, N.D μ * d_farkas (N.s μ) (N.t μ)) < lam :=
      (div_lt_iff₀ hD_farkas_pos).mpr h_farkas_lt
    have : obj d' < lam := hd'_le.trans_lt h_div_lt_lam
    linarith
