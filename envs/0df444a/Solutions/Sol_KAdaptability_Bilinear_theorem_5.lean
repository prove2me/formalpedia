-- Prove2me | solution 1 for KAdaptability.Bilinear.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:06:00.283269+00:00
-- url     : https://prove2.me/submissions/26c152cf-78b5-4775-a67c-8090f7f24a33

import Definitions.Def_KAdaptability_Bilinear_Program7


namespace DualityKit

open Matrix

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

-- K0: pointwise duality to joint minimization
theorem isLeast_add_isGreatest_iff {X : Type*} (S : Set X) (g : X → ℝ)
    (W D : X → Set ℝ) (h : ∀ x ∈ S, ∃ w, IsGreatest (W x) w ∧ IsLeast (D x) w) (q : ℝ) :
    IsLeast {v | ∃ x ∈ S, ∃ w, IsGreatest (W x) w ∧ v = g x + w} q ↔
      IsLeast {v | ∃ x ∈ S, ∃ d ∈ D x, v = g x + d} q := by
  have key : ∀ x ∈ S, ∀ w, IsGreatest (W x) w → IsLeast (D x) w := by
    intro x hx w hw
    obtain ⟨w', hw', hd'⟩ := h x hx
    rw [hw.unique hw']
    exact hd'
  constructor
  · rintro ⟨⟨x, hx, w, hw, rfl⟩, hlow⟩
    refine ⟨⟨x, hx, w, (key x hx w hw).1, rfl⟩, ?_⟩
    rintro _ ⟨x', hx', d', hd', rfl⟩
    obtain ⟨w', hw', hdw'⟩ := h x' hx'
    have h1 := hlow ⟨x', hx', w', hw', rfl⟩
    have h2 := hdw'.2 hd'
    linarith
  · rintro ⟨⟨x, hx, d, hd, rfl⟩, hlow⟩
    obtain ⟨w, hw, hdw⟩ := h x hx
    have h1 := hdw.2 hd
    have h2 := hlow ⟨x, hx, w, hdw.1, rfl⟩
    refine ⟨⟨x, hx, w, hw, by linarith⟩, ?_⟩
    rintro _ ⟨x', hx', w', hw', rfl⟩
    exact hlow ⟨x', hx', w', (key x' hx' w' hw').1, rfl⟩

section aux1cone
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {G : Type*} [Fintype G] [DecidableEq G] (u : G → F)

def aux1_coneS (s : Finset G) : Set F :=
  {x | ∃ c : G → ℝ, (∀ k, 0 ≤ c k) ∧ (∀ k ∉ s, c k = 0) ∧ x = ∑ k, c k • u k}

omit [FiniteDimensional ℝ F] [DecidableEq G] in
lemma aux1_sum_sub_eq (s : Finset G) (c : G → ℝ) (hc : ∀ k ∉ s, c k = 0) :
    ∑ k : s, c k • u k = ∑ k, c k • u k := by
  rw [Finset.sum_coe_sort s (fun k => c k • u k)]
  exact Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => by rw [hc k hk, zero_smul])

omit [FiniteDimensional ℝ F] in
lemma aux1_coneS_LI_closed (s : Finset G) (hli : LinearIndependent ℝ (fun k : s => u k)) :
    IsClosed (aux1_coneS u s) := by
  set Λ := Fintype.linearCombination ℝ (fun k : s => u k) with hΛ
  have hker : LinearMap.ker Λ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [hΛ, Fintype.linearCombination_apply] at hc
    funext k
    exact Fintype.linearIndependent_iff.1 hli c hc k
  have heq : aux1_coneS u s = Λ '' {c | ∀ k, 0 ≤ c k} := by
    ext x
    constructor
    · rintro ⟨c, hc0, hcs, rfl⟩
      refine ⟨fun k => c k, fun k => hc0 k, ?_⟩
      rw [hΛ, Fintype.linearCombination_apply]
      exact aux1_sum_sub_eq u s c hcs
    · rintro ⟨c, hc0, rfl⟩
      refine ⟨fun k => if h : k ∈ s then c ⟨k, h⟩ else 0, fun k => ?_, fun k hk => ?_, ?_⟩
      · by_cases h : k ∈ s
        · simp only [h, dif_pos]; exact hc0 _
        · simp [h]
      · simp [hk]
      · rw [hΛ, Fintype.linearCombination_apply,
          ← aux1_sum_sub_eq u s _ (fun k hk => by simp [hk])]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp
  have hQ : {c : s → ℝ | ∀ k, 0 ≤ c k} = ⋂ k, {c : s → ℝ | 0 ≤ c k} := by ext; simp
  rw [heq, hQ]
  exact (LinearMap.isClosedEmbedding_of_injective hker).isClosedMap _
    (isClosed_iInter fun k => isClosed_le continuous_const (continuous_apply k))

omit [FiniteDimensional ℝ F] in
lemma aux1_cara_step (s : Finset G) (hdep : ¬ LinearIndependent ℝ (fun k : s => u k)) :
    aux1_coneS u s ⊆ ⋃ k ∈ s, aux1_coneS u (s.erase k) := by
  rintro x ⟨c, hc0, hcs, rfl⟩
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg, i, hi⟩ := hdep
  set a0 : G → ℝ := fun k => if h : k ∈ s then g ⟨k, h⟩ else 0 with ha0
  have ha0s : ∀ k ∉ s, a0 k = 0 := fun k hk => by simp [ha0, hk]
  have ha0sum : ∑ k, a0 k • u k = 0 := by
    rw [← aux1_sum_sub_eq u s a0 ha0s, ← hg]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [ha0]
  have ha0i : a0 i ≠ 0 := by simpa [ha0] using hi
  obtain ⟨a, has, hasum, k1, hk1⟩ : ∃ a : G → ℝ, (∀ k ∉ s, a k = 0) ∧ ∑ k, a k • u k = 0 ∧
      ∃ k1, 0 < a k1 := by
    rcases lt_or_gt_of_ne ha0i with h | h
    · refine ⟨-a0, fun k hk => by simp [ha0s k hk], ?_, i, by simp; linarith⟩
      simp [neg_smul, Finset.sum_neg_distrib, ha0sum]
    · exact ⟨a0, ha0s, ha0sum, i, h⟩
  have hk1s : k1 ∈ s := by by_contra h; rw [has k1 h] at hk1; exact lt_irrefl _ hk1
  set P := s.filter (fun k => 0 < a k) with hP
  have hPne : P.Nonempty := ⟨k1, Finset.mem_filter.2 ⟨hk1s, hk1⟩⟩
  obtain ⟨k0, hk0P, hmin⟩ := Finset.exists_min_image P (fun k => c k / a k) hPne
  have hk0 := Finset.mem_filter.1 hk0P
  set t := c k0 / a k0 with ht
  have ht0 : 0 ≤ t := div_nonneg (hc0 k0) hk0.2.le
  refine Set.mem_biUnion hk0.1 ⟨fun k => c k - t * a k, fun k => ?_, fun k hk => ?_, ?_⟩
  · by_cases hak : 0 < a k
    · by_cases hks : k ∈ s
      · have := hmin k (Finset.mem_filter.2 ⟨hks, hak⟩)
        rw [div_le_div_iff₀ hk0.2 hak] at this
        have : t * a k ≤ c k := by
          rw [ht, div_mul_eq_mul_div, div_le_iff₀ hk0.2]; linarith
        linarith
      · rw [has k hks] at hak; exact absurd hak (lt_irrefl _)
    · push Not at hak
      nlinarith [hc0 k]
  · rcases Finset.mem_erase.not.1 hk |> not_and_or.1 with h | h
    · push Not at h; subst h
      show c k - t * a k = 0
      rw [ht, div_mul_cancel₀ _ hk0.2.ne', sub_self]
    · show c k - t * a k = 0
      rw [hcs k h, has k h]; ring
  · simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hasum, smul_zero,
      sub_zero]

lemma aux1_coneS_closed : ∀ s : Finset G, IsClosed (aux1_coneS u s) := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hli : LinearIndependent ℝ (fun k : s => u k)
    · exact aux1_coneS_LI_closed u s hli
    · have heq : aux1_coneS u s = ⋃ k ∈ s, aux1_coneS u (s.erase k) := by
        refine Set.Subset.antisymm (aux1_cara_step u s hli) ?_
        refine Set.iUnion₂_subset fun k _ => ?_
        rintro x ⟨c, hc0, hcs, rfl⟩
        exact ⟨c, hc0, fun j hj => hcs j (fun h => hj (Finset.mem_of_mem_erase h)), rfl⟩
      rw [heq]
      exact isClosed_biUnion_finset fun k hk => ih _ (Finset.erase_ssubset hk)

end aux1cone

-- K1: closedness of finitely generated cones
/-- Finitely generated cones are closed (the missing Mathlib fact). -/
theorem isClosed_finite_cone {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (u : κ → F) :
    IsClosed {w | ∃ c : κ → ℝ, 0 ≤ c ∧ w = ∑ k, c k • u k} := by
  classical
  have h := aux1_coneS_closed u Finset.univ
  convert h using 1
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, hc, fun k hk => absurd (Finset.mem_univ k) hk, rfl⟩
  · rintro ⟨c, hc, -, rfl⟩; exact ⟨c, hc, rfl⟩


lemma aux1_linear_pi {α : Type*} [Fintype α] [DecidableEq α] (L : (α → ℝ) →ₗ[ℝ] ℝ) (p : α → ℝ) :
    L p = ∑ i, p i * L (Pi.single i 1) := by
  rw [LinearMap.pi_apply_eq_sum_univ L p]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

lemma aux1_prod_decomp {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (L : (α → ℝ) × (β → ℝ) →ₗ[ℝ] ℝ) (p : α → ℝ) (q : β → ℝ) :
    L (p, q) = ∑ i, p i * L (Pi.single i 1, 0) + ∑ j, q j * L (0, Pi.single j 1) := by
  have h1 : L (p, q) = (L ∘ₗ LinearMap.inl ℝ _ _) p + (L ∘ₗ LinearMap.inr ℝ _ _) q := by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
      ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  rw [h1, aux1_linear_pi, aux1_linear_pi]
  rfl

-- K1: Farkas alternative
/-- Farkas, mixed inequality/equality system, functional form. -/
theorem LP.farkas (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ) :
    (¬ ∃ x : E, (∀ i, a i x ≤ b i) ∧ ∀ j, e j x = d j) ↔
      ∃ (y : ι → ℝ) (z : κ → ℝ), 0 ≤ y ∧
        ∑ i, y i • a i + ∑ j, z j • e j = 0 ∧ y ⬝ᵥ b + z ⬝ᵥ d < 0 := by
  classical
  constructor
  · intro hno
    set bas := Module.finBasis ℝ E
    let M : E →ₗ[ℝ] (ι → ℝ) × (κ → ℝ) := (LinearMap.pi a).prod (LinearMap.pi e)
    have hMx : ∀ x, M x = (fun i => a i x, fun j => e j x) := fun x => rfl
    let u : ι ⊕ (Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ E)) → (ι → ℝ) × (κ → ℝ) :=
      fun g => match g with
        | Sum.inl i => (Pi.single i 1, 0)
        | Sum.inr (Sum.inl k) => M (bas k)
        | Sum.inr (Sum.inr k) => -M (bas k)
    set S := {w | ∃ c : ι ⊕ (Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ E)) → ℝ,
      0 ≤ c ∧ w = ∑ g, c g • u g} with hS
    have hcl : IsClosed S := isClosed_finite_cone u
    have hcv : Convex ℝ S := by
      rintro w1 ⟨c1, h1, rfl⟩ w2 ⟨c2, h2, rfl⟩ s t hs ht _
      refine ⟨s • c1 + t • c2, fun g => ?_, ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        exact add_nonneg (mul_nonneg hs (h1 g)) (mul_nonneg ht (h2 g))
      · simp [add_smul, mul_smul, Finset.smul_sum, Finset.sum_add_distrib]
    have hzero : (0 : (ι → ℝ) × (κ → ℝ)) ∈ S := ⟨0, le_rfl, by simp⟩
    have hsmul : ∀ w ∈ S, ∀ t : ℝ, 0 ≤ t → t • w ∈ S := by
      rintro w ⟨c, hc, rfl⟩ t ht
      refine ⟨t • c, fun g => ?_, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; exact mul_nonneg ht (hc g)
      · simp [Finset.smul_sum, mul_smul]
    have hgen : ∀ g, u g ∈ S := by
      intro g
      refine ⟨Pi.single g 1, fun h => ?_, ?_⟩
      · by_cases hh : h = g
        · subst hh; simp
        · simp [Pi.single_apply, hh]
      · rw [Finset.sum_eq_single g (fun h _ hh => by simp [Pi.single_apply, hh])
          (fun h => absurd (Finset.mem_univ g) h)]
        simp
    have hM : ∀ x, M x ∈ S := by
      intro x
      refine ⟨fun g => match g with
        | Sum.inl _ => 0
        | Sum.inr (Sum.inl k) => (bas.repr x k)⁺
        | Sum.inr (Sum.inr k) => (bas.repr x k)⁻, fun g => ?_, ?_⟩
      · rcases g with i | k | k
        · exact le_rfl
        · exact posPart_nonneg _
        · exact negPart_nonneg _
      · symm
        rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
        simp only [u, zero_smul, Finset.sum_const_zero, zero_add, smul_neg]
        rw [Finset.sum_neg_distrib, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
        simp_rw [← sub_smul, posPart_sub_negPart, ← map_smul]
        rw [← map_sum, bas.sum_repr]
    have hnot : (b, d) ∉ S := by
      rintro ⟨c, hc, hbd⟩
      set x := ∑ k, (c (Sum.inr (Sum.inl k)) - c (Sum.inr (Sum.inr k))) • bas k with hx
      have hsum : ∑ g, c g • u g = (fun i => c (Sum.inl i), 0) + M x := by
        rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
        simp only [u, smul_neg]
        rw [Finset.sum_neg_distrib, ← sub_eq_add_neg]
        have hMx' : M x = ∑ k, c (Sum.inr (Sum.inl k)) • M (bas k) -
            ∑ k, c (Sum.inr (Sum.inr k)) • M (bas k) := by
          rw [hx]
          simp only [sub_smul, Finset.sum_sub_distrib, map_sub, map_sum, map_smul]
        rw [hMx']
        congr 1
        ext i
        · rw [Prod.fst_sum, Finset.sum_apply]; simp [Pi.single_apply]
        · rw [Prod.snd_sum]; simp
      rw [hsum] at hbd
      apply hno
      refine ⟨x, fun i => ?_, fun j => ?_⟩
      · have := congrFun (congrArg Prod.fst hbd) i
        rw [hMx] at this
        simp only [Prod.fst_add, Pi.add_apply] at this
        have h0 : (0:ℝ) ≤ c (Sum.inl i) := hc (Sum.inl i)
        linarith
      · have := congrFun (congrArg Prod.snd hbd) j
        rw [hMx] at this
        simp only [Prod.snd_add, Pi.add_apply, Prod.snd_zero, Pi.zero_apply, zero_add] at this
        exact this.symm
    obtain ⟨Fl, s, hFw, hFb⟩ := geometric_hahn_banach_point_closed hcv hcl hnot
    have hs0 : s < 0 := by simpa using hFb 0 hzero
    have hFnn : ∀ w ∈ S, 0 ≤ Fl w := by
      intro w hw
      by_contra hneg
      push Not at hneg
      have hmem := hsmul w hw (s / Fl w) (div_nonneg_of_nonpos hs0.le hneg.le)
      have := hFb _ hmem
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
      exact lt_irrefl _ this
    have hFM : ∀ x, Fl (M x) = 0 := by
      intro x
      have h1 := hFnn _ (hM x)
      have h2 := hFnn _ (hM (-x))
      rw [map_neg, map_neg] at h2
      linarith
    have hdec := aux1_prod_decomp (Fl : (ι → ℝ) × (κ → ℝ) →L[ℝ] ℝ).toLinearMap
    refine ⟨fun i => Fl (Pi.single i 1, 0), fun j => Fl (0, Pi.single j 1),
      fun i => hFnn _ (hgen (Sum.inl i)), ?_, ?_⟩
    · ext x
      have := hFM x
      rw [hMx] at this
      have h2 := hdec (fun i => a i x) (fun j => e j x)
      simp only [ContinuousLinearMap.coe_coe] at h2
      rw [this] at h2
      simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, LinearMap.zero_apply]
      rw [h2]
      congr 1 <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    · have h2 := hdec b d
      simp only [ContinuousLinearMap.coe_coe] at h2
      have : Fl (b, d) < 0 := hFw.trans hs0
      rw [h2] at this
      simp only [dotProduct]
      convert this using 2 <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · rintro ⟨y, z, hy, hsum, hneg⟩ ⟨x, hax, hex⟩
    have h := congrArg (fun φ : Module.Dual ℝ E => φ x) hsum
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, LinearMap.zero_apply, hex] at h
    have hle : ∑ i, y i * a i x ≤ ∑ i, y i * b i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hax i) (hy i)
    simp only [dotProduct] at hneg
    linarith


-- K2: primal feasible set
/-- Primal: maximize `c x` subject to `a i x ≤ b i`, `e j x = d j` (`x` free in `E`). -/
def LP.Feas (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ) : Set E :=
  {x | (∀ i, a i x ≤ b i) ∧ ∀ j, e j x = d j}

-- K2: dual feasible set
/-- Dual: `y ≥ 0`, `z` free, `Σ yᵢ aᵢ + Σ zⱼ eⱼ = c`; objective `y ⬝ᵥ b + z ⬝ᵥ d` (minimize). -/
def LP.DualFeas (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) (c : Module.Dual ℝ E) :
    Set ((ι → ℝ) × (κ → ℝ)) :=
  {yz | 0 ≤ yz.1 ∧ ∑ i, yz.1 i • a i + ∑ j, yz.2 j • e j = c}

-- K2: weak duality
theorem LP.weak_duality
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) {x : E} (hx : x ∈ LP.Feas a b e d)
    {yz : (ι → ℝ) × (κ → ℝ)} (hyz : yz ∈ LP.DualFeas a e c) :
    c x ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d := by
  obtain ⟨hax, hex⟩ := hx
  obtain ⟨hy, hsum⟩ := hyz
  have h := congrArg (fun φ : Module.Dual ℝ E => φ x) hsum
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    hex] at h
  have hle : ∑ i, yz.1 i * a i x ≤ ∑ i, yz.1 i * b i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hax i) (hy i)
  simp only [dotProduct]
  linarith

lemma aux1_alt (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) (hP : (LP.Feas a b e d).Nonempty) (t : ℝ)
    (h : ∀ x ∈ LP.Feas a b e d, c x < t) :
    ∃ yz ∈ LP.DualFeas a e c, yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d < t := by
  classical
  let a' : Option ι → Module.Dual ℝ E := fun o => o.elim (-c) a
  let b' : Option ι → ℝ := fun o => o.elim (-t) b
  have hinf : ¬ ∃ x : E, (∀ i, a' i x ≤ b' i) ∧ ∀ j, e j x = d j := by
    rintro ⟨x, hx1, hx2⟩
    have h1 := h x ⟨fun i => hx1 (some i), hx2⟩
    have h2 := hx1 none
    simp only [a', b', Option.elim, LinearMap.neg_apply] at h2
    linarith
  obtain ⟨y', z, hy', hsum, hneg⟩ := (LP.farkas a' b' e d).1 hinf
  rw [Fintype.sum_option] at hsum
  simp only [dotProduct, Fintype.sum_option] at hneg
  simp only [a', b', Option.elim, smul_neg] at hsum hneg
  have hy0 : 0 ≤ y' none := hy' none
  rcases hy0.eq_or_lt with h0 | h0
  · exfalso
    obtain ⟨x0, hx0⟩ := hP
    refine (LP.farkas a b e d).2 ⟨fun i => y' (some i), z, fun i => hy' (some i), ?_, ?_⟩
      ⟨x0, hx0⟩
    · rw [← h0] at hsum; simpa using hsum
    · simp only [dotProduct]; rw [← h0] at hneg; simpa using hneg
  · refine ⟨(fun i => y' (some i) / y' none, fun j => z j / y' none),
      ⟨fun i => div_nonneg (hy' _) h0.le, ?_⟩, ?_⟩
    · have hAB : ∑ i, y' (some i) • a i + ∑ j, z j • e j = y' none • c := by
        rw [← sub_eq_zero, ← hsum]; abel
      show ∑ i, (y' (some i) / y' none) • a i + ∑ j, (z j / y' none) • e j = c
      have hr : ∀ (r : ℝ) (φ : Module.Dual ℝ E), (r / y' none) • φ = (y' none)⁻¹ • (r • φ) :=
        fun r φ => by rw [smul_smul, div_eq_inv_mul]
      simp only [hr]
      rw [← Finset.smul_sum, ← Finset.smul_sum, ← smul_add, hAB, smul_smul,
        inv_mul_cancel₀ h0.ne', one_smul]
    · simp only [dotProduct]
      have : ∑ i, y' (some i) / y' none * b i + ∑ j, z j / y' none * d j =
          (∑ i, y' (some i) * b i + ∑ j, z j * d j) / y' none := by
        rw [add_div, Finset.sum_div, Finset.sum_div]
        congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
      rw [this, div_lt_iff₀ h0]
      linarith

lemma aux1_attain (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E) (hP : (LP.Feas a b e d).Nonempty)
    (hb : BddAbove (c '' LP.Feas a b e d)) :
    ∃ x ∈ LP.Feas a b e d, ∀ x' ∈ LP.Feas a b e d, c x' ≤ c x := by
  by_contra hno
  push Not at hno
  have hlt : ∀ x ∈ LP.Feas a b e d, c x < sSup (c '' LP.Feas a b e d) := fun x hx => by
    obtain ⟨x', hx', hlt⟩ := hno x hx
    exact lt_of_lt_of_le hlt (le_csSup hb ⟨x', hx', rfl⟩)
  obtain ⟨yz, hyz, hobj⟩ := aux1_alt a b e d c hP _ hlt
  have : sSup (c '' LP.Feas a b e d) ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d :=
    csSup_le (hP.image c) (by rintro _ ⟨x, hx, rfl⟩; exact LP.weak_duality a b e d c hx hyz)
  linarith


/-- The dual constraint map `(y, z) ↦ Σ yᵢ aᵢ + Σ zⱼ eⱼ`. -/
def aux1_T (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) :
    (ι → ℝ) × (κ → ℝ) →ₗ[ℝ] Module.Dual ℝ E where
  toFun yz := ∑ i, yz.1 i • a i + ∑ j, yz.2 j • e j
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' t p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
      ← Finset.smul_sum, smul_add, RingHom.id_apply]

/-- The dual objective `(y, z) ↦ y ⬝ᵥ b + z ⬝ᵥ d`. -/
def aux1_obj (b : ι → ℝ) (d : κ → ℝ) : Module.Dual ℝ ((ι → ℝ) × (κ → ℝ)) where
  toFun yz := yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, add_dotProduct]; ring
  map_smul' t p := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, smul_eq_mul, RingHom.id_apply]; ring

lemma aux1_dualFeas_eq (a : ι → Module.Dual ℝ E) (e : κ → Module.Dual ℝ E) (c : Module.Dual ℝ E) :
    LP.DualFeas a e c =
      LP.Feas (fun i => -(LinearMap.proj i ∘ₗ LinearMap.fst ℝ (ι → ℝ) (κ → ℝ))) 0
        (fun k => Module.Dual.eval ℝ E (Module.finBasis ℝ E k) ∘ₗ aux1_T a e)
        (fun k => c (Module.finBasis ℝ E k)) := by
  ext yz
  simp only [LP.DualFeas, LP.Feas, Set.mem_setOf_eq, LinearMap.neg_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.coe_fst, LinearMap.coe_proj, Function.eval, Pi.zero_apply,
    neg_nonpos, Module.Dual.eval_apply]
  constructor
  · rintro ⟨hy, hsum⟩
    exact ⟨fun i => hy i, fun k => by rw [← hsum]; rfl⟩
  · rintro ⟨hy, hk⟩
    refine ⟨fun i => hy i, ?_⟩
    have : aux1_T a e yz = c := (Module.finBasis ℝ E).ext fun k => hk k
    exact this

lemma aux1_dual_attain (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E)
    (d : κ → ℝ) (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty) (hD : (LP.DualFeas a e c).Nonempty) :
    ∃ yz ∈ LP.DualFeas a e c, ∀ yz' ∈ LP.DualFeas a e c,
      yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d ≤ yz'.1 ⬝ᵥ b + yz'.2 ⬝ᵥ d := by
  obtain ⟨x0, hx0⟩ := hP
  rw [aux1_dualFeas_eq] at hD ⊢
  obtain ⟨yz, hyz, hmax⟩ := aux1_attain _ _ _ _ (-aux1_obj b d) hD (by
    refine ⟨-c x0, ?_⟩
    rintro _ ⟨yz', hyz', rfl⟩
    rw [← aux1_dualFeas_eq] at hyz'
    have := LP.weak_duality a b e d c hx0 hyz'
    simp only [LinearMap.neg_apply, neg_le_neg_iff]
    exact this)
  refine ⟨yz, hyz, fun yz' hyz' => ?_⟩
  have := hmax yz' hyz'
  simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
  exact this

-- K2: strong duality with attainment
/-- Both feasible ⇒ both optima attained and equal. (No constraint qualification needed.) -/
theorem LP.strong_duality
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty) (hD : (LP.DualFeas a e c).Nonempty) :
    ∃ v : ℝ, IsGreatest (c '' LP.Feas a b e d) v ∧
      IsLeast ((fun yz => yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d) '' LP.DualFeas a e c) v := by
  obtain ⟨yz, hyz, hmin⟩ := aux1_dual_attain a b e d c hP hD
  obtain ⟨x, hx, hxw⟩ : ∃ x ∈ LP.Feas a b e d, yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d ≤ c x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨yz', hyz', hlt⟩ := aux1_alt a b e d c hP _ hcon
    linarith [hmin yz' hyz']
  refine ⟨yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d,
    ⟨⟨x, hx, le_antisymm (LP.weak_duality a b e d c hx hyz) hxw⟩, ?_⟩,
    ⟨⟨yz, hyz, rfl⟩, ?_⟩⟩
  · rintro _ ⟨x', hx', rfl⟩; exact LP.weak_duality a b e d c hx' hyz
  · rintro _ ⟨yz', hyz', rfl⟩; exact hmin yz' hyz'

-- K2: bounded primal gives dual feasibility
/-- Primal feasible and bounded ⇒ dual feasible. -/
theorem LP.dualFeas_nonempty_of_bddAbove
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E)
    (hP : (LP.Feas a b e d).Nonempty)
    (hb : BddAbove (c '' LP.Feas a b e d)) : (LP.DualFeas a e c).Nonempty := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨yz, hyz, -⟩ := aux1_alt a b e d c hP (M + 1) fun x hx => by
    have := hM ⟨x, hx, rfl⟩
    linarith
  exact ⟨yz, hyz⟩

-- K2: infeasible primal gives unbounded dual
/-- Primal infeasible, dual feasible ⇒ dual unbounded below. -/
theorem LP.not_bddBelow_dual_of_infeasible
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E)
    (hP : LP.Feas a b e d = ∅)
    (hD : (LP.DualFeas a e c).Nonempty) :
    ¬ BddBelow ((fun yz => yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d) '' LP.DualFeas a e c) := by
  rintro ⟨L, hL⟩
  obtain ⟨y0, z0, hy0, hsum0, hneg0⟩ := (LP.farkas a b e d).1 (by
    rintro ⟨x, hx⟩
    have : x ∈ LP.Feas a b e d := hx
    rw [hP] at this
    exact this)
  obtain ⟨yz, hy, hsum⟩ := hD
  have hLle : L ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d := hL ⟨yz, ⟨hy, hsum⟩, rfl⟩
  set g := y0 ⬝ᵥ b + z0 ⬝ᵥ d with hg
  set t := (yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d - L + 1) / (-g) with ht
  have hgpos : 0 < -g := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hgpos.le
  have htg : t * g = -(yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d - L + 1) := by
    rw [ht, div_mul_eq_mul_div, div_eq_iff hgpos.ne']; ring
  have hmem : (yz.1 + t • y0, yz.2 + t • z0) ∈ LP.DualFeas a e c := by
    refine ⟨fun i => ?_, ?_⟩
    · have h1 : (0:ℝ) ≤ yz.1 i := hy i
      have h2 : (0:ℝ) ≤ y0 i := hy0 i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      positivity
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
        Finset.sum_add_distrib, ← Finset.smul_sum]
      calc _ = (∑ i, yz.1 i • a i + ∑ j, yz.2 j • e j) +
            t • (∑ i, y0 i • a i + ∑ j, z0 j • e j) := by rw [smul_add]; abel
        _ = c := by rw [hsum, hsum0, smul_zero, add_zero]
  have := hL ⟨_, hmem, rfl⟩
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at this
  have : L ≤ yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d + t * g := by rw [hg]; linarith
  linarith

-- K2: EReal value form
/-- EReal value form: equal unless both sides are infeasible (then `⊥ ≠ ⊤`). -/
theorem LP.ereal_duality
    (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (e : κ → Module.Dual ℝ E) (d : κ → ℝ)
    (c : Module.Dual ℝ E)
    (h : (LP.Feas a b e d).Nonempty ∨ (LP.DualFeas a e c).Nonempty) :
    ⨆ x ∈ LP.Feas a b e d, ((c x : ℝ) : EReal) =
      ⨅ yz ∈ LP.DualFeas a e c, ((yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d : ℝ) : EReal) := by
  by_cases hP : (LP.Feas a b e d).Nonempty <;> by_cases hD : (LP.DualFeas a e c).Nonempty
  · obtain ⟨v, ⟨⟨x, hx, hxv⟩, hvub⟩, ⟨⟨yz, hyz, hyzv⟩, hvlb⟩⟩ :=
      LP.strong_duality a b e d c hP hD
    have hL : ⨆ x ∈ LP.Feas a b e d, ((c x : ℝ) : EReal) = (v : EReal) := by
      refine le_antisymm (iSup₂_le fun x' hx' => EReal.coe_le_coe_iff.2 (hvub ⟨x', hx', rfl⟩)) ?_
      exact le_iSup₂_of_le x hx (by rw [hxv])
    have hR : ⨅ yz ∈ LP.DualFeas a e c, ((yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d : ℝ) : EReal) = (v : EReal) := by
      refine le_antisymm ?_ (le_iInf₂ fun yz' hyz' => EReal.coe_le_coe_iff.2
        (hvlb ⟨yz', hyz', rfl⟩))
      exact iInf₂_le_of_le yz hyz (by rw [← hyzv])
    rw [hL, hR]
  · have hR : ⨅ yz ∈ LP.DualFeas a e c, ((yz.1 ⬝ᵥ b + yz.2 ⬝ᵥ d : ℝ) : EReal) = ⊤ := by
      refine iInf₂_eq_top.2 fun yz hyz => absurd ⟨yz, hyz⟩ hD
    rw [hR, EReal.eq_top_iff_forall_lt]
    intro r
    have hnb : ¬ BddAbove (c '' LP.Feas a b e d) := fun hb =>
      hD (LP.dualFeas_nonempty_of_bddAbove a b e d c hP hb)
    rw [not_bddAbove_iff] at hnb
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := hnb r
    exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hlt) (le_iSup₂_of_le x hx le_rfl)
  · have hL : ⨆ x ∈ LP.Feas a b e d, ((c x : ℝ) : EReal) = ⊥ := by
      refine iSup₂_eq_bot.2 fun x hx => absurd ⟨x, hx⟩ hP
    rw [hL, eq_comm, EReal.eq_bot_iff_forall_lt]
    intro r
    have hnb := LP.not_bddBelow_dual_of_infeasible a b e d c
      (Set.not_nonempty_iff_eq_empty.1 hP) hD
    rw [not_bddBelow_iff] at hnb
    obtain ⟨_, ⟨yz, hyz, rfl⟩, hlt⟩ := hnb r
    exact lt_of_le_of_lt (iInf₂_le_of_le yz hyz le_rfl) (EReal.coe_lt_coe_iff.2 hlt)
  · exact absurd h (by tauto)


/-- The functional `v ↦ u ⬝ᵥ v`. -/
def aux1_dotL {n : Type*} [Fintype n] (u : n → ℝ) : Module.Dual ℝ (n → ℝ) where
  toFun v := u ⬝ᵥ v
  map_add' v w := dotProduct_add u v w
  map_smul' t v := by simp [dotProduct_smul]

lemma aux1_dotL_apply {n : Type*} [Fintype n] (u v : n → ℝ) : aux1_dotL u v = u ⬝ᵥ v := rfl

lemma aux1_dotL_inj {n : Type*} [Fintype n] {u w : n → ℝ} (h : aux1_dotL u = aux1_dotL w) :
    u = w := by
  classical
  funext j
  have := congrArg (fun φ : Module.Dual ℝ (n → ℝ) => φ (Pi.single j 1)) h
  simpa [aux1_dotL_apply, dotProduct_single] using this

lemma aux1_sum_dotL {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (y : m → ℝ) :
    ∑ i, y i • aux1_dotL (A i) = aux1_dotL (Aᵀ *ᵥ y) := by
  ext v
  rw [LinearMap.sum_apply, aux1_dotL_apply, mulVec_transpose, ← dotProduct_mulVec]
  simp only [LinearMap.smul_apply, smul_eq_mul, aux1_dotL_apply, dotProduct]
  rfl

lemma aux1_matFeas {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (b : m → ℝ)
    (x : n → ℝ) :
    x ∈ LP.Feas (fun i => aux1_dotL (A i)) b (fun j : Empty => j.elim) (fun j => j.elim) ↔
      A *ᵥ x ≤ b :=
  ⟨fun h i => h.1 i, fun h => ⟨fun i => h i, fun j => j.elim⟩⟩

lemma aux1_matDual {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (c : n → ℝ)
    (yz : (m → ℝ) × (Empty → ℝ)) :
    yz ∈ LP.DualFeas (fun i => aux1_dotL (A i)) (fun j : Empty => j.elim) (aux1_dotL c) ↔
      0 ≤ yz.1 ∧ Aᵀ *ᵥ yz.1 = c := by
  simp only [LP.DualFeas, Set.mem_setOf_eq, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    aux1_sum_dotL]
  exact and_congr Iff.rfl ⟨aux1_dotL_inj, fun h => by rw [h]⟩

-- K2 (matrix corollary): strong duality for `max c⬝x, A x ≤ b`
theorem LP.strong_duality_matrix {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ)
    (hP : ∃ x, A *ᵥ x ≤ b) (hD : ∃ y, 0 ≤ y ∧ Aᵀ *ᵥ y = c) :
    ∃ x y, A *ᵥ x ≤ b ∧ 0 ≤ y ∧ Aᵀ *ᵥ y = c ∧ c ⬝ᵥ x = b ⬝ᵥ y ∧
      (∀ x', A *ᵥ x' ≤ b → c ⬝ᵥ x' ≤ c ⬝ᵥ x) := by
  obtain ⟨x0, hx0⟩ := hP
  obtain ⟨y0, hy0, hy0c⟩ := hD
  obtain ⟨v, ⟨⟨x, hx, hxv⟩, hub⟩, ⟨⟨yz, hyz, hyzv⟩, -⟩⟩ :=
    LP.strong_duality (fun i => aux1_dotL (A i)) b (fun j : Empty => j.elim) (fun j => j.elim)
      (aux1_dotL c) ⟨x0, (aux1_matFeas A b x0).2 hx0⟩
      ⟨(y0, fun j => j.elim), (aux1_matDual A c _).2 ⟨hy0, hy0c⟩⟩
  obtain ⟨hy, hyc⟩ := (aux1_matDual A c yz).1 hyz
  refine ⟨x, yz.1, (aux1_matFeas A b x).1 hx, hy, hyc, ?_, fun x' hx' => ?_⟩
  · rw [aux1_dotL_apply] at hxv
    have h0 : yz.2 ⬝ᵥ (fun j : Empty => j.elim) = 0 := by simp [dotProduct]
    simp only [h0, add_zero] at hyzv
    rw [hxv, ← hyzv, dotProduct_comm]
  · have := hub ⟨x', (aux1_matFeas A b x').2 hx', rfl⟩
    rw [← hxv] at this
    exact this

-- K2 (matrix corollary): bounded polyhedron gives dual feasibility
/-- A nonempty bounded polyhedron has a feasible dual for every cost. -/
theorem LP.exists_dual_of_isBounded {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (hne : {x | A *ᵥ x ≤ b}.Nonempty)
    (hbd : Bornology.IsBounded {x | A *ᵥ x ≤ b}) (c : n → ℝ) :
    ∃ y, 0 ≤ y ∧ Aᵀ *ᵥ y = c := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hbd
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨yz, hyz⟩ := LP.dualFeas_nonempty_of_bddAbove (fun i => aux1_dotL (A i)) b
    (fun j : Empty => j.elim) (fun j => j.elim) (aux1_dotL c)
    ⟨x0, (aux1_matFeas A b x0).2 hx0⟩ (by
      refine ⟨∑ i, |c i| * R, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      have hxR := hR x ((aux1_matFeas A b x).1 hx)
      rw [aux1_dotL_apply, dotProduct]
      refine Finset.sum_le_sum fun i _ => ?_
      calc c i * x i ≤ |c i * x i| := le_abs_self _
        _ = |c i| * |x i| := abs_mul _ _
        _ ≤ |c i| * R := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have := norm_le_pi_norm x i
          rw [Real.norm_eq_abs] at this
          linarith)
  exact ⟨yz.1, (aux1_matDual A c yz).1 hyz⟩

-- K2-aux: functionals on `n → ℝ` are dot products
theorem Module.Dual.exists_dotProduct_eq {n : Type*} [Fintype n] [DecidableEq n]
    (φ : Module.Dual ℝ (n → ℝ)) : ∃ u : n → ℝ, ∀ v, φ v = u ⬝ᵥ v := by
  refine ⟨fun i => φ (Pi.single i 1), fun v => ?_⟩
  rw [aux1_linear_pi φ v, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

-- K2-aux: functionals on matrices are trace pairings
theorem Module.Dual.exists_trace_eq {n : Type*} [Fintype n] [DecidableEq n]
    (φ : Module.Dual ℝ (Matrix n n ℝ)) : ∃ Y : Matrix n n ℝ, ∀ A, φ A = (Yᵀ * A).trace := by
  refine ⟨Matrix.of fun i j => φ (Matrix.single i j 1), fun A => ?_⟩
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  have hs : ∀ i j, Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℝ) := by
    intro i j; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  simp only [map_sum, hs, map_smul, smul_eq_mul, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.of_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

end DualityKit


open Matrix

namespace RRAux_KAdaptability_Bilinear_theorem_5

/-- dot-product functional -/
def dl {n : Type*} [Fintype n] (u : n → ℝ) : Module.Dual ℝ (n → ℝ) where
  toFun ξ := u ⬝ᵥ ξ
  map_add' a b := dotProduct_add u a b
  map_smul' c a := by simp [dotProduct_smul]

theorem dl_apply {n : Type*} [Fintype n] (u ξ : n → ℝ) : dl u ξ = u ⬝ᵥ ξ := rfl

theorem farkas_mat {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (b : m → ℝ) (h : ¬ ∃ x, M *ᵥ x ≤ b) :
    ∃ y, 0 ≤ y ∧ Mᵀ *ᵥ y = 0 ∧ b ⬝ᵥ y < 0 := by
  have h' : ¬ ∃ x : n → ℝ, (∀ i, dl (M i) x ≤ b i) ∧
      ∀ j : Empty, (0 : Module.Dual ℝ (n → ℝ)) x = (0 : Empty → ℝ) j := by
    rintro ⟨x, hx, -⟩
    exact h ⟨x, fun i => by simpa [dl_apply, mulVec] using hx i⟩
  obtain ⟨y, z, hy, hsum, hneg⟩ := (DualityKit.LP.farkas (fun i => dl (M i)) b
    (fun _ : Empty => (0 : Module.Dual ℝ (n → ℝ))) (fun _ => 0)).1 h'
  refine ⟨y, hy, ?_, ?_⟩
  · funext j
    have := LinearMap.congr_fun hsum (Pi.single j 1)
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, LinearMap.sum_apply,
      LinearMap.smul_apply, dl_apply, LinearMap.zero_apply] at this
    simp only [mulVec, dotProduct, transpose_apply, Pi.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [dotProduct_single, mul_comm]
  · simpa [dotProduct_comm] using hneg

theorem weak_mat {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) (b : m → ℝ) (c x : n → ℝ) (y : m → ℝ) (hx : M *ᵥ x ≤ b)
    (hy : 0 ≤ y) (hc : Mᵀ *ᵥ y = c) : c ⬝ᵥ x ≤ b ⬝ᵥ y := by
  rw [← hc, mulVec_transpose, ← dotProduct_mulVec, dotProduct_comm b]
  exact dotProduct_le_dotProduct_of_nonneg_left hx hy

theorem dual_le_of_bound {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (τ : ℝ)
    (hD : ∃ y, 0 ≤ y ∧ Mᵀ *ᵥ y = c) (H : ∀ x, M *ᵥ x ≤ b → c ⬝ᵥ x ≤ τ) :
    ∃ y, 0 ≤ y ∧ Mᵀ *ᵥ y = c ∧ b ⬝ᵥ y ≤ τ := by
  by_cases hP : ∃ x, M *ᵥ x ≤ b
  · obtain ⟨x, y, hx, hy, hc, heq, -⟩ := DualityKit.LP.strong_duality_matrix M b c hP hD
    exact ⟨y, hy, hc, heq ▸ H x hx⟩
  · obtain ⟨y0, hy0, hc0⟩ := hD
    obtain ⟨z, hz, hMz, hbz⟩ := farkas_mat M b hP
    set s : ℝ := max 0 ((b ⬝ᵥ y0 - τ) / (-(b ⬝ᵥ z))) with hs
    have hs0 : 0 ≤ s := le_max_left _ _
    refine ⟨y0 + s • z, add_nonneg hy0 (smul_nonneg hs0 hz), ?_, ?_⟩
    · rw [mulVec_add, mulVec_smul, hMz, smul_zero, add_zero, hc0]
    · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      have h1 : (b ⬝ᵥ y0 - τ) / (-(b ⬝ᵥ z)) ≤ s := le_max_right _ _
      have hpos : 0 < -(b ⬝ᵥ z) := by linarith
      rw [div_le_iff₀ hpos] at h1
      nlinarith



open KAdaptability.Bilinear KAdaptability.Bilinear.Problem

variable {N M L nQ R K : ℕ} (P : Problem N M L nQ R)

abbrev Row (K L R : ℕ) := Fin K ⊕ (Fin R ⊕ ((Fin K × Fin L) ⊕ Fin K))

def g (ℓ : Fin K → Fin (L + 1)) (k : Fin K) : ℝ := if ℓ k = 0 then 1 else 0

def Mb (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) :
    Matrix (Row K L R) (Option (Fin nQ)) ℝ := Matrix.of fun i o =>
  match i, o with
  | Sum.inl k, none => g ℓ k
  | Sum.inl k, some q => -(g ℓ k * (P.Q *ᵥ y k) q)
  | Sum.inr (Sum.inl _), none => 0
  | Sum.inr (Sum.inl r), some q => P.A r q
  | Sum.inr (Sum.inr (Sum.inl _)), none => 0
  | Sum.inr (Sum.inr (Sum.inl p)), some q => -(g ℓ p.1 * P.H p.2 q)
  | Sum.inr (Sum.inr (Sum.inr _)), none => 0
  | Sum.inr (Sum.inr (Sum.inr k)), some q => P.Hrow ℓ k q

def bb (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) :
    Row K L R → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl r) => P.b r
  | Sum.inr (Sum.inr (Sum.inl p)) => -(g ℓ p.1 * P.lhs x (y p.1) p.2)
  | Sum.inr (Sum.inr (Sum.inr k)) => (1 - g ℓ k) * (P.lhsRow x y ℓ k - ε)

def cb (x : Fin N → ℝ) : Option (Fin nQ) → ℝ
  | none => 1
  | some q => (P.C *ᵥ x) q

def wα (w : Row K L R → ℝ) : Fin R → ℝ := fun r => w (Sum.inr (Sum.inl r))
def wβ (w : Row K L R → ℝ) : Fin K → Fin L → ℝ := fun k i => w (Sum.inr (Sum.inr (Sum.inl (k, i))))
def wγ (w : Row K L R → ℝ) : Fin K → ℝ := fun k => w (Sum.inr (Sum.inr (Sum.inr k)))
def wlam (ℓ : Fin K → Fin (L + 1)) (w : Row K L R → ℝ) : Fin K → ℝ := fun k => g ℓ k * w (Sum.inl k)

theorem Hrow_zero (ℓ : Fin K → Fin (L + 1)) (k : Fin K) (h : ℓ k = 0) : P.Hrow ℓ k = 0 := by
  simp [Hrow, h]

theorem I1 (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) (w : Row K L R → ℝ) :
    ((Mb P y ℓ)ᵀ *ᵥ w) none = ∑ k, wlam ℓ w k := by
  simp [Mb, mulVec, dotProduct, Fintype.sum_sum_type, wlam]

theorem I2 (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) (w : Row K L R → ℝ) (q : Fin nQ) :
    ((Mb P y ℓ)ᵀ *ᵥ w) (some q) = P.dualLhsBdry ℓ (wα w) (wβ w) (wγ w) q
      - (∑ k, wlam ℓ w k • (P.Q *ᵥ y k)) q := by
  simp only [Mb, mulVec, dotProduct, Fintype.sum_sum_type, transpose_apply, of_apply,
    dualLhsBdry, Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_filter, Fintype.sum_prod_type, wα, wγ, wlam]
  have h1 : ∑ x, -(g ℓ x * ∑ x_1, P.Q q x_1 * y x x_1) * w (Sum.inl x) =
      -∑ x, g ℓ x * w (Sum.inl x) * ∑ x_1, P.Q q x_1 * y x x_1 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have h2 : ∑ x, ∑ x_1, -(g ℓ x * P.H x_1 q) * w (Sum.inr (Sum.inr (Sum.inl (x, x_1)))) =
      -∑ c, (if ℓ c = 0 then P.Hᵀ *ᵥ wβ w c else 0) q := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : ℓ c = 0
    · simp only [hc, if_true, g, mulVec, dotProduct, transpose_apply, wβ, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    · simp [hc, g]
  have h3 : ∑ x, P.Hrow ℓ x q * w (Sum.inr (Sum.inr (Sum.inr x))) =
      ∑ c, (if ℓ c ≠ 0 then w (Sum.inr (Sum.inr (Sum.inr c))) • P.Hrow ℓ c else 0) q := by
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : ℓ c = 0
    · simp [hc, Hrow_zero P ℓ c hc]
    · simp [hc, mul_comm]
  rw [h1, h2, h3]
  ring

theorem I3 (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (w : Row K L R → ℝ) :
    bb P ε x y ℓ ⬝ᵥ w = P.dualObjBdry ε x y ℓ (wα w) (wβ w) (wγ w) := by
  simp only [bb, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, dualObjBdry,
    Finset.sum_filter, wα, wβ, wγ, zero_mul, Finset.sum_const_zero, zero_add]
  have h2 : ∑ x_1, ∑ x_2, -(g ℓ x_1 * P.lhs x (y x_1) x_2) * w (Sum.inr (Sum.inr (Sum.inl (x_1, x_2))))
      = -∑ c, if ℓ c = 0 then P.lhs x (y c) ⬝ᵥ (fun i => w (Sum.inr (Sum.inr (Sum.inl (c, i))))) else 0 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : ℓ c = 0
    · simp only [hc, if_true, g, dotProduct, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    · simp [hc, g]
  have h3 : ∑ x_1, (1 - g ℓ x_1) * (P.lhsRow x y ℓ x_1 - ε) * w (Sum.inr (Sum.inr (Sum.inr x_1)))
      = ∑ c, if ℓ c ≠ 0 then (P.lhsRow x y ℓ c - ε) * w (Sum.inr (Sum.inr (Sum.inr c))) else 0 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : ℓ c = 0
    · simp [hc, g]
    · simp [hc, g]
  rw [h2, h3]
  simp only [dotProduct]
  ring

theorem Mb_row1 (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) (v : Option (Fin nQ) → ℝ)
    (k : Fin K) :
    (Mb (R := R) P y ℓ *ᵥ v) (Sum.inl k) =
      g ℓ k * (v none - P.secondCost (fun q => v (some q)) (y k)) := by
  simp only [Mb, mulVec, dotProduct, Fintype.sum_option, of_apply, secondCost]
  rw [mul_sub, Finset.mul_sum]
  simp only [neg_mul, Finset.sum_neg_distrib]
  have : ∀ i, g ℓ k * (∑ x, P.Q i x * y k x) * v (some i) = g ℓ k * (v (some i) * ∑ x, P.Q i x * y k x) :=
    fun i => by ring
  simp only [this]
  ring

theorem Mb_row2 (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) (v : Option (Fin nQ) → ℝ)
    (r : Fin R) :
    (Mb P y ℓ *ᵥ v) (Sum.inr (Sum.inl r)) = (P.A *ᵥ fun q => v (some q)) r := by
  simp [Mb, mulVec, dotProduct, Fintype.sum_option]

theorem Mb_row3 (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) (v : Option (Fin nQ) → ℝ)
    (k : Fin K) (i : Fin L) :
    (Mb (R := R) P y ℓ *ᵥ v) (Sum.inr (Sum.inr (Sum.inl (k, i)))) =
      -(g ℓ k * P.rhs (fun q => v (some q)) i) := by
  simp only [Mb, mulVec, dotProduct, Fintype.sum_option, of_apply, rhs, zero_mul, zero_add,
    neg_mul, Finset.sum_neg_distrib, Finset.mul_sum, mul_assoc]

theorem Mb_row4 (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) (v : Option (Fin nQ) → ℝ)
    (k : Fin K) :
    (Mb (R := R) P y ℓ *ᵥ v) (Sum.inr (Sum.inr (Sum.inr k))) =
      P.Hrow ℓ k ⬝ᵥ (fun q => v (some q)) := by
  simp [Mb, mulVec, dotProduct, Fintype.sum_option]

theorem hrow_iff (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (k : Fin K) (h : ℓ k ≠ 0) (ξ : Fin nQ → ℝ) :
    (∀ i : Fin L, ℓ k = i.succ → P.rhs ξ i + ε ≤ P.lhs x (y k) i) ↔
      P.Hrow ℓ k ⬝ᵥ ξ + ε ≤ P.lhsRow x y ℓ k := by
  simp only [Hrow, lhsRow, h, dite_false]
  constructor
  · intro hh
    exact hh _ (Fin.succ_pred _ h).symm
  · intro hh i hi
    have hp : (ℓ k).pred h = i := by simp [hi]
    rw [hp] at hh
    exact hh

theorem XiEps_iff (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (ξ : Fin nQ → ℝ) :
    ξ ∈ P.XiEps ε x y ℓ ↔ (∀ r, (P.A *ᵥ ξ) r ≤ P.b r) ∧
      (∀ k i, ℓ k = 0 → P.lhs x (y k) i ≤ P.rhs ξ i) ∧
      ∀ k, ℓ k ≠ 0 → P.Hrow ℓ k ⬝ᵥ ξ + ε ≤ P.lhsRow x y ℓ k := by
  simp only [XiEps, Xi, Set.mem_ofPred_eq, Pi.le_def]
  refine and_congr Iff.rfl (and_congr ⟨fun h k i hk => h k hk i, fun h k hk i => h k i hk⟩ ?_)
  refine forall_congr' fun k => ?_
  by_cases hk : ℓ k = 0
  · simp only [hk, ne_eq, not_true_eq_false, IsEmpty.forall_iff, iff_true]
    intro i hi
    exact absurd hi.symm (Fin.succ_ne_zero i)
  · rw [hrow_iff P ε x y ℓ k hk ξ]
    exact ⟨fun h _ => h, fun h => h hk⟩

theorem feas_iff (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (v : Option (Fin nQ) → ℝ) :
    Mb (R := R) P y ℓ *ᵥ v ≤ bb P ε x y ℓ ↔
      (∀ k, ℓ k = 0 → v none ≤ P.secondCost (fun q => v (some q)) (y k)) ∧
        (fun q => v (some q)) ∈ P.XiEps ε x y ℓ := by
  rw [XiEps_iff, Pi.le_def]
  simp only [Sum.forall, Prod.forall, Mb_row1, Mb_row2, Mb_row3, Mb_row4, bb]
  refine and_congr (forall_congr' fun k => ?_) (and_congr Iff.rfl
    (and_congr (forall_congr' fun k => forall_congr' fun i => ?_) (forall_congr' fun k => ?_)))
  · by_cases hk : ℓ k = 0
    · simp only [g, hk, if_true, one_mul, true_imp_iff]; constructor <;> intro h <;> linarith
    · simp [g, hk]
  · by_cases hk : ℓ k = 0
    · simp only [g, hk, if_true, one_mul, true_imp_iff, neg_le_neg_iff]
    · simp [g, hk]
  · by_cases hk : ℓ k = 0
    · simp [g, hk, Hrow_zero P ℓ k hk]
    · simp only [g, hk, if_false, sub_zero, one_mul, ne_eq, not_false_eq_true, true_imp_iff]
      constructor <;> intro h <;> linarith

theorem dual_iff (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (w : Row K L R → ℝ) :
    (Mb P y ℓ)ᵀ *ᵥ w = cb P x ↔ ∑ k, wlam ℓ w k = 1 ∧
      P.dualLhsBdry ℓ (wα w) (wβ w) (wγ w) = P.costVec x y (wlam ℓ w) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := congr_fun h none
      rwa [I1] at this
    · funext q
      have := congr_fun h (some q)
      rw [I2] at this
      simp only [cb] at this
      simp only [costVec, Pi.add_apply]
      linarith
  · rintro ⟨h1, h2⟩
    funext o
    cases o with
    | none => rw [I1, h1]; rfl
    | some q =>
      rw [I2, h2]
      simp [costVec, cb]

theorem cb_dot (x : Fin N → ℝ) (v : Option (Fin nQ) → ℝ) :
    cb P x ⬝ᵥ v = v none + P.firstCost (fun q => v (some q)) x := by
  simp [cb, dotProduct, Fintype.sum_option, firstCost, mul_comm]

theorem bracket_eq (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (hZ : (Finset.univ.filter fun k => ℓ k = 0).Nonempty) (ξ : Fin nQ → ℝ) :
    P.bracket x y ℓ ξ = ((P.firstCost ξ x +
      (Finset.univ.filter fun k => ℓ k = 0).inf' hZ (fun k => P.secondCost ξ (y k)) : ℝ) : EReal) := by
  rw [bracket, EReal.coe_add]
  congr 1
  apply le_antisymm
  · obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_inf' hZ (fun k => P.secondCost ξ (y k))
    rw [hkeq]
    exact iInf₂_le k (by simpa using hk)
  · refine le_iInf₂ fun k hk => EReal.coe_le_coe_iff.2 (Finset.inf'_le _ ?_)
    simpa using hk

theorem bracket_top (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (hℓ : ∀ k, ℓ k ≠ 0) (ξ : Fin nQ → ℝ) : P.bracket x y ℓ ξ = ⊤ := by
  simp [bracket, hℓ]

theorem bdry_iff (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (hℓ : ∃ k, ℓ k = 0) (τ : ℝ) :
    (∃ (lam : Fin K → ℝ) (α : Fin R → ℝ) (β : Fin K → Fin L → ℝ) (γ : Fin K → ℝ),
      lam ∈ DeltaK ℓ ∧ P.DualBdry ε x y ℓ lam τ α β γ) ↔
      ∀ ξ ∈ P.XiEps ε x y ℓ, P.bracket x y ℓ ξ ≤ (τ : EReal) := by
  classical
  obtain ⟨k0, hk0⟩ := hℓ
  have hZ : (Finset.univ.filter fun k => ℓ k = 0).Nonempty := ⟨k0, by simp [hk0]⟩
  constructor
  · rintro ⟨lam, α, β, γ, hΔ, hD⟩ ξ hξ
    let w : Row K L R → ℝ := Sum.elim lam (Sum.elim α (Sum.elim (fun p => β p.1 p.2) γ))
    have hwl : wlam ℓ w = lam := by
      funext k
      by_cases hk : ℓ k = 0
      · simp [wlam, g, hk, w]
      · simp [wlam, g, hk, hΔ.2.2 k hk]
    have hw : 0 ≤ w := by
      intro i
      rcases i with k | r | p | k
      · exact hΔ.1 k
      · exact hD.1 r
      · exact hD.2.1 p.1 p.2
      · exact hD.2.2.1 k
    have hc : (Mb P y ℓ)ᵀ *ᵥ w = cb P x :=
      (dual_iff P x y ℓ w).2 ⟨by rw [hwl]; exact hΔ.2.1, by rw [hwl]; exact hD.2.2.2.2⟩
    have hb : bb P ε x y ℓ ⬝ᵥ w ≤ τ := by rw [I3]; exact hD.2.2.2.1
    let t : ℝ := (Finset.univ.filter fun k => ℓ k = 0).inf' hZ (fun k => P.secondCost ξ (y k))
    let v : Option (Fin nQ) → ℝ := fun o => o.elim t ξ
    have hv : Mb P y ℓ *ᵥ v ≤ bb P ε x y ℓ := by
      refine (feas_iff P ε x y ℓ v).2 ⟨fun k hk => ?_, hξ⟩
      exact Finset.inf'_le _ (by simp [hk])
    have hwk := weak_mat _ _ _ _ _ hv hw hc
    rw [cb_dot] at hwk
    rw [bracket_eq P x y ℓ hZ, EReal.coe_le_coe_iff]
    change t + P.firstCost ξ x ≤ bb P ε x y ℓ ⬝ᵥ w at hwk
    linarith
  · intro H
    have H' : ∀ v, Mb (R := R) P y ℓ *ᵥ v ≤ bb P ε x y ℓ → cb P x ⬝ᵥ v ≤ τ := by
      intro v hv
      obtain ⟨hk, hξ⟩ := (feas_iff P ε x y ℓ v).1 hv
      have h1 := H _ hξ
      rw [bracket_eq P x y ℓ hZ, EReal.coe_le_coe_iff] at h1
      have h2 : v none ≤ (Finset.univ.filter fun k => ℓ k = 0).inf' hZ
          (fun k => P.secondCost (fun q => v (some q)) (y k)) :=
        Finset.le_inf' _ _ fun k hk' => hk k (by simpa using hk')
      rw [cb_dot]
      linarith
    have hD : ∃ w, 0 ≤ w ∧ (Mb (R := R) P y ℓ)ᵀ *ᵥ w = cb P x := by
      obtain ⟨α0, hα0, hAα0⟩ := DualityKit.LP.exists_dual_of_isBounded P.A P.b P.Xi_nonempty
        P.Xi_bounded (P.C *ᵥ x + P.Q *ᵥ y k0)
      let w0 : Row K L R → ℝ :=
        Sum.elim (fun k => if k = k0 then 1 else 0) (Sum.elim α0 0)
      have hwl : wlam ℓ w0 = fun k => if k = k0 then 1 else 0 := by
        funext k
        by_cases hk : k = k0
        · subst hk; simp [wlam, g, hk0, w0]
        · simp [wlam, hk, w0]
      refine ⟨w0, ?_, (dual_iff P x y ℓ w0).2 ⟨?_, ?_⟩⟩
      · intro i
        rcases i with k | r | p | k
        · by_cases hk : k = k0 <;> simp [w0, hk]
        · exact hα0 r
        · exact le_refl 0
        · exact le_refl 0
      · rw [hwl]; simp
      · rw [hwl]
        have hβ : wβ w0 = 0 := rfl
        have hγ : wγ w0 = 0 := rfl
        have hα : wα w0 = α0 := rfl
        rw [hβ, hγ, hα]
        simp [dualLhsBdry, costVec, hAα0, ite_smul]
    obtain ⟨w, hw, hc, hb⟩ := dual_le_of_bound _ _ _ τ hD H'
    obtain ⟨hsum, heq⟩ := (dual_iff P x y ℓ w).1 hc
    refine ⟨wlam ℓ w, wα w, wβ w, wγ w, ⟨?_, hsum, ?_⟩, ?_, ?_, ?_, ?_, heq⟩
    · intro k
      exact mul_nonneg (by unfold g; split_ifs <;> norm_num) (hw _)
    · intro k hk
      simp [wlam, g, hk]
    · exact fun r => hw _
    · exact fun k i => hw _
    · exact fun k => hw _
    · rw [← I3]; exact hb

def Mp (ℓ : Fin K → Fin (L + 1)) : Matrix (Fin R ⊕ Fin K) (Fin nQ) ℝ := Matrix.of fun i q =>
  match i with
  | Sum.inl r => P.A r q
  | Sum.inr k => P.Hrow ℓ k q

def bp (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) :
    Fin R ⊕ Fin K → ℝ
  | Sum.inl r => P.b r
  | Sum.inr k => P.lhsRow x y ℓ k - ε

theorem Mp_feas (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (hℓ : ∀ k, ℓ k ≠ 0) (ξ : Fin nQ → ℝ) :
    Mp P ℓ *ᵥ ξ ≤ bp P ε x y ℓ ↔ ξ ∈ P.XiEps ε x y ℓ := by
  rw [XiEps_iff, Pi.le_def, Sum.forall]
  simp only [Mp, bp, hℓ, false_imp_iff, implies_true, true_and, ne_eq, not_false_eq_true,
    true_imp_iff]
  refine and_congr Iff.rfl (forall_congr' fun k => ?_)
  simp only [mulVec, of_apply]
  constructor <;> intro h <;> linarith

theorem MpT (ℓ : Fin K → Fin (L + 1)) (w : Fin R ⊕ Fin K → ℝ) :
    (Mp P ℓ)ᵀ *ᵥ w = P.Aᵀ *ᵥ (fun r => w (Sum.inl r)) + ∑ k, w (Sum.inr k) • P.Hrow ℓ k := by
  funext q
  simp [Mp, mulVec, dotProduct, Fintype.sum_sum_type, Finset.sum_apply, mul_comm]

theorem bp_dot (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (w : Fin R ⊕ Fin K → ℝ) :
    bp P ε x y ℓ ⬝ᵥ w = P.b ⬝ᵥ (fun r => w (Sum.inl r)) +
      ∑ k, (P.lhsRow x y ℓ k - ε) * w (Sum.inr k) := by
  simp [bp, dotProduct, Fintype.sum_sum_type]

theorem plus_iff (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (hℓ : ∀ k, ℓ k ≠ 0) :
    (∃ (α : Fin R → ℝ) (γ : Fin K → ℝ), P.PlusBlock ε x y ℓ α γ) ↔
      P.XiEps ε x y ℓ = ∅ := by
  constructor
  · rintro ⟨α, γ, hα, hγ, hobj, heq⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro ξ hξ
    have hw : (0 : Fin R ⊕ Fin K → ℝ) ≤ Sum.elim α γ := by
      intro i; rcases i with r | k
      · exact hα r
      · exact hγ k
    have hc : (Mp P ℓ)ᵀ *ᵥ Sum.elim α γ = 0 := by
      rw [MpT]; exact heq
    have := weak_mat _ _ _ _ _ ((Mp_feas P ε x y ℓ hℓ ξ).2 hξ) hw hc
    rw [bp_dot, zero_dotProduct] at this
    simp only [Sum.elim_inl, Sum.elim_inr] at this
    change 0 ≤ P.b ⬝ᵥ α + ∑ k, (P.lhsRow x y ℓ k - ε) * γ k at this
    linarith
  · intro h
    have hP : ¬ ∃ ξ, Mp P ℓ *ᵥ ξ ≤ bp P ε x y ℓ := by
      rintro ⟨ξ, hξ⟩
      have := (Mp_feas P ε x y ℓ hℓ ξ).1 hξ
      rw [h] at this
      exact this
    obtain ⟨z, hz, hMz, hbz⟩ := farkas_mat _ _ hP
    set s : ℝ := -1 / (bp P ε x y ℓ ⬝ᵥ z) with hs
    have hs0 : 0 ≤ s := by
      rw [hs]; exact div_nonneg_of_nonpos (by norm_num) hbz.le
    have hsb : s * (bp P ε x y ℓ ⬝ᵥ z) = -1 := by
      rw [hs]; field_simp [hbz.ne]
    have hw : 0 ≤ s • z := smul_nonneg hs0 hz
    have hc : (Mp P ℓ)ᵀ *ᵥ (s • z) = 0 := by rw [mulVec_smul, hMz, smul_zero]
    have hb : bp P ε x y ℓ ⬝ᵥ (s • z) = -1 := by rw [dotProduct_smul, smul_eq_mul, hsb]
    rw [MpT] at hc
    rw [bp_dot] at hb
    refine ⟨fun r => (s • z) (Sum.inl r), fun k => (s • z) (Sum.inr k), fun r => hw _,
      fun k => hw _, le_of_eq hb, hc⟩

theorem loc_iff (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (τ : ℝ) :
    (∃ t : (Fin K → ℝ) × (Fin R → ℝ) × (Fin K → Fin L → ℝ) × (Fin K → ℝ),
      (ℓ ∈ LBdry K L → t.1 ∈ DeltaK ℓ ∧ P.DualBdry ε x y ℓ t.1 τ t.2.1 t.2.2.1 t.2.2.2) ∧
      (ℓ ∈ LPlus K L → P.PlusBlock ε x y ℓ t.2.1 t.2.2.2)) ↔
      ∀ ξ ∈ P.XiEps ε x y ℓ, P.bracket x y ℓ ξ ≤ (τ : EReal) := by
  by_cases hB : ∃ k, ℓ k = 0
  · have hnP : ℓ ∉ LPlus K L := by
      obtain ⟨k, hk⟩ := hB
      exact fun h => h k hk
    rw [← bdry_iff P ε x y ℓ hB τ]
    constructor
    · rintro ⟨t, h1, -⟩
      exact ⟨t.1, t.2.1, t.2.2.1, t.2.2.2, h1 hB⟩
    · rintro ⟨lam, α, β, γ, h⟩
      exact ⟨(lam, α, β, γ), fun _ => h, fun h' => absurd h' hnP⟩
  · simp only [not_exists] at hB
    have hnB : ℓ ∉ LBdry K L := by
      rintro ⟨k, hk⟩; exact hB k hk
    have hR : (∀ ξ ∈ P.XiEps ε x y ℓ, P.bracket x y ℓ ξ ≤ (τ : EReal)) ↔
        P.XiEps ε x y ℓ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      refine forall_congr' fun ξ => ?_
      rw [bracket_top P x y ℓ hB]
      simp
    rw [hR, ← plus_iff P ε x y ℓ hB]
    constructor
    · rintro ⟨t, -, h2⟩
      exact ⟨t.2.1, t.2.2.2, h2 hB⟩
    · rintro ⟨α, γ, h⟩
      exact ⟨(0, α, 0, γ), fun h' => absurd h' hnB, fun _ => h⟩

theorem feas7_iff (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (τ : ℝ) :
    P.Feasible7 ε x y τ ↔ P.obj6Eps ε x y ≤ (τ : EReal) := by
  simp only [obj6Eps, iSup_le_iff]
  rw [show (∀ ℓ, ∀ ξ ∈ P.XiEps ε x y ℓ, P.bracket x y ℓ ξ ≤ (τ : EReal)) ↔ _ from
    forall_congr' fun ℓ => (loc_iff P ε x y ℓ τ).symm]
  constructor
  · rintro ⟨lam, α, β, γ, h1, h2⟩ ℓ
    exact ⟨(lam ℓ, α ℓ, β ℓ, γ ℓ), h1 ℓ, h2 ℓ⟩
  · intro h
    choose f hf using h
    exact ⟨fun ℓ => (f ℓ).1, fun ℓ => (f ℓ).2.1, fun ℓ => (f ℓ).2.2.1, fun ℓ => (f ℓ).2.2.2,
      fun ℓ => (hf ℓ).1, fun ℓ => (hf ℓ).2⟩

theorem sInf_upper (φ : EReal) :
    sInf ((fun τ : ℝ => (τ : EReal)) '' {τ | φ ≤ (τ : EReal)}) = φ := by
  apply le_antisymm
  · induction φ using EReal.rec with
    | bot =>
      refine le_of_eq ((EReal.eq_bot_iff_forall_lt _).2 fun r => ?_)
      exact lt_of_le_of_lt (sInf_le ⟨r - 1, show (⊥ : EReal) ≤ ((r - 1 : ℝ) : EReal) from bot_le, rfl⟩)
        (EReal.coe_lt_coe_iff.2 (by linarith))
    | top => exact le_top
    | coe r => exact sInf_le ⟨r, show ((r : ℝ) : EReal) ≤ r from le_refl _, rfl⟩
  · refine le_sInf ?_
    rintro _ ⟨τ, hτ, rfl⟩
    exact hτ

end RRAux_KAdaptability_Bilinear_theorem_5

open KAdaptability.Bilinear KAdaptability.Bilinear.Problem in
theorem solution {N M L nQ R K : ℕ} (P : Problem N M L nQ R) (ε : ℝ) (hε : 0 < ε) :
    (∀ (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ), P.IsDecision x y →
      P.obj6Eps ε x y = P.val7 ε x y ∧
      ∀ τ : ℝ, P.Feasible7 ε x y τ ↔ P.obj6Eps ε x y ≤ (τ : EReal)) ∧
    P.opt6Eps ε K = P.opt7 ε K := by
  have hval : ∀ (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ), P.val7 ε x y = P.obj6Eps ε x y := by
    intro x y
    rw [val7]
    simp_rw [RRAux_KAdaptability_Bilinear_theorem_5.feas7_iff P ε x y]
    exact RRAux_KAdaptability_Bilinear_theorem_5.sInf_upper _
  refine ⟨fun x y _ => ⟨(hval x y).symm, RRAux_KAdaptability_Bilinear_theorem_5.feas7_iff P ε x y⟩, ?_⟩
  apply le_antisymm
  · refine le_sInf ?_
    rintro _ ⟨τ, ⟨x, y, hd, hf⟩, rfl⟩
    refine iInf_le_of_le x (iInf_le_of_le y (iInf_le_of_le hd ?_))
    exact (RRAux_KAdaptability_Bilinear_theorem_5.feas7_iff P ε x y τ).1 hf
  · refine le_iInf fun x => le_iInf fun y => le_iInf fun hd => ?_
    rw [← hval x y, val7]
    refine sInf_le_sInf (Set.image_mono ?_)
    intro τ hτ
    exact ⟨x, y, hd, hτ⟩

#print axioms solution
