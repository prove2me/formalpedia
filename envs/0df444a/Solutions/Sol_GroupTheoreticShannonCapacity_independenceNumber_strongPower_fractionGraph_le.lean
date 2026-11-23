-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.independenceNumber_strongPower_fractionGraph_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:41:41.103876+00:00
-- url     : https://prove2.me/submissions/82507bb1-1808-45c1-9aa5-3bf1040bbb85

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
import Theorems.Thm_GroupTheoreticShannonCapacity_isClique_arc
import Theorems.Thm_GroupTheoreticShannonCapacity_independenceNumber_le_of_clique_cover
import Theorems.Thm_GroupTheoreticShannonCapacity_strongPower_isClique_piFinset


set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (p q : ℕ) [NeZero p]
    (hq : 0 < q) (hpq : q ≤ p) (n : ℕ) :
    ((strongPower (fractionGraph p q) (n + 1)).indepNum : ℝ) ≤
    ((p : ℝ) / q) ^ (n + 1) := by
  -- Case split: 2q ≤ p (structured arcs) vs q ≤ p < 2q (complete or near-complete)
  by_cases h2q : 2 * q ≤ p
  · -- Case 2q ≤ p: Product arcs form a proper clique cover
    -- The product arcs are {(s₁+j₁, ..., s_{n+1}+j_{n+1}) : 0 ≤ jₖ < q} for each start s
    -- There are p^(n+1) such arcs
    -- Each vertex is in q^(n+1) arcs
    -- Each arc is a clique (any two distinct vertices differ in some coordinate by < q)
    -- The counting argument gives: |S| ≤ (p/q)^(n+1)

    -- Define product arc: vertices reachable from start by adding offsets in [0, q)
    let productArc (start : Fin (n + 1) → ZMod p) : Finset (Fin (n + 1) → ZMod p) :=
      Fintype.piFinset (fun i => (Finset.range q).image (fun j : ℕ => start i + j))
    -- Each product arc is a clique in the strong power graph
    have harc_clique : ∀ start : Fin (n + 1) → ZMod p,
        (strongPower (fractionGraph p q) (n + 1)).IsClique (productArc start) := by
      intro start
      apply strongPower_isClique_piFinset
      intro i
      exact isClique_arc p q hq h2q (start i)
    -- Use the clique cover bound: α ≤ (p/q)^(n+1)
    -- This follows from counting: each vertex is in q^(n+1) arcs, p^(n+1) total arcs
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq
    have hpq_ge : 1 ≤ (p : ℝ) / q := by
      have hpq_real : (q : ℝ) ≤ p := by exact_mod_cast hpq
      exact (one_le_div hq_pos).mpr hpq_real
    -- The set of all product arcs
    let allArcs : Finset (Finset (Fin (n + 1) → ZMod p)) :=
      Finset.univ.image productArc
    -- Define weights
    let weights : Finset (Fin (n + 1) → ZMod p) → ℝ :=
      fun _ => 1 / (q : ℝ) ^ (n + 1)
    -- Apply the clique cover bound
    classical
    apply independenceNumber_le_of_clique_cover (strongPower (fractionGraph p q) (n + 1))
      allArcs weights
    · -- Each arc is a clique
      intro C hC
      simp only [allArcs, Finset.mem_image, Finset.mem_univ, true_and] at hC
      obtain ⟨start, hstart⟩ := hC
      rw [← hstart]
      exact harc_clique start
    · -- Weights are non-negative
      intro _ _
      apply div_nonneg zero_le_one
      apply pow_nonneg
      linarith
    · -- Each vertex is covered with weight ≥ 1
      intro v
      -- v is in q^(n+1) arcs: for each offset j ∈ [0,q)^(n+1), v is in arc(v - j)
      -- Each arc contributes weight 1/q^(n+1), so total ≥ 1
      -- Define the covering arcs: {productArc (v - j) : j ∈ [0,q)^(n+1)}
      let offsetType := Fin (n + 1) → Fin q
      let startFromOffset : offsetType → (Fin (n + 1) → ZMod p) :=
        fun j => fun i => v i - (j i : ℕ)
      let coveringArcs := Finset.univ.image (fun j : offsetType => productArc (startFromOffset j))
      -- v is in productArc (v - j) for each offset j
      have hv_in_arc : ∀ j : offsetType, v ∈ productArc (startFromOffset j) := by
        intro j
        simp only [productArc, Fintype.mem_piFinset, Finset.mem_image, Finset.mem_range]
        intro i
        use (j i : ℕ)
        constructor
        · exact (j i).isLt
        · simp [startFromOffset]
      -- The covering arcs are in allArcs
      have hcover_in_all : coveringArcs ⊆ allArcs := by
        intro C hC
        simp only [coveringArcs, Finset.mem_image, Finset.mem_univ, true_and] at hC
        obtain ⟨j, rfl⟩ := hC
        simp only [allArcs, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨startFromOffset j, rfl⟩
      -- The covering arcs are all arcs containing v
      have hcover_v : ∀ C ∈ coveringArcs, v ∈ C := by
        intro C hC
        simp only [coveringArcs, Finset.mem_image, Finset.mem_univ, true_and] at hC
        obtain ⟨j, rfl⟩ := hC
        exact hv_in_arc j
      -- Hence coveringArcs ⊆ {x ∈ allArcs | v ∈ x}
      have hcover_subset : coveringArcs ⊆ allArcs.filter (v ∈ ·) := by
        intro C hC
        rw [Finset.mem_filter]
        exact ⟨hcover_in_all hC, hcover_v C hC⟩
      -- startFromOffset is injective
      have hstart_inj : Function.Injective startFromOffset := by
        intro j1 j2 heq
        funext i
        have h := congrFun heq i
        simp only [startFromOffset] at h
        -- h: v i - (j1 i : ℕ) = v i - (j2 i : ℕ) in ZMod p
        -- This implies (j1 i : ℕ) = (j2 i : ℕ) in ZMod p
        have hj1_lt : (j1 i : ℕ) < p := Nat.lt_of_lt_of_le (j1 i).isLt hpq
        have hj2_lt : (j2 i : ℕ) < p := Nat.lt_of_lt_of_le (j2 i).isLt hpq
        have hval : ((j1 i : ℕ) : ZMod p) = ((j2 i : ℕ) : ZMod p) := sub_right_injective h
        -- Since j1 i, j2 i < q ≤ p, their ZMod p values determine them
        have hval_nat : (j1 i : ℕ) = (j2 i : ℕ) := by
          have h1 : ((j1 i : ℕ) : ZMod p).val = (j1 i : ℕ) := ZMod.val_natCast_of_lt hj1_lt
          have h2 : ((j2 i : ℕ) : ZMod p).val = (j2 i : ℕ) := ZMod.val_natCast_of_lt hj2_lt
          rw [← h1, ← h2, hval]
        exact Fin.ext hval_nat
      -- productArc is injective on startFromOffset's range (by function injectivity)
      have hprod_inj : ∀ j1 j2 : offsetType,
          productArc (startFromOffset j1) = productArc (startFromOffset j2) → j1 = j2 := by
        intro j1 j2 heq
        apply hstart_inj
        funext i
        -- start is the element with all 0 offsets in the arc
        have hmem1 : startFromOffset j1 ∈ productArc (startFromOffset j1) := by
          simp only [productArc, Fintype.mem_piFinset, Finset.mem_image, Finset.mem_range]
          intro i'; use 0; simp [hq]
        have hmem2 : startFromOffset j1 ∈ productArc (startFromOffset j2) := by
          rw [← heq]; exact hmem1
        simp only [productArc, Fintype.mem_piFinset, Finset.mem_image, Finset.mem_range] at hmem2
        obtain ⟨k, hk_lt, hk_eq⟩ := hmem2 i
        have hmem3 : startFromOffset j2 ∈ productArc (startFromOffset j2) := by
          simp only [productArc, Fintype.mem_piFinset, Finset.mem_image, Finset.mem_range]
          intro i'; use 0; simp [hq]
        have hmem4 : startFromOffset j2 ∈ productArc (startFromOffset j1) := by
          rw [heq]; exact hmem3
        simp only [productArc, Fintype.mem_piFinset, Finset.mem_image, Finset.mem_range] at hmem4
        obtain ⟨k', hk'_lt, hk'_eq⟩ := hmem4 i
        -- hk_eq: s2 i + k = s1 i, hk'_eq: s1 i + k' = s2 i
        -- Substituting: (s2 i + k) + k' = s2 i, so k + k' = 0 in ZMod p
        have hkk' : (k : ZMod p) + k' = 0 := by
          have h1 : startFromOffset j2 i + k + k' = startFromOffset j2 i := by
            calc startFromOffset j2 i + k + k' = startFromOffset j1 i + k' := by rw [hk_eq]
              _ = startFromOffset j2 i := hk'_eq
          calc (k : ZMod p) + k' = startFromOffset j2 i + k + k' - startFromOffset j2 i := by ring
            _ = startFromOffset j2 i - startFromOffset j2 i := by rw [h1]
            _ = 0 := by ring
        -- k, k' < q, k + k' < 2q ≤ p
        have hsum_lt_p : k + k' < p := by omega
        -- If (k + k' : ZMod p) = 0 and k + k' < p, then k + k' = 0
        have hsum_zero : k + k' = 0 := by
          -- hkk' says (k : ZMod p) + k' = 0
          -- Since k + k' < p, we have ((k+k') : ZMod p).val = k + k'
          -- And (0 : ZMod p).val = 0
          have hval := ZMod.val_natCast_of_lt hsum_lt_p
          -- ((k + k') : ZMod p) = (k : ZMod p) + k' = 0
          simp only [Nat.cast_add, hkk', ZMod.val_zero] at hval
          exact hval.symm
        -- k = 0 and k' = 0 from k + k' = 0 (both are ℕ)
        have hk_zero : k = 0 := by omega
        have hk'_zero : k' = 0 := by omega
        -- From hk_eq: s2 i + 0 = s1 i, so s2 i = s1 i
        simp only [hk_zero, Nat.cast_zero, add_zero] at hk_eq
        exact hk_eq.symm
      -- coveringArcs has cardinality q^(n+1)
      have hcard : coveringArcs.card = q ^ (n + 1) := by
        simp only [coveringArcs]
        rw [Finset.card_image_of_injective _ (fun j1 j2 heq => hprod_inj j1 j2 heq)]
        simp only [Finset.card_univ]
        -- offsetType = Fin (n + 1) → Fin q, so card = q^(n+1)
        simp only [offsetType, Fintype.card_fun, Fintype.card_fin]
      -- Sum over coveringArcs = q^(n+1) * (1/q^(n+1)) = 1
      have hsum_covering : coveringArcs.sum weights = 1 := by
        simp only [weights, Finset.sum_const, hcard]
        rw [nsmul_eq_mul, mul_one_div]
        rw [Nat.cast_pow]
        rw [div_self]
        apply pow_ne_zero
        exact_mod_cast hq.ne'
      -- Sum over filter ≥ sum over coveringArcs
      have hweights_nonneg : ∀ x, 0 ≤ weights x := by
        intro x
        simp only [weights]
        apply div_nonneg zero_le_one (pow_nonneg (by linarith : (0 : ℝ) ≤ q) _)
      calc (allArcs.filter (v ∈ ·)).sum weights
          ≥ coveringArcs.sum weights := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hcover_subset
            intro i _ _
            exact hweights_nonneg i
          _ = 1 := hsum_covering
    · -- Total weight ≤ (p/q)^(n+1)
      -- There are at most p^(n+1) arcs, each with weight 1/q^(n+1)
      have hcard : allArcs.card ≤ p ^ (n + 1) := by
        simp only [allArcs]
        have h1 : (Finset.univ.image productArc).card ≤
            (Finset.univ : Finset (Fin (n + 1) → ZMod p)).card := Finset.card_image_le
        have h3 : Fintype.card (Fin (n + 1) → ZMod p) = p ^ (n + 1) := by
          simp [Fintype.card_fin, ZMod.card]
        simp only [Finset.card_univ] at h1
        omega
      have hsum : allArcs.sum weights = allArcs.card • (1 / (q : ℝ) ^ (n + 1)) := by
        simp only [weights, Finset.sum_const]
      have hle : (allArcs.card : ℝ) ≤ (p ^ (n + 1) : ℕ) := by exact_mod_cast hcard
      calc allArcs.sum weights
          = allArcs.card • (1 / (q : ℝ) ^ (n + 1)) := hsum
        _ = (allArcs.card : ℝ) * (1 / (q : ℝ) ^ (n + 1)) := by rw [nsmul_eq_mul]
        _ ≤ (p ^ (n + 1) : ℕ) * (1 / (q : ℝ) ^ (n + 1)) := by
              apply mul_le_mul_of_nonneg_right hle
              apply div_nonneg zero_le_one (pow_nonneg (by linarith) _)
        _ = (p : ℝ) ^ (n + 1) / (q : ℝ) ^ (n + 1) := by
              rw [mul_one_div]
              norm_cast
        _ = ((p : ℝ) / q) ^ (n + 1) := by rw [div_pow]
  · -- Case q ≤ p < 2q: Graph is complete!
    -- When 2q > p, we have q > p/2 ≥ ⌊p/2⌋.
    -- distMod(u,v) ≤ ⌊p/2⌋ < q for all pairs, so all distinct pairs are adjacent.
    -- Complete graph has α = 1, and strong power of complete graph is complete.
    -- So α(E_{p/q}^⊠(n+1)) = 1 ≤ (p/q)^(n+1) since p/q ≥ 1 (because q ≤ p).
    push_neg at h2q
    -- The fraction graph is complete when 2q > p
    have hcomplete : ∀ u v : ZMod p, u ≠ v → (fractionGraph p q).Adj u v := by
      intro u v huv
      simp only [fractionGraph]
      constructor
      · exact huv
      · -- distMod u v < q because distMod ≤ ⌊p/2⌋ < q
        have hdist_le : distMod p u v ≤ p / 2 := by
          simp only [distMod]
          have hval := (u - v).val_lt
          have hval_pos : 0 < (u - v).val := by
            by_contra h
            push_neg at h
            have hzval := Nat.eq_zero_of_le_zero h
            have hzero : u - v = 0 := (ZMod.val_eq_zero (u - v)).mp hzval
            exact huv (sub_eq_zero.mp hzero)
          omega
        omega
    -- Strong power of complete graph is complete
    have hstrong_complete : ∀ f g : Fin (n + 1) → ZMod p, f ≠ g →
        (strongPower (fractionGraph p q) (n + 1)).Adj f g := by
      intro f g hfg
      simp only [strongPower]
      constructor
      · exact hfg
      · intro i
        by_cases heq : f i = g i
        · left; exact heq
        · right; exact hcomplete (f i) (g i) heq
    -- Independence number of complete graph is 1
    have hindep_le : (strongPower (fractionGraph p q) (n + 1)).indepNum ≤ 1 := by
      classical
      obtain ⟨S, hSmax⟩ :=
        SimpleGraph.maximumIndepSet_exists (G := strongPower (fractionGraph p q) (n + 1))
      have hS_indep : (strongPower (fractionGraph p q) (n + 1)).IsIndepSet (S : Set _) :=
        (SimpleGraph.isMaximumIndepSet_iff _ S).1 hSmax |>.1
      have hS_pairwise := (SimpleGraph.isIndepSet_iff _).1 hS_indep
      have hcard : S.card ≤ 1 := by
        by_contra h
        have h1 : 1 < S.card := Nat.lt_of_not_ge h
        obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h1
        have hadj := hstrong_complete u v huv
        have hnadj := hS_pairwise (by simpa using hu) (by simpa using hv) huv
        exact hnadj hadj
      have hS_card : S.card = (strongPower (fractionGraph p q) (n + 1)).indepNum := by
        simpa using
          (SimpleGraph.maximumIndepSet_card_eq_indepNum
            (G := strongPower (fractionGraph p q) (n + 1)) S hSmax)
      simpa [hS_card] using hcard
    -- Now show 1 ≤ (p/q)^(n+1)
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq
    have hpq_ge : 1 ≤ (p : ℝ) / q := by
      have hpq_real : (q : ℝ) ≤ p := by exact_mod_cast hpq
      exact (one_le_div hq_pos).mpr hpq_real
    calc ((strongPower (fractionGraph p q) (n + 1)).indepNum : ℝ)
        ≤ 1 := by exact_mod_cast hindep_le
      _ = 1 ^ (n + 1) := by ring
      _ ≤ ((p : ℝ) / q) ^ (n + 1) := by
            apply pow_le_pow_left₀ zero_le_one hpq_ge
end GroupTheoreticShannonCapacity
