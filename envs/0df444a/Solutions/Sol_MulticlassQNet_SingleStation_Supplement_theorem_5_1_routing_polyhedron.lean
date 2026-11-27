-- Prove2me | solution 1 for MulticlassQNet.SingleStation.Supplement.theorem_5_1_routing_polyhedron
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:10:27.589779+00:00
-- url     : https://prove2.me/submissions/ee7d176e-39fb-4465-a86b-3d77a4ef8a4e

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics
import Definitions.Def_MulticlassQNet_SingleStation_Supplement_Routing

open MulticlassQNet
open MulticlassQNet.SingleStation
open MulticlassQNet.SingleStation.Supplement

open MulticlassQNet.FirstOrder

/-- Theorem 5.1 (pp. 23–24): for every routing-and-sequencing policy satisfying Assumption A,
the stationary quantities `n_r`, `u_r` (32), `D_{rd}` (33), `G_{rdj}` (34), `I_{rj}` (35) satisfy
(36)–(42), vanish on routes outside `F_r`, and are nonnegative. In (38) the right-hand side is
`−μ_r D_{rr'} − μ_{r'} D_{r'r}` (the printed `u_r D_{rr'}` products double-count `u`, since (33)
already includes `1{B_r}`); in (40) the free index is `j`. The exit target is `none`. -/
theorem solution {N R : ℕ} (net : Network N R)
    (F : Fin R → Finset (Option (Fin R))) (P : RoutingPolicy net F) (π : (Fin R → ℕ) → ℝ)
    (hA : P.AssumptionA π) :
    -- (36)
    (∀ r, net.μ r * P.u π r - ∑ l, net.μ l * P.D π l (some r) = net.lam0 r) ∧
    -- (37)
    (∀ r, 2 * net.μ r * P.I π r r - 2 * ∑ l, net.μ l * P.G π l (some r) r
        - 2 * net.lam0 r * meanNum π r
      = net.lam0 r + net.μ r * (P.u π r - P.D π r (some r))
        + ∑ l ∈ Finset.univ.erase r, net.μ l * P.D π l (some r)) ∧
    -- (38), corrected right-hand side
    (∀ r r', r' < r →
      net.μ r * P.I π r r' + net.μ r' * P.I π r' r - ∑ w, net.μ w * P.G π w (some r) r'
        - ∑ w, net.μ w * P.G π w (some r') r - net.lam0 r * meanNum π r'
        - net.lam0 r' * meanNum π r
      = -(net.μ r * P.D π r (some r')) - net.μ r' * P.D π r' (some r)) ∧
    -- (39)
    (∀ i, ∑ r ∈ net.C i, P.u π r ≤ 1) ∧
    -- (40)
    (∀ i j, ∑ r ∈ net.C i, P.I π r j ≤ meanNum π j) ∧
    -- (41)
    (∀ r, P.u π r = ∑ d, P.D π r d) ∧
    -- (42)
    (∀ r j, P.I π r j = ∑ d, P.G π r d j) ∧
    -- forbidden routes
    (∀ r d, d ∉ F r → P.D π r d = 0 ∧ ∀ j, P.G π r d j = 0) ∧
    -- nonnegativity
    (∀ r, 0 ≤ meanNum π r) ∧ (∀ r, 0 ≤ P.u π r) ∧ (∀ r d, 0 ≤ P.D π r d) ∧
    (∀ r d j, 0 ≤ P.G π r d j) ∧ (∀ r j, 0 ≤ P.I π r j) := by
      obtain ⟨⟨hπ0, hπ1, hbal⟩, _, hsq⟩ := hA
      have hbusy0 : ∀ n r, 0 ≤ P.toPolicy.busy n r := by
        intro n r; unfold Policy.busy; split_ifs <;> norm_num
      have hbusy1 : ∀ n r, P.toPolicy.busy n r ≤ 1 := by
        intro n r; unfold Policy.busy; split_ifs <;> norm_num
      have hroute1 : ∀ n r d, P.route n r d ≤ 1 := by
        intro n r d
        rw [← P.route_sum_one n r]
        exact Finset.single_le_sum (fun d _ => P.route_nonneg n r d) (Finset.mem_univ d)
      -- the weight W
      have hπs : Summable π := hπ1.summable
      have hW : Summable (fun n : Fin R → ℕ => π n * (1 + ∑ j, ((n j : ℝ)) ^ 2)) := by
        have : (fun n : Fin R → ℕ => π n * (1 + ∑ j, ((n j : ℝ)) ^ 2))
            = fun n => π n + ∑ j, π n * ((n j : ℝ)) ^ 2 := by
          funext n; rw [mul_add, mul_one, Finset.mul_sum]
        rw [this]
        exact hπs.add (summable_sum fun j _ => hsq j)
      have hWge : ∀ n : Fin R → ℕ, ∀ j, ((n j : ℝ)) ^ 2 ≤ ∑ j, ((n j : ℝ)) ^ 2 := by
        intro n j
        exact Finset.single_le_sum (f := fun j => ((n j : ℝ)) ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ j)
      have hW1 : ∀ n : Fin R → ℕ, 1 ≤ 1 + ∑ j, ((n j : ℝ)) ^ 2 := by
        intro n; have := Finset.sum_nonneg (s := Finset.univ) (fun j _ => sq_nonneg ((n j : ℝ))); linarith
      have hsumW : ∀ f : (Fin R → ℕ) → ℝ, (∀ n, 0 ≤ f n) →
          (∃ K, ∀ n, f n ≤ K * (π n * (1 + ∑ j, ((n j : ℝ)) ^ 2))) → Summable f := by
        rintro f hf0 ⟨K, hK⟩
        exact Summable.of_nonneg_of_le hf0 hK (hW.mul_left K)
      have hnW : ∀ n : Fin R → ℕ, ∀ j, (n j : ℝ) ≤ 1 + ∑ j, ((n j : ℝ)) ^ 2 := by
        intro n j
        have := hWge n j
        nlinarith [sq_nonneg ((n j : ℝ) - 1)]
      -- summabilities of the basic quantities
      have hs_busy : ∀ r, Summable (fun n => π n * P.toPolicy.busy n r) := by
        intro r
        refine hsumW _ (fun n => mul_nonneg (hπ0 n) (hbusy0 n r)) ⟨1, fun n => ?_⟩
        nlinarith [hπ0 n, hbusy1 n r, hW1 n, mul_le_mul_of_nonneg_left (hbusy1 n r) (hπ0 n)]
      have hs_busyj : ∀ r j, Summable (fun n => π n * P.toPolicy.busy n r * (n j : ℝ)) := by
        intro r j
        refine hsumW _ (fun n => mul_nonneg (mul_nonneg (hπ0 n) (hbusy0 n r)) (Nat.cast_nonneg _))
          ⟨1, fun n => ?_⟩
        have h1 := mul_le_mul_of_nonneg_left (hbusy1 n r) (hπ0 n)
        have h2 := hnW n j
        have h3 : (0:ℝ) ≤ n j := Nat.cast_nonneg _
        have h4 := hπ0 n
        calc π n * P.toPolicy.busy n r * (n j : ℝ) ≤ π n * 1 * (n j : ℝ) :=
              mul_le_mul_of_nonneg_right h1 h3
          _ ≤ 1 * (π n * (1 + ∑ j, ((n j : ℝ)) ^ 2)) := by nlinarith
      have hs_D : ∀ r d, Summable (fun n => π n * P.toPolicy.busy n r * P.route n r d) := by
        intro r d
        refine hsumW _ (fun n => mul_nonneg (mul_nonneg (hπ0 n) (hbusy0 n r)) (P.route_nonneg _ _ _))
          ⟨1, fun n => ?_⟩
        have h1 := mul_le_mul_of_nonneg_left (hbusy1 n r) (hπ0 n)
        have h2 := mul_le_mul_of_nonneg_left (hroute1 n r d) (mul_nonneg (hπ0 n) (hbusy0 n r))
        have h4 := hπ0 n
        have := hW1 n
        nlinarith
      have hs_G : ∀ r d j, Summable (fun n => π n * P.toPolicy.busy n r * P.route n r d * (n j : ℝ)) := by
        intro r d j
        refine hsumW _ (fun n => mul_nonneg (mul_nonneg (mul_nonneg (hπ0 n) (hbusy0 n r))
          (P.route_nonneg _ _ _)) (Nat.cast_nonneg _)) ⟨1, fun n => ?_⟩
        have h1 := mul_le_mul_of_nonneg_left (hbusy1 n r) (hπ0 n)
        have h2 := mul_le_mul_of_nonneg_left (hroute1 n r d) (mul_nonneg (hπ0 n) (hbusy0 n r))
        have h3 : (0:ℝ) ≤ n j := Nat.cast_nonneg _
        have h5 := hnW n j
        have h4 := hπ0 n
        have h6 : π n * P.toPolicy.busy n r * P.route n r d ≤ π n := by nlinarith
        calc π n * P.toPolicy.busy n r * P.route n r d * (n j : ℝ) ≤ π n * (n j : ℝ) :=
              mul_le_mul_of_nonneg_right h6 h3
          _ ≤ 1 * (π n * (1 + ∑ j, ((n j : ℝ)) ^ 2)) := by nlinarith
      have hs_m : ∀ j, Summable (fun n => π n * (n j : ℝ)) := by
        intro j
        refine hsumW _ (fun n => mul_nonneg (hπ0 n) (Nat.cast_nonneg _)) ⟨1, fun n => ?_⟩
        have := mul_le_mul_of_nonneg_left (hnW n j) (hπ0 n); linarith
      -- (41), (42)
      have h41 : ∀ r, P.u π r = ∑ d, P.D π r d := by
        intro r
        unfold RoutingPolicy.u RoutingPolicy.D
        rw [← Summable.tsum_finsetSum (fun d _ => hs_D r d)]
        congr 1; funext n
        rw [← Finset.mul_sum, P.route_sum_one, mul_one]
      have h42 : ∀ r j, P.I π r j = ∑ d, P.G π r d j := by
        intro r j
        unfold RoutingPolicy.I RoutingPolicy.G
        rw [← Summable.tsum_finsetSum (fun d _ => hs_G r d j)]
        congr 1; funext n
        rw [← Finset.sum_mul, ← Finset.mul_sum, P.route_sum_one, mul_one]
      have hforb : ∀ r d, d ∉ F r → P.D π r d = 0 ∧ ∀ j, P.G π r d j = 0 := by
        intro r d hd
        refine ⟨?_, fun j => ?_⟩
        · unfold RoutingPolicy.D; simp [P.route_supp _ _ _ hd]
        · unfold RoutingPolicy.G; simp [P.route_supp _ _ _ hd]
      have hstation : ∀ i n, ∑ r ∈ net.C i, P.toPolicy.busy n r ≤ 1 := by
        intro i n
        by_cases h : ∃ r ∈ net.C i, P.toPolicy.serve n r = true
        · obtain ⟨r0, hr0, hs0⟩ := h
          rw [Finset.sum_eq_single r0]
          · exact hbusy1 n r0
          · intro b hb hne
            have hσ : net.σ b = net.σ r0 := by
              simp [Network.C] at hb hr0; rw [hb, hr0]
            have := P.toPolicy.serve_one_class n b r0 hσ hne
            unfold Policy.busy
            have hb' : P.toPolicy.serve n b = false := by
              cases hsb : P.toPolicy.serve n b
              · rfl
              · exact absurd ⟨hsb, hs0⟩ this
            simp [hb']
          · intro h; exact absurd hr0 h
        · push Not at h
          rw [Finset.sum_eq_zero]
          · norm_num
          · intro r hr; unfold Policy.busy; simp [h r hr]
      have h39 : ∀ i, ∑ r ∈ net.C i, P.u π r ≤ 1 := by
        intro i
        unfold RoutingPolicy.u
        rw [← Summable.tsum_finsetSum (fun r _ => hs_busy r)]
        rw [← hπ1.tsum_eq]
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_sum fun r _ => hs_busy r) hπs
        rw [← Finset.mul_sum]
        have := mul_le_mul_of_nonneg_left (hstation i n) (hπ0 n)
        linarith
      have h40 : ∀ i j, ∑ r ∈ net.C i, P.I π r j ≤ meanNum π j := by
        intro i j
        unfold RoutingPolicy.I meanNum
        rw [← Summable.tsum_finsetSum (fun r _ => hs_busyj r j)]
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_sum fun r _ => hs_busyj r j) (hs_m j)
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        have := mul_le_mul_of_nonneg_left (hstation i n) (hπ0 n)
        exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
      have hm0 : ∀ r, 0 ≤ meanNum π r := fun r =>
        tsum_nonneg fun n => mul_nonneg (hπ0 n) (Nat.cast_nonneg _)
      have hu0 : ∀ r, 0 ≤ P.u π r := fun r =>
        tsum_nonneg fun n => mul_nonneg (hπ0 n) (hbusy0 n r)
      have hD0 : ∀ r d, 0 ≤ P.D π r d := fun r d =>
        tsum_nonneg fun n => mul_nonneg (mul_nonneg (hπ0 n) (hbusy0 n r)) (P.route_nonneg _ _ _)
      have hG0 : ∀ r d j, 0 ≤ P.G π r d j := fun r d j =>
        tsum_nonneg fun n => mul_nonneg (mul_nonneg (mul_nonneg (hπ0 n) (hbusy0 n r))
          (P.route_nonneg _ _ _)) (Nat.cast_nonneg _)
      have hI0 : ∀ r j, 0 ≤ P.I π r j := fun r j =>
        tsum_nonneg fun n => mul_nonneg (mul_nonneg (hπ0 n) (hbusy0 n r)) (Nat.cast_nonneg _)
      -- transitions
      obtain ⟨c, hc⟩ : ∃ c : Fin R ⊕ (Fin R × Option (Fin R)) → (Fin R → ℕ) → ℝ,
          c = fun t n => Sum.elim (fun r => net.lam0 r)
            (fun p => P.toPolicy.busy n p.1 * net.μ p.1 * P.route n p.1 p.2) t := ⟨_, rfl⟩
      obtain ⟨φ, hφ⟩ : ∃ φ : Fin R ⊕ (Fin R × Option (Fin R)) → (Fin R → ℕ) → (Fin R → ℕ),
          φ = fun t n => Sum.elim (fun r => n + unitVec r)
            (fun p => n - unitVec p.1 + p.2.elim 0 unitVec) t := ⟨_, rfl⟩
      have hc1 : ∀ r n, c (Sum.inl r) n = net.lam0 r := by intro r n; rw [hc]; rfl
      have hc2 : ∀ r d n, c (Sum.inr (r, d)) n = P.toPolicy.busy n r * net.μ r * P.route n r d := by
        intro r d n; rw [hc]; rfl
      have hφ1 : ∀ r n, φ (Sum.inl r) n = n + unitVec r := by intro r n; rw [hφ]; rfl
      have hφ2 : ∀ r n, φ (Sum.inr (r, none)) n = n - unitVec r := by
        intro r n; rw [hφ]; simp
      have hφ3 : ∀ r s n, φ (Sum.inr (r, some s)) n = n - unitVec r + unitVec s := by
        intro r s n; rw [hφ]; rfl
      have hgen : ∀ g n, P.generator g n = ∑ t, c t n * (g (φ t n) - g n) := by
        intro g n
        simp only [RoutingPolicy.generator, Fintype.sum_sum_type, Fintype.sum_prod_type,
          Fintype.sum_option, hc1, hc2, hφ1, hφ2, hφ3]
        congr 1
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [mul_add, Finset.mul_sum]
        rw [add_comm]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun s _ => by ring
      have hc0 : ∀ t n, 0 ≤ c t n := by
        intro t n
        rcases t with r | ⟨r, d⟩
        · rw [hc1]; exact net.lam0_nonneg r
        · rw [hc2]; exact mul_nonneg (mul_nonneg (hbusy0 n r) (net.μ_pos r).le) (P.route_nonneg _ _ _)
      have hcle : ∀ t n, c t n ≤ ∑ r, net.lam0 r + ∑ r, net.μ r := by
        have hl : 0 ≤ ∑ r, net.lam0 r := Finset.sum_nonneg fun r _ => net.lam0_nonneg r
        have hm : 0 ≤ ∑ r, net.μ r := Finset.sum_nonneg fun r _ => (net.μ_pos r).le
        intro t n
        rcases t with r | ⟨r, d⟩
        · rw [hc1]
          have := Finset.single_le_sum (f := net.lam0) (fun r _ => net.lam0_nonneg r) (Finset.mem_univ r)
          linarith
        · rw [hc2]
          have := Finset.single_le_sum (f := net.μ) (fun r _ => (net.μ_pos r).le) (Finset.mem_univ r)
          have h1 := hbusy1 n r
          have h2 := hroute1 n r d
          have h3 := hbusy0 n r
          have h4 := P.route_nonneg n r d
          have h5 := net.μ_pos r
          have : P.toPolicy.busy n r * net.μ r * P.route n r d ≤ net.μ r := by
            have : P.toPolicy.busy n r * P.route n r d ≤ 1 := by nlinarith
            nlinarith
          linarith
      have hφle : ∀ t n j, φ t n j ≤ n j + 1 := by
        intro t n j
        have hu : ∀ r, unitVec r j ≤ 1 := by
          intro r; unfold unitVec; rw [Pi.single_apply]; split_ifs <;> omega
        rcases t with r | ⟨r, _ | s⟩
        · rw [hφ1]; simp only [Pi.add_apply]; have := hu r; omega
        · rw [hφ2]; simp only [Pi.sub_apply]; omega
        · rw [hφ3]; simp only [Pi.add_apply, Pi.sub_apply]; have := hu s; omega
      have h1 : ∀ (g : (Fin R → ℕ) → ℝ) x, HasSum (fun m => g m * (if x = m then 1 else 0)) (g x) := by
        intro g x
        convert hasSum_ite_eq x (g x) using 1
        funext m
        by_cases h : m = x
        · subst h; simp
        · simp [h, Ne.symm h]
      have lin : ∀ g n, HasSum (fun m => g m * P.generator (fun k => if k = m then 1 else 0) n)
          (P.generator g n) := by
        intro g n
        simp only [hgen]
        have := hasSum_sum (s := Finset.univ) (fun t _ => ((h1 g (φ t n)).sub (h1 g n)).mul_left (c t n))
        rw [show (fun m => g m * ∑ t, c t n * ((if φ t n = m then (1:ℝ) else 0) - if n = m then 1 else 0))
            = fun b => ∑ i, c i n * ((g b * if φ i n = b then 1 else 0) - g b * if n = b then 1 else 0)
            from funext fun m => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => by ring]
        exact this
      have key : ∀ (g : (Fin R → ℕ) → ℝ) (C : ℝ),
          (∀ x n : Fin R → ℕ, (∀ j, x j ≤ n j + 1) → |g x| ≤ C * (1 + ∑ j, ((n j : ℝ)) ^ 2)) →
          ∑' n, π n * P.generator g n = 0 := by
        intro g C hg
        set Fn : (Fin R → ℕ) × (Fin R → ℕ) → ℝ := fun p =>
          π p.1 * (g p.2 * P.generator (fun k => if k = p.2 then 1 else 0) p.1) with hFn
        set H : (Fin R → ℕ) × (Fin R → ℕ) → ℝ := fun p => π p.1 * ∑ t, c t p.1 *
          (|g p.2| * (if φ t p.1 = p.2 then 1 else 0) + |g p.2| * (if p.1 = p.2 then 1 else 0)) with hH
        have hH0 : 0 ≤ H := by
          intro p
          apply mul_nonneg (hπ0 _)
          apply Finset.sum_nonneg
          intro t _
          apply mul_nonneg (hc0 _ _)
          have := abs_nonneg (g p.2)
          split_ifs <;> simp [this]
        have hHfib : ∀ n, HasSum (fun m => H (n, m)) (π n * ∑ t, c t n * (|g (φ t n)| + |g n|)) := by
          intro n
          exact (hasSum_sum fun t _ => ((h1 (fun x => |g x|) (φ t n)).add
            (h1 (fun x => |g x|) n)).mul_left (c t n)).mul_left (π n)
        have hgC : ∀ x n : Fin R → ℕ, (∀ j, x j ≤ n j + 1) → |g x| ≤ C * (1 + ∑ j, ((n j : ℝ)) ^ 2) := hg
        have hHsum : Summable H := by
          refine (summable_prod_of_nonneg hH0).2 ⟨fun n => (hHfib n).summable, ?_⟩
          refine Summable.congr ?_ (fun n => ((hHfib n).tsum_eq).symm)
          refine hsumW _ (fun n => ?_) ⟨(Fintype.card (Fin R ⊕ (Fin R × Option (Fin R))) : ℝ) *
            (∑ r, net.lam0 r + ∑ r, net.μ r) * (2 * C), fun n => ?_⟩
          · exact mul_nonneg (hπ0 n) (Finset.sum_nonneg fun t _ => mul_nonneg (hc0 t n)
              (add_nonneg (abs_nonneg _) (abs_nonneg _)))
          · have hb : ∀ t, c t n * (|g (φ t n)| + |g n|) ≤
                (∑ r, net.lam0 r + ∑ r, net.μ r) * (2 * C * (1 + ∑ j, ((n j : ℝ)) ^ 2)) := by
              intro t
              have e1 := hgC (φ t n) n (hφle t n)
              have e2 := hgC n n (fun j => by omega)
              have e3 : 0 ≤ |g (φ t n)| + |g n| := add_nonneg (abs_nonneg _) (abs_nonneg _)
              exact mul_le_mul (hcle t n) (by linarith) e3 ((hc0 t n).trans (hcle t n))
            have := Finset.sum_le_sum (s := Finset.univ) fun t _ => hb t
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
            have := mul_le_mul_of_nonneg_left this (hπ0 n)
            calc _ ≤ _ := this
              _ = _ := by ring
        have hFsum : Summable Fn := by
          refine Summable.of_norm_bounded hHsum (fun p => ?_)
          rw [Real.norm_eq_abs]
          simp only [hFn, hH, hgen]
          rw [abs_mul, abs_of_nonneg (hπ0 _)]
          apply mul_le_mul_of_nonneg_left _ (hπ0 _)
          rw [Finset.mul_sum]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
          rw [abs_mul, abs_mul, abs_of_nonneg (hc0 _ _)]
          have hab : |((if φ t p.1 = p.2 then (1:ℝ) else 0) - (if p.1 = p.2 then 1 else 0))| ≤
              (if φ t p.1 = p.2 then (1:ℝ) else 0) + (if p.1 = p.2 then 1 else 0) := by
            split_ifs <;> norm_num
          have := abs_nonneg (g p.2)
          have := hc0 t p.1
          nlinarith [mul_le_mul_of_nonneg_left hab (mul_nonneg this (abs_nonneg (g p.2)))]
        calc ∑' n, π n * P.generator g n = ∑' n, ∑' m, Fn (n, m) := by
              congr 1; funext n
              rw [← (lin g n).tsum_eq, ← tsum_mul_left]
          _ = ∑' m, ∑' n, Fn (n, m) := (Summable.tsum_comm (f := fun n m => Fn (n, m)) hFsum).symm
          _ = ∑' m, g m * ∑' n, π n * P.generator (fun k => if k = m then 1 else 0) n := by
              congr 1; funext m
              rw [← tsum_mul_left]; congr 1; funext n; simp only [hFn]; ring
          _ = 0 := by simp [(hbal _).tsum_eq]
      obtain ⟨δ, hδ⟩ : ∃ δ : Fin R ⊕ (Fin R × Option (Fin R)) → Fin R → ℝ,
          δ = fun t a => Sum.elim (fun r => if r = a then (1:ℝ) else 0)
            (fun p => (if p.2 = some a then (1:ℝ) else 0) - (if p.1 = a then 1 else 0)) t := ⟨_, rfl⟩
      have hδ1 : ∀ r a, δ (Sum.inl r) a = if r = a then 1 else 0 := by intro r a; rw [hδ]; rfl
      have hδ2 : ∀ r d a, δ (Sum.inr (r, d)) a =
          (if d = some a then (1:ℝ) else 0) - (if r = a then 1 else 0) := by intro r d a; rw [hδ]; rfl
      have hφδ : ∀ t n a, c t n ≠ 0 → ((φ t n a : ℕ) : ℝ) = n a + δ t a := by
        intro t n a hne
        rcases t with r | ⟨r, d⟩
        · rw [hφ1, hδ1]
          simp only [Pi.add_apply, unitVec, Pi.single_apply]
          by_cases h : a = r
          · subst h; simp
          · simp [h, Ne.symm h]
        · have hs : P.toPolicy.serve n r = true := by
            rw [hc2] at hne
            by_contra hcon
            apply hne
            unfold Policy.busy
            simp [hcon]
          have hn1 := P.toPolicy.serve_present n r hs
          rw [hδ2]
          rcases d with _ | s
          · rw [hφ2]
            simp only [Pi.sub_apply, unitVec, Pi.single_apply]
            by_cases h : a = r
            · subst h; simp; rw [Nat.cast_sub hn1]; push_cast; ring
            · simp [h, Ne.symm h]
          · rw [hφ3]
            simp only [Pi.add_apply, Pi.sub_apply, unitVec, Pi.single_apply, Option.some.injEq]
            by_cases h : a = r
            · subst h
              by_cases h2 : a = s
              · subst h2; simp [Nat.sub_add_cancel hn1]
              · simp [h2, Ne.symm h2]; rw [Nat.cast_sub hn1]; push_cast; ring
            · by_cases h2 : a = s
              · subst h2; simp [h, Ne.symm h]
              · simp [h, Ne.symm h, h2, Ne.symm h2]
      have hsc : ∀ t, Summable (fun n => π n * c t n) := by
        intro t
        refine hsumW _ (fun n => mul_nonneg (hπ0 n) (hc0 t n)) ⟨∑ r, net.lam0 r + ∑ r, net.μ r, fun n => ?_⟩
        have h1 := mul_le_mul_of_nonneg_left (hcle t n) (hπ0 n)
        have h2 := mul_le_mul_of_nonneg_left (hW1 n) (hπ0 n)
        have h3 := (hc0 t n).trans (hcle t n)
        nlinarith
      have hscn : ∀ t j, Summable (fun n => π n * c t n * (n j : ℝ)) := by
        intro t j
        refine hsumW _ (fun n => mul_nonneg (mul_nonneg (hπ0 n) (hc0 t n)) (Nat.cast_nonneg _))
          ⟨∑ r, net.lam0 r + ∑ r, net.μ r, fun n => ?_⟩
        have h1 := mul_le_mul_of_nonneg_left (hcle t n) (hπ0 n)
        have h2 := mul_le_mul_of_nonneg_left (hnW n j) (hπ0 n)
        have h3 := (hc0 t n).trans (hcle t n)
        have h4 : (0:ℝ) ≤ n j := Nat.cast_nonneg _
        have h5 := mul_nonneg (hπ0 n) (hc0 t n)
        calc π n * c t n * (n j : ℝ) ≤ π n * (∑ r, net.lam0 r + ∑ r, net.μ r) * (n j : ℝ) :=
              mul_le_mul_of_nonneg_right h1 h4
          _ = (∑ r, net.lam0 r + ∑ r, net.μ r) * (π n * (n j : ℝ)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left h2 h3
      have ha : ∀ a, ∑ t, δ t a * ∑' n, π n * c t n = 0 := by
        intro a
        have := key (fun x => (x a : ℝ)) 2 (by
          intro x n hj
          have hx : (x a : ℝ) ≤ n a + 1 := by exact_mod_cast hj a
          have := hnW n a
          have := hW1 n
          rw [abs_of_nonneg (Nat.cast_nonneg _)]
          linarith)
        have e : ∀ n, π n * P.generator (fun x => (x a : ℝ)) n = ∑ t, δ t a * (π n * c t n) := by
          intro n
          rw [hgen, Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          by_cases h : c t n = 0
          · simp [h]
          · rw [hφδ t n a h]; ring
        simp only [e] at this
        rw [Summable.tsum_finsetSum (fun t _ => (hsc t).mul_left _)] at this
        simpa only [tsum_mul_left] using this
      have hb : ∀ a b, ∑ t, (δ t b * (∑' n, π n * c t n * (n a : ℝ)) +
          δ t a * (∑' n, π n * c t n * (n b : ℝ)) + δ t a * δ t b * ∑' n, π n * c t n) = 0 := by
        intro a b
        have := key (fun x => (x a : ℝ) * (x b : ℝ)) 2 (by
          intro x n hj
          have hx : (x a : ℝ) ≤ n a + 1 := by exact_mod_cast hj a
          have hy : (x b : ℝ) ≤ n b + 1 := by exact_mod_cast hj b
          have h0 : (0:ℝ) ≤ x a := Nat.cast_nonneg _
          have h0' : (0:ℝ) ≤ x b := Nat.cast_nonneg _
          have h0'' : (0:ℝ) ≤ n a := Nat.cast_nonneg _
          have h0''' : (0:ℝ) ≤ n b := Nat.cast_nonneg _
          have ha' := hWge n a
          have hb' := hWge n b
          rw [abs_of_nonneg (mul_nonneg h0 h0')]
          have : (x a : ℝ) * x b ≤ (n a + 1) * (n b + 1) := mul_le_mul hx hy h0' (by linarith)
          nlinarith [sq_nonneg ((n a : ℝ) - n b), sq_nonneg ((n a : ℝ) - 1), sq_nonneg ((n b : ℝ) - 1)])
        have e : ∀ n, π n * P.generator (fun x => (x a : ℝ) * (x b : ℝ)) n =
            ∑ t, (δ t b * (π n * c t n * (n a : ℝ)) + δ t a * (π n * c t n * (n b : ℝ)) +
              δ t a * δ t b * (π n * c t n)) := by
          intro n
          rw [hgen, Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          by_cases h : c t n = 0
          · simp [h]
          · rw [hφδ t n a h, hφδ t n b h]; ring
        simp only [e] at this
        rw [Summable.tsum_finsetSum (fun t _ => (((hscn t a).mul_left _).add
          ((hscn t b).mul_left _)).add ((hsc t).mul_left _))] at this
        rw [← this]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Summable.tsum_add (((hscn t a).mul_left _).add ((hscn t b).mul_left _)) ((hsc t).mul_left _),
          Summable.tsum_add ((hscn t a).mul_left _) ((hscn t b).mul_left _)]
        simp only [tsum_mul_left]
      have hA1 : ∀ r, ∑' n, π n * c (Sum.inl r) n = net.lam0 r := by
        intro r; simp only [hc1]; rw [tsum_mul_right, hπ1.tsum_eq, one_mul]
      have hA2 : ∀ r d, ∑' n, π n * c (Sum.inr (r, d)) n = net.μ r * P.D π r d := by
        intro r d; simp only [hc2]; unfold RoutingPolicy.D; rw [← tsum_mul_left]
        congr 1; funext n; ring
      have hB1 : ∀ r j, ∑' n, π n * c (Sum.inl r) n * (n j : ℝ) = net.lam0 r * meanNum π j := by
        intro r j; simp only [hc1]; unfold meanNum; rw [← tsum_mul_left]
        congr 1; funext n; ring
      have hB2 : ∀ r d j, ∑' n, π n * c (Sum.inr (r, d)) n * (n j : ℝ) = net.μ r * P.G π r d j := by
        intro r d j; simp only [hc2]; unfold RoutingPolicy.G; rw [← tsum_mul_left]
        congr 1; funext n; ring
      have e36 : ∀ r, _ := fun r => ha r
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, hδ1, hδ2, hA1, hA2] at e36
      simp [sub_mul, mul_sub, ite_mul, mul_ite, Finset.sum_sub_distrib, Finset.sum_add_distrib] at e36
      have e37 : ∀ r, _ := fun r => hb r r
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, hδ1, hδ2, hA1, hA2, hB1, hB2] at e37
      simp [sub_mul, mul_sub, ite_mul, mul_ite, Finset.sum_sub_distrib, Finset.sum_add_distrib] at e37
      have e38 : ∀ r r', _ := fun r r' => hb r r'
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, hδ1, hδ2, hA1, hA2, hB1, hB2] at e38
      simp [sub_mul, mul_sub, ite_mul, mul_ite, Finset.sum_sub_distrib, Finset.sum_add_distrib] at e38
      have hu' : ∀ r, net.μ r * P.u π r = net.μ r * P.D π r none + ∑ i, net.μ r * P.D π r (some i) := by
        intro r; rw [h41, Fintype.sum_option, mul_add, Finset.mul_sum]
      have hI' : ∀ r j, net.μ r * P.I π r j =
          net.μ r * P.G π r none j + ∑ i, net.μ r * P.G π r (some i) j := by
        intro r j; rw [h42, Fintype.sum_option, mul_add, Finset.mul_sum]
      refine ⟨fun r => ?_, fun r => ?_, fun r r' hr => ?_, h39, h40, h41, h42, hforb, hm0, hu0, hD0, hG0, hI0⟩
      · linarith [e36 r, hu' r]
      · rw [Finset.sum_erase_eq_sub (Finset.mem_univ r)]
        linarith [e37 r, hu' r, hI' r r]
      · have hne : r' ≠ r := ne_of_lt hr
        have := e38 r r'
        simp only [hne, if_false] at this
        linarith [hI' r r', hI' r' r]
