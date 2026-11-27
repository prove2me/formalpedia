-- Prove2me | solution 1 for MLRPCake.EnvyFree.Supplement.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:11:58.726381+00:00
-- url     : https://prove2.me/submissions/3b51471e-6a4b-4c96-bc90-e5e30fe9cec5

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_Divisions
import Definitions.Def_MLRPCake_EnvyFree_Supplement_NashDP

open MLRPCake
open MLRPCake.EnvyFree
open MLRPCake.EnvyFree.Supplement

/-- Theorem 5, p. 9: under MLRP and `λ`-Lipschitz queries, for every `ε > 0` the §9 algorithm
(value grid of cells worth at most `ε/(8n)` to every agent, then the Nash-product dynamic
program) returns an allocation whose Nash social welfare is at least `(1 - ε)` times that of
every allocation, with work polynomial in `n`, `1/ε` and `log λ`. -/
theorem solution : ∃ c : ℕ, ∀ (n : ℕ) (f : Fin n → ℝ → ℝ) (lam ε : ℝ),
    1 ≤ n → IsInstance f → IsMLRP f → 1 ≤ lam → QueriesLipschitz f lam → 0 < ε →
    IsAllocation (n := n) (nashOutput f ε) ∧
      (∀ (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)), IsAllocation (n := n) x →
        (1 - ε) * NSW f x σ ≤ NSW f (nashOutput f ε) (Equiv.refl (Fin n))) ∧
      (nashCost n ε : ℝ) ≤ c * ((n : ℝ) + 1 / ε + Real.logb 2 lam + 1) ^ c := by
        obtain ⟨c, hc0⟩ : ∃ c : ℕ, 200 ≤ c := ⟨200, le_rfl⟩
        have hc200 : (200:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc0
        refine ⟨c, ?_⟩
        intro n f lam ε hn hI hM hlam hQ hε
        have hCost : (nashCost n ε : ℝ) ≤ (c:ℝ) * ((n : ℝ) + 1 / ε + Real.logb 2 lam + 1) ^ c := by
          set X : ℝ := (n : ℝ) + 1 / ε + Real.logb 2 lam + 1 with hX
          have hlog : 0 ≤ Real.logb 2 lam := Real.logb_nonneg (by norm_num) hlam
          have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
          have hie : 0 < 1 / ε := by positivity
          have hX2 : 2 ≤ X := by linarith
          have hX1 : 1 ≤ X := by linarith
          have hnX : (n:ℝ) ≤ X := by linarith
          have heX : 1 / ε ≤ X := by linarith
          have hXnn : 0 ≤ X := by linarith
          clear_value X
          set N := nashLen n ε with hNdef
          have hN : (N : ℝ) ≤ 8 * X ^ 3 + 2 := by
            have h1 : (N:ℝ) = (⌈8 * (n : ℝ) ^ 2 / ε⌉₊ : ℝ) + 1 := by
              simp [hNdef, nashLen]
            have h2 : (⌈8 * (n : ℝ) ^ 2 / ε⌉₊ : ℝ) < 8 * (n : ℝ) ^ 2 / ε + 1 :=
              Nat.ceil_lt_add_one (by positivity)
            have h3 : 8 * (n : ℝ) ^ 2 / ε ≤ 8 * X ^ 3 := by
              have : 8 * (n : ℝ) ^ 2 / ε = 8 * ((n:ℝ) ^ 2 * (1 / ε)) := by ring
              rw [this]
              have : (n:ℝ) ^ 2 * (1 / ε) ≤ X ^ 2 * X := by
                apply mul_le_mul (pow_le_pow_left₀ (by positivity) hnX 2) heX (by positivity) (by positivity)
              have e0 : X ^ 2 * X = X ^ 3 := by ring
              rw [e0] at this
              linarith
            linarith
          have hN2 : (N : ℝ) + 2 ≤ 11 * X ^ 3 := by
            have h8 : (2:ℝ) ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ (by norm_num) hX2 3
            norm_num at h8
            linarith
          have hcost : (nashCost n ε : ℝ) ≤ n * N + (N + 1) + n * ((N + 1) * (N + 2)) := by
            simp only [nashCost, dpQueries]
            push_cast
            have hdiv : (((N + 1) * (N + 1 + 1) / 2 : ℕ) : ℝ) ≤ ((N:ℝ) + 1) * ((N:ℝ) + 2) := by
              have := Nat.div_le_self ((N + 1) * (N + 1 + 1)) 2
              have h' : (((N + 1) * (N + 1 + 1) / 2 : ℕ) : ℝ) ≤ (((N + 1) * (N + 1 + 1) : ℕ) : ℝ) := by
                exact_mod_cast this
              push_cast at h'
              linarith
            have hsub : (((n - 1 : ℕ)) : ℝ) ≤ n := by
              have : n - 1 ≤ n := Nat.sub_le n 1
              exact_mod_cast this
            have hpos : (0:ℝ) ≤ (((N + 1) * (N + 1 + 1) / 2 : ℕ) : ℝ) := by positivity
            calc (n:ℝ) * N + (N + 1 + (((n - 1 : ℕ)) : ℝ) * (((N + 1) * (N + 1 + 1) / 2 : ℕ) : ℝ))
                ≤ n * N + (N + 1 + n * (((N + 1) * (N + 1 + 1) / 2 : ℕ) : ℝ)) := by
                  gcongr
              _ ≤ n * N + (N + 1) + n * ((N + 1) * (N + 2)) := by
                  have := mul_le_mul_of_nonneg_left hdiv (by positivity : (0:ℝ) ≤ n)
                  linarith
          have hN0 : (0:ℝ) ≤ N := by positivity
          have hb : (n:ℝ) * N + (N + 1) + n * ((N + 1) * (N + 2)) ≤ 200 * X ^ 7 := by
            have a1 : (n:ℝ) * N ≤ X * (11 * X ^ 3) := mul_le_mul hnX (by linarith) hN0 (by linarith)
            have a2 : ((N:ℝ) + 1) * (N + 2) ≤ (11 * X ^ 3) * (11 * X ^ 3) :=
              mul_le_mul (by linarith) hN2 (by positivity) (by positivity)
            have a3 : (n:ℝ) * ((N + 1) * (N + 2)) ≤ X * ((11 * X ^ 3) * (11 * X ^ 3)) :=
              mul_le_mul hnX a2 (by positivity) (by linarith)
            have x4 : X ^ 4 ≤ X ^ 7 := pow_le_pow_right₀ hX1 (by norm_num)
            have x3 : X ^ 3 ≤ X ^ 7 := pow_le_pow_right₀ hX1 (by norm_num)
            have e1 : X * (11 * X ^ 3) = 11 * X ^ 4 := by ring
            have e2 : X * ((11 * X ^ 3) * (11 * X ^ 3)) = 121 * X ^ 7 := by ring
            rw [e1] at a1
            rw [e2] at a3
            linarith
          have hc : 200 * X ^ 7 ≤ (c:ℝ) * X ^ c := by
            have : X ^ 7 ≤ X ^ c := pow_le_pow_right₀ hX1 (by omega)
            exact mul_le_mul hc200 this (by positivity) (by positivity)
          exact le_trans hcost (le_trans hb hc)
        classical
        have hD : ∀ k, k < n → IsDensity (dens f k) := fun k hk => by
          simp only [dens, dif_pos hk]; exact hI ⟨k, hk⟩
        have hII : ∀ k, k < n → ∀ a b, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
            IntervalIntegrable (dens f k) MeasureTheory.volume a b := by
          intro k hk a b ha0 ha1 hb0 hb1
          apply (hD k hk).2.2.1.mono_set
          rw [Set.uIcc_of_le (zero_le_one' ℝ)]
          intro x hx
          rcases Set.mem_uIcc.1 hx with h | h <;> constructor <;> linarith [h.1, h.2]
        have hnonneg : ∀ k, k < n → ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 → 0 ≤ val f k a b := by
          intro k hk a b ha hab hb
          unfold val
          apply intervalIntegral.integral_nonneg hab
          intro x hx
          exact (hD k hk).1 x ⟨by linarith [hx.1], by linarith [hx.2]⟩
        have hadd : ∀ k, k < n → ∀ a b c, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → 0 ≤ c → c ≤ 1 →
            val f k a b + val f k b c = val f k a c := by
          intro k hk a b c ha0 ha1 hb0 hb1 hc0 hc1
          unfold val
          exact intervalIntegral.integral_add_adjacent_intervals (hII k hk a b ha0 ha1 hb0 hb1)
            (hII k hk b c hb0 hb1 hc0 hc1)
        have hle1 : ∀ k, k < n → ∀ c, 0 ≤ c → c ≤ 1 → val f k 0 c ≤ 1 := by
          intro k hk c hc0 hc1
          have h1 : val f k 0 1 = 1 := (hD k hk).2.2.2
          have := hadd k hk 0 c 1 le_rfl zero_le_one hc0 hc1 zero_le_one le_rfl
          have := hnonneg k hk c 1 hc0 hc1 le_rfl
          linarith
        have hE1 : ∃ z : ℕ → ℝ, z 0 = 0 ∧ z n = 1 ∧ (∀ k < n, z k ≤ z (k+1)) ∧ (∀ k, 0 ≤ z k ∧ z k ≤ 1) ∧
            (∀ k, k < n → 0 < val f k (z k) (z (k+1))) ∧
            ∀ k, k + 1 < n → ∀ q, z k ≤ q → q ≤ z (k+2) →
              val f k (z k) q * val f (k+1) q (z (k+2)) ≤
                val f k (z k) (z (k+1)) * val f (k+1) (z (k+1)) (z (k+2)) := by
          have hn0 : (0:ℝ) < n := by exact_mod_cast hn
          let K : Set (ℕ → ℝ) := {z | (∀ k, z k ∈ Set.Icc (0:ℝ) 1) ∧ z 0 = 0 ∧ z n = 1 ∧ ∀ k < n, z k ≤ z (k+1)}
          let P : (ℕ → ℝ) → ℝ := fun z => ∏ k ∈ Finset.range n, val f k (z k) (z (k+1))
          have hKc : IsCompact K := by
            have h1 : IsCompact (Set.pi Set.univ (fun _ : ℕ => Set.Icc (0:ℝ) 1)) :=
              isCompact_univ_pi (fun _ => isCompact_Icc)
            have hcl : IsClosed {z : ℕ → ℝ | z 0 = 0 ∧ z n = 1 ∧ ∀ k < n, z k ≤ z (k+1)} := by
              refine IsClosed.and (isClosed_eq (continuous_apply 0) continuous_const) (IsClosed.and (isClosed_eq (continuous_apply n) continuous_const) ?_)
              have : {z : ℕ → ℝ | ∀ k < n, z k ≤ z (k+1)} = ⋂ k, ⋂ (_ : k < n), {z | z k ≤ z (k+1)} := by
                ext z; simp
              rw [this]
              exact isClosed_iInter fun k => isClosed_iInter fun _ =>
                isClosed_le (continuous_apply k) (continuous_apply (k+1))
            have := h1.inter_right hcl
            convert this using 1
            ext z
            simp only [K, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, true_imp_iff]
          have hFc : ∀ k, k < n → ContinuousOn (fun t => val f k 0 t) (Set.Icc 0 1) := by
            intro k hk
            have := intervalIntegral.continuousOn_primitive_interval'
              (hII k hk 0 1 le_rfl zero_le_one zero_le_one le_rfl) (Set.left_mem_uIcc (a := (0:ℝ)) (b := 1))
            rw [Set.uIcc_of_le zero_le_one] at this
            exact this
          have hPc : ContinuousOn P K := by
            apply continuousOn_finsetProd
            intro k hk
            have hk' := Finset.mem_range.1 hk
            have e : Set.EqOn (fun z : ℕ → ℝ => val f k (z k) (z (k+1)))
                (fun z => val f k 0 (z (k+1)) - val f k 0 (z k)) K := by
              intro z hz
              have := hadd k hk' 0 (z k) (z (k+1)) le_rfl zero_le_one (hz.1 k).1 (hz.1 k).2 (hz.1 (k+1)).1 (hz.1 (k+1)).2
              simp only
              linarith
            refine ContinuousOn.congr ?_ e
            exact ((hFc k hk').comp (continuous_apply (k+1)).continuousOn (fun z hz => hz.1 (k+1))).sub
              ((hFc k hk').comp (continuous_apply k).continuousOn (fun z hz => hz.1 k))
          have hposv : ∀ k, k < n → ∀ a b, 0 ≤ a → a < b → b ≤ 1 → 0 < val f k a b := by
            intro k hk a b ha hab hb
            unfold val
            apply intervalIntegral.intervalIntegral_pos_of_pos_on
              (hII k hk a b ha (by linarith) (by linarith) hb) _ hab
            intro t ht
            simp only [dens, dif_pos hk]
            exact hM.1 ⟨k, hk⟩ t ⟨by linarith [ht.1], by linarith [ht.2]⟩
          let z0 : ℕ → ℝ := fun k => min ((k:ℝ) / n) 1
          have hz0K : z0 ∈ K := by
            refine ⟨fun k => ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩, ?_, ?_, ?_⟩
            · simp [z0]
            · simp [z0, div_self hn0.ne']
            · intro k _
              apply min_le_min_right
              push_cast
              gcongr
              linarith
          have hz0P : 0 < P z0 := by
            apply Finset.prod_pos
            intro k hk
            have hk' := Finset.mem_range.1 hk
            apply hposv k hk' _ _ (hz0K.1 k).1 _ (hz0K.1 (k+1)).2
            have h1 : ((k:ℝ) + 1) ≤ n := by exact_mod_cast hk'
            have h2 : ((k:ℝ) + 1) / n ≤ 1 := (div_le_one hn0).2 h1
            have h3 : (k:ℝ) / n < ((k:ℝ) + 1) / n := by gcongr; linarith
            simp only [z0]
            push_cast
            rw [min_eq_left h2, min_eq_left (by linarith)]
            exact h3
          obtain ⟨z, hzK, hzmax⟩ := hKc.exists_isMaxOn ⟨z0, hz0K⟩ hPc
          have hPz : 0 < P z := lt_of_lt_of_le hz0P (hzmax hz0K)
          have hge : ∀ k, k < n → 0 ≤ val f k (z k) (z (k+1)) := fun k hk =>
            hnonneg k hk _ _ (hzK.1 k).1 (hzK.2.2.2 k hk) (hzK.1 (k+1)).2
          have hvpos : ∀ k, k < n → 0 < val f k (z k) (z (k+1)) := by
            intro k hk
            refine lt_of_le_of_ne (hge k hk) (fun h => ?_)
            have : P z = 0 := Finset.prod_eq_zero (Finset.mem_range.2 hk) h.symm
            linarith
          refine ⟨z, hzK.2.1, hzK.2.2.1, hzK.2.2.2, hzK.1, hvpos, ?_⟩
          intro k hk q hq1 hq2
          let z' : ℕ → ℝ := fun j => if j = k + 1 then q else z j
          have hq0 : 0 ≤ q := le_trans (hzK.1 k).1 hq1
          have hq01 : q ≤ 1 := le_trans hq2 (hzK.1 (k+2)).2
          have hz'K : z' ∈ K := by
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro j
              simp only [z']
              split_ifs
              · exact ⟨hq0, hq01⟩
              · exact hzK.1 j
            · simp only [z']; rw [if_neg (by omega)]; exact hzK.2.1
            · simp only [z']; rw [if_neg (by omega)]; exact hzK.2.2.1
            · intro j hj
              simp only [z']
              by_cases h1 : j = k + 1
              · subst h1; rw [if_pos rfl, if_neg (by omega)]; exact hq2
              · by_cases h2 : j = k
                · subst h2; rw [if_neg (by omega), if_pos rfl]; exact hq1
                · rw [if_neg h1, if_neg (by omega)]; exact hzK.2.2.2 j hj
          have hle : P z' ≤ P z := hzmax hz'K
          have hsplit : ∀ y : ℕ → ℝ, P y = val f k (y k) (y (k+1)) * (val f (k+1) (y (k+1)) (y (k+1+1)) *
              ∏ j ∈ ((Finset.range n).erase k).erase (k+1), val f j (y j) (y (j+1))) := by
            intro y
            rw [Finset.mul_prod_erase ((Finset.range n).erase k) (fun j => val f j (y j) (y (j+1)))
              (Finset.mem_erase.2 ⟨by omega, Finset.mem_range.2 hk⟩),
              Finset.mul_prod_erase (Finset.range n) (fun j => val f j (y j) (y (j+1)))
              (Finset.mem_range.2 (by omega))]
          have hR : ∏ j ∈ ((Finset.range n).erase k).erase (k+1), val f j (z' j) (z' (j+1)) =
              ∏ j ∈ ((Finset.range n).erase k).erase (k+1), val f j (z j) (z (j+1)) := by
            apply Finset.prod_congr rfl
            intro j hj
            have h1 : j ≠ k + 1 := (Finset.mem_erase.1 hj).1
            have h2 : j ≠ k := (Finset.mem_erase.1 (Finset.mem_erase.1 hj).2).1
            simp only [z']
            rw [if_neg h1, if_neg (by omega)]
          have hRpos : 0 < ∏ j ∈ ((Finset.range n).erase k).erase (k+1), val f j (z j) (z (j+1)) := by
            apply Finset.prod_pos
            intro j hj
            exact hvpos j (Finset.mem_range.1 (Finset.mem_erase.1 (Finset.mem_erase.1 hj).2).2)
          rw [hsplit z', hsplit z, hR, ← mul_assoc, ← mul_assoc] at hle
          have hfin := le_of_mul_le_mul_right hle hRpos
          have e1 : z' k = z k := by simp [z']
          have e2 : z' (k+1) = q := by simp [z']
          have e3 : z' (k+1+1) = z (k+2) := by simp [z']
          rw [e1, e2, e3] at hfin
          exact hfin
        have hE2 : ∀ z : ℕ → ℝ, z 0 = 0 → z n = 1 → (∀ k < n, z k ≤ z (k+1)) → (∀ k, 0 ≤ z k ∧ z k ≤ 1) →
            (∀ k, k < n → 0 < val f k (z k) (z (k+1))) →
            (∀ k, k + 1 < n → ∀ q, z k ≤ q → q ≤ z (k+2) →
              val f k (z k) q * val f (k+1) q (z (k+2)) ≤
                val f k (z k) (z (k+1)) * val f (k+1) (z (k+1)) (z (k+2))) →
            (∀ k, k < n → 1 ≤ n * val f k (z k) (z (k+1))) ∧
            ∀ (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)), IsAllocation (n := n) x → (∀ k, k ≤ n → 0 ≤ x k ∧ x k ≤ 1) →
              ∑ i : Fin n, pieceVal f x σ i / val f i (z i) (z ((i:ℕ)+1)) ≤ n := by
          intro z hz0 hzn hzm hz01 hw hopt
          have hn0 : (0:ℝ) < n := by exact_mod_cast hn
          have hfpos : ∀ k, k < n → ∀ t, 0 ≤ t → t ≤ 1 → 0 < dens f k t := by
            intro k hk t h0 h1
            simp only [dens, dif_pos hk]
            exact hM.1 ⟨k, hk⟩ t ⟨h0, h1⟩
          have hratio : ∀ k, k + 1 < n → ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 →
              dens f (k+1) s * dens f k t ≤ dens f (k+1) t * dens f k s := by
            intro k hk s t h0 hst h1
            have := hM.2 ⟨k, by omega⟩ ⟨k+1, hk⟩ rfl s t h0 hst h1
            have p1 := hfpos k (by omega) s h0 (by linarith)
            have p2 := hfpos k (by omega) t (by linarith) h1
            simp only [dens, dif_pos hk, dif_pos (show k < n by omega)] at p1 p2 ⊢
            rwa [div_le_div_iff₀ p1 p2] at this
          -- value monotone comparison
          have hcmp : ∀ k, k < n → ∀ j, j < n → ∀ a b α β, 0 ≤ a → a ≤ b → b ≤ 1 →
              (∀ t ∈ Set.Icc a b, α * dens f k t ≤ β * dens f j t) → α * val f k a b ≤ β * val f j a b := by
            intro k hk j hj a b α β ha hab hb h
            unfold val
            rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
            exact intervalIntegral.integral_mono_on hab
              ((hII k hk a b ha (by linarith) (by linarith) hb).const_mul _)
              ((hII j hj a b ha (by linarith) (by linarith) hb).const_mul _) h
          have hposv : ∀ k, k < n → ∀ a b, 0 ≤ a → a < b → b ≤ 1 → 0 < val f k a b := by
            intro k hk a b ha hab hb
            unfold val
            apply intervalIntegral.intervalIntegral_pos_of_pos_on
              (hII k hk a b ha (by linarith) (by linarith) hb) _ hab
            intro t ht
            exact hfpos k hk t (by linarith [ht.1]) (by linarith [ht.2])
          have hzlt : ∀ k, k < n → z k < z (k+1) := by
            intro k hk
            refine lt_of_le_of_ne (hzm k hk) (fun h => ?_)
            have := hw k hk
            rw [← h] at this
            simp [val] at this
          -- small pieces
          have hsmall : ∀ k, k < n → ∀ c, 0 ≤ c → c ≤ 1 → ∀ δ, 0 < δ →
              (∀ a, 0 ≤ a → a < c → ∃ q, a ≤ q ∧ q < c ∧ val f k q c < δ) ∧
              (∀ b, b ≤ 1 → c < b → ∃ q, q ≤ b ∧ c < q ∧ val f k c q < δ) := by
            intro k hk c hc0 hc1 δ hδ
            have hco : ContinuousOn (fun y => val f k c y) (Set.Icc 0 1) := by
              have := intervalIntegral.continuousOn_primitive_interval'
                (hII k hk 0 1 le_rfl zero_le_one zero_le_one le_rfl)
                (show c ∈ Set.uIcc (0:ℝ) 1 by rw [Set.uIcc_of_le zero_le_one]; exact ⟨hc0, hc1⟩)
              rw [Set.uIcc_of_le zero_le_one] at this
              exact this
            obtain ⟨η, hη, hη2⟩ := Metric.continuousOn_iff.1 hco c ⟨hc0, hc1⟩ δ hδ
            have hcc : val f k c c = 0 := by simp [val]
            constructor
            · intro a ha hac
              refine ⟨max a (c - η/2), le_max_left _ _, max_lt hac (by linarith), ?_⟩
              have hm0 : 0 ≤ max a (c - η/2) := le_trans ha (le_max_left _ _)
              have hmc : max a (c - η/2) < c := max_lt hac (by linarith)
              have := hη2 (max a (c - η/2)) ⟨hm0, by linarith⟩ (by
                rw [Real.dist_eq, abs_lt]; constructor <;> linarith [le_max_right a (c - η/2)])
              simp only [hcc, Real.dist_eq, sub_zero] at this
              have h2 := hadd k hk c (max a (c - η/2)) c hc0 hc1 hm0 (by linarith) hc0 hc1
              rw [hcc] at h2
              have := (abs_lt.1 this).1
              linarith
            · intro b hb hcb
              refine ⟨min b (c + η/2), min_le_left _ _, lt_min hcb (by linarith), ?_⟩
              have hmc : c < min b (c + η/2) := lt_min hcb (by linarith)
              have := hη2 (min b (c + η/2)) ⟨by linarith, le_trans (min_le_left _ _) hb⟩ (by
                rw [Real.dist_eq, abs_lt]; constructor <;> linarith [min_le_right b (c + η/2)])
              simp only [hcc, Real.dist_eq, sub_zero] at this
              exact (abs_lt.1 this).2
          -- pointwise first-order conditions
          have hL : ∀ k, k + 1 < n → ∀ t, 0 ≤ t → t < z (k+1) →
              val f k (z k) (z (k+1)) * dens f (k+1) t ≤ val f (k+1) (z (k+1)) (z (k+2)) * dens f k t := by
            intro k hk t ht0 ht
            by_contra hcon
            push Not at hcon
            have hk' : k < n := by omega
            set u := val f k (z k) (z (k+1)) with hu
            set v := val f (k+1) (z (k+1)) (z (k+2)) with hv
            have hupos : 0 < u := hw k hk'
            have hvpos : 0 < v := hw (k+1) hk
            have hft := hfpos k hk' t ht0 (by linarith [(hz01 (k+1)).2])
            have hft2 := hfpos (k+1) hk t ht0 (by linarith [(hz01 (k+1)).2])
            obtain ⟨δ, hδ, hδ2⟩ : ∃ δ, 0 < δ ∧ (v + δ) * dens f k t < u * dens f (k+1) t :=
              ⟨(u * dens f (k+1) t - v * dens f k t) / (2 * dens f k t), by
                apply div_pos <;> linarith, by
                have : (u * dens f (k+1) t - v * dens f k t) / (2 * dens f k t) * dens f k t =
                  (u * dens f (k+1) t - v * dens f k t) / 2 := by field_simp
                rw [add_mul, this]; linarith⟩
            obtain ⟨q, hq1, hq2, hq3⟩ := (hsmall (k+1) hk (z (k+1)) (hz01 _).1 (hz01 _).2 δ hδ).1
              (max t (z k)) (le_trans ht0 (le_max_left _ _)) (max_lt ht (hzlt k hk'))
            have hqt : t ≤ q := le_trans (le_max_left _ _) hq1
            have hqz : z k ≤ q := le_trans (le_max_right _ _) hq1
            have hq0 : 0 ≤ q := by linarith
            have hq01 : q ≤ 1 := by linarith [(hz01 (k+1)).2]
            have ho := hopt k hk q hqz (le_trans hq2.le (hzm (k+1) hk))
            have a1 := hadd k hk' (z k) q (z (k+1)) (hz01 _).1 (hz01 _).2 hq0 hq01 (hz01 _).1 (hz01 _).2
            have a2 := hadd (k+1) hk q (z (k+1)) (z (k+2)) hq0 hq01 (hz01 _).1 (hz01 _).2 (hz01 _).1 (hz01 _).2
            have hapos := hposv k hk' q (z (k+1)) hq0 hq2 (hz01 _).2
            have hc : dens f (k+1) t * val f k q (z (k+1)) ≤ dens f k t * val f (k+1) q (z (k+1)) := by
              apply hcmp k hk' (k+1) hk _ _ _ _ hq0 hq2.le (hz01 _).2
              intro s hs
              have := hratio k hk t s ht0 (by linarith [hs.1]) (by linarith only [hs.2, (hz01 (k+1)).2])
              linarith only [this]
            set a := val f k q (z (k+1)) with ha
            set b := val f (k+1) q (z (k+1)) with hb
            have e1 : val f k (z k) q = u - a := by linarith only [a1]
            have e2 : val f (k+1) q (z (k+2)) = b + v := by linarith only [a2]
            rw [e1, e2] at ho
            have h1 : u * b ≤ a * (v + b) := by linarith only [ho]
            have h2 : a * (v + b) < a * (v + δ) := by
              apply mul_lt_mul_of_pos_left _ hapos; linarith only [hq3]
            have h3 : u * b < a * (v + δ) := lt_of_le_of_lt h1 h2
            have h4 : u * b * dens f k t < a * (v + δ) * dens f k t := mul_lt_mul_of_pos_right h3 hft
            have h5 : u * (dens f (k+1) t * a) ≤ u * (dens f k t * b) := mul_le_mul_of_nonneg_left hc hupos.le
            have h6 : a * ((v + δ) * dens f k t) < a * (u * dens f (k+1) t) := mul_lt_mul_of_pos_left hδ2 hapos
            linarith only [h4, h5, h6]
          have hRt : ∀ k, k + 1 < n → ∀ t, t ≤ 1 → z (k+1) < t →
              val f (k+1) (z (k+1)) (z (k+2)) * dens f k t ≤ val f k (z k) (z (k+1)) * dens f (k+1) t := by
            intro k hk t ht1 ht
            by_contra hcon
            push Not at hcon
            have hk' : k < n := by omega
            set u := val f k (z k) (z (k+1)) with hu
            set v := val f (k+1) (z (k+1)) (z (k+2)) with hv
            have hupos : 0 < u := hw k hk'
            have hvpos : 0 < v := hw (k+1) hk
            have ht0 : 0 ≤ t := by linarith [(hz01 (k+1)).1]
            have hft := hfpos k hk' t ht0 ht1
            have hft2 := hfpos (k+1) hk t ht0 ht1
            obtain ⟨δ, hδ, hδ2⟩ : ∃ δ, 0 < δ ∧ (u + δ) * dens f (k+1) t < v * dens f k t :=
              ⟨(v * dens f k t - u * dens f (k+1) t) / (2 * dens f (k+1) t), by
                apply div_pos <;> linarith, by
                have : (v * dens f k t - u * dens f (k+1) t) / (2 * dens f (k+1) t) * dens f (k+1) t =
                  (v * dens f k t - u * dens f (k+1) t) / 2 := by field_simp
                rw [add_mul, this]; linarith⟩
            obtain ⟨q, hq1, hq2, hq3⟩ := (hsmall k hk' (z (k+1)) (hz01 _).1 (hz01 _).2 δ hδ).2
              (min t (z (k+2))) (le_trans (min_le_left _ _) ht1) (lt_min ht (hzlt (k+1) hk))
            have hqt : q ≤ t := le_trans hq1 (min_le_left _ _)
            have hqz : q ≤ z (k+2) := le_trans hq1 (min_le_right _ _)
            have hq0 : 0 ≤ q := by linarith [(hz01 (k+1)).1]
            have hq01 : q ≤ 1 := by linarith
            have ho := hopt k hk q (le_trans (hzm k hk') hq2.le) hqz
            have a1 := hadd k hk' (z k) (z (k+1)) q (hz01 _).1 (hz01 _).2 (hz01 _).1 (hz01 _).2 hq0 hq01
            have a2 := hadd (k+1) hk (z (k+1)) q (z (k+2)) (hz01 _).1 (hz01 _).2 hq0 hq01 (hz01 _).1 (hz01 _).2
            have hbpos := hposv (k+1) hk (z (k+1)) q (hz01 _).1 hq2 hq01
            have hc : dens f k t * val f (k+1) (z (k+1)) q ≤ dens f (k+1) t * val f k (z (k+1)) q := by
              apply hcmp (k+1) hk k hk' _ _ _ _ (hz01 _).1 hq2.le hq01
              intro s hs
              have := hratio k hk s t (by linarith [hs.1, (hz01 (k+1)).1]) (by linarith only [hs.2, hqt, ht1, hs.1]) ht1
              linarith only [this]
            set a := val f k (z (k+1)) q with ha
            set b := val f (k+1) (z (k+1)) q with hb
            have e1 : val f k (z k) q = u + a := by linarith only [a1]
            have e2 : val f (k+1) q (z (k+2)) = v - b := by linarith only [a2]
            rw [e1, e2] at ho
            have h1 : a * v ≤ b * (u + a) := by linarith only [ho]
            have h2 : b * (u + a) < b * (u + δ) := by
              apply mul_lt_mul_of_pos_left _ hbpos; linarith only [hq3]
            have h3 : a * v < b * (u + δ) := lt_of_le_of_lt h1 h2
            have h4 : a * v * dens f (k+1) t < b * (u + δ) * dens f (k+1) t := mul_lt_mul_of_pos_right h3 hft2
            have h5 : v * (dens f k t * b) ≤ v * (dens f (k+1) t * a) := mul_le_mul_of_nonneg_left hc hvpos.le
            have h6 : b * ((u + δ) * dens f (k+1) t) < b * (v * dens f k t) := mul_lt_mul_of_pos_left hδ2 hbpos
            linarith only [h4, h5, h6]
          let φ : ℕ → ℝ → ℝ := fun k t => (val f k (z k) (z (k+1)))⁻¹ * dens f k t
          have hzmono : ∀ i j, i ≤ j → j ≤ n → z i ≤ z j := by
            intro i j hij
            induction j, hij using Nat.le_induction with
            | base => intro _; exact le_rfl
            | succ j hj ih => intro h; exact le_trans (ih (by omega)) (hzm j (by omega))
          have hφL : ∀ k, k + 1 < n → ∀ t, 0 ≤ t → t < z (k+1) → φ (k+1) t ≤ φ k t := by
            intro k hk t h0 h1
            have := hL k hk t h0 h1
            simp only [φ]
            rw [inv_mul_eq_div, inv_mul_eq_div, div_le_div_iff₀ (hw (k+1) hk) (hw k (by omega))]
            linarith
          have hφR : ∀ k, k + 1 < n → ∀ t, t ≤ 1 → z (k+1) < t → φ k t ≤ φ (k+1) t := by
            intro k hk t h0 h1
            have := hRt k hk t h0 h1
            simp only [φ]
            rw [inv_mul_eq_div, inv_mul_eq_div, div_le_div_iff₀ (hw k (by omega)) (hw (k+1) hk)]
            linarith
          have hmaxφ : ∀ k, k < n → ∀ t, z k < t → t < z (k+1) → ∀ i, i < n → φ i t ≤ φ k t := by
            intro k hk t h1 h2 i hi
            have ht0 : 0 ≤ t := by linarith [(hz01 k).1]
            have ht1 : t ≤ 1 := by linarith [(hz01 (k+1)).2]
            rcases le_total k i with h | h
            · induction i, h using Nat.le_induction with
              | base => exact le_rfl
              | succ i hki ih =>
                exact le_trans (hφL i hi t ht0 (lt_of_lt_of_le h2 (hzmono _ _ (by omega) (by omega)))) (ih (by omega))
            · obtain ⟨d, rfl⟩ : ∃ d, k = i + d := ⟨k - i, by omega⟩
              have : ∀ e, e ≤ d → φ i t ≤ φ (i + e) t := by
                intro e
                induction e with
                | zero => intro _; exact le_rfl
                | succ e ih =>
                  intro he
                  exact le_trans (ih (by omega)) (hφR (i+e) (by omega) t ht1
                    (lt_of_le_of_lt (hzmono _ _ (by omega) (by omega)) h1))
              exact this d le_rfl
          have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
          let p : ℝ → ℝ := fun t => ⨆ i : Fin n, φ i t
          have hφp : ∀ i, i < n → ∀ t, φ i t ≤ p t := fun i hi t =>
            le_ciSup (f := fun i : Fin n => φ i t) (Set.finite_range _).bddAbove ⟨i, hi⟩
          have hpeq : ∀ k, k < n → ∀ t, z k < t → t < z (k+1) → p t = φ k t := by
            intro k hk t h1 h2
            exact le_antisymm (ciSup_le fun i => hmaxφ k hk t h1 h2 i i.isLt) (hφp k hk t)
          have hφint : ∀ k, k < n → ∀ a b, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
              IntervalIntegrable (φ k) MeasureTheory.volume a b := fun k hk a b h1 h2 h3 h4 =>
            (hII k hk a b h1 h2 h3 h4).const_mul _
          have hφval : ∀ k a b, ∫ t in a..b, φ k t = val f k a b / val f k (z k) (z (k+1)) := by
            intro k a b
            simp only [φ]
            rw [intervalIntegral.integral_const_mul, inv_mul_eq_div]; rfl
          have hae : ∀ k, k < n → ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc (z k) (z (k+1)) → φ k t = p t := by
            intro k hk
            have : ∀ᵐ t ∂MeasureTheory.volume, t ≠ z (k+1) := by
              simp [MeasureTheory.ae_iff]
            filter_upwards [this] with t ht hmem
            rw [Set.uIoc_of_le (hzm k hk)] at hmem
            exact (hpeq k hk t hmem.1 (lt_of_le_of_ne hmem.2 ht)).symm
          have hpint : ∀ k, k < n → IntervalIntegrable p MeasureTheory.volume (z k) (z (k+1)) := by
            intro k hk
            refine (hφint k hk _ _ (hz01 _).1 (hz01 _).2 (hz01 _).1 (hz01 _).2).congr_ae ?_
            exact (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).2 (hae k hk)
          have hp01 : IntervalIntegrable p MeasureTheory.volume 0 1 := by
            have := IntervalIntegrable.trans_iterate (a := z) (n := n) hpint
            rwa [hz0, hzn] at this
          have hptot : ∫ t in (0:ℝ)..1, p t = n := by
            have h := intervalIntegral.sum_integral_adjacent_intervals (a := z) (n := n) hpint
            rw [hz0, hzn] at h
            rw [← h]
            have : ∀ k ∈ Finset.range n, ∫ t in (z k)..(z (k+1)), p t = 1 := by
              intro k hk
              have hk' := Finset.mem_range.1 hk
              rw [← intervalIntegral.integral_congr_ae (hae k hk'), hφval, div_self (hw k hk').ne']
            rw [Finset.sum_congr rfl this]
            simp
          have hpsub : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 → IntervalIntegrable p MeasureTheory.volume a b := by
            intro a b h1 h2 h3
            apply hp01.mono_set
            rw [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le h2]
            exact Set.Icc_subset_Icc h1 h3
          have hbound : ∀ k, k < n → ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 →
              val f k a b / val f k (z k) (z (k+1)) ≤ ∫ t in a..b, p t := by
            intro k hk a b h1 h2 h3
            rw [← hφval]
            exact intervalIntegral.integral_mono_on h2 (hφint k hk a b h1 (by linarith) (by linarith) h3)
              (hpsub a b h1 h2 h3) (fun t _ => hφp k hk t)
          constructor
          · intro k hk
            have h := hbound k hk 0 1 le_rfl zero_le_one le_rfl
            have h1 : val f k 0 1 = 1 := by
              have := (hI ⟨k, hk⟩).2.2.2
              simpa [val, dens, hk] using this
            rw [hptot, h1, div_le_iff₀ (hw k hk)] at h
            exact h
          · intro x σ hx hx01
            have h1 : ∑ i : Fin n, pieceVal f x σ i / val f i (z i) (z ((i:ℕ)+1)) ≤
                ∑ i : Fin n, ∫ t in (x (σ i))..(x ((σ i : ℕ) + 1)), p t := by
              apply Finset.sum_le_sum
              intro i _
              exact hbound i i.isLt _ _ (hx01 _ (σ i).isLt.le).1 (hx.2.1 _ (σ i).isLt) (hx01 _ (σ i).isLt).2
            have h2 : ∑ i : Fin n, ∫ t in (x (σ i))..(x ((σ i : ℕ) + 1)), p t =
                ∑ i : Fin n, ∫ t in (x i)..(x ((i : ℕ) + 1)), p t :=
              Equiv.sum_comp σ (fun i : Fin n => ∫ t in (x i)..(x ((i : ℕ) + 1)), p t)
            have h3 : ∑ i : Fin n, ∫ t in (x i)..(x ((i : ℕ) + 1)), p t = n := by
              rw [Fin.sum_univ_eq_sum_range (fun i => ∫ t in (x i)..(x (i + 1)), p t) n]
              rw [intervalIntegral.sum_integral_adjacent_intervals (a := x) (n := n)
                (fun k hk => hpsub _ _ (hx01 k hk.le).1 (hx.2.1 k hk) (hx01 (k+1) hk).2), hx.1, hx.2.2, hptot]
            linarith
        -- cut facts
        have hcut_ge : ∀ k ℓ τ, ℓ ≤ 1 → ℓ ≤ cut f k ℓ τ := by
          intro k ℓ τ hℓ
          unfold cut
          split_ifs with h
          · apply le_csInf
            · obtain ⟨y, hy, hy2⟩ := h; exact ⟨y, hy, hy2⟩
            · intro y hy; exact hy.1.1
          · exact hℓ
        have hcut_le : ∀ k ℓ τ, cut f k ℓ τ ≤ 1 := by
          intro k ℓ τ
          unfold cut
          split_ifs with h
          · obtain ⟨y, hy, hy2⟩ := h
            exact le_trans (csInf_le ⟨ℓ, fun z hz => hz.1.1⟩ ⟨hy, hy2⟩) hy.2
          · exact le_rfl
        have hcut_val : ∀ k, k < n → ∀ ℓ τ, 0 ≤ ℓ → ℓ ≤ 1 → cut f k ℓ τ < 1 →
            val f k ℓ (cut f k ℓ τ) = τ := by
          intro k hk ℓ τ hℓ0 hℓ1 hlt
          unfold cut at hlt ⊢
          split_ifs with h
          · rw [if_pos h] at hlt
            have hcl : IsClosed {y | y ∈ Set.Icc ℓ 1 ∧ val f k ℓ y = τ} := by
              have hco : ContinuousOn (fun y => val f k ℓ y) (Set.Icc ℓ 1) := by
                have := intervalIntegral.continuousOn_primitive_interval'
                  (hII k hk ℓ 1 hℓ0 hℓ1 zero_le_one le_rfl) (Set.left_mem_uIcc (a := ℓ) (b := 1))
                rw [Set.uIcc_of_le hℓ1] at this
                exact this
              exact hco.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
            obtain ⟨y, hy, hy2⟩ := h
            have hm := hcl.csInf_mem ⟨y, hy, hy2⟩ ⟨ℓ, fun z hz => hz.1.1⟩
            exact hm.2
          · rw [if_neg h] at hlt; exact absurd hlt (lt_irrefl _)
        set τ : ℝ := ε / (8 * n) with hτ
        have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
        have hτpos : 0 < τ := by positivity
        have hmin_ge : ∀ ℓ, ℓ ≤ 1 → ∀ m, ℓ ≤ minCut f ℓ τ m ∧ minCut f ℓ τ m ≤ 1 := by
          intro ℓ hℓ m
          induction m with
          | zero => simp [minCut, hℓ]
          | succ m ih =>
            simp only [minCut]
            exact ⟨le_min ih.1 (hcut_ge _ _ _ hℓ), le_trans (min_le_left _ _) ih.2⟩
        have hmin_eq : ∀ ℓ m, minCut f ℓ τ m < 1 → ∃ k < m, minCut f ℓ τ m = cut f k ℓ τ := by
          intro ℓ m
          induction m with
          | zero => intro h; simp [minCut] at h
          | succ m ih =>
            intro h
            simp only [minCut] at h ⊢
            rcases min_choice (minCut f ℓ τ m) (cut f m ℓ τ) with h' | h'
            · rw [h'] at h ⊢
              obtain ⟨k, hk, hk2⟩ := ih h
              exact ⟨k, by omega, hk2⟩
            · rw [h']; exact ⟨m, by omega, rfl⟩
        set g := nashGrid f ε with hg
        have hg_succ : ∀ t, g (t + 1) = minCut f (g t) τ n := fun t => rfl
        have hg01 : ∀ t, 0 ≤ g t ∧ g t ≤ 1 := by
          intro t
          induction t with
          | zero => simp [hg, nashGrid]
          | succ t ih =>
            rw [hg_succ]
            have := hmin_ge (g t) ih.2 n
            exact ⟨le_trans ih.1 this.1, this.2⟩
        have hg_step : ∀ t, g t ≤ g (t + 1) := fun t => by
          rw [hg_succ]; exact (hmin_ge (g t) (hg01 t).2 n).1
        have hg_mono : Monotone g := monotone_nat_of_le_succ hg_step
        -- potential
        set Φ : ℕ → ℝ := fun t => ∑ k ∈ Finset.range n, val f k 0 (g t) with hΦ
        have hΦle : ∀ t, Φ t ≤ n := by
          intro t
          have : Φ t ≤ ∑ k ∈ Finset.range n, (1:ℝ) := by
            apply Finset.sum_le_sum
            intro k hk
            exact hle1 k (Finset.mem_range.1 hk) (g t) (hg01 t).1 (hg01 t).2
          simpa using this
        have hΦstep : ∀ t, g (t + 1) < 1 → Φ t + τ ≤ Φ (t + 1) := by
          intro t ht
          have hdiff : Φ (t + 1) = Φ t + ∑ k ∈ Finset.range n, val f k (g t) (g (t + 1)) := by
            simp only [hΦ]
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            rw [hadd k (Finset.mem_range.1 hk) 0 (g t) (g (t+1)) le_rfl zero_le_one (hg01 t).1
              (hg01 t).2 (hg01 (t+1)).1 (hg01 (t+1)).2]
          rw [hdiff]
          rw [hg_succ] at ht
          obtain ⟨k, hk, hk2⟩ := hmin_eq (g t) n ht
          have hv : val f k (g t) (g (t + 1)) = τ := by
            rw [hg_succ, hk2]
            exact hcut_val k hk (g t) τ (hg01 t).1 (hg01 t).2 (hk2 ▸ ht)
          have : val f k (g t) (g (t + 1)) ≤ ∑ k ∈ Finset.range n, val f k (g t) (g (t + 1)) := by
            apply Finset.single_le_sum (f := fun k => val f k (g t) (g (t + 1)))
            · intro j hj
              exact hnonneg j (Finset.mem_range.1 hj) _ _ (hg01 t).1 (hg_step t) (hg01 (t+1)).2
            · exact Finset.mem_range.2 hk
          linarith
        have hΦ0 : 0 ≤ Φ 0 := by
          apply Finset.sum_nonneg
          intro k hk
          exact hnonneg k (Finset.mem_range.1 hk) 0 (g 0) le_rfl (hg01 0).1 (hg01 0).2
        have hgN : g (nashLen n ε) = 1 := by
          by_contra hne
          have hlt : g (nashLen n ε) < 1 := lt_of_le_of_ne (hg01 _).2 hne
          have hgrow : ∀ t, t ≤ nashLen n ε → Φ 0 + t * τ ≤ Φ t := by
            intro t
            induction t with
            | zero => intro _; simp
            | succ t ih =>
              intro ht
              have h1 := ih (by omega)
              have h2 : g (t + 1) < 1 := lt_of_le_of_lt (hg_mono ht) hlt
              have h3 := hΦstep t h2
              push_cast
              linarith
          have h1 := hgrow (nashLen n ε) le_rfl
          have h2 := hΦle (nashLen n ε)
          have h3 : (n:ℝ) < (nashLen n ε : ℝ) * τ := by
            have hc : 8 * (n:ℝ) ^ 2 / ε ≤ (⌈8 * (n : ℝ) ^ 2 / ε⌉₊ : ℝ) := Nat.le_ceil _
            have hL : (nashLen n ε : ℝ) = (⌈8 * (n : ℝ) ^ 2 / ε⌉₊ : ℝ) + 1 := by simp [nashLen]
            rw [hL, hτ]
            have hL2 : (8 * (n:ℝ) ^ 2 / ε + 1) * (ε / (8 * n)) = n + ε / (8 * n) := by
              field_simp
            have : (8 * (n:ℝ) ^ 2 / ε + 1) * (ε / (8 * n)) ≤
                ((⌈8 * (n : ℝ) ^ 2 / ε⌉₊ : ℝ) + 1) * (ε / (8 * n)) := by
              gcongr
            have : 0 < ε / (8 * n) := hτpos
            linarith
          linarith
        -- DP backtracking
        have harg : ∀ (h : ℕ → ℝ) t, argmaxUpTo h t ≤ t := by
          intro h t
          induction t with
          | zero => simp [argmaxUpTo]
          | succ t ih =>
            simp only [argmaxUpTo]
            split_ifs <;> omega
        have hpred : ∀ j t, dpPred f (· * ·) g j t ≤ t := by
          intro j t
          match j with
          | 0 => simp [dpPred]
          | 1 => simp [dpPred]
          | k + 2 => simp only [dpPred]; exact harg _ _
        have hback : ∀ m, dpBack f (· * ·) g (nashLen n ε) (m + 1) ≤ dpBack f (· * ·) g (nashLen n ε) m :=
          fun m => hpred _ _
        have hback_n : dpBack f (· * ·) g (nashLen n ε) n = 0 := by
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          show dpPred f (· * ·) g (m + 1 - m) _ = 0
          rw [show m + 1 - m = 1 by omega]
          simp [dpPred]
        have hpred0 := hpred
        have hAlloc : IsAllocation (n := n) (nashOutput f ε) := by
          refine ⟨?_, ?_, ?_⟩
          · show g (dpBack f (· * ·) g (nashLen n ε) (n - 0)) = 0
            rw [Nat.sub_zero, hback_n]; simp [hg, nashGrid]
          · intro k hk
            show g (dpBack f (· * ·) g (nashLen n ε) (n - k)) ≤ g (dpBack f (· * ·) g (nashLen n ε) (n - (k+1)))
            apply hg_mono
            rw [show n - k = (n - (k + 1)) + 1 by omega]
            exact hback _
          · show g (dpBack f (· * ·) g (nashLen n ε) (n - n)) = 1
            rw [Nat.sub_self]; exact hgN
        have hIcc : ∀ k s t, s ≤ t → eval f k (g s) (g t) = val f k (g s) (g t) := by
          intro k s t hst
          unfold eval val
          rw [intervalIntegral.integral_of_le (hg_mono hst), MeasureTheory.integral_Icc_eq_integral_Ioc]
        have hg0 : g 0 = 0 := rfl
        have hcell : ∀ t k, k < n → val f k (g t) (g (t+1)) ≤ τ := by
          intro t k hk
          have hmin_le : ∀ m, k < m → minCut f (g t) τ m ≤ cut f k (g t) τ := by
            intro m
            induction m with
            | zero => intro h; omega
            | succ m ih =>
              intro h
              simp only [minCut]
              rcases Nat.lt_or_ge k m with h' | h'
              · exact le_trans (min_le_left _ _) (ih h')
              · rw [show k = m by omega]; exact min_le_right _ _
          have hle : g (t+1) ≤ cut f k (g t) τ := hmin_le n hk
          have hcv : val f k (g t) (cut f k (g t) τ) ≤ τ := by
            rcases lt_or_ge (cut f k (g t) τ) 1 with h1 | h1
            · exact (hcut_val k hk (g t) τ (hg01 t).1 (hg01 t).2 h1).le
            · have hc1 : cut f k (g t) τ = 1 := le_antisymm (hcut_le k (g t) τ) h1
              rw [hc1]
              by_contra hcon
              push Not at hcon
              have hco : ContinuousOn (fun y => val f k (g t) y) (Set.Icc (g t) 1) := by
                have := intervalIntegral.continuousOn_primitive_interval'
                  (hII k hk (g t) 1 (hg01 t).1 (hg01 t).2 zero_le_one le_rfl) (Set.left_mem_uIcc (a := g t) (b := 1))
                rw [Set.uIcc_of_le (hg01 t).2] at this
                exact this
              have hvv : val f k (g t) (g t) = 0 := by simp [val]
              obtain ⟨y, hy, hy2⟩ := intermediate_value_Icc (hg01 t).2 hco
                (show τ ∈ Set.Icc _ _ from ⟨by simp only [hvv]; exact hτpos.le, hcon.le⟩)
              have hc2 : cut f k (g t) τ ≤ y := by
                unfold cut
                rw [if_pos ⟨y, hy, hy2⟩]
                exact csInf_le ⟨g t, fun z hz => hz.1.1⟩ ⟨hy, hy2⟩
              have hy1 : y = 1 := le_antisymm hy.2 (hc1 ▸ hc2)
              rw [hy1] at hy2
              simp only at hy2
              linarith
          have h1 := hadd k hk (g t) (g (t+1)) (cut f k (g t) τ) (hg01 t).1 (hg01 t).2 (hg01 _).1 (hg01 _).2
            (le_trans (hg01 t).1 (hcut_ge k _ τ (hg01 t).2)) (hcut_le _ _ _)
          have h2 := hnonneg k hk (g (t+1)) (cut f k (g t) τ) (hg01 _).1 hle (hcut_le _ _ _)
          linarith
        have hround : ∀ z : ℕ → ℝ, z 0 = 0 → z n = 1 → (∀ k < n, z k ≤ z (k+1)) → (∀ k, 0 ≤ z k ∧ z k ≤ 1) →
            (∀ k, k < n → τ ≤ val f k (z k) (z (k+1))) →
            ∏ k ∈ Finset.range n, (val f k (z k) (z (k+1)) - τ) ≤ dpVal f (· * ·) g n (nashLen n ε) := by
          intro z hz0 hzn hzm hz01 hzτ
          classical
          let s : ℕ → ℕ := fun k => Nat.findGreatest (fun t => g t ≤ z k) (nashLen n ε)
          have hs1 : ∀ k, g (s k) ≤ z k := fun k =>
            Nat.findGreatest_spec (P := fun t => g t ≤ z k) (Nat.zero_le _) (by rw [hg0]; exact (hz01 k).1)
          have hsN : ∀ k, s k ≤ nashLen n ε := fun k => Nat.findGreatest_le _
          have hsmax : ∀ k t, t ≤ nashLen n ε → g t ≤ z k → t ≤ s k := fun k t h1 h2 =>
            Nat.le_findGreatest h1 h2
          have hsn : s n = nashLen n ε := le_antisymm (hsN n) (hsmax n _ le_rfl (by rw [hgN, hzn]))
          have hsm : ∀ k, k < n → s k ≤ s (k+1) := fun k hk =>
            hsmax (k+1) _ (hsN k) (le_trans (hs1 k) (hzm k hk))
          have hloss : ∀ i k, i < n → val f i (g (s k)) (z k) ≤ τ := by
            intro i k hi
            rcases Nat.lt_or_ge (s k) (nashLen n ε) with h | h
            · have hlt : z k < g (s k + 1) := by
                by_contra hcon
                push Not at hcon
                have := hsmax k (s k + 1) h hcon
                omega
              have h1 := hcell (s k) i hi
              have h2 := hadd i hi (g (s k)) (z k) (g (s k + 1)) (hg01 _).1 (hg01 _).2 (hz01 _).1 (hz01 _).2 (hg01 _).1 (hg01 _).2
              have h3 := hnonneg i hi (z k) (g (s k + 1)) (hz01 _).1 hlt.le (hg01 _).2
              linarith
            · have e1 : s k = nashLen n ε := le_antisymm (hsN k) h
              have e2 : g (s k) = 1 := by rw [e1, hgN]
              have e3 : z k = 1 := le_antisymm (hz01 k).2 (e2 ▸ hs1 k)
              rw [e2, e3]
              simp [val, hτpos.le]
          have hkeep : ∀ i, i < n → val f i (z i) (z (i+1)) - τ ≤ val f i (g (s i)) (g (s (i+1))) := by
            intro i hi
            have h1 := hloss i (i+1) hi
            have h2 := hnonneg i hi (g (s i)) (z i) (hg01 _).1 (hs1 i) (hz01 _).2
            have h3 := hadd i hi (g (s i)) (z i) (z (i+1)) (hg01 _).1 (hg01 _).2 (hz01 _).1 (hz01 _).2 (hz01 _).1 (hz01 _).2
            have h4 := hadd i hi (g (s i)) (g (s (i+1))) (z (i+1)) (hg01 _).1 (hg01 _).2 (hg01 _).1 (hg01 _).2 (hz01 _).1 (hz01 _).2
            linarith
          have hs0 : g (s 0) = 0 := le_antisymm (hz0 ▸ hs1 0) (hg01 _).1
          have hmaxarg : ∀ (h : ℕ → ℝ) t s, s ≤ t → h s ≤ h (argmaxUpTo h t) := by
            intro h t
            induction t with
            | zero => intro s hs; rw [Nat.le_zero.1 hs]; simp [argmaxUpTo]
            | succ t ih =>
              intro s hs
              simp only [argmaxUpTo]
              split_ifs with hlt
              · rcases Nat.lt_or_ge s (t + 1) with h1 | h1
                · exact le_trans (ih s (by omega)) hlt.le
                · rw [show s = t + 1 by omega]
              · rcases Nat.lt_or_ge s (t + 1) with h1 | h1
                · exact ih s (by omega)
                · rw [show s = t + 1 by omega]; exact not_lt.1 hlt
          have hind : ∀ k, k + 1 ≤ n → ∏ i ∈ Finset.range (k+1), (val f i (z i) (z (i+1)) - τ) ≤
              dpVal f (· * ·) g (k+1) (s (k+1)) := by
            intro k
            induction k with
            | zero =>
              intro h
              have := hkeep 0 (by omega)
              rw [hs0] at this
              show _ ≤ eval f 0 (g 0) (g (s (0+1)))
              rw [hIcc 0 0 _ (Nat.zero_le _), hg0]
              simpa using this
            | succ k ih =>
              intro h
              have ih' := ih (by omega)
              rw [Finset.prod_range_succ]
              have hk := hkeep (k+1) (by omega)
              have hm := hmaxarg (dpCand f (· * ·) g (dpVal f (· * ·) g (k + 1)) (k + 1) (s (k+1+1)))
                (s (k+1+1)) (s (k+1)) (hsm (k+1) (by omega))
              have hp0 : 0 ≤ ∏ i ∈ Finset.range (k+1), (val f i (z i) (z (i+1)) - τ) :=
                Finset.prod_nonneg fun i hi => sub_nonneg.2 (hzτ i (by have := Finset.mem_range.1 hi; omega))
              refine le_trans ?_ hm
              show _ ≤ dpVal f (· * ·) g (k + 1) (s (k+1)) * eval f (k+1) (g (s (k+1))) (g (s (k+1+1)))
              rw [hIcc _ _ _ (hsm (k+1) (by omega))]
              exact mul_le_mul ih' hk (sub_nonneg.2 (hzτ _ (by omega))) (le_trans hp0 ih')
          have := hind (n-1) (by omega)
          rw [show n - 1 + 1 = n by omega, hsn] at this
          exact this
        have hBT : ∀ k, 1 ≤ k → k ≤ n →
            ∏ i ∈ Finset.range k, val f i (g (dpBack f (· * ·) g (nashLen n ε) (n - i)))
              (g (dpBack f (· * ·) g (nashLen n ε) (n - (i + 1)))) =
            dpVal f (· * ·) g k (dpBack f (· * ·) g (nashLen n ε) (n - k)) := by
          set b := dpBack f (· * ·) g (nashLen n ε) with hb
          have hbs : ∀ m, b (m + 1) = dpPred f (· * ·) g (n - m) (b m) := fun m => rfl
          have hb_n : b n = 0 := by
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            rw [hbs, show m + 1 - m = 1 by omega]
            simp [dpPred]
          intro k hk1 hkn
          induction k with
          | zero => omega
          | succ k ih =>
            rcases Nat.eq_zero_or_pos k with h0 | hpos
            · subst h0
              simp only [Finset.range_one, Finset.prod_singleton, Nat.zero_add, Nat.sub_zero]
              rw [hb_n]
              show _ = eval f 0 (g 0) (g (b (n - 1)))
              rw [hIcc 0 0 _ (Nat.zero_le _)]
            · rw [Finset.prod_range_succ, ih hpos (by omega)]
              obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
              have hm : n - (j + 1) = (n - (j + 2)) + 1 := by omega
              have hpred : b (n - (j + 1)) = dpPred f (· * ·) g (j + 2) (b (n - (j + 2))) := by
                rw [hm, hbs, show n - (n - (j + 2)) = j + 2 by omega]
              show _ = dpCand f (· * ·) g (dpVal f (· * ·) g (j + 1)) (j + 1) (b (n - (j + 2)))
                (argmaxUpTo (dpCand f (· * ·) g (dpVal f (· * ·) g (j + 1)) (j + 1) (b (n - (j + 2))))
                  (b (n - (j + 2))))
              have hp2 : dpPred f (· * ·) g (j + 2) (b (n - (j + 2))) =
                  argmaxUpTo (dpCand f (· * ·) g (dpVal f (· * ·) g (j + 1)) (j + 1) (b (n - (j + 2))))
                  (b (n - (j + 2))) := rfl
              rw [← hp2, ← hpred]
              unfold dpCand
              rw [hIcc _ _ _ (by rw [hpred]; exact hpred0 _ _)]
        have hDP : ∏ i : Fin n, pieceVal f (nashOutput f ε) (Equiv.refl (Fin n)) i =
            dpVal f (· * ·) g n (nashLen n ε) := by
          have h := hBT n hn le_rfl
          rw [Nat.sub_self] at h
          rw [← Fin.prod_univ_eq_prod_range (fun i => val f i (g (dpBack f (· * ·) g (nashLen n ε) (n - i)))
              (g (dpBack f (· * ·) g (nashLen n ε) (n - (i + 1))))) n] at h
          exact h
        have hbd : ∀ y : ℕ → ℝ, IsAllocation (n := n) y → ∀ k, k ≤ n → 0 ≤ y k ∧ y k ≤ 1 := by
          intro y hy k hk
          have hmono : ∀ i j, i ≤ j → j ≤ n → y i ≤ y j := by
            intro i j hij
            induction j, hij using Nat.le_induction with
            | base => intro _; exact le_rfl
            | succ j hj ih => intro h; exact le_trans (ih (by omega)) (hy.2.1 j (by omega))
          exact ⟨hy.1 ▸ hmono 0 k (Nat.zero_le _) hk, hy.2.2 ▸ hmono k n hk le_rfl⟩
        have hPV : ∀ y : ℕ → ℝ, IsAllocation (n := n) y → ∀ (π : Equiv.Perm (Fin n)) i,
            0 ≤ pieceVal f y π i := fun y hy π i =>
          hnonneg i i.isLt _ _ (hbd y hy _ (π i).isLt.le).1 (hy.2.1 _ (π i).isLt) (hbd y hy _ (π i).isLt).2
        refine ⟨hAlloc, ?_, hCost⟩
        intro x σ hx
        have hPx : 0 ≤ ∏ i, pieceVal f x σ i := Finset.prod_nonneg fun i _ => hPV x hx σ i
        have hPo : 0 ≤ ∏ i, pieceVal f (nashOutput f ε) (Equiv.refl (Fin n)) i :=
          Finset.prod_nonneg fun i _ => hPV _ hAlloc _ i
        rcases le_or_gt 1 ε with hε1 | hε1
        · have h1 : 0 ≤ NSW f x σ := Real.rpow_nonneg hPx _
          have h2 : 0 ≤ NSW f (nashOutput f ε) (Equiv.refl (Fin n)) := Real.rpow_nonneg hPo _
          exact le_trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) h1) h2
        · obtain ⟨z, hz0, hzn, hzm, hz01, hw, hopt⟩ := hE1
          obtain ⟨hprop, hEG⟩ := hE2 z hz0 hzn hzm hz01 hw hopt
          have hsum := hEG x σ hx (hbd x hx)
          have hn0 : (0:ℝ) < n := by exact_mod_cast hn
          have hwτ : ∀ k, k < n → τ ≤ ε * val f k (z k) (z (k+1)) := by
            intro k hk
            have h1 := hprop k hk
            have h2 := hw k hk
            rw [hτ, div_le_iff₀ (by positivity)]
            have : ε * 1 ≤ ε * (n * val f k (z k) (z (k+1))) := mul_le_mul_of_nonneg_left h1 hε.le
            have h3 : 0 < ε * (n * val f k (z k) (z (k+1))) := by positivity
            linarith
          have hwτ' : ∀ k, k < n → τ ≤ val f k (z k) (z (k+1)) := fun k hk => by
            have h1 := hwτ k hk
            have h2 := hw k hk
            have h3 := mul_le_mul_of_nonneg_right hε1.le h2.le
            linarith
          have hR := hround z hz0 hzn hzm hz01 hwτ'
          have hR2 : ∏ k ∈ Finset.range n, ((1 - ε) * val f k (z k) (z (k+1))) ≤
              ∏ k ∈ Finset.range n, (val f k (z k) (z (k+1)) - τ) := by
            apply Finset.prod_le_prod
            · intro k hk
              exact mul_nonneg (by linarith) (hw k (Finset.mem_range.1 hk)).le
            · intro k hk
              have := hwτ k (Finset.mem_range.1 hk)
              linarith
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at hR2
          have hAG : ∏ i : Fin n, pieceVal f x σ i ≤ ∏ i : Fin n, val f i (z i) (z ((i:ℕ)+1)) := by
            have hr : ∏ i : Fin n, (pieceVal f x σ i / val f i (z i) (z ((i:ℕ)+1))) ≤ 1 := by
              calc ∏ i : Fin n, (pieceVal f x σ i / val f i (z i) (z ((i:ℕ)+1)))
                  ≤ ∏ i : Fin n, Real.exp (pieceVal f x σ i / val f i (z i) (z ((i:ℕ)+1)) - 1) := by
                    apply Finset.prod_le_prod
                    · intro i _
                      exact div_nonneg (hPV x hx σ i) (hw i i.isLt).le
                    · intro i _
                      have := Real.add_one_le_exp (pieceVal f x σ i / val f i (z i) (z ((i:ℕ)+1)) - 1)
                      linarith
                _ = Real.exp (∑ i : Fin n, (pieceVal f x σ i / val f i (z i) (z ((i:ℕ)+1)) - 1)) :=
                    (Real.exp_sum _ _).symm
                _ ≤ 1 := by
                    rw [Real.exp_le_one_iff, Finset.sum_sub_distrib]
                    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
                    linarith
            rw [Finset.prod_div_distrib, div_le_one (Finset.prod_pos (fun (i : Fin n) _ => hw (i:ℕ) i.isLt))] at hr
            exact hr
          rw [Fin.prod_univ_eq_prod_range (fun i => val f i (z i) (z (i+1))) n] at hAG
          have hε0 : 0 ≤ 1 - ε := by linarith
          have hmain : (1 - ε) ^ n * ∏ i, pieceVal f x σ i ≤
              ∏ i, pieceVal f (nashOutput f ε) (Equiv.refl (Fin n)) i := by
            rw [hDP]
            exact le_trans (mul_le_mul_of_nonneg_left hAG (pow_nonneg hε0 n)) (le_trans hR2 hR)
          have hroot : (1 - ε) = ((1 - ε) ^ n) ^ ((1:ℝ) / n) := by
            rw [one_div]
            exact (Real.pow_rpow_inv_natCast hε0 (by omega)).symm
          unfold NSW
          calc (1 - ε) * (∏ i, pieceVal f x σ i) ^ ((1:ℝ) / n)
              = ((1 - ε) ^ n) ^ ((1:ℝ) / n) * (∏ i, pieceVal f x σ i) ^ ((1:ℝ) / n) := by rw [← hroot]
            _ = ((1 - ε) ^ n * ∏ i, pieceVal f x σ i) ^ ((1:ℝ) / n) :=
                (Real.mul_rpow (pow_nonneg hε0 n) hPx).symm
            _ ≤ _ := Real.rpow_le_rpow (mul_nonneg (pow_nonneg hε0 n) hPx) hmain (by positivity)
