-- Prove2me | solution 1 for LinearChoresCLS.lemma_7_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Weiqiang
-- created : 2026-11-13T20:39:48.563071+00:00
-- url     : https://prove2.me/submissions/26f239de-3cb3-46a9-bd19-b40834a53200
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_LinearChoresCLS_lemma_6_3
import Theorems.Thm_LinearChoresCLS_lemma_7_3
import Theorems.Thm_LinearChoresCLS_lemma_7_4
import Definitions.Def_LinearChoresCLS_PriceFamily

open Finset LinearChoresCLS NetworkEquilibriumCLS.LinearNash

private theorem small_t {n : ℕ} (P : Quadratic n) (ε : ℚ) :
    0 < tParam P ε ∧ tParam P ε ≤ 1/256 := by
  have hL : 8 ≤ chainLength P ε := by
    classical
    unfold chainLength
    split
    next h => exact (Nat.find_spec h).1
    next => exact le_rfl
  refine ⟨by unfold tParam; positivity, ?_⟩
  calc
    _ ≤ (1/2 : ℝ)^8 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hL
    _ = _ := by norm_num

private theorem weights {n : ℕ} (P : Quadratic n) :
    (∀ π : Pair n, 0 < pairWeight P π ∧ pairWeight P π ≤ 2 / (n+1)) ∧
    ∀ j, |lam P * cExt P j| ≤ 1 := by
  classical
  let A := ∑ i, ∑ j, |(P.Q i j : ℝ)|
  let C := ∑ i, |(P.c i : ℝ)|
  have ha : 0 ≤ A := by dsimp [A]; positivity
  have hc : 0 ≤ C := by dsimp [C]; positivity
  have hLam : 0 < lam P := by unfold lam; positivity
  have hn : 0 < (n:ℝ)+1 := by positivity
  have hmass : lam P * (1 + A + C) = 1 / (2*((n:ℝ)+1)) := by
    change 1 / (2 * ((n:ℝ)+1) * (1+A+C)) * _ = _
    field_simp
  have scale {r : ℝ} (hr : |r| ≤ A + C) : |lam P * r| < 1 / ((n:ℝ)+1) := by
    rw [abs_mul, abs_of_pos hLam]
    calc
      _ < lam P * (1 + A + C) := (mul_lt_mul_iff_of_pos_left hLam).mpr (by linarith)
      _ = _ := hmass
      _ < _ := by apply one_div_lt_one_div_of_lt <;> linarith
  have row (i : Fin n) : (∑ j, |(P.Q i j : ℝ)|) ≤ A :=
    Finset.single_le_sum (f := fun k => ∑ j, |(P.Q k j : ℝ)|) (fun k _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (mem_univ i)
  have term (i j : Fin n) : |(P.Q i j : ℝ)| ≤ A :=
    (Finset.single_le_sum (fun k _ => abs_nonneg (P.Q i k : ℝ)) (mem_univ j)).trans (row i)
  constructor
  · intro π
    have hright : π.1.2 ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) π.2)
    unfold pairWeight wgt
    split <;> rename_i h
    · try rw [dif_neg hright]
      have hrow := (Finset.abs_sum_le_sum_abs (fun k => (P.Q (π.1.2.pred hright) k : ℝ)) univ).trans (row _)
      have hbd := abs_lt.mp (scale (le_trans hrow (by linarith)))
      constructor <;> linarith [show (2:ℝ)/((n:ℝ)+1) = 2*(1/((n:ℝ)+1)) by ring]
    · try rw [dif_neg hright]
      have hbd := abs_lt.mp (scale ((term (π.1.1.pred h) (π.1.2.pred hright)).trans (by linarith)))
      constructor <;> linarith [show (2:ℝ)/((n:ℝ)+1) = 2*(1/((n:ℝ)+1)) by ring]
  · intro j
    have b : |cExt P j| ≤ C := by
      refine Fin.cases ?_ (fun i => ?_) j
      · simpa [cExt,C] using Finset.abs_sum_le_sum_abs (fun i => (P.c i : ℝ)) univ
      · simpa [cExt,C] using (Finset.single_le_sum (fun k _ => abs_nonneg (P.c k : ℝ)) (mem_univ i))
    exact (scale (le_trans b (by linarith))).le.trans (by apply (div_le_iff₀ hn).mpr; simp)

private theorem inc_card {n : ℕ} (j : Fin (n+1)) :
    (incident j).card ≤ n + 1 := by
  classical
  let other (π : Pair n) := if π.1.1 = j then π.1.2 else π.1.1
  classical
  have inj : Set.InjOn other (incident j : Set (Pair n)) := by
    intro a ha b hb he
    have h₁ := (Finset.mem_filter.mp ha).2
    have h₂ := (Finset.mem_filter.mp hb).2
    apply Subtype.ext
    apply Prod.ext <;> dsimp [other] at he <;> split_ifs at he <;>
      grind [a.2,b.2]
  simpa using Finset.card_le_card_of_injOn other
    (t := (univ : Finset (Fin (n+1)))) (fun _ _ => mem_univ _) inj

private theorem market_valid {n : ℕ} (P : Quadratic n) (ε : ℚ) : (completedMarket P ε).Valid := by
  classical
  let t := tParam P ε
  let L := chainLength P ε
  have ht : 0 < t := (small_t P ε).1
  have hs : t ≤ 1/256 := (small_t P ε).2
  have hr : 0 < 1/2 - 4*t := by linarith
  have hs' : 0 < 1 - 4*t := by linarith
  have hq (k : ℕ) : 0 < qPar t k := by unfold qPar; positivity
  have he (π : Pair n) (k : ℕ) : 0 < gadgetEarn P t π k := by
    unfold gadgetEarn
    have := ((weights P).1 π).1
    positivity
  have hsup (π : Pair n) (k : ℕ) : 0 < gadgetSupply P t π k := mul_pos hs' (he π k)
  have hw (j : Fin (n+1)) : (∑ π ∈ incident j, pairWeight P π) ≤ 2 := calc
    _ ≤ ∑ _π ∈ incident j, (2 / ((n:ℝ)+1)) := Finset.sum_le_sum (fun π _ => ((weights P).1 π).2)
    _ = (incident j).card * (2 / ((n:ℝ)+1)) := by simp
    _ ≤ ((n:ℝ)+1) * (2 / ((n:ℝ)+1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast inc_card j
    _ = 2 := by field_simp
  have hgeom : (∑ k : Fin L, (1/2-4*t)^k.val) ≤ 2 := calc
    _ ≤ ∑ k : Fin L, (1/2:ℝ)^k.val := Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ hr.le (by linarith) k.val)
    _ ≤ 2 := by rw [Fin.sum_univ_eq_sum_range (fun k => (1/2:ℝ)^k) L]; exact sum_geometric_two_le L
  have hinc (j : Fin (n+1)) : (∑ k : Fin L, ∑ π ∈ incident j, gadgetEarn P t π k.val) ≤ 4*t := calc
    _ = (∑ π ∈ incident j, pairWeight P π) * t * ∑ k : Fin L, (1/2-4*t)^k.val := by
      simp only [gadgetEarn, Finset.mul_sum, Finset.sum_mul]
    _ ≤ (2*t)*2 := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right (hw j) ht.le) hgeom
        (Finset.sum_nonneg (fun k _ => pow_nonneg hr.le _)) (by positivity)
    _ = _ := by ring
  have hlin (j : Fin (n+1)) : alpha P t / t * cExt P j ≤ t := calc
    _ = (lam P * cExt P j) * t := by unfold alpha; field_simp
    _ ≤ 1*t := mul_le_mul_of_nonneg_right ((le_abs_self _).trans ((weights P).2 j)) ht.le
    _ = _ := one_mul _
  change (chainMarket P t L).Valid
  refine ⟨?_, ?_, ?_⟩
  · rintro (a | ⟨π,k,r⟩) (j | ⟨ρ,l,b⟩) <;>
      simp only [chainMarket] <;> (try split_ifs) <;> first | exact hq _ | exact one_div_pos.mpr (hq _) | positivity
  · rintro (j | ⟨π,k,r⟩)
    · change 0 < 1 - 3/2*(∑ k : Fin L, ∑ π ∈ incident j, gadgetEarn P t π k.val) - alpha P t / t * cExt P j
      linarith [hinc j, hlin j]
    · exact he _ _
  · rintro (j | ⟨π,k,s⟩)
    · change 0 < 1 - ∑ k : Fin L, ∑ π ∈ incident j, gadgetSupply P t π k.val
      have hle (π : Pair n) (k : ℕ) : gadgetSupply P t π k ≤ gadgetEarn P t π k := by
        unfold gadgetSupply
        nlinarith [mul_pos ht (he π k)]
      have h := Finset.sum_le_sum (s := univ) (fun (k : Fin L) _ =>
        Finset.sum_le_sum (s := incident j) (fun π _ => hle π k.val))
      linarith [hinc j]
    · exact hsup _ _

section
variable {N M : Type*} [Fintype N] [Fintype M] [Nonempty M]
variable {F : ChoresMarket N M} {p : M → ℝ} {z : N → M → ℝ}

private theorem ratio_le_mu (a : N) (j : M) : p j / F.disutil a j ≤ F.mu a p :=
  Finset.le_sup' (fun k => p k / F.disutil a k) (Finset.mem_univ j)

/-- A one-chore optimal-ratio bundle witnesses the minimum disutility.
Equality in the resulting weighted sum forces every used chore to attain the ratio. -/
private theorem demand_conditions (hF : F.Valid) (hCE : F.IsCE p z) (a : N) :
    (∑ j, p j * z a j) = F.earn a ∧
    0 < F.mu a p ∧ ∀ j, 0 < z a j → p j / F.disutil a j = F.mu a p := by
  classical
  obtain ⟨hz, hbudget, hopt⟩ := hCE.2.2.1 a
  have hpospay : 0 < ∑ j, p j * z a j := lt_of_lt_of_le (hF.2.1 a) hbudget
  obtain ⟨i, hi⟩ : ∃ i, 0 < p i * z a i := by
    by_contra! hall
    exact hpospay.not_ge (Finset.sum_nonpos (fun i _ => hall i))
  have hpi : 0 < p i := by
    by_contra! h
    rw [le_antisymm h (hCE.1 i), zero_mul] at hi
    exact hi.false
  have hmu : 0 < F.mu a p :=
    lt_of_lt_of_le (div_pos hpi (hF.1 a i)) (ratio_le_mu a i)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_eq_sup' (univ_nonempty : (univ : Finset M).Nonempty)
    (fun j => p j / F.disutil a j)
  change F.mu a p = _ at hb
  have hbmul : F.mu a p * F.disutil a b = p b := (eq_div_iff (hF.1 a b).ne').mp hb
  have hpb : 0 < p b := by rw [← hbmul]; exact mul_pos hmu (hF.1 a b)
  let y : M → ℝ := fun j => if j = b then F.earn a / p b else 0
  have hy : ∀ j, 0 ≤ y j := by
    intro j
    dsimp [y]
    split_ifs
    · exact div_nonneg (hF.2.1 a).le hpb.le
    · exact le_rfl
  have hyval : ∑ j, p j * y j = F.earn a := by
    simp [y, mul_ite]
    field_simp
  have hycost : ∑ j, F.disutil a j * y j = F.disutil a b * (F.earn a / p b) := by
    simp [y, mul_ite]
  have hcost := hopt y hy hyval.ge
  rw [hycost] at hcost
  have hcap : F.mu a p * (∑ j, F.disutil a j * z a j) ≤ F.earn a := calc
    _ ≤ F.mu a p * (F.disutil a b * (F.earn a / p b)) := mul_le_mul_of_nonneg_left hcost hmu.le
    _ = _ := by rw [← mul_assoc, hbmul]; field_simp
  have hterm (j : M) : p j * z a j ≤ F.mu a p * (F.disutil a j * z a j) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right ((div_le_iff₀ (hF.1 a j)).mp (ratio_le_mu a j)) (hz j)
  have hsum := Finset.sum_le_sum (s := (univ : Finset M)) (fun j _ => hterm j)
  rw [← Finset.mul_sum] at hsum
  have hearn := le_antisymm (hsum.trans hcap) hbudget
  refine ⟨hearn, hmu, ?_⟩
  intro j hj
  have hgap : ∑ k, (F.mu a p * (F.disutil a k * z a k) - p k * z a k) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    linarith
  have hg := Finset.single_le_sum (s := (univ : Finset M))
    (f := fun k => F.mu a p * (F.disutil a k * z a k) - p k * z a k)
    (fun k _ => sub_nonneg.mpr (hterm k)) (Finset.mem_univ j)
  rw [hgap] at hg
  apply (div_eq_iff (hF.1 a j).ne').mpr
  apply mul_right_cancel₀ hj.ne'
  rw [mul_assoc]
  exact le_antisymm (hterm j) (sub_nonpos.mp hg)

end
/-- Each unordered pair has exactly two endpoints. -/
private theorem sum_incident {n : ℕ} (w : Pair n → ℝ) :
    ∑ j : Fin (n + 1), ∑ π ∈ incident j, w π = 2 * ∑ π, w π := by
  classical
  simp only [incident, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π _
  have hne : π.1.1 ≠ π.1.2 := ne_of_lt π.2
  have hsplit (j : Fin (n + 1)) :
      (if π.1.1 = j ∨ π.1.2 = j then w π else 0) =
      (if j = π.1.1 then w π else 0) + (if j = π.1.2 then w π else 0) := by
    by_cases h₁ : j = π.1.1
    · subst j; simp [hne]
    · by_cases h₂ : j = π.1.2
      · subst j; simp [hne, hne.symm]
      · simp [h₁, h₂, Ne.symm h₁, Ne.symm h₂]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  simp [two_mul]

private theorem total_earnings {n L : ℕ} (P : Quadratic n) (t : ℝ) :
    ∑ a, (chainMarket P t L).earn a = (n : ℝ) + 1 := by
  classical
  have hlin : (∑ j : Fin (n + 1), cExt P j) = 0 := by
    rw [Fin.sum_univ_succ]; simp [cExt]
  have hinc : (∑ j : Fin (n+1), ∑ k : Fin L, ∑ π ∈ incident j, gadgetEarn P t π k.val)
      = 2 * ∑ k : Fin L, ∑ π, gadgetEarn P t π k.val := by
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => sum_incident _)
  change (∑ a : Fin (n+1) ⊕ (Pair n × Fin L × Fin 3), _) = _
  rw [Fintype.sum_sum_type]
  change (∑ j : Fin (n+1), ((1 - 3 / 2 * ∑ k : Fin L, ∑ π ∈ incident j, gadgetEarn P t π k.val) -
      alpha P t / t * cExt P j)) + (∑ a : Pair n × Fin L × Fin 3, gadgetEarn P t a.1 a.2.1.val) = _
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hinc, hlin, mul_zero, sub_zero]
  have haux : (∑ a : Pair n × Fin L × Fin 3, gadgetEarn P t a.1 a.2.1.val) =
      3 * ∑ k : Fin L, ∑ π, gadgetEarn P t π k.val := by
    rw [Fintype.sum_prod_type, Finset.sum_comm (s := (univ : Finset (Fin L))) (t := (univ : Finset (Pair n)))]
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat, Finset.mul_sum]
  rw [haux]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, mul_one]
  ring

open Finset LinearChoresCLS NetworkEquilibriumCLS.LinearNash

private theorem outside_bound {n L : ℕ} (P : Quadratic n) (t : ℝ)
    (z : Agent n L → Chore n L → ℝ) (π : Pair n) (k : Fin L) (σ : Bool)
    (hd : ∀ a ℓ, 0 < z a ℓ → Designated a ℓ)
    (hB : 0 ≤ gadgetEarn P t π (k.val+1)) :
    ∑ a ∈ outUsers z π k σ, (chainMarket P t L).earn a ≤ 2 * gadgetEarn P t π (k.val+1) := by
  classical
  let A := outUsers z π k σ
  have input (ρ : Pair n) (l : Fin L) (b : Bool)
      (h : (if b then firstIn ρ l else secondIn ρ l) = Sum.inr (π,k,σ)) :
      ρ = π ∧ l.val = k.val+1 ∧ b = σ := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, firstIn, secondIn] at h <;>
      split at h <;> simp_all <;> grind
  have internal (a : Agent n L) (ha : a ∈ A) :
      ∃ (l : Fin L) (r : Fin 3), a = Sum.inr (π,l,r) ∧ l.val = k.val+1 ∧
        (r = 0 ∨ r = (if σ then 1 else 2)) := by
    obtain ⟨hout,huse⟩ := (Finset.mem_filter.mp ha).2
    have h := hd _ _ huse
    rcases a with j | ⟨ρ,l,r⟩
    · obtain ⟨_, e⟩ := h; contradiction
    · refine ⟨l,r,?_⟩
      change (_ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _) at h
      rcases h with ⟨hr,hi|hi|ho⟩ | ⟨hr,hi|ho⟩ | ⟨hr,hi|ho⟩
      · have e := input ρ l true (by simpa using hi.symm); simp [e.1,e.2.1,hr]
      · have e := input ρ l false (by simpa using hi.symm); simp [e.1,e.2.1,hr]
      · obtain ⟨e₁,e₂,_⟩ := (show π = ρ ∧ k = l ∧ _ from by simpa only [Sum.inr.injEq,Prod.mk.injEq] using ho)
        exact (hout r (by rw [e₁,e₂])).elim
      · have e := input ρ l true (by simpa using hi.symm); simp [e.1,e.2.1,← e.2.2,hr]
      · obtain ⟨e₁,e₂,_⟩ := (show π = ρ ∧ k = l ∧ _ from by simpa only [Sum.inr.injEq,Prod.mk.injEq] using ho)
        exact (hout r (by rw [e₁,e₂])).elim
      · have e := input ρ l false (by simpa using hi.symm); simp [e.1,e.2.1,← e.2.2,hr]
      · obtain ⟨e₁,e₂,_⟩ := (show π = ρ ∧ k = l ∧ _ from by simpa only [Sum.inr.injEq,Prod.mk.injEq] using ho)
        exact (hout r (by rw [e₁,e₂])).elim
  let tag : Agent n L → Fin 3 := Sum.elim (fun _ => 0) (fun u => u.2.2)
  let tags : Finset (Fin 3) := {0, if σ then 1 else 2}
  have card : A.card ≤ 2 := calc
    _ ≤ tags.card := by
      apply Finset.card_le_card_of_injOn tag
      · intro a ha
        obtain ⟨l,r,rfl,_,h⟩ := internal a ha
        simpa [tag,tags] using h
      · intro a ha b hb he
        obtain ⟨l,r,rfl,hl,_⟩ := internal a ha
        obtain ⟨m,s,rfl,hm,_⟩ := internal b hb
        have : l = m := Fin.ext (hl.trans hm.symm)
        change r = s at he
        simp [this,he]
    _ ≤ 2 := by dsimp [tags]; exact Finset.card_le_two
  calc
    _ = ∑ _a ∈ A, gadgetEarn P t π (k.val+1) := by
      apply Finset.sum_congr rfl; intro a ha
      obtain ⟨l,r,rfl,hl,_⟩ := internal a ha
      change gadgetEarn P t π l.val = _
      rw [hl]
    _ = (A.card : ℝ) * gadgetEarn P t π (k.val+1) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card) hB

private theorem rule {n : ℕ} (hn : 0<n) (P : Quadratic n) (ε : ℚ) (hε : 0<ε)
    (p : Chore n (chainLength P ε) → ℝ)
    (z : Agent n (chainLength P ε) → Chore n (chainLength P ε) → ℝ)
    (hCE : (completedMarket P ε).IsCE p z) (π : Pair n) (k : Fin (chainLength P ε)) :
    p (Sum.inr (π,k,true)) = max (p (firstIn π k)) (p (secondIn π k)) / qPar (tParam P ε) k.val ∧
    p (Sum.inr (π,k,false)) = qPar (tParam P ε) k.val * min (p (firstIn π k)) (p (secondIn π k)) := by
  classical
  let t := tParam P ε
  let F := completedMarket P ε
  let B := gadgetEarn P t π k.val
  let S := gadgetSupply P t π k.val
  let q := qPar t k.val
  let plus : Chore n (chainLength P ε) := Sum.inr (π,k,true)
  let minus : Chore n (chainLength P ε) := Sum.inr (π,k,false)
  let a (r : Fin 3) : Agent n (chainLength P ε) := Sum.inr (π,k,r)
  obtain ⟨hp,hpay,_⟩ := lemma_7_3 hn P ε hε p z hCE
  have hd := (lemma_7_4 hn P ε hε p z hCE).2.2
  have ht := (small_t P ε).1
  have ht' := (small_t P ε).2
  change 0<t at ht
  change t≤1/256 at ht'
  have hB : 0 < B := (market_valid P ε).2.1 (a 0)
  have hcond (σ : Bool) :
      (∑ u ∈ univ.filter (fun u => u ≠ a 0 ∧ u ≠ a 1 ∧ u ≠ a 2 ∧ 0 < z u (Sum.inr (π,k,σ))), F.earn u)
        < S * p (Sum.inr (π,k,σ)) ∧ S * p (Sum.inr (π,k,σ)) < B := by
    refine ⟨?_, (hpay π k σ).1⟩
    have eqset : univ.filter (fun u => u ≠ a 0 ∧ u ≠ a 1 ∧ u ≠ a 2 ∧ 0 < z u (Sum.inr (π,k,σ))) = outUsers z π k σ := by
      ext u; simp only [outUsers,mem_filter,mem_univ,true_and]
      constructor
      · rintro ⟨h₀,h₁,h₂,hz⟩
        refine ⟨fun r => ?_,hz⟩
        fin_cases r <;> assumption
      · rintro ⟨hh,hz⟩; exact ⟨hh 0,hh 1,hh 2,hz⟩
    rw [eqset]
    have hnext : gadgetEarn P t π (k.val+1) = B*(1/2-4*t) := by dsimp [B,gadgetEarn]; rw [pow_succ]; ring
    have houts := outside_bound P t z π k σ hd (by rw [hnext]; exact mul_nonneg hB.le (by linarith))
    have hlow := (hp (Sum.inr (π,k,σ))).1
    change ((1+t)^3)⁻¹ ≤ _ at hlow
    have hpow : 0 < (1+t)^3 := by positivity
    have hl : 1-3*t ≤ ((1+t)^3)⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ hpow]
      nlinarith [sq_nonneg t, pow_nonneg ht.le 3, pow_nonneg ht.le 4]
    have hS : 0 ≤ (1-4*t)*B := mul_nonneg (by linarith) hB.le
    calc
      _ ≤ _ := houts
      _ = B*(1-8*t) := by rw [hnext]; ring
      _ < ((1-4*t)*B)*(1-3*t) := by nlinarith [mul_pos ht hB, mul_nonneg (sq_nonneg t) hB.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hl.trans hlow) hS
  have inp : firstIn π k ≠ secondIn π k := by
    unfold firstIn secondIn; split <;> simp [ne_of_lt π.2]
  have disj (b : Bool) : Sum.inr (π,k,b) ≠ firstIn π k ∧ Sum.inr (π,k,b) ≠ secondIn π k := by
    unfold firstIn secondIn
    split
    · simp
    · rename_i h
      have hk : k ≠ (⟨k.val-1,by omega⟩ : Fin (chainLength P ε)) := fun e => by
        have := congrArg Fin.val e; dsimp at this; omega
      simp [hk]
  have hpm : plus ≠ minus := by simp [plus,minus]
  have H := lemma_6_3 F (market_valid P ε) p z hCE (firstIn π k) (secondIn π k) plus minus
    inp (disj true).1 (disj true).2 (disj false).1 (disj false).2 hpm
    (a 0) (a 1) (a 2) (by simp [a]) (by simp [a]) (by simp [a]) B S q
    ⟨rfl,rfl,rfl⟩ ⟨rfl,rfl⟩ (by
      simp [F,completedMarket,chainMarket,a,plus,minus, q,t,inp,inp.symm,
        (disj true).1,(disj true).2,(disj false).1,(disj false).2])
    (by
      refine ⟨fun j hj => ?_,fun j hj => ?_,fun j hj => ?_⟩
      · simpa [a, Designated, plus] using hd (a 0) j hj
      · simpa [a, Designated, minus] using hd (a 1) j hj
      · simpa [a, Designated, minus] using hd (a 2) j hj)
    (by
      refine ⟨?_,(hcond true).2,?_,(hcond false).2⟩
      · convert (hcond true).1 using 2 <;> first | rfl | (ext u; simp [plus])
      · convert (hcond false).1 using 2 <;> first | rfl | (ext u; simp [minus]))
  exact ⟨H.1,H.2.1⟩

theorem solution {n : ℕ} (hn : 0<n) (P : Quadratic n) (ε : ℚ) (hε : 0<ε)
    (p : Chore n (chainLength P ε) → ℝ)
    (z : Agent n (chainLength P ε) → Chore n (chainLength P ε) → ℝ)
    (hCE : (completedMarket P ε).IsCE p z) :
    InCube (decoder (tParam P ε) p) ∧ p = completedNormPrice P ε (decoder (tParam P ε) p) := by
  classical
  let t := tParam P ε
  let L := chainLength P ε
  let x := decoder t p
  let p₀ := p (Sum.inl 0)
  have ht : 0<t := (small_t P ε).1
  obtain ⟨hb,_,hi⟩ := lemma_7_3 hn P ε hε p z hCE
  have hp₀ : 0<p₀ := lt_of_lt_of_le (by change 0 < ((1+t)^3)⁻¹; positivity) (hb (Sum.inl 0)).1
  have hx : InCube x := by
    intro i
    obtain ⟨hi₁,hi₂⟩ := hi i
    have h₁ : 1 ≤ p (Sum.inl i.succ) / p₀ := (one_le_div hp₀).mpr hi₁
    have h₂ : p (Sum.inl i.succ) / p₀ ≤ 1+t := (div_le_iff₀ hp₀).mpr hi₂
    change 0 ≤ 1/t * (_ / p₀ - 1) ∧ 1/t * (_ / p₀ - 1) ≤ 1
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ ht, div_le_iff₀ ht]; constructor <;> linarith
  refine ⟨hx, ?_⟩
  have hav : 0 ≤ xbar x := by
    unfold xbar; apply div_nonneg _ (by positivity)
    exact Finset.sum_nonneg (fun b _ => Fin.cases (by simp [xExt]) (fun i => by simpa [xExt] using (hx i).1) b)
  let κ := p₀*(1+t*xbar x)
  have hd : 0 < 1+t*xbar x := by positivity
  have hk : 0<κ := mul_pos hp₀ hd
  have basic (b : Fin (n+1)) : p (Sum.inl b) = κ * basicPrice t x b := by
    unfold basicPrice; dsimp only [κ]; rw [mul_assoc, mul_div_cancel₀ _ hd.ne']
    refine Fin.cases ?_ (fun i => ?_) b
    · simp [xExt,p₀]
    · simp only [xExt,Fin.cons_succ]
      change _ = p₀*(1+t*(1/t*(p (Sum.inl i.succ)/p₀-1)))
      field_simp; ring
  have prop (π : Pair n) : ∀ (m : ℕ) (hm : m<L),
      let k : Fin L := ⟨m,hm⟩
      let o := layerOut t (basicPrice t x π.1.1) (basicPrice t x π.1.2) m
      p (Sum.inr (π,k,true)) = κ*o.1 ∧ p (Sum.inr (π,k,false)) = κ*o.2 := by
    intro m
    induction m with
    | zero =>
      intro hm
      obtain ⟨h₁,h₂⟩ := rule hn P ε hε p z hCE π ⟨0,hm⟩
      simp only [firstIn,secondIn,↓reduceDIte] at h₁ h₂
      rw [basic,basic,← mul_max_of_nonneg _ _ hk.le] at h₁
      rw [basic,basic,← mul_min_of_nonneg _ _ hk.le] at h₂
      constructor
      · exact h₁.trans (by simp [layerOut,t]; ring)
      · exact h₂.trans (by simp [layerOut,t]; ring)
    | succ m ih =>
      intro hm
      obtain ⟨ha,hb⟩ := ih (by omega)
      obtain ⟨h₁,h₂⟩ := rule hn P ε hε p z hCE π ⟨m+1,hm⟩
      simp only [firstIn,secondIn,Nat.succ_ne_zero,↓reduceDIte,Nat.add_one_sub_one] at h₁ h₂
      rw [ha,hb,← mul_max_of_nonneg _ _ hk.le] at h₁
      rw [ha,hb,← mul_min_of_nonneg _ _ hk.le] at h₂
      constructor
      · exact h₁.trans (by simp [layerOut,t]; ring)
      · exact h₂.trans (by simp [layerOut,t]; ring)
  have allP (j : Chore n L) : p j = κ * priceFam t L x j := by
    rcases j with j | ⟨π,k,b⟩
    · exact basic j
    · cases b <;> first | exact (prop π k.val k.isLt).1 | exact (prop π k.val k.isLt).2
  let F := completedMarket P ε
  have hbal : (∑ j, F.supply j * p j) = (n:ℝ)+1 := calc
    _ = ∑ j, ∑ a, p j * z a j := by
      apply Finset.sum_congr rfl; intro j _
      rw [← hCE.2.2.2 j, mul_comm, Finset.mul_sum]
    _ = ∑ a, ∑ j, p j * z a j := Finset.sum_comm
    _ = ∑ a, F.earn a := Finset.sum_congr rfl (fun a _ => (demand_conditions (market_valid P ε) hCE a).1)
    _ = _ := total_earnings P t
  have hκ : κ * totalPay P t L x = (n:ℝ)+1 := by
    rw [← hbal]; unfold totalPay; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [allP j]; change κ*((chainMarket P t L).supply j *priceFam t L x j) = (chainMarket P t L).supply j*(κ*priceFam t L x j); ring)
  have hT : totalPay P t L x ≠ 0 := by intro h; rw [h,mul_zero] at hκ; linarith
  have hscale := (eq_div_iff hT).mpr hκ
  exact funext (fun j => (allP j).trans (by change κ * priceFam t L x j = _; rw [hscale]; rfl))
