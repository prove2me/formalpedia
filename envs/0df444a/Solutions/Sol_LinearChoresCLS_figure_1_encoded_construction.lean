-- Prove2me | solution 1 for LinearChoresCLS.figure_1_encoded_construction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Weiqiang
-- created : 2026-11-13T20:49:14.713797+00:00
-- url     : https://prove2.me/submissions/d61e2b62-e479-4385-a094-a19f0ddcc863
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_LinearChoresCLS_completed_market_word
import Theorems.Thm_LinearChoresCLS_encoded_basic_price_ratios

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
open Finset LinearChoresCLS
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
open Finset LinearChoresCLS NetworkEquilibriumCLS.LinearNash

private def Prefix {α : Type} (c : α → List Bool) : Prop :=
  ∀ a b x y, c a ++ x = c b ++ y → a=b ∧ x=y

private theorem unary (n m : ℕ) (x y : List Bool)
    (h : List.replicate n true ++ false :: x = List.replicate m true ++ false :: y) :
    n=m ∧ x=y := by
  induction n generalizing m with
  | zero => cases m <;> simp_all [List.replicate_succ]
  | succ n ih =>
    cases m with
    | zero => simp_all [List.replicate_succ]
    | succ m => simpa using ih m (by simpa [List.replicate_succ] using h)

private theorem read_nat : Prefix encNat := by
  intro a b x y h
  unfold encNat at h
  simp only [List.append_assoc,List.cons_append] at h
  obtain ⟨hl,hd⟩ := unary _ _ _ _ h
  obtain ⟨hb,hr⟩ := List.append_inj hd hl
  have decode (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
    induction n using Nat.binaryRec' with
    | zero => rfl
    | bit b n hn ih => simp [Nat.bits_append_bit n b hn,ih]
  exact ⟨(decode a).symm.trans ((congrArg (List.foldr Nat.bit 0) hb).trans (decode b)),hr⟩

private theorem read_int : Prefix encInt := by
  rintro a b x y h
  obtain ⟨hs,ht⟩ := List.cons.inj h
  obtain ⟨hn,hr⟩ := read_nat _ _ _ _ ht
  refine ⟨?_,hr⟩
  cases a <;> cases b <;> simp_all <;> omega

private theorem read_rat : Prefix encRat := by
  intro a b x y h
  simp only [encRat,List.append_assoc] at h
  obtain ⟨hn,ht⟩ := read_int _ _ _ _ h
  obtain ⟨hd,hr⟩ := read_nat _ _ _ _ ht
  exact ⟨Rat.ext hn hd,hr⟩

private theorem read_list {α : Type} {c : α → List Bool} (hc : Prefix c) : Prefix (encList c) := by
  intro a b x y h
  simp only [encList,List.append_assoc] at h
  obtain ⟨hl,ht⟩ := read_nat _ _ _ _ h
  clear h
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons a as ih =>
    cases b with
    | nil => simp at hl
    | cons b bs =>
      simp only [List.flatMap_cons,List.append_assoc] at ht
      obtain ⟨hab,htail⟩ := hc a b (as.flatMap c ++ x) (bs.flatMap c ++ y) ht
      obtain ⟨has,hxy⟩ := ih bs (by simpa using hl) htail
      exact ⟨by rw [hab,has],hxy⟩

private theorem read_vec {n : ℕ} : Prefix (@encVector n) := by
  intro a b x y h
  obtain ⟨he,hr⟩ := read_list read_rat _ _ _ _ h
  exact ⟨List.ofFn_injective he,hr⟩

private theorem same_market {a m a' m' : ℕ} (F : RatChoresMarket a m) (G : RatChoresMarket a' m')
    (h : encChores F = encChores G) : ∃ (ha : a=a') (hm : m=m'), ha ▸ hm ▸ F = G := by
  unfold encChores at h
  simp only [List.append_assoc] at h
  obtain ⟨rfl,h₁⟩ := read_nat _ _ _ _ h
  obtain ⟨rfl,h₂⟩ := read_nat _ _ _ _ h₁
  obtain ⟨hd,h₃⟩ := read_list (read_list read_rat) _ _ _ _ h₂
  obtain ⟨he,h₄⟩ := read_vec _ _ _ _ h₃
  have hs := (read_vec F.supply G.supply [] [] (by simpa using h₄)).1
  have heq := List.ofFn_injective hd
  have hd' : F.disutil = G.disutil := funext (fun i => List.ofFn_injective (congrFun heq i))
  refine ⟨rfl,rfl,?_⟩
  change F = G
  cases F; cases G; simp only at hd' he hs; subst_vars; rfl

private theorem pull_equilibrium {A M : Type*} [Fintype A] [Fintype M] {a m : ℕ}
    (e : A ≃ Fin a) (d : M ≃ Fin m) (F : ChoresMarket A M) (G : RatChoresMarket a m)
    (hd : ∀ i j, (G.disutil (e i) (d j):ℝ) = F.disutil i j)
    (he : ∀ i, (G.earn (e i):ℝ) = F.earn i) (hs : ∀ j, (G.supply (d j):ℝ) = F.supply j)
    (p : Fin m → ℚ) (z : Fin a → Fin m → ℚ)
    (hCE : G.toReal.IsCE (fun j => (p j:ℝ)) (fun i j => (z i j:ℝ))) :
    F.IsCE (fun j => (p (d j):ℝ)) (fun i j => (z (e i) (d j):ℝ)) := by
  classical
  refine ⟨fun j => hCE.1 _,fun i j => hCE.2.1 _ _,?_,?_⟩
  · intro i
    obtain ⟨hn,hb,ho⟩ := hCE.2.2.1 (e i)
    have hpay := d.sum_comp (fun j => (p j:ℝ)*(z (e i) j : ℝ))
    refine ⟨fun j => hn _,?_,?_⟩
    · rw [← he,hpay]; exact hb
    · intro y hy hyb
      have s := d.sum_comp (fun j => (p j:ℝ)*y (d.symm j))
      simp only [Equiv.symm_apply_apply] at s
      have H := ho (fun j => y (d.symm j)) (fun j => hy _) (by change (G.earn (e i):ℝ) ≤ _; rw [he,← s]; exact hyb)
      change (∑ j, (G.disutil (e i) j:ℝ)*(z (e i) j:ℝ)) ≤ ∑ j, (G.disutil (e i) j:ℝ)*y (d.symm j) at H
      rw [← d.sum_comp (fun j => (G.disutil (e i) j:ℝ)*(z (e i) j:ℝ)),← d.sum_comp (fun j => (G.disutil (e i) j:ℝ)*y (d.symm j))] at H
      simpa only [hd, Equiv.symm_apply_apply] using H
  · intro j
    rw [e.sum_comp (fun i => (z i (d j):ℝ)), ← hs]
    exact hCE.2.2.2 (d j)
private theorem eq_price_pos {A M : Type*} [Fintype A] [Fintype M] [Nonempty M]
    {F : ChoresMarket A M} {p : M → ℝ} {z : A → M → ℝ}
    (hv : F.Valid) (hCE : F.IsCE p z) (j : M) : 0 < p j := by
  have hpos : 0 < ∑ a, z a j := by rw [hCE.2.2.2]; exact hv.2.2 j
  obtain ⟨a,ha⟩ : ∃ a, 0 < z a j := by
    by_contra! h; exact hpos.not_ge (sum_nonpos (fun a _ => h a))
  obtain ⟨_,hμ,he⟩ := demand_conditions hv hCE a
  have h := (div_eq_iff (hv.1 a j).ne').mp (he j ha)
  rw [h]; exact mul_pos hμ (hv.1 a j)

theorem solution :
    ∃ (f : List Bool → List Bool) (g : List (Option (Bool ⊕ Bool)) → List Bool),
      PolyTime f ∧ PolyTime g ∧
      ∀ (n : ℕ) (_ : 0 < n) (P : Quadratic n) (ε : ℚ) (_ : 0 < ε),
        let I := encQuadratic P ++ encRat ε
        (completedMarket P ε).Valid ∧ choresCESearch.valid (f I) ∧
        ∀ y, choresCESearch.answer (f I) y →
          ∃ (p : Chore n (chainLength P ε) → ℝ)
            (z : Agent n (chainLength P ε) → Chore n (chainLength P ε) → ℝ)
            (v : Fin n → ℚ),
            (completedMarket P ε).IsCE p z ∧
            (fun i => (v i : ℝ)) = decoder (tParam P ε) p ∧
            encVector v = g (pairCode I y) := by
  classical
  obtain ⟨f,hf,hf'⟩ := completed_market_word
  obtain ⟨g,hg,hg'⟩ := encoded_basic_price_ratios
  refine ⟨f,g,hf,hg,?_⟩
  intro n hn P ε hε
  obtain ⟨a,m,e,d,G,hb,hdis,he,hs,hw⟩ := hf' hn P ε hε
  have hv := market_valid P ε
  have hgvalid : G.toReal.Valid := by
    refine ⟨?_,?_,?_⟩
    · intro i j; obtain ⟨i,rfl⟩ := e.surjective i; obtain ⟨j,rfl⟩ := d.surjective j
      change 0 < (G.disutil (e i) (d j):ℝ); rw [hdis]; exact hv.1 _ _
    · intro i; obtain ⟨i,rfl⟩ := e.surjective i
      change 0 < (G.earn (e i):ℝ); rw [he]; exact hv.2.1 _
    · intro j; obtain ⟨j,rfl⟩ := d.surjective j
      change 0 < (G.supply (d j):ℝ); rw [hs]; exact hv.2.2 _
  have ha := (e (Sum.inl 0)).isLt
  have hm := (d (Sum.inl 0)).isLt
  refine ⟨hv,⟨a,m,by omega,by omega,G,hgvalid,hw⟩,?_⟩
  rintro y ⟨a',m',_,_,G',_,hw',p,z,rfl,hCE⟩
  obtain ⟨rfl,rfl,hG⟩ := same_market G G' (hw.trans hw'.symm)
  subst G'
  let b := fun j : Fin (n+1) => d (Sum.inl j)
  letI : Nonempty (Fin m) := ⟨b 0⟩
  have hp : 0 < p (b 0) := by exact_mod_cast eq_price_pos hgvalid hCE (b 0)
  refine ⟨_,_,_,pull_equilibrium e d _ G hdis he hs p z hCE,?_,hg' hn P ε hε b hb p z hp⟩
  ext i
  simp [decoder,b,tParam]
