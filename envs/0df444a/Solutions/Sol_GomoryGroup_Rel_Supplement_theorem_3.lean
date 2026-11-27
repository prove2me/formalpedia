-- Prove2me | solution 1 for GomoryGroup.Rel.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:22:29.257833+00:00
-- url     : https://prove2.me/submissions/0cb6f100-adce-47e5-8de9-9f749d5e94ac

import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting
import Definitions.Def_GomoryGroup_Rel_Supplement_Presentation
import Definitions.Def_GomoryGroup_Rel_Supplement_Tabulation

set_option autoImplicit false

open GomoryGroup
open GomoryGroup.Rel
open GomoryGroup.Rel.Supplement

/-- THEOREM 3, including all value and recovery bounds. The recovered vectors are
values of y^B: optimal for (4) with Σ y_i ≤ D − 1, the vector used in (3).
At n=0 the impossible literal bound cost < 0 is replaced by cost = 0; no input
case is discarded. -/
theorem solution {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (cB : Fin m → ℝ) (cN : Fin n → ℝ)
    (hB : B.det ≠ 0) (hI : HasUnitColumns B N)
    (hopt : ∀ j, reducedCost B N cB cN j ≤ 0)
    (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (P : LatticePresentation B G)
    (images : Fin n → G) (himages : ∀ j, images j = P.quotientMap (fun i => N i j))
    (costs : Fin n → ℝ) (hcosts : costs = reducedCost B N cB cN) :
    let forward := tabulate P.enumeration images costs
    Fintype.card G = detD B ∧
    (if n = 0 then forward.steps = 0 else forward.steps < 7 * n * detD B) ∧
    (∀ p : G, ∃ (z : ℝ) (y : Fin n → ℕ),
      forward.result p = some (z, y) ∧
      ∀ b : Fin m → ℤ, P.quotientMap b = p →
        IsGreatest (groupValues B N cB cN b) z ∧ IsGroupOptimal B N cB cN b y) ∧
    (∀ b : Fin m → ℤ,
      (recoverOne forward.result (P.quotientMap b)).steps = n ∧
      ∃ y : Fin n → ℕ,
        (recoverOne forward.result (P.quotientMap b)).result = some y ∧
        IsGroupOptimal B N cB cN b y ∧ ∑ j, y j ≤ detD B - 1) ∧
    (recoverAll P.enumeration forward.result).steps = n * detD B ∧
    (∀ b : Fin m → ℤ, ∃ y : Fin n → ℕ,
      (recoverAll P.enumeration forward.result).result (P.quotientMap b) = some y ∧
      IsGroupOptimal B N cB cN b y ∧ ∑ j, y j ≤ detD B - 1) := by
        intro forward
        have hcard : Fintype.card G = detD B := by
          let L : Submodule ℤ (Fin m → ℤ) := LinearMap.range (Matrix.mulVecLin B)
          have hker : P.quotientMap.ker = L.toAddSubgroup := by
            ext v
            simp only [AddMonoidHom.mem_ker, P.kernel]
            simp [L, eq_comm]
          have e : ((Fin m → ℤ) ⧸ L.toAddSubgroup) ≃+ G := by
            rw [← hker]; exact QuotientAddGroup.quotientKerEquivOfSurjective _ P.onto
          have hc : Nat.card ((Fin m → ℤ) ⧸ L) = B.det.natAbs := by
            have hinj : Function.Injective (Matrix.mulVecLin B) := by
              intro x y hxy
              have h0 : Matrix.mulVec B (x - y) = 0 := by
                rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hxy
              exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hB h0)
            let bN : Module.Basis (Fin m) ℤ L :=
              (Pi.basisFun ℤ (Fin m)).map (LinearEquiv.ofInjective _ hinj)
            rw [← Submodule.natAbs_det_basis_change (Pi.basisFun ℤ (Fin m)) L bN]
            congr 1
            rw [Module.Basis.det_apply]
            congr 1
            ext i j
            simp only [Module.Basis.toMatrix_apply, bN, Module.Basis.map_apply, Pi.basisFun_apply,
              Pi.basisFun_repr, Function.comp_apply]
            show (Matrix.mulVecLin B (Pi.single j 1)) i = B i j
            simp
          rw [Fintype.card_eq_nat_card, ← Nat.card_congr e.toEquiv]
          unfold detD
          exact hc
        have hcopy : ∀ y : Fin n → ℕ, (copyVector y).result = y ∧ (copyVector y).steps = n := by
          intro y
          have key : ∀ (l : List (Fin n)) (s : ArithmeticRun (Fin n → ℕ)),
              (l.foldl (fun state j => do
                let v ← state
                let k ← ArithmeticRun.copyOutput (y j)
                pure (Function.update v j k)) s).result = (fun j => if j ∈ l then y j else s.result j) ∧
              (l.foldl (fun state j => do
                let v ← state
                let k ← ArithmeticRun.copyOutput (y j)
                pure (Function.update v j k)) s).steps = s.steps + l.length := by
            intro l
            induction l with
            | nil => intro s; simp
            | cons a l ih =>
              intro s
              rw [List.foldl_cons]
              obtain ⟨h1, h2⟩ := ih _
              refine ⟨?_, ?_⟩
              · rw [h1]; funext j
                show _ = if j ∈ a :: l then y j else s.result j
                by_cases hj : j ∈ l
                · simp [hj]
                · simp only [hj, if_false, List.mem_cons]
                  show (Function.update s.result a (y a)) j = _
                  by_cases hja : j = a
                  · subst hja; simp
                  · simp [hja]
              · rw [h2]
                show (s.trace ++ ([ArithmeticStep.outputCopy] ++ [])).length + l.length = _
                simp [ArithmeticRun.steps]; omega
          obtain ⟨h1, h2⟩ := key (List.finRange n) (pure (fun _ => 0))
          refine ⟨?_, ?_⟩
          · unfold copyVector; rw [h1]; funext j; simp
          · unfold copyVector; rw [h2]; simp [ArithmeticRun.steps]; rfl
        have hDP : ∀ p : G, ∃ (z : ℝ) (y : Fin n → ℕ),
            forward.result p = some (z, y) ∧
            (∀ b : Fin m → ℤ, P.quotientMap b = p →
              IsGreatest (groupValues B N cB cN b) z ∧ IsGroupOptimal B N cB cN b y) ∧
            ∑ j, y j ≤ detD B - 1 := by
          have hfeas : ∀ (b : Fin m → ℤ) (y : Fin n → ℕ), IsGroupFeasible B N b y ↔
              P.quotientMap b = ∑ j, y j • images j := by
            intro b y
            have hNy : Matrix.mulVec N (fun j => (y j : ℤ)) = ∑ j, (y j : ℤ) • (fun i => N i j) := by
              ext i; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
            have hS : P.quotientMap (Matrix.mulVec N (fun j => (y j : ℤ))) = ∑ j, y j • images j := by
              rw [hNy, map_sum]; refine Finset.sum_congr rfl ?_; intro j _
              rw [map_zsmul, himages j]; simp
            constructor
            · rintro ⟨k, hk⟩
              have : P.quotientMap (b - Matrix.mulVec N (fun j => (y j : ℤ))) = 0 := (P.kernel _).2 ⟨k, hk⟩
              rw [map_sub, sub_eq_zero, hS] at this; exact this
            · intro h
              exact (P.kernel _).1 (by rw [map_sub, hS, h, sub_self])
          have hobj : ∀ y : Fin n → ℕ, groupObj B N cB cN y = ∑ j, costs j * (y j : ℝ) := by
            intro y; simp [groupObj, hcosts]
          have hfinal : ∀ p : G, ∃ (v : ℝ) (y : Fin n → ℕ), forward.result p = some (v, y) ∧
              ∑ j, y j • images j = p ∧ v = ∑ j, costs j * (y j : ℝ) ∧
              (∀ y' : Fin n → ℕ, ∑ j, y' j • images j = p → ∑ j, costs j * (y' j : ℝ) ≤ v) ∧
              (∀ w : Fin n → ℕ, w ≤ y → ∑ j, w j • images j = 0 → w = 0) := by
            have hreach : ∀ p : G, ∃ y : Fin n → ℕ, ∑ j, y j • images j = p := by
              let M : AddSubmonoid G := AddSubmonoid.closure (Set.range images)
              have hM : ∀ x ∈ M, -x ∈ M := by
                intro x hx
                have : -x = (addOrderOf x - 1) • x := by
                  have h0 := addOrderOf_nsmul_eq_zero x
                  have hpos := addOrderOf_pos x
                  obtain ⟨k, hk⟩ : ∃ k, addOrderOf x = k + 1 := ⟨addOrderOf x - 1, by omega⟩
                  rw [hk, succ_nsmul] at h0
                  rw [hk, Nat.add_sub_cancel]
                  exact neg_eq_of_add_eq_zero_left h0
                rw [this]; exact AddSubmonoid.nsmul_mem _ hx _
              have hz : ∀ x ∈ M, ∀ k : ℤ, k • x ∈ M := by
                intro x hx k
                rcases k with k | k
                · simp only [Int.ofNat_eq_natCast, natCast_zsmul]; exact AddSubmonoid.nsmul_mem _ hx _
                · rw [negSucc_zsmul]; exact hM _ (AddSubmonoid.nsmul_mem _ hx _)
              have he : ∀ i : Fin m, P.quotientMap (Pi.single i 1) ∈ M := by
                intro i
                rcases hI i with ⟨j, hj⟩ | ⟨j, hj⟩
                · have : P.quotientMap (Pi.single i 1) = 0 := by
                    rw [P.kernel]; refine ⟨Pi.single j 1, ?_⟩
                    ext r; rw [Matrix.mulVec_single_one]; simp [hj r, Pi.single_apply]
                  rw [this]; exact M.zero_mem
                · have : (Pi.single i 1 : Fin m → ℤ) = fun r => N r j := by
                    ext r; rw [hj r]; simp [Pi.single_apply]
                  rw [this, ← himages j]
                  exact AddSubmonoid.subset_closure ⟨j, rfl⟩
              intro p
              obtain ⟨v, rfl⟩ := P.onto p
              have hv : v = ∑ i, v i • (Pi.single i 1 : Fin m → ℤ) := by
                ext r; simp [Pi.single_apply]
              have : P.quotientMap v ∈ M := by
                rw [hv, map_sum]
                refine AddSubmonoid.sum_mem _ (fun i _ => ?_)
                rw [map_zsmul]; exact hz _ (he i) _
              obtain ⟨y, hy⟩ := (AddSubmonoid.mem_closure_range_iff_of_fintype).1 this
              exact ⟨y, hy.symm⟩
            let Good : ℕ → ValueTable G n → Prop := fun s T => ∀ p : G,
              (∀ (v : ℝ) (y : Fin n → ℕ), T p = some (v, y) →
                ∑ j, y j • images j = p ∧ v = ∑ j, costs j * (y j : ℝ) ∧ (∀ j : Fin n, s ≤ j.val → y j = 0) ∧
                (∀ y' : Fin n → ℕ, (∀ j : Fin n, s ≤ j.val → y' j = 0) → ∑ j, y' j • images j = p →
                    ∑ j, costs j * (y' j : ℝ) ≤ v) ∧
                (∀ w : Fin n → ℕ, w ≤ y → ∑ j, w j • images j = 0 → w = 0)) ∧
              (T p = none → ∀ y' : Fin n → ℕ, (∀ j : Fin n, s ≤ j.val → y' j = 0) → ∑ j, y' j • images j ≠ p)
            have hGood0 : Good 0 (initialTable n) := by
              intro p
              have hz : ∀ y' : Fin n → ℕ, (∀ j : Fin n, 0 ≤ j.val → y' j = 0) → y' = 0 := by
                intro y' h; ext j; exact h j (Nat.zero_le _)
              refine ⟨?_, ?_⟩
              · intro v y h
                unfold initialTable at h
                split_ifs at h with hp
                · simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  refine ⟨by simp [hp], by simp, fun _ _ => rfl, ?_, ?_⟩
                  · intro y' hy' _; rw [hz y' hy']; simp
                  · intro w hw _; ext j; have := hw j; simp at this ⊢; omega
              · intro h y' hy' hS
                unfold initialTable at h
                split_ifs at h with hp
                rw [hz y' hy'] at hS; simp at hS; exact hp hS.symm
            have hGoodStage : ∀ (j : Fin n) (T : ValueTable G n), Good j.val T →
                Good (j.val + 1) (tabulateStage P.enumeration j (images j) (costs j) T).result := by
              intro j T hT
              have hc : costs j ≤ 0 := by rw [hcosts]; exact hopt j
              have hsweepInv : ∀ (Inv : ValueTable G n → Prop),
                  (∀ (t : ValueTable G n) (p : G), Inv t →
                    Inv (Function.update t p (relax j (costs j) (t (p - images j)) (t p)).result)) →
                  ∀ (l : List G) (s : ArithmeticRun (ValueTable G n × Cell n)),
                    l.IsChain (fun x y => y = x + images j) →
                    (∀ x, l.head? = some x → s.result.2 = s.result.1 (x - images j)) →
                    Inv s.result.1 →
                    Inv (l.foldl (fun state p => do
                      let (t, previous) ← state
                      let cell ← relax j (costs j) previous (t p)
                      pure (Function.update t p cell, cell)) s).result.1 := by
                intro Inv hstep l
                induction l with
                | nil => intro s _ _ h; exact h
                | cons x l ih =>
                  intro s hch hhead hI
                  rw [List.foldl_cons]
                  have hprev := hhead x rfl
                  apply ih
                  · exact hch.tail
                  · intro y hy
                    have hyx : y = x + images j := by
                      cases l with
                      | nil => simp at hy
                      | cons z l => simp at hy; subst hy; exact (List.isChain_cons_cons.1 hch).1
                    show (relax j (costs j) s.result.2 (s.result.1 x)).result =
                      Function.update s.result.1 x (relax j (costs j) s.result.2 (s.result.1 x)).result (y - images j)
                    rw [hyx, add_sub_cancel_right, Function.update_self]
                  · show Inv (Function.update s.result.1 x (relax j (costs j) s.result.2 (s.result.1 x)).result)
                    rw [hprev]; exact hstep _ _ hI
              have horbk : ∀ (a o : G) (fuel k : ℕ), k < addOrderOf a → addOrderOf a - k ≤ fuel →
                  (walkOrbit a o fuel (o + k • a)).result =
                    List.map (fun i => o + i • a) (List.range' k (addOrderOf a - k)) := by
                intro a o
                have hr : 0 < addOrderOf a := addOrderOf_pos a
                intro fuel
                induction fuel with
                | zero => intro k hk h; omega
                | succ f ih =>
                  intro k hk h
                  have e : walkOrbit a o (f+1) (o + k • a) = ArithmeticRun.bind (ArithmeticRun.addGroup (o + k • a) a) (fun q =>
                            if q = o then ArithmeticRun.pure [o + k • a] else
                              ArithmeticRun.bind (walkOrbit a o f q) (fun tail => ArithmeticRun.pure ((o + k • a) :: tail))) := rfl
                  rw [e]
                  have hq : o + k • a + a = o + (k+1) • a := by rw [succ_nsmul]; abel
                  by_cases hk1 : k + 1 = addOrderOf a
                  · have : o + k • a + a = o := by rw [hq, hk1, addOrderOf_nsmul_eq_zero, add_zero]
                    simp only [ArithmeticRun.bind, ArithmeticRun.addGroup, this, if_true, ArithmeticRun.pure]
                    have : addOrderOf a - k = 1 := by omega
                    rw [this]; simp
                  · have hne : o + k • a + a ≠ o := by
                      rw [hq]; intro h'
                      have : (k+1) • a = 0 := by simpa using h'
                      exact nsmul_ne_zero_of_lt_addOrderOf (by omega) (by omega) this
                    simp only [ArithmeticRun.bind, ArithmeticRun.addGroup, hne, if_false, ArithmeticRun.pure]
                    rw [hq, ih (k+1) (by omega) (by omega)]
                    have : addOrderOf a - k = (addOrderOf a - (k+1)) + 1 := by omega
                    rw [this, List.range'_succ]; simp
              have hlenE : P.enumeration.length = Fintype.card G := by
                rw [← List.toFinset_card_of_nodup P.nodup]
                congr 1
                ext g; simp [P.complete g]
              have horb : ∀ (a o : G), (walkOrbit a o P.enumeration.length o).result =
                  List.map (fun i => o + i • a) (List.range (addOrderOf a)) := by
                intro a o
                have := horbk a o P.enumeration.length 0 (addOrderOf_pos a)
                  (by rw [hlenE]; exact Nat.sub_le_of_le_add (by simpa using addOrderOf_le_card (x := a)))
                simpa [List.range_eq_range'] using this
              have hfin2 : ∀ x : ArithmeticRun (ValueTable G n × Cell n),
                  (do let (t, _) ← x; pure t : ArithmeticRun (ValueTable G n)).result = x.result.1 := by
                intro x; obtain ⟨⟨t, s⟩, tr⟩ := x; rfl
              have hsw : ∀ (Inv : ValueTable G n → Prop),
                  (∀ (t : ValueTable G n) (p : G), Inv t →
                    Inv (Function.update t p (relax j (costs j) (t (p - images j)) (t p)).result)) →
                  ∀ (p : G) (t : ValueTable G n), Inv t →
                  Inv (sweep j (costs j) (List.map (fun i => p + i • images j)
                    (List.range (addOrderOf (images j)))) t).result := by
                intro Inv hstep p t hI
                have hr := addOrderOf_pos (images j)
                unfold sweep
                rw [hfin2 _]
                apply hsweepInv Inv hstep
                · rw [List.isChain_map, List.isChain_range]; intro k _
                  simp only [Nat.succ_eq_add_one, succ_nsmul, add_assoc]
                · intro x hx
                  rw [List.head?_map, List.head?_range, if_neg (by omega)] at hx
                  simp only [Option.map_some, Option.some.injEq, zero_smul, add_zero] at hx
                  subst hx
                  show t _ = t _
                  congr 1
                  rw [List.getLast?_map, List.getLast?_range, if_neg (by omega)]
                  simp only [Option.map_some, Option.getD_some]
                  have h0 := addOrderOf_nsmul_eq_zero (images j)
                  obtain ⟨k, hk⟩ : ∃ k, addOrderOf (images j) = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hr).symm⟩
                  rw [hk, succ_nsmul] at h0
                  rw [hk, Nat.add_sub_cancel, sub_eq_add_neg, neg_eq_of_add_eq_zero_left h0]
                · exact hI
              have hstageInv : ∀ (Inv : ValueTable G n → Prop),
                  (∀ (t : ValueTable G n) (p : G), Inv t →
                    Inv (Function.update t p (relax j (costs j) (t (p - images j)) (t p)).result)) →
                  Inv T → Inv (tabulateStage P.enumeration j (images j) (costs j) T).result := by
                intro Inv hstep hI
                have hfold3 : ∀ (l : List G) (s : ArithmeticRun (ValueTable G n × List G)), Inv s.result.1 →
                    Inv (l.foldl (fun state p => do
                      let (t, seen) ← state
                      if p ∈ seen then pure (t, seen)
                      else
                        let orbit ← walkOrbit (images j) p P.enumeration.length p
                        let t₁ ← sweep j (costs j) orbit t
                        let t₂ ← sweep j (costs j) orbit t₁
                        pure (t₂, seen ++ orbit)) s).result.1 := by
                  intro l
                  induction l with
                  | nil => intro s h; exact h
                  | cons x l ih =>
                    intro s h
                    rw [List.foldl_cons]
                    apply ih
                    obtain ⟨⟨t, seen⟩, tr⟩ := s
                    by_cases hx : x ∈ seen
                    · show Inv (if x ∈ seen then pure (t, seen) else _ : ArithmeticRun (ValueTable G n × List G)).result.1
                      rw [if_pos hx]; exact h
                    · show Inv (if x ∈ seen then pure (t, seen) else _ : ArithmeticRun (ValueTable G n × List G)).result.1
                      rw [if_neg hx]
                      show Inv (sweep j (costs j) (walkOrbit (images j) x P.enumeration.length x).result
                        (sweep j (costs j) (walkOrbit (images j) x P.enumeration.length x).result t).result).result
                      rw [horb]
                      exact hsw Inv hstep x _ (hsw Inv hstep x t h)
                unfold tabulateStage
                have hfin3 : ∀ x : ArithmeticRun (ValueTable G n × List G),
                    (do let (t, _) ← x; pure t : ArithmeticRun (ValueTable G n)).result = x.result.1 := by
                  intro x; obtain ⟨⟨t, s⟩, tr⟩ := x; rfl
                rw [hfin3 _]
                exact hfold3 _ _ hI
              have hrelaxR : ∀ (prev old : Cell n), (relax j (costs j) prev old).result = old ∨
                  ∃ v y, prev = some (v, y) ∧ (∀ w y', old = some (w, y') → w < v + costs j) ∧
                    (relax j (costs j) prev old).result = some (v + costs j, Function.update y j (y j + 1)) := by
                intro prev old
                rcases prev with _ | ⟨v, y⟩
                · left; rfl
                · rcases old with _ | ⟨w, y'⟩
                  · right; exact ⟨v, y, rfl, fun w y' h => by simp at h, rfl⟩
                  · by_cases hlt : w < v + costs j
                    · right
                      refine ⟨v, y, rfl, fun w' y'' h => by
                        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact hlt, ?_⟩
                      show (ArithmeticRun.bind (ArithmeticRun.addReal v (costs j)) (fun cand =>
                        ArithmeticRun.bind (ArithmeticRun.lessReal w cand) (fun imp =>
                          if imp then ArithmeticRun.bind (ArithmeticRun.succWitness (y j))
                            (fun k => ArithmeticRun.pure (some (cand, Function.update y j k)))
                          else ArithmeticRun.pure (some (w, y'))))).result = _
                      simp [ArithmeticRun.bind, ArithmeticRun.addReal, ArithmeticRun.lessReal,
                        ArithmeticRun.succWitness, ArithmeticRun.pure, hlt]
                    · left
                      show (ArithmeticRun.bind (ArithmeticRun.addReal v (costs j)) (fun cand =>
                        ArithmeticRun.bind (ArithmeticRun.lessReal w cand) (fun imp =>
                          if imp then ArithmeticRun.bind (ArithmeticRun.succWitness (y j))
                            (fun k => ArithmeticRun.pure (some (cand, Function.update y j k)))
                          else ArithmeticRun.pure (some (w, y'))))).result = _
                      simp [ArithmeticRun.bind, ArithmeticRun.addReal, ArithmeticRun.lessReal,
                        ArithmeticRun.pure, hlt]
              have hSadd : ∀ u w : Fin n → ℕ, ∑ i, (u + w) i • images i = ∑ i, u i • images i + ∑ i, w i • images i := by
                intro u w; simp [add_nsmul, Finset.sum_add_distrib]
              have hOadd : ∀ u w : Fin n → ℕ, ∑ i, costs i * ((u + w) i : ℝ) =
                  ∑ i, costs i * (u i : ℝ) + ∑ i, costs i * (w i : ℝ) := by
                intro u w; simp [mul_add, Finset.sum_add_distrib]
              have hSup : ∀ y : Fin n → ℕ, ∑ i, (Function.update y j (y j + 1)) i • images i =
                  ∑ i, y i • images i + images j := by
                intro y
                rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
                rw [Function.update_self, succ_nsmul, ← add_assoc]
                congr 2
                refine Finset.sum_congr rfl (fun i hi => ?_)
                rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
              have hOup : ∀ y : Fin n → ℕ, ∑ i, costs i * ((Function.update y j (y j + 1)) i : ℝ) =
                  ∑ i, costs i * (y i : ℝ) + costs j := by
                intro y
                rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
                rw [Function.update_self]; push_cast
                have : ∑ x ∈ Finset.univ.erase j, costs x * ((Function.update y j (y j + 1)) x : ℝ) =
                    ∑ x ∈ Finset.univ.erase j, costs x * (y x : ℝ) :=
                  Finset.sum_congr rfl (fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
                rw [this]; ring
              have hcostall : ∀ i, costs i ≤ 0 := by intro i; rw [hcosts]; exact hopt i
              let Inv : ValueTable G n → Prop := fun t =>
                (∀ (p : G) (v : ℝ) (y : Fin n → ℕ), t p = some (v, y) →
                  ∑ i, y i • images i = p ∧ v = ∑ i, costs i * (y i : ℝ) ∧
                  (∀ i : Fin n, j.val + 1 ≤ i.val → y i = 0) ∧
                  (∀ w : Fin n → ℕ, w ≤ y → ∑ i, w i • images i = 0 → w = 0)) ∧
                (∀ (p : G) (v0 : ℝ) (y0 : Fin n → ℕ), T p = some (v0, y0) → ∃ v y, t p = some (v, y) ∧ v0 ≤ v)
              have hInv0 : Inv T := by
                refine ⟨?_, fun p v0 y0 h => ⟨v0, y0, h, le_rfl⟩⟩
                intro p v y h
                obtain ⟨h1, h2, h3, -, h5⟩ := (hT p).1 v y h
                exact ⟨h1, h2, fun i hi => h3 i (by omega), h5⟩
              have hInvStep : ∀ (t : ValueTable G n) (p : G), Inv t →
                  Inv (Function.update t p (relax j (costs j) (t (p - images j)) (t p)).result) := by
                intro t p hI
                rcases hrelaxR (t (p - images j)) (t p) with hres | ⟨v, y, hprev, hstrict, hres⟩
                · rw [hres, Function.update_eq_self]; exact hI
                · rw [hres]
                  obtain ⟨hA, hB'⟩ := hI
                  obtain ⟨hy1, hy2, hy3, hy4⟩ := hA _ v y hprev
                  refine ⟨?_, ?_⟩
                  · intro q v' y' hq
                    by_cases hqp : q = p
                    · subst hqp
                      rw [Function.update_self] at hq
                      simp only [Option.some.injEq, Prod.mk.injEq] at hq
                      obtain ⟨rfl, rfl⟩ := hq
                      refine ⟨by rw [hSup, hy1]; abel, by rw [hOup, hy2], ?_, ?_⟩
                      · intro i hi
                        have hij : i ≠ j := fun h => by subst h; omega
                        rw [Function.update_of_ne hij]; exact hy3 i hi
                      · intro w hw hw0
                        by_cases hwj : w j ≤ y j
                        · apply hy4 w _ hw0
                          intro i
                          by_cases hij : i = j
                          · subst hij; exact hwj
                          · have := hw i; rwa [Function.update_of_ne hij] at this
                        · exfalso
                          have hwj' : w j = y j + 1 := by
                            have : w j ≤ Function.update y j (y j + 1) j := hw j
                            rw [Function.update_self] at this; omega
                          obtain ⟨u, hu⟩ : ∃ u : Fin n → ℕ, u = Function.update y j (y j + 1) - w := ⟨_, rfl⟩
                          have huw : u + w = Function.update y j (y j + 1) := by
                            ext i; rw [hu]; have : w i ≤ Function.update y j (y j + 1) i := hw i
                            simp only [Pi.add_apply, Pi.sub_apply]; omega
                          have hSu : ∑ i, u i • images i = q := by
                            have := hSadd u w; rw [huw, hSup, hy1, hw0, add_zero] at this
                            rw [← this]; abel
                          have hOw : ∑ i, costs i * (w i : ℝ) ≤ 0 :=
                            Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonpos_of_nonneg (hcostall i) (Nat.cast_nonneg _))
                          have hOu : v + costs j ≤ ∑ i, costs i * (u i : ℝ) := by
                            have := hOadd u w; rw [huw, hOup, ← hy2] at this; linarith
                          have hsuppu : ∀ i : Fin n, j.val ≤ i.val → u i = 0 := by
                            intro i hi
                            rw [hu]; simp only [Pi.sub_apply]
                            by_cases hij : i = j
                            · subst hij; rw [Function.update_self]; omega
                            · rw [Function.update_of_ne hij, hy3 i (by
                                have : i.val ≠ j.val := fun h => hij (Fin.ext h)
                                omega)]; simp
                          rcases h0 : T q with _ | ⟨v0, y0⟩
                          · exact (hT q).2 h0 u hsuppu hSu
                          · obtain ⟨-, -, -, hopt0, -⟩ := (hT q).1 v0 y0 h0
                            have h1 := hopt0 u hsuppu hSu
                            obtain ⟨w', y'', hw', hle⟩ := hB' q v0 y0 h0
                            have h2 := hstrict w' y'' hw'
                            linarith
                    · rw [Function.update_of_ne hqp] at hq
                      exact hA q v' y' hq
                  · intro q v0 y0 h0
                    obtain ⟨w', y'', hw', hle⟩ := hB' q v0 y0 h0
                    by_cases hqp : q = p
                    · subst hqp
                      refine ⟨_, _, Function.update_self _ _ _, ?_⟩
                      have := hstrict w' y'' hw'; linarith
                    · exact ⟨w', y'', by rw [Function.update_of_ne hqp]; exact hw', hle⟩
              have hInvEnd := hstageInv Inv hInvStep hInv0
              have hsound : ∀ (p : G) (v : ℝ) (y : Fin n → ℕ),
                  (tabulateStage P.enumeration j (images j) (costs j) T).result p = some (v, y) →
                  ∑ i, y i • images i = p ∧ v = ∑ i, costs i * (y i : ℝ) ∧
                  (∀ i : Fin n, j.val + 1 ≤ i.val → y i = 0) ∧
                  (∀ w : Fin n → ℕ, w ≤ y → ∑ i, w i • images i = 0 → w = 0) := hInvEnd.1
              have hmono : ∀ (p : G) (v0 : ℝ) (y0 : Fin n → ℕ), T p = some (v0, y0) →
                  ∃ v y, (tabulateStage P.enumeration j (images j) (costs j) T).result p = some (v, y) ∧ v0 ≤ v :=
                hInvEnd.2
              have hclosed : ∀ (p : G) (v : ℝ) (y : Fin n → ℕ),
                  (tabulateStage P.enumeration j (images j) (costs j) T).result p = some (v, y) →
                  ∃ v' y', (tabulateStage P.enumeration j (images j) (costs j) T).result (p + images j) = some (v', y') ∧
                    v + costs j ≤ v' := by
                let UB : ValueTable G n → Prop := fun t => ∀ (p : G) (v : ℝ) (y : Fin n → ℕ), t p = some (v, y) →
                  ∃ (k : ℕ) (v0 : ℝ) (y0 : Fin n → ℕ), T (p - k • images j) = some (v0, y0) ∧ v ≤ v0 + k * costs j
                have hUB0 : UB T := fun p v y h => ⟨0, v, y, by simpa using h, by simp⟩
                have hUBstep : ∀ (t : ValueTable G n) (p : G), UB t →
                    UB (Function.update t p (relax j (costs j) (t (p - images j)) (t p)).result) := by
                  intro t p hU
                  rcases hrelaxR (t (p - images j)) (t p) with hres | ⟨v, y, hprev, -, hres⟩
                  · rw [hres, Function.update_eq_self]; exact hU
                  · rw [hres]
                    intro q v' y' hq
                    by_cases hqp : q = p
                    · subst hqp
                      rw [Function.update_self] at hq
                      simp only [Option.some.injEq, Prod.mk.injEq] at hq
                      obtain ⟨rfl, rfl⟩ := hq
                      obtain ⟨k, v0, y0, h0, hle⟩ := hU _ v y hprev
                      refine ⟨k + 1, v0, y0, ?_, ?_⟩
                      · rw [succ_nsmul', ← sub_sub]; exact h0
                      · push_cast; linarith
                    · rw [Function.update_of_ne hqp] at hq
                      exact hU q v' y' hq
                have hUBend := hstageInv UB hUBstep hUB0
                have hLB : ∀ (q : G) (k : ℕ) (v0 : ℝ) (y0 : Fin n → ℕ), T (q - k • images j) = some (v0, y0) →
                    ∃ v y, (tabulateStage P.enumeration j (images j) (costs j) T).result q = some (v, y) ∧
                      v0 + k * costs j ≤ v := by
                  let C : Cell n → ℝ → Prop := fun cell v => ∃ w y, cell = some (w, y) ∧ v ≤ w
                  have hCle : ∀ cell v w, C cell w → v ≤ w → C cell v := by
                    rintro cell v w ⟨z, y, hz, h⟩ h'; exact ⟨z, y, hz, h'.trans h⟩
                  have hro : ∀ prev old v, C old v → C (relax j (costs j) prev old).result v := by
                    rintro prev old v ⟨w, y, hw, hv⟩
                    rcases hrelaxR prev old with h | ⟨z, u, _, hs, h⟩
                    · rw [h]; exact ⟨w, y, hw, hv⟩
                    · exact ⟨_, _, h, hv.trans (hs w y hw).le⟩
                  have hrp : ∀ prev old v, C prev v → C (relax j (costs j) prev old).result (v + costs j) := by
                    rintro prev old v ⟨w, y, hw, hv⟩
                    rw [hw]
                    rcases ho : old with _ | ⟨z, u⟩
                    · exact ⟨w + costs j, Function.update y j (y j + 1), rfl, by linarith⟩
                    · by_cases hlt : z < w + costs j
                      · refine ⟨w + costs j, Function.update y j (y j + 1), ?_, by linarith⟩
                        show (ArithmeticRun.bind (ArithmeticRun.addReal w (costs j)) (fun cand =>
                          ArithmeticRun.bind (ArithmeticRun.lessReal z cand) (fun imp =>
                            if imp then ArithmeticRun.bind (ArithmeticRun.succWitness (y j))
                              (fun k => ArithmeticRun.pure (some (cand, Function.update y j k)))
                            else ArithmeticRun.pure (some (z, u))))).result = _
                        simp [ArithmeticRun.bind, ArithmeticRun.addReal, ArithmeticRun.lessReal,
                          ArithmeticRun.succWitness, ArithmeticRun.pure, hlt]
                      · refine ⟨z, u, ?_, by linarith⟩
                        show (ArithmeticRun.bind (ArithmeticRun.addReal w (costs j)) (fun cand =>
                          ArithmeticRun.bind (ArithmeticRun.lessReal z cand) (fun imp =>
                            if imp then ArithmeticRun.bind (ArithmeticRun.succWitness (y j))
                              (fun k => ArithmeticRun.pure (some (cand, Function.update y j k)))
                            else ArithmeticRun.pure (some (z, u))))).result = _
                        simp [ArithmeticRun.bind, ArithmeticRun.addReal, ArithmeticRun.lessReal,
                          ArithmeticRun.succWitness, ArithmeticRun.pure, hlt]
                  let F := fun (state : ArithmeticRun (ValueTable G n × Cell n)) (p : G) => do
                    let (t, previous) ← state
                    let cell ← relax j (costs j) previous (t p)
                    pure (Function.update t p cell, cell)
                  have hfm : ∀ s p q v, C (s.result.1 q) v → C ((F s p).result.1 q) v := by
                    intro s p q v h
                    change C (Function.update s.result.1 p (relax j (costs j) s.result.2 (s.result.1 p)).result q) v
                    by_cases hq : q = p
                    · subst hq; rw [Function.update_self]; exact hro _ _ _ h
                    · rw [Function.update_of_ne hq]; exact h
                  have hsm : ∀ (l : List G) s q v, C (s.result.1 q) v → C ((l.foldl F s).result.1 q) v := by
                    intro l
                    induction l with
                    | nil => intro s q v h; exact h
                    | cons x l ih => intro s q v h; exact ih (F s x) q v (hfm s x q v h)
                  have hsp : ∀ (l : List G) s v, C s.result.2 v →
                      C (l.foldl F s).result.2 (v + (l.length : ℝ) * costs j) ∧
                      ∀ (i : ℕ) (hi : i < l.length), C ((l.foldl F s).result.1 l[i]) (v + (i + 1 : ℕ) * costs j) := by
                    intro l
                    induction l with
                    | nil => intro s v h; exact ⟨by simpa using h, fun i hi => by simp at hi⟩
                    | cons x l ih =>
                      intro s v h
                      have hp : C (F s x).result.2 (v + costs j) := hrp _ _ _ h
                      obtain ⟨h1, h2⟩ := ih (F s x) (v + costs j) hp
                      refine ⟨?_, ?_⟩
                      · convert h1 using 1 <;> first | rfl | (simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring)
                      · intro i hi
                        cases i with
                        | zero =>
                          have hx : C ((F s x).result.1 x) (v + costs j) := by
                            change C (Function.update s.result.1 x (relax j (costs j) s.result.2 (s.result.1 x)).result x) _; rw [Function.update_self]; exact hp
                          simpa using hsm l (F s x) x (v + costs j) hx
                        | succ i =>
                          have hh := h2 i (by simpa using hi)
                          convert hh using 1 <;> first | rfl | (push_cast; ring)
                  have hss : ∀ (l : List G) s (i : ℕ) (hi : i < l.length) v,
                      C (s.result.1 l[i]) v →
                      C (l.foldl F s).result.2 (v + ((l.length - 1 - i : ℕ) : ℝ) * costs j) ∧
                      ∀ (k : ℕ) (hk : k < l.length), i ≤ k →
                        C ((l.foldl F s).result.1 l[k]) (v + ((k - i : ℕ) : ℝ) * costs j) := by
                    intro l
                    induction l with
                    | nil => intro s i hi; simp at hi
                    | cons x l ih =>
                      intro s i hi v h
                      cases i with
                      | zero =>
                        have hp : C (F s x).result.2 v := hro _ _ _ h
                        obtain ⟨h1, h2⟩ := hsp l (F s x) v hp
                        refine ⟨by simpa using h1, ?_⟩
                        intro k hk _
                        cases k with
                        | zero =>
                          have hx : C ((F s x).result.1 x) v := by
                            change C (Function.update s.result.1 x (relax j (costs j) s.result.2 (s.result.1 x)).result x) _; rw [Function.update_self]; exact hp
                          simpa using hsm l (F s x) x v hx
                        | succ k => simpa using h2 k (by simpa using hk)
                      | succ i =>
                        have hi' : i < l.length := by simpa using hi
                        have h' := hfm s x l[i] v h
                        obtain ⟨h1, h2⟩ := ih (F s x) i (by simpa using hi) v h'
                        refine ⟨?_, ?_⟩
                        · convert h1 using 1 <;> congr 2 <;> simp <;> omega
                        · intro k hk hik
                          cases k with
                          | zero => omega
                          | succ k => simpa using h2 k (by simpa using hk) (by omega)
                  have hswm : ∀ (l : List G) (t : ValueTable G n) q v, C (t q) v → C ((sweep j (costs j) l t).result q) v := by
                    intro l t q v h
                    exact hsm l (pure (t, t (l.getLast?.getD 0))) q v h
                  have hdbl : ∀ (o : G) (t : ValueTable G n) (i d : ℕ),
                      i < addOrderOf (images j) → d < addOrderOf (images j) → ∀ v,
                      C (t (o + i • images j)) v →
                      C ((sweep j (costs j) (List.map (fun k => o + k • images j) (List.range (addOrderOf (images j))))
                        (sweep j (costs j) (List.map (fun k => o + k • images j) (List.range (addOrderOf (images j)))) t).result).result
                        (o + (i + d) • images j)) (v + (d : ℝ) * costs j) := by
                    intro o t i d hi hd v hv
                    let r := addOrderOf (images j)
                    let O := List.map (fun k => o + k • images j) (List.range r)
                    have hr : 0 < r := addOrderOf_pos _
                    have hlen : O.length = r := by simp [O]
                    have hget : ∀ k (hk : k < O.length), O[k] = o + k • images j := by intro k hk; simp [O]
                    let s : ArithmeticRun (ValueTable G n × Cell n) := pure (t, t (O.getLast?.getD 0))
                    have hv' : C (s.result.1 O[i]) v := by rw [hget]; exact hv
                    obtain ⟨h1, h2⟩ := hss O s i (by simpa [hlen] using hi) v hv'
                    change C ((sweep j (costs j) O (sweep j (costs j) O t).result).result _) _
                    by_cases hid : i + d < r
                    · have hh := h2 (i+d) (by rwa [hlen]) (by omega)
                      rw [hget] at hh
                      have he : i + d - i = d := by omega
                      rw [he] at hh
                      exact hswm O _ _ _ hh
                    · have hlast : O.getLast?.getD 0 = o + (r-1) • images j := by
                        simp [O, List.getLast?_map, List.getLast?_range, Nat.ne_of_gt hr]
                      have htlast : C ((sweep j (costs j) O t).result (o + (r-1) • images j))
                          (v + ((r-1-i : ℕ) : ℝ) * costs j) := by
                        have hh := h2 (r-1) (by rw [hlen]; omega) (by omega)
                        rw [hget] at hh
                        exact hh
                      have hp : C ((pure ((sweep j (costs j) O t).result,
                          (sweep j (costs j) O t).result (O.getLast?.getD 0)) : ArithmeticRun (ValueTable G n × Cell n)).result.2)
                          (v + ((r-1-i : ℕ) : ℝ) * costs j) := by rw [hlast]; exact htlast
                      have hh := (hsp O _ _ hp).2 (i+d-r) (by rw [hlen]; omega)
                      rw [hget] at hh
                      have he : o + (i + d - r) • images j = o + (i+d) • images j := by
                        have h0 := addOrderOf_nsmul_eq_zero (images j)
                        have he' : i + d = i+d-r+r := by omega
                        conv_rhs => rw [he', add_nsmul]
                        simpa [r] using (add_zero (o + (i+d-r) • images j)).symm
                      rw [he] at hh
                      have he' : (r-1-i : ℕ) + (i+d-r+1) = d := by omega
                      have heq : v + (d : ℝ) * costs j =
                          v + ((r-1-i : ℕ) : ℝ) * costs j + ((i+d-r+1 : ℕ) : ℝ) * costs j := by
                        have he'' := congrArg (fun k : ℕ => (k : ℝ)) he'
                        push_cast at he'' ⊢
                        nlinarith
                      rw [heq]
                      exact hh
                  let O := fun o : G => List.map (fun k => o + k • images j) (List.range (addOrderOf (images j)))
                  have horbitLB : ∀ o t,
                      (∀ q v y, T q = some (v,y) → C (t q) v) →
                      ∀ q ∈ O o, ∀ (k : ℕ) (v : ℝ) (y : Fin n → ℕ), T (q-k • images j) = some (v,y) →
                        C ((sweep j (costs j) (O o) (sweep j (costs j) (O o) t).result).result q)
                          (v + (k : ℝ) * costs j) := by
                    intro o t hmono q hq k v y hv
                    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hq
                    have hr := addOrderOf_pos (images j)
                    let r := addOrderOf (images j)
                    let l := (i + (r-1)*k) % r
                    let d := k % r
                    have hl : l < addOrderOf (images j) := Nat.mod_lt _ hr
                    have hd : d < addOrderOf (images j) := Nat.mod_lt _ hr
                    have hn : (r-1) • images j = -images j := by
                      have h0 := addOrderOf_nsmul_eq_zero (images j)
                      have he : addOrderOf (images j) = (r-1)+1 := by dsimp [r]; omega
                      rw [he, succ_nsmul] at h0
                      exact eq_neg_of_add_eq_zero_left h0
                    have hls : l • images j = i • images j - k • images j := by
                      dsimp [l, r]
                      rw [mod_addOrderOf_nsmul, add_nsmul, mul_nsmul]
                      change _ + k • ((r-1) • images j) = _
                      rw [hn, smul_neg, sub_eq_add_neg]
                    have hds : d • images j = k • images j := mod_addOrderOf_nsmul _ _
                    have hsource : o + l • images j = o + i • images j - k • images j := by rw [hls]; abel
                    have ht : C (t (o+l • images j)) v := by rw [hsource]; exact hmono _ v y hv
                    have hh := hdbl o t l d hl hd v ht
                    have htarget : o + (l+d) • images j = o + i • images j := by rw [add_nsmul, hls, hds]; abel
                    rw [htarget] at hh
                    apply hCle _ _ _ hh
                    have hdk : (d : ℝ) ≤ k := by exact_mod_cast Nat.mod_le k r
                    nlinarith
                  let SF := fun (state : ArithmeticRun (ValueTable G n × List G)) (p : G) => do
                    let (t, seen) ← state
                    if p ∈ seen then pure (t, seen)
                    else
                      let orbit ← walkOrbit (images j) p P.enumeration.length p
                      let t₁ ← sweep j (costs j) orbit t
                      let t₂ ← sweep j (costs j) orbit t₁
                      pure (t₂, seen ++ orbit)
                  let SI := fun st : ValueTable G n × List G =>
                    (∀ q v y, T q = some (v,y) → C (st.1 q) v) ∧
                    (∀ q ∈ st.2, ∀ (k : ℕ) (v : ℝ) (y : Fin n → ℕ), T (q-k • images j) = some (v,y) → C (st.1 q) (v+(k:ℝ)*costs j))
                  have hSIstep : ∀ s p, SI s.result → SI (SF s p).result ∧
                      (∀ q ∈ s.result.2, q ∈ (SF s p).result.2) ∧ p ∈ (SF s p).result.2 := by
                    intro s p hs
                    by_cases hp : p ∈ s.result.2
                    · have he : (SF s p).result = s.result := by
                        change (if p ∈ s.result.2 then _ else _ : ArithmeticRun (ValueTable G n × List G)).result = _
                        rw [if_pos hp]; rfl
                      rw [he]; exact ⟨hs, fun _ h => h, hp⟩
                    · have he : (SF s p).result =
                          ((sweep j (costs j) (O p) (sweep j (costs j) (O p) s.result.1).result).result, s.result.2 ++ O p) := by
                        change (if p ∈ s.result.2 then _ else _ : ArithmeticRun (ValueTable G n × List G)).result = _
                        rw [if_neg hp]
                        change ((sweep j (costs j) (walkOrbit (images j) p P.enumeration.length p).result
                          (sweep j (costs j) (walkOrbit (images j) p P.enumeration.length p).result s.result.1).result).result,
                          s.result.2 ++ (walkOrbit (images j) p P.enumeration.length p).result) = _
                        rw [horb]
                      rw [he]
                      have hpres : ∀ q v, C (s.result.1 q) v →
                          C ((sweep j (costs j) (O p) (sweep j (costs j) (O p) s.result.1).result).result q) v := by
                        intro q v h; exact hswm _ _ _ _ (hswm _ _ _ _ h)
                      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
                      · intro q v y hv; exact hpres q v (hs.1 q v y hv)
                      · intro q hq k v y hv
                        rcases List.mem_append.1 hq with hq | hq
                        · exact hpres _ _ (hs.2 q hq k v y hv)
                        · exact horbitLB p _ hs.1 q hq k v y hv
                      · intro q hq; exact List.mem_append_left _ hq
                      · apply List.mem_append_right
                        exact List.mem_map.2 ⟨0, List.mem_range.2 (addOrderOf_pos _), by simp⟩
                  have hSIfold : ∀ (l : List G) s, SI s.result →
                      SI (l.foldl SF s).result ∧ (∀ q ∈ l, q ∈ (l.foldl SF s).result.2) ∧
                        (∀ q ∈ s.result.2, q ∈ (l.foldl SF s).result.2) := by
                    intro l
                    induction l with
                    | nil => intro s hs; exact ⟨hs, by simp, fun _ h => h⟩
                    | cons p l ih =>
                      intro s hs
                      obtain ⟨h1, h2, h3⟩ := hSIstep s p hs
                      obtain ⟨h4, h5, h6⟩ := ih (SF s p) h1
                      refine ⟨h4, ?_, fun q hq => h6 q (h2 q hq)⟩
                      intro q hq
                      rcases List.mem_cons.1 hq with rfl | hq
                      · exact h6 _ h3
                      · exact h5 _ hq
                  have hs0 : SI (pure (T, []) : ArithmeticRun (ValueTable G n × List G)).result := by
                    exact ⟨fun q v y hv => ⟨v,y,hv,le_rfl⟩, by intro q hq; exact (List.not_mem_nil hq).elim⟩
                  obtain ⟨h1,h2,h3⟩ := hSIfold P.enumeration (pure (T, [])) hs0
                  intro q k v y hv
                  exact h1.2 q (h2 q (P.complete q)) k v y hv
                intro p v y h
                obtain ⟨k, v0, y0, h0, hle⟩ := hUBend p v y h
                have h0' : T ((p + images j) - (k + 1) • images j) = some (v0, y0) := by
                  rw [succ_nsmul, add_sub_add_right_eq_sub]; exact h0
                obtain ⟨v', y', h', hle'⟩ := hLB (p + images j) (k + 1) v0 y0 h0'
                refine ⟨v', y', h', ?_⟩
                push_cast at hle'; linarith
              set T' := (tabulateStage P.enumeration j (images j) (costs j) T).result with hT'
              have hclosedK : ∀ (k : ℕ) (p : G) (v : ℝ) (y : Fin n → ℕ), T' p = some (v, y) →
                  ∃ v' y', T' (p + k • images j) = some (v', y') ∧ v + k * costs j ≤ v' := by
                intro k
                induction k with
                | zero => intro p v y h; exact ⟨v, y, by simpa using h, by simp⟩
                | succ k ih =>
                  intro p v y h
                  obtain ⟨v1, y1, h1, h1'⟩ := ih p v y h
                  obtain ⟨v2, y2, h2, h2'⟩ := hclosed _ v1 y1 h1
                  refine ⟨v2, y2, by rw [succ_nsmul, ← add_assoc]; exact h2, ?_⟩
                  push_cast; linarith
              have hsplitS : ∀ y' : Fin n → ℕ, ∑ i, y' i • images i =
                  ∑ i, (Function.update y' j 0) i • images i + y' j • images j := by
                intro y'
                rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
                simp only [Function.update_self, zero_smul, add_zero]
                rw [add_left_inj]
                refine Finset.sum_congr rfl (fun i hi => ?_)
                rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
              have hsplitC : ∀ y' : Fin n → ℕ, ∑ i, costs i * (y' i : ℝ) =
                  ∑ i, costs i * ((Function.update y' j 0) i : ℝ) + y' j * costs j := by
                intro y'
                rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
                simp only [Function.update_self, Nat.cast_zero, mul_zero, add_zero]
                rw [mul_comm, add_left_inj]
                refine Finset.sum_congr rfl (fun i hi => ?_)
                rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
              have hdom : ∀ (p : G) (y' : Fin n → ℕ), (∀ i : Fin n, j.val + 1 ≤ i.val → y' i = 0) →
                  ∑ i, y' i • images i = p →
                  ∃ v y, T' p = some (v, y) ∧ ∑ i, costs i * (y' i : ℝ) ≤ v := by
                intro p y' hsupp hS
                set y'' := Function.update y' j 0 with hy''
                have hsupp'' : ∀ i : Fin n, j.val ≤ i.val → y'' i = 0 := by
                  intro i hi
                  by_cases hij : i = j
                  · rw [hy'', hij, Function.update_self]
                  · rw [hy'', Function.update_of_ne hij]
                    exact hsupp i (by
                      have : i.val ≠ j.val := fun h => hij (Fin.ext h)
                      omega)
                have hq : ∑ i, y'' i • images i + y' j • images j = p := by rw [← hsplitS]; exact hS
                rcases h0 : T (∑ i, y'' i • images i) with _ | ⟨v0, y0⟩
                · exact absurd rfl ((hT _).2 h0 y'' hsupp'')
                · obtain ⟨-, -, -, hopt0, -⟩ := (hT _).1 v0 y0 h0
                  have hle0 := hopt0 y'' hsupp'' rfl
                  obtain ⟨v1, y1, h1, h1'⟩ := hmono _ v0 y0 h0
                  obtain ⟨v2, y2, h2, h2'⟩ := hclosedK (y' j) _ v1 y1 h1
                  rw [hq] at h2
                  refine ⟨v2, y2, h2, ?_⟩
                  rw [hsplitC]
                  linarith
              intro p
              refine ⟨?_, ?_⟩
              · intro v y h
                obtain ⟨h1, h2, h3, h5⟩ := hsound p v y h
                refine ⟨h1, h2, h3, ?_, h5⟩
                intro y' hsupp hS
                obtain ⟨v', y2, h', hle⟩ := hdom p y' hsupp hS
                rw [h] at h'
                simp only [Option.some.injEq, Prod.mk.injEq] at h'
                rw [h'.1]; exact hle
              · intro h y' hsupp hS
                obtain ⟨v', y2, h', -⟩ := hdom p y' hsupp hS
                rw [h] at h'; cases h'
            have hGoodAll : ∀ k ≤ n, Good k ((List.finRange n).take k |>.foldl (fun state j => do
                  let table ← state
                  tabulateStage P.enumeration j (images j) (costs j) table) (pure (initialTable n))).result := by
              intro k
              induction k with
              | zero => intro _; exact hGood0
              | succ k ih =>
                intro hk
                have hk' : k < (List.finRange n).length := by rw [List.length_finRange]; omega
                rw [List.take_succ, List.getElem?_eq_getElem hk', Option.toList_some, List.foldl_append,
                  List.foldl_cons, List.foldl_nil]
                have := hGoodStage ⟨k, by omega⟩ _ (ih (by omega))
                simp only [List.getElem_finRange, Fin.cast_mk]
                exact this
            have hG := hGoodAll n le_rfl
            rw [List.take_of_length_le (by simp)] at hG
            intro p
            obtain ⟨hs, hn⟩ := hG p
            rcases hfp : forward.result p with _ | ⟨v, y⟩
            · obtain ⟨y', hy'⟩ := hreach p
              exact absurd hy' (hn hfp y' (fun j hj => absurd j.isLt (by omega)))
            · obtain ⟨h1, h2, -, h4, h5⟩ := hs v y hfp
              exact ⟨v, y, rfl, h1, h2, fun y' hy' => h4 y' (fun j hj => absurd j.isLt (by omega)) hy', h5⟩
          have hZSF : ∀ y : Fin n → ℕ, (∀ w : Fin n → ℕ, w ≤ y → ∑ j, w j • images j = 0 → w = 0) →
              ∑ j, y j ≤ detD B - 1 := by
            intro y hy
            have hchain : ∀ s : ℕ, ∀ y : Fin n → ℕ, ∑ j, y j = s → ∃ f : ℕ → (Fin n → ℕ),
                (∀ t, f t ≤ y) ∧ Monotone f ∧ ∀ t ≤ s, ∑ j, f t j = t := by
              intro s
              induction s with
              | zero =>
                intro y hy0
                refine ⟨fun _ => 0, fun _ => by simp, fun _ _ _ => le_rfl, ?_⟩
                intro t ht; simp; omega
              | succ s ih =>
                intro y hys
                obtain ⟨i, hi⟩ : ∃ i, 0 < y i := by
                  by_contra hcon; push_neg at hcon
                  have : ∑ j, y j = 0 := Finset.sum_eq_zero (fun j _ => by have := hcon j; omega)
                  omega
                set y' := Function.update y i (y i - 1) with hy'
                have hsum' : ∑ j, y' j = s := by
                  have h1 := Finset.sum_update_of_mem (Finset.mem_univ i) y (y i - 1)
                  rw [hy', h1]
                  have h2 := Finset.add_sum_erase Finset.univ y (Finset.mem_univ i)
                  rw [Finset.sdiff_singleton_eq_erase] at *
                  omega
                have hy'le : y' ≤ y := by
                  intro j; rw [hy']; by_cases hj : j = i
                  · subst hj; simp
                  · simp [hj]
                obtain ⟨f, hf1, hf2, hf3⟩ := ih y' hsum'
                refine ⟨fun t => if t ≤ s then f t else y, ?_, ?_, ?_⟩
                · intro t; simp only; split_ifs
                  · exact le_trans (hf1 t) hy'le
                  · exact le_rfl
                · intro t1 t2 ht; simp only; split_ifs with h1 h2 h2
                  · exact hf2 ht
                  · exact le_trans (hf1 t1) hy'le
                  · omega
                  · exact le_rfl
                · intro t ht; simp only; split_ifs with h1
                  · exact hf3 t h1
                  · omega
            obtain ⟨f, hf1, hf2, hf3⟩ := hchain _ y rfl
            by_contra hcon
            have hD : detD B ≤ ∑ j, y j := by omega
            have hcardlt : Fintype.card G < Fintype.card (Fin (detD B + 1)) := by
              rw [Fintype.card_fin, hcard]; omega
            obtain ⟨s, t, hst, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
              (fun t : Fin (detD B + 1) => ∑ j, f t.val j • images j) hcardlt
            have hadd : ∀ u v : Fin n → ℕ, ∑ j, (u + v) j • images j = ∑ j, u j • images j + ∑ j, v j • images j := by
              intro u v; simp [add_nsmul, Finset.sum_add_distrib]
            have key : ∀ s t : ℕ, s < t → t ≤ ∑ j, y j → ∑ j, f s j • images j = ∑ j, f t j • images j → False := by
              intro s t hlt htle he
              have hle : f s ≤ f t := hf2 hlt.le
              obtain ⟨w, hw⟩ : ∃ w : Fin n → ℕ, w = f t - f s := ⟨_, rfl⟩
              have hwf : w + f s = f t := by
                ext j; rw [hw]; have h' : f s j ≤ f t j := hle j
                simp only [Pi.add_apply, Pi.sub_apply]; omega
              have hw0 : ∑ j, w j • images j = 0 := by
                have := hadd w (f s); rw [hwf, he] at this
                exact (add_eq_right.mp this.symm)
              have hw00 := hy w (by rw [hw]; exact le_trans (fun j => Nat.sub_le _ _) (hf1 t)) hw0
              have h1 := hf3 t htle
              have h2 := hf3 s (by omega)
              have hsum : ∑ j, (w + f s) j = ∑ j, w j + ∑ j, f s j := by
                simp only [Pi.add_apply, Finset.sum_add_distrib]
              rw [hwf, hw00, h1, h2] at hsum
              simp only [Pi.zero_apply, Finset.sum_const_zero, zero_add] at hsum
              omega
            rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hst) with h | h
            · exact key _ _ h (by have := t.isLt; omega) heq
            · exact key _ _ h (by have := s.isLt; omega) heq.symm
          intro p
          obtain ⟨v, y, h1, h2, h3, h4, h5⟩ := hfinal p
          refine ⟨v, y, h1, ?_, hZSF y h5⟩
          intro b hb
          have hfy : IsGroupFeasible B N b y := (hfeas b y).2 (hb.trans h2.symm)
          refine ⟨⟨⟨y, hfy, by rw [hobj, h3]⟩, ?_⟩, hfy, ?_⟩
          · rintro z ⟨y', hy', rfl⟩; rw [hobj]; exact h4 y' (((hfeas b y').1 hy').symm.trans hb)
          · intro y' hy'; rw [hobj, hobj, ← h3]; exact h4 y' (((hfeas b y').1 hy').symm.trans hb)
        have hsteps : (if n = 0 then forward.steps = 0 else forward.steps < 7 * n * detD B) := by
          split_ifs with hn
          · subst hn
            simp [forward, tabulate, ArithmeticRun.steps]
            rfl
          · have hwalk : ∀ (a o : G) (fuel : ℕ) (p : G),
                (walkOrbit a o fuel p).steps = (walkOrbit a o fuel p).result.length := by
              intro a o
              intro fuel
              induction fuel with
              | zero => intro p; rfl
              | succ k ih =>
                intro p
                have e : walkOrbit a o (k+1) p = ArithmeticRun.bind (ArithmeticRun.addGroup p a) (fun q =>
                    if q = o then ArithmeticRun.pure [p] else
                      ArithmeticRun.bind (walkOrbit a o k q) (fun tail => ArithmeticRun.pure (p :: tail))) := rfl
                rw [e]
                by_cases h : p + a = o
                · simp [ArithmeticRun.bind, ArithmeticRun.addGroup, h, ArithmeticRun.pure, ArithmeticRun.steps]
                · have := ih (p + a)
                  simp only [ArithmeticRun.steps] at this
                  simp [ArithmeticRun.bind, ArithmeticRun.addGroup, h, ArithmeticRun.pure, ArithmeticRun.steps, this]
            have hrelax : ∀ (j : Fin n) (c : ℝ) (prev old : Cell n), (relax j c prev old).steps ≤ 3 := by
              intro j c prev old
              rcases prev with _ | ⟨v, y⟩
              · show ([] : List ArithmeticStep).length ≤ 3
                simp
              · rcases old with _ | ⟨w, y'⟩
                · show ([ArithmeticStep.realAdd] ++ ([ArithmeticStep.witnessSucc] ++ [])).length ≤ 3
                  simp
                · show (ArithmeticRun.bind (ArithmeticRun.addReal v c) (fun cand =>
                      ArithmeticRun.bind (ArithmeticRun.lessReal w cand) (fun imp =>
                        if imp then ArithmeticRun.bind (ArithmeticRun.succWitness (y j))
                          (fun k => ArithmeticRun.pure (some (cand, Function.update y j k)))
                        else ArithmeticRun.pure (some (w, y'))))).steps ≤ 3
                  by_cases hlt : w < v + c
                  · simp [ArithmeticRun.bind, ArithmeticRun.addReal, ArithmeticRun.lessReal,
                      ArithmeticRun.succWitness, ArithmeticRun.pure, ArithmeticRun.steps, hlt]
                  · simp [ArithmeticRun.bind, ArithmeticRun.addReal, ArithmeticRun.lessReal,
                      ArithmeticRun.succWitness, ArithmeticRun.pure, ArithmeticRun.steps, hlt]
            have hrelax2 : ∀ (j : Fin n) (c : ℝ) (prev old : Cell n), c ≤ 0 →
                (prev = none ∨ prev = some (0, fun _ => 0)) → (old = none ∨ old = some (0, fun _ => 0)) →
                (relax j c prev old).steps ≤ 2 := by
              intro j c prev old hc hp ho
              rcases hp with rfl | rfl
              · show ([] : List ArithmeticStep).length ≤ 2
                simp
              · rcases ho with rfl | rfl
                · show ([ArithmeticStep.realAdd] ++ ([ArithmeticStep.witnessSucc] ++ [])).length ≤ 2
                  simp
                · show (ArithmeticRun.bind (ArithmeticRun.addReal 0 c) (fun cand =>
                      ArithmeticRun.bind (ArithmeticRun.lessReal 0 cand) (fun imp =>
                        if imp then ArithmeticRun.bind (ArithmeticRun.succWitness ((fun _ => 0 : Fin n → ℕ) j))
                          (fun k => ArithmeticRun.pure (some (cand, Function.update (fun _ => 0 : Fin n → ℕ) j k)))
                        else ArithmeticRun.pure (some (0, fun _ => 0))))).steps ≤ 2
                  have hlt : ¬ (0:ℝ) < 0 + c := by linarith
                  have hlt' : ¬ (0:ℝ) < c := by linarith
                  simp [ArithmeticRun.bind, ArithmeticRun.addReal, ArithmeticRun.lessReal,
                      ArithmeticRun.pure, ArithmeticRun.steps, hlt, hlt']
            have hsweepfold : ∀ (j : Fin n) (c : ℝ) (l : List G) (s : ArithmeticRun (ValueTable G n × Cell n)),
                (l.foldl (fun state p => do
                  let (t, previous) ← state
                  let cell ← relax j c previous (t p)
                  pure (Function.update t p cell, cell)) s).steps ≤ s.steps + 3 * l.length := by
              intro j c l
              induction l with
              | nil => intro s; simp
              | cons x l ih =>
                intro s
                rw [List.foldl_cons]
                refine le_trans (ih _) ?_
                have := hrelax j c s.result.2 (s.result.1 x)
                show (s.trace ++ ((relax j c s.result.2 (s.result.1 x)).trace ++ [])).length + 3 * l.length ≤ _
                simp only [ArithmeticRun.steps] at this ⊢
                simp only [List.length_append, List.length_nil, List.length_cons]
                omega
            have hsweep : ∀ (j : Fin n) (c : ℝ) (orbit : List G) (t : ValueTable G n),
                (sweep j c orbit t).steps ≤ 3 * orbit.length := by
              intro j c orbit t
              have := hsweepfold j c orbit (pure (t, t (orbit.getLast?.getD 0)))
              have h0 : (pure (t, t (orbit.getLast?.getD 0)) : ArithmeticRun (ValueTable G n × Cell n)).steps = 0 := rfl
              rw [h0, zero_add] at this
              unfold sweep
              show (_ ++ []).length ≤ _
              rw [List.append_nil]
              exact this
            have hsweep0 : ∀ (j : Fin n) (c : ℝ) (x : G) (l : List G) (t : ValueTable G n),
                (sweep j c (x :: l) t).steps ≤ (relax j c (t ((x :: l).getLast?.getD 0)) (t x)).steps + 3 * l.length := by
              intro j c x l t
              have := hsweepfold j c l (ArithmeticRun.bind (pure (t, t ((x :: l).getLast?.getD 0)))
                (fun st => ArithmeticRun.bind (relax j c st.2 (st.1 x)) (fun cell =>
                  ArithmeticRun.pure (Function.update st.1 x cell, cell))))
              unfold sweep
              show (_ ++ []).length ≤ _
              rw [List.append_nil, List.foldl_cons]
              refine le_trans this (le_of_eq ?_)
              show ([] ++ ((relax j c (t ((x :: l).getLast?.getD 0)) (t x)).trace ++ [])).length + 3 * l.length = _
              simp [ArithmeticRun.steps]
            have horbk : ∀ (a o : G) (fuel k : ℕ), k < addOrderOf a → addOrderOf a - k ≤ fuel →
                (walkOrbit a o fuel (o + k • a)).result =
                  List.map (fun i => o + i • a) (List.range' k (addOrderOf a - k)) := by
              intro a o
              have hr : 0 < addOrderOf a := addOrderOf_pos a
              intro fuel
              induction fuel with
              | zero => intro k hk h; omega
              | succ f ih =>
                intro k hk h
                have e : walkOrbit a o (f+1) (o + k • a) = ArithmeticRun.bind (ArithmeticRun.addGroup (o + k • a) a) (fun q =>
                          if q = o then ArithmeticRun.pure [o + k • a] else
                            ArithmeticRun.bind (walkOrbit a o f q) (fun tail => ArithmeticRun.pure ((o + k • a) :: tail))) := rfl
                rw [e]
                have hq : o + k • a + a = o + (k+1) • a := by rw [succ_nsmul]; abel
                by_cases hk1 : k + 1 = addOrderOf a
                · have : o + k • a + a = o := by rw [hq, hk1, addOrderOf_nsmul_eq_zero, add_zero]
                  simp only [ArithmeticRun.bind, ArithmeticRun.addGroup, this, if_true, ArithmeticRun.pure]
                  have : addOrderOf a - k = 1 := by omega
                  rw [this]; simp
                · have hne : o + k • a + a ≠ o := by
                    rw [hq]; intro h'
                    have : (k+1) • a = 0 := by simpa using h'
                    exact nsmul_ne_zero_of_lt_addOrderOf (by omega) (by omega) this
                  simp only [ArithmeticRun.bind, ArithmeticRun.addGroup, hne, if_false, ArithmeticRun.pure]
                  rw [hq, ih (k+1) (by omega) (by omega)]
                  have : addOrderOf a - k = (addOrderOf a - (k+1)) + 1 := by omega
                  rw [this, List.range'_succ]; simp
            have hlenE : P.enumeration.length = Fintype.card G := by
              rw [← List.toFinset_card_of_nodup P.nodup]
              congr 1
              ext g; simp [P.complete g]
            have horb : ∀ (a o : G), (walkOrbit a o P.enumeration.length o).result =
                List.map (fun i => o + i • a) (List.range (addOrderOf a)) := by
              intro a o
              have := horbk a o P.enumeration.length 0 (addOrderOf_pos a)
                (by rw [hlenE]; exact Nat.sub_le_of_le_add (by simpa using addOrderOf_le_card (x := a)))
              simpa [List.range_eq_range'] using this
            have hclos : ∀ (a : G) (S : List G), (∀ x ∈ S, x + a ∈ S) → ∀ k : ℕ, ∀ x ∈ S, x + k • a ∈ S := by
              intro a S hS k
              induction k with
              | zero => intro x hx; simpa using hx
              | succ k ih => intro x hx; rw [succ_nsmul, ← add_assoc]; exact hS _ (ih x hx)
            have hone : ∀ (j : Fin n) (a : G) (c : ℝ) (t : ValueTable G n) (seen : List G)
                (tr : List ArithmeticStep) (p : G), (seen.Nodup ∧ ∀ x ∈ seen, x + a ∈ seen) →
                let s : ArithmeticRun (ValueTable G n × List G) := ⟨(t, seen), tr⟩
                let r := (do
                    let (t, seen) ← s
                    if p ∈ seen then pure (t, seen)
                    else
                      let orbit ← walkOrbit a p P.enumeration.length p
                      let t₁ ← sweep j c orbit t
                      let t₂ ← sweep j c orbit t₁
                      pure (t₂, seen ++ orbit) : ArithmeticRun (ValueTable G n × List G))
                (r.result.2.Nodup ∧ ∀ x ∈ r.result.2, x + a ∈ r.result.2) ∧
                  r.steps + 7 * seen.length + (if p ∈ seen then 0 else
                    3 - (relax j c (t ((walkOrbit a p P.enumeration.length p).result.getLast?.getD 0)) (t p)).steps)
                    ≤ tr.length + 7 * r.result.2.length := by
              intro j a c t seen tr p hs s r
              have hr : 0 < addOrderOf a := addOrderOf_pos a
              by_cases hp : p ∈ seen
              · have e : r = ⟨(t, seen), tr ++ []⟩ := by
                  simp only [r, s]; show ArithmeticRun.bind _ _ = _
                  simp [ArithmeticRun.bind, hp]; try exact ⟨rfl, rfl⟩
                rw [e]; exact ⟨hs, by simp [ArithmeticRun.steps, hp]⟩
              · set O := walkOrbit a p P.enumeration.length p with hO
                have e : r = ⟨((sweep j c O.result (sweep j c O.result t).result).result, seen ++ O.result),
                    tr ++ (O.trace ++ ((sweep j c O.result t).trace ++ ((sweep j c O.result (sweep j c O.result t).result).trace ++ [])))⟩ := by
                  simp only [r, s]; show ArithmeticRun.bind _ _ = _
                  simp only [ArithmeticRun.bind, hp, if_false]; rfl
                rw [e]
                have hOr := horb a p
                rw [← hO] at hOr
                have hOnd : O.result.Nodup := by
                  rw [hOr]
                  refine List.Nodup.map_on ?_ List.nodup_range
                  intro x hx y hy hxy
                  simp only [List.mem_range] at hx hy
                  exact nsmul_injOn_Iio_addOrderOf hx hy (add_left_cancel hxy)
                have hdisj : ∀ x ∈ seen, x ∉ O.result := by
                  intro x hx hxO
                  rw [hOr, List.mem_map] at hxO
                  obtain ⟨i, hi, rfl⟩ := hxO
                  rw [List.mem_range] at hi
                  apply hp
                  have := hclos a seen hs.2 (addOrderOf a - i) _ hx
                  rwa [add_assoc, ← add_nsmul, Nat.add_sub_cancel' hi.le, addOrderOf_nsmul_eq_zero, add_zero] at this
                refine ⟨⟨?_, ?_⟩, ?_⟩
                · exact List.Nodup.append hs.1 hOnd (fun x hx hx' => hdisj x hx hx')
                · intro x hx
                  simp only [List.mem_append] at hx ⊢
                  rcases hx with hx | hx
                  · exact Or.inl (hs.2 x hx)
                  · right
                    rw [hOr, List.mem_map] at hx ⊢
                    obtain ⟨i, hi, rfl⟩ := hx
                    rw [List.mem_range] at hi
                    by_cases hi1 : i + 1 = addOrderOf a
                    · refine ⟨0, by simpa using hr, ?_⟩
                      rw [add_assoc, ← succ_nsmul, hi1, addOrderOf_nsmul_eq_zero]; simp
                    · exact ⟨i+1, by rw [List.mem_range]; omega, by rw [succ_nsmul, add_assoc]⟩
                · have h1 := hwalk a p P.enumeration.length p
                  rw [← hO] at h1
                  have h2 := hsweep j c O.result t
                  have h3 := hsweep j c O.result (sweep j c O.result t).result
                  obtain ⟨tail, htail⟩ : ∃ tail, O.result = p :: tail := by
                    rw [hOr]
                    obtain ⟨k, hk⟩ : ∃ k, addOrderOf a = k + 1 := ⟨addOrderOf a - 1, by omega⟩
                    rw [hk, List.range_succ_eq_map]; simp
                  have h2' := hsweep0 j c p tail t
                  have h4 := hrelax j c (t ((p :: tail).getLast?.getD 0)) (t p)
                  have hlen1 : O.result.length = tail.length + 1 := by rw [htail]; rfl
                  rw [← htail] at h2' h4
                  rw [if_neg hp]
                  simp only [ArithmeticRun.steps] at h1 h2 h3 h2' h4 ⊢
                  simp only [List.length_append, List.length_nil]
                  omega
            have hfold : ∀ {α : Type} (f : ArithmeticRun α → G → ArithmeticRun α) (I : α → Prop) (μ : α → ℕ),
                (∀ s x, I s.result → I (f s x).result ∧ (f s x).steps + 7 * μ s.result ≤ s.steps + 7 * μ (f s x).result) →
                ∀ (l : List G) (s : ArithmeticRun α), I s.result →
                  I (l.foldl f s).result ∧ (l.foldl f s).steps + 7 * μ s.result ≤ s.steps + 7 * μ (l.foldl f s).result := by
              intro α f I μ hst l
              induction l with
              | nil => intro s hs; exact ⟨hs, le_refl _⟩
              | cons x l ih =>
                intro s hs
                rw [List.foldl_cons]
                obtain ⟨h1, h2⟩ := hst s x hs
                obtain ⟨h3, h4⟩ := ih (f s x) h1
                exact ⟨h3, by omega⟩
            have hfoldB : ∀ {α : Type} (f : ArithmeticRun α → G → ArithmeticRun α) (I : α → Prop) (μ : α → ℕ) (K : ℕ),
                (∀ s x, I s.result → I (f s x).result ∧ (f s x).steps + 7 * μ s.result ≤ s.steps + 7 * μ (f s x).result) →
                (∀ st, I st → μ st ≤ K) →
                ∀ (l : List G) (s : ArithmeticRun α), I s.result → (l.foldl f s).steps ≤ s.steps + 7 * K := by
              intro α f I μ K hst hK l s hs
              obtain ⟨h1, h2⟩ := hfold f I μ hst l s hs
              have := hK _ h1
              omega
            have hfin : ∀ (x : ArithmeticRun (ValueTable G n × List G)),
                (do let (t, _) ← x; pure t : ArithmeticRun (ValueTable G n)).steps = x.steps := by
              intro x; obtain ⟨⟨t, s⟩, tr⟩ := x
              show (tr ++ []).length = tr.length
              simp
            have hlenS : ∀ S : List G, S.Nodup → S.length ≤ detD B := by
              intro S hS; rw [← hcard]; exact hS.length_le_card
            have hstage : ∀ (j : Fin n) (a : G) (c : ℝ) (t : ValueTable G n),
                (tabulateStage P.enumeration j a c t).steps ≤ 7 * detD B := by
              intro j a c t
              unfold tabulateStage
              refine le_trans (le_of_eq (hfin _)) ?_
              refine le_trans (hfoldB _ (fun st : ValueTable G n × List G => st.2.Nodup ∧ ∀ x ∈ st.2, x + a ∈ st.2)
                (fun st => st.2.length) (detD B) ?_ ?_ _ _ ?_) ?_
              · intro s x hs
                obtain ⟨⟨t, seen⟩, tr⟩ := s
                obtain ⟨h1, h2⟩ := hone j a c t seen tr x hs
                exact ⟨h1, le_trans (Nat.le_add_right _ _) h2⟩
              · intro st hst; exact hlenS _ hst.1
              · exact ⟨List.nodup_nil, fun x hx => absurd hx List.not_mem_nil⟩
              · show 0 + _ ≤ _; simp
            have hfoldS : ∀ {α : Type} (f : ArithmeticRun α → G → ArithmeticRun α) (I : α → Prop) (μ : α → ℕ) (K : ℕ),
                (∀ s x, I s.result → I (f s x).result ∧ (f s x).steps + 7 * μ s.result ≤ s.steps + 7 * μ (f s x).result) →
                (∀ st, I st → μ st ≤ K) →
                ∀ (rest : List G) (s : ArithmeticRun α) (x : G),
                  (I (f s x).result ∧ (f s x).steps + 1 ≤ 7 * μ (f s x).result) →
                  (rest.foldl f (f s x)).steps + 1 ≤ 7 * K := by
              intro α f I μ K hst hK rest s x hs
              obtain ⟨h1, h2⟩ := hfold f I μ hst rest (f s x) hs.1
              have := hK _ h1
              have := hs.2
              omega
            have hconsF : ∀ {α : Type} (f : ArithmeticRun α → G → ArithmeticRun α) (l : List G) (s : ArithmeticRun α)
                (x : G) (rest : List G), l = x :: rest → l.foldl f s = rest.foldl f (f s x) := by
              intro α f l s x rest h; subst h; rfl
            obtain ⟨p0, rest, hE⟩ : ∃ p0 rest, P.enumeration = p0 :: rest := by
              rcases h : P.enumeration with _ | ⟨p0, rest⟩
              · have := P.complete 0; rw [h] at this; simp at this
              · exact ⟨p0, rest, rfl⟩
            have hinit : ∀ q : G, initialTable (G := G) n q = none ∨ initialTable (G := G) n q = some (0, fun _ => 0) := by
              intro q; unfold initialTable; split_ifs <;> simp
            have hstage0 : ∀ (j : Fin n) (a : G) (c : ℝ), c ≤ 0 →
                (tabulateStage P.enumeration j a c (initialTable n)).steps + 1 ≤ 7 * detD B := by
              intro j a c hc
              unfold tabulateStage
              rw [hfin _, hconsF _ P.enumeration _ p0 rest hE]
              refine hfoldS _ (fun st : ValueTable G n × List G => st.2.Nodup ∧ ∀ x ∈ st.2, x + a ∈ st.2)
                (fun st => st.2.length) (detD B) ?_ ?_ rest _ p0 ?_
              · intro s x hs
                obtain ⟨⟨t, seen⟩, tr⟩ := s
                obtain ⟨h1, h2⟩ := hone j a c t seen tr x hs
                exact ⟨h1, le_trans (Nat.le_add_right _ _) h2⟩
              · intro st hst; exact hlenS _ hst.1
              · obtain ⟨h1, h2⟩ := hone j a c (initialTable n) [] [] p0 ⟨List.nodup_nil, fun x hx => absurd hx List.not_mem_nil⟩
                refine ⟨h1, ?_⟩
                have hk := hrelax2 j c _ _ hc (hinit ((walkOrbit a p0 P.enumeration.length p0).result.getLast?.getD 0)) (hinit p0)
                have hite : (if p0 ∈ ([] : List G) then 0 else 3 - (relax j c (initialTable n
                    ((walkOrbit a p0 P.enumeration.length p0).result.getLast?.getD 0)) (initialTable n p0)).steps) =
                    3 - (relax j c (initialTable n
                    ((walkOrbit a p0 P.enumeration.length p0).result.getLast?.getD 0)) (initialTable n p0)).steps :=
                  if_neg List.not_mem_nil
                refine le_trans ?_ (le_trans h2 ?_)
                · rw [hite]
                  have h3 : 1 ≤ 3 - (relax j c (initialTable n
                    ((walkOrbit a p0 P.enumeration.length p0).result.getLast?.getD 0)) (initialTable n p0)).steps := by omega
                  refine le_trans (Nat.add_le_add_left h3 _) ?_
                  simp only [List.length_nil, mul_zero, add_zero]
                  exact le_rfl
                · simp only [List.length_nil, zero_add]
                  exact le_rfl
            have hcost : ∀ j, costs j ≤ 0 := by intro j; rw [hcosts]; exact hopt j
            have htabfold : ∀ (l : List (Fin n)) (s : ArithmeticRun (ValueTable G n)),
                (l.foldl (fun state j => do
                  let table ← state
                  tabulateStage P.enumeration j (images j) (costs j) table) s).steps ≤ s.steps + 7 * detD B * l.length := by
              intro l
              induction l with
              | nil => intro s; simp
              | cons x l ih =>
                intro s
                rw [List.foldl_cons]
                refine le_trans (ih _) ?_
                have := hstage x (images x) (costs x) s.result
                show (s.trace ++ (tabulateStage P.enumeration x (images x) (costs x) s.result).trace).length + _ ≤ _
                simp only [ArithmeticRun.steps] at this ⊢
                rw [List.length_append, List.length_cons]
                nlinarith
            obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
            have hD : 0 < detD B := by rw [← hcard]; exact Fintype.card_pos
            show (tabulate P.enumeration images costs).steps < _
            unfold tabulate
            rw [List.finRange_succ, List.foldl_cons]
            refine lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.succ_le_of_lt ?_)) (le_of_eq rfl)
            refine lt_of_le_of_lt (htabfold _ _) ?_
            have h0 := hstage0 0 (images 0) (costs 0) (hcost 0)
            show (([] : List ArithmeticStep) ++ (tabulateStage P.enumeration 0 (images 0) (costs 0) (initialTable (k+1))).trace).length + _ < _
            simp only [ArithmeticRun.steps] at h0
            rw [List.nil_append, List.length_map, List.length_finRange]
            have : 7 * (k + 1) * detD B = 7 * detD B + 7 * detD B * k := by ring
            omega
        have hrec1 : ∀ p : G, ∀ (z : ℝ) (y : Fin n → ℕ), forward.result p = some (z, y) →
            (recoverOne forward.result p).result = some y ∧
            (recoverOne forward.result p).steps = n := by
          intro p z y h
          simp only [recoverOne, h]
          refine ⟨?_, ?_⟩
          · show some (copyVector y).result = some y
            rw [(hcopy y).1]
          · show ((copyVector y).trace ++ []).length = n
            rw [List.append_nil]; exact (hcopy y).2
        have hrecAll : ∀ (l : List G) (s : ArithmeticRun (G → Option (Fin n → ℕ))),
            (l.foldl (fun state p => do
              let t ← state
              let y ← recoverOne forward.result p
              pure (Function.update t p y)) s).result =
              (fun p => if p ∈ l then (recoverOne forward.result p).result else s.result p) ∧
            (l.foldl (fun state p => do
              let t ← state
              let y ← recoverOne forward.result p
              pure (Function.update t p y)) s).steps = s.steps + n * l.length := by
          intro l
          induction l with
          | nil => intro s; simp
          | cons a l ih =>
            intro s
            rw [List.foldl_cons]
            obtain ⟨h1, h2⟩ := ih _
            refine ⟨?_, ?_⟩
            · rw [h1]; funext q
              show _ = if q ∈ a :: l then (recoverOne forward.result q).result else s.result q
              by_cases hq : q ∈ l
              · simp [hq]
              · simp only [hq, if_false, List.mem_cons]
                show (Function.update s.result a (recoverOne forward.result a).result) q = _
                by_cases hqa : q = a
                · subst hqa; simp
                · simp [hqa]
            · rw [h2]
              obtain ⟨z, y, hy, -⟩ := hDP a
              show (s.trace ++ ((recoverOne forward.result a).trace ++ [])).length + n * l.length = _
              rw [List.append_nil, List.length_append]
              have := (hrec1 a z y hy).2
              simp only [ArithmeticRun.steps] at this ⊢
              rw [this, List.length_cons]; ring
        have hlen : P.enumeration.length = detD B := by
          rw [← hcard, ← List.toFinset_card_of_nodup P.nodup]
          congr 1
          ext g; simp [P.complete g]
        refine ⟨hcard, hsteps, ?_, ?_, ?_, ?_⟩
        · intro p
          obtain ⟨z, y, h1, h2, -⟩ := hDP p
          exact ⟨z, y, h1, h2⟩
        · intro b
          obtain ⟨z, y, h1, h2, h3⟩ := hDP (P.quotientMap b)
          obtain ⟨r1, r2⟩ := hrec1 _ z y h1
          exact ⟨r2, y, r1, (h2 b rfl).2, h3⟩
        · unfold recoverAll
          rw [(hrecAll _ _).2, hlen]
          simp [ArithmeticRun.steps]; rfl
        · intro b
          obtain ⟨z, y, h1, h2, h3⟩ := hDP (P.quotientMap b)
          obtain ⟨r1, r2⟩ := hrec1 _ z y h1
          refine ⟨y, ?_, (h2 b rfl).2, h3⟩
          unfold recoverAll
          rw [(hrecAll _ _).1]
          simp [P.complete, r1]
