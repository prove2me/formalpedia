-- Prove2me | solution 1 for OAI.PiExponent.select_separated_denominators
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-15T05:33:06.23248+00:00
-- url     : https://prove2.me/submissions/af3fd522-310f-4990-9642-0d80bf4390a7

-- Adapted from Eyal1990 submission 496eb62d-9635-4b3c-a6c8-7d15973808f5.
import Definitions.Def_PiExponent_DeterminantSetup

private theorem separatedWeights_append_final
    (S : List ℕ → ℕ) {m : ℕ} (w : Fin m → ℕ) (x : ℕ)
    (hw : OAI.PiExponent.separatedWeights S w)
    (hx : S (List.ofFn w) ≤ x) :
    OAI.PiExponent.separatedWeights S
      (Fin.snoc (α := fun _ => ℕ) w x) := by
  intro i
  induction i using Fin.lastCases with
  | last =>
      have hpref :
          (fun k : Fin m =>
            Fin.snoc (α := fun _ => ℕ) w x
              ⟨k.val, Nat.lt_trans k.isLt (Fin.last m).isLt⟩) = w := by
        funext k
        change Fin.snoc (α := fun _ => ℕ) w x k.castSucc = w k
        simp only [Fin.snoc_castSucc]
      change S (List.ofFn (fun k : Fin m =>
        Fin.snoc (α := fun _ => ℕ) w x
          ⟨k.val, Nat.lt_trans k.isLt (Fin.last m).isLt⟩)) ≤
        Fin.snoc (α := fun _ => ℕ) w x (Fin.last m)
      rw [hpref, Fin.snoc_last]
      exact hx
  | cast i =>
      have hpref :
          (fun k : Fin i.val =>
            Fin.snoc (α := fun _ => ℕ) w x
              ⟨k.val, Nat.lt_trans k.isLt i.castSucc.isLt⟩) =
          (fun k : Fin i.val =>
            w ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩) := by
        funext k
        change Fin.snoc (α := fun _ => ℕ) w x
          (Fin.castSucc ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩) =
            w ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩
        simp only [Fin.snoc_castSucc]
      change S (List.ofFn (fun k : Fin i.val =>
        Fin.snoc (α := fun _ => ℕ) w x
          ⟨k.val, Nat.lt_trans k.isLt i.castSucc.isLt⟩)) ≤
        Fin.snoc (α := fun _ => ℕ) w x i.castSucc
      rw [hpref, Fin.snoc_castSucc]
      exact hw i

theorem solution
    (R : ℤ → ℕ → Prop)
    (hR : ∀ L : ℕ, ∃ (p : ℤ) (q : ℕ),
      2 ≤ q ∧ p ≠ 0 ∧ L ≤ Nat.ceil (Real.log (q : ℝ)) ∧ R p q)
    (m W : ℕ) (S : List ℕ → ℕ) :
    ∃ (p : Fin m → ℤ) (q : Fin m → ℕ),
      (∀ i : Fin m, 2 ≤ q i ∧ p i ≠ 0 ∧
        W ≤ Nat.ceil (Real.log (q i : ℝ)) ∧ R (p i) (q i)) ∧
      OAI.PiExponent.separatedWeights S
        (fun i : Fin m => Nat.ceil (Real.log (q i : ℝ))) := by
  induction m with
  | zero =>
      refine ⟨Fin.elim0, Fin.elim0, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ m ih =>
      obtain ⟨p, q, hpairs, hsep⟩ := ih
      let w : Fin m → ℕ := fun i => Nat.ceil (Real.log (q i : ℝ))
      obtain ⟨pNew, qNew, hNew⟩ := hR (max W (S (List.ofFn w)))
      let wNew : ℕ := Nat.ceil (Real.log (qNew : ℝ))
      refine ⟨Fin.snoc (α := fun _ => ℤ) p pNew,
        Fin.snoc (α := fun _ => ℕ) q qNew, ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last =>
            simp only [Fin.snoc_last]
            exact ⟨hNew.1, hNew.2.1,
              Nat.le_trans (Nat.le_max_left _ _) hNew.2.2.1,
              hNew.2.2.2⟩
        | cast i =>
            simpa only [Fin.snoc_castSucc] using hpairs i
      · have hweights :
            (fun i : Fin (m + 1) =>
              Nat.ceil (Real.log
                ((Fin.snoc (α := fun _ => ℕ) q qNew) i : ℝ))) =
              Fin.snoc (α := fun _ => ℕ) w wNew := by
          funext i
          induction i using Fin.lastCases with
          | last => simp only [Fin.snoc_last, wNew]
          | cast i => simp only [Fin.snoc_castSucc, w]
        rw [hweights]
        exact separatedWeights_append_final S w wNew hsep
          (Nat.le_trans (Nat.le_max_right _ _) hNew.2.2.1)
