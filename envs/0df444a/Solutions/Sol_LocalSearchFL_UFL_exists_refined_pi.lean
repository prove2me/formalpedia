-- Prove2me | solution 1 for LocalSearchFL.UFL.exists_refined_pi
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-04T11:34:43.004513+00:00
-- url     : https://prove2.me/submissions/5040e3d4-089c-4243-a9e0-857379d8697d

import Definitions.Def_LocalSearchFL_UFL_captures

open LocalSearchFL.UFL

private theorem refined_fiber {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (o : Fa) :
    ∃ e : Equiv.Perm {j // σO j = o}, ∀ x,
      σS (e x).1 ≠ σS x.1 ∨ (captures σS σO (σS x.1) o ∧ (e x).1 = x.1) := by
  classical
  let N := nbhd σO o
  let A (x : {j // σO j = o}) :=
    N.filter (fun y => σS y ≠ σS x.1 ∨ (captures σS σO (σS x.1) o ∧ y = x.1))
  have hall : ∀ s : Finset {j // σO j = o}, s.card ≤ (s.biUnion A).card := by
    intro s
    have hsN : s.card ≤ N.card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro x _; simpa [N, nbhd] using x.2
      · intro x _ y _ h; exact Subtype.ext h
    by_cases hfull : N ⊆ s.biUnion A
    · exact hsN.trans (Finset.card_le_card hfull)
    obtain ⟨y, hyN, hy⟩ := Finset.not_subset.mp hfull
    rcases s.eq_empty_or_nonempty with hs | ⟨x0, hx0⟩
    · simp [hs]
    have key : ∀ x ∈ s, σS y = σS x.1 := by
      intro x hx
      by_contra h
      exact hy (Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨hyN, Or.inl h⟩⟩)
    by_cases hcap : captures σS σO (σS y) o
    · apply Finset.card_le_card_of_injOn Subtype.val
      · intro x hx
        refine Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨?_, Or.inr ⟨?_, rfl⟩⟩⟩
        · simpa [N, nbhd] using x.2
        · simpa only [← key x hx] using hcap
      · intro x _ z _ h; exact Subtype.ext h
    · have hsmall : s.card ≤ (N.filter (fun j => σS j = σS y)).card := by
        apply Finset.card_le_card_of_injOn Subtype.val
        · intro x hx
          exact Finset.mem_filter.mpr ⟨by simpa [N, nbhd] using x.2, (key x hx).symm⟩
        · intro x _ z _ h; exact Subtype.ext h
      have hinter : N ∩ nbhd σS (σS y) = N.filter (fun j => σS j = σS y) := by
        ext j; simp [nbhd]
      have hhalf : 2 * (N.filter (fun j => σS j = σS y)).card ≤ N.card := by
        unfold captures at hcap
        change ¬ N.card < 2 * (N ∩ nbhd σS (σS y)).card at hcap
        rw [hinter] at hcap
        omega
      have hsplit := Finset.card_filter_add_card_filter_not (s := N) (fun j => σS j = σS y)
      have hsub : N.filter (fun j => σS j ≠ σS y) ⊆ s.biUnion A := by
        intro j hj
        obtain ⟨hjN, hj⟩ := Finset.mem_filter.mp hj
        refine Finset.mem_biUnion.mpr ⟨x0, hx0, Finset.mem_filter.mpr ⟨hjN, Or.inl ?_⟩⟩
        simpa only [← key x0 hx0] using hj
      have hcard := Finset.card_le_card hsub
      simp only [ne_eq] at hcard
      omega
  obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective A).mp hall
  have hfo : ∀ x, σO (f x) = o := by
    intro x
    have := (Finset.mem_filter.mp (hf x)).1
    simpa [N, nbhd] using this
  let g : {j // σO j = o} → {j // σO j = o} := fun x => ⟨f x, hfo x⟩
  have hg : Function.Injective g := fun x y h => hinj (congrArg Subtype.val h)
  refine ⟨Equiv.ofBijective g hg.bijective_of_finite, ?_⟩
  intro x
  exact (Finset.mem_filter.mp (hf x)).2

theorem solution {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) :
    ∃ π : Equiv.Perm Cl, IsRefinedPi σS σO π := by
  classical
  choose e he using refined_fiber σS σO
  let π : Equiv.Perm Cl := (Equiv.sigmaFiberEquiv σO).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv σO))
  have happ (j : Cl) : π j = (e (σO j) ⟨j, rfl⟩).1 := rfl
  have hpres (j : Cl) : σO (π j) = σO j := (e (σO j) ⟨j, rfl⟩).2
  have hrel (j : Cl) : σS (π j) ≠ σS j ∨
      (captures σS σO (σS j) (σO j) ∧ π j = j) := he (σO j) ⟨j, rfl⟩
  refine ⟨π, hpres, ?_, ?_⟩
  · intro s o hn j hj hmem
    have hjS : σS j = s := by simpa [nbhd] using (Finset.mem_inter.mp hj).2
    have hjO : σO j = o := by simpa [nbhd] using (Finset.mem_inter.mp hj).1
    have hπS : σS (π j) = s := by simpa [nbhd] using (Finset.mem_inter.mp hmem).2
    rcases hrel j with h | h
    · exact h (hπS.trans hjS.symm)
    · exact hn (by simpa only [hjS, hjO] using h.1)
  · intro s o _ j hj hmem
    have hjS : σS j = s := by simpa [nbhd] using (Finset.mem_inter.mp hj).2
    have hπS : σS (π j) = s := by simpa [nbhd] using (Finset.mem_inter.mp hmem).2
    exact (hrel j).resolve_left (fun h => h (hπS.trans hjS.symm)) |>.2

#print axioms solution
