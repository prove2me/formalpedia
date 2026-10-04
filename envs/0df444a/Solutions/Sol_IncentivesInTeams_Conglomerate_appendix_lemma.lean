-- Prove2me | solution 1 for IncentivesInTeams.Conglomerate.appendix_lemma
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-03T12:42:44.661225+00:00
-- url     : https://prove2.me/submissions/a1538076-e4af-4562-a6ca-11f64cb482c0

import Definitions.Def_IncentivesInTeams_Conglomerate_Model

open IncentivesInTeams.Conglomerate

namespace OwnProfitProof

variable {ι : Type*} [DecidableEq ι] {S₀ : Type*} {S : ι → Type*}
  {Z₀ : Type*} {Z M₀ M : ι → Type*} {D₀ : Type*} {D : ι → Type*}

private theorem fiber_fst (β : JointStrategy S₀ S Z₀ Z M₀ M D₀ D)
    (y : Z₀ × ∀ k, M k) (hne : {s | β.headInfo s = y}.Nonempty) :
    Prod.fst '' {s | β.headInfo s = y} = {t | β.head.obs t = y.1} := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact congrArg Prod.fst hs
  · intro ht
    obtain ⟨s, hs⟩ := hne
    change β.head.obs t = y.1 at ht
    change β.headInfo s = y at hs
    have hs0 : β.head.obs s.1 = y.1 := congrArg Prod.fst hs
    refine ⟨(t, s.2), ?_, rfl⟩
    change β.headInfo (t, s.2) = y
    simpa only [JointStrategy.headInfo, JointStrategy.subInfo, ht.trans hs0.symm] using hs

private theorem fiber_sub (β : JointStrategy S₀ S Z₀ Z M₀ M D₀ D)
    (y : Z₀ × ∀ k, M k) (hne : {s | β.headInfo s = y}.Nonempty) (j : ι) :
    (fun s : S₀ × ∀ k, S k => s.2 j) '' {s | β.headInfo s = y} =
      {t | (β.sub j).msg ((β.sub j).obs t, β.head.msg j y.1) = y.2 j} := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs0 : β.head.obs s.1 = y.1 := congrArg Prod.fst hs
    have hsj := congrFun (congrArg Prod.snd hs) j
    simpa only [JointStrategy.headInfo, JointStrategy.subInfo, hs0, Set.mem_ofPred_eq] using hsj
  · intro ht
    obtain ⟨s, hs⟩ := hne
    change β.headInfo s = y at hs
    have hs0 : β.head.obs s.1 = y.1 := congrArg Prod.fst hs
    refine ⟨(s.1, Function.update s.2 j t), ?_, Function.update_self j t s.2⟩
    change β.headInfo (s.1, Function.update s.2 j t) = y
    apply Prod.ext hs0
    funext k
    by_cases hkj : k = j
    · subst k
      simpa only [JointStrategy.headInfo, JointStrategy.subInfo,
        Function.update_self, hs0, Set.mem_ofPred_eq] using ht
    · simpa only [JointStrategy.headInfo, JointStrategy.subInfo,
        Function.update_of_ne hkj] using congrFun (congrArg Prod.snd hs) k

end OwnProfitProof

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S₀ : Type*} [Fintype S₀]
    {S : ι → Type*} [∀ i, Fintype (S i)] {Z₀ : Type*} {Z M₀ M : ι → Type*}
    {D₀ : Type*} {D : ι → Type*} (T : Model S₀ S Z₀ Z M₀ M D₀ D)
    (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (i : ι)
    (b : SubStrategy (S i) (Z i) (M₀ i) (M i) (D i)) (hb : b ∈ T.B i)
    (s : S₀ × ∀ k, S k)
    (hB : {s' | βs.headInfo s' = (βs.update i b).headInfo s}.Nonempty) :
    Prod.fst '' {s' | (βs.update i b).headInfo s' = (βs.update i b).headInfo s} =
        Prod.fst '' {s' | βs.headInfo s' = (βs.update i b).headInfo s} ∧
      ∀ j, j ≠ i →
        (fun s' : S₀ × ∀ k, S k => s'.2 j) ''
            {s' | (βs.update i b).headInfo s' = (βs.update i b).headInfo s} =
          (fun s' : S₀ × ∀ k, S k => s'.2 j) ''
            {s' | βs.headInfo s' = (βs.update i b).headInfo s} := by
  have hA : {s' | (βs.update i b).headInfo s' = (βs.update i b).headInfo s}.Nonempty :=
    ⟨s, rfl⟩
  constructor
  · rw [OwnProfitProof.fiber_fst _ _ hA, OwnProfitProof.fiber_fst _ _ hB]
    rfl
  · intro j hji
    rw [OwnProfitProof.fiber_sub _ _ hA, OwnProfitProof.fiber_sub _ _ hB]
    simp only [JointStrategy.update, Function.update_of_ne hji]
