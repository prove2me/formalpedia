-- Prove2me | solution 1 for MondererShapley.ClosedPath.closed_paths_of_four
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:23:28.164659+00:00
-- url     : https://prove2.me/submissions/735de1cd-8101-48a4-a3a6-af07d4ccb36a

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_FinPath
import Definitions.Def_MondererShapley_ClosedPath_IsPotentialGame

namespace MondererShapley.ClosedPath
variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

theorem exchange (u : ι → (∀ i, Y i) → ℝ)
    (hfour : ∀ γ : FinPath Y, γ.IsSimpleClosed → γ.len = 4 → γ.I u = 0)
    (a b c : ∀ i, Y i) (i k : ι) (hik : i ≠ k)
    (hab : IsStep a b i) (hbc : IsStep b c k) :
    let z := Function.update a k (c k)
    IsStep a z k ∧ IsStep z c i ∧
      (u i b - u i a) + (u k c - u k b) =
        (u k z - u k a) + (u i c - u i z) := by
  classical
  let z := Function.update a k (c k)
  have hki := hik.symm
  have hbi : b i ≠ a i := hab.1
  have hbk : b k = a k := hab.2 k hki
  have hci : c i = b i := hbc.2 i hik
  have hck : c k ≠ a k := by simpa [hbk] using hbc.1
  have haz : IsStep a z k := ⟨by simpa [z] using hck, fun j hj => by simp [z, hj]⟩
  have hzc : IsStep z c i := by
    refine ⟨by simpa [z, hik, hci] using hbi, ?_⟩
    intro j hj
    by_cases hjk : j = k
    · subst j; simp [z]
    · simpa [z, hjk] using (hbc.2 j hjk).trans (hab.2 j hj)
  have hab' : a ≠ b := fun he => hbi (congrFun he.symm i)
  have hbc' : b ≠ c := fun he => hbc.1 (congrFun he.symm k)
  have haz' : a ≠ z := fun he => haz.1 (congrFun he.symm k)
  have hzc' : z ≠ c := fun he => hzc.1 (congrFun he.symm i)
  have hac' : a ≠ c := by
    intro he; apply hck; exact congrFun he.symm k
  have hbz' : b ≠ z := by
    intro he; apply hbi
    have hh := congrFun he i
    simpa [z, hik] using hh
  let γ : FinPath Y :=
    { len := 4
      pt := ![a, b, c, z, a]
      dev := ![i, k, i, k]
      step := by
        intro j; fin_cases j
        · exact hab
        · exact hbc
        · exact ⟨hzc.1.symm, fun j hj => (hzc.2 j hj).symm⟩
        · exact ⟨haz.1.symm, fun j hj => (haz.2 j hj).symm⟩ }
  have hs : γ.IsSimpleClosed := by
    refine ⟨rfl, ?_⟩
    intro l j hl hj hlj
    fin_cases l <;> fin_cases j <;>
      simp_all [γ, ne_comm]
  have hz := hfour γ hs rfl
  norm_num [γ, FinPath.I, Fin.sum_univ_succ] at hz
  exact ⟨haz, hzc, by dsimp [z] at hz; linarith⟩

theorem square_update (u : ι → (∀ i, Y i) → ℝ)
    (hfour : ∀ γ : FinPath Y, γ.IsSimpleClosed → γ.len = 4 → γ.I u = 0)
    (a : ∀ i, Y i) (j i : ι) (hji : j ≠ i) (x : Y j) (y : Y i) :
    (u j (Function.update a j x) - u j a) +
      (u i (Function.update (Function.update a j x) i y) - u i (Function.update a j x)) =
    (u i (Function.update a i y) - u i a) +
      (u j (Function.update (Function.update a i y) j x) - u j (Function.update a i y)) := by
  classical
  by_cases hx : x = a j
  · subst x
    have he : Function.update (Function.update a i y) j (a j) = Function.update a i y := by
      rw [Function.update_comm hji.symm]; simp
    simp [he]
  by_cases hy : y = a i
  · subst y
    have he : Function.update (Function.update a j x) i (a i) = Function.update a j x := by
      rw [Function.update_comm hji]; simp
    simp [he]
  have hab : IsStep a (Function.update a j x) j :=
    ⟨by simpa using hx, fun k hk => by simp [hk]⟩
  have hbc : IsStep (Function.update a j x) (Function.update (Function.update a j x) i y) i :=
    ⟨by simpa [hji.symm] using hy, fun k hk => by simp [hk]⟩
  have he := (exchange u hfour a (Function.update a j x)
    (Function.update (Function.update a j x) i y) j i hji hab hbc).2.2
  simpa [hji.symm, Function.update_comm hji] using he

noncomputable def mask (base a : ∀ i, Y i) (s : Finset ι) : ∀ i, Y i :=
  fun j => if j ∈ s then a j else base j

theorem mask_update_mem (base a : ∀ i, Y i) (s : Finset ι) {j : ι}
    (hj : j ∈ s) (x : Y j) :
    mask base (Function.update a j x) s = Function.update (mask base a s) j x := by
  funext k
  by_cases hk : k = j
  · subst k; simp [mask, hj]
  · simp [mask, hk]

theorem mask_update_not_mem (base a : ∀ i, Y i) (s : Finset ι) {j : ι}
    (hj : j ∉ s) (x : Y j) :
    mask base (Function.update a j x) s = mask base a s := by
  funext k
  by_cases hk : k = j
  · subst k; simp [mask, hj]
  · simp [mask, hk]

theorem mask_insert (base a : ∀ i, Y i) (s : Finset ι) (i : ι) :
    mask base a (insert i s) = Function.update (mask base a s) i (a i) := by
  funext k
  by_cases hk : k = i
  · subst k; simp [mask]
  · simp [mask, hk]

theorem potential_from_four [Fintype ι] (u : ι → (∀ i, Y i) → ℝ)
    (hfour : ∀ γ : FinPath Y, γ.IsSimpleClosed → γ.len = 4 → γ.I u = 0) :
    IsPotentialGame u := by
  classical
  by_cases hn : Nonempty (∀ i, Y i)
  · let base := Classical.choice hn
    have aux (s : Finset ι) : ∃ P : (∀ i, Y i) → ℝ,
        (∀ a b, (∀ j ∈ s, a j = b j) → P a = P b) ∧
        (∀ j ∈ s, ∀ a x, P (Function.update a j x) - P a =
          u j (mask base (Function.update a j x) s) - u j (mask base a s)) := by
      induction s using Finset.induction_on with
      | empty => exact ⟨fun _ => 0, by simp [mask]⟩
      | @insert i s hi ih =>
        obtain ⟨P, hinv, hder⟩ := ih
        let Q := fun a => P a + u i (mask base a (insert i s)) - u i (mask base a s)
        refine ⟨Q, ?_, ?_⟩
        · intro a b hab
          have hp := hinv a b (fun j hj => hab j (by simp [hj]))
          have hm : mask base a (insert i s) = mask base b (insert i s) := by
            funext j; by_cases hj : j ∈ insert i s
            · simp [mask, hj, hab j hj]
            · simp [mask, hj]
          have hm' : mask base a s = mask base b s := by
            funext j; by_cases hj : j ∈ s
            · simp [mask, hj, hab j (by simp [hj])]
            · simp [mask, hj]
          simp [Q, hp, hm, hm']
        · intro j hj a x
          by_cases hji : j = i
          · subst j
            have hp := hinv (Function.update a i x) a (by
              intro j hj; simp [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)])
            simp only [Q, hp, mask_update_not_mem base a s hi x]
            ring
          · have hjs : j ∈ s := by simpa [hji] using hj
            have hd := hder j hjs a x
            have he := square_update u hfour (mask base a s) j i hji x (a i)
            simp only [mask_insert, mask_update_mem base a s hjs x,
              Function.update_of_ne (Ne.symm hji)] at hd ⊢
            dsimp [Q]
            simp only [mask_insert, mask_update_mem base a s hjs x,
              Function.update_of_ne (Ne.symm hji)]
            rw [Function.update_comm hji] at he
            rw [Function.update_comm hji]
            linarith
    obtain ⟨P, _, hd⟩ := aux Finset.univ
    refine ⟨P, ?_⟩
    intro i a x z
    have hx := hd i (Finset.mem_univ i) a x
    have hz := hd i (Finset.mem_univ i) a z
    have hm (b : ∀ i, Y i) : mask base b Finset.univ = b := by funext j; simp [mask]
    simp only [hm] at hx hz
    linarith
  · refine ⟨fun _ => 0, ?_⟩
    intro i a x z; exact (hn ⟨a⟩).elim

end MondererShapley.ClosedPath
open MondererShapley.ClosedPath

theorem closed_from_potential {ι : Type*} [DecidableEq ι] {Y : ι → Type*} [Fintype ι]
    (u : ι → (∀ i, Y i) → ℝ) (P : (∀ i, Y i) → ℝ)
    (hP : IsPotential u P) (γ : FinPath Y) (hγ : γ.IsClosed) : γ.I u = 0 := by
  have hs (k : Fin γ.len) :
      u (γ.dev k) (γ.pt k.succ) - u (γ.dev k) (γ.pt k.castSucc) =
      P (γ.pt k.succ) - P (γ.pt k.castSucc) := by
    have he : Function.update (γ.pt k.castSucc) (γ.dev k) (γ.pt k.succ (γ.dev k)) =
        γ.pt k.succ := by
      funext j
      by_cases hj : j = γ.dev k
      · subst j; simp
      · simpa [hj] using (γ.step k).2 j hj |>.symm
    simpa [he] using hP (γ.dev k) (γ.pt k.castSucc)
      (γ.pt k.succ (γ.dev k)) (γ.pt k.castSucc (γ.dev k))
  unfold FinPath.I
  simp_rw [hs]
  rw [Finset.sum_sub_distrib]
  have h₁ := Fin.sum_univ_succ (fun k => P (γ.pt k))
  have h₂ := Fin.sum_univ_castSucc (fun k => P (γ.pt k))
  have he : P (γ.pt 0) = P (γ.pt (Fin.last γ.len)) := congrArg P hγ
  linarith


theorem solution {ι : Type*} [DecidableEq ι] {Y : ι → Type*} [Fintype ι]
    (u : ι → (∀ i, Y i) → ℝ)
    (hfour : ∀ γ : FinPath Y, γ.IsSimpleClosed → γ.len = 4 → γ.I u = 0) :
    ∀ γ : FinPath Y, γ.IsClosed → γ.I u = 0 := by
  obtain ⟨P, hP⟩ := potential_from_four u hfour
  exact closed_from_potential u P hP
#print axioms solution
