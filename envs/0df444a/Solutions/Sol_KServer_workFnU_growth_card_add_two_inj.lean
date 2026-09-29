-- Prove2me | solution 1 for KServer.workFnU_growth_card_add_two_inj
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T11:08:02.263011+00:00
-- url     : https://prove2.me/submissions/a3a76eb6-6ce9-4a64-bd42-4b04a962de57

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_quasiconvex
import Theorems.Thm_KServer_workFn_rec_le
import Theorems.Thm_KServer_workFn_rec_ge
import Theorems.Thm_KServer_workFn_covered
import Theorems.Thm_KServer_workFn_mono
import Theorems.Thm_KServer_workFn_approx_offlineCost
import Theorems.Thm_KServer_workFn_lipschitz
import Theorems.Thm_KServer_workFn_nonneg
import Theorems.Thm_KServer_mst_cut_property

open KServer

private theorem wfU_le {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (π : Equiv.Perm (Fin k)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) π

private theorem wfU_exists {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : ∃ π : Equiv.Perm (Fin k), workFn C₀ σ (X ∘ π) = workFnU C₀ σ X :=
  exists_eq_ciInf_of_finite

private theorem wfU_self {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : workFnU C₀ σ X ≤ workFn C₀ σ X := by
  simpa using wfU_le C₀ σ X 1

private theorem mc_perm {k : ℕ} {M : Type} [MetricSpace M] (Y Z : Config k M)
    (π : Equiv.Perm (Fin k)) :
    moveCost (Y ∘ (π : Equiv.Perm (Fin k))) (Z ∘ (π : Equiv.Perm (Fin k))) = moveCost Y Z := by
  unfold moveCost
  exact Fintype.sum_equiv π (fun i => dist (Y (π i)) (Z (π i))) (fun j => dist (Y j) (Z j))
    (fun i => rfl)

private theorem sum_perm {k : ℕ} {M : Type} [MetricSpace M] (v : M) (Y : Config k M)
    (π : Equiv.Perm (Fin k)) : ∑ i, dist v (Y (π i)) = ∑ i, dist v (Y i) :=
  Fintype.sum_equiv π (fun i => dist v (Y (π i))) (fun i => dist v (Y i)) (fun i => rfl)

/-- The distance between the endpoints of a walk is at most its length. -/
private theorem dist_telescope {M : Type} [MetricSpace M] (f : ℕ → M) (n : ℕ) :
    dist (f 0) (f n) ≤ ∑ j ∈ Finset.range n, dist (f j) (f (j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have := dist_triangle (f 0) (f n) (f (n + 1))
      linarith

/-- The work function grows at unit rate away from the initial configuration: measured from
any base point, the target's total distance is paid for. -/
private theorem wfU_lower (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (v : M) (X : Config k M) :
    (∑ i, dist v (X i)) - (∑ i, dist v (C₀ i)) ≤ workFnU C₀ σ X := by
  classical
  obtain ⟨π, hπ⟩ := wfU_exists C₀ σ X
  rw [← hπ, ← sum_perm v X π]
  set Y : Config k M := X ∘ (π : Equiv.Perm (Fin k)) with hY
  show (∑ i, dist v (Y i)) - (∑ i, dist v (C₀ i)) ≤ workFn C₀ σ Y
  have hbdd : BddBelow {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
      c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
          + moveCost (S σ.length) Y} := by
    refine ⟨0, ?_⟩
    rintro c ⟨S, -, rfl⟩
    have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => dist_nonneg
    have h2 : (0:ℝ) ≤ moveCost (S σ.length) Y := Finset.sum_nonneg fun i _ => dist_nonneg
    linarith
  have hne : {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
      c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
          + moveCost (S σ.length) Y}.Nonempty := by
    have hk0 : (0 : ℕ) < k := hk
    refine ⟨_, ⟨fun j => if j = 0 then C₀ else fun _ => σ.getD (j - 1) (C₀ ⟨0, hk0⟩),
      ⟨by simp, ?_⟩, rfl⟩⟩
    intro j
    refine ⟨⟨0, hk0⟩, ?_⟩
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [List.getD_eq_getElem σ _ j.2]
    simp
  refine le_csInf hne ?_
  rintro c ⟨S, hS, rfl⟩
  have hcost : ∑ i, dist (C₀ i) (S σ.length i)
      ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) := by
    have hswap : ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))
        = ∑ i, ∑ j ∈ Finset.range σ.length, dist (S j i) (S (j + 1) i) := by
      unfold moveCost
      exact Finset.sum_comm
    rw [hswap]
    refine Finset.sum_le_sum fun i _ => ?_
    have := dist_telescope (fun j => S j i) σ.length
    rw [hS.1] at this
    exact this
  have hfin : ∑ i, dist (C₀ i) (Y i)
      ≤ (∑ i, dist (C₀ i) (S σ.length i)) + moveCost (S σ.length) Y := by
    unfold moveCost
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _
  have hbase : (∑ i, dist v (Y i)) - (∑ i, dist v (C₀ i)) ≤ ∑ i, dist (C₀ i) (Y i) := by
    have : ∀ i : Fin k, dist v (Y i) - dist v (C₀ i) ≤ dist (C₀ i) (Y i) := by
      intro i
      have := dist_triangle v (C₀ i) (Y i)
      linarith
    calc (∑ i, dist v (Y i)) - (∑ i, dist v (C₀ i))
        = ∑ i, (dist v (Y i) - dist v (C₀ i)) := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i, dist (C₀ i) (Y i) := Finset.sum_le_sum fun i _ => this i
  linarith

private theorem update_comp {k : ℕ} {M : Type} (X : Config k M) (i : Fin k) (r : M)
    (π : Equiv.Perm (Fin k)) :
    (Function.update X i r) ∘ (π : Equiv.Perm (Fin k))
      = Function.update (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i) r := by
  classical
  funext l
  by_cases h : l = π.symm i
  · subst h
    rw [Function.comp_apply, Equiv.apply_symm_apply, Function.update_self,
      Function.update_self]
  · have h2 : (π : Equiv.Perm (Fin k)) l ≠ i := by
      intro hc; exact h (by rw [← hc]; simp)
    simp [Function.update_of_ne h, Function.update_of_ne h2]

private theorem wfU_rec_le (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (i : Fin k) :
    workFnU C₀ (σ ++ [r]) X ≤ workFnU C₀ σ (Function.update X i r) + dist r (X i) := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ σ (Function.update X i r)
  have h1 := wfU_le C₀ (σ ++ [r]) X π
  have h2 := workFn_rec_le k hk M C₀ σ r (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i)
  rw [← update_comp X i r π] at h2
  have h3 : (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i) = X i := by simp
  rw [h3, hπ] at h2
  linarith

private theorem wfU_rec_ge (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    ∃ i : Fin k, workFnU C₀ σ (Function.update X i r) + dist r (X i)
      ≤ workFnU C₀ (σ ++ [r]) X := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ (σ ++ [r]) X
  obtain ⟨i', hi'⟩ := workFn_rec_ge k hk M C₀ σ r (X ∘ (π : Equiv.Perm (Fin k)))
  refine ⟨π i', ?_⟩
  have hup : Function.update (X ∘ (π : Equiv.Perm (Fin k))) i' r
      = (Function.update X (π i') r) ∘ (π : Equiv.Perm (Fin k)) := by
    rw [update_comp X (π i') r π]; simp
  rw [hup] at hi'
  have h1 := wfU_le C₀ σ (Function.update X (π i') r) π
  have h2 : (X ∘ (π : Equiv.Perm (Fin k))) i' = X (π i') := rfl
  rw [h2, hπ] at hi'
  linarith

private theorem wfU_covered (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (hX : ∃ i, X i = r) :
    workFnU C₀ (σ ++ [r]) X = workFnU C₀ σ X := by
  unfold workFnU
  refine iInf_congr fun π => ?_
  refine workFn_covered k hk M C₀ σ r (X ∘ π) ?_
  obtain ⟨i, hi⟩ := hX
  exact ⟨π.symm i, by simpa using hi⟩

private theorem wfU_mono (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    workFnU C₀ σ X ≤ workFnU C₀ (σ ++ [r]) X := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ (σ ++ [r]) X
  rw [← hπ]
  exact le_trans (wfU_le C₀ σ X π) (workFn_mono k hk M C₀ σ r (X ∘ π))

/-- One step of the recurrence, expressed purely in the new work function. -/
private theorem wfU_step_self (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (U : Config k M) :
    ∃ i : Fin k, workFnU C₀ (σ ++ [r]) U
      = workFnU C₀ (σ ++ [r]) (Function.update U i r) + dist r (U i) := by
  classical
  obtain ⟨i, hi⟩ := wfU_rec_ge k hk M C₀ σ r U
  refine ⟨i, le_antisymm ?_ ?_⟩
  · have hcov : ∃ l, (Function.update U i r) l = r := ⟨i, Function.update_self _ _ _⟩
    have hc := wfU_covered k hk M C₀ σ r (Function.update U i r) hcov
    have := wfU_rec_le k hk M C₀ σ r U i
    rw [← hc] at this
    exact this
  · have hcov : ∃ l, (Function.update U i r) l = r := ⟨i, Function.update_self _ _ _⟩
    have hc := wfU_covered k hk M C₀ σ r (Function.update U i r) hcov
    rw [hc]
    exact hi

private theorem sum_diff_single {k : ℕ} (F G : Fin k → ℝ) (p : Fin k)
    (h : ∀ i, i ≠ p → F i = G i) : ∑ i, F i - ∑ i, G i = F p - G p := by
  classical
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ p),
    ← Finset.add_sum_erase _ G (Finset.mem_univ p),
    Finset.sum_congr rfl (fun i hi => h i (Finset.ne_of_mem_erase hi))]
  ring

/-- The approximate duality property: an `ε`-minimiser of `w - d(r^k, ·)` is an
`ε`-minimiser for the new work function and an `ε`-maximiser of the increment. -/
private theorem wfU_duality_approx (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (A : Config k M) (ε : ℝ)
    (hA : ∀ X : Config k M, workFnU C₀ σ A - ∑ i, dist r (A i)
      ≤ workFnU C₀ σ X - ∑ i, dist r (X i) + ε) :
    (∀ X : Config k M, workFnU C₀ (σ ++ [r]) A - ∑ i, dist r (A i)
        ≤ workFnU C₀ (σ ++ [r]) X - ∑ i, dist r (X i) + ε) ∧
    (∀ X : Config k M, workFnU C₀ (σ ++ [r]) X - workFnU C₀ σ X
        ≤ workFnU C₀ (σ ++ [r]) A - workFnU C₀ σ A + ε) := by
  classical
  set D : Config k M → ℝ := fun V => ∑ i, dist r (V i) with hDdef
  set g : Config k M → ℝ := fun V => workFnU C₀ σ V - D V with hgdef
  have hgA : ∀ X : Config k M, g A ≤ g X + ε := hA
  have hDupd : ∀ (V : Config k M) (m : Fin k) (u : M),
      D (Function.update V m u) = D V - dist r (V m) + dist r u := by
    intro V m u
    have h := sum_diff_single (fun i => dist r (Function.update V m u i))
      (fun i => dist r (V i)) m (fun i hi => by
        show dist r (Function.update V m u i) = dist r (V i)
        rw [Function.update_of_ne hi])
    simp only [Function.update_self] at h
    rw [hDdef]
    linarith
  have hDperm : ∀ (V : Config k M) (π : Equiv.Perm (Fin k)),
      D (V ∘ (π : Equiv.Perm (Fin k))) = D V := by
    intro V π
    rw [hDdef]
    exact Fintype.sum_equiv π (fun i => dist r (V (π i))) (fun i => dist r (V i))
      (fun i => rfl)
  have hup : ∀ (V : Config k M) (l : Fin k),
      workFnU C₀ (σ ++ [r]) V - D V ≤ g (Function.update V l r) := by
    intro V l
    have h := wfU_rec_le k hk M C₀ σ r V l
    have hd := hDupd V l r
    rw [hgdef]; simp only []; rw [hd]
    simp only [dist_self, add_zero]
    linarith
  have hlow : ∀ V : Config k M, ∃ l : Fin k,
      g (Function.update V l r) ≤ workFnU C₀ (σ ++ [r]) V - D V := by
    intro V
    obtain ⟨l, hl⟩ := wfU_rec_ge k hk M C₀ σ r V
    refine ⟨l, ?_⟩
    have hd := hDupd V l r
    rw [hgdef]; simp only []; rw [hd]
    simp only [dist_self, add_zero]
    linarith
  have hkey : ∀ (P Q : Config k M) (m : Fin k), Q m = r →
      ∃ l : Fin k, g (Function.update P l r) + g A ≤ g Q + g P + ε := by
    intro P Q m hQm
    obtain ⟨π, hπ⟩ := workFnU_quasiconvex k hk M C₀ σ Q P
    refine ⟨π m, ?_⟩
    set s : Finset (Fin k) := Finset.univ.erase m with hsdef
    have hmem : ∀ l : Fin k, (l ∈ s) ↔ l ≠ m := by
      intro l; rw [hsdef]; simp [Finset.mem_erase]
    have hZ : (fun l => if l ∈ s then Q l else P (π l))
        = Function.update Q m (P (π m)) := by
      funext l
      show (if l ∈ s then Q l else P (π l)) = Function.update Q m (P (π m)) l
      by_cases hl : l = m
      · rw [hl, if_neg (by simp [hmem]), Function.update_self]
      · rw [if_pos ((hmem l).mpr hl), Function.update_of_ne hl]
    have hW : (fun l => if l ∈ s then P (π l) else Q l)
        = (Function.update P (π m) r) ∘ (π : Equiv.Perm (Fin k)) := by
      funext l
      show (if l ∈ s then P (π l) else Q l) = Function.update P (π m) r (π l)
      by_cases hl : l = m
      · rw [hl, if_neg (by simp [hmem]), Function.update_self, hQm]
      · have hne : (π : Equiv.Perm (Fin k)) l ≠ π m := fun hc => hl (π.injective hc)
        rw [if_pos ((hmem l).mpr hl), Function.update_of_ne hne]
    have hq := hπ s
    rw [hZ, hW, workFnU_perm k M C₀ σ (Function.update P (π m) r) π] at hq
    have hDZ := hDupd Q m (P (π m))
    have hDW := hDupd P (π m) r
    have hgZ := hgA (Function.update Q m (P (π m)))
    rw [hgdef] at hgZ ⊢
    simp only [] at hgZ ⊢
    rw [hDZ, hDW, hQm] at *
    simp only [dist_self, sub_zero, add_zero] at *
    linarith
  constructor
  · intro X
    obtain ⟨l₀, hl₀⟩ := hlow X
    obtain ⟨l, hl⟩ := hkey A (Function.update X l₀ r) l₀ (Function.update_self _ _ _)
    have h1 := hup A l
    simp only [hgdef, hDdef] at hl h1 hl₀
    linarith
  · intro X
    obtain ⟨m₀, hm₀⟩ := hlow A
    obtain ⟨l, hl⟩ := hkey X (Function.update A m₀ r) m₀ (Function.update_self _ _ _)
    have h1 := hup X l
    simp only [hgdef, hDdef] at hl h1 hm₀
    linarith


/-! ### Configurations with a prescribed range -/

/-- Two injective configurations with the same range differ by a permutation, so the
unordered work function does not distinguish them. -/
private theorem wfU_range {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X Y : Config k M) (hX : Function.Injective X) (hY : Function.Injective Y)
    (h : Set.range X = Set.range Y) : workFnU C₀ σ X = workFnU C₀ σ Y := by
  have hmem : ∀ i, ∃ j, X j = Y i := by
    intro i
    have hi : Y i ∈ Set.range X := by rw [h]; exact ⟨i, rfl⟩
    exact hi
  choose f hf using hmem
  have hinj : Function.Injective f := by
    intro i j hij
    exact hY (by rw [← hf i, ← hf j, hij])
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hinj
  have hcomp : Y = X ∘ (Equiv.ofBijective f hbij) := by
    funext i
    exact (hf i).symm
  rw [hcomp]
  exact (workFnU_perm k M C₀ σ X (Equiv.ofBijective f hbij)).symm

/-- The unordered work function is `1`-Lipschitz for the labelled movement cost. -/
private theorem wfU_lip (k : ℕ) (hk : 1 ≤ k) {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X Y : Config k M) :
    workFnU C₀ σ X ≤ workFnU C₀ σ Y + moveCost Y X := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ σ Y
  have h1 : workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ (π : Equiv.Perm (Fin k))) := wfU_le C₀ σ X π
  have h2 := workFn_lipschitz k hk M C₀ σ (X ∘ (π : Equiv.Perm (Fin k)))
    (Y ∘ (π : Equiv.Perm (Fin k)))
  rw [mc_perm Y X π] at h2
  rw [← hπ]
  linarith

/-! ### The complement of a pair of points on a space with `k + 2` points -/

private theorem card_avoid {k : ℕ} {M : Type} [Fintype M] [DecidableEq M]
    (hM : Fintype.card M = k + 2) (u v : M) (huv : u ≠ v) :
    ((Finset.univ.erase u).erase v).card = k := by
  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm huv, Finset.mem_univ v⟩),
    Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, hM]
  omega

private theorem exists_avoid {k : ℕ} {M : Type} [Fintype M] [DecidableEq M]
    (hM : Fintype.card M = k + 2) (u v : M) (huv : u ≠ v) :
    ∃ X : Config k M, Function.Injective X ∧ (∀ i, X i ≠ u) ∧ (∀ i, X i ≠ v) := by
  classical
  have hc : Fintype.card {x : M // x ≠ u ∧ x ≠ v} = k := by
    rw [Fintype.card_subtype]
    have hset : (Finset.univ.filter (fun x : M => x ≠ u ∧ x ≠ v))
        = (Finset.univ.erase u).erase v := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      tauto
    rw [hset, card_avoid hM u v huv]
  set e := Fintype.equivFinOfCardEq hc with he
  refine ⟨fun i => ((e.symm i : {x : M // x ≠ u ∧ x ≠ v}) : M), ?_, ?_, ?_⟩
  · intro a b hab
    exact e.symm.injective (Subtype.ext hab)
  · intro i; exact (e.symm i).2.1
  · intro i; exact (e.symm i).2.2

/-- On a space with `k + 2` points an injective configuration avoiding two distinct points
occupies exactly the complement of those points. -/
private theorem image_avoid {k : ℕ} {M : Type} [Fintype M] [DecidableEq M]
    (hM : Fintype.card M = k + 2) (u v : M) (huv : u ≠ v)
    (X : Config k M) (hX : Function.Injective X) (hu : ∀ i, X i ≠ u) (hv : ∀ i, X i ≠ v) :
    Finset.univ.image X = (Finset.univ.erase u).erase v := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_erase.mpr ⟨hv i, Finset.mem_erase.mpr ⟨hu i, Finset.mem_univ _⟩⟩
  · rw [Finset.card_image_of_injective _ hX, Finset.card_univ, Fintype.card_fin,
      card_avoid hM u v huv]

private theorem range_avoid_eq {k : ℕ} {M : Type} [Fintype M] [DecidableEq M]
    (hM : Fintype.card M = k + 2) (u v : M) (huv : u ≠ v)
    (X Y : Config k M) (hX : Function.Injective X) (hXu : ∀ i, X i ≠ u) (hXv : ∀ i, X i ≠ v)
    (hY : Function.Injective Y) (hYu : ∀ i, Y i ≠ u) (hYv : ∀ i, Y i ≠ v) :
    Set.range X = Set.range Y := by
  have h1 := image_avoid hM u v huv X hX hXu hXv
  have h2 := image_avoid hM u v huv Y hY hYu hYv
  have h3 : Finset.univ.image X = Finset.univ.image Y := by rw [h1, h2]
  have h4 : ((Finset.univ.image X : Finset M) : Set M)
      = ((Finset.univ.image Y : Finset M) : Set M) := by rw [h3]
  simpa [Finset.coe_image, Set.image_univ] using h4

/-- All injective configurations avoiding the same two distinct points have the same
unordered work function value. -/
private theorem wfU_avoid_eq {k : ℕ} {M : Type} [MetricSpace M] [Fintype M] [DecidableEq M]
    (hM : Fintype.card M = k + 2) (C₀ : Config k M) (σ : List M) (u v : M) (huv : u ≠ v)
    (X Y : Config k M) (hX : Function.Injective X) (hXu : ∀ i, X i ≠ u) (hXv : ∀ i, X i ≠ v)
    (hY : Function.Injective Y) (hYu : ∀ i, Y i ≠ u) (hYv : ∀ i, Y i ≠ v) :
    workFnU C₀ σ X = workFnU C₀ σ Y :=
  wfU_range C₀ σ X Y hX hY (range_avoid_eq hM u v huv X Y hX hXu hXv hY hYu hYv)

/-! ### The edge weight and its recurrence -/

/-- `cm u v` is a configuration occupying the complement of `{u, v}`. -/
private def IsCmpl {k : ℕ} {M : Type} (cm : M → M → Config k M) : Prop :=
  ∀ u v : M, u ≠ v →
    Function.Injective (cm u v) ∧ (∀ i, cm u v i ≠ u) ∧ (∀ i, cm u v i ≠ v)

private theorem exists_cmpl (k : ℕ) {M : Type} [Fintype M] [DecidableEq M]
    (hM : Fintype.card M = k + 2) : ∃ cm : M → M → Config k M, IsCmpl cm := by
  classical
  have hne : Nonempty M := by
    rw [← Fintype.card_pos_iff, hM]; omega
  have key : ∀ u v : M, u ≠ v →
      ∃ X : Config k M, Function.Injective X ∧ (∀ i, X i ≠ u) ∧ (∀ i, X i ≠ v) :=
    fun u v h => exists_avoid hM u v h
  choose! cm h1 h2 h3 using key
  exact ⟨cm, fun u v h => ⟨h1 u v h, h2 u v h, h3 u v h⟩⟩

/-- Every point other than `u` and `v` is occupied by `cm u v`. -/
private theorem cmpl_covers {k : ℕ} {M : Type} [Fintype M] [DecidableEq M]
    (hM : Fintype.card M = k + 2) (cm : M → M → Config k M) (hcm : IsCmpl cm)
    (u v : M) (huv : u ≠ v) (x : M) (hxu : x ≠ u) (hxv : x ≠ v) : ∃ i, cm u v i = x := by
  obtain ⟨hi, hu, hv⟩ := hcm u v huv
  have himg := image_avoid hM u v huv (cm u v) hi hu hv
  have hx : x ∈ (Finset.univ.erase u).erase v :=
    Finset.mem_erase.mpr ⟨hxv, Finset.mem_erase.mpr ⟨hxu, Finset.mem_univ _⟩⟩
  rw [← himg] at hx
  obtain ⟨i, -, hix⟩ := Finset.mem_image.mp hx
  exact ⟨i, hix⟩

/-- Identifying an arbitrary injective configuration avoiding `u` and `v` with `cm u v`. -/
private theorem wt_of_avoid {k : ℕ} {M : Type} [MetricSpace M] [Fintype M] [DecidableEq M]
    (hM : Fintype.card M = k + 2) (cm : M → M → Config k M) (hcm : IsCmpl cm)
    (C₀ : Config k M) (σ : List M) (u v : M) (huv : u ≠ v)
    (X : Config k M) (hX : Function.Injective X) (hXu : ∀ i, X i ≠ u) (hXv : ∀ i, X i ≠ v) :
    workFnU C₀ σ X = workFnU C₀ σ (cm u v) := by
  obtain ⟨hi, hu, hv⟩ := hcm u v huv
  exact wfU_avoid_eq hM C₀ σ u v huv X (cm u v) hX hXu hXv hi hu hv

private theorem wt_symm {k : ℕ} {M : Type} [MetricSpace M] [Fintype M] [DecidableEq M]
    (hM : Fintype.card M = k + 2) (cm : M → M → Config k M) (hcm : IsCmpl cm)
    (C₀ : Config k M) (σ : List M) (u v : M) (huv : u ≠ v) :
    workFnU C₀ σ (cm v u) = workFnU C₀ σ (cm u v) := by
  obtain ⟨hi, hv, hu⟩ := hcm v u (Ne.symm huv)
  exact wt_of_avoid hM cm hcm C₀ σ u v huv (cm v u) hi hu hv

/-- An edge not containing the new request keeps its weight. -/
private theorem wt_fix (k : ℕ) (hk : 1 ≤ k) {M : Type} [MetricSpace M] [Fintype M]
    [DecidableEq M] (hM : Fintype.card M = k + 2) (cm : M → M → Config k M)
    (hcm : IsCmpl cm) (C₀ : Config k M) (σ : List M) (r u v : M) (huv : u ≠ v)
    (hru : r ≠ u) (hrv : r ≠ v) :
    workFnU C₀ (σ ++ [r]) (cm u v) = workFnU C₀ σ (cm u v) :=
  wfU_covered k hk M C₀ σ r (cm u v) (cmpl_covers hM cm hcm u v huv r hru hrv)

/-- One direction of the edge recurrence. -/
private theorem wt_rec_le (k : ℕ) (hk : 1 ≤ k) {M : Type} [MetricSpace M] [Fintype M]
    [DecidableEq M] (hM : Fintype.card M = k + 2) (cm : M → M → Config k M)
    (hcm : IsCmpl cm) (C₀ : Config k M) (σ : List M) (r a c : M) (hra : r ≠ a)
    (hcr : c ≠ r) (hca : c ≠ a) :
    workFnU C₀ (σ ++ [r]) (cm r a) ≤ workFnU C₀ σ (cm a c) + dist r c := by
  obtain ⟨hi, hr, ha⟩ := hcm r a hra
  obtain ⟨i, hic⟩ := cmpl_covers hM cm hcm r a hra c hcr hca
  have hupd : Function.Injective (Function.update (cm r a) i r) := by
    intro p q hpq
    by_cases hp : p = i <;> by_cases hq : q = i
    · rw [hp, hq]
    · rw [hp, Function.update_self, Function.update_of_ne hq] at hpq
      exact absurd hpq.symm (hr q)
    · rw [hq, Function.update_self, Function.update_of_ne hp] at hpq
      exact absurd hpq (hr p)
    · rw [Function.update_of_ne hp, Function.update_of_ne hq] at hpq
      exact hi hpq
  have hupa : ∀ j, Function.update (cm r a) i r j ≠ a := by
    intro j
    by_cases hj : j = i
    · rw [hj, Function.update_self]; exact hra
    · rw [Function.update_of_ne hj]; exact ha j
  have hupc : ∀ j, Function.update (cm r a) i r j ≠ c := by
    intro j
    by_cases hj : j = i
    · rw [hj, Function.update_self]; exact Ne.symm hcr
    · rw [Function.update_of_ne hj]
      intro hcon
      exact hj (hi (by rw [hcon, hic]))
  have heq : workFnU C₀ σ (Function.update (cm r a) i r) = workFnU C₀ σ (cm a c) :=
    wt_of_avoid hM cm hcm C₀ σ a c (Ne.symm hca) _ hupd hupa hupc
  have h := wfU_rec_le k hk M C₀ σ r (cm r a) i
  rw [heq, hic] at h
  exact h

/-- The other direction of the edge recurrence. -/
private theorem wt_rec_ge (k : ℕ) (hk : 1 ≤ k) {M : Type} [MetricSpace M] [Fintype M]
    [DecidableEq M] (hM : Fintype.card M = k + 2) (cm : M → M → Config k M)
    (hcm : IsCmpl cm) (C₀ : Config k M) (σ : List M) (r a : M) (hra : r ≠ a) :
    ∃ c : M, c ≠ r ∧ c ≠ a ∧
      workFnU C₀ σ (cm a c) + dist r c ≤ workFnU C₀ (σ ++ [r]) (cm r a) := by
  obtain ⟨hi, hr, ha⟩ := hcm r a hra
  obtain ⟨i, hi'⟩ := wfU_rec_ge k hk M C₀ σ r (cm r a)
  refine ⟨cm r a i, hr i, ha i, ?_⟩
  have hupd : Function.Injective (Function.update (cm r a) i r) := by
    intro p q hpq
    by_cases hp : p = i <;> by_cases hq : q = i
    · rw [hp, hq]
    · rw [hp, Function.update_self, Function.update_of_ne hq] at hpq
      exact absurd hpq.symm (hr q)
    · rw [hq, Function.update_self, Function.update_of_ne hp] at hpq
      exact absurd hpq (hr p)
    · rw [Function.update_of_ne hp, Function.update_of_ne hq] at hpq
      exact hi hpq
  have hupa : ∀ j, Function.update (cm r a) i r j ≠ a := by
    intro j
    by_cases hj : j = i
    · rw [hj, Function.update_self]; exact hra
    · rw [Function.update_of_ne hj]; exact ha j
  have hupc : ∀ j, Function.update (cm r a) i r j ≠ cm r a i := by
    intro j
    by_cases hj : j = i
    · rw [hj, Function.update_self]; exact Ne.symm (hr i)
    · rw [Function.update_of_ne hj]
      intro hcon
      exact hj (hi hcon)
  have hac : a ≠ cm r a i := Ne.symm (ha i)
  have heq : workFnU C₀ σ (Function.update (cm r a) i r) = workFnU C₀ σ (cm a (cm r a i)) :=
    wt_of_avoid hM cm hcm C₀ σ a (cm r a i) hac _ hupd hupa hupc
  rw [heq] at hi'
  exact hi'

/-! ### Choosing a hybrid that stays injective -/

/-- Given two injective configurations `Q` and `P'` such that `r` and `b` are occupied by
`Q` but not by `P'`, the quasiconvexity hybrids can be chosen injective, with `r` missing
from the first and `b` missing from the second, and with every point occupied by both `Q`
and `P'` occupied by both hybrids. The set `s` is the reachability set of the index of `r`
under the relation "the point I contribute from `P'` is the point `Q` contributes here". -/
private theorem hybrid_exists {k : ℕ} {M : Type} [DecidableEq M]
    (Q P' : Config k M) (hQ : Function.Injective Q) (hP : Function.Injective P')
    (r b : M) (l₀ lb : Fin k) (hl₀ : Q l₀ = r) (hlb : Q lb = b) (hrb : r ≠ b)
    (hrP : ∀ i, P' i ≠ r) (hbP : ∀ i, P' i ≠ b) :
    ∃ s : Finset (Fin k),
      Function.Injective (fun i => if i ∈ s then Q i else P' i) ∧
      Function.Injective (fun i => if i ∈ s then P' i else Q i) ∧
      (∀ i, (if i ∈ s then Q i else P' i) ≠ r) ∧
      (∀ i, (if i ∈ s then P' i else Q i) ≠ b) ∧
      (∀ (x : M) (p q : Fin k), Q p = x → P' q = x →
        (∃ i, (if i ∈ s then Q i else P' i) = x) ∧
        (∃ i, (if i ∈ s then P' i else Q i) = x)) ∧
      (∀ (x : M) (q : Fin k), P' q = x → (∀ i, Q i ≠ x) →
        (((∃ i, (if i ∈ s then Q i else P' i) = x) ↔ q ∉ s) ∧
         ((∃ i, (if i ∈ s then P' i else Q i) = x) ↔ q ∈ s))) := by
  classical
  set O : Set (Fin k) := {l | Relation.ReflTransGen (fun l l' => Q l' = P' l) l₀ l} with hO
  set s : Finset (Fin k) := Finset.univ.filter (fun l => l ∉ O) with hs
  have hmem : ∀ l, l ∈ s ↔ l ∉ O := by
    intro l; rw [hs]; simp
  have hmemO : ∀ l, l ∉ s ↔ l ∈ O := by
    intro l; rw [hmem l]; exact not_not
  have hl0O : l₀ ∈ O := Relation.ReflTransGen.refl
  have hclosed : ∀ l l' : Fin k, l ∈ O → Q l' = P' l → l' ∈ O := fun l l' hl h =>
    Relation.ReflTransGen.tail hl h
  have hpred : ∀ l : Fin k, l ∈ O → l ≠ l₀ → ∃ l'', l'' ∈ O ∧ Q l = P' l'' := by
    intro l hl hne
    rcases Relation.ReflTransGen.cases_tail hl with h | ⟨c, hc1, hc2⟩
    · exact absurd h hne
    · exact ⟨c, hc1, hc2⟩
  have hlbs : lb ∈ s := by
    rw [hmem]
    intro hcon
    by_cases h : lb = l₀
    · exact hrb (by rw [← hl₀, ← h, hlb])
    · obtain ⟨l'', -, hl''⟩ := hpred lb hcon h
      exact hbP l'' (by rw [← hl'', hlb])
  refine ⟨s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q hpq
    dsimp only at hpq
    by_cases hp : p ∈ s <;> by_cases hq : q ∈ s
    · rw [if_pos hp, if_pos hq] at hpq; exact hQ hpq
    · rw [if_pos hp, if_neg hq] at hpq
      exact absurd (hclosed q p ((hmemO q).mp hq) hpq) ((hmem p).mp hp)
    · rw [if_neg hp, if_pos hq] at hpq
      exact absurd (hclosed p q ((hmemO p).mp hp) hpq.symm) ((hmem q).mp hq)
    · rw [if_neg hp, if_neg hq] at hpq; exact hP hpq
  · intro p q hpq
    dsimp only at hpq
    by_cases hp : p ∈ s <;> by_cases hq : q ∈ s
    · rw [if_pos hp, if_pos hq] at hpq; exact hP hpq
    · rw [if_pos hp, if_neg hq] at hpq
      exfalso
      by_cases hq0 : q = l₀
      · exact hrP p (by rw [hpq, hq0, hl₀])
      · obtain ⟨l'', hl''O, hl''⟩ := hpred q ((hmemO q).mp hq) hq0
        exact ((hmem p).mp hp) (by rw [hP (hpq.trans hl'')]; exact hl''O)
    · rw [if_neg hp, if_pos hq] at hpq
      exfalso
      by_cases hp0 : p = l₀
      · exact hrP q (by rw [← hpq, hp0, hl₀])
      · obtain ⟨l'', hl''O, hl''⟩ := hpred p ((hmemO p).mp hp) hp0
        exact ((hmem q).mp hq) (by rw [hP (hpq.symm.trans hl'')]; exact hl''O)
    · rw [if_neg hp, if_neg hq] at hpq; exact hQ hpq
  · intro i h
    by_cases hi : i ∈ s
    · rw [if_pos hi] at h
      exact ((hmem i).mp hi) ((hQ (h.trans hl₀.symm) : i = l₀) ▸ hl0O)
    · rw [if_neg hi] at h; exact hrP i h
  · intro i h
    by_cases hi : i ∈ s
    · rw [if_pos hi] at h; exact hbP i h
    · rw [if_neg hi] at h
      exact hi ((hQ (h.trans hlb.symm) : i = lb) ▸ hlbs)
  · intro x p q hp hq
    have hxr : x ≠ r := by rw [← hq]; exact hrP q
    constructor
    · by_cases h : p ∈ s
      · exact ⟨p, by rw [if_pos h, hp]⟩
      · refine ⟨q, ?_⟩
        have hqs : q ∉ s := by
          intro hqs
          have hpO : p ∈ O := (hmemO p).mp h
          have hp0 : p ≠ l₀ := by
            intro hc; exact hxr (by rw [← hp, hc, hl₀])
          obtain ⟨l'', hl''O, hl''⟩ := hpred p hpO hp0
          have : l'' = q := hP (by rw [← hl'', hp, ← hq])
          exact ((hmem q).mp hqs) (this ▸ hl''O)
        rw [if_neg hqs, hq]
    · by_cases h : q ∈ s
      · exact ⟨q, by rw [if_pos h, hq]⟩
      · refine ⟨p, ?_⟩
        have hps : p ∉ s := by
          intro hps
          have hqO : q ∈ O := (hmemO q).mp h
          exact ((hmem p).mp hps) (hclosed q p hqO (by rw [hp, ← hq]))
        rw [if_neg hps, hp]
  · intro x q hq hnQ
    constructor
    · constructor
      · rintro ⟨i, hi⟩
        by_cases h : i ∈ s
        · rw [if_pos h] at hi; exact absurd hi (hnQ i)
        · rw [if_neg h] at hi
          have : i = q := hP (by rw [hi, hq])
          exact this ▸ h
      · intro h
        exact ⟨q, by rw [if_neg h, hq]⟩
    · constructor
      · rintro ⟨i, hi⟩
        by_cases h : i ∈ s
        · rw [if_pos h] at hi
          have : i = q := hP (by rw [hi, hq])
          exact this ▸ h
        · rw [if_neg h] at hi; exact absurd hi (hnQ i)
      · intro h
        exact ⟨q, by rw [if_pos h, hq]⟩

/-! ### The exchange inequality for edges -/

private theorem card_erase3 {k : ℕ} {M : Type} [Fintype M] [DecidableEq M]
    (hM : Fintype.card M = k + 2) (r a c : M) (hra : r ≠ a) (hrc : r ≠ c) (hac : a ≠ c) :
    (((Finset.univ.erase r).erase a).erase c).card = k - 1 := by
  have h1 : a ∈ Finset.univ.erase r := Finset.mem_erase.mpr ⟨Ne.symm hra, Finset.mem_univ a⟩
  have h2 : c ∈ (Finset.univ.erase r).erase a :=
    Finset.mem_erase.mpr ⟨Ne.symm hac, Finset.mem_erase.mpr ⟨Ne.symm hrc, Finset.mem_univ c⟩⟩
  rw [Finset.card_erase_of_mem h2, Finset.card_erase_of_mem h1,
    Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, hM]
  omega

/-- **Quasiconvexity in edge form.** For four distinct points, one of the two rewirings of
the pair of edges `{r,b}`, `{a,c}` does not increase the total work-function value. -/
private theorem edge_exchange (k : ℕ) (hk : 1 ≤ k) {M : Type} [MetricSpace M] [Fintype M]
    [DecidableEq M] (hM : Fintype.card M = k + 2) (cm : M → M → Config k M)
    (hcm : IsCmpl cm) (C₀ : Config k M) (σ : List M) (r b a c : M)
    (hrb : r ≠ b) (hra : r ≠ a) (hrc : r ≠ c) (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) :
    workFnU C₀ σ (cm r a) + workFnU C₀ σ (cm b c)
        ≤ workFnU C₀ σ (cm r b) + workFnU C₀ σ (cm a c)
      ∨ workFnU C₀ σ (cm r c) + workFnU C₀ σ (cm b a)
        ≤ workFnU C₀ σ (cm r b) + workFnU C₀ σ (cm a c) := by
  classical
  obtain ⟨hQinj, hQa, hQc⟩ := hcm a c hac
  obtain ⟨hPinj, hPr, hPb⟩ := hcm r b hrb
  obtain ⟨π, hπ⟩ := workFnU_quasiconvex k hk M C₀ σ (cm a c) (cm r b)
  obtain ⟨l₀, hl₀⟩ := cmpl_covers hM cm hcm a c hac r hra hrc
  obtain ⟨lb, hlb⟩ := cmpl_covers hM cm hcm a c hac b hba hbc
  have hP'inj : Function.Injective (fun i => cm r b (π i)) :=
    fun p q h => π.injective (hPinj h)
  obtain ⟨s, hZinj, hWinj, hZr, hWb, hboth, hsplit⟩ :=
    hybrid_exists (cm a c) (fun i => cm r b (π i)) hQinj hP'inj r b l₀ lb hl₀ hlb hrb
      (fun i => hPr (π i)) (fun i => hPb (π i))
  set Z : Config k M := fun i => if i ∈ s then cm a c i else cm r b (π i) with hZdef
  set W : Config k M := fun i => if i ∈ s then cm r b (π i) else cm a c i with hWdef
  have hkey := hπ s
  rw [← hZdef, ← hWdef] at hkey
  -- `b` is occupied by `Z`, `r` by `W`
  have hZb : ∃ i, Z i = b := by
    by_cases h : lb ∈ s
    · exact ⟨lb, by rw [hZdef]; dsimp only; rw [if_pos h, hlb]⟩
    · exact absurd (by rw [hWdef]; dsimp only; rw [if_neg h, hlb] : W lb = b) (hWb lb)
  -- every point other than `r, b, a, c` is occupied by both hybrids
  have hcommon : ∀ x : M, x ≠ r → x ≠ b → x ≠ a → x ≠ c →
      (∃ i, Z i = x) ∧ (∃ i, W i = x) := by
    intro x hxr hxb hxa hxc
    obtain ⟨p, hp⟩ := cmpl_covers hM cm hcm a c hac x hxa hxc
    obtain ⟨q, hq⟩ := cmpl_covers hM cm hcm r b hrb x hxr hxb
    exact hboth x p (π.symm q) hp (by simp [hq])
  -- exactly one of `a`, `c` is occupied by `Z`
  have hZcard : (Finset.univ.image Z).card = k := by
    rw [Finset.card_image_of_injective _ hZinj, Finset.card_univ, Fintype.card_fin]
  have hnotboth : ¬((∃ i, Z i = a) ∧ (∃ i, Z i = c)) := by
    rintro ⟨ha', hc'⟩
    have hsub : Finset.univ.erase r ⊆ Finset.univ.image Z := by
      intro x hx
      have hxr : x ≠ r := (Finset.mem_erase.mp hx).1
      refine Finset.mem_image.mpr ?_
      by_cases hxa : x = a
      · obtain ⟨i, hi⟩ := ha'; exact ⟨i, Finset.mem_univ i, by rw [hi, hxa]⟩
      by_cases hxc : x = c
      · obtain ⟨i, hi⟩ := hc'; exact ⟨i, Finset.mem_univ i, by rw [hi, hxc]⟩
      by_cases hxb : x = b
      · obtain ⟨i, hi⟩ := hZb; exact ⟨i, Finset.mem_univ i, by rw [hi, hxb]⟩
      · obtain ⟨i, hi⟩ := (hcommon x hxr hxb hxa hxc).1
        exact ⟨i, Finset.mem_univ i, hi⟩
    have hc1 : (Finset.univ.erase r).card = k + 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, hM]
      omega
    have := Finset.card_le_card hsub
    rw [hc1, hZcard] at this
    omega
  have hnotneither : ¬((∀ i, Z i ≠ a) ∧ (∀ i, Z i ≠ c)) := by
    rintro ⟨ha', hc'⟩
    have hsub : Finset.univ.image Z ⊆ ((Finset.univ.erase r).erase a).erase c := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_erase.mpr ⟨hc' i, Finset.mem_erase.mpr ⟨ha' i,
        Finset.mem_erase.mpr ⟨hZr i, Finset.mem_univ _⟩⟩⟩
    have := Finset.card_le_card hsub
    rw [hZcard, card_erase3 hM r a c hra hrc hac] at this
    omega
  -- the index of `a` and of `c` inside `cm r b ∘ π`
  obtain ⟨qa, hqa⟩ := cmpl_covers hM cm hcm r b hrb a hra.symm hba.symm
  obtain ⟨qc, hqc⟩ := cmpl_covers hM cm hcm r b hrb c hrc.symm hbc.symm
  have hqa' : (fun i => cm r b (π i)) (π.symm qa) = a := by simp [hqa]
  have hqc' : (fun i => cm r b (π i)) (π.symm qc) = c := by simp [hqc]
  have hsa := hsplit a (π.symm qa) hqa' (fun i => hQa i)
  have hsc := hsplit c (π.symm qc) hqc' (fun i => hQc i)
  by_cases hZa : ∃ i, Z i = a
  · -- then `c` is missing from `Z`, so `Z` realises the edge `{r, c}`
    right
    have hZc : ∀ i, Z i ≠ c := by
      intro i hi
      exact hnotboth ⟨hZa, ⟨i, hi⟩⟩
    have hWa : ∀ i, W i ≠ a := by
      intro i hi
      have h1 : (π.symm qa) ∉ s := hsa.1.mp hZa
      exact h1 (hsa.2.mp ⟨i, hi⟩)
    have e1 : workFnU C₀ σ Z = workFnU C₀ σ (cm r c) :=
      wt_of_avoid hM cm hcm C₀ σ r c hrc Z hZinj hZr hZc
    have e2 : workFnU C₀ σ W = workFnU C₀ σ (cm b a) :=
      wt_of_avoid hM cm hcm C₀ σ b a (Ne.symm hba.symm) W hWinj hWb hWa
    rw [e1, e2] at hkey
    linarith
  · push_neg at hZa
    left
    have hZc : ∃ i, Z i = c := by
      by_contra hcon
      push_neg at hcon
      exact hnotneither ⟨hZa, hcon⟩
    have hWc : ∀ i, W i ≠ c := by
      intro i hi
      have h1 : (π.symm qc) ∉ s := hsc.1.mp hZc
      exact h1 (hsc.2.mp ⟨i, hi⟩)
    have e1 : workFnU C₀ σ Z = workFnU C₀ σ (cm r a) :=
      wt_of_avoid hM cm hcm C₀ σ r a hra Z hZinj hZr hZa
    have e2 : workFnU C₀ σ W = workFnU C₀ σ (cm b c) :=
      wt_of_avoid hM cm hcm C₀ σ b c hbc W hWinj hWb hWc
    rw [e1, e2] at hkey
    linarith

/-! ### The maximiser of the increment is a minimum-weight edge at the request -/

private noncomputable def muE {k : ℕ} {M : Type} [MetricSpace M]
    (cm : M → M → Config k M) (C₀ : Config k M) (σ : List M) (r u v : M) : ℝ :=
  workFnU C₀ σ (cm u v) + dist r u + dist r v

private theorem muE_symm {k : ℕ} {M : Type} [MetricSpace M] [Fintype M] [DecidableEq M]
    (hM : Fintype.card M = k + 2) (cm : M → M → Config k M) (hcm : IsCmpl cm)
    (C₀ : Config k M) (σ : List M) (r u v : M) (huv : u ≠ v) :
    muE cm C₀ σ r v u = muE cm C₀ σ r u v := by
  rw [muE, muE, wt_symm hM cm hcm C₀ σ u v huv]
  ring

private theorem step_le (k : ℕ) (hk : 1 ≤ k) {M : Type} [MetricSpace M] [Fintype M]
    [DecidableEq M] (hM : Fintype.card M = k + 2) (cm : M → M → Config k M)
    (hcm : IsCmpl cm) (C₀ : Config k M) (σ : List M) (r b c : M) (hbr : b ≠ r)
    (hcr : c ≠ r) (hcb : c ≠ b) :
    workFnU C₀ (σ ++ [r]) (cm r b) + dist r b ≤ muE cm C₀ σ r b c := by
  have h := wt_rec_le k hk hM cm hcm C₀ σ r b c (Ne.symm hbr) hcr hcb
  rw [muE]
  linarith

private theorem step_ge (k : ℕ) (hk : 1 ≤ k) {M : Type} [MetricSpace M] [Fintype M]
    [DecidableEq M] (hM : Fintype.card M = k + 2) (cm : M → M → Config k M)
    (hcm : IsCmpl cm) (C₀ : Config k M) (σ : List M) (r b : M) (hbr : b ≠ r) :
    ∃ c : M, c ≠ r ∧ c ≠ b ∧
      muE cm C₀ σ r b c ≤ workFnU C₀ (σ ++ [r]) (cm r b) + dist r b := by
  obtain ⟨c, hcr, hcb, h⟩ := wt_rec_ge k hk hM cm hcm C₀ σ r b (Ne.symm hbr)
  exact ⟨c, hcr, hcb, by rw [muE]; linarith⟩

/-- **The duality step in edge form.** There is a point `z` such that the edge `{r, z}` has
minimum weight among the edges at `r` for the new work function, and at the same time the
increment of the work function is maximal at the complement of `{r, z}`. -/
private theorem max_increment_edge (k : ℕ) (hk : 1 ≤ k) {M : Type} [MetricSpace M]
    [Fintype M] [DecidableEq M] (hM : Fintype.card M = k + 2) (cm : M → M → Config k M)
    (hcm : IsCmpl cm) (C₀ : Config k M) (σ : List M) (r : M) :
    ∃ z : M, z ≠ r ∧
      (∀ b : M, b ≠ r →
        workFnU C₀ (σ ++ [r]) (cm r z) + dist r z
          ≤ workFnU C₀ (σ ++ [r]) (cm r b) + dist r b) ∧
      (∀ b : M, b ≠ r →
        workFnU C₀ (σ ++ [r]) (cm r b) - workFnU C₀ σ (cm r b)
          ≤ workFnU C₀ (σ ++ [r]) (cm r z) - workFnU C₀ σ (cm r z)) := by
  classical
  set S : Finset (M × M) :=
    Finset.univ.filter (fun p : M × M => p.1 ≠ p.2 ∧ p.1 ≠ r ∧ p.2 ≠ r) with hS
  have hcard : 2 ≤ (Finset.univ.erase r).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, hM]
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.erase r).card)
  have hSne : S.Nonempty := by
    refine ⟨(x, y), ?_⟩
    rw [hS]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hxy, (Finset.mem_erase.mp hx).1, (Finset.mem_erase.mp hy).1⟩
  obtain ⟨p, hpS, hpmin⟩ :=
    S.exists_min_image (fun p : M × M => muE cm C₀ σ r p.1 p.2) hSne
  obtain ⟨hac, har, hcr⟩ : p.1 ≠ p.2 ∧ p.1 ≠ r ∧ p.2 ≠ r := by
    have := hpS; rw [hS] at this
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using this
  set A : M := p.1 with hA
  set C : M := p.2 with hC
  have hminAC : ∀ u v : M, u ≠ v → u ≠ r → v ≠ r →
      muE cm C₀ σ r A C ≤ muE cm C₀ σ r u v := by
    intro u v h1 h2 h3
    refine hpmin (u, v) ?_
    rw [hS]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h1, h2, h3⟩
  -- both endpoints of the minimising edge give a minimum-weight edge at `r`
  have hbase : ∀ b : M, b ≠ r →
      muE cm C₀ σ r A C ≤ workFnU C₀ (σ ++ [r]) (cm r b) + dist r b := by
    intro b hb
    obtain ⟨c, hcr', hcb, h⟩ := step_ge k hk hM cm hcm C₀ σ r b hb
    exact le_trans (hminAC b c (Ne.symm hcb) hb hcr') h
  have hAval : workFnU C₀ (σ ++ [r]) (cm r A) + dist r A = muE cm C₀ σ r A C :=
    le_antisymm (step_le k hk hM cm hcm C₀ σ r A C har hcr (Ne.symm hac)) (hbase A har)
  have hCval : workFnU C₀ (σ ++ [r]) (cm r C) + dist r C = muE cm C₀ σ r A C := by
    refine le_antisymm ?_ (hbase C hcr)
    have h := step_le k hk hM cm hcm C₀ σ r C A hcr har hac
    rwa [muE_symm hM cm hcm C₀ σ r A C hac] at h
  -- the increments at the two endpoints
  have hincrA : workFnU C₀ (σ ++ [r]) (cm r A) - workFnU C₀ σ (cm r A)
      = workFnU C₀ σ (cm A C) + dist r C - workFnU C₀ σ (cm r A) := by
    rw [muE] at hAval; linarith
  have hincrC : workFnU C₀ (σ ++ [r]) (cm r C) - workFnU C₀ σ (cm r C)
      = workFnU C₀ σ (cm A C) + dist r A - workFnU C₀ σ (cm r C) := by
    rw [muE] at hCval; linarith
  -- the general case
  have hgen : ∀ b : M, b ≠ r → b ≠ A → b ≠ C →
      workFnU C₀ (σ ++ [r]) (cm r b) - workFnU C₀ σ (cm r b)
        ≤ max (workFnU C₀ (σ ++ [r]) (cm r A) - workFnU C₀ σ (cm r A))
              (workFnU C₀ (σ ++ [r]) (cm r C) - workFnU C₀ σ (cm r C)) := by
    intro b hbr hbA hbC
    rcases edge_exchange k hk hM cm hcm C₀ σ r b A C (Ne.symm hbr) (Ne.symm har)
        (Ne.symm hcr) hbA hbC hac with hex | hex
    · have hup := step_le k hk hM cm hcm C₀ σ r b C hbr hcr (Ne.symm hbC)
      rw [muE] at hup
      refine le_trans ?_ (le_max_left _ _)
      rw [hincrA]
      linarith
    · have hup := step_le k hk hM cm hcm C₀ σ r b A hbr har (Ne.symm hbA)
      rw [muE] at hup
      refine le_trans ?_ (le_max_right _ _)
      rw [hincrC]
      linarith
  by_cases hcase : workFnU C₀ (σ ++ [r]) (cm r C) - workFnU C₀ σ (cm r C)
      ≤ workFnU C₀ (σ ++ [r]) (cm r A) - workFnU C₀ σ (cm r A)
  · refine ⟨A, har, fun b hb => by rw [hAval]; exact hbase b hb, fun b hb => ?_⟩
    by_cases hbA : b = A
    · rw [hbA]
    by_cases hbC : b = C
    · rw [hbC]; exact hcase
    · have := hgen b hb hbA hbC
      rw [max_eq_left hcase] at this
      exact this
  · push_neg at hcase
    refine ⟨C, hcr, fun b hb => by rw [hCval]; exact hbase b hb, fun b hb => ?_⟩
    by_cases hbA : b = A
    · rw [hbA]; exact le_of_lt hcase
    by_cases hbC : b = C
    · rw [hbC]
    · have := hgen b hb hbA hbC
      rw [max_eq_right (le_of_lt hcase)] at this
      exact this

/-! ### The spanning-tree potential -/

private theorem wfU_nonneg (k : ℕ) (hk : 1 ≤ k) {M : Type} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : 0 ≤ workFnU C₀ σ X := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ σ X
  rw [← hπ]
  exact workFn_nonneg k hk M C₀ σ (X ∘ (π : Equiv.Perm (Fin k)))

private noncomputable def Dsum (M : Type) [MetricSpace M] [Fintype M] : ℝ :=
  ∑ u : M, ∑ v : M, dist u v

private theorem dist_le_Dsum {M : Type} [MetricSpace M] [Fintype M] (u v : M) :
    dist u v ≤ Dsum M := by
  have h1 : dist u v ≤ ∑ w : M, dist u w :=
    Finset.single_le_sum (f := fun w => dist u w) (fun w _ => dist_nonneg)
      (Finset.mem_univ v)
  have h2 : (∑ w : M, dist u w) ≤ Dsum M :=
    Finset.single_le_sum (f := fun z => ∑ w : M, dist z w)
      (fun z _ => Finset.sum_nonneg fun w _ => dist_nonneg) (Finset.mem_univ u)
  linarith

private theorem Dsum_nonneg (M : Type) [MetricSpace M] [Fintype M] : 0 ≤ Dsum M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg

private theorem moveCost_le {k : ℕ} {M : Type} [MetricSpace M] [Fintype M]
    (X Y : Config k M) : moveCost X Y ≤ (k : ℝ) * Dsum M := by
  unfold moveCost
  calc ∑ i, dist (X i) (Y i) ≤ ∑ _i : Fin k, Dsum M :=
        Finset.sum_le_sum fun i _ => dist_le_Dsum (X i) (Y i)
    _ = (k : ℝ) * Dsum M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private def IsRT {M : Type} (ρ : M) (par : M → M) (rk : M → ℕ) : Prop :=
  rk ρ = 0 ∧ (∀ v, rk v = 0 → v = ρ) ∧ (∀ v, v ≠ ρ → rk (par v) < rk v)

private noncomputable def edgeW {k : ℕ} {M : Type} [MetricSpace M]
    (cm : M → M → Config k M) (C₀ : Config k M) (σ : List M) (u v : M) : ℝ :=
  workFnU C₀ σ (cm u v) + dist u v

private noncomputable def treeWt {k : ℕ} {M : Type} [MetricSpace M] [Fintype M]
    [DecidableEq M] (cm : M → M → Config k M) (C₀ : Config k M) (σ : List M)
    (ρ : M) (par : M → M) : ℝ :=
  ∑ v ∈ Finset.univ.erase ρ, edgeW cm C₀ σ v (par v)

private noncomputable def PotT {k : ℕ} {M : Type} [MetricSpace M] [Fintype M]
    [DecidableEq M] (cm : M → M → Config k M) (C₀ : Config k M) (σ : List M) : ℝ :=
  sInf {t : ℝ | ∃ (ρ : M) (par : M → M) (rk : M → ℕ),
    IsRT ρ par rk ∧ t = treeWt cm C₀ σ ρ par}

private theorem edgeW_symm {k : ℕ} {M : Type} [MetricSpace M] [Fintype M] [DecidableEq M]
    (hM : Fintype.card M = k + 2) (cm : M → M → Config k M) (hcm : IsCmpl cm)
    (C₀ : Config k M) (σ : List M) (u v : M) :
    edgeW cm C₀ σ u v = edgeW cm C₀ σ v u := by
  by_cases h : u = v
  · rw [h]
  · rw [edgeW, edgeW, wt_symm hM cm hcm C₀ σ u v h, dist_comm]

private theorem treeWt_nonneg (k : ℕ) (hk : 1 ≤ k) {M : Type} [MetricSpace M] [Fintype M]
    [DecidableEq M] (cm : M → M → Config k M) (C₀ : Config k M) (σ : List M)
    (ρ : M) (par : M → M) : 0 ≤ treeWt cm C₀ σ ρ par := by
  refine Finset.sum_nonneg fun v _ => ?_
  rw [edgeW]
  have := wfU_nonneg k hk C₀ σ (cm v (par v))
  have : (0:ℝ) ≤ dist v (par v) := dist_nonneg
  positivity

private theorem PotT_bdd (k : ℕ) (hk : 1 ≤ k) {M : Type} [MetricSpace M] [Fintype M]
    [DecidableEq M] (cm : M → M → Config k M) (C₀ : Config k M) (σ : List M) :
    BddBelow {t : ℝ | ∃ (ρ : M) (par : M → M) (rk : M → ℕ),
      IsRT ρ par rk ∧ t = treeWt cm C₀ σ ρ par} := by
  refine ⟨0, ?_⟩
  rintro t ⟨ρ, par, rk, -, rfl⟩
  exact treeWt_nonneg k hk cm C₀ σ ρ par

private theorem PotT_le (k : ℕ) (hk : 1 ≤ k) {M : Type} [MetricSpace M] [Fintype M]
    [DecidableEq M] (cm : M → M → Config k M) (C₀ : Config k M) (σ : List M)
    (ρ : M) (par : M → M) (rk : M → ℕ) (h : IsRT ρ par rk) :
    PotT cm C₀ σ ≤ treeWt cm C₀ σ ρ par :=
  csInf_le (PotT_bdd k hk cm C₀ σ) ⟨ρ, par, rk, h, rfl⟩

private theorem star_rt {M : Type} (v₀ : M) [DecidableEq M] :
    IsRT v₀ (fun _ => v₀) (fun v => if v = v₀ then 0 else 1) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro v hv
    dsimp only at hv
    by_contra h
    rw [if_neg h] at hv
    exact one_ne_zero hv
  · intro v hv
    dsimp only
    rw [if_neg hv, if_pos rfl]
    omega

private theorem PotT_nonneg (k : ℕ) (hk : 1 ≤ k) {M : Type} [MetricSpace M] [Fintype M]
    [DecidableEq M] [Nonempty M] (cm : M → M → Config k M) (C₀ : Config k M)
    (σ : List M) : 0 ≤ PotT cm C₀ σ := by
  obtain ⟨v₀⟩ := ‹Nonempty M›
  refine le_csInf ⟨treeWt cm C₀ σ v₀ (fun _ => v₀),
    ⟨v₀, fun _ => v₀, fun v => if v = v₀ then 0 else 1, star_rt v₀, rfl⟩⟩ ?_
  rintro t ⟨ρ, par, rk, -, rfl⟩
  exact treeWt_nonneg k hk cm C₀ σ ρ par

private theorem PotT_le_opt (k : ℕ) (hk : 1 ≤ k) {M : Type} [MetricSpace M] [Fintype M]
    [DecidableEq M] (hM : Fintype.card M = k + 2) (cm : M → M → Config k M)
    (C₀ : Config k M) (σ : List M) :
    PotT cm C₀ σ ≤ ((k : ℝ) + 1) * offlineCost C₀ σ
      + ((k : ℝ) + 1) * ((k : ℝ) + 1) * Dsum M := by
  have hne : Nonempty M := by rw [← Fintype.card_pos_iff, hM]; omega
  obtain ⟨v₀⟩ := hne
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨Xo, hXo⟩ := workFn_approx_offlineCost k hk M C₀ σ (ε / ((k : ℝ) + 1))
    (by positivity)
  have hbound : ∀ v ∈ Finset.univ.erase v₀,
      edgeW cm C₀ σ v ((fun _ => v₀) v)
        ≤ offlineCost C₀ σ + ε / ((k : ℝ) + 1) + ((k : ℝ) + 1) * Dsum M := by
    intro v _
    have h1 : workFnU C₀ σ (cm v v₀) ≤ workFnU C₀ σ Xo + moveCost Xo (cm v v₀) :=
      wfU_lip k hk C₀ σ (cm v v₀) Xo
    have h2 : workFnU C₀ σ Xo ≤ workFn C₀ σ Xo := wfU_self C₀ σ Xo
    have h3 := moveCost_le Xo (cm v v₀)
    have h4 : dist v v₀ ≤ Dsum M := dist_le_Dsum v v₀
    have h5 : (0:ℝ) ≤ Dsum M := Dsum_nonneg M
    rw [edgeW]
    nlinarith [hXo]
  have hsum := Finset.sum_le_card_nsmul (Finset.univ.erase v₀)
    (fun v => edgeW cm C₀ σ v ((fun _ => v₀) v))
    (offlineCost C₀ σ + ε / ((k : ℝ) + 1) + ((k : ℝ) + 1) * Dsum M) hbound
  have hcard : (Finset.univ.erase v₀).card = k + 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v₀), Finset.card_univ, hM]
    omega
  rw [hcard, nsmul_eq_mul] at hsum
  have hstar := PotT_le k hk cm C₀ σ v₀ (fun _ => v₀) (fun v => if v = v₀ then 0 else 1)
    (star_rt v₀)
  rw [treeWt] at hstar
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hsum
  have hk1 : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have hdiv : ((k : ℝ) + 1) * (ε / ((k : ℝ) + 1)) = ε := by field_simp
  nlinarith [hstar, hsum, hdiv]

/-! ### The step inequality and the growth bound -/

private theorem take_succ_eq {M : Type} (σ : List M) (t : ℕ) (ht : t < σ.length) :
    σ.take (t + 1) = σ.take t ++ [σ[t]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht]
  rfl

private theorem geom_half_le_one (n : ℕ) :
    (∑ t ∈ Finset.range n, (1:ℝ) / 2 ^ (t + 1)) ≤ 1 := by
  have key : ∀ m : ℕ, (∑ t ∈ Finset.range m, (1:ℝ) / 2 ^ (t + 1)) = 1 - 1 / 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; field_simp; ring
  rw [key]
  have h1 : (0:ℝ) ≤ 1 / 2 ^ n := by positivity
  linarith

private theorem exists_missing {k : ℕ} {M : Type} [Fintype M] [DecidableEq M]
    (hM : Fintype.card M = k + 2) (X : Config k M) (hX : Function.Injective X) :
    ∃ u v : M, u ≠ v ∧ (∀ i, X i ≠ u) ∧ (∀ i, X i ≠ v) := by
  classical
  have hc : (Finset.univ \ Finset.univ.image X).card = 2 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hM,
      Finset.card_image_of_injective _ hX, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨u, v, huv, hset⟩ := Finset.card_eq_two.mp hc
  have hu : u ∈ Finset.univ \ Finset.univ.image X := by rw [hset]; simp
  have hv : v ∈ Finset.univ \ Finset.univ.image X := by rw [hset]; simp
  refine ⟨u, v, huv, ?_, ?_⟩
  · intro i hi
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
  · intro i hi
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)

private theorem PotT_step (k : ℕ) (hk : 1 ≤ k) {M : Type} [MetricSpace M] [Fintype M]
    [DecidableEq M] (hM : Fintype.card M = k + 2) (cm : M → M → Config k M)
    (hcm : IsCmpl cm) (C₀ : Config k M) (σ : List M) (r : M) (ε : ℝ) (hε : 0 < ε)
    (X : Config k M) (hX : Function.Injective X) :
    workFnU C₀ (σ ++ [r]) X - workFnU C₀ σ X
      ≤ PotT cm C₀ (σ ++ [r]) - PotT cm C₀ σ + ε := by
  classical
  obtain ⟨z, hzr, hzmin, hzmax⟩ := max_increment_edge k hk hM cm hcm C₀ σ r
  have hrz : r ≠ z := Ne.symm hzr
  have hδ0 : 0 ≤ workFnU C₀ (σ ++ [r]) (cm r z) - workFnU C₀ σ (cm r z) := by
    have := wfU_mono k hk M C₀ σ r (cm r z); linarith
  -- the increment at `X` is dominated by the increment at the complement of `{r, z}`
  have hXδ : workFnU C₀ (σ ++ [r]) X - workFnU C₀ σ X
      ≤ workFnU C₀ (σ ++ [r]) (cm r z) - workFnU C₀ σ (cm r z) := by
    obtain ⟨u, v, huv, hu, hv⟩ := exists_missing hM X hX
    have e1 : workFnU C₀ (σ ++ [r]) X = workFnU C₀ (σ ++ [r]) (cm u v) :=
      wt_of_avoid hM cm hcm C₀ (σ ++ [r]) u v huv X hX hu hv
    have e2 : workFnU C₀ σ X = workFnU C₀ σ (cm u v) :=
      wt_of_avoid hM cm hcm C₀ σ u v huv X hX hu hv
    rw [e1, e2]
    by_cases hur : u = r
    · have hvr : v ≠ r := by rw [← hur]; exact Ne.symm huv
      rw [hur]
      exact hzmax v hvr
    · by_cases hvr : v = r
      · have h := hzmax u hur
        rw [hvr, wt_symm hM cm hcm C₀ (σ ++ [r]) r u (Ne.symm hur),
          wt_symm hM cm hcm C₀ σ r u (Ne.symm hur)]
        exact h
      · rw [wt_fix k hk hM cm hcm C₀ σ r u v huv (Ne.symm hur) (Ne.symm hvr)]
        linarith
  -- an `ε`-minimiser of the new potential
  have hne : ({t : ℝ | ∃ (ρ : M) (par : M → M) (rk : M → ℕ),
      IsRT ρ par rk ∧ t = treeWt cm C₀ (σ ++ [r]) ρ par}).Nonempty := by
    have hnem : Nonempty M := by rw [← Fintype.card_pos_iff, hM]; omega
    obtain ⟨v₀⟩ := hnem
    exact ⟨treeWt cm C₀ (σ ++ [r]) v₀ (fun _ => v₀),
      ⟨v₀, fun _ => v₀, fun v => if v = v₀ then 0 else 1, star_rt v₀, rfl⟩⟩
  obtain ⟨t0, ht0mem, ht0lt⟩ := exists_lt_of_csInf_lt hne
    (show PotT cm C₀ (σ ++ [r]) < PotT cm C₀ (σ ++ [r]) + ε by linarith)
  obtain ⟨ρ, par, rk, hRT, rfl⟩ := ht0mem
  -- move the edge `{r, z}` into the tree
  obtain ⟨par', rk', h1, h2, h3, hpr, hsum⟩ :=
    mst_cut_property (edgeW cm C₀ (σ ++ [r])) (edgeW_symm hM cm hcm C₀ (σ ++ [r]))
      r z hrz (fun b hb => hzmin b hb) ρ par rk hRT.1 hRT.2.1 hRT.2.2
  have hRT' : IsRT z par' rk' := ⟨h1, h2, h3⟩
  have hold : PotT cm C₀ σ ≤ treeWt cm C₀ σ z par' := PotT_le k hk cm C₀ σ z par' rk' hRT'
  have hnew : treeWt cm C₀ (σ ++ [r]) z par' ≤ PotT cm C₀ (σ ++ [r]) + ε := by
    rw [treeWt]
    have : treeWt cm C₀ (σ ++ [r]) ρ par ≤ PotT cm C₀ (σ ++ [r]) + ε := le_of_lt ht0lt
    rw [treeWt] at this
    linarith
  -- the change of the potential dominates the increment
  have hterms : ∀ v ∈ Finset.univ.erase z,
      0 ≤ edgeW cm C₀ (σ ++ [r]) v (par' v) - edgeW cm C₀ σ v (par' v) := by
    intro v _
    have := wfU_mono k hk M C₀ σ r (cm v (par' v))
    rw [edgeW, edgeW]
    linarith
  have hrmem : r ∈ Finset.univ.erase z := Finset.mem_erase.mpr ⟨hrz, Finset.mem_univ r⟩
  have hsingle := Finset.single_le_sum
    (f := fun v => edgeW cm C₀ (σ ++ [r]) v (par' v) - edgeW cm C₀ σ v (par' v))
    hterms hrmem
  have hsplit : ∑ v ∈ Finset.univ.erase z,
      (edgeW cm C₀ (σ ++ [r]) v (par' v) - edgeW cm C₀ σ v (par' v))
      = treeWt cm C₀ (σ ++ [r]) z par' - treeWt cm C₀ σ z par' := by
    rw [treeWt, treeWt, ← Finset.sum_sub_distrib]
  have hval : edgeW cm C₀ (σ ++ [r]) r (par' r) - edgeW cm C₀ σ r (par' r)
      = workFnU C₀ (σ ++ [r]) (cm r z) - workFnU C₀ σ (cm r z) := by
    rw [hpr, edgeW, edgeW]
    ring
  try dsimp only at hsingle
  rw [hsplit, hval] at hsingle
  linarith

theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (hM : Fintype.card M = k + 2) (C₀ : Config k M) :
    ∃ c : ℝ, ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config k M, Function.Injective X →
          workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ ((k : ℝ) + 1) * offlineCost C₀ σ + c := by
  classical
  have hnem : Nonempty M := by rw [← Fintype.card_pos_iff, hM]; omega
  obtain ⟨cm, hcm⟩ := exists_cmpl k hM
  refine ⟨((k : ℝ) + 1) * ((k : ℝ) + 1) * Dsum M + 1, fun σ => ?_⟩
  refine ⟨fun t => (PotT cm C₀ (σ.take (t + 1)) - PotT cm C₀ (σ.take t))
      + (1:ℝ) / 2 ^ (t + 1), ?_, ?_⟩
  · intro t ht X hX
    show workFnU C₀ (σ.take (t + 1)) X
      ≤ workFnU C₀ (σ.take t) X
        + ((PotT cm C₀ (σ.take (t + 1)) - PotT cm C₀ (σ.take t)) + (1:ℝ) / 2 ^ (t + 1))
    have hts : σ.take (t + 1) = σ.take t ++ [σ[t]] := take_succ_eq σ t ht
    have h := PotT_step k hk hM cm hcm C₀ (σ.take t) σ[t] ((1:ℝ) / 2 ^ (t + 1))
      (by positivity) X hX
    rw [← hts] at h
    linarith
  · show (∑ t ∈ Finset.range σ.length,
        ((PotT cm C₀ (σ.take (t + 1)) - PotT cm C₀ (σ.take t)) + (1:ℝ) / 2 ^ (t + 1)))
      ≤ ((k : ℝ) + 1) * offlineCost C₀ σ
        + (((k : ℝ) + 1) * ((k : ℝ) + 1) * Dsum M + 1)
    have hsplit : ∑ t ∈ Finset.range σ.length,
        ((PotT cm C₀ (σ.take (t + 1)) - PotT cm C₀ (σ.take t)) + (1:ℝ) / 2 ^ (t + 1))
        = (∑ t ∈ Finset.range σ.length,
            (PotT cm C₀ (σ.take (t + 1)) - PotT cm C₀ (σ.take t)))
          + ∑ t ∈ Finset.range σ.length, ((1:ℝ) / 2 ^ (t + 1)) := by
      rw [Finset.sum_add_distrib]
    have htel : ∑ t ∈ Finset.range σ.length,
        (PotT cm C₀ (σ.take (t + 1)) - PotT cm C₀ (σ.take t))
        = PotT cm C₀ σ - PotT cm C₀ [] := by
      rw [Finset.sum_range_sub (fun t => PotT cm C₀ (σ.take t)) σ.length, List.take_length,
        List.take_zero]
    have hgeom := geom_half_le_one σ.length
    have hopt := PotT_le_opt k hk hM cm C₀ σ
    have hge := PotT_nonneg k hk cm C₀ ([] : List M)
    rw [hsplit, htel]
    linarith
