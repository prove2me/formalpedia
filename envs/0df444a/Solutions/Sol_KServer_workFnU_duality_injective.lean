-- Prove2me | solution 1 for KServer.workFnU_duality_injective
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T11:46:11.845429+00:00
-- url     : https://prove2.me/submissions/fefc20d1-de1e-4b99-a96a-797999fb4cdb

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_quasiconvex
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_mono
import Theorems.Thm_KServer_workFn_rec_ge
import Theorems.Thm_KServer_workFn_rec_le

/-!
Duality for the unordered work function, restricted to proper configurations.

The proof follows the recurrence/quasiconvexity framework of Koutsoupias.  The
new ingredient is an *injective ksd_exchange lemma*: for a proper `P` and an
injective `Q` containing the request `r`, the quasiconvexity matching `π`
between `P` and `Q` is cut along the component of the "matching graph"
containing the index of `r`; the two resulting hybrids are injective, one of
them is proper, and the other is a relabelling of `P` with one point moved to
`r`.
-/

open KServer

set_option linter.unusedSectionVars false

variable {k : ℕ} {M : Type} [MetricSpace M]

/-- The distance functional `ksd_D(X) = ∑ᵢ d(r, Xᵢ)`. -/
def ksd_D (r : M) (X : Config k M) : ℝ := ∑ i, dist r (X i)

lemma ksd_workFnU_le_workFn (C₀ : Config k M) (σ : List M) (X : Config k M)
    (π : Equiv.Perm (Fin k)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) := by
  unfold workFnU
  exact ciInf_le (Set.finite_range _).bddBelow π

lemma ksd_exists_workFnU_eq (C₀ : Config k M) (σ : List M) (X : Config k M) :
    ∃ π : Equiv.Perm (Fin k), workFnU C₀ σ X = workFn C₀ σ (X ∘ π) := by
  unfold workFnU
  obtain ⟨π, hπ⟩ :=
    exists_eq_ciInf_of_finite (f := fun π : Equiv.Perm (Fin k) => workFn C₀ σ (X ∘ π))
  exact ⟨π, hπ.symm⟩

lemma ksd_update_comp_perm (X : Config k M) (i : Fin k) (r : M) (π : Equiv.Perm (Fin k)) :
    Function.update X i r ∘ π = Function.update (X ∘ π) (π.symm i) r :=
  Function.update_comp_equiv X π i r

/-- Recurrence, upper bound. -/
lemma ksd_recU_le (hk : 1 ≤ k) (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M)
    (i : Fin k) :
    workFnU C₀ (σ ++ [r]) X ≤ workFnU C₀ σ (Function.update X i r) + dist r (X i) := by
  obtain ⟨π, hπ⟩ := ksd_exists_workFnU_eq C₀ σ (Function.update X i r)
  calc workFnU C₀ (σ ++ [r]) X ≤ workFn C₀ (σ ++ [r]) (X ∘ π) := ksd_workFnU_le_workFn _ _ _ _
    _ ≤ workFn C₀ σ (Function.update (X ∘ π) (π.symm i) r) + dist r ((X ∘ π) (π.symm i)) :=
        workFn_rec_le k hk M C₀ σ r (X ∘ π) (π.symm i)
    _ = workFnU C₀ σ (Function.update X i r) + dist r (X i) := by
        rw [hπ, ksd_update_comp_perm]
        simp

/-- Recurrence, lower bound. -/
lemma ksd_recU_ge (hk : 1 ≤ k) (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    ∃ i : Fin k,
      workFnU C₀ σ (Function.update X i r) + dist r (X i) ≤ workFnU C₀ (σ ++ [r]) X := by
  obtain ⟨π, hπ⟩ := ksd_exists_workFnU_eq C₀ (σ ++ [r]) X
  obtain ⟨j, hj⟩ := workFn_rec_ge k hk M C₀ σ r (X ∘ π)
  refine ⟨π j, ?_⟩
  rw [hπ]
  have h1 : workFnU C₀ σ (Function.update X (π j) r) ≤
      workFn C₀ σ (Function.update (X ∘ π) j r) := by
    have := ksd_workFnU_le_workFn C₀ σ (Function.update X (π j) r) π
    rwa [ksd_update_comp_perm, Equiv.symm_apply_apply] at this
  have h2 : (X ∘ π) j = X (π j) := rfl
  rw [h2] at hj
  linarith

lemma ksd_D_update (r : M) (X : Config k M) (i : Fin k) :
    ksd_D r (Function.update X i r) + dist r (X i) = ksd_D r X := by
  unfold ksd_D
  have hfun : (fun j => dist r (Function.update X i r j)) =
      Function.update (fun j => dist r (X j)) i 0 := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ i), zero_add,
    Finset.sdiff_singleton_eq_erase]
  exact Finset.sum_erase_add _ _ (Finset.mem_univ i)

lemma ksd_D_perm (r : M) (X : Config k M) (τ : Equiv.Perm (Fin k)) :
    ksd_D r (X ∘ τ) = ksd_D r X :=
  Equiv.sum_comp τ (fun j => dist r (X j))

lemma ksd_update_injective (X : Config k M) (r : M) (hX : Function.Injective X)
    (hXr : ∀ i, X i ≠ r) (i : Fin k) : Function.Injective (Function.update X i r) := by
  intro a b hab
  by_cases ha : a = i <;> by_cases hb : b = i
  · rw [ha, hb]
  · subst ha
    rw [Function.update_self, Function.update_of_ne hb] at hab
    exact absurd hab.symm (hXr b)
  · subst hb
    rw [Function.update_self, Function.update_of_ne ha] at hab
    exact absurd hab (hXr a)
  · rw [Function.update_of_ne ha, Function.update_of_ne hb] at hab
    exact hX hab

/-- An injective configuration whose values lie in `range P ∪ {r}` and which
contains `r` is a relabelling of `P` with exactly one point moved to `r`. -/
lemma ksd_relabel (P : Config k M) (r : M) (hP : Function.Injective P) (hPr : ∀ i, P i ≠ r)
    (W : Config k M) (hW : Function.Injective W) (hWrange : ∀ i, W i = r ∨ ∃ b, W i = P b)
    (hWr : ∃ i, W i = r) :
    ∃ (l : Fin k) (τ : Equiv.Perm (Fin k)), W = Function.update P l r ∘ τ := by
  classical
  let B : Finset (Fin k) := Finset.univ.filter (fun j => ∀ i, W i ≠ P j)
  have hB : B.card = 1 := by
    have hSP : (Finset.univ.image P).card = k := by
      rw [Finset.card_image_of_injective _ hP, Finset.card_univ, Fintype.card_fin]
    have hSW : (Finset.univ.image W).card = k := by
      rw [Finset.card_image_of_injective _ hW, Finset.card_univ, Fintype.card_fin]
    have hrSW : r ∈ Finset.univ.image W := by
      obtain ⟨i, hi⟩ := hWr
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
    have hrSP : r ∉ Finset.univ.image P := by
      intro h
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
      exact hPr j hj
    have hinter : Finset.univ.image P ∩ Finset.univ.image W =
        (Finset.univ.image W).erase r := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_erase]
      constructor
      · rintro ⟨hxP, hxW⟩
        exact ⟨fun h => hrSP (h ▸ hxP), hxW⟩
      · rintro ⟨hxr, hxW⟩
        refine ⟨?_, hxW⟩
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hxW
        rcases hWrange i with h | ⟨b, hb⟩
        · exact absurd h hxr
        · exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb.symm⟩
    have hBimg : B.image P = Finset.univ.image P \ Finset.univ.image W := by
      ext x
      simp only [B, Finset.mem_image, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
        true_and, not_exists]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨j, rfl⟩, fun i hi => hj i hi⟩
      · rintro ⟨⟨j, rfl⟩, hx⟩
        exact ⟨j, fun i hi => hx i hi, rfl⟩
    have h1 := Finset.card_sdiff_add_card_inter (Finset.univ.image P) (Finset.univ.image W)
    rw [hinter, Finset.card_erase_of_mem hrSW, hSW, hSP] at h1
    have h2 : (B.image P).card = B.card := Finset.card_image_of_injective _ hP
    rw [hBimg] at h2
    have hk1 : 1 ≤ k := by
      obtain ⟨i, _⟩ := hWr
      have := i.isLt
      omega
    omega
  obtain ⟨l, hl⟩ := Finset.card_eq_one.mp hB
  have hlB : l ∈ B := by rw [hl]; exact Finset.mem_singleton_self l
  have hl_missed : ∀ i, W i ≠ P l := (Finset.mem_filter.mp hlB).2
  have huniq : ∀ j, (∀ i, W i ≠ P j) → j = l := by
    intro j hj
    have : j ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    rw [hl] at this
    exact Finset.mem_singleton.mp this
  have hU : Function.Injective (Function.update P l r) := ksd_update_injective P r hP hPr l
  have hrange : Set.range W = Set.range (Function.update P l r) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rcases hWrange i with h | ⟨b, hb⟩
      · exact ⟨l, by rw [Function.update_self, h]⟩
      · have hbl : b ≠ l := by
          rintro rfl
          exact hl_missed i hb
        exact ⟨b, by rw [Function.update_of_ne hbl, hb]⟩
    · rintro ⟨j, rfl⟩
      by_cases hj : j = l
      · subst hj
        rw [Function.update_self]
        obtain ⟨i, hi⟩ := hWr
        exact ⟨i, hi⟩
      · rw [Function.update_of_ne hj]
        by_contra hne
        apply hj
        apply huniq j
        intro i hi
        exact hne ⟨i, hi⟩
  refine ⟨l, (Equiv.ofInjective W hW).trans
    ((Equiv.setCongr hrange).trans (Equiv.ofInjective _ hU).symm), ?_⟩
  funext i
  simp only [Function.comp_apply, Equiv.trans_apply, Equiv.setCongr_apply]
  rw [Equiv.apply_ofInjective_symm hU]
  simp

/-- The injective ksd_exchange lemma. -/
lemma ksd_exchange (hk : 1 ≤ k) (C₀ : Config k M) (σ : List M) (r : M) (A : Config k M)
    (hA : ∀ X : Config k M, Function.Injective X → (∀ i, X i ≠ r) →
      workFnU C₀ σ A - ksd_D r A ≤ workFnU C₀ σ X - ksd_D r X)
    (P Q : Config k M) (hP : Function.Injective P) (hPr : ∀ i, P i ≠ r)
    (hQ : Function.Injective Q) (j₀ : Fin k) (hQj : Q j₀ = r) :
    ∃ l : Fin k,
      (workFnU C₀ σ A - ksd_D r A) +
        (workFnU C₀ σ (Function.update P l r) - ksd_D r (Function.update P l r))
      ≤ (workFnU C₀ σ P - ksd_D r P) + (workFnU C₀ σ Q - ksd_D r Q) := by
  classical
  obtain ⟨π, hπ⟩ := workFnU_quasiconvex k hk M C₀ σ P Q
  set i₀ : Fin k := π.symm j₀ with hi₀
  have hQπi₀ : Q (π i₀) = r := by rw [hi₀, Equiv.apply_symm_apply]; exact hQj
  -- reverse-edge relation: `R b c` iff `P b = Q (π c)`
  let R : Fin k → Fin k → Prop := fun b c => P b = Q (π c)
  let T : Finset (Fin k) := Finset.univ.filter (fun i => Relation.ReflTransGen R i₀ i)
  have hT : ∀ i, i ∈ T ↔ Relation.ReflTransGen R i₀ i := by
    intro i; simp [T]
  have hi₀T : i₀ ∈ T := (hT i₀).2 Relation.ReflTransGen.refl
  have hin : ∀ i c, i ∈ T → P i = Q (π c) → c ∈ T := fun i c hi h =>
    (hT c).2 (Relation.ReflTransGen.tail ((hT i).1 hi) h)
  have hout : ∀ i c, i ∈ T → P c = Q (π i) → c ∈ T := by
    intro i c hi h
    rcases Relation.ReflTransGen.cases_tail ((hT i).1 hi) with h0 | ⟨b, hb, hbi⟩
    · exfalso
      subst h0
      exact hPr c (h.trans hQπi₀)
    · have : c = b := hP (h.trans hbi.symm)
      rw [this]
      exact (hT b).2 hb
  have hout_ex : ∀ i, i ∈ T → i ≠ i₀ → ∃ b, P b = Q (π i) := by
    intro i hi hne
    rcases Relation.ReflTransGen.cases_tail ((hT i).1 hi) with h0 | ⟨b, _, hbi⟩
    · exact absurd h0 hne
    · exact ⟨b, hbi⟩
  set Z : Config k M := fun i => if i ∈ T then P i else Q (π i) with hZ
  set W : Config k M := fun i => if i ∈ T then Q (π i) else P i with hW
  have hqc := hπ T
  have hZinj : Function.Injective Z := by
    intro a b hab
    simp only [hZ] at hab
    by_cases ha : a ∈ T <;> by_cases hb : b ∈ T <;>
      simp only [ha, hb, if_true, if_false] at hab
    · exact hP hab
    · exact absurd (hin a b ha hab) hb
    · exact absurd (hin b a hb hab.symm) ha
    · exact π.injective (hQ hab)
  have hZr : ∀ i, Z i ≠ r := by
    intro i
    simp only [hZ]
    split_ifs with hi
    · exact hPr i
    · intro h
      have h1 : π i = j₀ := hQ (h.trans hQj.symm)
      apply hi
      have h2 : i = i₀ := by rw [hi₀, ← h1, Equiv.symm_apply_apply]
      rw [h2]
      exact hi₀T
  have hW_i₀ : W i₀ = r := by simp only [hW, if_pos hi₀T, hQπi₀]
  have hWinj : Function.Injective W := by
    intro a b hab
    simp only [hW] at hab
    by_cases ha : a ∈ T <;> by_cases hb : b ∈ T <;>
      simp only [ha, hb, if_true, if_false] at hab
    · exact π.injective (hQ hab)
    · exact absurd (hout a b ha hab.symm) hb
    · exact absurd (hout b a hb hab) ha
    · exact hP hab
  have hWrange : ∀ i, W i = r ∨ ∃ b, W i = P b := by
    intro i
    simp only [hW]
    split_ifs with hi
    · by_cases hne : i = i₀
      · left; rw [hne, hQπi₀]
      · right
        obtain ⟨b, hb⟩ := hout_ex i hi hne
        exact ⟨b, hb.symm⟩
    · right; exact ⟨i, rfl⟩
  have hD : ksd_D r Z + ksd_D r W = ksd_D r P + ksd_D r Q := by
    unfold ksd_D
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ i, dist r (Z i) + dist r (W i) = dist r (P i) + dist r (Q (π i)) := by
      intro i
      simp only [hZ, hW]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
    congr 1
    exact Equiv.sum_comp π (fun j => dist r (Q j))
  obtain ⟨l, τ, hWτ⟩ := ksd_relabel P r hP hPr W hWinj hWrange ⟨i₀, hW_i₀⟩
  refine ⟨l, ?_⟩
  have hAZ := hA Z hZinj hZr
  have hWU : workFnU C₀ σ W = workFnU C₀ σ (Function.update P l r) := by
    rw [hWτ]
    exact workFnU_perm k M C₀ σ _ τ
  have hWD : ksd_D r W = ksd_D r (Function.update P l r) := by
    rw [hWτ]
    exact ksd_D_perm r _ τ
  linarith

open KServer in
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (A : Config k M)
    (hAinj : Function.Injective A) (hAr : ∀ i, A i ≠ r)
    (hA : ∀ X : Config k M, Function.Injective X → (∀ i, X i ≠ r) →
      workFnU C₀ σ A - ∑ i, dist r (A i) ≤ workFnU C₀ σ X - ∑ i, dist r (X i)) :
    (∀ X : Config k M, Function.Injective X → (∀ i, X i ≠ r) →
        workFnU C₀ (σ ++ [r]) A - ∑ i, dist r (A i)
          ≤ workFnU C₀ (σ ++ [r]) X - ∑ i, dist r (X i)) ∧
    (∀ X : Config k M, Function.Injective X →
        workFnU C₀ (σ ++ [r]) X - workFnU C₀ σ X
          ≤ workFnU C₀ (σ ++ [r]) A - workFnU C₀ σ A) := by
  classical
  have hA' : ∀ X : Config k M, Function.Injective X → (∀ i, X i ≠ r) →
      workFnU C₀ σ A - ksd_D r A ≤ workFnU C₀ σ X - ksd_D r X := hA
  constructor
  · intro X hX hXr
    obtain ⟨i, hi⟩ := ksd_recU_ge hk C₀ σ r X
    obtain ⟨l, hl⟩ := ksd_exchange hk C₀ σ r A hA' A (Function.update X i r) hAinj hAr
      (ksd_update_injective X r hX hXr i) i (by simp)
    have h1 := ksd_recU_le hk C₀ σ r A l
    have h2 := ksd_D_update r A l
    have h3 := ksd_D_update r X i
    show workFnU C₀ (σ ++ [r]) A - ksd_D r A ≤ workFnU C₀ (σ ++ [r]) X - ksd_D r X
    linarith
  · intro X hX
    by_cases hXr : ∀ i, X i ≠ r
    · obtain ⟨i, hi⟩ := ksd_recU_ge hk C₀ σ r A
      obtain ⟨l, hl⟩ := ksd_exchange hk C₀ σ r A hA' X (Function.update A i r) hX hXr
        (ksd_update_injective A r hAinj hAr i) i (by simp)
      have h1 := ksd_recU_le hk C₀ σ r X l
      have h2 := ksd_D_update r X l
      have h3 := ksd_D_update r A i
      linarith
    · push Not at hXr
      obtain ⟨i, hi⟩ := hXr
      have h1 := ksd_recU_le hk C₀ σ r X i
      have h2 : Function.update X i r = X := by
        rw [← hi]
        exact Function.update_eq_self i X
      rw [h2, hi, dist_self, add_zero] at h1
      have h3 := workFnU_mono k hk M C₀ σ r A
      linarith
