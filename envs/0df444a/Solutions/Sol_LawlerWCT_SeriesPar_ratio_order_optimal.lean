-- Prove2me | solution 1 for LawlerWCT.SeriesPar.ratio_order_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:58:53.534973+00:00
-- url     : https://prove2.me/submissions/0e061c2e-2ed7-47e7-abfd-b8517b6093cf

import Mathlib
import Definitions.Def_LawlerWCT_SeriesPar_Model



namespace LawlerWCT.SeriesPar

def fcost {ι : Type*} (p w : ι → ℝ) : List ι → ℝ
  | [] => 0
  | a :: l => p a * (w a + (l.map w).sum) + fcost p w l

theorem fcost_append {ι : Type*} (p w : ι → ℝ) (l1 l2 : List ι) :
    fcost p w (l1 ++ l2) = fcost p w l1 + fcost p w l2 + (l1.map p).sum * (l2.map w).sum := by
  induction l1 with
  | nil => simp [fcost]
  | cons a l ih => simp only [List.cons_append, fcost, List.map_cons, List.sum_cons, List.map_append, List.sum_append, ih]; ring

theorem ct_cons_self {ι : Type*} [DecidableEq ι] (p : ι → ℝ) (a : ι) (l : List ι) :
    MooreLateJobs.Shared.completionTime p (a :: l) a = p a := by
  simp [MooreLateJobs.Shared.completionTime, MooreLateJobs.Shared.completionAt]

theorem ct_cons_ne {ι : Type*} [DecidableEq ι] (p : ι → ℝ) (a j : ι) (l : List ι) (h : j ≠ a) :
    MooreLateJobs.Shared.completionTime p (a :: l) j = p a + MooreLateJobs.Shared.completionTime p l j := by
  have : (a :: l).idxOf j = l.idxOf j + 1 := by
    simp [List.idxOf_cons, h.symm, beq_iff_eq]
  simp [MooreLateJobs.Shared.completionTime, MooreLateJobs.Shared.completionAt, this, List.take_succ_cons]

theorem wc_eq {ι : Type*} [DecidableEq ι] (p w : ι → ℝ) (l : List ι) (hl : l.Nodup) :
    ∑ j ∈ l.toFinset, w j * MooreLateJobs.Shared.completionTime p l j = fcost p w l := by
  induction l with
  | nil => simp [fcost]
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨ha, hl⟩ := hl
    have ih := ih hl
    rw [List.toFinset_cons, Finset.sum_insert (by simpa using ha), ct_cons_self]
    have : ∑ j ∈ l.toFinset, w j * MooreLateJobs.Shared.completionTime p (a :: l) j
        = ∑ j ∈ l.toFinset, (w j * p a + w j * MooreLateJobs.Shared.completionTime p l j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have : j ≠ a := fun h => ha (h ▸ List.mem_toFinset.1 hj)
      rw [ct_cons_ne p a j l this]; ring
    rw [this, Finset.sum_add_distrib, ih, ← Finset.sum_mul]
    have hs : ∑ j ∈ l.toFinset, w j = (l.map w).sum := by
      rw [List.sum_toFinset _ hl]
    rw [hs]; simp only [fcost]; ring

def gcost {ι : Type*} (p w : ι → ℝ) : List (List ι) → ℝ
  | [] => 0
  | c :: L => fcost p w c + gcost p w L + (c.map p).sum * (L.flatten.map w).sum

theorem gcost_eq {ι : Type*} (p w : ι → ℝ) (L : List (List ι)) :
    gcost p w L = fcost p w L.flatten := by
  induction L with
  | nil => simp [gcost, fcost]
  | cons c L ih => simp only [gcost, List.flatten_cons, fcost_append, ih]

theorem flat_bound {ι : Type*} (p w : ι → ℝ) (r : ℝ) (B : List (List ι))
    (h : ∀ b ∈ B, (b.map w).sum ≤ r * (b.map p).sum) :
    (B.flatten.map w).sum ≤ r * (B.flatten.map p).sum := by
  induction B with
  | nil => simp
  | cons b B ih =>
    simp only [List.flatten_cons, List.map_append, List.sum_append]
    have h1 := h b List.mem_cons_self
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    nlinarith

theorem gcost_le {ι : Type*} (p w : ι → ℝ) :
    ∀ (A B : List (List ι)), A.Perm B →
      A.Pairwise (fun a b => (b.map w).sum / (b.map p).sum ≤ (a.map w).sum / (a.map p).sum) →
      (∀ c ∈ A, 0 < (c.map p).sum) → gcost p w A ≤ gcost p w B := by
  intro A
  induction A with
  | nil => intro B h _ _; rw [List.nil_perm.1 h]
  | cons a A ih =>
    intro B hperm hsort hpos
    rw [List.pairwise_cons] at hsort
    obtain ⟨hmax, hsortA⟩ := hsort
    have haB : a ∈ B := hperm.subset (List.mem_cons_self)
    obtain ⟨B1, B2, hB⟩ := List.append_of_mem haB
    subst hB
    have hperm' : (B1 ++ B2).Perm A := by
      have := (List.perm_middle (a := a) (l₁ := B1) (l₂ := B2))
      exact (List.Perm.cons_inv (this.symm.trans hperm.symm)).symm.symm |>.symm.symm
    have hpa : 0 < (a.map p).sum := hpos a List.mem_cons_self
    have hposA : ∀ c ∈ A, 0 < (c.map p).sum := fun c hc => hpos c (List.mem_cons_of_mem _ hc)
    have ih' := ih (B1 ++ B2) hperm'.symm hsortA hposA
    have hWeq : (A.flatten.map w).sum = ((B1 ++ B2).flatten.map w).sum :=
      (hperm'.flatten.map w).sum_eq.symm
    -- B1 ratio bound
    have hB1 : ∀ b ∈ B1, (b.map w).sum ≤ (a.map w).sum / (a.map p).sum * (b.map p).sum := by
      intro b hb
      have hbA : b ∈ a :: A := hperm.symm.subset (by simp [hb])
      have hbpos := hpos b hbA
      have : (b.map w).sum / (b.map p).sum ≤ (a.map w).sum / (a.map p).sum := by
        rcases List.mem_cons.1 hbA with rfl | h
        · exact le_rfl
        · exact hmax b h
      rwa [div_le_iff₀ hbpos] at this
    have hB1' := flat_bound p w _ B1 hB1
    have key : gcost p w (a :: (B1 ++ B2)) ≤ gcost p w (B1 ++ a :: B2) := by
      have gapp : ∀ X Y : List (List ι), gcost p w (X ++ Y) = gcost p w X + gcost p w Y +
          (X.flatten.map p).sum * (Y.flatten.map w).sum := by
        intro X Y
        rw [gcost_eq, gcost_eq, gcost_eq, List.flatten_append, fcost_append]
      rw [gapp B1 (a :: B2)]
      simp only [gcost, List.flatten_cons, List.flatten_append, List.map_append, List.sum_append]
      rw [gapp B1 B2]
      have hr : (B1.flatten.map p).sum * (a.map w).sum - (a.map p).sum * (B1.flatten.map w).sum ≥ 0 := by
        have := mul_le_mul_of_nonneg_left hB1' hpa.le
        have e : (a.map p).sum * ((a.map w).sum / (a.map p).sum * (B1.flatten.map p).sum) = (a.map w).sum * (B1.flatten.map p).sum := by
          field_simp
        nlinarith
      nlinarith
    calc gcost p w (a :: A) = fcost p w a + gcost p w A + (a.map p).sum * (A.flatten.map w).sum := rfl
      _ ≤ fcost p w a + gcost p w (B1 ++ B2) + (a.map p).sum * ((B1 ++ B2).flatten.map w).sum := by
          rw [hWeq]; linarith
      _ = gcost p w (a :: (B1 ++ B2)) := rfl
      _ ≤ _ := key

theorem ro_core {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    (F : List (List ι)) (hne : ∀ c ∈ F, c ≠ []) (hnd : F.flatten.Nodup)
    (hp : ∀ j ∈ F.flatten, 0 < p j) :
    ∀ L L' : List (List ι), L.Perm F → IsRatioOrder p w L → L'.Perm F →
      SingleMachinePrec.Biclique.weightedCompletion p w F.flatten.toFinset L.flatten ≤
        SingleMachinePrec.Biclique.weightedCompletion p w F.flatten.toFinset L'.flatten := by
  intro L L' hL hord hL'
  have key : ∀ M : List (List ι), M.Perm F →
      SingleMachinePrec.Biclique.weightedCompletion p w F.flatten.toFinset M.flatten = gcost p w M := by
    intro M hM
    have hperm := hM.flatten
    unfold SingleMachinePrec.Biclique.weightedCompletion
    rw [← List.toFinset_eq_of_perm _ _ hperm, wc_eq p w _ (hperm.nodup_iff.2 hnd), gcost_eq]
  rw [key L hL, key L' hL']
  apply gcost_le p w L L' (hL.trans hL'.symm) hord
  intro c hc
  have hcF := hL.subset hc
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (hne c hcF)
  have hall : ∀ j ∈ c, 0 < p j := fun j hj => hp j (List.mem_flatten.2 ⟨c, hcF, hj⟩)
  have : ∀ (c : List ι), (∀ j ∈ c, 0 < p j) → c ≠ [] → 0 < (c.map p).sum := by
    intro c hc hne
    induction c with
    | nil => exact absurd rfl hne
    | cons x c ih =>
      simp only [List.map_cons, List.sum_cons]
      have h1 := hc x List.mem_cons_self
      by_cases h : c = []
      · subst h; simpa using h1
      · have := ih (fun j hj => hc j (List.mem_cons_of_mem _ hj)) h
        linarith
  exact this c hall (hne c hcF)

end LawlerWCT.SeriesPar

open LawlerWCT.SeriesPar


theorem solution {ι : Type*} [DecidableEq ι] (p w : ι → ℝ)
    (F : List (List ι)) (hne : ∀ c ∈ F, c ≠ []) (hnd : F.flatten.Nodup)
    (hp : ∀ j ∈ F.flatten, 0 < p j) :
    ∀ L L' : List (List ι), L.Perm F → IsRatioOrder p w L → L'.Perm F →
      SingleMachinePrec.Biclique.weightedCompletion p w F.flatten.toFinset L.flatten ≤
        SingleMachinePrec.Biclique.weightedCompletion p w F.flatten.toFinset L'.flatten := by
  exact ro_core p w F hne hnd hp
