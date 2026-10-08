-- Prove2me | solution 1 for MulticutLShaped.SimpleRecourse.eq25_equivalent
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T04:23:20.78122+00:00
-- url     : https://prove2.me/submissions/5e4e48bb-5693-4c0b-9bfd-231d272c4314

import Mathlib
import Definitions.Def_MulticutLShaped_SimpleRecourse_Model



namespace MulticutLShaped.SimpleRecourse

variable {n1 m1 m2 J : ℕ}

lemma mc_coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) :=
  map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) f s

lemma mc_psiVal (qp qm h χ : ℝ) (hq : 0 ≤ qp + qm) :
    psiVal qp qm h χ = ((qm * (χ - h) + (qp + qm) * max 0 (h - χ) : ℝ) : EReal) := by
  unfold psiVal
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨max 0 (h - χ), max 0 (χ - h), le_max_left _ _, le_max_left _ _, ?_, ?_⟩
    · rcases le_total 0 (h - χ) with h1 | h1
      · rw [max_eq_right h1, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h1, max_eq_right (by linarith)]; ring
    · congr 1
      rcases le_total 0 (h - χ) with h1 | h1
      · rw [max_eq_right h1, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h1, max_eq_right (by linarith)]; ring
  · rintro _ ⟨yp, ym, hyp, hym, hd, rfl⟩
    rw [EReal.coe_le_coe_iff]
    have : max 0 (h - χ) ≤ yp := max_le hyp (by linarith)
    have hym' : ym = yp - (h - χ) := by linarith
    subst hym'
    nlinarith [mul_le_mul_of_nonneg_left this hq]

/-- real value of psi_ij -/
noncomputable def psiR (inst : Instance n1 m1 m2 J) (i : Fin m2) (j : Fin J) (χi : ℝ) : ℝ :=
  inst.qminus i j * (χi - inst.h i j) + inst.q i j * max 0 (inst.h i j - χi)

lemma mc_psi (inst : Instance n1 m1 m2 J) (i : Fin m2) (j : Fin J) (χi : ℝ) :
    psi inst i j χi = (psiR inst i j χi : EReal) :=
  mc_psiVal _ _ _ _ (inst.hq i j)

noncomputable def PsiIR (inst : Instance n1 m1 m2 J) (i : Fin m2) (χi : ℝ) : ℝ :=
  ∑ j, inst.p i j * psiR inst i j χi

lemma mc_PsiI (inst : Instance n1 m1 m2 J) (i : Fin m2) (χi : ℝ) :
    PsiI inst i χi = (PsiIR inst i χi : EReal) := by
  unfold PsiI PsiIR
  rw [mc_coe_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mc_psi, ← EReal.coe_mul]

lemma mc_Psi (inst : Instance n1 m1 m2 J) (χ : Fin m2 → ℝ) :
    Psi inst χ = ((∑ i, PsiIR inst i (χ i) : ℝ) : EReal) := by
  unfold Psi
  rw [mc_coe_sum]
  exact Finset.sum_congr rfl fun i _ => mc_PsiI _ _ _

noncomputable def ustar (inst : Instance n1 m1 m2 J) (x : Fin n1 → ℝ) : Fin m2 → Fin J → ℝ :=
  fun i j => max 0 (inst.p i j * inst.q i j * (inst.h i j - inst.T.mulVec x i))

lemma mc_pq (inst : Instance n1 m1 m2 J) (i : Fin m2) (j : Fin J) : 0 ≤ inst.p i j * inst.q i j :=
  mul_nonneg (inst.p_nonneg i j) (inst.hq i j)

lemma mc_z (inst : Instance n1 m1 m2 J) (x : Fin n1 → ℝ) :
    z inst x = ((obj25 inst x (inst.T.mulVec x) (ustar inst x) : ℝ) : EReal) := by
  unfold z
  rw [mc_Psi, ← EReal.coe_add]
  congr 1
  unfold obj25 PsiIR psiR ustar
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpq := mc_pq inst i j
  rcases le_total 0 (inst.h i j - inst.T.mulVec x i) with h1 | h1
  · rw [max_eq_right h1, max_eq_right (mul_nonneg hpq h1)]; ring
  · rw [max_eq_left h1, max_eq_left (mul_nonpos_of_nonneg_of_nonpos hpq h1)]; ring

lemma mc_feas_ustar (inst : Instance n1 m1 m2 J) (x : Fin n1 → ℝ) (hx : x ∈ K1 inst) :
    Feasible25 inst x (inst.T.mulVec x) (ustar inst x) :=
  ⟨hx.1, hx.2, sub_self _, fun _ _ => le_max_right _ _, fun _ _ => le_max_left _ _⟩

lemma mc_feas_T (inst : Instance n1 m1 m2 J) {x : Fin n1 → ℝ} {χ : Fin m2 → ℝ}
    {u : Fin m2 → Fin J → ℝ} (h : Feasible25 inst x χ u) : χ = inst.T.mulVec x :=
  (sub_eq_zero.mp h.2.2.1).symm

lemma mc_min (inst : Instance n1 m1 m2 J) (x : Fin n1 → ℝ) (u : Fin m2 → Fin J → ℝ)
    (hu : Feasible25 inst x (inst.T.mulVec x) u) :
    obj25 inst x (inst.T.mulVec x) (ustar inst x) ≤ obj25 inst x (inst.T.mulVec x) u := by
  unfold obj25
  gcongr with i _ j _
  exact max_le (hu.2.2.2.2 i j) (hu.2.2.2.1 i j)

lemma mc_feasK1 (inst : Instance n1 m1 m2 J) {x : Fin n1 → ℝ} {χ : Fin m2 → ℝ}
    {u : Fin m2 → Fin J → ℝ} (h : Feasible25 inst x χ u) : x ∈ K1 inst := ⟨h.1, h.2.1⟩

theorem eq25_core (inst : Instance n1 m1 m2 J) :
    (∀ x ∈ K1 inst,
      Feasible25 inst x (inst.T.mulVec x)
          (fun i j => max 0 (inst.p i j * inst.q i j * (inst.h i j - inst.T.mulVec x i))) ∧
      ((obj25 inst x (inst.T.mulVec x)
          (fun i j => max 0 (inst.p i j * inst.q i j * (inst.h i j - inst.T.mulVec x i))) : ℝ)
          : EReal) = z inst x ∧
      ∀ u, Feasible25 inst x (inst.T.mulVec x) u →
        obj25 inst x (inst.T.mulVec x)
            (fun i j => max 0 (inst.p i j * inst.q i j * (inst.h i j - inst.T.mulVec x i)))
          ≤ obj25 inst x (inst.T.mulVec x) u) ∧
    ∀ x, IsOptimal inst x ↔ ∃ χ u, IsOptimal25 inst x χ u := by
  refine ⟨fun x hx => ⟨mc_feas_ustar inst x hx, (mc_z inst x).symm, mc_min inst x⟩, fun x => ?_⟩
  constructor
  · rintro ⟨hx, hopt⟩
    refine ⟨_, _, mc_feas_ustar inst x hx, fun x' χ' u' h' => ?_⟩
    have hT := mc_feas_T inst h'
    subst hT
    have h1 := hopt x' (mc_feasK1 inst h')
    rw [mc_z, mc_z, EReal.coe_le_coe_iff] at h1
    exact h1.trans (mc_min inst x' u' h')
  · rintro ⟨χ, u, hf, hopt⟩
    have hT := mc_feas_T inst hf
    subst hT
    refine ⟨mc_feasK1 inst hf, fun x' hx' => ?_⟩
    rw [mc_z, mc_z, EReal.coe_le_coe_iff]
    exact (mc_min inst x u hf).trans (hopt _ _ _ (mc_feas_ustar inst x' hx'))

end MulticutLShaped.SimpleRecourse

open MulticutLShaped.SimpleRecourse

variable {n1 m1 m2 J : ℕ}


theorem solution (inst : Instance n1 m1 m2 J) :
    (∀ x ∈ K1 inst,
      Feasible25 inst x (inst.T.mulVec x)
          (fun i j => max 0 (inst.p i j * inst.q i j * (inst.h i j - inst.T.mulVec x i))) ∧
      ((obj25 inst x (inst.T.mulVec x)
          (fun i j => max 0 (inst.p i j * inst.q i j * (inst.h i j - inst.T.mulVec x i))) : ℝ)
          : EReal) = z inst x ∧
      ∀ u, Feasible25 inst x (inst.T.mulVec x) u →
        obj25 inst x (inst.T.mulVec x)
            (fun i j => max 0 (inst.p i j * inst.q i j * (inst.h i j - inst.T.mulVec x i)))
          ≤ obj25 inst x (inst.T.mulVec x) u) ∧
    ∀ x, IsOptimal inst x ↔ ∃ χ u, IsOptimal25 inst x χ u := by
  exact eq25_core inst
