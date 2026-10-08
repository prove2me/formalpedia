-- Prove2me | solution 1 for MulticutLShaped.SimpleRecourse.relaxation_stop
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T04:23:23.588097+00:00
-- url     : https://prove2.me/submissions/b51b102a-e0fd-4a89-ab49-05e5420f7b56

import Mathlib
import Definitions.Def_MulticutLShaped_SimpleRecourse_Algorithm



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


lemma mc_rowdot (inst : Instance n1 m1 m2 J) (x : Fin n1 → ℝ) (i : Fin m2) :
    inst.T i ⬝ᵥ x = inst.T.mulVec x i := rfl

lemma mc_cut (inst : Instance n1 m1 m2 J) (x : Fin n1 → ℝ) (l : Fin m2 × Fin J) :
    cute inst l - cutE inst l ⬝ᵥ x =
      inst.p l.1 l.2 * inst.q l.1 l.2 * (inst.h l.1 l.2 - inst.T.mulVec x l.1) := by
  unfold cute cutE
  rw [smul_dotProduct, smul_eq_mul, mc_rowdot]; ring

lemma mc_sumprod (u : Fin m2 → Fin J → ℝ) :
    ∑ i, ∑ j, u i j = ∑ l : Fin m2 × Fin J, u l.1 l.2 := by
  rw [Fintype.sum_prod_type]

theorem relax_core (inst : Instance n1 m1 m2 J) (I : Finset (Fin m2 × Fin J)) :
    (∀ x χ u, Feasible25 inst x χ u →
      MasterFeasible inst I x (fun l => u l.1 l.2) ∧
      masterObj inst I x (fun l => u l.1 l.2) -
          ∑ i, ∑ j, inst.p i j * inst.qminus i j * inst.h i j ≤ obj25 inst x χ u) ∧
    ∀ x u, MasterOptimal inst I x u → violated inst I x = ∅ →
      IsOptimal25 inst x (inst.T.mulVec x) (fun i j => if (i, j) ∈ I then u (i, j) else 0) := by
  have part1 : ∀ x χ u, Feasible25 inst x χ u →
      MasterFeasible inst I x (fun l => u l.1 l.2) ∧
      masterObj inst I x (fun l => u l.1 l.2) -
          ∑ i, ∑ j, inst.p i j * inst.qminus i j * inst.h i j ≤ obj25 inst x χ u := by
    intro x χ u hf
    have hT := mc_feas_T inst hf
    subst hT
    refine ⟨⟨hf.1, hf.2.1, fun l _ => ⟨?_, hf.2.2.2.2 _ _⟩⟩, ?_⟩
    · rw [mc_cut]; exact hf.2.2.2.1 _ _
    · unfold masterObj obj25
      have hs : ∑ l ∈ I, u l.1 l.2 ≤ ∑ i, ∑ j, u i j := by
        rw [mc_sumprod]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun l _ _ => hf.2.2.2.2 _ _)
      have he : ∑ i, ∑ j, inst.p i j * inst.qminus i j * (inst.T i ⬝ᵥ x) -
          ∑ i, ∑ j, inst.p i j * inst.qminus i j * inst.h i j =
          ∑ i, ∑ j, inst.p i j * inst.qminus i j * (inst.T.mulVec x i - inst.h i j) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mc_rowdot]; ring
      linarith
  refine ⟨part1, fun x u hopt hv => ?_⟩
  have hf : Feasible25 inst x (inst.T.mulVec x)
      (fun i j => if (i, j) ∈ I then u (i, j) else 0) := by
    refine ⟨hopt.1.1, hopt.1.2.1, sub_self _, fun i j => ?_, fun i j => ?_⟩
    · by_cases hI : (i, j) ∈ I
      · simp only [hI, if_true]
        have := (hopt.1.2.2 (i, j) hI).1
        rw [mc_cut] at this; exact this
      · simp only [hI, if_false]
        have : (i, j) ∉ violated inst I x := by rw [hv]; simp
        unfold violated at this
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at this
        have := this hI
        rw [mc_rowdot] at this; exact this
    · by_cases hI : (i, j) ∈ I
      · simp only [hI, if_true]; exact (hopt.1.2.2 (i, j) hI).2
      · simp [hI]
  refine ⟨hf, fun x' χ' u' hf' => ?_⟩
  have h1 := (part1 x' χ' u' hf').2
  have h2 := hopt.2 x' _ (part1 x' χ' u' hf').1
  have h3 := (part1 _ _ _ hf).2
  have heq : obj25 inst x (inst.T.mulVec x) (fun i j => if (i, j) ∈ I then u (i, j) else 0) =
      masterObj inst I x (fun l => if (l.1, l.2) ∈ I then u (l.1, l.2) else 0) -
          ∑ i, ∑ j, inst.p i j * inst.qminus i j * inst.h i j := by
    unfold masterObj obj25
    have hs : ∑ i, ∑ j, (if (i, j) ∈ I then u (i, j) else 0) =
        ∑ l ∈ I, (if (l.1, l.2) ∈ I then u (l.1, l.2) else 0) := by
      rw [mc_sumprod]
      rw [← Finset.sum_subset (Finset.subset_univ I)]
      intro l _ hl; simp [hl]
    rw [hs, ← sub_eq_zero]
    have he : ∑ i, ∑ j, inst.p i j * inst.qminus i j * (inst.T i ⬝ᵥ x) -
        ∑ i, ∑ j, inst.p i j * inst.qminus i j * inst.h i j =
        ∑ i, ∑ j, inst.p i j * inst.qminus i j * (inst.T.mulVec x i - inst.h i j) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mc_rowdot]; ring
    linarith
  have hmo : masterObj inst I x (fun l => if (l.1, l.2) ∈ I then u (l.1, l.2) else 0) =
      masterObj inst I x u := by
    unfold masterObj
    congr 1
    refine Finset.sum_congr rfl fun l hl => ?_
    simp [hl]
  linarith

lemma mc_reach_card (inst : Instance n1 m1 m2 J) {ν : ℕ} {I : Finset (Fin m2 × Fin J)}
    (h : Reach inst ν I) : ν ≤ I.card + 1 := by
  induction h with
  | start => simp
  | @step ν0 I0 I1 _ hs ih =>
    obtain ⟨x, u, _, hne, rfl⟩ := hs
    have hd : Disjoint I0 (violated inst I0 x) := by
      rw [Finset.disjoint_right]
      intro l hl
      unfold violated at hl
      simp only [Finset.mem_filter] at hl
      exact hl.2.1
    rw [Finset.card_union_of_disjoint hd]
    have := hne.card_pos
    omega

theorem goal_core (inst : Instance n1 m1 m2 J) :
    (∀ ν I, Reach inst ν I → ν ≤ J * m2 + 1) ∧
    ∀ ν I x, Reach inst ν I → StopsAt inst I x → IsOptimal inst x := by
  refine ⟨fun ν I h => ?_, fun ν I x _ ⟨u, hopt, hv⟩ => ?_⟩
  · have h1 := mc_reach_card inst h
    have h2 : I.card ≤ m2 * J := by
      have := Finset.card_le_univ I
      simpa [Fintype.card_prod, Fintype.card_fin] using this
    rw [mul_comm]; omega
  · exact ((eq25_core inst).2 x).2 ⟨_, _, (relax_core inst I).2 x u hopt hv⟩

end MulticutLShaped.SimpleRecourse

open MulticutLShaped.SimpleRecourse

variable {n1 m1 m2 J : ℕ}


theorem solution (inst : Instance n1 m1 m2 J) (I : Finset (Fin m2 × Fin J)) :
    (∀ x χ u, Feasible25 inst x χ u →
      MasterFeasible inst I x (fun l => u l.1 l.2) ∧
      masterObj inst I x (fun l => u l.1 l.2) -
          ∑ i, ∑ j, inst.p i j * inst.qminus i j * inst.h i j ≤ obj25 inst x χ u) ∧
    ∀ x u, MasterOptimal inst I x u → violated inst I x = ∅ →
      IsOptimal25 inst x (inst.T.mulVec x) (fun i j => if (i, j) ∈ I then u (i, j) else 0) := by
  exact relax_core inst I
