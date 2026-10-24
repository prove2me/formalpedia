-- Prove2me | solution 1 for GoldfarbIdnani.DualQP.theorem_3_dual_algorithm_terminates
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T02:15:13.788853+00:00
-- url     : https://prove2.me/submissions/1d9c5e73-e662-4530-b762-d981e8511ffd

import Mathlib
import Definitions.Def_GoldfarbIdnani_DualQP_Algorithm

set_option autoImplicit false

namespace GI1bca

open Matrix GoldfarbIdnani.DualQP

variable {n m : ℕ}

lemma Nmat_mulVec (C : Matrix (Fin n) (Fin m) ℝ) (A : Finset (Fin m)) (w : A → ℝ) :
    Nmat C A *ᵥ w = ∑ i : A, w i • normal C i := by
  ext k
  simp [Nmat, normal, mulVec, dotProduct, Finset.sum_apply, mul_comm]

lemma sum_multVec (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ)
    (A : Finset (Fin m)) (v : Fin n → ℝ) :
    ∑ i ∈ A, multVec G C A v i • normal C i = Nmat C A *ᵥ (Nstar G C A *ᵥ v) := by
  rw [Nmat_mulVec, ← Finset.sum_coe_sort A]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [multVec, i.2]

lemma G_mul_inv {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) : G * G⁻¹ = 1 :=
  Matrix.mul_nonsing_inv G ((Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit)

lemma G_mul_H {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (C : Matrix (Fin n) (Fin m) ℝ)
    (A : Finset (Fin m)) : G * Hmat G C A = 1 - Nmat C A * Nstar G C A := by
  have h1 := G_mul_inv hG
  unfold Hmat Nstar
  simp only [Matrix.mul_sub, ← Matrix.mul_assoc, h1, Matrix.one_mul]

lemma G_H_mulVec {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (C : Matrix (Fin n) (Fin m) ℝ)
    (A : Finset (Fin m)) (v : Fin n → ℝ) :
    G *ᵥ (Hmat G C A *ᵥ v) = v - ∑ i ∈ A, multVec G C A v i • normal C i := by
  rw [sum_multVec, mulVec_mulVec, G_mul_H hG, sub_mulVec, one_mulVec, mulVec_mulVec]

lemma M_posDef {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (C : Matrix (Fin n) (Fin m) ℝ)
    (A : Finset (Fin m)) (hA : LinIndep C A) :
    ((Nmat C A)ᵀ * G⁻¹ * Nmat C A).PosDef := by
  have hinj : Function.Injective (Nmat C A).mulVec := Matrix.mulVec_injective_iff.mpr hA
  have := hG.inv.conjTranspose_mul_mul_same hinj
  simpa [conjTranspose_eq_transpose_of_trivial] using this

lemma NT_H {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (C : Matrix (Fin n) (Fin m) ℝ)
    (A : Finset (Fin m)) (hA : LinIndep C A) : (Nmat C A)ᵀ * Hmat G C A = 0 := by
  have hM := M_posDef hG C A hA
  have h1 : (Nmat C A)ᵀ * G⁻¹ * Nmat C A * ((Nmat C A)ᵀ * G⁻¹ * Nmat C A)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM.isUnit)
  unfold Hmat
  simp only [Matrix.mul_sub, ← Matrix.mul_assoc, h1, Matrix.one_mul, sub_self]

lemma normal_dot_H {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (C : Matrix (Fin n) (Fin m) ℝ)
    (A : Finset (Fin m)) (hA : LinIndep C A) (v : Fin n → ℝ) (i : Fin m) (hi : i ∈ A) :
    normal C i ⬝ᵥ (Hmat G C A *ᵥ v) = 0 := by
  have h : ((Nmat C A)ᵀ *ᵥ (Hmat G C A *ᵥ v)) ⟨i, hi⟩ = 0 := by
    rw [mulVec_mulVec, NT_H hG C A hA, zero_mulVec]; rfl
  exact h

lemma GT_eq {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) : Gᵀ = G := by
  have := hG.1
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this

lemma G_symm {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (u v : Fin n → ℝ) :
    u ⬝ᵥ (G *ᵥ v) = v ⬝ᵥ (G *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, GT_eq hG, dotProduct_comm]

lemma quad_nonneg {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (z : Fin n → ℝ) :
    0 ≤ z ⬝ᵥ (G *ᵥ z) := by
  by_cases hz : z = 0
  · simp [hz]
  · have := hG.dotProduct_mulVec_pos hz
    simp only [star_trivial] at this
    exact this.le

lemma quad_pos {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (z : Fin n → ℝ) (hz : z ≠ 0) :
    0 < z ⬝ᵥ (G *ᵥ z) := by
  have := hG.dotProduct_mulVec_pos hz
  simpa only [star_trivial] using this

lemma grad_add (a : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (x z : Fin n → ℝ) (t : ℝ) :
    grad a G (x + t • z) = grad a G x + t • (G *ᵥ z) := by
  unfold grad
  rw [mulVec_add, mulVec_smul]
  abel

lemma f_add {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (a : Fin n → ℝ) (x d : Fin n → ℝ) :
    f a G (x + d) = f a G x + grad a G x ⬝ᵥ d + 1 / 2 * (d ⬝ᵥ (G *ᵥ d)) := by
  simp only [f, grad, mulVec_add, dotProduct_add, add_dotProduct]
  rw [G_symm hG x d, dotProduct_comm (G *ᵥ x) d]
  ring

lemma slack_add (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (x z : Fin n → ℝ) (t : ℝ)
    (i : Fin m) : slack C b (x + t • z) i = slack C b x i + t * (normal C i ⬝ᵥ z) := by
  unfold slack
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring

lemma sum_smul_dot (A : Finset (Fin m)) (c : Fin m → ℝ) (v : Fin m → Fin n → ℝ)
    (d : Fin n → ℝ) : (∑ i ∈ A, c i • v i) ⬝ᵥ d = ∑ i ∈ A, c i * (v i ⬝ᵥ d) := by
  rw [sum_dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_dotProduct, smul_eq_mul]

lemma LinIndep_mono (C : Matrix (Fin n) (Fin m) ℝ) {A B : Finset (Fin m)} (hA : LinIndep C A)
    (hBA : B ⊆ A) : LinIndep C B := by
  have h : LinearIndepOn ℝ (normal C) (A : Set (Fin m)) := hA
  have h2 : LinearIndepOn ℝ (normal C) (B : Set (Fin m)) := h.mono (by exact_mod_cast hBA)
  exact h2

/-- Step invariant. -/
def Inv (a : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin m → ℝ) : State n m → Prop
  | .step1 x A u => LinIndep C A ∧ (∀ i ∈ A, slack C b x i = 0) ∧ (∀ i ∈ A, 0 ≤ u i) ∧
      grad a G x = ∑ i ∈ A, u i • normal C i
  | .step2 x A p u => LinIndep C A ∧ p ∉ A ∧ (∀ i ∈ A, slack C b x i = 0) ∧
      slack C b x p < 0 ∧ (∀ i ∈ A, 0 ≤ u i) ∧ 0 ≤ u p ∧
      grad a G x = ∑ i ∈ A, u i • normal C i + u p • normal C p
  | .stopOptimal x => IsOptimal a G C b x
  | .stopInfeasible => ∀ y, ¬ Feasible C b y

lemma inv_init {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (a : Fin n → ℝ)
    (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) : Inv a G C b (initState a G) := by
  refine ⟨?_, by simp, by simp, ?_⟩
  · have h : LinearIndepOn ℝ (normal C) ((∅ : Finset (Fin m)) : Set (Fin m)) := by
      rw [Finset.coe_empty]; exact linearIndepOn_empty ℝ _
    exact h
  · simp only [grad, Finset.sum_empty, mulVec_neg, mulVec_mulVec, G_mul_inv hG, one_mulVec,
      neg_add_cancel]

/-- the gradient after a dual step -/
lemma grad_step (a : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ)
    (A : Finset (Fin m)) (p : Fin m) (x z : Fin n → ℝ) (u r : Fin m → ℝ) (t : ℝ)
    (hg : grad a G x = ∑ i ∈ A, u i • normal C i + u p • normal C p)
    (hGz : G *ᵥ z = normal C p - ∑ i ∈ A, r i • normal C i) :
    grad a G (x + t • z) = ∑ i ∈ A, (u i - t * r i) • normal C i + (u p + t) • normal C p := by
  rw [grad_add, hg, hGz]
  simp only [sub_smul, add_smul, mul_smul, Finset.sum_sub_distrib, smul_sub, Finset.smul_sum]
  abel

lemma nonneg_step (u r : Fin m → ℝ) (A : Finset (Fin m)) (t : ℝ) (ht0 : 0 ≤ t)
    (ht : ∀ j ∈ A, 0 < r j → t ≤ u j / r j) (i : Fin m) (hi : i ∈ A) (hu : 0 ≤ u i) :
    0 ≤ u i - t * r i := by
  by_cases hr : 0 < r i
  · have := ht i hi hr
    rw [le_div_iff₀ hr] at this
    linarith
  · push Not at hr
    nlinarith

lemma t1_nonneg (A : Finset (Fin m)) (u r : Fin m → ℝ) (k : Fin m) (hk : IsT1Argmin A u r k)
    (hu : ∀ i ∈ A, 0 ≤ u i) : 0 ≤ u k / r k :=
  div_nonneg (hu k hk.1) hk.2.1.le

/-- Key facts in a Step-2 state. -/
lemma key_facts {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (C : Matrix (Fin n) (Fin m) ℝ)
    (A : Finset (Fin m)) (hA : LinIndep C A) (p : Fin m) :
    G *ᵥ (Hmat G C A *ᵥ normal C p) =
        normal C p - ∑ i ∈ A, multVec G C A (normal C p) i • normal C i ∧
    (∀ i ∈ A, normal C i ⬝ᵥ (Hmat G C A *ᵥ normal C p) = 0) ∧
    (Hmat G C A *ᵥ normal C p) ⬝ᵥ normal C p =
      (Hmat G C A *ᵥ normal C p) ⬝ᵥ (G *ᵥ (Hmat G C A *ᵥ normal C p)) := by
  have h1 := G_H_mulVec hG C A (normal C p)
  have h2 := normal_dot_H hG C A hA (normal C p)
  refine ⟨h1, h2, ?_⟩
  rw [h1, dotProduct_sub, dotProduct_sum]
  have : ∑ i ∈ A, (Hmat G C A *ᵥ normal C p) ⬝ᵥ
      (multVec G C A (normal C p) i • normal C i) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [dotProduct_smul, dotProduct_comm, h2 i hi, smul_zero]
  rw [this, sub_zero]

lemma inv_step {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (a : Fin n → ℝ)
    (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) {s s' : State n m}
    (hs : Inv a G C b s) (h : Step a G C b s s') : Inv a G C b s' := by
  cases h with
  | step1_stop x A u hV =>
    obtain ⟨_, hsl, hu, hg⟩ := hs
    have hfeas : Feasible C b x := by
      intro i
      by_cases hi : i ∈ A
      · rw [hsl i hi]
      · exact hV i hi
    refine ⟨hfeas, fun y hy => ?_⟩
    have key := f_add hG a x (y - x)
    rw [add_sub_cancel] at key
    have hq := quad_nonneg hG (y - x)
    have hlin : 0 ≤ grad a G x ⬝ᵥ (y - x) := by
      rw [hg, sum_smul_dot]
      refine Finset.sum_nonneg (fun i hi => ?_)
      have : normal C i ⬝ᵥ (y - x) = slack C b y i - slack C b x i := by
        unfold slack; rw [dotProduct_sub]; ring
      rw [this, hsl i hi]
      exact mul_nonneg (hu i hi) (by linarith [hy i])
    linarith
  | step1_choose x A u p hpA hp =>
    obtain ⟨hli, hsl, hu, hg⟩ := hs
    refine ⟨hli, hpA, hsl, hp, fun i hi => ?_, ?_, ?_⟩
    · simp only [restrict, if_pos hi]; exact hu i hi
    · simp [restrict, hpA]
    · rw [hg]
      simp only [restrict, if_neg hpA, zero_smul, add_zero]
      exact Finset.sum_congr rfl (fun i hi => by rw [if_pos hi])
  | step2_infeasible x A p u hr hz =>
    obtain ⟨hli, hpA, hsl, hp, hu, hup, hg⟩ := hs
    intro y hy
    obtain ⟨h1, -, -⟩ := key_facts hG C A hli p
    rw [hz, mulVec_zero] at h1
    have hnp : normal C p = ∑ i ∈ A, multVec G C A (normal C p) i • normal C i :=
      (sub_eq_zero.mp h1.symm)
    have hy' := hy p
    have hx' := hp
    unfold slack at hy' hx'
    rw [hnp, sum_smul_dot] at hy' hx'
    have hle : ∑ i ∈ A, multVec G C A (normal C p) i * (normal C i ⬝ᵥ y) ≤
        ∑ i ∈ A, multVec G C A (normal C p) i * (normal C i ⬝ᵥ x) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      have h1 := hy i
      have h2 := hsl i hi
      unfold slack at h1 h2
      exact mul_le_mul_of_nonpos_left (by linarith) (hr i hi)
    linarith
  | step2_dual x A p u k hz hk =>
    obtain ⟨hli, hpA, hsl, hp, hu, hup, hg⟩ := hs
    obtain ⟨h1, -, -⟩ := key_facts hG C A hli p
    set r := multVec G C A (normal C p) with hr_def
    set t := u k / r k with ht_def
    have ht0 : 0 ≤ t := t1_nonneg A u r k hk hu
    have hgs := grad_step a G C A p x (Hmat G C A *ᵥ normal C p) u r t hg h1
    rw [hz, smul_zero, add_zero] at hgs
    have hkA : k ∈ A := hk.1
    have hpE : p ∉ A.erase k := fun h => hpA (Finset.mem_of_mem_erase h)
    have hval : ∀ i ∈ A.erase k, restrict (insert p (A.erase k)) (dualStep u r p t) i =
        u i - t * r i := by
      intro i hi
      have hip : i ≠ p := fun h => hpE (h ▸ hi)
      simp [restrict, dualStep, hi, hip]
    have hvalp : restrict (insert p (A.erase k)) (dualStep u r p t) p = u p + t := by
      simp [restrict, dualStep]
    refine ⟨LinIndep_mono C hli (Finset.erase_subset k A), hpE,
      fun i hi => hsl i (Finset.mem_of_mem_erase hi), hp, fun i hi => ?_, ?_, ?_⟩
    · rw [hval i hi]
      exact nonneg_step u r A t ht0 (fun j hj hrj => hk.2.2 j hj hrj) i
        (Finset.mem_of_mem_erase hi) (hu i (Finset.mem_of_mem_erase hi))
    · rw [hvalp]; linarith
    · rw [hgs, hvalp]
      congr 1
      rw [← Finset.sum_erase A (a := k) (by
        rw [ht_def, div_mul_cancel₀ _ hk.2.1.ne', sub_self, zero_smul])]
      exact Finset.sum_congr rfl (fun i hi => by rw [hval i hi])
  | step2_full x A p u hz ht =>
    obtain ⟨hli, hpA, hsl, hp, hu, hup, hg⟩ := hs
    obtain ⟨h1, h2, h3⟩ := key_facts hG C A hli p
    set r := multVec G C A (normal C p) with hr_def
    set z := Hmat G C A *ᵥ normal C p with hz_def
    set c := z ⬝ᵥ normal C p with hc_def
    have hc : 0 < c := by rw [h3]; exact quad_pos hG z hz
    set t := -slack C b x p / c with ht_def
    have htpos : 0 < t := div_pos (by linarith) hc
    have hgs := grad_step a G C A p x z u r t hg h1
    refine ⟨?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
    · -- linear independence of insert p A
      have hspan : normal C p ∉ Submodule.span ℝ (normal C '' (A : Set (Fin m))) := by
        intro hmem
        have hall : ∀ v ∈ Submodule.span ℝ (normal C '' (A : Set (Fin m))), z ⬝ᵥ v = 0 := by
          intro v hv
          induction hv using Submodule.span_induction with
          | mem v hv =>
            obtain ⟨i, hi, rfl⟩ := hv
            rw [dotProduct_comm]; exact h2 i hi
          | zero => simp
          | add u v _ _ hu hv => rw [dotProduct_add, hu, hv, add_zero]
          | smul c v _ hv => rw [dotProduct_smul, hv, smul_zero]
        have hzero := hall _ hmem
        rw [← hc_def] at hzero
        linarith
      have hli' : LinearIndepOn ℝ (normal C) (A : Set (Fin m)) := hli
      have h4 : LinearIndepOn ℝ (normal C) (insert p (A : Set (Fin m))) :=
        (linearIndepOn_insert (by simpa using hpA)).mpr ⟨hli', hspan⟩
      have h5 : LinearIndepOn ℝ (normal C) ((insert p A : Finset (Fin m)) : Set (Fin m)) := by
        rw [Finset.coe_insert]; exact h4
      exact h5
    · rw [slack_add]
      rcases Finset.mem_insert.mp hi with rfl | hiA
      · rw [dotProduct_comm, ← hc_def, ht_def]
        field_simp
        ring
      · rw [hsl i hiA, h2 i hiA, mul_zero, add_zero]
    · rcases Finset.mem_insert.mp hi with rfl | hiA
      · unfold dualStep; rw [if_pos rfl]; linarith
      · have hip : i ≠ p := fun h => hpA (h ▸ hiA)
        simp only [dualStep, if_neg hip]
        exact nonneg_step u r A t htpos.le ht i hiA (hu i hiA)
    · rw [hgs, Finset.sum_insert hpA]
      unfold dualStep
      rw [if_pos rfl, add_comm]
      congr 1
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hip : i ≠ p := fun h => hpA (h ▸ hi)
      rw [if_neg hip]
  | step2_partial x A p u k hz hk ht =>
    obtain ⟨hli, hpA, hsl, hp, hu, hup, hg⟩ := hs
    obtain ⟨h1, h2, h3⟩ := key_facts hG C A hli p
    set r := multVec G C A (normal C p) with hr_def
    set z := Hmat G C A *ᵥ normal C p with hz_def
    set c := z ⬝ᵥ normal C p with hc_def
    have hc : 0 < c := by rw [h3]; exact quad_pos hG z hz
    set t := u k / r k with ht_def
    have ht0 : 0 ≤ t := t1_nonneg A u r k hk hu
    have hgs := grad_step a G C A p x z u r t hg h1
    have hkA : k ∈ A := hk.1
    have hpE : p ∉ A.erase k := fun h => hpA (Finset.mem_of_mem_erase h)
    have hval : ∀ i ∈ A.erase k, restrict (insert p (A.erase k)) (dualStep u r p t) i =
        u i - t * r i := by
      intro i hi
      have hip : i ≠ p := fun h => hpE (h ▸ hi)
      simp [restrict, dualStep, hi, hip]
    have hvalp : restrict (insert p (A.erase k)) (dualStep u r p t) p = u p + t := by
      simp [restrict, dualStep]
    refine ⟨LinIndep_mono C hli (Finset.erase_subset k A), hpE,
      fun i hi => ?_, ?_, fun i hi => ?_, ?_, ?_⟩
    · rw [slack_add, hsl i (Finset.mem_of_mem_erase hi), h2 i (Finset.mem_of_mem_erase hi),
        mul_zero, add_zero]
    · rw [slack_add, dotProduct_comm, ← hc_def]
      have := (lt_div_iff₀ hc).mp ht
      linarith
    · rw [hval i hi]
      exact nonneg_step u r A t ht0 (fun j hj hrj => hk.2.2 j hj hrj) i
        (Finset.mem_of_mem_erase hi) (hu i (Finset.mem_of_mem_erase hi))
    · rw [hvalp]; linarith
    · rw [hgs, hvalp]
      congr 1
      rw [← Finset.sum_erase A (a := k) (by
        rw [ht_def, div_mul_cancel₀ _ hk.2.1.ne', sub_self, zero_smul])]
      exact Finset.sum_congr rfl (fun i hi => by rw [hval i hi])

noncomputable def Fv (a : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ) : State n m → ℝ
  | .step1 x _ _ => f a G x
  | .step2 x _ _ _ => f a G x
  | _ => 0

def IsS1 (s : State n m) : Prop := ∃ x A u, s = State.step1 x A u
def IsS2 (s : State n m) : Prop := ∃ x A p u, s = State.step2 x A p u

def rk : State n m → ℕ
  | .step2 _ A _ _ => A.card + 1
  | _ => 0

def getA : State n m → Finset (Fin m)
  | .step1 _ A _ => A
  | _ => ∅

lemma f_step_mono {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (a : Fin n → ℝ)
    (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) (A : Finset (Fin m))
    (p : Fin m) (u : Fin m → ℝ) (hs : Inv a G C b (State.step2 x A p u)) (t : ℝ) (ht : 0 ≤ t) :
    f a G x ≤ f a G (x + t • (Hmat G C A *ᵥ normal C p)) ∧
    (0 < t → Hmat G C A *ᵥ normal C p ≠ 0 →
      f a G x < f a G (x + t • (Hmat G C A *ᵥ normal C p))) := by
  obtain ⟨hli, hpA, hsl, hp, hu, hup, hg⟩ := hs
  obtain ⟨h1, h2, h3⟩ := key_facts hG C A hli p
  set z := Hmat G C A *ᵥ normal C p with hz_def
  set c := z ⬝ᵥ normal C p with hc_def
  have hc0 : 0 ≤ c := by rw [h3]; exact quad_nonneg hG z
  have hgz : grad a G x ⬝ᵥ z = u p * c := by
    rw [hg, add_dotProduct, sum_smul_dot,
      Finset.sum_eq_zero (fun i hi => by rw [h2 i hi, mul_zero]), zero_add, smul_dotProduct,
      smul_eq_mul, dotProduct_comm]
  have hq : (t • z) ⬝ᵥ (G *ᵥ (t • z)) = t ^ 2 * c := by
    rw [mulVec_smul, smul_dotProduct, dotProduct_smul, h3, smul_eq_mul, smul_eq_mul]; ring
  have hf : f a G (x + t • z) = f a G x + t * (u p * c) + 1 / 2 * (t ^ 2 * c) := by
    rw [f_add hG, hq, dotProduct_smul, hgz, smul_eq_mul]
  refine ⟨?_, fun htp hz => ?_⟩
  · rw [hf]
    have : 0 ≤ t * (u p * c) := mul_nonneg ht (mul_nonneg hup hc0)
    have : 0 ≤ t ^ 2 * c := mul_nonneg (sq_nonneg t) hc0
    linarith
  · have hc : 0 < c := by rw [h3]; exact quad_pos hG z hz
    rw [hf]
    have : 0 ≤ t * (u p * c) := mul_nonneg ht (mul_nonneg hup hc0)
    have : 0 < t ^ 2 * c := mul_pos (pow_pos htp 2) hc
    linarith

lemma Fv_step {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (a : Fin n → ℝ)
    (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) {s s' : State n m}
    (hs : Inv a G C b s) (h : Step a G C b s s') :
    (IsS2 s' → Fv a G s ≤ Fv a G s') ∧ (IsS1 s' → Fv a G s < Fv a G s') := by
  cases h with
  | step1_stop x A u hV =>
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, _, _, h⟩; cases h
    · rintro ⟨_, _, _, h⟩; cases h
  | step1_choose x A u p hpA hp =>
    refine ⟨fun _ => le_refl _, ?_⟩
    rintro ⟨_, _, _, h⟩; cases h
  | step2_infeasible x A p u hr hz =>
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, _, _, h⟩; cases h
    · rintro ⟨_, _, _, h⟩; cases h
  | step2_dual x A p u k hz hk =>
    refine ⟨fun _ => le_refl _, ?_⟩
    rintro ⟨_, _, _, h⟩; cases h
  | step2_full x A p u hz ht =>
    refine ⟨?_, fun _ => ?_⟩
    · rintro ⟨_, _, _, _, h⟩; cases h
    · have hs' := hs
      obtain ⟨hli, hpA, hsl, hp, hu, hup, hg⟩ := hs'
      obtain ⟨h1, h2, h3⟩ := key_facts hG C A hli p
      have hc : 0 < (Hmat G C A *ᵥ normal C p) ⬝ᵥ normal C p := by
        rw [h3]; exact quad_pos hG _ hz
      have htpos : 0 < -slack C b x p / ((Hmat G C A *ᵥ normal C p) ⬝ᵥ normal C p) :=
        div_pos (by linarith) hc
      exact ((f_step_mono hG a C b x A p u hs _ htpos.le).2 htpos hz)
  | step2_partial x A p u k hz hk ht =>
    refine ⟨fun _ => ?_, ?_⟩
    · have hs' := hs
      obtain ⟨hli, hpA, hsl, hp, hu, hup, hg⟩ := hs'
      exact (f_step_mono hG a C b x A p u hs _ (t1_nonneg A u _ k hk hu)).1
    · rintro ⟨_, _, _, h⟩; cases h

lemma step_src {a : Fin n → ℝ} {G : Matrix (Fin n) (Fin n) ℝ} {C : Matrix (Fin n) (Fin m) ℝ}
    {b : Fin m → ℝ} {s s' : State n m} (h : Step a G C b s s') : IsS1 s ∨ IsS2 s := by
  cases h <;> first | exact Or.inl ⟨_, _, _, rfl⟩ | exact Or.inr ⟨_, _, _, _, rfl⟩

lemma rk_lt {a : Fin n → ℝ} {G : Matrix (Fin n) (Fin n) ℝ} {C : Matrix (Fin n) (Fin m) ℝ}
    {b : Fin m → ℝ} {s s' : State n m} (h : Step a G C b s s') (h1 : IsS2 s) (h2 : IsS2 s') :
    rk s' < rk s := by
  cases h with
  | step1_stop x A u hV => obtain ⟨_, _, _, _, h⟩ := h1; cases h
  | step1_choose x A u p hpA hp => obtain ⟨_, _, _, _, h⟩ := h1; cases h
  | step2_infeasible x A p u hr hz => obtain ⟨_, _, _, _, h⟩ := h2; cases h
  | step2_full x A p u hz ht => obtain ⟨_, _, _, _, h⟩ := h2; cases h
  | step2_dual x A p u k hz hk =>
    simp only [rk]; have := Finset.card_erase_lt_of_mem hk.1; omega
  | step2_partial x A p u k hz hk ht =>
    simp only [rk]; have := Finset.card_erase_lt_of_mem hk.1; omega

lemma uniq {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (a : Fin n → ℝ)
    (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (x x' : Fin n → ℝ) (A : Finset (Fin m))
    (u u' : Fin m → ℝ) (h : Inv a G C b (State.step1 x A u))
    (h' : Inv a G C b (State.step1 x' A u')) : x = x' := by
  obtain ⟨_, hsl, _, hg⟩ := h
  obtain ⟨_, hsl', _, hg'⟩ := h'
  have hGd : G *ᵥ (x - x') = ∑ i ∈ A, (u i - u' i) • normal C i := by
    have : G *ᵥ (x - x') = grad a G x - grad a G x' := by
      unfold grad; rw [mulVec_sub]; abel
    rw [this, hg, hg', ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [sub_smul])
  have hq : (x - x') ⬝ᵥ (G *ᵥ (x - x')) = 0 := by
    rw [hGd, dotProduct_comm, sum_smul_dot]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have e1 := hsl i hi
    have e2 := hsl' i hi
    unfold slack at e1 e2
    rw [dotProduct_sub]
    have : normal C i ⬝ᵥ x - normal C i ⬝ᵥ x' = 0 := by linarith
    rw [this, mul_zero]
  by_contra hne
  have := quad_pos hG (x - x') (sub_ne_zero.mpr hne)
  linarith

lemma no_inf {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (a : Fin n → ℝ)
    (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (σ : ℕ → State n m)
    (h0 : σ 0 = initState a G) (hs : ∀ k, Step a G C b (σ k) (σ (k + 1))) : False := by
  have hinv : ∀ k, Inv a G C b (σ k) := by
    intro k
    induction k with
    | zero => rw [h0]; exact inv_init hG a C b
    | succ k ih => exact inv_step hG a C b ih (hs k)
  have hns : ∀ k, IsS1 (σ k) ∨ IsS2 (σ k) := fun k => step_src (hs k)
  have hle : ∀ k, Fv a G (σ k) ≤ Fv a G (σ (k + 1)) := by
    intro k
    rcases hns (k + 1) with h | h
    · exact ((Fv_step hG a C b (hinv k) (hs k)).2 h).le
    · exact (Fv_step hG a C b (hinv k) (hs k)).1 h
  have hmono : Monotone (fun k => Fv a G (σ k)) := monotone_nat_of_le_succ hle
  have hstrict : ∀ i j, i < j → IsS1 (σ j) → Fv a G (σ i) < Fv a G (σ j) := by
    intro i j hij hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact lt_of_le_of_lt (hmono (by omega : i ≤ j')) ((Fv_step hG a C b (hinv j') (hs j')).2 hj)
  have H : ∀ N k, rk (σ k) = N → ∃ j, k ≤ j ∧ IsS1 (σ j) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro k hk
      rcases hns k with h | h
      · exact ⟨k, le_rfl, h⟩
      · rcases hns (k + 1) with h' | h'
        · exact ⟨k + 1, by omega, h'⟩
        · have hlt := rk_lt (hs k) h h'
          obtain ⟨j, hj, hj1⟩ := ih _ (hk ▸ hlt) (k + 1) rfl
          exact ⟨j, by omega, hj1⟩
  have hex : ∀ k, ∃ j ∈ {j | IsS1 (σ j)}, k < j := by
    intro k
    obtain ⟨j, hj, hj1⟩ := H _ (k + 1) rfl
    exact ⟨j, hj1, by omega⟩
  have hSinf : ({j | IsS1 (σ j)} : Set ℕ).Infinite := Set.infinite_of_forall_exists_gt hex
  obtain ⟨i, hi, j, hj, hij, heq⟩ := hSinf.exists_ne_map_eq_of_mapsTo
    (f := fun k => getA (σ k)) (Set.mapsTo_univ _ _) Set.finite_univ
  have key : ∀ i j, i < j → IsS1 (σ i) → IsS1 (σ j) → getA (σ i) = getA (σ j) → False := by
    intro i j hij hi hj heq
    have hlt := hstrict i j hij hj
    obtain ⟨x, A, u, hxi⟩ := hi
    obtain ⟨x', A', u', hxj⟩ := hj
    have hAi := hinv i
    have hAj := hinv j
    rw [hxi] at hAi hlt heq
    rw [hxj] at hAj hlt heq
    simp only [getA] at heq
    subst heq
    have hxx := uniq hG a C b x x' A u u' hAi hAj
    simp only [Fv] at hlt
    rw [hxx] at hlt
    exact lt_irrefl _ hlt
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hi hj heq
  · exact key j i h hj hi heq.symm

lemma exists_step1 (a : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (A : Finset (Fin m)) (u : Fin m → ℝ) :
    ∃ s', Step a G C b (State.step1 x A u) s' := by
  by_cases hV : ∀ j, j ∉ A → 0 ≤ slack C b x j
  · exact ⟨_, Step.step1_stop x A u hV⟩
  · push Not at hV
    obtain ⟨p, hpA, hp⟩ := hV
    exact ⟨_, Step.step1_choose x A u p hpA hp⟩

lemma argmin_ex (A : Finset (Fin m)) (u r : Fin m → ℝ) (h : ∃ j ∈ A, 0 < r j) :
    ∃ k, IsT1Argmin A u r k := by
  obtain ⟨j, hj, hrj⟩ := h
  have hne : (A.filter (fun j => 0 < r j)).Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, hrj⟩⟩
  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image _ (fun j => u j / r j) hne
  rw [Finset.mem_filter] at hk
  exact ⟨k, hk.1, hk.2, fun j hj hrj => hmin j (Finset.mem_filter.mpr ⟨hj, hrj⟩)⟩

lemma exists_step2 (a : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (A : Finset (Fin m)) (p : Fin m) (u : Fin m → ℝ) :
    ∃ s', Step a G C b (State.step2 x A p u) s' := by
  by_cases hz : Hmat G C A *ᵥ normal C p = 0
  · by_cases hr : ∀ j ∈ A, multVec G C A (normal C p) j ≤ 0
    · exact ⟨_, Step.step2_infeasible x A p u hr hz⟩
    · push Not at hr
      obtain ⟨k, hk⟩ := argmin_ex A u _ hr
      exact ⟨_, Step.step2_dual x A p u k hz hk⟩
  · by_cases ht : ∀ j ∈ A, 0 < multVec G C A (normal C p) j →
        -slack C b x p / ((Hmat G C A *ᵥ normal C p) ⬝ᵥ normal C p) ≤
          u j / multVec G C A (normal C p) j
    · exact ⟨_, Step.step2_full x A p u hz ht⟩
    · push Not at ht
      obtain ⟨j, hj, hrj, hlt⟩ := ht
      obtain ⟨k, hk⟩ := argmin_ex A u _ ⟨j, hj, hrj⟩
      exact ⟨_, Step.step2_partial x A p u k hz hk (lt_of_le_of_lt (hk.2.2 j hj hrj) hlt)⟩

end GI1bca

open GoldfarbIdnani.DualQP Matrix in
theorem solution {n m : ℕ} (a : Fin n → ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ)
    (hG : G.PosDef) :
    (¬ ∃ σ : ℕ → State n m, σ 0 = initState a G ∧ ∀ k, Step a G C b (σ k) (σ (k + 1))) ∧
    (∀ s : State n m, Relation.ReflTransGen (Step a G C b) (initState a G) s →
      (∀ s', ¬ Step a G C b s s') →
      (∃ x, s = State.stopOptimal x ∧ IsOptimal a G C b x) ∨
        (s = State.stopInfeasible ∧ ∀ y, ¬ Feasible C b y)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨σ, h0, hs⟩
    exact GI1bca.no_inf hG a C b σ h0 hs
  · intro s hreach
    have hinv : GI1bca.Inv a G C b s := by
      induction hreach with
      | refl => exact GI1bca.inv_init hG a C b
      | tail _ hst ih => exact GI1bca.inv_step hG a C b ih hst
    intro hno
    cases s with
    | step1 x A u =>
      obtain ⟨s', h⟩ := GI1bca.exists_step1 a G C b x A u
      exact absurd h (hno s')
    | step2 x A p u =>
      obtain ⟨s', h⟩ := GI1bca.exists_step2 a G C b x A p u
      exact absurd h (hno s')
    | stopOptimal x => exact Or.inl ⟨x, rfl, hinv⟩
    | stopInfeasible => exact Or.inr ⟨rfl, hinv⟩
