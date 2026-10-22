-- Prove2me | solution 1 for ModernConvex.Truss.compliance_cqr
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:50:47.685336+00:00
-- url     : https://prove2.me/submissions/cdadd28d-8718-4c06-97fe-fc1e572e8336

import Mathlib
import Definitions.Def_ModernConvex_Truss_Compliance

open Matrix ModernConvex.Truss

lemma g70mc1_range {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsHermitian) (f : Fin m → ℝ)
    (hf : ∀ w, A *ᵥ w = 0 → f ⬝ᵥ w = 0) : ∃ v, A *ᵥ v = f := by
  have hT : (Matrix.toEuclideanLin A).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.2 hA
  have hF : WithLp.toLp 2 f ∈ LinearMap.range (Matrix.toEuclideanLin A) := by
    rw [← Submodule.orthogonal_orthogonal (LinearMap.range (Matrix.toEuclideanLin A)),
      hT.orthogonal_range, Submodule.mem_orthogonal]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have h1 : A *ᵥ WithLp.ofLp u = 0 := by
      have := congrArg WithLp.ofLp hu
      simpa using this
    simpa using hf _ h1
  obtain ⟨V, hV⟩ := hF
  refine ⟨WithLp.ofLp V, ?_⟩
  have := congrArg WithLp.ofLp hV
  simpa using this

lemma g70mc1_stiff_mulVec {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (v : Fin m → ℝ) :
    stiffness B t *ᵥ v = ∑ i, t i • (B i *ᵥ ((B i)ᵀ *ᵥ v)) := by
  simp [stiffness, sum_mulVec, smul_mulVec, mulVec_mulVec]

lemma g70mc1_dot_B {m k : ℕ} (B : Matrix (Fin m) (Fin k) ℝ) (w : Fin m → ℝ) (y : Fin k → ℝ) :
    w ⬝ᵥ (B *ᵥ y) = (Bᵀ *ᵥ w) ⬝ᵥ y := by
  rw [dotProduct_mulVec, mulVec_transpose]

lemma g70mc1_quad {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (w : Fin m → ℝ) :
    w ⬝ᵥ (stiffness B t *ᵥ w) = ∑ i, t i * (((B i)ᵀ *ᵥ w) ⬝ᵥ ((B i)ᵀ *ᵥ w)) := by
  rw [g70mc1_stiff_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotProduct_smul, g70mc1_dot_B, smul_eq_mul]

lemma g70mc1_herm {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) :
    (stiffness B t).IsHermitian := by
  unfold IsHermitian stiffness
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_smul, conjTranspose_mul]
  simp [conjTranspose_eq_transpose_of_trivial]

lemma g70mc1_nn {k : ℕ} (x : Fin k → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

lemma g70mc1_La {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (f : Fin m → ℝ)
    (h : ∃ v : Fin m → ℝ, stiffness B t *ᵥ v = f) :
    ∃ s : (i : Fin n) → Fin (k i) → ℝ, ∑ i, B i *ᵥ s i = f ∧ (∀ i, t i = 0 → s i = 0) ∧
      compliance B f t = ((∑ i, (s i ⬝ᵥ s i) / (2 * t i) : ℝ) : EReal) := by
  unfold compliance
  rw [dif_pos h]
  have hv := h.choose_spec
  set v := h.choose
  refine ⟨fun i => t i • ((B i)ᵀ *ᵥ v), ?_, ?_, ?_⟩
  · rw [← hv, g70mc1_stiff_mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mulVec_smul]
  · intro i hi; simp [hi]
  · have e : ∑ i, ((t i • ((B i)ᵀ *ᵥ v)) ⬝ᵥ (t i • ((B i)ᵀ *ᵥ v))) / (2 * t i)
        = (1 / 2 : ℝ) * (f ⬝ᵥ v) := by
      rw [← hv, dotProduct_comm, g70mc1_quad, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
      rcases eq_or_ne (t i) 0 with h0 | h0
      · simp [h0]
      · field_simp
    rw [EReal.coe_eq_coe_iff]; exact e.symm

lemma g70mc1_Lb {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (ht : 0 ≤ t)
    (f : Fin m → ℝ) (s : (i : Fin n) → Fin (k i) → ℝ) (hs : ∑ i, B i *ᵥ s i = f)
    (hs0 : ∀ i, t i = 0 → s i = 0) :
    compliance B f t ≤ ((∑ i, (s i ⬝ᵥ s i) / (2 * t i) : ℝ) : EReal) := by
    set A := stiffness B t
    have hsol : ∃ v, A *ᵥ v = f := by
      apply g70mc1_range A (g70mc1_herm B t) f
      intro w hw
      have hq : ∑ i, t i * (((B i)ᵀ *ᵥ w) ⬝ᵥ ((B i)ᵀ *ᵥ w)) = 0 := by
        rw [← g70mc1_quad, hw, dotProduct_zero]
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
        mul_nonneg (ht i) (g70mc1_nn ((B i)ᵀ *ᵥ w)))).1 hq
      rw [← hs, dotProduct_comm, dotProduct_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [g70mc1_dot_B]
      rcases eq_or_ne (t i) 0 with h0 | h0
      · rw [hs0 i h0, dotProduct_zero]
      · have := hz i hi
        have hw0 : (B i)ᵀ *ᵥ w = 0 :=
          dotProduct_self_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h0)
        rw [hw0, zero_dotProduct]
    unfold compliance
    rw [dif_pos hsol]
    have hv := hsol.choose_spec
    set v := hsol.choose
    rw [EReal.coe_le_coe_iff]
    have h1 : f ⬝ᵥ v = ∑ i, s i ⬝ᵥ ((B i)ᵀ *ᵥ v) := by
      rw [← hs, sum_dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [dotProduct_comm, g70mc1_dot_B, dotProduct_comm]
    have h2 : f ⬝ᵥ v = ∑ i, t i * (((B i)ᵀ *ᵥ v) ⬝ᵥ ((B i)ᵀ *ᵥ v)) := by
      rw [← hv, dotProduct_comm, g70mc1_quad]
    have h3 : ∀ i, s i ⬝ᵥ ((B i)ᵀ *ᵥ v) ≤
        (s i ⬝ᵥ s i) / (2 * t i) + t i * (((B i)ᵀ *ᵥ v) ⬝ᵥ ((B i)ᵀ *ᵥ v)) / 2 := by
      intro i
      set w := (B i)ᵀ *ᵥ v
      rcases eq_or_ne (t i) 0 with h0 | h0
      · simp [hs0 i h0, h0]
      · have htp : 0 < t i := lt_of_le_of_ne (ht i) (Ne.symm h0)
        have hsq := g70mc1_nn (s i - t i • w)
        simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
          smul_eq_mul] at hsq
        rw [dotProduct_comm w (s i)] at hsq
        rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
        nlinarith
    have h4 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h3 i
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← h2, ← h1] at h4
    linarith

theorem g70mc1_part1 {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (f : Fin m → ℝ) (τ : ℝ) :
    extendedCompliance B f t ≤ (τ : EReal) ↔
        ∃ s : (i : Fin n) → Fin (k i) → ℝ,
          ∑ i, B i *ᵥ s i = f ∧
          ((∀ i, t i = 0 → s i = 0) ∧ ∑ i, (s i ⬝ᵥ s i) / (2 * t i) ≤ τ) ∧
          0 ≤ t := by
  unfold extendedCompliance
  by_cases ht : 0 ≤ t
  · rw [if_pos ht]
    constructor
    · intro hc
      have hsol : ∃ v : Fin m → ℝ, stiffness B t *ᵥ v = f := by
        by_contra hno
        unfold compliance at hc; rw [dif_neg hno] at hc; simp at hc
      obtain ⟨s, hs, hs0, he⟩ := g70mc1_La B t f hsol
      rw [he, EReal.coe_le_coe_iff] at hc
      exact ⟨s, hs, ⟨hs0, hc⟩, ht⟩
    · rintro ⟨s, hs, ⟨hs0, hle⟩, _⟩
      exact (g70mc1_Lb B t ht f s hs hs0).trans (EReal.coe_le_coe_iff.2 hle)
  · rw [if_neg ht]
    simp only [top_le_iff, EReal.coe_ne_top, false_iff, not_exists, not_and]
    intro s _ _ h; exact ht h

lemma g70mc1_lin_mat {κ ρ : Type} [Fintype κ] [DecidableEq κ] [Fintype ρ]
    (g : (κ → ℝ) → (ρ → ℝ)) (hadd : ∀ v w, g (v + w) = g v + g w)
    (hsmul : ∀ (a : ℝ) v, g (a • v) = a • g v) : ∃ A : Matrix ρ κ ℝ, ∀ v, A *ᵥ v = g v := by
  let L : (κ → ℝ) →ₗ[ℝ] (ρ → ℝ) := ⟨⟨g, hadd⟩, hsmul⟩
  exact ⟨LinearMap.toMatrix' L, fun v => by rw [LinearMap.toMatrix'_mulVec]; rfl⟩

lemma g70mc1_sumpad (h : ℕ → ℝ) (K P : ℕ) (hK : K ≤ P) (hz : ∀ c, K ≤ c → h c = 0) :
    ∑ c : Fin P, h c = ∑ c : Fin K, h c := by
  rw [Fin.sum_univ_eq_sum_range h P, Fin.sum_univ_eq_sum_range h K]
  exact (Finset.sum_subset (Finset.range_subset_range.2 hK)
    (fun c _ hc => hz c (by simpa using hc))).symm

section CQ
variable {n m : ℕ} {k : Fin n → ℕ}

abbrev g70mc1_ι (k : Fin n → ℕ) : Type := (Σ i, Fin (k i)) ⊕ Fin n

noncomputable def g70mc1_e (k : Fin n → ℕ) : g70mc1_ι k ≃ Fin (Fintype.card (g70mc1_ι k)) :=
  Fintype.equivFin _

abbrev g70mc1_V (n m : ℕ) (k : Fin n → ℕ) : Type :=
  ((Fin n ⊕ Fin m) ⊕ Unit) ⊕ Fin (Fintype.card (g70mc1_ι k))

def g70mc1_T (v : g70mc1_V n m k → ℝ) (i : Fin n) : ℝ := v (Sum.inl (Sum.inl (Sum.inl i)))
def g70mc1_F (v : g70mc1_V n m k → ℝ) (j : Fin m) : ℝ := v (Sum.inl (Sum.inl (Sum.inr j)))
def g70mc1_tau (v : g70mc1_V n m k → ℝ) : ℝ := v (Sum.inl (Sum.inr ()))
noncomputable def g70mc1_S (v : g70mc1_V n m k → ℝ) (i : Fin n) (c : Fin (k i)) : ℝ :=
  v (Sum.inr (g70mc1_e k (Sum.inl ⟨i, c⟩)))
noncomputable def g70mc1_Sg (v : g70mc1_V n m k → ℝ) (i : Fin n) : ℝ :=
  v (Sum.inr (g70mc1_e k (Sum.inr i)))

noncomputable def g70mc1_rot (v : g70mc1_V n m k → ℝ) (i : Fin n) (c : ℕ) : ℝ :=
  if hc : c < k i then Real.sqrt 2 * g70mc1_S v i ⟨c, hc⟩
  else if c = k i then g70mc1_T v i - g70mc1_Sg v i else 0

noncomputable def g70mc1_eqc (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ)
    (v : g70mc1_V n m k → ℝ) (c : ℕ) : ℝ :=
  if hc : c < m then (∑ i, ∑ c', B i ⟨c, hc⟩ c' * g70mc1_S v i c') - g70mc1_F v ⟨c, hc⟩ else 0

noncomputable def g70mc1_g (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (P : ℕ)
    (j : Fin (n + 2)) (v : g70mc1_V n m k → ℝ) : Fin (P + 1) ⊕ Unit → ℝ := fun r =>
  match r with
  | Sum.inl c => if h : (j : ℕ) < n then g70mc1_rot v ⟨j, h⟩ c
      else if (j : ℕ) = n then g70mc1_eqc B v c else 0
  | Sum.inr _ => if h : (j : ℕ) < n then g70mc1_T v ⟨j, h⟩ + g70mc1_Sg v ⟨j, h⟩
      else if (j : ℕ) = n then 0 else g70mc1_tau v - ∑ i, g70mc1_Sg v i

lemma g70mc1_g_add (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (P : ℕ) (j : Fin (n + 2))
    (v w : g70mc1_V n m k → ℝ) :
    g70mc1_g B P j (v + w) = g70mc1_g B P j v + g70mc1_g B P j w := by
  ext r
  rcases r with c | _ <;>
  simp only [g70mc1_g, g70mc1_rot, g70mc1_eqc, g70mc1_T, g70mc1_F, g70mc1_tau, g70mc1_S,
    g70mc1_Sg, Pi.add_apply] <;> split_ifs <;>
  (try simp only [mul_add, Finset.sum_add_distrib]) <;> ring

lemma g70mc1_g_smul (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (P : ℕ) (j : Fin (n + 2))
    (a : ℝ) (v : g70mc1_V n m k → ℝ) :
    g70mc1_g B P j (a • v) = a • g70mc1_g B P j v := by
  ext r
  rcases r with c | _ <;>
  simp only [g70mc1_g, g70mc1_rot, g70mc1_eqc, g70mc1_T, g70mc1_F, g70mc1_tau, g70mc1_S,
    g70mc1_Sg, Pi.smul_apply, smul_eq_mul] <;> split_ifs <;>
  (try simp only [Finset.mul_sum, mul_sub, mul_add]) <;> ring_nf <;>
  (congr 1; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

end CQ

section CQ2
variable {n m : ℕ} {k : Fin n → ℕ}

lemma g70mc1_rot_sum (P : ℕ) (hP : ∀ i, k i ≤ P) (v : g70mc1_V n m k → ℝ) (i : Fin n) :
    ∑ c : Fin (P + 1), (g70mc1_rot v i c) ^ 2 =
      2 * (g70mc1_S v i ⬝ᵥ g70mc1_S v i) + (g70mc1_T v i - g70mc1_Sg v i) ^ 2 := by
  rw [g70mc1_sumpad (fun c => (g70mc1_rot v i c) ^ 2) (k i + 1) (P + 1) (by have := hP i; omega)
    (fun c hc => by simp only [g70mc1_rot]; rw [dif_neg (by omega), if_neg (by omega)]; simp)]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, g70mc1_rot, lt_irrefl, dif_neg (lt_irrefl _), dite_false,
    if_true]
  congr 1
  rw [dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [dif_pos c.isLt, mul_pow, Real.sq_sqrt (by norm_num)]
  ring

lemma g70mc1_eqc_sum (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (P : ℕ) (hP : m ≤ P)
    (v : g70mc1_V n m k → ℝ) :
    ∑ c : Fin (P + 1), (g70mc1_eqc B v c) ^ 2 = ∑ c : Fin m, (g70mc1_eqc B v c) ^ 2 :=
  g70mc1_sumpad (fun c => (g70mc1_eqc B v c) ^ 2) m (P + 1) (by omega)
    (fun c hc => by simp only [g70mc1_eqc]; rw [dif_neg (by omega)]; simp)

lemma g70mc1_eqc_val (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ)
    (v : g70mc1_V n m k → ℝ) (c : Fin m) :
    g70mc1_eqc B v c = (∑ i, B i *ᵥ g70mc1_S v i) c - g70mc1_F v c := by
  simp only [g70mc1_eqc, dif_pos c.isLt, Finset.sum_apply, mulVec, dotProduct]

lemma g70mc1_eqc_zero (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (P : ℕ) (hP : m ≤ P)
    (v : g70mc1_V n m k → ℝ) :
    Real.sqrt (∑ c : Fin (P + 1), (g70mc1_eqc B v c) ^ 2) ≤ 0 ↔
      ∑ i, B i *ᵥ g70mc1_S v i = g70mc1_F v := by
  rw [g70mc1_eqc_sum B P hP, Real.sqrt_le_left le_rfl, sq, mul_zero]
  constructor
  · intro h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (f := fun c : Fin m => (g70mc1_eqc B v (c : ℕ)) ^ 2) (fun c _ => sq_nonneg _)).1
      (le_antisymm h (Finset.sum_nonneg fun c _ => sq_nonneg _))
    ext c
    have := hz c (Finset.mem_univ _)
    rw [g70mc1_eqc_val] at this
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  · intro h
    refine le_of_eq (Finset.sum_eq_zero fun c _ => ?_)
    rw [g70mc1_eqc_val, h, sub_self]; simp

end CQ2

lemma g70mc1_key {n m : ℕ} {k : Fin n → ℕ} (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ)
    (P : ℕ) (hPk : ∀ i, k i ≤ P) (hPm : m ≤ P) (v : g70mc1_V n m k → ℝ) :
    (∀ j : Fin (n + 2), g70mc1_g B P j v ∈ lorentzCone (Fin (P + 1))) ↔
      (∀ i, Real.sqrt (2 * (g70mc1_S v i ⬝ᵥ g70mc1_S v i) + (g70mc1_T v i - g70mc1_Sg v i) ^ 2)
          ≤ g70mc1_T v i + g70mc1_Sg v i) ∧
      ∑ i, B i *ᵥ g70mc1_S v i = g70mc1_F v ∧ 0 ≤ g70mc1_tau v - ∑ i, g70mc1_Sg v i := by
  simp only [lorentzCone, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_, ?_⟩
    · have := h ⟨i, by omega⟩
      simp only [g70mc1_g, dif_pos i.isLt] at this
      rwa [g70mc1_rot_sum P hPk] at this
    · have := h ⟨n, by omega⟩
      simp only [g70mc1_g, lt_irrefl, dif_neg (lt_irrefl n), if_true] at this
      exact (g70mc1_eqc_zero B P hPm v).1 this
    · have := h ⟨n + 1, by omega⟩
      simp only [g70mc1_g, dif_neg (show ¬ (n + 1 < n) by omega),
        if_neg (show ¬ (n + 1 = n) by omega)] at this
      simpa using this
  · rintro ⟨hrot, heq, hsum⟩ j
    rcases Nat.lt_or_ge (j : ℕ) n with hj | hj
    · simp only [g70mc1_g, dif_pos hj]
      rw [g70mc1_rot_sum P hPk]; exact hrot _
    · rcases eq_or_ne (j : ℕ) n with hj' | hj'
      · simp only [g70mc1_g, dif_neg (show ¬ ((j : ℕ) < n) by omega), if_pos hj']
        exact (g70mc1_eqc_zero B P hPm v).2 heq
      · simp only [g70mc1_g, dif_neg (show ¬ ((j : ℕ) < n) by omega), if_neg hj']
        simpa using hsum

theorem g70mc1_cqrfun {n m : ℕ} {k : Fin n → ℕ} (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) :
    IsCQrFunction (fun x : Fin n ⊕ Fin m → ℝ =>
      extendedCompliance B (fun j => x (Sum.inr j)) (fun i => x (Sum.inl i))) := by
  classical
  set P := m + ∑ i, k i
  have hPk : ∀ i, k i ≤ P := fun i =>
    le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i))
      (Nat.le_add_left _ _)
  have hPm : m ≤ P := Nat.le_add_right _ _
  have hA := fun j => g70mc1_lin_mat (g70mc1_g B P j) (g70mc1_g_add B P j) (g70mc1_g_smul B P j)
  have hAs : ∀ j v, (hA j).choose *ᵥ v = g70mc1_g B P j v := fun j => (hA j).choose_spec
  refine ⟨Fintype.card (g70mc1_ι k), n + 2, fun _ => P, fun j => (hA j).choose, fun _ => 0, ?_⟩
  intro z
  simp only [Set.mem_setOf_eq, sub_zero, hAs]
  rw [g70mc1_part1]
  constructor
  · rintro ⟨s, hs, ⟨hs0, hle⟩, ht⟩
    let σ : Fin n → ℝ := fun i => s i ⬝ᵥ s i / (2 * z (Sum.inl (Sum.inl i)))
    let u : Fin (Fintype.card (g70mc1_ι k)) → ℝ := fun l =>
      match (g70mc1_e k).symm l with
      | Sum.inl q => s q.1 q.2
      | Sum.inr i => σ i
    have hS : ∀ i, g70mc1_S (Sum.elim z u) i = s i := by
      intro i; ext c; simp [g70mc1_S, u]
    have hSg : ∀ i, g70mc1_Sg (Sum.elim z u) i = σ i := by
      intro i; simp [g70mc1_Sg, u]
    refine ⟨u, (g70mc1_key B P hPk hPm _).2 ⟨fun i => ?_, ?_, ?_⟩⟩
    · rw [hS, hSg]
      show Real.sqrt (2 * (s i ⬝ᵥ s i) + (z (Sum.inl (Sum.inl i)) - σ i) ^ 2) ≤
        z (Sum.inl (Sum.inl i)) + σ i
      set t := z (Sum.inl (Sum.inl i))
      have hti : 0 ≤ t := ht i
      rcases eq_or_lt_of_le hti with h0 | h0
      · have hs00 := hs0 i h0.symm
        simp [σ, ← h0, hs00]
      · have hσ : σ i = s i ⬝ᵥ s i / (2 * t) := rfl
        have hσ0 : 0 ≤ σ i := div_nonneg (g70mc1_nn _) (by positivity)
        have e : 2 * (s i ⬝ᵥ s i) + (t - σ i) ^ 2 = (t + σ i) ^ 2 := by
          have : 2 * (s i ⬝ᵥ s i) = 4 * t * σ i := by rw [hσ]; field_simp; ring
          nlinarith
        rw [e, Real.sqrt_sq (by linarith)]
    · simp only [hS]; exact hs
    · simp only [hSg]
      show 0 ≤ z (Sum.inr ()) - ∑ i, σ i
      linarith
  · rintro ⟨u, hu⟩
    obtain ⟨hrot, heq, hsum⟩ := (g70mc1_key B P hPk hPm _).1 hu
    set v := Sum.elim z u
    have hTi : ∀ i, g70mc1_T v i = z (Sum.inl (Sum.inl i)) := fun i => rfl
    have hinfo : ∀ i, 0 ≤ g70mc1_T v i ∧ 0 ≤ g70mc1_Sg v i ∧
        2 * (g70mc1_S v i ⬝ᵥ g70mc1_S v i) ≤ 4 * g70mc1_T v i * g70mc1_Sg v i := by
      intro i
      have h := hrot i
      have hy : 0 ≤ g70mc1_T v i + g70mc1_Sg v i := le_trans (Real.sqrt_nonneg _) h
      rw [Real.sqrt_le_left hy] at h
      have hnn := g70mc1_nn (g70mc1_S v i)
      have hts : 0 ≤ g70mc1_T v i * g70mc1_Sg v i := by nlinarith
      refine ⟨?_, ?_, by nlinarith⟩
      · by_contra hc; push Not at hc; nlinarith
      · by_contra hc; push Not at hc; nlinarith
    refine ⟨g70mc1_S v, heq, ⟨fun i hi => ?_, ?_⟩, fun i => (hinfo i).1⟩
    · obtain ⟨_, _, h3⟩ := hinfo i
      rw [hTi, hi] at h3
      exact dotProduct_self_eq_zero.1 (le_antisymm (by linarith) (g70mc1_nn _))
    · have hterm : ∀ i, g70mc1_S v i ⬝ᵥ g70mc1_S v i / (2 * z (Sum.inl (Sum.inl i))) ≤
          g70mc1_Sg v i := by
        intro i
        obtain ⟨h1, h2, h3⟩ := hinfo i
        rw [hTi] at h1 h3
        rcases eq_or_lt_of_le h1 with h0 | h0
        · rw [← h0]; simp; exact h2
        · rw [div_le_iff₀ (by positivity)]; nlinarith
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
      have ht : g70mc1_tau v = z (Sum.inr ()) := rfl
      rw [ht] at hsum
      linarith

theorem solution {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) :
    (∀ (t : Fin n → ℝ) (f : Fin m → ℝ) (τ : ℝ),
      extendedCompliance B f t ≤ (τ : EReal) ↔
        ∃ s : (i : Fin n) → Fin (k i) → ℝ,
          -- (a)
          ∑ i, B i *ᵥ s i = f ∧
          -- (b)
          ((∀ i, t i = 0 → s i = 0) ∧ ∑ i, (s i ⬝ᵥ s i) / (2 * t i) ≤ τ) ∧
          -- (c)
          0 ≤ t) ∧
    IsCQrFunction (fun x : Fin n ⊕ Fin m → ℝ =>
      extendedCompliance B (fun j => x (Sum.inr j)) (fun i => x (Sum.inl i))) := by
  exact ⟨fun t f τ => g70mc1_part1 B t f τ, g70mc1_cqrfun B⟩

