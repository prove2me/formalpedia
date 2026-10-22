-- Prove2me | solution 1 for HackingInterval.ATE.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T15:08:13.490722+00:00
-- url     : https://prove2.me/submissions/50bd8bc1-956b-42a2-b765-cb75b3055498

import Mathlib
import Definitions.Def_HackingInterval_ATE_Model
open Matrix

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HackingInterval.ATE.E40

open Matrix

section General
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The quadratic form `‖X u‖²`. -/
def q (X : Matrix ι κ ℝ) (u : κ → ℝ) : ℝ := (X *ᵥ u) ⬝ᵥ (X *ᵥ u)

lemma q_nonneg (X : Matrix ι κ ℝ) (u : κ → ℝ) : 0 ≤ q X u := by
  unfold q dotProduct
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

lemma bilin (X : Matrix ι κ ℝ) (u w : κ → ℝ) :
    (X *ᵥ u) ⬝ᵥ (X *ᵥ w) = u ⬝ᵥ ((Xᵀ * X) *ᵥ w) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, dotProduct_comm]

lemma inj_of_det (X : Matrix ι κ ℝ) (hA : IsUnit (Xᵀ * X).det) (u : κ → ℝ)
    (h : X *ᵥ u = 0) : u = 0 := by
  have h2 : (Xᵀ * X) *ᵥ u = 0 := by rw [← mulVec_mulVec, h, mulVec_zero]
  have h3 : (Xᵀ * X)⁻¹ *ᵥ ((Xᵀ * X) *ᵥ u) = u := by
    rw [mulVec_mulVec, nonsing_inv_mul _ hA, one_mulVec]
  rw [← h3, h2, mulVec_zero]

lemma q_eq_zero_imp (X : Matrix ι κ ℝ) (hA : IsUnit (Xᵀ * X).det) (u : κ → ℝ)
    (h : q X u = 0) : u = 0 :=
  inj_of_det X hA u (dotProduct_self_eq_zero.mp h)

lemma q_sub_smul (X : Matrix ι κ ℝ) (u z : κ → ℝ) (s : ℝ) :
    q X (u - s • z) = q X u - 2 * s * ((X *ᵥ u) ⬝ᵥ (X *ᵥ z)) + s ^ 2 * q X z := by
  unfold q
  rw [mulVec_sub, mulVec_smul]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (X *ᵥ z) (X *ᵥ u)]
  ring

lemma q_smul (X : Matrix ι κ ℝ) (z : κ → ℝ) (s : ℝ) : q X (s • z) = s ^ 2 * q X z := by
  unfold q
  rw [mulVec_smul]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

lemma aux_sq (R W : ι → ℝ) (h : R ⬝ᵥ W = 0) :
    (R - W) ⬝ᵥ (R - W) = R ⬝ᵥ R + W ⬝ᵥ W := by
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm W R, h]; ring

lemma loss_eq_dot (D : Design ι κ) (v : κ → ℝ) :
    D.loss v = (D.Y - D.X *ᵥ v) ⬝ᵥ (D.Y - D.X *ᵥ v) := by
  simp only [Design.loss, dotProduct, Pi.sub_apply, sq]

lemma normal_eq (D : Design ι κ) (hA : IsUnit (D.Xᵀ * D.X).det) :
    D.Xᵀ *ᵥ (D.Y - D.X *ᵥ D.betaLS) = 0 := by
  rw [mulVec_sub, mulVec_mulVec, Design.betaLS, mulVec_mulVec, mul_nonsing_inv _ hA,
    one_mulVec, sub_self]

lemma loss_decomp (D : Design ι κ) (hA : IsUnit (D.Xᵀ * D.X).det) (v : κ → ℝ) :
    D.loss v = D.SSE + q D.X (v - D.betaLS) := by
  have h1 : D.Y - D.X *ᵥ v = (D.Y - D.X *ᵥ D.betaLS) - D.X *ᵥ (v - D.betaLS) := by
    rw [mulVec_sub]; abel
  have h2 : (D.Y - D.X *ᵥ D.betaLS) ⬝ᵥ (D.X *ᵥ (v - D.betaLS)) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, normal_eq D hA, zero_dotProduct]
  rw [Design.SSE, loss_eq_dot, loss_eq_dot, h1, aux_sq _ _ h2, q]

lemma ratio_id (Q a V : ℝ) (hV : 0 < V) :
    Q - 2 * (a / V) * a + (a / V) ^ 2 * V = (V * Q - a ^ 2) / V := by
  field_simp
  ring

end General

section Treat
variable {n p : ℕ}

lemma Xt_mulVec (D : TreatData n p) (v : Fin p ⊕ Unit → ℝ) :
    D.Xt *ᵥ v = D.X *ᵥ (fun j => v (Sum.inl j)) + v (Sum.inr ()) • D.ind := by
  ext i
  simp [TreatData.Xt, mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]

lemma XtT_mulVec_inl (D : TreatData n p) (x : Fin n → ℝ) (j : Fin p) :
    (D.Xtᵀ *ᵥ x) (Sum.inl j) = (D.Xᵀ *ᵥ x) j := by
  simp [TreatData.Xt, mulVec, dotProduct, transpose_apply]

lemma loss_full (D : TreatData n p) (β : Fin p → ℝ) (b0 : ℝ) :
    D.loss β b0 = D.full.loss (Sum.elim β (fun _ => b0)) := by
  simp only [TreatData.loss, Design.loss, TreatData.full, Xt_mulVec, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Sum.elim_inl, Sum.elim_inr]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma XtX_isUnit (D : TreatData n p) (hrank : IsUnit (D.Xtᵀ * D.Xt).det) :
    IsUnit (D.Xᵀ * D.X).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨β, hβ, hβ0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hβ
  have hq : q D.X β = 0 := by
    rw [q, bilin, hβ0, dotProduct_zero]
  have hX : D.X *ᵥ β = 0 := dotProduct_self_eq_zero.mp hq
  have hv : D.Xt *ᵥ (Sum.elim β (fun _ => (0:ℝ))) = 0 := by
    rw [Xt_mulVec]
    simp [hX]
  have h0 := inj_of_det D.Xt hrank _ hv
  funext j
  have := congrFun h0 (Sum.inl j)
  simpa using this

/-- `z = (X̃ᵀX̃)⁻¹ e_t`. -/
noncomputable def zt (D : TreatData n p) : Fin p ⊕ Unit → ℝ :=
  (D.Xtᵀ * D.Xt)⁻¹ *ᵥ Pi.single (Sum.inr ()) 1

lemma A_zt (D : TreatData n p) (hrank : IsUnit (D.Xtᵀ * D.Xt).det) :
    (D.Xtᵀ * D.Xt) *ᵥ zt D = Pi.single (Sum.inr ()) 1 := by
  rw [zt, mulVec_mulVec, mul_nonsing_inv _ hrank, one_mulVec]

lemma B_zt (D : TreatData n p) (hrank : IsUnit (D.Xtᵀ * D.Xt).det) (u : Fin p ⊕ Unit → ℝ) :
    (D.Xt *ᵥ u) ⬝ᵥ (D.Xt *ᵥ zt D) = u (Sum.inr ()) := by
  rw [bilin, A_zt D hrank]
  simp

lemma zt_t (D : TreatData n p) : zt D (Sum.inr ()) = D.Vtt := by
  simp [zt, TreatData.Vtt, mulVec]

lemma q_zt (D : TreatData n p) (hrank : IsUnit (D.Xtᵀ * D.Xt).det) :
    q D.Xt (zt D) = D.Vtt := by
  rw [q, B_zt D hrank, zt_t]

lemma Vtt_pos (D : TreatData n p) (hrank : IsUnit (D.Xtᵀ * D.Xt).det) : 0 < D.Vtt := by
  rcases (q_nonneg D.Xt (zt D)).lt_or_eq with h | h
  · rwa [q_zt D hrank] at h
  · exfalso
    have h0 := q_eq_zero_imp D.Xt hrank _ h.symm
    have hA := A_zt D hrank
    rw [h0, mulVec_zero] at hA
    have := congrFun hA (Sum.inr ())
    simp at this

lemma q_sub_zt (D : TreatData n p) (hrank : IsUnit (D.Xtᵀ * D.Xt).det) (u : Fin p ⊕ Unit → ℝ) :
    q D.Xt (u - (u (Sum.inr ()) / D.Vtt) • zt D)
      = (D.Vtt * q D.Xt u - u (Sum.inr ()) ^ 2) / D.Vtt := by
  rw [q_sub_smul, B_zt D hrank, q_zt D hrank, ratio_id _ _ _ (Vtt_pos D hrank)]

lemma cs_bound (D : TreatData n p) (hrank : IsUnit (D.Xtᵀ * D.Xt).det) (u : Fin p ⊕ Unit → ℝ) :
    u (Sum.inr ()) ^ 2 ≤ D.Vtt * q D.Xt u := by
  have hV := Vtt_pos D hrank
  have h := q_nonneg D.Xt (u - (u (Sum.inr ()) / D.Vtt) • zt D)
  rw [q_sub_zt D hrank] at h
  have h' := (le_div_iff₀ hV).mp h
  rw [zero_mul] at h'
  linarith

lemma cs_eq (D : TreatData n p) (hrank : IsUnit (D.Xtᵀ * D.Xt).det) (u : Fin p ⊕ Unit → ℝ)
    (h : D.Vtt * q D.Xt u ≤ u (Sum.inr ()) ^ 2) :
    u = (u (Sum.inr ()) / D.Vtt) • zt D := by
  have hV := Vtt_pos D hrank
  have h1 : q D.Xt (u - (u (Sum.inr ()) / D.Vtt) • zt D) = 0 := by
    apply le_antisymm _ (q_nonneg _ _)
    rw [q_sub_zt D hrank]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hV.le
  have h2 := q_eq_zero_imp D.Xt hrank _ h1
  exact sub_eq_zero.mp h2

lemma full_loss (D : TreatData n p) (hrank : IsUnit (D.Xtᵀ * D.Xt).det) (v : Fin p ⊕ Unit → ℝ) :
    D.full.loss v = D.SSE + q D.Xt (v - D.betaTildeLS) :=
  loss_decomp D.full hrank v

/-- The candidate optimum `β̃*_LS + (e / V_tt) z`. -/
noncomputable def wv (D : TreatData n p) (e : ℝ) : Fin p ⊕ Unit → ℝ :=
  D.betaTildeLS + (e / D.Vtt) • zt D

lemma wv_t (D : TreatData n p) (hrank : IsUnit (D.Xtᵀ * D.Xt).det) (e : ℝ) :
    wv D e (Sum.inr ()) = D.beta0TildeLS + e := by
  have hV := Vtt_pos D hrank
  simp only [wv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, zt_t, TreatData.beta0TildeLS]
  rw [div_mul_cancel₀ e hV.ne']

lemma wv_loss (D : TreatData n p) (hrank : IsUnit (D.Xtᵀ * D.Xt).det) (θ e : ℝ)
    (he : e ^ 2 = D.Vtt * (θ - D.SSE)) : D.full.loss (wv D e) = θ := by
  have hV := Vtt_pos D hrank
  rw [full_loss D hrank, wv, add_sub_cancel_left, q_smul, q_zt D hrank, div_pow, he]
  field_simp
  ring

lemma feas_bound (D : TreatData n p) (hrank : IsUnit (D.Xtᵀ * D.Xt).det) (θ : ℝ)
    (v : Fin p ⊕ Unit → ℝ) (hv : D.full.loss v ≤ θ) :
    (v (Sum.inr ()) - D.beta0TildeLS) ^ 2 ≤ D.Vtt * (θ - D.SSE) := by
  have hV := Vtt_pos D hrank
  have h := cs_bound D hrank (v - D.betaTildeLS)
  rw [full_loss D hrank] at hv
  have hq : q D.Xt (v - D.betaTildeLS) ≤ θ - D.SSE := by linarith
  calc (v (Sum.inr ()) - D.beta0TildeLS) ^ 2 = (v - D.betaTildeLS) (Sum.inr ()) ^ 2 := rfl
    _ ≤ D.Vtt * q D.Xt (v - D.betaTildeLS) := h
    _ ≤ D.Vtt * (θ - D.SSE) := mul_le_mul_of_nonneg_left hq hV.le

lemma wv_unique (D : TreatData n p) (hrank : IsUnit (D.Xtᵀ * D.Xt).det) (θ e : ℝ)
    (he : e ^ 2 = D.Vtt * (θ - D.SSE)) (v : Fin p ⊕ Unit → ℝ) (hv : D.full.loss v ≤ θ)
    (ht : v (Sum.inr ()) = D.beta0TildeLS + e) : v = wv D e := by
  have hV := Vtt_pos D hrank
  have hut : (v - D.betaTildeLS) (Sum.inr ()) = e := by
    simp only [Pi.sub_apply, ht, TreatData.beta0TildeLS]
    ring
  rw [full_loss D hrank] at hv
  have hq : q D.Xt (v - D.betaTildeLS) ≤ θ - D.SSE := by linarith
  have hu := cs_eq D hrank (v - D.betaTildeLS)
    (by rw [hut, he]; exact mul_le_mul_of_nonneg_left hq hV.le)
  rw [hut] at hu
  have hv' : v = D.betaTildeLS + (v - D.betaTildeLS) := by abel
  rw [hv', hu]
  rfl

lemma wv_inl (D : TreatData n p) (hrank : IsUnit (D.Xtᵀ * D.Xt).det) (e : ℝ) :
    (fun j => wv D e (Sum.inl j)) = D.betaLS - (wv D e (Sum.inr ())) • D.gammaLS := by
  have hX := XtX_isUnit D hrank
  have hbt : D.betaTildeLS = (D.Xtᵀ * D.Xt)⁻¹ *ᵥ (D.Xtᵀ *ᵥ D.Y) := rfl
  have hA : (D.Xtᵀ * D.Xt) *ᵥ wv D e
      = D.Xtᵀ *ᵥ D.Y + (e / D.Vtt) • Pi.single (Sum.inr ()) 1 := by
    rw [wv, mulVec_add, mulVec_smul, A_zt D hrank, hbt, mulVec_mulVec, mul_nonsing_inv _ hrank,
      one_mulVec]
  have hrow : D.Xᵀ *ᵥ (D.Xt *ᵥ wv D e) = D.Xᵀ *ᵥ D.Y := by
    funext j
    have := congrFun hA (Sum.inl j)
    rw [← mulVec_mulVec, XtT_mulVec_inl] at this
    simpa [XtT_mulVec_inl] using this
  rw [Xt_mulVec, mulVec_add, mulVec_mulVec, mulVec_smul] at hrow
  calc (fun j => wv D e (Sum.inl j))
      = (D.Xᵀ * D.X)⁻¹ *ᵥ ((D.Xᵀ * D.X) *ᵥ (fun j => wv D e (Sum.inl j))) := by
        rw [mulVec_mulVec, nonsing_inv_mul _ hX, one_mulVec]
    _ = (D.Xᵀ * D.X)⁻¹ *ᵥ (D.Xᵀ *ᵥ D.Y - wv D e (Sum.inr ()) • (D.Xᵀ *ᵥ D.ind)) := by
        rw [← hrow, add_sub_cancel_right]
    _ = D.betaLS - (wv D e (Sum.inr ())) • D.gammaLS := by
        rw [mulVec_sub, mulVec_smul]
        rfl

lemma pair_eq (D : TreatData n p) (hrank : IsUnit (D.Xtᵀ * D.Xt).det) (e : ℝ) :
    Sum.elim (D.betaLS - (D.beta0TildeLS + e) • D.gammaLS) (fun _ => D.beta0TildeLS + e)
      = wv D e := by
  funext x
  rcases x with j | u
  · have := congrFun (wv_inl D hrank e) j
    rw [this, wv_t D hrank]
    rfl
  · cases u
    rw [wv_t D hrank]
    rfl

theorem part14 (D : TreatData n p) (θ : ℝ) (hrank : IsUnit (D.Xtᵀ * D.Xt).det)
    (hθ : D.SSE ≤ θ) (β : Fin p → ℝ) (b0 : ℝ) :
    D.IsSol14 θ β b0 ↔ β = D.betaMax θ ∧ b0 = D.beta0Max θ := by
  have hV := Vtt_pos D hrank
  have hc0 : 0 ≤ Real.sqrt D.Vtt * Real.sqrt (θ - D.SSE) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hc2 : (Real.sqrt D.Vtt * Real.sqrt (θ - D.SSE)) ^ 2 = D.Vtt * (θ - D.SSE) := by
    rw [mul_pow, Real.sq_sqrt hV.le, Real.sq_sqrt (sub_nonneg.mpr hθ)]
  have hW : Sum.elim (D.betaMax θ) (fun _ => D.beta0Max θ)
      = wv D (Real.sqrt D.Vtt * Real.sqrt (θ - D.SSE)) := pair_eq D hrank _
  have hWloss := wv_loss D hrank θ _ hc2
  have bound : ∀ v, D.full.loss v ≤ θ → v (Sum.inr ()) ≤ D.beta0Max θ := by
    intro v hv
    have h := feas_bound D hrank θ v hv
    rw [← hc2] at h
    have := (abs_le_of_sq_le_sq' h hc0).2
    simp only [TreatData.beta0Max]
    linarith
  constructor
  · rintro ⟨hfeas, hopt⟩
    rw [loss_full] at hfeas
    have h1 : b0 ≤ D.beta0Max θ := bound _ hfeas
    have h2 : D.beta0Max θ ≤ b0 :=
      hopt (D.betaMax θ) (D.beta0Max θ) (by rw [loss_full, hW, hWloss])
    have hb : b0 = D.beta0Max θ := le_antisymm h1 h2
    have hv := wv_unique D hrank θ _ hc2 _ hfeas hb
    rw [← hW] at hv
    refine ⟨?_, hb⟩
    funext j
    exact congrFun hv (Sum.inl j)
  · rintro ⟨rfl, rfl⟩
    refine ⟨by rw [loss_full, hW, hWloss], fun β' b0' h' => ?_⟩
    rw [loss_full] at h'
    exact bound _ h'

theorem part15 (D : TreatData n p) (θ : ℝ) (hrank : IsUnit (D.Xtᵀ * D.Xt).det)
    (hθ : D.SSE ≤ θ) (β : Fin p → ℝ) (b0 : ℝ) :
    D.IsSol15 θ β b0 ↔ β = D.betaMin θ ∧ b0 = D.beta0Min θ := by
  have hV := Vtt_pos D hrank
  have hc0 : 0 ≤ Real.sqrt D.Vtt * Real.sqrt (θ - D.SSE) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hc2 : (Real.sqrt D.Vtt * Real.sqrt (θ - D.SSE)) ^ 2 = D.Vtt * (θ - D.SSE) := by
    rw [mul_pow, Real.sq_sqrt hV.le, Real.sq_sqrt (sub_nonneg.mpr hθ)]
  have hc2' : (-(Real.sqrt D.Vtt * Real.sqrt (θ - D.SSE))) ^ 2 = D.Vtt * (θ - D.SSE) := by
    rw [neg_sq, hc2]
  have hmin : D.beta0Min θ = D.beta0TildeLS + -(Real.sqrt D.Vtt * Real.sqrt (θ - D.SSE)) := by
    simp only [TreatData.beta0Min]
    ring
  have hW : Sum.elim (D.betaMin θ) (fun _ => D.beta0Min θ)
      = wv D (-(Real.sqrt D.Vtt * Real.sqrt (θ - D.SSE))) := by
    rw [← pair_eq D hrank _, ← hmin]
    rfl
  have hWloss := wv_loss D hrank θ _ hc2'
  have bound : ∀ v, D.full.loss v ≤ θ → D.beta0Min θ ≤ v (Sum.inr ()) := by
    intro v hv
    have h := feas_bound D hrank θ v hv
    rw [← hc2] at h
    have := (abs_le_of_sq_le_sq' h hc0).1
    simp only [TreatData.beta0Min]
    linarith
  constructor
  · rintro ⟨hfeas, hopt⟩
    rw [loss_full] at hfeas
    have h1 : D.beta0Min θ ≤ b0 := bound _ hfeas
    have h2 : b0 ≤ D.beta0Min θ :=
      hopt (D.betaMin θ) (D.beta0Min θ) (by rw [loss_full, hW, hWloss])
    have hb : b0 = D.beta0Min θ := le_antisymm h2 h1
    have hv := wv_unique D hrank θ _ hc2' _ hfeas (by rw [← hmin]; exact hb)
    rw [← hW] at hv
    refine ⟨?_, hb⟩
    funext j
    exact congrFun hv (Sum.inl j)
  · rintro ⟨rfl, rfl⟩
    refine ⟨by rw [loss_full, hW, hWloss], fun β' b0' h' => ?_⟩
    rw [loss_full] at h'
    exact bound _ h'

end Treat

end HackingInterval.ATE.E40

open HackingInterval.ATE Matrix in
theorem solution {n p : ℕ} (D : TreatData n p) (θ : ℝ)
    (hrank : IsUnit (D.Xtᵀ * D.Xt).det) (hθ : D.SSE ≤ θ) :
    (∀ (β : Fin p → ℝ) (b0 : ℝ),
      D.IsSol14 θ β b0 ↔ β = D.betaMax θ ∧ b0 = D.beta0Max θ) ∧
    (∀ (β : Fin p → ℝ) (b0 : ℝ),
      D.IsSol15 θ β b0 ↔ β = D.betaMin θ ∧ b0 = D.beta0Min θ) := by
  exact ⟨HackingInterval.ATE.E40.part14 D θ hrank hθ, HackingInterval.ATE.E40.part15 D θ hrank hθ⟩
