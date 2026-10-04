-- Prove2me | solution 1 for HardyFiveAxioms.transformation_linear
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T03:30:32.566609+00:00
-- url     : https://prove2.me/submissions/523abe8b-97a4-4546-80b4-a7c42249edda

import Mathlib

set_option autoImplicit false

namespace HardyTransfLin5e82

/-- Sub-convex combinations (weights summing to at most one) are respected by `g`. -/
lemma subconvex_map {K : ℕ} {S : Set (Fin K → ℝ)} (hS : Convex ℝ S)
    (h0 : (0 : Fin K → ℝ) ∈ S) {g : (Fin K → ℝ) → (Fin K → ℝ)} (hg0 : g 0 = 0)
    (hmix : ∀ pA ∈ S, ∀ pB ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      g (t • pA + (1 - t) • pB) = t • g pA + (1 - t) • g pB)
    {ι : Type} [Fintype ι] (w : ι → ℝ) (x : ι → (Fin K → ℝ))
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i ≤ 1) (hx : ∀ i, x i ∈ S) :
    g (∑ i, w i • x i) = ∑ i, w i • g (x i) := by
  have hconv : ConvexOn ℝ S g := by
    refine ⟨hS, ?_⟩
    intro a ha b hb s t hs ht hst
    have h := hmix a ha b hb s hs (by linarith)
    rw [show t = 1 - s by linarith]
    exact le_of_eq h
  have hcave : ConcaveOn ℝ S g := by
    refine ⟨hS, ?_⟩
    intro a ha b hb s t hs ht hst
    have h := hmix a ha b hb s hs (by linarith)
    rw [show t = 1 - s by linarith]
    exact le_of_eq h.symm
  let W : Option ι → ℝ := fun o => o.elim (1 - ∑ i, w i) w
  let X : Option ι → (Fin K → ℝ) := fun o => o.elim 0 x
  have hW : ∀ o ∈ (Finset.univ : Finset (Option ι)), 0 ≤ W o := by
    intro o _
    cases o with
    | none => simp only [W, Option.elim]; linarith
    | some i => simp only [W, Option.elim]; exact hw i
  have hW1 : ∑ o ∈ (Finset.univ : Finset (Option ι)), W o = 1 := by
    simp [W, Fintype.sum_option]
  have hX : ∀ o ∈ (Finset.univ : Finset (Option ι)), X o ∈ S := by
    intro o _
    cases o with
    | none => simpa [X] using h0
    | some i => simpa [X] using hx i
  have e1 : ∑ o ∈ (Finset.univ : Finset (Option ι)), W o • X o = ∑ i, w i • x i := by
    simp [W, X, Fintype.sum_option]
  have e2 : ∑ o ∈ (Finset.univ : Finset (Option ι)), W o • g (X o) = ∑ i, w i • g (x i) := by
    simp [W, X, Fintype.sum_option, hg0]
  have A := hconv.map_sum_le hW hW1 hX
  have B := hcave.le_map_sum hW hW1 hX
  rw [e1, e2] at A B
  exact le_antisymm A B

/-- `g` respects arbitrary real linear relations between points of `S`. -/
lemma linear_rel {K : ℕ} {S : Set (Fin K → ℝ)} (hS : Convex ℝ S)
    (h0 : (0 : Fin K → ℝ) ∈ S) {g : (Fin K → ℝ) → (Fin K → ℝ)} (hg0 : g 0 = 0)
    (hmix : ∀ pA ∈ S, ∀ pB ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      g (t • pA + (1 - t) • pB) = t • g pA + (1 - t) • g pB)
    {n : ℕ} (c : Fin n → ℝ) (v : Fin n → (Fin K → ℝ)) (hv : ∀ i, v i ∈ S)
    (p : Fin K → ℝ) (hp : p ∈ S) (hpv : ∑ i, c i • v i = p) :
    g p = ∑ i, c i • g (v i) := by
  set M : ℝ := 1 + ∑ i, |c i| with hM
  have hsabs : 0 ≤ ∑ i, |c i| := Finset.sum_nonneg (fun i _ => abs_nonneg (c i))
  have hMpos : 0 < M := by linarith
  -- left family: p with weight 1/M, v i with weight (|c i| - c i)/(2M)
  let wl : Option (Fin n) → ℝ := fun o => o.elim (1 / M) (fun i => (|c i| - c i) / (2 * M))
  let xl : Option (Fin n) → (Fin K → ℝ) := fun o => o.elim p v
  let wr : Fin n → ℝ := fun i => (|c i| + c i) / (2 * M)
  have hwl : ∀ o, 0 ≤ wl o := by
    intro o
    cases o with
    | none => simp only [wl, Option.elim]; positivity
    | some i =>
      simp only [wl, Option.elim]
      apply div_nonneg _ (by positivity)
      linarith [le_abs_self (c i)]
  have hwr : ∀ i, 0 ≤ wr i := by
    intro i
    simp only [wr]
    apply div_nonneg _ (by positivity)
    linarith [neg_abs_le (c i)]
  have hbound : ∀ i, |c i| - c i ≤ 2 * |c i| ∧ |c i| + c i ≤ 2 * |c i| := by
    intro i
    constructor <;> linarith [le_abs_self (c i), neg_abs_le (c i)]
  have hsl : ∑ o, wl o ≤ 1 := by
    rw [Fintype.sum_option]
    simp only [wl, Option.elim]
    rw [← Finset.sum_div]
    have : ∑ i, (|c i| - c i) ≤ ∑ i, 2 * |c i| :=
      Finset.sum_le_sum (fun i _ => (hbound i).1)
    rw [← Finset.mul_sum] at this
    rw [div_add_div _ _ (ne_of_gt hMpos) (by positivity), div_le_one (by positivity)]
    nlinarith
  have hsr : ∑ i, wr i ≤ 1 := by
    simp only [wr]
    rw [← Finset.sum_div]
    have : ∑ i, (|c i| + c i) ≤ ∑ i, 2 * |c i| :=
      Finset.sum_le_sum (fun i _ => (hbound i).2)
    rw [← Finset.mul_sum] at this
    rw [div_le_one (by positivity)]
    nlinarith
  have hxl : ∀ o, xl o ∈ S := by
    intro o
    cases o with
    | none => exact hp
    | some i => exact hv i
  have hGLs := subconvex_map hS h0 hg0 hmix wl xl hwl hsl hxl
  have hGRs := subconvex_map hS h0 hg0 hmix wr v hwr hsr hv
  rw [Fintype.sum_option, Fintype.sum_option] at hGLs
  simp only [wl, xl, Option.elim] at hGLs
  -- the two combinations are the same vector
  have hvec : (1 / M) • p + ∑ i, ((|c i| - c i) / (2 * M)) • v i = ∑ i, wr i • v i := by
    rw [← hpv]
    funext j
    simp only [wr, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
    ring
  rw [hvec, hGRs] at hGLs
  funext j
  have hj := congrFun hGLs j
  simp only [wr, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
  have key : g p j = M * (∑ i, (|c i| + c i) / (2 * M) * g (v i) j
      - ∑ i, (|c i| - c i) / (2 * M) * g (v i) j) := by
    rw [hj]; field_simp; ring
  rw [key, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp
  ring

end HardyTransfLin5e82

open Matrix in
theorem solution {K : ℕ} (S : Set (Fin K → ℝ)) (hS : Convex ℝ S)
    (h0 : (0 : Fin K → ℝ) ∈ S) (g : (Fin K → ℝ) → (Fin K → ℝ)) (hg0 : g 0 = 0)
    (hmix : ∀ pA ∈ S, ∀ pB ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      g (t • pA + (1 - t) • pB) = t • g pA + (1 - t) • g pB) :
    ∃ Z : Matrix (Fin K) (Fin K) ℝ, ∀ p ∈ S, g p = Z *ᵥ p := by
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℝ S
  have hli' : LinearIndepOn ℝ id b := hli
  let B := Module.Basis.extend hli'
  let L : (Fin K → ℝ) →ₗ[ℝ] (Fin K → ℝ) := B.constr ℝ (fun x => g (x : Fin K → ℝ))
  refine ⟨LinearMap.toMatrix' L, fun p hp => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  have hpb : p ∈ Submodule.span ℝ b := hspan ▸ Submodule.subset_span hp
  obtain ⟨n, c, v, hv⟩ := Submodule.mem_span_set'.mp hpb
  have hLv : ∀ i, L (v i : Fin K → ℝ) = g (v i) := by
    intro i
    have hm : ((v i : Fin K → ℝ)) ∈ hli'.extend (Set.subset_univ b) :=
      Module.Basis.subset_extend hli' (v i).2
    have h := B.constr_basis ℝ (fun x => g (x : Fin K → ℝ)) ⟨v i, hm⟩
    simpa [B, L] using h
  rw [← hv, map_sum]
  simp only [map_smul, hLv]
  exact HardyTransfLin5e82.linear_rel hS h0 hg0 hmix c (fun i => (v i : Fin K → ℝ))
    (fun i => hbS (v i).2) _ (hv ▸ hp) rfl
