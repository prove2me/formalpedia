-- Prove2me | solution 1 for KoanaKPaths.Main.recursive_sketch_step_moments
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:28:33.08598+00:00
-- url     : https://prove2.me/submissions/c6f91cb0-af56-42ed-9d36-485ac57834b4

import Theorems.Thm_KoanaKPaths_Main_fixed_matrix_sketching_moments

open scoped BigOperators Classical
noncomputable section
namespace KoanaKPaths.Main.SketchStep

lemma mean_const {Ω : Type} [Fintype Ω] [Nonempty Ω] (a : ℝ) :
    uniformMean (fun _ : Ω => a) = a := by simp [uniformMean]

lemma mean_mul {Ω : Type} [Fintype Ω] (a : ℝ) (f : Ω → ℝ) :
    uniformMean (fun w => a * f w) = a * uniformMean f := by
  simp [uniformMean, ← Finset.mul_sum, mul_div_assoc]

lemma mean_mono {Ω : Type} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ w, f w ≤ g w) :
    uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun w _ => h w) (by positivity)

lemma mean_equiv {Ω A : Type} [Fintype Ω] [Fintype A] (e : Ω ≃ A) (f : A → ℝ) :
    uniformMean (fun w => f (e w)) = uniformMean f := by
  unfold uniformMean
  rw [e.sum_comp, Fintype.card_congr e]

lemma mean_prod {Ω A : Type} [Fintype Ω] [Fintype A] (f : Ω × A → ℝ) :
    uniformMean f = uniformMean (fun w : Ω => uniformMean (fun a : A => f (w,a))) := by
  simp only [uniformMean,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,← Finset.sum_div]
  ring

lemma mean_reseed {Ω A : Type} [Fintype Ω] [Fintype A] [Nonempty A]
    (read : Ω → A) (write : Ω → A → Ω)
    (hr : ∀ w a, read (write w a) = a)
    (hw : ∀ w a b, write (write w a) b = write w b)
    (ho : ∀ w, write w (read w) = w) (f : Ω → ℝ) :
    uniformMean f = uniformMean (fun w : Ω => uniformMean (fun a : A => f (write w a))) := by
  let swap : Ω × A → Ω × A := fun z => (write z.1 z.2, read z.1)
  have hi : Function.Involutive swap := by
    intro z
    apply Prod.ext
    · change write (write z.1 z.2) (read z.1) = z.1
      rw [hw,ho]
    · exact hr _ _
  let e : Ω × A ≃ Ω × A := ⟨swap,swap,hi,hi⟩
  calc
    uniformMean f = uniformMean (fun z : Ω × A => f z.1) := by
      rw [mean_prod]
      simp only [mean_const]
    _ = uniformMean (fun z : Ω × A => f (write z.1 z.2)) := by
      exact (mean_equiv e (fun z => f z.1)).symm
    _ = _ := mean_prod _

lemma fixed_moments_general {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] (ℓ : ℕ) (X : I → J → ℝ) :
    uniformMean (fun R : Fin ℓ → I → Bool =>
      ∑ a : Fin ℓ, ∑ b : J, (∑ u : I, (sgn (R a u) : ℝ) * X u b)^2) =
        (ℓ : ℝ) * (∑ u : I, ∑ b : J, (X u b)^2) ∧
    uniformMean (fun R : Fin ℓ → I → Bool =>
      (∑ a : Fin ℓ, ∑ b : J, (∑ u : I, (sgn (R a u) : ℝ) * X u b)^2)^2) ≤
        ((ℓ : ℝ)^2+2*ℓ) * (∑ u : I, ∑ b : J, (X u b)^2)^2 := by
  classical
  let ei := Fintype.equivFin I
  let ej := Fintype.equivFin J
  let eR : (Fin ℓ → I → Bool) ≃ (Fin ℓ → Fin (Fintype.card I) → Bool) :=
    Equiv.piCongrRight (fun _ => Equiv.arrowCongr ei (Equiv.refl Bool))
  let XF : Fin (Fintype.card I) → Fin (Fintype.card J) → ℝ := fun u b => X (ei.symm u) (ej.symm b)
  have hin (R : Fin ℓ → I → Bool) (a : Fin ℓ) (b : Fin (Fintype.card J)) :
      (∑ u : Fin (Fintype.card I), (sgn (eR R a u) : ℝ) * XF u b) =
        ∑ u : I, (sgn (R a u) : ℝ) * X u (ej.symm b) := by
    exact ei.symm.sum_comp (fun u => (sgn (R a u) : ℝ) * X u (ej.symm b))
  have hout (R : Fin ℓ → I → Bool) :
      realFrobSq (signMul (eR R) XF) =
        ∑ a : Fin ℓ, ∑ b : J, (∑ u : I, (sgn (R a u) : ℝ) * X u b)^2 := by
    unfold realFrobSq signMul
    simp_rw [hin]
    apply Finset.sum_congr rfl
    intro a _
    exact ej.symm.sum_comp (fun b : J => (∑ u : I, (sgn (R a u) : ℝ) * X u b)^2)
  have hx : realFrobSq XF = ∑ u : I, ∑ b : J, (X u b)^2 := by
    unfold realFrobSq XF
    calc
      _ = ∑ u : Fin (Fintype.card I), ∑ b : J, (X (ei.symm u) b)^2 := by
        apply Finset.sum_congr rfl
        intro u _
        exact ej.symm.sum_comp (fun b : J => (X (ei.symm u) b)^2)
      _ = _ := ei.symm.sum_comp (fun u : I => ∑ b : J, (X u b)^2)
  have h := fixed_matrix_sketching_moments ℓ (Fintype.card I) (Fintype.card J) XF
  have hm1 := mean_equiv eR (fun R => realFrobSq (signMul R XF))
  have hm2 := mean_equiv eR (fun R => realFrobSq (signMul R XF)^2)
  simp_rw [hout] at hm1 hm2
  rw [hx] at h
  exact ⟨hm1.trans h.1, hm2.le.trans h.2⟩


def residSplit {n k i : ℕ} (hi : i < k) : Resid n k i ≃ Fin n × Resid n k (i+1) where
  toFun ρ := (ρ ⟨⟨i,hi⟩,le_rfl⟩, fun r => ρ ⟨r.val, by have := r.property; omega⟩)
  invFun p := extendResid p.2 p.1
  left_inv := by
    intro ρ
    funext r
    dsimp [extendResid]
    split_ifs with h
    · congr 1
      apply Subtype.ext
      apply Fin.ext
      exact h.symm
    · rfl
  right_inv := by
    intro p
    apply Prod.ext
    · simp [extendResid]
    · funext r
      have hne : r.val.val ≠ i := by have := r.property; omega
      simp [extendResid,hne]

def fullWordEquiv {n k : ℕ} : Resid n k 0 ≃ (Fin k → Fin n) where
  toFun := fullWord
  invFun τ := fun r => τ r.val
  left_inv := by intro ρ; funext r; rfl
  right_inv := by intro τ; rfl

lemma split_sum {n k i : ℕ} (hi : i < k) (f : Resid n k i → ℝ) :
    (∑ j : Fin n, ∑ ρ : Resid n k (i+1), f (extendResid ρ j)) = ∑ ρ : Resid n k i, f ρ := by
  have h := (residSplit (n := n) hi).symm.sum_comp f
  simpa only [Fintype.sum_prod_type, residSplit, Equiv.coe_fn_mk, Equiv.symm_mk] using h

lemma initial_flat_norm {n k : ℕ} (hk : 0 < k) (c : (Fin k → Fin n) → ℤ) (σ : Labels n k) :
    (∑ j : Fin n, ∑ ρ : Resid n k 1, (Psi c σ (fullWord (extendResid ρ j)) : ℝ)^2) =
      (psiFrobSq c σ : ℝ) := by
  rw [split_sum hk (fun ρ => (Psi c σ (fullWord ρ) : ℝ)^2)]
  have h := (fullWordEquiv (n := n) (k := k)).sum_comp (fun τ => (Psi c σ τ : ℝ)^2)
  simp only [psiFrobSq,Int.cast_sum,Int.cast_pow]
  change (∑ ρ : Resid n k 0, (Psi c σ (fullWord ρ) : ℝ)^2) =
    (∑ τ : Fin k → Fin n, (Psi c σ τ : ℝ)^2) at h
  exact h

lemma later_flat_norm {n k ℓ i : ℕ} (hi : i+1 < k)
    (A : Fin ℓ → Resid n k (i+1) → ℤ) :
    (∑ u : Fin ℓ × Fin n, ∑ ρ : Resid n k (i+2), (A u.1 (extendResid ρ u.2) : ℝ)^2) =
      ∑ b : Fin ℓ, ∑ ρ : Resid n k (i+1), (A b ρ : ℝ)^2 := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  exact split_sum hi (fun ρ => (A b ρ : ℝ)^2)

lemma sketch_update_later {n k ℓ : ℕ} (c : (Fin k → Fin n) → ℤ) (σ : Labels n k)
    (R : SketchSigns n k ℓ) (j : Fin (k-1)) (r : Fin ℓ → Fin ℓ × Fin n → Bool)
    (i : ℕ) (hi : i ≤ j.val) :
    sketch c σ (R.1,Function.update R.2 j r) i = sketch c σ R i := by
  classical
  induction i with
  | zero => rfl
  | succ i ih =>
    funext a ρ
    unfold sketch
    split_ifs with h
    · have hne : (⟨i,h⟩ : Fin (k-1)) ≠ j := by intro he; have := Fin.mk.inj he; omega
      simp only [Prod.snd,Function.update_of_ne hne]
      have heq := ih (by omega)
      simp_rw [heq]
    · rfl


lemma first_conditional {n k ℓ : ℕ} (hk : 0 < k)
    (c : (Fin k → Fin n) → ℤ) (σ : Labels n k)
    (R2 : Fin (k-1) → Fin ℓ → Fin ℓ × Fin n → Bool) :
    uniformMean (fun r : Fin ℓ → Fin n → Bool => (sketchFrobSq c σ (r,R2) 1 : ℝ)) =
        (ℓ : ℝ) * (psiFrobSq c σ : ℝ) ∧
      uniformMean (fun r : Fin ℓ → Fin n → Bool => (sketchFrobSq c σ (r,R2) 1 : ℝ)^2) ≤
        ((ℓ : ℝ)^2+2*ℓ) * (psiFrobSq c σ : ℝ)^2 := by
  have h := fixed_moments_general ℓ (fun j : Fin n => fun ρ : Resid n k 1 =>
    (Psi c σ (fullWord (extendResid ρ j)) : ℝ))
  rw [initial_flat_norm hk c σ] at h
  have heq (r : Fin ℓ → Fin n → Bool) :
      (sketchFrobSq c σ (r,R2) 1 : ℝ) =
        ∑ a : Fin ℓ, ∑ ρ : Resid n k 1,
          (∑ j : Fin n, (sgn (r a j) : ℝ) * (Psi c σ (fullWord (extendResid ρ j)) : ℝ))^2 := by
    change ((∑ a : Fin ℓ, ∑ ρ : Resid n k 1,
      (∑ j : Fin n, sgn (r a j) * Psi c σ (fullWord (extendResid ρ j)))^2 : ℤ) : ℝ) = _
    simp only [Int.cast_sum,Int.cast_pow,Int.cast_mul]
  simp_rw [heq]
  exact h

lemma later_conditional {n k ℓ : ℕ} (i : ℕ) (hi : i+1 < k)
    (c : (Fin k → Fin n) → ℤ) (σ : Labels n k) (R : SketchSigns n k ℓ) :
    uniformMean (fun r : Fin ℓ → Fin ℓ × Fin n → Bool =>
      (sketchFrobSq c σ (R.1,Function.update R.2 ⟨i,by omega⟩ r) (i+2) : ℝ)) =
        (ℓ : ℝ) * (sketchFrobSq c σ R (i+1) : ℝ) ∧
      uniformMean (fun r : Fin ℓ → Fin ℓ × Fin n → Bool =>
        (sketchFrobSq c σ (R.1,Function.update R.2 ⟨i,by omega⟩ r) (i+2) : ℝ)^2) ≤
        ((ℓ : ℝ)^2+2*ℓ) * (sketchFrobSq c σ R (i+1) : ℝ)^2 := by
  have hik : i < k-1 := by omega
  have h := fixed_moments_general ℓ
    (fun u : Fin ℓ × Fin n => fun ρ : Resid n k (i+2) =>
      (sketch c σ R i u.1 (extendResid ρ u.2) : ℝ))
  rw [later_flat_norm hi] at h
  have heq (r : Fin ℓ → Fin ℓ × Fin n → Bool) :
      (sketchFrobSq c σ (R.1,Function.update R.2 ⟨i,hik⟩ r) (i+2) : ℝ) =
        ∑ a : Fin ℓ, ∑ ρ : Resid n k (i+2),
          (∑ u : Fin ℓ × Fin n, (sgn (r a u) : ℝ) *
            (sketch c σ R i u.1 (extendResid ρ u.2) : ℝ))^2 := by
    simp only [sketchFrobSq,sketch,dif_pos hik,Prod.snd,Function.update_self]
    simp_rw [sketch_update_later c σ R ⟨i,hik⟩ r i le_rfl]
    simp only [Int.cast_sum,Int.cast_pow,Int.cast_mul,Fintype.sum_prod_type]
  simp_rw [heq]
  simpa only [sketchFrobSq,Int.cast_sum,Int.cast_pow] using h

lemma unnormalized_step {n k ℓ : ℕ} (c : (Fin k → Fin n) → ℤ) (i : ℕ) (hi : i < k) :
    uniformMean (fun w : Labels n k × SketchSigns n k ℓ =>
      (sketchFrobSq c w.1 w.2 (i+1) : ℝ)) =
        (ℓ : ℝ) * uniformMean (fun w : Labels n k × SketchSigns n k ℓ =>
          (sketchFrobSq c w.1 w.2 i : ℝ)) ∧
      uniformMean (fun w : Labels n k × SketchSigns n k ℓ =>
        (sketchFrobSq c w.1 w.2 (i+1) : ℝ)^2) ≤
        ((ℓ : ℝ)^2+2*ℓ) * uniformMean (fun w : Labels n k × SketchSigns n k ℓ =>
          (sketchFrobSq c w.1 w.2 i : ℝ)^2) := by
  classical
  cases i with
  | zero =>
    let read : Labels n k × SketchSigns n k ℓ → (Fin ℓ → Fin n → Bool) := fun w => w.2.1
    let write : (Labels n k × SketchSigns n k ℓ) → (Fin ℓ → Fin n → Bool) →
        Labels n k × SketchSigns n k ℓ := fun w r => (w.1,(r,w.2.2))
    have hr : ∀ w r, read (write w r) = r := by intros; rfl
    have hw : ∀ w r s, write (write w r) s = write w s := by intros; rfl
    have ho : ∀ w, write w (read w) = w := by intro w; rfl
    constructor
    · rw [mean_reseed read write hr hw ho]
      have hcond (w : Labels n k × SketchSigns n k ℓ) :
          uniformMean (fun r : Fin ℓ → Fin n → Bool =>
            (sketchFrobSq c (write w r).1 (write w r).2 1 : ℝ)) =
            (ℓ : ℝ) * (psiFrobSq c w.1 : ℝ) := (first_conditional hi c w.1 w.2.2).1
      simp_rw [hcond]
      exact mean_mul _ _
    · rw [mean_reseed read write hr hw ho]
      calc
        _ ≤ uniformMean (fun w : Labels n k × SketchSigns n k ℓ =>
            ((ℓ : ℝ)^2+2*ℓ) * (psiFrobSq c w.1 : ℝ)^2) :=
          mean_mono (fun w => (first_conditional hi c w.1 w.2.2).2)
        _ = _ := mean_mul _ _
  | succ i =>
    have hik : i < k-1 := by omega
    let idx : Fin (k-1) := ⟨i,hik⟩
    let read : Labels n k × SketchSigns n k ℓ → (Fin ℓ → Fin ℓ × Fin n → Bool) := fun w => w.2.2 idx
    let write : (Labels n k × SketchSigns n k ℓ) → (Fin ℓ → Fin ℓ × Fin n → Bool) →
        Labels n k × SketchSigns n k ℓ := fun w r => (w.1,(w.2.1,Function.update w.2.2 idx r))
    have hr : ∀ w r, read (write w r) = r := by intros; simp [read,write]
    have hw : ∀ w r s, write (write w r) s = write w s := by intros; simp [write]
    have ho : ∀ w, write w (read w) = w := by intro w; simp [write,read]
    constructor
    · rw [mean_reseed read write hr hw ho]
      have hcond (w : Labels n k × SketchSigns n k ℓ) :
          uniformMean (fun r : Fin ℓ → Fin ℓ × Fin n → Bool =>
            (sketchFrobSq c (write w r).1 (write w r).2 (i+2) : ℝ)) =
            (ℓ : ℝ) * (sketchFrobSq c w.1 w.2 (i+1) : ℝ) := (later_conditional i hi c w.1 w.2).1
      simp_rw [hcond]
      exact mean_mul _ _
    · rw [mean_reseed read write hr hw ho]
      calc
        _ ≤ uniformMean (fun w : Labels n k × SketchSigns n k ℓ =>
            ((ℓ : ℝ)^2+2*ℓ) * (sketchFrobSq c w.1 w.2 (i+1) : ℝ)^2) :=
          mean_mono (fun w => (later_conditional i hi c w.1 w.2).2)
        _ = _ := mean_mul _ _

end KoanaKPaths.Main.SketchStep

theorem solution (n k ℓ : ℕ)
    (c : (Fin k → Fin n) → ℤ) (i : ℕ) (hi : i < k) :
    KoanaKPaths.Main.uniformMean (fun w : KoanaKPaths.Main.Labels n k × KoanaKPaths.Main.SketchSigns n k ℓ =>
      (KoanaKPaths.Main.sketchFrobSq c w.1 w.2 (i+1) : ℝ)) =
        (ℓ : ℝ) * KoanaKPaths.Main.uniformMean (fun w : KoanaKPaths.Main.Labels n k × KoanaKPaths.Main.SketchSigns n k ℓ =>
          (KoanaKPaths.Main.sketchFrobSq c w.1 w.2 i : ℝ)) ∧
      KoanaKPaths.Main.uniformMean (fun w : KoanaKPaths.Main.Labels n k × KoanaKPaths.Main.SketchSigns n k ℓ =>
        (KoanaKPaths.Main.sketchFrobSq c w.1 w.2 (i+1) : ℝ)^2) ≤
        ((ℓ : ℝ)^2+2*ℓ) * KoanaKPaths.Main.uniformMean (fun w : KoanaKPaths.Main.Labels n k × KoanaKPaths.Main.SketchSigns n k ℓ =>
          (KoanaKPaths.Main.sketchFrobSq c w.1 w.2 i : ℝ)^2) := by
  exact KoanaKPaths.Main.SketchStep.unnormalized_step c i hi
