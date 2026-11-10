-- Prove2me | solution 1 for IntLInfty.Kan.fillerAt_zero_abs
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:47:08.068214+00:00
-- url     : https://prove2.me/submissions/da8ce91e-963e-47b4-b7d6-7451fac5c9e1

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

set_option autoImplicit false

namespace IntLInfty.Kan.A83Fib

open scoped ContDiff
open Filter Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The fibre operator `T z = DG(z) ∘ π`. -/
noncomputable def Top (G : E → E) (π : E →L[ℝ] E) (z : E) : E →L[ℝ] E :=
  (fderiv ℝ G z).comp π

/-- The fibre inverse `z₀ + (1 - T z₀)⁻¹ u`. -/
noncomputable def fibInv (G : E → E) (π : E →L[ℝ] E) (z0 u : E) : E :=
  z0 + Ring.inverse (1 - Top G π z0) u

theorem Top_pow (G : E → E) (π : E →L[ℝ] E) (hπ : ∀ x, π (π x) = π x)
    (hI : ∀ z v, π v = v → π (fderiv ℝ G z v) = fderiv ℝ G z v) (z : E) (k : ℕ) :
    Top G π z ^ (k + 1) = fderiv ℝ G z ^ (k + 1) * π := by
  have hπD : π * (fderiv ℝ G z * π) = fderiv ℝ G z * π := by
    ext x
    show π (fderiv ℝ G z (π x)) = fderiv ℝ G z (π x)
    exact hI z (π x) (hπ x)
  induction k with
  | zero => rw [zero_add, pow_one, pow_one]; rfl
  | succ k ih =>
    rw [pow_succ, ih, pow_succ (fderiv ℝ G z) (k + 1)]
    show fderiv ℝ G z ^ (k + 1) * π * (fderiv ℝ G z * π) = _
    rw [mul_assoc, hπD, ← mul_assoc]

theorem isUnit_one_sub_Top (G : E → E) (π : E →L[ℝ] E) (hπ : ∀ x, π (π x) = π x)
    (hI : ∀ z v, π v = v → π (fderiv ℝ G z v) = fderiv ℝ G z v) (z : E)
    (hV : ∃ N : ℕ, ‖(fderiv ℝ G z) ^ N‖ < 1) : IsUnit (1 - Top G π z) := by
  obtain ⟨N, hN⟩ := hV
  set D := fderiv ℝ G z with hD
  set T := Top G π z with hT
  have ht : Tendsto (fun k : ℕ => ‖D ^ N‖ ^ k * (‖D‖ * ‖π‖)) atTop (𝓝 (0 * (‖D‖ * ‖π‖))) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hN).mul_const _
  rw [zero_mul] at ht
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds one_pos))
  set k := k0 + 1 with hk
  have hlt : ‖D ^ N‖ ^ k * (‖D‖ * ‖π‖) < 1 := hk0 k (by omega)
  have hTM : ‖T ^ (N * k + 1)‖ < 1 := by
    rw [hT, Top_pow G π hπ hI z (N * k), ← hD, pow_succ, pow_mul]
    calc ‖(D ^ N) ^ k * D * π‖ ≤ ‖(D ^ N) ^ k‖ * ‖D‖ * ‖π‖ := by
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ‖D ^ N‖ ^ k * ‖D‖ * ‖π‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
            (norm_nonneg _)
          exact norm_pow_le' _ (by omega)
      _ = ‖D ^ N‖ ^ k * (‖D‖ * ‖π‖) := by ring
      _ < 1 := hlt
  set S : E →L[ℝ] E := ∑ i ∈ Finset.range (N * k + 1), T ^ i with hS
  have hSV : Commute (1 - T) S :=
    (Commute.one_left S).sub_left
      (Commute.sum_right _ _ _ fun i _ => ((Commute.refl T).pow_right i))
  have hR : (1 - T) * S = 1 - T ^ (N * k + 1) := by rw [hS, mul_neg_geom_sum]
  have hu : IsUnit ((1 - T) * S) := by
    rw [hR, ← Units.val_oneSub _ hTM]; exact Units.isUnit _
  exact ((Commute.isUnit_mul_iff hSV).1 hu).1

theorem contDiff_Top (G : E → E) (π : E →L[ℝ] E) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (Top G π) :=
  (contDiff_infty_iff_fderiv.1 hG).2.clm_comp contDiff_const

theorem contDiff_inv (G : E → E) (π : E →L[ℝ] E) (hG : ContDiff ℝ ∞ G)
    (hπ : ∀ x, π (π x) = π x)
    (hI : ∀ z v, π v = v → π (fderiv ℝ G z v) = fderiv ℝ G z v)
    (hV : ∀ z : E, ∃ N : ℕ, ‖(fderiv ℝ G z) ^ N‖ < 1) :
    ContDiff ℝ ∞ (fun z => Ring.inverse (1 - Top G π z)) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  have hu := isUnit_one_sub_Top G π hπ hI z (hV z)
  have h1 := contDiffAt_ringInverse ℝ (n := ∞) hu.unit
  rw [hu.unit_spec] at h1
  exact h1.comp z (contDiff_const.sub (contDiff_Top G π hG)).contDiffAt

theorem contDiff_fibInv (G : E → E) (π : E →L[ℝ] E) (hG : ContDiff ℝ ∞ G)
    (hπ : ∀ x, π (π x) = π x)
    (hI : ∀ z v, π v = v → π (fderiv ℝ G z v) = fderiv ℝ G z v)
    (hV : ∀ z : E, ∃ N : ℕ, ‖(fderiv ℝ G z) ^ N‖ < 1) :
    ContDiff ℝ ∞ (fun p : E × E => fibInv G π p.1 p.2) :=
  contDiff_fst.add (((contDiff_inv G π hG hπ hI hV).comp contDiff_fst).clm_apply contDiff_snd)

theorem one_sub_Top_inv (G : E → E) (π : E →L[ℝ] E) (hπ : ∀ x, π (π x) = π x)
    (hI : ∀ z v, π v = v → π (fderiv ℝ G z v) = fderiv ℝ G z v) (z0 : E)
    (hV : ∃ N : ℕ, ‖(fderiv ℝ G z0) ^ N‖ < 1) (u : E) :
    Ring.inverse (1 - Top G π z0) u - Top G π z0 (Ring.inverse (1 - Top G π z0) u) = u := by
  have h := congrArg (fun f : E →L[ℝ] E => f u)
    (Ring.mul_inverse_cancel _ (isUnit_one_sub_Top G π hπ hI z0 hV))
  simpa using h

/-- The fibre inverse moves only in fibre directions. -/
theorem fibInv_dir (G : E → E) (π : E →L[ℝ] E) (hπ : ∀ x, π (π x) = π x)
    (hI : ∀ z v, π v = v → π (fderiv ℝ G z v) = fderiv ℝ G z v) (z0 : E)
    (hV : ∃ N : ℕ, ‖(fderiv ℝ G z0) ^ N‖ < 1) (u : E) (hu : π u = u) :
    π (Ring.inverse (1 - Top G π z0) u) = Ring.inverse (1 - Top G π z0) u := by
  set v := Ring.inverse (1 - Top G π z0) u
  have e := one_sub_Top_inv G π hπ hI z0 hV u
  have hTv : π (Top G π z0 v) = Top G π z0 v := hI z0 (π v) (hπ v)
  have ev : v = u + Top G π z0 v := by rw [← e]; abel
  rw [ev, map_add, hu, hTv]

theorem Psi_add (G : E → E) (π : E →L[ℝ] E)
    (hA : ∀ z v, π v = v → G (z + v) = G z + fderiv ℝ G z v) (z0 v : E) (hv : π v = v) :
    (z0 + v) - G (z0 + v) = (z0 - G z0) + (v - Top G π z0 v) := by
  have : Top G π z0 v = fderiv ℝ G z0 v := by
    show fderiv ℝ G z0 (π v) = _
    rw [hv]
  rw [hA z0 v hv, this]
  abel

/-- (K1c) `Ψ (fibInv z₀ u) = Ψ z₀ + u` for every fibre direction `u`. -/
theorem Psi_fibInv (G : E → E) (π : E →L[ℝ] E) (hπ : ∀ x, π (π x) = π x)
    (hI : ∀ z v, π v = v → π (fderiv ℝ G z v) = fderiv ℝ G z v)
    (hA : ∀ z v, π v = v → G (z + v) = G z + fderiv ℝ G z v) (z0 : E)
    (hV : ∃ N : ℕ, ‖(fderiv ℝ G z0) ^ N‖ < 1) (u : E) (hu : π u = u) :
    fibInv G π z0 u - G (fibInv G π z0 u) = (z0 - G z0) + u := by
  unfold fibInv
  rw [Psi_add G π hA z0 _ (fibInv_dir G π hπ hI z0 hV u hu), one_sub_Top_inv G π hπ hI z0 hV u]

/-- (K1c) uniqueness: every point of the fibre through `z₀` is `fibInv z₀ (Ψ z - Ψ z₀)`. -/
theorem fibInv_unique (G : E → E) (π : E →L[ℝ] E) (hπ : ∀ x, π (π x) = π x)
    (hI : ∀ z v, π v = v → π (fderiv ℝ G z v) = fderiv ℝ G z v)
    (hA : ∀ z v, π v = v → G (z + v) = G z + fderiv ℝ G z v) (z0 : E)
    (hV : ∃ N : ℕ, ‖(fderiv ℝ G z0) ^ N‖ < 1) (z : E) (hz : π (z - z0) = z - z0) :
    z = fibInv G π z0 ((z - G z) - (z0 - G z0)) := by
  have hP := Psi_add G π hA z0 (z - z0) hz
  rw [add_sub_cancel] at hP
  have e : (z - G z) - (z0 - G z0) = (1 - Top G π z0) (z - z0) := by
    rw [hP, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]; abel
  unfold fibInv
  rw [e, ← ContinuousLinearMap.mul_apply,
    Ring.inverse_mul_cancel _ (isUnit_one_sub_Top G π hπ hI z0 hV),
    ContinuousLinearMap.one_apply, add_sub_cancel]

end IntLInfty.Kan.A83Fib

namespace IntLInfty.Kan.A83Abs

open IntLInfty.Kan
open scoped ContDiff

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, _root_.Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

/-- (K1e, fully abstract) horn-`0` filler from abstract fibre data `G`, `H`, `Z`. -/
theorem fillerAt_zero_abs {r m : ℕ} (δ : LInfty L) {S S' : GenSys L} (h : ∀ i, S' i ≤ S i)
    [CompleteSpace (Amb r S (m + 1))] [CompleteSpace (Amb r S m)]
    (G1 : Amb r S (m + 1) → Amb r S (m + 1)) (G0 : Amb r S m → Amb r S m)
    (H1 : Amb r S (m + 1) →L[ℝ] Amb r S (m + 1)) (H0 : Amb r S m →L[ℝ] Amb r S m)
    (Z : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ 0} → Amb r S m) × Amb r S' (m + 1)) →
      Amb r S (m + 1))
    (hG1 : ContDiff ℝ ∞ G1)
    (hV1 : ∀ x, ∃ n : ℕ, ‖(fderiv ℝ G1 x) ^ n‖ < 1)
    (hV0 : ∀ x, ∃ n : ℕ, ‖(fderiv ℝ G0 x) ^ n‖ < 1)
    (hGf : ∀ i : Fin (m + 2), i ≠ 0 → ∀ z, faceAmb r S m i (G1 z) = G0 (faceAmb r S m i z))
    (hint1 : ∀ z, z ∈ integ r δ S (m + 1) ↔ H1 (z - G1 z) = 0)
    (hint0 : ∀ z, z ∈ integ r δ S m ↔ H0 (z - G0 z) = 0)
    (hHid : ∀ z, H1 (H1 z) = H1 z)
    (hHf : ∀ i : Fin (m + 2), i ≠ 0 → ∀ z, faceAmb r S m i (H1 z) = H0 (faceAmb r S m i z))
    (hFsub : ∀ (i : Fin (m + 2)) (a b : Amb r S (m + 1)),
      faceAmb r S m i (a - b) = faceAmb r S m i a - faceAmb r S m i b)
    (hRsub : ∀ a b : Amb r S (m + 1), res h (a - b) = res h a - res h b)
    (hZc : ∀ x, ContDiff ℝ ∞ (fun y => Z x y))
    (hZres : ∀ x y, res h (Z x y) = y.2)
    (hZface : ∀ x (y : ({i : Fin (m + 2) // i ≠ 0} → Amb r S m) × Amb r S' (m + 1)),
      HornCompat (fun q => faceAmb r S q) m 0 y.1 →
      (∀ i, faceAmb r S' m i.1 y.2 = res h (y.1 i)) → ∀ i, faceAmb r S m i.1 (Z x y) = y.1 i)
    (hZkan : ∀ x, Z x (kanMap h m 0 x) = x)
    (π1 : Amb r S (m + 1) →L[ℝ] Amb r S (m + 1)) (π0 : Amb r S m →L[ℝ] Amb r S m)
    (hπ1 : ∀ x, π1 (π1 x) = π1 x) (hπ0 : ∀ x, π0 (π0 x) = π0 x)
    (hI1 : ∀ z v, π1 v = v → π1 (fderiv ℝ G1 z v) = fderiv ℝ G1 z v)
    (hI0 : ∀ z v, π0 v = v → π0 (fderiv ℝ G0 z v) = fderiv ℝ G0 z v)
    (hA1 : ∀ z v, π1 v = v → G1 (z + v) = G1 z + fderiv ℝ G1 z v)
    (hA0 : ∀ z v, π0 v = v → G0 (z + v) = G0 z + fderiv ℝ G0 z v)
    (hface : ∀ i : Fin (m + 2), i ≠ 0 → ∀ v, π1 v = v → π0 (faceAmb r S m i v) = faceAmb r S m i v)
    (hres : ∀ v, π1 v = v → res h v = 0)
    (hu : ∀ z0 : Amb r S (m + 1), res h z0 ∈ integ r δ S' (m + 1) →
      π1 (H1 (z0 - G1 z0)) = H1 (z0 - G1 z0)) :
    ∃ σ : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ 0} → Amb r S m) × Amb r S' (m + 1)) →
        Amb r S (m + 1),
      (∀ x, ContDiff ℝ ∞ (σ x)) ∧
      (∀ x ∈ integ r δ S (m + 1), ∀ y ∈ RelHorn r δ h m 0,
          σ x y ∈ integ r δ S (m + 1) ∧ kanMap h m 0 (σ x y) = y) ∧
      (∀ x ∈ integ r δ S (m + 1), σ x (kanMap h m 0 x) = x) := by
  have hc := A83Fib.contDiff_fibInv G1 π1 hG1 hπ1 hI1 hV1
  have huniq : ∀ a b : Amb r S m, π0 (a - b) = a - b → a - G0 a = b - G0 b → a = b := by
    intro a b hab hPsi
    have e1 := A83Fib.fibInv_unique G0 π0 hπ0 hI0 hA0 b (hV0 b) a hab
    have e2 := A83Fib.fibInv_unique G0 π0 hπ0 hI0 hA0 b (hV0 b) b (by rw [sub_self, map_zero])
    rw [hPsi] at e1
    rw [e1, ← e2]
  refine ⟨fun x y => A83Fib.fibInv G1 π1 (Z x y) (-(H1 (Z x y - G1 (Z x y)))), fun x => ?_,
    fun x hx y hy => ?_, fun x hx => ?_⟩
  · have hz := hZc x
    have hH : ContDiff ℝ ∞ H1 := H1.contDiff
    have h2 := ContDiff.neg (ContDiff.comp hH (ContDiff.sub hz (ContDiff.comp hG1 hz)))
    exact ContDiff.comp hc (ContDiff.prodMk hz h2)
  · obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
    set z0 := Z x y with hz0
    have hres0 : res h z0 = y.2 := hZres x y
    have hf0 : ∀ i, faceAmb r S m i.1 z0 = y.1 i := hZface x y hy3 hy4
    set u := -(H1 (z0 - G1 z0)) with hu_def
    have hu' : π1 u = u := by
      rw [hu_def, map_neg, hu z0 (by rw [hres0]; exact hy2)]
    have hPsi := A83Fib.Psi_fibInv G1 π1 hπ1 hI1 hA1 z0 (hV1 z0) u hu'
    set z := A83Fib.fibInv G1 π1 z0 u with hz
    have hdir : π1 (z - z0) = z - z0 := by
      have hd := A83Fib.fibInv_dir G1 π1 hπ1 hI1 z0 (hV1 z0) u hu'
      have e : z - z0 = Ring.inverse (1 - A83Fib.Top G1 π1 z0) u := by
        rw [hz]
        show z0 + Ring.inverse (1 - A83Fib.Top G1 π1 z0) u - z0 = _
        abel
      rw [e]
      exact hd
    have hPz : z - G1 z = (z0 - G1 z0) - H1 (z0 - G1 z0) := by
      rw [hPsi, hu_def, ← sub_eq_add_neg]
    have hint : z ∈ integ r δ S (m + 1) := by
      rw [hint1, hPz, map_sub, hHid, sub_self]
    refine ⟨hint, Prod.ext (funext fun i => ?_) ?_⟩
    · show faceAmb r S m i.1 z = y.1 i
      have hi0 : i.1 ≠ 0 := i.2
      have hFl : ∀ a b : Amb r S (m + 1),
          faceAmb r S m i.1 (a - b) = faceAmb r S m i.1 a - faceAmb r S m i.1 b :=
        fun a b => hFsub i.1 a b
      refine huniq _ _ ?_ ?_
      · rw [← hf0 i, ← hFl]
        exact hface i.1 hi0 _ hdir
      · have hPi : faceAmb r S m i.1 z - G0 (faceAmb r S m i.1 z) =
            faceAmb r S m i.1 (z - G1 z) := by
          rw [hFl, hGf i.1 hi0 z]
        have hPi0 : faceAmb r S m i.1 (z0 - G1 z0) = y.1 i - G0 (y.1 i) := by
          rw [hFl, hGf i.1 hi0 z0, hf0 i]
        have hH : H0 (y.1 i - G0 (y.1 i)) = 0 := (hint0 (y.1 i)).1 (hy1 i)
        rw [hPi, hPz, hFl, hHf i.1 hi0, hPi0, hH, sub_zero]
    · show res h z = y.2
      have e : res h z - res h z0 = res h (z - z0) := (hRsub z z0).symm
      rw [hres _ hdir, sub_eq_zero, hres0] at e
      exact e
  · show A83Fib.fibInv G1 π1 (Z x (kanMap h m 0 x))
      (-(H1 (Z x (kanMap h m 0 x) - G1 (Z x (kanMap h m 0 x))))) = x
    rw [hZkan x, (hint1 x).1 hx, neg_zero]
    show x + Ring.inverse (1 - A83Fib.Top G1 π1 x) 0 = x
    rw [map_zero, add_zero]

end IntLInfty.Kan.A83Abs

open IntLInfty.Kan in
open scoped ContDiff in
theorem solution {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, _root_.Module ℝ (L i)]
    [∀ i, FiniteDimensional ℝ (L i)] {r m : ℕ} (δ : LInfty L) {S S' : GenSys L} (h : ∀ i, S' i ≤ S i)
    [CompleteSpace (Amb r S (m + 1))] [CompleteSpace (Amb r S m)]
    (G1 : Amb r S (m + 1) → Amb r S (m + 1)) (G0 : Amb r S m → Amb r S m)
    (H1 : Amb r S (m + 1) →L[ℝ] Amb r S (m + 1)) (H0 : Amb r S m →L[ℝ] Amb r S m)
    (Z : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ 0} → Amb r S m) × Amb r S' (m + 1)) →
      Amb r S (m + 1))
    (hG1 : ContDiff ℝ ∞ G1)
    (hV1 : ∀ x, ∃ n : ℕ, ‖(fderiv ℝ G1 x) ^ n‖ < 1)
    (hV0 : ∀ x, ∃ n : ℕ, ‖(fderiv ℝ G0 x) ^ n‖ < 1)
    (hGf : ∀ i : Fin (m + 2), i ≠ 0 → ∀ z, faceAmb r S m i (G1 z) = G0 (faceAmb r S m i z))
    (hint1 : ∀ z, z ∈ integ r δ S (m + 1) ↔ H1 (z - G1 z) = 0)
    (hint0 : ∀ z, z ∈ integ r δ S m ↔ H0 (z - G0 z) = 0)
    (hHid : ∀ z, H1 (H1 z) = H1 z)
    (hHf : ∀ i : Fin (m + 2), i ≠ 0 → ∀ z, faceAmb r S m i (H1 z) = H0 (faceAmb r S m i z))
    (hFsub : ∀ (i : Fin (m + 2)) (a b : Amb r S (m + 1)),
      faceAmb r S m i (a - b) = faceAmb r S m i a - faceAmb r S m i b)
    (hRsub : ∀ a b : Amb r S (m + 1), res h (a - b) = res h a - res h b)
    (hZc : ∀ x, ContDiff ℝ ∞ (fun y => Z x y))
    (hZres : ∀ x y, res h (Z x y) = y.2)
    (hZface : ∀ x (y : ({i : Fin (m + 2) // i ≠ 0} → Amb r S m) × Amb r S' (m + 1)),
      HornCompat (fun q => faceAmb r S q) m 0 y.1 →
      (∀ i, faceAmb r S' m i.1 y.2 = res h (y.1 i)) → ∀ i, faceAmb r S m i.1 (Z x y) = y.1 i)
    (hZkan : ∀ x, Z x (kanMap h m 0 x) = x)
    (π1 : Amb r S (m + 1) →L[ℝ] Amb r S (m + 1)) (π0 : Amb r S m →L[ℝ] Amb r S m)
    (hπ1 : ∀ x, π1 (π1 x) = π1 x) (hπ0 : ∀ x, π0 (π0 x) = π0 x)
    (hI1 : ∀ z v, π1 v = v → π1 (fderiv ℝ G1 z v) = fderiv ℝ G1 z v)
    (hI0 : ∀ z v, π0 v = v → π0 (fderiv ℝ G0 z v) = fderiv ℝ G0 z v)
    (hA1 : ∀ z v, π1 v = v → G1 (z + v) = G1 z + fderiv ℝ G1 z v)
    (hA0 : ∀ z v, π0 v = v → G0 (z + v) = G0 z + fderiv ℝ G0 z v)
    (hface : ∀ i : Fin (m + 2), i ≠ 0 → ∀ v, π1 v = v → π0 (faceAmb r S m i v) = faceAmb r S m i v)
    (hres : ∀ v, π1 v = v → res h v = 0)
    (hu : ∀ z0 : Amb r S (m + 1), res h z0 ∈ integ r δ S' (m + 1) →
      π1 (H1 (z0 - G1 z0)) = H1 (z0 - G1 z0)) :
    ∃ σ : Amb r S (m + 1) → (({i : Fin (m + 2) // i ≠ 0} → Amb r S m) × Amb r S' (m + 1)) →
        Amb r S (m + 1),
      (∀ x, ContDiff ℝ ∞ (σ x)) ∧
      (∀ x ∈ integ r δ S (m + 1), ∀ y ∈ RelHorn r δ h m 0,
          σ x y ∈ integ r δ S (m + 1) ∧ kanMap h m 0 (σ x y) = y) ∧
      (∀ x ∈ integ r δ S (m + 1), σ x (kanMap h m 0 x) = x) := by
  exact A83Abs.fillerAt_zero_abs δ h G1 G0 H1 H0 Z hG1 hV1 hV0 hGf hint1 hint0 hHid hHf hFsub hRsub
    hZc hZres hZface hZkan π1 π0 hπ1 hπ0 hI1 hI0 hA1 hA0 hface hres hu
