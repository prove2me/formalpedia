-- Prove2me | solution 1 for LoopTwoGroup.Equiv.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:38:09.911033+00:00
-- url     : https://prove2.me/submissions/be64b7a2-5b46-4895-915b-cd28cb7527fd

import Definitions.Def_LoopTwoGroup_Equiv_Model
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring


set_option autoImplicit false
noncomputable section
open LoopTwoGroup.Equiv MeasureTheory InnerProductSpace Set

namespace Loop54Work

variable {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]

lemma twoPi_pos : 0 < 2 * Real.pi := mul_pos zero_lt_two Real.pi_pos

lemma path_c1 (p : pathSpace g) :
    ContDiffOn ℝ 1 p.1 (Icc 0 (2 * Real.pi)) :=
  p.2.1.of_le (by simp)

lemma path_diff (p : pathSpace g) {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) :
    DifferentiableWithinAt ℝ p.1 (Icc 0 (2 * Real.pi)) t :=
  (path_c1 p).differentiableOn_one t ht

lemma dpath_continuous (p : pathSpace g) :
    ContinuousOn (dpath p.1) (Icc 0 (2 * Real.pi)) :=
  (path_c1 p).continuousOn_derivWithin (uniqueDiffOn_Icc twoPi_pos) le_rfl

lemma inner_c1 (p q : pathSpace g) :
    ContDiffOn ℝ 1 (fun t => ⟪p.1 t, q.1 t⟫_ℝ) (Icc 0 (2 * Real.pi)) :=
  ((path_c1 p).continuousLinearMap_comp (innerSL ℝ)).clm_apply (path_c1 q)

lemma deriv_inner (p q : pathSpace g) {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) :
    derivWithin (fun t => ⟪p.1 t, q.1 t⟫_ℝ) (Icc 0 (2 * Real.pi)) t =
      ⟪p.1 t, dpath q.1 t⟫_ℝ + ⟪q.1 t, dpath p.1 t⟫_ℝ := by
  calc
    _ = ⟪p.1 t, dpath q.1 t⟫_ℝ + ⟪dpath p.1 t, q.1 t⟫_ℝ :=
      (innerSL ℝ (E := g)).derivWithin_of_bilinear (path_diff p ht) (path_diff q ht)
    _ = _ := by rw [real_inner_comm (dpath p.1 t) (q.1 t)]

lemma deriv_bracket (L : InvLieBracket g) (p q : pathSpace g)
    {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) :
    dpath (pathBracket L p q).1 t =
      L.br (p.1 t) (dpath q.1 t) + L.br (dpath p.1 t) (q.1 t) :=
  L.br.derivWithin_of_bilinear (path_diff p ht) (path_diff q ht)

lemma pairing_integrable (p q : pathSpace g) :
    IntervalIntegrable (fun t => ⟪p.1 t, dpath q.1 t⟫_ℝ) volume 0 (2 * Real.pi) :=
  ContinuousOn.intervalIntegrable_of_Icc twoPi_pos.le
    ((path_c1 p).continuousOn.inner (dpath_continuous q))

def J (p q : pathSpace g) : ℝ :=
  ∫ t in (0 : ℝ)..(2 * Real.pi), ⟪p.1 t, dpath q.1 t⟫_ℝ

lemma J_add_left (p q r : pathSpace g) : J (p + q) r = J p r + J q r := by
  unfold J
  simp only [Submodule.coe_add, Pi.add_apply, inner_add_left]
  exact intervalIntegral.integral_add (pairing_integrable p r) (pairing_integrable q r)

lemma J_add_right (p q r : pathSpace g) : J p (q + r) = J p q + J p r := by
  unfold J
  rw [← intervalIntegral.integral_add (pairing_integrable p q) (pairing_integrable p r)]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc 0 (2 * Real.pi) := by simpa only [uIcc_of_le twoPi_pos.le] using ht
  change ⟪p.1 t, derivWithin (q.1 + r.1) (Icc 0 (2 * Real.pi)) t⟫_ℝ = _
  simpa only [dpath, inner_add_right] using
    congrArg (fun v : g => ⟪p.1 t, v⟫_ℝ)
      (derivWithin_add (path_diff q ht') (path_diff r ht'))

lemma J_smul_left (s : ℝ) (p q : pathSpace g) : J (s • p) q = s * J p q := by
  unfold J
  simp only [Submodule.coe_smul, Pi.smul_apply, real_inner_smul_left,
    intervalIntegral.integral_const_mul]

lemma J_smul_right (s : ℝ) (p q : pathSpace g) : J p (s • q) = s * J p q := by
  unfold J
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc 0 (2 * Real.pi) := by simpa only [uIcc_of_le twoPi_pos.le] using ht
  change ⟪p.1 t, derivWithin (s • q.1) (Icc 0 (2 * Real.pi)) t⟫_ℝ = _
  simpa only [dpath, real_inner_smul_right] using
    congrArg (fun v : g => ⟪p.1 t, v⟫_ℝ)
      (derivWithin_const_smul s (path_diff q ht'))

lemma J_boundary (p q : pathSpace g) :
    J p q + J q p = ⟪p.1 (2 * Real.pi), q.1 (2 * Real.pi)⟫_ℝ := by
  have h := intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc
    (inner_c1 p q) twoPi_pos.le
  have hder : (∫ t in (0 : ℝ)..(2 * Real.pi),
      derivWithin (fun t => ⟪p.1 t, q.1 t⟫_ℝ) (Icc 0 (2 * Real.pi)) t) =
      J p q + J q p := by
    unfold J
    rw [← intervalIntegral.integral_add (pairing_integrable p q) (pairing_integrable q p)]
    apply intervalIntegral.integral_congr
    intro t ht
    exact deriv_inner p q (by simpa only [uIcc_of_le twoPi_pos.le] using ht)
  rw [hder] at h
  simpa only [p.2.2.1, q.2.2.1, inner_zero_left, sub_zero] using h

lemma inner_cyclic (L : InvLieBracket g) (a b c : g) :
    ⟪a, L.br b c⟫_ℝ = ⟪L.br c a, b⟫_ℝ := by
  calc
    ⟪a, L.br b c⟫_ℝ = ⟪L.br a b, c⟫_ℝ := (L.invariant a b c).symm
    _ = ⟪c, L.br a b⟫_ℝ := real_inner_comm c (L.br a b)
    _ = ⟪L.br c a, b⟫_ℝ := (L.invariant c a b).symm

lemma J_bracket_right (L : InvLieBracket g) (p q r : pathSpace g) :
    J p (pathBracket L q r) = J (pathBracket L p q) r + J (pathBracket L r p) q := by
  unfold J
  rw [← intervalIntegral.integral_add
    (pairing_integrable (pathBracket L p q) r)
    (pairing_integrable (pathBracket L r p) q)]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc 0 (2 * Real.pi) := by simpa only [uIcc_of_le twoPi_pos.le] using ht
  dsimp only
  rw [deriv_bracket L q r ht', inner_add_right]
  change ⟪p.1 t, L.br (q.1 t) (dpath r.1 t)⟫_ℝ +
      ⟪p.1 t, L.br (dpath q.1 t) (r.1 t)⟫_ℝ =
    ⟪L.br (p.1 t) (q.1 t), dpath r.1 t⟫_ℝ +
      ⟪L.br (r.1 t) (p.1 t), dpath q.1 t⟫_ℝ
  rw [L.invariant, inner_cyclic L (p.1 t) (dpath q.1 t) (r.1 t)]

end Loop54Work


set_option autoImplicit false
open LoopTwoGroup.Equiv Loop54Work MeasureTheory InnerProductSpace

theorem solution {g : Type*} [NormedAddCommGroup g] [InnerProductSpace ℝ g]
    [FiniteDimensional ℝ g] (L : InvLieBracket g) (k : ℝ) :
    ∃ Φ : LInfHom (Pk L k) (gk L k), PhiComponents L k Φ := by
  let Φ : LInfHom (Pk L k) (gk L k) := {
    f0 := {
      toFun := fun p => p.1 (2 * Real.pi)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    f1 := LinearMap.snd ℝ (loopSpace g) ℝ
    f2 := fun p q => k * (J q p - J p q)
    f2_add := by
      intro p q r
      rw [J_add_right, J_add_left]
      ring
    f2_smul := by
      intro s p q
      rw [J_smul_right, J_smul_left]
      simp only [smul_eq_mul]
      ring
    f2_skew := by intros; ring
    chain := by
      intro h
      change (0 : g) = h.1.1 (2 * Real.pi)
      exact h.1.2.2.symm
    eq3 := by
      intro p q
      change (0 : g) = L.br (p.1 (2 * Real.pi)) (q.1 (2 * Real.pi)) -
        L.br (p.1 (2 * Real.pi)) (q.1 (2 * Real.pi))
      exact (sub_self _).symm
    eq4 := by
      intro p h
      let l : pathSpace g := ⟨h.1.1, h.1.2.1⟩
      have he : l.1 (2 * Real.pi) = 0 := h.1.2.2
      have hz := J_boundary p l
      rw [he, inner_zero_right] at hz
      have hj : J p l = -J l p := eq_neg_of_add_eq_zero_left hz
      change k * (J l p - J p l) = 2 * k * J l p - 0
      rw [hj]
      ring
    eq5 := by
      intro p q r
      have h := J_boundary p (pathBracket L q r)
      rw [J_bracket_right L p q r] at h
      change J (pathBracket L p q) r + J (pathBracket L r p) q +
          J (pathBracket L q r) p =
        ⟪p.1 (2 * Real.pi), L.br (q.1 (2 * Real.pi)) (r.1 (2 * Real.pi))⟫_ℝ at h
      change (0 : ℝ) - k *
          ⟪p.1 (2 * Real.pi), L.br (q.1 (2 * Real.pi)) (r.1 (2 * Real.pi))⟫_ℝ =
        k * (J (pathBracket L q r) p - J p (pathBracket L q r)) +
          k * (J (pathBracket L r p) q - J q (pathBracket L r p)) +
          k * (J (pathBracket L p q) r - J r (pathBracket L p q)) + 0 + 0 + 0
      rw [J_bracket_right L p q r, J_bracket_right L q r p,
        J_bracket_right L r p q, ← h]
      ring }
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro p; rfl
  · intro h; rfl
  · intro p q
    change k * (J q p - J p q) =
      k * ∫ t in (0 : ℝ)..(2 * Real.pi),
        (⟪q.1 t, dpath p.1 t⟫_ℝ - ⟪dpath q.1 t, p.1 t⟫_ℝ)
    congr 1
    unfold J
    rw [← intervalIntegral.integral_sub (pairing_integrable q p) (pairing_integrable p q)]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [real_inner_comm (dpath q.1 t) (p.1 t)]
