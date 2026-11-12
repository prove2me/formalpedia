-- Prove2me | solution 1 for LSAPR.decomposition_8_13
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T00:18:02.702311+00:00
-- url     : https://prove2.me/submissions/0ec8f191-1681-479e-a57b-dece6911d040

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model
import Definitions.Def_LSAPR_Model

open MeasureTheory ProbabilityTheory PolyakJuditsky.Averaging

namespace Aux_LSAPR_813
open LSAPR

theorem mA_sub {d : ℕ} (M N : Mat d) (v : Vec d) :
    matApply (M - N) v = matApply M v - matApply N v := by
  unfold matApply
  rw [map_sub, LinearMap.sub_apply]

theorem mA_smul {d : ℕ} (c : ℝ) (M : Mat d) (v : Vec d) :
    matApply (c • M) v = c • matApply M v := by
  unfold matApply
  rw [map_smul, LinearMap.smul_apply]

theorem mA_one {d : ℕ} (v : Vec d) : matApply (1 : Mat d) v = v := by
  unfold matApply
  rw [Matrix.toLpLin_one, LinearMap.id_apply]

theorem mA_mul {d : ℕ} (M N : Mat d) (v : Vec d) :
    matApply (M * N) v = matApply M (matApply N v) := by
  unfold matApply
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply]

theorem mA_add_v {d : ℕ} (M : Mat d) (v w : Vec d) :
    matApply M (v + w) = matApply M v + matApply M w := by
  unfold matApply
  exact map_add _ _ _

theorem mA_sub_v {d : ℕ} (M : Mat d) (v w : Vec d) :
    matApply M (v - w) = matApply M v - matApply M w := by
  unfold matApply
  exact map_sub _ _ _

theorem mA_smul_v {d : ℕ} (M : Mat d) (c : ℝ) (v : Vec d) :
    matApply M (c • v) = c • matApply M v := by
  unfold matApply
  exact map_smul _ _ _

end Aux_LSAPR_813

open LSAPR Aux_LSAPR_813 in
theorem solution {d : ℕ} {Z : Type*} [MeasurableSpace Z] (π : Measure Z)
    (A : Z → Mat d) (b : Z → Vec d) (θstar : Vec d)
    (hsol : matApply (Abar π A) θstar = bbar π b)
    (α : ℝ) (hα : 0 < α) (θ0 : Vec d) (Zpath : ℕ → Z) (n : ℕ) :
    lsaIter α A b θ0 Zpath n - θstar =
        matApply (Gamma α A Zpath 1 n) (θ0 - θstar)
          + J0 (Abar π A) (epsNoise π A b θstar) α Zpath n
          + H0 (Abar π A) A (epsNoise π A b θstar) α Zpath n ∧
      H0 (Abar π A) A (epsNoise π A b θstar) α Zpath n =
        J1 (Abar π A) A (epsNoise π A b θstar) α Zpath n
          + H1 (Abar π A) A (epsNoise π A b θstar) α Zpath n ∧
      lsaIter α A b θ0 Zpath n - θstar =
        matApply (Gamma α A Zpath 1 n) (θ0 - θstar)
          + J0 (Abar π A) (epsNoise π A b θstar) α Zpath n
          + J1 (Abar π A) A (epsNoise π A b θstar) α Zpath n
          + H1 (Abar π A) A (epsNoise π A b θstar) α Zpath n := by
  have hε : ∀ z, epsNoise π A b θstar z = matApply (A z) θstar - b z := by
    intro z
    unfold epsNoise Atilde btilde
    rw [mA_sub, hsol]
    abel
  have hΓ0 : Gamma α A Zpath 1 0 = 1 := by
    unfold Gamma
    simp
  have hΓ : ∀ m, Gamma α A Zpath 1 (m + 1) = (1 - α • A (Zpath (m + 1))) * Gamma α A Zpath 1 m := by
    intro m
    unfold Gamma
    rw [show m + 1 + 1 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega, List.range'_1_concat,
      List.reverse_append, List.map_append, List.prod_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    rw [add_comm 1 m]
  have c1 : ∀ m, lsaIter α A b θ0 Zpath m - θstar =
      matApply (Gamma α A Zpath 1 m) (θ0 - θstar)
        + J0 (Abar π A) (epsNoise π A b θstar) α Zpath m
        + H0 (Abar π A) A (epsNoise π A b θstar) α Zpath m := by
    intro m
    induction m with
    | zero =>
      rw [hΓ0, mA_one]
      simp only [lsaIter, J0, H0]
      abel
    | succ m ih =>
      have hθ : lsaIter α A b θ0 Zpath m =
          matApply (Gamma α A Zpath 1 m) (θ0 - θstar)
            + J0 (Abar π A) (epsNoise π A b θstar) α Zpath m
            + H0 (Abar π A) A (epsNoise π A b θstar) α Zpath m + θstar := by
        rw [← ih]
        abel
      rw [hΓ m, mA_mul]
      simp only [lsaIter, J0, H0]
      rw [hθ, hε (Zpath (m + 1))]
      simp only [mA_sub, mA_one, mA_smul, mA_add_v, mA_sub_v, mA_smul_v]
      module
  have c2 : ∀ m, H0 (Abar π A) A (epsNoise π A b θstar) α Zpath m =
      J1 (Abar π A) A (epsNoise π A b θstar) α Zpath m
        + H1 (Abar π A) A (epsNoise π A b θstar) α Zpath m := by
    intro m
    induction m with
    | zero =>
      simp only [H0, J1, H1]
      abel
    | succ m ih =>
      simp only [H0, J1, H1]
      rw [ih]
      simp only [mA_sub, mA_one, mA_smul, mA_add_v, mA_sub_v, mA_smul_v]
      module
  refine ⟨c1 n, c2 n, ?_⟩
  rw [c1 n, c2 n]
  abel
