-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6_label_gcd_positive__p2m_58793991_d9f6_4cd5_bcae_633aaf737148_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T10:59:30.032816+00:00
-- url     : https://prove2.me/submissions/d36681d6-a6bd-42bb-990d-9e9d0d22cf35

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling

set_option autoImplicit false

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    ∀ e ∈ (KnodelPrimeCordial.knodel 3 n).edgeFinset,
      0 < KnodelPrimeCordial.edgeGcd
        (fun v : Fin 2 × Fin (n / 2) =>
          KnodelPrimeCordial.labelF
            (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n)) e := by
  have hlabel : ∀ i : ℕ, 0 < KnodelPrimeCordial.labelF i := by
    intro i
    have hlt : i % 12 < 12 := Nat.mod_lt _ (by omega)
    interval_cases h : i % 12 <;>
      simp [KnodelPrimeCordial.labelF, h] <;> omega
  intro e he
  have hvertex : ∀ v : Fin 2 × Fin (n / 2),
      0 < KnodelPrimeCordial.labelF
        (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n) := by
    intro v
    exact hlabel _
  refine Sym2.inductionOn e ?_
  intro u v
  change 0 < Nat.gcd
    (KnodelPrimeCordial.labelF
      (if u.1 = 0 then (2 * u.2.val) % n else (2 * u.2.val + n - 1) % n))
    (KnodelPrimeCordial.labelF
      (if v.1 = 0 then (2 * v.2.val) % n else (2 * v.2.val + n - 1) % n))
  exact Nat.gcd_pos_of_pos_left _ (hvertex u)
