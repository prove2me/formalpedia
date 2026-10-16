-- Prove2me | solution 1 for OAI.ComplexCancellation.Rigidity.radical_orbit_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:31:40.415602+00:00
-- url     : https://prove2.me/submissions/14c67dd9-975e-4a76-9c34-aee9a1177a6b

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Rigidity.lean:L45-L71
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.Rigidity.radical_orbit_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation

-- ---- from OAI.Algebra.AffineCancellation.Rigidity ----
namespace OAI

noncomputable section

/-! Polynomial orbit rigidity from the Mason–Stothers theorem. -/
namespace ComplexCancellation.Rigidity
open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain

variable {k : Type*} [Field k]

/-- The polynomial degree bound expressed with radicals. -/
lemma radical_orbit_bound [DecidableEq k] (a d u n : k[X]) :
    (radical (d ^ 2 * (a ^ 2 * u ^ 3) * (-n))).natDegree ≤
    d.natDegree + a.natDegree + u.natDegree + n.natDegree := by
  classical
  have hdvd : radical (d ^ 2 * (a ^ 2 * u ^ 3) * (-n)) ∣
      radical d * (radical a * radical u) * radical n := by
    apply radical_mul_dvd.trans
    apply mul_dvd_mul
    · apply radical_mul_dvd.trans
      apply mul_dvd_mul
      · rw [radical_pow d (by decide : 2 ≠ 0)]
      · apply radical_mul_dvd.trans
        rw [radical_pow a (by decide : 2 ≠ 0), radical_pow u (by decide : 3 ≠ 0)]
    · rw [radical_neg]
  have hb := natDegree_le_of_dvd hdvd
    (mul_ne_zero (mul_ne_zero radical_ne_zero (mul_ne_zero radical_ne_zero radical_ne_zero))
      radical_ne_zero)
  rw [natDegree_mul (mul_ne_zero radical_ne_zero (mul_ne_zero radical_ne_zero radical_ne_zero))
      radical_ne_zero,
    natDegree_mul radical_ne_zero (mul_ne_zero radical_ne_zero radical_ne_zero),
    natDegree_mul radical_ne_zero radical_ne_zero] at hb
  have ha : (radical a).natDegree ≤ a.natDegree := natDegree_radical_le
  have hd : (radical d).natDegree ≤ d.natDegree := natDegree_radical_le
  have hu : (radical u).natDegree ≤ u.natDegree := natDegree_radical_le
  have hn : (radical n).natDegree ≤ n.natDegree := natDegree_radical_le
  omega

end ComplexCancellation.Rigidity

namespace ComplexCancellation.Rigidity

end ComplexCancellation.Rigidity

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Rigidity
open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain


theorem solution : type_of% @_root_.OAI.ComplexCancellation.Rigidity.radical_orbit_bound := @_root_.OAI.ComplexCancellation.Rigidity.radical_orbit_bound
