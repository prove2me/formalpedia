-- Prove2me | solution 1 for MetricCodes.projection_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/ef92cec9-26a0-4063-b778-a94081698cd0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_projection_certificate_mul

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix InnerProductSpace
variable {X E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D d : ℕ}
namespace MetricCodes
theorem _root_.solution
    (P : ProjectionFamily X D d)
    (C : Finset X)
    (t : X → X → ℝ)
    (q : X → E)
    {s lam : ℝ}
    (hd : 0 < d)
    (hs : s < 1)
    (hgap : s < lam)
    (hdiag : ∀ x ∈ C, t x x = 1)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → t x y ≤ s)
    (hgram : ∀ x ∈ C, ∀ y ∈ C,
      ⟪q x, q y⟫_ℝ = (t x y - lam) * P.overlap x y) :
    (C.card : ℝ) ≤
      ((1 - s) / (lam - s)) * ((D : ℝ) / (d : ℝ)) := by
  have hrank : 0 < (d : ℝ) := by exact_mod_cast hd
  have hgap_pos : 0 < lam - s := sub_pos.mpr hgap
  have hmul :=
    projection_certificate_mul P C t q hd hs hgap hdiag hsep hgram
  have hdiv :
      (C.card : ℝ) * (d : ℝ) ≤
        ((1 - s) * (D : ℝ)) / (lam - s) := by
    apply (le_div_iff₀ hgap_pos).2
    calc
      ((C.card : ℝ) * (d : ℝ)) * (lam - s) =
          (C.card : ℝ) * (lam - s) * (d : ℝ) := by ring
      _ ≤ (1 - s) * (D : ℝ) := hmul
  calc
    (C.card : ℝ) ≤
        (((1 - s) / (lam - s)) * (D : ℝ)) / (d : ℝ) := by
          apply (le_div_iff₀ hrank).2
          calc
            (C.card : ℝ) * (d : ℝ) ≤
                ((1 - s) * (D : ℝ)) / (lam - s) := hdiv
            _ = ((1 - s) / (lam - s)) * (D : ℝ) := by ring
    _ = ((1 - s) / (lam - s)) * ((D : ℝ) / (d : ℝ)) := by ring
end MetricCodes
