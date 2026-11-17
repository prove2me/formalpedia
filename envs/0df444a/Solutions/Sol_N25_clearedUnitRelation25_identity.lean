-- Prove2me | solution 1 for N25.clearedUnitRelation25_identity
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:29.216763+00:00
-- url     : https://prove2.me/submissions/3555dcea-4df5-483a-bfb0-358b2e5c082f

import Definitions.Def_N25_UnitRelation

set_option autoImplicit false

namespace N25

/-- Clearing the two denominators recovers the integral homogeneous expression. -/
theorem _root_.solution
    {K : Type*} [Field K] (g f₀ f₁ : K) (hg : g ≠ 0) (hf₁ : f₁ ≠ 0) :
    clearedUnitRelation25 g f₀ f₁ =
      g ^ 7 * f₁ ^ 4 * planeRelation (f₀ / g) (f₀ / f₁) := by
  unfold clearedUnitRelation25 planeRelation
  field_simp [hg, hf₁]
  ring

end N25
