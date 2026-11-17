-- Prove2me | solution 1 for MazurProof.RationalPointsN25QuotientSmoothF2.normalized_projective_point_not_singular
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:09:29.894365+00:00
-- url     : https://prove2.me/submissions/bb6a6d9c-9868-44f7-835f-d624dbc2c472

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF2_wChart_jacobian_certificate
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF2_yChart_jacobian_certificate
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF2_zChart_jacobian_certificate
import Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF2_xChart_jacobian_certificate

/-! Structural Jacobian certificates for the canonical curve in both good characteristics. -/

namespace MazurProof.RationalPointsN25QuotientSmoothF2

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

/-- No normalized projective point over any characteristic-two field is a
singular point of the canonical complete intersection.  Applying this theorem
to an algebraic closure supplies the geometric Jacobian-criterion
certificate needed for good reduction at two. -/
theorem _root_.solution
    {K : Type*} [Field K] [CharP K 2] (P : NormalizedProjective4 K) :
    ¬ IsCanonicalSingular25CharTwo (normalizedCoordinates25 P) := by
  intro hsing
  cases P with
  | xChart y z w =>
      change IsCanonicalSingular25CharTwo
        (⟨1, y, z, w⟩ : Coordinates4 K) at hsing
      rcases hsing with ⟨hq, hk, hxy, hxz, hxw, hyz, hyw, hzw⟩
      have hcert := xChart_jacobian_certificate y z w
      simp [hq, hk, hxz, hxw, hyz, hyw, hzw] at hcert
  | yChart z w =>
      change IsCanonicalSingular25CharTwo
        (⟨0, 1, z, w⟩ : Coordinates4 K) at hsing
      rcases hsing with ⟨hq, hk, hxy, hxz, hxw, hyz, hyw, hzw⟩
      have hcert := yChart_jacobian_certificate (0 : K) z w
      simp [hq, hk, hxy, hxz, hyz, hyw] at hcert
  | zChart w =>
      change IsCanonicalSingular25CharTwo
        (⟨0, 0, 1, w⟩ : Coordinates4 K) at hsing
      rcases hsing with ⟨hq, hk, hxy, hxz, hxw, hyz, hyw, hzw⟩
      have hcert := zChart_jacobian_certificate (0 : K) 0 w
      simp [hq, hxy, hxz, hxw, hyz, hyw, hzw] at hcert
  | wChart =>
      change IsCanonicalSingular25CharTwo
        (⟨0, 0, 0, 1⟩ : Coordinates4 K) at hsing
      rcases hsing with ⟨hq, hk, hxy, hxz, hxw, hyz, hyw, hzw⟩
      have hcert := wChart_jacobian_certificate (K := K) 0 0 0
      simp [hq, hk, hxy, hxz, hyz, hyw, hzw] at hcert

end MazurProof.RationalPointsN25QuotientSmoothF2

namespace MazurProof.RationalPointsN25QuotientSmoothF3

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

open MazurProof.RationalPointsN25QuotientKummerThree

open MazurProof.RationalPointsN25QuotientWeilThreeLinear

open MazurProof.RationalPointsN25QuotientKummerThreeProjective

open MazurProof.RationalPointsN25QuotientSmallThreeSemantic

end MazurProof.RationalPointsN25QuotientSmoothF3

namespace N25

open scoped BigOperators

end N25

namespace N25

open scoped BigOperators

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

open MazurProof.RationalPointsN25QuotientKummerThreeProjective

end N25

namespace N25

open scoped BigOperators

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientKummerThreeProjective

end N25

namespace N25

end N25
