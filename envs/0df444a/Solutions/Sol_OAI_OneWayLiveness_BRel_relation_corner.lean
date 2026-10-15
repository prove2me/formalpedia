-- Prove2me | solution 1 for OAI.OneWayLiveness.BRel.relation_corner
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:48:17.432935+00:00
-- url     : https://prove2.me/submissions/7fa83419-4dfe-4e72-be7d-f01ff7edccc3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Relations.lean:L63-L98
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.BRel.relation_corner. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations

-- ---- from OAI.Combinatorics.Automata.Relations ----
namespace OAI

namespace OneWayLiveness

namespace BRel
variable {H : Type*}

/-- Restrict a relation corner with a split subidentity. -/
lemma relation_corner {P : BRel H} (hP : P * P = P) (F : Set H)
    (hF : restrictedId F * P * restrictedId F = restrictedId F) :
    let Q := P * restrictedId F * P
    ∃ hQ : Q * Q = Q, ∃ θ : Corner Q hQ ≃* BRel F,
      (∀ z x y, (θ z).holds x y ↔ z.val.holds x.val y.val) ∧ P * Q = Q ∧ Q * P = Q := by
  let E := restrictedId F
  have hE : E * E = E := restrictedId_idem F
  let u := P * E
  let v := E * P
  let Q := P * E * P
  have huv : u * v = Q := by dsimp [u, v, Q]; rw [← mul_assoc, mul_assoc P E E, hE]
  have hvu : v * u = E := by dsimp [u, v]; rw [mul_assoc E P, ← mul_assoc P P E, hP]; simpa only [E, mul_assoc] using hF
  have hu : u * E = u := by dsimp [u]; rw [mul_assoc, hE]
  have hv : E * v = v := by dsimp [v]; rw [← mul_assoc, hE]
  have hQ : Q * Q = Q := by
    rw [← huv, mul_assoc, ← mul_assoc v u, hvu, ← mul_assoc, hu]
  have hpq : P * Q = Q := by dsimp [Q]; rw [← mul_assoc, ← mul_assoc, hP]
  have hqp : Q * P = Q := by dsimp [Q]; rw [mul_assoc, hP]
  let θ := (Corner.equivOfSplit (he := hQ) (hf := hE) u v huv hvu hu hv).trans (restrictionEquiv F)
  refine ⟨hQ, θ, ?_, hpq, hqp⟩
  intro z x y
  change (v * z.val * u).holds x.val y.val ↔ z.val.holds x.val y.val
  have hpz : P * z.val = z.val := by
    calc
      _ = P * (Q * z.val) := by rw [z.left]
      _ = z.val := by rw [← mul_assoc, hpq, z.left]
  have hzp : z.val * P = z.val := by
    calc
      _ = (z.val * Q) * P := by rw [z.right]
      _ = z.val := by rw [mul_assoc, hqp, z.right]
  have heq : v * z.val * u = E * z.val * E := by
    dsimp [u, v]
    rw [mul_assoc E P, hpz, ← mul_assoc, mul_assoc E z.val P, hzp]
  rw [heq, mul_restrictedId, restrictedId_mul]
  simp
end BRel

namespace BRel
variable {H : Type*}
end BRel

namespace RectangleFrame
variable {H I J : Type*} (F : RectangleFrame H I J)
end RectangleFrame

namespace Corner
variable {M : Type*} [Monoid M] {e : M} {he : e * e = e}

end Corner

namespace BRel
variable {H : Type*}
end BRel

end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness OAI.OneWayLiveness.BRel


theorem solution : type_of% @_root_.OAI.OneWayLiveness.BRel.relation_corner := @_root_.OAI.OneWayLiveness.BRel.relation_corner
