-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Hom.Rel.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:27.626361+00:00
-- url     : https://prove2.me/submissions/dd205543-62ca-47a2-9468-26b919219a8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransport
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_Rel_mul
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_rel_one
import Theorems.Thm_GlobalTheory_Ex_NumD_Iso_rel_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD GlobalTheory.Ex.NumD.Hom
variable {O O' : Type} [CommRing O] [CommRing O'] {f : O →+* O'} {N : NumD O} {N' : NumD O'} (I : NumD.Hom f N N')
local notation "F" => Units.map (RingHom.toMonoidHom f)
variable {I}
namespace GlobalTheory.Ex.NumD.Hom
namespace Rel
theorem _root_.solution {g : N.Gt} {g' : N'.Gt} (hg : I.Rel g g') (n : ℕ) : I.Rel (g ^ n) (g' ^ n) := by
  induction n with
  | zero => simpa using I.rel_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hg
end Rel
end GlobalTheory.Ex.NumD.Hom
