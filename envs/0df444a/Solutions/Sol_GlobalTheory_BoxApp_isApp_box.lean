-- Prove2me | solution 1 for GlobalTheory.BoxApp.isApp_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:51:45.249952+00:00
-- url     : https://prove2.me/submissions/ac8fe88c-74c2-47b5-8dc9-6fa11d31f608

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_IsAppBox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory GlobalTheory.BoxApp
namespace GlobalTheory.BoxApp
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {D D₂ D' : DegPre R} {n₁ n₂ : ℕ} (pD₂ : IsPowDeg D₂ D n₂)
    (pD : IsPowDeg D' D (n₁ + n₂)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
    (a : Fin n₁ → Fam D F k) (u : Fin n₂ → Fam D F k) (sb : Fam D₂ F k) (S : Fam D' F k)
    (h₂ : IsBoxFam pD₂ F k sb u) (h : IsBoxFam pD F k S (Fin.append a u)) : IsApp pD₂ pD F k a sb S :=
  ⟨1, fun _ => 1, fun _ => u, fun _ => sb, fun _ => S, fun _ => h₂, fun _ => h, by simp, by simp⟩
end GlobalTheory.BoxApp
