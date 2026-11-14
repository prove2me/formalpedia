-- Prove2me | solution 1 for LatticePrepro.CodeFamily.accepts_of_isApprox
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:28:03.921438+00:00
-- url     : https://prove2.me/submissions/5eab4dc8-d47e-4ad5-93b5-c7932c13e901

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Conversions_SearchTest

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.CodeFamily end LatticePrepro.CodeFamily

namespace LatticePrepro

namespace CodeFamily

variable {F : Type} [Field F] [DecidableEq F] {X : Type} (C : CodeFamily F X)

/-- **Lemma 5.2 for codes, YES instances**: if `dist(t_x, 𝒞) ≤ R` and `f ≤ g`, every
`f`-approximate solution is accepted. -/
private theorem accepts_of_isApprox {g R : ℕ} {x : X} (hx : codeDist (C.target x) C.code ≤ R) {f : ℝ}
    (hfg : f ≤ g) {c : C.M → F} (hc : C.IsApprox f x c) : C.Accepts g R x c := by
  refine ⟨hc.1, ?_⟩
  have h : (hammingDist (C.target x) c : ℝ) ≤ (g : ℝ) * R :=
    calc (hammingDist (C.target x) c : ℝ) ≤ f * codeDist (C.target x) C.code := hc.2
      _ ≤ g * R := by gcongr
  exact_mod_cast h

end CodeFamily

end LatticePrepro

open LatticePrepro
open LatticePrepro.CodeFamily
variable {F : Type} [Field F] [DecidableEq F] {X : Type} (C : CodeFamily F X)
theorem solution {g R : ℕ} {x : X} (hx : codeDist (C.target x) C.code ≤ R) {f : ℝ}
    (hfg : f ≤ g) {c : C.M → F} (hc : C.IsApprox f x c) : C.Accepts g R x c :=
  @LatticePrepro.CodeFamily.accepts_of_isApprox F _ _ X C g R x hx f hfg c hc
