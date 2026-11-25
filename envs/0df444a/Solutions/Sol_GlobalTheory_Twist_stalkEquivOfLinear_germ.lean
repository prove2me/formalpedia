-- Prove2me | solution 1 for GlobalTheory.Twist.stalkEquivOfLinear_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:14:35.025042+00:00
-- url     : https://prove2.me/submissions/acbaddf0-ba74-4637-946c-2169fbc818bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasicoherentOfLocallyIso

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self val_res le_iSup_inf unitMod homOfLinear isoOfLinear toMod)
open GlobalTheory
open GlobalTheory.Twist
variable {X Y : Scheme.{0}}
variable {F G : X.Modules}
variable {U : X.Opens} (φ : ∀ V : X.Opens, V ≤ U → (Γ(F, V) ≃ₗ[Γ(X, V)] Γ(G, V)))
  (hφ : ∀ {V W : X.Opens} (hV : V ≤ U) (h : W ≤ V) (s : Γ(F, V)),
    φ W (h.trans hV) (resM F h s) = resM G h (φ V hV s)) {x : X} (hx : x ∈ U)
namespace GlobalTheory.Twist
theorem _root_.solution {V : X.Opens} (hV : V ≤ U) (hxV : x ∈ V) (s : Γ(F, V)) :
    stalkEquivOfLinear φ hφ hx (F.presheaf.germ V x hxV s) =
      G.presheaf.germ V x hxV (φ V hV s) :=
  stalkHomOfLinear_germ φ hφ hx hV hxV s
end GlobalTheory.Twist
