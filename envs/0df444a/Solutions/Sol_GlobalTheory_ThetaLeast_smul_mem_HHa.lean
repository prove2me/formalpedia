-- Prove2me | solution 1 for GlobalTheory.ThetaLeast.smul_mem_HHa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:51:27.841202+00:00
-- url     : https://prove2.me/submissions/d5b8b069-5569-469e-aa28-76c237bd0ecc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCombinationOfMemHaO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_VVAlgebraMapNonnegDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCombinationIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.ThetaLeast
namespace GlobalTheory.ThetaLeast
theorem _root_.solution {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k] {cc : Ty → Ty} {isX : Ty → Prop}
    {a : Ty → ℕ → ℕ} (s : k) {P : MvPolynomial (Letter Ty r n) k} (hP : P ∈ HHa r n k cc isX a) :
    s • P ∈ HHa r n k cc isX a :=
  ⟨Submodule.smul_mem _ s hP.1, fun σ i i' hi t => by rw [map_smul, hP.2.1 σ i i' hi t],
    fun m hm => hP.2.2 m (MvPolynomial.support_smul hm)⟩
end GlobalTheory.ThetaLeast
