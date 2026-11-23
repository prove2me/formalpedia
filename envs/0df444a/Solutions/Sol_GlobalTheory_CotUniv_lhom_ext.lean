-- Prove2me | solution 1 for GlobalTheory.CotUniv.lhom_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:03.97398+00:00
-- url     : https://prove2.me/submissions/cdd944c8-6b05-41e3-baef-1fa1862ff24b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FstHomCompSqzOfLeibniz
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_UniversalDerivation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory GlobalTheory.CotUniv
variable {R₀ : Type} [CommRing R₀] (O : LAlg R₀)
  (M : Type) [AddCommGroup M] [Module (O : Type) M]
namespace GlobalTheory.CotUniv
theorem _root_.solution {R S : LAlg R₀} {f g : LHom R S} (h : ∀ a, f.1 a = g.1 a) : f = g :=
  Subtype.ext (AlgHom.ext h)
end GlobalTheory.CotUniv
