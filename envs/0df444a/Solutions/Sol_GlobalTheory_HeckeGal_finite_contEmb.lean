-- Prove2me | solution 1 for GlobalTheory.HeckeGal.finite_contEmb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:14.174928+00:00
-- url     : https://prove2.me/submissions/b2dd88d3-b9be-4df5-acda-dd09d1e9a012

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory GlobalTheory.HeckeGal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.HeckeGal
theorem _root_.solution (v : HeightOneSpectrum (𝓞 E)) :
    Finite {j : v.adicCompletion E →+* Qbar l // Continuous j} := by
  refine Finite.of_injective
    (fun j : {j : v.adicCompletion E →+* Qbar l // Continuous j} =>
      j.1.comp (algebraMap E (v.adicCompletion E))) fun a b h => ?_
  apply Subtype.ext
  apply DFunLike.coe_injective
  refine (HeightOneSpectrum.denseRange_algebraMap E v).equalizer a.2 b.2 ?_
  funext k
  exact DFunLike.congr_fun h k
end GlobalTheory.HeckeGal
