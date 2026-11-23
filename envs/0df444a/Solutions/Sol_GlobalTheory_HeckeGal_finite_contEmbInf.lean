-- Prove2me | solution 1 for GlobalTheory.HeckeGal.finite_contEmbInf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:45:57.55586+00:00
-- url     : https://prove2.me/submissions/f40b443f-36ac-43c4-a267-984fc54b0c82

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
theorem _root_.solution (w : InfinitePlace E) :
    Finite {i : w.Completion →+* ℂ // Continuous i} := by
  refine Finite.of_injective
    (fun j : {i : w.Completion →+* ℂ // Continuous i} =>
      j.1.comp (algebraMap E w.Completion)) fun a b h => ?_
  apply Subtype.ext
  apply DFunLike.coe_injective
  have hd : DenseRange (algebraMap E w.Completion) := by
    refine Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)
    rintro _ ⟨a, rfl⟩
    exact ⟨WithAbs.equiv w.1 a, rfl⟩
  refine hd.equalizer a.2 b.2 ?_
  funext k
  exact DFunLike.congr_fun h k
end GlobalTheory.HeckeGal
