-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.mem_euclidLattice2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:54:14.631173+00:00
-- url     : https://prove2.me/submissions/7b98081b-3de9-4b00-89f8-921c5efe00bd

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Adele2
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Automorphic.Adele2
theorem _root_.solution (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (u : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K)) :
    u ∈ euclidLattice2 I ↔ (toEuclid2 K).symm u ∈ idealLattice2 I := Iff.rfl
end GroundTheory.Automorphic.Adele2
