-- Prove2me | solution 1 for N25.Endgame.FBaseCoeffMap25_generates
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:45.052281+00:00
-- url     : https://prove2.me/submissions/f41d3f30-645e-41eb-ae79-d48140f720f8

import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

namespace N25.Endgame

theorem _root_.solution
    (k K : Type*) [Field k] [Field K] [Algebra k K] :
    IntermediateField.adjoin K (Set.range (FBaseCoeffMap25 k K)) = ⊤ := by
  let inclusion : FBase K →ₐ[K] LaurentSeries K := (FBase K).val
  apply (IntermediateField.map_injective inclusion)
  rw [IntermediateField.adjoin_map]
  have himage : inclusion ''
      Set.range (FBaseCoeffMap25 k K) =
      ModularCurve.coeffMap (algebraMap k K) ''
        (ModularCurve.qExpFunctionFieldC k Γ25 : Set (LaurentSeries k)) := by
    ext z
    constructor
    · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
      exact ⟨f, f.property, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨FBaseCoeffMap25 k K ⟨f, hf⟩, ⟨⟨f, hf⟩, rfl⟩, rfl⟩
  rw [himage, ← ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC k K Γ25]
  ext x
  simp [inclusion]
  rfl

end N25.Endgame
