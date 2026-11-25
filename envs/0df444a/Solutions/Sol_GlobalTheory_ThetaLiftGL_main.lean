-- Prove2me | solution 1 for GlobalTheory.ThetaLiftGL.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:41:16.827537+00:00
-- url     : https://prove2.me/submissions/77f61570-f72b-4b23-bb04-ba93163c8392

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_IsParahoricVec
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisGeometry__HoweDualityGL_c4f3064dc8a43034
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SmoothContragredientIrreducibleAndReflexiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairContragredientQuotientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaPairDetTwistStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaCorrespondenceLargeRank
import Theorems.Thm_GlobalTheory_ThetaLiftGL_compactOpen_basis
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_contra
import Theorems.Thm_GlobalTheory_T_smoothContragredient_irreducible_and_reflexive
import Theorems.Thm_GlobalTheory_T_theta_pair_contragredient_quotient
import Theorems.Thm_GlobalTheory_T_theta_pair_det_twist
import Theorems.Thm_P2M_GlobalTheory_Published_BernsteinUnitaryProductIrreducible_prod__detRep_462f64e927a8
import Theorems.Thm_P2M_GlobalTheory_SmGL_isSmooth_prod__6cb49fe9213d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.Published
open scoped TensorProduct
open GlobalTheory GlobalTheory.ThetaLiftGL
namespace GlobalTheory.ThetaLiftGL
theorem _root_.solution : BernsteinZelevinskyFiniteness → BernsteinUnitaryProductIrreducible → HoweDualityGL →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ)
    (μ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin (r + t)) k) W), r < t →
    IsSmoothChar μ → IsUnitaryChar μ → IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ → IsSmooth π →
    π.IsIrreducible → ThetaPair μ σ π → Nonempty (π.Equiv (prod₂ σ (detRep (Fin t) μ))) := by
  intro hBZ hB hH k _ _ _ _ r t μ V _ _ W _ _ σ π hrt hμs hμu hσs hσi hσu hπs hπi hθ
  have hb := compactOpen_basis k (r + t)
  have hIi : (prod₂ σ (detRep (Fin t) μ)).IsIrreducible :=
    BernsteinUnitaryProductIrreducible.prod₂_detRep hB t hσs hσi hσu hμs hμu
  have hIs : IsSmooth (prod₂ σ (detRep (Fin t) μ)) := isSmooth_prod₂ _ _
  have hπa : IsAdmissible π := (hBZ k).1 (Fin (r + t)) W π hπs hπi
  have hIa : IsAdmissible (prod₂ σ (detRep (Fin t) μ)) := (hBZ k).1 (Fin (r + t)) _ _ hIs hIi
  have hθI : ThetaPair μ σ (prod₂ σ (detRep (Fin t) μ)) :=
    GlobalTheory.T.theta_pair_det_twist hBZ k r t μ V σ hrt hμs hμu hσs hσi hσu
  have hq : OmQuot μ σ (contra π) := GlobalTheory.T.theta_pair_contragredient_quotient k r (r + t) μ V W σ π hμs hπa hθ
  have hqI : OmQuot μ σ (contra (prod₂ σ (detRep (Fin t) μ))) :=
    GlobalTheory.T.theta_pair_contragredient_quotient k r (r + t) μ V _ σ _ hμs hIa hθI
  have hc := GlobalTheory.T.smoothContragredient_irreducible_and_reflexive (GL (Fin (r + t)) k) hb W _ π (prod₂ σ (detRep (Fin t) μ)) hπa hIa
  have hc' := GlobalTheory.T.smoothContragredient_irreducible_and_reflexive (GL (Fin (r + t)) k) hb _ W (prod₂ σ (detRep (Fin t) μ)) π hIa hπa
  obtain ⟨e⟩ := (hH k r (r + t) μ hμs).1 V _ _ σ (contra π) (contra (prod₂ σ (detRep (Fin t) μ)))
    hσs hσi (isSmooth_contra π) (hc.1 hπi) (isSmooth_contra _) (hc'.1 hIi) hq hqI
  exact hc.2.2 ⟨e⟩
end GlobalTheory.ThetaLiftGL
