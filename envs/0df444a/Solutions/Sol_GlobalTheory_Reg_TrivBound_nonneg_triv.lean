-- Prove2me | solution 1 for GlobalTheory.Reg.TrivBound.nonneg_triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:16:00.074911+00:00
-- url     : https://prove2.me/submissions/5d5a6cff-cdba-4694-8144-f3450185965e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RealPtGeo
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_CombinedBoundAtTrivialValuationsOfCharts
import Theorems.Thm_GlobalTheory_Reg_TrivBound_chval_nonneg
import Theorems.Thm_P2M_GlobalTheory_Reg_TrivBound_transfer___c2638dae37f4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.TrivBound
open IsLocalRing Formalism.L2.PjFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
namespace GlobalTheory.Reg.TrivBound
theorem _root_.solution {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) (hQ : S.CovQ) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) : ∀ q ∈ trivSet Xo c, 0 ≤ q F := by
  intro q hq
  obtain ⟨j, V, _, _, _, _, φ, hcen, -, ⟨x, hxE, hφx⟩, hChV⟩ := hQ q hq
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.O
  have hqq : (maximalIdeal V).comap φ.toRingHom ⊔
      Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤ := by
    have hm : maximalIdeal S.O = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    rw [hm, Ideal.map_span, Set.image_singleton, sup_comm]
    exact hcen ϖ hϖ
  obtain ⟨a', s', hs', hfs'⟩ := transfer'' (O := S.O) (S.ch j F) x hx0 (fun V _ _ _ _ _ φ hφx => by
    obtain ⟨ioV, e', hov, -, v, hv, hChV⟩ := S.pts j V φ ⟨x, hxE, hφx⟩
    exact ⟨e', v F, hov.1, hChV a n F hF, h0 v hv⟩) ((maximalIdeal V).comap φ.toRingHom) hqq
  exact chval_nonneg φ.toRingHom 1 (S.ch j F) _ (hChV a n F hF) a' s' hfs' hs'
end GlobalTheory.Reg.TrivBound
