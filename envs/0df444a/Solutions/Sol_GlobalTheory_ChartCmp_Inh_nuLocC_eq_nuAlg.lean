-- Prove2me | solution 1 for GlobalTheory.ChartCmp.Inh.nuLocC_eq_nuAlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:07:09.977491+00:00
-- url     : https://prove2.me/submissions/421ca388-2368-4499-8c89-8214bb9c04ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_Comp1Scalar
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_map_id


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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.Inh
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.AdditiveBiext
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
namespace GlobalTheory.ChartCmp.Inh
theorem _root_.solution {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (Ch : IntChart T io y)
    (B : FB T.V (chD Ch.ch) (𝓞 E)) (hF : B.G.F = Ch.FT) (hA : B.A.act = Ch.actT) (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    nuLocC Ch e k a n = letI := io.toAlgebra; nuAlg Dw T B Ch.ch.h Ch.ch.uvec e k a n := by
  letI := io.toAlgebra
  have hFK : Ch.ch.B.FK T.Fr = B.FK T.Fr := by
    funext j
    show MvPowerSeries.map (algebraMap T.Fr T.Fr) (Ch.ch.B.G.F j) =
      MvPowerSeries.map (algebraMap T.V T.Fr) (B.G.F j)
    rw [gt_map_id, hF, Ch.gen.1.1 j]
  have hAK : ∀ b, Ch.ch.B.actK T.Fr b = B.actK T.Fr b := by
    intro b
    funext j
    show MvPowerSeries.map (algebraMap T.Fr T.Fr) (Ch.ch.B.A.act b j) =
      MvPowerSeries.map (algebraMap T.V T.Fr) (B.A.act b j)
    rw [gt_map_id, hA, Ch.gen.1.2.1 b j]
  have hB : ∀ {ι : Type} [Fintype ι] (f : PS T.Fr n (chD Ch.ch)) (cp : ι → Fin n)
      (u : ι → Fin (chD Ch.ch) → T.Fr) (P : MvPolynomial ι T.Fr),
      nabValN Ch.ch.B T.Fr Ch.ch.h H.w0 k f cp u P = nabValN B T.Fr Ch.ch.h H.w0 k f cp u P := by
    intro ι _ f cp u P
    simp only [nabValN, FB.hL, hFK, hAK]
  dsimp only [nuLocC, nuAlg]
  refine iInf_congr fun P => iInf_congr fun _ => ?_
  apply le_antisymm
  · refine le_iInf fun g => ?_
    have hmem : IsIntPS T (MvPowerSeries.map (algebraMap T.V T.Fr) g) := fun m =>
      RingHom.mem_range.mpr ⟨MvPowerSeries.coeff m g, by simp⟩
    exact (iInf₂_le _ hmem).trans_eq (by rw [hB])
  · refine le_iInf fun f => le_iInf fun hf => ?_
    have hf' := fun m => RingHom.mem_range.mp (hf m)
    choose g hg using hf'
    have hfg : MvPowerSeries.map (algebraMap T.V T.Fr) (g : PS T.V n (chD Ch.ch)) = f := by
      ext m
      exact hg m
    exact (iInf_le _ (g : PS T.V n (chD Ch.ch))).trans_eq (by rw [hfg, hB])
end GlobalTheory.ChartCmp.Inh
