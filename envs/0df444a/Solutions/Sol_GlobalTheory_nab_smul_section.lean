-- Prove2me | solution 1 for GlobalTheory.nab_smul_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:07.081338+00:00
-- url     : https://prove2.me/submissions/fc3b7d17-4643-452f-94e7-3ff2753547c4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThExpBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ConnectionLinearInSection
import Theorems.Thm_GlobalTheory_NabLinear_nabVal_C_mul
import Theorems.Thm_GlobalTheory_NabLinear_psJet_C
import Theorems.Thm_GlobalTheory_NabLinear_isValueAt_scale
import Theorems.Thm_P2M_GlobalTheory_NabLinear_appTop_to__e0b53a85c105
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_mul
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_exists_pullSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open GlobalTheory
open NabLinear
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (N : ℕ) (F F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (r : S), (∀ j, F'.f j = liftFun Xo.univ.t.G _ (T := ptO Xo y.x) (toΓ S r) * F.f j) → ∀ α, nab y ((N : ℤ) ^ 2) F' α = r * nab y ((N : ℤ) ^ 2) F α := by
  intro E _ _ _ H Dw l Xo c _ nab hnab S _ _ y N
  letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  have key : ∀ (K : ℤ) (k : ℕ), K = (k : ℤ) →
      ∀ (F F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x))) (r : S),
      (∀ j, F'.f j = liftFun Xo.univ.t.G _ (T := ptO Xo y.x) (toΓ S r) * F.f j) →
        ∀ α, nab y K F' α = r * nab y K F α := by
    rintro K k rfl F F' r hF α
    obtain ⟨C, hex, hval⟩ := hnab.2 S y
    obtain ⟨f, hf⟩ := hex k F
    have hf' : IsGerm y C.d C.x C.B.A.act C.e C.wP k F' (MvPowerSeries.C r * f) := by
      intro m
      obtain ⟨F₁, τ, hP, hC, hV⟩ := hf m
      obtain ⟨F₂, hP₂⟩ := GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
        (jBase y C.d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F'
      refine ⟨F₂, τ, hP₂, hC, ?_⟩
      have h := isValueAt_scale Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (jBase y C.d m 1) hF hP hP₂ hV
      refine (congrArg (IsValueAt Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) F₂ (C.x m) τ) ?_).mp h
      refine (congrArg (fun w : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤) => w * toΓ _ (psJet m f))
        (appTop_toΓ (algebraMap S (Jet S (Fin 1 × Fin C.d) m)) r)).trans ?_
      rw [FBIdJet.psJet_mul, psJet_C, map_mul]
    exact (hval k F' _ hf' α).trans ((nabVal_C_mul _ _ _ _ _ _ _ _).trans (congrArg (r * ·) (hval k F f hf α).symm))
  exact key _ (N ^ 2) (Nat.cast_pow N 2).symm
end GlobalTheory
